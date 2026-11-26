"""LLM transport; Gemini uses REST without an additional SDK dependency."""
import json
import os
from pathlib import Path
import re
import time
from urllib.error import HTTPError, URLError
from urllib.request import Request, urlopen

DEFAULT_MODELS = {"anthropic": "claude-opus-4-8", "gemini": "gemini-3.8-flash",
                  "groq": "qwen/qwen3.8-27b"}


class APIQuotaError(RuntimeError):
    def __init__(self, metadata):
        super().__init__("Groq rate limit (HTTP 429); see saved quota details")
        self.metadata = metadata


def _groq_wait(prompt):
    """Pace serial campaign requests using the last token bucket headers."""
    filename = os.environ.get("DIG_GROQ_RATE_STATE")
    if not filename or not Path(filename).is_file():
        return 0.0
    state = json.loads(Path(filename).read_text())
    limits = state["limits"]
    capacity = float(limits.get("x-ratelimit-limit-tokens") or 8000)
    remaining = float(limits.get("x-ratelimit-remaining-tokens") or 0)
    required = len(prompt) / 3 + 512 + 256
    if required > capacity:
        raise RuntimeError("Groq prompt exceeds configured token-per-minute capacity")
    elapsed = max(0, time.time() - state["timestamp"])
    reset = limits.get("x-ratelimit-reset-tokens") or "60s"
    reset_seconds = sum(float(n) * {"h": 3600, "m": 60, "s": 1}[unit]
                        for n, unit in re.findall(r"(\d+(?:\.\d+)?)([hms])", reset))
    # Wait for the full reported reset if headroom is low; do not assume that
    # the service continuously refills its bucket. Keep at least 20s between
    # requests, including across separate DIG invocations in the campaign.
    delay = max(0, 20 - elapsed)
    delay = max(delay, state.get("blocked_until", 0) - time.time())
    if required > remaining:
        delay = max(delay, reset_seconds + 2 - elapsed)
    left = delay
    while left > 0:
        step = min(left, 20)
        time.sleep(step)
        left -= step
    return delay


def _groq_generate(prompt, model):
    if not re.fullmatch(r"[A-Za-z0-9._/-]+", model):
        raise ValueError("Invalid Groq model ID")
    key = os.environ.get("GROQ_API_KEY", "").strip()
    if not key:
        for name in (".GROQ_API_KEY", ".GROG_API_KEY"):
            path = Path.home() / name
            if path.is_file():
                key = path.read_text().strip()
                break
    if not key or any(c.isspace() for c in key):
        raise RuntimeError("Set GROQ_API_KEY or save a valid key in ~/.GROQ_API_KEY")
    while True:
        waited = _groq_wait(prompt)
        payload = {"model": model, "messages": [{"role": "user", "content": prompt}],
                   "max_completion_tokens": 512}
        request = Request("https://api.groq.com/openai/v1/chat/completions",
                          data=json.dumps(payload).encode(),
                          headers={"Content-Type": "application/json",
                                   "User-Agent": "DIG-benchmark/0.1",
                                   "Authorization": "Bearer " + key}, method="POST")
        try:
            with urlopen(request, timeout=120) as response:
                body = json.load(response)
                limits = {name: response.headers.get(name) for name in (
                    "x-ratelimit-limit-tokens",
                    "x-ratelimit-remaining-requests", "x-ratelimit-remaining-tokens",
                    "x-ratelimit-reset-requests", "x-ratelimit-reset-tokens")}
            break
        except HTTPError as error:
            if error.code == 429:
                try:
                    detail = json.loads(error.read().decode()).get("error", {})
                except (ValueError, UnicodeError):
                    detail = {}
                message = str(detail.get("message", "")).replace(key, "[redacted]")
                retry = error.headers.get("retry-after") if error.headers else None
                metadata = {"http_status": 429, "code": detail.get("code"),
                            "message": message, "retry_after": retry}
                try:
                    wait_sec = max(30, float(retry) + 5) if retry else 60
                except (ValueError, TypeError):
                    wait_sec = 60
                if wait_sec <= 600:
                    time.sleep(wait_sec)
                    continue
                raise APIQuotaError(metadata) from None
            raise RuntimeError(f"Groq API failed (HTTP {error.code}); check key/model access") from None
        except (URLError, TimeoutError):
            raise RuntimeError("Groq connection failed or timed out") from None
    if os.environ.get("DIG_GROQ_RATE_STATE"):
        Path(os.environ["DIG_GROQ_RATE_STATE"]).write_text(
            json.dumps({"timestamp": time.time(), "limits": limits})+"\n")
    choices = body.get("choices", [])
    choice = choices[0] if choices else {}
    output = choice.get("message", {}).get("content")
    if not isinstance(output, str) or not output.strip():
        raise RuntimeError("Groq returned no candidate text")
    return output, {"model": body.get("model", model), "usage": body.get("usage", {}),
                    "finish_reason": choice.get("finish_reason"),
                    "request_id": body.get("id"), "rate_limits": limits,
                    "max_completion_tokens": 512, "rate_wait_seconds": waited}


def generate(prompt, provider="anthropic", model=None):
    model = model or DEFAULT_MODELS[provider]
    if provider == "groq":
        return _groq_generate(prompt, model)
    if provider == "anthropic":
        import anthropic
        msg = anthropic.Anthropic().messages.create(
            model=model, max_tokens=1024,
            messages=[{"role": "user", "content": prompt}],
        )
        return "\n".join(p.text for p in msg.content if p.type == "text"), {
            "model": model, "usage": msg.usage.model_dump(),
        }
    if provider != "gemini":
        raise ValueError("Unknown LLM provider")
    if not re.fullmatch(r"[A-Za-z0-9._-]+", model):
        raise ValueError("Invalid Gemini model ID")
    key = os.environ.get("GEMINI_API_KEY", "").strip()
    if not key:
        path = Path.home() / ".GEMINI_API_KEY"
        if not path.is_file():
            raise RuntimeError("Set GEMINI_API_KEY or create ~/.GEMINI_API_KEY")
        key = path.read_text().strip()
    if not key or any(c.isspace() for c in key):
        raise RuntimeError("Gemini key is empty or contains whitespace")
    payload = {
        "contents": [{"role": "user", "parts": [{"text": prompt}]}],
        "generationConfig": {"maxOutputTokens": 8192},
    }
    request = Request(
        f"https://generativelanguage.googleapis.com/v1beta/models/{model}:generateContent",
        data=json.dumps(payload).encode(),
        headers={"Content-Type": "application/json", "x-goog-api-key": key},
        method="POST",
    )
    try:
        with urlopen(request, timeout=120) as response:
            body = json.load(response)
    except HTTPError as error:
        # Do not print request headers, the key, or server-supplied messages.
        if error.code == 429:
            raise RuntimeError("Gemini quota exhausted (HTTP 429); stop and retry later") from None
        raise RuntimeError(f"Gemini API failed (HTTP {error.code}); check key/model access") from None
    except (URLError, TimeoutError):
        raise RuntimeError("Gemini connection failed or timed out") from None
    candidates = body.get("candidates", [])
    candidate = candidates[0] if candidates else {}
    parts = candidate.get("content", {}).get("parts", [])
    output = "\n".join(p["text"] for p in parts if "text" in p and not p.get("thought"))
    if not output:
        raise RuntimeError("Gemini returned no candidate text")
    return output, {"model": body.get("modelVersion", model),
                    "usage": body.get("usageMetadata", {}),
                    "finish_reason": candidate.get("finishReason")}
