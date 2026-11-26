"""Offline checks for credentials, Gemini responses, and safe API errors."""
import io
import json
from pathlib import Path
import sys
from urllib.error import HTTPError

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))
import llm_backend


def test_gemini_reads_key_file_and_skips_thoughts(monkeypatch, tmp_path):
    monkeypatch.delenv("GEMINI_API_KEY", raising=False)
    monkeypatch.setattr(Path, "home", lambda: tmp_path)
    (tmp_path / ".GEMINI_API_KEY").write_text("test-key\n")
    def response(request, timeout):
        assert request.get_header("X-goog-api-key") == "test-key"
        assert "test-key" not in request.full_url
        assert json.loads(request.data)["contents"][0]["parts"][0]["text"] == "prompt"
        return io.StringIO(json.dumps({
            "candidates": [{"content": {"parts": [
                {"text": "reasoning", "thought": True}, {"text": "x >= 0"}]},
                "finishReason": "STOP"}],
            "usageMetadata": {"totalTokenCount": 30}, "modelVersion": "resolved-model",
        }))
    monkeypatch.setattr(llm_backend, "urlopen", response)
    text, metadata = llm_backend.generate("prompt", "gemini")
    assert text == "x >= 0"
    assert metadata["usage"]["totalTokenCount"] == 30
    assert metadata["model"] == "resolved-model"


def test_environment_key_takes_precedence(monkeypatch):
    monkeypatch.setenv("GEMINI_API_KEY", "env-key")
    def response(request, timeout):
        assert request.get_header("X-goog-api-key") == "env-key"
        return io.StringIO('{"candidates":[{"content":{"parts":[{"text":"x == y"}]}}]}')
    monkeypatch.setattr(llm_backend, "urlopen", response)
    assert llm_backend.generate("prompt", "gemini")[0] == "x == y"


@pytest.mark.parametrize("code", [400, 403, 404, 429, 503])
def test_errors_are_safe_and_not_retried(monkeypatch, code):
    monkeypatch.setenv("GEMINI_API_KEY", "secret-key")
    calls = []
    def response(request, timeout):
        calls.append(request)
        raise HTTPError(request.full_url, code, "secret-key", {}, None)
    monkeypatch.setattr(llm_backend, "urlopen", response)
    with pytest.raises(RuntimeError) as error:
        llm_backend.generate("prompt", "gemini")
    assert str(code) in str(error.value)
    assert "secret-key" not in str(error.value)
    assert len(calls) == 1


def test_empty_response_is_an_error(monkeypatch):
    monkeypatch.setenv("GEMINI_API_KEY", "test-key")
    monkeypatch.setattr(llm_backend, "urlopen", lambda *a, **k: io.StringIO('{}'))
    with pytest.raises(RuntimeError, match="no candidate text"):
        llm_backend.generate("prompt", "gemini")


@pytest.mark.parametrize("filename", [".GROQ_API_KEY", ".GROG_API_KEY"])
def test_groq_key_files_and_usage(monkeypatch, tmp_path, filename):
    monkeypatch.delenv("GROQ_API_KEY", raising=False)
    monkeypatch.setattr(Path, "home", lambda: tmp_path)
    (tmp_path / filename).write_text("test-groq-key\n")
    def response(request, timeout):
        assert request.get_header("Authorization") == "Bearer test-groq-key"
        assert request.get_header("User-agent") == "DIG-benchmark/0.1"
        assert request.full_url == "https://api.groq.com/openai/v1/chat/completions"
        assert json.loads(request.data)["messages"][0]["content"] == "prompt"
        result = io.StringIO(json.dumps({"model": "resolved-qwen", "choices": [
            {"message": {"content": "x >= 0"}, "finish_reason": "stop"}],
            "usage": {"total_tokens": 12}, "id": "test-request"}))
        result.headers = {"x-ratelimit-remaining-requests": "999"}
        return result
    monkeypatch.setattr(llm_backend, "urlopen", response)
    output, meta = llm_backend.generate("prompt", "groq")
    assert output == "x >= 0"
    assert meta["usage"]["total_tokens"] == 12
    assert meta["rate_limits"]["x-ratelimit-remaining-requests"] == "999"


def test_groq_quota_error_is_safe(monkeypatch):
    monkeypatch.setenv("GROQ_API_KEY", "secret-groq-key")
    def response(request, timeout):
        raise HTTPError(request.full_url, 429, "secret-groq-key", {}, None)
    monkeypatch.setattr(llm_backend, "urlopen", response)
    with pytest.raises(RuntimeError, match="Groq rate limit") as error:
        llm_backend.generate("prompt", "groq")
    assert "secret-groq-key" not in str(error.value)


def test_groq_pacing_honors_full_reset(monkeypatch, tmp_path):
    state = tmp_path / "rate.json"
    state.write_text(json.dumps({"timestamp": 100, "limits": {
        "x-ratelimit-limit-tokens": "8000", "x-ratelimit-remaining-tokens": "10",
        "x-ratelimit-reset-tokens": "45s"}}))
    monkeypatch.setenv("DIG_GROQ_RATE_STATE", str(state))
    monkeypatch.setattr(llm_backend.time, "time", lambda: 105)
    sleeps = []
    monkeypatch.setattr(llm_backend.time, "sleep", sleeps.append)
    assert llm_backend._groq_wait("prompt") == 42
    assert sum(sleeps) == 42
    assert max(sleeps) <= 20
