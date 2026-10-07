from __future__ import annotations

from pathlib import Path
import sys

import pytest

REPO = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(REPO / "web"))

from docker_runner import DIGRunner  # noqa: E402


MANIFEST = (REPO / "web" / "examples" / "stack-axioms.toml").read_text()


def test_web_runner_executes_installed_axiom_fixture_and_returns_structured_json():
    result = DIGRunner(use_docker=False).run(
        code=MANIFEST,
        input_type="toml",
        tool="axioms",
        options={"seed": 42, "timeout": 20},
    )
    assert result["status"] == "completed", result.get("raw_output")
    assert result["axiom_result"]["analysis_kind"] == "axioms"
    assert result["axiom_result"]["language"] == "python"
    assert any(
        finding["verdict"] == "VALIDATED"
        for finding in result["axiom_result"]["findings"]
    )


@pytest.mark.parametrize(
    ("old", "new", "message"),
    [
        ("axioms.fixtures:Stack.push", "os:system", "not an installed API"),
        ('language = "python"', 'language = "java"', "Python fixtures only"),
        ('module_roots = ["/dig/src"]', 'module_roots = ["/tmp"]', "module_roots"),
    ],
)
def test_web_runner_rejects_uninstalled_targets(old, new, message):
    runner = DIGRunner(use_docker=False)
    with pytest.raises(ValueError, match=message):
        runner.run(
            code=MANIFEST.replace(old, new, 1),
            input_type="toml",
            tool="axioms",
        )

