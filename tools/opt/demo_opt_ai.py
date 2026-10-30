#!/usr/bin/env python3
"""Reproduce the opt-only before/after demo; no external API by default."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[2]
FIXTURE = ROOT / "rapx/tests/opt/ai_demo"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cargo-rapx", default=shutil.which("cargo-rapx"))
    parser.add_argument("--output", type=Path, default=ROOT / "target/opt-ai-demo")
    parser.add_argument("--api", action="store_true", help="Use configured real API instead of offline export")
    args = parser.parse_args()
    if not args.cargo_rapx:
        parser.error("pass --cargo-rapx or install cargo-rapx")
    args.output.mkdir(parents=True, exist_ok=True)
    out = Path(tempfile.mkdtemp(prefix="demo-", dir=args.output.resolve()))
    env = os.environ.copy()
    binary = str(Path(args.cargo_rapx).resolve())
    env["PATH"] = str(Path(binary).parent) + os.pathsep + env.get("PATH", "")
    records = []
    for label, features in (("before", []), ("after", ["--features", "optimized"])):
        test_cmd = ["cargo", "test", "--offline", *features]
        test_env = env | {"CARGO_TARGET_DIR": str(out / "tests")}
        with (out / f"{label}-tests.log").open("wb") as log:
            subprocess.run(test_cmd, cwd=FIXTURE, env=test_env, stdout=log,
                           stderr=subprocess.STDOUT, check=True)
        command = [binary, "rapx", "opt-ai", "--output", str(out / label)]
        if not args.api:
            command.append("--offline")
        command += ["--", "--offline", *features]
        with (out / f"{label}-scan.log").open("wb") as log:
            subprocess.run(command, cwd=FIXTURE, env=env, stdout=log,
                           stderr=subprocess.STDOUT, check=True)
        reports = list((out / label).glob("run-*/report.json"))
        assert len(reports) == 1
        result = json.loads(reports[0].read_text())
        count = sum(f["static"]["title"] == "Improper data collection detected"
                    for f in result["findings"])
        assert count == (1 if label == "before" else 0), result
        records.append({"variant": label, "test_command": test_cmd, "tests_passed": True,
                        "scan_command": command, "front_removal_candidates": count,
                        "report": str(reports[0]), "review_mode": result["mode"]})
    result = {"source_sha256": hashlib.sha256((FIXTURE / "src/lib.rs").read_bytes()).hexdigest(),
              "runs": records, "performance_measured": False,
              "note": "Manually authored safe rewrite selected with a feature; not an AI-generated patch. "
                      "Candidate disappearance and finite tests do not prove equivalence or speedup."}
    (out / "result.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))
    print(f"Demo artifacts: {out}")


if __name__ == "__main__":
    main()
