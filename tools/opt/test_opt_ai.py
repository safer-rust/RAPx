"""Run: python3 -m unittest discover -s tools/opt -p test_opt_ai.py -v.

Set RAPX_TEST_CARGO_RAPX to a built cargo-rapx to also run real compiler tests.
"""
import contextlib
import importlib.util
import json
import os
from pathlib import Path
import subprocess
import tempfile
import threading
import unittest
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location("opt_ai", ROOT / "rapx/opt_ai.py")
ai = importlib.util.module_from_spec(spec)
spec.loader.exec_module(ai)


def review(identifier="candidate"):
    return dict(id=identifier, verdict="keep", reason="Repeated prefix copy.",
                suggestion="Use push_str with an independent suffix.",
                validation=["Compare empty and Unicode inputs; benchmark release."])


@contextlib.contextmanager
def server(mode="valid"):
    requests = []

    class Handler(BaseHTTPRequestHandler):
        def log_message(self, *args):
            pass

        def do_POST(self):
            payload = json.loads(self.rfile.read(int(self.headers["Content-Length"])))
            requests.append(payload)
            finding = json.loads(payload["messages"][1]["content"])
            value = review(finding["id"])
            if mode == "invalid":
                value["id"] = "wrong-id"
            if mode == "echo-key":
                value["reason"] = "unit-test-secret"
            status = 429 if mode == "error" else 200
            self.send_response(status)
            self.end_headers()
            self.wfile.write(json.dumps({"choices": [{"finish_reason": "stop",
                "message": {"content": json.dumps(value)}}]}).encode())

    http = ThreadingHTTPServer(("127.0.0.1", 0), Handler)
    thread = threading.Thread(target=http.serve_forever, daemon=True)
    thread.start()
    try:
        yield f"http://127.0.0.1:{http.server_port}/v1/chat/completions", requests
    finally:
        http.shutdown()
        http.server_close()
        thread.join()


class ReviewTests(unittest.TestCase):
    def test_strict_review_contract(self):
        self.assertEqual(ai.validate_review(review(), "candidate")["verdict"], "keep")
        for change in ({"id": "unknown"}, {"verdict": "proved"}, {"reason": ""},
                       {"validation": []}, {"validation": [42]}, {"extra": "field"}):
            with self.subTest(change=change), self.assertRaises(ai.PipelineError):
                ai.validate_review(review() | change, "candidate")

    def test_endpoint_validation(self):
        for url in ("https://example.test/v1/chat/completions", "http://localhost:1234/v1/chat/completions"):
            self.assertEqual(ai.endpoint(url), url)
        for url in (None, "file:///tmp/a", "http://example.test", "https://user:secret@host/v1",
                    "https://host/v1?key=secret", "https://host:bad/v1"):
            with self.subTest(url=url), self.assertRaises(ai.PipelineError):
                ai.endpoint(url)

    def test_http_and_provider_errors(self):
        payload = {"messages": [{}, {"content": '{"id": "candidate"}'}]}
        with server() as (url, requests):
            value = ai.request_review(payload, url, "unit-test-secret", 2)
            self.assertEqual(ai.validate_review(value, "candidate")["verdict"], "keep")
            self.assertEqual(len(requests), 1)
        with server("error") as (url, _), self.assertRaisesRegex(ai.PipelineError, "HTTP 429"):
            ai.request_review(payload, url, "unit-test-secret", 2)

    def test_incomplete_scan_is_not_empty_success(self):
        with tempfile.TemporaryDirectory() as tmp:
            directory = Path(tmp)
            with self.assertRaises(ai.PipelineError):
                ai.collect(directory)
            file = directory / "1.jsonl"
            file.write_text('{"type":"begin","schema_version":1,"crate":"demo"}\n')
            with self.assertRaises(ai.PipelineError):
                ai.collect(directory)
            with file.open("a") as stream:
                stream.write('{"type":"complete","statistics":[0,0,0,0,0,0]}\n')
            findings, scans = ai.collect(directory)
            self.assertEqual(findings, [])
            self.assertEqual(len(scans), 1)

    def test_duplicate_records_and_parallel_crates(self):
        with tempfile.TemporaryDirectory() as tmp:
            directory = Path(tmp)
            for i, crate in enumerate(["a", "a", "b"]):
                rows = [{"type": "begin", "schema_version": 1, "crate": crate},
                        {"type": "finding", "source": "fn foo() {}", "file": "lib.rs", "line_start": 1},
                        {"type": "complete", "statistics": [0, 0, 1, 0, 0, 0]}]
                (directory / f"{i}.jsonl").write_text("\n".join(map(json.dumps, rows)))
            findings, scans = ai.collect(directory)
            self.assertEqual(len(findings), 2)
            self.assertEqual(len(scans), 3)
            self.assertNotEqual(findings[0]["id"], findings[1]["id"])

    def test_malformed_response_is_rejected(self):
        class Reply:
            def __enter__(self): return self
            def __exit__(self, *args): pass
            def read(self, *args): return b'{"choices":[]}'
        with patch.object(ai.urllib.request.OpenerDirector, "open", return_value=Reply()):
            with self.assertRaises(ai.PipelineError):
                ai.request_review({}, "https://example.test", "secret", 1)


@unittest.skipUnless(os.environ.get("RAPX_TEST_CARGO_RAPX"), "requires built RAPx binaries")
class CompilerTests(unittest.TestCase):
    def run_pipeline(self, args, extra_env=None, success=True, features="two-findings"):
        with tempfile.TemporaryDirectory(prefix="rapx-opt-ai-test-") as tmp:
            env = os.environ.copy()
            for name in ("RAPX_AI_API_KEY", "RAPX_AI_MODEL", "RAPX_AI_URL"):
                env.pop(name, None)
            env.update(extra_env or {})
            cmd = [env["RAPX_TEST_CARGO_RAPX"], "rapx", "opt-ai", "--output", tmp, *args,
                   "--", "--offline", "--features", features]
            run = subprocess.run(cmd, cwd=ROOT / "rapx/tests/opt/ai_demo", env=env,
                                 capture_output=True, text=True, timeout=120)
            self.assertEqual(run.returncode == 0, success, run.stdout + run.stderr)
            dirs = list(Path(tmp).glob("run-*"))
            self.assertEqual(len(dirs), 1)
            result = json.loads((dirs[0] / "report.json").read_text())
            for path in dirs[0].rglob("*.json"):
                self.assertNotIn("unit-test-secret", path.read_text())
            self.assertTrue((dirs[0] / "report.md").exists())
            return result

    def test_offline_positive_and_no_key(self):
        result = self.run_pipeline(["--offline"])
        self.assertEqual(result["status"], "offline")
        found = [f for f in result["findings"] if f["static"]["title"] == "Improper data collection detected"]
        self.assertEqual(len(found), 2)
        self.assertTrue(all(f["review"]["verdict"] == "unreviewed" for f in found))
        self.assertTrue(all("remove(0)" in f["static"]["source"] for f in found))

    def test_no_candidates_is_success(self):
        result = self.run_pipeline([], features="optimized")
        self.assertEqual(result["findings"], [])
        self.assertEqual(result["status"], "complete")

    def test_missing_key_preserves_static_findings(self):
        result = self.run_pipeline(["--api-url", "https://example.test/v1/chat/completions"], success=False)
        self.assertEqual(result["status"], "failed")
        self.assertGreater(len(result["findings"]), 0)

    def test_online_loopback_provider(self):
        with server() as (url, requests):
            result = self.run_pipeline(["--api-url", url, "--model", "test-model"],
                                       extra_env={"RAPX_AI_API_KEY": "unit-test-secret"})
        self.assertEqual(result["status"], "complete")
        self.assertEqual(len(requests), len(result["findings"]))
        self.assertTrue(all(f["review"]["verdict"] == "keep" for f in result["findings"]))

    def test_budget_does_not_drop_findings(self):
        with server() as (url, requests):
            result = self.run_pipeline(["--api-url", url, "--model", "test", "--max-findings", "1"],
                                       extra_env={"RAPX_AI_API_KEY": "unit-test-secret"})
        self.assertEqual(result["status"], "partial")
        self.assertEqual(len(requests), 1)
        self.assertEqual(len(result["findings"]), 2)

    def test_oversized_context_is_not_sent(self):
        with server() as (url, requests):
            result = self.run_pipeline(["--api-url", url, "--model", "test", "--max-context-bytes", "1"],
                                       extra_env={"RAPX_AI_API_KEY": "unit-test-secret"})
        self.assertEqual(result["status"], "partial")
        self.assertEqual(len(requests), 0)

    def test_invalid_provider_responses_are_unreviewed(self):
        for mode in ("invalid", "error", "echo-key"):
            with self.subTest(mode=mode), server(mode) as (url, requests):
                result = self.run_pipeline(["--api-url", url, "--model", "test"],
                    extra_env={"RAPX_AI_API_KEY": "unit-test-secret"}, success=False)
                self.assertEqual(result["status"], "partial")
                self.assertTrue(all(f["review"]["verdict"] == "unreviewed" for f in result["findings"]))


if __name__ == "__main__":
    unittest.main()
