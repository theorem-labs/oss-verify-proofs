"""tools/oft/ci/facts-review-served, which records what answered the facts review and whether it is the provider the
review asked for, and its two callers: facts-review-run, which runs the review agent through it, and
facts-review-comment, which posts the review only when the record shows the provider asked for.

Each stand-in agent prints events in the shapes the review agent's tool prints them (`--output-format stream-json
--verbose`): a `system` event, an `assistant` event for each content block of a response, with the response's model and
message id, and a `result` event whose `modelUsage` names the tool's provider."""
import importlib.machinery
import importlib.util
import json
import os
import shutil
import subprocess
import sys
import tempfile
import time
import unittest

from oft.tests.helpers import REPO

CI = os.path.join(REPO, "tools", "oft", "ci")
SERVED = os.path.join(CI, "facts-review-served")
RUN = os.path.join(CI, "facts-review-run")
COMMENT = os.path.join(CI, "facts-review-comment")
ASKED = "anthropic/model-a-1"
REVIEW = "The facts hold.\n"
TOOL = "claude"   # the review agent's command, as facts-review-run calls it
HOST = "api.anthropic.com"
HEAD = f"asked {ASKED}\nendpoint {HOST}\n"   # the record's first lines, when the tool sends its requests to the API
# The variables that send the tool's requests elsewhere: no test inherits one from the environment it runs in.
ELSEWHERE = ("ANTHROPIC_BASE_URL", "ANTHROPIC_UNIX_SOCKET", "CLAUDE_CODE_API_BASE_URL",
             "_CLAUDE_CODE_ASSUME_FIRST_PARTY_BASE_URL", "CLAUDE_CONFIG_DIR", "NODE_TLS_REJECT_UNAUTHORIZED",
             "NODE_EXTRA_CA_CERTS", "SSL_CERT_FILE", "SSL_CERT_DIR", "HTTPS_PROXY", "HTTP_PROXY", "ALL_PROXY",
             "ANTHROPIC_PROFILE", "ANTHROPIC_CONFIG_DIR", "XDG_CONFIG_HOME", "CLAUDE_CODE_EXTRA_BODY",
             "ANTHROPIC_BETAS", "CLAUDE_CODE_MANAGED_SETTINGS_PATH", "CLAUDE_CODE_REMOTE_SETTINGS_PATH",
             "CLAUDE_CODE_DISABLE_ADMIN_ENV_UNION", "CLAUDE_CODE_MOCK_REMOTE_SETTINGS", "ANTHROPIC_CUSTOM_HEADERS",
             "CLAUDE_CODE_CUSTOM_OAUTH_URL")
# A stand-in agent: prints the events of the JSON list in $HOME/events.json, each on a line of its own as it comes; an
# item {"sleep": seconds} waits, {"exit": status} ends there, {"raw": text} prints the text as it is, and {"child":
# seconds} starts a process of its own that sleeps that long, as a tool the agent runs would. It writes its arguments
# to $HOME/argv.json, and its own process id and its child's to $HOME/pids.
FAKE_AGENT = r"""#!/usr/bin/env python3
import json, os, subprocess, sys, time
home = os.environ.get("HOME", "")
with open(os.path.join(home, "argv.json"), "w") as f:
    json.dump(sys.argv[1:], f)
with open(os.path.join(home, "events.json")) as f:
    events = json.load(f)
pids = [os.getpid()]


def write_pids():
    with open(os.path.join(home, "pids.new"), "w") as f:
        f.write(" ".join(map(str, pids)))
    os.replace(os.path.join(home, "pids.new"), os.path.join(home, "pids"))


write_pids()
for event in events:
    if "sleep" in event:
        time.sleep(event["sleep"])
    elif "exit" in event:
        sys.exit(event["exit"])
    elif "raw" in event:
        print(event["raw"], flush=True)
    elif "child" in event:
        pids.append(subprocess.Popen(["sleep", str(event["child"])]).pid)
        write_pids()
    else:
        print(json.dumps(event), flush=True)
"""


def init():
    return {"type": "system", "subtype": "init", "model": "model-a-1", "apiKeySource": "none"}


def turn(n, model="model-a-1", blocks=1):
    """The events of the agent's turn n: one per content block, each with the response's model and message id."""
    message = {"id": f"msg_{n:04d}", "role": "assistant", "content": [{"type": "text", "text": "..."}]}
    if model is not None:
        message["model"] = model
    return [{"type": "assistant", "message": message, "parent_tool_use_id": None} for _ in range(blocks)]


def result(text=REVIEW, providers=("firstParty",), is_error=False, turns=2):
    usage = {f"model-a-1{'' if i == 0 else f'-{i}'}": {"canonicalModel": "model-a-1", "provider": p}
             for i, p in enumerate(providers)}
    return {"type": "result", "subtype": "success", "is_error": is_error, "result": text, "num_turns": turns,
            "modelUsage": usage}


def check(record):
    r = subprocess.run([sys.executable, SERVED, "check"], input=record, capture_output=True, text=True)
    return r.returncode, r.stdout.strip()


def environment(**variables):
    """The environment a test runs a script in: this one's, without the variables that send the tool's requests
    elsewhere, and with `variables`."""
    env = {k: v for k, v in os.environ.items()
           if k.upper() not in ELSEWHERE and not k.startswith(("ANTHROPIC_", "CLAUDE_CODE_", "_CLAUDE_CODE_"))}
    env.update(variables)
    return env


class StandIn(unittest.TestCase):
    def setUp(self):
        self._tmp = tempfile.TemporaryDirectory(prefix="oft-served-")
        self.dir = os.path.realpath(self._tmp.name)
        self.bin = os.path.join(self.dir, "bin")
        os.mkdir(self.bin)
        self.review = os.path.join(self.dir, ".review")
        os.mkdir(self.review)

    def tearDown(self):
        self._tmp.cleanup()

    def agent(self, name, events):
        path = os.path.join(self.bin, name)
        with open(path, "w") as f:
            f.write(FAKE_AGENT)
        os.chmod(path, 0o755)
        with open(os.path.join(self.dir, "events.json"), "w") as f:
            json.dump(events, f)
        return path

    def read(self, name):
        with open(os.path.join(self.review, name)) as f:
            return f.read()


class Run(StandIn):
    """facts-review-served run: the record it writes, its exit status, and that it stops the agent at a turn another
    model answers."""

    def run_agent(self, events, asked=ASKED, **variables):
        agent = self.agent("agent", events)
        env = environment(HOME=self.dir, **variables)
        started = time.monotonic()
        r = subprocess.run([sys.executable, SERVED, "run", self.review, asked, "--", agent], env=env, cwd=self.dir,
                           capture_output=True, text=True, timeout=120)
        return r.returncode, r.stderr, time.monotonic() - started

    def test_the_provider_asked_for_answered_every_turn(self):
        events = [init()] + turn(1, blocks=2) + turn(2) + [result()]
        code, err, _ = self.run_agent(events)
        self.assertEqual(code, 0, err)
        self.assertEqual(self.read("served"), f"{HEAD}usage firstParty/model-a-1\nfirstParty/model-a-1 2\n")
        self.assertEqual(json.loads(self.read("review.json")), result())
        self.assertEqual(len(self.read("review.jsonl").splitlines()), len(events))
        self.assertEqual(check(self.read("served")), (0, "firstParty/model-a-1 (2 turns)"))

    def test_another_model_at_the_first_turn_stops_the_agent_at_once(self):
        events = [init()] + turn(1, "other-b-1") + [{"sleep": 100}] + turn(2) + [result()]
        code, err, seconds = self.run_agent(events)
        self.assertEqual(code, 4, err)
        self.assertLess(seconds, 60, "the agent was not stopped at its first turn")
        self.assertIn("turn 1 was answered by other-b-1, not model-a-1", err)
        self.assertEqual(self.read("served"), f"{HEAD}none/other-b-1 1\n")
        self.assertEqual(self.read("review.json"), "", "no result: an empty review.json, as `> review.json` left it")
        code, line = check(self.read("served"))
        self.assertEqual(code, 1)
        self.assertIn("but none/other-b-1 (1 turn) answered", line)

    def test_another_model_after_some_turns_stops_the_agent_there(self):
        events = [init()] + turn(1) + turn(2) + turn(3, "other-b-1") + [{"sleep": 100}, result()]
        code, err, seconds = self.run_agent(events)
        self.assertEqual(code, 4, err)
        self.assertLess(seconds, 60)
        self.assertIn("turn 3 was answered by other-b-1", err)
        self.assertEqual(check(self.read("served"))[0], 1)

    def test_a_turn_that_names_no_model_stops_the_agent(self):
        events = [init()] + turn(1, None) + [{"sleep": 100}, result()]
        code, err, seconds = self.run_agent(events)
        self.assertEqual(code, 4, err)
        self.assertLess(seconds, 60)
        self.assertIn("turn 1 was answered by no model it named", err)
        self.assertEqual(self.read("served"), f"{HEAD}none/none 1\n")
        self.assertEqual(check(self.read("served"))[0], 3)

    def test_another_provider_at_the_end_is_not_the_one_asked_for(self):
        events = [init()] + turn(1) + turn(2) + [result(providers=("bedrock",))]
        code, err, _ = self.run_agent(events)
        self.assertEqual(code, 4, err)
        self.assertEqual(self.read("served"), f"{HEAD}usage bedrock/model-a-1\nbedrock/model-a-1 2\n")
        code, line = check(self.read("served"))
        self.assertEqual(code, 1)
        self.assertIn("which the tool calls firstParty/model-a-1, but bedrock/model-a-1 (2 turns) answered, and the "
                      "tool's usage names bedrock/model-a-1", line)
        # the review is still there, though it is not to be posted
        self.assertEqual(json.loads(self.read("review.json"))["result"], REVIEW)

    def test_two_providers_at_the_end_are_not_the_one_asked_for(self):
        events = [init()] + turn(1) + [result(providers=("firstParty", "vertex"))]
        code, err, _ = self.run_agent(events)
        self.assertEqual(code, 4, err)
        self.assertEqual(self.read("served"), f"{HEAD}usage firstParty/model-a-1\nusage vertex/model-a-1\n"
                                              "firstParty+vertex/model-a-1 1\n")
        self.assertEqual(check(self.read("served"))[0], 1)

    def test_a_usage_entry_of_another_model_is_not_the_one_asked_for(self):
        """Every turn answered by the model asked for, but the tool's usage names a request of another model."""
        side = result()
        side["modelUsage"]["other-b-1"] = {"canonicalModel": "other-b-1", "provider": "firstParty"}
        code, err, _ = self.run_agent([init()] + turn(1) + [side])
        self.assertEqual(code, 4, err)
        self.assertIn("usage firstParty/other-b-1\n", self.read("served"))
        code, line = check(self.read("served"))
        self.assertEqual(code, 1)
        self.assertIn("the tool's usage names firstParty/model-a-1, firstParty/other-b-1", line)

    def test_a_review_whose_result_names_no_provider_is_not_attributable(self):
        """The tool's `.modelUsage` is {} when no request got a response: a review beside it names no provider."""
        events = [init()] + turn(1) + turn(2) + [result(providers=())]
        code, err, _ = self.run_agent(events)
        self.assertEqual(code, 4, err)
        self.assertEqual(self.read("served"), f"{HEAD}none/model-a-1 2\n")
        code, line = check(self.read("served"))
        self.assertEqual(code, 3)
        self.assertIn("it is not attributable", line)

    def test_a_message_the_tool_wrote_itself_is_no_turn(self):
        """A refused key: the tool's own message, model "<synthetic>", then an error result with {} for modelUsage."""
        synthetic = {"type": "assistant", "message": {"id": "0068f1fb", "model": "<synthetic>", "content": []},
                     "error": "authentication_failed", "is_api_error_message": True}
        events = [init(), synthetic, result("Invalid API key", providers=(), is_error=True, turns=1), {"exit": 1}]
        code, err, _ = self.run_agent(events)
        self.assertEqual(code, 1, "the agent's own failure, not a stop")
        self.assertEqual(self.read("served"), HEAD)
        self.assertEqual(check(self.read("served"))[0], 3)

    def test_an_agent_that_fails_by_itself_keeps_its_status(self):
        events = [init()] + turn(1) + [{"exit": 7}]
        code, err, _ = self.run_agent(events)
        self.assertEqual(code, 7, err)
        self.assertEqual(self.read("served"), f"{HEAD}none/model-a-1 1\n")

    def test_a_provider_it_has_no_name_for_is_refused_before_the_agent_runs(self):
        code, err, _ = self.run_agent([init()] + turn(1) + [result()], asked="openai/model-a-1")
        self.assertEqual(code, 2)
        self.assertIn("not <provider>/<model>", err)
        self.assertFalse(os.path.exists(os.path.join(self.dir, "argv.json")), "the agent ran")

    def test_a_stale_record_and_result_do_not_survive_a_run(self):
        for name in ("served", "review.json"):
            with open(os.path.join(self.review, name), "w") as f:
                f.write(f"asked {ASKED}\nfirstParty/model-a-1 9\n")
        self.run_agent([init()] + turn(1, "other-b-1"))
        self.assertEqual(self.read("served"), f"{HEAD}none/other-b-1 1\n")
        self.assertEqual(self.read("review.json"), "")

    def test_an_endpoint_other_than_the_provider_s_own_starts_no_agent(self):
        """The tool calls its provider firstParty also when ANTHROPIC_BASE_URL names a proxy, which could answer with
        any model under any name (GateReview, finding 1): such a review is refused before the agent runs."""
        for variables, where in (({"ANTHROPIC_BASE_URL": "https://proxy.example/"}, "https:proxy.example"),
                                 ({"ANTHROPIC_BASE_URL": "http://api.anthropic.com"}, "http:api.anthropic.com"),
                                 ({"ANTHROPIC_BASE_URL": "https://api.anthropic.com:8443"},
                                  "https:api.anthropic.com:8443"),
                                 ({"ANTHROPIC_BASE_URL": "https:/" + "/x" + "@api.anthropic.com"},
                                  "https:api.anthropic.com+userinfo"),
                                 ({"ANTHROPIC_BASE_URL": "https://api.anthropic.com.proxy.example"},
                                  "https:api.anthropic.com.proxy.example"),
                                 ({"ANTHROPIC_BASE_URL": ""}, "none:none"),
                                 ({"ANTHROPIC_BASE_URL": "https://[::1"}, "unreadable-url"),
                                 ({"ANTHROPIC_BASE_URL": "https://api.anthropic.com:x"}, "unreadable-url"),
                                 ({"https_proxy": "http://proxy.example"}, "https_proxy"),
                                 ({"NODE_EXTRA_CA_CERTS": "/tmp/ca.pem"}, "NODE_EXTRA_CA_CERTS"),
                                 ({"NODE_TLS_REJECT_UNAUTHORIZED": "0"}, "NODE_TLS_REJECT_UNAUTHORIZED"),
                                 ({"SSL_CERT_FILE": "/tmp/ca.pem"}, "SSL_CERT_FILE"),
                                 ({"SSL_CERT_DIR": "/tmp/certs"}, "SSL_CERT_DIR"),
                                 ({"HTTP_PROXY": "http://proxy.example"}, "HTTP_PROXY"),
                                 ({"all_proxy": "socks5://proxy.example"}, "all_proxy"),
                                 ({"CLAUDE_CODE_EXTRA_BODY": '{"x": 1}'}, "CLAUDE_CODE_EXTRA_BODY"),
                                 ({"ANTHROPIC_BETAS": "x-2026-01-01"}, "ANTHROPIC_BETAS"),
                                 ({"CLAUDE_CODE_MANAGED_SETTINGS_PATH": "/tmp/managed"},
                                  "CLAUDE_CODE_MANAGED_SETTINGS_PATH"),
                                 ({"CLAUDE_CODE_REMOTE_SETTINGS_PATH": "/tmp/remote.json"},
                                  "CLAUDE_CODE_REMOTE_SETTINGS_PATH"),
                                 ({"CLAUDE_CODE_DISABLE_ADMIN_ENV_UNION": "1"}, "CLAUDE_CODE_DISABLE_ADMIN_ENV_UNION"),
                                 ({"CLAUDE_CODE_MOCK_REMOTE_SETTINGS": "1"}, "CLAUDE_CODE_MOCK_REMOTE_SETTINGS"),
                                 ({"ANTHROPIC_CUSTOM_HEADERS": "anthropic-beta: x"}, "ANTHROPIC_CUSTOM_HEADERS"),
                                 ({"CLAUDE_CODE_CUSTOM_OAUTH_URL": "https://claude.ai"},
                                  "CLAUDE_CODE_CUSTOM_OAUTH_URL"),
                                 ({"ANTHROPIC_UNIX_SOCKET": "/tmp/s"}, "ANTHROPIC_UNIX_SOCKET"),
                                 ({"CLAUDE_CODE_API_BASE_URL": "https://proxy.example"}, "CLAUDE_CODE_API_BASE_URL"),
                                 ({"_CLAUDE_CODE_ASSUME_FIRST_PARTY_BASE_URL": "1"},
                                  "_CLAUDE_CODE_ASSUME_FIRST_PARTY_BASE_URL"),
                                 ({"CLAUDE_CODE_USE_BEDROCK": "1"}, "CLAUDE_CODE_USE_BEDROCK"),
                                 ({"CLAUDE_CODE_USE_GATEWAY": "1", "ANTHROPIC_UNIX_SOCKET": "/s"},
                                  "ANTHROPIC_UNIX_SOCKET+CLAUDE_CODE_USE_GATEWAY")):
            with self.subTest(variables=variables):
                code, err, _ = self.run_agent([init()] + turn(1) + [result()], **variables)
                self.assertEqual(code, 4, err)
                self.assertIn(f"did not start the agent: the tool's environment or settings set {where}, which can "
                              f"send its requests elsewhere than {HOST}", err)
                self.assertFalse(os.path.exists(os.path.join(self.dir, "argv.json")), "the agent ran")
                self.assertEqual(self.read("served"), f"asked {ASKED}\nendpoint {where}\n")
                self.assertEqual(check(self.read("served"))[0], 1)

    def test_an_endpoint_a_settings_file_sets_starts_no_agent(self):
        """The tool applies the `env` of its settings files as it starts: the user's, and the checkout's."""
        for path in (os.path.join(self.dir, ".claude", "settings.json"),
                     os.path.join(self.dir, ".claude", "settings.local.json")):
            for settings, where in (({"env": {"ANTHROPIC_BASE_URL": "https://proxy.example"}}, "https:proxy.example"),
                                    ({"env": ["not", "a", "map"]}, "unreadable-settings"),
                                    ("{", "unreadable-settings")):
                with self.subTest(path=path, settings=settings):
                    os.makedirs(os.path.dirname(path), exist_ok=True)
                    with open(path, "w") as f:
                        f.write(settings if isinstance(settings, str) else json.dumps(settings))
                    self.addCleanup(lambda p=path: os.path.exists(p) and os.remove(p))
                    code, err, _ = self.run_agent([init()] + turn(1) + [result()])
                    os.remove(path)
                    self.assertEqual(code, 4, err)
                    self.assertIn(f"settings set {where}, which", err)
                    self.assertFalse(os.path.exists(os.path.join(self.dir, "argv.json")), "the agent ran")

    def test_an_endpoint_the_settings_of_claude_config_dir_set_starts_no_agent(self):
        config = os.path.join(self.dir, "config")
        os.mkdir(config)
        with open(os.path.join(config, "settings.json"), "w") as f:
            json.dump({"env": {"CLAUDE_CODE_USE_VERTEX": "1"}}, f)
        code, err, _ = self.run_agent([init()] + turn(1) + [result()], CLAUDE_CONFIG_DIR=config)
        self.assertEqual(code, 4, err)
        self.assertIn("settings set CLAUDE_CODE_USE_VERTEX, which", err)
        self.assertFalse(os.path.exists(os.path.join(self.dir, "argv.json")), "the agent ran")

    def test_the_provider_s_own_endpoint_named_or_in_settings_is_the_one_asked_for(self):
        os.makedirs(os.path.join(self.dir, ".claude"))
        with open(os.path.join(self.dir, ".claude", "settings.json"), "w") as f:
            json.dump({"env": {"ANTHROPIC_BASE_URL": "https://api.anthropic.com"}, "permissions": {}}, f)
        for base in ("https://api.anthropic.com", "https://api.anthropic.com/", "https://api.anthropic.com:443"):
            with self.subTest(base=base):
                code, err, _ = self.run_agent([init()] + turn(1) + [result()], ANTHROPIC_BASE_URL=base)
                self.assertEqual(code, 0, err)
                self.assertEqual(self.read("served"), f"{HEAD}usage firstParty/model-a-1\nfirstParty/model-a-1 1\n")

    def test_a_message_named_as_the_tool_s_own_but_not_marked_so_is_a_turn_of_another_model(self):
        """The model's name comes from the response: "<synthetic>" without the tool's own mark of an API error is a
        model's turn, and not of the model asked for (GateReview, finding 2)."""
        for mark in ({}, {"is_api_error_message": False}, {"is_api_error_message": "true"}):
            with self.subTest(mark=mark):
                unmarked = dict(turn(2, "<synthetic>")[0], **mark)
                events = [init()] + turn(1) + [unmarked, {"sleep": 100}, result()]
                code, err, seconds = self.run_agent(events)
                self.assertEqual(code, 4, err)
                self.assertLess(seconds, 60)
                self.assertIn("turn 2 was answered by ?synthetic?, not model-a-1", err)
                self.assertEqual(check(self.read("served"))[0], 1)

    def test_a_line_it_cannot_read_stops_the_agent_and_is_not_attributable(self):
        """A line of the stream that is not an event could hide a turn; a deeply nested one once crashed the reader
        with RecursionError and no record (GateReview, finding 5)."""
        for line, why in (("[" * 100000 + "]" * 100000, "nested too deeply to read"),
                          ('{"type": "assistant", "message": {"model": "other-b-1"', "not JSON")):
            with self.subTest(why=why):
                events = [init()] + turn(1) + [{"raw": line}, {"sleep": 100}] + turn(2) + [result()]
                code, err, seconds = self.run_agent(events)
                self.assertEqual(code, 4, err)
                self.assertLess(seconds, 60)
                self.assertIn(f"line 3 of its stream is {why}: what answered is not attributable", err)
                self.assertNotIn("Traceback", err)
                self.assertEqual(self.read("served"), f"{HEAD}none/model-a-1 1\n")
                self.assertEqual(self.read("review.json"), "")
                self.assertEqual(check(self.read("served"))[0], 3)

    def test_a_password_in_a_refused_base_url_is_never_shown(self):
        """The record, and so the log and the comment, name a refused URL's scheme, host and port, never its user or
        password (PubGateReview, S1)."""
        code, err, _ = self.run_agent([init()] + turn(1) + [result()],
                                      ANTHROPIC_BASE_URL="https://ci-bot:p4ssw0rdp4ssw0rd" + "@proxy.example:8443/v1")
        self.assertEqual(code, 4, err)
        self.assertEqual(self.read("served"), f"asked {ASKED}\nendpoint https:proxy.example:8443+userinfo\n")
        for text in (err, self.read("served"), check(self.read("served"))[1]):
            self.assertNotIn("p4ssw0rd", text)
            self.assertNotIn("ci-bot", text)

    def test_a_proxy_or_trust_a_settings_file_sets_starts_no_agent(self):
        """A proxy, with a CA it trusts, can answer as the API: the tool's settings set either (PubGateReview, S3)."""
        os.makedirs(os.path.join(self.dir, ".claude"))
        with open(os.path.join(self.dir, ".claude", "settings.json"), "w") as f:
            json.dump({"env": {"HTTPS_PROXY": "http://proxy.example", "NODE_EXTRA_CA_CERTS": "/tmp/ca.pem"}}, f)
        code, err, _ = self.run_agent([init()] + turn(1) + [result()])
        self.assertEqual(code, 4, err)
        self.assertIn("settings set HTTPS_PROXY+NODE_EXTRA_CA_CERTS, which can send its requests elsewhere than "
                      "api.anthropic.com", err)
        self.assertFalse(os.path.exists(os.path.join(self.dir, "argv.json")), "the agent ran")

    def test_the_base_url_of_the_anthropic_profile_is_an_endpoint(self):
        """The tool reads <config dir>/configs/<profile>.json's base_url (PubGateReview, S3)."""
        def profile(directory, name, url, active=None):
            os.makedirs(os.path.join(directory, "configs"), exist_ok=True)
            with open(os.path.join(directory, "configs", f"{name}.json"), "w") as f:
                json.dump({"base_url": url, "authentication": {"type": "user_oauth"}}, f)
            if active is not None:
                with open(os.path.join(directory, "active_config"), "w") as f:
                    f.write(active + "\n")
        home = os.path.join(self.dir, ".config", "anthropic")
        profile(home, "default", "https://proxy.example")
        code, err, _ = self.run_agent([init()] + turn(1) + [result()])
        self.assertEqual(code, 4, err)
        self.assertIn("settings set https:proxy.example, which", err)
        profile(home, "default", "https://api.anthropic.com")
        self.assertEqual(self.run_agent([init()] + turn(1) + [result()])[0], 0)
        profile(home, "work", "https://work.example", active="work")
        self.assertIn("https:work.example", self.run_agent([init()] + turn(1) + [result()])[1])
        named = os.path.join(self.dir, "named")
        profile(named, "other", "http://other.example")
        code, err, _ = self.run_agent([init()] + turn(1) + [result()], ANTHROPIC_CONFIG_DIR=named,
                                      ANTHROPIC_PROFILE="other")
        self.assertIn("http:other.example", err)
        with open(os.path.join(named, "configs", "other.json"), "w") as f:
            f.write("{")
        self.assertIn("unreadable-profile", self.run_agent([init()] + turn(1) + [result()], ANTHROPIC_CONFIG_DIR=named,
                                                           ANTHROPIC_PROFILE="other")[1])

    def test_another_model_of_the_family_stops_the_agent(self):
        events = [init()] + turn(1) + turn(2, "model-b-2") + [{"sleep": 100}, result()]
        code, err, seconds = self.run_agent(events)
        self.assertEqual(code, 4, err)
        self.assertLess(seconds, 60)
        self.assertIn("turn 2 was answered by model-b-2, not model-a-1", err)
        self.assertEqual(check(self.read("served"))[0], 1)

    def test_a_dated_snapshot_of_the_model_answers_for_it(self):
        code, err, _ = self.run_agent([init()] + turn(1, "model-a-1-20251001") + [result()])
        self.assertEqual(code, 0, err)

    def test_another_model_in_a_later_event_of_a_response_stops_the_agent(self):
        """The tool can switch models within a response: every event's model is checked, not only the first of its
        message id (PubGateReview, S4)."""
        switched = turn(1, blocks=2)
        switched[1]["message"] = dict(switched[1]["message"], model="other-b-1")
        code, err, seconds = self.run_agent([init()] + switched + [{"sleep": 100}, result()])
        self.assertEqual(code, 4, err)
        self.assertLess(seconds, 60)
        self.assertIn("turn 1 was answered by other-b-1", err)
        self.assertEqual(self.read("served"), f"{HEAD}none/other-b-1 1\n")

    def test_a_json_line_that_is_not_an_object_stops_the_agent(self):
        hidden = json.dumps(turn(2, "other-b-1"))
        code, err, seconds = self.run_agent([init()] + turn(1) + [{"raw": hidden}, {"sleep": 100}, result()])
        self.assertEqual(code, 4, err)
        self.assertLess(seconds, 60)
        self.assertIn("line 3 of its stream is not a JSON object", err)
        self.assertEqual(check(self.read("served"))[0], 3)

    def test_a_deeply_nested_result_is_kept_as_it_came(self):
        """A result that json.loads reads but json.dump cannot write again once crashed after the agent ended, with no
        record (PubGateReview, M2): review.json is the line as it came."""
        line = json.dumps(result())[:-1] + ', "deep": ' + "[" * 3000 + "]" * 3000 + "}"
        code, err, _ = self.run_agent([init()] + turn(1) + [{"raw": line}])
        self.assertEqual(code, 0, err)
        self.assertEqual(self.read("review.json"), line)
        self.assertEqual(self.read("served"), f"{HEAD}usage firstParty/model-a-1\nfirstParty/model-a-1 1\n")

    def test_a_provider_or_model_it_cannot_check_is_refused(self):
        for asked, status in ((ASKED, 0), ("openai/model-a-1", 2), ("anthropic/", 2), ("anthropic/none", 2),
                              ("anthropic/a b", 2)):
            with self.subTest(asked=asked):
                r = subprocess.run([sys.executable, SERVED, "asked", asked], capture_output=True, text=True)
                self.assertEqual(r.returncode, status, r.stderr)

    def test_a_server_fallback_to_another_model_within_a_response_stops_the_agent(self):
        """The API can hand a response to another model part way, with a content block naming it; the tool renames the
        response only when it asked for the fallback itself, so the event still names the model asked for."""
        handed = turn(2)
        handed[0]["message"]["content"] = [{"type": "fallback", "from": {"model": "model-a-1"},
                                            "to": {"model": "other-b-1"}}, {"type": "text", "text": "..."}]
        code, err, seconds = self.run_agent([init()] + turn(1) + handed + [{"sleep": 100}, result()])
        self.assertEqual(code, 4, err)
        self.assertLess(seconds, 60)
        self.assertIn("turn 2 was answered by other-b-1 (a server fallback within the response), not model-a-1", err)
        self.assertEqual(self.read("served"), f"{HEAD}none/model-a-1 1\nnone/other-b-1 1\n")
        self.assertEqual(check(self.read("served"))[0], 1)
        # A fallback to the model asked for is no other model.
        handed[0]["message"]["content"][0]["to"]["model"] = "model-a-1"
        self.assertEqual(self.run_agent([init()] + turn(1) + handed + [result()])[0], 0)

    def test_a_setting_that_lets_another_model_answer_starts_no_agent(self):
        """advisorModel, and a policy helper (which managed settings use to give the tool settings, an env among them),
        in any settings file the script reads; /etc/claude-code's files are read the same way."""
        os.makedirs(os.path.join(self.dir, ".claude"))
        for key, value in (("advisorModel", "other-b-1"),
                           ("policyHelper", {"default": {"env": {"ANTHROPIC_BASE_URL": "https://proxy.example"}}}),
                           ("policyHelpers", [{"command": "/usr/local/bin/settings"}])):
            with self.subTest(key=key):
                with open(os.path.join(self.dir, ".claude", "settings.json"), "w") as f:
                    json.dump({key: value}, f)
                code, err, _ = self.run_agent([init()] + turn(1) + [result()])
                self.assertEqual(code, 4, err)
                self.assertIn(f"settings set {key}, which can send its requests elsewhere than api.anthropic.com or "
                              "let another model answer", err)
                self.assertFalse(os.path.exists(os.path.join(self.dir, "argv.json")), "the agent ran")

    def test_a_usage_entry_that_is_not_an_object_is_not_attributable(self):
        side = result()
        side["modelUsage"]["model-a-1-20251001"] = None
        code, err, _ = self.run_agent([init()] + turn(1) + [side])
        self.assertEqual(code, 4, err)
        self.assertIn("usage none/model-a-1-20251001\n", self.read("served"))
        self.assertIn("firstParty+none/model-a-1 1\n", self.read("served"))
        self.assertNotEqual(check(self.read("served"))[0], 0)

    def test_a_long_name_that_the_record_cuts_to_the_model_asked_for_is_another(self):
        """The record cuts a name to 100 characters; the stream's own name is compared."""
        asked = "model-" + "a" * 94
        code, err, _ = self.run_agent([init()] + turn(1, asked + "-evil") + [{"sleep": 100}, result()],
                                      asked=f"anthropic/{asked}")
        self.assertEqual(code, 4, err)

    def test_the_profile_under_xdg_config_home_is_read(self):
        xdg = os.path.join(self.dir, "xdg")
        os.makedirs(os.path.join(xdg, "anthropic", "configs"))
        with open(os.path.join(xdg, "anthropic", "configs", "default.json"), "w") as f:
            json.dump({"base_url": "https://proxy.example"}, f)
        code, err, _ = self.run_agent([init()] + turn(1) + [result()], XDG_CONFIG_HOME=xdg)
        self.assertEqual(code, 4, err)
        self.assertIn("https:proxy.example", err)

    def test_the_env_of_the_global_config_is_read(self):
        """The tool applies the `env` of its global config, ~/.claude.json, as it starts, like a settings file's."""
        for directory, variables in ((self.dir, {}), (os.path.join(self.dir, "config"),
                                                      {"CLAUDE_CONFIG_DIR": os.path.join(self.dir, "config")})):
            with self.subTest(directory=directory):
                os.makedirs(directory, exist_ok=True)
                path = os.path.join(directory, ".claude.json")
                with open(path, "w") as f:
                    json.dump({"env": {"ANTHROPIC_BASE_URL": "https://proxy.example"}, "numStartups": 3}, f)
                code, err, _ = self.run_agent([init()] + turn(1) + [result()], **variables)
                os.remove(path)
                self.assertEqual(code, 4, err)
                self.assertIn("settings set https:proxy.example, which", err)
                self.assertFalse(os.path.exists(os.path.join(self.dir, "argv.json")), "the agent ran")
        with open(os.path.join(self.dir, ".claude.json"), "w") as f:
            json.dump({"numStartups": 3, "env": {}}, f)
        self.assertEqual(self.run_agent([init()] + turn(1) + [result()])[0], 0)

    def test_the_env_of_every_file_the_global_config_can_come_from_is_read(self):
        """The tool takes its global config from .config.json in its config home when that is not empty, and names
        .claude.json after its OAuth setting (.claude-custom-oauth.json, for one): each is read."""
        config = os.path.join(self.dir, "config")
        for path, variables in ((os.path.join(self.dir, ".claude", ".config.json"), {}),
                                (os.path.join(config, ".config.json"), {"CLAUDE_CONFIG_DIR": config}),
                                (os.path.join(self.dir, ".claude-custom-oauth.json"), {}),
                                (os.path.join(self.dir, ".claude-staging-oauth.json"), {}),
                                (os.path.join(config, ".claude-local-oauth.json"), {"CLAUDE_CONFIG_DIR": config})):
            with self.subTest(path=path):
                os.makedirs(os.path.dirname(path), exist_ok=True)
                with open(path, "w") as f:
                    json.dump({"env": {"ANTHROPIC_BASE_URL": "https://proxy.example"}}, f)
                code, err, _ = self.run_agent([init()] + turn(1) + [result()], **variables)
                os.remove(path)
                self.assertEqual(code, 4, err)
                self.assertIn("settings set https:proxy.example, which", err)
                self.assertFalse(os.path.exists(os.path.join(self.dir, "argv.json")), "the agent ran")
        # An empty .config.json holds no env: the tool reads none from it, and it refuses nothing.
        os.makedirs(os.path.join(self.dir, ".claude"), exist_ok=True)
        open(os.path.join(self.dir, ".claude", ".config.json"), "w").close()
        self.assertEqual(self.run_agent([init()] + turn(1) + [result()])[0], 0)

    def test_a_fallback_block_or_content_that_hides_its_model_stops_the_agent(self):
        """A fallback block whose `to` names no model, and content that is not a list, could hide another model."""
        for content in ([{"type": "fallback", "from": {"model": "model-a-1"}, "to": "other-b-1"}],
                        [{"type": "fallback", "from": {"model": "model-a-1"}}], {"type": "text", "text": "..."}):
            with self.subTest(content=content):
                hidden = turn(1)
                hidden[0]["message"]["content"] = content
                code, err, seconds = self.run_agent([init()] + hidden + [{"sleep": 100}, result()])
                self.assertEqual(code, 4, err)
                self.assertLess(seconds, 60)
                self.assertIn("turn 1 was answered by no model it named", err)

    def test_a_stale_record_is_gone_also_when_no_agent_starts(self):
        for name in ("served", "review.json"):
            with open(os.path.join(self.review, name), "w") as f:
                f.write(f"{HEAD}usage firstParty/model-a-1\nfirstParty/model-a-1 9\n")
        self.run_agent([init()] + turn(1) + [result()], ANTHROPIC_BASE_URL="https://proxy.example")
        self.assertEqual(self.read("served"), f"asked {ASKED}\nendpoint https:proxy.example\n")
        self.assertEqual(self.read("review.json"), "")

    def test_a_variable_of_the_tool_s_own_that_is_not_allowed_starts_no_agent(self):
        """Of the tool's own variables only credentials and knobs that move no request are allowed: any other, a new
        one included, is refused (a host's credentials file, for one, sets the base URL another way)."""
        for variables in ({"CLAUDE_CODE_PROVIDER_MANAGED_BY_HOST": "1", "CLAUDE_CODE_HOST_CREDS_FILE": "/tmp/c.json"},
                          {"CLAUDE_CODE_SOMETHING_NEW": "1"}, {"ANTHROPIC_MODEL": "other-b-1"},
                          {"ANTHROPIC_PROFILE": "work"}):
            with self.subTest(variables=variables):
                code, err, _ = self.run_agent([init()] + turn(1) + [result()], **variables)
                self.assertEqual(code, 4, err)
                self.assertIn(f"settings set {'+'.join(sorted(variables))}, which", err)
                self.assertFalse(os.path.exists(os.path.join(self.dir, "argv.json")), "the agent ran")
        # The same in a settings file's env.
        os.makedirs(os.path.join(self.dir, ".claude"), exist_ok=True)
        with open(os.path.join(self.dir, ".claude", "settings.json"), "w") as f:
            json.dump({"env": {"CLAUDE_CODE_HOST_CREDS_FILE": "/tmp/c.json"}}, f)
        code, err, _ = self.run_agent([init()] + turn(1) + [result()])
        self.assertEqual(code, 4, err)
        self.assertIn("settings set CLAUDE_CODE_HOST_CREDS_FILE, which", err)
        self.assertFalse(os.path.exists(os.path.join(self.dir, "argv.json")), "the agent ran")
        os.remove(os.path.join(self.dir, ".claude", "settings.json"))
        # The credentials and knobs that are allowed.
        allowed = {"ANTHROPIC_API_KEY": "k", "ANTHROPIC_AUTH_TOKEN": "t", "CLAUDE_CODE_OAUTH_TOKEN": "o",
                   "ANTHROPIC_IDENTITY_TOKEN_FILE": "/tmp/jwt", "ANTHROPIC_FEDERATION_RULE_ID": "fdrl_x",
                   "ANTHROPIC_ORGANIZATION_ID": "o", "ANTHROPIC_SERVICE_ACCOUNT_ID": "svac_x",
                   "ANTHROPIC_WORKSPACE_ID": "wrkspc_x", "ANTHROPIC_SCOPE": "workspace:inference",
                   "CLAUDE_CODE_ENABLE_TELEMETRY": "1", "CLAUDE_CODE_MAX_OUTPUT_TOKENS": "1000",
                   "ANTHROPIC_BASE_URL": "https://api.anthropic.com"}
        code, err, _ = self.run_agent([init()] + turn(1) + [result()], **allowed)
        self.assertEqual(code, 0, err)

    def test_a_global_config_that_moves_the_profile_starts_no_agent(self):
        """HOME or XDG_CONFIG_HOME in a global config's env moves the folder of the Anthropic profile the tool reads,
        and so its base_url; in the process environment the script follows them itself."""
        for path in (os.path.join(self.dir, ".claude.json"), os.path.join(self.dir, ".claude", ".config.json")):
            for name in ("XDG_CONFIG_HOME", "HOME"):
                with self.subTest(path=path, name=name):
                    os.makedirs(os.path.dirname(path), exist_ok=True)
                    with open(path, "w") as f:
                        json.dump({"env": {name: os.path.join(self.dir, "elsewhere")}}, f)
                    code, err, _ = self.run_agent([init()] + turn(1) + [result()])
                    os.remove(path)
                    self.assertEqual(code, 4, err)
                    self.assertIn(f"settings set {name}, which", err)
                    self.assertFalse(os.path.exists(os.path.join(self.dir, "argv.json")), "the agent ran")
        code, err, _ = self.run_agent([init()] + turn(1) + [result()], XDG_CONFIG_HOME=os.path.join(self.dir, "x"))
        self.assertEqual(code, 0, err)

    def gone(self, pid):
        """Whether the process `pid` has ended (and been reaped), waiting up to 10 seconds."""
        for _ in range(100):
            try:
                os.kill(pid, 0)
            except ProcessLookupError:
                return True
            time.sleep(0.1)
        return False

    def test_a_stopped_agent_s_own_processes_are_stopped_too(self):
        """A process the agent started holds the stream open after the agent ends: it is stopped with the agent."""
        events = [init(), {"child": 600}] + turn(1, "other-b-1") + [{"sleep": 600}]
        code, err, seconds = self.run_agent(events)
        self.assertEqual(code, 4, err)
        self.assertLess(seconds, 60)
        with open(os.path.join(self.dir, "pids")) as f:
            pids = [int(p) for p in f.read().split()]
        self.assertEqual(len(pids), 2)
        for pid in pids:
            self.assertTrue(self.gone(pid), f"process {pid} still runs")

    def test_a_stop_of_the_script_stops_the_agent(self):
        """The step's timeout or a cancelled run stops facts-review-served with SIGTERM: the agent goes with it."""
        agent = self.agent("agent", [init(), {"child": 600}] + turn(1) + [{"sleep": 600}])
        served = subprocess.Popen([sys.executable, SERVED, "run", self.review, ASKED, "--", agent],
                                  env=environment(HOME=self.dir), cwd=self.dir, stderr=subprocess.DEVNULL)
        self.addCleanup(served.kill)
        for _ in range(100):
            if os.path.exists(os.path.join(self.review, "review.jsonl")) and "msg_0001" in self.read("review.jsonl"):
                break
            time.sleep(0.1)
        served.terminate()
        self.assertEqual(served.wait(timeout=60), 143)
        # What answered until the stop is recorded (PubGateReview, M3).
        self.assertEqual(self.read("served"), f"{HEAD}none/model-a-1 1\n")
        with open(os.path.join(self.dir, "pids")) as f:
            for pid in map(int, f.read().split()):
                self.assertTrue(self.gone(pid), f"process {pid} still runs")


def load_served():
    """review-served as a module, so that a test can point the folders it reads at its own."""
    loader = importlib.machinery.SourceFileLoader("review_served", SERVED)
    module = importlib.util.module_from_spec(importlib.util.spec_from_loader("review_served", loader))
    loader.exec_module(module)
    return module


class Managed(unittest.TestCase):
    """endpoint() reads the tool's managed settings where the tool does: the platform's folder (on macOS its own), and
    under WSL also Windows' folder and registry keys."""
    PROXY = {"env": {"ANTHROPIC_BASE_URL": "https://proxy.example"}}

    def setUp(self):
        self._tmp = tempfile.TemporaryDirectory(prefix="served-managed-")
        self.dir = os.path.realpath(self._tmp.name)
        self.addCleanup(self._tmp.cleanup)
        self.served = load_served()
        self.served.MANAGED = {name: os.path.join(self.dir, name) for name in ("darwin", "linux", "wsl")}
        self.served.REG = os.path.join(self.dir, "reg.exe")
        self.served.PLATFORM = "linux"
        self.served.under_wsl = lambda: False
        home = os.path.join(self.dir, "home")
        os.mkdir(home)
        self.environ = environment(HOME=home)
        cwd = os.getcwd()
        os.chdir(self.dir)
        self.addCleanup(os.chdir, cwd)

    def endpoint(self):
        saved = dict(os.environ)
        os.environ.clear()
        os.environ.update(self.environ)
        try:
            return self.served.endpoint(HOST)
        finally:
            os.environ.clear()
            os.environ.update(saved)

    def write(self, *parts, content=None):
        path = os.path.join(self.dir, *parts)
        os.makedirs(os.path.dirname(path), exist_ok=True)
        with open(path, "w") as f:
            f.write(content if content is not None else json.dumps(self.PROXY))
        return path

    def reg(self, status, output=""):
        """A stand-in reg.exe that prints `output` and exits with `status`."""
        with open(os.path.join(self.dir, "reg.out"), "w", newline="") as f:
            f.write(output)
        with open(self.served.REG, "w") as f:
            f.write(f"#!/bin/sh\ncat '{self.dir}/reg.out'\nexit {status}\n")
        os.chmod(self.served.REG, 0o755)

    def test_the_platform_s_managed_settings_are_read(self):
        self.assertEqual(self.endpoint(), HOST)
        for platform, parts in (("linux", ("linux", "managed-settings.json")),
                                ("linux", ("linux", "managed-settings.d", "10-proxy.json")),
                                ("darwin", ("darwin", "managed-settings.json"))):
            with self.subTest(platform=platform, parts=parts):
                self.served.PLATFORM = platform
                path = self.write(*parts)
                self.assertEqual(self.endpoint(), "https:proxy.example")
                os.remove(path)

    def test_windows_managed_settings_are_read_under_wsl_only(self):
        self.write("wsl", "managed-settings.json")
        self.assertEqual(self.endpoint(), HOST)
        self.served.under_wsl = lambda: True
        self.assertEqual(self.endpoint(), "https:proxy.example")

    def test_the_windows_registry_is_read_under_wsl_only(self):
        line = "\r\nHKEY_LOCAL_MACHINE\\SOFTWARE\\Policies\\ClaudeCode\r\n    Settings    REG_SZ    " + \
            json.dumps(self.PROXY) + "\r\n"
        self.reg(0, line)
        self.assertEqual(self.endpoint(), HOST)
        self.served.under_wsl = lambda: True
        self.assertEqual(self.endpoint(), "https:proxy.example")
        self.reg(1)   # no such key: nothing set
        self.assertEqual(self.endpoint(), HOST)
        self.reg(0, "something else")   # an answer it cannot read: refused
        self.assertEqual(self.endpoint(), "unreadable-registry")
        self.reg(0, "    Settings    REG_SZ    {not json")
        self.assertEqual(self.endpoint(), "unreadable-registry")
        # The tool's own parse: the name in any case, and a value over several lines.
        self.reg(0, "\r\n    settings    REG_SZ    " + json.dumps(self.PROXY, indent=2) + "\r\n")
        self.assertEqual(self.endpoint(), "https:proxy.example")
        self.reg(0, "    Settings    REG_SZ    {}\r\n{}\r\n")   # two objects: the tool starts on neither
        self.assertEqual(self.endpoint(), "unreadable-registry")
        self.reg(2, "ERROR")
        self.assertEqual(self.endpoint(), "unreadable-registry")
        self.served.REG_TIMEOUT = 0.5
        with open(self.served.REG, "w") as f:
            f.write("#!/bin/sh\nsleep 5\n")
        self.assertEqual(self.endpoint(), "unreadable-registry")

    def test_a_platform_whose_folders_it_does_not_know_refuses(self):
        for platform in ("win32", "cygwin", "msys"):
            with self.subTest(platform=platform):
                self.served.PLATFORM = platform
                self.assertEqual(self.endpoint(), "unsupported-platform")
        code, line = self.served.check(f"asked {ASKED}\nendpoint unsupported-platform\n")
        self.assertEqual(code, 1)
        self.assertIn("a platform where nothing shows where the tool reads its settings", line)

    def test_a_registry_env_that_is_no_object_names_the_registry(self):
        self.served.under_wsl = lambda: True
        self.reg(0, "    Settings    REG_SZ    " + json.dumps({"env": ["x"]}))
        self.assertEqual(self.endpoint(), "unreadable-registry")


class Check(unittest.TestCase):
    def test_a_record_with_no_asked_line_is_not_attributable(self):
        self.assertEqual(check("firstParty/model-a-1 3\n")[0], 3)
        self.assertEqual(check("")[0], 3)

    def test_a_line_that_is_not_one_is_not_attributable(self):
        self.assertEqual(check(f"{HEAD}firstParty/model-a-1 three\n")[0], 3)

    def test_a_line_of_no_turns_is_not_attributable(self):
        """run never writes a count of 0, so only a hand-written or damaged record holds one: no turn is no evidence,
        whatever the other lines say (FailOpenTests, at c25b831bc7)."""
        for record in (f"{HEAD}firstParty/model-a-1 0\n",
                       f"{HEAD}usage firstParty/model-a-1\nfirstParty/model-a-1 0\n",
                       f"{HEAD}firstParty/model-a-1 3\nfirstParty/model-a-1 0\n",
                       f"{HEAD}firstParty/model-a-1 00\n"):
            with self.subTest(record=record):
                self.assertEqual(check(record)[0], 3)

    def test_another_model_of_the_same_family_is_another_model(self):
        """The review asked for one model: another of its family (a fallback model, say) is another (PubGateReview,
        B1)."""
        for record in (f"{HEAD}firstParty/model-a-1 3\nfirstParty/model-b-2 1\n",
                       f"{HEAD}usage firstParty/model-b-2\nfirstParty/model-a-1 3\n",
                       f"{HEAD}firstParty/model-a-1-x 3\n", f"{HEAD}firstParty/modelx-a-1 3\n",
                       f"{HEAD}firstParty/model-a-1-2025010 3\n"):
            with self.subTest(record=record):
                self.assertEqual(check(record)[0], 1)

    def test_a_dated_snapshot_of_the_model_is_the_model(self):
        self.assertEqual(check(f"{HEAD}usage firstParty/model-a-1\nfirstParty/model-a-1-20251001 3\n"),
                         (0, "firstParty/model-a-1-20251001 (3 turns)"))

    def test_a_usage_entry_that_names_no_model_is_not_attributable(self):
        self.assertEqual(check(f"{HEAD}usage firstParty/none\nfirstParty/model-a-1 3\n")[0], 3)

    def test_a_record_with_no_usage_line_is_not_attributable(self):
        """run writes a usage line for each entry of the tool's .modelUsage; with none, nothing names the provider."""
        code, line = check(f"{HEAD}firstParty/model-a-1 3\n")
        self.assertEqual(code, 3, line)
        self.assertIn("the tool's usage names nothing", line)

    def test_a_count_of_digits_that_are_not_ascii_is_not_attributable_and_no_crash(self):
        """str.isdigit takes "²" for a digit and int() does not: that once crashed check with exit 1, which is the
        exit of another provider (GateReview, finding 4)."""
        code, line = check(f"asked {ASKED}\nfirstParty/model-a-1 ²\n")
        self.assertEqual(code, 3, line)
        self.assertIn("a line of the record of what answered the review is not one", line)

    def test_a_record_that_names_another_endpoint_is_another_provider(self):
        code, line = check(f"asked {ASKED}\nendpoint https:proxy.example\nfirstParty/model-a-1 3\n")
        self.assertEqual(code, 1, line)
        self.assertIn(f"whose API is {HOST}, but the tool's environment or settings set https:proxy.example, which can "
                      "send its requests elsewhere or let another model answer, and firstParty/model-a-1 (3 turns) "
                      "answered", line)
        self.assertEqual(check(f"{HEAD}endpoint https:proxy.example\nfirstParty/model-a-1 3\n")[0], 1)

    def test_a_record_that_names_no_endpoint_is_not_attributable(self):
        code, line = check(f"asked {ASKED}\nusage firstParty/model-a-1\nfirstParty/model-a-1 3\n")
        self.assertEqual(code, 3, line)
        self.assertIn("nothing recorded where the tool sent its requests", line)


@unittest.skipUnless(shutil.which("jq"), "jq is not installed")
class RunScript(StandIn):
    """facts-review-run with a stand-in for the review agent's tool on PATH, under the command's name."""

    def review_run(self, events, **variables):
        self.agent(TOOL, events)
        with open(os.path.join(self.review, "changed.txt"), "w") as f:
            f.write("M\tprojects/zlib/project.yaml\n")
        env = environment(PATH=self.bin + os.pathsep + os.environ["PATH"], HOME=self.dir, PR="7",
                          REVIEW_MODEL="model-a-1", **variables)
        env.pop("REVIEW_PROVIDER", None)
        r = subprocess.run(["bash", RUN, ".review"], cwd=self.dir, env=env, capture_output=True, text=True,
                           timeout=120)
        return r.returncode, r.stdout + r.stderr

    def no_comment(self):
        """No review is in comment.md: it is not there, or empty."""
        path = os.path.join(self.review, "comment.md")
        self.assertFalse(os.path.exists(path) and os.path.getsize(path), "a comment was written")

    def test_a_review_the_provider_asked_for_answered_is_written_with_what_answered(self):
        events = [init()] + turn(1) + turn(2, blocks=2) + [result()]
        code, out = self.review_run(events)
        self.assertEqual(code, 0, out)
        self.assertEqual(self.read("comment.md").strip(), REVIEW.strip())
        self.assertIn(f"asked for {ASKED}, answered by firstParty/model-a-1 (2 turns),", out)
        with open(os.path.join(self.dir, "argv.json")) as f:
            argv = json.load(f)
        self.assertIn("--verbose", argv)
        self.assertEqual(argv[argv.index("--output-format") + 1], "stream-json")
        self.assertEqual(argv[argv.index("--model") + 1], "model-a-1")

    def test_a_review_another_model_answered_writes_no_comment(self):
        events = [init()] + turn(1, "other-b-1") + [{"sleep": 100}, result()]
        code, out = self.review_run(events)
        self.assertEqual(code, 4, out)
        self.assertIn("turn 1 was answered by other-b-1", out)
        self.no_comment()

    def test_a_base_url_of_a_proxy_starts_no_agent_and_writes_no_comment(self):
        code, out = self.review_run([init()] + turn(1) + [result()], ANTHROPIC_BASE_URL="https://proxy.example/v1")
        self.assertEqual(code, 4, out)
        self.assertIn("did not start the agent: the tool's environment or settings set https:proxy.example", out)
        self.assertFalse(os.path.exists(os.path.join(self.dir, "argv.json")), "the agent ran")
        self.no_comment()


class Comment(StandIn):
    """facts-review-comment: the review is posted only with a record that shows the provider asked for."""

    def comment(self, review, record=None, why=""):
        path = os.path.join(self.dir, "review.md")
        with open(path, "w") as f:
            f.write(review)
        env = {k: v for k, v in environment().items() if k != "SERVED"}
        env.update(HEAD_SHA="a" * 40, BASE_REF="main")
        if record is not None:
            env["SERVED"] = record
        r = subprocess.run(["bash", COMMENT, path, why], env=env, capture_output=True, text=True)
        self.assertEqual(r.returncode, 0, r.stderr)
        return r.stdout

    def test_a_review_the_provider_asked_for_answered_is_posted_with_what_answered(self):
        out = self.comment(REVIEW, f"{HEAD}usage firstParty/model-a-1\nfirstParty/model-a-1 112\n")
        self.assertIn(REVIEW, out)
        self.assertIn("Answered by firstParty/model-a-1 (112 turns), as the review agent's tool reported it.", out)

    def test_a_review_another_provider_answered_is_not_posted(self):
        out = self.comment(REVIEW, f"{HEAD}firstParty/model-a-1 3\nfirstParty/other-b-1 2\n")
        self.assertNotIn(REVIEW.strip(), out)
        lines = out.strip().splitlines()
        self.assertEqual(lines[:2], ["<!-- facts-review -->", "## Facts review"])
        self.assertEqual(len([line for line in lines[2:] if line]), 1, out)
        self.assertIn("review of this push of commit aaaaaaaaaaaa against `main` is not published: it asked for "
                      f"{ASKED}, which the tool calls firstParty/model-a-1, but firstParty/model-a-1 (3 turns), "
                      "firstParty/other-b-1 (2 turns) answered, and the tool's usage names nothing.", out)

    def test_a_review_whose_record_names_no_turn_is_not_posted(self):
        out = self.comment(REVIEW, HEAD)
        self.assertNotIn(REVIEW.strip(), out)
        self.assertIn("is not published: it asked for anthropic/model-a-1, and no turn named the provider", out)

    def test_a_review_with_no_record_is_not_posted(self):
        for record in (None, ""):
            with self.subTest(record=record):
                out = self.comment(REVIEW, record)
                self.assertNotIn(REVIEW.strip(), out)
                self.assertIn("is not published: nothing recorded which provider answered the review", out)

    def test_a_review_stopped_at_another_provider_says_so_rather_than_that_the_job_failed(self):
        out = self.comment("", f"{HEAD}none/other-b-1 1\n",
                           why="the review job ended with the result failure")
        self.assertIn("is not published: it asked for anthropic/model-a-1", out)
        self.assertNotIn("the review job ended", out)

    def test_no_review_names_what_answered_or_that_nothing_did(self):
        """Every comment names what answered, the one that says there is no review too (GateReview, finding 3)."""
        why = "did not review this push of commit aaaaaaaaaaaa against `main`: the review job ended with the result " \
              "failure. What answered it, as the review agent's tool reported it: "
        for record, answered in ((None, "nothing recorded which provider answered the review: it is not attributable"),
                                 (HEAD, "it asked for anthropic/model-a-1, and no turn named the provider"),
                                 (f"{HEAD}none/model-a-1 4\n",
                                  "it asked for anthropic/model-a-1, and none/model-a-1 (4 turns) answered, "
                                  "where none"),
                                 (f"{HEAD}usage firstParty/model-a-1\nfirstParty/model-a-1 2\n",
                                  "firstParty/model-a-1 (2 turns). The maintainers")):
            with self.subTest(record=record):
                out = self.comment("", record, why="the review job ended with the result failure")
                self.assertIn(why + answered, out)

    def test_a_review_whose_record_check_cannot_count_is_not_published_rather_than_failed(self):
        """A count of non-ASCII digits once crashed check with exit 1, and the comment said the job failed."""
        out = self.comment(REVIEW, f"asked {ASKED}\nfirstParty/model-a-1 ²\n")
        self.assertNotIn(REVIEW.strip(), out)
        self.assertIn("is not published: a line of the record of what answered the review is not one", out)

    def test_a_check_that_cannot_run_shows_nothing_and_posts_nothing(self):
        """facts-review-comment alone, with no facts-review-served beside it: the record cannot be checked."""
        alone = os.path.join(self.dir, "alone")
        os.mkdir(alone)
        shutil.copy(COMMENT, alone)
        path = os.path.join(self.dir, "review.md")
        for review, why, said in ((REVIEW, "", "is not published: facts-review-served could not check the record of "
                                                "what answered: it is not attributable"),
                                  ("", "the review job ended with the result failure",
                                   "What answered it, as the review agent's tool reported it: facts-review-served "
                                   "could not check the record")):
            with self.subTest(review=review):
                with open(path, "w") as f:
                    f.write(review)
                env = dict(environment(), HEAD_SHA="a" * 40, BASE_REF="main",
                           SERVED=f"{HEAD}usage firstParty/model-a-1\nfirstParty/model-a-1 2\n")
                r = subprocess.run(["bash", os.path.join(alone, "facts-review-comment"), path, why], env=env,
                                   capture_output=True, text=True)
                self.assertEqual(r.returncode, 0, r.stderr)
                self.assertNotIn(REVIEW.strip(), r.stdout)
                self.assertIn(said, r.stdout)

    def test_a_review_through_another_endpoint_is_not_posted(self):
        out = self.comment(REVIEW, f"asked {ASKED}\nendpoint https:proxy.example\nfirstParty/model-a-1 2\n")
        self.assertNotIn(REVIEW.strip(), out)
        self.assertIn("is not published: it asked for anthropic/model-a-1, whose API is api.anthropic.com, but the "
                      "tool's environment or settings set https:proxy.example", out)


if __name__ == "__main__":
    unittest.main()
