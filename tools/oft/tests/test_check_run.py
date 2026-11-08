"""check_run.py (oft prove --post-check): the report of `oft prove` as the pull request check theorem/prove, a GitHub
check run on the change's head commit."""
import contextlib
import http.server
import io
import json
import os
import re
import subprocess
import sys
import threading
import unittest
from unittest import mock

from oft import __main__ as cli
from oft import check_run, classify, keys, prove, symbols
from oft.tests.helpers import tree
from oft.tests.test_contracts import LIB, contract_repo, put_row
from oft.tests.test_keys import TOOLS, UNIT, commit

BASE, HEAD = "a" * 40, "b" * 40
# the head commit of the pull request the check goes on (a commit of another repository than the report's)
SHA = "0123456789abcdef0123456789abcdef01234567"
NEUTRAL = ("Every contract that is not unchanged is data changed: Rocq decides whether its proofs still hold, and no "
           "agent is predicted.\n\n")
# a token whose every display a test looks for, and the tokens no request may carry: empty, or with whitespace, a
# control character or a character outside ASCII
SECRET = "ghs_s3cr3tTOKENx9"
MALFORMED = ("", " ", SECRET + "\n", "\n" + SECRET, "ghs_s3cr3t TOKENx9", SECRET + "\t", "ghs_s3cr3t\x00TOKENx9",
             "ghs_s3cr3tTOKENé9", SECRET + "\r")


def report(*states, functions=(), unit=UNIT):
    """A Report of unit with one contract in each of states and one function of the plain build of each class in
    functions."""
    p, h = unit.split("/")
    lib = LIB.replace("zlib/checksum_fuzzer", "%s/%s" % (p, h))
    contracts = [{"file": "%s/Prog/c%d_c.v" % (lib, i), "state": s, "why": "stand-in", "base": None, "changed": None,
                  "references": [], "functions": []} for i, s in enumerate(states)]
    rows = []
    for i, cls in enumerate(functions):
        sym = symbols.Sym("f%d" % i, "func", 0x11270 + 16 * i, 8, "1e" * 32, "2d" * 32, "-",
                          "zlib/f.c:%d-%d" % (i, i + 1))
        rows.append(("plain", classify.Row(cls, ("f%d" % i,), None if cls == "added" else sym,
                                           None if cls == "removed" else sym)))
    counts = dict.fromkeys(classify.CLASSES, 0)
    for cls in functions:
        counts[cls] += 1
    return prove.Report(unit, BASE, HEAD, rows, contracts, counts)


class StandIn(http.server.BaseHTTPRequestHandler):
    """GitHub's REST API as far as one POST: records each request, with its target as the client sent it (not
    self.path, which http.server reduces from //repos/... to /repos/...), and answers with the server's reply for that
    target (server.replies), else its one reply; with the server's mode "cut", a Content-Length 100 bytes over the
    body, so the answer ends short, and with "garbage", a line that is no HTTP answer, holding SECRET."""

    def do_POST(self):
        body = self.rfile.read(int(self.headers["Content-Length"]))
        self.server.requests.append((self.command, self.requestline.split()[1],
                                     {k.lower(): v for k, v in self.headers.items()}, json.loads(body)))
        if self.server.mode == "garbage":
            self.wfile.write(b"garbage " + SECRET.encode() + b"\r\n")
            return
        status, headers, reply = self.server.replies.get(self.requestline.split()[1], self.server.reply)
        data = json.dumps(reply).encode()
        length = len(data) + (100 if self.server.mode == "cut" else 0)
        self.send_response(status)
        for k, v in dict(headers, **{"Content-Type": "application/json", "Content-Length": str(length)}).items():
            self.send_header(k, v)
        self.end_headers()
        self.wfile.write(data)

    def log_message(self, *args):
        pass


def created(repo, sha, check_id=4242):
    """GitHub's answer to a POST that made a check run: the check run, in the fields a create returns."""
    return {"id": check_id, "head_sha": sha, "node_id": "CR_stand-in", "external_id": "",
            "url": "https://api.github.com/repos/%s/check-runs/%d" % (repo, check_id),
            "html_url": "https://github.com/%s/runs/%d" % (repo, check_id), "details_url": "https://github.com/apps/x",
            "status": "completed", "conclusion": "success", "started_at": "2026-10-31T00:00:00Z",
            "completed_at": "2026-10-31T00:00:00Z", "output": {"title": "t", "summary": "s", "text": None,
                                                               "annotations_count": 0, "annotations_url": ""},
            "name": "theorem/prove: " + UNIT, "check_suite": {"id": 1}, "app": {"slug": "x"}, "pull_requests": []}


@contextlib.contextmanager
def github(status=201, reply=None, headers=None, mode=None, replies=None):
    """A stand-in for GitHub's REST API on a free local port: (the server, with .requests, and its base URL).  replies
    is {repository: (status, reply)} for the POSTs to that repository's /check-runs, each made check run's id 4242
    plus its place in replies."""
    server = http.server.ThreadingHTTPServer(("127.0.0.1", 0), StandIn)
    server.requests, server.mode = [], mode
    server.reply = (status, headers or {}, created("example/libreac", SHA) if reply is None else reply)
    server.replies = {"/repos/%s/check-runs" % repo: (s, {}, created(repo, SHA, 4242 + i) if r is None else r)
                      for i, (repo, (s, r)) in enumerate((replies or {}).items())}
    thread = threading.Thread(target=server.serve_forever, daemon=True)
    thread.start()
    try:
        yield server, "http://127.0.0.1:%d" % server.server_address[1]
    finally:
        server.shutdown()
        server.server_close()
        thread.join()


class Payload(unittest.TestCase):
    """check_run.payload: the check run `theorem/prove: <unit>`, completed, with a conclusion, a title that counts and
    the report's Markdown as its summary."""

    def test_no_work_is_success(self):
        """No contract predicts work, whatever functions moved or are identical, and also with no contract at all."""
        for r in (report("unchanged", "unchanged", functions=("moved", "identical")), report()):
            with self.subTest(contracts=len(r.contracts)):
                self.assertEqual(check_run.payload(r, SHA),
                                 {"name": "theorem/prove: zlib/checksum_fuzzer", "head_sha": SHA,
                                  "status": "completed", "conclusion": "success",
                                  "output": {"title": "0 contracts need work, 0 functions changed",
                                             "summary": prove.markdown(r)}})

    def test_each_unit_has_a_check_of_its_own(self):
        """Two units' reports on one head: two check runs of two names, so that neither hides the other (GitHub shows
        the newest check run of each name)."""
        names = [check_run.payload(report("needs work", unit=u), SHA)["name"]
                 for u in ("libreac/fuzz_pcap", "libreac/fuzz_records")]
        self.assertEqual(names, ["theorem/prove: libreac/fuzz_pcap", "theorem/prove: libreac/fuzz_records"])

    def test_work_is_action_required(self):
        """A contract that needs work, whose own file changed, that is gone, or whose prediction cannot be made, beside
        an unchanged one and a data changed one."""
        for state in ("needs work", "changed contract", "removed", "unknown"):
            with self.subTest(state=state):
                r = report("unchanged", "data changed", state)
                got = check_run.payload(r, SHA)
                self.assertEqual((got["conclusion"], got["output"]["summary"]), ("action_required", prove.markdown(r)))

    def test_data_changed_alone_is_neutral(self):
        """Every contract that is not unchanged is data changed (Ruling 22): Rocq decides, and the summary says so
        above the report."""
        r = report("unchanged", "data changed", "data changed", functions=("moved",))
        got = check_run.payload(r, SHA)
        self.assertEqual((got["conclusion"], got["output"]),
                         ("neutral", {"title": "0 contracts need work, 0 functions changed, 2 data changed",
                                      "summary": NEUTRAL + prove.markdown(r)}))

    def test_the_title_counts(self):
        """Contracts that need work are those that need work, changed contracts and removed ones; functions changed
        are those whose instructions changed, were added or were removed, in every build; data changed and unknown
        contracts are counted when there are any."""
        for r, title in (
                (report("needs work", "changed contract", "removed", "unchanged",
                        functions=("changed", "added", "removed", "moved", "identical", "changed")),
                 "3 contracts need work, 4 functions changed"),
                (report("needs work", "data changed", "data changed", "unknown", "unchanged"),
                 "1 contracts need work, 0 functions changed, 2 data changed, 1 unknown"),
                (report("unknown", "unknown", functions=("added",)),
                 "0 contracts need work, 1 functions changed, 2 unknown"),
                (report(functions=("changed",)), "0 contracts need work, 1 functions changed")):
            with self.subTest(title=title):
                self.assertEqual(check_run.payload(r, SHA)["output"]["title"], title)

    def test_a_pull_request_s_check_names_it_first_as_unmerged(self):
        """On the code repository's commit, the check says whose change it is: the head of an unmerged pull request."""
        url = "https://github.com/acme/proofs/pull/7"
        for r, prefix in ((report("needs work"), ""), (report("data changed"), NEUTRAL)):
            with self.subTest(prefix=prefix):
                got = check_run.payload(r, SHA, url)["output"]["summary"]
                self.assertEqual(got, "This report is of the head of an unmerged pull request, %s: a prediction for a "
                                      "proposed change that no one has merged, not a result of the repository's main "
                                      "branch.\n\n%s%s" % (url, prefix, prove.markdown(r)))

    def test_oft_prove_takes_only_a_pull_request_s_url(self):
        for url in ("https://github.com/acme/proofs/issues/7", "https://github.com/acme/proofs/pull/7\n",
                    "http://github.com/acme/proofs/pull/7", "https://github.com/acme/proofs/pull/0",
                    "https://example.com/acme/proofs/pull/7"):
            with self.subTest(url=url), contextlib.redirect_stderr(io.StringIO()), self.assertRaises(SystemExit):
                cli.main(["prove", "--base", BASE, "--pull-request", url, UNIT])

    def test_a_name_of_the_head_s_facts_stays_text(self):
        """A backtick in a name would close its code and let the rest be a link, an image or HTML in the check: each
        name is code whose fence is longer than any backtick run in it, and the why column escapes Markdown."""
        r = report("needs work", functions=("changed",))
        evil = "f`[x](https://evil.example)`|<img src=x>"
        r = r._replace(rows=[("plain", r.rows[0][1]._replace(names=(evil, "``g")))],
                       contracts=[dict(r.contracts[0], why="plain:%s changed" % evil)])
        md = prove.markdown(r)
        self.assertIn("| plain | changed | ``f`[x](https://evil.example)`\\|<img src=x>``, ``` ``g ``` |", md)
        self.assertIn("| plain:f\\`\\[x\\](https://evil.example)\\`\\|\\<img src=x\\> changed |", md)

    def test_a_control_character_of_the_head_s_facts_ends_no_row(self):
        """A contract path with a newline and a Markdown image after it: one row, the image as code, the newline and
        any other control character as U+FFFD."""
        r = report("needs work")
        c = r.contracts[0]
        path = c["file"].replace("c0_c.v", "c0\n![x](https://evil.example/x.png)\x1b[31m.v")
        r = r._replace(contracts=[dict(c, file=path, why="a\rb\x7fc")])
        md = prove.markdown(r)
        row = "| `Prog/c0\ufffd![x](https://evil.example/x.png)\ufffd[31m.v` | needs work | a\ufffdb\ufffdc |"
        self.assertIn("\n" + row + "\n", md)
        self.assertIsNone(re.search(r"[\x00-\x09\x0b-\x1f\x7f]", md))


def sized(r, prefix, length):
    """r with its last contract's why grown so that prefix and prove.markdown(r) together are length characters."""
    grow = length - len(prefix) - len(prove.markdown(r))
    assert grow >= 0, grow
    c = r.contracts[-1]
    return r._replace(contracts=r.contracts[:-1] + [dict(c, why=c["why"] + "x" * grow)])


def lists(md):
    """(the function rows, the contract rows) of a report's Markdown: the table rows under its two ### headings."""
    _, functions, contracts = re.split(r"^### .*$", md, flags=re.M)

    def rows(part):
        return [l for l in part.splitlines() if l.startswith("| ") and not l.startswith(("| build |", "| contract |"))]
    return rows(functions), rows(contracts)


def left_out(n, total):
    return ("\n\n_%d of the report's %d rows are left out to keep this summary within GitHub's 65,535 characters: the "
            "full report is the output of `oft prove`, and every row is in `oft prove --json`._\n" % (n, total))


class Summary(unittest.TestCase):
    """A check run's summary holds at most 65,535 characters (GitHub's limit).  A longer report keeps its counts, then
    the rows of the contracts that need work, are changed contracts, are removed or are unknown, then the functions
    whose instructions changed, then the other contracts, and ends with a line that says how many rows it left out."""

    # a report whose rows need work, and a neutral one, whose summary starts with a sentence
    CASES = ((("needs work",) + ("unchanged",) * 1400, ""), (("data changed",) * 1400, NEUTRAL))

    def test_a_summary_of_the_limit_is_the_whole_report(self):
        for states, prefix in self.CASES:
            with self.subTest(prefix=prefix):
                r = sized(report(*states), prefix, 65535)
                got = check_run.payload(r, SHA)["output"]["summary"]
                self.assertEqual((len(got), got), (65535, prefix + prove.markdown(r)))

    def test_a_summary_one_over_the_limit_is_cut(self):
        for (states, prefix), title in zip(self.CASES, ("1 contracts need work, 0 functions changed",
                                                        "0 contracts need work, 0 functions changed, 1400 data "
                                                        "changed")):
            with self.subTest(prefix=prefix):
                r = sized(report(*states), prefix, 65536)
                md = prove.markdown(r)
                got = check_run.payload(r, SHA)
                summary = got["output"]["summary"]
                functions, contracts = lists(md)
                kept_functions, kept = lists(summary)
                n = len(functions) + len(contracts) - len(kept_functions) - len(kept)
                self.assertLessEqual(len(summary), 65535)
                self.assertGreater(n, 0)
                self.assertEqual((got["conclusion"], got["output"]["title"]),
                                 ("action_required" if not prefix else "neutral", title))
                # the sentence, the heading, the counts and the empty list of functions, whole
                self.assertTrue(summary.startswith(prefix + md[:md.index("### Contracts")]))
                self.assertEqual(kept, contracts[:len(kept)])
                self.assertTrue(summary.endswith(left_out(n, len(functions) + len(contracts))), summary[-300:])

    def test_rows_that_need_work_come_first_then_functions(self):
        """Every contract that predicts work or cannot be predicted and every function whose instructions changed is
        kept before any data changed contract; the unchanged ones go first."""
        r = report("needs work", "changed contract", "removed", "unknown", *(("data changed",) * 900 +
                                                                            ("unchanged",) * 300),
                   functions=("changed",) * 600)
        md = prove.markdown(r)
        functions, contracts = lists(md)
        summary = check_run.payload(r, SHA)["output"]["summary"]
        kept_functions, kept = lists(summary)
        self.assertGreater(len(md), 65535)
        self.assertLessEqual(len(summary), 65535)
        self.assertEqual(kept_functions, functions)
        self.assertEqual([l.split(" | ")[1] for l in kept[:4]],
                         ["changed contract", "removed", "needs work", "unknown"])
        self.assertEqual({l.split(" | ")[1] for l in kept[4:]}, {"data changed"})
        self.assertLess(len(kept), 4 + 900)
        self.assertTrue(summary.endswith(left_out(len(contracts) - len(kept), len(functions) + len(contracts))))

    def test_contracts_that_need_work_come_before_functions(self):
        """More functions changed than fit: the contracts that predict work or cannot be predicted are kept whole, then
        as many functions as fit, in their order, and no other contract."""
        r = report("needs work", "changed contract", "removed", "unknown", "data changed", "unchanged",
                   functions=("changed",) * 2000)
        md = prove.markdown(r)
        functions, contracts = lists(md)
        summary = check_run.payload(r, SHA)["output"]["summary"]
        kept_functions, kept = lists(summary)
        self.assertLessEqual(len(summary), 65535)
        self.assertEqual(kept, contracts[:4])
        self.assertEqual(kept_functions, functions[:len(kept_functions)])
        self.assertLess(len(kept_functions), 2000)
        self.assertTrue(summary.endswith(left_out(2002 - len(kept_functions), 2006)))

    def test_a_row_too_long_to_fit_hides_no_other_row(self):
        """A contract whose why alone is over the limit is left out, and every row after it that fits is kept."""
        r = report("needs work", "needs work", "unchanged", functions=("changed",))
        r = r._replace(contracts=[dict(r.contracts[0], why="x" * 70000)] + r.contracts[1:])
        functions, contracts = lists(prove.markdown(r))
        summary = check_run.payload(r, SHA)["output"]["summary"]
        self.assertLessEqual(len(summary), 65535)
        self.assertEqual(lists(summary), (functions, contracts[1:]))
        self.assertTrue(summary.endswith(left_out(1, 4)))


class Post(unittest.TestCase):
    """check_run.post: POST /repos/{repo}/check-runs with the token; the id of the check run GitHub made, and its page.
    A PostError holds the HTTP status of GitHub's refusal, or None when there was no answer."""

    def test_post_sends_the_payload(self):
        """Called with keywords, as the interface names them; also with an API base URL that ends in a slash."""
        payload = check_run.payload(report("needs work", functions=("changed",)), SHA)
        for slash in ("", "/"):
            with self.subTest(slash=slash), github() as (server, api):
                self.assertEqual(check_run.post(repo="example/libreac", payload=payload,
                                                token=check_run.Token("ghs_stand-in"), api=api + slash),
                                 (4242, "https://github.com/example/libreac/runs/4242"))
                self.assertEqual(len(server.requests), 1)
                method, path, headers, body = server.requests[0]
                self.assertEqual((method, path, body), ("POST", "/repos/example/libreac/check-runs", payload))
                self.assertEqual({k: headers.get(k) for k in ("authorization", "accept", "x-github-api-version",
                                                              "content-type")},
                                 {"authorization": "Bearer ghs_stand-in", "accept": "application/vnd.github+json",
                                  "x-github-api-version": "2022-11-28", "content-type": "application/json"})

    def test_an_answer_with_no_page_gives_none_for_it(self):
        with github(201, {"id": 4242}) as (_server, api):
            self.assertEqual(check_run.post("example/libreac", check_run.payload(report(), SHA),
                                            check_run.Token("ghs_stand-in"), api=api), (4242, None))

    def test_a_refusal_names_github_s_message_and_the_permission_it_asks_for(self):
        """The agent App's token on example/libreac gets this answer (checks: read)."""
        payload = check_run.payload(report(), SHA)
        with github(403, {"message": "Resource not accessible by integration",
                          "documentation_url": "https://docs.github.com/rest/checks/runs#create-a-check-run",
                          "status": "403"}, {"X-Accepted-GitHub-Permissions": "checks=write"}) as (_server, api):
            with self.assertRaises(check_run.PostError) as e:
                check_run.post("example/libreac", payload, check_run.Token("ghs_stand-in"), api=api)
        self.assertEqual(str(e.exception), "POST /repos/example/libreac/check-runs: HTTP 403: Resource not accessible "
                                           "by integration (the token needs checks=write)")
        self.assertEqual(e.exception.status, 403)

    def test_an_unreachable_api_is_a_post_error(self):
        with github() as (_server, api):
            pass
        with self.assertRaises(check_run.PostError) as e:
            check_run.post("example/libreac", check_run.payload(report(), SHA), check_run.Token("ghs_stand-in"),
                           api=api)
        self.assertTrue(str(e.exception).startswith("POST /repos/example/libreac/check-runs: "), str(e.exception))
        self.assertIsNone(e.exception.status)

    def test_a_malformed_token_is_refused_once_and_not_shown(self):
        """A token with a newline once made http.client raise ValueError with the whole Authorization value.  The one
        check is check_run.Token's, which the command makes before the report; post sends nothing but a Token."""
        for token in MALFORMED:
            with self.subTest(token=token):
                with self.assertRaises(ValueError) as e:
                    check_run.Token(token)
                self.assertEqual(str(e.exception), "the token is empty or holds whitespace, a control character or a "
                                                   "non-ASCII character; it is not shown")
        with github() as (server, api):
            with self.assertRaises(TypeError) as e:
                check_run.post("example/libreac", check_run.payload(report(), SHA), "ghs\nstand-in", api=api)
            self.assertNotIn("stand-in", str(e.exception))
            self.assertEqual(server.requests, [])

    def test_github_s_answer_never_shows_the_token(self):
        """A refusal whose message, body or header quotes the token shows [token] in its place."""
        for status, reply, headers, says in (
                (403, {"message": "Bad credentials: " + SECRET}, {"X-Accepted-GitHub-Permissions": "checks=" + SECRET},
                 "HTTP 403: Bad credentials: [token] (the token needs checks=[token])"),
                (401, "Bearer %s is no token" % SECRET, {}, 'HTTP 401: "Bearer [token] is no token"'),
                (201, {"echo": SECRET}, {}, "HTTP 201 with no check run id")):
            with self.subTest(status=status), github(status, reply, headers) as (_server, api):
                with self.assertRaises(check_run.PostError) as e:
                    check_run.post("example/libreac", check_run.payload(report(), SHA), check_run.Token(SECRET),
                                   api=api)
                self.assertEqual(str(e.exception), "POST /repos/example/libreac/check-runs: " + says)

    def test_a_body_cut_to_200_characters_shows_no_part_of_the_token(self):
        """A refusal whose body has no message is shown cut to its first 200 characters.  The token is replaced before
        the cut, so a token that the cut splits leaves none of its characters."""
        for kept in range(1, len(SECRET)):
            # the stand-in sends the JSON string '"..."': the token starts at character 200 - kept of the body
            reply = "." * (199 - kept) + SECRET + "-" * 30
            with self.subTest(kept=kept), github(403, reply) as (_server, api):
                with self.assertRaises(check_run.PostError) as e:
                    check_run.post("example/libreac", check_run.payload(report(), SHA), check_run.Token(SECRET),
                                   api=api)
                self.assertEqual(str(e.exception), "POST /repos/example/libreac/check-runs: HTTP 403: "
                                 + ('"%s[token]%s"' % ("." * (199 - kept), "-" * 30))[:200])
                self.assertNotIn(SECRET[:kept], str(e.exception))

    def test_an_interrupted_answer_is_a_post_error(self):
        """A success or a refusal whose body ends short, and an answer that is no HTTP: a PostError (never an
        http.client error), which never shows the token."""
        for status, mode, says in ((201, "cut", "no complete answer: IncompleteRead("),
                                   (403, "cut", "HTTP 403, whose body could not be read: IncompleteRead("),
                                   (201, "garbage", "no complete answer: BadStatusLine: garbage [token]")):
            with self.subTest(status=status, mode=mode), github(status, {"message": "Bad credentials"},
                                                               mode=mode) as (_server, api):
                with self.assertRaises(check_run.PostError) as e:
                    check_run.post("example/libreac", check_run.payload(report(), SHA), check_run.Token(SECRET),
                                   api=api)
                self.assertTrue(str(e.exception).startswith("POST /repos/example/libreac/check-runs: " + says),
                                str(e.exception))
                self.assertNotIn(SECRET, str(e.exception))


def posted(check_id, repo, sha, conclusion="success", title="0 contracts need work, 0 functions changed"):
    """The line `oft prove` writes for a check run GitHub made, as the stand-in answers."""
    return ('oft prove: posted check run %d "theorem/prove: zlib/checksum_fuzzer" on %s@%s: %s, %s: '
            "https://github.com/%s/runs/%d\n" % (check_id, repo, sha, conclusion, title, repo, check_id))


class PostCheck(unittest.TestCase):
    """`oft prove --post-check OWNER/REPO@SHA`: the report to stdout, and the check run on that commit, with the token
    in GH_TOKEN, at GITHUB_API_URL (GitHub's own variable for its API; https://api.github.com when unset).  Each
    --post-check and --post-check-optional is posted, the --post-check ones first, each in the order given; a refusal
    stops no other post.  The exit status is 1 when a post failed, except a --post-check-optional one that GitHub
    refused with 403 or 404 (the App is not installed there, or may not write checks): that is a warning."""

    def prove(self, t, *args, **env):
        return subprocess.run([sys.executable, "-B", "-m", "oft", "--root", t.root, "prove", UNIT, *args],
                              capture_output=True, text=True,
                              env=dict({k: v for k, v in os.environ.items() if k not in ("GH_TOKEN", "GITHUB_API_URL")},
                                       PYTHONPATH=TOOLS, **env))

    def test_oft_prove_post_check_posts_the_report(self):
        with tree() as t:
            base = contract_repo(t)
            put_row(t, "LLVMFuzzerTestOneInput", exact="1e" * 32, masked="2d" * 32, lines="fuzz/checksum.c:3-9")
            head = commit(t)
            with github() as (server, api):
                done = self.prove(t, "--base", base, "--head", head, "--post-check", "example/libreac@" + SHA,
                                  GH_TOKEN="ghs_stand-in", GITHUB_API_URL=api)
            r = prove.report(t.root, UNIT, base, head)
            self.assertEqual((done.returncode, done.stdout), (0, prove.markdown(r)), done.stderr)
            self.assertEqual(done.stderr, posted(4242, "example/libreac", SHA, "action_required",
                                                 "1 contracts need work, 1 functions changed"))
            self.assertEqual([(m, p, h["authorization"], b) for m, p, h, b in server.requests],
                             [("POST", "/repos/example/libreac/check-runs", "Bearer ghs_stand-in",
                               check_run.payload(r, SHA))])

    def test_a_refused_post_fails_after_the_report(self):
        with tree() as t:
            head = contract_repo(t)
            with github(403, {"message": "Resource not accessible by integration"},
                        {"X-Accepted-GitHub-Permissions": "checks=write"}) as (_server, api):
                done = self.prove(t, "--base", head, "--head", head, "--post-check", "example/libreac@" + SHA,
                                  GH_TOKEN="ghs_stand-in", GITHUB_API_URL=api)
            self.assertEqual((done.returncode, done.stdout),
                             (1, prove.markdown(prove.report(t.root, UNIT, head, head))))
            self.assertEqual(done.stderr, "FAIL oft prove --post-check: POST /repos/example/libreac/check-runs: HTTP "
                                          "403: Resource not accessible by integration (the token needs "
                                          "checks=write)\n")

    def test_each_post_check_is_posted(self):
        with tree() as t:
            head = contract_repo(t)
            with github(replies={"acme/proofs": (201, None), "example/libreac": (201, None)}) as (server, api):
                done = self.prove(t, "--base", head, "--head", head, "--post-check", "acme/proofs@" + HEAD,
                                  "--post-check", "example/libreac@" + SHA, GH_TOKEN="ghs_stand-in", GITHUB_API_URL=api)
            r = prove.report(t.root, UNIT, head, head)
            self.assertEqual((done.returncode, done.stdout), (0, prove.markdown(r)), done.stderr)
            self.assertEqual(done.stderr, posted(4242, "acme/proofs", HEAD) + posted(4243, "example/libreac", SHA))
            self.assertEqual([(p, b) for _m, p, _h, b in server.requests],
                             [("/repos/acme/proofs/check-runs", check_run.payload(r, HEAD)),
                              ("/repos/example/libreac/check-runs", check_run.payload(r, SHA))])

    def test_a_refused_post_stops_no_other_and_fails_the_run(self):
        """Refused with 403 or 404 without --post-check-optional: a failure."""
        for status, message in ((403, "Resource not accessible by integration"), (404, "Not Found")):
            with self.subTest(status=status), tree() as t:
                head = contract_repo(t)
                with github(replies={"acme/proofs": (status, {"message": message}),
                                     "example/libreac": (201, None)}) as (server, api):
                    done = self.prove(t, "--base", head, "--head", head, "--post-check", "acme/proofs@" + HEAD,
                                      "--post-check", "example/libreac@" + SHA, GH_TOKEN="ghs_stand-in",
                                      GITHUB_API_URL=api)
                self.assertEqual(done.returncode, 1)
                self.assertEqual(done.stderr, "FAIL oft prove --post-check: POST /repos/acme/proofs/check-runs: HTTP "
                                              "%d: %s\n" % (status, message) + posted(4243, "example/libreac", SHA))
                self.assertEqual(len(server.requests), 2)

    def test_an_optional_post_refused_with_403_or_404_is_a_warning(self):
        """The App not installed on the code repository (404), or not allowed to write its checks (403)."""
        for status, message in ((404, "Not Found"), (403, "Resource not accessible by integration")):
            with self.subTest(status=status), tree() as t:
                head = contract_repo(t)
                with github(replies={"acme/proofs": (201, None),
                                     "example/libreac": (status, {"message": message})}) as (server, api):
                    done = self.prove(t, "--base", head, "--head", head, "--post-check-optional",
                                      "example/libreac@" + SHA, "--post-check", "acme/proofs@" + HEAD,
                                      GH_TOKEN="ghs_stand-in", GITHUB_API_URL=api)
                self.assertEqual((done.returncode, done.stdout),
                                 (0, prove.markdown(prove.report(t.root, UNIT, head, head))), done.stderr)
                self.assertEqual(done.stderr, posted(4242, "acme/proofs", HEAD)
                                 + "WARN oft prove --post-check-optional: POST /repos/example/libreac/check-runs: HTTP "
                                   "%d: %s; no check run there\n" % (status, message))

    def test_an_optional_post_that_fails_otherwise_fails_the_run(self):
        for status, message in ((401, "Bad credentials"), (422, "Validation Failed"), (500, "Server Error")):
            with self.subTest(status=status), tree() as t:
                head = contract_repo(t)
                with github(replies={"example/libreac": (status, {"message": message})}) as (_server, api):
                    done = self.prove(t, "--base", head, "--head", head, "--post-check-optional",
                                      "example/libreac@" + SHA, GH_TOKEN="ghs_stand-in", GITHUB_API_URL=api)
                self.assertEqual((done.returncode, done.stderr),
                                 (1, "FAIL oft prove --post-check-optional: POST /repos/example/libreac/check-runs: "
                                     "HTTP %d: %s\n" % (status, message)))

    def test_post_check_without_a_token_fails_before_the_report(self):
        with tree() as t:
            head = contract_repo(t)
            for flag in ("--post-check", "--post-check-optional"):
                with self.subTest(flag=flag), github() as (server, api):
                    done = self.prove(t, "--base", head, "--head", head, flag, "example/libreac@" + SHA,
                                      GITHUB_API_URL=api)
                self.assertEqual((done.returncode, done.stdout, done.stderr, server.requests),
                                 (1, "FAIL oft prove: %s needs a token in GH_TOKEN\n" % flag, "", []))

    def test_a_malformed_gh_token_fails_before_the_report_and_is_not_shown(self):
        """Each malformed token an environment can hold (not an empty one, which is none, nor one with a NUL)."""
        with tree() as t:
            head = contract_repo(t)
            for token in (k for k in MALFORMED if k and "\x00" not in k):
                with self.subTest(token=token), github() as (server, api):
                    done = self.prove(t, "--base", head, "--head", head, "--post-check", "example/libreac@" + SHA,
                                      GH_TOKEN=token, GITHUB_API_URL=api)
                    self.assertEqual((done.returncode, done.stdout, done.stderr, server.requests),
                                     (1, "FAIL oft prove: GH_TOKEN holds whitespace, a control character or a "
                                         "non-ASCII character; it is not shown\n", "", []))

    def test_a_refusal_that_quotes_the_token_does_not_show_it(self):
        with tree() as t:
            head = contract_repo(t)
            with github(401, {"message": "Bad credentials for " + SECRET}) as (_server, api):
                done = self.prove(t, "--base", head, "--head", head, "--post-check", "example/libreac@" + SHA,
                                  GH_TOKEN=SECRET, GITHUB_API_URL=api)
            self.assertEqual((done.returncode, done.stderr),
                             (1, "FAIL oft prove --post-check: POST /repos/example/libreac/check-runs: HTTP 401: Bad "
                                 "credentials for [token]\n"))
            self.assertNotIn(SECRET, done.stdout + done.stderr)

    def test_with_no_github_api_url_the_check_goes_to_api_github_com(self):
        """GITHUB_API_URL unset or empty.  check_run.post is replaced, at the edge of the network, by a recorder that
        answers as GitHub does."""
        with tree() as t:
            head = contract_repo(t)
            for env in ({}, {"GITHUB_API_URL": ""}):
                with self.subTest(env=env):
                    calls = []

                    def record(repo, body, token, api):
                        calls.append((repo, token, api))
                        return check_run.Posted(4242, "https://github.com/example/libreac/runs/4242")
                    with mock.patch.dict(os.environ, dict(env, GH_TOKEN="ghs_stand-in")), \
                            mock.patch.object(check_run, "post", record), \
                            contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(io.StringIO()):
                        if not env:
                            os.environ.pop("GITHUB_API_URL", None)
                        rc = cli.main(["--root", t.root, "prove", UNIT, "--base", head, "--head", head,
                                       "--post-check", "example/libreac@" + SHA])
                    self.assertEqual((rc, calls), (0, [("example/libreac", "ghs_stand-in", "https://api.github.com")]))

    def test_post_check_is_owner_repo_at_a_full_commit_id(self):
        with tree() as t:
            head = contract_repo(t)
            for flag in ("--post-check", "--post-check-optional"):
                for bad in ("example/libreac", "example/libreac@" + SHA[:12], "example@" + SHA, "../libreac@" + SHA,
                            "example/..@" + SHA, "example/libreac/x@" + SHA, "example/libreac@" + SHA.upper()):
                    with self.subTest(flag=flag, bad=bad):
                        done = self.prove(t, "--base", head, "--head", head, flag, bad, GH_TOKEN="ghs_stand-in")
                        self.assertEqual((done.returncode, done.stdout), (2, ""))
                        self.assertIn("%s: not OWNER/REPO@SHA" % flag, done.stderr)

    def test_check_run_is_not_the_checker(self):
        """keys.NOT_THE_CHECKER names check_run.py, so a change to it re-checks no fuzz target; that holds only while
        a check opens it not, so oft.check, with oft.facts and oft.fetch, does not import it."""
        self.assertTrue(keys.not_the_checker("tools/oft/check_run.py"))
        done = subprocess.run([sys.executable, "-c", "import sys, oft.check, oft.facts, oft.fetch; "
                               "print('oft.check_run' in sys.modules)"],
                              capture_output=True, text=True, env=dict(os.environ, PYTHONPATH=TOOLS))
        self.assertEqual((done.returncode, done.stdout, done.stderr), (0, "False\n", ""))

    def test_the_report_does_not_import_the_poster(self):
        """prove.py makes the report; the command posts it with check_run.run: no import cycle between them."""
        done = subprocess.run([sys.executable, "-c", "import sys, oft.prove; print('oft.check_run' in sys.modules)"],
                              capture_output=True, text=True, env=dict(os.environ, PYTHONPATH=TOOLS))
        self.assertEqual((done.returncode, done.stdout, done.stderr), (0, "False\n", ""))


class CodeLine(unittest.TestCase):
    """check_run.code_target: the commit of the code repository a pull request's body names on a line of its own,
    `Code: OWNER/REPO@SHA`, where the prove workflow also posts the check; and what is wrong with its Code: lines."""

    def test_a_valid_line(self):
        for body in ("Code: example/libreac@%s" % SHA,
                     "The symbol facts of v1.9.0.\r\n\r\n  Code: example/libreac@%s  \r\nMore text.\r\n" % SHA,
                     "First line\nCode: example/libreac@%s\n" % SHA):
            with self.subTest(body=body):
                self.assertEqual(check_run.code_target(body), (("example/libreac", SHA), []))

    def test_no_line(self):
        for body in (None, "", "No code repository.", "Codes: example/libreac@%s" % SHA,
                     "The Code: example/libreac@%s line" % SHA, "code: example/libreac@%s" % SHA):
            with self.subTest(body=body):
                self.assertEqual(check_run.code_target(body), (None, []))

    def test_a_malformed_line_is_named_by_its_number_and_not_shown(self):
        """Its text is the pull request author's: the problem names the line, never quotes it."""
        for value in ("example/libreac@" + SHA[:12], "example/libreac@" + SHA.upper(), "example/libreac " + SHA,
                      "example/libreac@%s and more" % SHA, "", "example/..@" + SHA, "::warning::x@" + SHA):
            with self.subTest(value=value):
                self.assertEqual(check_run.code_target("Title\n\nCode: " + value),
                                 (None, ["line 3 of the pull request's body starts with `Code:` but is not "
                                         "`Code: OWNER/REPO@SHA` with the full 40-hex commit id"]))

    def test_several_lines(self):
        other = "f" * 40
        line = "Code: example/libreac@%s\n" % SHA
        self.assertEqual(check_run.code_target(line + "text\n" + line), (("example/libreac", SHA), []))
        self.assertEqual(check_run.code_target(line + "Code: example/libreac@%s\n" % other),
                         (None, ["the pull request's body names 2 code commits on `Code:` lines (example/libreac@%s, "
                                 "example/libreac@%s): none is posted" % (SHA, other)]))
        self.assertEqual(check_run.code_target(line + "Code: example/libreac\n"),
                         (("example/libreac", SHA),
                          ["line 2 of the pull request's body starts with `Code:` but is not `Code: OWNER/REPO@SHA` "
                           "with the full 40-hex commit id"]))


if __name__ == "__main__":
    unittest.main()
