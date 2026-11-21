"""The held-content check: .github/workflows/held-content.yml, which scans a pull request with the patterns of
detectors.tsv, .github/workflows/held-content-private.yml, which scans it from main with the patterns of the secret
too and posts a status, the scanner they run (.github/held/held_content_scan.py), and the self-tests of the scripts
of the three public checks.

A job runs as GitHub runs it: its `if:`, then each step's own `run:` text, read with yamlio, under
`bash --noprofile --norc -eo pipefail` (what `shell: bash` runs), with its `env` computed from the workflow's own
${{ }} expressions by helpers.gh_value, in a checkout of a scratch origin that holds main and refs/pull/<n>/head.
FAKE_GH, the stand-in gh that those steps call, and the pieces that run a job are here for test_public_guards too.
A step finds the stand-in GitHub API (StandInApi, which answers each request by HTTP with FAKE_GH) at GITHUB_API_URL,
as a step on GitHub's runner finds the GitHub API.  The scan step of the private workflow reads a pull request from
that API by HTTP, and the other steps call the stand-in gh.  So the tests of the private workflow tell the stand-in
which pull requests are open, and hold every number the scan prints to `git log --reverse` and `git diff --raw
--no-renames`, run on the scratch repository.
Each class skips, with a reason, when a file of .github/ that it reads is absent: tools/oft alone, as the runner image
carries it, has no .github."""
import contextlib
import hashlib
import importlib.util
import http.server
import io
import json
import os
import random
import re
import shlex
import shutil
import subprocess
import sys
import tempfile
import threading
import time
import unittest
from unittest import mock

from oft import yamlio
from oft.tests.helpers import (NO_HOME, REPO, Concurrency, child_environment, gh_text, gh_truthy, gh_value, git,
                               git_repo, inline_scripts)

PUBLIC = "theorem-labs/oss-verify-proofs"   # the one repository whose jobs run
TOKEN = "stand-in-token"    # the github.token of a run, made up
HELD = os.path.join(REPO, ".github", "held")
SCANNER = os.path.join(HELD, "held_content_scan.py")
DETECTORS = os.path.join(HELD, "detectors.tsv")
HELD_FILES = tuple(os.path.join(HELD, name) for name in
                   ("held_content_scan.py", "detectors.tsv", "must-pass-lines.txt", "private-detectors.sha256"))
WORKFLOWS = os.path.join(REPO, ".github", "workflows")
HELD_CONTENT = os.path.join(WORKFLOWS, "held-content.yml")
PRIVATE = os.path.join(WORKFLOWS, "held-content-private.yml")
FREEZE_WORKFLOW = os.path.join(WORKFLOWS, "statement-freeze.yml")
PINS_WORKFLOW = os.path.join(WORKFLOWS, "pin-coherence.yml")
STATEMENT_FREEZE = os.path.join(REPO, ".github", "guards", "statement_freeze.py")
PIN_COHERENCE = os.path.join(REPO, ".github", "guards", "pin_coherence.py")
# the steps of held-content.yml, by name
PLANT = "plant one fresh canary per detector, and require a refusal"
SCAN = "nothing this change adds is held content"
# the steps of held-content-private.yml, by name
HEADS = "the heads to scan, each with its pull requests"
API_SCAN = "nothing these pull requests add is held content"
POST = "one status on the head, when it is still the head"
PLANT_ALL = "plant one fresh sample per pattern, and require a refusal"
CONTEXT = "held-content-private"    # the name of the status that the private workflow posts
ACTIONS = "github-actions[bot]"     # the account that GitHub posts it as


def absent(*paths):
    """A skip reason that names each of paths that is not there, or "" when every one is there."""
    gone = [os.path.relpath(p, REPO) for p in paths if not os.path.exists(p)]
    return "no %s beside tools/oft" % ", ".join(gone) if gone else ""


HELD_ABSENT = absent(*HELD_FILES)
HELD_CONTENT_ABSENT = absent(HELD_CONTENT, *HELD_FILES)
PRIVATE_ABSENT = absent(PRIVATE, *HELD_FILES)
WORKFLOWS_ABSENT = absent(HELD_CONTENT, PRIVATE, FREEZE_WORKFLOW, PINS_WORKFLOW)
GUARDS_ABSENT = absent(STATEMENT_FREEZE, PIN_COHERENCE)

# A stand-in for `gh api`: <dir>/gh runs <dir>/gh.py, which answers from <dir>/state.json and from the scratch git
# repository that state["git"] names, read with git plumbing only (rev-parse, rev-list, merge-base, ls-tree,
# cat-file), and adds each call to <dir>/calls.jsonl as one JSON object: its arguments, its method, its endpoint,
# every field it posts (-f, -F, --field, --raw-field) with its value, its headers, the number of pages it served, the
# HTTP status it answered, and `http`: None for a call of gh, and {"bearer": whether the Authorization header was
# Bearer and the token of the run} for a request that came by HTTP (StandInApi).  Endpoints:
#   repos/<owner>/<repo>/pulls/<n>/reviews: state["reviews"][<n>], each {"login", "state", "at"}, where `at` is a
#       revision of the repository that `git rev-parse` turns into the review's commit_id.
#   repos/<owner>/<repo>/pulls and .../pulls/<n>: the open pull requests, state["pulls"], each {"number", "head"}
#       with "base" (a branch, main when absent) and "labels".  state["moved"][<n>] = {"after": k, "head": id} gives
#       pull request n that other head from its read number k + 1 on: a head that moved during a run.
#   repos/<owner>/<repo>/commits/<id>/statuses: the statuses posted through this stand-in, newest first, then
#       state["statuses"][<id>] in its order, each {"state", "description", "context", "created_at"} with "login"
#       (ACTIONS when absent) and "id".  A status given with no "id" gets the count of the given statuses from it to
#       the last, so a list that is newest first and has no ids is newest first by id too.
#   POST repos/<owner>/<repo>/statuses/<id>: keeps the fields in <dir>/posted.json, as a status of state["actor"]
#       (ACTIONS when absent).
#   repos/<owner>/<repo>/compare/<base>...<head>: the merge base, the count of the commits of base..head (plus
#       state["miscount"]) and one page of them, with message, parents, committer date and tree.  The commits are in
#       an order that is not git's: by committer date, then by id.
#   repos/<owner>/<repo>/git/trees/<id>: one folder.  With state["cut_listings"] it lacks its last entry and says
#       `truncated: true`.  A recursive read always does, as GitHub's does on a large tree.
#   repos/<owner>/<repo>/git/blobs/<id>: the bytes with the raw media type, else GitHub's JSON with base64.  The
#       size that a folder lists for a blob is state["sizes"][<id>] when that is given.
#   rate_limit: state["rate"], {"limit", "remaining"}, each 15000 when absent.
# state["refuse"], each {"endpoint": a regular expression, "status", "message"}, makes the stand-in refuse a request
# as gh shows a refusal of GitHub: the body on stdout, `gh: <message> (HTTP <status>)` on stderr, exit 1.
# state["hang"], each {"endpoint": a regular expression, "seconds"}, makes the stand-in hang on a request, as a read
# that GitHub never answers: it records the call with "hung": seconds, waits that long, and exits 1 with no answer.
# A list is paged as GitHub pages it: per_page of the query (30 when it has none), and no more than
# state["page_size"] (100 when absent) on a page, so a test can serve two pages with two items.  As gh does: without
# --paginate one page is read (the query's `page`, 1 when it has none); with --paginate every page is read, and the
# pages of a list are printed as one list; with --paginate --slurp they are printed as one list of pages.  It refuses
# --slurp with --jq or --template, as gh 2.98.0 does, and it applies no --jq (the tests have no jq), so it refuses
# every --jq.  An endpoint it does not serve is GitHub's 404.
# The stand-in writes JSON as Python's json module does by default: backspace, tab, newline, form feed and carriage
# return as short escapes, and each other control character as a \u00XX escape, as GitHub's answers do.  Unlike gh
# 2.98.0, the stand-in called as gh changes no control character to its caret pair.  It gives a raw blob as its bytes.
FAKE_GH = r'''import base64, json, os, re, subprocess, sys, time, urllib.parse

HERE = os.path.dirname(os.path.abspath(__file__))
CALLS, POSTED = os.path.join(HERE, "calls.jsonl"), os.path.join(HERE, "posted.json")
with open(os.path.join(HERE, "state.json")) as f:
    state = json.load(f)
argv = sys.argv[1:]
# {"bearer": ...} for a request by HTTP, from StandInApi, and None for a call of gh
by_http = json.loads(os.environ["STAND_IN_HTTP"]) if "STAND_IN_HTTP" in os.environ else None
call = {"argv": argv, "method": None, "endpoint": None, "fields": {}, "headers": [], "pages": 0, "status": 200,
        "http": by_http}


def emit(answer):
    """Print answer as JSON, as GitHub writes it."""
    sys.stdout.buffer.write((json.dumps(answer) + "\n").encode())


def record():
    with open(CALLS, "a") as f:
        f.write(json.dumps(call) + "\n")


def fail(message, status=1):
    record()
    sys.stderr.write(message + "\n")
    sys.exit(status)


def refuse(status, message):
    call["status"] = status
    emit({"message": message, "status": str(status)})
    fail("gh: %s (HTTP %d)" % (message, status))


def earlier():
    if not os.path.exists(CALLS):
        return []
    with open(CALLS) as f:
        return [json.loads(line) for line in f if line.strip()]


def git(*args, text=True):
    done = subprocess.run(["git", "-C", state["git"]] + list(args), capture_output=True)
    if done.returncode:
        refuse(404, "Not Found")
    return done.stdout.decode().strip() if text else done.stdout


def reviews(number):
    return [{"id": n, "user": {"login": r["login"]}, "state": r["state"], "body": "",
             "commit_id": git("rev-parse", "--verify", r["at"] + "^{commit}")}
            for n, r in enumerate(state.get("reviews", {}).get(number, []), 1)]


def pull(p):
    return {"number": p["number"], "state": "open", "head": {"sha": p["head"], "ref": "a-branch"},
            "base": {"ref": p.get("base", "main")}, "labels": [{"name": name} for name in p.get("labels", [])]}


def pulls():
    return [pull(p) for p in state.get("pulls", [])]


def one_pull(number):
    found = [p for p in state.get("pulls", []) if str(p["number"]) == number]
    if not found:
        refuse(404, "Not Found")
    moved = state.get("moved", {}).get(number)
    asked = sum(c["method"] == "GET" and c["endpoint"] == call["endpoint"] for c in earlier())
    return pull(dict(found[0], head=moved["head"]) if moved and asked >= moved["after"] else found[0])


def posted():
    if not os.path.exists(POSTED):
        return []
    with open(POSTED) as f:
        return json.load(f)


def statuses(sha):
    given = state.get("statuses", {}).get(sha, [])
    given = [dict(s, id=s.get("id", len(given) - n), creator={"login": s.get("login", "github-actions[bot]")})
             for n, s in enumerate(given)]
    return [s for s in reversed(posted()) if s["sha"] == sha] + given


def post_status(sha):
    made = posted()
    made.append(dict(call["fields"], sha=sha, id=1000 + len(made),
                     created_at=time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
                     creator={"login": state.get("actor", "github-actions[bot]")}))
    with open(POSTED, "w") as f:
        json.dump(made, f)
    return made[-1]


def commit(sha):
    head, _, message = git("cat-file", "commit", sha, text=False).partition(b"\n\n")
    fields = [line.split(" ", 1) for line in head.decode().split("\n")]
    when = int(next(v for k, v in fields if k == "committer").rsplit(" ", 2)[1])
    return {"sha": sha, "parents": [{"sha": v} for k, v in fields if k == "parent"],
            "commit": {"message": message.decode().rstrip("\n"),
                       "tree": {"sha": next(v for k, v in fields if k == "tree")},
                       "committer": {"date": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime(when))}}}


def compare(base, head):
    base = git("rev-parse", "--verify", urllib.parse.unquote(base) + "^{commit}")
    commits = [commit(sha) for sha in git("rev-list", "%s..%s" % (base, head)).split()]
    commits.sort(key=lambda c: (c["commit"]["committer"]["date"], c["sha"]))
    size, page = int(query.get("per_page", 30)), int(query.get("page", 1))
    answer = {"merge_base_commit": commit(git("merge-base", base, head)),
              "total_commits": len(commits) + state.get("miscount", 0),
              "commits": commits[(page - 1) * size:page * size]}
    if page == 1:
        answer["files"] = []
    return answer


def tree(sha):
    recursive = "recursive" in query
    listed = git("ls-tree", "-z", "-l", *(["-r", "-t"] if recursive else []), sha, text=False)
    entries = []
    for item in listed.split(b"\0")[:-1]:
        meta, _, path = item.partition(b"\t")
        mode, kind, oid, size = meta.decode().split()
        entries.append({"path": path.decode(), "mode": mode, "type": kind, "sha": oid})
        if kind == "blob":
            entries[-1]["size"] = state.get("sizes", {}).get(oid, int(size))
    cut = recursive or state.get("cut_listings", False)
    return {"sha": sha, "tree": entries[:-1] if cut else entries, "truncated": bool(cut)}


def blob(sha):
    data = git("cat-file", "blob", sha, text=False)
    if any(h.replace(" ", "").lower() == "accept:application/vnd.github.raw" for h in call["headers"]):
        return data
    return {"sha": sha, "size": len(data), "encoding": "base64", "content": base64.encodebytes(data).decode()}


def rate_limit():
    core = dict({"limit": 15000, "remaining": 15000}, **state.get("rate", {}))
    return {"resources": {"core": core}, "rate": core}


REPOSITORY = r"repos/[^/]+/[^/]+/"
SERVED = (("GET", REPOSITORY + r"pulls/(\d+)/reviews", reviews),
          ("GET", REPOSITORY + r"pulls", pulls),
          ("GET", REPOSITORY + r"pulls/(\d+)", one_pull),
          ("GET", REPOSITORY + r"commits/([0-9a-f]+)/statuses", statuses),
          ("POST", REPOSITORY + r"statuses/([0-9a-f]+)", post_status),
          ("GET", REPOSITORY + r"compare/(.+)\.\.\.([0-9a-f]+)", compare),
          ("GET", REPOSITORY + r"git/trees/([0-9a-f]+)", tree),
          ("GET", REPOSITORY + r"git/blobs/([0-9a-f]+)", blob),
          ("GET", r"rate_limit", rate_limit))

if argv[:1] != ["api"]:
    fail("gh: this stand-in serves `gh api` alone", 9)
paginate = slurp = False
jq = None
words, at = argv[1:], 0
while at < len(words):
    word = words[at]
    if word == "--paginate":
        paginate = True
    elif word == "--slurp":
        slurp = True
    elif word in ("--jq", "-q", "--template", "-t"):
        jq, at = words[at + 1], at + 1
    elif word in ("--method", "-X"):
        call["method"], at = words[at + 1], at + 1
    elif word in ("-f", "-F", "--field", "--raw-field"):
        key, _, value = words[at + 1].partition("=")
        call["fields"][key], at = value, at + 1
    elif word in ("-H", "--header"):
        call["headers"].append(words[at + 1])
        at += 1
    elif word.startswith("-"):
        fail("gh: this stand-in does not know the option " + word, 9)
    else:
        call["endpoint"] = word
    at += 1
call["method"] = call["method"] or ("POST" if call["fields"] else "GET")
if slurp and jq is not None:
    fail("the `--slurp` option is not supported with `--jq` or `--template`")
if jq is not None:
    fail("gh: this stand-in applies no --jq", 9)
url = urllib.parse.urlsplit(call["endpoint"] or "")
query = dict(urllib.parse.parse_qsl(url.query))
for hang in state.get("hang", []):
    if re.search(hang["endpoint"], call["endpoint"] or ""):
        call["hung"] = hang["seconds"]
        record()
        time.sleep(hang["seconds"])
        sys.stderr.write("gh: no answer came in %d seconds\n" % hang["seconds"])
        sys.exit(1)
for refusal in state.get("refuse", []):
    if re.search(refusal["endpoint"], call["endpoint"] or ""):
        refuse(refusal["status"], refusal["message"])
for method, pattern, answer in SERVED:
    found = re.fullmatch(pattern, url.path.strip("/"))
    if found and call["method"] == method:
        body = answer(*found.groups())
        break
else:
    refuse(404, "Not Found")
if isinstance(body, bytes):
    call["pages"] = 1
    record()
    sys.stdout.buffer.write(body)
    sys.exit(0)
if isinstance(body, list):
    size = min(int(query.get("per_page", 30)), int(state.get("page_size", 100)))
    pages = [body[i:i + size] for i in range(0, len(body), size)] or [[]]
    if paginate:
        call["pages"], printed = len(pages), pages if slurp else [item for page in pages for item in page]
    else:
        page = int(query.get("page", 1))
        call["pages"], printed = 1, pages[page - 1] if page <= len(pages) else []
else:
    call["pages"], printed = 1, [body] if slurp else body
record()
emit(printed)
'''


def install_gh(directory, state):
    """FAKE_GH in directory, answering from state (`git`, the scratch repository it reads, and the answers of its
    endpoints); the directory, to put first on PATH."""
    os.makedirs(directory, exist_ok=True)
    with open(os.path.join(directory, "state.json"), "w") as f:
        json.dump(state, f)
    with open(os.path.join(directory, "gh.py"), "w") as f:
        f.write(FAKE_GH)
    with open(os.path.join(directory, "gh"), "w") as f:
        f.write('#!/bin/sh\nexec %s %s "$@"\n'
                % (shlex.quote(sys.executable), shlex.quote(os.path.join(directory, "gh.py"))))
    os.chmod(os.path.join(directory, "gh"), 0o755)
    return directory


def _recorded(directory, name, lines):
    path = os.path.join(directory, name)
    if not os.path.exists(path):
        return []
    with open(path) as f:
        return [json.loads(line) for line in f if line.strip()] if lines else json.load(f)


def gh_calls(directory):
    """Each call of the stand-in in directory, as gh or by HTTP, in order, as the dict it recorded."""
    return _recorded(directory, "calls.jsonl", True)


def posted_statuses(directory):
    """Each status posted through the stand-in gh in directory, in order: the fields of the call, and `sha`, the
    commit it is on."""
    return _recorded(directory, "posted.json", False)


class StandInApi(http.server.BaseHTTPRequestHandler):
    """The stand-in GitHub API of api_server().  Each GET runs FAKE_GH, the gh.py in the server's `directory`, with the
    arguments `api -H "Accept: <the Accept header>" <the path and the query, with no leading slash>` and with
    STAND_IN_HTTP set.  So FAKE_GH answers as GitHub does, and it records the call as one by HTTP, with whether its
    Authorization header was `Bearer <the server's token>`.  An exit 0 is a 200 answer with its stdout.  A refusal,
    `gh: <message> (HTTP <status>)` on stderr, is that status with the body on stdout.  Another exit is a 502 with no
    body.  A request that FAKE_GH hangs on waits as long.  state["redirect"], each {"endpoint": a regular expression,
    "location"}, makes the server answer each request whose endpoint matches with a 302 to that location, and run no
    FAKE_GH.  A call of the stand-in gh reads no redirect."""

    def do_GET(self):
        directory, endpoint = self.server.directory, self.path.lstrip("/")
        with open(os.path.join(directory, "state.json")) as f:
            state = json.load(f)
        for redirect in state.get("redirect", []):
            if re.search(redirect["endpoint"], endpoint):
                return self.answer(302, b"", {"Location": redirect["location"]})
        accept = self.headers.get("Accept", "")
        bearer = self.headers.get("Authorization") == "Bearer " + self.server.token
        process = subprocess.Popen([sys.executable, os.path.join(directory, "gh.py"), "api", "-H", "Accept: " + accept,
                                    endpoint], stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                   env=child_environment(NO_HOME, GIT_CONFIG_NOSYSTEM="1",
                                                         STAND_IN_HTTP=json.dumps({"bearer": bearer})))
        self.server.processes.append(process)
        stdout, stderr = process.communicate()
        refused = re.search(rb"\(HTTP (\d{3})\)", stderr)
        if process.returncode == 0:
            raw = accept.replace(" ", "").lower() == "application/vnd.github.raw"
            self.answer(200, stdout, {"Content-Type": "application/vnd.github.raw" if raw else "application/json"})
        elif refused:
            self.answer(int(refused.group(1)), stdout, {"Content-Type": "application/json"})
        else:
            self.answer(502, b"", {})

    def answer(self, status, body, headers):
        try:
            self.send_response(status)
            for name, text in headers.items():
                self.send_header(name, text)
            self.send_header("Content-Length", str(len(body)))
            self.end_headers()
            self.wfile.write(body)
        except OSError:
            pass        # the client stopped waiting, as the scan does when a read hangs

    def log_message(self, *args):
        pass            # a test reads the calls that FAKE_GH records, and no log of the server


class Recorder(http.server.BaseHTTPRequestHandler):
    """A server that adds each connection it gets to its list `got`, and answers each GET with 404."""

    def handle(self):
        self.server.got.append(self.client_address)
        super().handle()

    def do_GET(self):
        self.send_error(404)

    def log_message(self, *args):
        pass


class SlowAnswer(http.server.BaseHTTPRequestHandler):
    """A server that answers each GET with HTTP `status` and a Content-Length of 1 MiB.  It sends one byte at once,
    then one byte every 0.1 seconds for its `seconds` seconds, and then no byte more until the cleanup of http_server
    sets the event `release` of the server.  It waits for the event 30 seconds at most, and then it ends, so the client
    gets an answer shorter than its Content-Length."""

    status = 200

    def do_GET(self):
        try:
            self.send_response(self.status)
            self.send_header("Content-Length", str(1 << 20))
            self.end_headers()
            self.wfile.write(b"x")
            stop = time.monotonic() + self.server.seconds
            while time.monotonic() < stop:
                time.sleep(0.1)
                self.wfile.write(b"x")
            self.server.release.wait(30)
        except OSError:
            pass        # the client stopped waiting

    def log_message(self, *args):
        pass


class SlowRefusal(SlowAnswer):
    """A SlowAnswer with HTTP 403 that names no rate limit: no header of a rate limit, and no such text in its body."""

    status = 403


def http_server(test, handler, **attributes):
    """A threaded HTTP server on a free port of 127.0.0.1 that handler answers, with `attributes` for the handler to
    read and an event `release` of its own for the handler to wait for; its address.  The cleanup of test stops it:
    first each stand-in that it still runs and each wait for `release`, so that a request that hangs ends, and then
    the server."""
    server = http.server.ThreadingHTTPServer(("127.0.0.1", 0), handler)
    server.processes, server.release = [], threading.Event()
    for name, data in attributes.items():
        setattr(server, name, data)
    thread = threading.Thread(target=server.serve_forever, kwargs={"poll_interval": 0.05}, daemon=True)
    thread.start()

    def stop():
        for process in server.processes:
            if process.poll() is None:
                process.kill()
        server.release.set()        # a handler that waits for the event ends
        server.shutdown()
        server.server_close()
        thread.join()

    test.addCleanup(stop)
    return "http:" + "//%s:%d" % server.server_address        # in two parts, so that this file holds no link


def api_server(test, directory, token):
    """A StandInApi that answers from the stand-in in directory and takes `Bearer <token>` as the token of the run; its
    address, which a step reads as GITHUB_API_URL."""
    return http_server(test, StandInApi, directory=directory, token=token)


class Origin:
    """A scratch repository that a test makes its commits in (`src`, on branch main, its first commit `base` holding
    `files`), and the bare repository a job's checkout and fetches read as origin (`bare`).  publish() points the
    bare repository's main at the base and refs/pull/<n>/head at a head, as GitHub keeps the head of a pull request
    in the base repository, fork or not."""

    def __init__(self, root, files):
        self.src, self.bare = os.path.join(root, "src"), os.path.join(root, "origin.git")
        os.makedirs(self.src)
        for rel, data in files.items():
            self.write(rel, data)
        self.base = git_repo(self.src)
        git(root, "init", "-q", "--bare", self.bare)
        # the blobless fetches of a job read this origin as they read GitHub
        git(self.bare, "config", "uploadpack.allowFilter", "true")

    def write(self, rel, data):
        path = os.path.join(self.src, rel)
        os.makedirs(os.path.dirname(path), exist_ok=True)
        with open(path, "wb" if isinstance(data, bytes) else "w") as f:
            f.write(data)

    def commit(self, message, files=(), gitlinks=()):
        """Write files ({path: text}), add each of gitlinks ({path: commit}) as a submodule entry (mode 160000) with an
        empty folder at its path, as an uninitialised submodule has, and commit it all; the new commit."""
        for rel, data in dict(files).items():
            self.write(rel, data)
        git(self.src, "add", "-A")
        for rel, commit in dict(gitlinks).items():
            os.makedirs(os.path.join(self.src, rel))
            git(self.src, "update-index", "--add", "--cacheinfo", "160000,%s,%s" % (commit, rel))
        git(self.src, "commit", "-q", "--allow-empty", "-m", message)
        return git(self.src, "rev-parse", "HEAD")

    def publish(self, head, number=7):
        # The origin fetches from src, and src pushes nothing: a push from a machine of ours runs a leak check that
        # refuses the samples these tests plant, even into a scratch repository.
        git(self.src, "update-ref", "refs/published/base", self.base)
        git(self.src, "update-ref", "refs/published/head", head)
        git(self.bare, "fetch", "-q", self.src, "+refs/published/base:refs/heads/main",
            "+refs/published/head:refs/pull/%d/head" % number)

    def ref(self, name, commit):
        """Point the ref `name` of the bare repository at commit, by a fetch, as publish() does."""
        git(self.src, "update-ref", "refs/published/one", commit)
        git(self.bare, "fetch", "-q", self.src, "+refs/published/one:" + name)

    def places(self, head, base=None):
        """(the commits of `git log --reverse <base>..<head>`, the paths of `git diff --raw --no-renames <base>
        <head>`), each in git's order: commit K and path K of the scanner are their K-th entries.  base is the
        first commit when none is given."""
        base = base or self.base
        commits = git(self.src, "log", "--reverse", "--format=%H", "%s..%s" % (base, head)).split("\n")
        raw = git(self.src, "diff", "--raw", "--no-renames", base, head).split("\n")
        return commits, [line.split("\t", 1)[1] for line in raw if line]


def pull_request(origin, head, number=7, labels=(), event="pull_request", repository=PUBLIC):
    """The github context of a pull_request (or pull_request_review) event of pull request `number`, from main of
    origin at its base to head."""
    pr = {"number": number, "base": {"ref": "main", "sha": origin.base}, "head": {"ref": "a-branch", "sha": head},
          "labels": [{"name": label} for label in labels]}
    payload = {"action": "submitted" if event == "pull_request_review" else "synchronize", "number": number,
               "pull_request": pr}
    if event == "pull_request_review":
        payload["review"] = {"commit_id": head}
    return {"event_name": event, "repository": repository, "token": TOKEN, "sha": head,
            "ref": "refs/pull/%d/merge" % number, "event": payload}


# an object filter of GitHub's expressions: `a.b.*.c`, the c of each item of the array a.b
OBJECT_FILTER = re.compile(r"([A-Za-z_][A-Za-z0-9_.-]*)\.\*\.([A-Za-z_][A-Za-z0-9_-]*)")


def _contains(search, item):
    """GitHub's contains(): an item of an array, or a part of a string, without regard to case."""
    if isinstance(search, list):
        return any(gh_text(x).lower() == gh_text(item).lower() for x in search)
    return gh_text(item).lower() in gh_text(search).lower()


def value(text, scope, functions=None):
    """The value of a workflow key over scope, by helpers.gh_value, with the things these workflows use that gh_value
    does not read: an object filter, contains(), fromJSON(), each of `functions`, and a key of several expressions
    with text between them, which is that text with each value written into it."""
    if not isinstance(text, str):
        return text
    scope = dict(scope)

    def lift(found):
        items = scope
        for part in found.group(1).split("."):
            items = items.get(part) if isinstance(items, dict) else None
        name = "filtered%d" % len(scope)
        scope[name] = [item.get(found.group(2)) for item in items or [] if isinstance(item, dict)]
        return name

    text = OBJECT_FILTER.sub(lift, text)
    functions = dict({"contains": _contains, "fromJSON": json.loads}, **(functions or {}))
    # gh_value takes a key that starts with `${{` and ends with `}}` for one expression, from its first to its last
    pieces = re.split(r"(\$\{\{.*?\}\})", text, flags=re.S)
    if len(pieces) > 3:
        return "".join(gh_text(gh_value(piece, scope, functions)) if piece.startswith("${{") else piece
                       for piece in pieces)
    return gh_value(text, scope, functions)


def condition(text, scope, functions=None):
    """Whether a job's or a step's `if:` holds.  GitHub reads it as an expression whether or not it is written in
    ${{ }}.  To an `if:` that names no status function GitHub adds success(): Job.run() does that for a step."""
    if text is None:
        return True
    text = str(text).strip()
    if not (text.startswith("${{") and text.endswith("}}")):
        text = "${{ %s }}" % text
    return gh_truthy(value(text, scope, functions))


# a status function in a step's `if:`, which GitHub then evaluates also after a step failed
STATUS_FUNCTION = re.compile(r"\b(?:always|cancelled|failure|success)\s*\(")


class Job:
    """One job of a workflow, run as GitHub runs it on one event, against an Origin.  run() takes the steps in order;
    after a step fails, each later one is skipped, as GitHub skips a step with no status function in its `if:`, and a
    step whose `if:` names one (always(), cancelled(), failure(), success()) is judged by it.  The
    checkout step is emulated: every branch of origin with no blob (fetch-depth 0, filter blob:none), the step's own
    sparse-checkout patterns, and a detached checkout of the step's own `ref`.  A `run:` step runs its own text, or
    the text that `edits` gives for its name, in that checkout, with the workflow's, the job's and the step's `env`,
    the stand-in gh first on PATH, and GITHUB_API_URL at a StandInApi of the same stand-in, which the first `run:`
    step starts.  Each step is {name, outcome, status, stdout, stderr, calls} in `steps`, where `calls` holds the
    calls of the stand-in that the step made, as gh or by HTTP, and `calls` of the job holds those of every step.

    The stand-in gh is a new one that answers from gh_state, or the one in the directory `gh`, which several jobs
    then share.  needs, matrix and secrets are the job's contexts of those names.  variables are more variables of
    every step's environment, under the workflow's own."""

    def __init__(self, test, workflow, name, github, origin, gh_state=None, inputs=None, gh=None, needs=None,
                 matrix=None, secrets=None, variables=None):
        self.test, self.origin = test, origin
        self.workflow = yamlio.load_file(workflow)
        self.job = self.workflow["jobs"][name]
        self.scope = {"github": github, "inputs": inputs or {}, "env": {}, "steps": {}, "needs": needs or {},
                      "matrix": matrix or {}, "secrets": secrets or {}}
        self.dir = tempfile.mkdtemp()
        test.addCleanup(shutil.rmtree, self.dir)
        self.work, self.temp, self.home = (os.path.join(self.dir, d) for d in ("work", "runner-temp", "home"))
        os.makedirs(self.temp)
        os.makedirs(self.home)
        self.gh = gh or install_gh(os.path.join(self.dir, "bin"), dict(gh_state or {}, git=origin.bare))
        self.variables = dict(variables or {})
        self.edits, self.steps, self.calls, self.api = {}, [], [], None

    def runs(self):
        return condition(self.job.get("if"), self.scope)

    def outputs(self):
        """The job's outputs, as a job that needs it reads them."""
        return {key: gh_text(value(text, self.scope)) for key, text in (self.job.get("outputs") or {}).items()}

    def failed(self):
        return any(s["outcome"] == "failure" for s in self.steps)

    def run(self):
        self.test.assertTrue(self.runs(), "the job's if: does not hold")
        for block in (self.workflow.get("env"), self.job.get("env")):
            for key, text in (block or {}).items():
                self.scope["env"][key] = gh_text(value(text, self.scope))
        seen = len(gh_calls(self.gh))
        for step in self.job["steps"]:
            name = step.get("name") or step["uses"]
            failed = self.failed()
            functions = {"always": lambda: True, "cancelled": lambda: False, "failure": lambda: failed,
                         "success": lambda: not failed}
            judged = STATUS_FUNCTION.search(str(step.get("if") or ""))
            if (failed and not judged) or not condition(step.get("if"), self.scope, functions):
                self.steps.append({"name": name, "outcome": "skipped", "status": None, "stdout": "", "stderr": "",
                                   "calls": []})
                continue
            if "uses" in step:
                status, stdout, stderr, outputs = self.checkout(step), "", "", {}
            else:
                status, stdout, stderr, outputs = self.shell(step)
            outcome = "failure" if status else "success"
            calls = gh_calls(self.gh)
            self.steps.append({"name": name, "outcome": outcome, "status": status, "stdout": stdout,
                               "stderr": stderr, "calls": calls[seen:]})
            seen = len(calls)
            if step.get("id"):
                self.scope["steps"][step["id"]] = {"outputs": outputs, "outcome": outcome}
        self.calls = [c for s in self.steps for c in s["calls"]]
        return self

    def step(self, name):
        found = [s for s in self.steps if s["name"] == name]
        self.test.assertEqual(len(found), 1, (name, [s["name"] for s in self.steps]))
        return found[0]

    def outcomes(self):
        return [(s["name"], s["outcome"]) for s in self.steps]

    def output(self):
        """Everything the job's steps printed."""
        return "".join(s["stdout"] + s["stderr"] for s in self.steps)

    def checkout(self, step):
        self.test.assertTrue(step["uses"].startswith("actions/checkout@"), step["uses"])
        given = step.get("with") or {}
        cone = given.get("sparse-checkout-cone-mode", True) not in (False, "false")
        git(self.dir, "init", "-q", self.work)
        git(self.work, "remote", "add", "origin", "file://" + self.origin.bare)
        git(self.work, "fetch", "-q", "--filter=blob:none", "origin", "+refs/heads/*:refs/remotes/origin/*")
        git(self.work, "sparse-checkout", "set", "--cone" if cone else "--no-cone",
            *str(given["sparse-checkout"]).split())
        git(self.work, "checkout", "-q", "--detach", gh_text(value(given["ref"], self.scope)))
        return 0

    def shell(self, step):
        text = self.edits.get(step.get("name"), step["run"])
        self.test.assertNotIn("${{", text, "a run: text with an expression in it")
        output = os.path.join(self.temp, "output-%d" % len(self.steps))
        github = self.scope["github"]
        if self.api is None:
            self.api = api_server(self.test, self.gh, github["token"])
        env = child_environment(self.home, PATH=self.gh + os.pathsep + os.environ["PATH"], GIT_CONFIG_NOSYSTEM="1",
                                CI="true", RUNNER_TEMP=self.temp, GITHUB_OUTPUT=output, GITHUB_WORKSPACE=self.work,
                                GITHUB_REPOSITORY=github["repository"], GITHUB_EVENT_NAME=github["event_name"],
                                GITHUB_API_URL=self.api)
        env.update(self.variables)
        env.update(self.scope["env"])
        env.update({key: gh_text(value(v, self.scope)) for key, v in (step.get("env") or {}).items()})
        os.makedirs(self.work, exist_ok=True)       # the workspace is there for a job that checks nothing out too
        r = subprocess.run(["bash", "--noprofile", "--norc", "-eo", "pipefail", "-c", text], cwd=self.work, env=env,
                           capture_output=True, text=True)
        outputs = {}
        if os.path.exists(output):
            with open(output) as f:
                outputs = dict(line.rstrip("\n").split("=", 1) for line in f if "=" in line)
        return r.returncode, r.stdout, r.stderr, outputs


def load_scanner(path=SCANNER):
    spec = importlib.util.spec_from_file_location("held_content_scan_under_test", path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def draw(n, alphabet):
    """n bytes of alphabet from os.urandom, as the scanner's self-test draws a canary from /dev/urandom."""
    return bytes(alphabet[c % len(alphabet)] for c in os.urandom(n))


def sample(name):
    """A fresh sample of the row `name` of detectors.tsv, drawn from its canary template, which the row's own
    pattern finds: the text a pull request must not add."""
    scanner = load_scanner()
    with open(DETECTORS, encoding="utf-8") as f:
        rows = {d.name: d for d in scanner.parse_table(f.read(), "detectors.tsv")}
    text = scanner.draw_canary(rows[name].canary, draw)
    assert rows[name].rx.search(text), name
    return text.decode("ascii")


# hit lines, as the scanner prints them
HIT = re.compile(r"^  (\S.*?)  (detector \S+ \(\S+\)|private row \d+)$")


def hits(stdout):
    """(place, detector) of each hit line of the scanner's output."""
    return [found.groups() for found in map(HIT.match, stdout.split("\n")) if found]


class Covers:
    def assertCovers(self, stdout):
        """The first line says that the run covers the patterns of detectors.tsv only and that the private table runs
        in held-content-private.yml."""
        first = stdout.split("\n")[0]
        for word in ("detectors.tsv", " only", "held-content-private.yml"):
            self.assertIn(word, first, stdout)


def held_origin(test, files):
    """An Origin in a scratch folder that test deletes after it.  Its first commit holds the files of .github/held and
    files ({path: text})."""
    root = tempfile.mkdtemp()
    test.addCleanup(shutil.rmtree, root)
    held = {}
    for path in HELD_FILES:
        with open(path, "rb") as f:
            held[".github/held/" + os.path.basename(path)] = f.read()
    return Origin(os.path.join(root, "repository"), dict(held, **files))


@unittest.skipIf(HELD_CONTENT_ABSENT, HELD_CONTENT_ABSENT)
class HeldContentWorkflow(Covers, unittest.TestCase):
    """held-content.yml on a pull_request event, with no HELD_CONTENT_RULES: the job's if:, the checkout of the base
    (sparse, .github/held alone), the range step and the scan step."""

    def setUp(self):
        self.origin = held_origin(self, {"README.md": "A scratch repository of the held-content tests.\n",
                                         "docs/a.txt": "the first line\n"})

    def job(self, head, labels=()):
        self.origin.publish(head)
        return Job(self, HELD_CONTENT, "held-content", pull_request(self.origin, head, labels=labels), self.origin)

    def test_it_starts_on_pull_request_with_no_secret_and_runs_in_the_public_repository_alone(self):
        workflow = yamlio.load_file(HELD_CONTENT)
        self.assertEqual(workflow["name"], "held-content")
        self.assertNotIn("pull_request_target", workflow["on"])
        self.assertEqual(workflow["on"]["pull_request"],
                         {"types": ["opened", "synchronize", "reopened", "labeled", "unlabeled"]})
        with open(HELD_CONTENT, encoding="utf-8") as f:
            self.assertNotIn("secrets.", f.read())
        head = self.origin.commit("a clean change", {"docs/b.txt": "nothing held here\n"})
        self.assertTrue(self.job(head).runs())
        self.assertFalse(Job(self, HELD_CONTENT, "held-content",
                             pull_request(self.origin, head, repository="acme/proofs"), self.origin).runs())

    def test_a_clean_change_passes_and_says_it_covers_detectors_tsv_only(self):
        head = self.origin.commit("a clean change", {"docs/b.txt": "nothing held here\n"})
        job = self.job(head).run()
        self.assertEqual([o for _, o in job.outcomes()], ["success", "success", "skipped", "success"], job.output())
        scan = job.step(SCAN)
        self.assertCovers(scan["stdout"])
        self.assertIn(head, scan["stdout"])
        self.assertIn("HELD CONTENT: clean", scan["stdout"])

    def test_a_sample_fails_the_scan_which_names_its_place_by_number_alone(self):
        in_message, in_name, in_line = sample("github-token"), sample("aws-key"), sample("slack-token")
        first = self.origin.commit("a first, clean commit", {"docs/b.txt": "clean\n"})
        head = self.origin.commit("a second commit\n\nIt quotes %s here.\n" % in_message, {
            "notes/%s.txt" % in_name: "clean\n", "docs/a.txt": "the first line\n%s\n" % in_line})
        job = self.job(head).run()
        scan = job.step(SCAN)
        self.assertEqual(scan["status"], 3, job.output())
        commits, paths = self.origin.places(head)
        self.assertEqual(sorted(hits(scan["stdout"])), sorted([
            ("commit %d" % (commits.index(head) + 1), "detector github-token (secret)"),
            ("path %d" % (paths.index("notes/%s.txt" % in_name) + 1), "detector aws-key (secret)"),
            ("path %d line 2" % (paths.index("docs/a.txt") + 1), "detector slack-token (secret)")]))
        self.assertCovers(scan["stdout"])
        self.assertIn(head, scan["stdout"])
        for withheld in (in_message, in_name, in_line, "notes/", "docs/a.txt"):
            self.assertNotIn(withheld, job.output())
        # the scan names the head and no other commit
        for other in (first, self.origin.base):
            self.assertNotIn(other[:7], scan["stdout"] + scan["stderr"])

    def test_a_submodule_is_a_path_with_no_text(self):
        in_name = sample("aws-key")
        head = self.origin.commit("two submodules", gitlinks={"vendor/lib": self.origin.base,
                                                              "vendor/%s" % in_name: self.origin.base})
        job = self.job(head).run()
        scan = job.step(SCAN)
        self.assertEqual(scan["status"], 3, job.output())
        _, paths = self.origin.places(head)
        self.assertEqual(paths, ["vendor/%s" % in_name, "vendor/lib"])
        self.assertEqual(hits(scan["stdout"]), [("path 1", "detector aws-key (secret)")])
        self.assertNotIn(in_name, job.output())

    def test_the_demonstration_plants_every_pattern_of_detectors_tsv_and_ends_red(self):
        head = self.origin.commit("a clean change", {"docs/b.txt": "nothing held here\n"})
        job = self.job(head, labels=("prove-it-can-fail",))
        plant = next(s for s in job.job["steps"] if s.get("name") == PLANT)["run"]
        self.assertIn("/tmp/planted.txt", plant)
        # the step writes its canaries to the runner's /tmp; here they go to the job's own folder
        job.edits[PLANT] = plant.replace("/tmp/planted.txt", os.path.join(job.temp, "planted.txt"))
        job.run()
        self.assertEqual(job.step(SCAN)["outcome"], "skipped")
        step = job.step(PLANT)
        self.assertEqual(step["outcome"], "failure", job.output())
        self.assertIn("::error::HELD CONTENT:", step["stdout"], job.output())
        # the scan's exit 3 does not end the step: the step reports it, and then ends red on purpose
        lines = step["stdout"].split("\n")
        self.assertIn("The scan of the planted commit exited 3 (3 is a refusal).", lines, job.output())
        self.assertIn("::error::demonstration: the check refused the planted canaries, as it must. This run is red "
                      "on purpose.", lines, job.output())
        self.assertEqual(step["status"], 1, job.output())
        self.assertCovers(step["stdout"])
        with open(DETECTORS, encoding="utf-8") as f:
            public = {d.name for d in load_scanner().parse_table(f.read(), "detectors.tsv")}
        found = {d.split()[1] for _, d in hits(step["stdout"])}
        self.assertEqual(public - found, set(), "a pattern of detectors.tsv the demonstration did not plant")


# the files that one change of the next class changes
MANY = 12


def fetches(trace):
    """The count of the `git fetch` processes in trace, a file that GIT_TRACE2_EVENT names: each git process writes
    one `start` event there, with its arguments."""
    with open(trace, encoding="utf-8") as f:
        events = [json.loads(line) for line in f if line.strip()]
    return sum(1 for event in events if event.get("event") == "start" and "fetch" in event.get("argv", ()))


@unittest.skipIf(HELD_CONTENT_ABSENT, HELD_CONTENT_ABSENT)
class HeldContentFetches(unittest.TestCase):
    """The scan of held-content.yml gets the blobs of a change of MANY files into its blobless checkout with ONE `git
    fetch`.  Without that fetch, `git cat-file --batch` fetches each missing blob with a `git fetch` of its own, two
    for each changed path, so a large pull request can run past the 10 minutes of the job.  A step runs its own text
    with GIT_TRACE2_EVENT set, and the test counts the fetches in the trace.  The verdict is the one that a full clone
    of the same origin gives, and the full clone makes no fetch: its remote is gone."""

    def setUp(self):
        self.origin = held_origin(self, {"docs/f%02d.txt" % k: "the first line of file %d\n" % k
                                         for k in range(1, MANY + 1)})
        # GitHub gives an object of the repository by its id, which is how a partial clone asks for a blob
        git(self.origin.bare, "config", "uploadpack.allowAnySHA1InWant", "true")

    def change(self, lines=None):
        """A head that adds a second line to each of the MANY files: lines[k] to file k when lines has k."""
        lines = lines or {}
        return self.origin.commit("a change of %d files" % MANY, {
            "docs/f%02d.txt" % k: "the first line of file %d\n%s\n" % (k, lines.get(k, "a second line"))
            for k in range(1, MANY + 1)})

    def traced(self, job, name):
        """Run job, and the count of the fetches of its step `name`.  That step runs its own text (or the text of
        job.edits) with GIT_TRACE2_EVENT set.  The range step fetches the head, and the count leaves that fetch out."""
        trace = os.path.join(job.temp, "trace2.json")
        text = job.edits.get(name) or next(s for s in job.job["steps"] if s.get("name") == name)["run"]
        job.edits[name] = "export GIT_TRACE2_EVENT=%s\n%s" % (shlex.quote(trace), text)
        job.run()
        return fetches(trace)

    def scan(self, head):
        """The scan step of the job on a pull request from main to head, and the count of its fetches."""
        self.origin.publish(head)
        job = Job(self, HELD_CONTENT, "held-content", pull_request(self.origin, head), self.origin)
        count = self.traced(job, SCAN)
        return job.step(SCAN), count

    def full_clone_scan(self, head):
        """The scan step's command in a full clone of origin that holds head, with GIT_TRACE2_EVENT set, after the
        clone's remote is gone: its result, and the count of its fetches."""
        d = tempfile.mkdtemp()
        self.addCleanup(shutil.rmtree, d)
        clone = os.path.join(d, "clone")
        git(d, "clone", "-q", "-b", "main", "file://" + self.origin.bare, clone)
        git(clone, "fetch", "-q", "origin", "refs/pull/7/head:refs/held-content/head")
        git(clone, "remote", "set-url", "origin", "file://" + os.path.join(d, "gone.git"))
        base = git(clone, "merge-base", self.origin.base, head)
        trace = os.path.join(d, "trace2.json")
        r = subprocess.run([sys.executable, ".github/held/held_content_scan.py", "--public-only", "--commits", base,
                            head], cwd=clone, capture_output=True, text=True,
                           env=child_environment(NO_HOME, GIT_CONFIG_NOSYSTEM="1", GIT_TRACE2_EVENT=trace))
        return r, fetches(trace)

    def test_a_clean_change_of_many_files_is_read_with_one_fetch_and_passes_as_in_a_full_clone(self):
        head = self.change()
        scan, count = self.scan(head)
        self.assertEqual(scan["status"], 0, scan["stdout"] + scan["stderr"])
        self.assertIn("HELD CONTENT: clean", scan["stdout"])
        self.assertEqual(count, 1, "the git fetches of the scan of %d changed files" % MANY)
        full, full_count = self.full_clone_scan(head)
        self.assertEqual((full.returncode, full_count), (0, 0), full.stdout + full.stderr)
        self.assertEqual(scan["stdout"], full.stdout)

    def test_a_sample_in_a_change_of_many_files_is_read_with_one_fetch_and_gets_the_hits_of_a_full_clone(self):
        head = self.change({1: sample("slack-token"), MANY: sample("github-token")})
        scan, count = self.scan(head)
        self.assertEqual(scan["status"], 3, scan["stdout"] + scan["stderr"])
        self.assertEqual(count, 1, "the git fetches of the scan of %d changed files" % MANY)
        _, paths = self.origin.places(head)
        self.assertEqual(hits(scan["stdout"]), [
            ("path %d line 2" % (paths.index("docs/f01.txt") + 1), "detector slack-token (secret)"),
            ("path %d line 2" % (paths.index("docs/f%02d.txt" % MANY) + 1), "detector github-token (secret)")])
        full, full_count = self.full_clone_scan(head)
        self.assertEqual((full.returncode, full_count), (3, 0), full.stdout + full.stderr)
        self.assertEqual(scan["stdout"], full.stdout)

    def test_the_demonstration_fetches_once_and_asks_for_no_blob_that_its_clone_alone_has(self):
        # Main moved after the head branched off.  So the range from the merge base holds the commit of main, whose
        # blobs the clone does not have, and the planted commit, whose blob is in the clone alone: the remote refuses
        # a fetch that asks for that blob.
        first = self.origin.base
        head = self.change()
        git(self.origin.src, "checkout", "-q", "-b", "moved", first)
        moved = self.origin.commit("main moves", {"docs/f01.txt": "the first line of file 1\nmain's own line\n"})
        self.origin.publish(head)
        self.origin.ref("refs/heads/main", moved)
        github = pull_request(self.origin, head, labels=("prove-it-can-fail",))
        github["event"]["pull_request"]["base"]["sha"] = moved
        job = Job(self, HELD_CONTENT, "held-content", github, self.origin)
        plant = next(s for s in job.job["steps"] if s.get("name") == PLANT)["run"]
        # the step writes its canaries to the runner's /tmp; here they go to the job's own folder
        job.edits[PLANT] = plant.replace("/tmp/planted.txt", os.path.join(job.temp, "planted.txt"))
        count = self.traced(job, PLANT)
        step = job.step(PLANT)
        self.assertIn("The scan of the planted commit exited 3 (3 is a refusal).", step["stdout"].split("\n"),
                      job.output())
        self.assertEqual(count, 1, job.output())


def pin_of(table):
    """The text of private-detectors.sha256 that names table: its sha256, of the text as the scanner normalises it,
    and its row count."""
    text = table.replace("\r\n", "\n").rstrip("\n") + "\n"
    rows = [line for line in text.split("\n") if line.strip() and not line.lstrip().startswith("#")]
    return "%s %d\n" % (hashlib.sha256(text.encode()).hexdigest(), len(rows))


# A made-up private table in the secret's format.  A comment and a blank line come first, so that a row's number, its
# line in the text, is not its place among the rows.  Its names and its category are words that no other output holds.
MADE_UP_TABLE = ("# a made-up private table\n\n"
                 "made-up-first\tmade-up-kind\t-\t\\bqzvx[0-9a-f]{16}\\b\tqzvx{16:hex}\n"
                 "made-up-second\tmade-up-kind\ti\t\\bwqkj-[a-z0-9-]{12}\twqkj-{12:lowerdash}\n")


@unittest.skipIf(HELD_ABSENT, HELD_ABSENT)
class ScannerSelfTest(Covers, unittest.TestCase):
    """held_content_scan.py with the real detectors.tsv and must-pass-lines.txt, and with a scratch copy of
    .github/held whose pin names a made-up private table."""

    def scan(self, held, *args, rules=None, cwd=None, **variables):
        env = child_environment(NO_HOME, **variables)
        if rules is not None:
            env["HELD_CONTENT_RULES"] = rules
        return subprocess.run([sys.executable, os.path.join(held, "held_content_scan.py"), *args], env=env, cwd=cwd,
                              capture_output=True, text=True)

    def held_with(self, table):
        """A scratch copy of .github/held whose pin names table (pin_of)."""
        d = tempfile.mkdtemp()
        self.addCleanup(shutil.rmtree, d)
        for path in HELD_FILES:
            shutil.copyfile(path, os.path.join(d, os.path.basename(path)))
        with open(os.path.join(d, "private-detectors.sha256"), "w") as f:
            f.write(pin_of(table))
        return d

    def test_the_public_table_passes_its_self_test_with_public_only(self):
        r = self.scan(HELD, "--self-test", "--public-only")
        self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
        self.assertCovers(r.stdout)

    def test_without_public_only_a_missing_secret_stops_the_run(self):
        r = self.scan(HELD, "--self-test")
        self.assertEqual(r.returncode, 2, r.stdout + r.stderr)
        self.assertIn("HELD_CONTENT_RULES is not set", r.stderr)

    def test_a_made_up_private_table_that_matches_its_pin_passes(self):
        r = self.scan(self.held_with(MADE_UP_TABLE), "--self-test", rules=MADE_UP_TABLE)
        self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
        for withheld in ("made-up-first", "made-up-second", "made-up-kind", "qzvx", "wqkj"):
            self.assertNotIn(withheld, r.stdout + r.stderr)

    def test_a_private_row_that_cannot_work_is_named_by_its_number_alone(self):
        for why, row in (
                ("it misses its own canary", "made-up-missing\tmade-up-kind\t-\t\\bqzvy[0-9]{20}\tqzvy{4:hex}"),
                ("it does not compile", "made-up-broken\tmade-up-kind\t-\tqzvy(\tqzvy{4:hex}"),
                ("it repeats a name", "made-up-first\tmade-up-kind\t-\t\\bqzvy[0-9a-f]{8}\tqzvy{8:hex}")):
            with self.subTest(why=why):
                table = MADE_UP_TABLE + row + "\n"
                r = self.scan(self.held_with(table), "--self-test", rules=table)
                self.assertEqual(r.returncode, 2, r.stdout + r.stderr)
                self.assertIn("private row 5", r.stdout + r.stderr)   # line 5 of the table's text
                for withheld in (row.split("\t")[0], "made-up-kind", "qzvy"):
                    self.assertNotIn(withheld, r.stdout + r.stderr)

    def test_a_hit_of_a_private_row_names_no_row_and_no_category_and_never_its_text(self):
        held = self.held_with(MADE_UP_TABLE)
        root = tempfile.mkdtemp()
        self.addCleanup(shutil.rmtree, root)
        origin = Origin(root, {"README.md": "A scratch repository.\n"})
        planted = load_scanner().draw_canary("qzvx{16:hex}", draw).decode("ascii")
        head = origin.commit("a change", {"docs/b.txt": "clean\n%s\n" % planted})
        # HELD_CONTENT_SHOW_MATCHES shows the text with --files alone
        r = self.scan(held, "--commits", origin.base, head, rules=MADE_UP_TABLE, cwd=origin.src,
                      HELD_CONTENT_SHOW_MATCHES="1")
        self.assertEqual(r.returncode, 3, r.stdout + r.stderr)
        self.assertEqual(hits(r.stdout), [("path 1 line 2", "private row 3")])
        for withheld in (planted, "made-up-first", "made-up-kind", "docs/b.txt", origin.base[:12]):
            self.assertNotIn(withheld, r.stdout + r.stderr)
        self.assertIn(head, r.stdout)


@unittest.skipIf(GUARDS_ABSENT, GUARDS_ABSENT)
class GuardSelfTests(unittest.TestCase):
    """The self-tests of statement_freeze.py and pin_coherence.py pass, as their workflows run them before a change."""

    def test_each_guard_passes_its_self_test(self):
        for script in (STATEMENT_FREEZE, PIN_COHERENCE):
            with self.subTest(script=os.path.basename(script)):
                r = subprocess.run([sys.executable, script, "--self-test"], env=child_environment(NO_HOME),
                                   capture_output=True, text=True)
                self.assertEqual(r.returncode, 0, r.stdout + r.stderr)


# The made-up private table of the private workflow's tests: one row for each letter of ROWS, after a comment and a
# blank line, so that row k (from 0) is line k + 3 of the text.  A sample of a row is `qzv`, the row's letter and 12
# hex digits.  No letter is a hex digit, so no row finds the sample of another row.
ROWS = "ghjkmnpqrstv"
PRIVATE_TABLE = "# a made-up private table\n\n" + "".join(
    "made-up-%s\tmade-up-kind\t-\t\\bqzv%s[0-9a-f]{12}\\b\tqzv%s{12:hex}\n" % (letter, letter, letter)
    for letter in ROWS)
# github.server_url and github.run_id of a run.  The address is in two parts, so that this file holds no link.
SERVER = "https:" + "//github.com"
RUN_ID = "4242"


def row(k):
    """How the scanner names row k (from 0) of PRIVATE_TABLE."""
    return "private row %d" % (k + 3)


def mark(k):
    """A fresh sample of row k (from 0) of PRIVATE_TABLE: text that a pull request must not add."""
    return "qzv%s%s" % (ROWS[k], draw(12, b"0123456789abcdef").decode("ascii"))


def status(state, description="", at="2026-11-01T00:00:00Z", context=CONTEXT, login=ACTIONS, id=None):
    """A status that a head has before a run, as the stand-in gh takes it in state["statuses"]: with the id `id`, else
    with the id that the stand-in gives it."""
    made = {"state": state, "description": description, "context": context, "created_at": at, "login": login}
    return made if id is None else dict(made, id=id)


class Run:
    """One run of held-content-private.yml on one event, job by job as GitHub runs them: find, when its `if:` holds;
    then, when find passed and the `if:` of scan holds, one scan job for each entry of find's matrix; and demonstrate,
    when its `if:` holds.  Every job calls the stand-in in the directory `gh`, as gh and by HTTP.  secret is the value
    of HELD_CONTENT_RULES, "" for a repository that has none.  No job prints the token of the run."""

    def __init__(self, test, github, origin, gh, secret, inputs=None, variables=None, edits=None):
        def job(name, **contexts):
            made = Job(test, PRIVATE, name, github, origin, gh=gh, inputs=inputs, variables=variables,
                       secrets={"HELD_CONTENT_RULES": secret}, **contexts)
            made.edits.update(edits or {})
            return made

        self.find, self.scans, self.demonstrate = job("find"), [], job("demonstrate")
        if self.find.runs() and not self.find.run().failed():
            needs = {"find": {"result": "success", "outputs": self.find.outputs()}}
            plan = job("scan", needs=needs)
            if plan.runs():
                for entry in value(plan.job["strategy"]["matrix"]["include"], plan.scope):
                    self.scans.append(job("scan", needs=needs, matrix=entry).run())
        if self.demonstrate.runs():
            self.demonstrate.run()
        # The scan step sends the token to the stand-in GitHub API, and the other steps give it to gh.
        test.assertNotIn(github["token"], self.output())

    def output(self):
        """Everything the jobs of the run printed."""
        return "".join(job.output() for job in [self.find] + self.scans + [self.demonstrate])


class Private(unittest.TestCase):
    """What the tests of the private workflow share: a scratch origin whose main holds .github/held with a pin for a
    made-up private table, the open pull requests that the stand-in gh serves, one run of the workflow, and what git
    says the scan must print."""

    def setUp(self):
        self.root = tempfile.mkdtemp()
        self.addCleanup(shutil.rmtree, self.root)
        self.gh = os.path.join(self.root, "gh")

    def repository(self, files=(), table=PRIVATE_TABLE, name="repository"):
        """A scratch origin (self.origin) whose first commit, which main is at, holds the four files of .github/held,
        the pin among them naming table, and `files`."""
        held = {}
        for path in HELD_FILES:
            with open(path, "rb") as f:
                held[".github/held/" + os.path.basename(path)] = f.read()
        held[".github/held/private-detectors.sha256"] = pin_of(table)
        held["README.md"] = "A scratch repository of the private held-content tests.\n"
        held.update(files)
        self.origin = Origin(os.path.join(self.root, name), held)
        self.origin.ref("refs/heads/main", self.origin.base)
        return self.origin

    def clean_heads(self, count):
        """A scratch origin and `count` heads, each one clean commit on a branch of its own from the first commit."""
        origin, heads = self.repository({"docs/a.txt": "the first line\n"}), []
        for n in range(1, count + 1):
            git(origin.src, "checkout", "-q", "-B", "topic-%d" % n, origin.base)
            heads.append(origin.commit("a clean change %d" % n, {"docs/change-%d.txt" % n: "nothing held here\n"}))
        git(origin.src, "checkout", "-q", "main")
        return origin, heads

    def two_heads(self, name, clean, held, first=(("docs/a.txt", "the first line\n"),)):
        """A scratch origin whose first commit holds the files `first`, and two heads of one commit each over that
        commit, on branches of their own: clean and held, each (message, files).  Returns (the origin, the head clean,
        the head held)."""
        origin = self.repository(first, name=name)
        heads = []
        for branch, (message, files) in (("clean", clean), ("held", held)):
            git(origin.src, "checkout", "-q", "-B", branch, origin.base)
            heads.append(origin.commit(message, files))
        git(origin.src, "checkout", "-q", "main")
        return origin, heads[0], heads[1]

    def verdicts(self, origin, clean, held, sample, gh):
        """Scan the head clean (pull request 7) and the head held (pull request 8) of origin in one scheduled run:
        held's hits are git's places of sample, held gets `failure` and clean gets `success`."""
        gh = self.serve({"number": 7, "head": clean}, {"number": 8, "head": held}, gh=os.path.join(self.root, gh))
        run = self.run_workflow("schedule", gh=gh)
        scans = {job.scope["matrix"]["head"]: job for job in run.scans}
        self.assertEqual(sorted(hits(scans[held].step(API_SCAN)["stdout"])),
                         sorted(self.expected(held, origin.base, {0: sample})), run.output())
        self.assertEqual(sorted(self.states(gh)), sorted([(clean, "success"), (held, "failure")]), run.output())

    def serve(self, *pulls, gh=None, **state):
        """Make the stand-in gh (in self.gh, or in gh) serve the open pull requests `pulls`, each {"number", "head"}
        with "base" and "labels", and the rest of `state`.  The head of each goes to refs/pull/<n>/head of origin, as
        GitHub keeps it, fork or not."""
        for p in pulls:
            self.origin.ref("refs/pull/%d/head" % p["number"], p["head"])
        return install_gh(gh or self.gh, dict(state, pulls=list(pulls), git=self.origin.bare))

    def github(self, event, head=None, ref="refs/heads/main", repository=PUBLIC, **run):
        """The github context of a run on event, which GitHub starts from main.  A workflow_run event is of a
        pull_request run of held-content.yml at head, with an empty pull_requests list, as for a fork's pull request;
        `run` gives other values of its workflow_run."""
        github = {"event_name": event, "repository": repository, "token": TOKEN, "ref": ref,
                  "sha": git(self.origin.bare, "rev-parse", "refs/heads/main"), "server_url": SERVER,
                  "run_id": RUN_ID, "event": {}}
        if event == "workflow_run":
            github["event"] = {"workflow_run": dict({
                "event": "pull_request", "path": ".github/workflows/held-content.yml", "head_sha": head,
                "pull_requests": [], "conclusion": "success"}, **run)}
        return github

    def run_workflow(self, event="workflow_run", head=None, secret=PRIVATE_TABLE, gh=None, inputs=None,
                     variables=None, edits=None, **github):
        """One Run on event.  The scanner waits no time between its requests: the tests of its spacing are apart."""
        return Run(self, self.github(event, head, **github), self.origin, gh or self.gh, secret, inputs=inputs,
                   variables=dict({"HELD_CONTENT_REQUEST_GAP": "0"}, **(variables or {})), edits=edits)

    def posted(self, gh=None):
        """Each status posted so far.  Each has the name of this workflow and the address of the run, has a
        description that GitHub takes, and is no `pending`."""
        made = posted_statuses(gh or self.gh)
        for s in made:
            self.assertEqual(set(s), {"state", "description", "context", "target_url", "sha", "id", "created_at",
                                      "creator"})
            self.assertEqual((s["context"], s["target_url"]),
                             (CONTEXT, "%s/%s/actions/runs/%s" % (SERVER, PUBLIC, RUN_ID)))
            self.assertIn(s["state"], ("success", "failure", "error"))
            self.assertLessEqual(len(s["description"]), 140)
        return made

    def states(self, gh=None):
        return [(s["sha"], s["state"]) for s in self.posted(gh)]

    def assertPosted(self, expected, gh=None):
        """The statuses posted so far are expected, each (head, state, description)."""
        self.assertEqual([(s["sha"], s["state"], s["description"]) for s in self.posted(gh)], expected)

    def blob(self, oid):
        done = subprocess.run(["git", "-C", self.origin.src, "cat-file", "blob", oid], capture_output=True, check=True)
        return done.stdout.decode("latin-1")

    def expected(self, head, base, marks):
        """What git says the scan must print for base..head, as a set of (place, row): for each of marks ({row from
        0: sample}), the commits of `git log --reverse` whose message holds it, the paths of `git diff --raw
        --no-renames` whose name holds it, and the lines that hold it and are new in a path.  A file with a zero
        byte is left to the test."""
        src, out = self.origin.src, set()

        def find(place, text):
            out.update((place, row(k)) for k, sample in marks.items() if re.search(r"\b%s\b" % sample, text))

        for k, commit in enumerate(filter(None, self.origin.places(head, base)[0]), 1):
            find("commit %d" % k, git(src, "log", "-1", "--format=%B", commit))
        raw = git(src, "diff", "--raw", "--no-renames", "--abbrev=40", base, head)
        for k, line in enumerate(raw.split("\n") if raw else [], 1):
            meta, path = line.split("\t", 1)
            old_mode, new_mode, old, new = meta.lstrip(":").split()[:4]
            find("path %d" % k, path)
            absent_or_submodule = ("000000", "160000")
            text = "" if new_mode in absent_or_submodule else self.blob(new)
            if "\0" in text:
                continue
            before = set() if old_mode in absent_or_submodule else set(self.blob(old).split("\n"))
            for n, new_line in enumerate(text.split("\n"), 1):
                if new_line not in before:
                    find("path %d line %d" % (k, n), new_line)
        return out


@unittest.skipIf(PRIVATE_ABSENT, PRIVATE_ABSENT)
class PrivateFind(Private):
    """Which heads a run of held-content-private.yml scans: the `if:` of each job, and the job find."""

    def test_a_fork_s_pull_request_whose_event_lists_no_pull_request_is_found_by_its_head(self):
        _, (other, head) = self.clean_heads(2)
        # one pull request on a page: the head of the run is on the second page of the open pull requests
        self.serve({"number": 7, "head": other}, {"number": 8, "head": head}, page_size=1)
        run = self.run_workflow("workflow_run", head)
        self.assertEqual(run.find.scope["github"]["event"]["workflow_run"]["pull_requests"], [])
        self.assertEqual(run.find.outputs(), {"count": "1", "matrix": json.dumps([{"head": head, "numbers": "8"}])})
        # one read, of every page, with no --jq: on workflow_run the job reads no status
        self.assertEqual([(c["method"], c["endpoint"], c["pages"]) for c in run.find.calls],
                         [("GET", "repos/%s/pulls?state=open&per_page=100" % PUBLIC, 2)])
        self.assertEqual(run.find.calls[0]["argv"][:3], ["api", "--paginate", "--slurp"])
        self.assertEqual([job.scope["matrix"] for job in run.scans], [{"head": head, "numbers": "8"}])
        self.assertEqual(self.states(), [(head, "success")])

    def test_a_run_whose_head_has_no_open_pull_request_scans_nothing(self):
        _, (head, closed) = self.clean_heads(2)
        self.serve({"number": 7, "head": head})
        run = self.run_workflow("workflow_run", closed)
        self.assertEqual(run.find.outputs(), {"count": "0", "matrix": "[]"})
        self.assertEqual(run.scans, [])       # a matrix with no entry fails, so the job does not start
        self.assertEqual(self.states(), [])

    def test_only_a_pull_request_run_of_held_content_in_the_public_repository_starts_a_scan(self):
        _, (head,) = self.clean_heads(1)
        self.serve({"number": 7, "head": head})

        def runs(name="find", event="workflow_run", inputs=None, **github):
            return Job(self, PRIVATE, name, self.github(event, head, **github), self.origin, gh=self.gh, inputs=inputs,
                       needs={"find": {"result": "success", "outputs": {"count": "1"}}}).runs()

        self.assertTrue(runs())
        self.assertTrue(runs(conclusion="failure"))     # the demonstration of held-content.yml ends red
        self.assertFalse(runs(event="push"))
        self.assertFalse(runs(event="pull_request_target"))
        self.assertFalse(runs(path=".github/workflows/another.yml"))
        self.assertTrue(runs("scan"))
        self.assertTrue(runs("demonstrate", "workflow_dispatch", {"demonstrate_a_refusal": True}))
        # in any other repository, the internal one among them, no job of any event runs
        for event in ("workflow_run", "schedule", "workflow_dispatch"):
            for name in ("find", "scan", "demonstrate"):
                for demonstrate in (False, True):
                    with self.subTest(event=event, job=name, demonstrate_a_refusal=demonstrate):
                        self.assertFalse(runs(name, event, {"demonstrate_a_refusal": demonstrate},
                                              repository="acme/proofs"))

    def test_the_hourly_run_scans_each_head_that_has_no_success_and_no_failure(self):
        origin, heads = self.clean_heads(3)
        # Pull request 4 changes a line that main changes too.  It has a merge conflict, so GitHub starts no
        # pull_request run for it, and no workflow_run follows.
        git(origin.src, "checkout", "-q", "-B", "topic-4", origin.base)
        heads.append(origin.commit("a clean change 4", {"docs/a.txt": "the first line\nthe line of the branch\n"}))
        git(origin.src, "checkout", "-q", "main")
        main = origin.commit("main changes the same line", {"docs/a.txt": "the first line\nthe line of main\n"})
        origin.ref("refs/heads/main", main)
        merged = subprocess.run(["git", "-C", origin.src, "merge-tree", "--write-tree", main, heads[3]],
                                capture_output=True)
        self.assertEqual(merged.returncode, 1, "pull request 4 has no merge conflict")
        self.serve(*({"number": n, "head": head} for n, head in enumerate(heads, 1)), statuses={
            # the newest status counts: this head has its answer, and the next one has not
            heads[0]: [status("success", "clean", "2026-11-03T00:00:00Z"),
                       status("error", "a GitHub read failed", "2026-11-02T00:00:00Z")],
            heads[1]: [status("error", "a GitHub read failed", "2026-11-04T00:00:00Z"),
                       status("success", "clean", "2026-11-01T00:00:00Z")],
            # a status of another account, and a status of another name, are no answer of this workflow
            heads[2]: [status("success", "clean", login="made-up-account"),
                       status("failure", "held", context="another-check")]})
        run = self.run_workflow("schedule")
        # first the heads with no status, the oldest pull request first, then the head with an `error`
        scanned = [heads[2], heads[3], heads[1]]
        self.assertEqual([job.scope["matrix"] for job in run.scans],
                         [{"head": head, "numbers": str(heads.index(head) + 1)} for head in scanned])
        self.assertEqual(self.states(), [(head, "success") for head in scanned])
        self.assertEqual(sorted(c["endpoint"] for c in run.find.calls if "/statuses" in c["endpoint"]),
                         sorted("repos/%s/commits/%s/statuses?per_page=100" % (PUBLIC, head) for head in heads))
        self.assertFalse([c for c in run.find.calls if "--jq" in c["argv"] or c["method"] != "GET"])

    def test_a_run_by_hand_on_main_without_the_input_does_what_the_hourly_run_does(self):
        _, heads = self.clean_heads(2)
        self.serve({"number": 1, "head": heads[0]}, {"number": 2, "head": heads[1]},
                   statuses={heads[0]: [status("failure", "held content")]})
        run = self.run_workflow("workflow_dispatch", inputs={"demonstrate_a_refusal": False})
        self.assertFalse(run.demonstrate.runs())
        self.assertEqual([job.scope["matrix"] for job in run.scans], [{"head": heads[1], "numbers": "2"}])
        self.assertEqual(self.states(), [(heads[1], "success")])

    def test_a_run_by_hand_on_another_ref_runs_no_job(self):
        _, (head,) = self.clean_heads(1)
        self.serve({"number": 1, "head": head})
        for demonstrate in (False, True):
            with self.subTest(demonstrate_a_refusal=demonstrate):
                run = self.run_workflow("workflow_dispatch", ref="refs/heads/a-branch",
                                        inputs={"demonstrate_a_refusal": demonstrate})
                self.assertFalse(run.find.runs())
                self.assertFalse(run.demonstrate.runs())
                self.assertEqual(run.scans, [])
                # the condition of scan says no by itself, whatever find gave
                scan = Job(self, PRIVATE, "scan", run.find.scope["github"], self.origin, gh=self.gh,
                           needs={"find": {"result": "success", "outputs": {"count": "1"}}})
                self.assertFalse(scan.runs())
        self.assertEqual(gh_calls(self.gh), [])
        self.assertEqual(self.states(), [])

    def test_at_most_256_heads_go_to_one_run_and_those_with_no_status_go_first(self):
        self.repository()

        def head(n):
            return "%040x" % n      # find reads no commit, so a made-up id serves

        pulls = [{"number": n, "head": head(n)} for n in range(1, 7)] + [{"number": 9, "head": head(2)}]
        install_gh(self.gh, {"git": self.origin.bare, "pulls": pulls, "statuses": {
            head(1): [status("error", at="2026-11-03T00:00:00Z")],
            head(3): [status("error", at="2026-11-01T00:00:00Z")],
            head(5): [status("success")],
            head(6): [status("pending", at="2026-11-02T00:00:00Z")]}})
        # no status: 2 (with 9) and 4.  Then by the time of the newest status: 3, 6, 1.  5 has its answer.
        order = [head(n) for n in (2, 4, 3, 6, 1)]

        def find(most=None):
            job = Job(self, PRIVATE, "find", self.github("schedule"), self.origin, gh=self.gh)
            text = job.job["steps"][0]["run"]
            self.assertIn("MOST = 256\n", text)
            if most:
                job.edits[HEADS] = text.replace("MOST = 256\n", "MOST = %d\n" % most)
            return job.run()

        whole = find()
        self.assertEqual(whole.outputs()["count"], "5", whole.output())
        self.assertEqual(json.loads(whole.outputs()["matrix"]),
                         [{"head": h, "numbers": "2 9" if h == head(2) else str(int(h, 16))} for h in order])
        cut = find(most=3)
        self.assertEqual(cut.outputs()["count"], "3", cut.output())
        self.assertEqual([entry["head"] for entry in json.loads(cut.outputs()["matrix"])], order[:3])
        self.assertIn("2 head(s) wait for the next run.", cut.output())


@unittest.skipIf(PRIVATE_ABSENT, PRIVATE_ABSENT)
class PrivateScan(Private):
    """What a scan of held-content-private.yml reads through the API, how it numbers it, and what it posts."""

    def change(self, marks):
        """A scratch origin, and a head of two commits over its first commit that holds one of marks in each of five
        places: [0] in the message of its second commit, [1] in the name of a new path, [2] in the name of a path it
        deletes, [3] in a line it adds to a file, and [4] in a file that holds a zero byte.  Returns (origin, the
        first of the two commits, the head)."""
        origin = self.repository({"docs/a.txt": "the first line\n", "old/%s.txt" % marks[2]: "to delete\n"})
        first = origin.commit("a first, clean commit", {"docs/b.txt": "clean\n"})
        os.remove(os.path.join(origin.src, "old", "%s.txt" % marks[2]))
        head = origin.commit("a second commit\n\nIt quotes %s here.\n" % marks[0], {
            "notes/%s.txt" % marks[1]: "clean\n",
            "docs/a.txt": "the first line\n%s\n" % marks[3],
            "bin/blob.bin": b"\0a leading run\0\xff" + marks[4].encode() + b"\0\xfe"})
        return origin, first, head

    def scan_of(self, head, **options):
        """The one scan job of a workflow_run run for head, and the run."""
        run = self.run_workflow("workflow_run", head, **options)
        self.assertEqual(len(run.scans), 1, run.output())
        return run.scans[0], run

    def test_a_sample_of_each_pattern_gets_failure_and_each_hit_is_named_by_number_alone(self):
        m = [mark(k) for k in range(5)]
        origin, first, head = self.change(m)
        self.serve({"number": 7, "head": head})
        scan, run = self.scan_of(head)
        step = scan.step(API_SCAN)
        self.assertEqual(step["status"], 0, run.output())      # it wrote its verdict, which the next step posts
        _, paths = origin.places(head)
        zero = ("path %d line 2" % (paths.index("bin/blob.bin") + 1), row(4))     # its second printable run
        expected = self.expected(head, origin.base, dict(enumerate(m))) | {zero}
        self.assertEqual(sorted(expected), sorted([
            ("commit 2", row(0)),
            ("path %d" % (paths.index("notes/%s.txt" % m[1]) + 1), row(1)),
            ("path %d" % (paths.index("old/%s.txt" % m[2]) + 1), row(2)),
            ("path %d line 2" % (paths.index("docs/a.txt") + 1), row(3)), zero]))
        found = hits(step["stdout"])
        self.assertEqual(sorted(found), sorted(expected))
        self.assertPosted([(head, "failure", "held content: pull request 7: "
                            + ", ".join(dict.fromkeys(place for place, _ in found)))])
        self.assertEqual(scan.step(POST)["outcome"], "failure")     # the job ends red
        # the log names the pull request and the head, and no sample, no path, no row's name and no other commit
        out = run.output()
        for withheld in m + ["notes/", "old/", "docs/a.txt", "blob.bin", "made-up-", "qzv", first[:7],
                             origin.base[:7]]:
            self.assertNotIn(withheld, out)
        self.assertIn("pull request 7 at head %s" % head, out)
        # every call is `api` with no --jq, never a recursive read, and each blob is read once, raw
        self.assertFalse([c for c in scan.calls if c["argv"][0] != "api" or "--jq" in c["argv"]
                          or "recursive" in c["endpoint"]])
        blobs = [c for c in scan.calls if "/git/blobs/" in c["endpoint"]]
        self.assertEqual({tuple(c["headers"]) for c in blobs}, {("Accept: application/vnd.github.raw",)})
        self.assertEqual(len({c["endpoint"] for c in blobs}), len(blobs))
        # Each read of the scan step is a GET by HTTP with the token of the run, and asks for JSON but for a blob.  The
        # scan step runs no gh.  The post step reads the pull request and posts the status through gh.
        reads = scan.step(API_SCAN)["calls"]
        self.assertTrue(blobs and all(c in reads for c in blobs), run.output())
        self.assertEqual([c for c in reads if c["http"] != {"bearer": True} or c["method"] != "GET"], [])
        self.assertEqual({tuple(c["headers"]) for c in reads if c not in blobs},
                         {("Accept: application/vnd.github+json",)})
        self.assertEqual([(c["method"], c["http"]) for c in scan.step(POST)["calls"]], [("GET", None), ("POST", None)])
        self.assertEqual([c["method"] for c in scan.calls if c["method"] != "GET"], ["POST"])

    def test_the_same_change_with_no_sample_gets_success(self):
        origin, _first, head = self.change(["clean-%d" % k for k in range(5)])
        self.serve({"number": 7, "head": head})
        scan, run = self.scan_of(head)
        self.assertEqual([outcome for _, outcome in scan.outcomes()], ["success"] * 3, run.output())
        self.assertEqual(hits(scan.step(API_SCAN)["stdout"]), [])
        commits, paths = origin.places(head)
        self.assertPosted([(head, "success", "no pattern matched: pull request 7: %d commit(s), %d path(s)"
                            % (len(commits), len(paths)))])

    def test_each_number_is_the_place_that_git_gives_the_path(self):
        m = {k: mark(k) for k in range(12)}
        origin = self.repository({
            "src/%s-old.txt" % m[0]: "to rename\n",
            "tree/%s" % m[2]: "a file that becomes a folder\n", "tree/%s.txt" % m[2]: "its neighbour\n",
            "bin/%s.sh" % m[5]: "#!/bin/sh\n",
            "gone/%s/%s.txt" % (m[9], m[10]): "one\n", "gone/%s/sub/%s.txt" % (m[9], m[11]): "two\n"})
        src = origin.src

        def path(rel):
            return os.path.join(src, rel)

        def a_rename():
            os.rename(path("src/%s-old.txt" % m[0]), path("src/%s-new.txt" % m[1]))

        def a_file_that_becomes_a_folder():
            os.remove(path("tree/%s" % m[2]))
            origin.write("tree/%s/%s.txt" % (m[2], m[3]), "inside\n")
            origin.write("tree/%s/%s.txt" % (m[2], m[4]), "inside\n")
            origin.write("tree/%s.txt" % m[2], "its neighbour, changed\n")

        def a_change_of_mode_alone():
            os.chmod(path("bin/%s.sh" % m[5]), 0o755)
            git(src, "update-index", "--chmod=+x", "bin/%s.sh" % m[5])

        def a_symbolic_link():
            os.makedirs(path("links"))
            os.symlink("../docs/%s" % m[7], path("links/%s" % m[6]))

        def a_deleted_folder():
            shutil.rmtree(path("gone/%s" % m[9]))

        def a_folder_that_becomes_a_file():
            shutil.rmtree(path("gone/%s" % m[9]))
            origin.write("gone/%s" % m[9], "a file where a folder was\n")

        def a_submodule():
            origin.commit("a submodule", gitlinks={"vendor/%s" % m[8]: origin.base})

        kinds = (a_rename, a_file_that_becomes_a_folder, a_change_of_mode_alone, a_symbolic_link, a_deleted_folder,
                 a_submodule, a_folder_that_becomes_a_file)
        heads = {}
        for change in kinds:
            git(src, "checkout", "-q", "-B", "topic", origin.base)
            git(src, "clean", "-q", "-fd")
            change()
            heads[change.__name__] = origin.commit("a change: %s" % change.__name__)
        # and all of them in one head, one commit each, but for the last, which takes the folder of the fifth
        git(src, "checkout", "-q", "-B", "topic", origin.base)
        git(src, "clean", "-q", "-fd")
        for change in kinds[:-1]:
            change()
            heads["all of them"] = origin.commit("a change: %s" % change.__name__)
        self.serve(*({"number": n, "head": head} for n, head in enumerate(heads.values(), 1)))
        run = self.run_workflow("schedule")
        scans = {job.scope["matrix"]["head"]: job for job in run.scans}
        places = {}
        for kind, head in heads.items():
            with self.subTest(kind=kind):
                expected = self.expected(head, origin.base, m)
                self.assertTrue(expected)
                self.assertEqual(sorted(hits(scans[head].step(API_SCAN)["stdout"])), sorted(expected), run.output())
                places[kind] = (origin.places(head)[1], expected,
                                [c for c in scans[head].calls if "/git/blobs/" in c["endpoint"]])
        self.assertEqual(sorted(self.states()), sorted((head, "failure") for head in heads.values()))
        # what git's order is, and so what the numbers above are
        paths, expected, _ = places["a_rename"]
        self.assertEqual(paths, ["src/%s-old.txt" % m[0], "src/%s-new.txt" % m[1]])
        self.assertEqual(expected, {("path 1", row(0)), ("path 2", row(1))})
        paths, expected, _ = places["a_file_that_becomes_a_folder"]     # its deletion, and then the additions
        self.assertEqual(paths, ["tree/%s" % m[2], "tree/%s.txt" % m[2], "tree/%s/%s.txt" % (m[2], m[3]),
                                 "tree/%s/%s.txt" % (m[2], m[4])])
        self.assertEqual(expected, {("path 1", row(2)), ("path 2", row(2)), ("path 3", row(2)), ("path 3", row(3)),
                                    ("path 4", row(2)), ("path 4", row(4))})
        paths, expected, blobs = places["a_change_of_mode_alone"]       # one record, and no blob read
        self.assertEqual((paths, expected, blobs), (["bin/%s.sh" % m[5]], {("path 1", row(5))}, []))
        _, expected, _ = places["a_symbolic_link"]                      # its text is its target
        self.assertEqual(expected, {("path 1", row(6)), ("path 1 line 1", row(7))})
        _, expected, blobs = places["a_submodule"]                      # a path with no text
        self.assertEqual((expected, blobs), ({("path 1", row(8))}, []))
        _, expected, blobs = places["a_deleted_folder"]                 # each deleted path is a record
        self.assertEqual((expected, blobs), ({("path 1", row(9)), ("path 1", row(10)), ("path 2", row(9)),
                                              ("path 2", row(11))}, []))
        paths, _, _ = places["a_folder_that_becomes_a_file"]            # its addition, and then the deletions
        self.assertEqual(paths, ["gone/%s" % m[9], "gone/%s/%s.txt" % (m[9], m[10]),
                                 "gone/%s/sub/%s.txt" % (m[9], m[11])])

    def merged(self, times, name="repository", marked=True):
        """A scratch origin where the branch topic (b1, b2) merges main (c1, c2) and then adds b3.  The six commits
        are made in the order b1, c1, b2, c2, the merge, b3, each at the committer time of `times` (seconds from one
        instant) and, with marked, with a sample of its own row in its message.  main is at c2, and the branch stable
        is left at the first commit.  Returns (origin, the head, c2, the samples by row)."""
        origin = self.repository(name=name)
        src, m = origin.src, {k: mark(k) if marked else "clean text %d" % k for k in range(6)}

        def commit(k, rel=None):
            stamp = "%d +0000" % (1700000000 + times[k])
            with mock.patch.dict(os.environ, {"GIT_AUTHOR_DATE": stamp, "GIT_COMMITTER_DATE": stamp}):
                if rel:
                    return origin.commit("a commit that holds %s" % m[k], {rel: "clean\n"})
                git(src, "merge", "-q", "--no-ff", "-m", "a merge of main that holds %s" % m[k], "main")
                return git(src, "rev-parse", "HEAD")

        git(src, "checkout", "-q", "-b", "topic")
        commit(0, "topic/1.txt")
        git(src, "checkout", "-q", "main")
        commit(1, "main/1.txt")
        git(src, "checkout", "-q", "topic")
        commit(2, "topic/2.txt")
        git(src, "checkout", "-q", "main")
        main = commit(3, "main/2.txt")
        git(src, "checkout", "-q", "topic")
        commit(4)
        head = commit(5, "topic/3.txt")
        git(src, "checkout", "-q", "main")
        origin.ref("refs/heads/main", main)
        origin.ref("refs/heads/stable", origin.base)
        return origin, head, main, m

    def test_a_merge_of_main_is_numbered_as_git_log_numbers_it(self):
        for name, times in (("equal", [0] * 6), ("distinct", [100, 200, 300, 400, 500, 600]),
                            ("older-than-its-parent", [600, 500, 400, 300, 200, 100])):
            with self.subTest(committer_times=name):
                origin, head, _main, m = self.merged(times, "repository-" + name)
                # Into stable, which main left at the first commit: the two commits of main are commits of the
                # pull request, on a line of their own beside the two of the branch.
                gh = self.serve({"number": 21, "head": head, "base": "stable"}, gh=os.path.join(self.root, name))
                scan, run = self.scan_of(head, gh=gh)
                commits, _ = origin.places(head)
                expected = self.expected(head, origin.base, m)
                self.assertEqual(sorted(place for place, _ in expected), ["commit %d" % k for k in range(1, 7)])
                self.assertEqual(sorted(hits(scan.step(API_SCAN)["stdout"])), sorted(expected), run.output())
                if name == "older-than-its-parent":
                    # the answer listed them by committer date, which is not git's order here
                    dated = sorted(commits, key=lambda c: (git(origin.src, "log", "-1", "--format=%ct", c), c))
                    self.assertNotEqual(dated, commits)

    def test_a_head_that_merged_main_after_a_commit_with_a_sample_gets_failure_for_that_message(self):
        origin, head, main, m = self.merged([100, 200, 300, 400, 500, 600])
        self.serve({"number": 7, "head": head})     # into main, which is at the commit that the head merged
        scan, run = self.scan_of(head)
        # the commits of main are not the pull request's: git lists b1, b2, the merge and b3
        self.assertEqual(len(origin.places(head, main)[0]), 4)
        found = hits(scan.step(API_SCAN)["stdout"])
        self.assertEqual(sorted(found), sorted(self.expected(head, main, m)), run.output())
        self.assertIn(("commit 1", row(0)), found)
        self.assertPosted([(head, "failure", "held content: pull request 7: commit 1, commit 2, commit 3, commit 4")])

    def test_the_same_head_with_no_sample_gets_success(self):
        origin, head, main, _ = self.merged([100, 200, 300, 400, 500, 600], marked=False)
        self.serve({"number": 7, "head": head})
        scan, run = self.scan_of(head)
        commits, paths = origin.places(head, main)
        self.assertEqual((len(commits), len(paths)), (4, 3))
        self.assertEqual(hits(scan.step(API_SCAN)["stdout"]), [], run.output())
        self.assertPosted([(head, "success", "no pattern matched: pull request 7: 4 commit(s), 3 path(s)")])

    def test_a_recursive_read_that_github_cuts_short_does_not_stop_the_scan(self):
        origin, (head,) = self.clean_heads(1)
        self.serve({"number": 7, "head": head})
        tree = git(origin.src, "rev-parse", head + "^{tree}")
        whole = subprocess.run([os.path.join(self.gh, "gh"), "api",
                                "repos/%s/git/trees/%s?recursive=1" % (PUBLIC, tree)], capture_output=True, text=True)
        self.assertIs(json.loads(whole.stdout)["truncated"], True, whole.stderr)
        scan, run = self.scan_of(head)
        trees = [c["endpoint"] for c in scan.calls if "/git/trees/" in c["endpoint"]]
        self.assertTrue(trees, run.output())
        self.assertFalse([endpoint for endpoint in trees if "?" in endpoint])   # one folder at a time
        self.assertEqual(self.states(), [(head, "success")])

    def test_two_pull_requests_on_one_head_get_one_status(self):
        m = mark(0)
        origin = self.repository()
        held = origin.commit("a change", {"docs/%s.txt" % m: "clean\n"})
        head = origin.commit("a clean change", {"docs/b.txt": "clean\n"})
        origin.ref("refs/heads/stable", held)
        # Into main, the head adds the path with the sample.  Into stable, which has that commit, it adds nothing
        # held.  One job scans the two, and the one status is `failure`.
        self.serve({"number": 7, "head": head}, {"number": 8, "head": head, "base": "stable"})
        run = self.run_workflow("workflow_run", head)
        self.assertEqual([job.scope["matrix"] for job in run.scans], [{"head": head, "numbers": "7 8"}])
        stdout = run.scans[0].step(API_SCAN)["stdout"]
        ((place, private),) = self.expected(head, origin.base, {0: m})
        self.assertEqual(hits(stdout), [(place, private)])
        self.assertIn("of pull request 8 at head %s matched no detector" % head, stdout)
        self.assertPosted([(head, "failure", "held content: pull request 7: %s" % place)])

    def test_the_label_prove_it_can_fail_plants_a_sample_of_every_pattern_and_gets_failure_never_success(self):
        _, (head,) = self.clean_heads(1)
        self.serve({"number": 7, "head": head, "labels": ["prove-it-can-fail"]})
        scan, run = self.scan_of(head)
        with open(DETECTORS, encoding="utf-8") as f:
            public = load_scanner().parse_table(f.read(), "detectors.tsv")
        # sample K is of the K-th pattern: those of detectors.tsv, and then the rows of the secret
        every = ["detector %s (%s)" % (d.name, d.category) for d in public] + [row(k) for k in range(len(ROWS))]
        found = hits(scan.step(API_SCAN)["stdout"])
        self.assertEqual([("planted sample %d" % k, label) for k, label in enumerate(every, 1)
                          if ("planted sample %d" % k, label) not in found], [], run.output())
        self.assertEqual({place.rsplit(" ", 1)[0] for place, _ in found}, {"planted sample"})
        (posted,) = self.posted()
        self.assertEqual((posted["sha"], posted["state"]), (head, "failure"))
        # the description lists the places by number, cut to the 140 characters that GitHub takes
        self.assertTrue(posted["description"].startswith(
            "held content: pull request 7: planted sample 1, planted sample 2, "), posted["description"])
        self.assertEqual((len(posted["description"]), posted["description"][-3:]), (140, "..."))
        self.assertEqual(scan.step(POST)["outcome"], "failure")
        self.assertNotIn("qzv", run.output())       # no sample is in the log

    def test_a_head_that_moved_gets_no_status(self):
        _, (head, later) = self.clean_heads(2)
        for when, after in (("before the post", 1), ("before the scan", 0)):
            with self.subTest(moved=when):
                gh = self.serve({"number": 7, "head": head}, gh=os.path.join(self.root, "gh-%d" % after),
                                moved={"7": {"after": after, "head": later}})
                scan, run = self.scan_of(head, gh=gh)
                self.assertEqual(self.posted(gh), [], run.output())
                self.assertEqual([c for c in scan.calls if c["method"] != "GET"], [])
                self.assertIn("Nothing is posted.", scan.step(POST)["stdout"])
                # a head that moved before the scan is not read at all
                self.assertEqual(bool([c for c in scan.calls if "/compare/" in c["endpoint"]]), after == 1)
                self.assertEqual([outcome for _, outcome in scan.outcomes()], ["success"] * 3)

    def test_a_head_of_more_than_100_commits_is_read_page_by_page(self):
        origin = self.repository()
        tree, head = git(origin.src, "rev-parse", origin.base + "^{tree}"), origin.base
        samples = {1: mark(0), 105: mark(1)}
        for n in range(1, 106):
            head = git(origin.src, "commit-tree", tree, "-p", head, "-m",
                       "commit %d: %s" % (n, samples.get(n, "clean")))
        self.serve({"number": 7, "head": head})
        scan, run = self.scan_of(head)
        self.assertEqual(sorted(hits(scan.step(API_SCAN)["stdout"])),
                         [("commit 1", row(0)), ("commit 105", row(1))], run.output())
        # the merge base and the count from the branch, and then each page between two fixed commits
        self.assertEqual([c["endpoint"] for c in scan.calls if "/compare/" in c["endpoint"]],
                         ["repos/%s/compare/main...%s?per_page=100" % (PUBLIC, head)]
                         + ["repos/%s/compare/%s...%s?per_page=100&page=%d" % (PUBLIC, origin.base, head, page)
                            for page in (1, 2)])

    def test_a_text_file_that_holds_a_terminal_escape_sequence_is_read_and_judged(self):
        # A log with colours is text that holds ESC bytes.  held-content.yml reads it with git and judges it, and the
        # scan of the private workflow must judge it the same way.
        m = mark(0)
        origin, clean, held = self.two_heads(
            "coloured-log", ("a coloured log", {"logs/run.log": "\x1b[32mok\x1b[0m the build passed\n"}),
            ("a coloured log with a sample", {"logs/run.log": "\x1b[31m %s \x1b[0m\n" % m}))
        self.verdicts(origin, clean, held, m, "gh-coloured-log")

    def test_one_changed_line_of_a_large_file_is_judged_as_git_judges_it(self):
        # held-content.yml counts toward MAX_BYTES the text that a change adds (records_of), so it judges a change of
        # one line in a file of 34 MiB.  The API mode stops before its first blob read when the blobs it reads, the
        # old and the new together, are over MAX_BYTES, so it posts `error` on that change at every run.  Public #6 is
        # such a pull request (measured 2026-11-18): its old and new blobs are 448.8 MiB, the largest is 4.1 MiB, and
        # the text of git's records is 62.2 MiB, under MAX_BYTES.
        m = mark(0)
        filler = "".join("filler line %07d %s\n" % (n, "x" * 1000) for n in range(34 * 1024))
        self.assertGreater(2 * len(filler), load_scanner().MAX_BYTES)
        origin = self.repository({"data/big.txt": filler})
        git(origin.src, "checkout", "-q", "-B", "topic", origin.base)
        head = origin.commit("one line more", {"data/big.txt": filler + "a sample %s here\n" % m})
        git(origin.src, "checkout", "-q", "main")
        self.serve({"number": 7, "head": head})
        scan, run = self.scan_of(head)
        self.assertEqual(sorted(hits(scan.step(API_SCAN)["stdout"])),
                         sorted(self.expected(head, origin.base, {0: m})), run.output())
        self.assertEqual(self.states(), [(head, "failure")], run.output())


@unittest.skipIf(PRIVATE_ABSENT, PRIVATE_ABSENT)
class PrivateErrors(Private):
    """Each way a scan of held-content-private.yml does not finish gets one `error` status with a fixed description.
    A second run with the same cause posts nothing more on that commit until a `success` or a `failure` of this
    workflow follows that `error`."""

    # the descriptions of a `success` and of a `failure` of pull request 7 at self.head, for statuses of the head
    # before a run
    SUCCESS = "no pattern matched: pull request 7: 1 commit(s), 2 path(s)"
    FAILURE = "held content: pull request 7: path 1"

    def setUp(self):
        super().setUp()
        origin = self.repository({"docs/a.txt": "the first line\n"})
        self.head = origin.commit("a clean change", {"docs/a.txt": "the first line\na second line\n",
                                                     "docs/b.txt": "clean\n"})
        self.pull = {"number": 7, "head": self.head}

    def test_each_cause_gets_error_once(self):
        scanner = load_scanner()
        new = git(self.origin.src, "rev-parse", self.head + ":docs/b.txt")
        limit = {"endpoint": "/git/trees/", "status": 403, "message": "API rate limit exceeded for installation."}
        second = dict(limit, status=429, message="You have exceeded a secondary rate limit.")
        fails = "echo 'this step fails before the scan'; exit 1"
        # (the cause, its description, the state of the stand-in gh, the options of the run, whether the scan
        # stopped before it read a blob)
        causes = (
            ("a missing secret", scanner.SECRET, {}, {"secret": ""}, True),
            ("a changed secret", scanner.SECRET, {}, {"secret": PRIVATE_TABLE.replace("{12}", "{13}", 1)}, True),
            ("a folder listing cut short", scanner.LISTING, {"cut_listings": True}, {}, True),
            ("a rate-limit answer", scanner.FLOOR, {"refuse": [limit]}, {}, True),
            ("a secondary rate-limit answer", scanner.FLOOR, {"refuse": [second]}, {}, True),
            ("a remaining count under the floor", scanner.FLOOR, {"rate": {"limit": 15000, "remaining": 2999}}, {},
             True),
            # three blob reads: the old and the new text of one path, and the text of a new path
            ("a remaining count that cannot pay for the blob reads", scanner.FLOOR,
             {"rate": {"limit": 15000, "remaining": 3002}}, {}, True),
            ("a file over 100 MB", scanner.TOO_LARGE, {"sizes": {new: 100 * 1024 * 1024 + 1}}, {}, True),
            ("a comparison with another count than its commits", scanner.INCOMPLETE, {"miscount": 1}, {}, True),
            ("a read that fails", scanner.READ,
             {"refuse": [{"endpoint": "/git/blobs/", "status": 502, "message": "Server Error"}]}, {}, False),
            ("a scan past its time", scanner.TIME, {}, {"variables": {"HELD_CONTENT_TIME_LIMIT": "0"}}, True),
            ("a failed step", "a step failed before the scan finished", {}, {"edits": {API_SCAN: fails}}, True),
        )
        for at, (cause, description, state, options, no_blob) in enumerate(causes):
            with self.subTest(cause=cause):
                # a fixed text: no count, no time and no run in it but the two limits it names
                self.assertNotRegex(description.replace("100 MB", "").replace("64 MiB", ""), r"\d")
                gh = self.serve(self.pull, gh=os.path.join(self.root, "gh-%d" % at), **state)
                for again in (False, True):
                    run = self.run_workflow("workflow_run", self.head, gh=gh, **options)
                    (scan,) = run.scans
                    self.assertPosted([(self.head, "error", description)], gh=gh)
                    self.assertEqual(scan.step(POST)["outcome"], "failure", run.output())   # red each time
                    self.assertEqual("Nothing is posted." in scan.step(POST)["stdout"], again, run.output())
                    self.assertEqual(not [c for c in scan.calls if "/git/blobs/" in c["endpoint"]], no_blob)
                    # the scan step wrote its verdict and passed, but where the step itself is what fails
                    self.assertEqual(scan.step(API_SCAN)["status"], 1 if cause == "a failed step" else 0)

    def test_more_text_than_max_bytes_gets_error_once_after_the_blob_is_read(self):
        # MAX_BYTES counts the text that a change introduces (records_of), as in held-content.yml, and not the size of
        # its blobs.  So the scan reads the blob of a new file of a little more than 64 MiB, and then stops on its text.
        scanner = load_scanner()
        text = "".join("filler line %07d %s\n" % (n, "x" * 1000) for n in range(66 * 1024))
        self.assertGreater(len(text) - text.count("\n"), scanner.MAX_BYTES)     # the text of its lines alone
        self.assertLess(len(text), scanner.MAX_BLOB)
        git(self.origin.src, "checkout", "-q", "-B", "large", self.origin.base)
        head = self.origin.commit("a large new file", {"data/big.txt": text})
        git(self.origin.src, "checkout", "-q", "main")
        blob = git(self.origin.src, "rev-parse", head + ":data/big.txt")
        self.serve({"number": 7, "head": head})
        for again in (False, True):
            run = self.run_workflow("workflow_run", head)
            (scan,) = run.scans
            self.assertPosted([(head, "error", scanner.TOO_LARGE)])
            self.assertEqual(scan.step(POST)["outcome"], "failure", run.output())   # red each time
            self.assertEqual("Nothing is posted." in scan.step(POST)["stdout"], again, run.output())
            self.assertIn("this change introduces more than %d bytes of text" % scanner.MAX_BYTES, run.output())
            self.assertEqual([c["endpoint"] for c in scan.calls if "/git/blobs/" in c["endpoint"]],
                             ["repos/%s/git/blobs/%s" % (PUBLIC, blob)])
            self.assertEqual(scan.step(API_SCAN)["status"], 0, run.output())

    def test_a_read_that_hangs_gets_error_when_the_time_of_the_scan_is_out(self):
        # The scan stops a read when the time of the scan is out.  A read that hangs would otherwise hold the job to its
        # 60 minutes, and the post step would then post nothing.
        scanner, hang = load_scanner(), 300
        self.serve(self.pull, hang=[{"endpoint": "/git/blobs/", "seconds": hang}])
        started = time.monotonic()
        run = self.run_workflow("workflow_run", self.head, variables={"HELD_CONTENT_TIME_LIMIT": "10"})
        took = time.monotonic() - started
        (scan,) = run.scans
        self.assertPosted([(self.head, "error", scanner.TIME)])
        self.assertEqual(scan.step(API_SCAN)["status"], 0, run.output())     # it wrote its verdict
        self.assertEqual(scan.step(POST)["outcome"], "failure", run.output())
        # the scan stopped in its first blob read, which hung, and long before the hang would have ended
        self.assertEqual([c.get("hung") for c in scan.calls if "/git/blobs/" in c["endpoint"]], [hang], run.output())
        self.assertLess(took, hang / 2, run.output())

    def test_a_redirect_gets_error_and_the_token_goes_to_no_other_host(self):
        # urllib's own redirect handler follows a 302 to any host, with the headers of the request.  The scan follows
        # no redirect: the read of the pull request gets `error`, and the other host gets no request.
        elsewhere = []
        other = http_server(self, Recorder, got=elsewhere)
        endpoint = "repos/%s/pulls/7" % PUBLIC
        self.serve(self.pull, redirect=[{"endpoint": "^%s$" % re.escape(endpoint),
                                         "location": "%s/%s" % (other, endpoint)}])
        run = self.run_workflow("workflow_run", self.head)
        (scan,) = run.scans
        self.assertPosted([(self.head, "error", load_scanner().READ)])
        step = scan.step(API_SCAN)
        self.assertEqual(step["status"], 0, run.output())                   # it wrote its verdict
        self.assertIn("a read of pull request 7 failed (HTTP 302)", step["stderr"])
        self.assertEqual([c["endpoint"] for c in step["calls"]], ["rate_limit"], run.output())
        self.assertEqual(elsewhere, [])

    def test_another_error_is_posted_and_the_hourly_run_scans_the_head_again(self):
        scanner = load_scanner()
        # an `error` with this description that another account posted is not this workflow's
        mine = {self.head: [status("error", scanner.SECRET, login="made-up-account")]}
        self.serve(self.pull, statuses=mine)
        self.run_workflow("workflow_run", self.head, secret="")
        self.serve(self.pull, statuses=mine, cut_listings=True)
        self.run_workflow("workflow_run", self.head)
        self.serve(self.pull, statuses=mine)
        run = self.run_workflow("schedule")
        self.assertEqual([job.scope["matrix"]["head"] for job in run.scans], [self.head])
        self.assertEqual([(s["state"], s["description"]) for s in self.posted()],
                         [("error", scanner.SECRET), ("error", scanner.LISTING),
                          ("success", "no pattern matched: pull request 7: 1 commit(s), 2 path(s)")])
        # the head has its answer now: the next hourly run leaves it alone
        run = self.run_workflow("schedule")
        self.assertEqual((run.find.outputs()["count"], run.scans), ("0", []))
        self.assertEqual(len(self.posted()), 3)

    def test_each_error_is_posted_once_after_the_newest_success_or_on_a_commit_with_no_success_and_no_failure(self):
        scanner = load_scanner()
        # each cause: (its description, the state of the stand-in gh, the options of the run)
        a = (scanner.SECRET, {}, {"secret": ""})
        b = (scanner.LISTING, {"cut_listings": True}, {})
        c = (scanner.INCOMPLETE, {"miscount": 1}, {})
        # (the case, the statuses of the head before the runs, the runs: each a cause and whether the run posts it)
        cases = (
            # A, B, A, B, then C: the third and the fourth run post nothing, though the other error is the newest
            # status of the head each time, and A is the oldest.  C, an error that the head does not have yet, is
            # posted.
            ("no earlier status", [], ((a, True), (b, True), (a, False), (b, False), (c, True))),
            # A, `success`, B, then runs that give A, B and A.  The first posts A: the A before the `success` does
            # not count.  The second and the third post nothing: B and then A are on the head after the `success`.
            ("earlier A, success, B", [status("error", scanner.LISTING, "2026-11-03T00:00:00Z"),
                                       status("success", self.SUCCESS, "2026-11-02T00:00:00Z"),
                                       status("error", scanner.SECRET, "2026-11-01T00:00:00Z")],
             ((a, True), (b, False), (a, False))))
        for at, (case, earlier, runs) in enumerate(cases):
            with self.subTest(case=case):
                gh, expected = os.path.join(self.root, "gh-%d" % at), []
                for (description, state, options), new in runs:
                    self.serve(self.pull, gh=gh, statuses={self.head: earlier}, **state)
                    run = self.run_workflow("workflow_run", self.head, gh=gh, **options)
                    (scan,) = run.scans
                    self.assertEqual(scan.step(POST)["outcome"], "failure", run.output())   # red each time
                    self.assertEqual("Nothing is posted." in scan.step(POST)["stdout"], not new, run.output())
                    expected += [(self.head, "error", description)] if new else []
                    self.assertPosted(expected, gh=gh)

    def test_a_second_pull_request_on_a_head_with_a_success_gets_the_error_that_the_head_had_before(self):
        # The head has error A, then `success` for pull request 7.  Then pull request 8 opens on the head, into another
        # branch: the `success` is the answer for 7 alone.  A scan of 7 and 8 that gives A posts A.  The next hourly
        # run then scans the head again, because the newest status of the head is that `error`.
        scanner = load_scanner()
        self.origin.ref("refs/heads/stable", self.origin.base)
        self.serve(self.pull, {"number": 8, "head": self.head, "base": "stable"}, statuses={self.head: [
            status("success", self.SUCCESS, "2026-11-02T00:00:00Z"),
            status("error", scanner.SECRET, "2026-11-01T00:00:00Z")]})
        both = [{"head": self.head, "numbers": "7 8"}]
        run = self.run_workflow("workflow_run", self.head, secret="")
        self.assertEqual([job.scope["matrix"] for job in run.scans], both)
        self.assertNotIn("Nothing is posted.", run.scans[0].step(POST)["stdout"], run.output())
        self.assertPosted([(self.head, "error", scanner.SECRET)])
        run = self.run_workflow("schedule")
        self.assertEqual([job.scope["matrix"] for job in run.scans], both)
        self.assertEqual(self.states(), [(self.head, "error"), (self.head, "success")])

    def test_after_and_newest_go_by_the_time_and_then_by_the_id_and_not_by_the_list(self):
        # In each case the head has error A, and a run gives A.  The stand-in lists the statuses in the order given.
        # That order is newest first, as GitHub lists them, in the first two cases alone.
        scanner = load_scanner()
        one = "2026-11-02T00:00:00Z"        # the time of two statuses: only their ids put them in order
        # (the case, the statuses of the head in the order of the list, whether the run posts A)
        cases = (
            # A, then a `success` or a `failure`: A is posted, so the newest status of the head is the answer of the
            # newest scan
            ("A, then a success", [status("success", self.SUCCESS, "2026-11-02T00:00:00Z"),
                                   status("error", scanner.SECRET, "2026-11-01T00:00:00Z")], True),
            ("A, then a failure", [status("failure", self.FAILURE, "2026-11-02T00:00:00Z"),
                                   status("error", scanner.SECRET, "2026-11-01T00:00:00Z")], True),
            # the first `success` or `failure` of the list is not the newest, and A is before the newest
            ("a list in no order", [status("error", scanner.SECRET, "2026-11-02T00:00:00Z", id=2),
                                    status("success", self.SUCCESS, "2026-11-01T00:00:00Z", id=1),
                                    status("failure", self.FAILURE, "2026-11-03T00:00:00Z", id=3)], True),
            ("one time, and the error after the success by its id",
             [status("success", self.SUCCESS, one, id=1), status("error", scanner.SECRET, one, id=2)], False),
            ("one time, and the success after the error by its id",
             [status("error", scanner.SECRET, one, id=1), status("success", self.SUCCESS, one, id=2)], True))
        for at, (case, earlier, new) in enumerate(cases):
            with self.subTest(case=case):
                gh = self.serve(self.pull, gh=os.path.join(self.root, "gh-%d" % at), statuses={self.head: earlier})
                run = self.run_workflow("workflow_run", self.head, secret="", gh=gh)
                (scan,) = run.scans
                self.assertEqual(scan.step(POST)["outcome"], "failure", run.output())
                self.assertEqual("Nothing is posted." in scan.step(POST)["stdout"], not new, run.output())
                self.assertPosted([(self.head, "error", scanner.SECRET)] if new else [], gh=gh)

    def test_an_error_of_another_name_or_of_another_account_does_not_count(self):
        # each has the state and the text of the error of this run, and one other field
        scanner = load_scanner()
        self.serve(self.pull, statuses={self.head: [status("error", scanner.SECRET, context="held-content"),
                                                    status("error", scanner.SECRET, login="made-up-account")]})
        run = self.run_workflow("workflow_run", self.head, secret="")
        (scan,) = run.scans
        self.assertEqual(scan.step(POST)["outcome"], "failure", run.output())
        self.assertNotIn("Nothing is posted.", scan.step(POST)["stdout"], run.output())
        self.assertPosted([(self.head, "error", scanner.SECRET)])

    def test_a_success_or_a_failure_of_another_name_or_of_another_account_does_not_count(self):
        # The head has error A of this workflow.  A `success` of another name and a `failure` of another account come
        # after it.  Neither is a verdict of this workflow, so a run that gives A posts nothing.
        scanner = load_scanner()
        self.serve(self.pull, statuses={self.head: [
            status("failure", self.FAILURE, "2026-11-03T00:00:00Z", login="made-up-account"),
            status("success", self.SUCCESS, "2026-11-02T00:00:00Z", context="held-content"),
            status("error", scanner.SECRET, "2026-11-01T00:00:00Z")]})
        run = self.run_workflow("workflow_run", self.head, secret="")
        (scan,) = run.scans
        self.assertEqual(scan.step(POST)["outcome"], "failure", run.output())
        self.assertIn("Nothing is posted.", scan.step(POST)["stdout"], run.output())
        self.assertPosted([])

    def test_an_earlier_error_on_a_later_page_of_the_statuses_counts(self):
        # one status on a page: the error of this run is on the second page, after a newer error
        scanner = load_scanner()
        self.serve(self.pull, page_size=1, statuses={self.head: [
            status("error", scanner.LISTING, "2026-11-02T00:00:00Z"),
            status("error", scanner.SECRET, "2026-11-01T00:00:00Z")]})
        run = self.run_workflow("workflow_run", self.head, secret="")
        (scan,) = run.scans
        self.assertEqual(scan.step(POST)["outcome"], "failure", run.output())
        self.assertIn("Nothing is posted.", scan.step(POST)["stdout"], run.output())
        self.assertPosted([])
        reads = [c["pages"] for c in scan.step(POST)["calls"] if c["endpoint"].endswith("/statuses?per_page=100")]
        self.assertEqual(reads, [2], run.output())

    def test_a_private_row_that_cannot_work_gets_error_and_is_named_by_its_number_alone(self):
        for at, (why, bad) in enumerate((
                ("it misses its own sample", "made-up-missing\tmade-up-kind\t-\t\\bqzvw[0-9]{20}\tqzvw{4:hex}"),
                ("it does not compile", "made-up-broken\tmade-up-kind\t-\tqzvw(\tqzvw{4:hex}"),
                ("it repeats a name", "made-up-g\tmade-up-kind\t-\t\\bqzvw[0-9a-f]{8}\tqzvw{8:hex}"))):
            with self.subTest(why=why):
                table = PRIVATE_TABLE + bad + "\n"
                origin = self.repository(table=table, name="repository-%d" % at)
                head = origin.commit("a clean change", {"docs/b.txt": "clean\n"})
                gh = self.serve({"number": 7, "head": head}, gh=os.path.join(self.root, "gh-%d" % at))
                run = self.run_workflow("workflow_run", head, secret=table, gh=gh)
                out = run.output()
                self.assertIn("private row %d" % (len(ROWS) + 3), out)      # the line of the row in the secret
                for withheld in ("made-up-", "qzv"):
                    self.assertNotIn(withheld, out)
                self.assertPosted([(head, "error", load_scanner().SELF_TEST)], gh=gh)


@unittest.skipIf(PRIVATE_ABSENT, PRIVATE_ABSENT)
class PrivateControlCharacters(Private):
    """Names and commit messages with a control character, and with a caret pair as plain text.  gh changes each C0
    and C1 control character of a JSON answer but tab, newline, vertical tab and carriage return to its caret pair.
    The scan step reads the GitHub API by HTTP, and the stand-in GitHub API writes JSON as GitHub does.  So the scan
    judges each name and each message as git reads it: `failure` at git's place of a sample, and `success` for a clean
    change."""

    def test_two_sibling_names_that_gh_gives_as_one_are_two_paths_with_git_s_numbers(self):
        # git keeps n<ESC> and n^[ apart, and gh gives both as n^[.  The scan reads them as two names, numbers the two
        # paths as git does, and finds the sample in n<ESC>, which git lists first.
        for kind, (held, other) in (("files", ("docs/n\x1b", "docs/n^[")),
                                    ("folders", ("docs/n\x1b/a.txt", "docs/n^[/a.txt"))):
            with self.subTest(names=kind):
                m = mark(0)
                origin, clean, head = self.two_heads(
                    "siblings-" + kind, ("two sibling names", {held: "clean\n", other: "clean\n"}),
                    ("two sibling names", {held: "a sample %s here\n" % m, other: "clean\n"}))
                self.verdicts(origin, clean, head, m, "gh-siblings-" + kind)
                self.assertIn((clean, "success", "no pattern matched: pull request 7: 1 commit(s), 2 path(s)"),
                              [(s["sha"], s["state"], s["description"])
                               for s in self.posted(os.path.join(self.root, "gh-siblings-" + kind))])
                # git holds the two names apart
                docs = git(origin.src, "rev-parse", head + ":docs")
                listed = git(origin.src, "ls-tree", "-z", "--name-only", docs)
                self.assertEqual([n for n in listed.split("\0") if n], ["a.txt", "n\x1b", "n^["])

    def test_a_name_and_a_message_that_hold_a_control_character_are_judged_as_git_judges_them(self):
        # gh gives each of these characters as a caret pair: ESC and CSI (a C1 character) as ^[, the file separator
        # as ^\ and SOH as ^A.  The scan reads the name and the message as git reads them.
        for at, (why, c) in enumerate((("ESC", "\x1b"), ("a C0 separator", "\x1c"), ("a C1 character", "\x9b"),
                                       ("SOH", "\x01"))):
            with self.subTest(character=why):
                m = mark(0)
                message = "a %s[1mbold%s[0m word" % (c, c)
                origin, clean, held = self.two_heads(
                    "control-%d" % at, (message, {"docs/odd%sname.txt" % c: "clean\n"}),
                    ("%s and %s" % (message, m), {"docs/%s-odd%sname.txt" % (m, c): "clean\n"}))
                self.verdicts(origin, clean, held, m, "gh-control-%d" % at)

    def test_a_caret_and_a_tab_in_a_name_and_a_message_are_plain_text(self):
        # `^` alone, or before a small letter, a digit or a space, and a tab, which gh does not change
        m = mark(0)
        files = {"docs/x^2.txt": "clean\n", "docs/a\ttab.txt": "clean\n"}
        message = "raise x^2 to y^a\n\na ^ alone\tand a tab"
        held = ("%s and %s" % (message, m), dict(files, **{"docs/%s\ttab.txt" % m: "clean\n"}))
        origin, clean, held = self.two_heads("plain", (message, files), held)
        self.verdicts(origin, clean, held, m, "gh-plain")

    def test_a_caret_pair_that_is_plain_text_in_a_message_or_a_name_is_judged_as_git_judges_it(self):
        # git reads `^C`, `^VOID: ` and `^[A-Za-z]` as plain characters: the three messages are texts of commits on
        # internal main (10 of its 2,091 commit messages hold a caret pair as plain text, measured 2026-11-18), and
        # `^A` is plain text in the path name.  held-content.yml judges them, and R6 allows `error` only where the scan
        # cannot read what a pull request adds.  Only gh's printing of JSON makes them look like control characters.
        for at, (message, path) in enumerate((("so a ^C stops a loop", "docs/b.txt"),
                                              ("a lane greps `^VOID: ` lines", "docs/b.txt"),
                                              ("keeps only ^[A-Za-z][A-Za-z0-9]* names", "docs/b.txt"),
                                              ("a clean change", "docs/caret^Apair.txt"))):
            with self.subTest(message=message, path=path):
                m = mark(0)
                origin, clean, held = self.two_heads("plain-%d" % at, (message, {path: "clean\n"}),
                                                     ("%s\n\nand a sample %s" % (message, m), {path: "clean\n"}))
                self.verdicts(origin, clean, held, m, "gh-plain-%d" % at)

    def test_a_change_beside_a_control_character_that_main_already_holds_is_judged_as_git_judges_it(self):
        # main already holds docs/odd<SOH>name.txt, and the pull request leaves it as it is.  git's records of the pull
        # request hold no control character: its message, its one path docs/b.txt and that path's line.  So the scan
        # gives their verdict, and not `error`.
        m = mark(0)
        origin, clean, held = self.two_heads(
            "beside", ("a clean change", {"docs/b.txt": "clean\n"}),
            ("a change", {"docs/b.txt": "a sample %s here\n" % m}),
            first={"docs/a.txt": "the first line\n", "docs/odd\x01name.txt": "already published\n"})
        self.verdicts(origin, clean, held, m, "gh-beside")


@unittest.skipIf(PRIVATE_ABSENT, PRIVATE_ABSENT)
class PrivateDemonstration(Private):
    """A run of held-content-private.yml by hand with demonstrate_a_refusal, on main."""

    def demonstrate(self, **options):
        self.repository()
        self.serve()
        run = self.run_workflow("workflow_dispatch", inputs={"demonstrate_a_refusal": True}, **options)
        self.assertFalse(run.find.runs())
        self.assertEqual(run.scans, [])
        return run, run.demonstrate.step(PLANT_ALL)

    def test_it_plants_a_sample_of_every_pattern_in_a_commit_on_main_ends_red_and_posts_nothing(self):
        run, step = self.demonstrate()
        self.assertEqual((step["outcome"], step["status"]), ("failure", 1), run.output())
        lines = step["stdout"].split("\n")
        self.assertIn("The scan of the planted commit exited 3 (3 is a refusal).", lines, run.output())
        self.assertIn("::error::demonstration: the check refused the planted samples, as it must. This run is red "
                      "on purpose.", lines)
        with open(DETECTORS, encoding="utf-8") as f:
            public = load_scanner().parse_table(f.read(), "detectors.tsv")
        every = {"detector %s (%s)" % (d.name, d.category) for d in public} | {row(k) for k in range(len(ROWS))}
        found = hits(step["stdout"])
        self.assertEqual(every - {label for _place, label in found}, set(), "a pattern it did not plant")
        self.assertEqual({place.split(" line ")[0] for place, _ in found}, {"path 1"})
        # the commit it scanned is one it made in the runner, on top of the commit of main it checked out
        work = run.demonstrate.work
        self.assertEqual(git(work, "rev-parse", "HEAD^"), git(self.origin.bare, "rev-parse", "refs/heads/main"))
        self.assertIn("the commits up to head %s" % git(work, "rev-parse", "HEAD"), step["stdout"])
        # it calls no API, posts nothing, and prints no sample
        self.assertEqual(gh_calls(self.gh), [])
        self.assertEqual(self.posted(), [])
        self.assertNotIn("qzv", run.output())

    def test_without_the_secret_it_ends_red_before_it_plants(self):
        run, step = self.demonstrate(secret="")
        self.assertEqual(step["outcome"], "failure", run.output())
        self.assertIn("HELD_CONTENT_RULES is not set", step["stderr"])
        self.assertNotIn("The scan of the planted commit", step["stdout"])
        self.assertEqual(gh_calls(self.gh), [])


class Clock:
    """A clock for the scanner's requests that only a sleep and the test move."""

    def __init__(self):
        self.now, self.slept = 1000.0, []

    def time(self):
        return self.now

    def sleep(self, seconds):
        self.slept.append(round(seconds, 6))
        self.now += seconds


@unittest.skipIf(HELD_ABSENT, HELD_ABSENT)
class ApiReads(Private):
    """The requests of the scanner's API mode, in this process against the stand-in GitHub API: their spacing, the
    clock of the scan, a read that gets no byte, the request floor, the token, the order of the commits, the blob reads
    of records_of, a folder listing that names one entry twice, and a planted sample that is not found."""

    def setUp(self):
        super().setUp()
        self.repository()
        self.scanner = load_scanner()
        environment = mock.patch.dict(os.environ, {"GITHUB_API_URL": api_server(self, self.gh, TOKEN),
                                                   "GH_TOKEN": TOKEN})
        environment.start()
        self.addCleanup(environment.stop)
        for name in ("HELD_CONTENT_REQUEST_GAP", "HELD_CONTENT_TIME_LIMIT"):
            os.environ.pop(name, None)      # the scanner's own values, as in a workflow
        self.clock = Clock()

    def api(self):
        return self.scanner.GitHub(PUBLIC, clock=self.clock.time, sleep=self.clock.sleep)

    def test_the_requests_are_a_fifth_of_a_second_apart_at_least(self):
        self.serve()
        self.assertEqual(self.scanner.REQUEST_GAP, 0.2)
        api = self.api()
        api.call("the rate limit", "rate_limit")        # the first: no wait
        api.call("the rate limit", "rate_limit")        # at the same instant: the whole gap
        self.clock.now += 0.05
        api.call("the rate limit", "rate_limit")        # 0.05 s later: the rest of the gap
        self.clock.now += 0.25
        api.call("the rate limit", "rate_limit")        # more than a gap later: no wait
        self.assertEqual(self.clock.slept, [0.2, 0.15])
        # each by HTTP, with the token
        self.assertEqual([c["http"] for c in gh_calls(self.gh)], [{"bearer": True}] * 4)

    def test_the_scan_stops_at_50_minutes_of_its_own_clock(self):
        self.serve()
        self.assertEqual(self.scanner.TIME_LIMIT, 50 * 60)
        api = self.api()
        self.clock.now += 50 * 60 - 0.5
        api.call("the rate limit", "rate_limit")
        self.clock.now += 0.5
        with self.assertRaises(self.scanner.Stop) as stopped:
            api.call("the rate limit", "rate_limit")
        self.assertEqual(stopped.exception.cause, self.scanner.TIME)
        self.assertEqual(len(gh_calls(self.gh)), 1)     # no request after the time

    def test_a_wait_for_the_gap_that_ends_past_the_time_stops_the_scan_before_its_request(self):
        # The time is not out when the second call starts.  Its wait for the gap ends past the time, and the scan then
        # sends no request.
        self.serve()
        api = self.api()
        self.clock.now += 50 * 60 - 0.1
        api.call("the rate limit", "rate_limit")
        with self.assertRaises(self.scanner.Stop) as stopped:
            api.call("the rate limit", "rate_limit")        # at the same instant: a wait of the whole gap, 0.2 s
        self.assertEqual((stopped.exception.cause, stopped.exception.message),
                         (self.scanner.TIME, "the scan ran past its time before a read of the rate limit"))
        self.assertEqual(self.clock.slept, [0.2])
        self.assertEqual(len(gh_calls(self.gh)), 1)     # no request after the time

    def test_a_call_that_starts_when_the_time_is_out_sends_no_request_and_waits_for_no_gap(self):
        # The time is out when the second call starts, 0.1 s after the first and so inside the gap of 0.2 s.  The scan
        # then stops before it waits for the rest of the gap.
        self.serve()
        api = self.api()
        self.clock.now += 50 * 60 - 0.1
        api.call("the rate limit", "rate_limit")
        self.clock.now = api.end        # 0.1 s later: the end of the time
        with self.assertRaises(self.scanner.Stop) as stopped:
            api.call("the rate limit", "rate_limit")
        self.assertEqual((stopped.exception.cause, stopped.exception.message),
                         (self.scanner.TIME, "the scan ran past its time before a read of the rate limit"))
        self.assertEqual(self.clock.slept, [])
        self.assertEqual(len(gh_calls(self.gh)), 1)     # no request after the time

    def test_an_answer_that_still_comes_when_the_time_is_out_stops_the_scan(self):
        # Each read of the socket waits CALL_MOST seconds at most.  The scan stops too when the time is out between two
        # parts of an answer, so an answer that comes slowly cannot hold the job either.  This answer ends after ten
        # parts, and the time of the scan is out after five.
        api, clock = self.api(), self.clock

        class Slow:
            headers = {}
            parts = 10

            def read1(self, most):
                if not self.parts:
                    return b""
                self.parts -= 1
                clock.now += 600        # each part comes ten minutes after the part before
                return b"x"

        with self.assertRaises(self.scanner.Stop) as stopped:
            api.body("the rate limit", Slow())
        self.assertEqual((stopped.exception.cause, clock.now), (self.scanner.TIME, 1000.0 + 50 * 60))

    def test_a_read_that_still_waits_when_the_time_is_out_stops_the_scan_call_most_seconds_later_at_most(self):
        # The answer comes one byte at a time until shortly before the time of the scan is out, and then no byte more
        # comes.  The read that waits then stops the scan after CALL_MOST seconds, and not after the whole time that
        # was left at the start of the request.  CALL_LEAST is under CALL_MOST, as in the scan.
        limit, most = 3, 0.5
        address = http_server(self, SlowAnswer, seconds=limit - 0.3)
        with mock.patch.dict(os.environ, {"GITHUB_API_URL": address, "HELD_CONTENT_TIME_LIMIT": str(limit)}):
            api = self.scanner.GitHub(PUBLIC)
        started = time.monotonic()
        with mock.patch.object(self.scanner, "CALL_LEAST", 0.1), mock.patch.object(self.scanner, "CALL_MOST", most):
            with self.assertRaises(self.scanner.Stop) as stopped:
                api.call("the rate limit", "rate_limit")
        took = time.monotonic() - started
        self.assertEqual(stopped.exception.cause, self.scanner.TIME)
        # a read that waits for the whole time that was left at the start of the request takes about 2 * limit
        self.assertLess(took, limit + most + 1)

    def test_a_read_that_gets_no_byte_while_the_time_still_runs_is_a_read_that_failed(self):
        # The time of the scan is TIME_LIMIT, 50 minutes, and a read of the socket waits CALL_MOST seconds at most.  A
        # read that gets no byte in that time stops the scan with READ, and not with TIME: the time is not out, so a
        # later read can still succeed.  The read gets no byte before the status line, or in the body of the answer.
        most = 0.5
        self.serve(hang=[{"endpoint": "^rate_limit$", "seconds": 60}])
        slow = http_server(self, SlowAnswer, seconds=0.3)
        for where, address in (("before the status line", os.environ["GITHUB_API_URL"]), ("in the body", slow)):
            with self.subTest(no_byte=where):
                with mock.patch.dict(os.environ, {"GITHUB_API_URL": address}):
                    api = self.scanner.GitHub(PUBLIC)
                with mock.patch.object(self.scanner, "CALL_LEAST", 0.1), \
                        mock.patch.object(self.scanner, "CALL_MOST", most):
                    with self.assertRaises(self.scanner.Stop) as stopped:
                        api.call("the rate limit", "rate_limit")
                self.assertEqual((stopped.exception.cause, stopped.exception.message),
                                 (self.scanner.READ, "a read of the rate limit got no byte for 0.5 seconds"))

    def test_a_refusal_whose_body_gets_no_byte_is_late_when_the_time_is_out_and_else_a_read_that_failed(self):
        # A 403 answer with no header of a rate limit can name one in its body, so the scan reads the body.  A read of
        # that body that gets no byte stops the scan with TIME when the time is out.  Else the body names no rate
        # limit, and the refusal is a read that failed.  The body sends a byte every 0.1 seconds, and then no byte:
        # shortly before a time of `limit` seconds is out, or after 0.3 seconds of the 50 minutes of TIME_LIMIT.
        limit, most = 3, 0.5
        late = (self.scanner.TIME, self.scanner.LATE % "the rate limit")
        failed = (self.scanner.READ, "a read of the rate limit failed (HTTP 403). The answer is not printed, because "
                                     "it can name a path or a commit.")
        for out, variables, seconds, expected in ((True, {"HELD_CONTENT_TIME_LIMIT": str(limit)}, limit - 0.3, late),
                                                  (False, {}, 0.3, failed)):
            with self.subTest(time_out=out):
                address = http_server(self, SlowRefusal, seconds=seconds)
                with mock.patch.dict(os.environ, dict(variables, GITHUB_API_URL=address)):
                    api = self.scanner.GitHub(PUBLIC)
                with mock.patch.object(self.scanner, "CALL_LEAST", 0.1), \
                        mock.patch.object(self.scanner, "CALL_MOST", most):
                    with self.assertRaises(self.scanner.Stop) as stopped:
                        api.call("the rate limit", "rate_limit")
                self.assertEqual((stopped.exception.cause, stopped.exception.message), expected)

    def test_a_url_error_for_a_timeout_is_late_when_the_time_is_out_and_else_a_read_that_failed(self):
        # urllib gives a timeout of the connect or of the send as a URLError, with a TimeoutError as its reason.  Such
        # a read stops the scan with TIME when the time is out.  Else the cause is READ, as for a read that gets no
        # byte.  The message then names the timeout that the call gave to the read.
        scanner, clock = self.scanner, self.clock

        class TimesOut:
            """An opener that sends no request.  Each request times out, and when `late` is true, the clock is then
            past the end of the time of `api`."""

            def __init__(self, api, late):
                self.api, self.late, self.timeouts = api, late, []

            def open(self, request, timeout=None):
                self.timeouts.append(timeout)
                if self.late:
                    clock.now = self.api.end + 1
                raise scanner.urllib.error.URLError(TimeoutError())

        for late in (True, False):
            with self.subTest(time_out=late):
                api = self.api()
                api.opener = opener = TimesOut(api, late)
                with self.assertRaises(scanner.Stop) as stopped:
                    api.call("the rate limit", "rate_limit")
                (timeout,) = opener.timeouts
                expected = ((scanner.TIME, scanner.LATE % "the rate limit") if late else
                            (scanner.READ, scanner.STALLED % ("the rate limit", timeout)))
                self.assertEqual((stopped.exception.cause, stopped.exception.message), expected)

    def test_the_timeout_of_a_read_is_the_time_that_is_left_but_call_least_at_least_and_call_most_at_most(self):
        # A read of the socket waits for the time of the scan that is left when its request starts.  But it waits
        # CALL_MOST seconds at most and CALL_LEAST seconds at least.  The opener records the timeout that it gets, and
        # then it does not connect.  So each call stops the scan with READ.
        scanner, clock = self.scanner, self.clock
        self.assertEqual((scanner.CALL_LEAST, scanner.CALL_MOST), (5, 60))

        class Refuses:
            """An opener that sends no request.  It records the timeout of each request, and then it cannot connect."""

            def __init__(self):
                self.timeouts = []

            def open(self, request, timeout=None):
                self.timeouts.append(timeout)
                raise scanner.urllib.error.URLError(ConnectionRefusedError())

        api = self.api()
        api.opener = opener = Refuses()
        # The three calls start when 50 minutes, 20 seconds and 2 seconds of the scan are left.  They are far apart, so
        # no call waits for the gap.
        starts = [clock.now, api.end - 20, api.end - 2]
        for start in starts:
            clock.now = start
            with self.assertRaises(scanner.Stop) as stopped:
                api.call("the rate limit", "rate_limit")
            self.assertEqual(stopped.exception.cause, scanner.READ)
        self.assertEqual(opener.timeouts, [scanner.CALL_MOST, api.end - starts[1], scanner.CALL_LEAST])

    def test_a_read_that_gets_no_byte_leaves_the_other_pull_requests_of_the_head_to_scan(self):
        # Pull requests 7 and 8 have one head, which adds a sample.  The read of pull request 7 gets no byte, early in
        # the scan.  That read failed, but the time of the scan is not out.  So the scan reads pull request 8, and the
        # verdict on the head is its `failure`.
        head = self.origin.commit("a change", {"docs/b.txt": sample("github-token") + "\n"})
        self.serve({"number": 7, "head": head}, {"number": 8, "head": head},
                   hang=[{"endpoint": "/pulls/7$", "seconds": 60}])
        verdict, out = os.path.join(self.root, "verdict.json"), io.StringIO()
        # CALL_MOST is small, and far over the time of one read of the stand-in
        with mock.patch.object(self.scanner, "CALL_LEAST", 0.1), mock.patch.object(self.scanner, "CALL_MOST", 5), \
                mock.patch.dict(os.environ, {"HELD_CONTENT_REQUEST_GAP": "0"}), contextlib.redirect_stdout(out), \
                contextlib.redirect_stderr(out):
            status = self.scanner.scan_pull_requests(PUBLIC, head, [7, 8], verdict, True)
        self.assertEqual(status, 0, out.getvalue())
        with open(verdict) as f:
            self.assertEqual(json.load(f), {"state": "failure", "pull_requests": [7, 8],
                                            "description": "held content: pull request 8: path 1 line 1"},
                             out.getvalue())
        self.assertIn("pull request 7 could not be judged: a read of pull request 7 got no byte for 5 seconds",
                      out.getvalue())
        self.assertEqual([c.get("hung") for c in gh_calls(self.gh) if "/pulls/" in c["endpoint"]], [60, None])

    def test_an_answer_with_fewer_bytes_than_its_length_stops_the_scan(self):
        parts = [b"", b"abc"]

        class Short:
            headers = {"Content-Length": "5"}

            def read1(self, most):
                return parts.pop()

        with self.assertRaises(self.scanner.Stop) as stopped:
            self.api().body("the rate limit", Short())
        self.assertEqual(stopped.exception.cause, self.scanner.READ)

    def test_no_gh_token_stops_the_scan_before_its_first_request(self):
        self.serve()
        with mock.patch.dict(os.environ):
            del os.environ["GH_TOKEN"]
            api = self.api()
        with self.assertRaises(self.scanner.Stop) as stopped:
            api.call("the rate limit", "rate_limit")
        self.assertEqual(stopped.exception.cause, self.scanner.READ)
        self.assertEqual(gh_calls(self.gh), [])

    def test_the_floor_is_a_fifth_of_the_limit_and_3000_at_most(self):
        for limit, remaining, cost, stops in ((15000, 3000, 0, False), (15000, 2999, 0, True),
                                              (15000, 3002, 2, False), (15000, 3002, 3, True),
                                              (5000, 1000, 0, False), (5000, 999, 0, True)):
            with self.subTest(limit=limit, remaining=remaining, cost=cost):
                self.serve(rate={"limit": limit, "remaining": remaining})
                if not stops:
                    self.api().floor(cost)
                    continue
                with self.assertRaises(self.scanner.Stop) as stopped:
                    self.api().floor(cost)
                self.assertEqual(stopped.exception.cause, self.scanner.FLOOR)

    def test_the_count_is_read_before_the_first_read_and_after_every_100(self):
        api, asked = self.api(), []

        def call(what, endpoint, raw=False):
            asked.append(endpoint)
            return b'{"resources": {"core": {"limit": 15000, "remaining": 15000}}}'

        api.call = call
        for n in range(201):
            api.read("a file", "read-%d" % n)
        self.assertEqual([at for at, endpoint in enumerate(asked) if endpoint == "rate_limit"], [0, 101, 202])
        self.assertEqual(len(asked), 204)

    def test_the_commits_come_out_in_git_s_order_on_histories_with_merges(self):
        rng, src = random.Random(553), self.origin.src
        tree = git(src, "rev-parse", self.origin.base + "^{tree}")
        install_gh(self.gh, {"git": src})
        api, checked = self.api(), 0
        for history, times in enumerate(("equal", "few", "any")):
            made = [self.origin.base]
            for n in range(1, 21):
                when = 1700000000 + {"equal": 0, "few": rng.randrange(3), "any": rng.randrange(40)}[times]
                parents = rng.sample(made, min(len(made), rng.choice((1, 1, 1, 2, 2, 3))))
                stamp = "%d +0000" % when
                with mock.patch.dict(os.environ, {"GIT_AUTHOR_DATE": stamp, "GIT_COMMITTER_DATE": stamp}):
                    made.append(git(src, "commit-tree", tree, "-m", "commit %d of history %d" % (n, history),
                                    *[word for parent in parents for word in ("-p", parent)]))
            for _ in range(4):
                head, base = rng.choice(made[1:]), rng.choice(made)
                with self.subTest(committer_times=times, head=made.index(head), base=made.index(base)):
                    merge_base = git(src, "merge-base", base, head)
                    log = git(src, "log", "--reverse", "--format=%s", "%s..%s" % (merge_base, head))
                    _old, _new, messages = self.scanner.commits_of(api, base, head)
                    self.assertEqual([message.decode() for message in messages], log.split("\n") if log else [])
                    checked += len(messages)
        self.assertGreater(checked, 30)     # the histories gave the walk something to order

    def test_a_blob_stays_in_memory_only_until_the_last_path_that_reads_it(self):
        # The API mode reads each blob once.  It keeps a blob only while a later path reads the same id, so it holds
        # about the blobs of one path and not every blob of the change.  Paths 2 and 5 hold one text.
        base, shared = self.origin.base, "the same text at two paths\n"
        head = self.origin.commit("five changed paths", {
            "README.md": "A changed first line.\n", "docs/1.txt": shared, "docs/2.txt": "two\n",
            "docs/3.txt": "three\n", "docs/4.txt": shared})
        self.serve({"number": 7, "head": head})
        api, reads, freed = self.api(), [], []
        plain = api.read

        class Blob(bytes):
            """The bytes of a blob, which note when they leave memory."""

            def __del__(self):
                freed.append(self.oid)

        def read(what, endpoint, raw=False):
            answer = plain(what, endpoint, raw)
            if not raw:
                return answer
            # each blob read, with the blobs that are in memory when it is read
            reads.append((endpoint.rsplit("/", 1)[1], [oid for oid, _ in reads if oid not in freed]))
            answer = Blob(answer)
            answer.oid = reads[-1][0]
            return answer

        api.read = read
        _records, _commits, paths = self.scanner.pull_request_records(api, "main", head)
        old, new, one, two, three = (git(self.origin.src, "rev-parse", at) for at in (
            base + ":README.md", head + ":README.md", head + ":docs/1.txt", head + ":docs/2.txt", head + ":docs/3.txt"))
        self.assertEqual(paths, 5)
        self.assertEqual(reads, [(old, []), (new, []), (one, []), (two, [one]), (three, [one])])
        self.assertEqual(sorted(freed), sorted([old, new, one, two, three]))    # none is in memory after the scan

    def test_records_of_reads_the_blobs_of_blob_reads_in_their_order(self):
        # fetch_blobs fetches the ids of blob_reads, and the API mode reads each of them once and keeps it until its
        # last read.  So records_of reads those ids, in that order, and no other.
        changes = [(b"added", None, b"blob-1"), (b"changed", b"blob-2", b"blob-3"), (b"deleted", b"blob-4", None),
                   (b"a submodule, or a change of mode alone", None, None), (b"changed too", b"blob-3", b"blob-5")]
        reads = []

        def read(oid, place):
            if oid is None:
                return b""
            reads.append(oid)
            return b"a line of %s\n" % oid

        self.scanner.records_of([b"a message"], changes, read)
        self.assertEqual(reads, self.scanner.blob_reads(changes))
        self.assertEqual(reads, [b"blob-1", b"blob-2", b"blob-3", b"blob-3", b"blob-5"])

    def test_a_folder_listing_that_names_one_entry_twice_stops_the_scan(self):
        # A git tree holds each name once, so such a listing is a broken answer.  It would leave one of the two entries
        # unread.
        entry = {"path": "twice.txt", "mode": "100644", "type": "blob", "sha": "1" * 40, "size": 6}
        api = self.api()
        api.json = lambda what, endpoint: {"truncated": False, "tree": [entry, dict(entry, sha="2" * 40)]}
        with self.assertRaises(self.scanner.Stop) as stopped:
            self.scanner.tree_changes(api, "a" * 40, "b" * 40)
        self.assertEqual(stopped.exception.cause, self.scanner.READ)

    def test_a_planted_sample_that_its_detector_does_not_find_is_an_error(self):
        head = self.origin.commit("a clean change", {"docs/b.txt": "clean\n"})
        self.serve({"number": 7, "head": head, "labels": ["prove-it-can-fail"]})
        drawn, verdict, out = self.scanner.fresh_canaries, os.path.join(self.root, "verdict.json"), io.StringIO()
        draws = []

        def canaries(detectors):
            # The first draw is the self-test's.  The second is the label's: its first sample becomes text that its
            # detector does not find.
            draws.append(drawn(detectors))
            return draws[-1] if len(draws) == 1 else [(draws[-1][0][0], b"nothing held")] + draws[-1][1:]

        with mock.patch.object(self.scanner, "fresh_canaries", canaries), contextlib.redirect_stdout(out), \
                contextlib.redirect_stderr(out), mock.patch.dict(os.environ, {"HELD_CONTENT_REQUEST_GAP": "0"}):
            status = self.scanner.main(["--public-only", "--pull-request", PUBLIC, head, "7", "--verdict", verdict])
        self.assertEqual((status, len(draws)), (0, 2), out.getvalue())
        with open(verdict) as f:
            self.assertEqual(json.load(f), {"state": "error", "description": self.scanner.PLANTED,
                                            "pull_requests": [7]})

    def test_a_wrong_argument_of_the_api_mode_ends_with_exit_2_and_no_verdict(self):
        verdict, head = os.path.join(self.root, "verdict.json"), "0" * 40
        for args in ([PUBLIC, head, "7"], [PUBLIC, head, "7", "--verdict"], [PUBLIC, head, "--verdict", verdict],
                     [PUBLIC, "main", "7", "--verdict", verdict], [PUBLIC, head, "seven", "--verdict", verdict],
                     ["no-owner", head, "7", "--verdict", verdict]):
            with self.subTest(args=args[:-1]):
                r = subprocess.run([sys.executable, SCANNER, "--public-only", "--pull-request", *args],
                                   env=child_environment(NO_HOME), capture_output=True, text=True)
                self.assertEqual(r.returncode, 2, r.stdout + r.stderr)
                self.assertFalse(os.path.exists(verdict))


@unittest.skipIf(WORKFLOWS_ABSENT, WORKFLOWS_ABSENT)
class WorkflowInvariants(unittest.TestCase):
    """What must stay true of the four workflows of the public checks, read as YAML (OSSV-553): which file
    holds the secret and in which steps, what the private workflow reads of a pull request, and what a job that
    starts on pull_request may do."""

    @classmethod
    def setUpClass(cls):
        cls.private = yamlio.load_file(PRIVATE)
        cls.jobs = cls.private["jobs"]
        with open(PRIVATE, encoding="utf-8") as f:
            cls.text = f.read()

    def steps(self):
        return [(name, step) for name, job in self.jobs.items() for step in job["steps"]]

    def test_the_private_workflow_starts_on_no_event_of_a_pull_request_and_runs_in_the_public_repository(self):
        on = self.private["on"]
        self.assertEqual(self.private["name"], CONTEXT)
        self.assertEqual(set(on), {"workflow_run", "schedule", "workflow_dispatch"})
        # by the name of held-content.yml, with no `branches` key
        self.assertEqual(on["workflow_run"], {"workflows": [yamlio.load_file(HELD_CONTENT)["name"]],
                                              "types": ["completed"]})
        self.assertEqual(on["schedule"], [{"cron": "17 * * * *"}])
        self.assertEqual(list(on["workflow_dispatch"]["inputs"]), ["demonstrate_a_refusal"])
        self.assertEqual(on["workflow_dispatch"]["inputs"]["demonstrate_a_refusal"]["type"], "boolean")
        self.assertEqual(self.private["permissions"], {})
        self.assertEqual(self.private["defaults"], {"run": {"shell": "bash"}})
        self.assertEqual(list(self.jobs), ["find", "scan", "demonstrate"])
        for name, job in self.jobs.items():
            with self.subTest(job=name):
                self.assertEqual(job["runs-on"], "ubuntu-24.04")
                condition_text = " ".join(job["if"].split())
                self.assertTrue(condition_text.startswith("github.repository == '%s' && " % PUBLIC), condition_text)
                # on a run by hand, each job names main
                self.assertIn("github.ref == 'refs/heads/main'", condition_text)

    def test_only_the_private_workflow_names_the_secret_and_only_in_its_scan_and_planting_steps(self):
        for name in sorted(os.listdir(WORKFLOWS)):
            if os.path.join(WORKFLOWS, name) != PRIVATE:
                with open(os.path.join(WORKFLOWS, name), encoding="utf-8") as f:
                    self.assertNotIn("secrets.HELD_CONTENT_RULES", inline_scripts(f.read()), name)

        def strings(node, where=()):
            if isinstance(node, dict):
                for key, item in node.items():
                    yield from strings(item, where + (key,))
            elif isinstance(node, list):
                for at, item in enumerate(node):
                    yield from strings(item, where + (at,))
            elif isinstance(node, str):
                yield where, node

        named = {where: text for where, text in strings(self.private) if "secrets" in text}
        places = {("jobs", name, "steps", at, "env", "HELD_CONTENT_RULES")
                  for name, wanted in (("scan", API_SCAN), ("demonstrate", PLANT_ALL))
                  for at, step in enumerate(self.jobs[name]["steps"]) if step.get("name") == wanted}
        self.assertEqual(len(places), 2)
        self.assertEqual(named, dict.fromkeys(places, "${{ secrets.HELD_CONTENT_RULES }}"))

    def test_no_step_of_the_private_workflow_checks_out_fetches_or_runs_a_file_of_a_pull_request(self):
        held_content = yamlio.load_file(HELD_CONTENT)["jobs"]["held-content"]["steps"]
        pinned = next(step["uses"] for step in held_content if "uses" in step)
        used = [(name, step) for name, step in self.steps() if "uses" in step]
        self.assertEqual([name for name, _ in used], ["scan", "demonstrate"])
        for name, step in self.steps():
            with self.subTest(job=name, step=step.get("name")):
                if "uses" in step:
                    # main's commit, the scanner's folder alone, and no token left in the clone
                    self.assertEqual(step["uses"], pinned)
                    self.assertEqual(step["with"], {"ref": "${{ github.sha }}", "fetch-depth": 1,
                                                    "persist-credentials": False, "sparse-checkout": ".github/held",
                                                    "sparse-checkout-cone-mode": False})
                    continue
                for refused in ("refs/pull", "git fetch", "git clone", "git checkout", "git pull", "git remote",
                                "gh pr", "gh run", "download"):
                    self.assertNotIn(refused, step["run"])
                # the one file a step runs is main's copy of the scanner
                self.assertLessEqual(set(re.findall(r"python3 (\S+)", step["run"])),
                                     {"-", ".github/held/held_content_scan.py"})
        self.assertNotIn("download-artifact", self.text)
        self.assertNotIn("upload-artifact", self.text)

    def test_a_job_that_starts_on_pull_request_has_read_permissions_alone_and_no_secret(self):
        for path in (HELD_CONTENT, FREEZE_WORKFLOW, PINS_WORKFLOW):
            with self.subTest(workflow=os.path.basename(path)):
                workflow = yamlio.load_file(path)
                self.assertIn("pull_request", workflow["on"])
                self.assertNotIn("pull_request_target", workflow["on"])
                self.assertEqual(workflow["permissions"], {})
                for job in workflow["jobs"].values():
                    self.assertTrue(job["permissions"])
                    self.assertEqual(set(job["permissions"].values()), {"read"})
                with open(path, encoding="utf-8") as f:
                    text = f.read()
                for refused in ("secrets.", "id-token"):
                    self.assertNotIn(refused, text)
        # the private workflow starts on no event of a pull request, and its one write is the status of scan
        self.assertEqual({name: job["permissions"] for name, job in self.jobs.items()}, {
            "find": {"pull-requests": "read", "statuses": "read"},
            "scan": {"contents": "read", "pull-requests": "read", "statuses": "write"},
            "demonstrate": {"contents": "read"}})
        self.assertNotIn("id-token", self.text)

    def test_one_scan_job_for_each_head_and_never_two_at_once_on_one_head(self):
        scan = self.jobs["scan"]
        self.assertEqual(scan["needs"], "find")
        self.assertEqual(scan["strategy"], {"fail-fast": False, "max-parallel": 2, "matrix": {
            "include": "${{ fromJSON(needs.find.outputs.matrix) }}"}})
        self.assertEqual(scan["timeout-minutes"], 60)
        self.assertEqual(scan["concurrency"], {"group": "held-content-private-${{ matrix.head }}",
                                               "cancel-in-progress": False})
        runs = Concurrency(scan)
        one, other = ({"matrix": {"head": letter * 40}} for letter in "12")
        runs.start("the scan of a workflow_run run", one)
        runs.start("the scan of the hourly run", one)
        runs.start("the scan of another head", other)
        self.assertEqual([runs.state(name) for name in ("the scan of a workflow_run run", "the scan of the hourly run",
                                                        "the scan of another head")], ["running", "pending", "running"])
        runs.finish("the scan of a workflow_run run")
        self.assertEqual(runs.state("the scan of the hourly run"), "running")

    def test_the_scan_step_alone_holds_the_secret_and_the_post_step_needs_no_file_of_the_checkout(self):
        steps = {step.get("name"): step for step in self.jobs["scan"]["steps"]}
        self.assertEqual(list(steps)[1:], [API_SCAN, POST])
        scan, post = steps[API_SCAN], steps[POST]
        self.assertEqual(set(scan["env"]), {"GH_TOKEN", "HELD_CONTENT_RULES", "REPO", "HEAD", "NUMBERS"})
        self.assertNotIn("if", scan)
        self.assertEqual(post["if"], "always() && !cancelled()")
        self.assertEqual(set(post["env"]), {"GH_TOKEN", "REPO", "HEAD", "NUMBERS", "RUN_URL"})
        for refused in (".github", "git ", "pending"):
            self.assertNotIn(refused, post["run"])
        # no workflow sets the variables with which the tests change the scanner's spacing and its clock
        for name in sorted(os.listdir(WORKFLOWS)):
            with open(os.path.join(WORKFLOWS, name), encoding="utf-8") as f:
                text = inline_scripts(f.read())
            for variable in ("HELD_CONTENT_REQUEST_GAP", "HELD_CONTENT_TIME_LIMIT"):
                self.assertNotIn(variable, text, name)


if __name__ == "__main__":
    unittest.main()
