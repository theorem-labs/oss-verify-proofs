"""The report of `oft prove` as the pull request check `theorem/prove: <unit>` (`oft prove --post-check`): a GitHub
check run on the head commit of the pull request, with stdlib urllib.  Each unit has a check run of its own name, so a
pull request that changes two units shows both (GitHub shows the newest check run of each name).

The check's conclusion comes from the contract states (prove.STATES):

    action_required   a contract needs work, is a changed contract, is removed or is unknown
    neutral           every contract that is not unchanged is data changed: Rocq decides, no agent is predicted
                      (Ruling 22), and the summary says so above the report
    success           every contract is unchanged, or the unit has none

Its title counts the contracts that need work (prove.PREDICTS_WORK: needs work, changed contract and removed), the
functions changed (the rows of every build whose class prove.CHANGED_CLASSES names: changed, added or removed), and the
data changed and unknown contracts when there are any.  Its summary is prove.markdown, cut to GitHub's limit of LIMIT
characters when it is longer (_summary): the counts stay whole, and the rows that predict an agent's work come first.
The state is a prediction, never a verdict: Rocq checks every proof, so success says no agent is predicted, not that a
proof holds.

Writing a check run needs a GitHub App installation token, or a workflow's GITHUB_TOKEN, with checks: write on the
repository: a Token, which is checked once, when it is made, before the report.  `oft prove --post-check`
(__main__.cmd_prove) makes the report with prove.py, prints it, then posts it with run().  code_target reads the line
`Code: OWNER/REPO@SHA` of a pull request's body: the commit of the code repository, where the prove workflow
(.github/workflows/prove.yml, ci/prove-pr) posts the same check when github_repository of a unit's `library.repository`
names that repository.

This module is not the checker (keys.NOT_THE_CHECKER): no check posts a check run."""
import collections
import http.client
import json
import re
import urllib.error
import urllib.request

from . import prove

# the check run of a unit is named NAME + ": <project>/<harness>"
NAME = "theorem/prove"
API = "https://api.github.com"
NEUTRAL = ("Every contract that is not unchanged is data changed: Rocq decides whether its proofs still hold, and no "
           "agent is predicted.")
# GitHub's limit on a check run's output.summary, in characters
LIMIT = 65535
LEFT_OUT = ("_%d of the report's %d rows are left out to keep this summary within GitHub's 65,535 characters: the full "
            "report is the output of `oft prove`, and every row is in `oft prove --json`._")
# a token: printable ASCII, with no whitespace or control character (a header value may hold no other, and http.client
# names the whole value when it refuses one)
_TOKEN = re.compile(r"[\x21-\x7e]+")
# what stands for each whole copy of the token in every text post shows: GitHub's message, its body, a header, an
# error's reason
REDACTED = "[token]"
# a commit of a GitHub repository, OWNER/REPO@SHA: where `oft prove --post-check` posts, and what a pull request's
# `Code:` line names; the commit by its full lower-case id
TARGET = re.compile(r"([A-Za-z0-9][A-Za-z0-9-]*)/([A-Za-z0-9._-]+)@([0-9a-f]{40})")
# a line of a pull request's body that names the commit of its code repository (code_target)
CODE = "Code:"
# a pull request on GitHub, as `oft prove --pull-request` takes it
PULL_REQUEST = re.compile("https" + r"://github\.com/[A-Za-z0-9][A-Za-z0-9-]*/[A-Za-z0-9._-]+/pull/[1-9][0-9]*")
# what the summary says first with --pull-request: the report is of a change no reviewer has merged
UNMERGED = ("This report is of the head of an unmerged pull request, %s: a prediction for a proposed change that no "
            "one has merged, not a result of the repository's main branch.")


class PostError(Exception):
    """A check run GitHub did not make: its answer, or why there was none, with REDACTED for each copy of the token;
    status is the HTTP status of GitHub's refusal, None when there was no answer or no token was sent."""

    def __init__(self, text, status=None):
        super().__init__(text)
        self.status = status


# a check run GitHub made: its id, and its page (None when GitHub's answer names none), which the job log shows
Posted = collections.namedtuple("Posted", "id url")
# a repository on GitHub as a fact's URL names it (library.repository): https://github.com/OWNER/REPO, with .git or a
# slash after it or neither
GITHUB_URL = re.compile(re.escape("https://github.com/") + r"([A-Za-z0-9][A-Za-z0-9-]*)/([A-Za-z0-9._-]+?)(?:\.git)?/?")


def github_repository(url):
    """OWNER/REPO, lower-cased (GitHub's names ignore case), of a GitHub repository's URL (GITHUB_URL); None for any
    other URL."""
    m = GITHUB_URL.fullmatch(url) if isinstance(url, str) else None
    if not m or m.group(2) in (".", ".."):
        return None
    return ("%s/%s" % m.group(1, 2)).lower()


def target(text):
    """(repository, commit) of text when it is OWNER/REPO@SHA (TARGET), else None."""
    m = TARGET.fullmatch(text)
    if not m or m.group(2) in (".", ".."):
        return None
    return "%s/%s" % m.group(1, 2), m.group(3)


def code_target(body):
    """The commit a pull request's body names on a line of its own, `Code: OWNER/REPO@SHA` (CODE, target), where the
    prove workflow also posts the check: ((repository, commit) or None, [problem]).  Lines that name one commit are
    one; lines that name two or more name none.  A line that starts with `Code:` and names no commit is a problem,
    named by its number: its text is the pull request author's, and is never shown."""
    found, problems = [], []
    for n, line in enumerate((body or "").splitlines(), 1):
        line = line.strip()
        if not line.startswith(CODE):
            continue
        got = target(line[len(CODE):].strip())
        if got is None:
            problems.append("line %d of the pull request's body starts with `%s` but is not `%s OWNER/REPO@SHA` with "
                            "the full 40-hex commit id" % (n, CODE, CODE))
        elif got not in found:
            found.append(got)
    if len(found) > 1:
        problems.append("the pull request's body names %d code commits on `%s` lines (%s): none is posted"
                        % (len(found), CODE, ", ".join("%s@%s" % t for t in found)))
        return None, problems
    return (found[0] if found else None), problems


class Token(str):
    """An installation token that can be sent (printable ASCII, no whitespace or control character), checked here,
    once, when it is made: ValueError, which does not show it, for any other value.  post sends no other."""

    def __new__(cls, value):
        if not isinstance(value, str) or _TOKEN.fullmatch(value) is None:
            raise ValueError("the token is empty or holds whitespace, a control character or a non-ASCII character; "
                             "it is not shown")
        return super().__new__(cls, value)


def payload(r, sha, pull_request=None):
    """The check run `theorem/prove: <unit>` of the prove.Report r on the commit sha, as the body of a POST
    /check-runs; with pull_request (a PULL_REQUEST URL), its summary names that pull request first (UNMERGED)."""
    states = collections.Counter(c["state"] for c in r.contracts)
    work, data, unknown = sum(states[s] for s in prove.PREDICTS_WORK), states["data changed"], states["unknown"]
    title = "%d contracts need work, %d functions changed" % (work, sum(r.counts[c] for c in prove.CHANGED_CLASSES))
    title += (", %d data changed" % data if data else "") + (", %d unknown" % unknown if unknown else "")
    conclusion = "action_required" if work or unknown else "neutral" if data else "success"
    prefix = UNMERGED % pull_request + "\n\n" if pull_request else ""
    summary = _summary(r, prefix + (NEUTRAL + "\n\n" if conclusion == "neutral" else ""))
    return {"name": "%s: %s" % (NAME, r.unit), "head_sha": sha, "status": "completed", "conclusion": conclusion,
            "output": {"title": title, "summary": summary}}


def _summary(r, prefix):
    """prefix and prove.markdown(r), or, when they hold more than LIMIT characters, prefix and the parts of the
    Markdown (prove.markdown_parts) with each row that fits in what the rows before it left, taken in this order: the
    contracts in a prove.FIRST state, the functions whose instructions changed, the other contracts (data changed, then
    unchanged); then a line that says how many rows are left out (LEFT_OUT).  A row too long to fit hides no row after
    it.  Each list keeps its order and its lines above its rows."""
    text = prefix + prove.markdown(r)
    if len(text) <= LIMIT:
        return text
    head, (above_functions, functions), (above_contracts, contracts) = prove.markdown_parts(r)
    order = ([("contract", i) for i, (state, _l) in enumerate(contracts) if state in prove.FIRST]
             + [("function", i) for i in range(len(functions))]
             + [("contract", i) for i, (state, _l) in enumerate(contracts) if state not in prove.FIRST])
    total = len(functions) + len(contracts)
    # what is always shown, each line with its newline; the count left out at its widest
    room = LIMIT - len(prefix) - sum(len(l) + 1 for l in head + above_functions + above_contracts
                                     + ["", LEFT_OUT % (total, total)])
    kept = set()
    for kind, i in order:
        line = functions[i] if kind == "function" else contracts[i][1]
        if len(line) + 1 > room:
            continue
        room -= len(line) + 1
        kept.add((kind, i))
    lines = (head + above_functions + [l for i, l in enumerate(functions) if ("function", i) in kept]
             + above_contracts + [l for i, (_s, l) in enumerate(contracts) if ("contract", i) in kept]
             + ["", LEFT_OUT % (total - len(kept), total)])
    return prefix + "\n".join(lines) + "\n"


def post(repo, payload, token, api=API):
    """POST payload (what payload() gives) to /repos/<repo>/check-runs of the REST API at api, with token, a Token:
    the Posted check run GitHub made, its id and its page.  PostError for any other answer, with GitHub's message (or
    the first 200 characters of its body), the permission it asks for and its HTTP status, and for no answer;
    TypeError for a token that is not a Token, which is never sent.  In a PostError, REDACTED stands for each whole
    copy of the token, replaced before any text is cut."""
    where = "POST /repos/%s/check-runs" % repo
    if not isinstance(token, Token):
        raise TypeError("%s: the token is no check_run.Token; it is not sent" % where)

    def refused(why, status=None):
        return PostError(("%s: %s" % (where, why)).replace(token, REDACTED), status)
    req = urllib.request.Request(api.rstrip("/") + "/repos/%s/check-runs" % repo, data=json.dumps(payload).encode(),
                                 method="POST", headers={"Accept": "application/vnd.github+json",
                                                         "Authorization": "Bearer " + token,
                                                         "Content-Type": "application/json",
                                                         "X-GitHub-Api-Version": "2022-11-28"})
    try:
        with urllib.request.urlopen(req, timeout=60) as resp:
            status, data = resp.status, resp.read()
    except urllib.error.HTTPError as e:
        try:
            data = e.read()
        except (http.client.HTTPException, OSError) as unread:
            raise refused("HTTP %d, whose body could not be read: %s" % (e.code, _why(unread)), e.code) from None
        try:
            message = json.loads(data)["message"]
        except (ValueError, KeyError, TypeError):
            # replaced before the cut, which would leave a part of a token that crosses it
            message = data.decode("utf-8", "replace").replace(token, REDACTED).strip()[:200] or e.reason
        needs = e.headers.get("X-Accepted-GitHub-Permissions")
        raise refused("HTTP %d: %s%s" % (e.code, message, " (the token needs %s)" % needs if needs else ""),
                      e.code) from None
    except (urllib.error.URLError, http.client.HTTPException, OSError) as e:
        raise refused("no complete answer: %s" % _why(e)) from None
    try:
        made = json.loads(data)
        url = made.get("html_url")
        return Posted(made["id"], url if isinstance(url, str) else None)
    except (ValueError, KeyError, TypeError, AttributeError):
        raise refused("HTTP %d with no check run id" % status) from None


def _why(e):
    """An error with no HTTP status (a connection refused, an answer cut short or that is no HTTP) as text: a URLError's
    reason, else the error's class and its text."""
    if isinstance(e, urllib.error.URLError):
        return str(e.reason)
    name, text = type(e).__name__, str(e).strip()
    return text if text.startswith(name) else "%s: %s" % (name, text) if text else name


def run(r, posts, token, api, err, pull_request=None):
    """`oft prove --post-check` and `--post-check-optional`: for each (repo, sha, optional) of posts, the prove.Report
    r as the check run `theorem/prove: <unit>` on the commit sha of the GitHub repository repo (payload, with
    pull_request), posted with token (a Token) to the REST API at api, and a line to err that names the check run and
    its page, or says why GitHub made none; a refusal stops no other post.  A refusal with 403 or 404 of an optional
    post is a warning, not a failure: the App is not installed on that repository, or may not write its checks.  The
    exit status: 0 when every check run asked for was made or warned of, else 1."""
    failed = False
    for repo, sha, optional in posts:
        flag = "--post-check-optional" if optional else "--post-check"
        body = payload(r, sha, pull_request)
        try:
            got = post(repo, body, token, api)
        except PostError as e:
            if optional and e.status in (403, 404):
                print("WARN oft prove %s: %s; no check run there" % (flag, e), file=err)
            else:
                print("FAIL oft prove %s: %s" % (flag, e), file=err)
                failed = True
            continue
        print('oft prove: posted check run %d "%s" on %s@%s: %s, %s%s'
              % (got.id, body["name"], repo, sha, body["conclusion"], body["output"]["title"],
                 ": " + got.url if got.url else ""), file=err)
    return 1 if failed else 0
