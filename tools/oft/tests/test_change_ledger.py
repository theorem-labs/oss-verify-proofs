"""change_ledger.py (oft change-ledger): what one change cost, summed from the records that hold it: the tagged agent
sessions' transcripts (tokens, cost, agent hours), the VM samples (vCPU hours), the time logs of its checks, and git
(proof lines, function classes, contracts, and each rewritten proof line's class).  A number comes from a source that
was read; a source that could not be read is written as not measured, never as zero."""
import contextlib
import csv
import datetime
import io
import json
import os
import subprocess
import sys
import tempfile
import unittest
import unittest.mock

from oft import __main__ as oft_main
from oft import change_ledger, keys, paths, prove, release_tree
from oft.tests.helpers import tree
from oft.tests.test_contracts import ENTRY, LIB, STATE, TABLE, contract_repo, put_row
from oft.tests.test_keys import UNIT, commit

T0 = datetime.datetime(2026, 10, 31, 10, 0, 0, tzinfo=datetime.timezone.utc)


def at(minutes, seconds=0):
    """The transcript timestamp minutes (and seconds) after T0."""
    return (T0 + datetime.timedelta(minutes=minutes, seconds=seconds)).strftime("%Y-%m-%dT%H:%M:%S.000Z")


def usage(inp, out, read, write, cost):
    return {"input": inp, "output": out, "cacheRead": read, "cacheWrite": write,
            "totalTokens": inp + out + read + write, "cost": {"total": cost}}


def assistant(minutes, use, seconds=0, model=("anthropic", "claude-opus-5-5"), id=None):
    """An assistant turn; with id, the entry id omp gives it (a resume that copies the history keeps it)."""
    return dict({"type": "message", "timestamp": at(minutes, seconds),
                 "message": {"role": "assistant", "provider": model[0], "model": model[1], "usage": use,
                             "stopReason": "toolUse"}}, **({"id": id} if id else {}))


def tool_result(minutes, seconds=0):
    return {"type": "message", "timestamp": at(minutes, seconds), "message": {"role": "toolResult"}}


def user(minutes):
    return {"type": "message", "timestamp": at(minutes), "message": {"role": "user"}}


def side_call(minutes, use):
    """omp's own call for the session (a task-completion probe): a model_usage entry."""
    return {"type": "model_usage", "timestamp": at(minutes), "purpose": "task-completion-probe",
            "provider": "anthropic", "model": "claude-opus-5-5", "usage": use}


def write_transcript(path, session, entries, start=0, tail=b""):
    """A stand-in omp transcript: its session entry at start minutes, then entries, one JSON object per line."""
    lines = [{"type": "session", "version": 3, "id": session, "timestamp": at(start), "cwd": "/w"},
             {"type": "session_init", "timestamp": at(start), "resolvedModel": "openai-codex/gpt-5.6-terra:xhigh"}]
    with open(path, "wb") as f:
        f.write("".join(json.dumps(e) + "\n" for e in lines + entries).encode())
        f.write(tail)
    return path


def rows(root, change, name="ledger.tsv"):
    with open(os.path.join(root, "changes", change, name), encoding="utf-8", newline="") as f:
        return list(csv.DictReader(f, delimiter="\t"))


def by_step(root, change):
    return {r["step"]: r for r in rows(root, change)}


def run(*argv):
    """`oft ARGV`: (exit status, what it printed)."""
    out = io.StringIO()
    with contextlib.redirect_stdout(out):
        rc = oft_main.main(list(argv))
    return rc, out.getvalue()


@contextlib.contextmanager
def scratch():
    with tempfile.TemporaryDirectory() as d:
        yield d


class Sessions(unittest.TestCase):
    """The agent columns come only from the tagged transcripts: each usage and each turn counts once, in the one step
    of the one change its session is tagged in, from its own transcript; what a transcript does not hold (a lost tail,
    a missing timestamp or usage field) is `+ not measured`, never 0, and gaps.tsv says why."""

    def test_tokens_and_cost_sum_over_tagged_sessions(self):
        """Each assistant turn's message.usage and each omp side call's usage (a model_usage entry) count, per step
        and in total; the ledger's columns are the plan's, in its order."""
        with scratch() as d:
            one = write_transcript(os.path.join(d, "One.jsonl"), "s-one", [
                user(0.5), assistant(1, usage(10, 100, 1000, 50, 0.25)), tool_result(1.5),
                assistant(2, usage(5, 50, 2000, 0, 0.125)), side_call(2.5, usage(1, 2, 3, 4, 0.0625))])
            two = write_transcript(os.path.join(d, "Two.jsonl"), "s-two", [
                assistant(11, usage(7, 70, 700, 70, 0.5))], start=10)
            for step, session, path in (("implement", "s-one", one), ("review", "s-two", two)):
                rc, out = run("--root", d, "change-ledger", "tag", "c", "--step", step, "--session", session,
                              "--host", "box", "--transcript", path)
                self.assertEqual(rc, 0, out)
            rc, out = run("--root", d, "change-ledger", "sum", "c")
            self.assertEqual(rc, 0, out)
            with open(os.path.join(d, "changes", "c", "ledger.tsv"), encoding="utf-8") as f:
                self.assertEqual(f.readline().rstrip("\n").split("\t"), list(change_ledger.COLUMNS))
            got = {s: tuple(r[k] for k in ("sessions", "wall_start", "wall_end", "input_tokens", "output_tokens",
                                           "cache_read", "cache_write", "cost_usd"))
                   for s, r in by_step(d, "c").items()}
            self.assertEqual(got, {
                "implement": ("1", "2026-10-31T10:00:00Z", "2026-10-31T10:02:30Z", "16", "152", "3003", "54",
                              "0.4375"),
                "review": ("1", "2026-10-31T10:10:00Z", "2026-10-31T10:11:00Z", "7", "70", "700", "70", "0.5000"),
                "total": ("2", "2026-10-31T10:00:00Z", "2026-10-31T10:11:00Z", "23", "222", "3703", "124",
                          "0.9375")})
            served = {r["session"]: (r["requested"], r["served"]) for r in rows(d, "c", "session-totals.tsv")}
            self.assertEqual(served, {"s-one": ("openai-codex/gpt-5.6-terra:xhigh", "anthropic/claude-opus-5-5 x2"),
                                      "s-two": ("openai-codex/gpt-5.6-terra:xhigh", "anthropic/claude-opus-5-5 x1")})

    def test_agent_hours_leave_out_long_gaps(self):
        """An assistant turn's time runs from the entry before it to its own timestamp; a turn of exactly 10 minutes
        counts, one of 10 minutes and 1 second is left out."""
        with scratch() as d:
            path = write_transcript(os.path.join(d, "A.jsonl"), "s-a", [
                user(1), assistant(3, usage(1, 1, 0, 0, 0.01)), tool_result(4),
                assistant(14, usage(1, 1, 0, 0, 0.01)), tool_result(15),
                assistant(25, usage(1, 1, 0, 0, 0.01), seconds=1)])
            change_ledger.tag(d, "c", "implement", "s-a", "box", path)
            change_ledger.summarize(d, "c")
            self.assertEqual({s: r["agent_hours"] for s, r in by_step(d, "c").items()},
                             {"implement": "0.20", "total": "0.20"})

    def test_a_turn_whose_timestamps_are_missing_is_not_measured(self):
        """A turn's time needs its own timestamp and that of the entry just before it: when either is missing, or the
        turn is timed before that entry, the turn is not measured (never 0, and never measured from an older entry),
        and gaps.tsv says so."""
        untimed_result = {"type": "message", "message": {"role": "toolResult"}}
        untimed_turn = assistant(9, usage(1, 1, 0, 0, 0.01))
        del untimed_turn["timestamp"]
        with scratch() as d:
            path = write_transcript(os.path.join(d, "T.jsonl"), "s-t", [
                user(1), assistant(2, usage(1, 1, 0, 0, 0.01)), untimed_result,
                assistant(4, usage(1, 1, 0, 0, 0.01)), tool_result(5), untimed_turn, tool_result(20),
                assistant(19, usage(1, 1, 0, 0, 0.01))])
            change_ledger.tag(d, "c", "implement", "s-t", "box", path)
            change_ledger.summarize(d, "c")
            # only the turn at minute 2 is measured: 1 minute
            self.assertEqual(by_step(d, "c")["total"]["agent_hours"], "0.02 + not measured")
            whats = [g["what"] for g in rows(d, "c", "gaps.tsv") if g["column"] == "agent_hours"]
            self.assertEqual(len(whats), 3, whats)

    def test_a_missing_transcript_is_a_named_error(self):
        """A tagged transcript that is gone stops the sum with its path named, and writes no ledger: its tokens are
        not zero.  Tagging a transcript that does not exist is refused too."""
        with scratch() as d:
            path = write_transcript(os.path.join(d, "Gone.jsonl"), "s-gone", [assistant(1, usage(1, 1, 1, 1, 1.0))])
            change_ledger.tag(d, "c", "implement", "s-gone", "box", path)
            os.remove(path)
            with self.assertRaises(change_ledger.LedgerError) as e:
                change_ledger.summarize(d, "c")
            self.assertIn(path, str(e.exception))
            self.assertIn("transcript", str(e.exception))
            self.assertFalse(os.path.exists(os.path.join(d, "changes", "c", "ledger.tsv")))
            rc, out = run("--root", d, "change-ledger", "sum", "c")
            self.assertEqual((rc, out.startswith("FAIL oft change-ledger: "), path in out), (1, True, True))
            with self.assertRaises(change_ledger.LedgerError) as e:
                change_ledger.tag(d, "c", "review", "s-other", "box", os.path.join(d, "Never.jsonl"))
            self.assertIn(os.path.join(d, "Never.jsonl"), str(e.exception))

    def test_a_transcript_cut_by_a_crash_counts_what_it_holds_and_names_what_it_lost(self):
        """A machine that crashes leaves a transcript whose tail is zero bytes or half a line: the lines before it
        count, each agent column says the rest is not measured, and gaps.tsv names the transcript.  A broken line
        anywhere else is an error."""
        for tail in (b"\0" * 482, b'{"type":"message","timestamp":"2026-10-31T10:0'):
            with self.subTest(tail=tail[:8]), scratch() as d:
                path = write_transcript(os.path.join(d, "Cut.jsonl"), "s-cut",
                                        [assistant(1, usage(3, 4, 5, 6, 0.5))], tail=tail)
                change_ledger.tag(d, "c", "implement", "s-cut", "box", path)
                change_ledger.summarize(d, "c")
                row = by_step(d, "c")["implement"]
                self.assertEqual((row["input_tokens"], row["cost_usd"], row["agent_hours"]),
                                 ("3 + not measured", "0.5000 + not measured", "0.02 + not measured"))
                gaps = [(g["session"], g["column"]) for g in rows(d, "c", "gaps.tsv")]
                self.assertIn(("s-cut", "input_tokens"), gaps)
        with scratch() as d:
            path = write_transcript(os.path.join(d, "Bad.jsonl"), "s-bad", [assistant(1, usage(1, 1, 1, 1, 1.0))])
            change_ledger.tag(d, "c", "implement", "s-bad", "box", path)
            with open(path, "a") as f:
                f.write("{broken\n" + json.dumps(assistant(2, usage(1, 1, 1, 1, 1.0))) + "\n")
            with self.assertRaises(change_ledger.LedgerError) as e:
                change_ledger.summarize(d, "c")
            self.assertIn("%s:4" % path, str(e.exception))

    def test_the_records_write_the_home_folder_as_a_tilde(self):
        """No file the ledger writes names the home folder: a transcript, a check log and a sample file under it are
        recorded as ~/..., in gaps.tsv too."""
        with scratch() as d, unittest.mock.patch.dict(os.environ, {"HOME": d}):
            path = write_transcript(os.path.join(d, "Cut.jsonl"), "s-cut", [assistant(1, {"input": 1})],
                                    tail=b"\0" * 8)
            log = os.path.join(d, "check.time")
            with open(log, "w") as f:
                f.write(ELAPSED % "1:00")
            samples = os.path.join(d, "samples.tsv")
            with open(samples, "w") as f:
                f.write(SAMPLES)
            root = os.path.join(d, "repo")
            change_ledger.tag(root, "c", "implement", "s-cut", "box", path)
            change_ledger.check(root, "c", "implement", log)
            change_ledger.summarize(root, "c", samples=[samples])
            folder = os.path.join(root, "changes", "c")
            for name in sorted(os.listdir(folder)):
                with self.subTest(name=name), open(os.path.join(folder, name), encoding="utf-8") as f:
                    self.assertNotIn(d, f.read())
            self.assertIn("~/Cut.jsonl", " ".join(g["what"] for g in rows(root, "c", "gaps.tsv")))

    def test_a_session_is_tagged_once_and_only_with_its_own_transcript(self):
        """A session counts in one step of one change, so its cost is never summed twice; the transcript must be the
        session's own."""
        with scratch() as d:
            path = write_transcript(os.path.join(d, "S.jsonl"), "s-1", [assistant(1, usage(1, 1, 1, 1, 1.0))])
            change_ledger.tag(d, "a", "implement", "s-1", "box", path)
            for change, step in (("a", "implement"), ("a", "review"), ("b", "implement")):
                with self.subTest(change=change, step=step), self.assertRaises(change_ledger.LedgerError) as e:
                    change_ledger.tag(d, change, step, "s-1", "box", path)
                self.assertIn("s-1 is already tagged", str(e.exception))
            with self.assertRaises(change_ledger.LedgerError) as e:
                change_ledger.tag(d, "b", "implement", "s-2", "box", path)
            self.assertIn("s-1", str(e.exception))
            self.assertEqual(len(rows(d, "a", "sessions.tsv")), 1)

    def test_the_sum_checks_each_tag_again(self):
        """A transcript may be replaced, and a sessions.tsv edited, after tag: the sum checks again that each
        transcript is its session's own and that each session counts in one step of one change."""
        with scratch() as d:
            path = write_transcript(os.path.join(d, "A.jsonl"), "s-a", [assistant(1, usage(1, 1, 1, 1, 1.0))])
            change_ledger.tag(d, "x", "implement", "s-a", "box", path)
            write_transcript(path, "s-other", [assistant(1, usage(1, 1, 1, 1, 1.0))])
            with self.assertRaises(change_ledger.LedgerError) as e:
                change_ledger.summarize(d, "x")
            self.assertIn("is the transcript of session s-other, not of s-a", str(e.exception))
        with scratch() as d:
            path = write_transcript(os.path.join(d, "A.jsonl"), "s-a", [assistant(1, usage(1, 1, 1, 1, 1.0))])
            change_ledger.tag(d, "x", "implement", "s-a", "box", path)
            os.makedirs(os.path.join(d, "changes", "y"))
            with open(os.path.join(d, "changes", "x", "sessions.tsv")) as f, \
                    open(os.path.join(d, "changes", "y", "sessions.tsv"), "w") as g:
                g.write(f.read())
            for change in ("x", "y"):
                with self.subTest(change=change), self.assertRaises(change_ledger.LedgerError) as e:
                    change_ledger.summarize(d, change)
                self.assertIn("s-a is already tagged", str(e.exception))

    def test_the_fragments_of_one_session_are_one_session(self):
        """A resumed agent writes a second transcript, X-2.jsonl beside X.jsonl, under a new session id or its first
        one: the fragments are one session.  Tag takes the second fragment in the same step and refuses it in another;
        the sum counts it once in `sessions`, and each entry once by its id, so a resume that copies the history
        before it adds nothing twice."""
        with scratch() as d:
            first = write_transcript(os.path.join(d, "X.jsonl"), "s-x", [
                user(0), assistant(6, usage(1, 10, 0, 0, 0.5), id="a1")])
            second = write_transcript(os.path.join(d, "X-2.jsonl"), "s-x2", [
                user(21), assistant(27, usage(2, 20, 0, 0, 0.25), id="a2")], start=20)
            change_ledger.tag(d, "c", "implement", "s-x", "box", first)
            with self.assertRaises(change_ledger.LedgerError) as e:
                change_ledger.tag(d, "c", "review", "s-x2", "box", second)
            self.assertIn("fragment", str(e.exception))
            change_ledger.tag(d, "c", "implement", "s-x2", "box", second)
            change_ledger.summarize(d, "c")
            row = by_step(d, "c")["implement"]
            self.assertEqual((row["sessions"], row["input_tokens"], row["output_tokens"], row["cost_usd"],
                              row["agent_hours"]), ("1", "3", "30", "0.7500", "0.20"))
        with scratch() as d:
            history = [user(0), assistant(6, usage(1, 10, 0, 0, 0.5), id="a1")]
            first = write_transcript(os.path.join(d, "X.jsonl"), "s-x", history)
            second = write_transcript(os.path.join(d, "X-2.jsonl"), "s-x", history + [
                user(21), assistant(27, usage(2, 20, 0, 0, 0.25), id="a2")], start=20)
            change_ledger.tag(d, "c", "implement", "s-x", "box", first)
            change_ledger.tag(d, "c", "implement", "s-x", "box", second)
            change_ledger.summarize(d, "c")
            row = by_step(d, "c")["implement"]
            self.assertEqual((row["sessions"], row["input_tokens"], row["output_tokens"], row["cost_usd"],
                              row["agent_hours"]), ("1", "3", "30", "0.7500", "0.20"))


def walk(d):
    """A session that walked two upstream commits: turns at minutes 1 and 3 for the first, 11 and 13 for the second;
    the path of its transcript."""
    return write_transcript(os.path.join(d, "Walk.jsonl"), "s-walk", [
        user(0), assistant(1, usage(1, 10, 0, 0, 0.5)), tool_result(2), assistant(3, usage(2, 20, 0, 0, 0.25)),
        user(10), assistant(11, usage(4, 40, 0, 0, 0.125)), tool_result(12), assistant(13, usage(8, 80, 0, 0, 0.0625))])


class Windows(unittest.TestCase):
    """A session that worked on several steps or changes is tagged once for each, each tag with a window, no two of
    one session overlapping: each transcript entry counts in the one tag whose window holds it, so the tags' figures
    add up to the session's, never more; a tag that could count an entry twice is refused."""

    def test_a_session_tagged_to_two_changes_counts_each_entry_once(self):
        """Tagged to change a until 10:05 and to change b from 10:05, each change sums only its window's turns, with
        its window's wall time, and the two sum to the whole session's figures; session-totals.tsv shows each tag's
        window."""
        with scratch() as d:
            path = walk(d)
            for change, window in (("a", ["--until", at(5)]), ("b", ["--from", "2026-10-31T11:05:00+01:00"])):
                rc, out = run("--root", d, "change-ledger", "tag", change, "--step", "walk", "--session", "s-walk",
                              "--host", "box", "--transcript", path, *window)
                self.assertEqual(rc, 0, out)
                change_ledger.summarize(d, change)
            got = {c: tuple(by_step(d, c)["total"][k] for k in ("sessions", "wall_start", "wall_end", "input_tokens",
                                                                 "output_tokens", "cost_usd", "agent_hours"))
                   for c in ("a", "b")}
            self.assertEqual(got, {"a": ("1", "2026-10-31T10:00:00Z", "2026-10-31T10:03:00Z", "3", "30", "0.7500",
                                         "0.03"),
                                   "b": ("1", "2026-10-31T10:10:00Z", "2026-10-31T10:13:00Z", "12", "120", "0.1875",
                                         "0.03")})
            self.assertEqual([(r["from"], r["until"]) for c in ("a", "b") for r in rows(d, c, "session-totals.tsv")],
                             [("-", "2026-10-31T10:05:00Z"), ("2026-10-31T10:05:00Z", "-")])
            self.assertEqual([r for c in ("a", "b") for r in rows(d, c, "gaps.tsv") if r["session"] != "-"], [])

    def test_a_session_tagged_to_two_steps_of_one_change_counts_once_in_the_total(self):
        """The same transcript tagged in two steps of one change, with windows apart: each step sums its window, and
        the total counts the session once and each entry once."""
        with scratch() as d:
            path = walk(d)
            change_ledger.tag(d, "c", "one", "s-walk", "box", path, until=at(5))
            change_ledger.tag(d, "c", "two", "s-walk", "box", path, since=at(5))
            change_ledger.summarize(d, "c")
            got = {s: (r["sessions"], r["input_tokens"], r["cost_usd"]) for s, r in by_step(d, "c").items()}
            self.assertEqual(got, {"one": ("1", "3", "0.7500"), "two": ("1", "12", "0.1875"),
                                   "total": ("1", "15", "0.9375")})

    def test_a_tag_that_could_count_an_entry_twice_is_refused(self):
        """With no window beside another tag of the session, with windows that overlap, or with a window that holds
        no moment or no entry, tag refuses and says how to share a session; the sum checks the windows again."""
        with scratch() as d:
            path = walk(d)
            change_ledger.tag(d, "a", "walk", "s-walk", "box", path, until=at(5))
            refused = {"no window": dict(), "overlapping": dict(since=at(4)), "until before from":
                       dict(since=at(12), until=at(11)), "holds no entry": dict(since=at(20)),
                       "no time zone": dict(since="2026-10-31T10:06:00")}
            for what, window in refused.items():
                with self.subTest(what), self.assertRaises(change_ledger.LedgerError) as e:
                    change_ledger.tag(d, "b", "walk", "s-walk", "box", path, **window)
                if what in ("no window", "overlapping"):
                    self.assertIn("s-walk is already tagged", str(e.exception))
                    self.assertIn("--from, --until", str(e.exception))
            self.assertFalse(os.path.exists(os.path.join(d, "changes", "b", "sessions.tsv")))
            change_ledger.tag(d, "b", "walk", "s-walk", "box", path, since=at(5))
            sessions = os.path.join(d, "changes", "b", "sessions.tsv")
            with open(sessions) as f:
                text = f.read()
            with open(sessions, "w") as f:
                f.write(text.replace("2026-10-31T10:05:00Z", "2026-10-31T10:04:00Z"))
            for change in ("a", "b"):
                with self.subTest(change=change), self.assertRaises(change_ledger.LedgerError) as e:
                    change_ledger.summarize(d, change)
                self.assertIn("s-walk is already tagged", str(e.exception))

    def test_with_a_window_a_usage_with_no_timestamp_is_not_measured(self):
        """No window can be said to hold a usage with no timestamp: in a tag with a window it makes each agent
        figure `+ not measured`, and gaps.tsv says why, rather than counting it in every window or in none."""
        with scratch() as d:
            lost = assistant(2, usage(100, 100, 0, 0, 9.0))
            del lost["timestamp"]
            path = write_transcript(os.path.join(d, "L.jsonl"), "s-l", [
                user(0), assistant(1, usage(1, 10, 0, 0, 0.5)), lost])
            change_ledger.tag(d, "c", "walk", "s-l", "box", path, until=at(5))
            change_ledger.summarize(d, "c")
            row = by_step(d, "c")["walk"]
            self.assertEqual((row["input_tokens"], row["cost_usd"]), ("1 + not measured", "0.5000 + not measured"))
            self.assertIn("a usage in %s has no timestamp: no window can be said to hold it" % path,
                          [g["what"] for g in rows(d, "c", "gaps.tsv")])


SAMPLES = ("time\tvm\tzone\ttype\tload15\tcontainers\n"
           + "".join("2026-10-31T%s:00Z\tossv-x\tus-central1-a\tn2-highmem-32\t1.0\t1\n" % hm
                     for hm in ("10:00", "10:10", "10:20", "10:30", "10:40", "10:50", "11:00", "11:50")))
IDLE_HEADER = ("run_ts\tvm\tzone\tmachine_type\tcreated\tlast_start\towner\tlast_container_end\tload15\tverdict\t"
               "reason\n")


def idle_row(at, start, vm="ossv-x", kind="n2-highmem-32"):
    """A row of notes/idle-stop.tsv: a sample at `at` of vm, whose life began at `start` (HH:MM, or HH:MM:SS for the
    start, of 2026-10-31)."""
    start += "" if start.count(":") == 2 else ":00"
    return "2026-10-31T%s:00Z\t%s\tus-central1-a\t%s\t2026-10-31T%sZ\t2026-10-31T%sZ\tsomeone\tnever\t1.0\t" \
           "keep\t-\n" % (at, vm, kind, start, start)


def write_samples(d, header, lines, name="samples.tsv"):
    """A VM sample file under d with header and lines; its path."""
    path = os.path.join(d, name)
    with open(path, "w") as f:
        f.write(header + "".join(lines))
    return path


class Machines(unittest.TestCase):
    """vcpu_hours comes only from VM samples (and recorded deletions) inside the sessions' spans: every interval it
    counts is one a machine ran in one life, and every part of a span in which a machine may have run without a
    measurement is named in gaps.tsv and makes the figure `+ not measured`, or `not measured` when nothing was."""

    def test_vcpu_hours_come_from_the_samples_of_each_machine_in_the_session_span(self):
        """vCPU hours: the samples of the session's host and of each VM it names, between consecutive samples under
        45 minutes apart (as bin/ossv-stream-numbers counts them), times the vCPUs of the machine type, inside the
        session's span.  A machine with no sample there is not measured, and gaps.tsv names it; with no sample file
        nothing is measured."""
        with scratch() as d:
            samples = os.path.join(d, "compute-ledger.tsv")
            with open(samples, "w") as f:
                f.write(SAMPLES)
            # the session spans 10:15 to 10:45: 30 minutes of a 32-vCPU VM
            path = write_transcript(os.path.join(d, "V.jsonl"), "s-v", [assistant(45, usage(1, 1, 1, 1, 0.1))],
                                    start=15)
            change_ledger.tag(d, "vm", "implement", "s-v", "box", path, vms=["ossv-x"])
            change_ledger.summarize(d, "vm", samples=[samples])
            self.assertEqual(by_step(d, "vm")["implement"]["vcpu_hours"], "16.00 + not measured")
            self.assertIn(("vcpu_hours", "box"), [(g["column"], g["what"].split(":")[0])
                                                  for g in rows(d, "vm", "gaps.tsv")])
            self.assertEqual([(r["input"], os.path.expanduser(r["value"])) for r in rows(d, "vm", "inputs.tsv")
                              if r["input"] in ("unit", "vm_samples")], [("unit", "-"), ("vm_samples", samples)])
            path2 = write_transcript(os.path.join(d, "W.jsonl"), "s-w", [assistant(45, usage(1, 1, 1, 1, 0.1))],
                                     start=15)
            change_ledger.tag(d, "host", "implement", "s-w", "ossv-x", path2)
            change_ledger.summarize(d, "host", samples=[samples])
            self.assertEqual(by_step(d, "host")["total"]["vcpu_hours"], "16.00")
            change_ledger.summarize(d, "host")
            self.assertEqual(by_step(d, "host")["total"]["vcpu_hours"], "not measured")

    def test_a_vm_deleted_and_made_again_is_two_lives(self):
        """notes/idle-stop.tsv gives each sample its VM's creation and last start (GCE's): two samples of different
        lives never make an interval, even under 45 minutes apart (the VM was gone between them), and a life counts
        from its last start, not from its first sample.  The time after each life's last sample is not measured."""
        with scratch() as d:
            samples = write_samples(d, IDLE_HEADER, [idle_row("10:10", "10:02"), idle_row("10:20", "10:02"),
                                                     idle_row("10:45", "10:40"), idle_row("10:55", "10:40")])
            path = write_transcript(os.path.join(d, "L.jsonl"), "s-l", [assistant(60, usage(1, 1, 1, 1, 0.1))])
            change_ledger.tag(d, "c", "implement", "s-l", "ossv-x", path)
            change_ledger.summarize(d, "c", samples=[samples])
            # 10:02 to 10:20, then 10:40 to 10:55: 33 minutes of 32 vCPUs
            self.assertEqual(by_step(d, "c")["total"]["vcpu_hours"], "17.60 + not measured")

    def test_a_sample_of_no_known_life_never_joins_two_lives(self):
        """A compute-ledger.tsv sample names no life: it takes the life of the latest start at or before it (from
        idle-stop.tsv), so it never makes an interval across the start of another life, and inside a life it is one
        more sample of that life."""
        with scratch() as d:
            idle = write_samples(d, IDLE_HEADER, [idle_row("10:10", "10:02"), idle_row("10:45", "10:40")],
                                 name="idle-stop.tsv")
            ledger = write_samples(d, SAMPLES.split("\n")[0] + "\n",
                                   ["2026-10-31T10:30:00Z\tossv-x\tus-central1-a\tn2-highmem-32\t1.0\t1\n"],
                                   name="compute-ledger.tsv")
            path = write_transcript(os.path.join(d, "R.jsonl"), "s-r", [assistant(60, usage(1, 1, 1, 1, 0.1))])
            change_ledger.tag(d, "c", "implement", "s-r", "ossv-x", path)
            change_ledger.summarize(d, "c", samples=[ledger, idle])
            # life A from 10:02 to its last sample at 10:30 (the compute-ledger one), life B from 10:40 to 10:45
            self.assertEqual(by_step(d, "c")["total"]["vcpu_hours"], "17.60 + not measured")
            self.assertIn("ossv-x: not measured from 2026-10-31T10:30:00Z to 2026-10-31T10:40:00Z: after its last "
                          "sample, and no deletion record after it",
                          [g["what"] for g in rows(d, "c", "gaps.tsv")])
        with scratch() as d:
            idle = write_samples(d, IDLE_HEADER, [idle_row("10:10", "10:02"), idle_row("10:40", "10:02")],
                                 name="idle-stop.tsv")
            ledger = write_samples(d, SAMPLES.split("\n")[0] + "\n",
                                   ["2026-10-31T10:30:00Z\tossv-x\tus-central1-a\tn2-highmem-32\t1.0\t1\n"],
                                   name="compute-ledger.tsv")
            path = write_transcript(os.path.join(d, "I.jsonl"), "s-i", [assistant(40, usage(1, 1, 1, 1, 0.1))])
            change_ledger.tag(d, "c", "implement", "s-i", "ossv-x", path)
            change_ledger.summarize(d, "c", samples=[ledger, idle])
            # one life from 10:02 to 10:40, with no gap at the compute-ledger sample: 38 minutes of 32 vCPUs
            self.assertEqual(by_step(d, "c")["total"]["vcpu_hours"], "20.27")

    def test_a_resumed_fragment_spans_only_its_own_entries(self):
        """A resumed fragment that copies the history before it spans only its own new entries: the copied ones (omp
        gives every entry an id), which count in no sum, widen neither its wall time nor the span of its machines."""
        with scratch() as d:
            samples = write_samples(d, SAMPLES.split("\n")[0] + "\n", [
                "2026-10-31T%s:00Z\tossv-b\tus-central1-a\tn2-highmem-32\t1.0\t1\n" % hm
                for hm in ("10:00", "10:10", "10:20", "10:30", "10:40")])
            history = [dict(user(0), id="u1"), assistant(6, usage(1, 10, 0, 0, 0.5), id="a1")]
            first = write_transcript(os.path.join(d, "X.jsonl"), "s-x", history)
            second = write_transcript(os.path.join(d, "X-2.jsonl"), "s-x2", history + [
                user(21), assistant(30, usage(2, 20, 0, 0, 0.25), id="a2")], start=20)
            change_ledger.tag(d, "c", "implement", "s-x", "box-a", first)
            change_ledger.tag(d, "c", "implement", "s-x2", "ossv-b", second)
            change_ledger.summarize(d, "c", samples=[samples])
            # ossv-b ran for the second fragment from 10:20 to 10:30 only; box-a has no sample
            self.assertEqual(by_step(d, "c")["total"]["vcpu_hours"], "5.33 + not measured")
            spans = {r["session"]: (r["wall_start"], r["wall_end"]) for r in rows(d, "c", "session-totals.tsv")}
            self.assertEqual(spans, {"s-x": ("2026-10-31T10:00:00Z", "2026-10-31T10:06:00Z"),
                                     "s-x2": ("2026-10-31T10:20:00Z", "2026-10-31T10:30:00Z")})

    def test_vm_time_with_no_measurement_is_named_and_a_recorded_deletion_ends_a_life(self):
        """Each part of a session's span in which a machine may have run with no measurement is named in gaps.tsv,
        and the measured subtotal stays: a gap of 45 minutes or more between samples, the time after a life's last
        sample, an interval whose machine type names no vCPU count.  A deletion that the compute inventory records
        (gone=, from bin/ossv-vm) ends a life: less than 45 minutes after its last sample, the tail up to it counts;
        later, the tail up to it is not measured, and after it the VM is gone."""
        def vm_gaps(d):
            return [g["what"] for g in rows(d, "c", "gaps.tsv") if g["column"] == "vcpu_hours" and g["step"] == "total"]
        with scratch() as d:
            samples = write_samples(d, IDLE_HEADER, [idle_row("10:10", "10:00"), idle_row("10:20", "10:00")])
            path = write_transcript(os.path.join(d, "D.jsonl"), "s-d", [assistant(60, usage(1, 1, 1, 1, 0.1))])
            change_ledger.tag(d, "c", "implement", "s-d", "ossv-x", path)
            change_ledger.summarize(d, "c", samples=[samples])
            # 10:00 to 10:20 measured; 10:20 to 11:00 the VM may have run on
            self.assertEqual(by_step(d, "c")["total"]["vcpu_hours"], "10.67 + not measured")
            self.assertEqual(vm_gaps(d), ["ossv-x: not measured from 2026-10-31T10:20:00Z to 2026-10-31T11:00:00Z: "
                                          "after its last sample, and no deletion record after it"])
            inventory = os.path.join(d, "compute-inventory.csv")
            with open(inventory, "w") as f:
                f.write('example-project,ossv-x,us-central1-a,n2-highmem-32,DELETED,10-31T10:00Z,'
                        '"owner=someone,gone=10-31T10:28Z"\n')
            change_ledger.summarize(d, "c", samples=[samples], deletions=[inventory])
            # 10:00 to the deletion at 10:28: 28 minutes of 32 vCPUs
            self.assertEqual((by_step(d, "c")["total"]["vcpu_hours"], vm_gaps(d)), ("14.93", []))
            self.assertIn(("vm_deletions", inventory), [(r["input"], os.path.expanduser(r["value"]))
                                                        for r in rows(d, "c", "inputs.tsv")])
        with scratch() as d:
            samples = write_samples(d, IDLE_HEADER, [idle_row("10:10", "10:00"), idle_row("10:20", "10:00")])
            inventory = os.path.join(d, "compute-inventory.csv")
            with open(inventory, "w") as f:
                f.write('example-project,ossv-x,us-central1-a,n2-highmem-32,DELETED,10-31T10:00Z,'
                        '"owner=someone,gone=10-31T11:10Z"\n')
            path = write_transcript(os.path.join(d, "E.jsonl"), "s-e", [assistant(90, usage(1, 1, 1, 1, 0.1))])
            change_ledger.tag(d, "c", "implement", "s-e", "ossv-x", path)
            change_ledger.summarize(d, "c", samples=[samples], deletions=[inventory])
            # deleted 50 minutes after the last sample: up to 11:10 not measured, then gone until the span's end
            self.assertEqual((by_step(d, "c")["total"]["vcpu_hours"], vm_gaps(d)),
                             ("10.67 + not measured", ["ossv-x: not measured from 2026-10-31T10:20:00Z to "
                                                       "2026-10-31T11:10:00Z: after its last sample, until its "
                                                       "recorded deletion"]))
        for kinds, end, want, why in (
                (("n2-highmem-32",) * 2 + (None,) * 4 + ("n2-highmem-32",), 60, "5.33 + not measured",
                 "from 2026-10-31T10:10:00Z to 2026-10-31T11:00:00Z: no sample for 50 minutes"),
                (("n2-highmem-32", "e2-medium", "n2-highmem-32"), 20, "5.33 + not measured",
                 "from 2026-10-31T10:10:00Z to 2026-10-31T10:20:00Z: its machine type e2-medium names no vCPU count")):
            with self.subTest(why=why), scratch() as d:
                times = ("10:00", "10:10", "10:20", "10:30", "10:40", "10:50", "11:00")
                samples = write_samples(d, SAMPLES.split("\n")[0] + "\n", [
                    "2026-10-31T%s:00Z\tossv-x\tus-central1-a\t%s\t1.0\t1\n" % (hm, kind)
                    for hm, kind in zip(times, kinds) if kind])
                path = write_transcript(os.path.join(d, "G.jsonl"), "s-g", [assistant(end, usage(1, 1, 1, 1, 0.1))])
                change_ledger.tag(d, "c", "implement", "s-g", "ossv-x", path)
                change_ledger.summarize(d, "c", samples=[samples])
                self.assertEqual(by_step(d, "c")["total"]["vcpu_hours"], want)
                self.assertEqual(vm_gaps(d), ["ossv-x: not measured " + why])

    def test_a_recorded_deletion_is_a_boundary(self):
        """A deletion ends the life it falls in: a compute-ledger sample after it does not take that life, no
        interval crosses it, and the time from it to that sample is not measured (a life of no known start began
        then).  Samples of that later life measure the time between them, as any compute-ledger samples do."""
        def vm_gaps(d):
            return [g["what"] for g in rows(d, "c", "gaps.tsv") if g["column"] == "vcpu_hours" and g["step"] == "total"]
        for later, want, gaps in (
                (("10:20",), "8.00 + not measured",
                 ["from 2026-10-31T10:15:00Z to 2026-10-31T10:20:00Z: after its recorded deletion, before its next "
                  "sample", "from 2026-10-31T10:20:00Z to 2026-10-31T10:30:00Z: after its last sample, and no "
                  "deletion record after it"]),
                (("10:20", "10:25"), "10.67 + not measured",
                 ["from 2026-10-31T10:15:00Z to 2026-10-31T10:20:00Z: after its recorded deletion, before its next "
                  "sample", "from 2026-10-31T10:25:00Z to 2026-10-31T10:30:00Z: after its last sample, and no "
                  "deletion record after it"])):
            with self.subTest(later=later), scratch() as d:
                idle = write_samples(d, IDLE_HEADER, [idle_row("10:00", "10:00"), idle_row("10:10", "10:00")],
                                     name="idle-stop.tsv")
                ledger = write_samples(d, SAMPLES.split("\n")[0] + "\n", [
                    "2026-10-31T%s:00Z\tossv-x\tus-central1-a\tn2-highmem-32\t1.0\t1\n" % hm for hm in later],
                    name="compute-ledger.tsv")
                inventory = os.path.join(d, "compute-inventory.csv")
                with open(inventory, "w") as f:
                    f.write('example-project,ossv-x,us-central1-a,n2-highmem-32,DELETED,10-31T10:00Z,'
                            '"owner=someone,gone=10-31T10:15Z"\n')
                path = write_transcript(os.path.join(d, "B.jsonl"), "s-b", [assistant(30, usage(1, 1, 1, 1, 0.1))])
                change_ledger.tag(d, "c", "implement", "s-b", "ossv-x", path)
                change_ledger.summarize(d, "c", samples=[idle, ledger], deletions=[inventory])
                # the known life from 10:00 to its deletion at 10:15: 15 minutes of 32 vCPUs (and 10:20-10:25)
                self.assertEqual(by_step(d, "c")["total"]["vcpu_hours"], want)
                self.assertEqual(vm_gaps(d), ["ossv-x: not measured " + g for g in gaps])

    def test_every_stretch_no_record_measures_is_named_and_never_reads_0(self):
        """Between two recorded deletions with no start or sample between them a life no sample shows ran: that
        stretch is not measured.  A span that holds no measured interval reads `not measured`, never 0.00, and
        gaps.tsv says why, even where the records show the VM gone."""
        def vm_gaps(d):
            return [g["what"] for g in rows(d, "c", "gaps.tsv") if g["column"] == "vcpu_hours" and g["step"] == "total"]
        for start, end, want, gaps in (
                (16, 17, "not measured",
                 ["from 2026-10-31T10:16:00Z to 2026-10-31T10:17:00Z: between two recorded deletions, a life no "
                  "sample shows"]),
                (0, 30, "8.00 + not measured",
                 ["from 2026-10-31T10:15:00Z to 2026-10-31T10:18:00Z: between two recorded deletions, a life no "
                  "sample shows",
                  "from 2026-10-31T10:18:00Z to 2026-10-31T10:20:00Z: after its recorded deletion, before its next "
                  "sample",
                  "from 2026-10-31T10:20:00Z to 2026-10-31T10:30:00Z: after its last sample, and no deletion record "
                  "after it"])):
            with self.subTest(span=(start, end)), scratch() as d:
                idle = write_samples(d, IDLE_HEADER, [idle_row("10:00", "10:00"), idle_row("10:10", "10:00")],
                                     name="idle-stop.tsv")
                ledger = write_samples(d, SAMPLES.split("\n")[0] + "\n",
                                       ["2026-10-31T10:20:00Z\tossv-x\tus-central1-a\tn2-highmem-32\t1.0\t1\n"],
                                       name="compute-ledger.tsv")
                inventory = os.path.join(d, "compute-inventory.csv")
                with open(inventory, "w") as f:
                    f.write('example-project,ossv-x,us-central1-a,n2-highmem-32,DELETED,10-31T10:00Z,'
                            '"owner=someone,gone=10-31T10:15Z,gone=10-31T10:18Z"\n')
                path = write_transcript(os.path.join(d, "S.jsonl"), "s-s", [assistant(end, usage(1, 1, 1, 1, 0.1))],
                                        start=start)
                change_ledger.tag(d, "c", "implement", "s-s", "ossv-x", path)
                change_ledger.summarize(d, "c", samples=[idle, ledger], deletions=[inventory])
                self.assertEqual(by_step(d, "c")["total"]["vcpu_hours"], want)
                self.assertEqual(vm_gaps(d), ["ossv-x: not measured " + g for g in gaps])
        with scratch() as d:
            idle = write_samples(d, IDLE_HEADER, [idle_row("10:00", "10:00"), idle_row("10:10", "10:00")])
            inventory = os.path.join(d, "compute-inventory.csv")
            with open(inventory, "w") as f:
                f.write('example-project,ossv-x,us-central1-a,n2-highmem-32,DELETED,10-31T10:00Z,'
                        '"owner=someone,gone=10-31T10:15Z"\n')
            path = write_transcript(os.path.join(d, "G.jsonl"), "s-g", [assistant(30, usage(1, 1, 1, 1, 0.1))],
                                    start=20)
            change_ledger.tag(d, "c", "implement", "s-g", "ossv-x", path)
            change_ledger.summarize(d, "c", samples=[idle], deletions=[inventory])
            # deleted at 10:15, before the span: no record shows it running, so nothing is measured, never 0.00
            self.assertEqual((by_step(d, "c")["total"]["vcpu_hours"], vm_gaps(d)),
                             ("not measured", ["ossv-x: not measured from 2026-10-31T10:20:00Z to "
                                               "2026-10-31T10:30:00Z: no record shows it running then"]))

    def test_a_deletion_cut_to_the_minute_ends_its_own_life(self):
        """A deletion mark is cut to the minute, so a sample less than a minute after it may still be of the life it
        ends; the start of a life begun after the mark is not, and the mark stays a boundary before it."""
        with scratch() as d:
            idle = write_samples(d, IDLE_HEADER, [idle_row("19:20", "19:10"), idle_row("19:30", "19:10"),
                                                  idle_row("19:45", "19:37:30")])
            inventory = os.path.join(d, "compute-inventory.csv")
            with open(inventory, "w") as f:
                f.write('example-project,ossv-x,us-central1-a,n2-highmem-32,DELETED,10-31T19:10Z,'
                        '"owner=someone,gone=10-31T19:37Z"\n')
            path = write_transcript(os.path.join(d, "M.jsonl"), "s-m", [assistant(590, usage(1, 1, 1, 1, 0.1))],
                                    start=550)
            change_ledger.tag(d, "c", "implement", "s-m", "ossv-x", path)
            change_ledger.summarize(d, "c", samples=[idle], deletions=[inventory])
            # 19:10 to the deletion at 19:37, then the next life from 19:37:30 to 19:45: 34.5 minutes of 32 vCPUs
            self.assertEqual(by_step(d, "c")["total"]["vcpu_hours"], "18.40 + not measured")
            self.assertEqual([g["what"] for g in rows(d, "c", "gaps.tsv") if g["step"] == "total"
                              and g["column"] == "vcpu_hours"],
                             ["ossv-x: not measured from 2026-10-31T19:45:00Z to 2026-10-31T19:50:00Z: after its last "
                              "sample, and no deletion record after it"])

    def test_a_deletion_a_later_sample_of_the_life_contradicts_is_not_its_end(self):
        """A deletion mark of the same name that a later sample of a running life contradicts (another VM of that
        name was deleted) is no boundary of that life."""
        with scratch() as d:
            idle = write_samples(d, IDLE_HEADER, [idle_row(hm, "10:00") for hm in ("10:10", "10:20", "10:30")])
            inventory = os.path.join(d, "compute-inventory.csv")
            with open(inventory, "w") as f:
                f.write('example-project,ossv-x,us-west1-b,n2-highmem-32,DELETED,10-31T09:00Z,'
                        '"owner=someone,gone=10-31T10:15Z"\n')
            path = write_transcript(os.path.join(d, "K.jsonl"), "s-k", [assistant(30, usage(1, 1, 1, 1, 0.1))])
            change_ledger.tag(d, "c", "implement", "s-k", "ossv-x", path)
            change_ledger.summarize(d, "c", samples=[idle], deletions=[inventory])
            # one life from 10:00 to 10:30: 30 minutes of 32 vCPUs
            self.assertEqual(by_step(d, "c")["total"]["vcpu_hours"], "16.00")

    def test_a_machine_type_names_its_vcpus_or_none(self):
        """A machine type names its vCPUs as <series>-<class>-<vcpus>, <series>-custom-<vcpus>-<memory MB>[-ext] or,
        for N1, custom-<vcpus>-<memory MB>; any other form (a shared core, a GPU count, a suffix) names none, so its
        time is not measured, never read as its last number."""
        for kind, vcpus in (("n2-highmem-32", 32), ("n2d-standard-64", 64), ("e2-highcpu-8", 8),
                            ("n2-custom-8-32768", 8), ("n2d-custom-16-65536-ext", 16), ("custom-4-16384", 4),
                            ("e2-medium", None), ("a2-highgpu-1g", None), ("c3-standard-4-lssd", None), ("-", None)):
            with self.subTest(kind=kind):
                self.assertEqual(change_ledger.vcpus_of(kind), vcpus)
        with scratch() as d:
            samples = os.path.join(d, "compute-ledger.tsv")
            with open(samples, "w") as f:
                f.write(SAMPLES.replace("n2-highmem-32", "n2-custom-8-32768"))
            path = write_transcript(os.path.join(d, "C.jsonl"), "s-c", [assistant(45, usage(1, 1, 1, 1, 0.1))],
                                    start=15)
            change_ledger.tag(d, "c", "implement", "s-c", "ossv-x", path)
            change_ledger.summarize(d, "c", samples=[samples])
            # 30 minutes of 8 vCPUs, not of 32768
            self.assertEqual(by_step(d, "c")["total"]["vcpu_hours"], "4.00")


ELAPSED = "\tCommand being timed: \"oft check\"\n\tElapsed (wall clock) time (h:mm:ss or m:ss): %s\n\tExit status: 0\n"


class Checks(unittest.TestCase):
    """check_seconds comes only from GNU time -v logs recorded with `oft change-ledger check`; a step with none is not
    measured, never 0."""

    def test_check_seconds_come_from_the_time_logs_of_the_checks(self):
        """A check is recorded by its GNU time -v log; its seconds are the log's elapsed wall clock time.  A log that
        holds none is refused; a step with no check log is not measured."""
        with scratch() as d:
            logs = []
            for name, elapsed in (("a.time", "2:15:51"), ("b.time", "1:54.99")):
                logs.append(os.path.join(d, name))
                with open(logs[-1], "w") as f:
                    f.write(ELAPSED % elapsed)
            path = write_transcript(os.path.join(d, "C.jsonl"), "s-c", [assistant(1, usage(1, 1, 1, 1, 0.1))])
            change_ledger.tag(d, "c", "implement", "s-c", "box", path)
            for log in logs:
                change_ledger.check(d, "c", "implement", log)
            change_ledger.summarize(d, "c")
            self.assertEqual(by_step(d, "c")["implement"]["check_seconds"], "8265.99")
            empty = os.path.join(d, "empty.time")
            with open(empty, "w") as f:
                f.write("nothing timed\n")
            with self.assertRaises(change_ledger.LedgerError) as e:
                change_ledger.check(d, "c", "implement", empty)
            self.assertIn(empty, str(e.exception))
            path2 = write_transcript(os.path.join(d, "R.jsonl"), "s-r", [assistant(1, usage(1, 1, 1, 1, 0.1))])
            change_ledger.tag(d, "c", "review", "s-r", "box", path2)
            change_ledger.summarize(d, "c")
            got = by_step(d, "c")
            self.assertEqual((got["review"]["check_seconds"], got["total"]["check_seconds"]),
                             ("not measured", "8265.99 + not measured"))


class NoWork(unittest.TestCase):
    """0 is written only where a record says so: a step recorded as needing no work (`oft change-ledger no-work`)
    reads 0 and gaps.tsv names nothing for it, while a step with no record still reads `not measured`; a step that
    needed no work has no session and no check log."""

    def test_a_step_that_needed_no_work_reads_0_and_is_no_gap(self):
        """The upstream commits of a change that change no binary need no proof run: recorded so, the step's and the
        total's agent, VM and check figures are 0, its wall time does not apply, and gaps.tsv is empty, with or
        without VM samples."""
        with scratch() as d:
            rc, out = run("--root", d, "change-ledger", "no-work", "c", "--step", "walk-1",
                          "--why", "oft prove finds no function changed")
            self.assertEqual(rc, 0, out)
            self.assertEqual(rows(d, "c", "no-work.tsv"), [{"step": "walk-1",
                                                            "why": "oft prove finds no function changed"}])
            samples = write_samples(d, SAMPLES, [])
            for given in ([], [samples]):
                with self.subTest(samples=given):
                    change_ledger.summarize(d, "c", samples=given)
                    zero = {"sessions": "0", "wall_start": "-", "wall_end": "-", "agent_hours": "0.00",
                            "input_tokens": "0", "output_tokens": "0", "cache_read": "0", "cache_write": "0",
                            "cost_usd": "0.0000", "vcpu_hours": "0.00", "check_seconds": "0.00"}
                    self.assertEqual({s: {k: r[k] for k in zero} for s, r in by_step(d, "c").items()},
                                     {"walk-1": zero, "total": zero})
                    self.assertEqual(rows(d, "c", "gaps.tsv"), [])

    def test_a_step_with_no_record_still_reads_not_measured(self):
        """Beside a step that needed no work, a step that has only a check log is not measured in its agent and VM
        figures, and so is the total's; a step that did work and one that needed none sum to the first's figures,
        with no `+ not measured` for the step that needed none.  A change with no record reads not measured."""
        with scratch() as d:
            log = os.path.join(d, "a.time")
            with open(log, "w") as f:
                f.write(ELAPSED % "0:10")
            change_ledger.no_work(d, "c", "walk-1", "no binary changed")
            change_ledger.check(d, "c", "walk-2", log)
            change_ledger.summarize(d, "c")
            got = {s: (r["agent_hours"], r["cost_usd"], r["vcpu_hours"], r["check_seconds"])
                   for s, r in by_step(d, "c").items()}
            self.assertEqual(got, {"walk-1": ("0.00", "0.0000", "0.00", "0.00"),
                                   "walk-2": ("not measured", "not measured", "not measured", "10.00"),
                                   "total": ("not measured", "not measured", "not measured", "10.00")})
            self.assertEqual({g["step"] for g in rows(d, "c", "gaps.tsv")}, {"walk-2", "total"})
        with scratch() as d:
            log = os.path.join(d, "a.time")
            with open(log, "w") as f:
                f.write(ELAPSED % "0:10")
            path = write_transcript(os.path.join(d, "W.jsonl"), "s-w", [user(0), assistant(1, usage(1, 1, 0, 0, 0.5))])
            change_ledger.tag(d, "c", "walk-2", "s-w", "box", path)
            change_ledger.check(d, "c", "walk-2", log)
            change_ledger.no_work(d, "c", "walk-1", "no binary changed")
            change_ledger.summarize(d, "c")
            total = by_step(d, "c")["total"]
            self.assertEqual((total["sessions"], total["cost_usd"], total["check_seconds"]), ("1", "0.5000", "10.00"))
        with scratch() as d:
            change_ledger.summarize(d, "c")
            total = by_step(d, "c")["total"]
            self.assertEqual((total["cost_usd"], total["vcpu_hours"], total["check_seconds"]),
                             (change_ledger.NOT_MEASURED,) * 3)

    def test_a_step_that_needed_no_work_has_no_session_and_no_check_log(self):
        """no-work refuses a step with a tagged session or a check log, one recorded already, and a reason that is
        empty or more than one line; tag and check refuse a step recorded as needing no work; and the sum checks a
        no-work.tsv edited after them again."""
        with scratch() as d:
            log = os.path.join(d, "a.time")
            with open(log, "w") as f:
                f.write(ELAPSED % "0:10")
            path = write_transcript(os.path.join(d, "S.jsonl"), "s-1", [assistant(1, usage(1, 1, 1, 1, 1.0))])
            change_ledger.tag(d, "c", "worked", "s-1", "box", path)
            change_ledger.check(d, "c", "checked", log)
            change_ledger.no_work(d, "c", "idle", "no binary changed")
            refused = {"a tagged step": lambda: change_ledger.no_work(d, "c", "worked", "x"),
                       "a checked step": lambda: change_ledger.no_work(d, "c", "checked", "x"),
                       "a step recorded already": lambda: change_ledger.no_work(d, "c", "idle", "x"),
                       "no reason": lambda: change_ledger.no_work(d, "c", "other", " "),
                       "two lines": lambda: change_ledger.no_work(d, "c", "other", "a\nb"),
                       "a tag": lambda: change_ledger.tag(d, "c", "idle", "s-2", "box", write_transcript(
                           os.path.join(d, "T.jsonl"), "s-2", [assistant(1, usage(1, 1, 1, 1, 1.0))])),
                       "a check": lambda: change_ledger.check(d, "c", "idle", log)}
            for what, call in refused.items():
                with self.subTest(what), self.assertRaises(change_ledger.LedgerError):
                    call()
            self.assertEqual(rows(d, "c", "no-work.tsv"), [{"step": "idle", "why": "no binary changed"}])
            with open(os.path.join(d, "changes", "c", "no-work.tsv"), "a") as f:
                f.write("worked\tedited by hand\n")
            with self.assertRaises(change_ledger.LedgerError) as e:
                change_ledger.summarize(d, "c")
            self.assertIn("step worked of c is recorded as needing no work", str(e.exception))


class Journal(unittest.TestCase):
    """journal.md is made from its template once and then belongs to its writers; changes/ is internal maintainers'
    work, and the ledger is not the checker."""

    def test_the_journal_is_made_once_with_every_section(self):
        with scratch() as d:
            change_ledger.summarize(d, "c")
            journal = os.path.join(d, "changes", "c", "journal.md")
            with open(journal, encoding="utf-8") as f:
                text = f.read()
            self.assertEqual([line[3:] for line in text.split("\n") if line.startswith("## ")],
                             list(change_ledger.JOURNAL_SECTIONS))
            with open(journal, "a") as f:
                f.write("Kept.\n")
            change_ledger.summarize(d, "c")
            with open(journal, encoding="utf-8") as f:
                self.assertTrue(f.read().endswith("Kept.\n"))

    def test_changes_are_internal_hand_files(self):
        """changes/ is maintainers' work, and only this repository has it: a release leaves it out."""
        self.assertEqual([c for c, _p, _b in paths.classify("changes/libreac-35/ledger.tsv")], ["hand"])
        self.assertIn("changes/", release_tree.INTERNAL)

    def test_the_change_ledger_is_not_the_checker(self):
        """keys.NOT_THE_CHECKER names change_ledger.py and the journal's template, so a change to them re-checks no
        fuzz target; that holds only while a check opens them not, so oft.check, with oft.facts and oft.fetch, does
        not import it."""
        self.assertTrue(keys.not_the_checker("tools/oft/change_ledger.py"))
        self.assertTrue(keys.not_the_checker("tools/oft/templates/journal.md.tmpl"))
        tools = os.path.dirname(os.path.dirname(os.path.abspath(change_ledger.__file__)))
        done = subprocess.run([sys.executable, "-c", "import sys, oft.check, oft.facts, oft.fetch; "
                               "print('oft.change_ledger' in sys.modules)"],
                              capture_output=True, text=True, env=dict(os.environ, PYTHONPATH=tools))
        self.assertEqual((done.returncode, done.stdout, done.stderr), (0, "False\n", ""))


class Git(unittest.TestCase):
    """The fixture: test_contracts.contract_repo, with a proof file of zlib/checksum_fuzzer's proof library."""

    WALK = LIB + "/Lib/Walk.v"

    def test_edits_are_split_into_address_layout_and_content(self):
        """Each rewritten line pair of the unit's proofs (a hunk's removed and added lines, in order) is an address
        edit when it is equal with its hex literals masked, a layout edit when equal with every number masked, else
        a content edit; the proof lines added and removed are git's numstat; the function classes are oft prove's.
        A Rocq bullet at the start of a line (`--`) is a line like any other."""
        with tree() as t:
            t.write(self.WALK, "Definition A := 0x11000.\nDefinition B := 4096.\nDefinition C := 0x10 + 3.\n"
                               "Lemma l : True. Proof. exact I. Qed.\n-- exact I.\n")
            base = contract_repo(t)
            t.write(self.WALK, "Definition A := 0x11008.\nDefinition B := 4104.\nDefinition C := 0x18 + 4.\n"
                               "Lemma l : True. Proof. trivial. Qed.\n-- exact (I).\nDefinition D := 1.\n")
            head = commit(t)
            change_ledger.summarize(t.root, "c", unit=UNIT, base="HEAD~1", head="HEAD")
            inputs = {r["input"]: r["value"] for r in rows(t.root, "c", "inputs.tsv")}
            self.assertEqual({k: inputs[k] for k in ("unit", "base", "head")}, {"unit": UNIT, "base": base,
                                                                                "head": head})
            total = by_step(t.root, "c")["total"]
            self.assertEqual({k: total[k] for k in ("proof_lines_added", "proof_lines_removed", "edits_address",
                                                    "edits_layout", "edits_content", "contracts_changed")},
                             {"proof_lines_added": "6", "proof_lines_removed": "5", "edits_address": "1",
                              "edits_layout": "2", "edits_content": "2", "contracts_changed": "0"})
            counts = prove.report(t.root, UNIT, base, head).counts
            self.assertEqual({k: total[k] for k in counts}, {k: str(v) for k, v in counts.items()})
            self.assertEqual(total["contracts_needing_work"], "not measured")

    def test_predicted_work_is_compared_with_the_contracts_edited(self):
        """With the oft prove --json saved when the change was made (changes/<change>/prove.json), contracts.tsv
        holds each contract's predicted state against whether its file was edited, and contracts_needing_work is
        the prediction's count: the work key's precision is a measured number."""
        with tree() as t:
            base = contract_repo(t)
            put_row(t, "LLVMFuzzerTestOneInput", exact="1e" * 32, masked="2d" * 32)
            predicted = commit(t)
            os.makedirs(t.path("changes", "c"))
            with open(t.path("changes", "c", "prove.json"), "w") as f:
                json.dump(prove.as_json(prove.report(t.root, UNIT, base, predicted)), f)
            for rel in (ENTRY, TABLE):
                t.write(rel, t.read(rel) + "(* edited *)\n")
            head = commit(t)
            change_ledger.summarize(t.root, "c", unit=UNIT, base=base, head=head)
            got = {r["contract"]: (r["predicted"], r["edited"]) for r in rows(t.root, "c", "contracts.tsv")}
            self.assertEqual({k: got[k] for k in (ENTRY, TABLE, STATE)},
                             {ENTRY: ("needs work", "yes"), TABLE: ("unchanged", "yes"), STATE: ("unchanged", "no")})
            total = by_step(t.root, "c")["total"]
            self.assertEqual((total["contracts_needing_work"], total["contracts_changed"]), ("1", "2"))
            with open(t.path("changes", "c", "prove.json"), "w") as f:
                json.dump(prove.as_json(prove.report(t.root, UNIT, predicted, head)), f)
            with self.assertRaises(change_ledger.LedgerError) as e:
                change_ledger.summarize(t.root, "c", unit=UNIT, base=base, head=head)
            self.assertIn("prove.json", str(e.exception))


if __name__ == "__main__":
    unittest.main()
