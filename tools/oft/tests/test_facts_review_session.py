"""tools/oft/ci/facts-review-run's conversation from one push to the next (REVIEW_SESSION), with a stand-in agent.

The stand-in keeps its conversation as the real agent does, in $HOME/.claude/projects/<folder>/<id>.jsonl, and refuses
to resume one that is not there, or any one when the file fail-resume exists (an exit 1 with no result) or
fail-resume-json (a result of 1 turn). A resumed conversation keeps its id: the stand-in adds to <id>.jsonl, as the
real agent does without --fork-session. When the file fail-resume-late exists, it resumes and then fails after 40
turns; when timeout-resume exists, a resume ends as `timeout` ends it (124); when fail-fresh exists, every fresh review
fails after 5 turns. A stand-in `timeout` logs the limit each call is given, in seconds, then runs the real one."""
import os
import pathlib
import shutil
import subprocess
import tempfile
import unittest

from oft import yamlio
from oft.tests.helpers import REPO
from oft.tests.test_facts_review_gate import HAVE_WORKFLOW, NO_WORKFLOW, WORKFLOW

RUN = os.path.join(REPO, "tools", "oft", "ci", "facts-review-run")
COMMENT = os.path.join(REPO, "tools", "oft", "ci", "facts-review-comment")
# The comment's and the job summary's filter for a line of tries.txt.
PLAIN = r"\A[A-Za-z0-9 ,._()-]{1,300}\Z"
FOLDER = "-runner-work-proofs-proofs"
HEAD = "1" * 40
LAST = "2" * 40
OLD = "0f97bfe1-152c-4ec0-a947-fb9d1ba5c35b"
ASKED = "anthropic/claude-opus-5-5"   # the provider and model facts-review-run asks for by default
# The stand-in prints as `--output-format stream-json` does: each result after a turn of the model it was asked for,
# with a modelUsage that names Anthropic's API.
AGENT = r"""#!/usr/bin/env bash
{ printf '%s\0' "$@"; printf '\0'; } >> "$CALLS"
id="" resume="" model=none
while [ $# -gt 0 ]; do case $1 in --session-id) id=$2 ;; --resume) resume=$2 ;; --model) model=$2 ;; esac; shift; done
# A resumed conversation that another model answers, when the file other-model exists.
[ -z "$resume" ] || [ ! -e "$CALLS.other-model" ] || model=other-b-1
result() {
  printf '{"type": "assistant", "message": {"id": "msg_%s", "model": "%s", "content": []}}\n' "$RANDOM" "$model"
  printf '%s, "modelUsage": {"%s": {"provider": "firstParty", "canonicalModel": "%s"}}}\n' "${1%\}}" "$model" "$model"
}
if [ -n "$resume" ]; then
  if [ -e "$CALLS.fail-resume" ] || ! [ -f "$HOME/.claude/projects/FOLDER/$resume.jsonl" ]; then
    echo "No conversation found with session ID: $resume" >&2; exit 1
  fi
  if [ -e "$CALLS.fail-resume-json" ]; then
    result '{"type": "result", "subtype": "success", "is_error": true, "result": "No conversation", "num_turns": 1}'
    exit 1
  fi
  if [ -e "$CALLS.fail-resume-late" ]; then
    result '{"type": "result", "subtype": "error_during_execution", "is_error": true, "num_turns": 40}'; exit 1
  fi
  [ ! -e "$CALLS.timeout-resume" ] || exit 124
  echo "{\"resumed\": \"$resume\"}" >> "$HOME/.claude/projects/FOLDER/$resume.jsonl"
elif [ -e "$CALLS.fail-fresh" ]; then
  result '{"type": "result", "subtype": "error_during_execution", "is_error": true, "num_turns": 5}'; exit 1
fi
if [ -n "$id" ]; then
  mkdir -p "$HOME/.claude/projects/FOLDER"
  echo "{\"resumed\": \"$resume\"}" > "$HOME/.claude/projects/FOLDER/$id.jsonl"
fi
result '{"type": "result", "subtype": "success", "is_error": false, "result": "No findings.", "num_turns": 3}'
""".replace("FOLDER", FOLDER)
TIMEOUT = r"""#!/usr/bin/env bash
for a in "$@"; do case $a in --*) ;; *s) echo "${a%s}" >> "$CALLS.timeouts"; break ;; esac; done
exec /usr/bin/timeout "$@"
"""

class Session(unittest.TestCase):
    def setUp(self):
        self.tmp = pathlib.Path(tempfile.mkdtemp(prefix="oft-test-"))
        self.addCleanup(shutil.rmtree, self.tmp)
        self.checkout, self.home, self.session, bin = (self.tmp / d for d in ("checkout", "home", "session", "bin"))
        for d in (self.checkout / "review", self.home, self.session, bin):
            d.mkdir(parents=True)
        # The run passes the agent none of the test's variables, so the stand-in's log path is written into it.
        (bin / "claude").write_text(AGENT.replace('"$CALLS', f'"{self.tmp}/calls'))
        (bin / "timeout").write_text(TIMEOUT.replace('"$CALLS', f'"{self.tmp}/calls'))
        for tool in ("claude", "timeout"):
            (bin / tool).chmod(0o755)
        (self.checkout / "review" / "changed.txt").write_text("M\tprojects/zlib/project.yaml\n")
        (self.checkout / "review" / "reviewed.txt").write_text(f"head={HEAD}\nbase_ref=main\nmerge_base={LAST}\n")

    def run_review(self, **environment):
        env = {"PATH": f"{self.tmp / 'bin'}:{os.environ['PATH']}", "HOME": str(self.home), "PR": "7",
               "REVIEW_SESSION": str(self.session), **environment}
        return subprocess.run([RUN, "review"], cwd=self.checkout, env=env, capture_output=True, text=True)

    def last_review(self):
        (self.session / "session").write_text(f"id={OLD}\nhead={LAST}\ndir={FOLDER}\nasked={ASKED}\nbase=main\n")
        (self.session / f"{OLD}.jsonl").write_text("I found two wrong sizes.\n")
        (self.checkout / "review" / "since-last-review.diff").write_text("diff --git a/x b/x\n")

    def calls(self):
        return [call.split("\0") for call in (self.tmp / "calls").read_text().split("\0\0")[:-1]]

    def kept(self):
        fields = dict(line.split("=", 1) for line in (self.session / "session").read_text().splitlines())
        return fields, (self.session / f"{fields['id']}.jsonl").read_text()

    def test_a_first_review_is_fresh_and_keeps_its_conversation(self):
        r = self.run_review()
        self.assertEqual(r.returncode, 0, r.stderr)
        self.assertIn("no conversation of an earlier review of pull request #7 to resume: a fresh review", r.stdout)
        [call] = self.calls()
        self.assertNotIn("--resume", call)
        new = call[call.index("--session-id") + 1]
        self.assertEqual(self.kept(), ({"id": new, "head": HEAD, "dir": FOLDER, "asked": ASKED, "base": "main"}, '{"resumed": ""}\n'))
        self.assertIn(f"kept the conversation {new} of the review of {HEAD}", r.stdout)

    def test_a_later_review_resumes_the_same_conversation_and_reviews_only_the_new_diff(self):
        self.last_review()
        r = self.run_review()
        self.assertEqual(r.returncode, 0, r.stderr)
        self.assertIn(f"resuming the conversation {OLD} (the review of {LAST}), reviewing only {LAST}..{HEAD}", r.stdout)
        [call] = self.calls()
        self.assertEqual(call[call.index("--resume") + 1], OLD)
        self.assertNotIn("--fork-session", call)
        self.assertNotIn("--session-id", call)
        prompt = call[call.index("-p") + 1]
        self.assertIn("This review looks only at the diff since the head you last reviewed: "
                      f"review/since-last-review.diff holds the changes from {LAST} to {HEAD}, ", prompt)
        self.assertIn("Do not review again what the diff does not change: a new finding comes only from the diff.",
                      prompt)
        self.assertIn("drop the finding when they show that it no longer holds, and keep it otherwise", prompt)
        self.assertIn("to the facts files and to each reviewed fuzz target's provenance/", prompt)
        self.assertIn("Review that diff against review.md (read it again: main can have changed it)", prompt)
        self.assertNotIn("It is empty", prompt)
        # The kept conversation is the same one, under the same id, with this review added to it.
        self.assertEqual(self.kept(), ({"id": OLD, "head": HEAD, "dir": FOLDER, "asked": ASKED, "base": "main"},
                                       f'I found two wrong sizes.\n{{"resumed": "{OLD}"}}\n'))
        self.assertEqual(sorted(p.name for p in self.session.iterdir()), sorted(["session", f"{OLD}.jsonl"]))
        self.assertEqual((self.checkout / "review" / "comment.md").read_text(), "No findings.\n")

    def test_a_new_head_with_an_empty_diff_resumes_the_same_conversation(self):
        """A push that changes none of the files the diff covers (a merge of main, a proof or a tool) is still a new
        head: the review resumes, and the prompt says that the diff is empty."""
        self.last_review()
        (self.checkout / "review" / "since-last-review.diff").write_text("")
        r = self.run_review()
        self.assertEqual(r.returncode, 0, r.stderr)
        self.assertIn(f"resuming the conversation {OLD} (the review of {LAST}), reviewing only {LAST}..{HEAD}", r.stdout)
        [call] = self.calls()
        self.assertEqual(call[call.index("--resume") + 1], OLD)
        self.assertIn("It is empty: this push changes none of those files.", call[call.index("-p") + 1])
        self.assertEqual(self.kept()[0]["id"], OLD)

    def test_the_same_head_or_a_missing_diff_gives_a_fresh_full_review(self):
        """The same head (a new base, a run by hand) has no new diff, and a missing diff (gather could not fetch or
        diff the last head) shows nothing to look at alone: each review is a fresh, full one."""
        for case, said in (("same head", f"the kept conversation {OLD} is the review of this head, {HEAD}: a fresh, "
                                          "full review"),
                           ("missing", "gather could not make review/since-last-review.diff since the review of "
                                       f"{LAST}: a fresh, full review")):
            with self.subTest(case):
                self.setUp()
                self.last_review()
                diff = self.checkout / "review" / "since-last-review.diff"
                if case == "missing":
                    diff.unlink()
                else:
                    (self.session / "session").write_text(f"id={OLD}\nhead={HEAD}\ndir={FOLDER}\nasked={ASKED}\nbase=main\n")
                    diff.write_text("")
                r = self.run_review()
                self.assertEqual(r.returncode, 0, r.stderr)
                self.assertIn(said, r.stdout)
                # A kept conversation was there and was left alone on purpose: the log does not say there was none.
                self.assertNotIn("no conversation of an earlier review", r.stdout)
                self.assertIn("facts-review-run: a fresh review, as ", r.stdout)
                [call] = self.calls()
                self.assertNotIn("--resume", call)
                self.assertNotIn("since-last-review.diff", call[call.index("-p") + 1])
                self.assertEqual(self.kept()[0]["id"], call[call.index("--session-id") + 1])

    def test_the_first_prompt_names_review_md(self):
        self.run_review()
        [call] = self.calls()
        self.assertIn("Read review.md, at the root of this checkout, for what to check", call[call.index("-p") + 1])

    def test_a_resumed_review_another_model_answered_is_not_published_or_tried_fresh(self):
        """The resumed try runs under facts-review-served too: another model answers it, so the review is not
        published, there is no fresh try, and the last conversation is left as it was."""
        self.last_review()
        (self.tmp / "calls.other-model").touch()
        r = self.run_review()
        self.assertEqual(r.returncode, 4, r.stdout + r.stderr)
        self.assertEqual(len(self.calls()), 1, "a fresh try after a review another model answered")
        self.assertIn("turn 1 was answered by other-b-1", r.stderr)
        self.assertIn("the review is not published: ", r.stderr)
        self.assertEqual((self.checkout / "review" / "comment.md").read_text(), "")
        self.assertEqual(self.tries(), [f"try 1 of 3 (resumed from the review of {LAST[:12]}), not published, as the "
                                        "provider or model that answered it is not the one asked for or is not shown"])
        self.assertEqual((self.session / "session").read_text(),
                         f"id={OLD}\nhead={LAST}\ndir={FOLDER}\nasked={ASKED}\nbase=main\n")

    def test_a_conversation_kept_against_another_base_is_not_resumed(self):
        """On another base branch (a retargeted stacked pull request, say), changed.txt, targets.txt and patches/ are
        counted again, and the diff since the last head does not show what that adds: the review is fresh and full,
        also on a new head with an empty diff. A session kept before `base=` was written names none: fresh too."""
        for base in ("base=release\n", ""):
            with self.subTest(base=base):
                self.setUp()
                self.last_review()
                (self.session / "session").write_text(f"id={OLD}\nhead={LAST}\ndir={FOLDER}\nasked={ASKED}\n{base}")
                (self.checkout / "review" / "since-last-review.diff").write_text("")
                r = self.run_review()
                self.assertEqual(r.returncode, 0, r.stderr)
                self.assertIn(f"the kept conversation {OLD} is a review against another base branch than this one: a "
                              "fresh, full review", r.stdout)
                [call] = self.calls()
                self.assertNotIn("--resume", call)
                self.assertEqual(self.kept()[0], {"id": call[call.index("--session-id") + 1], "head": HEAD,
                                                  "dir": FOLDER, "asked": ASKED, "base": "main"})

    def test_a_conversation_kept_for_another_model_or_none_is_not_resumed(self):
        """A conversation kept before facts-review-served names no model (no `asked=`), and one kept for another
        REVIEW_MODEL is another model's: neither is resumed, and the review is fresh."""
        for asked in ("", "asked=anthropic/claude-sonnet-5\n"):
            with self.subTest(asked=asked):
                self.setUp()
                self.last_review()
                (self.session / "session").write_text(f"id={OLD}\nhead={LAST}\ndir={FOLDER}\n{asked}")
                r = self.run_review()
                self.assertEqual(r.returncode, 0, r.stderr)
                self.assertIn(f"the kept conversation {OLD} names no review of {ASKED}, so it is not resumed", r.stdout)
                [call] = self.calls()
                self.assertNotIn("--resume", call)

    def tries(self):
        """tries.txt, each line of which the comment and the job summary must show: plain words only."""
        lines = (self.checkout / "review" / "tries.txt").read_text().splitlines()
        for line in lines:
            self.assertRegex(line, PLAIN)
        return lines

    def limits(self):
        return [int(s) for s in (self.tmp / "calls.timeouts").read_text().split()]

    def test_a_conversation_that_cannot_be_resumed_gives_a_fresh_review_that_is_try_1(self):
        """No conversation to load is a sure failure, not the chance death that the 3 tries are sized for."""
        for refusal in ("fail-resume", "fail-resume-json"):
            with self.subTest(refusal):
                self.setUp()
                self.last_review()
                (self.tmp / f"calls.{refusal}").touch()
                r = self.run_review()
                self.assertEqual(r.returncode, 0, r.stderr)
                turns = "-" if refusal == "fail-resume" else "1"
                self.assertIn(f"could not resume the conversation {OLD} (exit 1, {turns} turns): a fresh review "
                              "instead, which is try 1", r.stdout)
                resumed, fresh = self.calls()
                self.assertIn("--resume", resumed)
                self.assertNotIn("--resume", fresh)
                self.assertEqual(self.kept()[0]["id"], fresh[fresh.index("--session-id") + 1])
                [refused, review] = self.tries()
                self.assertTrue(refused.startswith(f"a resume of the review of {LAST[:12]} that the agent could not "
                                                   "load, not counted as a try, the review agent ended with exit "
                                                   "status 1"), refused)
                self.assertEqual(review, "try 1 of 3, a review, success after 3 turns and 0 seconds")

    def test_a_resume_that_cannot_load_leaves_3_fresh_tries(self):
        self.last_review()
        (self.tmp / "calls.fail-resume-json").touch()
        (self.tmp / "calls.fail-fresh").touch()
        r = self.run_review()
        self.assertEqual(r.returncode, 1, r.stderr)
        calls = self.calls()
        self.assertEqual(["--resume" in call for call in calls], [True, False, False, False])
        self.assertEqual([line.split(",")[0] for line in self.tries()[1:]],
                         ["try 1 of 3", "try 2 of 3", "try 3 of 3"])

    def test_a_resumed_try_stops_in_time_for_a_fresh_one(self):
        """A slow resume (its context grows with each push) cannot use up the time a fresh try needs."""
        self.last_review()
        (self.tmp / "calls.timeout-resume").touch()
        r = self.run_review()
        self.assertEqual(r.returncode, 0, r.stderr)
        resumed, fresh = self.calls()
        self.assertIn("--resume", resumed)
        self.assertNotIn("--resume", fresh)
        first, second = self.limits()
        self.assertLessEqual(first, 45 * 60 - 720)
        self.assertGreater(second, 45 * 60 - 720)
        self.assertEqual(self.tries(), [
            f"try 1 of 3 (resumed from the review of {LAST[:12]}), the review agent ended with exit status 124, "
            "stopped at the time limit of the resumed try, which leaves a fresh try time, and wrote no review (output "
            "that is not one JSON object)",
            "try 2 of 3, a review, success after 3 turns and 0 seconds"])

    def test_a_run_with_no_review_leaves_the_last_conversation(self):
        """The next push resumes the last conversation kept."""
        self.last_review()
        (self.tmp / "calls.fail-resume-late").touch()
        (self.tmp / "calls.fail-fresh").touch()
        r = self.run_review()
        self.assertEqual(r.returncode, 1, r.stderr)
        self.assertEqual((self.session / "session").read_text(), f"id={OLD}\nhead={LAST}\ndir={FOLDER}\nasked={ASKED}\nbase=main\n")
        self.assertEqual((self.session / f"{OLD}.jsonl").read_text(), "I found two wrong sizes.\n")
        self.assertEqual(sorted(p.name for p in self.session.iterdir()), sorted(["session", f"{OLD}.jsonl"]))

    def test_a_resumed_review_that_fails_later_is_tried_again_fresh(self):
        """The second try of a run that ended without a review is a fresh review, never the conversation again."""
        self.last_review()
        (self.tmp / "calls.fail-resume-late").touch()
        r = self.run_review()
        self.assertEqual(r.returncode, 0, r.stderr)
        self.assertIn(f"the resumed review of the conversation {OLD} failed (exit 1): a fresh review instead", r.stdout)
        self.assertIn("error_during_execution after 40 turns", r.stderr)
        resumed, fresh = self.calls()
        self.assertIn("--resume", resumed)
        self.assertNotIn("--resume", fresh)
        self.assertNotEqual(OLD, fresh[fresh.index("--session-id") + 1])
        self.assertEqual(self.kept()[0]["id"], fresh[fresh.index("--session-id") + 1])
        self.assertEqual(self.tries(), [
            f"try 1 of 3 (resumed from the review of {LAST[:12]}), the review agent ended with exit status 1, "
            "error_during_execution after 40 turns and 0 seconds, and wrote no review (an error result)",
            "try 2 of 3, a review, success after 3 turns and 0 seconds"])
        self.assertIn("(try 2)", r.stdout)

    def test_a_resumed_review_says_so_in_its_try(self):
        self.last_review()
        r = self.run_review()
        self.assertEqual(r.returncode, 0, r.stderr)
        self.assertEqual(self.tries(),
                         [f"try 1 of 3 (resumed from the review of {LAST[:12]}), a review, success after 3 turns and "
                          "0 seconds"])
        self.assertIn("(try 1, resumed)", r.stdout)
        # The comment shows that line as the run wrote it, so a reworded line cannot silently drop out of it.
        (self.tmp / "review.md").write_text("No findings.\n")
        c = subprocess.run([COMMENT, str(self.tmp / "review.md")], capture_output=True, text=True, check=True,
                           env={"PATH": os.environ["PATH"], "TRIES": "\n".join(self.tries()),
                                "SERVED": (self.checkout / "review" / "served").read_text()})
        self.assertIn(f"ended: {self.tries()[0]}.</sub>", c.stdout)

    @unittest.skipUnless(HAVE_WORKFLOW, NO_WORKFLOW)
    def test_the_workflow_has_no_fresh_input_and_always_restores(self):
        workflow = yamlio.load_file(WORKFLOW)
        self.assertEqual(list(workflow["on"]["workflow_dispatch"]["inputs"]), ["pr"])
        [restore] = [s for s in workflow["jobs"]["review"]["steps"]
                     if s.get("uses", "").startswith("actions/cache/restore@")]
        self.assertNotIn("if", restore)

    def test_a_session_file_that_is_not_whole_gives_a_fresh_review(self):
        (self.session / "session").write_text(f"id={OLD}\nhead={LAST}\ndir=../../elsewhere\n")
        (self.session / f"{OLD}.jsonl").write_text("x\n")
        r = self.run_review()
        self.assertEqual(r.returncode, 0, r.stderr)
        self.assertIn("does not name a whole conversation", r.stdout)
        [call] = self.calls()
        self.assertNotIn("--resume", call)

    def test_the_conversation_is_kept_outside_the_checkout(self):
        r = self.run_review(REVIEW_SESSION=str(self.checkout / "session"))
        self.assertEqual(r.returncode, 2)
        self.assertIn("REVIEW_SESSION is inside this checkout", r.stderr)

    def test_without_review_session_nothing_is_kept_or_resumed(self):
        self.last_review()
        env = {k: v for k, v in os.environ.items() if k != "REVIEW_SESSION"}
        r = subprocess.run([RUN, "review"], cwd=self.checkout, capture_output=True, text=True,
                           env={**env, "PATH": f"{self.tmp / 'bin'}:{os.environ['PATH']}", "HOME": str(self.home),
                                "PR": "7"})
        self.assertEqual(r.returncode, 0, r.stderr)
        [call] = self.calls()
        self.assertNotIn("--resume", call)
        self.assertEqual((self.session / "session").read_text(), f"id={OLD}\nhead={LAST}\ndir={FOLDER}\nasked={ASKED}\nbase=main\n")


if __name__ == "__main__":
    unittest.main()
