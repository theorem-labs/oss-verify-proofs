#!/usr/bin/env python3
"""made_from.py: which proof files of a unit were made from a file that carries Anthropic's licence lines,
among the files with no licence lines, the files whose licence lines are Anthropic's tag without Anthropic's
copyright line and the files whose licence lines are only `Modified by` lines, and the licence lines each takes
(docs/adding-a-proof.md, requirement 7).  This file is the one generator of every unit's made-from record; each
unit's evidence/licence/made_from.py holds only that unit's data and calls it.

Usage (from the top of a checkout of this repository; L is a unit's directory
projects/<p>/<h>/proofs/provenance/evidence/licence):
  python3 L/made_from.py [--history TSV] [--apply] [--record-first-added] OUT.tsv
  python3 L/made_from.py --record [--apply] [--history TSV] RECORD
  python3 L/made_from.py --check [--history TSV] [--top TOP] [RECORD]
  python3 dev/licence/made_from.py --unit-file L/made_from.py

The unit file.  A unit's L/made_from.py holds, in this order and nothing else: an optional `#!` line and comment
lines; a docstring of one sentence that states the rule and names dev/licence/made_from.py; `DONORS = (...)`, a
tuple of "<project>/<harness>" string literals (the fuzz targets whose proof files the unit's history copied or
relocated: a file's text came into the repository when the file first came at its path in the unit or in one of
them), `()` for none; `HISTORY = ...`, the name of a file in L, a string literal, or `None`: the --history that
--check reads by default (history-named.tsv, the record's own, where the record was made with one); comment lines
and blank lines may stand between these parts; then FIXED_BLOCK of this file, byte for byte, to the end of the file.
The fixed block finds dev/licence/made_from.py seven directories above the unit file, loads it under the name
licence_made_from, and calls main() with the unit file's path; when it cannot load this file (missing, unreadable,
or an error while it loads) it exits 4.  The unit is the <p>/<h> of the unit file's path; a unit file at any
other path is refused.  Before it reads any other file, main() reads the unit file from disk and checks it, with
ast and with its text: a def, an import, a computed value (a call, a name, an operator) given to a data name, a name
other than DONORS and HISTORY, a missing or longer docstring, a line of the fixed block changed, added or taken away,
a coding declaration (PEP 263) on line 1 or 2, utf-8 included, or a byte order mark at its start (Python could
read the file as another text than the check reads, and a unit file needs neither), or a wrong path, is refused
with exit 4, naming the part that is not allowed.  So a unit file holds data and no code, and no unit's generator
can drift from another's.  --unit-file PATH does that check alone: exit 0 the file holds only its data and the
fixed block, exit 4 it is refused.  A unit file whose fixed block no longer calls this file never reaches the
check, so the made-from job of .github/workflows/pr.yml runs --unit-file on each unit file before its --check.
The data are read from the unit file's text (its checked literals), never from the process that runs it.

The files: every .v file under projects/<p>/<h>/proofs/.  A file is Anthropic-licensed when its first 10 lines
hold `Copyright <year> Anthropic PBC`.  The files decided: those whose first 10 lines hold no copyright, SPDX or
`Modified by` line and no comment of a program's instruction words, and those whose licence lines are Anthropic's
tag, `(* SPDX-License-Identifier: Apache-2.0 OR MIT *)` or the earlier bundle's `Apache-2.0`, perhaps with
`Modified by` lines, without Anthropic's copyright line (the licence rule of `oft lint` refuses them), and those
whose licence lines are only `Modified by` lines (lint reads them as MIT).  A decided file's own `Modified by` lines
stay, after the licence lines it takes; one that is exactly a comment of those its source gives is not written again:
it stands once, as the source's.

Measure.  A file's lines of code are its lines with a character outside comments (which nest), after its licence
lines.  Each line is compared after four masks, in this order: module paths (OssFuzzTheorems. or OSSVerify., then
Proofs.<p>.<h>.lib... or <p>.<h>.images), module names (the stem of a .v file of the unit or of its images),
addresses (0x...), decimal numbers.  The decision reads the lines of code without From/Require/Import/Export lines
(every file of the unit has such lines, so they show nothing of where a file came from), and the distinctive lines
among them: those of DISTINCT (20) or more characters after the masks, which leaves out lines such as `Proof.`,
`lia.` and `reflexivity.`, common to every proof.
held_d is the length of a longest common subsequence of the file's distinctive lines and a source's, held the same of
all its lines of code, share = held / its lines of code.  The best source is the Anthropic-licensed file with the
largest held_d; on a tie the largest held, then the file X.v beside a twin X_cf.v, X_cfw.v, X_cfwi.v or X_mf.v,
then the file with the same name, then path order.  The search passes over sources that cannot hold MIN_D (5)
distinctive lines (an upper bound: the distinctive lines the two files share, with repeats).  A file whose named
origin the run licenses while the file is undecided takes it with no score, unless its history row decides it (Named
origins, below).

Rule: a file was made from its best source when held_d >= HELD_D (30: a block of 30 or more distinctive lines of
Anthropic's code, in order, is a copy whatever the file's size), or share >= SHARE (0.5) with held_d >= MIN_D, or it
shares with an Anthropic-licensed file a block of consecutive lines of code, line for line after the masks, that
holds RUN (6) or more distinctive lines (a copied tactic or proof body; that file is then its source), or the history
TSV names it (path, source; history.py writes it: the commit that first added the file added it as a copy of a file
with Anthropic's lines).  A history row comes first: the named file waits while its source carries no licence lines,
and is made from it when the source carries them while the file waits, before the run or by it, whatever its named
origin or the rule finds; when the run can license no other file and the source still carries none, the wait fails.
The history row of a failed wait still decides its file when the run licenses its source while the file is
undecided: a file that names no origin is open to the rule meanwhile, and a file that names one is decided by the two
together, by its history source when that is licensed, or else by its named origin when that is.
A file whose text came into the repository's history after the file's
(the first commit, on any ref, that added a file at its path in this unit or in a fuzz target of DONORS, as
evidence/licence/first-added.tsv records it; --record-first-added writes that file from the git history of a clone
that has the branches the unit was built on) is never its source by the rule; a named origin and a history row take
no such test.  The run licenses one file at a time, the strongest first (licensed_in_order).  The licensed files
start as those with Anthropic's copyright line.  Each file whose history row names a licensed file while the file
waits joins them; so does each file whose wait failed and that names no origin, when its history row names a
licensed file, and each file with no history row whose named origin is licensed; and when none of those is left,
each file whose wait failed and that names an origin joins them by its history source when that is licensed, or
else by its origin when that is, all of them read against the same licensed files.  That repeats until none is left;
then, of the files the rule finds made from a licensed file, the one with the largest held_d, then the largest held,
then the first path joins them, and the history rows and named origins are read again.  When the rule finds none,
each history row that still waits fails; when none waits, each file that waits for an origin with Anthropic's tag
alone, or for its origin on a cycle of named origins of which no file is licensed or tagged, stops waiting (Named
origins, below); the run ends when neither is left, and each file the rule decides that is still undecided then is
written here (or borderline).  A file licensed in the run is a candidate source for each file still undecided when
it joins, and a file decided is not decided again, so no chain of sources returns to a file of the chain, and each
ends at a file that carried Anthropic's lines before the run.  An undecided file has at most one claim at any moment
(its history row while it waits, or else the one of its history row and its named origin that it has), except a
file whose wait failed and that names an origin, and such files are decided together against one set of licensed
files; every choice is made by numbers and paths, so the record is the same for any order of the files.  A file
made from its source
takes the source's licence lines (its copyright, its SPDX tag, its `Modified by` lines, as this run leaves them),
then its own `Modified by` lines, then one line

  (* Modified by Theorem Labs, 2026-11: made from proofs/<source>, with its <kinds> changed; N of its M lines of
     code are new or changed and K lines of the source are left out. *)

(one line; the form of the reac-pw targets' lines), where every line of code, Require lines included, is aligned
with the source's after the four masks, N = this file's lines of code not matched, M = its lines of code, K = the
source's lines of code not matched, and a kind is named when a matched pair of lines differs with the other three
masks applied.  Paths are spelled proofs/<p>/<h>/<path>, as every such line in this repository spells them.  The
licence lines go at the top of the file, in place of its own (the copyright and the tag within its first 10 lines,
counted in the file's lines as written, where lint reads them); its lines of code stay as they are (checked, for
every file a run writes).  A source's licence lines, and a written file's own `Modified by` lines, are copied as
whole comments: a `Modified by` comment that goes on over several lines is copied with all its lines
(licence_comments).  A source's licence lines are every licence comment among the comments that open it, with no
bound of 10 lines, each whole, in order, to its first line of code (source_licence); the 10-line rule is for the
copyright and the tag of the file as written, above, so the source's `Modified by` lines below its line 10 are
taken too.  A comment of another kind among them, such as a note of the branch the file was carried from, is passed
over and not copied, so the copyright and the tag below such a note are taken too; a source whose lines taken hold
no Anthropic copyright line is refused.  No file is written whose comments and string literals do
not close, read by oft lint's own Rocq lexer (tools/oft/rocq.py, which the checkout at --top must hold; READS names
it): the run stops and names it instead.  A tagged file that the rule finds written here takes the repository's
licence: its tag becomes `(* SPDX-License-Identifier: MIT *)`.  A file with no licence lines that the rule finds
written here is not changed.  A file with Anthropic's copyright line whose tag is the earlier bundle's `Apache-2.0`
takes the final package's `Apache-2.0 OR MIT` (LICENSES/anthropic-proofs-NOTICE); the files decided above include
those with the tag `Apache-2.0` alone.

A file below the rule with share >= BORDER (0.25) or held_d >= HELD_D / 2 is listed as borderline (decision:
written here).  OUT gets one row per file decided: path, held, held_d, lines of code, share, best source, decision,
the line; the decided files in path order, then the rows of the tag pass.  --apply writes the files.  Run on its
own output it changes nothing.  Every refusal of a run -- a write that would change a file's code, a copyright or
tag that would not fit in the first 10 lines, licence lines taken that hold no Anthropic copyright line, a file
whose comment would not close, and the three refusals of --record below -- is decided before the run writes OUT or
any .v file, so a refused run writes neither (--record-first-added writes first-added.tsv before them).

Named origins.  A file names its origin in the comments that open it, before its first line of code, each whole and
every one, not only its licence comments, however far down they go (lib/AU/YFk0g.v of curl/fuzz_fnmatch at its line
90), and in each comment's own text, not in a comment inside it (named_origins).  Three forms name one: derive_y.py's
two notes, `derived from <path> of this library by derive_y.py` and `copied from proofs/<p>/<h>/<path>` with `by
derive_y.py` later in the same comment, their words split by any blanks; and a comment whose text, after `(*` and
blanks, starts with `Relocated from <path>` (a `Relocated from` later in a comment, and a `relocated from`, name
nothing).  The path ends at its first blank or at the `*)` that closes its comment, less each `.`, `,`,
`;`, `:` and `)` at its end; it is under the unit's proofs/, or it is a path from the top of the repository,
proofs/<p>/<h>/<path> of the layout before projects/ read as tools/oft/layout.py's canonical reads it (new_layout:
this file does not load layout.py, which READS would then name).  It names no origin when ` at <commit>`
or ` (at <commit>)` (7 to 40 hex digits) follows it, when it is of another unit, when it is no .v file of
the unit outside provenance/, or when it is the file's own path.  A file whose comments name two different
origins names none, and the run says so on stderr.  An origin that carries no Anthropic copyright line
before the run and is no file the run decides (the MIT tag, a comment of a program's instruction words, a first
comment over several lines) names none either.
A file with a named origin waits until its origin is licensed, before the run or by it, and is then `made from (named
origin)`, with no score and no age test: the origin is its best source, held, held_d, its lines of code and share
are counted against the origin (as for a history row, so a file of fewer than MIN_D distinctive lines has its
counts too), and its line is `-`.  --apply writes into it the origin's licence lines as this run leaves them
(source_licence), unchanged, then each of its own `Modified by` lines that they do not hold, then the file without
its own licence comments, and no `made from` line; every refusal of a write holds for it.  An origin that the run
does not license gives the file the origin's own decision (written here,
borderline, or a `left bare` one, whose reason the file's row carries as its line), decided before the file, with
the counts and best source the rule gives the file; a tagged file's tag then becomes MIT, as above, and a `left bare`
one is then plain `left bare`, a row --check does not compare, since the file carries the MIT tag after --apply.  An
origin with Anthropic's tag alone that the run does not license is the exception: --apply gives it the MIT tag, after
which it names no origin (a file waits for it all the same, since --apply gives it Anthropic's lines when the run
licenses it).  So when the run would end, each file that still waits for such an origin stops waiting and is decided
by the rule, as a run on the output of --apply, where the origin carries the MIT tag, decides the file there when it
is still a file a run decides (a file the rule licenses carries Anthropic's lines after --apply, and no run decides it
again); and the file still takes the origin if the run licenses it while the file is undecided.  A cycle of named
origins among the files the run decides is the other exception: the first of its files that the run licenses cannot
take its origin, so when the run would end, each file of the cycle that still waits stops waiting in the same way,
while the run licenses no file of the cycle and no file of it is tagged, and the run says so on stderr, one line for
each cycle.  When the run licenses a file of it, the others wait again, and the file that names that one takes it,
and so on round the cycle: on the output of --apply that file carries Anthropic's lines and the cycle is gone, so a
run there gives each file of the cycle that it still decides the same row, and decides no file --apply licensed; a
file of the cycle whose origin the run never licenses (a file left bare is never licensed) takes that origin's
decision, as above, and so does a file that leads into the cycle.  A history row that decides the file (Rule, above)
wins over its named origin, and when the two name different files the decision is `made from (history; it names
<origin>)`.  At the end of the run, when a file
left bare is decided, an origin that is a tagged file the run does not license is not named there, since --apply
gives it the MIT tag, after which the file names no origin: the decision is `made from (history)`.  When the
history row's wait failed, the two are read together against the same licensed files: the file takes its history
source when that is licensed, or else its origin when that is.

A better match is not a wrong line.  The score finds the file that shares the most with a file, not the file it came
from: a tie across many copies shows a family of copies, any of which holds the file's text, and a nearer copy that
scores higher than a true ancestor -- a later copy of that ancestor, or one that holds more of the file's other text
-- does not show that the ancestor is wrong.  So a named origin is kept over a copy that scores higher, and nothing
here fails a row because another file matches it better.

Refreshing the record.  A run gives a row only for the files it decides, so OUT alone is not the record: the record
also holds a row for each file this generator once decided and no run decides now -- what --apply wrote (the file
carries Anthropic's lines now, or the MIT tag), and what some other change stamped since a refresh, whose row keeps its
numbers and takes the decision `carries licence lines since (was: ...)`.  It holds no row for a file this generator has
never decided, which is most of a unit's files.  `--record RECORD` writes the record: this run's rows, and those rows
of the files this run gives no row for, all in path order.  It is how to bring a record up to date after a change to
the tree -- editing a row by hand instead is what --check catches, among the rows it compares.  Without --apply it
writes no .v file.  Keeping those rows is what lets --record see a licence line that goes missing later: without them
the record would forget that it ever decided the file.  So --record exits, naming the file, when a run decides a file
the record accounts for that way and left-bare.tsv does not declare (the file has lost the licence lines its row
records, or that row was written for a bare file); when left-bare.tsv declares a file whose row says --apply wrote it
(undoing that decision is a person's to do, by hand, in the record's diff); and when a run gives a row of a decision
--apply carries out (`made from ...`, the MIT tag, the tag pass), either without --apply (a row no run gives again,
which --check would report on every run) or for a file the record keeps a row for (an applied row or a stamped row,
this refresh's included), since a refresh never replaces a kept row with the row of a decision --apply carries out.  A
row of left-bare.tsv retires a stamped row, not an applied one: the run's `left bare` row then takes the stamped row's
place.  The comment above the refusals in decide() says what to do for each.  `--record --apply` does both in one run:
it writes the .v files it decides (`made from`, the MIT tag and the tag pass) and the record, which keeps every row
--record keeps and takes this run's rows, those of the files it wrote included; with --apply the third refusal counts
only a file the record keeps a row for.

What neither can see.  --check compares the rows that regenerable() names (each row a run gives again, and each row of
fewer than 7 columns) and no others, so a row of another decision -- what --apply wrote, and the stamped rows -- can be
changed or taken out by hand and --check still passes.  Those rows are also what --record's refusal reads, so that is
its reach too.  And a file that already carried Anthropic's lines when the record was written has no row at all, so
nothing in the record says it ever had them: --check reports a strip of such a file, since the run gives a row the
record lacks.  When the run finds the file written here and the file keeps no licence tag, that row is one a run gives
again, so the exit is 3 ("Exit codes"), and a refresh after that takes the row.  When the run finds the file written
here and the file keeps Anthropic's tag, the row's decision ends `(Apache-2.0 OR MIT tag becomes MIT)`, and when the
run finds the file made from a source, the decision is `made from ...`, with the tag or without it: neither is a row a
run gives again, so the exit is 1.  Closing either reach needs something this generator does not have -- the record
compared against the record of the commit before it, or a row for every .v file of the unit and its licence state.
Both reaches are keyed on a path, so a file moved to a path the record holds no row for is outside them as well: a file
--apply stamped, renamed, stripped and declared is a strip this generator does not report, and its old row stays in the
record as the row of a file no longer in the unit.  Only a reader of the record's own diff sees that pair.

Files left bare on purpose.  The rule reads what two files share today, and two files of ours can share a block
with one of Anthropic's without coming from it (#1818: 54 files whose made-from line named a reac-repacer file over
six lines in common each equal, line for line, a bare file of the same name in another unit).  A lane that has
established a file's content is ours writes the file in the unit's evidence/licence/left-bare.tsv, one row of
`path<TAB>reason` for each, and the file carries no licence lines: its decision is `left bare`, or `left bare
(overrules made from ...)` when the run, against the files it licenses, would find it made from a source (by its
history row, its named origin or the rule), its row carries the reason as its line, --apply writes nothing to it,
and it is no source for another file either (a file made from it is ours as well, so no licence lines pass through
it; a file that names it as its origin takes its decision and its reason).  Each such row is a decision a reader can
see and weigh -- which file, and why -- where a file that is simply missing its lines cannot be told from one someone
stripped by mistake.  A row that is not one path and one reason, names a file that is not a file of the unit, names
a file that carries licence lines, gives no reason, names a path another row of the file names, or holds a byte that
is not UTF-8, is a mistake and declares nothing -- and a path named twice declares nothing whichever of its rows is
the mistake, unless the mistake is a byte that is not UTF-8, which leaves no path to read.  The run says so on
stderr and goes on.  A run leaves out no file: a file left bare is a row of OUT like any other, and a run on a tree
whose declaration was deleted, absent or a mistake decides that file by the rule alone, so its row is not the
record's and --check reports the difference (exit 1, or 3 when that difference is drift: "Exit codes").
Nothing here exits the run, because a run that refuses is a check that cannot decide (2), which a workflow may pass
over: that file, deleted or mistaken, would otherwise be a way to turn the check off.

The limit of the record.  After a file loses Anthropic's copyright line, the record reports the change only when
the file is left with (a) nothing licence-like in its first 10 lines; (b) only `Modified by` comments from line 1,
each closing on its own line (a `Modified by` comment over more than one line leaves the file undecided: 100 of
2,027 such files of libreac/fuzz_scene, measured in OSSV-348's comment 5d882363); (c) Anthropic's tag without its
copyright line; or (d) a header that oft lint refuses.  It reports no other change.  For example, a file whose
Anthropic lines are replaced by our MIT tag is not reported, and that is what --apply writes for a tagged file that
it decides written here (#2279: none of 2,027 such changes on libreac/fuzz_scene is reported).  The strip check of
the lint job of .github/workflows/pr.yml (its rules: docs/adding-a-proof.md, requirement 7) fails, in a unit with a
licence record, a change that takes Anthropic's copyright line off a proof file it pairs with that file at the base,
and no left-bare.tsv row declares a file that carries our MIT tag (left_bare() takes only a file with no licence
lines).  So that change fails the merge checks when one change makes it; a file that one change deletes and a later
change adds back with our MIT tag, or a stripped file the check pairs with no base, is still seen only by a reader
of the diffs.  The record itself still reports only (a) to (d).

--check checks the record, evidence/licence/made-from.tsv (or RECORD), against this generator's output on the tree
as it is, writing no file of the tree (its two runs write their rows in a directory of their own, and it takes them
away).  It runs the unit file twice, each run in a process of its own, with --history TSV when given, or else the
unit's HISTORY file (the record's own; history.tsv is history.py's output, whose paths are under lib/ and not under
proofs/), or else no --history, and compares the record's rows that regenerable() names (each row a run on today's tree
gives again, and each row of fewer than 7 columns), in the record's order, with the rows the runs give, in their order.
Without --top it checks the checkout the unit file is in.  It takes no --apply, --record or --record-first-added.
Before the runs it reads each of its inputs whole, with the reader a run reads it with, and loads oft lint's lexer as a
run loads it (read_inputs): an input that is missing or cannot be read, or a lexer that does not load (an error or an
exit while it loads, or no callable tokens), is refused with exit 4, naming the file, and so is a proofs folder none of
whose .v files carries Anthropic's copyright line (the checkout does not hold the unit's proofs, or every file lost
that line).  The refusal names the input as what to fix, where a run left to fail on it would stop on an uncaught
exception (a lexer that exits while it loads aside), which --check reports as a defect of this generator (5).  A run
reads its own inputs first in the same way, and refuses in the same way.

Exit codes.  0: a run wrote OUT (and with --apply the files), or --check found the record matches, or --unit-file found
the file is data only.  1: a run refused (the refusals above, a failed git log); or --check found that the record names
a path twice, or that the record differs and the difference is not drift (3), printing each row that differs (`-` the
record has it there, `+` the generator gives it there; a row under both is in the record at another place, as a row
added by hand at the end is), and --check exits 1 for nothing else.  2: --check cannot decide, for a cause outside this
generator's code: a run cannot start or its OUT cannot be read (an OSError), a run is killed by a signal (the memory
guard's SIGKILL, say), or a run exits non-zero otherwise (a refusal of its own: 1 or 4); and every refusal of argparse.
3: --check, when the record names no path twice and differs only in drift: every row that differs is one a run gives
again (given_again() says which: a row of 7 or more columns whose decision is `written here`, `borderline: written
here`, `left bare` or `left bare (overrules ...)`), and no such row names a path that the record holds in a row a run
does not give again.  It prints the rows that differ as for 1, then a line that says `made_from.py --record` brings the
record up to date.  No other path exits 3.  4: the unit file is refused, or the fixed block cannot load this file, or
an input is missing or cannot be read, or the lexer does not load, before any run or write: the record (the one --check
checks, and the RECORD --record refreshes, since a refresh without it would drop every row --apply wrote),
first-added.tsv (unless --record-first-added writes it), the history TSV (--history, and for --check the unit's HISTORY
file when no --history is given), the images' dune file, the proofs folder (it holds a .v file outside provenance, and
each such file is UTF-8), and oft lint's lexer tools/oft/rocq.py (it must be there, be UTF-8 and load: no error or exit
while it loads, and a callable tokens); or --check finds no .v file of the unit with Anthropic's copyright line.
5 (DEFECT): a defect of this generator's own code: a run or --check stops on a Fault (which no input should reach),
printing FAULT and the fault on stderr with no traceback, or on any other uncaught exception, printing its traceback;
or --check finds that a run exited 5 (printing the run's stderr, which holds the fault or the traceback), that a run
exited 0 and wrote no OUT, that a run's OUT is not UTF-8, or that its two runs on the one tree differ.  --check reads
its runs' exit codes and OUT files, never the text of their stderr, which text of the tree can shape.  The made-from
job of .github/workflows/pr.yml warns on 2, and on 3 for a unit that only a change to its proofs names, and its text
for 1 says the record differs, so a defect of this code is 5, none of those, which the job fails for every unit.  No
other code is given.
"""
import argparse
import ast
import bisect
import collections
import difflib
import importlib.util
import os
import re
import subprocess
import sys
import tempfile
import traceback

LEXER = "tools/oft/rocq.py"   # oft lint's Rocq lexer: comments (nested) and string literals, as Rocq lexes them
# the files of the repository outside a unit and outside dev/licence/ that this generator reads; the made-from job
# of .github/workflows/pr.yml runs every unit's --check when a change touches one of them (its MADE_FROM_READS)
READS = (LEXER,)
WHO, WHEN = "Theorem Labs", "2026-11"
SHARE, BORDER = 0.5, 0.25           # share of a file's lines of code held in order by its source
HELD_D, MIN_D, DISTINCT = 30, 5, 20  # distinctive lines (DISTINCT+ characters after the masks) held in order
RUN = 6                              # distinctive lines in one block of consecutive lines shared line for line
IMPORTS = ("From ", "Require ", "Import ", "Export ")
HEADER_LINES = 10
ANTHROPIC = re.compile(r"Copyright \d{4} Anthropic PBC")
LICENCE = re.compile(r"\(\* (?:Copyright \d{4} |SPDX-License-Identifier:|Modified by )")
PROGRAM = re.compile(r"^\(\* (?:Machine-generated data computed|This file states or restates instruction words)", re.M)
MODULE = re.compile(r"(?:OssFuzzTheorems|OSSVerify)\.(?:Proofs\.\w+\.\w+\.lib(?:\.\w+)*|\w+\.\w+\.images)")
IDENT = re.compile(r"(?<![\w'])[^\W\d][\w']*")
ADDRESS = re.compile(r"\b0x[0-9a-fA-F]+\b")
DECIMAL = re.compile(r"\b\d+\b")
TOKEN = re.compile(r"\(\*|\*\)|\"")
IMAGE_TARGET = re.compile(r"\(targets ([^)]*)\)")
KIND_NAMES = ("module paths", "module names", "addresses", "numbers")
TWIN_SUFFIXES = ("_cf", "_cfw", "_cfwi", "_mf")


def licence_lines(text):
    """The leading comment lines of the file's first HEADER_LINES that are a copyright, an SPDX tag or a Modified by
    line, and the rest of the file."""
    # what this reading leaves the record unable to report: the module docstring, "The limit of the record"
    lines = text.split("\n")
    j = 0
    # a licence line is one whole comment on its line: a comment that goes on below its first line is the file's text
    while j < min(len(lines), HEADER_LINES) and LICENCE.match(lines[j]) and lines[j].rstrip().endswith("*)"):
        j += 1
    return lines[:j], "\n".join(lines[j:])


ROCQ = None   # oft lint's lexer, the module LEXER, once load_lexer has loaded it


def load_lexer(top):
    """Load oft lint's own lexer from the checkout at top as ROCQ, so that what this generator calls a closed comment
    is what lint calls one: a second rule of its own could pass a file that lint and Rocq refuse.  It raises what
    loading the module raises (a syntax error, or an error or an exit while it runs), and ImportError when the module
    has no callable tokens, which comment_end and unclosed call; ROCQ is set only when the load succeeds, so a failed
    load leaves the lexer loaded before it."""
    global ROCQ
    spec = importlib.util.spec_from_file_location("oft_rocq", os.path.join(top, LEXER))
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    if not callable(getattr(module, "tokens", None)):
        raise ImportError("it has no callable tokens, which comment_end and unclosed call")
    ROCQ = module


def comment_end(text):
    """The offset just after the comment that opens at offset 0 of text closes, by lint's lexer; None if it never
    closes."""
    depth, at = 0, 0
    for kind, piece, _inside in ROCQ.tokens(text):
        at += len(piece)
        if kind == "open":
            depth += 1
        elif kind == "close":
            depth -= 1
            if depth == 0:
                return at
    return None


def whole_comment(rest):
    """The offset just after the comment that opens rest closes, with the whole comments that follow it on its last
    line; None when it never closes, or when code follows it on that line (then it is no licence comment)."""
    end = comment_end(rest)
    # more whole comments on the comment's last line, as `(* Copyright ... *) (* SPDX-... *)`, go with it
    while end is not None and rest[end:].lstrip(" \t").startswith("(*"):
        more = len(rest[end:]) - len(rest[end:].lstrip(" \t"))
        tail = comment_end(rest[end + more:])
        end = None if tail is None else end + more + tail
    if end is None:
        return None
    stop = rest.find("\n", end)
    return None if rest[end:len(rest) if stop < 0 else stop].strip() else end


def licence_comments(text):
    """A file's licence lines as they are copied: the leading comments of its first HEADER_LINES lines that are a
    copyright, an SPDX tag or a Modified by line, each WHOLE however many lines it goes on over (one item per comment,
    its lines joined by newlines), each closing at the end of a line; and the rest of the file.  licence_lines, which
    decides which files this generator reads, takes only comments of one line, and copying only those dropped a
    source's `Modified by` comment of several lines and every licence line after it."""
    lines, out, j = text.split("\n"), [], 0
    while j < min(len(lines), HEADER_LINES) and LICENCE.match(lines[j]):
        rest = "\n".join(lines[j:])
        end = whole_comment(rest)
        if end is None:
            break
        k = j + rest.count("\n", 0, end)
        out.append("\n".join(lines[j:k + 1]))
        j = k + 1
    return out, "\n".join(lines[j:])


def opening_comments(text):
    """(j, k, comment) for each comment among the comments that open text, each whole (whole_comment: with the whole
    comments that follow it on its last line), in order, with no bound of HEADER_LINES: j and k its first and last
    line, from 0, and comment its text.  They end at the file's first line of code, at a comment that never closes, or
    at a comment with code after it on its last line."""
    lines, j = text.split("\n"), 0
    while j < len(lines):
        if not lines[j].strip():
            j += 1
            continue
        if not lines[j].lstrip().startswith("(*"):
            break   # the file's code: its opening comments end here
        rest = "\n".join(lines[j:])
        end = whole_comment(rest)
        if end is None:
            break
        k = j + rest.count("\n", 0, end)
        yield j, k, rest[:end]
        j = k + 1


def source_licence(text):
    """The licence lines an Anthropic-licensed source gives a file made from it: every licence comment (a copyright, an
    SPDX tag or a Modified by line) among the comments that open it (opening_comments), each whole, in their order,
    with no bound of HEADER_LINES: they end at its first line of code, at a comment that never closes, or at a comment
    with code after it on its last line.  The 10-line rule is for the copyright and the tag of the file as written
    (decide), so the source's `Modified by` lines below its line 10, as this generator's own writes leave a file, are
    taken too.  A comment of another kind among them, such as a note of the branch the file was carried from, is not
    a licence line and is passed over, not copied; licence_comments, which stops at it, would leave the copy without
    the source's copyright and tag when they stand below such a note."""
    lines = text.split("\n")
    return ["\n".join(lines[j:k + 1]) for j, k, _comment in opening_comments(text) if LICENCE.match(lines[j])]


# The three forms of a line that names a file's origin (origins_named): the two notes derive_y.py writes into a copy,
# and the first words of a comment that a relocation wrote.  Words may be split by any blanks, newlines included.
DERIVED = re.compile(r"\bderived\s+from\s+(\S+)\s+of\s+this\s+library\s+by\s+derive_y\.py")
COPIED = re.compile(r"\bcopied\s+from\s+(proofs/\S+)")
BY_DERIVE_Y = re.compile(r"\bby\s+derive_y\.py")
RELOCATED = re.compile(r"\(\*\s*Relocated\s+from\s+(\S+)")
# After a path: ` at <commit>` or ` (at <commit>)`, the path at a commit, not in this tree.
AT_COMMIT = re.compile(r"\s+(?:at\s+[0-9a-fA-F]{7,40}(?!\w)|\(at\s+[0-9a-fA-F]{7,40}\))")
NO_PLACE = ("lib", "lib-lean")   # proofs/lib/ and proofs/lib-lean/: no fuzz target's (tools/oft/layout.py NO_PLACE)


def new_layout(path):
    """A path from the top of the repository as tools/oft/layout.py canonical gives it, for a path under proofs/:
    proofs/<p>/<h>/<rest> of the layout before projects/ is projects/<p>/<h>/proofs/<rest>, and any other path is
    itself (proofs/lib/ and proofs/lib-lean/ among them, which the new layout gives no place).  This file does not
    load layout.py: READS, and the made-from job's MADE_FROM_READS, would then have to name it."""
    parts = path.split("/")
    if parts[0] == "proofs" and len(parts) > 3 and parts[1] not in NO_PLACE:
        return "projects/%s/%s/proofs/%s" % (parts[1], parts[2], "/".join(parts[3:]))
    return path


def origin_path(path, unit):
    """The path under the proofs/ of unit (<p>, <h>) that a path of a provenance line names, each `.`, `,`, `;`, `:`
    and `)` at its end not part of it: a path under the unit's proofs/, or a path from the top of the repository in
    either layout (new_layout); None for a path of another unit or of no unit.  The path given ends at its first
    blank or at the `*)` that closes its comment, and a path with ` at <commit>` or ` (at <commit>)` after it names
    no origin (origins_named)."""
    path = new_layout(path.rstrip(".,;:)"))
    prefix = "projects/%s/%s/proofs/" % unit
    if path.startswith(prefix):
        return path[len(prefix):]
    return None if path.startswith(("projects/", "proofs/")) else path


def own_comments(text):
    """The text of each top-level comment among the comments that open text (opening_comments, every one and not only
    licence comments, each of a line's whole comments on its own), less its close `*)`, so that the close ends a path
    as the end of the text does, and with each comment inside it read as one blank: a line inside another comment
    names nothing."""
    out = []
    for _j, _k, comment in opening_comments(text):
        depth, own = 0, []
        for kind, piece, _inside in ROCQ.tokens(comment):
            if kind == "open":
                depth += 1
                if depth == 1:
                    own = [piece]
                elif depth == 2:
                    own.append(" ")   # a comment inside it: one blank, so the words around it stay apart
            elif kind == "close":
                depth -= 1
                if not depth:
                    out.append("".join(own))
            elif depth == 1:
                own.append(piece)
    return out


def origins_named(text, unit):
    """The paths under the proofs/ of unit that a file's text names as its origin, in its opening comments
    (own_comments, however far down they go): `derived from <path> of this library by derive_y.py`; `copied from
    proofs/<p>/<h>/<path>` with `by derive_y.py` later in the same comment; and a comment whose text, after `(*` and
    blanks, starts with `Relocated from <path>` (a `Relocated from` later in a comment, and a `relocated from`, name
    nothing).  The path ends at its first blank or at the `*)` that closes its comment (own_comments, origin_path);
    a path with ` at <commit>` or ` (at <commit>)` after it (7 to 40 hex digits) is one at another commit and names
    nothing, nor does a path of another unit or of no unit."""
    if "derive_y.py" not in text and "Relocated" not in text:
        return []   # none of the three forms can stand in it
    out = []
    for comment in own_comments(text):
        found = list(DERIVED.finditer(comment))
        found += [m for m in COPIED.finditer(comment) if BY_DERIVE_Y.search(comment, m.end())]
        relocated = RELOCATED.match(comment)
        if relocated:
            found.append(relocated)
        for m in found:
            path = None if AT_COMMIT.match(comment, m.end(1)) else origin_path(m.group(1), unit)
            if path is not None:
                out.append(path)
    return out


def named_origins(u, files, unit):
    """({file: its named origin}, {file on a cycle of named origins: the files of its cycle, in path order}) for the
    files a run decides (files, in any order; the result does not depend on it).  A file's origin is a path
    origins_named gives that is a .v file of the unit outside provenance/ (u.files) and not the file itself; a file
    that names two different such files names none, and the run says so on stderr.  An origin that carries no
    Anthropic copyright line before the run (u.anthropic) and is no file the run decides names none either (the MIT
    tag, a comment of a program's instruction words, a first comment over several lines): the rule decides the file.
    A cycle of named origins among the files the run decides keeps its origins: the first of its files that the run
    licenses cannot take its origin, so each file of it that still waits for its origin may stop waiting when the run
    stalls (licensed_in_order, step 4), and a file that leads into the cycle waits for its own as any other file does.
    The run says so on stderr, one line for each cycle, its files in path order, the cycles in the order of their
    first paths."""
    decided, named = set(files), {}
    for p in files:
        found = sorted({o for o in origins_named(u.files[p], unit) if o in u.files and o != p})
        if len(found) > 1:
            print("made_from.py: %s names %d origins, %s: it names none" % (p, len(found), words(found)),
                  file=sys.stderr)
        elif found and (found[0] in u.anthropic or found[0] in decided):
            named[p] = found[0]
    cycles, seen = [], set()
    for p in files:
        trail, at, x = [], {}, p
        while x in named and x not in seen and x not in at:
            at[x] = len(trail)
            trail.append(x)
            x = named[x]
        if x in at:
            cycles.append(sorted(trail[at[x]:]))
        seen.update(trail)
    cycle = {}
    for c in sorted(cycles):
        print("made_from.py: a cycle of named origins, %s: each of them may stop waiting for its origin when the run "
              "stalls" % words(c), file=sys.stderr)
        cycle.update((p, tuple(c)) for p in c)
    return dict(sorted(named.items())), cycle


def unclosed(text):
    """What lint's lexer finds open at the end of text: "comment", "string literal", or None when all close."""
    depth = 0
    for kind, piece, _inside in ROCQ.tokens(text):
        if kind == "open":
            depth += 1
        elif kind == "close":
            depth -= 1
        elif kind == "string" and piece.count('"') % 2:   # "" inside a literal is a quote: a closed one has an even count
            return "string literal"
    return "comment" if depth else None


def lines_of(items):
    """The line each item of a list of licence comments starts on, from 0."""
    out, n = [], 0
    for x in items:
        out.append(n)
        n += x.count("\n") + 1
    return out


APACHE_TAG = "(* SPDX-License-Identifier: Apache-2.0 OR MIT *)"
BUNDLE_TAG = "(* SPDX-License-Identifier: Apache-2.0 *)"   # the earlier bundle's form of Anthropic's tag
MIT_TAG = "(* SPDX-License-Identifier: MIT *)"


def headerless(text):
    head = "\n".join(text.split("\n")[:HEADER_LINES])
    return not ANTHROPIC.search(head) and not LICENCE.search(head) and not PROGRAM.search(head)


def tagged(text):
    """A file whose licence lines are Anthropic's licence tag (either form), and perhaps `Modified by` lines, without
    Anthropic's copyright line: the licence rule of `oft lint` refuses it, and this generator decides it as it decides
    a headerless file.  Its own `Modified by` lines stay, after the licence lines it takes."""
    lic = licence_lines(text)[0]
    return (bool(lic) and lic[0] in (APACHE_TAG, BUNDLE_TAG) and all(x.startswith("(* Modified by ") for x in lic[1:])
            and not ANTHROPIC.search("\n".join(text.split("\n")[:HEADER_LINES])))


def modified_only(text):
    """A file whose licence lines are only `Modified by` lines (no copyright, no tag): lint reads it as MIT, written
    here, and this generator decides it as it decides a headerless file; its `Modified by` lines stay."""
    lic = licence_lines(text)[0]
    return bool(lic) and all(x.startswith("(* Modified by ") for x in lic) and not ANTHROPIC.search(
        "\n".join(text.split("\n")[:HEADER_LINES]))


def own_lines(text):
    """A decided file's own `Modified by` lines (none for a headerless file), as its whole leading licence comments
    (licence_comments): a write keeps each of them whole, after the lines the file takes.  Which files are decided
    is licence_lines' to say (tagged, modified_only); this says only what a written file keeps."""
    lic = licence_comments(text)[0]
    return lic[1:] if tagged(text) else lic if modified_only(text) else []


def code_lines(body):
    """The lines with a character outside comments (which nest) and not blank."""
    out, depth, in_string = [], 0, False
    for line in body.split("\n"):
        if not depth and not in_string and "(*" not in line and '"' not in line:
            if line.strip():
                out.append(line)
            continue
        code, pos = False, 0
        for m in TOKEN.finditer(line):
            t = m.group()
            if in_string:
                code = True
                in_string = t != '"'
            else:
                if not depth and line[pos:m.start()].strip():
                    code = True
                if t == "(*":
                    depth += 1
                elif t == "*)":
                    depth, code = (depth - 1, code) if depth else (0, True)
                elif not depth:
                    in_string = code = True
            pos = m.end()
        if in_string or (not depth and line[pos:].strip()):
            code = True
        if code:
            out.append(line)
    return out


def masked(line, stems, keep=None):
    if keep != 0:
        line = MODULE.sub("\x01", line)
    if keep != 1:
        line = IDENT.sub(lambda m: "\x02" if m.group() in stems else m.group(), line)
    if keep != 2:
        line = ADDRESS.sub("\x03", line)
    if keep != 3:
        line = DECIMAL.sub("\x04", line)
    return line


def _trim(a, b):
    n, m, lo = len(a), len(b), 0
    while lo < n and lo < m and a[lo] == b[lo]:
        lo += 1
    hi = 0
    while hi < n - lo and hi < m - lo and a[n - 1 - hi] == b[m - 1 - hi]:
        hi += 1
    return lo, hi


def _myers(a, b):
    n, m = len(a), len(b)
    off = n + m + 1
    v = [0] * (2 * off + 3)
    for d in range(n + m + 1):
        for k in range(-d, d + 1, 2):
            if k == -d or (k != d and v[off + k - 1] < v[off + k + 1]):
                x = v[off + k + 1]
            else:
                x = v[off + k - 1] + 1
            y = x - k
            while x < n and y < m and a[x] == b[y]:
                x += 1
                y += 1
            v[off + k] = x
            if x >= n and y >= m:
                return d
    return n + m


def lcs_len(a, b):
    lo, hi = _trim(a, b)
    ma, mb = a[lo:len(a) - hi], b[lo:len(b) - hi]
    if not ma or not mb:
        return lo + hi
    return lo + hi + (len(ma) + len(mb) - _myers(ma, mb)) // 2


def align(a, b, weight):
    """Index pairs of a longest common subsequence of a and b; among the longest, the one with the largest sum of
    weight(i, j)."""
    n, m = len(a), len(b)
    lcs = lcs_len(a, b)
    lo, hi = -(n - lcs), m - lcs
    big = 5 * (n + 1)
    rows, prev, p0, p1 = [], None, 0, -1
    for i in range(n + 1):
        j0, j1 = max(0, i + lo), min(m, i + hi)
        row = [0] * (j1 - j0 + 1)
        for j in range(j0, j1 + 1):
            if not i and not j:
                continue
            best = prev[j - p0] if i and p0 <= j <= p1 else -1
            if j > j0 and row[j - 1 - j0] > best:
                best = row[j - 1 - j0]
            if i and j and p0 <= j - 1 <= p1 and a[i - 1] == b[j - 1]:
                s = prev[j - 1 - p0] + big + weight(i - 1, j - 1)
                if s > best:
                    best = s
            row[j - j0] = best
        rows.append((j0, row))
        prev, p0, p1 = row, j0, j1
    score = lambda i, j: rows[i][1][j - rows[i][0]] if 0 <= j - rows[i][0] < len(rows[i][1]) else None
    i, j, pairs = n, m, []
    while i or j:
        s = score(i, j)
        d = score(i - 1, j - 1) if i and j and a[i - 1] == b[j - 1] else None
        if d is not None and d + big + weight(i - 1, j - 1) == s:
            pairs.append((i - 1, j - 1))
            i, j = i - 1, j - 1
        elif i and score(i - 1, j) == s:
            i -= 1
        else:
            j -= 1
    pairs.reverse()
    return pairs


def twin_of(p, universe):
    d, stem = p.rsplit("/", 1)[0] if "/" in p else "", p.rsplit("/", 1)[-1][:-2]
    for suffix in TWIN_SUFFIXES:
        f = ("%s/%s.v" % (d, stem[:-len(suffix)])).lstrip("/")
        if stem.endswith(suffix) and len(stem) > len(suffix) and f in universe:
            return f
    return None


def words(xs):
    return xs[0] if len(xs) == 1 else "%s and %s" % (", ".join(xs[:-1]), xs[-1])


def sentence(src, kinds, n, m, k):
    clause = ", with its %s changed" % words(kinds) if kinds else ""
    if not n and not k:
        s = "copied from %s%s" % (src, clause or ", with only its comments or blank lines changed")
    else:
        parts = []
        if n:
            parts.append("its one line of code is new or changed" if m == 1 else
                         "%d of its %d lines of code %s new or changed" % (n, m, "is" if n == 1 else "are"))
        if k:
            parts.append("%d %s of the source %s left out" % (k, "line" if k == 1 else "lines", "is" if k == 1 else "are"))
        s = "made from %s%s; %s" % (src, clause, " and ".join(parts))
    return "(* Modified by %s, %s: %s. *)" % (WHO, WHEN, s)


class Layout:
    """Where a unit's files are, from the path of its unit file (projects/<p>/<h>/proofs/provenance/evidence/licence/
    made_from.py), and the data the unit file holds.  Every path but top and unit_file is relative to a checkout's
    top."""

    def __init__(self, unit_file, donors, history):
        self.unit_file = os.path.abspath(unit_file)
        parts = self.unit_file.split(os.sep)
        self.unit = (parts[-7], parts[-6])
        # the top of the checkout the unit file is in: it lives seven directories below it
        self.top = os.sep.join(parts[:-8]) or os.sep
        self.root_dir = "projects/%s/%s/proofs" % self.unit
        self.logical = "proofs/%s/%s" % self.unit
        self.images_dune = "projects/%s/%s/images/dune" % self.unit
        licence = self.root_dir + "/provenance/evidence/licence"
        self.record = licence + "/made-from.tsv"
        self.first_added = licence + "/first-added.tsv"
        self.left_bare_tsv = licence + "/left-bare.tsv"
        # the --history the record was made with, which --check reads by default
        self.history = licence + "/" + history if history is not None else None
        self.donors = donors


class Unit:
    def __init__(self, top, layout):
        self.top = top
        base = os.path.join(top, layout.root_dir)
        self.files = {}
        for d, dirs, names in os.walk(base):
            dirs.sort()
            if os.path.relpath(d, base).split(os.sep)[0] == "provenance":
                continue
            for n in sorted(names):
                if n.endswith(".v"):
                    rel = os.path.relpath(os.path.join(d, n), base)
                    with open(os.path.join(d, n), encoding="utf-8", newline="") as f:
                        self.files[rel] = f.read()
        self.stems = {p.rsplit("/", 1)[-1][:-2] for p in self.files}
        dune = os.path.join(top, layout.images_dune)
        if os.path.isfile(dune):
            for t in IMAGE_TARGET.findall(open(dune, encoding="utf-8").read()):
                self.stems.update(x[:-2] for x in t.split() if x.endswith(".v"))
        self.anthropic = {p for p, t in self.files.items()
                          if ANTHROPIC.search("\n".join(t.split("\n")[:HEADER_LINES]))}
        self._all, self._code, self._dist, self._bag = {}, {}, {}, {}
        self._index, self._indexed = collections.defaultdict(dict), set()   # masked line -> {source: count}
        self._lcs = {}   # (kind, p, q) -> lcs_len of the two files' lines of that kind (lcs)

    def code_all(self, p):
        """(lines of code, masked): every line with code, the measure of the Modified by line's counts."""
        if p not in self._all:
            raw = code_lines(licence_lines(self.files[p])[1])
            self._all[p] = (raw, [masked(l, self.stems) for l in raw])
        return self._all[p]

    def code(self, p):
        """The masked lines of code that the decision reads: without From/Require/Import/Export lines."""
        if p not in self._code:
            raw, m = self.code_all(p)
            self._code[p] = [x for r, x in zip(raw, m) if not r.strip().startswith(IMPORTS)]
        return self._code[p]

    def dist(self, p):
        """The distinctive lines: lines of code (as code) of DISTINCT or more characters after the masks."""
        if p not in self._dist:
            self._dist[p] = [x for x in self.code(p) if len(x.strip()) >= DISTINCT]
        return self._dist[p]

    def lcs(self, kind, p, q):
        """lcs_len(self.code(p), self.code(q)) when kind is "code", lcs_len(self.dist(p), self.dist(q)) when it is
        "dist": measured once for each pair and kept, since a run decides a file again each time a file joins the
        licensed files, and so measures the same pairs again.  Keeping it is right because a file's text does not
        change once the run measures it, as the caches of code_all, code and dist assume too: self.files is rewritten
        only in the tag pass (to_decide), before any measure, and a file the run licenses is written as a text of its
        own (licensed_in_order's written), never back into self.files."""
        key = (kind, p, q)
        if key not in self._lcs:
            lines = self.code if kind == "code" else self.dist
            self._lcs[key] = lcs_len(lines(p), lines(q))
        return self._lcs[key]

    def best(self, p, sources):
        """(held, held_d, source): the source with the most distinctive lines in common, in order (held_d, a longest
        common subsequence of the distinctive lines); on a tie the most lines of code in common (held), then the
        twin's X.v, then the file of the same name, then path order.  None when no source holds MIN_D of them."""
        for q in sources:
            if q not in self._indexed:
                self._indexed.add(q)
                for line, c in collections.Counter(self.dist(q)).items():
                    self._index[line][q] = c
        da = self.dist(p)
        shared = collections.Counter()
        for line, c in collections.Counter(da).items():
            for q, d in self._index.get(line, {}).items():
                if q in sources and q != p:
                    shared[q] += min(c, d)
        out, top = [], 0
        for bound, q in sorted(((b, q) for q, b in shared.items()), key=lambda x: (-x[0], x[1])):
            if bound < max(top, MIN_D):
                break
            h = self.lcs("dist", p, q)
            if h >= max(top, MIN_D):
                out.append((h, q))
                top = h
        if not out:
            return 0, 0, None
        cands = [(self.lcs("code", p, q), q) for h, q in out if h == top]
        most = max(h for h, _ in cands)
        ties = sorted(q for h, q in cands if h == most)
        twin, name = twin_of(p, sources), p.rsplit("/", 1)[-1]
        pick = twin if twin in ties else next((q for q in ties if q.rsplit("/", 1)[-1] == name), ties[0])
        return most, top, pick

    def run(self, p, sources):
        """(run, source): the longest block of consecutive lines of code (as code) that p and a source share, line for
        line, counted in the distinctive lines it holds; the source with the longest, then path order.  (0, None)
        when no source shares RUN distinctive lines."""
        da = collections.Counter(self.dist(p))
        shared = collections.Counter()
        for line, c in da.items():
            for q, d in self._index.get(line, {}).items():
                if q in sources and q != p:
                    shared[q] += min(c, d)
        a = self.code(p)
        best = (0, None)
        for q in sorted(q for q, b in shared.items() if b >= RUN):
            pos = collections.defaultdict(list)
            for j, x in enumerate(self.code(q)):
                pos[x].append(j)
            prev, top = {}, 0
            for x in a:
                inc = len(x.strip()) >= DISTINCT
                cur = {j: prev.get(j - 1, 0) + inc for j in pos.get(x, ())}
                if cur:
                    top = max(top, max(cur.values()))
                prev = cur
            if top > best[0]:
                best = (top, q)
        return best if best[0] >= RUN else (0, None)

    def describe(self, p, q):
        variants = {}

        def kinds_of(x, y):
            if x == y:
                return ()
            for line in (x, y):
                if line not in variants:
                    variants[line] = [masked(line, self.stems, kind) for kind in range(4)]
            return [kind for kind in range(4) if variants[x][kind] != variants[y][kind]]

        raw, a = self.code_all(p)
        sraw, b = self.code_all(q)
        pairs = align(a, b, lambda i, j: 4 - len(kinds_of(raw[i], sraw[j])))
        kinds = set()
        for i, j in pairs:
            kinds.update(kinds_of(raw[i], sraw[j]))
        return len(a) - len(pairs), len(a), len(b) - len(pairs), [KIND_NAMES[x] for x in sorted(kinds)]


def first_added_git(top, layout):
    """{path under the unit's proofs: the commit time of the earliest commit, on any ref, that added a file at that
    path in this unit or in one of its DONORS (each in the per-project layout, or proofs/<p>/<h>/<path> before it)},
    read from the git history of the checkout at top.  The order lives in the branches the unit was built on: main
    holds the unit's files from one squashed commit, so a clone of main alone gives no order, and first-added.tsv
    records it."""
    roots = []
    for unit in (layout.unit,) + tuple(tuple(d.split("/")) for d in layout.donors):
        roots += ["projects/%s/%s/proofs/" % unit, "proofs/%s/%s/" % unit]
    r = subprocess.run(["git", "-C", top, "log", "--all", "--diff-filter=A", "--name-only", "--format=C %ct", "--"]
                       + [x.rstrip("/") for x in roots], capture_output=True, text=True)
    if r.returncode:
        sys.exit("made_from.py: git log failed: %s" % r.stderr.strip())
    born, t = {}, None
    for line in r.stdout.split("\n"):
        if line.startswith("C "):
            t = int(line[2:])
            continue
        root = next((x for x in roots if line.startswith(x)), None)
        if root and t is not None:
            rel = line[len(root):]
            born[rel] = min(born.get(rel, t), t)
    return born


def pairs_of(path, what, second=str):
    """The first two columns of each row of a TSV at path, its blank lines, comment lines and header passed over, as
    (path, second(column 2)) pairs, read as each copy of this generator read them; ValueError naming the first line
    that has fewer than two columns or whose second column second() refuses (what says what a row holds)."""
    out = []
    with open(path, encoding="utf-8") as f:
        for n, line in enumerate(f, 1):
            if line.strip() and not line.startswith(("#", "path\t")):
                cols = line.rstrip("\n").split("\t")
                try:
                    if len(cols) < 2:
                        raise ValueError("one column")
                    out.append((cols[0], second(cols[1])))
                except ValueError:
                    raise ValueError("line %d is not %s: %r" % (n, what, line.rstrip("\n"))) from None
    return out


def first_added_of(path):
    """first-added.tsv at path as {path under the unit's proofs: commit time}; ValueError for a line that is not a
    path, a tab and a commit time."""
    return dict(pairs_of(path, "a path, a tab and a commit time", int))


def history_of(path):
    """A --history TSV at path as {path under the unit's proofs: the source the history names}; ValueError for a row
    that is not a path, a tab and a source."""
    return dict(pairs_of(path, "a path, a tab and a source"))


def first_added(top, layout):
    """first-added.tsv as {path under the unit's proofs: commit time}: the times the rule's history order reads."""
    born = first_added_of(os.path.join(top, layout.first_added))
    print("history: when each of %d paths first came (%s)" % (len(born), layout.first_added), file=sys.stderr)
    return born


HEADER = "path\theld\theld_distinctive\tlines_of_code\tshare\tbest_source\tdecision\tline"
LEFT_BARE = "left bare"   # the decision of a file that its unit declares carries no licence lines on purpose
# a row of a record for a file that this generator decided when the record was written and does not decide now: the
# file is not one it decides today -- it carries licence lines, or a comment of a program's instruction words -- so
# no run gives its row again, and the record keeps the fact instead of the row
STAMPED = "carries licence lines since"


def left_bare(top, files, layout):
    """{path: reason} from the unit's left-bare.tsv (path, reason): the files of this unit that carry no licence lines
    on purpose, each with the reason its row gives.  A row is a lane's written decision that the file's content is
    not the Anthropic-licensed file the rule names -- the rule's sources are what two files share today, and two files
    of ours can share a block with one of Anthropic's -- so the file takes no licence lines and is no source for
    another file either.  A row that is not one path and one reason, names a file that is not a file of this unit,
    names a file that carries licence lines, gives no reason, or names a path another row of the file names is a
    mistake and declares nothing -- a path named twice declares nothing whichever of its rows is the mistake, unless
    that mistake is a byte that is not UTF-8, which leaves no path to read: the run says so on stderr and goes on, so
    the file is decided by the rule alone, its row is not the record's, and --check reports the difference (exit 1,
    or 3 when that difference is drift: the module docstring, "Exit codes").  The file not being there at all is
    read the same way.  Both fail safe, and neither exits: a run that refuses is a check that cannot decide (2),
    which a workflow may pass over, so a mistake in this file would have been a way to turn the check off."""
    path = os.path.join(top, layout.left_bare_tsv)
    out, bad, seen = {}, [], set()
    if os.path.isfile(path):
        # bytes, decoded a line at a time: a byte that is not UTF-8 makes that row a mistake and no more.  Reading
        # the file as text would raise, and --check reports a run that stops on an exception as a defect of this
        # generator (exit 5, DEFECT), where the mistake is the tree's.
        try:
            with open(path, "rb") as f:
                raw = f.read().split(b"\n")
        except OSError as e:
            # a path that is there and cannot be read -- a symlink to a file of someone else's, a mode of 000 --
            # declares nothing, for the reason a byte that is not UTF-8 does: a run that stopped on it would be
            # reported as a defect of this generator
            raw, bad = [], ["cannot be read: %s" % e]
        for n, line8 in enumerate(raw, 1):
            try:
                line = line8.decode("utf-8")
            except UnicodeDecodeError:
                bad.append("line %d: not UTF-8" % n)
                continue
            if not line.strip() or line.startswith(("#", "path\t")):
                continue
            cols = line.rstrip("\r").split("\t")
            p, reason = cols[0], (cols[1].strip() if len(cols) == 2 else "")
            # every row whose bytes decode names a path, mistake or not, so a second row for a path is a second
            # row whatever the first one was: the first stops declaring, and the path is kept so no later row puts
            # it back.  A row that is not UTF-8 has no path to read, so it is a mistake of its own and no duplicate
            if p in seen:
                out.pop(p, None)
                bad.append("line %d: %s is named twice" % (n, p))
                continue
            seen.add(p)
            if len(cols) != 2:
                bad.append("line %d: %d column(s), not one path and one reason" % (n, len(cols)))
            elif p not in files:
                bad.append("line %d: %s is no .v file of this unit" % (n, p))
            elif not headerless(files[p]):
                bad.append("line %d: %s carries licence lines -- Anthropic's, the MIT tag, a Modified by line, or "
                           "a comment of a program's instruction words.  A file left bare carries none: take "
                           "them off, or take out this row" % (n, p))
            elif not reason:
                bad.append("line %d: %s gives no reason" % (n, p))
            else:
                out[p] = reason
    if bad:
        # a row that is a mistake declares nothing: the run says so and goes on, so the file is decided by the rule
        # alone and its row is not the record's, which --check reports as a difference (exit 1, or 3 when that
        # difference is drift: the module docstring, "Exit codes").  Exiting here instead would be a run that refuses,
        # which a workflow may pass over as a check that cannot decide (2).
        print("made_from.py: %s: %s" % (layout.left_bare_tsv, "; ".join(bad)), file=sys.stderr)
    print("left bare on purpose: %d files (%s)" % (len(out), layout.left_bare_tsv), file=sys.stderr)
    return out


# The rows of a record that a run on today's tree gives again (given_again) are those whose decision is one of
# REGENERABLE or is a LEFT_BARE decision.  Such a decision leaves its file as it was (--apply writes nothing to it), so
# the file is still one this generator decides, and a run gives its row again, byte for byte.  Every other decision is
# of a file no run decides: `made from ...` is one --apply carried out, which gave the file Anthropic's licence lines,
# `... (Apache-2.0 OR MIT tag becomes MIT)` gave it the MIT tag, and `Anthropic-licensed: tag Apache-2.0 becomes
# Apache-2.0 OR MIT` rewrote its tag, so the file is no longer one this generator decides and its row records the run
# on the tree before --apply; `carries licence lines since (was: ...)` is a row --record kept of a file this generator
# decided when the record was written and that has taken licence lines since, which a run cannot give again either.
# --check compares the rows a run gives again and each row of fewer than 7 columns (regenerable), and no row of another
# decision: comparing any of those would fail a correct record.
REGENERABLE = ("written here", "borderline: written here")


def given_again(row):
    """Whether this row is one a run on today's tree gives again: it has a decision column (7 or more columns), and
    its decision is one of REGENERABLE or the decision of a file left bare on purpose, which --apply leaves as it is
    as well.  `left bare` is matched whole and `left bare (overrules ...)` by that prefix, so the decisions a record
    can carry that this reads as given again are only a run's own.  The header is no such row.  check() reads a
    difference made only of such rows, none for a path that the record holds in a row of another kind, in a record that
    names no path twice, as drift."""
    cols = row.split("\t")
    return len(cols) >= 7 and (cols[6] in REGENERABLE or cols[6] == LEFT_BARE
                               or cols[6].startswith(LEFT_BARE + " (overrules "))


def regenerable(row):
    """Whether --check compares this row of the record: a run gives it again (given_again), or it has no decision
    column.  A row with no decision column is not one this generator writes, so it is compared too, and differs, and
    that difference is never drift."""
    return len(row.split("\t")) < 7 or given_again(row)


def generate(layout, top, history, out):
    """Start one run of the unit file on the tree at top (with --history history, unless None), in a process of its
    own (so its own hash seed), that writes its rows to out and no other file.  The unit file, not this file, is
    what runs: it holds the unit's data."""
    return subprocess.Popen([sys.executable, layout.unit_file, "--top", top, out]
                            + (["--history", history] if history else []),
                            stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)


def rows_of(path):
    """The lines of a TSV file, without their newlines."""
    with open(path, encoding="utf-8", newline="") as f:
        text = f.read()
    return text[:-1].split("\n") if text.endswith("\n") else text.split("\n")


def differing(have, want):
    """[(sign, row)]: where the sequences of rows have and want differ, in order: `-` a row of have that want lacks
    there, `+` a row of want that have lacks there.  Order is compared: a correct row at another place than the
    generator puts it, as a row added by hand at the end of a record is, shows under both."""
    out = []
    for tag, i1, i2, j1, j2 in difflib.SequenceMatcher(None, have, want, autojunk=False).get_opcodes():
        if tag != "equal":
            out += [("-", r) for r in have[i1:i2]] + [("+", r) for r in want[j1:j2]]
    return out


class Unreadable(Exception):
    """An input of a run or of --check that is missing or cannot be read, or oft lint's lexer when it does not load,
    refused with exit REFUSED before any run or write; the message names each such file, by its path from the top of
    the checkout, and why."""


class Fault(Exception):
    """A fault of this generator's own code, which no input should reach: a run left in a state its steps should never
    leave it in (the end of licensed_in_order: a chain of named origins that returns to a file of it).  The message
    says what the state is.  A run stops on it with exit DEFECT, 5, writing FAULT and the message on stderr with no
    traceback (main), and --check exits DEFECT when a run exits so (check): the made-from job of
    .github/workflows/pr.yml only warns on 2 (cannot decide), and on 3 (drift) for a unit that only a change to its
    proofs names, either of which would let a fault of this code pass, and its text for 1 says the record differs."""


# the exit code of a defect of this generator's own code: a run or --check that stops on a Fault or another uncaught
# exception (main), and --check when a run exits so, a run exits 0 and writes no OUT or an OUT that is not UTF-8, or
# the two runs differ (check).  Not 3, which is drift (DRIFT), nor 4, a refusal (REFUSED)
DEFECT = 5
# what begins the line a run writes on stderr when it stops on a Fault (main)
FAULT = "made_from.py: a fault of this generator: "


def unreadable(top, path, e):
    """What a refusal says of the input at path, which reading raised e for: it is missing, or why it cannot be
    read."""
    shown = os.path.relpath(path, top)
    return "%s is missing" % shown if isinstance(e, FileNotFoundError) else "%s cannot be read: %s" % (shown, e)


def text_of(path):
    """A file's text, read whole as UTF-8, its newlines as they are."""
    with open(path, encoding="utf-8", newline="") as f:
        return f.read()


def proof_file_counts(top, layout):
    """How many .v files the unit has outside provenance, and how many of those carry Anthropic's copyright line,
    each file read whole as UTF-8, as a run reads it.  Unreadable, naming the path, when the proofs folder is missing,
    a folder in it cannot be listed, or a .v file cannot be read (a byte that is not UTF-8, a path that cannot be
    opened): a run would fail on it.  A checkout that holds the licence folder but not the unit's proofs (a sparse
    checkout of the top of the tree) gives 0 and 0, which read_inputs refuses, and one whose .v files have all lost
    Anthropic's copyright line gives 0 for the second, which --check refuses: a run on either has no file to take
    licence lines from, so neither is a record that differs."""
    base, files, anth = os.path.join(top, layout.root_dir), 0, 0

    def unlisted(e):   # without this, os.walk passes over a folder it cannot list
        raise Unreadable(unreadable(top, e.filename or base, e))

    for d, dirs, names in os.walk(base, onerror=unlisted):
        dirs.sort()
        if os.path.relpath(d, base).split(os.sep)[0] == "provenance":
            continue
        for n in names:
            if n.endswith(".v"):
                files += 1
                path = os.path.join(d, n)
                try:
                    head = "\n".join(text_of(path).split("\n")[:HEADER_LINES])
                except (OSError, ValueError) as e:   # UnicodeDecodeError is a ValueError
                    raise Unreadable(unreadable(top, path, e))
                if ANTHROPIC.search(head):
                    anth += 1
    return files, anth


def read_inputs(layout, top, record, history, record_first_added=False):
    """Read each input of a run or of --check whole, before it runs, with the reader a run reads it with: record
    (the record --check checks, or the RECORD --record refreshes; None for a plain run) with rows_of, first-added.tsv
    with first_added_of (unless record_first_added: --record-first-added writes it), history (the history TSV, unless
    None) with history_of, the images' dune file and oft lint's lexer (LEXER) as UTF-8 text, and the proofs folder,
    which holds a .v file outside provenance, with proof_file_counts; then it loads the lexer (load_lexer), once its
    text reads.  (the record's rows, or None; the two counts of proof_file_counts), or Unreadable naming every input
    that is missing or cannot be read, and the lexer when it does not load, and why.  Such an input is refused rather
    than left to fail a run: the refusal (REFUSED) names the input as what to fix, where the run would stop on an
    uncaught exception (a lexer that exits while it loads aside), which main and --check report as a defect of this
    generator (DEFECT)."""
    problems = []

    def read(path, reader):
        try:
            return reader(path)
        except (OSError, ValueError) as e:   # UnicodeDecodeError is a ValueError
            problems.append(unreadable(top, path, e))

    rows = read(record, rows_of) if record else None
    if not record_first_added:
        read(os.path.join(top, layout.first_added), first_added_of)
    if history:
        read(history, history_of)
    read(os.path.join(top, layout.images_dune), text_of)
    files = anth = 0
    try:
        files, anth = proof_file_counts(top, layout)
        if not files:
            problems.append("%s holds no .v file outside provenance/: this checkout does not hold the unit's proofs"
                            % layout.root_dir)
    except Unreadable as e:
        problems.append(str(e))
    if read(os.path.join(top, LEXER), text_of) is not None:
        try:
            load_lexer(top)
        except (Exception, SystemExit) as e:   # what the fixed block's load of this file catches
            why = "%s: %s" % (type(e).__name__, e) if str(e) else type(e).__name__
            problems.append("%s cannot be loaded: %s" % (LEXER, why))
    if problems:
        raise Unreadable("; ".join(problems))
    return rows, files, anth


def check(layout, top, record, history):
    """--check: 0 when the record's header and the rows of it that --check compares (regenerable) are, in order, the
    rows a run on the tree at top gives; 1 when they are not and the difference is not drift, printing the rows that
    differ, or when the record names a path twice, and for no other cause; DRIFT (3) when they are not and the
    difference is drift: every row that differs is one a run gives again (given_again), and none of them names a path
    that the record holds in a row that is not, printing the rows that differ and then a line that says `--record`
    brings the record up to date; DEFECT (5) for a defect of this generator's own code: a run exits DEFECT (it stopped
    on a Fault or another uncaught exception; its stderr, printed, holds the fault or the traceback), a run exits 0 and
    writes no OUT, a run's OUT is not UTF-8, or the two runs differ; 2 when it cannot decide, for a cause outside this
    code: a run cannot start or its OUT cannot be read (OSError), a run is killed by a signal, or a run exits non-zero
    otherwise (a refusal of its own); REFUSED, before any run, when an input is missing or cannot be read, or oft lint's
    lexer does not load (read_inputs), or when no .v file of the unit carries Anthropic's copyright line (the checkout
    does not hold the unit's proofs, or every file lost that line).  It reads the runs' exit codes and OUT files, never
    the text of their stderr, which text of the tree (a path of left-bare.tsv, say) can shape.  An uncaught exception
    of the check itself exits DEFECT too (main)."""
    try:
        rows, files, anth = read_inputs(layout, top, record, history)
    except Unreadable as e:
        print("made_from.py --check: refusing the check: %s" % e)
        return REFUSED
    if not anth:
        print("made_from.py --check: refusing the check: %s holds %d .v file(s) outside provenance and none with "
              "Anthropic's copyright line: this checkout does not hold the unit's proofs, or every file lost that "
              "line" % (layout.root_dir, files))
        return REFUSED
    try:
        with tempfile.TemporaryDirectory(prefix="made_from-check-") as tmp:
            outs = [os.path.join(tmp, "run%d.tsv" % i) for i in (1, 2)]
            procs = [generate(layout, top, history, out) for out in outs]   # at once: the check takes one run's time
            ends = [proc.communicate()[1] for proc in procs]
            for out, proc, err in zip(outs, procs, ends):   # a defect of this code first: the check fails closed
                if proc.returncode == DEFECT:
                    print("made_from.py --check: a run stopped on a defect of this generator, which is what to fix "
                          "(it exited %d; its stderr follows):\n%s" % (DEFECT, err.strip()))
                    return DEFECT
                if not proc.returncode and not os.path.isfile(out):
                    print("made_from.py --check: a run exited 0 and wrote no OUT, a defect of this generator, which is "
                          "what to fix; its stderr:\n%s" % err.strip())
                    return DEFECT
            for proc, err in zip(procs, ends):
                if proc.returncode:
                    print("made_from.py --check: cannot decide: a run %s:\n%s"
                          % ("was killed by signal %d" % -proc.returncode if proc.returncode < 0
                             else "exited %d" % proc.returncode, err.strip()))
                    return 2
            try:
                runs = [rows_of(out) for out in outs]
            except UnicodeDecodeError as e:   # an OUT this generator wrote
                print("made_from.py --check: a run wrote an OUT that is not UTF-8, a defect of this generator, which "
                      "is what to fix: %s" % e)
                return DEFECT
    except OSError as e:   # a run that cannot start, or whose OUT cannot be read
        print("made_from.py --check: cannot decide: a run cannot start, or its OUT cannot be read: %s" % e)
        return 2
    if runs[0] != runs[1]:
        print("made_from.py --check: its two runs on the same tree differ, a defect of this generator, which is what "
              "to fix; the rows that differ (`-` the first run's, `+` the second's):")
        print("".join("%s %s\n" % d for d in differing(runs[0], runs[1])), end="")
        return DEFECT
    shown = os.path.relpath(record, top)
    # a record naming a path twice: the rows a run gives again can hold the run's row for a file beside a row of
    # its own that no run gives, which reads as a match while the record says two things about one file
    twice = sorted(p for p, n in collections.Counter(r.split("\t")[0] for r in rows[1:]).items() if n > 1)
    if twice:
        print("made_from.py --check: %s names %s twice: a record says one thing about each file of the unit"
              % (shown, ", ".join(twice)))
        return 1
    have = rows[:1] + [r for r in rows[1:] if regenerable(r)]   # the header, then the rows --check compares
    diff = differing(have, runs[0])
    if not diff:
        print("made_from.py --check: %s matches: its %d rows that a run gives again are the run's rows (its other "
              "%d rows are not ones a run gives again -- files that carry licence lines, and files no longer in "
              "the unit -- and are not compared)"
              % (shown, len(have) - 1, len(rows) - len(have)))
        return 0
    print("made_from.py --check: %s is not what this generator gives on this tree; the rows that differ (`-` the "
          "record has it there, `+` the generator gives it there; a row under both is in the record at another "
          "place):" % shown)
    print("".join("%s %s\n" % d for d in diff), end="")
    # a run gives a row of a decision --apply carries out wherever the file does not carry what that decision gives
    # it, and three different things look like that: the file was added or newly decided since the record was made
    # and never got it, it lost it, or the decision is wrong about the file.  The check cannot tell them apart, so it
    # names all three instead of sending the reader to --apply.
    unapplied = [r.split("\t")[0] for s, r in diff if s == "+" and r != HEADER and not regenerable(r)]
    if unapplied:
        print("of these, the `+` rows of %s are decisions --apply carries out, and those files do not carry what "
              "the decision gives them. Either the file never got it (added or newly decided since the record), or "
              "it lost it, or the decision is wrong about the file: read each row's decision and its source before "
              "running --apply, which would write what the decision gives each file." % ", ".join(unapplied))
    # drift: every row that differs is one a run gives again, and none of them is for a file that the record holds in a
    # row of another kind.  --record refuses a run that decides again a file of a row --apply carried out, and one of a
    # stamped row unless left-bare.tsv declares the file ("Refreshing the record").  A row of fewer than 7 columns is no
    # row this generator writes.  A difference with a row of either kind is 1
    other = {r.split("\t")[0] for r in rows[1:] if not given_again(r)}
    if all(given_again(r) and r.split("\t")[0] not in other for _sign, r in diff):
        print("made_from.py --check: every row that differs is one a run gives again, for a file that the record "
              "holds in no row of another kind: `made_from.py --record` brings the record up to date")
        return DRIFT
    return 1


NAMED = "made from (named origin)"   # the decision of a file made from the origin it names (licensed_in_order)
# licensed_in_order decides again, when a file joins the licensed files, only the undecided files that share a
# distinctive line with it (Unit.best and Unit.run read no source that shares none) or whose history row names it.
# False decides every undecided file again at each step: the same rows, more slowly, the run to compare it with.
SHORTCUT = True


def licensed_in_order(u, files, layout, bare, history, born, shortcut):
    """Decide the files a run decides (files, a list in any order, read in that order and never sorted: the result
    does not depend on it, every choice is made by numbers and paths), one file at a time, the strongest first:

    1. The licensed files, A, start as those with Anthropic's copyright line before the run (u.anthropic, after the
       tag pass), each with the licence lines it gives a file made from it (source_licence).
    2. Cascade, until nothing changes, over the undecided files not left bare (bare), each by its claim (claim): a file
       whose history row (history) waits and names a file of A is `made from (history)`; a file whose history row's
       wait failed (4) and that names no origin is `made from (history)` when A holds its history source; a file with
       no history row whose named origin (named_origins) is in A is `made from (named origin)`.  A file whose history
       row's wait failed and that names an origin is deferred (deferred): when no other file is left to join, each
       deferred file is decided against that one A (either), by its history source when A holds it, else by its named
       origin when A holds it, and the cascade goes on with the files that name the files decided.  Each file decided
       joins A; a deferred file that neither source decides stays undecided.
    3. Rule: each undecided file open to the rule (no named origin it waits for, not left bare, no history row that
       waits) takes the rule's decision (Unit.best, then Unit.run) against the files of A that the age test (born) lets
       be its source.  Of those it finds `made from`, the one with the largest held_d, then the largest held, then the
       first path, joins A with that decision.  Back to 2.
    4. Stall: when 3 finds none, each history row that still waits fails: 2 decides its file as one whose wait failed,
       and a file that names no origin is open to the rule as well; back to 2.  When none waits, each file not decided
       that waits for its named origin stops waiting for it when the origin is a tagged file (one that --apply gives
       the MIT tag, after which it names no origin), or when the file is on a cycle of named origins (named_origins:
       the first file of a cycle that joins A cannot take its origin) of which A holds no file and no file is tagged
       (may_stop): one not left bare is open to the rule, and 2 still decides it if its origin, or its history source,
       joins A while it is undecided; one left bare takes at the end what 5 gives it.  A file of a cycle waits again
       once A holds a file of its cycle.  Back to 3.  When there is none, the run ends.
    5. End: each file still undecided takes its history source when the final A holds it, else its named origin when
       the final A holds it (either; only a file left bare, which 2 passes over, can have one of them in A then, and
       its history row's wait can stand to the end, since a file left bare never stalls); its history decision names
       no origin that is a tagged file the final A does not hold, since --apply gives that the MIT tag.  Else each
       file that waits for no origin takes the rule's decision against the final A (written here, or borderline); a
       file whose named origin is not in A and that still waits for it takes its origin's decision (the origin
       decided first), with its own counts and best source, and the origin's reason when that is a `left bare` one (a
       `left bare` one is plain `left bare` for a tagged file, which --apply gives the MIT tag); a file left bare
       takes `left bare`, or `left bare (overrules <what 2 to 5 give it>)`, against the final A, and never joins A.

    A file joins A with a source already in A and is not decided again, so no chain of sources returns to a file of
    the chain, and each ends at a file with Anthropic's lines before the run.  An undecided file that is not deferred
    has at most one claim at any moment, and the deferred files are decided together against one A, so no decision
    depends on the order of the files.  shortcut: SHORTCUT.
    (result {file: (held, held_d, lines of code, share, source, decision)}, taken {file made from: the licence lines
    written at its top}, written {file made from: its text as written}, reasons {file: the reason of left-bare.tsv its
    line carries}, (files licensed by named origin, by history, by the rule, steps))."""
    older = lambda q, p: not (q in born and p in born and born[q] > born[p])   # the rule's age test
    origins, cycle = named_origins(u, files, layout.unit)
    lic = {q: source_licence(u.files[q]) for q in sorted(u.anthropic)}   # A: each file's lines, copied whole
    licensed = sorted(lic)   # A's paths in path order: the rule's candidate sources
    result, taken, written, reasons, ruled, failed = {}, {}, {}, {}, {}, set()
    counts = collections.Counter()
    waiters = collections.defaultdict(list)   # a file -> the files whose history row or named origin names it
    near = collections.defaultdict(list)      # a distinctive line -> the files to decide that hold it (shortcut)
    released = set()   # the files that stopped waiting for an origin not in A, a tagged one or one of a cycle (step 4)
    for p in files:
        for source in (history.get(p), origins.get(p)):
            if source is not None:
                waiters[source].append(p)
        if shortcut:
            for line in dict.fromkeys(u.dist(p)):   # each of its lines once, in their first order
                near[line].append(p)

    def rule(p):
        """The rule's decision for p against the files of A its age test lets be its source, kept until a file that
        shares a distinctive line with p joins A."""
        if p in ruled:
            return ruled[p]
        m = len(u.code(p))
        srcs = {q: lic[q] for q in licensed if older(q, p)}
        held, held_d, q = u.best(p, srcs)
        share = held / m if m else 0.0
        if q and held_d >= HELD_D:
            decision = "made from (block)"
        elif q and share >= SHARE:
            decision = "made from (share)"
        else:
            run, rq = u.run(p, srcs)
            if rq:
                ruled[p] = against(p, rq, "made from (run of %d)" % run)
                return ruled[p]
            decision = ("borderline: written here" if q and (share >= BORDER or held_d >= HELD_D // 2)
                        else "written here")
        ruled[p] = (held, held_d, m, share, q, decision)
        return ruled[p]

    def against(p, q, decision):
        """The row of p made from q with decision, held and held_d counted against q whatever their size: q is the
        source its history row or its named origin gives (no score, no age test), or the source of a run."""
        held, held_d, m = u.lcs("code", p, q), u.lcs("dist", p, q), len(u.code(p))
        return held, held_d, m, held / m if m else 0.0, q, decision

    def by_history(p):
        o = origins.get(p)
        return "made from (history)" if o in (None, history[p]) else "made from (history; it names %s)" % o

    def join(p, row):
        """p is decided made from the source of row and joins A; the files whose history row or origin names it."""
        result[p] = row
        q = row[4]
        # a comment of the file's own that is exactly one the source gives above it is not written again: it stands
        # once, as the source's; the file's body below stays as it is
        taken[p] = lic[q] + [x for x in own_lines(u.files[p]) if x not in lic[q]]
        if row[5] != NAMED:   # a file made from its named origin takes the origin's lines and no sentence
            n, mm, k, kinds = u.describe(p, q)
            taken[p].append(sentence("%s/%s" % (layout.logical, q), kinds, n, mm, k))
        written[p] = "\n".join(taken[p]) + "\n" + licence_comments(u.files[p])[1]
        # what p gives a file made from it: the licence comments among the opening comments of p as it is written
        # (source_licence), the rule of a source this run does not write.  taken[p] alone would leave out p's own
        # `Modified by` lines that stay in its body, below a note or below line 10
        lic[p] = source_licence(written[p])
        bisect.insort(licensed, p)
        if shortcut:
            for line in u.dist(p):
                for h in near.get(line, ()):
                    ruled.pop(h, None)
        else:
            ruled.clear()
        return waiters.get(p, [])

    def waits(p):
        """p's history row holds it back: p has one, and its wait has not failed at a stall (step 4).  A file left bare
        never stalls, so its wait can stand to the end, where either reads its history row as for any file (step 5)."""
        return p in history and p not in failed

    def may_stop(p):
        """p may stop waiting for its named origin at a stall (step 4): the origin is a tagged file, which --apply gives
        the MIT tag when A does not hold it, or p is on a cycle of named origins of which A holds no file and no file
        is tagged, which --apply leaves a cycle.  A run on the output of --apply then reads no origin of p, or the
        same cycle.  Once A holds a file of p's cycle, that run finds no cycle there, so p waits again."""
        if tagged(u.files[origins[p]]):
            return True
        return p in cycle and not any(q in lic or tagged(u.files[q]) for q in cycle[p])

    def waits_for_origin(p):
        """p names an origin that A does not hold, and has not stopped waiting for it at a stall, or waits again
        (may_stop, step 4)."""
        return p in origins and origins[p] not in lic and not (p in released and may_stop(p))

    def deferred(p):
        """p's history row's wait failed and p names an origin: a cascade defers p until no other file is left to
        join, and either then decides it (step 2)."""
        return p in failed and p in origins

    def either(p):
        """(source, decision) of p's history row when A holds its source, else of p's named origin when A holds that,
        else None.  Its three callers: claim, for a file not deferred, unless its history row waits for a source that
        A does not hold (claim relies on this order, history first: a row that waits decides its file once A holds its
        source, whatever its named origin); cascade, for each deferred file (step 2); and given, for a file still
        undecided at the end (step 5)."""
        if history.get(p) in lic:
            return history[p], by_history(p)
        return (origins[p], NAMED) if origins.get(p) in lic else None

    def claim(p):
        """(source, decision) that decides p, a file not deferred, in a cascade against A, or None: while p's history
        row waits, it alone can decide p, when A holds its source; once its wait failed (p names no origin, or it would
        be deferred), the history row decides p when A holds its source, even when that joins A later; and a file with
        no history row is decided by its named origin when A holds it.  So each file not deferred has at most one
        claim at any moment, and none depends on the order of the files."""
        return None if waits(p) and history[p] not in lic else either(p)

    def take(p, c):
        """p joins A by its history row or its named origin, c (source, decision); the files that name p."""
        counts["named origin" if c[1] == NAMED else "history"] += 1
        return join(p, against(p, *c))

    def cascade(todo):
        """Step 2 from the files of todo: each file not deferred joins A by its claim, and the files that name it are
        read next; each deferred file read is set aside (deferred_now) until no other file is left, and then the files
        set aside are decided against that one A (either), all before any of them joins, and the files that name those
        that join are read next."""
        todo, deferred_now = collections.deque(todo), set()
        while todo or deferred_now:
            while todo:
                p = todo.popleft()
                if p in result or p in bare:
                    continue
                if deferred(p):
                    deferred_now.add(p)
                    continue
                c = claim(p)
                if c:
                    todo.extend(take(p, c))
            decided = [(p, either(p)) for p in sorted(deferred_now)]   # one A for all of them
            deferred_now.clear()
            for p, c in decided:
                if c:
                    todo.extend(take(p, c))

    cascade(files)
    steps = 0
    while True:
        steps += 1
        pick = None
        for p in files:
            if p in result or p in bare or waits_for_origin(p) or waits(p):
                continue
            row = rule(p)
            if row[5].startswith("made from") and (pick is None or (-row[1], -row[0], p) < pick[0]):
                pick = ((-row[1], -row[0], p), row)
        if pick:
            counts["rule"] += 1
            cascade(join(pick[0][2], pick[1]))
            continue
        stalled = [p for p in files if p not in result and p not in bare and waits(p)]
        if stalled:
            failed.update(stalled)
            cascade(stalled)
            continue
        # an origin that carries Anthropic's tag alone and that A does not hold is one --apply gives the MIT tag, and
        # a run on that output reads no origin there: the file is open to the rule now, unless it is left bare, as it
        # is then where a run still decides it.  And the first file of a cycle of named origins that joins A cannot
        # take its origin: while A holds no file of a cycle, and no file of it is tagged, those of its files not left
        # bare are open to the rule, and when the run licenses one of them, the others wait again, and the file that
        # names it takes it, so that a run on the output of --apply (where that file carries Anthropic's lines, and the
        # cycle is gone) gives each file of the cycle that it still decides the same row (may_stop)
        freed = [p for p in files if p not in result and waits_for_origin(p) and may_stop(p)]
        if not freed:
            break
        released.update(freed)

    def given(p):
        """What steps 2 to 5 give p against the final A, and the reason of left-bare.tsv its line carries, if any."""
        c = either(p)
        o = origins.get(p)
        if c and o is not None and o not in lic and tagged(u.files[o]):
            # a history row decides p, and its origin is a tagged file that A does not hold: --apply gives that the
            # MIT tag, after which p names no origin, so the decision names none either
            c = c[0], "made from (history)"
        if c:
            return against(p, *c), None
        if not waits_for_origin(p):
            return rule(p), None
        # the origin's own decision, which holds no tag suffix (the rows add it, for the file's own tag); a `left bare`
        # one is plain `left bare` for a tagged file, whose row then gives no decision that --check compares, since
        # --apply gives the file the MIT tag
        decision = result[o][5]
        if decision.startswith(LEFT_BARE) and tagged(u.files[p]):
            decision = LEFT_BARE
        return rule(p)[:5] + (decision,), reasons.get(o) if decision.startswith(LEFT_BARE) else None

    for p in files:
        # an origin is decided before the files that name it: each chain of named origins ends at a file that waits for
        # no origin.  On a cycle of which A holds a file, that is the file that names it; on a cycle with a tagged
        # file, the file that names that one, which stopped waiting at a stall; on any other, each file (may_stop).  A
        # chain that returns to a file of it, which this walk would follow for ever, is a fault of this code: the run
        # stops there with a Fault that names the chain, and exits DEFECT, 5 (main)
        chain, x = [], p
        while x not in result:
            if x in chain:
                raise Fault("at the end of the run, the chain of named origins %s returns to %s, a file of it: no file "
                            "of its cycle stopped waiting for its origin at a stall (licensed_in_order: may_stop, "
                            "released, waits_for_origin)" % (" -> ".join(chain), x))
            chain.append(x)
            if not waits_for_origin(x):
                break
            x = origins[x]
        for x in reversed(chain):
            row, reason = given(x)
            if x in bare:
                # a file left bare on purpose takes no licence lines, so it is no source for another file either: its
                # row says what the run would give it and that the declaration overrules it
                d = row[5]
                left = LEFT_BARE if d in REGENERABLE or d.startswith(LEFT_BARE) else "%s (overrules %s)" % (
                    LEFT_BARE, d)
                row, reason = row[:5] + (left,), bare[x]
            result[x] = row
            if reason is not None:
                reasons[x] = reason
    return result, taken, written, reasons, (counts["named origin"], counts["history"], counts["rule"], steps)


def to_decide(u):
    """The tag pass, then the files a run decides.  The tag pass: in each file with Anthropic's copyright line,
    Anthropic's tag in the earlier bundle's form, `Apache-2.0`, becomes the final package's `Apache-2.0 OR MIT` (the
    release carries the final package), written into u.files; nothing else of the file changes.  The files decided
    are then those of u.files with no licence lines (headerless), with Anthropic's tag alone (tagged) or with
    `Modified by` lines alone (modified_only).  ({file the tag pass rewrites: its text}, the files to decide in path
    order)."""
    line2 = {}
    for p in sorted(u.anthropic):
        lic, body = licence_lines(u.files[p])
        if BUNDLE_TAG in lic:
            line2[p] = u.files[p] = "\n".join([APACHE_TAG if x == BUNDLE_TAG else x for x in lic] + [body])
    return line2, sorted(p for p, t in u.files.items() if headerless(t) or tagged(t) or modified_only(t))


def decide(layout, args):
    """A run: decide the unit's files on the tree at args.top, refuse what must not be written, then write OUT (and,
    with --apply, the files).  Its inputs are read first (read_inputs; --record's RECORD among them) and oft lint's
    lexer loaded, and an input that is missing or cannot be read, or a lexer that does not load, is refused with exit
    REFUSED.  Every refusal is decided before OUT or a .v file is written (--record-first-added writes first-added.tsv
    first)."""
    try:
        # the rows of the record --record refreshes; None without --record
        record_rows = read_inputs(layout, args.top, args.out if args.record else None, args.history,
                                  args.record_first_added)[0]
    except Unreadable as e:
        print("made_from.py: refusing the run: %s" % e, file=sys.stderr)
        sys.exit(REFUSED)
    u = Unit(args.top, layout)
    original = dict(u.files)
    if args.record_first_added:
        git_born = first_added_git(args.top, layout)
        missing = sorted(p for p in u.files if p not in git_born)
        if missing:
            sys.exit("made_from.py: no commit adds %s" % " ".join(missing[:5]))
        with open(os.path.join(args.top, layout.first_added), "w", encoding="utf-8") as f:
            f.write("path\tfirst_added_commit_time\n")
            f.write("".join("%s\t%d\n" % (p, git_born[p]) for p in sorted(u.files)))
    line2, heads = to_decide(u)
    history = history_of(args.history) if args.history else {}
    bare = left_bare(args.top, u.files, layout)   # the files this unit declares carry no licence lines on purpose
    born = first_added(args.top, layout)
    result, taken, written, reasons, (by_origin, by_history, by_rule, steps) = licensed_in_order(
        u, heads, layout, bare, history, born, SHORTCUT)
    print("licensed in this run, one file at a time: %d by named origin, %d by history, %d by the rule, in %d step(s)"
          % (by_origin, by_history, by_rule, steps), file=sys.stderr)
    rows, writes, bad = [], {}, []
    for p in heads:
        held, held_d, m, share, q, decision = result[p]
        body = licence_comments(u.files[p])[1]   # the file without its own licence comments; a headerless file whole
        # the reason its row of left-bare.tsv gives, for a file left bare (nothing is written to it: it is headerless,
        # and its decision is no `made from`) or for the origin left bare whose decision the file takes
        line = reasons.get(p, "")
        if decision.startswith("made from"):
            line = "-" if decision == NAMED else taken[p][-1]   # the lines of a named origin hold no sentence
            new = written[p]
            # lint reads the copyright and the tag in the first HEADER_LINES lines of the file as written (a comment
            # of several lines counts each of its lines); `Modified by` lines may go on below, a source's among them
            # (source_licence takes them with no bound of lines).  The lines taken hold Anthropic's copyright line, or
            # the file would be written as one this generator still decides
            tags = [n for n, x in zip(lines_of(taken[p]), taken[p]) if not x.startswith("(* Modified by ")]
            if (code_lines(new) != code_lines(body) or (tags and tags[-1] >= HEADER_LINES)
                    or not any(ANTHROPIC.search(x) for x in taken[p] if not x.startswith("(* Modified by "))):
                bad.append(p)
            writes[p] = new
        elif tagged(u.files[p]):
            writes[p] = "\n".join([MIT_TAG] + own_lines(u.files[p]) + [body])   # written here: the repository's MIT
            decision += " (Apache-2.0 OR MIT tag becomes MIT)"
        rows.append((p, held, held_d, m, "%.3f" % share, q or "-", decision, line))
    for p, new in line2.items():
        writes[p] = new
        rows.append((p, "-", "-", "-", "-", "-", "Anthropic-licensed: tag Apache-2.0 becomes Apache-2.0 OR MIT", ""))
    given = ["\t".join(str(x) for x in r) for r in rows]
    # every file written keeps its lines of code, read over the whole file (comments nest)
    bad += [p for p, new in writes.items() if code_lines(new) != code_lines(original[p]) and p not in bad]
    # no file is written whose comments or string literals do not close, by lint's own lexer: such a file is found
    # otherwise only when a build reaches it ("Unterminated comment"), long after the licence commit
    open_at = {p: unclosed(new) for p, new in writes.items()}
    unbalanced = sorted(p for p, what in open_at.items() if what)
    if unbalanced:
        sys.exit("made_from.py: refusing to write a file with an unclosed %s, by oft lint's lexer (%s): %s"
                 % (" or ".join(sorted({open_at[p] for p in unbalanced})), LEXER, " ".join(unbalanced)))
    if bad:
        sys.exit("made_from.py: the licence lines would change the code of, or not fit in the first %d lines of, or "
                 "hold no Anthropic copyright line for: %s" % (HEADER_LINES, " ".join(bad)))
    if args.record:
        # A run gives a row only for the files it decides, so its rows are not the record.  A refresh keeps the rows of
        # the record that no run gives again -- what --apply wrote, and what some other change stamped since -- for the
        # files this run gives no row for, and takes this run's rows, all in path order.  Keeping the stamped rows is
        # what lets a licence line that goes missing later be seen: without them the record would forget that it ever
        # decided the file.
        # A file deleted from the unit: the row of a decision --apply carried out stays, because it records what the
        # repository did to that file and nothing in the tree can say it again, while the row of a decision a run
        # gives again goes, because the file is not there to decide.  So a file deleted and then written again at
        # the same path meets the refusal below, and its author says in left-bare.tsv what the new file is.
        old = record_rows[1:]
        kept = []
        for r in old:
            cols = r.split("\t")
            p = cols[0]
            if not regenerable(r):
                kept.append(r)                     # --apply wrote it, or an earlier refresh found it stamped
            elif len(cols) > 6 and p not in result and p in u.files:
                cols[6] = "%s (was: %s)" % (STAMPED, cols[6])   # decided then, not decided now: it took lines since
                kept.append("\t".join(cols))
        held_back = {r.split("\t")[0] for r in kept}
        # the rows of what --apply carried out, apart from those an earlier refresh found stamped since: a
        # declaration retires the second, because such a row is this generator's own observation, and must not
        # retire the first, because that row records what this repository did to the file
        applied = {r.split("\t")[0] for r in kept if not r.split("\t")[6].startswith(STAMPED)}
        # The refusals of --record.  Each exits 1 and writes nothing, and the first that applies is the one a run gives.
        # A kept row (held_back) is an applied row, what --apply wrote (`made from ...`, the MIT tag, the tag pass:
        # applied), or a stamped row (`carries licence lines since ...`), of a file this generator decided that took
        # licence lines since.  A refresh never replaces a kept row with the row of a decision --apply carries out.  A
        # row of left-bare.tsv declares a file only when the file carries no licence lines at all (left_bare()); a
        # declaration retires a stamped row, and never an applied row, which records what this repository did.
        # undone: the run decides a file that left-bare.tsv declares and whose kept row is an applied row.  Give the
        # file back what --apply wrote and take out its declaration; or, when its content is this unit's own, take the
        # applied row out of the record by hand, where it stands in the record's diff, and refresh.
        # back: the run decides a file that the record keeps a row for and left-bare.tsv does not declare: the file has
        # lost the licence lines its row records, or that row was written for a bare file.  Give the file those licence
        # lines; or, when its content is this unit's own, take every licence line left off the file and declare it,
        # after taking its row out of the record by hand when that row is an applied row.
        # replacing: the run gives the row of a decision --apply carries out for a file the record keeps a row for, with
        # --apply or without.  Only the tag pass's row comes here: a file the run decides that the record keeps a row
        # for meets undone or back first, or its row is `left bare`.  Give the file by hand what that decision gives it
        # (the tag Apache-2.0 OR MIT in place of Apache-2.0), and refresh.
        # unwritten: without --apply, the run gives the row of a decision --apply carries out for a file the record
        # keeps no row for.  No run gives such a row again, so --check would report it on every run.  The file never got
        # what its decision gives it (added or newly decided since the record), or it lost its licence lines, or the
        # decision is wrong about it: read the decision and its source.  A file decided with the MIT tag keeps
        # Anthropic's tag without Anthropic's copyright line, and the code cannot tell which of two files it is: this
        # unit's own work written with Anthropic's tag, for which --record --apply is right, or Anthropic's file that
        # lost that line, for which a person gives the line back by hand, since --apply would put our MIT tag on it.
        # Its history (git log of the file, and where it was copied from) tells which.  When the decision is right,
        # --record --apply writes the file and its row; when the file's content is this unit's own and the file carries
        # no licence lines, declare it.
        # A file the record holds no row for at all is outside what it can tell: see "What neither can see" in the
        # docstring.
        undone = sorted(p for p in result if p in bare and p in applied)
        back = sorted(p for p in result if p in held_back and p not in bare)
        # this run's rows, the tag pass's among them, each read as given_again reads it
        refused = sorted((r[0], r[6]) for r, text in zip(rows, given)
                         if not given_again(text) and (not args.apply or r[0] in held_back))
        replacing = [x for x in refused if x[0] in held_back]
        unwritten = [x for x in refused if x[0] not in held_back]
        if undone:
            sys.exit("made_from.py: %s declares %s, whose row of this record says --apply wrote the file: an applied "
                     "row, which a declaration never retires.  Give the file back what --apply wrote and take out its "
                     "declaration; or, when its content is this unit's own, take that row out of the record by hand, "
                     "where it stands in the record's diff, and refresh again (the comment above the refusals in "
                     "decide() says why)"
                     % (layout.left_bare_tsv, " ".join(undone)))
        if back:
            sys.exit("made_from.py: a run decides %s again, which the record accounts for as a file that carries "
                     "licence lines: the file has lost the licence lines its row records, or that row was written for "
                     "a bare file.  Give the file those licence lines; or, when its content is this unit's own, take "
                     "every licence line left off it (a row of %s declares no file that carries one) and declare it in "
                     "%s with a reason, after taking its row out of the record by hand when that row is an applied row "
                     "(`made from ...`, the MIT tag, the tag pass): a declaration retires only a stamped row"
                     % (" ".join(back), layout.left_bare_tsv, layout.left_bare_tsv))
        if replacing:
            sys.exit("made_from.py: this run gives the row of a decision --apply carries out for a file the record "
                     "keeps a row for: %s.  A refresh never replaces a kept row with such a row, with --apply or "
                     "without.  Give the file by hand what that decision gives it (for the tag pass, the tag "
                     "Apache-2.0 OR MIT in place of Apache-2.0), then refresh again"
                     % "; ".join("%s, decided `%s`" % x for x in replacing))
        if unwritten:
            sys.exit("made_from.py: without --apply, this run gives the row of a decision --apply carries out for a "
                     "file the record keeps no row for: %s.  No run gives such a row again, so --check would report it "
                     "on every run.  The file never got what its decision gives it (added or newly decided since the "
                     "record), or it lost its licence lines, or the decision is wrong about it: read each decision and "
                     "its source.  A file decided with the MIT tag keeps Anthropic's tag without Anthropic's copyright "
                     "line, and this generator cannot tell which of two files it is: read its history (git log of the "
                     "file, and where it was copied from).  When it is this unit's own work written with Anthropic's "
                     "tag, --record --apply is right.  When it is Anthropic's file and lost its copyright line, give "
                     "that line back by hand, since --record --apply would put our MIT tag on it.  When the decision "
                     "is right, --record --apply writes the file and its row.  When the file's content is this unit's "
                     "own and it carries no licence lines, a row of %s declares it, with a reason"
                     % ("; ".join("%s, decided `%s`" % x for x in unwritten), layout.left_bare_tsv))
        this_run = {r[0] for r in rows}
        kept = [r for r in kept if r.split("\t")[0] not in this_run]
        given = sorted(kept + given, key=lambda r: r.split("\t")[0])
    with open(args.out, "w", encoding="utf-8") as f:
        f.write(HEADER + "\n")
        f.write("".join(r + "\n" for r in given))
    if args.apply:
        for p, new in writes.items():
            with open(os.path.join(args.top, layout.root_dir, p), "w", encoding="utf-8", newline="") as f:
                f.write(new)
    counts = collections.Counter(r[6] for r in rows)
    print("files decided: %d (no licence lines, Anthropic's tag alone, or Modified by lines alone); "
          "Anthropic-licensed: %d; %s; %d files %s%s"
          % (len(heads), len(u.anthropic), "; ".join("%s: %d" % kv for kv in sorted(counts.items())), len(writes),
             "written" if args.apply else "to write (no --apply)",
             "; %d rows kept of files that carry licence lines" % (len(given) - len(rows)) if args.record else ""))


# The unit file's end, byte for byte: unit_data() refuses a unit file that does not end with this text.
FIXED_BLOCK = '''\
# The fixed block: the same text, byte for byte, in every unit's made_from.py, to the end of the file.  It loads
# dev/licence/made_from.py from the checkout this file is in and calls it with this file, whose data it reads.
import importlib.util
import os
import sys

_GENERATOR = os.path.join(os.path.dirname(os.path.abspath(__file__)), *[os.pardir] * 7, "dev", "licence",
                          "made_from.py")
try:
    _SPEC = importlib.util.spec_from_file_location("licence_made_from", _GENERATOR)
    _MODULE = importlib.util.module_from_spec(_SPEC)
    _SPEC.loader.exec_module(_MODULE)
    _MAIN = _MODULE.main
except (Exception, SystemExit) as _ERROR:   # a load that fails is exit 4, never 1 (the record differs) or 2 (a warning)
    print("made_from.py: cannot load the shared generator %s: %r" % (os.path.normpath(_GENERATOR), _ERROR),
          file=sys.stderr)
    sys.exit(4)
_MAIN(__file__)
'''
UNIT_PATH = "projects/<p>/<h>/proofs/provenance/evidence/licence/made_from.py"
DATA = ("DONORS", "HISTORY")
DONOR = re.compile(r"[^/\s]+/[^/\s]+")
CODING = re.compile(r"^[ \t\f]*#.*?coding[:=][ \t]*([-\w.]+)")   # a coding declaration: PEP 263's regular expression
# the exit code of a refused unit file, of a fixed block that cannot load this file, and of an input of a run or of
# --check that is missing or cannot be read, or of oft lint's lexer when it does not load (read_inputs)
REFUSED = 4
# the exit code of --check when the record names no path twice and differs from a run only in drift: every row that
# differs is one a run gives again (given_again), and none of them names a path that the record holds in a row that is
# not.  `--record` brings such a record up to date.  check() alone gives it
DRIFT = 3


class Refused(Exception):
    """A unit file that holds more than its docstring, its data and the fixed block, or that is at another path; the
    message names the part."""


def layout_of(path):
    """The Layout of the unit file at path, from its path and its text, read here before any other file; Refused
    when it is not a unit file."""
    parts = os.path.abspath(path).split(os.sep)
    if (len(parts) < 9 or parts[-8] != "projects" or not parts[-7] or not parts[-6]
            or parts[-5:] != ["proofs", "provenance", "evidence", "licence", "made_from.py"]):
        raise Refused("its path is not %s" % UNIT_PATH)
    try:
        with open(path, encoding="utf-8", newline="") as f:
            text = f.read()
    except (OSError, UnicodeDecodeError) as e:
        raise Refused("it cannot be read, or is not UTF-8 text: %s" % e)
    donors, history = unit_data(text)
    return Layout(path, donors, history)


def unit_data(text):
    """(DONORS, HISTORY) of a unit file's text, or Refused naming the part that is not allowed: the whole text is an
    optional #! line and comment lines, the docstring (one sentence, naming dev/licence/made_from.py), DONORS = a
    tuple of "<project>/<harness>" string literals, HISTORY = a file name string literal or None, with comment lines
    and blank lines between them, then FIXED_BLOCK to the end of the file.  First of all, a byte order mark at the
    start of the text and a coding declaration (PEP 263) on its line 1 or 2, of any encoding, utf-8 included, are
    refused: Python drops the mark and reads the file in the encoding the declaration names, while this check reads
    the text as UTF-8 and ast.parse of a str passes over a declaration, so the two could read two texts, and a unit
    file needs neither."""
    lines = text.split("\n")
    if text.startswith("\ufeff"):
        raise Refused("line 1: a byte order mark (U+FEFF) at its start: Python reads the file without it, another "
                      "text than this check reads; a unit file needs none")
    # Python finds a declaration in the first two lines broken at \r, \n or \r\n, and tokenize.detect_encoding (which
    # tokenize.open uses) in the first two broken at \n alone: both readings are checked
    for split in (re.split(r"\r\n|\r|\n", text, maxsplit=2), lines):
        for n, line in enumerate(split[:2], 1):
            if CODING.match(line):
                raise Refused("line %d: a coding declaration (%r): Python would read the file in the encoding it "
                              "names, which can give another text than this check reads; a unit file needs none, "
                              "utf-8 included" % (n, line))
    first = FIXED_BLOCK.split("\n", 1)[0]
    if first not in lines:
        raise Refused("it has no fixed block: the line %r that starts FIXED_BLOCK of dev/licence/made_from.py is not "
                      "in it" % first)
    k = lines.index(first)
    tail = "\n".join(lines[k:])
    if tail != FIXED_BLOCK:
        if tail.startswith(FIXED_BLOCK):
            raise Refused("line %d: text after the fixed block: %r"
                          % (k + FIXED_BLOCK.count("\n") + 1, tail[len(FIXED_BLOCK):].split("\n", 1)[0]))
        have, want = tail.split("\n"), FIXED_BLOCK.split("\n")
        i = next((i for i, (a, b) in enumerate(zip(have, want)) if a != b), None)
        if i is None:
            raise Refused("the file ends at line %d, inside the fixed block: FIXED_BLOCK goes on to its line %d%s"
                          % (len(lines), len(want) - 1, " and its last newline" if len(have) == len(want) - 1 else ""))
        raise Refused("line %d is not line %d of the fixed block: %r, where FIXED_BLOCK has %r"
                      % (k + i + 1, i + 1, have[i], want[i]))
    head = "\n".join(lines[:k]) + "\n"
    try:
        tree = ast.parse(head)
    except SyntaxError as e:
        raise Refused("line %s: not Python: %s" % (e.lineno, e.msg))
    body = tree.body
    if not (body and isinstance(body[0], ast.Expr) and isinstance(body[0].value, ast.Constant)
            and isinstance(body[0].value.value, str)):
        raise Refused("it has no docstring: its first statement must be a docstring that states the rule in one "
                      "sentence and names dev/licence/made_from.py")
    doc = body[0].value.value.strip()
    if "dev/licence/made_from.py" not in doc:
        raise Refused("line %d: the docstring does not name dev/licence/made_from.py" % body[0].lineno)
    if not doc.endswith(".") or re.search(r"[.!?]\s+\S", doc):
        raise Refused("line %d: the docstring is not one sentence" % body[0].lineno)
    values = {}
    for stmt in body[1:]:
        what = {ast.FunctionDef: "a def", ast.AsyncFunctionDef: "a def", ast.ClassDef: "a class",
                ast.Import: "an import", ast.ImportFrom: "an import"}.get(type(stmt))
        if what:
            raise Refused("line %d: %s; a unit file holds only its docstring, DONORS, HISTORY and the fixed block"
                          % (stmt.lineno, what))
        if not isinstance(stmt, ast.Assign):
            raise Refused("line %d: a statement (%s) that is not an assignment of a data name"
                          % (stmt.lineno, type(stmt).__name__))
        if len(stmt.targets) != 1 or not isinstance(stmt.targets[0], ast.Name):
            raise Refused("line %d: an assignment that is not of one data name (%s)" % (stmt.lineno, " or ".join(DATA)))
        name = stmt.targets[0].id
        if name not in DATA:
            raise Refused("line %d: the unknown name %s; a unit file's data names are %s"
                          % (stmt.lineno, name, " and ".join(DATA)))
        if name in values:
            raise Refused("line %d: %s is given a second time" % (stmt.lineno, name))
        if DATA.index(name) != len(values):
            raise Refused("line %d: %s before %s; the data names come in this order: %s"
                          % (stmt.lineno, name, DATA[len(values)], ", ".join(DATA)))
        values[name] = literal_of(name, stmt.value)
    for name in DATA:
        if name not in values:
            raise Refused("it gives no %s" % name)
    # the text outside the statements: comment lines and blank lines, and after a statement on its last line a comment
    spans = {}
    for stmt in body:
        for n in range(stmt.lineno, stmt.end_lineno + 1):
            spans[n] = stmt
    for n, line in enumerate(lines[:k], 1):
        stmt = spans.get(n)
        if stmt is None:
            rest = line
        elif n == stmt.end_lineno:
            rest = line.encode("utf-8")[stmt.end_col_offset:].decode("utf-8")
        else:
            continue
        if rest.strip() and not rest.lstrip().startswith("#"):
            raise Refused("line %d: %r is not a comment line, a blank line, a docstring or a data name's literal"
                          % (n, line))
    return values["DONORS"], values["HISTORY"]


def literal_of(name, node):
    """The value of a data name's literal: DONORS a tuple of "<project>/<harness>" strings, HISTORY the name of a file
    of the unit's licence directory or None.  Anything else is Refused, naming what it is."""
    def kind(x):
        if isinstance(x, (ast.Constant, ast.Tuple)):
            return None
        for types, what in (((ast.Call,), "a call"), ((ast.Name, ast.Attribute), "a name"),
                            ((ast.BinOp, ast.UnaryOp, ast.BoolOp, ast.Compare, ast.IfExp), "an operator")):
            if isinstance(x, types):
                return "a computed value (%s)" % what
        return "a computed value (%s)" % type(x).__name__
    where = "line %d: %s is " % (node.lineno, name)
    if name == "DONORS":
        if kind(node):
            raise Refused(where + kind(node) + ", not a tuple of string literals")
        if not isinstance(node, ast.Tuple):
            raise Refused(where + "not a tuple of string literals")
        for x in node.elts:
            if kind(x):
                raise Refused(where + "a tuple holding %s, not only string literals" % kind(x))
            if not (isinstance(x, ast.Constant) and isinstance(x.value, str) and DONOR.fullmatch(x.value)):
                raise Refused(where + "a tuple holding %s, not a \"<project>/<harness>\" string literal"
                              % ast.unparse(x))
        return tuple(x.value for x in node.elts)
    if kind(node):
        raise Refused(where + kind(node) + ", not a string literal or None")
    if not isinstance(node, ast.Constant) or not (node.value is None or isinstance(node.value, str)):
        raise Refused(where + "not a string literal or None")
    if isinstance(node.value, str) and (node.value in ("", ".", "..") or "/" in node.value or "\\" in node.value
                                        or "\0" in node.value):
        raise Refused(where + "%r, not the name of a file in the unit's licence directory" % node.value)
    return node.value


def refuse(path, why):
    print("made_from.py: refusing the unit file %s: %s" % (path, why), file=sys.stderr)
    sys.exit(REFUSED)


def main(unit_file):
    """What a unit file's fixed block calls, with the unit file's path: check the unit file (exit 4 when it is refused),
    then the command line: a run, --record, or --check.  A Fault or any other uncaught exception, of the unit file's
    check as well (an Exception: a SystemExit, a refusal or argparse's, passes as it is), exits DEFECT, 5: a Fault
    writing FAULT and the fault on stderr, with no traceback, and any other its traceback.  check() reads that exit
    code of its runs, not their text."""
    try:
        try:
            layout = layout_of(unit_file)
        except Refused as e:
            refuse(unit_file, e)   # exit 4: a SystemExit, which the clauses below pass
        command_line(layout)
    except Fault as e:
        print(FAULT + str(e), file=sys.stderr)   # the fault alone, with no traceback
        sys.exit(DEFECT)
    except Exception:
        traceback.print_exc()
        sys.exit(DEFECT)


def command_line(layout):
    """The command line of the unit file whose Layout is layout: a run, --record, or --check."""
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("out", nargs="?", help="the TSV to write; with --check, the record to check (default %s)"
                                           % layout.record)
    ap.add_argument("--top", help="the top of the checkout (default: the current directory; with --check, the "
                                  "checkout the unit file is in)")
    ap.add_argument("--history", help="TSV: path, source (paths under %s/); with --check, default %s"
                                      % (layout.root_dir, layout.history or "none"))
    ap.add_argument("--apply", action="store_true", help="write the files the run decides")
    ap.add_argument("--record-first-added", action="store_true",
                    help="write first-added.tsv from the git history of the checkout at --top (every .v file of the "
                         "unit), then decide as usual")
    ap.add_argument("--record", action="store_true",
                    help="write OUT as the record: this run's rows, and the rows OUT already has that no run gives "
                         "again (what --apply wrote, and files that carry licence lines since), in path order; "
                         "with --apply, the files too")
    ap.add_argument("--check", action="store_true",
                    help="check the record against a run on the tree, writing no file of the tree: exit 0 it "
                         "matches, 1 it differs (the rows printed), 2 cannot decide (a run cannot start or its OUT "
                         "cannot be read, is killed by a signal, or refuses), 3 it names no path twice and differs "
                         "only in rows a run gives again, none for a file that the record holds in a row of another "
                         "kind (the rows printed; --record brings it up to date), 4 an input is missing or cannot be "
                         "read, or oft lint's lexer does not load, 5 a defect of this generator (a run or the check "
                         "stops on a fault or an uncaught exception, a run exits 0 and writes no OUT or an OUT that is "
                         "not UTF-8, or the two runs differ)")
    args = ap.parse_args()
    if args.check:
        if args.apply or args.record_first_added or args.record:
            ap.error("--check writes no file of the tree: it takes no --apply, --record or --record-first-added")
        top = args.top or layout.top
        history = args.history or (os.path.join(top, layout.history) if layout.history else None)
        sys.exit(check(layout, top, args.out or os.path.join(top, layout.record), history))
    if not args.out:
        ap.error("the TSV to write is required (or --check)")
    args.top = args.top or "."
    decide(layout, args)


def unit_file_main():
    """python3 dev/licence/made_from.py --unit-file PATH: exit 0 when PATH is a unit file of data only, 4 when it is
    refused, naming the part."""
    ap = argparse.ArgumentParser(description="check that a unit's made_from.py holds only its docstring, its data "
                                             "and the fixed block that calls this generator: exit 0 it does, 4 it "
                                             "does not")
    ap.add_argument("--unit-file", required=True, metavar="PATH", help="a unit's %s" % UNIT_PATH)
    args = ap.parse_args()
    try:
        layout = layout_of(args.unit_file)
    except Refused as e:
        refuse(args.unit_file, e)
    print("made_from.py: %s is the unit file of %s/%s: data only (DONORS: %d, HISTORY: %s) and the fixed block"
          % (args.unit_file, layout.unit[0], layout.unit[1], len(layout.donors),
             layout.history and os.path.basename(layout.history)))


if __name__ == "__main__":
    unit_file_main()
