# Step (E): internal names out of the proof comments

## The run

`scrub-comments` at the scrub head of record, `aab1e7684343` (the units' CI/CD lead named it at 2026-10-31 14:55Z),
ran ONCE on the pre-scrub bytes of this branch's head `a3f9509d24de`, from 16:28Z to 16:45Z, as
`scrub-comments --commit --base a3f9509d24de --formats-dir <comment formats 892a91f0aeb6> --machine-names <the unit's
names file, sha256 9613a711985e> --lane-names <the unit's lane-names file, sha256 4df44bfec534> ... reac-repacer/fuzz_wire`.
The formats are the version the tools registry's `tools/comment-formats/LATEST` named when the run started (registry
7a6e4e9997b9, its SHA256SUMS OK). It wrote one commit, `72f35bc38566`: 720 `.v` files, 2182 comment lines, no other
change (`git diff --numstat` adds as many lines as it deletes in every file, so no line number moved).

The tool's own check of that commit ended with exit 1 and 2 problems, both `a stoplist word replaced by a lane`, at
`lib/A/AD3j.v:7` and `lib/B/YD3k.v:5`. Each rewrites a lane's name whose first word is on the scrub's stoplist to `the
Theorem Labs lane's`. The name is a lane's, so the rewrite is right; the CI/CD lead ruled (16:51Z) that these two lines
stand and that the successor scrub head fixes the check.

The run's own outputs are internal records, not shipped, because its stderr names host paths and its report's kind
column names the delivery's codename. They are kept byte-exact at the records ref `75c46c1a4634`, folder `scrub-E/`:

| file | sha256 |
|---|---|
| stderr.txt | f904c2c2d7f0 |
| stdout.txt | d138603703e2 |
| report.tsv (one row per `.v`: comment lines, kept, rewritten, refused) | e01f740cdd3d |
| context.tsv (`--context-rewrites`) | db7f4d6eb81b |
| lane-labels.tsv (`--lane-labels`, written by the run) | c40e40275551 |
| unregistered.tsv (`--unregistered-shapes`) | 313af2909ccc |
| run.meta, run-E.sh (the run's command and times) | fd03ea0bb8ce, c6306ae6d2b8 |

The scrub left 0 tokens for the licence pass (`left for licence-lines --apply`: 0 lines), and no line holds the
doubled lane label the scrub writes when it runs over its own output.

## The residual rows

`residual-rows.tsv` holds 33 rows, one comment line each. `apply_residual.py` applies them after the scrub commit: it
checks every row first (the line's sha256 as the scrub wrote it, or the row's new text already in place) and writes
nothing unless all pass. A reader who did not write the rows checked all 33 against both commits and the rulings below
(VERDICT: PASS rows 33). Each class is a ruling of the CI/CD lead (16:51Z) or a class on the units' lead's residual list:

- A, 25 rows: the scrub deleted the label `rule 24:` from 25 lines and kept the sentence. The scanner of record does not
  flag the label, so it is restored byte-equal, with the next word's own case.
- C, 4 rows: the delivery's codename in this unit's own text becomes `the delivered package`, the scrub's own rule
  for it (lib/A/AD3c.v:24, AD3d.v:11, AD3g.v:83, AD3h.v:8). Two of these lines the scrub had rewritten for a lane name,
  which made them no longer equal to released text, so the scanner read the codename in them as new.
- D, 1 row: lib/B/YD3g.v:22, where the scrub dropped a commit sha together with a lane name; the sha is kept
  (`at d9020f8b4339:`).
- K, 3 rows: a lane possessive the scrub wrote as `a working branch's` becomes `a Theorem Labs lane's`
  (lib/A/AD3i.v:34, lib/B/YD3i.v:40, lib/B/YD3j.v:14).

## The readers' rows over the series' comment lines in new files

Before the merge, every comment line that this series' comment commits wrote in the unit's NEW files was read by a
non-writer against two rules: each sentence must be true of the code or image beside it, and each citation of content
(a file, a line, a lemma, a donor) must resolve in the shipped tree or a published commit. `git blame` at the head
found those lines: 2150 lines in 688 files, 2118 written by the scrub commit, the rest by the residual rows, the
`rule 24:` restore and two pack owners' comment fixes. Six readers read every line; their reports also covered every
defect they met on neighbouring lines, and a sweep over every comment line of the new files found 127 lines holding a
time of day, which another reader rewrote. The line numbers of these rows were not moved by any of that.

`reader-rows.tsv` holds the result: 1275 rows, one comment line each, in the residual rows' format (file, line,
sha256 of the line before, the line after, class), applied by `apply_residual.py`, which checks every row first and
writes nothing unless each line has its recorded sha256; a second run writes nothing. Every row changes comment text
only: the code outside comments of each of the 603 files is byte-equal before and after, and no line is added or
removed. Classes: FALSE 578, CITATION 549, NAME 122, BROKEN 26. What they fix, by kind:

- Copy notes that name the wrong donor or leave out what was copied. For 36 lib/A AF files the notes now name the
  donors their statements come from, in the order the path map gives (fuzz_knock, fuzz_grant or both), each at a
  published commit, and say which declarations or proof steps the second donor gave. In lib/A and lib/B the cgif ->
  fuzz_grant step again says `TfibSyms -> GrantSyms`, as the donor's released line does; the series' own rename had
  rewritten it.
- Paths that no published commit ever held (`proofs/libreac/fuzz_grant/lib/X.v` for a file fuzz_grant keeps under
  `lib/Reusable/` or `lib/B/`, `lib/AU/` in a unit that has `lib/B/`), now named as they exist at a published commit.
  A further 248 rows change nothing but add the commit (242 rows) or the release (6) at which an old-layout path
  exists; each of those was checked mechanically, that the commit is published and holds the path, and against the
  donor file at that commit.
- Commit ids no published branch holds, internal file names, placeholders such as `(internal path)`, names of lanes
  and of checks, and times of day: removed, keeping the sentence only where it holds without them.
- Addresses: the walk listings of the AD3* / YD3* headers are labelled as the donor fuzz_knock image's (each checked
  against that image), and every address a reader needs to follow this image's code (an entry, a call, a value a
  proof reads) is this image's, measured in it; wrong line numbers into this unit's files are corrected.

## The second read of those rows, and four sweeps over the same files

Each of the 1275 rows was read again by a non-writer that had not written it: the line before, the line after and the
reason, against the same two rules. 122 rows were judged wrong and their lines corrected again. The largest group,
61 rows, is a copy note that calls this unit's build "ASan" where every address in the file is the ASan+UBSan one;
a reader measured each file in both pinned images. Those readers also reported the defects they met on neighbouring
lines, 215 rows more.

Four sweeps followed, each for one class of defect, every line they found judged and measured. The first
read every comment line of the 1216 new .v files; the others read the lines that carry the class:

- a SOURCE no reader can open: 263 lines hold a placeholder, an internal record, an earlier revision of a design
  text, or a tool or log no tree holds. 139 are defects; in the rest the placeholder names an author or an approver,
  which the series allows. Each defect now cites what this tree ships or a published commit, or states the fact
  without the source where the fact holds alone.
- a PATH no published commit holds, and the build a copy note names: 220 lines, each path checked at the donor's
  published commits and each build decided by measuring the file's own numerals in both twins.
- the DONOR order of every copy note, re-measured by comparing the declarations each file shares with each donor
  rather than reading its sentences, against the path map's own table: 215 rows, 42 lib/A files and 73 lib/B files.
  Four files where the measurement and the table disagree are named to the path map's owner.
- an ADDRESS given as this image's that is in fact the donor's, with the lib/A twins of the lib/B fixes: 35 rows.

Two header blocks described the kernel through an unpublished revision of a design text. Each was rewritten from the
kernel this unit ships, `lib/B/YD3j.v:89-137` and its image-A twin `lib/A/AD3j.v:31-79`: 49 lines become 19 in each,
every sentence one fact with the file:line that holds it, and the lines the block no longer needs are empty. No line
is added or removed anywhere in this pass, so every `file:line` citation in the unit still points where it did.

The three generator-output files (sha256 36072c05a309, 643acca6a5e1 and 2d0075462125, not in the published tree) are left byte-exact: they are what
`gen_exitW.py` printed, and that run's own `logs/sha256.out` (sha256 7aa28ac5f7b4, not in the published tree) pins their bytes, so their line 5 keeps the generator's
wording. The `lib/B` copies of those three files, `YD1y.v`, `YE23.v` and `YE37.v`, name the generator at the path
this tree ships it instead: `provenance/evidence/startup-B/exitdrv/gen_exitW.py`, sha256 48590f3a6182, which is
byte-equal to the copy that run used, which is not in the published tree.

Where two readers wrote different text for one line, a third read both, measured every claim of each and wrote the
one line that carries the true ones; a last read then took every changed line of the files where that happened,
with the lines around it, and corrected what the merge had left half-said or false, in those files and in the twins
of the lines it fixed.

`second-rows.tsv` holds the result: 1201 rows over 410 files, in the same format and applied by the same
tool, `apply_residual.py`. The code outside comments of every file is byte-equal before and after, 58 lines are
emptied, and no line is added or removed. Classes: ADDR 35, BLOCK 96, DONOR 129, MERGED 345, PATH 204, SECOND 231, SOURCE 108, TWIN 53.

## Lane names, and paths the published tree does not hold

The shipping prep keeps, of `provenance/`, only `evidence/` from this branch; `startup-gen/`, `core-reloc/`, `k2/`,
`prog-gen/`, `memmove/` and `TRUNK.md` stay in the source repository. 49 lines in files that ship cited one of those
paths. Each now cites a byte-equal copy that ships, or a released commit and path (a released later version is named
as such), or names the file with its sha256 and says it is not in the published tree; a citation of a path that no
commit holds is dropped, and the sentence is kept only where it holds without it. Six of the 49 are code and stay, and
four are rows of the two earlier records, which stay as they are (below).

The gate record `provenance/evidence/startup-B/GATES-wireB.md` is made by `mk_evidence_gates.py` from the lane copy
`provenance/startup-gen/B/GATES-wireB.md`, so its rows went into the lane copy and the shipped copy was made again by
the same, unchanged tool: its diff is exactly the effect of those rows, line for line. 13 rows take out the names of
the lanes that wrote the record and the rulings it cited by lane and time, each sentence now resting on what it
measures; 22 more give the record's relative paths their base. Its line 17 names every base the record uses, and
`GATES-wireB.paths.tsv` beside it resolves all 212 relative paths, one row each, with its base and, for a file, its sha256.

Seven changed files have their sha256 named in other files. Every such naming in a hand-written file now gives the
new sha256 followed by the old one, as `NEW (OLD before a comment-only change)`; the logs of the runs that read those
files keep the old sha256, which is what those runs read.

`prep-rows.tsv` records every hand-made line of this step in the same format, applied by `apply_residual.py` to the
commit before it, after which `mk_evidence_gates.py` makes the shipped gate record again; together they reproduce every
changed line of this step but this section. Rows on files under `provenance/startup-gen/` apply only in the source
repository. `reader-rows.tsv` and
`second-rows.tsv` are left as they were, the records of their own commits: four of their rows (reader-rows line 728,
second-rows lines 8, 9 and 330) give the text a line had before this step rewrote it.

A non-writer then read the regenerated gate record's diff against its lane copy. It found the regeneration exact and
three faults in the text, fixed in the lane copy, after which the shipped copy was made again by the same tool: two tool
sha256s on line 144 that had gone stale (nsW.py and trunk_missing.py; each now gives its current sha256 and the old
one), a commit no published branch holds named as the place of the tool set on line 384, and the base table's row for
`provenance/evidence/MANIFEST.md`, which gave the parent's sha256 (a table the top MANIFEST lists cannot name that
MANIFEST's final sha256). The slice's `MANIFEST.md` names the base table, and its tools paragraph no longer gives the
tool sets' places as commits no published branch holds.

## The second read of every changed line

Every line that `second-rows.tsv` and `prep-rows.tsv` changed, 1285 in all, was then read by one of six readers that
wrote none of them, each twin pair inside one reader or with its twin named: the line as it stands, its neighbours,
its twin, every address measured in its own image, every citation opened. They judged 75 lines wrong. The largest
groups: 37 copy notes said the steps taken from fuzz_grant write the image bounds as numbers, where the file only drops
`YImgTop.IMG_LO` / `IMG_TOP` from unfold lists (each file was compared with its fuzz_knock donor; a sweep of the same
phrase over all of `lib/` found 4 more); lib/B comments that named a lib/A module; copy notes that left out a change a
donor made; and tools that named a donor file by a path no published commit holds.

The readers also reported the defects they met on other lines, and those were fixed too, with three exceptions kept by
rule. A line byte-equal to the donor's published line is the donor's own history and keeps its text: 46 such lines
were reported (copy notes byte-equal to fuzz_grant's `lib/B` at 4f87de75d67, the three `lib/B/Rt` headers, and
`lib/B/WireBClose.v:7`, which is fuzz_decode's line). An unpublished commit named as a run's identifier stays (gate
record lines 427 and 657). And the generator-output files stay as their generator printed them.

Six tools and inputs changed in comment lines: five of the start-up slice, each changed in its shipped copy and its
byte-equal lane copy alike, and the depot's `emit_col.py`. Every hand-written naming of their sha256 now gives the new
value, with the value the runs read kept beside it. A second read of the gate record by the same non-writer found four
more faults (the start-up
tool set is not in the published tree except one file, `ColA.v`, which the main line holds; and the base table's
description overclaimed), fixed the same way.

`reread-rows.tsv` records the 106 hand-made lines of this step in the same format; `apply_residual.py` on the commit
before it, then `mk_evidence_gates.py`, reproduces every changed file but this section, the base table (whose lines
hold tabs; only sha256 cells changed in it) and the allocator slice's files, which carry their own record.

## The donor's own history, and the read of the second read

A line byte-equal to the donor's published line is exempt from the name scanner, not from being true: the series'
lead ruled that such a line is fixed here when it is false of this unit's file or cites what a reader cannot open.
46 lines were of that kind. 27 copy notes cited the old-layout cgif path with no commit and now name `25e3d17bdb50`,
which holds it; 15 line 4s of `lib/B/YFk*` and `YFl*` said the donor moved its addresses to fuzz_grant's ASan build,
where every numeral in fuzz_grant's `lib/B` is its ASan+UBSan one (measured in both of fuzz_grant's pinned images);
the four `lib/B/Rt/*` headers and `lib/B/WireBClose.v:5` cited `origin/cold/...` branches and a version no published
commit holds, and now cite the published commit whose bytes the relocation read, with this unit's own values; and
`lib/B/WireBClose.v:7` gives each of its three donor files a commit. A non-writer then read all 48 of those lines and
found two more faults, the `GrantSyms -> WireSyms` rename left out of two `Rt` headers, which are fixed here too.

A non-writer also read every one of `reread-rows.tsv`'s 106 lines against the files, the images and the donors. It
confirmed the record (each line at the head equals its row, each old sha256 the line before it, the code outside
comments unchanged, and the shipped gate record byte-equal to a fresh run of its unchanged generator on the lane
copy) and the seven re-taken sha256 pins, and judged 32 lines wrong: 23 copy notes that leave out fuzz_knock's local
`Zify` and `YM03.lf_lia_orig` settings, which the file drops; 14 that leave the tactic `off_by` out of the list whose
`YImgTop` unfolds went; 17 `lib/B` notes that cite the image-A `lib/Reusable/YImgTop.v` where image B's bounds come
from `lib/B/YImgTop.v`; `lib/A/AB12.v:4`, which named a branch rather than its commit; `lib/A/AD1g.v:5`, which left
out three differences from its donors; and `lib/B/YFi5.v:4`, which claimed a premise no statement gained. Some lines
carry more than one of those faults.

`delta-rows.tsv` records all 80 hand-made lines of this step, 48 of the donor's history and 32 of the read;
`apply_residual.py` on the commit before it reproduces every changed file, and a second run writes nothing.

## Every copy notice's donor path, resolvable

A non-writer read of the step above reported, on lines outside it, two classes this step closes.

Twenty lines are the `lib/A` side of corrections their `lib/B` twins already carry, or the same fault in one more
file: `AFis.v:5`, `AFgi.v:5`, `AFgm.v:5` and `AFgn.v:5` left out the tactic `off_by`, whose `YImgTop` unfolds went,
and the two `Local Ltac` settings the file drops; line 4 of `AE2k.v`, `AE3e.v`, `AF0l.v`, `AF0x.v`, `AFiy.v` and
`AFjc.v` cited the cgif path with no commit; `lib/B/YB12.v:4` named an unpublished commit as the place to find
`atable.py`, where its twin keeps the sha256 and says the tool is not in the published tree; and nine `lib/B` copy
notices named a fuzz_grant path that commit does not hold, or gave the right path with no commit and left out what
the copy changed (`YD1p` applies `ly0` without `ch`, `YD1r` requires `KnLayoutGle` and uses `gle_le_ablocks` and
`top_ok_gle`, `YD2l` drops the `as_dhash` case, `YD1u` goes through `gle_le`; no statement changed in any of them).

The second class was wider than the lines that reader could see, so it was measured over all of `lib/`: 1443 citations
of a donor path carry no commit, and 59 of them name a path that no published donor commit holds, because the donor
keeps the file in another directory. Each of those 59 now names the path that exists and the commit that holds it,
and in each case the donor file's declarations are this file's: 53 are fuzz_grant's `lib/B/<f>.v` at `4f87de75d67`,
three are fuzz_grant's `lib/Reusable/<f>.v` there, and three are fuzz_knock's `lib/Reusable/<f>.v` at
`88154566652a` (`KnBlockExt.v`, and `YC5d.v` and `YCbp.v`, whose text uses `depot_has_trace` and `DepotCfg`, which
no fuzz_grant copy has). A non-writer read all 59 and the 20 above: it confirmed the 54 the measurement had settled
and decided the five the measurement could not, two of them to a different donor than the measurement proposed.

`last-rows.tsv` records the 79 hand-made lines of this step; `apply_residual.py` on the commit before it reproduces
every changed file, and a second run writes nothing. The 1384 citations whose path does exist at a donor commit, but
which name no commit, are left: that is the series' older form, and changing it is not this pass's work.

## A citation names a commit, never a branch

The branch `ossv/recipes` is being deleted, and 69 lines of the files this unit ships named it. 56 of them name a
commit as well, and each of those nine commits is an ancestor of `origin/main`, so they resolve after the deletion
and their branch word is stale, not broken. Thirteen named the branch with no commit beside it. Eleven are fixed
here, each by naming the commit that holds the file the sentence cites, opened and checked first: `88154566652a`
for the six `crtA_*.v` helpers of `lib/{A,B}/Prog/check_copy_cgW_walk.v`, `48907dc7e8ca` for the five
`lib/A/Prog/reac_frame_is_reac*.v` headers (the layout-move commit, which is the published commit that holds the
new-layout path those lines give) and for `stackmalloc-B/MANIFEST.md`'s citation of fuzz_knock's `lib/AU/YF0s.v`,
`4f87de75d67` for the two `depot_apply.py` docstrings, and `5098883da0b` for `memmove-reloc/adapt_memmove.py`.

Two are left as they are, because each is a verbatim record of other text and editing it would make the record
false, and each names its commit anyway: `depot/hashlen-cases.tsv:54`, whose cell quotes `provenance/TRUNK.md:3`
word for word, and `depot-B/adaptations/depot_apply.py.diff:9`, a context line of a recorded diff whose hunk's
commit sits on the line above it.

residual-rows.tsv, reader-rows.tsv and second-rows.tsv, named above and in prep-rows.tsv and reread-rows.tsv, were removed from the shipped tree on 2026-11-04 (internal record; in git history).
