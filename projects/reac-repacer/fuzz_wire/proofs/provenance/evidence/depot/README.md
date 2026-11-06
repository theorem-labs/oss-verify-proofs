v4 / v5.2.1 = the AB1w clause-2 classifier's rule version (yb1w_clause2_v4.py sha256 53e5ca93b62c; yb1w_clause2_v5.py sha256 600920ff3e78)

This directory holds the records of image A's relocated core of reac-repacer/fuzz_wire; each file is named after what it holds.

Known non-shipped item: provenance/TRUNK.md (sha256 9fc709131602 (a91aca7cc34a before a comment-only change); the trunk's table, with git blob ids in its 'released blob' column). The ship step takes, of provenance/, only evidence/, LICENSES/, PROVENANCE.md, PROVENANCE.yaml and port/, so TRUNK.md is not shipped and its table is left as it is.

## Classifier of record

The AB1w clause-2 classifier of record is v5.2.1: gates/yb1w_clause2_v5.py, sha256 600920ff3e78, commit f3aacd133b42
(ab1w-clause2-v5.2.1.tsv, ab1w-clause2-v5.2.1-after.tsv, ab1w-remove-list-v5.2.1.tsv). The earlier removals cite
yb1w_clause2_lockB.py (sha256 e46125e3f178; internal record). Its copy is no longer in this directory: no record here
re-runs it, and its bytes are preserved with the unit's records.

## Rulings are cited by role

A ruling is cited by the role that gave it and its time, never by a session name: the unit owner, the publication
owner, the publish tool. role_names.py made that rewrite. It keys the three names by their sha256, so it carries none of
them, and it refuses unless each file holds exactly the number of roster names the scanner of record reported there:
takes.tsv 476, mkaf-RESULT.md 2, derivation-RESULT.md 1, hyp-values-RESULT.md 1, name-audit-RESULT.md 1, donor_map.py 1,
leak_gate.py 1. It also rewrote one name in ab1w_clause2.py that is not on the roster. For the three scripts, only their
docstrings change (role_names.py checks that their code, the AST without docstrings, is equal). Each one's output is
byte-equal before and after the rewrite: donor_map.py (403 lines), ab1w_clause2.py (1087 lines) and leak_gate.py
(423 lines). takes.tsv keeps its 1247 lines and every tab.

## Hash-length convention

A commit is cited at 12 hex. A sha256 is cited at 12 hex beside the word `sha256`. The full form stays only where a
tool's own output carries it. A line byte-equal to a released line is inherited and stays as it is. hashlen_sweep.py
applies the rule to the ids its MAP input lists (hashlen-map.tsv), with BASE c7fdc56f75bb for the inherited-line test
(`git grep -F` over its projects/ and proofs/, then an exact whole-line comparison). hashlen-cases.tsv is its
measurement at the final text (152 cases, none left in scope; tabs inside a cell are written as \t). 3 cases were in our own prose, and the sweep
rewrote them: AF0w-zify-flag.md:7 and :9, and pa-RESULT.md:4. 2 more come from our writers' inputs, so the writers were
re-run instead: ACej.v:7 / :9 from its header file, and AF0m.v:9 from af0m's --modified value. That value also names
the tool by content, `af0m.py (sha256 238598b380f1; internal record)`; its `port_core 0e4e065eab9f` is the released form.
ACej.v:10-12 (the gen_traces.py cite, with its commit and its sha256 in full) are not ours: they are byte-equal to
lines 10-12 of the released fuzz_uci A/ACej.v at recipes c5e779efe8c9, so they are inherited and stay. Every other case
is exempt:
- The `(* Read from: <image> ... sha256 <64>; unstripped twin sha256 <64> *)` line is written by the start-up tools of
  record (the provenance line of pins.py).
  - pins.py stamp writes it in AB12, AD1k, AD2i, AD2j, AE37, AE3i and AF0m.
  - The collector's hsform.py writes it in AB01, AB03, AB13, AB1h, AB1k, AB1l and AB1v. It also writes it in AB1m,
    whose line emit_col.py keeps byte for byte.
- exitdrv.py formats the image sha256 itself: AD1y.v:5 and AE23.v:7.
- ae37gen.py writes the 16-hex image sha: AE37.v:5. This is the form the released AE37 files of other units carry.
- own_line_names.py writes `commit f529bfe14c7` in AD3a.v:135 and AD3b.v:122, the commit as its source line gives it.
- af0m.py writes the full sha256 values of lib/Reusable/DepotCfg.v:12-15 (a trunk file).
- SHA256SUMS and PROVENANCE.md are tool output.
- Verbatim records and scripts: 101 cases.
- Lines byte-equal to released lines: 16 cases.
Decimal-literal control: the Rocq literals 6108936 (3 times) and 6041018 (2 times) are unchanged. The sweep considers
only hex runs of 8 or more characters that start a listed id, and it refuses a .v edit that would change a code token.

## The fresh-build record

fresh-build-v-files.tsv replaces fresh-build-v-blobs.tsv (sha256 a24e9531ff60, which gave git object ids). It holds the
sha256 of each .v file's bytes, at 78d6988b23aa and in the copy the 04:02Z build compiled (1635 of 1635 equal).
fresh_build_file_sha.py writes it: `hash` where the copy is, then `table` against the commit.

## Stage maps (internal records)

The four stage maps are not shipped. Each is cited by its content, and is preserved in the unit's records:
- grant-donor-stage-out.tar (sha256 f3e3b121f3a6; internal record): the grant run's stage output, 370 .v files.
- knock-donor-stage-out.tar (sha256 31d2c45ba9da; internal record): the knock run's stage output, 121 .v files.
- grant-consumer-base.tar (sha256 059d1c043b51; internal record): the 110 consumer files in grant's text, as the
  consumer classification read them.
- knock-release.tar (sha256 91342cd41d44; internal record): 411 .v files. 301 are byte-equal to the knock release
  (recipes 88154566652a). The other 110 are the consumer files in the knock run's relocated text.
Earlier records cite the gzip form. Each .tar is the byte-exact content of its .tar.gz, and a record that cites either
sha256 resolves by its prefix:
- grant-consumer-base.tar.gz sha256 7da1f9d32a9d -> grant-consumer-base.tar sha256 059d1c043b51 (5601280 bytes)
- grant-donor-stage-out.tar.gz sha256 075d54d28677 -> grant-donor-stage-out.tar sha256 f3e3b121f3a6 (15493120 bytes)
- knock-donor-stage-out.tar.gz sha256 c349e1f9a325 -> knock-donor-stage-out.tar sha256 31d2c45ba9da (6696960 bytes)
- knock-release.tar.gz sha256 5c83b75981ce -> knock-release.tar sha256 91342cd41d44 (16373760 bytes)

Some shipped tables were derived from these maps. For each one, here is which of its numbers a reader can re-check
from shipped files and public commits, and which rest on an internal map:
- stage-pairing.tsv and differing-numerals.tsv: each value at a unit line and its verification can be re-checked on
  fuzz_wire.asan and the unit's own lib/. Which donor value a line replaced, and the differing-line counts, rest on
  grant-donor-stage-out.tar (sha256 f3e3b121f3a6) and knock-donor-stage-out.tar (sha256 31d2c45ba9da).
- consumer-classes.tsv, hunk-residue-variants.tsv, layout-growth-classify.out, layout-growth-classify-ops.tsv,
  layout-growth-statements.tsv, layout-growth-complete.out and layout-growth-complete-control.out: their grant line
  ranges and texts are the consumer files' grant text, grant-consumer-base.tar (sha256 059d1c043b51). Their knock line
  ranges and texts are the knock run's relocated text: knock-donor-stage-out.tar (sha256 31d2c45ba9da), which
  knock-release.tar (sha256 91342cd41d44) holds too, for 109 of the 110 consumer files. The grant column's path names
  the unit file as it was before the consumer round, not today's lib/. So their line ranges and residues rest on those
  internal maps. What a reader can check is the result: the unit's lib/ as shipped, and its build.
- takes.tsv: its hunk numbers are consumer-classes.tsv's, so they rest on the same maps. The build logs that its
  breaks cite are internal.
- depot-classes.tsv and knock-diff-sweep.tsv compare the two public releases (recipes 4f87de75d677 and 88154566652a),
  and can be re-checked on those.
The relocation runs themselves (port_core with its address gate, and the derivation of the knock run's override rows)
are not shipped. Their tables cannot be re-run from the shipped files alone.

## The 18 empty-depot kernel files of lib/Reusable (internal records)

lib/Reusable's 18 kernel files (YC5d YCbp YCbq YCe5 YF06 YG00 YG08 YG0d YG0f YG0h YG0i YG0j YG0n YG0o YG0q YG0r YG0s
YG0t) come from three steps. Each step's difference was measured:
1. A depot_apply.py run of 10-30 at 10:13Z. Its inputs: grant's kernel text at recipes 4f87de75d677 (all 18 files
   byte-equal to the release); knock's lib at recipes 88154566652a; depot-classes.tsv (sha256 a15c803b29eb). Its
   arguments: --take YG0f.v:4, YG0n.v:25, YG0n.v:26; --merge YG08.v:9 prim_committed_bound_any=prim_committed_bound_nev;
   --glue YG0s.v:12 (the `unfold kFreeArrayOffset in *.` glue). Its unified diff is
   depot.patch (sha256 728cb481859d; internal record). The version of depot_apply.py that made that run wrote one
   `Modified by` notice line into each
   file. The shipped depot_apply.py (sha256 18f7257c92fa before its comment line) is the later version and writes no
   notice. Re-run with the same inputs and arguments, its output differs from that run's output by exactly that one
   notice line in each of the 18 files, and by nothing else.
2. wire_kernel.py (sha256 b67ba8b7d8fe) maps that run's output to the unit's form.
3. The header-rule scrub rewrote comments in lib/. Its rewrite table is
   scrub-table.tsv (sha256 de9ccdf1fc0f; internal record): it records that run's patterns, replacements and counts as
   written; each rewrite is a measured difference
   between the writers' outputs and the shipped lib/. For these 18 files, wire_kernel.py's map of step 1's output (its notice line included) differs from lib/Reusable in 84 comment lines and in no code line:
   6 where a lane name became `a Theorem Labs lane` (that table's lane-name row; YG0n.v 4 lines, YG0s.v 2), and all 78 `Modified by` lines, step 1's notice among them, which step (E) of evidence/scrub/README.md dated `Modified by Theorem Labs, 2026-10:`.
   Then the readers' rows (evidence/scrub/reader-rows.tsv; that README's section "The readers' rows") reworded 28 of the 84: all 18 fuzz_grant copy notices (now lib/Reusable/<F> at 4f87de75d677), step 1's notice in the 9 files where every hunk was taken, and YG0n.v:589; the second read (evidence/scrub/second-rows.tsv) reworded one more, YG0n.v:282.
   Both row files were removed from the shipped tree on 2026-11-04 (internal record; in git history).
So the shipped depot_apply.py does not reproduce the notice line that lib/Reusable's 18 kernel files carry from step 1.
Its other output is the same as before its one comment line: all 19 files of a re-run are byte-equal, and its code
(the AST) is unchanged.

## Held files

lib/Reusable/R/Cfg.v (file sha256 4f674d6a1e76, 358 lines) and lib/Lib/Acfg.v (file sha256 aed270899484, 591 lines)
are HELD. Their code stays byte-equal until each one's clean-room
restatement is posted, which is then taken byte-equal. The licence-lines --apply may rewrite their line-3 notice:
ship.sh vet reads a comment-only change as unchanged, and HELD. Both stay out of the scrub. The U twin of R/Cfg.v is
not held.

## Known items

Three role names that have no h- prefix, and the scratch path stem, occur on 14 lines of the unit's lib/. The anchored
grep `git grep -n -P '(?<![\w-])c-(?:asan(?:-rt)?|libc-fmt)(?![\w-])|cold[/]scratch[/]' -- projects/reac-repacer/fuzz_wire/proofs/lib`
lists them: lib/A/AD3c.v:7, :36, :53, :83; lib/A/AD3d.v:10, :146; lib/A/AD3g.v:7, :17, :130; lib/A/AD3i.v:37;
lib/A/AD3j.v:36, :2582; lib/A/AFk0g.v:3; lib/Reusable/KnLayoutGle.v:3. Each line is byte-equal to a line of the knock
release (recipes 88154566652a), so all 14 are inherited, and none is in our own text. The name checks of this unit's
start-up runs flag them from now on.

## Cells the classifiers do not judge

ab1w_unjudged.py reads, against fuzz_wire.asan, every A/AB1w.v cell that the clause-2 classifier v5.2.1 does not
judge (48 of 830 sentences: section bounds, image cells, at-table cells, and the nat and list cells); table
ab1w-unjudged.tsv. 47 are TRUE. tfib_at_stops_more is FALSE: .text holds 13 self-loop stops, the same set as
A/AB12.v's stops_more, and the cell lists 12, lacking SealedRepairReservation+0xc0. All 48 have 0 readers; the table's
`next series` column gives the removal row ('remove: incomplete (12 of 13), unread').
yh03_unjudged.py reads the YH03 cells (plain lib/Reusable, ubsan lib/U/Reusable) that yh03check's record
(yh03check-record-plain.tsv, yh03check-record-ubsan.tsv) did not clear: 6 not judged and 6 NOSYM per image (tables
yh03-unjudged-plain.tsv, yh03-unjudged-ubsan.tsv). 8 are TRUE. The 4 D_str cells are FALSE, read only via sk_file,
and removed with their readers by the series (5dc55e235e5f); they are trunk files, not changed here.
yh03_unjudged.py and its four tables were removed from the shipped tree on 2026-11-04 (internal record; in git history).

## The leak gate's grant-term rule

leak_gate.py (sha256 1f93aa2abd28; before the rule 9b8564eb01a5) counts a hit of the numeral lineage tokens 8192 or
11776 as LINEAGE only if GRANT_A's file of the same name does NOT carry the same numeral in the same TERM. The TERM of
a numeral is the numeral and the two tokens directly before it in the file's token stream. The match is exact, token
for token, after the gate's existing normalisation (comments removed; module paths, image and record names masked),
and nothing else is normalised. Every other lineage token is unchanged by the rule.
Its tests (`leak_gate.py --test`, 3 of 3 as expected): the same term in grant clears the hit (`MSv + (MSv / 8 + 8192)`
against `MSv + MSv / 8 + 8192`, term `8 + 8192`); a planted knock-only EV_MAX term still fails (`y < 8192` where grant
has `y < 11776`); a numeral that grant carries in a different term still fails (`w + 8192` where grant has `z * 8192`).
Measured on a trial tree (not of record; the record run is on the frozen head):
- before: `GATE leak-gate VERDICT: FAIL head 3fc1c6a482f905b8685595d708ec10c0cb3ad506 inputs GRANT_A = grant-consumer-base.tar (sha256 059d1c043b51; internal record), its 110 files; APPLIED_A = lib/A at the head; leak_gate.py (sha256 9b8564eb01a5)`,
  `LINEAGE hits 2`: A/AFk0.v:1529 and :1617, both the term `8 + 8192` of knock's `MSv + MSv / 8 + 8192`, which
  grant's A/AFk0.v carries in `MSv + (MSv / 8 + 8192)`.
- after: `GATE leak-gate VERDICT: PASS head 3fc1c6a482f905b8685595d708ec10c0cb3ad506 inputs GRANT_A = grant-consumer-base.tar (sha256 059d1c043b51; internal record), its 110 files; APPLIED_A = lib/A at the head; leak_gate.py (sha256 1f93aa2abd28)`,
  `LINEAGE hits 0; numeral hits in a grant term 2`. Of its 4923 rows, only those 2 change (their lineage column).
