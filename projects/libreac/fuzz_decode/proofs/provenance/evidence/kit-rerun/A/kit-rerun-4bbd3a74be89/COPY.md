# COPY.md: this directory is a token copy of another lane's record

This directory holds a copy of another lane's re-run of the image-A alloc-reloc record on cmpkit 4bbd3a74be89. The
copy is that record with named tokens put in where the original names a host path, a branch, a session or lane name,
a date or a time. Nothing else differs. `copycheck.py` beside this file proves it from the original's bytes in git.

## 1. The original

- Commit `ec63ec6c4edeb4e7ee2360980dbd3f1070504c41`, the head of the other lane's re-run branch, its final reviewed
  state. Its fourteen commits change only this directory:
  - `c53a0cf3a289`, `4639e23e5c2d`, `d0b5ec3b38ca`: the re-run on cmpkit 4bbd3a74be89;
  - `e88411a35760`: adds the exposure scans of cmpkit 86da41d3ef68 (`SCANS-86da41d3ef68.md` and 3 outputs);
  - `f39105e6ace8`: adds the hand-trace of every lui through all ALU ops (`LUI-HANDTRACE.md`, `luitrace.py`, 5 outputs);
  - `4870be5440a6`, `8d5e07101db5`, `944f3f95abda`, `032f7ba55aca`, `295eb9e170df`, `f3ebf71c45fb`, `23ce03c3683c`,
    `ed324b3a30a3`, `ec63ec6c4ede`: the hand-trace through its reviews to ACCEPT. They change `LUI-HANDTRACE.md`,
    `luitrace.py` and 2 of its outputs, and add `plant_controls.py` and 9 outputs; a planted-control script and its
    output that `4870be5440a6` added are deleted again by `8d5e07101db5` and are not in the original.

  The 31 files of `e88411a35760` (the re-run and its scans) are unchanged at `ec63ec6c4ede` (checker step 1). The
  branch name is a name the proofs-file rule keeps out of this tree, so this file gives the commits only.
- Directory `proofs/libreac/fuzz_decode/provenance/alloc-reloc/A/kit-rerun-4bbd3a74be89/` at that commit:
  48 files. Every one of them is here, with the same name and mode. This copy lies at
  `proofs/libreac/fuzz_decode/provenance/evidence/kit-rerun/A/kit-rerun-4bbd3a74be89/`; it was moved there from the
  original's path with no byte changed.
- Section 4 gives the file sha256 of each of them at that commit, beside the sha256 of the file as shipped here.

## 2. What changed, and the proof

595 spans in 35 of the 48 files are changed. Each span is one whole token of the original. A token
replaces it, in UPPER_CASE, as `provenance/evidence/startup-A/inputs/scrub_input.py` does. The other
13 files are byte-identical to the original. No span holds a newline, so every line keeps its number,
and no line is added or removed.

| token | class | spans | what it stands for |
|---|---|---|---|
| `DONOR_TWIN` | PATH | 30 | the unstripped twin of the donor build cgif_file_fuzzer.asan-ubsan, sha256 `ce511d541cdabbe3c8df3f672dc517e8b5a7edd37b280a7483043b438de0adf7` |
| `DECODE_A_TWIN` | PATH | 39 | the unstripped twin of decode A, fuzz_decode.asan, sha256 `4cb0a852e8262acb5ed0fa075a6bee7b1a25192189b168e777c760a4bfd65ae2` |
| `DECODE_A_PIN` | PATH | 2 | the pinned decode A binary, fuzz_decode.asan, sha256 `5973b76807d8d2e14b82dc6afde70a2c882923658406aeca43681719cb4e8036` |
| `DECODE_PLAIN_TWIN` | PATH | 1 | the unstripped twin of decode plain, fuzz_decode.plain (sha256 `18a5c8eae19b`, out/negctl-mine.out line 3) |
| `FRAME_TWIN` | PATH | 1 | the unstripped twin of libdiginet fuzz_frame.asan (sha256 `67d7e481d74e`, out/negctl-mine.out line 1) |
| `HUB` | PATH | 5 | the hub clone (a directory; the default of `HUB` in run.sh line 5) |
| `OLD_RECORD` | PATH / PATH_PREFIX | 2 | the earlier record's directory; its `out/` holds pairs.tsv (sha256 `44cd93f173b5bb0fc717224e7975e22c15b222527eb50e13198f453394313ed9`) and numerals.tsv (sha256 `864c853942d67a9f6dc7ce2702838da8f5318f02bd25b7192196b659f35cbc6d`) |
| `KIT_PARENT` | PATH_PREFIX | 3 | the directory the kit was extracted under; the kept tail `/cmpkit-4bbd3a74be89` is the kit id |
| `NEGCTL_ROOT` | PATH_PREFIX | 3 | the root of the fixed path that the kit's controls/negctl.py (line 10) reads the old repin_check e5487165abb8 from; the kept tail `/tools/repin_check/e5487165abb8` holds the tool sha |
| `DEPOT_DIR` | PATH_PREFIX | 2 | the host directory of the sanitizer toolchain depot; the kept tail `/src-llvm-20.1.8/` (LUI-HANDTRACE.md) or `/` (a luitrace.py comment) names its local copy of llvm-project llvmorg-20.1.8 |
| `REVIEW_DIR` | PATH_PREFIX | 6 | the reviewer's scratch directory of the first review rounds; the kept tails name the scripts (`/myplants.py`, `/myplants2.py`) whose logic luitrace.py and plant_controls.py copy |
| `REVIEW_DIR3` | PATH_PREFIX | 2 | the reviewer's scratch directory of the third review; the kept tail `/imgaddr.py` names the script imgaddr_run() copies |
| `REVIEW_DIR4` | PATH_PREFIX | 1 | the reviewer's scratch directory of the fourth review; the kept tail `/allstops.py` names the script the dead-argument walk copies |
| `REVIEW_DIR6` | PATH_PREFIX | 2 | the reviewer's scratch directory of the final review; the kept tail `/frameesc_may2.py` names the script `frameesc` copies |
| `BRANCH` | BRANCH | 9 | the name of the tools branch that holds the kit commits (3c3e62ee2786, and 6d8ff128a01 in luitrace.py line 2) |
| `WORKER` | NAME | 8 | a worker session name |
| `AGENT` | NAME | 398 | a lead or reviewer session name |
| `LANE` | NAME | 1 | a lane name |
| `DEPOT_NAME` | NAME | 1 | the name of that depot directory, in the citation `DEPOT_NAME/depot/README.md:9-13` |
| `DATE` | DATE | 8 | a date |
| `TIME` | TIME | 71 | a time of day |

`COPY.diff` is the diff original -> copy. It has one hunk per changed line. The `-` line is the original line with
every removed span shown as `<redacted>`. The `+` line is the copy's line. The removed text is not in this tree.
`copy-edits.tsv` lists every span: file, line, byte offset, length, the sha256 of the removed bytes, the class and the
token. With the original's files, it is enough to rebuild the copy.

`python3 copycheck.py <hub clone> --scanner <scanner of record>` reads the original from git and checks the following.
Section 4 and the checker's docstring give the details.
- Every listed span is a whole token of its class.
- Each path token always replaces the same path, and each path always gets the same token.
- The original with the spans replaced is the copy, byte for byte.
- No removed text is left anywhere in this directory.
- `COPY.diff` and the file table below match. copycheck.py writes COPY.diff (`--write-diff`) and the file table
  (`--write-table`) itself, and without those options checks them line for line.
- The scanner of record exits 0 on this directory with no blocking hit, and every blocking hit it finds in the
  original lies inside a replaced span. It lists no non-blocking hit here.

Its output on this tree (scanner of record: `binscan_of_record.sh`, scanner `0609a660961e`, exceptions
`2fe8196d9738`):

```
$ python3 copycheck.py <hub clone> --scanner <scanner of record>
copycheck: original ec63ec6c4ede proofs/libreac/fuzz_decode/provenance/alloc-reloc/A/kit-rerun-4bbd3a74be89: 48 files; chain from d0b5ec3b38ca (27 files), files added / changed / deleted per commit: e88411a35760 +4 ~0 -0, f39105e6ace8 +7 ~0 -0, 4870be5440a6 +2 ~3 -0, 8d5e07101db5 +3 ~3 -2, 944f3f95abda +1 ~7 -0, 032f7ba55aca +2 ~5 -0, 295eb9e170df +1 ~4 -0, f3ebf71c45fb +0 ~4 -0, 23ce03c3683c +2 ~4 -0, ed324b3a30a3 +1 ~2 -0, ec63ec6c4ede +0 ~4 -0; the 31 files of e88411a35760 unchanged at ec63ec6c4ede; 595 spans in 35 files {'BRANCH': 9, 'DATE': 8, 'NAME': 408, 'PATH': 79, 'PATH_PREFIX': 20, 'TIME': 71}; every other byte identical; COPY.diff and COPY.md file table match
copycheck: scanner on the 52 files here: exit 0, 0 blocking hits; listed, non-blocking, per file: {}
copycheck: scanner on the original: 575 blocking hits, every one inside a replaced span (0 listed, non-blocking); 515 of 595 spans hold a hit; spans that hold none, by class: {'DATE': 8, 'NAME': 1, 'TIME': 71}
```

No number, verdict, count or row changed. Outside the DATE and TIME classes, no removed span holds a number: no
`0x...` value, no run of three or more digits, no run of eight or more hex digits (checker step 2). Every byte outside
the spans is the original's byte (step 4). Each DATE or TIME span is a calendar date or a time of day
(`(\d{4}-)?\d\d-\d\d`, `\d\d:\d\dZ`) in prose, and none is a measurement. Every table row, verdict, count, address and sha
of the original is in the copy unchanged.

## 3. The script lines

The scripts are run.sh, the eight Python steps of the re-run, luitrace.py and plant_controls.py. In them, 79 spans
change.
- In run.sh and the eight Python steps, each span is the text of a path inside a string literal or a shell word, and it
  is replaced by its token.
- luitrace.py has 40 spans: 22 in docstrings, 3 in comments, and 15 in the string literals of the settlement-class text
  that its `uses` and `deadarg` modes print (lines 609-725, an agent name and a time each). The printed outputs carry
  the same tokens at the same places, and section 3.1 shows that the copy's luitrace.py prints them.
- plant_controls.py has 14 spans, 8 in its docstring and 6 in comments.
- No span of luitrace.py or plant_controls.py is a path the code reads. Their code is unchanged.

The rest of every line, and every other line, is the original's byte for byte. No span adds an environment read
(run.sh line 5 reads `$HUB`, as the original does), and no import changes. Two of the run.sh lines (6 and 23) change
only a comment.

| line | token | the line as shipped |
|---|---|---|
| `dupnames.py:14` | `DONOR_TWIN` | `` C = 'DONOR_TWIN' `` |
| `dupnames.py:15` | `DECODE_A_TWIN` | `` A = 'DECODE_A_TWIN' `` |
| `dupzone.py:9` | `DECODE_A_TWIN` | `` A = 'DECODE_A_TWIN' `` |
| `dupzone.py:10` | `DONOR_TWIN` | `` C = 'DONOR_TWIN' `` |
| `fulldiff.py:13` | `DECODE_A_TWIN` | `` A = 'DECODE_A_TWIN' `` |
| `fulldiff.py:14` | `DONOR_TWIN` | `` C = 'DONOR_TWIN' `` |
| `luitrace.py:2` | `AGENT` | `` """luitrace.py -- hand-trace helper for the KIT LIMIT of AGENT TIME (BRANCH 6d8ff128a01): `` |
| `luitrace.py:2` | `TIME` | `` """luitrace.py -- hand-trace helper for the KIT LIMIT of AGENT TIME (BRANCH 6d8ff128a01): `` |
| `luitrace.py:2` | `BRANCH` | `` """luitrace.py -- hand-trace helper for the KIT LIMIT of AGENT TIME (BRANCH 6d8ff128a01): `` |
| `luitrace.py:441` | `REVIEW_DIR` | `` reviewer scripts static_base.py + static_mem.py (REVIEW_DIR/, AGENT TIME and TIME), logic copied. `` |
| `luitrace.py:441` | `AGENT` | `` reviewer scripts static_base.py + static_mem.py (REVIEW_DIR/, AGENT TIME and TIME), logic copied. `` |
| `luitrace.py:441` | `TIME` | `` reviewer scripts static_base.py + static_mem.py (REVIEW_DIR/, AGENT TIME and TIME), logic copied. `` |
| `luitrace.py:441` | `TIME` | `` reviewer scripts static_base.py + static_mem.py (REVIEW_DIR/, AGENT TIME and TIME), logic copied. `` |
| `luitrace.py:508` | `AGENT` | `` """settlement class (e) of AGENT TIME: is REG read before it is written, on any path through the callee, `` |
| `luitrace.py:508` | `TIME` | `` """settlement class (e) of AGENT TIME: is REG read before it is written, on any path through the callee, `` |
| `luitrace.py:609` | `AGENT` | `` print('# dead = never read: the argument is dead at the call (settlement class (e), AGENT TIME).') `` |
| `luitrace.py:609` | `TIME` | `` print('# dead = never read: the argument is dead at the call (settlement class (e), AGENT TIME).') `` |
| `luitrace.py:617` | `AGENT` | `` # settlement classes of AGENT TIME, assigned per use. Citations are file:line in the pinned compiler-rt `` |
| `luitrace.py:617` | `TIME` | `` # settlement classes of AGENT TIME, assigned per use. Citations are file:line in the pinned compiler-rt `` |
| `luitrace.py:618` | `DEPOT_DIR` | `` # source of these binaries (llvm-project llvmorg-20.1.8; the local pin DEPOT_DIR/ `` |
| `luitrace.py:662` | `AGENT` | `` ' conversions (a1, a2, a3), so the saved slot is never read back (AGENT TIME (d): a spill is' `` |
| `luitrace.py:662` | `TIME` | `` ' conversions (a1, a2, a3), so the saved slot is never read back (AGENT TIME (d): a spill is' `` |
| `luitrace.py:681` | `AGENT` | `` return '(d) frame spill', 'AGENT TIME (d): a spill to the frame is not a use' `` |
| `luitrace.py:681` | `TIME` | `` return '(d) frame spill', 'AGENT TIME (d): a spill to the frame is not a use' `` |
| `luitrace.py:687` | `AGENT` | `` ' out/strictcmp3-cmp-86da41d3ef68.out. Owner ruling AGENT TIME (2): this is the STORE class,' `` |
| `luitrace.py:687` | `TIME` | `` ' out/strictcmp3-cmp-86da41d3ef68.out. Owner ruling AGENT TIME (2): this is the STORE class,' `` |
| `luitrace.py:694` | `AGENT` | `` ' constants only. NARROWED after AGENT\'s third review: this says the value is not a constant' `` |
| `luitrace.py:708` | `AGENT` | `` ' AGENT TIME: (iii) applied to the return value') `` |
| `luitrace.py:708` | `TIME` | `` ' AGENT TIME: (iii) applied to the return value') `` |
| `luitrace.py:721` | `AGENT` | `` ' callee set is {memset} and deadarg(memset, a4/a5/a6) = dead (owner rule AGENT TIME)') `` |
| `luitrace.py:721` | `TIME` | `` ' callee set is {memset} and deadarg(memset, a4/a5/a6) = dead (owner rule AGENT TIME)') `` |
| `luitrace.py:725` | `AGENT` | `` return 'OPEN', 'no class of AGENT TIME applies' `` |
| `luitrace.py:725` | `TIME` | `` return 'OPEN', 'no class of AGENT TIME applies' `` |
| `luitrace.py:768` | `REVIEW_DIR4` | `` """EVERY stop of a dead-argument walk, not just the first (the reviewer's REVIEW_DIR4/allstops.py, logic `` |
| `luitrace.py:882` | `AGENT` | `` register alone: AGENT's fourth review). LIMITS, stated: a write through a pointer obtained in another way `` |
| `luitrace.py:922` | `REVIEW_DIR3` | `` """MAY image-address analysis, the reviewer's REVIEW_DIR3/imgaddr.py (AGENT's third review), logic `` |
| `luitrace.py:922` | `AGENT` | `` """MAY image-address analysis, the reviewer's REVIEW_DIR3/imgaddr.py (AGENT's third review), logic `` |
| `luitrace.py:988` | `REVIEW_DIR6` | `` every join (the reviewer's REVIEW_DIR6/frameesc_may2.py, AGENT's final review; logic copied). The `` |
| `luitrace.py:988` | `AGENT` | `` every join (the reviewer's REVIEW_DIR6/frameesc_may2.py, AGENT's final review; logic copied). The `` |
| `luitrace.py:1131` | `AGENT` | `` its CONTENTS (AGENT's final review): a .got cell by the symbol + offset of the pointer it holds, another `` |
| `luitrace.py:1268` | `AGENT` | `` carries and, for a call argument, the callee the call resolves to. The settlement classes of AGENT TIME `` |
| `luitrace.py:1268` | `TIME` | `` carries and, for a call argument, the callee the call resolves to. The settlement classes of AGENT TIME `` |
| `luitrace.py:1316` | `REVIEW_DIR` | `` """MAY-STATIC check: the reviewer's static_base.py plus static_mem.py (REVIEW_DIR/, AGENT's reviews of `` |
| `luitrace.py:1316` | `AGENT` | `` """MAY-STATIC check: the reviewer's static_base.py plus static_mem.py (REVIEW_DIR/, AGENT's reviews of `` |
| `luitrace.py:1317` | `TIME` | `` TIME and TIME), their logic copied here. Independent of the trace's value evaluator, it asks per load / `` |
| `luitrace.py:1317` | `TIME` | `` TIME and TIME), their logic copied here. Independent of the trace's value evaluator, it asks per load / `` |
| `nmcount.py:14` | `DECODE_A_TWIN` | `` A = 'DECODE_A_TWIN' `` |
| `nmcount.py:15` | `DONOR_TWIN` | `` C = 'DONOR_TWIN' `` |
| `ownctl.py:16` | `DONOR_TWIN` | `` C = 'DONOR_TWIN' `` |
| `ownctl.py:17` | `DECODE_A_TWIN` | `` A = 'DECODE_A_TWIN' `` |
| `plant_controls.py:2` | `AGENT` | `` """plant_controls.py -- the two planted controls luitrace.py must refuse (AGENT TIME and TIME). `` |
| `plant_controls.py:2` | `TIME` | `` """plant_controls.py -- the two planted controls luitrace.py must refuse (AGENT TIME and TIME). `` |
| `plant_controls.py:2` | `TIME` | `` """plant_controls.py -- the two planted controls luitrace.py must refuse (AGENT TIME and TIME). `` |
| `plant_controls.py:7` | `AGENT` | `` as a load base (AGENT TIME): `` |
| `plant_controls.py:7` | `TIME` | `` as a load base (AGENT TIME): `` |
| `plant_controls.py:10` | `WORKER` | `` x5-logical   WORKER's plant X5 shape (AGENT TIME): the lui value goes through LOGICAL ops only and then `` |
| `plant_controls.py:10` | `AGENT` | `` x5-logical   WORKER's plant X5 shape (AGENT TIME): the lui value goes through LOGICAL ops only and then `` |
| `plant_controls.py:10` | `TIME` | `` x5-logical   WORKER's plant X5 shape (AGENT TIME): the lui value goes through LOGICAL ops only and then `` |
| `plant_controls.py:29` | `AGENT` | `` # the fresh reviewer's plants (AGENT TIME, REVIEW_DIR/myplants.py) `` |
| `plant_controls.py:29` | `TIME` | `` # the fresh reviewer's plants (AGENT TIME, REVIEW_DIR/myplants.py) `` |
| `plant_controls.py:29` | `REVIEW_DIR` | `` # the fresh reviewer's plants (AGENT TIME, REVIEW_DIR/myplants.py) `` |
| `plant_controls.py:38` | `AGENT` | `` # the second-round reviewer plants (AGENT TIME, REVIEW_DIR/myplants2.py) `` |
| `plant_controls.py:38` | `TIME` | `` # the second-round reviewer plants (AGENT TIME, REVIEW_DIR/myplants2.py) `` |
| `plant_controls.py:38` | `REVIEW_DIR` | `` # the second-round reviewer plants (AGENT TIME, REVIEW_DIR/myplants2.py) `` |
| `probe_tbl.py:12` | `DONOR_TWIN` | `` C = 'DONOR_TWIN' `` |
| `probe_tbl.py:13` | `DECODE_A_TWIN` | `` A = 'DECODE_A_TWIN' `` |
| `resolve.py:27` | `DONOR_TWIN` | `` C = 'DONOR_TWIN' `` |
| `resolve.py:28` | `DECODE_A_TWIN` | `` A = 'DECODE_A_TWIN' `` |
| `run.sh:5` | `HUB` | `` HUB=${HUB:-HUB} `` |
| `run.sh:6` | `BRANCH` | `` KITCOMMIT=3c3e62ee2786af6133699ff6684d17d66adcb03c          # BRANCH, the kit commit `` |
| `run.sh:8` | `DONOR_TWIN` | `` C=DONOR_TWIN          # donor twin ce511d541cda `` |
| `run.sh:9` | `DECODE_A_TWIN` | `` A=DECODE_A_TWIN   # decode A twin 4cb0a852e826 `` |
| `run.sh:11` | `DECODE_A_PIN` | `` APIN=DECODE_A_PIN       # decode pin 5973b76807d8 `` |
| `run.sh:12` | `OLD_RECORD` | `` OLD=OLD_RECORD/out                       # the old record's outputs `` |
| `run.sh:23` | `BRANCH` | `` #    the old repin_check e5487165abb8 that controls/negctl.py loads, from the same BRANCH commit `` |
| `run.sh:24` | `NEGCTL_ROOT` | `` mkdir -p NEGCTL_ROOT/tools/repin_check/e5487165abb8 `` |
| `run.sh:26` | `NEGCTL_ROOT` | `` > NEGCTL_ROOT/tools/repin_check/e5487165abb8/repin_check.py `` |
| `symcheck.py:11` | `DONOR_TWIN` | `` C = 'DONOR_TWIN' `` |
| `symcheck.py:12` | `DECODE_A_TWIN` | `` A = 'DECODE_A_TWIN' `` |

Each of these lines changes only where an input is read from. To run the copy, bind each token in the directory that
run.sh runs in: a symlink (or copy) named `DONOR_TWIN`, `DECODE_A_TWIN`, `DECODE_A_PIN`, `OLD_RECORD` and
`NEGCTL_ROOT`, and `HUB` (or set `$HUB`).
- The same input is read wherever the original read it. In the original, one literal stood for each input in run.sh
  and in every script. The checker proves (step 3) that each token replaces exactly one path, every time.
- The scripts check what they read. Seven of the eight edited scripts print the sha256 of each image they open in
  their output header, and the shipped outputs show `ce511d541cda` for DONOR_TWIN and `4cb0a852e826` for
  DECODE_A_TWIN. dupzone.py prints no sha; its re-run output below is byte-identical.
- Re-run: in a scratch directory, the tokens were bound to the original inputs, each checked by full sha256:
  - DONOR_TWIN `ce511d541cdabbe3c8df3f672dc517e8b5a7edd37b280a7483043b438de0adf7`
  - DECODE_A_TWIN `4cb0a852e8262acb5ed0fa075a6bee7b1a25192189b168e777c760a4bfd65ae2`
  - OLD_RECORD/out/pairs.tsv `44cd93f1...`, OLD_RECORD/out/numerals.tsv `864c8539...`
  - ../numdiff.tsv `79129d06014e7c04aae1c62b7e83b35ed685050d10c8ab2a5760decc19754a34` (= provenance/alloc-reloc/A/numdiff.tsv;
    run.sh names it by that relative path, an input the reader binds like the tokens)
- Run that way, with the kit at `cmpkit-4bbd3a74be89` (given to resolve.py as `cmpkit-4bbd3a74be89`, the spelling
  line 1 of out/resolve-kit.out shows) and pyelftools 0.33, the eight edited scripts of the copy
  gave outputs that are byte-identical to the shipped out/ files: symcheck.out, resolve-kit.out, resolve-kit.tsv,
  dupzone.out, fulldiff.out and nmcount.out.
- The exceptions are ownctl.out, probe_tbl.out and dupnames.out. They are byte-identical from line 2 on. Their line 1
  prints the absolute path of the kit directory that the run used, and the copy shows that line as
  `# kit KIT_PARENT/cmpkit-4bbd3a74be89 ...`.
- Three run.sh lines carry a sha in their trailing comment: 8 `ce511d541cda`, 9 `4cb0a852e826`, 11 `5973b76807d8`.
  Lines 24 and 26 carry `e5487165abb8` in the kept tail of the path. In each case the sha is outside the span and
  unchanged.
- NEGCTL_ROOT: run.sh writes the old repin_check e5487165abb8 from the kit commit to
  `NEGCTL_ROOT/tools/repin_check/e5487165abb8/repin_check.py`. The kit's controls/negctl.py (sha-pinned by the kit's
  SHA256SUMS) reads that file from its own fixed path. So NEGCTL_ROOT must be bound to the root of that path, as the
  original wrote there. The control's own check stays: run.sh diffs its output with the kit's
  controls/repin-negctl.out.
- HUB: line 5's default is now the relative name `HUB`.

### 3.1 The hand-trace scripts, run from the copy

The copy's luitrace.py (sha256 `3f3ff007156b85dcfce882255fc60aaf293ce8682a0dee57e61ec00dd488294d`, the file as shipped
here) was run in a scratch directory on the original inputs, with python 3.12.3, pyelftools 0.33 and capstone 5.0.7:
- C = `cgif_file_fuzzer.asan-ubsan`, sha256 `ce511d541cdabbe3c8df3f672dc517e8b5a7edd37b280a7483043b438de0adf7` (DONOR_TWIN);
- A = `fuzz_decode.asan`, sha256 `4cb0a852e8262acb5ed0fa075a6bee7b1a25192189b168e777c760a4bfd65ae2` (DECODE_A_TWIN).

Both runs give outputs that are byte-identical to the shipped outputs, tokens included. That shows the 15 string-literal
spans are the labels these outputs print, and nothing else:
- `python3 luitrace.py uses C A "$FNS"` (the 7 names of `out/run-strictcmp2.out`, LUI-HANDTRACE.md line 85) gives
  sha256 `9e4d1afcfe51556dd7964f28f2d62e0750db80961ed4c3da3a9365d1a47be15a`, the shipped `out/luitrace-uses.out`.
- `python3 luitrace.py deadarg C A "<callee>:<reg>,..."` (the 16 pairs of `out/luitrace-deadarg.out`) gives sha256
  `0c2f4aba9621260d6fd76d6358b26d268b24da9d320733b7910fe0740b5c1cb1`, the shipped `out/luitrace-deadarg.out`.

The other luitrace.py outputs, and `out/plant-controls.out`, print the image paths they were given. Here those paths are
tokens. The checker proves that every byte outside a span is the author's byte.

## 4. Files (the manifest of this directory)

Every file here except this one, with the sha256 of its bytes as shipped. For a file of the original, the file sha256
it has at commit `ec63ec6c4ede` (the first 12 hex digits; a file of the check has `-`), and the number of replaced
spans. `python3 copycheck.py <hub clone> --write-table` wrote this table from the original in git and the files here,
and copycheck.py checks every row.

| file | original file sha256 (12 hex) | sha256 as shipped | spans |
|---|---|---|---|
| `COPY.diff` | - | `aa47e8b189e00ed60ca4193f4fe8edff349c9dcde07da3357a6a465debbf2d6a` | 0 |
| `KIT-RERUN.md` | `510be3d58e19` | `ddcfcfa5e36bd456e579dde539a601d3b8d2948638a6f8453a68c5f1d7fc65d7` | 32 |
| `LUI-HANDTRACE.md` | `0a84f5028823` | `f77b0ff6100f59b4101d1ed5aa9ebb908e869d618dd40419ca97d7d6d8623f2b` | 44 |
| `SCANS-86da41d3ef68.md` | `fc4110d36cee` | `f698dd22516b97f19e4833780f932447cd50f3f98219de91dd1cdc01dda4092c` | 17 |
| `copy-edits.tsv` | - | `90f33a4039604efcdb6eb2870af5e8279d7becfb91d4ee442122169d6ecbadc0` | 0 |
| `copycheck.py` | - | `1f938d7f96119fdde99871e8089d11043443a01ada6b6aa371b4a970084ba03b` | 0 |
| `dupnames.py` | `d0880e787820` | `0842c9a2158a50e7a4eafca8a7c119eba6f012a9c47fd0ee44d2f637e810ba00` | 2 |
| `dupzone.py` | `b3d90a3bdd56` | `fcca6e8412916fd2759a397b8f6424c9d3130faf7155ee0fbdccd753baa8cb37` | 2 |
| `fulldiff.py` | `ee27ec111ade` | `45502f973e6040690d86ca8fedb708054ac690275f371e919af5797f879e9fd7` | 2 |
| `headers.py` | `b65e11968446` | `b65e119684468462fc20541b16b2e4efc7d7b8555bc443c1b183fd576c9427dd` | 0 |
| `luitrace.py` | `c3409fe33a88` | `3f3ff007156b85dcfce882255fc60aaf293ce8682a0dee57e61ec00dd488294d` | 40 |
| `nmcount.py` | `0a1a4c4bacc7` | `b18f21c5e802a8a82592ff0e494368cdd7cd68c1587e5bf2931918bd4de6cdef` | 2 |
| `numerals.py` | `dbcab24e7538` | `dbcab24e7538aaac17884f90d6a6efb04c15b88878910a4a4b53154b956d4d11` | 0 |
| `out/ambiscan-86da41d3ef68.out` | `bedfa33f8109` | `65e4e4745a9bfb7e91b20efc8bdfbaf9fe14176abc1e0fb9b57945f2e2f7cf11` | 2 |
| `out/dupnames.out` | `b2a1850b20d3` | `c3cea134e6303c972294fcf954b33da4114ea6484f3331b652e348e8d1feff1b` | 3 |
| `out/dupzone.out` | `fe6daa43a560` | `fe6daa43a5604d70ede6812e2270e68bcad9e51d87e45c242c60920fcae18090` | 0 |
| `out/fulldiff.out` | `7c1237a30a24` | `35e584a911f6a39802b7bda9ab2e89e578e9d9f1763f9c3e28c87e703ac7868f` | 2 |
| `out/headers.out` | `70db95c6a3ce` | `5c52416dc6d62fed00ddd9553d8cfecad78ab346609b86d43c1a0f6903edcfdf` | 1 |
| `out/luiscan-86da41d3ef68.out` | `4aaea46a8e2d` | `5102bbc4ba074207f72feb8f87c21f9198c5c76faf0d131778569ab4fa2eb86d` | 2 |
| `out/luitrace-bases.out` | `6f0005630ab3` | `45a2335d3230140cb554f76af5c3c84775db9946d4b8c9928c1919d6366dead0` | 2 |
| `out/luitrace-deadarg.out` | `5609d1373d8e` | `0c2f4aba9621260d6fd76d6358b26d268b24da9d320733b7910fe0740b5c1cb1` | 2 |
| `out/luitrace-ea.out` | `352a87024aad` | `352a87024aad72a3b6698135b17712a2d366e976495b8a672cafcadf5092f554` | 0 |
| `out/luitrace-frameesc.out` | `59db77fb99b2` | `59db77fb99b235afd0e8126379596d200c8106e51a7d80d6756406b764686511` | 0 |
| `out/luitrace-maystatic.out` | `b8e9e74ce8f1` | `8187e91a3a9abe7a6d46a68c663a9aa466c313b4192f18cef7eba37a1af97b4b` | 2 |
| `out/luitrace-openclose.out` | `56bade8dce5e` | `56bade8dce5ed59cae5f80153e55d44d626516eafdd72ebb49588ba5944b25e2` | 0 |
| `out/luitrace-ops.out` | `496bb4fd41ae` | `496bb4fd41ae6d5a5d8793689d4118e23b5ffced4a5a3b6961e3ff1e48a46f78` | 0 |
| `out/luitrace-pair-86da41d3ef68.out` | `05274eaaa6f9` | `65683c904d47acb324cec237fb5df12b7e1916d75614b61844611eaf430e83a1` | 2 |
| `out/luitrace-shapes.out` | `d4724ffff695` | `d4724ffff695f5301ced7d9a8d8cda207241d0dd831fc90c59adea148cf3b365` | 0 |
| `out/luitrace-uses.out` | `98bb80c3dbca` | `9e4d1afcfe51556dd7964f28f2d62e0750db80961ed4c3da3a9365d1a47be15a` | 368 |
| `out/luitrace-windows.out` | `380bb572f90e` | `f60563e1cb18bf381bada93f6b31a09c897a0d5adf820f3a0625704f0f5bd572` | 2 |
| `out/luitrace-words.out` | `d73378066164` | `d73378066164885ab38d0fd9e99ca253160ddfca37c47536db0f789c59ea9bf6` | 0 |
| `out/negctl-mine.out` | `019b8d79d949` | `630723aa8599aa39c33dc4afa3a74f6e9948e8c3ab821006b364a366f7f2a731` | 3 |
| `out/nmcount.out` | `01703150d4e5` | `ea2050c87d88122ed06134715bc6732b99d12ae14c3818425791f81be5862e9a` | 2 |
| `out/numerals-kit.out` | `9def71ced7d9` | `a914e9be0b6482f0ee4e0e898a9c00047a4b9aaa56b3af241003b9f2b356e200` | 2 |
| `out/numerals-kit.tsv` | `efffe9954be2` | `efffe9954be2d4ba89607dacd3a5043a47884e7d37a4e294ca8ff5a78d8905ee` | 0 |
| `out/ownctl.out` | `52d46e2dee8f` | `acda530712a18e9f170db1df6aa34a65d5b521ef0d5974c05d6ef28f184e9df4` | 3 |
| `out/plant-controls.out` | `cd91dd415d06` | `33b72bce7ca72e29aaeca1f5011beef728c7bc7b1456b21d1c1dc98db6ad8e7a` | 14 |
| `out/probe_tbl.out` | `b31b07d7525b` | `aa231e67b707d05b2ff99e31b39ba5479581b1748b978049978761e39a8e28e3` | 3 |
| `out/resolve-kit.out` | `05c6ff4e5850` | `4b563dbd73e240cb960779113451101a6b1b9c43e0da07bf023fea630f895f6b` | 2 |
| `out/resolve-kit.tsv` | `ac8703efb975` | `ac8703efb9752e66173a470b2c118ed38ec5069eb706929fa070f522e6fd90b7` | 0 |
| `out/run-strictcmp2.out` | `677c17346228` | `a8617069a85bc373d8ecf839dcff976d0f9bba8c524f62db1a518f6020521b72` | 2 |
| `out/scans-kitsha.out` | `b66daf86c1a6` | `b66daf86c1a662405ce55ce05e82020593d4155cc9618703c6f0bde00dc02019` | 0 |
| `out/strictcmp3-cmp-86da41d3ef68.out` | `48ea2429b429` | `dadd591db7d8bf99e775b500826e8527ee336c7d1dbc364a4f551513d974c7a8` | 2 |
| `out/symcheck.out` | `84e5395862a7` | `5d9f8a915ed26f273d51152417c31d079cd9a2e5f094e0547423724f227bc0c8` | 2 |
| `out/twins.out` | `ddfc13e2e860` | `ddfc13e2e86042c2a386c299648618c0f969d30aaaa0610b3d4a20064571ff2f` | 0 |
| `ownctl.py` | `bdc9e837acd8` | `0d6a4ac6dd90e1afb44c7f7b843558e314ef2df346554257eefe43242fb5a80f` | 2 |
| `plant_controls.py` | `77db029aa262` | `ecfb1bb9ee4dc1a3e57db9bb1450c08d8c6034267c9d762f7f56039f0a24b722` | 14 |
| `probe_tbl.py` | `827516da8990` | `f5c1b37e03d154f8e125fa8d24e3d7112c1ba4c11c021b88b0a90153d0a5e734` | 2 |
| `resolve.py` | `b6f2612cac18` | `a52ca3837a4ccb804aae083109009532fc2e858e64005f7d54acda28671c2318` | 2 |
| `run.sh` | `fa153ce7d741` | `d897c3de0da0c69e9165c299efab0e887583ae5fc00fe99f02bab44fa07985e4` | 9 |
| `symcheck.py` | `14d5908def19` | `9ab07cd9920ec27b73e9b66a67974c013a5eb43117d097708a7fdbedc2a67e22` | 2 |
