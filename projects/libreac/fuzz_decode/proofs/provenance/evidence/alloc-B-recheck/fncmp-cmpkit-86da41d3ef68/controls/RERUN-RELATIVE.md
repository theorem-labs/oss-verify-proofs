# controls/negctl.out and controls/suite-planted.sha256: the kit's two controls re-run with relative input names

`negctl.out` and `suite-planted.sha256` are the outputs of a re-run of the kit's controls negctl.py and suite.py with
every input under a relative name (the owner's ruling, 2026-10-31 12:50Z). The first run's outputs named each input by its
directory on the host. These outputs name it by the relative names below. Every sha256, every verdict line and the
line order are the same as in the first run; only the path text changed (section "Equality"). The other files of
controls/ are from the first run (`run-controls.sh`, ../RECORD.md section 11) and do not change.

## The re-run

`run-controls-rel.sh RUN_DIR` did the re-run on 2026-10-31 (JOBS=8; exit 0), with the inputs below in RUN_DIR. It is
run-controls.sh with these changes:

- It checks the sha256 of each input before it runs.
- The kit is the same: cmpkit 86da41d3ef68 (hub commit 98e50c029045; the sha256 of its SHA256SUMS is
  86da41d3ef68abf071a843e599786e5eb0a6ed77c4a6b6eb645e7498bffbee60; 9 of 9 OK) and the old kit 4bbd3a74be89 (hub
  commit 3c3e62ee278, 7 of 7 OK). The cross-check directory is the old kit plus the kit's
  `controls/xchk/jtcheck_strict2.py`.
- negctl.py and suite.py are not members of the kit's SHA256SUMS. The script runs copies of them that sed makes, and it
  stops when the count of changed lines is not 3 / 21 or when a copy's sha256 is not the one in the table below. The
  copies are `negctl-rel.py` and `suite-rel.py` in this directory, byte for byte. sed changes only:
  - path constants: in negctl.py `S` (the directory of the env.sh that names its three images) and `E548` (the path of
    repin_check e5487165abb8, the file of hub commit f69e6d74ebe, sha256
    e5487165abb8dfb7a39518a418fc24a0e815cea74918943bafbf35667c70ed11); in suite.py `R`, `CU`, `DA`, `PO`, `PN` and
    `E548` (suite.py does not read `E548` when SUITE_OLD_KIT is set);
  - suite.py line 26: OUT and PLANTED_DIR stay relative, and KIT stays absolute;
  - lane names, which become `<agent>`: in the labels of plants A5, V1 and V2 (as in the first run's committed file),
    and in comments and docstrings, which do not change what runs.

  | driver | the kit's original (hub commit 98e50c029045), sha256 | the copy that ran, sha256 | lines changed |
  | --- | --- | --- | --- |
  | `controls/negctl.py` -> `negctl-rel.py` | `867ce661d8d5d9e9f94931149b1671bc2ea02d5a680e89d381a50848f7350266` | `287d2110aff0ad195b4470f98e53e40f85b88264be2e29a40a9fe939c40c3c8f` | 3 |
  | `controls/suite.py` -> `suite-rel.py` | `c29e2c6b7ffacda987d856edb4fc0c8f48c1f27f118ad9f5b4424b2536c8b32f` | `a7f357899752b6bfc2a2a27dc4d27c69361b33c7eee251ff4827485e22822a2a` | 21 |

  `diff` of each original and its copy shows every changed line. The re-run first committed (commit 97e71a03582e) used
  copies that kept the lane names in comments and suite.py's `E548` (sha256 e92cc680834a and c6a9827b9bb7); its
  negctl.out and planted.sha256 are byte-identical to this run's.
- driver/env.sh gives negctl.py `FA=src5/fuzz_frame/fuzz_frame.asan`, `DA=src2/fuzz_decode/fuzz_decode.asan` and
  `DP=src2/fuzz_decode/fuzz_decode.plain`.
- The tools run with their own directory as cwd. In each tool directory (kitrun/, oldkit/, xchk/), a symlink for each
  input directory, planted/ and suite-out/ points to the one in RUN_DIR, so a relative name opens the same file there.

## The inputs

| relative name | sha256 | image |
| --- | --- | --- |
| `bin/fuzz_ctrl/fuzz_ctrl.asan` | `78efaeda1de51f8cb9208f86af7467cc8cb84e10c53295e7b6c3dce28ddcbebd` | libreac v190 fuzz_ctrl, asan (T3) |
| `bin/fuzz_ctrl/fuzz_ctrl.asan-ubsan` | `ee07e2c38d942e2b8934937ada9746fb6e66942335ac0a2693c398a3f0c65338` | libreac v190 fuzz_ctrl, asan-ubsan (T3) |
| `src1/fuzz_lock/fuzz_lock.plain` | `04ef57cccba30736e8e7bbacaa27832e18b470f7e6235ca6a1cd77cbf4531fb2` | reac-repacer result, unstripped |
| `src1/fuzz_uci/fuzz_uci.asan` | `56822e263d767986a76ec862cbfbee7571b0e64df2413ad18d7201205a7563fb` | reac-repacer result, unstripped |
| `src1/fuzz_uci/fuzz_uci.plain` | `bf96847dbf1b9ab1e827610a8f10d6fff77e1406f7b1819547fd3763c6250522` | reac-repacer result, unstripped |
| `src1/fuzz_wire/fuzz_wire.asan` | `d2f662a229626fd402f1018631498190e800834bad837fa4027204b79088b128` | reac-repacer result, unstripped |
| `src2/fuzz_decode/fuzz_decode.asan` | `4cb0a852e8262acb5ed0fa075a6bee7b1a25192189b168e777c760a4bfd65ae2` | libreac fuzz_decode, unstripped |
| `src2/fuzz_decode/fuzz_decode.plain` | `18a5c8eae19bb74fbc117c13e83c703c4c6c96007627c4d957601805c6ef78fa` | libreac fuzz_decode, unstripped (negctl.py only) |
| `src3/fuzz_preset/fuzz_preset.asan-ubsan` | `c90d4fa54d43160baf62e5aa387211a798dddbad13d2619d85acbf37aee0c175` | fuzz_preset #102 B (bound-fix 9e1283d1) |
| `src4/fuzz_preset/fuzz_preset.asan-ubsan` | `3b5e1a099b535acf2c4e81d857fed63daaf3cf5e758d7fe50834a6bd419c3c58` | fuzz_preset old B |
| `src5/fuzz_frame/fuzz_frame.asan` | `67d7e481d74edac58be0e018835f577491192d461b4a35bd4109dc4ab0494fd5` | libdiginet fuzz_frame, unstripped (negctl.py only) |

Each sha256 is the one that the first run's outputs give for that input: in full in suite-planted.sha256, and as the
first 12 hex digits in negctl.out for its three images. suite.py writes the files of planted.sha256 sorted by path; the
relative names sort in the same order as the first run's directories, so the line order stays the same.

## Equality

norm.sed replaces each directory prefix of the first run's outputs by its relative name and changes no other text:

    s#[^ ]*/bin/libreac-v190/x/unstripped/#bin/#g
    s#[^ ]*/planted/#planted/#g
    s#[^ ]*/agents/[^/]*-next3/reac-repacer/result/unstripped/#src1/#g
    s#[^ ]*/agents/[^/]*/libreac/unstripped/#src2/#g
    s#[^ ]*/reports/preset-harness/bound-fix/9e1283d1/unstripped/#src3/#g
    s#[^ ]*/reports/preset-harness/unstripped/#src4/#g
    s#[^ ]*/agents/[^/]*-next3/libdiginet/unstripped/#src5/#g

The first run's files are blobs 07e77167602e and 5734b993541b at commit c1db711343fc, in both copies of this
directory (P = proofs/libreac/fuzz_decode/provenance/evidence/alloc-B-recheck/fncmp-cmpkit-86da41d3ef68/controls or
proofs/libreac/fuzz_decode/provenance/alloc-reloc/B/fncmp-cmpkit-86da41d3ef68/controls):

    git show c1db711343fc:$P/negctl.out | sed -f norm.sed | diff - $P/negctl.out                       # 0 lines
    git show c1db711343fc:$P/suite-planted.sha256 | sed -f norm.sed | diff - $P/suite-planted.sha256   # 0 lines

| file | first run (blob, sha256) | re-run sha256 | lines | lines with other path text | diff after norm.sed |
| --- | --- | --- | --- | --- | --- |
| negctl.out | 07e77167602e, 314168a26e3b | f3626b2fee91 | 15 | 3 (the image lines) | 0 lines |
| suite-planted.sha256 | 5734b993541b, 73bed2495053 | ea6710261c31 | 106 | 106 | 0 lines |

So the three image sha256 prefixes and the other 12 lines (the verdict lines) of negctl.out are the same bytes, and the
66 sha256 lines and the 40 plant lines of suite-planted.sha256 are the same apart from the paths, in the same order.

Two more checks of the same re-run:

- Against the outputs the kit registered (its `controls/repin-negctl.out` and `controls/planted.sha256`), after
  norm.sed, and for planted.sha256 also the two lane names in the A5, V1 and V2 labels replaced by `<agent>`: 0 diff
  lines for each.
- The re-run's SUMMARY.tsv (473 rows; not kept here) and `suite-SUMMARY.tsv` have the same seven verdict columns
  (plant, family, tool, sha12, version, baseline verdict, planted verdict) in all 473 rows.

../RECORD.md section 11 and `compare.out` describe the first run. For this re-run, `negctl.out` is equal to the kit's
`repin-negctl.out` after norm.sed, not byte for byte.
