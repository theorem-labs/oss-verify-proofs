# Builds, Print Assumptions and Print All Dependencies of the restated tree (13514b13daad)

The tree is 13514b13daad: the restatement in fuzz_knock's form, the YH03 changes, YI5cSat.v and the call-site list.
Every build ran on a build VM with the cb build tool (versioned cb-80326e751d22), on a clone of the series branch at
13514b13daad, called `<clone>` below. Base f7e88c4793ca, facts ed6b6b7b0abd. Each build log starts with
`cb: pins libreac/fuzz_boxreg at facts ed6b6b7b0abd: 4 PINNED, 0 MISMATCH, 0 MISSING, 0 UNPINNED, 0 ABSENT` and a
passing sync check.

## Builds

| build | command | result |
|---|---|---|
| build-20261030T205259Z (dune, the shared cache) | `cb build <clone>` | rc 0, wall 5453 s: 2904 targets, 697 compiled, 2207 restored from the cache, 0 failed |
| build-20261030T222454Z (record) | `CACHE=none cb build --fresh <clone>` | rc 0, wall 3993 s: 932 of 2904 files compiled, 0 failed |

The record build is not a from-scratch build. `--fresh` starts from the unit's packed base, whose .vo files rsync
keeps, so only the files that changed and the files that depend on them are compiled: 932 of the 2904 files of the
make build (lib/ at any depth, 2897 files, plus the 7 tops' Proof.v). Its compiled files include both YH03.v, both
YI5cSat.v and the 7 Proof.v. Two earlier dune builds of intermediate heads, build-20261030T183723Z and
build-20261030T193955Z, also returned rc 0.

## Print Assumptions of the 7 tops

`cb assume <clone> plain_halts ubsan_halts ubsan_agrees asan_halts asan_agrees asan_ubsan_halts
asan_ubsan_agrees` was run on the record build's files. Each top reports `15 axioms, all allowed`. The local ssh
stopped at its 3500 s timeout before the seventh summary line. The VM run went on and wrote asan_ubsan_agrees's
wrapper.log at 00:42Z, and that log is byte-identical to the other runs' logs too. pa/<top>/wrapper.log is oft
check's wrapper output; Wrapper.v.txt is its wrapper source, renamed so no build compiles it.

Every wrapper.log is byte-identical to the one taken before the restatement (pa-pre: the release tree, record of
b5dd72116a44 / a60f6b380c99): sha256 d0a538d26101ede9... for all 14 files. Every Wrapper.v is equal too.

## Print All Dependencies (OBLIGATIONS.md rows 29-31, 41, 271, 272)

SinkDepsAudit.v.txt is the scratch file, put at lib/SinkDepsAudit.v for the run and not committed as .v. It writes
`Print All Dependencies` of lib.Theorems.libreac_fuzz_boxreg_<top> for each of the 7 tops, under `Set Printing
Fully Qualified`, with `Redirect "sinkdeps-<top>"`:

    CB_COMPILE=proofs/libreac/fuzz_boxreg/lib/SinkDepsAudit.vo \
      cb build <clone> proofs/libreac/fuzz_boxreg/lib/SinkDepsAudit.vo
      (build-20261031T014637Z: rc 0, wall 3621 s; 1 target compiled, and 0 more compiled outside the target, so its
      dependencies are the files of the dune build above; layout line: `cb: layout old (the unit's proofs are
      proofs/libreac/fuzz_boxreg; base f7e88c4793ca, facts ed6b6b7b0abd, clone HEAD 13514b13daad)`)
    on the VM, in the clone's build directory (_build/default):
      LC_ALL=C awk '/^[A-Za-z_][A-Za-z0-9_.'"'"']* :/{print $1}' sinkdeps-<top>.out | LC_ALL=C sort -u > sinkdeps-<top>.names
    deps-gate.py <dir of the 7 .names files> > deps-gate.txt

A first run (build-20261031T004353Z) printed to the build log without Redirect. That log kept only the start and end
of the output, so the Redirect run replaced it.

| top | .out bytes | .out sha256 | dependencies |
|---|---|---|---|
| plain_halts | 42644186 | 75ebefbcdd340cab5662cb089ec24ebfd1284791dbdfba5a11aa79820871d610 | 20423 |
| ubsan_halts | 42966130 | 04355e5397db3b825f0c775e170c048f9896c9a1603294113153ca4b04e19b2d | 20534 |
| ubsan_agrees | 76946954 | 0c28e3d68b4dab2ecbcb093ef7bbf26bcaeb9781ff19bd3b60fc0286198cfc89 | 35707 |
| asan_halts | 82541196 | 754bcd89d66a99e6f74a03b2dffa6bcd241b1087bb0c8285aefd99b267eee27a | 38639 |
| asan_agrees | 118392827 | e8ccf52504584ca70ea16eb531be9fbdbfb30c587047842285e4d6dffba32053 | 50134 |
| asan_ubsan_halts | 84627138 | 6cf47d6f1fa7dd3d66bf72cdba03f2173de6ccf69676b8bc0e8fc3ebef386c4e | 39217 |
| asan_ubsan_agrees | 120474690 | dd4a29d8faffa18b90c5323981c8672f93e7ba09314e7261d68b74f31220bb4a | 50715 |

Each .out has the sections `Transparent constants:`, `Axioms:` and `Opaque constants:`. The .out and .names files are
kept outside the repository (names sha256: plain_halts c9544feb2072..., ubsan_halts 386c81387427..., ubsan_agrees
d9d835601ae3..., asan_halts 22e865d0e5f3..., asan_agrees abcc59b4d0b8..., asan_ubsan_halts dcded337b767...,
asan_ubsan_agrees de80eb02e77f...).

Results (deps-gate.txt), for all 7 tops:

- No YK09.asan_init, YK09.ASAN, AITAB or AsanRT name. The ASan tops reach YK09 only in YK09.APC (250 constants),
  which the gate does not name.
- No YI14 FILE constant: stdio_env, sink_at, file_sink_at, file_static, file_at, file_env, file_window, sink_laws,
  fopen_spec, unlink_spec, fwrite_spec or fclose_spec.
- None of the 8 ruled YH03 sink rows; they no longer exist. No YH03 string cell either. The YH03 cells reached are
  the A cells of linked functions and D cells that yh03check passes or that yh03/v64/nosym-table.*.tsv judges TRUE.
- asan_halts and asan_ubsan_halts reach no YI14, YI5b, YI5c or YH03 name (row 271 holds).
- plain_halts, ubsan_halts, asan_agrees and asan_ubsan_agrees each reach 14 YI14 names of their copy, and
  ubsan_agrees reaches the 14 of each copy. They are closed_stdio_env, env_addr, file_addr, sink_none, sk_file,
  sk_highs_addr, sk_ofl_lock, sk_ones_addr, sk_threaded, val_mem_frame, and the 4 file_sink_syms fields
  sk_path_addr, sk_mode_addr, sk_trailer_addr and sk_rwa_addr. These tops also reach YI5b.src0_sink_head and
  YI5c.src0_sink. The 4 fields are reached only as projections inside YI14.file_addr, which env_addr applies under
  `match sk_file with Some F => file_addr F a | None => False end`, and src0_sink has sk_file := None. So no top
  takes a fact about a FILE string address. Row 272's INERT verdict holds, and the string addresses that it says
  "enter as numbers via YI14.env_addr" no longer enter.
- No top reaches YI5cSat. It is a satisfiability record, not a dependency of any top.
