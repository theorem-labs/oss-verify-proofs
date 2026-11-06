# Start-up records of image A

The run logs, check outputs, scripts and header records of reac-pw/fuzz_link image A's start-up files are kept,
unchanged, in an internal record (its file list with each sha256: path MANIFEST, sha256
ffcf718548602b26fb255a992abf87180fb811930cdf6aabf9510c59d56eb4cc). This directory carries one statement per group, with the facts, the commands, the tool and image sha256
values, and the path and sha256 of each recorded file:

- `RUNS.md`: the generator and check runs (hsform, itabranges, plantail, af0m, ifchk, gen_ad2, gen_ad1k, pins, codeptr,
  imgread_check.py, asan_globals_check.py), and the 2026-10-30d gen_ad2 run that wrote lib/A/AD2i.v and lib/A/AWH8.v
  (its tool list and tool check are in `runs-30d/`).
- `acej/ACEJ.md`: lib/A/ACej.v (regen.sh, acej_check.py, compose_jt.py, the universe report).
- `ae37/AE37.md`: lib/A/AE23.v and lib/A/AE37.v (ae37gen.sh and its output).
- `HEADERS.md`: the licence-header record (headers_check.py, STARTUP-HEADERS.tsv, AF0m.body-removed.tsv).

`AF0m.owned-with-bss-globals.v` in this directory is the file that lib/A/AD2j.v (line 4) cites at
`provenance/evidence/startgen/AF0m.owned-with-bss-globals.v` (sha256 2c69c569c0239b86f21a93e6d54ad35865bbf5ce20e255016a5c5e3f566747b1).
A byte-identical copy was also kept at `provenance/startgen/AF0m.owned-with-bss-globals.v` and was removed on
2026-10-31: `tools/oft/paths.py` allows no such path under `provenance/`, only `provenance/evidence/**` and the
named PROVENANCE / recipe / port / LICENSES entries, and `oft lint` reported it. This directory's copy is the one
that survives. The run records below quote each run's arguments and inputs AS THEY STOOD WHEN IT RAN, so they
still name the removed path; those lines are a record of a past run, not a live citation, and are left as written.
One change from the generator's file: the comment on line 4 names the start-up tool set by its commit instead of by
its branch. No definition, number or address changed. The file before the change:
path proofs/reac-pw/fuzz_link/provenance/startgen/AF0m.owned-with-bss-globals.v,
sha256 ab0e0e1cb877f6f8f89113a58d44746d469b6cb63ee6a614977c22a0d8e37725; the same bytes are in the internal record, path
startgen/AF0m.owned-with-bss-globals.v, sha256 ab0e0e1cb877f6f8f89113a58d44746d469b6cb63ee6a614977c22a0d8e37725. That version (Tfib_const_abs 767 rows, with the
interceptors' flag-byte and REAL(f) cells) is the owned-cells input of the 2026-10-30d gen_ad2 run in `RUNS.md`. The
2026-10-30b gen_ad2 run in `RUNS.md` read the earlier version (Tfib_const_abs 736 rows): internal record, path
startgen/AF0m.owned-with-bss-globals.v, sha256 855f0996314d4c751b7187c0d57f151db7052161821e823ae52457eec3d3effb.

`acej-wild-listing.txt` is the listing that lib/A/ACejUniv.v (line 19) cites at
`provenance/evidence/startgen/acej-wild-listing.txt`.

`../af/` holds the script checks of lib/A/AStackApi.v (af_stack_classes.py with its output and two controls;
bypath_check.py with its output and control). lib/A/AStackApi.v (lines 4 and 30) cites them at `provenance/af/`; the
files in `../af/` are byte-identical copies of those.
