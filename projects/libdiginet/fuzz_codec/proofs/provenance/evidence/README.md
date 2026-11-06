# Evidence: libdiginet/fuzz_codec

- `untime-removed.tsv`: the `timeout N` markers this release removed from four proof files
  (`lib/A/ACeg.v`, `lib/A/ACeh.v`, `lib/AU/YCeg.v`, `lib/AU/YCeh.v`), one row per marker, written by the untime tool.
  The files build without them. The table's paths are as the tool wrote them, in the unit's old layout; each names
  the file of the same `lib/...` path under `projects/libdiginet/fuzz_codec/proofs/` in this tree.
- `lib/A/AB1w.v` and `lib/AU/YB1w.v` no longer define `tfib_A_libc_exit_fini_call` and `tfib_E_libc_exit_fini_call`.
  In both images the value was the start and end of atexit.c's static function `call` (0x8d28c in fuzz_codec.asan,
  0x8dbc4 in fuzz_codec.asan-ubsan), not `__libc_exit_fini`, which starts 8 bytes later. The names came with the
  copied symbol table; no proof read them.
- `lib/Reusable/R/Cfg.v` is the reviewed clean-room restatement of this shared file, byte-equal to libreac/fuzz_ctrl's
  copy (file sha256 2e67e5f0d5001849488d25a4e83198f82f69c7c9100e79bb542fa955f45c6fa8).
