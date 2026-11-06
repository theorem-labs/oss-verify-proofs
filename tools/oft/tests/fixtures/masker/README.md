# The masker fixture of test_symbols.py

`fuzz_ctrl-asan.json` holds six functions of the asan runtime in the `fuzz_ctrl` asan and asan-ubsan builds of
FreeREAC/libreac 3425050 and 1842185: `___interceptor_strcmp`, `___interceptor_memcmp`, `___interceptor_bcmp`,
`___interceptor_wcrtomb`, `__asan::PoisonShadow` and `__unw_step`. 1842185 changed `fuzz/fuzz_ctrl.c` only, so these
functions differ only where the data they address moved (683 data objects); 40e964d5bd98 classified all six
`changed` (`changes/masker/README.md`). For each function and build the file holds its address and bytes, the SHA-256
of its masked bytes, and what `symbols.mask` asked of the build's Image (`symbols.build_image`) while it masked them:
the addresses it found in `noreturn`, every `constant` and `data` read and its answer, the stored code addresses
inside the function and the landing ranges over it, and the build's sections. It also holds
`__sanitizer::VSNPrintf` of the 1842185 asan build, the bytes its jump table proof reads and the table range
`jump_table_words` finds.

[`make.py`](make.py) writes it from the two builds' work directories (`raw/<build>/fuzz_ctrl`, the unstripped twin,
and `out/fuzz_ctrl/fuzz_ctrl.<build>`, the stripped binary), as `tools/check` leaves them; each build was reproducible
(the second build gave the same 36 binaries). Run in `tools/`:

```sh
PYTHONPATH=. python3 -B oft/tests/fixtures/masker/make.py WORK_3425050 WORK_1842185 > oft/tests/fixtures/masker/fuzz_ctrl-asan.json
```
