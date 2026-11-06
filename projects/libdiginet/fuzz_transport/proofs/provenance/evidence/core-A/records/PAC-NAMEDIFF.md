# Addendum to records/PAC-GATE.md: named-symbol rows that 205a90fd19b8 passes and 0d24592683b6 flagged

proves no function (kind: measurement). The checker's owner reported at 08:31Z that port_addr_check 205a90fd19b8 fails
open when a cell's name contains the name of the symbol at its value (boxreg's AB1w.v `tfib_A_asan_register_globals`
holding `__asan_register_elf_globals+0` passes as SAME-SYMBOL, where 0d24592683b6 flagged it). This addendum diffs the
named-symbol rows of the two checkers on the run of record and reads each row that changed against the twins.

## Inputs and commands

- The two runs, both on WORK = work-rec5 with LIB = the run's lib, by the same gate scripts (pac-A.sh a06e8121786b,
  flag-gate-A.sh 1c7b72e40c30, triage-A.py 95a4f4b1996c). The 205a90fd19b8 run was repeated after edits of the
  scripts' comments and printed text (pac-A.sh cf205cb0cdd8, flag-gate-A.sh 1624404302eb, triage-A.py ce9ec163a04c);
  its raw rows OUT/pac/rec.tsv are byte-equal to the ones this diff read, so the diff stands:
  - 205a90fd19b8: the gate run of record, `checks/run-gates.sh WORK LIB OUT` (records/flag-gate.txt, OUT/pac/rec.tsv);
  - 0d24592683b6: `SHA=0d24592683b6 gates/flag-gate-A.sh WORK LIB OUT0` (records/flag-gate-0d24592683b6.txt, OUT0/rec.tsv):
    `FLAGGED 521 rows in 9 classes: DIFFERENT-SYMBOL=63 ...`, `UNMEASURED-NAME=7`, `checker files: 6 of 6 in
    versions/0d24592683b6.SHA256SUMS OK`, triage `528 explained, 0 UNEXPLAINED`, `controls: PASS`.
- The diff: `DST_TWIN=<fuzz_transport.asan twin 86efc3a80314> SRC_TWIN=<fuzz_grant.asan twin 57c26f993615>
  checks/pac_namediff.py OUT0/rec.tsv OUT/pac/rec.tsv records/pac-namediff.tsv`. It joins the raw rows of the two runs
  on (src_file, src_line, dst_file, dst_line, sentence, idx, src_value, dst_value) and keeps each row that 0d24592683b6
  calls DIFFERENT-SYMBOL or UNMEASURED-NAME and 205a90fd19b8 calls SAME-SYMBOL. For each it reads the cell's stated name
  `<prefix>_(A|D|E)_<name>` against the twin: the symbols at the value (for an A cell the symbols that start there; for an
  E cell the function that ends there, the end of the walked region), and where the twin has a symbol named `<name>`
  (up to leading underscores). It reads the donor's value in fuzz_grant's twin the same way.

## Result (records/pac-namediff.tsv)

    rows 0d24592683b6 calls DIFFERENT-SYMBOL or UNMEASURED-NAME and 205a90fd19b8 calls SAME-SYMBOL: 54; stated function
    DIFFERENT from the one at the value: 54; SAME: 0; donor and port values carry the same symbols: 54 of 54

All 54 rows are cells of A/AB1w.v's function table (27 cells, an A and an E row each); 48 were DIFFERENT-SYMBOL and 6
UNMEASURED-NAME under 0d24592683b6. In every one the stated function is a DIFFERENT function from the one at the value:

| cells (A and E rows) | value holds (twin) | the stated function in the twin |
|---|---|---|
| A/AB1w.v:76 tfib_A/E_asan_register_globals | `__asan_register_elf_globals` [0x40c20, 0x40c8c) | `__asan_register_globals` [0x3f838, 0x40654) (the cell tfib_A_asan_register_globals_impl_RegisterGlobal_loop holds it) |
| A/AB1w.v:77 tfib_A/E_asan_unregister_globals | `__asan_unregister_elf_globals` [0x40c8c, 0x40cf4) | `__asan_unregister_globals` [0x40654, 0x40c20) (the cell tfib_A_asan_unregister_globals_impl holds it) |
| A/AB1w.v:82-86, 88-96, 99-101, 103, 110, 112-115, 148-149: tfib_A/E_<f> for f = strlen, strnlen, strcmp, strchr, memcmp, memchr, frexpl, read, fwrite, time, gmtime_r, vprintf, vfprintf, vsnprintf, clock_gettime, wcrtomb, wctomb, pthread_attr_getstack, sem_timedwait, pthread_setcancelstate, send, sendto, sigaltstack, memset, memcpy (25 cells, 50 rows) | the 4-byte `__interceptor_trampoline_<f>` (alias `__wrap_<f>`), the entry calls to `<f>` reach when the link wraps `<f>` | libc's `<f>` at another address (e.g. strlen [0x9d860, 0x9d8f0), memset [0x9d614, 0x9d70c), memcpy [0x9d210, 0x9d614)); the ASan interceptor `__interceptor_<f>` is a third function (e.g. __interceptor_strlen 0x42d74) |

Verdict of each row:

- 205a90fd19b8: FAIL-OPEN on all 54 rows (SAME-SYMBOL, but the cell's name names another function).
- The relocation: RIGHT on all 54. In each row the donor's cell names the same symbols in fuzz_grant's twin (the donor
  value is `__asan_register_elf_globals`, `__interceptor_trampoline_<f>` / `__wrap_<f>` there too), so port_core kept the
  object the donor's cell holds. The names are the released donor's labels, carried from cgif_file_fuzzer's AB1w (gate (a)
  reason DS-AB1W-LABEL under 0d24592683b6); this core does not rename them. A wrong VALUE would show as a different symbol
  in the two images; there is none.
- No row has a stated function that is absent from the twin (column `stated function in the twin`: never `none`).

The 205a90fd19b8 rows of the record (records/gate-205a90-triage-rows.tsv) still hold 3 DS-AB1W-LABEL rows that it flags;
they are not in this addendum (205a90fd19b8 does not call them SAME-SYMBOL).
