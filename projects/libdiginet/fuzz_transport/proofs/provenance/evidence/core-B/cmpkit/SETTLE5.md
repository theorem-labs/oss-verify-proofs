# Five runtime functions on cmpkit 86da41d3ef68 (row TCB, image B): kit verdict and settled verdict

Kit: the tool registry 98e50c029045 tools/cmpkit/86da41d3ef68/ (SHA256SUMS: all 9 files OK). Compare: strictcmp3
65688e94214a, donor libreac fuzz_decode.asan-ubsan twin (6744989bb2e6) vs libdiginet fuzz_transport.asan-ubsan twin
(e217cb0a84f1; pin 41113a03c82f). Each name has exactly one sized FUNC copy in both twins (strictcmp3 refuses
otherwise; settle5-B.py asserts it). The full differing-target list is read from tcmp, not the printed rows.

| function | D / T, size | kit (tcmp) | targets | settled |
| --- | --- | --- | --- | --- |
| SizeClassAllocator64<AP64>::MaybeReleaseToOS | 0x341a8 / 0x351a0, 492 | EQUAL-mod-pcrel words, 2 targets differ | +0x140 BYTE table (`srli a3, a3, 0x3a` then `add` + `lbu`: N = 1 << 6 = 64, the ctz De Bruijn table, at 0x10480 on both); +0xdc lui 0xf4240 | EQUAL: the 64 bytes are equal; lui: `mul a1, a1, a3` only (1000000), no address use |
| __sanitizer::VSNPrintf | 0x66340 / 0x67530, 1464 | 1 target | +0x1c0 rel4 switch table, N 33 / 33 | EQUAL: every entry the same VSNPrintf+offset |
| __asan::Decorator::ShadowByte | 0x5482c / 0x55d80, 160 | 2 targets | +0x14 rel4 switch table N 83 / 83; +0x80 empty string (a1 := "", `mv a0, a1; ret`: the function returns it as a C string) | EQUAL; EQUAL |
| __sanitizer::SignalContext::Describe | 0x660f8 / 0x672e8, 60 | 1 target | +0x1c rel4 STRING table N 8 / 8 | EQUAL: ILL TRAP ABRT BUS FPE UNKNOWN UNKNOWN SEGV, each with its NUL |
| __strftime_fmt_1 | 0x96fec / 0xa1840, 1572 | 10 targets | +0x44 rel4 switch table N 86 / 86 (= '%%' .. '%z': guard +0x34 `bltu a6, a1` with a6 = 0x55, a1 = c - 0x25; entry [0] is the `%%` case); +0x530, +0x54c empty string (a0 := "" then the return path: returned as a C string); 7 lui values 0x20007 / 0x20028 / 0x20029 / 0x2002a / 0x2002b | EQUAL; EQUAL; lui: see below |

0 REAL differences (no differing instruction word, no differing named target, no table entry whose symbol + offset
differs). 0 not certified.

lui values (luitrace-B.T.out / .D.out, the same trace on both images up to pc-relative fields): the five values are
musl's nl_langinfo item numbers (DAY_1 0x20007, D_T_FMT 0x20028, D_FMT 0x20029, T_FMT 0x2002a, T_FMT_AMPM 0x2002b).
Every use, followed through mv / add / addw / addi / addiw (the kit's dataflow does not follow add / sub / shNadd):
the item, or item + index, reaches `nl_langinfo_l`'s first argument (+0x480, +0x508), or is overwritten, or dies at a
call whose callee takes one argument (__tm_to_secs, week_num, __tm_to_tzname: a1 is not an argument) or at `ret`
(the function returns a0). 0 MEMORY BASE uses: none of them is an address. The D_T_FMT value set before the switch
dispatch (+0x64 `jr t2`) was followed into all 37 distinct case targets of the 86-entry table. MaybeReleaseToOS's
0xf4240 (a3) is also still live at its call to MonotonicNanoTime (+0xec), which takes no arguments and does not read it.

Inputs and outputs: settle5-B.py, settle5-B.out, luitrace-B.py, luitrace-B.T.out, luitrace-B.D.out, cmpkit5.out (the
kit's own `cmp` rows).

FRESH REVIEW (a fresh review subagent, 22:5xZ, own scripts): every guard N re-derived from the bound check (VSNPrintf
+0x1b4 `bltu s0, a7` N 33; ShadowByte +0x8 `bltu a2, a1` N 83; Describe +0x10 `bltu a1, a0` N 8; __strftime_fmt_1
+0x34 N 86; MaybeReleaseToOS +0x13c `srli ..., 0x3a` N 64) equals the claimed N; every entry, string and byte equal;
the empty strings are only returned; the lui values have no load / store / jalr base use and the named callees ignore
a1; tcmp refuses exactly these 16 targets; every differing word is an auipc / jal / lo12 after an auipc. CONFIRM on 4
rows, SEND BACK on 1 for this text only (the strftime range was written '%A' .. '%z'; corrected above to '%%' .. '%z').
