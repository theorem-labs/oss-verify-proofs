# codeptr-decl.sh -- the values codeptr 12348302dfd2's pass 1 (logs/G2c.codeptr.pass1.log) reports as STALE that are
# NOT stale, each declared with its ROLE and its symbol / section + offset (or term) in BOTH images: fuzz_uci B pin
# a1b86e424add (names: twin .symtab) and cgif B 1c29845fe605 (stripped; names: the recovered nm of its release).
# Form = the image-A start-up gates' (uci-sg/start/*/run_*.sh): --same only for a value that IS an address meaning the
# same thing in both images (gp); --not-address for a length, a bound, a stored value or an instruction word. The value
# set is fuzz_decode B's SAME_COMMON (codeptrc0ce/same.sh, 19 values); every fact in each reason is re-checked on THESE two images
# by tools/decl_evidence.py (logs/G2e.decl_evidence.log, rc 0 = every fact holds). Sourced by run_gates.sh (G2d).
DECL=(
  --same '0x10800=SYMBOL __global_pointer$ (gp) of fuzz_uci B (twin .symtab) and cgif B .rodata+0x520 (stripped; cgif YF0m TFIB_GP := 0x10800): register x3 of all 50 hand-off states (YB01) and of the join state (YB03), YD2i sregs_main SLit 67584, YF0m TFIB_GP, the same in both images'
  --not-address '0x10101=VALUE of the 4-byte cell _ZN6__asan28asan_flags_dont_use_directlyE+0x70 (uci 0x9c968, cgif 0xa3ae8; flag bytes 01 01 01 00): YB01/YB03 KWord .. 4 (ELit 65793), YF0m Tfib_const_abs z8 (ANum 0x9c968) 0x10101 / cgif z8 (ANum 0xa3ae8) 0x10101'
  --not-address '0x100000=SIZE 1 MiB: VALUE of _ZN6__asanL8instanceE+0x328 (uci 0x9bdc0, cgif 0xa2f40; YF0m z8 rows), am_len of the anonymous mapping 4096*EVar 500 and the shadow-band length of mapping 4096*EVar 501 (8 MiB / 8) in YB01/YB03, the same terms in cgif YB01/YB03'
  --not-address '0x20000=LENGTH 131072 = 1 MiB / 8: the shadow-band KDisj window (0x7fff8000 + 512*EVar 500, 131072) of the 1 MiB anonymous mapping 4096*EVar 500 in YB01 (am_len 1048576 in both images)'
  --not-address '0x71c00=LENGTH 465920 = 3727360 / 8: the shadow-band KDisj window (0x7fff8000 + 512*EVar 254, 465920) of mapping 4096*EVar 254 in YB01/YB03 (am_len 3727360 in both images)'
  --not-address '0x161200=LENGTH 1446400 = 11571200 / 8: the shadow-band KDisj window (0x7fff8000 + 512*EVar 424, 1446400) of mapping 4096*EVar 424 in YB01 (am_len 11571200 in both images)'
  --not-address '0x38e000=LENGTH 3727360: am_len of the anonymous mapping 4096*EVar 254 (KDisj (4096*EVar 254, 3727360)) in YB01/YB03, the same in both images'
  --not-address '0x1ffff=BOUND KRange (EVar 3) 0 131071 / KRange (EVar 7) 0 131071 of the hand-off and join states (YB01/YB03), the same term in both images'
  --not-address '0x445c0=BOUND the decimal 280000 of KRange (EVar 4) 0 280000 in YB01/YB03, the same term in both images'
  --not-address '0x100018=VALUE 1048600 of the KWr cell at 4096*EVar 0 + 2*EVar 6 + 0x7fe00000 (then KZero) in YB01/YB03, the same term in both images'
  --not-address '0x3fffff=BOUND the tid upper bound 2^22 - 1: KRange (EVar 43) 1 4194303 (YB01/YB03), KRange (EVar TIDV) 1 4194303 (YD2i), mkAF 1 4194303 0 (YD1y), the same terms in both images'
  --not-address '0x55c000=LENGTH rw_len = page_ceil(image top) - rw_lo: uci 0x5f4000 - 0x98000, cgif 0x5fb000 - 0x9f000 (YB12 rw_len, YB1h tfib_res_eq last window, YB13 tfib_hex3 5619712); the BASES differ, only the length matches'
  --not-address '0x158593=INSTRUCTION word 0x00158593 (bv 32) of YB1h tfib_Fp1 at x_pnscan - 4 (uci x_pnscan 0x86324, cgif 0x8cf58; both images hold the word there)'
  --not-address '0x155593=INSTRUCTION word 0x00155593 (bv 32) of YB1k F_000, fetched at uci 0x63e08 / cgif 0x64fe0 (both images hold the word there)'
  --not-address '0x155793=INSTRUCTION word 0x00155793 (bv 32) of YB1k F_074, fetched at uci 0x63e7c / cgif 0x65054'
  --not-address '0x255513=INSTRUCTION word 0x00255513 (bv 32) of YB1k F_084, fetched at uci 0x63e8c / cgif 0x65064'
  --not-address '0x255793=INSTRUCTION word 0x00255793 (bv 32) of YB1k F_028, fetched at uci 0x63e30 / cgif 0x65008'
  --not-address '0x455593=INSTRUCTION word 0x00455593 (bv 32) of YB1k F_090, fetched at uci 0x63e98 / cgif 0x65070'
  --not-address '0x455793=INSTRUCTION word 0x00455793 (bv 32) of YB1k F_050, fetched at uci 0x63e58 / cgif 0x65030'
)
