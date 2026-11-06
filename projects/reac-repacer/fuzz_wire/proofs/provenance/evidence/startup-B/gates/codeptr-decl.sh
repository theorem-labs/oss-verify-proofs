# codeptr-decl.sh -- the values codeptr 12348302dfd2's pass 1 (logs/G2c.codeptr.pass1.log) reports as STALE that are
# NOT stale, each declared with its ROLE and its symbol / section + offset (or term) in BOTH images: fuzz_wire B pin
# af4534831a45 (names: twin .symtab) and cgif B 1c29845fe605 (stripped; names: the recovered nm). Form of the fuzz_uci B
# gate (its codeptr-decl.sh a29aa058ea48): --same only for a value that IS an address meaning the same thing in both
# images; --not-address for a length, a bound, a stored value or an instruction word. Every fact in each reason is
# re-checked on THESE two images by tools/decl_evidence_wire.py (logs/G2e.decl_evidence.log, rc 0 = every fact holds).
# Sourced by run_gates.sh (G2d). Each value is one pass 1 found on the files present.
DECL=(
  --same '0x10040=ADDRESS of the program-header table (AT_PHDR = PT_PHDR p_vaddr 0x10040 in both images): the auxv word KWord .. a_off := 32 |} 8 (ELit 65600) of the hand-off and join states (YB01/YB03), YB12 ph_addr_z, the same in both images'
  --same '0x10330=ADDRESS: the start of the unowned .rodata run [0x10330, 0x10398) (104 bytes, byte-equal in both images) between each image'"'"'s own owned cells ending at 0x10330 and starting at 0x10398 (YF0m Tfib_owned_static of each): YE3i chunk (0x10330, 0x10398), YD1k region (66352, 104), the same in both images'
  --same '0x103b8=ADDRESS of the owned 8-byte .rodata constant [0x103b8, 0x103c0) (word 0x0218a392cd3d5dbf at the same address in both images; YF0m z8 (ANum 0x103b8) in both): the end of the YE3i chunk (0x103a8, 0x103b8), the same in both images'
  --not-address '0x10101=VALUE of the 4-byte cell _ZN6__asan28asan_flags_dont_use_directlyE+0x70 (wire 0x9e068, cgif 0xa3ae8; flag bytes 01 01 01 00): YB01/YB03 KWord .. 4 (ELit 65793), YF0m Tfib_const_abs z8 rows, the same in cgif'
  --not-address '0x100000=LENGTH 1048576: the shadow-band KDisj window (0x7fff8000 + 512*EVar n, 1048576) of the 8 MiB anonymous mapping 4096*EVar n (am_len 8388608) in YB01/YB03, the same in cgif; YF0m VALUE of _ZN6__asanL8instanceE+0x328 (wire 0x9d4c0, cgif 0xa2f40)'
  --not-address '0x71c00=LENGTH 465920 = 3727360 / 8: the shadow-band KDisj window (0x7fff8000 + 512*EVar 254, 465920) of mapping 4096*EVar 254 in YB01/YB03 (am_len 3727360 in both images)'
  --not-address '0x38e000=LENGTH 3727360: am_len of the anonymous mapping 4096*EVar 254 (KDisj (4096*EVar 254, 3727360)) in YB01/YB03, the same in both images'
  --not-address '0x1ffff=BOUND KRange (EVar 3) 0 131071 / KRange (EVar 7) 0 131071 of the hand-off and join states (YB01/YB03), the same term in both images'
  --not-address '0x445c0=BOUND the decimal 280000 of KRange (EVar 4) 0 280000 in YB01/YB03, the same term in both images'
  --not-address '0x100018=VALUE 1048600 of the KWr cell at 4096*EVar 0 + 2*EVar 6 + 0x7fe00000 (then KZero) in YB01/YB03, the same term in both images'
  --not-address '0x3fffff=BOUND the tid upper bound 2^22 - 1: KRange (EVar 43) 1 4194303 (YB01/YB03), KRange (EVar TIDV) 1 4194303 (YD2i), mkAF 1 4194303 0 (YD1y), the same terms in both images'
  --not-address '0x55c000=LENGTH rw_len = page_ceil(image top) - rw_lo: wire 0x5f6000 - 0x9a000, cgif 0x5fb000 - 0x9f000 (YB12 rw_len, YB1h tfib_res_eq last window, YB13 tfib_hex3 / b_len3 5619712); the BASES differ, only the length matches'
  --not-address '0x158593=INSTRUCTION word 0x00158593 (bv 32) of YB1h tfib_Fp1 at x_pnscan - 4 (wire x_pnscan 0x87a70, cgif 0x8cf58; both images hold the word there)'
  --not-address '0x155593=INSTRUCTION word 0x00155593 (bv 32) of YB1k F_000, fetched at wire 0x64718 / cgif 0x64fe0 (both images hold the word there)'
  --not-address '0x155793=INSTRUCTION word 0x00155793 (bv 32) of YB1k F_074, fetched at wire 0x6478c / cgif 0x65054'
  --not-address '0x255513=INSTRUCTION word 0x00255513 (bv 32) of YB1k F_084, fetched at wire 0x6479c / cgif 0x65064'
  --not-address '0x255793=INSTRUCTION word 0x00255793 (bv 32) of YB1k F_028, fetched at wire 0x64740 / cgif 0x65008'
  --not-address '0x455593=INSTRUCTION word 0x00455593 (bv 32) of YB1k F_090, fetched at wire 0x647a8 / cgif 0x65070'
  --not-address '0x455793=INSTRUCTION word 0x00455793 (bv 32) of YB1k F_050, fetched at wire 0x64768 / cgif 0x65030'
)
