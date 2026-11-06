(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: made for libreac/fuzz_boxreg's ASan build from the module of the same name in
   proofs/cgif/cgif_file_fuzzer/lib/A/ACfl.v (origin/ossv/recipes c8557374ad2): its names, boxreg's values. *)
(* boxreg content behind cgif's module name; source BoxLibX.v / BoxShape.v.
   cgif's ACfl.v holds the constants of the entry function's call (A_LLVMF, RA_LLVMF, A_EMPTY, EV_LIB, LIVE_LIB,
   LLVMF_STK; the same values as its lib/A/ACfn.v) and tfib_lib_contract, an older form of LLVMFuzzerTestOneInput's
   contract that no file of cgif's tree uses. The relocated core reads five of the constants, through lib/A/AD2f.v's
   `Require Export ACeg ACfl` (cgif line numbers):
   - A_LLVMF: AD2f.v:81,90,165,184; AD1r.v:97,291,303,623,624; AD1w.v:105; AD2d.v:219; AD2e.v:46,97.
   - RA_LLVMF: AD2f.v:82,91,154; AD1r.v:24,88,98,110,297,303,333,334,601,612; AD1w.v:73,95.
   - LLVMF_STK: AD1r.v:226,249,293,321,631; AD1w.v:77,96.
   - EV_LIB: AD1r.v:582,644,727,729,821,868,949,1001,1025; AD1w.v:86,96,225; AD2d.v:314; AD2e.v:645.
   - LIVE_LIB: AD1r.v:645; AD1w.v:86.
   This file states exactly these five. Each is an abbreviation of lib/A/Prog/BoxLibX.v's constant, so `unfold` in the
   core reaches BoxLibX's value, and lib/A/ACfn.v's LLVMF_STK is the same constant:
   - A_LLVMF = box_text + AF_LLVMFuzzerTestOneInput = 0x7ff4c, RA_LLVMF = 0x7fe48 (the instruction after target_run's
     `jal` at 0x7fe44), both measured in BoxLibX.v on fuzz_boxreg.asan.
   - LLVMF_STK = 32768, EV_LIB = 2000, LIVE_LIB = 2 ^ 33: BoxLibX.v's bounds (justified there).
   A_EMPTY and tfib_lib_contract have no reader in the core and are not stated. No value is defined here. *)
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require YZ00.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require BoxLibX.

Abbreviation A_LLVMF := OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog.BoxLibX.A_LLVMF.
Abbreviation RA_LLVMF := OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog.BoxLibX.RA_LLVMF.
Abbreviation EV_LIB := OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog.BoxLibX.EV_LIB.
Abbreviation LIVE_LIB := OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog.BoxLibX.LIVE_LIB.
Abbreviation LLVMF_STK := OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog.BoxLibX.LLVMF_STK.
