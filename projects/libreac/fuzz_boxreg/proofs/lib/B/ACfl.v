(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: made for libreac/fuzz_boxreg's ASan+UBSan build from the module of the same name
   in proofs/cgif/cgif_file_fuzzer/lib/A/ACfl.v (origin/ossv/recipes c8557374ad2), the twin of this tree's
   lib/A/ACfl.v: cgif's names, boxreg's ASan+UBSan values. *)
(* boxreg content behind cgif's module name; source lib/B/Prog/BoxBLibX.v.
   cgif's ACfl.v holds the constants of the entry function's call (A_LLVMF, RA_LLVMF, A_EMPTY, EV_LIB, LIVE_LIB,
   LLVMF_STK; the same values as its lib/A/ACfn.v) and tfib_lib_contract, an older form of LLVMFuzzerTestOneInput's
   contract that no file of cgif's tree uses. The relocated core (lib/B/<A names>, e.g. lib/B/AD2f.v) reads five of
   the constants, through lib/B/AD2f.v's `Require Export ACeg ACfl` (cgif line numbers):
   - A_LLVMF: AD2f.v:81,90,165,184; AD1r.v:97,291,303,623,624; AD1w.v:105; AD2d.v:219; AD2e.v:46,97.
   - RA_LLVMF: AD2f.v:82,91,154; AD1r.v:24,88,98,110,297,303,333,334,601,612; AD1w.v:73,95.
   - LLVMF_STK: AD1r.v:226,249,293,321,631; AD1w.v:77,96.
   - EV_LIB: AD1r.v:582,644,727,729,821,868,949,1001,1025; AD1w.v:86,96,225; AD2d.v:314; AD2e.v:645.
   - LIVE_LIB: AD1r.v:645; AD1w.v:86.
   This file states exactly these five. Each is an abbreviation of lib/B/Prog/BoxBLibX.v's constant (the B names carry
   the B forms of lib/B/Prog: A_ -> AB_, RA_ -> RAB_, a B suffix on the bounds), so `unfold` in the core reaches
   BoxBLibX's value, and lib/B/ACfn.v's LLVMF_STK is the same constant:
   - A_LLVMF = AB_LLVMF = boxb_text + AF_LLVMFuzzerTestOneInput = 0x7ffac + 0x0 = 0x7ffac (BoxBAddr.v:12,
     BoxBList.v:11): the address of LLVMFuzzerTestOneInput in the .symtab of the ORIGINAL unstripped image
     the release's unstripped fuzz_boxreg.asan-ubsan (sha256
     1d548458eac37ae17f9e8dfb06a5dfef3c606ec9e03eca8ef291d5fec9dce495), measured with pyelftools 0.33 + capstone 5.0.7
     (STT_FUNC, 4232 bytes).
   - RA_LLVMF = RAB_LLVMF = 0x7fea8 (BoxBLibX.v:73): the driver's only call of the function is target_run's (0x7fddc,
     344 bytes) `jal 0x108` at 0x7fea4, whose target is 0x7fea4 + 0x108 = 0x7ffac; 0x7fea8 = 0x7fea4 + 4 is the
     instruction after it (`mv s3, a0`). No other instruction of the image jumps to 0x7ffac.
   - LLVMF_STK = LLVMF_STKB = 32768, EV_LIB = EV_LIBB = 2000, LIVE_LIB = LIVE_LIBB = 2 ^ 33: BoxBLibX.v's bounds
     (justified there, BoxBLibX.v:15-26).
   A_EMPTY (BoxBLibX.v:74 AB_EMPTY = 0x5d3a20) and tfib_lib_contract have no reader in the core and are not stated.
   No value is defined here. *)
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require YZ00.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require BoxBLibX.

Abbreviation A_LLVMF := OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog.BoxBLibX.AB_LLVMF.
Abbreviation RA_LLVMF := OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog.BoxBLibX.RAB_LLVMF.
Abbreviation EV_LIB := OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog.BoxBLibX.EV_LIBB.
Abbreviation LIVE_LIB := OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog.BoxBLibX.LIVE_LIBB.
Abbreviation LLVMF_STK := OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog.BoxBLibX.LLVMF_STKB.
