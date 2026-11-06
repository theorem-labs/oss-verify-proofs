(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/boost-beast/http_request/lib/Lib/ZBridge.v; 280 of its 297 lines of code are new or changed and 392 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/Prog/LLVMFuzzerTestOneInput_seg.v, with its module paths changed; 12 of its 33 lines of code are new or changed and 276 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/U/Prog/LLVMFuzzerTestOneInput_case2_cg.v, with its module names and numbers changed; 13 of its 39 lines of code are new or changed and 7 lines of the source are left out. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U Require Import Contract Img0.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Tac Bytes ZBridge Image.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U.Spec Require Import StrFun.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U.Prog Require Import Boxreg BoxregRd BoxregStep BoxregUpd
  bcmp_c reac_boxreg_find_c lowest_free_base_c reac_boxreg_add_c reac_boxreg_add_inv range_free_c read_mac_c
  reac_boxreg_find bcmp read_mac memcpy mac_is_zero.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U.Prog Require reac_boxreg_add lowest_free_base range_taken
  range_free memset.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U.Prog Require Import
  LLVMFuzzerTestOneInput_c LLVMFuzzerTestOneInput_fr LLVMFuzzerTestOneInput_inv LLVMFuzzerTestOneInput_top
  LLVMFuzzerTestOneInput_seg LLVMFuzzerTestOneInput_c1p LLVMFuzzerTestOneInput_case2.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U Require Import SlotAgree AgreeLift.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U.Prog Require Import LLVMFuzzerTestOneInput_case1 LLVMFuzzerTestOneInput_cfb read_name_ccf LLVMFuzzerTestOneInput_top_cg LLVMFuzzerTestOneInput_seg_cg LLVMFuzzerTestOneInput_case2_cg.
Import ListNotations.
Open Scope Z_scope.

Section C1.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.

Theorem llvm_case1_ok_cf : llvm_case_ok_cf B API 1.
Proof.
  exact (llvm_case_of_evt_cf B API 1
    (u1_evt bcmp_holds (reac_boxreg_find_holds mac_is_zero_holds bcmp_holds)
       (reac_boxreg_add.reac_boxreg_add_holds mac_is_zero_holds (reac_boxreg_find_holds mac_is_zero_holds bcmp_holds)
          (lowest_free_base.lowest_free_base_holds range_taken.range_taken_holds) memset.memset_holds memcpy_holds)
       range_free.range_free_holds (read_mac_holds memcpy_holds))).
Qed.

End C1.
