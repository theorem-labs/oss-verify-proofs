(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_wire/lib/U/Prog/LLVMFuzzerTestOneInput_cfb.v, with its module paths changed; 532 of its 580 lines of code are new or changed and 97 lines of the source are left out. *)
(* Modified by Theorem Labs: reac-repacer/fuzz_uci's lib/Prog/LLVMFuzzerTestOneInput_fr.v (6874bc78b1f) at fuzz_wire's
   module paths; lf_guard_img reads this image's __stack_chk_guard GOT slot 0x1cef0; lf_fr_call_x is new. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_wire/lib/Prog/LLVMFuzzerTestOneInput_fr.v, with its module paths and module names changed; 455 of its 574 lines of code are new or changed and 461 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_role/lib/U/Prog/Seg/Tac_slot.v, with its module names changed; 218 of its 245 lines of code are new or changed and 547 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_role/lib/U/Prog/Seg/M01.v, with its module paths and module names changed; 194 of its 223 lines of code are new or changed and 216 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_headamp/lib/Prog/LLVMFuzzerTestOneInput_c.v, with its module paths and module names changed; 4 of its 28 lines of code are new or changed and 199 lines of the source are left out. *)
(* The segment statements of reac-pw/fuzz_role LLVMFuzzerTestOneInput (UBSan) over the cut-free invariants
   U/Prog/SlotInvCF.v: Section Stmts of U/Prog/LLVMFuzzerTestOneInput_c.v, word for word (S_E01, S_M01, S_M02, S_X01 at
   the cuts ENTRY -> K12f48 -> K13f34 -> K141b4 -> RET, seg_lemmas), with Hcut and the cut invariants read from
   SlotInvCF (SR := SRcf). Model: reac-pw/fuzz_pin's U/Prog/SegCF/StmtsCF.v. The two evts (role_build_contract,
   role_check_contract) and the other definitions of LLVMFuzzerTestOneInput_c.v do not mention SR and are used from
   there. Statement text only. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.U Require Import Contract Img0 FrameAPI.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells FP.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.U.Prog Require Import SlotInvCF.
Import ListNotations.
Open Scope Z_scope.

Section Stmts.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.

Definition S_E01 : Prop :=
  Hcut B APIf ra (Inv_K12f48 B APIf ra empty) -> Hcut B APIf ra (Inv_ENTRY B APIf ra empty).
Definition S_M01 : Prop :=
  Hcut B APIf ra (Inv_K13f34 B APIf ra empty) -> Hcut B APIf ra (Inv_K12f48 B APIf ra empty).
Definition S_M02 : Prop :=
  Hcut B APIf ra (Inv_K141b4 B APIf ra empty) -> Hcut B APIf ra (Inv_K13f34 B APIf ra empty).
Definition S_X01 : Prop := Hcut B APIf ra (Inv_K141b4 B APIf ra empty).

Definition seg_lemmas : Prop := S_E01 /\ S_M01 /\ S_M02 /\ S_X01.

End Stmts.
