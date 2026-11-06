(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_decode/lib/Prog/LLVMFuzzerTestOneInput_fr.v, with its module paths and module names changed; 456 of its 574 lines of code are new or changed and 409 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_headamp/lib/Prog/Seg/Tac_slot.v, with its module paths and module names changed; 259 of its 298 lines of code are new or changed and 535 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/Prog/SegSlot.v; 21 of its 38 lines of code are new or changed and 281 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/Prog/LLVMFuzzerTestOneInput_c.v, with its module paths changed; 12 of its 30 lines of code are new or changed and 20 lines of the source are left out. *)
(* The segment statements of reac-pw/fuzz_rate LLVMFuzzerTestOneInput (UBSan) over the cut-free invariants
   U/Prog/SlotInvCF.v: Section Stmts of U/Prog/LLVMFuzzerTestOneInput_c.v, word for word (S_E01, S_M01, S_M02, S_M03,
   S_X01 at the cuts ENTRY -> K13110 -> K1420c -> K14614 -> K14660 -> RET, seg_lemmas), with Hcut and the cut
   invariants read from SlotInvCF (SR := SRcf). Model: reac-pw/fuzz_role's U/Prog/SegCF/StmtsCF.v, itself reac-pw/fuzz_pin's. The three evts (rate_build_contract,
   rate_check_contract, rate_csv_contract) and the other definitions of LLVMFuzzerTestOneInput_c.v do not mention SR
   and are used from there. Statement text only. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U Require Import Contract Img0 FrameAPI.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells FP.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U.Prog Require Import SlotInvCF.
Import ListNotations.
Open Scope Z_scope.

Section Stmts.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.

Definition S_E01 : Prop :=
  Hcut B APIf ra (Inv_K13110 B APIf ra empty) -> Hcut B APIf ra (Inv_ENTRY B APIf ra empty).
Definition S_M01 : Prop :=
  Hcut B APIf ra (Inv_K1420c B APIf ra empty) -> Hcut B APIf ra (Inv_K13110 B APIf ra empty).
Definition S_M02 : Prop :=
  Hcut B APIf ra (Inv_K14614 B APIf ra empty) -> Hcut B APIf ra (Inv_K1420c B APIf ra empty).
Definition S_M03 : Prop :=
  Hcut B APIf ra (Inv_K14660 B APIf ra empty) -> Hcut B APIf ra (Inv_K14614 B APIf ra empty).
Definition S_X01 : Prop := Hcut B APIf ra (Inv_K14660 B APIf ra empty).

Definition seg_lemmas : Prop := S_E01 /\ S_M01 /\ S_M02 /\ S_M03 /\ S_X01.

End Stmts.
