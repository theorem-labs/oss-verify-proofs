(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_decode/lib/Prog/LLVMFuzzerTestOneInput_fr.v, with its module paths and module names changed; 456 of its 574 lines of code are new or changed and 409 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_headamp/lib/Prog/Seg/Tac_slot.v, with its module paths and module names changed; 259 of its 298 lines of code are new or changed and 535 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/Prog/SegSlot.v, with its module paths and module names changed; 20 of its 38 lines of code are new or changed and 280 lines of the source are left out. *)
(* The segment statements of reac-pw/fuzz_segconf LLVMFuzzerTestOneInput (UBSan) over the cut-free invariants
   U/Prog/SlotInvCF.v: Section Stmts of U/Prog/LLVMFuzzerTestOneInput_c.v, word for word (S_E01 .. S_X01 at the cuts
   ENTRY -> K13984 -> K139e4 f -> K13aac f -> K13c34 f -> K139e4 (S f) | K13c3c -> K13e90 -> K141ec -> RET,
   seg_lemmas), with Hcut, Hat and the cut invariants read from SlotInvCF (SR := SRcf), as reac-pw/fuzz_pin's
   U/Prog/SegCF/StmtsCF.v (commit a2a7540da98) restates pin's. Statement text only. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U Require Import Contract Img0 FrameAPI.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog Require Import SlotFR SlotInv SlotInvCF.
Import ListNotations.
Open Scope Z_scope.

Section Stmts.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Variable CP : cut_preds.

Definition S_E01 : Prop :=
  Hcut B APIf ra (Inv_K13984 B APIf ra empty CP) -> Hcut B APIf ra (Inv_ENTRY B APIf ra empty).
Definition S_M01 : Prop :=
  Hat B APIf ra (Inv_K139e4 B APIf ra empty CP) 0%nat -> Hcut B APIf ra (Inv_K13984 B APIf ra empty CP).
Definition S_L01 : Prop := forall f,
  Hat B APIf ra (Inv_K13aac B APIf ra empty CP) f -> Hat B APIf ra (Inv_K139e4 B APIf ra empty CP) f.
Definition S_L02 : Prop := forall f,
  Hat B APIf ra (Inv_K13c34 B APIf ra empty CP) f -> Hat B APIf ra (Inv_K13aac B APIf ra empty CP) f.
Definition S_L03 : Prop := forall f,
  Hat B APIf ra (Inv_K139e4 B APIf ra empty CP) (S f) -> Hcut B APIf ra (Inv_K13c3c B APIf ra empty CP) ->
  Hat B APIf ra (Inv_K13c34 B APIf ra empty CP) f.
Definition S_M02 : Prop :=
  Hcut B APIf ra (Inv_K13e90 B APIf ra empty CP) -> Hcut B APIf ra (Inv_K13c3c B APIf ra empty CP).
Definition S_V01 : Prop :=
  Hcut B APIf ra (Inv_K141ec B APIf ra empty CP) -> Hcut B APIf ra (Inv_K13e90 B APIf ra empty CP).
Definition S_X01 : Prop := Hcut B APIf ra (Inv_K141ec B APIf ra empty CP).

Definition seg_lemmas : Prop :=
  S_E01 /\ S_M01 /\ S_L01 /\ S_L02 /\ S_L03 /\ S_M02 /\ S_V01 /\ S_X01.

End Stmts.
