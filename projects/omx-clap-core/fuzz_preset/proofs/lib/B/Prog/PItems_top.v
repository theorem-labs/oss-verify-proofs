(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/B/Prog/PItems_head.v; 37 of its 70 lines of code are new or changed and 1273 lines of the source are left out. *)
(* Theorem Labs, 2026-10: the TOP of parse_items' image-B walk (lane PItemsB, owner): the kit's record text
   tparse_items_specX d CTX CTX0 DW (walk-S5b 5a205b573d4a, lib/A/PRH_FnParse.v blob 5bba1f6e0daa) from the segment steps, wired.
   Each Section hypothesis below is ONE segment lane's step lemma, in exactly the shape that lane proves it over
   lib/B/Prog/PItems_pres.v's specs; this file proves only the wiring: the strong induction on the rest's length at
   the cut PI_O_BODY (PItemsValue's re-entry after a comma is at a strictly shorter rest), then the loop head, the
   head block and the entry block. When a lane's lemma is Qed its hypothesis is discharged by an application; no
   step is assumed that a lane does not prove.
     STEP_ENTRY  PItemsEntry  pi_entry_holds   the prologue, the depth refusal, the first skip_ws call
     STEP_HEAD   PItemsHead   pi_head_holds    the empty-container path and the first closer
     STEP_LOOP   PItemsBody   pi_loop_holds    the loop head: grow and the frame cache
     STEP_BODY   PItemsBody   pi_body_holds    the object / array branch at the cut
     STEP_KEY    PItemsBody   pi_key_holds     the object key: parse_string, the colon
     FREE        PItemsBody   pi_free_holds    the missing-colon free
     STEP_VAL    PItemsValue  pi_val_holds     the kid slot, memset, parse_value, the comma, grow, the 2nd closer test
     CLOSE2      PItemsHead   pi_close2_holds  B's duplicated close-brace block
     EPI         PItemsEntry  pi_epi_holds     the epilogue
   The recursive callee parse_value (at Nat.succ d) is a premise of STEP_VAL alone, guarded by d < MAXD (the member
   loop is reached only past the depth check). pi_step_PI below has EXACTLY the shape of step_PI in the kit's walk-S5b
   lib/A/VrdUnit.v (PV / PI instantiated with pi_PV / pi_PI at fixed CTX0 DW), so the pair closes by
   vrd_unit_closed with this theorem and PValueB's step_PV.
   Rule 24: proves no function in this file (kind: segment wiring); the function is proved when every step is Qed. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YG0s YP07 YI00 YI16.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YG0p.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0d YP0c YC80 YC80x YPsym YC4aP YImgTop YC1fP YC1fPx YCbqG YCbqGcall.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YK06 YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import
PRH_Base PRH_Reader PRH_FnReader PRH_Charge PRH_FnParse PRH_FnAlloc.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import PItems_defs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.
From Stdlib Require Import Wf_nat.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import PItems_pres PItems_loop.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import VrdUnit.


Section top. Context {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {PIi : PrhImg} {RL : PrhRoomLive}.
Context {L : ptable asym} {PA : PAImg L} {PL : PAListing L}.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world pa_segs -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
Variable CTX0 : list (list Z).
(* The batch kit (240b06ed4fd4): the cursor set of the texts and of every segment spec *)
Variable CW : list (list Z).

(* the two texts at nesting d, at every float state and every entry CTX: VrdUnit's PV / PI *)
Definition pi_PV (d : nat) : Prop :=
  forall (fy : YK11.FPState) (CTX : list (list Z)), tparse_value_specX (fx := fy) B ARx SK d CTX CTX0 CW.
Definition pi_PI (d : nat) : Prop :=
  forall (fy : YK11.FPState) (CTX : list (list Z)), tparse_items_specX (fx := fy) B ARx SK d CTX CTX0 CW.

Hypothesis EPI : forall d, pi_epi_spec B ARx SK d.
Hypothesis CLOSE2 : forall d, pi_close2_spec B ARx SK d CTX0 CW.
Hypothesis FREE : forall d, pi_free_spec B ARx SK d CTX0 CW.
Hypothesis STEP_VAL : forall d, ((d < PjGrammar.MAXD)%nat -> pi_PV (Nat.succ d)) ->
  forall N, (forall N', (N' < N)%nat -> pi_body_spec B ARx SK d CTX0 CW N') ->
  pi_close2_spec B ARx SK d CTX0 CW -> pi_epi_spec B ARx SK d -> pi_val_spec B ARx SK d CTX0 CW N.
Hypothesis STEP_KEY : forall d N, pi_free_spec B ARx SK d CTX0 CW -> pi_val_spec B ARx SK d CTX0 CW N ->
  pi_key_spec B ARx SK d CTX0 CW N.
Hypothesis STEP_BODY : forall d N, pi_key_spec B ARx SK d CTX0 CW N -> pi_val_spec B ARx SK d CTX0 CW N ->
  pi_body_spec B ARx SK d CTX0 CW N.
Hypothesis STEP_LOOP : forall d, (forall N, pi_body_spec B ARx SK d CTX0 CW N) -> pi_loop_spec B ARx SK d CTX0 CW.
Hypothesis STEP_HEAD : forall d, pi_epi_spec B ARx SK d -> pi_loop_spec B ARx SK d CTX0 CW ->
  pi_head_spec B ARx SK d CTX0 CW.
Hypothesis STEP_ENTRY : forall d, pi_head_spec B ARx SK d CTX0 CW -> pi_epi_spec B ARx SK d -> pi_PI d.

(* the cut at PI_O_BODY holds at every bound N: Value's re-entry is at a strictly shorter rest *)
Lemma pi_cut_all : forall d, ((d < PjGrammar.MAXD)%nat -> pi_PV (Nat.succ d)) ->
  forall N, pi_body_spec B ARx SK d CTX0 CW N.
Proof.
intros d HPV. apply (pi_body_all B ARx SK d CTX0 CW). intros N IH.
pose proof (STEP_VAL d HPV N IH (CLOSE2 d) (EPI d)) as HV.
exact (STEP_BODY d N (STEP_KEY d N (FREE d) HV) HV).
Qed.

(* VrdUnit's step_PI: parse_items' record text at d from parse_value's at d + 1, the latter needed only below MAXD *)
Theorem pi_step_PI : forall d, ((d < PjGrammar.MAXD)%nat -> pi_PV (Nat.succ d)) -> pi_PI d.
Proof.
intros d HPV. apply STEP_ENTRY; [| exact (EPI d)]. apply STEP_HEAD; [exact (EPI d) |].
apply STEP_LOOP. exact (pi_cut_all d HPV).
Qed.

(* the pair closed, given PValueB's step_PV (parse_value at d from parse_items at d): the kit's VrdUnit.v, applied *)
Theorem pi_unit_closed : (forall d, pi_PI d -> pi_PV d) -> forall d, pi_PI d.
Proof. intros HPV. exact (vrd_parse_items_closed pi_PV pi_PI pi_step_PI HPV). Qed.

End top.
