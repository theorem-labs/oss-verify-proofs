(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Instr Sem.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import PropExec AxSymExec3 AxSymExec3Sound AsanPlanCore AsanPlan AsanPlanSound. From OSSVerify.Proofs.simdjson.fuzz_utf8.lib Require Import SlotProp MallocNodes2 MinifyGhost Stage1Model Stage2Ghost Stage1Ghost.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)
Import ListNotations. Import AX2. Import AX2S. Import APC. Import AP.
Open Scope Z_scope.

Module PGA.
Section S.
Context {fx : FPState}.
Variable SEGS : list Segment.
Variable GV : list vc.                 (* [comment removed for export] *)

Definition loops_id (id : nat) : bool := negb (Nat.eqb id MN2.SLOT_ID || Nat.eqb id MG.QS_ID)%bool.

Definition fp (id : nat) (args : list expr) : list (expr * expr) :=
  if Nat.eqb id MN2.SLOT_ID then MN2.slot_fp args
  else if Nat.eqb id MG.QS_ID then MG.fp_qs args
  else S1G.fp1 id args.
Definition vcok (v : vc) : bool := MG.qs_vcokM v || AP.vc_list GV v.
Definition Gparse : gparams := GPAR fp vcok.

Definition GPall (id : nat) (vs : list Z) (M : word -> option byte) : Prop :=
  if Nat.eqb id MN2.SLOT_ID then slot_sem SEGS vs M
  else if Nat.eqb id MG.QS_ID then MG.p_qs SEGS vs M
  else S1G.GP1 SEGS id vs M.

Lemma GPall_slot : forall vs M, GPall MN2.SLOT_ID vs M <-> slot_sem SEGS vs M.
Proof. intros. unfold GPall. rewrite Nat.eqb_refl. tauto. Qed.
Lemma GPall_qs : forall vs M, GPall MG.QS_ID vs M <-> MG.p_qs SEGS vs M.
Proof. intros. unfold GPall. cbn [Nat.eqb MG.QS_ID MN2.SLOT_ID]. tauto. Qed.
Lemma GPall_loops : forall id vs M, loops_id id = true -> GPall id vs M = S1G.GP1 SEGS id vs M.
Proof.
  intros id vs M H. unfold loops_id in H. unfold GPall.
  destruct (Nat.eqb id MN2.SLOT_ID); [discriminate|]. destruct (Nat.eqb id MG.QS_ID); [discriminate|]. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma GPall_frame : forall id args E M M',
  (forall a, APS.in_fp E (g_fp Gparse id args) a = true -> M' a = M a) ->
  GPall id (map (APS.uE E) args) M -> GPall id (map (APS.uE E) args) M'.
Proof.
  intros id args E M M' Hfp H. unfold GPall in *. unfold Gparse in Hfp. cbn [g_fp] in Hfp. unfold fp in Hfp.
  destruct (Nat.eqb_spec id MN2.SLOT_ID) as [->|Hne].
  - apply (SlotProp.GPm_frame SEGS MN2.SLOT_ID args E M M'); unfold SlotProp.GPm; rewrite ?Nat.eqb_refl; [|exact H].
    unfold MN2.Gm. cbn [g_fp]. rewrite Nat.eqb_refl. exact Hfp.
  - destruct (Nat.eqb_spec id MG.QS_ID) as [->|Hne2].
    + change (map (APS.uE E) args) with (map (MG.uD E) args) in H |- *. exact (MG.p_qs_frame SEGS args E M M' Hfp H).
    + exact (S1G.GP1_frame SEGS id args E M M' Hfp H).
Qed.

(* [comment removed for export] *)
Definition vc_loops (c : vc) : bool :=
  forallb (fun g => loops_id (g_id g)) (vc_hyps c) && match vc_concl c with VCAtom g => loops_id (g_id g) | VCFact _ => true end.
Lemma vc_loops_transfer : forall c, vc_loops c = true -> APS.vc_holds SEGS (S1G.GP1 SEGS) c -> APS.vc_holds SEGS GPall c.
Proof.
  intros c H HV. unfold vc_loops in H. apply andb_prop in H as [Hh Hc]. unfold APS.vc_holds in *. intros E M Hk Hhyps.
  assert (H1 : Forall (APS.gholds (S1G.GP1 SEGS) E M) (vc_hyps c)).
  { apply Forall_forall. intros g Hg. pose proof (proj1 (Forall_forall _ _) Hhyps g Hg) as X.
    unfold APS.gholds in *. rewrite <- (GPall_loops (g_id g)); [exact X|]. exact (proj1 (forallb_forall _ _) Hh g Hg). }
  pose proof (HV E M Hk H1) as R. destruct (vc_concl c) as [g|K]; [|exact R].
  unfold APS.gholds in *. rewrite GPall_loops; [exact R | exact Hc].
Qed.
Theorem gp1_vcs_transfer : forall L, forallb vc_loops L = true -> Forall (APS.vc_holds SEGS (S1G.GP1 SEGS)) L ->
  Forall (APS.vc_holds SEGS GPall) L.
Proof.
  intros L H HL. apply Forall_forall. intros c Hc.
  apply vc_loops_transfer; [exact (proj1 (forallb_forall _ _) H c Hc) | exact (proj1 (Forall_forall _ _) HL c Hc)].
Qed.

(* [comment removed for export] *)
Hypothesis GV_ok : Forall (APS.vc_holds SEGS GPall) GV.
Lemma Gparse_ok : forall v, g_vcok Gparse v = true -> APS.vc_holds SEGS GPall v.
Proof.
  intros v H. cbn [g_vcok Gparse] in H. unfold vcok in H. apply Bool.orb_prop in H as [H|H].
  - rewrite MG.qs_vcokM_eq in H. exact (MG.qs_vcok_sound SEGS GPall GPall_qs v H).
  - exact (APS.vc_list_ok SEGS GPall GV GV_ok v H).
Qed.
End S.
End PGA.
