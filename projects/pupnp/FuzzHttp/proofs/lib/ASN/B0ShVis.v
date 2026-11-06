(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.ASN Require Import
  PropExec AsanAcct BackingAlgebra AxSymExec3 AsanPlanCore AsanPlan AsanPlanSound MainExport MainFactsBoth B0Img MainEntryBoth.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import PropExec MState Mem Cells Step Frame.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Nodes.
Import ListNotations.
Open Scope Z_scope.

Lemma fact_at : forall V (m : word -> option byte) k f,
  Forall (mfact_ok bsegs V m) both_mem_facts -> nth_error both_mem_facts k = Some f -> mfact_ok bsegs V m f.
Proof. intros V m k f HF HN. exact (proj1 (Forall_forall _ _) HF f (nth_error_In _ _ HN)). Qed.

Lemma wr_present : forall (m : word -> option byte) A n a, wr_at bsegs m A n -> A <= a < A + n -> 0x609000 <= a -> a < 2^64 -> m (wa a) <> None.
Proof.
  intros m A n a (W0 & W1 & WV) Ha HI H64. specialize (WV (a - A) ltac:(lia)). replace (A + (a - A)) with a in WV by lia.
  unfold wview in WV. destruct (m (wa a)); [discriminate|].
  rewrite wa_unsigned in WV by lia. rewrite (ref_find_segment_none a 1 ltac:(lia) ltac:(right; exact HI)) in WV. exact WV.
Qed.

Lemma vis_sh_eq : forall v n, n mod 8 = 0 -> ASHOFF + (4096 * v) / 8 = 512 * v + 2147450880 /\ ASHOFF + (4096 * v + n) / 8 = 512 * v + 2147450880 + n / 8.
Proof. intros v n Hn. unfold ASHOFF. split; Z.div_mod_to_equations; lia. Qed.

Lemma ashadow_vis_dec : forall V a, bshadow_vis V a \/ ~ bshadow_vis V a.
Proof.
  intros V a. unfold bshadow_vis.
  assert (D : forall l : list (zexp * zexp),
             (exists bn, In bn l /\ ASHOFF + zv V (fst bn) / 8 <= a < ASHOFF + (zv V (fst bn) + zv V (snd bn)) / 8)
             \/ ~ (exists bn, In bn l /\ ASHOFF + zv V (fst bn) / 8 <= a < ASHOFF + (zv V (fst bn) + zv V (snd bn)) / 8)).
  { induction l as [|bn l IH]; [right; intros (bn & [] & _)|].
    destruct (Z_le_dec (ASHOFF + zv V (fst bn) / 8) a) as [L1|L1]; [destruct (Z_lt_dec a (ASHOFF + (zv V (fst bn) + zv V (snd bn)) / 8)) as [L2|L2]|].
    - left. exists bn. split; [left; reflexivity| lia].
    - destruct IH as [(bn' & I' & B')|N]; [left; exists bn'; split; [right; exact I'| exact B']|].
      right. intros (bn' & [<-|I'] & B'); [lia| apply N; exists bn'; split; assumption].
    - destruct IH as [(bn' & I' & B')|N]; [left; exists bn'; split; [right; exact I'| exact B']|].
      right. intros (bn' & [<-|I'] & B'); [lia| apply N; exists bn'; split; assumption]. }
  apply D.
Qed.

Ltac fact_k HF k H :=
  let o := eval vm_compute in (nth_error both_mem_facts k) in
  lazymatch o with
  | Some ?f => let N := fresh "N" in
               assert (N : nth_error both_mem_facts k = Some f) by (vm_cast_no_check (@eq_refl (option mfact) (Some f)));
               pose proof (fact_at _ _ k f HF N) as H; clear N
  end.

Theorem ashadow_present : forall V (m : word -> option byte),
  Forall (mfact_ok bsegs V m) both_mem_facts -> bshadow0 V m ->
  forall a, bshadow a -> m (wa a) <> None.
Proof.
  intros V m HF SH0 a HA.
  destruct (ashadow_vis_dec V a) as [VIS|NV]; [| rewrite (SH0 a HA NV); discriminate].
  assert (AB : 0x609000 <= a /\ a < 2^64) by (unfold bshadow in HA; lia).
  destruct VIS as (bn & HIN & HB). unfold both_vis_app in HIN. cbn [In] in HIN.

  fact_k HF 1042%nat F1.  fact_k HF 1126%nat F2.  fact_k HF 1119%nat F3.  fact_k HF 1115%nat F4.  fact_k HF 1108%nat F5.
  fact_k HF 1102%nat F6.  fact_k HF 1095%nat F7.  fact_k HF 1089%nat F8.  fact_k HF 1064%nat F9.  fact_k HF 1048%nat F10.
  fact_k HF 1045%nat F11. fact_k HF 778%nat F12.  fact_k HF 371%nat F13.  fact_k HF 602%nat F14.
  cbn [mfact_ok zv] in F1, F2, F3, F4, F5, F6, F7, F8, F9, F10, F11, F12, F13, F14.
  repeat (destruct HIN as [<-|HIN]); [..| destruct HIN]; cbn [fst snd zv] in HB; unfold ASHOFF in HB.
  all: match goal with
       | W : wr_at bsegs ?mm ?A ?n |- _ =>
           first [ apply (wr_present mm A n a W); [clear - HB; Z.div_mod_to_equations; lia| lia| lia] ]
       end.
Qed.

Corollary ashadow_present_r : forall V (m : word -> option byte) (H : word -> bool),
  Forall (mfact_ok bsegs V m) both_mem_facts -> bshadow0 V m ->
  forall x : word, bshadow (bv_unsigned x) -> H x = false -> mrestrict H m x <> None.
Proof.
  intros V m H HF SH0 x HA HX. unfold mrestrict. rewrite HX.
  pose proof (ashadow_present V m HF SH0 (bv_unsigned x) HA) as P. rewrite Nodes.wa_unsigned_id in P. exact P.
Qed.
