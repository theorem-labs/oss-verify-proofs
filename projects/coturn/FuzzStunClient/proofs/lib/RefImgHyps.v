(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From OSSVerify.coturn.FuzzStunClient.images Require Import Plain.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import PropExec StoreOk RefNodes.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import SymExec3 SymPlan SymPlanSoundA SymPlanSound.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFast.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFastK.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFastM.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import SumWalkFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.WalkTac.gres ::= gres_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.WalkTac.vnorm ::= vnorm_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.StepTac.step_simpl ::= step_simpl_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.RefMemcpyLib.not_kept ::= not_kept_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.StoreOk.store_ok_peel ::= store_ok_peel_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.SumWalkTac.rdn_peel1 ::= rdn_peel1_fast.
(* [comment removed for export] *)
Import ListNotations.
Import SX2. Import SP. Import SPS.
Open Scope Z_scope.

#[local] Abbreviation RSEGS := Plain.M.loaded_segments.

Lemma reserved_val : segments_reserved RSEGS =
  [(Z_to_bv 64 0x10000, Z_to_bv 64 0x3000); (Z_to_bv 64 0x13000, Z_to_bv 64 0x12000);
   (Z_to_bv 64 0x25000, Z_to_bv 64 0x1000); (Z_to_bv 64 0x26000, Z_to_bv 64 0x32000)].
Proof. vm_compute. reflexivity. Qed.

Lemma u64_lit' : forall z, (0 <= z < 2 ^ 64)%Z -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros z Hz. apply Z_to_bv_small. unfold bv_modulus. lia. Qed.

Lemma H_hull_ref : forall (a : word) (n : Z), (0 < n < 2 ^ 64)%Z ->
  region_free (segments_reserved RSEGS) a (Z_to_bv 64 n) = true ->
  (bv_unsigned a + n <= IMG_LO \/ IMG_HI <= bv_unsigned a)%Z.
Proof.
  intros a n Hn Hr. rewrite reserved_val in Hr. unfold IMG_LO, IMG_HI.
  pose proof (fun b s Hin => region_free_In _ a (Z_to_bv 64 n) b s Hr Hin) as X.
  pose proof (X _ _ (or_introl eq_refl)) as X1.
  pose proof (X _ _ (or_intror (or_introl eq_refl))) as X2.
  pose proof (X _ _ (or_intror (or_intror (or_introl eq_refl)))) as X3.
  pose proof (X _ _ (or_intror (or_intror (or_intror (or_introl eq_refl))))) as X4.
  rewrite !u64_lit' in X1, X2, X3, X4 by lia. pose proof (u64_range a). lia.
Qed.

Lemma H_res_small_ref : Forall (fun p => (bv_unsigned (snd p) <= 2 ^ 30)%Z) (segments_reserved RSEGS).
Proof. rewrite reserved_val. repeat apply Forall_cons; try apply Forall_nil; cbn [snd]; rewrite u64_lit' by lia; lia. Qed.

Lemma H_res_len_ref : res_len_okP RSEGS.
Proof. unfold res_len_okP. rewrite reserved_val. cbn. lia. Qed.

Lemma H_wview_off_ref : forall M (x : word),
  (bv_unsigned x + 1 <= IMG_LO \/ IMG_HI <= bv_unsigned x)%Z -> M x = None -> wview RSEGS M x = None.
Proof.
  intros M x Hx HM. unfold IMG_LO, IMG_HI in Hx. unfold wview. rewrite HM. pose proof (u64_range x) as Hr.
  cbn -[Z.leb Z.add Z.of_N bv_unsigned andb].
  change (Z.of_N 0x10000%N) with 0x10000%Z. change (Z.of_N 0x13000%N) with 0x13000%Z.
  change (Z.of_N 0x25000%N) with 0x25000%Z. change (Z.of_N 0x26000%N) with 0x26000%Z.
  change (Z.of_N 0x3000%N) with 0x3000%Z. change (Z.of_N 0x12000%N) with 0x12000%Z.
  change (Z.of_N 0x1000%N) with 0x1000%Z. change (Z.of_N 0x32000%N) with 0x32000%Z.
  repeat (match goal with |- context [Z.leb ?a ?b] => destruct (Z.leb_spec a b); cbn [andb] end); try reflexivity; exfalso; lia.
Qed.
