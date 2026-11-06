(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec Require Import STree AsanCtrl AsanCtrlProps.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AS Require Import BackingAlgebra.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec Require Import AsanInv.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache.

Section Budget.
Variable ATOP : Z.

Definition size2n_chk (n : Z) : bool := size_of_class (class_id (needed_size n)) <=? 2 * n + 32.
Lemma size2n_range : forallb size2n_chk (zseq 0 (Z.to_nat 64513)) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma size_le_2n : forall n, 0 <= n <= 64512 -> size_of_class (class_id (needed_size n)) <= 2 * n + 32.
Proof. intros. apply Z.leb_le. apply (forallb_zseq size2n_chk 0 (Z.to_nat 64513) size2n_range). rewrite Z2Nat.id; lia. Qed.

Lemma size_le_2n_g : forall c n, 0 <= n <= 64512 -> prim_cls_ok c n -> size_of_class c <= 2 * n + 32.
Proof. intros c n Hn [->|(-> & Hr & Hm)]; [apply size_le_2n; exact Hn|]. pose proof (al16_facts n Hr Hm) as F. cbv zeta in F. tauto. Qed.

Lemma class_chunks_bound : forall c l, 1 <= c <= 31 -> Forall (chunk_wf ATOP) l -> Forall (fun ch => 0 <= chunk_size ch) l ->
  size_of_class c * cntP c l <= 2 * zsumc l + 32 * zlen l.
Proof.
  intros c l Hc HW HP. induction l as [|ch l IH]; [unfold cntP, zlen; cbn; lia|].
  apply Forall_cons_iff in HW as [H1 HW]. apply Forall_cons_iff in HP as [H2 HP]. specialize (IH HW HP).
  rewrite cntP_cons, zlen_cons. cbn [zsumc]. destruct ch as [c' n|mb ms n]; cbn [is_prim_of chunk_size] in *.
  - destruct H1 as [Hn Hc0]. destruct (Z.eqb_spec c' c) as [E|NE].
    + subst c'. pose proof (size_le_2n_g c n Hn Hc0). nia.
    + nia.
  - nia.
Qed.

Lemma zsumc_nonneg : forall l, Forall (fun ch => 0 <= chunk_size ch) l -> 0 <= zsumc l.
Proof. induction l; intros H; cbn; [lia|]. apply Forall_cons_iff in H as [H1 H]. specialize (IHl H). lia. Qed.

Lemma quarantine_class_bound : forall c bs, 1 <= c <= 31 -> Forall batch_wf bs -> Forall (chunk_wf ATOP) (qchunks bs) ->
  size_of_class c * cntP c (qchunks bs) <= 6 * bsum bs /\ 8192 * zlen bs <= bsum bs /\ 0 <= bsum bs.
Proof.
  intros c bs Hc HB HW. induction bs as [|b bs IH]; [unfold cntP, zlen; cbn; lia|].
  apply Forall_cons_iff in HB as [Hb HB]. rewrite qchunks_cons in HW. apply Forall_app in HW as [HWb HW].
  destruct (IH HB HW) as (I1 & I2 & I3). rewrite qchunks_cons, cntP_app, zlen_cons. cbn [bsum].
  destruct Hb as (B1 & B2 & B3 & B4).
  assert (HP : Forall (fun ch => 0 <= chunk_size ch) (b_chunks b)) by (eapply Forall_impl; [|exact B4]; cbv beta; intros ch Hch; lia).
  pose proof (class_chunks_bound c (b_chunks b) Hc HWb HP). pose proof (zsumc_nonneg _ HP).
  unfold Q_BATCH, Q_BATCH_BYTES in *. rewrite <- B1 in *. nia.
Qed.

Lemma room24_of_AINV : forall pc pb st,
  AINV ATOP pc pb st ->
  bsum (qbatches pb st) <= 2^28 + 2^22 -> size_of_class K_BATCH_CLASS * cntP K_BATCH_CLASS pc <= 2^20 ->
  size_of_class K_BATCH_CLASS * (cntP K_BATCH_CLASS (all_chunks pc pb st) + nbatch K_BATCH_CLASS (qbatches pb st) + 8) + 2^20 <= K_FREEARR_OFF.
Proof.
  intros pc pb st HA HQ Hpc. set (c := K_BATCH_CLASS) in *. assert (Hc : 1 <= c <= 31) by (unfold c, K_BATCH_CLASS; lia).
  destruct HA as (HC & HW & HBW & _ & _ & _ & _ & _ & _ & _ & _ & _ & HLB & _).
  destruct HLB as (L1 & L2 & L3).
  unfold all_chunks in *. rewrite !cntP_app. apply Forall_app in HW as [HWpc HW]. apply Forall_app in HW as [HWl HWq].
  destruct (quarantine_class_bound c (qbatches pb st) Hc HBW HWq) as (Q1 & Q2 & Q3).
  assert (HN : size_of_class c * nbatch c (qbatches pb st) <= bsum (qbatches pb st)).
  { unfold nbatch. unfold c at 2. rewrite Z.eqb_refl. change (size_of_class c) with 8192. lia. }
  fold c in L1. change (size_of_class c) with 8192 in *. unfold L24MAX, K_FREEARR_OFF in *. nia.
Qed.

Lemma zsum2_app : forall l1 l2, zsum2 (l1 ++ l2) = zsum2 l1 + zsum2 l2.
Proof. induction l1; intros; cbn; [lia|]. rewrite IHl1. lia. Qed.

Lemma secs_bounds : forall L, Forall (chunk_wf ATOP) L ->
  64513 * zlen (secs L) <= secbytes L /\ zsum2 (secs L) <= secbytes L + 12296 * zlen (secs L) /\ 0 <= secbytes L.
Proof.
  intros L HW. induction L as [|ch L IH]; [unfold zlen; cbn; lia|].
  apply Forall_cons_iff in HW as [H1 HW]. destruct (IH HW) as (A & B & C).
  rewrite secs_cons, zlen_app, zsum2_app. destruct ch as [c n|mb ms n]; cbn [sec_of secbytes zsum2 snd] in *.
  - unfold zlen in *. cbn in *. lia.
  - destruct H1 as (Hn & -> & _). pose proof (sec_map_size_bounds n ltac:(lia)). unfold zlen in *. cbn [length app Z.of_nat] in *. lia.
Qed.

Lemma secbytes_le_zsumc : forall L, Forall (fun ch => 0 <= chunk_size ch) L -> secbytes L <= zsumc L.
Proof.
  induction L as [|ch L IH]; intros H; [cbn; lia|]. apply Forall_cons_iff in H as [H1 H]. specialize (IH H).
  destruct ch; cbn in *; lia.
Qed.

Lemma qchunks_secbytes : forall bs, Forall batch_wf bs -> secbytes (qchunks bs) <= bsum bs.
Proof.
  induction bs as [|b bs IH]; intros HB; [cbn; lia|]. apply Forall_cons_iff in HB as [Hb HB]. specialize (IH HB).
  rewrite qchunks_cons. cbn [bsum]. destruct Hb as (B1 & B2 & B3 & B4).
  assert (HP : Forall (fun ch => 0 <= chunk_size ch) (b_chunks b)) by (eapply Forall_impl; [|exact B4]; cbv beta; intros; lia).
  pose proof (secbytes_le_zsumc _ HP).
  assert (SA : forall l1 l2, secbytes (l1 ++ l2) = secbytes l1 + secbytes l2) by (induction l1 as [|[? ?|? ? ?] l1 IH1]; intros; cbn; rewrite ?IH1; lia).
  rewrite SA. unfold Q_BATCH_BYTES in *. lia.
Qed.

Lemma CH_bounds_gen : forall pc pb st QB,
  AINV ATOP pc pb st -> bsum (qbatches pb st) <= QB -> 0 <= QB <= 2^31 -> zlen (secs pc) <= 2 -> secbytes pc <= 2^32 ->
  64513 * zlen (CH pc pb st) <= 64513 * (SMAX + 2) + QB /\ zsum2 (CH pc pb st) <= 2 * LSBYTES + 2^34 + 2 * QB.
Proof.
  intros pc pb st QB HA HQ HQB Hpc1 Hpc2.
  destruct HA as (HC & HW & HBW & _ & _ & _ & _ & _ & _ & _ & _ & _ & (L1 & L2 & L3) & _).
  unfold CH, all_chunks in *. rewrite !secs_app, !zlen_app, !zsum2_app.
  apply Forall_app in HW as [HWpc HW]. apply Forall_app in HW as [HWl HWq].
  destruct (secs_bounds _ HWpc) as (P1 & P2 & P3). destruct (secs_bounds _ HWl) as (A1 & A2 & A3). destruct (secs_bounds _ HWq) as (Q1 & Q2 & Q3).
  pose proof (qchunks_secbytes _ HBW). unfold SMAX, LSBYTES in *. nia.
Qed.

Lemma CH_bounds : forall pc pb st,
  AINV ATOP pc pb st -> bsum (qbatches pb st) <= 2^30 -> zlen (secs pc) <= 2 -> secbytes pc <= 2^32 ->
  zlen (CH pc pb st) <= SMAX + 2^15 + 2^14 /\ zsum2 (CH pc pb st) <= 2^37 - 2^33.
Proof.
  intros pc pb st HA HQ Hpc1 Hpc2. destruct (CH_bounds_gen pc pb st (2^30) HA HQ ltac:(lia) Hpc1 Hpc2) as [X Y]. unfold SMAX, LSBYTES in *. split; [nia| lia].
Qed.

Definition live_budget_list (L : list achunk) : Prop :=
  size_of_class K_BATCH_CLASS * cntP K_BATCH_CLASS L <= L24MAX /\ zlen (secs L) <= SMAX /\ secbytes L <= LSBYTES.
Lemma live_budget_list_iff : forall st, live_budget st <-> live_budget_list (live_chunks st).
Proof. intros. unfold live_budget, live_budget_list. tauto. Qed.
End Budget.

Arguments class_chunks_bound {ATOP} c l.
Arguments quarantine_class_bound {ATOP} c bs.
Arguments room24_of_AINV {ATOP} pc pb st.
Arguments secs_bounds {ATOP} L.
Arguments CH_bounds_gen {ATOP} pc pb st QB.
Arguments CH_bounds {ATOP} pc pb st.
