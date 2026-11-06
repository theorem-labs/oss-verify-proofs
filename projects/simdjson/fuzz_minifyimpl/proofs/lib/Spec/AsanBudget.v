(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Spec Require Import STree AsanCtrl AsanCtrlProps MI_Inv LB_Inv LB_Sum SizeHist.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.AS Require Import BackingAlgebra.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Spec Require Import AsanInv.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition mth (c : Z) : Z :=
  match c with
  | 3 => 11 | 4 => 15 | 6 => 23 | 7 => 31 | 8 => 39 | 9 => 47 | 10 => 55 | 11 => 63 | 12 => 71 | 13 => 79
  | 14 => 87 | 15 => 95 | 16 => 103 | 17 => 111 | 18 => 159 | 19 => 223 | 20 => 351 | 21 => 479 | 22 => 735
  | 23 => 991 | 24 => 1471 | 25 => 1983 | 26 => 3007 | 27 => 4031 | 28 => 6015 | 29 => 8063 | 30 => 12031
  | _ => 16128
  end.

Definition pred_of_class (c : Z) (z : Z) : bool :=
  if c =? 1 then z <=? 16 else if c =? 2 then (16 <? z) && (z <=? 48) else 4 * (mth c + 1) <=? z.

(* [comment removed for export] *)
Definition class_chk (n : Z) : bool := pred_of_class (class_id (needed_size n)) n.
(* [comment removed for export] *)
Definition cs_chk (n : Z) : bool :=
  let c := class_id (needed_size n) in pred_of_class c n && (size_of_class c <=? 2 * n + 32).
Lemma cs_chk_range : forallb cs_chk (zseq 0 (Z.to_nat 64513)) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma class_chk_range : forallb class_chk (zseq 0 (Z.to_nat 64513)) = true.
Proof.
  apply forallb_forall. intros x Hx. pose proof (proj1 (forallb_forall _ _) cs_chk_range x Hx) as H.
  unfold cs_chk in H. cbv zeta in H. apply andb_true_iff in H. exact (proj1 H).
Qed.
Lemma class_chk_ok : forall n, 0 <= n <= 64512 -> pred_of_class (class_id (needed_size n)) n = true.
Proof. intros. apply (forallb_zseq class_chk 0 (Z.to_nat 64513) class_chk_range). rewrite Z2Nat.id; lia. Qed.

(* [comment removed for export] *)
Definition budget_chk (c : Z) : bool := (size_of_class c * (HB / mth c + 4) <=? 2^28) && (6 <=? mth c) && (0 <=? size_of_class c).
Lemma budget_chk_range : forallb budget_chk (zseq 3 (Z.to_nat 29)) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma budget_chk_ok : forall c, 3 <= c <= 31 -> size_of_class c * (HB / mth c + 4) <= 2^28 /\ 6 <= mth c /\ 0 <= size_of_class c.
Proof.
  intros c Hc. pose proof (forallb_zseq budget_chk 3 (Z.to_nat 29) budget_chk_range c ltac:(rewrite Z2Nat.id; lia)) as H.
  unfold budget_chk in H. apply andb_true_iff in H as [H H3]. apply andb_true_iff in H as [H1 H2].
  apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.leb_le in H3. auto.
Qed.

Section Budget.
Variable ATOP : Z.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition sizes (L : list achunk) : list Z := map chunk_size L.

Lemma cntP_le_zcount : forall c L, 1 <= c -> Forall (chunk_wf ATOP) L ->
  cntP c L <= LB_Inv.zcount (pred_of_class c) (sizes L).
Proof.
  intros c L Hc HW. induction L as [|ch L IH]; [unfold cntP, LB_Inv.zcount, LB_Inv.zlen, AsanInv.zlen; cbn; lia|].
  apply Forall_cons_iff in HW as [H1 HW]. rewrite cntP_cons. unfold sizes. cbn [map]. rewrite LB_Sum.zcount_cons. fold (sizes L).
  specialize (IH HW).
  destruct ch as [c' n|mb ms n]; cbn [is_prim_of chunk_size].
  - cbn in H1. destruct H1 as [Hn ->]. destruct (Z.eqb_spec (class_id (needed_size n)) c) as [E|NE].
    + subst c. rewrite (class_chk_ok n Hn). lia.
    + destruct (pred_of_class c n); lia.
  - destruct (pred_of_class c n); lia.
Qed.

Lemma zlen_secs_le : forall L, Forall (chunk_wf ATOP) L -> zlen (secs L) <= LB_Inv.zcount (fun z => 4 * (16127 + 1) <=? z) (sizes L).
Proof.
  intros L HW. induction L as [|ch L IH]; [unfold LB_Inv.zcount, LB_Inv.zlen, AsanInv.zlen; cbn; lia|].
  apply Forall_cons_iff in HW as [H1 HW]. rewrite secs_cons, zlen_app. unfold sizes. cbn [map]. rewrite LB_Sum.zcount_cons. fold (sizes L).
  specialize (IH HW). destruct ch as [c' n|mb ms n]; cbn [sec_of chunk_size].
  - rewrite zlen_nil. destruct (_ <=? n); lia.
  - cbn in H1. destruct H1 as (Hn & _). replace (4 * (16127 + 1) <=? n) with true by (symmetry; apply Z.leb_le; lia). rewrite zlen_cons, zlen_nil. lia.
Qed.

Lemma secbytes_le : forall L, Forall (chunk_wf ATOP) L -> secbytes L <= zsum (List.filter (fun z => 64512 <? z) (sizes L)).
Proof.
  intros L HW. induction L as [|ch L IH]; [cbn; lia|].
  apply Forall_cons_iff in HW as [H1 HW]. specialize (IH HW). unfold sizes. cbn [map List.filter]. fold (sizes L).
  destruct ch as [c' n|mb ms n]; cbn [secbytes chunk_size].
  - cbn in H1. destruct H1 as (Hn & _). replace (64512 <? n) with false by (symmetry; apply Z.ltb_ge; lia). exact IH.
  - cbn in H1. destruct H1 as (Hn & _). replace (64512 <? n) with true by (symmetry; apply Z.ltb_lt; lia). rewrite zsum_cons. lia.
Qed.

Definition live_budget_list (L : list achunk) : Prop :=
  (forall c, 1 <= c <= 31 -> size_of_class c * cntP c L <= LMAX c) /\ zlen (secs L) <= SMAX /\ secbytes L <= LSBYTES.

Lemma live_budget_list_iff : forall st, live_budget st <-> live_budget_list (live_chunks st).
Proof. intros. unfold live_budget, live_budget_list. tauto. Qed.

(* [comment removed for export] *)
Theorem live_budget_of_HISTOK : forall L, Forall (chunk_wf ATOP) L -> HISTOK (sizes L) -> live_budget_list L.
Proof.
  intros L HW HH.
  assert (HF : Forall (fun z => 0 <= z <= 2^30) (sizes L)).
  { unfold sizes. apply Forall_map. eapply Forall_impl; [|exact HW]. intros [c n|mb ms n] H; cbn in *; lia. }
  split; [|split].
  - intros c Hc. pose proof (cntP_le_zcount c L ltac:(lia) HW) as HC. unfold pred_of_class in HC.
    destruct (Z.eqb_spec c 1) as [->|N1].
    + pose proof (HISTOK_small _ HH). unfold LMAX. cbn. change (size_of_class 1) with 32. nia.
    + destruct (Z.eqb_spec c 2) as [->|N2].
      * pose proof (HISTOK_mid _ HH). unfold LMAX. cbn. change (size_of_class 2) with 64. nia.
      * destruct (budget_chk_ok c ltac:(lia)) as (B1 & B2 & B3).
        pose proof (HISTOK_large _ HH (mth c) B2).
        unfold LMAX. replace (c =? 1) with false by (symmetry; apply Z.eqb_neq; lia). replace (c =? 2) with false by (symmetry; apply Z.eqb_neq; lia).
        apply Z.le_trans with (size_of_class c * (HB / mth c + 4)); [apply Z.mul_le_mono_nonneg_l; lia| exact B1].
  - pose proof (zlen_secs_le L HW). pose proof (HISTOK_large _ HH 16127 ltac:(lia)). unfold SMAX. lia.
  - pose proof (secbytes_le L HW). pose proof (HISTOK_big_sum' _ HH HF). unfold LSBYTES. lia.
Qed.

(* [comment removed for export] *)
Definition size2n_chk (n : Z) : bool := size_of_class (class_id (needed_size n)) <=? 2 * n + 32.
Lemma size2n_range : forallb size2n_chk (zseq 0 (Z.to_nat 64513)) = true.
Proof.
  apply forallb_forall. intros x Hx. pose proof (proj1 (forallb_forall _ _) cs_chk_range x Hx) as H.
  unfold cs_chk in H. cbv zeta in H. apply andb_true_iff in H. exact (proj2 H).
Qed.
Lemma size_le_2n : forall n, 0 <= n <= 64512 -> size_of_class (class_id (needed_size n)) <= 2 * n + 32.
Proof. intros. apply Z.leb_le. apply (forallb_zseq size2n_chk 0 (Z.to_nat 64513) size2n_range). rewrite Z2Nat.id; lia. Qed.

Lemma class_chunks_bound : forall c l, 1 <= c <= 31 -> Forall (chunk_wf ATOP) l -> Forall (fun ch => 0 <= chunk_size ch) l ->
  size_of_class c * cntP c l <= 2 * zsumc l + 32 * zlen l.
Proof.
  intros c l Hc HW HP. induction l as [|ch l IH]; [unfold cntP, zlen; cbn; lia|].
  apply Forall_cons_iff in HW as [H1 HW]. apply Forall_cons_iff in HP as [H2 HP]. specialize (IH HW HP).
  rewrite cntP_cons, zlen_cons. cbn [zsumc]. destruct ch as [c' n|mb ms n]; cbn [is_prim_of chunk_size] in *.
  - destruct H1 as [Hn ->]. destruct (Z.eqb_spec (class_id (needed_size n)) c) as [E|NE].
    + subst c. pose proof (size_le_2n n Hn). nia.
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

(* [comment removed for export] *)
Lemma room_of_AINV : forall pc pb st c,
  AINV ATOP pc pb st -> 1 <= c <= 31 -> size_of_class c <= 65536 -> 0 <= size_of_class c ->
  bsum (qbatches pb st) <= 2^28 + 2^22 -> size_of_class c * cntP c pc <= 2^20 ->
  size_of_class c * (cntP c (all_chunks pc pb st) + nbatch c (qbatches pb st) + 8) + 2^20 <= K_FREEARR_OFF.
Proof.
  intros pc pb st c HA Hc Hsz Hs0 HQ Hpc.
  destruct HA as (HC & HW & HBW & _ & _ & _ & _ & _ & _ & _ & _ & _ & HLB).
  destruct HLB as (L1 & L2 & L3). specialize (L1 c Hc).
  unfold all_chunks in *. rewrite !cntP_app. apply Forall_app in HW as [HWpc HW]. apply Forall_app in HW as [HWl HWq].
  destruct (quarantine_class_bound c (qbatches pb st) Hc HBW HWq) as (Q1 & Q2 & Q3).
  assert (HN : size_of_class c * nbatch c (qbatches pb st) <= bsum (qbatches pb st)).
  { unfold nbatch. destruct (Z.eqb_spec c K_BATCH_CLASS) as [->|]; [|lia]. change (size_of_class K_BATCH_CLASS) with 8192. lia. }
  assert (HL : LMAX c <= 64 * (HB + 4)) by (unfold LMAX, HB; destruct (c =? 1); [lia|]; destruct (c =? 2); lia).
  unfold HB, K_FREEARR_OFF in *. nia.
Qed.

(* [comment removed for export] *)
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
  AINV ATOP pc pb st -> bsum (qbatches pb st) <= QB -> 0 <= QB <= 2^31 -> zlen (secs pc) <= 2 -> secbytes pc <= 2^31 ->
  64513 * zlen (CH pc pb st) <= 64513 * 1100 + QB /\ zsum2 (CH pc pb st) <= 2^33 + 2 * QB.
Proof.
  intros pc pb st QB HA HQ HQB Hpc1 Hpc2.
  destruct HA as (HC & HW & HBW & _ & _ & _ & _ & _ & _ & _ & _ & _ & (L1 & L2 & L3)).
  unfold CH, all_chunks in *. rewrite !secs_app, !zlen_app, !zsum2_app.
  apply Forall_app in HW as [HWpc HW]. apply Forall_app in HW as [HWl HWq].
  destruct (secs_bounds _ HWpc) as (P1 & P2 & P3). destruct (secs_bounds _ HWl) as (A1 & A2 & A3). destruct (secs_bounds _ HWq) as (Q1 & Q2 & Q3).
  pose proof (qchunks_secbytes _ HBW). unfold SMAX, LSBYTES, HB in *. nia.
Qed.

Lemma CH_bounds : forall pc pb st,
  AINV ATOP pc pb st -> bsum (qbatches pb st) <= 2^29 -> zlen (secs pc) <= 2 -> secbytes pc <= 2^31 ->
  zlen (CH pc pb st) <= 15000 /\ zsum2 (CH pc pb st) <= 2^34.
Proof.
  intros pc pb st HA HQ Hpc1 Hpc2. destruct (CH_bounds_gen pc pb st (2^29) HA HQ ltac:(lia) Hpc1 Hpc2) as [X Y]. split; [nia| lia].
Qed.

Lemma CH_bounds2 : forall pc pb st,
  AINV ATOP pc pb st -> bsum (qbatches pb st) <= 2^30 -> zlen (secs pc) <= 2 -> secbytes pc <= 2^31 ->
  zlen (CH pc pb st) <= 18000 /\ zsum2 (CH pc pb st) <= 2^34 + 2^32.
Proof.
  intros pc pb st HA HQ Hpc1 Hpc2. destruct (CH_bounds_gen pc pb st (2^30) HA HQ ltac:(lia) Hpc1 Hpc2) as [X Y]. split; [nia| lia].
Qed.
End Budget.

(* [comment removed for export] *)
Arguments cntP_le_zcount {ATOP} c L.
Arguments zlen_secs_le {ATOP} L.
Arguments secbytes_le {ATOP} L.
Arguments live_budget_of_HISTOK {ATOP} L.
Arguments class_chunks_bound {ATOP} c l.
Arguments quarantine_class_bound {ATOP} c bs.
Arguments room_of_AINV {ATOP} pc pb st c.
Arguments secs_bounds {ATOP} L.
Arguments CH_bounds_gen {ATOP} pc pb st QB.
Arguments CH_bounds {ATOP} pc pb st.
Arguments CH_bounds2 {ATOP} pc pb st.
