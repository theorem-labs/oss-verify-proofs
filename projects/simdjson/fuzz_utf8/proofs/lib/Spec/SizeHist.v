(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Spec Require Import MI_Inv LB_Inv LB_Sum.
Import ListNotations.
Open Scope Z_scope.

Definition itemsz (z : Z) : Prop := z = 24 \/ exists l, 0 <= l /\ z = 4 * (l + 1).
Definition YWs (L : list Z) : Prop := Forall itemsz L.
Definition bcs (z : Z) : Z := if z =? 24 then 1 else z / 4 - 1.
Definition BCs (L : list Z) : Z := zsum (map bcs L).
Definition N24s (L : list Z) : Z := zcount (fun z => z =? 24) L.
Definition N4s (L : list Z) : Z := zcount (fun z => z =? 4) L.

(* [comment removed for export] *)
Definition HB : Z := 2^24 + 2.

Definition HISTOK (M : list Z) : Prop :=
  exists I Z, Permutation M (I ++ Z) /\ YWs I /\ BCs I <= HB /\ N4s I <= 2 * N24s I + 2 /\ (length Z <= 4)%nat.

Lemma BCs_cons z L : BCs (z :: L) = bcs z + BCs L. Proof. reflexivity. Qed.
Lemma BCs_app L1 L2 : BCs (L1 ++ L2) = BCs L1 + BCs L2. Proof. unfold BCs. rewrite map_app, zsum_app. reflexivity. Qed.
Lemma N24s_cons z L : N24s (z :: L) = (if z =? 24 then 1 else 0) + N24s L. Proof. unfold N24s. rewrite zcount_cons. reflexivity. Qed.
Lemma N4s_cons z L : N4s (z :: L) = (if z =? 4 then 1 else 0) + N4s L. Proof. unfold N4s. rewrite zcount_cons. reflexivity. Qed.
Lemma N24s_app L1 L2 : N24s (L1 ++ L2) = N24s L1 + N24s L2. Proof. unfold N24s. apply zcount_app. Qed.
Lemma N4s_app L1 L2 : N4s (L1 ++ L2) = N4s L1 + N4s L2. Proof. unfold N4s. apply zcount_app. Qed.
Lemma N24s_nonneg L : 0 <= N24s L. Proof. unfold N24s. apply zcount_nonneg. Qed.
Lemma N4s_nonneg L : 0 <= N4s L. Proof. unfold N4s. apply zcount_nonneg. Qed.
Lemma bcs_kv l : 0 <= l -> bcs (4 * (l + 1)) = (if l =? 5 then 1 else l).
Proof. intros Hl. unfold bcs. destruct (Z.eqb_spec (4 * (l + 1)) 24); destruct (Z.eqb_spec l 5); lia. Qed.
Lemma bcs_24 : bcs 24 = 1. Proof. reflexivity. Qed.
Lemma bcs_nonneg z : itemsz z -> 0 <= bcs z.
Proof. intros [->|(l & Hl & ->)]; [rewrite bcs_24; lia| rewrite bcs_kv by lia; destruct (l =? 5); lia]. Qed.
Lemma BCs_nonneg L : YWs L -> 0 <= BCs L.
Proof. induction L as [|z L IH]; intros HW; [cbn; unfold BCs, zsum; cbn; lia|]. apply Forall_cons_iff in HW as [Hz HW]. rewrite BCs_cons. pose proof (bcs_nonneg z Hz). specialize (IH HW). lia. Qed.
Lemma YWs_app L1 L2 : YWs (L1 ++ L2) <-> YWs L1 /\ YWs L2. Proof. unfold YWs. apply Forall_app. Qed.
Lemma YWs_perm L1 L2 : Permutation L1 L2 -> YWs L1 -> YWs L2.
Proof. intros HP HW. unfold YWs in *. rewrite Forall_forall in *. intros z Hz. apply HW. eapply Permutation_in; [apply Permutation_sym; exact HP| exact Hz]. Qed.
Lemma BCs_perm L1 L2 : Permutation L1 L2 -> BCs L1 = BCs L2. Proof. intros HP. unfold BCs. apply zsum_map_perm. exact HP. Qed.
Lemma N24s_perm L1 L2 : Permutation L1 L2 -> N24s L1 = N24s L2. Proof. intros HP. unfold N24s. apply zcount_perm. exact HP. Qed.
Lemma N4s_perm L1 L2 : Permutation L1 L2 -> N4s L1 = N4s L2. Proof. intros HP. unfold N4s. apply zcount_perm. exact HP. Qed.

(* [comment removed for export] *)
Lemma HISTOK_intro I Z M : Permutation M (I ++ Z) -> YWs I -> BCs I <= HB -> N4s I <= 2 * N24s I + 2 -> (length Z <= 4)%nat -> HISTOK M.
Proof. intros. exists I, Z. repeat split; assumption. Qed.

(* [comment removed for export] *)
Lemma HISTOK_amb n I Z : YWs I -> BCs I <= HB -> N4s I <= 2 * N24s I + 2 -> (length Z <= 3)%nat -> HISTOK (n :: I ++ Z).
Proof.
  intros HW HB0 H42 HL. apply (HISTOK_intro I (n :: Z)); auto; [| cbn; lia].
  apply Permutation_middle.
Qed.

(* [comment removed for export] *)
Lemma HISTOK_item n I Z : YWs (n :: I) -> BCs (n :: I) <= HB -> N4s (n :: I) <= 2 * N24s (n :: I) + 2 -> (length Z <= 3)%nat -> HISTOK (n :: I ++ Z).
Proof. intros HW HB0 H42 HL. apply (HISTOK_intro (n :: I) Z); auto. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma zcount_items_lin (f : Z -> bool) (a b c : Z) I : YWs I ->
  (forall z, itemsz z -> (if f z then 1 else 0) <= a * (if z =? 4 then 1 else 0) + b * bcs z + c * (if z =? 24 then 1 else 0)) ->
  zcount f I <= a * N4s I + b * BCs I + c * N24s I.
Proof.
  induction I as [|z I IH]; intros HW Hf.
  - unfold N4s, N24s, BCs, zsum. rewrite !zcount_nil. cbn. lia.
  - apply Forall_cons_iff in HW as [Hz HW]. rewrite zcount_cons, N4s_cons, BCs_cons, N24s_cons.
    specialize (IH HW Hf). specialize (Hf z Hz). lia.
Qed.

Lemma zlen_le_4 {A} (Z : list A) : (length Z <= 4)%nat -> zlen Z <= 4.
Proof. unfold zlen. lia. Qed.

(* [comment removed for export] *)
Lemma HISTOK_small M : HISTOK M -> zcount (fun z => z <=? 16) M <= 2 * HB + 6.
Proof.
  intros (I & Z & HP & HW & HBC & H42 & HL). rewrite (zcount_perm _ _ _ HP), zcount_app.
  pose proof (zcount_le_len (fun z => z <=? 16) Z). pose proof (zlen_le_4 Z HL).
  pose proof (zcount_items_lin (fun z => z <=? 16) 1 1 (-1) I HW) as HI.
  assert (N24 : N24s I <= BCs I).
  { pose proof (zcount_items_lin (fun z => z =? 24) 0 1 0 I HW) as H24. unfold N24s at 1.
    enough (E : forall z, itemsz z -> (if z =? 24 then 1 else 0) <= 0 * (if z =? 4 then 1 else 0) + 1 * bcs z + 0 * (if z =? 24 then 1 else 0)) by (specialize (H24 E); lia).
    intros z [->|(l & Hl & ->)]; [rewrite bcs_24; cbn; lia|]. rewrite bcs_kv by lia.
    destruct (Z.eqb_spec (4 * (l + 1)) 24); destruct (Z.eqb_spec l 5); lia. }
  enough (E : forall z, itemsz z -> (if z <=? 16 then 1 else 0) <= 1 * (if z =? 4 then 1 else 0) + 1 * bcs z + (-1) * (if z =? 24 then 1 else 0)) by (specialize (HI E); lia).
  intros z [->|(l & Hl & ->)]; [rewrite bcs_24; cbn; lia|]. rewrite bcs_kv by lia.
  destruct (Z.leb_spec (4 * (l + 1)) 16); destruct (Z.eqb_spec (4 * (l + 1)) 4); destruct (Z.eqb_spec (4 * (l + 1)) 24); destruct (Z.eqb_spec l 5); lia.
Qed.

(* [comment removed for export] *)
Lemma HISTOK_mid M : HISTOK M -> zcount (fun z => (16 <? z) && (z <=? 48)) M <= HB + 4.
Proof.
  intros (I & Z & HP & HW & HBC & H42 & HL). rewrite (zcount_perm _ _ _ HP), zcount_app.
  pose proof (zcount_le_len (fun z => (16 <? z) && (z <=? 48)) Z). pose proof (zlen_le_4 Z HL).
  pose proof (zcount_items_lin (fun z => (16 <? z) && (z <=? 48)) 0 1 0 I HW) as HI.
  enough (E : forall z, itemsz z -> (if (16 <? z) && (z <=? 48) then 1 else 0) <= 0 * (if z =? 4 then 1 else 0) + 1 * bcs z + 0 * (if z =? 24 then 1 else 0)) by (specialize (HI E); lia).
  intros z [->|(l & Hl & ->)]; [rewrite bcs_24; cbn; lia|]. rewrite bcs_kv by lia.
  destruct (Z.ltb_spec 16 (4 * (l + 1))); destruct (Z.leb_spec (4 * (l + 1)) 48); destruct (Z.eqb_spec l 5); cbn [andb]; lia.
Qed.

(* [comment removed for export] *)
Lemma HISTOK_large M : HISTOK M -> forall m, 6 <= m -> zcount (fun z => 4 * (m + 1) <=? z) M <= HB / m + 4.
Proof.
  intros (I & Z & HP & HW & HBC & H42 & HL) m Hm. rewrite (zcount_perm _ _ _ HP), zcount_app.
  pose proof (zcount_le_len (fun z => 4 * (m + 1) <=? z) Z). pose proof (zlen_le_4 Z HL).
  enough (HI : zcount (fun z => 4 * (m + 1) <=? z) I <= HB / m) by lia.
  apply Z.div_le_lower_bound; [lia|].
  pose proof (zcount_items_lin (fun z => 4 * (m + 1) <=? z) 0 1 0 I HW) as HI.
  enough (E : forall I', YWs I' -> m * zcount (fun z => 4 * (m + 1) <=? z) I' <= BCs I').
  { specialize (E I HW). lia. }
  clear - Hm. induction I' as [|z I' IH]; intros HW'.
  - rewrite zcount_nil. unfold BCs, zsum. cbn -[Z.mul]. lia.
  - apply Forall_cons_iff in HW' as [Hz HW']. rewrite zcount_cons, BCs_cons. specialize (IH HW').
    destruct Hz as [->|(l & Hl & ->)]; [rewrite bcs_24; replace (4 * (m + 1) <=? 24) with false by (symmetry; apply Z.leb_gt; lia); lia|].
    rewrite bcs_kv by lia. destruct (Z.leb_spec (4 * (m + 1)) (4 * (l + 1))); destruct (Z.eqb_spec l 5); lia.
Qed.

(* [comment removed for export] *)
Lemma HISTOK_big_sum M : HISTOK M -> Forall (fun z => 0 <= z <= 2^30) M ->
  zsum (map (fun z => if 64512 <? z then z else 0) M) <= 5 * HB + 4 * 2^30.
Proof.
  intros (I & Z & HP & HW & HBC & H42 & HL) HF.
  rewrite (zsum_map_perm _ _ _ HP), map_app, zsum_app.
  assert (HI : zsum (map (fun z => if 64512 <? z then z else 0) I) <= 5 * BCs I).
  { unfold BCs. rewrite <- (zsum_map_mul 5 bcs I). apply zsum_map_le. intros z Hz.
    pose proof (proj1 (Forall_forall _ _) HW z Hz) as [->|(l & Hl & ->)]; [rewrite bcs_24; cbn; lia|].
    rewrite bcs_kv by lia. destruct (Z.ltb_spec 64512 (4 * (l + 1))); destruct (Z.eqb_spec l 5); lia. }
  assert (HZ : zsum (map (fun z => if 64512 <? z then z else 0) Z) <= 2^30 * zlen Z).
  { rewrite <- (zsum_map_const (2^30) Z). apply zsum_map_le. intros z Hz.
    assert (Hin : In z M) by (eapply Permutation_in; [apply Permutation_sym; exact HP| apply in_or_app; right; exact Hz]).
    pose proof (proj1 (Forall_forall _ _) HF z Hin) as Hb. cbn beta in Hb. destruct (64512 <? z); lia. }
  pose proof (zlen_le_4 Z HL). pose proof (zlen_nonneg Z). nia.
Qed.

Lemma HISTOK_big_sum' M : HISTOK M -> Forall (fun z => 0 <= z <= 2^30) M ->
  zsum (filter (fun z => 64512 <? z) M) <= 5 * HB + 4 * 2^30.
Proof.
  intros H1 H2. rewrite <- (map_id (filter _ M)). rewrite (zsum_map_filter (fun z => 64512 <? z) (fun z => z) M). exact (HISTOK_big_sum M H1 H2).
Qed.
