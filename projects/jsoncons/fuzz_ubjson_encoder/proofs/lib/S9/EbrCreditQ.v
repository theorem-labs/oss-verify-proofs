(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import ArtRuns ArtBridge EbtFxBatch3 EbrInv EbrInvFreePure.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Definition art_ibytes (its : list (Z * Z)) : Z := fold_right (fun it z => snd it + z) 0 its.
Definition art_items_pos (bs : list art_batch) : Prop := forall b it, In b bs -> In it (bt_items b) -> 1 <= snd it.

Lemma arq_bytes_cons : forall b r, art_batches_bytes (b :: r) = 8192 + art_ibytes (bt_items b) + art_batches_bytes r.
Proof. intros. reflexivity. Qed.
Lemma arq_bytes_app : forall a b, art_batches_bytes (a ++ b) = art_batches_bytes a + art_batches_bytes b.
Proof. intros a b. induction a as [|x r IH]; [reflexivity|]. cbn [app]. rewrite !arq_bytes_cons, IH. lia. Qed.
Lemma art_ibytes_app : forall a b, art_ibytes (a ++ b) = art_ibytes a + art_ibytes b.
Proof. intros a b. unfold art_ibytes. induction a as [|x r IH]; cbn [app fold_right]; [lia|]. rewrite IH. lia. Qed.
Lemma art_items_pos_cons : forall b r, art_items_pos (b :: r) -> (forall it, In it (bt_items b) -> 1 <= snd it) /\ art_items_pos r.
Proof. intros b r H. split; [intros it Hit; exact (H b it (or_introl eq_refl) Hit) | intros x it Hx Hit; exact (H x it (or_intror Hx) Hit)]. Qed.
Lemma art_items_pos_app : forall a b, art_items_pos (a ++ b) <-> art_items_pos a /\ art_items_pos b.
Proof.
  intros a b. split.
  - intros H. split; intros x it Hx Hit; apply (H x it); [apply in_or_app; left; exact Hx | exact Hit | apply in_or_app; right; exact Hx | exact Hit].
  - intros (Ha & Hb) x it Hx Hit. apply in_app_or in Hx. destruct Hx as [Hx|Hx]; [exact (Ha x it Hx Hit) | exact (Hb x it Hx Hit)].
Qed.
Lemma art_ibytes_ge : forall its, (forall it, In it its -> 1 <= snd it) -> Z.of_nat (length its) <= art_ibytes its.
Proof.
  induction its as [|x r IH]; intros H; [cbn; lia|]. unfold art_ibytes in *. cbn [fold_right length]. rewrite Nat2Z.inj_succ.
  specialize (IH (fun it Hit => H it (or_intror Hit))). specialize (H x (or_introl eq_refl)). lia.
Qed.
Lemma arq_bytes_ge : forall bs, art_items_pos bs -> 8192 * Z.of_nat (length bs) <= art_batches_bytes bs.
Proof.
  induction bs as [|b r IH]; intros H; [cbn; lia|]. rewrite arq_bytes_cons. cbn [length]. rewrite Nat2Z.inj_succ.
  destruct (art_items_pos_cons b r H) as (Hb & Hr). specialize (IH Hr). pose proof (art_ibytes_ge (bt_items b) Hb). lia.
Qed.

Lemma art_nnonfull_cons : forall b r, art_nnonfull (b :: r) = (if art_bfull b then 0 else 1) + art_nnonfull r.
Proof.
  intros b r. unfold art_nnonfull. cbn [List.filter]. destruct (art_bfull b); cbn [negb]; [lia|].
  cbn [length]. rewrite Nat2Z.inj_succ. lia.
Qed.
Lemma art_nnonfull_nil : art_nnonfull [] = 0.
Proof. reflexivity. Qed.
Lemma art_nnonfull_app : forall a b, art_nnonfull (a ++ b) = art_nnonfull a + art_nnonfull b.
Proof. intros a b. unfold art_nnonfull. rewrite List.filter_app, length_app, Nat2Z.inj_add. reflexivity. Qed.
Lemma art_nnonfull_range : forall bs, 0 <= art_nnonfull bs <= Z.of_nat (length bs).
Proof. intros bs. unfold art_nnonfull. pose proof (List.filter_length_le (fun b => negb (art_bfull b)) bs). lia. Qed.

Lemma art_qt_ok_nil : art_qt_ok [].
Proof. intros b []. Qed.
Lemma art_qt_ok_tail : forall b r, art_qt_ok (b :: r) -> art_qt_ok r.
Proof.
  intros b r H x Hx. apply H. destruct r as [|y r']; [destruct Hx|]. cbn [removelast]. right. exact Hx.
Qed.
Lemma art_qt_ok_nnonfull : forall bs, art_qt_ok bs -> art_nnonfull bs <= 1.
Proof.
  induction bs as [|b r IH]; intros H; [rewrite art_nnonfull_nil; lia|]. rewrite art_nnonfull_cons.
  destruct r as [|y r'].
  - rewrite art_nnonfull_nil. destruct (art_bfull b); cbv iota; lia.
  - assert (Fb : art_bfull b = true) by (apply H; cbn [removelast]; left; reflexivity). rewrite Fb. cbv iota.
    specialize (IH (art_qt_ok_tail b (y :: r') H)). lia.
Qed.
Lemma art_removelast_snoc : forall (A : Type) (l : list A) x, removelast (l ++ [x]) = l.
Proof. intros A l x. apply removelast_last. Qed.

Lemma art_qt_ok_add : forall qt b it, art_qt_ok qt -> art_qt_ok (art_qt_add qt b it).
Proof.
  intros qt b it H. unfold art_qt_add.
  destruct (art_free_newb qt) eqn:NB.
  - intros x Hx. rewrite art_removelast_snoc in Hx.
    destruct (exists_last (l := qt)) as (q' & lb & E); [intros ->; destruct Hx|]. subst qt.
    apply in_app_or in Hx. destruct Hx as [Hx|[<-|[]]].
    + apply H. rewrite art_removelast_snoc. exact Hx.
    + unfold art_free_newb, art_enq_newb, art_lastb in NB. rewrite last_last in NB. rewrite length_app in NB. cbn [length] in NB.
      apply orb_true_iff in NB. destruct NB as [NB|NB]; [apply Z.eqb_eq in NB; lia|]. apply Z.eqb_eq in NB.
      unfold art_bfull. apply Nat.eqb_eq. lia.
  - intros x Hx. rewrite art_removelast_snoc in Hx. apply H. exact Hx.
Qed.

Lemma art_qg_ok_skipn : forall k bs, art_qg_ok bs -> art_qg_ok (skipn k bs).
Proof.
  induction k as [|k IH]; intros bs H; [exact H|]. destruct bs as [|b r]; [exact I|]. cbn [skipn]. apply IH. exact (proj2 H).
Qed.
Lemma art_qg_ok_of_qt : forall t, art_qt_ok t -> art_items_pos t -> art_qg_ok t.
Proof.
  induction t as [|b r IH]; intros H P; [exact I|]. split.
  - pose proof (art_qt_ok_nnonfull (b :: r) H). pose proof (arq_bytes_ge (b :: r) P). pose proof (art_nnonfull_range (b :: r)). nia.
  - apply IH; [exact (art_qt_ok_tail b r H) | exact (proj2 (art_items_pos_cons b r P))].
Qed.

Lemma art_qg_ok_transfer : forall g t, art_qg_ok g -> art_qt_ok t -> art_items_pos t -> 2 ^ 20 < art_batches_bytes t -> art_qg_ok (g ++ t).
Proof.
  induction g as [|b r IH]; intros t G T P B; [exact (art_qg_ok_of_qt t T P)|].
  destruct G as (G1 & G2). cbn [app]. split; [|exact (IH t G2 T P B)].
  change (b :: r ++ t) with ((b :: r) ++ t). rewrite art_nnonfull_app, arq_bytes_app.
  pose proof (art_qt_ok_nnonfull t T). pose proof (art_nnonfull_range t). lia.
Qed.
Lemma art_qg_ok_nnonfull : forall bs, art_qg_ok bs -> 2 ^ 20 * art_nnonfull bs <= art_batches_bytes bs + 2 ^ 20.
Proof. intros [|b r] H; [rewrite art_nnonfull_nil; change (art_batches_bytes []) with 0; lia | exact (proj1 H)]. Qed.

Lemma art_nirr_nil : forall spb, art_nirr spb [] = 0.
Proof. reflexivity. Qed.
Lemma art_ibytes_nil : art_ibytes [] = 0.
Proof. reflexivity. Qed.
Lemma arq_bytes_nil : art_batches_bytes [] = 0.
Proof. reflexivity. Qed.
Lemma art_nirr_cons : forall spb it l, art_nirr spb (it :: l) = (if art_irr spb it then 1 else 0) + art_nirr spb l.
Proof. intros spb it l. unfold art_nirr. cbn [List.filter]. destruct (art_irr spb it); [cbn [length]; rewrite Nat2Z.inj_succ; lia | lia]. Qed.
Lemma art_nirr_app : forall spb a b, art_nirr spb (a ++ b) = art_nirr spb a + art_nirr spb b.
Proof. intros spb a b. unfold art_nirr. rewrite List.filter_app, length_app, Nat2Z.inj_add. reflexivity. Qed.
Lemma art_nirr_range : forall spb l, 0 <= art_nirr spb l <= Z.of_nat (length l).
Proof. intros spb l. unfold art_nirr. pose proof (List.filter_length_le (art_irr spb) l). lia. Qed.
Lemma art_items_cons : forall b r, art_items (b :: r) = bt_items b ++ art_items r.
Proof. reflexivity. Qed.
Lemma art_items_app : forall a b, art_items (a ++ b) = art_items a ++ art_items b.
Proof. intros a b. unfold art_items. apply flat_map_app. Qed.
Lemma art_ibytes_irr : forall spb its, (forall it, In it its -> 1 <= snd it) -> 64 * (Z.of_nat (length its) - art_nirr spb its) <= art_ibytes its.
Proof.
  induction its as [|x r IH]; intros H; [rewrite art_nirr_nil, art_ibytes_nil; cbn [length]; lia|]. rewrite art_nirr_cons. unfold art_ibytes in *. cbn [fold_right length]. rewrite Nat2Z.inj_succ.
  specialize (IH (fun it Hit => H it (or_intror Hit))). pose proof (H x (or_introl eq_refl)) as Hx.
  destruct (art_irr spb x) eqn:E; [lia|].
  unfold art_irr in E. apply orb_false_iff in E. destruct E as (E & _). apply orb_false_iff in E. destruct E as (E & _). apply Z.ltb_ge in E. lia.
Qed.

Lemma art_bytes_full : forall spb bs, art_items_pos bs ->
  8192 * Z.of_nat (length bs) + 64 * (1021 * (Z.of_nat (length bs) - art_nnonfull bs) - art_nirr spb (art_items bs)) <= art_batches_bytes bs.
Proof.
  induction bs as [|b r IH]; intros P; [rewrite art_nnonfull_nil, arq_bytes_nil; change (art_items []) with (@nil (Z * Z)); rewrite art_nirr_nil; cbn [length]; lia|].
  destruct (art_items_pos_cons b r P) as (Pb & Pr). specialize (IH Pr).
  rewrite arq_bytes_cons, art_nnonfull_cons, art_items_cons, art_nirr_app. cbn [length]. rewrite Nat2Z.inj_succ.
  pose proof (art_ibytes_irr spb (bt_items b) Pb) as Hb. pose proof (art_nirr_range spb (bt_items b)) as Rb.
  pose proof (art_ibytes_ge (bt_items b) Pb) as Gb.
  destruct (art_bfull b) eqn:F; cbv iota.
  - unfold art_bfull in F. apply Nat.eqb_eq in F. rewrite F in Hb. change (Z.of_nat 1021) with 1021 in Hb. lia.
  - lia.
Qed.

Lemma art_nb_bound : forall spb bs irr, art_qg_ok bs -> art_items_pos bs -> art_nirr spb (art_items bs) <= irr ->
  65536 * Z.of_nat (length bs) <= art_batches_bytes bs + 64 * irr + 65536 * art_nnonfull bs
  /\ 2 ^ 20 * art_nnonfull bs <= art_batches_bytes bs + 2 ^ 20.
Proof.
  intros spb bs irr Q P I. pose proof (art_bytes_full spb bs P) as B. pose proof (art_qg_ok_nnonfull bs Q) as N.
  pose proof (art_nnonfull_range bs) as R. split; [lia | exact N].
Qed.

Lemma art_merge_dead : forall spb bs irr, art_qg_ok bs -> art_items_pos bs -> art_nirr spb (art_items bs) <= irr -> 0 <= irr <= 4096 ->
  2 ^ 20 <= art_batches_bytes bs -> 16384 * Z.of_nat (length bs) <= art_batches_bytes bs.
Proof.
  intros spb bs irr Q P I Hirr Hb. destruct (art_nb_bound spb bs irr Q P I) as (B1 & B2).
  change (2 ^ 20) with 1048576 in *. lia.
Qed.

Lemma art_nb_small : forall spb bs irr, art_qg_ok bs -> art_items_pos bs -> art_nirr spb (art_items bs) <= irr -> 0 <= irr <= 4096 ->
  art_batches_bytes bs <= 2 ^ 30 -> Z.of_nat (length bs) <= 17416.
Proof.
  intros spb bs irr Q P I Hirr Hb. destruct (art_nb_bound spb bs irr Q P I) as (B1 & B2).
  change (2 ^ 20) with 1048576 in *. change (2 ^ 30) with 1073741824 in *. lia.
Qed.
Lemma art_items_length : forall bs, (forall b, In b bs -> (length (bt_items b) <= 1021)%nat) -> Z.of_nat (length (art_items bs)) <= 1021 * Z.of_nat (length bs).
Proof.
  induction bs as [|b r IH]; intros H; [change (art_items []) with (@nil (Z * Z)); cbn [length]; lia|]. rewrite art_items_cons, length_app, Nat2Z.inj_add. cbn [length]. rewrite Nat2Z.inj_succ.
  specialize (IH (fun x Hx => H x (or_intror Hx))). specialize (H b (or_introl eq_refl)). lia.
Qed.

Lemma art_nirr_perm : forall spb l l', Permutation l l' -> art_nirr spb l = art_nirr spb l'.
Proof.
  intros spb l l' P. induction P as [|x l l' P IH|x y l|l1 l2 l3 P1 IH1 P2 IH2].
  - reflexivity.
  - rewrite !art_nirr_cons, IH. reflexivity.
  - rewrite !art_nirr_cons. lia.
  - rewrite IH1. exact IH2.
Qed.
Lemma art_nirr_hdrs_perm : forall spb (LB LB' : list (Z * Z)), List.NoDup (map fst LB) -> List.NoDup (map fst LB') -> (forall b, In b LB <-> In b LB') ->
  art_nirr spb (art_hdrs LB') = art_nirr spb (art_hdrs LB) /\ length LB' = length LB.
Proof.
  intros spb LB LB' N1 N2 EQ.
  assert (P : Permutation LB LB').
  { apply NoDup_Permutation; [exact (List.NoDup_map_inv fst LB N1) | exact (List.NoDup_map_inv fst LB' N2) | exact EQ]. }
  split; [symmetry; apply art_nirr_perm; unfold art_hdrs; apply Permutation_map; exact P | symmetry; apply Permutation_length; exact P].
Qed.
