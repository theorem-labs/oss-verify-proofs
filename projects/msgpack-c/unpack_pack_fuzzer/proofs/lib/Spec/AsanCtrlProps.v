(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From stdpp Require Import gmap.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec Require Import STree AsanCtrl.
Unset Nra Cache.

Unset Lia Cache.
Unset Nia Cache.
Import ListNotations.
Local Open Scope Z_scope.

Fixpoint zseq (lo : Z) (n : nat) : list Z :=
  match n with O => [] | S m => lo :: zseq (lo + 1) m end.

Lemma zseq_spec : forall n lo x, In x (zseq lo n) <-> lo <= x < lo + Z.of_nat n.
Proof.
  induction n; intros; simpl.
  - split; [intros []|lia].
  - rewrite Nat2Z.inj_succ. rewrite IHn. lia.
Qed.

Lemma forallb_zseq : forall (p : Z -> bool) lo n,
  forallb p (zseq lo n) = true -> forall x, lo <= x < lo + Z.of_nat n -> p x = true.
Proof.
  intros p lo n H x Hx. rewrite forallb_forall in H. apply H. apply zseq_spec. exact Hx.
Qed.

Definition prim_ok (n : Z) : bool :=
  let c := class_id (needed_size n) in
  (0 <=? rz_log n) && (rz_log n <=? 7) && (rz_size n =? 16 * 2 ^ rz_log n)
  && Bool.eqb (is_primary n) (n <=? 64512)
  && (if is_primary n then (1 <=? c) && (c <=? 30) && (needed_size n <=? size_of_class c) && (32 <=? size_of_class c)
                          && (size_of_class c <=? 65536) && (2 <=? max_cached c) && (max_cached c <=? 16)
                          && (max_cached c / 2 * size_of_class c <=? K_USER_MAP) && (Z.even (max_cached c))
      else (needed_size n =? rup (Z.max n 8) 8 + 2 * 2048)).

Lemma prim_ok_range : forallb prim_ok (zseq 0 (Z.to_nat 70000)) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma prim_facts : forall n, 0 <= n < 70000 -> prim_ok n = true.
Proof. intros. apply (forallb_zseq prim_ok 0 (Z.to_nat 70000) prim_ok_range). rewrite Z2Nat.id; lia. Qed.

Lemma is_primary_iff : forall n, 0 <= n < 70000 -> is_primary n = (n <=? 64512).
Proof.
  intros n H. pose proof (prim_facts n H) as P. unfold prim_ok in P. cbn zeta in P.
  repeat rewrite Bool.andb_true_iff in P.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  match goal with Hb : Bool.eqb _ _ = true |- _ => apply Bool.eqb_prop in Hb; exact Hb end.
Qed.

Lemma rz_log_range : forall n, 0 <= rz_log n <= 7.
Proof. intros. unfold rz_log. repeat (destruct (_ <=? _)); lia. Qed.

Lemma rup8_ge : forall m, 0 <= m -> m <= rup m 8.
Proof.
  intros m Hm. unfold rup.
  pose proof (Z.div_mod (m + 8 - 1) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (m + 8 - 1) 8 ltac:(lia)). lia.
Qed.

Lemma large_not_primary : forall n, 64512 < n -> is_primary n = false.
Proof.
  intros n H. unfold is_primary, needed0, K_MAX_SIZE. apply Z.leb_gt.
  assert (Hr : rz_log n = 7).
  { unfold rz_log.
    rewrite (proj2 (Z.leb_gt n 48)) by lia. rewrite (proj2 (Z.leb_gt n 96)) by lia.
    rewrite (proj2 (Z.leb_gt n 448)) by lia. rewrite (proj2 (Z.leb_gt n 3968)) by lia.
    rewrite (proj2 (Z.leb_gt n 16128)) by lia. rewrite (proj2 (Z.leb_gt n 32256)) by lia.
    rewrite (proj2 (Z.leb_gt n 64512)) by lia. reflexivity. }
  unfold rz_size. rewrite Hr. change (Z.shiftl 16 7) with 2048.
  unfold rounded_size. pose proof (rup8_ge (Z.max n 8) ltac:(lia)). lia.
Qed.

Lemma primary_class_facts : forall n, 0 <= n -> is_primary n = true ->
  let c := class_id (needed_size n) in
  1 <= c <= 30 /\ needed_size n <= size_of_class c /\ 32 <= size_of_class c <= 65536
  /\ 2 <= max_cached c <= 16 /\ max_cached c / 2 * size_of_class c <= K_USER_MAP /\ Z.even (max_cached c) = true.
Proof.
  intros n Hn Hp.
  assert (n < 70000) by (destruct (Z_lt_dec n 70000); auto; rewrite large_not_primary in Hp; [discriminate|lia]).
  pose proof (prim_facts n ltac:(lia)) as P. unfold prim_ok in P. cbn zeta in P. rewrite Hp in P.
  repeat rewrite Bool.andb_true_iff in P.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  repeat match goal with Hb : (_ <=? _) = true |- _ => apply Z.leb_le in Hb end.
  cbn zeta. repeat split; auto; lia.
Qed.

Definition al16_ok (n : Z) : bool :=
  let c := class_id (needed16 n) in
  implb ((16 <=? n) && (n mod 16 =? 0))
    ((1 <=? c) && (c <=? 30) && (needed16 n <=? size_of_class c) && (32 <=? size_of_class c) && (size_of_class c <=? 65536)
     && (2 <=? max_cached c) && (max_cached c <=? 16) && (max_cached c / 2 * size_of_class c <=? K_USER_MAP) && Z.even (max_cached c)
     && negb (c =? K_BATCH_CLASS) && (size_of_class c <=? 2 * n + 32) && is_primary16 n && is_primary n).
Lemma al16_ok_range : forallb al16_ok (zseq 0 (Z.to_nat (ALIGNED_NMAX + 1))) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma al16_facts : forall n, 16 <= n <= ALIGNED_NMAX -> n mod 16 = 0 ->
  let c := class_id (needed16 n) in
  1 <= c <= 30 /\ needed16 n <= size_of_class c /\ 32 <= size_of_class c <= 65536
  /\ 2 <= max_cached c <= 16 /\ max_cached c / 2 * size_of_class c <= K_USER_MAP /\ Z.even (max_cached c) = true
  /\ c <> K_BATCH_CLASS /\ size_of_class c <= 2 * n + 32 /\ is_primary16 n = true /\ is_primary n = true.
Proof.
  intros n Hn Hm. pose proof (forallb_zseq al16_ok 0 (Z.to_nat (ALIGNED_NMAX + 1)) al16_ok_range n ltac:(rewrite Z2Nat.id; unfold ALIGNED_NMAX in *; lia)) as P.
  unfold al16_ok in P. cbn zeta in P.
  rewrite (proj2 (Z.leb_le 16 n)) in P by lia. rewrite Hm in P. cbn [Z.eqb andb implb] in P.
  repeat rewrite Bool.andb_true_iff in P.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  repeat match goal with Hb : (_ <=? _) = true |- _ => apply Z.leb_le in Hb end.
  match goal with Hb : negb _ = true |- _ => apply Bool.negb_true_iff, Z.eqb_neq in Hb end.
  cbn zeta. repeat split; auto; lia.
Qed.

Lemma prim_cls_facts : forall c n, 0 <= n <= 64512 -> prim_cls_ok c n ->
  1 <= c <= 30 /\ 32 <= size_of_class c <= 65536
  /\ 2 <= max_cached c <= 16 /\ max_cached c / 2 * size_of_class c <= K_USER_MAP /\ Z.even (max_cached c) = true.
Proof.
  intros c n Hn [->|(-> & Hr & Hm)].
  - assert (EP : is_primary n = true) by (rewrite is_primary_iff by lia; apply Z.leb_le; lia).
    pose proof (primary_class_facts n ltac:(lia) EP) as F. cbv zeta in F. tauto.
  - pose proof (al16_facts n Hr Hm) as F. cbv zeta in F. tauto.
Qed.
Lemma prim_cls_c24 : forall c n, prim_cls_ok c n -> c = K_BATCH_CLASS -> c = class_id (needed_size n).
Proof.
  intros c n [H|(-> & Hr & Hm)] E; [exact H|]. pose proof (al16_facts n Hr Hm) as F. cbv zeta in F. exfalso. tauto.
Qed.

Lemma batch_class_facts : size_of_class K_BATCH_CLASS = 8192 /\ max_cached K_BATCH_CLASS = 2 /\ class_id 8192 = K_BATCH_CLASS.
Proof. vm_compute. repeat split; reflexivity. Qed.

Definition remap_node {R} (pb l : Z) (k : AM R) : AM R :=
  SVis (AMmap pb l PROT_RW F_FIXNORES)
       (fun r => if r =? pb then k else if is_err r then aundef_ USpin k else aundef_ UBadAnswer k).

Lemma poison0_shape : forall R (a s : Z) (k : AM R),
  poison0 a s k = k \/ exists pb l, 0 < l /\ poison0 a s k = remap_node pb l k.
Proof. intros. left. reflexivity. Qed.

Lemma poison0_small : forall R (a s : Z) (k : AM R), a mod 8 = 0 -> 0 <= s < 524288 -> poison0 a s k = k.
Proof. intros. reflexivity. Qed.

Lemma poison0_id : forall R (a s : Z) (k : AM R), a mod 8 = 0 -> 0 <= s < 2^64 -> poison0 a s k = k.
Proof. intros. reflexivity. Qed.

Fixpoint tdepth {E A R} (t : stree E A R) (n : nat) {struct t} : Prop :=
  match t with
  | SRet _ => True
  | SVis _ k => match n with O => False | S m => forall a, tdepth (k a) m end
  end.
Lemma tdepth_ret : forall E A R (r : R) n, @tdepth E A R (SRet r) n.
Proof. intros; simpl; auto. Qed.
Lemma tdepth_mono : forall E A R (t : stree E A R) n m, (n <= m)%nat -> tdepth t n -> tdepth t m.
Proof.
  induction t; intros n m Hnm Ht; [apply tdepth_ret|].
  destruct n; [destruct Ht|]. destruct m; [lia|]. simpl in *. intros a. eapply H; [|apply Ht]. lia.
Qed.
Lemma aundef_depth : forall R w (k : AM R) n, tdepth k n -> tdepth (aundef_ w k) (S n).
Proof. intros. unfold aundef_. simpl. auto. Qed.
Lemma tdepth_S : forall E A R (t : stree E A R) n, tdepth t n -> tdepth t (S n).
Proof. intros. eapply tdepth_mono; [|eassumption]. lia. Qed.

Ltac peel :=
  lazymatch goal with
  | |- True => exact I
  | |- forall _, _ => intros ?
  | |- tdepth (SRet _) _ => apply tdepth_ret
  | |- tdepth (aundef_ _ _) (S _) => apply aundef_depth
  | |- tdepth (aundef_ _ _) ?m => destruct m; [exfalso|apply aundef_depth]
  | |- tdepth (SVis _ _) (S _) => simpl; intros ?
  | |- tdepth (ev _ _) (S _) => unfold ev at 1; simpl; intros ?
  | |- tdepth (if ?b then _ else _) _ => destruct b
  | |- tdepth (match ?x with _ => _ end) _ => destruct x
  end.
Ltac leaf H := solve [eapply tdepth_mono; [|apply H]; simpl; lia].
Ltac crush H := cbv zeta; simpl; repeat first [leaf H | peel].

Lemma ensure_free_array_depth : forall R st c nf (k : astate -> bool -> AM R) n,
  (forall st' b, tdepth (k st' b) n) -> tdepth (ensure_free_array st c nf k) (2 + n).
Proof. intros. unfold ensure_free_array. crush H. Qed.

Lemma populate_depth : forall R st c rq (k : astate -> bool -> AM R) n,
  (forall st' b, tdepth (k st' b) n) -> tdepth (populate_free_array st c rq k) (4 + n).
Proof.
  intros. unfold populate_free_array, populate_free_array_g. cbv zeta. simpl.
  repeat first [leaf H | peel | solve [eapply tdepth_mono; [|apply ensure_free_array_depth with (n := n); intros; crush H]; simpl; lia] ].
Qed.

Lemma emb_realloc_depth : forall R ATOP RESV st w (k : astate -> AM R) n,
  (forall st', tdepth (k st') n) -> tdepth (emb_realloc ATOP RESV st w k) (3 + n).
Proof. intros. unfold emb_realloc. destruct (a_emb st) as [[d cap] sz]. crush H. Qed.
Lemma emb_append_depth : forall R ATOP RESV st len (k : astate -> AM R) n,
  (forall st', tdepth (k st') n) -> tdepth (emb_append ATOP RESV st len k) (6 + n).
Proof.
  intros. unfold emb_append. cbv zeta.
  assert (GO : forall st1, tdepth (let '(_, cap, sz) := a_emb st1 in
                if cap <? sz + len then emb_realloc ATOP RESV st1 (sz + len) (fun st2 => k (emb_set_size (sz + len) st2))
                else k (emb_set_size (sz + len) st1)) (3 + n)).
  { intros st1. destruct (a_emb st1) as [[d cap] sz]. destruct (cap <? sz + len).
    - apply emb_realloc_depth. intros; apply H.
    - eapply tdepth_mono; [| apply H]. lia. }
  pose proof (GO st) as G0. destruct (a_emb st) as [[d0 cap0] sz0]. destruct (cap0 =? 0).
  - replace (6 + n)%nat with (3 + (3 + n))%nat by lia. apply emb_realloc_depth. exact GO.
  - eapply tdepth_mono; [| exact G0]. lia.
Qed.
Lemma exh_report_depth : forall R ATOP RESV c st (k : astate -> AM R) n,
  (forall st', tdepth (k st') n) -> tdepth (exh_report ATOP RESV c st k) (12 + n).
Proof.
  intros. unfold exh_report. destruct (exh_mem c st).
  - eapply tdepth_mono; [| apply H]. lia.
  - replace (12 + n)%nat with (6 + (6 + n))%nat by lia. apply emb_append_depth. intros. apply emb_append_depth. exact H.
Qed.
Lemma populate_x_depth : forall R ATOP RESV st c rq (k : astate -> bool -> AM R) n,
  (forall st' b, tdepth (k st' b) n) -> tdepth (populate_free_array_x ATOP RESV st c rq k) (12 + n).
Proof.
  intros. unfold populate_free_array_x. destruct (c =? K_BATCH_CLASS).
  { eapply tdepth_mono; [| apply populate_depth; exact H]. lia. }
  unfold populate_free_array_g. cbv zeta. simpl.
  repeat first [leaf H | solve [apply exh_report_depth; intros; apply H] | peel
               | solve [eapply tdepth_mono; [|apply ensure_free_array_depth with (n := n); intros; crush H]; simpl; lia] ].
Qed.

Lemma cache_alloc_depth : forall R st c (k : astate -> bool -> AM R) n,
  (forall st' b, tdepth (k st' b) n) -> tdepth (cache_alloc st c k) (5 + n).
Proof.
  intros. unfold cache_alloc, cache_alloc_g. cbv zeta. simpl.
  repeat first [leaf H | peel | solve [eapply tdepth_mono; [|apply populate_depth with (n := S n); intros; crush H]; simpl; lia] ].
Qed.
Lemma cache_alloc_x_depth : forall R ATOP RESV st c (k : astate -> bool -> AM R) n,
  (forall st' b, tdepth (k st' b) n) -> tdepth (cache_alloc_x ATOP RESV st c k) (13 + n).
Proof.
  intros. unfold cache_alloc_x, cache_alloc_g. cbv zeta. simpl.
  repeat first [leaf H | peel | solve [eapply tdepth_mono; [|apply populate_x_depth with (n := S n); intros; crush H]; simpl; lia] ].
Qed.

Lemma cache_dealloc_depth : forall R st c (k : astate -> AM R) n,
  (forall st', tdepth (k st') n) -> tdepth (cache_dealloc st c k) (3 + n).
Proof.
  intros. unfold cache_dealloc. cbv zeta. simpl.
  repeat first [leaf H | peel | solve [eapply tdepth_mono; [|apply ensure_free_array_depth with (n := S n); intros; crush H]; simpl; lia] ].
Qed.

Lemma poison0_depth : forall R a s (k : AM R) n, tdepth k n -> tdepth (poison0 a s k) (2 + n).
Proof.
  intros. unfold poison0. cbv zeta. simpl.
  repeat first [ solve [eapply tdepth_mono; [|apply H]; simpl; lia] | peel ].
Qed.

Lemma large_alloc_depth : forall R ATOP RESV st m (k : astate -> option achunk -> AM R) n,
  (forall st' o, tdepth (k st' o) n) -> tdepth (large_alloc ATOP RESV st m k) (3 + n).
Proof. intros. unfold large_alloc. crush H. Qed.

Lemma large_dealloc_depth : forall R st mb ms (k : astate -> AM R) n,
  (forall st', tdepth (k st') n) -> tdepth (large_dealloc st mb ms k) (4 + n).
Proof.
  intros. unfold large_dealloc, poison0, flush_shadow. crush H.
Qed.

Lemma amalloc_depth : forall ATOP RESV st n, tdepth (amalloc ATOP RESV st n) 15.
Proof.
  intros. unfold amalloc. cbv zeta.
  destruct (_ || _); [apply tdepth_ret|].
  destruct (is_primary n).
  - eapply tdepth_mono; [|apply cache_alloc_x_depth with (n := 2%nat)]; [simpl; lia|].
    intros st' b. destruct b; apply tdepth_ret.
  - eapply tdepth_mono; [|apply large_alloc_depth with (n := 2%nat)]; [simpl; lia|].
    intros st' [ch|]; [|apply tdepth_ret]. destruct ch; [apply tdepth_ret|].
    replace 2%nat with (2 + 0)%nat by lia. apply poison0_depth. apply tdepth_ret.
Qed.

Lemma recycle_chunk_depth : forall R st ch (k : astate -> AM R) n,
  (forall st', tdepth (k st') n) -> tdepth (recycle_chunk st ch k) (4 + n).
Proof.
  intros. unfold recycle_chunk. destruct ch.
  - eapply tdepth_mono; [|apply cache_dealloc_depth; eauto]. simpl; lia.
  - apply large_dealloc_depth; auto.
Qed.

Lemma recycle_chunks_depth : forall R l st (k : astate -> AM R) n,
  (forall st', tdepth (k st') n) -> tdepth (recycle_chunks st l k) (4 * length l + n).
Proof.
  induction l; intros; simpl.
  - auto.
  - eapply tdepth_mono; [|apply recycle_chunk_depth with (n := (4 * length l + n)%nat)]. simpl; lia.
    intros. apply IHl. auto.
Qed.

Definition batches_cost (bs : list abatch) : nat :=
  fold_right (fun b acc => (4 * length (b_chunks b) + 3 + acc)%nat) 0%nat bs.

Lemma do_recycle_depth : forall R bs st (k : astate -> AM R) n,
  (forall st', tdepth (k st') n) -> tdepth (do_recycle st bs k) (batches_cost bs + n).
Proof.
  induction bs; intros; simpl; auto.
  eapply tdepth_mono; [|apply recycle_chunks_depth with (n := (3 + (batches_cost bs + n))%nat)].
  rewrite length_rev. simpl; lia.
  intros. apply cache_dealloc_depth. intros. apply IHbs. auto.
Qed.

Lemma enqueue_depth : forall R st ch (k : astate -> AM R) n,
  (forall st', tdepth (k st') n) -> tdepth (enqueue st ch k) (6 + n).
Proof.
  intros. unfold enqueue. cbv zeta.
  assert (K : forall st' (b : bool), tdepth (if negb b then aundef_ USpin (k st') else
     k (set_qloc (a_qloc st' ++ [mkABatch 1 (chunk_size ch + Q_BATCH_BYTES) [ch]]) (a_qloc_bytes st' + chunk_size ch + Q_BATCH_BYTES) st')) (S n)).
  { intros st' b. destruct b; cbn [negb]. apply tdepth_S; apply H. apply aundef_depth; apply H. }
  destruct (rev (a_qloc st)) as [|b rl].
  - replace (6 + n)%nat with (5 + S n)%nat by lia. apply cache_alloc_depth. exact K.
  - destruct (b_count b =? Q_BATCH).
    + replace (6 + n)%nat with (5 + S n)%nat by lia. apply cache_alloc_depth. exact K.
    + eapply tdepth_mono; [|apply H]. lia.
Qed.

Definition cls_wf (mc : Z) (r : aclass) : Prop :=
  0 <= c_allocated_user r <= c_mapped_user r /\ 0 <= c_num_freed r /\ 0 <= c_mapped_free_array r /\ 0 <= c_count r <= mc
  /\ c_mapped_user r mod K_USER_MAP = 0 /\ c_mapped_free_array r mod K_FREEARR_MAP = 0.

Definition awf (st : astate) : Prop :=
  0 <= a_nres st /\ 0 <= a_nsec st /\ 0 <= a_qloc_bytes st /\ 0 <= a_qglob_bytes st
  /\ a_ptr_array st mod PG = 0
  /\ forall c, 1 <= c <= 31 -> cls_wf (max_count st c) (get_cls st c).

Lemma ainit_wf : forall sb pa, pa mod PG = 0 -> awf (ainit sb pa).
Proof.
  intros. unfold awf, ainit, cls_wf, get_cls, max_count; simpl. repeat split; try lia; auto.
  all: rewrite lookup_empty; simpl; try lia; reflexivity.
Qed.

Lemma rup_small : forall x a, 0 < a -> 0 < x <= a -> rup x a = a.
Proof.
  intros x a Ha Hx. unfold rup.
  assert (E : (x + a - 1) / a = 1) by (symmetry; apply Z.div_unique with (r := x - 1); lia).
  rewrite E. lia.
Qed.

Lemma fixed_answer_ok_self : forall a, fixed_answer_ok a a = true.
Proof. intros. unfold fixed_answer_ok. rewrite Z.eqb_refl. apply orb_true_r. Qed.
Lemma carve_enough : forall mapped alloc size req ums,
  0 < size -> 0 <= alloc <= mapped -> 0 <= req ->
  alloc + req * size > mapped -> ums >= alloc + req * size - mapped ->
  (mapped + ums - alloc) / size >= req.
Proof.
  intros. apply Z.le_ge. apply Z.div_le_lower_bound; [lia|nia].
Qed.
Lemma carve_enough_nomap : forall mapped alloc size req,
  0 < size -> 0 <= alloc -> 0 <= req -> alloc + req * size <= mapped -> (mapped - alloc) / size >= req.
Proof. intros. apply Z.le_ge. apply Z.div_le_lower_bound; [lia|nia]. Qed.
Lemma get_put_eq : forall st c r, get_cls (put_cls c r st) c = r.
Proof. intros. unfold get_cls, put_cls, set_cls; simpl. rewrite lookup_insert_eq. reflexivity. Qed.
Lemma get_put_ne : forall st c c' r, c <> c' -> get_cls (put_cls c r st) c' = get_cls st c'.
Proof. intros. unfold get_cls, put_cls, set_cls; simpl. rewrite lookup_insert_ne; auto. Qed.
Lemma put_put : forall st c r1 r2, put_cls c r2 (put_cls c r1 st) = put_cls c r2 st.
Proof. intros. unfold put_cls, set_cls; simpl. rewrite insert_insert_eq. reflexivity. Qed.
Lemma region_beg_put : forall st c r c', region_beg (put_cls c r st) c' = region_beg st c'.
Proof. reflexivity. Qed.
Lemma max_count_put : forall st c r c', max_count (put_cls c r st) c' = max_count st c'.
Proof. reflexivity. Qed.
Lemma get_cls_init_cache : forall st c, get_cls (init_cache st) c = get_cls st c.
Proof. intros. unfold init_cache. destruct (a_cinit st); reflexivity. Qed.
Lemma region_beg_init_cache : forall st c, region_beg (init_cache st) c = region_beg st c.
Proof. intros. unfold init_cache. destruct (a_cinit st); reflexivity. Qed.
Lemma max_count_init_cache : forall st c, max_count (init_cache st) c = max_cached c.
Proof. intros. unfold init_cache, max_count. destruct (a_cinit st) eqn:E; [rewrite E|]; reflexivity. Qed.
Lemma rup_ge : forall x a, 0 < a -> x <= rup x a.
Proof. intros. unfold rup. pose proof (Z.div_mod (x + a - 1) a ltac:(lia)). pose proof (Z.mod_pos_bound (x + a - 1) a ltac:(lia)). lia. Qed.
Lemma rup_le : forall x a, 0 < a -> rup x a <= x + a - 1.
Proof. intros. unfold rup. pose proof (Z.div_mod (x + a - 1) a ltac:(lia)). pose proof (Z.mod_pos_bound (x + a - 1) a ltac:(lia)). lia. Qed.
Lemma rup_freearr_bounds : forall x, 0 <= x -> 0 <= rup x K_FREEARR_MAP <= x + K_FREEARR_MAP.
Proof.
  intros. unfold rup, K_FREEARR_MAP.
  pose proof (Z.div_mod (x + 262144 - 1) 262144 ltac:(lia)). pose proof (Z.mod_pos_bound (x + 262144 - 1) 262144 ltac:(lia)).
  pose proof (Z.div_pos (x + 262144 - 1) 262144 ltac:(lia) ltac:(lia)). lia.
Qed.
Lemma carve_facts : forall x size, 0 < size -> 0 <= x ->
  0 <= x / size /\ 0 <= x / size * size <= x /\ x - x / size * size < size.
Proof.
  intros x size Hs Hx. pose proof (Z.div_pos x size Hx Hs).
  rewrite (Z.mul_comm (x / size) size). pose proof (Z.div_mod x size ltac:(lia)). pose proof (Z.mod_pos_bound x size ltac:(lia)). lia.
Qed.
Lemma sec_map_size_bounds : forall n, 64512 < n <= 2^40 -> n + 4096 <= sec_map_size n <= n + 4096 + 4096 + 4096 + 8.
Proof.
  intros n Hn. unfold sec_map_size, needed_size. rewrite large_not_primary by lia. unfold needed0, rounded_size.
  assert (Hr : rz_size n = 2048).
  { unfold rz_size, rz_log. repeat (rewrite (proj2 (Z.leb_gt _ _)) by lia). reflexivity. }
  rewrite Hr. pose proof (rup_ge (Z.max n 8) 8 ltac:(lia)). pose proof (rup_le (Z.max n 8) 8 ltac:(lia)).
  pose proof (rup_ge (rup (Z.max n 8) 8 + 2048 + 2048) PG ltac:(unfold PG; lia)). pose proof (rup_le (rup (Z.max n 8) 8 + 2048 + 2048) PG ltac:(unfold PG; lia)).
  unfold PG in *. lia.
Qed.
Lemma qbytes_put : forall st c r, a_qloc_bytes (put_cls c r st) = a_qloc_bytes st /\ a_qglob_bytes (put_cls c r st) = a_qglob_bytes st
  /\ a_qloc (put_cls c r st) = a_qloc st /\ a_qglob (put_cls c r st) = a_qglob st.
Proof. intros. repeat split; reflexivity. Qed.
Lemma qbytes_init_cache : forall st, a_qloc_bytes (init_cache st) = a_qloc_bytes st /\ a_qglob_bytes (init_cache st) = a_qglob_bytes st
  /\ a_qloc (init_cache st) = a_qloc st /\ a_qglob (init_cache st) = a_qglob st.
Proof. intros. unfold init_cache. destruct (a_cinit st); repeat split; reflexivity. Qed.

Definition sum_Z (l : list Z) : Z := fold_right Z.add 0 l.

Definition chunk_mapped (ch : achunk) : Z := match ch with CSec _ ms _ => ms | CPrim _ _ => 0 end.

Definition a_mapped_bytes (st : astate) : Z :=
  sum_Z (map (fun kr => cls_mapped_bytes (snd kr)) (map_to_list (a_cls st)))
  + sum_Z (map (fun kc => chunk_mapped (snd kc)) (map_to_list (a_live st)))
  + sum_Z (map (fun b => sum_Z (map chunk_mapped (b_chunks b))) (a_qloc st ++ a_qglob st))
  + 8 * a_nres st.

Lemma a_mapped_bytes_init : forall sb pa, a_mapped_bytes (ainit sb pa) = 0.
Proof. intros. reflexivity. Qed.

Definition startup_committed_bytes : Z :=
  0x10000 + 0x38e000 + 0x1000 + 0x1000 + 0x10000 + 0x1000 + 0x1000 + FAKESTACK_BYTES + 2 * PG + PG + 0x100000 + 0x1000 + 0x1000.
Example startup_committed_val : startup_committed_bytes = 16515072.
Proof. vm_compute. reflexivity. Qed.
