(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Bool Lia.
From stdpp Require Import gmap.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import STree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require Import AsanCtrl.
(* [comment removed for export] *)
Unset Lia Cache.
Unset Nia Cache.
Import ListNotations.
Local Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

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

(* [comment removed for export] *)
Definition prim_ok (n : Z) : bool :=
  let c := class_id (needed_size n) in
  (0 <=? rz_log n) && (rz_log n <=? 7) && (rz_size n =? 16 * 2 ^ rz_log n)
  && Bool.eqb (is_primary n) (n <=? 64512)
  && (if is_primary n then (1 <=? c) && (c <=? 30) && (needed_size n <=? size_of_class c) && (32 <=? size_of_class c)
                          && (size_of_class c <=? 65536) && (2 <=? max_cached c) && (max_cached c <=? 16)
                          && (max_cached c / 2 * size_of_class c <=? K_USER_MAP) && (Z.even (max_cached c))
      else (needed_size n =? rup (Z.max n 8) 8 + 2 * 2048)).

(* [comment removed for export] *)
Definition rup8f (x : Z) : Z := Z.shiftl (Z.shiftr (x + 8 - 1) 3) 3.
Lemma rup8f_eq : forall x, rup x 8 = rup8f x.
Proof. intros x. unfold rup, rup8f. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. reflexivity. Qed.
Definition prim_ok_f (n : Z) : bool :=
  let r := rz_log n in
  let rs := Z.shiftl 16 r in
  let ru := rup8f (Z.max n 8) in
  let n0 := ru + rs in
  let pr := n0 <=? K_MAX_SIZE in
  let ns := if pr then n0 else n0 + rs in
  let c := class_id ns in
  (0 <=? r) && (r <=? 7) && (rs =? 16 * 2 ^ r)
  && Bool.eqb pr (n <=? 64512)
  && (if pr then let sc := size_of_class c in let mc := max_cached c in
                 (1 <=? c) && (c <=? 30) && (ns <=? sc) && (32 <=? sc)
                 && (sc <=? 65536) && (2 <=? mc) && (mc <=? 16)
                 && (mc / 2 * sc <=? K_USER_MAP) && (Z.even mc)
      else (ns =? ru + 2 * 2048)).
Lemma prim_ok_f_eq : forall n, prim_ok_f n = prim_ok n.
Proof. intros n. unfold prim_ok, prim_ok_f, needed_size, is_primary, needed0, rounded_size, rz_size. rewrite !rup8f_eq. reflexivity. Qed.
Lemma forallb_ext_eq : forall (f g : Z -> bool), (forall x, f x = g x) -> forall l, forallb f l = forallb g l.
Proof. intros f g H l. induction l as [|x l IH]; cbn; [reflexivity|]. rewrite H, IH. reflexivity. Qed.

Lemma prim_ok_range : forallb prim_ok (zseq 0 (Z.to_nat 70000)) = true.
Proof. rewrite <- (forallb_ext_eq prim_ok_f prim_ok prim_ok_f_eq). vm_cast_no_check (eq_refl true). Qed.

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

(* [comment removed for export] *)
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

Lemma batch_class_facts : size_of_class K_BATCH_CLASS = 8192 /\ max_cached K_BATCH_CLASS = 2 /\ class_id 8192 = K_BATCH_CLASS.
Proof. vm_compute. repeat split; reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition remap_node {R} (pb l : Z) (k : AM R) : AM R :=
  SVis (AMmap pb l PROT_RW F_FIXNORES)
       (fun r => if r =? pb then k else if is_err r then aundef_ USpin k else aundef_ UBadAnswer k).

Lemma poison0_shape : forall R (a s : Z) (k : AM R),
  poison0 a s k = k \/ exists pb l, 0 < l /\ poison0 a s k = remap_node pb l k.
Proof.
  intros. left. reflexivity.   (* [comment removed for export] *)
Qed.

(* [comment removed for export] *)
Lemma poison0_small : forall R (a s : Z) (k : AM R), a mod 8 = 0 -> 0 <= s < 524288 -> poison0 a s k = k.
Proof.
  intros R a s k Ha Hs. reflexivity.   (* [comment removed for export] *)
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

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
  intros. unfold populate_free_array. cbv zeta. simpl.
  repeat first [leaf H | peel | solve [eapply tdepth_mono; [|apply ensure_free_array_depth with (n := n); intros; crush H]; simpl; lia] ].
Qed.

Lemma cache_alloc_depth : forall R st c (k : astate -> bool -> AM R) n,
  (forall st' b, tdepth (k st' b) n) -> tdepth (cache_alloc st c k) (5 + n).
Proof.
  intros. unfold cache_alloc. cbv zeta. simpl.
  repeat first [leaf H | peel | solve [eapply tdepth_mono; [|apply populate_depth with (n := S n); intros; crush H]; simpl; lia] ].
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
  intros. unfold large_dealloc. replace (4 + n)%nat with (2 + (2 + n))%nat by lia. apply poison0_depth. crush H.
Qed.

Lemma amalloc_depth : forall ATOP RESV st n, tdepth (amalloc ATOP RESV st n) 7.
Proof.
  intros. unfold amalloc. cbv zeta.
  destruct (_ || _); [apply tdepth_ret|].
  destruct (is_primary n).
  - eapply tdepth_mono; [|apply cache_alloc_depth with (n := 2%nat)]; [simpl; lia|].
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

(* [comment removed for export] *)
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

(* [comment removed for export] *)
(* [comment removed for export] *)

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

(* [comment removed for export] *)
Lemma rup_small : forall x a, 0 < a -> 0 < x <= a -> rup x a = a.
Proof.
  intros x a Ha Hx. unfold rup.
  assert (E : (x + a - 1) / a = 1) by (symmetry; apply Z.div_unique with (r := x - 1); lia).
  rewrite E. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Section Totality.
Variable AV : list (Z * Z).
Variable ATOP : Z.
Hypothesis HATOP : ALLOC_TOP_MIN <= ATOP <= 2^47.

Definition good_answer (e : aev) (a : Z) : Prop :=
  match e with
  | AMmap addr len _ flags => if addr =? 0 then mmap_answer_ok ATOP len a = true /\ is_err a = false /\ avoids_all a len AV = true
                            else a = addr /\ is_err a = false
  | AMunmap _ _ => a = 0
  | AUndef _ => False
  | _ => True
  end.

(* [comment removed for export] *)
Fixpoint gtotal {R} (P : R -> Prop) (t : AM R) (n : nat) {struct t} : Prop :=
  match t with
  | SRet r => P r
  | SVis e k => match n with O => False | S m => (exists a, good_answer e a) /\ forall a, good_answer e a -> gtotal P (k a) m end
  end.

#[using="Type"] Lemma gtotal_ret : forall R (P : R -> Prop) r n, P r -> gtotal P (SRet r) n.
Proof. destruct n; simpl; auto. Qed.

#[using="Type"] Lemma gtotal_mono : forall R (P Q : R -> Prop) t n m, (forall r, P r -> Q r) -> (n <= m)%nat -> gtotal P t n -> gtotal Q t m.
Proof.
  induction t; intros n m HPQ Hnm Ht; simpl in *.
  - auto.
  - destruct n; [destruct Ht|]. destruct m; [lia|]. destruct Ht as [Hex Hall]. split; auto.
    intros a Ha. apply (H a n m); auto. lia.
Qed.

#[using="Type"] Lemma fixed_addr_nonzero_good : forall addr len p f a,
  addr <> 0 -> good_answer (AMmap addr len p f) a -> a = addr /\ is_err a = false.
Proof. intros. simpl in H0. destruct (Z.eqb_spec addr 0); [lia|auto]. Qed.

#[using="Type"] Lemma good_fixed_exists : forall addr len p f, 0 < addr < TWO64 - 4096 -> exists a, good_answer (AMmap addr len p f) a.
Proof.
  intros. exists addr. simpl. destruct (Z.eqb_spec addr 0); [lia|]. split; auto.
  unfold is_err. apply Z.ltb_ge. lia.
Qed.

#[using="Type"] Lemma fixed_answer_ok_self : forall a, fixed_answer_ok a a = true.
Proof. intros. unfold fixed_answer_ok. rewrite Z.eqb_refl. apply orb_true_r. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma carve_enough : forall mapped alloc size req ums,
  0 < size -> 0 <= alloc <= mapped -> 0 <= req ->
  alloc + req * size > mapped -> ums >= alloc + req * size - mapped ->
  (mapped + ums - alloc) / size >= req.
Proof.
  intros. apply Z.le_ge. apply Z.div_le_lower_bound; [lia|nia].
Qed.

#[using="Type"] Lemma carve_enough_nomap : forall mapped alloc size req,
  0 < size -> 0 <= alloc -> 0 <= req -> alloc + req * size <= mapped -> (mapped - alloc) / size >= req.
Proof. intros. apply Z.le_ge. apply Z.div_le_lower_bound; [lia|nia]. Qed.

(* [comment removed for export] *)

#[using="Type"] Lemma get_put_eq : forall st c r, get_cls (put_cls c r st) c = r.
Proof. intros. unfold get_cls, put_cls, set_cls; simpl. rewrite lookup_insert_eq. reflexivity. Qed.
#[using="Type"] Lemma get_put_ne : forall st c c' r, c <> c' -> get_cls (put_cls c r st) c' = get_cls st c'.
Proof. intros. unfold get_cls, put_cls, set_cls; simpl. rewrite lookup_insert_ne; auto. Qed.
#[using="Type"] Lemma put_put : forall st c r1 r2, put_cls c r2 (put_cls c r1 st) = put_cls c r2 st.
Proof. intros. unfold put_cls, set_cls; simpl. rewrite insert_insert_eq. reflexivity. Qed.
#[using="Type"] Lemma region_beg_put : forall st c r c', region_beg (put_cls c r st) c' = region_beg st c'.
Proof. reflexivity. Qed.
#[using="Type"] Lemma max_count_put : forall st c r c', max_count (put_cls c r st) c' = max_count st c'.
Proof. reflexivity. Qed.
#[using="Type"] Lemma get_cls_init_cache : forall st c, get_cls (init_cache st) c = get_cls st c.
Proof. intros. unfold init_cache. destruct (a_cinit st); reflexivity. Qed.
#[using="Type"] Lemma region_beg_init_cache : forall st c, region_beg (init_cache st) c = region_beg st c.
Proof. intros. unfold init_cache. destruct (a_cinit st); reflexivity. Qed.
#[using="Type"] Lemma max_count_init_cache : forall st c, max_count (init_cache st) c = max_cached c.
Proof. intros. unfold init_cache, max_count. destruct (a_cinit st) eqn:E; [rewrite E|]; reflexivity. Qed.

(* [comment removed for export] *)
Definition addr_ok (st : astate) : Prop :=
  0 < a_space_beg st /\ a_space_beg st + 33 * K_REGION < TWO64 - 4096 /\ 0 < a_ptr_array st /\ a_ptr_array st + K_PTRARR_RESERVE < TWO64 - 4096.
#[using="ATOP HATOP"] Lemma addr_ok_put : forall st c r, addr_ok (put_cls c r st) <-> addr_ok st.
Proof. intros. unfold addr_ok; simpl. tauto. Qed.
#[using="ATOP HATOP"] Lemma addr_ok_init_cache : forall st, addr_ok (init_cache st) <-> addr_ok st.
Proof. intros. unfold init_cache. destruct (a_cinit st); unfold addr_ok; simpl; tauto. Qed.

#[using="Type"] Lemma gtotal_vis : forall R (P : R -> Prop) e k n,
  (exists a, good_answer e a) -> (forall a, good_answer e a -> gtotal P (k a) n) -> gtotal P (SVis e k) (S n).
Proof. intros. simpl. auto. Qed.

#[using="Type"] Lemma rup_ge : forall x a, 0 < a -> x <= rup x a.
Proof. intros. unfold rup. pose proof (Z.div_mod (x + a - 1) a ltac:(lia)). pose proof (Z.mod_pos_bound (x + a - 1) a ltac:(lia)). lia. Qed.
#[using="Type"] Lemma rup_le : forall x a, 0 < a -> rup x a <= x + a - 1.
Proof. intros. unfold rup. pose proof (Z.div_mod (x + a - 1) a ltac:(lia)). pose proof (Z.mod_pos_bound (x + a - 1) a ltac:(lia)). lia. Qed.

(* [comment removed for export] *)
Definition cls_room (r : aclass) : Prop :=
  0 <= c_allocated_user r <= c_mapped_user r /\ c_mapped_user r - c_allocated_user r <= K_USER_MAP
  /\ 0 <= c_num_freed r /\ 0 <= c_mapped_free_array r <= K_FREEARR_MAX
  /\ c_mapped_user r + K_USER_MAP <= K_FREEARR_OFF
  /\ 4 * (c_num_freed r + 16384 + 8) + K_FREEARR_MAP <= K_FREEARR_MAX.

#[using="Type"] Lemma rup_freearr_bounds : forall x, 0 <= x -> 0 <= rup x K_FREEARR_MAP <= x + K_FREEARR_MAP.
Proof.
  intros. unfold rup, K_FREEARR_MAP.
  pose proof (Z.div_mod (x + 262144 - 1) 262144 ltac:(lia)). pose proof (Z.mod_pos_bound (x + 262144 - 1) 262144 ltac:(lia)).
  pose proof (Z.div_pos (x + 262144 - 1) 262144 ltac:(lia) ltac:(lia)). lia.
Qed.

#[using="Type"] Lemma ensure_total : forall R (P : R -> Prop) st c nf (k : astate -> bool -> AM R) m,
  addr_ok st -> 1 <= c <= 31 -> 0 <= nf ->
  0 <= c_mapped_free_array (get_cls st c) <= K_FREEARR_MAX ->
  4 * nf + K_FREEARR_MAP <= K_FREEARR_MAX ->
  (forall r', (r' = get_cls st c \/ (r' = cls_set_mapped_free_array (rup (nf * 4) K_FREEARR_MAP) (get_cls st c)
                                      /\ 0 <= rup (nf * 4) K_FREEARR_MAP <= K_FREEARR_MAX)) -> gtotal P (k (put_cls c r' st) true) m) ->
  gtotal P (k st true) m ->
  gtotal P (ensure_free_array st c nf k) (S m).
Proof.
  intros R P st c nf k m Hao Hc Hnf Hm Hroom Hk Hk0. unfold ensure_free_array. cbv zeta.
  destruct (Z.leb_spec (nf * 4) (c_mapped_free_array (get_cls st c))).
  - eapply gtotal_mono; [| |apply Hk0]; auto.
  - pose proof (rup_freearr_bounds (nf * 4) ltac:(lia)) as Hr.
    destruct (Z.ltb_spec K_FREEARR_MAX (rup (nf * 4) K_FREEARR_MAP)); [lia|].
    unfold ev. apply gtotal_vis.
    + apply good_fixed_exists. unfold addr_ok, region_beg, K_REGION, K_FREEARR_OFF, K_FREEARR_MAX, TWO64 in *. nia.
    + intros a Ha. apply fixed_addr_nonzero_good in Ha.
      2:{ unfold addr_ok, region_beg, K_REGION, K_FREEARR_OFF in *. nia. }
      destruct Ha as [-> Herr]. rewrite fixed_answer_ok_self. cbn [negb]. rewrite Herr.
      apply Hk. right. split; [reflexivity|lia].
Qed.

#[using="Type"] Lemma carve_facts : forall x size, 0 < size -> 0 <= x ->
  0 <= x / size /\ 0 <= x / size * size <= x /\ x - x / size * size < size.
Proof.
  intros x size Hs Hx. pose proof (Z.div_pos x size Hx Hs).
  rewrite (Z.mul_comm (x / size) size). pose proof (Z.div_mod x size ltac:(lia)). pose proof (Z.mod_pos_bound x size ltac:(lia)). lia.
Qed.

#[using="Type"] Lemma div_le_16384 : forall x size, 32 <= size -> 0 <= x <= 2 * K_USER_MAP -> x / size <= 16384.
Proof.
  intros. apply Z.le_trans with (x / 32). apply Z.div_le_compat_l; lia.
  change 16384 with (2 * K_USER_MAP / 32). apply Z.div_le_mono; lia.
Qed.

Local Ltac cproj := cbn [c_mapped_user c_allocated_user c_num_freed c_mapped_free_array c_count
                         cls_set_allocated_user cls_set_num_freed cls_set_mapped_free_array cls_set_mapped_user cls_set_count negb].

(* [comment removed for export] *)
#[using="HATOP"] Lemma populate_total : forall R (P : R -> Prop) st c req (k : astate -> bool -> AM R) m,
  addr_ok st -> 1 <= c <= 31 -> 32 <= size_of_class c -> 0 <= req -> req * size_of_class c <= K_USER_MAP ->
  cls_room (get_cls st c) ->
  (forall r', c_num_freed r' >= c_num_freed (get_cls st c) + req ->
              0 <= c_allocated_user r' <= c_mapped_user r' -> c_mapped_user r' - c_allocated_user r' < size_of_class c ->
              0 <= c_mapped_free_array r' <= K_FREEARR_MAX ->
              c_mapped_user (get_cls st c) <= c_mapped_user r' <= c_mapped_user (get_cls st c) + K_USER_MAP ->
              c_num_freed r' <= c_num_freed (get_cls st c) + 16384 -> c_count r' = c_count (get_cls st c) ->
              gtotal P (k (put_cls c r' st) true) m) ->
  gtotal P (populate_free_array st c req k) (2 + m).
Proof.
  intros R P st c req k m Hao Hc Hsz Hreq Hrs Hr Hk.
  destruct Hr as (Hal & Hgap & Hnf & Hmfa & Hroom1 & Hroom2).
  unfold populate_free_array. cbv zeta.
  set (r := get_cls st c) in *.
  set (size := size_of_class c) in *.
  destruct (Z.leb_spec (c_allocated_user r + req * size) (c_mapped_user r)).
  - (* [comment removed for export] *)
    simpl (2 + m)%nat. apply (gtotal_mono R P P _ (S m)); [auto|lia|].
    pose proof (carve_enough_nomap (c_mapped_user r) (c_allocated_user r) size req ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as Hcarve.
    pose proof (carve_facts (c_mapped_user r - c_allocated_user r) size ltac:(lia) ltac:(lia)) as (Hq0 & Hcv & Hrest).
    pose proof (div_le_16384 (c_mapped_user r - c_allocated_user r) size Hsz ltac:(unfold K_USER_MAP in *; lia)) as Hle.
    set (q := (c_mapped_user r - c_allocated_user r) / size) in *.
    set (cv := q * size) in *. clearbody cv q.
    apply ensure_total; auto; try lia.
    + intros r' Hr'. rewrite put_put, get_put_eq. fold r in Hr'.
      destruct Hr' as [-> | [-> Hb]]; cproj; (apply Hk; cproj; [lia|lia|lia| |lia|lia|reflexivity]); lia.
    + cproj. fold r. apply Hk; cproj; try lia.
  - (* [comment removed for export] *)
    assert (Hums : rup (c_allocated_user r + req * size - c_mapped_user r) K_USER_MAP = K_USER_MAP).
    { apply rup_small; unfold K_USER_MAP in *; lia. }
    rewrite Hums.
    destruct (Z.ltb_spec K_FREEARR_OFF (c_mapped_user r + K_USER_MAP)); [lia|].
    unfold ev. simpl (2 + m)%nat. apply gtotal_vis.
    + apply good_fixed_exists. unfold addr_ok, region_beg, K_REGION, K_FREEARR_OFF, K_USER_MAP, TWO64 in *. nia.
    + intros a Ha. apply fixed_addr_nonzero_good in Ha.
      2:{ unfold addr_ok, region_beg, K_REGION in *. nia. }
      destruct Ha as [-> Herr]. rewrite fixed_answer_ok_self. cbn [negb]. rewrite Herr.
      rewrite get_put_eq. cproj.
      pose proof (carve_enough (c_mapped_user r) (c_allocated_user r) size req K_USER_MAP ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as Hcarve.
      pose proof (carve_facts (c_mapped_user r + K_USER_MAP - c_allocated_user r) size ltac:(lia) ltac:(unfold K_USER_MAP in *; lia)) as (Hq0 & Hcv & Hrest).
      pose proof (div_le_16384 (c_mapped_user r + K_USER_MAP - c_allocated_user r) size Hsz ltac:(unfold K_USER_MAP in *; lia)) as Hle.
      set (q := (c_mapped_user r + K_USER_MAP - c_allocated_user r) / size) in *.
      set (cv := q * size) in *. clearbody cv q.
      apply ensure_total.
      * apply addr_ok_put; auto.
      * auto.
      * lia.
      * rewrite get_put_eq. cproj. lia.
      * lia.
      * intros r' Hr'. rewrite get_put_eq in Hr'. rewrite !put_put, get_put_eq.
        destruct Hr' as [-> | [-> Hb]]; cproj; (apply Hk; cproj; [lia|lia|lia| |lia|lia|reflexivity]); lia.
      * rewrite put_put, get_put_eq. cproj. apply Hk; cproj; try lia.
Qed.

(* [comment removed for export] *)
Definition cls_after (c : Z) (r r' : aclass) : Prop :=
  0 <= c_allocated_user r' <= c_mapped_user r'
  /\ (c_mapped_user r' - c_allocated_user r' <= c_mapped_user r - c_allocated_user r \/ c_mapped_user r' - c_allocated_user r' < size_of_class c)
  /\ 0 <= c_num_freed r' <= c_num_freed r + 16384
  /\ 0 <= c_mapped_free_array r' <= K_FREEARR_MAX
  /\ c_mapped_user r <= c_mapped_user r' <= c_mapped_user r + K_USER_MAP.

#[using="HATOP"] Lemma cache_alloc_total : forall R (P : R -> Prop) st c (k : astate -> bool -> AM R) m,
  addr_ok st -> 1 <= c <= 31 -> 32 <= size_of_class c -> 2 <= max_cached c <= 16 -> max_cached c / 2 * size_of_class c <= K_USER_MAP ->
  cls_room (get_cls st c) -> 0 <= c_count (get_cls st c) ->
  (forall st1 r', (st1 = st \/ st1 = init_cache st) -> cls_after c (get_cls st c) r' -> 0 <= c_count r' < max_cached c + c_count (get_cls st c) ->
                  gtotal P (k (put_cls c r' st1) true) m) ->
  gtotal P (cache_alloc st c k) (2 + m).
Proof.
  intros R P st c k m Hao Hc Hsz Hmc Hmcs Hroom Hcnt Hk.
  pose proof Hroom as (Hal & Hgap & Hnf & Hmfa & Hroom1 & Hroom2).
  unfold cache_alloc. cbv zeta.
  destruct (Z.ltb_spec 0 (c_count (get_cls st c))).
  - (* [comment removed for export] *)
    apply (gtotal_mono R P P _ m); [auto|lia|]. apply Hk; [left; reflexivity| |cproj; lia].
    unfold cls_after; cproj. lia.
  - rewrite max_count_init_cache, get_cls_init_cache.
    assert (Hhalf : 1 <= max_cached c / 2 <= 8 /\ 2 * (max_cached c / 2) <= max_cached c).
    { split. split; [apply Z.div_le_lower_bound|apply Z.div_le_upper_bound]; lia. apply Z.mul_div_le; lia. }
    set (n := max_cached c / 2) in *. clearbody n.
    destruct (Z.leb_spec n (c_num_freed (get_cls st c))).
    + (* [comment removed for export] *)
      destruct (Z.ltb_spec (c_num_freed (get_cls st c)) n); [lia|].
      apply (gtotal_mono R P P _ m); [auto|lia|]. apply Hk; [right; reflexivity| |cproj; lia].
      unfold cls_after; cproj. lia.
    + apply populate_total.
      * apply addr_ok_init_cache; auto.
      * auto. * auto. * lia. * apply Z.le_trans with (n * size_of_class c); [apply Z.mul_le_mono_nonneg_r; lia|lia].
      * rewrite get_cls_init_cache. auto.
      * intros r' H1 H2 H3 H4 H5 H6 H7. rewrite get_cls_init_cache in *. rewrite get_put_eq.
        destruct (Z.ltb_spec (c_num_freed r') n); [lia|]. cproj. rewrite put_put.
        apply Hk; [right; reflexivity| |cproj; lia]. unfold cls_after; cproj. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma poison0_total : forall R (P : R -> Prop) a s (k : AM R) m,
  0 <= a < TWO64 -> 0 <= s -> a + s <= TWO64 -> gtotal P k m -> gtotal P (poison0 a s k) (S m).
Proof.
  intros R P a s k m Ha Hs Has Hk. unfold poison0.   (* [comment removed for export] *)
  eapply gtotal_mono; [| |apply Hk]; auto.
Qed.

Definition sec_room (st : astate) : Prop := 0 <= a_nres st /\ 8 * (a_nres st + K_CHUNKS_BLOCK) <= K_PTRARR_RESERVE.

#[using="Type"] Lemma sec_map_size_bounds : forall n, 64512 < n <= 2^40 -> n + 4096 <= sec_map_size n <= n + 4096 + 4096 + 4096 + 8.
Proof.
  intros n Hn. unfold sec_map_size, needed_size. rewrite large_not_primary by lia. unfold needed0, rounded_size.
  assert (Hr : rz_size n = 2048).
  { unfold rz_size, rz_log. repeat (rewrite (proj2 (Z.leb_gt _ _)) by lia). reflexivity. }
  rewrite Hr. pose proof (rup_ge (Z.max n 8) 8 ltac:(lia)). pose proof (rup_le (Z.max n 8) 8 ltac:(lia)).
  pose proof (rup_ge (rup (Z.max n 8) 8 + 2048 + 2048) PG ltac:(unfold PG; lia)). pose proof (rup_le (rup (Z.max n 8) 8 + 2048 + 2048) PG ltac:(unfold PG; lia)).
  unfold PG in *. lia.
Qed.

#[using="Type"] Lemma large_alloc_total : forall R (P : R -> Prop) RESV st n (k : astate -> option achunk -> AM R) m,
  addr_ok st -> sec_room st -> 64512 < n <= 2^40 ->
  AV = RESV ++ asec_ranges st ->
  (exists a, good_answer (AMmap 0 (sec_map_size n) PROT_RW F_ANON) a) ->
  (forall st1 mb, 0 < mb -> mb + sec_map_size n <= ATOP ->
     (st1 = set_nsec (a_nsec st + 1) st \/ st1 = set_nres (a_nres st + K_CHUNKS_BLOCK) (set_nsec (a_nsec st + 1) st)) ->
     gtotal P (k st1 (Some (CSec mb (sec_map_size n) n))) m) ->
  gtotal P (large_alloc ATOP RESV st n k) (2 + m).
Proof.
  intros R P RESV st n k m Hao (Hr0 & Hr1) Hn HAV HEX Hk. unfold large_alloc. unfold ev. simpl (2 + m)%nat.
  pose proof (sec_map_size_bounds n Hn) as Hms.
  apply gtotal_vis.
  - exact HEX.
  - intros mb Hmb. simpl in Hmb. destruct Hmb as (Hok & Herr & Hav). rewrite Hok, Herr. cbn [negb].
    rewrite <- HAV, Hav. cbn [andb negb].
    unfold mmap_answer_ok in Hok. rewrite Herr in Hok. cbn [orb] in Hok. rewrite !Bool.andb_true_iff in Hok.
    destruct Hok as [[[Hp Hal] Hce] Hlt]. apply Z.ltb_lt in Hp. apply Z.leb_le in Hce. apply Z.ltb_lt in Hlt.
    pose proof (rup_ge (sec_map_size n) PG ltac:(unfold PG; lia)).
    destruct (Z.eqb_spec (a_nsec st) (a_nres st)).
    + destruct (Z.ltb_spec K_PTRARR_RESERVE (8 * (a_nres st + K_CHUNKS_BLOCK))); [lia|].
      apply gtotal_vis.
      * apply good_fixed_exists. unfold addr_ok, K_PTRARR_RESERVE, K_CHUNKS_BLOCK, TWO64 in *. lia.
      * intros r Hr. apply fixed_addr_nonzero_good in Hr. 2:{ unfold addr_ok in *; lia. }
        destruct Hr as [-> Herr2]. rewrite fixed_answer_ok_self, Herr2. cbn [negb].
        apply Hk; [lia|lia|right; reflexivity].
    + apply (gtotal_mono R P P _ m); [auto|lia|]. apply Hk; [lia|lia|left; reflexivity].
Qed.

(* [comment removed for export] *)
#[using="HATOP"] Theorem amalloc_total : forall RESV st n,
  addr_ok st -> 0 <= n <= 2^32 ->
  (is_primary n = true -> let c := class_id (needed_size n) in cls_room (get_cls st c) /\ 0 <= c_count (get_cls st c)) ->
  (is_primary n = false -> sec_room st /\ AV = RESV ++ asec_ranges st /\ exists a, good_answer (AMmap 0 (sec_map_size n) PROT_RW F_ANON) a) ->
  gtotal (fun r => snd r <> None) (amalloc ATOP RESV st n) 3.
Proof.
  intros RESV st n Hao Hn Hprim Hsec. unfold amalloc.
  assert (Hns : needed_size n <= 2^40).
  { unfold needed_size, needed0, rounded_size. pose proof (rup_le (Z.max n 8) 8 ltac:(lia)).
    pose proof (rz_log_range n) as Hrl.
    assert (0 <= rz_size n <= 2048).
    { unfold rz_size. rewrite Z.shiftl_mul_pow2 by lia. change 2048 with (16 * 2^7).
      split. apply Z.mul_nonneg_nonneg; [lia|apply Z.pow_nonneg; lia]. apply Z.mul_le_mono_nonneg_l; [lia|apply Z.pow_le_mono_r; lia]. }
    destruct (is_primary n); lia. }
  destruct (Z.ltb_spec (2^40) n); [lia|]. destruct (Z.ltb_spec (2^40) (needed_size n)); [lia|]. cbn [orb].
  destruct (is_primary n) eqn:Hp.
  - pose proof (primary_class_facts n ltac:(lia) Hp) as F. cbv zeta in F. destruct F as (F1 & F2 & F3 & F4 & F5 & F6).
    destruct (Hprim eq_refl) as [Hroom Hcnt].
    apply (gtotal_mono _ (fun r => snd r <> None) _ _ 2); [auto|lia|].
    apply cache_alloc_total; auto; try lia.
    intros st1 r' _ _ _. simpl. congruence.
  - destruct (Hsec eq_refl) as (Hsr & HAV & HEX).
    apply large_alloc_total; auto.
    + assert (64512 < n) by (destruct (Z_lt_dec 64512 n); auto; rewrite is_primary_iff in Hp by lia; apply Z.leb_gt in Hp; lia). lia.
    + intros st1 mb Hmb Hce Hst1. cbv beta iota.
      pose proof (sec_map_size_bounds n) as Hms.
      assert (64512 < n) by (destruct (Z_lt_dec 64512 n); auto; rewrite is_primary_iff in Hp by lia; apply Z.leb_gt in Hp; lia).
      apply poison0_total.
      * unfold chunk_user_beg. unfold ALLOC_TOP_MIN, TWO64, PG in *.
        assert (rz_size n = 2048) by (unfold rz_size, rz_log; repeat (rewrite (proj2 (Z.leb_gt _ _)) by lia); reflexivity). lia.
      * rewrite Z.land_nonneg. lia.
      * unfold chunk_user_beg. assert (rz_size n = 2048) by (unfold rz_size, rz_log; repeat (rewrite (proj2 (Z.leb_gt _ _)) by lia); reflexivity).
        assert (0 <= Z.land n (Z.lnot 7) <= n).
        { rewrite <- Z.ldiff_land. change 7 with (Z.ones 3). rewrite Z.ldiff_ones_r by lia.
          rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
          pose proof (Z.div_mod n (2^3) ltac:(lia)). pose proof (Z.mod_pos_bound n (2^3) ltac:(lia)). lia. }
        unfold ALLOC_TOP_MIN, TWO64, PG in *. lia.
      * simpl. congruence.
Qed.

(* [comment removed for export] *)

#[using="Type"] Lemma qbytes_put : forall st c r, a_qloc_bytes (put_cls c r st) = a_qloc_bytes st /\ a_qglob_bytes (put_cls c r st) = a_qglob_bytes st
  /\ a_qloc (put_cls c r st) = a_qloc st /\ a_qglob (put_cls c r st) = a_qglob st.
Proof. intros. repeat split; reflexivity. Qed.
#[using="Type"] Lemma qbytes_init_cache : forall st, a_qloc_bytes (init_cache st) = a_qloc_bytes st /\ a_qglob_bytes (init_cache st) = a_qglob_bytes st
  /\ a_qloc (init_cache st) = a_qloc st /\ a_qglob (init_cache st) = a_qglob st.
Proof. intros. unfold init_cache. destruct (a_cinit st); repeat split; reflexivity. Qed.

(* [comment removed for export] *)
#[using="HATOP"] Lemma enqueue_total : forall R (P : R -> Prop) st ch (k : astate -> AM R) m,
  addr_ok st -> 0 <= chunk_size ch ->
  cls_room (get_cls st K_BATCH_CLASS) -> 0 <= c_count (get_cls st K_BATCH_CLASS) ->
  (forall st', a_qglob_bytes st' = a_qglob_bytes st -> a_qglob st' = a_qglob st ->
              a_qloc_bytes st <= a_qloc_bytes st' <= a_qloc_bytes st + chunk_size ch + Q_BATCH_BYTES -> gtotal P (k st') m) ->
  gtotal P (enqueue st ch k) (2 + m).
Proof.
  intros R P st ch k m Hao Hn Hroom Hcnt Hk.
  pose proof batch_class_facts as (Bsz & Bmc & _).
  unfold enqueue. cbv zeta.
  assert (NB : forall st0, addr_ok st0 -> get_cls st0 K_BATCH_CLASS = get_cls st K_BATCH_CLASS ->
            a_qglob_bytes st0 = a_qglob_bytes st -> a_qglob st0 = a_qglob st -> a_qloc_bytes st0 = a_qloc_bytes st ->
            gtotal P (cache_alloc st0 K_BATCH_CLASS (fun st1 ok =>
              if negb ok then aundef_ USpin (k st1)
              else k (set_qloc (a_qloc st1 ++ [mkABatch 1 (chunk_size ch + Q_BATCH_BYTES) [ch]]) (a_qloc_bytes st1 + chunk_size ch + Q_BATCH_BYTES) st1))) (2 + m)).
  { intros st0 Hao0 Hcls Hg Hgl Hl. apply cache_alloc_total.
    - exact Hao0. - unfold K_BATCH_CLASS; lia. - rewrite Bsz; lia. - rewrite Bmc; lia.
    - rewrite Bsz, Bmc. vm_compute. congruence.
    - rewrite Hcls; auto. - rewrite Hcls; auto.
    - intros st1 r' Hst1 _ _. cbn [negb].
      pose proof (qbytes_init_cache st0) as (Q1 & Q2 & Q3 & Q4).
      apply Hk; destruct Hst1 as [-> | ->]; simpl; rewrite ?Q1, ?Q2, ?Q3, ?Q4; unfold Q_BATCH_BYTES; lia || congruence. }
  destruct (rev (a_qloc st)) as [|b rl].
  - apply NB; auto.
  - destruct (Z.eqb_spec (b_count b) Q_BATCH).
    + apply NB; auto.
    + apply (gtotal_mono R P P _ m); [auto|lia|]. apply Hk; simpl; auto. unfold Q_BATCH_BYTES; lia.
Qed.

(* [comment removed for export] *)
#[using="HATOP"] Theorem afree_total_norecycle : forall st id ch,
  addr_ok st -> (a_live st) !! id = Some ch -> 0 <= chunk_size ch <= Q_MAX ->
  cls_room (get_cls st K_BATCH_CLASS) -> 0 <= c_count (get_cls st K_BATCH_CLASS) ->
  a_qglob_bytes st + a_qloc_bytes st + chunk_size ch + Q_BATCH_BYTES <= Q_MAX ->
  gtotal (fun _ => True) (afree st (Some id)) 2.
Proof.
  intros st id ch Hao Hlive Hn Hroom Hcnt Hq. unfold afree. rewrite Hlive.
  destruct (Z.leb_spec (chunk_size ch) Q_MAX); [|lia].
  apply (enqueue_total _ (fun _ => True) (set_live (delete id (a_live st)) st) ch _ 0).
  - exact Hao. - lia. - exact Hroom. - exact Hcnt.
  - intros st' Hg Hgl Hl. simpl in Hg, Hgl, Hl. cbv beta.
    destruct (Z.ltb_spec Q_CACHE (a_qloc_bytes st')).
    + unfold drain. cbv zeta. simpl. rewrite Hg.
      destruct (Z.ltb_spec Q_MAX (a_qglob_bytes st + a_qloc_bytes st')); [lia|]. simpl. exact I.
    + simpl. exact I.
Qed.

(* [comment removed for export] *)

#[using="Type"] Lemma init_cls_room : forall sb pa c, cls_room (get_cls (ainit sb pa) c).
Proof. intros. unfold cls_room, get_cls, ainit; simpl. rewrite lookup_empty. simpl. unfold K_USER_MAP, K_FREEARR_MAX, K_FREEARR_OFF, K_FREEARR_MAP. lia. Qed.
#[using="Type"] Lemma init_sec_room : forall sb pa, sec_room (ainit sb pa).
Proof. intros. unfold sec_room, ainit, K_CHUNKS_BLOCK, K_PTRARR_RESERVE; simpl. lia. Qed.
#[using="Type"] Lemma init_addr_ok : forall sb pa, 0 < sb -> sb + 33 * K_REGION < TWO64 - 4096 -> 0 < pa -> pa + K_PTRARR_RESERVE < TWO64 - 4096 -> addr_ok (ainit sb pa).
Proof. intros. unfold addr_ok, ainit; simpl. lia. Qed.
(* [comment removed for export] *)
#[using="HATOP"] Example first_malloc_total : forall sb pa, 0 < sb -> sb + 33 * K_REGION < TWO64 - 4096 -> 0 < pa -> pa + K_PTRARR_RESERVE < TWO64 - 4096 ->
  AV = [] ->
  gtotal (fun r => snd r <> None) (amalloc ATOP [] (ainit sb pa) 65536) 3.
Proof.
  intros sb pa H1 H2 H3 H4 HAV. apply amalloc_total. apply init_addr_ok; auto. lia.
  intros _. split. apply init_cls_room. unfold get_cls, ainit; simpl. rewrite lookup_empty. simpl. lia.
  intros _. split; [apply init_sec_room|]. split.
  { rewrite HAV. unfold asec_ranges, achunks, ainit. cbn [a_live a_qloc a_qglob]. rewrite map_to_list_empty. reflexivity. }
  (* [comment removed for export] *)
  exists 4096. cbn [good_answer Z.eqb]. rewrite HAV. split; [|split; reflexivity].
  unfold mmap_answer_ok, is_err. unfold ALLOC_TOP_MIN, TWO64, PG in *.
  change (sec_map_size 65536) with 0x12000. change (rup 0x12000 4096) with 0x12000.
  rewrite (proj2 (Z.ltb_lt 0 4096)) by lia. change (4096 mod 4096 =? 0) with true.
  rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.ltb_lt 4096 _)) by lia.
  destruct (Z.ltb_spec (2^64 - 4096) 4096); [lia| reflexivity].
Qed.
End Totality.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition sum_Z (l : list Z) : Z := fold_right Z.add 0 l.

Definition chunk_mapped (ch : achunk) : Z := match ch with CSec _ ms _ => ms | CPrim _ _ => 0 end.

(* [comment removed for export] *)
Definition a_mapped_bytes (st : astate) : Z :=
  sum_Z (map (fun kr => cls_mapped_bytes (snd kr)) (map_to_list (a_cls st)))
  + sum_Z (map (fun kc => chunk_mapped (snd kc)) (map_to_list (a_live st)))
  + sum_Z (map (fun b => sum_Z (map chunk_mapped (b_chunks b))) (a_qloc st ++ a_qglob st))
  + 8 * a_nres st.

Lemma a_mapped_bytes_init : forall sb pa, a_mapped_bytes (ainit sb pa) = 0.
Proof. intros. reflexivity. Qed.

(* [comment removed for export] *)
Definition startup_committed_bytes : Z :=
  0x10000 + 0x38e000 + 0x1000 + 0x1000 + 0x10000 + 0x1000 + 0x1000 + FAKESTACK_BYTES + 2 * PG + PG + 0x100000 + 0x1000 + 0x1000.
Example startup_committed_val : startup_committed_bytes = 16515072.
Proof. vm_compute. reflexivity. Qed.
