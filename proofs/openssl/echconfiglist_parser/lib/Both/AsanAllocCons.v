(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FinFun.
From Stdlib Require Import FMapPositive.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import AsanAllocModel.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import AllocWf AllocKit AG_MallocModel AG_WFHit CidBits AllocBudget.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition ncarved (st : astate) (c : Z) : Z := rg_allocated_user (get_region st c) / class_size c.
Definition slot (st : astate) (c i : Z) : Z := region_beg st c + i * class_size c.

Definition own_free  (st : astate) (c : Z) : list Z := map (compact_to_addr st c) (rg_free_array (get_region st c)).
Definition own_cache (st : astate) (c : Z) : list Z := map (compact_to_addr st c) (pc_chunks (get_pc st c)).
Definition own_chunk (st : astate) (c : Z) : list Z := map ch_alloc_beg (filter (fun ch => ch_class ch =? c) (chunk_list st)).
Definition own_batch (st : astate) (c : Z) : list Z :=
  if c =? kBatchClass then map qb_addr (qc_list (as_tq st) ++ qc_list (as_gq st)) else [].
(* [comment removed for export] *)
Definition owners (st : astate) (X : Z -> list Z) (c : Z) : list Z :=
  own_free st c ++ own_cache st c ++ own_chunk st c ++ own_batch st c ++ X c.
Definition noX : Z -> list Z := fun _ => [].

Definition COMPLETE (st : astate) (X : Z -> list Z) : Prop :=
  forall c, 1 <= c < kNumClasses -> forall i, 0 <= i < ncarved st c -> In (slot st c i) (owners st X c).

(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint zseq (a : Z) (n : nat) : list Z := match n with O => [] | S k => a :: zseq (a + 1) k end.
Lemma zseq_In : forall n a x, In x (zseq a n) <-> a <= x < a + Z.of_nat n.
Proof.
  induction n as [|n IH]; intros a x; cbn [zseq].
  - split; [intros []| lia].
  - rewrite Nat2Z.inj_succ. split.
    + intros [<-|H]; [lia|]. apply IH in H. lia.
    + intros H. destruct (Z.eq_dec a x); [left; exact e| right]. apply IH. lia.
Qed.
Lemma zseq_length : forall n a, length (zseq a n) = n.
Proof. induction n; intros; cbn; [reflexivity| now rewrite IHn]. Qed.
Lemma zseq_NoDup : forall n a, NoDup (zseq a n).
Proof.
  induction n as [|n IH]; intros a; cbn; constructor; [| apply IH].
  intros H. apply zseq_In in H. lia.
Qed.

Lemma zlen_app {A} : forall (l1 l2 : list A), zlen (l1 ++ l2) = zlen l1 + zlen l2.
Proof. intros. unfold zlen. rewrite length_app, Nat2Z.inj_add. reflexivity. Qed.
Lemma zlen_map {A B} : forall (f : A -> B) l, zlen (map f l) = zlen l.
Proof. intros. unfold zlen. rewrite length_map. reflexivity. Qed.
Lemma zlen_nonneg {A} : forall (l : list A), 0 <= zlen l.
Proof. intros. unfold zlen. lia. Qed.

Lemma slots_NoDup : forall st c n, 0 < class_size c -> NoDup (map (slot st c) (zseq 0 n)).
Proof.
  intros st c n Hs. apply Injective_map_NoDup; [| apply zseq_NoDup].
  intros x y E. unfold slot in E. nia.
Qed.

(* [comment removed for export] *)
Lemma COMPLETE_count : forall st X c, COMPLETE st X -> 1 <= c < kNumClasses -> 0 < class_size c -> 0 <= ncarved st c ->
  ncarved st c <= Z.of_nat (length (owners st X c)).
Proof.
  intros st X c CO Hc Hs Hn.
  pose proof (NoDup_incl_length (l := map (slot st c) (zseq 0 (Z.to_nat (ncarved st c)))) (l' := owners st X c)
                (slots_NoDup st c _ Hs)) as L.
  rewrite length_map, zseq_length in L.
  assert (I : incl (map (slot st c) (zseq 0 (Z.to_nat (ncarved st c)))) (owners st X c)).
  { intros x Hx. apply in_map_iff in Hx. destruct Hx as (i & <- & Hi). apply zseq_In in Hi. apply (CO c Hc i). lia. }
  specialize (L I). lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition rview (r : region) : Z * list Z := (rg_allocated_user r, rg_free_array r).
Definition cview (st : astate) := (as_space_beg st, map rview (as_regions st), as_cache st, as_chunks st, as_tq st, as_gq st).

Lemma znth_map {A B} : forall (f : A -> B) l i d, znth (map f l) i (f d) = f (znth l i d).
Proof. intros f l. induction l as [|x l IH]; intros [|i] d; cbn; try reflexivity. apply IH. Qed.
Lemma rview_get_region : forall st c, rview (get_region st c) = znth (map rview (as_regions st)) (zidx c) (rview region0).
Proof. intros. unfold get_region. rewrite znth_map. reflexivity. Qed.

Lemma rview_eq_of_view : forall a b c, cview a = cview b -> rview (get_region a c) = rview (get_region b c).
Proof.
  intros a b c E. rewrite !rview_get_region. unfold cview in E.
  set (ra := map rview (as_regions a)) in *. set (rb := map rview (as_regions b)) in *.
  assert (H : ra = rb) by congruence. rewrite H. reflexivity.
Qed.

Lemma owners_view : forall a b X c, cview a = cview b -> owners a X c = owners b X c.
Proof.
  intros a b X c E. pose proof (rview_eq_of_view a b c E) as R. unfold rview in R.
  assert (FA : rg_free_array (get_region a c) = rg_free_array (get_region b c)) by congruence.
  unfold cview in E.
  assert (SB : as_space_beg a = as_space_beg b) by congruence.
  assert (CA : as_cache a = as_cache b) by congruence.
  assert (CH : as_chunks a = as_chunks b) by congruence.
  assert (TQ : as_tq a = as_tq b) by congruence.
  assert (GQ : as_gq a = as_gq b) by congruence.
  unfold owners, own_free, own_cache, own_chunk, own_batch, get_pc, chunk_list, compact_to_addr, region_beg.
  rewrite FA, SB, CA, CH, TQ, GQ. reflexivity.
Qed.
Lemma ncarved_view : forall a b c, cview a = cview b -> ncarved a c = ncarved b c.
Proof.
  intros a b c E. pose proof (rview_eq_of_view a b c E) as R. unfold rview in R. unfold ncarved. congruence.
Qed.
Lemma slot_view : forall a b c i, cview a = cview b -> slot a c i = slot b c i.
Proof. intros a b c i E. unfold cview in E. unfold slot, region_beg. assert (SB : as_space_beg a = as_space_beg b) by congruence. rewrite SB. reflexivity. Qed.
Lemma COMPLETE_view : forall a b X, cview a = cview b -> COMPLETE a X -> COMPLETE b X.
Proof.
  intros a b X E CO c Hc i Hi. rewrite <- (owners_view a b X c E), <- (slot_view a b c i E). apply CO; [exact Hc|].
  rewrite (ncarved_view a b c E). exact Hi.
Qed.

(* [comment removed for export] *)
Lemma cview_paint : forall st lo hi v, cview (paint st lo hi v) = cview st.            Proof. reflexivity. Qed.
Lemma cview_add_map : forall st m, cview (add_map st m) = cview st.                   Proof. reflexivity. Qed.
Lemma cview_remove_map : forall st b, cview (remove_map st b) = cview st.             Proof. reflexivity. Qed.
Lemma cview_set_sec : forall st n l, cview (set_sec st n l) = cview st.               Proof. reflexivity. Qed.
Lemma cview_set_internal_init : forall st, cview (set_internal_init st) = cview st.  Proof. reflexivity. Qed.
Lemma cview_set_cache_inited : forall st, cview (set_cache_inited st) = cview st.    Proof. reflexivity. Qed.
Lemma cview_ensure_cache_inited : forall st, cview (ensure_cache_inited st) = cview st.
Proof. intros st. unfold ensure_cache_inited. destruct (as_cache_inited st); reflexivity. Qed.
Lemma cview_pop_env : forall st, cview (snd (pop_env st)) = cview st.
Proof. intros st. unfold pop_env. destruct (as_env st); reflexivity. Qed.

Lemma poison_shadow_cview : forall st a n v st' ev, poison_shadow st a n v = Some (st', ev) -> cview st' = cview st.
Proof.
  intros st a n v st' ev H. unfold poison_shadow in H.
  repeat match type of H with
         | (if ?b then _ else _) = _ => destruct b eqn:?; try discriminate H
         | (let _ := ?x in _) = _ => cbv zeta in H
         end;
  injection H as <- _; (destruct (0 <? n); [apply cview_paint| reflexivity]).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma zidx_inj : forall c c', 0 <= c -> 0 <= c' -> zidx c = zidx c' -> c = c'.
Proof. intros c c' Hc Hc' E. unfold zidx in E. lia. Qed.

Lemma get_region_set_region_eq : forall st c r, length (as_regions st) = 32%nat -> 0 <= c < kNumClasses -> get_region (set_region st c r) c = r.
Proof. intros st c r LENR Hc. unfold get_region, set_region. cbn [as_regions]. apply znth_upd_nth_eq. rewrite LENR. unfold kNumClasses in Hc. unfold zidx. lia. Qed.
Lemma get_region_set_region_neq : forall st c c' r, 0 <= c -> 0 <= c' -> c' <> c -> get_region (set_region st c r) c' = get_region st c'.
Proof. intros st c c' r Hc Hc' NE. unfold get_region, set_region. cbn [as_regions]. apply znth_upd_nth_neq. intros E. apply NE. symmetry. exact (zidx_inj _ _ Hc Hc' E). Qed.
Lemma get_pc_set_pc_eq : forall st c p, length (as_cache st) = 32%nat -> 0 <= c < kNumClasses -> get_pc (set_pc st c p) c = p.
Proof. intros st c p LENC Hc. unfold get_pc, set_pc. cbn [as_cache]. apply znth_upd_nth_eq. rewrite LENC. unfold kNumClasses in Hc. unfold zidx. lia. Qed.
Lemma get_pc_set_pc_neq : forall st c c' p, 0 <= c -> 0 <= c' -> c' <> c -> get_pc (set_pc st c p) c' = get_pc st c'.
Proof. intros st c c' p Hc Hc' NE. unfold get_pc, set_pc. cbn [as_cache]. apply znth_upd_nth_neq. intros E. apply NE. symmetry. exact (zidx_inj _ _ Hc Hc' E). Qed.
(* [comment removed for export] *)
Lemma get_pc_set_region : forall st c c' r, get_pc (set_region st c r) c' = get_pc st c'.            Proof. reflexivity. Qed.
Lemma get_region_set_pc : forall st c c' p, get_region (set_pc st c p) c' = get_region st c'.        Proof. reflexivity. Qed.
Lemma chunk_list_set_region : forall st c r, chunk_list (set_region st c r) = chunk_list st.         Proof. reflexivity. Qed.
Lemma chunk_list_set_pc : forall st c p, chunk_list (set_pc st c p) = chunk_list st.                 Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma chunk_list_remove_iff : forall st u x,
  In x (chunk_list (set_chunks st (remove_chunk (as_chunks st) u))) <-> In x (chunk_list st) /\ (exists k, PositiveMap.find k (as_chunks st) = Some x /\ k <> ckey u).
Proof.
  intros st u x. rewrite !chunk_list_in_iff. unfold set_chunks, remove_chunk. cbn [as_chunks]. split.
  - intros [k F]. destruct (PositiveMap.E.eq_dec k (ckey u)) as [->|NE].
    + rewrite PositiveMap.grs in F. discriminate F.
    + rewrite PositiveMap.gro in F by exact NE. split; [exists k; exact F| exists k; split; [exact F| exact NE]].
  - intros [_ (k & F & NE)]. exists k. rewrite PositiveMap.gro by exact NE. exact F.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma COMPLETE_transfer : forall st st' X X',
  as_space_beg st' = as_space_beg st ->
  (forall c, 1 <= c < kNumClasses -> ncarved st' c = ncarved st c) ->
  (forall c x, 1 <= c < kNumClasses -> In x (owners st X c) -> In x (owners st' X' c)) ->
  COMPLETE st X -> COMPLETE st' X'.
Proof.
  intros st st' X X' SB NC INC CO c Hc i Hi. rewrite (NC c Hc) in Hi.
  replace (slot st' c i) with (slot st c i) by (unfold slot, region_beg; rewrite SB; reflexivity).
  apply (INC c _ Hc). exact (CO c Hc i Hi).
Qed.

(* [comment removed for export] *)
Lemma In_owners : forall st X c x,
  In x (owners st X c) <->
  In x (own_free st c) \/ In x (own_cache st c) \/ In x (own_chunk st c) \/ In x (own_batch st c) \/ In x (X c).
Proof. intros. unfold owners. rewrite !in_app_iff. tauto. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition same_core (a b : astate) : Prop :=
  as_space_beg a = as_space_beg b /\ as_ptr_array a = as_ptr_array b /\ as_regions a = as_regions b /\ as_cache_inited a = as_cache_inited b
  /\ as_cache a = as_cache b /\ as_n_reserved a = as_n_reserved b /\ as_sec a = as_sec b /\ as_chunks a = as_chunks b /\ as_tq a = as_tq b
  /\ as_gq a = as_gq b /\ as_internal_init a = as_internal_init b
  /\ as_qmax a = as_qmax b /\ as_qmin a = as_qmin b /\ as_qcache a = as_qcache b.
Lemma same_core_refl : forall a, same_core a a. Proof. intros; repeat split; reflexivity. Qed.
Lemma same_core_trans : forall a b c, same_core a b -> same_core b c -> same_core a c.
Proof. intros a b c H1 H2. unfold same_core in *. intuition congruence. Qed.
Lemma same_core_sbs : forall a b, same_but_shadow a b -> same_core a b.
Proof. intros a b H. unfold same_but_shadow, same_core in *. intuition. Qed.
Lemma same_core_add_map : forall st m, same_core (add_map st m) st. Proof. intros; repeat split; reflexivity. Qed.
Lemma same_core_remove_map : forall st b, same_core (remove_map st b) st. Proof. intros; repeat split; reflexivity. Qed.
Lemma same_core_paint : forall st lo hi v, same_core (paint st lo hi v) st. Proof. intros; repeat split; reflexivity. Qed.
Lemma same_core_cview : forall a b, same_core a b -> cview a = cview b.
Proof. intros a b H. unfold same_core in H. unfold cview. destruct H as (E1 & _ & E3 & _ & E5 & _ & _ & E8 & E9 & E10 & _). rewrite E1, E3, E5, E8, E9, E10. reflexivity. Qed.
Lemma same_core_set_region : forall a b c r, same_core a b -> same_core (set_region a c r) (set_region b c r).
Proof. intros a b c r H. unfold same_core in *. unfold set_region. cbn. intuition congruence. Qed.
Lemma same_core_set_pc : forall a b c p, same_core a b -> same_core (set_pc a c p) (set_pc b c p).
Proof. intros a b c p H. unfold same_core in *. unfold set_pc. cbn. intuition congruence. Qed.

Lemma poison_shadow_core : forall st a n v st' ev, poison_shadow st a n v = Some (st', ev) -> same_core st' st.
Proof.
  intros st a n v st' ev H. unfold poison_shadow in H.
  repeat match type of H with
         | (if ?b then _ else _) = _ => destruct b eqn:?; try discriminate H
         | (let _ := ?x in _) = _ => cbv zeta in H
         end;
  injection H as <- _; (destruct (0 <? n); [apply same_core_paint| apply same_core_refl]).
Qed.


Lemma map_upd_nth {A B} : forall (f : A -> B) l i x, map f (upd_nth l i x) = upd_nth (map f l) i (f x).
Proof. intros f l. induction l as [|y l IH]; intros [|i] x; cbn; try reflexivity. now rewrite IH. Qed.
Lemma upd_nth_znth {A} : forall (l : list A) i d, upd_nth l i (znth l i d) = l.
Proof. induction l as [|y l IH]; intros [|i] d; cbn; try reflexivity. now rewrite IH. Qed.
Lemma upd_nth_upd_nth {A} : forall (l : list A) i x y, upd_nth (upd_nth l i x) i y = upd_nth l i y.
Proof. induction l as [|z l IH]; intros [|i] x y; cbn; try reflexivity. now rewrite IH. Qed.
Lemma cview_set_region_keep : forall st c r,
  rview r = rview (get_region st c) -> cview (set_region st c r) = cview st.
Proof.
  intros st c r E. unfold cview, set_region. cbn. rewrite map_upd_nth, E. unfold get_region. rewrite <- (znth_map rview). rewrite upd_nth_znth. reflexivity.
Qed.
Lemma set_region_set_region : forall st c r r', set_region (set_region st c r) c r' = set_region st c r'.
Proof. intros. unfold set_region. cbn. rewrite upd_nth_upd_nth. reflexivity. Qed.
Lemma cview_set_region_cong : forall a b c r, cview a = cview b -> cview (set_region a c r) = cview (set_region b c r).
Proof.
  intros a b c r E. unfold cview in *. unfold set_region. cbn. rewrite !map_upd_nth.
  assert (M : map rview (as_regions a) = map rview (as_regions b)) by congruence. rewrite M.
  assert (SB : as_space_beg a = as_space_beg b) by congruence.
  assert (CA : as_cache a = as_cache b) by congruence. assert (CH : as_chunks a = as_chunks b) by congruence.
  assert (TQ : as_tq a = as_tq b) by congruence. assert (GQ : as_gq a = as_gq b) by congruence.
  rewrite SB, CA, CH, TQ, GQ. reflexivity.
Qed.
Lemma set_region_same : forall st c, set_region st c (get_region st c) = st.
Proof. intros st c. destruct st. unfold set_region, get_region. cbn. rewrite upd_nth_znth. reflexivity. Qed.

(* [comment removed for export] *)
Lemma ensure_free_array_space_shape : forall st c n st2 ev,
  ensure_free_array_space st c n = Some (st2, ev) ->
  let r := get_region st c in
  exists st1 r', same_core st1 st /\ st2 = set_region st1 c r'
    /\ rg_mapped_user r' = rg_mapped_user r /\ rg_allocated_user r' = rg_allocated_user r /\ rg_num_freed r' = rg_num_freed r
    /\ rg_free_array r' = rg_free_array r
    /\ (rg_mapped_free_array r' = rg_mapped_free_array r
        \/ (rg_mapped_free_array r < 4 * n /\ rg_mapped_free_array r' = round_up (4 * n) kFreeArrayMapSize /\ rg_mapped_free_array r' <= kFreeArraySize)).
Proof.
  intros st c n st2 ev H r. unfold ensure_free_array_space in H. fold r in H.
  destruct (n * 4 <=? rg_mapped_free_array r) eqn:LE.
  - injection H as <- _. exists st, r. rewrite set_region_same. split; [apply same_core_refl|]. repeat split; try reflexivity. left; reflexivity.
  - destruct (kFreeArraySize <? round_up (n * 4) kFreeArrayMapSize) eqn:OV; [discriminate H|].
    unfold map_fixed in H.
    destruct (poison_shadow _ _ _ _) as [[stp evp]|] eqn:PS; [| discriminate H].
    injection H as <- _. pose proof (poison_shadow_core _ _ _ _ _ _ PS) as CV.
    eexists stp, _. split; [exact (same_core_trans _ _ _ CV (same_core_add_map _ _))|]. split; [reflexivity|].
    cbn [rg_mapped_user rg_allocated_user rg_num_freed rg_free_array rg_mapped_free_array]. repeat split; try reflexivity. right.
    apply Z.leb_gt in LE. apply Z.ltb_ge in OV. rewrite (Z.mul_comm 4 n). lia.
Qed.

Lemma same_core_set_region_l : forall a b c r r', same_core a (set_region b c r) -> same_core (set_region a c r') (set_region b c r').
Proof. intros a b c r r' H. eapply same_core_trans; [apply same_core_set_region; exact H|]. rewrite set_region_set_region. apply same_core_refl. Qed.

Lemma ensure_free_array_space_core : forall st c n st2 ev,
  ensure_free_array_space st c n = Some (st2, ev) ->
  let r := get_region st c in
  exists mfa', same_core st2 (set_region st c (mkRegion (rg_mapped_user r) (rg_allocated_user r) (rg_num_freed r) (rg_free_array r) mfa'))
    /\ (mfa' = rg_mapped_free_array r
        \/ (rg_mapped_free_array r < 4 * n /\ mfa' = round_up (4 * n) kFreeArrayMapSize /\ mfa' <= kFreeArraySize)).
Proof.
  intros st c n st2 ev H r.
  destruct (ensure_free_array_space_shape st c n st2 ev H) as (st1 & r' & C1 & -> & M1 & M2 & M3 & M4 & M5). fold r in M1, M2, M3, M4, M5.
  exists (rg_mapped_free_array r'). split; [| exact M5].
  replace r' with (mkRegion (rg_mapped_user r) (rg_allocated_user r) (rg_num_freed r) (rg_free_array r) (rg_mapped_free_array r')) at 1
    by (destruct r'; cbn in *; subst; reflexivity).
  apply same_core_set_region. exact C1.
Qed.

Lemma get_region_core_set : forall a b c r, same_core a (set_region b c r) -> length (as_regions b) = 32%nat -> 0 <= c < kNumClasses ->
  get_region a c = r.
Proof.
  intros a b c r C L Hc. destruct C as (_ & _ & E & _). unfold get_region. rewrite E. apply get_region_set_region_eq; assumption.
Qed.
Lemma same_core_len_regions : forall a b, same_core a b -> length (as_regions a) = length (as_regions b).
Proof. intros a b C. destruct C as (_ & _ & E & _). rewrite E. reflexivity. Qed.
Lemma length_regions_set_region : forall st c r, length (as_regions (set_region st c r)) = length (as_regions st).
Proof. intros. unfold set_region. cbn. apply length_upd_nth. Qed.

Lemma populate_free_array_core : forall st c req st' ev,
  length (as_regions st) = 32%nat -> 0 <= c < kNumClasses ->
  populate_free_array st c req = Some (st', ev) ->
  let r := get_region st c in let s := class_size c in
  exists mu' mfa',
    let new := (mu' - rg_allocated_user r) / s in
    same_core st' (set_region st c (mkRegion mu' (rg_allocated_user r + new * s) (rg_num_freed r + new)
                                              (carve_asc (rg_allocated_user r) s 0 (Z.to_nat new) ++ rg_free_array r) mfa'))
    /\ rg_mapped_user r <= mu' /\ rg_allocated_user r + new * s <= mu'
    /\ (mu' = rg_mapped_user r \/ (rg_mapped_user r < rg_allocated_user r + req * s
                                   /\ mu' = rg_mapped_user r + round_up (rg_allocated_user r + req * s - rg_mapped_user r) kUserMapSize
                                   /\ mu' <= kFreeArrayOffset))
    /\ (mfa' = rg_mapped_free_array r
        \/ (rg_mapped_free_array r < 4 * (rg_num_freed r + new) /\ mfa' = round_up (4 * (rg_num_freed r + new)) kFreeArrayMapSize /\ mfa' <= kFreeArraySize)).
Proof.
  intros st c req st' ev LENR Hc H r s. unfold populate_free_array in H. fold r s in H.
  set (total := rg_allocated_user r + req * s) in H.
  (* [comment removed for export] *)
  assert (S1 : exists st1 mu', same_core st1 (set_region st c (mkRegion mu' (rg_allocated_user r) (rg_num_freed r) (rg_free_array r) (rg_mapped_free_array r)))
            /\ rg_mapped_user r <= mu'
            /\ (mu' = rg_mapped_user r \/ (rg_mapped_user r < total /\ mu' = rg_mapped_user r + round_up (total - rg_mapped_user r) kUserMapSize /\ mu' <= kFreeArrayOffset))
            /\ match (let r1 := mkRegion mu' (rg_allocated_user r) (rg_num_freed r) (rg_free_array r) (rg_mapped_free_array r) in
                      let new_chunks := (rg_mapped_user r1 - rg_allocated_user r1) / s in
                      let total_freed := rg_num_freed r1 + new_chunks in
                      match ensure_free_array_space st1 c total_freed with
                      | None => None
                      | Some (st2, ev2) =>
                          let r2 := get_region st2 c in
                          let seg := carve_asc (rg_allocated_user r2) s 0 (Z.to_nat new_chunks) in
                          let r3 := mkRegion (rg_mapped_user r2) (rg_allocated_user r2 + new_chunks * s) total_freed (seg ++ rg_free_array r2) (rg_mapped_free_array r2) in
                          if rg_mapped_user r3 <? rg_allocated_user r3 then None else Some (set_region st2 c r3)
                      end) with Some stx => st' = stx | None => False end).
  { destruct (total <=? rg_mapped_user r) eqn:T1.
    - exists st, (rg_mapped_user r). split.
      { replace (mkRegion _ _ _ _ _) with r by (destruct r; reflexivity). rewrite set_region_same. apply same_core_refl. }
      split; [lia|]. split; [left; reflexivity|].
      replace (mkRegion _ _ _ _ _) with r by (destruct r; reflexivity). cbv zeta in H |- *.
      destruct (ensure_free_array_space st c _) as [[st2 ev2]|]; [| discriminate H].
      destruct (_ <? _); [discriminate H|]. injection H as <- _. reflexivity.
    - cbv zeta in H.
      destruct (kFreeArrayOffset <? rg_mapped_user r + 0 + round_up (total - rg_mapped_user r) kUserMapSize) eqn:EX; [discriminate H|].
      unfold map_fixed in H. destruct (poison_shadow _ _ _ _) as [[stp evp]|] eqn:PS; [| discriminate H].
      exists (set_region stp c (mkRegion (rg_mapped_user r + round_up (total - rg_mapped_user r) kUserMapSize) (rg_allocated_user r) (rg_num_freed r) (rg_free_array r) (rg_mapped_free_array r))),
             (rg_mapped_user r + round_up (total - rg_mapped_user r) kUserMapSize).
      split. { apply same_core_set_region. eapply same_core_trans; [exact (poison_shadow_core _ _ _ _ _ _ PS)| apply same_core_add_map]. }
      apply Z.leb_gt in T1. apply Z.ltb_ge in EX.
      split; [unfold round_up, kUserMapSize; Z.div_mod_to_equations; lia|]. split; [right; repeat split; lia|].
      cbv zeta in H |- *. cbn [rg_mapped_user rg_allocated_user rg_num_freed rg_free_array rg_mapped_free_array] in H |- *.
      destruct (ensure_free_array_space _ c _) as [[st2 ev2]|]; [| discriminate H].
      destruct (_ <? _); [discriminate H|]. injection H as <- _. reflexivity. }
  clear H. destruct S1 as (st1 & mu' & C1 & LE1 & MU1 & REST). cbv zeta in REST.
  cbn [rg_mapped_user rg_allocated_user rg_num_freed rg_free_array rg_mapped_free_array] in REST.
  destruct (ensure_free_array_space st1 c _) as [[st2 ev2]|] eqn:EN; [| destruct REST].
  destruct (ensure_free_array_space_core st1 c _ st2 ev2 EN) as (mfa' & C2 & MFA).
  assert (L1 : length (as_regions st1) = 32%nat) by (rewrite (same_core_len_regions _ _ C1), length_regions_set_region; exact LENR).
  pose proof (get_region_core_set _ _ _ _ C1 LENR Hc) as G1. rewrite G1 in C2, MFA.
  cbn [rg_mapped_user rg_allocated_user rg_num_freed rg_free_array rg_mapped_free_array] in C2, MFA.
  pose proof (get_region_core_set _ _ _ _ C2 L1 Hc) as G2. rewrite G2 in REST.
  cbn [rg_mapped_user rg_allocated_user rg_num_freed rg_free_array rg_mapped_free_array] in REST.
  destruct (mu' <? rg_allocated_user r + (mu' - rg_allocated_user r) / s * s) eqn:CHK; [destruct REST|]. subst st'.
  exists mu', mfa'. cbv zeta. split.
  { eapply same_core_trans; [apply (same_core_set_region_l _ _ _ _ _ C2)|]. apply (same_core_set_region_l _ _ _ _ _ C1). }
  apply Z.ltb_ge in CHK. split; [exact LE1|]. split; [lia|]. split; [exact MU1| exact MFA].
Qed.

Lemma get_from_allocator_core : forall st c n st' taken ev,
  get_from_allocator st c n = Some (st', taken, ev) ->
  exists st1, (st1 = st /\ n <= rg_num_freed (get_region st c)
               \/ (rg_num_freed (get_region st c) < n /\ exists ev1, populate_free_array st c (n - rg_num_freed (get_region st c)) = Some (st1, ev1)
                   /\ n <= rg_num_freed (get_region st1 c)))
   /\ let r1 := get_region st1 c in
      taken = firstn (Z.to_nat n) (rg_free_array r1)
   /\ st' = set_region st1 c (mkRegion (rg_mapped_user r1) (rg_allocated_user r1) (rg_num_freed r1 - n) (skipn (Z.to_nat n) (rg_free_array r1)) (rg_mapped_free_array r1)).
Proof.
  intros st c n st' taken ev H. unfold get_from_allocator in H.
  destruct (rg_num_freed (get_region st c) <? n) eqn:LT.
  - apply Z.ltb_lt in LT. destruct (populate_free_array st c _) as [[st1 ev1]|] eqn:P; [| discriminate H].
    destruct (rg_num_freed (get_region st1 c) <? n) eqn:LT2; [discriminate H|]. apply Z.ltb_ge in LT2.
    injection H as <- <- _. exists st1. split; [right; split; [exact LT| exists ev1; split; [reflexivity| exact LT2]]|]. split; reflexivity.
  - apply Z.ltb_ge in LT. injection H as <- <- _. exists st. split; [left; split; [reflexivity| exact LT]|]. split; reflexivity.
Qed.

Lemma cache_alloc_core : forall st c st' a ev,
  cache_alloc st c = Some (st', a, ev) ->
  (c <> 0 /\ c < kNumClasses) /\
  exists st1 pc1 cp rest,
     ((pc_count (get_pc st c) = 0 /\ exists taken ev', get_from_allocator (ensure_cache_inited st) c (max_count c / 2) = Some (st1, taken, ev')
                                   /\ pc1 = mkPC (max_count c / 2) taken)
      \/ (pc_count (get_pc st c) <> 0 /\ st1 = st /\ pc1 = get_pc st c))
  /\ pc_chunks pc1 = cp :: rest
  /\ st' = set_pc st1 c (mkPC (pc_count pc1 - 1) rest)
  /\ a = compact_to_addr st' c cp.
Proof.
  intros st c st' a ev H. unfold cache_alloc in H.
  destruct ((c =? 0) || (kNumClasses <=? c)) eqn:C0; [discriminate H|].
  apply Bool.orb_false_iff in C0. destruct C0 as [C0 C1]. apply Z.eqb_neq in C0. apply Z.leb_gt in C1.
  split; [exact (conj C0 C1)|].
  destruct (pc_count (get_pc st c) =? 0) eqn:PZ.
  - apply Z.eqb_eq in PZ. destruct (get_from_allocator _ c _) as [[[st2 taken] ev2]|] eqn:G; [| discriminate H].
    cbn [pc_chunks pc_count] in H. destruct taken as [|cp rest]; [discriminate H|]. injection H as <- <- _.
    exists st2, (mkPC (max_count c / 2) (cp :: rest)), cp, rest. split; [left; split; [exact PZ| exists (cp :: rest), ev2; split; reflexivity]|].
    split; [reflexivity|]. split; reflexivity.
  - apply Z.eqb_neq in PZ. destruct (pc_chunks (get_pc st c)) as [|cp rest] eqn:PC; [discriminate H|]. injection H as <- <- _.
    exists st, (get_pc st c), cp, rest. split; [right; split; [exact PZ| split; reflexivity]|]. rewrite PC. split; [reflexivity|]. split; reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma own_free_set_region_eq : forall st c r, length (as_regions st) = 32%nat -> 0 <= c < kNumClasses ->
  own_free (set_region st c r) c = map (compact_to_addr st c) (rg_free_array r).
Proof. intros st c r L Hc. unfold own_free. rewrite (get_region_set_region_eq st c r L Hc). reflexivity. Qed.
Lemma own_free_set_region_neq : forall st c c' r, 0 <= c -> 0 <= c' -> c' <> c -> own_free (set_region st c r) c' = own_free st c'.
Proof. intros st c c' r Hc Hc' NE. unfold own_free. rewrite (get_region_set_region_neq st c c' r Hc Hc' NE). reflexivity. Qed.
Lemma own_cache_set_region : forall st c c' r, own_cache (set_region st c r) c' = own_cache st c'.   Proof. reflexivity. Qed.
Lemma own_chunk_set_region : forall st c c' r, own_chunk (set_region st c r) c' = own_chunk st c'.   Proof. reflexivity. Qed.
Lemma own_batch_set_region : forall st c c' r, own_batch (set_region st c r) c' = own_batch st c'.   Proof. reflexivity. Qed.
Lemma ncarved_set_region_eq : forall st c r, length (as_regions st) = 32%nat -> 0 <= c < kNumClasses ->
  ncarved (set_region st c r) c = rg_allocated_user r / class_size c.
Proof. intros st c r L Hc. unfold ncarved. rewrite (get_region_set_region_eq st c r L Hc). reflexivity. Qed.
Lemma ncarved_set_region_neq : forall st c c' r, 0 <= c -> 0 <= c' -> c' <> c -> ncarved (set_region st c r) c' = ncarved st c'.
Proof. intros st c c' r Hc Hc' NE. unfold ncarved. rewrite (get_region_set_region_neq st c c' r Hc Hc' NE). reflexivity. Qed.
Lemma own_cache_set_pc_eq : forall st c p, length (as_cache st) = 32%nat -> 0 <= c < kNumClasses ->
  own_cache (set_pc st c p) c = map (compact_to_addr st c) (pc_chunks p).
Proof. intros st c p L Hc. unfold own_cache. rewrite (get_pc_set_pc_eq st c p L Hc). reflexivity. Qed.
Lemma own_cache_set_pc_neq : forall st c c' p, 0 <= c -> 0 <= c' -> c' <> c -> own_cache (set_pc st c p) c' = own_cache st c'.
Proof. intros st c c' p Hc Hc' NE. unfold own_cache. rewrite (get_pc_set_pc_neq st c c' p Hc Hc' NE). reflexivity. Qed.
Lemma own_free_set_pc : forall st c c' p, own_free (set_pc st c p) c' = own_free st c'.     Proof. reflexivity. Qed.
Lemma own_chunk_set_pc : forall st c c' p, own_chunk (set_pc st c p) c' = own_chunk st c'.   Proof. reflexivity. Qed.
Lemma own_batch_set_pc : forall st c c' p, own_batch (set_pc st c p) c' = own_batch st c'.   Proof. reflexivity. Qed.
Lemma ncarved_set_pc : forall st c c' p, ncarved (set_pc st c p) c' = ncarved st c'.         Proof. reflexivity. Qed.

Lemma carve_asc_In : forall k base s i x,
  In x (carve_asc base s i k) <-> exists j, 0 <= j < Z.of_nat k /\ x = Z.shiftr (base + (i + j) * s) kCompactPtrScale.
Proof.
  induction k as [|k IH]; intros base s i x; cbn [carve_asc].
  - split; [intros []| intros (j & Hj & _); lia].
  - rewrite Nat2Z.inj_succ. split.
    + intros [<-|H]; [exists 0; split; [lia| f_equal; f_equal; lia]|].
      apply IH in H. destruct H as (j & Hj & ->). exists (j + 1). split; [lia| f_equal; f_equal; lia].
    + intros (j & Hj & ->). destruct (Z.eq_dec j 0) as [->|NZ]; [left; f_equal; f_equal; lia| right].
      apply IH. exists (j - 1). split; [lia| f_equal; f_equal; lia].
Qed.
Lemma carve_asc_length : forall k base s i, length (carve_asc base s i k) = k.
Proof. induction k; intros; cbn; [reflexivity| now rewrite IHk]. Qed.

Lemma shiftr4_shiftl4 : forall x, 0 <= x -> x mod 16 = 0 -> Z.shiftl (Z.shiftr x kCompactPtrScale) kCompactPtrScale = x.
Proof.
  intros x Hx Hm. unfold kCompactPtrScale. rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia. change (2 ^ 4) with 16. Z.div_mod_to_equations. lia.
Qed.
Lemma compact_to_addr_carved : forall st c au j s, 0 <= au -> 0 <= j -> 0 < s -> au mod s = 0 -> s mod 16 = 0 ->
  compact_to_addr st c (Z.shiftr (au + (0 + j) * s) kCompactPtrScale) = region_beg st c + au + j * s.
Proof.
  intros st c au j s Hau Hj Hs Hm Hs16. unfold compact_to_addr. rewrite shiftr4_shiftl4; [lia| nia|].
  rewrite Z.add_0_l. rewrite Z.add_mod, Z.mul_mod, Hs16, Z.mul_0_r, Z.mod_0_l, Z.add_0_r by lia.
  replace (au mod 16) with 0; [reflexivity|]. symmetry. Z.div_mod_to_equations. nia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition xadd (X : Z -> list Z) (c a : Z) : Z -> list Z := fun c' => if c' =? c then a :: X c' else X c'.
Definition xdel (X : Z -> list Z) (c a : Z) : Z -> list Z := fun c' => if c' =? c then remove Z.eq_dec a (X c') else X c'.

Lemma In_map_cta_app : forall st c l1 l2 x, In x (map (compact_to_addr st c) (l1 ++ l2)) <-> In x (map (compact_to_addr st c) l1) \/ In x (map (compact_to_addr st c) l2).
Proof. intros. rewrite map_app, in_app_iff. tauto. Qed.

(* [comment removed for export] *)
Lemma populate_complete : forall st X c req st0 ev,
  length (as_regions st) = 32%nat -> 1 <= c < kNumClasses ->
  0 <= rg_allocated_user (get_region st c) <= rg_mapped_user (get_region st c) -> rg_allocated_user (get_region st c) mod class_size c = 0 ->
  0 < class_size c -> class_size c mod 16 = 0 ->
  COMPLETE st X -> populate_free_array st c req = Some (st0, ev) ->
  COMPLETE st0 X
  /\ (exists new, 0 <= new /\ ncarved st0 c = ncarved st c + new
        /\ rg_allocated_user (get_region st0 c) = rg_allocated_user (get_region st c) + new * class_size c
        /\ rg_mapped_user (get_region st c) <= rg_mapped_user (get_region st0 c)
        /\ rg_allocated_user (get_region st0 c) <= rg_mapped_user (get_region st0 c)
        /\ (rg_mapped_user (get_region st0 c) = rg_mapped_user (get_region st c)
            \/ (rg_mapped_user (get_region st c) < rg_allocated_user (get_region st c) + req * class_size c
                /\ rg_mapped_user (get_region st0 c) = rg_mapped_user (get_region st c)
                     + round_up (rg_allocated_user (get_region st c) + req * class_size c - rg_mapped_user (get_region st c)) kUserMapSize
                /\ rg_mapped_user (get_region st0 c) <= kFreeArrayOffset))
        /\ (rg_mapped_free_array (get_region st0 c) = rg_mapped_free_array (get_region st c)
            \/ (rg_mapped_free_array (get_region st0 c) = round_up (4 * rg_num_freed (get_region st0 c)) kFreeArrayMapSize
                /\ rg_mapped_free_array (get_region st0 c) <= kFreeArraySize))
        /\ rg_num_freed (get_region st0 c) = rg_num_freed (get_region st c) + new)
  /\ (forall c', 0 <= c' -> c' <> c -> ncarved st0 c' = ncarved st c' /\ get_region st0 c' = get_region st c')
  /\ as_cache st0 = as_cache st /\ as_space_beg st0 = as_space_beg st /\ length (as_regions st0) = 32%nat /\ length (as_cache st0) = length (as_cache st)
  /\ as_chunks st0 = as_chunks st /\ as_tq st0 = as_tq st /\ as_gq st0 = as_gq st /\ as_sec st0 = as_sec st.
Proof.
  intros st X c req st0 ev LENR Hc [AU0 AU1] AUM Hs Hs16 CO P.
  destruct (populate_free_array_core st c req st0 ev LENR ltac:(lia) P) as (mu' & mfa' & C0 & LE1 & LE2 & MU & MFA).
  cbv zeta in C0, LE2, MFA. set (r := get_region st c) in *. set (s := class_size c) in *.
  set (new := (mu' - rg_allocated_user r) / s) in *.
  assert (NEW0 : 0 <= new) by (subst new; apply Z.div_pos; lia).
  set (r3 := mkRegion mu' (rg_allocated_user r + new * s) (rg_num_freed r + new) (carve_asc (rg_allocated_user r) s 0 (Z.to_nat new) ++ rg_free_array r) mfa') in C0.
  pose proof (same_core_cview _ _ C0) as CV.
  assert (G0 : get_region st0 c = r3) by (apply (get_region_core_set _ _ _ _ C0 LENR); lia).
  destruct C0 as (SB0 & _ & RG0 & _ & CA0 & _ & SEC0 & CH0 & TQ0 & GQ0 & _).
  assert (LENR0 : length (as_regions st0) = 32%nat) by (rewrite RG0; unfold set_region; cbn; rewrite length_upd_nth; exact LENR).
  split.
  - (* [comment removed for export] *)
    apply (COMPLETE_view (set_region st c r3) st0 X (eq_sym CV)).
    intros c' Hc' i Hi. destruct (Z.eq_dec c' c) as [->|NE].
    + rewrite (ncarved_set_region_eq st c r3 LENR) in Hi by lia. subst r3. cbn [rg_allocated_user] in Hi.
      replace (slot (set_region st c _) c i) with (slot st c i) by reflexivity.
      unfold owners. rewrite (own_free_set_region_eq st c _ LENR) by lia. cbn [rg_free_array].
      rewrite own_cache_set_region, own_chunk_set_region, own_batch_set_region.
      rewrite Z.div_add in Hi by lia. fold (ncarved st c) in Hi.
      destruct (Z.lt_ge_cases i (ncarved st c)) as [OLD|NEWi].
      * pose proof (CO c Hc' i ltac:(lia)) as IN. unfold owners in IN. rewrite !in_app_iff in IN |- *. rewrite map_app, in_app_iff.
        unfold own_free in IN. fold r in IN. tauto.
      * rewrite !in_app_iff. left. rewrite map_app, in_app_iff. left.
        apply in_map_iff. exists (Z.shiftr (rg_allocated_user r + (0 + (i - ncarved st c)) * s) kCompactPtrScale). split.
        -- rewrite (compact_to_addr_carved st c (rg_allocated_user r) (i - ncarved st c) s AU0 ltac:(lia) Hs AUM Hs16).
           unfold slot, ncarved. fold r s. rewrite <- Z.add_assoc. f_equal.
           set (q := rg_allocated_user r / s) in *.
           assert (E : rg_allocated_user r = s * q) by (pose proof (Z.div_mod (rg_allocated_user r) s ltac:(lia)); lia).
           rewrite E. ring.
        -- apply carve_asc_In. exists (i - ncarved st c). rewrite Z2Nat.id by exact NEW0. unfold ncarved in NEWi, Hi |- *. fold r s in NEWi, Hi |- *. split; [lia| reflexivity].
    + assert (Hc'0 : 0 <= c') by lia.
      rewrite (ncarved_set_region_neq st c c' r3) in Hi by (first [clear - Hc Hc'0 NE; lia | lia]).
      replace (slot (set_region st c r3) c' i) with (slot st c' i) by reflexivity.
      unfold owners. rewrite (own_free_set_region_neq st c c' r3) by (first [clear - Hc Hc'0 NE; lia | lia]).
      rewrite own_cache_set_region, own_chunk_set_region, own_batch_set_region. exact (CO c' Hc' i Hi).
  - split.
    + exists new. rewrite G0. subst r3. cbn [rg_allocated_user rg_mapped_user rg_mapped_free_array rg_num_freed]. fold r.
      split; [exact NEW0|]. split.
      { unfold ncarved. rewrite G0. cbn [rg_allocated_user]. fold r s. rewrite Z.div_add by lia. reflexivity. }
      split; [reflexivity|]. split; [exact LE1|]. split; [exact LE2|]. split; [exact MU|]. split; [| reflexivity].
      destruct MFA as [E|(LT & E & B)]; [left; exact E| right; split; [exact E| exact B]].
    + split.
      { intros c' Hc'0 NE. unfold ncarved. rewrite <- (get_region_set_region_neq st c c' r3 ltac:(lia) Hc'0 NE).
        unfold get_region at 1 3. rewrite RG0. split; reflexivity. }
      rewrite CA0, SB0, CH0, TQ0, GQ0, SEC0. unfold set_region. cbn. repeat split; try reflexivity. exact LENR0.
Qed.

Lemma xadd_eq : forall X c a, xadd X c a c = a :: X c.
Proof. intros. unfold xadd. rewrite Z.eqb_refl. reflexivity. Qed.
Lemma xadd_neq : forall X c a c', c' <> c -> xadd X c a c' = X c'.
Proof. intros X c a c' NE. unfold xadd. destruct (Z.eqb_spec c' c); [contradiction| reflexivity]. Qed.

Lemma firstn_skipn_In {A} : forall (l : list A) k x, In x l <-> In x (firstn k l) \/ In x (skipn k l).
Proof. intros l k x. rewrite <- (firstn_skipn k l) at 1. rewrite in_app_iff. tauto. Qed.

(* [comment removed for export] *)
Lemma take_complete : forall st0 X c n cp rest cnt st',
  length (as_regions st0) = 32%nat -> length (as_cache st0) = 32%nat -> 1 <= c < kNumClasses ->
  pc_chunks (get_pc st0 c) = [] ->
  let r0 := get_region st0 c in
  cp :: rest = firstn (Z.to_nat n) (rg_free_array r0) ->
  st' = set_pc (set_region st0 c (mkRegion (rg_mapped_user r0) (rg_allocated_user r0) (rg_num_freed r0 - n) (skipn (Z.to_nat n) (rg_free_array r0)) (rg_mapped_free_array r0)))
               c (mkPC cnt rest) ->
  COMPLETE st0 X -> COMPLETE st' (xadd X c (compact_to_addr st0 c cp)).
Proof.
  intros st0 X c n cp rest cnt st' LENR LENC Hc PC0 r0 TK -> CO.
  set (r1 := mkRegion _ _ _ _ _).
  apply (COMPLETE_transfer st0 _ X); [reflexivity| | | exact CO].
  - intros c' Hc'. rewrite ncarved_set_pc. destruct (Z.eq_dec c' c) as [->|NE].
    + rewrite (ncarved_set_region_eq st0 c r1 LENR) by lia. reflexivity.
    + rewrite (ncarved_set_region_neq st0 c c' r1) by lia. reflexivity.
  - intros c' x Hc' IN. apply In_owners in IN. apply In_owners.
    rewrite own_free_set_pc, own_chunk_set_pc, own_batch_set_pc, own_chunk_set_region, own_batch_set_region.
    destruct (Z.eq_dec c' c) as [->|NE].
    + rewrite (own_cache_set_pc_eq (set_region st0 c r1) c _ ltac:(unfold set_region; cbn; exact LENC)) by lia. cbn [pc_chunks].
      rewrite (own_free_set_region_eq st0 c r1 LENR) by lia. replace (rg_free_array r1) with (skipn (Z.to_nat n) (rg_free_array r0)) by reflexivity. rewrite xadd_eq.
      replace (compact_to_addr (set_region st0 c r1) c) with (compact_to_addr st0 c) by reflexivity.
      destruct IN as [F|[C|[K|[B|XX]]]].
      * unfold own_free in F. fold r0 in F. rewrite <- (firstn_skipn (Z.to_nat n) (rg_free_array r0)) in F.
        rewrite map_app, in_app_iff, <- TK in F. cbn [map In] in F.
        destruct F as [[<-|R]|S]; [do 4 right; left; reflexivity| right; left; exact R| left; exact S].
      * unfold own_cache in C. rewrite PC0 in C. destruct C.
      * tauto.
      * tauto.
      * do 4 right. right. exact XX.
    + rewrite (own_cache_set_pc_neq (set_region st0 c r1) c c') by lia. rewrite own_cache_set_region.
      rewrite (own_free_set_region_neq st0 c c' r1) by lia. rewrite xadd_neq by exact NE. exact IN.
Qed.

(* [comment removed for export] *)
Lemma pop_complete : forall st X c cp rest cnt,
  length (as_cache st) = 32%nat -> 1 <= c < kNumClasses ->
  pc_chunks (get_pc st c) = cp :: rest ->
  COMPLETE st X -> COMPLETE (set_pc st c (mkPC cnt rest)) (xadd X c (compact_to_addr st c cp)).
Proof.
  intros st X c cp rest cnt LENC Hc PC CO.
  apply (COMPLETE_transfer st _ X); [reflexivity| intros; apply ncarved_set_pc| | exact CO].
  intros c' x Hc' IN. apply In_owners in IN. apply In_owners.
  rewrite own_free_set_pc, own_chunk_set_pc, own_batch_set_pc.
  destruct (Z.eq_dec c' c) as [->|NE].
  - rewrite (own_cache_set_pc_eq st c _ LENC) by lia. cbn [pc_chunks]. rewrite xadd_eq. cbn [In].
    destruct IN as [F|[C|[K|[B|XX]]]]; try tauto.
    unfold own_cache in C. rewrite PC in C. cbn [map In] in C. destruct C as [<-|C]; tauto.
  - rewrite (own_cache_set_pc_neq st c c') by lia. rewrite xadd_neq by exact NE. exact IN.
Qed.

Lemma get_pc_ensure_cache_inited : forall st c, get_pc (ensure_cache_inited st) c = get_pc st c.
Proof. intros. unfold ensure_cache_inited. destruct (as_cache_inited st); reflexivity. Qed.
Lemma get_region_ensure_cache_inited : forall st c, get_region (ensure_cache_inited st) c = get_region st c.
Proof. intros. unfold ensure_cache_inited. destruct (as_cache_inited st); reflexivity. Qed.
Lemma as_regions_eci : forall st, as_regions (ensure_cache_inited st) = as_regions st.
Proof. intros. unfold ensure_cache_inited. destruct (as_cache_inited st); reflexivity. Qed.
Lemma as_cache_eci : forall st, as_cache (ensure_cache_inited st) = as_cache st.
Proof. intros. unfold ensure_cache_inited. destruct (as_cache_inited st); reflexivity. Qed.
Lemma as_space_beg_eci : forall st, as_space_beg (ensure_cache_inited st) = as_space_beg st.
Proof. intros. unfold ensure_cache_inited. destruct (as_cache_inited st); reflexivity. Qed.

(* [comment removed for export] *)
Theorem cache_alloc_complete : forall st X c st' a ev,
  length (as_regions st) = 32%nat -> length (as_cache st) = 32%nat -> 0 <= c ->
  0 <= rg_allocated_user (get_region st c) <= rg_mapped_user (get_region st c) -> rg_allocated_user (get_region st c) mod class_size c = 0 ->
  0 < class_size c -> class_size c mod 16 = 0 ->
  pc_count (get_pc st c) = zlen (pc_chunks (get_pc st c)) ->
  COMPLETE st X -> cache_alloc st c = Some (st', a, ev) ->
  COMPLETE st' (xadd X c a).
Proof.
  intros st X c st' a ev LENR LENC C0 AU AUM Hs Hs16 CNT CO CA.
  destruct (cache_alloc_core st c st' a ev CA) as ([CN0 CLT] & st1 & pc1 & cp & rest & CASES & PC1 & -> & ->).
  assert (Hc : 1 <= c < kNumClasses) by lia.
  destruct CASES as [(PZ & taken & ev' & GFA & ->)|(PNZ & -> & ->)].
  - (* [comment removed for export] *)
    cbn [pc_chunks pc_count] in PC1 |- *. subst taken.
    assert (PCE : pc_chunks (get_pc st c) = []).
    { rewrite PZ in CNT. destruct (pc_chunks (get_pc st c)); [reflexivity| rewrite zlen_cons in CNT; unfold zlen in CNT; lia]. }
    destruct (get_from_allocator_core _ _ _ _ _ _ GFA) as (st0 & ALT & TK & ->). cbv zeta in TK.
    assert (F0 : COMPLETE st0 X /\ length (as_regions st0) = 32%nat /\ length (as_cache st0) = 32%nat /\ pc_chunks (get_pc st0 c) = []
                 /\ as_space_beg st0 = as_space_beg st).
    { destruct ALT as [[-> _]|(_ & ev1 & P & _)].
      - split; [apply (COMPLETE_view st); [symmetry; apply cview_ensure_cache_inited| exact CO]|].
        rewrite as_regions_eci, as_cache_eci, get_pc_ensure_cache_inited, as_space_beg_eci. repeat split; assumption.
      - destruct (populate_complete _ X _ _ _ _ ltac:(rewrite as_regions_eci; exact LENR) Hc
                    ltac:(rewrite get_region_ensure_cache_inited; exact AU) ltac:(rewrite get_region_ensure_cache_inited; exact AUM) Hs Hs16
                    ltac:(apply (COMPLETE_view st); [symmetry; apply cview_ensure_cache_inited| exact CO]) P)
          as (CO0 & _ & _ & CA0 & SB0 & LR0 & LC0 & _).
        split; [exact CO0|]. split; [exact LR0|]. rewrite as_cache_eci in LC0, CA0. rewrite as_space_beg_eci in SB0.
        split; [rewrite LC0; exact LENC|]. split; [| exact SB0]. unfold get_pc. rewrite CA0. fold (get_pc st c). exact PCE. }
    destruct F0 as (CO0 & LR0 & LC0 & PC0 & SB0).
    replace (compact_to_addr _ c cp) with (compact_to_addr st0 c cp) by reflexivity.
    eapply (take_complete st0 X c _ cp rest _ _ LR0 LC0 Hc PC0 TK); [reflexivity| exact CO0].
  - (* [comment removed for export] *)
    replace (compact_to_addr _ c cp) with (compact_to_addr st c cp) by reflexivity.
    apply pop_complete; assumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition fresh_key (st : astate) (u : Z) : Prop := PositiveMap.find (ckey u) (as_chunks st) = None.

Lemma chunk_list_upd_fresh : forall st ch x, fresh_key st (ch_user_beg ch) ->
  In x (chunk_list (upd_chunk st ch)) <-> x = ch \/ In x (chunk_list st).
Proof.
  intros st ch x FR. rewrite chunk_list_upd_iff, chunk_list_in_iff. split.
  - intros [->|(k & F & _)]; [left; reflexivity| right; exists k; exact F].
  - intros [->|(k & F)]; [left; reflexivity| right]. exists k. split; [exact F|]. intros ->. unfold fresh_key in FR. congruence.
Qed.

Lemma own_chunk_In : forall st c x, In x (own_chunk st c) <-> exists ch, In ch (chunk_list st) /\ ch_class ch = c /\ ch_alloc_beg ch = x.
Proof.
  intros st c x. unfold own_chunk. rewrite in_map_iff. split.
  - intros (ch & <- & IN). apply filter_In in IN. destruct IN as [IN E]. apply Z.eqb_eq in E. exists ch. repeat split; assumption.
  - intros (ch & IN & E & <-). exists ch. split; [reflexivity|]. apply filter_In. split; [exact IN| apply Z.eqb_eq; exact E].
Qed.

(* [comment removed for export] *)
Lemma upd_chunk_complete_absorb : forall st X c a ch,
  fresh_key st (ch_user_beg ch) -> ch_class ch = c -> ch_alloc_beg ch = a ->
  COMPLETE st (xadd X c a) -> COMPLETE (upd_chunk st ch) X.
Proof.
  intros st X c a ch FR CL AB CO.
  apply (COMPLETE_transfer st _ (xadd X c a)); [reflexivity| intros; reflexivity| | exact CO].
  intros c' x Hc' IN. apply In_owners in IN. apply In_owners.
  change (own_free (upd_chunk st ch) c') with (own_free st c'). change (own_cache (upd_chunk st ch) c') with (own_cache st c').
  change (own_batch (upd_chunk st ch) c') with (own_batch st c').
  assert (OC : forall y, In y (own_chunk st c') -> In y (own_chunk (upd_chunk st ch) c')).
  { intros y Hy. apply own_chunk_In in Hy. destruct Hy as (ch0 & IN0 & E0 & A0). apply own_chunk_In. exists ch0.
    split; [apply (chunk_list_upd_fresh st ch ch0 FR); right; exact IN0| split; assumption]. }
  destruct IN as [F|[C|[K|[B|XX]]]]; [tauto| tauto| right; right; left; apply OC; exact K| tauto|].
  unfold xadd in XX. destruct (Z.eqb_spec c' c) as [->|NE]; [| tauto].
  destruct XX as [<-|XX]; [| tauto]. right; right; left. apply own_chunk_In. exists ch.
  split; [apply (chunk_list_upd_fresh st ch ch FR); left; reflexivity| split; assumption].
Qed.

(* [comment removed for export] *)
Lemma upd_chunk_complete_fresh : forall st X ch,
  fresh_key st (ch_user_beg ch) -> COMPLETE st X -> COMPLETE (upd_chunk st ch) X.
Proof.
  intros st X ch FR CO.
  apply (COMPLETE_transfer st _ X); [reflexivity| intros; reflexivity| | exact CO].
  intros c' x Hc' IN. apply In_owners in IN. apply In_owners.
  change (own_free (upd_chunk st ch) c') with (own_free st c'). change (own_cache (upd_chunk st ch) c') with (own_cache st c').
  change (own_batch (upd_chunk st ch) c') with (own_batch st c').
  destruct IN as [F|[C|[K|[B|XX]]]]; [tauto| tauto| | tauto| tauto]. right; right; left.
  apply own_chunk_In in K. destruct K as (ch0 & IN0 & E0 & A0). apply own_chunk_In. exists ch0.
  split; [apply (chunk_list_upd_fresh st ch ch0 FR); right; exact IN0| split; assumption].
Qed.

(* [comment removed for export] *)
Lemma upd_chunk_complete_restate : forall st X ch ch0,
  keys_ok (as_chunks st) -> In ch0 (chunk_list st) -> ch_user_beg ch = ch_user_beg ch0 -> ch_class ch = ch_class ch0 -> ch_alloc_beg ch = ch_alloc_beg ch0 ->
  COMPLETE st X -> COMPLETE (upd_chunk st ch) X.
Proof.
  intros st X ch ch0 K IN0 U CL AB CO.
  apply (COMPLETE_transfer st _ X); [reflexivity| intros; reflexivity| | exact CO].
  intros c' x Hc' IN. apply In_owners in IN. apply In_owners.
  change (own_free (upd_chunk st ch) c') with (own_free st c'). change (own_cache (upd_chunk st ch) c') with (own_cache st c').
  change (own_batch (upd_chunk st ch) c') with (own_batch st c').
  destruct IN as [F|[C|[Kc|[B|XX]]]]; [tauto| tauto| | tauto| tauto]. right; right; left.
  apply own_chunk_In in Kc. destruct Kc as (ch1 & IN1 & E1 & A1). apply own_chunk_In.
  destruct (Z.eq_dec (ch_user_beg ch1) (ch_user_beg ch0)) as [EQ|NE].
  - (* [comment removed for export] *)
    assert (ch1 = ch0).
    { apply (chunk_list_find st ch1 K) in IN1. apply (chunk_list_find st ch0 K) in IN0. rewrite EQ in IN1. congruence. }
    subst ch1. exists ch. split; [apply chunk_list_upd_iff; left; reflexivity| split; congruence].
  - exists ch1. split; [| split; assumption]. apply chunk_list_upd_iff. right. exists (ckey (ch_user_beg ch1)).
    split; [apply (chunk_list_find st ch1 K); exact IN1|]. rewrite U. intros E. apply NE.
    destruct (K _ _ (proj1 (chunk_list_find st ch1 K) IN1)) as [_ P1]. destruct (K _ _ (proj1 (chunk_list_find st ch0 K) IN0)) as [_ P0].
    unfold ckey in E. apply Z2Pos.inj in E; [exact E| exact P1| exact P0].
Qed.

(* [comment removed for export] *)
Lemma remove_chunk_complete : forall st X ch,
  keys_ok (as_chunks st) -> In ch (chunk_list st) ->
  COMPLETE st X -> COMPLETE (set_chunks st (remove_chunk (as_chunks st) (ch_user_beg ch))) (xadd X (ch_class ch) (ch_alloc_beg ch)).
Proof.
  intros st X ch K IN0 CO.
  apply (COMPLETE_transfer st _ X); [reflexivity| intros; reflexivity| | exact CO].
  intros c' x Hc' IN. apply In_owners in IN. apply In_owners.
  change (own_free (set_chunks st _) c') with (own_free st c'). change (own_cache (set_chunks st _) c') with (own_cache st c').
  change (own_batch (set_chunks st _) c') with (own_batch st c').
  destruct IN as [F|[C|[Kc|[B|XX]]]]; [tauto| tauto| | tauto| do 4 right; unfold xadd; destruct (c' =? ch_class ch); [right|]; exact XX].
  apply own_chunk_In in Kc. destruct Kc as (ch1 & IN1 & E1 & A1).
  destruct (Z.eq_dec (ch_user_beg ch1) (ch_user_beg ch)) as [EQ|NE].
  - assert (ch1 = ch).
    { apply (chunk_list_find st ch1 K) in IN1. pose proof (proj1 (chunk_list_find st ch K) IN0) as F0. rewrite EQ in IN1. congruence. }
    subst ch1. do 4 right. unfold xadd. rewrite <- E1, Z.eqb_refl. left. exact A1.
  - right; right; left. apply own_chunk_In. exists ch1. split; [| split; assumption].
    apply chunk_list_remove_iff. split; [exact IN1|]. exists (ckey (ch_user_beg ch1)).
    split; [apply (chunk_list_find st ch1 K); exact IN1|]. intros E. apply NE.
    destruct (K _ _ (proj1 (chunk_list_find st ch1 K) IN1)) as [_ P1]. destruct (K _ _ (proj1 (chunk_list_find st ch K) IN0)) as [_ P0].
    unfold ckey in E. apply Z2Pos.inj in E; [exact E| exact P1| exact P0].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma populate_chunks : forall st c req st0 ev, length (as_regions st) = 32%nat -> 0 <= c < kNumClasses ->
  populate_free_array st c req = Some (st0, ev) -> as_chunks st0 = as_chunks st /\ as_space_beg st0 = as_space_beg st.
Proof.
  intros st c req st0 ev L Hc P. destruct (populate_free_array_core st c req st0 ev L Hc P) as (mu' & mfa' & C & _).
  destruct C as (SB & _ & _ & _ & _ & _ & _ & CH & _). rewrite SB, CH. split; reflexivity.
Qed.

Lemma cache_alloc_frame : forall st c st' a ev, length (as_regions st) = 32%nat -> 0 <= c ->
  cache_alloc st c = Some (st', a, ev) ->
  as_chunks st' = as_chunks st /\ as_space_beg st' = as_space_beg st /\ length (as_regions st') = 32%nat /\ length (as_cache st') = length (as_cache st)
  /\ as_tq st' = as_tq st /\ as_gq st' = as_gq st /\ as_sec st' = as_sec st /\ as_n_reserved st' = as_n_reserved st.
Proof.
  intros st c st' a ev L C0 CA.
  destruct (cache_alloc_core st c st' a ev CA) as ([CN0 CLT] & st1 & pc1 & cp & rest & CASES & PC1 & -> & ->).
  cbn [as_chunks as_space_beg as_regions as_cache as_tq as_gq as_sec as_n_reserved set_pc]. rewrite length_upd_nth.
  destruct CASES as [(PZ & taken & ev' & GFA & ->)|(PNZ & -> & ->)]; [| repeat split; try reflexivity; exact L].
  destruct (get_from_allocator_core _ _ _ _ _ _ GFA) as (st0 & ALT & TK & ->).
  cbn [as_chunks as_space_beg as_regions as_cache as_tq as_gq as_sec as_n_reserved set_region]. rewrite length_upd_nth.
  destruct ALT as [[-> _]|(_ & ev1 & P & _)].
  - unfold ensure_cache_inited. destruct (as_cache_inited st); cbn; repeat split; try reflexivity; exact L.
  - destruct (populate_free_array_core _ c _ st0 ev1 ltac:(rewrite as_regions_eci; exact L) ltac:(lia) P) as (mu' & mfa' & C & _).
    destruct C as (SB & _ & RG & _ & CAc & NR & SEC & CH & TQ & GQ & _). rewrite SB, RG, CAc, NR, SEC, CH, TQ, GQ.
    unfold set_region. cbn. rewrite length_upd_nth. unfold ensure_cache_inited. destruct (as_cache_inited st); cbn; repeat split; try reflexivity; exact L.
Qed.
Lemma cache_alloc_chunks : forall st c st' a ev, length (as_regions st) = 32%nat -> 0 <= c ->
  cache_alloc st c = Some (st', a, ev) -> as_chunks st' = as_chunks st /\ as_space_beg st' = as_space_beg st.
Proof. intros st c st' a ev L C0 CA. destruct (cache_alloc_frame st c st' a ev L C0 CA) as (A & B & _). exact (conj A B). Qed.

Lemma large_allocate_core : forall st needed k st' res ev,
  large_allocate st needed k = Some (st', res, ev) -> same_core st' (set_sec st (as_n_reserved st') (as_sec st')).
Proof.
  intros st needed k st' res ev H. unfold large_allocate in H. cbv zeta in H.
  destruct (_ <? needed); [discriminate H|]. destruct (negb _); [discriminate H|].
  destruct (poison_shadow (add_map st _) _ _ _) as [[st1 ev1]|] eqn:P1; [| discriminate H].
  destruct (poison_shadow st1 _ _ _) as [[st2 ev2]|] eqn:P2; [| discriminate H].
  destruct (_ <? _ + needed); [discriminate H|]. destruct (kMaxNumChunks <=? _); [discriminate H|].
  pose proof (same_core_trans _ _ _ (poison_shadow_core _ _ _ _ _ _ P2) (same_core_trans _ _ _ (poison_shadow_core _ _ _ _ _ _ P1) (same_core_add_map _ _))) as C2.
  destruct (zlen (as_sec st2) =? as_n_reserved st2).
  - unfold map_fixed in H. injection H as <- _ _. cbn [as_n_reserved as_sec set_sec].
    unfold same_core in *. unfold set_sec, add_map. cbn. intuition congruence.
  - injection H as <- _ _. cbn [as_n_reserved as_sec set_sec].
    unfold same_core in *. unfold set_sec. cbn. intuition congruence.
Qed.
Lemma cview_set_sec2 : forall st n l, cview (set_sec st n l) = cview st. Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition cons_pre (st : astate) (c : Z) : Prop :=
     length (as_regions st) = 32%nat /\ length (as_cache st) = 32%nat
  /\ 0 <= rg_allocated_user (get_region st c) <= rg_mapped_user (get_region st c)
  /\ rg_allocated_user (get_region st c) mod class_size c = 0
  /\ 0 < class_size c /\ class_size c mod 16 = 0
  /\ pc_count (get_pc st c) = zlen (pc_chunks (get_pc st c)).

Theorem am_malloc_k_complete : forall st X n k U st' ev,
  (forall c, 1 <= c < kNumClasses -> cons_pre st c) ->
  COMPLETE st X ->
  am_malloc_k st n k = Some (U, st', ev) ->
  fresh_key st U ->
  COMPLETE st' X.
Proof.
  intros st X n k U st' ev PRE CO H FR. unfold am_malloc_k in H.
  destruct (n <? 0) eqn:NNEG; [discriminate H|]. apply Z.ltb_ge in NNEG. destruct (size_too_big _); [discriminate H|]. cbv zeta in H.
  set (r := compute_req n) in *.
  (* [comment removed for export] *)
  match type of H with (match ?alloc with _ => _ end) = _ =>
    destruct alloc as [[[[st1 allocated] cls] ev1]|] eqn:AL; [| discriminate H] end.
  set (ch := mkChunk allocated (allocated + rq_rz r) (rq_size r) (rq_rz r) cls CAllocated) in H.
  destruct (allocated + rq_needed r <? allocated + rq_rz r + rq_size r); [discriminate H|].
  (* [comment removed for export] *)
  assert (POST : exists st5, cview st5 = cview (upd_chunk st1 ch) /\ st' = st5 /\ U = allocated + rq_rz r).
  { match type of H with (match ?s13 with _ => _ end) = _ => destruct s13 as [[st3 ev3]|] eqn:S13; [| discriminate H] end.
    assert (C3 : cview st3 = cview (upd_chunk st1 ch)).
    { destruct (negb (rq_primary r)).
      - destruct (actually_allocated_size _ _); [| discriminate S13].
        destruct (poison_shadow (upd_chunk st1 ch) _ _ _) as [[sa ea]|] eqn:PA; [| discriminate S13].
        destruct (poison_shadow sa _ _ _) as [[sb eb]|] eqn:PB; [| discriminate S13]. injection S13 as <- _.
        rewrite (same_core_cview _ _ (poison_shadow_core _ _ _ _ _ _ PB)). apply same_core_cview. exact (poison_shadow_core _ _ _ _ _ _ PA).
      - injection S13 as <- _. reflexivity. }
    match type of H with (match ?s14 with _ => _ end) = _ => destruct s14 as [[st4 ev4]|] eqn:S14; [| discriminate H] end.
    assert (C4 : cview st4 = cview st3).
    { destruct (0 <? _); [apply same_core_cview; exact (poison_shadow_core _ _ _ _ _ _ S14)| injection S14 as <- _; reflexivity]. }
    match type of H with (match ?s15 with _ => _ end) = _ => destruct s15 as [[st5 ev5]|] eqn:S15; [| discriminate H] end.
    assert (C5 : cview st5 = cview st4).
    { destruct (negb (rq_size r =? _)); [| injection S15 as <- _; reflexivity].
      destruct (negb (addr_is_in_mem _)); [discriminate S15|]. injection S15 as <- _. apply cview_paint. }
    destruct (negb _ && _); [discriminate H|]. injection H as <- <- _.
    exists st5. split; [congruence|]. split; reflexivity. }
  destruct POST as (st5 & C5 & -> & EU).
  apply (COMPLETE_view (upd_chunk st1 ch) st5 X (eq_sym C5)).
  (* [comment removed for export] *)
  destruct (kMaxSize <? rq_needed r) eqn:LARGE.
  - (* [comment removed for export] *)
    destruct (large_allocate st _ k) as [[[stL resL] evL]|] eqn:LA; [| discriminate AL]. injection AL as <- <- <- _.
    pose proof (large_allocate_core _ _ _ _ _ _ LA) as CL.
    apply upd_chunk_complete_fresh.
    + unfold fresh_key. subst ch. cbn [ch_user_beg]. destruct CL as (_ & _ & _ & _ & _ & _ & _ & CH & _). rewrite CH. cbn [as_chunks set_sec]. rewrite <- EU. exact FR.
    + apply (COMPLETE_view st); [| exact CO]. rewrite (same_core_cview _ _ CL). symmetry. apply cview_set_sec2.
  - (* [comment removed for export] *)
    destruct (cache_alloc st (class_id (rq_needed r))) as [[[stC aC] evC]|] eqn:CA; [| discriminate AL].
    injection AL as E1 E2 E3 E4. subst st1 allocated cls ev1.
    pose proof (cache_alloc_core _ _ _ _ _ CA) as ([CN0 CLT] & _).
    assert (HC : 1 <= class_id (rq_needed r) < kNumClasses).
    { unfold kNumClasses. apply class_id_range. apply Z.ltb_ge in LARGE. unfold kMaxSize in LARGE.
      pose proof (compute_req_facts n NNEG) as RQ. cbv zeta in RQ. fold r in RQ. destruct RQ as (_ & RZ & RD & _ & ND & _).
      destruct (rq_primary r); lia. }
    assert (C0 : 0 <= class_id (rq_needed r)) by lia.
    destruct (PRE _ HC) as (LENR & LENC & AU & AUM & Hs & Hs16 & CNT).
    apply (upd_chunk_complete_absorb stC X (ch_class ch) (ch_alloc_beg ch) ch); [| reflexivity| reflexivity|].
    + unfold fresh_key. subst ch. cbn [ch_user_beg]. destruct (cache_alloc_chunks _ _ _ _ _ LENR C0 CA) as [CH _]. rewrite CH, <- EU. exact FR.
    + subst ch. cbn [ch_class ch_alloc_beg].
      exact (cache_alloc_complete st X _ stC aC evC LENR LENC C0 AU AUM Hs Hs16 CNT CO CA).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma COMPLETE_Xext : forall st X X', (forall c, 1 <= c < kNumClasses -> forall x, In x (X c) -> In x (X' c)) -> COMPLETE st X -> COMPLETE st X'.
Proof.
  intros st X X' E CO. apply (COMPLETE_transfer st _ X); [reflexivity| intros; reflexivity| | exact CO].
  intros c x Hc IN. apply In_owners in IN. apply In_owners. intuition eauto.
Qed.
Lemma COMPLETE_xadd0 : forall st X a, COMPLETE st (xadd X 0 a) -> COMPLETE st X.
Proof. intros st X a. apply COMPLETE_Xext. intros c Hc x. unfold xadd. destruct (Z.eqb_spec c 0); [lia| tauto]. Qed.
Lemma COMPLETE_xadd_weaken : forall st X c a, COMPLETE st X -> COMPLETE st (xadd X c a).
Proof. intros st X c a. apply COMPLETE_Xext. intros c' Hc' x IN. unfold xadd. destruct (c' =? c); [right|]; exact IN. Qed.

Lemma own_batch_set_tq : forall st t c, own_batch (set_tq st t) c = (if c =? kBatchClass then map qb_addr (qc_list t ++ qc_list (as_gq st)) else []).
Proof. reflexivity. Qed.
Lemma own_batch_set_gq : forall st g c, own_batch (set_gq st g) c = (if c =? kBatchClass then map qb_addr (qc_list (as_tq st) ++ qc_list g) else []).
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma COMPLETE_set_queues : forall st X t g,
  (forall b, In b (qc_list (as_tq st) ++ qc_list (as_gq st)) -> In (qb_addr b) (map qb_addr (qc_list t ++ qc_list g))) ->
  COMPLETE st X -> COMPLETE (set_gq (set_tq st t) g) X.
Proof.
  intros st X t g INC CO. apply (COMPLETE_transfer st _ X); [reflexivity| intros; reflexivity| | exact CO].
  intros c x Hc IN. apply In_owners in IN. apply In_owners.
  change (own_free (set_gq (set_tq st t) g) c) with (own_free st c). change (own_cache (set_gq (set_tq st t) g) c) with (own_cache st c).
  change (own_chunk (set_gq (set_tq st t) g) c) with (own_chunk st c).
  destruct IN as [F|[C|[K|[B|XX]]]]; [tauto| tauto| tauto| | tauto]. right; right; right; left.
  unfold own_batch in B |- *. cbn [as_tq as_gq set_gq set_tq] in *. destruct (c =? kBatchClass); [| destruct B].
  apply in_map_iff in B. destruct B as (b & <- & Hb). apply INC. exact Hb.
Qed.
(* [comment removed for export] *)
Lemma COMPLETE_set_queues_out : forall st X t g (out : list Z),
  (forall b, In b (qc_list (as_tq st) ++ qc_list (as_gq st)) -> In (qb_addr b) (map qb_addr (qc_list t ++ qc_list g)) \/ In (qb_addr b) out) ->
  COMPLETE st X -> COMPLETE (set_gq (set_tq st t) g) (fun c => if c =? kBatchClass then out ++ X c else X c).
Proof.
  intros st X t g out INC CO. apply (COMPLETE_transfer st _ X); [reflexivity| intros; reflexivity| | exact CO].
  intros c x Hc IN. apply In_owners in IN. apply In_owners.
  change (own_free (set_gq (set_tq st t) g) c) with (own_free st c). change (own_cache (set_gq (set_tq st t) g) c) with (own_cache st c).
  change (own_chunk (set_gq (set_tq st t) g) c) with (own_chunk st c).
  destruct IN as [F|[C|[K|[B|XX]]]]; [tauto| tauto| tauto| | do 4 right; destruct (c =? kBatchClass); [apply in_app_iff; right|]; exact XX].
  unfold own_batch in B |- *. cbn [as_tq as_gq set_gq set_tq] in *. destruct (c =? kBatchClass); [| destruct B].
  apply in_map_iff in B. destruct B as (b & <- & Hb). destruct (INC b Hb) as [L|R]; [tauto|]. do 4 right. apply in_app_iff. left. exact R.
Qed.

(* [comment removed for export] *)
Lemma return_to_allocator_complete : forall st X c n ret st',
  length (as_regions st) = 32%nat -> 1 <= c < kNumClasses ->
  COMPLETE st (fun c' => if c' =? c then map (compact_to_addr st c) ret ++ X c' else X c') ->
  return_to_allocator st c n ret = Some (st', []) \/ (exists ev, return_to_allocator st c n ret = Some (st', ev)) ->
  COMPLETE st' X /\ same_core st' (set_region st c (mkRegion (rg_mapped_user (get_region st c)) (rg_allocated_user (get_region st c))
                                     (rg_num_freed (get_region st c) + n) (ret ++ rg_free_array (get_region st c)) (rg_mapped_free_array (get_region st' c))))
  /\ (rg_mapped_free_array (get_region st' c) = rg_mapped_free_array (get_region st c)
      \/ (rg_mapped_free_array (get_region st c) < 4 * (rg_num_freed (get_region st c) + n)
          /\ rg_mapped_free_array (get_region st' c) = round_up (4 * (rg_num_freed (get_region st c) + n)) kFreeArrayMapSize
          /\ rg_mapped_free_array (get_region st' c) <= kFreeArraySize)).
Proof.
  intros st X c n ret st' LENR Hc CO RT. set (X0 := fun c' : Z => if c' =? c then map (compact_to_addr st c) ret ++ X c' else X c') in CO.
  assert (RT' : exists ev, return_to_allocator st c n ret = Some (st', ev)) by (destruct RT as [R|R]; [exists []; exact R| exact R]). clear RT.
  destruct RT' as [ev RT]. unfold return_to_allocator in RT.
  destruct (ensure_free_array_space st c _) as [[st1 ev1]|] eqn:EN; [| discriminate RT]. injection RT as <- _.
  destruct (ensure_free_array_space_core st c _ st1 ev1 EN) as (mfa' & C1 & MFA). cbv zeta in C1.
  pose proof (get_region_core_set _ _ _ _ C1 LENR ltac:(lia)) as G1.
  assert (L1 : length (as_regions st1) = 32%nat) by (rewrite (same_core_len_regions _ _ C1), length_regions_set_region; exact LENR).
  set (r2 := mkRegion _ _ _ _ _).
  assert (C2 : same_core (set_region st1 c r2) (set_region st c r2)) by (apply (same_core_set_region_l _ _ _ _ _ C1)).
  assert (G2 : get_region (set_region st1 c r2) c = r2) by (apply get_region_set_region_eq; [exact L1| lia]).
  split; [| split].
  - apply (COMPLETE_view (set_region st c r2)); [symmetry; apply same_core_cview; exact C2|].
    apply (COMPLETE_transfer st _ X0); [reflexivity| | | exact CO].
    + intros c' Hc'. destruct (Z.eq_dec c' c) as [->|NE]; [rewrite (ncarved_set_region_eq st c r2 LENR) by lia; subst r2; cbn; rewrite G1; reflexivity|].
      rewrite (ncarved_set_region_neq st c c' r2) by lia. reflexivity.
    + intros c' x Hc' IN. apply In_owners in IN. apply In_owners.
      rewrite own_cache_set_region, own_chunk_set_region, own_batch_set_region.
      destruct (Z.eq_dec c' c) as [->|NE].
      * rewrite (own_free_set_region_eq st c r2 LENR) by lia. subst r2. cbn [rg_free_array]. rewrite G1. cbn [rg_free_array].
        subst X0. cbv beta in IN. rewrite Z.eqb_refl in IN. rewrite map_app. rewrite !in_app_iff in IN |- *. unfold own_free in IN. tauto.
      * rewrite (own_free_set_region_neq st c c' r2) by lia. subst X0. cbv beta in IN. destruct (Z.eqb_spec c' c); [contradiction|]. exact IN.
  - rewrite G2. subst r2. rewrite G1 in C2 |- *. cbn [rg_mapped_user rg_allocated_user rg_num_freed rg_free_array rg_mapped_free_array] in C2 |- *. exact C2.
  - rewrite G2. subst r2. rewrite G1. cbn [rg_mapped_user rg_allocated_user rg_num_freed rg_free_array rg_mapped_free_array]. exact MFA.
Qed.

Lemma cta_atc : forall st c p, region_beg st c <= p -> (p - region_beg st c) mod 16 = 0 ->
  compact_to_addr st c (addr_to_compact st c p) = p.
Proof.
  intros st c p LE M. unfold compact_to_addr, addr_to_compact. rewrite shiftr4_shiftl4; [lia| lia| exact M].
Qed.

(* [comment removed for export] *)
Lemma cache_cut_complete : forall st X c k cnt,
  length (as_cache st) = 32%nat -> 1 <= c < kNumClasses ->
  COMPLETE st X ->
  COMPLETE (set_pc st c (mkPC cnt (skipn k (pc_chunks (get_pc st c)))))
           (fun c' => if c' =? c then map (compact_to_addr st c) (firstn k (pc_chunks (get_pc st c))) ++ X c' else X c').
Proof.
  intros st X c k cnt LENC Hc CO.
  apply (COMPLETE_transfer st _ X); [reflexivity| intros; apply ncarved_set_pc| | exact CO].
  intros c' x Hc' IN. apply In_owners in IN. apply In_owners. rewrite own_free_set_pc, own_chunk_set_pc, own_batch_set_pc.
  destruct (Z.eq_dec c' c) as [->|NE].
  - rewrite (own_cache_set_pc_eq st c _ LENC) by lia. cbn [pc_chunks]. rewrite Z.eqb_refl.
    destruct IN as [F|[C|[K|[B|XX]]]]; [tauto| | tauto| tauto| do 4 right; apply in_app_iff; right; exact XX].
    unfold own_cache in C. rewrite <- (firstn_skipn k (pc_chunks (get_pc st c))), map_app, in_app_iff in C.
    destruct C as [C|C]; [do 4 right; apply in_app_iff; left; exact C| right; left; exact C].
  - rewrite (own_cache_set_pc_neq st c c') by lia. destruct (Z.eqb_spec c' c); [contradiction|]. exact IN.
Qed.

(* [comment removed for export] *)
Lemma cache_push_complete : forall st X c p cnt,
  length (as_cache st) = 32%nat -> 1 <= c < kNumClasses -> region_beg st c <= p -> (p - region_beg st c) mod 16 = 0 ->
  COMPLETE st (xadd X c p) ->
  COMPLETE (set_pc st c (mkPC cnt (addr_to_compact st c p :: pc_chunks (get_pc st c)))) X.
Proof.
  intros st X c p cnt LENC Hc LE M CO.
  apply (COMPLETE_transfer st _ (xadd X c p)); [reflexivity| intros; apply ncarved_set_pc| | exact CO].
  intros c' x Hc' IN. apply In_owners in IN. apply In_owners. rewrite own_free_set_pc, own_chunk_set_pc, own_batch_set_pc.
  destruct (Z.eq_dec c' c) as [->|NE].
  - rewrite (own_cache_set_pc_eq st c _ LENC) by lia. cbn [pc_chunks map]. rewrite (cta_atc st c p LE M). rewrite xadd_eq in IN.
    unfold own_cache in IN. cbn [In] in IN |- *. destruct IN as [F|[C|[K|[B|[<-|XX]]]]]; tauto.
  - rewrite (own_cache_set_pc_neq st c c') by lia. rewrite xadd_neq in IN by exact NE. exact IN.
Qed.

Theorem cache_dealloc_complete : forall st X c p st' ev,
  length (as_regions st) = 32%nat -> length (as_cache st) = 32%nat -> 0 <= c ->
  region_beg st c <= p -> (p - region_beg st c) mod 16 = 0 ->
  COMPLETE st (xadd X c p) -> cache_dealloc st c p = Some (st', ev) -> COMPLETE st' X.
Proof.
  intros st X c p st' ev LENR LENC C0 LE M CO H. unfold cache_dealloc in H.
  destruct ((c =? 0) || (kNumClasses <=? c)) eqn:CC; [discriminate H|].
  apply Bool.orb_false_iff in CC. destruct CC as [CC1 CC2]. apply Z.eqb_neq in CC1. apply Z.leb_gt in CC2.
  assert (Hc : 1 <= c < kNumClasses) by lia.
  set (st0 := ensure_cache_inited st) in H.
  assert (CO0 : COMPLETE st0 (xadd X c p)) by (apply (COMPLETE_view st); [symmetry; apply cview_ensure_cache_inited| exact CO]).
  assert (L0R : length (as_regions st0) = 32%nat) by (subst st0; rewrite as_regions_eci; exact LENR).
  assert (L0C : length (as_cache st0) = 32%nat) by (subst st0; rewrite as_cache_eci; exact LENC).
  assert (RB0 : region_beg st0 c = region_beg st c) by (subst st0; unfold region_beg; rewrite as_space_beg_eci; reflexivity).
  destruct (pc_count (get_pc st0 c) =? max_count c) eqn:FULL.
  - destruct (pc_count (get_pc st0 c) <? max_count c / 2); [discriminate H|].
    set (k := Z.to_nat (max_count c / 2)) in H.
    set (pck := mkPC (pc_count (get_pc st0 c) - max_count c / 2) (skipn k (pc_chunks (get_pc st0 c)))) in H.
    destruct (return_to_allocator (set_pc st0 c pck) c _ _) as [[st1 ev1]|] eqn:RT; [| discriminate H]. injection H as <- _.
    pose proof (cache_cut_complete st0 (xadd X c p) c k (pc_count (get_pc st0 c) - max_count c / 2) L0C Hc CO0) as CUT. fold pck in CUT.
    destruct (return_to_allocator_complete (set_pc st0 c pck) (xadd X c p) c (max_count c / 2) (firstn k (pc_chunks (get_pc st0 c))) st1
                ltac:(unfold set_pc; cbn; exact L0R) Hc) as (CO1 & C1 & _).
    { exact CUT. }
    { right. exists ev1. exact RT. }
    pose proof (same_core_cview _ _ C1) as CV1.
    assert (PC1 : get_pc st1 c = pck).
    { destruct C1 as (_ & _ & _ & _ & CA & _). unfold get_pc. rewrite CA. unfold set_region, set_pc. cbn [as_cache].
      fold (get_pc (set_pc st0 c pck) c). apply get_pc_set_pc_eq; [exact L0C| lia]. }
    assert (RB1 : region_beg st1 c = region_beg st c) by (destruct C1 as (SB & _); rewrite <- RB0; unfold region_beg; rewrite SB; reflexivity).
    assert (LC1 : length (as_cache st1) = 32%nat) by (destruct C1 as (_ & _ & _ & _ & CA & _); rewrite CA; unfold set_region, set_pc; cbn; rewrite length_upd_nth; exact L0C).
    replace (skipn k (pc_chunks (get_pc st0 c))) with (pc_chunks (get_pc st1 c)) by (rewrite PC1; subst pck; reflexivity).
    apply cache_push_complete; [exact LC1| exact Hc| rewrite RB1; exact LE| rewrite RB1; exact M| exact CO1].
  - injection H as <- _. cbn [pc_count pc_chunks].
    apply cache_push_complete; [exact L0C| exact Hc| rewrite RB0; exact LE| rewrite RB0; exact M| exact CO0].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition chunk_slot_ok (st : astate) (ch : chunk) : Prop :=
     (ch_primary ch = true ->
      1 <= ch_class ch < kNumClasses /\ class_of_addr st (ch_chunk_beg ch) = ch_class ch
      /\ region_beg st (ch_class ch) <= ch_alloc_beg ch /\ (ch_alloc_beg ch - region_beg st (ch_class ch)) mod 16 = 0
      /\ in_primary st (ch_chunk_beg ch) = true)
  /\ (ch_primary ch = false -> in_primary st (ch_alloc_beg ch) = false).     (* [comment removed for export] *)

(* [comment removed for export] *)
Lemma class_of_addr_lt32 : forall st a, 0 <= class_of_addr st a < 32.
Proof.
  intros st a. unfold class_of_addr. split; [apply Z.land_nonneg; right; lia|].
  change 31 with (Z.ones 5). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia.
Qed.
Lemma class_of_addr_window : forall st m, in_primary st m = true ->
  region_beg st (class_of_addr st m) <= m < region_beg st (class_of_addr st m) + 2 ^ 32.
Proof.
  intros st m P. unfold in_primary in P. apply andb_true_iff in P as [P1 P2]. apply Z.leb_le in P1. apply Z.ltb_lt in P2. unfold kSpaceSize in P2.
  unfold class_of_addr, kRegionSizeLog. rewrite region_beg_eq. rewrite Z.shiftr_div_pow2 by lia.
  change 31 with (Z.ones 5). rewrite Z.land_ones by lia.
  assert (Q : 0 <= (m - as_space_beg st) / 2 ^ 32 < 32) by (split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
  rewrite Z.mod_small by lia. pose proof (Z.div_mod (m - as_space_beg st) (2 ^ 32) ltac:(lia)). pose proof (Z.mod_pos_bound (m - as_space_beg st) (2 ^ 32) ltac:(lia)). lia.
Qed.
Lemma chunk_slot_prim : forall st ch c k, chunk_slot_ok st ch ->
  in_primary st (ch_chunk_beg ch) = true -> 0 <= c < 32 -> region_beg st c + k = ch_alloc_beg ch -> 0 <= k < 2 ^ 32 ->
  1 <= ch_class ch < kNumClasses /\ class_of_addr st (ch_chunk_beg ch) = ch_class ch
  /\ region_beg st (ch_class ch) <= ch_alloc_beg ch /\ (ch_alloc_beg ch - region_beg st (ch_class ch)) mod 16 = 0.
Proof.
  intros st ch c k [P S] PRIM Hc E Hk. destruct (ch_primary ch) eqn:PR.
  - destruct (P eq_refl) as (A & B & C & D & _). exact (conj A (conj B (conj C D))).
  - exfalso. pose proof (S eq_refl) as NP. rewrite <- E in NP. rewrite (in_primary_region st c k Hc Hk) in NP. discriminate NP.
Qed.
Lemma chunk_slot_sec : forall st ch, chunk_slot_ok st ch -> in_primary st (ch_chunk_beg ch) = false -> ch_class ch = 0.
Proof.
  intros st ch [P S] NP. destruct (ch_primary ch) eqn:PR.
  - destruct (P eq_refl) as (_ & _ & _ & _ & T). rewrite T in NP. discriminate NP.
  - unfold ch_primary in PR. destruct (Z.eqb_spec (ch_class ch) 0); [assumption| discriminate PR].
Qed.
Definition batch_slot_ok (st : astate) (b : qbatch) : Prop :=
  region_beg st kBatchClass <= qb_addr b /\ (qb_addr b - region_beg st kBatchClass) mod 16 = 0
  /\ in_primary st (qb_addr b) = true /\ class_of_addr st (qb_addr b) = kBatchClass.

(* [comment removed for export] *)
Definition free_env (st : astate) : Prop :=
     length (as_regions st) = 32%nat /\ length (as_cache st) = 32%nat /\ keys_ok (as_chunks st)
  /\ (forall ch, In ch (chunk_list st) -> chunk_slot_ok st ch).

Lemma large_deallocate_core : forall st p st' ev, large_deallocate st p = Some (st', ev) -> cview st' = cview st /\ same_core st' (set_sec st (as_n_reserved st') (as_sec st')).
Proof.
  intros st p st' ev H. unfold large_deallocate in H.
  destruct (negb _); [discriminate H|]. destruct (find_sec_idx _ _ _); [| discriminate H]. cbv zeta in H.
  destruct (poison_shadow (set_sec st _ _) _ _ _) as [[st2 ev2]|] eqn:P2; [| discriminate H].
  destruct (negb _); [discriminate H|]. injection H as <- _.
  pose proof (same_core_trans _ _ _ (same_core_remove_map st2 (p - kPageSize)) (poison_shadow_core _ _ _ _ _ _ P2)) as C.
  split.
  - rewrite (same_core_cview _ _ C). reflexivity.
  - cbn [as_n_reserved as_sec remove_map]. unfold same_core in *. unfold set_sec in *. cbn in *. intuition congruence.
Qed.

Lemma find_chunk_In : forall st u ch, find_chunk (as_chunks st) u = Some ch -> In ch (chunk_list st).
Proof.
  intros st u ch F. unfold find_chunk in F. destruct (u <=? 0); [discriminate F|]. apply chunk_list_in_iff. exists (ckey u). exact F.
Qed.
Lemma find_chunk_key : forall st u ch, keys_ok (as_chunks st) -> find_chunk (as_chunks st) u = Some ch -> ch_user_beg ch = u.
Proof.
  intros st u ch K F. unfold find_chunk in F. destruct (u <=? 0) eqn:U; [discriminate F|]. apply Z.leb_gt in U.
  destruct (K _ _ F) as [E P]. unfold ckey in E. apply Z2Pos.inj; [exact P| exact U| congruence].
Qed.


(* [comment removed for export] *)
Definition regs_am_same (a b : astate) : Prop :=
  forall c, rg_allocated_user (get_region a c) = rg_allocated_user (get_region b c) /\ rg_mapped_user (get_region a c) = rg_mapped_user (get_region b c).
Lemma regs_am_same_refl : forall a, regs_am_same a a. Proof. intros a c. split; reflexivity. Qed.
Lemma regs_am_same_trans : forall a b c, regs_am_same a b -> regs_am_same b c -> regs_am_same a c.
Proof. intros a b c H1 H2 k. destruct (H1 k) as [A B]. destruct (H2 k) as [C D]. split; congruence. Qed.
Lemma regs_am_same_regions : forall a b, as_regions a = as_regions b -> regs_am_same a b.
Proof. intros a b E k. unfold get_region. rewrite E. split; reflexivity. Qed.
Lemma regs_am_same_core : forall a b, same_core a b -> regs_am_same a b.
Proof. intros a b C. apply regs_am_same_regions. destruct C as (_ & _ & E & _). exact E. Qed.
Lemma regs_am_same_set_region : forall st c r, length (as_regions st) = 32%nat -> 0 <= c < kNumClasses ->
  rg_allocated_user r = rg_allocated_user (get_region st c) -> rg_mapped_user r = rg_mapped_user (get_region st c) ->
  regs_am_same (set_region st c r) st.
Proof.
  intros st c r L Hc A M k. destruct (Z_lt_le_dec k 0) as [NEG|NN].
  - unfold get_region, set_region, zidx. cbn [as_regions]. replace (Z.to_nat k) with 0%nat by lia.
    destruct (Z.eq_dec c 0) as [->|NZ].
    + rewrite (znth_upd_nth_eq) by (rewrite L; cbn; lia). change (znth (as_regions st) 0 region0) with (get_region st 0). rewrite A, M. split; reflexivity.
    + rewrite znth_upd_nth_neq by (unfold zidx; lia). split; reflexivity.
  - destruct (Z.eq_dec k c) as [->|NE].
    + rewrite (get_region_set_region_eq st c r L Hc). split; assumption.
    + rewrite (get_region_set_region_neq st c k r) by lia. split; reflexivity.
Qed.

Lemma cache_dealloc_frame : forall st c p st' ev, length (as_regions st) = 32%nat -> 0 <= c ->
  cache_dealloc st c p = Some (st', ev) ->
  as_chunks st' = as_chunks st /\ as_space_beg st' = as_space_beg st /\ length (as_regions st') = 32%nat /\ length (as_cache st') = length (as_cache st)
  /\ as_tq st' = as_tq st /\ as_gq st' = as_gq st /\ as_sec st' = as_sec st /\ as_n_reserved st' = as_n_reserved st
  /\ regs_am_same st' st.
Proof.
  intros st c p st' ev LENR C0 H. unfold cache_dealloc in H.
  destruct ((c =? 0) || (kNumClasses <=? c)) eqn:CC; [discriminate H|].
  apply Bool.orb_false_iff in CC. destruct CC as [CC1 CC2]. apply Z.eqb_neq in CC1. apply Z.leb_gt in CC2.
  set (st0 := ensure_cache_inited st) in H.
  assert (F0 : as_chunks st0 = as_chunks st /\ as_space_beg st0 = as_space_beg st /\ as_regions st0 = as_regions st /\ as_cache st0 = as_cache st
               /\ as_tq st0 = as_tq st /\ as_gq st0 = as_gq st /\ as_sec st0 = as_sec st /\ as_n_reserved st0 = as_n_reserved st).
  { subst st0. unfold ensure_cache_inited. destruct (as_cache_inited st); repeat split; reflexivity. }
  destruct F0 as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
  assert (Hc : 0 <= c < kNumClasses) by lia.
  assert (L0 : length (as_regions st0) = 32%nat) by (rewrite A3; exact LENR).
  destruct (pc_count (get_pc st0 c) =? max_count c).
  - destruct (_ <? _); [discriminate H|].
    destruct (return_to_allocator (set_pc st0 c _) c _ _) as [[st1 ev1]|] eqn:RT; [| discriminate H]. injection H as <- _.
    unfold return_to_allocator in RT. destruct (ensure_free_array_space _ c _) as [[st2 ev2]|] eqn:EN; [| discriminate RT]. injection RT as <- _.
    destruct (ensure_free_array_space_core _ c _ st2 ev2 EN) as (mfa' & C2 & _). cbv zeta in C2.
    assert (RS : regs_am_same st2 st).
    { eapply regs_am_same_trans; [apply regs_am_same_core; exact C2|]. eapply regs_am_same_trans; [apply regs_am_same_set_region; [cbn; exact L0| exact Hc| reflexivity| reflexivity]|].
      apply regs_am_same_regions. cbn. exact A3. }
    pose proof (get_region_core_set _ _ _ _ C2 ltac:(cbn; exact L0) Hc) as G2.
    destruct C2 as (B1 & _ & B3 & _ & B5 & B6 & B7 & B8 & B9 & B10 & _). cbn in B1, B3, B5, B6, B7, B8, B9, B10.
    split; [cbn; rewrite B8, A1; reflexivity|]. split; [cbn; rewrite B1, A2; reflexivity|]. split; [cbn; rewrite length_upd_nth, B3; cbn; rewrite length_upd_nth, A3; exact LENR|].
    split; [cbn; rewrite length_upd_nth, B5; cbn; rewrite length_upd_nth, A4; reflexivity|].
    split; [cbn; rewrite B9, A5; reflexivity|]. split; [cbn; rewrite B10, A6; reflexivity|]. split; [cbn; rewrite B7, A7; reflexivity|]. split; [cbn; rewrite B6, A8; reflexivity|].
    eapply regs_am_same_trans; [apply regs_am_same_regions; reflexivity|].
    eapply regs_am_same_trans; [| exact RS]. apply regs_am_same_set_region; [rewrite B3; cbn; rewrite length_upd_nth, A3; exact LENR| exact Hc| rewrite G2; reflexivity| rewrite G2; reflexivity].
  - injection H as <- _. cbn. rewrite A1, A2, A3, A5, A6, A7, A8, length_upd_nth, A4. split; [reflexivity|]. split; [reflexivity|]. split; [exact LENR|].
    repeat (split; [reflexivity|]). apply regs_am_same_regions. cbn. exact A3.
Qed.

Theorem cb_recycle_complete : forall st X m st' ev,
  free_env st -> COMPLETE st X -> cb_recycle st m = Some (st', ev) ->
  COMPLETE st' X /\ (forall ch, In ch (chunk_list st') -> In ch (chunk_list st)) /\ as_space_beg st' = as_space_beg st
  /\ length (as_regions st') = 32%nat /\ length (as_cache st') = 32%nat /\ keys_ok (as_chunks st')
  /\ as_tq st' = as_tq st /\ as_gq st' = as_gq st /\ regs_am_same st' st.
Proof.
  intros st X m st' ev (LENR & LENC & K & CSO) CO H. unfold cb_recycle in H.
  destruct (find_chunk (as_chunks st) (m + kChunkHeaderSize)) as [ch|] eqn:F; [| discriminate H].
  pose proof (find_chunk_In _ _ _ F) as INch. pose proof (find_chunk_key _ _ _ K F) as KEY.
  assert (CB : ch_chunk_beg ch = m) by (unfold ch_chunk_beg; rewrite KEY; unfold kChunkHeaderSize; lia).
  assert (REMK : keys_ok (remove_chunk (as_chunks st) (ch_user_beg ch))).
  { intros k x Fk. unfold remove_chunk in Fk. destruct (PositiveMap.E.eq_dec k (ckey (ch_user_beg ch))) as [->|NE].
    - rewrite PositiveMap.grs in Fk. discriminate Fk.
    - rewrite PositiveMap.gro in Fk by exact NE. exact (K _ _ Fk). }
  destruct (ch_state ch); [discriminate H|].
  destruct (in_primary st m) eqn:PRIM.
  - (* [comment removed for export] *)
    cbv zeta in H. destruct (class_of_addr st m =? 0); [discriminate H|]. destruct (_ <? _); [discriminate H|].
    destruct (negb (_ =? ch_alloc_beg ch)) eqn:PB; [discriminate H|]. apply Bool.negb_false_iff in PB. apply Z.eqb_eq in PB.
    destruct (poison_shadow st _ _ _) as [[st1 ev1]|] eqn:P1; [| discriminate H].
    destruct (cache_dealloc _ _ _) as [[st3 ev3]|] eqn:CD; [| discriminate H]. injection H as <- _.
    rewrite <- CB in PRIM.
    assert (SLOT : 1 <= ch_class ch < kNumClasses /\ class_of_addr st (ch_chunk_beg ch) = ch_class ch
                   /\ region_beg st (ch_class ch) <= ch_alloc_beg ch /\ (ch_alloc_beg ch - region_beg st (ch_class ch)) mod 16 = 0).
    { pose proof (class_of_addr_window st m ltac:(rewrite <- CB; exact PRIM)) as WIN. pose proof (class_of_addr_lt32 st m) as C32.
      set (c0 := class_of_addr st m) in *. set (sz := class_size c0) in *.
      pose proof (class_size_table_facts c0 C32) as (CS1 & _).
      assert (KB : 0 <= (m - region_beg st c0) / sz * sz < 2 ^ 32).
      { destruct (Z.eq_dec sz 0) as [Z0|NZ]; [rewrite Z0, Z.mul_0_r; lia|].
        assert (0 <= (m - region_beg st c0) / sz) by (apply Z.div_pos; lia).
        pose proof (Z.mul_div_le (m - region_beg st c0) sz ltac:(lia)). split; [apply Z.mul_nonneg_nonneg; lia| lia]. }
      exact (chunk_slot_prim st ch c0 _ (CSO ch INch) PRIM C32 PB KB). }
    destruct SLOT as (HC & CL & LE & MD). rewrite CB in CL. rewrite PB in CD. rewrite CL in CD.
    pose proof (poison_shadow_core _ _ _ _ _ _ P1) as C1.
    assert (CH1 : as_chunks st1 = as_chunks st) by (destruct C1 as (_ & _ & _ & _ & _ & _ & _ & E & _); exact E).
    set (st2 := set_chunks st1 (remove_chunk (as_chunks st1) (ch_user_beg ch))) in CD.
    assert (C2 : cview st2 = cview (set_chunks st (remove_chunk (as_chunks st) (ch_user_beg ch)))).
    { subst st2. unfold cview, set_chunks. cbn. rewrite CH1. pose proof C1 as (E1 & _ & E3 & _ & E5 & _ & _ & _ & E9 & E10 & _). rewrite E1, E3, E5, E9, E10. reflexivity. }
    assert (CO2 : COMPLETE st2 (xadd X (ch_class ch) (ch_alloc_beg ch))).
    { apply (COMPLETE_view _ _ _ (eq_sym C2)). apply remove_chunk_complete; assumption. }
    assert (L2R : length (as_regions st2) = 32%nat) by (subst st2; cbn; rewrite (same_core_len_regions _ _ C1); exact LENR).
    assert (L2C : length (as_cache st2) = 32%nat) by (subst st2; cbn; destruct C1 as (_ & _ & _ & _ & E & _); rewrite E; exact LENC).
    assert (SB2 : as_space_beg st2 = as_space_beg st) by (subst st2; cbn; destruct C1 as (E & _); exact E).
    assert (RB2 : region_beg st2 (ch_class ch) = region_beg st (ch_class ch)) by (unfold region_beg; rewrite SB2; reflexivity).
    pose proof (cache_dealloc_complete st2 X (ch_class ch) (ch_alloc_beg ch) st3 ev3 L2R L2C ltac:(lia) ltac:(rewrite RB2; exact LE) ltac:(rewrite RB2; exact MD) CO2 CD) as CO3.
    (* [comment removed for export] *)
    destruct (cache_dealloc_frame st2 (ch_class ch) (ch_alloc_beg ch) st3 ev3 L2R ltac:(lia) CD) as (CH3 & SB3 & L3R & L3C & TQ3 & GQ3 & _ & _ & RS3).
    assert (CH3' : as_chunks st3 = remove_chunk (as_chunks st) (ch_user_beg ch)) by (rewrite CH3; subst st2; cbn; rewrite CH1; reflexivity).
    pose proof C1 as (_ & _ & RG1 & _ & _ & _ & _ & _ & TQ1 & GQ1 & _).
    split; [exact CO3|]. split.
    { intros x Hx. unfold chunk_list in Hx |- *. rewrite CH3' in Hx. apply (chunk_list_remove_iff st (ch_user_beg ch) x) in Hx. exact (proj1 Hx). }
    split; [rewrite SB3; exact SB2|]. split; [exact L3R|]. split; [rewrite L3C; exact L2C|]. split; [rewrite CH3'; exact REMK|].
    split; [rewrite TQ3; subst st2; cbn; exact TQ1|]. split; [rewrite GQ3; subst st2; cbn; exact GQ1|].
    eapply regs_am_same_trans; [exact RS3|]. apply regs_am_same_regions. subst st2. cbn. exact RG1.
  - (* [comment removed for export] *)
    destruct (large_get_block_begin st m) as [p|]; [| discriminate H]. destruct (p =? 0); [discriminate H|].
    destruct (in_primary st p); [discriminate H|]. destruct (negb (p =? ch_alloc_beg ch)); [discriminate H|].
    destruct (large_deallocate_core _ _ _ _ H) as [CV CL].
    split.
    { apply (COMPLETE_view _ _ _ (eq_sym CV)). apply (COMPLETE_xadd0 _ X (ch_alloc_beg ch)).
      assert (CL0 : ch_class ch = 0) by (apply (chunk_slot_sec st ch (CSO ch INch)); rewrite CB; exact PRIM).
      rewrite <- CL0. apply remove_chunk_complete; assumption. }
    destruct CL as (SB' & _ & RG' & _ & CA' & _ & _ & CH' & TQ' & GQ' & _). cbn in SB', RG', CA', CH', TQ', GQ'.
    split.
    { intros x Hx. unfold chunk_list in Hx |- *. rewrite CH' in Hx. apply (chunk_list_remove_iff st (ch_user_beg ch) x) in Hx. exact (proj1 Hx). }
    split; [exact SB'|]. split; [rewrite RG'; exact LENR|]. split; [rewrite CA'; exact LENC|]. split; [rewrite CH'; exact REMK|].
    split; [exact TQ'|]. split; [exact GQ'|]. apply regs_am_same_regions. exact RG'.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition same_but_queues (a b : astate) : Prop :=
  as_space_beg a = as_space_beg b /\ as_regions a = as_regions b /\ as_cache a = as_cache b /\ as_chunks a = as_chunks b.

Lemma COMPLETE_requeue : forall st st' X X',
  same_but_queues st' st ->
  (forall c x, 1 <= c < kNumClasses -> In x (own_batch st c) \/ In x (X c) -> In x (own_batch st' c) \/ In x (X' c)) ->
  COMPLETE st X -> COMPLETE st' X'.
Proof.
  intros st st' X X' (SB & RG & CA & CH) INC CO.
  apply (COMPLETE_transfer st _ X); [exact SB| intros; unfold ncarved, get_region; rewrite RG; reflexivity| | exact CO].
  intros c x Hc IN. apply In_owners in IN. apply In_owners.
  replace (own_free st' c) with (own_free st c) by (unfold own_free, get_region, compact_to_addr, region_beg; rewrite RG, SB; reflexivity).
  replace (own_cache st' c) with (own_cache st c) by (unfold own_cache, get_pc, compact_to_addr, region_beg; rewrite CA, SB; reflexivity).
  replace (own_chunk st' c) with (own_chunk st c) by (unfold own_chunk, chunk_list; rewrite CH; reflexivity).
  destruct IN as [F|[C|[K|[B|XX]]]]; [tauto| tauto| tauto| |]; destruct (INC c x Hc ltac:(tauto)); tauto.
Qed.

Definition xbat (out : list qbatch) (X : Z -> list Z) : Z -> list Z :=
  fun c => if c =? kBatchClass then map qb_addr out ++ X c else X c.
Lemma xbat_nil : forall X c, xbat [] X c = X c.
Proof. intros. unfold xbat. destruct (c =? kBatchClass); reflexivity. Qed.

Lemma own_batch_In : forall st c x, In x (own_batch st c) <-> c = kBatchClass /\ exists b, In b (qc_list (as_tq st) ++ qc_list (as_gq st)) /\ qb_addr b = x.
Proof.
  intros st c x. unfold own_batch. destruct (Z.eqb_spec c kBatchClass) as [->|NE].
  - rewrite in_map_iff. split; [intros (b & E & IN); split; [reflexivity| exists b; tauto]| intros [_ (b & IN & E)]; exists b; tauto].
  - split; [intros []| intros [E _]; contradiction].
Qed.

(* [comment removed for export] *)
Lemma free_env_transfer : forall st st', as_space_beg st' = as_space_beg st ->
  length (as_regions st') = 32%nat -> length (as_cache st') = 32%nat -> keys_ok (as_chunks st') ->
  (forall ch, In ch (chunk_list st') -> In ch (chunk_list st) \/ exists ch0, In ch0 (chunk_list st) /\ ch_alloc_beg ch = ch_alloc_beg ch0 /\ ch_user_beg ch = ch_user_beg ch0 /\ ch_class ch = ch_class ch0) ->
  free_env st -> free_env st'.
Proof.
  intros st st' SB LR LC K SUB (_ & _ & _ & CSO). split; [exact LR|]. split; [exact LC|]. split; [exact K|].
  intros ch IN. unfold chunk_slot_ok, ch_primary, in_primary, region_beg, class_of_addr in *. rewrite SB.
  destruct (SUB ch IN) as [IN0|(ch0 & IN0 & A & U & C)]; [exact (CSO ch IN0)|].
  pose proof (CSO ch0 IN0) as Q. unfold ch_chunk_beg in *. rewrite A, U, C. exact Q.
Qed.

(* [comment removed for export] *)
Theorem quarantine_enqueue_complete : forall st X m size st' ev,
  cons_pre st kBatchClass -> COMPLETE st X -> quarantine_enqueue st m size = Some (st', ev) ->
  COMPLETE st' X
  /\ (exists stc, (stc = st \/ exists b evb, cache_alloc st kBatchClass = Some (stc, b, evb)) /\ same_but_queues st' stc /\ as_gq st' = as_gq st
       /\ as_sec st' = as_sec stc /\ as_n_reserved st' = as_n_reserved stc)
  /\ (forall b', In b' (qc_list (as_tq st') ++ qc_list (as_gq st')) ->
        (exists b0, In b0 (qc_list (as_tq st) ++ qc_list (as_gq st)) /\ qb_addr b' = qb_addr b0)
        \/ (exists stc evb, cache_alloc st kBatchClass = Some (stc, qb_addr b', evb))).
Proof.
  intros st X m size st' ev PRE CO H. unfold quarantine_enqueue in H.
  match type of H with (if ?nn then _ else _) = _ => destruct nn eqn:NN end.
  - destruct (cache_alloc st kBatchClass) as [[[st1 b] evb]|] eqn:CA; [| discriminate H].
    destruct (b =? 0); [discriminate H|]. injection H as <- _.
    destruct PRE as (LENR & LENC & AU & AUM & Hs & Hs16 & CNT).
    pose proof (cache_alloc_complete st X kBatchClass st1 b evb LENR LENC ltac:(unfold kBatchClass; lia) AU AUM Hs Hs16 CNT CO CA) as CO1.
    destruct (cache_alloc_frame st kBatchClass st1 b evb LENR ltac:(unfold kBatchClass; lia) CA) as (CH1 & SB1 & LR1 & LC1 & TQ1 & GQ1 & SEC1 & NR1).
    split; [| split].
    + apply (COMPLETE_requeue st1 _ (xadd X kBatchClass b)); [repeat split; reflexivity| | exact CO1].
      intros c x Hc [B|XX].
      * left. apply own_batch_In in B. destruct B as (-> & b0 & IN & E). apply own_batch_In. split; [reflexivity|]. exists b0. split; [| exact E].
        cbn [as_tq as_gq set_tq qc_list]. apply in_app_iff in IN. apply in_app_iff. destruct IN as [IN|IN]; [left; apply in_app_iff; left; exact IN| right; exact IN].
      * unfold xadd in XX. destruct (Z.eqb_spec c kBatchClass) as [->|NE]; [| right; exact XX].
        destruct XX as [<-|XX]; [left| right; exact XX]. apply own_batch_In. split; [reflexivity|].
        exists (mkQB b (size + kBatchSize) 1 [m]). split; [| reflexivity]. cbn [as_tq as_gq set_tq qc_list]. apply in_app_iff. left. apply in_app_iff. right. left. reflexivity.
    + exists st1. split; [right; exists b, evb; reflexivity|]. cbn. rewrite GQ1. repeat split; reflexivity.
    + intros b' IN. cbn [as_tq as_gq set_tq qc_list] in IN. rewrite TQ1, GQ1 in IN. rewrite in_app_iff, in_app_iff in IN. cbn [In] in IN.
      destruct IN as [[IN|[<-|[]]]|IN].
      * left. exists b'. split; [apply in_app_iff; left; exact IN| reflexivity].
      * right. exists st1, evb. reflexivity.
      * left. exists b'. split; [apply in_app_iff; right; exact IN| reflexivity].
  - injection H as <- _. split; [| split].
    + apply (COMPLETE_requeue st _ X); [repeat split; reflexivity| | exact CO].
      intros c x Hc [B|XX]; [left| right; exact XX].
      apply own_batch_In in B. destruct B as (-> & b0 & IN & E). apply own_batch_In. split; [reflexivity|].
      cbn [as_tq as_gq set_tq qc_list]. apply in_app_iff in IN. destruct IN as [IN|IN].
      * destruct (qc_list (as_tq st)) as [|b1 l] eqn:TL; [destruct IN|].
        assert (SPLIT : forall (l0 : list qbatch) y, In y l0 -> In y (firstn (length l0 - 1) l0) \/ y = last l0 (mkQB 0 0 0 [])).
        { clear. intros l0. induction l0 as [|z l0 IH]; intros y Hy; [destruct Hy|].
          destruct l0 as [|w l0].
          - destruct Hy as [<-|[]]. right. reflexivity.
          - cbn [length Nat.sub firstn last] in *. rewrite Nat.sub_0_r in *. destruct Hy as [<-|Hy]; [left; left; reflexivity|].
            destruct (IH y Hy) as [L|R]; [left; right| right; exact R].
            replace (length (w :: l0) - 1)%nat with (length l0) in L by (cbn; lia). exact L. }
        destruct (SPLIT (b1 :: l) b0 IN) as [L|R].
        -- exists b0. split; [| exact E]. apply in_app_iff. left. apply in_app_iff. left. exact L.
        -- eexists. split; [apply in_app_iff; left; apply in_app_iff; right; left; reflexivity|]. cbn [qb_addr]. rewrite <- R. exact E.
      * exists b0. split; [apply in_app_iff; right; exact IN| exact E].
    + exists st. split; [left; reflexivity|]. cbn. repeat split; reflexivity.
    + intros b' IN. left. cbn [as_tq as_gq set_tq qc_list] in IN. apply in_app_iff in IN. destruct IN as [IN|IN].
      * apply in_app_iff in IN. destruct IN as [IN|[<-|[]]].
        -- exists b'. split; [| reflexivity]. apply in_app_iff. left.
           destruct (qc_list (as_tq st)) as [|b1 l]; [destruct IN|]. apply (firstn_skipn_In (b1 :: l) (length (b1 :: l) - 1)). left. exact IN.
        -- destruct (qc_list (as_tq st)) as [|b1 l] eqn:TL; [discriminate NN|].
           exists (last (b1 :: l) (mkQB 0 0 0 [])). split; [| reflexivity]. apply in_app_iff. left.
           assert (LIN : forall (l0 : list qbatch) z d, In (last (z :: l0) d) (z :: l0)).
           { clear. induction l0 as [|w l0 IH]; intros z d; [left; reflexivity| right; apply IH]. }
           apply LIN.
      * exists b'. split; [apply in_app_iff; right; exact IN| reflexivity].
Qed.

(* [comment removed for export] *)
Lemma cb_recycle_list_complete : forall ms st X racc st' racc',
  free_env st -> COMPLETE st X -> cb_recycle_list st ms racc = Some (st', racc') ->
  COMPLETE st' X /\ free_env st' /\ as_space_beg st' = as_space_beg st /\ as_tq st' = as_tq st /\ as_gq st' = as_gq st
  /\ (forall ch, In ch (chunk_list st') -> In ch (chunk_list st)) /\ regs_am_same st' st.
Proof.
  induction ms as [|m ms IH]; intros st X racc st' racc' FE CO H; cbn [cb_recycle_list] in H.
  - injection H as <- <-. split; [exact CO|]. split; [exact FE|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [intros ch IN; exact IN| apply regs_am_same_refl].
  - destruct (cb_recycle st m) as [[st1 ev1]|] eqn:R; [| discriminate H].
    destruct (cb_recycle_complete st X m st1 ev1 FE CO R) as (CO1 & SUB1 & SB1 & LR1 & LC1 & K1 & TQ1 & GQ1 & RS1).
    assert (FE1 : free_env st1) by (apply (free_env_transfer st st1 SB1 LR1 LC1 K1); [intros ch IN; left; exact (SUB1 ch IN)| exact FE]).
    destruct (IH st1 X _ st' racc' FE1 CO1 H) as (CO' & FE' & SB' & TQ' & GQ' & SUB' & RS').
    rewrite SB1 in SB'. rewrite TQ1 in TQ'. rewrite GQ1 in GQ'. split; [exact CO'|]. split; [exact FE'|]. split; [exact SB'|]. split; [exact TQ'|]. split; [exact GQ'|].
    split; [intros ch IN; apply SUB1; apply SUB'; exact IN|]. eapply regs_am_same_trans; [exact RS'| exact RS1].
Qed.

Lemma xbat_cons_xadd : forall b r X c, 1 <= c < kNumClasses -> forall x, In x (xbat (b :: r) X c) -> In x (xadd (xbat r X) kBatchClass (qb_addr b) c).
Proof. intros b r X c Hc x. unfold xbat, xadd. destruct (c =? kBatchClass); cbn; tauto. Qed.

(* [comment removed for export] *)
Lemma do_recycle_complete : forall bs st X racc st' racc',
  free_env st -> (forall b, In b bs -> batch_slot_ok st b) -> COMPLETE st (xbat bs X) ->
  do_recycle st bs racc = Some (st', racc') ->
  COMPLETE st' X /\ free_env st' /\ as_space_beg st' = as_space_beg st /\ as_tq st' = as_tq st /\ as_gq st' = as_gq st
  /\ (forall ch, In ch (chunk_list st') -> In ch (chunk_list st)) /\ regs_am_same st' st.
Proof.
  induction bs as [|b r IH]; intros st X racc st' racc' FE BOK CO H; cbn [do_recycle] in H.
  - injection H as <- <-. split; [| split; [exact FE| split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity|]; split; [intros ch IN; exact IN| apply regs_am_same_refl]]].
    apply (COMPLETE_Xext st (xbat [] X) X); [| exact CO]. intros c Hc x. rewrite xbat_nil. tauto.
  - destruct (cb_recycle_list st (qb_chunks b) racc) as [[st1 racc1]|] eqn:CL; [| discriminate H].
    destruct (cb_recycle_list_complete _ _ _ _ _ _ FE CO CL) as (CO1 & FE1 & SB1 & TQ1 & GQ1 & SUB1 & RS1).
    destruct (negb (in_primary st1 (qb_addr b))); [discriminate H|].
    destruct (cache_dealloc st1 _ _) as [[st2 ev2]|] eqn:CD; [| discriminate H].
    destruct (BOK b ltac:(left; reflexivity)) as (LE & MD & PR & CL24).
    assert (CL24' : class_of_addr st1 (qb_addr b) = kBatchClass) by (unfold class_of_addr in *; rewrite SB1; exact CL24). rewrite CL24' in CD.
    destruct FE1 as (LR1 & LC1 & K1 & CSO1).
    assert (RB1 : region_beg st1 kBatchClass = region_beg st kBatchClass) by (unfold region_beg; rewrite SB1; reflexivity).
    pose proof (cache_dealloc_complete st1 (xbat r X) kBatchClass (qb_addr b) st2 ev2 LR1 LC1 ltac:(unfold kBatchClass; lia)
                  ltac:(rewrite RB1; exact LE) ltac:(rewrite RB1; exact MD)
                  (COMPLETE_Xext st1 _ _ (xbat_cons_xadd b r X) CO1) CD) as CO2.
    destruct (cache_dealloc_frame st1 kBatchClass (qb_addr b) st2 ev2 LR1 ltac:(unfold kBatchClass; lia) CD) as (CH2 & SB2 & LR2 & LC2 & TQ2 & GQ2 & _ & _ & RS2).
    assert (FE2 : free_env st2).
    { apply (free_env_transfer st1 st2 SB2 LR2 ltac:(rewrite LC2; exact LC1) ltac:(rewrite CH2; exact K1)); [| exact (conj LR1 (conj LC1 (conj K1 CSO1)))].
      intros ch IN. left. unfold chunk_list in IN |- *. rewrite CH2 in IN. exact IN. }
    assert (BOK2 : forall b0, In b0 r -> batch_slot_ok st2 b0).
    { intros b0 IN. pose proof (BOK b0 ltac:(right; exact IN)) as Q. unfold batch_slot_ok, in_primary, class_of_addr, region_beg in *. rewrite SB2, SB1. exact Q. }
    destruct (IH st2 X _ st' racc' FE2 BOK2 CO2 H) as (CO' & FE' & SB' & TQ' & GQ' & SUB' & RS').
    rewrite SB2, SB1 in SB'. rewrite TQ2, TQ1 in TQ'. rewrite GQ2, GQ1 in GQ'.
    split; [exact CO'|]. split; [exact FE'|]. split; [exact SB'|]. split; [exact TQ'|]. split; [exact GQ'|].
    split; [intros ch IN; apply SUB1; unfold chunk_list; rewrite <- CH2; apply SUB'; exact IN|].
    eapply regs_am_same_trans; [exact RS'|]. eapply regs_am_same_trans; [exact RS2| exact RS1].
Qed.

(* [comment removed for export] *)
Lemma merge_batches_aux_addrs : forall fuel cur rest rdone rext xb l' ex xb',
  merge_batches_aux fuel cur rest rdone rext xb = Some (l', ex, xb') ->
     (forall b, In b (cur :: rest ++ rdone ++ rext) -> In (qb_addr b) (map qb_addr (l' ++ ex)))
  /\ (forall b', In b' (l' ++ ex) -> exists b, In b (cur :: rest ++ rdone ++ rext) /\ qb_addr b' = qb_addr b).
Proof.
  induction fuel as [|fuel IH]; intros cur rest rdone rext xb l' ex xb' H; cbn [merge_batches_aux] in H; [discriminate H|].
  destruct rest as [|nx rest'].
  - injection H as <- <- <-. split.
    + intros b IN. cbn [app In] in IN. rewrite in_app_iff in IN. rewrite map_app, in_app_iff, !in_map_iff.
      destruct IN as [<-|[IN|IN]].
      * left. exists cur. split; [reflexivity|]. apply in_app_iff. right. left. reflexivity.
      * left. exists b. split; [reflexivity|]. apply in_app_iff. left. rewrite <- in_rev. exact IN.
      * right. exists b. split; [reflexivity|]. rewrite <- in_rev. exact IN.
    + intros b' IN. exists b'. split; [| reflexivity]. cbn [app In]. rewrite in_app_iff. apply in_app_iff in IN.
      destruct IN as [IN|IN].
      * apply in_app_iff in IN. destruct IN as [IN|[<-|[]]]; [right; left; rewrite <- in_rev in IN; exact IN| left; reflexivity].
      * rewrite <- in_rev in IN. right; right; exact IN.
  - destruct (qb_count cur + qb_count nx <=? kBatchCount).
    + destruct (qb_size cur <? kBatchSize); [discriminate H|].
      destruct (IH _ _ _ _ _ _ _ _ H) as [A B]. split.
      * intros b IN. cbn [app] in IN. destruct IN as [<-|[<-|IN]].
        -- exact (A (mkQB (qb_addr cur) (qb_size cur + (qb_size nx - kBatchSize)) (qb_count cur + qb_count nx) (qb_chunks cur ++ qb_chunks nx)) (or_introl eq_refl)).
        -- replace (qb_addr nx) with (qb_addr (mkQB (qb_addr nx) kBatchSize 0 [])) by reflexivity. apply A. right. rewrite !in_app_iff. right. right. left. reflexivity.
        -- apply in_app_iff in IN. destruct IN as [IN|IN].
           ++ apply (A b). right. apply in_app_iff. left. exact IN.
           ++ apply in_app_iff in IN. destruct IN as [IN|IN]; apply (A b); right; rewrite !in_app_iff; [right; left; exact IN| right; right; right; exact IN].
      * intros b' IN'. destruct (B b' IN') as (b & IN & E). cbn [In] in IN. rewrite !in_app_iff in IN. cbn [In] in IN.
        destruct IN as [<-|[IN|[IN|[<-|IN]]]].
        -- exists cur. split; [left; reflexivity| exact E].
        -- exists b. split; [right; apply in_app_iff; left; right; exact IN| exact E].
        -- exists b. split; [right; apply in_app_iff; right; apply in_app_iff; left; exact IN| exact E].
        -- exists nx. split; [right; left; reflexivity| exact E].
        -- exists b. split; [right; apply in_app_iff; right; apply in_app_iff; right; exact IN| exact E].
    + destruct (IH _ _ _ _ _ _ _ _ H) as [A B]. split.
      * intros b IN. cbn [app] in IN. destruct IN as [<-|[<-|IN]].
        -- apply A. right. rewrite !in_app_iff. right. left. left. reflexivity.
        -- apply A. left. reflexivity.
        -- apply in_app_iff in IN. destruct IN as [IN|IN]; apply A; right; rewrite !in_app_iff; [left; exact IN|].
           apply in_app_iff in IN. destruct IN as [IN|IN]; [right; left; right; exact IN| right; right; exact IN].
      * intros b' IN'. destruct (B b' IN') as (b & IN & E). cbn [In] in IN. rewrite !in_app_iff in IN. cbn [In] in IN.
        destruct IN as [<-|[IN|[[<-|IN]|IN]]].
        -- exists nx. split; [right; left; reflexivity| exact E].
        -- exists b. split; [right; apply in_app_iff; left; right; exact IN| exact E].
        -- exists cur. split; [left; reflexivity| exact E].
        -- exists b. split; [right; apply in_app_iff; right; apply in_app_iff; left; exact IN| exact E].
        -- exists b. split; [right; apply in_app_iff; right; apply in_app_iff; right; exact IN| exact E].
Qed.

Lemma merge_batches_addrs : forall q q' ex xb, merge_batches q = Some (q', ex, xb) ->
     (forall b, In b (qc_list q) -> In (qb_addr b) (map qb_addr (qc_list q' ++ ex)))
  /\ (forall b', In b' (qc_list q' ++ ex) -> exists b, In b (qc_list q) /\ qb_addr b' = qb_addr b).
Proof.
  intros q q' ex xb H. unfold merge_batches in H. destruct (qc_list q) as [|b r] eqn:QL.
  - injection H as <- <- <-. rewrite QL. cbn. split; [intros b []| intros b' []].
  - destruct (merge_batches_aux _ b r [] [] 0) as [[[l' ex'] xb']|] eqn:M; [| discriminate H]. injection H as <- <- <-. cbn [qc_list].
    destruct (merge_batches_aux_addrs _ _ _ _ _ _ _ _ _ M) as [A B]. split.
    + intros b0 IN. apply A. cbn [app]. rewrite app_nil_r. exact IN.
    + intros b' IN'. destruct (B b' IN') as (b0 & IN & E). exists b0. split; [| exact E]. cbn [app] in IN. rewrite app_nil_r in IN. exact IN.
Qed.

Lemma pop_while_split : forall fuel l bytes mn acc l2 b2 racc,
  pop_while fuel l bytes mn acc = Some (l2, b2, racc) -> exists pre, l = pre ++ l2 /\ racc = rev pre ++ acc.
Proof.
  induction fuel as [|fuel IH]; intros l bytes mn acc l2 b2 racc H; cbn [pop_while] in H; [discriminate H|].
  destruct (bytes <=? mn).
  - injection H as <- <- <-. exists []. split; reflexivity.
  - destruct l as [|b r]; [discriminate H|]. destruct (IH _ _ _ _ _ _ _ H) as (pre & -> & ->).
    exists (b :: pre). split; [reflexivity|]. cbn. rewrite <- app_assoc. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition cps_ok (st : astate) (c : Z) : Prop :=
  rg_mapped_user (get_region st c) + kUserMapSize <= kFreeArrayOffset
  /\ forall cp, In cp (rg_free_array (get_region st c)) \/ In cp (pc_chunks (get_pc st c)) ->
       0 <= cp /\ Z.shiftl cp kCompactPtrScale + class_size c <= rg_allocated_user (get_region st c) /\ Z.shiftl cp kCompactPtrScale mod class_size c = 0.

Lemma shiftl4_nonneg : forall cp, 0 <= cp -> 0 <= Z.shiftl cp kCompactPtrScale.
Proof. intros. unfold kCompactPtrScale. rewrite Z.shiftl_mul_pow2 by lia. lia. Qed.
Lemma shiftl4_mod16 : forall cp, Z.shiftl cp kCompactPtrScale mod 16 = 0.
Proof. intros. unfold kCompactPtrScale. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 4) with 16. apply Z_mod_mult. Qed.

Lemma cache_alloc_addr : forall st c st' a ev,
  cons_pre st c -> cps_ok st c -> 0 <= c ->
  cache_alloc st c = Some (st', a, ev) ->
  exists off, a = region_beg st c + off /\ 0 <= off /\ off + class_size c <= kFreeArrayOffset /\ off mod 16 = 0.
Proof.
  intros st c st' a ev (LENR & LENC & AU & AUM & Hs & Hs16 & CNT) [MUB CPS] C0 CA. unfold kUserMapSize, kFreeArrayOffset in *.
  destruct (cache_alloc_chunks st c _ _ _ LENR C0 CA) as [_ SB'].
  destruct (cache_alloc_core st c st' a ev CA) as ([CN0 CLT] & st1 & pc1 & cp & rest & CASES & PC1 & -> & ->).
  assert (Hc : 1 <= c < kNumClasses) by lia.
  exists (Z.shiftl cp kCompactPtrScale).
  assert (GOAL : 0 <= cp /\ Z.shiftl cp kCompactPtrScale + class_size c <= kFreeArrayOffset).
  { unfold kFreeArrayOffset. destruct CASES as [(PZ & taken & ev' & GFA & ->)|(PNZ & -> & ->)].
    - cbn [pc_chunks] in PC1. subst taken.
      destruct (get_from_allocator_core _ _ _ _ _ _ GFA) as (st0 & ALT & TK & ->). cbv zeta in TK.
      assert (INcp : In cp (rg_free_array (get_region st0 c))).
      { apply (firstn_skipn_In _ (Z.to_nat (max_count c / 2))). left. rewrite <- TK. left. reflexivity. }
      destruct ALT as [[-> _]|(_ & ev1 & P & _)].
      + rewrite get_region_ensure_cache_inited in INcp. destruct (CPS cp (or_introl INcp)) as (A1 & A2 & _). split; [exact A1| lia].
      + destruct (populate_free_array_core _ c _ st0 ev1 ltac:(rewrite as_regions_eci; exact LENR) ltac:(lia) P) as (mu' & mfa' & C0' & LE1 & LE2 & MU & _).
        rewrite get_region_ensure_cache_inited in C0', LE1, LE2, MU. cbv zeta in C0', LE2.
        pose proof (get_region_core_set _ _ _ _ C0' ltac:(rewrite as_regions_eci; exact LENR) ltac:(lia)) as G0. rewrite G0 in INcp. cbn [rg_free_array] in INcp.
        apply in_app_iff in INcp. destruct INcp as [NEW|OLD].
        * apply carve_asc_In in NEW. destruct NEW as (j & Hj & ->). rewrite Z2Nat.id in Hj by (apply Z.div_pos; lia).
          assert (NN : 0 <= rg_allocated_user (get_region st c) + (0 + j) * class_size c) by (clear - AU Hs Hj; nia).   (* [comment removed for export] *)
          split; [unfold kCompactPtrScale; rewrite Z.shiftr_div_pow2 by lia; apply Z.div_pos; lia|].
          rewrite shiftr4_shiftl4; [| exact NN|].
          2:{ pose proof (Z.div_mod (rg_allocated_user (get_region st c)) (class_size c) ltac:(lia)) as D1. rewrite AUM, Z.add_0_r in D1.
              pose proof (Z.div_mod (class_size c) 16 ltac:(lia)) as D2. rewrite Hs16, Z.add_0_r in D2.
              set (q := rg_allocated_user (get_region st c) / class_size c) in *. set (t := class_size c / 16) in *.
              replace (rg_allocated_user (get_region st c) + (0 + j) * class_size c) with ((t * q + j * t) * 16) by lia. apply Z_mod_mult. }
          assert (JB : (j + 1) * class_size c <= (mu' - rg_allocated_user (get_region st c)) / class_size c * class_size c) by (apply Z.mul_le_mono_nonneg_r; lia).
          unfold kFreeArrayOffset, kUserMapSize in MU. destruct MU as [->|(_ & -> & B)]; [| lia]. lia.
        * destruct (CPS cp (or_introl OLD)) as (A1 & A2 & _). split; [exact A1| lia]. 
    - rewrite PC1 in CPS. destruct (CPS cp (or_intror (or_introl eq_refl))) as (A1 & A2 & _). split; [exact A1| lia]. }
  destruct GOAL as [G1 G2]. split; [unfold compact_to_addr, region_beg; rewrite SB'; reflexivity|]. split; [apply shiftl4_nonneg; exact G1|]. split; [exact G2| apply shiftl4_mod16].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition batches_ok (st : astate) : Prop := forall b, In b (qc_list (as_tq st) ++ qc_list (as_gq st)) -> batch_slot_ok st b.

Lemma batch_slot_ok_addr : forall st st' b b', as_space_beg st' = as_space_beg st -> qb_addr b' = qb_addr b -> batch_slot_ok st b -> batch_slot_ok st' b'.
Proof. intros st st' b b' SB E Q. unfold batch_slot_ok, in_primary, class_of_addr, region_beg in *. rewrite SB, E. exact Q. Qed.

Theorem quarantine_recycle_complete : forall st X mn st' ev,
  free_env st -> batches_ok st -> COMPLETE st X -> quarantine_recycle st mn = Some (st', ev) ->
  COMPLETE st' X /\ free_env st' /\ batches_ok st' /\ as_space_beg st' = as_space_beg st /\ as_tq st' = as_tq st
  /\ (forall ch, In ch (chunk_list st') -> In ch (chunk_list st)) /\ regs_am_same st' st.
Proof.
  intros st X mn st' ev FE BQ CO H. unfold quarantine_recycle in H.
  destruct (qc_bytes (as_gq st) <? _); [discriminate H|].
  match type of H with (match ?mg with _ => _ end) = _ =>
    assert (MG : exists g1 extracted, mg = Some (g1, extracted)
              /\ (forall b, In b (qc_list (as_gq st)) -> In (qb_addr b) (map qb_addr (qc_list g1 ++ extracted)))
              /\ (forall b', In b' (qc_list g1 ++ extracted) -> exists b, In b (qc_list (as_gq st)) /\ qb_addr b' = qb_addr b));
    [| destruct MG as (g1 & extracted & EM & A1 & A2); rewrite EM in H] end.
  { match goal with |- exists g1 ex, (if ?cnd then _ else _) = _ /\ _ => destruct cnd end.
    - destruct (merge_batches (as_gq st)) as [[[g' ex] xb]|] eqn:MB; [| discriminate H].
      exists g', ex. split; [reflexivity|]. exact (merge_batches_addrs _ _ _ _ MB).
    - exists (as_gq st), []. split; [reflexivity|]. rewrite app_nil_r. split; [intros b IN; apply in_map; exact IN| intros b' IN; exists b'; split; [exact IN| reflexivity]]. }
  destruct (pop_while _ (qc_list g1) (qc_bytes g1) mn []) as [[[l2 b2] rpopped]|] eqn:PW; [| discriminate H].
  destruct (pop_while_split _ _ _ _ _ _ _ _ PW) as (pre & EG1 & ER). rewrite app_nil_r in ER. subst rpopped.
  set (st1 := set_gq st (mkQC l2 b2)) in H.
  destruct (do_recycle st1 _ []) as [[st2 racc]|] eqn:DR; [| discriminate H]. injection H as <- _.
  rewrite rev_involutive in DR.
  assert (FE1 : free_env st1) by (destruct FE as (A & B & C & D); exact (conj A (conj B (conj C D)))).
  assert (BOK1 : forall b, In b (extracted ++ pre) -> batch_slot_ok st1 b).
  { intros b IN. assert (IN' : In b (qc_list g1 ++ extracted)) by (rewrite EG1; rewrite in_app_iff in IN; rewrite in_app_iff; rewrite in_app_iff; tauto).
    destruct (A2 b IN') as (b0 & IN0 & E). apply (batch_slot_ok_addr st st1 b0 b eq_refl E). apply BQ. apply in_app_iff. right. exact IN0. }
  assert (CO1 : COMPLETE st1 (xbat (extracted ++ pre) X)).
  { apply (COMPLETE_requeue st st1 X); [repeat split; reflexivity| | exact CO].
    intros c x Hc [B|XX]; [| right; unfold xbat; destruct (c =? kBatchClass); [apply in_app_iff; right|]; exact XX].
    apply own_batch_In in B. destruct B as (-> & b & IN & <-). apply in_app_iff in IN. destruct IN as [IN|IN].
    - left. apply own_batch_In. split; [reflexivity|]. exists b. split; [apply in_app_iff; left; exact IN| reflexivity].
    - pose proof (A1 b IN) as IN1. rewrite EG1, !map_app, !in_app_iff in IN1.
      destruct IN1 as [[P|L2]|EX].
      + right. unfold xbat. rewrite Z.eqb_refl. apply in_app_iff. left. rewrite map_app, in_app_iff. right. exact P.
      + left. apply own_batch_In. split; [reflexivity|]. apply in_map_iff in L2. destruct L2 as (b' & E & IN'). exists b'. split; [apply in_app_iff; right; exact IN'| exact E].
      + right. unfold xbat. rewrite Z.eqb_refl. apply in_app_iff. left. rewrite map_app, in_app_iff. left. exact EX. }
  destruct (do_recycle_complete _ _ _ _ _ _ FE1 BOK1 CO1 DR) as (CO2 & FE2 & SB2 & TQ2 & GQ2 & SUB2 & RS2).
  split; [exact CO2|]. split; [exact FE2|]. split.
  { intros b IN. rewrite TQ2, GQ2 in IN. subst st1. cbn [as_tq as_gq set_gq qc_list] in IN. apply in_app_iff in IN. destruct IN as [IN|IN].
    - apply (batch_slot_ok_addr st st2 b b SB2 eq_refl). apply BQ. apply in_app_iff. left. exact IN.
    - assert (IN' : In b (qc_list g1 ++ extracted)) by (rewrite EG1; rewrite in_app_iff; rewrite in_app_iff; tauto).
      destruct (A2 b IN') as (b0 & IN0 & E). apply (batch_slot_ok_addr st st2 b0 b SB2 E). apply BQ. apply in_app_iff. right. exact IN0. }
  split; [exact SB2|]. split; [exact TQ2|]. split; [exact SUB2|]. eapply regs_am_same_trans; [exact RS2|]. apply regs_am_same_regions. reflexivity.
Qed.

Theorem quarantine_drain_complete : forall st X st' ev,
  free_env st -> batches_ok st -> COMPLETE st X -> quarantine_drain st = Some (st', ev) ->
  COMPLETE st' X /\ free_env st' /\ batches_ok st' /\ as_space_beg st' = as_space_beg st
  /\ (forall ch, In ch (chunk_list st') -> In ch (chunk_list st)) /\ regs_am_same st' st.
Proof.
  intros st X st' ev FE BQ CO H. unfold quarantine_drain in H.
  set (st1 := set_gq (set_tq st qcache0) _) in H.
  assert (FE1 : free_env st1) by (destruct FE as (A & B & C & D); exact (conj A (conj B (conj C D)))).
  assert (BQ1 : batches_ok st1).
  { intros b IN. subst st1. cbn [as_tq as_gq set_gq set_tq qc_list qcache0 app] in IN. apply (batch_slot_ok_addr st _ b b eq_refl eq_refl). apply BQ.
    rewrite in_app_iff in IN |- *. tauto. }
  assert (CO1 : COMPLETE st1 X).
  { apply (COMPLETE_requeue st st1 X); [repeat split; reflexivity| | exact CO]. intros c x Hc [B|XX]; [left| right; exact XX].
    apply own_batch_In in B. destruct B as (-> & b & IN & E). apply own_batch_In. split; [reflexivity|]. exists b. split; [| exact E].
    subst st1. cbn [as_tq as_gq set_gq set_tq qc_list qcache0 app]. rewrite in_app_iff in IN |- *. tauto. }
  destruct (as_qmax st <? _).
  - destruct (quarantine_recycle_complete st1 X _ st' ev FE1 BQ1 CO1 H) as (CO' & FE' & BQ' & SB' & _ & SUB' & RS').
    split; [exact CO'|]. split; [exact FE'|]. split; [exact BQ'|]. split; [exact SB'|]. split; [intros ch IN; exact (SUB' ch IN)|].
    eapply regs_am_same_trans; [exact RS'|]. apply regs_am_same_regions. reflexivity.
  - injection H as <-. split; [exact CO1|]. split; [exact FE1|]. split; [exact BQ1|]. split; [reflexivity|]. split; [intros ch IN; exact IN|].
    apply regs_am_same_regions. reflexivity.
Qed.

Lemma cons_pre_transfer : forall st st' c, as_regions st' = as_regions st -> as_cache st' = as_cache st -> cons_pre st c -> cons_pre st' c.
Proof. intros st st' c R C P. unfold cons_pre, get_region, get_pc in *. rewrite R, C. exact P. Qed.
Lemma cps_ok_transfer : forall st st' c, as_regions st' = as_regions st -> as_cache st' = as_cache st -> cps_ok st c -> cps_ok st' c.
Proof. intros st st' c R C P. unfold cps_ok, get_region, get_pc in *. rewrite R, C. exact P. Qed.

Theorem quarantine_put_complete : forall st X ch st' ev,
  free_env st -> batches_ok st -> cons_pre st kBatchClass -> cps_ok st kBatchClass -> COMPLETE st X ->
  quarantine_put st ch = Some (st', ev) ->
  COMPLETE st' X /\ free_env st' /\ batches_ok st' /\ as_space_beg st' = as_space_beg st
  /\ (forall x, In x (chunk_list st') -> In x (chunk_list st))
  /\ (regs_am_same st' st
      \/ exists st1 stc b evb, same_core st1 st /\ COMPLETE st1 X /\ cache_alloc st1 kBatchClass = Some (stc, b, evb) /\ regs_am_same st' stc).
Proof.
  intros st X ch st' ev FE BQ PRE CPS CO H. unfold quarantine_put in H.
  destruct (_ || _); [discriminate H|].
  destruct (poison_shadow st _ _ _) as [[st1 ev1]|] eqn:P1; [| discriminate H].
  pose proof (poison_shadow_core _ _ _ _ _ _ P1) as C1. pose proof C1 as (SB1 & _ & RG1 & _ & CA1 & _ & _ & CH1 & TQ1 & GQ1 & _).
  assert (FE1 : free_env st1).
  { destruct FE as (A & B & C & D). apply (free_env_transfer st st1 SB1); [rewrite RG1; exact A| rewrite CA1; exact B| rewrite CH1; exact C| | exact (conj A (conj B (conj C D)))].
    intros x IN. left. unfold chunk_list in IN |- *. rewrite CH1 in IN. exact IN. }
  assert (CO1 : COMPLETE st1 X) by (apply (COMPLETE_view st); [symmetry; apply same_core_cview; exact C1| exact CO]).
  destruct (quarantine_enqueue st1 _ _) as [[st2 ev2]|] eqn:EQ; [| discriminate H].
  pose proof (cons_pre_transfer st st1 kBatchClass RG1 CA1 PRE) as PRE1. pose proof (cps_ok_transfer st st1 kBatchClass RG1 CA1 CPS) as CPS1.
  destruct (quarantine_enqueue_complete st1 X _ _ st2 ev2 PRE1 CO1 EQ) as (CO2 & (stc & ALT & (SB2 & RG2 & CA2 & CH2) & GQ2 & SEC2 & NR2) & BADDR).
  assert (RSW : forall stz, regs_am_same stz st2 ->
            regs_am_same stz st \/ exists st1' stc' b evb, same_core st1' st /\ COMPLETE st1' X /\ cache_alloc st1' kBatchClass = Some (stc', b, evb) /\ regs_am_same stz stc').
  { intros stz RZ. destruct ALT as [->|(b & evb & CA)].
    - left. eapply regs_am_same_trans; [exact RZ|]. eapply regs_am_same_trans; [apply regs_am_same_regions; exact RG2|]. apply regs_am_same_core. exact C1.
    - right. exists st1, stc, b, evb. split; [exact C1|]. split; [exact CO1|]. split; [exact CA|]. eapply regs_am_same_trans; [exact RZ|]. apply regs_am_same_regions. exact RG2. }
  (* [comment removed for export] *)
  assert (FC : as_chunks stc = as_chunks st1 /\ as_space_beg stc = as_space_beg st1 /\ length (as_regions stc) = 32%nat /\ length (as_cache stc) = length (as_cache st1)).
  { destruct ALT as [->|(b & evb & CA)].
    - repeat split; try reflexivity. destruct FE1 as (A & _). exact A.
    - destruct FE1 as (A & _). destruct (cache_alloc_frame st1 kBatchClass stc b evb A ltac:(unfold kBatchClass; lia) CA) as (E1 & E2 & E3 & E4 & _).
      repeat split; assumption. }
  destruct FC as (CHc & SBc & LRc & LCc).
  assert (SB2' : as_space_beg st2 = as_space_beg st) by (rewrite SB2, SBc; exact SB1).
  assert (FE2 : free_env st2).
  { destruct FE1 as (A & B & C & D). apply (free_env_transfer st1 st2); [rewrite SB2; exact SBc| rewrite RG2; exact LRc| rewrite CA2, LCc; exact B| rewrite CH2, CHc; exact C| | exact (conj A (conj B (conj C D)))].
    intros x IN. left. unfold chunk_list in IN |- *. rewrite CH2, CHc in IN. exact IN. }
  assert (BQ2 : batches_ok st2).
  { intros b' IN. destruct (BADDR b' IN) as [(b0 & IN0 & E)|(stc' & evb & CA)].
    - apply (batch_slot_ok_addr st st2 b0 b' SB2' E). apply BQ. rewrite TQ1, GQ1 in IN0. exact IN0.
    - destruct FE1 as (A & _).
      destruct (cache_alloc_addr st1 kBatchClass stc' _ evb PRE1 CPS1 ltac:(unfold kBatchClass; lia) CA) as (off & E & O1 & O2 & O3).
      unfold batch_slot_ok, in_primary, class_of_addr. rewrite E. unfold region_beg. rewrite SB2', <- SB1.
      split; [lia|]. split; [replace (_ + _ + off - _) with off by lia; exact O3|].
      unfold kBatchClass, kRegionSizeLog, kSpaceSize, kFreeArrayOffset in *. rewrite Z.shiftl_mul_pow2 by lia.
      pose proof (class_size_pos24 := eq_refl : class_size 24 = 8192).
      split.
      + apply andb_true_iff. split; [apply Z.leb_le; lia| apply Z.ltb_lt; lia].
      + replace (as_space_beg st1 + 24 * 2 ^ 32 + off - as_space_beg st1) with (24 * 2 ^ 32 + off) by lia.
        rewrite Z.shiftr_div_pow2 by lia. replace ((24 * 2 ^ 32 + off) / 2 ^ 32) with 24; [reflexivity|].
        symmetry. Z.div_mod_to_equations. nia. }
  destruct (as_qcache st2 <? qc_bytes (as_tq st2)).
  - destruct (quarantine_drain st2) as [[st3 ev3]|] eqn:DR; [| discriminate H]. injection H as <- _.
    destruct (quarantine_drain_complete st2 X st3 ev3 FE2 BQ2 CO2 DR) as (CO3 & FE3 & BQ3 & SB3 & SUB3 & RS3).
    split; [exact CO3|]. split; [exact FE3|]. split; [exact BQ3|]. split; [rewrite SB3; exact SB2'|].
    split; [intros x IN; apply SUB3 in IN; unfold chunk_list in IN |- *; rewrite CH2, CHc, CH1 in IN; exact IN|].
    apply RSW. exact RS3.
  - injection H as <- _. split; [exact CO2|]. split; [exact FE2|]. split; [exact BQ2|]. split; [exact SB2'|].
    split; [intros x IN; unfold chunk_list in IN |- *; rewrite CH2, CHc, CH1 in IN; exact IN|].
    apply RSW. apply regs_am_same_refl.
Qed.

Lemma own_chunk_ext : forall a b c, as_chunks a = as_chunks b -> own_chunk a c = own_chunk b c.
Proof. intros a b c E. unfold own_chunk, chunk_list. rewrite E. reflexivity. Qed.
Lemma own_chunk_restate_len : forall st ch ch0 c, keys_ok (as_chunks st) -> In ch0 (chunk_list st) -> ch_user_beg ch = ch_user_beg ch0 -> 0 < ch_user_beg ch ->
  zlen (own_chunk (upd_chunk st ch) c) <= zlen (own_chunk st c) + 1.
Proof.
  intros st ch ch0 c K IN0 U POS. unfold own_chunk. rewrite !zlen_map.
  pose proof (NoDup_incl_length (l := filter (fun c0 : chunk => ch_class c0 =? c) (chunk_list (upd_chunk st ch)))
                               (l' := ch :: filter (fun c0 : chunk => ch_class c0 =? c) (chunk_list st))) as L.
  unfold zlen. cbn [length] in L.
  assert (ND : NoDup (filter (fun c0 : chunk => ch_class c0 =? c) (chunk_list (upd_chunk st ch)))).
  { apply NoDup_filter. apply chunk_list_nodup. apply keys_ok_upd; [exact K| exact POS]. }
  assert (INC : incl (filter (fun c0 : chunk => ch_class c0 =? c) (chunk_list (upd_chunk st ch))) (ch :: filter (fun c0 : chunk => ch_class c0 =? c) (chunk_list st))).
  { intros x Hx. apply filter_In in Hx. destruct Hx as [Hx E]. apply chunk_list_upd_iff in Hx. destruct Hx as [->|(k & Fk & NE)]; [left; reflexivity| right].
    apply filter_In. split; [| exact E]. apply chunk_list_in_iff. exists k. exact Fk. }
  specialize (L ND INC). lia.
Qed.

(* [comment removed for export] *)
Theorem am_free_full_complete : forall st X p st' ev,
  free_env st -> batches_ok st -> cons_pre st kBatchClass -> cps_ok st kBatchClass ->
  COMPLETE st X -> am_free_full st p = Some (st', ev) ->
  COMPLETE st' X /\ as_space_beg st' = as_space_beg st
  /\ (regs_am_same st' st
      \/ exists st1 stc b evb, as_regions st1 = as_regions st /\ as_cache st1 = as_cache st /\ as_tq st1 = as_tq st /\ as_gq st1 = as_gq st
           /\ zlen (own_chunk st1 kBatchClass) <= zlen (own_chunk st kBatchClass) + 1
           /\ COMPLETE st1 X /\ cache_alloc st1 kBatchClass = Some (stc, b, evb) /\ regs_am_same st' stc).
Proof.
  intros st X p st' ev FE BQ PRE CPS CO H. unfold am_free_full in H.
  match type of H with (let '(_, _) := ?x in _) = _ => destruct x as [st0 ev0] eqn:E0 end.
  assert (F0 : cview st0 = cview st /\ as_regions st0 = as_regions st /\ as_cache st0 = as_cache st /\ as_chunks st0 = as_chunks st
               /\ as_tq st0 = as_tq st /\ as_gq st0 = as_gq st /\ as_space_beg st0 = as_space_beg st).
  { destruct (as_internal_init st); injection E0 as <- _; repeat split; reflexivity. }
  destruct F0 as (CV0 & RG0 & CA0 & CH0 & TQ0 & GQ0 & SB0).
  assert (CO0 : COMPLETE st0 X) by (exact (COMPLETE_view _ _ _ (eq_sym CV0) CO)).
  destruct (p =? 0). { injection H as <- _. split; [exact CO0|]. split; [exact SB0| left; apply regs_am_same_regions; exact RG0]. }
  destruct (find_chunk (as_chunks st0) p) as [ch|] eqn:F; [| discriminate H].
  destruct (ch_state ch) eqn:STATE; [| discriminate H].
  set (ch' := mkChunk (ch_alloc_beg ch) (ch_user_beg ch) (ch_used ch) (ch_rz ch) (ch_class ch) CQuarantine) in H.
  destruct (quarantine_put (upd_chunk st0 ch') ch') as [[st2 ev2]|] eqn:QP; [| discriminate H]. injection H as <- _.
  destruct FE as (LENR & LENC & K & CSO).
  assert (K0 : keys_ok (as_chunks st0)) by (rewrite CH0; exact K).
  pose proof (find_chunk_In _ _ _ F) as INch.
  assert (POS : 0 < ch_user_beg ch) by (destruct (K0 _ _ (proj1 (chunk_list_find st0 ch K0) INch)) as [_ P]; exact P).
  assert (K1 : keys_ok (as_chunks (upd_chunk st0 ch'))) by (apply keys_ok_upd; [exact K0| exact POS]).
  assert (CO1 : COMPLETE (upd_chunk st0 ch') X).
  { apply (upd_chunk_complete_restate st0 X ch' ch K0 INch); [reflexivity| reflexivity| reflexivity| exact CO0]. }
  assert (FE1 : free_env (upd_chunk st0 ch')).
  { apply (free_env_transfer st (upd_chunk st0 ch')); [cbn; exact SB0| cbn; rewrite RG0; exact LENR| cbn; rewrite CA0; exact LENC| exact K1| | exact (conj LENR (conj LENC (conj K CSO)))].
    intros x IN. apply chunk_list_upd_iff in IN. destruct IN as [->|(k & Fk & NE)].
    - right. exists ch. split; [unfold chunk_list; rewrite <- CH0; exact INch| repeat split; reflexivity].
    - left. apply chunk_list_in_iff. exists k. rewrite <- CH0. exact Fk. }
  assert (BQ1 : batches_ok (upd_chunk st0 ch')).
  { intros b IN. cbn in IN. rewrite TQ0, GQ0 in IN. apply (batch_slot_ok_addr st _ b b); [cbn; exact SB0| reflexivity| exact (BQ b IN)]. }
  assert (PRE1 : cons_pre (upd_chunk st0 ch') kBatchClass) by (apply (cons_pre_transfer st); [cbn; exact RG0| cbn; exact CA0| exact PRE]).
  assert (CPS1 : cps_ok (upd_chunk st0 ch') kBatchClass) by (apply (cps_ok_transfer st); [cbn; exact RG0| cbn; exact CA0| exact CPS]).
  destruct (quarantine_put_complete _ X ch' st2 ev2 FE1 BQ1 PRE1 CPS1 CO1 QP) as (CO2 & _ & _ & SB2 & _ & RS).
  split; [exact CO2|]. split; [rewrite SB2; cbn; exact SB0|].
  destruct RS as [RS|(st1 & stc & b & evb & C1 & COx & CA & RS)].
  - left. eapply regs_am_same_trans; [exact RS|]. apply regs_am_same_regions. cbn. exact RG0.
  - right. exists st1, stc, b, evb. destruct C1 as (_ & _ & RG1 & _ & CA1 & _ & _ & CH1' & TQ1 & GQ1 & _). cbn in RG1, CA1, CH1', TQ1, GQ1.
    split; [rewrite RG1; exact RG0|]. split; [rewrite CA1; exact CA0|]. split; [rewrite TQ1; exact TQ0|]. split; [rewrite GQ1; exact GQ0|].
    split; [| split; [exact COx| split; [exact CA| exact RS]]].
    (* [comment removed for export] *)
    rewrite (own_chunk_ext st1 (upd_chunk st0 ch') kBatchClass CH1'). rewrite <- (own_chunk_ext st0 st kBatchClass CH0).
    apply (own_chunk_restate_len st0 ch' ch kBatchClass K0 INch eq_refl POS).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma max_count_nonneg : forall c, 0 <= max_count c.
Proof. intros c. unfold max_count, max_cached_hint. destruct (class_size c =? 0); lia. Qed.

(* [comment removed for export] *)
Lemma populate_new_bound : forall mu au mu' req s new,
  0 < s -> 0 <= au <= mu -> mu - au < s + kUserMapSize -> 0 <= req ->
  (mu' = mu \/ (mu < au + req * s /\ mu' = mu + round_up (au + req * s - mu) kUserMapSize /\ mu' <= kFreeArrayOffset)) ->
  0 <= new -> au + new * s <= mu' ->
  new <= req + 1 + kUserMapSize / s /\ mu' <= mu + req * s + kUserMapSize.
Proof.
  intros mu au mu' req s new Hs AU TAIL REQ MU NEW0 LE. unfold round_up, kUserMapSize, kFreeArrayOffset in *.
  assert (B : mu' - au < req * s + s + 262144 /\ mu' <= mu + req * s + 262144).
  { destruct MU as [->|(LT & -> & _)]; [nia|]. Z.div_mod_to_equations. nia. }
  destruct B as [B2 B3]. split; [| exact B3].
  assert (T : (new - req - 1) * s < 262144) by nia.
  Z.div_mod_to_equations. (first [clear - H0 H T Hs; nia | nia]).
Qed.

Theorem cache_alloc_ncarved : forall st X c st' a ev,
  cons_pre st c -> rg_num_freed (get_region st c) = zlen (rg_free_array (get_region st c)) ->
  rg_mapped_user (get_region st c) - rg_allocated_user (get_region st c) < class_size c + kUserMapSize ->
  0 <= c -> COMPLETE st X ->
  cache_alloc st c = Some (st', a, ev) ->
     (forall c', 0 <= c' -> c' <> c -> get_region st' c' = get_region st c')
  /\ (ncarved st' c = ncarved st c
      \/ ncarved st' c <= max_count c + 2 + kUserMapSize / class_size c + zlen (own_chunk st c) + zlen (own_batch st c) + zlen (X c))
  /\ rg_mapped_user (get_region st' c) <= rg_mapped_user (get_region st c) + max_count c * class_size c + kUserMapSize.
Proof.
  intros st X c st' a ev (LENR & LENC & AU & AUM & Hs & Hs16 & CNT) NF TAIL C0 CO CA.
  destruct (cache_alloc_core st c st' a ev CA) as ([CN0 CLT] & st1 & pc1 & cp & rest & CASES & PC1 & -> & ->).
  assert (Hc : 1 <= c < kNumClasses) by lia. assert (Hc0 : 0 <= c < kNumClasses) by lia. pose proof (max_count_nonneg c) as MC0.
  assert (KU : 0 <= kUserMapSize / class_size c) by (apply Z.div_pos; unfold kUserMapSize; lia).
  unfold ncarved.
  destruct CASES as [(PZ & taken & ev' & GFA & ->)|(PNZ & -> & ->)].
  2:{ (* [comment removed for export] *)
      split; [intros c' H1 H2; rewrite get_region_set_pc; reflexivity|]. rewrite !get_region_set_pc.
      assert (P0 : 0 <= max_count c * class_size c) by (apply Z.mul_nonneg_nonneg; lia).
      split; [left; reflexivity| unfold kUserMapSize; lia]. }
  destruct (get_from_allocator_core _ _ _ _ _ _ GFA) as (st0 & ALT & TK & ->).
  assert (CO0 : COMPLETE (ensure_cache_inited st) X) by (apply (COMPLETE_view st); [symmetry; apply cview_ensure_cache_inited| exact CO]).
  destruct ALT as [[-> LE]|(LT & ev1 & P & LE)].
  - (* [comment removed for export] *)
    split. { intros c' H1 H2. rewrite get_region_set_pc, (get_region_set_region_neq _ c c' _ C0 H1 H2). apply get_region_ensure_cache_inited. }
    rewrite !get_region_set_pc, (get_region_set_region_eq _ c _ ltac:(rewrite as_regions_eci; exact LENR) Hc0). cbn [rg_allocated_user rg_mapped_user].
    rewrite !get_region_ensure_cache_inited. assert (P0 : 0 <= max_count c * class_size c) by (apply Z.mul_nonneg_nonneg; lia).
    split; [left; reflexivity| unfold kUserMapSize; lia].
  - destruct (populate_complete (ensure_cache_inited st) X c _ st0 ev1 ltac:(rewrite as_regions_eci; exact LENR) Hc
                ltac:(rewrite get_region_ensure_cache_inited; exact AU) ltac:(rewrite get_region_ensure_cache_inited; exact AUM) Hs Hs16 CO0 P)
      as (_ & (new & NEW0 & NC & AUE & MLE & AUM' & MU & _ & NFE) & OTH & _ & _ & LR0 & _).
    rewrite !get_region_ensure_cache_inited in *.
    split. { intros c' H1 H2. rewrite get_region_set_pc, (get_region_set_region_neq st0 c c' _ C0 H1 H2). rewrite (proj2 (OTH c' H1 H2)). apply get_region_ensure_cache_inited. }
    rewrite !get_region_set_pc, (get_region_set_region_eq st0 c _ LR0 Hc0). cbn [rg_allocated_user rg_mapped_user].
    destruct (populate_new_bound (rg_mapped_user (get_region st c)) (rg_allocated_user (get_region st c)) (rg_mapped_user (get_region st0 c))
                (max_count c / 2 - rg_num_freed (get_region st c)) (class_size c) new Hs AU TAIL ltac:(pose proof (zlen_nonneg (rg_free_array (get_region st c))); lia) MU NEW0 ltac:(rewrite <- AUE; exact AUM'))
      as [NB1 NB3].
    assert (P1 : (max_count c / 2 - rg_num_freed (get_region st c)) * class_size c <= max_count c * class_size c).
    { apply Z.mul_le_mono_nonneg_r; [lia|]. pose proof (zlen_nonneg (rg_free_array (get_region st c))). lia. }
    split; [| lia].
    right. rewrite (ncarved_view (ensure_cache_inited st) st c (cview_ensure_cache_inited st)) in NC.
    change (rg_allocated_user (get_region st0 c) / class_size c) with (ncarved st0 c). rewrite NC.
    (* [comment removed for export] *)
    pose proof (COMPLETE_count st X c CO Hc Hs ltac:(unfold ncarved; apply Z.div_pos; lia)) as CNTB.
    unfold owners in CNTB. rewrite !length_app, !Nat2Z.inj_add in CNTB. unfold own_free, own_cache in CNTB. rewrite !length_map in CNTB.
    assert (PCE : pc_chunks (get_pc st c) = []).
    { rewrite PZ in CNT. destruct (pc_chunks (get_pc st c)); [reflexivity| rewrite zlen_cons in CNT; pose proof (zlen_nonneg l); lia]. }
    rewrite PCE in CNTB. cbn [length] in CNTB. unfold zlen in NF |- *. rewrite <- NF in CNTB.
    assert (MC2 : max_count c / 2 <= max_count c) by lia. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition fclass (u : Z) : Z := class_id (rq_needed (compute_req u)).
(* [comment removed for export] *)
Definition mused_table : list Z :=
  [0;1;17;49;65;0;97;129;161;193;225;257;289;321;353;385;417;449;641;897;1409;1921;2945;3969;5889;7937;12033;16129;24065;32257;48129;0].
Definition mused (c : Z) : Z := znth mused_table (Z.to_nat c) 0.

Fixpoint check_mused (u : Z) (n : nat) : bool :=
  match n with
  | O => true
  | S k => (negb (rq_primary (compute_req u)) || ((1 <=? mused (fclass u)) && (mused (fclass u) <=? u))) && check_mused (u + 1) k
  end.
Lemma check_mused_sound : forall n u0 u, check_mused u0 n = true -> u0 <= u < u0 + Z.of_nat n ->
  rq_primary (compute_req u) = true -> 1 <= mused (fclass u) <= u.
Proof.
  induction n as [|n IH]; intros u0 u C R P; [lia|]. cbn [check_mused] in C. apply andb_true_iff in C. destruct C as [C1 C2].
  destruct (Z.eq_dec u u0) as [->|NE].
  - rewrite P in C1. cbn [negb orb] in C1. apply andb_true_iff in C1. destruct C1 as [A B]. apply Z.leb_le in A. apply Z.leb_le in B. lia.
  - apply (IH (u0 + 1) u C2); [rewrite Nat2Z.inj_succ in R; lia| exact P].
Qed.
(* [comment removed for export] *)
Definition mused_step (u : Z) : bool :=
  negb (rq_primary (compute_req u)) || ((1 <=? mused (fclass u)) && (mused (fclass u) <=? u)).
Definition mused_step_f (u : Z) : bool :=
  let needed0 := Z.shiftl (Z.shiftr (Z.max u 8 + 8 - 1) 3) 3 + rz_size u in
  if needed0 <=? kMaxSize then (let m := mused (class_id needed0) in (1 <=? m) && (m <=? u)) else true.
Lemma mused_step_f_eq : forall u, mused_step u = mused_step_f u.
Proof.
  intros u. unfold mused_step, mused_step_f, fclass, compute_req. cbn [rq_primary rq_needed]. cbv zeta.
  assert (R : round_up (Z.max u 8) 8 = Z.shiftl (Z.shiftr (Z.max u 8 + 8 - 1) 3) 3).
  { unfold round_up. rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by (clear; lia). reflexivity. }
  rewrite R. destruct (Z.shiftl (Z.shiftr (Z.max u 8 + 8 - 1) 3) 3 + rz_size u <=? kMaxSize); reflexivity.
Qed.
Fixpoint check_mused_g (f : Z -> bool) (u : Z) (n : nat) : bool :=
  match n with O => true | S k => f u && check_mused_g f (u + 1) k end.
Lemma check_mused_g_eq : forall n u, check_mused u n = check_mused_g mused_step u n.
Proof. induction n as [|n IH]; intros u; [reflexivity|]. cbn [check_mused check_mused_g]. rewrite IH. reflexivity. Qed.
Lemma check_mused_g_ext : forall f g, (forall u, f u = g u) -> forall n u, check_mused_g f u n = check_mused_g g u n.
Proof. intros f g E. induction n as [|n IH]; intros u; [reflexivity|]. cbn [check_mused_g]. rewrite E, IH. reflexivity. Qed.
Lemma check_mused_f_ok : check_mused_g mused_step_f 1 65536 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma check_mused_ok : check_mused 1 65536 = true.
Proof. rewrite check_mused_g_eq, (check_mused_g_ext _ _ mused_step_f_eq). exact check_mused_f_ok. Qed.
Lemma not_primary_large : forall u, 65536 < u -> rq_primary (compute_req u) = false.
Proof.
  intros u Hu. unfold compute_req. cbn [rq_primary]. apply Z.leb_gt. unfold kMaxSize, round_up. pose proof (rz_size_facts u) as [RZ _].
  Z.div_mod_to_equations. lia.
Qed.
(* [comment removed for export] *)
Theorem mused_ok : forall u, 1 <= u -> rq_primary (compute_req u) = true -> 1 <= mused (fclass u) <= u.
Proof.
  intros u Hu P. destruct (Z.le_gt_cases u 65536) as [LE|GT].
  - apply (check_mused_sound 65536 1 u check_mused_ok); [| exact P]. replace (1 + Z.of_nat 65536) with 65537 by (vm_compute; reflexivity). lia.
  - rewrite (not_primary_large u GT) in P. discriminate P.
Qed.

(* [comment removed for export] *)
Definition LIVEB : Z := 2850.                                        (* [comment removed for export] *)
Definition QTOT : Z := kQuarantineMaxSize + kMaxCacheSize.           (* [comment removed for export] *)
Definition CHB (c : Z) : Z := LIVEB + 2 + QTOT / (mused c + 8).      (* [comment removed for export] *)
Definition NBB : Z := QTOT / kBatchSize + 2.                         (* [comment removed for export] *)
Definition CAP (c : Z) : Z :=
  max_count c + 2 + kUserMapSize / class_size c + CHB c + (if c =? kBatchClass then NBB else 0).
Definition NUM (st : astate) : Prop := forall c, 1 <= c < kNumClasses -> ncarved st c <= CAP c.

(* [comment removed for export] *)
Definition MUB (c : Z) : Z := class_size c * (CAP c + 2) + kUserMapSize.
(* [comment removed for export] *)
Definition UB (c : Z) : Z := MUB c + kFreeArraySize + 40960 * (MUB c / 262144 + kFreeArraySize / 262144).
Definition B0 : Z := csum UB 1 31.

Lemma B0_val : B0 + 2^24 <= B_PRIM.
Proof. vm_compute. discriminate. Qed.
Lemma MUB_room : forall c, 1 <= c < kNumClasses -> 1 <= mused c -> MUB c + 2 * kUserMapSize <= kFreeArrayOffset.
Proof.
  intros c Hc M. unfold kNumClasses in Hc.
  assert (E : exists k, c = Z.of_nat k /\ (k < 32)%nat) by (exists (Z.to_nat c); split; [lia| lia]).
  destruct E as (k & -> & Hk).
  do 32 (destruct k as [|k]; [vm_compute in M |- *; first [lia | discriminate] |]). lia.
Qed.

(* [comment removed for export] *)
Theorem pusage_bound : forall st,
  NUM st ->
  (forall c, 1 <= c < kNumClasses -> let r := get_region st c in
      0 < class_size c /\ 0 <= rg_allocated_user r <= rg_mapped_user r
      /\ rg_mapped_user r - rg_allocated_user r < class_size c + kUserMapSize
      /\ 0 <= rg_mapped_free_array r <= kFreeArraySize) ->
  pusage st <= B0.
Proof.
  intros st NM SH. unfold pusage, B0. apply csum_le. intros c Hc. change (1 + Z.of_nat 31) with 32 in Hc.
  pose proof (NM c Hc) as N. destruct (SH c Hc) as (Hs & AU & TAIL & MFA). unfold reg_usage, UB, MUB. cbv zeta.
  unfold ncarved in N. unfold kUserMapSize, kFreeArraySize in *.
  set (r := get_region st c) in *. set (s := class_size c) in *.
  assert (MU : rg_mapped_user r <= s * (CAP c + 2) + 262144).
  { pose proof (Z.div_mod (rg_allocated_user r) s ltac:(lia)) as D. pose proof (Z.mod_pos_bound (rg_allocated_user r) s Hs).
    assert (M1 : s * (rg_allocated_user r / s) <= s * CAP c) by (apply Z.mul_le_mono_nonneg_l; lia). lia. }
  assert (D1 : rg_mapped_user r / 262144 <= (s * (CAP c + 2) + 262144) / 262144) by (apply Z.div_le_mono; lia).
  assert (D2 : rg_mapped_free_array r / 262144 <= 536870912 / 262144) by (apply Z.div_le_mono; lia).
  lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition PINV (st : astate) : Prop := COMPLETE st noX /\ NUM st.

Lemma COMPLETE_init_q : forall rb sb pa env ts qx qn qc, COMPLETE (init_state_q rb sb pa env ts qx qn qc) noX.
Proof.
  intros. intros c Hc i Hi. exfalso. unfold ncarved, get_region in Hi. cbn [as_regions init_state_q] in Hi.
  unfold kNumClasses in Hc.
  assert (E : exists k, c = Z.of_nat k /\ (k < 32)%nat) by (exists (Z.to_nat c); split; [lia| lia]).
  destruct E as (k & -> & Hk). unfold zidx in Hi. rewrite Nat2Z.id in Hi.
  do 32 (destruct k as [|k]; [cbn in Hi; rewrite Zdiv_0_l in Hi; lia|]). lia.
Qed.
Lemma NUM_init_q : forall rb sb pa env ts qx qn qc, NUM (init_state_q rb sb pa env ts qx qn qc).
Proof.
  intros. intros c Hc. unfold ncarved, get_region. cbn [as_regions init_state_q]. unfold kNumClasses in Hc.
  assert (E : exists k, c = Z.of_nat k /\ (k < 32)%nat) by (exists (Z.to_nat c); split; [lia| lia]).
  destruct E as (k & -> & Hk). unfold zidx. rewrite Nat2Z.id.
  assert (CP : 0 <= CAP (Z.of_nat k)).
  { unfold CAP, CHB, NBB, QTOT, LIVEB, kUserMapSize, kQuarantineMaxSize, kMaxCacheSize, kBatchSize.
    pose proof (max_count_nonneg (Z.of_nat k)). pose proof (class_size_table_facts (Z.of_nat k) ltac:(lia)) as (CS & _).
    assert (0 <= 262144 / class_size (Z.of_nat k)) by (destruct (Z.eq_dec (class_size (Z.of_nat k)) 0) as [->|NE]; [rewrite Zdiv_0_r; lia| apply Z.div_pos; lia]).
    assert (0 <= (268435456 + 1048576) / (mused (Z.of_nat k) + 8)).
    { do 32 (destruct k as [|k]; [vm_compute; discriminate|]). lia. }
    destruct (Z.of_nat k =? kBatchClass); [| lia]. change ((268435456 + 1048576) / 8192 + 2) with 32898. lia. }
  do 32 (destruct k as [|k]; [cbn -[CAP]; rewrite Zdiv_0_l; exact CP|]). lia.
Qed.
Theorem PINV_init_q : forall rb sb pa env ts qx qn qc, PINV (init_state_q rb sb pa env ts qx qn qc).
Proof. intros. split; [apply COMPLETE_init_q| apply NUM_init_q]. Qed.
Theorem PINV_init : forall rb sb pa env ts, PINV (init_state rb sb pa env ts).
Proof. intros. apply PINV_init_q. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition allocb (ch : chunk) : bool := match ch_state ch with CAllocated => true | CQuarantine => false end.
Definition nalloc (st : astate) : Z := zlen (List.filter allocb (chunk_list st)).
(* [comment removed for export] *)
Definition batches (st : astate) : list qbatch := qc_list (as_tq st) ++ qc_list (as_gq st).

Lemma zlen_filter_le {A} : forall (f : A -> bool) l, zlen (List.filter f l) <= zlen l.
Proof. intros f l. unfold zlen. induction l as [|x l IH]; cbn; [lia|]. destruct (f x); cbn; lia. Qed.
Lemma zlen_nil {A} : zlen (@nil A) = 0. Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma zlen_filter_split {A} : forall (f g : A -> bool) l,
  zlen (List.filter f l) = zlen (List.filter (fun x => f x && g x) l) + zlen (List.filter (fun x => f x && negb (g x)) l).
Proof.
  intros f g l. induction l as [|x l IH]; [reflexivity|]. cbn [List.filter].
  destruct (f x); destruct (g x); cbn [andb negb]; rewrite ?zlen_cons; lia.
Qed.
Lemma zlen_filter_implies {A} : forall (f g : A -> bool) l, (forall x, In x l -> f x = true -> g x = true) ->
  zlen (List.filter f l) <= zlen (List.filter g l).
Proof.
  intros f g l H. induction l as [|x l IH]; [cbn; lia|]. cbn [List.filter].
  pose proof (H x (or_introl eq_refl)) as Hx. specialize (IH ltac:(intros y Hy; apply H; right; exact Hy)).
  destruct (f x) eqn:F; [rewrite (Hx eq_refl)| destruct (g x)]; rewrite ?zlen_cons; lia.
Qed.

(* [comment removed for export] *)
Lemma zlen_inj_le {A B} : forall (h : A -> B) (l : list A) (l' : list B),
  NoDup l -> (forall x y, In x l -> In y l -> h x = h y -> x = y) -> (forall x, In x l -> In (h x) l') -> zlen l <= zlen l'.
Proof.
  intros h l l' ND INJ IN. unfold zlen.
  pose proof (NoDup_incl_length (l := map h l) (l' := l')) as L.
  rewrite length_map in L. apply Nat2Z.inj_le, L.
  - apply NoDup_map_NoDup_ForallPairs; [| exact ND]. intros x y Hx Hy E. exact (INJ x y Hx Hy E).
  - intros b Hb. apply in_map_iff in Hb. destruct Hb as (x & <- & Hx). exact (IN x Hx).
Qed.

(* [comment removed for export] *)
Definition Pm (st : astate) (P : chunk -> bool) (m : Z) : bool :=
  match find_chunk (as_chunks st) (m + kChunkHeaderSize) with Some ch => P ch | None => false end.
Definition bcnt (st : astate) (P : chunk -> bool) (b : qbatch) : Z := zlen (List.filter (Pm st P) (qb_chunks b)).
Definition bused (st : astate) (l : list Z) : Z :=
  fold_right (fun m acc => match find_chunk (as_chunks st) (m + kChunkHeaderSize) with Some ch => ch_used ch | None => 0 end + acc) 0 l.

Lemma bused_ge : forall st P U l,
  (forall m ch, In m l -> find_chunk (as_chunks st) (m + kChunkHeaderSize) = Some ch -> 0 <= ch_used ch /\ (P ch = true -> U <= ch_used ch)) ->
  U * zlen (List.filter (Pm st P) l) <= bused st l.
Proof.
  intros st P U l H. induction l as [|m l IH]; [unfold zlen; cbn; lia|].
  cbn [bused fold_right List.filter]. fold (bused st l). unfold Pm at 1.
  specialize (IH ltac:(intros m' ch Hm F; apply (H m' ch); [right; exact Hm| exact F])).
  destruct (find_chunk (as_chunks st) (m + kChunkHeaderSize)) as [ch|] eqn:F.
  - destruct (H m ch (or_introl eq_refl) F) as [NN PU]. destruct (P ch) eqn:HP; [rewrite zlen_cons; specialize (PU eq_refl); nia| lia].
  - lia.
Qed.

Lemma batch_weight : forall st b P U, batch_ok st b -> 0 <= U ->
  (forall m ch, In m (qb_chunks b) -> find_chunk (as_chunks st) (m + kChunkHeaderSize) = Some ch -> 0 <= ch_used ch /\ (P ch = true -> U <= ch_used ch)) ->
  (U + 8) * bcnt st P b <= qb_size b.
Proof.
  intros st b P U BOK HU H. destruct BOK as (CNT & CB & _ & _ & _ & _ & _ & SZ & _).
  unfold bcnt. pose proof (bused_ge st P U (qb_chunks b) H) as G. fold (bused st (qb_chunks b)) in SZ. rewrite SZ.
  pose proof (zlen_filter_le (Pm st P) (qb_chunks b)) as FL. unfold kBatchSize, kBatchCount in *.
  pose proof (zlen_nonneg (List.filter (Pm st P) (qb_chunks b))). nia.
Qed.

(* [comment removed for export] *)
Fixpoint bsum (f : qbatch -> Z) (l : list qbatch) : Z := match l with [] => 0 | b :: r => f b + bsum f r end.
Lemma bsum_app : forall f l1 l2, bsum f (l1 ++ l2) = bsum f l1 + bsum f l2.
Proof. intros f l1 l2. induction l1; cbn; lia. Qed.
Lemma qc_bytes_bsum : forall st q, qcache_ok st q -> qc_bytes q = bsum qb_size (qc_list q).
Proof. intros st q [_ E]. rewrite E. clear E; induction (qc_list q) as [|b l IH]; cbn; [reflexivity| rewrite IH; reflexivity]. Qed.
Lemma bsum_le : forall f g l, (forall b, In b l -> f b <= g b) -> bsum f l <= bsum g l.
Proof. intros f g l H. induction l as [|b l IH]; cbn -[zlen]; [lia|]. pose proof (H b (or_introl eq_refl)). specialize (IH ltac:(intros; apply H; right; assumption)). lia. Qed.
Lemma bsum_mul : forall k f l, bsum (fun b => k * f b) l = k * bsum f l.
Proof. intros k f l. induction l; cbn; lia. Qed.
Lemma bsum_bcnt_flat : forall st P l, bsum (bcnt st P) l = zlen (List.filter (Pm st P) (flat_map qb_chunks l)).
Proof. intros st P l. induction l as [|b l IH]; cbn -[Pm]; [reflexivity|]. rewrite List.filter_app, zlen_app, IH. reflexivity. Qed.
Lemma bsum_const : forall k l, bsum (fun _ => k) l = k * zlen l.
Proof. intros k l. unfold zlen. induction l as [|b l IH]; cbn [bsum length]; [lia|]. rewrite Nat2Z.inj_succ. lia. Qed.

Definition QTOT' : Z := kQuarantineMaxSize + kMaxCacheSize.   (* [comment removed for export] *)

(* [comment removed for export] *)
Lemma quarantine_weight : forall st P U, WF st -> 0 <= U ->
  (forall ch, In ch (chunk_list st) -> P ch = true -> U <= ch_used ch) ->
  (U + 8) * zlen (List.filter (Pm st P) (flat_map qb_chunks (batches st))) <= QTOT.
Proof.
  intros st P U W HU HP.
  pose proof W as (_ & _ & CHK & _ & _ & _ & _ & _ & TQ & GQ & QB1 & QB2 & _ & _ & _ & _ & _ & _ & _ & _ & QMAX & _ & QC & KEYS).
  rewrite <- bsum_bcnt_flat. unfold batches. rewrite bsum_app.
  assert (BW : forall b, In b (qc_list (as_tq st) ++ qc_list (as_gq st)) -> (U + 8) * bcnt st P b <= qb_size b).
  { intros b Hb. apply batch_weight; [exact (WF_batch st b W Hb)| exact HU|].
    intros m ch Hm F. pose proof (find_chunk_In st _ _ F) as IN. pose proof (CHK ch IN) as (U1 & _). split; [lia|]. intros HPc. exact (HP ch IN HPc). }
  pose proof (bsum_le (fun b => (U + 8) * bcnt st P b) qb_size (qc_list (as_tq st)) ltac:(intros b Hb; apply BW; apply in_app_iff; left; exact Hb)) as L1.
  pose proof (bsum_le (fun b => (U + 8) * bcnt st P b) qb_size (qc_list (as_gq st)) ltac:(intros b Hb; apply BW; apply in_app_iff; right; exact Hb)) as L2.
  rewrite !bsum_mul in L1, L2. rewrite <- (qc_bytes_bsum st _ TQ) in L1. rewrite <- (qc_bytes_bsum st _ GQ) in L2.
  unfold QTOT. rewrite QMAX in QB2. rewrite QC in QB1. lia.
Qed.

(* [comment removed for export] *)
Lemma nbatches_bound : forall st, WF st -> kBatchSize * zlen (batches st) <= QTOT.
Proof.
  intros st W.
  pose proof W as (_ & _ & CHK & _ & _ & _ & _ & _ & TQ & GQ & QB1 & QB2 & _ & _ & _ & _ & _ & _ & _ & _ & QMAX & _ & QC & KEYS).
  assert (BW : forall b, In b (batches st) -> kBatchSize <= qb_size b).
  { intros b Hb. pose proof (WF_batch st b W Hb) as (CNT & CB & _ & _ & _ & _ & _ & SZ & _). rewrite SZ. fold (bused st (qb_chunks b)).
    pose proof (bused_ge st (fun _ => false) 0 (qb_chunks b)) as G.
    specialize (G ltac:(intros m ch Hm F; pose proof (CHK ch (find_chunk_In st _ _ F)) as (U1 & _); split; [lia| discriminate])). lia. }
  unfold batches in *. rewrite zlen_app.
  pose proof (bsum_le (fun _ => kBatchSize) qb_size (qc_list (as_tq st)) ltac:(intros b Hb; apply BW; apply in_app_iff; left; exact Hb)) as L1.
  pose proof (bsum_le (fun _ => kBatchSize) qb_size (qc_list (as_gq st)) ltac:(intros b Hb; apply BW; apply in_app_iff; right; exact Hb)) as L2.
  rewrite !bsum_const in *. rewrite <- (qc_bytes_bsum st _ TQ) in L1. rewrite <- (qc_bytes_bsum st _ GQ) in L2.
  unfold QTOT. rewrite QMAX in QB2. rewrite QC in QB1. lia.
Qed.

(* [comment removed for export] *)
Lemma quar_records_le : forall st P, WF st ->
  zlen (List.filter (fun ch => negb (allocb ch) && P ch) (chunk_list st)) <= zlen (List.filter (Pm st P) (flat_map qb_chunks (batches st))).
Proof.
  intros st P W.
  pose proof W as (_ & _ & CHK & INJ & _ & _ & _ & _ & _ & _ & _ & _ & _ & QIN & _).
  pose proof (WF_keys st W) as K.
  apply (zlen_inj_le ch_chunk_beg).
  - apply NoDup_filter. apply chunk_list_nodup. exact K.
  - intros x y Hx Hy E. apply filter_In in Hx as [Hx _]. apply filter_In in Hy as [Hy _]. apply (INJ x y Hx Hy). unfold ch_chunk_beg in E. lia.
  - intros x Hx. apply filter_In in Hx as [Hx Q]. apply andb_true_iff in Q as [Q1 Q2].
    assert (ST : ch_state x = CQuarantine) by (unfold allocb in Q1; destruct (ch_state x); [discriminate Q1| reflexivity]).
    destruct (QIN x Hx ST) as (b & Hb & Hm).
    apply filter_In. split; [apply in_flat_map; exists b; split; [exact Hb| exact Hm]|].
    unfold Pm, ch_chunk_beg. replace (ch_user_beg x - kChunkHeaderSize + kChunkHeaderSize) with (ch_user_beg x) by lia.
    pose proof (proj1 (chunk_list_find st x K) Hx) as F. destruct (K _ _ F) as [_ POS].
    unfold find_chunk. rewrite F. replace (ch_user_beg x <=? 0) with false by (symmetry; apply Z.leb_gt; lia). exact Q2.
Qed.

Theorem quar_count : forall st P U, WF st -> 0 <= U ->
  (forall ch, In ch (chunk_list st) -> P ch = true -> U <= ch_used ch) ->
  (U + 8) * zlen (List.filter (fun ch => negb (allocb ch) && P ch) (chunk_list st)) <= QTOT.
Proof.
  intros st P U W HU HP. pose proof (quar_records_le st P W). pose proof (quarantine_weight st P U W HU HP). nia.
Qed.

(* [comment removed for export] *)
Lemma primary_small : forall u, 1 <= u <= 64512 -> rq_primary (compute_req u) = true.
Proof.
  intros u Hu. unfold compute_req. cbn [rq_primary]. apply Z.leb_le. unfold kMaxSize, round_up, rz_size, rz_log, kMinRedzoneLog, kMaxRedzoneLog.
  repeat match goal with |- context [if ?b then _ else _] => destruct b eqn:? end;
  repeat match goal with H : (_ <=? _) = true |- _ => apply Z.leb_le in H | H : (_ <=? _) = false |- _ => apply Z.leb_gt in H end.
  all: match goal with |- context [Z.shiftl ?a ?b] => let v := eval vm_compute in (Z.shiftl a b) in change (Z.shiftl a b) with v end.
  all: Z.div_mod_to_equations; lia.
Qed.
Lemma nonprimary_used : forall u, 1 <= u -> rq_primary (compute_req u) = false -> 64513 <= u.
Proof.
  intros u Hu P. destruct (Z.le_gt_cases u 64512) as [LE|GT]; [| lia]. rewrite (primary_small u ltac:(lia)) in P. discriminate P.
Qed.

(* [comment removed for export] *)
Lemma own_chunk_split : forall st c,
  zlen (own_chunk st c) = zlen (List.filter (fun ch => (ch_class ch =? c) && allocb ch) (chunk_list st))
                        + zlen (List.filter (fun ch => negb (allocb ch) && (ch_class ch =? c)) (chunk_list st)).
Proof.
  intros st c. unfold own_chunk. rewrite zlen_map, (zlen_filter_split (fun ch => ch_class ch =? c) allocb).
  pose proof (zlen_filter_implies (fun x => (ch_class x =? c) && negb (allocb x)) (fun ch => negb (allocb ch) && (ch_class ch =? c)) (chunk_list st)
                ltac:(intros x Hx0 Hb0; apply andb_true_iff in Hb0; apply andb_true_iff; tauto)).
  pose proof (zlen_filter_implies (fun ch => negb (allocb ch) && (ch_class ch =? c)) (fun x => (ch_class x =? c) && negb (allocb x)) (chunk_list st)
                ltac:(intros x Hx0 Hb0; apply andb_true_iff in Hb0; apply andb_true_iff; tauto)). lia.
Qed.

Theorem own_chunk_bound : forall st c, WF st -> 1 <= c < kNumClasses ->
  zlen (own_chunk st c) <= nalloc st + QTOT / (mused c + 8).
Proof.
  intros st c W Hc. rewrite own_chunk_split.
  pose proof (zlen_filter_implies (fun ch => (ch_class ch =? c) && allocb ch) allocb (chunk_list st) ltac:(intros x _ H; apply andb_true_iff in H; tauto)) as L1.
  fold (nalloc st) in L1.
  assert (MU : forall ch, In ch (chunk_list st) -> (ch_class ch =? c) = true -> 1 <= mused c <= ch_used ch).
  { intros ch Hin E. apply Z.eqb_eq in E. pose proof (WF_chunk st ch W Hin) as CO. unfold chunk_ok in CO. cbv zeta in CO.
    destruct CO as (U1 & _ & _ & _ & REST). unfold ch_primary in REST. rewrite E in REST.
    destruct (Z.eqb_spec c 0) as [C0|C0]; [lia|]. cbn [negb] in REST. destruct REST as (PR & CL & _).
    replace c with (fclass (ch_used ch)) by (unfold fclass; symmetry; exact CL). apply mused_ok; [lia| exact PR]. }
  assert (M0 : 0 <= mused c).
  { unfold mused. generalize (Z.to_nat c) as k. intros k. do 32 (destruct k as [|k]; [cbn; lia|]). destruct k; cbn; lia. }
  pose proof (quar_count st (fun ch => ch_class ch =? c) (mused c) W M0 ltac:(intros ch Hin E; apply (MU ch Hin E))) as Q. cbv beta in Q.
  assert (D : zlen (List.filter (fun ch => negb (allocb ch) && (ch_class ch =? c)) (chunk_list st)) <= QTOT / (mused c + 8)).
  { apply Z.div_le_lower_bound; [lia|]. lia. }
  lia.
Qed.

(* [comment removed for export] *)
Theorem nsec_bound : forall st, WF st -> zlen (as_sec st) <= nalloc st + QTOT / 64521.
Proof.
  intros st W. pose proof W as (_ & _ & CHK & _ & SECN & _).
  rewrite <- SECN. rewrite (zlen_filter_split (fun ch => negb (ch_primary ch)) allocb).
  pose proof (zlen_filter_implies (fun ch => negb (ch_primary ch) && allocb ch) allocb (chunk_list st) ltac:(intros x _ H; apply andb_true_iff in H; tauto)) as L1.
  fold (nalloc st) in L1.
  pose proof (zlen_filter_implies (fun x => negb (ch_primary x) && negb (allocb x)) (fun ch => negb (allocb ch) && negb (ch_primary ch)) (chunk_list st)
                ltac:(intros x Hx0 Hb0; apply andb_true_iff in Hb0; apply andb_true_iff; tauto)) as L2.
  pose proof (quar_count st (fun ch => negb (ch_primary ch)) 64513 W ltac:(lia)) as Q.
  specialize (Q ltac:(intros ch Hin E; cbv beta in E; pose proof (CHK ch Hin) as CO; unfold chunk_ok in CO; cbv zeta in CO; destruct CO as (U1 & _ & _ & _ & REST);
                    destruct (ch_primary ch); [discriminate E|]; destruct REST as (PR & _); exact (nonprimary_used _ U1 PR))).
  cbv beta in Q.
  assert (D : zlen (List.filter (fun ch => negb (allocb ch) && negb (ch_primary ch)) (chunk_list st)) <= QTOT / 64521).
  { apply Z.div_le_lower_bound; [lia|]. lia. }
  lia.
Qed.

(* [comment removed for export] *)
Theorem own_batch_bound : forall st c, WF st -> zlen (own_batch st c) <= (if c =? kBatchClass then QTOT / kBatchSize else 0).
Proof.
  intros st c W. unfold own_batch. destruct (c =? kBatchClass); [| unfold zlen; cbn; lia].
  rewrite zlen_map. fold (batches st). pose proof (nbatches_bound st W). apply Z.div_le_lower_bound; [unfold kBatchSize; lia| lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma WF_lengths : forall st, WF st -> length (as_regions st) = 32%nat /\ length (as_cache st) = 32%nat.
Proof. intros st W. pose proof W as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & LR & LC & _). split; assumption. Qed.

Lemma WF_cons_pre : forall st c, WF st -> 1 <= c < kNumClasses -> cons_pre st c.
Proof.
  intros st c W Hc. destruct (WF_lengths st W) as [LR LC]. unfold kNumClasses in Hc.
  pose proof (WF_region st c W ltac:(unfold kNumClasses; lia)) as RO. pose proof (WF_cache st c W ltac:(unfold kNumClasses; lia)) as CO.
  pose proof (class_size_table_facts c ltac:(lia)) as (CS1 & CS2 & CS3 & _).
  unfold cons_pre. split; [exact LR|]. split; [exact LC|].
  split; [split; [apply (ro_alloc_nonneg _ _ RO)| apply (ro_alloc_le _ _ RO)]|].
  split; [apply (ro_alloc_mod _ _ RO); lia|]. split; [lia|]. split; [clear - CS2; Z.div_mod_to_equations; lia|]. apply (co_count _ _ CO).
Qed.

Lemma mod_lt_step : forall x a s, 0 < s -> x mod s = 0 -> a mod s = 0 -> x < a -> x + s <= a.
Proof.
  intros x a s Hs Mx Ma LT.
  pose proof (Z.div_mod x s ltac:(lia)) as Dx. pose proof (Z.div_mod a s ltac:(lia)) as Da. rewrite Mx, Z.add_0_r in Dx. rewrite Ma, Z.add_0_r in Da.
  assert (Q : x / s < a / s) by (apply (Z.mul_lt_mono_pos_l s); lia).
  assert (M : s * (x / s + 1) <= s * (a / s)) by (apply Z.mul_le_mono_nonneg_l; lia). lia.
Qed.

Lemma WF_cps_ok : forall st c, WF st -> 1 <= c < kNumClasses -> cps_ok st c.
Proof.
  intros st c W Hc. unfold kNumClasses in Hc.
  pose proof (WF_region st c W ltac:(unfold kNumClasses; lia)) as RO. pose proof (WF_cache st c W ltac:(unfold kNumClasses; lia)) as CO.
  pose proof (class_size_table_facts c ltac:(lia)) as (CS1 & CS2 & CS3 & _).
  pose proof (ro_alloc_mod _ _ RO ltac:(lia)) as AM.
  split; [apply (ro_mapped_bound _ _ RO)|].
  intros cp [Hin|Hin].
  - destruct (ro_fa_elems _ _ RO cp Hin) as (P1 & P2 & P3 & P4). split; [exact P1|]. split; [| exact P4].
    apply mod_lt_step; [lia| exact P4| exact AM| exact P2].
  - destruct (co_elems _ _ CO cp Hin) as (P1 & P2 & P3 & P4). split; [exact P1|]. split; [| exact P4].
    apply mod_lt_step; [lia| exact P4| exact AM| exact P2].
Qed.

Lemma WF_batches_ok : forall st, WF st -> batches_ok st.
Proof.
  intros st W b Hb. pose proof (WF_batch st b W Hb) as (CNT & CB & INP & COA & MOD & NN & LE & _).
  pose proof (class_size_table_facts kBatchClass ltac:(unfold kBatchClass; lia)) as (_ & CS2 & _).
  unfold batch_slot_ok. split; [lia|]. split; [| split; [exact INP| exact COA]].
  clear - MOD CS2. Z.div_mod_to_equations. lia.
Qed.

Lemma req_shape : forall u, 1 <= u ->
  rq_size (compute_req u) = u /\ rq_rz (compute_req u) = rz_size u
  /\ rq_needed (compute_req u) = round_up (Z.max u 8) 8 + rz_size u + (if rq_primary (compute_req u) then 0 else rz_size u)
  /\ (rq_primary (compute_req u) = true <-> round_up (Z.max u 8) 8 + rz_size u <= kMaxSize)
  /\ u <= round_up (Z.max u 8) 8.
Proof.
  intros u Hu. unfold compute_req. cbn [rq_size rq_rz rq_needed rq_primary].
  replace (u =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  split; [reflexivity|]. split; [reflexivity|]. split; [destruct (_ <=? _); lia|]. split; [rewrite Z.leb_le; tauto|].
  unfold round_up. Z.div_mod_to_equations. lia.
Qed.

Lemma WF_chunk_slot_ok : forall st ch, WF st -> In ch (chunk_list st) -> chunk_slot_ok st ch.
Proof.
  intros st ch W Hin. pose proof (WF_chunk st ch W Hin) as CO. unfold chunk_ok in CO. cbv zeta in CO.
  destruct CO as (U1 & U2 & RZ & UB & REST). pose proof (rz_size_facts (ch_used ch)) as (RZB & _ & _).
  assert (ERZ : ch_rz ch = rz_size (ch_used ch)) by (rewrite RZ; reflexivity).
  assert (ECB : ch_chunk_beg ch = ch_alloc_beg ch + ch_rz ch - 16) by (unfold ch_chunk_beg, kChunkHeaderSize; lia).
  unfold chunk_slot_ok. destruct (ch_primary ch) eqn:PRIM.
  - destruct REST as (PR & CL & COA & INP & MOD & NN & LE & NEED).
    pose proof (req_shape (ch_used ch) U1) as (Q1 & Q2 & Q3 & Q4 & Q5). rewrite PR in Q3. pose proof (proj1 Q4 PR) as Q6. unfold kMaxSize in Q6.
    assert (Hc : 1 <= ch_class ch < 32).
    { rewrite CL. apply class_id_range. rewrite Q3. lia. }
    pose proof (class_size_table_facts (ch_class ch) ltac:(lia)) as (CS1 & CS2 & CS3 & _).
    assert (NEEDGE : ch_rz ch - 16 < class_size (ch_class ch)) by lia.
    set (off := ch_chunk_beg ch - region_beg st (ch_class ch)).
    assert (OFF : 0 <= off < 2 ^ 32).
    { subst off. rewrite ECB. pose proof (ro_alloc_le _ _ (WF_region st (ch_class ch) W ltac:(unfold kNumClasses; lia))).
      pose proof (ro_mapped_bound _ _ (WF_region st (ch_class ch) W ltac:(unfold kNumClasses; lia))). unfold kUserMapSize, kFreeArrayOffset in *. lia. }
    replace (ch_chunk_beg ch) with (region_beg st (ch_class ch) + off) by lia.
    rewrite (in_primary_region st (ch_class ch) off ltac:(lia) OFF), (class_of_addr_region st (ch_class ch) off ltac:(lia) OFF).
    split; [| intros F; discriminate F]. intros _. unfold kNumClasses. split; [lia|]. split; [reflexivity|]. split; [lia|].
    split; [| reflexivity]. clear - MOD CS2. Z.div_mod_to_equations. lia.
  - destruct REST as (PR & INP & _). split; [intros F; discriminate F| intros _; exact INP].
Qed.

Lemma WF_free_env : forall st, WF st -> free_env st.
Proof.
  intros st W. destruct (WF_lengths st W) as [LR LC]. split; [exact LR|]. split; [exact LC|]. split; [exact (WF_keys st W)|].
  intros ch Hin. exact (WF_chunk_slot_ok st ch W Hin).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition mk_new (allocated : Z) (r : req) (cls : Z) : chunk :=
  mkChunk allocated (allocated + rq_rz r) (rq_size r) (rq_rz r) cls CAllocated.

Lemma am_malloc_k_shape : forall st n k U st' ev,
  am_malloc_k st n k = Some (U, st', ev) ->
  let r := compute_req n in
  exists st1 allocated cls,
       0 <= n /\ U = allocated + rq_rz r
    /\ same_core st' (upd_chunk st1 (mk_new allocated r cls))
    /\ (   (kMaxSize <? rq_needed r) = true /\ cls = 0 /\ (exists evL, large_allocate st (rq_needed r) k = Some (st1, allocated, evL))
        \/ (kMaxSize <? rq_needed r) = false /\ cls = class_id (rq_needed r) /\ (exists evC, cache_alloc st cls = Some (st1, allocated, evC))).
Proof.
  intros st n k U st' ev H. unfold am_malloc_k in H.
  destruct (n <? 0) eqn:NNEG; [discriminate H|]. apply Z.ltb_ge in NNEG. destruct (size_too_big _); [discriminate H|]. cbv zeta in H.
  cbv zeta. set (r := compute_req n) in *.
  match type of H with (match ?alloc with _ => _ end) = _ =>
    destruct alloc as [[[[st1 allocated] cls] ev1]|] eqn:AL; [| discriminate H] end.
  change (mkChunk allocated (allocated + rq_rz r) (rq_size r) (rq_rz r) cls CAllocated) with (mk_new allocated r cls) in H.
  set (ch := mk_new allocated r cls) in H.
  destruct (allocated + rq_needed r <? allocated + rq_rz r + rq_size r); [discriminate H|].
  assert (POST : same_core st' (upd_chunk st1 ch) /\ U = allocated + rq_rz r).
  { match type of H with (match ?s13 with _ => _ end) = _ => destruct s13 as [[st3 ev3]|] eqn:S13; [| discriminate H] end.
    assert (C3 : same_core st3 (upd_chunk st1 ch)).
    { destruct (negb (rq_primary r)).
      - destruct (actually_allocated_size _ _); [| discriminate S13].
        destruct (poison_shadow (upd_chunk st1 ch) _ _ _) as [[sa ea]|] eqn:PA; [| discriminate S13].
        destruct (poison_shadow sa _ _ _) as [[sb eb]|] eqn:PB; [| discriminate S13]. injection S13 as <- _.
        eapply same_core_trans; [exact (poison_shadow_core _ _ _ _ _ _ PB)| exact (poison_shadow_core _ _ _ _ _ _ PA)].
      - injection S13 as <- _. apply same_core_refl. }
    match type of H with (match ?s14 with _ => _ end) = _ => destruct s14 as [[st4 ev4]|] eqn:S14; [| discriminate H] end.
    assert (C4 : same_core st4 st3).
    { destruct (0 <? _); [exact (poison_shadow_core _ _ _ _ _ _ S14)| injection S14 as <- _; apply same_core_refl]. }
    match type of H with (match ?s15 with _ => _ end) = _ => destruct s15 as [[st5 ev5]|] eqn:S15; [| discriminate H] end.
    assert (C5 : same_core st5 st4).
    { destruct (negb (rq_size r =? _)); [| injection S15 as <- _; apply same_core_refl].
      destruct (negb (addr_is_in_mem _)); [discriminate S15|]. injection S15 as <- _. apply same_core_paint. }
    destruct (negb _ && _); [discriminate H|]. injection H as <- <- _.
    split; [| reflexivity]. eapply same_core_trans; [exact C5|]. eapply same_core_trans; [exact C4| exact C3]. }
  destruct POST as [CORE EU].
  exists st1, allocated, cls. split; [exact NNEG|]. split; [exact EU|]. split; [exact CORE|].
  destruct (kMaxSize <? rq_needed r) eqn:LARGE.
  - left. destruct (large_allocate st _ k) as [[[stL resL] evL]|] eqn:LA; [| discriminate AL]. injection AL as <- <- <- _.
    split; [reflexivity|]. split; [reflexivity|]. exists evL. first [exact LA| reflexivity].
  - right. destruct (cache_alloc st (class_id (rq_needed r))) as [[[stC aC] evC]|] eqn:CA; [| discriminate AL].
    injection AL as E1 E2 E3 E4. subst st1 allocated cls ev1. split; [reflexivity|]. split; [reflexivity|]. exists evC. first [exact CA| reflexivity].
Qed.

(* [comment removed for export] *)
Lemma am_malloc_k_frame : forall st n k U st' ev, WF st ->
  am_malloc_k st n k = Some (U, st', ev) ->
  let r := compute_req n in
  exists st1 allocated cls,
       same_core st' (upd_chunk st1 (mk_new allocated r cls)) /\ U = allocated + rq_rz r
    /\ as_chunks st1 = as_chunks st /\ as_tq st1 = as_tq st /\ as_gq st1 = as_gq st /\ as_space_beg st1 = as_space_beg st
    /\ length (as_regions st1) = 32%nat /\ length (as_cache st1) = 32%nat
    /\ (   ((kMaxSize <? rq_needed r) = true /\ cls = 0 /\ as_regions st1 = as_regions st)
        \/ ((kMaxSize <? rq_needed r) = false /\ cls = class_id (rq_needed r) /\ 1 <= cls < kNumClasses
            /\ (exists evC, cache_alloc st cls = Some (st1, allocated, evC)))).
Proof.
  intros st n k U st' ev W H. destruct (WF_lengths st W) as [LR LC].
  destruct (am_malloc_k_shape st n k U st' ev H) as (st1 & allocated & cls & NNEG & EU & CORE & ARMS). cbv zeta.
  exists st1, allocated, cls. split; [exact CORE|]. split; [exact EU|].
  destruct ARMS as [(LG & -> & evL & LA)|(LG & -> & evC & CA)].
  - pose proof (large_allocate_core _ _ _ _ _ _ LA) as CL.
    destruct CL as (E1 & _ & E3 & _ & E5 & _ & _ & E8 & E9 & E10 & _). cbn in E1, E3, E5, E8, E9, E10.
    split; [exact E8|]. split; [exact E9|]. split; [exact E10|]. split; [exact E1|]. split; [rewrite E3; exact LR|]. split; [rewrite E5; exact LC|].
    left. split; [exact LG|]. split; [reflexivity| exact E3].
  - assert (HC : 1 <= class_id (rq_needed (compute_req n)) < kNumClasses).
    { unfold kNumClasses. apply class_id_range. apply Z.ltb_ge in LG. unfold kMaxSize in LG.
      pose proof (compute_req_facts n NNEG) as RQ. cbv zeta in RQ. destruct RQ as (_ & RZ & RD & _ & ND & _).
      destruct (rq_primary (compute_req n)); lia. }
    destruct (cache_alloc_frame st (class_id (rq_needed (compute_req n))) st1 allocated evC LR ltac:(clear - HC; lia) CA) as (CH & SB & LR1 & LC1 & TQ & GQ & _).
    split; [exact CH|]. split; [exact TQ|]. split; [exact GQ|]. split; [exact SB|]. split; [exact LR1|]. split; [rewrite LC1; exact LC|].
    right. split; [exact LG|]. split; [reflexivity|]. split; [exact HC|]. exists evC. exact CA.
Qed.

(* [comment removed for export] *)
Lemma PINV_core : forall a b, same_core a b -> PINV b -> PINV a.
Proof.
  intros a b C [CO NM]. split; [exact (COMPLETE_view b a noX (eq_sym (same_core_cview a b C)) CO)|].
  intros c Hc. rewrite (ncarved_view a b c (same_core_cview a b C)). exact (NM c Hc).
Qed.
Lemma PINV_sbs : forall a b, same_but_shadow a b -> PINV b -> PINV a.
Proof. intros a b S P. exact (PINV_core a b (same_core_sbs a b S) P). Qed.

(* [comment removed for export] *)
Lemma am_malloc_k_fresh : forall st n k U st' ev, WF st -> WF st' ->
  (forall x, In x (chunk_list st) -> ch_state x = CAllocated -> ch_user_beg x <> U) ->
  am_malloc_k st n k = Some (U, st', ev) -> fresh_key st U.
Proof.
  intros st n k U st' ev W W' NOLIVE H.
  destruct (am_malloc_k_frame st n k U st' ev W H) as (st1 & allocated & cls & CORE & EU & CH1 & TQ1 & GQ1 & _).
  pose proof CORE as (_ & _ & _ & _ & _ & _ & _ & CH' & TQ' & GQ' & _). cbn [as_chunks as_tq as_gq upd_chunk set_chunks] in CH', TQ', GQ'.
  set (chn := mk_new allocated (compute_req n) cls) in *.
  assert (UN : ch_user_beg chn = U) by (subst chn; cbn [ch_user_beg mk_new]; lia).
  assert (FN : PositiveMap.find (ckey U) (as_chunks st') = Some chn) by (rewrite CH', <- UN; apply PositiveMap.gss).
  pose proof (WF_keys st' W') as K'. destruct (K' _ _ FN) as [_ POS]. rewrite UN in POS.
  unfold fresh_key. destruct (PositiveMap.find (ckey U) (as_chunks st)) as [x|] eqn:F; [exfalso| reflexivity].
  pose proof (WF_keys st W) as K. destruct (K _ _ F) as [KE XPOS].
  assert (UX : ch_user_beg x = U) by (apply Z2Pos.inj; [lia| lia| unfold ckey in KE; congruence]).
  assert (INx : In x (chunk_list st)) by (apply chunk_list_in_iff; exists (ckey U); exact F).
  destruct (ch_state x) eqn:ST; [exact (NOLIVE x INx ST UX)|].
  pose proof W as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & QIN & _).
  destruct (QIN x INx ST) as (b & Hb & Hm).
  assert (Hb' : In b (qc_list (as_tq st') ++ qc_list (as_gq st'))) by (rewrite TQ', GQ', TQ1, GQ1; exact Hb).
  pose proof (WF_batch st' b W' Hb') as (_ & _ & _ & _ & _ & _ & _ & _ & QF).
  destruct (QF _ Hm) as (ch' & F' & ST'). unfold ch_chunk_beg in F'.
  replace (ch_user_beg x - kChunkHeaderSize + kChunkHeaderSize) with U in F' by lia.
  unfold find_chunk in F'. replace (U <=? 0) with false in F' by (symmetry; apply Z.leb_gt; lia). rewrite FN in F'.
  injection F' as <-. subst chn. cbn [ch_state mk_new] in ST'. discriminate ST'.
Qed.

(* [comment removed for export] *)
Theorem PINV_am_malloc_k : forall st n k U st' ev, WF st -> WF st' -> PINV st -> nalloc st + 1 <= LIVEB ->
  (forall x, In x (chunk_list st) -> ch_state x = CAllocated -> ch_user_beg x <> U) ->
  am_malloc_k st n k = Some (U, st', ev) -> PINV st'.
Proof.
  intros st n k U st' ev W W' PI NL NOLIVE H.
  pose proof (am_malloc_k_fresh st n k U st' ev W W' NOLIVE H) as FR. destruct PI as [CO NM].
  assert (CO' : COMPLETE st' noX) by (exact (am_malloc_k_complete st noX n k U st' ev (fun c Hc => WF_cons_pre st c W Hc) CO H FR)).
  split; [exact CO'|].
  destruct (am_malloc_k_frame st n k U st' ev W H) as (st1 & allocated & cls & CORE & EU & CH1 & TQ1 & GQ1 & SB1 & LR1 & LC1 & ARMS).
  assert (RG' : as_regions st' = as_regions st1) by (destruct CORE as (_ & _ & E & _); exact E).
  intros c Hc. unfold ncarved. unfold get_region. rewrite RG'. fold (get_region st1 c). fold (ncarved st1 c).
  destruct ARMS as [(LG & -> & RG1)|(LG & -> & HC & evC & CA)].
  - unfold ncarved, get_region. rewrite RG1. apply (NM c Hc).
  - set (c0 := class_id (rq_needed (compute_req n))) in *.
    pose proof (WF_region st c0 W ltac:(unfold kNumClasses in HC; unfold kNumClasses; lia)) as RO.
    pose proof (class_size_table_facts c0 ltac:(unfold kNumClasses in HC; lia)) as (CS1 & _ & CS3 & _).
    assert (TAIL : rg_mapped_user (get_region st c0) - rg_allocated_user (get_region st c0) < class_size c0 + kUserMapSize).
    { pose proof (ro_tail_small _ _ RO ltac:(lia)) as T. destruct (rg_allocated_user (get_region st c0) =? 0); unfold kUserMapSize in *; lia. }
    destruct (cache_alloc_ncarved st noX c0 st1 allocated evC (WF_cons_pre st c0 W HC) (ro_numfreed _ _ RO) TAIL ltac:(lia) CO CA) as (OTH & NC & _).
    destruct (Z.eq_dec c c0) as [->|NE].
    + destruct NC as [E|B]; [rewrite E; apply (NM c0 Hc)|].
      pose proof (own_chunk_bound st c0 W Hc) as OC. pose proof (own_batch_bound st c0 W) as OB.
      unfold CAP, CHB, NBB. replace (zlen (noX c0)) with 0 in B by reflexivity.
      assert (D0 : 0 <= QTOT / kBatchSize) by (apply Z.div_pos; unfold QTOT, kBatchSize, kQuarantineMaxSize, kMaxCacheSize; lia).
      destruct (c0 =? kBatchClass); lia.
    + unfold ncarved. rewrite (OTH c ltac:(lia) NE). apply (NM c Hc).
Qed.

Lemma ncarved_regs : forall a b c, regs_am_same a b -> ncarved a c = ncarved b c.
Proof. intros a b c R. unfold ncarved. destruct (R c) as [E _]. rewrite E. reflexivity. Qed.

Theorem PINV_am_free_full : forall st p st' ev, WF st -> PINV st -> nalloc st <= LIVEB ->
  am_free_full st p = Some (st', ev) -> PINV st'.
Proof.
  intros st p st' ev W [CO NM] NL H.
  assert (HC : 1 <= kBatchClass < kNumClasses) by (unfold kBatchClass, kNumClasses; lia).
  destruct (am_free_full_complete st noX p st' ev (WF_free_env st W) (WF_batches_ok st W) (WF_cons_pre st kBatchClass W HC) (WF_cps_ok st kBatchClass W HC) CO H)
    as (CO' & SB' & CASES).
  split; [exact CO'|]. intros c Hc.
  destruct CASES as [RS|(st1 & stc & b & evb & RG1 & CA1 & TQ1 & GQ1 & OC1 & CO1 & CA & RS)].
  - rewrite (ncarved_regs st' st c RS). exact (NM c Hc).
  - rewrite (ncarved_regs st' stc c RS).
    pose proof (WF_region st kBatchClass W ltac:(unfold kNumClasses in HC; unfold kNumClasses; lia)) as RO.
    pose proof (class_size_table_facts kBatchClass ltac:(unfold kNumClasses in HC; lia)) as (CS1 & _ & CS3 & _).
    assert (GR1 : forall c', get_region st1 c' = get_region st c') by (intros c'; unfold get_region; rewrite RG1; reflexivity).
    assert (PRE1 : cons_pre st1 kBatchClass).
    { pose proof (WF_cons_pre st kBatchClass W HC) as (L1 & L2 & P3 & P4 & P5 & P6 & P7). unfold cons_pre.
      rewrite RG1, CA1, !GR1. unfold get_pc. rewrite CA1. repeat split; try assumption. exact (proj1 P3). exact (proj2 P3). }
    assert (TAIL : rg_mapped_user (get_region st1 kBatchClass) - rg_allocated_user (get_region st1 kBatchClass) < class_size kBatchClass + kUserMapSize).
    { rewrite GR1. pose proof (ro_tail_small _ _ RO ltac:(lia)) as T. destruct (rg_allocated_user (get_region st kBatchClass) =? 0); unfold kUserMapSize in *; lia. }
    destruct (cache_alloc_ncarved st1 noX kBatchClass stc b evb PRE1 ltac:(rewrite GR1; exact (ro_numfreed _ _ RO)) TAIL ltac:(lia) CO1 CA) as (OTH & NC & _).
    destruct (Z.eq_dec c kBatchClass) as [->|NE].
    + destruct NC as [E|B]; [rewrite E; unfold ncarved; rewrite GR1; apply (NM _ Hc)|].
      pose proof (own_chunk_bound st kBatchClass W Hc) as OC. pose proof (own_batch_bound st kBatchClass W) as OB.
      assert (OB1 : own_batch st1 kBatchClass = own_batch st kBatchClass) by (unfold own_batch; rewrite TQ1, GQ1; reflexivity). rewrite OB1 in B.
      unfold CAP, CHB, NBB. replace (zlen (noX kBatchClass)) with 0 in B by reflexivity.
      assert (D0 : 0 <= QTOT / kBatchSize) by (apply Z.div_pos; unfold QTOT, kBatchSize, kQuarantineMaxSize, kMaxCacheSize; lia).
      rewrite Z.eqb_refl in OB |- *. lia.
    + unfold ncarved. rewrite (OTH c ltac:(lia) NE), GR1. apply (NM c Hc).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Theorem PROOM_of_PINV : forall st, WF st -> PINV st -> pusage st + 2 ^ 24 <= B_PRIM.
Proof.
  intros st W [_ NM]. pose proof B0_val as BV.
  assert (PB : pusage st <= B0); [| lia].
  apply pusage_bound; [exact NM|]. intros c Hc. unfold kNumClasses in Hc.
  pose proof (WF_region st c W ltac:(unfold kNumClasses; lia)) as RO. pose proof (class_size_table_facts c ltac:(lia)) as (CS1 & _ & CS3 & _).
  cbv zeta. split; [lia|]. split; [split; [apply (ro_alloc_nonneg _ _ RO)| apply (ro_alloc_le _ _ RO)]|].
  split.
  - pose proof (ro_tail_small _ _ RO ltac:(lia)) as T. destruct (rg_allocated_user (get_region st c) =? 0); unfold kUserMapSize in *; lia.
  - pose proof (ro_fa_le _ _ RO). pose proof (ro_fa_bound _ _ RO). pose proof (ro_numfreed _ _ RO). pose proof (zlen_nonneg (rg_free_array (get_region st c))). lia.
Qed.

Theorem ROOM_of_PINV : forall st c, WF st -> PINV st -> 1 <= c < kNumClasses -> 1 <= mused c ->
  rg_mapped_user (get_region st c) + 2 * kUserMapSize <= kFreeArrayOffset.
Proof.
  intros st c W [_ NM] Hc M. pose proof (MUB_room c Hc M) as MR. pose proof (NM c Hc) as N. unfold kNumClasses in Hc.
  pose proof (WF_region st c W ltac:(unfold kNumClasses; lia)) as RO. pose proof (class_size_table_facts c ltac:(lia)) as (CS1 & _ & CS3 & _).
  pose proof (ro_tail_small _ _ RO ltac:(lia)) as T. pose proof (ro_alloc_nonneg _ _ RO) as A0.
  unfold ncarved in N. unfold MUB in MR.
  pose proof (Z.div_mod (rg_allocated_user (get_region st c)) (class_size c) ltac:(lia)) as D. rewrite (ro_alloc_mod _ _ RO ltac:(lia)), Z.add_0_r in D.
  assert (M1 : class_size c * (rg_allocated_user (get_region st c) / class_size c) <= class_size c * CAP c) by (apply Z.mul_le_mono_nonneg_l; lia).
  destruct (rg_allocated_user (get_region st c) =? 0); unfold kUserMapSize in *; lia.
Qed.

Theorem NSEC_of_WF : forall st, WF st -> nalloc st + 1 <= LIVEB -> zlen (as_sec st) <= 7040.   (* [comment removed for export] *)
Proof.
  intros st W NL. pose proof (nsec_bound st W) as NS. unfold LIVEB in NL.
  assert (Q : QTOT / 64521 <= 4177) by (unfold QTOT, kQuarantineMaxSize, kMaxCacheSize; apply Z.div_le_upper_bound; lia). lia.
Qed.

(* [comment removed for export] *)
Lemma mused_class_pos : forall size, 1 <= size -> rq_primary (compute_req size) = true ->
  1 <= mused (class_id (rq_needed (compute_req size))).
Proof. intros size Hs P. pose proof (mused_ok size Hs P) as [M _]. unfold fclass in M. exact M. Qed.

(* [comment removed for export] *)
Lemma cache_alloc_ptr_array : forall st c st' a ev, length (as_regions st) = 32%nat -> 0 <= c < kNumClasses ->
  cache_alloc st c = Some (st', a, ev) -> as_ptr_array st' = as_ptr_array st.
Proof.
  intros st c st' a ev LR Hc CA.
  destruct (cache_alloc_core st c st' a ev CA) as (_ & st1 & pc1 & cp & rest & CASES & PC1 & -> & ->). cbn [as_ptr_array set_pc].
  destruct CASES as [(_ & taken & ev' & GFA & ->)|(_ & -> & ->)]; [| reflexivity].
  destruct (get_from_allocator_core _ _ _ _ _ _ GFA) as (st0 & ALT & _ & ->). cbn [as_ptr_array set_region].
  destruct ALT as [[-> _]|(_ & ev1 & P & _)]; [unfold ensure_cache_inited; destruct (as_cache_inited st); reflexivity|].
  destruct (populate_free_array_core (ensure_cache_inited st) c _ st0 ev1 ltac:(rewrite as_regions_eci; exact LR) Hc P) as (mu' & mfa' & CORE & _).
  destruct CORE as (_ & E & _). rewrite E. cbn [as_ptr_array set_region]. unfold ensure_cache_inited; destruct (as_cache_inited st); reflexivity.
Qed.

Lemma am_malloc_k_ptr_array : forall st n k U st' ev, WF st -> am_malloc_k st n k = Some (U, st', ev) ->
  as_ptr_array st' = as_ptr_array st /\ as_space_beg st' = as_space_beg st.
Proof.
  intros st n k U st' ev W H. destruct (WF_lengths st W) as [LR LC].
  destruct (am_malloc_k_shape st n k U st' ev H) as (st1 & allocated & cls & NNEG & EU & CORE & ARMS).
  destruct CORE as (SB & PA & _). cbn [as_space_beg as_ptr_array upd_chunk set_chunks] in SB, PA. rewrite SB, PA.
  destruct ARMS as [(LG & -> & evL & LA)|(LG & -> & evC & CA)].
  - pose proof (large_allocate_core _ _ _ _ _ _ LA) as (E1 & E2 & _). cbn in E1, E2. split; [exact E2| exact E1].
  - assert (HC : 0 <= class_id (rq_needed (compute_req n)) < kNumClasses).
    { pose proof (class_id_range (rq_needed (compute_req n))) as CR. unfold kNumClasses. apply Z.ltb_ge in LG. unfold kMaxSize in LG.
      pose proof (compute_req_facts n NNEG) as RQ. cbv zeta in RQ. destruct RQ as (_ & RZ & RD & _ & ND & _).
      assert (1 <= rq_needed (compute_req n) <= 65536) by (destruct (rq_primary (compute_req n)); lia). specialize (CR H0). lia. }
    split; [exact (cache_alloc_ptr_array st (class_id (rq_needed (compute_req n))) st1 allocated evC LR HC CA)|].
    exact (proj1 (proj2 (cache_alloc_frame st (class_id (rq_needed (compute_req n))) st1 allocated evC LR ltac:(clear - HC; lia) CA))).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition INITQ (st : astate) : Prop :=
  as_cache_inited st = true \/ (qc_list (as_tq st) = [] /\ qc_list (as_gq st) = []).

Lemma same_core_inited : forall a b, same_core a b -> as_cache_inited a = as_cache_inited b.
Proof. intros a b C. destruct C as (_ & _ & _ & I & _). exact I. Qed.
Lemma same_core_tq : forall a b, same_core a b -> as_tq a = as_tq b.
Proof. intros a b C. destruct C as (_ & _ & _ & _ & _ & _ & _ & _ & T & _). exact T. Qed.
Lemma same_core_gq : forall a b, same_core a b -> as_gq a = as_gq b.
Proof. intros a b C. destruct C as (_ & _ & _ & _ & _ & _ & _ & _ & _ & G & _). exact G. Qed.

Lemma eci_inited : forall st, as_cache_inited (ensure_cache_inited st) = true.
Proof. intros st. unfold ensure_cache_inited. destruct (as_cache_inited st) eqn:E; [exact E| reflexivity]. Qed.
Lemma eci_tq : forall st, as_tq (ensure_cache_inited st) = as_tq st.
Proof. intros st. unfold ensure_cache_inited. destruct (as_cache_inited st); reflexivity. Qed.
Lemma eci_gq : forall st, as_gq (ensure_cache_inited st) = as_gq st.
Proof. intros st. unfold ensure_cache_inited. destruct (as_cache_inited st); reflexivity. Qed.
Lemma eci_regions : forall st, as_regions (ensure_cache_inited st) = as_regions st.
Proof. intros st. unfold ensure_cache_inited. destruct (as_cache_inited st); reflexivity. Qed.

Lemma poison_shadow_inited : forall st a n v st' ev, poison_shadow st a n v = Some (st', ev) ->
  as_cache_inited st' = as_cache_inited st /\ as_tq st' = as_tq st /\ as_gq st' = as_gq st.
Proof.
  intros st a n v st' ev H. pose proof (poison_shadow_core _ _ _ _ _ _ H) as C.
  split; [exact (same_core_inited _ _ C)| split; [exact (same_core_tq _ _ C)| exact (same_core_gq _ _ C)]].
Qed.

Lemma populate_inited : forall st c req st' ev, length (as_regions st) = 32%nat -> 0 <= c < kNumClasses ->
  populate_free_array st c req = Some (st', ev) ->
  as_cache_inited st' = as_cache_inited st /\ as_tq st' = as_tq st /\ as_gq st' = as_gq st.
Proof.
  intros st c req st' ev L Hc H. destruct (populate_free_array_core st c req st' ev L Hc H) as (mu' & mfa' & C & _). cbv zeta in C.
  split; [exact (same_core_inited _ _ C)| split; [exact (same_core_tq _ _ C)| exact (same_core_gq _ _ C)]].
Qed.

Lemma get_from_allocator_inited : forall st c n st' taken ev, length (as_regions st) = 32%nat -> 0 <= c < kNumClasses ->
  get_from_allocator st c n = Some (st', taken, ev) ->
  as_cache_inited st' = as_cache_inited st /\ as_tq st' = as_tq st /\ as_gq st' = as_gq st.
Proof.
  intros st c n st' taken ev L Hc H. destruct (get_from_allocator_core st c n st' taken ev H) as (st1 & A & _ & ->). cbn.
  destruct A as [[-> _]|(_ & (ev1 & P & _))]; [repeat split; reflexivity|].
  exact (populate_inited st c _ st1 ev1 L Hc P).
Qed.

Lemma cache_alloc_inited : forall st c st' a ev, length (as_regions st) = 32%nat -> 0 <= c -> cache_ok st c ->
  cache_alloc st c = Some (st', a, ev) ->
  as_cache_inited st' = true /\ as_tq st' = as_tq st /\ as_gq st' = as_gq st.
Proof.
  intros st c st' a ev L C00 CO H. destruct (cache_alloc_core st c st' a ev H) as ((C0 & C1) & st1 & pc1 & cp & rest & A & _ & -> & _). cbn.
  destruct A as [(PZ & taken & ev' & G & _)|(PZ & -> & _)].
  - assert (Hc : 0 <= c < kNumClasses) by (pose proof (co_count _ _ CO); unfold kNumClasses in *; lia).
    destruct (get_from_allocator_inited (ensure_cache_inited st) c _ st1 taken ev' ltac:(rewrite eci_regions; exact L) Hc G) as (I1 & T1 & G1).
    rewrite I1, T1, G1, eci_inited, eci_tq, eci_gq. repeat split; reflexivity.
  - pose proof (co_bound _ _ CO) as B. destruct (as_cache_inited st); [repeat split; reflexivity| exfalso; exact (PZ B)].
Qed.

Lemma cache_dealloc_inited : forall st c p st' ev, cache_dealloc st c p = Some (st', ev) ->
  as_cache_inited st' = true /\ as_tq st' = as_tq st /\ as_gq st' = as_gq st.
Proof.
  intros st c p st' ev H. unfold cache_dealloc in H.
  destruct ((c =? 0) || (kNumClasses <=? c)); [discriminate H|].
  set (st0 := ensure_cache_inited st) in H.
  assert (I0 : as_cache_inited st0 = true /\ as_tq st0 = as_tq st /\ as_gq st0 = as_gq st) by (subst st0; split; [apply eci_inited| split; [apply eci_tq| apply eci_gq]]).
  destruct I0 as (I0 & T0 & G0).
  destruct (pc_count (get_pc st0 c) =? max_count c).
  - destruct (_ <? _); [discriminate H|].
    destruct (return_to_allocator (set_pc st0 c _) c _ _) as [[st1 ev1]|] eqn:RT; [| discriminate H]. injection H as <- _.
    unfold return_to_allocator in RT. destruct (ensure_free_array_space _ c _) as [[st2 ev2]|] eqn:EN; [| discriminate RT]. injection RT as <- _.
    destruct (ensure_free_array_space_core _ c _ st2 ev2 EN) as (mfa' & C2 & _). cbv zeta in C2.
    cbn. rewrite (same_core_inited _ _ C2), (same_core_tq _ _ C2), (same_core_gq _ _ C2). cbn. split; [exact I0| split; [exact T0| exact G0]].
  - injection H as <- _. cbn. split; [exact I0| split; [exact T0| exact G0]].
Qed.

Lemma large_deallocate_inited : forall st p st' ev, large_deallocate st p = Some (st', ev) ->
  as_cache_inited st' = as_cache_inited st /\ as_tq st' = as_tq st /\ as_gq st' = as_gq st.
Proof.
  intros st p st' ev H. destruct (large_deallocate_core st p st' ev H) as [_ C].
  split; [exact (same_core_inited _ _ C)| split; [exact (same_core_tq _ _ C)| exact (same_core_gq _ _ C)]].
Qed.

(* [comment removed for export] *)
Definition imono (st st' : astate) : Prop :=
  (as_cache_inited st = true -> as_cache_inited st' = true) /\ as_tq st' = as_tq st /\ as_gq st' = as_gq st.
Lemma imono_refl : forall st, imono st st. Proof. intros st. split; [intros H; exact H| split; reflexivity]. Qed.
Lemma imono_trans : forall a b c, imono a b -> imono b c -> imono a c.
Proof. intros a b c (I1 & T1 & G1) (I2 & T2 & G2). split; [intros H; exact (I2 (I1 H))| split; congruence]. Qed.

Lemma cb_recycle_inited : forall st m st' ev, cb_recycle st m = Some (st', ev) -> imono st st'.
Proof.
  intros st m st' ev H. unfold cb_recycle in H.
  destruct (find_chunk (as_chunks st) (m + kChunkHeaderSize)) as [ch|]; [| discriminate H].
  destruct (ch_state ch); [discriminate H|].
  destruct (in_primary st m).
  - destruct (class_of_addr st m =? 0); [discriminate H|]. destruct (_ <? _); [discriminate H|]. destruct (negb _); [discriminate H|].
    destruct (poison_shadow st _ _ _) as [[st1 ev1]|] eqn:PS; [| discriminate H].
    destruct (cache_dealloc _ _ _) as [[st3 ev3]|] eqn:CD; [| discriminate H]. injection H as <- _.
    pose proof (poison_shadow_inited _ _ _ _ _ _ PS) as (I1 & T1 & G1).
    pose proof (cache_dealloc_inited _ _ _ _ _ CD) as (I3 & T3 & G3). cbn in T3, G3.
    split; [intros _; exact I3| split; congruence].
  - destruct (large_get_block_begin st m) as [p|]; [| discriminate H]. destruct (p =? 0); [discriminate H|].
    destruct (in_primary st p); [discriminate H|]. destruct (negb _); [discriminate H|].
    pose proof (large_deallocate_inited _ _ _ _ H) as (I1 & T1 & G1). cbn in I1, T1, G1.
    split; [intros I; rewrite I1; exact I| split; [exact T1| exact G1]].
Qed.

Lemma cb_recycle_list_inited : forall ms st racc st' racc', cb_recycle_list st ms racc = Some (st', racc') -> imono st st'.
Proof.
  induction ms as [|m ms IH]; intros st racc st' racc' H; cbn in H.
  - injection H as <- _. apply imono_refl.
  - destruct (cb_recycle st m) as [[st1 ev1]|] eqn:CB; [| discriminate H].
    exact (imono_trans _ _ _ (cb_recycle_inited _ _ _ _ CB) (IH _ _ _ _ H)).
Qed.

Lemma do_recycle_inited : forall bs st racc st' racc', do_recycle st bs racc = Some (st', racc') -> imono st st'.
Proof.
  induction bs as [|b bs IH]; intros st racc st' racc' H; cbn in H.
  - injection H as <- _. apply imono_refl.
  - destruct (cb_recycle_list st (qb_chunks b) racc) as [[st1 racc1]|] eqn:CL; [| discriminate H].
    destruct (negb _); [discriminate H|].
    destruct (cache_dealloc st1 _ _) as [[st2 ev2]|] eqn:CD; [| discriminate H].
    pose proof (cache_dealloc_inited _ _ _ _ _ CD) as (I2 & T2 & G2).
    eapply imono_trans; [exact (cb_recycle_list_inited _ _ _ _ _ CL)|].
    eapply imono_trans; [| exact (IH _ _ _ _ H)]. split; [intros _; exact I2| split; [exact T2| exact G2]].
Qed.

(* [comment removed for export] *)
Lemma quarantine_recycle_inited : forall st ms st' ev, quarantine_recycle st ms = Some (st', ev) ->
  as_cache_inited st = true -> as_cache_inited st' = true.
Proof.
  intros st ms st' ev H I. unfold quarantine_recycle in H.
  destruct (_ <? _); [discriminate H|].
  match type of H with (match ?mg with _ => _ end) = _ => destruct mg as [[g1 extracted]|]; [| discriminate H] end.
  destruct (pop_while _ _ _ _ _) as [[[l2 bytes2] rpopped]|]; [| discriminate H].
  destruct (do_recycle (set_gq st _) _ _) as [[st2 racc]|] eqn:DR; [| discriminate H]. injection H as <- _.
  destruct (do_recycle_inited _ _ _ _ _ DR) as (I2 & _). apply I2. cbn. exact I.
Qed.

Lemma quarantine_drain_inited : forall st st' ev, quarantine_drain st = Some (st', ev) ->
  as_cache_inited st = true -> as_cache_inited st' = true.
Proof.
  intros st st' ev H I. unfold quarantine_drain in H.
  destruct (as_qmax st <? _).
  - apply (quarantine_recycle_inited _ _ _ _ H). cbn. exact I.
  - injection H as <- _. cbn. exact I.
Qed.

(* [comment removed for export] *)
Lemma quarantine_enqueue_inited : forall st m size st' ev, length (as_regions st) = 32%nat -> cache_ok st kBatchClass -> INITQ st ->
  quarantine_enqueue st m size = Some (st', ev) -> as_cache_inited st' = true.
Proof.
  intros st m size st' ev L CO IQ H. unfold quarantine_enqueue in H.
  destruct (qc_list (as_tq st)) as [|b0 l0] eqn:TQ.
  - destruct (cache_alloc st kBatchClass) as [[[st1 b] ev1]|] eqn:CA; [| discriminate H].
    destruct (b =? 0); [discriminate H|]. injection H as <- _. cbn.
    exact (proj1 (cache_alloc_inited st kBatchClass _ _ _ L ltac:(unfold kBatchClass; lia) CO CA)).
  - destruct (kBatchCount <=? _).
    + destruct (cache_alloc st kBatchClass) as [[[st1 b] ev1]|] eqn:CA; [| discriminate H].
      destruct (b =? 0); [discriminate H|]. injection H as <- _. cbn.
      exact (proj1 (cache_alloc_inited st kBatchClass _ _ _ L ltac:(unfold kBatchClass; lia) CO CA)).
    + injection H as <- _. cbn. destruct IQ as [I|[T _]]; [exact I| exfalso; rewrite TQ in T; discriminate T].
Qed.

Lemma cache_ok_transfer : forall a b c, as_cache a = as_cache b -> as_regions a = as_regions b -> as_cache_inited a = as_cache_inited b ->
  cache_ok b c -> cache_ok a c.
Proof.
  intros a b c C R I [X Y W]. constructor; unfold get_pc, get_region in *; rewrite ?C, ?R, ?I; assumption.
Qed.

Lemma quarantine_put_inited : forall st ch st' ev, length (as_regions st) = 32%nat -> cache_ok st kBatchClass -> INITQ st ->
  quarantine_put st ch = Some (st', ev) -> as_cache_inited st' = true.
Proof.
  intros st ch st' ev L CO IQ H. unfold quarantine_put in H.
  destruct (_ || _); [discriminate H|].
  destruct (poison_shadow st _ _ _) as [[st1 ev1]|] eqn:PS; [| discriminate H].
  pose proof (poison_shadow_core _ _ _ _ _ _ PS) as C1. pose proof (poison_shadow_inited _ _ _ _ _ _ PS) as (I1 & T1 & G1).
  assert (L1 : length (as_regions st1) = 32%nat) by (rewrite (same_core_len_regions _ _ C1); exact L).
  assert (CO1 : cache_ok st1 kBatchClass).
  { destruct C1 as (_ & _ & R & I & C & _). exact (cache_ok_transfer _ _ _ C R I CO). }
  assert (IQ1 : INITQ st1) by (unfold INITQ in *; rewrite I1, T1, G1; exact IQ).
  destruct (quarantine_enqueue st1 _ _) as [[st2 ev2]|] eqn:EQ; [| discriminate H].
  pose proof (quarantine_enqueue_inited _ _ _ _ _ L1 CO1 IQ1 EQ) as I2.
  destruct (_ <? _).
  - destruct (quarantine_drain st2) as [[st3 ev3]|] eqn:DR; [| discriminate H]. injection H as <- _.
    exact (quarantine_drain_inited _ _ _ DR I2).
  - injection H as <- _. exact I2.
Qed.

Theorem am_free_full_initq : forall st p st' ev, WF st -> INITQ st -> am_free_full st p = Some (st', ev) ->
  INITQ st' /\ (p <> 0 -> as_cache_inited st' = true).
Proof.
  intros st p st' ev W IQ H.
  pose proof (WF_lengths st W) as [LENR LENC]. pose proof (WF_cache st kBatchClass W ltac:(unfold kBatchClass, kNumClasses; lia)) as CO.
  assert (K : forall st0 (ev0 : list effect),
    as_cache_inited st0 = as_cache_inited st -> as_tq st0 = as_tq st -> as_gq st0 = as_gq st -> as_regions st0 = as_regions st -> as_cache st0 = as_cache st ->
    (if p =? 0 then Some (st0, ev0) else
     match find_chunk (as_chunks st0) p with
     | None => None
     | Some ch => match ch_state ch with
                  | CQuarantine => None
                  | CAllocated =>
                      match quarantine_put (upd_chunk st0 (mkChunk (ch_alloc_beg ch) (ch_user_beg ch) (ch_used ch) (ch_rz ch) (ch_class ch) CQuarantine))
                              (mkChunk (ch_alloc_beg ch) (ch_user_beg ch) (ch_used ch) (ch_rz ch) (ch_class ch) CQuarantine) with
                      | None => None
                      | Some (st2, ev2) => Some (st2, ev0 ++ [EStore64 p 0xFFFFFFFF00000000; EStore64 p 0] ++ ev2)
                      end
                  end
     end) = Some (st', ev) -> INITQ st' /\ (p <> 0 -> as_cache_inited st' = true)).
  { intros st0 ev0 I0 T0 G0 R0 C0 H0. destruct (Z.eqb_spec p 0) as [P0|P0].
    - injection H0 as <- _. split; [unfold INITQ in *; rewrite I0, T0, G0; exact IQ| intros NE; exfalso; exact (NE P0)].
    - destruct (find_chunk (as_chunks st0) p) as [ch|]; [| discriminate H0]. destruct (ch_state ch); [| discriminate H0].
      match type of H0 with (match quarantine_put ?a ?b with _ => _ end) = _ => destruct (quarantine_put a b) as [[st2 ev2]|] eqn:QP; [| discriminate H0] end.
      injection H0 as <- _.
      assert (I2 : as_cache_inited st2 = true).
      { match type of QP with quarantine_put ?s1 ?c1 = _ =>
          apply (quarantine_put_inited s1 c1 _ _ ltac:(cbn; rewrite R0; exact LENR) (cache_ok_transfer s1 st _ ltac:(cbn; exact C0) ltac:(cbn; exact R0) ltac:(cbn; exact I0) CO)
                ltac:(unfold INITQ in *; cbn; rewrite I0, T0, G0; exact IQ) QP) end. }
      split; [left; exact I2| intros _; exact I2]. }
  unfold am_free_full in H. destruct (as_internal_init st); [exact (K st [] eq_refl eq_refl eq_refl eq_refl eq_refl H)| exact (K (set_internal_init st) [EInternalAllocInit] eq_refl eq_refl eq_refl eq_refl eq_refl H)].
Qed.

Theorem am_malloc_k_initq : forall st n k U st' ev, WF st -> INITQ st -> am_malloc_k st n k = Some (U, st', ev) -> INITQ st'.
Proof.
  intros st n k U st' ev W IQ H. pose proof (WF_lengths st W) as [LENR LENC].
  destruct (am_malloc_k_shape st n k U st' ev H) as (st1 & allocated & cls & _ & _ & C & ALT). cbv zeta in C, ALT.
  pose proof (same_core_inited _ _ C) as I'. pose proof (same_core_tq _ _ C) as T'. pose proof (same_core_gq _ _ C) as G'. cbn in I', T', G'.
  unfold INITQ in *. rewrite I', T', G'.
  destruct ALT as [(_ & _ & (evL & LA))|(NP & -> & (evC & CA))].
  - pose proof (large_allocate_core _ _ _ _ _ _ LA) as C1.
    rewrite (same_core_inited _ _ C1), (same_core_tq _ _ C1), (same_core_gq _ _ C1). cbn. exact IQ.
  - apply Z.ltb_ge in NP. set (needed := rq_needed (compute_req n)) in *.
    assert (NR : 1 <= needed <= 65536).
    { split; [| unfold kMaxSize in NP; exact NP]. subst needed. unfold compute_req. cbn [rq_needed].
      pose proof (rz_size_facts n) as [R1 _]. destruct (_ <=? kMaxSize); unfold round_up; lia. }
    pose proof (class_id_range needed NR) as CR.
    destruct (cache_alloc_inited st (class_id needed) _ _ _ LENR ltac:(lia) (WF_cache st (class_id needed) W ltac:(unfold kNumClasses; lia)) CA) as (I1 & T1 & G1).
    rewrite I1, T1, G1. left. reflexivity.
Qed.

Lemma INITQ_core : forall a b, same_core a b -> INITQ b -> INITQ a.
Proof.
  intros a b C IQ. unfold INITQ in *. rewrite (same_core_inited _ _ C), (same_core_tq _ _ C), (same_core_gq _ _ C). exact IQ.
Qed.
Lemma INITQ_init : forall st, qc_list (as_tq st) = [] -> qc_list (as_gq st) = [] -> INITQ st.
Proof. intros st T G. right. split; [exact T| exact G]. Qed.
