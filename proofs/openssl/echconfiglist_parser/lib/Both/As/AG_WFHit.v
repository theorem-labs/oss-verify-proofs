(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From Stdlib Require Import FMapPositive.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import AsanAllocModel.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import AllocWf AllocKit AG_MallocModel.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Lemma WF_ext : forall a b,
  as_space_beg a = as_space_beg b -> as_regions a = as_regions b -> as_cache_inited a = as_cache_inited b ->
  as_cache a = as_cache b -> as_n_reserved a = as_n_reserved b -> as_sec a = as_sec b -> as_chunks a = as_chunks b ->
  as_tq a = as_tq b -> as_gq a = as_gq b -> as_qmax a = as_qmax b -> as_qmin a = as_qmin b -> as_qcache a = as_qcache b ->
  WF b -> WF a.
Proof.
  intros a b. destruct a, b; cbn. intros -> -> -> -> -> -> -> -> -> -> -> -> W.
  destruct W as (H1 & Hrest). split.
  - intros c Hc. destruct (H1 c Hc) as [RO CO]. split.
    + destruct RO; constructor; assumption.
    + destruct CO; constructor; assumption.
  - exact Hrest.
Qed.

Lemma WF_sbs : forall a b, same_but_shadow a b -> WF b -> WF a.
Proof.
  intros a b S W. unfold same_but_shadow in S.
  destruct S as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & E15 & E16).
  eapply WF_ext; [ .. | exact W]; assumption.
Qed.

(* [comment removed for export] *)
Lemma length_upd_nth {A} : forall (l : list A) i x, length (upd_nth l i x) = length l.
Proof. induction l; intros [|i] x; cbn; auto. Qed.
Lemma znth_upd_nth_eq {A} : forall (l : list A) i x d, (i < length l)%nat -> znth (upd_nth l i x) i d = x.
Proof. induction l; intros [|i] x d H; cbn in *; try lia; auto. apply IHl. lia. Qed.
Lemma znth_upd_nth_neq {A} : forall (l : list A) i j x d, i <> j -> znth (upd_nth l i x) j d = znth l j d.
Proof. induction l; intros [|i] [|j] x d H; cbn in *; auto; try congruence. Qed.

Lemma Permutation_filter {A} : forall (f : A -> bool) l l', Permutation l l' -> Permutation (filter f l) (filter f l').
Proof.
  intros f l l' P. induction P; cbn.
  - constructor.
  - destruct (f x); [apply perm_skip|]; assumption.
  - destruct (f x), (f y); try apply perm_swap; try apply perm_skip; apply Permutation_refl.
  - eapply Permutation_trans; eassumption.
Qed.

Lemma zlen_cons {A} : forall (x : A) l, zlen (x :: l) = zlen l + 1.
Proof. intros. unfold zlen. cbn [length]. lia. Qed.

(* [comment removed for export] *)
Definition keys_ok (mp : PositiveMap.t chunk) : Prop :=
  forall k x, PositiveMap.find k mp = Some x -> k = ckey (ch_user_beg x) /\ 0 < ch_user_beg x.

Lemma WF_keys : forall st, WF st -> keys_ok (as_chunks st).
Proof. intros st W. destruct W as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & K). exact K. Qed.

Lemma chunk_list_nodup : forall st, keys_ok (as_chunks st) -> NoDup (chunk_list st).
Proof.
  intros st K. unfold chunk_list.
  assert (INJ : forall k k' x, In (k, x) (PositiveMap.elements (as_chunks st)) -> In (k', x) (PositiveMap.elements (as_chunks st)) -> k = k').
  { intros k k' x H1 H2. apply PositiveMap.elements_complete in H1. apply PositiveMap.elements_complete in H2.
    destruct (K _ _ H1) as [-> _]. destruct (K _ _ H2) as [-> _]. reflexivity. }
  pose proof (PositiveMap.elements_3w (as_chunks st)) as ND.
  revert INJ ND. generalize (PositiveMap.elements (as_chunks st)) as l. induction l as [|[k x] l IH]; intros INJ ND; cbn; constructor.
  - inversion ND; subst. intros Hin. apply H1. apply in_map_iff in Hin as [[k' x'] [E Hin]]. cbn in E. subst x'.
    assert (k = k') by (eapply INJ; [left; reflexivity| right; exact Hin]). subst k'.
    apply SetoidList.InA_alt. exists (k, x). split; [reflexivity| exact Hin].
  - apply IH; [| inversion ND; assumption]. intros k1 k2 y Ha Hb. eapply INJ; right; eassumption.
Qed.

Lemma chunk_list_find : forall st x, keys_ok (as_chunks st) ->
  In x (chunk_list st) <-> PositiveMap.find (ckey (ch_user_beg x)) (as_chunks st) = Some x.
Proof.
  intros st x K. rewrite chunk_list_in_iff. split.
  - intros [k F]. destruct (K _ _ F) as [-> _]. exact F.
  - intros F. exists (ckey (ch_user_beg x)). exact F.
Qed.

Lemma keys_ok_upd : forall st ch, keys_ok (as_chunks st) -> 0 < ch_user_beg ch -> keys_ok (as_chunks (upd_chunk st ch)).
Proof.
  intros st ch K POS k x F. unfold upd_chunk, set_chunks in F. cbn [as_chunks] in F. rewrite gadd_find in F.
  destruct (PositiveMap.E.eq_dec _ _) as [E|NE]; [| exact (K _ _ F)]. inversion F; subst. split; [reflexivity| exact POS].
Qed.

Lemma chunk_list_upd_perm : forall st ch, keys_ok (as_chunks st) -> 0 < ch_user_beg ch ->
  PositiveMap.find (ckey (ch_user_beg ch)) (as_chunks st) = None ->
  Permutation (chunk_list (upd_chunk st ch)) (ch :: chunk_list st).
Proof.
  intros st ch K POS FR. apply NoDup_Permutation.
  - apply chunk_list_nodup. apply keys_ok_upd; assumption.
  - constructor; [| apply chunk_list_nodup; exact K]. rewrite (chunk_list_find st ch K). congruence.
  - intros x. rewrite chunk_list_upd_iff. cbn [In]. split.
    + intros [->|[k [F NE]]]; [left; reflexivity| right]. apply chunk_list_in_iff. exists k. exact F.
    + intros [<-|Hin]; [left; reflexivity| right]. apply (chunk_list_find st x K) in Hin.
      exists (ckey (ch_user_beg x)). split; [exact Hin| congruence].
Qed.

(* [comment removed for export] *)
Lemma compute_req_facts : forall n, 0 <= n -> let r := compute_req n in
  rq_size r = Z.max n 1 /\ 16 <= rq_rz r <= 2048 /\ Z.max n 8 <= rq_rounded r < Z.max n 8 + 8 /\ rq_rounded r mod 8 = 0
  /\ rq_needed r = rq_rounded r + rq_rz r + (if rq_primary r then 0 else rq_rz r)
  /\ compute_req (rq_size r) = mkReq (rq_size r) (rq_size r) (rq_rz r) (rq_rounded r) (rq_needed r) (rq_primary r).
Proof.
  intros n Hn r. pose proof (rz_size_facts n) as (RZ & _).
  assert (RU : forall x, x <= round_up x 8 < x + 8 /\ round_up x 8 mod 8 = 0).
  { intros x. unfold round_up. Z.div_mod_to_equations. nia. }
  subst r. destruct (Z.eq_dec n 0) as [->|NZ].
  - cbn. repeat split; (lia || reflexivity).
  - unfold compute_req. replace (n =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
    cbn -[Z.add Z.mul Z.max round_up rz_size Z.leb Z.ltb Z.eqb]. pose proof (RU (Z.max n 8)).
    replace (n =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
    repeat split; try lia; try reflexivity.
    destruct (round_up (Z.max n 8) 8 + rz_size n <=? kMaxSize); lia.
Qed.

(* [comment removed for export] *)
Lemma flat_map_ext_in {A B} : forall (g g' : A -> list B) l, (forall x, In x l -> g' x = g x) -> flat_map g' l = flat_map g l.
Proof. induction l as [|y l IH]; intros H; [reflexivity|]. cbn. rewrite H by (left; reflexivity). rewrite IH; [reflexivity|]. intros x Hx. apply H. right. exact Hx. Qed.
Lemma flat_map_perm_remove : forall (g g' : Z -> list Z) l c AB F M,
  NoDup l -> In c l -> (forall x, In x l -> x <> c -> g' x = g x) -> g c = F ++ AB :: M -> g' c = F ++ M ->
  Permutation (AB :: flat_map g' l) (flat_map g l).
Proof.
  intros g g' l c AB F M ND Hin Hg Gc Gc'. induction l as [|y l IH]; [destruct Hin|]. cbn.
  inversion ND; subst. destruct (Z.eq_dec y c) as [->|NE].
  - rewrite Gc, Gc'. rewrite (flat_map_ext_in g g' l).
    2:{ intros x Hx. apply Hg; [right; exact Hx|]. intros ->. exact (H1 Hx). }
    rewrite <- !app_assoc. cbn. apply Permutation_cons_app. apply Permutation_refl.
  - destruct Hin as [->|Hin]; [congruence|]. rewrite (Hg y) by (auto; left; reflexivity).
    eapply Permutation_trans; [apply Permutation_middle|]. apply Permutation_app_head. apply IH; auto.
    intros x Hx Hne. apply Hg; [right; exact Hx| exact Hne].
Qed.

Lemma classes_nodup : NoDup (map Z.of_nat (seq 0 32)).
Proof. apply NoDup_map_NoDup_ForallPairs; [intros x y _ _; lia| apply seq_NoDup]. Qed.
Lemma classes_in : forall c, 0 <= c < 32 -> In c (map Z.of_nat (seq 0 32)).
Proof. intros c Hc. apply in_map_iff. exists (Z.to_nat c). split; [lia|]. apply in_seq. lia. Qed.

(* [comment removed for export] *)
Lemma NoDup_app_disjoint' : forall (l1 l2 : list Z) x, NoDup (l1 ++ l2) -> In x l1 -> In x l2 -> False.
Proof.
  induction l1 as [|y l1 IH]; intros l2 x ND H1 H2; [destruct H1|].
  inversion ND; subst. destruct H1 as [->|H1].
  - apply H3. apply in_app_iff. right. exact H2.
  - eapply IH; eauto.
Qed.

Lemma cache_vs_inuse : forall st c cp x, WF st -> 0 <= c < kNumClasses -> In cp (pc_chunks (get_pc st c)) ->
  In x (chunk_list st) -> ch_primary x = true -> ch_alloc_beg x <> compact_to_addr st c cp.
Proof.
  intros st c cp x W Hc Hcp Hx Hp E. destruct W as (_ & ND & _). unfold carved_addr_list in ND.
  eapply (NoDup_app_disjoint' _ _ (ch_alloc_beg x) ND).
  - apply in_flat_map. exists c. split; [apply classes_in; exact Hc|]. apply in_app_iff. right. rewrite E. apply in_map. exact Hcp.
  - apply in_app_iff. left. apply in_map. apply filter_In. auto.
Qed.

Section WFHit.
  Variables (st : astate) (n c cp : Z) (rest : list Z).
  Let r := compute_req n.
  Let AB := compact_to_addr st c cp.
  Let U := AB + rq_rz r.
  Let ch := mkChunk AB U (rq_size r) (rq_rz r) c CAllocated.
  Let cnt := pc_count (get_pc st c).
  Let st' := hit_state st c cnt rest ch.
  Hypothesis W : WF st.
  Hypothesis Hn : 0 <= n.
  Hypothesis HC : 0 < c < kNumClasses.
  Hypothesis CID : c = class_id (rq_needed r).
  Hypothesis PRIM : rq_primary r = true.
  Hypothesis FIT : rq_needed r <= class_size c.
  Hypothesis PCS : pc_chunks (get_pc st c) = cp :: rest.
  Hypothesis SB0 : 0 <= as_space_beg st.

  Let CO : cache_ok st c. Proof. apply WF_cache; [exact W| lia]. Qed.
  Let RO : region_ok st c. Proof. apply WF_region; [exact W| lia]. Qed.
  Let CV : carved st c AB. Proof. apply carved_cache; [exact W| lia| rewrite PCS; left; reflexivity]. Qed.
  Let T : 0 <= class_size c <= 65536 /\ class_size c mod 32 = 0 /\ (1 <= c -> 32 <= class_size c)
          /\ 0 <= max_count c <= 16 /\ (1 <= c -> 2 <= max_count c) /\ max_count c mod 2 = 0.
  Proof. apply class_size_table_facts. unfold kNumClasses in HC. lia. Qed.
  Let RQ : rq_size r = Z.max n 1 /\ 16 <= rq_rz r <= 2048 /\ Z.max n 8 <= rq_rounded r < Z.max n 8 + 8 /\ rq_rounded r mod 8 = 0
           /\ rq_needed r = rq_rounded r + rq_rz r + (if rq_primary r then 0 else rq_rz r)
           /\ compute_req (rq_size r) = mkReq (rq_size r) (rq_size r) (rq_rz r) (rq_rounded r) (rq_needed r) (rq_primary r).
  Proof. apply compute_req_facts. exact Hn. Qed.
  Let RNG : region_beg st c <= AB /\ AB + class_size c <= region_beg st c + kFreeArrayOffset /\ 0 < class_size c <= 65536.
  Proof. apply carved_range; [exact W| exact CV]. Qed.
  Let RB : region_beg st c = as_space_beg st + c * 2^32. Proof. apply region_beg_eq. Qed.
  Let CNT1 : cnt = zlen rest + 1. Proof. unfold cnt. rewrite (co_count _ _ CO), PCS. apply zlen_cons. Qed.
  Let KEYS : keys_ok (as_chunks st). Proof. apply WF_keys. exact W. Qed.
  Let UPOS : 0 < U. Proof. unfold U. unfold kFreeArrayOffset in RNG. lia. Qed.

  Lemma hit_fresh : PositiveMap.find (ckey U) (as_chunks st) = None.
  Proof.
    destruct (PositiveMap.find (ckey U) (as_chunks st)) as [x|] eqn:F; [exfalso| reflexivity].
    destruct (KEYS _ _ F) as [K POS].
    assert (EU : ch_user_beg x = U) by (unfold ckey in K; apply Z2Pos.inj; [exact POS| exact UPOS| congruence]).
    assert (Hx : In x (chunk_list st)) by (apply chunk_list_in_iff; eexists; exact F).
    pose proof (WF_chunk st x W Hx) as OKx. unfold chunk_ok in OKx. destruct OKx as (U1 & U2 & U3 & U4 & REST).
    pose proof (rz_size_facts (ch_used x)) as (RZx & _). change (rz_size (ch_used x)) with (rq_rz (compute_req (ch_used x))) in RZx.
    rewrite <- U3 in RZx.
    pose proof (compute_req_facts (ch_used x) ltac:(lia)) as (_ & _ & X3 & _ & X5 & _). rewrite <- U3 in X5.
    pose proof RQ as RQ2. rewrite PRIM in RQ2.
    unfold kFreeArrayOffset in RNG. unfold kNumClasses in HC. subst U.
    destruct (ch_primary x) eqn:PX.
    - destruct REST as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8). rewrite P1 in X5.
      set (c' := ch_class x) in *.
      assert (HC' : 0 <= c' < 32).
      { rewrite P3. unfold class_of_addr. pose proof (Z.land_ones (Z.shiftr (ch_alloc_beg x - as_space_beg st) kRegionSizeLog) 5 ltac:(lia)) as LO.
        change (Z.ones 5) with 31 in LO. rewrite LO. pose proof (Z.mod_pos_bound (Z.shiftr (ch_alloc_beg x - as_space_beg st) kRegionSizeLog) (2^5)). lia. }
      assert (CV' : carved st c' (ch_alloc_beg x)).
      { unfold carved, kNumClasses. pose proof (class_size_table_facts c' HC'). repeat split; lia. }
      destruct (carved_sep st c AB c' (ch_alloc_beg x) W CV CV') as [[Ec Ea]|[D|D]].
      + eapply (cache_vs_inuse st c cp x W); [unfold kNumClasses; lia| rewrite PCS; left; reflexivity| exact Hx| exact PX| symmetry; exact Ea].
      + lia.
      + lia.
    - destruct REST as (P1 & P2 & _). unfold in_primary in P2. apply andb_false_iff in P2. unfold kSpaceSize in P2.
      destruct P2 as [P2|P2]; [apply Z.leb_gt in P2| apply Z.ltb_ge in P2]; nia.
  Qed.

  Let LENC : length (as_cache st) = 32%nat.
  Proof. destruct W as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & L & _). exact L. Qed.
  Let PCc : get_pc st' c = mkPC (cnt - 1) rest.
  Proof. unfold st', hit_state, get_pc, upd_chunk, set_chunks, set_pc. cbn [as_cache]. apply znth_upd_nth_eq. rewrite LENC. unfold zidx. unfold kNumClasses in HC. lia. Qed.
  Let PCo : forall c', 0 <= c' -> c' <> c -> get_pc st' c' = get_pc st c'.
  Proof. intros c' H1 H2. unfold st', hit_state, get_pc, upd_chunk, set_chunks, set_pc. cbn [as_cache]. apply znth_upd_nth_neq. unfold zidx. lia. Qed.
  Let PERM : Permutation (chunk_list st') (ch :: chunk_list st).
  Proof. exact (chunk_list_upd_perm (set_pc st c (mkPC (cnt - 1) rest)) ch KEYS UPOS hit_fresh). Qed.
  Let INl : forall x, In x (chunk_list st') <-> x = ch \/ In x (chunk_list st).
  Proof.
    intros x. split.
    - intros Hx. apply (Permutation_in x PERM) in Hx. destruct Hx as [E|Hx]; [left; symmetry; exact E| right; exact Hx].
    - intros Hx. apply (Permutation_in x (Permutation_sym PERM)). destruct Hx as [->|Hx]; [left; reflexivity| right; exact Hx].
  Qed.
  Let PRIMch : ch_primary ch = true.
  Proof. unfold ch_primary. cbn [ch_class ch]. apply Bool.negb_true_iff. apply Z.eqb_neq. lia. Qed.
  Let FCB : forall b q, In b (qc_list (as_tq st) ++ qc_list (as_gq st)) -> In q (qb_chunks b) ->
    find_chunk (as_chunks st') (q + kChunkHeaderSize) = find_chunk (as_chunks st) (q + kChunkHeaderSize).
  Proof.
    intros b q Hb Hq. pose proof (WF_batch st b W Hb) as BO. destruct BO as (_ & _ & _ & _ & _ & _ & _ & _ & B9).
    destruct (B9 q Hq) as [x [Fx _]]. unfold find_chunk in *. destruct (q + kChunkHeaderSize <=? 0) eqn:LE; [reflexivity|].
    unfold st', hit_state, upd_chunk, set_chunks, set_pc. cbn [as_chunks ch_user_beg]. rewrite gadd_find.
    destruct (PositiveMap.E.eq_dec _ _) as [E|NE]; [exfalso| reflexivity].
    apply Z.leb_gt in LE. unfold ckey in E. apply Z2Pos.inj in E; [| exact UPOS| exact LE].
    rewrite <- E in Fx. cbn [ch_user_beg ch] in Fx. rewrite hit_fresh in Fx. discriminate.
  Qed.
  Lemma fold_used_ext : forall (F F' : Z -> Z) l, (forall q, In q l -> F q = F' q) ->
    fold_right (fun q acc => F q + acc) 0 l = fold_right (fun q acc => F' q + acc) 0 l.
  Proof. induction l as [|y l IH]; intros H; [reflexivity|]. cbn. rewrite H by (left; reflexivity). rewrite IH; [reflexivity|]. intros q Hq. apply H. right. exact Hq. Qed.
  Let QOK : forall q, (forall b, In b (qc_list q) -> In b (qc_list (as_tq st) ++ qc_list (as_gq st))) -> qcache_ok st q -> qcache_ok st' q.
  Proof.
    intros q SUB [Q1 Q2]. split; [| exact Q2]. intros b Hb. pose proof (Q1 b Hb) as BO.
    destruct BO as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9). unfold batch_ok.
    refine (conj B1 (conj B2 (conj B3 (conj B4 (conj B5 (conj B6 (conj B7 (conj _ _)))))))).
    - rewrite B8. f_equal. apply fold_used_ext. intros q0 Hq0. rewrite (FCB b q0); [reflexivity| apply SUB; exact Hb| exact Hq0].
    - intros q0 Hq0. rewrite (FCB b q0); [| apply SUB; exact Hb| exact Hq0]. apply B9. exact Hq0.
  Qed.

  Theorem WF_hit : WF st'.
  Proof.
    pose proof W as WW.
    destruct WW as (Wrc & Wnd & Wch & Winj & Wsec & Wsnd & Wres1 & Wres2 & Wtq & Wgq & Wtqb & Wgqb & Wndb & Wq & Wm0 & Wm31 & Wpc0 & Wpc31 & WlenR & WlenC & Wqmax & Wqmin & Wqc & Wkeys).
    unfold kNumClasses in HC. unfold kFreeArrayOffset in RNG.
    pose proof (Nat2Z.is_nonneg (length rest)) as NN. unfold zlen in CNT1.
    pose proof RNG as RNG2. unfold AB in RNG2. rewrite compact_to_addr_eq in RNG2.
    assert (COA : class_of_addr st AB = c). { unfold AB. rewrite compact_to_addr_eq. apply class_of_addr_region; lia. }
    assert (INP : in_primary st AB = true). { unfold AB. rewrite compact_to_addr_eq. apply in_primary_region; lia. }
    unfold WF.
    split. { intros c0 Hc0. destruct (Wrc c0 Hc0) as [R0 C0]. split; [destruct R0; constructor; assumption|].
      destruct (Z.eq_dec c0 c) as [->|NE].
      - constructor; rewrite PCc; cbn [pc_count pc_chunks].
        + unfold zlen. lia.
        + pose proof (co_bound _ _ C0) as B. change (as_cache_inited st') with (as_cache_inited st). fold cnt in B. destruct (as_cache_inited st); lia.
        + intros cp0 Hin. apply (co_elems _ _ C0). rewrite PCS. right. exact Hin.
      - destruct C0 as [A0 B0 C0]; constructor; rewrite PCo by lia; assumption. }
    split. 2:{
    split. { intros x Hx. apply INl in Hx as [->|Hx]; [| exact (Wch x Hx)].
      destruct RQ as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6).
      unfold chunk_ok. cbn [ch_used ch_rz ch_user_beg ch_alloc_beg ch_class ch]. rewrite Q6. cbn [rq_size rq_rz rq_needed rq_primary].
      rewrite PRIMch. refine (conj _ (conj eq_refl (conj eq_refl (conj eq_refl _)))); [lia|].
      destruct CV as (_ & _ & V3 & V4 & V5).
      refine (conj PRIM (conj CID (conj (eq_sym COA) (conj INP (conj V4 (conj V3 (conj V5 FIT))))))). }
    split. { intros x y Hx Hy E. apply INl in Hx as [->|Hx]; apply INl in Hy as [->|Hy]; [reflexivity| exfalso| exfalso| exact (Winj x y Hx Hy E)].
      - apply (chunk_list_find st y KEYS) in Hy. cbn [ch_user_beg ch] in E. rewrite <- E in Hy. rewrite hit_fresh in Hy. discriminate.
      - apply (chunk_list_find st x KEYS) in Hx. cbn [ch_user_beg ch] in E. rewrite E in Hx. rewrite hit_fresh in Hx. discriminate. }
    split. { unfold zlen in *. rewrite (Permutation_length (Permutation_filter _ _ _ PERM)). cbn [filter]. rewrite PRIMch. cbn [negb]. exact Wsec. }
    split. { exact Wsnd. } split. { exact Wres1. } split. { exact Wres2. }
    split. { apply QOK; [| exact Wtq]. intros b Hb. apply in_app_iff. left. exact Hb. }
    split. { apply QOK; [| exact Wgq]. intros b Hb. apply in_app_iff. right. exact Hb. }
    split. { exact Wtqb. } split. { exact Wgqb. } split. { exact Wndb. }
    split. { intros x Hx Q. apply INl in Hx as [->|Hx]; [cbn in Q; discriminate| exact (Wq x Hx Q)]. }
    split. { exact Wm0. } split. { exact Wm31. }
    split. { rewrite PCo by lia. exact Wpc0. }
    split. { destruct (Z.eq_dec c 31) as [E|NE].
      - exfalso. assert (Z0 : cnt = 0) by (unfold cnt; rewrite E; exact Wpc31). lia.
      - rewrite PCo by lia. exact Wpc31. }
    split. { exact WlenR. }
    split. { unfold st', hit_state, upd_chunk, set_chunks, set_pc. cbn [as_cache]. rewrite length_upd_nth. exact WlenC. }
    split. { exact Wqmax. } split. { exact Wqmin. } split. { exact Wqc. }
    exact (keys_ok_upd (set_pc st c (mkPC (cnt - 1) rest)) ch KEYS UPOS). }
    (* [comment removed for export] *)
    apply (Permutation_NoDup (l := carved_addr_list st)); [| exact Wnd]. apply Permutation_sym.
    unfold carved_addr_list.
    set (L := map Z.of_nat (seq 0 32)).
    set (g := fun c0 : Z => map (compact_to_addr st c0) (rg_free_array (get_region st c0)) ++ map (compact_to_addr st c0) (pc_chunks (get_pc st c0))).
    set (g' := fun c0 : Z => map (compact_to_addr st' c0) (rg_free_array (get_region st' c0)) ++ map (compact_to_addr st' c0) (pc_chunks (get_pc st' c0))).
    set (B := map qb_addr (qc_list (as_tq st) ++ qc_list (as_gq st))).
    change (map qb_addr (qc_list (as_tq st') ++ qc_list (as_gq st'))) with B.
    set (IU := map ch_alloc_beg (filter ch_primary (chunk_list st))).
    assert (P1 : Permutation (map ch_alloc_beg (filter ch_primary (chunk_list st'))) (AB :: IU)).
    { change AB with (ch_alloc_beg ch). change (ch_alloc_beg ch :: IU) with (map ch_alloc_beg (ch :: filter ch_primary (chunk_list st))).
      apply Permutation_map. replace (ch :: filter ch_primary (chunk_list st)) with (filter ch_primary (ch :: chunk_list st)) by (cbn [filter]; rewrite PRIMch; reflexivity).
      apply Permutation_filter. exact PERM. }
    eapply Permutation_trans. { apply Permutation_app_head. apply Permutation_app_tail. exact P1. }
    eapply Permutation_trans. { apply Permutation_sym. apply (Permutation_middle (flat_map g' L) (IU ++ B) AB). }
    change (AB :: flat_map g' L ++ IU ++ B) with ((AB :: flat_map g' L) ++ (IU ++ B)).
    apply Permutation_app_tail.
    apply (flat_map_perm_remove g g' L c AB (map (compact_to_addr st c) (rg_free_array (get_region st c))) (map (compact_to_addr st c) rest)).
    - apply classes_nodup.
    - apply classes_in. lia.
    - intros x Hx Hne. unfold g, g'. assert (0 <= x) by (unfold L in Hx; apply in_map_iff in Hx as [y [<- _]]; lia). rewrite PCo by lia. reflexivity.
    - unfold g. rewrite PCS. reflexivity.
    - unfold g'. rewrite PCc. reflexivity.
  Qed.
End WFHit.
