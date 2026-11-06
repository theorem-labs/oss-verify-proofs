(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.boost_beast.http_request.lib.Common Require KReplay.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_beast.http_request.lib.As Require AW_0Gc. (* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From Stdlib Require Import FMapPositive.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import AsanAllocModel.
From OSSVerify.Proofs.boost_beast.http_request.lib.As Require Import AllocWf AllocKit AG_MallocModel.
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
Scheme kc__1 := Elimination for Corelib.Init.Datatypes.option Sort Prop.
Scheme kc__2 := Elimination for Corelib.Init.Logic.and Sort Prop.
Scheme kc__3 := Elimination for Corelib.Init.Datatypes.bool Sort Prop.
Scheme kc__4 := Elimination for Corelib.Init.Logic.or Sort Prop.

  Lemma hit_fresh : PositiveMap.find (ckey U) (as_chunks st) = None.
  Proof.
    ltac2:(KReplay.run [|constr:(@Stdlib.FSets.FMapPositive.PositiveMap.find); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAllocModel.chunk); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAllocModel.ckey); constr:(U); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAllocModel.as_chunks); constr:(st); constr:(@Corelib.Init.Datatypes.option); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Corelib.Init.Logic.eq); constr:(@kc__1); constr:(@Corelib.Init.Datatypes.None); constr:(@Corelib.Init.Datatypes.Some); constr:(@Corelib.Init.Logic.False_ind); constr:(KEYS); constr:(@Corelib.Init.Logic.and); constr:(@Stdlib.FSets.FMapPositive.PositiveMap.key); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAllocModel.ch_user_beg); constr:(@Stdlib.ZArith.BinInt.Z.lt); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@kc__2); constr:(@Corelib.Init.Logic.False); constr:(@Stdlib.ZArith.BinInt.Z2Pos.inj); constr:(UPOS); constr:(@Corelib.Init.Logic.eq_sym); constr:(@Corelib.Numbers.BinNums.positive); constr:(@Corelib.BinNums.IntDef.Z.to_pos); constr:(@Corelib.Numbers.BinNums.Z); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAllocModel.astate); constr:(@Stdlib.Lists.List.In); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAllocModel.chunk_list); constr:(@Corelib.Init.Logic.ex); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AG_MallocModel.chunk_list_in_iff); constr:(@Corelib.Init.Logic.ex_intro); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AllocWf.WF_chunk); constr:(W); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AllocWf.chunk_ok); constr:(@Stdlib.ZArith.BinInt.Z.le); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Numbers.BinNums.xH); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAllocModel.ch_used); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAllocModel.rq_size); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAllocModel.compute_req); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAllocModel.ch_rz); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAllocModel.rq_rz); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAllocModel.ch_alloc_beg); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAllocModel.ch_primary); constr:(@Corelib.Init.Datatypes.bool); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAllocModel.rq_primary); constr:(@Corelib.Init.Datatypes.true); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAllocModel.ch_class); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAllocModel.class_id); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAllocModel.rq_needed); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAllocModel.class_of_addr); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAllocModel.in_primary); constr:(@Stdlib.ZArith.BinInt.Z.modulo); constr:(@Stdlib.ZArith.BinInt.Z.sub); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAllocModel.region_beg); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAllocModel.class_size); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAllocModel.rg_allocated_user); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAllocModel.get_region); constr:(@Corelib.Init.Datatypes.false); constr:(@Corelib.Init.Datatypes.nat); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAllocModel.schunk); constr:(@Stdlib.Lists.List.nth_error); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAllocModel.as_sec); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAllocModel.sc_map_beg); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAllocModel.kPageSize); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAllocModel.sc_size); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAllocModel.sc_map_size); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAllocModel.round_up); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AllocWf.rz_size_facts); constr:(@Corelib.Numbers.BinNums.xO); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAllocModel.rz_size); constr:(@Corelib.Init.Logic.or); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AG_WFHit.compute_req_facts); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAllocModel.pc_count); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAllocModel.get_pc); constr:(c); constr:(cnt); constr:(AB); constr:(r); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAllocModel.compact_to_addr); constr:(cp); constr:(@Stdlib.micromega.ZifyClasses.rew_iff); constr:(@Stdlib.micromega.ZifyClasses.mkrel); constr:(@Stdlib.micromega.ZifyInst.eq_pos_inj); constr:(@Stdlib.ZArith.BinInt.Pos2Z.pos_is_pos); constr:(@Stdlib.ZArith.BinInt.Z.max_spec); constr:(n); constr:(@Stdlib.ZArith.BinInt.Z.max); constr:(@Stdlib.ZArith.BinInt.Z.pow_pos_nonneg); constr:(@Stdlib.ZArith.BinInt.Z.pow); constr:(@Corelib.Init.Logic.True); constr:(@Stdlib.ZArith.BinInt.Z.pow_nonneg); constr:(@Corelib.Init.Datatypes.nil); constr:(@Stdlib.micromega.ZMicromega.ZArithProof); constr:(@Corelib.Init.Datatypes.list); constr:(@Stdlib.micromega.VarMap.Branch); constr:(@Stdlib.micromega.VarMap.Empty); constr:(@Stdlib.micromega.VarMap.Elt); constr:(@Stdlib.micromega.VarMap.t); constr:(@Stdlib.micromega.Tauto.IMPL); constr:(@Stdlib.micromega.RingMicromega.Formula); constr:(@Stdlib.micromega.Tauto.eKind); constr:(@Corelib.Init.Datatypes.unit); constr:(@Stdlib.micromega.Tauto.isProp); constr:(@Stdlib.micromega.Tauto.A); constr:(@Stdlib.micromega.RingMicromega.Build_Formula); constr:(@Stdlib.micromega.EnvRing.PEc); constr:(@Stdlib.micromega.RingMicromega.OpLe); constr:(@Stdlib.micromega.EnvRing.PEX); constr:(@Corelib.Init.Datatypes.tt); constr:(@Stdlib.micromega.Tauto.AND); constr:(@Stdlib.micromega.RingMicromega.OpLt); constr:(@Corelib.Numbers.BinNums.xI); constr:(@Stdlib.micromega.Tauto.X); constr:(@Stdlib.micromega.Tauto.BFormula); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker_sound); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker); constr:(@Stdlib.micromega.VarMap.find); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAllocModel.kNumClasses); constr:(HC); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAllocModel.req); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAllocModel.rq_rounded); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAllocModel.mkReq); constr:(RQ); constr:(@Corelib.Init.Logic.eq_ind); constr:(PRIM); constr:(@kc__3); constr:(@Stdlib.ZArith.BinInt.Z.land_ones); constr:(@Stdlib.ZArith.BinInt.Z.shiftr); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAllocModel.as_space_beg); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAllocModel.kRegionSizeLog); constr:(@Stdlib.ZArith.BinInt.Z.land); constr:(@Stdlib.ZArith.BinInt.Z.ones); constr:(@Stdlib.ZArith.BinInt.Z.mod_pos_bound); constr:(@Stdlib.micromega.EnvRing.PEpow); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AllocWf.class_size_table_facts); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAllocModel.max_count); constr:(@Corelib.Init.Logic.conj); constr:(@Corelib.Init.Logic.not); constr:(@Corelib.Init.Datatypes.cons); constr:(@Stdlib.micromega.ZMicromega.RatProof); constr:(@Stdlib.micromega.RingMicromega.PsatzAdd); constr:(@Stdlib.micromega.RingMicromega.PsatzIn); constr:(@Corelib.Init.Datatypes.S); constr:(@Corelib.Init.Datatypes.O); constr:(@Stdlib.micromega.RingMicromega.PsatzMulC); constr:(@Stdlib.micromega.EnvRing.Pc); constr:(@Corelib.Numbers.BinNums.Zneg); constr:(@Stdlib.micromega.ZMicromega.DoneProof); constr:(@Stdlib.micromega.Tauto.OR); constr:(@Stdlib.micromega.RingMicromega.OpEq); constr:(@Stdlib.micromega.EnvRing.PEadd); constr:(@Stdlib.micromega.Tauto.NOT); constr:(@Stdlib.micromega.EnvRing.PEsub); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AllocKit.carved); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AllocKit.carved_sep); constr:(CV); constr:(@kc__4); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AG_WFHit.cache_vs_inuse); constr:(rest); constr:(@Corelib.Init.Logic.or_introl); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAllocModel.pc_chunks); constr:(PCS); constr:(FIT); constr:(@Corelib.Init.Datatypes.andb); constr:(@Stdlib.Bool.Bool.andb_false_iff); constr:(@Stdlib.ZArith.BinInt.Z.leb); constr:(@Stdlib.ZArith.BinInt.Z.ltb); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAllocModel.kSpaceSize); constr:(@Stdlib.ZArith.BinInt.Z.leb_gt); constr:(@Stdlib.micromega.RingMicromega.PsatzMulE); constr:(@Stdlib.micromega.RingMicromega.PsatzC); constr:(@Stdlib.micromega.EnvRing.PEmul); constr:(@Stdlib.ZArith.BinInt.Z.mul); constr:(RB); constr:(RNG); constr:(@Stdlib.ZArith.BinInt.Z.ltb_ge); constr:(@kc__1 (@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAllocModel.chunk))|] [|@F; @o; @k; @x; @st; @H; @h; @i; @z; @Ha; @__ff; @__varmap; @__wit; @__x1; @__x2; @__p1; @__arith; @__sat7; @__sat8; @z6; @H6; @z5; @H5; @cstr0; @cstr; @K0; @heq_AB; @heq_U; @heq_cnt; @r; @b; @REST; @PX; @c'; @__sat12; @__sat13; @z11; @H11; @z10; @H10; @z9; @H9; @heq_c'; @__sat14; @__sat15; @LO; @__p2; @__x3; @__x4; @__x5; @__x6; @__x7; @__p3; @__p4; @l; @Ea; @Ec; @__x8; @__x9; @__x10; @__x11; @__p5; @__p6; @__p7; @__p8; @__p9; @D; @CV'; @HC'; @X5; @P8; @P7; @P6; @P5; @P4; @P3; @P2; @P1; @b2; @b1; @y; @__sat9; @__sat10; @z8; @H8; @z7; @H7; @__x12; @__x13; @__p10; @__sat11; @_H; @RQ2; @_H2; @_H1; @X3; @_H0; @RZx; @U4; @U3; @U2; @U1; @OKx; @Hx; @EU; @POS; @K; @a; @c|] "#M\$7&2$T%H%I%G$L$i$?##$7#$$w#%$k%O$y$x#*$N#.%-#&#+#,%M$}#-%/%Z$;#0#'#4$I#/#1#3#(#2%Y#)%8%?%y#5#7%Q%w%L$R#6#8#;%2%6%t#9$_%7#z$V#:%4%5%3%<#C&-&.$=$E$`%'%)%0#]#b#n#s#|%l$:$W#E#[#d#g#i#o#u%b%d%x$6$>$\#=#<#>#?$B%:%;%=#^#_#a#c#e#f#j#k#m#q#r#v#{$%%i%h$1$)&$&+$@$D$S$Q$U#@#A#F%@#K#W%^#`#h#p#t#w#x#y$#$$$*$+%e#}#~$&$,$-$3%k%s$'&&$/&*&4&5&6$G$O$P$Y$Z$[$]${$z$|$~%#%$%%#B%,%+%.%1%>%B%D%F%T%V%W%U%X#O%*#D#G#H#I#J#L#M#N#P#Q#R#S#T#U#V#X%_#Z#\#l%c%a%f%g%j%m%v%u%{%|%}%~&#$($4&'&(&)&%$2&,&/&0&2&1&3&7%`%]$F$C$H$^$f$c$a%&%A$n$K$r$g%E$q%(%P$t$l%K%J%p$X$s$j$v$u$J$e%[$M$p$b$o%9%N$A$d%S%\$m$<$h%R%z%C%q%r%n%oU%^%$*&%_%%`%%a$%b$%c$%d'%e$%f%%g%%h$%i+%j%%k%%l*%m$%n$%o'%p*%q&%r%%s%%t$%u%%v$%w$#[$%x$%y$%z(%{%%|$%}%%~%&#%&$%&%$&&)&')&($&)$&*$&+$&,&&-%&.%&/$&0&&1%LSWUSpIWScS/$#UT2S/G#J$$%JUT3S/$&L#k#$%#j#%(#VSXS/J$*+#VSXS/L$,#)WTY0LJ=LL#$S33#,G%#$#=NL#$S38#,G%#$#j###S$=S',G#=S1L#$S3@#=S7,G#=S:UT4SWUT4$XT5SC$#LYTZ&SWJT[#$C'SWUSdLWSNS/J#USpS'WScS/J#VSXS/N$s#+$#j#&S3#8S3#k##)#USpNWScS/J#$s#1#s#(j#&S3#8S3#USdNWSNS/L#k##%##+#USdS'WSNS/N#k##/#j##&#j##$Jj##1#VT\LJA3+&$#j#'S/#j#(T6#k#'S/.k#(T6#WScS/Js#FVSXS/S)$s#F$#j#&S3#XT]S3#s#KS#WJIS(#l#)+)#USdIWSNS/S##XT^IS(SqJVT_IS(>SY(S)%$#'$C#$C&#HS)?&$C$#=S).S)&#'$C%#MS):-$H#O4S)+0K#$C%#DI,$C'#BI.$H#O9I*-1#3,0$#$C#G%G&&'&;I1<#%%#%3*#$##)##+##1##4##7##<#$H>M$H7MUT2QUT`IWTaQ#LVSXQJ$&$#UTbJ.S%-#S+$C%#UTcJ(S%'#+#$C&#UTdJVTe(S+&#S+$C%##'##-##2#j#*Q#8Q#j#+R#8R##<##>#nH#$##Ks#<#%#@###s#>##s#C##s#G##s#K#j###S$(S,'#C#$C%#HS,?&$C$#=S,.S,&#'$C%#MS,:-$H#O4S,+0K#$C%#DI,$C'#BI.$H#O9I*-1#3,0$#$C#G%G&&'&;I1<#%%#%3*#$##)##+##1##4##7##<#$H>M$H7M.S4-#S+$Cs#J#(S4'#+#$Cs#J###s#C#(##s#R#j#*Q#8Q#j#+R#8R##1##3#nH#$##Ks#1#%#5###s#3##s#8##s#<#%s$1s#WC3$C5#HS4?6$C$#=S4&=&$C$#MS4:<$H#O4S4K>$C$#DIs#%$C&#BIs#'$H#O9I)-s#*#3+0$#$C#G%G&&'&;I0<#%%#%s#.*#$##)##+##1##4##7##;#$H=M$H7M.S5-#S+$Cs$)#(S5'#+#$Cs$)###s#~#(##s$1#j#*Q#8Q#j#+R#8R##1##3#nH#$##Ks#0#%#5###s#2##s#6##s#:#(S0'#C#$C%#HS0?&$C$#=S0.S0&#'$C%#MS0:-$H#O4S0+0K#$C%#DI,$C'#BI.$H#O9I*-1#3,0$#$C#G%G&&'&;I1<#%%#%3*#$##)##+##1##4##7##<#$H>M$H7M.S8-#S+$Cs$g#(S8'#+#$Cs$g###s$`#(##s$o#j#*Q#8Q#j#+R#8R##1##3#nH#$##Ks#1#%#5###s#3##s#8##s#<#j###S$HS5?s#R$C$#=S5&s#Y&$C$#MS5:s#X$H#O4S5Ks#Z$C$#DIs#a$C&#BIs#c$H#O9I)-s#f#3+0$#$C#G%G&&'&;I0<#%%#%s#j*#$##)##+##1##4##7##;#$H=M$H7M.S6-#S+$Cs%D#(S6'#+#$Cs%D###s%=#(##s%L#j#*Q#8Q#j#+R#8R##1##3#nH#$##Ks#0#%#5###s#2##s#6#Cs#J$Cs#L#HS6?4$C$#=S6&;&$C$#MS6::$H#O4S6K<$C$#DIs##$C&#BIs#%$H#O9I)-s#(#3+0$#$C#G%G&&'&;I0<#%%#%s#,*#$##)##+##1##4##7##;#$H=M$H7M.S>-#S+$Cs%}#(S>'#+#$Cs%}###s%v#(##s&)#j#*Q#8Q#j#+R#8R##1##3#nH#$##Ks#0#%#5###s#2##s#6#HS2(S2'#?#$C&#=S2.S2&#)$C%#MS2:*$H#O4S2+-K#$C%#DI,$C'#BI.$H#O9I*-1#3,0$#$C#G%G&&'&;I1<#%%#%3*#$##)##+##1##4##7##<#$H>M$H7M.SD-#S+$Cs&\#(SD'#+#$Cs&\###s&U#(##s&d#j#*Q#8Q#j#+R#8R##1##3#nH#$##Ks#1#%#5###s#3##s#8#j###S$=S>HS>&s#S#$C%#MS>:s#R$H#O4S>Ks#T$C$#DIs#[$C&#BIs#]$H#O9I)-s#`#3+0$#$C#G%G&&'&;I0<#%%#%s#d*#$##)##+##1##4##7##;#$H=M$H7M.S?-#S+$Cs'6#(S?'#+#$Cs'6###s'/#(##s'>#j#*Q#8Q#j#+R#8R##1##3#nH#$##Ks#0#%#5###s#2#HSD?s#G$C$#=S?HS?&9#$C%#MS?:8$H#O4S?K:$C$#DIA$C&#BIs##$H#O9I)-s#&#3+0$#$C#G%G&&'&;I0<#%%#%s#**#$##)##+##1##4##7##;#$H=M$H7M.SJ-#S+$Cs'm#(SJ'#+#$Cs'm###s'f#(##s'u#j#*Q#8Q#j#+R#8R##1##3#nH#$##Ks#0#%#5###s#2#=SE.SEHSE&$#$C&#MSE(SE'#:#$H#O4SE+&K#$C%#DI/$C'#BI1$H#O9I*-4#3,0$#$C#G%G&&'&;I1<#%%#%3*#$##)##+##1##4##7##<#$H>M$H7M.SO-#S+$Cs(I#(SO'#+#$Cs(I###s(B#(##s(Q#j#*Q#8Q#j#+R#8R##1##3#nH#$##Ks#3#%#5###s#5#j###S$MSJ:s#J$H#O4SJKs#L$C$#DIs#S$C&#BIs#U$H#O9I)-s#X#3+0$#$C#G%G&&'&;I0<#%%#%s#\*#$##)##+##1##4##7##;#$H=M$H7M.SF-#S+$Cs(z#(SF'#+#$Cs(z###s(s#(##s)&#j#*Q#8Q#j#+R#8R##1##3#nH#$##Ks#0#%#5##=SOHSO&s#F#$C%#MSF:4$H#O4SFK6$C$#DI=$C&#BI?$H#O9I)-B#3+0$#$C#G%G&&'&;I0<#%%#%s#&*#$##)##+##1##4##7##;#$H=M$H7M.Sr-#S+$Cs)Q#(Sr'#+#$Cs)Q###s)J#(##s)Y#j#*Q#8Q#j#+R#8R##1##3#nH#$##Ks#0#%#5##(SsUTf#)SY)#)#)#>#USZ)%$#)&)#)#)#)#)#)#>#%,##,#0./$C#G$C01>/$C2#>0$C4#>1$C6#>2$C8#>3$C:#>4$C<#$C=41$#1'#1*#1-#10#13#16##8##;#USZs#<%s#)#%$@#$#0&s#,$C#G$C(s#.$C)?$C*>$C+=$C,<$C-;$C.:$C/s#+1$#1&#1(#1*#1,#1.#10##2##5#j###S$(StUSZ#0#s#B$C#G$C%s#D$C&s#5$C's#4$C(s#3$C)s#2$C*s#1$C+s#0$C,s#A1$#1&#1(#1*#1,#1.#10##2#(SuUSZ#%s#V#%$s#M#$#(T7USZ#0#s#[$C#G$C%s#]$C&s#N$C's#M$C(s#L$C)s#K$C*s#J$C+s#I$C,s#Z1$#1&#1(#1*#1,#1.#10##2#(T8'#?#%s#pJ%Js#g#$#j#,C#HT8ZS[C($L#S,%s#v$%%s#m#$#(TgVThIS&UTi#GC#$CTj$m#$#?S\&S-#GC#$CSW$m#$#WTkIS&SGGC#$CS-$m#$#=SeL#$S3s,[#>s,\>%$C$#USvSCUSvCGC'GC'`SPSCC&SK%SQs,c)$+(#XSR+(#T7=T9L#USH#>$,G#USHs,j,G1>s$AVSLS;#,S;$ES;%$C#&#%#%(S;$C&S;#$#1&#VSLS;s,&,S;s,'ES;s,($C#s,)#%#%s,+S;$C&S;#$#1&#>s$VVSw#s$C,G$%Gs$EVSx&s$F,G#k##%#k##'#%G*WSy+s$KLj##SS#j#-%#%G*k##SS#k#-(#UTlS<UT:S<UTmCPCN*C$L#UTnCUToCVSBCs,EFCSY5C$S*#6&FDDE#PUT3DVSBCGNSYFC#5C%S@#6,FDDE#PI-FDDES12.FDDE$#5C)S*-60FDDE#P/1FDDE%,#/2FDDE.-#VTp3EGHOVTqJN$H#Om$%#WTrCGLXTsJN$#l#.*)#l#/=<#l#0BA#j#1C#j#2C#j#3K#%s,bJ,GN##S'%GNk##$#k##'#k#1C#k#2C#k#3K#,S&Tt(TuYJ$S&#STS9l#4/&#l#5s#7s#4#l#6s#Bs#<#l#7s#KC#l#8s#Ns#F#l#9s#VC#l#:s#Ys#Q#l#;s#]s#\#l#<s#as#_#l#=s#es#k#l#>s#rs#s#l#?s#ws#x#l#@s#}s#~#VTvs$'#'s$(CJ(STE#s-#$C%#?J%s%I#%$s%@#$#E)s#k@J%$#&%s#n,%##%#0's#q$C#G+J&*/:JnH#$##C##%#G#1&%#$C'#'8J9950)'$S.$##&##-##0##7##<#l#AAS.#'@C#$C#A?%%s%g#%$s%^#$#@)%A#,$?#$#0&s$1$C#G+/&)-:1nH#$##C##%#G#/&%#$C'#'4J553/)'$S.$##&##-##0##5##:#j###S$(Tw'#?#%s&&#%$s%y#$#E(s$H@(%$#&%s$K,%##%#0's$N$C#G+/&*/:1nH#$##C##%#G#1&%#$C'#C5'#J$$61*($S.$##'##.##1##8#(Se'#C#E%s-{$C$#(T9'#?#%s&G#%$s&>#$#E(s$i@(%$#&%s$l,%##%#0's$o$C#G+/&*/:1nH#$##C##%#G#1&%#$C'#C5'#J$$61*($S.$##'##.##1##8#(Tx'#?#%s&c#%$s&Z#$#E(s%)@(%$#&%s%,,%##%#0's%/$C#G+/&*/:1nH#$##C##%#G#1&%#$C'#C5'#J$$61*($S.$##'##.##1##8#j###S$(TyE#s%A'$@#%%#&&s%E,%##%#0's%H$C#G+*?+&+#:-nH#$##C##%#G#%&%#$C(#C1'#J$$*2+($S.$##'##/##2#(Tz'#?#%s'<#%$s'3#$#(T{E#s%_'$@#%%#&&s%c,%##%#0's%f$C#G+*?+&+#:-nH#$##C##%#G#%&%#$C(#C1'#J$$*2+($S.$##'##/##2#(T;E#s%w'$@#%%#&&s%{,%##%#0's%~$C#G+*?+&+#:-nH#$##C##%#G#%&%#$C(#C1'#J$$*2+($S.$##'##/##2#j###S$(T|'#@#0#s&6$C#G+&?'&'#:)nH#$##C##%#G#%&%#$C(#C-'#J$$*.+($S.$##'##/#(T}E#s&F'$@#%%#&&s&J,%##%#(T~'#@#0#s&P$C#G+&?'&'#:)nH#$##C##%#G#%&%#$C(#C-'#J$$*.+($S.$##'##/#'s%k@#0#s&a$C#G+&?'&'#:)nH#$##C##%#G#%&%#$C(#C-'#J$$*.+($S.$##'##/#j###S$(U#'#+#@$?%&$#:'nH#$##C##%#G#%&%#$C)#C+'#J$$*+,($S.$##'#(U$'#@#0#s''$C#G(U%'#+#@$?%&$#:'nH#$##C##%#G#%&%#$C)#C+'#J$$*+,($S.$##'#(U&'#+#@$?%&$#:'nH#$##C##%#G#%&%#$C)#C+'#J$$*+,($S.$##'#j###S$(U''#C#'#?%@&+':(J((&%$#$S.(#(U('#+#@$?%&$#:'nH#$##C##%#G#%&%#$C)#(U)'#C#'#?%@&+':(J((&%$#$S.(#(T<'#?#(U*'#+#@$&#J:&nH#$##C##%#G#J&%#$C(#j#,C#HT<ZS[C.$L#ST+0@1&#&:3nH#$##C##%#G#(&%#$C(#CS\$C#s'q%s)_s(>%s(?s)V#$#@S\%s(##&s($s(',%##%#0's(*$C#G+S\&*s(I:S\nH#$##C##%#G#s(K&%#$C'#'4J55s(O0)'$S.$##&##-##0##6##:#nH#$##CJ#%#G#s(V&0#$C2#J??s(Y:3J$S..##%##7##:##@##s#$#j#BH#ZT=H9#JOU+&;G$C=#Js#*s#*s(ds#%>O$S.9##%##B##s#%##s#+##s#/#MU,GHJMSf$H#JMS]$H#J(Sz'#:#$H#O4Sz+&K#$C%#.SzDI#$C(#BI%$H#O9I+-(#3-0$#$C#G%G&&'&;I2<#%%#%4*#$##)##+##1##4##8##=#$H?M$H7M.T>-#S+$Cs1a#(T>'#+#$Cs1a###s1Z#(##s1i#j#*Q#8Q#j#+R#8R##1##3#nH#$##KL#%#5##k#C#S$k#Ds#6#j#BH#MU-$H#O(S]'#:#$H#O4S]+&K#$C%#.S]DI#$C(#BI%$H#O9I+-(#3-0$#$C#G%G&&'&;I2<#%%#%4*#$##)##+##1##4##8##=#j##s#:S$4S{(S{'#+#K#$C'#.S{DI#$C*#BI%$H#O9I--(#3/0$#$C#G%G&&'&;I4<#%%#%4*#$##)##+##1##4##8#:s#P$H#O4S|(S|'#+#K#$C'#.S|DI#$C*#BI%$H#O9I--(#3/0$#$C#G%G&&'&;I4<#%%#%4*#$##)##+##1##4##8#4S^(S^'#+#K#$C'#.S^DI#$C*#BI%$H#O9I--(#3/0$#$C#G%G&&'&;I4<#%%#%4*#$##)##+##1##4##8#j###S$4S}.S}DI#$C%#BI%$H#O9I(-(#3*0$#$C#G%G&&'&;I/<#%%#(S}'#+#%#-#'##,##.##4##7#4Sg(Sg'#+#K#$C'#4S~.S~DI#$C%#BI%$H#O9I(-(#3*0$#$C#G%G&&'&;I/<#%%#(S~'#+#%#-#'##,##.##4##7#4T#.T#DI#$C%#BI%$H#O9I(-(#3*0$#$C#G%G&&'&;I/<#%%#(T#'#+#%#-#'##,##.##4##7#j###S$.ShBI#$H#O4Sh9I#-'#3%0$#$C#G%G&&'&;I*<#%%#(Sh'#+#%#-#'##,##.##5#4T?.T?DI#$C%#.SiBI#$H#O4Si9I#-'#3%0$#$C#G%G&&'&;I*<#%%#(Si'#+#%#-#'##,##.##5#.T$BI#$H#O4T$9I#-'#3%0$#$C#G%G&&'&;I*<#%%#(T$'#+#%#-#'##,##.##5#j###S$.T%4T%9I#-%#3%0$#$C#G%G&&'&;I*<#%%#(T%'#+#%#-#'##,##.#.U.BI#$H#O.T&4T&9I#-%#3%0$#$C#G%G&&'&;I*<#%%#(T&'#+#%#-#'##,##.#.S_4S_9I#-%#3%0$#$C#G%G&&'&;I*<#%%#(S_'#+#%#-#'##,##.#j###S$.Sj4Sj9I#-%#%G#3&&%#;I(<#%%#(Sj'#+#%#*#'##-#.T@4T@9I#-%#3%0$#$C#G.T'4T'9I#-%#%G#3&&%#;I(<#%%#(T''#+#%#*#'##-#.T(4T(9I#-%#%G#3&&%#;I(<#%%#(T('#+#%#*#'##-#j###S$.S`4S`9I#-%#3%&$#;I'<#%%#(S`'#+#%#*#'#.TA4TA9I#-%#%G#.Sk4Sk9I#-%#3%&$#;I'<#%%#(Sk'#+#%#*#'#.T)4T)9I#-%#3%&$#;I'<#%%#(T)'#+#%#*#'#j###S$(TB'#+#4TB3#%%#.TC4TC9I#-%#3%&$#;I'<#%%#(TD'#+#4TD3#%%#(SM'#:#(T*'#+#@$HT*&$#nH#$##CJ#%#G#$&$#$C(#j#BH#ZT=H-#SeOSs+/@0HSM&$#&#G$C'#4T*.SaDI#%GJ,Js/s#$#j#EC#UU/I-)#VSl#SmNs01>#4SaGC#$CJ$m#$#Ls.m=TEL#$S3%#>&>%$C$#GC%GC%`SPSCCs.hSKs.gSQ+'$)&#XSR)&#SM=TFL#USH#>$,G#USH2,G/(TGVSL#s.e,$s.fE%s.g$C#s.h#%#%s.j($C&)#$#1&#(THE#s.oVSBCs#%5Cs.CS*#6s.JFDDE#Pl#.#s.:s.4l#/s.Ps.M#l#0s.Ss.R#%Gs#+l#4$#Jl#Fs.Zs.W#l#Gs.es._#l#H-C#l#I80#l#Js.pC#l#Ks.ss.k#l#Ls.{C#l#Ms.~s.v#l#;@?#l#<s#$B#l#=s#(s#,#l#>s/;s/<#l#@s/Es/F#l#Ns#6s#7#WU0s#=s#;#UU1s#<VTIs#?#VSxs.vs#>0s#A#$C%#.TJ-#s#FVSl#Sm0#(j#,Cs#KVU2%*,G+.TK-#s#MVSl#Sm0#/%G#,$1#$#k##*#4TKGC#$CN$m#$#=T+L#$S3s#Q#>$$Cs#O#GC$`SPSCCs/VSKs/USQs#Us#Qs#N'%#XSR'%#Sa=TLL#USH#>$,G#(TMVSL#s/Q,$s/RE%s/S$C#s/T#%#%s/V($C&)#$#1&#(TNE#s/[VSws/Is#mk##s#Es#)k##s/I#WSys/Ls#pLj##SS#j#-s/F#%Gs#7k##SS#k#-s/I#VSBCs/RUT,s#xWT-C$#5Cs/:S@#6s/AFDDE#P5Cs/@S@%6s/CFDDE#P2s/DFDDEs/6#/s/EFDDE&s/@#VSBCs1?5Cs/ES@#6s/HFDDE#P2s/IFDDEs/;#/s/JFDDEs/>s/E#/s/KFDDE(s/F#l#.#s/;s/5l#/s/Os/N#l#0s/Ts/S#j#1C#j#2C#j#3K#%GL,Ls#P#$#k##s#I#,Ns1O#s/6#k##s/8#k##&#k#1C#k#2C#k#3K#,S&s1V.TO-#s$@VSl#Sm0#s#^YJ'S&#S2S9l#44)#l#Fs#-s#*#l#Gs#3s#1#l#Os/ps/m#l#Ps/{s/u#l#Hs#7C#l#Is#Bs#:#l#Js0*C#l#Ks0-s0%#l#Ls05C#l#Ms08s00#l#;s$6s$5#l#<s#Ls#J#l#=s#Ps#S#l#>s0Qs0R#l#@s0[s0\#l#Ns#[s#\#l#)s#is#`#Ns/nN#N#>#VTIs#q#ZS[Cs#qs#p(#Jl#Qs#{s#v#%Gs$b,s$cs1v#$#m#&#ZS[Cs$fs$b#JSDVU3LJ3L%G#)s2()#)#)#)#>#%*##*#0,s2)$C#G%s9tL3N%s2-#k##%#UTPL%G#%$s2A#$#UTPN%s0P#k##,#0)s0R$C#G#%##)##.##3##6#$C3GUU4#9IN-s$:#%G#0$8$C#G&&:;IN<#%%##'##*##.#2s0RFDDEs0Ds0GIs0SFDDES72s0TFDDEs0J#/s0UFDDE#s0Ps0G/s0VFDDE&s0Q#l#.#s0Fs0@l#/s0Zs0Y#l#0s0_s0^#j#1C#j#2C#j#3K#j#RK##s%CN#s0@S1k###s0?k##%#k#1C#k#2C#k#3K#k#RK#,S2s2_ZJs#h#S&S2S6S9l#4-%#l#Fs0ss0p#l#Gs0~s0x#l#Hs$:C#l#Is$Es$=#l#Js1-C#l#Ks10s1(#l#Ls18C#l#Ms1;s13#l#;s%9s%8#l#<s$Os$M#l#=s$Ss$V#l#>s1Ts1U#l#@s1^s1_#l#Ns$^s$_#2s0wFDDEs0ls$1/s0xFDDEs#&s0ss$2/s0yFDDE$s0t#l#.#s0is0cl#/s0}s0|#l#0s1&s1%#j#1C#j#2C#j#3K#j#RK##Ns%ek##s#%s$.k##$#k#1C#k#2C#k#3K#k#RK#%GS2ZJs$.#S&S2S6S9l#4,%#l#Fs19s16#l#Gs1Ds1>#l#Hs$\C#l#Is$gs$_#l#Js1OC#l#Ks1Rs1J#l#Ls1ZC#l#Ms1]s1U#l#;s%[s%Z#l#<s$qs$o#l#=s$us$x#l#>s1vs1w#l#@s2$s2%#l#Ns%$s%%#XSbs0xs$Es#%#RTQR#R#R#R#R#R#QC#UU5SYVU6C#QC'WSIC$#QC*WSIC&#QC-QC/QC1QCTQ7C$#7C&#7C(#7C*#7C-#7C2#T#SAT%SASS<#s1^SS<%#PCS#*C#S#s1_*C#S#s1`*Cs1aS##PCS7*C#S#s1c*C#S#s1d*C#S#s1e*C'S##PCS1*Cs1hS##*C#S#s1iPCS:*C#S#s1k*C#S#s1lPCS'*C#S#s1n*C%S##*C)N#*C-L#Is1nFDDES)Ns3zN#FC#VSBCs2>5C$S=#6s1tFDDE#P2s1uFDDE)#Ns&TN#FC#5C)S*#6s1zFDDE#P5C,S=%6s1|FDDE#P2s1}FDDE%#[Sns1~FDDE+#)2FC#Ns41)#)#FC#)s1~)#N#FC#OC'#OC#s2(5C-S=#6s20FDDE#P5C>S*+6s22FDDE#PIs23FDDES,2s24FDDE$#VSBCs4>5C#S*,6s27FDDE#PIs28FDDES%2s29FDDE$#5C8S*s286s2;FDDE#PIs2<FDDES42s2=FDDEs23#5Cs2<S=s286s2?FDDE#PZU7s2@FDDE#/s2AFDDE&s2<#/s2BFDDE)s2=#/s2CFDDE,s2>#/s2DFDDE2s2?#/s2EFDDE7s2@#/s2FFDDEs#&s2A#l#.#s26s20l#/s#9s2I#l#0s#Ns2N#j#1C#j#2C#j#SC#j#TC#j#UC#j#VC#j#WC#j#3K#j#RK#j#XK#j#YK#$CS7s2}#S##%s3#N$CS7N#$#1&#&S#S1&#G$CS7#%S#S(##S,%s4iS:##S4%S(S1,GS:##S8$CS:Gk###S$k##%#k##(#k##*#k##-#k##0#k##4#k#1C#k#2C#k#SC#k#TC#k#UC#k#VC#k#WC#k#3K#k#RK#k#XK#k#YK#HT.%#s4x(T.'#@#&S's3I,$#,'s3K+'3S2eJs&'+&%(S'$,*S&#S1S>S^S_SDS9l#4s#1.#l#Fs32s3/#l#Gs3=s37#l#Hs&UC#l#Is&`s&X#l#Js3HC#l#Ks3Ks3C#l#Ls3SC#l#Ms3Vs3N#l#;s'Ts'S#l#<s&js&h#l#=s&ns&q#l#>s3os3p#l#@s3ys3z#l#Ns&ys&z#*Cs$+Ns3:*C#Ls3;FCs5EWU8Cs37#5Cs34S*#6s3;FDDE#PFCs5H5Cs37S@#6s3>FDDE#P2s3?FDDE#s%J/s3@FDDE#s3;'/s3AFDDE(s3<#l#.#s31s3+l#/.s3D#l#0s3Js3I#j#1C#j#2C#j#SC#j#3K#-JL%G#,GS'##S1-NS'%G#k##%#k##(#k#1C#k#2C#k#SC#k#3K#9IS2.T.ZJs&XS&$#SFS9l#42&#l#Fs3cs3`#l#Gs3ns3h#l#Hs'*C#l#Is'5s'-#l#Js3yC#l#Ks3|s3t#l#Ls4(C#l#Ms4+s4##l#;s()s((#l#<s'?s'=#l#=s'Cs'F#l#>s4Ds4E#l#@s4Ns4O#l#Ns'Ns'O#WSICs$~s$w7C#s$wT#SASS<#s3p/s3kFDDEs3_s3fs$./s3lFDDEs$/s3g#l#.#s3\s3Vl#/s3ps3o#l#0's3t#j#1C#j#2C#j#3K#$CJG$CNGk##s3U#k##%#k#1C#k#2C#k#3K#-s#&s#'0#s#XYJs&}S&#SuS9l#4-&#l#Fs4,s4)#l#Gs47s41#l#Hs'OC#l#Is'Zs'R#l#Js4BC#l#Ks4Es4=#l#Ls4MC#l#Ms4Ps4H#l#;s(Ns(M#l#<s'ds'b#l#=s'hs'k#l#>s4is4j#l#@s4ss4t#l#Ns'ss't#*Cs%+Ns%0*C#Ls%&OCs#Ws4*5C#S*s#U6s44FDDE#PFCs$j5Cs40S@#6s47FDDE#PIs48FDDES#2s49FDDE$#/s4:FDDE#s45(/s4;FDDE)s46#l#.#s4+s4%l#/.s4>#l#0s4Ds4C#j#1C#j#2C#j#SC#j#TC#j#UC#j#3K#&s#ZN%#S',GS7##S:&s#ZS1%#S7k##%#k##(#k#1C#k#2C#k#SC#k#TC#k#UC#k#3K#;IS2<#\Js'VS&#s$2s#^s#]S?S9l#44&#l#Fs4as4^#l#Gs4ls4f#l#Hs((C#l#Is(3s(+#l#Js4wC#l#Ks4zs4r#l#Ls5&C#l#Ms5)s4}#l#;s)'s)&#l#<s(=s(;#l#=s(As(D#l#>s5Bs5C#l#@s5Ls5M#l#Ns(Ls(M#XSbs&ys&us#8#XSbs&|s&us#^#XSbs'$s&us$4#XSbs'os&us&-#l#)s'Fs'(#WU9ILs(dm#$#\U:IS&S-Ns(_SqU;J$CS&N$CS-s(a#$#3S&&S-#%#s(e&s(fs'B%#S-1%#1)#$CS&S'.TE$CS-##%#%,%3S'&'#%#S-1&#1(#j###S$$CS&S1.TF$CS-##%#$CS&S7.T+$CS-##%#j###S$.TL$CS-#$CS&S#.U<$CS-#4T/GC#$CS)$m#$#=TML#$S3s)n#>$$Cs)l#GC$`SPSCCs5sSKs5rSQs)rs)ns)k'%#XSR'%#TR=TNL#USH#>$,G#(TOVSL#s5n,$s5oE%s5p$C#s5q#%#%s5s($C&)#$#1&#(U=E#s5xPCL5Cs5LS@s5P6s5SFDDE#P2s5TFDDE#s(j/s5UFDDE#s5Ps(jl#.#s5Es5?l#/(s5X#l#0s5^s5]#j#1C#,GJ##s*?,Ls7U#s(i#k##%#k#1C#VJS&S9l#4*$#l#Fs5ls5i#l#Gs5ws5q#l#H6C#l#IA9#l#Js6&C#l#Ks6)s5}#l#Ls61C#l#Ms64s6,#l#;s*2s*1#l#<s#+s#)#l#=s#/s#2#l#>s6Ms6N#l#@s6Ws6X#l#Ns#:s#;#%GS&##s5Jm#%#UT:CSCSGTSWSNCSGJj#Z%#$CSGSGWSNCSGTSGCSGWU>%$#UU?s6hZS[+*($#U@.T/XT5Cs6a#J^UAIS&SGT/Sq/%TJT;#j#[s#O#j#\s#R#V#LJj##s#U#j##s#\#As#]s#[s#Y#Jj#)s#_#U#Jj##s#l#%s#vs#d3S1&s#f#%#S-1&#%s#{s#e3S7&s#g#%#S-1&#j###S$%s$%s#g4TRGC#$CS#$m#$#=TGL#$S3s*s#>$$Cs*q#GC$`SPSCCs6xSKs6wSQs*ws*ss*p'%#XSR'%#T+=THL#USH#>$,G#VSLs&.s6rEs&/s6s$C#s6t#s&,#%s6vs&2$C&s&3#$#1&#(UBE#s6{Rs'nR#QC#QC%WSICs'o#WSICs'ps'jQCs'z7Cs'k#7C%#7Cs'o#7Cs'q#7Cs'u#7Cs'y#7C+#7C.#T#SAT%SASS<#s6kSS<%#PCS,*Cs6lS%#*C#S's'iPCS(PCS%*C$S%#*C#S%s'q*C'N#PCS)*C#S:s6t*Cs6uS1#*C#S%s6v*C'L#Is6tFDDES0Ns'NFC#5C#S=s'c6s6xFDDE#P2s6yFDDE'#5Cs'fS*s6x6s6{FDDE#P5C(S=s6z6s6}FDDE#P2s6~FDDE%#[Sns7#FDDE(#FCs'\FCs+_OC$#)0FC#5C%S*#6s7*FDDE#PIs7+FDDES5Is7,FDDES8)s)rFC#5C7S*#6s70FDDE#PIs71FDDES62s72FDDE$#Is73FDDES2FCs'hOC)#OC#s705Cs&YS=#6s78FDDE#PIs79FDDES>2s7:FDDE$#2s7;FDDE*#2s7<FDDE,#2s7=FDDE3#2s7>FDDE5#)s'sFC#5Cs'jS*#6s7BFDDE#PIs7CFDDESD2s7DFDDE$#)s,#N#FC#OCB*5C$S=#6s7JFDDE#POCs#)95C'S=#6s7MFDDE#P5Cs&pS*s#+6s7OFDDE#P5Cs7JS@s&v6s7QFDDE#PIs7RFDDES?2s7SFDDE$#Is7TFDDESE/s7UFDDE$s7P#/s7VFDDE)s7Q#/s7WFDDE,s7R#/s7XFDDE0s7S#/s7YFDDE7s7T#/s7ZFDDE>s7U#/s7[FDDEs#3s7V#/s7\FDDEs#;s7W#l#.#s7Ls7Fl#/s#Is7_#l#0s#Ws7d#j#1C#j#2C#j#SC#j#TC#j#UC#j#VC#j#WC#j#]C#j#^C#j#_C#j#`C#j#3K#j#RK#j#XK#j#YK#j#aK#j#bK#j#cK#j#dK#j#eK##S%s'}%s8AJ$CS7J#$#1&#&S(S1%#S%#s'{S6&S(S:&#G$CS1###S>#S2##(##S8##S5#%s:1S4##S?&S5S0$CS4#&S4S)$CS0#%S(S),GS(##Ssk###Stk##&#k##(#k##+#k##.#k##1#k##;#k##>#k#1C#k#2C#k#SC#k#TC#k#UC#k#VC#k#WC#k#]C#k#^C#k#_C#k#`C#k#3K#k#RK#k#XK#k#YK#k#aK#k#bK#k#cK#k#dK#k#eK#HSo%#s:M&S#s8w,s3U#$Cs3[S7.So=Soi#?JS$s+U(s35s3S&s3Z%s8z$)#S-s3YS#s9<s&Bs3RS&S;S(S8SfS`SMTTTUS9l#4s#@+#l#Fs8`s8]#l#Gs8ks8e#l#Hs$cC#l#Is$ms$f#l#Js8vC#l#Ks8ys8q#l#Ls9%C#l#Ms9(s8|#l#;s-&s-%#l#<s$vs$t#l#=s$zs$}#l#>s9As9B#l#@s9Ks9L#l#Ns%)s%*#j#fs%.#U#Jj##s%6#3S:&s&;#%#S-WSICs*%s$n7Cs){#7Cs)}#7Cs*##7Cs*%#7Cs*)#7Cs*-#7Cs$w#7Cs$z#T#SAT%SASS<#s8{SS<%#*Cs$kS%s8{*C#S%s)p*Cs$lS%s8}*C#Ns8~*C%S%#*Cs$kS's9$*C#S%s*%*Cs)~S%s9&*C$S%#*C'L#*Cs)|S%s9)*Cs9*S%#*Cs$zS%s9+*C#S%s9,*C#S%s9-*C&S%#*C)S%#2s9,FDDEs$rs)r)s)qFC#5Cs)wS*#6s90FDDE#P5Cs)zS=%6s92FDDE#P2s93FDDE%#[Sns94FDDE*#FCs;;OCs$l#5C#S*s$q6s98FDDE#P5Cs)bS*s$c6s9:FDDE#P2s9;FDDE#s$m2s9<FDDE#s$i2s9=FDDEs$p#OCs)ts$\OC#s995Cs)zS=#6s9AFDDE#P2s9BFDDEs)ns$m5Cs)}S*06s9DFDDE#P2s9EFDDEs$Rs$j/s9FFDDE#s9As$a/s9GFDDEs$Xs9B#/s9HFDDEs$\s9C#/s9IFDDE's9D#/s9JFDDE*s9E#/s9KFDDE,s9F#/s9LFDDE1s9G#/s9MFDDE7s9H#/s9NFDDE<s9I#l#.#s9>s98l#/s#'s9Q#l#0s#9s9V#j#1C#j#2C#j#SC#j#TC#j#UC#j#VC#j#WC#j#]C#j#^C#j#_C#j#`C#j#3K#j#RK#j#XK#j#YK#j#aK#j#bK#j#cK#$CS)s:0#S%#%s:2S1$CS)S1#$#1&#&S#S(%#S'%s;uS'##S8##S6#S5#&S0S(&#G$CS%#%S0S5##SD%S0S4&S4S%$CS)#&S)S($CS,##s$MSFk###Srk##%#k##(#k##+#k##-#k##0#k##4#k##9#k##<#k#1C#k#2C#k#SC#k#TC#k#UC#k#VC#k#WC#k#]C#k#^C#k#_C#k#`C#k#3K#k#RK#k#XK#k#YK#k#aK#k#bK#k#cK#(So'#@#,#s)z%S#s5C##s$M##s4{,)s:i+)3SJi#>JS$s-E)&s5Ks$Q%*S'$#s$Ps$U,s$OS-s;,S&S1S8SfSOShSFSMTTS9l#4s#@.#l#Fs:Ps:M#l#Gs:[s:U#l#Hs&SC#l#Is&]s&V#l#Js:fC#l#Ks:is:a#l#Ls:qC#l#Ms:ts:l#l#;s.rs.q#l#<s&fs&d#l#=s&js&m#l#>s;1s;2#l#@s;;s;<#l#Ns&us&v#j#fs$I#U#Jj##s'##ZT0s''s'$s&~s$O#Jj#)s')#U#Jj##s(9#ZT0s(?s(:s(8s'1#Jl#%s(Ns(D#l#gs(Ps(Q#l#hs-<s/A#l#Es/GC#l#is/Os/I#j#js/^#j#ks/e#V#LJj##s/p#j##s/}#As/~s/zs/x#Jj#)s0,#j#ls0;#V#LJj##s0B#j##s0]#As0^s0Ts0R#Jj#)s0d#j#ms0u#V#LJj##s0~#j##s1@#As1As16s14#Jj#)s1I#j#ns1]#V#LJj##s1b#j##s2.#As2/s1ys1w#Jj#)s23#j#os2J#V#LJj##s2P#j##s2}#As2~s2js2h#Jj#)s3'#j#ps3A#V#LJj##s3I#j##s3z#As3{s3fs3d#Jj#)s4&#j#qs4C#V#LJj##s4G#j##s5[#As5\s5Bs4e#Jj#Cs4g#j#Ds5+#$Hs5-M$Hs5*M$Hs4~M-s4dS+$CsDF#$CsDCs4i##sD<#%##sDK#j#*Q#8Q#j#+R#8R##-##/#j##s5AS$$Hs4nM-s4TS+$CsDT#$CsDQs4Y##sDJ#%##sDY#j#*Q#8Q#j#+R#8R##-#$Hs4gM$Hs4]M-s4-S+$CsDa#$CsD^s3z##sDW#%##sDf#j#*Q#8Q#j#+R#8R##-#$Hs4MM.Sg-#S+$CsDn#$CsDks3}##sDd#%##sDs#j#*Q#8Q#j#+R#8R##.#j###S$-s4'S+$CsDz#$CsDws3t##sDp#%##sE##j#*Q#8Q#j#+R#8R#BI9$H#M-s3]S+$CsE*#$CsE's3O##sD|#%##sE/#j#*Q#8Q#j#+R#8R#VT1LJ$H#M$HNM$HLM1$#k##&#$HJM1&#VT1NL$H#Mk##%##(#$HS'M1#-k##'#j##&#VT1S'N$H#Mk##0#j###Lj##1#VUCLJA3.)$#j#rH#j#sH#k#rH6k#sH#VSUs0zs4&&s0{UDVSVs4(#WJ%#N$H&M$H%M1$#VSUs1%s3r$H#MNs,~>#VSxs<]#&s1*#VSVs3x#$H#M1)#j###S$VSUs1/s3y$H#MVSULJ$H#M,LNk##$#,JLVSUNL$H#Mk##%##'#,NS'k##&#j##%#VSUS'N$H#Mk##.#j###Lj##/#VUELJA1-)$#j#tC#j#'C#k#tC4k#'C#WJs1Hs3eL,s3fs1I=S_L#$S3s1C#>$$Cs1A#GC$`SPSCCs=HSKs=GSQs1Gs1Cs1@'%#XSR'%#Si=SjL#USH#>$,G#VSLs2?s=B,s2@s=CEs2As=D$C#s=E#%#%s=Gs2D$C&s2E#$#1&#Es2:s=K)s/V)#)#)#)#)#)#)#)#)#)#)#)#)#)#)#>#VUFC#WUGC#s.E7Cs);#7Cs,/#7Cs)>#7Cs.L#7Cs.O#7Cs.R#7Cs.V#T#SASS<#s=E*Cs=DS(s.D*C#S(s.6*Cs.BS(s)6*C#Ns=G*C%L#*Cs.@S(s=I*Cs.>S(s=J*C$S(#*C#S(s=L*C'S(#2s=JFDDEs&ns-p2s=KFDDE#s-m2s=LFDDEs-w#VSBCs?L5Cs(lS*#6s=OFDDE#P2s=PFDDEs):#5Cs)+S@s+z6s=RFDDE#PFCs.BUT,s?ZWT-Cs0v#WUHCs,|#OCs,$#5C'S=#6s=YFDDE#P5C)S*s)86s=[FDDE#P2s=\FDDE#s)32s=]FDDEs(js)3/s=^FDDE#s=Ys)//s=_FDDE%s=Z#/s=`FDDE)s=[#/s=aFDDEs(rs=\#/s=bFDDEs(vs=]#/s=cFDDE3s=^#/s=dFDDE6s=_#/s=eFDDE;s=`#l#.#s=Us=Ol#/@s=h#l#0s#+s=m#j#1C#j#2C#j#SC#j#TC#j#UC#j#VC#j#WC#j#]C#j#3K#j#RK#j#XK#j#YK#j#aK#j#bK#j#cK#%s@%N##S)##S,#S(#%S#s?{#S4#,S)S'&S,S)$CS(#$CS)s(cVTVS7s>7&S:#$CS(#%S)S,##S>,GS###S?k###SJk##&#k##)#k##-#k##/#k##2#k##4#k##7#k#1C#k#2C#k#SC#k#TC#k#UC#k#VC#k#WC#k#]C#k#3K#k#RK#k#XK#k#YK#k#aK#k#bK#k#cK#9IS&)s)v)#)#)#)#)#)#)#)#)#)#)#)#)#)#)#)#)#)#)#)#)#)#)#)#)#)#)#>#&@#%s,P#,Gs,R%s,Ss1:#$##&#%s@qs3T.SM=SMi#:JS$s1l&%s'-s9rs(x$s3W#S-s#)s?Ss3LS&STSfS5S^S`TWTXS9l#4s#Ss#+#l#us>ws>t#l#vs?&s>|#l#ws$NC#l#xs$Xs$P#l#ys?1C#l#zs?4s?,#l#7s?<C#l#8s??s?7#l#;s3=s3<#l#<s$as$_#l#=s$es$h#l#>s?Xs?Y#l#@s?bs?c#l#ps$qs$p#l#)s$us$s#j#ps%/#U#Jj##s%;#VSVs6Ns%8$H#MVSVLJ$H#M%LNk##$#%JLVSVNL$H#Mk##%##'#%NS'k##&#j##%#VSVS'N$H#Mk##.#j###Lj##/#VUILJA1-)$#j#tC#j#'C#k#tC4k#'C#WJs6:s%QL%s%Rs6;VSws?Ss%U%Gs%V,Gs%Vk##$#k##s?U#WSys?Xs%ZLj##SS#j#-s?R#%Gs%\k##SS#k#-s?U#Rs+RR#R#QC#QC%WSICs0e#QC(WSICs0gs+X7Cs0as$y7Cs0c#7Cs0e#7Cs0h#7Cs0j#7Cs0o#7Cs+^#7C*#7C,#7C.#7C1#T#SAT%SASS<#s?dSS<%#PCS4*Cs?eS0#*C#S's0ZPCS0*Cs+[S0#*C#S7s+Y*C&N#*Cs+VS0s?k*Cs+[S#s?l*C$S1#*C#S0s?n*C'L#2s?lFDDEs+Bs+R[Sns?mFDDE#s+M2s?nFDDEs+@s+72s?oFDDEs+9s*{2s?pFDDEs+/#2s?qFDDE%#2s?rFDDEs+A#2s?sFDDEs+D#2s?tFDDEs+4s*~UT,s&1WT-Cs3;#OCs.D#5C#S*s+R6s?yFDDE#PIs?zFDDESJVSBCs#xOCs%+#5Cs+YS*#6s?~FDDE#PIs@#FDDESO2s@$FDDE$#2s@%FDDE)#5Cs/LS@s3>6s@'FDDE#P2s@(FDDEs+5#Is@)FDDESF/s@*FDDE$s@%#/s@+FDDEs+:s@&#/s@,FDDE)s@'#/s@-FDDEs%2s@(#/s@.FDDEs+?s@)#/s@/FDDEs+Cs@*#/s@0FDDE5s@+#/s@1FDDE;s@,#/s@2FDDE=s@-#/s@3FDDEs#$s@.#l#.#s@#s?yl#/s#(s@6#l#0s#5s@;#j#1C#j#2C#j#SC#j#TC#j#UC#j#VC#j#WC#j#]C#j#^C#j#_C#j#`C#j#{C#j#|C#j#3K#j#RK#j#XK#j#YK#j#aK#j#bK#j#cK#j#dK#j#eK#j#}K#$CS:s@v#S0#$CS:J#s+:#1%##s0SS2$CS's+5##SD#S>##&##S6##S8#%sBcS0##SE&S#s&r%#S8&S6S8$CS5#&S5S,$CS8#VTVS#s@s&S,#$CS5#&S6S,&S8s$c%$###Su#St#%S,S%,GS,,S,sBe#$#k###STk##'#k##)#k##/#k##3#k##6#k##9#k##<#k##?#k##s#'#k#1C#k#2C#k#SC#k#TC#k#UC#k#VC#k#WC#k#]C#k#^C#k#_C#k#`C#k#{C#k#|C#k#3K#k#RK#k#XK#k#YK#k#aK#k#bK#k#cK#k#dK#k#eK#k#}K#%s%MS-HSa%#sC4&S)sA^,s<<#$Cs<BS#=Sai#DJS$s%2)'s;ws<9%s<@$sA`s5}(#S-s%Ts<?S)sA~s5ws/(s<8S&S;S,SeS]S6SgSkTWTXTUS9l#4s#L+#l#usAFsAC#l#vsAQsAK#l#~s$Ws$T#l#Fs$_s$[#l#ws&{C#l#xs')s&}#l#ysA^C#l#zsAasAY#l#7sAiC#l#8sAlsAd#l#;s5js5i#l#<s'2s'0#l#=s'6s'9#l#>sB)sB*#l#@sB3sB4#l#ps$ms$l#l#)s$qs$o#j#ps%+#U#Jj##s'b#ZT0s'is'cs'as%0#Jl#ps'os'l#l#)s'vs't#j$#s(4#j#ps(?#V#LJj##s(C#j##s([#As(\s(Qs(O#Jj#)s(^#j#qs(k#V#LJj##s(n#j##s;o#As;ps;`s(|#Jj#Cs(~#j#Ds)1#XUJs;^s)3#LV#JSTl#Ds<=s<;#l#Bs<?H#l$$s<Js<A#l$$UKs<W#l#is<ys<r#j$%s=-#j#is=8#V#LJj##s=D#j##s=U#As=Vs=Rs=P#Jj#)s=a#j$&s=q#V#LJj##s=x#j##s>:#As>;s>/s>-#Jj#)s>@#j$'s>S#V#LJj##s>]#j##s?%#As?&s>ss>q#Jj#)s?/#j$(s?H#V#LJj##s?P#j##s@$#As@%s?ls?j#Jj#)s@,#j$#s@I#V#LJj##s@P#j##sA*#AsA+s@ps@n#Jl#)sAOsA/#l$)sBysBv#j$#sC'#j$)sC<#V#LJj##sCC#j##sCl#AsCmsC[sCY#Jl#)sD@sCr#j#CsDC#j$*sDs#V#LJj##sDy#j##sF%#AsF&sEPsEN#Jj#)sF,#j$+sFa#V#LJj##sFf#j##sGv#AsGwsGBsG@#Jj#)sG}#j$,sHY#V#LJj##sH]#j##sIt#AsIusI<sI:#Jj#)sIz#j$-sJY#V#LJj##sJ\#j##sL-#AsL.sKBsK@#Jl$.sL3sL2#l$/sL7sL5#l$0sL^sL]#j$1sLd#j$2sLg#V#LJj##sLl#j##sLr#AsLssLrsLp#Jl$3sL|sLw#VULsL~#j#$sM%#j#'S/#U#Jj$4S/#$sM1sM2sM.GsM2sM/j#$$#YUMS/sM.&#LU#Jl#$sM5sM4#l#%sM8sM7##"). Qed.

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
