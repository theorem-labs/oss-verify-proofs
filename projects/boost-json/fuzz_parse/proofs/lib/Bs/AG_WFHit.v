(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Bs Require AW_0Gc. (* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From Stdlib Require Import FMapPositive.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import AsanAllocModel.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Bs Require Import AllocWf AllocKit AG_MallocModel.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib4Init5Logic02eq37Corelib7Numbers7BinNumsh81Z37Corelib4Init9Datatypesj54list69OSSVerify6Proofsaboost_jsonafuzz_parse3libeAsanAllocModel~~~~~~l48as_cachel4fas_cache_initedl49as_chunksl45as_gql4das_n_reservedl49as_qcachel47as_qmaxl47as_qminl4aas_regionsl46as_secl4cas_space_begl45as_tql46astatel46qcache79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs7AllocWf~~~~~~hj52WFj54booll45chunkl46pclassl46regionl46schunk46Stdlib5FSetscFMapPositivebPositiveMaphq21t79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2BseAG_MallocModel~~~~~~hsefsame_but_shadowl4bch_user_beghq23keyj54Somej56option03andl44ckeyhq24find46Stdlib6ZArith6BinInt1Zile2lt79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs8AG_WFHit~~~~~~inc7keys_okl4achunk_list36Stdlib5Lists4Listit25NoDup03iffit22Inl49upd_chunkj54Nonej54cons36Stdlib7SortingbPermutationjh3bPermutationl4arq_roundedl45rq_rzl47rq_sizeile2leile3addile3maxl4bcompute_reql43reql49rq_neededl4arq_primaryl45mkReqile6moduloj53appit28flat_map03notj53nat37Corelib5Lists7ListDefjsd3mapjsd3seqile6of_nat05Falsej54truel4cch_alloc_begl4ach_primaryl4fcompact_to_addrl46get_pcl4bkNumClassesl49pc_chunksit2afold_right" s.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Lemma WF_ext : ltac2:(zQ "h80!h4!j1!kd!p5!q0!r2!re!s6!t6!u2!uc!v6!hg3!hgc!hhb!hi3!hic!hn2!hn8!hnf!ho7!hp0!hp9!hs9>1a$f>1b$f>0@3$0$1@1$d^2@1$d^1>0@3$0@1$2$h5@1$b^3@1$b^2>0@3$0$h2@1$4^4@1$4^3>0@3$0@1$2$h4@1$3^5@1$3^4>0@3$0$1@1$7^6@1$7^5>0@3$0@1$2$h6@1$c^7@1$c^6>0@3$0@1$h7$h3@1$5^8@1$5^7>0@3$0$h0@1$e^9@1$e^8>0@3$0$h0@1$6^a@1$6^9>0@3$0$1@1$9^b@1$9^a>0@3$0$1@1$a^c@1$a^b>0@3$0$1@1$8^d@1$8^c>0@1$h1^d@1$h1^f").
Proof.
  intros a b. destruct a, b; cbn. intros -> -> -> -> -> -> -> -> -> -> -> -> W.
  destruct W as (H1 & Hrest). split.
  - intros c Hc. destruct (H1 c Hc) as [RO CO]. split.
    + destruct RO; constructor; assumption.
    + destruct CO; constructor; assumption.
  - exact Hrest.
Qed.

Lemma WF_sbs : ltac2:(zQ "30!hi3!hn2!ih2>1a$0>1b$0>0@2$2^2^1>0@1$1^2@1$1^4").
Proof.
  intros a b S W. unfold same_but_shadow in S.
  ndestruct S as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & E15 & E16).
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
Definition keys_ok : ltac2:(zQ "20!hnf!hs9>2mp@1$1$0P") := ltac2:(zQ "b0!hnf!h4!ii5!ij3!ija!ik1!ika!ikf!il6!hs9!in6\2mp@1$9$0>1k$3>1x$0>0@3$1@1$5$0@3$8$0^2^3@2$4$0^1@2$6@3$1$3^3@1$7@1$2^2@2$aZ@1$2^2").

Lemma WF_keys : ltac2:(zQ "40!r2!hi3!ira!hn2>2st$1>0@1$3^1@1$2@1$0^2").
Proof. intros st W. ndestruct W as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & K). exact K. Qed.

Lemma chunk_list_nodup : ltac2:(zQ "60!r2!hi3!hnf!is5!ira!iu5>2st$1>0@1$4@1$0^1@2$5$2@1$3^2").
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

Lemma chunk_list_find : ltac2:(zQ "d0!hnf!r2!ija!ik1!h4!iue!hi3!ii5!is5!ikf!ira!il6!iv3>2st$6>1x$0>0@1$a@1$1^2@2$5@3$c$0^2@1$8^3@3$4@1$3$0@3$b$0@1$9@1$7^2@1$1^3@2$2$0^2").
Proof.
  intros st x K. rewrite chunk_list_in_iff. split.
  - intros [k F]. destruct (K _ _ F) as [-> _]. exact F.
  - intros F. exists (ckey (ch_user_beg x)). exact F.
Qed.

Lemma keys_ok_upd : ltac2:(zQ "70!r2!ira!hi3!ii5!hnf!iv9!in6>2st$2>2ch$4>0@1$1@1$0^2>0@2$6Z@1$3^2@1$1@1$0@2$5^4^3").
Proof.
  intros st ch K POS k x F. unfold upd_chunk, set_chunks in F. cbn [as_chunks] in F. rewrite gadd_find in F.
  destruct (PositiveMap.E.eq_dec _ _) as [E|NE]; [| exact (K _ _ F)]. inversion F; subst. split; [reflexivity| exact POS].
Qed.

Lemma chunk_list_upd_perm : ltac2:(zQ "f0!hnf!r2!ii5!is5!jg5!jgc!ik1!h4!hi3!ikf!iv9!ira!il6!jif!in6>2st$8>2ch$0>0@1$b@1$1^2>0@2$eZ@1$2^2>0@3$7@1$6$0@3$c$0@1$9@1$2^3@1$1^4@1$4$0@3$d$0@1$3@2$a^5^4@3$5$0^4@1$3^5").
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
Lemma compute_req_facts : ltac2:(zQ "h10!ika!j1!jje!jkb!h4!jl3!jld!jm3!jma!hn8!jn1!jnf!jo5!jp1!jpe!in6!jq6>1n$1>0@2$6Z^1=1r$b@1$a^2@2$0@3$4$1@1$5^1@2$8^3+1@2$0@2$0@2$6+h0@1$3^1@2$6@1$3^1+og0@2$0@2$0@2$6@2$8^3+8@1$2^1@2$f@1$2^1@2$7@2$8^3+8+8@2$0@3$4$1@2$h0@1$2^1+8Z@2$0@3$4$1@1$c^1@2$7@2$7@1$2^1@1$3^1M9\0$9$1@1$d^1Z@1$3^1@3$4$b@1$a@1$5^1@6$e@1$5^1@1$5^1@1$3^1@1$2^1@1$c^1@1$d^1").
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
Lemma flat_map_perm_remove : ltac2:(zQ "a0!j1!kd!h4!jr0!jgc!iv3!jr6!js2!iu5!jif>1g>0$0@1$1$0>2g'>0$0@1$1$0>1l@1$1$0>1c$0>2AB$0>1F@1$1$0>1M@1$1$0>0@2$8$0^5>0@3$5$0^5^6>0>1x$0>0@3$5$0^1^8>0@1$7@3$2$0^2^8@3$2@1$1$0@1^b^3@1^c^3>0@3$2@1$1$0@1^a^7@3$3$0^5@3$4$0^6^4>0@3$2@1$1$0@1^a^8@3$3$0^6^5@3$9$0@3$4$0^8@4$6$0$0^b^a@4$6$0$0^c^a").
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

Lemma classes_nodup : ltac2:(zQ "60!j1!js7!ju4!jub!iu5!jv2@2$4$0@4$2$1$0$5@2$3N0Ni0").
Proof. apply NoDup_map_NoDup_ForallPairs; [intros x y _ _; lia| apply seq_NoDup]. Qed.
Lemma classes_in : ltac2:(zQ "90!j1!js7!ika!ju4!jub!iv3!jld!in6!jv2>1c$0>0@2$2@2$6Z^1@2$7^1+i0@3$5$0^2@4$3$1$0$8@2$4N0Ni0").
Proof. intros c Hc. apply in_map_iff. exists (Z.to_nat c). split; [lia|]. apply in_seq. lia. Qed.

(* [comment removed for export] *)
Lemma NoDup_app_disjoint' : ltac2:(zQ "60!j1!kd!iv3!jr0!jvc!iu5>2l1@1$1$0>2l2@1$1$0>1x$0>0@2$5$0@3$3$0^3^2>0@3$2$0^2^4>0@3$2$0^3^4$4").
Proof.
  induction l1 as [|y l1 IH]; intros l2 x ND H1 H2; [destruct H1|].
  inversion ND; subst. destruct H1 as [->|H1].
  - apply H3. apply in_app_iff. right. exact H2.
  - eapply IH; eauto.
Qed.

Lemma cache_vs_inuse : ltac2:(zQ "h30!j1!h4!hnf!iv3!hn8!kg3!ika!js2!hi3!kga!kh9!is5!ki6!kj8!kk1!kkf!hn2!jld!in6>2st$8>1c$0>2cp$0>1x$2>0@1$h0^4>0@2$6@2$h1Z^4@2$h2^4$e>0@3$3$0^4@1$f@2$d^6^5>0@3$3$2^4@1$b^7>0@3$1$4@1$a^5$5@1$7@3$1$0@1$9^6@3$c^9^8^7").
Proof.
  intros st c cp x W Hc Hcp Hx Hp E. ndestruct W as (_ & ND & _). unfold carved_addr_list in ND.
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
  Hypothesis W : ltac2:(zQ "10!hn2@1$0?2st").
  Hypothesis Hn : ltac2:(zQ "10!jld@2$0Z?1n").
  Hypothesis HC : ltac2:(zQ "30!in6!ika!kk1@2$1@2$0Z?1c@2$0?1c$2").
  Hypothesis CID : c = class_id (rq_needed r).
  Hypothesis PRIM : rq_primary r = true.
  Hypothesis FIT : rq_needed r <= class_size c.
  Hypothesis PCS : ltac2:(zQ "60!j1!jgc!kd!h4!kj8!kkf@3$3@1$2$0@1$5@2$4?2st?1c@3$1$0?2cp?4rest").
  Hypothesis SB0 : ltac2:(zQ "20!hgc!jld@2$1Z@1$0?2st").

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
    pose proof (WF_chunk st x W Hx) as OKx. unfold chunk_ok in OKx. ndestruct OKx as (U1 & U2 & U3 & U4 & REST).
    pose proof (rz_size_facts (ch_used x)) as (RZx & _). change (rz_size (ch_used x)) with (rq_rz (compute_req (ch_used x))) in RZx.
    rewrite <- U3 in RZx.
    npose (compute_req_facts (ch_used x) ltac:(lia)) as (_ & _ & X3 & _ & X5 & _). rewrite <- U3 in X5.
    pose proof RQ as RQ2. rewrite PRIM in RQ2.
    unfold kFreeArrayOffset in RNG. unfold kNumClasses in HC. subst U.
    destruct (ch_primary x) eqn:PX.
    - ndestruct REST as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8). rewrite P1 in X5.
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
    - ndestruct REST as (P1 & P2 & _). unfold in_primary in P2. apply andb_false_iff in P2. unfold kSpaceSize in P2.
      destruct P2 as [P2|P2]; [apply Z.leb_gt in P2| apply Z.ltb_ge in P2]; nia.
  Qed.

  Let LENC : length (as_cache st) = 32%nat.
  Proof. ndestruct W as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & L & _). exact L. Qed.
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
    intros b q Hb Hq. pose proof (WF_batch st b W Hb) as BO. ndestruct BO as (_ & _ & _ & _ & _ & _ & _ & _ & B9).
    destruct (B9 q Hq) as [x [Fx _]]. unfold find_chunk in *. destruct (q + kChunkHeaderSize <=? 0) eqn:LE; [reflexivity|].
    unfold st', hit_state, upd_chunk, set_chunks, set_pc. cbn [as_chunks ch_user_beg]. rewrite gadd_find.
    destruct (PositiveMap.E.eq_dec _ _) as [E|NE]; [exfalso| reflexivity].
    apply Z.leb_gt in LE. unfold ckey in E. apply Z2Pos.inj in E; [| exact UPOS| exact LE].
    rewrite <- E in Fx. cbn [ch_user_beg ch] in Fx. rewrite hit_fresh in Fx. discriminate.
  Qed.
  Lemma fold_used_ext : ltac2:(zQ "60!j1!h4!klb!jm3!kd!iv3>1F>0$0$0>2F'>0$0$0>1l@1$4$0>0>1q$0>0@3$5$0^1^2@3$1$0@1^5^2@1^4^2@3$1$0@5$2$0$0\1q$0\3acc$0@2$3@1^6^2^1Z^2@5$2$0$0\1q$0\3acc$0@2$3@1^5^2^1Z^2").
  Proof. induction l as [|y l IH]; intros H; [reflexivity|]. cbn. rewrite H by (left; reflexivity). rewrite IH; [reflexivity|]. intros q Hq. apply H. right. exact Hq. Qed.
  Let QOK : forall q, (forall b, In b (qc_list q) -> In b (qc_list (as_tq st) ++ qc_list (as_gq st))) -> qcache_ok st q -> qcache_ok st' q.
  Proof.
    intros q SUB [Q1 Q2]. split; [| exact Q2]. intros b Hb. pose proof (Q1 b Hb) as BO.
    ndestruct BO as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9). unfold batch_ok.
    refine (conj B1 (conj B2 (conj B3 (conj B4 (conj B5 (conj B6 (conj B7 (conj _ _)))))))).
    - rewrite B8. f_equal. apply fold_used_ext. intros q0 Hq0. rewrite (FCB b q0); [reflexivity| apply SUB; exact Hb| exact Hq0].
    - intros q0 Hq0. rewrite (FCB b q0); [| apply SUB; exact Hb| exact Hq0]. apply B9. exact Hq0.
  Qed.

  Theorem WF_hit : WF st'.
  Proof.
    pose proof W as WW.
    ndestruct WW as (Wrc & Wnd & Wch & Winj & Wsec & Wsnd & Wres1 & Wres2 & Wtq & Wgq & Wtqb & Wgqb & Wndb & Wq & Wm0 & Wm31 & Wpc0 & Wpc31 & WlenR & WlenC & Wqmax & Wqmin & Wqc & Wkeys).
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
      ndestruct RQ as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6).
      unfold chunk_ok. cbn [ch_used ch_rz ch_user_beg ch_alloc_beg ch_class ch]. rewrite Q6. cbn [rq_size rq_rz rq_needed rq_primary].
      rewrite PRIMch. refine (conj _ (conj eq_refl (conj eq_refl (conj eq_refl _)))); [lia|].
      ndestruct CV as (_ & _ & V3 & V4 & V5).
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
