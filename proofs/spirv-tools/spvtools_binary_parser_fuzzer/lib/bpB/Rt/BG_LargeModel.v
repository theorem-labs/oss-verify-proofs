(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)

From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BW_0Gc.
From Stdlib Require Import ZArith List Lia Bool Permutation.
From Stdlib Require Import FMapPositive.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BothAllocModel.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BllocWf BllocKit BG_MallocModel BG_WFHit.
Import ListNotations.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Section Req.
  Variable n : Z.
  Hypothesis SZ : 64512 < n < 2^32.
  Let r := compute_req n.

  Lemma rz_log_large : rz_log n = 7.
  Proof. unfold rz_log. repeat match goal with |- context [?a <=? ?b] => first [rewrite (proj2 (Z.leb_gt a b)) by lia] end. reflexivity. Qed.

  Lemma rz_size_large : rz_size n = 2048.
  Proof. unfold rz_size. rewrite rz_log_large. reflexivity. Qed.

  Lemma large_req : rq_size r = n /\ rq_rz r = 2048 /\ rq_rounded r = round_up n 8 /\ rq_needed r = round_up (Z.max n 8) 8 + 4096
                    /\ rq_primary r = false /\ rq_n r = n /\ size_too_big r = false /\ kMaxSize < rq_needed r.
  Proof.
    subst r. unfold compute_req. rewrite rz_size_large.
    replace (n =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
    replace (round_up (Z.max n 8) 8 + 2048 <=? kMaxSize) with false by (symmetry; apply Z.leb_gt; unfold kMaxSize, round_up; Z.div_mod_to_equations; lia).
    cbn [rq_size rq_rz rq_rounded rq_needed rq_primary rq_n]. unfold size_too_big. cbn [rq_n rq_needed rq_size].
    unfold kMaxAllowedMalloc, kMaxSize, round_up. replace (Z.max n 8) with n by lia.
    repeat split; try reflexivity; try lia.
    - rewrite !orb_false_iff. repeat split; apply Z.ltb_ge; Z.div_mod_to_equations; lia.
    - Z.div_mod_to_equations; lia.
  Qed.
End Req.

Lemma nearest_le_snoc : forall l x m best,
  sc_map_beg x <= m ->
  (forall h, In h l -> sc_map_beg h <= m -> sc_map_beg h < sc_map_beg x) ->
  (best = None \/ exists b, best = Some b /\ sc_map_beg b < sc_map_beg x) ->
  nearest_le (l ++ [x]) m best = Some x.
Proof.
  induction l as [|h l IH]; intros x m best Hx Hl Hb; cbn [nearest_le app].
  - replace (m <? sc_map_beg x) with false by (symmetry; apply Z.ltb_ge; lia).
    destruct Hb as [->|(b & -> & Hbx)]; [reflexivity|].
    replace (m - sc_map_beg x <? m - sc_map_beg b) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
  - destruct (Z.ltb_spec m (sc_map_beg h)) as [LT|GE].
    + apply IH; [exact Hx| intros hh HH Hm; apply Hl; [right; exact HH| exact Hm]| exact Hb].
    + assert (Hh : sc_map_beg h < sc_map_beg x) by (apply Hl; [left; reflexivity| lia]).
      destruct Hb as [->|(b & -> & Hbx)].
      * apply IH; [exact Hx| intros hh HH Hm; apply Hl; [right; exact HH| exact Hm]|]. right. exists h. split; [reflexivity| exact Hh].
      * destruct (m - sc_map_beg h <? m - sc_map_beg b) eqn:CMP;
          (apply IH; [exact Hx| intros hh HH Hm; apply Hl; [right; exact HH| exact Hm]| right; eexists; split; [reflexivity| assumption]]).
Qed.

Lemma land_lnot7 : forall x, Z.land x (Z.lnot 7) = x - x mod 8.
Proof.
  intros x. rewrite <- Z.ldiff_land. change 7 with (Z.ones 3). rewrite Z.ldiff_ones_r by lia.
  rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. change (2^3) with 8. Z.div_mod_to_equations. lia.
Qed.

Section LargeState.
  Variables (st : astate) (a n : Z).
  Let r := compute_req n.
  Let needed := rq_needed r.
  Let msz := round_up needed kPageSize + kPageSize.
  Let nch := zlen (as_sec st).
  Let committed := nch =? as_n_reserved st.

  Definition large_nres : Z := if committed then as_n_reserved st + kChunksBlockCount else as_n_reserved st.
  Definition large_maps : list mapping :=
    (if committed then [mkMap (as_ptr_array st + as_n_reserved st * 8) (kChunksBlockCount * 8) MkPtrArrayCommit PROT_RW false] else [])
    ++ mkMap a msz MkSecondary PROT_RW false :: as_maps st.
  Definition large_chunk : chunk := mkChunk (a + kPageSize) (a + kPageSize + 2048) n 2048 0 CAllocated.
  Definition large_base : astate :=
    mkState (as_space_beg st) (as_ptr_array st) (as_regions st) (as_cache_inited st) (as_cache st)
            large_nres (as_sec st ++ [mkSC a msz needed]) (as_chunks st) (as_tq st) (as_gq st) (as_internal_init st)
            large_maps (as_shadow st) (as_env st) (as_track_shadow st) (as_qmax st) (as_qmin st) (as_qcache st).
  Definition large_state : astate := upd_chunk large_base large_chunk.

  Hypothesis SZ : 64512 < n < 2^32.
  Hypothesis AL : Z.land a (kPageSize - 1) = 0.

  Hypothesis AR : (0 <= a /\ a + msz <= kLowMemEnd) \/ (kHighMemBeg <= a /\ a + msz <= kHighMemEnd).
  Hypothesis NP : in_primary st (a + kPageSize) = false.
  Hypothesis BELOW : forall h, In h (as_sec st) -> sc_map_beg h <= a + kPageSize -> sc_map_beg h < a.
  Hypothesis ROOM : zlen (as_sec st) < kMaxNumChunks.

  Let RQ := large_req n SZ.

  Lemma large_geo : n + 8 <= needed - 4088 /\ needed <= n + 4104 /\ needed + 4096 <= msz /\ msz < needed + 8192 /\ needed mod 8 = 0 /\ msz mod 4096 = 0 /\ a mod 4096 = 0.
  Proof.
    destruct RQ as (_ & _ & _ & ND & _). subst msz needed r. rewrite ND. unfold round_up, kPageSize.
    assert (A : a mod 4096 = 0).
    { unfold kPageSize in AL. change (4096 - 1) with (Z.ones 12) in AL. rewrite Z.land_ones in AL by lia. change 4096 with (2^12). exact AL. }
    repeat split; try exact A; Z.div_mod_to_equations; nia.
  Qed.

  Lemma aim : forall x, a <= x -> x <= a + msz -> addr_is_in_mem x = true.
  Proof.
    intros x H1 H3. unfold addr_is_in_mem, kHighMemBeg, kHighMemEnd, kLowMemEnd, kShadowOffset in *. apply orb_true_iff.
    destruct AR as [[A1 A2]|[A1 A2]]; [left| right]; apply andb_true_iff; split; apply Z.leb_le; lia.
  Qed.

  Lemma land7_of_mod8 : forall x, x mod 8 = 0 -> Z.land x 7 = 0.
  Proof. intros x H. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. change (2^3) with 8. exact H. Qed.

  Lemma am_malloc_large : exists st' ev, am_malloc_k st n a = Some (a + kPageSize + 2048, st', ev) /\ same_but_shadow st' large_state.
  Proof.
    destruct RQ as (RS & RZ & RR & ND & RP & RN & TB & BIG). pose proof large_geo as (G1 & G2 & G3 & G4 & G5 & G6 & G7).
    fold r in RS, RZ, RR, ND, RP, RN, TB, BIG. fold needed in ND, BIG.
    unfold am_malloc_k. replace (n <? 0) with false by (symmetry; apply Z.ltb_ge; lia). fold r. rewrite TB. fold needed.
    replace (kMaxSize <? needed) with true by (symmetry; apply Z.ltb_lt; exact BIG).

    unfold large_allocate. fold msz. replace (msz <? needed) with false by (symmetry; apply Z.ltb_ge; lia). rewrite AL. cbn [negb].
    set (st0 := add_map st _).
    assert (A8 : Z.land a 7 = 0) by (apply land7_of_mod8; Z.div_mod_to_equations; lia).
    replace (round_up (a + kPageSize) 8 - a) with 4096 by (unfold round_up, kPageSize; Z.div_mod_to_equations; lia).
    destruct (poison_shadow_some st0 a 4096 kAsanHeapLeftRedzoneMagic A8 ltac:(apply aim; lia) eq_refl ltac:(apply aim; lia)) as (st1 & ev1 & E1 & S1). rewrite E1.
    replace (round_down (a + kPageSize + needed) 8) with (a + 4096 + needed) by (unfold round_down, kPageSize; Z.div_mod_to_equations; lia).
    destruct (poison_shadow_some st1 (a + 4096 + needed) (a + msz - (a + 4096 + needed)) kAsanHeapLeftRedzoneMagic
                ltac:(apply land7_of_mod8; Z.div_mod_to_equations; lia) ltac:(apply aim; lia) ltac:(apply land7_of_mod8; Z.div_mod_to_equations; lia) ltac:(apply aim; lia))
      as (st2 & ev2 & E2 & S2). rewrite E2.
    replace (a + msz <? a + kPageSize + needed) with false by (symmetry; apply Z.ltb_ge; unfold kPageSize; lia).
    assert (SEC2 : as_sec st2 = as_sec st /\ as_n_reserved st2 = as_n_reserved st /\ as_ptr_array st2 = as_ptr_array st).
    { pose proof (sbs_trans _ _ _ S2 S1) as S. unfold same_but_shadow in S. subst st0. unfold add_map in S. cbn in S. intuition congruence. }
    destruct SEC2 as (SEC2 & NR2 & PA2). rewrite SEC2, NR2, PA2. fold nch.
    replace (kMaxNumChunks <=? nch) with false by (symmetry; apply Z.leb_gt; exact ROOM).

    replace (negb (0 =? 0)) with false by reflexivity.
    pose proof (sbs_trans _ _ _ S2 S1) as S20.
    assert (SB0 : as_space_beg st0 = as_space_beg st) by (subst st0; reflexivity).
    assert (SP2 : as_space_beg st2 = as_space_beg st) by (destruct S20 as (E & _); rewrite E; exact SB0).
    unfold large_state, large_base, large_maps, large_nres. fold nch. subst committed.
    destruct (nch =? as_n_reserved st) eqn:EC; unfold map_fixed; cbn beta iota zeta;
      match goal with |- context [upd_chunk ?X4 _] => set (st4 := X4) in * end.
    all: rewrite RZ, RS, RP; replace (a + kPageSize + needed <? a + kPageSize + 2048 + n) with false by (symmetry; apply Z.ltb_ge; lia); cbn [negb].
    all: assert (SP4 : as_space_beg st4 = as_space_beg st) by (subst st4; cbn; exact SP2).
    all: assert (SEC4 : as_sec st4 = as_sec st ++ [mkSC a msz needed]) by (subst st4; cbn; rewrite ?SEC2; reflexivity).
    all: set (ch := {| ch_alloc_beg := a + kPageSize; ch_user_beg := a + kPageSize + 2048; ch_used := n; ch_rz := 2048; ch_class := 0; ch_state := CAllocated |}).

    all: unfold actually_allocated_size; unfold in_primary; cbn [as_space_beg as_sec upd_chunk set_chunks]; rewrite SP4, SEC4.
    all: unfold in_primary in NP; rewrite NP.
    all: replace (Z.land (a + kPageSize) (kPageSize - 1) =? 0) with true by (symmetry; apply Z.eqb_eq; unfold kPageSize; apply land7_of_mod8 || idtac; change (4096 - 1) with (Z.ones 12); rewrite Z.land_ones by lia; change (2^12) with 4096; Z.div_mod_to_equations; lia).
    all: cbn [negb].
    all: rewrite (nearest_le_snoc (as_sec st) (mkSC a msz needed) (a + kPageSize) None ltac:(cbn [sc_map_beg]; unfold kPageSize; lia)
                                  ltac:(cbn [sc_map_beg]; exact BELOW) (or_introl eq_refl)).
    all: cbn [sc_map_beg sc_size]. all: replace (a =? a + kPageSize - kPageSize) with true by (symmetry; apply Z.eqb_eq; lia).
    all: replace (a + kPageSize + 2048 - (a + kPageSize)) with 2048 by lia.
    all: destruct (poison_shadow_some (upd_chunk st4 ch) (a + kPageSize) 2048 kAsanHeapLeftRedzoneMagic
                ltac:(apply land7_of_mod8; unfold kPageSize; Z.div_mod_to_equations; lia) ltac:(apply aim; unfold kPageSize; lia) eq_refl ltac:(apply aim; unfold kPageSize; lia))
           as (st5 & ev5 & E5 & S5); rewrite E5.
    all: set (tb := round_up (a + kPageSize + 2048 + n) 8) in *.
    all: assert (TBB : a + 6144 + n <= tb < a + 6144 + n + 8 /\ tb mod 8 = 0) by (subst tb; unfold round_up, kPageSize; Z.div_mod_to_equations; lia).
    all: replace (a + kPageSize + round_up needed kPageSize) with (a + msz) by (subst msz; unfold kPageSize; lia).
    all: destruct (poison_shadow_some st5 tb (a + msz - tb) kAsanHeapLeftRedzoneMagic
                ltac:(apply land7_of_mod8; lia) ltac:(apply aim; unfold kPageSize in *; lia) ltac:(apply land7_of_mod8; Z.div_mod_to_equations; lia) ltac:(apply aim; unfold kPageSize in *; lia))
           as (st6 & ev6 & E6 & S6); rewrite E6.

    all: rewrite (land_lnot7 n); set (rd := n - n mod 8) in *.
    all: assert (RD : 8 <= rd <= n /\ rd mod 8 = 0) by (subst rd; Z.div_mod_to_equations; lia).
    all: replace (0 <? rd) with true by (symmetry; apply Z.ltb_lt; lia).
    all: destruct (poison_shadow_some st6 (a + kPageSize + 2048) rd 0
                ltac:(apply land7_of_mod8; unfold kPageSize; Z.div_mod_to_equations; lia) ltac:(apply aim; unfold kPageSize; lia) ltac:(apply land7_of_mod8; lia) ltac:(apply aim; unfold kPageSize in *; lia))
           as (st7 & ev7 & E7 & S7); rewrite E7.

    all: rewrite (aim (a + kPageSize + 2048 + rd)) by (unfold kPageSize in *; lia); cbn [negb andb].
    all: assert (S8 : exists st8 ev8, (if negb (n =? rd) then Some (paint st7 (a + kPageSize + 2048 + rd) (a + kPageSize + 2048 + rd + 8) (Z.land n 7), [EShadow1 (a + kPageSize + 2048 + rd) (Z.land n 7)])
                                      else Some (st7, [])) = Some (st8, ev8) /\ same_but_shadow st8 st7)
      by (destruct (negb (n =? rd)); do 2 eexists; (split; [reflexivity|]); [apply sbs_paint| apply sbs_refl]).
    all: destruct S8 as (st8 & ev8 & E8 & S8); rewrite E8.
    all: replace (negb (a + kPageSize + 2048 - kChunkHeaderSize =? a + kPageSize) && (a + kPageSize + 2048 - kChunkHeaderSize <? a + kPageSize + 16)) with false
      by (symmetry; apply andb_false_iff; right; apply Z.ltb_ge; unfold kChunkHeaderSize; lia).
    all: do 2 eexists; split; [reflexivity|].

    all: eapply sbs_trans; [exact S8|]. all: eapply sbs_trans; [exact S7|]. all: eapply sbs_trans; [exact S6|]. all: eapply sbs_trans; [exact S5|].
    all: subst st4 ch; unfold upd_chunk, set_chunks, set_sec, large_chunk; cbn [as_space_beg as_ptr_array as_regions as_cache_inited as_cache as_n_reserved as_sec as_chunks as_tq as_gq as_internal_init as_maps as_shadow as_env as_track_shadow as_qmax as_qmin as_qcache].
    all: unfold same_but_shadow in S20 |- *; subst st0; unfold add_map in S20 |- *; cbn in S20 |- *.
    all: destruct S20 as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13 & Q14 & Q15 & Q16); rewrite ?Q1, ?Q2, ?Q3, ?Q4, ?Q5, ?Q6, ?Q7, ?Q8, ?Q9, ?Q10, ?Q11, ?Q12, ?Q13, ?Q14, ?Q15, ?Q16; repeat split; reflexivity.
  Qed.
End LargeState.

Lemma nth_error_app_l {A} : forall (l l' : list A) i x, nth_error l i = Some x -> nth_error (l ++ l') i = Some x.
Proof. induction l as [|y l IH]; intros l' [|i] x H; cbn in *; try discriminate; [exact H| apply IH; exact H]. Qed.

Lemma nodup_snoc {A} : forall (l : list A) x, NoDup l -> ~ In x l -> NoDup (l ++ [x]).
Proof.
  induction l as [|y l IH]; intros x ND NI; cbn.
  - constructor; [intros []| constructor].
  - inversion ND; subst. constructor.
    + intros Hin. apply in_app_iff in Hin. destruct Hin as [Hin|[Hin|[]]]; [exact (H1 Hin)|]. apply NI. left. symmetry. exact Hin.
    + apply IH; [exact H2|]. intros Hin. apply NI. right. exact Hin.
Qed.

Section WFLarge.
  Variables (st : astate) (a n : Z).
  Let r := compute_req n.
  Let needed := rq_needed r.
  Let msz := round_up needed kPageSize + kPageSize.
  Let nch := zlen (as_sec st).
  Let ch := large_chunk a n.
  Let st' := large_state st a n.
  Hypothesis W : WF st.
  Hypothesis SZ : 64512 < n < 2^32.
  Hypothesis AL : Z.land a (kPageSize - 1) = 0.
  Hypothesis APOS : 0 < a.

  Hypothesis SBX : a + msz <= as_space_beg st \/ as_space_beg st + kSpaceSize <= a.
  Hypothesis BELOW : forall h, In h (as_sec st) -> sc_map_beg h <= a + kPageSize -> sc_map_beg h < a.

  Hypothesis NSEC : nch = as_n_reserved st -> as_n_reserved st = 0.

  Let RQ := large_req n SZ.
  Let KEYS : keys_ok (as_chunks st). Proof. apply WF_keys. exact W. Qed.
  Let GEO : n + 8 <= needed - 4088 /\ needed <= n + 4104 /\ needed + 4096 <= msz /\ msz < needed + 8192 /\ needed mod 8 = 0 /\ msz mod 4096 = 0 /\ a mod 4096 = 0.
  Proof. apply (large_geo st a n SZ AL). Qed.
  Let UPOS : 0 < a + kPageSize + 2048. Proof. unfold kPageSize. lia. Qed.
  Let NPRIM : forall x, a <= x -> x < a + msz -> in_primary st x = false.
  Proof.
    intros x H1 H2. unfold in_primary. apply andb_false_iff. unfold kSpaceSize in *.
    destruct SBX as [S|S]; [left; apply Z.leb_gt; lia| right; apply Z.ltb_ge; lia].
  Qed.

  Lemma large_fresh : PositiveMap.find (ckey (a + kPageSize + 2048)) (as_chunks st) = None.
  Proof.
    destruct (PositiveMap.find (ckey (a + kPageSize + 2048)) (as_chunks st)) as [x|] eqn:F; [exfalso| reflexivity].
    destruct (KEYS _ _ F) as [K POS].
    assert (EU : ch_user_beg x = a + kPageSize + 2048) by (unfold ckey in K; apply Z2Pos.inj; [exact POS| exact UPOS| congruence]).
    assert (Hx : In x (chunk_list st)) by (apply chunk_list_in_iff; eexists; exact F).
    pose proof (WF_chunk st x W Hx) as OKx. unfold chunk_ok in OKx. destruct OKx as (U1 & U2 & U3 & U4 & REST).
    pose proof (rz_size_facts (ch_used x)) as (RZx & _). change (rz_size (ch_used x)) with (rq_rz (compute_req (ch_used x))) in RZx.
    rewrite <- U3 in RZx. pose proof GEO as (G1 & G2 & G3 & _). unfold kPageSize in *.
    destruct (ch_primary x) eqn:PX.
    - destruct REST as (_ & _ & _ & P4 & _). rewrite (NPRIM (ch_alloc_beg x)) in P4; [discriminate| lia| lia].
    - destruct REST as (_ & _ & i & h & NTH & MB & _).
      assert (Hh : In h (as_sec st)) by (eapply nth_error_In; exact NTH).
      pose proof (BELOW h Hh ltac:(lia)). lia.
  Qed.

  Let PERM : Permutation (chunk_list st') (ch :: chunk_list st).
  Proof. exact (chunk_list_upd_perm (large_base st a n) ch KEYS UPOS large_fresh). Qed.
  Let INl : forall x, In x (chunk_list st') <-> x = ch \/ In x (chunk_list st).
  Proof.
    intros x. split.
    - intros Hx. apply (Permutation_in x PERM) in Hx. destruct Hx as [E|Hx]; [left; symmetry; exact E| right; exact Hx].
    - intros Hx. apply (Permutation_in x (Permutation_sym PERM)). destruct Hx as [->|Hx]; [left; reflexivity| right; exact Hx].
  Qed.
  Let PRIMch : ch_primary ch = false. Proof. reflexivity. Qed.
  Let FCB : forall b q, In b (qc_list (as_tq st) ++ qc_list (as_gq st)) -> In q (qb_chunks b) ->
    find_chunk (as_chunks st') (q + kChunkHeaderSize) = find_chunk (as_chunks st) (q + kChunkHeaderSize).
  Proof.
    intros b q Hb Hq. pose proof (WF_batch st b W Hb) as BO. destruct BO as (_ & _ & _ & _ & _ & _ & _ & _ & B9).
    destruct (B9 q Hq) as [x [Fx _]]. unfold find_chunk in *. destruct (q + kChunkHeaderSize <=? 0) eqn:LE; [reflexivity|].
    unfold st', large_state, upd_chunk, set_chunks, large_base. cbn [as_chunks ch_user_beg large_chunk]. rewrite gadd_find.
    destruct (PositiveMap.E.eq_dec _ _) as [E|NE]; [exfalso| reflexivity].
    apply Z.leb_gt in LE. unfold ckey in E. apply Z2Pos.inj in E; [| exact UPOS| exact LE].
    rewrite <- E in Fx. rewrite large_fresh in Fx. discriminate.
  Qed.
  Let QOK : forall q, (forall b, In b (qc_list q) -> In b (qc_list (as_tq st) ++ qc_list (as_gq st))) -> qcache_ok st q -> qcache_ok st' q.
  Proof.
    intros q SUB [Q1 Q2]. split; [| exact Q2]. intros b Hb. pose proof (Q1 b Hb) as BO.
    destruct BO as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9). unfold batch_ok.
    refine (conj B1 (conj B2 (conj B3 (conj B4 (conj B5 (conj B6 (conj B7 (conj _ _)))))))).
    - rewrite B8. f_equal. apply fold_used_ext. intros q0 Hq0. rewrite (FCB b q0); [reflexivity| apply SUB; exact Hb| exact Hq0].
    - intros q0 Hq0. rewrite (FCB b q0); [| apply SUB; exact Hb| exact Hq0]. apply B9. exact Hq0.
  Qed.

  Lemma lg_chunks : forall x, In x (chunk_list st') <-> x = ch \/ In x (chunk_list st). Proof. exact INl. Qed.

  Theorem WF_large : WF st'.
  Proof.
    pose proof W as WW.
    destruct WW as (Wrc & Wnd & Wch & Winj & Wsec & Wsnd & Wres1 & Wres2 & Wtq & Wgq & Wtqb & Wgqb & Wndb & Wq & Wm0 & Wm31 & Wpc0 & Wpc31 & WlenR & WlenC & Wqmax & Wqmin & Wqc & Wkeys).
    destruct RQ as (RS & RZ & RR & ND & RP & RN & TB & BIG). pose proof GEO as (G1 & G2 & G3 & G4 & G5 & G6 & G7).
    unfold WF.
    split. { intros c0 Hc0. destruct (Wrc c0 Hc0) as [R0 C0]. split; [destruct R0; constructor; assumption| destruct C0; constructor; assumption]. }
    split. {
      apply (Permutation_NoDup (l := carved_addr_list st)); [| exact Wnd]. unfold carved_addr_list.
      apply Permutation_app; [apply Permutation_refl|]. apply Permutation_app; [| apply Permutation_refl].
      apply Permutation_map. apply Permutation_sym.
      change (filter ch_primary (chunk_list st)) with (filter ch_primary (ch :: chunk_list st)). apply Permutation_filter. exact PERM. }
    split. { intros x Hx. apply INl in Hx as [->|Hx].
      - unfold chunk_ok. cbn [ch_used ch_rz ch_user_beg ch_alloc_beg ch_class ch_state ch large_chunk]. fold r.
        rewrite PRIMch. change (in_primary st' (a + kPageSize)) with (in_primary st (a + kPageSize)). change (as_sec st') with (as_sec st ++ [mkSC a msz needed]).
        refine (conj _ (conj (eq_sym RS) (conj (eq_sym RZ) (conj eq_refl (conj RP (conj _ _)))))); [lia| apply NPRIM; unfold kPageSize; lia|].
        exists (Z.to_nat nch), (mkSC a msz needed). split; [| cbn [sc_map_beg sc_size sc_map_size]; repeat split; unfold kPageSize; try lia; reflexivity].
        rewrite nth_error_app2 by (unfold nch, zlen; lia).
        replace (Z.to_nat nch - length (as_sec st))%nat with 0%nat by (unfold nch, zlen; lia). reflexivity.
      - pose proof (Wch x Hx) as OK. unfold chunk_ok in OK |- *. destruct OK as (O1 & O2 & O3 & O4 & REST).
        refine (conj O1 (conj O2 (conj O3 (conj O4 _)))). destruct (ch_primary x); [exact REST|].
        destruct REST as (P1 & P2 & i & h & NTH & P3 & P4). refine (conj P1 (conj P2 _)). exists i, h. split; [| exact (conj P3 P4)].
        change (as_sec st') with (as_sec st ++ [mkSC a msz needed]). apply nth_error_app_l. exact NTH. }
    split. { intros x y Hx Hy E. apply INl in Hx as [->|Hx]; apply INl in Hy as [->|Hy]; [reflexivity| exfalso| exfalso| exact (Winj x y Hx Hy E)].
      - apply (chunk_list_find st y KEYS) in Hy. cbn [ch_user_beg ch large_chunk] in E. rewrite <- E in Hy. rewrite large_fresh in Hy. discriminate.
      - apply (chunk_list_find st x KEYS) in Hx. cbn [ch_user_beg ch large_chunk] in E. rewrite E in Hx. rewrite large_fresh in Hx. discriminate. }
    split. { unfold zlen in *. rewrite (Permutation_length (Permutation_filter _ _ _ PERM)). cbn [filter ch_primary ch_class ch large_chunk negb Z.eqb].
      change (as_sec st') with (as_sec st ++ [mkSC a msz needed]). rewrite length_app. cbn [length]. lia. }
    split. { change (as_sec st') with (as_sec st ++ [mkSC a msz needed]). rewrite map_app. cbn [map sc_map_beg]. apply nodup_snoc; [exact Wsnd|].
      intros Hin. apply in_map_iff in Hin. destruct Hin as (h & E & Hh). pose proof (BELOW h Hh ltac:(unfold kPageSize; lia)). lia. }
    assert (ZL : zlen (as_sec st') = nch + 1) by (change (as_sec st') with (as_sec st ++ [mkSC a msz needed]); unfold nch, zlen; rewrite length_app; cbn [length]; lia).
    split. { rewrite ZL. change (as_n_reserved st') with (large_nres st). unfold large_nres. fold nch.
      destruct (Z.eqb_spec nch (as_n_reserved st)) as [E|NE]; unfold kChunksBlockCount; [pose proof (NSEC E); lia| unfold nch in NE |- *; lia]. }
    split. { change (as_n_reserved st') with (large_nres st). unfold large_nres. fold nch.
      destruct (Z.eqb_spec nch (as_n_reserved st)) as [E|NE]; [pose proof (NSEC E); right; unfold kChunksBlockCount; lia| exact Wres2]. }
    split. { apply QOK; [| exact Wtq]. intros b Hb. apply in_app_iff. left. exact Hb. }
    split. { apply QOK; [| exact Wgq]. intros b Hb. apply in_app_iff. right. exact Hb. }
    split. { exact Wtqb. } split. { exact Wgqb. } split. { exact Wndb. }
    split. { intros x Hx Q. apply INl in Hx as [->|Hx]; [cbn in Q; discriminate| exact (Wq x Hx Q)]. }
    split. { exact Wm0. } split. { exact Wm31. } split. { exact Wpc0. } split. { exact Wpc31. }
    split. { exact WlenR. } split. { exact WlenC. }
    split. { exact Wqmax. } split. { exact Wqmin. } split. { exact Wqc. }
    exact (keys_ok_upd (large_base st a n) ch KEYS UPOS).
  Qed.
End WFLarge.
