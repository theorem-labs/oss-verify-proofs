(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BW_0Gc.
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FMapPositive Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BImage BZBridge BSysStep BSFModel BExec BellsX BArr BacX BLFrame.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BPrelim.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BothAllocModel BReach BazyRestrict BazyLedger BazySR BazyNodes BothAllocCons.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsDriverLaws BsSR BsChain BsUnwind BakeStackRep BllocWf BllocKit BllocBudget BllocRep BllocRepFacts BllocRepX BecLazy BecGap BsDepotInv BsDepotHash BG_WFHit BG_MallocModel BG_Frame BG_WriteSet BW_MallocBase BG_Malloc2 BG_MallocCold BG_MallocLarge3 BG_MallocAll BS_InstDefs BS_InstChain BS_InstLaws2 BsWalk BidBits RtB_Iface.
Import ListNotations.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac lia ::=
  first [ zify_prune; zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
        | zify_prune; Zify.zify; xlia zchecker
        | Zify.zify; xlia zchecker ].

Section Heap.
  Context {HCEIL : HeapCeil}.

  Lemma filter_allocb_is_alloc : forall l, List.filter allocb l = List.filter is_alloc l.
  Proof. intros l. induction l as [|x l IH]; [reflexivity|]. cbn. unfold allocb, is_alloc. rewrite IH. reflexivity. Qed.

  Lemma alb_NoDup : forall s, WF (a_st s) -> List.NoDup (alb s).
  Proof.
    intros s W. unfold alb. pose proof W as (_ & _ & _ & INJ & _).
    apply NoDup_map_NoDup_ForallPairs.
    - intros x y Hx Hy E. apply filter_In in Hx as [Hx _]. apply filter_In in Hy as [Hy _]. apply (INJ x y Hx Hy). congruence.
    - apply NoDup_filter. apply chunk_list_nodup. exact (WF_keys _ W).
  Qed.

  Lemma nalloc_le_blocks : forall s LB m, ARHEAP s LB m -> nalloc (a_st s) <= zlen LB.
  Proof.
    intros s LB m (R & ND & IFF). pose proof (proj2 (proj1 R)) as W.
    unfold nalloc. rewrite filter_allocb_is_alloc.
    replace (zlen (List.filter is_alloc (chunk_list (a_st s)))) with (zlen (alb s)) by (unfold alb, zlen; rewrite length_map; reflexivity).
    unfold zlen. apply Nat2Z.inj_le. apply (NoDup_incl_length (alb_NoDup s W)). intros b Hb. apply (proj2 (IFF b)). exact Hb.
  Qed.

  Fixpoint psmall (l : list (Z * Z)) : Z := match l with [] => 0 | b :: l' => nsmall (snd b) + psmall l' end.
  Fixpoint plarge (l : list (Z * Z)) : Z := match l with [] => 0 | b :: l' => nlg (snd b) + plarge l' end.
  Lemma psmall_perm : forall l1 l2, Permutation l1 l2 -> psmall l1 = psmall l2.
  Proof. intros l1 l2 P. induction P; cbn [psmall] in *; lia. Qed.
  Lemma plarge_perm : forall l1 l2, Permutation l1 l2 -> plarge l1 = plarge l2.
  Proof. intros l1 l2 P. induction P; cbn [plarge] in *; lia. Qed.
  Lemma lb_small_lbp : forall LB, lb_small LB = psmall (lbp LB).
  Proof. induction LB as [|b LB IH]; [reflexivity|]. unfold lbp in *. cbn [map psmall snd]. rewrite lb_small_cons, IH. reflexivity. Qed.
  Lemma nlarge_lbp : forall LB, nlarge LB = plarge (lbp LB).
  Proof. induction LB as [|b LB IH]; [reflexivity|]. unfold lbp in *. cbn [map plarge snd]. rewrite nlarge_cons, IH. reflexivity. Qed.

  Lemma prim_iff_small : forall u, 1 <= u -> (rq_primary (compute_req u) = true <-> u <= 64512).
  Proof.
    intros u Hu. pose proof (req_shape u Hu) as (_ & _ & _ & PRI & _). rewrite PRI, <- (mprimary_iff u Hu).
    unfold mprimary, mneeded. rewrite Z.leb_le. tauto.
  Qed.

  Lemma allocb_is_alloc : forall ch, allocb ch = is_alloc ch.
  Proof. intros ch. unfold allocb, is_alloc. destruct (ch_state ch); reflexivity. Qed.

  Lemma sum_used_prim : forall (l : list chunk),
    (forall ch, In ch l -> 1 <= ch_used ch /\ (ch_primary ch = true <-> ch_used ch <= 64512)) ->
    fold_right Z.add 0 (map ch_used (List.filter prim_allocb l)) = psmall (map (fun ch => (ch_user_beg ch, ch_used ch)) (List.filter is_alloc l)).
  Proof.
    induction l as [|x l IH]; intros H; [reflexivity|]. cbn [List.filter].
    destruct (H x (or_introl eq_refl)) as [U1 PE]. assert (IH' := IH (fun ch I => H ch (or_intror I))).
    unfold prim_allocb at 1. rewrite allocb_is_alloc.
    destruct (is_alloc x); [| rewrite andb_false_r; exact IH'].
    cbn [map psmall snd]. rewrite <- IH'. unfold nsmall.
    destruct (ch_primary x) eqn:P; cbn [andb].
    - pose proof (proj1 PE eq_refl) as SM. rewrite (proj2 (Z.leb_le _ _) SM). cbn [map fold_right]. lia.
    - assert (G : 64512 < ch_used x) by (destruct (Z.le_gt_cases (ch_used x) 64512) as [L|G]; [apply PE in L; discriminate L| exact G]).
      rewrite (proj2 (Z.leb_gt _ _) G). lia.
  Qed.

  Lemma count_sec : forall (l : list chunk),
    (forall ch, In ch l -> 1 <= ch_used ch /\ (ch_primary ch = true <-> ch_used ch <= 64512)) ->
    zlen (List.filter (fun ch => negb (ch_primary ch) && allocb ch) l) = plarge (map (fun ch => (ch_user_beg ch, ch_used ch)) (List.filter is_alloc l)).
  Proof.
    induction l as [|x l IH]; intros H; [reflexivity|]. cbn [List.filter].
    destruct (H x (or_introl eq_refl)) as [U1 PE]. assert (IH' := IH (fun ch I => H ch (or_intror I))).
    rewrite allocb_is_alloc.
    destruct (is_alloc x); [| rewrite andb_false_r; exact IH'].
    cbn [map plarge snd]. rewrite <- IH'. unfold nlg.
    destruct (ch_primary x) eqn:P; cbn [andb negb].
    - pose proof (proj1 PE eq_refl) as SM. rewrite (proj2 (Z.ltb_ge _ _) SM). lia.
    - assert (G : 64512 < ch_used x) by (destruct (Z.le_gt_cases (ch_used x) 64512) as [L|G]; [apply PE in L; discriminate L| exact G]).
      rewrite (proj2 (Z.ltb_lt _ _) G). rewrite zlen_cons. lia.
  Qed.

  Lemma chunks_prim_facts : forall s, WF (a_st s) ->
    forall ch, In ch (chunk_list (a_st s)) -> 1 <= ch_used ch /\ (ch_primary ch = true <-> ch_used ch <= 64512).
  Proof.
    intros s W ch Hin. pose proof (WF_chunk _ ch W Hin) as CO. unfold chunk_ok in CO. cbv zeta in CO.
    destruct CO as (U1 & _ & _ & _ & REST). split; [exact U1|]. rewrite <- (prim_iff_small (ch_used ch) U1).
    destruct (ch_primary ch); destruct REST as (PR & _); rewrite PR; tauto.
  Qed.

  Lemma aused_eq_small : forall s LB m, ARHEAP s LB m -> aused (a_st s) = psmall LB.
  Proof.
    intros s LB m (R & ND & IFF). pose proof (proj2 (proj1 R)) as W. unfold aused.
    rewrite (sum_used_prim _ (chunks_prim_facts s W)).
    change (map (fun ch => (ch_user_beg ch, ch_used ch)) (List.filter is_alloc (chunk_list (a_st s)))) with (alb s).
    apply psmall_perm. apply Permutation_sym. apply NoDup_Permutation; [exact ND| exact (alb_NoDup s W)| exact IFF].
  Qed.
  Lemma nsec_eq_large : forall s LB m, ARHEAP s LB m -> nalloc_sec (a_st s) = plarge LB.
  Proof.
    intros s LB m (R & ND & IFF). pose proof (proj2 (proj1 R)) as W. unfold nalloc_sec.
    rewrite (count_sec _ (chunks_prim_facts s W)).
    change (map (fun ch => (ch_user_beg ch, ch_used ch)) (List.filter is_alloc (chunk_list (a_st s)))) with (alb s).
    apply plarge_perm. apply Permutation_sym. apply NoDup_Permutation; [exact ND| exact (alb_NoDup s W)| exact IFF].
  Qed.

  Lemma no_live_at_new : forall s s' LB m m' (U n : Z) st'',
    ARHEAP s LB m -> ARHEAP s' ((U, n) :: LB) m' ->
    same_but_shadow st'' (a_st s') ->
    (exists chn, PositiveMap.find (ckey U) (as_chunks st'') = Some chn /\ ch_user_beg chn = U /\ ch_used chn = rq_size (compute_req n)) ->
    1 <= n ->
    forall x, In x (chunk_list (a_st s)) -> ch_state x = CAllocated -> ch_user_beg x <> U.
  Proof.
    intros s s' LB m m' U n st'' (R & ND & IFF) (R' & ND' & IFF') SBS FIND Hn x Hx ST E.
    assert (FN : exists chn, PositiveMap.find (ckey U) (as_chunks (a_st s')) = Some chn /\ ch_user_beg chn = U /\ ch_used chn = rq_size (compute_req n)).
    { destruct SBS as (_ & _ & _ & _ & _ & _ & _ & CH & _). rewrite <- CH. exact FIND. }
    destruct FN as (chn & F & UB & USED).

    assert (OLD : In (U, ch_used x) LB).
    { apply (proj2 (IFF _)). unfold alb. apply in_map_iff. exists x. rewrite E. split; [reflexivity|]. apply filter_In. split; [exact Hx|]. unfold is_alloc. rewrite ST. reflexivity. }

    assert (NEW : In (U, ch_used x) (alb s')) by (apply (proj1 (IFF' _)); right; exact OLD).
    unfold alb in NEW. apply in_map_iff in NEW. destruct NEW as (y & Ey & Hy). apply filter_In in Hy as [Hy _].
    pose proof (WF_keys _ (proj2 (proj1 R'))) as K'. pose proof (proj1 (chunk_list_find (a_st s') y K') Hy) as Fy.
    pose proof (f_equal fst Ey) as EU. pose proof (f_equal snd Ey) as EUSED. cbn [fst snd] in EU, EUSED.
    rewrite EU in Fy. rewrite F in Fy. injection Fy as Eyc. subst y. rewrite USED in EUSED.
    pose proof (compute_req_facts n ltac:(lia)) as (SZ & _). cbv zeta in SZ. rewrite SZ in EUSED.
    replace (Z.max n 1) with n in EUSED by lia.
    apply NoDup_cons_iff in ND' as [NI _]. apply NI. first [rewrite <- EUSED | rewrite EUSED]. exact OLD.
  Qed.

  Lemma idseq_succ : forall k, 0 <= k -> idseq (k + 1) = idseq k ++ [k + 1].
  Proof.
    intros k Hk. unfold idseq. rewrite Z2Nat.inj_add, Nat.add_1_r, seq_S, map_app by lia. cbn [map].
    replace (Z.of_nat (1 + Z.to_nat k)) with (k + 1) by lia. reflexivity.
  Qed.

  Lemma d_K_insert : forall d h n, 0 <= d_ids d -> d_K (d_insert d h n) = d_K d ++ [h].
  Proof.
    intros d h n Hi. unfold d_K. cbn [d_ids d_hash d_insert]. rewrite (idseq_succ _ Hi), map_app. cbn [map]. rewrite Z.eqb_refl. f_equal.
    apply map_ext_in. intros id Hid. apply in_idseq in Hid. destruct (Z.eqb_spec id (d_ids d + 1)); [lia| reflexivity].
  Qed.

  Lemma d_put_blocks : forall d h n, d_nb (d_put d h n) = d_nb d /\ d_sb (d_put d h n) = d_sb d.
  Proof. intros d h n. unfold d_put. destruct (d_find d h =? 0); split; reflexivity. Qed.

  Lemma malloc_stub_evt : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
                                 (F : bvmap 5 word) (fc : bv 32) (m : mem),
    mem_inv asegs m ->
    evt asegs (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 AMALLOC_ICPT) fc None m (seg_rom asegs))
              (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 AMALLOC_STUB) fc None m (seg_rom asegs)).
  Proof. intros until m. intros MI. unfold AMALLOC_STUB, AMALLOC_ICPT. step. apply evt_done. reflexivity. Qed.

  Lemma lg_cost_le_4n : forall n, 64512 < n -> lg_cost (msz_of n) <= 4 * n.
  Proof.
    intros n Hn. unfold lg_cost, msz_of. pose proof (req_shape n ltac:(lia)) as (_ & _ & ND & _ & RU).
    pose proof (rz_size_facts n) as (RZ & _). rewrite ND. unfold round_up, kPageSize in *.
    set (rz := rz_size n) in *. set (b := if rq_primary (compute_req n) then 0 else rz) in *.
    assert (Hb : 0 <= b <= 2048) by (subst b; destruct (rq_primary _); lia).
    clearbody b rz. Z.div_mod_to_equations. lia.
  Qed.

  Lemma msz_of_bound : forall n, 1 <= n <= 2 ^ 28 -> 4096 < msz_of n <= 2 ^ 28 + 12294.
  Proof.
    intros n Hn. unfold msz_of. pose proof (req_shape n ltac:(lia)) as (_ & _ & ND & _ & RU).
    pose proof (rz_size_facts n) as (RZ & _). rewrite ND. unfold round_up, kPageSize in *.
    set (rz := rz_size n) in *. set (b := if rq_primary (compute_req n) then 0 else rz) in *.
    assert (Hb : 0 <= b <= 2048) by (subst b; destruct (rq_primary _); lia).
    clearbody b rz. Z.div_mod_to_equations. lia.
  Qed.

  Lemma zsum_le_const : forall (l : list Z) (K : Z), (forall x, In x l -> x <= K) -> BecGap.zsum l <= K * zlen l.
  Proof.
    intros l K H. unfold zlen. induction l as [|x l IH]; cbn [BecGap.zsum length]; [lia|].
    rewrite Nat2Z.inj_succ. pose proof (H x (or_introl eq_refl)). specialize (IH ltac:(intros y Hy; apply H; right; exact Hy)). lia.
  Qed.

  Lemma agap_room : forall (K S M hc : Z),
    0 <= K <= 16177 -> 0 <= S <= ASECMAX * K -> 0 < M <= 2 ^ 28 + 12294 -> 0x7fff7f800000 <= hc ->
    AHI_LO + (AHL0 + S) + (AHC0 + K) * (M + 4096) + M <= hc.
  Proof.
    intros K S M hc HK HS HM Hc. unfold AHI_LO, AHL0, AHC0, ASECMAX in *.
    assert (P1 : (32 + K) * (M + 4096) <= 16209 * (2 ^ 28 + 12294 + 4096)).
    { apply Z.mul_le_mono_nonneg; lia. }
    assert (P2 : (2 ^ 32 + 2 ^ 14) * K <= (2 ^ 32 + 2 ^ 14) * 16177) by (apply Z.mul_le_mono_nonneg_l; lia).
    lia.
  Qed.

  Lemma mneeded_primary : forall n, 1 <= n -> mprimary n = true ->
    mneeded n = rq_needed (compute_req n) /\ rq_primary (compute_req n) = true /\ 1 <= class_id (mneeded n) < kNumClasses.
  Proof.
    intros n Hn PR. unfold mprimary in PR. apply Z.leb_le in PR. pose proof (req_shape n Hn) as (_ & _ & ND & PRI & _).
    assert (P : rq_primary (compute_req n) = true) by (apply (proj2 PRI); unfold mneeded in PR; exact PR).
    split; [rewrite ND, P; unfold mneeded; lia|]. split; [exact P|].
    unfold kNumClasses. apply class_id_range. unfold mneeded, kMaxSize in *. pose proof (rz_size_facts n) as (RZ & _). unfold round_up in *.
    Z.div_mod_to_equations. lia.
  Qed.

  Lemma schunk_eq_dec : forall x y : schunk, {x = y} + {x <> y}.
  Proof. intros [a b c] [a' b' c']. destruct (Z.eq_dec a a'), (Z.eq_dec b b'), (Z.eq_dec c c'); subst; try (left; reflexivity); right; congruence. Qed.

  Lemma sh_land : forall X k a, AIMG_TOP <= X -> X + k <= aceil -> sh X <= a < sh X + k / 8 -> ALOWSH_LO <= a < AHI_LO.
  Proof.
    intros X k a H1 H2 Ha. pose proof sh_ceiling_lt_AHI_LO as SC. acb. unfold sh, ASHADOW_BASE, AIMG_TOP, ALOWSH_LO, AHI_LO in *.
    Z.div_mod_to_equations. lia.
  Qed.
  Lemma akobj_not_land : forall X k a, akobj X k -> X + k <= aceil -> X <= a < X + k -> ~ (ALOWSH_LO <= a < AHI_LO).
  Proof. intros X k a AK CE Ha L. clear - AK CE Ha L. aunf. lia. Qed.
  Lemma aapp_ge_top : forall X k, aapp X k -> AIMG_TOP <= X.
  Proof. intros X k A. clear - A. aunf. lia. Qed.

  Lemma image_not_written : forall s s' d lo SP a,
    placed_ok s -> placed_ok s' -> a_thr s' = a_thr s -> depot_placed s d -> aceil <= lo ->
    AIMG_LO <= a < AIMG_TOP -> ~ astatw a -> ~ awrit s s' d lo SP a.
  Proof.
    intros s s' d lo SP a PL PL' ET DPL LO IMG NS W.
    pose proof PL as (_ & S2 & S3 & _ & P2 & P3 & _ & T2 & T3 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SEC & _).
    pose proof PL' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SEC' & _).
    pose proof DPL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & G10 & _ & G12 & _).
    acb. unfold awrit in W. destruct W as [C|[C|[C|[C|[C|[C|[C|[C|C]]]]]]]].
    - unfold AIMG_TOP in IMG. lia.
    - clear - T2 C IMG. aunf. unfold kPageSize in *. lia.
    - unfold AHI_LO, AIMG_TOP in *. lia.
    - unfold sh, ASHADOW_BASE, AHI_LO, AIMG_TOP in *. Z.div_mod_to_equations. lia.
    - pose proof (aapp_ge_top _ _ P2). lia.
    - destruct C as (sc & IN & R).
      assert (AP : aapp (sc_map_beg sc) (sc_map_size sc)) by (destruct IN as [IN|IN]; [exact (proj1 (proj2 (SEC sc IN)))| exact (proj1 (proj2 (SEC' sc IN)))]).
      pose proof (aapp_ge_top _ _ AP). unfold sh, ASHADOW_BASE, AIMG_TOP in *. Z.div_mod_to_equations. lia.
    - exact (NS C).
    - pose proof (aapp_ge_top _ _ G10). lia.
    - pose proof (aapp_ge_top _ _ G12). lia.
  Qed.

  Lemma thread_head_not_written : forall s s' d lo SP a,
    placed_ok s -> placed_ok s' -> a_thr s' = a_thr s -> depot_placed s d -> aceil <= lo ->
    a_thr s <= a < a_thr s + 64 -> ~ awrit s s' d lo SP a.
  Proof.
    intros s s' d lo SP a PL PL' ET DPL LO HT W.
    pose proof PL as (_ & S2 & S3 & _ & P2 & P3 & _ & T2 & T3 & _ & _ & _ & _ & DST & _ & DPT & _ & _ & _ & _ & _ & _ & _ & SEC & _).
    pose proof PL' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SEC' & _).
    pose proof DPL as (G1 & G2 & _).
    acb. unfold awrit in W. destruct W as [C|[C|[C|[C|[C|[C|[C|[C|C]]]]]]]].
    - unfold kPageSize in T3. lia.
    - lia.
    - clear - DST C HT. unfold disj, kPageSize in *. lia.
    - pose proof (akobj_not_land _ _ a T2 T3 ltac:(unfold kPageSize; lia)) as NL. apply NL.
      apply (sh_land (a_sb s) (kSpaceSize + kPageSize)); [unfold AHI_LO, AIMG_TOP in *; lia| clear - S3; lia|].
      clear - C. unfold sh, kSpaceSize, kPageSize in *. Z.div_mod_to_equations. lia.
    - clear - DPT C HT. unfold disj, kPageSize in *. lia.
    - destruct C as (sc & IN & R).
      assert (Q : aapp (sc_map_beg sc) (sc_map_size sc) /\ sc_map_beg sc + sc_map_size sc <= aceil /\ disj (sc_map_beg sc) (sc_map_size sc) (a_thr s) kPageSize).
      { destruct IN as [IN|IN]; [pose proof (SEC sc IN) as (_ & A & B & _ & _ & _ & Dt & _)| pose proof (SEC' sc IN) as (_ & A & B & _ & _ & _ & Dt & _); rewrite ET in Dt]; exact (conj A (conj B Dt)). }
      destruct Q as (AP & CE & DT). destruct R as [R|R].
      + clear - DT R HT. unfold disj, kPageSize in *. lia.
      + apply (akobj_not_land _ _ a T2 T3 ltac:(unfold kPageSize; lia)). apply (sh_land (sc_map_beg sc) (sc_map_size sc)); [exact (aapp_ge_top _ _ AP)| exact CE| exact R].
    - clear - T2 C HT. aunf. unfold astatw, AINST, AIAINIT, AIAINST, kPageSize in *. lia.
    - clear - G1 C HT. unfold disj, kPageSize in *. lia.
    - clear - G2 C HT. unfold disj, kPageSize in *. lia.
  Qed.

  Lemma imgshadow_not_written : forall s s' d lo SP a,
    placed_ok s -> placed_ok s' -> a_thr s' = a_thr s -> depot_placed s d -> aceil <= lo ->
    sh AIMG_LO <= a < sh AIMG_TOP -> ~ awrit s s' d lo SP a.
  Proof.
    intros s s' d lo SP a PL PL' ET DPL LO HS W.
    pose proof PL as (_ & S2 & S3 & _ & P2 & P3 & _ & T2 & T3 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SEC & _).
    pose proof PL' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SEC' & _).
    pose proof DPL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & G10 & _ & G12 & _).
    acb. unfold sh, ASHADOW_BASE, AIMG_LO, AIMG_TOP in HS. unfold awrit in W. destruct W as [C|[C|[C|[C|[C|[C|[C|[C|C]]]]]]]].
    - lia.
    - clear - T2 C HS. aunf. unfold kPageSize in *. lia.
    - unfold AHI_LO in *. lia.
    - unfold sh, ASHADOW_BASE, AHI_LO in *. Z.div_mod_to_equations. lia.
    - clear - P2 C HS. aunf. unfold kPtrArrayReserve in *. lia.
    - destruct C as (sc & IN & R).
      assert (AP : aapp (sc_map_beg sc) (sc_map_size sc)) by (destruct IN as [IN|IN]; [exact (proj1 (proj2 (SEC sc IN)))| exact (proj1 (proj2 (SEC' sc IN)))]).
      destruct R as [R|R]; [clear - AP R HS; aunf; lia|]. pose proof (aapp_ge_top _ _ AP). unfold sh, ASHADOW_BASE, AIMG_TOP in *. Z.div_mod_to_equations. lia.
    - unfold astatw, AINST, AIAINIT, AIAINST in C. lia.
    - clear - G10 C HS. aunf. lia.
    - clear - G12 C HS. aunf. lia.
  Qed.

  Variable p : iparams.

  Lemma dtv_not_written : forall s s' d lo SP mo1 mo' a,
    placed_ok s -> placed_ok s' -> a_thr s' = a_thr s -> a_sb s' = a_sb s -> a_pa s' = a_pa s -> aceil <= lo ->
    akobj (ip_D p) kPageSize -> ip_D p + 32 <= aceil -> 0 < ip_D p ->
    IDAPART p s d -> (forall sc, In sc (as_sec (a_st s)) -> disj (sc_map_beg sc) (sc_map_size sc) (ip_D p) kPageSize) ->
    dtv_cov p mo1 -> avmx s s' mo1 mo' ->
    ip_D p <= a < ip_D p + 32 -> ~ awrit s s' d lo SP a.
  Proof.
    intros s s' d lo SP mo1 mo' a PL PL' ET ESB EPA LO AKD DCE DPOS (DA1 & DA2 & DA3 & DA4 & DA5) DSEC DTV AVX HD W.
    pose proof PL as (_ & S2 & S3 & _ & P2 & P3 & _ & T2 & T3 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SEC & _).
    pose proof PL' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SEC' & _).
    assert (NL : ~ (ALOWSH_LO <= a < AHI_LO)).
    { intros L. clear - AKD DCE HD L. acb. unfold akobj, alow1, aapp, aapp_lo, aapp_hi, AIMG_LO, AIMG_TOP, ALOWSH_LO, AHI_LO, kPageSize in *. lia. }
    acb. unfold awrit in W. destruct W as [C|[C|[C|[C|[C|[C|[C|[C|C]]]]]]]].
    - lia.
    - clear - DA2 C HD. unfold disj, kPageSize in *. lia.
    - clear - DA1 C HD. unfold disj, kPageSize in *. lia.
    - apply NL. apply (sh_land (a_sb s) (kSpaceSize + kPageSize)); [unfold AHI_LO, AIMG_TOP in *; lia| clear - S3; lia|].
      clear - C. unfold sh, kSpaceSize, kPageSize in *. Z.div_mod_to_equations. lia.
    - clear - DA3 C HD. unfold disj, kPageSize in *. lia.
    - destruct C as (sc & IN & R).
      assert (Q : aapp (sc_map_beg sc) (sc_map_size sc) /\ sc_map_beg sc + sc_map_size sc <= aceil).
      { destruct IN as [IN|IN]; [pose proof (SEC sc IN) as (_ & A & B & _)| pose proof (SEC' sc IN) as (_ & A & B & _)]; exact (conj A B). }
      destruct Q as [AP CE]. destruct R as [R|R].
      + destruct (in_dec schunk_eq_dec sc (as_sec (a_st s))) as [INs|NIs].
        * pose proof (DSEC sc INs) as DS. clear - DS R HD. unfold disj, kPageSize in *. lia.
        * destruct IN as [IN|IN]; [exact (NIs IN)|].
          assert (RA : 0 <= a < 2 ^ 64) by lia.
          pose proof (DTV (wz a) ltac:(unfold wz; rewrite unsigned_lit by exact RA; unfold kPageSize; lia)) as CV.
          pose proof (proj2 (AVX (wz a) CV) sc IN NIs) as NR. apply NR. unfold wz. rewrite unsigned_lit by exact RA. exact R.
      + apply NL. apply (sh_land (sc_map_beg sc) (sc_map_size sc)); [exact (aapp_ge_top _ _ AP)| exact CE| exact R].
    - clear - AKD C HD. aunf. unfold astatw, AINST, AIAINIT, AIAINST, kPageSize in *. lia.
    - clear - DA4 C HD. unfold disj, kPageSize in *. lia.
    - clear - DA5 C HD. unfold disj, kPageSize in *. lia.
  Qed.

  Lemma obj_not_written : forall (X len : Z) s s' d lo SP mo1 mo' a,
    placed_ok s -> placed_ok s' -> a_thr s' = a_thr s -> a_sb s' = a_sb s -> a_pa s' = a_pa s -> aceil <= lo ->
    akobj X len -> X + len <= aceil -> 0 < X -> 0 <= len ->
    disj (a_sb s) (kSpaceSize + kPageSize) X len -> disj (a_thr s) kPageSize X len -> disj (a_pa s) kPtrArrayReserve X len ->
    disj (d_nb d) (16 * 65536) X len -> disj (d_sb d) (8 * 32768) X len ->
    (forall sc, In sc (as_sec (a_st s)) -> disj (sc_map_beg sc) (sc_map_size sc) X len) ->
    (forall x : word, X <= bv_unsigned x < X + len -> in_rangesb x (vm_maps (m_vmmaps mo1)) = true) -> avmx s s' mo1 mo' ->
    X <= a < X + len -> ~ awrit s s' d lo SP a.
  Proof.
    intros X len s s' d lo SP mo1 mo' a PL PL' ET ESB EPA LO AKD DCE DPOS LPOS DA1 DA2 DA3 DA4 DA5 DSEC DTV AVX HD W.
    pose proof PL as (_ & S2 & S3 & _ & P2 & P3 & _ & T2 & T3 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SEC & _).
    pose proof PL' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SEC' & _).
    assert (NL : ~ (ALOWSH_LO <= a < AHI_LO)).
    { intros L. clear - AKD DCE HD L. acb. unfold akobj, alow1, aapp, aapp_lo, aapp_hi, AIMG_LO, AIMG_TOP, ALOWSH_LO, AHI_LO in *. lia. }
    acb. unfold awrit in W. destruct W as [C|[C|[C|[C|[C|[C|[C|[C|C]]]]]]]].
    - lia.
    - clear - DA2 C HD. unfold disj, kPageSize in *. lia.
    - clear - DA1 C HD. unfold disj, kPageSize in *. lia.
    - apply NL. apply (sh_land (a_sb s) (kSpaceSize + kPageSize)); [unfold AHI_LO, AIMG_TOP in *; lia| clear - S3; lia|].
      clear - C. unfold sh, kSpaceSize, kPageSize in *. Z.div_mod_to_equations. lia.
    - clear - DA3 C HD. unfold disj, kPageSize in *. lia.
    - destruct C as (sc & IN & R).
      assert (Q : aapp (sc_map_beg sc) (sc_map_size sc) /\ sc_map_beg sc + sc_map_size sc <= aceil).
      { destruct IN as [IN|IN]; [pose proof (SEC sc IN) as (_ & A & B & _)| pose proof (SEC' sc IN) as (_ & A & B & _)]; exact (conj A B). }
      destruct Q as [AP CE]. destruct R as [R|R].
      + destruct (in_dec schunk_eq_dec sc (as_sec (a_st s))) as [INs|NIs].
        * pose proof (DSEC sc INs) as DS. clear - DS R HD. unfold disj in *. lia.
        * destruct IN as [IN|IN]; [exact (NIs IN)|].
          assert (RA : 0 <= a < 2 ^ 64) by lia.
          pose proof (DTV (wz a) ltac:(unfold wz; rewrite unsigned_lit by exact RA; lia)) as CV.
          pose proof (proj2 (AVX (wz a) CV) sc IN NIs) as NR. apply NR. unfold wz. rewrite unsigned_lit by exact RA. exact R.
      + apply NL. apply (sh_land (sc_map_beg sc) (sc_map_size sc)); [exact (aapp_ge_top _ _ AP)| exact CE| exact R].
    - clear - AKD C HD. aunf. unfold astatw, AINST, AIAINIT, AIAINST in *. lia.
    - clear - DA4 C HD. unfold disj in *. lia.
    - clear - DA5 C HD. unfold disj in *. lia.
  Qed.

  Lemma new_sec_apart : forall (X len : Z) s s' mo1 mo' sc,
    placed_ok s' -> (forall x : word, X <= bv_unsigned x < X + len -> in_rangesb x (vm_maps (m_vmmaps mo1)) = true) -> avmx s s' mo1 mo' ->
    0 <= X -> 0 < len -> X + len <= 2 ^ 64 -> In sc (as_sec (a_st s')) -> ~ In sc (as_sec (a_st s)) -> disj (sc_map_beg sc) (sc_map_size sc) X len.
  Proof.
    intros X len s s' mo1 mo' sc PL' COV AVX X0 LP XL Hsc NIs.
    unfold disj. destruct (Z.le_gt_cases (sc_map_beg sc + sc_map_size sc) X) as [A|A]; [left; exact A|].
    destruct (Z.le_gt_cases (X + len) (sc_map_beg sc)) as [B'|B']; [right; exact B'|]. exfalso.
    pose proof PL' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SEC' & _).
    pose proof (SEC' sc Hsc) as (_ & AP & CE & SZ2 & _). unfold kPageSize in SZ2.
    remember (Z.max (sc_map_beg sc) X) as x0 eqn:Ex0.
    assert (MX : X <= x0 /\ sc_map_beg sc <= x0 /\ (x0 = X \/ x0 = sc_map_beg sc)) by (subst x0; lia).
    assert (RA : 0 <= x0 < 2 ^ 64) by (acb; pose proof (aapp_ge_top _ _ AP); unfold AIMG_TOP in *; lia).
    pose proof (COV (wz x0) ltac:(unfold wz; rewrite unsigned_lit by exact RA; lia)) as CV.
    apply (proj2 (AVX (wz x0) CV) sc Hsc NIs). unfold wz. rewrite unsigned_lit by exact RA. lia.
  Qed.

  Hypothesis TRLEN : (length (ip_TR p) <= 1000)%nat.

  Lemma depot_tr_put : forall d h n, d_wf d -> depot_tr p d -> In h (map depot_hash (ip_TR p)) -> 0 <= n <= 31 ->
    depot_tr p (d_put d h n).
  Proof.
    intros d h n W (T1 & T2 & T3 & T4) Hh Hn. unfold d_put. destruct (Z.eqb_spec (d_find d h) 0) as [Z0|NZ]; [| exact (conj T1 (conj T2 (conj T3 T4)))].
    assert (NI : ~ In h (d_K d)) by (intros K; apply (proj2 (d_find_K d h W)) in K; exact (K Z0)).
    unfold depot_tr. cbn [d_ids d_frames d_hash d_insert]. rewrite (d_K_insert d h n ltac:(lia)).
    split; [lia|]. split.
    - intros id Hid. destruct (Z.eqb_spec id (d_ids d + 1)) as [->|NE]; [exact Hh|]. apply T2. lia.
    - split; [| lia]. apply NoDup_app; [exact T3| constructor; [intros []| constructor]|].
      intros a Ha [<-|[]]. exact (NI Ha).
  Qed.

  Lemma dcap_of_tr : forall d, depot_tr p d -> d_ids d + 1 < 65536 /\ d_frames d + 31 <= 32768.
  Proof.
    intros d (T1 & T2 & T3 & T4).
    assert (IDS : d_ids d <= 1001); [| lia].

    set (tl2 := map (d_hash d) (map Z.of_nat (seq 2 (Z.to_nat (d_ids d - 1))))).
    assert (EK : d_K d = d_hash d 1 :: tl2).
    { unfold d_K, idseq, tl2. replace (Z.to_nat (d_ids d)) with (S (Z.to_nat (d_ids d - 1))) by lia. rewrite <- cons_seq. reflexivity. }
    assert (ND2 : List.NoDup tl2) by (rewrite EK in T3; apply NoDup_cons_iff in T3; exact (proj2 T3)).
    assert (INC : incl tl2 (map depot_hash (ip_TR p))).
    { intros h Hh. unfold tl2 in Hh. apply in_map_iff in Hh. destruct Hh as (id & <- & Hid). apply in_map_iff in Hid. destruct Hid as (k & <- & Hk).
      apply in_seq in Hk. apply T2. lia. }
    pose proof (NoDup_incl_length ND2 INC) as L. unfold tl2 in L. rewrite !length_map, length_seq in L. lia.
  Qed.

  Theorem inst_malloc_stmt : malloc_stmt (KHp p).
  Proof.
    unfold malloc_stmt, malloc_stmt_at. cbn [as_VIS as_RHEAP as_AKREL as_alloc_ok as_Cm as_AL as_rauxv_ok as_SR as_MPRES as_chain as_TR as_St KHp].
    intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc msF m x LB n lo B errv mo CH.
    intros VIS HP K AOK CM AUX SPB ST CEIL LO ERR MI TP SP16 AC HCH TR A0 SZ.
    destruct x as [s d]. cbn [i_s i_d] in *.
    unfold BsSR.VIS in VIS. unfold BsSR.AKREL in K. cbn [i_s cfg_model] in VIS, K. destruct K as [OK IKx]. destruct IKx as (AMX & DCOV & DTV & TBV).
    unfold Ialloc_ok, ILIVE_MAX, ILIVE_CNT_MAX in AOK. destruct AOK as (AOK1 & AOK2 & AOK3). unfold Irauxv_ok in AUX. unfold AMALLOC_STACK in LO.
    pose proof HP as HP0. unfold IRHEAP in HP. cbn [i_s i_d] in HP.
    destruct HP as (HR & IDS & LEN & AWV & FLX & DEP & DPL & DTR & DF1 & DF2 & EF & MF & DFD & TH & TLS & ASV & DAP & DSEC & [PI IQ] & AHM).
    pose proof (proj1 HR) as R. pose proof (proj1 R) as OKs. pose proof (proj2 OKs) as W. pose proof (proj1 OKs) as PL.
    pose proof (nalloc_le_blocks s (lbp LB) m HR) as NAL. unfold lbp in NAL. rewrite zlen_map in NAL. unfold zlen in NAL.
    pose proof (aused_eq_small s (lbp LB) m HR) as AUS. rewrite <- lb_small_lbp in AUS.
    pose proof (nsec_eq_large s (lbp LB) m HR) as NSL. rewrite <- nlarge_lbp in NSL.
    destruct LEN as (LEN & LSM & LLG). unfold ILIVE_CNT_MAX in LEN.

    unfold BsSR.SR.
    eapply (evt_sreach_lazy_at asegs (a_L s) (a_S s) (a_Zr s) _ msF _ mo _ OK VIS); [apply malloc_stub_evt; exact MI|].
    cbv beta. intros msF1 mo1 OK1 SBM1 _ E1.
    pose proof (AMODELX_mat s mo mo1 AMX SBM1) as AMX1. pose proof (depot_cov_mat d mo mo1 DCOV SBM1) as DCOV1.

    destruct (fch_of_achain m (bv_unsigned sp) (bv_unsigned s0) (a_top s) (a_bot s) (bv_unsigned ra) lo CH HCH CEIL ltac:(lia) SP16 (bv_unsigned_in_range _ ra))
      as (CHg & FCH & UTR).
    assert (ALLOW : malloc_cost n <= a_AL s).
    { unfold malloc_cost. destruct (mprimary n) eqn:PR.
      - destruct AMX as [[_ [_ [AB0 _]]] _]. exact AB0.
      - assert (GT : 64512 < n) by (destruct (Z.le_gt_cases n 64512) as [LE|GT]; [rewrite (proj2 (mprimary_iff n ltac:(lia)) LE) in PR; discriminate PR| exact GT]).
        pose proof (lg_cost_le_4n n GT). unfold ICm in CM. replace (n <=? 64512) with false in CM by (symmetry; apply Z.leb_gt; lia). lia. }
    assert (PROOM : pusage (a_st s) + COLD_COST <= B_PRIM) by (pose proof (PROOM_of_PINV (a_st s) W PI); unfold COLD_COST; lia).
    assert (NSEC : zlen (as_sec (a_st s)) <= nalloc_sec (a_st s) + 4177) by exact (NSEC_of_WF (a_st s) W).
    assert (XTRA : if mprimary n then rg_mapped_user (get_region (a_st s) (class_id (mneeded n))) + 2 * kUserMapSize <= kFreeArrayOffset
                   else AGAP (msz_of n) mo1 /\ zlen (as_sec (a_st s)) + 1 <= kChunksBlockCount).
    { destruct (mprimary n) eqn:PR.
      - destruct (mneeded_primary n ltac:(lia) PR) as (MN & RP & HC). apply (ROOM_of_PINV (a_st s) _ W PI HC). rewrite MN. exact (mused_class_pos n ltac:(lia) RP).
      - assert (NLG1 : nlg n = 1) by (unfold nlg; destruct (Z.ltb_spec 64512 n) as [|L]; [reflexivity| exfalso; rewrite (proj2 (mprimary_iff n ltac:(lia)) L) in PR; discriminate PR]).
        split; [| unfold kChunksBlockCount, LMAX in *; lia].
        destruct AMX1 as [_ AK1]. pose proof (ak_hcov s mo1 AK1) as (C1 & C2 & C3). pose proof (msz_of_bound n SZ) as MB.
        apply (AGAP_of_akernel s mo1 (msz_of n) AK1 ltac:(lia)).
        assert (HK : 0 <= zlen (hsec (a_st s)) <= 16177).
        { split; [apply zlen_nonneg|]. unfold hsec. pose proof (zlen_filter_le schigh (as_sec (a_st s))). unfold LMAX in *. lia. }
        apply (agap_room (zlen (hsec (a_st s))) _ (msz_of n) hceil HK); [| clear - MB; lia| acb; hcb; lia].
        split.
        + apply BecGap.zsum_nonneg. apply Forall_map, Forall_forall. intros sc Hsc. unfold hsec in Hsc. apply filter_In in Hsc as [Hsc _]. pose proof (C3 sc Hsc). lia.
        + rewrite <- (zlen_map sc_map_size). apply zsum_le_const. intros x Hx. apply in_map_iff in Hx. destruct Hx as (sc & <- & Hsc).
          unfold hsec in Hsc. apply filter_In in Hsc as [Hsc _]. pose proof (C3 sc Hsc). lia. }
    eapply (malloc_arep ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m msF1 mo1 _ s (lbp LB) d lo n CHg
              HR (conj AWV FLX) AMX1 DEP DPL (conj DF1 DF2) DCOV1 MI ST CEIL ltac:(clear - LO; lia) SP16 ltac:(clear - AUX SPB; lia) ltac:(clear - SZ; lia) TP
              (dcap_of_tr d DTR) FCH A0 ALLOW PROOM XTRA OK1 E1).
    intros msF' mo' PO.
    destruct PO as (s' & U & t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & E_thr & E_ctx & E_fsb & E_zr & E_top & E_bot & AL
                    & OK' & VIS' & HR' & AWV' & FX' & AMX' & NV' & DEP' & DPL' & DCOV' & MI' & ST' & FR' & WM' & CP' & AVX' & [junk BLK] & ADDR & MODEL).
    destruct MODEL as (kaddr & st'' & ev & MK & SBS).

    set (T := utrace 762796 (bv_unsigned sp) (a_top s) (a_bot s) 30 (icpt_chain (bv_unsigned ra) (bv_unsigned s0) (bv_unsigned sp) (a_top s) CHg)) in *.
    set (d' := d_put d (depot_hash T) (Z.of_nat (length T))) in *.
    pose proof (proj1 HR') as R'. pose proof (proj1 R') as OKs'. pose proof (proj2 OKs') as W'. pose proof (proj1 OKs') as PL'.
    assert (W'' : WF st'') by (exact (WF_sbs st'' (a_st s') SBS W')).
    destruct (am_malloc_k_ptr_array (a_st s) n kaddr U st'' ev W MK) as [EPA0 ESB0].
    pose proof SBS as (Xsb & Xpa & _).
    assert (ESB : a_sb s' = a_sb s) by (unfold a_sb; rewrite <- Xsb; exact ESB0).
    assert (EPA : a_pa s' = a_pa s) by (unfold a_pa; rewrite <- Xpa; exact EPA0).

    assert (FIND : exists chn, PositiveMap.find (ckey U) (as_chunks st'') = Some chn /\ ch_user_beg chn = U /\ ch_used chn = rq_size (compute_req n)).
    { destruct (am_malloc_k_frame (a_st s) n kaddr U st'' ev W MK) as (st1 & allocated & cls & CORE & EU & _).
      destruct CORE as (_ & _ & _ & _ & _ & _ & _ & CHE & _). cbn [as_chunks upd_chunk set_chunks] in CHE.
      exists (mk_new allocated (compute_req n) cls). rewrite CHE.
      replace (ch_user_beg (mk_new allocated (compute_req n) cls)) with U by (cbn [ch_user_beg mk_new]; lia).
      split; [apply PositiveMap.gss|]. cbn [ch_user_beg ch_used mk_new]. split; [lia| reflexivity]. }
    pose proof (no_live_at_new s s' (lbp LB) m m' U n st'' HR HR' SBS FIND ltac:(lia)) as NOLIVE.
    assert (PI' : PINVI (a_st s')).
    { assert (SC : same_core (a_st s') st'') by (apply same_core_sbs; unfold same_but_shadow in SBS |- *; intuition congruence).
      split.
      - apply (PINV_core (a_st s') st'' SC). apply (PINV_am_malloc_k (a_st s) n kaddr U st'' ev W W'' PI ltac:(unfold CNTB in *; lia)
               ltac:(intros PRn; rewrite AUS; pose proof (proj1 (prim_iff_small n ltac:(lia)) PRn) as SM;
                     unfold nsmall in AOK1; rewrite (proj2 (Z.leb_le _ _) SM) in AOK1; exact AOK1) ltac:(lia) NOLIVE MK).
      - apply (INITQ_core (a_st s') st'' SC). exact (am_malloc_k_initq (a_st s) n kaddr U st'' ev W IQ MK). }

    pose proof (UTR (ip_TR p) 762796 30 ltac:(lia) TR) as TIN. fold T in TIN.
    pose proof (utrace_length 762796 (bv_unsigned sp) (a_top s) (a_bot s) 30 (icpt_chain (bv_unsigned ra) (bv_unsigned s0) (bv_unsigned sp) (a_top s) CHg) ltac:(lia)) as TL. fold T in TL.
    assert (DTR' : depot_tr p d').
    { apply (depot_tr_put d (depot_hash T) (Z.of_nat (length T)) (proj1 DEP) DTR); [apply in_map_iff; exists T; split; [reflexivity| exact TIN]| lia]. }
    destruct (d_put_blocks d (depot_hash T) (Z.of_nat (length T))) as [DNB DSB]. fold d' in DNB, DSB.

    pose proof TH as (TH1 & TH2 & DPOS & DM8 & DCE & AKD).
    pose proof CP' as AG'. unfold acompl in AG'.
    assert (AGR : agree_on (fun a => ~ awrit s s' d lo (bv_unsigned sp) a) m m') by (intros x Hx Hr; exact (AG' x Hr Hx)).
    assert (DTV1 : dtv_cov p mo1) by (intros x Hx; rewrite (same_but_materialized_vmmaps mo mo1 SBM1); exact (DTV x Hx)).
    assert (IMGW : forall a, AIMG_LO <= a < AIMG_TOP -> ~ astatw a -> ~ awrit s s' d lo (bv_unsigned sp) a).
    { intros a H1 H2. exact (image_not_written s s' d lo (bv_unsigned sp) a PL PL' E_thr DPL CEIL H1 H2). }
    assert (DTVW : forall a, ip_D p <= a < ip_D p + 32 -> ~ awrit s s' d lo (bv_unsigned sp) a).
    { intros a Ha. exact (dtv_not_written s s' d lo (bv_unsigned sp) mo1 mo' a PL PL' E_thr ESB EPA CEIL AKD DCE DPOS DAP DSEC DTV1 AVX' Ha). }

    pose proof AHM as (AH1 & AH2 & AH3 & AHP & AHA & AHK & AHC & AT1 & AT2 & AT3 & AT4 & AT5 & AT6 & AT7 & ATS).
    assert (TBV1 : tb_cov p mo1) by (intros x Hx; rewrite (same_but_materialized_vmmaps mo mo1 SBM1); exact (TBV x Hx)).
    assert (TBW : forall a, ip_TB p <= a < ip_TB p + AHM_SIZE -> ~ awrit s s' d lo (bv_unsigned sp) a).
    { intros a Ha. exact (obj_not_written (ip_TB p) AHM_SIZE s s' d lo (bv_unsigned sp) mo1 mo' a PL PL' E_thr ESB EPA CEIL AHK AHC AHP
                            ltac:(unfold AHM_SIZE; lia) AT1 AT2 AT3 AT4 AT5 ATS TBV1 AVX' Ha). }
    assert (RH' : IRHEAP p (IST s' d') ((U, U, n) :: LB) m').
    { unfold IRHEAP. cbn [i_s i_d lbp map blk_addr blk_size blk_id fst snd].
      split; [exact HR'|].
      split; [constructor; [cbn; split; [reflexivity| lia]| exact IDS]|].
      split; [cbn [length]; rewrite Nat2Z.inj_succ, lb_small_cons, nlarge_cons; cbn [blk_size snd]; unfold ILIVE_CNT_MAX; lia|].
      split; [exact AWV'|]. split; [exact FX'|]. split; [exact DEP'|]. split; [exact DPL'|]. split; [exact DTR'|].
      split; [rewrite E_fsb, DNB; exact DF1|]. split; [rewrite E_fsb, DSB; exact DF2|].
      split; [rewrite E_fsb; exact EF|]. split; [exact MF|]. split; [rewrite E_fsb; exact DFD|].
      split.
      {
        unfold ATHR. split; [| split; [| exact (conj DPOS (conj DM8 (conj DCE AKD)))]].
        - eapply (rw_cells_transport_pt _ m m' AGR WM'); [exact TH1|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ length].
          intros a Ha. apply IMGW; unfold astatw, ATP, AIMG_LO, AIMG_TOP, AINST, AIAINIT, AIAINST in *; lia.
        - eapply (rw_cells_transport_pt _ m m' AGR WM'); [exact TH2|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ length].
          intros a Ha. apply DTVW. lia. }
      split.
      { destruct TLS as (tb & te & TC). exists tb, te. rewrite E_thr. eapply (rw_cells_transport_pt _ m m' AGR WM'); [exact TC|].
        cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ length]. intros a Ha.
        exact (thread_head_not_written s s' d lo (bv_unsigned sp) a PL PL' E_thr DPL CEIL ltac:(lia)). }
      split; [exact (proj1 (proj2 (proj1 AMX')))|].
      split; [unfold IDAPART; rewrite ESB, E_thr, EPA, DNB, DSB; exact DAP|].
      split; [| split; [exact PI'|]].
      2:{
          unfold AHMI. rewrite ESB, E_thr, EPA, DNB, DSB, E_fsb.
          split; [eapply (rw_cells_transport_pt _ m m' AGR WM'); [exact AH1|]; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ length];
                  intros a Ha; apply IMGW; unfold astatw, AIMM_OBJ, AIMG_LO, AIMG_TOP, AINST, AIAINIT, AIAINST in *; lia|].
          split; [eapply (rw_cells_transport_pt _ m m' AGR WM'); [exact AH2|]; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ length];
                  intros a Ha; apply TBW; unfold AHM_SIZE, AHM_B1 in *; lia|].
          split; [eapply (rw_cells_transport_pt _ m m' AGR WM'); [exact AH3|]; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ length];
                  intros a Ha; apply TBW; unfold AHM_SIZE, AHM_B2 in *; lia|].
          repeat (split; [assumption|]).
          intros sc Hsc. destruct (in_dec schunk_eq_dec sc (as_sec (a_st s))) as [INs|NIs]; [exact (ATS sc INs)|].
          exact (new_sec_apart (ip_TB p) AHM_SIZE s s' mo1 mo' sc PL' TBV1 AVX' ltac:(lia) ltac:(unfold AHM_SIZE; lia) ltac:(acb; lia) Hsc NIs). }
      intros sc Hsc. destruct (in_dec schunk_eq_dec sc (as_sec (a_st s))) as [INs|NIs]; [exact (DSEC sc INs)|].

      unfold disj. destruct (Z.le_gt_cases (sc_map_beg sc + sc_map_size sc) (ip_D p)) as [A|A]; [left; exact A|].
      destruct (Z.le_gt_cases (ip_D p + kPageSize) (sc_map_beg sc)) as [B'|B']; [right; exact B'|]. exfalso.

      set (x0 := Z.max (sc_map_beg sc) (ip_D p)).
      assert (RA : 0 <= x0 < 2 ^ 64) by (acb; unfold kPageSize in *; lia).
      pose proof (DTV1 (wz x0) ltac:(unfold wz; rewrite unsigned_lit by exact RA; unfold kPageSize in *; lia)) as CV.
      pose proof PL' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SEC' & _).
      pose proof (SEC' sc Hsc) as (_ & _ & _ & SZ2 & _). unfold kPageSize in SZ2.
      apply (proj2 (AVX' (wz x0) CV) sc Hsc NIs). unfold wz. rewrite unsigned_lit by exact RA. lia. }
    apply sreach_done. unfold BsIface.malloc_post.
    exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m', errv, U, junk, U, (IST s' d').
    cbn [as_VIS as_RHEAP as_AKREL as_alloc_ok as_Cm as_AL as_rauxv_ok as_SR as_MPRES as_chain as_TR as_St as_FSB KHp i_s i_d].
    split; [unfold BsSR.VIS; cbn [i_s]; exact VIS'|].
    split. { unfold BsSR.AKREL. cbn [i_s i_d cfg_model cfg_ms]. split; [exact OK'|]. split; [exact AMX'|]. split; [exact DCOV'|].
             split.
             { intros x Hx. destruct (proj1 (AVX' x (DTV1 x Hx))) as [C|(sc & INs & _ & Rx)]; [exact C| exfalso].
               pose proof (DSEC sc INs) as DS. clear - DS Rx Hx. unfold disj, kPageSize in *. lia. }
             intros x Hx. destruct (proj1 (AVX' x (TBV1 x Hx))) as [C|(sc & INs & _ & Rx)]; [exact C| exfalso].
             pose proof (ATS sc INs) as DS. clear - DS Rx Hx. unfold disj in *. lia. }
    split; [exact (nonvm_same_trans _ _ _ (nonvm_same_mat mo mo1 SBM1) NV')|].
    split; [exact MI'|]. split; [exact ST'|].
    split. { rewrite TP. unfold wz. rewrite unsigned_lit by (unfold BsIface.ATP; lia). rewrite TP in ERR. rewrite unsigned_lit in ERR by (unfold BsIface.ATP; lia).
             eapply (rw_cells_transport_pt _ m m' AGR WM'); [exact ERR|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ length].
             intros a Ha. apply IMGW; unfold astatw, BsIface.ATP, AIMG_LO, AIMG_TOP, AINST, AIAINIT, AIAINST in *; lia. }
    split; [exact AUX|].
    split. {
             intros a Ha CL. split; [| intros Wv; apply WM'; exact Wv]. apply (FR' a Ha).
             unfold aclient_addr in CL. unfold aclient. cbn [as_FSB KHp] in CL.
             destruct CL as [C|[C|[C|[C|[C|[C|C]]]]]]; [left; exact C| right; left; exact C| | | | |].
             - right; right; left. destruct C as (b & Hb & Rb). exists (blk_addr b), (blk_size b). split; [| exact Rb].
               unfold lbp. apply in_map_iff. exists b. split; [reflexivity| exact Hb].
             - right; right; right; left. destruct C as (b & Hb & Rb). exists (blk_addr b), (blk_size b). split; [| exact Rb].
               unfold lbp. apply in_map_iff. exists b. split; [reflexivity| exact Hb].
             - do 4 right; left. rewrite EF. exact C.
             - do 5 right; left. rewrite EF. exact C.
             - do 6 right. exact C. }
    split; [exact (inst_RHEAP_block_range p (IST s' d') ((U, U, n) :: LB) m' (U, U, n) RH' (or_introl eq_refl))|].
    split; [exact RH'|].
    split; [exact BLK|]. split; [exact ADDR|].
    split. {
             eapply (ACONST_ext m m' AC).
             - intros a Ha HC. apply (AGR a); [| exact Ha]. unfold aconst_addr in HC.
               unfold BsConst.ASHBASE_CELL, AMEMCPYP_CELL, AINITED_CELL, AHIEND_CELL, ADYING_CELL, APGSZ_CELL, ACANPOISON_CELL, AVERBOSITY_CELL,
                 AREAL_TLSGA_CELL, ATSD_CELL, AREGISTERED_CELL, ACOVFLAG_CELL in HC.
               destruct (Z.lt_ge_cases a AIMG_TOP) as [LT|GE].
               + apply IMGW; unfold astatw, sh, ASHADOW_BASE, AIMG_LO, AIMG_TOP, AINST, AIAINIT, AIAINST in *; clear - HC LT; lia.
               + apply (imgshadow_not_written s s' d lo (bv_unsigned sp) a PL PL' E_thr DPL CEIL). unfold sh, ASHADOW_BASE, AIMG_LO, AIMG_TOP in *; clear - HC GE; lia.
             - intros a Ha Wv. apply WM'. exact Wv.
             - intros a Ha. destruct AC as (_ & _ & (S0 & S1 & SS)). destruct (SS a Ha) as [W0 (b & Hb)]. exists b.
               unfold mrd in *. rewrite (AGR a); [exact Hb| | unfold sh, AIMG_LO, AIMG_TOP, ASHADOW_BASE in *; lia].
               exact (imgshadow_not_written s s' d lo (bv_unsigned sp) a PL PL' E_thr DPL CEIL Ha). }

    unfold ICm. destruct (Z.leb_spec n 64512) as [LE|GT].
    - unfold malloc_cost in AL. rewrite (proj2 (mprimary_iff n ltac:(lia)) LE) in AL. lia.
    - unfold malloc_cost in AL. destruct (mprimary n) eqn:PR; [pose proof (proj1 (mprimary_iff n ltac:(lia)) PR); lia|].
      pose proof (lg_cost_le_4n n GT). lia.
  Qed.
End Heap.
