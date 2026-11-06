(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc Require Import Prelim STree Malloc MallocCtrl KInv
  MI_Inv MI_Kit MI_List MI_Cnt MI_Ledger MI_WAMeta MI_WSlot2 MI_WNtf2 MI_Contracts MF_Phi MF_SiteC.
Unset Nia Cache. Unset Nra Cache.
Unset Lia Cache.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Set Keyed Unification.
Import ListNotations.
Local Open Scope Z_scope.

Section CEIL.
Context {CLG : OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.Ceiling.ceiling}.

Lemma cpath_vis_inv {R} L e (k : Z -> M R) L' r :
  cpath L (SVis e k) L' r -> exists z, answer_ok L e z = true /\ cpath (event_post L e z) (k z) L' r.
Proof. intros CP. inversion CP; subst. eexists; split; eassumption. Qed.

Lemma cpath_ret_inv {R} L (x : R) L' r : cpath L (SRet x) L' r -> L' = L /\ r = x.
Proof. intros CP. inversion CP; subst. auto. Qed.

Lemma cpath_undef_inv {R} L u (k : Z -> M R) L' r : cpath L (SVis (EUndef u) k) L' r -> False.
Proof. intros CP. inversion CP; subst. cbn in *. discriminate. Qed.

Lemma answer_ok_mmap_anon L len a : answer_ok L (EMmap 0 len PROT_RW MAPF') a = mmap_answer_ok (lranges L) len a.
Proof. reflexivity. Qed.

Lemma errno_is_err z : is_errno_form z = true -> is_err z = true.
Proof.
  unfold is_errno_form, is_err. intros H. apply andb_true_iff in H as [H _]. apply Z.leb_le in H. apply Z.ltb_lt. unfold TWO64 in *. lia.
Qed.

Lemma sbind_ret {R S} (x : R) (f : R -> M S) : sbind (ret x) f = f x.
Proof. reflexivity. Qed.

Lemma if_true_eq {A} (x y : A) : (if true then x else y) = x. Proof. reflexivity. Qed.

Lemma if_false_eq {A} (x y : A) : (if false then x else y) = y. Proof. reflexivity. Qed.
Lemma guard_true {R} n (k b : M R) : guard n true k b = k. Proof. reflexivity. Qed.

Lemma take_eq {R} st (k : mstate -> optr -> M R) bail :
  c_init_done (s_ctx st) = 1 ->
  (c_free_meta_head (s_ctx st) = None /\ 0 < c_avail_meta_count (s_ctx st) /\ c_avail_meta (s_ctx st) <> None)
  \/ (exists f, c_free_meta_head (s_ctx st) = Some f /\ m_next (get_meta_rec st f) = Some f) ->
  alloc_meta st k bail = k (snd (take st)) (Some (fst (take st))).
Proof.
  intros HI [(HN & HC & HQ)|(f & HF & Hf)]; unfold take.
  - rewrite HN. destruct (c_avail_meta (s_ctx st)) as [q|] eqn:EQ; [| congruence]. cbn [default fst snd].
    apply alloc_meta_take; assumption.
  - rewrite HF. cbn [fst snd]. apply alloc_meta_free; assumption.
Qed.

Section BM.
Variables (cs : mstate) (L : mled) (n : Z).
Hypothesis HP : PHI cs.
Hypothesis CR : SIMREL cs L.
Hypothesis Hn : MMAP_THRESHOLD <= n.
Hypothesis Hov : size_overflows n = false.

Let needed := n + IB + UNIT.

Definition bm_st2 (a : Z) : mstate := step_seq (fst (new_region RKGroup a needed cs)).
Definition bm_final (a : Z) : mstate :=
  let rid := s_next_rid cs in
  let g := fst (take (bm_st2 a)) in
  let st3 := snd (take (bm_st2 a)) in
  let st4 := upd_meta g (fun mr => m_set_freed 0 (m_set_avail 0 (m_set_maplen ((needed + 4095) / 4096)
               (m_set_sizeclass 63 (m_set_freeable 1 (m_set_last_idx 0 (m_set_mem (Some (rid, 0)) mr))))))) st3 in
  let st5 := put_group (rid, 0) (Some g) (group_active_idx st4 (rid, 0)) st4 in
  let st6 := add_slots g (rid, 0) (get_stride (get_meta_rec st5 g)) 1 st5 in
  upd_ctx (fun c => set_mmap_counter (u32 (c_mmap_counter c + 1)) c) st6.

Lemma bm_path L' cs' c : cpath L (cmalloc cs n) L' (cs', Some c) ->
  exists a, is_err a = false /\ mmap_answer_ok (live_ranges cs) needed a = true /\ cs' = strip (bm_final a).
Proof.
  intros CP.
  destruct CR as (st & BL & LS & Ecs & INV & _).
  pose proof (CF_strip st (INVL_CF _ _ _ _ _ INV)) as CF0. rewrite Ecs in CF0.
  assert (LR : live_ranges cs = live_ranges st) by (rewrite <- Ecs; apply live_ranges_strip).
  destruct HP as (PI & PC & PA & PF & PG).
  unfold cmalloc, malloc_core in CP. rewrite Hov in CP. replace (MMAP_THRESHOLD <=? n) with true in CP by (symmetry; apply Z.leb_le; lia).
  rewrite sbind_vis in CP. apply cpath_vis_inv in CP as (a & OK & CP). cbv beta in CP.
  rewrite answer_ok_mmap_anon, (mmap_answer_ok_eq _ _ _ (proj1 INV)), <- LR in OK. fold needed in OK, CP. rewrite OK in CP. cbn [negb] in CP.
  exists a. destruct (is_err a) eqn:EZ.
  { cbn in CP. apply cpath_ret_inv in CP as [_ E]. discriminate. }
  split; [reflexivity|]. split; [exact OK|].
  change (new_region RKGroup a needed cs) with (fst (new_region RKGroup a needed cs), s_next_rid cs) in CP. cbv beta iota in CP.
  fold (bm_st2 a) in CP.
  assert (TK : c_init_done (s_ctx (bm_st2 a)) = 1 /\
     ((c_free_meta_head (s_ctx (bm_st2 a)) = None /\ 0 < c_avail_meta_count (s_ctx (bm_st2 a)) /\ c_avail_meta (s_ctx (bm_st2 a)) <> None)
      \/ (exists f, c_free_meta_head (s_ctx (bm_st2 a)) = Some f /\ m_next (get_meta_rec (bm_st2 a) f) = Some f))).
  { unfold bm_st2. unfold get_meta_rec. autorewrite with mst. split; [exact PI|].
    destruct PF as [[HN HC]|(f & HF & Hf)].
    - left. split; [exact HN|]. split; [lia|]. destruct (cf_avail _ CF0 ltac:(lia)) as (q & Eq & _). rewrite Eq. discriminate.
    - right. exists f. split; [exact HF|]. rewrite Hf. reflexivity. }
  destruct TK as [TK1 TK2]. rewrite (take_eq _ _ _ TK1 TK2) in CP.
  cbv beta iota zeta in CP. rewrite sbind_ret in CP. cbv beta iota zeta in CP. unfold ret in CP.
  apply cpath_ret_inv in CP as [_ E]. injection E as E1 E2. rewrite E1. reflexivity.
Qed.

Lemma bm_PHIB a : is_err a = false -> mmap_answer_ok (live_ranges cs) needed a = true -> PHIB (bm_final a).
Proof.
  intros EZ OK.
  destruct CR as (st & BL & LS & Ecs & INV & _).
  pose proof (CF_strip st (INVL_CF _ _ _ _ _ INV)) as CF0. rewrite Ecs in CF0.
  destruct HP as (PI & PC & PA & PF & PG).

  assert (TKF : exists g st3, take (bm_st2 a) = (g, st3)
            /\ s_metas st3 = <[g := meta0]> (s_metas cs)
            /\ c_init_done (s_ctx st3) = 1 /\ 49 <= c_avail_meta_count (s_ctx st3) /\ c_free_meta_head (s_ctx st3) = None
            /\ (forall sc, active st3 sc = active cs sc)
            /\ s_groups st3 = s_groups cs
            /\ (forall b h m, s_groups cs !! b = Some h -> g_meta h = Some m -> m <> g)).
  { unfold take, bm_st2. unfold get_meta_rec, active, ctx. autorewrite with mst.
    destruct PF as [[HN HC]|(f & HF & Hf)].
    - rewrite HN. destruct (cf_avail _ CF0 ltac:(lia)) as (q & Eq & _ & FREE). rewrite Eq. cbn [default].
      pose proof (cf_count _ CF0) as CC.
      eexists _, _. split; [reflexivity|]. autorewrite with mst. cbn. autorewrite with mst.
      unfold get_meta_rec. autorewrite with mst. rewrite (FREE (NSLOTS - c_avail_meta_count (s_ctx cs)) ltac:(lia)).
      split; [reflexivity|]. split; [exact PI|]. split; [lia|]. split; [exact HN|]. split; [intros; reflexivity|]. split; [reflexivity|].
      intros b h m Hb Hm ->. destruct h as [gm ai]; cbn in Hm; subst gm.
      apply (proj1 (cf_groups _ CF0 b _ ai Hb)). apply FREE. lia.
    - rewrite HF. cbn [fst snd]. eexists _, _. split; [reflexivity|]. autorewrite with mst. cbn. autorewrite with mst.
      unfold get_meta_rec. autorewrite with mst. rewrite Hf.
      split; [reflexivity|]. split; [exact PI|]. split; [lia|]. split; [reflexivity|]. split; [intros; reflexivity|]. split; [reflexivity|].
      intros b h m Hb Hm ->. exact (proj2 (cf_free _ CF0 f HF) b h Hb Hm). }
  destruct TKF as (g & st3 & ET & M3 & I3 & C3 & F3 & A3 & G3 & NG).
  unfold PHIB, bm_final. rewrite ET. cbn [fst snd]. cbv zeta.
  set (st4 := upd_meta g _ st3). set (st5 := put_group _ _ _ st4). set (st6 := add_slots _ _ _ _ st5). set (st7 := upd_ctx _ st6).
  assert (A7 : forall sc, active st7 sc = active cs sc).
  { intros sc. unfold st7, st6, st5, st4, active, ctx. autorewrite with mst. cbn. autorewrite with mst. apply A3. }
  assert (M7 : forall x, x <> g -> get_meta_rec st7 x = get_meta_rec cs x).
  { intros x NE. unfold st7, st6, st5, st4, get_meta_rec. autorewrite with mst. rewrite lookup_insert_ne by congruence.
    rewrite M3, lookup_insert_ne by congruence. reflexivity. }
  assert (MG : get_meta_rec st7 g = mkMeta None None (Some (s_next_rid cs, 0)) 0 0 0 1 63 (Z.land ((needed + 4095) / 4096) (2 ^ 52 - 1))).
  { unfold st7, st6, st5, st4, get_meta_rec. autorewrite with mst. rewrite lookup_insert_eq. cbn -[Z.land Z.div Z.add Z.pow Z.sub needed].
    unfold get_meta_rec. rewrite M3, lookup_insert_eq. reflexivity. }
  assert (HG : forall sc m, active cs sc = Some m -> m <> g).
  { intros sc m HA. destruct (cf_active _ CF0 sc m HA) as (_ & _ & b & ai & Hb & _). exact (NG b _ m Hb eq_refl). }
  split. { unfold st7, st6, st5, st4. autorewrite with mst. cbn. autorewrite with mst. exact I3. }
  split. { unfold st7, st6, st5, st4. autorewrite with mst. cbn. autorewrite with mst. exact C3. }
  split. { intros sc m HA. rewrite A7 in HA. rewrite (M7 m (HG sc m HA)). exact (PA sc m HA). }
  split. { unfold st7, st6, st5, st4. autorewrite with mst. cbn. autorewrite with mst. exact F3. }
  intros b h Hb. unfold st7, st6, st5, st4 in Hb. autorewrite with mst in Hb. rewrite G3 in Hb.
  destruct (aptr_eqb_spec b (s_next_rid cs, 0)) as [->|NE].
  - rewrite lookup_insert_eq in Hb. injection Hb as <-. exists g. split; [reflexivity|].
    unfold buf_group. rewrite MG. cbn -[Z.land Z.div Z.add Z.pow Z.sub needed Z.le Z.lt].
    split; [reflexivity|]. split.
    { change (2 ^ 52 - 1) with (Z.ones 52). rewrite Z.land_ones by lia.
      assert (1 <= (needed + 4095) / 4096 < 2 ^ 52).
      { pose proof Hn as Hn'. pose proof Hov as Hov'. unfold size_overflows in Hov'. apply Z.leb_gt in Hov'.
        unfold needed. unfold MMAP_THRESHOLD, IB, UNIT in Hn', Hov' |- *.
        split; [apply Z.div_le_lower_bound; lia| apply Z.div_lt_upper_bound; lia]. }
      rewrite Z.mod_small by lia. lia. }
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. right. repeat split; try reflexivity. lia.
  - rewrite lookup_insert_ne in Hb by congruence. destruct (PG b h Hb) as (m & Hm & BG). exists m. split; [exact Hm|].
    pose proof (NG b h m Hb Hm) as NEm.
    unfold buf_group in BG |- *. rewrite (M7 m NEm), A7. exact BG.
Qed.

Lemma PHIB_strip_eq : forall X : mstate, PHIB (strip X) = PHIB X.
Proof. intros X. destruct X. reflexivity. Qed.

Theorem T2_Bm_sec L' cs' c : cpath L (cmalloc cs n) L' (cs', Some c) -> PHIB cs'.
Proof.
  intros CP. destruct (bm_path L' cs' c CP) as (a & EZ & OK & ->).
  rewrite PHIB_strip_eq. exact (bm_PHIB a EZ OK).
Qed.
End BM.

Theorem T2_Bm_sim : forall cs L L' cs' c n, PHI cs -> SIMREL cs L -> MMAP_THRESHOLD <= n -> size_overflows n = false ->
  cpath L (cmalloc cs n) L' (cs', Some c) -> PHIB cs'.
Proof. intros cs L L' cs' c n HP CR Hn Hov CP. exact (T2_Bm_sec cs L n HP CR Hn Hov L' cs' c CP). Qed.
Theorem T2_Bm : forall cs L L' cs' c n, PHI cs -> creach cs L -> MMAP_THRESHOLD <= n -> size_overflows n = false ->
  cpath L (cmalloc cs n) L' (cs', Some c) -> PHIB cs'.
Proof. intros cs L L' cs' c n HP CR Hn Hov CP. exact (T2_Bm_sec cs L n HP (creach_sim cs L CR) Hn Hov L' cs' c CP). Qed.

Section BF.
Variables (cs : mstate) (L : mled) (c : cptr).
Hypothesis HP : PHIB cs.
Hypothesis CR : SIMREL cs L.
Hypothesis Hc : In c (ld_live L).

Lemma bf_slot : exists m b ai, s_slots cs !! c = Some (m, 0) /\ s_groups cs !! b = Some (mkGhdr (Some m) ai)
  /\ m_mem (get_meta_rec cs m) = Some b /\ buf_group cs m /\ 0 <= m_maplen (get_meta_rec cs m) /\ CF cs.
Proof.
  destruct CR as (st & BL & LS & Ecs & INV & LIVE).
  pose proof (CF_strip st (INVL_CF _ _ _ _ _ INV)) as CF0. rewrite Ecs in CF0.
  pose proof INV as (IR & IA & IM & IL & IG & IS & ISH).
  rewrite LIVE in Hc. apply in_map_iff in Hc as (k & Ek & Hk).
  destruct (is_blocks _ _ _ IS k Hk) as (m & i & Hs & _).
  destruct (is_valid _ _ _ IS _ _ _ Hs) as ((b & ai & Hb) & Hi & _).
  destruct HP as (PI & PC & PA & PF & PG).
  assert (Hb' : s_groups cs !! b = Some (mkGhdr (Some m) ai)) by (rewrite <- Ecs; exact Hb).
  destruct (PG b _ Hb') as (m' & Em & BG). cbn in Em. injection Em as <-.
  pose proof BG as (L0 & _). change (get_meta_rec cs m) with (MR cs m) in L0. rewrite <- Ecs in L0. change (MR (strip st) m) with (MR st m) in L0.
  assert (i = 0) by lia. subst i.
  exists m, b, ai. split; [rewrite <- Ecs, <- Ek; exact Hs|]. split; [exact Hb'|].
  split; [exact (proj2 (cf_groups _ CF0 b m ai Hb'))|]. split; [exact BG|]. split; [| exact CF0].
  pose proof (g_maplen _ _ _ _ _ _ (ig_ok _ _ _ IG m b ai Hb)) as ML. rewrite <- Ecs. exact ML.
Qed.

Definition bf_pre (m b : aptr) : mstate :=
  let r := get_meta_rec cs m in
  let sc := m_sizeclass r in
  let stX := match m_next r with Some _ => upd_meta m clr_rec (set_active sc None cs) | None => cs end in
  let st1 := if sc <? 48 then set_usage sc (usage stX sc - (0 + 1)) stX else stX in
  let stD := del_slots b (get_stride r) (0 + 1) (del_group b st1) in
  let st2 := record_seq sc (step_seq stD) in
  fm_st st2 m.

Lemma bf_path L' cs' : cpath L (cfree cs (Some c)) L' cs' ->
  exists m b ai, s_groups cs !! b = Some (mkGhdr (Some m) ai) /\ m_mem (get_meta_rec cs m) = Some b /\ buf_group cs m /\ CF cs
    /\ cs' = strip (drop_region (fst b) (bf_pre m b)).
Proof.
  intros CP. destruct bf_slot as (m & b & ai & Hs & Hb & Hmem & BG & ML & CF0). exists m, b, ai.
  split; [exact Hb|]. split; [exact Hmem|]. split; [exact BG|]. split; [exact CF0|].
  destruct HP as (PI & PC & PA & PF & PG).
  pose proof BG as (L0 & MP & FR & AV & FD & CASES).
  unfold cfree in CP. rewrite Hs in CP.
  unfold free_tail in CP.

  revert CP. generalize FUEL. intros F CP.
  rewrite AV, FD, L0 in CP.
  change (negb (testbit (Z.lor 0 0) 0)) with true in CP. rewrite guard_true in CP.
  change (negb ((0 =? 0) || (Z.lor 0 0 + bit 0 =? mask_upto 0))) with false in CP. cbv iota in CP.
  destruct F as [|F'].
  { exfalso. cbn [nontrivial_free sbind] in CP. exact (cpath_undef_inv _ _ _ _ _ CP). }
  rewrite ntf_unfold in CP. change (MR cs m) with (get_meta_rec cs m) in CP.
  rewrite FD, AV, L0 in CP. change (Z.lor 0 0 + bit 0 =? mask_upto 0) with true in CP.
  assert (OK2F : okay_to_free cs m = true).
  { unfold okay_to_free. rewrite FR. cbn [Z.eqb].
    destruct CASES as [(_ & _ & _ & Hsc & STR)|(_ & _ & Hsc)].
    - replace (get_stride (get_meta_rec cs m) <? UNIT * size_class (m_sizeclass (get_meta_rec cs m))) with true by (symmetry; apply Z.ltb_lt; exact STR).
      rewrite orb_true_r. reflexivity.
    - replace (48 <=? m_sizeclass (get_meta_rec cs m)) with true by (symmetry; apply Z.leb_le; exact Hsc). reflexivity. }
  rewrite OK2F in CP. cbn [andb] in CP.

  set (KT := fun (st3 : mstate) (mi : mapinfo) => match mi with
        | Some (base, len) => if negb (len =? 0) then SVis (EMunmap (conc st3 base) len) (fun ru => if munmap_answer_ok ru then ret (drop_region (fst base) st3) else bad_answer (ret cs)) else ret st3
        | None => ret st3 end) in CP.
  set (stX := match m_next (get_meta_rec cs m) with Some _ => upd_meta m clr_rec (set_active (m_sizeclass (get_meta_rec cs m)) None cs) | None => cs end).
  assert (CP' : cpath L (sbind (free_group mstate dec_slots (nontrivial_free dec_slots F') stX m KT (ret cs)) (fun st1 => ret (strip st1))) L' cs').
  { destruct CASES as [(NX & _ & HA & Hsc & _)|(NX & _ & _)]; rewrite NX in CP; subst stX; rewrite NX.
    - unfold guard in CP. replace (m_sizeclass (get_meta_rec cs m) <? 48) with true in CP by (symmetry; apply Z.ltb_lt; lia).
      rewrite HA, optr_eqb_refl in CP. rewrite (dequeue_self _ _ _ NX) in CP. cbn [set_head] in CP.
      rewrite active_upd_meta, active_set_active, Z.eqb_refl in CP. exact CP.
    - exact CP. }
  clear CP.
  assert (MRX : get_meta_rec stX m = match m_next (get_meta_rec cs m) with Some _ => clr_rec (get_meta_rec cs m) | None => get_meta_rec cs m end).
  { subst stX. destruct (m_next (get_meta_rec cs m)); [| reflexivity]. rewrite get_meta_rec_upd_same. reflexivity. }
  assert (FX : m_sizeclass (get_meta_rec stX m) = m_sizeclass (get_meta_rec cs m) /\ m_last_idx (get_meta_rec stX m) = 0
          /\ m_mem (get_meta_rec stX m) = Some b /\ m_maplen (get_meta_rec stX m) = m_maplen (get_meta_rec cs m)
          /\ get_stride (get_meta_rec stX m) = get_stride (get_meta_rec cs m)).
  { rewrite MRX. destruct (m_next (get_meta_rec cs m)); cbn; rewrite ?L0, ?Hmem; repeat split; reflexivity. }
  destruct FX as (F1 & F2 & F3 & F4 & F5).
  unfold free_group in CP'. rewrite F1, F2, F3, F4, F5 in CP'.
  replace (negb (m_maplen (get_meta_rec cs m) =? 0)) with true in CP' by (symmetry; apply negb_true_iff; apply Z.eqb_neq; exact MP).
  try rewrite if_true_eq in CP'.
  rewrite free_meta_eq in CP'.
  assert (EKT : forall st3 len, len <> 0 ->
            KT st3 (Some (b, len)) = SVis (EMunmap (conc st3 b) len) (fun ru => if munmap_answer_ok ru then ret (drop_region (fst b) st3) else bad_answer (ret cs))).
  { intros st3 len Hl. subst KT. cbv beta iota. replace (len =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hl). reflexivity. }
  rewrite EKT in CP' by lia. clear EKT. clearbody KT.
  rewrite sbind_vis in CP'. apply cpath_vis_inv in CP' as (ru & OK & CP'). cbn [answer_ok] in OK. cbv beta in CP'. rewrite OK in CP'.
  try rewrite if_true_eq in CP'.
  rewrite sbind_ret in CP'. unfold ret at 1 in CP'. apply cpath_ret_inv in CP' as [_ E]. rewrite E.
  unfold bf_pre. fold stX. exact eq_refl.
Qed.

Lemma bf_PHI m b ai : s_groups cs !! b = Some (mkGhdr (Some m) ai) -> m_mem (get_meta_rec cs m) = Some b -> buf_group cs m -> CF cs ->
  PHI (drop_region (fst b) (bf_pre m b)).
Proof.
  intros Hb Hmem BG CF0. destruct HP as (PI & PC & PA & PF & PG).
  pose proof BG as (L0 & MP & FR & AV & FD & CASES).
  set (r := get_meta_rec cs m). set (sc := m_sizeclass r).
  set (stX := match m_next r with Some _ => upd_meta m clr_rec (set_active sc None cs) | None => cs end).
  set (F := drop_region (fst b) (bf_pre m b)).

  assert (XA : forall sc', active stX sc' = match m_next r with Some _ => if sc' =? sc then None else active cs sc' | None => active cs sc' end).
  { intros sc'. subst stX. destruct (m_next r); [| reflexivity]. rewrite active_upd_meta, active_set_active. reflexivity. }
  assert (XM : forall x, x <> m -> s_metas stX !! x = s_metas cs !! x).
  { intros x NE. subst stX. destruct (m_next r); [| reflexivity]. rewrite lookup_upd_meta, (aptr_eqb_neq _ _ NE). reflexivity. }
  assert (XC : c_init_done (s_ctx stX) = c_init_done (s_ctx cs) /\ c_avail_meta_count (s_ctx stX) = c_avail_meta_count (s_ctx cs)
          /\ c_free_meta_head (s_ctx stX) = c_free_meta_head (s_ctx cs) /\ s_groups stX = s_groups cs).
  { subst stX. destruct (m_next r); [| repeat split; reflexivity]. autorewrite with mst. cbn. autorewrite with mst. repeat split; reflexivity. }
  destruct XC as (XC1 & XC2 & XC3 & XC4).

  assert (HD : forall st, c_free_meta_head (s_ctx st) = None -> fm_st st m = upd_ctx (set_free_meta_head (Some m)) (upd_meta m (fun r0 => m_set_prev (Some m) (m_set_next (Some m) r0)) (put_meta m meta0 st))).
  { intros st HN. unfold fm_st, queue_st. cbn [get_head]. unfold ctx. autorewrite with mst. rewrite HN. reflexivity. }
  assert (HN2 : c_free_meta_head (s_ctx (record_seq sc (step_seq (del_slots b (get_stride r) (0 + 1) (del_group b (if sc <? 48 then set_usage sc (usage stX sc - (0 + 1)) stX else stX)))))) = None).
  { autorewrite with mst. destruct (sc <? 48); autorewrite with mst; cbn; autorewrite with mst; rewrite XC3; exact PF. }
  assert (EF : F = drop_region (fst b) (upd_ctx (set_free_meta_head (Some m)) (upd_meta m (fun r0 => m_set_prev (Some m) (m_set_next (Some m) r0))
              (put_meta m meta0 (record_seq sc (step_seq (del_slots b (get_stride r) (0 + 1) (del_group b (if sc <? 48 then set_usage sc (usage stX sc - (0 + 1)) stX else stX))))))))).
  { subst F. unfold bf_pre. fold r. fold sc. fold stX. rewrite (HD _ HN2). reflexivity. }
  assert (FA : forall sc', active F sc' = active stX sc').
  { intros sc'. rewrite EF. unfold active, ctx. autorewrite with mst. cbn. autorewrite with mst. destruct (sc <? 48); autorewrite with mst; cbn; autorewrite with mst; reflexivity. }
  assert (FM : forall x, s_metas F !! x = if aptr_eqb x m then Some (selfrec m) else s_metas stX !! x).
  { intros x. rewrite EF. autorewrite with mst. destruct (aptr_eqb_spec x m) as [->|NE].
    - rewrite lookup_insert_eq. unfold get_meta_rec. autorewrite with mst. rewrite lookup_insert_eq. reflexivity.
    - rewrite !lookup_insert_ne by congruence. destruct (sc <? 48); autorewrite with mst; reflexivity. }
  assert (FG : s_groups F = delete b (s_groups cs)).
  { rewrite EF. autorewrite with mst. destruct (sc <? 48); autorewrite with mst; rewrite XC4; reflexivity. }
  assert (FC : c_init_done (s_ctx F) = c_init_done (s_ctx cs) /\ c_avail_meta_count (s_ctx F) = c_avail_meta_count (s_ctx cs)
          /\ c_free_meta_head (s_ctx F) = Some m).
  { rewrite EF. autorewrite with mst. cbn. autorewrite with mst. destruct (sc <? 48); autorewrite with mst; cbn; autorewrite with mst; rewrite ?XC1, ?XC2; repeat split; reflexivity. }
  destruct FC as (FC1 & FC2 & FC3).

  assert (NHm : forall sc' m', active F sc' = Some m' -> m' <> m /\ active cs sc' = Some m').
  { intros sc' m' HA. rewrite FA, XA in HA. destruct CASES as [(NX & _ & HAm & Hsc & _)|(NX & _ & _)]; fold r in NX; rewrite NX in HA.
    - destruct (Z.eqb_spec sc' sc) as [->|NE]; [discriminate|]. split; [| exact HA]. intros ->.
      destruct (cf_active _ CF0 sc' m HA) as (_ & _ & _ & _ & _ & SC'). fold r sc in SC'. lia.
    - split; [| exact HA]. intros ->. destruct (PA sc' m HA) as (_ & _ & NX' & _). fold r in NX'. rewrite NX in NX'. discriminate. }
  split; [rewrite FC1; exact PI|]. split; [rewrite FC2; exact PC|]. split.
  { intros sc' m' HA. destruct (NHm sc' m' HA) as [NE HA']. unfold get_meta_rec. rewrite FM, (aptr_eqb_neq _ _ NE), (XM _ NE).
    exact (PA sc' m' HA'). }
  split. { right. exists m. split; [exact FC3|]. rewrite FM, aptr_eqb_refl. reflexivity. }
  intros b' h Hb'. rewrite FG in Hb'. destruct (aptr_eqb_spec b' b) as [->|NEb]; [rewrite lookup_delete_eq in Hb'; discriminate|].
  rewrite lookup_delete_ne in Hb' by congruence. destruct (PG b' h Hb') as (m' & Hm' & BG'). exists m'. split; [exact Hm'|].
  assert (NEm : m' <> m).
  { intros ->. destruct h as [gm ai']; cbn in Hm'; subst gm. pose proof (proj2 (cf_groups _ CF0 b' m ai' Hb')) as MM. rewrite Hmem in MM. congruence. }
  assert (GM : get_meta_rec F m' = get_meta_rec cs m').
  { unfold get_meta_rec. rewrite FM, (aptr_eqb_neq _ _ NEm), (XM _ NEm). reflexivity. }
  unfold buf_group in BG' |- *. rewrite !GM.
  destruct BG' as (B1 & B2 & B3 & B4 & B5 & BC). repeat (split; [assumption|]).
  destruct BC as [(C1 & C2 & C3 & C4 & C5)|(C1 & C2 & C3)]; [left| right; auto].
  split; [exact C1|]. split; [exact C2|]. split; [| auto]. rewrite FA, XA.
  destruct CASES as [(NX & _ & HAm & Hsc & _)|(NX & _ & _)]; fold r in NX; rewrite NX; [| exact C3].
  destruct (Z.eqb_spec (m_sizeclass (get_meta_rec cs m')) sc) as [E|NE]; [| exact C3].
  exfalso. apply NEm. rewrite E in C3. fold r sc in HAm. rewrite HAm in C3. congruence.
Qed.

Lemma PHI_strip_eq : forall X : mstate, PHI (strip X) = PHI X.
Proof. intros X. destruct X. reflexivity. Qed.

Theorem T2_Bf_sec L' cs' : cpath L (cfree cs (Some c)) L' cs' -> PHI cs'.
Proof.
  intros CP. destruct (bf_path L' cs' CP) as (m & b & ai & Hb & Hmem & BG & CF0 & ->).
  rewrite PHI_strip_eq. exact (bf_PHI m b ai Hb Hmem BG CF0).
Qed.
End BF.

Theorem T2_Bf_sim : forall cs L L' cs' c, PHIB cs -> SIMREL cs L -> In c (ld_live L) -> cpath L (cfree cs (Some c)) L' cs' -> PHI cs'.
Proof. intros cs L L' cs' c HP CR Hc CP. exact (T2_Bf_sec cs L c HP CR Hc L' cs' CP). Qed.
Theorem T2_Bf : forall cs L L' cs' c, PHIB cs -> creach cs L -> In c (ld_live L) -> cpath L (cfree cs (Some c)) L' cs' -> PHI cs'.
Proof. intros cs L L' cs' c HP CR Hc CP. exact (T2_Bf_sec cs L c HP (creach_sim cs L CR) Hc L' cs' CP). Qed.

End CEIL.
