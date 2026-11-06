(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import STree Malloc MallocCtrl KInv
  MI_Tree MI_Inv MI_Kit MI_Arith MI_List MI_Geom MI_Ext MI_Ext2 MI_Shadow MI_Pres1 MI_Pres2 MI_Read
  MI_WFree MI_WFree2 MI_WNtf2 MI_WGroup MI_TF2 MI_WEnframe MI_WEnframe2 MI_WSlot MI_WMalloc MI_Ledger MI_Cnt
  Realloc ReallocProto ReallocKeep MI_WRealloc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Lemma TW_wr8 st q v (P : aptr -> Prop) : TW st P -> P q -> TW (wr8 q v st) P.
Proof.
  intros H Hq rid sh o w t Hsh Hc Ht.
  unfold wr8, upd_shadow in Hsh. cbn in Hsh. change (s_tick (wr8 q v st)) with (s_tick st) in Ht.
  destruct (N.eqb_spec rid (fst q)) as [->|NE].
  - rewrite lookup_insert_eq in Hsh. injection Hsh as <-. cbn in Hc.
    destruct (Z.eq_dec o (snd q)) as [->|NEo].
    + replace (fst q, snd q) with q by (destruct q; reflexivity). exact Hq.
    + rewrite lookup_insert_ne in Hc by congruence.
      destruct (get_shadow_cells_some st (fst q) o (w, t) Hc) as (sh0 & Hs0 & Hc0).
      exact (H (fst q) sh0 o w t Hs0 Hc0 Ht).
  - rewrite lookup_insert_ne in Hsh by congruence. exact (H rid sh o w t Hsh Hc Ht).
Qed.

Lemma blk_region X st L BL LS k : INVL X st L BL LS -> In k BL ->
  exists r, s_regions st !! fst (bslot k) = Some r /\ r_kind r = RKGroup.
Proof.
  intros INV Hk. pose proof INV as (IR & IA & IM & IL & IG & IS & ISH).
  destruct (is_blocks _ _ _ IS k Hk) as (m & i & Hs & _).
  destruct (is_valid _ _ _ IS _ _ _ Hs) as ([b Hb] & _ & Es).
  rewrite (slot_start'_eq _ _ _ IM _ _ i Hb) in Es. rewrite Es. cbn [fst].
  destruct Hb as [ai Hb]. exact (ig_region _ _ _ IG _ _ Hb).
Qed.

Lemma In_bl_remove (k : blk) c BL : In k (bl_remove c BL) -> In k BL.
Proof. induction BL as [|b BL IH]; cbn; [tauto|]. destruct (aptr_eqb (bslot b) c); cbn; intros H; [right; exact H|]. destruct H as [H|H]; [left; exact H| right; apply IH; exact H]. Qed.

Lemma bl_remove_neq (k : blk) c BL : NoDup (map bslot BL) -> In k (bl_remove c BL) -> bslot k <> c.
Proof.
  induction BL as [|b BL IH]; cbn; [tauto|]. intros ND H. apply NoDup_cons in ND as [N1 N2].
  destruct (aptr_eqb_spec (bslot b) c) as [E|NE].
  - intros Ek. apply N1. rewrite E, <- Ek. apply list_elem_of_In. apply in_map. exact H.
  - destruct H as [<-|H]; [exact NE| apply IH; assumption].
Qed.

(* [comment removed for export] *)
Lemma blk_in_63_region X st L BL LS bm g k :
  INVL X st L BL LS -> hosts st bm g -> m_sizeclass (MR st g) = 63 ->
  In k BL -> fst (bslot k) = fst bm -> bslot k = (fst bm, sstart (MR st g) 0).
Proof.
  intros INV Hg SC Hk Hf. pose proof INV as (IR & IA & IM & IL & IG & IS & ISH).
  destruct (is_blocks _ _ _ IS k Hk) as (m' & i' & Hs & _ & _ & _).
  destruct (is_valid _ _ _ IS _ _ _ Hs) as ([b' Hb'] & Hi' & Es).
  rewrite (slot_start'_eq _ _ _ IM _ _ i' Hb') in Es. rewrite Es in Hf |- *. cbn [fst] in Hf.
  destruct (hosts_ok _ _ _ IG _ _ Hg) as (aig & _ & GOg).
  destruct (g_sc _ _ _ _ _ _ GOg) as [[? ?]|(_ & L0 & MLg & _)]; [lia|].
  destruct (Z.eq_dec (m_maplen (MR st m')) 0) as [ML|ML].
  - destruct (top_chain X st BL LS IM IG IS m' b' Hb' ML) as (t & j & cc & bt & Ha & Ht & MLt & Hft).
    pose proof (top_unique X st LS IG t g bt bm Ht Hg MLt MLg ltac:(rewrite Hft; exact Hf)) as ->.
    destruct (anc_facts X st BL LS IM IG IS _ _ _ _ Ha) as (bm' & bp & _ & _ & _ & _ & _ & _ & _ & _ & SC'). lia.
  - pose proof (top_unique X st LS IG m' g b' bm Hb' Hg ML MLg Hf) as ->.
    pose proof (hosts_inj X st LS IM _ _ _ Hb' Hg) as ->. f_equal. f_equal. lia.
Qed.

Section MAIN.
Variables (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr) (c : cptr) (off n0 n : Z).
Hypothesis INV : INVL x0 st L BL LS.
Hypothesis Hk : In ((c, off), n0) BL.
Hypothesis Hn : 0 <= n.
Hypothesis OV : size_overflows n = false.
Let st0 := set_tick (N.succ (s_tick st)) st.

Lemma m_INV0 : INVL x0 st0 L BL LS. Proof. apply INVL_set_tick; [cbn; lia| exact INV]. Qed.
Lemma m_TF0 : TF0 st0. Proof. apply TF0_tick_new; [exact (TKS_of _ _ _ _ _ INV)| cbn; lia]. Qed.

Variables (m bm : aptr) (i ai : Z) (a : aptr) (ar : area) (ka : Z).
Hypothesis BF : blk_facts st0 c off n0 m bm i ai a ar ka.
Let p : aptr := aadd c (UNIT * off).
Let stride := get_stride (MR st0 m).
Let X1 := xpend x0 (Some c).
Let BL1 := bl_remove c BL.

Lemma m_hosts : hosts st0 bm m. Proof. exists ai. exact (bf_hosts _ _ _ _ _ _ _ _ _ _ _ BF). Qed.
Lemma m_c : c = (fst bm, sstart (MR st0 m) i). Proof. exact (bf_c _ _ _ _ _ _ _ _ _ _ _ BF). Qed.
Lemma m_slot : slot_start' (MR st0 m) i = c.
Proof. rewrite m_c. exact (slot_start'_eq _ _ _ (proj1 (proj2 (proj2 m_INV0))) _ _ i m_hosts). Qed.
Lemma m_gbase : gbase (MR st0 m) = bm. Proof. exact (hosts_gbase _ _ _ (proj1 (proj2 (proj2 m_INV0))) _ _ m_hosts). Qed.

(* [comment removed for export] *)
Lemma m_INV1 : INVL X1 st0 L BL1 LS.
Proof.
  pose proof m_INV0 as INV0.
  change c with (bslot ((c, off), n0)).
  apply (INVL_remove_block x0 st0 st0 L BL LS ((c, off), n0) INV0 Hk eq_refl (ctrl_eq_refl _) eq_refl).
  - intros; reflexivity.
  - exact (DOMS_of _ _ _ _ _ INV0).
  - exact (TKS_of _ _ _ _ _ INV0).
Qed.

(* [comment removed for export] *)
Lemma inplace_INVL : UNIT * off + n <= stride - IB ->
  m_sizeclass (MR st0 m) < 48 ->
  exists LS', INVL x0 (havoc p n (set_size p (aadd c (stride - IB)) n i st0)) L (((c, off), n) :: BL1) LS'.
Proof.
  intros FIT SC.
  pose proof m_INV0 as INV0. pose proof m_INV1 as INV1. pose proof m_hosts as Hm. pose proof m_c as Ec.
  pose proof (bf_shadow _ _ _ _ _ _ _ _ _ _ _ BF) as SH. unfold blk_shadow_ok in SH. cbn [bslot boff bsize fst snd] in SH.
  rewrite m_gbase in SH. destruct SH as (K4 & K3 & K2 & K1 & Q & _).
  destruct (hosts_ok _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 INV0))))) _ _ Hm) as (ai' & Hb & GO).
  assert (RES32 : stride - IB - UNIT * off - n < 2 ^ 32).
  { destruct (g_stride _ _ _ _ _ _ GO SC) as (_ & _ & LT). unfold cnt_of in LT. fold stride in LT.
    pose proof (bf_i _ _ _ _ _ _ _ _ _ _ _ BF) as Hi. pose proof (bf_stride _ _ _ _ _ _ _ _ _ _ _ BF) as [S16 _]. fold stride in S16.
    assert (S1 : stride * 1 <= stride * (m_last_idx (MR st0 m) + 1)) by (apply Z.mul_le_mono_nonneg_l; unfold UNIT in S16; lia).
    pose proof (bf_off _ _ _ _ _ _ _ _ _ _ _ BF). unfold IB, UNIT in *. lia. }
  exists LS.
  rewrite Ec in K4, K2, K1, Q. cbn [fst snd] in K4, K2, K1, Q.
  assert (EQ : (snd (aadd (fst bm, sstart (MR st0 m) i) (UNIT * off)) - (snd bm + UNIT)) / UNIT
               = (sstart (MR st0 m) i + UNIT * off - snd bm - UNIT) / UNIT) by (cbn [snd aadd]; f_equal; lia).
  destruct (resize_INVL X1 st0 L BL1 LS m bm i off n INV1 Hm (bf_i _ _ _ _ _ _ _ _ _ _ _ BF)
              ltac:(rewrite <- Ec; reflexivity) (bf_off _ _ _ _ _ _ _ _ _ _ _ BF) Hn FIT RES32) as (INV2 & _ & _).
  - cbn [fst snd aadd]. exact K4.
  - rewrite EQ. cbn [fst snd aadd]. exact K2.
  - rewrite EQ. cbn [fst snd aadd]. exact K1.
  - rewrite EQ. exact Q.
  - apply TF0_TW. exact m_TF0.
  - unfold stf2 in INV2. rewrite <- (rs_set_size st0 m bm i off n) in INV2. rewrite <- Ec in INV2.
    exact INV2.
Qed.

(* [comment removed for export] *)
Lemma bigsame_INVL : m_sizeclass (MR st0 m) = 63 -> UNIT * off + n <= stride - IB -> stride - IB - UNIT * off - n < 2 ^ 32 ->
  exists LS', INVL x0 (havoc p n (set_size p (aadd c (stride - IB)) n i (wr8 (aadd c (stride - IB)) 0 st0))) L (((c, off), n) :: BL1) LS'.
Proof.
  intros SC FIT RES32.
  pose proof m_INV0 as INV0. pose proof m_hosts as Hm. pose proof m_c as Ec.
  pose proof (bf_shadow _ _ _ _ _ _ _ _ _ _ _ BF) as SH. unfold blk_shadow_ok in SH. cbn [bslot boff bsize fst snd] in SH.
  rewrite m_gbase in SH. destruct SH as (K4 & K3 & K2 & K1 & Q & _).
  pose proof (bf_hdr0 _ _ _ _ _ _ _ _ _ _ _ BF) as H0. rewrite sstart_succ in H0. fold stride in H0.
  pose proof (bf_i _ _ _ _ _ _ _ _ _ _ _ BF) as Hi. pose proof (bf_off _ _ _ _ _ _ _ _ _ _ _ BF) as Hoff.
  pose proof (bf_stride _ _ _ _ _ _ _ _ _ _ _ BF) as [S16 _]. fold stride in S16.
  set (e := aadd c (stride - IB)).
  set (st1 := wr8 e 0 st0).
  assert (Ee : e = (fst bm, sstart (MR st0 m) i + stride - IB)) by (unfold e; rewrite Ec; unfold aadd; cbn [fst snd]; f_equal; lia).
  assert (TK0 : TKS st0 (s_tick st0)) by exact (TKS_of _ _ _ _ _ INV0).
  assert (RDe : forall r, cell_read (get_shadow st1 (fst r)) (snd r) = cell_read (get_shadow st0 (fst r)) (snd r)).
  { intros r. destruct (aptr_eqb_spec r e) as [->|NE].
    - unfold st1. rewrite (cell_read_wr8_same e 0 st0 (sh_ticks_of _ _ TK0)). symmetry. rewrite Ee. cbn [fst snd]. exact H0.
    - unfold st1. apply cell_read_wr8_other. exact NE. }
  assert (REG : exists rg, s_regions st0 !! fst bm = Some rg /\ r_kind rg = RKGroup).
  { destruct Hm as [ai0 Hb]. exact (ig_region _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 INV0))))) _ _ Hb). }
  assert (INV1 : INVL X1 st1 L BL1 LS).
  { change c with (bslot ((c, off), n0)). unfold X1, BL1. change c with (bslot ((c, off), n0)).
    apply (INVL_remove_block x0 st0 st1 L BL LS ((c, off), n0) INV0 Hk eq_refl (ctrl_eq_wr8 _ _ _) eq_refl).
    - intros; apply RDe.
    - unfold st1. apply (wr8_dom st0 e 0 (fun rid => exists rg, s_regions st0 !! rid = Some rg /\ r_kind rg = RKGroup)); [exact (DOMS_of _ _ _ _ _ INV0)|].
      rewrite Ee. cbn [fst]. exact REG.
    - unfold st1. apply wr8_tks; [cbn; lia| exact TK0]. }
  assert (Hm1 : hosts st1 bm m) by exact Hm.
  assert (MR1 : MR st1 m = MR st0 m) by reflexivity.
  exists LS.
  rewrite Ec in K4, K2, K1, Q. cbn [fst snd] in K4, K2, K1, Q.
  assert (EQ : (snd (aadd (fst bm, sstart (MR st1 m) i) (UNIT * off)) - (snd bm + UNIT)) / UNIT
               = (sstart (MR st0 m) i + UNIT * off - snd bm - UNIT) / UNIT) by (change (MR st1 m) with (MR st0 m); cbn [snd aadd]; f_equal; lia).
  destruct (resize_INVL X1 st1 L BL1 LS m bm i off n INV1 Hm1 Hi
              ltac:(rewrite <- Ec; reflexivity) Hoff Hn FIT RES32) as (INV2 & _ & _).
  - unfold known, SHd. cbn [fst snd aadd]. rewrite (RDe (fst bm, _)). exact K4.
  - rewrite EQ. unfold known, SHd. cbn [fst snd aadd]. rewrite (RDe (fst bm, _)). exact K2.
  - rewrite EQ. unfold known, SHd. cbn [fst snd aadd]. rewrite (RDe (fst bm, _)). exact K1.
  - rewrite EQ. exact Q.
  - (* [comment removed for export] *)
    unfold st1. apply TW_wr8; [apply TF0_TW; exact m_TF0|].
    rewrite Ee. cbn [fst snd aadd]. change (MR (wr8 _ _ st0) m) with (MR st0 m). unfold IB, UNIT in *. lia.
  - unfold stf2 in INV2. rewrite <- (rs_set_size st1 m bm i off n) in INV2. rewrite MR1, <- Ec in INV2. exact INV2.
Qed.

(* [comment removed for export] *)
Lemma m63_facts : m_sizeclass (MR st0 m) = 63 ->
  i = 0 /\ m_last_idx (MR st0 m) = 0 /\ snd bm = 0 /\ m_maplen (MR st0 m) <> 0 /\ 0 <= m_maplen (MR st0 m)
  /\ stride = m_maplen (MR st0 m) * 4096 - UNIT
  /\ (exists rg, s_regions st0 !! fst bm = Some rg /\ r_kind rg = RKGroup /\ m_maplen (MR st0 m) * 4096 = round_up_pg (r_len rg))
  /\ c = (fst bm, snd bm + UNIT) /\ p = aadd bm (UNIT + UNIT * off).
Proof.
  intros SC. pose proof m_INV0 as INV0. pose proof m_hosts as Hm. pose proof m_c as Ec.
  destruct (hosts_ok _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 INV0))))) _ _ Hm) as (ai' & Hb & GO).
  destruct (g_sc _ _ _ _ _ _ GO) as [[? ?]|(_ & L0 & ML & _)]; [lia|].
  pose proof (bf_i _ _ _ _ _ _ _ _ _ _ _ BF) as Hi. assert (I0 : i = 0) by lia.
  destruct (g_top _ _ _ _ _ _ GO ML) as (B0 & rg & Hrg & Hk' & Hml & _).
  pose proof (g_maplen _ _ _ _ _ _ GO) as MLG.
  assert (STR : stride = m_maplen (MR st0 m) * 4096 - UNIT).
  { unfold stride, get_stride. fold (MR st0 m). rewrite L0, (proj2 (Z.eqb_neq _ _) ML). reflexivity. }
  assert (EC : c = (fst bm, snd bm + UNIT)) by (rewrite Ec, I0; unfold sstart; rewrite m_gbase; f_equal; lia).
  repeat split; auto.
  - exists rg. auto.
  - unfold p. rewrite EC. unfold aadd. cbn [fst snd]. f_equal. lia.
Qed.


(* [comment removed for export] *)
Lemma mremap_ok_INVL z rg :
  m_sizeclass (MR st0 m) = 63 ->
  s_regions st0 !! fst bm = Some rg ->
  let needed := round_up_pg (n + UNIT * off + UNIT + IB) in
  mremap_answer_ok (live_ranges st0) (r_base rg) (m_maplen (MR st0 m) * 4096) needed z = true ->
  is_err z = false -> needed < PTRDIFF_MAX -> m_maplen (MR st0 m) * 4096 <> needed ->
  let st' := fst (realloc_big_tail (remap_region (fst bm) m z needed st0) bm (UNIT * off) i needed n) in
  INVL x0 st' (KInv.set_groups ((z, needed) :: g_remove (r_base rg) (ld_groups L)) L) (((c, off), n) :: BL1) LS
  /\ s_secret st' = s_secret st0
  /\ (forall rid' x, rid' <> fst bm -> s_regions st' !! rid' = Some x <-> s_regions st0 !! rid' = Some x)
  /\ s_regions st' !! fst bm = Some (mkRegion RKGroup z needed).
Proof.
  intros SC63 Hrg needed Hz EZ SMALL NEN st'.
  pose proof m_INV0 as INV0. pose proof m_hosts as Hm. pose proof m_c as Ec.
  pose proof (bf_i _ _ _ _ _ _ _ _ _ _ _ BF) as Hi. pose proof (bf_off _ _ _ _ _ _ _ _ _ _ _ BF) as Hoff.
  destruct (m63_facts SC63) as (I0 & L0 & B0 & ML & MLG & STR & (rg' & Hrg' & Hkrg & Hml) & EC & EP).
  rewrite Hrg in Hrg'. injection Hrg' as <-.
  pose proof (round_up_pg_spec (n + UNIT * off + UNIT + IB)) as [RU1 RU2]. fold needed in RU1, RU2.
  assert (N0 : 0 < needed).
  { enough (MMAP_THRESHOLD <= n \/ 0 <= n) by (unfold UNIT, IB, MMAP_THRESHOLD in *; lia). right; exact Hn. }
      pose proof m_INV1 as INV1.
      assert (HO : x_orph X1 = None) by reflexivity.
      assert (HPc : x_pend X1 = Some (fst bm, sstart (MR st0 m) 0)) by (unfold X1; cbn; rewrite Ec, I0; reflexivity).
      assert (OLD : r_base (default (mkRegion RKGroup 0 0) (s_regions st0 !! fst bm)) = r_base rg) by (rewrite Hrg; reflexivity).
      destruct (remap_INVL X1 st0 L BL1 LS m bm z needed INV1 Hm SC63 HPc HO) as (INVr & Hmr & MRr & KN & SEC & REGS & REG & TWr).
      { rewrite OLD. exact Hz. }
      { exact EZ. }
      { unfold PTRDIFF_MAX, MMAP_THRESHOLD, UNIT, IB in *. lia. }
      { unfold PGSZ. exact RU2. }
      { lia. }
      { exact m_TF0. }
      rewrite OLD in INVr.
      set (str := wr8 (fst bm, needed - IB) 0 (remap_region (fst bm) m z needed st0)) in *.
      (* [comment removed for export] *)
      assert (ML' : m_maplen (MR str m) = needed / 4096).
      { rewrite MRr. cbn. pose proof (Z.div_pos needed 4096 ltac:(lia) ltac:(lia)).
        assert (needed / 4096 < 2 ^ 52) by (apply Z.div_lt_upper_bound; unfold PTRDIFF_MAX in *; lia).
        change (2 ^ 52 - 1) with (Z.ones 52). rewrite Z.land_ones by lia. apply Z.mod_small. lia. }
      assert (ND : needed / 4096 * 4096 = needed).
      { pose proof (Z.div_mod needed 4096 ltac:(lia)). unfold PGSZ in *. lia. }
      assert (STR' : get_stride (MR str m) = needed - UNIT).
      { unfold get_stride. rewrite ML'. replace (m_last_idx (MR str m)) with 0 by (rewrite MRr; cbn; lia).
        cbn [Z.eqb andb negb]. destruct (Z.eqb_spec (needed / 4096) 0) as [E0|NE0]; [exfalso; lia|]. cbn [negb andb]. lia. }
      assert (SS' : sstart (MR str m) 0 = UNIT).
      { unfold sstart. replace (gbase (MR str m)) with (gbase (MR st0 m)) by (rewrite MRr; reflexivity). rewrite m_gbase, B0, STR'. lia. }
      assert (Hi' : 0 <= 0 <= m_last_idx (MR str m)) by (rewrite MRr; cbn; lia).
      assert (FIT' : UNIT * off + n <= get_stride (MR str m) - IB) by (rewrite STR'; unfold UNIT, IB in *; lia).
      assert (RES32' : get_stride (MR str m) - IB - UNIT * off - n < 2 ^ 32) by (rewrite STR'; unfold UNIT, IB in *; lia).
      pose proof (bf_shadow _ _ _ _ _ _ _ _ _ _ _ BF) as SH. unfold blk_shadow_ok in SH. cbn [bslot boff bsize fst snd] in SH.
      rewrite m_gbase in SH. destruct SH as (K4 & K3 & K2 & K1 & Q & _). rewrite EC in K4, K2, K1, Q. cbn [fst snd] in K4, K2, K1, Q. rewrite B0 in K4, K2, K1, Q.
      assert (HPr : x_pend X1 = Some (fst bm, sstart (MR str m) 0)) by (rewrite SS', HPc; unfold sstart; rewrite m_gbase, B0; f_equal; f_equal; lia).
      destruct (resize_INVL X1 str (KInv.set_groups ((z, needed) :: g_remove (r_base rg) (ld_groups L)) L) BL1 LS m bm 0 off n INVr Hmr Hi' HPr Hoff Hn FIT' RES32') as (INV2 & CE2 & _).
      * rewrite SS'. cbn [fst snd aadd]. apply KN; [unfold UNIT, IB in *; lia|]. replace (UNIT + UNIT * off - 4) with (0 + UNIT + UNIT * off - 4) by lia. exact K4.
      * rewrite SS', B0. cbn [fst snd aadd]. replace ((UNIT + UNIT * off - (0 + UNIT)) / UNIT) with ((0 + UNIT + UNIT * off - 0 - UNIT) / UNIT) by (f_equal; lia).
        apply KN; [unfold UNIT, IB in *; lia|]. replace (UNIT + UNIT * off - 2) with (0 + UNIT + UNIT * off - 2) by lia. exact K2.
      * rewrite SS', B0. cbn [fst snd aadd]. replace ((UNIT + UNIT * off - (0 + UNIT)) / UNIT) with ((0 + UNIT + UNIT * off - 0 - UNIT) / UNIT) by (f_equal; lia).
        apply KN; [unfold UNIT, IB in *; lia|]. replace (UNIT + UNIT * off - 1) with (0 + UNIT + UNIT * off - 1) by lia. exact K1.
      * rewrite SS', B0. cbn [fst snd aadd]. replace ((UNIT + UNIT * off - (0 + UNIT)) / UNIT) with ((0 + UNIT + UNIT * off - 0 - UNIT) / UNIT) by (f_equal; lia). exact Q.
      * eapply TW_mono; [| exact TWr]. intros q ->. cbn [fst snd aadd]. rewrite SS'. unfold UNIT, IB in *. lia.
      * subst st'. unfold realloc_big_tail. cbn [fst].
        assert (ES : havoc (aadd bm (UNIT + UNIT * off)) n (set_size (aadd bm (UNIT + UNIT * off)) (aadd bm (needed - IB)) n i str)
                     = stf2 str m bm 0 off n).
        { unfold stf2. rewrite <- (rs_set_size str m bm 0 off n). rewrite SS', STR'.
          unfold aadd. cbn [fst snd]. rewrite B0, I0. rewrite !Z.add_0_l.
          replace (UNIT + (needed - UNIT - IB)) with (needed - IB) by lia. reflexivity. }
        replace (wr8 (aadd bm (needed - IB)) 0 (remap_region (fst bm) m z needed st0)) with str
          by (unfold str, aadd; cbn [fst snd]; rewrite B0, Z.add_0_l; reflexivity).
        rewrite ES. split; [| split; [| split]].
        -- unfold BL1 in INV2 |- *. rewrite SS' in INV2. replace (fst bm, UNIT) with c in INV2 by (rewrite EC, B0; f_equal; lia). exact INV2.
        -- rewrite (ce_secret _ _ CE2). exact SEC.
        -- intros rid' x NE. rewrite (ce_regions _ _ CE2). apply REGS. exact NE.
        -- rewrite (ce_regions _ _ CE2). exact REG.
Qed.

Theorem realloc_INVL_main :
  ftreeX L (realloc st (Some p) n) (RPOST BL c n).
Proof.
  pose proof m_INV0 as INV0. pose proof m_hosts as Hm. pose proof m_c as Ec. pose proof INV0 as (IR & IA & IM & IL & IG & IS & ISH).
  pose proof (bf_i _ _ _ _ _ _ _ _ _ _ _ BF) as Hi. pose proof (bf_off _ _ _ _ _ _ _ _ _ _ _ BF) as Hoff.
  pose proof (bf_stride _ _ _ _ _ _ _ _ _ _ _ BF) as [S16 SM]. fold stride in S16, SM.
  unfold realloc. rewrite OV. fold st0. unfold p.
  rewrite (realloc_hdr_eq st0 c off n0 m bm i ai a ar ka BF). cbn [xlift sbind].
  fold (MR st0 m). rewrite m_slot. fold stride.
  replace (snd (aadd c (stride - IB)) - snd (aadd c (UNIT * off))) with (stride - IB - UNIT * off) by (cbn [snd aadd]; lia).
  replace (snd (aadd c (UNIT * off)) - snd c) with (UNIT * off) by (cbn [snd aadd]; lia).
  destruct ((n <=? stride - IB - UNIT * off) && (n <? MMAP_THRESHOLD) && (m_sizeclass (MR st0 m) <=? size_to_class n + 1)) eqn:C1.
  { (* [comment removed for export] *)
    apply andb_prop in C1 as [C1 C13]. apply andb_prop in C1 as [C11 C12].
    apply Z.leb_le in C11. apply Z.ltb_lt in C12. apply Z.leb_le in C13.
    pose proof (size_to_class_ok n ltac:(lia)) as [SCR _].
    assert (SC48 : m_sizeclass (MR st0 m) < 48) by (destruct (bf_sc _ _ _ _ _ _ _ _ _ _ _ BF) as [[? _]| E63]; lia).
    cbn [ftreeX RPOST fst snd]. destruct (inplace_INVL ltac:(lia) SC48) as [LS' INV']. exists c, off, LS'. auto. }
  destruct ((48 <=? m_sizeclass (MR st0 m)) && (MMAP_THRESHOLD <=? n)) eqn:C2.
  2:{ exact (realloc_move_ft st0 L BL LS c off n0 n INV0 Hk Hn). }
  apply andb_prop in C2 as [C21 C22]. apply Z.leb_le in C21. apply Z.leb_le in C22.
  assert (SC63 : m_sizeclass (MR st0 m) = 63) by (destruct (bf_sc _ _ _ _ _ _ _ _ _ _ _ BF) as [[? ?]| E63]; lia).
  apply ftreeX_xguard; [apply Z.eqb_eq; exact SC63|].
  destruct (m63_facts SC63) as (I0 & L0 & B0 & ML & MLG & STR & (rg & Hrg & Hkrg & Hml) & EC & EP).
  change (default (0%N, 0) (m_mem (MR st0 m))) with (gbase (MR st0 m)). rewrite m_gbase.
  set (needed := round_up_pg (n + UNIT * off + UNIT + IB)).
  pose proof (round_up_pg_spec (n + UNIT * off + UNIT + IB)) as [RU1 RU2]. fold needed in RU1, RU2.
  assert (N0 : 0 < needed) by (unfold UNIT, IB, MMAP_THRESHOLD in *; lia).
  destruct (Z.eqb_spec (m_maplen (MR st0 m) * 4096) needed) as [EQN|NEN].
  { (* [comment removed for export] *)
    cbn [ftreeX RPOST fst snd].
    assert (FIT : UNIT * off + n <= stride - IB) by (rewrite STR; unfold UNIT, IB in *; lia).
    assert (RES32 : stride - IB - UNIT * off - n < 2 ^ 32) by (rewrite STR; unfold UNIT, IB in *; lia).
    destruct (bigsame_INVL SC63 FIT RES32) as [LS' INV']. exists c, off, LS'.
    assert (E1 : aadd bm (UNIT + UNIT * off) = aadd c (UNIT * off)) by (rewrite EC; unfold aadd; cbn [fst snd]; f_equal; lia).
    assert (E2 : aadd bm (needed - IB) = aadd c (stride - IB)) by (rewrite EC, STR, EQN; unfold aadd; cbn [fst snd]; f_equal; lia).
    unfold realloc_big_tail. rewrite E1, E2. cbn [fst snd]. split; [reflexivity|]. split; [exact Hoff|]. unfold p in INV'. exact INV'. }
  destruct (Z.leb_spec PTRDIFF_MAX needed) as [BIG|SMALL].
  { exact (realloc_move_ft st0 L BL LS c off n0 n INV0 Hk Hn). }
  (* [comment removed for export] *)
  assert (CONC : conc st0 bm = r_base rg) by (unfold conc, get_region; rewrite Hrg; lia).
  rewrite CONC.
  assert (OKEQ : forall z, mremap_answer_ok (lranges L) (r_base rg) (m_maplen (MR st0 m) * 4096) needed z
                         = mremap_answer_ok (live_ranges st0) (r_base rg) (m_maplen (MR st0 m) * 4096) needed z).
  { intros z. unfold mremap_answer_ok. rewrite !(ranges_free_eq x0 st0 L IR). reflexivity. }
  apply ftreeX_vis; [reflexivity| reflexivity| | |].
  - (* [comment removed for export] *)
    cbn [xevent_pre]. split; [exact (brk_quiet_of _ _ _ IR)|]. split; [reflexivity|]. split.
    + exists (r_len rg). split; [| exact Hml].
      assert (Hf : In (fst bm, rg) (List.filter (fun kr : N * region => match r_kind (snd kr) with RKGroup => true | _ => false end) (map_to_list (s_regions st0)))).
      { apply filter_In. split; [apply In_map_to_list_regions; exact Hrg| cbn; rewrite Hkrg; reflexivity]. }
      pose proof (in_map (fun kr : N * region => (r_base (snd kr), r_len (snd kr))) _ _ Hf) as Hin. cbn [snd] in Hin.
      exact (Permutation_in _ (Permutation_sym (ir_groups _ _ _ IR)) Hin).
    + unfold LEN_MAX, PTRDIFF_MAX, MMAP_THRESHOLD, PGSZ, UNIT, IB in *. repeat split; try lia.
  - (* [comment removed for export] *)
    intros z Hz. cbn [xanswer_ok xevent_post] in Hz |- *. rewrite OKEQ in Hz. rewrite Hz. cbn [negb].
    destruct (is_err z) eqn:EZ.
    + exact (realloc_move_ft st0 L BL LS c off n0 n INV0 Hk Hn).
    + cbn [ftreeX RPOST fst snd].
      pose proof m_INV1 as INV1.
      assert (HO : x_orph X1 = None) by reflexivity.
      assert (HPc : x_pend X1 = Some (fst bm, sstart (MR st0 m) 0)) by (unfold X1; cbn; rewrite Ec, I0; reflexivity).
      assert (OLD : r_base (default (mkRegion RKGroup 0 0) (s_regions st0 !! fst bm)) = r_base rg) by (rewrite Hrg; reflexivity).
      destruct (remap_INVL X1 st0 L BL1 LS m bm z needed INV1 Hm SC63 HPc HO) as (INVr & Hmr & MRr & KN & SEC & REGS & REG & TWr).
      { rewrite OLD. exact Hz. }
      { exact EZ. }
      { unfold PTRDIFF_MAX, MMAP_THRESHOLD, UNIT, IB in *. lia. }
      { unfold PGSZ. exact RU2. }
      { lia. }
      { exact m_TF0. }
      rewrite OLD in INVr.
      set (str := wr8 (fst bm, needed - IB) 0 (remap_region (fst bm) m z needed st0)) in *.
      (* [comment removed for export] *)
      assert (ML' : m_maplen (MR str m) = needed / 4096).
      { rewrite MRr. cbn. pose proof (Z.div_pos needed 4096 ltac:(lia) ltac:(lia)).
        assert (needed / 4096 < 2 ^ 52) by (apply Z.div_lt_upper_bound; unfold PTRDIFF_MAX in *; lia).
        change (2 ^ 52 - 1) with (Z.ones 52). rewrite Z.land_ones by lia. apply Z.mod_small. lia. }
      assert (ND : needed / 4096 * 4096 = needed).
      { pose proof (Z.div_mod needed 4096 ltac:(lia)). unfold PGSZ in *. lia. }
      assert (STR' : get_stride (MR str m) = needed - UNIT).
      { unfold get_stride. rewrite ML'. replace (m_last_idx (MR str m)) with 0 by (rewrite MRr; cbn; lia).
        cbn [Z.eqb andb negb]. destruct (Z.eqb_spec (needed / 4096) 0) as [E0|NE0]; [exfalso; lia|]. cbn [negb andb]. lia. }
      assert (SS' : sstart (MR str m) 0 = UNIT).
      { unfold sstart. replace (gbase (MR str m)) with (gbase (MR st0 m)) by (rewrite MRr; reflexivity). rewrite m_gbase, B0, STR'. lia. }
      assert (Hi' : 0 <= 0 <= m_last_idx (MR str m)) by (rewrite MRr; cbn; lia).
      assert (FIT' : UNIT * off + n <= get_stride (MR str m) - IB) by (rewrite STR'; unfold UNIT, IB in *; lia).
      assert (RES32' : get_stride (MR str m) - IB - UNIT * off - n < 2 ^ 32) by (rewrite STR'; unfold UNIT, IB in *; lia).
      pose proof (bf_shadow _ _ _ _ _ _ _ _ _ _ _ BF) as SH. unfold blk_shadow_ok in SH. cbn [bslot boff bsize fst snd] in SH.
      rewrite m_gbase in SH. destruct SH as (K4 & K3 & K2 & K1 & Q & _). rewrite EC in K4, K2, K1, Q. cbn [fst snd] in K4, K2, K1, Q. rewrite B0 in K4, K2, K1, Q.
      assert (HPr : x_pend X1 = Some (fst bm, sstart (MR str m) 0)) by (rewrite SS', HPc; unfold sstart; rewrite m_gbase, B0; f_equal; f_equal; lia).
      destruct (resize_INVL X1 str _ BL1 LS m bm 0 off n INVr Hmr Hi' HPr Hoff Hn FIT' RES32') as (INV2 & _ & _).
      * rewrite SS'. cbn [fst snd aadd]. apply KN; [unfold UNIT, IB in *; lia|]. replace (UNIT + UNIT * off - 4) with (0 + UNIT + UNIT * off - 4) by lia. exact K4.
      * rewrite SS', B0. cbn [fst snd aadd]. replace ((UNIT + UNIT * off - (0 + UNIT)) / UNIT) with ((0 + UNIT + UNIT * off - 0 - UNIT) / UNIT) by (f_equal; lia).
        apply KN; [unfold UNIT, IB in *; lia|]. replace (UNIT + UNIT * off - 2) with (0 + UNIT + UNIT * off - 2) by lia. exact K2.
      * rewrite SS', B0. cbn [fst snd aadd]. replace ((UNIT + UNIT * off - (0 + UNIT)) / UNIT) with ((0 + UNIT + UNIT * off - 0 - UNIT) / UNIT) by (f_equal; lia).
        apply KN; [unfold UNIT, IB in *; lia|]. replace (UNIT + UNIT * off - 1) with (0 + UNIT + UNIT * off - 1) by lia. exact K1.
      * rewrite SS', B0. cbn [fst snd aadd]. replace ((UNIT + UNIT * off - (0 + UNIT)) / UNIT) with ((0 + UNIT + UNIT * off - 0 - UNIT) / UNIT) by (f_equal; lia). exact Q.
      * eapply TW_mono; [| exact TWr]. intros q ->. cbn [fst snd aadd]. rewrite SS'. unfold UNIT, IB in *. lia.
      * exists c, off, LS. split; [| split; [exact Hoff|]].
        -- rewrite EC, B0. unfold aadd. cbn [fst snd]. f_equal. lia.
        -- unfold realloc_big_tail. cbn [fst].
           unfold stf2 in INV2. rewrite <- (rs_set_size str m bm 0 off n) in INV2. rewrite SS', STR' in INV2.
           unfold BL1 in INV2. unfold aadd in INV2 |- *. cbn [fst snd] in INV2 |- *.
           rewrite EC, B0 in INV2 |- *. rewrite I0. rewrite !Z.add_0_l in INV2 |- *. cbn [fst snd] in INV2 |- *.
           replace (UNIT + (needed - UNIT - IB)) with (needed - IB) in INV2 by lia.
           first [exact INV2 | match goal with |- INVL _ ?S _ ?B _ => idtac "GOAL" S B end; match type of INV2 with INVL _ ?S _ ?B _ => idtac "INV2" S B end; fail].
  - (* [comment removed for export] *)
    intros z Hz. cbn [xanswer_ok] in Hz. rewrite OKEQ in Hz. rewrite Hz. exact I.
Qed.

(* [comment removed for export] *)
Theorem realloc_keep_INVL_main st' :
  realloc_keep st p n st' ->
  exists L' LS', INVL x0 st' L' (((c, off), n) :: BL1) LS'
    /\ ld_resv L' = ld_resv L /\ ld_live L' = ld_live L /\ s_secret st' = s_secret st
    /\ (forall k r', In k BL1 -> s_regions st' !! fst (bslot k) = Some r' -> s_regions st !! fst (bslot k) = Some r')
    /\ (exists r', s_regions st' !! fst c = Some r').
Proof.
  intros (OV' & g & idx & old & HDR & CASES).
  pose proof m_INV0 as INV0. pose proof m_hosts as Hm. pose proof m_c as Ec. pose proof INV0 as (IR & IA & IM & IL & IG & IS & ISH).
  pose proof (bf_i _ _ _ _ _ _ _ _ _ _ _ BF) as Hi. pose proof (bf_off _ _ _ _ _ _ _ _ _ _ _ BF) as Hoff.
  pose proof (bf_stride _ _ _ _ _ _ _ _ _ _ _ BF) as [S16 SM]. fold stride in S16, SM.
  fold st0 in HDR, CASES. unfold p in HDR. rewrite (realloc_hdr_eq st0 c off n0 m bm i ai a ar ka BF) in HDR.
  injection HDR as <- <- <-.
  unfold rk_of in CASES. cbn [rk_st0 rk_avail rk_e rk_maplen4096 rk_needed rk_gmem rk_base rk_start] in CASES.
  fold st0 in CASES. fold (MR st0 m) in CASES. rewrite m_slot in CASES. fold stride in CASES.
  replace (snd (aadd c (stride - IB)) - snd p) with (stride - IB - UNIT * off) in CASES by (unfold p; cbn [snd aadd]; lia).
  replace (snd p - snd c) with (UNIT * off) in CASES by (unfold p; cbn [snd aadd]; lia).
  change (default (0%N, 0) (m_mem (MR st0 m))) with (gbase (MR st0 m)) in CASES. rewrite m_gbase in CASES.
  assert (REGc : forall stx Lx BLx LSx, INVL x0 stx Lx (((c, off), n) :: BLx) LSx -> exists r', s_regions stx !! fst c = Some r').
  { intros stx Lx BLx LSx INVx. destruct (blk_region _ _ _ _ _ ((c, off), n) INVx ltac:(left; reflexivity)) as (r' & Hr' & _). exists r'. exact Hr'. }
  assert (SEC0 : s_secret st0 = s_secret st) by reflexivity.
  assert (REG0 : s_regions st0 = s_regions st) by reflexivity.
  destruct CASES as [[C1 ->]|(C1 & C2 & SC63 & BIG)].
  - (* [comment removed for export] *)
    apply andb_prop in C1 as [C1 C13]. apply andb_prop in C1 as [C11 C12].
    apply Z.leb_le in C11. apply Z.ltb_lt in C12. apply Z.leb_le in C13.
    pose proof (size_to_class_ok n ltac:(lia)) as [SCR _].
    assert (SC48 : m_sizeclass (MR st0 m) < 48) by (destruct (bf_sc _ _ _ _ _ _ _ _ _ _ _ BF) as [[? _]| E63]; lia).
    destruct (inplace_INVL ltac:(lia) SC48) as [LS' INV']. fold p.
    destruct (stf2_ctrl st0 m bm i off n) as [CE _].
    assert (ES : havoc p n (set_size p (aadd c (stride - IB)) n i st0) = stf2 st0 m bm i off n).
    { unfold stf2. rewrite <- (rs_set_size st0 m bm i off n). rewrite <- Ec. reflexivity. }
    exists L, LS'. split; [exact INV'|]. split; [reflexivity|]. split; [reflexivity|].
    rewrite ES. split; [rewrite (ce_secret _ _ CE); exact SEC0|]. split.
    + intros k r' _ H. rewrite (ce_regions _ _ CE), REG0 in H. exact H.
    + rewrite <- ES. eapply REGc. exact INV'.
  - apply andb_prop in C2 as [C21 C22]. apply Z.leb_le in C21. apply Z.leb_le in C22.
    destruct (m63_facts SC63) as (I0 & L0 & B0 & ML & MLG & STR & (rg & Hrg & Hkrg & Hml) & EC & EP).
    set (needed := round_up_pg (n + UNIT * off + UNIT + IB)) in *.
    pose proof (round_up_pg_spec (n + UNIT * off + UNIT + IB)) as [RU1 RU2]. fold needed in RU1, RU2.
    destruct BIG as [[EQN ->]|(NEN & SMALL & z & Hz & EZ & ->)].
    + (* [comment removed for export] *)
      assert (FIT : UNIT * off + n <= stride - IB) by (rewrite STR; unfold UNIT, IB in *; lia).
      assert (RES32 : stride - IB - UNIT * off - n < 2 ^ 32) by (rewrite STR; unfold UNIT, IB in *; lia).
      destruct (bigsame_INVL SC63 FIT RES32) as [LS' INV'].
      assert (E1 : aadd bm (UNIT + UNIT * off) = aadd c (UNIT * off)) by (rewrite EC; unfold aadd; cbn [fst snd]; f_equal; lia).
      assert (E2 : aadd bm (needed - IB) = aadd c (stride - IB)) by (rewrite EC, STR, EQN; unfold aadd; cbn [fst snd]; f_equal; lia).
      unfold realloc_big_tail. rewrite E1, E2. cbn [fst snd]. fold p.
      assert (CE : ctrl_eq st0 (havoc p n (set_size p (aadd c (stride - IB)) n i (wr8 (aadd c (stride - IB)) 0 st0)))).
      { eapply ctrl_eq_trans; [apply ctrl_eq_wr8|]. rewrite (set_size_eq p (aadd c (stride - IB)) n i).
        eapply ctrl_eq_trans; [apply (proj1 (wrs_ctrl (ss_list p (aadd c (stride - IB)) n i) _))| apply (proj1 (havoc_ctrl _ _ _))]. }
      exists L, LS'. split; [exact INV'|]. split; [reflexivity|]. split; [reflexivity|].
      split; [rewrite (ce_secret _ _ CE); exact SEC0|]. split.
      * intros k r' _ H. rewrite (ce_regions _ _ CE), REG0 in H. exact H.
      * eapply REGc. exact INV'.
    + (* [comment removed for export] *)
      unfold conc, get_region in Hz. rewrite Hrg, B0, Z.add_0_r in Hz.
      destruct (mremap_ok_INVL z rg SC63 Hrg Hz EZ SMALL ltac:(lia)) as (INV' & SEC' & REGS' & REG').
      eexists _, LS. split; [exact INV'|]. split; [reflexivity|]. split; [reflexivity|].
      split; [rewrite SEC'; exact SEC0|]. split.
      * intros k r' Hk' H. assert (NE : fst (bslot k) <> fst bm).
        { intros Ef. unfold BL1 in Hk'.
          pose proof (blk_in_63_region _ _ _ _ _ _ _ _ INV0 Hm SC63 (In_bl_remove _ _ _ Hk') Ef) as Eb.
          apply (bl_remove_neq k c BL (is_nodup _ _ _ IS) Hk'). rewrite Eb, EC, B0. unfold sstart. rewrite m_gbase, B0, ?Z.mul_0_r. f_equal; lia. }
        rewrite <- REG0. apply (proj1 (REGS' _ _ NE)). exact H.
      * rewrite EC. cbn [fst]. eexists. exact REG'.
Qed.
End MAIN.

(* [comment removed for export] *)
Theorem realloc_INVL st L BL LS c off n0 n :
  INVL x0 st L BL LS -> In ((c, off), n0) BL -> 0 <= n ->
  ftreeX L (realloc st (Some (aadd c (UNIT * off))) n) (RPOST BL c n).
Proof.
  intros INV Hk Hn.
  destruct (size_overflows n) eqn:OV.
  { unfold realloc. rewrite OV. cbn [ftreeX RPOST fst snd]. exists LS. exact INV. }
  destruct (block_facts x0 (set_tick (N.succ (s_tick st)) st) L BL LS (m_INV0 st L BL LS INV) c off n0 Hk)
    as (m & bm & i & ai & a & ar & ka & BF).
  exact (realloc_INVL_main st L BL LS c off n0 n INV Hk Hn OV m bm i ai a ar ka BF).
Qed.

(* [comment removed for export] *)
Theorem realloc_null_INVL st L BL LS n :
  INVL x0 st L BL LS -> 0 <= n ->
  ftreeX L (realloc st None n) (fun L' r =>
    ld_live L' = ld_live L /\ GP st (fst r) /\
    match snd r with
    | None => exists LS', INVL x0 (fst r) L' BL LS'
    | Some p => exists c off LS', p = aadd c (UNIT * off) /\ 0 <= off <= 255
        /\ INVL x0 (fst r) L' (((c, off), n) :: BL) LS' /\ ~ In c (map bslot BL)
    end).
Proof. intros INV Hn. unfold realloc. apply (proj1 (ftreeX_xlift _ _ _)). exact (malloc_INVL st L BL LS n INV Hn). Qed.

(* [comment removed for export] *)
Theorem realloc_keep_INVL st L BL LS c off n0 n st' :
  INVL x0 st L BL LS -> In ((c, off), n0) BL -> 0 <= n ->
  realloc_keep st (aadd c (UNIT * off)) n st' ->
  exists L' LS', INVL x0 st' L' (((c, off), n) :: bl_remove c BL) LS'
    /\ ld_resv L' = ld_resv L /\ ld_live L' = ld_live L /\ s_secret st' = s_secret st
    /\ (forall k r', In k (bl_remove c BL) -> s_regions st' !! fst (bslot k) = Some r' -> s_regions st !! fst (bslot k) = Some r')
    /\ (exists r', s_regions st' !! fst c = Some r').
Proof.
  intros INV Hk Hn RK.
  destruct (block_facts x0 (set_tick (N.succ (s_tick st)) st) L BL LS (m_INV0 st L BL LS INV) c off n0 Hk)
    as (m & bm & i & ai & a & ar & ka & BF).
  exact (realloc_keep_INVL_main st L BL LS c off n0 n INV Hk Hn m bm i ai a ar ka BF st' RK).
Qed.
End RC__1.
