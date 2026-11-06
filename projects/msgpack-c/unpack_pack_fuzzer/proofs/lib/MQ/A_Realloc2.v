(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc Require Import STree Malloc MallocCtrl KInv MI_Tree MI_Inv MI_Kit MI_Arith MI_Geom MI_Ext MI_Cnt MI_Pres2 MI_WFree2 MI_WGroup MI_WMalloc MI_WFree MI_Sim MI_Contracts MI_Ledger Realloc MI_Realloc2.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ Require Import Prog.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ Require Import A_MallocRep A_MallocTree A_MallocBlocks A_MallocFacts_B.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ Require A_MallocFacts_inv2 A_MallocFacts_inv3.

Set Keyed Unification.
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib Require Import CeilLia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section CEIL.
Context {CLG : OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.Ceiling.ceiling}.

Section REALLOC2.
Variables (resv : list (Z * Z)) (st : mstate) (LB : list block) (bp : bptr) (A old : Z).
Hypothesis AR : AREACH_from resv st LB.
Hypothesis Hb : In (bp, A, old) LB.
Let c : cptr := fst bp.
Variables (g bg : aptr) (idx : Z).
Hypothesis SL : s_slots st !! c = Some (g, idx).
Hypothesis HM : m_mem (MR st g) = Some bg.
Let stride := get_stride (MR st g).

Lemma realloc_ticks : ticks_ok st.
Proof. exact (ci_ticks _ _ (A_MallocFacts_inv3.areach_cinv_proof _ _ AR)). Qed.

Lemma realloc_nodup : List.NoDup (map blk_slot LB).
Proof. exact (ci_nodup _ _ (A_MallocFacts_inv3.areach_cinv_proof _ _ AR)). Qed.

Lemma realloc_bf : exists L LS BL off ai a ar ka,
  INVL x0 st L BL LS /\ CORR st LB BL /\ In ((c, off), old) BL /\ A = conc st c + UNIT * off
  /\ blk_facts st c off old g bg idx ai a ar ka.
Proof.
  destruct AR as (L & LS & BL & INV & LIVE & RESV & SEC & CR).
  destruct (A_MallocFacts_inv.Forall2_In_l _ _ _ _ CR Hb) as (k & Hk & (C1 & C2 & C3)).
  destruct k as [[c' off] n']. cbn [bslot boff bsize blk_slot blk_size blk_addr fst snd] in C1, C2, C3. subst n'.
  assert (Ec : c' = c) by (symmetry; exact C1). subst c'.
  destruct (block_facts x0 st L BL LS INV c off old Hk) as (g' & bg' & idx' & ai & a & ar & ka & BF).
  pose proof (bf_slot _ _ _ _ _ _ _ _ _ _ _ BF) as SL'. rewrite SL in SL'. assert (g' = g /\ idx' = idx) as [-> ->] by (split; congruence).
  pose proof (bf_mem _ _ _ _ _ _ _ _ _ _ _ BF) as HM'. rewrite HM in HM'. assert (bg' = bg) as -> by congruence.
  exists L, LS, BL, off, ai, a, ar, ka. split; [exact INV|]. split; [exact CR|]. split; [exact Hk|]. split; [exact C3| exact BF].
Qed.

Lemma realloc_nogrp : forall b' gh, s_groups st !! b' = Some gh -> fst b' = fst bg ->
  snd b' + 9 <= snd bg + 16 + stride * idx - 4 \/ snd bg + 16 + stride * idx + stride - 4 <= snd b'.
Proof.
  intros b' gh Hb' Hf. destruct realloc_bf as (L & LS & BL & off & ai & a & ar & ka & INV & CR & Hk & HA & BF).
  pose proof INV as (IR & IA & IM & IL & IG & IS & ISH).
  destruct (A_MallocFacts_inv2.hdr_hosts x0 st L BL LS INV b' gh Hb') as [m' Hm'].
  assert (Hm : hosts st bg g) by (exists ai; exact (bf_hosts _ _ _ _ _ _ _ _ _ _ _ BF)).
  pose proof (bf_i _ _ _ _ _ _ _ _ _ _ _ BF) as Hi. pose proof (bf_notH _ _ _ _ _ _ _ _ _ _ _ BF) as NH.
  rewrite (bf_c _ _ _ _ _ _ _ _ _ _ _ BF) in NH.
  pose proof (sstart_succ st g idx) as SS. pose proof (sstart0 x0 st LS IM _ _ Hm) as S0.
  pose proof (sstart_mono x0 st LS IG _ _ 0 idx Hm ltac:(lia)) as SM.
  pose proof (hosts_gbase x0 st LS IM _ _ Hm) as GB.
  destruct (sep_ghdr x0 st BL LS IM IG IS g bg idx Hm Hi NH m' b' Hm' Hf) as [X|X];
    unfold sstart in X, SS, S0, SM; rewrite ?GB in X, SS, S0, SM; fold stride in X, SS, S0, SM; unfold UNIT, IB in *; lia.
Qed.

Lemma realloc_slot_private : forall b', In b' LB -> blk_slot b' <> c ->
  forall x, conc st c - IB <= x < conc st c + stride - IB -> ~ (blk_addr b' <= x < blk_addr b' + blk_size b').
Proof.
  intros b' Hb' NE x Hx Hin. destruct realloc_bf as (L & LS & BL & off & ai & a & ar & ka & INV & CR & Hk & HA & BF).
  pose proof INV as (IR & IA & IM & IL & IG & IS & ISH).
  destruct (A_MallocFacts_inv2.LB_geo x0 st L BL LS INV LB CR b' Hb')
    as (c2 & off2 & n2 & m2 & bm2 & i2 & r2 & Hk2 & C1 & C2 & Hm2 & Hi2 & Ec2 & NH2 & Hr2 & Kr2 & Ea2 & Ho2 & Hn2 & Fit2).
  assert (Hm : hosts st bg g) by (exists ai; exact (bf_hosts _ _ _ _ _ _ _ _ _ _ _ BF)).
  pose proof (bf_i _ _ _ _ _ _ _ _ _ _ _ BF) as Hi. pose proof (bf_notH _ _ _ _ _ _ _ _ _ _ _ BF) as NH.
  pose proof (bf_c _ _ _ _ _ _ _ _ _ _ _ BF) as Ec. rewrite Ec in NH.
  destruct (ig_region _ _ _ IG _ _ (bf_hosts _ _ _ _ _ _ _ _ _ _ _ BF)) as (r & Hr & Kr).
  assert (CC : conc st c = r_base r + sstart (MR st g) idx).
  { rewrite Ec. unfold conc, get_region. cbn [fst snd]. rewrite Hr. reflexivity. }
  pose proof (sstart_succ st g idx) as SS. pose proof (sstart_succ st m2 i2) as SS2.
  rewrite C2 in Hin. rewrite Ea2 in Hin.
  destruct (N.eq_dec (fst bm2) (fst bg)) as [EF|NF].
  -
    rewrite EF, Hr in Hr2. assert (r2 = r) as -> by congruence.
    assert (NE' : m2 <> g \/ i2 <> idx).
    { destruct (aptr_eq_dec m2 g) as [->|]; [right| now left]. intros ->. apply NE. rewrite C1, Ec2, Ec, EF. reflexivity. }
    rewrite Ec2 in NH2.
    destruct (sep_ext x0 st BL LS IM IG IS g bg idx Hm Hi NH m2 bm2 i2 Hm2 EF Hi2 NE' NH2) as [X|X]; fold stride in SS; unfold UNIT, IB in *; lia.
  -
    destruct (A_MallocFacts_inv2.group_in_region x0 st L BL LS INV _ _ Hm) as (r' & Hr' & _ & B0 & GE).
    rewrite Hr in Hr'. assert (r' = r) as -> by congruence.
    destruct (A_MallocFacts_inv2.group_in_region x0 st L BL LS INV _ _ Hm2) as (r2' & Hr2' & _ & B02 & GE2).
    rewrite Hr2 in Hr2'. assert (r2' = r2) as -> by congruence.
    pose proof (sstart_mono x0 st LS IG _ _ (idx + 1) (m_last_idx (MR st g) + 1) Hm ltac:(lia)) as SM. rewrite <- gend_eq in SM.
    pose proof (sstart_mono x0 st LS IG _ _ (i2 + 1) (m_last_idx (MR st m2) + 1) Hm2 ltac:(lia)) as SM2. rewrite <- gend_eq in SM2.
    pose proof (sstart0 x0 st LS IM _ _ Hm) as S0. pose proof (sstart0 x0 st LS IM _ _ Hm2) as S02.
    pose proof (sstart_mono x0 st LS IG _ _ 0 idx Hm ltac:(lia)) as SMa. pose proof (sstart_mono x0 st LS IG _ _ 0 i2 Hm2 ltac:(lia)) as SMb.
    pose proof (ir_disj _ _ _ IR (fst bm2) (fst bg) r2 r Hr2 Hr NF) as D. unfold region_live_range in D. rewrite Kr2, Kr in D.
    fold stride in SS. unfold UNIT, IB in *. lia.
Qed.

Lemma realloc_geo_facts : exists off r, 0 <= off <= 255 /\ A = conc st c + UNIT * off /\ UNIT * off + old <= stride - IB /\ 0 <= old
  /\ UNIT <= stride /\ stride mod UNIT = 0 /\ (m_sizeclass (MR st g) < 48 -> stride < 2 ^ 20)
  /\ s_regions st !! (fst bg) = Some r /\ r_kind r = RKGroup /\ fst c = fst bg
  /\ c = (fst bg, snd bg + UNIT + stride * idx) /\ 0 <= snd bg /\ snd bg mod UNIT = 0 /\ 0 <= idx <= m_last_idx (MR st g) /\ m_last_idx (MR st g) <= 31
  /\ snd bg + UNIT + stride * (idx + 1) <= round_up_pg (r_len r) /\ r_base r + round_up_pg (r_len r) <= alloc_ceiling /\ 0 <= r_base r
  /\ known st (fst c, snd c + UNIT * off - 3) (idx + 32 * Z.min (snd c + stride - IB - (snd c + UNIT * off) - old) 5).
Proof.
  destruct realloc_bf as (L & LS & BL & off & ai & a & ar & ka & INV & CR & Hk & HA & BF).
  pose proof INV as (IR & IA & IM & IL & IG & IS & ISH).
  assert (Hm : hosts st bg g) by (exists ai; exact (bf_hosts _ _ _ _ _ _ _ _ _ _ _ BF)).
  destruct (ig_region _ _ _ IG _ _ (bf_hosts _ _ _ _ _ _ _ _ _ _ _ BF)) as (r & Hr & Kr).
  destruct (A_MallocFacts_inv2.group_in_region x0 st L BL LS INV _ _ Hm) as (r' & Hr' & _ & B0 & GE).
  rewrite Hr in Hr'. assert (r' = r) as -> by congruence.
  destruct (ir_shape _ _ _ IR _ _ Hr) as (RB0 & _ & _ & _ & RC & _).
  pose proof (sstart_mono x0 st LS IG _ _ (idx + 1) (m_last_idx (MR st g) + 1) Hm ltac:(pose proof (bf_i _ _ _ _ _ _ _ _ _ _ _ BF); lia)) as SM.
  rewrite <- gend_eq in SM. unfold sstart in SM. rewrite (hosts_gbase x0 st LS IM _ _ Hm) in SM.
  pose proof (bf_shadow _ _ _ _ _ _ _ _ _ _ _ BF) as SHB. unfold blk_shadow_ok in SHB. cbn [bslot boff bsize fst snd] in SHB.
  destruct SHB as (_ & K3 & _). fold stride in K3.
  exists off, r. split; [exact (bf_off _ _ _ _ _ _ _ _ _ _ _ BF)|]. split; [exact HA|]. split; [exact (bf_fit _ _ _ _ _ _ _ _ _ _ _ BF)|].
  split; [exact (bf_n _ _ _ _ _ _ _ _ _ _ _ BF)|].
  split; [exact (proj1 (bf_stride _ _ _ _ _ _ _ _ _ _ _ BF))|]. split; [exact (proj2 (bf_stride _ _ _ _ _ _ _ _ _ _ _ BF))|].
  split; [intros SC; exact (small_stride x0 st L BL LS bg g INV Hm SC)|].
  split; [exact Hr|]. split; [exact Kr|]. split; [rewrite (bf_c _ _ _ _ _ _ _ _ _ _ _ BF); reflexivity|].
  split; [rewrite (bf_c _ _ _ _ _ _ _ _ _ _ _ BF) at 1; unfold sstart; rewrite (hosts_gbase x0 st LS IM _ _ Hm); reflexivity|].
  split; [exact B0|]. split; [exact (proj2 (bf_b16 _ _ _ _ _ _ _ _ _ _ _ BF))|]. split; [exact (bf_i _ _ _ _ _ _ _ _ _ _ _ BF)|]. split; [exact (bf_li _ _ _ _ _ _ _ _ _ _ _ BF)|]. split; [fold stride in SM; lia|]. split; [exact RC|]. split; [lia|].
  exact K3.
Qed.

Lemma realloc_region_private : m_sizeclass (MR st g) = 63 ->
  forall r, s_regions st !! (fst bg) = Some r ->
  (forall b', In b' LB -> blk_slot b' <> c ->
     forall x, r_base r <= x < r_base r + round_up_pg (r_len r) -> ~ (blk_addr b' <= x < blk_addr b' + blk_size b'))
  /\ (forall b gh, s_groups st !! b = Some gh -> fst b = fst bg -> b = bg)
  /\ snd bg = 0 /\ idx = 0 /\ m_last_idx (MR st g) = 0 /\ m_maplen (MR st g) * 4096 = round_up_pg (r_len r) /\ r_kind r = RKGroup.
Proof.
  intros SC63 r Hr. destruct realloc_bf as (L & LS & BL & off & ai & a & ar & ka & INV & CR & Hk & HA & BF).
  pose proof INV as (IR & IA & IM & IL & IG & IS & ISH).
  pose proof (bf_hosts _ _ _ _ _ _ _ _ _ _ _ BF) as HgB. assert (Hm : hosts st bg g) by (exists ai; exact HgB).
  pose proof (ig_ok _ _ _ IG _ _ _ HgB) as GO.
  destruct (g_sc _ _ _ _ _ _ GO) as [[S48 _]|(_ & L0 & ML & _)]; [rewrite SC63 in S48; lia|].
  destruct (g_top _ _ _ _ _ _ GO ML) as (SB0 & r0 & Hr0 & Kr0 & EOL & GE). rewrite Hr in Hr0. assert (r0 = r) as -> by congruence.
  pose proof (bf_i _ _ _ _ _ _ _ _ _ _ _ BF) as Hi. assert (I0 : idx = 0) by lia.
  assert (Ebg : bg = (fst bg, 0)) by (destruct bg; cbn in SB0 |- *; subst; reflexivity).
  assert (HgB0 : s_groups st !! (fst bg, 0) = Some (mkGhdr (Some g) ai)) by (rewrite <- Ebg; exact HgB).
  assert (ONLYG : forall b gh, s_groups st !! b = Some gh -> fst b = fst bg -> b = bg).
  { intros b gh Hgh Hf. destruct (im_hdr _ _ _ IM _ _ Hgh) as (m' & Eg & _ & _).
    destruct gh as [gm gai]. cbn in Eg. subst gm.
    destruct (aptr_eq_dec m' g) as [->|NE].
    - exact (hosts_inj x0 st LS IM _ _ _ (ex_intro _ gai Hgh) Hm).
    - exfalso. exact (bb_not_rid x0 st L BL LS g (fst bg) ai 0 0 INV HgB0 SC63 m' b gai Hgh NE Hf). }
  split; [| split; [exact ONLYG| split; [exact SB0| split; [exact I0| split; [exact L0| split; [exact EOL| exact Kr0]]]]]].
  intros b' Hb' NE x Hx Hin.
  destruct (A_MallocFacts_inv2.LB_geo x0 st L BL LS INV LB CR b' Hb')
    as (c2 & off2 & n2 & m2 & bm2 & i2 & r2 & Hk2 & C1 & C2 & Hm2 & Hi2 & Ec2 & NH2 & Hr2 & Kr2 & Ea2 & Ho2 & Hn2 & Fit2).
  rewrite C2, Ea2 in Hin.
  destruct (N.eq_dec (fst bm2) (fst bg)) as [EF|NF].
  -
    destruct (is_blocks _ _ _ IS _ Hk2) as (m2' & i2' & Hs2 & _). cbn [bslot fst snd] in Hs2.
    destruct (rid_slots x0 st L BL LS g (fst bg) ai 0 0 INV HgB0 SC63 c2 m2' i2' Hs2 ltac:(rewrite Ec2; exact EF)) as (Es & _ & _).
    apply NE. rewrite C1, Es. pose proof (bf_c _ _ _ _ _ _ _ _ _ _ _ BF) as EC. unfold c in EC |- *. rewrite EC. rewrite Ebg at 2. cbn [fst]. f_equal.
    unfold sstart. rewrite (hosts_gbase x0 st LS IM _ _ Hm), SB0, I0. unfold UNIT. lia.
  -
    destruct (A_MallocFacts_inv2.group_in_region x0 st L BL LS INV _ _ Hm2) as (r2' & Hr2' & _ & B02 & GE2).
    rewrite Hr2 in Hr2'. assert (r2' = r2) as -> by congruence.
    pose proof (sstart_mono x0 st LS IG _ _ (i2 + 1) (m_last_idx (MR st m2) + 1) Hm2 ltac:(lia)) as SM2. rewrite <- gend_eq in SM2.
    pose proof (sstart_succ st m2 i2) as SS2. pose proof (sstart0 x0 st LS IM _ _ Hm2) as S02.
    pose proof (sstart_mono x0 st LS IG _ _ 0 i2 Hm2 ltac:(lia)) as SMb.
    pose proof (ir_disj _ _ _ IR (fst bm2) (fst bg) r2 r Hr2 Hr NF) as D. unfold region_live_range in D. rewrite Kr2, Kr0 in D.
    pose proof (stride_ge x0 st LS IG _ _ Hm2) as [SG _].
    unfold UNIT, IB in *. lia.
Qed.

Lemma realloc_blk_in_region : forall b', In b' LB ->
  forall x, blk_addr b' <= x < blk_addr b' + blk_size b' ->
  exists rq, s_regions st !! (fst (blk_slot b')) = Some rq /\ r_kind rq = RKGroup
             /\ r_base rq <= x < r_base rq + round_up_pg (r_len rq).
Proof.
  intros b' Hb' x Hx. destruct realloc_bf as (L & LS & BL & off & ai & a & ar & ka & INV & CR & Hk & HA & BF).
  pose proof INV as (IR & IA & IM & IL & IG & IS & ISH).
  destruct (A_MallocFacts_inv2.LB_geo x0 st L BL LS INV LB CR b' Hb')
    as (c2 & off2 & n2 & m2 & bm2 & i2 & r2 & Hk2 & C1 & C2 & Hm2 & Hi2 & Ec2 & NH2 & Hr2 & Kr2 & Ea2 & Ho2 & Hn2 & Fit2).
  rewrite C2, Ea2 in Hx. rewrite C1, Ec2. cbn [fst]. exists r2. split; [exact Hr2|]. split; [exact Kr2|].
  destruct (A_MallocFacts_inv2.group_in_region x0 st L BL LS INV _ _ Hm2) as (r2' & Hr2' & _ & B02 & GE2).
  rewrite Hr2 in Hr2'. assert (r2' = r2) as -> by congruence.
  pose proof (sstart_mono x0 st LS IG _ _ (i2 + 1) (m_last_idx (MR st m2) + 1) Hm2 ltac:(lia)) as SM2. rewrite <- gend_eq in SM2.
  pose proof (sstart_succ st m2 i2) as SS2. pose proof (sstart0 x0 st LS IM _ _ Hm2) as S02.
  pose proof (sstart_mono x0 st LS IG _ _ 0 i2 Hm2 ltac:(lia)) as SMb.
  pose proof (stride_ge x0 st LS IG _ _ Hm2) as [SG _].
  unfold UNIT, IB in *. lia.
Qed.
End REALLOC2.

End CEIL.
