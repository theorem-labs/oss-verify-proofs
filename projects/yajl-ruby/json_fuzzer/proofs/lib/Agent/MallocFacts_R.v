(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From stdpp Require Import gmap.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import STree Malloc MallocCtrl KInv MI_Tree MI_Inv MI_Kit MI_Geom MI_Ext
  MI_WSlot MI_WMalloc MI_Sim MI_Contracts MI_WRealloc2 MI_FreeNoPeek MI_Read.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Export MI_FreeNoPeek.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Agent Require Import MallocOracle MallocVocab MallocBlocks MallocFacts_inv MallocFacts_inv2 MallocFacts_inv3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac splits := repeat (lazymatch goal with |- _ /\ _ => split | |- _ => fail end).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Section R.
Context {resv : list (Z * Z)}.
Variables (st : mstate) (LB : list block) (blk : block) (pf : aptr).
Hypothesis AR : AREACH_from resv st LB.
Hypothesis Hb : In blk LB.
Hypothesis Hfst : fst pf = fst (blk_slot blk).
Hypothesis Hconc : conc st pf = blk_addr blk.

Lemma blk_inv : exists L LS BL off,
  INVL x0 st L BL LS /\ CORR st LB BL /\ ld_live L = map bslot BL /\ s_secret st = rc_secret
  /\ In ((blk_slot blk, off), blk_size blk) BL /\ 0 <= off
  /\ blk_addr blk = conc st (blk_slot blk) + UNIT * off /\ pf = aadd (blk_slot blk) (UNIT * off)
  /\ exists rg, s_regions st !! fst (blk_slot blk) = Some rg /\ r_kind rg = RKGroup.
Proof.
  destruct (areach_inv resv st LB AR) as (L & LS & BL & INV & LIVE & RESV & SEC & CR).
  destruct (Forall2_In_l _ _ _ _ CR Hb) as (k & Hk & (C1 & C2 & C3)).
  destruct k as [[c off] n0]. cbn [bslot boff bsize fst snd] in C1, C2, C3.
  destruct (MI_WRealloc2.blk_region _ _ _ _ _ _ INV Hk) as (rg & Hrg & Krg). cbn [bslot fst snd] in Hrg.
  pose proof INV as (_ & _ & _ & _ & _ & IS & _). destruct (is_blocks _ _ _ IS _ Hk) as (m & i & _ & Hoff & _). cbn [boff fst snd] in Hoff.
  exists L, LS, BL, off. rewrite C1, C2. splits; auto; try lia.
  - unfold conc, get_region in Hconc, C3 |- *. rewrite Hfst, C1 in Hconc. rewrite Hrg in Hconc, C3. rewrite C3 in Hconc.
    apply injective_projections; unfold aadd; cbn [fst snd]; [rewrite Hfst, C1; reflexivity| lia].
  - exists rg. auto.
Qed.

(* [comment removed for export] *)
Theorem areach_free_nopeek : nopeek (free st (Some pf)).
Proof.
  destruct blk_inv as (L & LS & BL & off & INV & CR & LIVE & SEC & Hk & Hoff & Haddr & -> & _).
  exact (free_nopeek st L BL LS (blk_slot blk) off (blk_size blk) INV Hk).
Qed.

(* [comment removed for export] *)
Theorem areach_blk_slot_nogrp g i :
  s_slots st !! blk_slot blk = Some (g, i) ->
  forall b' gh, s_groups st !! b' = Some gh -> fst b' = fst (blk_slot blk) ->
  snd b' + 12 <= snd (blk_slot blk) - IB \/ snd (blk_slot blk) + get_stride (get_meta_rec st g) - IB <= snd b'.
Proof.
  intros Hs b' gh Hb' Hf'.
  destruct blk_inv as (L & LS & BL & off & INV & CR & _).
  destruct (LB_geo _ _ _ _ _ INV LB CR blk Hb) as (c & off' & n & m & bm & j & r & Hk & Ec & En & Hm & Hj & Ecb & NH & Hr & Kr & _).
  pose proof INV as (IR & IA & IM & IL & IG & IS & ISH).
  rewrite Ec, Ecb in Hs. rewrite <- (slot_start'_eq _ _ _ IM _ _ j Hm) in Hs.
  rewrite (is_total _ _ _ IS _ _ _ Hm Hj) in Hs. inversion Hs. subst g i.
  destruct (im_hdr _ _ _ IM _ _ Hb') as (m2 & Em2 & Hmem2 & _).
  assert (H2 : hosts st b' m2) by (destruct gh as [gm ga]; cbn in Em2; subst gm; exists ga; exact Hb').
  rewrite Ec, Ecb. cbn [fst snd]. rewrite Ec, Ecb in Hf'. cbn [fst] in Hf'. rewrite Ecb in NH.
  destruct (sep_ghdr' _ _ _ _ _ INV m bm j m2 b' (proj2 (hostsB _ _ _) Hm) Hj NH (proj2 (hostsB _ _ _) H2) Hf') as [D|D].
  - left. unfold IB. lia.
  - right. rewrite sstart_succ in D. fold (MR st m). unfold IB. lia.
Qed.


(* [comment removed for export] *)
Lemma nodup_map_inj' {A B} (f : A -> B) l x y : List.NoDup (map f l) -> In x l -> In y l -> f x = f y -> x = y.
Proof.
  induction l as [|z l IH]; intros Hnd Hx Hy E; [destruct Hx|]. cbn in Hnd. inversion Hnd; subst.
  destruct Hx as [<-|Hx], Hy as [<-|Hy]; [reflexivity| | | apply IH; auto].
  - exfalso. apply H1. rewrite E. apply in_map. exact Hy.
  - exfalso. apply H1. rewrite <- E. apply in_map. exact Hx.
Qed.

Theorem areach_blk63_alone g i :
  s_slots st !! blk_slot blk = Some (g, i) -> m_sizeclass (get_meta_rec st g) = 63 ->
  let rid := fst (blk_slot blk) in
  i = 0 /\ blk_slot blk = (rid, UNIT) /\ pf = (rid, snd pf) /\ UNIT <= snd pf
  /\ m_mem (get_meta_rec st g) = Some (rid, 0) /\ m_last_idx (get_meta_rec st g) = 0 /\ m_maplen (get_meta_rec st g) <> 0
  /\ (exists rg, s_regions st !! rid = Some rg /\ r_kind rg = RKGroup
        /\ m_maplen (get_meta_rec st g) * 4096 = round_up_pg (r_len rg) /\ blk_addr blk = r_base rg + snd pf
        /\ snd pf + blk_size blk <= m_maplen (get_meta_rec st g) * 4096 - IB)
  /\ (forall b' gh, s_groups st !! b' = Some gh -> fst b' = rid -> b' = (rid, 0) /\ g_meta gh = Some g)
  /\ (forall blk', In blk' LB -> fst (blk_slot blk') = rid -> blk' = blk)
  /\ (forall s g' i', s_slots st !! s = Some (g', i') -> fst s = rid -> s = blk_slot blk /\ g' = g /\ i' = 0)
  /\ (forall m' b', m_mem (get_meta_rec st m') = Some b' -> fst b' = rid -> m' = g /\ b' = (rid, 0)).
Proof.
  intros Hs SC rid.
  destruct blk_inv as (L & LS & BL & off & INV & CR & LIVE & SEC & Hk & Hoff & Haddr & Epf & rg0 & Hrg0 & Krg0).
  destruct (LB_geo _ _ _ _ _ INV LB CR blk Hb) as (c & off' & n & m & bm & j & r & Hk' & Ec & En & Hm & Hj & Ecb & NH & Hr & Kr & Eaddr & Ho' & Hn & FIT).
  pose proof INV as (IR & IA & IM & IL & IG & IS & ISH).
  assert (Hs2 := Hs). rewrite Ec, Ecb, <- (slot_start'_eq _ _ _ IM _ _ j Hm), (is_total _ _ _ IS _ _ _ Hm Hj) in Hs2. inversion Hs2. subst g i. clear Hs2.
  fold (MR st m) in SC |- *.
  destruct (hosts_ok _ _ _ IG _ _ Hm) as (ai & Hgb & GO).
  destruct (g_sc _ _ _ _ _ _ GO) as [[? ?]|(_ & L0 & ML & NL)]; [lia|].
  destruct (g_top _ _ _ _ _ _ GO ML) as (B0 & rg & Hrg & Krg & Hml & GE).
  assert (J0 : j = 0) by lia. subst j.
  assert (Erid : rid = fst bm) by (unfold rid; rewrite Ec, Ecb; reflexivity).
  assert (Ebm : bm = (rid, 0)) by (rewrite Erid; destruct bm; cbn in B0 |- *; subst; reflexivity).
  pose proof (sstart0 _ _ _ IM _ _ Hm) as S0.
  assert (ALONE : forall b' m', hosts st b' m' -> fst b' = rid -> m' = m).
  { intros b' m' Hm' Hf. destruct (aptr_eq_dec m' m) as [->|NE]; [reflexivity|]. exfalso.
    destruct (Z.eq_dec (m_maplen (MR st m')) 0) as [Hml'|Hml'].
    - destruct (@top_chain _ _ _ _ IM IG IS m' b' Hm' Hml') as (t & jj & cc & bt & Ha & Ht & Htop & Hft).
      assert (t = m) by (apply (@top_unique _ _ _ IG t m bt bm Ht Hm Htop ML); congruence). subst t.
      destruct (@anc_facts _ _ _ _ IM IG IS m' m jj cc Ha) as (bm' & bp' & _ & _ & _ & _ & _ & _ & _ & _ & SC'). lia.
    - apply NE. apply (@top_unique _ _ _ IG m' m b' bm Hm' Hm Hml' ML). congruence. }
  assert (ND : off' = off /\ n = blk_size blk).
  { pose proof (proj1 (NoDup_ListNoDup _) (is_nodup _ _ _ IS)) as NDk. rewrite Ec in Hk.
    pose proof (nodup_map_inj' bslot BL _ _ NDk Hk Hk' eq_refl) as E. inversion E. auto. }
  destruct ND as [-> En']. 
  splits.
  - reflexivity.
  - rewrite Ec, Ecb, Erid, S0, B0. reflexivity.
  - rewrite Epf. unfold aadd. cbn. rewrite Ec at 1. rewrite Ecb. cbn [fst]. rewrite Erid. reflexivity.
  - rewrite Epf. unfold aadd. cbn [snd]. rewrite Ec, Ecb. cbn [snd]. rewrite S0, B0. unfold UNIT in *. lia.
  - rewrite (hosts_mem _ _ _ IM _ _ Hm), Ebm. reflexivity.
  - exact L0.
  - exact ML.
  - exists rg. rewrite Erid. split; [exact Hrg|]. split; [exact Krg|]. split; [exact Hml|].
    assert (r = rg) by (rewrite Hrg in Hr; congruence). subst r.
    rewrite Epf. unfold aadd. cbn [snd]. rewrite Ec, Ecb. cbn [snd]. split; [lia|].
    unfold gend, cnt_of in GE. rewrite L0, sstart_succ in GE. rewrite <- En'.
    pose proof (stride_ge _ _ _ IG _ _ Hm). unfold UNIT, IB in *. lia.
  - intros b' gh Hb' Hf. destruct (im_hdr _ _ _ IM _ _ Hb') as (m2 & Em2 & Hmem2 & _).
    assert (H2 : hosts st b' m2) by (destruct gh as [gm ga]; cbn in Em2; subst gm; exists ga; exact Hb').
    pose proof (ALONE b' m2 H2 Hf) as ->. split; [| exact Em2]. rewrite <- Ebm. exact (hosts_inj _ _ _ IM _ _ _ H2 Hm).
  - intros blk' Hb2 Hf.
    destruct (LB_geo _ _ _ _ _ INV LB CR blk' Hb2) as (c2 & off2 & n2 & m2 & bm2 & j2 & r2 & Hk2 & Ec2 & En2 & Hm2 & Hj2 & Ecb2 & _).
    rewrite Ec2, Ecb2 in Hf. cbn [fst] in Hf. pose proof (ALONE bm2 m2 Hm2 Hf) as ->.
    pose proof (hosts_inj _ _ _ IM _ _ _ Hm2 Hm) as ->. assert (j2 = 0) by lia. subst j2.
    apply (nodup_map_inj' blk_slot LB _ _ (LB_nodup _ _ _ _ _ INV LB CR) Hb2 Hb). rewrite Ec2, Ecb2, Ec, Ecb. reflexivity.
  - intros s g' i' Hs' Hf. destruct (is_valid _ _ _ IS _ _ _ Hs') as ([b' Hb'] & Hi' & Es).
    rewrite (slot_start'_eq _ _ _ IM _ _ i' Hb') in Es. subst s. cbn [fst] in Hf.
    pose proof (ALONE b' g' Hb' Hf) as ->. pose proof (hosts_inj _ _ _ IM _ _ _ Hb' Hm) as ->. assert (i' = 0) by lia. subst i'.
    rewrite Ec, Ecb. auto.
  - intros m' b' Hmem Hf. fold (MR st m') in Hmem.
    destruct (im_group _ _ _ IM _ _ Hmem) as [H'|H']; [| destruct H'].
    pose proof (ALONE b' m' H' Hf) as ->. split; [reflexivity|]. rewrite <- Ebm. exact (hosts_inj _ _ _ IM _ _ _ H' Hm).
Qed.

(* [comment removed for export] *)
Theorem areach_blk_hdr g i :
  s_slots st !! blk_slot blk = Some (g, i) ->
  let mr := get_meta_rec st g in
  let stride := get_stride mr in
  let rid := fst (blk_slot blk) in
  let p := snd pf in
  let e := snd (blk_slot blk) + stride - IB in
  let sh := get_shadow st rid in
  exists bm off rsv q,
    m_mem mr = Some bm /\ fst bm = rid /\ hosts st bm g /\ 0 <= i <= m_last_idx mr
    /\ snd (blk_slot blk) = snd bm + UNIT + stride * i
    /\ 0 <= off /\ p = snd (blk_slot blk) + UNIT * off /\ 0 <= blk_size blk
    /\ rsv = stride - IB - UNIT * off - blk_size blk /\ 0 <= rsv
    /\ q = (p - snd bm - UNIT) / UNIT /\ UNIT * q = p - snd bm - UNIT /\ 0 <= q < 2^16
    /\ cell_read sh (p - 4) = Known 0
    /\ cell_read sh (p - 3) = Known (i + 32 * Z.min rsv 5)
    /\ cell_read sh (p - 2) = Known (byte_of q 0) /\ cell_read sh (p - 1) = Known (byte_of q 1)
    /\ (5 <= rsv -> cell_read sh (e - 4) = Known (byte_of rsv 0) /\ cell_read sh (e - 3) = Known (byte_of rsv 1)
                  /\ cell_read sh (e - 2) = Known (byte_of rsv 2) /\ cell_read sh (e - 1) = Known (byte_of rsv 3)
                  /\ cell_read sh (e - 5) = Known 0 /\ rsv < 2^32)
    /\ (0 < rsv -> cell_read sh (e - rsv) = Known 0)
    /\ cell_read sh e = Known 0
    /\ (forall a, p <= a < p + blk_size blk -> exists hint, cell_read sh a = Unknown hint)
    /\ ((0 <= m_sizeclass mr < 48 /\ m_maplen mr <= 256) \/ (m_sizeclass mr = 63 /\ m_last_idx mr = 0 /\ m_maplen mr <> 0))
    /\ 16 <= stride /\ stride mod 16 = 0.
Proof.
  intros Hs mr stride rid p e sh.
  destruct blk_inv as (L & LS & BL & off & INV & CR & LIVE & SEC & Hk & Hoff & Haddr & Epf & rg0 & Hrg0 & Krg0).
  destruct (LB_geo _ _ _ _ _ INV LB CR blk Hb) as (c & off' & n & m & bm & j & r & Hk' & Ec & En & Hm & Hj & Ecb & NH & Hr & Kr & Eaddr & Ho' & Hn & FIT).
  pose proof INV as (IR & IA & IM & IL & IG & IS & ISH).
  assert (Hs2 := Hs). rewrite Ec, Ecb, <- (slot_start'_eq _ _ _ IM _ _ j Hm), (is_total _ _ _ IS _ _ _ Hm Hj) in Hs2. inversion Hs2. subst g i. clear Hs2.
  assert (ND : off' = off /\ n = blk_size blk).
  { pose proof (proj1 (NoDup_ListNoDup _) (is_nodup _ _ _ IS)) as NDk. rewrite Ec in Hk.
    pose proof (nodup_map_inj' bslot BL _ _ NDk Hk Hk' eq_refl) as E. inversion E. auto. }
  destruct ND as [-> En']. subst n.
  destruct (hosts_ok _ _ _ IG _ _ Hm) as (ai & Hgb & GO).
  pose proof (stride_ge _ _ _ IG _ _ Hm) as [S16 SM].
  pose proof (ish_blk _ _ ISH _ _ _ Hk' ltac:(cbn [bslot fst snd]; rewrite <- Ec; exact Hs)) as B. cbn zeta in B. cbn [fst snd bslot boff bsize] in B. rewrite Ecb in B. cbn [fst snd] in B.
  rewrite (hosts_gbase _ _ _ IM _ _ Hm) in B.
  destruct B as (K4 & K3 & K2 & K1 & Q & KR & KZ & KU).
  pose proof (ish_hdr0 _ _ ISH bm m (j + 1) Hm ltac:(unfold cnt_of; lia)) as KE. rewrite sstart_succ in KE.
  assert (Ep : p = sstart (MR st m) j + UNIT * off) by (subst p; rewrite Epf; unfold aadd; cbn [snd]; rewrite Ec, Ecb; reflexivity).
  pose proof (sstart0 _ _ _ IM _ _ Hm) as S0.
  assert (Esj : sstart (MR st m) j = snd bm + UNIT + get_stride (MR st m) * j) by (unfold sstart; rewrite (hosts_gbase _ _ _ IM _ _ Hm); reflexivity).
  exists bm, off, (get_stride (MR st m) - IB - UNIT * off - blk_size blk), ((sstart (MR st m) j + UNIT * off - snd bm - UNIT) / UNIT).
  fold (MR st m) in mr. subst mr stride rid sh e. rewrite Ec, Ecb. cbn [fst snd].
  assert (HQ : UNIT * ((sstart (MR st m) j + UNIT * off - snd bm - UNIT) / UNIT) = sstart (MR st m) j + UNIT * off - snd bm - UNIT).
  { rewrite Esj. replace (snd bm + UNIT + get_stride (MR st m) * j + UNIT * off - snd bm - UNIT) with ((get_stride (MR st m) / 16 * j + off) * UNIT).
    2:{ unfold UNIT. pose proof (Z_div_exact_full_2 (get_stride (MR st m)) 16 ltac:(lia) SM). nia. }
    unfold UNIT. rewrite Z.div_mul by lia. lia. }
  unfold known, SHd in K4, K3, K2, K1, KZ, KE. cbn [fst snd] in K4, K3, K2, K1, KZ, KE.
  replace (sstart (MR st m) j + get_stride (MR st m) - IB - (sstart (MR st m) j + UNIT * off) - blk_size blk)
     with (get_stride (MR st m) - IB - UNIT * off - blk_size blk) in K3, KR, KZ by lia.
  rewrite Ep. subst p.
  splits; auto; try lia.
  all: try exact (hosts_mem _ _ _ IM _ _ Hm).
  all: try (destruct (g_sc _ _ _ _ _ _ GO) as [A|(B1 & B2 & B3 & _)]; [left; exact A| right; auto]; fail).
  all: try (first [exact K4 | exact K2 | exact K1]).
  all: try (replace (sstart (MR st m) j + get_stride (MR st m) - IB - (sstart (MR st m) j + UNIT * off) - blk_size blk)
              with (get_stride (MR st m) - IB - UNIT * off - blk_size blk) by lia).
  all: try exact K3.
  all: try (intros H5; destruct (KR H5) as (R1 & R2 & R3 & R4 & R5 & R6); unfold known, SHd in R1, R2, R3, R4, R5; cbn [fst snd] in R1, R2, R3, R4, R5;
            repeat split; assumption).
  all: try (intros H0; apply KZ; exact H0).
  all: try (replace (sstart (MR st m) j + get_stride (MR st m) - IB) with (sstart (MR st m) j + get_stride (MR st m) - IB) by lia; exact KE).
  all: try (intros a Hpa; destruct (KU a Hpa) as [hint Hh]; exists hint; unfold SHd in Hh; exact Hh).
  all: match goal with |- ?G => idtac "REMAINS_HDR" G end.
Qed.

(* [comment removed for export] *)
Theorem areach_blk_slot_clear g i :
  s_slots st !! blk_slot blk = Some (g, i) ->
  forall blk', In blk' LB -> blk_slot blk' <> blk_slot blk -> fst (blk_slot blk') = fst (blk_slot blk) ->
  blk_addr blk' + blk_size blk' <= conc st (blk_slot blk) - IB
  \/ conc st (blk_slot blk) + get_stride (get_meta_rec st g) - IB <= blk_addr blk'.
Proof.
  intros Hs blk' Hb' NE Hf.
  destruct blk_inv as (L & LS & BL & off & INV & CR & _).
  destruct (LB_geo _ _ _ _ _ INV LB CR blk Hb) as (c & off1 & n & m & bm & j & r & Hk & Ec & En & Hm & Hj & Ecb & NH & Hr & Kr & Eaddr & Ho1 & Hn & FIT).
  destruct (LB_geo _ _ _ _ _ INV LB CR blk' Hb') as (c2 & off2 & n2 & m2 & bm2 & j2 & r2 & Hk2 & Ec2 & En2 & Hm2 & Hj2 & Ecb2 & NH2 & Hr2 & Kr2 & Eaddr2 & Ho2 & Hn2 & FIT2).
  pose proof INV as (IR & IA & IM & IL & IG & IS & ISH).
  assert (Hs2 := Hs). rewrite Ec, Ecb, <- (slot_start'_eq _ _ _ IM _ _ j Hm), (is_total _ _ _ IS _ _ _ Hm Hj) in Hs2. inversion Hs2. subst g i. clear Hs2.
  fold (MR st m).
  rewrite Ec, Ecb, Ec2, Ecb2 in Hf. cbn [fst] in Hf.
  assert (Er : r2 = r) by (rewrite Hf, Hr in Hr2; congruence). subst r2.
  assert (NE2 : m2 <> m \/ j2 <> j).
  { destruct (aptr_eq_dec m2 m) as [->|]; [right| now left]. intros ->. apply NE. rewrite Ec, Ec2, Ecb, Ecb2, Hf. reflexivity. }
  assert (Econc : conc st (blk_slot blk) = r_base r + sstart (MR st m) j).
  { unfold conc, get_region. rewrite Ec, Ecb. cbn [fst snd]. rewrite Hr. reflexivity. }
  rewrite Econc, Eaddr2, En2.
  pose proof (sstart_succ st m j) as SS. pose proof (sstart_succ st m2 j2) as SS2.
  rewrite Ecb2 in NH2. cbn [fst] in NH2.
  destruct (sep_ext _ _ _ _ IM IG IS m bm j Hm Hj ltac:(rewrite Ecb in NH; exact NH) m2 bm2 j2 Hm2 Hf Hj2 NE2 NH2) as [A|A];
    unfold UNIT, IB in *; lia.
Qed.

End R.

(* [comment removed for export] *)
Theorem areach_malloc_keeps_blocks {resv} st LB n (o o' : mem) ans st1 r :
  AREACH_from resv st LB -> 0 <= n ->
  follow (mrun o (malloc st n)) ans = Some (o', (st1, r)) ->
  (forall blk, In blk LB -> s_regions st1 !! fst (blk_slot blk) = s_regions st !! fst (blk_slot blk))
  /\ s_secret st1 = s_secret st.
Proof.
  intros AR Hn FF.
  destruct (areach_inv resv st LB AR) as (L & LS & BL & INV & LIVE & RESV & SEC & CR).
  destruct (malloc_sim pans_mem pupd_mem pans_mem_range st L BL LS n o ans o' st1 r INV Hn FF) as (rc & _ & _ & _ & [GPR GPS] & _).
  split; [| exact GPS].
  intros blk Hb. destruct (Forall2_In_l _ _ _ _ CR Hb) as (k & Hk & (C1 & C2 & C3)).
  destruct (MI_WRealloc2.blk_region _ _ _ _ _ _ INV Hk) as (rg & Hrg & Krg). rewrite <- C1 in Hrg.
  rewrite Hrg. exact (GPR _ _ Hrg Krg).
Qed.

Corollary areach_malloc_keeps_conc {resv} st LB n (o o' : mem) ans st1 r blk (q : aptr) :
  AREACH_from resv st LB -> 0 <= n ->
  follow (mrun o (malloc st n)) ans = Some (o', (st1, r)) ->
  In blk LB -> fst q = fst (blk_slot blk) -> conc st1 q = conc st q.
Proof.
  intros AR Hn FF Hb Hf. destruct (areach_malloc_keeps_blocks st LB n o o' ans st1 r AR Hn FF) as [RG _].
  unfold conc, get_region. rewrite Hf, (RG blk Hb). reflexivity.
Qed.
End RC__1.
