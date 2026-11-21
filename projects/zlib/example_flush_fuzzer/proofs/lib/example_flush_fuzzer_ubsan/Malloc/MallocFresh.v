(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From stdpp Require Import gmap.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.Spec Require Import STree Malloc MallocCtrl KInv MI_Tree MI_Inv MI_Kit MI_Geom MI_Shadow MI_TF2 MI_WGroup MI_WTry2 MI_WSlot MI_WSlot2 MI_WMalloc.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.Malloc Require Import MallocTree MallocBlocks MallocFacts_inv MallocSU.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.Common Require Import RunDraw.
Import ListNotations.
Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.


Lemma cell_read_hdrsh t o : 12 <= o -> cell_read (hdrsh t) o = Known 0.
Proof.
  intros Ho. unfold cell_read, hdrsh. cbn [r_cells r_hav r_havp]. rewrite !lookup_empty. cbn [stale_pg orb].
  destruct (Z.eq_dec (o / 16) 0) as [E|NE].
  - rewrite E, lookup_insert_eq. cbn [default from_option id stale existsb fst snd].
    assert (o < 16) by (pose proof (Z.div_mod o 16 ltac:(lia)); pose proof (Z.mod_pos_bound o 16 ltac:(lia)); lia).
    replace (o mod 16 <? 12) with false by (symmetry; apply Z.ltb_ge; rewrite Z.mod_small by lia; lia). reflexivity.
  - rewrite lookup_insert_ne by congruence. rewrite lookup_empty. reflexivity.
Qed.


Lemma cr_wr8_other rid o p v st : rid = fst p -> o <> snd p -> cell_read (get_shadow (wr8 p v st) rid) o = cell_read (get_shadow st rid) o.
Proof. intros -> NE. exact (cell_read_wr8_other p v st (fst p, o) ltac:(intros E; apply NE; rewrite <- E; reflexivity)). Qed.
Lemma cr_wr16_other rid o p v st : rid = fst p -> (o < snd p \/ snd p + 2 <= o) -> cell_read (get_shadow (wr16 p v st) rid) o = cell_read (get_shadow st rid) o.
Proof. intros -> R. unfold wr16. rewrite !cr_wr8_other; [reflexivity| reflexivity| cbn; lia| reflexivity| cbn; lia]. Qed.
Lemma cr_wr32_other rid o p v st : rid = fst p -> (o < snd p \/ snd p + 4 <= o) -> cell_read (get_shadow (wr32 p v st) rid) o = cell_read (get_shadow st rid) o.
Proof. intros -> R. unfold wr32. rewrite !cr_wr8_other; [reflexivity| reflexivity| cbn; lia| reflexivity| cbn; lia| reflexivity| cbn; lia| reflexivity| cbn; lia]. Qed.

Lemma cr_set_size_user p e n b3 st o : fst e = fst p -> snd p + n <= snd e -> snd p <= o < snd p + n ->
  cell_read (get_shadow (set_size p e n b3 st) (fst p)) o = cell_read (get_shadow st (fst p)) o.
Proof.
  intros Ef LE Ho. unfold set_size. set (res := snd e - snd p - n).
  set (st1 := if negb (res =? 0) then wr8 (aadd e (- res)) 0 st else st).
  assert (S1 : cell_read (get_shadow st1 (fst p)) o = cell_read (get_shadow st (fst p)) o).
  { unfold st1. destruct (negb (res =? 0)); [| reflexivity]. apply cr_wr8_other; cbn; [congruence| unfold res; lia]. }
  destruct (5 <=? res) eqn:R5.
  - apply Z.leb_le in R5. cbv beta iota. rewrite cr_wr8_other by (cbn; lia). rewrite cr_wr8_other by (cbn; first [congruence| unfold res in *; lia]).
    rewrite cr_wr32_other by (cbn; first [congruence| unfold res in *; lia]). exact S1.
  - cbv beta iota. rewrite cr_wr8_other by (cbn; lia). exact S1.
Qed.

Lemma enframe_at_user_reads st g idx n off k :
  0 <= off -> 0 <= n -> 16 * off + n + IB <= get_stride (MR st g) -> 0 <= k < n ->
  let r := enframe_at st g idx n off in
  cell_read (get_shadow (fst r) (fst (snd r))) (snd (snd r) + k) = cell_read (get_shadow st (fst (snd r))) (snd (snd r) + k).
Proof.
  intros Ho Hn FIT Hk. unfold enframe_at. fold (MR st g). cbn zeta.
  set (gm := default (0%N, 0) (m_mem (MR st g))). set (stride := get_stride (MR st g)) in *.
  set (p := aadd gm (UNIT + stride * idx)). clearbody p.
  destruct (negb (off =? 0)) eqn:NZ; cbv beta iota; cbn [fst snd].
  - rewrite cr_set_size_user by (cbn; unfold UNIT, IB in *; lia).
    rewrite cr_wr8_other by (cbn; lia). rewrite cr_wr16_other by (cbn; lia). rewrite cr_wr8_other by (cbn; unfold UNIT; lia).
    rewrite cr_wr8_other by (cbn; unfold UNIT; lia). rewrite cr_wr16_other by (cbn; unfold UNIT; lia). reflexivity.
  - apply negb_false_iff in NZ. apply Z.eqb_eq in NZ. subst off.
    rewrite cr_set_size_user by (cbn; unfold UNIT, IB in *; lia).
    rewrite cr_wr8_other by (cbn; lia). rewrite cr_wr16_other by (cbn; lia). reflexivity.
Qed.

Lemma enframe_at_ptr st g idx n off :
  snd (enframe_at st g idx n off) = (fst (gbase (MR st g)), sstart (MR st g) idx + UNIT * off).
Proof.
  unfold enframe_at, sstart, gbase, MR. destruct (negb (off =? 0)) eqn:E; cbn [fst snd].
  - unfold aadd. cbn. f_equal. lia.
  - apply negb_false_iff in E. apply Z.eqb_eq in E. subst off. unfold aadd. cbn. f_equal. lia.
Qed.


Section FRESH.
Context {rc : runConstT} {resv : list (Z * Z)}.

Lemma malloc_core_leaf st LB n (o : mem) ans o1 st2 g idx :
  AREACH_from resv st LB -> 0 <= n ->
  follow (mrun o (malloc_core full_lay (set_tick (N.succ (s_tick st)) st) n)) ans = Some (o1, (st2, Some (g, idx))) ->
  exists L LS BL L2 LS2 bg, INVL x0 st L BL LS /\ CORR st LB BL /\ GPX (set_tick (N.succ (s_tick st)) st) st2
    /\ hosts st2 bg g /\ 0 <= idx <= m_last_idx (MR st2 g)
    /\ INVL (MI_WFree2.xpend x0 (Some (fst bg, sstart (MR st2 g) idx))) st2 L2 BL LS2
    /\ ORIG (set_tick (N.succ (s_tick st)) st) st2 g bg.
Proof.
  intros AR Hn FL.
  destruct (areach_inv resv st LB AR) as (L & LS & BL & INV & _ & _ & _ & CR).
  set (st0 := set_tick (N.succ (s_tick st)) st) in *.
  assert (INV0 : INVL x0 st0 L BL LS) by (apply INVL_set_tick; [cbn; lia| exact INV]).
  assert (TF0' : TF0 st0) by (apply TF0_tick_new; [exact (TKS_of _ _ _ _ _ INV)| cbn; lia]).
  pose proof (ftree_prun pans_mem pupd_mem pans_mem_range _ L _ o (malloc_core_ft st0 L BL LS n INV0 TF0' Hn)) as PT.
  unfold mrun in FL. destruct (ptree_follow _ L _ ans PT FL) as (L2 & _ & POST).
  destruct POST as (_ & GX & LS2 & bg & Hh & Hidx & INV2 & _ & _ & _ & ORG). cbn [fst snd] in GX, Hh, Hidx, INV2, ORG.
  exists L, LS, BL, L2, LS2, bg. repeat (split; [assumption|]). exact ORG.
Qed.

Theorem malloc_core_fresh_known0' st LB n (o : mem) ans o1 st2 g idx b off k :
  AREACH_from resv st LB -> 0 <= n ->
  follow (mrun o (malloc_core full_lay (set_tick (N.succ (s_tick st)) st) n)) ans = Some (o1, (st2, Some (g, idx))) ->
  m_mem (get_meta_rec st2 g) = Some b ->
  gnone st (fst b) -> gonly0 st2 (fst b) ->
  0 <= off -> 16 * off + n + IB <= get_stride (get_meta_rec st2 g) -> 0 <= k < n ->
  let r := enframe_at st2 g idx n off in
  fst (snd r) = fst b /\ cell_read (get_shadow (fst r) (fst b)) (snd (snd r) + k) = Known 0.
Proof.
  intros AR Hn FL Hmem GN GO Ho FIT Hk. cbn zeta.
  destruct (malloc_core_leaf st LB n o ans o1 st2 g idx AR Hn FL) as (L & LS & BL & L2 & LS2 & bg & INV & CR & GX & Hh & Hidx & INV2 & _).
  set (X2 := MI_WFree2.xpend x0 _) in INV2.
  assert (Eb : bg = b).
  { pose proof (hosts_mem X2 st2 LS2 (proj1 (proj2 (proj2 INV2))) _ _ Hh) as M. unfold MR in M. rewrite Hmem in M. inversion M. reflexivity. }
  subst bg.
  assert (GB : gbase (MR st2 g) = b) by (unfold gbase, MR; rewrite Hmem; reflexivity).
  pose proof (enframe_at_ptr st2 g idx n off) as EP. rewrite GB in EP.
  split; [rewrite EP; reflexivity|].
  destruct GX as (_ & _ & _ & TOP).
  destruct (TOP (fst b)) as [t Ht]; [intros bq hq Hbq E; exact (GN bq hq Hbq E)| exact GO|].
  pose proof (enframe_at_user_reads st2 g idx n off k Ho Hn FIT Hk) as RD. cbn zeta in RD. rewrite EP in RD |- *. cbn [fst snd] in RD |- *.
  rewrite RD, Ht. apply cell_read_hdrsh.
  pose proof (sstart_ne0 _ _ _ _ _ g b idx INV2 Hh (proj1 Hidx)) as NZ.
  pose proof (stride_ge X2 st2 LS2 (proj1 (proj2 (proj2 (proj2 (proj2 INV2))))) _ _ Hh) as [SG _].
  destruct (hosts_ok X2 st2 LS2 (proj1 (proj2 (proj2 (proj2 (proj2 INV2))))) _ _ Hh) as (ai & _ & GOK). pose proof (g_align _ _ _ _ _ _ GOK) as [B0 _].
  unfold sstart. rewrite GB. assert (0 <= get_stride (MR st2 g) * idx) by (apply Z.mul_nonneg_nonneg; unfold UNIT in SG; lia). unfold UNIT in *. lia.
Qed.

Theorem malloc_core_fresh_known0 st LB n (o : mem) ans o1 st2 g idx b off k :
  AREACH_from resv st LB -> 0 <= n ->
  follow (mrun o (malloc_core full_lay (set_tick (N.succ (s_tick st)) st) n)) ans = Some (o1, (st2, Some (g, idx))) ->
  m_mem (get_meta_rec st2 g) = Some b ->
  (s_regions st) !! (fst b) = None ->
  (s_groups st2) !! (fst b, 0) <> None ->
  (forall b' h, (s_groups st2) !! b' = Some h -> fst b' = fst b -> b' = (fst b, 0)) ->
  0 <= off -> 16 * off + n + IB <= get_stride (get_meta_rec st2 g) -> 0 <= k < n ->
  let r := enframe_at st2 g idx n off in
  fst (snd r) = fst b /\ cell_read (get_shadow (fst r) (fst b)) (snd (snd r) + k) = Known 0.
Proof.
  intros AR Hn FL Hmem R0 G0 GONLY Ho FIT Hk.
  destruct (areach_inv resv st LB AR) as (L & LS & BL & INV & _).
  apply (malloc_core_fresh_known0' st LB n o ans o1 st2 g idx b off k AR Hn FL Hmem); [| split; [exact G0| exact GONLY]| exact Ho| exact FIT| exact Hk].
  intros bq hq Hbq E. destruct (ig_region _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 INV))))) _ _ Hbq) as (rq & Hrq & _).
  rewrite E, R0 in Hrq. discriminate.
Qed.




Theorem malloc_core_single_use_fresh st LB n (o : mem) ans o1 st2 g idx b :
  AREACH_from resv st LB -> 0 <= n ->
  follow (mrun o (malloc_core full_lay (set_tick (N.succ (s_tick st)) st) n)) ans = Some (o1, (st2, Some (g, idx))) ->
  m_mem (get_meta_rec st2 g) = Some b -> single_use (get_meta_rec st2 g) ->
  gnone st (fst b) /\ gonly0 st2 (fst b).
Proof.
  intros AR Hn FL Hmem SU2.
  destruct (malloc_core_leaf st LB n o ans o1 st2 g idx AR Hn FL) as (L & LS & BL & L2 & LS2 & bg & INV & CR & GX & Hh & Hidx & INV2 & ORG).
  set (X2 := MI_WFree2.xpend x0 _) in INV2.
  assert (Eb : bg = b).
  { pose proof (hosts_mem X2 st2 LS2 (proj1 (proj2 (proj2 INV2))) _ _ Hh) as M. unfold MR in M. rewrite Hmem in M. inversion M. reflexivity. }
  subst bg.
  destruct ORG as [(_ & _ & NS)|[[GN GO]|[SC STD]]].
  - exfalso.
    destruct NS as [S E]. unfold single_use, MR in *. lia.
  - split; [| exact GO]. intros bq hq Hbq E. exact (GN bq hq Hbq E).
  - exfalso. unfold single_use, MR in *. lia.
Qed.

Theorem malloc_core_single_use_known0 st LB n (o : mem) ans o1 st2 g idx b off k :
  AREACH_from resv st LB -> 0 <= n ->
  follow (mrun o (malloc_core full_lay (set_tick (N.succ (s_tick st)) st) n)) ans = Some (o1, (st2, Some (g, idx))) ->
  m_mem (get_meta_rec st2 g) = Some b -> single_use (get_meta_rec st2 g) ->
  0 <= off -> 16 * off + n + IB <= get_stride (get_meta_rec st2 g) -> 0 <= k < n ->
  let r := enframe_at st2 g idx n off in
  fst (snd r) = fst b /\ cell_read (get_shadow (fst r) (fst b)) (snd (snd r) + k) = Known 0.
Proof.
  intros AR Hn FL Hmem SU2 Ho FIT Hk.
  destruct (malloc_core_single_use_fresh st LB n o ans o1 st2 g idx b AR Hn FL Hmem SU2) as [GN GO].
  exact (malloc_core_fresh_known0' st LB n o ans o1 st2 g idx b off k AR Hn FL Hmem GN GO Ho FIT Hk).
Qed.
End FRESH.
