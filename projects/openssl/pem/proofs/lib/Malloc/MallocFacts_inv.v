(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From OSSVerify.Proofs.openssl.pem.lib.Spec Require Import STree Malloc MallocCtrl KInv MI_Tree MI_Inv MI_Kit MI_Geom MI_Ext
  MI_WFree MI_WFree2 MI_WNtf2 MI_TF2 MI_WSlot MI_WMalloc MI_Sim MI_Contracts MI_Pres2 MI_Arith.
From OSSVerify.Proofs.openssl.pem.lib.Malloc Require Import MallocRep MallocTree MallocBlocks.
Import ListNotations.
Local Open Scope Z_scope.

(* [comment removed for export] *)
From OSSVerify.Proofs.openssl.pem.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.openssl.pem.lib.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_lia__].
Local Ltac std_nia__ := nia.
Local Ltac nia := first [std_nia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_nia__].
Section WithCeiling0. Context {CE__ : Ceiling}.
Definition corr1 (st : mstate) (b : block) (k : blk) : Prop :=
  blk_slot b = bslot k /\ blk_size b = bsize k /\ blk_addr b = conc st (bslot k) + UNIT * boff k.
Definition CORR (st : mstate) (LB : list block) (BL : list blk) : Prop := Forall2 (corr1 st) LB BL.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma blk_region X st L BL LS k : INVL X st L BL LS -> In k BL ->
  exists r, s_regions st !! fst (bslot k) = Some r /\ r_kind r = RKGroup.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros INV Hk. pose proof INV as (IR & IA & IM & IL & IG & IS & ISH).
  destruct (is_blocks _ _ _ IS k Hk) as (m & i & Hs & _).
  destruct (is_valid _ _ _ IS _ _ _ Hs) as ([b Hb] & _ & Es).
  rewrite (slot_start'_eq _ _ _ IM _ _ i Hb) in Es. rewrite Es. cbn [fst].
  destruct Hb as [ai Hb]. exact (ig_region _ _ _ IG _ _ Hb).
Qed.

Lemma conc_aadd st p d : (exists r, s_regions st !! fst p = Some r) -> conc st (aadd p d) = conc st p + d.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__). intros [r Hr]. unfold conc, get_region, aadd. cbn. rewrite Hr. lia. Qed.

Lemma conc_same st st' p : (exists r, s_regions st !! fst p = Some r /\ s_regions st' !! fst p = Some r) -> conc st' p = conc st p.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__). intros (r & H1 & H2). unfold conc, get_region. rewrite H1, H2. reflexivity. Qed.

Lemma event_post_resv L e z : ld_resv (event_post L e z) = ld_resv L.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  destruct e as [rq|a len prot flags|a len|a len prot|p c h|w]; cbn; try reflexivity.
  - destruct (rq =? 0); [reflexivity|]. destruct (z =? rq); [| reflexivity]. destruct (ld_brk L); try reflexivity; destruct (ld_brkreg L) as [[b l]|]; reflexivity.
  - destruct (Z.land flags MAP_FIXED =? 0); [| reflexivity]. destruct (is_err z); [reflexivity|]. destruct (prot =? PROT_NONE); reflexivity.
  - destruct ((z =? 0) || (z =? TWO64 - ENOSYS)); reflexivity.
Qed.
Lemma cpath_resv {R} L (t : M R) L' r : cpath L t L' r -> ld_resv L' = ld_resv L.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__). induction 1; [reflexivity|]. rewrite IHcpath. apply event_post_resv. Qed.

Lemma Forall2_In_l {A B} (P : A -> B -> Prop) l1 l2 a : Forall2 P l1 l2 -> In a l1 -> exists b, In b l2 /\ P a b.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  induction 1 as [|x y l1' l2' Hxy H IH]; intros Hin; [destruct Hin|].
  destruct Hin as [<-|Hin]; [exists y; split; [left; reflexivity| exact Hxy]|].
  destruct (IH Hin) as (b & Hb & Pb). exists b. split; [right; exact Hb| exact Pb].
Qed.

Lemma Forall2_impl_in {A B} (P Q : A -> B -> Prop) l1 l2 :
  Forall2 P l1 l2 -> (forall a b, In a l1 -> In b l2 -> P a b -> Q a b) -> Forall2 Q l1 l2.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  induction 1 as [|x y l1' l2' Hxy H IH]; intros HPQ; constructor.
  - apply HPQ; [left; reflexivity| left; reflexivity| exact Hxy].
  - apply IH. intros a b Ha Hb. apply HPQ; right; assumption.
Qed.

Lemma Forall2_filter {A B} (P : A -> B -> Prop) (p : A -> bool) (q : B -> bool) l1 l2 :
  Forall2 P l1 l2 -> (forall a b, P a b -> p a = q b) -> Forall2 P (filter p l1) (filter q l2).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  induction 1 as [|x y l1' l2' Hxy H IH]; intros E; cbn; [constructor|].
  rewrite (E _ _ Hxy). destruct (q y); [constructor; [exact Hxy| apply IH; exact E]| apply IH; exact E].
Qed.

Lemma Forall2_map_eq {A B C} (P : A -> B -> Prop) (f : A -> C) (g : B -> C) l1 l2 :
  Forall2 P l1 l2 -> (forall a b, P a b -> f a = g b) -> map f l1 = map g l2.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__). induction 1; intros E; cbn; [reflexivity|]. rewrite (E _ _ H). f_equal. apply IHForall2. exact E. Qed.

Lemma filter_id {A} (p : A -> bool) l : (forall x, In x l -> p x = true) -> filter p l = l.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  induction l as [|x l IH]; intros H; cbn; [reflexivity|].
  rewrite (H x ltac:(left; reflexivity)). f_equal. apply IH. intros y Hy. apply H. right. exact Hy.
Qed.

Lemma bl_remove_filter c BL : NoDup (map bslot BL) ->
  bl_remove c BL = filter (fun k => negb (aptr_eqb (bslot k) c)) BL.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  induction BL as [|k BL IH]; intros ND; cbn; [reflexivity|].
  cbn in ND. apply NoDup_cons in ND as [NI ND].
  destruct (aptr_eqb_spec (bslot k) c) as [E|NE]; cbn.
  - symmetry. apply filter_id. intros y Hy. destruct (aptr_eqb_spec (bslot y) c) as [E'|NE']; [| reflexivity].
    exfalso. apply NI. apply list_elem_of_In. rewrite E, <- E'. apply in_map. exact Hy.
  - f_equal. apply IH. exact ND.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Theorem areach_inv resv st LB : AREACH_from resv st LB ->
  exists L LS BL, INVL x0 st L BL LS /\ ld_live L = map bslot BL /\ ld_resv L = resv /\ s_secret st = 0 /\ CORR st LB BL.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  induction 1 as [|st LB n o o' ans st' pf cst c AR IH Hn FF FC|st LB n o o' ans st' AR IH Hn FF|st LB b pf o o' ans st' AR IH Hb Hfst Hconc FF
                 |st LB b off' n' st' AR IH Hb RF].
  - exists (led_init resv), (fun _ => []), []. split; [apply INVL_init; lia|]. repeat split; try reflexivity. constructor.
  - destruct IH as (L & LS & BL & INV & LIVE & RESV & SEC & CR).
    destruct (malloc_sim pans_mem pupd_mem pans_mem_range st L BL LS n o ans o' st' (Some pf) INV Hn FF) as (rc & FT & CP & LIVE' & [GPR GPS] & RES).
    unfold mrun in FC |- *. rewrite FC in FT. inversion FT. subst cst rc.
    destruct RES as (off & LS' & Epf & Hoff & INV' & NI).
    set (L' := lafter L (cmalloc (strip st) n) ans) in *.
    exists (set_live (map bslot (((c, off), n) :: BL)) L'), LS', (((c, off), n) :: BL).
    split; [apply INVL_set_live; exact INV'|]. split; [reflexivity|]. split; [cbn; rewrite (cpath_resv _ _ _ _ CP); exact RESV|].
    split; [rewrite GPS; exact SEC|].
    constructor.
    + split; [reflexivity|]. split; [reflexivity|]. cbn [blk_addr bslot boff fst snd]. rewrite Epf. apply conc_aadd.
      destruct (blk_region _ _ _ _ _ ((c, off), n) INV' ltac:(left; reflexivity)) as (r & Hr & _). exists r. exact Hr.
    + eapply Forall2_impl_in; [exact CR|]. intros b k Hb Hk (C1 & C2 & C3). split; [exact C1|]. split; [exact C2|]. rewrite C3.
      rewrite (conc_same st st' (bslot k)); [reflexivity|].
      destruct (blk_region _ _ _ _ _ k INV Hk) as (r & Hr & Kr). exists r. split; [exact Hr| exact (GPR _ _ Hr Kr)].
  - destruct IH as (L & LS & BL & INV & LIVE & RESV & SEC & CR).
    destruct (malloc_sim pans_mem pupd_mem pans_mem_range st L BL LS n o ans o' st' None INV Hn FF) as (rc & FT & CP & LIVE' & [GPR GPS] & RES).
    destruct rc as [c|]; [destruct RES|]. destruct RES as (LS' & INV').
    set (L' := lafter L (cmalloc (strip st) n) ans) in *.
    exists (set_live (map bslot BL) L'), LS', BL.
    split; [apply INVL_set_live; exact INV'|]. split; [reflexivity|]. split; [cbn; rewrite (cpath_resv _ _ _ _ CP); exact RESV|].
    split; [rewrite GPS; exact SEC|].
    eapply Forall2_impl_in; [exact CR|]. intros bb k Hb Hk (C1 & C2 & C3). split; [exact C1|]. split; [exact C2|]. rewrite C3.
    rewrite (conc_same st st' (bslot k)); [reflexivity|].
    destruct (blk_region _ _ _ _ _ k INV Hk) as (r & Hr & Kr). exists r. split; [exact Hr| exact (GPR _ _ Hr Kr)].
  - destruct IH as (L & LS & BL & INV & LIVE & RESV & SEC & CR).
    destruct (Forall2_In_l _ _ _ _ CR Hb) as (k & Hk & (C1 & C2 & C3)).
    destruct k as [[c off] n]. cbn [bslot boff bsize fst snd] in C1, C2, C3.
    destruct (blk_region _ _ _ _ _ ((c, off), n) INV Hk) as (r & Hr & Kr). cbn [bslot fst snd] in Hr.
    assert (Epf : pf = aadd c (UNIT * off)).
    { unfold conc, get_region in Hconc, C3. rewrite Hfst, C1 in Hconc. rewrite Hr in Hconc, C3. rewrite C3 in Hconc.
      apply injective_projections; unfold aadd; cbn [fst snd]; [rewrite Hfst, C1; reflexivity| lia]. }
    subst pf.
    destruct (free_sim pans_mem pupd_mem pans_mem_range st L BL LS c off n o ans o' st' INV Hk FF) as (FT & CP & LIVE' & LS' & INV').
    destruct (free_leaf_facts pans_mem pupd_mem st L BL LS c off n o ans o' st' INV Hk FF) as [SUB SEC'].
    set (L' := lafter L (cfree (strip st) (Some c)) ans) in *.
    exists (set_live (map bslot (bl_remove c BL)) L'), LS', (bl_remove c BL).
    split; [apply INVL_set_live; exact INV'|]. split; [reflexivity|]. split; [cbn; rewrite (cpath_resv _ _ _ _ CP); exact RESV|].
    split; [rewrite SEC'; exact SEC|].
    rewrite (bl_remove_filter c BL (is_nodup _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV)))))))).
    rewrite C1.
    pose proof (Forall2_filter (corr1 st) (fun b' : block => negb (aptr_eqb (blk_slot b') c)) (fun k0 : blk => negb (aptr_eqb (bslot k0) c)) LB BL CR
                  ltac:(intros b' k' (D1 & _ & _); rewrite D1; reflexivity)) as CRF.
    eapply Forall2_impl_in; [exact CRF|]. intros b' k' Hb' Hk' (D1 & D2 & D3). split; [exact D1|]. split; [exact D2|]. rewrite D3.
    rewrite (conc_same st st' (bslot k')); [reflexivity|].
    rewrite <- (bl_remove_filter c BL (is_nodup _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV)))))))) in Hk'.
    destruct (blk_region _ _ _ _ _ k' INV' Hk') as (r' & Hr' & _). exists r'. split; [exact (SUB _ _ Hr')| exact Hr'].
  - (* [comment removed for export] *)
    destruct IH as (L & LS & BL & INV & LIVE & RESV & SEC & CR).
    destruct (Forall2_In_l _ _ _ _ CR Hb) as (k & Hk & (C1 & C2 & C3)).
    destruct RF as (RG & SC & RI).
    assert (Ek : k = ((blk_slot b, (blk_addr b - conc st (blk_slot b)) / UNIT), blk_size b)).
    { destruct k as [[c0 o0] n0]. cbn [bslot boff bsize fst snd] in C1, C2, C3. rewrite C1, C2, C3.
      replace (conc st c0 + UNIT * o0 - conc st c0) with (o0 * UNIT) by lia. rewrite Z.div_mul by (unfold UNIT; lia). reflexivity. }
    rewrite Ek in Hk.
    pose proof (RI L BL LS INV Hk) as INV'.
    assert (CONC : forall q, conc st' q = conc st q) by (intros q; unfold conc, get_region; rewrite RG; reflexivity).
    exists (set_live (map bslot (((blk_slot b, off'), n') :: bl_remove (blk_slot b) BL)) L), LS, (((blk_slot b, off'), n') :: bl_remove (blk_slot b) BL).
    split; [apply INVL_set_live; exact INV'|]. split; [reflexivity|]. split; [cbn; exact RESV|].
    split; [rewrite SC; exact SEC|].
    constructor.
    + split; [reflexivity|]. split; [reflexivity|]. cbn [blk_addr blk_id bslot boff fst snd]. rewrite CONC. reflexivity.
    + rewrite (bl_remove_filter (blk_slot b) BL (is_nodup _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV)))))))).
      pose proof (Forall2_filter (corr1 st) (fun b' : block => negb (aptr_eqb (blk_slot b') (blk_slot b))) (fun k0 : blk => negb (aptr_eqb (bslot k0) (blk_slot b))) LB BL CR
                    ltac:(intros b' k' (D1 & _ & _); rewrite D1; reflexivity)) as CRF.
      eapply Forall2_impl_in; [exact CRF|]. intros b' k' Hb' Hk' (D1 & D2 & D3). split; [exact D1|]. split; [exact D2|]. rewrite D3.
      rewrite CONC. reflexivity.
Qed.


(* [comment removed for export] *)
Lemma areach_hdr_ok_proof : forall {resv} st LB (blk : block) (off : Z),
  AREACH_from resv st LB -> In blk LB -> 0 <= off -> blk_addr blk = conc st (blk_slot blk) + UNIT * off ->
  hdr_ok pans_mem pupd_mem st (aadd (blk_slot blk) (UNIT * off)) (blk_slot blk).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros resv st LB blk off AR Hb Ho Ha.
  destruct (areach_inv resv st LB AR) as (L & LS & BL & INV & _ & _ & _ & CR).
  destruct (Forall2_In_l _ _ _ _ CR Hb) as (k & Hk & (C1 & C2 & C3)).
  destruct k as [[c bo] n]. cbn [bslot boff bsize fst snd] in C1, C2, C3. rewrite C1 in Ha |- *.
  assert (off = bo) by (unfold UNIT in *; lia). subst off.
  exact (INVL_hdr_ok pans_mem pupd_mem st L BL LS c bo n INV Hk).
Qed.

(* [comment removed for export] *)
Lemma areach_malloc_fresh : forall {resv} st LB n (o o' : mem) ans st' (pf : aptr) cst (c : cptr),
  AREACH_from resv st LB -> 0 <= n ->
  follow (mrun o (malloc st n)) ans = Some (o', (st', Some pf)) ->
  follow (cmalloc (strip st) n) ans = Some (cst, Some c) ->
  exists off, pf = aadd c (UNIT * off) /\ 0 <= off <= 255
    /\ (n < MMAP_THRESHOLD -> exists g idx, s_slots st' !! c = Some (g, idx) /\ m_sizeclass (MR st' g) < 48).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros resv st LB n o o' ans st' pf cst c AR Hn FF FC.
  destruct (areach_inv resv st LB AR) as (L & LS & BL & INV & _).
  destruct (malloc_sim pans_mem pupd_mem pans_mem_range st L BL LS n o ans o' st' (Some pf) INV Hn FF) as (rc & FT & _ & _ & _ & RES).
  unfold mrun in FC. rewrite FC in FT. inversion FT. subst cst rc.
  destruct RES as (off & LS' & Epf & Hoff & _ & _ & CLS).
  exists off. split; [exact Epf|]. split; [exact Hoff| exact CLS].
Qed.

(* [comment removed for export] *)
Lemma areach_blk_facts : forall {resv} st LB (blk : block) (off : Z),
  AREACH_from resv st LB -> In blk LB -> 0 <= off -> blk_addr blk = conc st (blk_slot blk) + UNIT * off ->
  exists g bg i ai a ar ka, blk_facts st (blk_slot blk) off (blk_size blk) g bg i ai a ar ka
    /\ (m_sizeclass (MR st g) < 48 -> get_stride (MR st g) * (m_last_idx (MR st g) + 1) < 2 ^ 20)
    /\ (forall b' gh, s_groups st !! b' = Some gh -> fst b' = fst bg ->
          snd b' + 9 <= sstart (MR st g) i - 4 \/ sstart (MR st g) (i + 1) - 4 <= snd b').
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros resv st LB blk off AR Hb Ho Ha.
  destruct (areach_inv resv st LB AR) as (L & LS & BL & INV & _ & _ & _ & CR).
  destruct (Forall2_In_l _ _ _ _ CR Hb) as (k & Hk & (C1 & C2 & C3)).
  destruct k as [[c bo] n]. cbn [bslot boff bsize fst snd] in C1, C2, C3. rewrite C1 in Ha |- *.
  assert (off = bo) by (unfold UNIT in *; lia). subst off. rewrite C2.
  destruct (block_facts x0 st L BL LS INV c bo n Hk) as (g & bg & i & ai & a & ar & ka & BF).
  exists g, bg, i, ai, a, ar, ka. split; [exact BF|].
  pose proof INV as (IR & IA & IM & IL & IG & IS & ISH).
  pose proof (bf_hosts _ _ _ _ _ _ _ _ _ _ _ BF) as Hbg. pose proof (bf_i _ _ _ _ _ _ _ _ _ _ _ BF) as Hi.
  assert (HH : hosts st bg g) by (exists ai; exact Hbg).
  split.
  - intros H48. pose proof (ig_ok _ _ _ IG _ _ _ Hbg) as GO. destruct (g_stride _ _ _ _ _ _ GO H48) as (_ & _ & LT).
    unfold cnt_of in LT. exact LT.
  - intros b' gh Hgh Hf.
    assert (NH : s_groups st !! (fst bg, sstart (MR st g) i) = None).
    { rewrite <- (bf_c _ _ _ _ _ _ _ _ _ _ _ BF). exact (bf_notH _ _ _ _ _ _ _ _ _ _ _ BF). }
    destruct gh as [[m2|] ai2]; [| exfalso; exact (ig_nometa _ _ _ IG _ _ Hgh)].
    assert (H2 : hosts st b' m2) by (exists ai2; exact Hgh).
    destruct (sep_ghdr _ _ _ _ IM IG IS g bg i HH Hi NH m2 b' H2 Hf) as [A|A]; lia.
Qed.

(* [comment removed for export] *)
Lemma blk_meta_guards : forall st c off n g bg i ai a ar ka, blk_facts st c off n g bg i ai a ar ka ->
  let q := (snd c + UNIT * off - snd bg - UNIT) / UNIT in
  let sc := m_sizeclass (MR st g) in
  UNIT * q = get_stride (MR st g) * i + UNIT * off /\ 0 <= q < 2 ^ 16
  /\ (sc < 48 -> size_class sc * i <= q < size_class sc * (i + 1))
  /\ (48 <= sc -> sc = 63)
  /\ (m_maplen (MR st g) <> 0 -> q <= m_maplen (MR st g) * 256 - 1).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros st c off n g bg i ai a ar ka BF q sc.
  pose proof (q16 st c off n g bg i ai a ar ka BF) as [Q1 Q2]. cbn [aadd snd] in Q1, Q2. fold q in Q1, Q2.
  pose proof (bf_fit _ _ _ _ _ _ _ _ _ _ _ BF) as FIT. pose proof (bf_n _ _ _ _ _ _ _ _ _ _ _ BF) as N0.
  pose proof (bf_off _ _ _ _ _ _ _ _ _ _ _ BF) as OFF. pose proof (bf_i _ _ _ _ _ _ _ _ _ _ _ BF) as Hi.
  pose proof (bf_stride _ _ _ _ _ _ _ _ _ _ _ BF) as [S1 _].
  split; [exact Q1|]. split; [exact Q2|]. unfold UNIT, IB in *.
  destruct (bf_sc _ _ _ _ _ _ _ _ _ _ _ BF) as [(Hsc & Hle & Hst)| E63].
  - fold sc in Hsc, Hle, Hst. pose proof (size_class_bound _ Hsc) as SB.
    assert (A : get_stride (MR st g) = 16 * size_class sc \/ m_last_idx (MR st g) = 0) by tauto.
    assert (B : get_stride (MR st g) <= 16 * size_class sc \/ 292 <= size_class sc).
    { destruct Hle as [Hle|H28]; [left; exact Hle| right; apply size_class_28; lia]. }
    split; [intros _; exact (guard16_arith _ _ _ _ _ _ _ (proj1 SB) Q1 FIT N0 OFF Hi A B)|].
    split; [intros H; lia|].
    intros NM. destruct (bf_top _ _ _ _ _ _ _ _ _ _ _ BF NM) as [B0 GE].
    unfold gend, cnt_of, sstart in GE. rewrite (gbase_bm st c off n g bg i ai a ar ka BF), B0 in GE. unfold UNIT in GE.
    pose proof (guard17_arith (get_stride (MR st g)) i off n q (m_last_idx (MR st g)) (m_maplen (MR st g)) S1 Q1 FIT N0 (proj1 OFF) Hi ltac:(lia)) as G17.
    replace (m_maplen (MR st g) * 4096 / 16) with (m_maplen (MR st g) * 256) in G17 by (rewrite <- (Z.div_mul (m_maplen (MR st g) * 256) 16) by lia; f_equal; lia).
    exact G17.
  - fold sc in E63. split; [intros H; lia|]. split; [intros _; exact E63|].
    intros NM. destruct (bf_top _ _ _ _ _ _ _ _ _ _ _ BF NM) as [B0 GE].
      unfold gend, cnt_of, sstart in GE. rewrite (gbase_bm st c off n g bg i ai a ar ka BF), B0 in GE. unfold UNIT in GE.
      pose proof (guard17_arith (get_stride (MR st g)) i off n q (m_last_idx (MR st g)) (m_maplen (MR st g)) S1 Q1 FIT N0 (proj1 OFF) Hi ltac:(lia)) as G17.
      replace (m_maplen (MR st g) * 4096 / 16) with (m_maplen (MR st g) * 256) in G17 by (rewrite <- (Z.div_mul (m_maplen (MR st g) * 256) 16) by lia; f_equal; lia).
      exact G17.
Qed.
End WithCeiling0.
