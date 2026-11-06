(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From stdpp Require Import gmap.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec Require STree Malloc MallocCtrl KInv MI_Tree MI_Inv MI_Kit MI_Arith MI_Geom MI_List MI_Ext MI_Pres1 MI_Pres3 MI_Pres4 MI_WFree2.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec Require MI_Bits.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec Require MI_TF2 MI_WSlot MI_WSlot2 MI_Ledger MI_Contracts MShapeA MShapeB MShapeC.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec.STree OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec.Malloc OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec.MallocCtrl OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec.KInv OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec.MI_Tree OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec.MI_Inv OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec.MI_Kit OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec.MI_Arith OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec.MI_Geom OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec.MI_List OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec.MI_Ext OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec.MI_Pres1 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec.MI_Pres3 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec.MI_Pres4 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec.MI_WFree2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec.MI_Bits.MI_Cnt OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec.MI_TF2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec.MI_WSlot OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec.MI_WSlot2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec.MI_Ledger OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec.MI_Contracts OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec.MShapeA OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec.MShapeB OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec.MShapeC.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
Section ACeilS1. Context {ACEIL__ : ACeil}.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition FILE_CLASS : Z := 21.

(* [comment removed for export] *)
Record C21 (W : list cptr) (cs : mstate) : Prop := mkC21 {
  c21_three : forall g b, hosts cs b g -> m_sizeclass (MR cs g) = FILE_CLASS -> m_last_idx (MR cs g) = 2;
  c21_uniq : forall g g' b b', hosts cs b g -> hosts cs b' g' ->
      m_sizeclass (MR cs g) = FILE_CLASS -> m_sizeclass (MR cs g') = FILE_CLASS -> g = g';
  c21_occ : forall g b i, hosts cs b g -> m_sizeclass (MR cs g) = FILE_CLASS -> 0 <= i <= 2 ->
      tbit (m_avail (MR cs g)) i = true \/ tbit (m_freed (MR cs g)) i = true \/ In (fst b, sstart (MR cs g) i) W
}.

(* [comment removed for export] *)
Definition C21none (cs : mstate) : Prop := forall g b, hosts cs b g -> m_last_idx (MR cs g) = 0.

Lemma C21_strip W st : C21 W st <-> C21 W (strip st).
Proof. split; intros [A B C]; constructor; assumption. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma C21none_no21 X st L BL LS g b : INVL X st L BL LS -> C21none st -> hosts st b g -> m_sizeclass (MR st g) = FILE_CLASS -> False.
Proof.
  intros INV HN Hh Hs. pose proof (HN g b Hh) as L0.
  cps_destruct (hosts_ok X st LS (proj1 (proj2 (proj2 (proj2 (proj2 INV))))) b g Hh) as (ai & Hb & GO).
  destruct (g_sc _ _ _ _ _ _ GO) as [[SC _]|(SC & _)]; [| unfold FILE_CLASS in Hs; lia].
  cps_destruct (g_stride _ _ _ _ _ _ GO ltac:(lia)) as (_ & L27 & _). specialize (L27 L0). unfold FILE_CLASS in Hs. lia.
Qed.

(* [comment removed for export] *)


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma AFR_unstrip C d e st st1 : AFR C d e (strip st) (strip st1) -> AFR C d e st st1.
Proof. intros [A1 A2 A3 A4 A5]. constructor; [exact A1| exact A2| exact A3| exact A4| exact A5]. Qed.

Section FRAME.
Variables (W W' : list cptr) (st st' : mstate) (L L' : mled) (BL BL' : list blk) (LS LS' : lhead -> list aptr) (C : Z -> Prop) (d : Z) (e : optr).
Hypothesis INV : INVL x0 st L BL LS.
Hypothesis INV' : INVL x0 st' L' BL' LS'.
Hypothesis AF : AFR C d e st st'.
(* [comment removed for export] *)
Hypothesis NC : forall x b, hosts st' b x -> m_sizeclass (MR st' x) = FILE_CLASS -> exists b0, hosts st b0 x.
(* [comment removed for export] *)
Hypothesis NEWB : forall x, In x (map bslot BL') -> In x (map bslot BL) \/ In x W' \/
   exists g bg idx, hosts st' bg g /\ m_sizeclass (MR st' g) <> FILE_CLASS /\ 0 <= idx <= m_last_idx (MR st' g) /\ x = (fst bg, sstart (MR st' g) idx).
Hypothesis HW : forall x, In x W -> In x W'.
Hypothesis HC : C21 W st.

Let IMx := proj1 (proj2 (proj2 INV)).
Let IGx := proj1 (proj2 (proj2 (proj2 (proj2 INV)))).
Let ISx := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV))))).
Let IMx' := proj1 (proj2 (proj2 INV')).
Let IGx' := proj1 (proj2 (proj2 (proj2 (proj2 INV')))).
Let ISx' := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV'))))).

Lemma C21_frame : C21 W' st'.
Proof.
  destruct AF as [A1 A2 A3 A4 A5]. destruct HC as [T1 T2 T3].
  assert (OLD : forall g b, hosts st' b g -> m_sizeclass (MR st' g) = FILE_CLASS -> hosts st b g /\ geo_of (MR st' g) = geo_of (MR st g)).
  { intros g b Hh Hs. destruct (NC g b Hh Hs) as [b0 H0]. destruct (A3 b0 g H0) as [H1 G].
    pose proof (hosts_inj x0 st' LS' IMx' _ _ _ Hh H1) as ->. auto. }
  constructor.
  - intros g b Hh Hs. destruct (OLD g b Hh Hs) as (H0 & G). rewrite (geo_li _ _ G). apply (T1 g b H0). rewrite <- (geo_sc _ _ G). exact Hs.
  - intros g g' b b' Hh Hh' Hs Hs'. destruct (OLD g b Hh Hs) as (H0 & G). destruct (OLD g' b' Hh' Hs') as (H0' & G').
    apply (T2 g g' b b' H0 H0'); [rewrite <- (geo_sc _ _ G); exact Hs| rewrite <- (geo_sc _ _ G'); exact Hs'].
  - intros g b i Hh Hs Hi. destruct (OLD g b Hh Hs) as (H0 & G).
    assert (Hs0 : m_sizeclass (MR st g) = FILE_CLASS) by (rewrite <- (geo_sc _ _ G); exact Hs).
    rewrite (geo_ss _ _ i G).
    assert (BBN : (tbit (m_avail (MR st g)) i = true \/ tbit (m_freed (MR st g)) i = true) \/ In (fst b, sstart (MR st g) i) W).
    { destruct (T3 g b i H0 Hs0 Hi) as [Bt|[Bt|Nm]]; [left; left; exact Bt| left; right; exact Bt| right; exact Nm]. }
    destruct BBN as [BB|Nm]; [| right; right; apply HW; exact Nm].
    pose proof (T1 g b H0 Hs0) as LI.
    cps_destruct (hosts_ok x0 st' LS' IGx' b g Hh) as (ai' & Hb' & GO').
    cps_destruct (hosts_ok x0 st LS IGx b g H0) as (ai & Hb & GO).
    assert (LI' : m_last_idx (MR st' g) = 2) by (rewrite (geo_li _ _ G); exact LI).
    pose proof (is_part _ _ _ ISx' b g ai' i Hb' ltac:(lia)) as ONE'.
    pose proof (is_part _ _ _ ISx b g ai i Hb ltac:(lia)) as ONE.
    rewrite (slot_start'_eq _ _ _ IMx' _ _ i ltac:(exists ai'; exact Hb')) in ONE'.
    rewrite (slot_start'_eq _ _ _ IMx _ _ i ltac:(exists ai; exact Hb)) in ONE.
    cbn zeta in ONE, ONE'.
    rewrite (geo_ss _ _ i G) in ONE'.
    cps_destruct ONE as (_ & AB & AC & AD & AE & BC & BD & BE & _).
    destruct ONE' as (D5 & _).
    assert (NOBLK : ~ In (fst b, sstart (MR st g) i) (map bslot BL)) by (intros Ho; destruct BB as [Bt|Bt]; [exact (AC (conj Bt Ho))| exact (BC (conj Bt Ho))]).
    assert (NOGRP : ~ (s_groups st !! (fst b, sstart (MR st g) i) <> None)) by (intros Ho; destruct BB as [Bt|Bt]; [exact (AD (conj Bt Ho))| exact (BD (conj Bt Ho))]).
    pose proof (is_total _ _ _ ISx' b g i ltac:(exists ai'; exact Hb') ltac:(lia)) as S1.
    rewrite (slot_start'_eq _ _ _ IMx' _ _ i ltac:(exists ai'; exact Hb')), (geo_ss _ _ i G) in S1.
    destruct (In_dec aptr_eq_dec (fst b, sstart (MR st g) i) W') as [HinW|NinW]; [right; right; exact HinW|].
    assert (NCb : ~ In (fst b, sstart (MR st g) i) (map bslot BL')).
    { intros Hin. destruct (NEWB _ Hin) as [Ho|[Hw|(g2 & bg2 & idx2 & Hh2 & Hs2 & Hi2 & E2)]]; [exact (NOBLK Ho)| exact (NinW Hw)|].
      pose proof (is_total _ _ _ ISx' bg2 g2 idx2 Hh2 Hi2) as S2.
      rewrite (slot_start'_eq _ _ _ IMx' _ _ idx2 Hh2), <- E2, S1 in S2.
      injection S2 as <- _. exact (Hs2 Hs). }
    assert (NDb : ~ (s_groups st' !! (fst b, sstart (MR st g) i) <> None)).
    { intros Hg'. destruct (s_groups st' !! (fst b, sstart (MR st g) i)) as [[mm aa]|] eqn:EG; [| exact (Hg' eq_refl)].
      destruct mm as [x|]; [| exact (ig_nometa _ _ _ IGx' _ _ EG)].
      assert (Hx : hosts st' (fst b, sstart (MR st g) i) x) by (exists aa; exact EG).
      destruct (A4 _ _ Hx) as [Hx0|(Cx & _ & [[RN _]|(_ & p & bp & ip & Hp & Cp & Hip & Ep)])].
      - apply NOGRP. destruct Hx0 as [aa0 E0]. rewrite E0. discriminate.
      - cbn [fst] in RN. exact (hosts_region _ _ _ _ _ _ _ INV H0 RN).
      - pose proof (is_total _ _ _ ISx' bp p ip Hp Hip) as S2.
        rewrite (slot_start'_eq _ _ _ IMx' _ _ ip Hp), <- Ep, S1 in S2.
        injection S2 as <- _. rewrite Hs in Cp. unfold midclass, FILE_CLASS in Cp. lia. }
    cbn [x_pend x0] in D5.
    destruct D5 as [Ha|[Hb2|[Hc|[Hd|He]]]]; [left; exact Ha| right; left; exact Hb2| exfalso; exact (NCb Hc)| exfalso; exact (NDb Hd)| discriminate].
Qed.
End FRAME.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma zsum_zero l : Forall (fun z => z = 0) l -> zsum l = 0.
Proof. induction 1 as [|x l Hx _ IH]; [reflexivity|]. unfold zsum in *. cbn. rewrite IH. lia. Qed.

Lemma no21_usage0 X st L BL LS : INVL X st L BL LS ->
  (forall g b, hosts st b g -> m_sizeclass (MR st g) <> FILE_CLASS) -> usage st FILE_CLASS = 0.
Proof.
  intros INV NO. cps_pose INV as (IR & IA & IM & IL & IG & IS & ISH).
  rewrite (ia_usage _ IA FILE_CLASS) by (unfold FILE_CLASS; lia).
  unfold gcnt. apply zsum_zero. apply Forall_map. apply Forall_forall. intros [b h] Hin. cbn [fst snd].
  apply elem_of_map_to_list in Hin.
  destruct h as [[m|] ai]; cbn [g_meta]; [| reflexivity].
  destruct (Z.eqb_spec (m_sizeclass (MR st m)) FILE_CLASS) as [E|NE]; [| reflexivity].
  exfalso. apply (NO m b); [exists ai; exact Hin| exact E].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma round_up_pg_4096 x : 1 <= x <= 4096 -> round_up_pg x = 4096.
Proof.
  intros Hx. pose proof (round_up_pg_spec x) as [A B].
  pose proof (Z.div_mod (round_up_pg x) 4096 ltac:(lia)) as D. rewrite B in D. nia.
Qed.

Lemma newcnt21 n li : 1 <= n <= 4076 -> NEWCNT FILE_CLASS n 0 li -> li = 2.
Proof.
  intros Hn NC.
  assert (E1 : ag_cnt1 FILE_CLASS 0 = 3) by (vm_compute; reflexivity).
  destruct NC as [(u1 & ns & E & _)|[E _]]; rewrite E1 in E; [| lia].
  assert (E2 : ag_cnt2 FILE_CLASS 3 u1 ns = 3).
  { unfold ag_cnt2. destruct ((u1 <? 4 * 3) && negb ns); [vm_compute| ]; reflexivity. }
  rewrite E2 in E. unfold ag_cn3 in E. cbn zeta in E.
  rewrite (round_up_pg_4096 (n + IB + UNIT)) in E by (unfold IB, UNIT; lia).
  replace (4096 <? UNIT * size_class FILE_CLASS + UNIT) with false in E by (vm_compute; reflexivity).
  replace (4 * PGSZ <=? 4096) with false in E by (vm_compute; reflexivity).
  cbn [andb orb] in E. destruct (negb ns && (3 <=? 7)); cbn [fst] in E; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section HEAD.
Variables (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr) (W : list cptr).
Hypothesis INV : INVL x0 st L BL LS.
Hypothesis HC : C21 W st.
Let IMx := proj1 (proj2 (proj2 INV)).
Let ILx := proj1 (proj2 (proj2 (proj2 INV))).
Let IGx := proj1 (proj2 (proj2 (proj2 (proj2 INV)))).

Lemma c21_head g b i :
  hosts st b g -> m_sizeclass (MR st g) = FILE_CLASS -> 0 <= i <= 2 -> ~ In (fst b, sstart (MR st g) i) W ->
  active st FILE_CLASS = Some g /\ (m_avail (MR st g) <> 0 \/ m_freed (MR st g) <> 0).
Proof.
  intros Hh Hs Hi NW.
  assert (NZ : m_avail (MR st g) <> 0 \/ m_freed (MR st g) <> 0).
  { destruct (c21_occ _ _ HC g b i Hh Hs Hi) as [Bt|[Bt|Nm]]; [left| right| exfalso; exact (NW Nm)];
      intros Z0; unfold tbit in Bt; rewrite Z0, Z.bits_0 in Bt; discriminate. }
  split; [| exact NZ].
  cps_destruct (hosts_ok x0 st LS IGx b g Hh) as (ai & Hb & GO).
  assert (INL : in_list LS g).
  { destruct (Classical_Prop.classic (in_list LS g)) as [Y|N]; [exact Y|]. exfalso.
    destruct (g_unlisted _ _ _ _ _ _ GO ltac:(cbn; discriminate) ltac:(rewrite Hs; unfold FILE_CLASS; lia) N) as [A F]. lia. }
  destruct INL as [h Hin].
  destruct h as [sc|].
  2:{ exfalso. pose proof (il_free _ _ ILx g Hin) as E. pose proof (hosts_mem x0 st LS IMx b g Hh) as M. rewrite E in M. cbn in M. discriminate. }
  cps_destruct (il_active _ _ ILx sc g Hin) as (_ & _ & Esc). rewrite Hs in Esc. subst sc.
  pose proof (il_head _ _ ILx (LActive FILE_CLASS)) as HH. cbn [get_head] in HH.
  destruct (LS (LActive FILE_CLASS)) as [|hd rest] eqn:EL; [destruct Hin|]. cbn [head_of] in HH.
  cps_destruct (il_active _ _ ILx FILE_CLASS hd ltac:(rewrite EL; left; reflexivity)) as (_ & [bh Hbh] & Ehd).
  rewrite (c21_uniq _ _ HC hd g bh b Hbh Hh Ehd Hs) in HH. exact HH.
Qed.
End HEAD.

(* [comment removed for export] *)
Lemma c21_unnamed st X L BL LS g b (c1 : cptr) (w : list cptr) i1 :
  INVL X st L BL LS -> hosts st b g -> (length w <= 1)%nat ->
  0 <= i1 <= 2 -> c1 = (fst b, sstart (MR st g) i1) ->
  exists i, 0 <= i <= 2 /\ ~ In (fst b, sstart (MR st g) i) (c1 :: w).
Proof.
  intros INV Hh Hw Hi1 ->.
  pose proof (stride_ge X st LS (proj1 (proj2 (proj2 (proj2 (proj2 INV))))) b g Hh) as [SG _].
  assert (INJ : forall i j, sstart (MR st g) i = sstart (MR st g) j -> i = j).
  { intros i j E. unfold sstart in E. unfold UNIT in SG. nia. }
  assert (CASE : forall i, 0 <= i <= 2 -> i <> i1 -> (forall x, In x w -> x <> (fst b, sstart (MR st g) i)) ->
                 exists i0, 0 <= i0 <= 2 /\ ~ In (fst b, sstart (MR st g) i0) ((fst b, sstart (MR st g) i1) :: w)).
  { intros i Hi NE NW. exists i. split; [exact Hi|]. intros [E|Hin]; [| exact (NW _ Hin eq_refl)]. injection E as E. apply NE. symmetry. apply INJ. exact E. }
  destruct w as [|x [|y l]]; [| | cbn in Hw; lia].
  - destruct (Z.eq_dec i1 0) as [->|]; [apply (CASE 1); [lia| lia| intros ? []]| apply (CASE 0); [lia| lia| intros ? []]].
  - (* [comment removed for export] *)
    assert (PICK : exists i j, 0 <= i <= 2 /\ 0 <= j <= 2 /\ i <> i1 /\ j <> i1 /\ i <> j).
    { destruct (Z.eq_dec i1 0) as [->|]; [exists 1, 2; lia|]. destruct (Z.eq_dec i1 1) as [->|]; [exists 0, 2; lia| exists 0, 1; lia]. }
    cps_destruct PICK as (i & j & Hi & Hj & Ni & Nj & Nij).
    destruct (aptr_eq_dec x (fst b, sstart (MR st g) i)) as [Ex|Nx].
    + apply (CASE j); [exact Hj| exact Nj|]. intros x' [<-|[]]. rewrite Ex. intros E. injection E as E. apply Nij. apply INJ. exact E.
    + apply (CASE i); [exact Hi| exact Ni|]. intros x' [<-|[]]. exact Nx.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition INSLOT (cs : mstate) (c : cptr) : Prop :=
  exists g b i, hosts cs b g /\ m_sizeclass (MR cs g) = FILE_CLASS /\ 0 <= i <= 2 /\ c = (fst b, sstart (MR cs g) i).

Lemma INSLOT_afr C d e cs cs' c : AFR C d e cs cs' -> INSLOT cs c -> INSLOT cs' c.
Proof.
  (intros [_ _ A3 _ _]; cps_intros (g & b & i & Hh & Hs & Hi & ->)). destruct (A3 b g Hh) as [Hh' G].
  exists g, b, i. rewrite (geo_sc _ _ G), (geo_ss _ _ i G). auto.
Qed.

Lemma INSLOT_strip cs c : INSLOT cs c <-> INSLOT (strip cs) c.
Proof. split; intros H; exact H. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma nonest21 : nonest FILE_CLASS = true.
Proof. vm_compute. reflexivity. Qed.

Section CREATE.
Variables (W : list cptr) (st st' : mstate) (L L' : mled) (BL BL' : list blk) (LS LS' : lhead -> list aptr) (d : Z).
Variables (g : aptr) (bg : aptr) (idx : Z).
Hypothesis INV : INVL x0 st L BL LS.
Hypothesis INV' : INVL x0 st' L' BL' LS'.
Hypothesis AF : AFR (chain FILE_CLASS) d (Some g) st st'.
Hypothesis NO21 : forall x b, hosts st b x -> m_sizeclass (MR st x) <> FILE_CLASS.
Hypothesis Hg : hosts st' bg g.
Hypothesis SCg : m_sizeclass (MR st' g) = FILE_CLASS.
Hypothesis LIg : m_last_idx (MR st' g) = 2.
Hypothesis Hidx : 0 <= idx <= 2.
Hypothesis NEWB : forall x, In x (map bslot BL') -> In x (map bslot BL) \/ x = (fst bg, sstart (MR st' g) idx).

Let IMx := proj1 (proj2 (proj2 INV)).
Let IGx := proj1 (proj2 (proj2 (proj2 (proj2 INV)))).
Let ISx := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV))))).
Let IMx' := proj1 (proj2 (proj2 INV')).
Let IGx' := proj1 (proj2 (proj2 (proj2 (proj2 INV')))).
Let ISx' := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV'))))).

Lemma C21_create : C21 ((fst bg, sstart (MR st' g) idx) :: W) st'.
Proof.
  destruct AF as [A1 A2 A3 A4 A5].
  assert (ONLY : forall x b, hosts st' b x -> m_sizeclass (MR st' x) = FILE_CLASS -> x = g /\ s_regions st !! (fst b) = None /\ snd b = 0).
  { intros x b Hh Hs. destruct (A4 b x Hh) as [H0|(_ & HE & HW)].
    - exfalso. destruct (A3 b x H0) as [_ G]. apply (NO21 x b H0). rewrite <- (geo_sc _ _ G). exact Hs.
    - destruct HE as [HM|HE]; [exfalso; rewrite Hs in HM; unfold midclass, FILE_CLASS in HM; lia|]. injection HE as ->.
      destruct HW as [[RN Z0]|(NN & _)]; [auto|]. exfalso. rewrite Hs, nonest21 in NN. discriminate. }
  cps_destruct (ONLY g bg Hg SCg) as (_ & FR & Z0).
  pose proof (stride_ge x0 st' LS' IGx' bg g Hg) as [SG _].
  assert (SSpos : forall i, 0 <= i -> 16 <= sstart (MR st' g) i).
  { intros i Hi. unfold sstart. rewrite (hosts_gbase x0 st' LS' IMx' bg g Hg), Z0. unfold UNIT in *. nia. }
  constructor.
  - intros x b Hh Hs. destruct (ONLY x b Hh Hs) as (-> & _). exact LIg.
  - intros x x' b b' Hh Hh' Hs Hs'. destruct (ONLY x b Hh Hs) as (-> & _). destruct (ONLY x' b' Hh' Hs') as (-> & _). reflexivity.
  - intros x b i Hh Hs Hi. cps_destruct (ONLY x b Hh Hs) as (-> & FRb & Zb).
    pose proof (hosts_inj x0 st' LS' IMx' _ _ _ Hh Hg) as ->.
    cps_destruct (hosts_ok x0 st' LS' IGx' bg g Hg) as (ai' & Hb' & GO').
    pose proof (is_part _ _ _ ISx' bg g ai' i Hb' ltac:(lia)) as ONE'.
    rewrite (slot_start'_eq _ _ _ IMx' _ _ i Hg) in ONE'. cbn zeta in ONE'. destruct ONE' as (D5 & _).
    pose proof (is_total _ _ _ ISx' bg g i Hg ltac:(lia)) as S1. rewrite (slot_start'_eq _ _ _ IMx' _ _ i Hg) in S1.
    assert (NCb : In (fst bg, sstart (MR st' g) i) (map bslot BL') -> i = idx).
    { intros Hin. destruct (NEWB _ Hin) as [Ho|E].
      - exfalso. apply in_map_iff in Ho as (k & Ek & Hk).
        cps_destruct (is_blocks _ _ _ ISx k Hk) as (m0 & i0 & Sk & _).
        cps_destruct (is_valid _ _ _ ISx _ _ _ Sk) as ([b0 Hm0] & _ & Es).
        rewrite (slot_start'_eq _ _ _ IMx _ _ i0 Hm0) in Es. rewrite Ek in Es.
        assert (Efst : fst b0 = fst bg) by (apply (f_equal fst) in Es; cbn in Es; congruence).
        apply (hosts_region _ _ _ _ _ _ _ INV Hm0). rewrite Efst. exact FR.
      - injection E as E. unfold sstart in E. unfold UNIT in SG. nia. }
    assert (NDb : ~ (s_groups st' !! (fst bg, sstart (MR st' g) i) <> None)).
    { intros Hg'. destruct (s_groups st' !! (fst bg, sstart (MR st' g) i)) as [[mm aa]|] eqn:EG; [| exact (Hg' eq_refl)].
      destruct mm as [x|]; [| exact (ig_nometa _ _ _ IGx' _ _ EG)].
      assert (Hx : hosts st' (fst bg, sstart (MR st' g) i) x) by (exists aa; exact EG).
      destruct (A4 _ _ Hx) as [Hx0|(Cx & HE & [[RN ZZ]|(_ & p & bp & ip & Hp & Cp & Hip & Ep)])].
      - apply (hosts_region _ _ _ _ _ _ _ INV Hx0). cbn [fst]. exact FR.
      - cbn [snd] in ZZ. pose proof (SSpos i ltac:(lia)). lia.
      - pose proof (is_total _ _ _ ISx' bp p ip Hp Hip) as S2.
        rewrite (slot_start'_eq _ _ _ IMx' _ _ ip Hp), <- Ep, S1 in S2.
        injection S2 as <- _. rewrite SCg in Cp. unfold midclass, FILE_CLASS in Cp. lia. }
    cbn [x_pend x0] in D5.
    destruct D5 as [Ha|[Hb2|[Hc|[Hd|He]]]]; [left; exact Ha| right; left; exact Hb2| | exfalso; exact (NDb Hd)| discriminate].
    right. right. left. rewrite (NCb Hc). reflexivity.
Qed.
End CREATE.

End ACeilS1.
