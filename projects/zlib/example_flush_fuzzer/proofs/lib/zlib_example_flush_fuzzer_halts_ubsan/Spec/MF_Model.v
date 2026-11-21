(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.Spec Require Import STree Malloc MallocCtrl KInv MI_Tree MI_Inv MI_Kit MI_Arith MI_Geom MI_List MI_Ext
  MI_WFree2 MI_WTry2 MI_WSlot MI_Cnt MI_WMalloc FreshIface MF_Defs MF_Inv MF_WMalloc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition KC30 (c : Z) : Prop := KCLS c \/ c = 30.
Lemma KC30_dec c : {KC30 c} + {~ KC30 c}.
Proof.
  unfold KC30, KCLS. destruct (Z.eq_dec c 31); [left; lia|]. destruct (Z.eq_dec c 40); [left; lia|].
  destruct (Z.eq_dec c 44); [left; lia|]. destruct (Z.eq_dec c 30); [left; lia|]. right. lia.
Qed.
Lemma crange_vals : crange 31 = (5437, 8172) /\ crange 40 = (32749, 37436) /\ crange 44 = (65517, 74876).
Proof. repeat split; reflexivity. Qed.

Section MALLOC.
Variables (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr) (n : Z) (X : list blk) (k : Z).
Hypothesis INV : INVL x0 st L BL LS.
Hypothesis Hn : 0 <= n.
Hypothesis HF : FF X k st.
Hypothesis HX : forall xb, In xb X -> In (bslot xb) (map bslot BL).
Hypothesis HND : List.NoDup (map bslot X).
Hypothesis HP : FPRE X k n.

Let HG := proj1 HF.
Let HX' : forall xb, In xb X -> In (bslot xb) (map bslot BL) \/ x_pend x0 = Some (bslot xb) := fun xb H => or_introl (HX xb H).

Lemma csel_30 : n < MMAP_THRESHOLD -> size_to_class n = 30 -> csel st n = 31.
Proof.
  intros Hlt E. destruct (FG_no30 x0 st L BL LS X INV HG) as [A30 U30].
  pose proof (size_to_class_K n ltac:(lia)) as (R30 & _). destruct (proj1 R30 E) as [N1 N2].
  assert (U31 : usage st 31 <= 7).
  { pose proof (FG_usage x0 st L BL LS X INV HG HND 31 ltac:(left; reflexivity)) as U. rewrite (proj1 crange_vals) in U. cbn [fst snd] in U. unfold FPRE, C31 in HP. lia. }
  unfold csel. rewrite E, A30. change ((4 <=? 30) && (30 <? 32) && negb (30 =? 6) && Z.even 30) with true. rewrite U30. cbn [Z.eqb andb].
  change (Z.lor 30 1) with 31.
  destruct (active st 31) as [m|] eqn:HA.
  - cbn [default]. fold (MR st m). destruct (FG_head_full x0 st L BL LS X INV HG HX' 31 m ltac:(left; reflexivity) HA) as [A B]. rewrite A, B. cbn [Z.eqb andb].
    replace (usage st 31 + 3 <=? 12) with true by (symmetry; apply Z.leb_le; lia). reflexivity.
  - replace (usage st 31 + 3 <=? 12) with true by (symmetry; apply Z.leb_le; lia). reflexivity.
Qed.

Lemma csel_K : n < MMAP_THRESHOLD -> KC30 (size_to_class n) -> KCLS (csel st n) /\ inrange (csel st n) n.
Proof.
  intros Hlt HK. pose proof (size_to_class_K n ltac:(lia)) as (R30 & R31 & R40 & R44).
  destruct HK as [HK|E30].
  - destruct (csel_cases st n) as [E|(E & EV & R)].
    + rewrite E. split; [exact HK|]. unfold inrange. destruct HK as [E1|[E1|E1]]; rewrite E1 in *; [pose proof (proj1 R31 eq_refl)| pose proof (proj1 R40 eq_refl)| pose proof (proj1 R44 eq_refl)]; lia.
    + exfalso. destruct HK as [E1|[E1|E1]]; rewrite E1 in EV, R; cbn in EV; try discriminate; lia.
  - rewrite (csel_30 Hlt E30). split; [left; reflexivity|]. left. split; [reflexivity|]. destruct (proj1 R30 E30). lia.
Qed.

Lemma csel_notK : n < MMAP_THRESHOLD -> ~ KC30 (size_to_class n) -> ~ KCLS (csel st n) /\ csel st n <> 30.
Proof.
  intros Hlt NK. pose proof (size_to_class_ok n ltac:(lia)) as [SC _].
  destruct (csel_cases st n) as [E|(E & EV & R)]; rewrite E.
  - split; [intros K; apply NK; left; exact K| intros E30; apply NK; right; exact E30].
  - split.
    + intros [E1|[E1|E1]]; try lia. assert (E30 : size_to_class n = 30) by lia. exact (NK (or_intror E30)).
    + intros E30. assert (E29 : size_to_class n = 29) by lia. rewrite E29 in EV. cbn in EV. discriminate.
Qed.

Lemma KPRE_of : n < MMAP_THRESHOLD -> KC30 (size_to_class n) -> KPRE (csel st n) n (usage st (csel st n)).
Proof.
  intros Hlt HK. destruct (csel_K Hlt HK) as [KC IR]. pose proof (FG_usage x0 st L BL LS X INV HG HND _ KC) as U.
  unfold FPRE, C31, C40, C44 in HP. unfold KPRE. unfold inrange in IR.
  destruct crange_vals as (C1 & C2 & C3).
  destruct KC as [E|[E|E]]; rewrite E in *; rewrite ?C1, ?C2, ?C3 in U; cbn [fst snd] in U; repeat split; intros; try lia.
Qed.

Theorem core_FF st1 L1 LS1 g bg idx off :
  (n < MMAP_THRESHOLD -> MFR (csel st n) st st1) -> (MMAP_THRESHOLD <= n -> MFR 63 st st1) ->
  hosts st1 bg g -> 0 <= idx <= m_last_idx (MR st1 g) ->
  INVL (xpend x0 (Some (fst bg, sstart (MR st1 g) idx))) st1 L1 BL LS1 ->
  (n < MMAP_THRESHOLD -> m_sizeclass (MR st1 g) = csel st n /\ XNEW (csel st n) n st st1 g bg) ->
  FF ((((fst bg, sstart (MR st1 g) idx), off), n) :: X) (k + 1) st1
  /\ (n < MMAP_THRESHOLD -> KC30 (size_to_class n) -> idx = 0 /\ s_regions st !! (fst bg) = None /\ snd bg = 0 /\ gonly0 st1 (fst bg)).
Proof.
  intros MFs MFb Hg Hidx INV1 KX.
  pose proof HP as HP0. unfold FPRE in HP0. destruct HP0 as (K98 & _).
  set (c0 := (fst bg, sstart (MR st1 g) idx)) in *.
  assert (NI : ~ In c0 (map bslot BL)).
  { destruct Hg as [ai Hg']. pose proof (is_part _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV1)))))) _ _ _ idx Hg' Hidx) as P. cbn zeta in P.
    rewrite (slot_start'_eq _ _ _ (proj1 (proj2 (proj2 INV1))) _ _ idx (ex_intro _ ai Hg')) in P. fold c0 in P.
    destruct P as (_ & _ & _ & _ & _ & _ & _ & _ & _ & nCE & _). intros C. apply nCE. split; [exact C| reflexivity]. }
  destruct (Z.lt_ge_cases n MMAP_THRESHOLD) as [Hlt|Hge].
  2:{ split; [| intros; lia].
      apply (FF_frame X _ k (k + 1) 63 st st1 HF (MFb Hge)); [intros [E|[E|E]]; lia| lia| intros xb Hxb; right; exact Hxb| lia]. }
  specialize (MFs Hlt). destruct (KX Hlt) as [SCg XN]. clear KX.
  destruct (KC30_dec (size_to_class n)) as [HK|NK].
  -
    destruct (csel_K Hlt HK) as [KC IR]. pose proof (KPRE_of Hlt HK) as KP. destruct HF as [HGx [B1 B2]].
    destruct (XN KC KP B2) as [[[ai0 Hb0] SG]|KN].
    +
      exfalso. destruct (HGx _ _ _ Hb0) as [_ KK]. pose proof SG as (_ & EL & _ & EC). rewrite <- EC, SCg in KK. destruct (KK KC) as [L0 (xb & Hin & Es & _)].
      apply NI. assert (Hi0 : idx = 0) by lia. unfold c0. rewrite Hi0.
      rewrite <- (slot_start'_eq _ _ _ (proj1 (proj2 (proj2 INV1))) _ _ 0 Hg), (same_geo_slot0 _ _ SG), <- Es. exact (HX xb Hin).
    + pose proof KN as (KL & KR & KS & KO & KOTH). destruct Hg as [ai Hg].
      assert (Hi0 : idx = 0) by lia.
      split.
      * apply (FF_knew X k (csel st n) st st1 g bg ai ((c0, off), n) (conj HGx (conj B1 B2)) (proj2 K98) MFs KC KN Hg SCg); [| exact IR].
        cbn [bslot fst]. unfold c0. rewrite Hi0. symmetry. exact (slot_start'_eq _ _ _ (proj1 (proj2 (proj2 INV1))) _ _ 0 (ex_intro _ ai Hg)).
      * intros _ _. auto.
  -
    destruct (csel_notK Hlt NK) as [NKC N30]. split; [| intros _ HK; exfalso; exact (NK HK)].
    apply (FF_frame X _ k (k + 1) (csel st n) st st1 HF MFs NKC N30); [intros xb Hxb; right; exact Hxb| lia].
Qed.
End MALLOC.
