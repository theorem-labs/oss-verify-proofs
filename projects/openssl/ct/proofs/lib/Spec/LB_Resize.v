(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From OSSVerify.Proofs.openssl.ct.lib.Lib Require Import Nodes.
From OSSVerify.Proofs.openssl.ct.lib.Spec Require Import Prelim Monad STree Malloc MallocCtrl Prog KInv KStep KStepC
  MI_Inv MI_Kit MI_Geom MI_Ext MI_Cnt MI_Contracts LB_Tables LB_Inv LB_Sum LB_Kernel LB_Logic LB_StmtA LB_WFree LB_Raw MAlign MI_Realign.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.openssl.ct.lib.Lib Require Import Ceiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section WithCeiling. Context {CE__ : Ceiling}.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Lemma bl_remove_perm_blk k BL : In k BL -> List.NoDup (map bslot BL) -> Permutation BL (k :: bl_remove (bslot k) BL).
Proof.
  induction BL as [|k' BL IH]; intros Hin ND; [destruct Hin|]. cbn [bl_remove].
  inversion ND as [|x l NI ND']; subst.
  destruct (aptr_eqb_spec (bslot k') (bslot k)) as [E|NE].
  - destruct Hin as [->|Hin]; [apply Permutation_refl|].
    exfalso. apply NI. rewrite E. apply in_map_iff. exists k. auto.
  - destruct Hin as [->|Hin]; [congruence|]. etransitivity; [apply perm_skip; apply IH; assumption| apply perm_swap].
Qed.

Lemma zcount_perm' {A} (f : A -> bool) l l' : Permutation l l' -> zcount f l = zcount f l'.
Proof. intros HP. apply (zcount_perm f l l' HP). Qed.

(* [comment removed for export] *)
Lemma zcount_swap_head {A} (f : A -> bool) k k2 l : f k2 = f k -> zcount f (k2 :: l) = zcount f (k :: l).
Proof. intros E. rewrite !zcount_cons, E. reflexivity. Qed.

Section RESIZE.
Variables (X : extras) (st st2 : mstate) (BL : list blk) (c : cptr) (off n n' : Z).
Let k : blk := ((c, off), n').
Let k2 : blk := ((c, off), n).
Let BL2 : list blk := k2 :: bl_remove c BL.
Hypothesis Hk : In k BL.
Hypothesis ND : List.NoDup (map bslot BL).
Hypothesis CE : ctrl_eq st st2.
Hypothesis Hn : 0 <= n <= n'.
Hypothesis Hsm : n' < MMAP_THRESHOLD.
Hypothesis Hcls : size_to_class n = size_to_class n'.

Lemma rs_perm : Permutation BL (k :: bl_remove c BL).
Proof. apply (bl_remove_perm_blk k BL Hk ND). Qed.

Lemma rs_isbig : isbig k2 = isbig k.
Proof. unfold isbig, k, k2. cbn [bsize snd]. destruct (Z.leb_spec MMAP_THRESHOLD n); destruct (Z.leb_spec MMAP_THRESHOLD n'); try reflexivity; lia. Qed.

Lemma rs_LR cl : LR BL2 cl = LR BL cl.
Proof.
  unfold LR. rewrite (zcount_perm' _ _ _ rs_perm). unfold BL2. apply zcount_swap_head. rewrite rs_isbig. unfold k, k2. cbn [bsize snd]. rewrite Hcls. reflexivity.
Qed.
Lemma rs_n63 : n63 BL2 = n63 BL.
Proof. unfold n63. rewrite (zcount_perm' _ _ _ rs_perm). unfold BL2. apply zcount_swap_head. apply rs_isbig. Qed.
Lemma rs_MIS cl : MIS st2 BL2 cl = MIS st BL cl.
Proof.
  unfold MIS. rewrite (zcount_perm' _ _ _ rs_perm). unfold BL2.
  assert (SC : forall q, slotcls st2 q = slotcls st q).
  { intros q. unfold slotcls, cls, MR, get_meta_rec. rewrite (ce_slots _ _ CE), (ce_metas _ _ CE). reflexivity. }
  rewrite zcount_cons, zcount_cons. rewrite !SC. unfold k, k2. cbn [bslot bsize fst snd]. rewrite Hcls. f_equal.
  apply zcount_ext. intros x _. rewrite SC. reflexivity.
Qed.
Lemma rs_slots : forall a, In a (map bslot BL2) <-> In a (map bslot BL).
Proof.
  intros a. unfold BL2. pose proof (Permutation_map bslot rs_perm) as PM. cbn [map] in PM.
  change (map bslot (k2 :: bl_remove c BL)) with (bslot k :: map bslot (bl_remove c BL)).
  split; intros H.
  - eapply Permutation_in; [apply Permutation_sym; exact PM| exact H].
  - eapply Permutation_in; [exact PM| exact H].
Qed.

Lemma SINV_resize : SINV X st BL -> SINV X st2 BL2.
Proof.
  intros SI. pose proof (SINV_ctrl X st st2 BL CE SI) as S2.
  destruct S2 as [qb_cls qb_mis qg_map qg_std qg_small qg_63 qg_host qm_leak qm_pages qm_brk qm_len qm_dist qm_shift].
  constructor; try assumption.
  - intros kk Hkk. destruct Hkk as [<-|Hkk].
    + destruct (qb_cls k Hk) as (m & i & Hs & H48 & H63). exists m, i. unfold k, k2 in *. cbn [bslot bsize fst snd] in *.
      split; [exact Hs|]. split.
      * intros Hc. destruct (H48 Hc) as [_ Hcl]. split; [lia|]. rewrite Hcls. exact Hcl.
      * intros Hc. destruct (H63 Hc) as [Hbig _]. exfalso. lia.
    + apply qb_cls. apply (In_bl_remove kk c BL). exact Hkk.
  - intros cl. rewrite rs_MIS. destruct SI as [_ qb_mis0]. apply qb_mis0.
  - intros b m ai Hg C63. apply (proj2 (rs_slots _)). exact (qg_63 b m ai Hg C63).
Qed.

Lemma AQ_resize P : AQ st BL P -> AQ st2 BL2 P.
Proof.
  intros HAQ. pose proof (AQ_ctrl st st2 BL P CE HAQ) as A2. destruct A2 as [A1 A2 A3 A4 A5]. destruct HAQ as [B1 B2 B3 B4 B5].
  constructor; auto.
  - intros cl Hcl. rewrite rs_LR. apply B1. exact Hcl.
  - rewrite rs_n63. exact B3.
Qed.
End RESIZE.

Theorem QI_resize Xl P p n n' s mo :
  QI ((p, n') :: Xl) P s mo -> 0 <= n <= n' -> n' < MMAP_THRESHOLD -> size_to_class n = size_to_class n' ->
  QI ((p, n) :: Xl) P s mo.
Proof.
  intros [(st & L & BL & LS & E & INV & SI & HAQ & HK & HL & HP) HB] Hn Hsm Hcls.
  assert (Hin : In (fst p, n') (map bs BL)) by (eapply Permutation_in; [exact HP| left; reflexivity]).
  apply in_map_iff in Hin as ([[c off] n0] & Ebs & Hk). unfold bs in Ebs. cbn in Ebs.
  assert (Ec : c = fst p) by congruence. assert (En : n0 = n') by congruence. subst n0.
  pose proof INV as (IR & IA & IM & IL & IG & IS & ISH).
  destruct (is_blocks _ _ _ IS _ Hk) as (g & idx & Hs & Hoff & _ & _). cbn [bslot boff fst snd] in Hs, Hoff.
  (* [comment removed for export] *)
  destruct (is_valid _ _ _ IS _ _ _ Hs) as ([bg Hbg] & Hidx & _).
  destruct (hosts_ok x0 st LS IG _ _ Hbg) as (ai & Hgrp & GO).
  assert (Hsc : m_sizeclass (MR st g) < 48).
  { destruct (qb_cls _ _ _ SI _ Hk) as (m & i & Hs' & _ & H63). cbn [bslot bsize fst snd] in Hs', H63. rewrite Hs in Hs'. inversion Hs'. subst m i.
    destruct (g_sc _ _ _ _ _ _ GO) as [[H48 _]|(C63 & _)]; [lia|]. exfalso. destruct (H63 C63) as [Hbig _]. lia. }
  assert (G20 : get_stride (MR st g) * (idx + 1) < 2 ^ 20).
  { destruct (g_stride _ _ _ _ _ _ GO Hsc) as (_ & _ & LT). unfold cnt_of in LT.
    pose proof (stride_ge x0 st LS IG _ _ Hbg) as [S16 _].
    assert (get_stride (MR st g) * (idx + 1) <= get_stride (MR st g) * (m_last_idx (MR st g) + 1)) by (apply Z.mul_le_mono_nonneg_l; unfold UNIT in S16; lia). lia. }
  assert (SLT : get_stride (MR st g) < 2 ^ 20).
  { pose proof (stride_ge x0 st LS IG _ _ Hbg) as [S16 _].
    assert (get_stride (MR st g) * 1 <= get_stride (MR st g) * (idx + 1)) by (apply Z.mul_le_mono_nonneg_l; unfold UNIT in S16; lia). lia. }
  destruct (INVL_realign x0 st L BL LS c off n' g idx n 0 INV eq_refl Hk Hs (or_intror G20) ltac:(unfold UNIT; lia) ltac:(lia) ltac:(reflexivity) ltac:(lia) ltac:(lia)
              ltac:(rewrite Z.div_0_l by (unfold UNIT; lia); lia)) as (INV' & CE & TK & _).
  rewrite Z.div_0_l in INV' by (unfold UNIT; lia). rewrite Z.add_0_r in INV'.
  set (st2 := fst (realign_at st g idx n off 0)) in *.
  split.
  - exists st2, L, (((c, off), n) :: bl_remove c BL), LS.
    split; [subst st2; rewrite strip_realign_at; exact E|]. split; [exact INV'|].
    split; [apply (SINV_resize x0 st st2 BL c off n n' Hk (INVL_nodup_slots _ _ _ _ _ INV) CE Hn Hsm Hcls SI)|].
    split; [apply (AQ_resize st st2 BL c off n n' Hk (INVL_nodup_slots _ _ _ _ _ INV) CE Hn Hsm Hcls P HAQ)|].
    split; [exact HK|]. split; [exact HL|].
    cbn [map]. unfold xs at 1. unfold bs at 1. cbn [fst snd bslot bsize]. rewrite <- Ec. apply perm_skip.
    pose proof (bl_remove_perm ((c, off), n') BL Hk (INVL_nodup_slots _ _ _ _ _ INV)) as BP. cbn [bs bslot bsize fst snd] in BP.
    apply Permutation_cons_inv with (a := (c, n')). etransitivity; [| exact BP]. rewrite Ec. exact HP.
  - rewrite R63X_cons in HB |- *. unfold bigb in *.
    destruct (Z.leb_spec MMAP_THRESHOLD n); destruct (Z.leb_spec MMAP_THRESHOLD n'); lia.
Qed.
End WithCeiling.
