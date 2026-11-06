(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require STree Malloc Mall7vg KInv.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_List.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Inv MI_Kit MI_Arith MI_List MI_Geom MI_Ext.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Pres2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_S421.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_WFree.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Pres2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Pres2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Pres4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Pres4 MI_WFree MI_Ws22.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_WNtf.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_WNtf MI_WNtf2 LB_T80p LB_Inv LB_Sum LB_Bound LB_WNtf.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_WFree.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.STree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Malloc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mall7vg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.KInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_List.MI_Tree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Inv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Kit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Arith OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_List OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Geom OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Ext OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Pres2.MI_Ext2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_S421 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_WFree.MI_Read OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Pres2.MI_Pres1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Pres2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Pres4.MI_Pres3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Pres4 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_WFree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Ws22 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_WNtf.MI_WKill OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_WNtf OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_WNtf2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LB_T80p OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LB_Inv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LB_Sum OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LB_Bound OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LB_WNtf OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_WFree.LB_Dead.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.

Module LB_WTry.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require STree Malloc Mall7vg KInv.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_List.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Inv MI_Kit MI_Arith MI_Bits MI_List MI_Geom MI_Ext.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Pres2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_S421.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_WFree.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Pres2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Pres2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Pres4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Pres4 MI_WFree MI_Ws22.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_WNtf.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_WNtf MI_WNtf2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_WTry2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_WTry2 LB_T80p LB_Inv LB_Sum LB_Bound LB_WNtf.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_WFree.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.STree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Malloc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mall7vg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.KInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_List.MI_Tree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Inv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Kit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Arith OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Bits OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_List OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Geom OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Ext OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Pres2.MI_Ext2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_S421 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_WFree.MI_Read OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Pres2.MI_Pres1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Pres2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Pres4.MI_Pres3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Pres4 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_WFree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Ws22 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_WNtf.MI_WKill OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_WNtf OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_WNtf2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_WTry2.MI_WTry OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_WTry2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LB_T80p OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LB_Inv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LB_Sum OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LB_Bound OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LB_WNtf OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_WFree.LB_Dead.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section LBCEIL.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

Section TRYQ.
Variables (T : Type) (X : extras) (L : mled) (BL : list blk) (sc : Z) (k : mstate -> Z -> M T) (bail : M T).
Hypothesis HP : x_pend X = None.
Hypothesis HF : x_fresh X = None.
Hypothesis Hsc : 0 <= sc < 48.

(* [comment removed for export] *)
Lemma fin_okQ st0 st LS m (mask : Z) :
  INVL X st L BL LS -> TA_frame st0 st sc -> FFR st0 st -> active st sc = Some m -> m_avail (MR st m) = mask -> mask <> 0 ->
  exists st1 first LS1, ta_fin st m mask k = k st1 first /\ TA_POST X L BL sc st0 st1 first LS1 /\ FFR st0 st1.
Proof.
  intros INV TF FF HA AM MNZ. destruct (hd_facts X st L BL LS sc m INV HA) as (_ & Esc & bm & ai & Hbm).
  pose proof (ta_fin_ok X st L BL LS m bm ai INV HP HF Hbm ltac:(rewrite Esc; exact (hd_head X st L BL LS sc m INV HA)) ltac:(rewrite AM; exact MNZ)) as (INV1 & R1 & R2 & R3 & R4).
  rewrite AM in *. unfold ta_fin. eexists _, _, LS. split; [reflexivity|].
  split; [| eapply FFR_trans; [exact FF| apply FFR_upd_meta; [exact (g_present _ _ _ _ _ _ (ig_ok _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 INV))))) _ _ _ Hbm))| intros r; destruct r; reflexivity| intros r Hr; destruct r; exact Hr]]].
  split; [eapply taf_trans; [exact TF| apply taf_upd_meta]|].
  right. exists m, bm, ai, (ctz32 (lowbit mask)).
  assert (MRE : forall x, x <> m -> MR (upd_meta m (m_set_avail (mask - lowbit mask)) st) x = MR st x) by (intros; unfold MR; apply get_meta_rec_upd_other; assumption).
  assert (MRm : MR (upd_meta m (m_set_avail (mask - lowbit mask)) st) m = m_set_avail (mask - lowbit mask) (MR st m)) by (unfold MR; apply get_meta_rec_upd_same).
  rewrite MRm. destruct (set_avail_views (mask - lowbit mask) (MR st m)) as (V1 & V2 & V3 & V4). rewrite V1, V2, V3, V4. rewrite Esc in R4 |- *.
  split; [exact R2|]. split; [exact R3|]. split; [reflexivity|]. split; [exact HA|]. split; [exact Hbm|]. split; [exact R1|]. split; [reflexivity|]. split; [exact R4| exact INV1].
Qed.

Theorem try_avail_okQ st LS :
  INVL X st L BL LS ->
  exists st1 first LS1, try_avail sc st k bail = k st1 first /\ TA_POST X L BL sc st st1 first LS1 /\ FFR st st1.
Proof.
  intros INV. unfold try_avail.
  destruct (active st sc) as [m|] eqn:HA.
  2:{ eexists _, _, LS. split; [reflexivity|]. split; [split; [apply taf_refl| left; auto]| apply FFR_refl]. }
  fold (MR st m). destruct (Z.eqb_spec (m_avail (MR st m)) 0) as [AZ|ANZ]; cbn [negb].
  2:{ exact (fin_okQ st st LS m _ INV (taf_refl st sc) (FFR_refl st) HA eq_refl ANZ). }
  (* [comment removed for export] *)
  assert (STEP1 : exists st1 m1 LS1,
    (if m_freed (MR st m) =? 0
     then match active (dequeue (LActive sc) m st) sc with Some m1 => Some (dequeue (LActive sc) m st, m1) | None => None end
     else match m_next (MR st m) with Some m1 => Some (set_active sc (Some m1) st, m1) | None => None end) = Some (st1, m1)
    /\ GOODH X st1 L BL LS1 sc m1 /\ (TA_frame st st1 sc /\ FFR st st1)
    \/ (m_freed (MR st m) = 0 /\ active (dequeue (LActive sc) m st) sc = None /\ exists LS1, INVL X (dequeue (LActive sc) m st) L BL LS1)).
  { pose proof (hd_facts X st L BL LS sc m INV HA) as (_ & _ & bm0 & ai0 & Hbm0).
    pose proof (FFR_dequeue_INV X st L BL LS m bm0 sc INV (ex_intro _ ai0 Hbm0) (hd_in X st L BL LS sc m INV HA)) as FD.
    destruct (Z.eqb_spec (m_freed (MR st m)) 0) as [FZ|FNZ].
    - destruct (dequeue_exhausted_ok X L BL sc HP HF Hsc st LS m INV HA AZ FZ) as (LS1 & rest & INV1 & HL & HA1 & NXT).
      rewrite HA1. destruct rest as [|m1 rest']; cbn.
      + exists st, m, LS. right. split; [exact FZ|]. split; [first [reflexivity| rewrite HA1; reflexivity]| exists LS1; exact INV1].
      + exists (dequeue (LActive sc) m st), m1, LS1. left. split; [reflexivity|]. split; [| split; [apply taf_dequeue| exact FD]].
        destruct (NXT m1 eq_refl) as [A1 F1].
        assert (NE : m1 <> m).
        { intros ->. pose proof (il_nodup _ _ (proj1 (proj2 (proj2 (proj2 INV)))) (LActive sc)) as ND. rewrite HL in ND. apply NoDup_cons in ND as [N _]. apply N. left. }
        pose proof (dequeue_data (LActive sc) m st m1) as D. destruct (data_same _ _ 0 D) as (_ & _ & Ea & Ef & _).
        split; [exact INV1|]. split; [first [reflexivity| rewrite HA1; reflexivity]|]. rewrite Ea, Ef. auto.
    - destruct (hd_next X st L BL LS sc m INV HA) as (mn & Hn & Hin). rewrite Hn.
      destruct (rotate_ok X L BL sc HF st LS m mn (conj INV (conj HA (conj AZ FNZ))) Hn) as [LS1 G1].
      exists (set_active sc (Some mn) st), mn, LS1. left. split; [reflexivity|]. split; [exact G1| split; [apply taf_set_active| apply (FFR_set_head st (LActive sc))]]. }
  destruct STEP1 as (st1 & m1 & LS1 & [(E1 & G1 & [TF1 FF1])|(FZ & HA1 & LS1' & INV1)]).
  2:{ rewrite (proj2 (Z.eqb_eq _ _) FZ), HA1. eexists _, 0, LS1'. split; [reflexivity|]. split; [split; [apply taf_dequeue| left; auto]|].
      pose proof (hd_facts X st L BL LS sc m INV HA) as (_ & _ & bm0 & ai0 & Hbm0).
      exact (FFR_dequeue_INV X st L BL LS m bm0 sc INV (ex_intro _ ai0 Hbm0) (hd_in X st L BL LS sc m INV HA)). }
  rewrite E1. clear E1.
  (* [comment removed for export] *)
  assert (STEP2 : exists st2 m2 LS2,
    (let mr := get_meta_rec st1 m1 in
     if (m_freed (MR st1 m1) =? mask_upto (m_last_idx mr)) && negb (m_freeable mr =? 0)
     then match m_next mr with Some mn => (set_active sc (Some mn) st1, mn, m_freed (get_meta_rec st1 mn)) | None => (st1, m1, m_freed (MR st1 m1)) end
     else (st1, m1, m_freed (MR st1 m1))) = (st2, m2, m_freed (MR st2 m2))
    /\ GOODH X st2 L BL LS2 sc m2 /\ (TA_frame st st2 sc /\ FFR st st2)).
  { cbn zeta. fold (MR st1 m1). destruct (_ && _).
    - pose proof G1 as (INV1 & HA1 & _). destruct (hd_next X st1 L BL LS1 sc m1 INV1 HA1) as (mn & Hn & _). rewrite Hn.
      destruct (rotate_ok X L BL sc HF st1 LS1 m1 mn G1 Hn) as [LS2 G2].
      exists (set_active sc (Some mn) st1), mn, LS2. split; [reflexivity|]. split; [exact G2| split; [eapply taf_trans; [exact TF1| apply taf_set_active]| eapply FFR_trans; [exact FF1| apply (FFR_set_head st1 (LActive sc))]]].
    - exists st1, m1, LS1. auto. }
  destruct STEP2 as (st2 & m2 & LS2 & E2 & G2 & [TF2 FF2]). cbn zeta in E2. fold (MR st1 m1) in E2 |- *.
  match goal with |- context [let '(p, mask) := ?t in _] => change t with (st2, m2, m_freed (MR st2 m2)) end || rewrite E2.
  cbn iota. fold (MR st2 m2).
  destruct G2 as (INV2 & HA2 & AZ2 & FNZ2).
  destruct (hd_facts X st2 L BL LS2 sc m2 INV2 HA2) as (_ & Esc2 & b2 & ai2 & Hb2).
  pose proof (ig_ok _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 INV2))))) _ _ _ Hb2) as GO2.
  pose proof (g_masks _ _ _ _ _ _ GO2) as (W1 & W2 & W3 & W4 & W5 & W6). pose proof (g_ai _ _ _ _ _ _ GO2) as AI2. pose proof (g_li _ _ _ _ _ _ GO2) as LI2.
  rewrite (hosts_mem _ _ _ (proj1 (proj2 (proj2 INV2))) _ _ (ex_intro _ ai2 Hb2)). cbn [default].
  assert (GAI : group_active_idx st2 b2 = ai2).
  { unfold group_active_idx, get_group. rewrite Hb2. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. apply Z.mod_small. change (2 ^ 5) with 32. lia. }
  rewrite GAI.
  (* [comment removed for export] *)
  assert (STEP3 : exists st3 m3 LS3 b3 ai3,
    (if Z.land (m_freed (MR st2 m2)) (mask_upto ai2) =? 0
     then if negb (optr_eqb (m_next (MR st2 m2)) (Some m2))
          then match m_next (MR st2 m2) with Some mn => (set_active sc (Some mn) st2, mn) | None => (st2, m2) end
          else (let cnt := ai2 + 2 in
                let size := size_class (m_sizeclass (MR st2 m2)) * UNIT in
                let span := UNIT + size * cnt in
                let cnt := span_loop 300 cnt span size in
                let cnt := if m_last_idx (MR st2 m2) + 1 <? cnt then m_last_idx (MR st2 m2) + 1 else cnt in
                (set_group_active_idx b2 (cnt - 1) st2, m2))
     else (st2, m2)) = (st3, m3)
    /\ GOODH X st3 L BL LS3 sc m3 /\ (TA_frame st st3 sc /\ FFR st st3)
    /\ s_groups st3 !! b3 = Some (mkGhdr (Some m3) ai3) /\ Z.land (m_freed (MR st3 m3)) (mask_upto ai3) <> 0).
  { destruct (Z.eqb_spec (Z.land (m_freed (MR st2 m2)) (mask_upto ai2)) 0) as [LZ|LNZ].
    - (* [comment removed for export] *)
      pose proof (land_mask_upto_zero_above _ _ W2 (proj1 AI2) LZ) as ABOVE.
      assert (PART : ai2 < m_last_idx (MR st2 m2)).
      { destruct (Z.eq_dec (m_freed (MR st2 m2)) 0) as [|NZ]; [contradiction|].
        destruct (Z.lt_ge_cases ai2 (m_last_idx (MR st2 m2))) as [|GE]; [assumption|]. exfalso. apply NZ.
        apply Z.bits_inj'. intros i Hi. rewrite Z.bits_0. destruct (Z.testbit (m_freed (MR st2 m2)) i) eqn:E; [| reflexivity].
        pose proof (ABOVE i Hi E). pose proof (W4 i Hi E). lia. }
      destruct (hd_next X st2 L BL LS2 sc m2 INV2 HA2) as (mn & Hn & Hin). rewrite Hn.
      destruct (optr_eqb_spec (Some mn) (Some m2)) as [E|NE]; cbn [negb].
      + (* [comment removed for export] *)
        set (cnt0 := span_loop 300 (ai2 + 2) (UNIT + size_class (m_sizeclass (MR st2 m2)) * UNIT * (ai2 + 2)) (size_class (m_sizeclass (MR st2 m2)) * UNIT)).
        set (cnt := if m_last_idx (MR st2 m2) + 1 <? cnt0 then m_last_idx (MR st2 m2) + 1 else cnt0).
        pose proof (span_loop_ge 300 (ai2 + 2) (UNIT + size_class (m_sizeclass (MR st2 m2)) * UNIT * (ai2 + 2)) (size_class (m_sizeclass (MR st2 m2)) * UNIT)) as SL. fold cnt0 in SL.
        assert (CR : ai2 + 1 <= cnt - 1 <= m_last_idx (MR st2 m2)) by (unfold cnt; destruct (Z.ltb_spec (m_last_idx (MR st2 m2) + 1) cnt0); lia).
        unfold set_group_active_idx, get_group. rewrite Hb2. cbn [g_meta].
        replace (Z.land (cnt - 1) 31) with (cnt - 1) by (change 31 with (Z.ones 5); rewrite Z.land_ones by lia; symmetry; apply Z.mod_small; change (2 ^ 5) with 32; lia).
        set (st3 := Malloc.set_groups _ st2).
        assert (INV3 : INVL X st3 L BL LS2).
        { apply (INVL_set_ai X st2 L BL LS2 m2 b2 ai2 (cnt - 1) INV2 Hb2); [lia| | intros _; rewrite Esc2; exact (hd_in X st2 L BL LS2 sc m2 INV2 HA2)].
          intros i Hi Hb. unfold tbit in Hb. rewrite AZ2, Z.bits_0 in Hb. discriminate. }
        exists st3, m2, LS2, b2, (cnt - 1). split; [reflexivity|].
        split; [split; [exact INV3| split; [exact HA2| auto]]|].
        split.
        { split; [eapply taf_trans; [exact TF2| constructor; auto; try (intros h _; destruct h; reflexivity)]|].
          eapply FFR_trans; [exact FF2|]. unfold st3. constructor; cbn; auto; try tauto.
          intros bb h' Hbb. destruct (aptr_eq_dec bb b2) as [->|NE]; [rewrite lookup_insert_eq in Hbb; inversion Hbb; subst; eexists; split; [exact Hb2| reflexivity]|].
          rewrite lookup_insert_ne in Hbb by congruence. exists h'. auto. }
        split; [unfold st3; cbn; rewrite lookup_insert_eq; reflexivity|].
        change (MR st3 m2) with (MR st2 m2). intros E0.
        assert (Tb : Z.testbit (Z.land (m_freed (MR st2 m2)) (mask_upto (cnt - 1))) (ai2 + 1) = true).
        { rewrite Z.land_spec, testbit_mask_upto by lia. unfold tbit in W6. rewrite (W6 (ai2 + 1)) by lia. cbn. apply Z.leb_le. lia. }
        rewrite E0, Z.bits_0 in Tb. discriminate.
      + (* [comment removed for export] *)
        destruct (rotate_ok X L BL sc HF st2 LS2 m2 mn (conj INV2 (conj HA2 (conj AZ2 FNZ2))) Hn) as [LS3 G3].
        assert (NEm : mn <> m2) by congruence.
        destruct (il_active _ _ (proj1 (proj2 (proj2 (proj2 INV2)))) sc mn Hin) as (_ & [b3 [ai3 Hb3]] & Esc3).
        pose proof (ig_ok _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 INV2))))) _ _ _ Hb3) as GO3.
        assert (FULL : ai3 = m_last_idx (MR st2 mn)).
        { pose proof (g_ai _ _ _ _ _ _ GO3) as AI3. destruct (Z.lt_ge_cases ai3 (m_last_idx (MR st2 mn))) as [LT|]; [| lia]. exfalso.
          apply NEm. eapply (ig_onepartial _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 INV2)))))); [exact Hb3| exact Hb2| exact LT| exact PART| congruence]. }
        exists (set_active sc (Some mn) st2), mn, LS3, b3, ai3. split; [reflexivity|]. split; [exact G3|].
        split; [split; [eapply taf_trans; [exact TF2| apply taf_set_active]| eapply FFR_trans; [exact FF2| apply (FFR_set_head st2 (LActive sc))]]|]. split; [exact Hb3|].
        change (MR (set_active sc (Some mn) st2) mn) with (MR st2 mn).
        pose proof (g_masks _ _ _ _ _ _ GO3) as (V1 & V2 & V3 & V4 & V5 & V6).
        pose proof (g_ai _ _ _ _ _ _ GO3) as AI3.
        rewrite (land_mask_upto_all (m_freed (MR st2 mn)) ai3 V2 ltac:(clear -AI3; lia) ltac:(rewrite FULL; exact V4)).
        destruct G3 as (_ & _ & _ & F3). exact F3.
    - exists st2, m2, LS2, b2, ai2. split; [reflexivity|]. split; [split; [exact INV2| auto]|]. auto. }
  destruct STEP3 as (st3 & m3 & LS3 & b3 & ai3 & E3 & G3 & [TF3 FF3] & Hb3 & ACT).
  match goal with |- context [let '(st4, m4) := ?t in _] => change t with (st3, m3) end || rewrite E3.
  cbn iota. clear E3.
  (* [comment removed for export] *)
  destruct G3 as (INV3 & HA3 & AZ3 & FNZ3).
  destruct (hd_facts X st3 L BL LS3 sc m3 INV3 HA3) as (_ & Esc3 & _).
  rewrite (activate_group_eq X st3 L BL LS3 m3 b3 ai3 INV3 Hb3 AZ3).
  pose proof (INVL_activate X st3 L BL LS3 m3 b3 ai3 INV3 Hb3 AZ3 ltac:(rewrite Esc3; exact (hd_head X st3 L BL LS3 sc m3 INV3 HA3))) as INV4.
  set (st4 := upd_meta m3 _ st3) in INV4 |- *.
  rewrite (guard_true 40) by (apply Bool.negb_true_iff; apply Z.eqb_neq; exact ACT).
  pose proof (INVL_decay_bounces X st4 L BL LS3 (m_sizeclass (get_meta_rec st4 m3)) INV4) as INV5.
  set (st5 := decay_bounces _ st4) in INV5 |- *.
  assert (MR5 : MR st5 m3 = m_set_avail (Z.land (m_freed (MR st3 m3)) (mask_upto ai3)) (m_set_freed (Z.ldiff (m_freed (MR st3 m3)) (mask_upto ai3)) (MR st3 m3))).
  { transitivity (MR st4 m3); [unfold st5, decay_bounces; destruct (sc_in_seq_range _ && _); reflexivity|]. unfold st4, MR. apply get_meta_rec_upd_same. }
  assert (HA5 : active st5 sc = Some m3) by (unfold st5, decay_bounces; destruct (sc_in_seq_range _ && _); exact HA3).
  destruct (fin_okQ st st5 LS3 m3 (Z.land (m_freed (MR st3 m3)) (mask_upto ai3)) INV5) as (st6 & first & LS6 & E6 & POST).
  - eapply taf_trans; [exact TF3|]. eapply taf_trans; [apply taf_upd_meta| apply taf_decay].
  - eapply FFR_trans; [exact FF3|]. apply (FFR_trans st3 st4 st5).
    + unfold st4. apply FFR_upd_meta; [exact (g_present _ _ _ _ _ _ (ig_ok _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 INV3))))) _ _ _ Hb3))| intros r; destruct r; reflexivity| intros r Hr; destruct r; exact Hr].
    + unfold st5, decay_bounces. destruct (sc_in_seq_range _ && _); [apply FFR_ctx; reflexivity| apply FFR_refl].
  - exact HA5.
  - rewrite MR5. reflexivity.
  - exact ACT.
  - exists st6, first, LS6. split; [exact E6| exact POST].
Qed.
End TRYQ.

End LBCEIL.
End LB_WTry.

   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section LBCEIL.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma ncarved_dom st1 st2 : (forall m, s_metas st2 !! m <> None <-> s_metas st1 !! m <> None) -> ncarved st2 = ncarved st1.
Proof.
  intros H. unfold ncarved, zlen. rewrite !length_map_to_list. f_equal. rewrite <- !size_dom. apply set_size_proper.
  apply set_equiv. intros m. rewrite !elem_of_dom, <- !not_eq_None_Some. apply H.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section XFERF.
Variables (X1 X2 : extras) (st1 st2 : mstate) (L1 L2 : mled) (BL : list blk) (LS1 LS2 : lhead -> list aptr) (P : Z -> Z).
Variable ex : option aptr.   (* [comment removed for export] *)
Hypothesis INV1 : INVL X1 st1 L1 BL LS1.
Hypothesis INV2 : INVL X2 st2 L2 BL LS2.
Hypothesis IDLE : x_idle X2 = x_idle X1.
Hypothesis F : FFR st1 st2.
Hypothesis HAQ : AQ st1 BL P.
(* [comment removed for export] *)
Hypothesis S_cls : forall k, In k BL -> exists m i, s_slots st1 !! bslot k = Some (m, i)
      /\ (m_sizeclass (MR st1 m) < 48 -> bsize k < MMAP_THRESHOLD)
      /\ (m_sizeclass (MR st1 m) = 63 -> MMAP_THRESHOLD <= bsize k /\ m_maplen (MR st1 m) * 4096 <= bigmap (bsize k)).
Hypothesis S_mis : zlen BL <= NBCAP.
Hypothesis S_map : forall b m ai, s_groups st1 !! b = Some (mkGhdr (Some m) ai) -> m_sizeclass (MR st1 m) < 48 -> m_maplen (MR st1 m) <> 0 ->
      m_maplen (MR st1 m) * 4096 <= cnt_of (MR st1 m) * S_ (m_sizeclass (MR st1 m)) + 4111.
Hypothesis S_std : forall b m ai, s_groups st1 !! b = Some (mkGhdr (Some m) ai) -> stdg st1 m = true ->
      (m_maplen (MR st1 m) = 0 <-> std_nested (m_sizeclass (MR st1 m)) = true)
      /\ (m_maplen (MR st1 m) = 0 -> exists p i, s_slots st1 !! b = Some (p, i) /\ m_sizeclass (MR st1 p) = bighost (m_sizeclass (MR st1 m)))
      /\ (m_maplen (MR st1 m) <> 0 -> m_maplen (MR st1 m) * 4096 = std_len (m_sizeclass (MR st1 m))).
Hypothesis S_small : forall c, 0 <= c < 48 -> nsc st1 c < 160.
Hypothesis S_63 : forall b m ai, s_groups st1 !! b = Some (mkGhdr (Some m) ai) -> m_sizeclass (MR st1 m) = 63 -> Some m <> ex ->
      In (slot_start' (MR st1 m) 0) (map bslot BL).
Hypothesis S_host : forall b m ai p i, s_groups st1 !! b = Some (mkGhdr (Some m) ai) -> m_maplen (MR st1 m) = 0 ->
      s_slots st1 !! b = Some (p, i) -> m_sizeclass (MR st1 p) <= 23.
Hypothesis S_leak : forall m mr, s_metas st1 !! m = Some mr -> m_mem mr = None -> m_next mr <> None \/ In m (x_idle X1).
Hypothesis S_pages : 101 * apages st1 <= ncarved st1 + c_avail_meta_count (s_ctx st1).
Hypothesis S_brk : forall rid r, s_regions st1 !! rid = Some r -> r_kind r = RKBrk -> 101 * (r_len r / PGSZ - 2) <= ncarved st1.
Hypothesis S_len : forall rid r, s_regions st1 !! rid = Some r -> r_kind r = RKMeta ->
      exists j, 1 <= j <= c_meta_alloc_shift (s_ctx st1) /\ r_len r = 2 ^ j * PGSZ.
Hypothesis S_dist : forall rid1 rid2 r1 r2, s_regions st1 !! rid1 = Some r1 -> s_regions st1 !! rid2 = Some r2 ->
      r_kind r1 = RKMeta -> r_kind r2 = RKMeta -> rid1 <> rid2 -> r_len r1 <> r_len r2.
Hypothesis S_shift : 1 <= c_meta_alloc_shift (s_ctx st1) -> 101 * (2 ^ c_meta_alloc_shift (s_ctx st1) - 1) <= 2 * ncarved st1 + 101.
(* [comment removed for export] *)
Hypothesis EXGONE : forall b m ai, ex = Some m -> s_groups st2 !! b = Some (mkGhdr (Some m) ai) -> False.

Let IM2 : inv_M X2 st2 LS2 := proj1 (proj2 (proj2 INV2)).
Let IG2 : inv_G X2 st2 LS2 := proj1 (proj2 (proj2 (proj2 (proj2 INV2)))).
Let IS2 : inv_S X2 st2 BL := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV2))))).

(* [comment removed for export] *)
Lemma x_geom m b : hosts st2 b m -> geom (MR st2 m) = geom (MR st1 m).
Proof.
  intros Hh. destruct (ffr_meta _ _ F m) as [E|[Z2 _]]; [exact E|]. exfalso.
  rewrite (hosts_mem _ _ _ IM2 _ _ Hh) in Z2. discriminate.
Qed.

Lemma x_MR m b : hosts st2 b m ->
  m_mem (MR st2 m) = m_mem (MR st1 m) /\ m_sizeclass (MR st2 m) = m_sizeclass (MR st1 m) /\ m_last_idx (MR st2 m) = m_last_idx (MR st1 m)
  /\ m_maplen (MR st2 m) = m_maplen (MR st1 m) /\ get_stride (MR st2 m) = get_stride (MR st1 m)
  /\ (forall i, slot_start' (MR st2 m) i = slot_start' (MR st1 m) i) /\ cnt_of (MR st2 m) = cnt_of (MR st1 m).
Proof.
  intros Hh. pose proof (x_geom m b Hh) as G. pose proof (geom_stride _ _ G) as S. unfold geom in G. inversion G.
  unfold slot_start', cnt_of. rewrite S, H0, H2. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; auto.
Qed.

(* [comment removed for export] *)
Lemma x_group b m ai : s_groups st2 !! b = Some (mkGhdr (Some m) ai) -> exists ai1, s_groups st1 !! b = Some (mkGhdr (Some m) ai1).
Proof.
  intros H. destruct (ffr_groups _ _ F _ _ H) as ([gm gai] & H1 & E). cbn in E. subst gm. exists gai. exact H1.
Qed.

(* [comment removed for export] *)
Lemma x_slot s m i : s_slots st2 !! s = Some (m, i) -> s_slots st1 !! s = Some (m, i) /\ exists b, hosts st2 b m.
Proof.
  intros H. split; [exact (ffr_slots _ _ F _ _ H)|]. destruct (is_valid _ _ _ IS2 _ _ _ H) as ([b Hb] & _). exists b. exact Hb.
Qed.

Lemma x_slotcls k : In k BL -> slotcls st2 (bslot k) = slotcls st1 (bslot k).
Proof.
  intros Hk. destruct (is_blocks _ _ _ IS2 k Hk) as (m & i & Hs & _). unfold slotcls. rewrite Hs.
  destruct (x_slot _ _ _ Hs) as [Hs1 [b Hb]]. rewrite Hs1. unfold cls. destruct (x_MR m b Hb) as (_ & E & _). rewrite E. reflexivity.
Qed.

Lemma x_gmetas m b : In (m, b) (gmetas st2) -> In (m, b) (gmetas st1) /\ hosts st2 b m.
Proof.
  intros H. apply gmetas_in in H as [ai H]. destruct (x_group _ _ _ H) as [ai1 H1]. split; [apply gmetas_in; exists ai1; exact H1| exists ai; exact H].
Qed.

Lemma dec_pair2 : forall x y : aptr * aptr, {x = y} + {x <> y}.
Proof. intros x y. apply (decide (x = y)). Qed.

(* [comment removed for export] *)
Lemma x_sum_le (F1 F2 : aptr * aptr -> Z) :
  (forall m b, In (m, b) (gmetas st2) -> hosts st2 b m -> F2 (m, b) <= F1 (m, b)) ->
  (forall mb, In mb (gmetas st1) -> 0 <= F1 mb) ->
  zsum (map F2 (gmetas st2)) <= zsum (map F1 (gmetas st1)).
Proof.
  intros HF HP. apply (zsum_inj_le dec_pair2 F2 F1 (fun x => x)); [apply gmetas_nodup| | auto| exact HP].
  intros [m b] Hin. destruct (x_gmetas m b Hin) as [H1 Hh]. split; [exact H1| exact (HF m b Hin Hh)].
Qed.

Theorem SINV_xfer : SINV X2 st2 BL /\ AQ st2 BL P /\ (forall c, 0 <= c < 48 -> gcnt st2 c <= gcnt st1 c) /\ ncarved st2 = ncarved st1.
Proof.
  pose proof (ncarved_dom st1 st2 (ffr_dom _ _ F)) as NC.
  pose proof INV1 as (IR1 & IA1 & IM1 & IL1 & IG1 & IS1 & ISH1).
  assert (GC : forall c, 0 <= c < 48 -> gcnt st2 c <= gcnt st1 c).
  { intros c Hc. rewrite !gcnt_gmetas. apply x_sum_le.
    - intros m b Hin Hh. cbn. destruct (x_MR m b Hh) as (_ & E2 & _ & _ & _ & _ & E7). rewrite E2, E7. lia.
    - intros [m b] Hin. cbn. destruct (gfacts _ _ _ _ _ INV1 m b Hin) as ([? ?] & _). destruct (_ =? _); lia. }
  assert (NS : forall c, nsc st2 c <= nsc st1 c).
  { intros c. unfold nsc. apply x_sum_le.
    - intros m b Hin Hh. cbn. destruct (x_MR m b Hh) as (_ & E2 & _ & _ & E5 & _ & E7). unfold cls, stdg, cls. rewrite E2, E7, E5. lia.
    - intros [m b] Hin. cbn. destruct (gfacts _ _ _ _ _ INV1 m b Hin) as ([? ?] & _). destruct (_ && _); lia. }
  assert (AP : apages st2 = apages st1).
  { unfold apages, regions_l. rewrite (ffr_regions _ _ F). apply zsum_map_ext. intros [rid r] _. cbn.
    unfold frontier. rewrite (ffr_amas _ _ F). reflexivity. }
  split; [| split; [| split; [exact GC| exact NC]]].
  - constructor.
    + intros k Hk. destruct (is_blocks _ _ _ IS2 k Hk) as (m & i & Hs & _). exists m, i. split; [exact Hs|].
      destruct (x_slot _ _ _ Hs) as [Hs1 [b Hb]]. destruct (x_MR m b Hb) as (_ & E2 & _ & E4 & _).
      destruct (S_cls k Hk) as (m1 & i1 & Hs1' & C1 & C2). rewrite Hs1 in Hs1'. assert (m1 = m) by congruence. subst m1.
      rewrite E2, E4. auto.
    + exact S_mis.
    + intros b m ai Hg Hc Hml. destruct (x_group _ _ _ Hg) as [ai1 Hg1]. destruct (x_MR m b (ex_intro _ ai Hg)) as (_ & E2 & _ & E4 & _ & _ & E7).
      rewrite E2, E4, E7 in *. exact (S_map _ _ _ Hg1 Hc Hml).
    + intros b m ai Hg SG. destruct (x_group _ _ _ Hg) as [ai1 Hg1]. destruct (x_MR m b (ex_intro _ ai Hg)) as (_ & E2 & _ & E4 & E5 & _ & E7).
      assert (SG1 : stdg st1 m = true) by (unfold stdg, cls in SG |- *; rewrite <- E2, <- E5, <- E7; exact SG).
      destruct (S_std _ _ _ Hg1 SG1) as (Q1 & Q2 & Q3). rewrite E2, E4. split; [exact Q1|]. split; [| exact Q3].
      intros Z0. destruct (g_nest _ _ _ _ _ _ (ig_ok _ _ _ IG2 _ _ _ Hg) ltac:(rewrite E4; exact Z0)) as (p & i & Hs & _).
      exists p, i. split; [exact Hs|]. destruct (x_slot _ _ _ Hs) as [Hs1 [bp Hp]]. destruct (Q2 Z0) as (p1 & i1 & Hs1' & Ep).
      rewrite Hs1 in Hs1'. assert (p1 = p) by congruence. subst p1. destruct (x_MR p bp Hp) as (_ & Ep2 & _). rewrite Ep2. exact Ep.
    + intros c Hc. pose proof (NS c). pose proof (S_small c Hc). lia.
    + intros b m ai Hg Hc. destruct (x_group _ _ _ Hg) as [ai1 Hg1]. destruct (x_MR m b (ex_intro _ ai Hg)) as (_ & E2 & _ & _ & _ & E6 & _).
      rewrite (E6 0). apply (S_63 _ _ _ Hg1); [rewrite <- E2; exact Hc|]. intros E. exact (EXGONE _ _ _ (eq_sym E) Hg).
    + intros b m ai p i Hg Z0 Hs. destruct (x_group _ _ _ Hg) as [ai1 Hg1]. destruct (x_MR m b (ex_intro _ ai Hg)) as (_ & _ & _ & E4 & _).
      destruct (x_slot _ _ _ Hs) as [Hs1 [bp Hp]]. destruct (x_MR p bp Hp) as (_ & Ep2 & _). rewrite Ep2.
      apply (S_host b m ai1 p i Hg1); [rewrite <- E4; exact Z0| exact Hs1].
    + intros m mr Hm Z0. destruct (ffr_meta _ _ F m) as [G|[_ N2]]; [| left; unfold MR, get_meta_rec in N2; rewrite Hm in N2; exact N2].
      assert (Hm1 : s_metas st1 !! m <> None) by (apply (ffr_dom _ _ F); rewrite Hm; discriminate).
      destruct (s_metas st1 !! m) as [mr1|] eqn:E1; [| congruence].
      unfold geom, MR, get_meta_rec in G. rewrite Hm, E1 in G. cbn in G.
      assert (Z1 : m_mem mr1 = None) by congruence.
      destruct (S_leak m mr1 E1 Z1) as [N1|I1]; [| right; rewrite IDLE; exact I1].
      destruct (ffr_keepq _ _ F m ltac:(unfold MR, get_meta_rec; rewrite E1; exact Z1) ltac:(unfold MR, get_meta_rec; rewrite E1; exact N1)) as [_ N2].
      left. unfold MR, get_meta_rec in N2. rewrite Hm in N2. exact N2.
    + rewrite AP, NC, (ffr_amc _ _ F). exact S_pages.
    + intros rid r Hr K. rewrite NC. rewrite (ffr_regions _ _ F) in Hr. exact (S_brk rid r Hr K).
    + intros rid r Hr K. rewrite (ffr_shift _ _ F). rewrite (ffr_regions _ _ F) in Hr. exact (S_len rid r Hr K).
    + intros rid1 rid2 r1 r2 H1 H2 K1 K2 NE. rewrite (ffr_regions _ _ F) in H1, H2. exact (S_dist _ _ _ _ H1 H2 K1 K2 NE).
    + rewrite (ffr_shift _ _ F), NC. exact S_shift.
  - constructor.
    + exact (aq_live _ _ _ HAQ).
    + intros c Hc. pose proof (GC c Hc). pose proof (aq_slots _ _ _ HAQ c Hc). lia.
    + exact (aq_big _ _ _ HAQ).
    + rewrite NC. exact (aq_carved _ _ _ HAQ).
    + exact (aq_P _ _ _ HAQ).
    + exact (aq_kcap _ _ _ HAQ).
Qed.
End XFERF.

End LBCEIL.
