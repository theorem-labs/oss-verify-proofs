(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (1 recorded proof replaced by written proofs (alloc_slot_ft)). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From stdpp Require Import gmap.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree Malloc KInv MI_Tree MI_Inv MI_Kit MI_Arith MI_Geom MI_List MI_Ext MI_Shadow
  MI_Pres1 MI_Pres2 MI_Pres3 MI_Pres4 MI_WFree2 MI_WTry MI_WTry2 MI_WGroup MI_Cnt MI_TF2 MI_WCreate2 MI_WSlot MI_WSlot2.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_MI_WSlot3 () := "I59OSSVerify5KrLib4Spec5STree5stree00C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rC59OSSVerify5KrLib4Spec7MI_Tree5ftreeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc1MC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9MI_WSlot26REC_OKC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8MI_WSlot>slot_finish_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8MI_WTry2<try_avail_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9MI_WSlot2>alloc_group_ftC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5queueC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9try_availC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;alloc_groupC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:alloc_slotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4aptrC1?~~~~~~~~~~~~~~~C35stdpp4base6ElemOfI35stdpp4base<list_elem_of00C59OSSVerify5KrLib4Spec6Malloc4optrC1?~~~~~~~~~~~~~~~I35stdpp4base5NoDup00I47Corelib4Init9Datatypes4list00K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z2leC59OSSVerify5KrLib4Spec6MI_TF23TF0C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00C59OSSVerify5KrLib4Spec9MI_WSlot29SLOT_POSTC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8iff_reflK47Corelib4Init5Logic2eq01K47Corelib4Init9Datatypes4list01K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr04K47Corelib4Init9Datatypes6option02C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC47Corelib4Init5Logic9False_indK47Corelib4Init9Datatypes3nat02C59OSSVerify5KrLib4Spec8MI_WSlot4X_asC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5ctz32C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7m_availC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;m_set_availC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8upd_metaC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z03I47Corelib4Init9Datatypes6option00C59OSSVerify5KrLib4Spec6MI_Inv6x_pendC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv7x_freshC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00I59OSSVerify5KrLib4Spec8MI_WTry28TA_frame00C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00C35stdpp9decidable;prod_eq_decC35stdpp9countable>prod_countableI35stdpp4gmap4gmap00C35stdpp4gmap;gmap_lookupC59OSSVerify5KrLib4Spec6Malloc8s_groupsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv2MRC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2or00K59OSSVerify5KrLib4Spec6Malloc5lhead01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6activeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv6sstartC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8get_headC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00C47Corelib4Init5Logic7f_equalC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t01C47Corelib4Init5Logic3notC59OSSVerify5KrLib4Spec8MI_WTry29taf_headsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8MI_WTry2:taf_shadowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8MI_WTry28taf_tickC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_TF28TF0_ctrlC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv4INVLC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3eqbC47Corelib4Init9Datatypes4negbK46Stdlib9micromega7EnvRing5PExpr03C59OSSVerify5KrLib4Spec9MI_WSlot27AG_POSTC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv7ld_liveC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8MI_WSlot2GPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9mask_uptoC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc4meta01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:get_strideC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6MI_Inv6extras01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:size_classC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_TF23TF2C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_List8queue_stC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6s_tickC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8s_shadowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9s_regionsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:m_last_idxC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4of_NC56Stdlib6ZArith4Znat3N2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat3N2Z9is_nonnegK46Stdlib9micromega5Tauto8GFormula07C59OSSVerify5KrLib4Spec8MI_WSlot6GP_tafC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8MI_WSlot5GP_eqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8MI_WSlot8GP_transC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc4ghdr01C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01C59OSSVerify5KrLib4Spec6Malloc;m_sizeclassC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01K47Corelib4Init5Logic2or02K47Corelib4Init5Logic2or01C46Stdlib4Bool4Bool=negb_true_iffC56Stdlib6ZArith6BinInt1Z7eqb_neqC47Corelib4Init5Logic6eq_symI59OSSVerify5KrLib4Spec6MI_Inv5inv_G00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv5inv_S00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv6inv_SH00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv5inv_L00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv5inv_M00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv5inv_A00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv5inv_R00C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj2C47Corelib4Init5Logic5proj1C59OSSVerify5KrLib4Spec6MI_Inv5ig_okC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv8group_ok00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv8g_strideC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8m_maplenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv6cnt_ofC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3powC47Corelib4Init5Logic6eq_indK46Stdlib9micromega7EnvRing5PExpr05C59OSSVerify5KrLib4Spec6MI_TF27TF0_TF2C1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes7nat_indC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08C59OSSVerify5KrLib4Spec8MI_WTry27TA_POSTC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01C47Corelib4Init9Datatypes3fstK47Corelib4Init9Datatypes4prod01C59OSSVerify5KrLib4Spec9MI_WFree25xpendC1?~~~~~~~~~~~~~~~C35stdpp4base6lookupK46Stdlib9micromega6VarMap1t03C59OSSVerify5KrLib4Spec6Malloc8s_secretC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z01C59OSSVerify5KrLib4Spec6Malloc4UNITC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc2IBC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00I47Corelib4Init9Datatypes3nat00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op205K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C59OSSVerify5KrLib4Spec6Malloc8full_layC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc4ghdr00C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00C56Stdlib6ZArith4Znat5Nat2Z8inj_succK46Stdlib9micromega=RingMicromega3Op201I59OSSVerify5KrLib4Spec6Malloc4meta00C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool02I59OSSVerify5KrLib4Spec6Malloc6mstate00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec4KInv4mled00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv3blkC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc5lhead00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib4Init5Logic5False00C45stdpp7numbers1N6eq_decC45stdpp7numbers1Z6eq_decC35stdpp9countable;N_countableC35stdpp9countable;Z_countableK46Stdlib9micromega:ZMicromega;ZArithProof01C59OSSVerify5KrLib4Spec6Malloc4cptrC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc6shadow00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc6region00C1?~~~~~~~~~~~~~~~".
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section SLOT.
Variable T : Type.
Variable Post : mled -> T -> Prop.

Theorem alloc_slot_ft (f : nat) : forall sc idle st L BL LS req (k : mstate -> Z -> M T) bail,
  49 - sc <= Z.of_nat f ->
  INVL (X_as idle) st L BL LS -> TF0 st -> NoDup idle -> 0 <= sc < 48 -> 0 <= req -> req + IB <= UNIT * size_class sc ->
  (forall st1 idx L1 LS1, SLOT_POST idle sc req st L BL st1 idx L1 LS1 -> ftree L1 (k st1 idx) Post) ->
  ftree L (alloc_slot full_lay f st sc req k bail) Post.
Proof.
  induction f as [|f IH]; intros sc idle st L BL LS req k bail Hf INV TF ND Hsc Hreq Hfit HK.
  { exfalso. cbn in Hf. lia. }
  change (alloc_slot full_lay (S f) st sc req k bail) with
    (try_avail sc st (fun st1 first =>
       if negb (first =? 0) then k st1 (ctz32 first)
       else alloc_group T full_lay (alloc_slot full_lay f) st1 sc req (fun st2 go =>
              match go with
              | None => k st2 (-1)
              | Some g => let st3 := upd_meta g (fun r => m_set_avail (m_avail r - 1) r) st2 in
                          queue (LActive sc) g st3 (fun st4 => k st4 0) bail
              end) bail) bail).
  destruct (try_avail_ok T (X_as idle) L BL sc
              (fun st1 first =>
                 if negb (first =? 0) then k st1 (ctz32 first)
                 else alloc_group T full_lay (alloc_slot full_lay f) st1 sc req (fun st2 go =>
                        match go with
                        | None => k st2 (-1)
                        | Some g => let st3 := upd_meta g (fun r => m_set_avail (m_avail r - 1) r) st2 in
                                    queue (LActive sc) g st3 (fun st4 => k st4 0) bail
                        end) bail) bail eq_refl eq_refl Hsc st LS INV) as (st1 & first & LS1 & E & TAF & RES).
  rewrite E. cbn beta.
  assert (ACT1 : forall sc', sc' < sc -> active st1 sc' = active st sc').
  { intros sc' Hs. change (active st1 sc') with (get_head st1 (LActive sc')). rewrite (taf_heads _ _ _ TAF) by (intros EQ; inversion EQ; lia). reflexivity. }
  assert (TF1 : TF0 st1) by exact (TF0_ctrl st st1 (taf_shadow _ _ _ TAF) (taf_tick _ _ _ TAF) TF).
  destruct RES as [(-> & HA & INV1)|(g & bg & ai & idx & NZ & POS & Eidx & HA & Hg & Hidx & SC & STR & INV1)].
  - (* [comment removed for export] *)
    change (negb (0 =? 0)) with false. cbn iota.
    assert (REC : REC_OK T (alloc_slot full_lay f) sc Post).
    { intros j idle' st' L' BL' LS' req' k' bail' Hj INV' TF' ND' Hreq' Hfit' HK'.
      apply (IH j idle' st' L' BL' LS' req' k' bail'); try assumption; lia. }
    apply (alloc_group_ft T (alloc_slot full_lay f) sc Post REC idle st1 L BL LS1 req _ bail INV1 TF1 ND Hsc Hreq Hfit HA).
    intros st2 go L2 LS2 (ACT2 & LIVE2 & GP2 & RES2). destruct go as [g|].
    + destruct RES2 as (b & ai & last & ml & Hb & Em & Hai & Hl & FIT & STR & UND & INV2 & TF2').
      cbn zeta.
        destruct (slot_finish_ok T idle st2 L2 BL LS2 g b ai last sc ml (fun st4 => k st4 0) bail INV2 Hb Em Hai Hl Hsc
                    ltac:(rewrite ACT2 by lia; exact HA) UND TF2')
          as (LS4 & EQ & INV4 & TF4 & HA4 & ACT4 & G4 & TK4 & SH4 & L4 & SC4 & STR4 & SS4 & RG4 & SE4).
        rewrite EQ. eapply HK. split; [intros sc' Hs; rewrite ACT4, ACT2 by lia; apply ACT1; exact Hs|]. split; [exact LIVE2|].
        split; [eapply GP_trans; [exact (GP_taf _ _ _ TAF)| eapply GP_trans; [exact GP2| apply GP_eq; [exact RG4| exact SE4]]]|].
        right. exists g, b, ai. rewrite L4, SC4, STR4, G4, SS4.
        split; [lia|]. split; [exact HA4|]. split; [exact Hb|]. split; [reflexivity|]. split; [exact FIT|]. split; [exact STR|].
        split; [exact INV4| exact TF4].
    + destruct RES2 as [INV2 TF2']. eapply HK. split; [intros sc' Hs; rewrite ACT2 by lia; apply ACT1; exact Hs|]. split; [exact LIVE2|].
      split; [eapply GP_trans; [exact (GP_taf _ _ _ TAF)| exact GP2]|].
      left. split; [reflexivity|]. split; [exact INV2| exact TF2'].
  - (* [comment removed for export] *)
    replace (negb (first =? 0)) with true by (symmetry; apply negb_true_iff; apply Z.eqb_neq; exact NZ).
    cbn iota. rewrite Eidx. eapply HK.
    split; [exact ACT1|]. split; [reflexivity|]. split; [exact (GP_taf _ _ _ TAF)|]. right.
    pose proof (ig_ok _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 INV1))))) _ _ _ Hg) as GO.
    pose proof (g_stride _ _ _ _ _ _ GO ltac:(rewrite SC; lia)) as (GS & _ & _). rewrite SC in GS.
    exists g, bg, ai. split; [exact Hidx|]. split; [exact HA|]. split; [exact Hg|]. split; [exact SC|].
    split; [lia|]. split; [intros Hs28; destruct GS; lia|]. split; [exact INV1|]. apply TF0_TF2. exact TF1.
Qed.
End SLOT.
