(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From stdpp Require Import gmap.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import STree Malloc KInv MI_Tree MI_Inv MI_Kit MI_Arith MI_Geom MI_List MI_Ext MI_Shadow
  MI_Pres1 MI_Pres2 MI_Pres3 MI_Pres4 MI_WFree2 MI_WTry MI_WTry2 MI_WGroup MI_Cnt MI_TF2 MI_WCreate2 MI_WAMeta2 MI_WSlot MI_WSlot2.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec6Malloc~~~~~~04aptr37Corelib4Init9Datatypesk44list37Corelib7Numbers7BinNumsm31Z46Stdlib6ZArith6BinInt1Zo02le06mstatek43nat79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec4KInv~~~~~~qb4mled79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec7MI_Tree~~~~~~ue5ftree01M05lheadk46length37Corelib4Init5Logichk83and37Corelib4Init3Nathm33add37Corelib4Init5Peanohnc2le79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec6MI_Inv~~~~~~hp64INVLhp63blk79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec6MI_TF2~~~~~~hu33TF079OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec8MI_WSlot~~~~~~ii84X_as79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec9MI_WSlot2~~~~~~in09SLOT_POST02IB04UNIT0aalloc_slot08full_lay0asize_classo03addo02lto03mulo06of_nato03sub25stdpp4basejga5NoDup" s.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.   (* [comment removed for export] *)
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section SLOT.
Variable T : Type.
Variable Post : ltac2:(zQ "10!u7>0$0>0?1TP").

Theorem alloc_slot_ft : ltac2:(zQ "he0!je!lc!nc!p8!pd!q5!u7!hid!hj5!hj8!hjf!hlc!hn5!hp0!ht4!htc!ii1!im8!ir1!ire!is2!is8!it4!ite!iua!iv0!iv5!ivb!jg4!jh6>1f$5>1N$5>2sc$2>4idle@1$1$0>2st$4>1L$6>2BL@1$1$f>2LS>0$9@1$1$0>3req$2>1k>0$4>0$2@1$8?1T>4bail@1$8?1T>0@2$3@2$hc+j1^9@1$hb^b>0@5$e@1$h1^9^8^7^6^5>0@1$h0^9>0@2$hd$0^b>0@2$d@2$c@2$a$0^c^f^e>0@2$b@2$3Z^e@2$h9^e+j0>0@2$3Z^9>0@2$3@2$h8^a$h3@2$ha$h4@1$h7^h0>0>3st1$4>3idx$2>2L1$6>3LS1>0$9@1$1$0>0@b$h2^h6^h4^h5^f^h3^h2^h1^4^3^2^1@4$7?1T^3@2^f^5^4?4Post@4$7?1T^f@8$h5?1T$h6^h4^h0^h2^c^b^a?4Post").
Proof. intros f.
  induction f as [|f IH]; intros N sc idle st L BL LS req k bail Hf INV TF ND HLEN Hsc Hreq Hfit HK.
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
    assert (REC : REC_OK T (alloc_slot full_lay f) sc f N Post).
    { intros j idle' st' L' BL' LS' req' k' bail' Hj INV' TF' ND' HLEN' Hreq' Hfit' HK'.
      apply (IH N j idle' st' L' BL' LS' req' k' bail'); try assumption; lia. }
    apply (alloc_group_ft T (alloc_slot full_lay f) sc f N Post REC idle st1 L BL LS1 req _ bail INV1 TF1 ND ltac:(lia) Hsc Hreq Hfit HA).
    intros st2 go L2 LS2 (ACT2 & LIVE2 & GP2 & AR2 & RES2). destruct go as [g|].
    + destruct RES2 as (b & ai & last & ml & Hb & Em & Hai & Hl & FIT & STR & UND & INV2 & TF2').
      cbn zeta.
        destruct (slot_finish_ok T idle st2 L2 BL LS2 g b ai last sc ml (fun st4 => k st4 0) bail INV2 Hb Em Hai Hl Hsc
                    ltac:(rewrite ACT2 by lia; exact HA) UND TF2')
          as (LS4 & EQ & INV4 & TF4 & HA4 & ACT4 & G4 & TK4 & SH4 & L4 & SC4 & STR4 & SS4 & RG4 & SE4 & AR4).
        rewrite EQ. eapply HK. split; [intros sc' Hs; rewrite ACT4, ACT2 by lia; apply ACT1; exact Hs|]. split; [exact LIVE2|].
        split; [eapply GP_trans; [exact (GP_taf _ _ _ TAF)| eapply GP_trans; [exact GP2| apply GP_eq; [exact RG4| exact SE4]]]|].
        split; [eapply AREAS_trans; [apply AREAS_eq; exact (taf_areas _ _ _ TAF)| apply (AREAS_eq_r _ _ _ _ _ AR2); exact AR4]|].
        right. exists g, b, ai. rewrite L4, SC4, STR4, G4, SS4.
        split; [lia|]. split; [exact HA4|]. split; [exact Hb|]. split; [reflexivity|]. split; [exact FIT|]. split; [exact STR|].
        split; [exact INV4| exact TF4].
    + destruct RES2 as [INV2 TF2']. eapply HK. split; [intros sc' Hs; rewrite ACT2 by lia; apply ACT1; exact Hs|]. split; [exact LIVE2|].
      split; [eapply GP_trans; [exact (GP_taf _ _ _ TAF)| exact GP2]|].
      split; [eapply AREAS_trans; [apply AREAS_eq; exact (taf_areas _ _ _ TAF)| exact AR2]|].
      left. split; [reflexivity|]. split; [exact INV2| exact TF2'].
  - (* [comment removed for export] *)
    replace (negb (first =? 0)) with true by (symmetry; apply negb_true_iff; apply Z.eqb_neq; exact NZ).
    cbn iota. rewrite Eidx. eapply HK.
    split; [exact ACT1|]. split; [reflexivity|]. split; [exact (GP_taf _ _ _ TAF)|]. split; [apply AREAS_eq; exact (taf_areas _ _ _ TAF)|]. right.
    pose proof (ig_ok _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 INV1))))) _ _ _ Hg) as GO.
    pose proof (g_stride _ _ _ _ _ _ GO ltac:(rewrite SC; lia)) as (GS & _ & _). rewrite SC in GS.
    exists g, bg, ai. split; [exact Hidx|]. split; [exact HA|]. split; [exact Hg|]. split; [exact SC|].
    split; [lia|]. split; [intros Hs28; destruct GS; lia|]. split; [exact INV1|]. apply TF0_TF2. exact TF1.
Qed.
End SLOT.
