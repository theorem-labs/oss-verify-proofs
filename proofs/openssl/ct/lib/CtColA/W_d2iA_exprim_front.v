(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Frame Cells Step Mem RzCPS. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim STree Malloc Monad Stdio Prog BnBase BnModel BnTree ApBase ApState ApLogic ApInv ApErr ApParse ApPrim CtSizes.
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout RT_iface RT_client_kit D_defs D_cs I_lkit.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnP Require Import BnKit BnKit2.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnW Require Import BnTac BnMem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnAsan Require Import AsKit AsLoop.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import R_unwind_chain.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtKitA Require Import RT_iface2 LibKitA ARun BnHeapA BnRepDefs BnRepA ImplA ImplAX BnIfaceA AsStruct RtCallA UnwindA EdgesA UnwindX UnwindRecA W_cryptoA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtFrameA Require Import AFrameKit AFrameCall AFrameTac.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepP Require Import ApCells.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepP Require ApErrKit.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepP Require W_get_object W_get_object_walk W_check_tlen.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApUTac.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require Import I_strcpyA ApATac ApATacX ApBImg ApWalkTac ApRepDefs ApRep ApIface ApFrame W_akit W_get_objectA W_check_tlenA W_item_d2i_stmtA W_item_d2i_imgA W_c2i_stmtA W_frkitA Fr_asn1_check_tlen Fr_asn1_d2i_ex_primitive W_err_newA W_err_set_debugA W_err_vsetA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require W_get_object_walkA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require Import W_item_d2i_exA W_item_d2i_tailA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtSctP Require SctStmt.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtSctA Require Import SctRepA SctStmtA O2iKitA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtColA Require Import ColBudgetA ColDefsA CtlStmtA W_check_tlen_genA W_bufmemA W_collectA W_d2iA_stmt W_d2iA_exprim_ctx W_d2iA_exprim_tail W_d2iA_exprim_call.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtHarA Require Import HarKitA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtTimeA Require Import BTacX.                (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac step := apre; OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.step.
Local Ltac zstep := apre; OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep.
Local Ltac alia := unfold BnHeapA.ACEIL, SEGTOP_A, SHHI, SHLO, STACK_WIN, USTACK_TOP in *; lia.
Local Ltac plia := unfold BnHeapA.ACEIL, SEGTOP_A, SHHI, SHLO, STACK_WIN, USTACK_TOP, RT_STACK in *; cbn [ar_FR ar_RT ar_SP0 ar_PMc push amb] in *; lia.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Open Scope am_scope.
Ltac zc H := rewrite ?bv_lts_zero_r, ?bv_lts_zero_l in H; unfold bv_eqb, bv_ltu, bv_lts, bv_leu in H; fold_lit_ux_in H; try zsimp_in H; zify_bool H.
Local Definition hidden (P : Prop) : Prop := P.
Local Ltac hide H := lazymatch type of H with ?T => change T with (hidden T) in H end.
Local Ltac unhide H := unfold hidden in H.
Local Ltac freeze H := lazymatch type of H with ?T => change T with (frozen T) in H end.
Local Ltac thaw H := unfold frozen in H.
Import CtRepP.W_get_object(land_32_cases, go_ret_cases, go_cls_cases, go_tag_range).
Import CtRepP.W_get_object_walk(signed_small, zxb_lit).
Notation go_ret_prim := CtRepP.W_check_tlen.go_ret_prim.
Notation tlc_in := CtRepP.W_check_tlen.tlc_in.
Notation payload_readA := CtRepA.W_get_object_walkA.payload_readA.

(* [comment removed for export] *)
Local Notation E_ex_ct := (E_asn1_d2i_ex_primitive_244534 : uk_call 0x24187c 0x241b70 0x2426a8).      (* [comment removed for export] *)

Section WithRT.
Context {AR : ARun} {UK : UnwindKit} {BE : BnEdges} {UR : UnwindRec ASN1_COLLECT_A ASN1_COLLECT_REC_RA 6}.
Local Notation RT := (@ar_RT AR).
Local Notation AF := (@ar_AF AR).
Local Notation PMc := (@ar_PMc AR).
Local Notation FR := (@ar_FR AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).

(* [comment removed for export] *)
Section Body.
  (* [comment removed for export] *)
  Hypothesis STRCPY : strcpy_icontract RT.
  Hypothesis HCTL : forall AR' : ARun, strcpy_icontract (@ar_RT AR') -> @check_tlen_gen_specA AR' UK.

  (* [comment removed for export] *)
  Variables (STK : Z) (CST : Z -> Z) (FRMb : Z).
  Variables (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word).
  Variables (m : mem) (Σ : rts RT) (st : ap_st bptr) (OW LB : list block) (E : ap_env) (bo : Z * Z) (lo : Z) (K : list block).
  Variables (adr : bptr -> Z) (D : Z) (d : list Z) (OPP PV TLC : Z) (j31 : list byte).
  Variables (f spa : Z) (g : nat) (junk gj : list byte) (Σ1 : rts RT) (m3 : mem).
  Let len := zlength d.
  Let gr := get_object d 0 len.

  (* [comment removed for export] *)
  Hypothesis PRE0 : ap_preA Σ st m OW LB E bo sp lo STK (CST len) FRMb.
  Variable ras : list Z.
  Hypothesis UW : uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras.
  Hypothesis CTX : uk_ctx ADEP_ENTRY (bv_unsigned ra :: ras).
  Hypothesis NE : ras <> nil.
  Hypothesis KOW : forall b, In b K -> In b OW.
  Hypothesis KIDS : forall b, In b K -> ~ In (blk_id b) (es_ids st ++ env_ids E).
  Hypothesis ADR : forall b, In b LB -> adr (blk_id b) = blk_addr b.
  Hypothesis CELLS : d2i_cells_okA m LB D d OPP PV TLC j31.
  Hypothesis LEN1 : 0 < len.

  (* [comment removed for export] *)
  Hypothesis HEAP3 : @BnHeapA.AHEAP (push AR f 2) Σ1 OW LB m3.
  Hypothesis FRESH : forall b, In b (OW ++ LB) -> off_fr f 2 b.
  Hypothesis GEO : @fr_geo (push AR f 2) f 2.
  Hypothesis CR1 : rt_credit RT Σ1 = rt_credit RT Σ - 1.
  Hypothesis ST3 : stk ctasegs m3 lo spa.
  Hypothesis MI3 : mem_inv ctasegs m3.
  Hypothesis AGF : agree_on (aclient_addr (OW ++ LB) (bv_unsigned sp)) m m3.
  Hypothesis SPA32 : spa mod 32 = 0.
  Hypothesis SPAL : bv_unsigned sp - 272 <= spa.
  Hypothesis SPAH : spa <= bv_unsigned sp - 256.
  Hypothesis GSZ : Z.of_nat g = bv_unsigned sp - spa - 168.
  Hypothesis SAVJ : junk = gj ++ cells_bytes [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1].
  (* [comment removed for export] *)
  Hypothesis STKB : ADEP_FRAME + CHECK_TLEN_STACK_A + 6 * 176 <= STK.
  Hypothesis FRMBb : 1 + CHECK_TLEN_FRAMES_A <= FRMb.
(* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis CSTB : 15 * len + 2 ^ 19 <= CST len.

  Local Ltac ctx := pose proof (exo_ctx STK CST FRMb sp m Σ st OW LB E bo lo D d OPP PV TLC j31 f spa PRE0 CELLS LEN1 FRESH GEO SPAL SPAH STKB)
                      as (DF & D0 & D63 & D26 & CL1 & CL2 & CL3 & CEIL & LO0 & LO & ESS & TOP & SPR & DLEN & ESPA & G1 & G2 & G3 & G4 & Ef & G5 & FSH & SHR1 & SHR2
                          & (bd & Hbd & BD1 & BD2 & BD3 & BD4 & BD5 & OD) & (bq & Hbq & BQ1 & BQ2 & BQ3 & BQ4 & BQ5 & OQ)
                          & (bv & Hbv & BV1 & BV2 & BV3 & BV4 & BV5 & OV) & (bt & Hbt & BT1 & BT2 & BT3 & BT4 & BT5 & OT));
                    unfold off_fr in OD, OQ, OV, OT; change (fs_size 2) with 256 in OD, OQ, OV, OT; cbn [blk_addr blk_size fst snd] in OD, OQ, OV, OT.
  Local Notation POST := (exprim_oct_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ OW LB E lo m K (CST len) adr OPP PV TLC).
  Local Notation linv := (exo_inv STK CST FRMb sp LB E lo K D d OPP PV TLC f spa Σ1).
  Local Notation pbs := (exo_pbs f).
  Local Notation XP := (exo_XP OPP PV TLC f).
  (* [comment removed for export] *)
  Local Ltac kitp L q1 q2 mr0 H :=   (* [comment removed for export] *)
    pose proof (L sp mr0 Σ1 (exo_pbs f q1 q2 ++ LB) E lo K d D (exo_XP OPP PV TLC f) (spa - bv_unsigned sp) (STK - ADEP_FRAME) (CST len - 1) (FRMb - 1)
                  (exo_KH STK CST FRMb sp m Σ st OW LB E bo lo D d OPP PV TLC j31 f spa PRE0 CELLS LEN1 FRESH GEO SPA32 SPAL SPAH STKB q1 q2)) as H.

  (* [comment removed for export] *)
  Let plen : Z := if Z.testbit (go_ret gr) 0 then len - go_p gr else go_len gr.

  (* [comment removed for export] *)
  Local Notation EXD := (exd_facts STK CST FRMb ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m OW LB E lo K D d OPP PV TLC f spa g junk gj Σ1 ras).
  Local Notation EXMS := (exd_ms sp gp TLC f spa).
  Local Notation EXC := (exc_facts ra sp s0 m OW LB D OPP PV f spa g junk ras).

  (* [comment removed for export] *)
  Hypothesis HPRIM : forall qfc qb mr ΣX stX mX OWX boX CX (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) FX fcX
      (j0 j8 j16 j24 j64 j72 j80 j104 j120 j128 j136 j144 jt : list byte) (vb : byte),
    Z.land (go_ret gr) 32 = 0 ->
    EXD qfc qb mr ΣX stX mX OWX boX CX j0 j8 j16 j24 j64 j72 j80 j104 j120 j128 j136 j144 jt vb ->
    @implAp (push AR f 2) _
      ((blk <- amalloc SZ_ASN1_STRING ;;
        dp <- amalloc_crypto plen ;;
        aret (Some (CtModel.mkOct blk (option_map (fun q => (q, plen)) dp) plen (CtWire.slice d (go_p gr) plen)))) stX)
      ΣX POST (EXMS EX_PRIM_ARM x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 FX fcX mX).
  Hypothesis HCONS : forall qfc qb mr ΣX stX mX OWX boX CX (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) FX fcX
      (j0 j8 j16 j24 j64 j72 j80 j104 j120 j128 j136 j144 jt : list byte) (vb : byte),
    Z.land (go_ret gr) 32 <> 0 ->
    EXD qfc qb mr ΣX stX mX OWX boX CX j0 j8 j16 j24 j64 j72 j80 j104 j120 j128 j136 j144 jt vb ->
    @implAp (push AR f 2) _
      ((' (b, r) <- CtModel.collect (CtModel.ct_fuel d) d CtModel.buf0 (go_p gr) plen (Z.testbit (go_ret gr) 0) 0 ;;
        match r with
        | None => afree_opt (option_map fst (CtModel.bm_data b)) ;;; aret None
        | Some _ =>
            let l := CtModel.bm_len b in
            b2 <- CtModel.buf_grow_clean b (l + 1) ;;
            blk <- amalloc SZ_ASN1_STRING ;;
            aret (Some (CtModel.mkOct blk (CtModel.bm_data b2) l (firstn (Z.to_nat l) (CtModel.bm_bytes b2))))
        end) stX)
      ΣX POST (EXMS EX_CONS_ARM x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 FX fcX mX).

  (* [comment removed for export] *)
  Lemma exo_front : forall (ra' t0' t1' t2' a7' t3' t4' t5' t6' : word) (F : bvmap 5 word) (fc : bv 32)
      (j0 j8 j16 j24 j32 j48 j64 j72 j80 j96 j104 j112 j120 j128 j136 j144 jf24 jf32 jf40 jf64 jf65 jf80 jf112 jst : list byte),
    rw_cells ctasegs m3 spa [CB 8 j0; CB 8 j8; CB 8 j16; CB 8 j24; CB 8 j32; C8 (Z_to_bv 64 PV); CB 8 j48; C8 (Z_to_bv 64 OPP); CB 8 j64; CB 8 j72; CB 8 j80; C8 (Z_to_bv 64 f); CB 8 j96; CB 8 j104; CB 8 j112; CB 8 j120; CB 8 j128; CB 8 j136; CB 8 j144; CB g junk] ->
    rw_cells ctasegs m3 (bv_unsigned sp + -16) [C8 s0; C8 ra] ->
    rw_cells ctasegs m3 f (ex_frameA jf24 jf32 jf40 jf64 jf65 jf80 jf112) ->
    rw_cells ctasegs m3 (shad f) (adep_shadow_pro jst) ->
    @implAp (push AR f 2) _ (d2i_exprim d len st) Σ1 POST
      (* [comment removed for export] *)
      (MS (mkR ra' (Z_to_bv 64 spa) gp (wz TP_A) t0' t1' t2' sp (Z_to_bv 64 spa) (Z_to_bv 64 (f + 80))
               (Z_to_bv 64 1) (Z_to_bv 64 (-13)) (Z_to_bv 64 (-14)) (Z_to_bv 64 (-8)) (Z_to_bv 64 (-15)) (Z_to_bv 64 1102416563) a7'
               (Z_to_bv 64 f) (Z_to_bv 64 f) (wz 0) (Z_to_bv 64 SHB) (Z_to_bv 64 (shad f)) (wz ITEM_OCTET_A) (wz TLC) (wz 0) (wz len) (wz (-1)) t3' t4' t5' t6')
          F (wz ADEP_BODY) fc None m3 (seg_rom ctasegs)).
  Proof.
    intros until jst. intros FRL FRH FRF FRS. ctx.
    pose proof PRE0 as (HEAP & AS & IDS & DC & ST & CEIL' & LOSP & TOP' & AL16 & MI & CRED & FRM).
    pose proof CELLS as (PAY & COPP & CPV & CTLC & ALO & ALV & ALT & DOV & DOT & DVT & DOD & DVD & DTD & HOPP & HPV & HTLC).
    hide DOV. hide DOT. hide DVT. hide DOD. hide DVD. hide DTD. hide BD5. hide BQ5. hide BV5. hide BT5. hide OD. hide OQ. hide OV. hide OT. hide G5.
    pose proof PAY as (HB & _).
    unfold ex_frameA in FRF. unfold adep_shadow_pro in FRS. unfold CtRepP.W_check_tlen.tlc_in in HTLC. unfold ADEP_BODY, MallocRep.wz in *.
    (* [comment removed for export] *)
    assert (VPOS : 0 <= CHECK_TLEN_STACK_A /\ 0 <= CHECK_TLEN_FRAMES_A /\ 272 + 16 <= STK /\ 1 <= CST len /\ 1 <= FRMb /\ 0 <= len).
    { pose proof STKB as S'. unfold ADEP_FRAME in S'. unfold len in LEN1, CSTB |- *.
      unfold CHECK_TLEN_STACK_A, ACTL_FRAME, GETOBJ_STACK_A, CHECK_TLEN_FRAMES_A, GETOBJ_FRAMES_A, ERR_SET_ERROR_STACK, ERR_VSET_ERROR_STACK,
             ERR_SET_ERROR_FRAMES, ERR_VSET_ERROR_FRAMES, RT_STACK in *; clear - S' LEN1 CSTB FRMBb; lia. }
    pose proof (pro_closeA Σ st m OW LB E bo sp lo _ _ _ f 2%nat Σ1 m3 spa 256 PRE0 HEAP3 ST3 MI3 AGF CR1 SPA32
                  ltac:(clear - SPAL; lia) ltac:(clear - SPAH; lia) ltac:(clear; lia) ltac:(clear - VPOS; lia)
                  ltac:(clear - VPOS; lia) ltac:(clear - VPOS; lia)) as PRE1.
    replace (STK - 256 - 16) with (STK - ADEP_FRAME) in PRE1 by (unfold ADEP_FRAME; clear; lia).
    pose proof PRE1 as (_ & AS1 & IDS1 & DC1 & ST1 & CEIL1 & LOSP1x & TOP1 & AL161 & MI1 & CRED1 & FRM1).
    rewrite ESPA in ST1, LOSP1x, TOP1, AL161. cbn [ar_FR ar_RT ar_SP0 push amb] in CRED1, FRM1, CEIL1. unfold ADEP_FRAME in LOSP1x.
    assert (LOSP1 : lo + CHECK_TLEN_STACK_A <= spa) by (pose proof STKB as X; unfold ADEP_FRAME in X; clear - LOSP1x X; lia).
    (* [comment removed for export] *)
    apply (rw_cells_agree _ _ _ _ _ AGF) in HOPP; [| intros a Ha; cbn in Ha; right; right; exists bq; split; [apply in_or_app; right; exact Hbq| clear - Ha BQ1 BQ2; lia]].
    apply (rw_cells_agree _ _ _ _ _ AGF) in HPV; [| intros a Ha; cbn in Ha; right; right; exists bv; split; [apply in_or_app; right; exact Hbv| clear - Ha BV1 BV2; lia]].
    apply (rw_cells_agree _ _ _ _ _ AGF) in HTLC; [| intros a Ha; cbn in Ha; right; right; exists bt; split; [apply in_or_app; right; exact Hbt| clear - Ha BT1 BT2; lia]].
    assert (PAY3 : payload_okA m3 LB D d).
    { eapply payload_okA_agreeA; [exact PAY|]. eapply agree_on_mono; [exact AGF|]. intros a Ha. right; right. eapply in_block_mono; [| exact Ha]. intros b Hb; apply in_or_app; right; exact Hb. }
    clear HB. pose proof PAY3 as (HB & _).
    (* [comment removed for export] *)
    pose proof (munch_refl [(spa, spa); (f, f + 248); (shad f, shad f + 32)]%Z m3) as MU. pose proof (wmono_refl ctasegs m3) as WM.
    freeze HOPP. freeze HPV. freeze HTLC. freeze HB. freeze FRL. freeze FRH.
    apply implAp_from_evt. step. step. step. step. step.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m4 end.
    assert (HEAP4 : @BnHeapA.AHEAP (push AR f 2) Σ1 OW LB m4).
    { eapply (@fr3_heap (push AR f 2) Σ1 OW LB m3 m4 f 2%nat spa spa 248 32 (or_introl eq_refl) HEAP3 MU WM);
        [clear - CEIL1 LOSP1 ESS; plia| clear - TOP1; unfold USTACK_TOP in *; lia| change (fs_size 2) with 256; clear; lia| change (fs_size 2) with 256; clear; lia
        | intros b Hb; apply FRESH; apply in_or_app; right; exact Hb]. }
    assert (OFFLB : forall b, In b LB -> off_fr f 2 b) by (intros b Hb; apply FRESH; apply in_or_app; right; exact Hb).
    destruct (bptr_fresh (map blk_id (OW ++ LB))) as [qb Hqb].
    assert (HEAPb : @BnHeapA.AHEAP (push AR f 2) Σ1 OW ((qb, f + 80, 32) :: LB) m4).
    { apply (@frame_obj_open (push AR f 2) Σ1 OW LB m4 f 2%nat qb (f + 80) 32 (or_introl eq_refl) HEAP4);
        [clear; lia| change (fs_size 2) with 256; clear; lia| clear; lia| | exact Hqb|].
      - eapply (acc_of_shadow_cells m4 (shad f) _ 10 (f + 80) 32 FRS); [clear - G2; Z.div_mod_to_equations; lia| clear - G1; lia| clear; lia
          | unfold shad; clear - G2; Z.div_mod_to_equations; lia| cbn; clear; lia| reflexivity].
      - intros b Hb. pose proof (OFFLB b Hb) as O. unfold off_fr in O. change (fs_size 2) with 256 in O. unfold blk_apart. cbn [blk_addr blk_size fst snd]. clear - O. lia. }
    clear HEAP4.
    (* [comment removed for export] *)
    pose proof (agree_on_of_munch_nw _ _ _ MU) as AG4. clear MU WM.
    thaw FRL. apply (rw_cells_agree _ _ _ _ _ AG4) in FRL; [| intros a Ha; cbn [cells_size csize] in Ha; rewrite ?Nat2Z.inj_add in Ha; cbn [outside fst snd]; clear - Ha GSZ SPAL SPAH G3 CEIL LO ESS SHR2 CL2; plia].
    pose proof (munch_refl [(spa, spa + 168)]%Z m4) as MU. pose proof (wmono_refl ctasegs m4) as WM.
    freeze FRF. freeze FRS.
    step. step. step. step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m5 end.
    assert (HEAP5 : @BnHeapA.AHEAP (push AR f 2) Σ1 OW ((qb, f + 80, 32) :: LB) m5).
    { eapply (@AH_frame (push AR f 2)); [exact HEAPb| exact MU| exact WM|]. constructor; [left; cbn [fst snd]; clear - CEIL1 LOSP1 TOP1 SPAH GSZ TOP ESS; plia| constructor]. }
    apply evt_done. eapply implAp_step_same.
    { eapply (@asan_memset_frA (push AR f 2)) with (lo := lo) (d := f + 80) (n := 32) (c := Z_to_bv 8 0) (bd := (qb, f + 80, 32)); rewrite ?ESPA;
        [exact HEAP5| | exact CEIL| clear - LOSP1 ESS; unfold CHECK_TLEN_STACK_A, ACTL_FRAME, GETOBJ_STACK_A, ERR_SET_ERROR_STACK, ERR_VSET_ERROR_STACK in *; lia
        | exact TOP1| clear - AL161; unfold al16 in *; exact AL161| | reflexivity| apply in_or_app; right; left; reflexivity| cbn; clear; lia| cbn; clear; lia| clear; lia
        | reflexivity| reflexivity| reflexivity].
      all: assumption. }
    intros msM POM. destruct POM as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & FM & fcM & m6 & -> & MI6 & ST6 & HEAP6 & WM6 & AG6 & BZ6 & WR6).
    rewrite ?ESPA in *. unfold EX_MEMSET_RA. rewrite (ret_pc_even 0x2419f8) by (clear; lia).
    (* [comment removed for export] *)
    assert (FRA : forall a, f <= a < f + 248 -> @fr_addr (push AR f 2) a).
    { intros a Ha. left. exists f, 2%nat. split; [left; reflexivity| change (fs_size 2) with 256; clear - Ha; lia]. }
    assert (FSA : forall a, shad f <= a < shad f + 32 -> @fr_addr (push AR f 2) a).
    { intros a Ha. right. apply (@fr_shadow_in (push AR f 2) f 2%nat a (or_introl eq_refl)). change (fs_size 2) with 256. clear - Ha. lia. }
    apply (rw_cells_agree _ _ _ _ _ AG6) in FRL; [| intros a Ha; cbn [cells_size csize] in Ha; rewrite ?Nat2Z.inj_add in Ha; split; [left; left; clear - Ha GSZ SPAH TOP; unfold USTACK_TOP in *; lia| clear - Ha G3 CEIL LO ESS SPAL; plia]].
    thaw FRH.
    apply (rw_cells_agree _ _ _ _ _ AG4) in FRH; [| intros a Ha; cbn in Ha; cbn [outside fst snd]; clear - Ha SPAL SPAH G3 CEIL LO ESS SHR2 CL2; plia].
    apply (rw_cells_agree _ _ _ _ _ (agree_on_of_munch_nw _ _ _ MU)) in FRH; [| intros a Ha; cbn in Ha; cbn [outside fst snd]; clear - Ha SPAH; lia].
    apply (rw_cells_agree _ _ _ _ _ AG6) in FRH; [| intros a Ha; cbn in Ha; split; [left; left; clear - Ha SPAH TOP; unfold USTACK_TOP in *; lia| clear - Ha SPAH G3 CEIL LO ESS; plia]].
    thaw FRF. thaw FRS.
    apply (rw_cells_agree _ _ _ _ _ (agree_on_of_munch_nw _ _ _ MU)) in FRF; [| intros a Ha; cbn in Ha; cbn [outside fst snd]; clear - Ha SPAL G3 CEIL LO ESS; plia].
    apply (rw_cells_agree _ _ _ _ _ (agree_on_of_munch_nw _ _ _ MU)) in FRS; [| intros a Ha; cbn in Ha; cbn [outside fst snd]; clear - Ha SPAL CEIL LO ESS SHR2 CL2; plia].
    apply (rw_cells_agree _ _ _ _ _ AG6) in FRS; [| intros a Ha; cbn in Ha; split; [right; apply FSA; clear - Ha; lia| clear - Ha FSH; lia]].
    lazymatch type of FRF with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?c7 :: ?c8 :: ?c9 :: nil) =>
      change (c0 :: c1 :: c2 :: c3 :: c4 :: c5 :: c6 :: c7 :: c8 :: c9 :: nil) with ([c0; c1; c2; c3; c4; c5; c6; c7] ++ [c8] ++ [c9]) in FRF end.
    apply rw_cells_app in FRF as [FRF1 FRF]. apply rw_cells_app in FRF as [_ FRF3].
    cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add] in FRF3. replace (f + 80 + 32) with (f + 112) in FRF3 by (clear; lia).
    apply (rw_cells_agree _ _ _ _ _ AG6) in FRF1; [| intros a Ha; cbn in Ha; split; [right; apply FRA; clear - Ha; lia| clear - Ha; lia]].
    apply (rw_cells_agree _ _ _ _ _ AG6) in FRF3; [| intros a Ha; cbn in Ha; split; [right; apply FRA; clear - Ha; lia| clear - Ha; lia]].
    assert (FRF2 : rw_cells ctasegs m6 (f + 80) [CB 32 (repeat (Z_to_bv 8 0) 32)]).
    { apply rw_cells_of_u8arr with (bs := repeat (Z_to_bv 8 0) 32). split; [exact BZ6| cbn; exact WR6]. }
    assert (OFFQ : forall b a l h, In b LB -> blk_addr b <= l -> h <= blk_addr b + blk_size b -> l <= a < h ->
                   outside [(spa, spa); (f, f + 248); (shad f, shad f + 32)]%Z a /\ outside [(spa, spa + 168)]%Z a /\ ~ (f + 80 <= a < f + 80 + 32)).
    { intros b a l h Hb H1 H2 Ha. pose proof (OFFLB b Hb) as O. unfold off_fr in O. change (fs_size 2) with 256 in O.
      pose proof (AH_range_gen _ _ _ _ b HEAP (in_or_app _ _ _ (or_intror Hb))) as (_ & _ & _ & R3 & _).
      pose proof (AH_offsh _ _ _ _ b HEAP (in_or_app _ _ _ (or_intror Hb))) as RO. unfold SHLO, SHHI in RO.
      cbn [outside fst snd]. clear - O R3 RO H1 H2 Ha CEIL LO ESS SPAL SHR1 SHR2. plia. }
    thaw HOPP. thaw HPV. thaw HTLC. thaw HB.
    Local Ltac tr3 H b l h Hb H1 H2 AG4 MU AG6 OFFQ :=
      apply (rw_cells_agree _ _ _ _ _ AG4) in H; [| intros a Ha; cbn in Ha; exact (proj1 (OFFQ b a l h Hb H1 H2 Ha))];
      apply (rw_cells_agree _ _ _ _ _ (agree_on_of_munch_nw _ _ _ MU)) in H; [| intros a Ha; cbn in Ha; exact (proj1 (proj2 (OFFQ b a l h Hb H1 H2 Ha)))];
      apply (rw_cells_agree _ _ _ _ _ AG6) in H; [| intros a Ha; cbn in Ha; split; [left; right; right; exists b; split; [apply in_or_app; right; right; exact Hb| lia]| exact (proj2 (proj2 (OFFQ b a l h Hb H1 H2 Ha)))]].
    tr3 HOPP bq OPP (OPP + 8) Hbq BQ1 BQ2 AG4 MU AG6 OFFQ.
    tr3 HPV bv PV (PV + 8) Hbv BV1 BV2 AG4 MU AG6 OFFQ.
    tr3 HTLC bt TLC (TLC + 32) Hbt BT1 BT2 AG4 MU AG6 OFFQ.
    rewrite <- DLEN in BD2.
    apply (bytes_at_agree _ _ _ _ _ AG4) in HB; [| intros a Ha; exact (proj1 (OFFQ bd a D (D + Z.of_nat (length (to_bytes d))) Hbd BD1 BD2 Ha))].
    apply (bytes_at_agree _ _ _ _ _ (agree_on_of_munch_nw _ _ _ MU)) in HB; [| intros a Ha; exact (proj1 (proj2 (OFFQ bd a D (D + Z.of_nat (length (to_bytes d))) Hbd BD1 BD2 Ha)))].
    apply (bytes_at_agree _ _ _ _ _ AG6) in HB.
    2:{ intros a Ha. split; [left; right; right; exists bd; split; [apply in_or_app; right; right; exact Hbd| clear - Ha BD1 BD2; lia]| exact (proj2 (proj2 (OFFQ bd a D (D + Z.of_nat (length (to_bytes d))) Hbd BD1 BD2 Ha)))]. }
    rewrite DLEN in BD2.
    (* [comment removed for export] *)
    assert (CSB : forall a, client_static a -> a < 12365824).
    { intros a [(l & h & Hin & Hlh) _]. unfold CLIENT_STATIC in Hin. cbn [In] in Hin. clear - Hin Hlh. destruct Hin as [E0|[E0|[E0|[]]]]; injection E0 as <- <-; lia. }
    assert (ALLOUT : forall a, lib_addr OW a \/ aclient_addr LB (bv_unsigned sp) a ->
              outside [(spa, spa); (f, f + 248); (shad f, shad f + 32)]%Z a /\ outside [(spa, spa + 168)]%Z a
              /\ (aclient_addr (OW ++ (qb, f + 80, 32) :: LB) spa a /\ ~ (f + 80 <= a < f + 80 + 32))).
    { intros a HL. assert (LO3 : (a < BnHeapA.ACEIL /\ (a < SHLO \/ SHHI <= a) /\ (a < f \/ f + 256 <= a)) \/ (bv_unsigned sp <= a /\ a < USTACK_TOP)).
      { assert (BLK : forall b, In b (OW ++ LB) -> blk_addr b <= a < blk_addr b + blk_size b -> a < BnHeapA.ACEIL /\ (a < SHLO \/ SHHI <= a) /\ (a < f \/ f + 256 <= a)).
        { intros b Hb Hr. pose proof (AH_range_gen _ _ _ _ b HEAP Hb) as (_ & _ & _ & R3 & _). pose proof (AH_offsh _ _ _ _ b HEAP Hb) as RO.
          pose proof (FRESH b Hb) as O. unfold off_fr in O. change (fs_size 2) with 256 in O. clear - Hr R3 RO O. lia. }
        destruct HL as [[HS|(b & Hb & Hr)]|[H1|[H1|(b & Hb & Hr)]]].
        - left. pose proof (LIBW_S_A a HS) as HA. unfold LIBW_A in HA. cbn [rin_ivs fst snd] in HA. unfold SHLO. clear - HA CL1 CL2 G4. lia.
        - left. exact (BLK b (in_or_app _ _ _ (or_introl Hb)) Hr).
        - right. exact H1.
        - left. pose proof (CSB a H1) as HA. unfold SHLO. clear - HA CL1 G4. lia.
        - left. exact (BLK b (in_or_app _ _ _ (or_intror Hb)) Hr). }
      unfold SHLO, SHHI in LO3. cbn [outside fst snd]. split; [clear - LO3 CEIL LO ESS SPAL SPAH SHR1 SHR2 CL2 G3; plia|]. split; [clear - LO3 CEIL LO ESS SPAL SPAH G3; plia|].
      split; [| clear - LO3 G3 CEIL LO ESS SPAH; plia].
      destruct HL as [HL|Ha].
      - eapply acl_sub; [| | exact (lib_addr_aclient OW LB spa a HL)]; [intros b Hb; apply in_or_app; apply in_app_or in Hb; destruct Hb as [Hb|Hb]; [left; exact Hb| right; right; exact Hb]| clear; lia].
      - eapply acl_sub; [| | exact Ha]; [intros b Hb; apply in_or_app; right; right; exact Hb| clear - SPAH; lia]. }
    assert (AG36 : agree_on (fun a => lib_addr OW a \/ aclient_addr LB (bv_unsigned sp) a) m3 m6).
    { eapply agree_on_trans; [eapply agree_on_mono; [exact AG4|]; intros a Ha; exact (proj1 (ALLOUT a Ha))|].
      eapply agree_on_trans; [eapply agree_on_mono; [exact (agree_on_of_munch_nw _ _ _ MU)|]; intros a Ha; exact (proj1 (proj2 (ALLOUT a Ha)))|].
      eapply agree_on_mono; [exact AG6|]. intros a Ha. pose proof (ALLOUT a Ha) as (_ & _ & X). split; [left; exact (proj1 X)| exact (proj2 X)]. }
    assert (LAG6 : agree_on (lib_addr OW) m3 m6) by (eapply agree_on_mono; [exact AG36|]; intros a Ha; left; exact Ha).
    assert (AXG6 : agree_on (aclient_addr LB (bv_unsigned sp)) m3 m6) by (eapply agree_on_mono; [exact AG36|]; intros a Ha; right; exact Ha).
    clear AG4 MU WM AG6 ALLOUT AG36 OFFQ HEAPb HEAP5 BZ6 WR6 FRA FSA.
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    lazymatch type of FRL with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?c7 :: ?c8 :: ?c9 :: ?c10 :: ?c11 :: ?c12 :: ?c13 :: ?c14 :: ?c15 :: ?rest) =>
      change (c0 :: c1 :: c2 :: c3 :: c4 :: c5 :: c6 :: c7 :: c8 :: c9 :: c10 :: c11 :: c12 :: c13 :: c14 :: c15 :: rest)
        with ([c0; c1; c2; c3; c4; c5; c6; c7; c8; c9; c10; c11] ++ [c12] ++ [c13] ++ [c14] ++ [c15] ++ rest) in FRL end.
    apply rw_cells_app in FRL as [FRLA FRL]. apply rw_cells_app in FRL as [F96 FRL]. apply rw_cells_app in FRL as [F104 FRL]. apply rw_cells_app in FRL as [F112 FRL].
    apply rw_cells_app in FRL as [F120 FRLB].
    cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add] in F96, F104, F112, F120, FRLB.
    replace (spa + Z.of_nat 96) with (spa + 96) in F96 by (clear; lia).
    replace (spa + 96 + 8) with (spa + 104) in F104 by (clear; lia). replace (spa + 96 + 8 + 8) with (spa + 112) in F112 by (clear; lia).
    replace (spa + 96 + 8 + 8 + 8) with (spa + 120) in F120 by (clear; lia). replace (spa + 96 + 8 + 8 + 8 + 8) with (spa + 128) in FRLB by (clear; lia).
    apply (cb_splitA _ _ 6 2) in F104. lazymatch type of F104 with rw_cells _ _ _ [?c1; ?c2] => change [c1; c2] with ([c1] ++ [c2]) in F104 end.
    apply rw_cells_app in F104 as [F104 F110]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in F110. replace (spa + 104 + 6) with (spa + 110) in F110 by (clear; lia).
    apply (cb_splitA _ _ 1 1) in F110. lazymatch type of F110 with rw_cells _ _ _ [?c1; ?c2] => change [c1; c2] with ([c1] ++ [c2]) in F110 end.
    apply rw_cells_app in F110 as [F110 F111]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in F111. replace (spa + 110 + 1) with (spa + 111) in F111 by (clear; lia).
    destruct (cb_byteA _ _ _ F110) as [bi F110']. clear F110. destruct (cb_byteA _ _ _ F111) as [bc F111']. clear F111.
    apply (cb_splitA _ _ 4 4) in F120.
    (* [comment removed for export] *)
    destruct (@item_cellsA_octet (push AR f 2) _ _ _ _ HEAP6) as (IT0 & IT8 & IT8L & IT16 & IT32 & ACCIT).
    unfold ITEM_OCTET_A in *.   (* [comment removed for export] *)
    replace (5535264 + 8) with 5535272 in IT8, IT8L by reflexivity. replace (5535264 + 16) with 5535280 in IT16 by reflexivity.
    replace (5535264 + 32) with 5535296 in IT32 by reflexivity.
    assert (ACCQ : acc ctasegs m6 OPP 8) by (eapply acc_sub; [exact (proj2 (@AH_acc (push AR f 2) _ _ _ _ _ HEAP6 (in_or_app OW ((qb, f + 80, 32) :: LB) bq (or_intror (in_cons _ _ _ Hbq)))))| exact BQ1| exact BQ2]).
    assert (EOPP : bv_unsigned (Z_to_bv 64 OPP) = OPP) by (apply unsigned_lit; clear - BQ1 BQ2 BQ3 BQ4 CL3; unfold BnHeapA.ACEIL in *; lia).
    pose proof (munch_refl [(spa, spa + 168)]%Z m6) as MU. pose proof (wmono_refl ctasegs m6) as WM.
    freeze FRF1. freeze FRF2. freeze FRF3. freeze FRS. freeze HPV. freeze HTLC. freeze FRH. freeze HB.
    apply implAp_from_evt.
    (* [comment removed for export] *)
    step. step. step. if_true.
    (* [comment removed for export] *)
    step. rewrite (sx32_small V_ASN1_OCTET_STRING) by (unfold V_ASN1_OCTET_STRING; clear; lia). step. step.
    step. if_cases KANY; zc KANY; [| exfalso; clear - KANY; unfold V_ASN1_OCTET_STRING in KANY; rewrite land64_pos_small in KANY by (clear; lia); clear - KANY; lia].
    (* [comment removed for export] *)
    step. step. step. if_false. step. rewrite (sx32_small V_ASN1_OCTET_STRING) by (unfold V_ASN1_OCTET_STRING; clear; lia). step.
    (* [comment removed for export] *)
    step. step. step. step. rewrite ?EOPP.
    (* [comment removed for export] *)
    step. step. step. step. step. step. step. step. step. step. step. step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m7 end.
    match goal with H : munch _ m6 m7 |- _ => rename H into MU7 end. match goal with H : wmono ctasegs m6 m7 |- _ => rename H into WM7 end.
    match goal with H : stk ctasegs m7 lo spa |- _ => rename H into ST7 end. match goal with H : mem_inv ctasegs m7 |- _ => rename H into MI7 end.
    apply evt_done. rewrite ?EOPP in FRLA.
    (* [comment removed for export] *)
    thaw FRS. thaw FRF1.
    apply (rw_cells_agree _ _ _ _ _ (agree_on_of_munch_nw _ _ _ MU7)) in FRS; [| intros a Ha; cbn in Ha; cbn [outside fst snd]; clear - Ha SPAL CEIL LO ESS SHR2 CL2; plia].
    apply (rw_cells_agree _ _ _ _ _ (agree_on_of_munch_nw _ _ _ MU7)) in FRF1; [| intros a Ha; cbn in Ha; cbn [outside fst snd]; clear - Ha SPAL G3 CEIL LO ESS; plia].
    assert (HEAP7 : @BnHeapA.AHEAP (push AR f 2) Σ1 OW ((qb, f + 80, 32) :: LB) m7).
    { eapply (@AH_frame (push AR f 2)); [exact HEAP6| exact MU7| exact WM7|]. constructor; [left; cbn [fst snd]; clear - CEIL1 LOSP1 TOP1 SPAH GSZ TOP ESS; plia| constructor]. }
    destruct (bptr_fresh (map blk_id (OW ++ (qb, f + 80, 32) :: LB))) as [qfc Hqfc].
    assert (HEAP7f : @BnHeapA.AHEAP (push AR f 2) Σ1 OW (pbs qfc qb ++ LB) m7).
    { unfold exo_pbs. cbn [app]. apply (@frame_obj_open (push AR f 2) Σ1 OW ((qb, f + 80, 32) :: LB) m7 f 2%nat qfc (f + 64) 1 (or_introl eq_refl) HEAP7);
        [clear; lia| change (fs_size 2) with 256; clear; lia| clear; lia| | exact Hqfc|].
      - eapply (acc_of_shadow_cells m7 (shad f) _ 8 (f + 64) 1 FRS); [clear - G2; Z.div_mod_to_equations; lia| clear - G1; lia| clear; lia
          | unfold shad; clear - G2; Z.div_mod_to_equations; lia| cbn; clear; lia| reflexivity].
      - intros b [<-|Hb]; [unfold blk_apart; cbn [blk_addr blk_size fst snd]; clear; lia|].
        pose proof (OFFLB b Hb) as O. unfold off_fr in O. change (fs_size 2) with 256 in O. unfold blk_apart. cbn [blk_addr blk_size fst snd]. clear - O. lia. }
    (* [comment removed for export] *)
    lazymatch type of FRF1 with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?c7 :: nil) =>
      change (c0 :: c1 :: c2 :: c3 :: c4 :: c5 :: c6 :: c7 :: nil) with ([c0; c1; c2; c3; c4; c5] ++ [c6] ++ [c7]) in FRF1 end.
    apply rw_cells_app in FRF1 as [_ FRF1]. apply rw_cells_app in FRF1 as [HFC _].
    cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add] in HFC. try replace (f + Z.of_nat 64) with (f + 64) in HFC by (clear; lia). try replace (f + 64 + 0) with (f + 64) in HFC by (clear; lia).
    (* [comment removed for export] *)
    assert (LAG7 : agree_on (lib_addr OW) m3 m7).
    { eapply agree_on_trans; [exact LAG6|]. eapply agree_on_mono; [exact (agree_on_of_munch_nw _ _ _ MU7)|]. intros a HL. cbn [outside fst snd].
      destruct HL as [HS|(b & Hb & Hr)].
      - pose proof (LIBW_S_A a HS) as HA. unfold LIBW_A in HA. cbn [rin_ivs fst snd] in HA. clear - HA CL1 CEIL LO ESS SPAL. lia.
      - pose proof (AH_range_gen _ _ _ _ b HEAP (in_or_app _ _ _ (or_introl Hb))) as (_ & _ & _ & R3 & _). clear - Hr R3 CEIL LO ESS SPAL. lia. }
    assert (AXG7 : agree_on (aclient_addr LB (bv_unsigned sp)) m3 m7).
    { eapply agree_on_trans; [exact AXG6|]. eapply agree_on_mono; [exact (agree_on_of_munch_nw _ _ _ MU7)|]. intros a Ha. cbn [outside fst snd].
      destruct Ha as [H1|[H1|(b & Hb & Hr)]].
      - clear - H1 SPAH. lia.
      - pose proof (CSB a H1) as HA. clear - HA CL1 CEIL LO ESS SPAL. lia.
      - pose proof (AH_range_gen _ _ _ _ b HEAP (in_or_app _ _ _ (or_intror Hb))) as (_ & _ & _ & R3 & _). clear - Hr R3 CEIL LO ESS SPAL. lia. }
    thaw HTLC. apply (rw_cells_agree _ _ _ _ _ (agree_on_of_munch_nw _ _ _ MU7)) in HTLC; [| intros a Ha; cbn in Ha; cbn [outside fst snd]; clear - Ha BT1 BT2 BT4 CEIL LO ESS SPAL; plia].
    thaw HPV. apply (rw_cells_agree _ _ _ _ _ (agree_on_of_munch_nw _ _ _ MU7)) in HPV; [| intros a Ha; cbn in Ha; cbn [outside fst snd]; clear - Ha BV1 BV2 BV4 CEIL LO ESS SPAL; plia].
    thaw FRH. apply (rw_cells_agree _ _ _ _ _ (agree_on_of_munch_nw _ _ _ MU7)) in FRH; [| intros a Ha; cbn in Ha; cbn [outside fst snd]; clear - Ha SPAH; lia].
    thaw FRF2. apply (rw_cells_agree _ _ _ _ _ (agree_on_of_munch_nw _ _ _ MU7)) in FRF2; [| intros a Ha; cbn in Ha; cbn [outside fst snd]; clear - Ha SPAL G3 CEIL LO ESS; plia].
    thaw HB. rewrite <- DLEN in BD2.
    apply (bytes_at_agree _ _ _ _ _ (agree_on_of_munch_nw _ _ _ MU7)) in HB; [| intros a Ha; cbn [outside fst snd]; clear - Ha BD1 BD2 BD4 CEIL LO ESS SPAL; plia].
    rewrite DLEN in BD2.
    (* [comment removed for export] *)
    assert (PREX7 : @ap_preA (push AR f 2) Σ1 st m7 OW (pbs qfc qb ++ LB) E bo (Z_to_bv 64 spa) lo (STK - ADEP_FRAME) (CST len - 1) (FRMb - 1)).
    { eapply (@ap_preA_memA (push AR f 2)); [exact PRE1| exact HEAP7f| exact LAG7| rewrite ESPA; exact ST7| exact MI7]. }
    assert (LI7 : linv qfc qb m7 Σ1 st m7 OW bo [] (CST len - 1)).
    { unfold exo_inv, oinv. cbn [app]. replace (Z_to_bv 64 (bv_unsigned sp + (spa - bv_unsigned sp))) with (Z_to_bv 64 spa) by (f_equal; clear; lia).
      split; [exact PREX7|]. split; [apply ax_pres_refl|]. split; [exact KOW|]. split; [exact KIDS|]. split; [apply CtRepP.ApErrKit.kept_refl|]. split; [exact HB|].
      split; [unfold len; clear; lia| constructor]. }
    assert (AGFr7 : agree_on (aclient_addr (OW ++ LB) (bv_unsigned sp)) m m7).
    { eapply agree_on_trans; [exact AGF|]. intros a Hr Ha. destruct Ha as [H1|[H1|(b & Hb & Hrr)]].
      - exact (AXG7 a Hr (or_introl H1)).
      - exact (AXG7 a Hr (or_intror (or_introl H1))).
      - apply in_app_iff in Hb as [Hb|Hb]; [exact (LAG7 a Hr (or_intror (ex_intro _ b (conj Hb Hrr))))| exact (AXG7 a Hr (or_intror (or_intror (ex_intro _ b (conj Hb Hrr)))))]. }
    assert (UW7 : uw_chain USTACK_TOP m7 spa (bv_unsigned sp) (bv_unsigned ra :: ras)).
    { eapply (uw_call m m7 spa (bv_unsigned sp) 16 [] (bv_unsigned ra) (bv_unsigned s0) ras);
        [ exact UW
        | eapply agree_on_trans; [eapply agree_on_mono; [exact AGF|]; intros a Ha; left; exact Ha | eapply agree_on_mono; [exact AXG7|]; intros a Ha; left; exact Ha]
        | reflexivity | clear - SPAH; lia | uchk_open; clear - AL16; Z.div_mod_to_equations; lia | clear - TOP; unfold USTACK_TOP in *; lia
        | apply bv_unsigned_in_range | rewrite !Z_to_bv_bv_unsigned; cbn [app]; exact FRH ]. }
    assert (XF : EXC m7 j0 j8 j16 j24 j64 j72 j80 (firstn 6 j104) (firstn 4 j120) j128 j136 j144).
    { unfold exc_facts, exo_lowD. split; [exact AGFr7|]. split; [exact UW7|]. split; [exact FRLA|]. split; [exact F104|]. split; [exact F120|]. split; [exact FRLB|].
      split; [exact FRH|]. split; [exact HFC|]. split; [exact FRF2|]. split; [exact HOPP| exact HPV]. }
    (* [comment removed for export] *)
    pose proof (rw_cells_app_join m7 _ _ _ F110' ltac:(cbn [cells_size csize Nat.add]; replace (spa + 110 + Z.of_nat 1) with (spa + 111) by (clear; lia); exact F111')) as FP1.
    pose proof (rw_cells_app_join m7 _ _ _ FP1 ltac:(cbn [cells_size csize Nat.add app]; replace (spa + 110 + Z.of_nat 2) with (spa + 112) by (clear; lia); exact F112)) as FPIC.
    cbn [app] in FPIC. clear FP1.
    (* [comment removed for export] *)
    pose proof (HCTL (push AR f 2) STRCPY sp m7 Σ1 (pbs qfc qb ++ LB) E lo K d D XP (spa - bv_unsigned sp) (STK - ADEP_FRAME) (CST len - 1) (FRMb - 1)
                  (exo_KH STK CST FRMb sp m Σ st OW LB E bo lo D d OPP PV TLC j31 f spa PRE0 CELLS LEN1 FRESH GEO SPA32 SPAL SPAH STKB qfc qb) D0 D63 D26
                  (option (CtModel.octet bptr)) (Some V_ASN1_OCTET_STRING)) as W.
    cbv beta iota delta [check_tlen_gen_actA CtColP.W_check_tlen_gen.tlen_tree] in W.
    pose proof col_consts as (KC1 & KC2 & KC3 & KC4 & KC5 & KC6 & KC7).
    unfold d2i_exprim. cbv zeta.
    replace (Z_to_bv 64 (bv_unsigned sp + (spa - bv_unsigned sp))) with (Z_to_bv 64 spa) in W by (f_equal; clear; lia).
    replace (Z_to_bv 64 (spa + 112)) with (Z_to_bv 64 (spa + 110 + 2)) by (f_equal; clear; lia).
    replace (Z_to_bv 64 (spa + 111)) with (Z_to_bv 64 (spa + 110 + 1)) by (f_equal; clear; lia).
    eapply W with (TLCo := Some TLC) (PIC := spa + 110) (PPC := spa + 96) (op := 0) (j31 := j31) (bi := bi) (bc := bc) (jl := j112); clear W;
      [ rewrite KC1; pose proof STKB as X; rewrite KC1 in X; unfold ADEP_FRAME in *; clear - X; lia
      | rewrite KC4; pose proof FRMBb as X; rewrite KC4 in X; clear - X; lia
      | exact LI7
      | rewrite KC6; unfold len in *; clear - CSTB LEN1; lia
      | replace (bv_unsigned sp + (spa - bv_unsigned sp)) with spa by (clear; lia); exact UW7
      | rewrite unsigned_lit by (clear; lia); exact (uk_ctx_call _ _ _ _ E_ex_ct CTX)
      | apply cons_ne
      | clear; lia | exact LEN1 | unfold len; clear; lia | unfold V_ASN1_OCTET_STRING; clear; lia
      | clear; lia | clear - SPAH; lia | clear; lia | clear - SPAH; lia | clear; lia
      | clear - SPA32; Z.div_mod_to_equations; lia | clear - SPA32; Z.div_mod_to_equations; lia
      | split; [unfold exo_XP; cbn [In]; right; right; left; reflexivity| split; [exact ALT| exact HTLC]]
      | exact FPIC
      | replace (D + 0) with D by (clear; lia); exact F96
      | | | ].
    - (* [comment removed for export] *)
      intros e st' Σ' ms' bi' bc' jl' CX' EGe HCX POT. unfold tlen_postA in POT.
      destruct POT as (y0 & y1 & y2 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & y3 & y4 & y5 & y6 & FY & fcY & mY & OWY & boY & -> & OIY & AXY & HPICY & HPPCY & (vb & jt & HTLCY)).
      rewrite (ret_pc_even 2366320) by (clear; lia). pose proof (ctl_costA_range gr (Some V_ASN1_OCTET_STRING)) as CR9.
      eapply (exo_after_fail STRCPY STK CST FRMb ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m Σ st OW LB E bo lo K adr D d OPP PV TLC j31 f spa g junk gj Σ1 PRE0 ras CTX KOW CELLS LEN1 FRESH
                GEO CR1 SPA32 SPAL SPAH GSZ SAVJ STKB FRMBb qfc qb m7);
        [exact XF| exact OIY| rewrite KC3, KC6 in *; unfold gr in *; unfold len in *; clear - HCX CR9 CSTB LEN1; lia| exact AXY| exact HPICY| exact HPPCY| exact HTLCY].
    - (* [comment removed for export] *)
      intros t st' Σ' ms' bi' bc' jl' CX' ET EGe NT HCX POT. unfold tlen_postA in POT.
      destruct POT as (y0 & y1 & y2 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & y3 & y4 & y5 & y6 & FY & fcY & mY & OWY & boY & -> & OIY & AXY & HPICY & HPPCY & (vb & jt & HTLCY)).
      rewrite (ret_pc_even 2366320) by (clear; lia). pose proof (ctl_costA_range gr (Some V_ASN1_OCTET_STRING)) as CR9.
      eapply (exo_after_fail STRCPY STK CST FRMb ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m Σ st OW LB E bo lo K adr D d OPP PV TLC j31 f spa g junk gj Σ1 PRE0 ras CTX KOW CELLS LEN1 FRESH
                GEO CR1 SPA32 SPAL SPAH GSZ SAVJ STKB FRMBb qfc qb m7);
        [exact XF| exact OIY| rewrite KC3, KC6 in *; unfold gr in *; unfold len in *; clear - HCX CR9 CSTB LEN1; lia| exact AXY| exact HPICY| exact HPPCY| exact HTLCY].
    - (* [comment removed for export] *)
      intros st' Σ' ms' CX' EGe [ETAG ECLS] HCX POT. unfold tlen_postA in POT.
      destruct POT as (y0 & y1 & y2 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & y3 & y4 & y5 & y6 & FY & fcY & mY & OWY & boY & -> & OIY & AXY & HPICY & HPPCY & (vb & jt & HTLCY)).
      rewrite (ret_pc_even 2366320) by (clear; lia).
      assert (HCX2 : CST len - 2 <= CX') by (unfold ctl_costA in HCX; rewrite EGe, ETAG, ECLS in HCX; cbn [Z.eqb negb orb V_ASN1_OCTET_STRING] in HCX; rewrite ?Z.eqb_refl in HCX; cbn in HCX; clear - HCX; lia).
      eapply (exo_after_ok STK CST FRMb ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m Σ st OW LB E bo lo K adr D d OPP PV TLC j31 f spa g junk gj Σ1 PRE0 ras CELLS LEN1 FRESH
                GEO SPA32 SPAL SPAH GSZ SAVJ STKB HPRIM HCONS qfc qb m7);
        [exact XF| exact OIY| exact HCX2| exact AXY| exact EGe| exact ETAG| exact ECLS| exact HPICY| exact HPPCY| exact HTLCY].
  Qed.
End Body.
End WithRT.
