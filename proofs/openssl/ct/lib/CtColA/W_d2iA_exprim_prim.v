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
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepP Require W_get_object W_get_object_walk W_check_tlen.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApUTac.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require Import I_strcpyA ApATac ApATacX ApBImg ApWalkTac ApRepDefs ApRep ApIface ApFrame W_akit W_get_objectA W_check_tlenA W_item_d2i_stmtA W_item_d2i_imgA W_c2i_stmtA W_frkitA Fr_asn1_check_tlen Fr_asn1_d2i_ex_primitive W_err_newA W_err_set_debugA W_err_vsetA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require W_get_object_walkA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require Import W_item_d2i_exA W_item_d2i_tailA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtSctP Require SctStmt.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtSctA Require Import SctRepA SctStmtA O2iKitA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtColA Require Import ColBudgetA ColDefsA CtlStmtA W_bufmemA W_collectA W_d2iA_stmt W_d2iA_exprim_ctx W_d2iA_exprim_tail W_d2iA_exprim_call W_d2iA_exprim_seg.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require Import W_asn1_stringA ApErrKitA2 W_item_d2i_octA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require W_prefix_create.
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
(* [comment removed for export] *)
Ltac cell_of_bytes bs ::=
  lazymatch bs with
  | le8 ?v => constr:(C8 v)
  | le4 ?v => constr:(C4 v)
  | le2 ?v => constr:(C2 v)
  | [?b] => constr:(C1 b)
  | le1 (zxb ?b) => constr:(C1 b)
  | le1 (Z_to_bv 64 ?z) => constr:(C1 (Z_to_bv 8 z))
  | Z_to_le_bytes 8 ?z => constr:(C8 (Z_to_bv 64 z))
  | Z_to_le_bytes 4 ?z => constr:(C4 (Z_to_bv 64 z))
  | Z_to_le_bytes 1 ?z => constr:(C1 (Z_to_bv 8 z))
  end.
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
Definition EX_SET1_RA : Z := 0x242540.      (* [comment removed for export] *)
Local Notation E_ex_set1 := (E_asn1_d2i_ex_primitive_244fb4 : uk_call 0x24187c 0x242540 0x2249e8).    (* [comment removed for export] *)

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
  Local Notation EXD := (exd_facts STK CST FRMb ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m OW LB E lo K D d OPP PV TLC f spa g junk gj Σ1 ras).
  Local Notation EXMS := (exd_ms sp gp TLC f spa).

  (* [comment removed for export] *)
  Lemma exo_prim : forall qfc qb mr ΣX stX mX OWX boX CX (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) FX fcX
      (j0 j8 j16 j24 j64 j72 j80 j104 j120 j128 j136 j144 jt : list byte) (vb : byte),
    Z.land (go_ret gr) 32 = 0 ->
    EXD qfc qb mr ΣX stX mX OWX boX CX j0 j8 j16 j24 j64 j72 j80 j104 j120 j128 j136 j144 jt vb ->
    @implAp (push AR f 2) _
      ((blk <- amalloc SZ_ASN1_STRING ;;
        dp <- amalloc_crypto plen ;;
        aret (Some (CtModel.mkOct blk (option_map (fun q => (q, plen)) dp) plen (CtWire.slice d (go_p gr) plen)))) stX)
      ΣX POST (EXMS EX_PRIM_ARM x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 FX fcX mX).
  Proof.
    intros until vb. intros EC XD. ctx. pose proof PRE0 as (HEAP & _).
    pose proof CELLS as (_ & _ & _ & _ & ALO & ALV & ALT & DOV & DOT & DVT & DOD & DVD & DTD & _).
    destruct XD as (AGFr & LI & CXB & UWX & FRLA & F96 & F104 & F110 & F111 & F112 & F120 & FRLB & FRH & HFC & HBUF & HOPPX & HPVX & HTLCX & EG & ETAG & ECLS & SAVJ').
    pose proof col_consts as (KC1 & KC2 & KC3 & KC4 & KC5 & KC6 & KC7).
    kitp (@oinv_call (push AR f 2)) qfc qb mr OC.
    pose proof (OC _ _ _ _ _ _ _ LI) as (HEAPX & STX & _ & _ & _ & _ & MIX & _). replace (bv_unsigned sp + (spa - bv_unsigned sp)) with spa in STX by (clear; lia).
    (* [comment removed for export] *)
    pose proof (get_object_bounds d 0 len ltac:(eapply Forall_impl; [| exact DF]; cbv beta; intros x Hx; clear - Hx; lia) LEN1) as GB. cbv zeta in GB. fold gr in GB. rewrite EG in GB.
    destruct GB as (GB1 & GB2 & GB3).
    assert (PLB : 0 <= plen /\ go_p gr + plen <= len) by (unfold plen; destruct (Z.testbit (go_ret gr) 0); clear - GB1 GB2 GB3; lia).
    assert (PL31 : plen < 2 ^ 31) by (unfold len in *; clear - PLB GB1 D26; lia).
    assert (ECV : bv_unsigned (Z_to_bv 64 (D + go_p gr)) = D + go_p gr) by (apply unsigned_lit; unfold len in *; clear - D0 D63 GB1 PLB; lia).
    assert (EPL : bv_unsigned (Z_to_bv 64 plen) = plen) by (apply unsigned_lit; clear - PLB PL31; lia).
    hide DOV. hide DOT. hide DVT. hide DOD. hide DVD. hide DTD. hide OD. hide OQ. hide OV. hide OT. hide BD5. hide BQ5. hide BV5. hide BT5. hide G5.
    unfold exo_lowD, exd_ms, EX_PRIM_ARM, MallocRep.wz in *.
    (* [comment removed for export] *)
    pose proof (munch_refl [(spa, spa + 168)]%Z mX) as MU. pose proof (wmono_refl ctasegs mX) as WM.
    freeze HFC. freeze HBUF. freeze HOPPX. freeze HPVX. freeze HTLCX. freeze FRH.
    apply implAp_from_evt.
    step. step. step. fold len. fold gr. fold plen. rewrite ?ECV, ?EPL. step. step. name_mem m1.      (* [comment removed for export] *)
    match goal with H : munch _ mX m1 |- _ => rename H into MU1 end. match goal with H : wmono ctasegs mX m1 |- _ => rename H into WM1 end.
    match goal with H : stk ctasegs m1 lo _ |- _ => rename H into ST1 end. match goal with H : mem_inv ctasegs m1 |- _ => rename H into MI1 end. rewrite ?ESPA in ST1.
    assert (LI1 : linv qfc qb mr ΣX stX m1 OWX boX [] CX).
    { kitp (@oinv_munch (push AR f 2)) qfc qb mr OM. eapply OM; [exact LI| exact MU1| exact WM1| exact MI1| replace (bv_unsigned sp + (spa - bv_unsigned sp)) with spa by (clear; lia); exact ST1|].
      constructor; [left; cbn [fst snd]; clear - SPAH CEIL LO ESS SPAL; lia| constructor]. }
    thaw HFC. thaw HBUF. thaw HOPPX. thaw HPVX. thaw HTLCX. thaw FRH.
    pose proof (AH_offsh _ _ _ _ bq HEAP (in_or_app _ _ _ (or_intror Hbq))) as ROQ. pose proof (AH_offsh _ _ _ _ bv HEAP (in_or_app _ _ _ (or_intror Hbv))) as ROV.
    pose proof (AH_offsh _ _ _ _ bt HEAP (in_or_app _ _ _ (or_intror Hbt))) as ROT. unfold SHLO, SHHI in ROQ, ROV, ROT.
    Local Ltac mv1 H MU1 tac := apply (rw_cells_agree _ _ _ _ _ (agree_on_of_munch_nw _ _ _ MU1)) in H; [| intros a Ha; cbn in Ha; cbn [outside fst snd]; tac].
    mv1 HFC MU1 ltac:(clear - Ha G3 CEIL LO ESS SPAL; plia). mv1 HBUF MU1 ltac:(clear - Ha G3 CEIL LO ESS SPAL; plia).
    mv1 HOPPX MU1 ltac:(clear - Ha BQ1 BQ2 BQ4 CEIL LO ESS SPAL; lia). mv1 HPVX MU1 ltac:(clear - Ha BV1 BV2 BV4 CEIL LO ESS SPAL; lia).
    mv1 HTLCX MU1 ltac:(clear - Ha BT1 BT2 BT4 CEIL LO ESS SPAL; lia). mv1 FRH MU1 ltac:(clear - Ha SPAH; lia).
    assert (UW1 : uw_chain USTACK_TOP m1 spa (bv_unsigned sp) (bv_unsigned ra :: ras)).
    { eapply uw_chain_agree16; [exact UWX|]. eapply agree_on_mono; [exact (agree_on_of_munch_nw _ _ _ MU1)|]. intros a Ha. cbv beta in Ha. cbn [outside fst snd]. clear - Ha SPAH. lia. }
    apply evt_done. unfold EX_C2I.
    eapply (exo_c2i STK CST FRMb ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m Σ st OW LB E bo lo K adr D d OPP PV TLC j31 f spa g junk Σ1 PRE0 ras CTX CELLS LEN1 FRESH GEO SPA32 SPAL SPAH GSZ STKB qfc qb mr) with
      (CV := D + go_p gr) (L := plen) (PEND := D + go_p gr + plen) (fcv := 0) (bufc := [CB 32 (repeat (Z_to_bv 8 0) 32)]);
      [exact AGFr| exact LI1| clear - CXB CSTB LEN1; unfold len in *; lia| exact UW1| clear - PLB PL31; lia| unfold len in *; clear - D0 D63 GB1 PLB; lia| clear; lia| reflexivity
      | exact FRLA| exact F96| exact F104| exact F110| exact F111| exact F112| exact F120| exact FRLB| exact FRH| exact HFC| exact HBUF| exact HOPPX| exact HPVX| exact HTLCX|].
    (* [comment removed for export] *)
    intros p ΣY ms' PC.
    destruct PC as (y1 & y5 & y6 & y7 & y10 & y12 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & FY & fcY & mY & A & OWX' & boX' & -> & EFC & LIY & NIp & AR24 & A16
                    & HSTR & UWY & FRLAy & F96y & F104y & F110y & F111y & F112y & F120y & FRLBy & FRHy & HCONTy & HFCy & HBUFy & HOPPy & HPVy & HTLCy & KEEPN).
    clear KEEPN HCONTy MU1 WM1 LI1 UW1 FRLA F96 F104 F110 F111 F112 F120 FRLB FRH HFC HBUF HOPPX HPVX HTLCX. clear ST1 MI1.
    (* [comment removed for export] *)
    pose proof (OC _ _ _ _ _ _ _ LIY) as (HEAPY & STY & _ & LOY & TOPY & ALY & MIY & CSY & ASY & CRY & _).
    replace (bv_unsigned sp + (spa - bv_unsigned sp)) with spa in STY, LOY, TOPY, ALY by (clear; lia). cbn [ar_RT push amb] in CRY.
    pose proof ASY as (_ & (_ & RSY & _) & _).
    kitp (@oinv_facts (push AR f 2)) qfc qb mr OFc. pose proof (OFc _ _ _ _ _ _ _ LIY) as (_ & NDY & BNDY & FRSHY & DJLY & DJOY). clear OFc.
    pose proof LIY as (_ & _ & _ & _ & _ & HBY & _ & LBOKY).
    pose proof AR24 as (BA0 & BA16 & _ & BAC & BAS). unfold ASN1_STRING_SIZE in BAC, BAS.
    assert (NIpl : ~ In p (map blk_id (pbs qfc qb ++ LB))) by (intros X; apply NIp; rewrite map_app; apply in_or_app; right; cbn [app]; exact X).
    (* [comment removed for export] *)
    assert (HEAPO : @BnHeapA.AHEAP (push AR f 2) ΣY ((p, A, 24) :: OWX') (pbs qfc qb ++ LB) mY).
    { pose proof (@AH_adopt (push AR f 2) _ _ _ _ (p, A, 24) HEAPY ltac:(apply in_or_app; left; left; reflexivity) (Forall_inv LBOKY)) as H.
      rewrite lb_remove_cons in H. cbn [blk_id fst snd] in H. rewrite bptr_eqb_refl in H. cbn [app] in H. rewrite (lb_remove_notin _ _ NIpl) in H. exact H. }
    pose proof (@AH_ow_off_fr (push AR f 2) _ _ _ _ f 2%nat (p, A, 24) HEAPO (or_introl eq_refl) (or_introl eq_refl)) as OA.
    unfold off_fr in OA. change (fs_size 2) with 256 in OA. cbn [blk_addr blk_size fst snd] in OA.
    destruct (slice_bytes_a mY D d (go_p gr) plen HBY DF ltac:(clear - GB1; lia) (proj1 PLB) ltac:(unfold len in PLB; clear - PLB; lia)) as [SRC SLEN].
    pose proof (mcost_nonneg plen (proj1 PLB)) as MC0.
    assert (MCB : mcost plen <= CX) by (unfold mcost; destruct (plen <=? 64512); unfold len in *; clear - CXB CSTB PLB GB1; lia).
    assert (ESK : ASN1_STRING_SET_STACK + 208 <= CHECK_TLEN_STACK_A)
      by (unfold ASN1_STRING_SET_STACK, CRYPTO_MALLOC_STACK, CHECK_TLEN_STACK_A, ACTL_FRAME, GETOBJ_STACK_A, ERR_SET_ERROR_STACK, ERR_VSET_ERROR_STACK; clear; lia).
    assert (NBD : blk_id bd <> p) by (intros X; apply NIpl; rewrite <- X, map_app; apply in_or_app; right; apply in_map; exact Hbd).
    (* [comment removed for export] *)
    assert (Ey10 : y10 = Z_to_bv 64 0) by (apply bv_eq; rewrite EFC, unsigned_lit by (clear; lia); reflexivity). subst y10.
    freeze HSTR. freeze FRLAy. freeze F96y. freeze F104y. freeze F110y. freeze F111y. freeze F112y. freeze F120y. freeze FRLBy. freeze FRHy.
    freeze HFCy. freeze HBUFy. freeze HOPPy. freeze HPVy. freeze HTLCy.
    pose proof (munch_refl ([] : list (Z * Z)) mY) as MU. pose proof (wmono_refl ctasegs mY) as WM.
    apply implAp_from_evt. unfold EX_FC_TEST. step. if_true. step. step. step. step. apply evt_done. clear MU WM.
    thaw HSTR. thaw FRLAy. thaw F96y. thaw F104y. thaw F110y. thaw F111y. thaw F112y. thaw F120y. thaw FRLBy. thaw FRHy.
    thaw HFCy. thaw HBUFy. thaw HOPPy. thaw HPVy. thaw HTLCy.
    destruct (Z.eq_dec plen 0) as [PZ|PNZ].
    + (* [comment removed for export] *)
      unfold abind, amalloc_crypto. rewrite (proj2 (Z.eqb_eq _ _) PZ). cbn [apbind fst snd].
      eapply implAp_step_same.
      { eapply (@ASN1_STRING_set1_data_zero_cpsA (push AR f 2) UK BE) with (lo := lo) (A := A) (pblk := p); rewrite ?ESPA;
          [exact HEAPO| exact STY| exact CEIL| clear - LOY STKB ESK; lia| exact TOPY| exact ALY| exact MIY| reflexivity| exact CSY
          | left; reflexivity| exact HSTR| unfold ApPrim.V_ASN1_OCTET_STRING, CtSizes.V_ASN1_OCTET_STRING; clear; lia| unfold ApPrim.V_ASN1_OCTET_STRING, CtSizes.V_ASN1_OCTET_STRING; clear; lia
          | reflexivity| rewrite PZ; reflexivity
          | exact UWY| rewrite unsigned_lit by (clear; lia); exact (uk_ctx_call _ _ _ _ E_ex_set1 CTX)]. }
      intros msd POd. destruct POd as (w0 & w1 & w2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & w3 & w4 & w5 & w6 & Fd & fcd & md & -> & MId & STd & APX & HEAPd & CELLd).
      rewrite ESPA in STd, APX. rewrite (ret_pc_even 0x242540) by (clear; lia). unfold ASN1_STRING_SIZE in APX.
      unfold aret. cbn [option_map].
      (* [comment removed for export] *)
      assert (AXS : forall A0 cs, rw_cells ctasegs mY A0 cs -> spa <= A0 -> A0 + Z.of_nat (cells_size cs) <= USTACK_TOP -> rw_cells ctasegs md A0 cs).
      { intros A0 cs HC H1 H2. eapply rw_cells_agree; [exact APX| exact HC|]. intros a Ha. split; [left; clear - Ha H1 H2; lia| cbn [outside fst snd]; clear - Ha H1 BAC CEIL LO ESS SPAL; plia]. }
      apply AXS in FRLAy; [| clear; lia| cbn; clear - SPAH TOP; unfold USTACK_TOP in *; lia]. apply AXS in F96y; [| clear; lia| cbn; clear - SPAH TOP; unfold USTACK_TOP in *; lia].
      apply AXS in F104y; [| clear; lia| cbn; clear - SPAH TOP; unfold USTACK_TOP in *; lia]. apply AXS in F110y; [| clear; lia| cbn; clear - SPAH TOP; unfold USTACK_TOP in *; lia].
      apply AXS in F111y; [| clear; lia| cbn; clear - SPAH TOP; unfold USTACK_TOP in *; lia]. apply AXS in F112y; [| clear; lia| cbn; clear - SPAH TOP; unfold USTACK_TOP in *; lia].
      apply AXS in F120y; [| clear; lia| cbn; clear - SPAH TOP; unfold USTACK_TOP in *; lia].
      apply AXS in FRLBy; [| clear; lia| cbn [cells_size csize Nat.add]; rewrite ?Nat2Z.inj_add; clear - GSZ SPAH TOP; unfold USTACK_TOP in *; lia].
      apply AXS in FRHy; [| clear - SPAH; lia| cbn; clear - TOP; unfold USTACK_TOP in *; lia]. clear AXS.
      pose proof (DJLY (p, A, 24) bq (or_introl eq_refl) ltac:(apply in_or_app; right; exact Hbq)) as DJQ. cbn [blk_addr blk_size fst snd] in DJQ.
      pose proof (DJLY (p, A, 24) bv (or_introl eq_refl) ltac:(apply in_or_app; right; exact Hbv)) as DJV. cbn [blk_addr blk_size fst snd] in DJV.
      pose proof (DJLY (p, A, 24) bt (or_introl eq_refl) ltac:(apply in_or_app; right; exact Hbt)) as DJT. cbn [blk_addr blk_size fst snd] in DJT.
      apply (rw_cells_agree _ _ _ _ _ APX) in HOPPy; [| intros a Ha; cbn in Ha; split; [right; right; exists bq; split; [apply in_or_app; right; apply in_or_app; right; exact Hbq| clear - Ha BQ1 BQ2; lia]| cbn [outside fst snd]; clear - Ha DJQ BQ1 BQ2; lia]].
      apply (rw_cells_agree _ _ _ _ _ APX) in HPVy; [| intros a Ha; cbn in Ha; split; [right; right; exists bv; split; [apply in_or_app; right; apply in_or_app; right; exact Hbv| clear - Ha BV1 BV2; lia]| cbn [outside fst snd]; clear - Ha DJV BV1 BV2; lia]].
      apply (rw_cells_agree _ _ _ _ _ APX) in HTLCy; [| intros a Ha; cbn in Ha; split; [right; right; exists bt; split; [apply in_or_app; right; apply in_or_app; right; exact Hbt| clear - Ha BT1 BT2; lia]| cbn [outside fst snd]; clear - Ha DJT BT1 BT2; lia]].
      apply (rw_cells_agree _ _ _ _ _ APX) in HFCy; [| intros a Ha; cbn in Ha; split; [right; right; exists (qfc, f + 64, 1); split; [apply in_or_app; right; apply in_or_app; left; left; reflexivity| cbn; clear - Ha; lia]| cbn [outside fst snd]; clear - Ha OA; lia]].
      apply (rw_cells_agree _ _ _ _ _ APX) in HBUFy; [| intros a Ha; cbn in Ha; split; [right; right; exists (qb, f + 80, 32); split; [apply in_or_app; right; apply in_or_app; left; right; left; reflexivity| cbn; clear - Ha; lia]| cbn [outside fst snd]; clear - Ha OA; lia]].
      (* [comment removed for export] *)
      destruct (@AH_release (push AR f 2) _ _ _ _ _ HEAPd) as [HEAPd1 OK1].
      assert (LId : linv qfc qb mr ΣY stX md OWX' boX' [(p, A, 24)] (CX - 0)).
      { kitp (@oinv_heap (push AR f 2)) qfc qb mr OH.
        eapply OH with (L1 := OWX' ++ pbs qfc qb ++ LB);
          [exact LIY
          | replace (bv_unsigned sp + (spa - bv_unsigned sp)) with spa by (clear; lia); eapply agree_on_mono; [exact APX|]; intros a [Ha _]; split;
            [ eapply acl_sub; [| | exact Ha]; [intros b Hb; apply in_app_iff in Hb as [Hb|Hb]; apply in_or_app; [left; right; exact Hb| right; exact Hb]| clear; lia]
            | cbn [outside fst snd]; split; [| exact I]; destruct Ha as [Hs|[Hs|(b & Hb & Hr)]];
              [ clear - Hs BAC CEIL LO ESS SPAL; plia
              | intros Hr; exact (blk_not_static _ _ _ _ (p, A, 24) a HEAPO ltac:(apply in_or_app; left; left; reflexivity) Hr Hs)
              | apply in_app_iff in Hb as [Hb|Hb]; [pose proof (DJOY (p, A, 24) b (or_introl eq_refl) Hb) as X| pose proof (DJLY (p, A, 24) b (or_introl eq_refl) Hb) as X];
                cbn [blk_addr blk_size fst snd] in X; clear - Hr X; lia ] ]
          | intros b [Hb|Hb]; apply in_or_app; [left; exact Hb| right; exact Hb]
          | cbn [app]; exact HEAPd1| constructor; [exact OK1| constructor]| exact MId
          | replace (bv_unsigned sp + (spa - bv_unsigned sp)) with spa by (clear; lia); exact STd| clear; lia| clear - CRY; lia]. }
      rewrite Z.sub_0_r in LId.
      (* [comment removed for export] *)
      pose proof (munch_refl ([] : list (Z * Z)) md) as MU. pose proof (wmono_refl ctasegs md) as WM.
      apply implAp_from_evt. step. if_true. apply evt_done. fold EX_OK_TAIL. clear MU WM.
      set (adr1 := fun q : bptr => if bptr_eqb q p then A else adr q).
      assert (E1p : adr1 p = A) by (subst adr1; cbn beta; rewrite bptr_eqb_refl; reflexivity).
      assert (ADR1 : forall b, In b LB -> adr1 (blk_id b) = adr (blk_id b)).
      { intros b Hb. subst adr1. cbn beta. rewrite (bptr_eqb_neq (blk_id b) p); [reflexivity|]. intros X. apply NIpl. rewrite <- X, map_app. apply in_or_app. right. apply in_map. exact Hb. }
      set (os := CtModel.mkOct p None plen (CtWire.slice d (go_p gr) plen)).
      assert (EB : oct_blocks adr1 os = [(p, A, ASN1_STRING_SIZE)]) by (subst os; unfold oct_blocks; cbn [CtModel.os_blk CtModel.os_data app]; rewrite E1p; reflexivity).
      assert (REP : octet_repA md (OWX' ++ oct_blocks adr1 os ++ LB) adr1 os).
      { rewrite EB. subst os. unfold octet_repA. cbn [CtModel.os_blk CtModel.os_data CtModel.os_len CtModel.os_bytes optr app]. rewrite E1p.
        split; [apply in_or_app; right; left; reflexivity|]. split; [exact BA16|]. split; [rewrite PZ; exact CELLd|].
        split; [rewrite PZ; unfold CtWire.slice, zlength; reflexivity|]. split; [apply slice_range; exact DF|]. split; [exact PL31|]. unfold CtWire.slice. rewrite PZ. reflexivity. }
      eapply (exo_oktail STK CST FRMb ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m Σ st OW LB E bo lo K adr D d OPP PV TLC j31 f spa g junk gj Σ1
                PRE0 KOW CELLS LEN1 FRESH GEO CR1 SPA32 SPAL SPAH GSZ SAVJ STKB qfc qb mr) with (adr' := adr1) (bufc := [CB 32 (repeat (Z_to_bv 8 0) 32)]);
        [exact AGFr| rewrite EB; exact LId| clear - CRY; lia| exact ADR1| exact REP| reflexivity
        | exact FRLAy| exact F96y| exact F104y| exact F110y| exact F111y| exact F112y| exact F120y| exact FRLBy| exact FRHy| exact HFCy| exact HBUFy| exact HOPPy
        | cbn [CtModel.os_blk]; rewrite E1p; exact HPVy| exact HTLCy].
    + (* [comment removed for export] *)
      assert (PPOS : 0 < plen) by (clear - PNZ PLB; lia).
      unfold abind, amalloc_crypto. rewrite (proj2 (Z.eqb_neq _ _) PNZ). cbn [apbind fst snd].
      eapply (@ASN1_STRING_set1_data_walkA (push AR f 2) UK BE) with (lo := lo) (pblk := p) (bsrc := bd) (A := A) (P := D + go_p gr) (n := plen) (src := to_bytes (CtWire.slice d (go_p gr) plen));
        rewrite ?ESPA;
        [exact HEAPO| exact STY| exact CEIL| clear - LOY STKB ESK; lia| exact TOPY| exact ALY| exact MIY| reflexivity| exact CSY| exact RSY
        | left; reflexivity| exact HSTR| unfold ApPrim.V_ASN1_OCTET_STRING, CtSizes.V_ASN1_OCTET_STRING; clear; lia| unfold ApPrim.V_ASN1_OCTET_STRING, CtSizes.V_ASN1_OCTET_STRING; clear; lia
        | apply in_or_app; right; apply in_or_app; right; exact Hbd| exact NBD| clear - BD1 GB1; lia| unfold len in *; clear - BD2 PLB; lia| exact SRC| exact SLEN
        | reflexivity| reflexivity| reflexivity| clear - PPOS PL31; lia| cbn [ar_RT push amb]; clear - CRY MCB; lia
        | exact UWY| rewrite unsigned_lit by (clear; lia); exact (uk_ctx_call _ _ _ _ E_ex_set1 CTX)|].
      intros p2 Σd msd NIp2 POd.
      destruct POd as (w0 & w1 & w2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & w3 & w4 & w5 & w6 & Fd & fcd & md & C & -> & MId & STd & APX & CRd & BRC & HEAPd & ACCC & (DSTd & CELLd & HBd)).
      rewrite ESPA in STd, APX. rewrite (ret_pc_even 0x242540) by (clear; lia). cbn [apbind fst snd]. unfold aret. cbn [option_map].
      unfold ASN1_STRING_SIZE in APX, HEAPd. cbn [ar_RT push amb] in CRd.
      pose proof BRC as (BC0 & BC16 & _ & BCC & BCS).
      assert (NPP : p <> p2) by (intros X; apply NIp2; rewrite map_app; apply in_or_app; left; cbn [map blk_id fst snd]; left; exact X).
      pose proof (@AH_disjoint_gen (push AR f 2) _ _ _ _ (p2, C, plen) (p, A, 24) HEAPd (or_introl eq_refl) (or_intror (or_introl eq_refl)) ltac:(cbn; clear - NPP; congruence)) as DJ2.
      cbn [blk_addr blk_size fst snd] in DJ2.
      (* [comment removed for export] *)
      assert (AXS : forall A0 cs, rw_cells ctasegs mY A0 cs -> spa <= A0 -> A0 + Z.of_nat (cells_size cs) <= USTACK_TOP -> rw_cells ctasegs md A0 cs).
      { intros A0 cs HC H1 H2. eapply rw_cells_agree; [exact APX| exact HC|]. intros a Ha. split; [left; clear - Ha H1 H2; lia| clear - Ha H1 BAC CEIL LO ESS SPAL; plia]. }
      apply AXS in FRLAy; [| clear; lia| cbn; clear - SPAH TOP; unfold USTACK_TOP in *; lia]. apply AXS in F96y; [| clear; lia| cbn; clear - SPAH TOP; unfold USTACK_TOP in *; lia].
      apply AXS in F104y; [| clear; lia| cbn; clear - SPAH TOP; unfold USTACK_TOP in *; lia]. apply AXS in F110y; [| clear; lia| cbn; clear - SPAH TOP; unfold USTACK_TOP in *; lia].
      apply AXS in F111y; [| clear; lia| cbn; clear - SPAH TOP; unfold USTACK_TOP in *; lia]. apply AXS in F112y; [| clear; lia| cbn; clear - SPAH TOP; unfold USTACK_TOP in *; lia].
      apply AXS in F120y; [| clear; lia| cbn; clear - SPAH TOP; unfold USTACK_TOP in *; lia].
      apply AXS in FRLBy; [| clear; lia| cbn [cells_size csize Nat.add]; rewrite ?Nat2Z.inj_add; clear - GSZ SPAH TOP; unfold USTACK_TOP in *; lia].
      apply AXS in FRHy; [| clear - SPAH; lia| cbn; clear - TOP; unfold USTACK_TOP in *; lia]. clear AXS.
      pose proof (DJLY (p, A, 24) bq (or_introl eq_refl) ltac:(apply in_or_app; right; exact Hbq)) as DJQ. cbn [blk_addr blk_size fst snd] in DJQ.
      pose proof (DJLY (p, A, 24) bv (or_introl eq_refl) ltac:(apply in_or_app; right; exact Hbv)) as DJV. cbn [blk_addr blk_size fst snd] in DJV.
      pose proof (DJLY (p, A, 24) bt (or_introl eq_refl) ltac:(apply in_or_app; right; exact Hbt)) as DJT. cbn [blk_addr blk_size fst snd] in DJT.
      apply (rw_cells_agree _ _ _ _ _ APX) in HOPPy; [| intros a Ha; cbn in Ha; split; [right; right; exists bq; split; [apply in_or_app; right; apply in_or_app; right; exact Hbq| clear - Ha BQ1 BQ2; lia]| clear - Ha DJQ BQ1 BQ2; lia]].
      apply (rw_cells_agree _ _ _ _ _ APX) in HPVy; [| intros a Ha; cbn in Ha; split; [right; right; exists bv; split; [apply in_or_app; right; apply in_or_app; right; exact Hbv| clear - Ha BV1 BV2; lia]| clear - Ha DJV BV1 BV2; lia]].
      apply (rw_cells_agree _ _ _ _ _ APX) in HTLCy; [| intros a Ha; cbn in Ha; split; [right; right; exists bt; split; [apply in_or_app; right; apply in_or_app; right; exact Hbt| clear - Ha BT1 BT2; lia]| clear - Ha DJT BT1 BT2; lia]].
      apply (rw_cells_agree _ _ _ _ _ APX) in HFCy; [| intros a Ha; cbn in Ha; split; [right; right; exists (qfc, f + 64, 1); split; [apply in_or_app; right; apply in_or_app; left; left; reflexivity| cbn; clear - Ha; lia]| clear - Ha OA; lia]].
      apply (rw_cells_agree _ _ _ _ _ APX) in HBUFy; [| intros a Ha; cbn in Ha; split; [right; right; exists (qb, f + 80, 32); split; [apply in_or_app; right; apply in_or_app; left; right; left; reflexivity| cbn; clear - Ha; lia]| clear - Ha OA; lia]].
      (* [comment removed for export] *)
      destruct (@AH_release (push AR f 2) _ _ _ _ _ HEAPd) as [HEAPd1 OK2]. destruct (@AH_release (push AR f 2) _ _ _ _ _ HEAPd1) as [HEAPd2 OK1]. clear HEAPd1.
      assert (LId : linv qfc qb mr Σd stX md OWX' boX' [(p, A, 24); (p2, C, plen)] (CX - mcost plen)).
      { kitp (@oinv_heap (push AR f 2)) qfc qb mr OH.
        eapply OH with (L1 := OWX' ++ pbs qfc qb ++ LB);
          [exact LIY
          | replace (bv_unsigned sp + (spa - bv_unsigned sp)) with spa by (clear; lia); eapply agree_on_mono; [exact APX|]; intros a [Ha _]; split;
            [ eapply acl_sub; [| | exact Ha]; [intros b Hb; apply in_app_iff in Hb as [Hb|Hb]; apply in_or_app; [left; right; exact Hb| right; exact Hb]| clear; lia]
            | destruct Ha as [Hs|[Hs|(b & Hb & Hr)]];
              [ clear - Hs BAC CEIL LO ESS SPAL; plia
              | intros Hr; exact (blk_not_static _ _ _ _ (p, A, 24) a HEAPO ltac:(apply in_or_app; left; left; reflexivity) Hr Hs)
              | apply in_app_iff in Hb as [Hb|Hb]; [pose proof (DJOY (p, A, 24) b (or_introl eq_refl) Hb) as X| pose proof (DJLY (p, A, 24) b (or_introl eq_refl) Hb) as X];
                cbn [blk_addr blk_size fst snd] in X; clear - Hr X; lia ] ]
          | intros b [Hb|Hb]; apply in_or_app; [left; exact Hb| right; exact Hb]
          | cbn [app]; exact HEAPd2| constructor; [exact OK1| constructor; [exact OK2| constructor]]| exact MId
          | replace (bv_unsigned sp + (spa - bv_unsigned sp)) with spa by (clear; lia); exact STd| exact CRd| clear - MC0 MCB; lia]. }
      (* [comment removed for export] *)
      pose proof (munch_refl ([] : list (Z * Z)) md) as MU. pose proof (wmono_refl ctasegs md) as WM.
      apply implAp_from_evt. step. if_true. apply evt_done. fold EX_OK_TAIL. clear MU WM.
      assert (NIp2l : ~ In p2 (map blk_id LB)) by (intros X; apply NIp2; rewrite !map_app; apply in_or_app; right; apply in_or_app; right; exact X).
      set (adr2 := fun q : bptr => if bptr_eqb q p then A else if bptr_eqb q p2 then C else adr q).
      assert (E2p : adr2 p = A) by (subst adr2; cbn beta; rewrite bptr_eqb_refl; reflexivity).
      assert (E2p2 : adr2 p2 = C) by (subst adr2; cbn beta; rewrite (bptr_eqb_neq p2 p) by (intros X; exact (NPP (eq_sym X))); rewrite bptr_eqb_refl; reflexivity).
      assert (ADR2 : forall b, In b LB -> adr2 (blk_id b) = adr (blk_id b)).
      { intros b Hb. subst adr2. cbn beta. rewrite (bptr_eqb_neq (blk_id b) p); [rewrite (bptr_eqb_neq (blk_id b) p2); [reflexivity|]|].
        - intros X. apply NIp2l. rewrite <- X. apply in_map. exact Hb.
        - intros X. apply NIpl. rewrite <- X, map_app. apply in_or_app. right. apply in_map. exact Hb. }
      set (os := CtModel.mkOct p (Some (p2, plen)) plen (CtWire.slice d (go_p gr) plen)).
      assert (EB : oct_blocks adr2 os = [(p, A, ASN1_STRING_SIZE); (p2, C, plen)]) by (subst os; unfold oct_blocks; cbn [CtModel.os_blk CtModel.os_data app]; rewrite E2p, E2p2; reflexivity).
      assert (REP : octet_repA md (OWX' ++ oct_blocks adr2 os ++ LB) adr2 os).
      { rewrite EB. subst os. unfold octet_repA. cbn [CtModel.os_blk CtModel.os_data CtModel.os_len CtModel.os_bytes optr app]. rewrite E2p, E2p2.
        split; [apply in_or_app; right; left; reflexivity|]. split; [exact BA16|]. split; [exact CELLd|].
        split; [symmetry; apply zlength_slice; unfold len in *; clear - GB1 PLB; lia|]. split; [apply slice_range; exact DF|]. split; [exact PL31|].
        split; [intros X; exact (NPP (eq_sym X))|]. split; [apply in_or_app; right; right; left; reflexivity|]. split; [clear; lia|].
        pose proof (rw_cells_bytes_at _ _ _ _ DSTd) as BY. cbn [cells_bytes cbytes app] in BY. rewrite app_nil_r in BY. exact BY. }
      eapply (exo_oktail STK CST FRMb ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m Σ st OW LB E bo lo K adr D d OPP PV TLC j31 f spa g junk gj Σ1
                PRE0 KOW CELLS LEN1 FRESH GEO CR1 SPA32 SPAL SPAH GSZ SAVJ STKB qfc qb mr) with (adr' := adr2) (bufc := [CB 32 (repeat (Z_to_bv 8 0) 32)]);
        [exact AGFr| rewrite EB; exact LId| clear - MC0 MCB; lia| exact ADR2| exact REP| reflexivity
        | exact FRLAy| exact F96y| exact F104y| exact F110y| exact F111y| exact F112y| exact F120y| exact FRLBy| exact FRHy| exact HFCy| exact HBUFy| exact HOPPy
        | cbn [CtModel.os_blk]; rewrite E2p; exact HPVy| exact HTLCy].
  Qed.
End Body.
End WithRT.
