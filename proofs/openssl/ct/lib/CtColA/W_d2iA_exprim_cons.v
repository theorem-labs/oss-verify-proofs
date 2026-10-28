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
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtColA Require Import ColBudgetA ColDefsA CtlStmtA W_bufmemA W_collectA W_collectMA W_d2iA_stmt W_d2iA_exprim_ctx W_d2iA_exprim_tail W_d2iA_exprim_call W_d2iA_exprim_seg W_set0A.
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
Definition EX_COLL_RA : Z := 0x242120.      (* [comment removed for export] *)
Definition EX_GROW_RA : Z := 0x242134.      (* [comment removed for export] *)
Definition EX_FAIL_X25 : Z := 0x242430.     (* [comment removed for export] *)
Definition EX_ERR_TAIL : Z := 0x242260.     (* [comment removed for export] *)
Definition EX_SET0_RA : Z := 0x242528.      (* [comment removed for export] *)
Local Notation E_ex_coll := (E_asn1_d2i_ex_primitive_244b08 : uk_call 0x24187c 0x242120 0x243768).    (* [comment removed for export] *)
Local Notation E_ex_grow := (E_asn1_d2i_ex_primitive_244b24 : uk_call 0x24187c 0x242134 0x24b32c).    (* [comment removed for export] *)
Local Notation E_ex_free := (E_asn1_d2i_ex_primitive_244cdc : uk_call 0x24187c 0x24227c 0x1fd334).    (* [comment removed for export] *)
Local Notation E_ex_set0 := (E_asn1_d2i_ex_primitive_244f9c : uk_call 0x24187c 0x242528 0x224888).    (* [comment removed for export] *)

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
  Local Notation exo_keepK := (exo_keep STK CST FRMb sp m Σ st OW LB E bo lo D d OPP PV TLC j31 f spa PRE0 CELLS LEN1 FRESH GEO SPAL SPAH STKB).
  Local Notation exo_keep_uwK := (exo_keep_uw STK CST FRMb ra sp m Σ st OW LB E bo lo D d OPP PV TLC j31 f spa PRE0 ras CELLS LEN1 FRESH GEO SPAL SPAH STKB).
  (* [comment removed for export] *)
  Let plen : Z := if Z.testbit (go_ret gr) 0 then len - go_p gr else go_len gr.
  Local Notation EXD := (exd_facts STK CST FRMb ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m OW LB E lo K D d OPP PV TLC f spa g junk gj Σ1 ras).
  Local Notation EXMS := (exd_ms sp gp TLC f spa).

  (* [comment removed for export] *)
  Lemma exo_cons : forall qfc qb mr ΣX stX mX OWX boX CX (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) FX fcX
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
  Proof.
    intros until vb. intros EC XD. ctx. pose proof PRE0 as (HEAP & _).
    pose proof CELLS as (_ & _ & _ & _ & ALO & ALV & ALT & DOV & DOT & DVT & DOD & DVD & DTD & _).
    destruct XD as (AGFr & LI & CXB & UWX & FRLA & F96 & F104 & F110 & F111 & F112 & F120 & FRLB & FRH & HFC & HBUF & HOPPX & HPVX & HTLCX & EG & ETAG & ECLS & SAVJ').
    pose proof col_consts as (KC1 & KC2 & KC3 & KC4 & KC5 & KC6 & KC7).
    kitp (@oinv_call (push AR f 2)) qfc qb mr OC. kitp (@oinv_facts (push AR f 2)) qfc qb mr OFc.
    pose proof (OC _ _ _ _ _ _ _ LI) as (HEAPX & STX & _ & LOX & TOPX & ALX & MIX & _). replace (bv_unsigned sp + (spa - bv_unsigned sp)) with spa in STX, LOX, TOPX, ALX by (clear; lia).
    (* [comment removed for export] *)
    pose proof (get_object_bounds d 0 len ltac:(eapply Forall_impl; [| exact DF]; cbv beta; intros x Hx; clear - Hx; lia) LEN1) as GB. cbv zeta in GB. fold gr in GB. rewrite EG in GB.
    destruct GB as (GB1 & GB2 & GB3).
    assert (PLB : 0 <= plen /\ go_p gr + plen <= len) by (unfold plen; destruct (Z.testbit (go_ret gr) 0); clear - GB1 GB2 GB3; lia).
    assert (PL26 : plen < 2 ^ 26) by (unfold len in *; clear - PLB GB1 D26; lia).
    assert (ECV : bv_unsigned (Z_to_bv 64 (D + go_p gr)) = D + go_p gr) by (apply unsigned_lit; unfold len in *; clear - D0 D63 GB1 PLB; lia).
    assert (EPL : bv_unsigned (Z_to_bv 64 plen) = plen) by (apply unsigned_lit; clear - PLB PL26; lia).
    (* [comment removed for export] *)
    pose proof (go_ret_cases d 0 len) as RC. cbv zeta in RC. fold gr in RC.
    pose proof (ret_bits (go_ret gr) RC) as (R1 & R32 & R129 & R128 & R11 & RTB).
    assert (IV1 : Z.land (Z.land (go_ret gr) 1) 1 = (if Z.testbit (go_ret gr) 0 then 1 else 0)).
    { rewrite R11. destruct (Z.testbit (go_ret gr) 0) eqn:TB.
      - apply (proj1 RTB). first [exact TB| reflexivity].
      - destruct R1 as [E1|E1]; [exact E1|]. exfalso. pose proof (proj2 RTB E1) as X. first [discriminate X| rewrite X in TB; discriminate TB]. }
    assert (IVR : 0 <= Z.land (go_ret gr) 1 < 2 ^ 64) by (clear - R1; lia).
    hide DOV. hide DOT. hide DVT. hide DOD. hide DVD. hide DTD. hide OD. hide OQ. hide OV. hide OT. hide BD5. hide BQ5. hide BV5. hide BT5. hide G5.
    unfold exo_lowD, exd_ms, EX_CONS_ARM, MallocRep.wz in *.
    (* [comment removed for export] *)
    pose proof (exo_KH STK CST FRMb sp m Σ st OW LB E bo lo D d OPP PV TLC j31 f spa PRE0 CELLS LEN1 FRESH GEO SPA32 SPAL SPAH STKB qfc qb) as KHX.
    assert (KH0 : @kit_hyps (push AR f 2) sp (pbs qfc qb ++ LB) lo d D XP 0 0).
    { destruct KHX as (kDF & kCEIL & kLO0 & kLO & kSTK0 & kOFS0 & kTOP & kSP16 & kOFS16 & kXPok & kXPD & kPBX & kD0).
      split; [exact kDF|]. split; [exact kCEIL|]. split; [exact kLO0|]. split; [clear - LO ESS; lia|]. split; [clear; lia|]. split; [clear; lia|].
      split; [exact kTOP|]. split; [exact kSP16|]. split; [reflexivity|]. split; [exact kXPok|]. split; [exact kXPD|]. split; [exact kPBX| exact kD0]. }
    clear KHX.
    assert (XBUF : In (f + 80, f + 80 + 32) XP) by (replace (f + 80 + 32) with (f + 112) by (clear; lia); unfold exo_XP; cbn [In]; do 4 right; left; reflexivity).
    assert (ALB : (f + 80) mod 8 = 0) by (clear - G2; Z.div_mod_to_equations; lia).
    assert (FRMG : CHECK_TLEN_FRAMES_A <= FRMb - 1) by (clear - FRMBb; lia).
    (* [comment removed for export] *)
    pose proof (munch_refl [(f + 64, f + 65)]%Z mX) as MU. pose proof (wmono_refl ctasegs mX) as WM.
    freeze FRLA. freeze F96. freeze F104. freeze F110. freeze F111. freeze F112. freeze F120. freeze FRLB. freeze FRH. freeze HBUF. freeze HOPPX. freeze HPVX. freeze HTLCX.
    apply implAp_from_evt.
    step. step. name_mem m1.
    match goal with H : munch _ mX m1 |- _ => rename H into MU1 end. match goal with H : wmono ctasegs mX m1 |- _ => rename H into WM1 end.
    match goal with H : stk ctasegs m1 lo _ |- _ => rename H into ST1 end. match goal with H : mem_inv ctasegs m1 |- _ => rename H into MI1 end. rewrite ?ESPA in ST1.
    assert (LI1 : linv qfc qb mr ΣX stX m1 OWX boX [] CX).
    { kitp (@oinv_munch (push AR f 2)) qfc qb mr OM. eapply OM; [exact LI| exact MU1| exact WM1| exact MI1| replace (bv_unsigned sp + (spa - bv_unsigned sp)) with spa by (clear; lia); exact ST1|].
      constructor; [right; left; exists (f + 64, f + 65); split; [unfold exo_XP; cbn [In]; do 3 right; left; reflexivity| cbn [fst snd]; clear; lia]| constructor]. }
    Local Ltac mv1 H MU1 tac := apply (rw_cells_agree _ _ _ _ _ (agree_on_of_munch_nw _ _ _ MU1)) in H; [| intros a Ha; cbn in Ha; cbn [outside fst snd]; tac].
    thaw FRLA. mv1 FRLA MU1 ltac:(clear - Ha G3 CEIL LO ESS SPAL; plia). thaw F96. mv1 F96 MU1 ltac:(clear - Ha G3 CEIL LO ESS SPAL; plia).
    thaw F104. mv1 F104 MU1 ltac:(clear - Ha G3 CEIL LO ESS SPAL; plia). thaw F110. mv1 F110 MU1 ltac:(clear - Ha G3 CEIL LO ESS SPAL; plia).
    thaw F111. mv1 F111 MU1 ltac:(clear - Ha G3 CEIL LO ESS SPAL; plia). thaw F112. mv1 F112 MU1 ltac:(clear - Ha G3 CEIL LO ESS SPAL; plia).
    thaw F120. mv1 F120 MU1 ltac:(clear - Ha G3 CEIL LO ESS SPAL; plia). thaw FRLB. mv1 FRLB MU1 ltac:(clear - Ha G3 CEIL LO ESS SPAL; plia).
    thaw FRH. mv1 FRH MU1 ltac:(clear - Ha G3 CEIL LO ESS SPAL SPAH; plia). thaw HBUF. mv1 HBUF MU1 ltac:(clear - Ha; lia).
    unhide OQ. unhide OV. unhide OT.
    thaw HOPPX. mv1 HOPPX MU1 ltac:(clear - Ha OQ BQ1 BQ2; lia). thaw HPVX. mv1 HPVX MU1 ltac:(clear - Ha OV BV1 BV2; lia). thaw HTLCX. mv1 HTLCX MU1 ltac:(clear - Ha OT BT1 BT2; lia).
    hide OQ. hide OV. hide OT.
    assert (UW1 : uw_chain USTACK_TOP m1 spa (bv_unsigned sp) (bv_unsigned ra :: ras)).
    { eapply uw_chain_agree16; [exact UWX|]. eapply agree_on_mono; [exact (agree_on_of_munch_nw _ _ _ MU1)|]. intros a Ha. cbv beta in Ha. cbn [outside fst snd]. clear - Ha G3 CEIL LO ESS SPAL SPAH. plia. }
    (* [comment removed for export] *)
    freeze HBUF. freeze HOPPX. freeze HPVX. freeze HTLCX. freeze HFC. freeze FRH.
    step. step. rewrite (zxb_lit (Z.land (go_ret gr) 1)) by (clear - R1; lia). step. step. step. step. step. apply evt_done.
    thaw HBUF. thaw HOPPX. thaw HPVX. thaw HTLCX. thaw HFC. thaw FRH.
    (* [comment removed for export] *)
    pose proof PRE0 as (_ & _ & _ & _ & _ & _ & _ & _ & AL16 & _).
    fold len. fold gr. fold plen.
    pose proof (@asn1_collect_walkA (push AR f 2) UK BE UR STRCPY HCTL sp mr Σ1 (pbs qfc qb ++ LB) E lo K d D XP (CST len - 1) (FRMb - 1) (f + 80)
                  KH0 D0 D63 D26 XBUF ALB FRMG (CtModel.ct_fuel d) 0%nat (EX_COLL_RA :: bv_unsigned ra :: ras) (spa - bv_unsigned sp) (STK - ADEP_FRAME)) as W.
    cbv delta [entry_okA] in W.
    replace (Z_to_bv 64 (bv_unsigned sp + (spa - bv_unsigned sp))) with (Z_to_bv 64 spa) in W by (f_equal; clear; lia).
    assert (MBB : 0 <= (zlength d + 4) / 3 * 4 /\ 3 * ((zlength d + 4) / 3 * 4) <= 4 * zlength d + 16) by (unfold len in LEN1; clear - LEN1; Z.div_mod_to_equations; lia).
    eapply implAp_abind.
    { eapply W with (b := CtModel.buf0) (A0 := 0) (NEW1 := []) (PP := spa + 96) (p := go_p gr) (len := plen) (inf := Z.testbit (go_ret gr) 0) (CX := CX); clear W;
        [ clear - LOX; lia| clear - SPAH; lia| clear - SPA32 AL16; Z.div_mod_to_equations; lia
        | rewrite KC2, KC7; change (Z.of_nat 0) with 0; pose proof STKB as X; rewrite KC1 in X; clear - X; lia
        | cbn [CtColP.ColDefs.buf_blk CtModel.bm_data CtModel.buf0 app]; exact LI1
        | unfold co_credit, MB, CO_RESERVE; cbn [CtModel.bm_max CtModel.bm_data CtModel.buf0]; rewrite KC6, KC3; unfold len in *; clear - CXB CSTB PLB GB1 MBB; lia
        | clear; lia| clear - SPAH; lia| clear - SPA32; Z.div_mod_to_equations; lia
        | unfold CtColP.ColDefs.buf_cells; cbn [CtModel.bm_len CtModel.bm_max CtModel.bm_data CtModel.buf0];
          eapply rw_cells_recast; [exact HBUF| cbn; repeat split; exact I| vm_compute; reflexivity| reflexivity]
        | unfold buf_invA; cbn [CtModel.bm_len CtModel.bm_data CtModel.bm_bytes CtModel.bm_max CtModel.buf0];
          split; [clear; lia|]; split; [reflexivity|]; split; [constructor|]; split; [unfold MB; clear - MBB; lia| split; reflexivity]
        | exact F96
        | clear - GB1; lia| exact (proj1 PLB)| unfold len in PLB; clear - PLB; lia| clear; lia| exact IVR| exact IV1
        | cbn [CtModel.bm_len CtModel.buf0]; clear - GB1; lia
        | replace (bv_unsigned sp + (spa - bv_unsigned sp)) with spa by (clear; lia); exact UW1
        | unfold EX_COLL_RA; rewrite unsigned_lit by (clear; lia); reflexivity
        | apply uk_ctxJ_enter; unfold EX_COLL_RA; exact (uk_ctx_call _ _ _ _ E_ex_coll CTX) ]. }
    clear W. intros r1 Σc msc POc. unfold coll_postA in POc.
    replace (Z_to_bv 64 (bv_unsigned sp + (spa - bv_unsigned sp))) with (Z_to_bv 64 spa) in POc by (f_equal; clear; lia).
    destruct POc as (w0 & w1 & w2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & w3 & w4 & w5 & w6 & FY & fcY & mY & OWY & boY & A' & CX' & -> & OIY & HBUFY & BIY & HPPY & AXY & CAPY & RESY).
    destruct r1 as [[b1 ro] st1]. cbn [fst snd] in OIY, HBUFY, BIY, HPPY, CAPY, RESY. cbn [fst snd]. unfold EX_COLL_RA. rewrite (ret_pc_even 0x242120) by (clear; lia).
    rewrite app_nil_r in OIY.
    (* [comment removed for export] *)
    assert (NXS : forall A n a, spa + 104 <= A \/ A + n <= spa + 96 -> spa <= A -> A <= a < A + n -> ~ rin_ivs [(f + 80, f + 80 + 32); (spa + 96, spa + 96 + 8)] a).
    { intros A n a W SA Ha HIN. cbn [rin_ivs fst snd] in HIN. clear - W SA Ha HIN G3 CEIL LO ESS SPAL. plia. }
    assert (NXF : forall a, f + 64 <= a < f + 65 -> ~ rin_ivs [(f + 80, f + 80 + 32); (spa + 96, spa + 96 + 8)] a).
    { intros a Ha HIN. cbn [rin_ivs fst snd] in HIN. clear - Ha HIN G3 CEIL LO ESS SPAL. plia. }
    unhide OQ. unhide OV. unhide OT.
    assert (NXQ : forall a, OPP <= a < OPP + 8 -> ~ rin_ivs [(f + 80, f + 80 + 32); (spa + 96, spa + 96 + 8)] a).
    { intros a Ha HIN. cbn [rin_ivs fst snd] in HIN. clear - Ha HIN OQ BQ1 BQ2 BQ4 CEIL LO ESS SPAL. plia. }
    assert (NXV : forall a, PV <= a < PV + 8 -> ~ rin_ivs [(f + 80, f + 80 + 32); (spa + 96, spa + 96 + 8)] a).
    { intros a Ha HIN. cbn [rin_ivs fst snd] in HIN. clear - Ha HIN OV BV1 BV2 BV4 CEIL LO ESS SPAL. plia. }
    assert (NXT : forall a, TLC <= a < TLC + 32 -> ~ rin_ivs [(f + 80, f + 80 + 32); (spa + 96, spa + 96 + 8)] a).
    { intros a Ha HIN. cbn [rin_ivs fst snd] in HIN. clear - Ha HIN OT BT1 BT2 BT4 CEIL LO ESS SPAL. plia. }
    hide OQ. hide OV. hide OT.
    Local Ltac kp AXY H NX WH := apply (exo_keepK _ _ [] _ _ _ _ _ AXY) in H; [| NX| WH].
    kp AXY FRLA ltac:(intros a Ha; apply (NXS spa 96 a); [right; clear; lia| clear; lia| cbn in Ha; clear - Ha; lia]) ltac:(left; cbn; clear - SPAH TOP; unfold USTACK_TOP in *; lia).
    kp AXY F104 ltac:(intros a Ha; apply (NXS (spa + 104) 6 a); [left; clear; lia| clear; lia| cbn in Ha; clear - Ha; lia]) ltac:(left; cbn; clear - SPAH TOP; unfold USTACK_TOP in *; lia).
    kp AXY F110 ltac:(intros a Ha; apply (NXS (spa + 110) 1 a); [left; clear; lia| clear; lia| cbn in Ha; clear - Ha; lia]) ltac:(left; cbn; clear - SPAH TOP; unfold USTACK_TOP in *; lia).
    kp AXY F111 ltac:(intros a Ha; apply (NXS (spa + 111) 1 a); [left; clear; lia| clear; lia| cbn in Ha; clear - Ha; lia]) ltac:(left; cbn; clear - SPAH TOP; unfold USTACK_TOP in *; lia).
    kp AXY F112 ltac:(intros a Ha; apply (NXS (spa + 112) 8 a); [left; clear; lia| clear; lia| cbn in Ha; clear - Ha; lia]) ltac:(left; cbn; clear - SPAH TOP; unfold USTACK_TOP in *; lia).
    kp AXY F120 ltac:(intros a Ha; apply (NXS (spa + 120) 8 a); [left; clear; lia| clear; lia| cbn in Ha; clear - Ha; lia]) ltac:(left; cbn; clear - SPAH TOP; unfold USTACK_TOP in *; lia).
    kp AXY FRLB ltac:(intros a Ha; cbn [cells_size csize Nat.add] in Ha; rewrite ?Nat2Z.inj_add in Ha; apply (NXS (spa + 128) (24 + Z.of_nat g) a); [left; clear; lia| clear; lia| clear - Ha; lia])
                ltac:(left; cbn [cells_size csize Nat.add]; rewrite ?Nat2Z.inj_add; clear - SPAH TOP GSZ; unfold USTACK_TOP in *; lia).
    kp AXY FRH ltac:(intros a Ha; apply (NXS (bv_unsigned sp + -16) 16 a); [left; clear - SPAH; lia| clear - SPAH; lia| cbn in Ha; clear - Ha; lia]) ltac:(left; cbn; clear - SPAH TOP; unfold USTACK_TOP in *; lia).
    kp AXY HFC ltac:(intros a Ha; apply NXF; cbn in Ha; clear - Ha; lia) ltac:(right; left; cbn; clear; lia).
    kp AXY HOPPX ltac:(intros a Ha; apply NXQ; cbn in Ha; clear - Ha; lia) ltac:(do 3 right; left; split; [reflexivity| reflexivity]).
    kp AXY HPVX ltac:(intros a Ha; apply NXV; cbn in Ha; clear - Ha; lia) ltac:(do 4 right; left; split; [reflexivity| reflexivity]).
    kp AXY HTLCX ltac:(intros a Ha; apply NXT; cbn in Ha; clear - Ha; lia) ltac:(do 5 right; split; [reflexivity| reflexivity]).
    pose proof (exo_keep_uwK _ _ [] _ _ _ AXY ltac:(intros a HIN; cbn [rin_ivs fst snd] in HIN; clear - HIN G3 CEIL LO ESS SPAL SPAH; plia) UW1) as UWY.
    clear F96 HBUF MU1 WM1 ST1 MI1 LI1 UW1.
    pose proof (OC _ _ _ _ _ _ _ OIY) as (HEAPY & STY & _ & LOY & TOPY & ALY & MIY & CSY & ASY & CRY & _).
    replace (bv_unsigned sp + (spa - bv_unsigned sp)) with spa in STY, LOY, TOPY, ALY by (clear; lia). cbn [ar_RT push amb] in CRY.
    pose proof (OFc _ _ _ _ _ _ _ OIY) as (_ & NDY & BNDY & FRSHY & DJLY & DJOY).
    pose proof OIY as (_ & _ & _ & _ & _ & _ & _ & LBOKY).
    pose proof BIY as (BL0 & BLEN & BRNG & BMB & BI4).
    cbn [CtModel.bm_max CtModel.buf0 CtModel.bm_data] in CAPY.
    assert (ESF : CRYPTO_FREE_STACK + 208 <= CHECK_TLEN_STACK_A /\ GROW_STACK_A <= CHECK_TLEN_STACK_A /\ ASN1_STRING_SET0_STACK_A + 208 <= CHECK_TLEN_STACK_A).
    { rewrite KC1, KC5. unfold CRYPTO_FREE_STACK, ASN1_STRING_SET0_STACK_A, RT_STACK. clear. lia. }
    unfold CtColP.ColDefs.buf_blk in OIY, HEAPY, LBOKY, FRSHY, DJLY, DJOY.
    destruct ro as [p'|].
    + (* [comment removed for export] *)
      destruct RESY as (BP1 & BP2 & BCX). cbn [CtModel.bm_max CtModel.buf0 CtModel.bm_data] in BCX. rewrite Z.sub_0_r in BCX.
      assert (LB26 : CtModel.bm_len b1 < 2 ^ 26) by (unfold len in *; clear - BP1 BP2 PLB GB1 D26; lia).
      pose proof (munch_refl ([] : list (Z * Z)) mY) as MU. pose proof (wmono_refl ctasegs mY) as WM.
      freeze F104. freeze F110. freeze F111. freeze F112. freeze F120. freeze FRLB. freeze FRH. freeze HOPPX. freeze HPVX. freeze HTLCX. freeze HPPY. freeze HFC.
      unfold CtColP.ColDefs.buf_cells, MallocRep.wz in HBUFY.
      (* [comment removed for export] *)
      apply implAp_from_evt. step. if_false. step. step. step. step. apply evt_done. clear MU WM.
      thaw F104. thaw F110. thaw F111. thaw F112. thaw F120. thaw FRLB. thaw FRH. thaw HOPPX. thaw HPVX. thaw HTLCX. thaw HPPY. thaw HFC.
      pose proof (@BUF_MEM_grow_clean_walkA (push AR f 2) UK BE sp mr Σ1 (pbs qfc qb ++ LB) E lo K d D XP (spa - bv_unsigned sp) (STK - ADEP_FRAME) (CST len - 1) (FRMb - 1)
                    (exo_KH STK CST FRMb sp m Σ st OW LB E bo lo D d OPP PV TLC j31 f spa PRE0 CELLS LEN1 FRESH GEO SPA32 SPAL SPAH STKB qfc qb)) as W.
      replace (Z_to_bv 64 (bv_unsigned sp + (spa - bv_unsigned sp))) with (Z_to_bv 64 spa) in W by (f_equal; clear; lia).
      assert (GCB : grow_costA b1 (CtModel.bm_len b1 + 1) <= CX' /\ 1 <= CX' - grow_costA b1 (CtModel.bm_len b1 + 1)).
      { unfold grow_costA. destruct (CtModel.bm_len b1 + 1 <=? CtModel.bm_max b1) eqn:GC.
        - unfold len in *. clear - BCX CXB CSTB BP1 BP2 PLB GB1 BMB MBB LEN1. unfold MB in BMB. lia.
        - apply Z.leb_gt in GC. unfold mcost. destruct (_ <=? 64512); unfold len in *; clear - GC BCX CXB CSTB BP1 BP2 PLB GB1 BMB MBB LEN1; unfold MB in BMB; Z.div_mod_to_equations; lia. }
      destruct GCB as [GC1 GC2].
      (* [comment removed for export] *)
      assert (AFTER : forall r2 Σg msg bytes,
        @grow_postA (push AR f 2) sp mr Σ1 (pbs qfc qb ++ LB) E lo K d D XP (spa - bv_unsigned sp) (STK - ADEP_FRAME) (CST len - 1) (FRMb - 1) (Z_to_bv 64 EX_GROW_RA) gp sp (Z_to_bv 64 spa) (Z_to_bv 64 f)
          (Z_to_bv 64 f) (Z_to_bv 64 (f + 80)) (Z_to_bv 64 SHB) (Z_to_bv 64 (shad f)) (Z_to_bv 64 ITEM_OCTET_A) (Z_to_bv 64 TLC) (Z_to_bv 64 (CtModel.bm_len b1)) (Z_to_bv 64 (f + 64))
          (Z_to_bv 64 V_ASN1_OCTET_STRING) st1 OWY boY mY [] b1 (CtModel.bm_len b1 + 1) (f + 80) bytes CX' r2 Σg msg ->      (* [comment removed for export] *)
        firstn (Z.to_nat (CtModel.bm_len b1)) bytes = to_bytes (CtModel.bm_bytes b1) ->
        @implAp (push AR f 2) _ ((blk <- amalloc SZ_ASN1_STRING ;;
                                  aret (Some (CtModel.mkOct blk (CtModel.bm_data (fst r2)) (CtModel.bm_len b1) (firstn (Z.to_nat (CtModel.bm_len b1)) (CtModel.bm_bytes (fst r2)))))) (snd r2)) Σg POST msg).
      { intros r2 Σg msg bytes POG FBY. unfold grow_postA in POG.
        replace (Z_to_bv 64 (bv_unsigned sp + (spa - bv_unsigned sp))) with (Z_to_bv 64 spa) in POG by (f_equal; clear; lia).
        destruct POG as (g0 & g1 & g2 & h1 & h2 & h3 & h4 & h5 & h6 & h7 & g3 & g4 & g5 & g6 & FG & fcG & mG & OWG & q & A & n & rest'
                         & -> & ER & EB & OIG & OWI & HBUFG & HBLKG & LEN & N4 & A0 & A16 & ACE & EN & AXG).
        rewrite ER, EB. cbn [CtModel.bm_data CtModel.bm_bytes fst snd]. unfold EX_GROW_RA. rewrite (ret_pc_even 0x242134) by (clear; lia).
        rewrite FBY in HBLKG. rewrite firstn_all2 by (unfold zlength in BLEN; rewrite BLEN, Nat2Z.id; clear; lia).
        change (@BnHeapA.ACEIL (push AR f 2)) with (@BnHeapA.ACEIL AR) in ACE.
        pose proof (OC _ _ _ _ _ _ _ OIG) as (HEAPG & STG & _ & LOG & TOPG & ALG & MIG & CSG & ASG & CRG & _).
        replace (bv_unsigned sp + (spa - bv_unsigned sp)) with spa in STG, LOG, TOPG, ALG by (clear; lia). cbn [ar_RT push amb] in CRG.
        pose proof (OFc _ _ _ _ _ _ _ OIG) as (_ & NDG & BNDG & FRSHG & DJLG & DJOG). cbn [app] in HEAPG.
        pose proof (proj2 (@AH_acc (push AR f 2) _ _ _ _ (q, A, n) HEAPG ltac:(apply in_or_app; right; left; reflexivity))) as ACCG. cbn [blk_addr blk_size fst snd] in ACCG.
        pose proof (@AH_offsh (push AR f 2) _ _ _ _ (q, A, n) HEAPG ltac:(apply in_or_app; right; left; reflexivity)) as ROA. cbn [blk_addr blk_size fst snd] in ROA. unfold SHLO, SHHI in ROA.
        assert (OFQ : A + n <= f \/ f + 256 <= A).
        { pose proof (exo_new_off _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ OIG (q, A, n) (or_introl eq_refl)) as O. unfold off_fr in O. change (fs_size 2) with 256 in O. exact O. }
        pose proof (DJLG (q, A, n) bq (or_introl eq_refl) ltac:(apply in_or_app; right; exact Hbq)) as DJQ. cbn [blk_addr blk_size fst snd] in DJQ.
        pose proof (DJLG (q, A, n) bv (or_introl eq_refl) ltac:(apply in_or_app; right; exact Hbv)) as DJV. cbn [blk_addr blk_size fst snd] in DJV.
        pose proof (DJLG (q, A, n) bt (or_introl eq_refl) ltac:(apply in_or_app; right; exact Hbt)) as DJT. cbn [blk_addr blk_size fst snd] in DJT.
        (* [comment removed for export] *)
        assert (MXS : forall A1 k a, spa <= A1 -> A1 <= a < A1 + k -> ~ rin_ivs [(f + 80, f + 80 + 32)] a).
        { intros A1 k a SA Ha HIN. cbn [rin_ivs fst snd] in HIN. clear - SA Ha HIN G3 CEIL LO ESS SPAL. plia. }
        assert (MXF : forall a, f + 64 <= a < f + 65 -> ~ rin_ivs [(f + 80, f + 80 + 32)] a) by (intros a Ha HIN; cbn [rin_ivs fst snd] in HIN; clear - Ha HIN; lia).
        unhide OQ. unhide OV. unhide OT.
        assert (MXQ : forall a, OPP <= a < OPP + 8 -> ~ rin_ivs [(f + 80, f + 80 + 32)] a) by (intros a Ha HIN; cbn [rin_ivs fst snd] in HIN; clear - Ha HIN OQ BQ1 BQ2; lia).
        assert (MXV : forall a, PV <= a < PV + 8 -> ~ rin_ivs [(f + 80, f + 80 + 32)] a) by (intros a Ha HIN; cbn [rin_ivs fst snd] in HIN; clear - Ha HIN OV BV1 BV2; lia).
        assert (MXT : forall a, TLC <= a < TLC + 32 -> ~ rin_ivs [(f + 80, f + 80 + 32)] a) by (intros a Ha HIN; cbn [rin_ivs fst snd] in HIN; clear - Ha HIN OT BT1 BT2; lia).
        hide OQ. hide OV. hide OT.
        Local Ltac kg AXG H NX WH := apply (exo_keepK _ _ [] _ _ _ _ _ AXG) in H; [| NX| WH].
        kg AXG FRLA ltac:(intros a Ha; apply (MXS spa 96 a); [clear; lia| cbn in Ha; clear - Ha; lia]) ltac:(left; cbn; clear - SPAH TOP; unfold USTACK_TOP in *; lia).
        kg AXG HPPY ltac:(intros a Ha; apply (MXS (spa + 96) 8 a); [clear; lia| cbn in Ha; clear - Ha; lia]) ltac:(left; cbn; clear - SPAH TOP; unfold USTACK_TOP in *; lia).
        kg AXG F104 ltac:(intros a Ha; apply (MXS (spa + 104) 6 a); [clear; lia| cbn in Ha; clear - Ha; lia]) ltac:(left; cbn; clear - SPAH TOP; unfold USTACK_TOP in *; lia).
        kg AXG F110 ltac:(intros a Ha; apply (MXS (spa + 110) 1 a); [clear; lia| cbn in Ha; clear - Ha; lia]) ltac:(left; cbn; clear - SPAH TOP; unfold USTACK_TOP in *; lia).
        kg AXG F111 ltac:(intros a Ha; apply (MXS (spa + 111) 1 a); [clear; lia| cbn in Ha; clear - Ha; lia]) ltac:(left; cbn; clear - SPAH TOP; unfold USTACK_TOP in *; lia).
        kg AXG F112 ltac:(intros a Ha; apply (MXS (spa + 112) 8 a); [clear; lia| cbn in Ha; clear - Ha; lia]) ltac:(left; cbn; clear - SPAH TOP; unfold USTACK_TOP in *; lia).
        kg AXG F120 ltac:(intros a Ha; apply (MXS (spa + 120) 8 a); [clear; lia| cbn in Ha; clear - Ha; lia]) ltac:(left; cbn; clear - SPAH TOP; unfold USTACK_TOP in *; lia).
        kg AXG FRLB ltac:(intros a Ha; cbn [cells_size csize Nat.add] in Ha; rewrite ?Nat2Z.inj_add in Ha; apply (MXS (spa + 128) (24 + Z.of_nat g) a); [clear; lia| clear - Ha; lia])
                    ltac:(left; cbn [cells_size csize Nat.add]; rewrite ?Nat2Z.inj_add; clear - SPAH TOP GSZ; unfold USTACK_TOP in *; lia).
        kg AXG FRH ltac:(intros a Ha; apply (MXS (bv_unsigned sp + -16) 16 a); [clear - SPAH; lia| cbn in Ha; clear - Ha; lia]) ltac:(left; cbn; clear - SPAH TOP; unfold USTACK_TOP in *; lia).
        kg AXG HFC ltac:(intros a Ha; apply MXF; cbn in Ha; clear - Ha; lia) ltac:(right; left; cbn; clear; lia).
        kg AXG HOPPX ltac:(intros a Ha; apply MXQ; cbn in Ha; clear - Ha; lia) ltac:(do 3 right; left; split; [reflexivity| reflexivity]).
        kg AXG HPVX ltac:(intros a Ha; apply MXV; cbn in Ha; clear - Ha; lia) ltac:(do 4 right; left; split; [reflexivity| reflexivity]).
        kg AXG HTLCX ltac:(intros a Ha; apply MXT; cbn in Ha; clear - Ha; lia) ltac:(do 5 right; split; [reflexivity| reflexivity]).
        pose proof (exo_keep_uwK _ _ [] _ _ _ AXG ltac:(intros a HIN; cbn [rin_ivs fst snd] in HIN; clear - HIN G3 CEIL LO ESS SPAL SPAH; plia) UWY) as UWG.
        clear HBUFY OIY HEAPY AXY.
        (* [comment removed for export] *)
        lazymatch type of HBLKG with rw_cells _ _ _ [?c0; ?c1] => change [c0; c1] with ([c0] ++ [c1]) in HBLKG end.
        apply rw_cells_app in HBLKG as [HA1 HA2]. cbn [cells_size csize Nat.add] in HA2. rewrite Nat.add_0_r, Z2Nat.id in HA2 by (clear - BL0; lia).
        replace (Z.to_nat (n - CtModel.bm_len b1)) with (1 + Z.to_nat (n - CtModel.bm_len b1 - 1))%nat in HA2 by (clear - LEN BL0; lia). apply cb_split_a in HA2.
        lazymatch type of HA2 with rw_cells _ _ _ [?c0; ?c1] => change [c0; c1] with ([c0] ++ [c1]) in HA2 end.
        apply rw_cells_app in HA2 as [HAZ HA3]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in HA3.
        destruct (cb_byte_a _ _ _ HAZ) as [bz HAZ']. clear HAZ.
        unfold MallocRep.wz in HBUFG, HPPY.
        (* [comment removed for export] *)
        pose proof (munch_refl [(spa, spa + 96); (A + CtModel.bm_len b1, A + CtModel.bm_len b1 + 1)]%Z mG) as MU. pose proof (wmono_refl ctasegs mG) as WM.
        assert (OFFW : offshW [(spa, spa + 96); (A + CtModel.bm_len b1, A + CtModel.bm_len b1 + 1)]%Z) by (cbn [offshW]; unfold SHLO, SHHI; clear - ROA LEN BL0 CL2 CEIL LO ESS SPAL; lia).
        freeze F104. freeze F110. freeze F111. freeze F112. freeze F120. freeze FRLB. freeze FRH. freeze HFC. freeze HOPPX. freeze HPVX. freeze HTLCX. freeze HPPY. freeze HA1. freeze HA3.
        (* [comment removed for export] *)
        hide RC. hide R1. hide R32. hide IV1. hide CAPY. hide BCX. hide MBB. hide BMB. hide GC1. hide GC2. hide EN. hide DJQ. hide DJV. hide DJT. hide OFQ. hide ROA. hide PLB.
        clear R129 R128 R11 RTB IVR.
        pose proof HBUFG as HBUFG0. freeze HBUFG0.
        apply implAp_from_evt.
        step. if_cases KA; zc KA; [exfalso; revert KA; rewrite ?unsigned_lit by (clear - BL0 LB26; lia); clear - BL0; lia|]. clear KA.
        (* [comment removed for export] *)
        step. step.
        (* [comment removed for export] *)
        apre. remember (A + CtModel.bm_len b1) as AZ eqn:EAZ. step. subst AZ. name_mem mb.
        match goal with H : munch _ mG mb |- _ => rename H into MUb end. match goal with H : wmono ctasegs mG mb |- _ => rename H into WMb end.
        try clear HBUFG. thaw HBUFG0. rename HBUFG0 into HBUFG.
        apply (rw_cells_agree _ _ _ _ _ (agree_on_of_munch_nw _ _ _ MUb)) in HBUFG; [| intros a Ha; cbn in Ha; cbn [outside fst snd]; unhide OFQ; clear - Ha OFQ G3 CEIL LO ESS SPAL LEN BL0; plia].
        step. step. apply evt_done.      (* [comment removed for export] *)
        (* [comment removed for export] *)
        assert (LIb : linv qfc qb mr Σg st1 mb OWG boY [(q, A, n)] (CX' - grow_costA b1 (CtModel.bm_len b1 + 1))).
        { kitp (@oinv_munch (push AR f 2)) qfc qb mr OM. eapply OM; [exact OIG| exact MUb| exact WMb| exact MIG| replace (bv_unsigned sp + (spa - bv_unsigned sp)) with spa by (clear; lia); exact STG|].
          constructor; [left; cbn [fst snd]; clear - SPAH CEIL LO ESS SPAL; lia|].
          constructor; [right; right; exists (q, A, n); split; [left; reflexivity| cbn [blk_addr blk_size fst snd]; clear - LEN BL0; lia]| constructor]. }
        Local Ltac mvb H MUb tac := apply (rw_cells_agree _ _ _ _ _ (agree_on_of_munch_nw _ _ _ MUb)) in H; [| intros a Ha; cbn in Ha; cbn [outside fst snd]; tac].
        thaw F104. mvb F104 MUb ltac:(clear - Ha ACE CEIL LO ESS SPAL LEN BL0; plia). thaw F110. mvb F110 MUb ltac:(clear - Ha ACE CEIL LO ESS SPAL LEN BL0; plia).
        thaw F111. mvb F111 MUb ltac:(clear - Ha ACE CEIL LO ESS SPAL LEN BL0; plia). thaw F112. mvb F112 MUb ltac:(clear - Ha ACE CEIL LO ESS SPAL LEN BL0; plia).
        thaw F120. mvb F120 MUb ltac:(clear - Ha ACE CEIL LO ESS SPAL LEN BL0; plia). thaw HPPY. mvb HPPY MUb ltac:(clear - Ha ACE CEIL LO ESS SPAL LEN BL0; plia).
        thaw FRLB. mvb FRLB MUb ltac:(clear - Ha ACE CEIL LO ESS SPAL LEN BL0; plia). thaw FRH. mvb FRH MUb ltac:(clear - Ha ACE CEIL LO ESS SPAL SPAH LEN BL0; plia).
        unhide OFQ. unhide DJQ. unhide DJV. unhide DJT.
        thaw HFC. mvb HFC MUb ltac:(clear - Ha OFQ G3 CEIL LO ESS SPAL LEN BL0; plia).
        thaw HOPPX. mvb HOPPX MUb ltac:(clear - Ha DJQ BQ1 BQ2 BQ4 CEIL LO ESS SPAL LEN BL0; plia).
        thaw HPVX. mvb HPVX MUb ltac:(clear - Ha DJV BV1 BV2 BV4 CEIL LO ESS SPAL LEN BL0; plia).
        thaw HTLCX. mvb HTLCX MUb ltac:(clear - Ha DJT BT1 BT2 BT4 CEIL LO ESS SPAL LEN BL0; plia).
        thaw HA1. mvb HA1 MUb ltac:(rewrite Nat.add_0_r, Z2Nat.id in Ha by (clear - BL0; lia); clear - Ha ACE CEIL LO ESS SPAL LEN BL0; plia).
        hide OFQ. hide DJQ. hide DJV. hide DJT.
        assert (UWb : uw_chain USTACK_TOP mb spa (bv_unsigned sp) (bv_unsigned ra :: ras)).
        { eapply uw_chain_agree16; [exact UWG|]. eapply agree_on_mono; [exact (agree_on_of_munch_nw _ _ _ MUb)|]. intros a Ha. cbv beta in Ha. cbn [outside fst snd]. clear - Ha SPAH ACE CEIL LO ESS SPAL LEN BL0. plia. }
        clear MUb WMb HA3 HAZ'.
        eapply (exo_c2i STK CST FRMb ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m Σ st OW LB E bo lo K adr D d OPP PV TLC j31 f spa g junk Σ1 PRE0 ras CTX CELLS LEN1 FRESH GEO SPA32 SPAL SPAH GSZ STKB qfc qb mr) with
          (CV := A) (L := CtModel.bm_len b1) (PEND := D + p') (fcv := 1) (bufc := [C8 (Z_to_bv 64 (CtModel.bm_len b1 + 1)); C8 (Z_to_bv 64 A); C8 (Z_to_bv 64 n); C8 (Z_to_bv 64 0)]);
          [exact AGFr| exact LIb| exact GC2| exact UWb| clear - BL0 LB26; lia| pose proof ACE as ACE'; unfold BnHeapA.ACEIL in ACE', CL3; clear - A0 ACE' CL3 LEN BL0; lia| clear; lia| reflexivity
          | exact FRLA| exact HPPY| exact F104| exact F110| exact F111| exact F112| exact F120| exact FRLB| exact FRH| exact HFC| exact HBUFG| exact HOPPX| exact HPVX| exact HTLCX|].
        (* [comment removed for export] *)
        clear HBUFG HFC FRLA F104 F110 F111 F112 F120 FRLB FRH HOPPX HPVX HTLCX HPPY UWb UWG.
        intros pS ΣS msS PC.
        destruct PC as (y1 & y5 & y6 & y7 & y10 & y12 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & FS & fcS & mS & As & OWS & boS & -> & EFC & LIS & NIp & AR24 & AS16
                        & HSTR & UWS & FRLA & F96 & F104 & F110 & F111 & F112 & F120 & FRLB & FRH & HCONT & HFC & HBUF & HOPPX & HPVX & HTLCX & KEEPN).
        unfold aret. clear HCONT UWS.
        pose proof (KEEPN (q, A, n) _ (or_introl eq_refl) HA1 ltac:(cbn [cells_size csize Nat.add blk_addr blk_size fst snd]; rewrite Nat.add_0_r, Z2Nat.id by (clear - BL0; lia); clear - LEN BL0; lia)) as HAs.
        cbn [blk_addr blk_size fst snd] in HAs. clear KEEPN HA1.
        pose proof (OC _ _ _ _ _ _ _ LIS) as (HEAPS & STS & _ & LOS & TOPS & ALS & MIS & _). replace (bv_unsigned sp + (spa - bv_unsigned sp)) with spa in STS, LOS, TOPS, ALS by (clear; lia).
        pose proof (OFc _ _ _ _ _ _ _ LIS) as (_ & NDS & _ & FRSHS & DJLS & _). cbn [app] in HEAPS.
        pose proof AR24 as (SA0 & _ & _ & SAC & SAS). change (@BnHeapA.ACEIL (push AR f 2)) with (@BnHeapA.ACEIL AR) in SAC. unfold ASN1_STRING_SIZE in SAC, SAS.
        assert (OFS' : As + 24 <= f \/ f + 256 <= As).
        { pose proof (exo_new_off _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ LIS (pS, As, ASN1_STRING_SIZE) (or_introl eq_refl)) as O. unfold off_fr in O. change (fs_size 2) with 256 in O. exact O. }
        assert (NPQ : pS <> q) by (intros X; apply NIp; rewrite X, map_app; apply in_or_app; right; left; reflexivity).
        pose proof (@AH_disjoint_gen (push AR f 2) _ _ _ _ (pS, As, ASN1_STRING_SIZE) (q, A, n) HEAPS ltac:(apply in_or_app; right; left; reflexivity) ltac:(apply in_or_app; right; right; left; reflexivity) ltac:(cbn; exact NPQ)) as DJpq.
        cbn [blk_addr blk_size fst snd] in DJpq. unfold ASN1_STRING_SIZE in DJpq.
        pose proof (DJLS (pS, As, ASN1_STRING_SIZE) bq (or_introl eq_refl) ltac:(apply in_or_app; right; exact Hbq)) as SDJQ. cbn [blk_addr blk_size fst snd] in SDJQ. unfold ASN1_STRING_SIZE in SDJQ.
        pose proof (DJLS (pS, As, ASN1_STRING_SIZE) bv (or_introl eq_refl) ltac:(apply in_or_app; right; exact Hbv)) as SDJV. cbn [blk_addr blk_size fst snd] in SDJV. unfold ASN1_STRING_SIZE in SDJV.
        pose proof (DJLS (pS, As, ASN1_STRING_SIZE) bt (or_introl eq_refl) ltac:(apply in_or_app; right; exact Hbt)) as SDJT. cbn [blk_addr blk_size fst snd] in SDJT. unfold ASN1_STRING_SIZE in SDJT.
        hide OFS'. hide DJpq. hide SDJQ. hide SDJV. hide SDJT.
        assert (Ey10 : y10 = Z_to_bv 64 1) by (apply bv_eq; rewrite EFC, unsigned_lit by (clear; lia); reflexivity). subst y10.
        (* [comment removed for export] *)
        pose proof (munch_refl ([] : list (Z * Z)) mS) as MU. pose proof (wmono_refl ctasegs mS) as WM.
        freeze HSTR. freeze FRLA. freeze F96. freeze F104. freeze F110. freeze F111. freeze F112. freeze F120. freeze FRLB. freeze FRH. freeze HFC. freeze HBUF. freeze HOPPX. freeze HPVX. freeze HTLCX. freeze HAs.
        apply implAp_from_evt. unfold EX_FC_TEST. step. if_false. step. step. step.      (* [comment removed for export] *)
        thaw HSTR.
        eapply evt_cut.
        { eapply (@ASN1_STRING_set0_walkA (push AR f 2)) with (lo := lo) (q := pS) (A := As) (D := A) (ty := 4) (len := CtModel.bm_len b1); rewrite ?ESPA;
            [exact HEAPS| exact STS| exact MIS| exact CEIL| clear - LOS STKB ESF; lia| apply in_or_app; right; left; reflexivity| exact AS16
            | pose proof ACE as ACE'; unfold BnHeapA.ACEIL in ACE', CL3; clear - A0 ACE' CL3 LEN BL0; lia| clear - BL0 LB26; lia
            | clear; lia| exact HSTR| reflexivity| reflexivity| reflexivity]. }
        cbv beta. intros ms5 (u0 & u1 & u2 & u3 & u4 & u5 & u6 & u7 & u8 & u9 & u10 & u11 & u12 & u13 & u14 & m5 & -> & MU5 & WM5 & MI5 & ST5 & CELL5). rewrite ?ESPA in ST5, MU5.
        rewrite (ret_pc_even 0x242528) by (clear; lia). unfold ASN1_STRING_SET0_STACK_A, ASN1_STRING_SIZE in MU5.
        assert (LI5 : linv qfc qb mr ΣS st1 m5 OWS boS [(pS, As, ASN1_STRING_SIZE); (q, A, n)] (CX' - grow_costA b1 (CtModel.bm_len b1 + 1))).
        { kitp (@oinv_munch (push AR f 2)) qfc qb mr OM. eapply OM; [exact LIS| exact MU5| exact WM5| exact MI5| replace (bv_unsigned sp + (spa - bv_unsigned sp)) with spa by (clear; lia); exact ST5|].
          constructor; [left; cbn [fst snd]; clear - SPAH CEIL LO ESS SPAL; lia|].
          constructor; [right; right; exists (pS, As, ASN1_STRING_SIZE); split; [left; reflexivity| cbn [blk_addr blk_size fst snd]; unfold ASN1_STRING_SIZE; clear; lia]| constructor]. }
        Local Ltac mv5 H MU5 tac := apply (rw_cells_agree _ _ _ _ _ (agree_on_of_munch_nw _ _ _ MU5)) in H; [| intros a Ha; cbn in Ha; cbn [outside fst snd]; tac].
        unhide OFS'. unhide DJpq. unhide SDJQ. unhide SDJV. unhide SDJT.
        thaw FRLA. mv5 FRLA MU5 ltac:(clear - Ha SAC CEIL LO ESS SPAL; plia). thaw F96. mv5 F96 MU5 ltac:(clear - Ha SAC CEIL LO ESS SPAL; plia).
        thaw F104. mv5 F104 MU5 ltac:(clear - Ha SAC CEIL LO ESS SPAL; plia). thaw F110. mv5 F110 MU5 ltac:(clear - Ha SAC CEIL LO ESS SPAL; plia).
        thaw F111. mv5 F111 MU5 ltac:(clear - Ha SAC CEIL LO ESS SPAL; plia). thaw F112. mv5 F112 MU5 ltac:(clear - Ha SAC CEIL LO ESS SPAL; plia).
        thaw F120. mv5 F120 MU5 ltac:(clear - Ha SAC CEIL LO ESS SPAL; plia). thaw FRLB. mv5 FRLB MU5 ltac:(clear - Ha SAC CEIL LO ESS SPAL; plia).
        thaw FRH. mv5 FRH MU5 ltac:(clear - Ha SAC CEIL LO ESS SPAL SPAH; plia).
        thaw HFC. mv5 HFC MU5 ltac:(clear - Ha OFS' G3 CEIL LO ESS SPAL; plia). thaw HBUF. mv5 HBUF MU5 ltac:(clear - Ha OFS' G3 CEIL LO ESS SPAL; plia).
        thaw HOPPX. mv5 HOPPX MU5 ltac:(clear - Ha SDJQ BQ1 BQ2 BQ4 CEIL LO ESS SPAL; plia). thaw HPVX. mv5 HPVX MU5 ltac:(clear - Ha SDJV BV1 BV2 BV4 CEIL LO ESS SPAL; plia).
        thaw HTLCX. mv5 HTLCX MU5 ltac:(clear - Ha SDJT BT1 BT2 BT4 CEIL LO ESS SPAL; plia).
        thaw HAs. mv5 HAs MU5 ltac:(rewrite Nat.add_0_r, Z2Nat.id in Ha by (clear - BL0; lia); clear - Ha DJpq ACE CEIL LO ESS SPAL LEN BL0; plia).
        hide DJpq. hide SDJQ. hide SDJV. hide SDJT.
        (* [comment removed for export] *)
        clear MU WM MU5 WM5 MIS STS. pose proof (munch_refl [(f + 64, f + 65)]%Z m5) as MU. pose proof (wmono_refl ctasegs m5) as WM.
        freeze FRLA. freeze F96. freeze F104. freeze F110. freeze F111. freeze F112. freeze F120. freeze FRLB. freeze FRH. freeze HBUF. freeze HOPPX. freeze HPVX. freeze HTLCX. freeze HAs. freeze CELL5.
        step. name_mem m6.
        match goal with H : munch _ m5 m6 |- _ => rename H into MU6 end. match goal with H : wmono ctasegs m5 m6 |- _ => rename H into WM6 end.
        match goal with H : stk ctasegs m6 lo _ |- _ => rename H into ST6 end. match goal with H : mem_inv ctasegs m6 |- _ => rename H into MI6 end. rewrite ?ESPA in ST6.
        assert (LI6 : linv qfc qb mr ΣS st1 m6 OWS boS [(pS, As, ASN1_STRING_SIZE); (q, A, n)] (CX' - grow_costA b1 (CtModel.bm_len b1 + 1))).
        { kitp (@oinv_munch (push AR f 2)) qfc qb mr OM. eapply OM; [exact LI5| exact MU6| exact WM6| exact MI6| replace (bv_unsigned sp + (spa - bv_unsigned sp)) with spa by (clear; lia); exact ST6|].
          constructor; [right; left; exists (f + 64, f + 65); split; [unfold exo_XP; cbn [In]; do 3 right; left; reflexivity| cbn [fst snd]; clear; lia]| constructor]. }
        Local Ltac mv6 H MU6 tac := apply (rw_cells_agree _ _ _ _ _ (agree_on_of_munch_nw _ _ _ MU6)) in H; [| intros a Ha; cbn in Ha; cbn [outside fst snd]; tac].
        thaw FRLA. mv6 FRLA MU6 ltac:(clear - Ha G3 CEIL LO ESS SPAL; plia). thaw F96. mv6 F96 MU6 ltac:(clear - Ha G3 CEIL LO ESS SPAL; plia).
        thaw F104. mv6 F104 MU6 ltac:(clear - Ha G3 CEIL LO ESS SPAL; plia). thaw F110. mv6 F110 MU6 ltac:(clear - Ha G3 CEIL LO ESS SPAL; plia).
        thaw F111. mv6 F111 MU6 ltac:(clear - Ha G3 CEIL LO ESS SPAL; plia). thaw F112. mv6 F112 MU6 ltac:(clear - Ha G3 CEIL LO ESS SPAL; plia).
        thaw F120. mv6 F120 MU6 ltac:(clear - Ha G3 CEIL LO ESS SPAL; plia). thaw FRLB. mv6 FRLB MU6 ltac:(clear - Ha G3 CEIL LO ESS SPAL; plia).
        thaw FRH. mv6 FRH MU6 ltac:(clear - Ha G3 CEIL LO ESS SPAL SPAH; plia). thaw HBUF. mv6 HBUF MU6 ltac:(clear - Ha; lia).
        unhide OQ. unhide OV. unhide OT. unhide OFQ.
        thaw HOPPX. mv6 HOPPX MU6 ltac:(clear - Ha OQ BQ1 BQ2; lia). thaw HPVX. mv6 HPVX MU6 ltac:(clear - Ha OV BV1 BV2; lia). thaw HTLCX. mv6 HTLCX MU6 ltac:(clear - Ha OT BT1 BT2; lia).
        thaw HAs. mv6 HAs MU6 ltac:(rewrite Nat.add_0_r, Z2Nat.id in Ha by (clear - BL0; lia); clear - Ha OFQ LEN BL0; lia).
        thaw CELL5. mv6 CELL5 MU6 ltac:(unfold asn1_string_cells in Ha; cbn in Ha; clear - Ha OFS'; lia).
        step. apply evt_done. fold EX_OK_TAIL.
        (* [comment removed for export] *)
        set (adr3 := fun x : bptr => if bptr_eqb x pS then As else if bptr_eqb x q then A else adr x).
        assert (E3p : adr3 pS = As) by (subst adr3; cbn beta; rewrite bptr_eqb_refl; reflexivity).
        assert (E3q : adr3 q = A) by (subst adr3; cbn beta; rewrite (bptr_eqb_neq q pS) by (intros X; exact (NPQ (eq_sym X))); rewrite bptr_eqb_refl; reflexivity).
        assert (NIpl : ~ In pS (map blk_id LB)) by (intros X; apply NIp; rewrite !map_app; apply in_or_app; right; apply in_or_app; right; apply in_or_app; right; exact X).
        assert (NIql : ~ In q (map blk_id LB)) by (intros X; apply (FRSHS (q, A, n) (or_intror (or_introl eq_refl))); rewrite !map_app; apply in_or_app; right; apply in_or_app; right; exact X).
        assert (ADR3 : forall b, In b LB -> adr3 (blk_id b) = adr (blk_id b)).
        { intros b Hb. subst adr3. cbn beta. rewrite (bptr_eqb_neq (blk_id b) pS); [rewrite (bptr_eqb_neq (blk_id b) q); [reflexivity|]|].
          - intros X. apply NIql. rewrite <- X. apply in_map. exact Hb.
          - intros X. apply NIpl. rewrite <- X. apply in_map. exact Hb. }
        set (os := CtModel.mkOct pS (Some (q, n)) (CtModel.bm_len b1) (CtModel.bm_bytes b1)).
        assert (EB3 : oct_blocks adr3 os = [(pS, As, ASN1_STRING_SIZE); (q, A, n)]) by (subst os; unfold oct_blocks; cbn [CtModel.os_blk CtModel.os_data app]; rewrite E3p, E3q; reflexivity).
        assert (REP : octet_repA m6 (OWS ++ oct_blocks adr3 os ++ LB) adr3 os).
        { rewrite EB3. subst os. unfold octet_repA. cbn [CtModel.os_blk CtModel.os_data CtModel.os_len CtModel.os_bytes optr app]. rewrite E3p, E3q.
          split; [apply in_or_app; right; left; reflexivity|]. split; [exact AS16|]. split; [exact CELL5|].
          split; [exact BLEN|]. split; [exact BRNG|]. split; [clear - BL0 LB26; lia|].
          split; [intros X; exact (NPQ (eq_sym X))|]. split; [apply in_or_app; right; right; left; reflexivity|]. split; [clear - LEN; lia|].
          pose proof (rw_cells_bytes_at _ _ _ _ HAs) as BY. cbn [cells_bytes cbytes app] in BY. rewrite app_nil_r in BY. exact BY. }
        unhide GC2.
        eapply (exo_oktail STK CST FRMb ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m Σ st OW LB E bo lo K adr D d OPP PV TLC j31 f spa g junk gj Σ1
                  PRE0 KOW CELLS LEN1 FRESH GEO CR1 SPA32 SPAL SPAH GSZ SAVJ STKB qfc qb mr) with (adr' := adr3) (bufc := [C8 (Z_to_bv 64 (CtModel.bm_len b1 + 1)); C8 (Z_to_bv 64 A); C8 (Z_to_bv 64 n); C8 (Z_to_bv 64 0)]);
          [exact AGFr| rewrite EB3; exact LI6| clear - GC2; lia| exact ADR3| exact REP| reflexivity
          | exact FRLA| exact F96| exact F104| exact F110| exact F111| exact F112| exact F120| exact FRLB| exact FRH| exact HFC| exact HBUF| exact HOPPX
          | cbn [CtModel.os_blk]; rewrite E3p; exact HPVX| exact HTLCX]. }
      destruct (CtModel.bm_data b1) as [[q0 n0]|] eqn:EBD.
      * destruct BI4 as (C1' & C2 & rest & HC). apply cb_join_a in HC.
        replace (Z.to_nat (CtModel.bm_len b1) + Z.to_nat (n0 - CtModel.bm_len b1))%nat with (Z.to_nat n0) in HC by (clear - C1' BL0; lia).
        eapply implAp_abind.
        { eapply W with (b := b1) (A0 := A') (NEW1 := []) (BUF := f + 80) (bytes := to_bytes (CtModel.bm_bytes b1) ++ rest) (CX := CX'); clear W;
            [ rewrite KC5; pose proof STKB as X; rewrite KC1 in X; clear - X; lia
            | unfold CtColP.ColDefs.buf_blk; rewrite EBD, app_nil_r; exact OIY
            | exact XBUF| exact ALB
            | unfold CtColP.ColDefs.buf_cells, MallocRep.wz; exact HBUFY
            | unfold CtModel.bm_max; rewrite EBD; clear - BL0 C1'; lia| clear; lia| clear - LB26; lia
            | rewrite EBD; split; [exact C2| exact HC]
            | exact GC1
            | replace (bv_unsigned sp + (spa - bv_unsigned sp)) with spa by (clear; lia); exact UWY
            | rewrite unsigned_lit by (clear; lia); exact (uk_ctx_call _ _ _ _ E_ex_grow CTX) ]. }
        clear W. intros r2 Σg msg POG. eapply AFTER; [exact POG|].
        rewrite firstn_app. replace (Z.to_nat (CtModel.bm_len b1) - length (to_bytes (CtModel.bm_bytes b1)))%nat with 0%nat by (unfold to_bytes; rewrite length_map; unfold zlength in BLEN; clear - BLEN; lia).
        cbn [firstn]. rewrite app_nil_r. apply firstn_all2. unfold to_bytes. rewrite length_map. unfold zlength in BLEN. clear - BLEN. lia.
      * destruct BI4 as [EA0 EL0].
        eapply implAp_abind.
        { eapply W with (b := b1) (A0 := A') (NEW1 := []) (BUF := f + 80) (bytes := []) (CX := CX'); clear W;
            [ rewrite KC5; pose proof STKB as X; rewrite KC1 in X; clear - X; lia
            | unfold CtColP.ColDefs.buf_blk; rewrite EBD, app_nil_r; exact OIY
            | exact XBUF| exact ALB
            | unfold CtColP.ColDefs.buf_cells, MallocRep.wz; exact HBUFY
            | unfold CtModel.bm_max; rewrite EBD; clear - BL0 EL0; lia| clear - EL0; lia| clear - LB26; lia
            | rewrite EBD; exact EA0
            | exact GC1
            | replace (bv_unsigned sp + (spa - bv_unsigned sp)) with spa by (clear; lia); exact UWY
            | rewrite unsigned_lit by (clear; lia); exact (uk_ctx_call _ _ _ _ E_ex_grow CTX) ]. }
        clear W. intros r2 Σg msg POG. eapply AFTER; [exact POG|].
        rewrite EL0. cbn [Z.to_nat firstn]. symmetry. rewrite EL0 in BLEN. destruct (CtModel.bm_bytes b1); [reflexivity| unfold zlength in BLEN; cbn in BLEN; lia].
    + (* [comment removed for export] *)
      clear RESY.
      pose proof (munch_refl ([] : list (Z * Z)) mY) as MU. pose proof (wmono_refl ctasegs mY) as WM.
      freeze FRLA. freeze F104. freeze F110. freeze F111. freeze F112. freeze F120. freeze FRLB. freeze FRH. freeze HOPPX. freeze HPVX. freeze HTLCX. freeze HPPY.
      unfold CtColP.ColDefs.buf_cells, MallocRep.wz in HBUFY.
      apply implAp_from_evt. step. if_true. step. step. step. change (zxb (Z_to_bv 8 1)) with (Z_to_bv 64 1). step. if_false.
      step. step. step. step. step. apply evt_done. clear MU WM.
      thaw FRLA. thaw F104. thaw F110. thaw F111. thaw F112. thaw F120. thaw FRLB. thaw FRH. thaw HOPPX. thaw HPVX. thaw HTLCX. thaw HPPY.
      (* [comment removed for export] *)
      assert (TAILF : forall (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y20 y23 y24 y26 y27 y28 y29 y30 y31 : word) (FF : bvmap 5 word) (fcF : definitions.bv 32) mF ΣF CXF,
        linv qfc qb mr ΣF st1 mF OWY boY [] CXF -> 0 <= CXF ->
        agree_on (aclient_addr (OWY ++ pbs qfc qb ++ LB) spa) mY mF ->
        @implAp (push AR f 2) _ (ARet (@None (CtModel.octet bptr), st1)) ΣF POST
          (MS (mkR y1 (Z_to_bv 64 spa) gp (Z_to_bv 64 TP_A) y5 y6 y7 sp (Z_to_bv 64 spa) y10 y11 y12 y13 y14 y15 y16 y17
                   (Z_to_bv 64 f) (Z_to_bv 64 f) y20 (Z_to_bv 64 SHB) (Z_to_bv 64 (shad f)) y23 y24 (Z_to_bv 64 0) y26 y27 y28 y29 y30 y31)
              FF (Z_to_bv 64 ADEP_EXIT) fcF None mF (seg_rom ctasegs))).      (* [comment removed for export] *)
      { intros until CXF. intros LIF HCXF AGF'.
        assert (AXS : forall A0 cs, rw_cells ctasegs mY A0 cs -> spa <= A0 -> A0 + Z.of_nat (cells_size cs) <= bv_unsigned sp -> rw_cells ctasegs mF A0 cs).
        { intros A0 cs HC H1 H2. eapply rw_cells_agree; [exact AGF'| exact HC|]. intros a Ha. left. clear - Ha H1 H2 TOP. lia. }
        apply AXS in FRLA; [| clear; lia| cbn; clear - SPAH; lia]. apply AXS in HPPY; [| clear; lia| cbn; clear - SPAH; lia].
        apply AXS in F104; [| clear; lia| cbn; clear - SPAH; lia]. apply AXS in F110; [| clear; lia| cbn; clear - SPAH; lia].
        apply AXS in F111; [| clear; lia| cbn; clear - SPAH; lia]. apply AXS in F112; [| clear; lia| cbn; clear - SPAH; lia].
        apply AXS in F120; [| clear; lia| cbn; clear - SPAH; lia].
        apply AXS in FRLB; [| clear; lia| cbn [cells_size csize Nat.add]; rewrite ?Nat2Z.inj_add; clear - GSZ SPAH; lia].
        apply AXS in FRH; [| clear - SPAH; lia| cbn; clear; lia]. clear AXS.
        Local Ltac blkF AGF' H b Hb RNG := apply (rw_cells_agree _ _ _ _ _ AGF') in H; [| intros a Ha; cbn in Ha; right; right; exists b; split; [apply in_or_app; right; apply in_or_app; right; exact Hb| RNG]].
        blkF AGF' HOPPX bq Hbq ltac:(clear - Ha BQ1 BQ2; lia). blkF AGF' HPVX bv Hbv ltac:(clear - Ha BV1 BV2; lia). blkF AGF' HTLCX bt Hbt ltac:(clear - Ha BT1 BT2; lia).
        apply rw_cells_CB_ofA in F112. cbn [cells_size csize Nat.add] in F112.
        pose proof (rw_cells_app_join mF _ _ _ F110 ltac:(cbn [cells_size csize Nat.add]; replace (spa + 110 + Z.of_nat 1) with (spa + 111) by (clear; lia); exact F111)) as FP1.
        pose proof (rw_cells_app_join mF _ _ _ FP1 ltac:(cbn [cells_size csize Nat.add app]; replace (spa + 110 + Z.of_nat 2) with (spa + 112) by (clear; lia); exact F112)) as FPIC.
        cbn [app] in FPIC. clear FP1.
        destruct (exo_join20 f spa g junk mF _ _ _ _ _ _ _ _ _ _ _ (CB 8 j16) (CB 8 j24) _ _ _ _ _ _ _ _ eq_refl eq_refl FRLA HPPY F104 FPIC F120 FRLB)
          as (k16 & k24 & k32 & k40 & k48 & k96 & k104 & k120 & FRL).
        apply rw_cells_CB_ofA in HTLCX. cbn [cells_size csize Nat.add cells_bytes cbytes app] in HTLCX.
        eapply (exo_exit STK CST FRMb ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m Σ st OW LB E bo lo K adr D d OPP PV TLC j31 f spa g junk gj Σ1) with (res := None) (mr := mr) (adr' := adr);
          [exact PRE0| exact KOW| exact CELLS| exact LEN1| exact FRESH| exact GEO| exact CR1| exact SPA32| exact SPAL| exact SPAH| exact GSZ| exact SAVJ| exact STKB
          | exact AGFr| exact LIF| exact HCXF| intros b Hb; reflexivity| intros b Hb; destruct Hb
          | exact HOPPX| exact HTLCX| split; [reflexivity| exact HPVX]| exact FRL| exact FRH]. }
      destruct (CtModel.bm_data b1) as [[q0 n0]|] eqn:EBD.
      * (* [comment removed for export] *)
        cbn [app] in HEAPY.
        assert (NIq : ~ In q0 (map blk_id (OWY ++ pbs qfc qb ++ LB))) by (exact (FRSHY (q0, A', n0) (or_introl eq_refl))).
        assert (NIql : ~ In q0 (map blk_id (pbs qfc qb ++ LB))) by (intros X; apply NIq; rewrite map_app; apply in_or_app; right; exact X).
        assert (NIqo : ~ In q0 (map blk_id OWY)) by (intros X; apply NIq; rewrite map_app; apply in_or_app; left; exact X).
        assert (HEAPO : @BnHeapA.AHEAP (push AR f 2) Σc ((q0, A', n0) :: OWY) (pbs qfc qb ++ LB) mY).
        { pose proof (@AH_adopt (push AR f 2) _ _ _ _ (q0, A', n0) HEAPY ltac:(left; reflexivity) (Forall_inv LBOKY)) as H.
          rewrite lb_remove_cons in H. cbn [blk_id fst snd] in H. rewrite bptr_eqb_refl in H. rewrite (lb_remove_notin _ _ NIql) in H. exact H. }
        unfold abind, afree_opt, afree, aret. cbn [apbind option_map fst snd].
        eapply CRYPTO_free_walkAp with (lo := lo) (A := A') (n := n0); rewrite ?ESPA;
          [exact HEAPO| left; reflexivity| exact STY| exact CEIL| clear - LOY STKB ESF; lia| exact TOPY| exact ALY| exact MIY| reflexivity| exact CSY| reflexivity
          | exact UWY| rewrite unsigned_lit by (clear; lia); exact (uk_ctx_call _ _ _ _ E_ex_free CTX)|].
        intros ΣF msF POF. unfold cfree_postA in POF. rewrite ?ESPA in POF.
        destruct POF as (z0 & z1 & z2 & u0 & u1 & u2 & u3 & u4 & u5 & u6 & u7 & z3 & z4 & z5 & z6 & FF & fcF & mF & -> & MIF & STF & AGF' & CRF & HEAPF).
        rewrite (ret_pc_even 0x24227c) by (clear; lia).
        cbn [app] in AGF'. rewrite lb_remove_cons in AGF', HEAPF. cbn [blk_id fst snd] in AGF', HEAPF. rewrite bptr_eqb_refl in AGF', HEAPF.
        rewrite (lb_remove_notin _ _ NIq) in AGF'. rewrite (lb_remove_notin _ _ NIqo) in HEAPF.
        assert (LIF : linv qfc qb mr ΣF st1 mF OWY boY [] (CX' - 0)).
        { kitp (@oinv_heap (push AR f 2)) qfc qb mr OH.
          eapply OH with (L1 := OWY ++ pbs qfc qb ++ LB);
            [exact OIY| replace (bv_unsigned sp + (spa - bv_unsigned sp)) with spa by (clear; lia); eapply agree_on_mono; [exact AGF'|]; intros a [Ha _]; exact Ha
            | intros b [Hb|Hb]; apply in_or_app; [left; exact Hb| right; exact Hb]
            | cbn [app]; exact HEAPF| constructor| exact MIF| replace (bv_unsigned sp + (spa - bv_unsigned sp)) with spa by (clear; lia); exact STF
            | cbn [ar_RT push amb] in CRF |- *; rewrite CRF; clear; lia| clear - CRY; lia]. }
        unfold MallocRep.wz. eapply TAILF; [exact LIF| clear - CRY; lia| exact AGF'].
      * (* [comment removed for export] *)
        destruct BI4 as [EA0 EL0]. subst A'. cbn [app] in HEAPY.
        unfold abind, afree_opt, afree, aret. cbn [apbind option_map fst snd].
        eapply implAp_step_same.
        { eapply CRYPTO_free_null_cpsA with (lo := lo) (OW := OWY) (LB := pbs qfc qb ++ LB); rewrite ?ESPA;
            [exact HEAPY| exact STY| exact CEIL| clear - LOY STKB ESF; lia| exact TOPY| exact ALY| exact MIY| reflexivity| exact CSY| reflexivity
            | exact UWY| rewrite unsigned_lit by (clear; lia); exact (uk_ctx_call _ _ _ _ E_ex_free CTX)]. }
        intros msF POF. unfold cfree_null_post in POF. rewrite ?ESPA in POF.
        destruct POF as (z0 & z1 & z2 & u0 & u1 & u2 & u3 & u4 & u5 & u6 & u7 & z3 & z4 & z5 & z6 & FF & fcF & mF & -> & MIF & STF & HEAPF & AGF').
        rewrite (ret_pc_even 0x24227c) by (clear; lia).
        assert (LIF : linv qfc qb mr Σc st1 mF OWY boY [] (CX' - 0)).
        { kitp (@oinv_heap (push AR f 2)) qfc qb mr OH.
          eapply OH with (L1 := OWY ++ pbs qfc qb ++ LB);
            [exact OIY| replace (bv_unsigned sp + (spa - bv_unsigned sp)) with spa by (clear; lia); eapply agree_on_mono; [exact AGF'|]; intros a [Ha _]; exact Ha
            | intros b [Hb|Hb]; apply in_or_app; [left; exact Hb| right; exact Hb]
            | cbn [app]; exact HEAPF| constructor| exact MIF| replace (bv_unsigned sp + (spa - bv_unsigned sp)) with spa by (clear; lia); exact STF
            | clear; lia| clear - CRY; lia]. }
        unfold MallocRep.wz. eapply TAILF; [exact LIF| clear - CRY; lia| exact AGF'].
  Qed.
End Body.
End WithRT.
