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
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtColA Require Import ColBudgetA ColDefsA CtlStmtA W_bufmemA W_collectA W_d2iA_stmt W_d2iA_exprim_ctx W_d2iA_exprim_tail.
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
Definition EX_CT_RET : Z := 0x241b70.       (* [comment removed for export] *)
Definition EX_PRIM_ARM : Z := 0x241de0.      (* [comment removed for export] *)
Definition EX_CONS_ARM : Z := 0x2420fc.      (* [comment removed for export] *)
Definition EX_RAISE779 : Z := 0x241b80.     (* [comment removed for export] *)
(* [comment removed for export] *)
Definition A_ASN1_D2I_EX_PRIMITIVE_A : Z := 0x72d20.

(* [comment removed for export] *)
Local Notation E_ex_new := (E_asn1_d2i_ex_primitive_244548 : uk_call 0x24187c 0x241b84 0x1fd52c).     (* [comment removed for export] *)
Local Notation E_ex_dbg := (E_asn1_d2i_ex_primitive_244560 : uk_call 0x24187c 0x241b9c 0x1fd844).     (* [comment removed for export] *)
Local Notation E_ex_err := (E_asn1_d2i_ex_primitive_244574 : uk_call 0x24187c 0x241bb0 0x1fdab8).     (* [comment removed for export] *)

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
  Definition exo_lowD (j0 j8 j16 j24 j64 j72 j80 : list byte) : list cell :=
    [CB 8 j0; CB 8 j8; CB 8 j16; CB 8 j24; C8 (Z_to_bv 64 (Z.shiftr OPP 3 + SHB)); C8 (Z_to_bv 64 PV); C8 (Z_to_bv 64 (f + 80)); C8 (Z_to_bv 64 OPP);
     CB 8 j64; CB 8 j72; CB 8 j80; C8 (Z_to_bv 64 f)].      (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition exd_facts (qfc qb : bptr) (mr : mem) (ΣX : rts RT) (stX : ap_st bptr) (mX : mem) (OWX : list block) (boX : Z * Z) (CX : Z)
      (j0 j8 j16 j24 j64 j72 j80 j104 j120 j128 j136 j144 jt : list byte) (vb : byte) : Prop :=
    agree_on (aclient_addr (OW ++ LB) (bv_unsigned sp)) m mr
    /\ linv qfc qb mr ΣX stX mX OWX boX [] CX /\ CST len - 2 <= CX
    /\ uw_chain USTACK_TOP mX spa (bv_unsigned sp) (bv_unsigned ra :: ras)
    /\ rw_cells ctasegs mX spa (exo_lowD j0 j8 j16 j24 j64 j72 j80)
    /\ rw_cells ctasegs mX (spa + 96) [C8 (Z_to_bv 64 (D + go_p gr))] /\ rw_cells ctasegs mX (spa + 104) [CB 6 j104]
    /\ rw_cells ctasegs mX (spa + 110) [C1 (Z_to_bv 8 (Z.land (go_ret gr) 1))] /\ rw_cells ctasegs mX (spa + 111) [C1 (Z_to_bv 8 (Z.land (go_ret gr) 32))]
    /\ rw_cells ctasegs mX (spa + 112) [C8 (Z_to_bv 64 plen)] /\ rw_cells ctasegs mX (spa + 120) [CB 4 j120; C4 (Z_to_bv 64 V_ASN1_OCTET_STRING)]
    /\ rw_cells ctasegs mX (spa + 128) [CB 8 j128; CB 8 j136; CB 8 j144; CB g junk]
    /\ rw_cells ctasegs mX (bv_unsigned sp + -16) [C8 s0; C8 ra]
    /\ rw_cells ctasegs mX (f + 64) [C1 (Z_to_bv 8 0)] /\ rw_cells ctasegs mX (f + 80) [CB 32 (repeat (Z_to_bv 8 0) 32)]
    /\ rw_cells ctasegs mX OPP [C8 (Z_to_bv 64 D)] /\ rw_cells ctasegs mX PV [C8 (Z_to_bv 64 0)] /\ rw_cells ctasegs mX TLC [C1 vb; CB 31 jt]
    /\ go_err gr = None /\ go_tag gr = V_ASN1_OCTET_STRING /\ go_cls gr = 0
    /\ junk = gj ++ cells_bytes [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1].
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition exd_ms (pc : Z) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (FX : bvmap 5 word) (fcX : bv 32) (mX : mem) : machine_state :=
    MS (mkR x1 (Z_to_bv 64 spa) gp (wz TP_A) x5 x6 x7 sp (Z_to_bv 64 spa) x10 x11 x12 x13 x14 x15 x16 x17
             (Z_to_bv 64 f) (Z_to_bv 64 f) (Z_to_bv 64 0) (Z_to_bv 64 SHB) (Z_to_bv 64 (shad f)) (Z_to_bv 64 ITEM_OCTET_A) (Z_to_bv 64 TLC) (Z_to_bv 64 1) (Z_to_bv 64 (f + 64))
             (Z_to_bv 64 V_ASN1_OCTET_STRING) x28 x29 x30 x31)
       FX (Z_to_bv 64 pc) fcX None mX (seg_rom ctasegs).

  (* [comment removed for export] *)
  Hypothesis HPRIM : forall qfc qb mr ΣX stX mX OWX boX CX (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) FX fcX
      (j0 j8 j16 j24 j64 j72 j80 j104 j120 j128 j136 j144 jt : list byte) (vb : byte),
    Z.land (go_ret gr) 32 = 0 ->
    exd_facts qfc qb mr ΣX stX mX OWX boX CX j0 j8 j16 j24 j64 j72 j80 j104 j120 j128 j136 j144 jt vb ->
    @implAp (push AR f 2) _
      ((blk <- amalloc SZ_ASN1_STRING ;;
        dp <- amalloc_crypto plen ;;
        aret (Some (CtModel.mkOct blk (option_map (fun q => (q, plen)) dp) plen (CtWire.slice d (go_p gr) plen)))) stX)
      ΣX POST (exd_ms EX_PRIM_ARM x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 FX fcX mX).
  Hypothesis HCONS : forall qfc qb mr ΣX stX mX OWX boX CX (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) FX fcX
      (j0 j8 j16 j24 j64 j72 j80 j104 j120 j128 j136 j144 jt : list byte) (vb : byte),
    Z.land (go_ret gr) 32 <> 0 ->
    exd_facts qfc qb mr ΣX stX mX OWX boX CX j0 j8 j16 j24 j64 j72 j80 j104 j120 j128 j136 j144 jt vb ->
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
      ΣX POST (exd_ms EX_CONS_ARM x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 FX fcX mX).

  (* [comment removed for export] *)
  Definition exc_facts (mc : mem) (j0 j8 j16 j24 j64 j72 j80 j104 j120 j128 j136 j144 : list byte) : Prop :=
    agree_on (aclient_addr (OW ++ LB) (bv_unsigned sp)) m mc
    /\ uw_chain USTACK_TOP mc spa (bv_unsigned sp) (bv_unsigned ra :: ras)
    /\ rw_cells ctasegs mc spa (exo_lowD j0 j8 j16 j24 j64 j72 j80)
    /\ rw_cells ctasegs mc (spa + 104) [CB 6 j104] /\ rw_cells ctasegs mc (spa + 120) [CB 4 j120; C4 (Z_to_bv 64 V_ASN1_OCTET_STRING)]
    /\ rw_cells ctasegs mc (spa + 128) [CB 8 j128; CB 8 j136; CB 8 j144; CB g junk]
    /\ rw_cells ctasegs mc (bv_unsigned sp + -16) [C8 s0; C8 ra]
    /\ rw_cells ctasegs mc (f + 64) [C1 (Z_to_bv 8 0)] /\ rw_cells ctasegs mc (f + 80) [CB 32 (repeat (Z_to_bv 8 0) 32)]
    /\ rw_cells ctasegs mc OPP [C8 (Z_to_bv 64 D)] /\ rw_cells ctasegs mc PV [C8 (Z_to_bv 64 0)].
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition exr_ms (pc : Z) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x25 x28 x29 x30 x31 : word) (FX : bvmap 5 word) (fcX : bv 32) (mX : mem) : machine_state :=
    MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + (spa - bv_unsigned sp))) gp (wz TP_A) x5 x6 x7 sp (Z_to_bv 64 spa) x10 x11 x12 x13 x14 x15 x16 x17
             (Z_to_bv 64 f) (Z_to_bv 64 f) (Z_to_bv 64 0) (Z_to_bv 64 SHB) (Z_to_bv 64 (shad f)) (Z_to_bv 64 ITEM_OCTET_A) (Z_to_bv 64 TLC) x25 (Z_to_bv 64 len)
             (Z_to_bv 64 V_ASN1_OCTET_STRING) x28 x29 x30 x31)
       FX (Z_to_bv 64 pc) fcX None mX (seg_rom ctasegs).

  (* [comment removed for export] *)
  Lemma exo_keep : forall qfc qb (NEWx : list block) (XX : list (Z * Z)) mA mB A cs,
    ax_pres (NEWx ++ pbs qfc qb ++ LB) (bv_unsigned sp + (spa - bv_unsigned sp)) (XX ++ LIBW_A) mA mB ->
    rw_cells ctasegs mA A cs ->
    (forall a, A <= a < A + Z.of_nat (cells_size cs) -> ~ rin_ivs XX a) ->
    ((spa <= A /\ A + Z.of_nat (cells_size cs) <= USTACK_TOP)
     \/ (f + 64 <= A /\ A + Z.of_nat (cells_size cs) <= f + 65) \/ (f + 80 <= A /\ A + Z.of_nat (cells_size cs) <= f + 112)
     \/ (A = OPP /\ Z.of_nat (cells_size cs) = 8) \/ (A = PV /\ Z.of_nat (cells_size cs) = 8) \/ (A = TLC /\ Z.of_nat (cells_size cs) = 32)) ->
    rw_cells ctasegs mB A cs.
  Proof.
    intros until cs. intros AX H NX WH. ctx. unhide BQ5. unhide BV5. unhide BT5.
    eapply rw_cells_agree; [exact AX| exact H|]. intros a Ha. split.
    - intros HIN. apply rin_ivs_app in HIN as [HIN|HIN]; [exact (NX a Ha HIN)|]. pose proof (libw_rangeA a HIN) as R.
      clear - Ha WH R G4 CL1 CEIL LO ESS SPAL BQ1 BQ2 BQ5 BV1 BV2 BV5 BT1 BT2 BT5. unfold SEGTOP_A in *. lia.
    - destruct WH as [W1|[W1|[W1|[[-> W1]|[[-> W1]|[-> W1]]]]]].
      + left. clear - Ha W1. lia.
      + right; right. exists (qfc, f + 64, 1). split; [apply in_or_app; right; apply in_or_app; left; left; reflexivity| cbn; clear - Ha W1; lia].
      + right; right. exists (qb, f + 80, 32). split; [apply in_or_app; right; apply in_or_app; left; right; left; reflexivity| cbn; clear - Ha W1; lia].
      + right; right. exists bq. split; [apply in_or_app; right; apply in_or_app; right; exact Hbq| clear - Ha W1 BQ1 BQ2; lia].
      + right; right. exists bv. split; [apply in_or_app; right; apply in_or_app; right; exact Hbv| clear - Ha W1 BV1 BV2; lia].
      + right; right. exists bt. split; [apply in_or_app; right; apply in_or_app; right; exact Hbt| clear - Ha W1 BT1 BT2; lia].
  Qed.

  (* [comment removed for export] *)
  Lemma exo_keep_uw : forall qfc qb (NEWx : list block) (XX : list (Z * Z)) mA mB,
    ax_pres (NEWx ++ pbs qfc qb ++ LB) (bv_unsigned sp + (spa - bv_unsigned sp)) (XX ++ LIBW_A) mA mB ->
    (forall a, rin_ivs XX a -> a < bv_unsigned sp - 16) ->
    uw_chain USTACK_TOP mA spa (bv_unsigned sp) (bv_unsigned ra :: ras) -> uw_chain USTACK_TOP mB spa (bv_unsigned sp) (bv_unsigned ra :: ras).
  Proof.
    intros until mB. intros AX NX UWA. ctx. eapply uw_chain_agree16; [exact UWA|]. eapply agree_on_mono; [exact AX|]. intros a Ha. cbv beta in Ha. split.
    - intros HIN. apply rin_ivs_app in HIN as [HIN|HIN]; [pose proof (NX a HIN); clear - H Ha; lia|]. pose proof (libw_rangeA a HIN) as R. clear - Ha R CL1 CEIL LO ESS SPAL SPAH. lia.
    - left. clear - Ha SPAH. lia.
  Qed.

  (* [comment removed for export] *)
  Definition raise779_postA (qfc qb : bptr) (mr mX : mem) (CX : Z) (x25 : word) (r : unit * ap_st bptr) (ΣY : rts RT) : machine_state -> Prop :=
    fun ms' => exists (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (FY : bvmap 5 word) (fcY : bv 32) mY OWY boY,
      ms' = exr_ms 0x241bb0 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x25 x28 x29 x30 x31 FY fcY mY
      /\ linv qfc qb mr ΣY (snd r) mY OWY boY [] (CX - GETOBJ_ERR_COST_A)
      /\ ax_pres ([] ++ pbs qfc qb ++ LB) (bv_unsigned sp + (spa - bv_unsigned sp)) LIBW_A mX mY.

  Lemma exo_raise779 : forall qfc qb mr ΣX stX mX OWX boX CX (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x25 x28 x29 x30 x31 : word) FX fcX,
    linv qfc qb mr ΣX stX mX OWX boX [] CX -> GETOBJ_ERR_COST_A <= CX ->
    uw_chain USTACK_TOP mX spa (bv_unsigned sp) (bv_unsigned ra :: ras) ->
    @implAp (push AR f 2) _ (err_raise RS_prim_nested stX) ΣX (raise779_postA qfc qb mr mX CX x25)
      (exr_ms EX_RAISE779 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x25 x28 x29 x30 x31 FX fcX mX).
  Proof.
    intros until fcX. intros LI HCX UWX. ctx. kitp (@oinv_call (push AR f 2)) qfc qb mr OC. kitp (@oinv_facts (push AR f 2)) qfc qb mr OFc.
    pose proof (OC _ _ _ _ _ _ _ LI) as (HEAPX & STX & _ & _ & _ & _ & MIX & _). rewrite ?(Z.add_simpl_l) in STX.
    replace (bv_unsigned sp + (spa - bv_unsigned sp)) with spa in STX by (clear; lia).
    pose proof col_consts as (KC1 & KC2 & KC3 & KC4 & KC5 & KC6 & KC7).
    destruct (lit_okA_auto A_TASN_DEC_C_A 23 ltac:(vm_compute; reflexivity)) as (fs & fk & LF).
    destruct (lit_okA_auto A_ASN1_D2I_EX_PRIMITIVE_A 22 ltac:(vm_compute; reflexivity)) as (ns & nk & LN).
    change 23 with (rs_flen RS_prim_nested) in LF. change 22 with (rs_fnlen RS_prim_nested) in LN.
    assert (STKG : ADEP_FRAME + 66352 <= STK) by (pose proof STKB as X; rewrite KC1 in X; clear - X; lia).
    assert (FRMG : 1 + 6 <= FRMb) by (pose proof FRMBb as X; rewrite KC4 in X; clear - X; lia).
    Local Ltac ecu := unfold ERR_SET_ERROR_COST, ERR_SET_ERROR_FRAMES, ERR_SET_ERROR_STACK, ERR_VSET_ERROR_COST, ERR_VSET_ERROR_FRAMES, ERR_VSET_ERROR_STACK,
                             ERR_NEW_COST, ERR_NEW_FRAMES, ERR_NEW_STACK, ERR_SET_DEBUG_COST, ERR_SET_DEBUG_FRAMES, ERR_SET_DEBUG_STACK, RT_STACK, ADEP_FRAME in *.
    (* [comment removed for export] *)
    Local Ltac err_call Wc Ec OIc UWc q1 q2 mr0 SG FG CX0 :=
      eapply (@oinv_ap_callA (push AR f 2) UK sp mr0 Σ1 (exo_pbs f q1 q2 ++ LB) E lo K d D (exo_XP OPP PV TLC f) (spa - bv_unsigned sp) (STK - ADEP_FRAME) (CST len - 1) (FRMb - 1)
                (exo_KH STK CST FRMb sp m Σ st OW LB E bo lo D d OPP PV TLC j31 f spa PRE0 CELLS LEN1 FRESH GEO SPA32 SPAL SPAH STKB q1 q2));
      [ exact Wc | exact OIc | ecu; clear - SG; lia | | ecu; clear - FG; lia
      | replace (bv_unsigned sp + (spa - bv_unsigned sp)) with spa by (clear; lia); exact UWc
      | rewrite unsigned_lit by (clear; lia); exact (uk_ctx_call _ _ _ _ Ec CX0)
      | apply cons_ne
      | ].
    unfold err_raise, exr_ms, EX_RAISE779. unfold MallocRep.wz in *.
    pose proof (munch_refl (@nil (Z * Z)) mX) as MU. pose proof (wmono_refl ctasegs mX) as WM.
    (* [comment removed for export] *)
    eapply implAp_abind.
    { apply implAp_from_evt. step. apply evt_done.
      err_call constr:(@ERR_new_walkA (push AR f 2) UK BE boX) constr:(E_ex_new) LI UWX qfc qb mr STKG FRMG CTX; [rewrite KC3 in HCX; ecu; clear - HCX; lia| reflexivity]. }
    intros r1 Σa msa POa. unfold ap_call_postA in POa.
    destruct POa as (q0 & q1 & q2 & q10 & q11 & q12 & q13 & q14 & q15 & q16 & q17 & q3 & q4 & q5 & q6 & Fa & fca & mA & OWa & boa & -> & LIa & AXa & EBOa). cbv beta in EBOa. subst boa.
    rewrite (ret_pc_even 0x241b84) by (clear; lia).
    pose proof (exo_keep_uw qfc qb [] [] mX mA AXa ltac:(intros a Ha; destruct Ha) UWX) as UWa.
    pose proof (OC _ _ _ _ _ _ _ LIa) as (_ & STa & _ & _ & _ & _ & MIa & _). replace (bv_unsigned sp + (spa - bv_unsigned sp)) with spa in STa by (clear; lia).
    clear MU WM. pose proof (munch_refl (@nil (Z * Z)) mA) as MU. pose proof (wmono_refl ctasegs mA) as WM.
    (* [comment removed for export] *)
    eapply implAp_abind.
    { apply implAp_from_evt. do 5 step. step. apply evt_done.
      err_call constr:(@ERR_set_debug_walkA (push AR f 2) UK BE STRCPY RS_prim_nested A_TASN_DEC_C_A A_ASN1_D2I_EX_PRIMITIVE_A boX _ _ _ _ LF LN) constr:(E_ex_dbg) LIa UWa qfc qb mr STKG FRMG CTX.
      - pose proof LIa as (PREa & _). pose proof PREa as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & CRa & _). rewrite KC3 in HCX. ecu. cbn [ar_RT push amb] in CRa |- *. clear - CRa HCX. lia.
      - cbv beta. unfold A_TASN_DEC_C_A, A_ASN1_D2I_EX_PRIMITIVE_A. repeat split; try reflexivity; apply bv_eq; vm_compute; reflexivity. }
    intros r2 Σb msb POb. unfold ap_call_postA in POb.
    destruct POb as (p0 & p1 & p2 & p10 & p11 & p12 & p13 & p14 & p15 & p16 & p17 & p3 & p4 & p5 & p6 & Fb & fcb & mB & OWb & bob & -> & LIb & AXb & EBOb). cbv beta in EBOb. subst bob.
    rewrite (ret_pc_even 0x241b9c) by (clear; lia).
    pose proof (exo_keep_uw qfc qb [] [] mA mB AXb ltac:(intros a Ha; destruct Ha) UWa) as UWb.
    pose proof (OC _ _ _ _ _ _ _ LIb) as (_ & STb & _ & _ & _ & _ & MIb & _). replace (bv_unsigned sp + (spa - bv_unsigned sp)) with spa in STb by (clear; lia).
    clear MU WM. pose proof (munch_refl (@nil (Z * Z)) mB) as MU. pose proof (wmono_refl ctasegs mB) as WM.
    (* [comment removed for export] *)
    eapply implAp_mono.
    { apply implAp_from_evt. do 4 step. step. apply evt_done.
      err_call constr:(@ERR_set_error_closedA (push AR f 2) UK BE RS_prim_nested 13 ERR_R_NESTED_ASN1_ERROR boX) constr:(E_ex_err) LIb UWb qfc qb mr STKG FRMG CTX.
      - pose proof LIb as (PREb & _). pose proof PREb as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & CRb & _).
        pose proof LIa as (PREa' & _). pose proof PREa' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & CRa' & _). rewrite KC3 in HCX. ecu. cbn [ar_RT push amb] in CRa', CRb |- *. clear - CRa' CRb HCX. lia.
      - cbv beta. unfold ERR_LIB_SYS, ERR_R_NESTED_ASN1_ERROR. repeat split; try reflexivity; try (clear; lia). all: apply bv_eq; vm_compute; reflexivity. }
    intros r3 Σc msc POc. unfold ap_call_postA in POc.
    destruct POc as (o0 & o1 & o2 & o10 & o11 & o12 & o13 & o14 & o15 & o16 & o17 & o3 & o4 & o5 & o6 & Fc & fcc & mC & OWc & boc & -> & LIc & AXc & EBOc). cbv beta in EBOc. subst boc.
    rewrite (ret_pc_even 0x241bb0) by (clear; lia).
    unfold raise779_postA, exr_ms. do 16 eexists. exists Fc, fcc, mC, OWc, boX.
    split; [reflexivity|]. split; [| cbn [app]; exact (ax_pres_trans _ _ _ _ _ _ AXa (ax_pres_trans _ _ _ _ _ _ AXb AXc))].
    kitp (@oinv_credit (push AR f 2)) qfc qb mr OCR. eapply OCR; [exact LIc|].
    pose proof LIc as (PREc & _). pose proof PREc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & CRc & _). rewrite KC3 in HCX |- *. ecu. cbn [ar_RT push amb] in CRc |- *. clear - CRc HCX. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma exo_join20 : forall mX (j0 j8 j64 j72 j80 j104 jl j120 j128 j136 j144 : list byte) (c16 c24 : cell) (a32 a40 a48 a56 : Z) (v96 v124 : word) (bi bc : byte),
    csize c16 = 8%nat -> csize c24 = 8%nat ->
    rw_cells ctasegs mX spa [CB 8 j0; CB 8 j8; c16; c24; C8 (Z_to_bv 64 a32); C8 (Z_to_bv 64 a40); C8 (Z_to_bv 64 a48); C8 (Z_to_bv 64 a56); CB 8 j64; CB 8 j72; CB 8 j80; C8 (Z_to_bv 64 f)] ->
    rw_cells ctasegs mX (spa + 96) [C8 v96] -> rw_cells ctasegs mX (spa + 104) [CB 6 j104] -> rw_cells ctasegs mX (spa + 110) [C1 bi; C1 bc; CB 8 jl] ->
    rw_cells ctasegs mX (spa + 120) [CB 4 j120; C4 v124] -> rw_cells ctasegs mX (spa + 128) [CB 8 j128; CB 8 j136; CB 8 j144; CB g junk] ->
    exists j16 j24 j32 j40 j48 j96 j104' j120',      (* [comment removed for export] *)
      rw_cells ctasegs mX spa [CB 8 j0; CB 8 j8; CB 8 j16; CB 8 j24; CB 8 j32; CB 8 j40; CB 8 j48; C8 (Z_to_bv 64 a56); CB 8 j64; CB 8 j72; CB 8 j80; C8 (Z_to_bv 64 f);
                               CB 8 j96; CB 8 j104'; CB 8 jl; CB 8 j120'; CB 8 j128; CB 8 j136; CB 8 j144; CB g junk].
  Proof.
    intros until bc. intros C16 C24 FRLA F96 F104 FPIC F120 FRLB.
    apply (rw_cells_cb_first mX spa _ 7) in FRLA. cbn [cb_first csize cbytes] in FRLA. rewrite C16, C24 in FRLA.
    apply rw_cells_CB_ofA in F96. apply rw_cells_CB_ofA in F120. cbn [cells_size csize Nat.add] in F96, F120.
    lazymatch type of FPIC with rw_cells _ _ _ [?c1; ?c2; ?c3] => change [c1; c2; c3] with ([c1; c2] ++ [c3]) in FPIC end.
    apply rw_cells_app in FPIC as [F110 F112]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add] in F112.
    replace (spa + 110 + 2) with (spa + 112) in F112 by (clear; lia).
    pose proof (rw_cells_app_join mX _ _ _ F104 ltac:(cbn [cells_size csize Nat.add]; replace (spa + 104 + Z.of_nat 6) with (spa + 110) by (clear; lia); exact F110)) as FM.
    apply rw_cells_CB_ofA in FM. cbn [cells_size csize Nat.add app] in FM. clear F104 F110.
    pose proof (rw_cells_app_join mX _ _ _ FRLA ltac:(cbn [cells_size csize Nat.add]; replace (spa + Z.of_nat 96) with (spa + 96) by (clear; lia); exact F96)) as T1.
    pose proof (rw_cells_app_join mX _ _ _ T1 ltac:(cbn [cells_size csize Nat.add app]; replace (spa + Z.of_nat 104) with (spa + 104) by (clear; lia); exact FM)) as T2.
    pose proof (rw_cells_app_join mX _ _ _ T2 ltac:(cbn [cells_size csize Nat.add app]; replace (spa + Z.of_nat 112) with (spa + 112) by (clear; lia); exact F112)) as T3.
    pose proof (rw_cells_app_join mX _ _ _ T3 ltac:(cbn [cells_size csize Nat.add app]; replace (spa + Z.of_nat 120) with (spa + 120) by (clear; lia); exact F120)) as T4.
    pose proof (rw_cells_app_join mX _ _ _ T4 ltac:(cbn [cells_size csize Nat.add app]; replace (spa + Z.of_nat 128) with (spa + 128) by (clear; lia); exact FRLB)) as FRL.
    cbn [app] in FRL. do 8 eexists. exact FRL.
  Qed.

  (* [comment removed for export] *)
  Lemma exo_after_fail : forall qfc qb mc ΣY stY mY OWY boY CXY (x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) FY fcY
      (j0 j8 j16 j24 j64 j72 j80 j104 j120 j128 j136 j144 jl jt : list byte) (bi bc vb : byte) (pp : Z),
    exc_facts mc j0 j8 j16 j24 j64 j72 j80 j104 j120 j128 j136 j144 ->
    linv qfc qb mc ΣY stY mY OWY boY [] CXY -> GETOBJ_ERR_COST_A <= CXY ->
    ax_pres ([] ++ pbs qfc qb ++ LB) (bv_unsigned sp + (spa - bv_unsigned sp)) ([(spa + 110, spa + 110 + 10); (spa + 96, spa + 96 + 8); (TLC, TLC + 32)] ++ LIBW_A) mc mY ->
    rw_cells ctasegs mY (spa + 110) [C1 bi; C1 bc; CB 8 jl] -> rw_cells ctasegs mY (spa + 96) [C8 (wz pp)] -> rw_cells ctasegs mY TLC [C1 vb; CB 31 jt] ->
    @implAp (push AR f 2) _ ((err_raise RS_prim_nested ;;; aret None) stY) ΣY POST
      (exr_ms EX_CT_RET (Z_to_bv 64 EX_CT_RET) x5 x6 x7 (Z_to_bv 64 0) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 0) x28 x29 x30 x31 FY fcY mY).
  Proof.
    intros until pp. intros XF LI HCX AXY HPIC HPPC HTLCY. ctx.
    pose proof XF as (AGFc & UWc & FRLAc & F104c & F120c & FRLBc & FRHc & HFCc & HBUFc & HOPPc & HPVc).
    pose proof CELLS as (_ & _ & _ & _ & _ & _ & _ & _ & DOT & DVT & _).
    pose proof col_consts as (KC1 & KC2 & KC3 & KC4 & KC5 & KC6 & KC7).
    kitp (@oinv_call (push AR f 2)) qfc qb mc OC. pose proof (OC _ _ _ _ _ _ _ LI) as (HEAPY & STY & _ & _ & _ & _ & MIY & _). replace (bv_unsigned sp + (spa - bv_unsigned sp)) with spa in STY by (clear; lia).
    (* [comment removed for export] *)
    assert (NXS : forall A n a, (spa + 120 <= A \/ A + n <= spa + 96 \/ (spa + 104 <= A /\ A + n <= spa + 110)) -> spa <= A -> A <= a < A + n ->
                  ~ rin_ivs [(spa + 110, spa + 110 + 10); (spa + 96, spa + 96 + 8); (TLC, TLC + 32)] a).
    { intros A n a W SA Ha HIN. cbn [rin_ivs fst snd] in HIN. clear - W SA Ha HIN BT1 BT2 BT4 CEIL LO ESS SPAL. plia. }
    assert (NXF : forall a, f <= a < f + 248 -> ~ rin_ivs [(spa + 110, spa + 110 + 10); (spa + 96, spa + 96 + 8); (TLC, TLC + 32)] a).
    { intros a Ha HIN. cbn [rin_ivs fst snd] in HIN. clear - Ha HIN OT BT1 BT2 G3 CEIL LO ESS SPAL. plia. }
    assert (NXQ : forall a, OPP <= a < OPP + 8 -> ~ rin_ivs [(spa + 110, spa + 110 + 10); (spa + 96, spa + 96 + 8); (TLC, TLC + 32)] a).
    { intros a Ha HIN. cbn [rin_ivs fst snd] in HIN. clear - Ha HIN DOT BQ1 BQ2 BQ4 CEIL LO ESS SPAL. plia. }
    assert (NXV : forall a, PV <= a < PV + 8 -> ~ rin_ivs [(spa + 110, spa + 110 + 10); (spa + 96, spa + 96 + 8); (TLC, TLC + 32)] a).
    { intros a Ha HIN. cbn [rin_ivs fst snd] in HIN. clear - Ha HIN DVT BV1 BV2 BV4 CEIL LO ESS SPAL. plia. }
    Local Ltac kp AXY H NX WH := apply (exo_keep _ _ [] _ _ _ _ _ AXY) in H; [| NX| WH].
    kp AXY FRLAc ltac:(intros a Ha; apply (NXS spa 96 a); [right; left; clear; lia| clear; lia| cbn in Ha; exact Ha]) ltac:(left; cbn; clear - SPAH TOP; unfold USTACK_TOP in *; lia).
    kp AXY F104c ltac:(intros a Ha; apply (NXS (spa + 104) 6 a); [right; right; clear; lia| clear; lia| cbn in Ha; exact Ha]) ltac:(left; cbn; clear - SPAH TOP; unfold USTACK_TOP in *; lia).
    kp AXY F120c ltac:(intros a Ha; apply (NXS (spa + 120) 8 a); [left; clear; lia| clear; lia| cbn in Ha; exact Ha]) ltac:(left; cbn; clear - SPAH TOP; unfold USTACK_TOP in *; lia).
    kp AXY FRLBc ltac:(intros a Ha; cbn [cells_size csize Nat.add] in Ha; rewrite ?Nat2Z.inj_add in Ha; apply (NXS (spa + 128) (40 + Z.of_nat g) a); [left; clear; lia| clear; lia| clear - Ha; lia])
                 ltac:(left; cbn [cells_size csize Nat.add]; rewrite ?Nat2Z.inj_add; clear - SPAH TOP GSZ; unfold USTACK_TOP in *; lia).
    kp AXY FRHc ltac:(intros a Ha; apply (NXS (bv_unsigned sp + -16) 16 a); [left; clear - SPAH; lia| clear - SPAH; lia| cbn in Ha; exact Ha]) ltac:(left; cbn; clear - SPAH TOP; unfold USTACK_TOP in *; lia).
    kp AXY HFCc ltac:(intros a Ha; apply NXF; cbn in Ha; clear - Ha; lia) ltac:(right; left; cbn; clear; lia).
    kp AXY HBUFc ltac:(intros a Ha; apply NXF; cbn in Ha; clear - Ha; lia) ltac:(right; right; left; cbn; clear; lia).
    kp AXY HOPPc ltac:(intros a Ha; apply NXQ; cbn in Ha; exact Ha) ltac:(do 3 right; left; split; [reflexivity| reflexivity]).
    kp AXY HPVc ltac:(intros a Ha; apply NXV; cbn in Ha; exact Ha) ltac:(do 4 right; left; split; [reflexivity| reflexivity]).
    pose proof (exo_keep_uw _ _ [] _ _ _ AXY ltac:(intros a HIN; cbn [rin_ivs fst snd] in HIN; clear - HIN BT1 BT2 BT4 CEIL LO ESS SPAL SPAH; plia) UWc) as UWY.
    (* [comment removed for export] *)
    pose proof (munch_refl (@nil (Z * Z)) mY) as MU. pose proof (wmono_refl ctasegs mY) as WM.
    unfold exr_ms, EX_CT_RET. unfold MallocRep.wz in *. apply implAp_from_evt.
    step. step. step. if_false. step. if_false. apply evt_done.
    eapply implAp_abind.
    { eapply (exo_raise779 qfc qb mc); [exact LI| exact HCX| exact UWY]. }
    intros r3 Σc msc POc. unfold raise779_postA, exr_ms in POc.
    destruct POc as (o1 & o5 & o6 & o7 & o10 & o11 & o12 & o13 & o14 & o15 & o16 & o17 & o28 & o29 & o30 & o31 & Fc & fcc & mC & OWc & boc & -> & LIc & AXc).
    pose proof (OC _ _ _ _ _ _ _ LIc) as (_ & STc & _ & _ & _ & _ & MIc & _). replace (bv_unsigned sp + (spa - bv_unsigned sp)) with spa in STc by (clear; lia).
    (* [comment removed for export] *)
    change (ax_pres ([] ++ pbs qfc qb ++ LB) (bv_unsigned sp + (spa - bv_unsigned sp)) LIBW_A mY mC)
      with (ax_pres ([] ++ pbs qfc qb ++ LB) (bv_unsigned sp + (spa - bv_unsigned sp)) ([] ++ LIBW_A) mY mC) in AXc.
    Local Ltac kq AXc H WH := apply (exo_keep _ _ [] [] _ _ _ _ AXc) in H; [| intros a _ HIN; exact HIN| WH].
    kq AXc FRLAc ltac:(left; cbn; clear - SPAH TOP; unfold USTACK_TOP in *; lia).
    kq AXc F104c ltac:(left; cbn; clear - SPAH TOP; unfold USTACK_TOP in *; lia).
    kq AXc F120c ltac:(left; cbn; clear - SPAH TOP; unfold USTACK_TOP in *; lia).
    kq AXc FRLBc ltac:(left; cbn [cells_size csize Nat.add]; rewrite ?Nat2Z.inj_add; clear - SPAH TOP GSZ; unfold USTACK_TOP in *; lia).
    kq AXc FRHc ltac:(left; cbn; clear - SPAH TOP; unfold USTACK_TOP in *; lia).
    kq AXc HOPPc ltac:(do 3 right; left; split; [reflexivity| reflexivity]).
    kq AXc HPVc ltac:(do 4 right; left; split; [reflexivity| reflexivity]).
    kq AXc HPIC ltac:(left; cbn; clear - SPAH TOP; unfold USTACK_TOP in *; lia).
    kq AXc HPPC ltac:(left; cbn; clear - SPAH TOP; unfold USTACK_TOP in *; lia).
    apply rw_cells_CB_ofA in HTLCY. cbn [cells_size csize Nat.add cells_bytes cbytes app] in HTLCY.
    kq AXc HTLCY ltac:(do 5 right; split; [reflexivity| reflexivity]).
    destruct (exo_join20 mC _ _ _ _ _ _ _ _ _ _ _ (CB 8 j16) (CB 8 j24) _ _ _ _ _ _ _ _ eq_refl eq_refl FRLAc HPPC F104c HPIC F120c FRLBc) as (k16 & k24 & k32 & k40 & k48 & k96 & k104 & k120 & FRL).
    (* [comment removed for export] *)
    clear MU WM. pose proof (munch_refl (@nil (Z * Z)) mC) as MU. pose proof (wmono_refl ctasegs mC) as WM.
    cbn [fst snd]. unfold aret. apply implAp_from_evt. step.
    setreg 2%Z (Z_to_bv 64 spa) ltac:(f_equal; clear; lia). apply evt_done.
    eapply (exo_exit STK CST FRMb ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m Σ st OW LB E bo lo K adr D d OPP PV TLC j31 f spa g junk gj Σ1) with (res := None) (mr := mc) (adr' := adr);
      [exact PRE0| exact KOW| exact CELLS| exact LEN1| exact FRESH| exact GEO| exact CR1| exact SPA32| exact SPAL| exact SPAH| exact GSZ| exact SAVJ| exact STKB
      | exact AGFc| exact LIc| rewrite KC3 in HCX |- *; clear - HCX; lia| intros b Hb; reflexivity| intros b Hb; destruct Hb
      | exact HOPPc| exact HTLCY| split; [reflexivity| exact HPVc]| exact FRL| exact FRHc].
  Qed.

  (* [comment removed for export] *)
  Lemma exo_after_ok : forall qfc qb mc ΣY stY mY OWY boY CXY (x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) FY fcY
      (j0 j8 j16 j24 j64 j72 j80 j104 j120 j128 j136 j144 jt : list byte) (vb : byte),
    exc_facts mc j0 j8 j16 j24 j64 j72 j80 j104 j120 j128 j136 j144 ->
    linv qfc qb mc ΣY stY mY OWY boY [] CXY -> CST len - 2 <= CXY ->
    ax_pres ([] ++ pbs qfc qb ++ LB) (bv_unsigned sp + (spa - bv_unsigned sp)) ([(spa + 110, spa + 110 + 10); (spa + 96, spa + 96 + 8); (TLC, TLC + 32)] ++ LIBW_A) mc mY ->
    go_err gr = None -> go_tag gr = V_ASN1_OCTET_STRING -> go_cls gr = 0 ->
    rw_cells ctasegs mY (spa + 110) [C1 (Z_to_bv 8 (Z.land (go_ret gr) 1)); C1 (Z_to_bv 8 (Z.land (go_ret gr) 32)); C8 (wz (tlen_plen gr 0 len))] ->
    rw_cells ctasegs mY (spa + 96) [C8 (wz (D + go_p gr))] -> rw_cells ctasegs mY TLC [C1 vb; CB 31 jt] ->
    @implAp (push AR f 2) _
      ((let p := go_p gr in
        let inf := Z.testbit (go_ret gr) 0 in
        let cst := negb (Z.land (go_ret gr) 32 =? 0) in
        let plen := if inf then len - p else go_len gr in
        if cst then
          ' (b, r) <- CtModel.collect (CtModel.ct_fuel d) d CtModel.buf0 p plen inf 0 ;;
          match r with
          | None => afree_opt (option_map fst (CtModel.bm_data b)) ;;; aret None
          | Some _ =>
              let l := CtModel.bm_len b in
              b2 <- CtModel.buf_grow_clean b (l + 1) ;;
              blk <- amalloc SZ_ASN1_STRING ;;
              aret (Some (CtModel.mkOct blk (CtModel.bm_data b2) l (firstn (Z.to_nat l) (CtModel.bm_bytes b2))))
          end
        else
          blk <- amalloc SZ_ASN1_STRING ;;
          dp <- amalloc_crypto plen ;;
          aret (Some (CtModel.mkOct blk (option_map (fun q => (q, plen)) dp) plen (CtWire.slice d p plen)))) stY)
      ΣY POST
      (exr_ms EX_CT_RET (Z_to_bv 64 EX_CT_RET) x5 x6 x7 (Z_to_bv 64 1) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 0) x28 x29 x30 x31 FY fcY mY).
  Proof.
    intros until vb. intros XF LI HCX AXY EG ETAG ECLS HPIC HPPC HTLCY. ctx.
    pose proof XF as (AGFc & UWc & FRLAc & F104c & F120c & FRLBc & FRHc & HFCc & HBUFc & HOPPc & HPVc).
    pose proof CELLS as (_ & _ & _ & _ & _ & _ & _ & _ & DOT & DVT & _).
    pose proof col_consts as (KC1 & KC2 & KC3 & KC4 & KC5 & KC6 & KC7).
    kitp (@oinv_call (push AR f 2)) qfc qb mc OC. pose proof (OC _ _ _ _ _ _ _ LI) as (HEAPY & STY & _ & _ & _ & _ & MIY & _). replace (bv_unsigned sp + (spa - bv_unsigned sp)) with spa in STY by (clear; lia).
    (* [comment removed for export] *)
    assert (NXS : forall A n a, (spa + 120 <= A \/ A + n <= spa + 96 \/ (spa + 104 <= A /\ A + n <= spa + 110)) -> spa <= A -> A <= a < A + n ->
                  ~ rin_ivs [(spa + 110, spa + 110 + 10); (spa + 96, spa + 96 + 8); (TLC, TLC + 32)] a).
    { intros A n a W SA Ha HIN. cbn [rin_ivs fst snd] in HIN. clear - W SA Ha HIN BT1 BT2 BT4 CEIL LO ESS SPAL. plia. }
    assert (NXF : forall a, f <= a < f + 248 -> ~ rin_ivs [(spa + 110, spa + 110 + 10); (spa + 96, spa + 96 + 8); (TLC, TLC + 32)] a).
    { intros a Ha HIN. cbn [rin_ivs fst snd] in HIN. clear - Ha HIN OT BT1 BT2 G3 CEIL LO ESS SPAL. plia. }
    assert (NXQ : forall a, OPP <= a < OPP + 8 -> ~ rin_ivs [(spa + 110, spa + 110 + 10); (spa + 96, spa + 96 + 8); (TLC, TLC + 32)] a).
    { intros a Ha HIN. cbn [rin_ivs fst snd] in HIN. clear - Ha HIN DOT BQ1 BQ2 BQ4 CEIL LO ESS SPAL. plia. }
    assert (NXV : forall a, PV <= a < PV + 8 -> ~ rin_ivs [(spa + 110, spa + 110 + 10); (spa + 96, spa + 96 + 8); (TLC, TLC + 32)] a).
    { intros a Ha HIN. cbn [rin_ivs fst snd] in HIN. clear - Ha HIN DVT BV1 BV2 BV4 CEIL LO ESS SPAL. plia. }
    Local Ltac kp2 AXY H NX WH := apply (exo_keep _ _ [] _ _ _ _ _ AXY) in H; [| NX| WH].
    kp2 AXY FRLAc ltac:(intros a Ha; apply (NXS spa 96 a); [right; left; clear; lia| clear; lia| cbn in Ha; exact Ha]) ltac:(left; cbn; clear - SPAH TOP; unfold USTACK_TOP in *; lia).
    kp2 AXY F104c ltac:(intros a Ha; apply (NXS (spa + 104) 6 a); [right; right; clear; lia| clear; lia| cbn in Ha; exact Ha]) ltac:(left; cbn; clear - SPAH TOP; unfold USTACK_TOP in *; lia).
    kp2 AXY F120c ltac:(intros a Ha; apply (NXS (spa + 120) 8 a); [left; clear; lia| clear; lia| cbn in Ha; exact Ha]) ltac:(left; cbn; clear - SPAH TOP; unfold USTACK_TOP in *; lia).
    kp2 AXY FRLBc ltac:(intros a Ha; cbn [cells_size csize Nat.add] in Ha; rewrite ?Nat2Z.inj_add in Ha; apply (NXS (spa + 128) (40 + Z.of_nat g) a); [left; clear; lia| clear; lia| clear - Ha; lia])
                  ltac:(left; cbn [cells_size csize Nat.add]; rewrite ?Nat2Z.inj_add; clear - SPAH TOP GSZ; unfold USTACK_TOP in *; lia).
    kp2 AXY FRHc ltac:(intros a Ha; apply (NXS (bv_unsigned sp + -16) 16 a); [left; clear - SPAH; lia| clear - SPAH; lia| cbn in Ha; exact Ha]) ltac:(left; cbn; clear - SPAH TOP; unfold USTACK_TOP in *; lia).
    kp2 AXY HFCc ltac:(intros a Ha; apply NXF; cbn in Ha; clear - Ha; lia) ltac:(right; left; cbn; clear; lia).
    kp2 AXY HBUFc ltac:(intros a Ha; apply NXF; cbn in Ha; clear - Ha; lia) ltac:(right; right; left; cbn; clear; lia).
    kp2 AXY HOPPc ltac:(intros a Ha; apply NXQ; cbn in Ha; exact Ha) ltac:(do 3 right; left; split; [reflexivity| reflexivity]).
    kp2 AXY HPVc ltac:(intros a Ha; apply NXV; cbn in Ha; exact Ha) ltac:(do 4 right; left; split; [reflexivity| reflexivity]).
    pose proof (exo_keep_uw _ _ [] _ _ _ AXY ltac:(intros a HIN; cbn [rin_ivs fst snd] in HIN; clear - HIN BT1 BT2 BT4 CEIL LO ESS SPAL SPAH; plia) UWc) as UWY.
    (* [comment removed for export] *)
    lazymatch type of HPIC with rw_cells _ _ _ [?c1; ?c2; ?c3] => change [c1; c2; c3] with ([c1] ++ [c2] ++ [c3]) in HPIC end.
    apply rw_cells_app in HPIC as [HINF HPIC]. apply rw_cells_app in HPIC as [HCST HPLEN].
    cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add app] in HCST, HPLEN.
    replace (spa + 110 + 1) with (spa + 111) in HCST by (clear; lia). replace (spa + 110 + 1 + 1) with (spa + 112) in HPLEN by (clear; lia).
    unfold CtColP.W_check_tlen_gen.tlen_plen in HPLEN. rewrite Z.sub_0_r in HPLEN.
    pose proof (go_ret_cases d 0 len) as RC. cbv zeta in RC. fold gr in RC.
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    clear NXS NXF NXQ NXV. hide OD. hide OQ. hide OV. hide OT. hide BD5. hide BQ5. hide BV5. hide BT5. hide G5. hide FSH. hide DOT. hide DVT. hide AXY. hide RC.
    pose proof (munch_refl (@nil (Z * Z)) mY) as MU. pose proof (wmono_refl ctasegs mY) as WM.
    unfold exr_ms, EX_CT_RET. unfold MallocRep.wz in *. apply implAp_from_evt.
    step. step. step. if_false. step. if_true.
    step. rewrite (sx32_small V_ASN1_OCTET_STRING) by (unfold V_ASN1_OCTET_STRING; clear; lia). step. step. step.
    unfold V_ASN1_OCTET_STRING. step. if_cases KU; zc KU; [| exfalso; clear - KU; lia]. clear KU.
    step. step. if_cases K3; zc K3; [| exfalso; clear - K3; lia]. clear K3.
    step. rewrite (zxb_lit (Z.land (go_ret gr) 32)) by (clear - RC; unhide RC; pose proof (land_32_cases (go_ret gr)) as [-> | ->]; lia).
    cbv zeta. pose proof (land_32_cases (go_ret gr)) as [L0|L32].
    - (* [comment removed for export] *)
      rewrite L0. step. if_true. setreg 2%Z (Z_to_bv 64 spa) ltac:(f_equal; clear; lia). apply evt_done. cbn [Z.eqb negb].
      eapply (HPRIM qfc qb mc); [exact L0|]. unfold exd_facts.
      repeat match goal with |- _ /\ _ => split end;
        first [exact AGFc| exact LI| exact HCX| exact UWY| exact FRLAc| exact HPPC| exact F104c| exact HINF| exact HCST| exact HPLEN| exact F120c| exact FRLBc
              | exact FRHc| exact HFCc| exact HBUFc| exact HOPPc| exact HPVc| exact HTLCY| exact EG| exact ETAG| exact ECLS| exact SAVJ].
    - (* [comment removed for export] *)
      rewrite L32. step. if_false. step. step. if_false. step. step. step. step. if_true. setreg 2%Z (Z_to_bv 64 spa) ltac:(f_equal; clear; lia). apply evt_done. cbn [Z.eqb negb].
      eapply (HCONS qfc qb mc); [rewrite L32; clear; lia|]. unfold exd_facts.
      repeat match goal with |- _ /\ _ => split end;
        first [exact AGFc| exact LI| exact HCX| exact UWY| exact FRLAc| exact HPPC| exact F104c| exact HINF| exact HCST| exact HPLEN| exact F120c| exact FRLBc
              | exact FRHc| exact HFCc| exact HBUFc| exact HOPPc| exact HPVc| exact HTLCY| exact EG| exact ETAG| exact ECLS| exact SAVJ].
  Qed.
End Body.
End WithRT.
