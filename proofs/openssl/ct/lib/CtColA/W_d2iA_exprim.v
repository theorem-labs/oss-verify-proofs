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
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtColA Require Import ColBudgetA ColDefsA CtlStmtA W_check_tlen_genA W_check_tlen_allA W_bufmemA W_collectA W_d2iA_stmt W_d2iA_exprim_ctx W_d2iA_exprim_tail W_d2iA_exprim_call W_d2iA_exprim_front ExoBudgetA W_d2iA_exprim_prim W_d2iA_exprim_cons.
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

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Open Scope am_scope.

Section WithRT.
Context {AR : ARun} {UK : UnwindKit} {BE : BnEdges} {UR : UnwindRec ASN1_COLLECT_A ASN1_COLLECT_REC_RA 6}.
Local Notation RT := (@ar_RT AR).

Section Walk.
  Hypothesis STRCPY : strcpy_icontract RT.
  (* [comment removed for export] *)
  Let HCTL : forall AR' : ARun, strcpy_icontract (@ar_RT AR') -> @check_tlen_gen_specA AR' UK :=
    fun AR' S => @check_tlen_gen_of_cpsA AR' UK (@check_tlen_cps_walkA AR' UK BE S).

  Theorem exprim_oct_walkA : exprim_oct_specA EXO_STACK_A EXO_COST_A EXO_FRAMES_A.
  Proof.
    unfold exprim_oct_specA. intros until j31. intros PRE0 ETP UW CTX NE KOW KIDS ADR CELLS LEN1 -> -> -> -> -> -> -> ->.
    pose proof PRE0 as (HEAP & AS & IDS & DC & ST & CEIL & LOSP & TOP & AL16 & MI & CRED & FRM).
    pose proof exo_budgets as (EB1 & EB2 & EB3). pose proof col_consts as (KC1 & KC2 & KC3 & KC4 & KC5 & KC6 & KC7).
    unfold MallocRep.wz. intros X Φ Dl SAFE LINK.
    eapply (adep_pro_cps _) with (lo := lo) (OW := OW) (LB := LB);
      [exact HEAP| exact ST| exact CEIL| rewrite EB1 in LOSP; unfold ADEP_FRAME, RT_STACK; clear - LOSP; lia| exact TOP| exact AL16| exact MI| exact ETP
      | rewrite EB2 in FRM; cbn [length]; clear - FRM; lia| rewrite EB3 in CRED; clear - CRED LEN1; pose proof (Z.pow_pos_nonneg 2 19); lia|].
    intros Σ1 m3 f spa g junk gj ra' t0' t1' t2' a7' t3' t4' t5' t6' F' fc' j0 j8 j16 j24 j32 j48 j64 j72 j80 j96 j104 j112 j120 j128 j136 j144 jf24 jf32 jf40 jf64 jf65 jf80 jf112 jst
           HEAP3 FRESH GEO CR1 EL1 ST3 MI3 AGF FRL FRH FRF FRS SPA32 SPAL SPAH GSZ SAVJ.
    eapply (@implAp_elim (push AR f 2) _ (d2i_exprim d (zlength d) st)); [| exact SAFE| exact LINK| exact EL1].
    eapply (exo_front STRCPY HCTL EXO_STACK_A EXO_COST_A EXO_FRAMES_A);
      [exact PRE0| exact UW| exact CTX| exact KOW| exact KIDS| exact CELLS| exact LEN1| exact HEAP3| exact FRESH| exact GEO| exact CR1| exact ST3| exact MI3| exact AGF
      | exact SPA32| exact SPAL| exact SPAH| exact GSZ| exact SAVJ
      | rewrite EB1, KC1; unfold ADEP_FRAME; clear; lia| rewrite EB2, KC4; clear; lia| rewrite EB3; clear; lia
      | intros; eapply (exo_prim EXO_STACK_A EXO_COST_A EXO_FRAMES_A); try eassumption;
          [rewrite EB1, KC1; unfold ADEP_FRAME; clear; lia| rewrite EB3; clear; lia]
      | intros; eapply (exo_cons STRCPY HCTL EXO_STACK_A EXO_COST_A EXO_FRAMES_A); try eassumption;
          [rewrite EB1, KC1; unfold ADEP_FRAME; clear; lia| rewrite EB2, KC4; clear; lia| rewrite EB3; clear; lia]
      | exact FRL| exact FRH| unfold ex_frameA; exact FRF| exact FRS].
  Qed.

  Goal True. idtac "Assumptions of exprim_oct_walkA:". Print Assumptions exprim_oct_walkA. exact I. Qed.
End Walk.
End WithRT.
