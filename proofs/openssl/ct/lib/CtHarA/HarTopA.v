(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim STree Malloc Stdio Prog LibProg ProgG CtSizes CtWire CtTime CtModel ApBase ApState ApErr ApParse ApBridge.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge Nodes Cells Mem RzCPS. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout RT_iface RT_client_kit D_defs D_libiface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtKitA Require Import RT_iface2 LibKitA ARun BnHeapA BnRepDefs BnRepA ImplA BnIfaceA W_cryptoA UnwindA UnwindRecA EdgesA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtFrameA Require Import AFrameKit.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require Import ApRepDefs ApRep ApIface ApFrame CtFuzzStmtA I_strcpyA W_err_clearA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtSctA Require Import SctRepA SctStmtA SctStmtA2 W_sct_freeA W_sct_list_freeA O2iSctStmtB O2iSctListStmtB W_o2i_sctA W_o2i_sct_listA W_d2i_sct_listA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtColA Require Import ColDefsA ColBudgetA ExoBudgetA W_d2iA_stmt W_d2i_octetA W_d2iA_exprim.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtEncA Require Import EncStmtA W_i2o_list_lenA W_i2d_sct_listA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import I_vsnstmt.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtSctA Require Import RtGenStmtA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtPrnA Require Import PrnStmtA W_sct_list_printA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtHarA Require Import HarStmtA W_bio_nullA W_fuzz_oneA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section Open.
Context {AR : ARun} {UK : UnwindKit} {BE : BnEdges} {URC : UnwindRec ASN1_COLLECT_A ASN1_COLLECT_REC_RA 6} {UR : UnwindRec I2O_SCT_LIST_A IOL_NESTED_RET IOL_REC_DEPTH}.

(* [comment removed for export] *)
Hypothesis STRCPY : strcpy_icontract (@ar_RT AR).

(* [comment removed for export] *)
Hypothesis PFC : printf_contracts (@ar_RT AR).
Hypothesis REA : realloc_contract_gen (@ar_RT AR).

(* [comment removed for export] *)
Definition HO2I (AR' : ARun) (S : strcpy_icontract (@ar_RT AR')) : @o2i_sct_specA2 AR' UK O2I_SCT_STACK_A O2I_SCT_COST_A O2I_SCT_FRAMES_A :=
  @o2i_sct_walkA AR' UK BE S.

(* [comment removed for export] *)
Definition HO2IL (AR' : ARun) (S : strcpy_icontract (@ar_RT AR')) (R : realloc_contract_gen (@ar_RT AR')) :
  @o2i_sct_list_specA2 AR' UK O2I_SCT_LIST_STACK_A (fun _ => O2I_SCT_LIST_COST_A) O2I_SCT_LIST_FRAMES_A :=
  @o2i_sct_list_walkA AR' UK BE S R (HO2I AR' S).

(* [comment removed for export] *)
Lemma I2D_A : forall f, @i2d_sct_list_specA (push AR f 1) UK IDL_STACK_A IDL_COST_A IDL_FRAMES_A.
Proof. intros f. exact (@i2d_sct_list_walkA (push AR f 1) UK BE UR STRCPY). Qed.

Lemma bud_i2d : 0 <= IDL_STACK_A <= CT_FUZZ_STACK_A - HAR_FRAME_A /\ 0 <= IDL_FRAMES_A <= CT_FUZZ_FRAMES_A - 1 /\ (forall n, 0 <= n < 2^26 -> 0 <= IDL_COST_A n <= 2^28).
Proof.
  destruct idl_budgets as (E1 & E2 & E3). rewrite E1, E2.
  replace (CT_FUZZ_STACK_A - HAR_FRAME_A) with 130928 by reflexivity. replace (CT_FUZZ_FRAMES_A - 1) with 510 by reflexivity.
  split; [lia|]. split; [lia|]. intros n Hn. rewrite E3. lia.
Qed.

(* [comment removed for export] *)
Definition HEXPRIM_B (AR' : ARun) (S : strcpy_icontract (@ar_RT AR')) : @exprim_oct_specA AR' UK EXO_STACK_A EXO_COST_A EXO_FRAMES_A :=
  @exprim_oct_walkA AR' UK BE URC S.
Definition HD2I_B (AR' : ARun) (S : strcpy_icontract (@ar_RT AR')) : @d2i_octet_specA AR' UK D2I_OCTET_STACK_A D2I_OCTET_COST_A D2I_OCTET_FRAMES_A :=
  @d2i_octet_walkA AR' UK BE S HEXPRIM_B.

(* [comment removed for export] *)
Lemma D2I_A : forall f, @d2i_sct_list_specA2 (push AR f 1) UK D2I_SCT_LIST_STACK_A D2I_SCT_LIST_COST_A D2I_SCT_LIST_FRAMES_A.
Proof.
  intros f. exact (@d2i_sct_list_walkA (push AR f 1) UK BE (fun f' => HD2I_B (push (push AR f 1) f' 1) STRCPY) (fun f' => HO2IL (push (push AR f 1) f' 1) STRCPY REA)).
  (* [comment removed for export] *)
Qed.
Lemma bud_d2i : 0 <= D2I_SCT_LIST_STACK_A <= CT_FUZZ_STACK_A - HAR_FRAME_A /\ 0 <= D2I_SCT_LIST_FRAMES_A <= CT_FUZZ_FRAMES_A - 1
                /\ (forall n, 0 <= n < 2^26 -> 0 <= D2I_SCT_LIST_COST_A n <= 2^30 + 2^27).
Proof. exact D2I_SCT_LIST_BUD_A. Qed.

(* [comment removed for export] *)
Lemma PRN_A : forall f, @SCT_LIST_print_specA (push AR f 1) UK SCT_LIST_PRINT_STACK_A SCT_LIST_PRINT_COST_A SCT_LIST_PRINT_FRAMES_A.
Proof. intros f. exact (@SCT_LIST_print_walkA (push AR f 1) UK BE PFC REA). Qed.

Lemma bud_prn : 0 <= SCT_LIST_PRINT_STACK_A <= CT_FUZZ_STACK_A - HAR_FRAME_A /\ 0 <= SCT_LIST_PRINT_FRAMES_A <= CT_FUZZ_FRAMES_A - 1
                /\ (forall n, 0 <= n < 2^26 -> 0 <= SCT_LIST_PRINT_COST_A n <= 2^28).
Proof.
  replace (CT_FUZZ_STACK_A - HAR_FRAME_A) with 130928 by reflexivity. replace (CT_FUZZ_FRAMES_A - 1) with 510 by reflexivity.
  replace SCT_LIST_PRINT_STACK_A with 66496 by (vm_compute; reflexivity). unfold SCT_LIST_PRINT_FRAMES_A, SCT_LIST_PRINT_COST_A.
  split; [lia|]. split; [lia|]. intros n Hn. lia.
Qed.

Theorem ct_fuzz_walkA_open : @ct_fuzz_stmtA AR UK.
Proof.
  pose proof bud_prn as BUD_PRN. pose proof bud_d2i as BUD_D2I. pose proof bud_i2d as BUD_I2D.
  apply (@fuzz_walkA AR UK BE D2I_SCT_LIST_STACK_A D2I_SCT_LIST_COST_A D2I_SCT_LIST_FRAMES_A SCT_LIST_PRINT_STACK_A SCT_LIST_PRINT_COST_A SCT_LIST_PRINT_FRAMES_A IDL_STACK_A IDL_COST_A IDL_FRAMES_A SK_POP_FREE_STACK_A).
  - destruct BUD_D2I as (S1 & F1 & C1). destruct BUD_PRN as (S2 & F2 & C2). destruct BUD_I2D as (S3 & F3 & C3).
    unfold har_budgetsA. repeat split; try assumption; try (intros; eauto; fail).
    all: try (apply C1; assumption). all: try (apply C2; assumption). all: try (apply C3; assumption).
    all: try (destruct S1; assumption). all: try (destruct S2; assumption). all: try (destruct S3; assumption).
    all: try (destruct F1; assumption). all: try (destruct F2; assumption). all: try (destruct F3; assumption).
    all: unfold SK_POP_FREE_STACK_A, SCT_FREE_STACK_A, CRYPTO_FREE_STACK, RT_STACK, CT_FUZZ_STACK_A, FUZZ_STACK, HAR_FRAME_A; lia.
  - unfold har_hypsA. split; [exact D2I_A|]. split; [exact PRN_A|]. split; [exact I2D_A|].
    split; [intros f; exact (@SCT_LIST_free_walkA (push AR f 1) UK BE)|].
    split; [intros f; exact (@BIO_new_null_walkA (push AR f 1) UK BE)|].
    split; [intros f; exact (@BIO_free_null_walkA (push AR f 1) UK BE)|].
    intros f; exact (@ERR_clear_error_walkA (push AR f 1) UK BE).
Qed.
End Open.
