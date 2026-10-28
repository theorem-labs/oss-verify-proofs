(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude DecodeC Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import MallocBlocks Malloc_iface ClientOwn LhRep.
From OssFuzzTheorems.Proofs.openssl.pem.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface RMalloc_ifaceP.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import Prelim STree Malloc Monad Stdio Harness Target Prog StrFun.
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Layout Fz_iface Driver_iface Drv_kit Fz_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Th_kit Fz_T_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_T_ekit. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Str_cpy. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_M_malloc Fz_M_zalloc Fz_M_free Fz_M_secure
     Fz_M_clear_free Fz_M_clear_realloc Fz_W1_defs Fz_W1_sync Fz_W1_growc Fz_W1_writec Fz_W1_read Fz_W3_iface Fz_W2_rep Fz_W3_defs Fz_W3_end Fz_W3_tail Fz_W3_dec
     Fz_W3_endl Fz_W3_gn Fz_W3_gng.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section W3. Context {CE__ : Ceiling} {RN__ : RunRnd}.
  Variable libenv : mem -> list block -> Z -> Prop.
  Variable libenv_fp : list block -> Z -> Prop.
  Hypothesis libenv_agree : forall m m' LBL E, libenv m LBL E -> agree_on (libenv_fp LBL) m m' -> libenv m' LBL E.
  Hypothesis libenv_fp_where : forall LBL a, libenv_fp LBL a ->
    (0x2c0000 <= a < 0x353000 /\ ~ ralloc_static a /\ a <> LX_FLAGS) \/ (exists b, In b LBL /\ blk_addr b <= a < blk_addr b + blk_size b).
  Variable errst_at_rest : Z -> list block -> mem -> Prop.
  Variable errst_live : Z -> Z -> Z -> list block -> mem -> Prop.
  Variable errst_fp : Z -> list block -> Z -> Prop.
  Hypothesis errst_rest_agree : forall m m' E strs, errst_at_rest E strs m -> agree_on (errst_fp E strs) m m' -> errst_at_rest E strs m'.
  Hypothesis errst_live_agree : forall m m' E top bot strs, errst_live E top bot strs m -> agree_on (errst_fp E strs) m m' -> errst_live E top bot strs m'.
  Hypothesis errst_fp_where : forall E strs a, errst_fp E strs a -> (E <= a < E + 904) \/ (exists b, In b strs /\ blk_addr b <= a < blk_addr b + blk_size b).
  Hypothesis errst_rest_live : forall m E, errst_at_rest E [] m -> errst_live E 0 0 [] m.

  Theorem GN_proof :
    sanitize_line_stmt -> bio_gets_stmt -> NAME_stmt libenv errst_at_rest errst_live -> RAISE1_stmt libenv errst_at_rest errst_live ->
    forall N, GN_at libenv errst_at_rest errst_live N.
  Proof.
    intros SAN BG NAMEP RAISEP.
    assert (STEP : forall N, GN_at libenv errst_at_rest errst_live (N - 1) -> GN_at libenv errst_at_rest errst_live N).
    { intros N IH.
      eapply (GN1_proof libenv libenv_fp libenv_agree libenv_fp_where errst_at_rest errst_live errst_fp errst_rest_agree errst_fp_where); [exact SAN| exact NAMEP|].
      eapply (GNG_proof libenv libenv_fp libenv_agree libenv_fp_where errst_at_rest errst_live errst_fp errst_rest_agree errst_fp_where); [exact BG| exact RAISEP| exact IH]. }
    assert (NEG : forall N, N < 0 -> GN_at libenv errst_at_rest errst_live N).
    { intros N HN. unfold GN_at. intros. exfalso.
      lazymatch goal with M : e_blen ?en - ?off <= N, C : pem_com _ ?en _ _ _ _ _ ?off _ _ _ _ |- _ =>
        pose proof C as (_ & _ & _ & _ & _ & _ & _ & _ & OFF & _); clear - M OFF HN; lia end. }
    assert (ALL : forall n : nat, GN_at libenv errst_at_rest errst_live (Z.of_nat n - 1)).
    { induction n as [|n IHn]; [apply NEG; lia|]. apply STEP. replace (Z.of_nat (S n) - 1 - 1) with (Z.of_nat n - 1) by lia. exact IHn. }
    intros N. destruct (Z_lt_le_dec N 0) as [HN|HN]; [apply NEG; exact HN|].
    replace N with (Z.of_nat (Z.to_nat (N + 1)) - 1) by lia. apply ALL.
  Qed.
End W3.
