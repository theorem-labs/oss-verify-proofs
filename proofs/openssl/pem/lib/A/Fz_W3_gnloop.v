(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Common Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac ImageA RzCPS NodesA SysStep Arr FarCall.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import StoreFast.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import StrFun.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Str_tac Startup_glue Th_kit Fz_T_kit.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Fz_W3_gnlem.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import IcptSpec Shadow RT_cg.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface D_defs D_kit D_agree D_clx R_cache_defs PLayout I_lkit I_ut RT_iface_pem D_libiface_pem Fz_kit Fz_ckit Fz_chk Fz_fkit Fz_mkit Fz_env Fz_M_free Fz_M_secure Fz_W1_defs Fz_W1_pploc Fz_W3_iface Fz_W3_defs Fz_W1_grow Fz_W3_lems Fz_W3_aux Fz_W3_aux2 Fz_W3_aux3 Fz_W3_lits Fz_W3_gnlem Fz_W3_gng Fz_W3_gn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

Section CGnloop.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Variable GOBJ : Z -> Z -> Prop.
Hypothesis AFP : art_facts_pem RT GOBJ.
Variable libenv : mem -> list (Z * Z) -> Z -> Prop.
Variable libenv_fp : list (Z * Z) -> Z -> Prop.
Hypothesis libenv_agree : forall m m' LBL E, libenv m LBL E -> agree_on (libenv_fp LBL) m m' -> libenv m' LBL E.
Hypothesis libenv_fp_where : forall LBL a, libenv_fp LBL a -> (in_ranges LIB_W a /\ client_static a /\ ~ cl_cell a) \/ in_live LBL a.
Variable errst_at_rest : Z -> list (Z * Z) -> mem -> Prop.
Variable errst_live : Z -> Z -> Z -> list (Z * Z) -> mem -> Prop.
Variable errst_fp : Z -> list (Z * Z) -> Z -> Prop.
Hypothesis errst_rest_agree : forall m m' E strs, errst_at_rest E strs m -> agree_on (errst_fp E strs) m m' -> errst_at_rest E strs m'.
Hypothesis errst_live_agree : forall m m' E top bot strs, errst_live E top bot strs m -> agree_on (errst_fp E strs) m m' -> errst_live E top bot strs m'.
Hypothesis errst_fp_where : forall E strs a, errst_fp E strs a -> (E <= a < E + 904) \/ in_live strs a.
Hypothesis errst_rest_live : forall m E, errst_at_rest E [] m -> errst_live E 0 0 [] m.
Variables FZ_SITES FZ_CALLS : list (Z * Z).
Hypothesis C_SAN : sanitize_line_stmt RT.
Hypothesis C_BG : bio_gets_stmt RT.
Hypothesis SNC : strncmp_icontract RT.
Hypothesis GO_begin : GOBJ LIT_BEGIN 12.
Hypothesis GO_tail : GOBJ LIT_TAIL 7.
Hypothesis NAMEP : NAME_stmt RT libenv errst_at_rest errst_live FZ_SITES FZ_CALLS.
Hypothesis RS1 : RAISE1_stmt RT libenv errst_at_rest errst_live FZ_SITES FZ_CALLS.

Theorem GN_proof : forall N, GN_at RT libenv errst_at_rest errst_live FZ_SITES FZ_CALLS N.
Proof.
  assert (STEP : forall N, GN_at RT libenv errst_at_rest errst_live FZ_SITES FZ_CALLS (N - 1) -> GN_at RT libenv errst_at_rest errst_live FZ_SITES FZ_CALLS N).
  { intros N IH.
    apply (GN1_proof RT AF GOBJ AFP libenv libenv_fp libenv_agree libenv_fp_where errst_at_rest errst_live errst_fp errst_rest_agree errst_fp_where FZ_SITES FZ_CALLS C_SAN SNC GO_begin GO_tail N NAMEP).
    exact (GNG_proof RT AF GOBJ AFP libenv libenv_fp libenv_agree libenv_fp_where errst_at_rest errst_live errst_fp errst_rest_agree errst_fp_where FZ_SITES FZ_CALLS C_BG N RS1 IH). }
  assert (NEG : forall N, N < 0 -> GN_at RT libenv errst_at_rest errst_live FZ_SITES FZ_CALLS N).
  { intros N HN. unfold GN_at. intros. exfalso.
    lazymatch goal with M : e_blen RT ?en - ?off <= N, C : pem_com RT libenv FZ_SITES FZ_CALLS ?en _ _ ?off _ _ _ |- _ =>
      pose proof C as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & OFF & _); clear - M OFF HN; lia end. }
  assert (ALL : forall n : nat, GN_at RT libenv errst_at_rest errst_live FZ_SITES FZ_CALLS (Z.of_nat n - 1)).
  { induction n as [|n IHn]; [apply NEG; lia|]. apply STEP. replace (Z.of_nat (S n) - 1 - 1) with (Z.of_nat n - 1) by lia. exact IHn. }
  intros N. destruct (Z_lt_le_dec N 0) as [HN|HN]; [apply NEG; exact HN|].
  replace N with (Z.of_nat (Z.to_nat (N + 1)) - 1) by lia. apply ALL.
Qed.

Theorem GNG_all : forall N, GNG_at RT libenv errst_at_rest errst_live FZ_SITES FZ_CALLS N.
Proof.
  intros N. exact (GNG_proof RT AF GOBJ AFP libenv libenv_fp libenv_agree libenv_fp_where errst_at_rest errst_live errst_fp errst_rest_agree errst_fp_where FZ_SITES FZ_CALLS C_BG N RS1 (GN_proof (N - 1))).
Qed.
End CGnloop.
