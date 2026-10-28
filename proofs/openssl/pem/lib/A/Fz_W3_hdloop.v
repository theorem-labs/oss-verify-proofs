(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Common Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac ImageA RzCPS NodesA SysStep Arr FarCall.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import StrFun.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Str_tac Startup_glue Th_kit Fz_T_kit.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow RT_cg IcptSpec.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface D_defs D_kit D_agree D_clx R_cache_defs PLayout I_lkit I_ut RT_iface_pem D_libiface_pem Fz_kit Fz_ckit Fz_env Fz_M_free Fz_M_secure Fz_W1_defs Fz_W1_pploc Fz_W1_grow Fz_icpt0 Fz_M_malloc Fz_W3_iface Fz_W3_defs Fz_W3_lems Fz_W3_endl Fz_W3_hd1 Fz_W3_hdg Fz_W3_hd2 Fz_W3_puts.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CHdloop.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Variable GOBJ : Z -> Z -> Prop.
Hypothesis AFP : art_facts_pem RT GOBJ.
Hypothesis MCHR : memchr_icontract RT.
Hypothesis SLC : strlen_icontract RT.
Hypothesis SNC : strncmp_icontract RT.
Hypothesis SNC0 : strncmp0_icontract RT.
Hypothesis GO_end : GOBJ LIT_ENDSTR LIT_ENDSTR_SZ.
Hypothesis GO_tail : GOBJ LIT_TAIL LIT_TAIL_SZ.
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
Hypothesis C_BP : bio_puts_stmt RT FZ_SITES FZ_CALLS.
Hypothesis C_PF : pem_free_stmt RT libenv FZ_SITES FZ_CALLS.
Hypothesis TAILP : TAIL_stmt RT libenv errst_at_rest errst_live FZ_SITES FZ_CALLS.
Hypothesis H_R2 : RAISE2_stmt RT libenv errst_at_rest errst_live FZ_SITES FZ_CALLS.
Hypothesis H_F2 : FREE2_stmt RT libenv errst_at_rest errst_live FZ_SITES FZ_CALLS.

Local Notation HD_atI := (HD_at RT libenv errst_at_rest errst_live FZ_SITES FZ_CALLS).

Theorem HD_proof : forall N, HD_atI N.
Proof.
  assert (STEP : forall N, HD_atI (N - 1) -> HD_atI N).
  { intros N IH.
    apply (HD1_proof RT AF GOBJ AFP MCHR SNC GO_end libenv libenv_fp libenv_agree libenv_fp_where errst_at_rest errst_live errst_fp errst_rest_agree errst_fp_where FZ_SITES FZ_CALLS N).
    apply (HD2_proof RT AF GOBJ AFP C_SAN SNC GO_end libenv libenv_fp libenv_agree libenv_fp_where errst_at_rest errst_live errst_fp errst_rest_agree errst_fp_where FZ_SITES FZ_CALLS H_R2 N).
    - exact (ENDLINE_proof RT AF GOBJ AFP SLC SNC SNC0 GO_tail libenv libenv_fp libenv_agree libenv_fp_where errst_at_rest errst_live errst_fp errst_rest_agree errst_fp_where FZ_SITES FZ_CALLS C_PF TAILP H_R2 N).
    - exact (GETS2_proof RT AF GOBJ AFP libenv libenv_fp libenv_agree libenv_fp_where errst_at_rest errst_live errst_fp errst_rest_agree errst_fp_where FZ_SITES FZ_CALLS C_BG H_R2 N IH).
    - apply (PUTS_proof RT AF GOBJ AFP libenv libenv_fp libenv_agree libenv_fp_where errst_at_rest errst_live errst_fp errst_rest_agree errst_fp_where FZ_SITES FZ_CALLS C_BP H_R2 H_F2 N).
      exact (GETS1_proof RT AF GOBJ AFP libenv libenv_fp libenv_agree libenv_fp_where errst_at_rest errst_live errst_fp errst_rest_agree errst_fp_where FZ_SITES FZ_CALLS C_BG H_R2 N IH). }
  assert (NEG : forall N, N < 0 -> HD_atI N).
  { intros N HN en Σ m off crem lrem j0 pv endv x1 x2 gap hj lenv j1 tav j2 bmv j3 F fc xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 t3 t4 t5 t6
           LB2 namev nn hBv dBv tmp len got prev bn bs KX KY methX methY lenX maxX lenY maxY MEAS INV. exfalso.
    pose proof INV as (COM & _). pose proof COM as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & OFF & _). clear - MEAS OFF HN. lia. }
  assert (ALL : forall n : nat, HD_atI (Z.of_nat n - 1)).
  { induction n as [|n IHn]; [apply NEG; lia|]. apply STEP. replace (Z.of_nat (S n) - 1 - 1) with (Z.of_nat n - 1) by lia. exact IHn. }
  intros N. destruct (Z_lt_le_dec N 0) as [HN|HN]; [apply NEG; exact HN|].
  replace N with (Z.of_nat (Z.to_nat (N + 1)) - 1) by lia. apply ALL.
Qed.
End CHdloop.
