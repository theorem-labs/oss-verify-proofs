(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Common Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac ImageA RzCPS Arr.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow RT_cg.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface RT_iface_pem D_defs D_libiface_pem D_agree D_clx PLayout Fz_kit Fz_ckit Fz_chk Fz_fkit Fz_env Fz_M_free Fz_M_secure Fz_W1_defs Fz_W3_iface Fz_W7_defs Fz_W7_segs Fz_W7_inv Fz_W7_calls Fz_W7_x Fz_W7_f Fz_W7_p Fz_W7_e.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Notation wz := (Z_to_bv 64) (only parsing).

Section W7A.
  Variable RT : rt_sig.
  Hypothesis AF : art_facts RT.
  Variable GOBJ : Z -> Z -> Prop.
  Hypothesis AFP : art_facts_pem RT GOBJ.
  (* [comment removed for export] *)
  Hypothesis SM2 : stack_malloc_contract RT 2.
  Hypothesis SLC : strlen_icontract RT.
  (* [comment removed for export] *)
  Variable libenv : mem -> list (Z * Z) -> Z -> Prop.
  Variable libenv_fp : list (Z * Z) -> Z -> Prop.
  Hypothesis libenv_agree : forall m m' LBL E, libenv m LBL E -> agree_on (libenv_fp LBL) m m' -> libenv m' LBL E.
  Hypothesis libenv_fp_where : forall LBL a, libenv_fp LBL a -> (in_ranges LIB_W a /\ client_static a /\ ~ cl_cell a) \/ in_live LBL a.
  Hypothesis libenv_errno : forall m LBL E, libenv m LBL E -> exists v, rw_cells asegs m (errno_cell (wz TP_A)) [C4 v].
  Variable errst_at_rest : Z -> list (Z * Z) -> mem -> Prop.
  Variable errst_live : Z -> Z -> Z -> list (Z * Z) -> mem -> Prop.
  Variable errst_fp : Z -> list (Z * Z) -> Z -> Prop.
  Hypothesis errst_rest_agree : forall m m' E strs, errst_at_rest E strs m -> agree_on (errst_fp E strs) m m' -> errst_at_rest E strs m'.
  Hypothesis errst_live_agree : forall m m' E top bot strs, errst_live E top bot strs m -> agree_on (errst_fp E strs) m m' -> errst_live E top bot strs m'.
  Hypothesis errst_fp_where : forall E strs a, errst_fp E strs a -> (E <= a < E + 904) \/ in_live strs a.
  (* [comment removed for export] *)
  Variables FZ_SITES FZ_CALLS : list (Z * Z).
  Hypothesis HCG_W7 : cg_sub W7_SITES_OWN W7_CALLS_ALL FZ_SITES FZ_CALLS.
  (* [comment removed for export] *)
  Hypothesis C_BNEW : bio_new_mem_stmt RT libenv FZ_SITES FZ_CALLS.
  Hypothesis C_BW : bio_writeg_stmt RT FZ_SITES FZ_CALLS.
  Hypothesis C_B0 : bio_write0_stmt RT.
  Hypothesis C_PEM : pem_read_bio_stmt RT libenv errst_at_rest errst_live FZ_SITES FZ_CALLS.
  Hypothesis C_BF : bio_free_mem_stmt RT libenv FZ_SITES FZ_CALLS.
  Hypothesis C_EC : err_clear_steady_stmt RT libenv errst_at_rest errst_live FZ_SITES FZ_CALLS.
  Hypothesis C_FR : crypto_free_env_stmt RT.
  Hypothesis C_FN : crypto_free_null_env_stmt RT.
  Hypothesis C_SF : crypto_secure_free_env_stmt RT.
  (* [comment removed for export] *)
  Variable LIB : list (Z * Z) -> mem -> Prop.
  Variable REST : mem -> Prop.
  Variable REST_fp : Z -> Prop.
  Hypothesis REST_agree : forall m m', REST m -> agree_on REST_fp m m' -> REST m'.
  Hypothesis REST_fp_where : forall a, REST_fp a -> client_static a /\ outside LIB_W a /\ ~ cl_cell a.
  Hypothesis W7_OPEN : forall CL m (g : word) (v : word), LIB CL m -> ro_cells asegs m ssp_guard [C8 g] -> rw_cells asegs m (errno_cell (wz TP_A)) [C4 v] ->
      cl_env m (Z_to_bv 8 1) g /\ sec_off m /\ exists (E : Z) (LBL : list (Z * Z)),
      libenv m LBL E /\ errst_at_rest E [] m /\ In (E, 904) CL /\ incl_live LBL CL /\ ~ In (E, 904) LBL /\ REST m.
  Hypothesis W7_CLOSE : forall CL m (canary : word) E LBL, In (E, 904) CL -> incl_live LBL CL -> ~ In (E, 904) LBL ->
      cl_env m (Z_to_bv 8 1) canary -> sec_off m -> libenv m LBL E -> errst_at_rest E [] m -> REST m -> LIB CL m.

  Theorem fuzz_one_A : fuzz_one_cps RT LIB FZ_SITES FZ_CALLS.
  Proof.
    assert (EXITP : EXIT_stmt RT libenv errst_at_rest FZ_SITES FZ_CALLS LIB REST) by (eapply EXIT_proof; eassumption).
    assert (F7P : F7_stmt RT libenv errst_live FZ_SITES FZ_CALLS LIB REST) by (eapply F7_proof; eassumption).
    assert (PW4P : PW4_stmt RT libenv errst_live FZ_SITES FZ_CALLS LIB REST) by (eapply PW4_proof; eassumption).
    assert (PW3P : PW3_stmt RT libenv errst_live FZ_SITES FZ_CALLS LIB REST) by (eapply PW3_proof; eassumption).
    assert (P7P : P7_stmt RT libenv errst_live FZ_SITES FZ_CALLS LIB REST) by (eapply P7_proof; eassumption).
    eapply E7_proof; eassumption.
  Qed.
End W7A.
