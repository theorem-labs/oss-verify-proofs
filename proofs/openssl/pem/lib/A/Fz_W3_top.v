(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow RT_cg IcptSpec.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface D_defs D_kit D_agree D_clx R_cache_defs PLayout I_lkit I_ut RT_iface_pem D_libiface_pem Fz_kit Fz_ckit Fz_env Fz_icpt0 Fz_W1_defs Fz_W3_iface Fz_W3_defs Fz_W3_lits Fz_W3_inik Fz_W3_end Fz_W3_tail Fz_W3_rzt Fz_W3_dec Fz_W3_ini Fz_W3_tl Fz_W3_free2 Fz_W3_endl Fz_W3_hdloop Fz_W3_free1 Fz_W3_ngets Fz_W3_name Fz_W3_gnloop Fz_W3_j0r Fz_W3_j0g Fz_W3_j0n Fz_W3_j0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section W3.
  Variable RT : rt_sig.
  Hypothesis AF : art_facts RT.
  Variable GOBJ : Z -> Z -> Prop.
  Hypothesis AFP : art_facts_pem RT GOBJ.
  (* [comment removed for export] *)
  Hypothesis SLC : strlen_icontract RT.
  Hypothesis SNC : strncmp_icontract RT.
  Hypothesis SNC0 : strncmp0_icontract RT.
  Hypothesis MCH : memchr_icontract RT.
  Hypothesis MCP : memcpy_icontract RT e_asan_memcpy.
  (* [comment removed for export] *)
  Hypothesis GO_begin : GOBJ LIT_BEGIN LIT_BEGIN_SZ.
  Hypothesis GO_tail : GOBJ LIT_TAIL LIT_TAIL_SZ.
  Hypothesis GO_end : GOBJ LIT_ENDSTR LIT_ENDSTR_SZ.
  Hypothesis GO_b64 : GOBJ LIT_B64TAB LIT_B64TAB_SZ.
  Hypothesis GO_file : GOBJ LIT_FILE LIT_FILE_SZ.
  Hypothesis GO_func : GOBJ LIT_FUNC LIT_FUNC_SZ.
  Hypothesis GO_getname : GOBJ LIT_GETNAME LIT_GETNAME_SZ.
  Hypothesis GO_gethd : GOBJ LIT_GETHD LIT_GETHD_SZ.
  (* [comment removed for export] *)
  Hypothesis SM1 : stack_malloc_contract RT 1.
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
  Hypothesis HCG : cg_sub PEM_SITES PEM_CALLS FZ_SITES FZ_CALLS.
  (* [comment removed for export] *)
  Local Notation E11 x := (x errst_at_rest errst_live errst_fp errst_rest_agree errst_live_agree errst_fp_where errst_rest_live FZ_SITES FZ_CALLS) (only parsing).
  Local Notation E10 x := (x errst_at_rest errst_live errst_fp errst_rest_agree errst_live_agree errst_fp_where FZ_SITES FZ_CALLS) (only parsing).
  Local Notation E9 x := (x errst_at_rest errst_live errst_fp errst_rest_agree errst_fp_where FZ_SITES FZ_CALLS) (only parsing).
  Local Notation E3 x := (x errst_at_rest errst_live FZ_SITES FZ_CALLS) (only parsing).
  Local Notation L4 x := (x libenv libenv_fp libenv_agree libenv_fp_where) (only parsing).
  Local Notation B4 x := (x RT AF GOBJ AFP) (only parsing).

  Theorem pem_read_bio_proof : bio_free_null_stmt RT -> pem_read_bio_deps RT GOBJ libenv errst_at_rest errst_live FZ_SITES FZ_CALLS.
  Proof.
    intros BFN PM PM0 PF PFN SAN ENEW EDBG ESET BN BF BG BP BCP BCI BRD ECN ECF ECFN.
    pose proof (E11 (L4 (B4 END0_proof)) ECFN PFN BFN) as END0P.
    pose proof (E11 (L4 (B4 END_proof)) ECF ECFN PF PFN BF) as ENDP.
    pose proof (E11 (L4 (B4 RELOAD_proof)) ECF ECFN PF PFN BF) as RLP.
    pose proof (E11 (L4 (B4 FREE1X_proof)) ECF ECFN PF PFN BF) as FXP.
    pose proof (E9 (L4 (B4 OUTFREE_proof)) PF PFN RLP) as OUTP.
    pose proof (E3 (L4 (B4 RZT_proof)) ENEW GO_file GO_func EDBG ESET RLP) as RZTP.
    pose proof (E9 (L4 (B4 DEC_proof)) BCI PM PM0 BRD RLP OUTP) as DECP.
    pose proof (E9 (L4 (B4 INI_proof GO_b64)) RZTP DECP) as INIP.
    pose proof (E9 (L4 (B4 TAIL_proof)) BCP ECN ENDP INIP) as TAILP.
    pose proof (E10 (L4 (B4 FREE2_proof)) PF FXP) as FREE2P.
    pose proof (E10 (L4 (B4 RAISE2_proof)) PF ENEW GO_file GO_gethd EDBG ESET FXP) as RAISE2P.
    pose proof (E9 (L4 (B4 LFREE_proof)) PF TAILP) as LFREEP.
    pose proof (E9 (L4 (B4 ENDLINE_proof SLC SNC SNC0 GO_tail)) PF TAILP RAISE2P) as ENDLP.
    pose proof (E9 (L4 (B4 HD_proof MCH SLC SNC SNC0 GO_end GO_tail)) SAN BG BP PF TAILP RAISE2P FREE2P) as HDP.
    pose proof (E10 (L4 (B4 FREE1_proof)) PF FXP) as FREE1P.
    pose proof (E10 (L4 (B4 RAISE1_proof)) PF ENEW GO_file GO_getname EDBG ESET FXP) as RAISE1P.
    pose proof (E9 (L4 (B4 NGETS_proof)) BG RAISE2P HDP) as NGETSP.
    pose proof (E9 (L4 (B4 NAME_proof)) MCP PM PF NGETSP) as NAMEP.
    pose proof (E9 (L4 (B4 GN_proof)) SAN BG SNC GO_begin GO_tail NAMEP RAISE1P) as GNP.
    pose proof (E9 (L4 (B4 J0G_proof)) GNP) as J0GP.
    pose proof (E9 (L4 (B4 J0N_proof)) BN PM BG RAISE1P J0GP) as J0NP.
    pose proof (E3 (L4 (B4 RAISE0_proof)) ENEW GO_file GO_func EDBG ESET END0P) as RAISE0P.
    exact (E9 (L4 (B4 J0_proof)) SM1 HCG RAISE0P J0NP).
  Qed.
End W3.
