(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Common Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac ImageA RzCPS Arr.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow RT_cg.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface RT_iface_pem D_defs D_libiface_pem D_agree D_clx PLayout Fz_kit Fz_ckit Fz_env Fz_icpt0 Fz_M_malloc Fz_M_zalloc Fz_M_free Fz_M_cleanse Fz_M_clear_free Fz_M_clear_realloc Fz_M_secure Fz_W1_defs Fz_W1_misc Fz_W1_new Fz_W1_free Fz_W1_puts Fz_W1_writec Fz_W1_writes Fz_W1_gets Fz_W1_read Fz_W5_glx Fz_W5_icb Fz_W5_gsi Fz_W5_gsi0 Fz_W5_vset Fz_W5_new Fz_W5_debug Fz_W5_seterr Fz_W5_clear Fz_W5_env Fz_W5_newc Fz_W5_debugc Fz_W5_error Fz_W5_clearc Fz_W2_exdl Fz_W2_exdc Fz_W2_bnew Fz_W2_bfree Fz_W2_ctrl Fz_W2_ctrlf Fz_W2_getsf Fz_W2_putsf Fz_W2_readf Fz_W2_writef Fz_W3_iface Fz_W3_defs Fz_W3_inik Fz_W3_pmem Fz_W3_sanitize Fz_W3_evp Fz_W3_top Fz_W7_defs Fz_W7_inv Fz_W7_top Fz_libA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Notation wz := (Z_to_bv 64) (only parsing).

(* [comment removed for export] *)
Definition CALLA_GOBJS : list (Z * Z) :=
  [(LIT_BEGIN, LIT_BEGIN_SZ); (LIT_TAIL, LIT_TAIL_SZ); (LIT_ENDSTR, LIT_ENDSTR_SZ); (LIT_B64TAB, LIT_B64TAB_SZ); (LIT_FILE, LIT_FILE_SZ); (LIT_FUNC, LIT_FUNC_SZ);
   (LIT_GETNAME, LIT_GETNAME_SZ); (LIT_GETHD, LIT_GETHD_SZ); (CTYPE_TAB, 256); (LIT_BOM, 3); (M_MEM_A, 112); (M_SECMEM_A, 112);
   (DC_CTX, 328); (DC_KEY, 4); (G_TL_MASTER_KEY, 4); (G_IC_OPTSDONE, 8)].

(* [comment removed for export] *)
Definition CALLA_SITES : list (Z * Z) :=
  W7_SITES_OWN ++ PEM_SITES ++ BNX_SITES ++ BFX_SITES ++ BP_SITES ++ BW_SITES ++ CLR_SITES ++ DBG_SITES ++ NEW_SITES.
Definition CALLA_CALLS : list (Z * Z) :=
  W7_CALLS_ALL ++ PEM_CALLS ++ BNX_CALLS ++ BFX_CALLS ++ BP_CALLS ++ BW_CALLS ++ CLR_CALLS ++ DBG_CALLS ++ NEW_CALLS.

Section CallA.
Variable RT : rt_sig.
Variable GOBJ : Z -> Z -> Prop.
Hypothesis CR : cli_rt RT GOBJ.
Hypothesis SNC0 : strncmp0_icontract RT.
Hypothesis TSD : forall Σ m, ART RT Σ m -> rw_cells asegs m 0xba3e98 [C8 (Z_to_bv 64 0xbc5298)].
Hypothesis ERRNO_ACC : forall Σ m, ART RT Σ m -> acc asegs m 0xba3e48 8.
Hypothesis HGO : Forall (fun p => GOBJ (fst p) (snd p)) CALLA_GOBJS.
Variables FZ_SITES FZ_CALLS : list (Z * Z).
Hypothesis HCG : cg_sub CALLA_SITES CALLA_CALLS FZ_SITES FZ_CALLS.

(* [comment removed for export] *)
(* [comment removed for export] *)
Let AF : art_facts RT := cr_af CR.
Let AFP : art_facts_pem RT GOBJ := cr_afp CR.
Let RC : rt_contracts RT := cr_rc CR.
Let RCP : rt_contracts_pem RT := cr_rcp CR.
Let MAL := rc_malloc RT RC.
Let FRC := rc_free RT RC.
Let FRN := rc_free_null RT RC.
Let MCP := rc_asan_memcpy RT RC.
Let MSI := rc_asan_memset RT RC.
Let MSP := rc_memset RT RC.
Let MCH := rc_memchr RT RC.
Let SLC := rc_strlen RT RC.
Let SNC := rc_strncmp RT RC.
Let SM0 := rc_stack_malloc_0 RT RC.
Let SM1 := rc_stack_malloc_1 RT RC.
Let SM2 := rc_stack_malloc_2 RT RC.
Let MCMP := rcp_memcmp RT RCP.
Let SCPY := rcp_strcpy RT RCP.
Let MMV := rcp_asan_memmove RT RCP.

(* [comment removed for export] *)
Local Ltac go_in := lazymatch goal with |- GOBJ ?b ?s => exact (proj1 (Forall_forall _ _) HGO (b, s) ltac:(unfold CALLA_GOBJS; cbn [In]; repeat (first [left; reflexivity | right]))) end.
Lemma GO_begin : GOBJ LIT_BEGIN LIT_BEGIN_SZ. Proof using HGO. go_in. Qed.
Lemma GO_tail : GOBJ LIT_TAIL LIT_TAIL_SZ. Proof using HGO. go_in. Qed.
Lemma GO_end : GOBJ LIT_ENDSTR LIT_ENDSTR_SZ. Proof using HGO. go_in. Qed.
Lemma GO_b64 : GOBJ LIT_B64TAB LIT_B64TAB_SZ. Proof using HGO. go_in. Qed.
Lemma GO_file : GOBJ LIT_FILE LIT_FILE_SZ. Proof using HGO. go_in. Qed.
Lemma GO_func : GOBJ LIT_FUNC LIT_FUNC_SZ. Proof using HGO. go_in. Qed.
Lemma GO_getname : GOBJ LIT_GETNAME LIT_GETNAME_SZ. Proof using HGO. go_in. Qed.
Lemma GO_gethd : GOBJ LIT_GETHD LIT_GETHD_SZ. Proof using HGO. go_in. Qed.
Lemma GO_ctype : GOBJ CTYPE_TAB 256. Proof using HGO. go_in. Qed.
Lemma GO_bom : GOBJ LIT_BOM 3. Proof using HGO. go_in. Qed.
Lemma GO_memmeth : GOBJ M_MEM_A 112. Proof using HGO. go_in. Qed.
Lemma GO_secmeth : GOBJ M_SECMEM_A 112. Proof using HGO. go_in. Qed.
Lemma GO_memmeth' : GOBJ MEM_METHOD 112. Proof using HGO. exact GO_memmeth. Qed.
Lemma GO_DC : GOBJ DC_CTX 328. Proof using HGO. go_in. Qed.
Lemma GO_DCKEY : GOBJ DC_KEY 4. Proof using HGO. go_in. Qed.
Lemma GO_mkey : GOBJ G_TL_MASTER_KEY 4. Proof using HGO. go_in. Qed.
Lemma GO_optsdone : GOBJ G_IC_OPTSDONE 8. Proof using HGO. go_in. Qed.

(* [comment removed for export] *)
Local Ltac cg_in := apply (cg_sub_trans _ _ CALLA_SITES CALLA_CALLS _ _); [apply cg_sub_lit; vm_compute; reflexivity| exact HCG].
Lemma HCG_W7 : cg_sub W7_SITES_OWN W7_CALLS_ALL FZ_SITES FZ_CALLS. Proof using HCG. cg_in. Qed.
Lemma HCG_PEM : cg_sub PEM_SITES PEM_CALLS FZ_SITES FZ_CALLS. Proof using HCG. cg_in. Qed.
Lemma HCG_BNX : cg_sub BNX_SITES BNX_CALLS FZ_SITES FZ_CALLS. Proof using HCG. cg_in. Qed.
Lemma HCG_BFX : cg_sub BFX_SITES BFX_CALLS FZ_SITES FZ_CALLS. Proof using HCG. cg_in. Qed.
Lemma HCG_BP : cg_sub BP_SITES BP_CALLS FZ_SITES FZ_CALLS. Proof using HCG. cg_in. Qed.
Lemma HCG_BW : cg_sub BW_SITES BW_CALLS FZ_SITES FZ_CALLS. Proof using HCG. cg_in. Qed.
Lemma HCG_CLR : cg_sub CLR_SITES CLR_CALLS FZ_SITES FZ_CALLS. Proof using HCG. cg_in. Qed.
Lemma HCG_DBG : cg_sub DBG_SITES DBG_CALLS FZ_SITES FZ_CALLS. Proof using HCG. cg_in. Qed.
Lemma HCG_NEW : cg_sub NEW_SITES NEW_CALLS FZ_SITES FZ_CALLS. Proof using HCG. cg_in. Qed.
Lemma HCG_PM : cg_sub [(SITE_cm_malloc, e_CRYPTO_malloc)] [(SITE_cm_malloc, e_malloc)] FZ_SITES FZ_CALLS. Proof using HCG. cg_in. Qed.
Lemma HCG_EVP : cg_sub [(SITE_cz_malloc, e_CRYPTO_zalloc); (SITE_cm_malloc, e_CRYPTO_malloc)] [(SITE_cz_malloc, e_CRYPTO_malloc); (SITE_cm_malloc, e_malloc)] FZ_SITES FZ_CALLS.
Proof using HCG. cg_in. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma CM : crypto_malloc_stmt RT. Proof using CR. exact (crypto_malloc_cps RT AF MAL). Qed.
Lemma CME : crypto_malloc_env_stmt RT. Proof using CR. exact (crypto_malloc_env RT AF CM). Qed.
Lemma CZ : crypto_zalloc_stmt RT. Proof using CR. exact (crypto_zalloc_cps RT AF CM MSI). Qed.
Lemma CZE : crypto_zalloc_env_stmt RT. Proof using CR. exact (crypto_zalloc_env RT AF CZ). Qed.
Lemma CFR : crypto_free_env_stmt RT. Proof using CR. exact (crypto_free_cps RT AF FRC). Qed.
Lemma CFN : crypto_free_null_env_stmt RT. Proof using CR. exact (crypto_free_null_cps RT AF FRN). Qed.
Lemma CCL : openssl_cleanse_env_stmt RT. Proof using CR. exact (openssl_cleanse_cps RT AF MSP). Qed.
Lemma CCF : crypto_clear_free_env_stmt RT. Proof using CR. exact (crypto_clear_free_cps RT AF FRC CCL). Qed.
Lemma CCR : crypto_clear_realloc_env_stmt RT. Proof using CR. exact (crypto_clear_realloc_cps RT AF CME MCP CCF). Qed.
Lemma CSM : crypto_secure_malloc_env_stmt RT. Proof using CR. exact (crypto_secure_malloc_cps RT AF CME). Qed.
Lemma CSF : crypto_secure_free_env_stmt RT. Proof using CR. exact (crypto_secure_free_cps RT AF CFR). Qed.
Lemma CSCF : crypto_secure_clear_free_env_stmt RT. Proof using CR. exact (crypto_secure_clear_free_cps RT AF CFR CCL). Qed.

(* [comment removed for export] *)
Lemma MNEW : mem_init_at_stmt RT e_mem_new (fun _ => Z_to_bv 64 0) (fun Σ ra => In (bv_unsigned ra, e_mem_init) (cg_call (rt_cg RT Σ))).
Proof using CR. exact (mem_new_cps RT AF GOBJ AFP CZE MCP). Qed.
Lemma SNEW : mem_init_at_stmt RT e_secmem_new (fun _ => Z_to_bv 64 1) (fun Σ ra => In (bv_unsigned ra, e_mem_init) (cg_call (rt_cg RT Σ))).
Proof using CR. exact (secmem_new_cps RT AF GOBJ AFP CZE MCP). Qed.
Lemma MF : mem_free_stmt RT. Proof using CR. exact (mem_free_cps RT AF GOBJ AFP CFR CCF). Qed.
Lemma MFS : mem_free_sec_stmt RT. Proof using CR. exact (mem_free_sec_cps RT AF GOBJ AFP CFR CSCF). Qed.
Lemma PFW : puts_fitw_stmt RT. Proof using CR. exact (puts_fitw_cps RT AF GOBJ AFP SLC MMV MSI MCP). Qed.
Lemma PRE : puts_re_stmt RT. Proof using CR. exact (puts_re_cps RT AF GOBJ AFP SLC MMV MSI MCP CME CCR). Qed.
Lemma PRS : puts_res_stmt RT. Proof using CR. exact (puts_res_cps RT AF GOBJ AFP SLC MMV MSI MCP CSM CSCF). Qed.
Lemma PZ : puts_zero_stmt RT. Proof using CR. exact (puts_zero_cps RT AF GOBJ AFP SLC). Qed.
Lemma WFW : write_fitw_stmt RT. Proof using CR. exact (write_fitw_cps RT AF GOBJ AFP MMV MSI MCP). Qed.
Lemma WRE : write_re_stmt RT. Proof using CR. exact (write_re_cps RT AF GOBJ AFP MMV MSI MCP CME CCR). Qed.
Lemma WRS : write_res_stmt RT. Proof using CR. exact (write_res_cps RT AF GOBJ AFP MMV MSI MCP CSM CSCF). Qed.
Lemma GD : gets_data_stmt RT. Proof using CR. exact (gets_data_cps RT AF GOBJ AFP MCP). Qed.
Lemma GE : gets_empty_stmt RT. Proof using CR. exact (gets_empty_cps RT AF GOBJ AFP). Qed.
Lemma RD : read_data_stmt RT. Proof using CR. exact (read_data_cps RT AF GOBJ AFP MCP). Qed.

(* [comment removed for export] *)
Lemma ICB : init_crypto_base_stmt RT. Proof using CR HGO. exact (init_crypto_base_cps RT AF GOBJ AFP SM0 GO_optsdone). Qed.
Lemma GSI : get_state_steady_stmt RT. Proof using CR HGO TSD ERRNO_ACC. exact (get_state_steady_cps RT AF GOBJ AFP ICB TSD ERRNO_ACC GO_mkey). Qed.
Lemma GSI0 : get_state_steady0_stmt RT. Proof using CR HGO TSD. exact (get_state_steady0_cps RT AF GOBJ AFP ICB TSD GO_mkey). Qed.
Lemma ENEW : Fz_W5_new.err_new_stmt RT. Proof using CR HGO TSD ERRNO_ACC. exact (err_new_cps RT AF GOBJ AFP GSI CFN). Qed.
Lemma EDBG : Fz_W5_debug.err_set_debug_stmt RT GOBJ. Proof using CR HGO TSD ERRNO_ACC. exact (err_set_debug_cps RT AF GOBJ AFP SLC SCPY GSI CFN CME). Qed.
Lemma VSE : err_vset_error_stmt RT. Proof using CR HGO TSD ERRNO_ACC. exact (err_vset_error_cps RT AF GOBJ AFP GSI). Qed.
Lemma ESE : Fz_W5_seterr.err_set_error_stmt RT. Proof using CR HGO TSD ERRNO_ACC. exact (err_set_error_cps RT AF SM0 VSE). Qed.
Lemma ECLR : err_clear_error_stmt RT. Proof using CR HGO TSD. exact (err_clear_error_cps RT AF GOBJ AFP GSI0 CFN CFR). Qed.
Lemma ENEWR : A.Fz_W3_iface.err_new_rest_stmt RT libenv errst_at_rest errst_live FZ_SITES FZ_CALLS.
Proof using CR HGO TSD ERRNO_ACC HCG. exact (err_new_rest_proof RT AF GOBJ AFP ENEW FZ_SITES FZ_CALLS HCG_NEW). Qed.
Lemma EDBGR : A.Fz_W3_iface.err_set_debug_stmt RT GOBJ libenv errst_live FZ_SITES FZ_CALLS.
Proof using CR HGO TSD ERRNO_ACC HCG. exact (err_set_debug_proof RT AF GOBJ AFP EDBG FZ_SITES FZ_CALLS HCG_DBG). Qed.
Lemma ESER : A.Fz_W3_iface.err_set_error_stmt RT libenv errst_live FZ_SITES FZ_CALLS.
Proof using CR HGO TSD ERRNO_ACC. exact (err_set_error_proof RT AF GOBJ AFP ESE FZ_SITES FZ_CALLS). Qed.
Lemma ECS : A.Fz_W3_iface.err_clear_steady_stmt RT libenv errst_at_rest errst_live FZ_SITES FZ_CALLS.
Proof using CR HGO TSD HCG. exact (err_clear_steady_proof RT AF GOBJ AFP ECLR FZ_SITES FZ_CALLS HCG_CLR). Qed.

(* [comment removed for export] *)
Lemma NEWEX : T_newex_stmt RT. Proof using CR HGO TSD. exact (T_newex_cps RT AF GOBJ AFP SM2 CFN TSD GO_DC GO_DCKEY). Qed.
Lemma FREEEX : T_freeex_stmt RT. Proof using CR HGO TSD. exact (T_freeex_cps RT AF GOBJ AFP SM2 CFN MSI TSD GO_DC GO_DCKEY). Qed.
Lemma BNEW : bio_new_mem_stmt RT libenv FZ_SITES FZ_CALLS.
Proof using CR HGO TSD HCG. exact (bio_new_mem_proof RT AF GOBJ AFP CZE NEWEX MNEW SNEW GO_memmeth GO_secmeth libenv libenv_fp libenv_fp_where libenv_exd FZ_SITES FZ_CALLS HCG_BNX). Qed.
Lemma BFREE : bio_free_mem_stmt RT libenv FZ_SITES FZ_CALLS.
Proof using CR HGO TSD HCG. exact (bio_free_mem_proof RT AF GOBJ AFP MF MFS FREEEX CFR GO_memmeth GO_secmeth libenv libenv_fp libenv_fp_where libenv_exd FZ_SITES FZ_CALLS HCG_BFX). Qed.
Lemma BFN : bio_free_null_stmt RT. Proof using CR. exact (bio_free_null_proof RT AF). Qed.
Lemma BG : bio_gets_stmt RT. Proof using CR HGO. exact (bio_gets_proof RT AF GOBJ AFP SM0 GO_memmeth GO_secmeth GD GE). Qed.
Lemma BP : bio_puts_stmt RT FZ_SITES FZ_CALLS. Proof using CR HGO HCG. exact (bio_puts_proof RT AF GOBJ AFP SM0 GO_memmeth GO_secmeth PFW PRE PRS PZ FZ_SITES FZ_CALLS HCG_BP). Qed.
Lemma BCP : A.Fz_W3_iface.bio_ctrl_ptr_stmt RT. Proof using CR HGO. exact (bio_ctrl_ptr_proof RT AF GOBJ AFP MMV GO_memmeth' GO_secmeth). Qed.
Lemma BCI : A.Fz_W3_iface.bio_ctrl_info_stmt RT. Proof using CR HGO. exact (bio_ctrl_info_proof RT AF GOBJ AFP GO_memmeth' GO_secmeth). Qed.
Lemma BRD : bio_read_stmt RT. Proof using CR HGO. exact (bio_read_proof RT AF GOBJ AFP SM0 GO_memmeth GO_secmeth RD). Qed.
Lemma BW0 : bio_write0_stmt RT. Proof using CR. exact (bio_write0_proof RT AF). Qed.
Lemma BWG : bio_writeg_stmt RT FZ_SITES FZ_CALLS. Proof using CR HGO HCG. exact (bio_writeg_proof RT AF GOBJ AFP SM0 GO_memmeth GO_secmeth WFW WRE WRS FZ_SITES FZ_CALLS HCG_BW). Qed.

(* [comment removed for export] *)
Lemma PM : pem_malloc_stmt RT libenv FZ_SITES FZ_CALLS.
Proof using CR HCG. exact (pem_malloc_proof RT AF libenv libenv_fp libenv_agree libenv_fp_where FZ_SITES FZ_CALLS CME CSM HCG_PM). Qed.
Lemma PM0 : pem_malloc0_stmt RT libenv. Proof using CR. exact (pem_malloc0_proof RT AF libenv libenv_fp libenv_agree libenv_fp_where). Qed.
Lemma PF : pem_free_stmt RT libenv FZ_SITES FZ_CALLS. Proof using CR. exact (pem_free_proof RT AF libenv libenv_fp libenv_agree libenv_fp_where FZ_SITES FZ_CALLS CFR CSCF). Qed.
Lemma PFN : pem_free_null_stmt RT libenv FZ_SITES FZ_CALLS. Proof using CR. exact (pem_free_null_proof RT AF libenv libenv_fp libenv_agree libenv_fp_where FZ_SITES FZ_CALLS CFN). Qed.
Lemma SAN : sanitize_line_stmt RT. Proof using CR HGO. exact (sanitize_line_proof RT AF GOBJ AFP MCMP MMV GO_ctype GO_bom). Qed.
Lemma ECN : evp_ctx_new_stmt RT FZ_SITES FZ_CALLS. Proof using CR HCG. exact (evp_ctx_new_proof RT AF FZ_SITES FZ_CALLS CZE HCG_EVP). Qed.
Lemma ECF : evp_ctx_free_stmt RT FZ_SITES FZ_CALLS. Proof using CR. exact (evp_ctx_free_proof RT AF FZ_SITES FZ_CALLS CFR). Qed.
Lemma ECFN : evp_ctx_free_null_stmt RT FZ_SITES FZ_CALLS. Proof using CR. exact (evp_ctx_free_null_proof RT AF FZ_SITES FZ_CALLS CFN). Qed.

Theorem PEMR : pem_read_bio_stmt RT libenv errst_at_rest errst_live FZ_SITES FZ_CALLS.
Proof using CR SNC0 TSD ERRNO_ACC HGO HCG.
  exact (pem_read_bio_proof RT AF GOBJ AFP SLC SNC SNC0 MCH MCP GO_begin GO_tail GO_end GO_b64 GO_file GO_func GO_getname GO_gethd SM1
           libenv libenv_fp libenv_agree libenv_fp_where errst_at_rest errst_live errst_fp errst_rest_agree errst_live_agree errst_fp_where errst_rest_live
           FZ_SITES FZ_CALLS HCG_PEM BFN PM PM0 PF PFN SAN ENEWR EDBGR ESER BNEW BFREE BG BP BCP BCI BRD ECN ECF ECFN).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma libenv_errno : forall m LBL E, libenv m LBL E -> exists v, rw_cells asegs m (errno_cell (wz D_defs.TP_A)) [C4 v].
Proof.
  intros m LBL E LE. destruct (libenv_core_errno m LBL E LE) as (e & He). exists e.
  unfold errno_cell, D_defs.TP_A. rewrite unsigned_lit by lia. exact He.
Qed.

Theorem W7_one_A : fuzz_one_cps RT LIB_A FZ_SITES FZ_CALLS.
Proof using CR SNC0 TSD ERRNO_ACC HGO HCG.
  exact (fuzz_one_A RT AF GOBJ AFP SM2 SLC libenv libenv_fp libenv_agree libenv_fp_where libenv_errno
           errst_at_rest errst_live errst_fp errst_rest_agree errst_live_agree errst_fp_where FZ_SITES FZ_CALLS HCG_W7
           BNEW BWG BW0 PEMR BFREE ECS CFR CFN CSF LIB_A REST_A REST_A_fp REST_A_agree REST_A_fp_where W7_OPEN_A W7_CLOSE_A).
Qed.
End CallA.
