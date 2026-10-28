(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Common Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import PropExec MState Mem Frame Cells Step Arr Exec ImageA RzCPS NodesA.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import Prelim Canon Stdio Prog.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow MainSkel.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface D_iface D_defs D_kit D_libiface D_libiface_pem D_clx D_usage D_open D_dir D_trpro D_file.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section MainA.
Variable RT : rt_sig.
Variable OUT_rep : stdout_st -> mem -> Prop.
Variable ERR_rep : mem -> Prop.
Variable IO_FP : list (Z * Z).
Variable XENV : mem -> Prop.
Variable XENV_FP : list (Z * Z).
Variable LIB : mem -> Prop.
Variable CG : cgraph.                (* [comment removed for export] *)
(* [comment removed for export] *)
Variable LIB0P : mem -> Prop.
Variable LIBP : list (Z * Z) -> mem -> Prop.
Variables FZ_SITES FZ_CALLS : list (Z * Z).
Variable argvb : list (list byte).
Variable fs : Fs.
Hypothesis AF : art_facts RT.
Hypothesis AF_DRV : forall Σ m, ART RT Σ m -> drv_consts m.
Hypothesis MAL : malloc_contract RT.
Hypothesis FRE : free_contract RT.
Hypothesis FRN : free_null_contract RT.
Hypothesis MCP : memcpy_icontract RT e_memcpy.
Hypothesis RFILE : read_icontract_file RT.
Hypothesis RDIR : read_icontract_dir RT.
Hypothesis FPR : fprintf_stderr_icontract RT OUT_rep ERR_rep IO_FP.
Hypothesis FWR : fwrite_stderr_icontract RT OUT_rep ERR_rep IO_FP.
Hypothesis VPR : vprintf_emit0_icontract RT OUT_rep ERR_rep IO_FP.
Hypothesis OPC : open_contract RT.
Hypothesis OPR : open_refused_contract RT.
Hypothesis CLS : close_contract RT.
Hypothesis EXC : exit_contract RT XENV OUT_rep ERR_rep.
Hypothesis INITC : fuzz_init_cps RT LIB0P LIBP FZ_SITES FZ_CALLS.
Hypothesis FUZZC : fuzz_one_cps RT LIBP FZ_SITES FZ_CALLS.
Hypothesis VARGV : valid_argv argvb.
Hypothesis OUT_loc : forall so, fp_local IO_FP (OUT_rep so).
Hypothesis ERR_loc : fp_local IO_FP ERR_rep.
Hypothesis XENV_loc : fp_local XENV_FP XENV.
Hypothesis LIB_loc : fp_local LIB_FP LIB.
Hypothesis IO_img : forall x, in_ranges IO_FP x -> client_static x /\ ~ drv_cell x /\ outside LIB_FP x.
Hypothesis XENV_img : forall x, in_ranges XENV_FP x -> client_static x /\ ~ drv_cell x /\ outside IO_FP x /\ outside LIB_FP x.
(* [comment removed for export] *)
Variable XENV' : mem -> Prop.
Hypothesis XENV'_loc : fp_local XENV_FP XENV'.
Hypothesis XENV_ax : forall m, XENV m -> exists fin p1 p2, ax_chunks false fin p1 p2 m.
Hypothesis XENV_libc : forall m, XENV m -> libc_cells m.
Hypothesis XENV_incb : forall m, XENV m -> rw_cells asegs m TR_INCB [C1 (Z_to_bv 8 0)].
Hypothesis XENV_step : forall m m', XENV m ->
  agree_on (fun x => in_ranges XENV_FP x /\ ~ (0xbc3f40 <= x < 0xbc3f70) /\ ~ (0xbc4060 <= x < 0xbc4070) /\ x <> TR_INCB) m m' ->
  (exists fin p1 p2, ax_chunks true fin p1 p2 m') -> rw_cells asegs m' TR_INCB [C1 (Z_to_bv 8 0)] -> XENV' m'.
Hypothesis XENV_fp_ax : forall x, (0xbc3f40 <= x < 0xbc3f70 \/ 0xbc4060 <= x < 0xbc4070 \/ x = TR_INCB) -> in_ranges XENV_FP x.
Hypothesis XENV'_ax : forall m, XENV' m -> exists fin p1 p2, ax_chunks true fin p1 p2 m.
Hypothesis XENV'_incb : forall m, XENV' m -> rw_cells asegs m TR_INCB [C1 (Z_to_bv 8 0)].
Hypothesis XENV'_upd : forall m m', XENV' m ->
  agree_on (fun x => in_ranges XENV_FP x /\ ~ (0xbc3f40 <= x < 0xbc3f70) /\ ~ (0xbc4060 <= x < 0xbc4070) /\ x <> TR_INCB) m m' ->
  (exists fin p1 p2, ax_chunks true fin p1 p2 m') -> rw_cells asegs m' TR_INCB [C1 (Z_to_bv 8 0)] -> XENV' m'.
Hypothesis EXC' : exit_contract RT XENV' OUT_rep ERR_rep.
Hypothesis LIB_pre : forall m, LIB m -> LIB0P m /\ rw_cells asegs m TR_INIT [C1 (Z_to_bv 8 0)].
Hypothesis LOC0 : lib0_local_d LIB0P.
Hypothesis LOCP : lib_local_d LIBP.
Hypothesis CGH : cg_has CG FZ_SITES FZ_CALLS.

Lemma length_argv_Z : forall (argv : list (list byte)), length (argv_Z argv) = length argv.
Proof. intros argv. unfold argv_Z. apply length_map. Qed.

Theorem main_realizesA : forall c, START RT OUT_rep ERR_rep XENV LIB CG argvb fs c -> realizes asegs c (canonT (argv_Z argvb) fs).
Proof using All.
  intros c HS.
  apply (main_realizes asegs (argv_Z argvb) fs (START RT OUT_rep ERR_rep XENV LIB CG argvb fs) (OPEN RT OUT_rep ERR_rep XENV LIB CG argvb fs)
           (FAILED RT OUT_rep ERR_rep XENV LIB CG argvb fs) (OPENED RT OUT_rep ERR_rep XENV LIB CG argvb fs) (EXIT fs)); [| | | | | | | | exact HS].
  - intros code c' (A & Pm & PM & HA & HPm & HPM).
    exact (ast_exit asegs SEGTOP_A asegs_wx asegs_below A Pm PM c' (Z_to_bv 64 code) fs HA HPm HPM).
  - intros HL. rewrite length_argv_Z in HL.
    exact (usage_cpsE RT OUT_rep ERR_rep IO_FP XENV XENV_FP LIB CG argvb fs AF AF_DRV FPR EXC VARGV OUT_loc ERR_loc XENV_loc LIB_loc
             IO_img XENV_img HL).
  - intros HL. rewrite length_argv_Z in HL.
    exact (to_open_cps RT OUT_rep ERR_rep IO_FP XENV XENV_FP LIB CG argvb fs AF OUT_loc ERR_loc XENV_loc LIB_loc IO_img XENV_img HL).
  - intros HL HCL. rewrite length_argv_Z in HL.
    exact (open_fail_cps RT OUT_rep ERR_rep IO_FP XENV XENV_FP LIB CG argvb fs AF AF_DRV OPR VARGV OUT_loc ERR_loc XENV_loc LIB_loc
             IO_img XENV_img HL HCL).
  - intros HL HCL. rewrite length_argv_Z in HL.
    exact (open_cps2 RT OUT_rep ERR_rep IO_FP XENV XENV_FP LIB CG argvb fs AF AF_DRV OPC VARGV OUT_loc ERR_loc XENV_loc LIB_loc
             IO_img XENV_img HL HCL).
  - intros HL. rewrite length_argv_Z in HL.
    exact (failed_cpsE RT OUT_rep ERR_rep IO_FP XENV XENV_FP LIB CG argvb fs AF AF_DRV FPR EXC VARGV OUT_loc ERR_loc XENV_loc LIB_loc
             IO_img XENV_img HL).
  - intros HL HCL. rewrite length_argv_Z in HL.
    exact (dir_cpsE RT OUT_rep ERR_rep IO_FP XENV XENV_FP LIB CG argvb fs AF AF_DRV MAL RDIR FPR EXC VARGV OUT_loc ERR_loc XENV_loc
             LIB_loc IO_img XENV_img HL HCL).
  - intros HL data HCL. rewrite length_argv_Z in HL.
    exact (file_cpsE RT OUT_rep ERR_rep IO_FP XENV XENV_FP LIB CG LIB0P LIBP FZ_SITES FZ_CALLS argvb fs AF AF_DRV CLS MAL FRE FRN MCP RFILE FPR FWR
             INITC FUZZC VPR EXC VARGV OUT_loc ERR_loc XENV_loc LIB_loc IO_img XENV_img
             XENV' XENV'_loc XENV_ax XENV_libc XENV_incb XENV_step XENV_fp_ax XENV'_ax XENV'_incb XENV'_upd EXC' LIB_pre LOC0 LOCP CGH HL data HCL).
Qed.

End MainA.

(* [comment removed for export] *)
