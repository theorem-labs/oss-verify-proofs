(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import PropExec MState Mem Frame Cells Step Arr Exec ImageA RzCPS NodesA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Spec Require Import Prelim Canon Stdio Prog.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A Require Import Shadow MainSkel.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import Layout RT_iface D_iface D_defs D_kit D_aex D_libiface D_clx D_usage D_open D_dir D_file X_aexdefs X_vecxdefs X_xdefs X_xiface Imp_libifaceA D_impkit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section MainA.
Variable RT : rt_sig.
Variable OUT_rep : stdout_st -> mem -> Prop.
Variable ERR_rep : mem -> Prop.
Variable IO_FP : list (Z * Z).
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
Hypothesis EXC : exit_contract_imp RT XENV_coreA OUT_rep ERR_rep imp_libA.
Hypothesis FUZZ : fuzz_one_cps_imp RT imp_libA.
Hypothesis VARGV : valid_argv argvb.
Hypothesis OUT_loc : forall so, fp_local IO_FP (OUT_rep so).
Hypothesis ERR_loc : fp_local IO_FP ERR_rep.
Hypothesis IO_img : forall x, in_ranges IO_FP x -> client_static x /\ ~ drv_cell x /\ outside LIB_FP x.
Hypothesis IO_img2 : forall x, in_ranges IO_FP x -> outside IMP_FP_A x /\ ~ in_ranges AEX_FPA x.
Hypothesis XENV_img : forall x, in_ranges XENV_FP0 x -> client_static x /\ ~ drv_cell x /\ outside IO_FP x /\ outside LIB_FP x.
Notation XENV := XENV0. Notation XENV_FP := XENV_FP0. Notation LIB := libN. Notation XENV_loc := XENV_laws0. Notation LIB_loc := libN_loc.

Lemma length_argv_Z : forall (argv : list (list byte)), length (argv_Z argv) = length argv.
Proof. intros argv. unfold argv_Z. apply length_map. Qed.

Theorem main_realizesA : forall c, START RT OUT_rep ERR_rep XENV0 libN argvb fs c -> realizes bsegs c (canonT (argv_Z argvb) fs).
Proof using All.
  pose proof (exit0_of_imp RT OUT_rep ERR_rep EXC) as EXC0.
  intros c HS.
  apply (main_realizes bsegs (argv_Z argvb) fs (START RT OUT_rep ERR_rep XENV LIB argvb fs) (OPEN RT OUT_rep ERR_rep XENV LIB argvb fs)
           (FAILED RT OUT_rep ERR_rep XENV LIB argvb fs) (OPENED RT OUT_rep ERR_rep XENV LIB argvb fs) (EXIT fs)); [| | | | | | | | exact HS].
  - intros code c' (A & Pm & PM & HA & HPm & HPM).
    exact (ast_exit bsegs SEGTOP_A asegs_wx asegs_below A Pm PM c' (Z_to_bv 64 code) fs HA HPm HPM).
  - intros HL. rewrite length_argv_Z in HL.
    exact (usage_cpsE RT OUT_rep ERR_rep IO_FP XENV XENV_FP LIB argvb fs AF AF_DRV FPR EXC0 VARGV OUT_loc ERR_loc XENV_loc LIB_loc
             IO_img XENV_img HL).
  - intros HL. rewrite length_argv_Z in HL.
    exact (to_open_cps RT OUT_rep ERR_rep IO_FP XENV XENV_FP LIB argvb fs AF OUT_loc ERR_loc XENV_loc LIB_loc IO_img XENV_img HL).
  - intros HL HCL. rewrite length_argv_Z in HL.
    exact (open_fail_cps RT OUT_rep ERR_rep IO_FP XENV XENV_FP LIB argvb fs AF AF_DRV OPR VARGV OUT_loc ERR_loc XENV_loc LIB_loc
             IO_img XENV_img HL HCL).
  - intros HL HCL. rewrite length_argv_Z in HL.
    exact (open_cps2 RT OUT_rep ERR_rep IO_FP XENV XENV_FP LIB argvb fs AF AF_DRV OPC VARGV OUT_loc ERR_loc XENV_loc LIB_loc
             IO_img XENV_img HL HCL).
  - intros HL. rewrite length_argv_Z in HL.
    exact (failed_cpsE RT OUT_rep ERR_rep IO_FP XENV XENV_FP LIB argvb fs AF AF_DRV FPR EXC0 VARGV OUT_loc ERR_loc XENV_loc LIB_loc
             IO_img XENV_img HL).
  - intros HL HCL. rewrite length_argv_Z in HL.
    exact (dir_cpsE RT OUT_rep ERR_rep IO_FP XENV XENV_FP LIB argvb fs AF AF_DRV MAL RDIR FPR EXC0 VARGV OUT_loc ERR_loc XENV_loc
             LIB_loc IO_img XENV_img HL HCL).
  - intros HL data HCL. rewrite length_argv_Z in HL.
    exact (file_cpsE RT OUT_rep ERR_rep IO_FP argvb fs AF AF_DRV CLS MAL FRE FRN MCP RFILE FPR FWR FUZZ VPR EXC0 EXC VARGV
             OUT_loc ERR_loc IO_img IO_img2 XENV_img HL data HCL).
Qed.

End MainA.

