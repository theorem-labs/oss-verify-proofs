(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS Require Import X0mx X0k2.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1d7 X1cx X1cy X1cp X1cj X1dd X1cg X1cm X1cs X1da X1d1.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.SpecA Require Import X1rw X1rn X1s9 X1rz.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require X1nu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0bp X0j9 X0ec X00a X001 X00b X00c X000 X0jg X00s X00j X003 X008 X004
X06k X0br.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0e7 X002.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X12c X14x X0r9 X0r0 X0ra X0rb X0qz X19x X0rr X0ri X0r2 X0r7 X0r3 X0xc.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X14s X0r1.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14x OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0r9 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0r0 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ra OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0rb OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0qz OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X19x OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0rr OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ri OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0r2 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0r7 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0r3 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0xc.
Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14s OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0r1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section MainAS.
Variable RT : rt_sig.
Variable OUT_rep : stdout_st -> mem -> Prop.
Variable ERR_rep : mem -> Prop.
Variable IO_FP : list (Z * Z).
Variable XENV : mem -> Prop.
Variable XENV_FP : list (Z * Z).
Variable XENV1 : mem -> Prop.
Variable XENV1x : mem -> Prop.
Variable LIB : mem -> Prop.
Variable argvb : list (list byte).
Variable fs : Fs.
Hypothesis AF : art_facts RT.
Hypothesis AF_DRV : forall Σ m, ART RT Σ m -> drv_consts m.
Hypothesis MAL : malloc_contract_okF RT.
Hypothesis FRE : free_contract_okF RT.
Hypothesis FRN : free_null_contract_ok RT.
Hypothesis MCP : memcpy_icontract RT e_memcpy.
Hypothesis RFILE : read_icontract_fileF RT.
Hypothesis RDIR : read_icontract_dir RT.
Hypothesis FPR : fprintf_stderr_icontract RT OUT_rep ERR_rep IO_FP.
Hypothesis FWR : fwrite_stderr_icontract RT OUT_rep ERR_rep IO_FP.
Hypothesis VPR : vprintf_emit0_icontractR RT OUT_rep ERR_rep IO_FP.
Hypothesis OPC : open_contractF RT.
Hypothesis OPR : open_refused_contract RT.
Hypothesis CLS : close_contractF RT.
Hypothesis EXC : exit_contract RT XENV OUT_rep ERR_rep.
Hypothesis EXC1 : exit_contract RT XENV1x OUT_rep ERR_rep.
Hypothesis XENV1x_of : forall m, XENV1 m -> rw_cells bsegs m TR_INIT [C1 (Z_to_bv 8 0)] -> XENV1x m.
Hypothesis FUZZ : fuzz_one_cpsE RT OUT_rep ERR_rep IO_FP LIB.
Hypothesis VARGV : valid_argv argvb.
Hypothesis OUT_loc : forall so, fp_local IO_FP (OUT_rep so).
Hypothesis ERR_loc : fp_local IO_FP ERR_rep.
Hypothesis XENV_loc : fp_local XENV_FP XENV.
Hypothesis XENV1_loc : fp_local XENV_FP XENV1.
Hypothesis LIB_loc : fp_local LIB_FP LIB.
Hypothesis IO_img : forall x, in_ranges IO_FP x -> client_static x /\ ~ drv_cell x /\ outside LIB_FP x.
Hypothesis XENV_img : forall x, in_ranges XENV_FP x -> client_static x /\ ~ drv_cell x /\ outside IO_FP x /\ outside LIB_FP x.
Hypothesis REG_out : forall m, XENV m -> reg_pre m.
Hypothesis REG_in : forall m m', XENV m ->
(forall a : word, in_ranges XENV_FP (bv_unsigned a) -> ~ in_ranges REG_CELLS (bv_unsigned a) -> m' a = m a) ->
reg_post m' -> XENV1 m'.
Hypothesis REG_fp : forall x, in_ranges REG_CELLS x -> in_ranges XENV_FP x.

Lemma length_argv_ZS : forall (argv : list (list byte)), length (argv_Z argv) = length argv.
Proof. intros argv. unfold argv_Z. apply length_map. Qed.

Theorem main_realizesAS : Spec.X1nu.run_defined fs (argv_Z argvb) true ->
forall c, STARTF RT OUT_rep ERR_rep XENV LIB argvb fs c -> realizes bsegs c (Spec.X1nu.canonT (argv_Z argvb) fs).
Proof using All.
intros RD c HS.
apply (main_realizesS bsegs (argv_Z argvb) fs (STARTF RT OUT_rep ERR_rep XENV LIB argvb fs) (OPENF RT OUT_rep ERR_rep XENV LIB argvb fs)
(FAILED RT OUT_rep ERR_rep XENV LIB argvb fs) (OPENEDF RT OUT_rep ERR_rep XENV LIB argvb fs) (EXIT fs)); [| | | | | | | | exact HS].
- intros code c' (A & Pm & PM & HA & HPm & HPM).
exact (ast_exit bsegs SEGTOP_A asegs_wx asegs_below A Pm PM c' (Z_to_bv 64 code) fs HA HPm HPM).
- intros HL. rewrite length_argv_ZS in HL.
exact (usage_cpsE RT OUT_rep ERR_rep IO_FP XENV XENV_FP LIB argvb fs AF AF_DRV FPR EXC VARGV OUT_loc ERR_loc XENV_loc LIB_loc
IO_img XENV_img HL).
- intros HL. rewrite length_argv_ZS in HL.
exact (to_open_cps RT OUT_rep ERR_rep IO_FP XENV XENV_FP LIB argvb fs AF OUT_loc ERR_loc XENV_loc LIB_loc IO_img XENV_img HL).
- intros HL HCL. rewrite length_argv_ZS in HL. rewrite open_classS in HCL. apply ocS_fail in HCL.
exact (open_fail_cps RT OUT_rep ERR_rep IO_FP XENV XENV_FP LIB argvb fs AF AF_DRV OPR VARGV OUT_loc ERR_loc XENV_loc LIB_loc
IO_img XENV_img HL HCL).
- intros HL HCL. rewrite length_argv_ZS in HL. rewrite open_classS in HCL.
assert (HCL' : open_class (nth 1 (argv_Z argvb) []) fs <> OCFail) by (intros E; apply HCL; apply ocS_fail; exact E).
exact (open_cps2 RT OUT_rep ERR_rep IO_FP XENV XENV_FP LIB argvb fs AF AF_DRV OPC VARGV OUT_loc ERR_loc XENV_loc LIB_loc
IO_img XENV_img HL HCL').
- intros HL. rewrite length_argv_ZS in HL.
exact (failed_cpsE RT OUT_rep ERR_rep IO_FP XENV XENV_FP LIB argvb fs AF AF_DRV FPR EXC VARGV OUT_loc ERR_loc XENV_loc LIB_loc
IO_img XENV_img HL).
- intros HL HCL. rewrite length_argv_ZS in HL. rewrite open_classS in HCL. apply ocS_dir in HCL.
exact (dir_cpsE RT OUT_rep ERR_rep IO_FP XENV XENV_FP LIB argvb fs AF AF_DRV (malloc_contract_ok_of_okF RT MAL) RDIR FPR EXC VARGV OUT_loc ERR_loc XENV_loc
LIB_loc IO_img XENV_img HL HCL).
- intros HL data HCL. rewrite length_argv_ZS in HL. rewrite open_classS in HCL. apply ocS_file in HCL.
exact (file_cpsE RT OUT_rep ERR_rep IO_FP XENV XENV_FP XENV1 XENV1x LIB argvb fs AF AF_DRV CLS MAL FRE FRN MCP RFILE FPR FWR FUZZ VPR EXC EXC1
XENV1x_of VARGV OUT_loc ERR_loc XENV_loc XENV1_loc LIB_loc IO_img XENV_img REG_out REG_in REG_fp HL data HCL RD).
Qed.

End MainAS.
End B_TWIN.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section MainAS.
Variable RT : rt_sig.
Variable OUT_rep : stdout_st -> mem -> Prop.
Variable ERR_rep : mem -> Prop.
Variable IO_FP : list (Z * Z).
Variable XENV : mem -> Prop.
Variable XENV_FP : list (Z * Z).
Variable XENV1 : mem -> Prop.
Variable XENV1x : mem -> Prop.
Variable LIB : mem -> Prop.
Variable argvb : list (list byte).
Variable fs : Fs.
Hypothesis AF : art_facts RT.
Hypothesis AF_DRV : forall Σ m, ART RT Σ m -> drv_consts m.
Hypothesis MAL : malloc_contract_okF RT.
Hypothesis FRE : free_contract_okF RT.
Hypothesis FRN : free_null_contract_ok RT.
Hypothesis MCP : memcpy_icontract RT e_memcpy.
Hypothesis RFILE : read_icontract_fileF RT.
Hypothesis RDIR : read_icontract_dir RT.
Hypothesis FPR : fprintf_stderr_icontract RT OUT_rep ERR_rep IO_FP.
Hypothesis FWR : fwrite_stderr_icontract RT OUT_rep ERR_rep IO_FP.
Hypothesis VPR : vprintf_emit0_icontractR RT OUT_rep ERR_rep IO_FP.
Hypothesis OPC : open_contractF RT.
Hypothesis OPR : open_refused_contract RT.
Hypothesis CLS : close_contractF RT.
Hypothesis EXC : exit_contract RT XENV OUT_rep ERR_rep.
Hypothesis EXC1 : exit_contract RT XENV1x OUT_rep ERR_rep.
Hypothesis XENV1x_of : forall m, XENV1 m -> rw_cells asegs m TR_INIT [C1 (Z_to_bv 8 0)] -> XENV1x m.
Hypothesis FUZZ : fuzz_one_cpsE RT OUT_rep ERR_rep IO_FP LIB.
Hypothesis VARGV : valid_argv argvb.
Hypothesis OUT_loc : forall so, fp_local IO_FP (OUT_rep so).
Hypothesis ERR_loc : fp_local IO_FP ERR_rep.
Hypothesis XENV_loc : fp_local XENV_FP XENV.
Hypothesis XENV1_loc : fp_local XENV_FP XENV1.
Hypothesis LIB_loc : fp_local LIB_FP LIB.
Hypothesis IO_img : forall x, in_ranges IO_FP x -> client_static x /\ ~ drv_cell x /\ outside LIB_FP x.
Hypothesis XENV_img : forall x, in_ranges XENV_FP x -> client_static x /\ ~ drv_cell x /\ outside IO_FP x /\ outside LIB_FP x.
Hypothesis REG_out : forall m, XENV m -> reg_pre m.
Hypothesis REG_in : forall m m', XENV m ->
(forall a : word, in_ranges XENV_FP (bv_unsigned a) -> ~ in_ranges REG_CELLS (bv_unsigned a) -> m' a = m a) ->
reg_post m' -> XENV1 m'.
Hypothesis REG_fp : forall x, in_ranges REG_CELLS x -> in_ranges XENV_FP x.

Lemma length_argv_ZS : forall (argv : list (list byte)), length (argv_Z argv) = length argv.
Proof. intros argv. unfold argv_Z. apply length_map. Qed.

Theorem main_realizesAS : Spec.X1nu.run_defined fs (argv_Z argvb) true ->
forall c, STARTF RT OUT_rep ERR_rep XENV LIB argvb fs c -> realizes asegs c (Spec.X1nu.canonT (argv_Z argvb) fs).
Proof using All.
intros RD c HS.
apply (main_realizesS asegs (argv_Z argvb) fs (STARTF RT OUT_rep ERR_rep XENV LIB argvb fs) (OPENF RT OUT_rep ERR_rep XENV LIB argvb fs)
(FAILED RT OUT_rep ERR_rep XENV LIB argvb fs) (OPENEDF RT OUT_rep ERR_rep XENV LIB argvb fs) (EXIT fs)); [| | | | | | | | exact HS].
- intros code c' (A & Pm & PM & HA & HPm & HPM).
exact (ast_exit asegs SEGTOP_A asegs_wx asegs_below A Pm PM c' (Z_to_bv 64 code) fs HA HPm HPM).
- intros HL. rewrite length_argv_ZS in HL.
exact (usage_cpsE RT OUT_rep ERR_rep IO_FP XENV XENV_FP LIB argvb fs AF AF_DRV FPR EXC VARGV OUT_loc ERR_loc XENV_loc LIB_loc
IO_img XENV_img HL).
- intros HL. rewrite length_argv_ZS in HL.
exact (to_open_cps RT OUT_rep ERR_rep IO_FP XENV XENV_FP LIB argvb fs AF OUT_loc ERR_loc XENV_loc LIB_loc IO_img XENV_img HL).
- intros HL HCL. rewrite length_argv_ZS in HL. rewrite open_classS in HCL. apply ocS_fail in HCL.
exact (open_fail_cps RT OUT_rep ERR_rep IO_FP XENV XENV_FP LIB argvb fs AF AF_DRV OPR VARGV OUT_loc ERR_loc XENV_loc LIB_loc
IO_img XENV_img HL HCL).
- intros HL HCL. rewrite length_argv_ZS in HL. rewrite open_classS in HCL.
assert (HCL' : open_class (nth 1 (argv_Z argvb) []) fs <> OCFail) by (intros E; apply HCL; apply ocS_fail; exact E).
exact (open_cps2 RT OUT_rep ERR_rep IO_FP XENV XENV_FP LIB argvb fs AF AF_DRV OPC VARGV OUT_loc ERR_loc XENV_loc LIB_loc
IO_img XENV_img HL HCL').
- intros HL. rewrite length_argv_ZS in HL.
exact (failed_cpsE RT OUT_rep ERR_rep IO_FP XENV XENV_FP LIB argvb fs AF AF_DRV FPR EXC VARGV OUT_loc ERR_loc XENV_loc LIB_loc
IO_img XENV_img HL).
- intros HL HCL. rewrite length_argv_ZS in HL. rewrite open_classS in HCL. apply ocS_dir in HCL.
exact (dir_cpsE RT OUT_rep ERR_rep IO_FP XENV XENV_FP LIB argvb fs AF AF_DRV (malloc_contract_ok_of_okF RT MAL) RDIR FPR EXC VARGV OUT_loc ERR_loc XENV_loc
LIB_loc IO_img XENV_img HL HCL).
- intros HL data HCL. rewrite length_argv_ZS in HL. rewrite open_classS in HCL. apply ocS_file in HCL.
exact (file_cpsE RT OUT_rep ERR_rep IO_FP XENV XENV_FP XENV1 XENV1x LIB argvb fs AF AF_DRV CLS MAL FRE FRN MCP RFILE FPR FWR FUZZ VPR EXC EXC1
XENV1x_of VARGV OUT_loc ERR_loc XENV_loc XENV1_loc LIB_loc IO_img XENV_img REG_out REG_in REG_fp HL data HCL RD).
Qed.

End MainAS.
