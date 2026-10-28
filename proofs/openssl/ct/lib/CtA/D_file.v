(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.openssl.ct.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import PropExec MState Mem Frame Cells Step Arr Exec RzCPS NodesA. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim Canon Stdio Prog.
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout RT_iface D_iface D_defs D_kit D_libiface D_clx D_libkit D_open D_rlkit D_loopdefs D_loop D_file1 D_file2 D_trpro D_atiface D_trdefs D_file4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma ft_toobig : forall (data : list byte), 67108864 <= Z.of_nat (length data) ->
  file_trace (map bv_unsigned data) = mkCT 2 msg_too_big 2.
Proof. intros data H. unfold file_trace, zlength. rewrite length_map. rewrite (proj2 (Z.leb_le _ _)) by lia. reflexivity. Qed.

Section File.
Variable RT : rt_sig.
Variable OUT_rep : stdout_st -> mem -> Prop.
Variable ERR_rep : mem -> Prop.
Variable IO_FP : list (Z * Z).
Variable XENV : mem -> Prop.
Variable XENV_FP : list (Z * Z).
Variable XENV1 : mem -> Prop.              (* [comment removed for export] *)
Variable XENV1_FP : list (Z * Z).
Variable XENV2 : mem -> Prop.
Variable LIBA : rts RT -> list (Z * Z) -> mem -> Prop.
Variable argvb : list (list byte).
Variable fs : Fs.
Hypothesis AF : art_facts RT.
Hypothesis AF_DRV : forall Σ m, ART RT Σ m -> drv_consts m.
Hypothesis CLS : close_contract RT.
Hypothesis MAL : malloc_contract_ok RT.
Hypothesis FRE : free_contract_ok RT.
Hypothesis FRN : free_null_contract_ok RT.
Hypothesis MCP : memcpy_icontract RT e_memcpy.
Hypothesis RFILE : read_icontract_file RT.
Hypothesis FPR : fprintf_stderr_icontract RT OUT_rep ERR_rep IO_FP.
Hypothesis FWR : fwrite_stderr_icontract RT OUT_rep ERR_rep IO_FP.
Hypothesis INIT : init_cps RT LIBA.
Hypothesis FUZZ : fuzz_one_cps' RT LIBA.
Hypothesis LFR : liba_frame RT LIBA.
Hypothesis LEX : liba_exit RT LIBA.
Hypothesis VPR : vprintf_emit0_icontract RT OUT_rep ERR_rep IO_FP.
Hypothesis EXC : exit_contract RT XENV OUT_rep ERR_rep lib_startA.
Hypothesis EXC2 : exit_contract RT XENV2 OUT_rep ERR_rep lib_exit_cells.
Hypothesis ATX : atexit_contract RT XENV XENV1.
Hypothesis VARGV : valid_argv argvb.
Hypothesis OUT_loc : forall so, fp_local IO_FP (OUT_rep so).
Hypothesis ERR_loc : fp_local IO_FP ERR_rep.
Hypothesis XENV_loc : fp_local XENV_FP XENV.
#[local] Notation LIB := lib_startA.
#[local] Notation LIB_loc := lib_startA_loc.
Hypothesis IO_img : forall x, in_ranges IO_FP x -> client_static x /\ ~ drv_cell x /\ outside LIB_FP x.
Hypothesis XENV_img : forall x, in_ranges XENV_FP x -> client_static x /\ ~ drv_cell x /\ outside IO_FP x /\ outside LIB_FP x.
Hypothesis XENV1_loc : fp_local XENV1_FP XENV1.
Hypothesis XENV2_loc : fp_local XENV_FP XENV2.
Hypothesis XENV1_img : forall x, in_ranges XENV1_FP x -> client_static x /\ ~ drv_cell x /\ outside IO_FP x /\ outside LIB_FP x.
Hypothesis XENV_incb : forall m, XENV m -> incb 0 m.
Hypothesis XENV2_intro : forall m, XENV1 m -> incb 0 m -> XENV2 m.
Hypothesis INCB_off : forall x, TR_INIT + 1 <= x < TR_INIT + 5 -> outside IO_FP x /\ outside XENV1_FP x.
Hypothesis ATXW_off : forall x, in_ranges ATX_W x -> outside IO_FP x.

Lemma RDONE_len : forall data c, RDONE RT OUT_rep ERR_rep XENV LIB argvb fs data c -> Z.of_nat (length data) < 67108864.
Proof.
  intros data c (Σ & usp & ap & path & buf & cap & gp & t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & s8 & s9 & s10 & s11
                  & t3 & t4 & t5 & t6 & c0 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & F & fc & m & _ & _ & _ & _ & Hdc & HCAP).
  pose proof (cap_ok_range cap HCAP). lia.
Qed.

Lemma RTOOBIG_len : forall data c, RTOOBIG RT OUT_rep ERR_rep XENV LIB argvb fs data c -> 67108864 <= Z.of_nat (length data).
Proof.
  intros data c (Σ & usp & ap & path & buf & gp & t0 & t1 & t2 & a3 & a4 & a5 & a6 & a7 & s8 & s9 & s10 & s11 & t3 & t4 & t5 & t6
                  & c0 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & F & fc & m & _ & _ & _ & Hbig). exact Hbig.
Qed.

Theorem file_cpsE : Z.of_nat (length argvb) = 2 -> forall data, open_class (nth 1 (argv_Z argvb) []) fs = OCFile data ->
  cpsE ctasegs (OPENED RT OUT_rep ERR_rep XENV LIB argvb fs)
    (evw (ct_fd (file_trace (map bv_unsigned data))) (ct_bytes (file_trace (map bv_unsigned data))))
    (EXIT fs (ct_code (file_trace (map bv_unsigned data)))).
Proof using All.
  intros HL data HCL.
  pose proof HCL as HCL'. rewrite nth1_argv_Z in HCL'. pose proof (oc_file _ _ _ HCL') as (_ & HDATA).
  eapply cps_cpsE; [exact (file_start RT OUT_rep ERR_rep IO_FP XENV XENV_FP LIB argvb fs data AF MAL VARGV OUT_loc ERR_loc XENV_loc
                             LIB_loc IO_img XENV_img HL HCL)|].
  eapply cps_cpsE; [exact (read_loop RT OUT_rep ERR_rep IO_FP XENV XENV_FP LIB argvb fs data HDATA AF AF_DRV MAL FRE MCP RFILE
                             OUT_loc ERR_loc XENV_loc LIB_loc IO_img XENV_img 0 65536)|].
  intros T c [HD|HT] Hk.
  - exact (done_cpsE RT OUT_rep ERR_rep IO_FP XENV XENV_FP XENV1 XENV1_FP XENV2 LIBA argvb fs data AF AF_DRV CLS MAL FRE FRN MCP FWR ATX INIT FUZZ LFR LEX VPR
             EXC EXC2 OUT_loc ERR_loc XENV_loc XENV1_loc XENV2_loc IO_img XENV_img XENV1_img XENV_incb XENV2_intro INCB_off ATXW_off
             (RDONE_len data c HD) T c HD Hk).
  - pose proof (RTOOBIG_len data c HT) as Hbig.
    rewrite (ft_toobig data Hbig) in Hk |- *. cbn [ct_fd ct_bytes ct_code] in Hk |- *.
    exact (toobig_cpsE RT OUT_rep ERR_rep IO_FP XENV XENV_FP LIB argvb fs data AF AF_DRV FPR EXC OUT_loc ERR_loc XENV_loc LIB_loc
             IO_img XENV_img T c HT Hk).
Qed.

End File.
