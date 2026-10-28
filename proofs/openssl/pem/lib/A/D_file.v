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
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface D_iface D_defs D_kit D_libiface D_libiface_pem D_clx D_open D_rlkit D_loopdefs D_loop D_file1 D_file2 X_ax D_trpro D_file4.
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
Hypothesis CLS : close_contract RT.
Hypothesis MAL : malloc_contract RT.
Hypothesis FRE : free_contract RT.
Hypothesis FRN : free_null_contract RT.
Hypothesis MCP : memcpy_icontract RT e_memcpy.
Hypothesis RFILE : read_icontract_file RT.
Hypothesis FPR : fprintf_stderr_icontract RT OUT_rep ERR_rep IO_FP.
Hypothesis FWR : fwrite_stderr_icontract RT OUT_rep ERR_rep IO_FP.
Hypothesis INITC : fuzz_init_cps RT LIB0P LIBP FZ_SITES FZ_CALLS.
Hypothesis FUZZC : fuzz_one_cps RT LIBP FZ_SITES FZ_CALLS.
Hypothesis VPR : vprintf_emit0_icontract RT OUT_rep ERR_rep IO_FP.
Hypothesis EXC : exit_contract RT XENV OUT_rep ERR_rep.
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

Lemma RDONE_len : forall data c, RDONE RT OUT_rep ERR_rep XENV LIB CG argvb fs data c -> Z.of_nat (length data) < 67108864.
Proof.
  intros data c (Σ & usp & ap & path & buf & cap & gp & t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & s8 & s9 & s10 & s11
                  & t3 & t4 & t5 & t6 & c0 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & F & fc & m & _ & _ & _ & _ & Hdc & HCAP).
  pose proof (cap_ok_range cap HCAP). lia.
Qed.

Lemma RTOOBIG_len : forall data c, RTOOBIG RT OUT_rep ERR_rep XENV LIB CG argvb fs data c -> 67108864 <= Z.of_nat (length data).
Proof.
  intros data c (Σ & usp & ap & path & buf & gp & t0 & t1 & t2 & a3 & a4 & a5 & a6 & a7 & s8 & s9 & s10 & s11 & t3 & t4 & t5 & t6
                  & c0 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & F & fc & m & _ & _ & _ & Hbig). exact Hbig.
Qed.

Theorem file_cpsE : Z.of_nat (length argvb) = 2 -> forall data, open_class (nth 1 (argv_Z argvb) []) fs = OCFile data ->
  cpsE asegs (OPENED RT OUT_rep ERR_rep XENV LIB CG argvb fs)
    (evw (ct_fd (file_trace (map bv_unsigned data))) (ct_bytes (file_trace (map bv_unsigned data))))
    (EXIT fs (ct_code (file_trace (map bv_unsigned data)))).
Proof using AF AF_DRV CLS MAL FRE FRN MCP RFILE FPR FWR INITC FUZZC VPR EXC VARGV OUT_loc ERR_loc XENV_loc LIB_loc IO_img XENV_img LIB_pre LOC0 LOCP CGH XENV'_loc XENV_ax XENV_libc XENV_incb XENV_step XENV_fp_ax XENV'_ax XENV'_incb XENV'_upd EXC'.
  intros HL data HCL.
  pose proof HCL as HCL'. rewrite nth1_argv_Z in HCL'. pose proof (oc_file _ _ _ HCL') as (_ & HDATA).
  eapply cps_cpsE; [exact (file_start RT OUT_rep ERR_rep IO_FP XENV XENV_FP LIB CG argvb fs data AF MAL VARGV OUT_loc ERR_loc XENV_loc
                             LIB_loc IO_img XENV_img HL HCL)|].
  eapply cps_cpsE; [exact (read_loop RT OUT_rep ERR_rep IO_FP XENV XENV_FP LIB CG argvb fs data HDATA AF AF_DRV MAL FRE MCP RFILE
                             OUT_loc ERR_loc XENV_loc LIB_loc IO_img XENV_img 0 65536)|].
  intros T c [HD|HT] Hk.
  - exact (done_cpsE RT OUT_rep ERR_rep IO_FP XENV XENV_FP LIB CG LIB0P LIBP FZ_SITES FZ_CALLS argvb fs data AF AF_DRV CLS MAL FRE FRN MCP FWR
             INITC FUZZC VPR EXC OUT_loc ERR_loc XENV_loc LIB_loc IO_img XENV_img XENV' XENV'_loc XENV_ax XENV_libc XENV_incb XENV_step XENV_fp_ax
             XENV'_ax XENV'_incb XENV'_upd EXC' LIB_pre LOC0 LOCP CGH (RDONE_len data c HD) T c HD Hk).
  - pose proof (RTOOBIG_len data c HT) as Hbig.
    rewrite (ft_toobig data Hbig) in Hk |- *. cbn [ct_fd ct_bytes ct_code] in Hk |- *.
    exact (toobig_cpsE RT OUT_rep ERR_rep IO_FP XENV XENV_FP LIB CG argvb fs data AF AF_DRV FPR EXC OUT_loc ERR_loc XENV_loc LIB_loc
             IO_img XENV_img T c HT Hk).
Qed.

End File.
