(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS Require Import X0mx X0k2.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1d7 X1cx X1cy X1cp X1cj X1dd X1cg X1cm X1cs X1da X1d1.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.SpecA Require Import X1rw X1rn X1s9 X1rz.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require X1r2 X1r8 X1nu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0bp X0j9 X0ec X00a X001 X00b X00c X000 X0jg X00j X00l
X00h X00d X005 X006 X008 X06k.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0e7 X002.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X12c X14x X0r9 X0r0 X0ra X0rb X0qz X19x X0ri X0rk X0rg X0rc X0r4 X0r5 X0r7 X0xc.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X14s X0r1.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14x OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0r9 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0r0 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ra OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0rb OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0qz OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X19x OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ri OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0rk OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0rg OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0rc OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0r4 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0r5 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0r7 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0xc.
Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14s OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0r1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma ft_toobig : forall (data : list byte), 67108864 <= Z.of_nat (length data) ->
file_trace (map bv_unsigned data) = mkCT 2 msg_too_big 2.
Proof. intros data H. unfold file_trace, zlength. rewrite length_map. rewrite (proj2 (Z.leb_le _ _)) by lia. reflexivity. Qed.

Lemma ftS_toobig : forall (data : list byte), 67108864 <= Z.of_nat (length data) ->
Spec.X1nu.file_trace (map bv_unsigned data) = Spec.X1nu.ct_diag msg_too_big.
Proof. intros data H. rewrite <- msgS_big. apply Spec.X1nu.file_trace_too_big. rewrite zlenS. exact H. Qed.

Section File.
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
Hypothesis CLS : close_contractF RT.
Hypothesis MAL : malloc_contract_okF RT.
Hypothesis FRE : free_contract_okF RT.
Hypothesis FRN : free_null_contract_ok RT.
Hypothesis MCP : memcpy_icontract RT e_memcpy.
Hypothesis RFILE : read_icontract_fileF RT.
Hypothesis FPR : fprintf_stderr_icontract RT OUT_rep ERR_rep IO_FP.
Hypothesis FWR : fwrite_stderr_icontract RT OUT_rep ERR_rep IO_FP.
Hypothesis FUZZ : fuzz_one_cpsE RT OUT_rep ERR_rep IO_FP LIB.
Hypothesis VPR : vprintf_emit0_icontractR RT OUT_rep ERR_rep IO_FP.
Hypothesis EXC : exit_contract RT XENV OUT_rep ERR_rep.
Hypothesis EXC1 : exit_contract RT XENV1x OUT_rep ERR_rep.
Hypothesis XENV1x_of : forall m, XENV1 m -> rw_cells bsegs m TR_INIT [C1 (Z_to_bv 8 0)] -> XENV1x m.
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

Lemma RDONE_len : forall data c, RDONE RT OUT_rep ERR_rep XENV LIB argvb fs data c -> Z.of_nat (length data) < 67108864.
Proof.
intros data c (Σ & usp & ap & path & buf & cap & gp & t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & s8 & s9 & s10 & s11
& t3 & t4 & t5 & t6 & c0 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & F & fc & m & _ & _ & _ & _ & Hdc & HCAP & _).
pose proof (cap_ok_range cap HCAP). lia.
Qed.

Lemma RTOOBIG_len : forall data c, RTOOBIG RT OUT_rep ERR_rep XENV LIB argvb fs data c -> 67108864 <= Z.of_nat (length data).
Proof.
intros data c (Σ & usp & ap & path & buf & gp & t0 & t1 & t2 & a3 & a4 & a5 & a6 & a7 & s8 & s9 & s10 & s11 & t3 & t4 & t5 & t6
& c0 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & F & fc & m & _ & _ & _ & Hbig). exact Hbig.
Qed.

Theorem file_cpsE : Z.of_nat (length argvb) = 2 -> forall data, open_class (nth 1 (argv_Z argvb) []) fs = OCFile data ->
Spec.X1nu.run_defined fs (argv_Z argvb) true   ->
cpsE bsegs (OPENEDF RT OUT_rep ERR_rep XENV LIB argvb fs)
(Spec.X1nu.ct_flat (Spec.X1nu.file_trace (map bv_unsigned data)))
(EXIT fs (Spec.X1nu.ct_code (Spec.X1nu.file_trace (map bv_unsigned data)))).
Proof using AF AF_DRV CLS MAL FRE FRN MCP RFILE FPR FWR FUZZ VPR EXC EXC1 XENV1x_of VARGV OUT_loc ERR_loc XENV_loc XENV1_loc LIB_loc IO_img XENV_img REG_out REG_in REG_fp.
intros HL data HCL RD.
assert (HDEF : ~ Z.of_nat (length data) < 6 -> ~ Z.of_nat (length data) < 6 + Spec.X1nu.cfg_len (map bv_unsigned data) ->
Z.of_nat (length data) < 67108864 -> Spec.X1nu.fuzz_defined (Spec.X1nu.cfg_payload (map bv_unsigned data))).
{ intros N1 N2 N3. apply (RD ltac:(unfold argv_Z; rewrite length_map; exact HL) data); [rewrite open_classS, HCL; reflexivity | | |]; cbv zeta; rewrite ?zlenS; assumption. }
pose proof HCL as HCL'. rewrite nth1_argv_Z in HCL'. pose proof (oc_file _ _ _ HCL') as (_ & HDATA).
eapply cps_cpsE; [exact (file_start RT OUT_rep ERR_rep IO_FP XENV XENV_FP LIB argvb fs data AF MAL VARGV OUT_loc ERR_loc XENV_loc
LIB_loc IO_img XENV_img HL HCL)|].
eapply cps_cpsE; [exact (read_loop RT OUT_rep ERR_rep IO_FP XENV XENV_FP LIB argvb fs data HDATA AF AF_DRV MAL FRE MCP RFILE
OUT_loc ERR_loc XENV_loc LIB_loc IO_img XENV_img 0 65536)|].
intros T c [HD|HT] Hk.
- exact (done_cpsE RT OUT_rep ERR_rep IO_FP XENV XENV_FP XENV1 XENV1x LIB argvb fs data AF AF_DRV CLS MAL (free_contract_ok_of_okF RT FRE) FRN MCP FWR FUZZ VPR EXC EXC1
XENV1x_of OUT_loc
ERR_loc XENV_loc XENV1_loc LIB_loc IO_img XENV_img REG_out REG_in REG_fp (RDONE_len data c HD) (fun N1 N2 => HDEF N1 N2 (RDONE_len data c HD)) T c HD Hk).
- pose proof (RTOOBIG_len data c HT) as Hbig.
rewrite (ftS_toobig data Hbig) in Hk |- *. rewrite Spec.X1nu.ct_flat_diag. change (Spec.X1nu.evw 2 msg_too_big) with (evw 2 msg_too_big).
change (Spec.X1nu.ct_code (Spec.X1nu.ct_diag msg_too_big)) with 2 in Hk.
exact (toobig_cpsE RT OUT_rep ERR_rep IO_FP XENV XENV_FP LIB argvb fs data AF AF_DRV FPR EXC OUT_loc ERR_loc XENV_loc LIB_loc
IO_img XENV_img T c HT Hk).
Qed.

End File.
End B_TWIN.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma ft_toobig : forall (data : list byte), 67108864 <= Z.of_nat (length data) ->
file_trace (map bv_unsigned data) = mkCT 2 msg_too_big 2.
Proof. intros data H. unfold file_trace, zlength. rewrite length_map. rewrite (proj2 (Z.leb_le _ _)) by lia. reflexivity. Qed.

Lemma ftS_toobig : forall (data : list byte), 67108864 <= Z.of_nat (length data) ->
Spec.X1nu.file_trace (map bv_unsigned data) = Spec.X1nu.ct_diag msg_too_big.
Proof. intros data H. rewrite <- msgS_big. apply Spec.X1nu.file_trace_too_big. rewrite zlenS. exact H. Qed.

Section File.
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
Hypothesis CLS : close_contractF RT.
Hypothesis MAL : malloc_contract_okF RT.
Hypothesis FRE : free_contract_okF RT.
Hypothesis FRN : free_null_contract_ok RT.
Hypothesis MCP : memcpy_icontract RT e_memcpy.
Hypothesis RFILE : read_icontract_fileF RT.
Hypothesis FPR : fprintf_stderr_icontract RT OUT_rep ERR_rep IO_FP.
Hypothesis FWR : fwrite_stderr_icontract RT OUT_rep ERR_rep IO_FP.
Hypothesis FUZZ : fuzz_one_cpsE RT OUT_rep ERR_rep IO_FP LIB.
Hypothesis VPR : vprintf_emit0_icontractR RT OUT_rep ERR_rep IO_FP.
Hypothesis EXC : exit_contract RT XENV OUT_rep ERR_rep.
Hypothesis EXC1 : exit_contract RT XENV1x OUT_rep ERR_rep.
Hypothesis XENV1x_of : forall m, XENV1 m -> rw_cells asegs m TR_INIT [C1 (Z_to_bv 8 0)] -> XENV1x m.
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

Lemma RDONE_len : forall data c, RDONE RT OUT_rep ERR_rep XENV LIB argvb fs data c -> Z.of_nat (length data) < 67108864.
Proof.
intros data c (Σ & usp & ap & path & buf & cap & gp & t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & s8 & s9 & s10 & s11
& t3 & t4 & t5 & t6 & c0 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & F & fc & m & _ & _ & _ & _ & Hdc & HCAP & _).
pose proof (cap_ok_range cap HCAP). lia.
Qed.

Lemma RTOOBIG_len : forall data c, RTOOBIG RT OUT_rep ERR_rep XENV LIB argvb fs data c -> 67108864 <= Z.of_nat (length data).
Proof.
intros data c (Σ & usp & ap & path & buf & gp & t0 & t1 & t2 & a3 & a4 & a5 & a6 & a7 & s8 & s9 & s10 & s11 & t3 & t4 & t5 & t6
& c0 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & F & fc & m & _ & _ & _ & Hbig). exact Hbig.
Qed.

Theorem file_cpsE : Z.of_nat (length argvb) = 2 -> forall data, open_class (nth 1 (argv_Z argvb) []) fs = OCFile data ->
Spec.X1nu.run_defined fs (argv_Z argvb) true   ->
cpsE asegs (OPENEDF RT OUT_rep ERR_rep XENV LIB argvb fs)
(Spec.X1nu.ct_flat (Spec.X1nu.file_trace (map bv_unsigned data)))
(EXIT fs (Spec.X1nu.ct_code (Spec.X1nu.file_trace (map bv_unsigned data)))).
Proof using AF AF_DRV CLS MAL FRE FRN MCP RFILE FPR FWR FUZZ VPR EXC EXC1 XENV1x_of VARGV OUT_loc ERR_loc XENV_loc XENV1_loc LIB_loc IO_img XENV_img REG_out REG_in REG_fp.
intros HL data HCL RD.
assert (HDEF : ~ Z.of_nat (length data) < 6 -> ~ Z.of_nat (length data) < 6 + Spec.X1nu.cfg_len (map bv_unsigned data) ->
Z.of_nat (length data) < 67108864 -> Spec.X1nu.fuzz_defined (Spec.X1nu.cfg_payload (map bv_unsigned data))).
{ intros N1 N2 N3. apply (RD ltac:(unfold argv_Z; rewrite length_map; exact HL) data); [rewrite open_classS, HCL; reflexivity | | |]; cbv zeta; rewrite ?zlenS; assumption. }
pose proof HCL as HCL'. rewrite nth1_argv_Z in HCL'. pose proof (oc_file _ _ _ HCL') as (_ & HDATA).
eapply cps_cpsE; [exact (file_start RT OUT_rep ERR_rep IO_FP XENV XENV_FP LIB argvb fs data AF MAL VARGV OUT_loc ERR_loc XENV_loc
LIB_loc IO_img XENV_img HL HCL)|].
eapply cps_cpsE; [exact (read_loop RT OUT_rep ERR_rep IO_FP XENV XENV_FP LIB argvb fs data HDATA AF AF_DRV MAL FRE MCP RFILE
OUT_loc ERR_loc XENV_loc LIB_loc IO_img XENV_img 0 65536)|].
intros T c [HD|HT] Hk.
- exact (done_cpsE RT OUT_rep ERR_rep IO_FP XENV XENV_FP XENV1 XENV1x LIB argvb fs data AF AF_DRV CLS MAL (free_contract_ok_of_okF RT FRE) FRN MCP FWR FUZZ VPR EXC EXC1
XENV1x_of OUT_loc
ERR_loc XENV_loc XENV1_loc LIB_loc IO_img XENV_img REG_out REG_in REG_fp (RDONE_len data c HD) (fun N1 N2 => HDEF N1 N2 (RDONE_len data c HD)) T c HD Hk).
- pose proof (RTOOBIG_len data c HT) as Hbig.
rewrite (ftS_toobig data Hbig) in Hk |- *. rewrite Spec.X1nu.ct_flat_diag. change (Spec.X1nu.evw 2 msg_too_big) with (evw 2 msg_too_big).
change (Spec.X1nu.ct_code (Spec.X1nu.ct_diag msg_too_big)) with 2 in Hk.
exact (toobig_cpsE RT OUT_rep ERR_rep IO_FP XENV XENV_FP LIB argvb fs data AF AF_DRV FPR EXC OUT_loc ERR_loc XENV_loc LIB_loc
IO_img XENV_img T c HT Hk).
Qed.

End File.
