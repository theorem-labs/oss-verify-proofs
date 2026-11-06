(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import
PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk StreamSim MmapSim LibAtomic Ju0ExitBase.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import OtfKit.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__Ju0Exit_run2 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ju0ExitBase."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ju0Exit_run2.FPX_1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Ubsan.M."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1bool"; "1option"; "1true"; "2I"; "2and"; "2eq"; "2ex"; "3store_ok"; "4bvmap"; "5msteps"; "6file_clean"; "6stdio_globals"; "7mem_w3a"; "8getr"; "8mkst"; "9loaded_segments"]; [":le"; ":sub"; "0code"; "0fx"; "0mem"; "0regs"; "0regs'"; "0rom"; "0rp1"; "0rp2"; "0sp"; ";BV"; ";Z_to_bv"; ";bv"; ";bv_unsigned"; "0wp1"]; ["0wp2"]]).
Local Ltac oF' pc := oF constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Ubsan.M.loaded_segments) pc.
Local Ltac oD' pc := oD constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Ubsan.M.loaded_segments) pc.
Local Ltac oE' pc := oE constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Ubsan.M.loaded_segments) pc.
Local Ltac oW' pc := oW constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Ubsan.M.loaded_segments) pc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section FPX_1. Context {fx : PropExec.FPState}.
Definition mem_w3a (mem : word -> option byte) (sp code : word) :=
wbytes (wbytes (wbytes (wbytes mem
(Z_to_bv 64 (bv_unsigned sp - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0x99b90)))
(Z_to_bv 64 (bv_unsigned sp - 32)) (word_to_le_bytes 8 code))
(Z_to_bv 64 (bv_unsigned sp - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0x9f13c)))
(Z_to_bv 64 (bv_unsigned sp - 48)) (word_to_le_bytes 8 code).
Section SE.
Local Abbreviation SEC_T_w3a := (ltac2:(TCodec.tc2 tcn__Ju0Exit_run2 "T0&8y5'MyR0%211%5241'1y8%611%311p061'5&=r9(K+2(3%33@21%6251&L&A&Nr6%22D1+@%5221%72G1%@3G91r:+8%@3M1>%C231%E3L1:r;+1%E3Q21C%H231+cVl@%C2Q31%L3Q331&@+TPPPPP0%E2Q7M+T@%H221%5241%I2Q;B+TPPPPPPPP0%8221'0&7&?r=%Q02QBD%Q221;%Q42QD1uT@%746521(2%Q@3:21&;r>%211&:r?+flY0%3421Q1Q6r@+flQ@%6421Q9QH'6'4'9&>vCrC+clY<%QO3R:1QM/01R:rBrA%8576321r1+cVQD%R63RA1R4/01RA&<%138DG%?5>6318%A3Q681+:%R=3RJ1R;%R@2:1%RB3RI1M+A%RA3RN1R?%RD2>1+RN%R?2RO1%RH3RO31%RH2BRC%R@2S2Q2%RB21R>%RD2S41%RM3S441%Q2261%Q32=1%Q42B1qQ>S71%Q72S81p0Q91p0Q=1p0QB1p0QF1p0R21p0R61p0R=1p0RE1p0RK1pQDSC1pR2SD1pQBSE1pR0SF1pQ6SG1pQFSH1pQ@SC1pQ:SD1pQ<SJ1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_w3a) 0%nat 0%nat).
Variable mem : ltac:(sec_ty2 constr:(SEC_T_w3a) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_w3a) 2%nat 0%nat).
Variable sp : ltac:(sec_ty2 constr:(SEC_T_w3a) 3%nat 0%nat).
Variable code : ltac:(sec_ty2 constr:(SEC_T_w3a) 4%nat 0%nat).
Variable wp1 : ltac:(sec_ty2 constr:(SEC_T_w3a) 5%nat 0%nat).
Variable rp1 : ltac:(sec_ty2 constr:(SEC_T_w3a) 6%nat 0%nat).
Variable wp2 : ltac:(sec_ty2 constr:(SEC_T_w3a) 7%nat 0%nat).
Variable rp2 : ltac:(sec_ty2 constr:(SEC_T_w3a) 8%nat 0%nat).
Lemma w3a : ltac:(sec_stmt2 constr:(SEC_T_w3a) 9%nat 0%nat).
Proof.
intros Hsp Hs0 Hra SPlo SPhi SOK
(Gnl & Gofl & Gin & Gout & Gerr)
(F1l & F1wp & F1wb & F1rp & F1re) (F2l & F2wp & F2wb & F2rp & F2re).
zaddr F1l; zaddr F1wp; zaddr F1wb; zaddr F1rp; zaddr F1re.
zaddr F2l; zaddr F2wp; zaddr F2wb; zaddr F2rp; zaddr F2re.
unfold mem_w3a. eexists. split.
-
stepn (ltac:(oF' 0x9f12c%Z)) (ltac:(oD' 0x9f12c%Z)). rewrite Hsp. sp_renorm.
stepST (ltac:(oF' 0x9f130%Z)) (ltac:(oD' 0x9f130%Z)) (Z_to_bv 64 (bv_unsigned sp - 24)) (Z_to_bv 64 0x99b90) ltac:(sok_stack SOK).
stepST (ltac:(oF' 0x9f134%Z)) (ltac:(oD' 0x9f134%Z)) (Z_to_bv 64 (bv_unsigned sp - 32)) code ltac:(sok_stack SOK).
stepn (ltac:(oF' 0x9f138%Z)) (ltac:(oD' 0x9f138%Z)).
stepn (ltac:(oF' 0x9f554%Z)) (ltac:(oD' 0x9f554%Z)). sp_renorm.
stepST (ltac:(oF' 0x9f558%Z)) (ltac:(oD' 0x9f558%Z)) (Z_to_bv 64 (bv_unsigned sp - 40)) (Z_to_bv 64 0x9f13c) ltac:(sok_stack SOK).
stepST (ltac:(oF' 0x9f55c%Z)) (ltac:(oD' 0x9f55c%Z)) (Z_to_bv 64 (bv_unsigned sp - 48)) code ltac:(sok_stack SOK).
stepn (ltac:(oF' 0x9f560%Z)) (ltac:(oD' 0x9f560%Z)).
stepn (ltac:(oF' 0x9f564%Z)) (ltac:(oD' 0x9f564%Z)).
stepn (ltac:(oF' 0x9f568%Z)) (ltac:(oD' 0x9f568%Z)).
stepn (ltac:(oF' 0x9f56c%Z)) (ltac:(oD' 0x9f56c%Z)).
stepn (ltac:(oF' 0xaae44%Z)) (ltac:(oD' 0xaae44%Z)).
chain_step; [reflexivity
| eapply step_lb with (b := Z_to_bv 8 0);
[exact (ltac:(oF' 0xaae48%Z)) | reflexivity | exact (ltac:(oD' 0xaae48%Z)) | gres; imm_norm; addr_norm; rdn_solve]
| step_simpl]; vnorm.
stepb_tk (ltac:(oF' 0xaae4c%Z)) (ltac:(oD' 0xaae4c%Z)) ltac:(cond_compute).
stepret (ltac:(oF' 0xab03c%Z)) (ltac:(oD' 0xab03c%Z)) (0x9f570 : word) ltac:(bveq).
stepn (ltac:(oF' 0x9f570%Z)) (ltac:(oD' 0x9f570%Z)).
stepLD8 (ltac:(oF' 0x9f574%Z)) (ltac:(oD' 0x9f574%Z)) (Z_to_bv 64 0x9f13c).
stepLD8 (ltac:(oF' 0x9f578%Z)) (ltac:(oD' 0x9f578%Z)) code.
stepn (ltac:(oF' 0x9f57c%Z)) (ltac:(oD' 0x9f57c%Z)). sp_renorm.
stepret (ltac:(oF' 0x9f580%Z)) (ltac:(oD' 0x9f580%Z)) (0x9f13c : word) ltac:(bveq).
stepLD8 (ltac:(oF' 0x9f13c%Z)) (ltac:(oD' 0x9f13c%Z)) (Z_to_bv 64 0).
stepb_ft (ltac:(oF' 0x9f140%Z)) (ltac:(oD' 0x9f140%Z)) ltac:(cond_compute).
stepn (ltac:(oF' 0x9f144%Z)) (ltac:(oD' 0x9f144%Z)).
stepLD8 (ltac:(oF' 0x9f148%Z)) (ltac:(oD' 0x9f148%Z)) (Z_to_bv 64 0).
stepb_tk (ltac:(oF' 0x9f14c%Z)) (ltac:(oD' 0x9f14c%Z)) ltac:(cond_compute).
stepn (ltac:(oF' 0x9f1a0%Z)) (ltac:(oD' 0x9f1a0%Z)).
stepLD8 (ltac:(oF' 0x9f1a4%Z)) (ltac:(oD' 0x9f1a4%Z)) (Z_to_bv 64 0xb7120).
stepb_ft (ltac:(oF' 0x9f1a8%Z)) (ltac:(oD' 0x9f1a8%Z)) ltac:(cond_compute).
stepLD (ltac:(oF' 0x9f1ac%Z)) (ltac:(oD' 0x9f1ac%Z)) (word_to_le_bytes 4 (Z_to_bv 64 4294967295)) (Z_to_bv 64 4294967295)
ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
stepb_tk (ltac:(oF' 0x9f1b0%Z)) (ltac:(oD' 0x9f1b0%Z)) ltac:(cond_compute).
stepLD8 (ltac:(oF' 0x9f1bc%Z)) (ltac:(oD' 0x9f1bc%Z)) wp1.
stepLD8 (ltac:(oF' 0x9f1c0%Z)) (ltac:(oD' 0x9f1c0%Z)) wp1.
stepb_tk (ltac:(oF' 0x9f1c4%Z)) (ltac:(oD' 0x9f1c4%Z)) ltac:(apply c_eq_refl).
stepLD8 (ltac:(oF' 0x9f1dc%Z)) (ltac:(oD' 0x9f1dc%Z)) rp1.
stepLD8 (ltac:(oF' 0x9f1e0%Z)) (ltac:(oD' 0x9f1e0%Z)) rp1.
stepb_tk (ltac:(oF' 0x9f1e4%Z)) (ltac:(oD' 0x9f1e4%Z)) ltac:(apply c_eq_refl).
stepn (ltac:(oF' 0x9f1fc%Z)) (ltac:(oD' 0x9f1fc%Z)).
stepLD8 (ltac:(oF' 0x9f200%Z)) (ltac:(oD' 0x9f200%Z)) (Z_to_bv 64 0xb7030).
stepb_ft (ltac:(oF' 0x9f204%Z)) (ltac:(oD' 0x9f204%Z)) ltac:(cond_compute).
stepLD (ltac:(oF' 0x9f208%Z)) (ltac:(oD' 0x9f208%Z)) (word_to_le_bytes 4 (Z_to_bv 64 4294967295)) (Z_to_bv 64 4294967295)
ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
stepb_tk (ltac:(oF' 0x9f20c%Z)) (ltac:(oD' 0x9f20c%Z)) ltac:(cond_compute).
stepLD8 (ltac:(oF' 0x9f218%Z)) (ltac:(oD' 0x9f218%Z)) wp2.
stepLD8 (ltac:(oF' 0x9f21c%Z)) (ltac:(oD' 0x9f21c%Z)) wp2.
stepb_tk (ltac:(oF' 0x9f220%Z)) (ltac:(oD' 0x9f220%Z)) ltac:(apply c_eq_refl).
stepLD8 (ltac:(oF' 0x9f238%Z)) (ltac:(oD' 0x9f238%Z)) rp2.
stepLD8 (ltac:(oF' 0x9f23c%Z)) (ltac:(oD' 0x9f23c%Z)) rp2.
stepb_tk (ltac:(oF' 0x9f240%Z)) (ltac:(oD' 0x9f240%Z)) ltac:(apply c_eq_refl).
stepLD8 (ltac:(oF' 0x9f2c0%Z)) (ltac:(oD' 0x9f2c0%Z)) (Z_to_bv 64 0x99b90).
stepLD8 (ltac:(oF' 0x9f2c4%Z)) (ltac:(oD' 0x9f2c4%Z)) code.
stepn (ltac:(oF' 0x9f2c8%Z)) (ltac:(oD' 0x9f2c8%Z)). sp_renorm.
stepret (ltac:(oF' 0x9f2cc%Z)) (ltac:(oD' 0x9f2cc%Z)) (0x99b90 : word) ltac:(bveq).
stepn (ltac:(oF' 0x99b90%Z)) (ltac:(oD' 0x99b90%Z)).
stepn (ltac:(oF' 0x99b94%Z)) (ltac:(oD' 0x99b94%Z)).
stepn (ltac:(oF' 0x9982c%Z)) (ltac:(oD' 0x9982c%Z)).
stepn (ltac:(oF' 0x99830%Z)) (ltac:(oD' 0x99830%Z)).
apply mst_refl.
- repeat split; gres; try reflexivity.
Qed.
End SE.
End FPX_1.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
