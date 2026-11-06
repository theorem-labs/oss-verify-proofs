(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import
PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk StreamSim MmapSim LibAtomic Js0ExitBase Js0Exit_run2.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import OtfKit.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Plain.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__Js0Exit_run3 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Js0ExitBase."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Js0Exit_run2."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Js0Exit_run3.FPX_1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1Some"; "1bool"; "1list"; "1option"; "1true"; "2I"; "2and"; "2eq"; "2ex"; "2not"; "3Z"; "4store_ok"; "4word_to_le_bytes"; "5bvmap"; "6msteps"; "7file_clean"]; ["7stdio_globals"; "8mem_w3a"; "9stdout_dirty_hdr"; ":getr"; ":mkst"; ":rdn"; ";loaded_segments"; "<add"; "<le"; "<lt"; "<pow"; "<sub"; "0code"; "0fx"; "0mem"; "0regs"]; ["0regs'"; "0rom"; "0rp1"; "0rp2"; "0sp"; "=BV"; "=Z_to_bv"; "=bv"; "=bv_unsigned"; "0wb"; "0wp"; "0wp2"]]).
Local Ltac oF' pc := oF constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M.loaded_segments) pc.
Local Ltac oD' pc := oD constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M.loaded_segments) pc.
Local Ltac oE' pc := oE constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M.loaded_segments) pc.
Local Ltac oW' pc := oW constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M.loaded_segments) pc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section FPX_1. Context {fx : PropExec.FPState}.
Definition stdout_dirty_hdr (mem : word -> option byte) (wb wp : Z) : Prop :=
rdn RSEGS mem (Z_to_bv 64 (0xb60d0 + 140)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 4294967295))
/\ rdn RSEGS mem (Z_to_bv 64 (0xb60d0 + 40)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 wp))
/\ rdn RSEGS mem (Z_to_bv 64 (0xb60d0 + 56)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 wb))
/\ rdn RSEGS mem (Z_to_bv 64 (0xb60d0 + 72)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x9dc38)).
Section SE.
Local Abbreviation SEC_T_w3b1 := (ltac2:(TCodec.tc2 tcn__Js0Exit_run3 "U6&=y5'Q7yR0%211%5241'3y8%611%311p061':'7&Cr7(Q5+2(5%33A21%6251&Q6&K&Q8r4%22E1+@%5221%72H1%@3H91r8+8%@3N1>%C231%E3M1:r9+1%E3Q31C%H231+cRiL%C2Q41%L3Q431&H+TPPPPP0%E2Q8M+T@%H221%5241%I2Q<B+TPPPPPPPP0%8221'1&;&Fr;%Q02QCD%Q221;%Q42QE1uT@%746521(4%Q@3:21&@r<%211&Br=%231Q0Q5'6zr:%M221&I&J+R0%22QJ1%4261%9261&9%R23R3@I%211'8'>&DvMrC+chVH%R73RC1R5/01RCrBrA%8576321r1+cgQH%R>3RJ1R</01RJ&Ar@r?%33:21%A5@851:%C3Q@:1+:%RG3S51RE%RJ2<1+fhV@%RE2S61%RN3S631+;%RM3S;1RK%S02B1%RJ2S;Q:%S33S;21+<%S23S@1S0%S52G1%S73S?15%S72IR@+ch\8%S22SC1%S;3SC31%S;2MS6%S32SFI+Q0%S6221%S82SI1%SA3SI51%SA2Q3RO%SC3SK1F+3%SB3T01S@%SE2Q71%SF2Q?2%SH3T021+4%SG3T51SE%SJ2Q<1%SK2QD2%SM3T521%R7261%R82<1%R92?1%R:2F1%R;2K1%R<2Q01%R=2Q61%R>2Q=1qR2T=1%R32T>1p0R51p0R91p0R:1p0RE1p0RI1p0RM1p0S91p0S=1p0SD1p0SL1p0T21pRFTD1pRDTE1pQJTM1pR:TN1pR4TI1pQNTJ1pR0U01")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_w3b1) 0%nat 0%nat).
Variable mem : ltac:(sec_ty2 constr:(SEC_T_w3b1) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_w3b1) 2%nat 0%nat).
Variable sp : ltac:(sec_ty2 constr:(SEC_T_w3b1) 3%nat 0%nat).
Variable code : ltac:(sec_ty2 constr:(SEC_T_w3b1) 4%nat 0%nat).
Variable wb : ltac:(sec_ty2 constr:(SEC_T_w3b1) 5%nat 0%nat).
Variable wp : ltac:(sec_ty2 constr:(SEC_T_w3b1) 6%nat 0%nat).
Lemma w3b1 : ltac:(sec_stmt2 constr:(SEC_T_w3b1) 7%nat 0%nat).
Proof.
intros Hsp Hs0 Hra SPlo SPhi SOK
(Gnl & Gofl & Gin & Gout & Gerr) (F1l & F1wp & F1wb & F1wr) WB WP NE.
zaddr F1l; zaddr F1wp; zaddr F1wb; zaddr F1wr.
unfold mem_w3a. eexists. split.
-
stepn (ltac:(oF' 0x9e0d8%Z)) (ltac:(oD' 0x9e0d8%Z)). rewrite Hsp. sp_renorm.
stepST (ltac:(oF' 0x9e0dc%Z)) (ltac:(oD' 0x9e0dc%Z)) (Z_to_bv 64 (bv_unsigned sp - 24)) (Z_to_bv 64 0x98b3c) ltac:(sok_stack SOK).
stepST (ltac:(oF' 0x9e0e0%Z)) (ltac:(oD' 0x9e0e0%Z)) (Z_to_bv 64 (bv_unsigned sp - 32)) code ltac:(sok_stack SOK).
stepn (ltac:(oF' 0x9e0e4%Z)) (ltac:(oD' 0x9e0e4%Z)).
stepn (ltac:(oF' 0x9e500%Z)) (ltac:(oD' 0x9e500%Z)). sp_renorm.
stepST (ltac:(oF' 0x9e504%Z)) (ltac:(oD' 0x9e504%Z)) (Z_to_bv 64 (bv_unsigned sp - 40)) (Z_to_bv 64 0x9e0e8) ltac:(sok_stack SOK).
stepST (ltac:(oF' 0x9e508%Z)) (ltac:(oD' 0x9e508%Z)) (Z_to_bv 64 (bv_unsigned sp - 48)) code ltac:(sok_stack SOK).
stepn (ltac:(oF' 0x9e50c%Z)) (ltac:(oD' 0x9e50c%Z)).
stepn (ltac:(oF' 0x9e510%Z)) (ltac:(oD' 0x9e510%Z)).
stepn (ltac:(oF' 0x9e514%Z)) (ltac:(oD' 0x9e514%Z)).
stepn (ltac:(oF' 0x9e518%Z)) (ltac:(oD' 0x9e518%Z)).
stepn (ltac:(oF' 0xa9df0%Z)) (ltac:(oD' 0xa9df0%Z)).
chain_step; [reflexivity
| eapply step_lb with (b := Z_to_bv 8 0);
[exact (ltac:(oF' 0xa9df4%Z)) | reflexivity | exact (ltac:(oD' 0xa9df4%Z)) | gres; imm_norm; addr_norm; rdn_solve]
| step_simpl]; vnorm.
stepb_tk (ltac:(oF' 0xa9df8%Z)) (ltac:(oD' 0xa9df8%Z)) ltac:(cond_compute).
stepret (ltac:(oF' 0xa9fe8%Z)) (ltac:(oD' 0xa9fe8%Z)) (0x9e51c : word) ltac:(bveq).
stepn (ltac:(oF' 0x9e51c%Z)) (ltac:(oD' 0x9e51c%Z)).
stepLD8 (ltac:(oF' 0x9e520%Z)) (ltac:(oD' 0x9e520%Z)) (Z_to_bv 64 0x9e0e8).
stepLD8 (ltac:(oF' 0x9e524%Z)) (ltac:(oD' 0x9e524%Z)) code.
stepn (ltac:(oF' 0x9e528%Z)) (ltac:(oD' 0x9e528%Z)). sp_renorm.
stepret (ltac:(oF' 0x9e52c%Z)) (ltac:(oD' 0x9e52c%Z)) (0x9e0e8 : word) ltac:(bveq).
stepLD8 (ltac:(oF' 0x9e0e8%Z)) (ltac:(oD' 0x9e0e8%Z)) (Z_to_bv 64 0).
stepb_ft (ltac:(oF' 0x9e0ec%Z)) (ltac:(oD' 0x9e0ec%Z)) ltac:(cond_compute).
stepn (ltac:(oF' 0x9e0f0%Z)) (ltac:(oD' 0x9e0f0%Z)).
stepLD8 (ltac:(oF' 0x9e0f4%Z)) (ltac:(oD' 0x9e0f4%Z)) (Z_to_bv 64 0).
stepb_tk (ltac:(oF' 0x9e0f8%Z)) (ltac:(oD' 0x9e0f8%Z)) ltac:(cond_compute).
stepn (ltac:(oF' 0x9e14c%Z)) (ltac:(oD' 0x9e14c%Z)).
stepLD8 (ltac:(oF' 0x9e150%Z)) (ltac:(oD' 0x9e150%Z)) (Z_to_bv 64 0xb60d0).
stepb_ft (ltac:(oF' 0x9e154%Z)) (ltac:(oD' 0x9e154%Z)) ltac:(cond_compute).
stepLD (ltac:(oF' 0x9e158%Z)) (ltac:(oD' 0x9e158%Z)) (word_to_le_bytes 4 (Z_to_bv 64 4294967295)) (Z_to_bv 64 4294967295)
ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
stepb_tk (ltac:(oF' 0x9e15c%Z)) (ltac:(oD' 0x9e15c%Z)) ltac:(cond_compute).
stepLD8 (ltac:(oF' 0x9e168%Z)) (ltac:(oD' 0x9e168%Z)) (Z_to_bv 64 wp).
stepLD8 (ltac:(oF' 0x9e16c%Z)) (ltac:(oD' 0x9e16c%Z)) (Z_to_bv 64 wb).
stepb_ft (ltac:(oF' 0x9e170%Z)) (ltac:(oD' 0x9e170%Z)) ltac:(rewrite c_eq_Z by lia; apply Z.eqb_neq; lia).
stepLD8 (ltac:(oF' 0x9e174%Z)) (ltac:(oD' 0x9e174%Z)) (Z_to_bv 64 0x9dc38).
stepn (ltac:(oF' 0x9e178%Z)) (ltac:(oD' 0x9e178%Z)).
stepn (ltac:(oF' 0x9e17c%Z)) (ltac:(oD' 0x9e17c%Z)).
stepn (ltac:(oF' 0x9e180%Z)) (ltac:(oD' 0x9e180%Z)).
stepjr (ltac:(oF' 0x9e184%Z)) (ltac:(oD' 0x9e184%Z)) (Z_to_bv 64 0x9dc38) ltac:(gres; reflexivity). vnorm.
apply mst_refl.
- repeat split; gres; try reflexivity.
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_w3b2 := (ltac2:(TCodec.tc2 tcn__Js0Exit_run3 "TK&=y5'Q7yR0%211%5241'3y8%611%311p061'7&Cr8(Q5+2(5%33@21%6251&Q6&K&Q8r5%22D1+Q0%5221%72G1%@3G91r9+8%@3M1>%C231+fhV@%>2N1%G3N31&H+TPPPPP0r7%A2Q31+T@%D221%6251%E2Q7M+TPPPPPPPP0%9221'2%11Q6%Q911&E&Fr;%N2Q@G+H%Q1221%Q32QC1u8%847621(0&<+cRiL%Q92QI1%3261%52@1%QD3@71r<r:%Q=2QO1%Q?21Q;%QA2R11%E4D51>%<2?Q:%>2I1%QM3I31r=&G%12Q;Q>%QI2R91%M4L41F%R33O17r>+@%72QA1%QO2R?1%Q34Q241L%J2MC%L2Q71%R;3Q731r?+fhV8%R62RF1%Q:4Q931Q3+fgo0%R92RI1%Q32Q61%Q52Q@1%RD3Q@51&?r@%2417Q@Q1'8'6'>&DvMrC+ch\8%RL3S71RJ/01S7rBrA%8576321r1+cQo0%S33S>1S1/01S>%=5<4176%?3R361+:%S83SE1S6%S;281%S=3SD1Q1+A%S<3SI1S:%S?2<1+RN%S:2SJ1%SC3SJ31%SC2@S>%S;2SMO%S=21QA%S?2SO1%SH3SO41%Q0261%Q12=1%Q22B1qR2T21%Q52T31p0Q71p0Q;1p0QE1p0QN1p0R51p0R?1p0S31p0S71p0S?1p0SG1pR8T?1pRHT@1pR6TA1pQJTB1pR:TC1pR4T>1pQNT?1pR0TE1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_w3b2) 0%nat 0%nat).
Variable mem : ltac:(sec_ty2 constr:(SEC_T_w3b2) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_w3b2) 2%nat 0%nat).
Variable sp : ltac:(sec_ty2 constr:(SEC_T_w3b2) 3%nat 0%nat).
Variable code : ltac:(sec_ty2 constr:(SEC_T_w3b2) 4%nat 0%nat).
Variable rp1 : ltac:(sec_ty2 constr:(SEC_T_w3b2) 5%nat 0%nat).
Variable wp2 : ltac:(sec_ty2 constr:(SEC_T_w3b2) 6%nat 0%nat).
Variable rp2 : ltac:(sec_ty2 constr:(SEC_T_w3b2) 7%nat 0%nat).
Lemma w3b2 : ltac:(sec_stmt2 constr:(SEC_T_w3b2) 8%nat 0%nat).
Proof.
intros Hsp Hs0 SPlo SPhi M24 M32 F1rp F1re Gerr
(F2l & F2wp & F2wb & F2rp & F2re).
zaddr F1rp; zaddr F1re. zaddr F2l; zaddr F2wp; zaddr F2wb; zaddr F2rp; zaddr F2re.
eexists. split.
-
stepLD8 (ltac:(oF' 0x9e188%Z)) (ltac:(oD' 0x9e188%Z)) rp1.
stepLD8 (ltac:(oF' 0x9e18c%Z)) (ltac:(oD' 0x9e18c%Z)) rp1.
stepb_tk (ltac:(oF' 0x9e190%Z)) (ltac:(oD' 0x9e190%Z)) ltac:(apply c_eq_refl).
stepn (ltac:(oF' 0x9e1a8%Z)) (ltac:(oD' 0x9e1a8%Z)).
stepLD8 (ltac:(oF' 0x9e1ac%Z)) (ltac:(oD' 0x9e1ac%Z)) (Z_to_bv 64 0xb5fe0).
stepb_ft (ltac:(oF' 0x9e1b0%Z)) (ltac:(oD' 0x9e1b0%Z)) ltac:(cond_compute).
stepLD (ltac:(oF' 0x9e1b4%Z)) (ltac:(oD' 0x9e1b4%Z)) (word_to_le_bytes 4 (Z_to_bv 64 4294967295)) (Z_to_bv 64 4294967295)
ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
stepb_tk (ltac:(oF' 0x9e1b8%Z)) (ltac:(oD' 0x9e1b8%Z)) ltac:(cond_compute).
stepLD8 (ltac:(oF' 0x9e1c4%Z)) (ltac:(oD' 0x9e1c4%Z)) wp2.
stepLD8 (ltac:(oF' 0x9e1c8%Z)) (ltac:(oD' 0x9e1c8%Z)) wp2.
stepb_tk (ltac:(oF' 0x9e1cc%Z)) (ltac:(oD' 0x9e1cc%Z)) ltac:(apply c_eq_refl).
stepLD8 (ltac:(oF' 0x9e1e4%Z)) (ltac:(oD' 0x9e1e4%Z)) rp2.
stepLD8 (ltac:(oF' 0x9e1e8%Z)) (ltac:(oD' 0x9e1e8%Z)) rp2.
stepb_tk (ltac:(oF' 0x9e1ec%Z)) (ltac:(oD' 0x9e1ec%Z)) ltac:(apply c_eq_refl).
stepLD8 (ltac:(oF' 0x9e26c%Z)) (ltac:(oD' 0x9e26c%Z)) (Z_to_bv 64 0x98b3c).
stepLD8 (ltac:(oF' 0x9e270%Z)) (ltac:(oD' 0x9e270%Z)) code.
stepn (ltac:(oF' 0x9e274%Z)) (ltac:(oD' 0x9e274%Z)). rewrite Hsp. sp_renorm.
stepret (ltac:(oF' 0x9e278%Z)) (ltac:(oD' 0x9e278%Z)) (0x98b3c : word) ltac:(bveq).
stepn (ltac:(oF' 0x98b3c%Z)) (ltac:(oD' 0x98b3c%Z)).
stepn (ltac:(oF' 0x98b40%Z)) (ltac:(oD' 0x98b40%Z)).
stepn (ltac:(oF' 0x987d8%Z)) (ltac:(oD' 0x987d8%Z)).
stepn (ltac:(oF' 0x987dc%Z)) (ltac:(oD' 0x987dc%Z)).
apply mst_refl.
- repeat split; gres; try reflexivity.
Qed.
End SE.
End FPX_1.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
