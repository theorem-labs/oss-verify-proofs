(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import StartupTac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__Js0Memset () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Hoare."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Js0Memset.FPX_1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ZStores."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1bool"; "1option"; "1true"; "2I"; "2and"; "2eq"; "2ex"; "3Z"; "4store_ok"; "5bvmap"; "6wbytes"; "7msteps"; "8regs_agree"; "8ret_ok"; "9memset304_ws"; "9memset_clob"]; [":getr"; ":mkst"; ";ws_cover"; ";ws_inb"; ";zeros"; "<loaded_segments"; "=In"; ">add"; ">lt"; ">modulo"; ">pow"; "0d"; "0fx"; "0mem"; "0mem'"; "0r"]; ["0regs"; "0regs'"; "0ret"; "0rom"; "?BV"; "?Z_to_bv"; "?bv"; "?bv_unsigned"]]).
Abbreviation SEGS := Plain.M.loaded_segments.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require PropExec.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import OtfKit.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Plain.
Local Ltac oF' pc := oF constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M.loaded_segments) pc.
Local Ltac oD' pc := oD constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M.loaded_segments) pc.
Local Ltac oE' pc := oE constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M.loaded_segments) pc.
Local Ltac oW' pc := oW constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M.loaded_segments) pc.
Section FPX_1. Context {fx : PropExec.FPState}.
Definition memset304_ws : list (Z * nat) :=
[(0,1%nat); (303,1%nat); (1,1%nat); (2,1%nat); (301,1%nat); (302,1%nat); (3,1%nat); (300,1%nat); (0,4%nat); (300,4%nat); (4,4%nat); (8,4%nat); (292,4%nat); (296,4%nat); (12,4%nat); (16,4%nat); (20,4%nat); (24,4%nat); (276,4%nat); (280,4%nat); (284,4%nat); (288,4%nat); (24,8%nat); (32,8%nat); (40,8%nat); (48,8%nat); (56,8%nat); (64,8%nat); (72,8%nat); (80,8%nat); (88,8%nat); (96,8%nat); (104,8%nat); (112,8%nat); (120,8%nat); (128,8%nat); (136,8%nat); (144,8%nat); (152,8%nat); (160,8%nat); (168,8%nat); (176,8%nat); (184,8%nat); (192,8%nat); (200,8%nat); (208,8%nat); (216,8%nat); (224,8%nat); (232,8%nat); (240,8%nat); (248,8%nat); (256,8%nat); (264,8%nat); (272,8%nat)]%Z.
Lemma memset304_ws_inb : ltac2:(TCodec.tc2 tcn__Js0Memset "8'5'0&C&>+Y@%3221(2%73621").
Proof. vm_compute. reflexivity. Qed.
Lemma memset304_ws_cover : ltac2:(TCodec.tc2 tcn__Js0Memset "8'5'0&B&>uY@%3221(2%73621").
Proof. vm_compute. reflexivity. Qed.
Definition memset_clob : list reg := [11; 12; 13; 14; 15; 16]%list.
Section SE.
Local Abbreviation SEC_T_memset304_run := (ltac2:(TCodec.tc2 tcn__Js0Memset "SC&9y5'Q6yR0%211%5241'1y8%611%311p061'5&@r5(Q4+1(3%33@21%6251r1%93@21&=r2%211r7+:%<3I1:%?231r4%B3I21r8+;%B3O1@%E231&Q5z%22Q11%J3Q141r9+<%J3Q71H%M231+Y@%92Q81%Q13Q831'7&I&Q7%12Q=H+8%4221%Q8361@&H&G%72QCH%221=&J+2+R0%3221%8251'0&8&Er;uY@%4432L1(2%QI3721'6'4';&AvLr?+eUg0%QN3R91QL/01R9r>r=%8576321%958QKAQN2%;3C21&:r<&D%11E%43931%R=3R>R51&<%RH1RI&F&?%233R:1qR041%631ER9%J281%K2?1qQNRH1%N2RI1qR4RO1%Q02S01p0Q21p0Q;1p0QE1p0QM1p0R51p0R>1p0RE1p0RI1pR6S:1pQHS;1pR8S61pQLS71pR2S=1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_memset304_run) 0%nat 0%nat).
Variable mem : ltac:(sec_ty2 constr:(SEC_T_memset304_run) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_memset304_run) 2%nat 0%nat).
Variable d : ltac:(sec_ty2 constr:(SEC_T_memset304_run) 3%nat 0%nat).
Variable ret : ltac:(sec_ty2 constr:(SEC_T_memset304_run) 4%nat 0%nat).
Lemma memset304_run : ltac:(sec_stmt2 constr:(SEC_T_memset304_run) 5%nat 0%nat).
Proof.
intros Hra Hret Hd H11 H12 Hal Hnw Hok.
pose proof (u64_range d) as Hdr.
assert (Hal4 : (bv_unsigned d mod 4 = 0)%Z).
{ rewrite <- (Z.mod_mod_divide _ 8 4) by (exists 2%Z; reflexivity). rewrite Hal. reflexivity. }
eexists. eexists. split; [|split].
-
stepb_ft (ltac:(oF' 0xa96e0%Z)) (ltac:(oD' 0xa96e0%Z)) ltac:(pin; cond_compute).
stw (ltac:(oF' 0xa96e4%Z)) (ltac:(oD' 0xa96e4%Z)) (Z_to_bv 64 (bv_unsigned d + 0)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
sv (ltac:(oF' 0xa96e8%Z)) (ltac:(oD' 0xa96e8%Z)) (Z_to_bv 64 (bv_unsigned d + 304)).
sn (ltac:(oF' 0xa96ec%Z)) (ltac:(oD' 0xa96ec%Z)).
stw (ltac:(oF' 0xa96f0%Z)) (ltac:(oD' 0xa96f0%Z)) (Z_to_bv 64 (bv_unsigned d + 303)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
stepb_ft (ltac:(oF' 0xa96f4%Z)) (ltac:(oD' 0xa96f4%Z)) ltac:(pin; cond_compute).
stw (ltac:(oF' 0xa96f8%Z)) (ltac:(oD' 0xa96f8%Z)) (Z_to_bv 64 (bv_unsigned d + 1)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
stw (ltac:(oF' 0xa96fc%Z)) (ltac:(oD' 0xa96fc%Z)) (Z_to_bv 64 (bv_unsigned d + 2)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
sn (ltac:(oF' 0xa9700%Z)) (ltac:(oD' 0xa9700%Z)).
stw (ltac:(oF' 0xa9704%Z)) (ltac:(oD' 0xa9704%Z)) (Z_to_bv 64 (bv_unsigned d + 301)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
stw (ltac:(oF' 0xa9708%Z)) (ltac:(oD' 0xa9708%Z)) (Z_to_bv 64 (bv_unsigned d + 302)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
stepb_ft (ltac:(oF' 0xa970c%Z)) (ltac:(oD' 0xa970c%Z)) ltac:(pin; cond_compute).
stw (ltac:(oF' 0xa9710%Z)) (ltac:(oD' 0xa9710%Z)) (Z_to_bv 64 (bv_unsigned d + 3)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
sn (ltac:(oF' 0xa9714%Z)) (ltac:(oD' 0xa9714%Z)).
stw (ltac:(oF' 0xa9718%Z)) (ltac:(oD' 0xa9718%Z)) (Z_to_bv 64 (bv_unsigned d + 300)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
stepb_ft (ltac:(oF' 0xa971c%Z)) (ltac:(oD' 0xa971c%Z)) ltac:(pin; cond_compute).
sn (ltac:(oF' 0xa9720%Z)) (ltac:(oD' 0xa9720%Z)).
sn (ltac:(oF' 0xa9724%Z)) (ltac:(oD' 0xa9724%Z)).
sn (ltac:(oF' 0xa9728%Z)) (ltac:(oD' 0xa9728%Z)).
stepiv (ltac:(oF' 0xa972c%Z)) (ltac:(oD' 0xa972c%Z)) (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; apply negw_and3_aligned; exact Hal4).
sn (ltac:(oF' 0xa9730%Z)) (ltac:(oD' 0xa9730%Z)).
sn (ltac:(oF' 0xa9734%Z)) (ltac:(oD' 0xa9734%Z)).
sv (ltac:(oF' 0xa9738%Z)) (ltac:(oD' 0xa9738%Z)) (d).
sn (ltac:(oF' 0xa973c%Z)) (ltac:(oD' 0xa973c%Z)).
sn (ltac:(oF' 0xa9740%Z)) (ltac:(oD' 0xa9740%Z)).
sn (ltac:(oF' 0xa9744%Z)) (ltac:(oD' 0xa9744%Z)).
stw (ltac:(oF' 0xa9748%Z)) (ltac:(oD' 0xa9748%Z)) (Z_to_bv 64 (bv_unsigned d + 0)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
sv (ltac:(oF' 0xa974c%Z)) (ltac:(oD' 0xa974c%Z)) (Z_to_bv 64 (bv_unsigned d + 304)).
stw (ltac:(oF' 0xa9750%Z)) (ltac:(oD' 0xa9750%Z)) (Z_to_bv 64 (bv_unsigned d + 300)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
stepb_ft (ltac:(oF' 0xa9754%Z)) (ltac:(oD' 0xa9754%Z)) ltac:(pin; cond_compute).
stw (ltac:(oF' 0xa9758%Z)) (ltac:(oD' 0xa9758%Z)) (Z_to_bv 64 (bv_unsigned d + 4)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
stw (ltac:(oF' 0xa975c%Z)) (ltac:(oD' 0xa975c%Z)) (Z_to_bv 64 (bv_unsigned d + 8)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
sn (ltac:(oF' 0xa9760%Z)) (ltac:(oD' 0xa9760%Z)).
stw (ltac:(oF' 0xa9764%Z)) (ltac:(oD' 0xa9764%Z)) (Z_to_bv 64 (bv_unsigned d + 292)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
stw (ltac:(oF' 0xa9768%Z)) (ltac:(oD' 0xa9768%Z)) (Z_to_bv 64 (bv_unsigned d + 296)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
stepb_ft (ltac:(oF' 0xa976c%Z)) (ltac:(oD' 0xa976c%Z)) ltac:(pin; cond_compute).
stw (ltac:(oF' 0xa9770%Z)) (ltac:(oD' 0xa9770%Z)) (Z_to_bv 64 (bv_unsigned d + 12)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
stw (ltac:(oF' 0xa9774%Z)) (ltac:(oD' 0xa9774%Z)) (Z_to_bv 64 (bv_unsigned d + 16)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
stw (ltac:(oF' 0xa9778%Z)) (ltac:(oD' 0xa9778%Z)) (Z_to_bv 64 (bv_unsigned d + 20)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
stw (ltac:(oF' 0xa977c%Z)) (ltac:(oD' 0xa977c%Z)) (Z_to_bv 64 (bv_unsigned d + 24)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
stepiv (ltac:(oF' 0xa9780%Z)) (ltac:(oD' 0xa9780%Z)) (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; apply v_andi_4_aligned8; exact Hal).
sn (ltac:(oF' 0xa9784%Z)) (ltac:(oD' 0xa9784%Z)).
sn (ltac:(oF' 0xa9788%Z)) (ltac:(oD' 0xa9788%Z)).
sn (ltac:(oF' 0xa978c%Z)) (ltac:(oD' 0xa978c%Z)).
stw (ltac:(oF' 0xa9790%Z)) (ltac:(oD' 0xa9790%Z)) (Z_to_bv 64 (bv_unsigned d + 276)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
stw (ltac:(oF' 0xa9794%Z)) (ltac:(oD' 0xa9794%Z)) (Z_to_bv 64 (bv_unsigned d + 280)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
stw (ltac:(oF' 0xa9798%Z)) (ltac:(oD' 0xa9798%Z)) (Z_to_bv 64 (bv_unsigned d + 284)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
stw (ltac:(oF' 0xa979c%Z)) (ltac:(oD' 0xa979c%Z)) (Z_to_bv 64 (bv_unsigned d + 288)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
stepb_ft (ltac:(oF' 0xa97a0%Z)) (ltac:(oD' 0xa97a0%Z)) ltac:(pin; cond_compute).
sn (ltac:(oF' 0xa97a4%Z)) (ltac:(oD' 0xa97a4%Z)).
sv (ltac:(oF' 0xa97a8%Z)) (ltac:(oD' 0xa97a8%Z)) (Z_to_bv 64 (bv_unsigned d + 24)).
sn (ltac:(oF' 0xa97ac%Z)) (ltac:(oD' 0xa97ac%Z)).
sn (ltac:(oF' 0xa97b0%Z)) (ltac:(oD' 0xa97b0%Z)).
sn (ltac:(oF' 0xa97b4%Z)) (ltac:(oD' 0xa97b4%Z)).
stw (ltac:(oF' 0xa97b8%Z)) (ltac:(oD' 0xa97b8%Z)) (Z_to_bv 64 (bv_unsigned d + 24)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
stw (ltac:(oF' 0xa97bc%Z)) (ltac:(oD' 0xa97bc%Z)) (Z_to_bv 64 (bv_unsigned d + 32)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
stw (ltac:(oF' 0xa97c0%Z)) (ltac:(oD' 0xa97c0%Z)) (Z_to_bv 64 (bv_unsigned d + 40)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
stw (ltac:(oF' 0xa97c4%Z)) (ltac:(oD' 0xa97c4%Z)) (Z_to_bv 64 (bv_unsigned d + 48)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
sn (ltac:(oF' 0xa97c8%Z)) (ltac:(oD' 0xa97c8%Z)).
sv (ltac:(oF' 0xa97cc%Z)) (ltac:(oD' 0xa97cc%Z)) (Z_to_bv 64 (bv_unsigned d + 56)).
stepb_tk (ltac:(oF' 0xa97d0%Z)) (ltac:(oD' 0xa97d0%Z)) ltac:(pin; cond_compute).
stw (ltac:(oF' 0xa97b8%Z)) (ltac:(oD' 0xa97b8%Z)) (Z_to_bv 64 (bv_unsigned d + 56)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
stw (ltac:(oF' 0xa97bc%Z)) (ltac:(oD' 0xa97bc%Z)) (Z_to_bv 64 (bv_unsigned d + 64)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
stw (ltac:(oF' 0xa97c0%Z)) (ltac:(oD' 0xa97c0%Z)) (Z_to_bv 64 (bv_unsigned d + 72)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
stw (ltac:(oF' 0xa97c4%Z)) (ltac:(oD' 0xa97c4%Z)) (Z_to_bv 64 (bv_unsigned d + 80)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
sn (ltac:(oF' 0xa97c8%Z)) (ltac:(oD' 0xa97c8%Z)).
sv (ltac:(oF' 0xa97cc%Z)) (ltac:(oD' 0xa97cc%Z)) (Z_to_bv 64 (bv_unsigned d + 88)).
stepb_tk (ltac:(oF' 0xa97d0%Z)) (ltac:(oD' 0xa97d0%Z)) ltac:(pin; cond_compute).
stw (ltac:(oF' 0xa97b8%Z)) (ltac:(oD' 0xa97b8%Z)) (Z_to_bv 64 (bv_unsigned d + 88)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
stw (ltac:(oF' 0xa97bc%Z)) (ltac:(oD' 0xa97bc%Z)) (Z_to_bv 64 (bv_unsigned d + 96)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
stw (ltac:(oF' 0xa97c0%Z)) (ltac:(oD' 0xa97c0%Z)) (Z_to_bv 64 (bv_unsigned d + 104)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
stw (ltac:(oF' 0xa97c4%Z)) (ltac:(oD' 0xa97c4%Z)) (Z_to_bv 64 (bv_unsigned d + 112)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
sn (ltac:(oF' 0xa97c8%Z)) (ltac:(oD' 0xa97c8%Z)).
sv (ltac:(oF' 0xa97cc%Z)) (ltac:(oD' 0xa97cc%Z)) (Z_to_bv 64 (bv_unsigned d + 120)).
stepb_tk (ltac:(oF' 0xa97d0%Z)) (ltac:(oD' 0xa97d0%Z)) ltac:(pin; cond_compute).
stw (ltac:(oF' 0xa97b8%Z)) (ltac:(oD' 0xa97b8%Z)) (Z_to_bv 64 (bv_unsigned d + 120)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
stw (ltac:(oF' 0xa97bc%Z)) (ltac:(oD' 0xa97bc%Z)) (Z_to_bv 64 (bv_unsigned d + 128)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
stw (ltac:(oF' 0xa97c0%Z)) (ltac:(oD' 0xa97c0%Z)) (Z_to_bv 64 (bv_unsigned d + 136)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
stw (ltac:(oF' 0xa97c4%Z)) (ltac:(oD' 0xa97c4%Z)) (Z_to_bv 64 (bv_unsigned d + 144)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
sn (ltac:(oF' 0xa97c8%Z)) (ltac:(oD' 0xa97c8%Z)).
sv (ltac:(oF' 0xa97cc%Z)) (ltac:(oD' 0xa97cc%Z)) (Z_to_bv 64 (bv_unsigned d + 152)).
stepb_tk (ltac:(oF' 0xa97d0%Z)) (ltac:(oD' 0xa97d0%Z)) ltac:(pin; cond_compute).
stw (ltac:(oF' 0xa97b8%Z)) (ltac:(oD' 0xa97b8%Z)) (Z_to_bv 64 (bv_unsigned d + 152)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
stw (ltac:(oF' 0xa97bc%Z)) (ltac:(oD' 0xa97bc%Z)) (Z_to_bv 64 (bv_unsigned d + 160)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
stw (ltac:(oF' 0xa97c0%Z)) (ltac:(oD' 0xa97c0%Z)) (Z_to_bv 64 (bv_unsigned d + 168)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
stw (ltac:(oF' 0xa97c4%Z)) (ltac:(oD' 0xa97c4%Z)) (Z_to_bv 64 (bv_unsigned d + 176)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
sn (ltac:(oF' 0xa97c8%Z)) (ltac:(oD' 0xa97c8%Z)).
sv (ltac:(oF' 0xa97cc%Z)) (ltac:(oD' 0xa97cc%Z)) (Z_to_bv 64 (bv_unsigned d + 184)).
stepb_tk (ltac:(oF' 0xa97d0%Z)) (ltac:(oD' 0xa97d0%Z)) ltac:(pin; cond_compute).
stw (ltac:(oF' 0xa97b8%Z)) (ltac:(oD' 0xa97b8%Z)) (Z_to_bv 64 (bv_unsigned d + 184)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
stw (ltac:(oF' 0xa97bc%Z)) (ltac:(oD' 0xa97bc%Z)) (Z_to_bv 64 (bv_unsigned d + 192)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
stw (ltac:(oF' 0xa97c0%Z)) (ltac:(oD' 0xa97c0%Z)) (Z_to_bv 64 (bv_unsigned d + 200)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
stw (ltac:(oF' 0xa97c4%Z)) (ltac:(oD' 0xa97c4%Z)) (Z_to_bv 64 (bv_unsigned d + 208)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
sn (ltac:(oF' 0xa97c8%Z)) (ltac:(oD' 0xa97c8%Z)).
sv (ltac:(oF' 0xa97cc%Z)) (ltac:(oD' 0xa97cc%Z)) (Z_to_bv 64 (bv_unsigned d + 216)).
stepb_tk (ltac:(oF' 0xa97d0%Z)) (ltac:(oD' 0xa97d0%Z)) ltac:(pin; cond_compute).
stw (ltac:(oF' 0xa97b8%Z)) (ltac:(oD' 0xa97b8%Z)) (Z_to_bv 64 (bv_unsigned d + 216)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
stw (ltac:(oF' 0xa97bc%Z)) (ltac:(oD' 0xa97bc%Z)) (Z_to_bv 64 (bv_unsigned d + 224)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
stw (ltac:(oF' 0xa97c0%Z)) (ltac:(oD' 0xa97c0%Z)) (Z_to_bv 64 (bv_unsigned d + 232)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
stw (ltac:(oF' 0xa97c4%Z)) (ltac:(oD' 0xa97c4%Z)) (Z_to_bv 64 (bv_unsigned d + 240)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
sn (ltac:(oF' 0xa97c8%Z)) (ltac:(oD' 0xa97c8%Z)).
sv (ltac:(oF' 0xa97cc%Z)) (ltac:(oD' 0xa97cc%Z)) (Z_to_bv 64 (bv_unsigned d + 248)).
stepb_tk (ltac:(oF' 0xa97d0%Z)) (ltac:(oD' 0xa97d0%Z)) ltac:(pin; cond_compute).
stw (ltac:(oF' 0xa97b8%Z)) (ltac:(oD' 0xa97b8%Z)) (Z_to_bv 64 (bv_unsigned d + 248)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
stw (ltac:(oF' 0xa97bc%Z)) (ltac:(oD' 0xa97bc%Z)) (Z_to_bv 64 (bv_unsigned d + 256)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
stw (ltac:(oF' 0xa97c0%Z)) (ltac:(oD' 0xa97c0%Z)) (Z_to_bv 64 (bv_unsigned d + 264)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
stw (ltac:(oF' 0xa97c4%Z)) (ltac:(oD' 0xa97c4%Z)) (Z_to_bv 64 (bv_unsigned d + 272)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
sn (ltac:(oF' 0xa97c8%Z)) (ltac:(oD' 0xa97c8%Z)).
sv (ltac:(oF' 0xa97cc%Z)) (ltac:(oD' 0xa97cc%Z)) (Z_to_bv 64 (bv_unsigned d + 280)).
stepb_ft (ltac:(oF' 0xa97d0%Z)) (ltac:(oD' 0xa97d0%Z)) ltac:(pin; cond_compute).
stepret (ltac:(oF' 0xa97d4%Z)) (ltac:(oD' 0xa97d4%Z)) ret ltac:(pin; reflexivity).
apply mst_refl.
- rewrite <- (zstores_cover d 304 Hnw memset304_ws mem 304%nat eq_refl memset304_ws_inb memset304_ws_cover).
reflexivity.
- unfold memset_clob. solve_regs_agree.
Qed.
End SE.
End FPX_1.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
