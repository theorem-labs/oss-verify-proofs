(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import
StartupTac ArgvEnv RefLayout Js0Img.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__Js0Startup1 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Js0Startup1.FPX_1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Js0Startup1.FPX_1.P1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.MemSplit."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1None"; "1cons"; "1length"; "1list"; "1nil"; "1option"; "2I"; "2and"; "2eq"; "2ex"; "3Z"; "0J"; "4bvmap"; "5msteps"; "7J1"; "6regs_init"]; ["8cmem"; "8wfJ"; "9getr"; "9mkst"; "9wrap_mem"; ":loaded_segments"; ":phdrs"; ";In"; "<le"; "<of_nat"; "<sub"; "0argc"; "0av"; "0envp"; "0ev"; "0fx"]; ["0hw"; "0pn"; "0r"; "0rdraw"; "0regs'"; "0rom"; "0sp0"; "=BV"; "=Z_to_bv"; "=bv"; "=bv_unsigned"; "0uid"]]).
Abbreviation SEGS := Plain.M.loaded_segments.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Abbreviation RPH := Plain.M.phdrs.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require PropExec.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import OtfKit.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Plain.
Local Ltac oF' pc := oF constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M.loaded_segments) pc.
Local Ltac oD' pc := oD constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M.loaded_segments) pc.
Local Ltac oE' pc := oE constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M.loaded_segments) pc.
Local Ltac oW' pc := oW constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M.loaded_segments) pc.
Section FPX_1. Context {fx : PropExec.FPState}.
Definition regs_init (sp0 : word) : bvmap 5 word :=
regupd (regupd bvmap_empty 10 (Z_to_bv 64 0)) 2 sp0.
Section P1.
Variable sp0 : word.
Variables av ev : list (list byte).
Variable uid : word.
Variable hw : word.
Variable rdraw : EntryDraw.
Hypothesis Hva : valid_argv av.
Hypothesis Hve : valid_envp ev.
Hypothesis Hlo : (0x7fff80000000 <= bv_unsigned sp0)%Z.
Hypothesis Hhi : (bv_unsigned sp0 <= 0x800000000000)%Z.
Hypothesis Hal : (bv_unsigned sp0 mod 16 = 0)%Z.
Local Notation mem0 := (wrap_mem RPH sp0 av ev uid hw rdraw) (only parsing).
Local Notation CM := (cmem sp0 (wrap_mem RPH sp0 av ev uid hw rdraw)) (only parsing).
Let argc : word := argcN av.
Local Notation argvp := (Z_to_bv 64 (bv_unsigned sp0 + 8)) (only parsing).
Let envp : word := envp_ptr sp0 av.
Let pn : word := cat_argv_ptr sp0 av ev 0.
Lemma u_argc : ltac2:(TCodec.tc2 tcn__Js0Startup1 "A'8':&Q:yR0vK%3221&I&2'3'Q9y8%211%411vL%7221%911%@3?;1").
Proof. exact (u_argcN av Hva). Qed.
Lemma len_av : ltac2:(TCodec.tc2 tcn__Js0Startup1 "A'7&H+1&I&2'3'Q9y8%211%411vL%7221%911%<2;1+QP0%>231%@231").
Proof. destruct Hva as [[H1 H2] _]. lia. Qed.
Definition J1 (J : word -> option byte) : word -> option byte :=
wbytes (wbytes (wbytes (wbytes
(wbytes (wbytes (wbytes (wbytes J
(Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
(Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
(Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
(Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
(Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0x98414)))
(Z_to_bv 64 (bv_unsigned sp0 - 48)) (word_to_le_bytes 8 argvp))
(Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 argc))
(Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (Z_to_bv 64 0x33bac)).
Section SE.
Local Abbreviation SEC_T_p1_run := (ltac2:(TCodec.tc2 tcn__Js0Startup1 "U='Q9yR0%211'5y8%511%311p051&AvQ6r1%3221'9&<y5%221='7'=&E&CvO&?%11=(Q7+V^c0(6%33I21/01I&@&D&FvLvNvQ;vQ0vQ3%776K54321r3(0%11Q2q0Q61%=4Q0541r4%H5GE@21+eUg0%F3Q<1D/01Q<&>%11;%E4Q8=19%O5NQ8418%Q23Q181'8&B+1%Q03Q91N%32Q>1&Q8+cP\D%22QJ1%83QJ41+2%Q73Q@1Q5%:2QE1&J&Q:%12R1QI+]0%4221%<2R41%B3R471+3%QA3QJ1Q?%D2QO1+RRP0%B2R:1%H3R:31+4%QG3R01QE%J2R51z%H2R@1%N3R@31+8%QM3R61QK%Q02R;1vQ1%Q33RE21+9%R23R;1R0%Q52R@1vM%Q83RJ21+:%R73R@1R5%Q:2RE1+[@%Q12O1%Q92S11%Q?3S141+;%R>3RG1R<%QA2RL1%QC3S51F+<%RB3RK1R@%QE2S01+Y@%QC2S;1%QI3S;31+B%RH3S11RF%QK2S61+V^m<%QI2SA1%QO3SA31%SD1S6&G(1+5%S13S:1RO+C%S33S<1S1+D%S53S>1S3+E%S73S@1S5+F%S93SB1S7+G%S;3SD1S9+H%S=3SF1S;+I%S?3SH1S=+J%SA3SJ1S?+K%SC3SL1SA(4%11H%G3I31%H3J61%I3K91%J3L<1%K3M?1%L3NB1%M3OE1%N3Q0H1%O3Q1K1%Q03Q2N1%Q23Q3T=1r2%S42SD1%S63TH1R9p041pR6Q81%T=2Q:1%T>2QA1%T?2QH1%T@2QM1%TA2R51%TB2R;1%TC2RA1%TD2RH1%TE2RO1%TF2S:1%TG2SD1qR:TI1%TM2TJ1p0TO1pHU41pR<U51")) (only parsing).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_p1_run) 0%nat 0%nat).
Variable J : ltac:(sec_ty2 constr:(SEC_T_p1_run) 1%nat 0%nat).
Lemma p1_run : ltac:(sec_stmt2 constr:(SEC_T_p1_run) 2%nat 0%nat).
Proof.
intros HJ.
pose proof len_av as Hlen. pose proof u_argc as Hargc.
eexists. split.
- unfold regs_init.
stepn (ltac:(oF' 0x33a60%Z)) (ltac:(oD' 0x33a60%Z)).
stepn (ltac:(oF' 0x33a64%Z)) (ltac:(oD' 0x33a64%Z)).
stepn (ltac:(oF' 0x33a68%Z)) (ltac:(oD' 0x33a68%Z)).
stepn (ltac:(oF' 0x33a6c%Z)) (ltac:(oD' 0x33a6c%Z)).
stepn (ltac:(oF' 0x33a70%Z)) (ltac:(oD' 0x33a70%Z)).
stepiv (ltac:(oF' 0x33a74%Z)) (ltac:(oD' 0x33a74%Z)) sp0 ltac:(gres; imm_norm; apply v_andi_m16_aligned; exact Hal).
stepn (ltac:(oF' 0x33a78%Z)) (ltac:(oD' 0x33a78%Z)).
chain_step; [reflexivity | eapply step_lw with (bs := word_to_le_bytes 4 argc) (v := argc);
[ exact (ltac:(oF' 0x33a7c%Z)) | reflexivity | exact (ltac:(oD' 0x33a7c%Z))
| addr_norm; rewrite rdn_cmem_above by region_side;
apply (rdn_low_bytes SEGS mem0 sp0 argc 4); [lia|];
exact (read_argc_w SEGS RPH sp0 av ev uid hw rdraw Hva Hve Hhi)
| apply bytes_le_to_Z_4_small; rewrite Hargc; lia ]
| step_simpl]; vnorm.
rewrite (v_lw_small argc) by (rewrite Hargc; lia).
stepn (ltac:(oF' 0x33a80%Z)) (ltac:(oD' 0x33a80%Z)).
stepn (ltac:(oF' 0x33a84%Z)) (ltac:(oD' 0x33a84%Z)).
stepn (ltac:(oF' 0x33a88%Z)) (ltac:(oD' 0x33a88%Z)).
chain_step; [reflexivity | eapply step_ld with (v := Z_to_bv 64 0x33bac);
[exact (ltac:(oF' 0x33a8c%Z)) | reflexivity | exact (ltac:(oD' 0x33a8c%Z)) | rd_img img_b4d40_8 | vm_compute; reflexivity] | step_simpl]; vnorm.
chain_step; [reflexivity | eapply step_ld with (v := Z_to_bv 64 0x98164);
[exact (ltac:(oF' 0x33a90%Z)) | reflexivity | exact (ltac:(oD' 0x33a90%Z)) | rd_img img_b4d48_8 | vm_compute; reflexivity] | step_simpl]; vnorm.
chain_step; [reflexivity | eapply step_ld with (v := Z_to_bv 64 0x98a80);
[exact (ltac:(oF' 0x33a94%Z)) | reflexivity | exact (ltac:(oD' 0x33a94%Z)) | rd_img img_b4d50_8 | vm_compute; reflexivity] | step_simpl]; vnorm.
sv (ltac:(oF' 0x33a98%Z)) (ltac:(oD' 0x33a98%Z)) (Z_to_bv 64 (bv_unsigned sp0 + 8)).
stepn (ltac:(oF' 0x33a9c%Z)) (ltac:(oD' 0x33a9c%Z)).
stepn (ltac:(oF' 0x33aa0%Z)) (ltac:(oD' 0x33aa0%Z)).
stepn (ltac:(oF' 0x33aa4%Z)) (ltac:(oD' 0x33aa4%Z)).
sv (ltac:(oF' 0x983e0%Z)) (ltac:(oD' 0x983e0%Z)) (Z_to_bv 64 (bv_unsigned sp0 - 32)).
stw (ltac:(oF' 0x983e4%Z)) (ltac:(oD' 0x983e4%Z)) (Z_to_bv 64 (bv_unsigned sp0 - 8)) (Z_to_bv 64 0) ltac:(ok_win HJ).
stw (ltac:(oF' 0x983e8%Z)) (ltac:(oD' 0x983e8%Z)) (Z_to_bv 64 (bv_unsigned sp0 - 16)) (Z_to_bv 64 0) ltac:(ok_win HJ).
stw (ltac:(oF' 0x983ec%Z)) (ltac:(oD' 0x983ec%Z)) (Z_to_bv 64 (bv_unsigned sp0 - 24)) (Z_to_bv 64 0) ltac:(ok_win HJ).
stw (ltac:(oF' 0x983f0%Z)) (ltac:(oD' 0x983f0%Z)) (Z_to_bv 64 (bv_unsigned sp0 - 32)) (Z_to_bv 64 0) ltac:(ok_win HJ).
stepn (ltac:(oF' 0x983f4%Z)) (ltac:(oD' 0x983f4%Z)).
stepn (ltac:(oF' 0x983f8%Z)) (ltac:(oD' 0x983f8%Z)).
stepn (ltac:(oF' 0x983fc%Z)) (ltac:(oD' 0x983fc%Z)).
chain_step; [reflexivity | eapply step_ld with (bs := word_to_le_bytes 8 pn) (v := pn);
[ exact (ltac:(oF' 0x98400%Z)) | reflexivity | exact (ltac:(oD' 0x98400%Z))
| addr_norm; rewrite rdn_cmem_above by region_side;
replace (Z_to_bv 64 (bv_unsigned sp0 + 8)) with (sp0 + nat_to_word (8 + 8 * 0))
by (rewrite word_add_nat; f_equal; lia);
exact (read_argv_ptr_w SEGS RPH sp0 av ev uid hw rdraw Hva Hve Hlo Hhi 0 ltac:(lia))
| apply bytes_le_to_Z_8 ]
| step_simpl]; vnorm.
stepiv (ltac:(oF' 0x98404%Z)) (ltac:(oD' 0x98404%Z)) (Z_to_bv 64 (8 * Z.of_nat (length av)))
ltac:(gres; imm_norm; rewrite <- Hargc; unfold v_slli; f_equal; rewrite Z.shiftl_mul_pow2 by lia; change (2^3)%Z with 8%Z; lia).
stepiv (ltac:(oF' 0x98408%Z)) (ltac:(oD' 0x98408%Z)) (Z_to_bv 64 (bv_unsigned sp0 + 8 + 8 * Z.of_nat (length av))) vclose.
stepiv (ltac:(oF' 0x9840c%Z)) (ltac:(oD' 0x9840c%Z)) envp
ltac:(gres; imm_norm; unfold envp, envp_ptr, v_addi; unorm; f_equal; lia).
stepn (ltac:(oF' 0x98410%Z)) (ltac:(oD' 0x98410%Z)).
sv (ltac:(oF' 0x98168%Z)) (ltac:(oD' 0x98168%Z)) (Z_to_bv 64 (bv_unsigned sp0 - 416)).
stw (ltac:(oF' 0x9816c%Z)) (ltac:(oD' 0x9816c%Z)) (Z_to_bv 64 (bv_unsigned sp0 - 40)) (Z_to_bv 64 0x98414) ltac:(ok_win HJ).
stw (ltac:(oF' 0x98170%Z)) (ltac:(oD' 0x98170%Z)) (Z_to_bv 64 (bv_unsigned sp0 - 48)) (Z_to_bv 64 (bv_unsigned sp0 + 8)) ltac:(ok_win HJ).
stw (ltac:(oF' 0x98174%Z)) (ltac:(oD' 0x98174%Z)) (Z_to_bv 64 (bv_unsigned sp0 - 56)) argc ltac:(ok_win HJ).
stw (ltac:(oF' 0x98178%Z)) (ltac:(oD' 0x98178%Z)) (Z_to_bv 64 (bv_unsigned sp0 - 64)) (Z_to_bv 64 0x33bac) ltac:(ok_win HJ).
stepn (ltac:(oF' 0x9817c%Z)) (ltac:(oD' 0x9817c%Z)).
stepn (ltac:(oF' 0x98180%Z)) (ltac:(oD' 0x98180%Z)).
sv (ltac:(oF' 0x98184%Z)) (ltac:(oD' 0x98184%Z)) (Z_to_bv 64 (bv_unsigned sp0 - 368)).
stepn (ltac:(oF' 0x98188%Z)) (ltac:(oD' 0x98188%Z)).
stepn (ltac:(oF' 0x9818c%Z)) (ltac:(oD' 0x9818c%Z)).
stepn (ltac:(oF' 0x98190%Z)) (ltac:(oD' 0x98190%Z)).
apply mst_refl.
- repeat split; gres; try reflexivity.
intros r Hr. cbn [In] in Hr.
repeat match goal with H : _ \/ _ |- _ => destruct H as [<-|H] end;
[ .. | contradiction]; gres; apply getr_empty.
Qed.
End SE.
End P1.
End FPX_1.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
