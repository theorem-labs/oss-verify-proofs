(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import
PropExec CatExec CatSim SeqExec StepTac Hoare StoreOk WalkTac RefMemcpyLib MemSplit As0StepLib Ja0RegionPoisoned Ja0AsanMemset Ja0ReadIcpt.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import OtfKit.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__Ja0DrvHIcpt () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ja0DrvHIcpt.FPX_1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ja0DrvHIcpt.FPX_1.RDPOSTE."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ja0ReadIcpt."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ja0RegionPoisoned."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.StoreOk."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1Some"; "1bool"; "1list"; "1option"; "1true"; "2I"; "2and"; "2eq"; "2ex"; "2not"; "3store_ok"; "3word_to_le_bytes"; "4bvmap"; "0M"; "5msteps"; "6EISDIR_RET"]; ["7RDE"; "8RIPL"; "9keeps_but"; ":getr"; ":mkst"; ":rdn"; ";mem_grows"; "<loaded_segments"; "=le"; "=lt"; "=sub"; "0fx"; "0ra"; "0regs"; "0regs'"; "0regs0"]; ["0rom"; "0s"; ">BV"; ">Z_to_bv"; ">bv"; ">bv_unsigned"; "0tp"; "0x"]]).
Local Ltac oF' pc := oF constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc.
Local Ltac oD' pc := oD constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc.
Local Ltac oE' pc := oE constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc.
Local Ltac oW' pc := oW constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
Section FPX_1. Context {fx : PropExec.FPState}.
#[local] Ltac rwH :=
repeat match goal with
| H : getr ?rg ?i = _ |- context [getr ?rg ?i] => rewrite !H
end.
#[local] Ltac unorm :=
repeat match goal with
| |- context [bv_unsigned (Z_to_bv 64 ?z)] =>
lazymatch z with context [Z_to_bv 64 _] => fail | _ => rewrite (u_Z2bv z) by lia end
end.
#[local] Ltac cond :=
rwH; unfold at_, v_addi, v_add, c_eq, c_ltu, bv_eqb, bv_ltu; imm_norm; unorm;
first [apply Z.eqb_eq | apply Z.eqb_neq | apply Z.ltb_lt | apply Z.ltb_ge]; lia.
#[local] Ltac wval :=
gres; rwH; unfold at_, v_addi, v_add, v_sub, v_srli; imm_norm; unorm; rewrite ?Z.shiftr_div_pow2 by lia;
try change (2 ^ 3)%Z with 8%Z; first [reflexivity | f_equal; lia].
#[local] Ltac vlit := gres; rwH; apply bv_eq; vm_compute; reflexivity.
#[local] Ltac peel0 :=
rewrite rdn_wbytes_out;
[ | rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.to_nat]; imm_norm; unorm; lia | cbn [Z.of_nat Pos.to_nat]; imm_norm; unorm; lia
| rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.to_nat]; imm_norm; unorm; lia ].
Definition ERRNO_OFF : Z := 164.
Definition EISDIR_RET : Z := 18446744073709551595.
Section RDPOSTE.
Variable rom : word -> option byte.
Variables ra : word.
Variables s tp : Z.
Hypothesis Hs : (0x1000000 <= s - 2200)%Z /\ (s < 2 ^ 64)%Z.
Hypothesis Htp : (4096 <= tp - 164)%Z /\ (tp <= s - 2200)%Z.
Hypothesis Hret : ret_ok ra.
Definition RDE (M : word -> option byte) : word -> option byte :=
wbytes (wbytes (wbytes M
(Z_to_bv 64 (s - 2136)) (word_to_le_bytes 8 (0x64c64 : word)))
(Z_to_bv 64 (s - 2144)) (word_to_le_bytes 8 (Z_to_bv 64 s)))
(Z_to_bv 64 (tp - 164)) (word_to_le_bytes 4 (Z_to_bv 64 21)).
Lemma RDE_out : ltac2:(TCodec.tc2 tcn__Ja0DrvHIcpt "Q?'Q4yR0%211'3y8%511%311p051&9'6&H&JvQ1+RS0%3221&Q5r1%22@1%8241&I+RR@%:291%3251%>251%@11vQ6+U4%@221r2%>2L1%D231+U0%E271%>241%I241%K11'7&@r4r3%3221%312%63Q421p081p0D1pR@Q;1pLQ71").
Proof.
intros M x N1 N2. unfold RDE. pose proof (u64_range x). destruct Hs as [S1' S2']. destruct Htp as [T1' T2'].
rewrite !wbytes_outside; first [reflexivity | rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.to_nat]; unorm; lia].
Qed.
Lemma RDE_grows : ltac2:(TCodec.tc2 tcn__Ja0DrvHIcpt ">'Q4yR0%211'3y8%511%311p051&Fr1&@%112%4231pL61").
Proof. intros M. unfold RDE. repeat (eapply mem_grows_trans; [|apply wbytes_grows]). apply mem_grows_refl. Qed.
Section SE.
Local Abbreviation SEC_T_read_icpt_post_err_run := (ltac2:(TCodec.tc2 tcn__Ja0DrvHIcpt "W4&<y5'Q4yR0%211%5241'3y8%611%311p061'7&Cr2(Q2+:(5%33@21%6251&Q3&?%22B1%;3B41r3+2%;3H19%>231&JvQ1+RS0%3221%<2L1%E3L61r4+1%E3Q21C%H231+QU\nH%H3Q31F/01Q3%M3Q441r5+8%M3Q:1K%Q0231%J2Q:A%Q33Q:21r6+D%Q33Q@1Q1%Q6231%Q02Q@A%Q93Q@21r7+4%Q93QF1Q7%Q<231vQ6%Q72QG1%Q@3QG31'1&:&G+RTH%Q52Q41%Q>2QN1uRTH%645>21(4%QJ3921r8+U4%Q=2?1%QF2R61u4%>4=521%R13@18'2%11R6%R911&Er9+RRH%QH2QG1%R12RA1u8%64H521(0&;+\cS4%R<3RG1R:/01RG%4271%62?1%RC3?81r:%R52R4QF%R>2RN1%B4Q431=vL%<2?1%>2G1%RK3G41r;+@%R>2R=1%RG2S71%K4Q=41Fr=%S121R2%F2I1%H2Q11%S53Q151r<+H%RH2RG1%S12SA1%Q54QG41Q0r>+9%S:3SG1S8%S=231%Q22Q51%Q42Q=1%SA3Q=71+Q0%S32S21%S<2SL1%Q@4R2D1Q;r?+B%SE3T21SC%SH231%Q=2Q@1%Q?2QH1%SL3QH71+Q8%S>2S=1%SG2T71%QK4R=E1QFr@+C%T03T=1SN%T3231%QH2QK1%QJ2R31%T73R371+Q@%SI2SH1%T22TB1%R64RHE1R1rA%T<21S7%R12R41%R32R<1%T@3R<51'8'6'>&DvKrB+QTf\8%TE3U01TC/01U0vQ0%75652?1r1&@%11B%;5:3R715%=3S=51%U025TK+_oooooooooooO%TK2U;1%U43U;31%U429TG%U63U=1T4%U62;T?%U83U?1R@%U82=T9rC%U:21T;%U<3UC31%U<2AR0%U=24R1%U?3UF21%U?2DQH%U@27QI%UB3UI21%UB2GQ@%UC2:QA%UE3UL21%UE2JT@%UF2=TA%UH3UO21&B&A%231Q5O%Q:241%Q;281%Q<2<1%Q=2@1%Q>2D1%Q?2I1%Q@2L1%QA2O1%QB2Q41qQNV;1%QE2V<1p0QG1p0R11p0R=1p0RI1p0S61p0SA1p0SJ1p0T=1p0TE1p0U01p0U81p0U?1p0UF1p0UO1p0V:1pLVG1pQLVM1pR0VN1")) (only parsing).
Variable regs0 : ltac:(sec_ty2 constr:(SEC_T_read_icpt_post_err_run) 0%nat 0%nat).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_read_icpt_post_err_run) 1%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_read_icpt_post_err_run) 2%nat 0%nat).
Theorem read_icpt_post_err_run : ltac:(sec_stmt2 constr:(SEC_T_read_icpt_post_err_run) 3%nat 0%nat).
Proof.
intros H10 H2 H1 H8 H20 H4 WOK EOK RA R1 R2 R3 R4 R5 R6.
destruct Hs as [S1' S2']. destruct Htp as [T1' T2']. unfold EISDIR_RET in H10.
assert (Rce : ret_ok (0x12b3d8 : word)) by (unfold ret_ok; apply bv_eq; vm_compute; reflexivity).
assert (R4e : ret_ok (0x64c64 : word)) by (unfold ret_ok; apply bv_eq; vm_compute; reflexivity).
assert (Rbd : ret_ok (Z_to_bv 64 1129628)) by (unfold ret_ok; apply bv_eq; vm_compute; reflexivity).
#[local] Ltac maddrE z := match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 z) by (symmetry; wval) end.
#[local] Ltac sokE WOK := match type of WOK with store_ok _ ?M0 _ _ = _ => apply (store_ok_mono _ _ M0) end; [repeat (eapply mem_grows_trans; [|apply wbytes_grows]); apply mem_grows_refl |];
apply (store_ok_sub ASEGS _ (Z_to_bv 64 (s - 2200)) _ 2200%nat); [unorm; cbn; lia | exact WOK | unorm; lia | unorm; cbn; lia].
eexists. split.
- stepret (ltac:(oF' 0x125988%Z)) (ltac:(oD' 0x125988%Z)) (0x12b3d8 : word) ltac:(rwH; reflexivity).
stepld (ltac:(oF' 0x12b3d8%Z)) (ltac:(oD' 0x12b3d8%Z)) (0x64c64 : word) ltac:(maddrE (s - 2136)%Z; exact RA).
stepiv (ltac:(oF' 0x12b3dc%Z)) (ltac:(oD' 0x12b3dc%Z)) (Z_to_bv 64 (s - 2128)) ltac:(wval).
stepn (ltac:(oF' 0x12b3e0%Z)) (ltac:(oD' 0x12b3e0%Z)).
stepn (ltac:(oF' 0x113c7c%Z)) (ltac:(oD' 0x113c7c%Z)).
stepn (ltac:(oF' 0x113c80%Z)) (ltac:(oD' 0x113c80%Z)).
stepb_ft (ltac:(oF' 0x113c84%Z)) (ltac:(oD' 0x113c84%Z)) ltac:(rwH; vm_compute; reflexivity).
stepiv (ltac:(oF' 0x113c88%Z)) (ltac:(oD' 0x113c88%Z)) (Z_to_bv 64 (s - 2144)) ltac:(wval).
stepsd (ltac:(oF' 0x113c8c%Z)) (ltac:(oD' 0x113c8c%Z)) (Z_to_bv 64 (s - 2136)) (0x64c64 : word) ltac:(sokE WOK).
stepsd (ltac:(oF' 0x113c90%Z)) (ltac:(oD' 0x113c90%Z)) (Z_to_bv 64 (s - 2144)) (Z_to_bv 64 s) ltac:(sokE WOK).
stepn (ltac:(oF' 0x113c94%Z)) (ltac:(oD' 0x113c94%Z)).
rewrite H10. replace (v_subw (Z_to_bv 64 0) (Z_to_bv 64 18446744073709551595)) with (Z_to_bv 64 21) by (apply bv_eq; vm_compute; reflexivity).
stepn (ltac:(oF' 0x113c98%Z)) (ltac:(oD' 0x113c98%Z)).
stepiv (ltac:(oF' 0x113550%Z)) (ltac:(oD' 0x113550%Z)) (Z_to_bv 64 tp) ltac:(wval).
stepiv (ltac:(oF' 0x113554%Z)) (ltac:(oD' 0x113554%Z)) (Z_to_bv 64 (tp - 164)) ltac:(wval).
stepret (ltac:(oF' 0x113558%Z)) (ltac:(oD' 0x113558%Z)) (Z_to_bv 64 1129628) ltac:(reflexivity).
chain_step; [ reflexivity
| eapply step_sw_at with (a := Z_to_bv 64 (tp - 164)) (v := Z_to_bv 64 21);
[ exact (ltac:(oF' 0x113c9c%Z)) | reflexivity | exact (ltac:(oD' 0x113c9c%Z)) | gres; imm_norm; rewrite ?v_addi_0; reflexivity | gres; reflexivity
| apply (store_ok_mono _ _ M); [repeat (eapply mem_grows_trans; [|apply wbytes_grows]); apply mem_grows_refl | exact EOK] ]
| step_simpl ].
stepn (ltac:(oF' 0x113ca0%Z)) (ltac:(oD' 0x113ca0%Z)).
stepld (ltac:(oF' 0x113ca4%Z)) (ltac:(oD' 0x113ca4%Z)) (0x64c64 : word) ltac:(maddrE (s - 2136)%Z; repeat peel0; apply rdn_wbytes_hit8; unorm; lia).
stepld (ltac:(oF' 0x113ca8%Z)) (ltac:(oD' 0x113ca8%Z)) (Z_to_bv 64 s) ltac:(maddrE (s - 2144)%Z; repeat peel0; apply rdn_wbytes_hit8; unorm; lia).
stepiv (ltac:(oF' 0x113cac%Z)) (ltac:(oD' 0x113cac%Z)) (Z_to_bv 64 (s - 2128)) ltac:(wval).
stepret (ltac:(oF' 0x113cb0%Z)) (ltac:(oD' 0x113cb0%Z)) (0x64c64 : word) ltac:(rwH; reflexivity).
stepb_ft (ltac:(oF' 0x64c64%Z)) (ltac:(oD' 0x64c64%Z)) ltac:(cond).
stepb_tk (ltac:(oF' 0x64c68%Z)) (ltac:(oD' 0x64c68%Z)) ltac:(rwH; vm_compute; reflexivity).
stepiv (ltac:(oF' 0x64cc4%Z)) (ltac:(oD' 0x64cc4%Z)) (Z_to_bv 64 (s - 2032)) ltac:(wval).
stepld (ltac:(oF' 0x64cc8%Z)) (ltac:(oD' 0x64cc8%Z)) ra ltac:(maddrE (s - 8)%Z; repeat peel0; exact R1).
stepld (ltac:(oF' 0x64ccc%Z)) (ltac:(oD' 0x64ccc%Z)) (getr regs0 8) ltac:(maddrE (s - 16)%Z; repeat peel0; exact R2).
stepld (ltac:(oF' 0x64cd0%Z)) (ltac:(oD' 0x64cd0%Z)) (getr regs0 9) ltac:(maddrE (s - 24)%Z; repeat peel0; exact R3).
stepld (ltac:(oF' 0x64cd4%Z)) (ltac:(oD' 0x64cd4%Z)) (getr regs0 18) ltac:(maddrE (s - 32)%Z; repeat peel0; exact R4).
stepld (ltac:(oF' 0x64cd8%Z)) (ltac:(oD' 0x64cd8%Z)) (getr regs0 19) ltac:(maddrE (s - 40)%Z; repeat peel0; exact R5).
stepld (ltac:(oF' 0x64cdc%Z)) (ltac:(oD' 0x64cdc%Z)) (getr regs0 20) ltac:(maddrE (s - 48)%Z; repeat peel0; exact R6).
stepiv (ltac:(oF' 0x64ce0%Z)) (ltac:(oD' 0x64ce0%Z)) (Z_to_bv 64 s) ltac:(wval).
stepret (ltac:(oF' 0x64ce4%Z)) (ltac:(oD' 0x64ce4%Z)) ra ltac:(rwH; reflexivity).
unfold RDE. apply mst_refl.
- repeat split; gres; rwH; try reflexivity. solve_keeps_but.
Qed.
End SE.
End RDPOSTE.
End FPX_1.
