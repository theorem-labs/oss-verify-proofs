(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import
PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk StreamSim MmapSim LibAtomic ExitSim ShapeAlg DivergeSim SpinAlg SpinAlgX Nodes Js0StdioDefs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__Js0StdioWrite_run1 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Js0StdioDefs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Js0StdioWrite_run1.FPX_1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1bool"; "1false"; "1option"; "1true"; "2I"; "2and"; "2eq"; "2ex"; "2not"; "3Z"; "4store_ok"; "5bvmap"; "6msteps"; "7ssp_cells"; "7sw_file"; "8mem_sw1"]; ["9c_lts"; "9getr"; "9mkst"; "9v_add"; "9v_and"; "9v_sltu"; "9v_sub"; "9v_subw"; "9v_xor"; ":loaded_segments"; ";add"; ";le"; ";lt"; ";pow"; ";sub"; "0a"]; ["0b"; "0bufp"; "0bufsz"; "0c"; "0can"; "0f"; "0fd"; "0fx"; "0l"; "0mem"; "0regs"; "0regs'"; "0ret"; "0rom"; "0s"; "<BV"]; ["<Z_to_bv"; "<bv"; "<bv_unsigned"; "0su"; "0wb"; "0wp"; "0x"; "0y"]]).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.RdnPeelKit.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import OtfKit.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Plain.
Local Ltac oF' pc := oF constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M.loaded_segments) pc.
Local Ltac oD' pc := oD constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M.loaded_segments) pc.
Local Ltac oE' pc := oE constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M.loaded_segments) pc.
Local Ltac oW' pc := oW constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M.loaded_segments) pc.
Local Ltac rdn_side_fast := rewrite ?length_N_to_le_bytes; cbn [Z.of_nat Pos.of_succ_nat Pos.succ length]; lia_fast.
Local Ltac rdn_solve_fast :=
lazymatch goal with
| |- rdn _ (wbytes _ ?a _) ?b _ = _ =>
tryif constr_eq a b then (apply rdn_wbytes_hit8; zsimp; lia)
else (first [ RdnPeelKit.rdn_peel_many ltac:(idtac; rdn_side_fast) | rdn_peel1 ]; rdn_solve_fast)
| |- _ => rdn_hyp
end.
Local Ltac rdn_solve ::= rdn_solve_fast.
Section FPX_1. Context {fx : PropExec.FPState}.
#[using="Type"] Lemma v_sub_Z : ltac2:(TCodec.tc2 tcn__Js0StdioWrite_run1 "Q2'9'5&Kzr1%3221r2%5231%7231&Lr3&M+2+R0%3221%6251'6'QAyR0%211&F&Q@r4%2251%326>%5221&N%125A%72:1%=3:41p0?1p0G1pR2Q01pR0Q11").
Proof. intros a b H H2. unfold v_sub. u_norm. reflexivity. Qed.
#[using="Type"] Lemma v_add_Z : ltac2:(TCodec.tc2 tcn__Js0StdioWrite_run1 "O'9'QAyR0%211'5&Kzr2%3221&L&M+2+R0%3221%5271%;271'6&C&Q@r3%22B1%421>&J&QB%12FA%3261%82H1%;3H61p0=1pRBJ1pR0N1").
Proof. intros a l H. unfold v_add. u_norm. reflexivity. Qed.
#[using="Type"] Lemma v_add_wZ : ltac2:(TCodec.tc2 tcn__Js0StdioWrite_run1 "Q0'QAyR0%211'9'5&Kzr1%3221&L&M+2+R0%3221%5271%;271'6&Cr3&Q@r2%22D1%5241&J&QB%12H7%3216%82J1%<3J61p0>1pR8K1pR2M1").
Proof. intros b c H. unfold v_add. u_norm. reflexivity. Qed.
#[using="Type"] Lemma v_add_ZZ' : ltac2:(TCodec.tc2 tcn__Js0StdioWrite_run1 "Q0'9'5&Kzr2%3221&L&M+2+R0%3221%5271%;271'6'QAyR0%211&C&Q@r4%2251r3%4271%6231&J%1264%82;1%>3;41p0@1p0A1pS@N1pS>O1").
Proof. intros. unfold v_add. u_norm. reflexivity. Qed.
#[using="Type"] Lemma sltu0_xor_ne : ltac2:(TCodec.tc2 tcn__Js0StdioWrite_run1 "Q7'9'5&Kzr2%3221&L&M+2+R0%3221%5271%;271&8'6r4r3%33A21%511'QAyR0%211&E&Q@%124E&Hr5%4271%528=%4221%8261+1%92<1%C3<31p0@1p0G1p0H1pR2Q51pR0Q61").
Proof.
intros a b Ha Hb Hne. unfold v_sltu, c_ltu, bv_ltu, v_xor.
rewrite (u_Z2bv a), (u_Z2bv b), (u_Z2bv 0) by lia.
pose proof (Z_lxor_range a b Ha Hb) as Hr.
rewrite u_Z2bv by lia.
destruct (Z.ltb_spec 0 (Z.lxor a b)) as [Hlt|Hge]; [reflexivity|].
exfalso. apply Hne. apply Z.lxor_eq. lia.
Qed.
#[using="Type"] Lemma sltu0_xor_eq : ltac2:(TCodec.tc2 tcn__Js0StdioWrite_run1 ">'QAyR0%211'6&E&Q@z%2261&Hr1%2211%7241%93:15pR0;1").
Proof.
intros a. unfold v_sltu, c_ltu, bv_ltu, v_xor. rewrite Z.lxor_nilpotent.
rewrite (u_Z2bv 0) by lia. reflexivity.
Qed.
#[using="Type"] Lemma sltu_ge : ltac2:(TCodec.tc2 tcn__Js0StdioWrite_run1 "Q0'9'5&Kzr1%3221r2%5231%7231&Lr3&M+2+R0%3221%6251'6'QAyR0%211&E&Q@r4%2251%326>%5221%528G%;3821p0=1p0E1pR2N1pR0O1").
Proof.
intros a b H H2. unfold v_sltu, c_ltu, bv_ltu. u_norm.
destruct (Z.ltb_spec a b); [lia|reflexivity].
Qed.
#[using="Type"] Lemma sltu_lt : ltac2:(TCodec.tc2 tcn__Js0StdioWrite_run1 "Q1'9'5&Kzr2%3221&Lr1%2241%8241&M+2+R0%3221%82:1'6'QAyR0%211&E&Q@r4%2251r3%4271%6231+1%72:1%=3:31p0?1p0E1pR2O1pR0Q01").
Proof.
intros a b H H2. unfold v_sltu, c_ltu, bv_ltu. u_norm.
destruct (Z.ltb_spec a b); [reflexivity|lia].
Qed.
#[using="Type"] Lemma c_lts_pos_0 : ltac2:(TCodec.tc2 tcn__Js0StdioWrite_run1 "J'9'5&Kzr1%3221&L&M+2+QO%3221%5271%;271'6'0&@&Q@yR0r2%3221%423A%6221(1%:3921p0<1pR0I1").
Proof.
intros a H. unfold c_lts, bv_lts. rewrite !bv_signed_small by (u_norm; lia). u_norm.
destruct (Z.ltb_spec a 0); [lia|reflexivity].
Qed.
#[using="Type"] Lemma v_and_0_l : ltac2:(TCodec.tc2 tcn__Js0StdioWrite_run1 "<'QAyR0%211'6&D&Q@z%2261r1%5221%73813pS>91").
Proof. intros x. unfold v_and. rewrite (u_Z2bv 0) by lia. rewrite Z.land_0_l. reflexivity. Qed.
#[using="Type"] Lemma v_and_m1_l : ltac2:(TCodec.tc2 tcn__Js0StdioWrite_run1 "K'9'5&Kzr1%3221&L&M+2+R0%3221%5271%;271'6'QAyR0%211&D&Q@+_oooooooooooO%2251r2%4271%6231%;3812p0=1pR0J1").
Proof.
intros a H. unfold v_and. u_norm.
change 18446744073709551615%Z with (Z.ones 64). rewrite Z.land_comm, Z.land_ones by lia.
f_equal. apply Z.mod_small. lia.
Qed.
#[using="Type"] Lemma v_subw_small_lit : ltac2:(TCodec.tc2 tcn__Js0StdioWrite_run1 "Q2'9'5&Kzr1%3221r2%5231%7231&Lr3&M+2+O%3221%6251'6'QAyR0%211&G&Q@r4%2251%326>%5221&N%125A%72:1%=3:41p0?1p0G1pR2Q01pR0Q11").
Proof.
intros a b H H2. unfold v_subw. u_norm.
rewrite bv_swrap_small by (change (bv_half_modulus 32) with (2^31)%Z; lia).
reflexivity.
Qed.
Definition mem_sw1 (mem : word -> option byte) (su : Z) (ra s0 s1 s2 s3 s4 s5 s6 : word)
(can : word) (wb n : Z) (s l : word) :=
wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes mem
(Z_to_bv 64 (su - 8)) (word_to_le_bytes 8 ra))
(Z_to_bv 64 (su - 16)) (word_to_le_bytes 8 s0))
(Z_to_bv 64 (su - 24)) (word_to_le_bytes 8 s1))
(Z_to_bv 64 (su - 32)) (word_to_le_bytes 8 s2))
(Z_to_bv 64 (su - 40)) (word_to_le_bytes 8 s3))
(Z_to_bv 64 (su - 48)) (word_to_le_bytes 8 s4))
(Z_to_bv 64 (su - 56)) (word_to_le_bytes 8 s5))
(Z_to_bv 64 (su - 64)) (word_to_le_bytes 8 s6))
(Z_to_bv 64 (su - 72)) (word_to_le_bytes 8 can))
(Z_to_bv 64 (su - 104)) (word_to_le_bytes 8 (Z_to_bv 64 wb)))
(Z_to_bv 64 (su - 96)) (word_to_le_bytes 8 (Z_to_bv 64 n)))
(Z_to_bv 64 (su - 88)) (word_to_le_bytes 8 s))
(Z_to_bv 64 (su - 80)) (word_to_le_bytes 8 l).
Section SE.
Local Abbreviation SEC_T_sw_enter := (ltac2:(TCodec.tc2 tcn__Js0StdioWrite_run1 "X<&;y5'QAyR0%211%5241'2y8%611%311p061'9'6&Ar>(Q?+2(4%33A21%6251&Q@r;%22C1%;3C41r?+:%;3I19%>231%@3H16r@+;%@3N1>%C231r8%F3N21rA+<%F3Q41D%I231%K3Q316rB+1%K3Q91I%N231r5%Q13Q921&K&J+TPPPPP0+S@%3221%521F+TPPPPPPPP0%72B1'0&:&IrD&N%12C:%Q82QI1uS@%746521(3%QD3:21+fdP0%D21JrC+W8%F221+lof@%I221'>rGr=%372B8Q3Q8QM1&=rH%2214'5&Lz%221?+RPPPPP0%42A1%6231rF%Q9261rE%9231%;231&M+R0%22R=1%>281%Q52FB&QB%12RNQ8%QC231%C21@'7'<&BvQ7rO+cgQH%RK3S71RI/01S7rNrM%8576321r1+cgV0%S23S>1S0/01S>&?rL+8%S73SE1S5%S:2?1+9%S:3SH1S8%S=2B1+B%S=3SK1S;%S@2E1+C%S@3SN1S>%SC2H1+D%SC3T11SA%SF2K1+E%SF3T41SD%SI2N1+F%SI3T71SG%SL2Q11rJrI%RB212%J?Q1IS5FC@=:74R:31R4QG%Q85Q7OL1Q1%Q:3RGQ11+A%T23T@1T0%T52Q31+R2%T02TA1%T93TA31%T92Q7SL%T32TDR:%T<3TD21%T<2Q:SJ+S8%S12Q71%T82TI1%TA3TI41%TA2Q?SI%T;2TLT?%TD3TL21%TD2QBT?%S82Q>SA%T?2U01%TH3U031%TH2QFQ?%TJ3U21R@%TJ2QHQ>rK%TE2U61%TN3U631%TN2QLQ?%U03U81=%U02QNQ>%U23U:1B%U22R0Q:%TL2U=S:%U53U=21%U52R3Q:%RC2U@RM%T52Q81%U12UB1%U:3UB41+3%U93UG1U7%U<2R:1%U=2RB2%U?3UG21+4%U>3UL1U<%UA2R?1%UB2RG2%UD3UL21+G%UC3V11UA%UF2RD1%UG2RL2%UI3V121+H%UH3V61UF%UK2RI1%UL2S12%UN3V621+I%UM3V;1UK%V02RN1%V12S62%V33V;21+J%V23V@1V0%V52S31%V62S;2%V83V@21+K%V73VE1V5%V:2S81%V;2S@2%V=3VE21%T;261%T<2<1%T=2B1%T>2H1%T?2N1%T@2Q41%TA2Q:1%TB2Q@1%TC2QD1%TD2QG1%TE2QJ1%TF2QO1%TG2R21%TH2R71%TI2R;1%TJ2RA1%TK2RE1%TL2RL1qRHW71%T92W81p0T;1p0TA1p0TF1p0TL1p0U41p0U81p0U=1p0UC1p0UF1p0V21p0V51p0V<1p0VC1p0VI1p0W01p0W61pRJWJ1pR:WK1pR6WL1pR4WM1pRBWN1pRNWO1pR>WI1pS<WJ1pS:WK1pR<WL1pS8WM1pRLWO1pRDX01pRFX61")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_sw_enter) 0%nat 0%nat).
Variable mem : ltac:(sec_ty2 constr:(SEC_T_sw_enter) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_sw_enter) 2%nat 0%nat).
Variable su : ltac:(sec_ty2 constr:(SEC_T_sw_enter) 3%nat 0%nat).
Variable f : ltac:(sec_ty2 constr:(SEC_T_sw_enter) 4%nat 0%nat).
Variable wb : ltac:(sec_ty2 constr:(SEC_T_sw_enter) 5%nat 0%nat).
Variable wp : ltac:(sec_ty2 constr:(SEC_T_sw_enter) 6%nat 0%nat).
Variable fd : ltac:(sec_ty2 constr:(SEC_T_sw_enter) 7%nat 0%nat).
Variable s : ltac:(sec_ty2 constr:(SEC_T_sw_enter) 8%nat 0%nat).
Variable l : ltac:(sec_ty2 constr:(SEC_T_sw_enter) 9%nat 0%nat).
Variable bufp : ltac:(sec_ty2 constr:(SEC_T_sw_enter) 10%nat 0%nat).
Variable bufsz : ltac:(sec_ty2 constr:(SEC_T_sw_enter) 11%nat 0%nat).
Variable can : ltac:(sec_ty2 constr:(SEC_T_sw_enter) 12%nat 0%nat).
Variable ret : ltac:(sec_ty2 constr:(SEC_T_sw_enter) 13%nat 0%nat).
Lemma sw_enter : ltac:(sec_stmt2 constr:(SEC_T_sw_enter) 14%nat 0%nat).
Proof using Type regs mem rom su f wb wp fd s l bufp bufsz can ret.
intros
Hsp Ha0 Ha1 Ha2 Hra SUlo SUhi SOK Flo Fhi [Fwp Fwb Ffd Fbuf Fbsz] [Ggot Gcan]
FD WBP WPhi SMALL.
zaddr Fwp; zaddr Fwb; zaddr Ffd; zaddr Fbuf; zaddr Fbsz.
unfold mem_sw1. eexists. split.
- stepn (ltac:(oF' 0x9dc38%Z)) (ltac:(oD' 0x9dc38%Z)). rewrite Hsp. sp_renorm.
stepST (ltac:(oF' 0x9dc3c%Z)) (ltac:(oD' 0x9dc3c%Z)) (Z_to_bv 64 (su - 8)) ret ltac:(sok_frame SOK).
stepST (ltac:(oF' 0x9dc40%Z)) (ltac:(oD' 0x9dc40%Z)) (Z_to_bv 64 (su - 16)) (getr regs 8) ltac:(sok_frame SOK).
stepST (ltac:(oF' 0x9dc44%Z)) (ltac:(oD' 0x9dc44%Z)) (Z_to_bv 64 (su - 24)) (getr regs 9) ltac:(sok_frame SOK).
stepST (ltac:(oF' 0x9dc48%Z)) (ltac:(oD' 0x9dc48%Z)) (Z_to_bv 64 (su - 32)) (getr regs 18) ltac:(sok_frame SOK).
stepST (ltac:(oF' 0x9dc4c%Z)) (ltac:(oD' 0x9dc4c%Z)) (Z_to_bv 64 (su - 40)) (getr regs 19) ltac:(sok_frame SOK).
stepST (ltac:(oF' 0x9dc50%Z)) (ltac:(oD' 0x9dc50%Z)) (Z_to_bv 64 (su - 48)) (getr regs 20) ltac:(sok_frame SOK).
stepST (ltac:(oF' 0x9dc54%Z)) (ltac:(oD' 0x9dc54%Z)) (Z_to_bv 64 (su - 56)) (getr regs 21) ltac:(sok_frame SOK).
stepST (ltac:(oF' 0x9dc58%Z)) (ltac:(oD' 0x9dc58%Z)) (Z_to_bv 64 (su - 64)) (getr regs 22) ltac:(sok_frame SOK).
stepn (ltac:(oF' 0x9dc5c%Z)) (ltac:(oD' 0x9dc5c%Z)). rewrite Ha2.
stepn (ltac:(oF' 0x9dc60%Z)) (ltac:(oD' 0x9dc60%Z)). rewrite Ha0.
stepn (ltac:(oF' 0x9dc64%Z)) (ltac:(oD' 0x9dc64%Z)).
stepLD8 (ltac:(oF' 0x9dc68%Z)) (ltac:(oD' 0x9dc68%Z)) (Z_to_bv 64 0xe7ed0).
stepLD8 (ltac:(oF' 0x9dc6c%Z)) (ltac:(oD' 0x9dc6c%Z)) can.
stepST (ltac:(oF' 0x9dc70%Z)) (ltac:(oD' 0x9dc70%Z)) (Z_to_bv 64 (su - 72)) can ltac:(sok_frame SOK).
stepLD8 (ltac:(oF' 0x9dc74%Z)) (ltac:(oD' 0x9dc74%Z)) (Z_to_bv 64 wp).
stepLD8 (ltac:(oF' 0x9dc78%Z)) (ltac:(oD' 0x9dc78%Z)) (Z_to_bv 64 wb).
stepn (ltac:(oF' 0x9dc7c%Z)) (ltac:(oD' 0x9dc7c%Z)). rewrite (v_sub_Z wp wb) by lia.
stepn (ltac:(oF' 0x9dc80%Z)) (ltac:(oD' 0x9dc80%Z)).
stepST (ltac:(oF' 0x9dc84%Z)) (ltac:(oD' 0x9dc84%Z)) (Z_to_bv 64 (su - 104)) (Z_to_bv 64 wb) ltac:(sok_frame SOK).
stepST (ltac:(oF' 0x9dc88%Z)) (ltac:(oD' 0x9dc88%Z)) (Z_to_bv 64 (su - 96)) (Z_to_bv 64 (wp - wb)) ltac:(sok_frame SOK).
stepST (ltac:(oF' 0x9dc8c%Z)) (ltac:(oD' 0x9dc8c%Z)) (Z_to_bv 64 (su - 88)) s ltac:(sok_frame SOK).
stepST (ltac:(oF' 0x9dc90%Z)) (ltac:(oD' 0x9dc90%Z)) (Z_to_bv 64 (su - 80)) l ltac:(sok_frame SOK).
stepn (ltac:(oF' 0x9dc94%Z)) (ltac:(oD' 0x9dc94%Z)). rewrite (v_add_Z (wp - wb) l) by lia.
stepn (ltac:(oF' 0x9dc98%Z)) (ltac:(oD' 0x9dc98%Z)). rewrite (sltu0_xor_ne wp wb) by lia.
stepb_ft (ltac:(oF' 0x9dc9c%Z)) (ltac:(oD' 0x9dc9c%Z)) ltac:(rewrite c_eq_Z by lia; apply Z.eqb_neq; lia).
stepn (ltac:(oF' 0x9dca0%Z)) (ltac:(oD' 0x9dca0%Z)).
replace (v_addi (Z_to_bv 64 (su - 112)) 8) with (Z_to_bv 64 (su - 104))
by (unfold v_addi; u_norm; f_equal; lia).
stepn (ltac:(oF' 0x9dca4%Z)) (ltac:(oD' 0x9dca4%Z)).
stepLD (ltac:(oF' 0x9dcac%Z)) (ltac:(oD' 0x9dcac%Z)) (word_to_le_bytes 4 (Z_to_bv 64 fd)) (Z_to_bv 64 fd)
ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
rewrite (v_lw_small fd) by lia.
stepn (ltac:(oF' 0x9dcb0%Z)) (ltac:(oD' 0x9dcb0%Z)).
stepn (ltac:(oF' 0x9dcb4%Z)) (ltac:(oD' 0x9dcb4%Z)).
stepn (ltac:(oF' 0x9dcb8%Z)) (ltac:(oD' 0x9dcb8%Z)).
stepn (ltac:(oF' 0x9dcbc%Z)) (ltac:(oD' 0x9dcbc%Z)).
apply mst_refl.
- repeat split; gres; try reflexivity.
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_sw_enter_eq := (ltac2:(TCodec.tc2 tcn__Js0StdioWrite_run1 "X0&;y5'QAyR0%211%5241'2y8%611%311p061'9'6&Ar=(Q?+2(4%33A21%6251&Q@r:%22C1%;3C41r>+:%;3I19%>231%@3H16r?+;%@3N1>%C231r8%F3N21r@+<%F3Q41D%I231%K3Q316rA+1%K3Q91I%N231r5%Q13Q921&K&J+TPPPPP0+S@%3221%521F+TPPPPPPPP0%72B1'0&:&IrC&N%12C:%Q82QI1uS@%746521(3%QD3:21+fdP0%D21JrB+W8%F221+lof@%I221'>rF%271A77Q2QBQL&=rG%221QO'5&Lz%221H+RPPPPP0%42J1%6231rE%Q8261&M+R0%22R91%;251%=251&QB%12RJQ4%?21<'7'<&BvQ7rM+cgQH%RF3S21RD/01S2rLrK%8576321r1+cgV0%RM3S91RK/01S9&?rJ+8%S23S@1S0%S52?1+9%S53SC1S3%S82B1+B%S83SF1S6%S;2E1+C%S;3SI1S9%S>2H1+D%S>3SL1S<%SA2K1+E%SA3SO1S?%SD2N1+F%SD3T21SB%SG2Q11rH%H?OGRNDA>;852R31QFQMQA%Q65Q5MJ1O%Q83R@O1+A%SK3T91SI%SN2Q11+R2%SI2T:1%T23T:31%T22Q5SE%SL2T=R4%T53T=21%T52Q8SC+RH%RJ2Q51%T12TB1%T:3TB41%T:2Q=SB%T42TES?%T=3TE21%T=2Q@T8%S12Q<S:%T82TI1%TA3TI31%TA2QDQ=%TC3TK1R:%TC2QFQ<rI%T>2TO1%TG3TO31%TG2QJQ=%TI3U11=%TI2QLQ<%TK3U31B%TK2QNQ8%TE2U6S3%TN3U621%TN2R1Q8%U03U81RG+3%TO3U=1TM%U22R51%U32R=2%U53U=21+4%U43UB1U2%U72R:1%U82RB2%U:3UB21+G%U93UG1U7%U<2R?1%U=2RG2%U?3UG21+H%U>3UL1U<%UA2RD1%UB2RL2%UD3UL21+I%UC3V11UA%UF2RI1%UG2S12%UI3V121+J%UH3V61UF%UK2RN1%UL2S62%UN3V621+K%UM3V;1UK%V02S31%V12S;2%V33V;21%T2261%T32<1%T42B1%T52H1%T62N1%T72Q41%T82Q:1%T92Q=1%T:2QA1%T;2QD1%T<2QG1%T=2QL1%T>2QO1%T?2R41%T@2R81%TA2R>1%TB2RB1%TC2RI1qRHVM1%T42VN1p0T61p0T:1p0TB1p0TJ1p0TN1p0U21p0U81p0U;1p0UG1p0UJ1p0V11p0V81p0V>1p0VE1p0VK1pRJW?1pR:W@1pR6WA1pR4WB1pRBWC1pRNWD1pR>W>1pS<W?1pR<W@1pS8WA1pRLWC1pRDWD1pRFWJ1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_sw_enter_eq) 0%nat 0%nat).
Variable mem : ltac:(sec_ty2 constr:(SEC_T_sw_enter_eq) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_sw_enter_eq) 2%nat 0%nat).
Variable su : ltac:(sec_ty2 constr:(SEC_T_sw_enter_eq) 3%nat 0%nat).
Variable f : ltac:(sec_ty2 constr:(SEC_T_sw_enter_eq) 4%nat 0%nat).
Variable wp : ltac:(sec_ty2 constr:(SEC_T_sw_enter_eq) 5%nat 0%nat).
Variable fd : ltac:(sec_ty2 constr:(SEC_T_sw_enter_eq) 6%nat 0%nat).
Variable s : ltac:(sec_ty2 constr:(SEC_T_sw_enter_eq) 7%nat 0%nat).
Variable l : ltac:(sec_ty2 constr:(SEC_T_sw_enter_eq) 8%nat 0%nat).
Variable bufp : ltac:(sec_ty2 constr:(SEC_T_sw_enter_eq) 9%nat 0%nat).
Variable bufsz : ltac:(sec_ty2 constr:(SEC_T_sw_enter_eq) 10%nat 0%nat).
Variable can : ltac:(sec_ty2 constr:(SEC_T_sw_enter_eq) 11%nat 0%nat).
Variable ret : ltac:(sec_ty2 constr:(SEC_T_sw_enter_eq) 12%nat 0%nat).
Lemma sw_enter_eq : ltac:(sec_stmt2 constr:(SEC_T_sw_enter_eq) 13%nat 0%nat).
Proof using Type regs mem rom su f wp fd s l bufp bufsz can ret.
intros
Hsp Ha0 Ha1 Ha2 Hra SUlo SUhi SOK Flo Fhi [Fwp Fwb Ffd Fbuf Fbsz] [Ggot Gcan]
FD WPhi SMALL.
pose proof (u64_range l) as Hl.
zaddr Fwp; zaddr Fwb; zaddr Ffd; zaddr Fbuf; zaddr Fbsz.
unfold mem_sw1. eexists. split.
- stepn (ltac:(oF' 0x9dc38%Z)) (ltac:(oD' 0x9dc38%Z)). rewrite Hsp. sp_renorm.
stepST (ltac:(oF' 0x9dc3c%Z)) (ltac:(oD' 0x9dc3c%Z)) (Z_to_bv 64 (su - 8)) ret ltac:(sok_frame SOK).
stepST (ltac:(oF' 0x9dc40%Z)) (ltac:(oD' 0x9dc40%Z)) (Z_to_bv 64 (su - 16)) (getr regs 8) ltac:(sok_frame SOK).
stepST (ltac:(oF' 0x9dc44%Z)) (ltac:(oD' 0x9dc44%Z)) (Z_to_bv 64 (su - 24)) (getr regs 9) ltac:(sok_frame SOK).
stepST (ltac:(oF' 0x9dc48%Z)) (ltac:(oD' 0x9dc48%Z)) (Z_to_bv 64 (su - 32)) (getr regs 18) ltac:(sok_frame SOK).
stepST (ltac:(oF' 0x9dc4c%Z)) (ltac:(oD' 0x9dc4c%Z)) (Z_to_bv 64 (su - 40)) (getr regs 19) ltac:(sok_frame SOK).
stepST (ltac:(oF' 0x9dc50%Z)) (ltac:(oD' 0x9dc50%Z)) (Z_to_bv 64 (su - 48)) (getr regs 20) ltac:(sok_frame SOK).
stepST (ltac:(oF' 0x9dc54%Z)) (ltac:(oD' 0x9dc54%Z)) (Z_to_bv 64 (su - 56)) (getr regs 21) ltac:(sok_frame SOK).
stepST (ltac:(oF' 0x9dc58%Z)) (ltac:(oD' 0x9dc58%Z)) (Z_to_bv 64 (su - 64)) (getr regs 22) ltac:(sok_frame SOK).
stepn (ltac:(oF' 0x9dc5c%Z)) (ltac:(oD' 0x9dc5c%Z)). rewrite Ha2.
stepn (ltac:(oF' 0x9dc60%Z)) (ltac:(oD' 0x9dc60%Z)). rewrite Ha0.
stepn (ltac:(oF' 0x9dc64%Z)) (ltac:(oD' 0x9dc64%Z)).
stepLD8 (ltac:(oF' 0x9dc68%Z)) (ltac:(oD' 0x9dc68%Z)) (Z_to_bv 64 0xe7ed0).
stepLD8 (ltac:(oF' 0x9dc6c%Z)) (ltac:(oD' 0x9dc6c%Z)) can.
stepST (ltac:(oF' 0x9dc70%Z)) (ltac:(oD' 0x9dc70%Z)) (Z_to_bv 64 (su - 72)) can ltac:(sok_frame SOK).
stepLD8 (ltac:(oF' 0x9dc74%Z)) (ltac:(oD' 0x9dc74%Z)) (Z_to_bv 64 wp).
stepLD8 (ltac:(oF' 0x9dc78%Z)) (ltac:(oD' 0x9dc78%Z)) (Z_to_bv 64 wp).
stepn (ltac:(oF' 0x9dc7c%Z)) (ltac:(oD' 0x9dc7c%Z)). rewrite (v_sub_Z wp wp) by lia. rewrite Z.sub_diag.
stepn (ltac:(oF' 0x9dc80%Z)) (ltac:(oD' 0x9dc80%Z)).
stepST (ltac:(oF' 0x9dc84%Z)) (ltac:(oD' 0x9dc84%Z)) (Z_to_bv 64 (su - 104)) (Z_to_bv 64 wp) ltac:(sok_frame SOK).
stepST (ltac:(oF' 0x9dc88%Z)) (ltac:(oD' 0x9dc88%Z)) (Z_to_bv 64 (su - 96)) (Z_to_bv 64 0) ltac:(sok_frame SOK).
stepST (ltac:(oF' 0x9dc8c%Z)) (ltac:(oD' 0x9dc8c%Z)) (Z_to_bv 64 (su - 88)) s ltac:(sok_frame SOK).
stepST (ltac:(oF' 0x9dc90%Z)) (ltac:(oD' 0x9dc90%Z)) (Z_to_bv 64 (su - 80)) l ltac:(sok_frame SOK).
stepn (ltac:(oF' 0x9dc94%Z)) (ltac:(oD' 0x9dc94%Z)).
stepn (ltac:(oF' 0x9dc98%Z)) (ltac:(oD' 0x9dc98%Z)). rewrite sltu0_xor_eq.
stepb_tk (ltac:(oF' 0x9dc9c%Z)) (ltac:(oD' 0x9dc9c%Z)) ltac:(apply c_eq_refl).
stepn (ltac:(oF' 0x9dca8%Z)) (ltac:(oD' 0x9dca8%Z)).
replace (v_addi (Z_to_bv 64 (su - 112)) 24) with (Z_to_bv 64 (su - 88))
by (unfold v_addi; u_norm; f_equal; lia).
stepLD (ltac:(oF' 0x9dcac%Z)) (ltac:(oD' 0x9dcac%Z)) (word_to_le_bytes 4 (Z_to_bv 64 fd)) (Z_to_bv 64 fd)
ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
rewrite (v_lw_small fd) by lia.
stepn (ltac:(oF' 0x9dcb0%Z)) (ltac:(oD' 0x9dcb0%Z)).
stepn (ltac:(oF' 0x9dcb4%Z)) (ltac:(oD' 0x9dcb4%Z)).
stepn (ltac:(oF' 0x9dcb8%Z)) (ltac:(oD' 0x9dcb8%Z)).
stepn (ltac:(oF' 0x9dcbc%Z)) (ltac:(oD' 0x9dcbc%Z)).
apply mst_refl.
- repeat split; gres; try reflexivity.
Qed.
End SE.
End FPX_1.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
