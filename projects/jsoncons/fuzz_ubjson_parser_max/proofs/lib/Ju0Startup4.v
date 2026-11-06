(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import
StartupTac ArgvEnv RefLayout Ju0Img Ju0StartupDefs.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__Ju0Startup4 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Init.Nat."; "Corelib.Init.Peano."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.MemImageType."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.LinuxProcessSem.StackLayout."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Hoare."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ju0StartupDefs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.MemSplit."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.StartupTac."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Ubsan.M."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1O"; "1Some"; "1cons"; "1length"; "1list"; "1nat"; "1nil"; "1option"; "2I"; "2and"; "2eq"; "3add"; "4le"; "5firstn"; "5skipn"; "6Z"]; ["0D"; "0G"; "0J"; "0Jb"; "7Segment"; "8machine_state"; "8word_to_le_bytes"; "9at_random_bytes"; "9ed_random"; ":sp_window_hi"; ":sp_window_lo"; ";bvmap"; "<wbytes"; "=regs_agree"; ">D_libc"; ">J_aux"]; [">J_lsm"; ">argc_w"; ">canary_w"; ">pn_w"; ">rlw"; ">rnd_w"; "?cmem"; "?wfJ"; "@getr"; "@mkst"; "@rdn"; "@v_slli"; "@wrap_mem"; "Abwd"; "Bloaded_segments"; "Bphdrs"]; ["CIn"; "Dadd"; "Dle"; "Dlt"; "Dmodulo"; "Dmul"; "Dof_nat"; "Dpow"; "Dsub"; "0a"; "0a'"; "0av"; "0ev"; "0fx"; "0hw"; "0j"]; ["0m"; "0n"; "0r"; "0rdraw"; "0regs"; "0regs'"; "0rom"; "0s1v"; "0segs"; "0sp0"; "EBV"; "EZ_to_bv"; "Ebv"; "Ebv_unsigned"; "0tid"; "0uid"]]).
Abbreviation SEGS := Ubsan.M.loaded_segments.
Abbreviation RPH := Ubsan.M.phdrs.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require PropExec.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import OtfKit.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Ubsan.
Local Ltac oF' pc := oF constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Ubsan.M.loaded_segments) pc.
Local Ltac oD' pc := oD constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Ubsan.M.loaded_segments) pc.
Local Ltac oE' pc := oE constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Ubsan.M.loaded_segments) pc.
Local Ltac oW' pc := oW constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Ubsan.M.loaded_segments) pc.
Section FPX_1. Context {fx : PropExec.FPState}.
Section P.
Variable sp0 : word.
Variable Jb : word -> option byte.
Variables av ev : list (list byte).
Variable uid : word.
Variable hw : word.
Variable rdraw : EntryDraw.
Hypothesis Hva : valid_argv av.
Hypothesis Hve : valid_envp ev.
Hypothesis Hlo : (0x7fff80000000 <= bv_unsigned sp0)%Z.
Hypothesis Hhi : (bv_unsigned sp0 <= 0x800000000000)%Z.
Hypothesis Hal : (bv_unsigned sp0 mod 16 = 0)%Z.
Local Notation RND := (ed_random rdraw) (only parsing).
Local Notation CM := (cmem sp0 (wrap_mem RPH sp0 av ev uid hw rdraw)) (only parsing).
Lemma Hsp_lo' : ltac2:(TCodec.tc2 tcn__Ju0Startup4 "7&QB&J&R=yR0vR9%3221%6251"). Proof. exact Hlo. Qed.
Lemma Hsp_hi' : ltac2:(TCodec.tc2 tcn__Ju0Startup4 "7&QB&R=yR0vR9%3221&I%6221"). Proof. exact Hhi. Qed.
Lemma len_av : ltac2:(TCodec.tc2 tcn__Ju0Startup4 "A'9&QB+1&QF&3'4'R<y8%211%411vQK%7221%911%<2;1+QP0%>231%@231").
Proof. destruct Hva as [[H1 H2] _]. lia. Qed.
Lemma rnd_bounds : ltac2:(TCodec.tc2 tcn__Ju0Startup4 "N'9&QB&R=yR0vR9%3221&Q5vQKvQL%33521%8271%:261&QC&QA+@%2251&QG+2+R0%3221%8251':'?&QD+8%22?1z%63521%L281%M2B1").
Proof.
destruct (rnd_facts SEGS RPH sp0 rdraw av ev uid hw Hva Hve Hsp_lo' Hsp_hi' Hal) as (A & B & C & D & _).
unfold rnd_w. repeat split; lia.
Qed.
Lemma rd_rnd : ltac2:(TCodec.tc2 tcn__Ju0Startup4 "QO'R<yR0%211'7y8%511%311p051'5'<&;r2r1%3221u@%6221':'4%11=%@11&Q:&Q>&Q6vR9&Q<&Q?vQKvQLvR?vQNvR3%776854321r5r4%<4;321&R;&QA&R=&Q5%13@=<%32Q71&QFr3%211%8241%:2Q<1%J4I<1Q3(1&=&>&G&H%11F%311%53QA<1%73QBQ<1%92Q61%Q93Q6;1p0Q;1pT4QC1pT0QD1pQ2QF1pQ6QG1").
Proof.
intros J D j n Hjn.
destruct (rnd_facts SEGS RPH sp0 rdraw av ev uid hw Hva Hve Hsp_lo' Hsp_hi' Hal) as (A & B & C & D' & E).
unfold rnd_w. rewrite rdn_cmem_above by (unorm; lia).
rewrite rdn_wrap_stack_above by (unorm; lia). apply E. exact Hjn.
Qed.
Lemma rdn_addr : ltac2:(TCodec.tc2 tcn__Ju0Startup4 "Q5'4'D%211'R<yR0%211'7y8%511%311p051'5%<14%711':&Q:r6r5r3r2%544321r1%83921r4%:3C71r8r7%<421;4%>3?1:p051p081pT6B1pT4E1pSFL1pSDM1pT2I1pTBQ21").
Proof. intros; subst; reflexivity. Qed.
Ltac RD_RND j :=
eapply rdn_addr; [ rewrite <- (rnd4_eq RND j) by reflexivity; apply (rd_rnd _ _ j 4); cbn; lia
| cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; first [reflexivity | symmetry; apply at_self | f_equal; lia] ].
Ltac RD_GUARD :=
rewrite rdn_cmem_data by region_side;
lazymatch goal with
| |- rdn _ (wbytes (wbytes (wbytes ?DD (Z_to_bv 64 ?g) _) _ _) _ _) _ _ = _ =>
let H := fresh in
pose proof (rd_guard_at SEGS DD RND g ltac:(lia) ltac:(lia)) as H;
cbn [Z.add Pos.add Pos.succ] in H; exact H
end.
Lemma slli_argc : ltac2:(TCodec.tc2 tcn__Ju0Startup4 "H':'R<yR0%211&Q;&Q1vQK%211+3%5221&R;&QE+8&QF&3'4y8%@11%311%521=%711%:291%<2D1%G3D>1").
Proof.
pose proof len_av. unfold argc_w, v_slli. rewrite (u_argcN av Hva).
f_equal. rewrite Z.shiftl_mul_pow2 by lia. change (2^3)%Z with 8%Z. lia.
Qed.
Section SE.
Local Abbreviation SEC_T_fin_c6 := (ltac2:(TCodec.tc2 tcn__Ju0Startup4 "[F'E!p021&Q=&Q>r1%3221&Ky5'R<yR0%211%5241'7y8%611%311p061&Q7vR9vC%3221':&Q8r5(R:+2(8%33D21%6251&R;&QH&R=%12G>+]0%4221%62J1%?3J81r6+3%?3Q01=%B231+RRP0%=2Q11%F3Q131r7+4%F3Q71D%I231+iSU@%D2Q81%M3Q831r8+C%M3Q>1K%Q0231z%K2Q?1%Q43Q?31r9+D%Q43QE1Q2%Q7231%Q93QD16r:+E%Q93QJ1Q7%Q<231%Q>3QI1;r;+F%Q>3QO1Q<%QA231%QC3QN1@r<+G%QC3R41QA%QF231%QH3R31Er=+H%QH3R91QF%QK231%QM3R81Jr>+I%QM3R>1QK%R0231%R23R=1Or?+J%R23RC1R0%R5231%R73RB1Q4r@+K%R73RH1R5%R:231%R<3RG1Q9%R<2RNR7%R>3RI1R0r2%R?21QN%RA3RL1QLr3%RB21QJ%RD3RO1QHr4%RE21QF%RG3S21QD%RG2RFQA%RI3S41QF%RI2R:Q>%RK3S61QH%RK2R5Q;%RM3S81QJ%RM2R0Q8%RO3S:1QL%RO2QKQ5%S13S<1QN%S12QHQ2%S33S>1R0%S32QEO%S53S@1R2%S52QBL%S73SB1R4&M%SF1SG&Q@(2+1%S:3SK1S8+:%S<3SM1S:+;%S>3SO1S<+<%S@3T11S>+=%SB3T31S@+>%SD3T51SB+?%SF3T71SD(6%11B%A3C31%B3D61%C3E91%D3F<1%E3G?1%F3HB1%G3ISL1%H3JF1%J3KTE1qT6L1rN%O321R>rQ1&Q9vQM+cTfD%T93TH1T7/01TH&Q6&Q<&Q?vQKvQLvR?vQNvR3%776TI54321&L&O&Q0%13TM9TL%36TN:9871+]8%TD2TB1%TF2U:1&Fu8+cTf<%TJ2U>1%4231%=3961+]@%TM2TK1%TO2UC1&Q3%13U<HG%;2:1%D3741+]H%U42U21%U62UJ1rM%A2@1%J3631+^0%U:2U81%U<2V01+mSj0%U>2V21%H2G1%Q13741+^8%UA2U?1%UC2V71%M2LTI%Q63521+^@%UF2UD1%UH2V<1%Q:3415+^H%UJ2UH1%UL2V@1%Q>3419%UN2VBQK%Q82Q71%QA33Q:1&N%14V=QIQHQF+mSVH%V42VH1%QF331A+mSW8%V72VK1%QI331D+mSW0%V:2VN1+8%V<2W01%QF2QE1%QO3641+mSjH%V@2W41+W0%VB2W61%QL2QK1%R53641+mSk0%VF2W:1%R8331:+iSV0%VI2W=1%R;331Q6+iSU8%VL2W@1%R62R54%R?3421+iRo8%W02WD1%R:2R91%RC3421%W32WCSO%SB1WC%T23WD21%RG34QH1+iSP@%W82WL1u4%W:2WNW>%RD221%RM3641+iSP8%W>2X21rL%RI271%S23531+iST0%WC2X71+mSkH%WE2X91%RO2RN1%S83641+iSS0%WI2X=1%S32S21%S<3421+iRo@%WM2XA1%S?331M+iRoH%X02XD1%SB331Q0+iSP0%X32XG1%SE331R@+mSi0%X62XJ1&Q4&H%11SL(0%4221%SE2Q31%SN3971+mSi4%X?2Y31%927Q7%SJ2Q81%T33531+mSi1%XD2Y81%XE2Y5WK%UC3Y51QB%T83531+iSU0%XI2Y=1&Q2%11B%T52T41%T>3641%TH4Y9T@RN1%TN5TMW9TJ1U1%U011p0U21p0V31p0V61p0V91p0V<1p0V?1p0VB1p0VE1p0VH1p0VK1p0VO1p0W31p0W71pT<Z01rDrB%YF3Z5THYD/01Z5%TL2TKWC%U53TAT>1%U631T9T6%U731T3T2%U831SOT3%U931SLT4%U22R@WN%U;3R>R<1%U<31R8R5%U=31R3R2%U>31R0RL%U?31QNRM%U@31QLT;%UJ4Z;UB81rA%V15V0B@21%D11p0F1p0X11p0X71p0X=1p0XC1p0XI1p0XO1p0Y51p0Y;1p0YA1p0YI1p0Z11p0Z91p0ZJ1pTN[51pT@[61pT>[11pT:[71p0[>1pQ4[C1")) (only parsing).
Variable G : ltac:(sec_ty2 constr:(SEC_T_fin_c6) 0%nat 0%nat).
Lemma fin_c6 : ltac:(sec_stmt2 constr:(SEC_T_fin_c6) 1%nat 0%nat).
Proof.
intros HG regs rom s1v tid HJ H2 H3 H4 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
eapply HG.
{ ld_step (ltac:(oF' 0x992cc%Z)) (ltac:(oD' 0x992cc%Z)) (word_to_le_bytes 8 (rnd_w sp0 av ev)) (rnd_w sp0 av ev) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
sn (ltac:(oF' 0x992d0%Z)) (ltac:(oD' 0x992d0%Z)).
sv (ltac:(oF' 0x99c7c%Z)) (ltac:(oD' 0x99c7c%Z)) (Z_to_bv 64 (bv_unsigned sp0 - 432)).
stw (ltac:(oF' 0x99c80%Z)) (ltac:(oD' 0x99c80%Z)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (Z_to_bv 64 627412) ltac:(ok_win HJ).
stepb_ft (ltac:(oF' 0x99c84%Z)) (ltac:(oD' 0x99c84%Z)) ltac:(pin; apply c_eq_0_false; pose proof rnd_bounds; lia).
sv (ltac:(oF' 0x99c88%Z)) (ltac:(oD' 0x99c88%Z)) (rnd_w sp0 av ev).
sn (ltac:(oF' 0x99c8c%Z)) (ltac:(oD' 0x99c8c%Z)).
ld_step (ltac:(oF' 0x99c90%Z)) (ltac:(oD' 0x99c90%Z)) (word_to_le_bytes 8 (Z_to_bv 64 954144)) (Z_to_bv 64 954144) ltac:(rd_img img_b5f18_8) ltac:(apply bytes_le_to_Z_8).
sn (ltac:(oF' 0x99c94%Z)) (ltac:(oD' 0x99c94%Z)).
sn (ltac:(oF' 0x99c98%Z)) (ltac:(oD' 0x99c98%Z)).
stepiv (ltac:(oF' 0xaa1b4%Z)) (ltac:(oD' 0xaa1b4%Z)) (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; apply v_andi_3_aligned; pose proof rnd_bounds as (_ & _ & RB); rewrite <- (Z.mod_mod_divide _ 8 4) by (exists 2%Z; reflexivity); rewrite RB; reflexivity).
stepb_tk (ltac:(oF' 0xaa1b8%Z)) (ltac:(oD' 0xaa1b8%Z)) ltac:(pin; cond_compute).
sn (ltac:(oF' 0xaa2c8%Z)) (ltac:(oD' 0xaa2c8%Z)).
sn (ltac:(oF' 0xaa2cc%Z)) (ltac:(oD' 0xaa2cc%Z)).
stepb_ft (ltac:(oF' 0xaa2d0%Z)) (ltac:(oD' 0xaa2d0%Z)) ltac:(pin; cond_compute).
sn (ltac:(oF' 0xaa2d4%Z)) (ltac:(oD' 0xaa2d4%Z)).
stepb_tk (ltac:(oF' 0xaa2d8%Z)) (ltac:(oD' 0xaa2d8%Z)) ltac:(pin; cond_compute).
sn (ltac:(oF' 0xaa310%Z)) (ltac:(oD' 0xaa310%Z)).
stepb_ft (ltac:(oF' 0xaa314%Z)) (ltac:(oD' 0xaa314%Z)) ltac:(pin; cond_compute).
ld_step (ltac:(oF' 0xaa318%Z)) (ltac:(oD' 0xaa318%Z)) (rnd4 RND 0) (rnd4w RND 0) ltac:(RD_RND 0%nat) ltac:(apply rnd4_val).
ld_step (ltac:(oF' 0xaa31c%Z)) (ltac:(oD' 0xaa31c%Z)) (rnd4 RND 4) (rnd4w RND 4) ltac:(RD_RND 4%nat) ltac:(apply rnd4_val).
stw (ltac:(oF' 0xaa320%Z)) (ltac:(oD' 0xaa320%Z)) (Z_to_bv 64 954144) (rlw RND 0) ltac:(ok_data).
stw (ltac:(oF' 0xaa324%Z)) (ltac:(oD' 0xaa324%Z)) (Z_to_bv 64 954148) (rlw RND 4) ltac:(ok_data).
sn (ltac:(oF' 0xaa328%Z)) (ltac:(oD' 0xaa328%Z)).
sv (ltac:(oF' 0xaa32c%Z)) (ltac:(oD' 0xaa32c%Z)) (Z_to_bv 64 (bv_unsigned (rnd_w sp0 av ev) + 8)).
sn (ltac:(oF' 0xaa330%Z)) (ltac:(oD' 0xaa330%Z)).
stepb_tk (ltac:(oF' 0xaa334%Z)) (ltac:(oD' 0xaa334%Z)) ltac:(pin; cond_compute).
sn (ltac:(oF' 0xaa574%Z)) (ltac:(oD' 0xaa574%Z)).
stepb_ft (ltac:(oF' 0xaa578%Z)) (ltac:(oD' 0xaa578%Z)) ltac:(pin; cond_compute).
sn (ltac:(oF' 0xaa57c%Z)) (ltac:(oD' 0xaa57c%Z)).
stepb_ft (ltac:(oF' 0xaa580%Z)) (ltac:(oD' 0xaa580%Z)) ltac:(pin; cond_compute).
stepret (ltac:(oF' 0xaa584%Z)) (ltac:(oD' 0xaa584%Z)) (0x99c9c : word) ltac:(pin; first [reflexivity | bveq]).
sn (ltac:(oF' 0x99c9c%Z)) (ltac:(oD' 0x99c9c%Z)).
sn (ltac:(oF' 0x99cb8%Z)) (ltac:(oD' 0x99cb8%Z)).
ld_step (ltac:(oF' 0x99cbc%Z)) (ltac:(oD' 0x99cbc%Z)) (word_to_le_bytes 8 (Z_to_bv 64 954144)) (Z_to_bv 64 954144) ltac:(rd_img img_b5f18_8) ltac:(apply bytes_le_to_Z_8).
stw (ltac:(oF' 0x99cc0%Z)) (ltac:(oD' 0x99cc0%Z)) (Z_to_bv 64 954145) (Z_to_bv 64 0) ltac:(ok_data).
ld_step (ltac:(oF' 0x99cc4%Z)) (ltac:(oD' 0x99cc4%Z)) (guard_bytes RND) (canary_w RND) ltac:(RD_GUARD) ltac:(apply canary_val).
sn (ltac:(oF' 0x99cc8%Z)) (ltac:(oD' 0x99cc8%Z)).
stw (ltac:(oF' 0x99ccc%Z)) (ltac:(oD' 0x99ccc%Z)) (Z_to_bv 64 822432) (canary_w RND) ltac:(ok_data).
ld_step (ltac:(oF' 0x99cd0%Z)) (ltac:(oD' 0x99cd0%Z)) (word_to_le_bytes 8 (Z_to_bv 64 627412)) (Z_to_bv 64 627412) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
sv (ltac:(oF' 0x99cd4%Z)) (ltac:(oD' 0x99cd4%Z)) (Z_to_bv 64 (bv_unsigned sp0 - 416)).
stepret (ltac:(oF' 0x99cd8%Z)) (ltac:(oD' 0x99cd8%Z)) (0x992d4 : word) ltac:(pin; first [reflexivity | bveq]).
apply mst_refl. }
apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
ra_chain.
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_fin_c7 := (ltac2:(TCodec.tc2 tcn__Ju0Startup4 "\L'E!p021&Q=&Q>r1%3221&Ky5'R<yR0%211%5241'7y8%611%311p061&Q7vR9vC%3221':&Q8r5(R:+2(8%33D21%6251&R;&QH&R=%12G>+]0%4221%62J1%?3J81r6+3%?3Q01=%B231+RRP0%=2Q11%F3Q131r7+4%F3Q71D%I231+iSU@%D2Q81%M3Q831r8+C%M3Q>1K%Q0231z%K2Q?1%Q43Q?31r9+D%Q43QE1Q2%Q7231%Q93QD16r:+E%Q93QJ1Q7%Q<231%Q>3QI1;r;+F%Q>3QO1Q<%QA231%QC3QN1@r<+G%QC3R41QA%QF231%QH3R31Er=+H%QH3R91QF%QK231%QM3R81Jr>+I%QM3R>1QK%R0231%R23R=1Or?+J%R23RC1R0%R5231%R73RB1Q4r@+K%R73RH1R5%R:231%R<3RG1Q9+1%R;3RL1R9%R>2S01%R@3RK1Q=r2%RA21R<%RC3RN1RFr3%RD21R3%RF3S11R1r4%RG21QO%RI3S41QM+8%RH3S91RF%RK2RJ1%RM3S81QJ+9%RL3S=1RJ%RO2R@1%S13S<1QN+:%S03SA1RN%S32R=1+V_`L%RN2SB1%S73SB31+;%S63SG1S4%S92R<1&Q1vQK%211%S>3SI41+<%S=3SN1S;%S@2R<1&QA%12S8I%S<2T01%SE3T041+B%SD3T51SB%SG2R>1%SI3T41RF%SI2R;RJ%SK3T61RH%SK2R8RE%SM3T81RJ%SM2R5RB%SO3T:1RL%SO2R2R?%T13T<1RN%T12QOR<%T33T>1S0%T32QLR9%T53T@1S2rA%T621R7%T83TC1S5rB%T921R5%T;3TF1S8rC%T<21R3%T>3TI1S;&M%TM1TN&Q@(2+6%TA3U21T?(6%116%537Q01%638Q81%739Q@1%83:QG1%93;QL1%:3<R11%;3=91%<3>TH1%=3?RA1%?3@UA1qT6A1rQ5rD%E3321rQ8&Q9vQMrE+cUTD%U73UF1U5/01UF&Q6&Q<&Q?vQLvR?vQNvR3%675UFR74321&L&O&Q0%13UJR;UI%36UKR<9871+]8%UA2U?1%UC2V71&Fu8+cTf<%UG2V;1%4231%=3961+]@%UJ2UH1%UL2V@1&Q3%13V9RJG%;2:1%D3741+]H%V12UO1%V32VG1rQ4%A2@1%J3631+^0%V72V51%V92VM1+mSj0%V;2VO1%H2G1%Q13741+^8%V>2V<1%V@2W41%M2LUF%Q63521+^@%VC2VA1%VE2W91%Q:3415+^H%VG2VE1%VI2W=1%Q>3419+cTfD%VL2W@1%Q92Q81%QB34Q;1&N%14W;SLQIQG+mSVH%W22WF1%QG331B+mSW8%W52WI1%QJ331E+mSW0%W82WL1%W92WMTG%QF2QE1%QO3531+mSjH%W=2X11+W0%W?2X31%QL2QK1%R53641+mSk0%WC2X71%R8331:+iSV0%WF2X:1%R;331Q6+iSU8%WI2X=1%R62R54%R?3421+iRo8%WM2XA1%R:2R91%RC3421%X02X@UK%SD1X@%SH3XA21%RG34QH1+iSP@%X52XI1u4%X72XKX;%RD221%RM3641+iSP8%X;2XO1rQ3%RI271%S23531+iST0%X@2Y41+mSkH%XB2Y61%RO2RN1%S83641+iSS0%XF2Y:1%S32S21%S<3421+iRo@%XJ2Y>1%S?331M+iRoH%XM2YA1%SB331Q0+iSP0%Y02YD1%SE331R@+mSi0%Y32YG1&Q4&H%11SL(0%4221%SE2Q31%SN3971+mSi4%Y<2Z01%927Q7%SJ2Q81%T33531+mSi1%YA2Z51%YB2Z2XH%U93Z21QB%T83531+iSU0%YF2Z:1&Q2%11B%T52T41%T>3641%TG4Z6T@RM1%TN5TMTLTI1U2%U011p0U21p0UI1p0UM1p0V11p0V51p0V81p0V;1p0V>1p0VA1p0VD1p0VG1p0VL1p0W41p0W<1p0WC1p0WH1p0WM1p0X11p0X51p0X91pT<[41%ZH3[7SHZF/01[7%U12U0XE%U:3TFTC1%U;31T>T;%U<31T8T7%U=31T4T8%U>31T1T9%U?31U8SN%U82RFY1%UA3RDRB1%UB31R>R;%UC31R9R8%UD31R6S2%UE31R4S3%UF31R2TA%UG31R0QJ%UH31QHQF%UI31QDQB%UJ31Q@Q=%V34[BUL<1%V:5V9W7D1W:%V>11p0H1p0Y71p0Y=1p0YC1p0YI1p0YO1p0Z51p0Z;1p0ZA1p0ZG1p0ZO1p0[71p0[?1p0\01pTN\;1pT@\<1pT>\71pT:\=1p0\D1pQ4\I1")) (only parsing).
Variable G : ltac:(sec_ty2 constr:(SEC_T_fin_c7) 0%nat 0%nat).
Lemma fin_c7 : ltac:(sec_stmt2 constr:(SEC_T_fin_c7) 1%nat 0%nat).
Proof.
intros HG regs rom s1v tid HJ H2 H3 H4 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
eapply HG.
{ ld_step (ltac:(oF' 0x992d4%Z)) (ltac:(oD' 0x992d4%Z)) (word_to_le_bytes 8 uid) uid ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
ld_step (ltac:(oF' 0x992d8%Z)) (ltac:(oD' 0x992d8%Z)) (word_to_le_bytes 8 uid) uid ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
stepb_ft (ltac:(oF' 0x992dc%Z)) (ltac:(oD' 0x992dc%Z)) ltac:(pin; first [apply c_eq_refl | cond_compute]).
ld_step (ltac:(oF' 0x992e0%Z)) (ltac:(oD' 0x992e0%Z)) (zeros 8) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; peel; apply rdn_wbytes_zeros_in; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; unorm; lia) ltac:(reflexivity).
ld_step (ltac:(oF' 0x992e4%Z)) (ltac:(oD' 0x992e4%Z)) (zeros 8) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; peel; apply rdn_wbytes_zeros_in; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; unorm; lia) ltac:(reflexivity).
stepb_ft (ltac:(oF' 0x992e8%Z)) (ltac:(oD' 0x992e8%Z)) ltac:(pin; cond_compute).
ld_step (ltac:(oF' 0x992ec%Z)) (ltac:(oD' 0x992ec%Z)) (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
stepb_tk (ltac:(oF' 0x992f0%Z)) (ltac:(oD' 0x992f0%Z)) ltac:(pin; cond_compute).
ld_step (ltac:(oF' 0x993d0%Z)) (ltac:(oD' 0x993d0%Z)) (word_to_le_bytes 8 (Z_to_bv 64 627816)) (Z_to_bv 64 627816) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
ld_step (ltac:(oF' 0x993d4%Z)) (ltac:(oD' 0x993d4%Z)) (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8))) (Z_to_bv 64 (bv_unsigned sp0 + 8)) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
ld_step (ltac:(oF' 0x993d8%Z)) (ltac:(oD' 0x993d8%Z)) (word_to_le_bytes 8 (argc_w av)) (argc_w av) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
ld_step (ltac:(oF' 0x993dc%Z)) (ltac:(oD' 0x993dc%Z)) (word_to_le_bytes 8 (Z_to_bv 64 212508)) (Z_to_bv 64 212508) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
sv (ltac:(oF' 0x993e0%Z)) (ltac:(oD' 0x993e0%Z)) (Z_to_bv 64 (bv_unsigned sp0 - 32)).
stepret (ltac:(oF' 0x993e4%Z)) (ltac:(oD' 0x993e4%Z)) (0x99468 : word) ltac:(pin; first [reflexivity | bveq]).
sn (ltac:(oF' 0x99468%Z)) (ltac:(oD' 0x99468%Z)).
sn (ltac:(oF' 0x9946c%Z)) (ltac:(oD' 0x9946c%Z)).
sn (ltac:(oF' 0x99470%Z)) (ltac:(oD' 0x99470%Z)).
sv (ltac:(oF' 0x99474%Z)) (ltac:(oD' 0x99474%Z)) (argc_w av).
sv (ltac:(oF' 0x99478%Z)) (ltac:(oD' 0x99478%Z)) (Z_to_bv 64 (bv_unsigned sp0 + 8)).
ld_step (ltac:(oF' 0x9947c%Z)) (ltac:(oD' 0x9947c%Z)) (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
ld_step (ltac:(oF' 0x99480%Z)) (ltac:(oD' 0x99480%Z)) (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
ld_step (ltac:(oF' 0x99484%Z)) (ltac:(oD' 0x99484%Z)) (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
ld_step (ltac:(oF' 0x99488%Z)) (ltac:(oD' 0x99488%Z)) (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
sv (ltac:(oF' 0x9948c%Z)) (ltac:(oD' 0x9948c%Z)) sp0.
stepret (ltac:(oF' 0x99490%Z)) (ltac:(oD' 0x99490%Z)) (0x99494 : word) ltac:(pin; first [reflexivity | bveq]).
apply mst_refl. }
apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
ra_chain.
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_fin_c8 := (ltac2:(TCodec.tc2 tcn__Ju0Startup4 "^O'E!p021&Q=&Q>r1%3221&Ky5'R<yR0%211%5241'7y8%611%311p061&Q7vR9vC%3221':&Q8r5(R:+1(8%33D21%6251&R;z%22F1%;3F41r6+2%;3L19%>231%@3K1Cr7+3%@3Q11>%C231+RRP0%>2Q21%G3Q231r8+4%G3Q81E%J231+iSU@%E2Q91%N3Q931r9+8%N3Q?1L%Q1231%Q33Q>1Ir:+9%Q33QD1Q1%Q6231%Q83QC1Nr;+:%Q83QI1Q6%Q;231+V_`L%Q62QJ1%Q?3QJ31r<+;%Q?3R01Q=%QB231&Q1vQK%211%QG3R241r=+<%QG3R81QE%QJ231&QA&R=%12R:R1%321O%QH2R<1%R13R<61r>+B%R13RB1QO%R4231%R63RA1QLr?+C%R63RG1R4%R9231%R;3RF1R1r@+D%R;3RL1R9%R>231%R@3RK1R6rA+E%R@3S11R>%RC231%RE3S01R;rB+F%RE3S61RC%RH231%RJ3S51R@rC+G%RJ3S;1RH%RM231%RO3S:1RErD+H%RO3S@1RM%S2231%S43S?1RJrE+I%S43SE1S2%S7231%S93SD1ROrF+J%S93SJ1S7%S<231%S>3SI1S4rG+K%S>3SO1S<%SA231%SC3SN1S9%SC2T5S>+cUPH%S>2T21%SG3T231r2%SH21S;&QH+R@%22QN1%SE2T91%SN3T951r3%SO21S=%T13T<1S;r4%T221S9%T43T?1S7%T42T3S4+fPa0%SO2TC1%T83TC31%T82SMS3+fP`H%T32TG1%T<3TG31%T<2SLR9%T>3TI1S0%T>2SGR6+@%RE2RC1&QE&QF&3'4%11TM%321S2%511%72SI1%RN291%TC2U71%TL3U7=1%TL2SNR?%TN3U91TD%TN2SKR<%U03U;1TF%U02SHR9%U23U=1TH%U22SCR6%U43U?1TJ%U42S=R3%U63UA1TL%U62S5R0%U83UC1TN%U82S2QM%U:3UE1U0%U:2ROQJ%U<3UG1U2&M%UK1UL&Q@(2(6%114%335S:1%436S@1%537T31%638T;1%739TA1%83:TG1%93;U;1%:3<UD1%<3=V<1qT6>1rQ9%A321S=rQ<&Q9vQM+V_XH%V03V?1UN/01V?&Q6&Q<&Q?vQLvR?vQNvR3%675V?TG4321&L&O&Q0%13VCTKVB%36VDTL9871+]8%RI2TE1%V<2W01&Fu8+cTf<%V@2W41%4231%=3961+]@%S22TN1%VE2W91&Q3%13W2U:G%;2:1%D3741+]H%S92U51%VL2W@1rQ8%A2@1%J3631+^0%S?2U;1%W22WF1+mSj0%W42WH1%H2G1%Q13741+^8%SF2UB1%W92WM1%M2LW8%Q63521+^@%SK2UG1%W>2X21%Q:3415+^H%SO2UK1%WB2X61%Q>3419+cTfD%WE2X91%Q92Q81%QB34Q;1%T62V2W0%WI2X=1%QE331@%T92V5SC%WL2X@1%QH331C%T<2V8U5%WO2XC1%QK331F+Q0%T@2V<1%X32XG1%QO341J+Q8%TD2V@1%X72XK1%R3341N+QH%TH2VD1%X;2XO1+cUV8%X=2Y11%R12R01%R:3741+R0%TO2VK1%XB2Y61%R62R5VK%R?3521+R8%U42W01%XG2Y;1%R;2R:W:%RD3521&N%14Y6W>RKRI+mSVH%XM2YA1%RI331QD+mSW8%Y02YD1%RL331QG+mSW0%Y32YG1%Y42YHX<%RH2RG1%S13531+mSjH%Y82YL1+W0%Y:2YN1%RN2RM1%S73641+mSk0%Y>2Z21%S:331:+iSV0%YA2Z51%S=331R8+iSU8%YD2Z81%S82S74%SA3421+iRo8%YH2Z<1%S<2S;1%SE3421%YK2Z;YO%TC1Z;%TE3Z<21%SI34RJ1+iSP@%Z02ZD1u4%Z22ZFYM%SF221%SO3641+iSP8%Z62ZJ1rQ7%SK271%T43531+iST0%Z;2ZO1+mSkH%Z=2[11%T12T01%T:3641+iSS0%ZA2[51%T52T41%T>3421+iRo@%ZE2[91%TA331M+iRoH%ZH2[<1%TD331Q0+iSP0%ZK2[?1%TG331SB+mSi0%ZN2[B1&Q4&H%11TN(0%4221%TG2Q31%U03971+mSi4%[72[K1%927Q7%TL2Q81%U53531+mSi1%[<2\01%[=2[M[<%V63[M1QB%U:3531+iSU0%[A2\51&Q2%11B%U72U61%U@3641%UI4\1UBRM1%UO5UNY9UK1V2%V111p0V31p0VF1p0VI1p0VL1p0VO1p0W21p0W51p0W81p0W;1p0W>1p0WM1p0X01p0X51p0X:1p0X>1p0XB1p0XJ1pT<\L1rKrI+cUTD%\C3]21\A/01]2%V32V2Y9%V<3UHUE1%V=31U@U=%V>31U:U9%V?31U6U:%V@31U3U;%VA31V:U0%V:2RFYE%VC3RDRB1%VD31R>R;%VE31R9R8%VF31R6S2%VG31R4S3%VH31R2UC%VI31R0QJ%VJ31QHQF%VK31QDQB%VL31Q@Q=%W54]=VN<1rH%W<5W;HE21%J11p0L1p0YL1p0Z21p0Z81p0Z>1p0ZD1p0ZJ1p0[01p0[61p0[<1p0[B1p0[H1p0\31p0\<1p0\D1p0\J1p0]01p0]81p0]@1p0]F1p0^31pTN^>1pT@^?1pT>^:1pT:^@1p0^G1pQ4^L1")) (only parsing).
Variable G : ltac:(sec_ty2 constr:(SEC_T_fin_c8) 0%nat 0%nat).
Lemma fin_c8 : ltac:(sec_stmt2 constr:(SEC_T_fin_c8) 1%nat 0%nat).
Proof.
intros HG regs rom s1v tid HJ H1 H2 H3 H4 H8 H9 H10 H11 H12 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
eapply HG.
{ sv (ltac:(oF' 0x99494%Z)) (ltac:(oD' 0x99494%Z)) (Z_to_bv 64 (bv_unsigned sp0 - 48)).
stw (ltac:(oF' 0x99498%Z)) (ltac:(oD' 0x99498%Z)) (Z_to_bv 64 (bv_unsigned sp0 - 8)) (Z_to_bv 64 0) ltac:(ok_win HJ).
stw (ltac:(oF' 0x9949c%Z)) (ltac:(oD' 0x9949c%Z)) (Z_to_bv 64 (bv_unsigned sp0 - 16)) (Z_to_bv 64 0) ltac:(ok_win HJ).
stw (ltac:(oF' 0x994a0%Z)) (ltac:(oD' 0x994a0%Z)) (Z_to_bv 64 (bv_unsigned sp0 - 24)) (Z_to_bv 64 0) ltac:(ok_win HJ).
stw (ltac:(oF' 0x994a4%Z)) (ltac:(oD' 0x994a4%Z)) (Z_to_bv 64 (bv_unsigned sp0 - 32)) (Z_to_bv 64 0) ltac:(ok_win HJ).
stw (ltac:(oF' 0x994a8%Z)) (ltac:(oD' 0x994a8%Z)) (Z_to_bv 64 (bv_unsigned sp0 - 40)) (Z_to_bv 64 0) ltac:(ok_win HJ).
sv (ltac:(oF' 0x994ac%Z)) (ltac:(oD' 0x994ac%Z)) (Z_to_bv 64 (bv_unsigned sp0 + 8)).
sv (ltac:(oF' 0x994b0%Z)) (ltac:(oD' 0x994b0%Z)) (argc_w av).
sn (ltac:(oF' 0x994b4%Z)) (ltac:(oD' 0x994b4%Z)).
stepiv (ltac:(oF' 0x994b8%Z)) (ltac:(oD' 0x994b8%Z)) (Z_to_bv 64 (8 * Z.of_nat (length av))) ltac:(gres; pin; imm_norm; apply slli_argc).
sv (ltac:(oF' 0x994bc%Z)) (ltac:(oD' 0x994bc%Z)) (Z_to_bv 64 (bv_unsigned sp0 + 8 + 8 * Z.of_nat (length av))).
sv (ltac:(oF' 0x994c0%Z)) (ltac:(oD' 0x994c0%Z)) (Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))).
sn (ltac:(oF' 0x994c4%Z)) (ltac:(oD' 0x994c4%Z)).
sv (ltac:(oF' 0x993e8%Z)) (ltac:(oD' 0x993e8%Z)) (Z_to_bv 64 (bv_unsigned sp0 - 80)).
stw (ltac:(oF' 0x993ec%Z)) (ltac:(oD' 0x993ec%Z)) (Z_to_bv 64 (bv_unsigned sp0 - 56)) (Z_to_bv 64 627912) ltac:(ok_win HJ).
stw (ltac:(oF' 0x993f0%Z)) (ltac:(oD' 0x993f0%Z)) (Z_to_bv 64 (bv_unsigned sp0 - 64)) (Z_to_bv 64 (bv_unsigned sp0 + 8)) ltac:(ok_win HJ).
stw (ltac:(oF' 0x993f4%Z)) (ltac:(oD' 0x993f4%Z)) (Z_to_bv 64 (bv_unsigned sp0 - 72)) (argc_w av) ltac:(ok_win HJ).
sn (ltac:(oF' 0x993f8%Z)) (ltac:(oD' 0x993f8%Z)).
stepret (ltac:(oF' 0x991b8%Z)) (ltac:(oD' 0x991b8%Z)) (0x993fc : word) ltac:(pin; first [reflexivity | bveq]).
sn (ltac:(oF' 0x993fc%Z)) (ltac:(oD' 0x993fc%Z)).
sn (ltac:(oF' 0x99400%Z)) (ltac:(oD' 0x99400%Z)).
ld_step (ltac:(oF' 0x99404%Z)) (ltac:(oD' 0x99404%Z)) (word_to_le_bytes 8 (Z_to_bv 64 721440)) (Z_to_bv 64 721440) ltac:(rd_img img_b5f08_8) ltac:(apply bytes_le_to_Z_8).
ld_step (ltac:(oF' 0x99408%Z)) (ltac:(oD' 0x99408%Z)) (word_to_le_bytes 8 (Z_to_bv 64 721432)) (Z_to_bv 64 721432) ltac:(rd_img img_b5f10_8) ltac:(apply bytes_le_to_Z_8).
stepb_ft (ltac:(oF' 0x9940c%Z)) (ltac:(oD' 0x9940c%Z)) ltac:(pin; cond_compute).
ld_step (ltac:(oF' 0x99410%Z)) (ltac:(oD' 0x99410%Z)) (word_to_le_bytes 8 (Z_to_bv 64 212248)) (Z_to_bv 64 212248) ltac:(rd_img img_b0218_8) ltac:(apply bytes_le_to_Z_8).
stepjr (ltac:(oF' 0x99414%Z)) (ltac:(oD' 0x99414%Z)) (0x33d18 : word) ltac:(gres; pin; first [reflexivity | bveq]).
apply mst_refl. }
apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
ra_chain.
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_fin_c9 := (ltac2:(TCodec.tc2 tcn__Ju0Startup4 "_D'E!p021&Q=&Q>r1%3221&Ky5'R<yR0%211%5241'7y8%611%311p061&Q7vR9vC%3221':&Q8r5(R:+1(8%33D21%6251&R;+cUPH%22F1%;3F41r6+2%;3L19%>231&QH&R=%12NE+R@%4221%=2Q11%F3Q171r7+3%F3Q71D%I231+RRP0%D2Q81%M3Q831r8+4%M3Q>1K%Q0231+iSU@%K2Q?1%Q43Q?31r9+8%Q43QE1Q2%Q7231+fPa0%Q22QF1%Q;3QF31r:+9%Q;3QL1Q9%Q>231+fP`H%Q92QM1%QB3QM31r;+B%QB3R31Q@%QE231+V_`L%Q@2R41%QI3R431r<+C%QI3R:1QG%QL231&QA+@%22Q>1&QE&QF&3'4%11R<vQK%4221%611%82Q31%<2:1%R32RG1%R<3RG?1r=+D%R<3RM1R:%R?231z%R:2RN1%RC3RN31r>+E%RC3S41RA%RF231%RH3S316r?+F%RH3S91RF%RK231%RM3S81;r@+G%RM3S>1RK%S0231%S23S=1@rA+H%S23SC1S0%S5231%S73SB1ErB+I%S73SH1S5%S:231%S<3SG1JrC+J%S<3SM1S:%S?231%SA3SL1OrD+K%SA3T21S?%SD231%SF3T11Q4%SF2T8SA+cUVH%SA2T51%SJ3T531r2%SK21S>+Q@%S>2S<1%SG2T;1%T03T;41r3%T121S9%T33T>1S7r4%T421S5%T63TA1S3%T62T5S0%R:2SFS2%T12TE1%T:3TE31%T:2SORM&Q1%11R7%T>3TI31+:%T=3TN1T;%T@2SJ1%TB3TM15+;%TA3U21T?%TD2SG1%TF3U11=+<%TE3U61TC%TH2SD1%TJ3U51R?%TJ2S?S6%TL3U71S4%TL2S:S1%TN3U91RC%TN2S5R@%U03U;1R>%U02RDR;%U23U=1R@%U22R?R8%U43U?1RB%U42R<R5%U63UA1RD%U62R9R2%U83UC1RF%U82R6QO%U:3UE1RH%U:2R3QL%U<3UG1RJ%U<2R0QI%U>3UI1RL&M%UM1UN&Q@(2(6%114%335M1%436Q21%537Q71%638T:1%739TB1%83:U<1%93;UE1%;3<V=1qT6=1rQ9%@321R=rQ<&Q9vQMrE%V13V@T=UO/01V@&Q6&Q<&Q?vQLvR?vQNvR3%675V@T74321&L&O&Q0%13VDT;VC%36VET<9871+]8%V42V21%V=2W11&Fu8+cTf<%VA2W51%4231%=3961+]@%V=2V;1%VF2W:1&Q3%13W3TJG%;2:1%D3741+]H%VD2VB1%VM2WA1rQ8%A2@1%J3631+^0%VJ2VH1%W32WG1+mSj0%W52WI1%H2G1%Q13741+^8%W12VO1%W:2WN1%M2LU1%Q63521+^@%W62W41%W?2X31%Q:3415+^H%W:2W81%WC2X71%Q>3419+cTfD%WF2X:1%Q92Q81%QB34Q;1%WA2W?VK%WJ2X>1%QE331@%WD2WBV5%WM2XA1%QH331C%WG2WEU3%X02XD1%QK331F+Q0%WK2WI1%X42XH1%QO341J+Q8%WO2WM1%X82XL1%R3341N+QH%X32X11%X<2Y01+cUV8%X>2Y21%R12R01%R:3741+R0%X:2X81%XC2Y71%R62R5TC%R?3521+R8%X?2X=1%XH2Y<1%R;2R:TD%RD3521+RH%XD2XB1%XM2YA1%R@2R?XL%RI3521+S0%XI2XG1%Y22YF1%RE2RDX1%RN3521&N%14YAW8S5S3+mSVH%Y82YL1%S3331QN+mSW8%Y;2YO1%S6331R1+mSW0%Y>2Z21%Y?2Z3XA%S22S11%S;3531+mSjH%YC2Z71+W0%YE2Z91%S82S71%SA3641+mSk0%YI2Z=1%SD331:+iSV0%YL2Z@1%SG331RB+iSU8%YO2ZC1%SB2SA4%SK3421+iRo8%Z32ZG1%SF2SE1%SO3421%Z62ZFZ:%TL1ZF%TN3ZG21%T334S41+iSP@%Z;2ZO1u4%Z=2[1Z8%T0221%T93641+iSP8%ZA2[51rQ7%T5271%T>3531+iST0%ZF2[:1+mSkH%ZH2[<1%T;2T:1%TD3641+iSS0%ZL2[@1%T?2T>1%TH3421+iRo@%[02[D1%TK331M+iRoH%[32[G1%TN331Q0+iSP0%[62[J1%U1331SL+mSi0%[92[M1&Q4&H%11U8(0%4221%U12Q31%U:3971+mSi4%[B2\61%927Q7%U62Q81%U?3531+mSi1%[G2\;1%[H2\8Y?%V?3\81QB%UD3531+iSU0%[L2\@1&Q2%11B%UA2U@1%UJ3641+fla@%\22\F1%UM331QK%V64\?UOS01%V<5V;V:V81V?%V>11p0V@1p0W21p0W51p0W81p0W;1p0W>1p0WA1p0WD1p0WG1p0WJ1p0WM1p0X01p0X51p0X:1p0X?1p0XD1p0XI1p0XM1p0Y11p0Y81pT<]=1rHrF+V_XH%]43]C1]2/01]C%VC2VBYG%VL3V8V51%VM31V0UM%VN31UJUI%VO31UFUJ%W031UCUK%W131VJU@%W231U>UM%W331U<UN%W431U:UO%W531U7V0%W631U4V1%W731U1TN%W831TKTJ%W931TGTF%W22S4Z;%W;3S2S01%W<31RLRI%W=31RGRF%W>31RDS@%W?31RBSA%W@31R@V;%WA31R>R8%WB31R6R4%WC31R2R0%WD31QNQK%WM4^6WF<1%X35X2OL1X1%Q111p0Q31p0ZA1p0ZG1p0ZM1p0[31p0[91p0[?1p0[E1p0[K1p0\31p0\G1p0\O1p0]71p0]?1p0]G1p0]O1p0^;1p0^H1pTN_31pT@_41pT>^O1pT:_51p0_<1pQ4_A1")) (only parsing).
Variable G : ltac:(sec_ty2 constr:(SEC_T_fin_c9) 0%nat 0%nat).
Lemma fin_c9 : ltac:(sec_stmt2 constr:(SEC_T_fin_c9) 1%nat 0%nat).
Proof.
intros HG regs rom s1v tid HJ H1 H2 H3 H4 H8 H9 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
eapply HG.
{ sv (ltac:(oF' 0x33d18%Z)) (ltac:(oD' 0x33d18%Z)) (Z_to_bv 64 (bv_unsigned sp0 - 96)).
stw (ltac:(oF' 0x33d1c%Z)) (ltac:(oD' 0x33d1c%Z)) (Z_to_bv 64 (bv_unsigned sp0 - 88)) (Z_to_bv 64 627736) ltac:(ok_win HJ).
stw (ltac:(oF' 0x33d20%Z)) (ltac:(oD' 0x33d20%Z)) (Z_to_bv 64 (bv_unsigned sp0 - 96)) (Z_to_bv 64 721440) ltac:(ok_win HJ).
sv (ltac:(oF' 0x33d24%Z)) (ltac:(oD' 0x33d24%Z)) (Z_to_bv 64 (bv_unsigned sp0 - 80)).
sn (ltac:(oF' 0x33d28%Z)) (ltac:(oD' 0x33d28%Z)).
sn (ltac:(oF' 0x33d2c%Z)) (ltac:(oD' 0x33d2c%Z)).
lb_step (ltac:(oF' 0x33d30%Z)) (ltac:(oD' 0x33d30%Z)) (Z_to_bv 8 0) ltac:(rd_img img_b7230_1).
sn (ltac:(oF' 0x33d34%Z)) (ltac:(oD' 0x33d34%Z)).
stepb_tk (ltac:(oF' 0x33d38%Z)) (ltac:(oD' 0x33d38%Z)) ltac:(pin; cond_compute).
sn (ltac:(oF' 0x33d44%Z)) (ltac:(oD' 0x33d44%Z)).
sn (ltac:(oF' 0x33d48%Z)) (ltac:(oD' 0x33d48%Z)).
sn (ltac:(oF' 0x33d4c%Z)) (ltac:(oD' 0x33d4c%Z)).
stw (ltac:(oF' 0x33d50%Z)) (ltac:(oD' 0x33d50%Z)) (Z_to_bv 64 750128) (Z_to_bv 64 1) ltac:(ok_data).
sn (ltac:(oF' 0x33d54%Z)) (ltac:(oD' 0x33d54%Z)).
ld_step (ltac:(oF' 0x33d58%Z)) (ltac:(oD' 0x33d58%Z)) (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_b5da8_8) ltac:(apply bytes_le_to_Z_8).
stepb_tk (ltac:(oF' 0x33d5c%Z)) (ltac:(oD' 0x33d5c%Z)) ltac:(pin; cond_compute).
ld_step (ltac:(oF' 0x33d7c%Z)) (ltac:(oD' 0x33d7c%Z)) (word_to_le_bytes 8 (Z_to_bv 64 627736)) (Z_to_bv 64 627736) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
ld_step (ltac:(oF' 0x33d80%Z)) (ltac:(oD' 0x33d80%Z)) (word_to_le_bytes 8 (Z_to_bv 64 721440)) (Z_to_bv 64 721440) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
sv (ltac:(oF' 0x33d84%Z)) (ltac:(oD' 0x33d84%Z)) (Z_to_bv 64 (bv_unsigned sp0 - 80)).
stepret (ltac:(oF' 0x33d88%Z)) (ltac:(oD' 0x33d88%Z)) (0x99418 : word) ltac:(pin; first [reflexivity | bveq]).
sn (ltac:(oF' 0x99418%Z)) (ltac:(oD' 0x99418%Z)).
stepb_ft (ltac:(oF' 0x9941c%Z)) (ltac:(oD' 0x9941c%Z)) ltac:(pin; cond_compute).
ld_step (ltac:(oF' 0x99420%Z)) (ltac:(oD' 0x99420%Z)) (word_to_le_bytes 8 (Z_to_bv 64 627912)) (Z_to_bv 64 627912) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
ld_step (ltac:(oF' 0x99424%Z)) (ltac:(oD' 0x99424%Z)) (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8))) (Z_to_bv 64 (bv_unsigned sp0 + 8)) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
ld_step (ltac:(oF' 0x99428%Z)) (ltac:(oD' 0x99428%Z)) (word_to_le_bytes 8 (argc_w av)) (argc_w av) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
sv (ltac:(oF' 0x9942c%Z)) (ltac:(oD' 0x9942c%Z)) (Z_to_bv 64 (bv_unsigned sp0 - 48)).
stepret (ltac:(oF' 0x99430%Z)) (ltac:(oD' 0x99430%Z)) (0x994c8 : word) ltac:(pin; first [reflexivity | bveq]).
sv (ltac:(oF' 0x994c8%Z)) (ltac:(oD' 0x994c8%Z)) (argc_w av).
sv (ltac:(oF' 0x994cc%Z)) (ltac:(oD' 0x994cc%Z)) (Z_to_bv 64 (bv_unsigned sp0 + 8)).
sv (ltac:(oF' 0x994d0%Z)) (ltac:(oD' 0x994d0%Z)) (Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))).
stepjr (ltac:(oF' 0x994d4%Z)) (ltac:(oD' 0x994d4%Z)) (0x33e1c : word) ltac:(gres; pin; first [reflexivity | bveq]).
apply mst_refl. }
apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
ra_chain.
Qed.
End SE.
End P.
End FPX_1.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
