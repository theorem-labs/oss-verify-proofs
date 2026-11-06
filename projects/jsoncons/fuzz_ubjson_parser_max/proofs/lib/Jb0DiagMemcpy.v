(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import
PropExec CatExec CatSim SeqExec StepTac Hoare StoreOk WalkTac RefMemcpyLib MemSplit As0StepLib Jb0MemIsZero Jb0RegionPoisoned Jb0AsanMemset Jb0AsanMemcpy Jb0MemcpyIcpt Jb0DiagChk.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__Jb0DiagMemcpy () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Hoare."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Jb0AsanMemcpy."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Jb0DiagMemcpy.FPX_1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Jb0RegionPoisoned."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.RefMemcpyLib."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.StoreOk."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1Some"; "1bool"; "1list"; "1option"; "1true"; "2I"; "2and"; "2eq"; "2ex"; "2or"; "3Z"; "4store_ok"; "5bvmap"; "0M"; "0Mj"; "6wbytes"]; ["7msteps"; "8ret_ok"; "9in_app8"; "9mc_icpt_globs"; ":zsh"; ";HIGHEND"; ";SB"; ";rt_layout_globs"; "<getr"; "<mkst"; "<rdn"; "<seg_rom"; "=keeps_cs"; ">mem_grows"; "?loaded_segments"; "@add"]; ["@div"; "@le"; "@lt"; "@min"; "@modulo"; "@pow"; "@sub"; "@to_nat"; "0bs"; "0fS"; "0fx"; "0lS"; "0m"; "0n"; "0p"; "0pd"]; ["0ps"; "0regs"; "0regs'"; "0ret"; "0s"; "ABV"; "AZ_to_bv"; "Abv"; "Abv_unsigned"; "0w0"; "0w1"; "0x"]]).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
Section FPX_1. Context {fx : PropExec.FPState}.
Definition zsh (M : word -> option byte) (p n : Z) : Prop :=
forall x : word, (SB + p / 8) - (SB + p / 8) mod 8 <= bv_unsigned x < (SB + (p + n - 1) / 8) - (SB + (p + n - 1) / 8) mod 8 + 8 -> M x = Some (Z_to_bv 8 0).
Lemma zsh_of_hull : ltac2:(TCodec.tc2 tcn__Jb0DiagMemcpy "QE'QGyR0%211'3y8%511%311pSH51':'6&Q1&Q6&O&F&Q0r3+8%3221%6251+7%9221&QHr1%22F1%>241&Q2r2%?2<1+1%B221%@21>%C2B1%D21@%82:1%I2:1'7r5%11;(0&QFz%22Q51%42Q51%83Q561p0:1pSHQ;1&Dr4%231Q1Fp041pRLQ:1pRNQ;1pLQ=1").
Proof.
intros M p n H x Hx. apply H. pose proof (Z.mod_pos_bound (SB + p / 8) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (SB + (p + n - 1) / 8) 8 ltac:(lia)). lia.
Qed.
Lemma zsh_of_hullm : ltac2:(TCodec.tc2 tcn__Jb0DiagMemcpy "R9'QGyR0%211'3y8%511%311pSH51':&Q1zr3%3221&Q6+1%2241r2%8221&Q2&Or5%221:&Q5+2+Q?%3221%8251'6&F&Q0r7+8%3221%>251+7%F221&QHr1%22Q51%N241&Q3%F2;E%=21;%H2?1%I21=+Q<%H2G1%L2C1%8241%O2;1%G2;1'7r9%11Q5(0&QF%12QDQ>%32QD1%73QD51p091pSHQJ1&Dr8r6%332Q21p051p0Q81p0QB1p0QH1pRJQM1pRLQN1pRNQO1pLR11").
Proof.
intros M p n m Hp Hnm Hpm H x Hx. apply H.
assert (Q1 : (p + n - 1) / 8 <= (p + m) / 8) by (apply Z.div_le_mono; lia).
assert (Q2 : (p + m) / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia).
pose proof (Z.mod_pos_bound (SB + p / 8) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (SB + (p + n - 1) / 8) 8 ltac:(lia)).
pose proof (Z.div_mod (SB + (p + n - 1) / 8) 8 ltac:(lia)). unfold SB in *. lia.
Qed.
Section SE.
Local Abbreviation SEC_T_zsh_words := (ltac2:(TCodec.tc2 tcn__Jb0DiagMemcpy "R>'QGyR0%211'3y8%511%311p051':&Dr3r2r1%43321&Q2z%2215&Q1r4%2241&Or5%2214+8%4221&E%9221&F&Q0r6%2217%;241&Q6r7%>215+1%4221%921>%B2;1'8'2%11Q4'6'7%Q913&J&Nr;&QF&Q4%12Q0K%C2Q11%42QC1u8%948721(0%12?Q=%>3=31%92Q@Q3%K2QA1%<2QK1%@4?>18%72EQB%D3C21%F271qSFH1%K2I1qSDJ1%M2K1tRHQMO1tRDQNQ71p0Q=1p0QE1p0QI1p0QM1pRLR31pRNR41pLR61")) (only parsing).
Variable M : ltac:(sec_ty2 constr:(SEC_T_zsh_words) 0%nat 0%nat).
Variable p : ltac:(sec_ty2 constr:(SEC_T_zsh_words) 1%nat 0%nat).
Variable n : ltac:(sec_ty2 constr:(SEC_T_zsh_words) 2%nat 0%nat).
Lemma zsh_words : ltac:(sec_stmt2 constr:(SEC_T_zsh_words) 3%nat 0%nat).
Proof.
intros HZ Hn Hp Hpn fS lS.
unfold HIGHEND in *.
assert (Pq : 0 <= p / 8 <= (p + n - 1) / 8 /\ (p + n - 1) / 8 <= 2 ^ 44).
{ split; [split; [apply Z.div_pos; lia | apply Z.div_le_mono; lia] | apply Z.div_le_upper_bound; lia]. }
assert (FL : fS <= lS) by (subst fS lS; lia).
pose proof (Z.mod_pos_bound fS 8 ltac:(lia)) as B0. pose proof (Z.mod_pos_bound lS 8 ltac:(lia)) as B1.
pose proof (Z.div_mod fS 8 ltac:(lia)) as E0. pose proof (Z.div_mod lS 8 ltac:(lia)) as E1.
pose proof (Z.div_le_mono fS lS 8 ltac:(lia) FL) as MONO.
assert (R0 : 0 <= fS - fS mod 8 /\ lS - lS mod 8 + 8 < 2 ^ 63) by (subst fS lS; unfold SB in *; lia).
unfold zsh in HZ. fold fS lS in HZ.
exists (repeat (Z_to_bv 8 0) 8), (repeat (Z_to_bv 8 0) 8).
split; apply rdn_zeros; try (rewrite u_Z2bv by lia; cbn; lia);
intros i Hi; rewrite u_Z2bv by lia; apply HZ; rewrite u_Z2bv by (cbn in Hi; lia); cbn in Hi; lia.
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_diag_memcpy := (ltac2:(TCodec.tc2 tcn__Jb0DiagMemcpy "W5'QGyR0%211'3y8%511%311p051':'2%115&<y5%221;'6&Q1zr4%3221&Q5+2+Q8%3221%8261%:261&Br6r5%3221r8%5214+`PPP0&Q6r:+RUH%3221%E251&Q2r;+R0%E2D1%4231&O&F&Q0r9%42=1+1%@221+8%6221%9281%:213r<%F21D%Q8231%>23G%I21:%>219%A2@1%B21;r=%N21L%Q@231%K2Q@J'9%H25=r?%Q421Q2%QF231%QG239%6221p081%Q42QID%Q027=r@%Q<21Q:%QN231%QO23;%>221p071r>%R3281%Q922F%R521A%D231'7'1&;&NrB&QFrA%QM21QK%32RM1uRUH%847621(4%<3;21rC%92S38&Q7%11Q3%?4>431%B3A17%S61RO&JrD%71Q1%34D291(0%12S5Q<%J3731&A%11Q?&GrF%211&CrG%211&DrHrE%3321ArI%53173&H(QE(5%23SFRC1%42Q01%Q>3T21I%53SISA4%72K1rJ%Q=2T71%QC3T731+:%;3SO1:%=2A1%QG3T;15+;%?3T31>%A2L1%QK3T?19+<%C3T71B%E2M1%QO3TC1='8'@&IvQ:+^m`8%K3TJ1J/01TJrQ1&K%11R6%857I431r2rK&?r1rO%R;2U51rL%53421%A5@871:%C3RA:1%Q<2:Q0%RF3U:16&L%12Q7=&QH%12U?<%TA2DT?%T=221%U42F3%SC221r3%11ErQ3%11G%S33UC31p061pSHUI1&M%12Q0I%U@231%UA2A1%UB2D1%UC2G1qNUK1%Q=2UL1qS6UG1%Q?2UH1p0QA1p0QF1p0QK1p0R01p0R61p0R=1p0R@1p0RE1p0RI1p0RM1p0S01p0S91p0S@1p0SN1p0T41p0T=1p0TG1p0U01p0U?1p0UE1p0UL1p0UO1p0V41pS4V@1pS8VL1pRBVE1pRLVH1pS2VI1pS0VJ1pS:VK1pLVM1")) (only parsing).
Variable M : ltac:(sec_ty2 constr:(SEC_T_diag_memcpy) 0%nat 0%nat).
Variable s : ltac:(sec_ty2 constr:(SEC_T_diag_memcpy) 1%nat 0%nat).
Variable pd : ltac:(sec_ty2 constr:(SEC_T_diag_memcpy) 2%nat 0%nat).
Variable ps : ltac:(sec_ty2 constr:(SEC_T_diag_memcpy) 3%nat 0%nat).
Variable n : ltac:(sec_ty2 constr:(SEC_T_diag_memcpy) 4%nat 0%nat).
Variable bs : ltac:(sec_ty2 constr:(SEC_T_diag_memcpy) 5%nat 0%nat).
Variable ret : ltac:(sec_ty2 constr:(SEC_T_diag_memcpy) 6%nat 0%nat).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_diag_memcpy) 7%nat 0%nat).
Theorem diag_memcpy : ltac:(sec_stmt2 constr:(SEC_T_diag_memcpy) 8%nat 0%nat).
Proof.
intros Hn HappS HappD Hs1 Hs2 HshS HshD HdjS HdjD Hover Hok Hdst Hsrc Hret HG HI HZS HZD H1 H2 H10 H11 H12.
assert (Hpd : 0 <= pd /\ pd + n + 8 <= HIGHEND) by (unfold in_app8, LOWEND, HIGHBEG, HIGHEND in *; lia).
assert (Hps : 0 <= ps /\ ps + n + 8 <= HIGHEND) by (unfold in_app8, LOWEND, HIGHBEG, HIGHEND in *; lia).
set (fD := SB + pd / 8) in *. set (lD := SB + (pd + n - 1) / 8) in *.
set (fS := SB + ps / 8) in *. set (lS := SB + (ps + n - 1) / 8) in *.
destruct (@wrap_memcpy_run fx M (seg_rom ASEGS) (Z_to_bv 64 s) ret pd ps n s bs 0 fS lS (fS - fS mod 8) (lS - lS mod 8) 0 fD lD (fD - fD mod 8) (lD - lD mod 8))
with (regs := regs) as (regs' & Mj & RUN & Q10 & Q2 & Q1 & KCS & OUT & GR).
- apply u_Z2bv; lia.
- reflexivity.
- reflexivity.
- reflexivity.
- reflexivity.
- reflexivity.
- reflexivity.
- reflexivity.
- reflexivity.
- lia.
- exact HappS.
- exact HappD.
- lia.
- subst lS. lia.
- subst lD. lia.
- exact HdjS.
- exact HdjD.
- exact Hover.
- exact Hok.
- exact Hdst.
- exact Hsrc.
- exact Hret.
- exact HG.
- exact HI.
- intros Hn0 x Hx. apply HZS. fold fS lS. pose proof (Z.mod_pos_bound fS 8 ltac:(lia)). pose proof (Z.mod_pos_bound lS 8 ltac:(lia)). lia.
- intros Hn0. apply HZS. fold fS lS. assert (0 <= (ps + n - 1) / 8 <= 2 ^ 44) by (unfold HIGHEND in *; split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
assert (ps / 8 <= (ps + n - 1) / 8) by (apply Z.div_le_mono; lia). assert (0 <= ps / 8) by (apply Z.div_pos; lia).
pose proof (Z.mod_pos_bound fS 8 ltac:(lia)). pose proof (Z.mod_pos_bound lS 8 ltac:(lia)). rewrite u_Z2bv by (subst lS; unfold SB; lia). subst fS lS. unfold SB in *. lia.
- left. reflexivity.
- intros [Hn0 _]. exact (zsh_words M ps n HZS Hn0 (proj1 Hps) (proj2 Hps)).
- intros Hn0 x Hx. apply HZD. fold fD lD. pose proof (Z.mod_pos_bound fD 8 ltac:(lia)). pose proof (Z.mod_pos_bound lD 8 ltac:(lia)). lia.
- intros Hn0. apply HZD. fold fD lD. assert (0 <= (pd + n - 1) / 8 <= 2 ^ 44) by (unfold HIGHEND in *; split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
assert (pd / 8 <= (pd + n - 1) / 8) by (apply Z.div_le_mono; lia). assert (0 <= pd / 8) by (apply Z.div_pos; lia).
pose proof (Z.mod_pos_bound fD 8 ltac:(lia)). pose proof (Z.mod_pos_bound lD 8 ltac:(lia)). rewrite u_Z2bv by (subst lD; unfold SB; lia). subst fD lD. unfold SB in *. lia.
- left. reflexivity.
- intros [Hn0 _]. exact (zsh_words M pd n HZD Hn0 (proj1 Hpd) (proj2 Hpd)).
- exact H10.
- exact H11.
- exact H12.
- exact H2.
- exact H1.
- exists regs', Mj. split; [exact RUN|]. split; [exact Q10|]. split; [exact KCS|]. split; [|exact GR].
intros x Hx. apply OUT. exact Hx.
Qed.
End SE.
End FPX_1.
