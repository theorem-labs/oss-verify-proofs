(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib As0Tables
ArtMem ArtRegs ArtAtomics ArtTac JbtLeaf JbtAllocG JbtPoison JbtPoisonRun ArtRuns ArtRunsMem JbtMmapFixed JbtPopulate1 JbtPopulate2 JbtPopulate3 JbtFp JbtClsPop1.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLiaT.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__JbtClsPop2 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ArtMem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ArtRuns."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Hoare."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtFp."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtLeaf."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtPoison."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtPopulate3."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.StoreOk."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1cons"; "1nat"; "1nil"; "1option"; "1pair"; "1prod"; "2I"; "2and"; "2eq"; "2ex"; "3Z"; "0E"; "4bvmap"; "0M"; "0M'"; "5apart"]; ["5cell"; "5wr"; "6art_mmap_args"; "7msteps"; "8ret_ok"; "9art_agree"; ":art_tsd"; ";art_layout"; ";kHighMemBeg"; "<art_carve"; "=getr"; "=mkst"; ">mem_grows"; "?loaded_segments"; "@In"; "Aadd"]; ["Adiv"; "Ale"; "Alt"; "Amodulo"; "Amul"; "Aof_nat"; "Apow"; "Asub"; "0a"; "0addr2"; "0au"; "0b"; "0c"; "0ctx"; "0fa"; "0fb"]; ["0fx"; "0g18"; "0g19"; "0g20"; "0g21"; "0g22"; "0g8"; "0g9"; "0i"; "0j"; "0k"; "0key"; "0kf"; "0len2"; "0m1"; "0m2"]; ["0mfa"; "0mu'"; "0new"; "0nf"; "0q"; "0qs"; "0r"; "0raw"; "0rb"; "0regs"; "0regs'"; "0rom"; "0rr"; "0shb2"; "0sp"; "0spb"]; ["BBV"; "BZ_to_bv"; "Bbv"; "Bbv_unsigned"; "0sz"; "0t"; "0total"; "0tp"; "0tsd"; "0x"]]).
Local Ltac lia := L5FastLiaT.plia2.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).
Lemma art_agree_carve : ltac2:(TCodec.tc2 tcn__JbtClsPop2 "QO'1'RByR0%211'3y8%511%311p051':&Q1zr1%3221&Q7r5&Q4+4&Or2&Q5r7%211%5241%8271%;2:1%@2?1&Q2r6&Q6+2+R0%3221%6251&E(0'5%12LL(4r4r9%E11%H231%K2J1%N2G1%M2L4%84Q5Q521(2%11;%>3<31r8&I%162OHQ5=<%C3431p0E1p0M1p0Q;1pSBQ@1pU:QA1pRFQB1pHQC1pLQE1pSFQN1").
Proof. intros k M E au sz i Hi HE HE' x Hx. cbn in Hx. destruct Hx as [Hx _]. apply art_carve_outside; [exact Hi|exact HE|exact HE'|lia]. Qed.
Section FPX. Context {fx : PropExec.FPState}.
Section SE.
Local Abbreviation SEC_T_art_clspop_D := (ltac2:(TCodec.tc2 tcn__JbtClsPop2 "\<&<y5'RByR0%211%5241'3y8%611%311p061':&Or>+S`PPPP0%3221'8&JrE(R@+2(6%33E21%6251&RA&Q7rA+R0%3221%52J1%>3J71rF+8%>3Q01<%A231%;2Q09%D3Q021rG+9%D3Q61B%G231r=r<%O221%D2Q91%M3Q951rH+:%M3Q?1K%Q0231+1%K2Q@1%Q43Q@31rI+B%Q43QF1Q2%Q7231rC%Q22QG1%Q;3QG31rJ+C%Q;3QM1Q9%Q>231r?%Q92QN1%QB3QN31rK+D%QB3R41Q@%QE231%QG3R316rL+E%QG3R91QE%QJ231%QD2R9QJ%QM3R921&Q1+Vb\P0%R421QE%321L&Q2&Q6+Q?%22R11%42J1&D%11@%;2:F+T0%R?2C1rM%R421R2%@231%A2@G+Q0%>2R=1%RF261rO%R;21R9%G231&?r@+M%F2RE1%447@31'7rN%O2=1+RPP0%Q1231%5231%Q32>QE%O2RNRG%Q12QG1%9231z%Q821C%Q92R5KrQ1&Q4rQ2%22?1%S@241rQ0%Q@221%QA27N%QB2;8+4%SF28:%:221%QF21K&A&MrQ<rQ8%44321Q?rQ=rQ4%C2;1%T12RA1rQ3%F2>1%;4:631&@rQ>rQ:%T821QDu8rQ7%65A5321rQ?rQ;+@%T?221rQ6%<5G5281rQ@+Q@%TD2I1%@5K31<IrQA+Q8%TH2J1%D5O31@Q@rQB+QH%TL2F1%H5Q331DQDrQC%TB2=T;&RC%12U:;%M5Q843I1rQD%TG2>F%52U>Q9%Q15Q<32M1rQE+H%TL2?1%Q55Q@31Q15rQF%TO2>RH%Q85QC21Q48rQG%U22<H%Q;5QF21Q7;rQH%U52;O%Q>5QI21Q:>rQI%U82:J%QA5QL21Q=ArQJ%U;2:U9%QD5QO21Q@D'9'C&KvQ@rQN+ZlgH%UI3V91UG/01V9rQMrQL%8576321r2rQKr1%<5;3215%>3R?51%V525U6%V73VC1U4%V727V2%V12VFF%V:3VF21%V83VJU9V6%V;2;1%V=3VI1;%V=2=UM%V?3VK1QM%V?2?UI%VA3VM1R3%VA2AU;%VC3VO1R;%VC2CU6%VE3W11RC%VE2EU1%VG3W31RM%VG2GTN%VI3W51S2+F%VH3W:1VF%VK2K1%VM3W91RD%W<1W=&N(0+3%VO3WA1VM%W03WBSBVN+G%W23WD1W0%W33WER2W1+I%W53WG1W3+J%W73WI1W5+K%W93WK1W7(2%11@%?3A31%@3B61%A3C91%B3D<1%C3E>1%D3FA1%E3GC1%G3HQC1r4%WG21QGrR0%WI21QI%WK3X731p061pUDO1&L%12R1QL&E'5%12X7X7(4%TK2TCS5%X92T21%TM2TES<%44X<X<21%X<2RHSN%64X>X>1WI%X>2RJUJ%84X@X@1WK+R4%XA2RM1%;4XCXC1W<%Q21=%Q@3>21%QA3?61%QB3@91%QC3A<1%D31RFRA%XI2SFSK%TE5U0RC>TA1%U>2SMS=%XL2SA1%TH5U3RF?TD1%VL2UERG%VI2RHSL%V1221r3%Y22SGSK%UF2U>1%Y42U91%Y52S0WO%UI2UA1%XJ231u4&Q0%UM2S5SF%Y;2SJ1%321TN%U85UC<651p0>1pSDY@1%VA2C1%VB2G1%VC2J1%VD2Q@1%VE2QC1%VF2RD1%VG2RI1%VH2RL1%VI2RO1%VJ2S21%VK2S51%VL2S81%VM2S;1%VN2S?1%VO2SC1%W02SF1qNZ21%T72Z31qTFZ91%T92Z:1p0T;1p0T?1p0TC1p0TG1p0TK1p0TO1p0U41p0U91p0U?1p0UD1p0UI1p0UN1p0V51p0V=1p0VE1p0VK1p0W01p0W21p0W41p0W<1p0W>1p0WA1p0WF1p0WM1p0X31p0X:1p0X<1p0XB1p0XD1p0XG1p0XM1p0Y21p0Y91p0Y?1p0YG1p0YO1p0Z71p0ZA1p0ZH1tRN[<[81pS<[D1pS:[E1pS8[F1pS6[G1pS4[H1pS@[I1pS>[J1pS0[D1pT6[E1pT8[F1pT4[G1pRF[H1pU:[I1pTB[J1pT>[K1pTN[L1pT@\41pTH[O1pL\01pTD\61")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_clspop_D) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_clspop_D) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_clspop_D) 2%nat 0%nat).
Variable raw : ltac:(sec_ty2 constr:(SEC_T_art_clspop_D) 3%nat 0%nat).
Variable sp : ltac:(sec_ty2 constr:(SEC_T_art_clspop_D) 4%nat 0%nat).
Variable r : ltac:(sec_ty2 constr:(SEC_T_art_clspop_D) 5%nat 0%nat).
Variable rb : ltac:(sec_ty2 constr:(SEC_T_art_clspop_D) 6%nat 0%nat).
Variable sz : ltac:(sec_ty2 constr:(SEC_T_art_clspop_D) 7%nat 0%nat).
Variable au : ltac:(sec_ty2 constr:(SEC_T_art_clspop_D) 8%nat 0%nat).
Variable mu' : ltac:(sec_ty2 constr:(SEC_T_art_clspop_D) 9%nat 0%nat).
Variable nf : ltac:(sec_ty2 constr:(SEC_T_art_clspop_D) 10%nat 0%nat).
Variable new : ltac:(sec_ty2 constr:(SEC_T_art_clspop_D) 11%nat 0%nat).
Variable fb : ltac:(sec_ty2 constr:(SEC_T_art_clspop_D) 12%nat 0%nat).
Variable g8 : ltac:(sec_ty2 constr:(SEC_T_art_clspop_D) 13%nat 0%nat).
Variable g9 : ltac:(sec_ty2 constr:(SEC_T_art_clspop_D) 14%nat 0%nat).
Variable g18 : ltac:(sec_ty2 constr:(SEC_T_art_clspop_D) 15%nat 0%nat).
Variable g19 : ltac:(sec_ty2 constr:(SEC_T_art_clspop_D) 16%nat 0%nat).
Variable g20 : ltac:(sec_ty2 constr:(SEC_T_art_clspop_D) 17%nat 0%nat).
Variable g21 : ltac:(sec_ty2 constr:(SEC_T_art_clspop_D) 18%nat 0%nat).
Variable g22 : ltac:(sec_ty2 constr:(SEC_T_art_clspop_D) 19%nat 0%nat).
Lemma art_clspop_D : ltac:(sec_stmt2 constr:(SEC_T_art_clspop_D) 20%nat 0%nat).
Proof using Type regs M rom raw sp r rb sz au mu' nf new fb g8 g9 g18 g19 g20 g21 g22.
intros fa H2 H8 H9 H10 H18 H19 H20 H21 IMG Hsp' Hret Hr Hr' Hrb Hrb' Arfa Hsz Hfb Hau Hnew Haumu Hmu' Hnf Htot
Wr Wfa Cau Cnf Cmu Cam Cmm F1 F8 F9 F18 F19 F20 F21 F22.
assert (Hfa : fa = rb + 3758096384) by reflexivity. clearbody fa.
pose proof (art_pop_d_fn regs M rom r rb sz au (nf + new) fb H10 H8 H9 H18 H20 H21 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hsz Hfb ltac:(lia) ltac:(lia) Cau) as RUN1.
match type of RUN1 with msteps _ _ (mkst ?R _ _ _) => set (r1 := R) in RUN1 end.
set (E := fa + 4 * (nf + new)).
destruct (art_pop_loop (Z.to_nat new) r1 M rom E au sz 0 new
ltac:(unfold r1; gres; reflexivity) ltac:(unfold r1, E; gres; f_equal; lia) ltac:(unfold r1; gres; f_equal; lia) ltac:(unfold r1; gres; exact H19) ltac:(unfold r1; gres; exact H21)
ltac:(lia) ltac:(lia) ltac:(lia) Hau Hsz ltac:(lia) ltac:(unfold E; lia) ltac:(unfold E; lia)
ltac:(rewrite Z2Nat.id by lia; replace (E - 4 * new) with (fa + 4 * nf) by (unfold E; lia); exact Wfa))
as (r2 & RUN2 & K2).
set (M2 := art_carve M E au sz 0 (Z.to_nat new)) in *.
assert (A2 : art_agree [(fa + 4 * nf, 4 * new)] M M2).
{ pose proof (art_agree_carve (Z.to_nat new) M E au sz 0 ltac:(lia) ltac:(unfold E; lia) ltac:(unfold E; lia)) as A. rewrite Z2Nat.id in A by lia.
replace (E - 4 * (0 + new)) with (fa + 4 * nf) in A by (unfold E; lia). exact A. }
assert (G2 : mem_grows M M2) by apply art_carve_grows.
assert (R2 : forall x : reg, x <> 10%bv -> x <> 12%bv -> x <> 14%bv -> x <> 15%bv -> getr r2 x = getr r1 x) by exact K2.
assert (UB : forall w : word, 0 <= U w < 2 ^ 64). { intros w. pose proof (bv_unsigned_in_range 64 w) as R. change (bv_modulus 64) with (2 ^ 64) in R. exact R. }
unfold apart in Arfa.
pose proof (art_pop_e_fn r2 M2 rom raw sp r sz new au nf mu' 0 0 (new * sz) (U g8) (U g9) (U g18) (U g19) (U g20) (U g21) (U g22)
ltac:(rewrite R2 by (intros E0; discriminate E0); unfold r1; gres; exact H2) ltac:(rewrite R2 by (intros E0; discriminate E0); unfold r1; gres; exact H8)
ltac:(rewrite R2 by (intros E0; discriminate E0); unfold r1; gres; reflexivity) ltac:(rewrite R2 by (intros E0; discriminate E0); unfold r1; gres; exact H19)
ltac:(rewrite R2 by (intros E0; discriminate E0); unfold r1; gres; exact H21)
ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hsz ltac:(lia) ltac:(reflexivity) Hau Haumu ltac:(lia) Hnf ltac:(lia) ltac:(lia) ltac:(lia) Hret
(UB g8) (UB g9) (UB g18) (UB g19) (UB g20) (UB g21) (UB g22)
ltac:(unfold apart; lia) ltac:(eapply wr_grows; [exact G2|exact Wr])
ltac:(ztr) ltac:(ztr) ltac:(ztr) ltac:(ztr) ltac:(ztr) ltac:(ztr) ltac:(ztr) ltac:(ztr) ltac:(ztr) ltac:(ztr) ltac:(ztr) ltac:(ztr)) as RUN3.
match type of RUN3 with msteps _ _ (mkst ?R _ ?MM _) => set (r3 := R) in RUN3; set (M3 := MM) in RUN3 end.
assert (A3 : art_agree [(r + 16, 8); (r + 32, 8); (r + 68, 1)] M2 M3). { unfold M3. eapply art_agree_sub; [zagree|]. zsub. }
assert (G3 : mem_grows M2 M3) by (unfold M3; zgrows).
exists r3, M3. split; [eapply msteps_trans; [exact RUN1|]; eapply msteps_trans; [exact RUN2|exact RUN3]|].
split; [unfold r3; gres; reflexivity|]. split; [unfold r3; gres; reflexivity|]. split; [unfold r3; gres; reflexivity|].
split; [unfold r3; gres; apply Z_to_bv_bv_unsigned|]. split; [unfold r3; gres; apply Z_to_bv_bv_unsigned|]. split; [unfold r3; gres; apply Z_to_bv_bv_unsigned|].
split; [unfold r3; gres; apply Z_to_bv_bv_unsigned|]. split; [unfold r3; gres; apply Z_to_bv_bv_unsigned|]. split; [unfold r3; gres; apply Z_to_bv_bv_unsigned|].
split; [unfold r3; gres; apply Z_to_bv_bv_unsigned|].
split. { intros x Hx. cbn [In] in Hx. repeat match type of Hx with _ \/ _ => destruct Hx as [<-|Hx] | False => destruct Hx end;
(unfold r3; gres; rewrite R2 by (intros E0; discriminate E0); unfold r1; gres; reflexivity). }
split; [eapply mem_grows_trans; [exact G2|exact G3]|].
split. { eapply art_agree_sub; [eapply art_agree_trans; [exact A2|exact A3]|]. zsub. }
split; [unfold M3; zcell|]. split; [unfold M3; zcell|].
intros j Hj. assert (C2 : cellA M2 (E - 4 * (j + 1)) 4 ((au + j * sz) / 16)).
{ unfold M2. apply cell_carve_hit; [lia|unfold E; lia|unfold E; lia|rewrite Z2Nat.id by lia; lia]. }
fold E. ztr.
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_art_clspop_Cw := (ltac2:(TCodec.tc2 tcn__JbtClsPop2 "V<&<y5'RByR0%211%5241'3y8%611%311p061':'8&Jr7(R@+1(6%33A21%6251+ZlgH%63B14/01B%;3C41r8+2%;3I19%>231&RA&Q7r5+R0%3221%52N1%F3N71r9+;%F3Q41D%I231%;2Q49%L3Q421r:+=%L3Q:1J%O231%Q13Q916&Q1&O+Vb\P0+S@%3221%521K&Q2&Q6+Q?%22N1%42E1%;29F+T0%<2B1r;%Q021<%@231z%B21G&Q4+4%2217%F21K%@2Q<Q6%B2:1&A&MrAr?%Q>21J+Q@%645421&@rB+H%Q2271u8r=%65<5321'9'7'C&KvQ@rF+Zca8%R=3RI1R;/01RIrErD%8576321r2r1%;5:2R=14%=3L41+:%RG3S51RE%RJ261%R<2S5RH%RM3S521%RM29R@rC%R?21R=%RA2S:1%S23S:41%S=1S>&N(0+3%S43SB1S2%S53SCQBS3+8%S73SE1S5+9%S93SG1S7+B%S;3SI1S9+C%S=3SK1S;+D%S?3SM1S=+E%SA3SO1S?+F%SC3T11SA+G%SE3T31SC%SF3T4QESD+I%SH3T61SF+J%SJ3T81SH+K%SL3T:1SJ(2%11N%M3O31%N3Q061%O3Q191%Q03Q2<1%Q13Q3>1%Q23Q4A1%Q33Q5D1%Q43Q6G1%Q53Q7J1%Q63Q8M1%Q73Q9Q01%Q83Q:Q31%Q93Q;Q61%Q:3Q<Q81%Q<3Q=QJ1r4%TA21QMrH%TC21QO%TE3TM31p061pUDQD1&L%12R7R3&E'5%12TMTM(4%T=2QOSI%24U0U01RO%Q014%QL3521%831R@R<%RI2:1%RJ2=1%RK2R31%RL2R91%RM2R?1qNU:1%S02U;1qTFUA1%S22UB1p0S41p0S<1p0SD1p0SG1p0SL1p0SO1p0T51p0T71p0T=1p0TD1p0TJ1p0U11p0U=1pT2UJ1pU>UK1pT>UL1pTNUM1pTHUO1pLV01pTDV61")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_clspop_Cw) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_clspop_Cw) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_clspop_Cw) 2%nat 0%nat).
Variable sp : ltac:(sec_ty2 constr:(SEC_T_art_clspop_Cw) 3%nat 0%nat).
Variable r : ltac:(sec_ty2 constr:(SEC_T_art_clspop_Cw) 4%nat 0%nat).
Variable total : ltac:(sec_ty2 constr:(SEC_T_art_clspop_Cw) 5%nat 0%nat).
Variable mfa : ltac:(sec_ty2 constr:(SEC_T_art_clspop_Cw) 6%nat 0%nat).
Lemma art_clspop_Cw : ltac:(sec_stmt2 constr:(SEC_T_art_clspop_Cw) 7%nat 0%nat).
Proof using Type regs M rom sp r total mfa.
intros H1 H2 H11 H13 IMG Hsp' Hr Hr' Htot Hmfa Hmfa' W Cmfa.
pose proof (art_efas_warm_fn regs M rom (0x572f8 : bv 64)%bv (sp - 64) r total mfa H1 ltac:(unfold ret_ok; bveq) H2 H11 H13 ltac:(lia) ltac:(lia) ltac:(lia) Hr ltac:(lia) Htot Hmfa Hmfa'
ltac:(unfold apart; lia) ltac:(replace (sp - 64 - 48) with (sp - 112) by lia; exact W) Cmfa) as RUN.
match type of RUN with msteps _ _ (mkst ?R _ ?MM _) => set (r1 := R) in RUN; set (M1 := MM) in RUN end.
exists r1, M1. split; [exact RUN|].
split; [unfold r1; gres; reflexivity|]. split; [unfold r1; gres; reflexivity|].
split. { intros x Hx. cbn [In] in Hx. repeat match type of Hx with _ \/ _ => destruct Hx as [<-|Hx] | False => destruct Hx end; (unfold r1; gres; reflexivity). }
split; [unfold M1, art_efas_frame; zgrows|]. unfold M1, art_efas_frame. eapply art_agree_sub; [zagree|]. zsub.
Qed.
End SE.
#[using="Type"] Lemma art_mod4096_lin2 : ltac2:(TCodec.tc2 tcn__JbtClsPop2 "J':'8&Q3&O&Q4+TP0r3%3221r2&Q6+2+Q0%3221%9251%;271+S`PPPP0%=221r1%>2=1%@231%B21?z%E3F21pRJG1pRHH1pRBI1").
Proof. intros a b c. replace (4096 * a + b * 2 ^ 32 + 3758096384 + 4096 * c) with ((a + b * 2 ^ 20 + 917504 + c) * 4096) by lia. apply Z_mod_mult. Qed.
Section SE.
Local Abbreviation SEC_T_art_clspop_Cm1 := (ltac2:(TCodec.tc2 tcn__JbtClsPop2 "[L&<y5'RByR0%211%5241'3y8%611%311p061':'8r1&Or8&Q4r9&Q6+2+Q0%3221%6251%9281+S`PPPP0%;221r5%=221%@3A?1&Jr?(R@+1(6%33Q121%6251+ZlgH%63Q214/01Q2%K3Q341r@%:3Q8F8%=221&RA&Q7r=+R0%3221%52Q=1%Q53Q=71rA+:%E3QC1C%H231+QWTnH%<2QD1%Q<3QD31rB+;%L3QJ1J%O231r>%C2QK1%QC3QK31rC+<%Q33R11Q1%Q6231%QD27Q?%QG2H1%K2R31%QK3R341rD+=%Q;3R91Q9%Q>231r<%Q22R:1%R23R:31&Q1+Vb\P0+`0%R4221%421J&Q2+Q?%R42R31%32G1'7%:2QIQ0+N%<2Q21%4231%>2=ErE+T0%RB221rF%QF21A%D231z%F21M+Q5%RE2RD1%RJ2:1%E21C+RPP0%RK21=%S03S1;1%N29?+4%RO21>%L2B1%I241+XPP0%S321E%S83S9C1rH%S6281+WooO%S:221%S;26QA%S>3S?21%Q72M9%Q42?1rG%S>2<1+`PPPP0%QA221&A&MrQ2rQ0%RI21QD+^0%645421&@rQ3+H%SM271u8rK%65<5321rQ4+QH%T32RK1u1%;5A421Q?rQ5+QV`l0+QiaW0%?5E32;1rQ6+TP0%B5H24>1rQ7+QV`l@+Qii[8%F5L32B1rQ8+X4%TC241%J5Q031@QN'9'C&KvQ@rQ<+Zca8%T:3U61T8/01U6rQ;rQ:%8576321r2+a]_H%TA3U=1T?/01U=%=5<41U56%?3QA61&BrOrQ1%U72R51%T<21Q?+QB%64<521%TN2=TI+admH%TB2UJ1%UB3UJ31%U22ATFrQ9+S@%TF221%TG21S4%TI2V11%UI3V161+8%U83V61U6%U;2J1%TN2V6A%UN3V621%V91V:&N(0+3%U@3V>1U>%UA3V?S2U?+E%UC3VA1UA+F%UE3VC1UC+G%UG3VE1UE%UH3VFR=UF+I%UJ3VH1UH+J%UL3VJ1UJ+K%UN3VL1UL(2%11D%C3E31%D3F61%E3G91%F3H<1%G3I>1%H3JA1%I3KD1%J3LG1%K3MI1%M3NVL1r4%V>21QMrQ>%V@21QO%W23W:31p061pUDQ51&L%12R7W5&E'5%12W:W:(4%V;2QGU6%24W=W=1SB%K14%Q=3521%831R@W>%V@2QLV>%VA21QG%SF5SLWA1SBVJ+@%VD241&RC%W52RKQK%22X01%SL5T2WG4SH1%VI29SK+9%W83X61W6%W;2S11%82X61%T25T8WM5SN1%VO2?WG+B%W>3X<1W<%WA2S71%>2X<1%T85T>X35T41+Q8%W62F1+C%WE3XC1WC%WH2S>1%E2XC1%T?5TEX:5T;1%W<2RFRB+Zcf8%TB5THX=2T>1%W?2RIL%TD5TJX?1T@S5%WA2RKTC%TF5TLXA1TBS9%WC2RMX;%TH5TNXC1TDS8%WE2RO@+be[@%X43Y01X2/01Y0%Q42Y21%TN5U4XI5TJ1+Q@%WL2S61%U15U7XL1TMSA%WN2S8TJ%U35U9XN1TOSF%X02S:WN%U55U;Y01U1SE+R8%X32S=1%U85U>Y31U4TA+R@%X62S@1+D%XE3YC1XC%XH2T>1%QE2YC1%U?5UEY:5U;1%W0281%W12<1%W22?1%W32B1%W42F1%W52M1%W62Q01%W72Q31%W82Q61%W92Q:1%W:2QB1%W;2QI1%W<2R01%W=2R71%W>2R;1%W?2RE1%W@2RH1%WA2SO1%WB2T51%WC2T=1%WD2TB1%WE2TJ1qNZ41%U<2Z51qTFZ;1%U>2Z<1p0U@1p0UE1p0UJ1p0UN1p0V31p0V91p0VA1p0VI1p0VN1p0W11p0W81p0W<1p0WA1p0WC1p0WG1p0WL1p0WO1p0X61p0X81p0X>1p0XC1p0XI1p0Y11p0Y:1p0YB1p0YJ1p0Z51p0ZA1pRD[31pTJ[41pT:[51pSJ[61pT2[71pU>[81pT<[91pU0[:1pRJ[;1pT>[<1pTN[=1pTH[?1pL[@1pTD[F1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_clspop_Cm1) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_clspop_Cm1) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_clspop_Cm1) 2%nat 0%nat).
Variable sp : ltac:(sec_ty2 constr:(SEC_T_art_clspop_Cm1) 3%nat 0%nat).
Variable r : ltac:(sec_ty2 constr:(SEC_T_art_clspop_Cm1) 4%nat 0%nat).
Variable c : ltac:(sec_ty2 constr:(SEC_T_art_clspop_Cm1) 5%nat 0%nat).
Variable spb : ltac:(sec_ty2 constr:(SEC_T_art_clspop_Cm1) 6%nat 0%nat).
Variable qs : ltac:(sec_ty2 constr:(SEC_T_art_clspop_Cm1) 7%nat 0%nat).
Variable total : ltac:(sec_ty2 constr:(SEC_T_art_clspop_Cm1) 8%nat 0%nat).
Variable mfa : ltac:(sec_ty2 constr:(SEC_T_art_clspop_Cm1) 9%nat 0%nat).
Variable kf : ltac:(sec_ty2 constr:(SEC_T_art_clspop_Cm1) 10%nat 0%nat).
Variable q : ltac:(sec_ty2 constr:(SEC_T_art_clspop_Cm1) 11%nat 0%nat).
Variable rr : ltac:(sec_ty2 constr:(SEC_T_art_clspop_Cm1) 12%nat 0%nat).
Variable addr2 : ltac:(sec_ty2 constr:(SEC_T_art_clspop_Cm1) 13%nat 0%nat).
Lemma art_clspop_Cm1 : ltac:(sec_stmt2 constr:(SEC_T_art_clspop_Cm1) 14%nat 0%nat).
Proof using Type regs M rom sp r c spb qs total mfa kf q rr addr2.
intros Haddr2 H1 H2 H10 H11 H12 H13 IMG Hsp' Hc Hr Hr' Hspb Hspb' Espb Htot Hmfa Emfa Eq Hrr Hq W Cmfa Cpm Cpg1 Cpg2 Ccf Cdec.
pose proof (art_efas_a_fn regs M rom (0x572f8 : bv 64)%bv (sp - 64) 1283032 r (spb + c * 2 ^ 32) total mfa q rr H1 H2 H10 H11 H12 H13
ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hr ltac:(lia) ltac:(lia) ltac:(lia) Htot Hmfa Eq Hrr Hq
ltac:(unfold apart; lia) ltac:(eapply wr_sub; [exact W|lia|lia]) Cmfa Cpm) as RUN1.
match type of RUN1 with msteps _ _ (mkst ?R _ ?MM _) => set (r1 := R) in RUN1; set (M1 := MM) in RUN1 end.
assert (A1 : art_agree [(sp - 512, 448)] M M1). { unfold M1, art_efas_frame. eapply art_agree_sub; [zagree|]. zsub. }
assert (G1 : mem_grows M M1) by (unfold M1, art_efas_frame; zgrows).
assert (Hq1 : kf + 1 <= q) by lia.
assert (Ha4 : addr2 mod 4096 = 0).
{ rewrite Haddr2, Espb, Emfa. replace (65536 * qs + c * 2 ^ 32 + 3758096384 + 262144 * kf) with (4096 * (16 * qs) + c * 2 ^ 32 + 3758096384 + 4096 * (64 * kf)) by lia. apply art_mod4096_lin2. }
assert (Hl4 : (262144 * q - mfa) mod 4096 = 0). { rewrite Emfa. replace (262144 * q - 262144 * kf) with ((64 * (q - kf)) * 4096) by lia. apply Z_mod_mult. }
pose proof (art_rar_map_pre_fn r1 M1 rom (0x54ec8 : bv 64)%bv (sp - 112) addr2 (262144 * q - mfa) 105066 0x1ce568 0
ltac:(unfold r1; gres; reflexivity) ltac:(unfold r1; gres; f_equal; lia) ltac:(unfold r1; gres; f_equal; lia) ltac:(unfold r1; gres; f_equal; lia)
ltac:(unfold r1; gres; reflexivity)
ltac:(lia) ltac:(lia) ltac:(lia) Ha4 ltac:(lia) Hl4 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(reflexivity)
ltac:(eapply wr_grows; [exact G1|]; eapply wr_sub; [exact W|lia|lia])
ltac:(ztr) ltac:(ztr) ltac:(ztr) ltac:(ztr)) as RUN2.
match type of RUN2 with msteps _ _ (mkst ?R _ ?MM _) => set (r2 := R) in RUN2; set (M2 := MM) in RUN2 end.
assert (A2 : art_agree [(sp - 512, 400)] M1 M2).
{ intros x Hx. cbn in Hx. destruct Hx as [Hx _]. unfold M2. apply art_rar_map_mem_agree; [lia|lia|lia]. }
assert (G2 : mem_grows M1 M2) by (apply art_rar_map_mem_grows).
destruct (art_rar_map_mem_cells M1 (sp - 112) (0x54ec8 : bv 64)%bv r1 addr2 (262144 * q - mfa) 105066 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
as (F1 & F8 & F9 & F18 & F0 & K8 & K9 & K18 & F19 & F20).
fold M2 in F1, F8, F9, F18, F0, K8, K9, K18, F19, F20.
exists r2, M2. split; [eapply msteps_trans; [exact RUN1|exact RUN2]|].
split. { unfold art_mmap_args, r2. repeat split; gres; reflexivity. }
split; [unfold r2; gres; reflexivity|]. split; [unfold r2; gres; reflexivity|]. split; [unfold r2; gres; reflexivity|].
split. { intros x Hx. cbn [In] in Hx. repeat match type of Hx with _ \/ _ => destruct Hx as [<-|Hx] | False => destruct Hx end; (unfold r2, r1; gres; reflexivity). }
split; [eapply mem_grows_trans; [exact G1|exact G2]|].
split. { eapply art_agree_sub; [eapply art_agree_trans; [exact A1|exact A2]|]. zsub. }
assert (E8 : cellA M1 (sp - 64 - 8) 8 0x572f8 /\ cellA M1 (sp - 64 - 16) 8 (U (getr regs 8)) /\ cellA M1 (sp - 64 - 24) 8 (U (getr regs 9))
/\ cellA M1 (sp - 64 - 32) 8 (U (getr regs 18)) /\ cellA M1 (sp - 64 - 40) 8 (U (getr regs 19))).
{ unfold M1, art_efas_frame. repeat split; zcell. }
destruct E8 as (E1 & E8 & E9 & E18 & E19).
split; [ztr|]. split; [ztr|]. split; [ztr|]. split; [ztr|]. split; [ztr|].
split; [exact F1|].
assert (X8 : U (getr r1 8) = 262144 * q). { unfold r1; gres. rewrite art_u_lit by lia. lia. }
assert (X9 : U (getr r1 9) = addr2). { unfold r1; gres. rewrite art_u_lit by lia. lia. }
assert (X18 : U (getr r1 18) = 262144 * q - mfa). { unfold r1; gres. rewrite art_u_lit by lia. lia. }
assert (X19 : U (getr r1 19) = r). { unfold r1; gres. rewrite art_u_lit by lia. lia. }
assert (X20 : getr r1 20 = getr regs 20). { unfold r1; gres. reflexivity. }
rewrite X8 in F8. rewrite X9 in F9. rewrite X18 in F18, K18. rewrite X19 in F19. rewrite X20 in F20.
split; [exact F8|]. split; [exact F9|]. split; [exact F18|]. split; [exact F0|]. split; [exact K8|]. split; [exact K9|]. split; [exact K18|].
split; [exact F19|]. exact F20.
Qed.
End SE.
#[using="Type"] Lemma art_div8_lin2 : ltac2:(TCodec.tc2 tcn__JbtClsPop2 "Q6':'8&Q0&O&Q4+RPP0r3%3221r2&Q6+2+Q0%3221%9251%;271+S`PPPP0%=221+XPP0r1%?221%A241+8%D221+XP0%D21B+M%A2@1%G2C1%I241+^PPPP0%K221+QPP0%L21>%N231%Q13Q2<1pSJQ31pRJQ41pT<Q51").
Proof. intros. replace (65536 * qs + c * 2 ^ 32 + 3758096384 + 262144 * kf) with ((8192 * qs + c * 2 ^ 29 + 469762048 + 32768 * kf) * 8) by lia. apply Z_div_mult. lia. Qed.
#[using="Type"] Lemma art_mod8_lin2 : ltac2:(TCodec.tc2 tcn__JbtClsPop2 "L':'8&Q3&O&Q4+RPP0r3%3221r2&Q6+2+Q0%3221%9251%;271+S`PPPP0%=221+XPP0r1%?221%A241+8%D221z%G3H21pSJI1pRJJ1pT<K1").
Proof. intros. replace (65536 * qs + c * 2 ^ 32 + 3758096384 + 262144 * kf) with ((8192 * qs + c * 2 ^ 29 + 469762048 + 32768 * kf) * 8) by lia. apply Z_mod_mult. Qed.
Section SE.
Local Abbreviation SEC_T_art_clspop_Cm2 := (ltac2:(TCodec.tc2 tcn__JbtClsPop2 "`3&<y5'RByR0%211%5241'3y8%611%311p061':'8r8&Or?&Q4r@&Q6+2+Q0%3221%6251%9281+S`PPPP0%;221r=%=221%@3A?1&Q7+XPP0r<%@221r>%5221%G3HF1+QoooPP0+XP0%F21E%I231rB+M%H2G1%K231%N251+^PPPP0%Q0221+QPP0%Q021?%Q3231%Q63Q7Q51&JrM(R@+1(6%33QG21%6251&RA+admH%22QI1%QA3QI41rN%:3QNQ<8%=221rK+S@%Q6221+T0%Q8221%<2R31%QK3R371rO+4%E3R91C%H231%B2R9;%R13R921rQ0+8%K3R?1I%N231%H2R?QH%R73R?21rQ1+:%Q13RE1O%Q4231%N2RER9%R=3RE21&Q1+Vb\P0+`0%R?221%421F&Q2+Q?%R?2R>1%32D1'7rJ%;2Q?1+N%=231%5231+RPP0rI%RK221%S03S181rH%RN2R@1%S33S451z%G217%S42>QL%I219%S42RF@+`PPPP0%L221&H%N21Q@+Q5%S82S71%S=2Q=1%M21KrL%Q42>1+R0%S>2S=1%Q2241%O241+TP0rQ6%Q;221rQ7%SI214rQ<%S<21Q=%Q@231%QA2Q@5rQ8%SO21R9rQ>%SB21QC%QF231&?rQ:rQ9%342A1R@+RPX0rQ?%QM221rQ@%T;21R:%R021QO%R12QB5+QP0%T?251%R421R3%R52L7rQA%TC21NrQE%T621R7%R:231rQ5rQ;%T:2E1%TH2SI1%H4419Q6%T=24Q2%TK2SL1%K4Q81<S8rQ=%TA2Q61%TO2T01rQD%Q04Q;21Q>%TE25Q4%U32T41%U62Q81rQI%TI21RJ%RM231&A&MrQLrQJ%TO21S0+\@%645421rQM%U32Q:Q8%UA2TB1%:493Q@1rQNrQG+RiH%UH221+@%@4?521rQO%B4A16T6&GrR0%211&FrR1rQK%362>BG1F&@rR2%UG28RE%UH21T6u8+ZlgH%65O5321rR3%UM2;RK%UN21D&RC%12VJR7%<5Q55381rR4%V32=S1+H%V5221%A5Q:41=6rR5%V82<S6%V921VB%E5Q>31A:rR6%V<2:S:+Q8%V>221%J5QC41F?rR7%VA2:U<%VB21U0+Zcf8%O5QH42K1rR8%VF2;UA%VG21Q=%W52VGQJ%Q45QM42Q01rR9%VK2;UF%VL21HrQH%Q95R242Q51rR:%W02;UK%W121W:%Q=5R631Q95rR;%W42:UO%W521H+be[@%V?3X11V=/01X1%Q:2X31%QE5R>75QA1rR<%W<2=V7+Q@%W>221%QJ5RC41QFRArR=%WA2>V<+QH%WC221%QO5RH41QKRGrR>%WF2;VA%WG21TE%R35RL31QORKrR?%WJ2:VE+R8%WL221%R85S141R4Q=rR@%WO2:VJ+R@%X1221%R32XLQ5%R>5S752R:1rRA+QV`l@+Qii[8%RB5S;32R>1rRB+T@%XI241%RF5S?31RBUHrRC%XL2Q2S5%RI5SB21RER<rRD+Rj0%Y02Q11%RM5SF31RIR@'9'C&KvQ@rRH+a]_L%X13YC1WO/01YCrRGrRF%8576321r2%X73YIS5X5/01YIr1%=5<4216%?3T761%X>26W;%X82YOX<%YG3YO21%XA29X5rRE%Y921V7%X=2Z41%YL3Z441%XF2>WI%YN3Z61SA+9%XG3Z;1XE%XJ2B1%Z23Z:1SK+B%XK3Z?1XI%XN2F1%Z63Z>1T3+C%XO3ZC1XM%Y22J1%Z:3ZB1T:+D%Y33ZG1Y1%Y62N1%Z>3ZF1TA%ZI1ZJ&N(0+3%Y:3ZN1Y8+E%Y<3[01Y:+F%Y>3[21Y<+G%Y@3[41Y>%YA3[5T5Y?+I%YC3[71YA+J%YE3[91YC+K%YG3[;1YE(2%11C%B3D31%C3E61%D3F91%E3G<1%F3H>1%G3IA1%H3JD1%I3KY<1%J3LH1%L3MQJ1r4%Z721QOrRJ%Z921R1%[A3[I31p061pUDQ41&L%12R9R3&E'5%12[I[I(4%[92R1Y:%24[L[L1V:%[;2TAT<%[I2ZJ1%54[O[OU;1%[M2S@V6%74\1\11V5%[O2SGU<%94\3\31YO%Q21;%QC3<21%QD3=51%QE3>81%QF3?<1%B31RLRF%\72U3ZO%V45VMRH;V01%\92SLS:%\:2U;UD%V75W0RK2V31%\:2[LU3%V95W2RM>V51%YI231%YJ271%YK2:1%YL2N1%YM2Q11%YN2R71%YO2R<1%Z02RA1%Z12RF1%Z22RK1%Z32RN1%Z42S41%Z52S81qN\O1%SJ2]01qTF]61%SL2]71p0SN1p0T31p0T71p0T<1p0TA1p0TH1p0TN1p0U31p0U91p0U?1p0UH1p0UM1p0V31p0V91p0V?1p0VE1p0VJ1p0W01p0W71p0W?1p0WD1p0WH1p0WK1p0X21p0X71p0X?1p0XF1p0XL1p0Y01p0Y61p0Y<1p0Y>1p0YB1p0YD1p0YH1p0YL1p0Z11p0Z71p0Z91p0Z?1p0ZC1p0ZD1p0ZK1p0[01p0[31p0[71p0[:1p0[=1p0[A1p0[F1p0[M1p0\21p0\81p0\?1p0\F1p0\M1p0]81p0]D1p0^41p0^<1pS8_51pS6_61pS4_71pS@_81pS>_91pTL_31pSL_41pRD_51pT0_61pSN_71pT:_81pSJ_91pT2_:1pT<_;1pU0_<1pRJ_=1pT>_>1pU<_?1pRL_@1pUB_A1pSH_B1pU@_C1pTN_D1pTH_F1pL_G1pTD_M1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_clspop_Cm2) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_clspop_Cm2) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_clspop_Cm2) 2%nat 0%nat).
Variable sp : ltac:(sec_ty2 constr:(SEC_T_art_clspop_Cm2) 3%nat 0%nat).
Variable tp : ltac:(sec_ty2 constr:(SEC_T_art_clspop_Cm2) 4%nat 0%nat).
Variable key : ltac:(sec_ty2 constr:(SEC_T_art_clspop_Cm2) 5%nat 0%nat).
Variable tsd : ltac:(sec_ty2 constr:(SEC_T_art_clspop_Cm2) 6%nat 0%nat).
Variable ctx : ltac:(sec_ty2 constr:(SEC_T_art_clspop_Cm2) 7%nat 0%nat).
Variable t : ltac:(sec_ty2 constr:(SEC_T_art_clspop_Cm2) 8%nat 0%nat).
Variable r : ltac:(sec_ty2 constr:(SEC_T_art_clspop_Cm2) 9%nat 0%nat).
Variable c : ltac:(sec_ty2 constr:(SEC_T_art_clspop_Cm2) 10%nat 0%nat).
Variable spb : ltac:(sec_ty2 constr:(SEC_T_art_clspop_Cm2) 11%nat 0%nat).
Variable qs : ltac:(sec_ty2 constr:(SEC_T_art_clspop_Cm2) 12%nat 0%nat).
Variable mfa : ltac:(sec_ty2 constr:(SEC_T_art_clspop_Cm2) 13%nat 0%nat).
Variable kf : ltac:(sec_ty2 constr:(SEC_T_art_clspop_Cm2) 14%nat 0%nat).
Variable q : ltac:(sec_ty2 constr:(SEC_T_art_clspop_Cm2) 15%nat 0%nat).
Variable m1 : ltac:(sec_ty2 constr:(SEC_T_art_clspop_Cm2) 16%nat 0%nat).
Variable m2 : ltac:(sec_ty2 constr:(SEC_T_art_clspop_Cm2) 17%nat 0%nat).
Variable addr2 : ltac:(sec_ty2 constr:(SEC_T_art_clspop_Cm2) 18%nat 0%nat).
Variable len2 : ltac:(sec_ty2 constr:(SEC_T_art_clspop_Cm2) 19%nat 0%nat).
Variable shb2 : ltac:(sec_ty2 constr:(SEC_T_art_clspop_Cm2) 20%nat 0%nat).
Variable g8 : ltac:(sec_ty2 constr:(SEC_T_art_clspop_Cm2) 21%nat 0%nat).
Variable g9 : ltac:(sec_ty2 constr:(SEC_T_art_clspop_Cm2) 22%nat 0%nat).
Variable g18 : ltac:(sec_ty2 constr:(SEC_T_art_clspop_Cm2) 23%nat 0%nat).
Variable g19 : ltac:(sec_ty2 constr:(SEC_T_art_clspop_Cm2) 24%nat 0%nat).
Variable g20 : ltac:(sec_ty2 constr:(SEC_T_art_clspop_Cm2) 25%nat 0%nat).
Lemma art_clspop_Cm2 : ltac:(sec_stmt2 constr:(SEC_T_art_clspop_Cm2) 26%nat 0%nat).
Proof using Type regs M rom sp tp key tsd ctx t r c spb qs mfa kf q m1 m2 addr2 len2 shb2 g8 g9 g18 g19 g20.
intros Haddr2 Hlen2 Hshb2 H1 H2 H4 H8 H10 IMG Hsp' Hc Espb Emfa Hkf Hq1 Hq Hspb Hspb'
Hm1 Hm2 Ht Ht' Hr Hr' Atr Htp Htp' Htsd Htsd' Hctx Hctx' Ast Asr Asc Hshsp W Wsh Wts Wr L T E1 E8 E9 E18 E19 F1 F8 F9 F18 F0 K8 K9 K18 F19 F20 Ccf Clim Cm1 Cm2.
unfold kHighMemBeg in Hspb.
assert (Eshb : SB + addr2 / 8 = shb2). { rewrite Haddr2, Hshb2. unfold SB. rewrite Espb, Emfa, art_div8_lin2. lia. }
assert (El8 : len2 / 8 = 32768 * (q - kf)). { rewrite Hlen2, Emfa. replace (262144 * q - 262144 * kf) with ((32768 * (q - kf)) * 8) by lia. apply Z_div_mult. lia. }
assert (Hl8 : len2 mod 8 = 0). { rewrite Hlen2, Emfa. replace (262144 * q - 262144 * kf) with ((32768 * (q - kf)) * 8) by lia. apply Z_mod_mult. }
assert (UB : forall w : word, 0 <= U w < 2 ^ 64). { intros w. pose proof (bv_unsigned_in_range 64 w) as R. change (bv_modulus 64) with (2 ^ 64) in R. exact R. }
pose proof (art_rar_map_post_fn regs M rom (0x54ec8 : bv 64)%bv (Z_to_bv 64 (262144 * q)) (Z_to_bv 64 addr2) (Z_to_bv 64 len2) (Z_to_bv 64 r) g20
(sp - 112) len2 addr2 addr2 0x1ce568 H1 H2 H8 H10 ltac:(unfold ret_ok; bveq) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
ltac:(eapply wr_sub; [exact W|lia|lia])
ltac:(exact F1) ltac:(rewrite art_u_lit by lia; exact F8) ltac:(rewrite art_u_lit by lia; exact F9) ltac:(rewrite art_u_lit by lia; exact F18)
F0 K8 K9 ltac:(rewrite art_u_lit by lia; exact K18) ltac:(rewrite art_u_lit by lia; exact F19) ltac:(exact F20)
Ccf Clim) as RUN1.
match type of RUN1 with msteps _ _ (mkst ?R _ ?MM _) => set (r1 := R) in RUN1; set (M1 := MM) in RUN1 end.
assert (A1 : art_agree [(sp - 512, 400)] M M1). { eapply art_agree_sub; [unfold M1; zagree|]. zsub. }
assert (G1 : mem_grows M M1) by (unfold M1; zgrows).
pose proof (art_efas_b_fn r1 M1 rom addr2 len2 ltac:(unfold r1; gres; reflexivity) ltac:(unfold r1; gres; reflexivity) ltac:(unfold r1; gres; reflexivity) ltac:(lia)) as RUN2.
match type of RUN2 with msteps _ _ (mkst ?R _ _ _) => set (r2 := R) in RUN2 end.
assert (L1 : art_layout M1). { eapply art_layout_fp; [exact A1| |exact L]. intros z Hz. cbn. repeat split; lia. }
destruct (art_poison_hi_run r2 M1 rom (0x54ee4 : bv 64)%bv (sp - 112) addr2 len2 250
ltac:(unfold r2; gres; reflexivity) ltac:(unfold ret_ok; bveq) ltac:(unfold r2, r1; gres; reflexivity) ltac:(unfold r2; gres; reflexivity)
ltac:(unfold r2; gres; reflexivity) ltac:(unfold r2; gres; reflexivity)
ltac:(lia) ltac:(lia) ltac:(eapply wr_grows; [exact G1|]; eapply wr_sub; [exact W|lia|lia]) ltac:(unfold apart; lia) ltac:(unfold apart; lia)
L1 ltac:(unfold kHighMemBeg; lia) ltac:(unfold kHighMemEnd; lia)
ltac:(rewrite Haddr2, Espb, Emfa; apply art_mod8_lin2) Hl8 ltac:(lia) ltac:(lia) ltac:(intros E; discriminate E)
ltac:(rewrite Eshb, El8; eapply wr_grows; [exact G1|exact Wsh]))
as (r3 & RUN3 & P10 & P1 & P2 & P8 & P9 & P18 & P19 & P20 & P21 & KP).
match type of RUN3 with msteps _ _ (mkst _ _ ?MM _) => set (M3 := MM) in RUN3 end.
assert (A3 : art_agree [(sp - 512, 400); (shb2, 32768 * (q - kf))] M1 M3).
{ unfold M3, art_poison_frame. rewrite Eshb, El8. eapply art_agree_sub; [zagree|]. rewrite Z2Nat.id by lia. zsub. }
assert (G3 : mem_grows M1 M3) by (unfold M3, art_poison_frame; zgrows).
assert (A13 : art_agree [(sp - 512, 400); (shb2, 32768 * (q - kf))] M M3). { eapply art_agree_sub; [eapply art_agree_trans; [exact A1|exact A3]|]. zsub. }
assert (G13 : mem_grows M M3) by (eapply mem_grows_trans; eassumption).
assert (Hqs : 0 <= qs) by lia.
assert (T3 : art_tsd M3 tp key tsd ctx t).
{ eapply art_tsd_fp; [exact A13| | |exact Htp|exact Htp'|exact Htsd|exact Htsd'|exact T].
- intros z Hz. cbn. repeat split; lia.
- intros z Hz. cbn. unfold apart in Asc. repeat split; lia. }
assert (R3_4 : getr r3 4 = Z_to_bv 64 tp). { rewrite KP by (unfold art_poison_kept; repeat split; intros E; discriminate E). unfold r2, r1; gres. exact H4. }
assert (R3_8 : getr r3 8 = Z_to_bv 64 (262144 * q)). { rewrite P8. unfold r2, r1; gres. reflexivity. }
assert (R3_18 : getr r3 18 = Z_to_bv 64 len2). { rewrite P18. unfold r2, r1; gres. reflexivity. }
assert (R3_19 : getr r3 19 = Z_to_bv 64 r). { rewrite P19. unfold r2, r1; gres. reflexivity. }
unfold apart in Ast, Asr, Atr.
pose proof (art_efas_c_fn r3 M3 rom (0x572f8 : bv 64)%bv (sp - 64) tp key tsd ctx t r (262144 * q) len2 m1 m2 (U g8) (U g9) (U g18) (U g19)
ltac:(rewrite P2; f_equal; lia) R3_4 R3_8 R3_18 R3_19
ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold ret_ok; bveq)
Hm1 Hm2 ltac:(lia) ltac:(lia) (UB g8) (UB g9) (UB g18) (UB g19)
ltac:(eapply wr_grows; [exact G13|]; eapply wr_sub; [exact W|lia|lia]) T3
ltac:(unfold apart; lia) ltac:(unfold apart; lia) ltac:(unfold apart; destruct T as (_ & _ & _ & _ & _ & _ & _ & Hk & _); lia) ltac:(unfold apart; lia)
ltac:(unfold apart; lia) ltac:(unfold apart; lia) ltac:(unfold apart; lia)
ltac:(eapply wr_grows; [exact G13|exact Wts]) ltac:(eapply wr_grows; [exact G13|exact Wr])
ltac:(ztr) ltac:(ztr) ltac:(change (U (0x572f8 : bv 64)%bv) with 0x572f8; ztr) ltac:(ztr) ltac:(ztr) ltac:(ztr) ltac:(ztr)) as RUN4.
match type of RUN4 with msteps _ _ (mkst ?R _ ?MM _) => set (r4 := R) in RUN4; set (M4 := MM) in RUN4 end.
assert (A4 : art_agree [(sp - 512, 400); (t + 2872, 16); (r + 24, 8)] M3 M4).
{ unfold M4, art_efas_c_mem. eapply art_agree_sub; [zagree|]. zsub. }
assert (G4 : mem_grows M3 M4) by (unfold M4, art_efas_c_mem; zgrows).
exists r4, M4. split; [eapply msteps_trans; [exact RUN1|]; eapply msteps_trans; [exact RUN2|]; eapply msteps_trans; [exact RUN3|exact RUN4]|].
split; [unfold r4; gres; reflexivity|]. split; [unfold r4; gres; reflexivity|].
split; [unfold r4; gres; apply Z_to_bv_bv_unsigned|]. split; [unfold r4; gres; apply Z_to_bv_bv_unsigned|].
split; [unfold r4; gres; apply Z_to_bv_bv_unsigned|]. split; [unfold r4; gres; apply Z_to_bv_bv_unsigned|].
split; [unfold r4; gres; rewrite P20; unfold r2, r1; gres; reflexivity|].
split. { intros x Hx. cbn [In] in Hx. repeat match type of Hx with _ \/ _ => destruct Hx as [<-|Hx] | False => destruct Hx end;
first [ unfold r4; gres; rewrite KP by (unfold art_poison_kept; repeat split; intros E; discriminate E); unfold r2, r1; gres; reflexivity
| unfold r4; gres; rewrite P21; unfold r2, r1; gres; reflexivity ]. }
split; [eapply mem_grows_trans; [exact G13|exact G4]|].
split. { eapply art_agree_sub; [eapply art_agree_trans; [exact A13|exact A4]|]. zsub. }
unfold M4, art_efas_c_mem.
split; [zcell|]. split; [zcell|]. zcell.
Qed.
End SE.
End FPX.
