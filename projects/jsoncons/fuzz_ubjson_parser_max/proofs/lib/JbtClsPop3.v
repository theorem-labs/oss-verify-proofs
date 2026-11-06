(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib As0Tables
ArtMem ArtRegs ArtAtomics ArtTac JbtLeaf JbtAllocG JbtPoison JbtPoisonRun JbtInitCache ArtRuns ArtRunsMem JbtMmapFixed JbtPopulate1 JbtPopulate2 JbtPopulate3
JbtCls JbtFp JbtClsPop1 JbtClsPop2.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLiaT.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import OtfKit.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__JbtClsPop3 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ArtMem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ArtRuns."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.As0Tables.AsanTab."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Hoare."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtCls."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtClsPop3."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtClsPop3.Spec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtFp."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtLeaf."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtPoison."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.StoreOk."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1app"; "1cons"; "1length"; "1list"; "1nil"; "1option"; "1prod"; "2I"; "2and"; "2eq"; "2ex"; "3Z"; "0EVOK"; "0GR"; "0HI"; "4machine_state"]; ["5bvmap"; "0M"; "0M'"; "0ME"; "0Q"; "6apart"; "6cell"; "6wr"; "7aev"; "7art_at_ecall"; "7aruns"; "8class_size"; "9ret_ok"; ":art_cls"; ":art_cls_mfa'"; ":art_cls_new"]; [":art_cls_ok"; ":art_cls_populate"; ":art_evok_list"; ":art_geo"; ":art_prim_consts"; ":art_region_rep"; ":cl_au"; ":cl_free"; ":cl_mfa"; ":cl_mu"; "<art_pop_fpE"; ";art_pop_events"; ";art_pop_fp"; "=art_agree"; "=art_gap"; ">art_tsd"]; ["?art_layout"; "@getr"; "@mkst"; "Amem_grows"; "Bloaded_segments"; "CIn"; "Dadd"; "Ddiv"; "Dle"; "Dlt"; "Dmul"; "Dof_nat"; "Dpow"; "Dsub"; "0W"; "0c"]; ["0cl"; "0ctx"; "0fa"; "0fx"; "0j"; "0key"; "0km"; "0log"; "0logE"; "0m1"; "0m1'"; "0m2"; "0m2'"; "0mfa'"; "0mx"; "0new"]; ["0nf"; "0qs"; "0r"; "0rE"; "0raw"; "0regs"; "0regs'"; "0req"; "0ris"; "0rom"; "0sp"; "0spb"; "EBV"; "EZ_to_bv"; "Ebv"; "Ebv_unsigned"]; ["0sv"; "0sv'"; "0sz"; "0t"; "0tp"; "0tsd"; "0x"]]).
Local Ltac oF' pc := oF constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc.
Local Ltac oD' pc := oD constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc.
Local Ltac oE' pc := oE constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc.
Local Ltac oW' pc := oW constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc. Local Ltac lia := L5FastLiaT.plia2.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).
Definition art_pop_events (spb c : Z) (cl : art_cls) : list aev :=
let tot := Z.of_nat (length (cl_free cl)) + art_cls_new c cl in
AMmapFixed (spb + c * 2 ^ 32 + cl_mu cl) 262144
:: (if 4 * tot <=? cl_mfa cl then [] else [AMmapFixed (spb + c * 2 ^ 32 + 3758096384 + cl_mfa cl) (art_cls_mfa' cl tot - cl_mfa cl)]).
Definition art_pop_fp (sp t spb ris qs c km : Z) : list (Z * Z) :=
[ (sp - 512, 512); (ris + 128 * c, 128); (spb + c * 2 ^ 32 + 262144 * km, 262144); (spb + c * 2 ^ 32 + 3758096384, 536870912);
(2147450880 + 8192 * qs + c * 2 ^ 29 + 32768 * km, 32768); (2147450880 + 8192 * qs + c * 2 ^ 29 + 469762048, 67108864);
(t + 2872, 16); (t + 2792, 8) ].
Lemma art_at_ecall_mmap : ltac2:(TCodec.tc2 tcn__JbtClsPop3 ";&I&QD(RLyR0+a]_H(7%43321'RN%115/031%:291").
Proof. exists (ltac:(oW' 0x8b5f8%Z)). split; [exact (ltac:(oF' 0x8b5f8%Z)) | exact (ltac:(oE' 0x8b5f8%Z))]. Qed.
Section SE.
Local Abbreviation SEC_T_art_region_rep_populate := (ltac2:(TCodec.tc2 tcn__JbtClsPop3 "V=';'M'RNyR0%211'5y8%511%311p051'3'6%12<<%311&Kr8%211&QK&2&Q7r7%211%42F1%611&QFr<&QJr:&QL+2+Q0%3221%6251%9281+S`PPPP0%;221+T0r;%<221%?2>1'9r6&O%12B@%43Q<31&QH+1%221K&Nr5%J21Q3%32J1%<3QDQ01zr4%:221&QI%Q128E+R0%O2N1%4231%@28Q9+M%Q32Q21%Q82QA1%9216+4%Q921Q8%G215&Q5rFrErDrCrBrA%76654321&QC%1243&Q=%13576&Q>+@%239QJ1r=+Q8%QN221+8%73?21r>+QH%R3221%;3D15r?+R8%R7221%?3I1>%R72OG%A3LG1&F&QDrH%R>2KDu8%R@2OQ2%6554321rI+H%RD2Q21%:59316Q7rJ%RG2Q6RA&Q6rL%211%RI2>Q=%RL221%B5A76>1rK+Q@%S02Q@1&Q9rM%211+XPP0%S5221%K5J86G1'8r1%RD2R<1%R:22<%4221rN&QM%S>2LE%S=2R51%S@2Q31r2%SB21RL%SA2R91%7241u4&QGrQ0%Q011%SG28Q3%SJ221%521R1%QA5Q@@871p0B1pT:TF1&GrG%24QEO1Q;rQ4rQ2%T221SM%T5231%Q51?%T721Q3%94QLL31rQ5rQ3&Q1rQ1%2231rO%S266=5<21p081p0@1p0D1p0Q=1p0QG1p0R01p0R51p0R=1p0R@1p0RE1p0RJ1p0S01p0S41p0S71p0S:1p0SC1p0SG1p0SL1p0SN1p0T41p0T81p0T>1p0TB1tU6UOTH1tT6V0TM1tU2V1U:1tV6V2UB1pTLV31pU0V41pSNUH1pQ6UM1pQ4UN1pT2V71pTNV91pT0V:1pUBV;1pUHV<1")) (only parsing).
Variable spb : ltac:(sec_ty2 constr:(SEC_T_art_region_rep_populate) 0%nat 0%nat).
Variable ris : ltac:(sec_ty2 constr:(SEC_T_art_region_rep_populate) 1%nat 0%nat).
Variable c : ltac:(sec_ty2 constr:(SEC_T_art_region_rep_populate) 2%nat 0%nat).
Variable mx : ltac:(sec_ty2 constr:(SEC_T_art_region_rep_populate) 3%nat 0%nat).
Variable cl : ltac:(sec_ty2 constr:(SEC_T_art_region_rep_populate) 4%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_region_rep_populate) 5%nat 0%nat).
Variable M' : ltac:(sec_ty2 constr:(SEC_T_art_region_rep_populate) 6%nat 0%nat).
Variable W : ltac:(sec_ty2 constr:(SEC_T_art_region_rep_populate) 7%nat 0%nat).
Variable new : ltac:(sec_ty2 constr:(SEC_T_art_region_rep_populate) 8%nat 0%nat).
Variable mfa' : ltac:(sec_ty2 constr:(SEC_T_art_region_rep_populate) 9%nat 0%nat).
Lemma art_region_rep_populate : ltac:(sec_stmt2 constr:(SEC_T_art_region_rep_populate) 10%nat 0%nat).
Proof.
intros sz nf fa r Enew Hnew Emfa Hr Hr' Hfa Hfa' Hnf RR G A G0 G40 G56 G72 GFA C16 C24 C32 C48 CFA WFA WU.
destruct RR as (Rmx & Rnf & Rmfa & Rau & Ram & Rmu & Rmm & Rna & Rnfr & Rfa & Wr & Wfa & Wu).
fold r in Rmx, Rnf, Rmfa, Rau, Ram, Rmu, Rmm, Rna, Rnfr, Wr. fold fa in Rfa, Wfa.
assert (Hnf0 : 0 <= nf) by (unfold nf; lia).
unfold art_region_rep, art_cls_populate. cbn [cl_free cl_au cl_mu cl_mfa cl_na cl_nfr cl_cache]. fold sz nf fa r. rewrite <- Enew.
assert (Elen : Z.of_nat (length (cl_free cl ++ art_carved (cl_au cl) sz (Z.to_nat new))) = nf + new).
{ rewrite length_app, art_carved_length, Nat2Z.inj_add, Z2Nat.id by lia. reflexivity. }
rewrite Elen, <- Emfa.
split. { apply (art_cell_tr W M M'); [exact A|eapply art_gap_sub; [exact G0|lia|cbn; lia]|lia|cbn; lia|exact Rmx]. }
split; [exact C16|]. split; [exact C24|]. split; [exact C32|].
split. { apply (art_cell_tr W M M'); [exact A|exact G40|lia|cbn; lia|exact Ram]. }
split; [exact C48|].
split. { apply (art_cell_tr W M M'); [exact A|exact G56|lia|cbn; lia|exact Rmm]. }
split. { apply (art_cell_tr W M M'); [exact A|eapply art_gap_sub; [exact G72|lia|cbn; lia]|lia|cbn; lia|exact Rna]. }
split. { apply (art_cell_tr W M M'); [exact A|eapply art_gap_sub; [exact G72|lia|cbn; lia]|lia|cbn; lia|exact Rnfr]. }
split.
{ intros j Hj. rewrite length_app, art_carved_length in Hj.
destruct (Nat.lt_ge_cases j (length (cl_free cl))) as [Lt|Ge].
- rewrite app_nth1 by exact Lt. pose proof (proj1 (Nat2Z.inj_lt _ _) Lt) as Lt'. fold nf in Lt'.
apply (art_cell_tr W M M'); [exact A|eapply art_gap_sub; [exact GFA|lia|cbn; lia]|lia|cbn; lia|exact (Rfa j Lt)].
- rewrite app_nth2 by exact Ge. set (k := (j - length (cl_free cl))%nat).
assert (Hk : (k < Z.to_nat new)%nat) by (unfold k; lia).
rewrite art_carved_nth by exact Hk. rewrite Z2Nat.id by lia.
assert (Ej : Z.of_nat j = nf + Z.of_nat k) by (unfold k, nf; lia).
pose proof (CFA (new - 1 - Z.of_nat k) ltac:(lia)) as C.
replace (fa + 4 * (nf + new) - 4 * (new - 1 - Z.of_nat k + 1)) with (fa + 4 * Z.of_nat j) in C by lia. exact C. }
split; [eapply wr_grows; [exact G|exact Wr]|]. split; [exact WFA|exact WU].
Qed.
End SE.
Section Spec.
Variable EVOK : list aev -> aev -> Prop.
Variable GR : list aev -> (word -> option byte) -> Z -> Z -> Prop.
Context {fx : PropExec.FPState}.
Definition art_pop_fpE (sp t spb ris qs c km mfa : Z) : list (Z * Z) :=
[ (sp - 512, 448); (sp - 64, 64); (spb + c * 2 ^ 32 + 262144 * km, 262144); (spb + c * 2 ^ 32 + 3758096384 + mfa, 536870912 - mfa);
(2147450880 + 8192 * qs + c * 2 ^ 29 + 32768 * km, 32768); (2147450880 + 8192 * qs + c * 2 ^ 29 + 469762048, 67108864);
(t + 2872, 16); (t + 2792, 8); (ris + 128 * c + 24, 8); (ris + 128 * c + 48, 8) ].
Section SE.
Local Abbreviation SEC_T_art_populate_tail := (ltac2:(TCodec.tc2 tcn__JbtClsPop3 "`N'3'H%211'?!p021p041&@y5'RNyR0%211%5241'5y8%611%311p061';'M&Kr6%211&QK&2&Q7r2%211%42:1%611&QFr;&QJr8&QL+2+Q0%3221%6251%9281+S`PPPP0%;221+T0r9%<221%?2>1&LrA%211'8&QH+1%221E+N%42G1%6231&QMrB+`0%3221%:2=1&QIrC+Q?%N2M1%4231'9+RPP0r?%Q5221%43QDG1+`PQoooPP0%F21?+Q5%Q82Q71%Q=2=1%:3QJC1+TP0%Q@2@1rF%N221%O242rG%QE216rH%Q3221&E%QI2=:%244;61rI+QoonlP0%Q32D1%643?21&Q9%11Q?+XPP0rE%R1221%Q03R@41z&Q6%11Q<%QD231%31Q9%;1Q:%QG221rD%>11%R>21=%QK21R5&Q8%11?%QN2=1+4%RB218%51Q4%R2221&OrL%221Q5%QF3S6O1rJ%R82R71%G1Q2rK%RM21Q9%S0231%Q21Q6%S221Q1%R?231%Q519%S521Q4%Q01;%R=221%RD2Q=1&NrM%S;2Q@1%32>1%R93SIE1%N1F%RK215rN+`PPPP0%RN221rQ0%SD2L1%SC2Q21rO%S3221&Q5rQ7rQ6rQ4rQ2rQ>%66543281&QArQ@(RL+:(7%33TJ21%6251&RM%12TKSB%S43TK31rQA%93U0T57%<221rQ<+R0%SD221%92U31%S<3U351rQB+8%B3U91@%E231%?2U9Q5%SB3U921rQC+9%H3U?1F%K231rQ1rQ5%TM221%H2UB1%SK3UB51rQD+B%Q13UH1O%Q4231rQ9%U321TN%U62J1%Q12UK1%T43UK51rQE+C%Q:3V11Q8%Q=231%Q72V1QD%T:3V121rQF+D%Q@3V71Q>%QC231%SD1QI%UD21SC%S?1QK%TL221%QA2V;1%TD3V;61rQG+E%QJ3VA1QH%QM231%QG2VAR3%TJ3VA21%VD1VE&QEr1(1+3%R33VJ1R1%R43VKSBR2+G%R63VM1R4+H%R83VO1R6+I%R:3W11R8+J%R<3W31R:+K%R>3W51R<(4%11B%@3C31%A3D61%B3E91%C3F<1%D3G?1%E3HB1%F3ID1%I3JH1rQJ%RL21VOrQK%RN21W1%UJ3WA31p061pV>Q11&QCrQH%221Q:&Q=&Q:rQ?rQ:%TH11%48R0RBRHS0S93S<1rQI%73219&F&QD%VD2QORLu8&RO%12X5QH%6558431+@%VJ2QK1rQM%SG21S3%72X;1%<5;N491%VO2GQArQN%SL21S2%<2X@1%A5@Q14>1rQL%W52EWIrQO%T221RO%B2XF1%G5F54D1+Q8%W;2Q;1rR0%T821RL%H2XL1%M5LD4J1+Q@%WA2Q?1rR1%T>21RL%N2Y21%Q35Q2E4Q01+QH%WG2C1rR2%TD21RH%Q42Y81%Q95Q8E4Q61%WL2Q1T9rR3+F%TH3Y?1TF%TK231%Q;2Y?1%Q@5Q?F6Q=1%XM2QGC%VO1T7%XO21VN%QD5QCD3QA1%Y12U1RI%QF5QE@1QCSI&G%14QG=TCSErR4%Y42R:XO%Y72Q=1%W91SI%Y921W8%74QM531%XG2W6S:+QPP0%X>2S<1%XK231rR7+QoooPP0+XP0%Y@21QB%YC231+M%YA2Y@1%YD2QL1%YG241%YF2<R3%YI221%YJ21YNu1+WJ%RA5R@>321p0@1pT:Z;1':rR9+RiH%Z32N1r3%RI5RH42RF1+Rj0%Z72Q21%RL5RK71RIZ<+Rg8%Z:2Q51%RO5RN:1RLT:%YI241%YJ281qV4ZJ1%?2ZK1qTJZL1%A2ZM1qTFZN1%C2ZO1%VE2ZHV@%YA3[81V>%VG2BV<%VA2[;Q8%YD3[;21r4%VI3[@Z5VG%VL221%YH3[?1K%TK3TNR4T7%TL3TOU31%TM3U0U>1%TN3U1UE1%TO3U2UO1%U03U3V91%U13U4V@1%U23U5TO1%U33U6U11%U63U7U51r7%W921[<rRA%W;21[>%Z73[N31p061pV>U>1rR>r5%T?221&Q<rR;rR8rR6rR5%574QE3R721RArR?%TD321\1&Q1%126S>%X36QJ87RF1Dr:rR:%[L2R=1%[O2R?1%[N2QOR;%\1221%\02RF?%\3221%\421\8%TI5TH91R:R9p0RH1pT:\C1r<%\92BR7%TN5TM21TKR6%\;2DR5%U05TO41TM\@%\=2FR4%U25U161TOV=%[L231%[M261qV4\M1%RB2\N1qTJ\O1%RD2]01qTF]11%RF2]21rRGrRF&QBvR3rR@%352\K1Q0QC%6251p081p0H1p0Q51p0Q91p0QB1p0QF1p0R81p0R=1p0RA1pQ6]D1pU>]J1'Jv<v=rR=rR<+ZlgH%Y>3^31Y</01^3%H5GQD1QNT2%97V587H651p0;1p0S11p0SF1p0T<1p0TC1p0TF1p0TI1p0TN1p0U61p0U=1p0UD1p0UK1p0V21p0V81p0V?1p0VG1p0W01p0W41p0X71p0X>1p0XI1p0Y01p0Y:1p0YD1p0YK1p0Z41p0Z?1p0ZG1p0ZM1p0[11p0[41p0[:1p0[@1p0[H1p0[K1p0\01p0\51p0\91p0\>1p0\B1p0\G1p0\N1p0]31p0]71p0]<1p0]>1p0]C1p0]H1p0]K1p0^11p0^71p0^=1p0^E1tU6_D^I1tT6_E^N1tU2_F_;1tV6_G_C1pT2_G1pTL_I1pU0_J1pTN_K1pT>_L1pT0_M1pU4_N1pUB_O1pUH`01pV8`11pN`21pUF`31pU:`;1pUD`61pQ8`71pQ4`81pU8`>1pU<`?1pTB`J1pQ:`G1")) (only parsing).
Variable Q : ltac:(sec_ty2 constr:(SEC_T_art_populate_tail) 0%nat 0%nat).
Variable logE : ltac:(sec_ty2 constr:(SEC_T_art_populate_tail) 1%nat 0%nat).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_populate_tail) 2%nat 0%nat).
Variable rE : ltac:(sec_ty2 constr:(SEC_T_art_populate_tail) 3%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_populate_tail) 4%nat 0%nat).
Variable ME : ltac:(sec_ty2 constr:(SEC_T_art_populate_tail) 5%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_populate_tail) 6%nat 0%nat).
Variable raw : ltac:(sec_ty2 constr:(SEC_T_art_populate_tail) 7%nat 0%nat).
Variable sp : ltac:(sec_ty2 constr:(SEC_T_art_populate_tail) 8%nat 0%nat).
Variable HI : ltac:(sec_ty2 constr:(SEC_T_art_populate_tail) 9%nat 0%nat).
Variable t : ltac:(sec_ty2 constr:(SEC_T_art_populate_tail) 10%nat 0%nat).
Variable spb : ltac:(sec_ty2 constr:(SEC_T_art_populate_tail) 11%nat 0%nat).
Variable ris : ltac:(sec_ty2 constr:(SEC_T_art_populate_tail) 12%nat 0%nat).
Variable qs : ltac:(sec_ty2 constr:(SEC_T_art_populate_tail) 13%nat 0%nat).
Variable c : ltac:(sec_ty2 constr:(SEC_T_art_populate_tail) 14%nat 0%nat).
Variable km : ltac:(sec_ty2 constr:(SEC_T_art_populate_tail) 15%nat 0%nat).
Variable mx : ltac:(sec_ty2 constr:(SEC_T_art_populate_tail) 16%nat 0%nat).
Variable new : ltac:(sec_ty2 constr:(SEC_T_art_populate_tail) 17%nat 0%nat).
Variable mfa' : ltac:(sec_ty2 constr:(SEC_T_art_populate_tail) 18%nat 0%nat).
Variable cl : ltac:(sec_ty2 constr:(SEC_T_art_populate_tail) 19%nat 0%nat).
Lemma art_populate_tail : ltac:(sec_stmt2 constr:(SEC_T_art_populate_tail) 20%nat 0%nat).
Proof using Type Q logE regs rE M ME rom raw sp HI t spb ris qs c km mx new mfa' cl.
intros sz nf fa r
Hret Hc HHI Hsp' Espb Hspb Eris Hris Ht Ht' Atk Ats Emu Hau0 Haumu Room1 Hmfa0 Hnf4 Enew Hnew Hcarve Hfb Emfa Hmfa1 Hmfa2 Htot RR
E10 E2 E8 E9 E18 E19 E20 E21 KE GE AE FP1 FP8 FP9 FP18 FP19 FP20 FP21 FP22 Emu' Emfa' WFA WU SH ST K.
destruct (art_class_size_facts c Hc) as (Hsz & _). fold sz in Hsz.
assert (Hnf0 : 0 <= nf) by (unfold nf; lia).
assert (Hr : r = ris + 128 * c) by reflexivity. assert (Hfa : fa = spb + c * 2 ^ 32 + 3758096384) by reflexivity.
pose proof RR as (Rmx & Rnf & Rmfa & Rau & Ram & Rmu & Rmm & Rna & Rnfr & Rfa & Wr & Wfa & Wu).
fold r in Rmx, Rnf, Rmfa, Rau, Ram, Rmu, Rmm, Rna, Rnfr, Wr. fold nf in Rnf.
unfold art_pop_fpE in AE. rewrite <- Hr, <- Hfa in AE.
destruct (art_clspop_D rE ME rom raw sp r (spb + c * 2 ^ 32) sz (cl_au cl) (cl_mu cl + 262144) nf new (cl_mu cl + 262144 - cl_au cl)
(getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22)
E2 E8 E9 E10 E18 E19 E20 E21 ltac:(lia) Hsp' Hret ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold apart; lia)
Hsz ltac:(lia) Hau0 Hnew Hcarve ltac:(lia) Hnf0 ltac:(lia)
ltac:(eapply wr_grows; [exact GE|exact Wr]) ltac:(eapply wr_sub; [exact WFA|lia|lia])
ltac:(ztr) ltac:(ztr) Emu' ltac:(ztr) ltac:(ztr) FP1 FP8 FP9 FP18 FP19 FP20 FP21 FP22)
as (rD & MD & RUND & D10 & D2 & D1 & D8 & D9 & D18 & D19 & D20 & D21 & D22 & KD & GD & AD & Dnf & Dau & Dfa).
fold fa in AD, Dfa.
eapply ar_steps; [exact RUND|]. apply ar_done.
assert (AMD : art_agree (art_pop_fpE sp t spb ris qs c km (cl_mfa cl) ++ [(fa + 4 * nf, 4 * new); (r + 16, 8); (r + 32, 8); (r + 68, 1)]) M MD).
{ unfold art_pop_fpE. rewrite <- Hr, <- Hfa. eapply art_agree_trans; [exact AE|exact AD]. }
apply (K rD MD D10 D2 D1).
- intros x Hx. cbn [In] in Hx.
destruct Hx as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]];
first [ exact D8 | exact D9 | exact D18 | exact D19 | exact D20 | exact D21 | exact D22 | rewrite KD by inl; apply KE; inl ].
- eapply mem_grows_trans; [exact GE|exact GD].
- eapply art_agree_sub; [exact AMD|]. unfold art_pop_fp, art_pop_fpE. rewrite <- Hr, <- Hfa. clear - Hmfa0 Hmfa2 Htot Hnf0 Hnew. zsub.
- apply (art_region_rep_populate spb ris c mx cl M MD _ new mfa' Enew Hnew Emfa ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) RR
ltac:(eapply mem_grows_trans; [exact GE|exact GD]) AMD).
+ unfold art_pop_fpE. fold r fa. clear - Hr Hfa Hc HHI Hsp' Espb Hspb Eris Hris Ht Ht' Atk Ats Emu Room1 Hmfa0 Hnf4 Hnf0 Hnew Htot Hmfa2. unfold apart in Atk, Ats. zgap.
+ unfold art_pop_fpE. fold r fa. clear - Hr Hfa Hc HHI Hsp' Espb Hspb Eris Hris Ht Ht' Atk Ats Emu Room1 Hmfa0 Hnf4 Hnf0 Hnew Htot Hmfa2. unfold apart in Atk, Ats. zgap.
+ unfold art_pop_fpE. fold r fa. clear - Hr Hfa Hc HHI Hsp' Espb Hspb Eris Hris Ht Ht' Atk Ats Emu Room1 Hmfa0 Hnf4 Hnf0 Hnew Htot Hmfa2. unfold apart in Atk, Ats. zgap.
+ unfold art_pop_fpE. fold r fa. clear - Hr Hfa Hc HHI Hsp' Espb Hspb Eris Hris Ht Ht' Atk Ats Emu Room1 Hmfa0 Hnf4 Hnf0 Hnew Htot Hmfa2. unfold apart in Atk, Ats. zgap.
+ unfold art_pop_fpE. fold r fa. clear - Hr Hfa Hc HHI Hsp' Espb Hspb Eris Hris Ht Ht' Atk Ats Emu Room1 Hmfa0 Hnf4 Hnf0 Hnew Htot Hmfa2. unfold apart in Atk, Ats. zgap.
+ exact Dnf.
+ ztr.
+ exact Dau.
+ ztr.
+ exact Dfa.
+ eapply wr_grows; [exact GD|exact WFA].
+ eapply wr_grows; [exact GD|exact WU].
- intros j Hj. pose proof (SH j Hj) as C. ztr.
- destruct ST as (m1' & m2' & sv' & S1 & S2 & S3). exists m1', m2', sv'. unfold apart in Atk. repeat split; ztr.
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_art_populate_aruns := (ltac2:(TCodec.tc2 tcn__JbtClsPop3 "\H'3'H%211'?!p021p041&@y5'RNyR0%211%5241'5y8%611%311p061';'M'9&QArF(RL+1(7%33B21%6251rC%93B21&LrD%211rH+2%<3K1:%?231&RM%12L7%C3L31rI+4%C3Q21A%F231rA%82Q31%J3Q331rJ+:%J3Q91H%M231+QWTnH%?2Q:1%Q13Q:31rK+;%Q13Q@1O%Q4231&QFrE+Rf@%3221%I2QD1%Q;3QD61rL+<%Q;3QJ1Q9%Q>231r>%Q02QK1%QB3QK31rM+=%QB3R11Q@%QE231&QJ+T0r?%3221%E2Q31%Q;2R61%QM3R671rN+>%QM3R<1QK%R0231%R23R;1A'8&QH%12R1Q=+N%32Q?1%5231&QM+`0%22O1%82Q:1&QI&QL+Q?%22R21%42N1&Q3rG%28Q1Q8QBQIR71RBQ=%A2RAR=+8%C2R?1%E231&K%11RH%Q421R@+XPP0%I221&G&QDrQ4rQ1%I21H%54431IrQ5rQ0+TP0%948321&Q4rQ6%23QNR81&Q@rQ7%211&Q?rQ8rOrQ2rQ3%564B>321&Q5rQ9%266QHR:S2R?1&Q0%12R5SF&Q9%11Q7%R42OR8%SL3SN21&FrQ<+RiH%RJ2D1u8%55Q3421S0rQ=+Rj0%RO2F1%95Q7315S4rQ>+Rg8%S32D1%=5Q;319S8%B1S9%S621Q@+S`PPPP0%R:221&N&QK&2&Q7%11S7%32TF1%511&O%12Q5S;%SB231%:2S=1+`PPPP0%RG221rQA+QoooPP0+XP0%S821QK%SJ231+M%RD2TD1%S<2R31%SN241+QPP0%S?21QD%T1231%R:4R9<13rQB%SC2<R1%T52>1%SE2R8:%T7221+^PPPP0%T9221+RPPPP0%RC4RB821&Q2v<rQE&Q;%13R1R=R6%53431r2%UH21TL%U92V4UF%UK3V421r3%UL21U>rQD%U>2V91%V03V931r4%V121ULrQF%V43V=21%V@1VA&QEr1(1+3%V73VF1V5%V83VGSEV6+9%V:3VI1V8+B%V<3VK1V:+C%V>3VM1V<+D%V@3VO1V>+E%VB3W11V@+F%VD3W31VB+G%VF3W51VD+H%VH3W71VF+I%VJ3W91VH+J%VL3W;1VJ+K%VN3W=1VL(4%11N%L3O31%M3Q061%N3Q191%O3Q2<1%Q03Q3?1%Q13Q4B1%Q23Q5E1%Q33Q6H1%Q43Q7K1%Q53Q8N1%Q63Q9Q11%Q73Q:Q41%Q83Q;VJ1%Q93Q<Q71%Q<3Q=Q;1r7%WC21QLrQL%WE21QN%WG3X031p061pU6QD1&QCrQJr5%3221&Q=&Q<rQHrQ@rQ?%473R0S721SLT0rQKr6%83321&Q1%126TI%TE6S0S=7T;1Fz%V721R4%UO2R5S7%V:221r:rQC%VI2SB1%W;2SD1%VK2S9S@%W=221%VM2S?SH%W?221%W@21RNu1+WJ%TL5UJ;321p0=1pT:XM1':r<%WH2Q9TO%U25V021TNS3%WJ2Q;TL%U45V241U0S9%WL2Q=TJ%U65V461U2RL%W1231%W2261qV4Y81%;2Y91qTJY:1%=2Y;1qTFY<1%?2Y=1rR2&0rR1rQ;%SK3SLT71%43Z431&QBvR3r;rQMrQN%55432Q91%<271p0>1p0O1p0QB1p0QF1p0R01p0R51p0SK1p0T01p0T61pQ6Z51pU>Z;1'Jv=rQG+Zl[4%Z53ZB1Z3/01ZB%H5GT71TFT<%77W<TH6HR;51p091p0TF1p0TM1p0U71p0UE1p0V31p0V81p0V=1p0VB1p0VI1p0VN1p0W11p0W51p0W<1p0W@1p0WD1p0WI1p0X01p0X61p0X;1p0X?1p0XE1p0XJ1p0Y11p0Y71p0YC1p0YK1p0Z61p0Z>1p0ZF1p0ZN1p0[21pT2[=1pV2[?1pTH[@1pTD[A1pTN[B1pU@[C1pT>[D1pT0[E1pU4[F1pUB[G1pUH[H1pV<[I1pT<[J1pV:[K1pT4[L1pV8[M1pN[N1pUF[O1pU:\71pUD\21pQ4\31pU<\91pT@\D1pQ:\A1")) (only parsing).
Variable Q : ltac:(sec_ty2 constr:(SEC_T_art_populate_aruns) 0%nat 0%nat).
Variable log : ltac:(sec_ty2 constr:(SEC_T_art_populate_aruns) 1%nat 0%nat).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_populate_aruns) 2%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_populate_aruns) 3%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_populate_aruns) 4%nat 0%nat).
Variable raw : ltac:(sec_ty2 constr:(SEC_T_art_populate_aruns) 5%nat 0%nat).
Variable sp : ltac:(sec_ty2 constr:(SEC_T_art_populate_aruns) 6%nat 0%nat).
Variable HI : ltac:(sec_ty2 constr:(SEC_T_art_populate_aruns) 7%nat 0%nat).
Variable t : ltac:(sec_ty2 constr:(SEC_T_art_populate_aruns) 8%nat 0%nat).
Variable ctx : ltac:(sec_ty2 constr:(SEC_T_art_populate_aruns) 9%nat 0%nat).
Variable tp : ltac:(sec_ty2 constr:(SEC_T_art_populate_aruns) 10%nat 0%nat).
Variable key : ltac:(sec_ty2 constr:(SEC_T_art_populate_aruns) 11%nat 0%nat).
Variable tsd : ltac:(sec_ty2 constr:(SEC_T_art_populate_aruns) 12%nat 0%nat).
Variable spb : ltac:(sec_ty2 constr:(SEC_T_art_populate_aruns) 13%nat 0%nat).
Variable ris : ltac:(sec_ty2 constr:(SEC_T_art_populate_aruns) 14%nat 0%nat).
Variable qs : ltac:(sec_ty2 constr:(SEC_T_art_populate_aruns) 15%nat 0%nat).
Variable c : ltac:(sec_ty2 constr:(SEC_T_art_populate_aruns) 16%nat 0%nat).
Variable km : ltac:(sec_ty2 constr:(SEC_T_art_populate_aruns) 17%nat 0%nat).
Variable req : ltac:(sec_ty2 constr:(SEC_T_art_populate_aruns) 18%nat 0%nat).
Variable mx : ltac:(sec_ty2 constr:(SEC_T_art_populate_aruns) 19%nat 0%nat).
Variable m1 : ltac:(sec_ty2 constr:(SEC_T_art_populate_aruns) 20%nat 0%nat).
Variable m2 : ltac:(sec_ty2 constr:(SEC_T_art_populate_aruns) 21%nat 0%nat).
Variable sv : ltac:(sec_ty2 constr:(SEC_T_art_populate_aruns) 22%nat 0%nat).
Variable cl : ltac:(sec_ty2 constr:(SEC_T_art_populate_aruns) 23%nat 0%nat).
Lemma art_populate_aruns : ltac:(sec_stmt2 constr:(SEC_T_art_populate_aruns) 24%nat 0%nat).
Proof using Type Q log regs M rom raw sp HI t ctx tp key tsd spb ris qs c km req mx m1 m2 sv cl.
intros
H1 Hret H2 H4 H10 H11 H12 H13 H14 Hc HHI Hsp' GEO Hreq Hneed W Wt PC L T RR OK Emu Cm1 Cm2 Csv Room1 Room2 Wsh1 Wsh2 EV K.
destruct GEO as (G1 & G2 & Espb & G4 & Eris & G6 & G7 & G8 & G9 & G10 & G11 & (qt & Et) & G13 & G14 & G15 & G16 & G17 & G18 & G19 & G20 & G21 & G22).
assert (At_i : apart t 4096 0x10000 (0x693000 - 0x10000)) by (unfold apart; clear - G9; lia).
assert (At_s : apart t 4096 0x7fff7000 (0x10007fff8000 - 0x7fff7000)) by (unfold apart; clear - G10; lia).
assert (Ac_i : apart ctx 4096 0x10000 (0x693000 - 0x10000)) by (unfold apart; clear - G15; lia).
assert (Ac_s : apart ctx 4096 0x7fff7000 (0x10007fff8000 - 0x7fff7000)) by (unfold apart; clear - G16; lia).
clear G9 G10 G15 G16.
destruct PC as (Pspb & Pris & Prel & Ppm & Pmask & Ppg1 & Ppg2 & Pdec & Plim).
destruct RR as (Rmx & Rnf & Rmfa & Rau & Ram & Rmu & Rmm & Rna & Rnfr & Rfa & Wr & Wfa & Wu).
destruct OK as (_ & (Hau0 & Haumu) & Hrem0 & _ & _ & Hmu3 & (kf & Emfa) & (Hmfa0 & Hmfa1) & Hnf4 & _ & _).
destruct (art_class_size_facts c Hc) as (Hsz & Hsz16).
set (sz := AsanTab.class_size c) in *. set (nf := Z.of_nat (length (cl_free cl))) in *.
set (au := cl_au cl) in *. set (mu := cl_mu cl) in *. set (mfa := cl_mfa cl) in *.
assert (Hnf0 : 0 <= nf) by (unfold nf; lia).
set (new := art_cls_new c cl). set (rem := (mu + 262144 - au) mod sz).
assert (Enew : mu + 262144 - au = new * sz + rem).
{ unfold new, art_cls_new, rem. fold sz au mu. rewrite Z.mul_comm. apply Z.div_mod. lia. }
assert (Hrem : 0 <= rem < sz) by (unfold rem; apply Z.mod_pos_bound; lia).
assert (Hnew : 1 <= new). { destruct (Z_lt_le_dec new 1) as [Lt|Ge]; [|exact Ge]. exfalso. assert (new * sz <= 0) by nia. lia. }
set (r := ris + 128 * c) in *. set (rb := spb + c * 2 ^ 32) in *.
assert (Hr : 0x693000 <= r /\ r + 128 <= HI) by (unfold r; lia).
assert (Er : r = ris + 128 * c) by reflexivity.
assert (Hkm : 0 <= km) by lia.
set (shb := 2147450880 + 8192 * qs + c * 2 ^ 29 + 32768 * km) in *.
set (addr := rb + mu).
cbn [art_pop_events art_evok_list] in EV. fold nf new mu mfa in EV. destruct EV as [EV1 EV2].
assert (Hneed1 : mu < au + sz * req). { assert (sz * 1 <= sz * req) by (apply Z.mul_le_mono_nonneg_l; lia). lia. }
destruct (art_clspop_A regs M rom raw sp (t + 2768) c r req spb qs au mu km (sz * req) H1 H2 H10 H11 H12 H13 H14
ltac:(lia) Hsp' ltac:(lia) Hc ltac:(lia) ltac:(lia) Hreq ltac:(reflexivity) ltac:(lia) ltac:(lia) Espb Emu Hau0 Haumu Hneed1 Hneed Room1
ltac:(unfold apart; lia) ltac:(eapply wr_sub; [exact W|lia|lia]) Pspb Rau Rmu Rmm Ppm ltac:(exact Prel) Ppg1 Ppg2 ltac:(destruct L as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & X & _); exact X) Pdec)
as (rA & MA & RUNA & ARGS & A1 & A2 & A8 & A21 & A22 & KA & GA & AA & FP1 & FP8 & FP9 & FP18 & FP19 & FP20 & FP21 & FP22 & FM1 & FM8 & FM9 & FM18 & FN0 & FN8 & FN9 & FN18 & FM19 & FM20).
eapply ar_steps; [exact RUNA|].
eapply (ar_mmap_fixed ASEGS EVOK GR Q log rA (0x8b5f8 : word) (0x8b5fc : word) MA rom addr 262144 art_at_ecall_mmap ltac:(apply bv_eq; reflexivity) ARGS EV1).
set (MZ := art_zfill MA addr 262144). set (rZ := regupd rA 10 (Z_to_bv 64 addr)).
assert (AZ : art_agree [(addr, 262144)] MA MZ) by apply art_agree_zfill.
assert (GZ : mem_grows MA MZ) by apply art_zfill_grows.
assert (AMZ : art_agree [(sp - 464, 464); (addr, 262144)] M MZ). { eapply art_agree_sub; [eapply art_agree_trans; [exact AA|exact AZ]|]. zsub. }
assert (GMZ : mem_grows M MZ) by (eapply mem_grows_trans; eassumption).
pose proof (art_cell_norm _ _ _ _ Cm1) as Cm1n. pose proof (art_cell_norm _ _ _ _ Cm2) as Cm2n. pose proof (art_cell_norm _ _ _ _ Csv) as Csvn.
pose proof (art_mod64_range m1) as Hm1n. pose proof (art_mod64_range m2) as Hm2n. pose proof (art_mod64_range sv) as Hsvn.
set (m1n := m1 mod 2 ^ 64) in *. set (m2n := m2 mod 2 ^ 64) in *. set (svn := sv mod 2 ^ 64) in *.
assert (Ccf : cellA M 0x134390 8 0x1ce568) by (destruct L as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & X & _); exact X).
assert (Hshb : shb = 2147450880 + 8192 * qs + c * 2 ^ 29 + 32768 * km) by reflexivity.
assert (Haddr : addr = spb + c * 2 ^ 32 + mu) by reflexivity.
assert (Hrb : rb = spb + c * 2 ^ 32) by reflexivity.
assert (LZ : art_layout MZ). { eapply art_layout_fp; [exact AMZ| |exact L]. intros z Hz. cbn. repeat split; lia. }
assert (TZ : art_tsd MZ tp key tsd ctx t).
{ eapply art_tsd_fp; [exact AMZ| | |exact G19|exact G20|exact G21|exact G22|exact T].
- intros z Hz. cbn. repeat split; lia.
- intros z Hz. cbn. pose proof G17 as X. unfold apart in X. repeat split; lia. }
assert (Ash_t : apart shb 32768 t 4096) by (pose proof At_s as X; unfold apart in X |- *; lia).
assert (Ash_c : apart shb 32768 ctx 4096) by (pose proof Ac_s as X; unfold apart in X |- *; lia).
assert (At_r : apart t 4096 r 128) by (pose proof G11 as X; unfold apart in X |- *; unfold r; lia).
assert (At_a : apart t 4096 addr 262144) by (pose proof G11 as X; unfold apart in X |- *; lia).
destruct (art_clspop_B rZ MZ rom sp tp key tsd ctx t r c spb qs au mu km nf sz new rem m1n m2n svn addr shb Haddr Hshb
ltac:(unfold rZ; gres; exact A1) ltac:(unfold rZ; gres; exact A2) ltac:(unfold rZ; gres; rewrite KA by inl; exact H4) ltac:(unfold rZ; gres; exact A8)
ltac:(unfold rZ; gres; f_equal; lia) ltac:(unfold rZ; gres; exact A21) ltac:(unfold rZ; gres; exact A22)
ltac:(lia) Hsp' Hc Espb Emu Hkm ltac:(unfold kHighMemBeg; lia) ltac:(lia) Room1 Hsz Hau0 Haumu Enew Hrem ltac:(lia) ltac:(lia) Hm1n Hm2n Hsvn
ltac:(lia) ltac:(lia) ltac:(rewrite Et; replace (4096 * qt + 2792) with ((512 * qt + 349) * 8) by lia; apply Z_mod_mult) ltac:(lia) ltac:(lia) At_r
G19 G20 G21 G22 ltac:(lia) ltac:(lia) Ash_t ltac:(unfold apart; lia) Ash_c ltac:(lia)
ltac:(eapply wr_grows; [exact GMZ|]; eapply wr_sub; [exact W|lia|lia]) ltac:(eapply wr_grows; [exact GMZ|exact Wsh1])
ltac:(eapply wr_grows; [exact GMZ|]; eapply wr_sub; [exact Wt|lia|lia]) ltac:(eapply wr_grows; [exact GMZ|]; eapply wr_sub; [exact Wt|lia|lia])
ltac:(eapply wr_grows; [exact GMZ|exact Wr]) LZ TZ
ltac:(ztr_c ltac:(clear - Hc HHI Hsp' G1 G2 Espb G4 Eris G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 At_i At_s Ac_i Ac_s Emu Hmu3 Emfa Hmfa0 Hmfa1 Hnf4 Room1 Hnf0 Hr Er Hkm Hshb Haddr Hrb Ash_t Ash_c At_r At_a)) ltac:(ztr_c ltac:(clear - Hc HHI Hsp' G1 G2 Espb G4 Eris G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 At_i At_s Ac_i Ac_s Emu Hmu3 Emfa Hmfa0 Hmfa1 Hnf4 Room1 Hnf0 Hr Er Hkm Hshb Haddr Hrb Ash_t Ash_c At_r At_a)) ltac:(ztr_c ltac:(clear - Hc HHI Hsp' G1 G2 Espb G4 Eris G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 At_i At_s Ac_i Ac_s Emu Hmu3 Emfa Hmfa0 Hmfa1 Hnf4 Room1 Hnf0 Hr Er Hkm Hshb Haddr Hrb Ash_t Ash_c At_r At_a)) ltac:(ztr_c ltac:(clear - Hc HHI Hsp' G1 G2 Espb G4 Eris G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 At_i At_s Ac_i Ac_s Emu Hmu3 Emfa Hmfa0 Hmfa1 Hnf4 Room1 Hnf0 Hr Er Hkm Hshb Haddr Hrb Ash_t Ash_c At_r At_a)) ltac:(ztr_c ltac:(clear - Hc HHI Hsp' G1 G2 Espb G4 Eris G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 At_i At_s Ac_i Ac_s Emu Hmu3 Emfa Hmfa0 Hmfa1 Hnf4 Room1 Hnf0 Hr Er Hkm Hshb Haddr Hrb Ash_t Ash_c At_r At_a)) ltac:(ztr_c ltac:(clear - Hc HHI Hsp' G1 G2 Espb G4 Eris G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 At_i At_s Ac_i Ac_s Emu Hmu3 Emfa Hmfa0 Hmfa1 Hnf4 Room1 Hnf0 Hr Er Hkm Hshb Haddr Hrb Ash_t Ash_c At_r At_a)) ltac:(rewrite Haddr; ztr_c ltac:(clear - Hc HHI Hsp' G1 G2 Espb G4 Eris G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 At_i At_s Ac_i Ac_s Emu Hmu3 Emfa Hmfa0 Hmfa1 Hnf4 Room1 Hnf0 Hr Er Hkm Hshb Haddr Hrb Ash_t Ash_c At_r At_a)) ltac:(ztr_c ltac:(clear - Hc HHI Hsp' G1 G2 Espb G4 Eris G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 At_i At_s Ac_i Ac_s Emu Hmu3 Emfa Hmfa0 Hmfa1 Hnf4 Room1 Hnf0 Hr Er Hkm Hshb Haddr Hrb Ash_t Ash_c At_r At_a)) ltac:(ztr_c ltac:(clear - Hc HHI Hsp' G1 G2 Espb G4 Eris G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 At_i At_s Ac_i Ac_s Emu Hmu3 Emfa Hmfa0 Hmfa1 Hnf4 Room1 Hnf0 Hr Er Hkm Hshb Haddr Hrb Ash_t Ash_c At_r At_a)) ltac:(rewrite Haddr; ztr_c ltac:(clear - Hc HHI Hsp' G1 G2 Espb G4 Eris G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 At_i At_s Ac_i Ac_s Emu Hmu3 Emfa Hmfa0 Hmfa1 Hnf4 Room1 Hnf0 Hr Er Hkm Hshb Haddr Hrb Ash_t Ash_c At_r At_a))
ltac:(ztr_c ltac:(clear - Hc HHI Hsp' G1 G2 Espb G4 Eris G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 At_i At_s Ac_i Ac_s Emu Hmu3 Emfa Hmfa0 Hmfa1 Hnf4 Room1 Hnf0 Hr Er Hkm Hshb Haddr Hrb Ash_t Ash_c At_r At_a)) ltac:(ztr_c ltac:(clear - Hc HHI Hsp' G1 G2 Espb G4 Eris G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 At_i At_s Ac_i Ac_s Emu Hmu3 Emfa Hmfa0 Hmfa1 Hnf4 Room1 Hnf0 Hr Er Hkm Hshb Haddr Hrb Ash_t Ash_c At_r At_a)) ltac:(ztr_c ltac:(clear - Hc HHI Hsp' G1 G2 Espb G4 Eris G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 At_i At_s Ac_i Ac_s Emu Hmu3 Emfa Hmfa0 Hmfa1 Hnf4 Room1 Hnf0 Hr Er Hkm Hshb Haddr Hrb Ash_t Ash_c At_r At_a)) ltac:(ztr_c ltac:(clear - Hc HHI Hsp' G1 G2 Espb G4 Eris G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 At_i At_s Ac_i Ac_s Emu Hmu3 Emfa Hmfa0 Hmfa1 Hnf4 Room1 Hnf0 Hr Er Hkm Hshb Haddr Hrb Ash_t Ash_c At_r At_a)) ltac:(ztr_c ltac:(clear - Hc HHI Hsp' G1 G2 Espb G4 Eris G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 At_i At_s Ac_i Ac_s Emu Hmu3 Emfa Hmfa0 Hmfa1 Hnf4 Room1 Hnf0 Hr Er Hkm Hshb Haddr Hrb Ash_t Ash_c At_r At_a)) ltac:(ztr_c ltac:(clear - Hc HHI Hsp' G1 G2 Espb G4 Eris G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 At_i At_s Ac_i Ac_s Emu Hmu3 Emfa Hmfa0 Hmfa1 Hnf4 Room1 Hnf0 Hr Er Hkm Hshb Haddr Hrb Ash_t Ash_c At_r At_a)) ltac:(ztr_c ltac:(clear - Hc HHI Hsp' G1 G2 Espb G4 Eris G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 At_i At_s Ac_i Ac_s Emu Hmu3 Emfa Hmfa0 Hmfa1 Hnf4 Room1 Hnf0 Hr Er Hkm Hshb Haddr Hrb Ash_t Ash_c At_r At_a)) ltac:(ztr_c ltac:(clear - Hc HHI Hsp' G1 G2 Espb G4 Eris G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 At_i At_s Ac_i Ac_s Emu Hmu3 Emfa Hmfa0 Hmfa1 Hnf4 Room1 Hnf0 Hr Er Hkm Hshb Haddr Hrb Ash_t Ash_c At_r At_a)))
as (rB & MB & RUNB & B1 & B2 & B4 & B8 & B9 & B10 & B11 & B12 & B13 & B18 & B19 & B20 & B21 & B22 & KB & GB & AB & SH & Sm1 & Sm2 & Ssv & Smu).
eapply ar_steps; [exact RUNB|].
set (fa := spb + c * 2 ^ 32 + 3758096384) in *.
assert (Hfa : fa = spb + c * 2 ^ 32 + 3758096384) by reflexivity.
assert (WUZ : wrA MZ rb (mu + 262144)).
{ apply wr_join; [lia|lia|lia|lia|eapply wr_grows; [exact GMZ|exact Wu]|]. replace (rb + mu) with addr by lia. unfold MZ. apply wr_zfill; lia. }
assert (AMB : art_agree [(sp - 464, 464); (addr, 262144); (shb, 32768); (t + 2872, 16); (t + 2792, 8); (r + 48, 8)] M MB).
{ eapply art_agree_sub; [eapply art_agree_trans; [exact AMZ|exact AB]|]. zsub_c ltac:(clear - Hc HHI Hsp' G1 G2 Espb G4 Eris G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 At_i At_s Ac_i Ac_s Emu Hmu3 Emfa Hmfa0 Hmfa1 Hnf4 Room1 Hnf0 Hr Er Hkm Hshb Haddr Hrb Ash_t Ash_c At_r At_a). }
assert (GMB : mem_grows M MB) by (eapply mem_grows_trans; eassumption).
assert (Ash_r : apart shb 32768 r 128) by (unfold apart, r; lia).
assert (Hcarve : au + new * sz <= mu + 262144) by lia.
assert (Hfb : sz <= mu + 262144 - au) by lia.
assert (KBR : forall x : reg, In x [3; 4; 23; 24; 25; 26; 27]%bv -> getr rB x = getr regs x).
{ intros x Hx. cbn [In] in Hx. destruct Hx as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]];
first [ rewrite B4; symmetry; exact H4 | rewrite KB by inl; unfold rZ; gres; apply KA; inl ]. }
destruct (Z_le_gt_dec (4 * (nf + new)) mfa) as [Hwarm|Hmap].
-
assert (Eleb : (4 * (nf + new) <=? mfa) = true) by (apply Z.leb_le; exact Hwarm).
assert (Emfa' : mfa = art_cls_mfa' cl (nf + new)) by (unfold art_cls_mfa'; fold mfa; rewrite Eleb; reflexivity).
assert (Eev : art_pop_events spb c cl = [AMmapFixed addr 262144]).
{ unfold art_pop_events. fold nf new mfa mu. rewrite Eleb. unfold addr, rb. reflexivity. }
destruct (art_clspop_Cw rB MB rom sp r (nf + new) mfa B1 B2 B11 B13 ltac:(lia) Hsp' ltac:(lia) ltac:(lia) ltac:(lia) Hwarm ltac:(lia)
ltac:(eapply wr_grows; [exact GMB|]; eapply wr_sub; [exact W|lia|lia]) ltac:(ztr_c ltac:(clear - Hc HHI Hsp' G1 G2 Espb G4 Eris G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 At_i At_s Ac_i Ac_s Emu Hmu3 Emfa Hmfa0 Hmfa1 Hnf4 Room1 Hnf0 Hr Er Hkm Hshb Haddr Hrb Ash_t Ash_c At_r At_a Hfa Ash_r Hnew)))
as (rC & MC & RUNC & C10 & C2 & KC & GC & AC).
eapply ar_steps; [exact RUNC|]. rewrite Eev in K.
apply (art_populate_tail Q (log ++ [AMmapFixed addr 262144]) regs rC M MC rom raw sp HI t spb ris qs c km mx new mfa cl
Hret Hc HHI Hsp' Espb G4 Eris G6 G7 G8 G11 At_s Emu Hau0 Haumu Room1 Hmfa0 Hnf4 eq_refl Hnew Hcarve Hfb Emfa' ltac:(lia) Hmfa1 Hwarm
ltac:(unfold art_region_rep; fold r fa nf; repeat split; assumption)
C10 C2 ltac:(rewrite KC by inl; exact B8) ltac:(rewrite KC by inl; exact B9) ltac:(rewrite KC by inl; exact B18)
ltac:(rewrite KC by inl; exact B19) ltac:(rewrite KC by inl; exact B20) ltac:(rewrite KC by inl; exact B21)).
+ intros x Hx. cbn [In] in Hx. destruct Hx as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]; (rewrite KC by inl; apply KBR; inl).
+ eapply mem_grows_trans; [exact GMB|exact GC].
+ eapply art_agree_sub; [eapply art_agree_trans; [exact AMB|exact AC]|]. unfold art_pop_fpE. fold r fa. clear - Haddr Hshb Emu Hmfa0 Hmfa1. zsub.
+ ztr_c ltac:(clear - Hc HHI Hsp' G1 G2 Espb G4 Eris G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 At_i At_s Ac_i Ac_s Emu Hmu3 Emfa Hmfa0 Hmfa1 Hnf4 Room1 Hnf0 Hr Er Hkm Hshb Haddr Hrb Ash_t Ash_c At_r At_a Hfa Ash_r Hnew).
+ ztr_c ltac:(clear - Hc HHI Hsp' G1 G2 Espb G4 Eris G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 At_i At_s Ac_i Ac_s Emu Hmu3 Emfa Hmfa0 Hmfa1 Hnf4 Room1 Hnf0 Hr Er Hkm Hshb Haddr Hrb Ash_t Ash_c At_r At_a Hfa Ash_r Hnew).
+ ztr_c ltac:(clear - Hc HHI Hsp' G1 G2 Espb G4 Eris G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 At_i At_s Ac_i Ac_s Emu Hmu3 Emfa Hmfa0 Hmfa1 Hnf4 Room1 Hnf0 Hr Er Hkm Hshb Haddr Hrb Ash_t Ash_c At_r At_a Hfa Ash_r Hnew).
+ ztr_c ltac:(clear - Hc HHI Hsp' G1 G2 Espb G4 Eris G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 At_i At_s Ac_i Ac_s Emu Hmu3 Emfa Hmfa0 Hmfa1 Hnf4 Room1 Hnf0 Hr Er Hkm Hshb Haddr Hrb Ash_t Ash_c At_r At_a Hfa Ash_r Hnew).
+ ztr_c ltac:(clear - Hc HHI Hsp' G1 G2 Espb G4 Eris G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 At_i At_s Ac_i Ac_s Emu Hmu3 Emfa Hmfa0 Hmfa1 Hnf4 Room1 Hnf0 Hr Er Hkm Hshb Haddr Hrb Ash_t Ash_c At_r At_a Hfa Ash_r Hnew).
+ ztr_c ltac:(clear - Hc HHI Hsp' G1 G2 Espb G4 Eris G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 At_i At_s Ac_i Ac_s Emu Hmu3 Emfa Hmfa0 Hmfa1 Hnf4 Room1 Hnf0 Hr Er Hkm Hshb Haddr Hrb Ash_t Ash_c At_r At_a Hfa Ash_r Hnew).
+ ztr_c ltac:(clear - Hc HHI Hsp' G1 G2 Espb G4 Eris G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 At_i At_s Ac_i Ac_s Emu Hmu3 Emfa Hmfa0 Hmfa1 Hnf4 Room1 Hnf0 Hr Er Hkm Hshb Haddr Hrb Ash_t Ash_c At_r At_a Hfa Ash_r Hnew).
+ ztr_c ltac:(clear - Hc HHI Hsp' G1 G2 Espb G4 Eris G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 At_i At_s Ac_i Ac_s Emu Hmu3 Emfa Hmfa0 Hmfa1 Hnf4 Room1 Hnf0 Hr Er Hkm Hshb Haddr Hrb Ash_t Ash_c At_r At_a Hfa Ash_r Hnew).
+ fold r mu. ztr_c ltac:(clear - Hc HHI Hsp' G1 G2 Espb G4 Eris G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 At_i At_s Ac_i Ac_s Emu Hmu3 Emfa Hmfa0 Hmfa1 Hnf4 Room1 Hnf0 Hr Er Hkm Hshb Haddr Hrb Ash_t Ash_c At_r At_a Hfa Ash_r Hnew).
+ fold r. ztr_c ltac:(clear - Hc HHI Hsp' G1 G2 Espb G4 Eris G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 At_i At_s Ac_i Ac_s Emu Hmu3 Emfa Hmfa0 Hmfa1 Hnf4 Room1 Hnf0 Hr Er Hkm Hshb Haddr Hrb Ash_t Ash_c At_r At_a Hfa Ash_r Hnew).
+ fold fa. eapply wr_grows; [eapply mem_grows_trans; [exact GMB|exact GC]|exact Wfa].
+ fold rb mu. eapply wr_grows; [eapply mem_grows_trans; [exact GB|exact GC]|exact WUZ].
+ intros j Hj. pose proof (SH j Hj) as C. rewrite Hshb in C. ztr_c ltac:(clear - Hj Hc HHI Hsp' G1 G2 Espb G4 Eris G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 At_i At_s Ac_i Ac_s Emu Hmu3 Emfa Hmfa0 Hmfa1 Hnf4 Room1 Hnf0 Hr Er Hkm Hshb Haddr Hrb Ash_t Ash_c At_r At_a Hfa Ash_r Hnew).
+ exists (m1n + 1), (m2n + 262144), (svn + 262144). repeat split; ztr_c ltac:(clear - Hc HHI Hsp' G1 G2 Espb G4 Eris G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 At_i At_s Ac_i Ac_s Emu Hmu3 Emfa Hmfa0 Hmfa1 Hnf4 Room1 Hnf0 Hr Er Hkm Hshb Haddr Hrb Ash_t Ash_c At_r At_a Hfa Ash_r Hnew).
+ exact K.
-
assert (Eleb : (4 * (nf + new) <=? mfa) = false) by (apply Z.leb_gt; lia).
set (q := (4 * (nf + new) + 262143) / 262144). set (rr := (4 * (nf + new) + 262143) mod 262144).
assert (Eq : 4 * (nf + new) + 262143 = 262144 * q + rr) by (unfold q, rr; apply Z.div_mod; lia).
assert (Hrr : 0 <= rr < 262144) by (unfold rr; apply Z.mod_pos_bound; lia).
assert (Emfa' : 262144 * q = art_cls_mfa' cl (nf + new)) by (unfold art_cls_mfa'; fold mfa; rewrite Eleb; fold q; lia).
assert (Hq : 262144 * q <= 536870912) by (rewrite Emfa'; exact Room2).
clearbody q rr.
set (addr2 := fa + mfa). set (len2 := 262144 * q - mfa). set (shb2 := 2147450880 + 8192 * qs + c * 2 ^ 29 + 469762048 + 32768 * kf).
assert (Haddr2 : addr2 = spb + c * 2 ^ 32 + 3758096384 + mfa) by reflexivity.
assert (Hlen2 : len2 = 262144 * q - mfa) by reflexivity.
assert (Hshb2 : shb2 = 2147450880 + 8192 * qs + c * 2 ^ 29 + 469762048 + 32768 * kf) by reflexivity.
rewrite Eleb in EV2. cbn [art_evok_list] in EV2. destruct EV2 as [EV2 _]. rewrite <- Emfa' in EV2. fold fa addr2 len2 in EV2.
assert (Eev : art_pop_events spb c cl = [AMmapFixed addr 262144; AMmapFixed addr2 len2]).
{ unfold art_pop_events. fold nf new mfa mu. rewrite Eleb, <- Emfa'. unfold addr, rb, addr2, len2, fa. reflexivity. }
assert (Hkf : 0 <= kf) by lia. assert (Hq1 : kf + 1 <= q) by lia.
destruct (art_clspop_Cm1 rB MB rom sp r c spb qs (nf + new) mfa kf q rr addr2 Haddr2 B1 B2 B10 B11 B12 B13
ltac:(lia) Hsp' Hc ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Espb ltac:(lia) ltac:(lia) Emfa Eq Hrr Hq
ltac:(eapply wr_grows; [exact GMB|]; eapply wr_sub; [exact W|lia|lia])
ltac:(ztr_c ltac:(clear - Hc HHI Hsp' G1 G2 Espb G4 Eris G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 At_i At_s Ac_i Ac_s Emu Hmu3 Emfa Hmfa0 Hmfa1 Hnf4 Room1 Hnf0 Hr Er Hkm Hshb Haddr Hrb Ash_t Ash_c At_r At_a Hfa Ash_r Hnew)) ltac:(ztr_c ltac:(clear - Hc HHI Hsp' G1 G2 Espb G4 Eris G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 At_i At_s Ac_i Ac_s Emu Hmu3 Emfa Hmfa0 Hmfa1 Hnf4 Room1 Hnf0 Hr Er Hkm Hshb Haddr Hrb Ash_t Ash_c At_r At_a Hfa Ash_r Hnew)) ltac:(ztr_c ltac:(clear - Hc HHI Hsp' G1 G2 Espb G4 Eris G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 At_i At_s Ac_i Ac_s Emu Hmu3 Emfa Hmfa0 Hmfa1 Hnf4 Room1 Hnf0 Hr Er Hkm Hshb Haddr Hrb Ash_t Ash_c At_r At_a Hfa Ash_r Hnew)) ltac:(ztr_c ltac:(clear - Hc HHI Hsp' G1 G2 Espb G4 Eris G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 At_i At_s Ac_i Ac_s Emu Hmu3 Emfa Hmfa0 Hmfa1 Hnf4 Room1 Hnf0 Hr Er Hkm Hshb Haddr Hrb Ash_t Ash_c At_r At_a Hfa Ash_r Hnew)) ltac:(ztr_c ltac:(clear - Hc HHI Hsp' G1 G2 Espb G4 Eris G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 At_i At_s Ac_i Ac_s Emu Hmu3 Emfa Hmfa0 Hmfa1 Hnf4 Room1 Hnf0 Hr Er Hkm Hshb Haddr Hrb Ash_t Ash_c At_r At_a Hfa Ash_r Hnew)) ltac:(ztr_c ltac:(clear - Hc HHI Hsp' G1 G2 Espb G4 Eris G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 At_i At_s Ac_i Ac_s Emu Hmu3 Emfa Hmfa0 Hmfa1 Hnf4 Room1 Hnf0 Hr Er Hkm Hshb Haddr Hrb Ash_t Ash_c At_r At_a Hfa Ash_r Hnew)))
as (r1 & M1 & RUN1 & ARGS2 & C1_1 & C1_2 & C1_8 & K1 & G1m & A1m & E1c & E8c & E9c & E18c & E19c & F1c & F8c & F9c & F18c & F0c & K8c & K9c & K18c & F19c & F20c).
fold len2 in F18c, K8c, K18c, C1_8, ARGS2.
eapply ar_steps; [exact RUN1|].
eapply (ar_mmap_fixed ASEGS EVOK GR Q (log ++ [AMmapFixed addr 262144]) r1 (0x8b5f8 : word) (0x8b5fc : word) M1 rom addr2 len2 art_at_ecall_mmap ltac:(apply bv_eq; reflexivity) ARGS2 EV2).
set (MZ2 := art_zfill M1 addr2 len2). set (rZ2 := regupd r1 10 (Z_to_bv 64 addr2)).
assert (AZ2 : art_agree [(addr2, len2)] M1 MZ2) by apply art_agree_zfill.
assert (GZ2 : mem_grows M1 MZ2) by apply art_zfill_grows.
assert (AM2 : art_agree [(sp - 512, 512); (addr, 262144); (shb, 32768); (t + 2872, 16); (t + 2792, 8); (r + 48, 8); (addr2, len2)] M MZ2).
{ eapply art_agree_sub; [eapply art_agree_trans; [eapply art_agree_trans; [exact AMB|exact A1m]|exact AZ2]|]. zsub_c ltac:(clear - Hc HHI Hsp' G1 G2 Espb G4 Eris G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 At_i At_s Ac_i Ac_s Emu Hmu3 Emfa Hmfa0 Hmfa1 Hnf4 Room1 Hnf0 Hr Er Hkm Hshb Haddr Hrb Ash_t Ash_c At_r At_a Hfa Ash_r Hnew Hq Hq1 Hkf Haddr2 Hlen2 Hshb2). }
assert (GM2 : mem_grows M MZ2) by (eapply mem_grows_trans; [eapply mem_grows_trans; [exact GMB|exact G1m]|exact GZ2]).
assert (LZ2 : art_layout MZ2).
{ eapply art_layout_fp; [exact AM2| |exact L]. intros z Hz. pose proof At_i as X. unfold apart in X. cbn. clear - Hz X HHI G1 G4 Eris G6 Hc Haddr Hshb Haddr2 Espb Emu Hr Hkm Hmfa0. repeat split; lia. }
assert (TZ2 : art_tsd MZ2 tp key tsd ctx t).
{ eapply art_tsd_fp; [exact AM2| | |exact G19|exact G20|exact G21|exact G22|exact T].
- intros z Hz. pose proof At_i as X. unfold apart in X. cbn. clear - Hz X HHI G1 G4 Eris G6 Hc Haddr Hshb Haddr2 Espb Emu Hr Hkm Hmfa0. repeat split; lia.
- intros z Hz. pose proof G17 as X1. pose proof G18 as X2. pose proof Ac_s as X3. unfold apart in X1, X2, X3. cbn.
clear - Hz X1 X2 X3 HHI G1 G2 G4 Eris G6 G13 G14 Hc Haddr Hshb Haddr2 Espb Emu Hr Er Hkm Room1 Hmfa0 Hq Hlen2 Hfa. repeat split; lia. }
pose proof (art_cell_norm _ _ _ _ Sm1) as Sm1n. pose proof (art_cell_norm _ _ _ _ Sm2) as Sm2n.
pose proof (art_mod64_range (m1n + 1)) as Hm1n'. pose proof (art_mod64_range (m2n + 262144)) as Hm2n'.
set (m1n' := (m1n + 1) mod 2 ^ 64) in *. set (m2n' := (m2n + 262144) mod 2 ^ 64) in *.
assert (Ash2_t : apart shb2 (32768 * (q - kf)) t 4096) by (pose proof At_s as X; unfold apart in X |- *; clear - X Hshb2 Espb G4 Eris G6 G1 G2 HHI Hc Hkf Hq1 Hq; lia).
assert (Ash2_c : apart shb2 (32768 * (q - kf)) ctx 4096) by (pose proof Ac_s as X; unfold apart in X |- *; clear - X Hshb2 Espb G4 Eris G6 G1 G2 HHI Hc Hkf Hq1 Hq; lia).
assert (Ash2_r : apart shb2 (32768 * (q - kf)) r 128) by (unfold apart, r; clear - Hshb2 Espb G4 Eris G6 G1 G2 HHI Hc Hkf Hq1 Hq; lia).
assert (Wsh2' : wrA MZ2 shb2 (32768 * (q - kf))). { eapply wr_grows; [exact GM2|]. eapply wr_sub; [exact Wsh2|lia|lia]. }
destruct (art_clspop_Cm2 rZ2 MZ2 rom sp tp key tsd ctx t r c spb qs mfa kf q m1n' m2n' addr2 len2 shb2 (getr rB 8) (getr rB 9) (getr rB 18) (getr rB 19) (getr rB 20)
Haddr2 Hlen2 Hshb2
ltac:(unfold rZ2; gres; exact C1_1) ltac:(unfold rZ2; gres; exact C1_2) ltac:(unfold rZ2; gres; rewrite K1 by inl; exact B4)
ltac:(unfold rZ2; gres; exact C1_8) ltac:(unfold rZ2; gres; reflexivity)
ltac:(lia) Hsp' Hc Espb Emfa Hkf Hq1 Hq ltac:(unfold kHighMemBeg; lia) ltac:(lia) Hm1n' Hm2n'
ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) At_r G19 G20 G21 G22 ltac:(lia) ltac:(lia) Ash2_t Ash2_r Ash2_c ltac:(lia)
ltac:(eapply wr_grows; [exact GM2|]; eapply wr_sub; [exact W|lia|lia]) Wsh2'
ltac:(eapply wr_grows; [exact GM2|]; eapply wr_sub; [exact Wt|lia|lia]) ltac:(eapply wr_grows; [exact GM2|exact Wr]) LZ2 TZ2
ltac:(ztr_c ltac:(clear - Hc HHI Hsp' G1 G2 Espb G4 Eris G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 At_i At_s Ac_i Ac_s Emu Hmu3 Emfa Hmfa0 Hmfa1 Hnf4 Room1 Hnf0 Hr Er Hkm Hshb Haddr Hrb Ash_t Ash_c At_r At_a Hfa Ash_r Hnew Hq Hq1 Hkf Haddr2 Hlen2 Hshb2 Ash2_t Ash2_c Ash2_r)) ltac:(ztr_c ltac:(clear - Hc HHI Hsp' G1 G2 Espb G4 Eris G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 At_i At_s Ac_i Ac_s Emu Hmu3 Emfa Hmfa0 Hmfa1 Hnf4 Room1 Hnf0 Hr Er Hkm Hshb Haddr Hrb Ash_t Ash_c At_r At_a Hfa Ash_r Hnew Hq Hq1 Hkf Haddr2 Hlen2 Hshb2 Ash2_t Ash2_c Ash2_r)) ltac:(ztr_c ltac:(clear - Hc HHI Hsp' G1 G2 Espb G4 Eris G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 At_i At_s Ac_i Ac_s Emu Hmu3 Emfa Hmfa0 Hmfa1 Hnf4 Room1 Hnf0 Hr Er Hkm Hshb Haddr Hrb Ash_t Ash_c At_r At_a Hfa Ash_r Hnew Hq Hq1 Hkf Haddr2 Hlen2 Hshb2 Ash2_t Ash2_c Ash2_r)) ltac:(ztr_c ltac:(clear - Hc HHI Hsp' G1 G2 Espb G4 Eris G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 At_i At_s Ac_i Ac_s Emu Hmu3 Emfa Hmfa0 Hmfa1 Hnf4 Room1 Hnf0 Hr Er Hkm Hshb Haddr Hrb Ash_t Ash_c At_r At_a Hfa Ash_r Hnew Hq Hq1 Hkf Haddr2 Hlen2 Hshb2 Ash2_t Ash2_c Ash2_r)) ltac:(ztr_c ltac:(clear - Hc HHI Hsp' G1 G2 Espb G4 Eris G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 At_i At_s Ac_i Ac_s Emu Hmu3 Emfa Hmfa0 Hmfa1 Hnf4 Room1 Hnf0 Hr Er Hkm Hshb Haddr Hrb Ash_t Ash_c At_r At_a Hfa Ash_r Hnew Hq Hq1 Hkf Haddr2 Hlen2 Hshb2 Ash2_t Ash2_c Ash2_r))
ltac:(ztr_c ltac:(clear - Hc HHI Hsp' G1 G2 Espb G4 Eris G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 At_i At_s Ac_i Ac_s Emu Hmu3 Emfa Hmfa0 Hmfa1 Hnf4 Room1 Hnf0 Hr Er Hkm Hshb Haddr Hrb Ash_t Ash_c At_r At_a Hfa Ash_r Hnew Hq Hq1 Hkf Haddr2 Hlen2 Hshb2 Ash2_t Ash2_c Ash2_r)) ltac:(ztr_c ltac:(clear - Hc HHI Hsp' G1 G2 Espb G4 Eris G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 At_i At_s Ac_i Ac_s Emu Hmu3 Emfa Hmfa0 Hmfa1 Hnf4 Room1 Hnf0 Hr Er Hkm Hshb Haddr Hrb Ash_t Ash_c At_r At_a Hfa Ash_r Hnew Hq Hq1 Hkf Haddr2 Hlen2 Hshb2 Ash2_t Ash2_c Ash2_r)) ltac:(ztr_c ltac:(clear - Hc HHI Hsp' G1 G2 Espb G4 Eris G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 At_i At_s Ac_i Ac_s Emu Hmu3 Emfa Hmfa0 Hmfa1 Hnf4 Room1 Hnf0 Hr Er Hkm Hshb Haddr Hrb Ash_t Ash_c At_r At_a Hfa Ash_r Hnew Hq Hq1 Hkf Haddr2 Hlen2 Hshb2 Ash2_t Ash2_c Ash2_r)) ltac:(ztr_c ltac:(clear - Hc HHI Hsp' G1 G2 Espb G4 Eris G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 At_i At_s Ac_i Ac_s Emu Hmu3 Emfa Hmfa0 Hmfa1 Hnf4 Room1 Hnf0 Hr Er Hkm Hshb Haddr Hrb Ash_t Ash_c At_r At_a Hfa Ash_r Hnew Hq Hq1 Hkf Haddr2 Hlen2 Hshb2 Ash2_t Ash2_c Ash2_r)) ltac:(ztr_c ltac:(clear - Hc HHI Hsp' G1 G2 Espb G4 Eris G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 At_i At_s Ac_i Ac_s Emu Hmu3 Emfa Hmfa0 Hmfa1 Hnf4 Room1 Hnf0 Hr Er Hkm Hshb Haddr Hrb Ash_t Ash_c At_r At_a Hfa Ash_r Hnew Hq Hq1 Hkf Haddr2 Hlen2 Hshb2 Ash2_t Ash2_c Ash2_r)) ltac:(ztr_c ltac:(clear - Hc HHI Hsp' G1 G2 Espb G4 Eris G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 At_i At_s Ac_i Ac_s Emu Hmu3 Emfa Hmfa0 Hmfa1 Hnf4 Room1 Hnf0 Hr Er Hkm Hshb Haddr Hrb Ash_t Ash_c At_r At_a Hfa Ash_r Hnew Hq Hq1 Hkf Haddr2 Hlen2 Hshb2 Ash2_t Ash2_c Ash2_r)) ltac:(ztr_c ltac:(clear - Hc HHI Hsp' G1 G2 Espb G4 Eris G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 At_i At_s Ac_i Ac_s Emu Hmu3 Emfa Hmfa0 Hmfa1 Hnf4 Room1 Hnf0 Hr Er Hkm Hshb Haddr Hrb Ash_t Ash_c At_r At_a Hfa Ash_r Hnew Hq Hq1 Hkf Haddr2 Hlen2 Hshb2 Ash2_t Ash2_c Ash2_r)) ltac:(ztr_c ltac:(clear - Hc HHI Hsp' G1 G2 Espb G4 Eris G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 At_i At_s Ac_i Ac_s Emu Hmu3 Emfa Hmfa0 Hmfa1 Hnf4 Room1 Hnf0 Hr Er Hkm Hshb Haddr Hrb Ash_t Ash_c At_r At_a Hfa Ash_r Hnew Hq Hq1 Hkf Haddr2 Hlen2 Hshb2 Ash2_t Ash2_c Ash2_r)) ltac:(ztr_c ltac:(clear - Hc HHI Hsp' G1 G2 Espb G4 Eris G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 At_i At_s Ac_i Ac_s Emu Hmu3 Emfa Hmfa0 Hmfa1 Hnf4 Room1 Hnf0 Hr Er Hkm Hshb Haddr Hrb Ash_t Ash_c At_r At_a Hfa Ash_r Hnew Hq Hq1 Hkf Haddr2 Hlen2 Hshb2 Ash2_t Ash2_c Ash2_r)) ltac:(ztr_c ltac:(clear - Hc HHI Hsp' G1 G2 Espb G4 Eris G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 At_i At_s Ac_i Ac_s Emu Hmu3 Emfa Hmfa0 Hmfa1 Hnf4 Room1 Hnf0 Hr Er Hkm Hshb Haddr Hrb Ash_t Ash_c At_r At_a Hfa Ash_r Hnew Hq Hq1 Hkf Haddr2 Hlen2 Hshb2 Ash2_t Ash2_c Ash2_r))
ltac:(ztr_c ltac:(clear - Hc HHI Hsp' G1 G2 Espb G4 Eris G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 At_i At_s Ac_i Ac_s Emu Hmu3 Emfa Hmfa0 Hmfa1 Hnf4 Room1 Hnf0 Hr Er Hkm Hshb Haddr Hrb Ash_t Ash_c At_r At_a Hfa Ash_r Hnew Hq Hq1 Hkf Haddr2 Hlen2 Hshb2 Ash2_t Ash2_c Ash2_r)) ltac:(ztr_c ltac:(clear - Hc HHI Hsp' G1 G2 Espb G4 Eris G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 At_i At_s Ac_i Ac_s Emu Hmu3 Emfa Hmfa0 Hmfa1 Hnf4 Room1 Hnf0 Hr Er Hkm Hshb Haddr Hrb Ash_t Ash_c At_r At_a Hfa Ash_r Hnew Hq Hq1 Hkf Haddr2 Hlen2 Hshb2 Ash2_t Ash2_c Ash2_r)) ltac:(ztr_c ltac:(clear - Hc HHI Hsp' G1 G2 Espb G4 Eris G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 At_i At_s Ac_i Ac_s Emu Hmu3 Emfa Hmfa0 Hmfa1 Hnf4 Room1 Hnf0 Hr Er Hkm Hshb Haddr Hrb Ash_t Ash_c At_r At_a Hfa Ash_r Hnew Hq Hq1 Hkf Haddr2 Hlen2 Hshb2 Ash2_t Ash2_c Ash2_r)) ltac:(ztr_c ltac:(clear - Hc HHI Hsp' G1 G2 Espb G4 Eris G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 At_i At_s Ac_i Ac_s Emu Hmu3 Emfa Hmfa0 Hmfa1 Hnf4 Room1 Hnf0 Hr Er Hkm Hshb Haddr Hrb Ash_t Ash_c At_r At_a Hfa Ash_r Hnew Hq Hq1 Hkf Haddr2 Hlen2 Hshb2 Ash2_t Ash2_c Ash2_r)))
as (rC & MC & RUNC & C10 & C2 & C8 & C9 & C18 & C19 & C20 & KC & GC & AC & Tm1 & Tm2 & Tmfa).
eapply ar_steps; [exact RUNC|]. rewrite Eev in K. rewrite <- app_assoc. cbn [app].
assert (GMC : mem_grows M MC) by (eapply mem_grows_trans; [exact GM2|exact GC]).
assert (AMC : art_agree [(sp - 512, 512); (addr, 262144); (shb, 32768); (t + 2872, 16); (t + 2792, 8); (r + 48, 8); (addr2, len2); (shb2, 32768 * (q - kf)); (r + 24, 8)] M MC).
{ eapply art_agree_sub; [eapply art_agree_trans; [exact AM2|exact AC]|]. zsub_c ltac:(clear - Hc HHI Hsp' G1 G2 Espb G4 Eris G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 At_i At_s Ac_i Ac_s Emu Hmu3 Emfa Hmfa0 Hmfa1 Hnf4 Room1 Hnf0 Hr Er Hkm Hshb Haddr Hrb Ash_t Ash_c At_r At_a Hfa Ash_r Hnew Hq Hq1 Hkf Haddr2 Hlen2 Hshb2 Ash2_t Ash2_c Ash2_r). }
assert (KCR : forall x : reg, In x [3; 4; 21; 22; 23; 24; 25; 26; 27]%bv -> getr rC x = getr rB x).
{ intros x Hx. cbn [In] in Hx.
destruct Hx as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]; (rewrite KC by inl; unfold rZ2; gres; apply K1; inl). }
apply (art_populate_tail Q (log ++ [AMmapFixed addr 262144; AMmapFixed addr2 len2]) regs rC M MC rom raw sp HI t spb ris qs c km mx new (262144 * q) cl
Hret Hc HHI Hsp' Espb G4 Eris G6 G7 G8 G11 At_s Emu Hau0 Haumu Room1 Hmfa0 Hnf4 eq_refl Hnew Hcarve Hfb Emfa' ltac:(lia) Hq ltac:(lia)
ltac:(unfold art_region_rep; fold r fa nf; repeat split; assumption)
C10 C2 ltac:(rewrite C8; exact B8) ltac:(rewrite C9; exact B9) ltac:(rewrite C18; exact B18)
ltac:(rewrite C19; exact B19) ltac:(rewrite C20; exact B20) ltac:(rewrite KCR by inl; exact B21)).
+ intros x Hx. cbn [In] in Hx. destruct Hx as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]; (rewrite KCR by inl; apply KBR; inl).
+ exact GMC.
+ eapply art_agree_sub; [exact AMC|]. unfold art_pop_fpE. fold r fa. clear - Haddr Hshb Emu Hmfa0 Hmfa1 Haddr2 Hlen2 Hshb2 Hfa Hq Hq1 Hkf Emfa. zsub.
+ ztr_c ltac:(clear - Hc HHI Hsp' G1 G2 Espb G4 Eris G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 At_i At_s Ac_i Ac_s Emu Hmu3 Emfa Hmfa0 Hmfa1 Hnf4 Room1 Hnf0 Hr Er Hkm Hshb Haddr Hrb Ash_t Ash_c At_r At_a Hfa Ash_r Hnew Hq Hq1 Hkf Haddr2 Hlen2 Hshb2 Ash2_t Ash2_c Ash2_r).
+ ztr_c ltac:(clear - Hc HHI Hsp' G1 G2 Espb G4 Eris G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 At_i At_s Ac_i Ac_s Emu Hmu3 Emfa Hmfa0 Hmfa1 Hnf4 Room1 Hnf0 Hr Er Hkm Hshb Haddr Hrb Ash_t Ash_c At_r At_a Hfa Ash_r Hnew Hq Hq1 Hkf Haddr2 Hlen2 Hshb2 Ash2_t Ash2_c Ash2_r).
+ ztr_c ltac:(clear - Hc HHI Hsp' G1 G2 Espb G4 Eris G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 At_i At_s Ac_i Ac_s Emu Hmu3 Emfa Hmfa0 Hmfa1 Hnf4 Room1 Hnf0 Hr Er Hkm Hshb Haddr Hrb Ash_t Ash_c At_r At_a Hfa Ash_r Hnew Hq Hq1 Hkf Haddr2 Hlen2 Hshb2 Ash2_t Ash2_c Ash2_r).
+ ztr_c ltac:(clear - Hc HHI Hsp' G1 G2 Espb G4 Eris G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 At_i At_s Ac_i Ac_s Emu Hmu3 Emfa Hmfa0 Hmfa1 Hnf4 Room1 Hnf0 Hr Er Hkm Hshb Haddr Hrb Ash_t Ash_c At_r At_a Hfa Ash_r Hnew Hq Hq1 Hkf Haddr2 Hlen2 Hshb2 Ash2_t Ash2_c Ash2_r).
+ ztr_c ltac:(clear - Hc HHI Hsp' G1 G2 Espb G4 Eris G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 At_i At_s Ac_i Ac_s Emu Hmu3 Emfa Hmfa0 Hmfa1 Hnf4 Room1 Hnf0 Hr Er Hkm Hshb Haddr Hrb Ash_t Ash_c At_r At_a Hfa Ash_r Hnew Hq Hq1 Hkf Haddr2 Hlen2 Hshb2 Ash2_t Ash2_c Ash2_r).
+ ztr_c ltac:(clear - Hc HHI Hsp' G1 G2 Espb G4 Eris G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 At_i At_s Ac_i Ac_s Emu Hmu3 Emfa Hmfa0 Hmfa1 Hnf4 Room1 Hnf0 Hr Er Hkm Hshb Haddr Hrb Ash_t Ash_c At_r At_a Hfa Ash_r Hnew Hq Hq1 Hkf Haddr2 Hlen2 Hshb2 Ash2_t Ash2_c Ash2_r).
+ ztr_c ltac:(clear - Hc HHI Hsp' G1 G2 Espb G4 Eris G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 At_i At_s Ac_i Ac_s Emu Hmu3 Emfa Hmfa0 Hmfa1 Hnf4 Room1 Hnf0 Hr Er Hkm Hshb Haddr Hrb Ash_t Ash_c At_r At_a Hfa Ash_r Hnew Hq Hq1 Hkf Haddr2 Hlen2 Hshb2 Ash2_t Ash2_c Ash2_r).
+ ztr_c ltac:(clear - Hc HHI Hsp' G1 G2 Espb G4 Eris G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 At_i At_s Ac_i Ac_s Emu Hmu3 Emfa Hmfa0 Hmfa1 Hnf4 Room1 Hnf0 Hr Er Hkm Hshb Haddr Hrb Ash_t Ash_c At_r At_a Hfa Ash_r Hnew Hq Hq1 Hkf Haddr2 Hlen2 Hshb2 Ash2_t Ash2_c Ash2_r).
+ fold r mu. ztr_c ltac:(clear - Hc HHI Hsp' G1 G2 Espb G4 Eris G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 At_i At_s Ac_i Ac_s Emu Hmu3 Emfa Hmfa0 Hmfa1 Hnf4 Room1 Hnf0 Hr Er Hkm Hshb Haddr Hrb Ash_t Ash_c At_r At_a Hfa Ash_r Hnew Hq Hq1 Hkf Haddr2 Hlen2 Hshb2 Ash2_t Ash2_c Ash2_r).
+ fold r. exact Tmfa.
+ fold fa. eapply wr_grows; [exact GC|]. replace (262144 * q) with (mfa + len2) by lia.
apply wr_join; [lia|lia|lia|lia|eapply wr_grows; [exact GM2|exact Wfa]|]. fold addr2. unfold MZ2. apply wr_zfill; lia.
+ fold rb mu. eapply wr_grows; [eapply mem_grows_trans; [exact GB|]; eapply mem_grows_trans; [exact G1m|]; eapply mem_grows_trans; [exact GZ2|exact GC]|exact WUZ].
+ intros j Hj. pose proof (SH j Hj) as C. rewrite Hshb in C. ztr_c ltac:(clear - Hj Hc HHI Hsp' G1 G2 Espb G4 Eris G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 At_i At_s Ac_i Ac_s Emu Hmu3 Emfa Hmfa0 Hmfa1 Hnf4 Room1 Hnf0 Hr Er Hkm Hshb Haddr Hrb Ash_t Ash_c At_r At_a Hfa Ash_r Hnew Hq Hq1 Hkf Haddr2 Hlen2 Hshb2 Ash2_t Ash2_c Ash2_r).
+ exists (m1n' + 1), (m2n' + len2), (svn + 262144). repeat split; [exact Tm1|exact Tm2|ztr_c ltac:(clear - Hc HHI Hsp' G1 G2 Espb G4 Eris G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 At_i At_s Ac_i Ac_s Emu Hmu3 Emfa Hmfa0 Hmfa1 Hnf4 Room1 Hnf0 Hr Er Hkm Hshb Haddr Hrb Ash_t Ash_c At_r At_a Hfa Ash_r Hnew Hq Hq1 Hkf Haddr2 Hlen2 Hshb2 Ash2_t Ash2_c Ash2_r)].
+ exact K.
Qed.
End SE.
End Spec.
