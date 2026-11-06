(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import Tac Arr Bytes.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec Require Import StrFun.
Import ListNotations.
Local Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__CJ_Agent_STRW_merge () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.BvBase."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.STRW_merge."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Bytes."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Mem."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1cons"; "1length"; "1list"; "1nat"; "1nil"; "2and"; "2eq"; "3map"; "4Z"; "5le_bytes_to_word"; "6sext"; "7v4"; "8le_val"; "9le1"; "9le4"; ":add"]; [":div"; ":le"; ":lor"; ":lt"; ":modulo"; ":mul"; ":pow"; ":shiftl"; ":shiftr"; ":sub"; "0a"; "0b"; "0b0"; "0b1"; "0b2"; "0b3"]; ["0bs"; "0c0"; "0c1"; "0c2"; "0c3"; "0j"; ";Z_to_bv"; ";bv"; ";bv_extract"; ";bv_swrap"; ";bv_unsigned"; ";bv_wrap"; "0x"; "0z"]]).
Local Notation LW w := (sext 64 (bv_extract 0 32 (le_bytes_to_word w))).
Local Notation M64 := 18446744073709551616%Z.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import RunP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section CEIL_WRAP_1.
Context {RUNp : RunP}.
Definition v4 (b0 b1 b2 b3 : byte) : Z :=
bv_unsigned b0 + 256 * bv_unsigned b1 + 65536 * bv_unsigned b2 + 16777216 * bv_unsigned b3.
End CEIL_WRAP_1.
Local Ltac br b := pose proof (byte_range b).
Section CEIL_WRAP_2.
Context {RUNp : RunP}.
Lemma lw_u : ltac2:(TCodec.tc2 tcn__CJ_Agent_STRW_merge "QB'Q7y8%211'6'8&Q:yR0&:yQ0&Q8w&9(0r4r3r2r1(4%11@%73A31%83B51%93C71%:3D91%<11%?4B>@1%B3AC1%E2D1&?&;%14@?>=&E&I&F+2+R0%3221+Q0%5241%7231&@%Q32Q7H+T0%3221%=251%A2?1%Q:3Q9C1pR0Q<1pQNQ=1pQLQ>1pQJQ?1").
Proof. intros b0 b1 b2 b3. rewrite lw_unsigned4. reflexivity. Qed.
Lemma lw_wrap32 : ltac2:(TCodec.tc2 tcn__CJ_Agent_STRW_merge "Q4'Q7y8%211'6'8&Q;yQ0&Q:yR0&:&Q8w&9(0r4r3r2r1(4%11A%73B31%83C51%93D71%:3E91%<11%?4A>C1%A3DB1%D2C1%G2F1&;%14@?>=%L3K31pR0N1pQNO1pQLQ01pQJQ11").
Proof. intros b0 b1 b2 b3.
rewrite lw_u, bv_wrap32_eq. br b0; br b1; br b2; br b3. unfold v4.
Z.div_mod_to_equations. lia.
Qed.
Lemma lw_mod32 : ltac2:(TCodec.tc2 tcn__CJ_Agent_STRW_merge "Q8'Q7y8%211'6'8&D&Q:yR0&:yQ0&Q8w&9(0r4r3r2r1(4%11A%73B31%83C51%93D71%:3E91%<11%?4B>@1%B3AC1%E2D1&F+2+Q0%3221%K251&;%14DCBA%Q03O31pR0Q21pQNQ31pQLQ41pQJQ51").
Proof. intros b0 b1 b2 b3. rewrite <- bv_wrap32_eq. apply lw_wrap32. Qed.
Lemma swrap32_small : ltac2:(TCodec.tc2 tcn__CJ_Agent_STRW_merge "E'8'5&Azr1%3221&C&F+2+O%3221%5271%;271'6&Q9yQ0r2%3221%53B12p071pRJD1").
Proof. intros x. intros. rewrite bv_swrap32_eq. rewrite Z.mod_small; lia. Qed.
Lemma mod64_small : ltac2:(TCodec.tc2 tcn__CJ_Agent_STRW_merge "E'8'5&Azr1%3221&C&F+2+R0%3221%5271%;271'6&Dr2+`PPPPPPPPPPP0%3221%53B13p071pRJD1").
Proof. intros x. intros. apply Z.mod_small. lia. Qed.
Lemma mod32_small : ltac2:(TCodec.tc2 tcn__CJ_Agent_STRW_merge "D'8'5&Azr1%3221&C&F+2+Q0%3221%5271%;271'6&Dr2%2216%43A12p061pRJC1").
Proof. intros x. intros. apply Z.mod_small. lia. Qed.
Lemma swrap32_mod32 : ltac2:(TCodec.tc2 tcn__CJ_Agent_STRW_merge "?'8'6&D&Q9yQ0r1%3221&F+2+Q0%3221%9251%:272%<3=21pRJ>1").
Proof. intros x. rewrite bv_swrap32_eq. Z.div_mod_to_equations. lia. Qed.
Lemma mod64_mod32 : ltac2:(TCodec.tc2 tcn__CJ_Agent_STRW_merge ">'8'6&Dr1+`PPPPPPPPPPP0%3221&F+2+Q0%3221%8251%9282%;3<21pRJ=1").
Proof. intros x. Z.div_mod_to_equations. lia. Qed.
Lemma lor_mod32 : ltac2:(TCodec.tc2 tcn__CJ_Agent_STRW_merge "B'8'6&D&Br2r1%3221&F+2+Q0%3221%9251%:282%;283%;221%>3?41pQH@1pQFA1").
Proof. intros a b. rewrite <- !Z.land_ones by lia. apply Z.land_lor_distr_l. Qed.
Lemma shl_mod32 : ltac2:(TCodec.tc2 tcn__CJ_Agent_STRW_merge "I'8&Azr1%3221'6&D&Gr3r2%3221&F+2+Q0%3221%9251&E%;293%7269%3221%>216%@3E61p0B1pR<G1pRJH1").
Proof. intros x j. intros. rewrite Z.shiftl_mul_pow2, <- Zmult_mod_idemp_l by lia. reflexivity. Qed.
Lemma le4_lit_of_mod32 : ltac2:(TCodec.tc2 tcn__CJ_Agent_STRW_merge "Q9'8'2'Q7y8%211%411'6'3&1r1%2261u4%63521&Dr3+`PPPPPPPPPPP0%3221&F+2+Q0%3221%8251&<&7&Q:%11Fr2%44GK21%611%G3M81&>&Q6yR0r4%3221%511%N3O1Fp081p0J1pR2Q21pRLQ81").
Proof. intros z bs.
intros Hl Hz. apply le4_of_mod32; [exact Hl|]. rewrite unsigned_lit_wrap. exact Hz.
Qed.
Lemma le1_lit_of_mod8 : ltac2:(TCodec.tc2 tcn__CJ_Agent_STRW_merge "Q2'8'Q7y8%211'6&Dr2+`PPPPPPPPPPP0%3221&F+2+8%3221%8251&Q:r1%22>1%=3A41'2%11@&=&Q6yR0r3%3221%511(0(4%11I%33JG1%J3;51p0>1pQHM1pRLQ11").
Proof. intros z b. intros Hz. apply le1_of_mod8. rewrite unsigned_lit_wrap. exact Hz. Qed.
Section merge.
Variables b0 b1 b2 b3 c0 c1 c2 c3 : byte.
Lemma lo24 : ltac2:(TCodec.tc2 tcn__CJ_Agent_STRW_merge "Q<'6'8&D&Q9yQ0&H&Q;&Q:yR0&:&Q8w&9(0'Q7y8%211vLvMvNvO(4%116%:3731%;3851%<3971%=3:91%?11%B4DAH1%D3IE1%G2F1%I2K1+H%L221%O2N1+`PPPPPPPPPPP0%Q2221&F+2+Q0%3221%Q7251%Q32KF%Q;3Q:21").
Proof.
rewrite lw_wrap32, Z.shiftr_div_pow2 by lia. br b0; br b1; br b2; br b3. unfold v4.
replace (_ / 2^24) with (bv_unsigned b3) by (Z.div_mod_to_equations; lia).
rewrite swrap32_small, mod64_small by lia. apply Z.mod_small. lia.
Qed.
Lemma lo16 : ltac2:(TCodec.tc2 tcn__CJ_Agent_STRW_merge "QB'6'8&D&Q9yQ0&H&Q;&Q:yR0&:&Q8w&9(0'Q7y8%211vLvMvNvO(4%116%:3731%;3851%<3971%=3:91%?11%B4DAH1%D3IE1%G2F1%I2K1+@%L221%O2N1+`PPPPPPPPPPP0%Q2221&F+2+Q0%3221%Q7251&?%Q42LH&E+X0%Q72OJ%3221%6251%QA3Q@81").
Proof.
rewrite lw_wrap32, Z.shiftr_div_pow2 by lia. br b0; br b1; br b2; br b3. unfold v4.
replace (_ / 2^16) with (bv_unsigned b2 + 256 * bv_unsigned b3) by (Z.div_mod_to_equations; lia).
rewrite swrap32_small, mod64_small by lia. apply Z.mod_small. lia.
Qed.
Lemma lo8 : ltac2:(TCodec.tc2 tcn__CJ_Agent_STRW_merge "QF'6'8&D&Q9yQ0&H&Q;&Q:yR0&:&Q8w&9(0'Q7y8%211vLvMvNvO(4%116%:3731%;3851%<3971%=3:91%?11%B4DAH1%D3IE1%G2F1%I2K1+8%L221%O2N1+`PPPPPPPPPPP0%Q2221&F+2+Q0%3221%Q7251&?%Q42LI&E+X0%Q72OK%3221%6251+RPP0%Q;2Q3N%7221%:241%QE3QD<1").
Proof.
rewrite lw_wrap32, Z.shiftr_div_pow2 by lia. br b0; br b1; br b2; br b3. unfold v4.
replace (_ / 2^8) with (bv_unsigned b1 + 256 * bv_unsigned b2 + 65536 * bv_unsigned b3) by (Z.div_mod_to_equations; lia).
rewrite swrap32_small, mod64_small by lia. apply Z.mod_small. lia.
Qed.
Lemma hi8 : ltac2:(TCodec.tc2 tcn__CJ_Agent_STRW_merge "Q1'6'8&D&E&;vQ1vQ2vQ3vQ4%544321&F+2+8%3221%;251+Q0%6251%?231&?+X0&Q:y8%221A%D241+RPP0%524C%G221%9241+`PPP0%928F%K221%=241%Q03O?1").
Proof. br c0; br c1; br c2; br c3. unfold v4. Z.div_mod_to_equations. lia. Qed.
Lemma hi16 : ltac2:(TCodec.tc2 tcn__CJ_Agent_STRW_merge "M'6'8&D&E&;vQ1vQ2vQ3vQ4%544321&F+2+@%3221%;251+Q0%6251%?231&?+RPP0&Q:y8%221A%D241+`PPP0%524C%G221%9241%L3K;1").
Proof. br c0; br c1; br c2; br c3. unfold v4. Z.div_mod_to_equations. lia. Qed.
Lemma hi24 : ltac2:(TCodec.tc2 tcn__CJ_Agent_STRW_merge "H'6'8&D&E&;vQ1vQ2vQ3vQ4%544321&F+2+H%3221%;251+Q0%6251%?231+`PPP0&Q:y8%221@%C241%G3F61").
Proof. br c0; br c1; br c2; br c3. unfold v4. Z.div_mod_to_equations. lia. Qed.
Lemma hi_a : ltac2:(TCodec.tc2 tcn__CJ_Agent_STRW_merge "QE'8&Azr1%3221'6&D&Q9yQ0&G&Q:yR0&:&Q8w&9(0'Q7y8%211vQ1vQ2vQ3vQ4(4%116%:3731%;3851%<3971%=3:91%?11%B4DAG1%D3HE1%G2F1r2%J221%M2L1+`PPPPPPPPPPP0%Q0221&F+2+Q0%3221%Q5251&E&;%14JIHG%827=%4221%Q;217%Q=3QB71p0Q?1pR<QD1").
Proof. intros j. intros. rewrite mod64_mod32, swrap32_mod32, shl_mod32, lw_mod32 by lia. reflexivity. Qed.
Lemma hi_r : ltac2:(TCodec.tc2 tcn__CJ_Agent_STRW_merge "QC'8&Azr1%3221'6&D&G&Q:yR0&:yQ0&Q8w&9(0'Q7y8%211vQ1vQ2vQ3vQ4(4%116%:3731%;3851%<3971%=3:91%?11%B4EAC1%E3DF1%H2G1r2%K221+`PPPPPPPPPPP0%N221&F+2+Q0%3221%Q3251&E&;%14IHGF%827<%4221%Q9217%Q;3Q@71p0Q=1pR<QB1").
Proof. intros j. intros. rewrite mod64_mod32, shl_mod32, lw_mod32 by lia. reflexivity. Qed.
Local Ltac merge_tac lo hi hik k :=
apply le4_lit_of_mod32; [reflexivity|];
rewrite mod64_mod32, lor_mod32, lo, hi, hik by lia; cbn [map le_val];
br b0; br b1; br b2; br b3; br c0; br c1; br c2; br c3;
first [ rewrite (lor_add' _ _ k); [ lia | lia | lia | Z.div_mod_to_equations; lia ]
| rewrite (lor_add _ _ k); [ lia | lia | lia | Z.div_mod_to_equations; lia ] ].
Lemma merge_a24 : ltac2:(TCodec.tc2 tcn__CJ_Agent_STRW_merge "R2'6'2'Q7y8%211%411&>&Q6yR0&B&D&Q9yQ0&H&Q;&Q:&:&Q8w&9(0vLvMvNvO(4%11F%73G31%83H51%93I71%:3J91%<11%?4H>D1%A3EI1%C2J1%E2G1+H%H221%K2J1+`PPPPPPPPPPP0%N221&GvQ1vQ2vQ3vQ4%J3Q:1D%K3Q;31%L3Q<51%M3Q=71%O11%Q24Q;Q1Q71%Q43Q8Q<1%Q62Q=1+8%>221%Q=2Q<1%Q?21B%QA2B1%QD2QC1%QF11%Q93QIAQ3%Q:3QJC1%Q;3QKE1%Q<3QLQ81%R13QL51").
Proof. merge_tac lo24 hi_a hi8 8%Z. Qed.
Lemma merge_a16 : ltac2:(TCodec.tc2 tcn__CJ_Agent_STRW_merge "R1'6'2'Q7y8%211%411&>&Q6yR0&B&D&Q9yQ0&H&Q;&Q:&:&Q8w&9(0vLvMvNvO(4%11F%73G31%83H51%93I71%:3J91%<11%?4H>D1%A3EI1%C2J1%E2G1+@%H221%K2J1+`PPPPPPPPPPP0%N221&GvQ1vQ2vQ3vQ4%J3Q:1D%K3Q;31%L3Q<51%M3Q=71%O11%Q24Q;Q1Q71%Q43Q8Q<1%Q62Q=1%=21B%Q<2Q;1%Q>21A%Q@2A1%QC2QB1%QE11%Q83QHAQ2%Q93QIC1%Q:3QJQ61%Q;3QKQ81%R03QK51").
Proof. merge_tac lo16 hi_a hi16 16%Z. Qed.
Lemma merge_a8 : ltac2:(TCodec.tc2 tcn__CJ_Agent_STRW_merge "R2'6'2'Q7y8%211%411&>&Q6yR0&B&D&Q9yQ0&H&Q;&Q:&:&Q8w&9(0vLvMvNvO(4%11F%73G31%83H51%93I71%:3J91%<11%?4H>D1%A3EI1%C2J1%E2G1+8%H221%K2J1+`PPPPPPPPPPP0%N221&GvQ1vQ2vQ3vQ4%J3Q:1D%K3Q;31%L3Q<51%M3Q=71%O11%Q24Q;Q1Q71%Q43Q8Q<1%Q62Q=1+H%>221%Q=2Q<1%Q?21B%QA2B1%QD2QC1%QF11%Q93QICQ3%Q:3QJQ61%Q;3QKQ81%Q<3QLQ:1%R13QL51").
Proof. merge_tac lo8 hi_a hi24 24%Z. Qed.
Lemma merge_r24 : ltac2:(TCodec.tc2 tcn__CJ_Agent_STRW_merge "R1'6'2'Q7y8%211%411&>&Q6yR0&B&D&G&Q:&:yQ0&Q8w&9(0vQ1vQ2vQ3vQ4(4%11D%73E31%83F51%93G71%:3H91%<11%?4F>@1%B3AG1%D2H1+8%G221+`PPPPPPPPPPP0%J221&Q9&H&Q;vLvMvNvO%J3Q81D%K3Q931%L3Q:51%M3Q;71%O11%Q24Q9Q1Q31%Q53Q4Q:1%Q72Q;1%=2Q61+H%@221%B2Q91%Q>21E%Q@2E1%QC2QB1%QE11%Q:3QHQ7Q4%Q;3QIQ91%Q<3QJQ;1%Q=3QKD1%R03QK51").
Proof. merge_tac lo24 hi_r hi8 8%Z. Qed.
Lemma merge_r16 : ltac2:(TCodec.tc2 tcn__CJ_Agent_STRW_merge "R0'6'2'Q7y8%211%411&>&Q6yR0&B&D&G&Q:&:yQ0&Q8w&9(0vQ1vQ2vQ3vQ4(4%11D%73E31%83F51%93G71%:3H91%<11%?4F>@1%B3AG1%D2H1+@%G221+`PPPPPPPPPPP0%J221&Q9&H&Q;vLvMvNvO%J3Q81D%K3Q931%L3Q:51%M3Q;71%O11%Q24Q9Q1Q31%Q53Q4Q:1%Q72Q;1%=2Q61%?21D%A2Q81%Q=21D%Q?2D1%QB2QA1%QD11%Q93QGQ7Q3%Q:3QHQ91%Q;3QIB1%Q<3QJD1%QO3QJ51").
Proof. merge_tac lo16 hi_r hi16 16%Z. Qed.
Lemma merge_r8 : ltac2:(TCodec.tc2 tcn__CJ_Agent_STRW_merge "R1'6'2'Q7y8%211%411&>&Q6yR0&B&D&G&Q:&:yQ0&Q8w&9(0vQ1vQ2vQ3vQ4(4%11D%73E31%83F51%93G71%:3H91%<11%?4F>@1%B3AG1%D2H1+H%G221+`PPPPPPPPPPP0%J221&Q9&H&Q;vLvMvNvO%J3Q81D%K3Q931%L3Q:51%M3Q;71%O11%Q24Q9Q1Q31%Q53Q4Q:1%Q72Q;1%=2Q61+8%@221%B2Q91%Q>21E%Q@2E1%QC2QB1%QE11%Q:3QHQ9Q4%Q;3QIB1%Q<3QJD1%Q=3QKF1%R03QK51").
Proof. merge_tac lo8 hi_r hi24 24%Z. Qed.
Lemma lwb0 : ltac2:(TCodec.tc2 tcn__CJ_Agent_STRW_merge "N'6'2'Q7y8%211%411&=&:yQ0yR0&Q8w&9(0vLvMvNvO(4%11?%73@31%83A51%93B71%:3C91%<11%?4@>A1%C3BA1%E11%?3H>9%M3H21").
Proof.
apply le1_of_mod8. rewrite lw_u. br b0; br b1; br b2; br b3. unfold v4.
Z.div_mod_to_equations. lia.
Qed.
Lemma lwb1 : ltac2:(TCodec.tc2 tcn__CJ_Agent_STRW_merge "Q5'6'2'Q7y8%211%411&=&Q6yR0&H&Q:&:yQ0&Q8w&9(0vLvMvNvO(4%11B%73C31%83D51%93E71%:3F91%<11%?4D>@1%B3AE1%D2F1+8%G221%J2I1%L11%C3OA=%Q43O21").
Proof.
apply le1_lit_of_mod8. rewrite lw_u, Z.shiftr_div_pow2 by lia. br b0; br b1; br b2; br b3. unfold v4.
replace (_ / 2^8) with (bv_unsigned b1 + 256 * bv_unsigned b2 + 65536 * bv_unsigned b3 + (2^56 - 2^24) * (bv_unsigned b3 / 128))
by (Z.div_mod_to_equations; lia).
rewrite mod64_small by lia. Z.div_mod_to_equations. lia.
Qed.
Lemma lwb2 : ltac2:(TCodec.tc2 tcn__CJ_Agent_STRW_merge "Q5'6'2'Q7y8%211%411&=&Q6yR0&H&Q:&:yQ0&Q8w&9(0vLvMvNvO(4%11B%73C31%83D51%93E71%:3F91%<11%?4D>@1%B3AE1%D2F1+@%G221%J2I1%L11%C3O@=%Q43O21").
Proof.
apply le1_lit_of_mod8. rewrite lw_u, Z.shiftr_div_pow2 by lia. br b0; br b1; br b2; br b3. unfold v4.
replace (_ / 2^16) with (bv_unsigned b2 + 256 * bv_unsigned b3 + (2^48 - 2^16) * (bv_unsigned b3 / 128))
by (Z.div_mod_to_equations; lia).
rewrite mod64_small by lia. Z.div_mod_to_equations. lia.
Qed.
End merge.
End CEIL_WRAP_2.
