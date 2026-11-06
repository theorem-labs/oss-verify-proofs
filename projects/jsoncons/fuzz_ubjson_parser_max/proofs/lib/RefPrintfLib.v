(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec SeqExec AgentLib.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__RefPrintfLib () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.MemImageType."; "LinuxProcessSemantics.Riscv.Instr."; "LinuxProcessSemantics.Riscv.Sem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1Some"; "1bool"; "1cons"; "1false"; "1list"; "1negb"; "1nil"; "1option"; "1true"; "2and"; "2eq"; "2or"; "3Z"; "4Segment"; "5ALU_ADD"; "5ALU_AND"]; ["5BC_EQ"; "5BC_GEU"; "5BC_LTU"; "5BC_NE"; "5M_MUL"; "6alu64"; "6branch_taken"; "6mul_div"; "7rdn"; "8add"; "8eqb"; "8le"; "8lt"; "8ltb"; "8modulo"; "8pow"]; ["8sub"; "0a"; "0b"; "0b0"; "0b1"; "0c"; "0k"; "0m"; "0r"; "0segs"; "9Z_to_bv"; "9bv"; "9bv_unsigned"; "0t"; "0w"; "0x"]]).
Section FPX_1. Context {fx : PropExec.FPState}.
Lemma alu_add_Z : ltac2:(TCodec.tc2 tcn__RefPrintfLib "C'<':'Q;yR0%211&E(>&Q:r2%2261r1%4281%73631&I%1264%82<1%?3<41pR6A1pR4B1").
Proof.
intros a b. apply bv_eq. change (alu64 ALU_ADD (Z_to_bv 64 a) (Z_to_bv 64 b)) with (Z_to_bv 64 a + Z_to_bv 64 b)%bv.
rewrite bv_add_unsigned, !Z_to_bv_unsigned, !bv_wrap64_mod.
rewrite <- Z.add_mod by lia. reflexivity.
Qed.
Lemma alu_and3_Z : ltac2:(TCodec.tc2 tcn__RefPrintfLib "H'<&Kzr1%3221':'Q;yR0%211&E(?&Q:r2%2261+3%4281%73631&N+4%2271%92=1%@3=51p0B1pR4G1").
Proof.
intros a Ha. apply bv_eq.
change (alu64 ALU_AND (Z_to_bv 64 a) (Z_to_bv 64 3)) with (bv_and (Z_to_bv 64 a) (Z_to_bv 64 3)).
rewrite bv_and_unsigned, !Z_to_bv_unsigned, !bv_wrap64_mod.
change (3 mod 2 ^ 64) with (Z.ones 2). rewrite Z.land_ones by lia.
change (2 ^ 2) with 4.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
lia.
Qed.
End FPX_1.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section FPX_2. Context {fx : PropExec.FPState}.
Lemma bt_eq0_Z : ltac2:(TCodec.tc2 tcn__RefPrintfLib "L'<'9&Kzr1%3221&L&O+2+R0%3221%5271%;271':'1&F(@&Q:yR0r2%3221%423B%73621&J%125E%<3;31p0>1pR4K1").
Proof. intros a Ha. cbn [branch_taken]. unfold bv_eqb. rewrite !u64_lit by lia. reflexivity. Qed.
Lemma bt_ne0_Z : ltac2:(TCodec.tc2 tcn__RefPrintfLib "N'<'9&Kzr1%3221&L&O+2+R0%3221%5271%;271':'1&F(C&Q:yR0r2%3221%423B%73621&5&J%126F%311%>3=51p0@1pR4M1").
Proof. intros a Ha. cbn [branch_taken]. unfold bv_eqb. rewrite !u64_lit by lia. reflexivity. Qed.
Lemma bt_and3 : forall c (w k : Z) (t : bool), 0 <= w + k ->
match c with BC_EQ => ((w + k) mod 4 =? 0) = t | BC_NE => negb ((w + k) mod 4 =? 0) = t | _ => False end ->
branch_taken c (alu64 ALU_AND (alu64 ALU_ADD (Z_to_bv 64 w) (Z_to_bv 64 k)) (Z_to_bv 64 3)) (Z_to_bv 64 0) = t.
Proof.
intros c w k t Hw Hc. rewrite alu_add_Z, alu_and3_Z by lia.
pose proof (Z.mod_pos_bound (w + k) 4 ltac:(lia)).
destruct c; try contradiction.
- rewrite bt_eq0_Z by lia. exact Hc.
- rewrite bt_ne0_Z by lia. exact Hc.
Qed.
Lemma bt_and3_0 : forall c (w : Z) (t : bool), 0 <= w ->
match c with BC_EQ => (w mod 4 =? 0) = t | BC_NE => negb (w mod 4 =? 0) = t | _ => False end ->
branch_taken c (alu64 ALU_AND (Z_to_bv 64 w) (Z_to_bv 64 3)) (Z_to_bv 64 0) = t.
Proof.
intros c w t Hw Hc. rewrite alu_and3_Z by lia.
pose proof (Z.mod_pos_bound w 4 ltac:(lia)).
destruct c; try contradiction.
- rewrite bt_eq0_Z by lia. exact Hc.
- rewrite bt_ne0_Z by lia. exact Hc.
Qed.
Lemma rdn_2 : ltac2:(TCodec.tc2 tcn__RefPrintfLib "QM'4'=%211'Q;yR0%211'7y8%511%311p051&K&I&Q<r3%22;1+2%5221&O+R0%2241%:241':%G1?%B11&Hr6r5r4u1%544321(0(2(6%11J%33KE1%52=1%?3=71r7&Q:%K2Q4=+1%N221%42Q71%C46B1?%G3E19r8u2%G42:F1%A3Q9E?%B3Q:G1%D2L1%N3L41p081p0A1p0Q21pR:Q@1pR8QA1pR4QE1pR@QA1pRDQJ1").
Proof.
intros segs m a b0 b1 Hnw H0 H1. cbn [rdn] in *.
destruct (match m a with Some b => Some b | None => seg_rom segs a end) as [x|]; [|discriminate].
injection H0 as ->.
replace (a + 1)%bv with (Z_to_bv 64 (bv_unsigned a + 1)).
2:{ apply bv_eq. rewrite u64_lit by (pose proof (u64_range a); lia). symmetry. apply u_add1. lia. }
destruct (match m (Z_to_bv 64 (bv_unsigned a + 1)) with Some b => Some b | None => seg_rom segs _ end) as [y|];
[|discriminate].
injection H1 as ->. reflexivity.
Qed.
Lemma lin_neg1_val : ltac2:(TCodec.tc2 tcn__RefPrintfLib "I'Q;yR0%211'<':&E(>&G(D&Q:-1%22:1r2%64<521r1%62>1%;3:31&Q0&Q<%12B7%3261%<2D1%B3D61pR<D1pS0F1").
Proof.
intros x c. apply bv_eq.
change (alu64 ALU_ADD (mul_div M_MUL (Z_to_bv 64 (-1)) x) (Z_to_bv 64 c))
with ((Z_to_bv 64 (-1) * x) + Z_to_bv 64 c)%bv.
rewrite bv_add_unsigned, bv_mul_unsigned, !Z_to_bv_unsigned, !bv_wrap64_mod.
change ((-1) mod 2 ^ 64) with (2 ^ 64 - 1).
rewrite <- Z.add_mod by lia.
replace ((2 ^ 64 - 1) * bv_unsigned x + c) with ((c - bv_unsigned x) + bv_unsigned x * 2 ^ 64) by lia.
rewrite Z.mod_add by lia. reflexivity.
Qed.
Lemma bt_geu_Z : ltac2:(TCodec.tc2 tcn__RefPrintfLib "Q0'<'9&Kzr1%3221r2%5231%7231&Lr3&O+2+R0%3221%6251':'1&F(A&Q:yR0r4%3221%423>%73621(8%;3:21p0=1p0E1pR6N1pR4O1").
Proof.
intros a b Hab Ha. cbn [branch_taken]. unfold bv_ltu. rewrite !u64_lit by lia.
apply Bool.negb_true_iff. apply Z.ltb_ge. lia.
Qed.
Lemma bt_geu_Z_false : ltac2:(TCodec.tc2 tcn__RefPrintfLib "Q0'<'9&Kzr2%3221&Lr1%2241%8241&O+2+R0%3221%82:1':'1&F(A&Q:yR0r4%3221r3%5241%83731(3%<3;21p0>1p0D1pR6N1pR4O1").
Proof.
intros a b Hab Hb. cbn [branch_taken]. unfold bv_ltu. rewrite !u64_lit by lia.
apply Bool.negb_false_iff. apply Z.ltb_lt. lia.
Qed.
Lemma bt_ltu_Z : ltac2:(TCodec.tc2 tcn__RefPrintfLib "Q3'<'1'9&Kzr3%3221&L&O+2+R0%3221%5271%;271':&Mr5r4%3221%53B1>&F(B&Q:yR0r6%3221%423:%73621%>3K1;p0:1p0A1p0B1pRLO1pR6Q11pR4Q21").
Proof. intros a b t Ha Hb Ht. cbn [branch_taken]. unfold bv_ltu. rewrite !u64_lit by lia. exact Ht. Qed.
End FPX_2.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Section FPX_3. Context {fx : PropExec.FPState}.
Lemma mod4_shift : ltac2:(TCodec.tc2 tcn__RefPrintfLib "D'<':&Nr3+4%3221r1%63721&Ir4%2217%9217r2%521:%<21:%>3?41p091pRBA1pR>B1pRNC1").
Proof. intros w k r H. rewrite <- Zplus_mod_idemp_l, H. reflexivity. Qed.
Lemma even_mod4 : ltac2:(TCodec.tc2 tcn__RefPrintfLib "A'<':&Nr1+2%3221z%63721';r2+4%9221%;3<16%<3=29%6221p081pRN@1").
Proof. intros w H. lia. Qed.
Lemma mod4_cases : ltac2:(TCodec.tc2 tcn__RefPrintfLib "C'<';':&Nr1+4%3221z%63821+1%83:41+2%:3<61+3%<3>81%>231%?261%@291pRNB1").
Proof. intros w. lia. Qed.
End FPX_3.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
