(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import
PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk StreamSim MemSplit.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__StartupAux () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Init.Peano."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.BvBase."; "LinuxProcessSemantics.LinuxProcessSem.MemImageType."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1Some"; "1bool"; "1list"; "1nat"; "1option"; "1true"; "2and"; "2eq"; "2or"; "3le"; "4firstn"; "5Z"; "6Z_to_le_bytes"; "6bytes_le_to_Z"; "7Segment"; "8word_to_le_bytes"]; ["9bv_eqb"; "9bvmap_empty"; ":getr"; ":rdn"; ":v_add"; ":v_andi"; ":v_lw"; ":v_slli"; ":v_subw"; ";In"; ";existsb"; ";forallb"; "<add"; "<land"; "<le"; "<lt"]; ["<modulo"; "<mul"; "<ones"; "<pow"; "<sub"; "0a"; "0k"; "0l1"; "0l2"; "0m"; "0n"; "0r"; "0segs"; "0sh"; "=Z_to_bv"; "=bv"]; ["=bv_unsigned"; "0t"; "0v"; "0x"; "0y"; "0z"]]).
Section FPX_1. Context {fx : PropExec.FPState}.
Lemma getr_empty : ltac2:(TCodec.tc2 tcn__StartupAux "@'Q?y5%211'7yR0%511&B&A%1273r1%4221&Q>z%2291%;3941pRH=1").
Proof.
intro r. unfold getr. destruct (bv_eqb r 0); [reflexivity|].
unfold reg_get, bvmap_get, bvmap_empty.
destruct (bv_key r); cbn [tget]; apply bv_eq; reflexivity.
Qed.
End FPX_1.
Local Open Scope Z_scope.
Section FPX_2. Context {fx : PropExec.FPState}.
Lemma land_align_mask : ltac2:(TCodec.tc2 tcn__StartupAux "Q2';'6&Nzr2%3221&O&Q3+2+R0%3221%5271%;271%;294%=291'7&Q0r4r3%<2;1%4231%63E1B&Mr5&Q4%B2A8%22@1%5241%=3L15p081p0@1p0C1pR>Q01pR<Q11").
Proof.
intros a k Ha Hk Hmod.
replace (2^64 - 2^k) with (Z.ldiff (Z.ones 64) (Z.ones k)).
2:{ rewrite Z.ldiff_land, <- Z.sub_land_same_l, Z.land_ones by lia.
rewrite Z.ones_mod_pow2 by lia. rewrite !Z.ones_equiv. lia. }
rewrite Z.ldiff_land, Z.land_assoc, Z.land_ones by lia.
rewrite Z.mod_small by lia.
rewrite <- Z.ldiff_land, Z.ldiff_ones_r by lia.
rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia.
pose proof (Z.div_mod a (2^k) ltac:(lia)). lia.
Qed.
Lemma v_andi_m16_aligned : ltac2:(TCodec.tc2 tcn__StartupAux "D'Q?yR0%211'7';&Q0&Q@r1%2271+@%5221z%93821&Er2-@%3221%>3?13p061pS8A1").
Proof.
intros x Hm. unfold v_andi. apply bv_eq. rewrite Z_to_bv_unsigned.
change (bv_wrap 64 (-16)) with (2^64 - 2^4).
pose proof (u64_range x).
rewrite land_align_mask by (first [lia | exact Hm]).
apply bv_wrap_small. unfold bv_modulus. lia.
Qed.
Lemma v_andi_m8_aligned : ltac2:(TCodec.tc2 tcn__StartupAux "D'Q?yR0%211'7';&Q0&Q@r1%2271+8%5221z%93821&Er2-8%3221%>3?13p061pS8A1").
Proof.
intros x Hm. unfold v_andi. apply bv_eq. rewrite Z_to_bv_unsigned.
change (bv_wrap 64 (-8)) with (2^64 - 2^3).
pose proof (u64_range x).
rewrite land_align_mask by (first [lia | exact Hm]).
apply bv_wrap_small. unfold bv_modulus. lia.
Qed.
Lemma land_low_zero : ltac2:(TCodec.tc2 tcn__StartupAux "I';&Nzr2%3221'7&Q0r4&Q3+2r3%3221%6251%83=1;&Mr5&Q2%11:%4231%>3C1Ap071p0A1p0B1pR>G1pR<H1").
Proof. intros a k Ha Hk Hm. rewrite Z.land_ones by lia. exact Hm. Qed.
Lemma v_andi_3_aligned : ltac2:(TCodec.tc2 tcn__StartupAux "F'Q?yR0%211'7';&Q0&Q@r1%2271+4%5221z%93821&Er2+3%3221&Q>%12A7%@3A31p081pS8C1").
Proof.
intros x Hm. unfold v_andi. f_equal.
change (bv_wrap 64 3) with (Z.ones 2). apply land_low_zero; [apply u64_range | lia | exact Hm].
Qed.
Lemma land_4_aligned8 : ltac2:(TCodec.tc2 tcn__StartupAux "C';&Nzr1%3221'7&Q0r2+8%3221%53:18&Mr3+4%3221%:3?1=p061p0=1pR<B1").
Proof.
intros a Ha Hm.
apply Z.bits_inj'. intros i Hi.
rewrite Z.land_spec, Z.bits_0.
change 4 with (2^2). rewrite Z.pow2_bits_eqb by lia.
destruct (Z.eqb_spec 2 i); [|apply andb_false_r].
subst i.
replace a with ((a / 8) * 2^3) by lia.
rewrite Z.mul_pow2_bits by lia. change (2 - 3) with (-1).
rewrite Z.testbit_neg_r by lia. reflexivity.
Qed.
Lemma v_andi_4_aligned8 : ltac2:(TCodec.tc2 tcn__StartupAux "F'Q?yR0%211'7';&Q0&Q@r1%2271+8%5221z%93821&Er2+4%3221&Q>%12A7%@3A31p081pS8C1").
Proof.
intros x Hm. unfold v_andi. f_equal.
change (bv_wrap 64 4) with 4. apply land_4_aligned8; [apply u64_range | exact Hm].
Qed.
Lemma v_andi_1_of01 : ltac2:(TCodec.tc2 tcn__StartupAux "D';'8'7r1z%33521+1%53741%7231'Q?yR0%211&E&Q>r2%2251%421:%?3612p0:1pS<C1").
Proof.
intros z [-> | ->]; apply bv_eq; reflexivity.
Qed.
Lemma mod4_mod_pow2 : ltac2:(TCodec.tc2 tcn__StartupAux "C';&N+2r1%3221'7&Q0r3&Q3r2%2281%5241+4%7221%8272%:3?21p0<1pR>A1pS4B1").
Proof.
intros t k Hk. apply Z.mod_mod_divide.
exists (2^(k-2)). change 4 with (2^2). rewrite <- Z.pow_add_r by lia. f_equal. lia.
Qed.
Lemma negw_and3_aligned : ltac2:(TCodec.tc2 tcn__StartupAux "H'Q?yR0%211'7';&Q0&Q@r1%2271+4%5221z%93821&E&H&Q>%12?5r2%4221+3%7221%B3C15p0:1pS8E1").
Proof.
intros x Hm. unfold v_andi, v_subw. f_equal.
change (bv_wrap 64 3) with (Z.ones 2). rewrite Z.land_ones by lia.
rewrite Z_to_bv_unsigned. change (bv_unsigned (Z_to_bv 64 0)) with 0.
unfold bv_swrap. rewrite bv_wrap64_mod.
change (bv_half_modulus 32) with (2^31).
unfold bv_wrap. change (bv_modulus 32) with (2^32). change (2^2) with 4.
rewrite mod4_mod_pow2 by lia.
rewrite <- Zminus_mod_idemp_l.
rewrite mod4_mod_pow2 by lia.
replace ((0 - bv_unsigned x + 2^31) mod 4) with 0.
2:{ replace (0 - bv_unsigned x + 2^31) with (2^31 - bv_unsigned x) by lia.
rewrite <- Zminus_mod_idemp_r, Hm. reflexivity. }
reflexivity.
Qed.
Lemma firstn_Z_to_le_bytes : ltac2:(TCodec.tc2 tcn__StartupAux "G'3';'9r3r2%3221'7'2'Q?y8%211%411&:r4&<%12<;%43631%324=%<3721p0>1pS<C1pRFE1pR>F1").
Proof.
induction k as [|k IH]; intros n z Hk; [reflexivity|].
destruct n as [|n]; [lia|]. cbn [Z_to_le_bytes firstn]. rewrite IH by lia. reflexivity.
Qed.
Lemma firstn_word_to_le_bytes : ltac2:(TCodec.tc2 tcn__StartupAux "H'3'Q?yR0%211'9r3r2%3221'7'2y8%:11%311&:r4&?%12;:%43631%324<%;3721p0=1pS6B1pRFF1pR>G1").
Proof. intros. unfold word_to_le_bytes. apply firstn_Z_to_le_bytes. assumption. Qed.
Lemma rdn_low_bytes : ltac2:(TCodec.tc2 tcn__StartupAux "Q:'2'>%211'Q?yR0%211'4y8%511%311p051'3'9r1u8%3221'7%A19%<11&Cr6r5r4%443219(0&?r3%22=1%42;1%=3;61r7%<41;:5%726:%92@1%B3@31p061p0E1pR>J1pS6Q11pR<Q21pRDN1pRJQ71").
Proof.
intros segs m a v k Hk H.
rewrite (rdn_firstn segs m 8 a _ k H Hk). f_equal. apply firstn_word_to_le_bytes. exact Hk.
Qed.
Lemma bytes_le_to_Z_4_small : ltac2:(TCodec.tc2 tcn__StartupAux "H'Q?yR0%211&O&Q@r1%2251&Q3+2+Q0%3221%8251'7';&=&?u4r2%3221%511%@2C3%93821p0;1pS6E1").
Proof.
intros v Hv. rewrite bytes_le_N. change (2 ^ (8 * Z.of_nat 4)) with (2^32).
apply Z.mod_small. pose proof (u64_range v). lia.
Qed.
Lemma v_lw_small : ltac2:(TCodec.tc2 tcn__StartupAux "C'Q?yR0%211&O&Q@r1%2251&Q3+2+O%3221%8251'7&Fr2%211%43>12p061pS6@1").
Proof.
intros v Hv. unfold v_lw. apply bv_eq. rewrite Z_to_bv_unsigned.
pose proof (u64_range v).
rewrite bv_swrap_small by (change (bv_half_modulus 32) with (2^31); lia).
apply bv_wrap_small. unfold bv_modulus. lia.
Qed.
Lemma v_add_lit_r : ltac2:(TCodec.tc2 tcn__StartupAux "Q0'Q?yR0%211';'6&Nzr1%3221&O&Q3+2+R0%3221%5271%;271'7&Dr3&Q>r2%22D1%5241&L&Q@%12H7%3216%82J1%<3J61p0>1pR>K1pS8M1").
Proof. intros x k Hk. unfold v_add. rewrite (u_Z2bv k) by lia. reflexivity. Qed.
Lemma v_add_lit_l : ltac2:(TCodec.tc2 tcn__StartupAux "Q0'Q?yR0%211';'6&Nzr1%3221&O&Q3+2+R0%3221%5271%;271'7&D&Q>r2%22C1r3%5221&L&Q@%12H4%3217%92J1%<3J61p0>1pR>K1pS8M1").
Proof. intros x k Hk. unfold v_add. rewrite (u_Z2bv k) by lia. f_equal. lia. Qed.
Lemma v_slli_lit : ltac2:(TCodec.tc2 tcn__StartupAux "Q2';&Nzr2%3221&O&Q1r4&Q3+2r3%3221%6251+R0%6251%:231'7'Q?yR0%211&G&Q>r5%2251%421A%A2@B%D241%6291%<3941p0>1p0J1p0K1pRLQ01pS<Q11").
Proof.
intros z sh Hz Hsh Hb. unfold v_slli. f_equal.
rewrite Z.shiftl_mul_pow2 by lia. rewrite u_Z2bv by nia. reflexivity.
Qed.
Lemma in_sub_bv : ltac2:(TCodec.tc2 tcn__StartupAux "M'2'Q?y5%211%411'7'1&K&J&@r2r1%33:21qS::1r3%73<21qS8=1%:3>13(5%>3=21&Ir4%23C<1%33D92p021p061pRHG1pRBG1pR@H1").
Proof.
induction l1 as [|x l1 IH]; intros l2 r H Hin; [contradiction|].
cbn [forallb] in H. apply andb_true_iff in H as [Hx Hl1].
destruct Hin as [<-|Hin]; [|apply IH; assumption].
clear IH Hl1. induction l2 as [|y l2 IH2]; [discriminate|].
cbn [existsb] in Hx. apply orb_true_iff in Hx as [Hxy|Hx].
- left. symmetry. apply bv_eq. unfold bv_eqb in Hxy. apply Z.eqb_eq in Hxy. exact Hxy.
- right. apply IH2. exact Hx.
Qed.
Lemma Z_to_bv_u_eq : ltac2:(TCodec.tc2 tcn__StartupAux "A'Q?yR0%211';'7r1&Q@r2%2271%53641&Q>%12:4r3%93;21p051pS<<1pR<>1").
Proof. intros a z ->. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range. Qed.
Lemma Z_to_bv_u_eq_sym : ltac2:(TCodec.tc2 tcn__StartupAux "A'Q?yR0%211';'7r1&Q@r2%2271%53641r3&Q>%12;5%93;31p051pS<<1pR<>1").
Proof. intros a z H. symmetry. apply Z_to_bv_u_eq. exact H. Qed.
End FPX_2.
