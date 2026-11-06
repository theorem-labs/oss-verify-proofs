(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StoreOk
AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 SegRun SegPlan AsanPlanCore BigLinkBase BigLinkGlue L5Defs.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__L5Kn () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.Riscv.Instr."; "LinuxProcessSemantics.Riscv.Sem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AxSymExec3.AX2."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AxSymExec3Sound.AX2S."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AxSymRun3."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.BigLinkBase.BL."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs.L5."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Kn.L5K."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SegPlan.SGP."; "Stdlib.Arith.PeanoNat.Nat."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1Some"; "1bool"; "1cons"; "1false"; "1list"; "1nat"; "1nil"; "1option"; "1pair"; "1prod"; "1true"; "2and"; "2eq"; "2ex"; "2not"; "2or"]; ["3Z"; "0E"; "0E'"; "0F"; "4ALU_AND"; "5alu64"; "0M"; "0M'"; "6EAlu"; "6ELit"; "6KAlign"; "6KDisj"; "6KImg"; "6KRange"; "6KUnk"; "6KWord"]; ["6KWr"; "6SA"; "6adenot"; "6edenot"; "6env"; "6ev"; "6evars_lt"; "6expr"; "7estart"; "7kentry_ok"; "8env_agree"; "8expr_vars_lt"; "9MM"; "9uv"; "9za"; "9zcomp"]; ["9zden"; ":defined"; ":img_clear"; ":u32_at"; ":u64_at"; ":u8_at"; ":writable"; ";zagree"; ";zpoly"; "<outside"; "<region"; "=eqb"; ">In"; ">existsb"; ">forallb"; "?add"]; ["?land"; "?le"; "?lt"; "?modulo"; "?pow"; "?testbit"; "0V"; "0a"; "0a1"; "0a2"; "0b"; "0b1"; "0b2"; "0e"; "0fb"; "0hi"]; ["0i"; "0l"; "0l1"; "0l2"; "0lo"; "0m"; "0n"; "0n1"; "0n1e"; "0n2"; "0n2e"; "0ne"; "0off"; "0off1"; "0off2"; "0segs"]; ["@Z_to_bv"; "@bv"; "@bv_unsigned"; "0t"; "0v"; "0x"; "0z"; "0zz"]]).
Local Ltac lia := L5FastLia.plia.
Module L5K.
Fixpoint zpoly (V : nat -> Z) (e : expr) : option Z :=
match e with
| ELit z => Some z
| EVar n => Some (V n)
| EAlu ALU_ADD a b => match zpoly V a, zpoly V b with Some x, Some y => Some (x + y) | _, _ => None end
| EAlu ALU_SUB a b => match zpoly V a, zpoly V b with Some x, Some y => Some (x - y) | _, _ => None end
| EMd M_MUL a b => match zpoly V a, zpoly V b with Some x, Some y => Some (x * y) | _, _ => None end
| _ => None
end.
Fixpoint zagree (E : env) (V : nat -> Z) (e : expr) : Prop :=
match e with
| ELit _ => True
| EVar n => bv_unsigned (ev E n) = V n
| EAlu _ a b | EMd _ a b => zagree E V a /\ zagree E V b
| _ => True
end.
Lemma MMpos : ltac2:(TCodec.tc2 tcn__L5Kn "4&R2z&Q<%3221"). Proof. unfold BL.MM. lia. Qed.
Lemma zpoly_sound : ltac2:(TCodec.tc2 tcn__L5Kn "Q2'Q4'5'@p021'Q7&QGr4r3r2%43321'<'7%11:&QH%1287(0%12>8%73531&S2yR0&Q3r6%221@%5241&R3&Q<%22C1%A3I41p0;1p0D1pV@L1pTLK1pT>M1pQ4Q11").
Proof. intros E V e.
induction e; intros zz HA HZ; cbn [zpoly zagree] in HA, HZ; try discriminate; cbn [edenot].
- inversion HZ; subst. rewrite Z_to_bv_unsigned. reflexivity.
- inversion HZ; subst. rewrite <- HA. symmetry. apply Z.mod_small. apply (BL.bvu_range (ev E n)).
- destruct HA as [Ha Hb].
destruct op; try discriminate;
destruct (zpoly V e1) as [x|] eqn:E1; try discriminate; destruct (zpoly V e2) as [y|] eqn:E2; try discriminate;
inversion HZ; subst; cbn [alu64 alu];
[ rewrite bv_add_unsigned | rewrite bv_sub_unsigned ];
unfold bv_wrap; change (bv_modulus 64) with BL.MM;
rewrite (IHe1 x Ha eq_refl), (IHe2 y Hb eq_refl).
+ rewrite <- Z.add_mod by (unfold BL.MM; lia). reflexivity.
+ rewrite <- Zminus_mod. reflexivity.
- destruct HA as [Ha Hb].
destruct op; try discriminate.
destruct (zpoly V e1) as [x|] eqn:E1; try discriminate; destruct (zpoly V e2) as [y|] eqn:E2; try discriminate.
inversion HZ; subst. cbn [mul_div]. rewrite bv_mul_unsigned. unfold bv_wrap; change (bv_modulus 64) with BL.MM.
rewrite (IHe1 x Ha eq_refl), (IHe2 y Hb eq_refl). rewrite <- Z.mul_mod by (unfold BL.MM; lia). reflexivity.
Qed.
Lemma zpoly_val : ltac2:(TCodec.tc2 tcn__L5Kn "Q6'Q4'5'@p021'Q7&QGr5r4r3%43321'<'7%11:&QH%1287(0%12>8%73531&R3&Q<%22=1%;3C1=&S2yR0&Q3r8r6%3221%6251%C3K1Fp091p0>1p0G1pV:O1pV>Q01pTLO1pT>Q11pQ4Q51").
Proof. intros E V e z v. intros HA HZ Hv. rewrite (zpoly_sound E V e z HA HZ). exact Hv. Qed.
Lemma zpoly_word : ltac2:(TCodec.tc2 tcn__L5Kn "Q8'Q4'5'@p021'Q7&QGr5r4r3%43321'<'7%11:&QH%1287(0%12>8%73531&R3&Q<%22=1%;3C1='S1yR0%211&Q3r8r6%3221&S0%127G%E3731p0;1p0@1p0I1pV:Q11pV>Q21pTLQ11pT>Q31pQ4Q71").
Proof. intros E V e z v. intros HA HZ Hv. apply BG.word_of_unsigned. eapply zpoly_val; eauto. Qed.
Lemma zagree_all : ltac2:(TCodec.tc2 tcn__L5Kn "H'Q4'5'@pV<21'Q7'<&S2yR0&Q5r4r1%3221%6251r3%114%:3=31pU>?1&QGr2%23:61p041pTLA1pT>C1pQ4G1").
Proof. intros E V e. intros H. induction e; cbn [zagree]; auto. Qed.
Lemma zagree_lt : ltac2:(TCodec.tc2 tcn__L5Kn "N'Q4'5'@p021'Q7&Q:r2r5r4%43321&QGr6%23146'<'1&Q;r3%2291(:%63521r7%;31:=p031p0;1p0?1pTLE1pTFI1pT>H1pQ6L1pQ4M1").
Proof. intros E E' V b e.
intros HA. induction e; cbn [zagree expr_vars_lt]; intros HZ HV; auto.
- apply Nat.ltb_lt in HV. rewrite <- (proj1 HA n HV). exact HZ.
- apply andb_prop in HV. destruct HV, HZ. split; auto.
- apply andb_prop in HV. destruct HV, HZ. split; auto.
Qed.
Section WithSegs.
Variable segs : list Segment.
Lemma estart_e : ltac2:(TCodec.tc2 tcn__L5Kn "F'Q4'Q7'@'<&Q8r3(Q1r2r1%3221%6251&QO&S2yR0&Q3%12:8%4231%6219%?3@81pUJA1pTFC1pQ4E1").
Proof. intros E b off. reflexivity. Qed.
Lemma adenot_e : ltac2:(TCodec.tc2 tcn__L5Kn "J'Q4'Q7'@'<'S1yR0%211&Q2r3(Q1r2r1%3221%6251&S0&QO&S2&Q3%12:8%32>1%5219%72@1%C3@91pUJE1pTFG1pQ4I1").
Proof. intros E b off. reflexivity. Qed.
Lemma kentry_KRange : ltac2:(TCodec.tc2 tcn__L5Kn "Q;'Q4'S1yR0%211'7y8%511%311p051'Q7'@'<&S2&Q3r6r4%3221%52?1r1%83921';&R1r2%2281r3%4231%6231&Q9vROr8r7(Mr5%23C1B%746541p091p0A1pV:K1pU0L1pU:M1pTLO1pQ>Q11pQ4Q:1").
Proof. intros E M e lo hi v. intros Hv Hr. cbn [kentry_ok]. rewrite Hv. lia. Qed.
Lemma and_lit_val : ltac2:(TCodec.tc2 tcn__L5Kn "Q1'S1yR0%211'@';&R1zr1%3221&R2&R4+2+R0%3221%5271%;271'<&S2&E(Dr3&S0r2%22F1%63541%82H1&R0%:2J7%2216%=3J41p0?1pU<L1pV<N1").
Proof. intros x m. intros Hm. cbn [alu64 alu]. rewrite bv_and_unsigned, BG.unsigned_lit by lia. reflexivity. Qed.
Lemma kentry_KRange_andlit : ltac2:(TCodec.tc2 tcn__L5Kn "QN'Q4'S1yR0%211'7y8%511%311p051'Q7'@'<&S2&Q3r7r5%3221%52?1r1%83921';&R1z%2218&R2&R4+2+R0%3221%52>1%:271&R0r3r6%3221%>2D1r4%@231%B231&Q9vROr:r9(M(H(Dr8(I%11Q2%53431%731AQ3%<4;:91p0>1p0G1p0Q31pV:Q=1pU0Q>1pU:Q?1pU<Q@1pTLQB1pQ>QD1pQ4QM1").
Proof. intros E M e m lo hi v. intros Hv Hm Hr. cbn [kentry_ok edenot]. rewrite and_lit_val by exact Hm. rewrite Hv. lia. Qed.
Lemma land1_bit0_false : ltac2:(TCodec.tc2 tcn__L5Kn "D'@&R1zr1%3221'<'1&R5r2%2217(3%63521&R0r3+1%3221%;3@1>p061p0>1pTNC1").
Proof. intros fb.
intros Hfb B0. apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
destruct (Z.eq_dec i 0) as [->|Hi0]. rewrite B0. reflexivity.
replace (Z.testbit 1 i) with false by (symmetry; apply Z.bits_above_log2; cbn; lia). apply Bool.andb_false_r.
Qed.
Lemma land1_bit0_true : ltac2:(TCodec.tc2 tcn__L5Kn "D'@&R1zr1%3221'<'1&R5r2%2217(:%63521&R0r3+1%3221%;3@12p061p0>1pTNC1").
Proof. intros fb.
intros Hfb B0. apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec.
destruct (Z.eq_dec i 0) as [->|Hi0]. rewrite B0. reflexivity.
replace (Z.testbit 1 i) with false by (symmetry; apply Z.bits_above_log2; cbn; lia). rewrite Bool.andb_false_r. reflexivity.
Qed.
Lemma land2_bit1_false : ltac2:(TCodec.tc2 tcn__L5Kn "E'@&R1zr1%3221'<'1&R5r2+1%3221(3%73621&R0r3+2%3221%<3A1?p061p0?1pTND1").
Proof. intros fb.
intros Hfb B1. apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
destruct (Z.eq_dec i 1) as [->|Hi1]. rewrite B1. reflexivity.
replace (Z.testbit 2 i) with false. apply Bool.andb_false_r.
destruct (Z.eq_dec i 0) as [->|Hi0]. reflexivity. symmetry. apply Z.bits_above_log2; cbn; lia.
Qed.
Lemma land2_bit1_true : ltac2:(TCodec.tc2 tcn__L5Kn "E'@&R1zr1%3221'<'1&R5r2+1%3221(:%73621&R0r3+2%3221%<3A12p061p0?1pTND1").
Proof. intros fb.
intros Hfb B1. apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec.
destruct (Z.eq_dec i 1) as [->|Hi1]. rewrite B1. reflexivity.
replace (Z.testbit 2 i) with false. rewrite Bool.andb_false_r. reflexivity.
destruct (Z.eq_dec i 0) as [->|Hi0]. reflexivity. symmetry. apply Z.bits_above_log2; cbn; lia.
Qed.
Lemma land_le_r : ltac2:(TCodec.tc2 tcn__L5Kn "A'@&R1zr2%3221';&R0r4r3%3221%9281%:223%7221p091p0:1pU<?1pT@@1").
Proof. intros a m.
intros Ha Hm. split. apply Z.land_nonneg. left; exact Ha.
pose proof (Z.lor_ldiff_and m a) as E1. pose proof (Z.add_lor_land (Z.ldiff m a) (Z.land m a)) as E2.
assert (Z0: Z.land (Z.ldiff m a) (Z.land m a) = 0).
{ rewrite (Z.land_comm m a). rewrite Z.land_assoc. rewrite Z.land_ldiff. apply Z.land_0_l. }
assert (D0: 0 <= Z.ldiff m a). { apply Z.ldiff_nonneg. left; exact Hm. }
rewrite Z.land_comm. lia.
Qed.
Lemma land_even_bit0 : ltac2:(TCodec.tc2 tcn__L5Kn "B'@'<'1&R5r1z%3221(3%73621&R0r3r2%3221%:218%=3<17p071pU<@1pT@A1").
Proof. intros a m. intros H. rewrite Z.land_spec, H. apply Bool.andb_false_r. Qed.
Lemma kentry_KAlign : ltac2:(TCodec.tc2 tcn__L5Kn "Q;'Q4'S1yR0%211'7y8%511%311p051'Q7'@'<&S2&Q3r5r3%3221%52?1r1%83921&R2z%2217&R3r4%22:1%?3@15&Q9vROr8r7(Jr6%221C%746541p091p0>1p0B1pV:L1pU<M1pTLO1pQ>Q11pQ4Q:1").
Proof. intros E M e m v. intros Hv Hm H0. cbn [kentry_ok]. rewrite Hv. auto. Qed.
Lemma kentry_KWr : ltac2:(TCodec.tc2 tcn__L5Kn "R4'Q4'S1yR0%211'7y8%511%311p051'Q7'@'<&S2&Q3r7r5%3221%52?1r2%83921r8r4%9221%;2E1%=3>16&R1z&QOr6%2281%5241&R2%126;%625=%721C&R4+2+R0%3221%>251&QFvROr;r9%A2N1%54431A&Q9r=r<(Q0(Q1r:%22:1%421:%84=761p0:1p0A1p0I1p0L1p0Q31p0Q91pU>QC1pT@QD1pUHQF1pUJQF1pTFQH1pQ>QJ1pQ4R31").
Proof. intros E M b off ne a n.
intros Ha Hn H1 H2 H3 Hw. cbn [kentry_ok]. unfold flat, elenZ. rewrite estart_e, Ha, Hn.
split. lia. intros d m Hd Hm. apply Hw; lia.
Qed.
Lemma kentry_KUnk : ltac2:(TCodec.tc2 tcn__L5Kn "R4'Q4'S1yR0%211'7y8%511%311p051'Q7'@'<&S2&Q3r7r5%3221%52?1r2%83921r8r4%9221%;2E1%=3>16&R1z&QOr6%2281%5241&R2%126;%625=%721C&R4+2+R0%3221%>251&QAr;r9%@2M1%4331@&Q9vROr=r<(N(Q1r:%22;1%421;%948761p0;1p0A1p0I1p0L1p0Q31p0Q91pU>QC1pT@QD1pUHQF1pUJQF1pTFQH1pQ>QJ1pQ4R31").
Proof. intros E M b off ne a n.
intros Ha Hn H1 H2 H3 Hd. cbn [kentry_ok]. unfold flat, elenZ. rewrite estart_e, Ha, Hn.
split. lia. intros i Hi. apply Hd. lia.
Qed.
Lemma kentry_KDisj : ltac2:(TCodec.tc2 tcn__L5Kn "R;'Q4'S1yR0%211'7y8%511%311p051'Q7'@'<&S2&Q3r<r:%3221%52?1r4%83921r=r9%9221%;2E1%=3>16r>%=215%?2I1%A3B1:r?r8%B221%D2N1%F3G1?'?&R1&QO%127Ar7%3221r6%521J%7231r5%8231%:218%<241&Q9vROrAr@(K(Q1%12HLr;%32Q91%543Q41Q9%:49871p0<1p0J1p0Q01p0Q51p0Q;1pUDQE1pTDQF1pU@QG1pTBQH1pUFQJ1pUNQJ1pTJQL1pUBQM1pULQM1pTHQO1pQ>R11pQ4R:1").
Proof. intros E M b1 off1 n1e b2 off2 n2e a1 n1 a2 n2.
intros Ha1 Hn1 Ha2 Hn2 Hd. cbn [kentry_ok]. unfold elenZ. rewrite !estart_e, Ha1, Ha2, Hn1, Hn2. exact Hd.
Qed.
Lemma kentry_KWord8 : ltac2:(TCodec.tc2 tcn__L5Kn "R2'Q4'S1yR0%211'7y8%511%311p051'Q7'@'<&S2&Q3r7r5%3221%52?1r2%83921r8r4%9221%;2E1%=3>16&R1z&QOr6%2281%5241%42@A+8%6221&R4+2+R0%3221%=251&QDvROr:%?2>F%44321L&Q9r<r;(O(Q1r9%2291u8%5321Q0%94=871p0;1p0A1p0J1p0Q11p0Q71pV:QA1pT@QB1pTLQD1pUJQD1pTFQF1pQ>QH1pQ4R11").
Proof. intros E M b off e a v.
intros Ha Hv H1 H2 Hu. cbn [kentry_ok]. split. lia. split.
- unfold flat. rewrite estart_e, Ha. lia.
- rewrite adenot_e, Ha. rewrite (BG.word_of_unsigned _ _ Hv). exact Hu.
Qed.
Lemma kentry_KWord1 : ltac2:(TCodec.tc2 tcn__L5Kn "R:'Q4'S1yR0%211'7y8%511%311p051'Q7'@'<&S2&Q3r7r5%3221%52?1r2%83921r8r4%9221%;2E1%=3>16&R1z&QOr6%2281%5241%42@A+1%6221&R4+2+R0%3221%=251';%?2>I&R2+X0%22L1%5241&QEvROr;r9%F2Q31%54431F&Q9r=r<(O(Q1r:%22:1u1%5321;%94>871p0;1p0B1p0I1p0Q21p0Q91p0Q?1pV:QI1pT@QJ1pTLQL1pUJQL1pTFQN1pQ>R01pQ4R91").
Proof. intros E M b off e a v.
intros Ha Hv H1 H2 Hr Hu. cbn [kentry_ok]. split. lia. split.
- unfold flat. rewrite estart_e, Ha. lia.
- rewrite adenot_e, Ha. rewrite (BG.word_of_unsigned _ _ Hv). rewrite BG.word_to_le_bytes_1 by exact Hr. exact Hu.
Qed.
Lemma kentry_KWord4 : ltac2:(TCodec.tc2 tcn__L5Kn "R2'Q4'S1yR0%211'7y8%511%311p051'Q7'@'<&S2&Q3r7r5%3221%52?1r2%83921r8r4%9221%;2E1%=3>16&R1z&QOr6%2281%5241%42@A+4%6221&R4+2+R0%3221%=251&QCvROr:%?2>F%44321L&Q9r<r;(O(Q1r9%2291u4%5321Q0%94=871p0;1p0A1p0J1p0Q11p0Q71pV:QA1pT@QB1pTLQD1pUJQD1pTFQF1pQ>QH1pQ4R11").
Proof. intros E M b off e a v.
intros Ha Hv H1 H2 Hu. cbn [kentry_ok]. split. lia. split.
- unfold flat. rewrite estart_e, Ha. lia.
- rewrite adenot_e, Ha. rewrite (BG.word_of_unsigned _ _ Hv). exact Hu.
Qed.
Lemma kentry_KImg : ltac2:(TCodec.tc2 tcn__L5Kn "Q6'Q4'S1yR0%211'7y8%511%311p051'@&R1zr2%3221&R4+2+R0%3221%8261&QBr5r4r3%43321&Q9vROr7r6(L%1298%645431p081p0>1p0D1pU0I1pU:J1pQ>L1pQ4Q51").
Proof. intros E M lo hi. intros H1 H2 H. cbn [kentry_ok]. repeat split; auto. Qed.
Lemma u64_of_KWord8 : ltac2:(TCodec.tc2 tcn__L5Kn "QA'Q4'S1yR0%211'7y8%511%311p051'Q7'@&Q9vROr7r6(O(Q1r5r4%3221u8r3%73321%<4;:91'<&S2&Q3r8%221>%42K1%63D19r9%621?%82O1%:3H1=&QD&QO%12DH%34J71Dp051p0:1p0B1pV:Q01pT@Q11pTLQ31pUJQ31pTFQ51pQ>Q71pQ4Q@1").
Proof. intros E M b off e a v.
intros K Ha Hv. cbn [kentry_ok] in K. destruct K as (_ & _ & Rd). unfold L5.u64_at.
rewrite adenot_e, Ha in Rd. rewrite <- (BG.word_of_unsigned _ _ Hv). exact Rd.
Qed.
Lemma u64_of_KWord8_ex : ltac2:(TCodec.tc2 tcn__L5Kn "QL'Q4'S1yR0%211'7y8%511%311p051'Q7'@&Q9vROr6r5(O(Q1r4r3%3221u8r2%73321%<4;:91'<&S2&Q3r7%221>%42K1%63D19'=';&R1zr1%3221&R2&R4+2+R0%3221%5271%;271&QDr8&QO%12NQ2%44Q431=%A261qV:Q81%D2Q91p0F1p0N1pT@Q<1pTLQ>1pUJQ>1pTFQ@1pQ>QB1pQ4QK1").
Proof. intros E M b off e a.
intros K Ha. exists (bv_unsigned (edenot E e)). split. apply (BL.bvu_range (edenot E e)).
eapply u64_of_KWord8; eauto.
Qed.
Lemma u32_of_KWord4 : ltac2:(TCodec.tc2 tcn__L5Kn "QA'Q4'S1yR0%211'7y8%511%311p051'Q7'@&Q9vROr7r6(O(Q1r5r4%3221u4r3%73321%<4;:91'<&S2&Q3r8%221>%42K1%63D19r9%621?%82O1%:3H1=&QC&QO%12DH%34J71Dp051p0:1p0B1pV:Q01pT@Q11pTLQ31pUJQ31pTFQ51pQ>Q71pQ4Q@1").
Proof. intros E M b off e a v.
intros K Ha Hv. cbn [kentry_ok] in K. destruct K as (_ & _ & Rd). unfold L5.u32_at.
rewrite adenot_e, Ha in Rd. rewrite <- (BG.word_of_unsigned _ _ Hv). exact Rd.
Qed.
Lemma u8_of_KWord1 : ltac2:(TCodec.tc2 tcn__L5Kn "QK'Q4'S1yR0%211'7y8%511%311p051'Q7'@&Q9vROr7r6(O(Q1r5r4%3221u1r3%73321%<4;:91'<&S2&Q3r8%221>%42K1%63D19r9%621?%82O1%:3H1=';&R1z%221D&R2+X0%22G1%7241&QEr:&QO%12Q0C%44Q331Np061p0?1p0D1p0L1pV:Q:1pT@Q;1pTLQ=1pUJQ=1pTFQ?1pQ>QA1pQ4QJ1").
Proof. intros E M b off e a v.
intros K Ha Hv Hr. cbn [kentry_ok] in K. destruct K as (_ & _ & Rd). unfold L5.u8_at.
rewrite adenot_e, Ha in Rd. rewrite (BG.word_of_unsigned _ _ Hv) in Rd. rewrite BG.word_to_le_bytes_1 in Rd by exact Hr. exact Rd.
Qed.
Lemma defined_of_KUnk : ltac2:(TCodec.tc2 tcn__L5Kn "Q@'Q4'S1yR0%211'7y8%511%311p051'Q7'@&Q9vROr7r6(N(Q1r5r4%3221r3%6221%;4:981'<&S2&Q3r8%221=%42J1%63C19r9%621>%82N1%:3G1=&QA&QO%12CG%3371Cp051p0:1p0B1pU>O1pT@Q01pUHQ21pUJQ21pTFQ41pQ>Q61pQ4Q?1").
Proof. intros E M b off ne a n.
intros K Ha Hn. cbn [kentry_ok] in K. destruct K as [_ D]. unfold elenZ in D. rewrite estart_e, Ha, Hn in D.
intros i Hi. apply D. exact Hi.
Qed.
Lemma range_of_KRange : ltac2:(TCodec.tc2 tcn__L5Kn "Q9'Q4'S1yR0%211'7y8%511%311p051'Q7'@&Q9vROr6r5(Mr4r3r2%43321%948761'<&S2&Q3r7%221;%42H1%63A19';&R1%12@=%22>?%4221p061p0>1pV:I1pU0J1pU:K1pTLM1pQ>O1pQ4Q81").
Proof. intros E M e lo hi v. intros K Hv. cbn [kentry_ok] in K. rewrite Hv in K. exact K. Qed.
Lemma u64_at_keep : ltac2:(TCodec.tc2 tcn__L5Kn "R2'S1yR0%211'7y8%511%311pV<51'@&>';&R1r5&S2r1%22>1%5241&R2r4%2241%:241%<11'<r7r2%211r8%113%63F31p081pV<L1'?&QOr3+8%3221%I21H%J2C4%K2DJ%8221%9241z%O21H%;2O9&R4+2+R0%3221%Q5251&QDvROr:r6%44321Q9%5443O2p021p081p0?1p0B1p0M1pV:QD1pT@QE1pU0QF1pU:QG1pQ@QI1pQ>QJ1").
Proof. intros M M' lo hi a v.
intros HF Hap Ha H8 Hu. eapply (L5.u64_at_frame segs M M' [(lo, hi - lo)]). 2: exact Ha. 2: exact H8. 3: exact Hu.
- intros x Hx. apply HF. intros Hin. apply (Hx (lo, hi - lo)). left; reflexivity. unfold L5.in_rng. cbn. lia.
- intros i Hi r [<-|[]]. unfold L5.in_rng. cbn. lia.
Qed.
Lemma u8_at_keep : ltac2:(TCodec.tc2 tcn__L5Kn "R2'S1yR0%211'7y8%511%311pV<51'@&>';&R1r5&S2r1%22>1%5241&R2r4%2241%:241%<11'<r7r2%211r8%113%63F31p081pV<L1'?&QOr3+1%3221%I21H%J2C4%K2DJ%8221%9241z%O21H%;2O9&R4+2+R0%3221%Q5251&QEvROr:r6%44321Q9%5443O2p021p081p0?1p0B1p0M1pV:QD1pT@QE1pU0QF1pU:QG1pQ@QI1pQ>QJ1").
Proof. intros M M' lo hi a v.
intros HF Hap Ha H1 Hu. eapply (L5.u8_at_frame segs M M' [(lo, hi - lo)]). 2: exact Ha. 2: exact H1. 3: exact Hu.
- intros x Hx. apply HF. intros Hin. apply (Hx (lo, hi - lo)). left; reflexivity. unfold L5.in_rng. cbn. lia.
- intros r [<-|[]]. unfold L5.in_rng. cbn. lia.
Qed.
Lemma outside_cons_e : ltac2:(TCodec.tc2 tcn__L5Kn "R0'Q4'Q7'@'4&QJ%211'S1yR0%211'<&S2&Q3r8r7%3221%5281r2%83?21r9r6%9221%;2>1%=3D16&>';&R1&QOr4%221@r5%D2G1%6231&R2r3%8261%3251%<251%>11&QIr;%231KEr<(2'9%12Q;Q:%221Q<(8r:%24Q?Q>91%345Q@1O%8351Q6%=3:1Q6p0<1p0@1p0Q01p0Q61pU>QF1pT@QG1pV<QB1pQ8QF1pUHQK1pUJQK1pTFQM1pQ4QO1").
Proof. intros E b off ne F x a n.
intros Ha Hn Hx HF. constructor. 2: exact HF. unfold estart, elenZ. cbn [a_base a_off]. rewrite Ha, Hn. lia.
Qed.
Lemma outside_nil_e : ltac2:(TCodec.tc2 tcn__L5Kn "='Q4'S1yR0%211&QIr2(6&QJ%211r1%63521pV<81pQ4<1").
Proof. intros E x. constructor. Qed.
End WithSegs.
Lemma In_of_existsb : ltac2:(TCodec.tc2 tcn__L5Kn "C'5'4%112'<'1&QM&QKr2%211r1%53:21(:%93821&QLr3%23?18p041pU4?1pU2B1").
Proof. intros i l. induction l as [|x l IH]; cbn; intros H. discriminate. apply Bool.orb_prop in H. destruct H as [H|H]. left. apply Nat.eqb_eq in H. lia. right. apply IH. exact H. Qed.
Lemma incl_b : ltac2:(TCodec.tc2 tcn__L5Kn "I'4'5%211'<'1&QN&QM&QKr1%211r2%53:21qU2;1%83<13(:%<3;21&QLr4%23A:1%33B92p021pU2D1p071pU8E1pU6F1").
Proof. intros l1 l2. intros H i Hi. rewrite forallb_forall in H. apply In_of_existsb. apply H. exact Hi. Qed.
Lemma in_b : ltac2:(TCodec.tc2 tcn__L5Kn "C'5'4%112'<'1&QM&QKr2%211r1%53:21(:%93821&QLr3%23?18p041pU4?1pU2B1").
Proof. intros i l. apply In_of_existsb. Qed.
Lemma nth_error_single {A} (x y : A) i : nth_error [x] i = Some y -> y = x.
Proof. intros H. destruct i as [|i]; cbn in H; [inversion H; auto | destruct i; discriminate]. Qed.
Lemma nth_error_pair {A} (x y z : A) i : nth_error [x; y] i = Some z -> (i = 0%nat /\ z = x) \/ (i = 1%nat /\ z = y).
Proof. intros H. destruct i as [|[|i]]; cbn in H; [inversion H; auto | inversion H; auto | destruct i; discriminate]. Qed.
Ltac zrange_tac :=
first [ apply BL.bvu_range | unfold BL.MM; lia
| lazymatch goal with
| |- context [getr] => fail
| |- context [bv_unsigned] => fail
| |- 0 <= ?z < _ => let v := eval vm_compute in z in
lazymatch v with Z0 => idtac | Zpos _ => idtac end;
change z with v; unfold BL.MM; lia
end ].
Ltac mod_small_tac := rewrite Z.mod_small; [| zrange_tac ].
Ltac solve_mod :=
first [ mod_small_tac; first [reflexivity | lia]
| symmetry; eapply (Z.mod_unique_pos _ _ (-1)); unfold BL.MM; lia
| symmetry; eapply (Z.mod_unique_pos _ _ 1); unfold BL.MM; lia ].
Ltac norm_expr :=
lazymatch goal with
| |- bv_unsigned (edenot _ ?e) = _ => let e' := eval vm_compute in e in change e with e'
| |- edenot _ ?e = _ => let e' := eval vm_compute in e in change e with e'
| _ => idtac
end.
Ltac evalE ZA :=
norm_expr; eapply zpoly_val;
[ apply (zagree_all _ _ _ ZA) | cbn [zpoly]; reflexivity | solve_mod ].
Ltac evalE' ZA AG :=
norm_expr; eapply zpoly_val;
[ eapply (zagree_lt _ _ _ _ _ AG); [apply (zagree_all _ _ _ ZA) | vm_compute; reflexivity]
| cbn [zpoly]; reflexivity | solve_mod ].
Ltac wordE ZA := apply BG.word_of_unsigned; evalE ZA.
Ltac wordE' ZA AG := apply BG.word_of_unsigned; evalE' ZA AG.
Ltac slot ZA := first [ assumption | reflexivity | (etransitivity; [eassumption|]; symmetry; wordE ZA) ].
Ltac kn_mem :=
rewrite ?Z.add_0_r;
first [ eassumption
| match goal with H : L5.u64_at _ ?M ?a' ?v' |- L5.u64_at _ ?M ?a ?v =>
replace a with a' by lia; replace v with v' by lia; exact H end
| match goal with H : L5.u8_at _ ?M ?a' ?v' |- L5.u8_at _ ?M ?a ?v =>
replace a with a' by lia; replace v with v' by lia; exact H end
| match goal with H : L5.u32_at _ ?M ?a' ?v' |- L5.u32_at _ ?M ?a ?v =>
replace a with a' by lia; replace v with v' by lia; exact H end
| match goal with H : L5.defined ?M ?a' ?n' |- L5.defined ?M ?a ?n =>
apply (L5.defined_sub M a' n' a n H); lia end
| match goal with H : L5.writable _ ?M ?a' ?n' |- L5.writable _ ?M ?a ?n =>
apply (L5.writable_sub _ M a' n' a n H); lia end
| idtac ].
Ltac kn1 ZA :=
lazymatch goal with
| |- kentry_ok _ _ _ (KRange (EAlu ALU_AND _ (ELit _)) _ _) =>
eapply kentry_KRange_andlit; [evalE ZA | lia | first [lia | rewrite land1_bit0_false by (first [assumption|lia]); lia
| rewrite land1_bit0_true by (first [assumption|lia]); lia
| rewrite land2_bit1_false by (first [assumption|lia]); lia
| rewrite land2_bit1_true by (first [assumption|lia]); lia | idtac] ]
| |- kentry_ok _ _ _ (KRange _ _ _) => eapply kentry_KRange; [evalE ZA | lia]
| |- kentry_ok _ _ _ (KAlign _ _) => eapply kentry_KAlign; [evalE ZA | lia | first [assumption | lia | idtac]]
| |- kentry_ok _ _ _ (KWr _ _) => eapply kentry_KWr; [evalE ZA | evalE ZA | lia | lia | lia | kn_mem]
| |- kentry_ok _ _ _ (KUnk _ _) => eapply kentry_KUnk; [evalE ZA | evalE ZA | lia | lia | lia | kn_mem]
| |- kentry_ok _ _ _ (KDisj _ _ _ _) => eapply kentry_KDisj; [evalE ZA | evalE ZA | evalE ZA | evalE ZA | lia]
| |- kentry_ok _ _ _ (KWord _ 8 _) => eapply kentry_KWord8; [evalE ZA | evalE ZA | lia | lia | kn_mem]
| |- kentry_ok _ _ _ (KWord _ 1 _) => eapply kentry_KWord1; [evalE ZA | evalE ZA | lia | lia | lia | kn_mem]
| |- kentry_ok _ _ _ (KWord _ 4 _) => eapply kentry_KWord4; [evalE ZA | evalE ZA | lia | lia | kn_mem]
| |- kentry_ok _ _ _ (KImg _ _) => eapply kentry_KImg; [lia | lia | first [eassumption | idtac]]
end.
Ltac kn_all ZA :=
lazymatch goal with
| |- Forall _ (_ :: _) => apply Forall_cons; [kn1 ZA | kn_all ZA]
| |- Forall _ [] => apply Forall_nil
| |- Forall _ _ => idtac
end.
Lemma zc_sound : ltac2:(TCodec.tc2 tcn__L5Kn "Q1'Q4'Q7'Q>'@'<'7%114&Q?r3%211(0r2%22:1%93741&Q@&Q=r5%211%421:%?3@18&S2yR0&Q3r6%2218%5241%F3G1Bp081p0?1pV:J1pV8L1pTLN1pQ4Q01").
Proof. intros E e t v. intros Ht Hv. rewrite (BL.zcomp_sound E e t Ht). exact Hv. Qed.
Lemma zc_sound' : ltac2:(TCodec.tc2 tcn__L5Kn "Q>'5'Q4'Q7'Q>'@&Q:r6r5r4%43321'<'1&Q6r7%2216(:%63521'7%11?&Q?%11=(0%12C>%=3531&Q@&Q=r8%211%421E%C3I1E&S2yR0&Q3%127D%4231%I3O1Lp071p0>1p0F1p0N1pV:Q41pV8Q61pTLQ81pQ6Q:1pQ4Q;1pTFQ=1").
Proof. intros b E E' e t v.
intros AG Hb Ht Hv. rewrite (BL.zcomp_sound E' e t Ht). rewrite <- (BL.zden_agree b (BL.uv E) (BL.uv E') e t). exact Hv.
intros n Hn. unfold BL.uv. rewrite (proj1 AG n Hn). reflexivity. exact Hb. exact Ht.
Qed.
Ltac evalB ZA :=
lazymatch goal with |- bv_unsigned (edenot _ ?e) = _ =>
let t := eval vm_compute in (BL.zc e) in
eapply (zc_sound _ e t); [vm_compute; reflexivity | cbn [BL.zden]; unfold BL.uv; rewrite ?ZA; unfold BL.MM] end.
Ltac evalB' ZA AG :=
lazymatch goal with |- bv_unsigned (edenot _ ?e) = _ =>
let t := eval vm_compute in (BL.zc e) in
eapply (zc_sound' _ _ _ e t _ AG); [vm_compute; reflexivity | vm_compute; reflexivity | cbn [BL.zden]; unfold BL.uv; rewrite ?ZA; unfold BL.MM] end.
Ltac wordB ZA := apply BG.word_of_unsigned; evalB ZA.
Ltac wordB' ZA AG := apply BG.word_of_unsigned; evalB' ZA AG.
Ltac outsideF ZA AG := repeat (eapply outside_cons_e; [evalE' ZA AG | evalE' ZA AG | lia |]); apply outside_nil_e.
End L5K.
