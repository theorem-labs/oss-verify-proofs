(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec StoreOk HeapIface HeapIfaceA L5Defs L5Core PmLayout PmModel PmModelFacts HeapIfaceAJx PmSpecsA.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__PmModelFactsA () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIfaceA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Core.L5C."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmModel.PM."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmModelFactsA.PMFA.Agree."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecsA.PMSPA."; "Stdlib.ZArith.BinInt.Z."], [["0A"; "1list"; "2and"; "2eq"; "3Z"; "0M"; "0M'"; "4S"; "4aacc"; "5agree_on"; "6CHUNK"; "6VLong"; "6iosb_at"; "6iss_at"; "6nullis_at"; "6p_b"]; ["6p_k"; "6p_src"; "6p_tb"; "6parser_at"; "6pst"; "6pstate"; "6sr_qc"; "6src_fields_at"; "6srcst"; "6strm"; "6vec_at"; "6vstr"; "6vstr_at"; "7agA"; "7agsh"; "8accA"]; ["8annA"; "9add"; "9le"; "9modulo"; "9mul"; "9pow"; "0a"; "0a'"; "0b"; "0c"; "0isp"; "0j"; "0k"; "0n"; "0n'"; "0o"]; ["0ois"; "0op"; "0os"; "0p"; "0rdb"; "0s"; "0sbp"; "0segs"; "0sm"; "0src"; "0st"; "0stk"; "0str"; "0u"; "0v"; "0vp"]]).
Module PMFA.
Abbreviation accA := PMSPA.accA.
Abbreviation annA := PMSPA.annA.
Section Agree.
Variable segs : list Segment.
Variable A : pm_addrs.
Variables M M' : word -> option byte.
Abbreviation ag := (L5C.agree_on M M').
Definition agsh (a n : Z) : Prop := forall x, a <= x < a + n -> M' (Z_to_bv 64 (S x)) = M (Z_to_bv 64 (S x)).
Definition agA (a n : Z) : Prop := ag a n /\ agsh a n.
Lemma agsh_sub : ltac2:(TCodec.tc2 tcn__PmModelFactsA "E'4&Nr4r3%3221&Q2r5%2214&Q1%1276r6%3215%7231%<27;p021p081p0<1pRNA1pR@B1pRLC1pR>D1").
Proof. intros a n a' n'. intros H H1 H2 x Hx. apply H. lia. Qed.
Lemma agA_sub : ltac2:(TCodec.tc2 tcn__PmModelFactsA "E'4&Mr4r3%3221&Q2r5%2214&Q1%1276r6%3215%7231%<27;p021p081p0<1pRNA1pR@B1pRLC1pR>D1").
Proof. intros a n a' n'. intros [G S] H1 H2. split; [eapply (L5C.agree_on_sub M M' a n); [exact G|lia|lia] | exact (agsh_sub a n a' n' S H1 H2)]. Qed.
Lemma aacc_agree : ltac2:(TCodec.tc2 tcn__PmModelFactsA "@'4&Nr2r1%3221&8v5r3%33216v6r4%63214p041p091pRL>1pR>?1").
Proof. intros a n.
intros H C x Hx. unfold byte_at in *. rewrite (H x Hx). exact (C x Hx).
Qed.
Lemma accA_agree : ltac2:(TCodec.tc2 tcn__PmModelFactsA "@'4&Nr2r1%3221&Ov5r3%33216v6r4%63214p041p091pRL>1pR>?1").
Proof. intros a n. apply aacc_agree. Qed.
Lemma S_granule : ltac2:(TCodec.tc2 tcn__PmModelFactsA "I'4'3&Q3r2+8%3221z%63721&Q2%1236&Q1&7r4%211r3%5221&Q4%12=3%8261%811%C3D51p0<1p0?1pRHG1pRBH1").
Proof. intros b j. intros Hb Hj. unfold S. rewrite <- Z.add_assoc, (Z.add_comm SB j), Z.add_assoc. f_equal.
replace (b + 8 * j) with (j * 8 + b) by lia. rewrite Z.div_add_l by lia. lia. Qed.
Lemma annA_agree : ltac2:(TCodec.tc2 tcn__PmModelFactsA "Q2'4'3&Q3r3+8%3221z%63721'2&Q2%1247r2%3291%5231&Nr6r4%3221&Q0v5r7r5%443271v6r8%74215:p041p0:1p0E1p0@1p0G1pRDO1pSLQ01pRBQ11").
Proof. intros b u c.
intros Hb Hu Hc H [Z1 Z2].
assert (C8 : 8 * (c / 8) = c) by (pose proof (Z.div_mod c 8 ltac:(lia)); lia).
assert (U8 : u / 8 <= c / 8) by (apply Z.div_le_mono; lia).
split.
- intros j Hj. unfold byte_at in *. rewrite (S_granule b j Hb ltac:(lia)). rewrite H by lia.
rewrite <- (S_granule b j Hb ltac:(lia)). exact (Z1 j Hj).
- intros j Hj. unfold byte_at in *. rewrite (S_granule b j Hb ltac:(lia)). rewrite H by lia.
rewrite <- (S_granule b j Hb ltac:(lia)). exact (Z2 j Hj).
Qed.
Lemma mod16_8 : ltac2:(TCodec.tc2 tcn__PmModelFactsA ">'4'3&Q3r1+@%3221z%63721r2+8%8221%:3;15p051pRB=1").
Proof. intros b. intros H. apply Z.mod_divide in H; [|lia]. destruct H as [q ->]. replace (q * 16) with ((q * 2) * 8) by lia. apply Z_mod_mult. Qed.
Lemma blk8 : ltac2:(TCodec.tc2 tcn__PmModelFactsA "?'4'3&Q3&Q4+Q0&Q5+2r1%3221%6251+8%9221z%<3=21pRJ>1").
Proof. intros k. replace (32 * 2 ^ k) with ((4 * 2 ^ k) * 8) by lia. apply Z_mod_mult. Qed.
Ltac u64x AG H := apply (L5C.u64_at_agree segs M M'); [eapply (L5C.agree_on_sub M M'); [exact AG|lia|lia]|lia|lia|exact H].
Ltac u32x AG H := apply (PMF.u32_at_agree segs M M'); [eapply (L5C.agree_on_sub M M'); [exact AG|lia|lia]|lia|lia|exact H].
Ltac u8x AG H := apply (L5C.u8_at_agree segs M M'); [eapply (L5C.agree_on_sub M M'); [exact AG|lia|lia]|lia|lia|exact H].
Ltac defx AG H := apply (L5C.defined_agree M M' _ _); [eapply (L5C.agree_on_sub M M'); [exact AG|lia|lia]|exact H].
Ltac accx SH H := apply accA_agree; [eapply agsh_sub; [exact SH|lia|lia]|exact H].
Lemma vstr_at_agreeA : ltac2:(TCodec.tc2 tcn__PmModelFactsA "Q='4'K&Q2zr2%3221&Q1r3+H%3221&Q5+2+R0%3221%<251&Mr4%2219'3r7(;r1%23?B1%53F41%92D8p021pS8J1pRLK1pRDL1&LvQG&Ov5r6r5%6554321v6%85761B4p031p0;1p0G1p0K1p0Q51pS<Q:1pS0Q<1").
Proof. intros o s.
intros Ho Ho' [AG SH] AGB (D & C & H). split; [apply (L5C.defined_agree M M' o 24 AG D)|]. split; [accx SH C|].
destruct s as [n|c n p].
- destruct H as (Hn & B0). split; [exact Hn|]. u8x AG B0.
- destruct H as (W0 & W8 & W16 & Hn & Hc & He & DB & CB). destruct (AGB c n p eq_refl) as [AGp SHp].
split; [u64x AG W0|]. split; [u64x AG W8|]. split; [u64x AG W16|]. split; [exact Hn|]. split; [exact Hc|]. split; [exact He|].
split; [apply (L5C.defined_agree M M' p c AGp DB)|]. accx SHp CB.
Qed.
Section S.
Local Abbreviation SECT := (ltac2:(TCodec.tc2 tcn__PmModelFactsA "QG'4'1'E%211&Q2zr4%3221&Q1r5+H%3221&Q5+2+R0%3221%<251%=2<8r6&Q4+Q0%928<%3221%?251%D219&9v5v6r8%44321C&Mr7%D2C1%>2=1%4261&JvQG&O&Q0r:r9%68543?21=:r;%88765@143?p031p0;1p0A1p0G1p0O1p0Q11p0Q;1pSHQ@1pRJQD1pRBQE1pSNQF1")) (only parsing).
Variable v : ltac:(sec_ty2 constr:(SECT) 0%nat 0%nat).
Variable b : ltac:(sec_ty2 constr:(SECT) 1%nat 0%nat).
Variable k : ltac:(sec_ty2 constr:(SECT) 2%nat 0%nat).
Variable stk : ltac:(sec_ty2 constr:(SECT) 3%nat 0%nat).
Lemma vec_at_agreeA : ltac:(sec_stmt2 constr:(SECT) 4%nat 0%nat).
Proof.
intros Hv Hv' Hb Hb' AGV [AGB SHB] (V0 & V8 & V16 & Hk & Hlen & Hal & DB & CB & AN & EL).
pose proof (PM.pow2_pos k ltac:(lia)) as P2.
split; [u64x AGV V0|]. split; [u64x AGV V8|]. split; [u64x AGV V16|].
split; [exact Hk|]. split; [exact Hlen|]. split; [exact Hal|].
split; [apply (L5C.defined_agree M M' b _ AGB DB)|]. split; [accx SHB CB|].
split; [apply annA_agree; [exact (mod16_8 b Hal)| lia| apply blk8| exact SHB| exact AN]|].
intros n Hn. apply (PMF.pstate_at_agree segs M M'); [lia|lia| |apply EL; exact Hn].
assert (Z.of_nat n < Z.of_nat (length stk)) by (apply Nat2Z.inj_lt; exact Hn).
eapply (L5C.agree_on_sub M M' b (32 * 2 ^ k)); [exact AGB|lia|lia].
Qed.
End S.
Section S.
Local Abbreviation SECT := (ltac2:(TCodec.tc2 tcn__PmModelFactsA "Q3'4&Q2zr4%3221&Q1r5+TH%3221&Q5+2+R0%3221%<251&Mr6%2219&<vQGv0&Ov5r7%68543218ADv6r8%98876214;Dp041p0<1p0@1p0J1pSFO1pS:Q01pT0Q11pS0Q21")) (only parsing).
Variable o : ltac:(sec_ty2 constr:(SECT) 0%nat 0%nat).
Variable vp : ltac:(sec_ty2 constr:(SECT) 1%nat 0%nat).
Variable rdb : ltac:(sec_ty2 constr:(SECT) 2%nat 0%nat).
Variable st : ltac:(sec_ty2 constr:(SECT) 3%nat 0%nat).
Lemma iosb_at_agreeA : ltac:(sec_stmt2 constr:(SECT) 4%nat 0%nat).
Proof.
intros Ho Ho' [AG SH] (H0 & H32 & H36 & H40 & H48 & Z & D & C & ST).
split; [u64x AG H0|]. split; [u32x AG H32|]. split; [u32x AG H36|]. split; [u64x AG H40|]. split; [u64x AG H48|].
split; [apply (PMF.zeros_at_agree M M'); [eapply (L5C.agree_on_sub M M'); [exact AG|lia|lia]|exact Z]|]. split; [defx AG D|].
split; [accx SH C| exact ST].
Qed.
End S.
Lemma nullis_at_agreeA : ltac2:(TCodec.tc2 tcn__PmModelFactsA "Q0'4&Q2zr1%3221&Q1r2+W8%3221&Q5+2+R0%3221%<251&Mr3%2219&>vQGv0&Ov5r4%6554321v6r5%9587621p041p0<1p0@1p0J1pS0O1").
Proof. intros o.
intros Ho Ho' AGa (H0 & D & C & H16 & H24 & IOS). destruct AGa as [AG SH] eqn:EA.
split; [u64x AG H0|]. split; [defx AG D|]. split; [accx SH C|]. split; [u64x AG H16|]. split; [u64x AG H24|].
apply iosb_at_agreeA; [lia|lia| eapply agA_sub; [exact AGa|lia|lia]| exact IOS].
Qed.
Section S.
Local Abbreviation SECT := (ltac2:(TCodec.tc2 tcn__PmModelFactsA "QF'4'H&Q2zr4%3221&Q1r5+Y8%3221&Q5+2+R0%3221%<251&Fr3%211%@2?1%41?&:%?221%D219&Mr8+W@%D221+QH%5221r6%?11%821;&GvQG&Ov5r:r9r7%7765432?1v6r;%:7982165Bp041p0=1p0A1p0H1p0M1p0Q21p0Q<1pSDQA1pS>QC1pRFQD1pS6QE1")) (only parsing).
Variable os : ltac:(sec_ty2 constr:(SECT) 0%nat 0%nat).
Variable isp : ltac:(sec_ty2 constr:(SECT) 1%nat 0%nat).
Variable sbp : ltac:(sec_ty2 constr:(SECT) 2%nat 0%nat).
Variable src : ltac:(sec_ty2 constr:(SECT) 3%nat 0%nat).
Lemma src_fields_at_agreeA : ltac:(sec_stmt2 constr:(SECT) 4%nat 0%nat).
Proof.
intros Ho Ho' Hq Hq' [AG SH] [AGC SHC] (F1 & F2 & F3 & F4 & F5 & F6 & F7 & B1 & B2 & B3 & B4 & DC & CC & CS).
split; [u64x AG F1|]. split; [u64x AG F2|]. split; [defx AG F3|]. split; [u64x AG F4|]. split; [u64x AG F5|]. split; [u64x AG F6|]. split; [u64x AG F7|].
split; [exact B1|]. split; [exact B2|]. split; [exact B3|]. split; [exact B4|].
split; [apply (L5C.defined_agree M M' _ _ AGC DC)|]. split; [accx SHC CC| accx SH CS].
Qed.
End S.
Section S.
Local Abbreviation SECT := (ltac2:(TCodec.tc2 tcn__PmModelFactsA "QA'4'K'I&Q2zr3%3221&Q1r4+X@%3221&Q5+2+R0%3221%<251&Mr5%2219'3r8(;r2r1%33C21%63H51%:24Bp021pS8L1pRLM1pRDN1&=vQGv0&Ov5r7r6%77654321Ev6%978761D43p031p0<1p0I1p0M1p0Q71pSBQ<1pSJQ>1pS2Q@1")) (only parsing).
Variable ois : ltac:(sec_ty2 constr:(SECT) 0%nat 0%nat).
Variable str : ltac:(sec_ty2 constr:(SECT) 1%nat 0%nat).
Variable sm : ltac:(sec_ty2 constr:(SECT) 2%nat 0%nat).
Lemma iss_at_agreeA : ltac:(sec_stmt2 constr:(SECT) 3%nat 0%nat).
Proof.
intros Ho Ho' AGa AGB (H0 & D & C & H16 & H24 & H32 & H40 & H48 & H64 & VS & H104 & H112 & IOS & E1 & E2). destruct AGa as [AG SH] eqn:EA.
split; [u64x AG H0|]. split; [defx AG D|]. split; [accx SH C|]. split; [u64x AG H16|]. split; [u64x AG H24|]. split; [u64x AG H32|].
split; [u64x AG H40|]. split; [u64x AG H48|]. split; [u64x AG H64|].
split; [apply vstr_at_agreeA; [lia|lia| eapply agA_sub; [exact AGa|lia|lia]| exact AGB| exact VS]|].
split; [u64x AG H104|]. split; [u32x AG H112|].
split; [apply iosb_at_agreeA; [lia|lia| eapply agA_sub; [exact AGa|lia|lia]| exact IOS]|]. split; [exact E1| exact E2].
Qed.
End S.
Section S.
Local Abbreviation SECT := (ltac2:(TCodec.tc2 tcn__PmModelFactsA "RM'4'D&Q2zr3%3221&Q1r4+\0%3221&Q5+2+R0%3221%<251&Mr5%2219&F&A%11=%311%D2C1%417%611&:%D221%I21>r6%:11%<11%@216&?r7%211%Q12Q01r8%511&Q4+Q0&@%115%Q02O1%5241%Q6271%Q;21Q0r9%?11%812%Q72Q61%<2;1%Q4241'3'K&Br=%211(;r2r1%33QH21%93851%Q?24QGp021pS8R01pRLR11pRDR21&CvQGv0&O&Q0v5r<r;%8876543D21v6r>%;8:98721G5p041p0>1p0N1p0Q51p0Q@1p0QE1p0QJ1p0R01p0R61p0R:1p0RD1pS<RI1pS2RK1pS4RL1")) (only parsing).
Variable op : ltac:(sec_ty2 constr:(SECT) 0%nat 0%nat).
Variable ois : ltac:(sec_ty2 constr:(SECT) 1%nat 0%nat).
Variable s : ltac:(sec_ty2 constr:(SECT) 2%nat 0%nat).
Lemma parser_at_agreeA : ltac:(sec_stmt2 constr:(SECT) 3%nat 0%nat).
Proof.
intros Ho Ho' AGa Hq Hq' AGC Hb Hb' AGV AGT (H0 & D & C0 & H8 & H9 & H12 & H16 & H20 & NI & SRC & H320 & H328 & C320 & TB & VEC & B1 & B2 & B3).
destruct AGa as [AG SH] eqn:EA.
split; [u64x AG H0|]. split; [defx AG D|]. split; [accx SH C0|]. split; [u8x AG H8|]. split; [u8x AG H9|]. split; [u32x AG H12|].
split; [u8x AG H16|]. split; [u32x AG H20|].
split; [apply nullis_at_agreeA; [lia|lia| eapply agA_sub; [exact AGa|lia|lia]| exact NI]|].
split; [apply src_fields_at_agreeA; [lia|lia|exact Hq|exact Hq'| eapply agA_sub; [exact AGa|lia|lia]| exact AGC| exact SRC]|].
split; [u32x AG H320|]. split; [u64x AG H328|]. split; [accx SH C320|].
split; [apply vstr_at_agreeA; [lia|lia| eapply agA_sub; [exact AGa|lia|lia]| exact AGT| exact TB]|].
split; [apply vec_at_agreeA; [lia|lia|exact Hb|exact Hb'| eapply (L5C.agree_on_sub M M'); [exact AG|lia|lia]| exact AGV| exact VEC]|].
split; [exact B1|]. split; [exact B2| exact B3].
Qed.
End S.
End Agree.
End PMFA.
