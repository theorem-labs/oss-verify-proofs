(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec StoreOk HeapIface L5Defs L5Core PmLayout PmModel.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__PmModelFacts () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.MemImageType."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Core.L5C."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs.L5."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmModel.PM."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmModelFacts.PMF."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0A"; "1bool"; "1false"; "1list"; "1option"; "1pair"; "1true"; "2and"; "2eq"; "3Z"; "0L"; "4Segment"; "0M"; "0M'"; "5heap_layout"; "5hl_b_overhead"]; ["5hl_k_per_malloc"; "6agree_on"; "7u32_at"; "7u64_at"; "7u8_at"; "8CHUNK"; "8VLong"; "8cost1"; "8credit_add"; "8iosb_at"; "8iss_at"; "8nullis_at"; "8p_b"; "8p_k"; "8p_src"; "8p_tb"]; ["8parser_at"; "8pot_call"; "8pot_stack"; "8pot_text"; "8pst"; "8pstate"; "8pstate_at"; "8sr_qc"; "8src_fields_at"; "8srcst"; "8strm"; "8tb_law"; "8vec_at"; "8vs_cap"; "8vstr"; "8vstr_at"]; ["8zeros_at"; "9credit_le"; ":add"; ":div"; ":le"; ":lor"; ":lt"; ":max"; ":modulo"; ":mul"; ":pow"; ":sub"; ":testbit"; "0T3"; "0T4"; "0a"]; ["0a'"; "0b"; "0c"; "0c'"; "0isp"; "0k"; "0n"; "0n'"; "0need"; "0o"; "0ois"; "0op"; "0os"; "0p"; "0rdb"; "0s"]; ["0s'"; "0sbp"; "0segs"; "0sm"; "0src"; "0st"; ";bv"; "0stk"; "0str"; "0tg"; "0v"; "0vp"; "0w"; "0x"]]).
Module PMF.
Lemma lor7 : ltac2:(TCodec.tc2 tcn__PmModelFacts "F'9&QDzr1%3221'8&QB&QEr2+7%3221+1%6221&QI+8&QC%1282%4231%<214%>3C71p0@1pULE1").
Proof. intros x.
intros Hx. pose proof (Z.add_lor_land x 7) as H.
assert (E : Z.land x 7 = x mod 8) by (change 7 with (Z.ones 3); rewrite Z.land_ones by lia; reflexivity).
rewrite E in H. pose proof (Z.div_mod x 8 ltac:(lia)). lia.
Qed.
Lemma tb_law_le : ltac2:(TCodec.tc2 tcn__PmModelFacts "J'9&Q;r2%211&QF&QKr3+1%3221%5217&QB&QJ+2+J%3221+`P0%6221%=2;1&QDr5%2216p041p0=1p0D1pTBH1pT6I1").
Proof. intros c need.
intros (j & Hj & Hlt & Hlo & Hmod) Hgrow Hneed.
destruct (Z_le_gt_dec c (2 ^ 26)) as [Hle|Hgt]; [exact Hle|exfalso].
assert (Hj12 : 12 <= j).
{ destruct (Z_le_gt_dec 12 j) as [H|H]; [exact H|exfalso].
assert (2 ^ (15 + j) <= 2 ^ 26) by (apply Z.pow_le_mono_r; lia). lia. }
assert (Hd : (2 ^ 15 | 2 ^ (3 + j))).
{ exists (2 ^ (j - 12)). rewrite <- Z.pow_add_r by lia. f_equal. lia. }
assert (Hm15 : c mod 2 ^ 15 = 0).
{ apply Z.mod_divide; [lia|]. apply Z.divide_trans with (2 ^ (3 + j)); [exact Hd|].
apply Z.mod_divide; [pose proof (PM.pow2_pos (3 + j)); lia| exact Hmod]. }
apply Z.mod_divide in Hm15; [|lia]. destruct Hm15 as (q & Hq).
change (2 ^ 15) with 32768 in Hq. change (2 ^ 26) with 67108864 in *. lia.
Qed.
Lemma double_core : ltac2:(TCodec.tc2 tcn__PmModelFacts "Q6'9'8&QHr2+8%3221z%63721&QD+`P0r3%3221'7&QI+2&QKr4+1%3221%6251%<21:%8275%7215%?2=1%<241&QB&QC%12;G%?2H1%421Ir5%B2A1%O3Q031p091p0G1p0L1pULQ41pT6Q51").
Proof. intros c x.
intros Hm Hc Hx. apply Z.mod_divide in Hm; [|lia]. destruct Hm as (q & ->).
assert (E : x / 8 = 2 * q - 1) by (symmetry; apply (Z.div_unique x 8 (2 * q - 1) (x - 8 * (2 * q - 1))); lia).
rewrite E. lia.
Qed.
Lemma mod_pow2_le : ltac2:(TCodec.tc2 tcn__PmModelFacts "J'9'7&QDzr2%3221r1%5231%7231'8&QHr4&QJ+2%221:%5241%73@1=r5%6257%9221%;3D1Ap051p0>1pT4G1pT0H1pT6I1").
Proof. intros c a b.
intros Hab Hm. apply Z.mod_divide; [pose proof (PM.pow2_pos a); lia|].
apply Z.divide_trans with (2 ^ b); [exists (2 ^ (b - a)); rewrite <- Z.pow_add_r by lia; f_equal; lia|].
apply Z.mod_divide; [pose proof (PM.pow2_pos b); lia| exact Hm].
Qed.
Section S.
Local Abbreviation SECT := (ltac2:(TCodec.tc2 tcn__PmModelFacts "R3'9&Q;r3%211&QD+Jr4%3221&QF&QKr5+1%3221%5217&QBr6%7215+`P0%4221%?291&QJ+2%221A%9216%@291'8&QE&QG&QIr8%E21C%32:1r7%6221+7%9221%F21I%<3Q5F1'7%Q617r9%Q021N%>2E1%Q22;Q0%Q8221%Q92@2+K%K2J1%Q<2@1&QH+8%22C1z%L3QE21%@261%A2:1%B2<1%C2B1p0E1p0Q31p0Q91p0Q@1p0QG1p0QL1pT8R01pTBR11pT6R21")) (only parsing).
Variable c : ltac:(sec_ty2 constr:(SECT) 0%nat 0%nat).
Variable need : ltac:(sec_ty2 constr:(SECT) 1%nat 0%nat).
Variable c' : ltac:(sec_ty2 constr:(SECT) 2%nat 0%nat).
Lemma tb_law_step : ltac:(sec_stmt2 constr:(SECT) 3%nat 0%nat).
Proof.
intros LAW Hc Hgrow Hstep Hneed ->.
pose proof (tb_law_le c need LAW Hgrow Hneed) as Hc26.
destruct LAW as (j & Hj & Hlt & Hlo & Hmod).
set (x := Z.max (2 * (c - 1)) need). assert (Hx0 : 0 <= x) by (unfold x; lia).
rewrite (lor7 x Hx0).
assert (Hm8 : c mod 8 = 0) by (apply (mod_pow2_le c 3 (3 + j)); [lia| exact Hmod]).
pose proof (Z.div_mod x 8 ltac:(lia)) as DM. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as MB.
assert (Hge : x <= 8 * (x / 8) + 8 - 1) by lia.
destruct (Z_lt_le_dec c 16384) as [Hsmall|Hbig].
-
assert (j = 0). { destruct Hlo as [E|H]; [exact E|exfalso]. assert (2 ^ 14 <= 2 ^ (14 + j)) by (apply Z.pow_le_mono_r; lia). change (2 ^ 14) with 16384 in *. lia. }
subst j. assert (Hx : x <= 32766) by (unfold x; lia).
assert (Hq : x / 8 <= 4095) by (apply Z.div_le_upper_bound; lia).
assert (M8 : (8 * (x / 8) + 8) mod 8 = 0) by (replace (8 * (x / 8) + 8) with ((x / 8 + 1) * 8) by lia; apply Z.mod_mul; lia).
split; [|change (2 ^ 27) with 134217728; unfold x in *; repeat split; try lia].
destruct (Z_lt_le_dec (8 * (x / 8) + 8) 32768) as [Hlt'|Hge'].
+ exists 0. change (2 ^ (15 + 0)) with 32768. change (2 ^ (3 + 0)) with 8. repeat split; lia.
+ exists 1. assert (E : 8 * (x / 8) + 8 = 32768) by lia. rewrite E. change (2 ^ (15 + 1)) with 65536. change (2 ^ (14 + 1)) with 32768.
change (2 ^ (3 + 1)) with 16. repeat split; first [lia | reflexivity].
-
assert (Hx : 2 * (c - 1) <= x <= 2 * c - 1) by (unfold x; lia).
rewrite (double_core c x Hm8 Hbig Hx).
assert (M8' : (2 * c) mod 8 = 0).
{ apply Z.mod_divide; [lia|]. apply Z.divide_mul_r. apply Z.mod_divide; [lia| exact Hm8]. }
assert (LAW' : PM.tb_law (2 * c)).
{ exists (j + 1).
assert (Hj12 : j <= 12).
{ destruct (Z_le_gt_dec j 12) as [H|H]; [exact H|exfalso]. destruct Hlo as [E|Hlo]; [lia|].
assert (2 ^ 27 <= 2 ^ (14 + j)) by (apply Z.pow_le_mono_r; lia). change (2 ^ 27) with 134217728 in *. change (2 ^ 26) with 67108864 in *. lia. }
replace (15 + (j + 1)) with (15 + j + 1) by lia. replace (14 + (j + 1)) with (15 + j) by lia. replace (3 + (j + 1)) with (3 + j + 1) by lia.
rewrite !(Z.pow_add_r 2 _ 1) by lia. change (2 ^ 1) with 2.
split; [lia|]. split; [lia|]. split.
- right. destruct Hlo as [->|Hlo].
+ change (2 ^ (15 + 0)) with 32768. lia.
+ replace (15 + j) with (14 + j + 1) by lia. rewrite Z.pow_add_r by lia. change (2 ^ 1) with 2. lia.
- replace (2 * c) with (c * 2) by lia. rewrite Z.mul_mod_distr_r; [rewrite Hmod; reflexivity| pose proof (PM.pow2_pos (3 + j)); lia| lia]. }
change (2 ^ 26) with 67108864 in *. change (2 ^ 27) with 134217728.
split; [exact LAW'|]. split; [lia|]. split; [unfold x in *; lia|]. split; [lia| exact M8'].
Qed.
End S.
Lemma tb_law_first : ltac2:(TCodec.tc2 tcn__PmModelFacts "QA'9&QF+Fr2%3221&QDr3&QB+`P0%2271%5241'8&QE&QG+Q<r4%3221+7%6221+1%=221%:3E?1'7&Q;%119&QK%12;7%F2=1r5%H213&QJ+2+K%3221%M2C1&QH+8%22F1z%L3Q721%B261%C2<1%D2?1%E2C1p0G1p0Q31p0Q:1pT8Q?1pTBQ@1").
Proof. intros need c'.
intros H1 H2 ->. set (x := Z.max 44 need). assert (Hx0 : 0 <= x) by (unfold x; lia). rewrite (lor7 x Hx0).
pose proof (Z.div_mod x 8 ltac:(lia)) as DM. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as MB.
assert (Hq : x / 8 <= 2051) by (apply Z.div_le_upper_bound; unfold x; lia).
assert (M8 : (8 * (x / 8) + 8) mod 8 = 0) by (replace (8 * (x / 8) + 8) with ((x / 8 + 1) * 8) by lia; apply Z.mod_mul; lia).
change (2 ^ 27) with 134217728. split; [|unfold x in *; repeat split; lia].
exists 0. change (2 ^ (15 + 0)) with 32768. change (2 ^ (3 + 0)) with 8. repeat split; lia.
Qed.
Definition credit_le (c c' : credit) : Prop := fst c <= fst c' /\ snd c <= snd c'.
Lemma pot_text_step : ltac2:(TCodec.tc2 tcn__PmModelFacts "Q1'>'Q>'9&QD&QI+2&Q=r3%211%5241r2%511%9231&QA&H&Gr5&QB+1%22;1%5241&Q3%52<4%237@1%:241r4%53:1@%>231p0@1pUDK1pU2M1pU0N1pFQ01").
Proof. intros L s s' tg. intros H. unfold credit_le, PM.credit_add, PM.cost1, PM.pot_text. cbn [fst snd]. split; lia. Qed.
Lemma pot_stack_step : ltac2:(TCodec.tc2 tcn__PmModelFacts "M'>'9&QDzr1%3221&QA&H&Gr3&QI+Q0&QJ+2&QBr2+1%3221%6251%9281%<2;1&Q2%12=5%@231%32?9%C221p0E1pT<J1pFL1").
Proof. intros L k.
intros Hk. unfold credit_le, PM.credit_add, PM.cost1, PM.pot_stack. cbn [fst snd].
replace (k + 1 + 1) with (k + 1 + 1) by lia. rewrite (Z.pow_add_r 2 (k + 1) 1) by lia. change (2 ^ 1) with 2. split; lia.
Qed.
Lemma pot_call_le : ltac2:(TCodec.tc2 tcn__PmModelFacts "Q?'>'9'7&QDz&@r2%211%5241+8%7231%9231&?r3%211%<2;1+VQieK%>231%@231%@2?6&QF&QJ+2+J%3221%52<1%H271&QA&Q1r5r4%3221(5+`0&QB+M%?2>1&QI%12M8%5231%84Q7Q771%>2:1p0@1p0I1p0Q11pT>Q<1pFQ>1").
Proof. intros L n.
intros HK HB Hn. unfold credit_le, PM.pot_call, PM.credit_add, PM.cost1, PM.pot_stack, PM.pot_text, PM.vs_cap, PM.CHUNK. cbn [fst snd].
change (2 ^ 12) with 4096. change (2 ^ (0 + 1)) with 2. change (2 ^ 28) with 268435456. change (2 ^ 29) with 536870912. change (2 ^ 26) with 67108864 in Hn.
split; nia.
Qed.
Lemma u8_of_u64 : ltac2:(TCodec.tc2 tcn__PmModelFacts "Q:'3';%211'RFyR0%211'4y8%511%311p051'9'7&QDzr1%3221&QF&QJ+2+R0%3221%5271%;271&Cr5r4r3r2%544321&Dr6&QH+X0%2271%544:91p071p0>1pUJK1pT0L1pJN1pU6Q71").
Proof. intros segs M a w.
intros Hw H. unfold L5.u64_at, L5.u8_at in *. unfold word_to_le_bytes in H. rewrite L5.unsigned_lit in H by lia.
change (Z_to_le_bytes 8 w) with (Z_to_bv 8 w :: Z_to_le_bytes 7 (Z.shiftr w 8)) in H.
change (rdn segs M (Z_to_bv 64 a) 8) with
(match (match M (Z_to_bv 64 a) with Some b => Some b | None => seg_rom segs (Z_to_bv 64 a) end) with
| Some b => match rdn segs M (Z_to_bv 64 a + 1) 7 with Some rest => Some (b :: rest) | None => None end | None => None end) in H.
cbn [rdn]. destruct (match M (Z_to_bv 64 a) with Some b => Some b | None => seg_rom segs (Z_to_bv 64 a) end) as [b0|]; [|discriminate].
destruct (rdn segs M (Z_to_bv 64 a + 1) 7) as [rest|]; [|discriminate]. injection H as Hb _. rewrite Hb. f_equal. f_equal.
apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. rewrite Z.mod_mod by lia. reflexivity.
Qed.
Lemma odd_byte : ltac2:(TCodec.tc2 tcn__PmModelFacts "I'9'8&QHr1+2%3221z%63721&QDr2%2241'1&QL&QBr3+1%3221+X0%@221%721=(6%D3:21p0<1p0@1pT6H1").
Proof. intros c.
intros Hc H0. change 256 with (2 ^ 8). rewrite Z.mod_pow2_bits_low by lia. rewrite Z.bit0_odd.
apply Z.mod_divide in Hc; [|lia]. destruct Hc as (q & ->). replace (q * 2 + 1) with (2 * q + 1) by lia. apply Z.odd_odd.
Qed.
Lemma even_byte : ltac2:(TCodec.tc2 tcn__PmModelFacts "='9'8'1&QL&QI+2r1%3221z%6221(2%:3921pT><1").
Proof. intros n. apply Z.testbit_even_0. Qed.
Section Agree.
Variable segs : list Segment.
Variable A : pm_addrs.
Let T3 : (word -> option byte) -> Z -> Z -> Prop := fun _ _ _ => True.
Let T4 : (word -> option byte) -> Z -> Z -> Z -> Prop := fun _ _ _ _ => True.
Variables M M' : word -> option byte.
Abbreviation ag := (L5C.agree_on M M').
Lemma u32_at_agree : ltac2:(TCodec.tc2 tcn__PmModelFacts "O'9&Av<v=r2+4%544321&QDzr3%3221&QBr4%2218&QJ+2+R0%3221%;251&BvRBr5%342D1:r6%544E13p031p081p0A1p0F1pUFM1pT0N1").
Proof. intros a v.
intros Hag Ha H4 Hu. unfold L5.u32_at in *. rewrite (L5C.rdn_agree segs M M' 4%nat a Ha ltac:(cbn; lia)); [exact Hu|].
intros i Hi. apply Hag. cbn in Hi. lia.
Qed.
Lemma zeros_at_agree : ltac2:(TCodec.tc2 tcn__PmModelFacts "@'9&Av<v=r2r1%544321&Q@r3%23715r4%43813p031p071pT>>1pT0?1").
Proof. intros a n. intros Hag Z i Hi. rewrite Hag by lia. apply Z. exact Hi. Qed.
Lemma vstr_at_agree : ltac2:(TCodec.tc2 tcn__PmModelFacts "Q='9'Q>&QDzr2%3221&QBr3+H%3221&QJ+2+R0%3221%<251&Av<v=r4%44321;'8r7(Fr1%23AD1%53H41%;4:9F8p021pTLL1pT>M1pT6N1&Q?vRBvQMr6r5%5543D21%6554D@3p021p091p0E1p0K1p0Q51pU0Q:1pTDQ<1").
Proof. intros o s.
intros Ho Ho' AG AGB (D & _ & H). split; [apply (L5C.defined_agree M M' o 24 AG D)|]. split; [exact I|].
destruct s as [n|c n p].
- destruct H as (Hn & B0). split; [exact Hn|]. apply (L5C.u8_at_agree segs M M'); [apply (L5C.agree_on_sub M M' o 24); [exact AG|lia|lia]|lia|lia|exact B0].
- destruct H as (W0 & W8 & W16 & Hn & Hc & He & DB & _).
repeat split; try assumption; try lia.
+ apply (L5C.u64_at_agree segs M M'); [apply (L5C.agree_on_sub M M' o 24); [exact AG|lia|lia]|lia|lia|exact W0].
+ apply (L5C.u64_at_agree segs M M'); [apply (L5C.agree_on_sub M M' o 24); [exact AG|lia|lia]|lia|lia|exact W8].
+ apply (L5C.u64_at_agree segs M M'); [apply (L5C.agree_on_sub M M' o 24); [exact AG|lia|lia]|lia|lia|exact W16].
+ apply (L5C.defined_agree M M' p c (AGB c n p eq_refl) DB).
Qed.
Lemma pstate_at_agree : ltac2:(TCodec.tc2 tcn__PmModelFacts "Q0'9'Q5&QDzr2%3221&QBr3+Q0%3221&QJ+2+R0%3221%<251&Av<v=r4%44321;&Q6vRBr5%342715r6%544813p031p081p0>1p0H1pU0M1pT0O1").
Proof. intros a s.
intros Ha Ha' AG (H0 & H8 & H16 & H24). repeat split.
- apply u32_at_agree; [apply (L5C.agree_on_sub M M' a 32); [exact AG|lia|lia]|lia|lia|exact H0].
- apply (L5C.u64_at_agree segs M M'); [apply (L5C.agree_on_sub M M' a 32); [exact AG|lia|lia]|lia|lia|exact H8].
- apply (L5C.u8_at_agree segs M M'); [apply (L5C.agree_on_sub M M' a 32); [exact AG|lia|lia]|lia|lia|exact H16].
- apply (L5C.u64_at_agree segs M M'); [apply (L5C.agree_on_sub M M' a 32); [exact AG|lia|lia]|lia|lia|exact H24].
Qed.
Section S.
Local Abbreviation SECT := (ltac2:(TCodec.tc2 tcn__PmModelFacts "QF'9'3'Q5%211&QDzr4%3221&QBr5+H%3221&QJ+2+R0%3221%<251%=2<8r6&QI+Q0%928<%3221%?251%D219&Av<v=r8%44321Cr7%C2B1%=2<1%847651&Q<vRBvQMvQNr:r9%68543>21<:r;%88765?143>p031p0;1p0@1p0F1p0N1p0Q01p0Q:1pU@Q?1pT<QC1pT4QD1pUFQE1")) (only parsing).
Variable v : ltac:(sec_ty2 constr:(SECT) 0%nat 0%nat).
Variable b : ltac:(sec_ty2 constr:(SECT) 1%nat 0%nat).
Variable k : ltac:(sec_ty2 constr:(SECT) 2%nat 0%nat).
Variable stk : ltac:(sec_ty2 constr:(SECT) 3%nat 0%nat).
Lemma vec_at_agree : ltac:(sec_stmt2 constr:(SECT) 4%nat 0%nat).
Proof.
intros Hv Hv' Hb Hb' AGV AGB (V0 & V8 & V16 & Hk & Hlen & Hal & DB & _ & _ & EL).
pose proof (PM.pow2_pos k ltac:(lia)) as P2.
split; [apply (L5C.u64_at_agree segs M M'); [apply (L5C.agree_on_sub M M' v 24); [exact AGV|lia|lia]|lia|lia|exact V0]|].
split; [apply (L5C.u64_at_agree segs M M'); [apply (L5C.agree_on_sub M M' v 24); [exact AGV|lia|lia]|lia|lia|exact V8]|].
split; [apply (L5C.u64_at_agree segs M M'); [apply (L5C.agree_on_sub M M' v 24); [exact AGV|lia|lia]|lia|lia|exact V16]|].
split; [exact Hk|]. split; [exact Hlen|]. split; [exact Hal|].
split; [apply (L5C.defined_agree M M' b _ AGB DB)|]. split; [exact I|]. split; [exact I|].
intros n Hn. apply pstate_at_agree; [lia|lia| |apply EL; exact Hn].
apply (L5C.agree_on_sub M M' b (32 * 2 ^ k)); [exact AGB|lia|lia].
Qed.
End S.
Lemma ag_sub : ltac2:(TCodec.tc2 tcn__PmModelFacts "G'9&Av<v=r4r3%544321&QDr5%2214&QB%1276r6%3215%7231%>4=<7;p021p081p0<1pT@C1pT2D1pT>E1pT0F1").
Proof. intros a n a' n'. apply L5C.agree_on_sub. Qed.
Ltac u64x AG H := apply (L5C.u64_at_agree segs M M'); [eapply ag_sub; [exact AG|lia|lia]|lia|lia|exact H].
Ltac u32x AG H := apply u32_at_agree; [eapply ag_sub; [exact AG|lia|lia]|lia|lia|exact H].
Ltac u8x AG H := apply (L5C.u8_at_agree segs M M'); [eapply ag_sub; [exact AG|lia|lia]|lia|lia|exact H].
Ltac defx AG H := apply (L5C.defined_agree M M' _ _); [eapply ag_sub; [exact AG|lia|lia]|exact H].
Lemma iosb_at_agree : ltac2:(TCodec.tc2 tcn__PmModelFacts "Q3'9&QDzr4%3221&QBr5+TH%3221&QJ+2+R0%3221%<251&Av<v=r6%44321;&IvRBv0vQMr7%58432917BEr8%78654:139Dp031p0:1p0@1p0J1pU<O1pTNQ01pUHQ11pTDQ21").
Proof. intros o vp rdb st.
intros Ho Ho' AG (H0 & H32 & H36 & H40 & H48 & Z & D & _ & ST).
split; [u64x AG H0|]. split; [u32x AG H32|]. split; [u32x AG H36|]. split; [u64x AG H40|]. split; [u64x AG H48|].
split; [apply zeros_at_agree; [eapply ag_sub; [exact AG|lia|lia]|exact Z]|]. split; [defx AG D|]. split; [exact I| exact ST].
Qed.
Lemma nullis_at_agree : ltac2:(TCodec.tc2 tcn__PmModelFacts "Q0'9&QDzr1%3221&QBr2+W8%3221&QJ+2+R0%3221%<251&Av<v=r3%44321;&KvRBv0vQMr4%5543291r5%75654:1p031p0:1p0@1p0J1pTDO1").
Proof. intros o.
intros Ho Ho' AG (H0 & D & _ & H16 & H24 & IOS).
split; [u64x AG H0|]. split; [defx AG D|]. split; [exact I|]. split; [u64x AG H16|]. split; [u64x AG H24|].
apply iosb_at_agree; [lia|lia| eapply ag_sub; [exact AG|lia|lia]| exact IOS].
Qed.
Section S.
Local Abbreviation SECT := (ltac2:(TCodec.tc2 tcn__PmModelFacts "QF'9'Q9&QDzr4%3221&QBr5+Y8%3221&QJ+2+R0%3221%<251&Q7r3%211%@2?1%41?&E%?221%D219&Av<v=r8+W@%F221+QH%746521r6%A11%:4981=&Q8vRBvQMr:r9r7%6754@32>1r;%8776A154@p031p0;1p0?1p0H1p0M1p0Q21p0Q<1pU:QA1pU4QC1pT:QD1pTJQE1")) (only parsing).
Variable os : ltac:(sec_ty2 constr:(SECT) 0%nat 0%nat).
Variable isp : ltac:(sec_ty2 constr:(SECT) 1%nat 0%nat).
Variable sbp : ltac:(sec_ty2 constr:(SECT) 2%nat 0%nat).
Variable src : ltac:(sec_ty2 constr:(SECT) 3%nat 0%nat).
Lemma src_fields_at_agree : ltac:(sec_stmt2 constr:(SECT) 4%nat 0%nat).
Proof.
intros Ho Ho' Hq Hq' AG AGC (F1 & F2 & F3 & F4 & F5 & F6 & F7 & B1 & B2 & B3 & B4 & DC & _ & _).
split; [u64x AG F1|]. split; [u64x AG F2|]. split; [defx AG F3|]. split; [u64x AG F4|]. split; [u64x AG F5|]. split; [u64x AG F6|]. split; [u64x AG F7|].
split; [exact B1|]. split; [exact B2|]. split; [exact B3|]. split; [exact B4|].
split; [apply (L5C.defined_agree M M' _ _ AGC DC)|]. split; exact I.
Qed.
End S.
Section S.
Local Abbreviation SECT := (ltac2:(TCodec.tc2 tcn__PmModelFacts "QA'9'Q>'Q:&QDzr3%3221&QBr4+X@%3221&QJ+2+R0%3221%<251&Av<v=r5%44321;'8r8(Fr2r1%33E21%63J51%<4;:4Dp021pTLN1pT>O1pT6Q01&JvRBv0vQMr7r6%67543F21D%77654FB32p021p0:1p0G1p0M1p0Q71pU8Q<1pUBQ>1pTFQ@1")) (only parsing).
Variable ois : ltac:(sec_ty2 constr:(SECT) 0%nat 0%nat).
Variable str : ltac:(sec_ty2 constr:(SECT) 1%nat 0%nat).
Variable sm : ltac:(sec_ty2 constr:(SECT) 2%nat 0%nat).
Lemma iss_at_agree : ltac:(sec_stmt2 constr:(SECT) 3%nat 0%nat).
Proof.
intros Ho Ho' AG AGB (H0 & D & _ & H16 & H24 & H32 & H40 & H48 & H64 & VS & H104 & H112 & IOS & E1 & E2).
split; [u64x AG H0|]. split; [defx AG D|]. split; [exact I|]. split; [u64x AG H16|]. split; [u64x AG H24|]. split; [u64x AG H32|].
split; [u64x AG H40|]. split; [u64x AG H48|]. split; [u64x AG H64|].
split; [apply vstr_at_agree; [lia|lia| eapply ag_sub; [exact AG|lia|lia]| exact AGB| exact VS]|].
split; [u64x AG H104|]. split; [u32x AG H112|].
split; [apply iosb_at_agree; [lia|lia| eapply ag_sub; [exact AG|lia|lia]| exact IOS]|]. split; [exact E1| exact E2].
Qed.
End S.
Section S.
Local Abbreviation SECT := (ltac2:(TCodec.tc2 tcn__PmModelFacts "RM'9'Q4&QDzr3%3221&QBr4+\0%3221&QJ+2+R0%3221%<251&Av<v=r5%44321;&Q7&N%11?%311%F2E1%417%611&E%F221%K21@r6%:11%<11%B4A@16&Lr7%211%Q32Q21r8%511&QI+Q0&M%115%Q22Q11%5241%Q8271%Q=21Q2r9%?11%812%Q92Q81%<2;1%Q64Q5Q441'8'Q>&Or=%211(Fr2r1%33QJ21%93851%QA4Q@Q?4QIp021pTLR21pT>R31pT6R41&Q0vRBv0vQMvQNr<r;%786543QLC21r>%988765QM1E4p031p0<1p0L1p0Q31p0Q>1p0QC1p0QH1p0QN1p0R41p0R:1p0RD1pU0RI1pTFRK1pTHRL1")) (only parsing).
Variable op : ltac:(sec_ty2 constr:(SECT) 0%nat 0%nat).
Variable ois : ltac:(sec_ty2 constr:(SECT) 1%nat 0%nat).
Variable s : ltac:(sec_ty2 constr:(SECT) 2%nat 0%nat).
Lemma parser_at_agree : ltac:(sec_stmt2 constr:(SECT) 3%nat 0%nat).
Proof.
intros Ho Ho' AG Hq Hq' AGC Hb Hb' AGV AGT (H0 & D & _ & H8 & H9 & H12 & H16 & H20 & NI & SRC & H320 & H328 & _ & TB & VEC & B1 & B2 & B3).
split; [u64x AG H0|]. split; [defx AG D|]. split; [exact I|]. split; [u8x AG H8|]. split; [u8x AG H9|]. split; [u32x AG H12|].
split; [u8x AG H16|]. split; [u32x AG H20|].
split; [apply nullis_at_agree; [lia|lia| eapply ag_sub; [exact AG|lia|lia]| exact NI]|].
split; [apply src_fields_at_agree; [lia|lia|exact Hq|exact Hq'| eapply ag_sub; [exact AG|lia|lia]| exact AGC| exact SRC]|].
split; [u32x AG H320|]. split; [u64x AG H328|]. split; [exact I|].
split; [apply vstr_at_agree; [lia|lia| eapply ag_sub; [exact AG|lia|lia]| exact AGT| exact TB]|].
split; [apply vec_at_agree; [lia|lia|exact Hb|exact Hb'| eapply ag_sub; [exact AG|lia|lia]| exact AGV| exact VEC]|].
split; [exact B1|]. split; [exact B2| exact B3].
Qed.
End S.
End Agree.
End PMF.
