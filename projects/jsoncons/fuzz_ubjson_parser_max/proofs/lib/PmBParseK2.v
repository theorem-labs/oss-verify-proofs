(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA IcptIfaceAB0
L5Defs L5Core L5CoreKit L5Kn L5KnA L5LazyA L5DefsAB0 L5CoreAB0 L5StepARB0 PmLayout PmLayoutA PmModel PmModelFacts PmStatics PmStaticsA HeapIfaceAJx PmSpecsA PmSpecsAX PmSpecsAb
PmModelFactsA PmStepAB0 PmStep PmParKit2.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__PmBParseK2 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Core.L5C."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs.L5."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmLayoutA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmModel.PM."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmModelFactsA.PMFA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecsA.PMSPA."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M."; "Stdlib.ZArith.BinInt.Z."], [["1app"; "1cons"; "1length"; "1list"; "1nil"; "2eq"; "3Z"; "0M"; "0M'"; "4agree_on"; "5defined"; "6ADDR_B"; "7CHUNK"; "7PST"; "7VLong"; "7p_b"]; ["7p_depth"; "7p_done"; "7p_k"; "7p_more"; "7p_src"; "7p_stk"; "7p_tb"; "7p_tg"; "7parser_at"; "7pst"; "7pstate"; "7pstate_at"; "7sr_qc"; "7vec_at"; "7vstr"; "8agA"]; ["8agsh"; "9accA"; "9annA"; ":loaded_segments"; ";add"; ";le"; ";mul"; ";of_nat"; ";pow"; ";sub"; "0b"; "0c"; "0k"; "0n"; "0ois"; "0op"]; ["0p"; "0p'"; "0pre"; "0q"; "0s"; "0v"]]).
Local Ltac lia := first [ L5FastLia.plia | Lia.lia ].
Module PMBLPK2.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Section Upd.
Variables M M' : word -> option byte.
Local Ltac u64x AG H := apply (L5C.u64_at_agree RSEGS M M'); [eapply L5C.agree_on_sub; [exact AG|lia|lia]|lia|lia|exact H].
Local Ltac u32x AG H := apply (PMF.u32_at_agree RSEGS M M'); [eapply L5C.agree_on_sub; [exact AG|lia|lia]|lia|lia|exact H].
Local Ltac u8x AG H := apply (L5C.u8_at_agree RSEGS M M'); [eapply L5C.agree_on_sub; [exact AG|lia|lia]|lia|lia|exact H].
Section S.
Local Abbreviation SECT := (ltac2:(TCodec.tc2 tcn__PmBParseK2 "S:'6'3'J%211&M&Q3&Q1&Q2v7r6r5r4&0r3(1r2(4%11?%43@31%73A61%@8?>=<;:91&Q5zr7%3221&Q4r8+H%3221&Q8+2+R0%3221%<251%=2<8r9&Q6+Q0%928<%3221%?251%D219&9v8r;%34Q521B&Q7&2%12Q>=%311%>2=1%94Q;871r<r:%72QD1%911%D2C1%Q0251%Q121E&Q9%O2N@%I2H1%3216%421J%F4QHE61&Q0r=%Q62Q5?%Q02O1%44QMJ31&:r>%I2R6D%K11%Q62Q51%QB241%63Q11Q7&Kr?%Q02R==%Q211%Q=2Q<1%QI241%64R>Q81Q7rAr@%R83RDQ2R5%R;3RE@1%RD8RCRBRAQ=43:1p061p0>1p0F1p0L1p0Q:1p0QA1p0QF1p0QN1p0R01p0R:1p0R?1pS4S21pS2S31pS6S31pRJS71pRFS81pS<S91")) (only parsing).
Variable v : ltac:(sec_ty2 constr:(SECT) 0%nat 0%nat).
Variable b : ltac:(sec_ty2 constr:(SECT) 1%nat 0%nat).
Variable k : ltac:(sec_ty2 constr:(SECT) 2%nat 0%nat).
Variable pre : ltac:(sec_ty2 constr:(SECT) 3%nat 0%nat).
Variable p : ltac:(sec_ty2 constr:(SECT) 4%nat 0%nat).
Variable p' : ltac:(sec_ty2 constr:(SECT) 5%nat 0%nat).
Lemma vec_at_set_topA : ltac:(sec_stmt2 constr:(SECT) 6%nat 0%nat).
Proof.
intros (V0 & V8 & V16 & Hk & Hlen & Hal & DB & CB & AN & EL) Hv Hv' Hb Hb' AG0 AGL AGH SH DT PT.
pose proof (PM.pow2_pos k ltac:(lia)) as P2.
unfold PM.vec_at. rewrite !length_app in *. cbn [length] in *. rewrite !Nat2Z.inj_add in *. cbn [Z.of_nat Pos.of_succ_nat] in *.
split; [u64x AG0 V0|]. split; [u64x AG0 V8|]. split; [u64x AG0 V16|].
split; [exact Hk|]. split; [exact Hlen|]. split; [exact Hal|].
split.
{ intros i Hi. destruct (Z_lt_le_dec i (32 * Z.of_nat (length pre))) as [X|X]; [rewrite AGL by lia; apply DB; lia|].
destruct (Z_lt_le_dec i (32 * Z.of_nat (length pre) + 32)) as [Y|Y].
- replace (b + i) with (b + 32 * Z.of_nat (length pre) + (i - 32 * Z.of_nat (length pre))) by lia. apply DT. lia.
- rewrite AGH by lia. apply DB; lia. }
split; [apply (PMFA.accA_agree M M' b _); [eapply PMFA.agsh_sub; [exact SH|lia|lia]| exact CB]|].
split; [apply (PMFA.annA_agree M M' b _ _ (PMFA.mod16_8 b Hal)); [lia| apply PMFA.blk8| exact SH| exact AN]|].
intros i Hi.
destruct (Nat.eq_dec i (length pre)) as [->|N]; [rewrite PMPK2.nth_app_at; exact PT|].
rewrite PMPK2.nth_app_last by (try rewrite length_app; cbn; lia).
specialize (EL i ltac:(lia)). rewrite PMPK2.nth_app_last in EL by (try rewrite length_app; cbn; lia).
apply (PMF.pstate_at_agree RSEGS M M'); [lia|lia| |exact EL].
apply (L5C.agree_on_sub M M' b (32 * Z.of_nat (length pre))); [exact AGL|lia|lia].
Qed.
End S.
Section S.
Local Abbreviation SECT := (ltac2:(TCodec.tc2 tcn__PmBParseK2 "U7'6'I'3'J%211&H&Q3&;&Q1&Q2v7r6r5r4%9887654321'5&E%115&0(1r3(4%11C%43D31%63E;1%:3E81&Q5zr8%3221&Q4r9+\0%3221&Q8+2+R0%3221%<251&Ov8r:%34Q021:&:&L&D%11?%311&<%63921&Q0%61:%811%34Q;=15&?r;%211%O2N1r<%511&Q6+Q0&B%115%N2M1%5241%Q4271%Q921N&9r=%@11&Q7&2%12R6?%311%?2>1%84R2Q461r>%H11%72R<:%911%E2D1%QD241%QE21F&Q9%G18%QD2QC1%K2J1%4217%521L%F4R@QB71r?%Q611%O12%QL2QK1%Q32Q21%Q>4RFQH41r@%Q<11%K2S08%M11%Q92Q81%R8241%QL3QO1Q:&KrA%QD11%Q32S8:%Q511%QA2Q@1%R@241%74S9R71Q2'N&FrE%211(>r2r1%33S321%S93851%RB4S?RA4S<p021pS8SK1pRLSL1pRHSM1rD(=&CrC%211&A%113&@%115%RJ16%G17&G%119%RE1:%R>1;rB%SK3T;Q=SH%SM3T<21%A9><:986541%T<8T;T:T9T8S9OC1p0E1p0Q41p0Q=1p0QE1p0QL1p0R;1p0RE1p0S01p0S51p0S:1p0SB1p0SG1p0T11p0T61p0TB1pS4TN1pS2TO1pS6TO1pS:U31pRNU51pS0U61")) (only parsing).
Variable op : ltac:(sec_ty2 constr:(SECT) 0%nat 0%nat).
Variable ois : ltac:(sec_ty2 constr:(SECT) 1%nat 0%nat).
Variable s : ltac:(sec_ty2 constr:(SECT) 2%nat 0%nat).
Variable pre : ltac:(sec_ty2 constr:(SECT) 3%nat 0%nat).
Variable p : ltac:(sec_ty2 constr:(SECT) 4%nat 0%nat).
Variable p' : ltac:(sec_ty2 constr:(SECT) 5%nat 0%nat).
Lemma parser_top_updA : ltac:(sec_stmt2 constr:(SECT) 6%nat 0%nat).
Proof.
intros PA ES Ho Ho' [AG SH] DCQ SHQ Hb Hb' AGL AGH SHB DT PT AGT.
pose proof PA as (H0 & D & C24 & H8 & H9 & H12 & H16 & H20 & NI & SRC & H320 & H328 & C320 & TB & VEC & B1 & B2 & B3).
destruct SRC as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & G1 & G2 & G3 & G4 & DC & CC & C240).
rewrite ES in VEC.
assert (U64 : forall a v, op <= a -> a + 8 <= op + 384 -> L5.u64_at RSEGS M a v -> L5.u64_at RSEGS M' a v).
{ intros a v Ha Hb0 X. apply (L5C.u64_at_agree RSEGS M M'); [intros i Hi; apply AG; lia| lia| lia| exact X]. }
assert (U32 : forall a v, op <= a -> a + 4 <= op + 384 -> L5.u32_at RSEGS M a v -> L5.u32_at RSEGS M' a v).
{ intros a v Ha Hb0 X. apply (PMF.u32_at_agree RSEGS M M'); [intros i Hi; apply AG; lia| lia| lia| exact X]. }
assert (U8 : forall a v, op <= a -> a + 1 <= op + 384 -> L5.u8_at RSEGS M a v -> L5.u8_at RSEGS M' a v).
{ intros a v Ha Hb0 X. apply (L5C.u8_at_agree RSEGS M M'); [intros i Hi; apply AG; lia| lia| lia| exact X]. }
unfold PM.parser_at, PM.src_fields_at. cbn [PM.p_more PM.p_done PM.p_depth PM.p_src PM.p_tb PM.p_tg PM.p_b PM.p_k PM.p_stk].
split; [apply U64; [lia|lia|exact H0]|]. split; [apply (L5C.defined_agree M M' op 384 AG D)|].
split; [apply (PMFA.accA_agree M M' op 24); [intros x Hx; apply SH; lia| exact C24]|].
split; [apply U8; [lia|lia|exact H8]|]. split; [apply U8; [lia|lia|exact H9]|]. split; [apply U32; [lia|lia|exact H12]|].
split; [apply U8; [lia|lia|exact H16]|]. split; [apply U32; [lia|lia|exact H20]|].
split; [apply (PMFA.nullis_at_agreeA RSEGS PMB.AD M M' (op + 32)); [lia|lia| split; [intros i Hi; apply AG; lia| intros x Hx; apply SH; lia]| exact NI]|].
split.
{ split; [apply U64; [lia|lia|exact F1]|]. split; [apply U64; [lia|lia|exact F2]|].
split; [intros i Hi; replace (op + 24 + 256 + i) with (op + (280 + i)) by lia; rewrite AG by lia; apply D; lia|].
split; [apply U64; [lia|lia|exact F4]|]. split; [apply U64; [lia|lia|exact F5]|]. split; [apply U64; [lia|lia|exact F6]|]. split; [apply U64; [lia|lia|exact F7]|].
split; [exact G1|]. split; [exact G2|]. split; [exact G3|]. split; [exact G4|].
split; [exact DCQ|].
split; [apply (PMFA.accA_agree M M' _ _ SHQ CC)|].
apply (PMFA.accA_agree M M' (op + 24 + 240) 56); [intros x Hx; apply SH; lia| exact C240]. }
split; [apply U32; [lia|lia|exact H320]|]. split; [apply U64; [lia|lia|exact H328]|].
split; [apply (PMFA.accA_agree M M' (op + 320) 64); [intros x Hx; apply SH; lia| exact C320]|].
split; [apply (PMFA.vstr_at_agreeA RSEGS M M' (op + 336)); [lia|lia| split; [intros i Hi; apply AG; lia| intros x Hx; apply SH; lia]| exact AGT| exact TB]|].
split; [apply (vec_at_set_topA (op + 360) (PM.p_b s) (PM.p_k s) pre p p' VEC); [lia|lia|exact Hb|exact Hb'| intros i Hi; apply AG; lia| exact AGL| exact AGH| exact SHB| exact DT| exact PT]|].
split; [exact B1|]. split; [exact B2| exact B3].
Qed.
End S.
End Upd.
End PMBLPK2.
