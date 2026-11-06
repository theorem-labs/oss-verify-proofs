(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim RefMemcpyLib As0StepLib
ArtMem ArtRegs ArtAtomics ArtTac JbtLeaf JbtPoison JbtAllocG.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLiaT.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import OtfKit.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__JbtUnwind () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Init.Nat."; "Corelib.Init.Peano."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.BvBase."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ArtMem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Hoare."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtUnwind."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.StoreOk."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1app"; "1cons"; "1list"; "1nat"; "1nil"; "1option"; "2I"; "2and"; "2eq"; "2ex"; "2not"; "2or"; "3add"; "4le"; "5Z"; "6Z_to_le_bytes"]; ["7bvmap"; "0M"; "0M'"; "8Wn"; "8apart"; "8cell"; "8wr"; "9msteps"; ":ret_ok"; ";readable8"; ";trace_cells"; "<getr"; "<mkst"; "<regupd"; "=mem_grows"; ">loaded_segments"]; ["?In"; "@add"; "@land"; "@le"; "@lt"; "@modulo"; "@mul"; "@of_nat"; "@pow"; "@shiftr"; "@sub"; "@to_nat"; "0a"; "0bot"; "0bp"; "0fx"]; ["0hi"; "0lo"; "0m"; "0n"; "0n1"; "0n2"; "0pc"; "0r"; "0raw"; "0regs"; "0regs'"; "0rom"; "0size"; "0sp"; "ABV"; "AZ_to_bv"]; ["Abv"; "Abv_unsigned"; "0sz"; "0this"; "0top"; "0v"; "0x"; "0z"]]).
Local Ltac oF' pc := oF constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc.
Local Ltac oD' pc := oD constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc.
Local Ltac oE' pc := oE constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc.
Local Ltac oW' pc := oW constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc. Local Ltac lia := L5FastLiaT.plia2.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).
Definition readable8 (M : word -> option byte) (lo hi : Z) : Prop :=
forall a, lo <= a -> a + 8 <= hi -> a mod 8 = 0 -> exists w : word, cellA M a 8 (bv_unsigned w).
Lemma readable8_Wn : ltac2:(TCodec.tc2 tcn__JbtUnwind "QH'3'R0yR0%211'5y8%511%311p051'>&Q3zr4%3221&Q4&Q1r5&Q7r7%211%5241&Q8+2+R0%3221%;251%<2>2';r8r:%=11%@231r6%G221%H2B6%8221&I%138C5&Cr<r;r9%4432=1%731?Ip071p0:1p0D1p0Q21p0G1p0Q41pS2Q91pS4Q:1pT<Q;1pRJQ<1pQ4Q>1pS8QG1").
Proof.
intros n M a v lo hi Ha Hn Hlo Hhi Hap R b Hb1 Hb2 Hb3. destruct (R b Hb1 Hb2 Hb3) as [w C]. exists w.
apply cell_Wn_other; [lia|lia|lia|cbn; lia|unfold apart; cbn; lia|exact C].
Qed.
Definition trace_cells (M : word -> option byte) (this sz : Z) : Prop :=
forall i, 0 <= i < sz -> exists w : word, cellA M (this + 16 + 8 * i) 8 (bv_unsigned w).
Lemma Z_land_upper_7 : ltac2:(TCodec.tc2 tcn__JbtUnwind "<'>&Q3zr1%3221&Q2r2+7%3221%8212p061pRJ;1").
Proof. intros a Ha. rewrite Z.land_comm. change 7 with (Z.ones 3). rewrite Z.land_ones_low || idtac.
pose proof (Z.land_ones a 3 ltac:(lia)). rewrite Z.land_comm in H. rewrite H. change (Z.ones 3) with 7. pose proof (Z.mod_pos_bound a 8 ltac:(lia)). change (2^3) with 8. lia. Qed.
Section FPX. Context {fx : PropExec.FPState}.
#[using="Type"] Lemma art_uwf_loop : ltac2:(TCodec.tc2 tcn__JbtUnwind "W?'3&@y5'R0yR0%211%5241'5y8%611%311p061'>'=&Q;&Q:r2r3%3221%511r9%8221'8&K(QN+:(6%33I21%5281&QOr6%22K1%:3K41r:+;%;3Q119%=231%?3Q016r;+<%@3Q61>%B231%D3Q51;r<+=%E3Q;1C%G231+TP0%C2Q<1%K3Q<31r=+>%L3QB1J%N231&Q1+@%22G1%L2QE1%Q43QE51r>+?%Q53QK1Q3%Q7231r7%Q32QL1%Q;3QL31r?+8%Q<3R21Q:%Q>231+N%Q:2R31%QB3R331r@+9%QC3R91QA%QE231%QN2Q<F%QA2R:1%QI3R:31'7&Q3+1%221QB%32QC>%5221z%621L&Q4&Q8+2+R0%3221%52Q21%>271%>29FrA+X0%Q<221%RD2Q1Q<%C221%=2L2+QO%>2=1%@2O1&Q5rB%221Q8%RF3S01F&F&OrGrE%44321@&IrHrD%S621QNrC%53421&ErI%R42;QGu4%45>3216&JrJ%231<;'9'G&LvQ?rN+cXl8%S>3T21S</01T2rMrL%8576321+cXn4%SD3T81SB/01T8r1%=5<SO216%?3Q261%T>1T?&:%SM325S;%211%SO34T5RH%411%SO3TES0SM%T237T71%711r4+A%T43TJ1T2%T73<31%<11r5%T92S11rQ3%T;213%T=3TN31p061p0<1p0@1p0C1pS@G1&N%12Q2L%SE2Q2S8&R1%12U9O%RM231%SI2Q6T8%RH231%S1231%Q011%SM2Q;SL%82U@U4%S4221%T02Q>RE%RO231%S8231%Q711%Q01U9rQ0%11U;%U73UC31p051p0=1pT>UK1%S@2S?QC%SA2QDSL%SC221%R<5RFUDIR9QF%R83UEQLQG%SF221%SG241qT6UL1%R92UM1%SJ2:1%SK2Q11%SL2Q41%SM2QM1qQ6V31%R?2V41qSFV:1%RA2V;1p0RC1p0RG1p0RM1p0S41p0S:1p0S?1p0SC1p0SE1p0SK1p0SM1p0T71p0T>1p0TF1p0TN1p0U61p0U@1p0UH1p0UN1p0V41p0V@1pSJVJ1pT:VK1pRNVL1pS>VM1pT8VN1pSHW01pQ4W11pSDW71pS6W>1").
Proof.
induction m as [|m IH]; intros regs M rom this pc bp top size Hm H10 H11 H12 H13 H14 H15 H8 H9 Hsz Hpc Hthis Hthis' Hbp Htop Hbp8 W RD CSZ TRC.
{ exfalso. lia. }
destruct (Z.le_gt_cases 30 size) as [Full|Room].
{
eexists _, M. split; [|split; [|split; [apply mem_grows_refl | split; [intros; reflexivity | exists size; split; [lia | split; [exact CSZ | exact TRC]]]]]].
- zbtk (ltac:(oF' 0x9a388%Z)) (ltac:(oD' 0x9a388%Z)). apply mst_refl.
- intros; reflexivity. }
pose proof RD as RDu. unfold readable8 in RDu.
destruct (RDu (bp - 8) ltac:(lia) ltac:(lia) ltac:(lia)) as [w1 C1].
destruct (RDu (bp - 16) ltac:(lia) ltac:(lia) ltac:(lia)) as [w2 C2].
pose proof (u64_range w1) as R1. pose proof (u64_range w2) as R2.
destruct (Z.lt_ge_cases (U w1) 4096) as [Lowpc|Okpc].
{
eexists _, M. split; [|split; [|split; [apply mem_grows_refl | split; [intros; reflexivity | exists size; split; [lia | split; [exact CSZ | exact TRC]]]]]].
- zbft (ltac:(oF' 0x9a388%Z)) (ltac:(oD' 0x9a388%Z)). zld (ltac:(oF' 0x9a38c%Z)) (ltac:(oD' 0x9a38c%Z)) (bp - 8) C1. zbtk (ltac:(oF' 0x9a390%Z)) (ltac:(oD' 0x9a390%Z)). apply mst_refl.
- intros; kept_solve. }
assert (STEP : exists regs1 M1,
msteps ASEGS (mkst regs (0x9a388 : word) M rom) (mkst regs1 (0x9a3ac : word) M1 rom)
/\ getr regs1 10 = Z_to_bv 64 this /\ getr regs1 11 = Z_to_bv 64 pc /\ getr regs1 12 = Z_to_bv 64 bp /\ getr regs1 13 = Z_to_bv 64 4096
/\ getr regs1 14 = Z_to_bv 64 (this + 16) /\ (exists size1, getr regs1 15 = Z_to_bv 64 size1 /\ size <= size1 <= size + 1)
/\ getr regs1 8 = Z_to_bv 64 30 /\ getr regs1 9 = Z_to_bv 64 (top - 16)
/\ (forall r : reg, r <> 12%bv -> r <> 15%bv -> r <> 16%bv -> r <> 17%bv -> getr regs1 r = getr regs r)
/\ mem_grows M M1 /\ (forall x : word, ~ (this + 8 <= U x < this + 12) -> ~ (this + 16 <= U x < this + 256) -> M1 x = M x)
/\ wrA M1 this 256 /\ readable8 M1 (bp - 16) top /\ (exists size1, size <= size1 <= size + 1 /\ cellA M1 (this + 8) 4 size1 /\ getr regs1 15 = Z_to_bv 64 size1 /\ trace_cells M1 this size1)).
{ destruct (Z.eq_dec (U w1) pc) as [Same|Diff].
- eexists _, M. split.
{ zbft (ltac:(oF' 0x9a388%Z)) (ltac:(oD' 0x9a388%Z)). zld (ltac:(oF' 0x9a38c%Z)) (ltac:(oD' 0x9a38c%Z)) (bp - 8) C1. zbft (ltac:(oF' 0x9a390%Z)) (ltac:(oD' 0x9a390%Z)). zbtk (ltac:(oF' 0x9a394%Z)) (ltac:(oD' 0x9a394%Z)). apply mst_refl. }
repeat (split; [gres; rwH; first [reflexivity | f_equal; lia]|]). split. { exists size. split; [gres; rwH; reflexivity|lia]. }
repeat (split; [gres; rwH; first [reflexivity | f_equal; lia]|]). split. { intros; kept_solve. }
split; [apply mem_grows_refl|]. split; [intros; reflexivity|]. split; [assumption|]. split; [assumption|]. exists size. split; [lia|]. split; [exact CSZ | split; [gres; rwH; reflexivity | exact TRC]].
- eexists _, _. split.
{ zbft (ltac:(oF' 0x9a388%Z)) (ltac:(oD' 0x9a388%Z)). zld (ltac:(oF' 0x9a38c%Z)) (ltac:(oD' 0x9a38c%Z)) (bp - 8) C1. zbft (ltac:(oF' 0x9a390%Z)) (ltac:(oD' 0x9a390%Z)). zbft (ltac:(oF' 0x9a394%Z)) (ltac:(oD' 0x9a394%Z)).
zstep (ltac:(oF' 0x9a398%Z)) (ltac:(oD' 0x9a398%Z)). zstep (ltac:(oF' 0x9a39c%Z)) (ltac:(oD' 0x9a39c%Z)). zstep (ltac:(oF' 0x9a3a0%Z)) (ltac:(oD' 0x9a3a0%Z)).
zsw (ltac:(oF' 0x9a3a4%Z)) (ltac:(oD' 0x9a3a4%Z)) (this + 8) (size + 1) ltac:(rewok W).
zsd (ltac:(oF' 0x9a3a8%Z)) (ltac:(oD' 0x9a3a8%Z)) (this + 16 + size * 8) (U w1) ltac:(rewok W).
apply mst_refl. }
repeat (split; [gres; rwH; first [reflexivity | f_equal; lia]|]). split. { exists (size + 1). split; [gres; rwH; first [reflexivity | f_equal; lia]|lia]. }
repeat (split; [gres; rwH; first [reflexivity | f_equal; lia]|]). split. { intros; kept_solve. }
split. { eapply mem_grows_trans; apply Wn_grows. }
split. { intros x Hx Hx'. rewrite !Wn_outside by (cbn; lia). reflexivity. }
split. { zwr. }
split. { apply readable8_Wn; try (cbn; lia). apply readable8_Wn; try (cbn; lia). exact RD. }
exists (size + 1). split; [lia|]. split; [|split; [gres; rwH; f_equal; lia|]].
{ apply cell_Wn_other; [lia|cbn; lia|lia|cbn; lia|unfold apart; cbn; lia|]. apply cell_Wn_hit; cbn; lia. }
intros i Hi. destruct (Z.eq_dec i size) as [->|Hne].
+ exists w1. replace (this + 16 + 8 * size) with (this + 16 + size * 8) by lia. apply cell_Wn_hit; cbn; lia.
+ destruct (TRC i ltac:(lia)) as [w Cw]. exists w.
apply cell_Wn_other; [lia|cbn; lia|lia|cbn; lia|unfold apart; cbn; lia|]. apply cell_Wn_other; [lia|cbn; lia|lia|cbn; lia|unfold apart; cbn; lia|]. exact Cw. }
destruct STEP as (regs1 & M1 & RUN1 & P10 & P11 & P12 & P13 & P14 & (size1 & P15 & Hs1) & P8 & P9 & K1 & G1 & A1 & W1 & RD1 & (size1' & Hs1' & CS1 & P15' & TRC1)).
assert (Esz : size1' = size1). { rewrite P15 in P15'. apply (f_equal bv_unsigned) in P15'. rewrite !art_u_lit in P15' by lia. lia. } subst size1'.
assert (C2' : cellA M1 (bp - 16) 8 (U w2)).
{ apply (cell_agree M M1); [|lia|cbn; lia|exact C2]. intros x Hx. apply A1; cbn in Hx; lia. }
destruct (Z.le_gt_cases (U w2) bp) as [Back|Fwd].
{ eexists _, M1. split; [|split; [|split; [exact G1 | split; [exact A1 | exists size1; split; [lia | split; [exact CS1 | exact TRC1]]]]]].
- eapply msteps_trans; [exact RUN1|]. zld (ltac:(oF' 0x9a3ac%Z)) (ltac:(oD' 0x9a3ac%Z)) (bp - 16) C2'. zbtk (ltac:(oF' 0x9a3b0%Z)) (ltac:(oD' 0x9a3b0%Z)). apply mst_refl.
- intros; rewrite <- (K1 r) by assumption; kept_solve. }
destruct (Z.le_gt_cases (top - 16) (U w2)) as [High|Inr].
{ eexists _, M1. split; [|split; [|split; [exact G1 | split; [exact A1 | exists size1; split; [lia | split; [exact CS1 | exact TRC1]]]]]].
- eapply msteps_trans; [exact RUN1|]. zld (ltac:(oF' 0x9a3ac%Z)) (ltac:(oD' 0x9a3ac%Z)) (bp - 16) C2'. zbft (ltac:(oF' 0x9a3b0%Z)) (ltac:(oD' 0x9a3b0%Z)). zbtk (ltac:(oF' 0x9a3b4%Z)) (ltac:(oD' 0x9a3b4%Z)). apply mst_refl.
- intros; rewrite <- (K1 r) by assumption; kept_solve. }
destruct (Z.eq_dec (U w2 mod 8) 0) as [Al|Nal].
-
assert (Hland : Z.land (U w2) 7 = 0). { change 7 with (Z.ones 3). rewrite Z.land_ones by lia. exact Al. }
assert (RUNm : exists regs2, msteps ASEGS (mkst regs1 (0x9a3ac : word) M1 rom) (mkst regs2 (0x9a388 : word) M1 rom)
/\ getr regs2 10 = Z_to_bv 64 this /\ getr regs2 11 = Z_to_bv 64 pc /\ getr regs2 12 = Z_to_bv 64 (U w2) /\ getr regs2 13 = Z_to_bv 64 4096
/\ getr regs2 14 = Z_to_bv 64 (this + 16) /\ getr regs2 15 = Z_to_bv 64 size1 /\ getr regs2 8 = Z_to_bv 64 30 /\ getr regs2 9 = Z_to_bv 64 (top - 16)
/\ (forall r : reg, r <> 12%bv -> r <> 16%bv -> r <> 17%bv -> getr regs2 r = getr regs1 r)).
{ eexists. split.
{ zld (ltac:(oF' 0x9a3ac%Z)) (ltac:(oD' 0x9a3ac%Z)) (bp - 16) C2'. zbft (ltac:(oF' 0x9a3b0%Z)) (ltac:(oD' 0x9a3b0%Z)). zbft (ltac:(oF' 0x9a3b4%Z)) (ltac:(oD' 0x9a3b4%Z)).
stepn (ltac:(oF' 0x9a3b8%Z)) (ltac:(oD' 0x9a3b8%Z)). rwH. rewrite art_zb_andi by lia. rewrite Hland.
zstep (ltac:(oF' 0x9a3bc%Z)) (ltac:(oD' 0x9a3bc%Z)). zbtk (ltac:(oF' 0x9a3c0%Z)) (ltac:(oD' 0x9a3c0%Z)). apply mst_refl. }
repeat (split; [gres; rwH; first [reflexivity | rewrite Z_to_bv_bv_unsigned; reflexivity | f_equal; lia]|]). intros; kept_solve. }
destruct RUNm as (regs2 & RUNm & T10 & T11 & T12 & T13 & T14 & T15 & T8 & T9 & Km).
destruct (IH regs2 M1 rom this pc (U w2) top size1 ltac:(lia) T10 T11 T12 T13 T14 T15 T8 T9
ltac:(lia) Hpc Hthis ltac:(lia) ltac:(lia) Htop Al W1
ltac:(intros b Hb1 Hb2 Hb3; unfold readable8 in RD1; apply RD1; lia) CS1 TRC1) as (regs' & M' & RUN2 & K2 & G2 & A2 & SZ2).
exists regs', M'. split; [|split; [|split; [|split]]].
+ eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUNm|]. exact RUN2.
+ intros r N12 N15 N16 N17. rewrite K2 by assumption. rewrite Km by assumption. apply K1; assumption.
+ eapply mem_grows_trans; [exact G1 | exact G2].
+ intros x Hx Hx'. rewrite A2 by assumption. apply A1; assumption.
+ exact SZ2.
-
assert (Hland : Z.land (U w2) 7 <> 0). { change 7 with (Z.ones 3). rewrite Z.land_ones by lia. exact Nal. }
pose proof (Z_land_upper_7 (U w2) ltac:(lia)) as Lu. pose proof (proj2 (Z.land_nonneg (U w2) 7) ltac:(left; lia)) as Ln.
eexists _, M1. split; [|split; [|split; [exact G1 | split; [exact A1 | exists size1; split; [lia | split; [exact CS1 | exact TRC1]]]]]].
+ eapply msteps_trans; [exact RUN1|]. zld (ltac:(oF' 0x9a3ac%Z)) (ltac:(oD' 0x9a3ac%Z)) (bp - 16) C2'. zbft (ltac:(oF' 0x9a3b0%Z)) (ltac:(oD' 0x9a3b0%Z)). zbft (ltac:(oF' 0x9a3b4%Z)) (ltac:(oD' 0x9a3b4%Z)).
stepn (ltac:(oF' 0x9a3b8%Z)) (ltac:(oD' 0x9a3b8%Z)). rwH. rewrite art_zb_andi by lia.
zstep (ltac:(oF' 0x9a3bc%Z)) (ltac:(oD' 0x9a3bc%Z)).
stepb_ft (ltac:(oF' 0x9a3c0%Z)) (ltac:(oD' 0x9a3c0%Z)) ltac:(rwH; rewrite art_c_eq_zb by lia; apply Z.eqb_neq; exact Hland).
apply mst_refl.
+ intros; rewrite <- (K1 r) by assumption; kept_solve.
Qed.
End FPX.
Lemma Z_to_le_bytes_add : ltac2:(TCodec.tc2 tcn__JbtUnwind "N'3'>'8'2'R0y8%211%411&?&<r3r2%3221r1%6221&0%8263&Q9&Q6+8&Q7%11;%4231%62:1%@2=1%:3C91%H3C<1pT@J1pS<L1pS:M1").
Proof.
induction n1 as [|n1 IH]; intros n2 z.
- cbn [Nat.add app Z.of_nat Z.mul]. rewrite Z.shiftr_0_r. reflexivity.
- cbn [Nat.add Z_to_le_bytes app]. f_equal. rewrite IH. f_equal. rewrite Z.shiftr_shiftr by lia. f_equal. f_equal. lia.
Qed.
Lemma cell8_of_cells4 : ltac2:(TCodec.tc2 tcn__JbtUnwind "QH'R0yR0%211'5y8%511%311p051'>&Q3zr3%3221&Q4&Q1r4+8%3221&Q8+2+R0%3221%9251'7%?2>9+Q0%8271%>2<1%5241&E&Or8r7u4r6%6554321r9+4%H271%:593165r:u8&Q6%12;A%N2=1%@5?5941p071p0<1p0D1p0E1p0L1p0Q71pS2Q<1pS4Q=1pRJQ>1pQ4Q@1").
Proof.
intros M a lo hi Ha Ha' Hlo Hhi C1 C2. unfold cell in *.
change 8%nat with (4 + 4)%nat. erewrite rdn_app; [|exact C1|].
2: { replace (Z_to_bv 64 a + nat_to_word 4)%bv with (Z_to_bv 64 (a + 4) : word); [exact C2|].
apply bv_eq. unfold nat_to_word. rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64). cbn [Z.of_nat Pos.of_succ_nat Pos.succ].
rewrite (Z.mod_small 4) by lia. rewrite (Z.mod_small a) by lia. rewrite Z.mod_small by lia. reflexivity. }
f_equal. unfold word_to_le_bytes. rewrite !art_u_lit by lia. rewrite (Z_to_le_bytes_add 4 4). f_equal.
- rewrite <- (Z_to_le_bytes_wrap 4 32 (lo + hi * 2 ^ 32)) by (cbn; lia). rewrite <- (Z_to_le_bytes_wrap 4 32 lo) by (cbn; lia). f_equal.
unfold bv_wrap. change (bv_modulus 32) with (2 ^ 32). rewrite Z.mod_add by lia. reflexivity.
- f_equal. change (8 * Z.of_nat 4) with 32. rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_add by lia. rewrite Z.div_small by lia. lia.
Qed.
Section FPX2. Context {fx : PropExec.FPState}.
Section SE.
Local Abbreviation SEC_T_art_unwind_fast_run := (ltac2:(TCodec.tc2 tcn__JbtUnwind "Y0&@y5'R0yR0%211%5241'5y8%611%311p061'>'8&Kr:(QN+1(6%33A21%6251r7%93A21&Hr8%211r<+2%<3J1:%?231&QO%12K7%C3K31r=+:%C3Q11A%F231%H3Q016r>+;%H3Q61F%K231%M3Q51;r?+<%M3Q;1K%Q0231%Q23Q:1@r@+=%Q23Q@1Q0%Q5231%Q73Q?1ErA+>%Q73QE1Q5%Q:231%Q<3QD1JrB+?%Q<3QJ1Q:%Q?231+N%Q12QK1%QC3QK31&Q3+R0%221H&Q1%12E3%521K+RP@%42H1&Q:+@%22Q51%;241z%=21Q=&Q4%12Q:Q0%82Q17%32M1&Q8+QO%22QJ1%72Q11&Q5rC+8%3221%R>3R?1>'7rE%M2A1%<2R4M%A231%5231+Vb\P0%O21Q1rH%Q4221&F&OrLrI%Q121Q8%54431Q9rM+X0%847251&IrN%Q82=Q7rG%43321&ErO+QV`l0u8+QiaW0%55B4321rQ0+TP0%85E2451'9'G&LvQ?rQ4+cXf8%SC3SO1SA/01SOrQ3rQ2%8576321r2rQ1r1%<5;3215%>3Q551%SO25SA%S@2T:D%T23T:21%T228SM%T43T<18%T?1T@&Q0(1%T53TCQLT3+9%T73TE1T5+B%T93TG1T7+C%T;3TI1T9+D%T=3TK1T;+E%T?3TM1T=+F%TA3TO1T?+G%TC3U11TA+H%TE3U31TC+I%TG3U51TE+J%TI3U71TG+K%TK3U91TI+3%TM3U;1TK+4%TO3U=1TM(4%11O%N3Q031%O3Q161%Q03Q291%Q13Q3<1%Q23Q4?1%Q33Q5B1%Q43Q6E1%Q53Q7H1%Q63Q8K1%Q73Q9N1%Q83Q:Q11%Q93Q;Q41%Q:3Q<Q71%Q;3Q=Q:1%Q=3Q>QF1r4%UD21QJrQ6%UF21QL%UH3V031p061pS@QE1&N%12R4QO&:%T72RASB&R1%12V9R3%T=231%T;2REU3%T1231%SE231%811%T?2R:T9%82V@R<%TD221%TB2R=S9%T8231%SL231%?11%TA2RETHr3%@2VH1%TL231%T?22RI%T3221%F11r5%11Q1rQ7%11Q3%VH3VK31p061p0>1p0F1pT>W41%U92VIS0%U:2S1U=%T@221u4%SJ5T7S6Q31S4&J%13S8SFS6%TE231%TF261qT6W71%SG2W81%TI2<1%TJ2Q=1%TK2Q@1%TL2S71%TM2S:1%TN2S>1qQ6W@1%SO2WA1qSFWG1%T12WH1p0T31p0T71p0T>1p0TD1p0TH1p0TO1p0U41p0U;1p0UA1p0UF1p0UI1p0UL1p0UO1p0V61p0V:1p0V>1p0VF1p0VL1p0W21p0W81p0W>1p0WD1p0WL1p0X01pRLX;1pT:X<1pRNX=1pS>X>1pT8X?1pSLX@1pSBXH1pSHXC1pQ4XD1pSDXJ1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_unwind_fast_run) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_unwind_fast_run) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_unwind_fast_run) 2%nat 0%nat).
Variable raw : ltac:(sec_ty2 constr:(SEC_T_art_unwind_fast_run) 3%nat 0%nat).
Variable sp : ltac:(sec_ty2 constr:(SEC_T_art_unwind_fast_run) 4%nat 0%nat).
Variable this : ltac:(sec_ty2 constr:(SEC_T_art_unwind_fast_run) 5%nat 0%nat).
Variable pc : ltac:(sec_ty2 constr:(SEC_T_art_unwind_fast_run) 6%nat 0%nat).
Variable bp : ltac:(sec_ty2 constr:(SEC_T_art_unwind_fast_run) 7%nat 0%nat).
Variable top : ltac:(sec_ty2 constr:(SEC_T_art_unwind_fast_run) 8%nat 0%nat).
Variable bot : ltac:(sec_ty2 constr:(SEC_T_art_unwind_fast_run) 9%nat 0%nat).
Lemma art_unwind_fast_run : ltac:(sec_stmt2 constr:(SEC_T_art_unwind_fast_run) 10%nat 0%nat).
Proof using Type regs M rom raw sp this pc bp top bot.
intros H1 Hret H2 H10 H11 H12 H13 H14 H15 Hsp Hsp' Hthis Hbot Hbot' Hbp Htop Hbp8 Hpc IMG W Wt RD Cg Cps.
assert (PRE : exists regs1 M1, msteps ASEGS (mkst regs (0x9a2c8 : word) M rom) (mkst regs1 (0x9a388 : word) M1 rom)
/\ getr regs1 10 = Z_to_bv 64 this /\ getr regs1 11 = Z_to_bv 64 pc /\ getr regs1 12 = Z_to_bv 64 bp /\ getr regs1 13 = Z_to_bv 64 4096
/\ getr regs1 14 = Z_to_bv 64 (this + 16) /\ getr regs1 15 = Z_to_bv 64 1 /\ getr regs1 8 = Z_to_bv 64 30 /\ getr regs1 9 = Z_to_bv 64 (top - 16)
/\ getr regs1 2 = Z_to_bv 64 (sp - 64)
/\ (forall r : reg, In r [3; 4; 23; 24; 25; 26; 27]%bv -> getr regs1 r = getr regs r)
/\ M1 = Wn 8 (Wn 4 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 M (sp - 8) (U raw)) (sp - 16) (U (getr regs 8))) (sp - 24) (U (getr regs 9))) (sp - 32) (U (getr regs 18)))
(sp - 40) (U (getr regs 19))) (sp - 48) (U (getr regs 20))) (sp - 56) (U (getr regs 21))) (sp - 64) (U (getr regs 22))) (this + 8) 1) (this + 16) pc).
{ eexists _, _. split.
- zstep (ltac:(oF' 0x9a2c8%Z)) (ltac:(oD' 0x9a2c8%Z)).
zsd (ltac:(oF' 0x9a2cc%Z)) (ltac:(oD' 0x9a2cc%Z)) (sp - 8) (U raw) ltac:(rewok W). zsd (ltac:(oF' 0x9a2d0%Z)) (ltac:(oD' 0x9a2d0%Z)) (sp - 16) (U (getr regs 8)) ltac:(rewok W).
zsd (ltac:(oF' 0x9a2d4%Z)) (ltac:(oD' 0x9a2d4%Z)) (sp - 24) (U (getr regs 9)) ltac:(rewok W). zsd (ltac:(oF' 0x9a2d8%Z)) (ltac:(oD' 0x9a2d8%Z)) (sp - 32) (U (getr regs 18)) ltac:(rewok W).
zsd (ltac:(oF' 0x9a2dc%Z)) (ltac:(oD' 0x9a2dc%Z)) (sp - 40) (U (getr regs 19)) ltac:(rewok W). zsd (ltac:(oF' 0x9a2e0%Z)) (ltac:(oD' 0x9a2e0%Z)) (sp - 48) (U (getr regs 20)) ltac:(rewok W).
zsd (ltac:(oF' 0x9a2e4%Z)) (ltac:(oD' 0x9a2e4%Z)) (sp - 56) (U (getr regs 21)) ltac:(rewok W). zsd (ltac:(oF' 0x9a2e8%Z)) (ltac:(oD' 0x9a2e8%Z)) (sp - 64) (U (getr regs 22)) ltac:(rewok W).
zstep (ltac:(oF' 0x9a2ec%Z)) (ltac:(oD' 0x9a2ec%Z)). zstep (ltac:(oF' 0x9a2f0%Z)) (ltac:(oD' 0x9a2f0%Z)). zstep (ltac:(oF' 0x9a2f4%Z)) (ltac:(oD' 0x9a2f4%Z)). zstep (ltac:(oF' 0x9a2f8%Z)) (ltac:(oD' 0x9a2f8%Z)).
zbft (ltac:(oF' 0x9a2fc%Z)) (ltac:(oD' 0x9a2fc%Z)).
match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cg' : cellA X 0x134380 8 0x1cc4e0) by (recell Cg); assert (Cps' : cellA X 0x1cc4e0 8 4096) by (recell Cps) end.
zstep (ltac:(oF' 0x9a300%Z)) (ltac:(oD' 0x9a300%Z)). zld (ltac:(oF' 0x9a304%Z)) (ltac:(oD' 0x9a304%Z)) 0x134380 Cg'. zld (ltac:(oF' 0x9a308%Z)) (ltac:(oD' 0x9a308%Z)) 0x1cc4e0 Cps'.
zbft (ltac:(oF' 0x9a30c%Z)) (ltac:(oD' 0x9a30c%Z)).
zstep (ltac:(oF' 0x9a310%Z)) (ltac:(oD' 0x9a310%Z)).
stepn (ltac:(oF' 0x9a314%Z)) (ltac:(oD' 0x9a314%Z)). rwH. rewrite art_zb_srli by lia.
zsw (ltac:(oF' 0x9a318%Z)) (ltac:(oD' 0x9a318%Z)) (this + 8) 1 ltac:(rewok Wt).
zsd (ltac:(oF' 0x9a31c%Z)) (ltac:(oD' 0x9a31c%Z)) (this + 16) pc ltac:(rewok Wt).
assert (Htop12 : 1 <= top / 2 ^ 12) by (apply Z.div_le_lower_bound; lia). assert (Htop12' : top / 2 ^ 12 < 2 ^ 52) by (apply Z.div_lt_upper_bound; lia). pose proof (art_u_lit top ltac:(lia)).
zbtk (ltac:(oF' 0x9a320%Z)) (ltac:(oD' 0x9a320%Z)).
zbft (ltac:(oF' 0x9a368%Z)) (ltac:(oD' 0x9a368%Z)). zbft (ltac:(oF' 0x9a36c%Z)) (ltac:(oD' 0x9a36c%Z)).
zstep (ltac:(oF' 0x9a370%Z)) (ltac:(oD' 0x9a370%Z)).
zbft (ltac:(oF' 0x9a374%Z)) (ltac:(oD' 0x9a374%Z)).
stepn (ltac:(oF' 0x9a378%Z)) (ltac:(oD' 0x9a378%Z)). rwH. rewrite art_zb_andi by lia. replace (Z.land bp 7) with 0 by (change 7 with (Z.ones 3); rewrite Z.land_ones by lia; change (2 ^ 3) with 8; lia).
zbft (ltac:(oF' 0x9a37c%Z)) (ltac:(oD' 0x9a37c%Z)).
zstep (ltac:(oF' 0x9a380%Z)) (ltac:(oD' 0x9a380%Z)). zstep (ltac:(oF' 0x9a384%Z)) (ltac:(oD' 0x9a384%Z)).
apply mst_refl.
- repeat (split; [gres; rwH; first [reflexivity | f_equal; lia]|]).
split. { intros r Hr. cbn [In] in Hr. destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]; gres; reflexivity. } reflexivity. }
destruct PRE as (regs1 & M1 & RUN1 & P10 & P11 & P12 & P13 & P14 & P15 & P8 & P9 & P2 & PK & EM1).
assert (W1 : wrA M1 this 256) by (rewrite EM1; zwr).
assert (RD1 : readable8 M1 (bp - 16) top).
{ rewrite EM1. do 10 (apply readable8_Wn; [cbn; lia|cbn; lia|lia|lia|cbn; lia|]). exact RD. }
destruct (art_uwf_loop (Z.to_nat (top - bp)) regs1 M1 rom this pc bp top 1 ltac:(lia) P10 P11 P12 P13 P14 P15 P8 P9
ltac:(lia) Hpc ltac:(lia) ltac:(lia) Hbp Htop Hbp8 W1 RD1 ltac:(rewrite EM1; zcell)
ltac:(intros i Hi; exists (Z_to_bv 64 pc); rewrite art_u_lit by lia; replace (this + 16 + 8 * i) with (this + 16) by lia; rewrite EM1; zcell)) as (regs2 & M2 & RUN2 & K2 & G2 & A2 & SZ2).
assert (FR : forall off v, 0 <= off <= 56 -> cellA M1 (sp - 64 + off) 8 v -> cellA M2 (sp - 64 + off) 8 v).
{ intros off v Hoff C. apply (cell_agree M1 M2); [|lia|cbn; lia|exact C]. intros x Hx. apply A2; cbn in Hx; lia. }
assert (C56 : cellA M2 (sp - 64 + 56) 8 (U raw)) by (apply FR; [lia|]; rewrite EM1; replace (sp - 64 + 56) with (sp - 8) by lia; zcell).
assert (C48 : cellA M2 (sp - 64 + 48) 8 (U (getr regs 8))) by (apply FR; [lia|]; rewrite EM1; replace (sp - 64 + 48) with (sp - 16) by lia; zcell).
assert (C40 : cellA M2 (sp - 64 + 40) 8 (U (getr regs 9))) by (apply FR; [lia|]; rewrite EM1; replace (sp - 64 + 40) with (sp - 24) by lia; zcell).
assert (C32 : cellA M2 (sp - 64 + 32) 8 (U (getr regs 18))) by (apply FR; [lia|]; rewrite EM1; replace (sp - 64 + 32) with (sp - 32) by lia; zcell).
assert (C24 : cellA M2 (sp - 64 + 24) 8 (U (getr regs 19))) by (apply FR; [lia|]; rewrite EM1; replace (sp - 64 + 24) with (sp - 40) by lia; zcell).
assert (C16 : cellA M2 (sp - 64 + 16) 8 (U (getr regs 20))) by (apply FR; [lia|]; rewrite EM1; replace (sp - 64 + 16) with (sp - 48) by lia; zcell).
assert (C08 : cellA M2 (sp - 64 + 8) 8 (U (getr regs 21))) by (apply FR; [lia|]; rewrite EM1; replace (sp - 64 + 8) with (sp - 56) by lia; zcell).
assert (C00 : cellA M2 (sp - 64 + 0) 8 (U (getr regs 22))) by (apply FR; [lia|]; rewrite EM1; replace (sp - 64 + 0) with (sp - 64) by lia; zcell).
assert (Q2 : getr regs2 2 = Z_to_bv 64 (sp - 64)) by (rewrite K2 by discriminate; exact P2).
eexists _, M2. split.
{ eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|].
zld (ltac:(oF' 0x9a3c4%Z)) (ltac:(oD' 0x9a3c4%Z)) (sp - 64 + 56) C56. rewrite Z_to_bv_bv_unsigned.
zld (ltac:(oF' 0x9a3c8%Z)) (ltac:(oD' 0x9a3c8%Z)) (sp - 64 + 48) C48. rewrite Z_to_bv_bv_unsigned.
zld (ltac:(oF' 0x9a3cc%Z)) (ltac:(oD' 0x9a3cc%Z)) (sp - 64 + 40) C40. rewrite Z_to_bv_bv_unsigned.
zld (ltac:(oF' 0x9a3d0%Z)) (ltac:(oD' 0x9a3d0%Z)) (sp - 64 + 32) C32. rewrite Z_to_bv_bv_unsigned.
zld (ltac:(oF' 0x9a3d4%Z)) (ltac:(oD' 0x9a3d4%Z)) (sp - 64 + 24) C24. rewrite Z_to_bv_bv_unsigned.
zld (ltac:(oF' 0x9a3d8%Z)) (ltac:(oD' 0x9a3d8%Z)) (sp - 64 + 16) C16. rewrite Z_to_bv_bv_unsigned.
zld (ltac:(oF' 0x9a3dc%Z)) (ltac:(oD' 0x9a3dc%Z)) (sp - 64 + 8) C08. rewrite Z_to_bv_bv_unsigned.
zld (ltac:(oF' 0x9a3e0%Z)) (ltac:(oD' 0x9a3e0%Z)) (sp - 64 + 0) C00. rewrite Z_to_bv_bv_unsigned.
zstep (ltac:(oF' 0x9a3e4%Z)) (ltac:(oD' 0x9a3e4%Z)).
stepret (ltac:(oF' 0x9a3e8%Z)) (ltac:(oD' 0x9a3e8%Z)) raw ltac:(rwH; reflexivity).
apply mst_refl. }
split. { gres. f_equal. lia. }
split. { gres. reflexivity. }
split. { intros r Hr. cbn [In] in Hr. destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]]; gres;
first [reflexivity | rewrite Z_to_bv_bv_unsigned; reflexivity | rewrite K2 by discriminate; apply PK; cbn; tauto]. }
split. { eapply mem_grows_trans; [|exact G2]. rewrite EM1. repeat (eapply mem_grows_trans; [|apply Wn_grows]). apply mem_grows_refl. }
split. { intros x N1 N2 N3. rewrite A2 by assumption. rewrite EM1. rewrite !Wn_outside by (cbn; lia). reflexivity. }
exact SZ2.
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_art_unwind_fn := (ltac2:(TCodec.tc2 tcn__JbtUnwind "W4&@y5'R0yR0%211%5241'5y8%611%311p061'>'8&Kr:(QN+1(6%33A21%6251r7%93A21r;+2%93G17%<231&QO%12H7%@3H31r<+:%@3N1>%C231%E3M16r=+;%E3Q31C%H231+N%=2Q41%L3Q431r>+<%L3Q:1J%O231r8%D2Q;1%Q33Q;31r?+=%Q33QA1Q1%Q6231%Q83Q@16r@+>%Q83QF1Q6%Q;231z%Q02QG1%Q?3QG31rA+?%Q?3QM1Q=%QB231r9%Q72QN1%QF3QN31rB+@%QF3R41QD%QI231%QK3R316rC+A%QK3R91QI%QN231%QB2R9QL%R13R921&Q3+R0%221K&Q4&Q8%12QL4%32H1%72LI&Q1+RP@%22E1%8216'7%1267&D&Q:rE%221@rD%542B1:&F&OrIrF%921G%54431HrJ%74614B'G&LvQ?rL+cZY4%S03S<1RN/01S<rK%756521:&M%137S2@rH%RL2SC1%433RO1+5%S:3SH1S8rG+QoO%Q6221%S32SJ1%;3751+6%SA3SO1S?%S72SNQ3%?3421+8%SE3T31SC%SH2H1%C3421+9%SI3T71SG%SL2L1%G3421%SA2T8Q6%I32S81%J31S2<%SD2T;Q>%L32RM1%SF2T=R8%N32RJ1%O31RDS;+B%T53TC1T3%T82Q81%Q33421+C%T93TG1T7%T<2Q<1%Q73421+D%T=3TK1T;%T@2Q@1%Q;3421+E%TA3TO1T?%TD2QD1%Q?3421+cXf8%TE3U11TC/01U1&Cu8%R;2QCQ5&R1%12U7R6%544QJ31%R?2QGS8%42U:Q8%847321+H%RC2QK1%82U>Q8%<4;421+Q0%RG2QO1%<2UBQ0%@4?421+Q8%RK2R31%@2UFQ0%D4C421+Q@%RO2R71%D2UJQ0%H4G421+QH%S32R;1%H2UNQ0%L4K421+RP8%S>2R:1%O4N31S7%RK5RJQ4Q11RN%RM3S4RE1p0RO1p0S21p0S91p0S@1p0SC1p0SH1p0SJ1p0SO1p0T31p0T:1p0T@1p0TH1p0U01p0U61p0U>1p0UF1p0UL1p0V41pRLV?1pT:V@1pRNVA1pS>VB1pT8VC1pSLVD1pSBVL1pSHVG1pQ4VH1pSDVN1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_unwind_fn) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_unwind_fn) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_unwind_fn) 2%nat 0%nat).
Variable raw : ltac:(sec_ty2 constr:(SEC_T_art_unwind_fn) 3%nat 0%nat).
Variable sp : ltac:(sec_ty2 constr:(SEC_T_art_unwind_fn) 4%nat 0%nat).
Variable this : ltac:(sec_ty2 constr:(SEC_T_art_unwind_fn) 5%nat 0%nat).
Variable pc : ltac:(sec_ty2 constr:(SEC_T_art_unwind_fn) 6%nat 0%nat).
Variable bp : ltac:(sec_ty2 constr:(SEC_T_art_unwind_fn) 7%nat 0%nat).
Variable top : ltac:(sec_ty2 constr:(SEC_T_art_unwind_fn) 8%nat 0%nat).
Variable bot : ltac:(sec_ty2 constr:(SEC_T_art_unwind_fn) 9%nat 0%nat).
Lemma art_unwind_fn : ltac:(sec_stmt2 constr:(SEC_T_art_unwind_fn) 10%nat 0%nat).
Proof using Type regs M rom raw sp this pc bp top bot.
intros H1 H2 H10 H11 H12 H13 H14 H15 H16 H17 Hsp Hsp' Hthis Hthis' Hbp Ap W Wt.
zstep (ltac:(oF' 0x9a924%Z)) (ltac:(oD' 0x9a924%Z)).
zsd (ltac:(oF' 0x9a928%Z)) (ltac:(oD' 0x9a928%Z)) (sp - 8) (U raw) ltac:(rewok W). zsd (ltac:(oF' 0x9a92c%Z)) (ltac:(oD' 0x9a92c%Z)) (sp - 16) (U (getr regs 8)) ltac:(rewok W).
zsd (ltac:(oF' 0x9a930%Z)) (ltac:(oD' 0x9a930%Z)) (sp - 24) (U (getr regs 9)) ltac:(rewok W). zsd (ltac:(oF' 0x9a934%Z)) (ltac:(oD' 0x9a934%Z)) (sp - 32) (U (getr regs 18)) ltac:(rewok W).
zsd (ltac:(oF' 0x9a938%Z)) (ltac:(oD' 0x9a938%Z)) (sp - 40) (U (getr regs 19)) ltac:(rewok W). zsd (ltac:(oF' 0x9a93c%Z)) (ltac:(oD' 0x9a93c%Z)) (sp - 48) (U (getr regs 20)) ltac:(rewok W).
zsd (ltac:(oF' 0x9a940%Z)) (ltac:(oD' 0x9a940%Z)) (sp - 56) (U (getr regs 21)) ltac:(rewok W).
zstep (ltac:(oF' 0x9a944%Z)) (ltac:(oD' 0x9a944%Z)). zstep (ltac:(oF' 0x9a948%Z)) (ltac:(oD' 0x9a948%Z)). zstep (ltac:(oF' 0x9a94c%Z)) (ltac:(oD' 0x9a94c%Z)). zstep (ltac:(oF' 0x9a950%Z)) (ltac:(oD' 0x9a950%Z)).
stepn (ltac:(oF' 0x9a954%Z)) (ltac:(oD' 0x9a954%Z)). rwH. rewrite art_zb_and by lia. rewrite art_land_full_l by lia.
zstep (ltac:(oF' 0x9a958%Z)) (ltac:(oD' 0x9a958%Z)).
zsd (ltac:(oF' 0x9a95c%Z)) (ltac:(oD' 0x9a95c%Z)) (this + 2056) bp ltac:(rewok Wt).
zbft (ltac:(oF' 0x9a960%Z)) (ltac:(oD' 0x9a960%Z)). zbtk (ltac:(oF' 0x9a964%Z)) (ltac:(oD' 0x9a964%Z)). zbtk (ltac:(oF' 0x9a99c%Z)) (ltac:(oD' 0x9a99c%Z)).
zstep (ltac:(oF' 0x9aa04%Z)) (ltac:(oD' 0x9aa04%Z)). zstep (ltac:(oF' 0x9aa08%Z)) (ltac:(oD' 0x9aa08%Z)). zstep (ltac:(oF' 0x9aa0c%Z)) (ltac:(oD' 0x9aa0c%Z)). zstep (ltac:(oF' 0x9aa10%Z)) (ltac:(oD' 0x9aa10%Z)). zstep (ltac:(oF' 0x9aa14%Z)) (ltac:(oD' 0x9aa14%Z)).
match goal with |- msteps _ (mkst _ _ ?X _) _ =>
assert (C56 : cellA X (sp - 8) 8 (U raw)) by zcell; assert (C48 : cellA X (sp - 16) 8 (U (getr regs 8))) by zcell;
assert (C40 : cellA X (sp - 24) 8 (U (getr regs 9))) by zcell; assert (C32 : cellA X (sp - 32) 8 (U (getr regs 18))) by zcell;
assert (C24 : cellA X (sp - 40) 8 (U (getr regs 19))) by zcell; assert (C16 : cellA X (sp - 48) 8 (U (getr regs 20))) by zcell;
assert (C08 : cellA X (sp - 56) 8 (U (getr regs 21))) by zcell end.
zld (ltac:(oF' 0x9aa18%Z)) (ltac:(oD' 0x9aa18%Z)) (sp - 8) C56. rewrite Z_to_bv_bv_unsigned.
zld (ltac:(oF' 0x9aa1c%Z)) (ltac:(oD' 0x9aa1c%Z)) (sp - 16) C48. rewrite Z_to_bv_bv_unsigned.
zld (ltac:(oF' 0x9aa20%Z)) (ltac:(oD' 0x9aa20%Z)) (sp - 24) C40. rewrite Z_to_bv_bv_unsigned.
zld (ltac:(oF' 0x9aa24%Z)) (ltac:(oD' 0x9aa24%Z)) (sp - 32) C32. rewrite Z_to_bv_bv_unsigned.
zld (ltac:(oF' 0x9aa28%Z)) (ltac:(oD' 0x9aa28%Z)) (sp - 40) C24. rewrite Z_to_bv_bv_unsigned.
zld (ltac:(oF' 0x9aa2c%Z)) (ltac:(oD' 0x9aa2c%Z)) (sp - 48) C16. rewrite Z_to_bv_bv_unsigned.
zld (ltac:(oF' 0x9aa30%Z)) (ltac:(oD' 0x9aa30%Z)) (sp - 56) C08. rewrite Z_to_bv_bv_unsigned.
zstep (ltac:(oF' 0x9aa34%Z)) (ltac:(oD' 0x9aa34%Z)).
stepn (ltac:(oF' 0x9aa38%Z)) (ltac:(oD' 0x9aa38%Z)).
zret.
Qed.
End SE.
End FPX2.
Lemma Wn8_zero_split : ltac2:(TCodec.tc2 tcn__JbtUnwind "Q7'R0yR0%211'5y8%511%311p051'>&Q3zr1%3221&Q4&Q1r2+8%3221&Q8+2+R0%3221%9251'8&Cu8r4r3%44321Bu4%64143D+4%B251%94431G%;3K61p0=1p0H1pRJM1pQ4O1").
Proof.
intros M a Ha Ha'. unfold Wn. change (word_to_le_bytes 8 (Z_to_bv 64 0)) with (word_to_le_bytes 4 (Z_to_bv 64 0) ++ word_to_le_bytes 4 (Z_to_bv 64 0)).
rewrite RefMemcpyLib.wbytes_app. f_equal. rewrite length_N_to_le_bytes. unfold at_. rewrite art_u_lit by lia. reflexivity.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
