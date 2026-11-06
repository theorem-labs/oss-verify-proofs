(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatSim StoreOk As0Tables ArtMem JatInitCache JatPopulate1 ArtRuns JatCls JatFp JatClsRep JatClsGfa2 JatClsRefill JatCARSpec JatAlloc3Pure.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLiaT. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__JatInvMallocPure () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Init.Specif."; "Corelib.Numbers.BinNums."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.As0Tables.AsanTab."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatCARSpec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatCls."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."], [["1app"; "1bool"; "1list"; "1nil"; "1true"; "2and"; "2eq"; "2ex"; "2iff"; "2not"; "2or"; "3sumbool"; "4Z"; "5class_size"; "6art_ca_pre"; "6art_cls_pop"]; ["7art_carved"; "7art_cls"; "7art_cls_needs_populate"; "7art_cls_new"; "7art_cls_ok"; "7art_cptr_ok"; "7cl_au"; "7cl_cache"; "7cl_free"; "7cl_mu"; "8In"; "8NoDup"; "8last"; "9add"; "9le"; "9lt"]; ["9modulo"; "9mul"; "9to_nat"; "0au"; "0au'"; "0c"; "0cl"; "0cl'"; "0clp"; "0ka"; "0new"; "0sz"; "0w"; "0w0"]]).
Local Ltac lia := L5FastLiaT.plia2.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Lemma art_cptr_apart : ltac2:(TCodec.tc2 tcn__JatInvMallocPure "Q4'<&Ozr4%3221&Er5r3%33251r6%53143&9'6%13=7:%311':&N&M&Q1+@%221>r8%5221%524>%8221%8224%:216%<231p0>1p0C1p0F1p0K1pRLQ01pRJQ11pR8Q21pRHQ31").
Proof.
intros sz au w w0 Hsz (_ & _ & (i & Ei)) (_ & _ & (i0 & Ei0)) N.
destruct (Z_lt_ge_dec i0 i) as [L|G]; [left|right].
- assert (sz * (i0 + 1) <= sz * i) by (apply Z.mul_le_mono_nonneg_l; lia). lia.
- assert (i <> i0) by (intros E; subst i0; lia). assert (sz * (i + 1) <= sz * i0) by (apply Z.mul_le_mono_nonneg_l; lia). lia.
Qed.
Lemma art_cptr_ok_dec : ltac2:(TCodec.tc2 tcn__JatInvMallocPure "A'<&Ozr3%3221';&Er4r2%33261&9%112%7231p091pRJ>1pR8?1pRH@1").
Proof.
intros sz au w Hsz. unfold art_cptr_ok.
destruct (Z_le_gt_dec 0 w) as [H0|H0]; [|right; intros (A & _); lia].
destruct (Z_le_gt_dec (16 * w + sz) au) as [H1|H1]; [|right; intros (_ & A & _); lia].
destruct (Z.eq_dec ((16 * w) mod sz) 0) as [H2|H2].
- left. split; [exact H0|]. split; [exact H1|]. exists (16 * w / sz). pose proof (Z.div_mod (16 * w) sz ltac:(lia)) as D. lia.
- right. intros (_ & _ & (i & Ei)). apply H2. rewrite Ei, Z.mul_comm. apply Z_mod_mult.
Qed.
Lemma art_carved_complete : ltac2:(TCodec.tc2 tcn__JatInvMallocPure "QA'<&Ozr4%3221'6&Q0r5+@%3221%53:18'7r6&Q1r7r1%3221%<3A51qRDB1%82C1&N%12C>&Er8&M%<2=2%22<1%5341D&9r9%8317B%311&J&@r:&Q2%11=%43831%63Q6H1p081p0=1p0D1p0G1p0Q11p0Q81pRLQ=1pRFQ>1pR8Q?1pRHQ@1").
Proof.
intros sz au new w0 Hsz Hsz16 (ka & Eau) Hnew (H0 & H1 & (i & Ei)) NOK.
assert (Hgt : au < 16 * w0 + sz). { destruct (Z_lt_ge_dec au (16 * w0 + sz)) as [L|G]; [exact L|]. exfalso. apply NOK. split; [exact H0|]. split; [lia|]. exists i. exact Ei. }
assert (Hi1 : ka <= i). { destruct (Z_le_gt_dec ka i) as [L|G]; [exact L|]. exfalso. assert (sz * (i + 1) <= sz * ka) by (apply Z.mul_le_mono_nonneg_l; lia). lia. }
assert (Hi2 : i + 1 <= ka + new). { destruct (Z_le_gt_dec (i + 1) (ka + new)) as [L|G]; [exact L|]. exfalso. assert (sz * (ka + new + 1) <= sz * (i + 1)) by (apply Z.mul_le_mono_nonneg_l; lia). lia. }
unfold art_carved. apply in_map_iff. exists (Z.to_nat (new - 1 - (i - ka))). split.
- rewrite !Z2Nat.id by lia. replace (new - 1 - (new - 1 - (i - ka))) with (i - ka) by lia.
replace (au + (i - ka) * sz) with (w0 * 16) by (rewrite Eau; lia). apply Z_div_mult. lia.
- apply in_seq. lia.
Qed.
Lemma art_ca_pre_in : ltac2:(TCodec.tc2 tcn__JatInvMallocPure "QC'<'A&8&Jr1&0&G&>r3r2%3221%511&H%113%93>31%<3?;1':%;18%619%>3C21%A3D@1'5'6'2%11H(3%11J%533:1'1&B%12FE(4%:3421&@&F%11J&=%11M&Q2&C%12Q0O%311%93751%Q83Q;Q71%G2<1%H2B1%N2J1%Q=2Q01pRLQ@1pR>Q@1pR<QB1").
Proof.
intros c cl w0. unfold art_ca_pre. destruct (cl_cache cl) as [|z l] eqn:E.
- rewrite art_cls_refill_eq. cbn [art_cls_take cl_cache cl_free].
set (fl := cl_free (art_cls_pre_take c cl)). set (k := (length fl - art_refill_n c)%nat).
assert (EQ : In w0 (skipn k fl ++ firstn k fl) <-> In w0 fl).
{ rewrite <- (firstn_skipn k fl) at 3. rewrite !in_app_iff. tauto. }
rewrite EQ. unfold fl, art_cls_pre_take. destruct (art_cls_needs_populate c cl) eqn:NP.
+ unfold art_cls_populate. cbn [cl_free app]. rewrite in_app_iff. cbn [app]. split.
* intros [H|H]; [left; exact H|right; repeat split; exact H].
* intros [H|(_ & _ & H)]; [left; exact H|right; exact H].
+ cbn [app]. split; [intros H; left; exact H|intros [H|(_ & F & _)]; [exact H|discriminate F]].
- split; [intros H; left; rewrite ?E in *; exact H|intros [H|(F & _)]; [rewrite ?E in *; exact H|discriminate F]].
Qed.
Lemma art_ca_pre_au : ltac2:(TCodec.tc2 tcn__JatInvMallocPure "Q7'<'A':'6&F&>r2r1%3221%511%613%83;21'5'2%11>&G%119(3%11B%@3531'1&B%12@?(4%E3421&M&Q1&C%12FE&=%11H%5231%72F1%N3Q1H1%F2:1%G2@1%Q22I1pR>Q41pR<Q61").
Proof.
intros c cl. unfold art_ca_pre. destruct (cl_cache cl) as [|z l] eqn:E; [|left; reflexivity].
rewrite art_cls_refill_eq. cbn [art_cls_take cl_au]. unfold art_cls_pre_take. destruct (art_cls_needs_populate c cl) eqn:NP; [|left; reflexivity].
right. repeat split.
Qed.
Lemma art_pop_in : ltac2:(TCodec.tc2 tcn__JatInvMallocPure "Q>'A'<'K&0&Gr2%211&H%113%63831%8291&9'6'2%11=r3%<11(3%11A%73531%911&8&J&?r4%211%F11%D12%I3K21%73L>1'5%K17%I18%N3Q021%<3Q1C1&Lz%23Q461%J3Q5G1%L11%:261%D2<1p0F1p0Q11pRLQ;1pRBQ=1").
Proof.
intros clp w0 ND NE. cbn [art_cls_pop cl_cache cl_free]. set (l := last (cl_cache clp) 0).
rewrite (app_removelast_last 0 NE) in ND. fold l in ND. rewrite (app_removelast_last 0 NE) at 2. fold l.
set (rl := removelast (cl_cache clp)) in *. rewrite <- app_assoc in ND. cbn [app] in ND.
apply NoDup_remove in ND. destruct ND as [_ NI]. rewrite !in_app_iff. cbn [In]. rewrite in_app_iff in NI. split.
- intros H. split; [tauto|]. intros ->. tauto.
- intros [[[H|[H|[]]]|H] N]; [left; exact H|exfalso; apply N; symmetry; exact H|right; exact H].
Qed.
Section Facts.
Variables (c : Z) (cl : art_cls).
Hypothesis Hc : 1 <= c <= 30.
Hypothesis OK : art_cls_ok c cl.
Let sz := AsanTab.class_size c.
Let w := art_ca_cptr c cl.
Let cl' := art_cls_pop (art_ca_pre c cl).
#[using="Hc OK"] Lemma art_malloc_in_free : ltac2:(TCodec.tc2 tcn__JatInvMallocPure "Q8'<&DvQ5&>vQ6%2231%5241&Jr2&0&GvQ7%211&H%113%63?31%93@81'5&9'6r3vQ<%33F21%511':%?1E%=1F%B3K21%E3L81&EvQ;&F%11L%4331=%@11%;271%C2=1p0E1p0Q01pRLQ71").
Proof.
intros w0 OKp H. pose proof OKp as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ND). apply NoDup_ListNoDup in ND.
apply (art_pop_in (art_ca_pre c cl) w0 ND (art_ca_pre_cache_ne c cl Hc OK)) in H. destruct H as [H N]. split; [exact N|].
apply art_ca_pre_in in H. destruct H as [H|(_ & _ & H)]; [left; exact H|right].
apply art_carved_in in H. destruct H as (i & Hi & Ew). intros (_ & B & _). fold sz in Ew.
destruct OK as (_ & (Hau0 & _) & _ & _ & (ka & Eau) & _). destruct (art_class_size_facts c Hc) as (Hsz & Hsz16). fold sz in Eau, Hsz, Hsz16.
assert (E16 : 16 * w0 = sz * (ka + i)).
{ rewrite Ew, Eau. replace (sz * ka + i * sz) with (sz * (ka + i)) by lia. pose proof (art_div16_mul sz (ka + i) Hsz16). lia. }
assert (sz * ka <= sz * (ka + i)) by (apply Z.mul_le_mono_nonneg_l; lia). lia.
Qed.
#[using="Hc OK"] Lemma art_malloc_free_in : ltac2:(TCodec.tc2 tcn__JatInvMallocPure "Q:'<&DvQ5&>vQ6%2231%5241&EvQ;&F%115r2%53421&9'6r3vQ<%33A21%511%:1?r4%>3=21&Jr5&0&G%11F&H%11H%53M31%83N71p0:1vQ7%811%712%;3Q321%>3Q4=1p061p0D1p0K1p0Q21pRLQ91").
Proof.
intros w0 OKp V N OLD. pose proof OKp as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ND). apply NoDup_ListNoDup in ND.
apply (art_pop_in (art_ca_pre c cl) w0 ND (art_ca_pre_cache_ne c cl Hc OK)). split; [|exact N].
apply art_ca_pre_in. destruct (art_class_size_facts c Hc) as (Hsz & Hsz16). fold sz in Hsz, Hsz16.
destruct (art_cptr_ok_dec sz (cl_au cl) w0 ltac:(lia)) as [Y|NO]; [left; exact (OLD Y)|].
destruct (art_ca_pre_au c cl) as [E|(E1 & E2 & E3)]; [rewrite E in V; contradiction|]. right. split; [exact E1|]. split; [exact E2|].
fold sz in E3. rewrite E3 in V. destruct OK as (_ & (Hau0 & Haumu) & _ & _ & Hka & _). fold sz in Hka.
apply art_carved_complete; try assumption; [lia|].
unfold art_cls_new. fold sz. apply Z.div_pos; lia.
Qed.
End Facts.
Lemma art_ca_pre_mu_cases : ltac2:(TCodec.tc2 tcn__JatInvMallocPure "Q7'<'A':'5'6&I&>r2r1%3221%511%613%83<21&F%115%217%<3@21%>251'2%11C&G%11=(3%11G%D3531'1&B%12DC(4%I3421&M+XPP0%22E1%M3Q1G1%O251%Q02;1%Q22C1pR>Q41pR<Q61").
Proof.
intros c cl. unfold art_ca_pre. destruct (cl_cache cl) as [|z l] eqn:E; [|left; split; reflexivity].
rewrite art_cls_refill_eq. cbn [art_cls_take cl_au cl_mu]. unfold art_cls_pre_take. destruct (art_cls_needs_populate c cl) eqn:NP; [|left; split; reflexivity].
right. repeat split.
Qed.
Lemma art_cptr_new_lo : ltac2:(TCodec.tc2 tcn__JatInvMallocPure "Q2'<&Ozr4%3221'7'6r5&Q1r6r1%3221%63<51qRD=1%92>1&Er3%238>1&9r7%531;A%311&N+@%@21A%3261p051p0:1p0>1p0I1pRLN1pR:O1pR8Q01pRHQ11").
Proof.
intros sz au au' w0 Hsz (ka & Eau) (H0 & H1 & (i & Ei)) NOK.
assert (Hgt : au < 16 * w0 + sz). { destruct (Z_lt_ge_dec au (16 * w0 + sz)) as [L|G]; [exact L|]. exfalso. apply NOK. split; [exact H0|]. split; [lia|]. exists i. exact Ei. }
destruct (Z_le_gt_dec ka i) as [L|G]. { assert (sz * ka <= sz * i) by (apply Z.mul_le_mono_nonneg_l; lia). lia. }
exfalso. assert (sz * (i + 1) <= sz * ka) by (apply Z.mul_le_mono_nonneg_l; lia). lia.
Qed.
