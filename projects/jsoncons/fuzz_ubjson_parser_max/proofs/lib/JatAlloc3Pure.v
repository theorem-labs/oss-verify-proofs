(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatSim StoreOk As0Tables ArtMem JatInitCache JatPopulate1 ArtRuns JatCls JatFp JatClsRep JatClsGfa2 JatClsRefill JatCARSpec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLiaT. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__JatAlloc3Pure () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatCARSpec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatCls."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."], [["1app"; "1bool"; "1list"; "1nil"; "1true"; "2and"; "2eq"; "2or"; "3Z"; "4art_ca_cptr"; "4art_ca_pre"; "5art_cls"; "5art_cls_needs_populate"; "5art_cls_ok"; "5cl_au"; "5cl_cache"]; ["5cl_free"; "5cl_mu"; "6In"; "7add"; "7le"; "7mul"; "0c"; "0cl"]]).
Local Ltac lia := L5FastLiaT.plia2.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Lemma art_in_skipn : forall (A : Type) (k : nat) (l : list A) x, In x (skipn k l) -> In x l.
Proof. intros A k l x H. rewrite <- (firstn_skipn k l). apply in_or_app. right. exact H. Qed.
Lemma art_ca_cptr_in : ltac2:(TCodec.tc2 tcn__JatAlloc3Pure "J'8';'5&D+1r2%3221+N%5231%7231&=r3%2217&B&9r4%2215&?&:%1248%311%83E51p0:1p0>1pQ@G1pQ>I1").
Proof.
intros c cl Hc OK. pose proof (art_ca_pre_cache_ne c cl Hc OK) as Hne. unfold art_ca_cptr.
rewrite (app_removelast_last 0 Hne) at 2. apply in_or_app. right. left. reflexivity.
Qed.
Lemma art_ca_cptr_origin : ltac2:(TCodec.tc2 tcn__JatAlloc3Pure "QA'8';'5&D+1r2%3221+N%5231%7231&=r3%2217'7&B&9r4%2216&0&?%119&@%11;%53G31%:3H71'6'2%11K(3%11M%533:1'1&<%12AF(4%:3421&>%11J&E+@%221G%Q6241%Q8271%Q92=1%O2D1p0Q11p0Q51pQ@Q>1pQ>Q@1").
Proof.
intros c cl Hc OK. pose proof (art_ca_cptr_in c cl Hc OK) as Hin. set (wp := art_ca_cptr c cl) in *.
unfold art_ca_pre in Hin. destruct (cl_cache cl) as [|z l] eqn:E.
- rewrite art_cls_refill_eq in Hin. cbn [art_cls_take cl_cache] in Hin. apply art_in_skipn in Hin.
unfold art_cls_pre_take in Hin. destruct (art_cls_needs_populate c cl) eqn:NP.
+ unfold art_cls_populate in Hin. cbn [cl_free] in Hin. apply in_app_or in Hin. destruct Hin as [Hin|Hin]; [left; exact Hin|].
right. split; [reflexivity|]. split; [reflexivity|].
apply art_carved_in in Hin. destruct Hin as (i & Hi & Ew).
destruct OK as (_ & (Hau0 & _) & _ & _ & (ka & Eau) & _). destruct (art_class_size_facts c Hc) as (Hsz & Hsz16).
assert (E16 : 16 * wp = AsanTab.class_size c * (ka + i)).
{ rewrite Ew, Eau. replace (AsanTab.class_size c * ka + i * AsanTab.class_size c) with (AsanTab.class_size c * (ka + i)) by lia.
pose proof (art_div16_mul (AsanTab.class_size c) (ka + i) Hsz16). lia. }
rewrite E16, Eau. assert (AsanTab.class_size c * ka <= AsanTab.class_size c * (ka + i)) by (apply Z.mul_le_mono_nonneg_l; lia). lia.
+ left. exact Hin.
- left. apply in_or_app. left. rewrite <- E. exact Hin.
Qed.
Lemma art_ca_pre_mu_pop : ltac2:(TCodec.tc2 tcn__JatAlloc3Pure "Q0'8';'6'2%114&?r1%211(3%119%83631'1&<r3r2%3221(4%?3621&A&:r4%2218%411&C%61;+XPP0%3221%I3K51p0;1p0C1pQ@M1pQ>O1").
Proof. intros c cl E NP. unfold art_ca_pre. rewrite E. rewrite art_cls_refill_eq. unfold art_cls_pre_take. rewrite NP. reflexivity. Qed.
