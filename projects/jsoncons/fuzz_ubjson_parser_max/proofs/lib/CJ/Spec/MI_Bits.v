(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Lia Bool.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec Require Import Malloc MI_Arith.
Local Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import RunP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__CJ_Spec_MI_Bits () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.Malloc."; "Stdlib.ZArith.BinInt.Z."], [["1andb"; "1bool"; "1negb"; "1true"; "2and"; "2eq"; "2ex"; "3Z"; "4ctz32"; "4lowbit"; "5add"; "5eqb"; "5land"; "5ldiff"; "5le"; "5lt"]; ["5mul"; "5opp"; "5pow"; "5sub"; "5testbit"; "0a"; "0f"; "0i"; "0j"; "0k"; "0m"; "0n"; "0v"]]).
Section CEIL_WRAP_1.
Context {RUNp : RunP}.
Lemma land_opp_odd : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Bits "?'7'5&<&:&@+2r1%3221+1%6221&A%112%:231%<3=15pQ<>1").
Proof. intros a.
apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec.
rewrite Z.bits_opp by lia. replace (Z.pred (2 * a + 1)) with (2 * a) by lia.
destruct (Z.eq_dec n 0) as [->|].
- rewrite Z.testbit_odd_0, Z.testbit_even_0. reflexivity.
- replace n with (Z.succ (n - 1)) by lia. rewrite Z.testbit_odd_succ, Z.testbit_even_succ by lia.
rewrite andb_negb_r. change 1 with (2^0). rewrite Z.pow2_bits_eqb by lia. symmetry. apply Z.eqb_neq. lia.
Qed.
Lemma land_opp_even : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Bits "?'7'5&<&@+2r1%3221&A%112%7231%315%9261%9281%<3=41pQ<>1").
Proof. intros a.
apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec. replace (- (2 * a)) with (2 * (- a)) by lia.
destruct (Z.eq_dec n 0) as [->|].
- rewrite !Z.testbit_even_0. reflexivity.
- replace n with (Z.succ (n - 1)) by lia. rewrite !Z.testbit_even_succ by lia. symmetry. apply Z.land_spec.
Qed.
Lemma lowbit_pow2 : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Bits "J'7&?zr1%3221'6'4&>%1265'5&<r3&A%112%4231&B+2%221>%93B41%<228%>221%?2=1qQDF1%B2G1p0D1pQFI1").
Proof.
intros m Hm.
pose proof (Wf_Z.Zlt_0_ind (fun x => 0 < x -> exists k, 0 <= k /\ Z.land x (- x) = 2 ^ k /\ 2 ^ k <= x)) as G.
cbv beta in G. apply G; [|lia|lia]. clear G m Hm.
intros x IH Hx0 Hx.
destruct (Z.Even_or_Odd x) as [[a ->]|[a ->]].
- destruct (IH a ltac:(lia) ltac:(lia)) as (k & Hk & E & L).
exists (k + 1). rewrite land_opp_even, E, Z.pow_add_r by lia. change (2^1) with 2. lia.
- exists 0. rewrite land_opp_odd. change (2^0) with 1. lia.
Qed.
Lemma land_opp_pow2 : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Bits "A'7&>zr1%3221'5&<&B+2r2%3221&A%112%7231%93>14p0;1pQD@1").
Proof. intros k.
intros Hk. apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_opp, Z.pow2_bits_eqb by lia.
rewrite <- Z.ones_equiv, Z.testbit_ones by lia.
destruct (Z.eqb_spec k n); cbn [andb]; [|reflexivity].
subst. replace (n <? n) with false by (symmetry; apply Z.ltb_irrefl). destruct (0 <=? n); reflexivity.
Qed.
Lemma lowbit_nonzero : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Bits "H'7&?zr1%3221'6'4&>%1265'5&9r3%211&B+2%221<%73@41%:226%<221%=2;1qQDD1%@2E1p0B1pQFG1").
Proof. intros m. intros. unfold lowbit. apply lowbit_pow2. assumption. Qed.
Lemma ctz32_pow2 : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Bits "?'7&>zr1%3221'5&8&B+2r2%3221%511%73<13p091pQD>1").
Proof. intros k. intros. unfold ctz32, lowbit. rewrite land_opp_pow2 by lia. apply Z.log2_pow2. lia. Qed.
Lemma lowbit_testbit : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Bits "H'7&>zr1%3221'5&9r3%211&B+2r2%3221%83=51'1&Dr4%221:(3%>3521p071p0A1pQDF1pQJG1").
Proof.
intros v k Hk E. unfold lowbit in E.
assert (T : Z.testbit (Z.land v (- v)) k = true) by (rewrite E; apply Z.pow2_bits_true; lia).
rewrite Z.land_spec in T. apply andb_prop in T. tauto.
Qed.
Lemma sub_bit_ldiff : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Bits "K'7&>zr2%3221'5'1&Dr4r3%3221(3%73621&Cr5&B+2%2219%5241&=%1263%@3E31p0:1p0C1p0D1pQ@I1pQ>J1").
Proof. intros f i.
intros Hf Hi Hb.
assert (E : f = Z.lor (Z.ldiff f (2 ^ i)) (2 ^ i)).
{ apply Z.bits_inj'. intros n Hn. rewrite Z.lor_spec, Z.ldiff_spec, Z.pow2_bits_eqb by lia.
destruct (Z.eqb_spec i n) as [<-|NE]; [rewrite Hb; reflexivity|]. cbn. rewrite Bool.andb_true_r, Bool.orb_false_r. reflexivity. }
assert (D : Z.land (Z.ldiff f (2 ^ i)) (2 ^ i) = 0).
{ apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.ldiff_spec, Z.pow2_bits_eqb, Z.bits_0 by lia.
destruct (Z.eqb_spec i n); cbn; [rewrite Bool.andb_false_r| rewrite Bool.andb_false_r]; reflexivity. }
pose proof (Z.add_nocarry_lxor _ _ D) as A. rewrite (Z.lxor_lor _ _ D) in A. rewrite <- E in A. lia.
Qed.
Lemma testbit_sub_bit : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Bits "Q3'7&>zr3%3221'5'1&Dr6r5%3221(3%73621&Cr7&B+2%2219%5241%<21:&0%>27<&2&;%12@?%311%6251%F3E81p0@1p0I1p0J1p0K1pQBQ01pQ@Q11pQ>Q21").
Proof. intros f i j.
intros Hf Hi Hj Hb. rewrite (sub_bit_ldiff f i Hf Hi Hb), Z.ldiff_spec, Z.pow2_bits_eqb by lia. reflexivity.
Qed.
Lemma lowbit_idiom : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Bits "QD'7&?zr1%3221'6'4&>%1265'5&9r3%211&B+2%221<%73@41&8%116%:3C1@'1&D%12;C(3%?3421&C%12?>%D2I1r5%C11%5221r2%;221&0%=263&2&;%12J6%311%6251%O3D81p0Q11pQBQ:1%Q52@1%Q62D1%Q72J1%Q82N1%Q92Q71qQDQ@1%Q<2QA1p0Q>1pQFQC1").
Proof. intros m.
intros Hm. destruct (lowbit_nonzero m Hm) as (k & Hk & E & L). exists k.
pose proof (lowbit_testbit m k Hk E) as Tb.
split; [exact Hk|]. split; [exact E|]. split; [rewrite E; apply ctz32_pow2; exact Hk|]. split; [exact Tb|].
rewrite E. split; [lia|]. intros j Hj. apply testbit_sub_bit; auto; lia.
Qed.
Lemma mask_below : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Bits "Q2'7&>zr2%3221r1%5241'5'1&Dr6%2218(3%63521r3%>215p031p0;1pQ@B1&?r5&B+2&:r4+1%3221%6251%9281p0;1p0J1p0K1pQHQ01pQFQ11").
Proof. intros m n. intros Hm Hn H. apply bits_below_bound; [lia| lia|]. intros i Hi Hb. pose proof (H i Hi Hb). lia. Qed.
End CEIL_WRAP_1.
