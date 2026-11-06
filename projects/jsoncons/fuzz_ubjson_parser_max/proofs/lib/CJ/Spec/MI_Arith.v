(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec Require Import Malloc.
Import ListNotations.
Local Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import RunP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__CJ_Spec_MI_Arith () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.Malloc."; "Stdlib.ZArith.BinInt.Z."], [["1bool"; "1false"; "1length"; "1nat"; "1true"; "2and"; "2eq"; "3Forall"; "4Z"; "5bit"; "5mask_upto"; "5size_class"; "5size_classes"; "6eqb"; "6le"; "6leb"]; ["6lt"; "6pow"; "6testbit"; "0a"; "0i"; "0j"; "0k"; "0n"; "0sc"; "0x"]]).
Section CEIL_WRAP_1.
Context {RUNp : RunP}.
Lemma size_classes_length : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Arith "8'6'3&2'8&<%3221uQ@%73621").
Proof. reflexivity. Qed.
Lemma size_classes_bounds : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Arith "='7'8'5&>+1r1%3221+WoO%5231%7231qQD91&<%<3;21").
Proof.
apply Forall_forall. intros x Hx. unfold size_classes in Hx.
repeat (destruct Hx as [<-|Hx]; [lia|]). destruct Hx.
Qed.
Lemma size_class_bound : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Arith "D'8'5&>zr1%3221&@+Q@%2241%8241+1&;r2%211%<241+WoO%>231%@231p091pQBC1").
Proof. intros sc.
intros H. unfold size_class.
apply (Forall_forall (fun x => 1 <= x <= 8191) size_classes); [apply size_classes_bounds|].
apply nth_In. rewrite size_classes_length. lia.
Qed.
Lemma mask_upto_nonneg : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Arith ";'8&>zr1%3221&:r2%211%7261p051pQ>:1").
Proof. intros k. intros. unfold mask_upto. assert (0 < 2 ^ (k + 1)) by (apply Z.pow_pos_nonneg; lia). lia. Qed.
Lemma testbit_mask_upto : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Arith "D'8&>zr2%3221'6'0&B&:r4%211r3%5221&?%1235%:3931p0<1p0=1pQ:B1pQ>C1").
Proof. intros k i.
intros Hk Hi. unfold mask_upto. replace (2 ^ (k + 1) - 1) with (Z.pred (2 ^ (k + 1))) by lia.
rewrite <- Z.ones_equiv. destruct (Z.leb_spec i k).
- apply Z.ones_spec_low. lia.
- apply Z.ones_spec_high. lia.
Qed.
Lemma testbit_bit : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Arith "D'8&>zr2%3221'6'0&B&9r4%211r3%5221&=%1253%:3931p0<1p0=1pQ<B1pQ:C1").
Proof. intros i j.
intros Hi Hj. unfold bit. destruct (Z.eqb_spec i j) as [<-|NE].
- apply Z.pow2_bits_true. exact Hi.
- apply Z.pow2_bits_false. lia.
Qed.
Lemma bits_below_bound : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Arith "O'8&>zr1%3221r3%5241'6'0&Br5r2%3221(4%73621&@r7%22<1p041p0?1pQ:D1r4&A+2%221>%:241p061p0E1p0H1pQ8M1pQ@N1").
Proof. intros n a.
intros Ha Hn Hb. destruct (Z.lt_ge_cases a (2 ^ n)) as [|Hge]; [assumption|]. exfalso.
assert (Hl : n <= Z.log2 a) by (apply Z.log2_le_pow2; lia).
assert (Ht : Z.testbit a (Z.log2 a) = true) by (apply Z.bit_log2; lia).
specialize (Hb (Z.log2 a) ltac:(apply Z.log2_nonneg) Ht). lia.
Qed.
Lemma testbit_false_above : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Arith "J'8'5&>zr2%3221&@&A+2r3%3221%5271%;271r4%<21:'6'0&B%1259(1%53421p071p0:1pQ:G1pQ8H1pQ@I1").
Proof. intros n a i.
intros Ha Hi. destruct (Z.eq_dec a 0) as [->|NZ]; [apply Z.bits_0|].
apply Z.bits_above_log2; [lia|]. apply Z.log2_lt_pow2; [lia|].
apply (Z.lt_le_trans _ (2 ^ n)); [lia|]. apply Z.pow_le_mono_r; lia.
Qed.
End CEIL_WRAP_1.
