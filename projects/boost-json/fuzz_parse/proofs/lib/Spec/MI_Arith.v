(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import Malloc.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib4Init9Datatypes06length03nat37Corelib4Init5Logici52eq37Corelib7Numbers7BinNumsje1Z79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec6Malloc~~~~~~lbcsize_classes46Stdlib6ZArith6BinInt1Zq82lei53and37Corelib5Lists7ListDefsb6Foralllbasize_classq82ltlb9mask_upto04boolq83lebq87testbitlb3bitq83eqb04trueq83pow" s.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.   (* [comment removed for export] *)
Import ListNotations.
Local Open Scope Z_scope.

Lemma size_classes_length : ltac2:(zQ "50!h8!i0!j9!l7!p9@3$2$1@2$0$3$4Nj0").
Proof. reflexivity. Qed.

Lemma size_classes_bounds : ltac2:(zQ "50!l7!s0!s5!u2!p9@3$3$0\1x$0@2$2@2$1+1^1@2$1^1+hvvf$4").
Proof.
  apply Forall_forall. intros x Hx. unfold size_classes in Hx.
  repeat (destruct Hx as [<-|Hx]; [lia|]). destruct Hx.
Qed.

Lemma size_class_bound : ltac2:(zQ "50!s0!s5!ub!l7!v8>2sc$3>0@2$1@2$0Z^1@2$4^1+j0@2$1@2$0+1@1$2^2@2$0@1$2^2+hvvf").
Proof. intros sc.
  intros H. unfold size_class.
  apply (Forall_forall (fun x => 1 <= x <= 8191) size_classes); [apply size_classes_bounds|].
  apply nth_In. rewrite size_classes_length. lia.
Qed.

(* [comment removed for export] *)
Lemma mask_upto_nonneg : ltac2:(zQ "30!s0!l7!vd>1k$1>0@2$0Z^1@2$0Z@1$2^2").
Proof. intros k. intros. unfold mask_upto. assert (0 < 2 ^ (k + 1)) by (apply Z.pow_pos_nonneg; lia). lia. Qed.

Lemma testbit_mask_upto : ltac2:(zQ "70!l7!s0!hg9!j9!vd!hgf!hh5>1k$0>1i$0>0@2$1Z^2>0@2$1Z^2@3$3$2@2$6@1$4^4^3@2$5^3^4").
Proof. intros k i.
  intros Hk Hi. unfold mask_upto. replace (2 ^ (k + 1) - 1) with (Z.pred (2 ^ (k + 1))) by lia.
  rewrite <- Z.ones_equiv. destruct (Z.leb_spec i k).
  - apply Z.ones_spec_low. lia.
  - apply Z.ones_spec_high. lia.
Qed.

Lemma testbit_bit : ltac2:(zQ "70!l7!s0!hg9!j9!hhf!hi5!hh5>1i$0>1j$0>0@2$1Z^2>0@2$1Z^2@3$3$2@2$6@1$4^4^3@2$5^4^3").
Proof. intros i j.
  intros Hi Hj. unfold bit. destruct (Z.eqb_spec i j) as [<-|NE].
  - apply Z.pow2_bits_true. exact Hi.
  - apply Z.pow2_bits_false. lia.
Qed.

Lemma bits_below_bound : ltac2:(zQ "80!l7!s0!v8!hg9!hib!j9!hj1!hh5>1n$0>1a$0>0@2$1Z^1>0@2$1Z^3>0>1i$0>0@2$1Z^1>0@3$5$3@2$7^5^2$4@2$2^3^7@2$2^4@2$6+2^5").
Proof. intros n a.
  intros Ha Hn Hb. destruct (Z.lt_ge_cases a (2 ^ n)) as [|Hge]; [assumption|]. exfalso.
  assert (Hl : n <= Z.log2 a) by (apply Z.log2_le_pow2; lia).
  assert (Ht : Z.testbit a (Z.log2 a) = true) by (apply Z.bit_log2; lia).
  specialize (Hb (Z.log2 a) ltac:(apply Z.log2_nonneg) Ht). lia.
Qed.

(* [comment removed for export] *)
