(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia Bool.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import Malloc MI_Arith.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums01Z46Stdlib6ZArith6BinInt1Zhc3addhc3mul37Corelib4Init5Logick02eqhc4landhc3oppk03andhc2lehc3powk02exhc2lt79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec6Malloc~~~~~~o16lowbito15ctz3237Corelib4Init9Datatypest04boolt04truehc7testbithc5ldiffhc3subt04andbt04negbhc3eqb" s.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.   (* [comment removed for export] *)
Local Open Scope Z_scope.

Lemma land_opp_odd : ltac2:(zQ "60!h9!j4!ja!l4!l9!m0>1a$0@3$3$0@2$4@2$1@2$2+2^1+1@1$5@2$1@2$2+2^1+1+1").
Proof. intros a.
  apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec.
  rewrite Z.bits_opp by lia. replace (Z.pred (2 * a + 1)) with (2 * a) by lia.
  destruct (Z.eq_dec n 0) as [->|].
  - rewrite Z.testbit_odd_0, Z.testbit_even_0. reflexivity.
  - replace n with (Z.succ (n - 1)) by lia. rewrite Z.testbit_odd_succ, Z.testbit_even_succ by lia.
    rewrite andb_negb_r. change 1 with (2^0). rewrite Z.pow2_bits_eqb by lia. symmetry. apply Z.eqb_neq. lia.
Qed.

Lemma land_opp_even : ltac2:(zQ "50!ja!h9!l9!m0!l4>1a$1@3$4$1@2$2@2$0+2^1@1$3@2$0+2^1@2$0+2@2$2^1@1$3^1").
Proof. intros a.
  apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec. replace (- (2 * a)) with (2 * (- a)) by lia.
  destruct (Z.eq_dec n 0) as [->|].
  - rewrite !Z.testbit_even_0. reflexivity.
  - replace n with (Z.succ (n - 1)) by lia. rewrite !Z.testbit_even_succ by lia. symmetry. apply Z.land_spec.
Qed.

Lemma lowbit_pow2 : ltac2:(zQ "90!h9!m6!mc!n1!l4!n7!l9!nc!m0>1m$0>0@2$7Z^1@2$5$0\1k$0@2$1@2$2Z^1@2$1@3$4$0@2$6^3@1$8^3@2$3+2^1@2$2@2$3+2^1^3").
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

Lemma land_opp_pow2 : ltac2:(zQ "60!n1!h9!l4!l9!mc!m0>1k$1>0@2$4Z^1@3$2$1@2$3@2$0+2^2@1$5@2$0+2^2@2$0+2^2").
Proof. intros k.
  intros Hk. apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_opp, Z.pow2_bits_eqb by lia.
  rewrite <- Z.ones_equiv, Z.testbit_ones by lia.
  destruct (Z.eqb_spec k n); cbn [andb]; [|reflexivity].
  subst. replace (n <? n) with false by (symmetry; apply Z.ltb_irrefl). destruct (0 <=? n); reflexivity.
Qed.

Lemma lowbit_nonzero : ltac2:(zQ "80!h9!m6!mc!n1!l4!n7!rf!nc>1m$0>0@2$7Z^1@2$5$0\1k$0@2$1@2$2Z^1@2$1@3$4$0@1$6^3@2$3+2^1@2$2@2$3+2^1^3").
Proof. intros m. intros. unfold lowbit. apply lowbit_pow2. assumption. Qed.

Lemma ctz32_pow2 : ltac2:(zQ "50!h9!l4!s8!mc!n1>1k$0>0@2$3Z^1@3$1$0@1$2@2$4+2^2^2").
Proof. intros k. intros. unfold ctz32, lowbit. rewrite land_opp_pow2 by lia. apply Z.log2_pow2. lia. Qed.

Lemma lowbit_testbit : ltac2:(zQ "80!h9!l4!u8!uf!rf!mc!n1!v6>1v$0>1k$0>0@2$5Z^1>0@3$1$0@1$4^3@2$6+2^2@3$1$2@2$7^4^3$3").
Proof.
  intros v k Hk E. unfold lowbit in E.
  assert (T : Z.testbit (Z.land v (- v)) k = true) by (rewrite E; apply Z.pow2_bits_true; lia).
  rewrite Z.land_spec in T. apply andb_prop in T. tauto.
Qed.

(* [comment removed for export] *)
Lemma sub_bit_ldiff : ltac2:(zQ "90!h9!l4!mc!n1!u8!uf!hg0!hg8!v6>1f$0>1i$0>0@2$2Z^2>0@2$2Z^2>0@3$1$4@2$8^4^3$5@3$1$0@2$7^5@2$3+2^4@2$6^5@2$3+2^4").
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

Lemma testbit_sub_bit : ltac2:(zQ "b0!h9!mc!v6!u8!l4!hge!hh5!uf!hhc!n1!hg8>1f$0>1i$0>1j$0>0@2$1Z^3>0@2$1Z^3>0@2$1Z^3>0@3$4$3@2$2^6^5$7@3$4$3@2$2@2$a^7@2$9+2^6^5@2$5@2$2^7^5@1$6@2$8^6^5").
Proof. intros f i j.
  intros Hf Hi Hj Hb. rewrite (sub_bit_ldiff f i Hf Hi Hb), Z.ldiff_spec, Z.pow2_bits_eqb by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma lowbit_idiom : ltac2:(zQ "h00!h9!m6!l4!rf!mc!v6!u8!hg8!hge!hh5!uf!n7!s8!hhc!nc!n1>1m$0>0@2$eZ^1@2$b$0\1k$0@2$1@2$4Z^1@2$1@3$2$0@1$3^3@2$f+2^1@2$1@3$2$0@1$c@1$3^3^1@2$1@3$2$6@2$5^3^1$a@2$1@2$4Z@2$7^3@1$3^3>1j$0>0@2$4Z^1@3$2$6@2$5@2$7^5@1$3^5^2@2$8@2$5^5^2@1$9@2$d^3^2").
Proof. intros m.
  intros Hm. destruct (lowbit_nonzero m Hm) as (k & Hk & E & L). exists k.
  pose proof (lowbit_testbit m k Hk E) as Tb.
  split; [exact Hk|]. split; [exact E|]. split; [rewrite E; apply ctz32_pow2; exact Hk|]. split; [exact Tb|].
  rewrite E. split; [lia|]. intros j Hj. apply testbit_sub_bit; auto; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
