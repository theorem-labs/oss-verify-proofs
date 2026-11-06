(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import PropExec MState Mem.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib4Init9Datatypes04list37Corelib7Numbers7BinNumshe1Z37Corelib4Init5Logicjb3and37Corelib5Lists7ListDefl56Forall46Stdlib6ZArith6BinInt1Zn52len52lt79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Bytes~~~~~~p76le_val06lengthp78bytes_okn56of_natn53pow04booln57testbitjb2eqn53addn53ltbn53muln53subn54landn53lor05falsen56modulon54lnotn54lxorn56shiftlhe4Npos35stdpp9bitvectorbdefinitionshm62bvl53maphm6bbv_unsigned3h5LinuxProcessSemanticsfLinuxProcessSem6BvBasehpedbytes_le_to_Z" s.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint le_val (bs : list Z) : Z :=
  match bs with [] => 0 | b :: bs' => b + 256 * le_val bs' end.
Definition bytes_ok : ltac2:(zQ "20!h8!j7>2bs@1$0$1P") := ltac2:(zQ "60!j7!h8!kf!mc!od!p2\2bs@1$1$0@3$3$0\1b$0@2$2@2$4Z^1@2$5^1+hg0^1").

Lemma le_val_range : ltac2:(zQ "a0!j7!t3!tc!h8!kf!u4!od!p2!uf!v8>2bs@1$3$0>0@1$5^1@2$4@2$6Z@1$1^2@2$7@1$1^2@2$9+hg0@1$8@2$2$0^2").
Proof.
  induction bs as [|b bs IH]; intros H; cbn [le_val length]; [lia|].
  inversion H; subst. specialize (IH ltac:(assumption)).
  rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. lia.
Qed.

Lemma testbit_split : ltac2:(zQ "b0!ve!j7!hg4!od!kf!hge!hh3!p2!hh9!hhf!hi5>1x$1>1y$1>1i$1>0@2$4@2$3Z^3@2$7^3+hg0>0@2$3Z^2@3$5$0@2$2@2$6^5@2$9+hg0^4^3M0\0$0$0@2$8^3+8@2$2^5^3@2$2^4@2$a^3+8").
Proof.
  intros x y i Hx Hi. destruct (Z.ltb_spec0 i 8).
  - rewrite <- (Z.mod_pow2_bits_low _ 8) by lia. change (2^8) with 256.
    rewrite (Z.mul_comm 256 y), Z.mod_add, Z.mod_small by lia. reflexivity.
  - replace i with ((i - 8) + 8) at 1 by lia. rewrite <- Z.div_pow2_bits by lia. change (2^8) with 256.
    rewrite (Z.mul_comm 256 y), Z.div_add, Z.div_small, Z.add_0_l by lia. reflexivity.
Qed.

Lemma land_lt_pow2 : ltac2:(zQ "60!j7!od!kf!hib!p2!v8>1a$0>1b$0>1n$0>0@2$2@2$1Z^3@2$4^3@2$5+2^1>0@2$1Z^3@2$2@2$1Z@2$3^5^4@2$4@2$3^5^4@2$5+2^3").
Proof.
  intros a b n Ha Hb.
  assert (Hn : 0 <= n). { destruct (Z.le_gt_cases 0 n); [assumption|]. rewrite Z.pow_neg_r in Ha by lia. lia. }
  pose proof (Z.land_nonneg a b) as Hnn. split; [lia|].
  destruct (Z.eq_dec (Z.land a b) 0) as [->|Hnz]. { apply Z.pow_pos_nonneg; lia. }
  destruct (Z.eq_dec a 0) as [->|Haz]. { rewrite Z.land_0_l. apply Z.pow_pos_nonneg; lia. }
  apply (proj2 (Z.log2_lt_pow2 (Z.land a b) n ltac:(lia))).
  pose proof (Z.log2_land a b ltac:(lia) Hb). assert (Z.log2 a < n) by (apply Z.log2_lt_pow2; lia). lia.
Qed.

Lemma lor_lt_pow2 : ltac2:(zQ "60!kf!j7!od!p2!v8!hj2>1a$1>1b$1>1n$1>0@2$0@2$2Z^3@2$3^3@2$4+2^1>0@2$0@2$2Z^3@2$3^3@2$4+2^2@2$0@2$2Z@2$5^5^4@2$3@2$5^5^4@2$4+2^3").
Proof.
  intros a b n Ha Hb.
  assert (Hn : 0 <= n). { destruct (Z.le_gt_cases 0 n); [assumption|]. rewrite Z.pow_neg_r in Ha by lia. lia. }
  pose proof (Z.lor_nonneg a b) as Hnn. split; [lia|].
  destruct (Z.eq_dec a 0) as [->|]. { rewrite Z.lor_0_l. lia. }
  destruct (Z.eq_dec b 0) as [->|]. { rewrite Z.lor_0_r. lia. }
  assert (Hp : 0 < Z.lor a b). { destruct (Z.eq_dec (Z.lor a b) 0) as [E|]; [|lia]. apply Z.lor_eq_0_iff in E. lia. }
  apply (proj2 (Z.log2_lt_pow2 (Z.lor a b) n Hp)). rewrite Z.log2_lor by lia.
  apply Z.max_lub_lt; apply Z.log2_lt_pow2; lia.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)



Lemma testbit_high_false : ltac2:(zQ "90!j7!od!kf!ve!hj8!hge!p2!v8!hg4>1x$0>1n$0>1i$0>0@2$2@2$1Z^3@2$6^3@2$7+2^2>0@2$2@2$1Z^3@2$1^3^2@3$5$3@2$8^5^3$4").
Proof.
  intros x n i Hx Hi. destruct (Z.eq_dec x 0) as [->|]; [apply Z.bits_0|].
  apply Z.bits_above_log2; [lia|]. apply Z.lt_le_trans with n; [apply Z.log2_lt_pow2; lia|lia].
Qed.

Lemma land_mod_pow2_r : ltac2:(zQ "80!j7!hib!od!v8!kf!hge!p2!hjf>1a$0>1b$0>1n$0>0@2$4@2$2Z^3@2$6^3@2$3+2^1>0@2$2Z^2@3$5$0@2$1^5@2$7^4@2$3+2^3@2$1^5^4").
Proof.
  intros a b n Ha Hn. apply Z.bits_inj'. intros i Hi. rewrite !Z.land_spec.
  destruct (Z.lt_ge_cases i n).
  - rewrite Z.mod_pow2_bits_low by lia. reflexivity.
  - rewrite (testbit_high_false a n i) by lia. reflexivity.
Qed.

Lemma lnot_mod64 : ltac2:(zQ "90!j7!v8!kf!hge!od!hk8!p2!hkf!hjf>1w$0>0@2$2@2$4Z^1@2$6^1@2$1+2+k0@3$3$0@2$7^2+vvvvvvvvvvvvvvvf@2$8@1$5^2@2$1+2+k0").
Proof.
  intros w Hw. change 18446744073709551615 with (Z.ones 64). rewrite <- Z.land_ones by lia.
  apply Z.bits_inj'. intros i Hi. rewrite Z.lxor_spec, Z.land_spec, Z.lnot_spec by lia.
  destruct (Z.lt_ge_cases i 64).
  - rewrite Z.ones_spec_low by lia. rewrite xorb_true_r, andb_true_r. reflexivity.
  - rewrite Z.ones_spec_high by lia. rewrite xorb_false_r, andb_false_r.
    destruct (Z.eq_dec w 0) as [->|]; [apply Z.bits_0|].
    apply Z.bits_above_log2; [lia|]. apply Z.lt_le_trans with 64; [apply Z.log2_lt_pow2; lia|lia].
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma lor_shiftl8_add : ltac2:(zQ "90!j7!od!kf!hge!hh3!hj2!p2!hhf!hl6>1x$0>1y$0>0@2$2@2$1Z^2@2$6^2+hg0>0@2$1Z^2@3$3$0@2$5^4@2$8^3+8@2$4^4@2$7+hg0^3").
Proof.
  intros x y Hx Hy. rewrite Z.shiftl_mul_pow2 by lia. change (2^8) with 256.
  rewrite <- Z.lxor_lor. 2:{ apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
       replace (y * 256) with (0 + 256 * y) by lia. rewrite (testbit_split 0 y i) by lia.
       destruct (Z.ltb_spec0 i 8). { rewrite Z.bits_0. apply andb_false_r. }
       rewrite (Z.bits_above_log2 x i); [reflexivity|lia|].
       destruct (Z.eq_dec x 0) as [->|]; [cbn; lia|]. apply Z.lt_le_trans with 8; [apply Z.log2_lt_pow2; lia|lia]. }
  symmetry. replace (256 * y) with (y * 256) by lia. apply Z.add_nocarry_lxor.
  apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
  replace (y * 256) with (0 + 256 * y) by lia. rewrite (testbit_split 0 y i) by lia.
  destruct (Z.ltb_spec0 i 8). { rewrite Z.bits_0. apply andb_false_r. }
  rewrite (Z.bits_above_log2 x i); [reflexivity|lia|].
  destruct (Z.eq_dec x 0) as [->|]; [cbn; lia|]. apply Z.lt_le_trans with 8; [apply Z.log2_lt_pow2; lia|lia].
Qed.

Lemma bytes_ok_map : ltac2:(zQ "70!hlf!ho3!h8!ho9!j7!u4!hof>2bs@1$2@1$1@1$0#8@1$5@4$3@1$1@1$0#8$4@1$6@1$0#8^1").
Proof.
  induction bs as [|b bs IH]; cbn; constructor; [|exact IH].
  pose proof (bv_unsigned_in_range 8 b). unfold bv_modulus in *. change (2 ^ Z.of_N 8) with 256 in *. lia.
Qed.

Lemma bytes_le_to_Z_le_val : ltac2:(zQ "90!hlf!j7!ho3!h8!hge!ho9!hsd!t3!hof>2bs@1$3@1$2@1$0#8@3$4$1@1$6^1@1$7@4$5@1$2@1$0#8$1@1$8@1$0#8^1").
Proof.
  induction bs as [|b bs IH]; cbn [bytes_le_to_Z le_val map]; [reflexivity|].
  rewrite IH. apply lor_shiftl8_add.
  - pose proof (bv_unsigned_in_range 8 b). unfold bv_modulus in *. change (2 ^ Z.of_N 8) with 256 in *. lia.
  - pose proof (le_val_range (map bv_unsigned bs) (bytes_ok_map bs)). lia.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
