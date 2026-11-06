(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.bndiv.lib.Lib Require Import Tac Arr.
From OSSVerify.Proofs.openssl.bndiv.lib.BnW Require Import BnMem.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Open Scope bv_scope.

Lemma u8_lit : forall f, (0 <= f < 256)%Z -> bv_unsigned (Z_to_bv 8 f) = f.
Proof. intros f Hf. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. change (2 ^ Z.of_N 8)%Z with 256%Z. lia. Qed.

Lemma land64_zero_iff : forall x, (-9223372036854775808 <= x < 9223372036854775808)%Z ->
  (Z.land x 18446744073709551615 = 0 <-> x = 0)%Z.
Proof.
  intros x Hx. change 18446744073709551615%Z with (Z.ones 64). rewrite Z.land_ones by lia.
  change (2 ^ 64)%Z with 18446744073709551616%Z. split; intros H; [|subst x; reflexivity].
  Z.div_mod_to_equations. lia.
Qed.


(* [comment removed for export] *)
Lemma land64_pos_iff : forall c, (-9223372036854775808 <= c < 9223372036854775808)%Z ->
  ((0 <? Z.land c 18446744073709551615) && (Z.land c 18446744073709551615 <? 9223372036854775808))%Z = (0 <? c)%Z.
Proof.
  intros c Hc. change 18446744073709551615%Z with (Z.ones 64). rewrite Z.land_ones by lia.
  change (2 ^ 64)%Z with 18446744073709551616%Z.
  destruct (Z.ltb_spec 0 c) as [H|H].
  - rewrite Z.mod_small by lia. apply andb_true_iff. split; apply Z.ltb_lt; lia.
  - apply andb_false_iff. destruct (Z.eq_dec c 0) as [->|N]; [left; reflexivity|].
    right. apply Z.ltb_ge. Z.div_mod_to_equations. lia.
Qed.

Lemma land64_neg_iff : forall c, (-9223372036854775808 <= c < 9223372036854775808)%Z ->
  (9223372036854775808 <= Z.land c 18446744073709551615 <-> c < 0)%Z.
Proof.
  intros c Hc. change 18446744073709551615%Z with (Z.ones 64). rewrite Z.land_ones by lia.
  change (2 ^ 64)%Z with 18446744073709551616%Z. split; intros H; Z.div_mod_to_equations; lia.
Qed.

(* [comment removed for export] *)
Lemma sllw_small : forall c k, (0 <= c)%Z -> (0 <= k < 32)%Z -> (c * 2 ^ k < 2147483648)%Z ->
  bv_swrap 32 (Z.shiftl c (k mod 32)) = (c * 2 ^ k)%Z.
Proof.
  intros c k Hc Hk Hs. rewrite Z.mod_small by lia. rewrite Z.shiftl_mul_pow2 by lia.
  apply BnMem.bn_swrap32_small. assert (0 <= 2 ^ k)%Z by (apply Z.pow_nonneg; lia). nia.
Qed.

(* [comment removed for export] *)
Lemma land64_le_small : forall v c, (-9223372036854775808 <= v < 9223372036854775808)%Z -> (0 <= c < 9223372036854775808)%Z ->
  (Z.land v 18446744073709551615 <= c <-> 0 <= v <= c)%Z.
Proof.
  intros v c Hv Hc. change 18446744073709551615%Z with (Z.ones 64). rewrite Z.land_ones by lia.
  change (2 ^ 64)%Z with 18446744073709551616%Z. split; intros H; Z.div_mod_to_equations; lia.
Qed.
