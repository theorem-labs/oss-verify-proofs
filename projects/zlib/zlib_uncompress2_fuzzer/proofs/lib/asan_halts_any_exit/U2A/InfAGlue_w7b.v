(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.Lib Require Import MState Mem ZBridge.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.U2A Require Import U2AKit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Definition sidx (val rb op H : Z) : Z := val + (H mod 2 ^ (rb + op)) / 2 ^ rb.
Lemma sidx_range : forall (rb op H : Z), 0 <= rb -> 0 <= op -> 0 <= (H mod 2 ^ (rb + op)) / 2 ^ rb < 2 ^ op.
Proof.
  intros rb op H Hr Ho. assert (P : 0 < 2 ^ rb) by (apply Z.pow_pos_nonneg; lia).
  pose proof (Z.mod_pos_bound H (2 ^ (rb + op)) ltac:(apply Z.pow_pos_nonneg; lia)) as M.
  split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|]. rewrite <- Z.pow_add_r by lia. lia.
Qed.
Lemma srlw_wrap_small : forall x k, 0 <= x < 2147483648 -> 0 <= k <= 31 ->
  bv_swrap 32 (Z.shiftr (bv_wrap 32 x) (k mod 32)) = x / 2 ^ k.
Proof.
  intros x k Hx Hk. rewrite (Z.mod_small k 32) by lia.
  replace (bv_wrap 32 x) with x by (unfold bv_wrap, bv_modulus; change (2 ^ Z.of_N 32) with 4294967296; rewrite Z.mod_small by lia; reflexivity).
  rewrite Z.shiftr_div_pow2 by lia. assert (P : 0 < 2 ^ k) by (apply Z.pow_pos_nonneg; lia).
  assert (0 <= x / 2 ^ k <= x) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; [lia | nia]]).
  apply swrap32_small. lia.
Qed.
Lemma zext32_shift30 : forall x, 0 <= x < 4294967296 ->
  Z.shiftr (Z.shiftl x 32 mod 18446744073709551616) 30 = 4 * x.
Proof.
  intros x Hx. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
  rewrite Z.mod_small by (change (2 ^ 32) with 4294967296; lia).
  change (2 ^ 32) with (4 * 2 ^ 30). rewrite Z.mul_assoc, Z.div_mul by lia. lia.
Qed.

Definition w7hide (P : Prop) : Prop := P.
Lemma w7hide_in : forall P : Prop, P -> w7hide P. Proof. intros P H. exact H. Qed.
Lemma w7hide_out : forall P : Prop, w7hide P -> P. Proof. intros P H. exact H. Qed.
