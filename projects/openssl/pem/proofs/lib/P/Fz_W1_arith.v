(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.openssl.pem.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma t_div3_magic : forall x, 0 <= x < 2 ^ 32 -> x * 2863311531 / 2 ^ 33 = x / 3.
Proof.
  intros x Hx. pose proof (Z.div_mod x 3 ltac:(lia)) as DM. pose proof (Z.mod_pos_bound x 3 ltac:(lia)) as MB.
  symmetry. apply (Z.div_unique _ _ _ (x / 3 + (x mod 3) * 2863311531)); lia.
Qed.

Lemma t_grow_n : forall x, 0 <= x < 2 ^ 31 ->
  bv_unsigned (Z_to_bv 64 (bv_swrap 32 (bv_wrap 32 (bv_unsigned (Z_to_bv 64 (bv_unsigned (Z_to_bv 64
     ((bv_unsigned (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 x) ≪ 32)) * 12297829383904690176) ≫ 64)) ≫ 31))) ≫ 2))) ≪ 2 = x / 3 * 4.
Proof.
  intros x Hx.
  rewrite (unsigned_lit x) by lia.
  rewrite (Z.shiftl_mul_pow2 x 32) by lia. rewrite (unsigned_lit (x * 2 ^ 32)) by lia.
  replace (x * 2 ^ 32 * 12297829383904690176) with (x * 2863311531 * 2 ^ 64) by lia.
  rewrite (Z.shiftr_div_pow2 (x * 2863311531 * 2 ^ 64) 64) by lia. rewrite Z.div_mul by lia.
  rewrite (unsigned_lit (x * 2863311531)) by lia.
  rewrite (Z.shiftr_div_pow2 (x * 2863311531) 31) by lia.
  assert (C31 : 0 <= x * 2863311531 / 2 ^ 31 < 2 ^ 32).
  { split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; lia. }
  rewrite (unsigned_lit (x * 2863311531 / 2 ^ 31)) by lia.
  unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 32) with (2 ^ 32). rewrite (Z.mod_small _ _ C31).
  rewrite (Z.shiftr_div_pow2 (x * 2863311531 / 2 ^ 31) 2) by lia. rewrite Z.div_div by lia. change (2 ^ 31 * 2 ^ 2) with (2 ^ 33).
  rewrite t_div3_magic by lia.
  assert (Q : 0 <= x / 3 < 2 ^ 30). { split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; lia. }
  unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 32) with (2 ^ 32). change (2 ^ 32 `div` 2) with (2 ^ 31).
  rewrite (Z.mod_small (x / 3 + 2 ^ 31)) by lia.
  replace (x / 3 + 2 ^ 31 - 2 ^ 31) with (x / 3) by lia.
  rewrite (unsigned_lit (x / 3)) by lia. rewrite Z.shiftl_mul_pow2 by lia. reflexivity.
Qed.
