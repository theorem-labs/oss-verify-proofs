(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzTac BzTac2. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpArith.
From Stdlib Require Lia. 
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require ZBridge.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require ACeil.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpLia.
Module CmpSdArith.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.PropExec.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Tac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.WalkLib OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.ZBridge.Bytes.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzTac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpArith.
 Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.ACeil.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpLia.   (* [comment removed for export] *)
Section ACeilS1. Context {ACEIL__ : ACeil}.


(* [comment removed for export] *)
Lemma low32_swrap_mod64 : forall v, (bv_swrap 32 v mod 18446744073709551616) mod M32 = v mod M32.
Proof. intros. rewrite mod64_mod32, swrap32_mod32. reflexivity. Qed.

(* [comment removed for export] *)
Lemma shr_2p31 : forall l, 0 <= l <= 31 -> Z.shiftr 2147483648 l = Z.shiftl 1 (32 - l - 1).
Proof.
  intros l Hl. rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia.
  change 2147483648 with (2 ^ 31). replace 31 with ((32 - l - 1) + l) at 1 by lia.
  rewrite Z.pow_add_r by lia. rewrite Z.div_mul by (apply Z.pow_nonzero; lia). lia.
Qed.
Lemma shl1_range : forall k, 0 <= k <= 31 -> 0 < Z.shiftl 1 k < M32.
Proof.
  intros k Hk. rewrite Z.shiftl_mul_pow2 by lia. change M32 with (2 ^ 32).
  pose proof (Z.pow_lt_mono_r 2 k 32 ltac:(lia) ltac:(lia)). pose proof (Z.pow_pos_nonneg 2 k ltac:(lia) ltac:(lia)). lia.
Qed.

(* [comment removed for export] *)
Lemma low32_or_bit : forall l (x : word) buff, 0 <= l <= 31 -> bv_unsigned x mod M32 = buff -> 0 <= buff < M32 ->
  bv_unsigned (Z_to_bv 64 (Z.lor (bv_swrap 32 (Z.shiftr 2147483648 (l mod 32)) mod 18446744073709551616) (bv_unsigned x))) mod M32
  = Z.lor buff (Z.shiftl 1 (32 - l - 1) mod M32).
Proof.
  intros l x buff Hl Hx Hb. rewrite (Z.mod_small l 32) by lia.
  rewrite low32_lit, low32_lor, low32_swrap_mod64, Hx, shr_2p31 by lia.
  pose proof (shl1_range (32 - l - 1) ltac:(lia)).
  rewrite (Z.mod_small (Z.shiftl 1 (32 - l - 1)) M32) by lia. apply Z.lor_comm.
Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma lor_bit_range : forall buff l, 0 <= buff < M32 -> 0 <= l <= 31 -> 0 <= Z.lor buff (Z.shiftl 1 (32 - l - 1) mod M32) < M32.
Proof.
  intros. change M32 with (2 ^ 32). apply lor_lt_pow2; [change (2^32) with M32; lia|]. apply Z.mod_pos_bound. lia.
Qed.

(* [comment removed for export] *)
Lemma lor_shl0 : forall buff s, Z.lor buff (Z.shiftl 0 s mod M32) = buff.
Proof. intros. rewrite Z.shiftl_0_l, Z.mod_0_l by lia. apply Z.lor_0_r. Qed.

End ACeilS1.
End CmpSdArith.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Open Scope Z_scope.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpLia.   (* [comment removed for export] *)
Section ACeilS1. Context {ACEIL__ : ACeil}.


(* [comment removed for export] *)
Lemma low32_inc_sx32 : forall v k, bv_unsigned (Z_to_bv 64 (bv_swrap 32 (bv_unsigned (sx32 (Z_to_bv 64 v)) + k))) mod M32 = (v + k) mod M32.
Proof.
  intros v k. rewrite low32_lit, swrap32_mod32, low32_add, low32_sx32, low32_lit, <- low32_add. reflexivity.
Qed.
(* [comment removed for export] *)
Lemma low32_inc64_sx32 : forall v k, bv_unsigned (Z_to_bv 64 (bv_unsigned (sx32 (Z_to_bv 64 v)) + k)) mod M32 = (v + k) mod M32.
Proof.
  intros v k. rewrite low32_lit, low32_add, low32_sx32, low32_lit, <- low32_add. reflexivity.
Qed.
Lemma low32_inc64_sx32_mod : forall v k, bv_unsigned (Z_to_bv 64 ((bv_unsigned (sx32 (Z_to_bv 64 v)) + k) mod 18446744073709551616)) mod M32 = (v + k) mod M32.
Proof.
  intros v k. rewrite low32_lit, mod64_mod32, low32_add, low32_sx32, low32_lit, <- low32_add. reflexivity.
Qed.
(* [comment removed for export] *)
Lemma swrap32_zero_iff : forall x, bv_swrap 32 x = 0 <-> x mod M32 = 0.
Proof.
  intros x. pose proof (swrap32_mod32 x) as E.
  assert (R : -2147483648 <= bv_swrap 32 x < 2147483648).
  { unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. cbn -[Z.add Z.sub Z.modulo Z.mul Z.opp].
    change (2 ^ 32 / 2) with 2147483648. change (2 ^ 32) with 4294967296.
    pose proof (Z.mod_pos_bound (x + 2147483648) 4294967296 ltac:(lia)). lia. }
  split; intros H.
  - rewrite H in E. rewrite Z.mod_0_l in E by lia. congruence.
  - rewrite H in E. apply Z.mod_divide in E; [|lia]. destruct E as [q Hq]. assert (q = 0) by lia. subst q. lia.
Qed.
Lemma inc_sx32_mod : forall v, (bv_unsigned (sx32 (Z_to_bv 64 v)) + 1) mod M32 = (v + 1) mod M32.
Proof. intros v. rewrite low32_add, low32_sx32, low32_lit, <- low32_add. reflexivity. Qed.

(* [comment removed for export] *)
Lemma b2z_range : forall b, 0 <= Z.b2z b <= 1. Proof. intros [|]; cbn; lia. Qed.
Lemma lor_b2z : forall a b, Z.lor (Z.b2z a) (Z.b2z b) = Z.b2z (a || b). Proof. intros [|] [|]; reflexivity. Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma swrap32_mod64_zero_iff : forall x, (bv_swrap 32 x) mod 18446744073709551616 = 0 <-> x mod M32 = 0.
Proof.
  intros x. rewrite <- swrap32_zero_iff.
  assert (R : -2147483648 <= bv_swrap 32 x < 2147483648).
  { unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. cbn -[Z.add Z.sub Z.modulo Z.mul Z.opp].
    change (2 ^ 32 / 2) with 2147483648. change (2 ^ 32) with 4294967296.
    pose proof (Z.mod_pos_bound (x + 2147483648) 4294967296 ltac:(lia)). lia. }
  split; intros H; [|rewrite H; reflexivity].
  destruct (Z.eq_dec (bv_swrap 32 x) 0) as [E|NE]; [exact E|].
  exfalso. destruct (Z_lt_le_dec (bv_swrap 32 x) 0).
  - replace (bv_swrap 32 x mod 18446744073709551616) with (bv_swrap 32 x + 18446744073709551616) in H by (apply Z.mod_unique with (q := -1); lia). lia.
  - rewrite Z.mod_small in H by lia. lia.
Qed.
End ACeilS1.


(* [comment removed for export] *)
Ltac cells_eq_by H :=
  lazymatch goal with |- rw_cells _ _ _ ?L1 =>
    lazymatch type of H with rw_cells _ _ _ ?L2 =>
      replace L1 with L2; [exact H|];
      repeat first [ reflexivity
                   | lazymatch goal with
                     | |- @eq Z _ _ => lia
                     | |- Z_to_bv _ _ = Z_to_bv _ _ => f_equal
                     | |- _ => progress f_equal
                     end ]
    end
  end.
Section ACeilS2. Context {ACEIL__ : ACeil}.


(* [comment removed for export] *)
Lemma mod16_lin : forall x, x mod 16 = 0 -> exists q, x = 16 * q.
Proof. intros x H. exists (x / 16). pose proof (Z.div_mod x 16 ltac:(lia)). lia. Qed.
Lemma mod16_of_lin : forall q k, (16 * q + 16 * k) mod 16 = 0.
Proof. intros. rewrite <- Z.mul_add_distr_l, Z.mul_comm. apply Z_mod_mult. Qed.

End ACeilS2.
