(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.ct.lib.Lib Require Import Tac Arr.
From OSSVerify.Proofs.openssl.ct.lib.BnW Require Import BnTac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
Lemma lts_small : forall x y, (0 <= x < 9223372036854775808)%Z -> (0 <= y < 9223372036854775808)%Z ->
  bv_lts (Z_to_bv 64 x) (Z_to_bv 64 y) = (x <? y)%Z.
Proof.
  intros x y Hx Hy. unfold bv_lts. rewrite !zb_signed.
  rewrite !inr64_unsigned_lit by (unfold inr64; change (2 ^ 64)%Z with 18446744073709551616%Z; lia).
  change (2 ^ 63)%Z with 9223372036854775808%Z.
  rewrite (proj2 (Z.ltb_lt x 9223372036854775808)), (proj2 (Z.ltb_lt y 9223372036854775808)) by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Definition hide (P : Prop) : Prop := P.
Lemma hide_intro : forall P : Prop, P -> hide P. Proof. intros P H. exact H. Qed.
Lemma hide_elim : forall P : Prop, hide P -> P. Proof. intros P H. exact H. Qed.
Global Opaque hide.

(* [comment removed for export] *)
Ltac show_s :=
  let v := reg_val 9%Z in idtac "s1 =" v; let v := reg_val 18%Z in idtac "s2 =" v; let v := reg_val 19%Z in idtac "s3 =" v;
  let v := reg_val 20%Z in idtac "s4 =" v; let v := reg_val 21%Z in idtac "s5 =" v; let v := reg_val 22%Z in idtac "s6 =" v;
  let v := reg_val 23%Z in idtac "s7 =" v.


(* [comment removed for export] *)
Lemma lts_signed : forall x y, (-9223372036854775808 <= x < 9223372036854775808)%Z -> (-9223372036854775808 <= y < 9223372036854775808)%Z ->
  bv_lts (Z_to_bv 64 x) (Z_to_bv 64 y) = (x <? y)%Z.
Proof.
  intros x y Hx Hy. unfold bv_lts. rewrite !Z_to_bv_signed.
  rewrite !bv_swrap_small by (unfold bv_half_modulus, bv_modulus; change (2 ^ Z.of_N 64 `div` 2)%Z with 9223372036854775808%Z; lia).
  reflexivity.
Qed.

(* [comment removed for export] *)
Lemma bn_swrap32_mod : forall z k, (-2147483648 <= z + k < 2147483648)%Z ->
  bv_swrap 32 (z mod 18446744073709551616 + k) = (z + k)%Z.
Proof.
  intros z k H. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 32)%Z with 4294967296%Z. change (4294967296 `div` 2)%Z with 2147483648%Z.
  Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Lemma wr_at_sub : forall segs m A n k n', wr_at segs m A n -> (0 <= k)%Z -> (0 <= n')%Z -> (k + n' <= n)%Z -> wr_at segs m (A + k) n'.
Proof.
  intros segs m A n k n' (H0 & H1 & H) Hk Hn' Hle. split; [lia|]. split; [lia|].
  intros i Hi. replace (A + k + i)%Z with (A + (k + i))%Z by lia. apply H. lia.
Qed.

