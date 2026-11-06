(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.bndiv.lib.Lib Require Import Tac Arr.
From OSSVerify.Proofs.openssl.bndiv.lib.BnP Require Import BnKit.
From OSSVerify.Proofs.openssl.bndiv.lib.BnW Require Import BnTac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Ltac show_s :=
  let v := reg_val 9%Z in idtac "s1 =" v; let v := reg_val 18%Z in idtac "s2 =" v; let v := reg_val 19%Z in idtac "s3 =" v;
  let v := reg_val 20%Z in idtac "s4 =" v; let v := reg_val 21%Z in idtac "s5 =" v; let v := reg_val 22%Z in idtac "s6 =" v;
  let v := reg_val 23%Z in idtac "s7 =" v.

(* [comment removed for export] *)
Lemma swrap32_wrap64 : forall x d, -2147483648 <= x + d < 2147483648 -> bv_swrap 32 (bv_unsigned (Z_to_bv 64 x) + d) = x + d.
Proof.
  intros x d H. rewrite Z_to_bv_unsigned. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 32) with 4294967296. change (4294967296 `div` 2) with 2147483648. change (2 ^ Z.of_N 64) with 18446744073709551616.
  Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Lemma unsigned_int_zero : forall y, -9223372036854775808 <= y < 9223372036854775808 -> bv_unsigned (Z_to_bv 64 y) = 0 -> y = 0.
Proof.
  intros y H. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with 18446744073709551616.
  Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Lemma bk_rw_cells_recast : forall segs m A cs cs',
  rw_cells segs m A cs -> cells_wf cs' -> cells_bytes cs' = cells_bytes cs -> cells_size cs' = cells_size cs ->
  rw_cells segs m A cs'.
Proof. intros segs m A cs cs' [[Hwf Hb] Hw] Hwf' Eb Es. split; [split; [exact Hwf'| rewrite Eb; exact Hb] | rewrite Es; exact Hw]. Qed.

Lemma bk_rw_cells_app : forall segs m A cs1 cs2,
  rw_cells segs m A (cs1 ++ cs2) <-> rw_cells segs m A cs1 /\ rw_cells segs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros segs m A cs1 cs2. unfold rw_cells, cells_at.
  rewrite cells_wf_app, cells_bytes_app, cells_size_app, Nat2Z.inj_add.
  rewrite wr_at_app by lia. rewrite bytes_at_app.
  assert (L : cells_wf cs1 -> length (cells_bytes cs1) = cells_size cs1) by apply cells_bytes_length.
  split.
  - intros [[[W1 W2] [B1 B2]] [R1 R2]]. rewrite (L W1) in B2. tauto.
  - intros [[[W1 B1] R1] [[W2 B2] R2]]. rewrite (L W1). tauto.
Qed.

(* [comment removed for export] *)
Ltac cell_of_bytes bs ::=
  lazymatch bs with
  | le8 ?v => constr:(C8 v)
  | le4 ?v => constr:(C4 v)
  | le2 ?v => constr:(C2 v)
  | [?b] => constr:(C1 b)
  | le1 (zxb ?b) => constr:(C1 b)
  | Z_to_le_bytes 8 0 => constr:(C8 (Z_to_bv 64 0))
  end.

(* [comment removed for export] *)
Definition hide (P : Prop) : Prop := P.
Lemma hide_intro : forall P : Prop, P -> hide P. Proof. intros P H. exact H. Qed.
Lemma hide_elim : forall P : Prop, hide P -> P. Proof. intros P H. exact H. Qed.
Global Opaque hide.
