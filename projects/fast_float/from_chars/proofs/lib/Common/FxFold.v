(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import FxLin FxCore.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Lemma bvm64 : bv_modulus 64 = two64. Proof. reflexivity. Qed.
Lemma uZ : forall x, 0 <= x < two64 -> bv_unsigned (Z_to_bv 64 x) = x.
Proof. intros x Hx. rewrite Z_to_bv_unsigned. apply bv_wrap_small. rewrite bvm64. exact Hx. Qed.
Lemma wrap64 : forall z, bv_wrap 64 z = w64 z.
Proof. intros z. rewrite w64_mod. reflexivity. Qed.

Lemma sgn64_ok : forall x, 0 <= x < two64 -> bv_signed (Z_to_bv 64 x) = sgn64 x.
Proof.
  intros x Hx. unfold bv_signed, bv_swrap. rewrite uZ by exact Hx. unfold bv_wrap.
  change (bv_half_modulus 64) with 9223372036854775808. change (bv_modulus 64) with 18446744073709551616.
  unfold sgn64, T63, two64 in *.
  destruct (Z.ltb_spec x 9223372036854775808).
  - rewrite Z.mod_small by lia. lia.
  - replace (x + 9223372036854775808) with ((x - 9223372036854775808) + 1 * 18446744073709551616) by lia.
    rewrite Z_mod_plus_full. rewrite Z.mod_small by lia. lia.
Qed.

Lemma alu_z_ok : forall op x y, 0 <= x < two64 -> 0 <= y < two64 ->
  alu_z op x y = bv_unsigned (alu64 op (Z_to_bv 64 x) (Z_to_bv 64 y)).
Proof.
  intros op x y Hx Hy. destruct op; cbn [alu_z alu64 alu]; try reflexivity.
  - rewrite bv_add_unsigned, !uZ by assumption. symmetry. apply wrap64.
  - rewrite bv_sub_unsigned, !uZ by assumption. symmetry. apply wrap64.
  - rewrite bv_shiftl_unsigned, bv_and_unsigned, !uZ by (assumption || (unfold two64; lia)). symmetry. apply wrap64.
  - unfold bv_lts. rewrite !sgn64_ok by assumption. destruct (Z.ltb (sgn64 x) (sgn64 y)); reflexivity.
  - unfold bv_ltu. rewrite !uZ by assumption. destruct (Z.ltb x y); reflexivity.
  - rewrite bv_xor_unsigned, !uZ by assumption. reflexivity.
  - rewrite bv_shiftr_unsigned, bv_and_unsigned, !uZ by (assumption || (unfold two64; lia)). reflexivity.
  - rewrite bv_or_unsigned, !uZ by assumption. reflexivity.
  - rewrite bv_and_unsigned, !uZ by assumption. reflexivity.
Qed.

Lemma br_z_ok : forall c x y, 0 <= x < two64 -> 0 <= y < two64 ->
  br_z c x y = branch_taken c (Z_to_bv 64 x) (Z_to_bv 64 y).
Proof.
  intros c x y Hx Hy. destruct c; cbn [br_z branch_taken]; unfold bv_eqb, bv_ltu, bv_lts; rewrite ?uZ by assumption;
    rewrite ?sgn64_ok by assumption; reflexivity.
Qed.
