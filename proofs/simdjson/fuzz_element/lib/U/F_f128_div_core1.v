(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import Sf_lib.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import F_sf_helpers F_sf_helpers2 F_f128_mul_core1 F_sf_helpers3 F_f128_div_wide.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Ltac flia ::= flia_fast.
Local Ltac unfold_sf_in H ::= unfold_sf_in_recast H.
Local Ltac blia ::= blia_fast.

Local Ltac step ::= step_fast.
Local Ltac zsimp ::= zsimp_fast.

Definition div_core_mid_pc := 0x11110%Z.

Lemma A4_even : forall x,
  Z.land (Z.land (Z.shiftl x 1) 18446744073709551615) 4294967294 = Z.land (Z.land (Z.shiftl x 1) 18446744073709551615) 4294967295.
Proof.
  intros x. apply Z.bits_inj'. intros i Hi. rewrite !Z.land_spec.
  destruct (Z.eq_dec i 0) as [->|Hnz].
  - rewrite Z.shiftl_spec_low by lia. reflexivity.
  - f_equal.
    replace 4294967295 with (Z.lor 4294967294 1) by reflexivity.
    rewrite Z.lor_spec. replace (Z.testbit 1 i) with false. { now rewrite orb_false_r. }
    symmetry. change 1 with (2^0). rewrite Z.pow2_bits_eqb by lia. apply Z.eqb_neq. lia.
Qed.

Lemma half_iter_range : forall x b, 0 <= half_iter x b < 18446744073709551616.
Proof.
  intros. unfold half_iter, shl64, mul64, mulhu, sub64.
  apply Z_lor_range.
  - apply (zr_shiftr _ 63). apply SoftFloat.wrap64_range. lia.
  - apply SoftFloat.wrap64_range.
Qed.
Ltac hi_rng X := let RX := fresh "R" X in
  assert (RX : 0 <= X < 18446744073709551616) by (cbv delta [X]; apply half_iter_range).
Ltac mulhu_rng X := let RX := fresh "R" X in
  assert (RX : 0 <= X < 18446744073709551616) by (cbv delta [X]; apply mulhu_range; (change (inr64 _) || idtac); zrange).

