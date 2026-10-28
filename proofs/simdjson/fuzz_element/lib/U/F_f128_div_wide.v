(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import Sf_lib.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import F_sf_helpers F_sf_helpers2 F_f128_mul_core1 F_sf_helpers3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Ltac flia ::= flia_fast.
Local Ltac unfold_sf_in H ::= unfold_sf_in_recast H.
Local Ltac blia ::= blia_fast.

Local Ltac step ::= step_fast.
Local Ltac zsimp ::= zsimp_fast.

Definition saved_dc (bSigHiI : Z) (bLo s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra : word) (j : list byte) : list cell :=
  [C8 (Z_to_bv 64 bSigHiI); C8 bLo; CB 8 j; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Ltac sf_vocab ::=
  cbv beta delta [add64 sub64 mul64 shl64 not64 ltu64 eqz64 nez64 zext32 sext32 srliw mulhu
         is_neg64 sra63 lt_s64 lo64 hi64 wrap64
         ONES64 M32 SIGN64 MASK48 MASKLO ABS_HI INF_HI QUIET_HI QNAN_HI IMPLICIT_HI IMPL3_HI SPEC_K HALF60 DQUIET
         C_HW X_ADJ EXPK EXPK2];
  rewrite ?b2z_Zb2z.

Ltac folded_check :=
  lazymatch goal with
  | |- (let x := ?b in _) = _ => fail 0 "fold_model_lets stuck at a let with body" b
  | |- _ => idtac
  end.

Lemma carry_gcc : forall r0c r1, 0 <= r0c < 2^64 -> 0 <= r1 < 2^64 ->
  Z.b2z (Z.land (r0c + r1) 18446744073709551615 <? r0c)
  = Z.land (Z.land (Z.b2z (Z.lxor r1 (Z.lxor r0c 18446744073709551615) =? 0) - 1) 18446744073709551615) (Z.b2z (Z.lxor r0c 18446744073709551615 <? r1)).
Proof.
  intros r0c r1 H0 H1. rewrite zb_lxor_ones by lia.
  rewrite zb_lxor_eqb0. rewrite !land_W64.
  destruct (Z.eqb_spec r1 (18446744073709551615 - r0c)) as [E|NE].
  - cbn [Z.b2z]. rewrite Z.land_0_l.
    replace ((r0c + r1) mod 2^64 <? r0c) with false; [reflexivity|]. symmetry. apply Z.ltb_ge.
    Z.div_mod_to_equations. lia.
  - cbn [Z.b2z]. change ((0 - 1) mod 2 ^ 64) with 18446744073709551615.
    rewrite land_ones_l by (destruct (_ <? _); cbv; split; congruence).
    f_equal. apply eq_true_iff_eq. rewrite !Z.ltb_lt. Z.div_mod_to_equations. lia.
Qed.

Ltac carry_fix r0c r1 nr0c ltc eqx neMask :=
  match goal with |- context [Z_to_bv 64 (Z.b2z (Z.land (r0c + r1) 18446744073709551615 <? r0c))] =>
    replace (Z_to_bv 64 (Z.b2z (Z.land (r0c + r1) 18446744073709551615 <? r0c))) with (Z_to_bv 64 (Z.land neMask ltc))
      by (f_equal; subst neMask eqx ltc nr0c; symmetry; apply carry_gcc; assumption)
  end.

