(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import Sf_lib.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import F_sf_helpers F_sf_helpers2 F_f128_mul_core1 F_f128_mul.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Ltac flia ::= flia_fast.
Local Ltac unfold_sf_in H ::= unfold_sf_in_recast H.
Local Ltac blia ::= blia_fast.

Local Ltac step ::= step_fast.
Local Ltac zsimp ::= zsimp_fast.

Section Model.
  Variables a_lo a_hi b_lo b_hi : Z.
  Let aExp := shr64 (shl64 a_hi 1) 49.
  Let bExp := shr64 (shl64 b_hi 1) 49.
  Let signHi := shl64 (shr64 (Z.lxor b_hi a_hi) 63) 63.
  Let aSigHi := Z.land a_hi MASK48.
  Let bSigHi := Z.land b_hi MASK48.
  Let aAbsHi := Z.land a_hi ABS_HI.
  Let bAbsHi := Z.land b_hi ABS_HI.

  Definition FM_p2b (aSigHi1 aSigLo1 scale1 : Z) : Z :=
    let '(bSigHi1, bSigLo1, scale2) :=
      if shr64 bAbsHi 48 =? 0 then
        let '(nbHi, nbLo, nbClz) := norm_denormal bSigHi b_lo in
        (nbHi, nbLo, scale1 - nbClz + 16)
      else (bSigHi, b_lo, scale1) in
    mul_core signHi aExp bExp aSigHi1 aSigLo1 bSigHi1 bSigLo1 scale2.

  Definition FM_p2 : Z :=
    let '(aSigHi1, aSigLo1, scale1) :=
      if shr64 aAbsHi 48 =? 0 then
        let '(naHi, naLo, naClz) := norm_denormal aSigHi a_lo in
        (naHi, naLo, 16 - naClz)
      else (aSigHi, a_lo, 0) in
    FM_p2b aSigHi1 aSigLo1 scale1.

  Definition FM_inf : Z :=
    if Z.lor (Z.lxor aAbsHi INF_HI) a_lo =? 0 then
      (if negb (Z.lor b_lo bAbsHi =? 0) then mk128 (Z.lor signHi INF_HI) 0 else mk128 QNAN_HI 0)
    else if Z.lor (Z.lxor bAbsHi INF_HI) b_lo =? 0 then
      (if negb (Z.lor a_lo aAbsHi =? 0) then mk128 (Z.lor signHi INF_HI) 0 else mk128 QNAN_HI 0)
    else if Z.lor a_lo aAbsHi =? 0 then mk128 signHi 0
    else if Z.lor b_lo bAbsHi =? 0 then mk128 signHi 0
    else FM_p2.

  Definition FM_b : Z :=
    let bIsNaN := if bAbsHi =? INF_HI then negb (b_lo =? 0) else negb (bAbsHi <? INF_HI) in
    if bIsNaN then mk128 (Z.lor b_hi QUIET_HI) b_lo else FM_inf.

  Definition FM_a : Z :=
    let aIsNaN := if aAbsHi =? INF_HI then negb (a_lo =? 0) else negb (aAbsHi <? INF_HI) in
    if aIsNaN then mk128 (Z.lor a_hi QUIET_HI) a_lo else FM_b.
  Definition f128_mul_w : Z :=
    let aExpM := add64 aExp 0xffffffffffff8001 in
    let bExpM := add64 bExp 0xffffffffffff8001 in
    if negb (orb (aExpM <? 0xffffffffffff8002) (bExpM <=? 0xffffffffffff8001))
    then mul_core signHi aExp bExp aSigHi a_lo bSigHi b_lo 0
    else FM_a.
End Model.

Lemma f128_mul_words : forall a_lo a_hi b_lo b_hi,
  0 <= a_lo < 2^64 -> 0 <= a_hi < 2^64 -> 0 <= b_lo < 2^64 -> 0 <= b_hi < 2^64 ->
  f128_mul (mk128 a_hi a_lo) (mk128 b_hi b_lo) = f128_mul_w a_lo a_hi b_lo b_hi.
Proof. intros. unfold f128_mul. rewrite !lo64_mk128, !hi64_mk128 by lia. reflexivity. Qed.

Lemma sgn_eq : forall x y, 0 <= x < 2^64 -> 0 <= y < 2^64 ->
  Z.land (Z.shiftl (Z.shiftr (Z.lxor y x) 63) 63) 18446744073709551615 = Z.land (Z.lxor x y) 9223372036854775808.
Proof.
  intros x y Hx Hy. rewrite (Z.lxor_comm y x).
  apply Z.bits_inj'. intros i Hi.
  rewrite !Z.land_spec.
  change 9223372036854775808 with (2^63). rewrite Z.pow2_bits_eqb by lia.
  change 18446744073709551615 with (Z.ones 64).
  destruct (Z.lt_ge_cases i 63).
  - rewrite Z.shiftl_spec_low by lia. rewrite (proj2 (Z.eqb_neq 63 i)) by lia.
    rewrite andb_false_r. reflexivity.
  - rewrite Z.shiftl_spec_high, Z.shiftr_spec by lia. replace (i - 63 + 63) with i by lia.
    destruct (Z.eq_dec i 63) as [->|].
    + rewrite Z.ones_spec_low by lia. reflexivity.
    + rewrite (proj2 (Z.eqb_neq 63 i)) by lia. rewrite andb_false_r.
      rewrite Z.ones_spec_high by lia. apply andb_false_r.
Qed.

Lemma lxor_b2z_1 : forall b, Z.lxor (Z.b2z b) 1 = Z.b2z (negb b).
Proof. intros [|]; reflexivity. Qed.

Lemma nd_hi_range : forall h l, 0 <= l < 2^64 -> 0 <= nd_hi h l < 2^64.
Proof.
  intros h l Hl. unfold nd_hi, norm_denormal, shl128_mirror.
  destruct (is_neg64 _).
  - apply Z_lor_range. apply SoftFloat.wrap64_range. apply (zr_shiftr (Z.shiftr l 1)); [apply (zr_shiftr l 1); [exact Hl|lia] | apply Z.land_nonneg; right; lia].
  - apply SoftFloat.wrap64_range.
Qed.
Lemma nd_lo_range : forall h l, 0 <= nd_lo h l < 2^64.
Proof.
  intros h l. unfold nd_lo, norm_denormal, shl128_mirror.
  apply (zr_land_r _ _). { unfold sra63, ONES64. destruct (is_neg64 _); lia. } apply SoftFloat.wrap64_range.
Qed.

Section Walk.
  Variables (sp a0 a1 a2 a3 : word).
  Notation a_lo := (bv_unsigned a0). Notation a_hi := (bv_unsigned a1).
  Notation b_lo := (bv_unsigned a2). Notation b_hi := (bv_unsigned a3).
  Notation spw := (Z_to_bv 64 (bv_unsigned sp + -112)).

  Notation E_sgn := (Z.land (Z.lxor a_hi b_hi) 9223372036854775808).
  Notation E_aExp := (Z.shiftr (Z.land (Z.shiftl a_hi 1) 18446744073709551615) 49).
  Notation E_bExp := (Z.shiftr (Z.land (Z.shiftl b_hi 1) 18446744073709551615) 49).
  Notation E_aSig := (Z.land a_hi 281474976710655).
  Notation E_bSig := (Z.land b_hi 281474976710655).
  Notation E_aAbs := (Z.land a_hi 9223372036854775807).
  Notation E_bAbs := (Z.land b_hi 9223372036854775807).

  Definition saved (s5 s4 s3 s2 s1 s0 ra : word) (j : list byte) : list cell :=
    [CB 8 j; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  Ltac hyp :=
    match goal with
    | H : mem_inv _ ?m |- mem_inv _ ?m => exact H
    | H : munch ?W ?m ?m' |- munch ?W ?m ?m' => exact H
    | H : wmono _ ?m ?m' |- wmono _ ?m ?m' => exact H
    | H : stk _ ?m ?lo ?hi |- stk _ ?m ?lo ?hi => exact H
    | H : rw_cells _ ?m ?A _ |- rw_cells _ ?m ?A _ => exact H
    | H : (?a <= ?b)%Z |- (?a <= ?b)%Z => exact H
    | H : bv_unsigned ?w = _ |- bv_unsigned ?w = _ => exact H
    end.
  Ltac join L := eapply L; try hyp.

  Ltac forget_cells H := apply rw_cells_forget in H; destruct H as [? H]; cbn [cells_size csize Nat.add] in H.

  Ltac eblia := rewrite ?Z.shiftl_mul_pow2 in * by lia; blia.
  Ltac decide_in_cond H c :=
    match c with
    | context [Z.eqb ?x ?y] =>
        first [ rewrite (proj2 (Z.eqb_eq x y)) in H by (clear H; eblia) | rewrite (proj2 (Z.eqb_neq x y)) in H by (clear H; eblia) ]
    | context [Z.ltb ?x ?y] =>
        first [ rewrite (proj2 (Z.ltb_lt x y)) in H by (clear H; eblia) | rewrite (proj2 (Z.ltb_ge x y)) in H by (clear H; eblia) ]
    | context [Z.leb ?x ?y] =>
        first [ rewrite (proj2 (Z.leb_le x y)) in H by (clear H; eblia) | rewrite (proj2 (Z.leb_gt x y)) in H by (clear H; eblia) ]
    end.

  Ltac decide_head H :=
    cbn_bool_in H;
    lazymatch type of H with
    | _ = ?t => match t with context [if ?c then _ else _] => decide_in_cond H c end
    end;
    cbn_bool_in H.

End Walk.

