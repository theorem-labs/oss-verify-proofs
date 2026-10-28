(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import Sf_lib.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import F_sf_helpers F_sf_helpers2 F_f128_mul_core1 F_f128_mul F_f128_mul_top F_sf_helpers3 F_f128_div_wide F_f128_div_core1 F_f128_div_core2.
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

  Definition FD_p2b (aSigHi1 aLo1 scale1 : Z) : Z :=
    let '(bSigHi1, bLo1, scale2) :=
      if shr64 bAbsHi 48 =? 0 then
        let '(nhi, nlo, nclz) := norm_denormal bSigHi b_lo in (nhi, nlo, (scale1 + nclz) - 16)
      else (bSigHi, b_lo, scale1) in
    div_core signHi aExp bExp aSigHi1 aLo1 bSigHi1 bLo1 scale2.

  Definition FD_p2 : Z :=
    let '(aSigHi1, aLo1, scale1) :=
      if shr64 aAbsHi 48 =? 0 then
        let '(nhi, nlo, nclz) := norm_denormal aSigHi a_lo in (nhi, nlo, 16 - nclz)
      else (aSigHi, a_lo, 0) in
    FD_p2b aSigHi1 aLo1 scale1.

  Definition FD_inf : Z :=
    if Z.lor (Z.lxor aAbsHi INF_HI) a_lo =? 0 then
      (if negb (Z.lor b_lo (Z.lxor bAbsHi INF_HI) =? 0) then mk128 (Z.lor signHi INF_HI) 0 else mk128 QNAN_HI 0)
    else if Z.lor b_lo (Z.lxor bAbsHi INF_HI) =? 0 then mk128 signHi 0
    else if Z.lor a_lo aAbsHi =? 0 then
      (if negb (Z.lor b_lo bAbsHi =? 0) then mk128 signHi 0 else mk128 QNAN_HI 0)
    else if Z.lor b_lo bAbsHi =? 0 then mk128 (Z.lor signHi INF_HI) 0
    else FD_p2.

  Definition FD_b : Z :=
    let bIsNaN := if bAbsHi =? INF_HI then negb (b_lo =? 0) else negb (bAbsHi <? INF_HI) in
    if bIsNaN then mk128 (Z.lor b_hi QUIET_HI) b_lo else FD_inf.

  Definition FD_a : Z :=
    let aIsNaN := if aAbsHi =? INF_HI then negb (a_lo =? 0) else negb (aAbsHi <? INF_HI) in
    if aIsNaN then mk128 (Z.lor a_hi QUIET_HI) a_lo else FD_b.

  Definition FD_0b : Z :=
    let bExpM := add64 bExp 0xffffffffffff8001 in
    if bExpM <=? 0xffffffffffff8001 then FD_a
    else div_core signHi aExp bExp aSigHi a_lo bSigHi b_lo 0.
  Definition f128_div_w : Z :=
    let aExpM := add64 aExp 0xffffffffffff8001 in
    if aExpM <? 0xffffffffffff8002 then FD_a else FD_0b.
End Model.

Lemma f128_div_words : forall a_lo a_hi b_lo b_hi,
  0 <= a_lo < 2^64 -> 0 <= a_hi < 2^64 -> 0 <= b_lo < 2^64 -> 0 <= b_hi < 2^64 ->
  f128_div (mk128 a_hi a_lo) (mk128 b_hi b_lo) = f128_div_w a_lo a_hi b_lo b_hi.
Proof.
  intros. unfold f128_div, f128_div_w, FD_0b. rewrite !lo64_mk128, !hi64_mk128 by lia. cbv zeta.
  destruct (_ <? _); destruct (_ <=? _); reflexivity.
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

  Definition savedD (s6 s5 s4 s3 s2 s1 s0 ra : word) : list cell :=
    [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

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

  Ltac exact_HR :=
    lazymatch goal with |- ?g =>
      match goal with
      | HR : ?t |- _ => constr_eq t g; exact HR
      | HR : @eq Z ?r ?t |- _ => fail 0 "exact_HR: goal" g "but HR:" r "=" t
      end
    end.
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

