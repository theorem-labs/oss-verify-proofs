(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import Sf_lib.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Export SF_buildtac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Definition mul_core_mid_pc := 0x11a6c%Z.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Ltac flia ::= flia_fast.

Local Ltac step ::= step_fast.
Local Ltac zsimp ::= zsimp_fast.

Ltac model_reg_tac n X mexpr ::=
  let w := getreg n in
  lazymatch w with
  | Z_to_bv 64 ?e =>
      first [ constr_eq e mexpr
            | replace (Z_to_bv 64 e) with (Z_to_bv 64 mexpr)
                by (first [ zeq_special e mexpr
                          | f_equal; zeq_fast
                          | rewrite Z_to_bv_land64; f_equal; zeq_fast
                          | apply Z_to_bv_eqm; rewrite ?Z.mod_mod by lia; zeq_fast
                          | idtac "note: model_reg" X ": slow path for" e; fail
                          | f_equal; zeq
                          | apply Z_to_bv_eqm; slim; zb_masks; pose_word_ranges; Z.div_mod_to_equations; lia
                          | apply Z_to_bv_eqm; zb_masks; pose_word_ranges; Z.div_mod_to_equations; lia ]) ];
      name_as_tac X mexpr
  | _ => fail "model_reg: register" n "holds" w
  end.

Ltac sf_vocab :=
  cbv beta delta [add64 sub64 mul64 shl64 not64 ltu64 eqz64 nez64 zext32 sext32 srliw mulhu
         is_neg64 sra63 lt_s64 lo64 hi64 wrap64
         ONES64 M32 SIGN64 MASK48 MASKLO ABS_HI INF_HI QUIET_HI QNAN_HI IMPLICIT_HI];
  rewrite ?b2z_Zb2z.

Ltac fold_head_let :=
  lazymatch goal with
  | |- (let x := ?b in ?c) = ?r =>
      match goal with
      | H := ?b' : Z |- _ =>
          constr_eq b b';
          let c' := eval cbv beta in ((fun x : Z => c) H) in
          change ((let x := b in c) = r) with (c' = r)
      end
  end.
Ltac fold_model_lets := repeat fold_head_let.

Definition MC_tail (signHi expSum hi_hi hi_lo lo_hi lo_lo scale : Z) : Z :=
  let scaleAdj := scale - 0x3fff in
  let productExponent := expSum + scaleAdj in
  if is_neg64 (shl64 hi_hi 15) then
    let productExponent1 := productExponent + 1 in
    if negb (productExponent1 <? 0x7fff) then mk128 (Z.lor signHi INF_HI) 0
    else mul_finish signHi productExponent1 hi_hi hi_lo lo_hi lo_lo
  else
    let hi_hi1 := Z.lor (shl64 hi_hi 1) (shr64 hi_lo 63) in
    let hi_lo1 := Z.lor (shl64 hi_lo 1) (shr64 lo_hi 63) in
    let lo_hi1 := Z.lor (shl64 lo_hi 1) (shr64 lo_lo 63) in
    let lo_lo1 := shl64 lo_lo 1 in
    if 0x7fff <=? productExponent then mk128 (Z.lor signHi INF_HI) 0
    else mul_finish signHi productExponent hi_hi1 hi_lo1 lo_hi1 lo_lo1.

