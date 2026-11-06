(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Lib Require Import SFModel.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.FA Require Export SF_buildtac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Local Ltac step ::= step_fast.
Local Ltac zsimp ::= zsimp_fast.

(* [comment removed for export] *)
Ltac sf_vocab :=
  cbv beta delta [add64 sub64 mul64 shl64 not64 ltu64 eqz64 nez64 zext32 sext32 srliw mulhu
         is_neg64 sra63 lt_s64 lo64 hi64 wrap64
         ONES64 M32 SIGN64 MASK48 MASKLO ABS_HI INF_HI QUIET_HI QNAN_HI IMPLICIT_HI];
  rewrite ?b2z_Zb2z.

(* [comment removed for export] *)
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

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

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

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)