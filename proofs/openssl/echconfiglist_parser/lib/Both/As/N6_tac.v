(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes ZBridge.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)

(* [comment removed for export] *)
Ltac nonneg_lit d := lazymatch (eval vm_compute in (andb (Z.leb 0 d) (Z.leb d 4096))) with true => d end.

Ltac addr_diff E A ::=
  lazymatch E with
  | Z.add ?X ?c1 =>
      lazymatch A with
      | Z.add X ?c2 => let c1 := zlit c1 in let c2 := zlit c2 in let d := eval vm_compute in (c1 - c2)%Z in nonneg_lit d
      | X => let c1 := zlit c1 in nonneg_lit c1
      | _ => let e := zlit E in let a := zlit A in let d := eval vm_compute in (e - a)%Z in nonneg_lit d
      end
  | _ =>
      lazymatch A with
      | Z.add E ?c2 => let c2 := zlit c2 in let d := eval vm_compute in (- c2)%Z in nonneg_lit d
      | E => constr:(0%Z)
      | _ => let e := zlit E in let a := zlit A in let d := eval vm_compute in (e - a)%Z in nonneg_lit d
      end
  end.

(* [comment removed for export] *)
Lemma land_m8 : forall y, 0 <= y < 2^64 -> Z.land y 18446744073709551608 = 8 * (y / 8).
Proof.
  intros y Hy. transitivity (Z.ldiff (Z.land y (Z.ones 64)) (Z.ones 3)).
  - rewrite Z.ldiff_land. rewrite <- Z.land_assoc. f_equal.
  - rewrite Z.land_ones, Z.mod_small by lia. rewrite Z.ldiff_ones_r by lia.
    rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. change (2^3) with 8. lia.
Qed.

(* [comment removed for export] *)
Lemma land_7 : forall y, Z.land y 7 = y mod 8.
Proof. intros. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity. Qed.

(* [comment removed for export] *)
Lemma land_ones64 : forall x, Z.land x 18446744073709551615 = x mod 2^64.
Proof. intros x. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma lxor_ones64 : forall x, 0 <= x < 2^64 -> Z.lxor x 18446744073709551615 = 18446744073709551615 - x.
Proof.
  intros x Hx. destruct (Z.eq_dec x 0) as [->|NZ]; [reflexivity|].
  change 18446744073709551615 with (Z.ones 64).
  rewrite <- Z.ldiff_ones_l_low; [| lia | apply Z.log2_lt_pow2; lia].
  rewrite <- Z.sub_nocarry_ldiff.
  - unfold Z.ones. rewrite Z.shiftl_1_l. reflexivity.
  - rewrite Z.ldiff_ones_r_low; [reflexivity | lia | apply Z.log2_lt_pow2; lia].
Qed.
