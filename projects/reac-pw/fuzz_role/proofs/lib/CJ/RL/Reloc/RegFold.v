(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.CJ.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache.

Ltac mkR_get_k R k :=
  lazymatch R with
  | mkR ?x1 ?x2 ?x3 ?x4 ?x5 ?x6 ?x7 ?x8 ?x9 ?x10 ?x11 ?x12 ?x13 ?x14 ?x15 ?x16 ?x17 ?x18 ?x19 ?x20 ?x21 ?x22 ?x23 ?x24 ?x25 ?x26 ?x27 ?x28 ?x29 ?x30 ?x31 =>
    lazymatch k with
    | 1%Z => x1
    | 2%Z => x2
    | 3%Z => x3
    | 4%Z => x4
    | 5%Z => x5
    | 6%Z => x6
    | 7%Z => x7
    | 8%Z => x8
    | 9%Z => x9
    | 10%Z => x10
    | 11%Z => x11
    | 12%Z => x12
    | 13%Z => x13
    | 14%Z => x14
    | 15%Z => x15
    | 16%Z => x16
    | 17%Z => x17
    | 18%Z => x18
    | 19%Z => x19
    | 20%Z => x20
    | 21%Z => x21
    | 22%Z => x22
    | 23%Z => x23
    | 24%Z => x24
    | 25%Z => x25
    | 26%Z => x26
    | 27%Z => x27
    | 28%Z => x28
    | 29%Z => x29
    | 30%Z => x30
    | 31%Z => x31
    end
  end.

Ltac mkR_set_k R k v :=
  lazymatch R with
  | mkR ?x1 ?x2 ?x3 ?x4 ?x5 ?x6 ?x7 ?x8 ?x9 ?x10 ?x11 ?x12 ?x13 ?x14 ?x15 ?x16 ?x17 ?x18 ?x19 ?x20 ?x21 ?x22 ?x23 ?x24 ?x25 ?x26 ?x27 ?x28 ?x29 ?x30 ?x31 =>
    lazymatch k with
    | 1%Z => constr:(mkR v x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
    | 2%Z => constr:(mkR x1 v x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
    | 3%Z => constr:(mkR x1 x2 v x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
    | 4%Z => constr:(mkR x1 x2 x3 v x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
    | 5%Z => constr:(mkR x1 x2 x3 x4 v x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
    | 6%Z => constr:(mkR x1 x2 x3 x4 x5 v x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
    | 7%Z => constr:(mkR x1 x2 x3 x4 x5 x6 v x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
    | 8%Z => constr:(mkR x1 x2 x3 x4 x5 x6 x7 v x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
    | 9%Z => constr:(mkR x1 x2 x3 x4 x5 x6 x7 x8 v x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
    | 10%Z => constr:(mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 v x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
    | 11%Z => constr:(mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 v x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
    | 12%Z => constr:(mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 v x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
    | 13%Z => constr:(mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 v x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
    | 14%Z => constr:(mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 v x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
    | 15%Z => constr:(mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 v x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
    | 16%Z => constr:(mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 v x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
    | 17%Z => constr:(mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 v x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
    | 18%Z => constr:(mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 v x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
    | 19%Z => constr:(mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 v x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
    | 20%Z => constr:(mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 v x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
    | 21%Z => constr:(mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 v x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
    | 22%Z => constr:(mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 v x23 x24 x25 x26 x27 x28 x29 x30 x31)
    | 23%Z => constr:(mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 v x24 x25 x26 x27 x28 x29 x30 x31)
    | 24%Z => constr:(mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 v x25 x26 x27 x28 x29 x30 x31)
    | 25%Z => constr:(mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 v x26 x27 x28 x29 x30 x31)
    | 26%Z => constr:(mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 v x27 x28 x29 x30 x31)
    | 27%Z => constr:(mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 v x28 x29 x30 x31)
    | 28%Z => constr:(mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 v x29 x30 x31)
    | 29%Z => constr:(mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 v x30 x31)
    | 30%Z => constr:(mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 v x31)
    | 31%Z => constr:(mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 v)
    end
  end.

Ltac simp_regs_folded :=
  repeat match goal with
  | |- context [reg_get ?R ?r] =>
      let k := eval vm_compute in (bv_unsigned r) in
      let x := mkR_get_k R k in
      change (reg_get R r) with x
  | |- context [@bvmap_set 5 word ?r ?v ?R] =>
      let k := eval vm_compute in (bv_unsigned r) in
      let R' := mkR_set_k R k v in
      change (@bvmap_set 5 word r v R) with R'
  end.

(* [comment removed for export] *)
Ltac simp_regs_f :=
  simp_regs_folded;
  repeat match goal with
  | |- context [reg_get ?R ?r] =>
      is_concrete_map R;
      let p := eval vm_compute in (bv_key r) in
      change (reg_get R r) with (match tget p R with Some v => v | None => w0 end);
      map_cbv_get
  | |- context [@bvmap_set 5 word ?r ?v ?R] =>
      is_concrete_map R;
      let p := eval vm_compute in (bv_key r) in
      change (@bvmap_set 5 word r v R) with (tset p v R);
      map_cbv_set
  | |- context [reg_get (@bvmap_set 5 word ?k ?v ?R) ?r] =>
      first [ rewrite (freg_get_same R k r v) by reflexivity
            | rewrite (freg_get_other R k r v) by reflexivity ]
  end;
  norm_fchain.

(* [comment removed for export] *)
Ltac simp_regs_folded_b :=
  repeat match goal with
  | |- context [reg_get ?R ?r] =>
      let k := eval vm_compute in (bv_unsigned r) in
      let x := mkR_get_k R k in
      change (reg_get R r) with x; cbv beta iota
  | |- context [@bvmap_set 5 word ?r ?v ?R] =>
      let k := eval vm_compute in (bv_unsigned r) in
      let R' := mkR_set_k R k v in
      change (@bvmap_set 5 word r v R) with R'; cbv beta iota
  end.
Ltac simp_regs_fb :=
  simp_regs_folded_b;
  repeat match goal with
  | |- context [reg_get ?R ?r] =>
      is_concrete_map R;
      let p := eval vm_compute in (bv_key r) in
      change (reg_get R r) with (match tget p R with Some v => v | None => w0 end);
      map_cbv_get
  | |- context [@bvmap_set 5 word ?r ?v ?R] =>
      is_concrete_map R;
      let p := eval vm_compute in (bv_key r) in
      change (@bvmap_set 5 word r v R) with (tset p v R);
      map_cbv_set
  | |- context [reg_get (@bvmap_set 5 word ?k ?v ?R) ?r] =>
      first [ rewrite (freg_get_same R k r v) by reflexivity
            | rewrite (freg_get_other R k r v) by reflexivity ]
  end;
  norm_fchain.

(* [comment removed for export] *)
Goal forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 v : word,
  reg_get (@bvmap_set 5 word (Z_to_bv 5 10) v
             (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31))
          (Z_to_bv 5 10) = v.
Proof.
  intros. simp_regs_f.
  lazymatch goal with |- ?a = ?b => constr_eq a b end. reflexivity.
Qed.
