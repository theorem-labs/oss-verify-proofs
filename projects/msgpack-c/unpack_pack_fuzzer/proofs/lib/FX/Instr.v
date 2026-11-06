(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 Val IMap.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import W64 Val.
Open Scope Z_scope.

Module FI.

Inductive r5 : Type := X0 | X1 | X2 | X3 | X4 | X5 | X6 | X7 | X8 | X9 | X10 | X11 | X12 | X13 | X14 | X15 | X16 | X17 | X18 | X19 | X20 | X21 | X22 | X23 | X24 | X25 | X26 | X27 | X28 | X29 | X30 | X31.

Definition r5_of_Z (z : Z) : option r5 :=
  match z with
  | 0 => Some X0
  | 1 => Some X1
  | 2 => Some X2
  | 3 => Some X3
  | 4 => Some X4
  | 5 => Some X5
  | 6 => Some X6
  | 7 => Some X7
  | 8 => Some X8
  | 9 => Some X9
  | 10 => Some X10
  | 11 => Some X11
  | 12 => Some X12
  | 13 => Some X13
  | 14 => Some X14
  | 15 => Some X15
  | 16 => Some X16
  | 17 => Some X17
  | 18 => Some X18
  | 19 => Some X19
  | 20 => Some X20
  | 21 => Some X21
  | 22 => Some X22
  | 23 => Some X23
  | 24 => Some X24
  | 25 => Some X25
  | 26 => Some X26
  | 27 => Some X27
  | 28 => Some X28
  | 29 => Some X29
  | 30 => Some X30
  | 31 => Some X31
  | _ => None
  end%Z.
Definition r5_to_Z (r : r5) : Z :=
  match r with X0 => 0 | X1 => 1 | X2 => 2 | X3 => 3 | X4 => 4 | X5 => 5 | X6 => 6 | X7 => 7 | X8 => 8 | X9 => 9 | X10 => 10 | X11 => 11 | X12 => 12 | X13 => 13 | X14 => 14 | X15 => 15 | X16 => 16 | X17 => 17 | X18 => 18 | X19 => 19 | X20 => 20 | X21 => 21 | X22 => 22 | X23 => 23 | X24 => 24 | X25 => 25 | X26 => 26 | X27 => 27 | X28 => 28 | X29 => 29 | X30 => 30 | X31 => 31 end%Z.
Definition r5_of_reg (r : reg) : option r5 := r5_of_Z (bv_unsigned r).
Definition r5_eqb (a b : r5) : bool := Z.eqb (r5_to_Z a) (r5_to_Z b).

Record rf (A : Type) : Type := RF { f0 : A; f1 : A; f2 : A; f3 : A; f4 : A; f5 : A; f6 : A; f7 : A; f8 : A; f9 : A; f10 : A; f11 : A; f12 : A; f13 : A; f14 : A; f15 : A; f16 : A; f17 : A; f18 : A; f19 : A; f20 : A; f21 : A; f22 : A; f23 : A; f24 : A; f25 : A; f26 : A; f27 : A; f28 : A; f29 : A; f30 : A; f31 : A }.
Arguments RF {A}. Arguments f0 {A}. Arguments f1 {A}. Arguments f2 {A}. Arguments f3 {A}. Arguments f4 {A}. Arguments f5 {A}. Arguments f6 {A}. Arguments f7 {A}. Arguments f8 {A}. Arguments f9 {A}. Arguments f10 {A}. Arguments f11 {A}. Arguments f12 {A}. Arguments f13 {A}. Arguments f14 {A}. Arguments f15 {A}. Arguments f16 {A}. Arguments f17 {A}. Arguments f18 {A}. Arguments f19 {A}. Arguments f20 {A}. Arguments f21 {A}. Arguments f22 {A}. Arguments f23 {A}. Arguments f24 {A}. Arguments f25 {A}. Arguments f26 {A}. Arguments f27 {A}. Arguments f28 {A}. Arguments f29 {A}. Arguments f30 {A}. Arguments f31 {A}.
Definition rf_get {A} (x : rf A) (r : r5) : A :=
  match r with X0 => f0 x | X1 => f1 x | X2 => f2 x | X3 => f3 x | X4 => f4 x | X5 => f5 x | X6 => f6 x | X7 => f7 x | X8 => f8 x | X9 => f9 x | X10 => f10 x | X11 => f11 x | X12 => f12 x | X13 => f13 x | X14 => f14 x | X15 => f15 x | X16 => f16 x | X17 => f17 x | X18 => f18 x | X19 => f19 x | X20 => f20 x | X21 => f21 x | X22 => f22 x | X23 => f23 x | X24 => f24 x | X25 => f25 x | X26 => f26 x | X27 => f27 x | X28 => f28 x | X29 => f29 x | X30 => f30 x | X31 => f31 x end.
Definition rf_set {A} (x : rf A) (r : r5) (v : A) : rf A :=
  match r with
  | X0 => RF v (f1 x) (f2 x) (f3 x) (f4 x) (f5 x) (f6 x) (f7 x) (f8 x) (f9 x) (f10 x) (f11 x) (f12 x) (f13 x) (f14 x) (f15 x) (f16 x) (f17 x) (f18 x) (f19 x) (f20 x) (f21 x) (f22 x) (f23 x) (f24 x) (f25 x) (f26 x) (f27 x) (f28 x) (f29 x) (f30 x) (f31 x)
  | X1 => RF (f0 x) v (f2 x) (f3 x) (f4 x) (f5 x) (f6 x) (f7 x) (f8 x) (f9 x) (f10 x) (f11 x) (f12 x) (f13 x) (f14 x) (f15 x) (f16 x) (f17 x) (f18 x) (f19 x) (f20 x) (f21 x) (f22 x) (f23 x) (f24 x) (f25 x) (f26 x) (f27 x) (f28 x) (f29 x) (f30 x) (f31 x)
  | X2 => RF (f0 x) (f1 x) v (f3 x) (f4 x) (f5 x) (f6 x) (f7 x) (f8 x) (f9 x) (f10 x) (f11 x) (f12 x) (f13 x) (f14 x) (f15 x) (f16 x) (f17 x) (f18 x) (f19 x) (f20 x) (f21 x) (f22 x) (f23 x) (f24 x) (f25 x) (f26 x) (f27 x) (f28 x) (f29 x) (f30 x) (f31 x)
  | X3 => RF (f0 x) (f1 x) (f2 x) v (f4 x) (f5 x) (f6 x) (f7 x) (f8 x) (f9 x) (f10 x) (f11 x) (f12 x) (f13 x) (f14 x) (f15 x) (f16 x) (f17 x) (f18 x) (f19 x) (f20 x) (f21 x) (f22 x) (f23 x) (f24 x) (f25 x) (f26 x) (f27 x) (f28 x) (f29 x) (f30 x) (f31 x)
  | X4 => RF (f0 x) (f1 x) (f2 x) (f3 x) v (f5 x) (f6 x) (f7 x) (f8 x) (f9 x) (f10 x) (f11 x) (f12 x) (f13 x) (f14 x) (f15 x) (f16 x) (f17 x) (f18 x) (f19 x) (f20 x) (f21 x) (f22 x) (f23 x) (f24 x) (f25 x) (f26 x) (f27 x) (f28 x) (f29 x) (f30 x) (f31 x)
  | X5 => RF (f0 x) (f1 x) (f2 x) (f3 x) (f4 x) v (f6 x) (f7 x) (f8 x) (f9 x) (f10 x) (f11 x) (f12 x) (f13 x) (f14 x) (f15 x) (f16 x) (f17 x) (f18 x) (f19 x) (f20 x) (f21 x) (f22 x) (f23 x) (f24 x) (f25 x) (f26 x) (f27 x) (f28 x) (f29 x) (f30 x) (f31 x)
  | X6 => RF (f0 x) (f1 x) (f2 x) (f3 x) (f4 x) (f5 x) v (f7 x) (f8 x) (f9 x) (f10 x) (f11 x) (f12 x) (f13 x) (f14 x) (f15 x) (f16 x) (f17 x) (f18 x) (f19 x) (f20 x) (f21 x) (f22 x) (f23 x) (f24 x) (f25 x) (f26 x) (f27 x) (f28 x) (f29 x) (f30 x) (f31 x)
  | X7 => RF (f0 x) (f1 x) (f2 x) (f3 x) (f4 x) (f5 x) (f6 x) v (f8 x) (f9 x) (f10 x) (f11 x) (f12 x) (f13 x) (f14 x) (f15 x) (f16 x) (f17 x) (f18 x) (f19 x) (f20 x) (f21 x) (f22 x) (f23 x) (f24 x) (f25 x) (f26 x) (f27 x) (f28 x) (f29 x) (f30 x) (f31 x)
  | X8 => RF (f0 x) (f1 x) (f2 x) (f3 x) (f4 x) (f5 x) (f6 x) (f7 x) v (f9 x) (f10 x) (f11 x) (f12 x) (f13 x) (f14 x) (f15 x) (f16 x) (f17 x) (f18 x) (f19 x) (f20 x) (f21 x) (f22 x) (f23 x) (f24 x) (f25 x) (f26 x) (f27 x) (f28 x) (f29 x) (f30 x) (f31 x)
  | X9 => RF (f0 x) (f1 x) (f2 x) (f3 x) (f4 x) (f5 x) (f6 x) (f7 x) (f8 x) v (f10 x) (f11 x) (f12 x) (f13 x) (f14 x) (f15 x) (f16 x) (f17 x) (f18 x) (f19 x) (f20 x) (f21 x) (f22 x) (f23 x) (f24 x) (f25 x) (f26 x) (f27 x) (f28 x) (f29 x) (f30 x) (f31 x)
  | X10 => RF (f0 x) (f1 x) (f2 x) (f3 x) (f4 x) (f5 x) (f6 x) (f7 x) (f8 x) (f9 x) v (f11 x) (f12 x) (f13 x) (f14 x) (f15 x) (f16 x) (f17 x) (f18 x) (f19 x) (f20 x) (f21 x) (f22 x) (f23 x) (f24 x) (f25 x) (f26 x) (f27 x) (f28 x) (f29 x) (f30 x) (f31 x)
  | X11 => RF (f0 x) (f1 x) (f2 x) (f3 x) (f4 x) (f5 x) (f6 x) (f7 x) (f8 x) (f9 x) (f10 x) v (f12 x) (f13 x) (f14 x) (f15 x) (f16 x) (f17 x) (f18 x) (f19 x) (f20 x) (f21 x) (f22 x) (f23 x) (f24 x) (f25 x) (f26 x) (f27 x) (f28 x) (f29 x) (f30 x) (f31 x)
  | X12 => RF (f0 x) (f1 x) (f2 x) (f3 x) (f4 x) (f5 x) (f6 x) (f7 x) (f8 x) (f9 x) (f10 x) (f11 x) v (f13 x) (f14 x) (f15 x) (f16 x) (f17 x) (f18 x) (f19 x) (f20 x) (f21 x) (f22 x) (f23 x) (f24 x) (f25 x) (f26 x) (f27 x) (f28 x) (f29 x) (f30 x) (f31 x)
  | X13 => RF (f0 x) (f1 x) (f2 x) (f3 x) (f4 x) (f5 x) (f6 x) (f7 x) (f8 x) (f9 x) (f10 x) (f11 x) (f12 x) v (f14 x) (f15 x) (f16 x) (f17 x) (f18 x) (f19 x) (f20 x) (f21 x) (f22 x) (f23 x) (f24 x) (f25 x) (f26 x) (f27 x) (f28 x) (f29 x) (f30 x) (f31 x)
  | X14 => RF (f0 x) (f1 x) (f2 x) (f3 x) (f4 x) (f5 x) (f6 x) (f7 x) (f8 x) (f9 x) (f10 x) (f11 x) (f12 x) (f13 x) v (f15 x) (f16 x) (f17 x) (f18 x) (f19 x) (f20 x) (f21 x) (f22 x) (f23 x) (f24 x) (f25 x) (f26 x) (f27 x) (f28 x) (f29 x) (f30 x) (f31 x)
  | X15 => RF (f0 x) (f1 x) (f2 x) (f3 x) (f4 x) (f5 x) (f6 x) (f7 x) (f8 x) (f9 x) (f10 x) (f11 x) (f12 x) (f13 x) (f14 x) v (f16 x) (f17 x) (f18 x) (f19 x) (f20 x) (f21 x) (f22 x) (f23 x) (f24 x) (f25 x) (f26 x) (f27 x) (f28 x) (f29 x) (f30 x) (f31 x)
  | X16 => RF (f0 x) (f1 x) (f2 x) (f3 x) (f4 x) (f5 x) (f6 x) (f7 x) (f8 x) (f9 x) (f10 x) (f11 x) (f12 x) (f13 x) (f14 x) (f15 x) v (f17 x) (f18 x) (f19 x) (f20 x) (f21 x) (f22 x) (f23 x) (f24 x) (f25 x) (f26 x) (f27 x) (f28 x) (f29 x) (f30 x) (f31 x)
  | X17 => RF (f0 x) (f1 x) (f2 x) (f3 x) (f4 x) (f5 x) (f6 x) (f7 x) (f8 x) (f9 x) (f10 x) (f11 x) (f12 x) (f13 x) (f14 x) (f15 x) (f16 x) v (f18 x) (f19 x) (f20 x) (f21 x) (f22 x) (f23 x) (f24 x) (f25 x) (f26 x) (f27 x) (f28 x) (f29 x) (f30 x) (f31 x)
  | X18 => RF (f0 x) (f1 x) (f2 x) (f3 x) (f4 x) (f5 x) (f6 x) (f7 x) (f8 x) (f9 x) (f10 x) (f11 x) (f12 x) (f13 x) (f14 x) (f15 x) (f16 x) (f17 x) v (f19 x) (f20 x) (f21 x) (f22 x) (f23 x) (f24 x) (f25 x) (f26 x) (f27 x) (f28 x) (f29 x) (f30 x) (f31 x)
  | X19 => RF (f0 x) (f1 x) (f2 x) (f3 x) (f4 x) (f5 x) (f6 x) (f7 x) (f8 x) (f9 x) (f10 x) (f11 x) (f12 x) (f13 x) (f14 x) (f15 x) (f16 x) (f17 x) (f18 x) v (f20 x) (f21 x) (f22 x) (f23 x) (f24 x) (f25 x) (f26 x) (f27 x) (f28 x) (f29 x) (f30 x) (f31 x)
  | X20 => RF (f0 x) (f1 x) (f2 x) (f3 x) (f4 x) (f5 x) (f6 x) (f7 x) (f8 x) (f9 x) (f10 x) (f11 x) (f12 x) (f13 x) (f14 x) (f15 x) (f16 x) (f17 x) (f18 x) (f19 x) v (f21 x) (f22 x) (f23 x) (f24 x) (f25 x) (f26 x) (f27 x) (f28 x) (f29 x) (f30 x) (f31 x)
  | X21 => RF (f0 x) (f1 x) (f2 x) (f3 x) (f4 x) (f5 x) (f6 x) (f7 x) (f8 x) (f9 x) (f10 x) (f11 x) (f12 x) (f13 x) (f14 x) (f15 x) (f16 x) (f17 x) (f18 x) (f19 x) (f20 x) v (f22 x) (f23 x) (f24 x) (f25 x) (f26 x) (f27 x) (f28 x) (f29 x) (f30 x) (f31 x)
  | X22 => RF (f0 x) (f1 x) (f2 x) (f3 x) (f4 x) (f5 x) (f6 x) (f7 x) (f8 x) (f9 x) (f10 x) (f11 x) (f12 x) (f13 x) (f14 x) (f15 x) (f16 x) (f17 x) (f18 x) (f19 x) (f20 x) (f21 x) v (f23 x) (f24 x) (f25 x) (f26 x) (f27 x) (f28 x) (f29 x) (f30 x) (f31 x)
  | X23 => RF (f0 x) (f1 x) (f2 x) (f3 x) (f4 x) (f5 x) (f6 x) (f7 x) (f8 x) (f9 x) (f10 x) (f11 x) (f12 x) (f13 x) (f14 x) (f15 x) (f16 x) (f17 x) (f18 x) (f19 x) (f20 x) (f21 x) (f22 x) v (f24 x) (f25 x) (f26 x) (f27 x) (f28 x) (f29 x) (f30 x) (f31 x)
  | X24 => RF (f0 x) (f1 x) (f2 x) (f3 x) (f4 x) (f5 x) (f6 x) (f7 x) (f8 x) (f9 x) (f10 x) (f11 x) (f12 x) (f13 x) (f14 x) (f15 x) (f16 x) (f17 x) (f18 x) (f19 x) (f20 x) (f21 x) (f22 x) (f23 x) v (f25 x) (f26 x) (f27 x) (f28 x) (f29 x) (f30 x) (f31 x)
  | X25 => RF (f0 x) (f1 x) (f2 x) (f3 x) (f4 x) (f5 x) (f6 x) (f7 x) (f8 x) (f9 x) (f10 x) (f11 x) (f12 x) (f13 x) (f14 x) (f15 x) (f16 x) (f17 x) (f18 x) (f19 x) (f20 x) (f21 x) (f22 x) (f23 x) (f24 x) v (f26 x) (f27 x) (f28 x) (f29 x) (f30 x) (f31 x)
  | X26 => RF (f0 x) (f1 x) (f2 x) (f3 x) (f4 x) (f5 x) (f6 x) (f7 x) (f8 x) (f9 x) (f10 x) (f11 x) (f12 x) (f13 x) (f14 x) (f15 x) (f16 x) (f17 x) (f18 x) (f19 x) (f20 x) (f21 x) (f22 x) (f23 x) (f24 x) (f25 x) v (f27 x) (f28 x) (f29 x) (f30 x) (f31 x)
  | X27 => RF (f0 x) (f1 x) (f2 x) (f3 x) (f4 x) (f5 x) (f6 x) (f7 x) (f8 x) (f9 x) (f10 x) (f11 x) (f12 x) (f13 x) (f14 x) (f15 x) (f16 x) (f17 x) (f18 x) (f19 x) (f20 x) (f21 x) (f22 x) (f23 x) (f24 x) (f25 x) (f26 x) v (f28 x) (f29 x) (f30 x) (f31 x)
  | X28 => RF (f0 x) (f1 x) (f2 x) (f3 x) (f4 x) (f5 x) (f6 x) (f7 x) (f8 x) (f9 x) (f10 x) (f11 x) (f12 x) (f13 x) (f14 x) (f15 x) (f16 x) (f17 x) (f18 x) (f19 x) (f20 x) (f21 x) (f22 x) (f23 x) (f24 x) (f25 x) (f26 x) (f27 x) v (f29 x) (f30 x) (f31 x)
  | X29 => RF (f0 x) (f1 x) (f2 x) (f3 x) (f4 x) (f5 x) (f6 x) (f7 x) (f8 x) (f9 x) (f10 x) (f11 x) (f12 x) (f13 x) (f14 x) (f15 x) (f16 x) (f17 x) (f18 x) (f19 x) (f20 x) (f21 x) (f22 x) (f23 x) (f24 x) (f25 x) (f26 x) (f27 x) (f28 x) v (f30 x) (f31 x)
  | X30 => RF (f0 x) (f1 x) (f2 x) (f3 x) (f4 x) (f5 x) (f6 x) (f7 x) (f8 x) (f9 x) (f10 x) (f11 x) (f12 x) (f13 x) (f14 x) (f15 x) (f16 x) (f17 x) (f18 x) (f19 x) (f20 x) (f21 x) (f22 x) (f23 x) (f24 x) (f25 x) (f26 x) (f27 x) (f28 x) (f29 x) v (f31 x)
  | X31 => RF (f0 x) (f1 x) (f2 x) (f3 x) (f4 x) (f5 x) (f6 x) (f7 x) (f8 x) (f9 x) (f10 x) (f11 x) (f12 x) (f13 x) (f14 x) (f15 x) (f16 x) (f17 x) (f18 x) (f19 x) (f20 x) (f21 x) (f22 x) (f23 x) (f24 x) (f25 x) (f26 x) (f27 x) (f28 x) (f29 x) (f30 x) v
  end.
Definition rf_init {A} (v : A) : rf A := RF v v v v v v v v v v v v v v v v v v v v v v v v v v v v v v v v.
Definition rf_map {A B} (g : A -> B) (x : rf A) : rf B := RF (g (f0 x)) (g (f1 x)) (g (f2 x)) (g (f3 x)) (g (f4 x)) (g (f5 x)) (g (f6 x)) (g (f7 x)) (g (f8 x)) (g (f9 x)) (g (f10 x)) (g (f11 x)) (g (f12 x)) (g (f13 x)) (g (f14 x)) (g (f15 x)) (g (f16 x)) (g (f17 x)) (g (f18 x)) (g (f19 x)) (g (f20 x)) (g (f21 x)) (g (f22 x)) (g (f23 x)) (g (f24 x)) (g (f25 x)) (g (f26 x)) (g (f27 x)) (g (f28 x)) (g (f29 x)) (g (f30 x)) (g (f31 x)).
Definition rf_to_list {A} (x : rf A) : list A := [f0 x; f1 x; f2 x; f3 x; f4 x; f5 x; f6 x; f7 x; f8 x; f9 x; f10 x; f11 x; f12 x; f13 x; f14 x; f15 x; f16 x; f17 x; f18 x; f19 x; f20 x; f21 x; f22 x; f23 x; f24 x; f25 x; f26 x; f27 x; f28 x; f29 x; f30 x; f31 x].
Definition rf_forallb2 {A B} (p : A -> B -> bool) (x : rf A) (y : rf B) : bool :=
  p (f0 x) (f0 y) && p (f1 x) (f1 y) && p (f2 x) (f2 y) && p (f3 x) (f3 y) && p (f4 x) (f4 y) && p (f5 x) (f5 y) && p (f6 x) (f6 y) && p (f7 x) (f7 y) && p (f8 x) (f8 y) && p (f9 x) (f9 y) && p (f10 x) (f10 y) && p (f11 x) (f11 y) && p (f12 x) (f12 y) && p (f13 x) (f13 y) && p (f14 x) (f14 y) && p (f15 x) (f15 y) && p (f16 x) (f16 y) && p (f17 x) (f17 y) && p (f18 x) (f18 y) && p (f19 x) (f19 y) && p (f20 x) (f20 y) && p (f21 x) (f21 y) && p (f22 x) (f22 y) && p (f23 x) (f23 y) && p (f24 x) (f24 y) && p (f25 x) (f25 y) && p (f26 x) (f26 y) && p (f27 x) (f27 y) && p (f28 x) (f28 y) && p (f29 x) (f29 y) && p (f30 x) (f30 y) && p (f31 x) (f31 y).

Lemma rf_get_set_same : forall A (x : rf A) r v, rf_get (rf_set x r v) r = v.
Proof. intros A x r v; destruct r; reflexivity. Qed.
Lemma rf_get_set_other : forall A (x : rf A) r r' v, r <> r' -> rf_get (rf_set x r v) r' = rf_get x r'.
Proof. intros A x r r' v H; destruct r, r'; try reflexivity; congruence. Qed.
Lemma rf_get_map : forall A B (g : A -> B) (x : rf A) r, rf_get (rf_map g x) r = g (rf_get x r).
Proof. intros; destruct r; reflexivity. Qed.
Lemma r5_of_to_Z : forall r, r5_of_Z (r5_to_Z r) = Some r.
Proof. destruct r; reflexivity. Qed.
Lemma r5_eqb_spec : forall a b, r5_eqb a b = true <-> a = b.
Proof. intros a b; unfold r5_eqb; rewrite Z.eqb_eq; split; [|intros ->; reflexivity].
  destruct a, b; cbn; intro H; try reflexivity; discriminate. Qed.

Inductive finstr : Type :=
| ILui (rd : r5) (v : w64)
| IAuipc (rd : r5) (v : w64)
| IJal (rd : r5) (off : w64)
| IJalr (rd rs1 : r5) (off : w64)
| IBranch (c : branch_cond) (rs1 rs2 : r5) (off : w64)
| ILoad (sz : msize) (sx : bool) (rd rs1 : r5) (off : w64)
| IStore (sz : msize) (rs1 rs2 : r5) (off : w64)
| IOpImm (op : aluop) (rd rs1 : r5) (v : w64)
| IOp (op : aluop) (rd rs1 rs2 : r5)
| IOpImm32 (op : aluop) (rd rs1 : r5) (v : w64)
| IOp32 (op : aluop) (rd rs1 rs2 : r5)
| IMul (op : mulop) (rd rs1 rs2 : r5)
| IMul32 (op : mulop) (rd rs1 rs2 : r5)
| IFence
| IEcall
| ILr (wd : awidth) (rd rs1 : r5)
| ISc (wd : awidth) (rd rs1 rs2 : r5)
| IAmo (op : amoop) (wd : awidth) (rd rs1 rs2 : r5)
| IFLoad (fmt : ffmt) (rd : r5) (rs1 : r5) (off : w64)
| IFStore (fmt : ffmt) (rs1 : r5) (rs2 : r5) (off : w64)
| IFmv (dir : fmvdir) (fmt : ffmt) (rd rs1 : r5)
| IFcvtDS (rd rs1 : r5) (rm : bv 3)
| IFcvtSD (rd rs1 : r5) (rm : bv 3)
| IOther (i : instr).

Definition w_of_imm {n} (b : bv n) : w64 := Z2w (bv_signed b).
Definition w_of_uimm {n} (b : bv n) : w64 := Z2w (bv_unsigned b).

Definition of_instr (i : instr) : option finstr :=
  let R := r5_of_reg in
  match i with
  | Lui rd imm => match R rd with Some d => Some (ILui d (Z2w (bv_signed imm * 4096))) | _ => None end
  | Auipc rd imm => match R rd with Some d => Some (IAuipc d (Z2w (bv_signed imm * 4096))) | _ => None end
  | Jal rd imm => match R rd with Some d => Some (IJal d (w_of_imm imm)) | _ => None end
  | Jalr rd rs1 imm => match R rd, R rs1 with Some d, Some s => Some (IJalr d s (w_of_imm imm)) | _, _ => None end
  | Branch c rs1 rs2 imm => match R rs1, R rs2 with Some a, Some b => Some (IBranch c a b (w_of_imm imm)) | _, _ => None end
  | Load sz sx rd rs1 imm => match R rd, R rs1 with Some d, Some s => Some (ILoad sz sx d s (w_of_imm imm)) | _, _ => None end
  | Store sz rs1 rs2 imm => match R rs1, R rs2 with Some a, Some b => Some (IStore sz a b (w_of_imm imm)) | _, _ => None end
  | OpImm op rd rs1 imm => match R rd, R rs1 with Some d, Some s => Some (IOpImm op d s (w_of_imm imm)) | _, _ => None end
  | ShiftImm op rd rs1 sh => match R rd, R rs1 with Some d, Some s => Some (IOpImm op d s (w_of_uimm sh)) | _, _ => None end
  | Op op rd rs1 rs2 => match R rd, R rs1, R rs2 with Some d, Some a, Some b => Some (IOp op d a b) | _, _, _ => None end
  | OpImm32 rd rs1 imm => match R rd, R rs1 with Some d, Some s => Some (IOpImm32 ALU_ADD d s (w_of_imm imm)) | _, _ => None end
  | ShiftImm32 op rd rs1 sh => match R rd, R rs1 with Some d, Some s => Some (IOpImm32 op d s (w_of_uimm sh)) | _, _ => None end
  | Op32 op rd rs1 rs2 => match R rd, R rs1, R rs2 with Some d, Some a, Some b => Some (IOp32 op d a b) | _, _, _ => None end
  | Fence _ _ _ _ _ | FenceI _ _ _ => Some IFence
  | Ecall => Some IEcall
  | Mul op rd rs1 rs2 => match R rd, R rs1, R rs2 with Some d, Some a, Some b => Some (IMul op d a b) | _, _, _ => None end
  | Mul32 op rd rs1 rs2 => match R rd, R rs1, R rs2 with Some d, Some a, Some b => Some (IMul32 op d a b) | _, _, _ => None end
  | Lr wd _ _ rd rs1 => match R rd, R rs1 with Some d, Some s => Some (ILr wd d s) | _, _ => None end
  | Sc wd _ _ rd rs1 rs2 => match R rd, R rs1, R rs2 with Some d, Some a, Some b => Some (ISc wd d a b) | _, _, _ => None end
  | Amo op wd _ _ rd rs1 rs2 => match R rd, R rs1, R rs2 with Some d, Some a, Some b => Some (IAmo op wd d a b) | _, _, _ => None end
  | FLoad fmt rd rs1 imm => match R rd, R rs1 with Some d, Some s => Some (IFLoad fmt d s (w_of_imm imm)) | _, _ => None end
  | FStore fmt rs1 rs2 imm => match R rs1, R rs2 with Some a, Some b => Some (IFStore fmt a b (w_of_imm imm)) | _, _ => None end
  | Fmv dir fmt rd rs1 => match R rd, R rs1 with Some d, Some s => Some (IFmv dir fmt d s) | _, _ => None end
  | Fcvt FC_D FC_S rd rs1 rm => match R rd, R rs1 with Some d, Some s => Some (IFcvtDS d s rm) | _, _ => None end
  | Fcvt FC_S FC_D rd rs1 rm => match R rd, R rs1 with Some d, Some s => Some (IFcvtSD d s rm) | _, _ => None end
  | _ => Some (IOther i)
  end.

Definition itab := IMap.t finstr.

Section WithSegs.
Variable segs : list Segment.

Definition decode_at (pc : int) : option finstr :=
  match fetch_word segs (Z_to_bv 64 (to_Z pc)) with
  | Some w =>
      if is_ecall w then Some IEcall else
      match decode_any w with
      | Some (i, 4%Z) => of_instr i
      | _ => None
      end
  | None => None
  end.

Fixpoint build_itab (pcs : list int) (acc : itab) : itab :=
  match pcs with
  | [] => acc
  | pc :: pcs' => build_itab pcs' (match decode_at pc with Some fi => IMap.add pc fi acc | None => acc end)
  end.

Fixpoint pcs_from (lo : int) (n : nat) : list int :=
  match n with O => [] | S n' => lo :: pcs_from (PrimInt63.add lo 4%uint63) n' end.

Definition itab_ok (t : itab) : Prop :=
  forall pc fi, IMap.find pc t = Some fi -> decode_at pc = Some fi.

End WithSegs.
End FI.
