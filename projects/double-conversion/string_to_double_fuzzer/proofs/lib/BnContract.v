(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import PropExec CatSim LibIface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition CBD_TBL_LO : Z := 0x13a88.
Definition CBD_TBL_HI : Z := 0x13ab8.

Section Contract.
  Variable segs : list Segment.
  Variables (ENTRY FR : Z).

  (* [comment removed for export] *)
  Definition cbd_stmt : Prop :=
    forall (fx : FPState) (regs : bvmap 5 word) (mem rom : word -> option byte)
           (sp buf len expo e a4 : Z) (ret f : word),
      getr regs (Z_to_bv 5 1) = ret -> bv_unsigned ret mod 4 = 0 ->
      getr regs (Z_to_bv 5 2) = Z_to_bv 64 sp -> sp mod 16 = 0 -> FR <= sp -> sp < 2 ^ 62 ->
      getr regs (Z_to_bv 5 10) = Z_to_bv 64 buf -> 0 < buf -> buf + len < 2 ^ 62 ->
      getr regs (Z_to_bv 5 11) = Z_to_bv 64 len -> getr regs (Z_to_bv 5 12) = Z_to_bv 64 expo ->
      getr regs (Z_to_bv 5 13) = f -> getr regs (Z_to_bv 5 14) = Z_to_bv 64 a4 -> a4 mod 2 ^ 32 = e mod 2 ^ 32 ->
      1 <= len <= 780 -> -323 <= len + expo <= 309 -> -2047 <= e <= 2047 ->
      (forall i, 0 <= i < len ->
         exists d, rdn segs mem (Z_to_bv 64 (buf + i)) 1 = Some [d] /\ 48 <= bv_unsigned d <= 57) ->
      store_ok segs mem (Z_to_bv 64 (sp - FR)) (Z.to_nat FR) = true ->
      (sp <= buf \/ buf + len <= sp - FR) -> CBD_TBL_HI <= sp - FR ->
      (forall a b, CBD_TBL_LO <= a < CBD_TBL_HI -> mem (Z_to_bv 64 a) = Some b ->
         memory_read segs (Z_to_bv 64 a) 1 = Some [b]) ->
      exists (regs' : bvmap 5 word) (mem' : word -> option byte),
           msteps segs (@mkst fx regs (Z_to_bv 64 ENTRY) mem rom) (@mkst fx regs' ret mem' rom)
        /\ keeps_cs regs regs'
        /\ (exists r, getr regs' (Z_to_bv 5 10) = Z_to_bv 64 r /\ -1 <= r <= 1)
        /\ (forall a : word, ~ (sp - FR <= bv_unsigned a < sp) -> mem' a = mem a)
        /\ (forall (a : word) b, mem a = Some b -> exists b', mem' a = Some b').
End Contract.

(* [comment removed for export] *)
Definition CBD_ENTRY_P : Z := 0x35320.
Definition CBD_FR_P : Z := 1888.
Definition cbd_stmt_P : Prop := cbd_stmt SEGS_P CBD_ENTRY_P CBD_FR_P.

(* [comment removed for export] *)
Definition CBD_ENTRY_U : Z := 0x3569c.
Definition CBD_FR_U : Z := 1888.
Definition cbd_stmt_U : Prop := cbd_stmt SEGS_U CBD_ENTRY_U CBD_FR_U.
