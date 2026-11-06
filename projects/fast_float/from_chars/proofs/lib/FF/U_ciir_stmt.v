(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
Import ListNotations.

Module U_copy_bwd_impl_stmt.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Local Open Scope bv_scope.

Notation USEGS := Ubsan.M.loaded_segments.

Definition copy_bwd_impl_entry : Z := 0x27b54.

(* [comment removed for export] *)
Definition copy_bwd_impl_post
    (ra sp gp tp s0 s1 a0 a1 a2 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (bs : list byte) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a1
                 (Z_to_bv 64 (bv_unsigned a2 - (bv_unsigned a1 - bv_unsigned a0))) a2' a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom USEGS)
    /\ munch [(bv_unsigned sp - 32, bv_unsigned sp);
              (bv_unsigned a2 - (bv_unsigned a1 - bv_unsigned a0), bv_unsigned a2)]%Z m m'
    /\ wmono USEGS m m'
    /\ u8arr USEGS m' (bv_unsigned a2 - (bv_unsigned a1 - bv_unsigned a0)) bs
    /\ stk USEGS m' (bv_unsigned sp - 32) (bv_unsigned sp).

Definition copy_bwd_impl_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (n D : Z) (bs old : list byte),
    stk USEGS m (bv_unsigned sp - 32) (bv_unsigned sp) ->
    (bv_unsigned a1 = bv_unsigned a0 + n)%Z ->
    (bv_unsigned a2 = D + n)%Z ->
    (0 <= n < 2 ^ 40)%Z -> (n mod 8 = 0)%Z ->
    bytes_at USEGS m (bv_unsigned a0) bs -> Z.of_nat (length bs) = n ->
    u8arr USEGS m D old -> length old = length bs ->
    (bv_unsigned a0 mod 8 = 0)%Z -> (D mod 8 = 0)%Z ->
    (0 < bv_unsigned a0)%Z -> (0 < D)%Z ->
    (bv_unsigned ra mod 2 = 0)%Z ->
    (* [comment removed for export] *)
    (D + n <= bv_unsigned sp - 32 \/ bv_unsigned sp <= D)%Z ->
    (bv_unsigned a0 + n <= bv_unsigned sp - 32 \/ bv_unsigned sp <= bv_unsigned a0)%Z ->
    evt USEGS (copy_bwd_impl_post ra sp gp tp s0 s1 a0 a1 a2 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc bs m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x27b54) fc None m (seg_rom USEGS)).
End U_copy_bwd_impl_stmt.

Module U_copy_bwd_stmt.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Local Open Scope bv_scope.

Notation USEGS := Ubsan.M.loaded_segments.

Definition copy_bwd_entry : Z := 0x27ad8.

(* [comment removed for export] *)
Definition copy_bwd_post
    (ra sp gp tp s0 s1 a0 a1 a2 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (bs : list byte) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a1
                 (Z_to_bv 64 (bv_unsigned a2 - (bv_unsigned a1 - bv_unsigned a0))) a2' a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom USEGS)
    /\ munch [(bv_unsigned sp - 64, bv_unsigned sp);
              (bv_unsigned a2 - (bv_unsigned a1 - bv_unsigned a0), bv_unsigned a2)]%Z m m'
    /\ wmono USEGS m m'
    /\ u8arr USEGS m' (bv_unsigned a2 - (bv_unsigned a1 - bv_unsigned a0)) bs
    /\ stk USEGS m' (bv_unsigned sp - 64) (bv_unsigned sp).

Definition copy_bwd_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (n D : Z) (bs old : list byte),
    stk USEGS m (bv_unsigned sp - 64) (bv_unsigned sp) ->
    (bv_unsigned a1 = bv_unsigned a0 + n)%Z ->
    (bv_unsigned a2 = D + n)%Z ->
    (0 <= n < 2 ^ 40)%Z -> (n mod 8 = 0)%Z ->
    bytes_at USEGS m (bv_unsigned a0) bs -> Z.of_nat (length bs) = n ->
    u8arr USEGS m D old -> length old = length bs ->
    (bv_unsigned a0 mod 8 = 0)%Z -> (D mod 8 = 0)%Z ->
    (0 < bv_unsigned a0)%Z -> (0 < D)%Z ->
    (bv_unsigned ra mod 2 = 0)%Z ->
    (* [comment removed for export] *)
    (D + n <= bv_unsigned sp - 64 \/ bv_unsigned sp <= D)%Z ->
    (bv_unsigned a0 + n <= bv_unsigned sp - 64 \/ bv_unsigned sp <= bv_unsigned a0)%Z ->
    evt USEGS (copy_bwd_post ra sp gp tp s0 s1 a0 a1 a2 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc bs m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x27ad8) fc None m (seg_rom USEGS)).
End U_copy_bwd_stmt.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Open Scope bv_scope.

Notation USEGS := Ubsan.M.loaded_segments.

Definition ciir_entry : Z := 0x22d6c.

(* [comment removed for export] *)
Definition ciir_result (n : Z) (bs : list byte) : Z :=
  if (n =? 0)%Z then 0
  else (bv_unsigned (nth (Z.to_nat (n - 1)) bs (Z_to_bv 8 0)) mod 4)%Z.

Definition ciir_remaining (n : Z) : Z := if (n =? 0)%Z then 0 else n - 1.

(* [comment removed for export] *)
Definition ciir_W (sp p : word) : list ivl :=
  [(bv_unsigned sp - 16, bv_unsigned sp); (bv_unsigned p + 8, bv_unsigned p + 16)]%Z.

Definition ciir_post
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (p dptr : word) (n : Z) (bs : list byte)
    (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (ciir_result n bs)) a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom USEGS)
    /\ munch (ciir_W sp p) m m'
    /\ wmono USEGS m m'
    /\ rw_cells USEGS m' (bv_unsigned p) [C8 dptr; C8 (Z_to_bv 64 (ciir_remaining n))]
    /\ stk USEGS m' (bv_unsigned sp - 16) (bv_unsigned sp).

Definition ciir_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (dptr : word) (n : Z) (bs : list byte),
    a1 = Z_to_bv 64 0 -> a2 = Z_to_bv 64 3 ->
    (* [comment removed for export] *)
    rw_cells USEGS m (bv_unsigned a0) [C8 dptr; C8 (Z_to_bv 64 n)] ->
    bytes_at USEGS m (bv_unsigned dptr) bs ->
    Z.of_nat (length bs) = n ->
    (bv_unsigned dptr + n < 2^64)%Z ->
    (n = 0 \/ 0 < bv_unsigned dptr)%Z ->
    (* [comment removed for export] *)
    stk USEGS m (bv_unsigned sp - 16) (bv_unsigned sp) ->
    (* [comment removed for export] *)
    (n = 0 \/ bv_unsigned a0 + 16 <= bv_unsigned dptr \/ bv_unsigned dptr + n <= bv_unsigned a0)%Z ->
    (bv_unsigned sp <= bv_unsigned a0 \/ bv_unsigned a0 + 16 <= bv_unsigned sp - 16)%Z ->
    (n = 0 \/ bv_unsigned sp <= bv_unsigned dptr \/ bv_unsigned dptr + n <= bv_unsigned sp - 16)%Z ->
    evt USEGS (ciir_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 dptr n bs m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x22d6c) fc None m (seg_rom USEGS)).
