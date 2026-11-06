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
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Import Bigint_defs.
Import ListNotations.

Module U_span_index_stmt.
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

Definition span_index_entry : Z := 0x27298.

Definition span_index_post
    (ra sp gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (p : word) (i : Z)
    (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (a1 a2 a3 a4 : word),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (bv_unsigned p + 8 * i)) a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m (seg_rom USEGS)
    /\ munch [] m m
    /\ wmono USEGS m m
    /\ True.   (* [comment removed for export] *)

Definition span_index_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (p : word) (i : Z),
    ov_read_bytes USEGS m a0 8 = Some (le8 p) ->
    a1 = Z_to_bv 64 i ->
    (0 <= i < 2^60)%Z ->
    (bv_unsigned p <> 0)%Z ->
    (bv_unsigned p mod 8 = 0)%Z ->
    (bv_unsigned p + 8 * i < 2^64)%Z ->
    evt USEGS (span_index_post ra sp gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                 F fc p i m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x27298) fc None m (seg_rom USEGS)).
End U_span_index_stmt.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Open Scope bv_scope.

Notation USEGS := Ubsan.M.loaded_segments.

Definition large_add_from_entry : Z := 0x274e8.
Definition large_add_from_frame : Z := 112.

(* [comment removed for export] *)
Definition large_add_from_W (sp A : Z) : list ivl := [(sp - 112, sp); (A, A + 498)]%Z.

Definition large_add_from_post
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (A Y ylen start : Z) (ws ys : list word) (len : Z)
    (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : word -> option byte)
                    (ws' : list word) (len' : Z),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom USEGS)
    /\ munch (large_add_from_W (bv_unsigned sp) A) m m'
    /\ wmono USEGS m m'
    /\ stk USEGS m' (bv_unsigned sp - 112) (bv_unsigned sp)
    /\ u64arr USEGS m' A ws'
    /\ length ws' = 62%nat
    /\ rw_cells USEGS m' (A + 496) [C2 (Z_to_bv 64 len')]
    /\ u64arr USEGS m' Y ys
    /\ (Z.max len (ylen + start) <= len' <= Z.max len (ylen + start) + 1 /\ len' <= 62)%Z
    /\ bval ws' (Z.to_nat len') = (bval ws (Z.to_nat len) + bval ys (Z.to_nat ylen) * 2 ^ (64 * start))%Z.

Definition large_add_from_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (ws : list word) (len : Z) (ys : list word) (ylen start : Z),
    stk USEGS m (bv_unsigned sp - 112) (bv_unsigned sp) ->
    (bv_unsigned sp mod 16 = 0)%Z ->
    (* [comment removed for export] *)
    u64arr USEGS m (bv_unsigned a0) ws -> length ws = 62%nat ->
    rw_cells USEGS m (bv_unsigned a0 + 496) [C2 (Z_to_bv 64 len)] ->
    (0 <= len <= 62)%Z -> (bv_unsigned a0 mod 8 = 0)%Z ->
    (* [comment removed for export] *)
    u64arr USEGS m (bv_unsigned a1) ys -> length ys = 62%nat ->
    a2 = Z_to_bv 64 ylen -> (0 <= ylen <= 62)%Z ->
    (bv_unsigned a1 mod 8 = 0)%Z -> (bv_unsigned a1 <> 0)%Z -> (bv_unsigned a1 + 496 < 2^64)%Z ->
    a3 = Z_to_bv 64 start -> (0 <= start)%Z -> (ylen + start <= 62)%Z ->
    (* [comment removed for export] *)
    (bval ws (Z.to_nat len) + bval ys (Z.to_nat ylen) * 2 ^ (64 * start) < BIG_CAP)%Z ->
    (* [comment removed for export] *)
    (bv_unsigned a0 + 498 <= bv_unsigned sp - 112 \/ bv_unsigned sp <= bv_unsigned a0)%Z ->
    (bv_unsigned a1 + 496 <= bv_unsigned sp - 112 \/ bv_unsigned sp <= bv_unsigned a1)%Z ->
    (bv_unsigned a0 + 498 <= bv_unsigned a1 \/ bv_unsigned a1 + 496 <= bv_unsigned a0)%Z ->
    evt USEGS (large_add_from_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                 F fc (bv_unsigned a0) (bv_unsigned a1) ylen start ws ys len m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x274e8) fc None m (seg_rom USEGS)).
