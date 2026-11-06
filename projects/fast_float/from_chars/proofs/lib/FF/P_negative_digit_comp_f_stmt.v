(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Require OSSVerify.Proofs.fast_float.from_chars.lib.Ox.F112_006.   (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Import Bigint_defs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Open Scope bv_scope.

Notation PSEGS := Plain.M.loaded_segments.

Definition negative_digit_comp_f_entry : Z := 0x28e2c.
Definition negative_digit_comp_f_need  : Z := 1808.

Definition negative_digit_comp_f_W (sp A : Z) : list ivl := [(sp - 1808, sp); (A, A + 498)]%Z.

Definition negative_digit_comp_f_post
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (A : Z)
    (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : word -> option byte)
                    (ws' : list word) (len' : Z),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom PSEGS)
    /\ munch (negative_digit_comp_f_W (bv_unsigned sp) A) m m'
    /\ wmono PSEGS m m'
    /\ stk PSEGS m' (bv_unsigned sp - 1808) (bv_unsigned sp)
    /\ u64arr PSEGS m' A ws'
    /\ length ws' = 62%nat
    /\ rw_cells PSEGS m' (A + 496) [C2 (Z_to_bv 64 len')]
    /\ (0 <= len' <= 62)%Z.

Definition negative_digit_comp_f_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (ws : list word) (len : Z) (p2 e : Z),
    stk PSEGS m (bv_unsigned sp - 1808) (bv_unsigned sp) ->
    (bv_unsigned sp mod 16 = 0)%Z ->
    (0x22000 <= bv_unsigned sp - 1808)%Z ->
    pristine m 0x10000 0x22000 ->
    (* [comment removed for export] *)
    u64arr PSEGS m (bv_unsigned a0) ws -> length ws = 62%nat ->
    rw_cells PSEGS m (bv_unsigned a0 + 496) [C2 (Z_to_bv 64 len)] ->
    (0 <= len <= 62)%Z -> (bv_unsigned a0 mod 8 = 0)%Z ->
    bnorm ws (Z.to_nat len) ->
    (* [comment removed for export] *)
    (bv_unsigned a2 = p2 mod 2 ^ 32)%Z -> (- 2 ^ 14 <= p2 <= 2 ^ 14)%Z ->
    (* [comment removed for export] *)
    a3 = Z_to_bv 64 e -> (-1300 <= e <= -1)%Z ->
    (* [comment removed for export] *)
    (bv_unsigned a0 + 498 <= bv_unsigned sp - 1808 \/ bv_unsigned sp <= bv_unsigned a0)%Z ->
    evt PSEGS (negative_digit_comp_f_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                 F fc (bv_unsigned a0) m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x28e2c) fc None m (seg_rom PSEGS)).
