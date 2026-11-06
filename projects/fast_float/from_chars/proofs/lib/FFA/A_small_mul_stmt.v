(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.Proofs.fast_float.from_chars.lib.LibAsan Require Import Shadow.
From OSSVerify.fast_float.from_chars.images Require Import Asan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Import Bigint_defs.
From OSSVerify.Proofs.fast_float.from_chars.lib.FFA Require Import A_app2.
Local Ltac lia ::= lia_tc.  (* [comment removed for export] *)
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Open Scope bv_scope.

Notation ASEGS := Asan.M.loaded_segments.

(* [comment removed for export] *)
Notation SMUL_ENTRY := 0x962d4%Z.
Notation RELRO_LO := 0xd9000%Z.       (* [comment removed for export] *)
Notation RELRO_HI := 0xde000%Z.
Notation BCELL := 937400%Z.           (* [comment removed for export] *)
Notation IMG_END := 0x63a000%Z.        (* [comment removed for export] *)

Definition small_mul_entry : Z := SMUL_ENTRY.
Definition small_mul_FR : Z := 16.

(* [comment removed for export] *)
Definition small_mul_W (A : Z) (sp : word) : list ivl :=
  [(A, A + 498); (bv_unsigned sp - 16, bv_unsigned sp)]%Z.

Definition small_mul_post
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (A y : Z) (ws : list word) (len : Z)
    (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : word -> option byte) (ws' : list word) (len' : Z),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom ASEGS)
    /\ munch (small_mul_W A sp) m m'
    /\ wmono ASEGS m m'
    /\ u64arr ASEGS m' A ws'
    /\ length ws' = 62%nat
    /\ rw_cells ASEGS m' (A + 496) [C2 (Z_to_bv 64 len')]
    /\ (len <= len' <= len + 1 /\ len' <= 62)%Z
    /\ bval ws' (Z.to_nat len') = (bval ws (Z.to_nat len) * y)%Z
    /\ (y <> 0%Z -> bnorm ws (Z.to_nat len) -> bnorm ws' (Z.to_nat len'))
    /\ stk ASEGS m' (bv_unsigned sp - 16) (bv_unsigned sp).

Definition small_mul_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (ws : list word) (len : Z),
    (* [comment removed for export] *)
    u64arr ASEGS m (bv_unsigned a0) ws -> length ws = 62%nat ->
    rw_cells ASEGS m (bv_unsigned a0 + 496) [C2 (Z_to_bv 64 len)] ->
    (0 <= len <= 62)%Z ->
    (bval ws (Z.to_nat len) * bv_unsigned a1 < BIG_CAP)%Z ->
    (* [comment removed for export] *)
    stk ASEGS m (bv_unsigned sp - 16) (bv_unsigned sp) ->
    (* [comment removed for export] *)
    pristine m RELRO_LO RELRO_HI ->
    ro_cells ASEGS m BCELL [C8 (Z_to_bv 64 ASAN_B)] ->
    (* [comment removed for export] *)
    (bv_unsigned sp <= bv_unsigned a0 \/ bv_unsigned a0 + 498 <= bv_unsigned sp - 16)%Z ->
    (* [comment removed for export] *)
    (IMG_END <= bv_unsigned sp - 16)%Z ->
    (KHI <= bv_unsigned sp - 16)%Z -> (bv_unsigned sp <= KTOP)%Z ->
    (app2r (bv_unsigned a0) (bv_unsigned a0 + 504))%Z -> (bv_unsigned a0 + 504 <= KTOP)%Z ->
    (* [comment removed for export] *)
    shz ASEGS m (ASAN_B + bv_unsigned a0 / 8) 63 ->
    evt ASEGS (small_mul_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                 F fc (bv_unsigned a0) (bv_unsigned a1) ws len m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 SMUL_ENTRY) fc None m (seg_rom ASEGS)).
