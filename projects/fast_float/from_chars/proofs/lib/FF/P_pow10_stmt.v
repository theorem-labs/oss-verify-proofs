(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
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

Definition pow10_entry : Z := 0x26038.
Definition pow10_need : Z := 1264.

Definition pow10_W (sp A : Z) : list ivl := [(sp - 1264, sp); (A, A + 498)]%Z.

Definition pow10_post
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (A e : Z) (ws : list word) (len : Z)
    (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : word -> option byte)
                    (ws' : list word) (len' : Z),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom PSEGS)
    /\ munch (pow10_W (bv_unsigned sp) A) m m'
    /\ wmono PSEGS m m'
    /\ stk PSEGS m' (bv_unsigned sp - 1264) (bv_unsigned sp)
    /\ u64arr PSEGS m' A ws'
    /\ length ws' = 62%nat
    /\ rw_cells PSEGS m' (A + 496) [C2 (Z_to_bv 64 len')]
    /\ (0 <= len' <= 62)%Z
    /\ bval ws' (Z.to_nat len') = (bval ws (Z.to_nat len) * 10 ^ e)%Z
    /\ bnorm ws' (Z.to_nat len')
    /\ pristine m' 0x10000 0x22000.

Definition pow10_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (ws : list word) (len : Z),
    stk PSEGS m (bv_unsigned sp - 1264) (bv_unsigned sp) ->
    (bv_unsigned sp mod 16 = 0)%Z ->
    (0x22000 <= bv_unsigned sp - 1264)%Z ->
    pristine m 0x10000 0x22000 ->
    (* [comment removed for export] *)
    u64arr PSEGS m (bv_unsigned a0) ws -> length ws = 62%nat ->
    rw_cells PSEGS m (bv_unsigned a0 + 496) [C2 (Z_to_bv 64 len)] ->
    (0 <= len <= 62)%Z -> (bv_unsigned a0 mod 8 = 0)%Z ->
    bnorm ws (Z.to_nat len) ->
    (* [comment removed for export] *)
    (bv_unsigned a1 < 2 ^ 11)%Z ->
    (* [comment removed for export] *)
    (bval ws (Z.to_nat len) * 10 ^ (bv_unsigned a1) < BIG_CAP)%Z ->
    (* [comment removed for export] *)
    (bv_unsigned a0 + 498 <= bv_unsigned sp - 1264 \/ bv_unsigned sp <= bv_unsigned a0)%Z ->
    evt PSEGS (pow10_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                 F fc (bv_unsigned a0) (bv_unsigned a1) ws len m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x26038) fc None m (seg_rom PSEGS)).
