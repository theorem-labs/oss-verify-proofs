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
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Export P_slow_path_float_stmt.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Open Scope bv_scope.

Notation PSEGS := Plain.M.loaded_segments.

Definition from_chars_float_entry : Z := 0x26a14.
Definition from_chars_float_frame : Z := 112.
(* [comment removed for export] *)
Definition from_chars_float_need  : Z := 112 + 2496.

(* [comment removed for export] *)
Definition FCF_OPT2 : Z := 42949673006.

(* [comment removed for export] *)
Definition from_chars_float_W (sp v : Z) : list ivl :=
  [(sp - from_chars_float_need, sp); (v, v + 4)]%Z.

Definition from_chars_float_post
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (V : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
                    (F' : bvmap 5 word) (fc' : bv 32) (m' : word -> option byte) (v' : word),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (ret_pc ra) fc' None m' (seg_rom PSEGS)
    /\ munch (from_chars_float_W (bv_unsigned sp) V) m m'
    /\ wmono PSEGS m m'
    /\ frm0 fc'
    /\ stk PSEGS m' (bv_unsigned sp - from_chars_float_need) (bv_unsigned sp)
    /\ rw_cells PSEGS m' V [C4 v'].

Definition from_chars_float_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (bs : list byte) (v : word) (fmt : Z),
    (* [comment removed for export] *)
    a3 = Z_to_bv 64 fmt -> (fmt = 1 \/ fmt = 4 \/ fmt = 5)%Z ->
    a4 = Z_to_bv 64 FCF_OPT2 ->
    (* [comment removed for export] *)
    bytes_at PSEGS m (bv_unsigned a0) bs ->
    Z.of_nat (length bs) = (bv_unsigned a1 - bv_unsigned a0)%Z ->
    (0 <= bv_unsigned a1 - bv_unsigned a0 < 2^40)%Z ->
    (bv_unsigned a1 < 2^64 - 8)%Z ->
    (* [comment removed for export] *)
    rw_cells PSEGS m (bv_unsigned a2) [C4 v] ->
    (bv_unsigned a2 mod 4 = 0)%Z ->
    (* [comment removed for export] *)
    stk PSEGS m (bv_unsigned sp - from_chars_float_need) (bv_unsigned sp) ->
    (bv_unsigned sp mod 16 = 0)%Z ->
    (0x97000 <= bv_unsigned sp - from_chars_float_need)%Z ->
    (* [comment removed for export] *)
    (0 < bv_unsigned a0)%Z -> (0 < bv_unsigned a2)%Z -> (0x97000 <= bv_unsigned a2)%Z ->
    (* [comment removed for export] *)
    pristine m 0x10000 0x22000 ->
    pristine m P_FMIN (P_FMIN + 4) ->
    frm0 fc ->
    (* [comment removed for export] *)
    (bv_unsigned sp <= bv_unsigned a0 \/ 16 <= bv_unsigned a0 /\ bv_unsigned a1 <= bv_unsigned sp - from_chars_float_need)%Z ->   (* [comment removed for export] *)
    (bv_unsigned a2 + 4 <= bv_unsigned sp - from_chars_float_need \/ bv_unsigned sp <= bv_unsigned a2)%Z ->
    (bv_unsigned a1 <= bv_unsigned a2 \/ bv_unsigned a2 + 4 <= bv_unsigned a0)%Z ->
    evt PSEGS (from_chars_float_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (bv_unsigned a2) m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x26a14) fc None m (seg_rom PSEGS)).
