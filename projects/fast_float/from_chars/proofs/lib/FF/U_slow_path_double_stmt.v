(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Open Scope bv_scope.

Notation USEGS := Ubsan.M.loaded_segments.

Definition slow_path_double_entry : Z := 0x245ac.
Definition slow_path_double_frame : Z := 704.
(* [comment removed for export] *)
Definition slow_path_double_need  : Z := 704 + 1872.
Definition U_FMIN_D : Z := 0x66b98.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition slow_path_double_W (sp v : Z) : list ivl :=
  [(sp - slow_path_double_need, sp); (v, v + 8)]%Z.

Definition slow_path_double_post
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (V : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
                    (F' : bvmap 5 word) (fc' : bv 32) (m' : word -> option byte) (v' : word),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (ret_pc ra) fc' None m' (seg_rom USEGS)
    /\ munch (slow_path_double_W (bv_unsigned sp) V) m m'
    /\ wmono USEGS m m'
    /\ frm0 fc'
    /\ stk USEGS m' (bv_unsigned sp - slow_path_double_need) (bv_unsigned sp)
    /\ rw_cells USEGS m' V [C8 v'].

Definition slow_path_double_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (bs : list byte) (v : word),
    (* [comment removed for export] *)
    bytes_at USEGS m (bv_unsigned a0) bs ->
    Z.of_nat (length bs) = (bv_unsigned a1 - bv_unsigned a0)%Z ->
    (1 <= bv_unsigned a1 - bv_unsigned a0 < 2^40)%Z ->
    (bv_unsigned a1 < 2^64 - 8)%Z ->
    (* [comment removed for export] *)
    a5 = Z_to_bv 64 0 ->
    (* [comment removed for export] *)
    rw_cells USEGS m (bv_unsigned a2) [C8 v] ->
    (bv_unsigned a2 mod 8 = 0)%Z ->
    (* [comment removed for export] *)
    stk USEGS m (bv_unsigned sp - slow_path_double_need) (bv_unsigned sp) ->
    (bv_unsigned sp mod 16 = 0)%Z ->
    (0x99000 <= bv_unsigned sp - slow_path_double_need)%Z ->
    (* [comment removed for export] *)
    (0 < bv_unsigned a0)%Z -> (0 < bv_unsigned a2)%Z ->
    (* [comment removed for export] *)
    (0x99000 <= bv_unsigned a2)%Z ->
    (* [comment removed for export] *)
    pristine m 0x10000 0x22000 ->
    pristine m U_FMIN_D (U_FMIN_D + 4) ->
    frm0 fc ->
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    (bv_unsigned sp <= bv_unsigned a0 \/ 16 <= bv_unsigned a0 /\ bv_unsigned a1 <= bv_unsigned sp - slow_path_double_need)%Z ->   (* [comment removed for export] *)
    (bv_unsigned a2 + 8 <= bv_unsigned sp - slow_path_double_need \/ bv_unsigned sp <= bv_unsigned a2)%Z ->
    (bv_unsigned a1 <= bv_unsigned a2 \/ bv_unsigned a2 + 8 <= bv_unsigned a0)%Z ->
    evt USEGS (slow_path_double_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (bv_unsigned a2) m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x245ac) fc None m (seg_rom USEGS)).
