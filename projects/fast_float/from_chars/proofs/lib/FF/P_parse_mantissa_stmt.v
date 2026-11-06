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

Definition parse_mantissa_entry : Z := 0x252a4.
Definition parse_mantissa_frame : Z := 144.

(* [comment removed for export] *)
Definition parse_mantissa_W (sp A D : Z) : list ivl := [(sp - 144, sp); (A, A + 498); (D, D + 8)]%Z.

Definition parse_mantissa_post
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (A D maxd : Z) (ws : list word)
    (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : word -> option byte)
                    (ws' : list word) (len' digits : Z),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom PSEGS)
    /\ munch (parse_mantissa_W (bv_unsigned sp) A D) m m'
    /\ wmono PSEGS m m'
    /\ stk PSEGS m' (bv_unsigned sp - 144) (bv_unsigned sp)
    /\ u64arr PSEGS m' A ws'
    /\ length ws' = 62%nat
    /\ rw_cells PSEGS m' (A + 496) [C2 (Z_to_bv 64 len')]
    /\ rw_cells PSEGS m' D [C8 (Z_to_bv 64 digits)]
    /\ (0 <= len' <= 62)%Z
    /\ (0 <= digits <= maxd + 1)%Z      (* [comment removed for export] *)
    /\ bnorm ws' (Z.to_nat len')
    /\ (bval ws' (Z.to_nat len') < 2 ^ (64 * (digits / 19 + 3)))%Z.

Definition parse_mantissa_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (ws : list word) (iptr fptr : word) (ibs fbs : list byte) (dg : word),
    stk PSEGS m (bv_unsigned sp - 144) (bv_unsigned sp) ->
    (bv_unsigned sp mod 16 = 0)%Z ->
    pristine m 0x10000 0x22000 ->
    (* [comment removed for export] *)
    u64arr PSEGS m (bv_unsigned a0) ws -> length ws = 62%nat ->
    rw_cells PSEGS m (bv_unsigned a0 + 496) [C2 (Z_to_bv 64 0)] ->
    (bv_unsigned a0 mod 8 = 0)%Z ->
    (* [comment removed for export] *)
    rw_cells PSEGS m (bv_unsigned a1 + 32)
        [C8 iptr; C8 (Z_to_bv 64 (Z.of_nat (length ibs))); C8 fptr; C8 (Z_to_bv 64 (Z.of_nat (length fbs)))] ->
    bytes_at PSEGS m (bv_unsigned iptr) ibs -> (bv_unsigned iptr <> 0)%Z ->
    (bv_unsigned iptr + Z.of_nat (length ibs) < 2^64)%Z -> (Z.of_nat (length ibs) < 2^40)%Z ->
    bytes_at PSEGS m (bv_unsigned fptr) fbs ->
    (bv_unsigned fptr + Z.of_nat (length fbs) < 2^64)%Z -> (Z.of_nat (length fbs) < 2^40)%Z ->
    (bv_unsigned fptr = 0 -> length fbs = 0%nat)%Z ->
    (* [comment removed for export] *)
    (0 < bv_unsigned a2 <= 769)%Z ->
    (* [comment removed for export] *)
    rw_cells PSEGS m (bv_unsigned a3) [C8 dg] ->
    (* [comment removed for export] *)
    (0x22000 <= bv_unsigned sp - 144)%Z ->
    (bv_unsigned sp <= bv_unsigned a1 + 32)%Z ->
    (bv_unsigned a1 + 64 <= bv_unsigned a0)%Z ->
    (bv_unsigned a0 + 498 <= bv_unsigned a3)%Z ->
    (bv_unsigned a3 + 8 <= bv_unsigned iptr \/ 16 <= bv_unsigned iptr /\ bv_unsigned iptr + Z.of_nat (length ibs) <= bv_unsigned sp - 144)%Z ->   (* [comment removed for export] *)
    (bv_unsigned fptr <> 0 -> bv_unsigned a3 + 8 <= bv_unsigned fptr \/ 16 <= bv_unsigned fptr /\ bv_unsigned fptr + Z.of_nat (length fbs) <= bv_unsigned sp - 144)%Z ->   (* [comment removed for export] *)
    evt PSEGS (parse_mantissa_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                 F fc (bv_unsigned a0) (bv_unsigned a3) (bv_unsigned a2) ws m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x252a4) fc None m (seg_rom PSEGS)).
