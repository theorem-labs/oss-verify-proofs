(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Require OSSVerify.Proofs.fast_float.from_chars.lib.Ox.F112_008.   (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.Proofs.fast_float.from_chars.lib.LibAsan Require Import Shadow.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FFB Require Import B_app2.
Local Ltac lia ::= lia_tc.  (* [comment removed for export] *)
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Open Scope bv_scope.

Notation BSEGS := AsanUbsan.M.loaded_segments.

(* [comment removed for export] *)
Notation COMPARE_ENTRY := 0x98ba8%Z.
Notation RELRO_LO := 0xda000%Z.
Notation RELRO_HI := 0xe0000%Z.
Notation BCELL := 943736%Z.           (* [comment removed for export] *)
Notation IMG_END := 0x63c000%Z.

Definition compare_entry : Z := COMPARE_ENTRY.
Definition compare_FR : Z := 16.
Definition compare_W (sp : word) : list ivl := [(bv_unsigned sp - 16, bv_unsigned sp)]%Z.

Definition compare_post
    (ra sp gp tp s0 s1 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a0 a2 a3 a4 a5 a6 a7 t3 t4 : word) (m' : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom BSEGS)
    /\ munch (compare_W sp) m m'
    /\ wmono BSEGS m m'
    /\ stk BSEGS m' (bv_unsigned sp - 16) (bv_unsigned sp).

Definition compare_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (xs : list word) (xlen : Z) (ys : list word) (ylen : Z),
    u64arr BSEGS m (bv_unsigned a0) xs -> length xs = 62%nat ->
    rw_cells BSEGS m (bv_unsigned a0 + 496) [C2 (Z_to_bv 64 xlen)] ->
    (0 <= xlen <= 62)%Z ->
    u64arr BSEGS m (bv_unsigned a1) ys -> length ys = 62%nat ->
    rw_cells BSEGS m (bv_unsigned a1 + 496) [C2 (Z_to_bv 64 ylen)] ->
    (0 <= ylen <= 62)%Z ->
    (* [comment removed for export] *)
    stk BSEGS m (bv_unsigned sp - 16) (bv_unsigned sp) ->
    (* [comment removed for export] *)
    pristine m RELRO_LO RELRO_HI ->
    ro_cells BSEGS m BCELL [C8 (Z_to_bv 64 ASAN_B)] ->
    (* [comment removed for export] *)
    (bv_unsigned sp <= bv_unsigned a0 \/ bv_unsigned a0 + 498 <= bv_unsigned sp - 16)%Z ->
    (bv_unsigned sp <= bv_unsigned a1 \/ bv_unsigned a1 + 498 <= bv_unsigned sp - 16)%Z ->
    (IMG_END <= bv_unsigned sp - 16)%Z ->
    (KHI <= bv_unsigned sp - 16)%Z -> (bv_unsigned sp <= KTOP)%Z ->
    (app2r (bv_unsigned a0) (bv_unsigned a0 + 504))%Z -> (bv_unsigned a0 + 504 <= KTOP)%Z ->
    (app2r (bv_unsigned a1) (bv_unsigned a1 + 504))%Z -> (bv_unsigned a1 + 504 <= KTOP)%Z ->
    shz BSEGS m (ASAN_B + bv_unsigned a0 / 8) 63 ->
    shz BSEGS m (ASAN_B + bv_unsigned a1 / 8) 63 ->
    evt BSEGS (compare_post ra sp gp tp s0 s1 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t5 t6 F fc m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 COMPARE_ENTRY) fc None m (seg_rom BSEGS)).
