(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA RA_m7de.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require Import AGlofzw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition DTOR_ENTRY : Z := 0x87644.
(* [comment removed for export] *)
Definition DTOR_FRAME : Z := 272.

(* [comment removed for export] *)
Definition MU_GLOBALS : Z := 0xb2470.
Definition ELF_FLAG : Z := 0xb1500.
Definition ODR_A : Z := 0x5e7280.   (* [comment removed for export] *)
Definition ODR_B : Z := 0x5e72c0.   (* [comment removed for export] *)
Definition LOWSH_LO : Z := 0x7fffa000.   (* [comment removed for export] *)
Definition LOWSH_HI : Z := 0x800c8c00.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition dtor_consts (m : word -> option byte) : Prop :=
     ro_cells rsegs m 0xa9808 [C8 (Z_to_bv 64 GMETA); C8 (Z_to_bv 64 (GMETA + 64 * Z.of_nat GCOUNT))]   (* [comment removed for export] *)
  /\ ro_cells rsegs m 0xa8b50 [C8 (Z_to_bv 64 0x144660)]                                            (* [comment removed for export] *)
  /\ ro_cells rsegs m 0x144660 [C8 (Z_to_bv 64 4096)]                                               (* [comment removed for export] *)
  /\ ro_cells rsegs m 0xa8b60 [C8 (Z_to_bv 64 0x1466e8); C8 (Z_to_bv 64 0xb23b8); C8 (Z_to_bv 64 0xb4bb8);
                               C8 (Z_to_bv 64 0xb58a8); C8 (Z_to_bv 64 0xb58b0); C8 (Z_to_bv 64 0xb58a0);
                               C8 (Z_to_bv 64 0xaaa18)]   (* [comment removed for export] *)
  /\ ro_cells rsegs m 0xb23d0 [C4 (Z_to_bv 64 1)]          (* [comment removed for export] *)
  /\ ro_cells rsegs m 0x146760 [C8 (Z_to_bv 64 18446744073709551615)]    (* [comment removed for export] *)
  /\ ro_cells rsegs m 0xb4bb8 [C8 (Z_to_bv 64 0x7fff8000)] (* [comment removed for export] *)
  /\ ro_cells rsegs m 0xb5898 [C1 (Z_to_bv 8 1)]           (* [comment removed for export] *)
  /\ ro_cells rsegs m 0xb441c [C1 (Z_to_bv 8 1)]           (* [comment removed for export] *)
  /\ ro_cells rsegs m 0xaaa18 [C8 (Z_to_bv 64 0xa1f90)]  (* [comment removed for export] *)
  /\ ro_cells rsegs m 0xb58a0 [C8 (Z_to_bv 64 0x7fffffffffff); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
                                                              (* [comment removed for export] *)
  /\ ro_cells rsegs m GMETA (gtab_cells gtab).               (* [comment removed for export] *)

(* [comment removed for export] *)
Definition gchunk (r : grec) (bs : list byte) : list cell := [CB (Z.to_nat (g_size_rz r / 8)) bs].
Definition gshadows (m : word -> option byte) (l : list grec) (bss : list (list byte)) : Prop :=
  Forall2 (fun r bs => rw_cells rsegs m (gsh (g_beg r)) (gchunk r bs)) l bss.

(* [comment removed for export] *)
Definition dtor_W (usp : Z) : list (Z * Z) :=
  [(usp - DTOR_FRAME, usp); (ELF_FLAG, ELF_FLAG + 8); (MU_GLOBALS, MU_GLOBALS + 8); (LOWSH_LO, LOWSH_HI); (ODRLO, ODRHI)].
(* [comment removed for export] *)

Definition dtor_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned sp - 272, bv_unsigned sp); (0xb1500, 0xb1500 + 8); (0xb2470, 0xb2470 + 8); (0x7fffa000, 0x800c8c00); (0x5e7280, 0x5e72c2)] m m'
    /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ stk rsegs m' lo (bv_unsigned sp)
    /\ rw_cells rsegs m' ELF_FLAG [C8 (Z_to_bv 64 0)]
    /\ rw_cells rsegs m' MU_GLOBALS [C8 (Z_to_bv 64 0)].

(* [comment removed for export] *)

(* [comment removed for export] *)
Section CEIL.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

Definition dtor_spec_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z)
         (bss : list (list byte)) (b1 b2 b3 b4 : byte) (junk0 : list byte),
    mem_inv rsegs m ->
    stk rsegs m lo (bv_unsigned sp) -> lo + DTOR_FRAME <= bv_unsigned sp -> alloc_ceiling <= lo -> bv_unsigned sp <= 2^47 ->
    bv_unsigned ra mod 2 = 0 ->
    dtor_consts m ->
    rw_cells rsegs m ELF_FLAG [C8 (Z_to_bv 64 1)] ->
    rw_cells rsegs m MU_GLOBALS [C8 (Z_to_bv 64 0)] ->
    rw_cells rsegs m ODR_A [C1 b1; C1 b2] ->
    rw_cells rsegs m ODR_B [C1 b3; C1 b4] ->
    gshadows m gtab bss ->
    rw_cells rsegs m (gsh GMETA) [CB 2016 junk0] ->
    evt rsegs (dtor_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 DTOR_ENTRY) fc None m (seg_rom rsegs)).

End CEIL.
