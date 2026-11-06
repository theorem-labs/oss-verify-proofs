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
From OSSVerify.Proofs.fast_float.from_chars.lib.FFA Require Import A_rt_stmt A_long_mul_stmt.
Local Ltac lia ::= lia_tc.  (* [comment removed for export] *)
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Open Scope bv_scope.

Notation ASEGS := Asan.M.loaded_segments.

(* [comment removed for export] *)
Notation PM_ENTRY := 0x9474c%Z.
Notation BCELL := 937400%Z.           (* [comment removed for export] *)
Notation TBL10 := 0x25280%Z.           (* [comment removed for export] *)
Notation TBL10_SH := 2147469904%Z.     (* [comment removed for export] *)
Notation TBL10_SHN := 20%Z.

Definition parse_mantissa_entry : Z := PM_ENTRY.
Definition parse_mantissa_frame : Z := 160.
Definition parse_mantissa_need : Z := 176.

(* [comment removed for export] *)
Definition parse_mantissa_W (sp A D : Z) : list ivl := [(sp - 176, sp); (A, A + 498); (D, D + 8)]%Z.

Definition parse_mantissa_post
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (A D maxd : Z) (ws : list word)
    (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : word -> option byte)
                    (ws' : list word) (len' digits : Z),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom ASEGS)
    /\ munch (parse_mantissa_W (bv_unsigned sp) A D) m m'
    /\ wmono ASEGS m m'
    /\ stk ASEGS m' (bv_unsigned sp - 176) (bv_unsigned sp)
    /\ u64arr ASEGS m' A ws'
    /\ length ws' = 62%nat
    /\ rw_cells ASEGS m' (A + 496) [C2 (Z_to_bv 64 len')]
    /\ rw_cells ASEGS m' D [C8 (Z_to_bv 64 digits)]
    /\ (0 <= len' <= 62)%Z
    /\ (0 <= digits <= maxd + 1)%Z      (* [comment removed for export] *)
    /\ bnorm ws' (Z.to_nat len')
    /\ (bval ws' (Z.to_nat len') < 2 ^ (64 * (digits / 19 + 3)))%Z.

Definition parse_mantissa_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (ws : list word) (iptr fptr : word) (ibs fbs : list byte) (dg : word)
         (FS THI GLO gi gin gf gfn : Z),
    stk ASEGS m (bv_unsigned sp - 176) (bv_unsigned sp) ->
    (bv_unsigned sp mod 16 = 0)%Z ->
    pristine m IMG_LO ROD_HI ->
    (* [comment removed for export] *)
    u64arr ASEGS m (bv_unsigned a0) ws -> length ws = 62%nat ->
    rw_cells ASEGS m (bv_unsigned a0 + 496) [C2 (Z_to_bv 64 0)] ->
    (bv_unsigned a0 mod 8 = 0)%Z ->
    (* [comment removed for export] *)
    rw_cells ASEGS m (bv_unsigned a1 + 32)
        [C8 iptr; C8 (Z_to_bv 64 (Z.of_nat (length ibs))); C8 fptr; C8 (Z_to_bv 64 (Z.of_nat (length fbs)))] ->
    bytes_at ASEGS m (bv_unsigned iptr) ibs -> (bv_unsigned iptr <> 0)%Z ->
    (bv_unsigned iptr + Z.of_nat (length ibs) < 2^64)%Z -> (Z.of_nat (length ibs) < 2^40)%Z ->
    bytes_at ASEGS m (bv_unsigned fptr) fbs ->
    (bv_unsigned fptr + Z.of_nat (length fbs) < 2^64)%Z -> (Z.of_nat (length fbs) < 2^40)%Z ->
    (bv_unsigned fptr = 0 -> length fbs = 0%nat)%Z ->
    (* [comment removed for export] *)
    (0 < bv_unsigned a2 <= 769)%Z ->
    (* [comment removed for export] *)
    rw_cells ASEGS m (bv_unsigned a3) [C8 dg] ->
    (* [comment removed for export] *)
    pristine m RELRO_LO RELRO_HI ->
    ro_cells ASEGS m BCELL [C8 (Z_to_bv 64 ASAN_B)] ->
    (* [comment removed for export] *)
    (IMG_END <= bv_unsigned sp - 176)%Z -> (KHI <= bv_unsigned sp - 176)%Z ->
    (bv_unsigned sp <= bv_unsigned a3)%Z -> (bv_unsigned a3 + 8 <= KTOP)%Z ->
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    (app2r (FS) (THI))%Z ->
    (GLO <= bv_unsigned a0 /\ (app2r (GLO) (GLO + FSSIZE)) /\ GLO + FSSIZE <= KTOP)%Z ->
    (FS <= bv_unsigned iptr)%Z -> (bv_unsigned iptr + Z.of_nat (length ibs) <= THI)%Z ->
    (bv_unsigned fptr <> 0 -> FS <= bv_unsigned fptr /\ bv_unsigned fptr + Z.of_nat (length fbs) <= THI)%Z ->
    (bv_unsigned a0 + 498 <= bv_unsigned a1 + 32)%Z -> (bv_unsigned a1 + 64 <= GLO + FSSIZE)%Z ->
    (bv_unsigned a1 mod 8 = 0)%Z ->
    ((THI <= bv_unsigned a0 \/ bv_unsigned a0 + 498 <= FS) /\ GLO + FSSIZE <= bv_unsigned sp - 176 /\ THI <= bv_unsigned sp - 176)%Z ->
    (* [comment removed for export] *)
    shz ASEGS m (ASAN_B + bv_unsigned a0 / 8) 63 ->
    shz ASEGS m (ASAN_B + bv_unsigned a3 / 8) 1 ->
    shz ASEGS m (ASAN_B + (bv_unsigned a1 + 32) / 8) 4 ->
    shz ASEGS m (ASAN_B + gi) gin -> (0 <= gi <= bv_unsigned iptr / 8)%Z ->
    (bv_unsigned iptr + Z.of_nat (length ibs) <= 8 * (gi + gin) <= KTOP)%Z ->
    (bv_unsigned fptr <> 0 ->
       shz ASEGS m (ASAN_B + gf) gfn /\ 0 <= gf <= bv_unsigned fptr / 8 /\
       bv_unsigned fptr + Z.of_nat (length fbs) <= 8 * (gf + gfn) <= KTOP)%Z ->
    shz ASEGS m TBL10_SH TBL10_SHN ->
    evt ASEGS (parse_mantissa_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                 F fc (bv_unsigned a0) (bv_unsigned a3) (bv_unsigned a2) ws m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 PM_ENTRY) fc None m (seg_rom ASEGS)).
