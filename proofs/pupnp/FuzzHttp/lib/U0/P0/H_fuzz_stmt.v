(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run Fs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac ZBridge Image FP.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Top Require Import Realize SafeReach AllocIF SReach AllocSpec.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import Segs F_syscalls.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Ceiling.
Import ListNotations.
Open Scope Z_scope.
Notation mem := (word -> option byte).

Definition fuzz_entry : Z := 0x13fbc.

Definition PARSER_STACK : Z := 16384.

Definition EMPTY_OBJ : Z := 0x3b6e0.

Definition gd_bytes (a : Z) (n : nat) : list byte :=
  match image_bytes rsegs a n with Some bs => bs | None => [] end.

Definition GD_ranges : list (Z * nat) :=
  [(0x2b1a8, 528%nat); (0x2b3b8, 176%nat); (0x2b468, 16%nat); (0x3b700, 12%nat); (0x2a118, 16%nat)].
Definition GD (m : mem) : Prop :=
  Forall (fun r => bytes_at rsegs m (fst r) (gd_bytes (fst r) (snd r))) GD_ranges.

Section S.
Context {HCEIL : HasCeiling}.
  Variable AI : alloc_if rsegs.
  Notation L := (ai_L rsegs AI).
  Notation K := (ai_K rsegs AI).

  Definition fuzz_one_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (LB : list (block K)) (lo B : Z) (canary : word) (m : mem)
      : ai_PS rsegs AI -> list (block K) -> machine_state -> Prop :=
    fun s' LB' ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
      ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (ret_pc ra) fc None m' (seg_rom rsegs)
      /\ alloc_frame AI sp lo B m m' LB
      /\ RHEAP rsegs AI s' LB' m' /\ (forall b, In b LB -> In b LB')
      /\ GD m'
      /\ rw_cells rsegs m' got_ssp [C8 (Z_to_bv 64 ssp_guard)] /\ rw_cells rsegs m' ssp_guard [C8 canary].

  Definition fuzz_one_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : ai_PS rsegs AI) (LB : list (block K))
           (D n lo B : Z) (errv canary : word) (data : list byte),

      bytes_at rsegs m D data -> Z.of_nat (length data) = n -> 0 <= n <= 2^26 ->
      ((n = 0 /\ D = EMPTY_OBJ) \/ (exists k, In (k, D, n) LB)) ->
      RHEAP rsegs AI s LB m -> RENV rsegs AI m B -> bv_unsigned sp <= B -> B < 2^62 ->
      stk rsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - PARSER_STACK ->
      bv_unsigned sp mod 16 = 0 ->
      rw_cells rsegs m (al_errno L) [C4 errv] -> mem_inv rsegs m -> GD m ->
      rw_cells rsegs m got_ssp [C8 (Z_to_bv 64 ssp_guard)] -> rw_cells rsegs m ssp_guard [C8 canary] ->
      tp = Z_to_bv 64 (al_tp L) -> a0 = Z_to_bv 64 D -> a1 = Z_to_bv 64 n -> frm0 fc ->
      SREACH AI (fuzz_one_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc LB lo B canary m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 fuzz_entry) fc None m (seg_rom rsegs))
        s LB.
End S.
