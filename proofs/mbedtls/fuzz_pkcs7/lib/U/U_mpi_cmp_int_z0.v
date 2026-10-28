(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk Asn1Aux CellsX MpiCoreAux HeapIface.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep MpiVal.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg U_mpi_cmp U_mpi_cmp_int.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXP Require Import LxPMpiTac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Definition mpi_cmp_int_z0_stmt {L : heap_layout} (segs : list Segment) (ENTRY : Z) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (X P sg : Z) (pad : word) (lo : Z),
  rw_cells segs m X (mpi_cells P (Z_to_bv 64 sg) 0 pad) -> X mod 8 = 0 -> 0 < X -> X + 16 <= 2^64 ->
  stk segs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - MPI_CMP_STACK -> alloc_ceiling <= lo -> bv_unsigned sp mod 16 = 0 ->
  (X + 16 <= lo \/ bv_unsigned sp <= X) ->
  mem_inv segs m ->
  a0 = Z_to_bv 64 X -> a1 = Z_to_bv 64 0 ->
  evt segs (mpi_cmp_int_post segs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc 0 lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 ENTRY) fc None m (seg_rom segs)).

Theorem U_mpi_cmp_int_z0_spec {L : heap_layout} : mpi_cmp_int_z0_stmt usegs U_MPI_CMP_INT.
Proof.
  unfold mpi_cmp_int_z0_stmt, U_MPI_CMP_INT. intros until lo. intros CX XAL X0 XB ST LO ACL SPA DA MI -> ->.
  unfold mpi_cells in CX.
  pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m) as MU. pose proof (wmono_refl usegs m) as WM.
  pose proof (proj1 ST) as LO0.
  carve_frame 32%nat ST.
  lxp_split_frame [4;4;8;2;2;4;8]%nat.
  lx_run_tac (PLAN [132168] [] 300%N); lx_tree.
  apply evt_done. unfold mpi_cmp_int_post. cbv beta. do 15 eexists.
  split; [reflexivity|]. split; [assumption|]. split; [assumption|]. split; assumption.
Qed.
