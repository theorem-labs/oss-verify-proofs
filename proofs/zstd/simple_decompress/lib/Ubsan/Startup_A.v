(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ITree Nodes Decode SysStep RegsEquiv.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import StoreFast.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import StrFun STRW_tac Startup_kit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg F_memset F_memcpy.
Import ListNotations.
Open Scope bv_scope.
Import ITree.Exc.
(* [comment removed for export] *)
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

Notation rsegs := UImg.usegs.

(* [comment removed for export] *)
Notation RLIBC := 0x68488%Z (only parsing).      (* [comment removed for export] *)
Notation RTLL := 0x68200%Z (only parsing).       (* [comment removed for export] *)
Notation RTD := 0x48130%Z (only parsing).        (* [comment removed for export] *)
Notation RTP := 0x481f8%Z (only parsing).        (* [comment removed for export] *)
Notation RSYSINFO := 0x68470%Z (only parsing).
Notation RDEFSTACK := 0x38098%Z (only parsing).
Notation RGOT_DYNAMIC := 0x36df0%Z (only parsing).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition rinit_tls_post (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (sysinfo auxvp page_size : word) (m : word -> option byte) (t : Z) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp (Z_to_bv 64 RTP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned sp - 64, bv_unsigned sp); (RTD, 0x48280); (0x68208, 0x68238); (RLIBC, 0x684f0)]%Z m m'
    /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ stk rsegs m' lo (bv_unsigned sp)
    /\ rw_cells rsegs m' RTD (td_cells (Z_to_bv 64 RTD) (Z_to_bv 64 RTD) (Z_to_bv 64 RTD) sysinfo (Z_to_bv 64 t) z64 (Z_to_bv 64 2)
                                (Z_to_bv 64 0x481a8) (* [comment removed for export] *) (Z_to_bv 64 0x684c0) (* [comment removed for export] *) (Z_to_bv 64 0x48208) (* [comment removed for export] *) z64)
    /\ rw_cells rsegs m' RLIBC (libc_cells (Z_to_bv 8 1) auxvp (Z_to_bv 64 224) (Z_to_bv 64 8) page_size)
    (* [comment removed for export] *)
    /\ rw_cells rsegs m' RTLL [C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 (Z_to_bv 64 8); C8 z64]
    /\ rw_cells rsegs m' RSYSINFO [C8 sysinfo]
    /\ rw_cells rsegs m' RDEFSTACK [C4 (Z_to_bv 64 0x20000)]
    /\ rw_cells rsegs m' RGOT_DYNAMIC [C8 z64]
    /\ (0 < t < 4194304)%Z.

Lemma rinit_tls_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (sysinfo page_size auxvp : word),
  stk rsegs m lo (bv_unsigned sp) ->
  (* [comment removed for export] *)
  rw_cells rsegs m (bv_unsigned a0 + 24) [C8 (Z_to_bv 64 0x10040); C8 (Z_to_bv 64 56); C8 (Z_to_bv 64 10)] ->
  rw_cells rsegs m RTD (td_cells z64 z64 z64 z64 z64 z64 z64 z64 z64 z64 z64) ->
  rw_cells rsegs m RLIBC (libc_cells (Z_to_bv 8 0) auxvp z64 z64 page_size) ->
  rw_cells rsegs m RTLL [C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64] ->
  rw_cells rsegs m RSYSINFO [C8 sysinfo] ->
  rw_cells rsegs m RDEFSTACK [C4 (Z_to_bv 64 0x20000)] ->
  rw_cells rsegs m RGOT_DYNAMIC [C8 z64] ->
  mem_inv rsegs m ->
  (lo <= bv_unsigned sp - 64)%Z -> (0x69000 <= lo)%Z ->
  (bv_unsigned sp <= bv_unsigned a0)%Z -> (bv_unsigned a0 + 48 <= 2^64)%Z ->
  impl rsegs (at_node rsegs) (enode NSetTid dec_set_tid)
       (epost (rinit_tls_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo sysinfo auxvp page_size m))
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           F (Z_to_bv 64 0x2dba8) fc None m (seg_rom rsegs)).
Proof.
  intros until auxvp. intros ST AUX TDC LC MT SI DS GD MI LO LOLO A0LO A0HI.
  unfold td_cells, libc_cells in *.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (RTD, 0x48280); (0x68208, 0x68238); (RLIBC, 0x684f0)]%Z m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  apply impl_enode.
  carve_frame 64%nat ST.
  (* [comment removed for export] *)
  steps_to 0x2dc80%Z.
  (* [comment removed for export] *)
  steps_to 0x2de04%Z.
  (* [comment removed for export] *)
  step_ecall.
  split. { at_node_solve. }
  intros rsp t Hdec. apply dec_set_tid_Some in Hdec. destruct Hdec as [ci [-> Ht]].
  sys_nret.
  steps_to 0x2de54%Z.
  release_frame FR ST (bv_unsigned sp). astep.
  unfold rinit_tls_post, td_cells, libc_cells. cbv delta [Fork.PID_MAX_ENVELOPE] in Ht. sys_finish; lia.
Qed.
