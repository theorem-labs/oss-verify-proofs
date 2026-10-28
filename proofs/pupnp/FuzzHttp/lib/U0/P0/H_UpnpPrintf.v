(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run Fs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac ZBridge STRW_tac Image.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import Segs.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Ceiling.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Set Printing Width 1000.

Definition UpnpPrintf_entry := 0x17234%Z.
Notation INITWASCALLED := 0x3b708%Z.

Definition UpnpPrintf_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned sp - 192, bv_unsigned sp)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ stk rsegs m' lo (bv_unsigned sp)
    /\ rw_cells rsegs m' INITWASCALLED [C1 (Z_to_bv 8 0)].

Lemma UpnpPrintf_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo : Z),
  rw_cells rsegs m INITWASCALLED [C1 (Z_to_bv 8 0)] ->
  stk rsegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 192)%Z -> (INITWASCALLED + 1 <= lo)%Z -> mem_inv rsegs m ->
  evt rsegs (UpnpPrintf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 UpnpPrintf_entry) fc None m (seg_rom rsegs)).
Proof.
  intros until lo. intros IW ST LO IWLO MI. unfold UpnpPrintf_entry.
  pose proof (word_lt64 sp) as SR. pose proof ST as ST0. destruct ST0 as [LO0 _].
  pose proof (munch_refl [(bv_unsigned sp - 192, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
  carve_frame 192%nat ST.
  zstep. do 9 step. zstep. step. step. step. zstep. zstep. zstep. zstep.
  if_cases K0; zify_cond K0.
  2:{ exfalso. clear -K0. cbv in K0. lia. }
  do 11 step.
  release_frame FR ST (bv_unsigned sp).
  unfold UpnpPrintf_post. finish.
Qed.
