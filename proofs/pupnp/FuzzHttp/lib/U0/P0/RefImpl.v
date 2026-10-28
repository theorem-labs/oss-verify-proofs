(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac ITree Nodes RegsEquiv.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import Segs.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import Startup_A Startup Stdio_base Printf_lib.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import F_atexit.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Spec Require Import Monad Stdio Driver Prog.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Local Notation z64 := (Z_to_bv 64 0).

Definition rat_exit (code : Z) (s : PState) (ms : machine_state) : Prop :=
  exists (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo t : Z) (td0 td1 td2 td3 guard : word)
         (cdt thr sec : byte) (tm1 : word),
    ms = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x17d94) fc None m (seg_rom rsegs)
    /\ stk rsegs m lo (bv_unsigned sp)
    /\ rw_cells rsegs m 0x3b758 [C8 td0; C8 td1; C8 td2; C8 td3; C4 (Z_to_bv 64 t)]
    /\ rw_cells rsegs m 0x5ba80 [C4 z64]
    /\ rw_cells rsegs m 0x2a158 [C8 (Z_to_bv 64 0x2a0b0); C8 (Z_to_bv 64 0x2a0a8)]
    /\ rw_cells rsegs m 0x2a0a8 [C8 (Z_to_bv 64 0x13a8c)]
    /\ rw_cells rsegs m 0x2b6c8 [C1 (Z_to_bv 8 0)]
    /\ rw_cells rsegs m 0x2a0f0 [C8 (Z_to_bv 64 0x17c78); C8 z64]
    /\ rw_cells rsegs m 0x5baa8 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1]
    /\ rw_cells rsegs m 0x2b180 [C8 (Z_to_bv 64 0x2b180)]
    /\ (exists reg : bool, atx_state reg m)
    /\ rw_cells rsegs m 0x5bed8 [C8 z64] /\ rw_cells rsegs m 0x5bec8 [C8 z64]
    /\ rw_cells rsegs m 0x2b658 [C8 (Z_to_bv 64 RSTDOUT)] /\ rw_cells rsegs m 0x2b568 [C8 (Z_to_bv 64 RSTDERR)]
    /\ stdout_file m (ps_so s) /\ stderr_file m
    /\ rw_cells rsegs m 0x2a150 [C8 (Z_to_bv 64 0x5ba88)] /\ rw_cells rsegs m 0x5ba88 [C8 guard]
    /\ mem_inv rsegs m
    /\ tp = Z_to_bv 64 0x3b820 /\ a0 = Z_to_bv 64 code
    /\ 0 < t < 4194304 /\ lo <= bv_unsigned sp - 176 /\ 0x5d000 <= lo
    /\ bv_unsigned sp <= 2^47.

Lemma rimpl_msys_of_enode : forall {St A} (n : node) (pl : resp -> option A) (Q : A -> machine_state -> Prop) (s : St) ms,
  impl rsegs (at_node rsegs) (enode n pl) (epost Q) ms ->
  impl rsegs (at_node rsegs) (Monad.msys n pl s) (epost (fun p ms' => Q (fst p) ms' /\ snd p = s)) ms.
Proof.
  intros St A n pl Q s ms H. unfold Monad.msys, enode in *. cbn in *.
  eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|].
  intros rsp. specialize (Hk rsp). destruct (pl rsp) as [a|]; cbn in *; [|exact Hk].
  eapply evt_mono; [exact Hk|]. intros ms2 HQ. cbn. auto.
Qed.

