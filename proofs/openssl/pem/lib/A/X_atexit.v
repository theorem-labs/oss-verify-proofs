(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac ImageA SysStep.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import StoreFast.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Str_tac Startup_glue.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import X_ax.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

(* [comment removed for export] *)
Ltac fold_sx32 :=
  repeat match goal with
  | |- context [sx32 (Z_to_bv 64 ?z)] => is_Zlit z; let v := eval vm_compute in (bv_unsigned (sx32 (Z_to_bv 64 z))) in
        replace (sx32 (Z_to_bv 64 z)) with (Z_to_bv 64 v) by (vm_compute; reflexivity)
  end.
Ltac xstep := lstep; fold_sx32; fold_closed_in_goal; try (first [if_true | if_false]).
Ltac xsteps_to p := repeat (tryif at_pc p then fail else xstep).

(* [comment removed for export] *)
Definition atexit_cells_done (k : bool) (p1 p2 : list byte) : list cell :=
  [C1 (Z_to_bv 8 1); CB 3 p1; C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 32); CB 4 p2; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
   C8 (Z_to_bv 64 AX_CALL); C8 (Z_to_bv 64 (if k then AX_CALL else 0))].

Definition funcs_on_exit_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (p1 p2 : list byte) (m : word -> option byte) (k : bool) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp); (0xbc3f40, 0xbc3f58)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' 0xbc3f40 (atexit_cells_done k p1 p2).

Lemma funcs_on_exit_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (fin : byte) (p1 p2 : list byte) (cdt thr sec : byte) (tm1 : word) (k : bool),
  stk asegs m lo (bv_unsigned sp) ->
  rw_cells asegs m 0xbc3f40 (ax_cells k fin p1 p2) ->
  rw_cells asegs m 0xbc4060 (ax_acells k) ->
  rw_cells asegs m 0xbc4180 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->
  ro_cells asegs m 0x6fe9e0 [C1 (Z_to_bv 8 0)] ->
  mem_inv asegs m ->
  lo <= bv_unsigned sp - 48 -> 0xbc6000 <= lo ->
  rw_cells asegs m AX_INCB [C1 (Z_to_bv 8 0)] ->                                       (* [comment removed for export] *)
  evt asegs (funcs_on_exit_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo p1 p2 m k)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x51ae7c) fc None m (seg_rom asegs)).
Proof.
  intros until k. intros ST ATX ATA LIBC COV MI LO LOLO INCB.
  unfold ax_cells, ax_acells, ax_slot, AX_CALL, AX_GUARD, AX_COVD in ATX, ATA. unfold AX_INCB in INCB.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (0xbc3f40, 0xbc3f58)] m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  carve_frame 48%nat ST.
  destruct k.
  - (* [comment removed for export] *)
    xsteps_to 0x51aef8%Z.
    (* [comment removed for export] *)
    xstep. xsteps_to 0x51aef8%Z.
    (* [comment removed for export] *)
    xstep. xsteps_to 0x51af40%Z.
    release_frame FR ST (bv_unsigned sp).
    (* [comment removed for export] *)
    xstep. xsteps_to 0x527538%Z. xstep.
    unfold funcs_on_exit_post, atexit_cells_done, AX_CALL. sys_finish.
  - xsteps_to 0x51aef8%Z.
    (* [comment removed for export] *)
    xstep. xsteps_to 0x51af40%Z.
    release_frame FR ST (bv_unsigned sp).
    (* [comment removed for export] *)
    xstep. xsteps_to 0x527538%Z. xstep.
    unfold funcs_on_exit_post, atexit_cells_done, AX_CALL. sys_finish.
Qed.
