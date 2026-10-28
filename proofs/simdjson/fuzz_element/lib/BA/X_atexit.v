(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac ImageA SysStep.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Str_tac Startup_glue.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import X_aexdefs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Ltac fold_sx32 :=
  repeat match goal with
  | |- context [sx32 (Z_to_bv 64 ?z)] => is_Zlit z; let v := eval vm_compute in (bv_unsigned (sx32 (Z_to_bv 64 z))) in
        replace (sx32 (Z_to_bv 64 z)) with (Z_to_bv 64 v) by (vm_compute; reflexivity)
  end.
Ltac xstep := lstep; fold_sx32; fold_closed_in_goal; try (first [if_true | if_false]).
Ltac xsteps_to p := repeat (tryif at_pc p then fail else xstep).

Definition aex_done (p1 p2 : list byte) (f1 : word) : list cell :=
  [C1 (Z_to_bv 8 1); CB 3 p1; C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 32); CB 4 p2; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 X_CALL); C8 f1].

Definition funcs_on_exit_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (p1 p2 : list byte) (f1 : word) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp); (0x6c7eb8, 0x6c7ed0)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' 0x6c7eb8 (aex_done p1 p2 f1).

Lemma funcs_on_exit_spec1 : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (p1 p2 : list byte) (f1 ar1 : word) (cdt thr sec : byte) (tm1 : word),
  stk asegs m lo (bv_unsigned sp) ->
  rw_cells asegs m AEX (aex_tbl 1 p1 p2 f1) ->
  rw_cells asegs m AEX_A0 [C8 (Z_to_bv 64 X_COVDUMP); C8 ar1] ->
  rw_cells asegs m 0x6c80f8 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->
  ro_cells asegs m 0x205ae0 [C1 (Z_to_bv 8 0)] ->
  mem_inv asegs m ->
  lo <= bv_unsigned sp - 48 -> 0x6ca000 <= lo ->
  evt asegs (funcs_on_exit_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo p1 p2 f1 m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x14b1f0) fc None m (seg_rom asegs)).
Proof.
  intros until tm1. intros ST ATX ATA LIBC COV MI LO LOLO. aex_lits.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (0x6c7eb8, 0x6c7ed0)] m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  carve_frame 48%nat ST.
  xsteps_to 0x14b26c%Z.

  xstep. xsteps_to 0x14b2b4%Z.
  release_frame FR ST (bv_unsigned sp).

  xstep. xsteps_to 0x15d538%Z. xstep.
  unfold funcs_on_exit_post, aex_done. aex_lits. sys_finish.
Qed.

Lemma funcs_on_exit_spec2 : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (p1 p2 : list byte) (cdt thr sec : byte) (tm1 : word),
  stk asegs m lo (bv_unsigned sp) ->
  rw_cells asegs m AEX (aex_tbl 2 p1 p2 (Z_to_bv 64 X_CALL)) ->
  rw_cells asegs m AEX_A0 [C8 (Z_to_bv 64 X_COVDUMP); C8 (Z_to_bv 64 X_AEXGUARD)] ->
  rw_cells asegs m AEF_INCB [C1 (Z_to_bv 8 0)] ->
  rw_cells asegs m 0x6c80f8 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->
  ro_cells asegs m 0x205ae0 [C1 (Z_to_bv 8 0)] ->
  mem_inv asegs m ->
  lo <= bv_unsigned sp - 48 -> 0x6ca000 <= lo ->
  evt asegs (funcs_on_exit_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo p1 p2 (Z_to_bv 64 X_CALL) m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x14b1f0) fc None m (seg_rom asegs)).
Proof.
  intros until tm1. intros ST ATX ATA FLG LIBC COV MI LO LOLO. aex_lits.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (0x6c7eb8, 0x6c7ed0)] m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  carve_frame 48%nat ST.
  xsteps_to 0x14b26c%Z.

  xstep. xsteps_to 0x14b26c%Z.

  xstep. xsteps_to 0x14b2b4%Z.
  release_frame FR ST (bv_unsigned sp).

  xstep. xsteps_to 0x15d538%Z. xstep.
  unfold funcs_on_exit_post, aex_done. aex_lits. sys_finish.
Qed.

Definition aex_case (m : word -> option byte) (p1 p2 : list byte) (f1 : word) : Prop :=
  (exists ar1 : word, rw_cells asegs m AEX (aex_tbl 1 p1 p2 f1) /\ rw_cells asegs m AEX_A0 [C8 (Z_to_bv 64 X_COVDUMP); C8 ar1])
  \/ (f1 = Z_to_bv 64 X_CALL /\ rw_cells asegs m AEX (aex_tbl 2 p1 p2 f1)
      /\ rw_cells asegs m AEX_A0 [C8 (Z_to_bv 64 X_COVDUMP); C8 (Z_to_bv 64 X_AEXGUARD)] /\ rw_cells asegs m AEF_INCB [C1 (Z_to_bv 8 0)]).

Lemma aexA_case : forall m, aexA m -> exists p1 p2 f1, aex_case m p1 p2 f1.
Proof.
  intros m [((p1 & p2 & f1 & T) & (a1 & A) & _ & _)|((p1 & p2 & T) & A & _ & F)].
  - exists p1, p2, f1. left. exists a1. split; assumption.
  - exists p1, p2, (Z_to_bv 64 X_CALL). right. split; [reflexivity|]. split; [exact T|]. split; assumption.
Qed.
