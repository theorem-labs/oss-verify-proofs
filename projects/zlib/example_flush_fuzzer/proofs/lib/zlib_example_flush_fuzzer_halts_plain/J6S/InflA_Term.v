(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: relocated for the zlib 1.4 build, ported to the model, comments removed. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare StepTac.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.E1 Require Import SymEx2Expr SymEx2 SymEx2Tac MemRel SymAux RomRead.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel Require Import Prog ZIface InflateState InflateFast InflateArms Inflate
     InflateInv InflateInvKit.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.D6S Require Import Segs6.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.J6S Require Import ISLayout IS6 InflMem InflRod6 InflCtx6 InflArmLib6.
Import ListNotations.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.PropExec.FPState}.

Section ArmTerm.

  Lemma arm_dead_sim : forall m, (FLAGS <= m <= HCRC \/ m = SYNC) -> arm_stmt m.
  Proof.
    intros m Hm v w R M C Hmode HE HP. exfalso.
    destruct HE as (_ & _ & HX & _). destruct w as [s c r]. open_lx HX. cbn [w_s] in Hmode.
    rewrite Hmode in Xlive. unfold live_mode in Xlive. lia.
  Qed.


  Theorem arm_BAD_sim : arm_stmt BAD.
  Proof.
    intros v w R M C Hmode HE HP. destruct w as [s c r]. cbn [w_s] in Hmode.
    rewrite dispatch_eq. cbn [w_s]. rewrite Hmode. change (arm_for ivar_ref (cv_flush v) BAD) with arm_BAD.
    unfold arm_BAD. rewrite abind_run, ur_eq, aleave_eq.
    destruct HE as (HM & HRC & HX & (HF & HV & G8)).
    exists R, M, pc6_leave. split; [change (arm6_pc BAD) with pc6_leave; apply mst_refl|].
    cbn [arm_post]. split; [reflexivity|]. split; [| apply MFRAME_refl].
    split; [eapply LMEM_regs; [exact HM | reflexivity ..]|].
    split.
    { open_lx HX. unfold LX; cbn [w_s w_c w_r ir_out ir_left ir_in ir_ret irset_ret]. destruct r; cbn in *.
      refine (conj Xwrap (conj Xwbits (conj Xlive (conj Xflags (conj Xin (conj _ (conj Xmsg Xhd))))))). unfold Z_DATA_ERROR; lia. }
    split; [apply same_blocks_refl|].
    open_fix HF. open_vars HV. unfold LREG_leave, LVARS, INF_FRAME; cbn [w_r ir_have ir_put ir_left ir_hold ir_bits ir_out ir_next ir_ret irset_ret].
    destruct r; cbn in *. repeat (split; [assumption|]). exact (G8 Hmode).
  Qed.

  Theorem arm_DONE_sim : arm_stmt DONE.
  Proof.
    intros v w R M C Hmode HE HP. destruct w as [s c r]. cbn [w_s] in Hmode.
    rewrite dispatch_eq. cbn [w_s]. rewrite Hmode. change (arm_for ivar_ref (cv_flush v) DONE) with arm_DONE.
    unfold arm_DONE. rewrite abind_run, ur_eq, aleave_eq.
    destruct HE as (HM & HRC & HX & (HF & HV & G8)).
    change (arm6_pc DONE) with 0x1ece4.
    arm_begin C HM HRC HX HF HV HP.
    arm_symex ilS 4%nat (@nil bool) NoReads (@nil (Z * expr)) (@nil (nat * Z)) v r (@nil Z) NoVals F0
      (mkst R (Z_to_bv 64 0x1ece4) M s6_rom) R' HR' Hfr Hms.
    all: try arm_side.
    exists R', M, pc6_leave. split; [by_run Hms|].
    cbn [arm_post]. split; [reflexivity|]. split; [| apply MFRAME_refl].
    split; [eapply LMEM_regs; [exact HM | reflexivity ..]|].
    split.
    { unfold LX; cbn [w_s w_c w_r ir_out ir_left ir_in ir_ret irset_ret]. destruct r; cbn in *.
      refine (conj Xwrap (conj Xwbits (conj Xlive (conj Xflags (conj Xin (conj _ (conj Xmsg Xhd))))))). unfold Z_STREAM_END; lia. }
    split; [apply same_blocks_refl|].
    symex_reg HR' (9%bv : reg) as G8'.
    unfold LREG_leave, LVARS, INF_FRAME; cbn [w_r ir_have ir_put ir_left ir_hold ir_bits ir_out ir_next ir_ret irset_ret].
    destruct r; cbn in *.
    repeat match goal with |- _ /\ _ => split end;
      try (lazymatch goal with |- getr _ ?n = _ => rewrite (Hfr n eq_refl); assumption end).
    exact G8'.
  Qed.

  Theorem arm_MEM_sim : arm_stmt MEM.
  Proof.
    intros v w R M C Hmode HE HP. destruct w as [s c r]. cbn [w_s] in Hmode.
    rewrite dispatch_eq. cbn [w_s]. rewrite Hmode. change (arm_for ivar_ref (cv_flush v) MEM) with arm_MEM.
    unfold arm_MEM, areturn.
    destruct HE as (HM & HRC & HX & (HF & HV & G8)).
    change (arm6_pc MEM) with 0x1ebe8.
    arm_begin C HM HRC HX HF HV HP.
    arm_symex ilS 4%nat (@nil bool) NoReads (@nil (Z * expr)) (@nil (nat * Z)) v r (@nil Z) NoVals F0
      (mkst R (Z_to_bv 64 0x1ebe8) M s6_rom) R' HR' Hfr Hms.
    all: try arm_side.
    exists R', M, pc6_ret. split; [by_run Hms|].
    cbn [arm_post]. split; [reflexivity|]. split; [| apply MFRAME_refl].
    split; [exact HM|]. split; [exact HX|]. split; [apply same_blocks_refl|].
    symex_reg HR' (21%bv : reg) as G20'.
    split; [| unfold Z_MEM_ERROR, Z_OK; lia].
    unfold LREG_ret, INF_FRAME.
    repeat match goal with |- _ /\ _ => split end;
      try (lazymatch goal with |- getr _ ?n = _ => rewrite (Hfr n eq_refl); assumption end).
    exact G20'.
  Qed.
End ArmTerm.
End FXG.
