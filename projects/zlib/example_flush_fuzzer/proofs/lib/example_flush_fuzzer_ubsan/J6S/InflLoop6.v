(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare StepTac.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1 Require Import SymEx2Expr SymEx2 SymEx2Tac MemRel SymAux RomRead.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import Prog ZIface InflateState InflateFast InflateArms Inflate
     InflateGarbBase InflateGarb InflateInv InflateInvKit InflateInvLoop.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.D6S Require Import Segs6.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S Require Import ISLayout IS6 InflMem InflRod6 InflCtx6 InflArmLib6.
Import ListNotations.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.

Lemma loop_post_reanchor : forall v w0 w1 stop w' R' M',
  same_blocks (w_s w0) (w_s w1) -> loop_post v w1 stop w' R' M' -> loop_post v w0 stop w' R' M'.
Proof.
  intros v w0 w1 stop w' R' M' HS (A & B & C & D). split; [exact A|]. split; [exact B|].
  split; [exact (same_blocks_trans _ _ _ HS C) | exact D].
Qed.

Lemma pinv_mode_range : forall v w, pinv (cv_NI v) (cv_NO v) (cv_WN v) (cv_TOT0 v) w -> HEAD <= is_mode (w_s w) <= SYNC.
Proof. intros v [s c r] HP. open_pinv HP. destruct SR as (H & _). exact H. Qed.

Section Loop.
  Hypothesis ARMS : forall m, HEAD <= m <= SYNC -> arm_stmt m.

  Definition mstep (flush : Z) (w : iw) : iw + (istop * iw) :=
    match dispatch ivar_ref flush w with
    | ARun _ w' => inl w'
    | ALeave w' => inr (SLeave, w')
    | ARet rc w' => inr (SRet rc, w')
    end.

  Lemma inf_loop_mstep : forall flush w,
    inf_loop ivar_ref flush w = iterZ (64 * (ic_avail_in (w_c w) + ic_avail_out (w_c w) + 64)) (mstep flush) (fun w => (SLeave, w)) w.
  Proof. reflexivity. Qed.

  Lemma loop_sim_n : forall n v w R M,
    ictx v -> ENTRY v w R M -> pinv (cv_NI v) (cv_NO v) (cv_WN v) (cv_TOT0 v) w -> PHI w < Z.of_nat n ->
    let '(stop, w') := match iterK_nat n (mstep (cv_flush v)) w with inl w' => (SLeave, w') | inr r => r end in
    exists R' M',
      msteps s6_segs (mkst R (Z_to_bv 64 (arm6_pc (is_mode (w_s w)))) M s6_rom) (mkst R' (Z_to_bv 64 (stop_pc stop)) M' s6_rom)
      /\ loop_post v w stop w' R' M'
      /\ MFRAME v (ir_put (w_r w)) (ir_put (w_r w')) M M'.
  Proof.
    induction n as [|n IH]; intros v w R M C HE HP Hphi.
    { exfalso. pose proof (PHI_nonneg _ _ _ _ w HP). lia. }
    cbn [iterK_nat]. unfold mstep at 1.
    pose proof (pinv_mode_range v w HP) as Hm.
    pose proof (ic_I0 _ C) as CI0. pose proof (ic_P0 _ C) as CP0.
    destruct (dispatch_ok ivar_ref (cv_flush v) (cv_NI v) (cv_NO v) (cv_WN v) (cv_TOT0 v) ltac:(lia) ltac:(lia) w HP) as [_ A].
    destruct (ARMS (is_mode (w_s w)) Hm v w R M C eq_refl HE HP) as (R2 & M2 & pc2 & Hms2 & HPOST).
    destruct (dispatch ivar_ref (cv_flush v) w) as [[] w2 | w2 | rc w2].
    -
      destruct HPOST as (-> & HE2 & HS2 & HF2). cbn [apost] in A. destruct A as [HP2 Hlt].
      specialize (IH v w2 R2 M2 C HE2 HP2 ltac:(lia)). revert IH.
      destruct (iterK_nat n (mstep (cv_flush v)) w2) as [w3|[stop w3]]; intros (R3 & M3 & Hms3 & HP3 & HF3);
        exists R3, M3; (split; [eapply msteps_trans; [exact Hms2 | exact Hms3]|]);
        (split; [exact (loop_post_reanchor v w w2 _ w3 R3 M3 HS2 HP3) | exact (MFRAME_trans v _ _ _ M M2 M3 HF2 HF3)]).
    -
      destruct HPOST as (-> & HP2 & HF2). exists R2, M2.
      split; [exact Hms2|]. split; [exact HP2 | exact HF2].
    -
      destruct HPOST as (-> & HP2 & HF2). exists R2, M2.
      split; [exact Hms2|]. split; [exact HP2 | exact HF2].
  Qed.

  Theorem inf_loop_sim : loop_stmt.
  Proof.
    intros v w R M C HE HP. rewrite inf_loop_mstep. rewrite iterZ_nat.
    apply (loop_sim_n _ v w R M C HE HP).
    pose proof (PHI_fuel _ _ _ _ w HP). pose proof (PHI_nonneg _ _ _ _ w HP). lia.
  Qed.
End Loop.
End FXG.
