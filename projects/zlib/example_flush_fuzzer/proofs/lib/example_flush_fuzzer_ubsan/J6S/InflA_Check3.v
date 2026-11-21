(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare StepTac.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1 Require Import SymEx2Expr SymEx2 SymEx2Tac MemRel SymAux RomRead.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import Prog ZIface InflateState InflateFast InflateArms Inflate
     InflateInv InflateInvKit InflateInvRun AdlerModel ZChecksum ZChkAdl.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.D6S Require Import Segs6 Callee6.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S Require Import ISLayout IS6 InflMem InflRod6 InflCtx6 InflArmLib6 InflArmLib6b InflArmLib6c
     InflNeed6 InflA_Check1 InflA_Check2.
Import ListNotations.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.

Lemma arm_CHECK_leave : forall s c r w1,
  (is_wrap s = 5 \/ is_wrap s = 1) -> NEEDBITS 32 (mkW s c r) = ALeave w1 -> arm_CHECK (mkW s c r) = ALeave w1.
Proof.
  intros s c r w1 Hw HN. unfold arm_CHECK. mstep1 (@gs_eq inflate_state). rewrite (wrap15_eqb0 _ Hw). change (negb false) with true. cbv iota.
  rewrite abind_run. rewrite abind_run, HN. reflexivity.
Qed.

Lemma sr_total : forall s, SRNGq s -> 0 <= is_total s < 2 ^ 64.
Proof. intros s H. do 7 (destruct H as [_ H]). destruct H as [H _]. exact H. Qed.

Section ArmCHECK.
  Variable ROM : (word -> option byte) -> Prop.
  Hypothesis ROMok : forall M, rod6_clear M -> ROM M.
  Hypothesis ADLER : adler32_run6 ROM.

  Theorem arm_CHECK_sim : arm_stmt CHECK.
  Proof.
    intros v w R M C Hmode HE HP. destruct w as [s c r]. cbn [w_s] in Hmode.
    rewrite dispatch_eq. cbn [w_s]. rewrite Hmode. change (arm_for ivar_ref (cv_flush v) CHECK) with arm_CHECK.
    destruct HE as (HM & HRC & HX & (HF & HV & G8)).
    arm_begin C HM HRC HX HF HV HP.
    assert (Hf : is_flags s = 0) by (destruct Xflags as [X0 | (_ & XM & _)]; [exact X0 | exfalso; rewrite Hmode in XM; destruct XM as [E|E]; cbv in E; discriminate]).
    pose proof (sr_total s SR) as Htot.
    pose proof (check_need v C s c r R M Xwrap HM HRC HF HV RI CI) as HN.
    destruct (NEEDBITS 32 (mkW s c r)) as [[] w1 | w1 | rc w1] eqn:EN; [| | destruct HN].
    - destruct HN as (r1 & R1 & -> & Hms1 & HJE & RI1 & S5 & Hb32).
      destruct S5 as (Q1 & Q2 & Q3 & Q4 & Q5).
      assert (Ho : 0 <= ir_out r1 - ir_left r1 < 2 ^ 32) by (pose proof RI1 as X; unfold RINV in X; clear - X CP0; lia).
      assert (HM1 : LMEM v (mkW s c r1) M) by (apply (LMEM_regs v s c r c r1 M HM); first [exact Q1 | exact Q4 | reflexivity]).
      assert (HRC1 : RETC v (mkW s c r1) M) by (eapply RETC_regs; [exact HRC | exact Q5]).
      assert (HX1 : LX v (mkW s c r1)).
      { apply (LX_step v s c r s c r1 HX); try reflexivity; [exact Xlive | left; exact Hf | exact Q3 | rewrite Q5; exact Xret | exact Xmsg]. }
      destruct Xwrap as [Hw5 | Hw1].
      +
        assert (Hcan : adler_canon (is_check s)).
        { apply ck_adl_canon. destruct PC as (CK & _). unfold cks in CK. cbn [w_s w_c w_r] in CK. rewrite Hmode, Hw5, Hf in CK. apply CK; [cbv; split; discriminate | cbv; discriminate | reflexivity]. }
        rewrite (arm_CHECK_run s c r c r1 Hw5 Hf EN Ho). rewrite Hw5 in HJE.
        destruct (check_B_sim v C ROM ROMok ADLER s c r1 R1 M Hmode Hw5 Hf Hcan Htot (conj (proj1 Cto) (proj2 Cto)) HM1 HRC1 HX1 HJE RI1 CI Hb32) as (R' & M' & pc' & Hms2 & HPOST).
        exists R', M', pc'. split; [eapply msteps_trans; [exact Hms1 | exact Hms2]|].
        apply (arm_post_rebase v s c r c r1); [symmetry; exact Q1 | exact HPOST].
      +
        rewrite (arm_CHECK_run1 s c r c r1 Hw1 Hf EN Ho). rewrite Hw1 in HJE.
        destruct (check_B1_sim v C s c r1 R1 M Hmode Hw1 Hf Htot (conj (proj1 Cto) (proj2 Cto)) HM1 HRC1 HX1 HJE RI1 CI Hb32) as (R' & M' & pc' & Hms2 & HPOST).
        exists R', M', pc'. split; [eapply msteps_trans; [exact Hms1 | exact Hms2]|].
        apply (arm_post_rebase v s c r c r1); [symmetry; exact Q1 | exact HPOST].
    - destruct HN as (r1 & R1 & -> & Hms1 & HL1 & RI1 & S5).
      destruct S5 as (Q1 & Q2 & Q3 & Q4 & Q5).
      rewrite (arm_CHECK_leave s c r _ Xwrap EN).
      exists R1, M, pc6_leave. split; [exact Hms1|].
      cbn [arm_post w_r]. split; [reflexivity|]. rewrite Q1. split; [| apply MFRAME_refl].
      split; [apply (LMEM_regs v s c r c r1 M HM); first [exact Q1 | exact Q4 | reflexivity]|].
      split; [| split; [apply same_blocks_refl | exact HL1]].
      apply (LX_step v s c r s c r1 HX); try reflexivity; [exact Xlive | left; exact Hf | exact Q3 | rewrite Q5; exact Xret | exact Xmsg].
  Qed.
End ArmCHECK.
End FXG.
