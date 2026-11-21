(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (mprotect's vDSO test; the launch's input, mmap base and entry draw; the CONFIG_RSEQ value). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.pupnp.FuzzHttp.images Require Import AsanUbsan.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.ASN Require Import
  PropExec ShapeAlg SpinAlg AgentLib AsanAcct AsanAcctImages AxSymExec3 AxSymExec3Sound AxSymRun3
  AsanPlanCore AsanPlan AsanPlanSound AsanPlanSound2 BothPlanImages AsanInit
  AsanNodesIface AsanNodesMmA AsanNodesMmB SumsBothClose AsanNodesStartX AsanNodesStartXBoth AsanMaxVA AsanNodesMaxVA AsanNodesWJoin.

Unset Lia Cache.
Import ListNotations.
Import AX2. Import AX2S. Import AP. Import APS.
Open Scope Z_scope.

Definition XN0 (id : nat) (args : list expr) (cs : acs) : option acs := None.
Definition XE0 (id : nat) (args : list expr) (cs : acs) : option (Z * list spiece * acs) := None.
Definition XB0 (id : nat) (args : list expr) (cs : acs) : option (acs * acs) := None.

Lemma XN0_sound : forall SEGS A nx0 LIMIT SINV argH FS0, ext_stmt SEGS A nx0 LIMIT XN0 SINV argH FS0.
Proof. intros ? ? ? ? ? ? ?. intros id args cs cs' E R FULL model T _ _ H. discriminate H. Qed.
Lemma XE0_sound : forall SEGS A nx0 LIMIT SINV argH FS0, emit_stmt SEGS A nx0 LIMIT XE0 SINV argH FS0.
Proof. intros ? ? ? ? ? ? ?. intros id args cs fd ps cs' E R FULL model T _ H _. discriminate H. Qed.
Lemma XB0_sound : forall SEGS A nx0 LIMIT SINV argH FS0, ext2_stmt SEGS A nx0 LIMIT XB0 SINV argH FS0.
Proof. intros ? ? ? ? ? ? ?. intros id args cs csa csb E R FULL model TA TB _ H. discriminate H. Qed.

Lemma both_maxva_code : forall i, (i < 45)%nat ->
  fetch_word BSEGS (Z_to_bv 64 (x_maxva BOTH + 4 * Z.of_nat i)) = Some (nth i MAXVA_WORDS W0).
Proof.
  intros i Hi. cbn [x_maxva BOTH].
  do 45 (destruct i as [|i];
    [cbn [Z.of_nat Pos.of_succ_nat Pos.succ Z.mul Z.add Pos.mul Pos.add nth MAXVA_WORDS];
     lazymatch goal with |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true) end |]).
  exfalso. lia.
Qed.

Lemma both_maxva_range : 0 < x_maxva BOTH /\ x_maxva BOTH + 180 < 2 ^ 64.
Proof. cbn [x_maxva BOTH]. lia. Qed.

Section XAll.
  Variable apc : N.
  Variable sp : word.
  Variable rdraw : EntryDraw.
  Variable brk0 mbase : word.
  Variable inp : ProcInput.
  Variable FS0 : Fs.Fs.
  Hypothesis HL : launch_ok BSEGS BOTH BPH apc sp rdraw brk0 mbase inp.
  Variable SINV : env -> (word -> option byte) -> Prop.
  Hypothesis SINV_SINV0 : forall E M, SINV E M -> SINV0 BPH apc sp rdraw brk0 mbase inp E M.
  Hypothesis SINV_frame : forall E M M', (forall a, argH0 sp rdraw inp E a = true -> M' a = M a) -> SINV E M -> SINV E M'.

  Variable nx0 : nat.
  Hypothesis Hnx0 : (NX0 <= nx0)%nat.
  Hypothesis SINV_agree : forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M.

  (* every start-up extension node, at the run's own CONFIG_RSEQ flag *)
  Theorem both_node_x_sound_all : forall x,
    x_stmt BSEGS BOTH nx0 AsanInit.LIMIT (rseq_z (kb_rseq (in_kernel inp))) SINV (argH0 sp rdraw inp) FS0 x.
  Proof using All.
    pose proof (argH0_high_l BSEGS BOTH BPH apc sp rdraw brk0 mbase inp HL) as AH.
    assert (AA : forall E E' (a : word), env_agree nx0 E E' -> argH0 sp rdraw inp E a = argH0 sp rdraw inp E' a).
    { intros E E' a [Hag Hb]. apply (argH0_agree sp rdraw inp). split; [|exact Hb]. intros n Hn. apply Hag. lia. }
    set (rz := rseq_z (kb_rseq (in_kernel inp))).
    intros [ | | | | | | | | | | ].
    - apply (both_node_x_sound_XIMemset nx0 AsanInit.LIMIT rz SINV _ AH AA SINV_frame SINV_agree FS0).
    - apply (both_node_x_sound_XIMemcpy nx0 AsanInit.LIMIT rz SINV _ AH AA SINV_frame SINV_agree FS0).
    - apply (both_node_x_sound_XMemset nx0 AsanInit.LIMIT rz SINV _ AH AA SINV_frame SINV_agree FS0).
    - apply (both_node_x_sound_XMemcpy nx0 AsanInit.LIMIT rz SINV _ AH AA SINV_frame SINV_agree FS0).
    - apply (both_node_x_sound_XMemIsZero nx0 AsanInit.LIMIT rz SINV _ AH AA SINV_frame SINV_agree FS0).
    - apply (node_x_sound_XEnvScan_asan_gen apc sp rdraw brk0 mbase inp FS0 HL SINV SINV_SINV0 SINV_frame nx0 Hnx0 SINV_agree).
    - apply (node_x_sound_XPnScan_asan_gen apc sp rdraw brk0 mbase inp FS0 HL SINV SINV_SINV0 SINV_frame nx0 Hnx0 SINV_agree).
    - apply x_sound_layout.
    - apply (both_node_x_sound_XIStrncpy nx0 AsanInit.LIMIT rz SINV _ AH AA SINV_frame SINV_agree FS0).
    - apply (both_node_x_sound_XPopFree nx0 AsanInit.LIMIT rz SINV _ AH AA SINV_frame SINV_agree FS0).
    - apply (x_sound_maxva BSEGS BOTH nx0 AsanInit.LIMIT rz SINV _ FS0 both_wx both_in_hull both_hull_ok SINV_frame both_maxva_range both_maxva_code).
  Qed.
End XAll.
