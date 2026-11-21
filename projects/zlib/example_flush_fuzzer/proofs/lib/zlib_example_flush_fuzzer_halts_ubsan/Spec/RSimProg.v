(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import String.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.Lib Require Import PropExec MState ITree Nodes Decode.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.Spec Require Import Prelim Monad MSafe MPaths STree Stdio Adapter Driver StepB EquivShared EquivProg RSim MI_Inv LB_Inv LB_Sum SizeHist FreshIface HarnessC.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.Spec Require TargetSafeC.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan Require Import ExFlushIface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.Common Require Import Keeps.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.Lib Require Import CTree.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.Spec Require Import CMonad CRSim.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.Spec Require AdapterC DriverC.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Local Notation M := Monad.M.
Ltac splits := repeat (lazymatch goal with |- _ /\ _ => split | |- _ => fail end).

Definition io_node (n : node) : Prop :=
  match n with
  | NWrite _ _ | NWritev _ _ | NOpen _ | NRead _ _ _ | NClose _ | NIoctl _ _ | NSetTid | NExit _ => True
  | _ => False
  end.


Definition REQMAX : Z := 2^29 - 2^16.

Section Prog.
Context {S1 S2 : Type}.
Variables (step1 step2 : node -> Model -> resp -> Model -> list event -> Prop).
Variables (Phi1 Phi2 : node -> Model -> Prop).
Hypothesis sub1 : forall n mo r mo' e, ~ nf_node n -> step1 n mo r mo' e -> nstep n mo r mo' e.
Hypothesis same1 : forall n mo r e, ~ nf_node n -> nstep n mo r mo e -> step1 n mo r mo e.
Hypothesis io1 : forall n mo r mo' e, io_node n -> nstep n mo r mo' e -> step1 n mo r mo' e.
Hypothesis sub2 : forall n mo r mo' e, ~ nf_node n -> step2 n mo r mo' e -> nstep n mo r mo' e.
Hypothesis same2 : forall n mo r e, ~ nf_node n -> nstep n mo r mo e -> step2 n mo r mo e.
Hypothesis io2 : forall n mo r mo' e, io_node n -> nstep n mo r mo' e -> step2 n mo r mo' e.

Local Notation rel := (rel S1 S2).
Local Notation rsim := (rsim step1 step2 nexit nexit Phi1 Phi2).
Local Notation STOT1 := (STOT step1 (fun R0 => texit (R:=R0) step1 nexit)).
Local Notation STOT2 := (STOT step2 (fun R0 => texit (R:=R0) step2 nexit)).


Definition rsimeq {A} (R : rel) (m1 : M S1 A) (m2 : M S2 A) (Q : A -> rel) : Prop :=
  rsim R m1 m2 (fun a b s1 mo1 s2 mo2 => a = b /\ Q a s1 mo1 s2 mo2).

Lemma rsimeq_bind {A B} (R : rel) (m1 : M S1 A) (m2 : M S2 A) (Q1 : A -> rel) (k1 : A -> M S1 B) (k2 : A -> M S2 B) Q :
  rsimeq R m1 m2 Q1 -> (forall a, rsimeq (Q1 a) (k1 a) (k2 a) Q) -> rsimeq R (mbind m1 k1) (mbind m2 k2) Q.
Proof. intros H1 H2. unfold rsimeq. eapply rsim_bind_eq; [exact H1| exact H2]. Qed.

Lemma rsimeq_bind_r {A B C} (R : rel) (m1 : M S1 A) (m2 : M S2 B) (Q1 : A -> B -> rel) (k1 : A -> M S1 C) (k2 : B -> M S2 C) Q :
  rsim R m1 m2 Q1 -> (forall a b, rsimeq (Q1 a b) (k1 a) (k2 b) Q) -> rsimeq R (mbind m1 k1) (mbind m2 k2) Q.
Proof. intros H1 H2. unfold rsimeq. eapply rsim_bind; [exact H1| exact H2]. Qed.

Lemma rsimeq_ret {A} (R : rel) (a : A) (Q : A -> rel) :
  (forall s1 mo1 s2 mo2, R s1 mo1 s2 mo2 -> Q a s1 mo1 s2 mo2) -> rsimeq R (mret a) (mret a) Q.
Proof. intros H. unfold rsimeq. apply rsim_ret. intros; split; [reflexivity| apply H; assumption]. Qed.

Lemma rsimeq_munr {A} (R : rel) (Q : A -> rel) : rsimeq R (munr (A:=A)) (munr (A:=A)) Q.
Proof. unfold rsimeq. apply rsim_munr. Qed.

Lemma rsimeq_conseq {A} (R R' : rel) (m1 : M S1 A) (m2 : M S2 A) (Q Q' : A -> rel) :
  rsimeq R m1 m2 Q -> (forall s1 mo1 s2 mo2, R' s1 mo1 s2 mo2 -> R s1 mo1 s2 mo2) ->
  (forall a s1 mo1 s2 mo2, Q a s1 mo1 s2 mo2 -> Q' a s1 mo1 s2 mo2) -> rsimeq R' m1 m2 Q'.
Proof. intros H HR HQ. unfold rsimeq in *. eapply rsim_conseq; [exact H| exact HR|]. intros a b s1 mo1 s2 mo2 [-> HQa]. auto. Qed.

Lemma rsimeq_pre {A} (R R' : rel) (m1 : M S1 A) (m2 : M S2 A) (Q : A -> rel) :
  rsimeq R m1 m2 Q -> (forall s1 mo1 s2 mo2, R' s1 mo1 s2 mo2 -> R s1 mo1 s2 mo2) -> rsimeq R' m1 m2 Q.
Proof. intros H HR. eapply rsimeq_conseq; eauto. Qed.

Lemma rsimeq_post {A} (R : rel) (m1 : M S1 A) (m2 : M S2 A) (Q Q' : A -> rel) :
  rsimeq R m1 m2 Q -> (forall a s1 mo1 s2 mo2, Q a s1 mo1 s2 mo2 -> Q' a s1 mo1 s2 mo2) -> rsimeq R m1 m2 Q'.
Proof. intros H HQ. eapply rsimeq_conseq; eauto. Qed.

Lemma rsimeq_seq {A B} (R R1 : rel) (m1 : M S1 A) (m2 : M S2 A) (k1 : A -> M S1 B) (k2 : A -> M S2 B) Q :
  rsimeq R m1 m2 (fun _ => R1) -> (forall a, rsimeq R1 (k1 a) (k2 a) Q) -> rsimeq R (mbind m1 k1) (mbind m2 k2) Q.
Proof. intros H1 H2. eapply rsimeq_bind; [exact H1| exact H2]. Qed.

Lemma rsimeq_seq_r {A B C} (R R1 : rel) (m1 : M S1 A) (m2 : M S2 B) (k1 : A -> M S1 C) (k2 : B -> M S2 C) Q :
  rsim R m1 m2 (fun _ _ => R1) -> (forall a b, rsimeq R1 (k1 a) (k2 b) Q) -> rsimeq R (mbind m1 k1) (mbind m2 k2) Q.
Proof. intros H1 H2. eapply rsimeq_bind_r; [exact H1| exact H2]. Qed.


Lemma rsimeq_if {A} (b : bool) (R : rel) (m1 m1' : M S1 A) (m2 m2' : M S2 A) Q :
  (b = true -> rsimeq R m1 m2 Q) -> (b = false -> rsimeq R m1' m2' Q) -> rsimeq R (if b then m1 else m1') (if b then m2 else m2') Q.
Proof. intros H1 H2. destruct b; auto. Qed.




Lemma rsimeq_exI {A X} (R : X -> rel) (m1 : M S1 A) (m2 : M S2 A) Q :
  (forall x, rsimeq (R x) m1 m2 Q) -> rsimeq (fun s1 mo1 s2 mo2 => exists x, R x s1 mo1 s2 mo2) m1 m2 Q.
Proof. intros H. unfold rsimeq. apply rsim_exI. exact H. Qed.

Local Notation crsim := (crsim step1 step2 nexit nexit Phi1 Phi2).

Definition crsimeq {A} (R : rel) (mc1 : MC S1 A) (mc2 : MC S2 A) (Q : A -> rel) : Prop :=
  crsim R mc1 mc2 (fun a b s1 mo1 s2 mo2 => a = b /\ Q a s1 mo1 s2 mo2).

Lemma crsimeq_lift {A} (R : rel) (m1 : M S1 A) (m2 : M S2 A) (Q : A -> rel) : rsimeq R m1 m2 Q -> crsimeq R (clift m1) (clift m2) Q.
Proof. intros H. unfold crsimeq. apply crsim_lift. exact H. Qed.

Lemma crsimeq_ret {A} (R : rel) (a : A) (Q : A -> rel) :
  (forall s1 mo1 s2 mo2, R s1 mo1 s2 mo2 -> Q a s1 mo1 s2 mo2) -> crsimeq R (cmret a) (cmret a) Q.
Proof. intros H. unfold crsimeq. apply crsim_ret. intros; split; [reflexivity| apply H; assumption]. Qed.

Lemma crsimeq_bind {A B} (R : rel) (m1 : MC S1 A) (m2 : MC S2 A) (Q1 : A -> rel) (k1 : A -> MC S1 B) (k2 : A -> MC S2 B) Q :
  crsimeq R m1 m2 Q1 -> (forall a, crsimeq (Q1 a) (k1 a) (k2 a) Q) -> crsimeq R (cmbind m1 k1) (cmbind m2 k2) Q.
Proof.
  intros H1 H2. unfold crsimeq in *. eapply crsim_bind; [exact H1|]. intros a b.
  apply (crsim_pure _ _ _ _ _ _ (Q1 a) (a = b)). intros <-. apply H2.
Qed.

Lemma crsimeq_bind_r {A B C} (R : rel) (m1 : MC S1 A) (m2 : MC S2 B) (Q1 : A -> B -> rel) (k1 : A -> MC S1 C) (k2 : B -> MC S2 C) Q :
  crsim R m1 m2 Q1 -> (forall a b, crsimeq (Q1 a b) (k1 a) (k2 b) Q) -> crsimeq R (cmbind m1 k1) (cmbind m2 k2) Q.
Proof. intros H1 H2. unfold crsimeq. eapply crsim_bind; [exact H1| exact H2]. Qed.

Lemma crsimeq_conseq {A} (R R' : rel) (m1 : MC S1 A) (m2 : MC S2 A) (Q Q' : A -> rel) :
  crsimeq R m1 m2 Q -> (forall s1 mo1 s2 mo2, R' s1 mo1 s2 mo2 -> R s1 mo1 s2 mo2) ->
  (forall a s1 mo1 s2 mo2, Q a s1 mo1 s2 mo2 -> Q' a s1 mo1 s2 mo2) -> crsimeq R' m1 m2 Q'.
Proof. intros H HR HQ. unfold crsimeq in *. eapply crsim_conseq; [exact H| exact HR|]. intros a b s1 mo1 s2 mo2 [-> HQa]. auto. Qed.


Lemma crsimeq_post {A} (R : rel) (m1 : MC S1 A) (m2 : MC S2 A) (Q Q' : A -> rel) :
  crsimeq R m1 m2 Q -> (forall a s1 mo1 s2 mo2, Q a s1 mo1 s2 mo2 -> Q' a s1 mo1 s2 mo2) -> crsimeq R m1 m2 Q'.
Proof. intros H HQ. eapply crsimeq_conseq; eauto. Qed.

Lemma crsimeq_seq {A B} (R R1 : rel) (m1 : MC S1 A) (m2 : MC S2 A) (k1 : A -> MC S1 B) (k2 : A -> MC S2 B) Q :
  crsimeq R m1 m2 (fun _ => R1) -> (forall a, crsimeq R1 (k1 a) (k2 a) Q) -> crsimeq R (cmbind m1 k1) (cmbind m2 k2) Q.
Proof. intros H1 H2. eapply crsimeq_bind; [exact H1| exact H2]. Qed.

Lemma crsimeq_seq_r {A B C} (R R1 : rel) (m1 : MC S1 A) (m2 : MC S2 B) (k1 : A -> MC S1 C) (k2 : B -> MC S2 C) Q :
  crsim R m1 m2 (fun _ _ => R1) -> (forall a b, crsimeq R1 (k1 a) (k2 b) Q) -> crsimeq R (cmbind m1 k1) (cmbind m2 k2) Q.
Proof. intros H1 H2. eapply crsimeq_bind_r; [exact H1| exact H2]. Qed.

Lemma crsimeq_if {A} (b : bool) (R : rel) (m1 m1' : MC S1 A) (m2 m2' : MC S2 A) Q :
  (b = true -> crsimeq R m1 m2 Q) -> (b = false -> crsimeq R m1' m2' Q) -> crsimeq R (if b then m1 else m1') (if b then m2 else m2') Q.
Proof. intros H1 H2. destruct b; auto. Qed.

Lemma crsimeq_false {A} (m1 : MC S1 A) (m2 : MC S2 A) Q : crsimeq (fun _ _ _ _ => False) m1 m2 Q.
Proof. unfold crsimeq. apply crsim_false. Qed.

Lemma crsimeq_exI {A X} (R : X -> rel) (m1 : MC S1 A) (m2 : MC S2 A) Q :
  (forall x, crsimeq (R x) m1 m2 Q) -> crsimeq (fun s1 mo1 s2 mo2 => exists x, R x s1 mo1 s2 mo2) m1 m2 Q.
Proof. intros H. unfold crsimeq. apply crsim_exI. exact H. Qed.

Lemma crsim_pure_r {A B} (R : rel) (phi : Prop) (m1 : MC S1 A) (m2 : MC S2 B) Q :
  (phi -> crsim R m1 m2 Q) -> crsim (fun s1 mo1 s2 mo2 => R s1 mo1 s2 mo2 /\ phi) m1 m2 Q.
Proof. intros H. eapply crsim_pre; [apply (crsim_pure _ _ _ _ _ _ R phi m1 m2 Q H)|]. intros ? ? ? ? [HR Hphi]. split; assumption. Qed.
Lemma crsimeq_pure_r {A} (R : rel) (phi : Prop) (m1 : MC S1 A) (m2 : MC S2 A) Q :
  (phi -> crsimeq R m1 m2 Q) -> crsimeq (fun s1 mo1 s2 mo2 => R s1 mo1 s2 mo2 /\ phi) m1 m2 Q.
Proof. intros H. unfold crsimeq. apply crsim_pure_r. exact H. Qed.


Lemma rsim_bind_get {A B} (R : rel) (k1 : S1 -> M S1 A) (k2 : S2 -> M S2 B) Q :
  (forall s1 mo1 s2 mo2, R s1 mo1 s2 mo2 ->
     rsim (fun s1' mo1' s2' mo2' => s1' = s1 /\ mo1' = mo1 /\ s2' = s2 /\ mo2' = mo2) (k1 s1) (k2 s2) Q) ->
  rsim R (mbind mget k1) (mbind mget k2) Q.
Proof.
  intros H. eapply rsim_bind; [apply rsim_get|]. intros a b. apply rsim_pointwise.
  intros s1 mo1 s2 mo2 (-> & -> & HR). eapply rsim_pre; [exact (H _ _ _ _ HR)|]. intros ? ? ? ? (-> & -> & -> & ->). auto.
Qed.




Lemma rsim_of_detio {A B} (R : rel) (m1 : M S1 A) (m2 : M S2 B) (Q : A -> B -> rel) :
  (forall s1 mo1 s2 mo2, R s1 mo1 s2 mo2 ->
     exists PG PC, detio (stp:=step1) (m1 s1) mo1 PG /\ detio (stp:=step2) (m2 s2) mo2 PC /\
       forall trG a s1' trC b s2', PG trG a s1' -> PC trC b s2' -> trG = trC /\ Q a b s1' mo1 s2' mo2) ->
  rsim R m1 m2 Q.
Proof.
  intros H. split.
  - intros s1 mo1 s2 mo2 HR _ _.
    destruct (H _ _ _ _ HR) as (PG & PC & (trG & a & s1' & HpG & HPG & HuG & HxG) & (trC & b & s2' & HpC & HPC & HuC & HxC) & HQ).
    destruct (HQ _ _ _ _ _ _ HPG HPC) as [<- HQ']. split.
    + intros tr r1 mo1' Hp. destruct (HuG _ _ _ Hp) as (-> & -> & ->). exists (Ok (b, s2')), mo2. split; [exact HpC| exact HQ'].
    + intros tr Hx. destruct (HxG _ Hx).
  - intros s2 mo2 s1 mo1 HR _ _.
    destruct (H _ _ _ _ HR) as (PG & PC & (trG & a & s1' & HpG & HPG & HuG & HxG) & (trC & b & s2' & HpC & HPC & HuC & HxC) & HQ).
    destruct (HQ _ _ _ _ _ _ HPG HPC) as [<- HQ']. split.
    + intros tr r2 mo2' Hp. destruct (HuC _ _ _ Hp) as (-> & -> & ->). exists (Ok (a, s1')), mo1. split; [exact HpG| exact HQ'].
    + intros tr Hx. destruct (HxC _ Hx).
Qed.


Section Stdio.
Variables (get1 : S1 -> stdout_st) (set1 : stdout_st -> S1 -> S1).
Variables (get2 : S2 -> stdout_st) (set2 : stdout_st -> S2 -> S2).
Hypothesis get_set1 : forall v s, get1 (set1 v s) = v.
Hypothesis set_set1 : forall v w s, set1 v (set1 w s) = set1 v s.
Hypothesis set_get1 : forall s, set1 (get1 s) s = s.
Hypothesis get_set2 : forall v s, get2 (set2 v s) = v.
Hypothesis set_set2 : forall v w s, set2 v (set2 w s) = set2 v s.
Hypothesis set_get2 : forall s, set2 (get2 s) s = s.
Variable R : rel.
Hypothesis HRget : forall s1 mo1 s2 mo2, R s1 mo1 s2 mo2 -> get1 s1 = get2 s2.
Hypothesis HRset : forall s1 mo1 s2 mo2 v, R s1 mo1 s2 mo2 -> R (set1 v s1) mo1 (set2 v s2) mo2.

Local Ltac ret_same := apply rsimeq_ret; intros ? ? ? ? HH; exact HH.

Lemma rd_so_sim : rsimeq R (rd_so get1) (rd_so get2) (fun _ => R).
Proof.
  unfold Stdio.rd_so, rsimeq. eapply rsim_bind; [apply rsim_get|]. intros a b. cbn beta.
  apply rsim_ret. intros s1 mo1 s2 mo2 (-> & -> & HR). split; [apply (HRget _ _ _ _ HR)| exact HR].
Qed.

Lemma upd_so_sim : forall f, rsimeq R (upd_so get1 set1 f) (upd_so get2 set2 f) (fun _ => R).
Proof.
  intros f. unfold Stdio.upd_so, rsimeq. apply rsim_upd. intros s1 mo1 s2 mo2 HR.
  split; [reflexivity|]. rewrite (HRget _ _ _ _ HR). apply HRset. exact HR.
Qed.

Lemma stdio_write_sim : forall fd buf s, rsimeq R (stdio_write fd buf s) (stdio_write fd buf s) (fun _ => R).
Proof.
  intros fd buf s. destruct (Z.ltb_spec WRITE_MAX (zlength buf + zlength s)) as [Hbig|Hok].
  - unfold stdio_write. replace (WRITE_MAX <? zlength buf + zlength s) with true by (symmetry; apply Z.ltb_lt; exact Hbig). apply rsimeq_munr.
  - unfold rsimeq. apply rsim_of_detio. intros s1 mo1 s2 mo2 HR.
    eexists _, _. split; [apply (stdio_write_det sub1 same1); exact Hok|]. split; [apply (stdio_write_det sub2 same2); exact Hok|].
    intros trG [] s1' trC [] s2' [-> ->] [-> ->]. auto.
Qed.

Lemma stdout_stdio_write_sim : forall s, rsimeq R (stdout_stdio_write get1 set1 s) (stdout_stdio_write get2 set2 s) (fun _ => R).
Proof.
  intros s. unfold stdout_stdio_write.
  eapply rsimeq_bind; [apply rd_so_sim|]. intros so.
  eapply rsimeq_seq; [apply stdio_write_sim|]. intros _. apply upd_so_sim.
Qed.

Lemma ioctl_sim : rsimeq R (msys (NIoctl 1 TIOCGWINSZ) dec_ioctl) (msys (NIoctl 1 TIOCGWINSZ) dec_ioctl) (fun _ => R).
Proof.
  unfold rsimeq. apply rsim_node. intros s1 mo1 s2 mo2 HR _ _. splits.
  - intros rsp1 mo1' evs Hst. apply sub1 in Hst; [|cbn; tauto]. destruct Hst as (-> & -> & ->).
    exists (efferr ENOTTY), mo2. split; [apply io2; [exact I| cbn; auto]|]. destruct (dec_ioctl (efferr ENOTTY)); auto.
  - intros rsp2 mo2' evs Hst. apply sub2 in Hst; [|cbn; tauto]. destruct Hst as (-> & -> & ->).
    exists (efferr ENOTTY), mo1. split; [apply io1; [exact I| cbn; auto]|]. destruct (dec_ioctl (efferr ENOTTY)); auto.
  - intros code mo1' Hx. destruct Hx.
  - intros code mo2' Hx. destruct Hx.
Qed.

Lemma stdout_writefn_sim : forall s, rsimeq R (stdout_writefn get1 set1 s) (stdout_writefn get2 set2 s) (fun _ => R).
Proof.
  intros s. unfold stdout_writefn.
  eapply rsimeq_bind; [apply rd_so_sim|]. intros so.
  eapply rsimeq_seq.
  - apply rsimeq_if; intros _; [|ret_same].
    eapply rsimeq_seq; [apply upd_so_sim|]. intros _.
    eapply rsimeq_bind; [apply ioctl_sim|]. intros [e|v]; [apply upd_so_sim| apply rsimeq_munr].
  - intros _. apply stdout_stdio_write_sim.
Qed.

Lemma stdout_towrite_sim : rsimeq R (stdout_towrite get1 set1) (stdout_towrite get2 set2) (fun _ => R).
Proof. unfold stdout_towrite. apply upd_so_sim. Qed.

Lemma stdout_fwritex_sim : forall s, rsimeq R (stdout_fwritex get1 set1 s) (stdout_fwritex get2 set2 s) (fun _ => R).
Proof.
  intros s. unfold stdout_fwritex.
  eapply rsimeq_seq; [apply stdout_towrite_sim|]. intros _.
  eapply rsimeq_bind; [apply rd_so_sim|]. intros so.
  apply rsimeq_if; intros _; [apply stdout_writefn_sim|].
  apply rsimeq_if; intros _; [|apply upd_so_sim].
  eapply rsimeq_seq; [apply rsimeq_if; intros _; [apply stdout_writefn_sim| ret_same]|]. intros _. apply upd_so_sim.
Qed.

Lemma out_pieces_sim : forall ps, rsimeq R (out_pieces get1 set1 ps) (out_pieces get2 set2 ps) (fun _ => R).
Proof.
  induction ps as [|p ps IH]; cbn [out_pieces]; [ret_same|].
  eapply rsimeq_seq; [apply stdout_fwritex_sim|]. intros _. apply IH.
Qed.

Lemma stdout_vprintf_sim : forall ps, rsimeq R (stdout_vprintf get1 set1 ps) (stdout_vprintf get2 set2 ps) (fun _ => R).
Proof. intros ps. unfold stdout_vprintf. eapply rsimeq_seq; [apply stdout_towrite_sim|]. intros _. apply out_pieces_sim. Qed.

Lemma stdout_exit_flush_sim : rsimeq R (stdout_exit_flush get1 set1) (stdout_exit_flush get2 set2) (fun _ => R).
Proof.
  unfold stdout_exit_flush. eapply rsimeq_bind; [apply rd_so_sim|]. intros so.
  apply rsimeq_if; intros _; [apply stdout_writefn_sim| ret_same].
Qed.

Lemma stderr_pieces_sim : forall ps buf, rsimeq R (stderr_pieces (St:=S1) buf ps) (stderr_pieces (St:=S2) buf ps) (fun _ => R).
Proof.
  induction ps as [|p ps IH]; intros buf; cbn [stderr_pieces]; [ret_same|].
  apply rsimeq_if; intros _; [|apply IH].
  eapply rsimeq_seq; [apply stdio_write_sim|]. intros _. apply IH.
Qed.

Lemma stderr_fprintf_sim : forall ps, rsimeq R (stderr_fprintf (St:=S1) ps) (stderr_fprintf (St:=S2) ps) (fun _ => R).
Proof. intros ps. unfold stderr_fprintf. eapply rsimeq_bind; [apply stderr_pieces_sim|]. intros buf. apply stdio_write_sim. Qed.

Lemma stderr_fwrite_sim : forall s, rsimeq R (stderr_fwrite (St:=S1) s) (stderr_fwrite (St:=S2) s) (fun _ => R).
Proof. intros s. unfold stderr_fwrite. apply rsimeq_if; intros _; [apply stdio_write_sim| ret_same]. Qed.

Lemma s_diag_sim : forall d, rsimeq R (s_diag d) (s_diag d) (fun _ => R).
Proof. intros d. destruct d; cbn [s_diag]; first [apply stderr_fprintf_sim | apply stderr_fwrite_sim]. Qed.

Lemma s_emit_sim : forall v, rsimeq R (s_emit get1 set1 v) (s_emit get2 set2 v) (fun _ => R).
Proof. intros v. unfold s_emit. apply stdout_vprintf_sim. Qed.

End Stdio.


Section FdNodes.
Variables (MI1 MI2 : Model -> Prop).
Hypothesis MI1_pres : forall n mo rsp mo' evs, nstep n mo rsp mo' evs -> io_node n -> MI1 mo -> m_halted mo = None -> MI1 mo' /\ m_halted mo' = None.
Hypothesis MI2_pres : forall n mo rsp mo' evs, nstep n mo rsp mo' evs -> io_node n -> MI2 mo -> m_halted mo = None -> MI2 mo' /\ m_halted mo' = None.
Variable R : rel.
Hypothesis Rmodels : forall s1 mo1 s2 mo2, R s1 mo1 s2 mo2 ->
  MI1 mo1 /\ MI2 mo2 /\ m_halted mo1 = None /\ m_halted mo2 = None /\ m_fds mo1 = m_fds mo2 /\ m_fs mo1 = m_fs mo2.
Hypothesis Rtables : forall s1 mo1 s2 mo2 f, R s1 mo1 s2 mo2 ->
  MI1 (with_fds f mo1) -> MI2 (with_fds f mo2) -> m_halted (with_fds f mo1) = None -> m_halted (with_fds f mo2) = None ->
  R s1 (with_fds f mo1) s2 (with_fds f mo2).

Lemma open_sim : forall path,
  rsimeq R (msys (NOpen path) dec_open) (msys (NOpen path) dec_open) (fun _ => R).
Proof.
  intros path. unfold rsimeq. apply rsim_node. intros s1 mo1 s2 mo2 HR _ _. pose proof (Rmodels _ _ _ _ HR) as (Mi1 & Mi2 & Hh1 & Hh2 & Hfds & Hfs). splits.
  - intros rsp1 mo1' evs Hst. apply sub1 in Hst; [|cbn; tauto].
    destruct (nstep_open_xfer _ _ _ _ _ mo2 Hst Hfds Hfs) as [Hst2 E].
    pose proof (MI1_pres _ _ _ _ _ Hst I Mi1 Hh1) as [M1' Hh1']. pose proof (MI2_pres _ _ _ _ _ Hst2 I Mi2 Hh2) as [M2' Hh2'].
    exists rsp1, (with_fds (m_fds mo1') mo2). split; [apply io2; [exact I| exact Hst2]|].
    destruct (dec_open rsp1); [| exact I]. split; [reflexivity|]. rewrite E in M1', Hh1' |- *. apply Rtables; auto.
  - intros rsp2 mo2' evs Hst. apply sub2 in Hst; [|cbn; tauto].
    destruct (nstep_open_xfer _ _ _ _ _ mo1 Hst (eq_sym Hfds) (eq_sym Hfs)) as [Hst1 E].
    pose proof (MI2_pres _ _ _ _ _ Hst I Mi2 Hh2) as [M2' Hh2']. pose proof (MI1_pres _ _ _ _ _ Hst1 I Mi1 Hh1) as [M1' Hh1'].
    exists rsp2, (with_fds (m_fds mo2') mo1). split; [apply io1; [exact I| exact Hst1]|].
    destruct (dec_open rsp2); [| exact I]. split; [reflexivity|]. rewrite E in M2', Hh2' |- *. apply Rtables; auto.
  - intros code mo1' Hx. destruct Hx.
  - intros code mo2' Hx. destruct Hx.
Qed.

Lemma close_sim : forall fd,
  rsimeq R (msys (NClose fd) dec_close) (msys (NClose fd) dec_close) (fun _ => R).
Proof.
  intros fd. unfold rsimeq. apply rsim_node. intros s1 mo1 s2 mo2 HR _ _. pose proof (Rmodels _ _ _ _ HR) as (Mi1 & Mi2 & Hh1 & Hh2 & Hfds & Hfs). splits.
  - intros rsp1 mo1' evs Hst. apply sub1 in Hst; [|cbn; tauto].
    destruct (nstep_close_xfer _ _ _ _ _ mo2 Hst Hfds) as [Hst2 E].
    pose proof (MI1_pres _ _ _ _ _ Hst I Mi1 Hh1) as [M1' Hh1']. pose proof (MI2_pres _ _ _ _ _ Hst2 I Mi2 Hh2) as [M2' Hh2'].
    exists rsp1, (with_fds (m_fds mo1') mo2). split; [apply io2; [exact I| exact Hst2]|].
    destruct (dec_close rsp1); [| exact I]. split; [reflexivity|]. rewrite E in M1', Hh1' |- *. apply Rtables; auto.
  - intros rsp2 mo2' evs Hst. apply sub2 in Hst; [|cbn; tauto].
    destruct (nstep_close_xfer _ _ _ _ _ mo1 Hst (eq_sym Hfds)) as [Hst1 E].
    pose proof (MI2_pres _ _ _ _ _ Hst I Mi2 Hh2) as [M2' Hh2']. pose proof (MI1_pres _ _ _ _ _ Hst1 I Mi1 Hh1) as [M1' Hh1'].
    exists rsp2, (with_fds (m_fds mo2') mo1). split; [apply io1; [exact I| exact Hst1]|].
    destruct (dec_close rsp2); [| exact I]. split; [reflexivity|]. rewrite E in M2', Hh2' |- *. apply Rtables; auto.
  - intros code mo1' Hx. destruct Hx.
  - intros code mo2' Hx. destruct Hx.
Qed.

Lemma read_sim : forall fd buf1 buf2 cnt, 0 <= cnt < 2^64 ->
  rsimeq R (msys (NRead fd buf1 cnt) (dec_read buf1 cnt)) (msys (NRead fd buf2 cnt) (dec_read buf2 cnt))
         (fun a => match a with RdData bs => fun s1 mo1 s2 mo2 => R s1 mo1 s2 mo2 /\ zlength bs <= cnt | RdErr _ => R end).
Proof.
  intros fd buf1 buf2 cnt Hcnt. unfold rsimeq. apply rsim_node. intros s1 mo1 s2 mo2 HR _ _. pose proof (Rmodels _ _ _ _ HR) as (Mi1 & Mi2 & Hh1 & Hh2 & Hfds & Hfs).
  assert (LEN : forall bufX mo rsp mo' evs bs, nstep (NRead fd bufX cnt) mo rsp mo' evs -> dec_read bufX cnt rsp = Some (RdData bs) -> zlength bs <= cnt).
  { intros bufX mo rsp mo' evs bs Hst Hd.
    pose proof (nstep_dec_read fd bufX cnt _ _ _ _ Hcnt Hst) as (_ & a' & Hd' & Ha'). rewrite Hd in Hd'. injection Hd' as <-.
    destruct Ha' as (p & off & data & _ & _ & -> & _). unfold zlength. pose proof (length_file_read_le_count data off cnt Hcnt). lia. }
  splits.
  - intros rsp1 mo1' evs Hst. apply sub1 in Hst; [|cbn; tauto].
    destruct (nstep_read_xfer fd buf1 buf2 cnt _ _ _ _ mo2 Hst Hfds Hfs) as (rsp2 & Hst2 & E & Hd).
    pose proof (MI1_pres _ _ _ _ _ Hst I Mi1 Hh1) as [M1' Hh1']. pose proof (MI2_pres _ _ _ _ _ Hst2 I Mi2 Hh2) as [M2' Hh2'].
    exists rsp2, (with_fds (m_fds mo1') mo2). split; [apply io2; [exact I| exact Hst2]|]. rewrite Hd.
    destruct (dec_read buf1 cnt rsp1) as [[e|bs]|] eqn:Hd1; [| | exact I]; split; try reflexivity; rewrite E in M1', Hh1' |- *.
    + apply Rtables; auto.
    + split; [apply Rtables; auto| eapply LEN; [exact Hst| exact Hd1]].
  - intros rsp2 mo2' evs Hst. apply sub2 in Hst; [|cbn; tauto].
    destruct (nstep_read_xfer fd buf2 buf1 cnt _ _ _ _ mo1 Hst (eq_sym Hfds) (eq_sym Hfs)) as (rsp1 & Hst1 & E & Hd).
    pose proof (MI2_pres _ _ _ _ _ Hst I Mi2 Hh2) as [M2' Hh2']. pose proof (MI1_pres _ _ _ _ _ Hst1 I Mi1 Hh1) as [M1' Hh1'].
    exists rsp1, (with_fds (m_fds mo2') mo1). split; [apply io1; [exact I| exact Hst1]|]. rewrite Hd.
    destruct (dec_read buf2 cnt rsp2) as [[e|bs]|] eqn:Hd2; [| | exact I]; split; try reflexivity; rewrite E in M2', Hh2' |- *.
    + apply Rtables; auto.
    + split; [apply Rtables; auto| eapply LEN; [exact Hst| exact Hd2]].
  - intros code mo1' Hx. destruct Hx.
  - intros code mo2' Hx. destruct Hx.
Qed.

Lemma exit_node_sim : forall c (Q : Empty_set -> Empty_set -> rel),
  rsim R (msys (NExit c) dec_exit) (msys (NExit c) dec_exit) Q.
Proof.
  intros c Q. apply rsim_node. intros s1 mo1 s2 mo2 HR _ _. pose proof (Rmodels _ _ _ _ HR) as (_ & _ & _ & _ & _ & Hfs). splits.
  - intros rsp1 mo1' evs Hst. apply sub1 in Hst; [destruct Hst| cbn; tauto].
  - intros rsp2 mo2' evs Hst. apply sub2 in Hst; [destruct Hst| cbn; tauto].
  - intros code mo1' [Hc ->]. exists (with_halted code mo2). split; [split; [exact Hc| reflexivity]|]. rewrite !m_fs_with_halted. symmetry. exact Hfs.
  - intros code mo2' [Hc ->]. exists (with_halted code mo1). split; [split; [exact Hc| reflexivity]|]. rewrite !m_fs_with_halted. exact Hfs.
Qed.
End FdNodes.




Lemma rsim_pure_r {A B} (R : rel) (phi : Prop) (m1 : M S1 A) (m2 : M S2 B) Q :
  (phi -> rsim R m1 m2 Q) -> rsim (fun s1 mo1 s2 mo2 => R s1 mo1 s2 mo2 /\ phi) m1 m2 Q.
Proof. intros H. eapply rsim_pre; [apply (rsim_pure _ _ _ _ _ _ R phi m1 m2 Q H)|]. intros ? ? ? ? [HR Hphi]. split; assumption. Qed.
Lemma rsimeq_pure_r {A} (R : rel) (phi : Prop) (m1 : M S1 A) (m2 : M S2 A) Q :
  (phi -> rsimeq R m1 m2 Q) -> rsimeq (fun s1 mo1 s2 mo2 => R s1 mo1 s2 mo2 /\ phi) m1 m2 Q.
Proof. intros H. unfold rsimeq. apply rsim_pure_r. exact H. Qed.

Section Target.
Context {P1 P2 : Type}.
Variable FM : flush_model.
Variable RX : Z -> Z -> list (P1 * P2 * Z) -> rel.
Variables (QOV CMAX : Z).
Variables (malloc1 : Z -> M S1 (option P1)) (malloc2 : Z -> M S2 (option P2)).
Variables (free1 : P1 -> M S1 unit) (free2 : P2 -> M S2 unit).
Variables (fresh1 : S1 -> S1 -> P1 -> bool) (fresh2 : S2 -> S2 -> P2 -> bool).
Variables (emit1 : Z -> M S1 unit) (emit2 : Z -> M S2 unit).

Local Notation sizes := (map (@snd (P1 * P2) Z)).
Definition xsz (X : list (P1 * P2 * Z)) : list (unit * Z) := map (fun t => (tt, snd t)) X.
Lemma xsz_cons p q n X : xsz ((p, q, n) :: X) = (tt, n) :: xsz X. Proof. reflexivity. Qed.
Ltac cnt55x :=
  repeat match goal with x := _ : list _ |- _ => subst x end;
  rewrite ?xsz_cons; unfold TargetSafeC.ENTRY, C31, C40, C44 in *;
  repeat match goal with H : _ /\ _ |- _ => destruct H end;
  repeat (apply TargetSafeC.cntr_peel); lia.
Lemma xsz_app X Y : xsz (X ++ Y) = xsz X ++ xsz Y. Proof. apply map_app. Qed.

Definition Qm (C k : Z) (X : list (P1 * P2 * Z)) (n : Z) (s10 : S1) (s20 : S2) (r1 : option P1) (r2 : option P2) : rel :=
  match r1, r2 with
  | Some p, Some q => fun s1 mo1 s2 mo2 => RX (C + n + QOV) (k + 1) ((p, q, n) :: X) s1 mo1 s2 mo2 /\ n < 2^63
                                          /\ (KREQ n -> fresh1 s10 s1 p = true /\ fresh2 s20 s2 q = true)
  | _, _ => fun _ _ _ _ => False
  end.

Hypothesis Hm : forall C k X n s10 s20, 0 <= n <= REQMAX -> HISTOK (n :: sizes X) -> FPRE (xsz X) k n -> C + n + QOV <= CMAX ->
  rsim (fun s1 mo1 s2 mo2 => s1 = s10 /\ s2 = s20 /\ RX C k X s1 mo1 s2 mo2) (malloc1 n) (malloc2 n) (Qm C k X n s10 s20).
Hypothesis Hf : forall C k X p q n, rsim (RX C k ((p, q, n) :: X)) (free1 p) (free2 q) (fun _ _ => RX C k X).
Hypothesis Hemit : forall C k X v, rsimeq (RX C k X) (emit1 v) (emit2 v) (fun _ => RX C k X).
Hypothesis Hfpr : forall C k X ps, Forall (fun p => zlength p <= TargetSafeC.PIECE_MAX) ps ->
  rsimeq (RX C k X) (stderr_fprintf (St:=S1) ps) (stderr_fprintf (St:=S2) ps) (fun _ => RX C k X).
Hypothesis Hfwr : forall C k X bs, zlength bs <= TargetSafeC.PIECE_MAX ->
  rsimeq (RX C k X) (stderr_fwrite (St:=S1) bs) (stderr_fwrite (St:=S2) bs) (fun _ => RX C k X).
Hypothesis Hmono : forall C C' k k' X s1 mo1 s2 mo2, C <= C' -> k <= k' -> RX C k X s1 mo1 s2 mo2 -> RX C' k' X s1 mo1 s2 mo2.
Hypothesis Hperm : forall C k X Y s1 mo1 s2 mo2, Permutation X Y -> RX C k X s1 mo1 s2 mo2 -> RX C k Y s1 mo1 s2 mo2.
Hypothesis HQ0 : 0 <= QOV.

Local Ltac ret_same := apply rsimeq_ret; intros ? ? ? ? HH; exact HH.
Local Ltac ret_rel := apply rsim_ret; intros ? ? ? ? HH.

Definition zitemb (n : Z) : bool := (n =? 5968) || (n =? 65536) || (n =? 7176) || (n =? 32768).
Definition NI (X : list (P1 * P2 * Z)) : Z := Z.of_nat (length (List.filter (fun t => zitemb (snd t)) X)).
Definition NA (X : list (P1 * P2 * Z)) : Z := Z.of_nat (length (List.filter (fun t => negb (zitemb (snd t))) X)).

Lemma NI_cons p q n X : NI ((p, q, n) :: X) = (if zitemb n then 1 else 0) + NI X.
Proof. unfold NI. cbn [List.filter snd]. destruct (zitemb n); cbn [length]; rewrite ?Nat2Z.inj_succ; lia. Qed.
Lemma NA_cons p q n X : NA ((p, q, n) :: X) = (if zitemb n then 0 else 1) + NA X.
Proof. unfold NA. cbn [List.filter snd]. destruct (zitemb n); cbn [negb length]; rewrite ?Nat2Z.inj_succ; lia. Qed.
Lemma NI_app X Y : NI (X ++ Y) = NI X + NI Y. Proof. unfold NI. rewrite List.filter_app, length_app. lia. Qed.
Lemma NA_app X Y : NA (X ++ Y) = NA X + NA Y. Proof. unfold NA. rewrite List.filter_app, length_app. lia. Qed.
Lemma NI_le X : NI X <= Z.of_nat (length X).
Proof. unfold NI. induction X as [|t X IH]; [cbn; lia|]. cbn [List.filter length]. destruct (zitemb (snd t)); cbn [length]; rewrite ?Nat2Z.inj_succ; lia. Qed.
Lemma NA_le X : NA X <= Z.of_nat (length X).
Proof. unfold NA. induction X as [|t X IH]; [cbn; lia|]. cbn [List.filter length]. destruct (zitemb (snd t)); cbn [negb length]; rewrite ?Nat2Z.inj_succ; lia. Qed.

Lemma zitemb_item n : zitemb n = true -> itemsz n /\ 0 <= bcs n <= 16383 /\ (n =? 4) = false.
Proof.
  unfold zitemb. intros H. repeat (apply Bool.orb_true_iff in H as [H|H]); apply Z.eqb_eq in H; subst;
    (split; [right; match goal with |- context [?m = 4 * _] => exists (m / 4 - 1) end; cbn; lia| unfold bcs; cbn; split; [lia| reflexivity]]).
Qed.
Lemma filter_perm_split {A} (f : A -> bool) (l : list A) : Permutation l (List.filter f l ++ List.filter (fun x => negb (f x)) l).
Proof.
  induction l as [|x l IH]; cbn; [constructor|]. destruct (f x); cbn; [apply perm_skip; exact IH|].
  etransitivity; [apply perm_skip; exact IH| apply Permutation_middle].
Qed.
Lemma items_facts : forall L, Forall (fun z => zitemb z = true) L -> YWs L /\ 0 <= BCs L <= 16383 * Z.of_nat (length L) /\ N4s L = 0.
Proof.
  induction L as [|z L IH]; intros H.
  - cbn. unfold YWs, BCs, N4s. cbn. repeat split; try constructor; lia.
  - apply Forall_cons_iff in H as [Hz HL]. destruct (IH HL) as (A & B & C). destruct (zitemb_item z Hz) as (I1 & I2 & I3).
    cbn [length]. rewrite Nat2Z.inj_succ, BCs_cons, N4s_cons, I3. split; [constructor; assumption|]. lia.
Qed.

Lemma HISTOK_of : forall X n, NI X <= 16 -> (NA X <= 3 \/ (zitemb n = true /\ NA X <= 4)) -> HISTOK (n :: sizes X).
Proof.
  intros X n HNI HNA.
  set (I := List.filter zitemb (sizes X)). set (Z := List.filter (fun z => negb (zitemb z)) (sizes X)).
  assert (HP : Permutation (sizes X) (I ++ Z)) by apply filter_perm_split.
  assert (HI : Forall (fun z => zitemb z = true) I) by (subst I; apply Forall_forall; intros z Hz; apply List.filter_In in Hz; tauto).
  assert (LI : Z.of_nat (length I) = NI X). { subst I. unfold NI. clear. induction X as [|[[p q] m] X IH]; [reflexivity|]. cbn [map snd List.filter]. destruct (zitemb m); cbn [length]; rewrite ?Nat2Z.inj_succ; lia. }
  assert (LZ : Z.of_nat (length Z) = NA X). { subst Z. unfold NA. clear. induction X as [|[[p q] m] X IH]; [reflexivity|]. cbn [map snd List.filter]. destruct (zitemb m); cbn [negb length]; rewrite ?Nat2Z.inj_succ; lia. }
  destruct (items_facts I HI) as (YW & BC & N4).
  destruct HNA as [HZ3 | [Hn HZ4]].
  - apply (HISTOK_intro I (n :: Z)); [| exact YW| unfold HB; lia| rewrite N4; pose proof (N24s_nonneg I); lia| cbn; lia].
    etransitivity; [apply perm_skip; exact HP| apply Permutation_middle].
  - destruct (zitemb_item n Hn) as (I1 & I2 & I3).
    apply (HISTOK_intro (n :: I) Z); [cbn; apply perm_skip; exact HP| constructor; [exact I1| exact YW]| rewrite BCs_cons; unfold HB; lia
                                     | rewrite N4s_cons, I3, N4; pose proof (N24s_nonneg (n :: I)); lia| lia].
Qed.


Lemma malloc_sim0 : forall C k X n, 0 <= n <= REQMAX -> HISTOK (n :: sizes X) -> FPRE (xsz X) k n -> C + n + QOV <= CMAX ->
  rsim (RX C k X) (malloc1 n) (malloc2 n)
       (fun r1 r2 => match r1, r2 with
                     | Some p, Some q => fun s1 mo1 s2 mo2 => RX (C + n + QOV) (k + 1) ((p, q, n) :: X) s1 mo1 s2 mo2 /\ n < 2^63
                     | _, _ => fun _ _ _ _ => False
                     end).
Proof.
  intros C k X n Hn HK0 HF HC. apply rsim_pointwise. intros s10 mo10 s20 mo20 HR.
  eapply rsim_conseq; [apply (Hm C k X n s10 s20 Hn HK0 HF HC)| intros ? ? ? ? (-> & -> & -> & ->); auto|].
  intros [p|] [q|] ? ? ? ? HQ; cbn [Qm] in HQ |- *; try exact HQ. destruct HQ as (A & B & _). auto.
Qed.

Lemma creq_sim : forall C k X n, 0 <= n <= REQMAX -> HISTOK (n :: sizes X) -> FPRE (xsz X) k n -> C + n + QOV <= CMAX ->
  rsim (RX C k X) (creq malloc1 n) (creq malloc2 n) (fun p q => RX (C + n + QOV) (k + 1) ((p, q, n) :: X)).
Proof.
  intros C k X n Hn HK0 HF HC. unfold creq.
  apply rsim_pointwise. intros s10 mo10 s20 mo20 HR.
  eapply rsim_bind. { eapply rsim_pre; [apply (Hm C k X n s10 s20 Hn HK0 HF HC)|]. intros ? ? ? ? (-> & -> & -> & ->). auto. }
  intros [p|] [q|]; cbn [Qm]; [| apply rsim_false| apply rsim_false| apply rsim_false].
  ret_rel. exact (proj1 HH).
Qed.

Lemma zreq_sim : forall C k X n, 0 <= n <= REQMAX -> KREQ n -> HISTOK (n :: sizes X) -> FPRE (xsz X) k n -> C + n + QOV <= CMAX ->
  rsim (RX C k X) (zreq malloc1 fresh1 n) (zreq malloc2 fresh2 n) (fun p q => RX (C + n + QOV) (k + 1) ((p, q, n) :: X)).
Proof.
  intros C k X n Hn HK HK0 HF HC. unfold zreq.
  apply rsim_bind_get. intros s10 mo10 s20 mo20 HR0.
  eapply rsim_bind. { eapply rsim_pre; [apply (Hm C k X n s10 s20 Hn HK0 HF HC)|]. intros ? ? ? ? (-> & -> & -> & ->). auto. }
  intros [p|] [q|]; cbn [Qm]; [| apply rsim_false| apply rsim_false| apply rsim_false].
  apply rsim_bind_get. intros s1 mo1 s2 mo2 (HR1 & _ & HFr). destruct (HFr HK) as [E1 E2]. rewrite E1, E2.
  ret_rel. destruct HH as (-> & -> & -> & ->). exact HR1.
Qed.

Lemma diag_zerr_sim : forall C k X msg e, zlength msg <= TargetSafeC.PIECE_MAX ->
  rsimeq (RX C k X) (diag_zerr (St:=S1) msg e) (diag_zerr (St:=S2) msg e) (fun _ => RX C k X).
Proof. intros C k X msg e HM. unfold diag_zerr. apply Hfpr. apply TargetSafeC.pieces_zerr_short. exact HM. Qed.

Lemma inflate_end_sim : forall C k X LK1 p q (w : option P1) (v : option P2),
  match w, v with
  | Some w1, Some v1 => LK1 = [(w1, v1, 32768)] | None, None => LK1 = [] | _, _ => False
  end ->
  rsimeq (RX C k (LK1 ++ (p, q, 7176) :: X)) (inflate_end (St:=S1) free1 p w) (inflate_end (St:=S2) free2 q v) (fun _ => RX C k X).
Proof.
  intros C k X LK1 p q w v Hw. unfold inflate_end, rsimeq. destruct w as [w1|], v as [v1|]; try (exfalso; exact Hw); subst LK1; cbn [app].
  - eapply rsim_seq; [apply Hf|]. intros _ _. eapply rsim_post; [apply Hf|]. intros [] [] ? ? ? ? HR. split; [reflexivity| exact HR].
  - eapply rsim_post; [apply Hf|]. intros [] [] ? ? ? ? HR. split; [reflexivity| exact HR].
Qed.

Definition FC : Z := 2^21 + 766 + 2^20 + 308056 + 9 * QOV.   (* 1.4: 268112 + 39944 (the two state sizes grew by 16 each) *)
Lemma FC_nonneg : 0 <= FC. Proof. unfold FC. lia. Qed.
Definition HENTRY (X0 : list (P1 * P2 * Z)) (k : Z) : Prop := TargetSafeC.ENTRY (xsz X0) k /\ NA X0 <= 2 /\ NI X0 <= 8.

Lemma zit_5968 : zitemb 5968 = true. Proof. reflexivity. Qed.
Lemma zit_65536 : zitemb 65536 = true. Proof. reflexivity. Qed.
Lemma zit_7176 : zitemb 7176 = true. Proof. reflexivity. Qed.
Lemma zit_32768 : zitemb 32768 = true. Proof. reflexivity. Qed.

Lemma flush_tail_sim : forall C k X (b : bool) (v1 v2 : Z),
  rsimeq (RX C k X) (if b then diag_zerr (St:=S1) MSG_DEFLATEEND ZE_DATA_ERROR ;;; mret v1 else mret v2)
                    (if b then diag_zerr (St:=S2) MSG_DEFLATEEND ZE_DATA_ERROR ;;; mret v1 else mret v2) (fun _ => RX C k X).
Proof.
  intros C k X b v1 v2. apply rsimeq_if; intros _; [| ret_same].
  eapply rsimeq_seq; [apply diag_zerr_sim; apply TargetSafeC.msg_deflateEnd_short|]. intros _. ret_same.
Qed.

Lemma test_flush_sim : forall C k X0 cp1 cp2 cb up1 up2 n d,
  HENTRY X0 k -> 0 <= n <= 2^20 -> n <= cb <= 2^21 + 766 -> C + 268112 + 5 * QOV <= CMAX ->   (* 1.4: 5968 + 4 * 65536 *)
  rsimeq (RX C (k + 2) ((up1, up2, n) :: (cp1, cp2, cb) :: X0))
         (test_flush_m FM malloc1 free1 fresh1 d n) (test_flush_m FM malloc2 free2 fresh2 d n)
         (fun _ => RX (C + 268112 + 5 * QOV) (k + 7) ((up1, up2, n) :: (cp1, cp2, cb) :: X0)).
Proof.
  intros C k X0 cp1 cp2 cb up1 up2 n d (HE & HA & HI) Hn Hcb HC. pose proof HE as (_ & _ & _ & K). unfold test_flush_m, DSTATE_N, DBLK_N.
  set (X := (up1, up2, n) :: (cp1, cp2, cb) :: X0).
  assert (NAX : NA X <= 4) by (unfold X; rewrite !NA_cons; destruct (zitemb n); destruct (zitemb cb); lia).
  assert (NIX : NI X <= 10) by (unfold X; rewrite !NI_cons; destruct (zitemb n); destruct (zitemb cb); lia).
  Local Ltac zr HFP := apply zreq_sim; [unfold REQMAX; lia| unfold KREQ; lia| apply HISTOK_of; [| right; split; [reflexivity|]]; try lia| exact HFP| lia].
  unfold rsimeq.
  eapply rsim_bind. { zr (TargetSafeC.live_at_s (xsz X0) k tt cb tt n 0 HE ltac:(lia)) || (replace (k + 2) with (k + 2 + 0) by lia; zr (TargetSafeC.live_at_s (xsz X0) k tt cb tt n 0 HE ltac:(lia))). }
  intros s1 s2. cbv beta.
  eapply rsim_bind. { zr (TargetSafeC.live_at_dblk ((tt, 5968) :: xsz X) (k + 2 + 0 + 1) ltac:(lia) ltac:(cnt55x)); rewrite ?NI_cons, ?NA_cons, ?zit_5968; lia. }
  intros w1 w2. cbv beta.
  eapply rsim_bind. { zr (TargetSafeC.live_at_dblk ((tt, 65536) :: (tt, 5968) :: xsz X) (k + 2 + 0 + 1 + 1) ltac:(lia) ltac:(cnt55x)); rewrite ?NI_cons, ?NA_cons, ?zit_5968, ?zit_65536; lia. }
  intros pv1 pv2. cbv beta.
  eapply rsim_bind. { zr (TargetSafeC.live_at_dblk ((tt, 65536) :: (tt, 65536) :: (tt, 5968) :: xsz X) (k + 2 + 0 + 1 + 1 + 1) ltac:(lia) ltac:(cnt55x)); rewrite ?NI_cons, ?NA_cons, ?zit_5968, ?zit_65536; lia. }
  intros hd1 hd2. cbv beta.
  eapply rsim_bind. { zr (TargetSafeC.live_at_dblk ((tt, 65536) :: (tt, 65536) :: (tt, 65536) :: (tt, 5968) :: xsz X) (k + 2 + 0 + 1 + 1 + 1 + 1) ltac:(lia) ltac:(cnt55x)); rewrite ?NI_cons, ?NA_cons, ?zit_5968, ?zit_65536; lia. }
  intros pb1 pb2. cbv beta.
  eapply rsim_seq; [apply Hf|]. intros _ _. eapply rsim_seq; [apply Hf|]. intros _ _.
  eapply rsim_seq; [apply Hf|]. intros _ _. eapply rsim_seq; [apply Hf|]. intros _ _.
  eapply rsim_seq; [apply Hf|]. intros _ _.
  eapply rsim_post; [apply flush_tail_sim|]. intros ? ? ? ? ? ? [-> HR]. split; [reflexivity|]. eapply Hmono; [| | exact HR]; lia.
Qed.

Definition leak3 (LK : list (P1 * P2 * Z)) : Prop :=
  LK = [] \/ (exists p q, LK = [(p, q, 7176)]) \/ (exists p q w v, LK = [(w, v, 32768); (p, q, 7176)]).

Lemma leak3_facts LK : leak3 LK -> TargetSafeC.leak_shape (xsz LK) /\ NA LK = 0 /\ NI LK <= 2.
Proof.
  intros [-> |[(p & q & ->)|(p & q & w & v & ->)]]; unfold TargetSafeC.leak_shape; cbn [xsz map snd fst];
    rewrite ?NA_cons, ?NI_cons, ?zit_7176, ?zit_32768; unfold NA, NI; cbn.
  - split; [left; reflexivity| lia].
  - split; [right; left; eexists; reflexivity| lia].
  - split; [right; right; eexists _, _; reflexivity| lia].
Qed.

Lemma finish_sync_sim : forall C k X p q (w : option P1) (v : option P2) LK1 rc,
  match w, v with
  | Some w1, Some v1 => LK1 = [(w1, v1, 32768)] | None, None => LK1 = [] | _, _ => False
  end ->
  rsimeq (RX C k (LK1 ++ (p, q, 7176) :: X)) (finish_sync (St:=S1) free1 p w rc) (finish_sync (St:=S2) free2 q v rc)
         (fun _ s1 mo1 s2 mo2 => exists LK, RX C k (LK ++ X) s1 mo1 s2 mo2 /\ leak3 LK).
Proof.
  intros C k X p q w v LK1 rc Hw. unfold finish_sync. apply rsimeq_if; intros _.
  - eapply rsimeq_post; [apply (inflate_end_sim C k X LK1 p q w v Hw)|]. cbv beta. intros [] ? ? ? ? HR. exists []. split; [exact HR| left; reflexivity].
  - eapply rsimeq_post; [apply Hfwr; unfold MSG_SHOULD, zlength, TargetSafeC.PIECE_MAX; cbn; lia|]. cbv beta. intros [] ? ? ? ? HR.
    destruct w as [w1|], v as [v1|]; try (exfalso; exact Hw); subst LK1; cbn [app] in HR.
    + exists [(w1, v1, 32768); (p, q, 7176)]. split; [exact HR| right; right; eexists _, _, _, _; reflexivity].
    + exists [(p, q, 7176)]. split; [exact HR| right; left; eexists _, _; reflexivity].
Qed.

Lemma test_sync_sim : forall C k X0 cp1 cp2 cb up1 up2 n c clen,
  HENTRY X0 k -> 0 <= n <= 2^20 -> n <= cb <= 2^21 + 766 -> C + 39944 + 2 * QOV <= CMAX ->   (* 1.4: 7176 + 32768 *)
  rsimeq (RX C (k + 7) ((up1, up2, n) :: (cp1, cp2, cb) :: X0))
         (test_sync_m FM malloc1 free1 fresh1 c clen n) (test_sync_m FM malloc2 free2 fresh2 c clen n)
         (fun _ s1 mo1 s2 mo2 => exists LK k', RX (C + 39944 + 2 * QOV) k' (LK ++ (up1, up2, n) :: (cp1, cp2, cb) :: X0) s1 mo1 s2 mo2 /\ (leak3 LK /\ k + 8 <= k' <= k + 9)).
Proof.
  intros C k X0 cp1 cp2 cb up1 up2 n c clen (HE & HA & HI) Hn Hcb HC. pose proof HE as (_ & _ & _ & K). unfold test_sync_m, ISTATE_N, WIN_N.
  set (X := (up1, up2, n) :: (cp1, cp2, cb) :: X0).
  assert (NAX : NA X <= 4) by (unfold X; rewrite !NA_cons; destruct (zitemb n); destruct (zitemb cb); lia).
  assert (NIX : NI X <= 10) by (unfold X; rewrite !NI_cons; destruct (zitemb n); destruct (zitemb cb); lia).
  unfold rsimeq.
  eapply rsim_bind. { replace (k + 7) with (k + 2 + 5) by lia. zr (TargetSafeC.live_at_p (xsz X0) k tt cb tt n 5 HE ltac:(lia)). }
  intros p1 p2. cbv beta. replace (k + 2 + 5 + 1) with (k + 8) by lia.
  destruct (fm_i1 FM c n) as [|e].
  - destruct (fm_is FM c clen n) as [|e].
    + destruct (fm_i2 FM c clen n) as [|rc].
      * eapply rsim_bind. { zr (TargetSafeC.live_at_wd ((tt, 7176) :: xsz X) (k + 8) ltac:(lia) ltac:(cnt55x)); rewrite ?NI_cons, ?NA_cons, ?zit_7176; lia. }
        intros w1 w2. cbv beta.
        eapply rsim_post; [apply (finish_sync_sim _ (k + 8 + 1) X p1 p2 (Some w1) (Some w2) [(w1, w2, 32768)] _ eq_refl)|].
        intros [] [] ? ? ? ? [_ (LK & HR & HL)]. split; [reflexivity|]. exists LK, (k + 9). split; [eapply Hmono; [| | exact HR]; lia|]. split; [exact HL| lia].
      * eapply rsim_post; [apply (finish_sync_sim _ (k + 8) X p1 p2 None None [] _ eq_refl)|].
        intros [] [] ? ? ? ? [_ (LK & HR & HL)]. split; [reflexivity|]. exists LK, (k + 8). split; [eapply Hmono; [| | exact HR]; lia|]. split; [exact HL| lia].
    + eapply rsim_post; [apply diag_zerr_sim; apply TargetSafeC.msg_inflateSync_short|]. intros [] [] ? ? ? ? [_ HR]. split; [reflexivity|]. exists [(p1, p2, 7176)], (k + 8).
      split; [eapply Hmono; [| | exact HR]; lia|]. split; [right; left; eexists _, _; reflexivity| lia].
  - eapply rsim_post; [apply diag_zerr_sim; apply TargetSafeC.msg_inflate_short|]. intros [] [] ? ? ? ? [_ HR]. split; [reflexivity|]. exists [(p1, p2, 7176)], (k + 8).
    split; [eapply Hmono; [| | exact HR]; lia|]. split; [right; left; eexists _, _; reflexivity| lia].
Qed.

Lemma CLEN_range : forall n, 0 <= n <= 2^20 -> n <= CLEN n <= 2^21 + 766.
Proof.
  intros n Hn. unfold CLEN, cbound.
  pose proof (Z.div_pos n 4096 ltac:(lia) ltac:(lia)). pose proof (Z.div_pos n 16384 ltac:(lia) ltac:(lia)). pose proof (Z.div_pos n 33554432 ltac:(lia) ltac:(lia)).
  pose proof (Z.div_le_mono n (2^20) 4096 ltac:(lia) ltac:(lia)). pose proof (Z.div_le_mono n (2^20) 16384 ltac:(lia) ltac:(lia)). pose proof (Z.div_le_mono n (2^20) 33554432 ltac:(lia) ltac:(lia)).
  change (2^20 / 4096) with 256 in *. change (2^20 / 16384) with 64 in *. change (2^20 / 33554432) with 0 in *. lia.
Qed.

Lemma fuzz_one_sim : forall C k X0 d, HENTRY X0 k -> C + FC <= CMAX ->
  rsimeq (RX C k X0) (fuzz_one_m FM malloc1 free1 fresh1 d) (fuzz_one_m FM malloc2 free2 fresh2 d)
         (fun _ s1 mo1 s2 mo2 => exists LK k', RX (C + FC) k' (LK ++ X0) s1 mo1 s2 mo2 /\ (leak3 LK /\ k <= k' <= k + 9)).
Proof.
  intros C k X0 d HEN HC. pose proof HEN as (HE & HA & HI). pose proof HE as (_ & _ & _ & K). pose proof FC_nonneg as F0. unfold fuzz_one_m.
  apply rsimeq_if; intros SK.
  { apply rsimeq_ret. intros s1 mo1 s2 mo2 H. exists [], k. split; [eapply Hmono; [| | exact H]; lia|]. split; [left; reflexivity| lia]. }
  unfold fuzz_skip, KMAX in SK. apply Bool.orb_false_iff in SK as [SK1 SK2]. apply Z.leb_gt in SK1. apply Z.ltb_ge in SK2.
  assert (Hn : 0 <= zlength d <= 2^20) by (unfold zlength in *; lia).
  pose proof (CLEN_range (zlength d) Hn) as Hcb. unfold FC in HC.
  eapply rsimeq_bind_r.
  { apply creq_sim; [unfold REQMAX; lia| apply HISTOK_of; lia| apply (TargetSafeC.live_at_cp _ _ _ HE); lia| lia]. }
  intros cp1 cp2.
  eapply rsimeq_bind_r.
  { apply creq_sim; [unfold REQMAX; lia| apply HISTOK_of; rewrite ?NI_cons, ?NA_cons; destruct (zitemb _); lia| rewrite xsz_cons; apply (TargetSafeC.live_at_up _ _ _ _ _ HE)| lia]. }
  intros up1 up2. replace (k + 1 + 1) with (k + 2) by lia.
  eapply rsimeq_bind.
  { apply (test_flush_sim _ k X0 cp1 cp2 _ up1 up2 _ d HEN Hn Hcb). lia. }
  intros clen.
  eapply rsimeq_bind.
  { apply (test_sync_sim _ k X0 cp1 cp2 _ up1 up2 _ _ clen HEN Hn Hcb). lia. }
  intros u. apply rsimeq_exI. intros LK. apply rsimeq_exI. intros k'. apply rsimeq_pure_r. intros [HL HK'].
  eapply rsimeq_pre with (R := RX _ k' ((cp1, cp2, CLEN (zlength d)) :: (up1, up2, zlength d) :: LK ++ X0)).
  2:{ intros ? ? ? ? HR. eapply Hperm; [| exact HR].
      change ((cp1, cp2, CLEN (zlength d)) :: (up1, up2, zlength d) :: LK ++ X0) with ([(cp1, cp2, CLEN (zlength d)); (up1, up2, zlength d)] ++ (LK ++ X0)).
      change (LK ++ (up1, up2, zlength d) :: (cp1, cp2, CLEN (zlength d)) :: X0) with (LK ++ [(up1, up2, zlength d); (cp1, cp2, CLEN (zlength d))] ++ X0).
      rewrite !app_assoc. apply Permutation_app_tail. etransitivity; [apply Permutation_app_comm|]. apply Permutation_app_tail. apply perm_swap. }
  eapply rsimeq_seq_r; [apply Hf|]. intros _ _. eapply rsimeq_seq_r; [apply Hf|]. intros _ _.
  apply rsimeq_ret. intros s1 mo1 s2 mo2 H. exists LK, k'. split; [eapply Hmono; [| | exact H]; unfold FC; lia|]. split; [exact HL| lia].
Qed.

Lemma fuzz_oneC_sim : forall C k X0 d, HENTRY X0 k -> C + FC <= CMAX ->
  crsimeq (RX C k X0) (HarnessC.fuzz_one FM malloc1 free1 fresh1 d) (HarnessC.fuzz_one FM malloc2 free2 fresh2 d)
          (fun _ s1 mo1 s2 mo2 => exists LK k', RX (C + FC) k' (LK ++ X0) s1 mo1 s2 mo2 /\ (leak3 LK /\ k <= k' <= k + 9)).
Proof. intros C k X0 d HE HC. unfold HarnessC.fuzz_one. apply crsimeq_lift. apply fuzz_one_sim; assumption. Qed.

Definition RUNX : Z := 4 * FC.

Definition CALLS (X : list (P1 * P2 * Z)) (k : Z) (ncalls : nat) : Prop :=
  TargetSafeC.CALLS_ENTRY (xsz X) k ncalls /\ NA X <= 2 /\ NI X + 2 * Z.of_nat ncalls <= 10.

Local Notation fuzz1c := (HarnessC.fuzz_one FM malloc1 free1 fresh1).
Local Notation fuzz2c := (HarnessC.fuzz_one FM malloc2 free2 fresh2).

Lemma run_callsC_sim : forall ncalls C k X payload rc, CALLS X k ncalls -> C + Z.of_nat ncalls * FC <= CMAX ->
  crsimeq (RX C k X) (AdapterC.run_calls fuzz1c emit1 ncalls payload rc) (AdapterC.run_calls fuzz2c emit2 ncalls payload rc)
          (fun _ s1 mo1 s2 mo2 => exists LK k', RX (C + Z.of_nat ncalls * FC) k' (LK ++ X) s1 mo1 s2 mo2 /\ k <= k' <= k + 9 * Z.of_nat ncalls).
Proof.
  pose proof FC_nonneg as F0.
  induction ncalls as [|nc IH]; intros C k X payload rc ((A & B & CC & K0 & K) & HA & HI) HC; cbn [AdapterC.run_calls].
  - apply crsimeq_ret. intros s1 mo1 s2 mo2 HR. exists [], k. split; [eapply Hmono; [| | exact HR]; lia| cbn; lia].
  - eapply crsimeq_bind.
    { apply fuzz_oneC_sim; [| nia]. split; [| split; [exact HA| lia]]. unfold TargetSafeC.ENTRY. lia. }
    intros rc'. apply crsimeq_exI. intros LK. apply crsimeq_exI. intros k'. apply crsimeq_pure_r. intros [HL HK'].
    destruct (leak3_facts LK HL) as (LS & LA & LI). destruct (TargetSafeC.leak_counts _ LS) as (L1 & L2 & L3 & L4).
    eapply crsimeq_seq; [apply crsimeq_lift; apply Hemit|]. intros _.
    eapply crsimeq_post; [apply (IH _ k' (LK ++ X))|].
    { split; [| rewrite NA_app, NI_app; split; lia].
      unfold TargetSafeC.CALLS_ENTRY, C31, C40, C44 in *. rewrite xsz_app, !cntr_app.
      unfold C31, C40, C44 in *. cbn [length] in K. lia. }
    { nia. }
    cbv beta. intros _ s1 mo1 s2 mo2 (LK2 & k2 & H & HK2). exists (LK2 ++ LK), k2. split; [rewrite <- app_assoc; eapply Hmono; [| | exact H]; nia| lia].
Qed.

Theorem target_runC_sim : forall C k b1 b2 cap cfg payload,
  (exists j, (j <= 10)%nat /\ cap = 65536 * 2 ^ Z.of_nat j) -> 0 <= k <= 12 -> zlength payload <= MAX_INPUT -> C + zlength payload + QOV + RUNX <= CMAX ->
  crsimeq (RX C k [(b1, b2, cap)]) (AdapterC.target_run malloc1 free1 fuzz1c emit1 cfg payload) (AdapterC.target_run malloc2 free2 fuzz2c emit2 cfg payload)
          (fun _ s1 mo1 s2 mo2 => exists LK k', RX (C + zlength payload + QOV + RUNX) k' ((b1, b2, cap) :: LK) s1 mo1 s2 mo2).
Proof.
  intros C k b1 b2 cap cfg payload (j & Hj & Hcap) Hk Hp HC. unfold AdapterC.target_run.
  assert (PL0 : 0 <= zlength payload) by (unfold zlength; lia).
  pose proof FC_nonneg as F0. unfold RUNX in *.
  assert (HN : 0 <= Z.of_nat (Z.to_nat (1 + Z.land cfg 3)) <= 4).
  { assert (HL3 : Z.land cfg 3 = cfg mod 4) by (apply (Z.land_ones cfg 2); lia).
    pose proof (Z.mod_pos_bound cfg 4 ltac:(lia)). lia. }
  set (NC := Z.to_nat (1 + Z.land cfg 3)) in *.
  assert (Hp2 : 1 <= 2 ^ Z.of_nat j <= 1024) by (split; [pose proof (Z.pow_pos_nonneg 2 (Z.of_nat j) ltac:(lia) ltac:(lia)); lia| change 1024 with (2 ^ 10); apply Z.pow_le_mono_r; lia]).
  assert (CAP : C31 [(tt, cap)] = 0 /\ C40 [(tt, cap)] = 0 /\ C44 [(tt, cap)] <= 1 /\ zitemb cap = (j =? 0)%nat).
  { unfold C31, C40, C44. rewrite !cntr_cons_out by lia. pose proof (cntr_cons_le 65517 74876 tt cap (@nil (unit * Z))). rewrite cntr_nil in *.
    split; [reflexivity|]. split; [reflexivity|]. split; [lia|].
    destruct j as [|j']; [subst cap; reflexivity|]. rewrite Nat2Z.inj_succ, Z.pow_succ_r in Hcap by lia.
    unfold zitemb. cbn [Nat.eqb]. pose proof (Z.pow_pos_nonneg 2 (Z.of_nat j') ltac:(lia) ltac:(lia)).
    repeat (rewrite (proj2 (Z.eqb_neq _ _)) by lia). reflexivity. }
  destruct CAP as (C1 & C2 & C3 & C4).
  eapply crsimeq_bind_r with (Q1 := fun a1 a2 => match a1, a2 with
                                                | Some None, Some None => RX (C + zlength payload + QOV) (k + 1) [(b1, b2, cap)]
                                                | Some (Some p), Some (Some q) => RX (C + zlength payload + QOV) (k + 1) [(p, q, zlength payload); (b1, b2, cap)]
                                                | _, _ => fun _ _ _ _ => False
                                                end).
  { apply crsim_lift. unfold AdapterC.payload_copy.
    apply rsim_if; intros _; [ret_rel; eapply Hmono; [| | exact HH]; lia|].
    eapply rsim_bind.
    - apply (malloc_sim0 C k [(b1, b2, cap)] (zlength payload)); [unfold zlength, REQMAX, MAX_INPUT in *; lia| | unfold FPRE; cbn [xsz map snd]; lia| lia].
      apply HISTOK_of; [pose proof (NI_le [(b1, b2, cap)]); cbn [length] in *; lia| left; pose proof (NA_le [(b1, b2, cap)]); cbn [length] in *; lia].
    - intros [p|] [q|]; cbn beta iota; [| apply rsim_false| apply rsim_false| apply rsim_false]. ret_rel. exact (proj1 HH). }
  intros [[p|]|] [[q|]|]; cbn beta iota; try apply crsimeq_false.
  - eapply crsimeq_bind.
    { apply (run_callsC_sim NC); [| nia].
      split; [| pose proof (NA_le [(p, q, zlength payload); (b1, b2, cap)]); pose proof (NI_le [(p, q, zlength payload); (b1, b2, cap)]); cbn [length] in *; lia].
      unfold TargetSafeC.CALLS_ENTRY. rewrite !xsz_cons. cbn [xsz map snd]. unfold C31, C40, C44 in *.
      pose proof (cntr_cons_le 5437 8172 tt (zlength payload) [(tt, cap)]). pose proof (cntr_cons_le 32749 37436 tt (zlength payload) [(tt, cap)]).
      pose proof (cntr_cons_le 65517 74876 tt (zlength payload) [(tt, cap)]). lia. }
    intros rc. apply crsimeq_exI. intros LK. apply crsimeq_exI. intros k'. apply crsimeq_pure_r. intros HK'.
    eapply crsimeq_seq_r.
    { apply crsim_lift. eapply rsim_pre; [apply (Hf (C + zlength payload + QOV + Z.of_nat NC * FC) k' ((b1, b2, cap) :: LK) p q (zlength payload))|].
      intros ? ? ? ? HR. eapply Hperm; [| exact HR]. symmetry. apply Permutation_cons_app. apply Permutation_cons_append. }
    intros _ _. apply crsimeq_ret. intros s1 mo1 s2 mo2 HR. exists LK, k'. eapply Hmono; [| | exact HR]; nia.
  - eapply crsimeq_bind.
    { apply (run_callsC_sim NC); [| nia].
      split; [| pose proof (NA_le [(b1, b2, cap)]); pose proof (NI_le [(b1, b2, cap)]); cbn [length] in *; lia].
      unfold TargetSafeC.CALLS_ENTRY. cbn [xsz map snd]. unfold C31, C40, C44 in *. lia. }
    intros rc. apply crsimeq_exI. intros LK. apply crsimeq_exI. intros k'. apply crsimeq_pure_r. intros HK'.
    eapply crsimeq_seq; [apply crsimeq_lift; ret_same|]. intros _.
    apply crsimeq_ret. intros s1 mo1 s2 mo2 HR. exists LK, k'. eapply Hmono; [| | eapply Hperm; [symmetry; apply Permutation_cons_append| exact HR]]; nia.
Qed.
End Target.


Section Driver.
Context {P1 P2 : Type}.
Variables (io1_ : IOStyle S1) (io2_ : IOStyle S2).
Variables (malloc1 : Z -> M S1 (option P1)) (malloc2 : Z -> M S2 (option P2)).
Variables (free1 : P1 -> M S1 unit) (free2 : P2 -> M S2 unit).
Variables (fresh1 : S1 -> S1 -> P1 -> bool) (fresh2 : S2 -> S2 -> P2 -> bool).
Variables (rs1 rs2 : Z).
Variables (alloc_init1 : Z -> M S1 unit) (alloc_init2 : Z -> M S2 unit).
Variables (alloc_count1 : M S1 Z) (alloc_count2 : M S2 Z).
Variable RX : Z -> Z -> list (P1 * P2 * Z) -> rel.
Variables (QOV CMAX : Z).
Variable RUNX : Z.
Hypothesis HRUNX : 0 <= RUNX.

Definition CK (k : nat) : Z := 65536 * (2 ^ (Z.of_nat k + 1) - 1) + QOV * (Z.of_nat k + 1).
Definition CDONE : Z := CK 10.
Hypothesis HQ0 : 0 <= QOV.
Hypothesis HCMAX : CDONE + MAX_INPUT + QOV + RUNX <= CMAX.

Local Notation sizes := (map (@snd (P1 * P2) Z)).
Local Notation xsz := (xsz (P1:=P1) (P2:=P2)).
Local Notation Qm := (Qm RX QOV fresh1 fresh2).
Hypothesis Hm : forall C k X n s10 s20, 0 <= n <= REQMAX -> HISTOK (n :: sizes X) -> FPRE (xsz X) k n -> C + n + QOV <= CMAX ->
  rsim (fun s1 mo1 s2 mo2 => s1 = s10 /\ s2 = s20 /\ RX C k X s1 mo1 s2 mo2) (malloc1 n) (malloc2 n) (Qm C k X n s10 s20).
Hypothesis Hf : forall C k X p q n, rsim (RX C k ((p, q, n) :: X)) (free1 p) (free2 q) (fun _ _ => RX C k X).
Hypothesis Hperm : forall C k X Y s1 mo1 s2 mo2, Permutation X Y -> RX C k X s1 mo1 s2 mo2 -> RX C k Y s1 mo1 s2 mo2.
Hypothesis Hmono : forall C C' k k' X s1 mo1 s2 mo2, C <= C' -> k <= k' -> RX C k X s1 mo1 s2 mo2 -> RX C' k' X s1 mo1 s2 mo2.
Hypothesis Hdiag : forall C k X d, diag_short d -> rsimeq (RX C k X) (io_diag io1_ d) (io_diag io2_ d) (fun _ => RX C k X).
Hypothesis Hinit : forall C k X bm, rsimeq (RX C k X) (alloc_init1 bm) (alloc_init2 bm) (fun _ => RX C k X).
Hypothesis Hcount : forall C k X, rsimeq (RX C k X) alloc_count1 alloc_count2 (fun _ => RX C k X).
Hypothesis Hopen : forall C k X path, rsimeq (RX C k X) (msys (NOpen path) dec_open) (msys (NOpen path) dec_open) (fun _ => RX C k X).
Hypothesis Hclose : forall C k X fd, rsimeq (RX C k X) (msys (NClose fd) dec_close) (msys (NClose fd) dec_close) (fun _ => RX C k X).
Hypothesis Hread : forall C k X fd buf1 buf2 cnt, 0 <= cnt < 2^64 ->
  rsimeq (RX C k X) (msys (NRead fd buf1 cnt) (dec_read buf1 cnt)) (msys (NRead fd buf2 cnt) (dec_read buf2 cnt))
         (fun a => match a with RdData bs => fun s1 mo1 s2 mo2 => RX C k X s1 mo1 s2 mo2 /\ zlength bs <= cnt | RdErr _ => RX C k X end).

Lemma malloc_sim0' : forall C k X n, 0 <= n <= REQMAX -> HISTOK (n :: sizes X) -> FPRE (xsz X) k n -> C + n + QOV <= CMAX ->
  rsim (RX C k X) (malloc1 n) (malloc2 n)
       (fun r1 r2 => match r1, r2 with
                     | Some p, Some q => fun s1 mo1 s2 mo2 => RX (C + n + QOV) (k + 1) ((p, q, n) :: X) s1 mo1 s2 mo2 /\ n < 2^63
                     | _, _ => fun _ _ _ _ => False
                     end).
Proof.
  intros C k X n Hn HK0 HF HC. apply rsim_pointwise. intros s10 mo10 s20 mo20 HR.
  eapply rsim_conseq; [apply (Hm C k X n s10 s20 Hn HK0 HF HC)| intros ? ? ? ? (-> & -> & -> & ->); auto|].
  intros [p|] [q|] ? ? ? ? HQ; cbn [Qm] in HQ |- *; try exact HQ. destruct HQ as (A & B & _). auto.
Qed.

Lemma kbound12 (k : nat) : (k <= 10)%nat -> Z.of_nat k + 1 <= 12. Proof. lia. Qed.

Lemma pow2_le_1024' : forall k, (k <= 10)%nat -> 1 <= 2 ^ Z.of_nat k <= 1024.
Proof. intros k Hk. split; [pose proof (Z.pow_pos_nonneg 2 (Z.of_nat k) ltac:(lia) ltac:(lia)); lia|]. change 1024 with (2 ^ 10). apply Z.pow_le_mono_r; lia. Qed.

Lemma CK_succ : forall k, CK (S k) = CK k + 65536 * 2 ^ Z.of_nat k * 2 + QOV.
Proof.
  intros k. unfold CK. rewrite Nat2Z.inj_succ. replace (Z.succ (Z.of_nat k) + 1) with (Z.succ (Z.succ (Z.of_nat k))) by lia.
  replace (Z.of_nat k + 1) with (Z.succ (Z.of_nat k)) by lia. rewrite !Z.pow_succ_r by lia. lia.
Qed.
Lemma CK_le : forall k, (k <= 10)%nat -> CK k <= CDONE.
Proof.
  intros k Hk. unfold CDONE, CK. pose proof (pow2_le_1024' k Hk) as P.
  assert (2 ^ (Z.of_nat k + 1) <= 2 ^ (Z.of_nat 10 + 1)) by (apply Z.pow_le_mono_r; lia). nia.
Qed.
Lemma CK_0 : CK 0 = 0 + 65536 + QOV. Proof. unfold CK. cbn. lia. Qed.

Definition rd_rel (st1 : @rd_st P1) (st2 : @rd_st P2) : rel := fun s1 mo1 s2 mo2 =>
  rd_cap st2 = rd_cap st1 /\ rd_content st2 = rd_content st1
  /\ zlength (rd_content st1) <= rd_cap st1 /\ exists k, (k <= 10)%nat /\ rd_cap st1 = 65536 * 2 ^ Z.of_nat k
  /\ RX (CK k) (Z.of_nat k + 1) [(rd_buf st1, rd_buf st2, rd_cap st1)] s1 mo1 s2 mo2.

Definition QR (r1 : @rd_result P1) (r2 : @rd_result P2) : rel :=
  match r1, r2 with
  | RdExit, RdExit => fun s1 mo1 s2 mo2 => exists C' k' X', RX C' k' X' s1 mo1 s2 mo2
  | RdDone b1 c1, RdDone b2 c2 => fun s1 mo1 s2 mo2 => (exists cap, RX CDONE 12 [(b1, b2, cap)] s1 mo1 s2 mo2 /\ (exists j, (j <= 10)%nat /\ cap = 65536 * 2 ^ Z.of_nat j)) /\ c2 = c1 /\ zlength c1 <= MAX_INPUT
  | _, _ => fun _ _ _ _ => False
  end.

Local Ltac ret_same := apply rsimeq_ret; intros ? ? ? ? HH; exact HH.
Local Ltac ret_rel := apply rsim_ret; intros ? ? ? ? HH.

Lemma HISTOK_amb0' n (Z : list Z) : (length Z <= 3)%nat -> HISTOK (n :: Z).
Proof. intros HL. apply (HISTOK_amb n [] Z); [apply Forall_nil| unfold BCs, zsum; cbn; unfold HB; lia| unfold N4s, N24s, zcount, zlen; cbn; lia| exact HL]. Qed.

Lemma read_loop_body_sim : forall fd path st1 st2, zlength path <= PIECE_MAX ->
  rsim (rd_rel st1 st2) (read_loop_body io1_ malloc1 free1 rs1 fd path st1) (read_loop_body io2_ malloc2 free2 rs2 fd path st2)
       (fun r1 r2 => match r1, r2 with
                     | inl st1', inl st2' => rd_rel st1' st2'
                     | inr res1, inr res2 => QR res1 res2
                     | _, _ => fun _ _ _ _ => False
                     end).
Proof.
  intros fd path st1 st2 Hpath. unfold read_loop_body.
  apply rsim_pointwise. intros s10 mo10 s20 mo20 (Ecap & Ect & Hlen & (k & Hk & Hcap & Ho0)). rewrite Ecap, Ect.
  pose proof (pow2_le_1024' k Hk) as Hp2.
  eapply rsim_bind with
    (Q1 := fun g1 g2 => match g1, g2 with
                       | None, None => fun s1 mo1 s2 mo2 => exists C' k' X', RX C' k' X' s1 mo1 s2 mo2
                       | Some st1', Some st2' => fun s1 mo1 s2 mo2 => rd_rel st1' st2' s1 mo1 s2 mo2 /\ rd_content st1' = rd_content st1 /\ zlength (rd_content st1) < rd_cap st1'
                       | _, _ => fun _ _ _ _ => False
                       end).
  { destruct (Z.eqb_spec (zlength (rd_content st1)) (rd_cap st1)) as [Heq|Hne].
    - destruct (Z.leb_spec MAX_INPUT (rd_cap st1)) as [Hbig|Hsmall].
      + eapply rsim_bind; [eapply rsim_pre; [apply Hdiag; exact I| intros ? ? ? ? (-> & -> & -> & ->); exact Ho0]|].
        intros ? ?. apply rsim_pure. intros _. ret_rel. exists (CK k), (Z.of_nat k + 1), [(rd_buf st1, rd_buf st2, rd_cap st1)]. exact HH.
      + assert (Hk9 : (k <= 9)%nat).
        { destruct (Nat.le_gt_cases k 9) as [|Hgt]; [assumption|]. exfalso. assert (k = 10%nat) as -> by lia. unfold MAX_INPUT in Hsmall. cbn in Hcap. lia. }
        assert (HCk : CK k + rd_cap st1 * 2 + QOV <= CMAX).
        { pose proof (CK_le (S k) ltac:(lia)) as L. rewrite CK_succ in L. rewrite Hcap. unfold MAX_INPUT in HCMAX. lia. }
        eapply rsim_bind. { eapply (rsim_pre _ _ _ _ _ _ (RX (CK k) (Z.of_nat k + 1) [(rd_buf st1, rd_buf st2, rd_cap st1)])); [apply malloc_sim0'; [unfold REQMAX, MAX_INPUT in *; lia| apply HISTOK_amb0'; cbn; lia| unfold FPRE; cbn [xsz map snd]; rewrite Hcap; nia| exact HCk]| intros ? ? ? ? (-> & -> & -> & ->); exact Ho0]. }
        intros [nb1|] [nb2|]; cbn beta iota; [| apply rsim_false| apply rsim_false| apply rsim_false].
        * eapply rsim_seq.
          { eapply rsim_pre; [apply (Hf (CK k + rd_cap st1 * 2 + QOV) (Z.of_nat k + 1 + 1) [(nb1, nb2, rd_cap st1 * 2)] (rd_buf st1) (rd_buf st2) (rd_cap st1))|]. intros ? ? ? ? [Ho _]. eapply Hperm; [apply perm_swap| exact Ho]. }
          intros _ _. ret_rel. cbn. unfold rd_rel. cbn.
          splits; auto; try lia.
          exists (S k). split; [lia|]. split; [rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia; lia|].
          rewrite CK_succ, <- Hcap, Nat2Z.inj_succ. replace (Z.succ (Z.of_nat k) + 1) with (Z.of_nat k + 1 + 1) by lia. exact HH.
    - ret_rel. destruct HH as (-> & -> & -> & ->). unfold rd_rel. splits; auto; try lia. exists k; auto. }
  intros [st1'|] [st2'|]; cbn beta iota; [| apply rsim_false| apply rsim_false| ret_rel; exact HH].
  apply rsim_pointwise. intros s11 mo11 s21 mo21 ((Ecap' & Ect' & Hlen' & (k' & Hk' & Hcap' & Ho)) & Hct & Hlt). rewrite Ecap', Ect', Hct.
  pose proof (pow2_le_1024' k' Hk') as Hp2'.
  set (want0 := rd_cap st1' - zlength (rd_content st1)).
  set (want := if 65536 <? want0 then 65536 else want0).
  assert (Hwant : 0 <= want <= want0 /\ want < 2^64). { subst want want0. destruct (Z.ltb_spec 65536 (rd_cap st1' - zlength (rd_content st1))); lia. }
  eapply rsim_bind_eq.
  { eapply rsim_pre; [apply (Hread (CK k') (Z.of_nat k' + 1) [(rd_buf st1', rd_buf st2', rd_cap st1')] fd _ _ want); lia|].
    intros ? ? ? ? (-> & -> & -> & ->). exact Ho. }
  intros [e|bs]; cbn beta iota.
  - eapply rsim_bind; [apply Hdiag; exact Hpath|]. intros ? ?. apply rsim_pure. intros _. ret_rel. exists (CK k'), (Z.of_nat k' + 1), [(rd_buf st1', rd_buf st2', rd_cap st1')]. exact HH.
  - destruct (length bs =? 0)%nat eqn:C.
    + ret_rel. destruct HH as [Ho' _]. cbn. split; [exists (rd_cap st1'); split; [eapply Hmono; [apply (CK_le k' Hk')| apply kbound12; exact Hk'| exact Ho']| exists k'; auto]|]. split; [reflexivity|]. unfold MAX_INPUT in *. lia.
    + ret_rel. destruct HH as [Ho' Hbs]. unfold rd_rel. cbn. rewrite zlength_app', zlength_u8s', ?Hct. splits; auto; [lia| exists k'; auto].
Qed.

Lemma read_all_sim : forall path, zlength path <= PIECE_MAX ->
  rsim (RX 0 0 []) (read_all io1_ malloc1 free1 rs1 path) (read_all io2_ malloc2 free2 rs2 path) QR.
Proof.
  intros path Hpath. unfold read_all.
  eapply rsim_bind_eq; [apply Hopen|]. intros [e|fd]; cbn beta iota.
  - eapply rsim_bind; [apply Hdiag; exact Hpath|]. intros ? ?. apply rsim_pure. intros _. ret_rel. exists 0, 0, []. exact HH.
  - assert (HC0 : 0 + 65536 + QOV <= CMAX).
    { pose proof (CK_le 0 ltac:(lia)) as L. rewrite CK_0 in L. unfold MAX_INPUT in HCMAX. lia. }
    eapply rsim_bind; [apply malloc_sim0'; [unfold REQMAX; lia| apply HISTOK_amb0'; cbn; lia| unfold FPRE, C31, C40, C44; cbn; rewrite ?cntr_nil; lia| exact HC0]|]. intros [buf1|] [buf2|]; cbn beta iota; [| apply rsim_false| apply rsim_false| apply rsim_false].
    eapply rsim_bind.
    + eapply rsim_pre.
      * apply (rsim_loop step1 step2 nexit nexit Phi1 Phi2 rd_rel QR).
        intros st1 st2. eapply rsim_post; [apply read_loop_body_sim; exact Hpath|]. intros [st1'|r1] [st2'|r2] s1 mo1 s2 mo2 H; exact H.
      * intros s1 mo1 s2 mo2 [Ho _]. unfold rd_rel. cbn. split; [reflexivity|]. split; [reflexivity|]. split; [unfold zlength; cbn; lia|]. exists 0%nat. split; [lia|]. split; [reflexivity|]. rewrite CK_0. cbn [Z.of_nat Z.add]. exact Ho.
    + intros [|buf1' c1] [|buf2' c2]; cbn beta iota; [ret_rel; exact HH| apply rsim_false| apply rsim_false|].
      apply rsim_pure_r. intros [-> Hlen].
      eapply rsim_bind with (Q1 := fun _ _ s1 mo1 s2 mo2 => exists cap, RX CDONE 12 [(buf1', buf2', cap)] s1 mo1 s2 mo2 /\ (exists j, (j <= 10)%nat /\ cap = 65536 * 2 ^ Z.of_nat j)).
      { apply rsim_exI. intros cap. apply rsim_pure_r. intros Hj. eapply rsim_post; [apply Hclose|]. intros ? ? ? ? ? ? [_ HR]. exists cap. split; [exact HR| exact Hj]. }
      intros ? ?. ret_rel. cbn. auto.
Qed.

Variables (run1c : Z -> list Z -> MC S1 Z) (run2c : Z -> list Z -> MC S2 Z).
Hypothesis HrunC : forall C k b1 b2 cap cfg payload, (exists j, (j <= 10)%nat /\ cap = 65536 * 2 ^ Z.of_nat j) -> 0 <= k <= 12 ->
  zlength payload <= MAX_INPUT -> C + zlength payload + QOV + RUNX <= CMAX ->
  crsimeq (RX C k [(b1, b2, cap)]) (run1c cfg payload) (run2c cfg payload)
          (fun _ s1 mo1 s2 mo2 => exists LK k', RX (C + zlength payload + QOV + RUNX) k' ((b1, b2, cap) :: LK) s1 mo1 s2 mo2).

Lemma main_modelC_sim : forall argv, Forall (fun a => zlength a <= PIECE_MAX) argv ->
  crsimeq (RX 0 0 []) (DriverC.main_model io1_ malloc1 free1 rs1 alloc_init1 run1c alloc_count1 argv)
                    (DriverC.main_model io2_ malloc2 free2 rs2 alloc_init2 run2c alloc_count2 argv)
          (fun _ s1 mo1 s2 mo2 => exists C' k' X', RX C' k' X' s1 mo1 s2 mo2).
Proof.
  intros argv Hargv. unfold DriverC.main_model.
  assert (Hnth : forall i, zlength (nth i argv []) <= PIECE_MAX).
  { intros i. destruct (nth_in_or_default i argv []) as [Hin| ->]; [exact (proj1 (Forall_forall _ _) Hargv _ Hin)| unfold zlength, PIECE_MAX; cbn; lia]. }
  apply crsimeq_if; intros C.
  { apply crsimeq_lift. eapply rsimeq_seq; [apply Hdiag; cbn; apply Hnth|]. intros _. apply rsimeq_ret. intros s1 mo1 s2 mo2 Ho. exists 0, 0, []. exact Ho. }
  eapply crsimeq_bind_r; [apply crsim_lift; apply read_all_sim; apply Hnth|]. intros [|buf1 c1] [|buf2 c2]; cbn beta iota; [| apply crsimeq_false| apply crsimeq_false|].
  { apply crsimeq_ret. intros s1 mo1 s2 mo2 (C' & k' & X' & Ho). exists C', k', X'. exact Ho. }
  apply crsimeq_pure_r. intros [-> Hlen]. apply crsimeq_exI. intros cap. apply crsimeq_pure_r. intros Hshape.
  apply crsimeq_if; intros C1.
  { apply crsimeq_lift. eapply rsimeq_seq; [apply Hdiag; exact I|]. intros _. eapply rsimeq_seq_r; [apply Hf|]. intros _ _. apply rsimeq_ret. intros s1 mo1 s2 mo2 Ho. exists CDONE, 12, []. exact Ho. }
  apply crsimeq_if; intros C2.
  { apply crsimeq_lift. eapply rsimeq_seq; [apply Hdiag; exact I|]. intros _. eapply rsimeq_seq_r; [apply Hf|]. intros _ _. apply rsimeq_ret. intros s1 mo1 s2 mo2 Ho. exists CDONE, 12, []. exact Ho. }
  eapply crsimeq_seq; [apply crsimeq_lift; apply Hinit|]. intros _.
  set (payload := skipn (Z.to_nat (6 + Z.land (le16 c1) 32767)) c1).
  assert (Hpl : zlength payload <= MAX_INPUT) by (etransitivity; [| exact Hlen]; unfold payload, zlength; rewrite length_skipn; lia).
  eapply crsimeq_bind; [apply (HrunC CDONE 12 buf1 buf2 cap); [exact Hshape| lia| exact Hpl| lia]|]. intros status.
  apply crsimeq_exI. intros LK. apply crsimeq_exI. intros k'.
  eapply crsimeq_bind with (Q1 := fun _ => RX (CDONE + zlength payload + QOV + RUNX) k' ((buf1, buf2, cap) :: LK)).
  { apply crsimeq_lift. destruct (Z.testbit _ 15).
    - eapply rsimeq_seq; [apply Hcount|]. intros n. apply rsimeq_ret. auto.
    - apply rsimeq_ret. auto. }
  intros status'. eapply crsimeq_seq_r; [apply crsim_lift; apply Hf|]. intros _ _.
  apply crsimeq_ret. intros s1 mo1 s2 mo2 Ho. exists (CDONE + zlength payload + QOV + RUNX), k', LK. exact Ho.
Qed.

Hypothesis Hioexit : forall C k X, rsimeq (RX C k X) (io_exit io1_) (io_exit io2_) (fun _ => RX C k X).
Hypothesis Hexitnode : forall C k X c (Q : Empty_set -> Empty_set -> rel), rsim (RX C k X) (msys (NExit c) dec_exit) (msys (NExit c) dec_exit) Q.

Lemma exit_model_sim : forall code (Q : Empty_set -> Empty_set -> rel),
  rsim (fun s1 mo1 s2 mo2 => exists C k X, RX C k X s1 mo1 s2 mo2) (exit_model io1_ code) (exit_model io2_ code) Q.
Proof.
  intros code Q. unfold exit_model. apply rsim_exI. intros C. apply rsim_exI. intros k. apply rsim_exI. intros X.
  eapply rsim_bind; [apply Hioexit|]. intros ? ?. apply rsim_pure. intros _. apply Hexitnode.
Qed.

Theorem main_exitC_sim : forall argv (Q : Empty_set -> Empty_set -> rel), Forall (fun a => zlength a <= PIECE_MAX) argv ->
  crsim (RX 0 0 []) (cmbind (DriverC.main_model io1_ malloc1 free1 rs1 alloc_init1 run1c alloc_count1 argv) (fun code => DriverC.exit_model io1_ code))
                  (cmbind (DriverC.main_model io2_ malloc2 free2 rs2 alloc_init2 run2c alloc_count2 argv) (fun code => DriverC.exit_model io2_ code)) Q.
Proof.
  intros argv Q Hargv. eapply crsim_bind; [apply main_modelC_sim; exact Hargv|]. intros c1 c2.
  apply (crsim_pure _ _ _ _ _ _ _ (c1 = c2)). intros <-. unfold DriverC.exit_model. apply crsim_lift. apply exit_model_sim.
Qed.
End Driver.

End Prog.

Lemma CDONE_nonneg : forall QOV, 0 <= QOV -> 0 <= CDONE QOV.
Proof. intros Q HQ. unfold CDONE, CK. change (2 ^ (Z.of_nat 10 + 1)) with 2048. lia. Qed.
