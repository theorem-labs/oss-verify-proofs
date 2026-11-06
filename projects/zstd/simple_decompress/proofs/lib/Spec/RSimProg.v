(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import String.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Lib Require Import PropExec MState ITree Nodes Decode.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Spec Require Import Prelim Monad MSafe MPaths STree Stdio Harness Adapter Driver TargetSafe StepB EquivShared EquivProg RSim MI_Inv LB_Inv LB_Sum SizeHist.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import Keeps.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Local Notation M := Monad.M.
Ltac splits := repeat (lazymatch goal with |- _ /\ _ => split | |- _ => fail end).

(* [comment removed for export] *)
Definition io_node (n : node) : Prop :=
  match n with
  | NWrite _ _ | NWritev _ _ | NOpen _ | NRead _ _ _ | NClose _ | NIoctl _ _ | NSetTid | NExit _ => True
  | _ => False
  end.

Lemma io_not_nf : forall n, io_node n -> ~ nf_node n.
Proof. intros n H Hn. destruct n; cbn in *; tauto. Qed.

(* [comment removed for export] *)
Definition REQMAX : Z := 10 * 2^26 + 2^12.

(* [comment removed for export] *)

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

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition rsimeq {A} (R : rel) (m1 : M S1 A) (m2 : M S2 A) (Q : A -> rel) : Prop :=
  rsim R m1 m2 (fun a b s1 mo1 s2 mo2 => a = b /\ Q a s1 mo1 s2 mo2).

Lemma rsimeq_bind {A B} (R : rel) (m1 : M S1 A) (m2 : M S2 A) (Q1 : A -> rel) (k1 : A -> M S1 B) (k2 : A -> M S2 B) Q :
  rsimeq R m1 m2 Q1 -> (forall a, rsimeq (Q1 a) (k1 a) (k2 a) Q) -> rsimeq R (mbind m1 k1) (mbind m2 k2) Q.
Proof. intros H1 H2. unfold rsimeq. eapply rsim_bind_eq; [exact H1| exact H2]. Qed.

(* [comment removed for export] *)
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

(* [comment removed for export] *)
Lemma rsimeq_seq_r {A B C} (R R1 : rel) (m1 : M S1 A) (m2 : M S2 B) (k1 : A -> M S1 C) (k2 : B -> M S2 C) Q :
  rsim R m1 m2 (fun _ _ => R1) -> (forall a b, rsimeq R1 (k1 a) (k2 b) Q) -> rsimeq R (mbind m1 k1) (mbind m2 k2) Q.
Proof. intros H1 H2. eapply rsimeq_bind_r; [exact H1| exact H2]. Qed.

Lemma rsimeq_pointwise {A} (R : rel) (m1 : M S1 A) (m2 : M S2 A) Q :
  (forall s1 mo1 s2 mo2, R s1 mo1 s2 mo2 -> rsimeq (fun s1' mo1' s2' mo2' => s1' = s1 /\ mo1' = mo1 /\ s2' = s2 /\ mo2' = mo2) m1 m2 Q) ->
  rsimeq R m1 m2 Q.
Proof. intros H. unfold rsimeq. apply rsim_pointwise. exact H. Qed.

Lemma rsimeq_if {A} (b : bool) (R : rel) (m1 m1' : M S1 A) (m2 m2' : M S2 A) Q :
  (b = true -> rsimeq R m1 m2 Q) -> (b = false -> rsimeq R m1' m2' Q) -> rsimeq R (if b then m1 else m1') (if b then m2 else m2') Q.
Proof. intros H1 H2. destruct b; auto. Qed.

Lemma rsimeq_false {A} (m1 : M S1 A) (m2 : M S2 A) Q : rsimeq (fun _ _ _ _ => False) m1 m2 Q.
Proof. unfold rsimeq. apply rsim_false. Qed.

Lemma rsimeq_drop {A} (R : rel) (phi : Prop) (m1 : M S1 A) (m2 : M S2 A) Q :
  rsimeq R m1 m2 Q -> rsimeq (fun s1 mo1 s2 mo2 => R s1 mo1 s2 mo2 /\ phi) m1 m2 Q.
Proof. intros H. eapply rsimeq_pre; [exact H|]. intros ? ? ? ? [HR _]. exact HR. Qed.

Lemma rsimeq_pure {A} (R : rel) (phi : Prop) (m1 : M S1 A) (m2 : M S2 A) Q :
  (phi -> rsimeq R m1 m2 Q) -> rsimeq (fun s1 mo1 s2 mo2 => phi /\ R s1 mo1 s2 mo2) m1 m2 Q.
Proof. intros H. unfold rsimeq. apply rsim_pure. exact H. Qed.

Lemma rsimeq_exI {A X} (R : X -> rel) (m1 : M S1 A) (m2 : M S2 A) Q :
  (forall x, rsimeq (R x) m1 m2 Q) -> rsimeq (fun s1 mo1 s2 mo2 => exists x, R x s1 mo1 s2 mo2) m1 m2 Q.
Proof. intros H. unfold rsimeq. apply rsim_exI. exact H. Qed.

Lemma rsimeq_loop {X A} (I : X -> rel) (Q : A -> rel) (body1 : X -> M S1 (X + A)) (body2 : X -> M S2 (X + A)) :
  (forall x, rsimeq (I x) (body1 x) (body2 x) (fun r => match r with inl x' => I x' | inr a => Q a end)) ->
  forall fuel x, rsimeq (I x) (mloop fuel body1 x) (mloop fuel body2 x) Q.
Proof.
  intros Hb fuel. induction fuel as [|fuel IH]; intros x; cbn [mloop]; [apply rsimeq_munr|].
  eapply rsimeq_bind; [apply Hb|]. intros [x'|a]; cbn beta; [apply IH| apply rsimeq_ret; auto].
Qed.

(* [comment removed for export] *)
Lemma rsim_bind_get {A B} (R : rel) (k1 : S1 -> M S1 A) (k2 : S2 -> M S2 B) Q :
  (forall s1 mo1 s2 mo2, R s1 mo1 s2 mo2 ->
     rsim (fun s1' mo1' s2' mo2' => s1' = s1 /\ mo1' = mo1 /\ s2' = s2 /\ mo2' = mo2) (k1 s1) (k2 s2) Q) ->
  rsim R (mbind mget k1) (mbind mget k2) Q.
Proof.
  intros H. eapply rsim_bind; [apply rsim_get|]. intros a b. apply rsim_pointwise.
  intros s1 mo1 s2 mo2 (-> & -> & HR). eapply rsim_pre; [exact (H _ _ _ _ HR)|]. intros ? ? ? ? (-> & -> & -> & ->). auto.
Qed.

(* [comment removed for export] *)
Lemma tall_tpath (step : node -> Model -> resp -> Model -> list event -> Prop) {A} (P : A -> Prop) (t : itree node (exc A)) :
  forall mo tr a mo', tall P t -> tpath step t mo tr (Ok a) mo' -> P a.
Proof.
  induction t as [[|r]|n k IH]; intros mo tr a mo' HT Hp; cbn in *.
  - destruct Hp as (E & _). discriminate.
  - destruct Hp as (E & _ & _). injection E as ->. exact HT.
  - destruct Hp as (rsp & mo1 & evs & tr' & _ & Hp & _). eapply IH; [apply HT| exact Hp].
Qed.

(* [comment removed for export] *)
Lemma rsim_tall {A B} (R : rel) (m1 : M S1 A) (m2 : M S2 B) (Q : A -> B -> rel) (Pl : A * S1 -> Prop) :
  rsim R m1 m2 Q -> (forall s, tall Pl (m1 s)) ->
  rsim R m1 m2 (fun a b s1 mo1 s2 mo2 => Q a b s1 mo1 s2 mo2 /\ Pl (a, s1)).
Proof.
  intros [H12 H21] HT. split.
  - intros s1 mo1 s2 mo2 HR G1 G2. destruct (H12 _ _ _ _ HR G1 G2) as [HP HE]. split; [|exact HE].
    intros tr r1 mo1' Hp. destruct (HP _ _ _ Hp) as (r2 & mo2' & Hp2 & HRes). exists r2, mo2'. split; [exact Hp2|].
    destruct r1 as [|[a s1']]; destruct r2 as [|[b s2']]; cbn in *; auto. split; [exact HRes|]. exact (tall_tpath step1 _ _ _ _ _ _ (HT s1) Hp).
  - intros s2 mo2 s1 mo1 HR G2 G1. destruct (H21 _ _ _ _ HR G2 G1) as [HP HE]. split; [|exact HE].
    intros tr r2 mo2' Hp. destruct (HP _ _ _ Hp) as (r1 & mo1' & Hp1 & HRes). exists r1, mo1'. split; [exact Hp1|].
    destruct r2 as [|[b s2']]; destruct r1 as [|[a s1']]; cbn in *; auto. unfold flQ, fl in *. split; [exact HRes|]. exact (tall_tpath step1 _ _ _ _ _ _ (HT s1) Hp1).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

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

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

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

(* [comment removed for export] *)
Lemma s_diag_sim : forall d, rsimeq R (s_diag d) (s_diag d) (fun _ => R).
Proof. intros d. destruct d; cbn [s_diag]; first [apply stderr_fprintf_sim | apply stderr_fwrite_sim]. Qed.

Lemma s_emit_sim : forall v, rsimeq R (s_emit get1 set1 v) (s_emit get2 set2 v) (fun _ => R).
Proof. intros v. unfold s_emit. apply stdout_vprintf_sim. Qed.

Lemma stderr_fputs_sim : forall s, rsimeq R (stderr_fputs (St:=S1) s) (stderr_fputs (St:=S2) s) (fun _ => R).
Proof. intros s. unfold stderr_fputs. apply stderr_fwrite_sim. Qed.
End Stdio.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section FdNodes.
(* [comment removed for export] *)
Variables (MI1 MI2 : Model -> Prop).
Hypothesis MI1_pres : forall n mo rsp mo' evs, nstep n mo rsp mo' evs -> io_node n -> MI1 mo -> m_halted mo = None -> MI1 mo' /\ m_halted mo' = None.
Hypothesis MI2_pres : forall n mo rsp mo' evs, nstep n mo rsp mo' evs -> io_node n -> MI2 mo -> m_halted mo = None -> MI2 mo' /\ m_halted mo' = None.
Variable R : rel.
Hypothesis Rmodels : forall s1 mo1 s2 mo2, R s1 mo1 s2 mo2 ->
  MI1 mo1 /\ MI2 mo2 /\ m_halted mo1 = None /\ m_halted mo2 = None /\ m_fds mo1 = m_fds mo2 /\ m_fs mo1 = m_fs mo2.
(* [comment removed for export] *)
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

(* [comment removed for export] *)
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

(* [comment removed for export] *)
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


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma rsim_drop {A B} (R : rel) (phi : Prop) (m1 : M S1 A) (m2 : M S2 B) Q :
  rsim R m1 m2 Q -> rsim (fun s1 mo1 s2 mo2 => R s1 mo1 s2 mo2 /\ phi) m1 m2 Q.
Proof. intros H. eapply rsim_pre; [exact H|]. intros ? ? ? ? [HR _]. exact HR. Qed.

(* [comment removed for export] *)
Lemma rsim_pure_r {A B} (R : rel) (phi : Prop) (m1 : M S1 A) (m2 : M S2 B) Q :
  (phi -> rsim R m1 m2 Q) -> rsim (fun s1 mo1 s2 mo2 => R s1 mo1 s2 mo2 /\ phi) m1 m2 Q.
Proof. intros H. eapply rsim_pre; [apply (rsim_pure _ _ _ _ _ _ R phi m1 m2 Q H)|]. intros ? ? ? ? [HR Hphi]. split; assumption. Qed.
Lemma rsimeq_pure_r {A} (R : rel) (phi : Prop) (m1 : M S1 A) (m2 : M S2 A) Q :
  (phi -> rsimeq R m1 m2 Q) -> rsimeq (fun s1 mo1 s2 mo2 => R s1 mo1 s2 mo2 /\ phi) m1 m2 Q.
Proof. intros H. unfold rsimeq. apply rsim_pure_r. exact H. Qed.

Section Target.
Context {P1 P2 : Type}.
(* [comment removed for export] *)
Variable RX : list (P1 * P2 * Z) -> rel.
Variables (malloc1 : Z -> M S1 (option P1)) (malloc2 : Z -> M S2 (option P2)).
Variables (free1 : P1 -> M S1 unit) (free2 : P2 -> M S2 unit).
Variables (nh1 : M S1 Empty_set) (nh2 : M S2 Empty_set).
Variables (emit1 : Z -> M S1 unit) (emit2 : Z -> M S2 unit).

Local Notation sizes := (map (@snd (P1 * P2) Z)).
Local Notation pairs := (map (@fst (P1 * P2) Z)).

(* [comment removed for export] *)
Definition Qm (X : list (P1 * P2 * Z)) (n : Z) (r1 : option P1) (r2 : option P2) : rel :=
  match r1, r2 with
  | Some p, Some q => fun s1 mo1 s2 mo2 => RX ((p, q, n) :: X) s1 mo1 s2 mo2 /\ n < 2^63
  | None, None => RX X
  | _, _ => fun _ _ _ _ => False
  end.

(* [comment removed for export] *)
Hypothesis Hm : forall X n, 0 <= n <= REQMAX -> HISTOK (n :: sizes X) -> rsim (RX X) (malloc1 n) (malloc2 n) (Qm X n).
Hypothesis Hf : forall X p q n, rsim (RX ((p, q, n) :: X)) (free1 p) (free2 q) (fun _ _ => RX X).
Hypothesis Hperm : forall X Y s1 mo1 s2 mo2, Permutation X Y -> RX X s1 mo1 s2 mo2 -> RX Y s1 mo1 s2 mo2.
Hypothesis Hnh : forall X (Q : Empty_set -> Empty_set -> rel), rsim (RX X) nh1 nh2 Q.
Hypothesis Hemit : forall X w, rsimeq (RX X) (emit1 w) (emit2 w) (fun _ => RX X).

Local Ltac ret_same := apply rsimeq_ret; intros ? ? ? ? HH; exact HH.
Local Ltac ret_rel := apply rsim_ret; intros ? ? ? ? HH.

Lemma sizes_app (A B : list (P1 * P2 * Z)) : sizes (A ++ B) = sizes A ++ sizes B. Proof. apply map_app. Qed.

(* [comment removed for export] *)
Lemma HISTOK_amb0 n (Z : list Z) : (length Z <= 3)%nat -> HISTOK (n :: Z).
Proof. intros HL. apply (HISTOK_amb n [] Z); [apply Forall_nil| unfold BCs, zsum; cbn; unfold HB; lia| unfold N4s, N24s, zcount, zlen; cbn; lia| exact HL]. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition olistP (o : option (P1 * P2)) (n : Z) : list (P1 * P2 * Z) :=
  match o with Some pq => [(pq, n)] | None => [] end.

Lemma fuzz_malloc_sim : forall X n, 0 <= n <= REQMAX -> (0 < n -> HISTOK (n :: sizes X)) ->
  rsim (RX X) (fuzz_malloc malloc1 nh1 n) (fuzz_malloc malloc2 nh2 n)
       (fun r1 r2 s1 mo1 s2 mo2 => exists o, r1 = option_map fst o /\ r2 = option_map snd o /\ RX (olistP o n ++ X) s1 mo1 s2 mo2).
Proof.
  intros X n Hn HH0. unfold fuzz_malloc.
  apply rsim_if; intros C.
  - apply Z.ltb_lt in C.
    eapply rsim_bind; [apply Hm; [lia| exact (HH0 C)]|].
    intros [p|] [q|]; cbn beta iota; [| apply rsim_false| apply rsim_false|].
    + apply rsim_drop. ret_rel. exists (Some (p, q)). cbn [option_map fst snd olistP app]. auto.
    + eapply rsim_bind; [apply (Hnh X (fun _ _ _ _ _ _ => False))|]. intros [].
  - ret_rel. exists None. cbn [option_map olistP app]. split; [reflexivity|]. split; [reflexivity|]. exact HH.
Qed.

Lemma free_opt_sim : forall X (o : option (P1 * P2)) n,
  rsimeq (RX (olistP o n ++ X)) (free_opt free1 (option_map fst o)) (free_opt free2 (option_map snd o)) (fun _ => RX X).
Proof.
  intros X [[p q]|] n; cbn [free_opt app option_map olistP fst snd]; [| ret_same].
  unfold rsimeq. eapply rsim_post; [apply Hf|]. intros [] [] ? ? ? ? HH; split; [reflexivity| exact HH].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Local Notation fuzz1 := (Harness.fuzz_one malloc1 free1 nh1).
Local Notation fuzz2 := (Harness.fuzz_one malloc2 free2 nh2).

(* [comment removed for export] *)
Lemma HISTOK_sd3 : forall n (o1 o2 : option (P1 * P2)) X, (length X <= 3)%nat ->
  HISTOK (n :: sizes (olistP o2 DCTX_SIZE ++ olistP o1 PRODUCER_SIZE ++ X)).
Proof.
  intros n o1 o2 X HL. rewrite app_assoc, sizes_app.
  apply HISTOK_amb; [| | | rewrite length_map; exact HL].
  - unfold YWs. rewrite sizes_app. apply Forall_app. split.
    + destruct o2 as [pq|]; cbn; [|constructor]. constructor; [|constructor]. right. exists 23997. unfold DCTX_SIZE. lia.
    + destruct o1 as [pq|]; cbn; [|constructor]. constructor; [|constructor]. right. exists 3. unfold PRODUCER_SIZE. lia.
  - rewrite sizes_app. destruct o2, o1; vm_compute; discriminate.
  - rewrite sizes_app. destruct o2, o1; vm_compute; discriminate.
Qed.

Lemma fuzz_one_sim : forall X data, (length X <= 2)%nat -> zlength data <= MAX_INPUT ->
  rsimeq (RX X) (fuzz1 data) (fuzz2 data) (fun _ => RX X).
Proof.
  intros X data HLX Hd. unfold Harness.fuzz_one.
  pose proof (buff_size_range data ltac:(unfold MAX_INPUT in Hd; lia)) as Hb. unfold BUFF_MAX in Hb.
  eapply rsimeq_bind_r.
  { apply fuzz_malloc_sim; [unfold PRODUCER_SIZE, REQMAX; lia|]. intros _. apply HISTOK_amb0. rewrite length_map. lia. }
  intros pr1 pr2. apply rsimeq_exI. intros o1. apply rsimeq_pure. intros ->. apply rsimeq_pure. intros ->.
  assert (HL3 : (length (olistP o1 PRODUCER_SIZE ++ X) <= 3)%nat) by (rewrite length_app; destruct o1; cbn; lia).
  eapply rsimeq_bind_r.
  { apply fuzz_malloc_sim; [unfold DCTX_SIZE, REQMAX; lia|]. intros _. apply HISTOK_amb0. rewrite length_map. exact HL3. }
  intros dc1 dc2. apply rsimeq_exI. intros o2. apply rsimeq_pure. intros ->. apply rsimeq_pure. intros ->.
  eapply rsimeq_bind_r.
  { apply fuzz_malloc_sim; [unfold REQMAX; lia|]. intros _. apply HISTOK_sd3. lia. }
  intros bf1 bf2. apply rsimeq_exI. intros o3. apply rsimeq_pure. intros ->. apply rsimeq_pure. intros ->.
  eapply rsimeq_seq; [apply free_opt_sim|]. intros _.                                  (* [comment removed for export] *)
  eapply rsimeq_seq.
  { eapply rsimeq_pre; [apply (free_opt_sim (olistP o2 DCTX_SIZE ++ X) o1 PRODUCER_SIZE)|].     (* [comment removed for export] *)
    intros s1 mo1 s2 mo2 H. eapply Hperm; [|exact H]. rewrite !app_assoc. apply Permutation_app_tail. apply Permutation_app_comm. }
  intros _.
  eapply rsimeq_seq; [apply free_opt_sim|]. intros _.                                  (* [comment removed for export] *)
  ret_same.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma run_calls_sim : forall n X payload rc, (length X <= 2)%nat -> zlength payload <= MAX_INPUT ->
  rsimeq (RX X) (run_calls fuzz1 emit1 n payload rc) (run_calls fuzz2 emit2 n payload rc) (fun _ => RX X).
Proof.
  induction n as [|n IH]; intros X payload rc HLX Hp; cbn [run_calls].
  - ret_same.
  - eapply rsimeq_bind; [apply fuzz_one_sim; [exact HLX| exact Hp]|]. intros rc'.
    eapply rsimeq_seq; [apply Hemit|]. intros _.
    apply IH; [exact HLX| exact Hp].
Qed.

(* [comment removed for export] *)
Theorem target_run_sim : forall X cfg payload, (length X <= 1)%nat -> zlength payload <= MAX_INPUT ->
  rsimeq (RX X) (target_run malloc1 free1 fuzz1 emit1 cfg payload) (target_run malloc2 free2 fuzz2 emit2 cfg payload) (fun _ => RX X).
Proof using Hm Hf Hperm Hnh Hemit.
  intros X cfg payload HLX Hp. unfold target_run.
  assert (HL0 : 0 <= zlength payload) by (unfold zlength; lia).
  eapply rsimeq_bind_r with (Q1 := fun a1 a2 => match a1, a2 with
                                               | None, None => RX X
                                               | Some None, Some None => RX X
                                               | Some (Some p), Some (Some q) => RX ((p, q, zlength payload) :: X)
                                               | _, _ => fun _ _ _ _ => False
                                               end).
  { apply rsim_if; intros _; [ret_rel; exact HH|].
    eapply rsim_bind; [apply Hm; [unfold zlength, REQMAX, MAX_INPUT in *; lia| apply HISTOK_amb0; rewrite length_map; lia]|].
    intros [p|] [q|]; cbn [Qm]; [| apply rsim_false| apply rsim_false|]; ret_rel; [exact (proj1 HH)| exact HH]. }
  intros [[p|]|] [[q|]|]; cbn beta iota; try apply rsimeq_false.
  - eapply rsimeq_seq; [apply run_calls_sim; [cbn; lia| exact Hp]|]. intros rc. eapply rsimeq_seq_r; [apply Hf|]. intros _ _. ret_same.
  - eapply rsimeq_seq; [apply run_calls_sim; [lia| exact Hp]|]. intros rc. eapply rsimeq_seq; [ret_same|]. intros _. ret_same.
  - ret_same.
Qed.
End Target.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Driver.
Context {P1 P2 : Type}.
Variables (io1_ : IOStyle S1) (io2_ : IOStyle S2).
Variables (malloc1 : Z -> M S1 (option P1)) (malloc2 : Z -> M S2 (option P2)).
Variables (free1 : P1 -> M S1 unit) (free2 : P2 -> M S2 unit).
Variables (rs1 rs2 : Z).      (* [comment removed for export] *)
Variables (alloc_init1 : Z -> M S1 unit) (alloc_init2 : Z -> M S2 unit).
Variables (run1 : Z -> list Z -> M S1 Z) (run2 : Z -> list Z -> M S2 Z).
Variables (alloc_count1 : M S1 Z) (alloc_count2 : M S2 Z).
Variable RX : list (P1 * P2 * Z) -> rel.

Local Notation sizes := (map (@snd (P1 * P2) Z)).
Local Notation Qm := (Qm RX).
Hypothesis Hm : forall X n, 0 <= n <= REQMAX -> HISTOK (n :: sizes X) -> rsim (RX X) (malloc1 n) (malloc2 n) (Qm X n).
Hypothesis Hf : forall X p q n, rsim (RX ((p, q, n) :: X)) (free1 p) (free2 q) (fun _ _ => RX X).
Hypothesis Hperm : forall X Y s1 mo1 s2 mo2, Permutation X Y -> RX X s1 mo1 s2 mo2 -> RX Y s1 mo1 s2 mo2.
Hypothesis Hdiag : forall X d, diag_short d -> rsimeq (RX X) (io_diag io1_ d) (io_diag io2_ d) (fun _ => RX X).
Hypothesis Hinit : forall X bm, rsimeq (RX X) (alloc_init1 bm) (alloc_init2 bm) (fun _ => RX X).
Hypothesis Hcount : forall X, rsimeq (RX X) alloc_count1 alloc_count2 (fun _ => RX X).
(* [comment removed for export] *)
Hypothesis Hrun : forall X cfg payload, (length X <= 1)%nat -> zlength payload <= MAX_INPUT -> rsimeq (RX X) (run1 cfg payload) (run2 cfg payload) (fun _ => RX X).
Hypothesis Hopen : forall X path, rsimeq (RX X) (msys (NOpen path) dec_open) (msys (NOpen path) dec_open) (fun _ => RX X).
Hypothesis Hclose : forall X fd, rsimeq (RX X) (msys (NClose fd) dec_close) (msys (NClose fd) dec_close) (fun _ => RX X).
Hypothesis Hread : forall X fd buf1 buf2 cnt, 0 <= cnt < 2^64 ->
  rsimeq (RX X) (msys (NRead fd buf1 cnt) (dec_read buf1 cnt)) (msys (NRead fd buf2 cnt) (dec_read buf2 cnt))
         (fun a => match a with RdData bs => fun s1 mo1 s2 mo2 => RX X s1 mo1 s2 mo2 /\ zlength bs <= cnt | RdErr _ => RX X end).

(* [comment removed for export] *)
Definition rd_rel (st1 : @rd_st P1) (st2 : @rd_st P2) : rel := fun s1 mo1 s2 mo2 =>
  RX [(rd_buf st1, rd_buf st2, rd_cap st1)] s1 mo1 s2 mo2 /\ rd_cap st2 = rd_cap st1 /\ rd_content st2 = rd_content st1
  /\ zlength (rd_content st1) <= rd_cap st1 /\ exists k, (k <= 10)%nat /\ rd_cap st1 = 65536 * 2 ^ Z.of_nat k.

Definition QR (r1 : @rd_result P1) (r2 : @rd_result P2) : rel :=
  match r1, r2 with
  | RdExit, RdExit => fun s1 mo1 s2 mo2 => exists X', RX X' s1 mo1 s2 mo2
  | RdDone b1 c1, RdDone b2 c2 => fun s1 mo1 s2 mo2 => (exists cap, RX [(b1, b2, cap)] s1 mo1 s2 mo2) /\ c2 = c1 /\ zlength c1 <= MAX_INPUT
  | _, _ => fun _ _ _ _ => False
  end.

Lemma pow2_le_1024' : forall k, (k <= 10)%nat -> 1 <= 2 ^ Z.of_nat k <= 1024.
Proof. intros k Hk. split; [pose proof (Z.pow_pos_nonneg 2 (Z.of_nat k) ltac:(lia) ltac:(lia)); lia|]. change 1024 with (2 ^ 10). apply Z.pow_le_mono_r; lia. Qed.

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
  apply rsim_pointwise. intros s10 mo10 s20 mo20 (Ho0 & Ecap & Ect & Hlen & (k & Hk & Hcap)). rewrite Ecap, Ect.
  pose proof (pow2_le_1024' k Hk) as Hp2.
  eapply rsim_bind with
    (Q1 := fun g1 g2 => match g1, g2 with
                       | None, None => fun s1 mo1 s2 mo2 => exists X', RX X' s1 mo1 s2 mo2
                       | Some st1', Some st2' => fun s1 mo1 s2 mo2 => rd_rel st1' st2' s1 mo1 s2 mo2 /\ rd_content st1' = rd_content st1 /\ zlength (rd_content st1) < rd_cap st1'
                       | _, _ => fun _ _ _ _ => False
                       end).
  { destruct (Z.eqb_spec (zlength (rd_content st1)) (rd_cap st1)) as [Heq|Hne].
    - destruct (Z.leb_spec MAX_INPUT (rd_cap st1)) as [Hbig|Hsmall].
      + eapply rsim_bind; [eapply rsim_pre; [apply Hdiag; exact I| intros ? ? ? ? (-> & -> & -> & ->); exact Ho0]|].
        intros ? ?. apply rsim_pure. intros _. ret_rel. exists [(rd_buf st1, rd_buf st2, rd_cap st1)]. exact HH.
      + eapply rsim_bind. { eapply (rsim_pre _ _ _ _ _ _ (RX [(rd_buf st1, rd_buf st2, rd_cap st1)])); [apply Hm; [unfold REQMAX, MAX_INPUT in *; lia| apply HISTOK_amb0'; cbn; lia]| intros ? ? ? ? (-> & -> & -> & ->); exact Ho0]. }
        intros [nb1|] [nb2|]; cbn beta iota; [| apply rsim_false| apply rsim_false|].
        * eapply rsim_seq.
          { eapply rsim_pre; [apply (Hf [(nb1, nb2, rd_cap st1 * 2)] (rd_buf st1) (rd_buf st2) (rd_cap st1))|]. intros ? ? ? ? [Ho _]. eapply Hperm; [apply perm_swap| exact Ho]. }
          intros _ _. ret_rel. cbn. unfold rd_rel. cbn.
          assert (Hk9 : (k <= 9)%nat).
          { destruct (Nat.le_gt_cases k 9) as [|Hgt]; [assumption|]. exfalso. assert (k = 10%nat) as -> by lia. unfold MAX_INPUT in Hsmall. cbn in Hcap. lia. }
          splits; auto; try lia.
          exists (S k). split; [lia|]. rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. lia.
        * eapply rsim_bind; [apply Hdiag; exact I|]. intros ? ?. apply rsim_pure. intros _. ret_rel. exists [(rd_buf st1, rd_buf st2, rd_cap st1)]. exact HH.
    - ret_rel. destruct HH as (-> & -> & -> & ->). unfold rd_rel. splits; auto; try lia. exists k; auto. }
  intros [st1'|] [st2'|]; cbn beta iota; [| apply rsim_false| apply rsim_false| ret_rel; exact HH].
  (* [comment removed for export] *)
  apply rsim_pointwise. intros s11 mo11 s21 mo21 ((Ho & Ecap' & Ect' & Hlen' & (k' & Hk' & Hcap')) & Hct & Hlt). rewrite Ecap', Ect', Hct.
  pose proof (pow2_le_1024' k' Hk') as Hp2'.
  set (want0 := rd_cap st1' - zlength (rd_content st1)).
  set (want := if 65536 <? want0 then 65536 else want0).
  assert (Hwant : 0 <= want <= want0 /\ want < 2^64). { subst want want0. destruct (Z.ltb_spec 65536 (rd_cap st1' - zlength (rd_content st1))); lia. }
  eapply rsim_bind_eq.
  { eapply rsim_pre; [apply (Hread [(rd_buf st1', rd_buf st2', rd_cap st1')] fd _ _ want); lia|].
    intros ? ? ? ? (-> & -> & -> & ->). exact Ho. }
  intros [e|bs]; cbn beta iota.
  - eapply rsim_bind; [apply Hdiag; exact Hpath|]. intros ? ?. apply rsim_pure. intros _. ret_rel. exists [(rd_buf st1', rd_buf st2', rd_cap st1')]. exact HH.
  - destruct (length bs =? 0)%nat eqn:C.
    + ret_rel. destruct HH as [Ho' _]. cbn. split; [exists (rd_cap st1'); exact Ho'|]. split; [reflexivity|]. unfold MAX_INPUT in *. lia.
    + ret_rel. destruct HH as [Ho' Hbs]. unfold rd_rel. cbn. rewrite zlength_app', zlength_u8s', ?Hct. splits; auto; [lia| exists k'; auto].
Qed.

Lemma read_all_sim : forall path, zlength path <= PIECE_MAX ->
  rsim (RX []) (read_all io1_ malloc1 free1 rs1 path) (read_all io2_ malloc2 free2 rs2 path) QR.
Proof.
  intros path Hpath. unfold read_all.
  eapply rsim_bind_eq; [apply Hopen|]. intros [e|fd]; cbn beta iota.
  - eapply rsim_bind; [apply Hdiag; exact Hpath|]. intros ? ?. apply rsim_pure. intros _. ret_rel. exists []. exact HH.
  - eapply rsim_bind; [apply Hm; [unfold REQMAX; lia| apply HISTOK_amb0'; cbn; lia]|]. intros [buf1|] [buf2|]; cbn beta iota; [| apply rsim_false| apply rsim_false|].
    2:{ eapply rsim_bind; [apply Hdiag; exact I|]. intros ? ?. apply rsim_pure. intros _. ret_rel. exists []. exact HH. }
    eapply rsim_bind.
    + eapply rsim_pre.
      * apply (rsim_loop step1 step2 nexit nexit Phi1 Phi2 rd_rel QR).
        intros st1 st2. eapply rsim_post; [apply read_loop_body_sim; exact Hpath|]. intros [st1'|r1] [st2'|r2] s1 mo1 s2 mo2 H; exact H.
      * intros s1 mo1 s2 mo2 [Ho _]. unfold rd_rel. cbn. split; [exact Ho|]. split; [reflexivity|]. split; [reflexivity|]. split; [unfold zlength; cbn; lia|]. exists 0%nat. split; [lia| reflexivity].
    + intros [|buf1' c1] [|buf2' c2]; cbn beta iota; [ret_rel; exact HH| apply rsim_false| apply rsim_false|].
      apply rsim_pure_r. intros [-> Hlen].
      eapply rsim_bind with (Q1 := fun _ _ s1 mo1 s2 mo2 => exists cap, RX [(buf1', buf2', cap)] s1 mo1 s2 mo2).
      { apply rsim_exI. intros cap. eapply rsim_post; [apply Hclose|]. intros ? ? ? ? ? ? [_ HR]. exists cap. exact HR. }
      intros ? ?. ret_rel. cbn. auto.
Qed.

Lemma main_model_sim : forall argv, Forall (fun a => zlength a <= PIECE_MAX) argv ->
  rsimeq (RX []) (main_model io1_ malloc1 free1 rs1 alloc_init1 run1 alloc_count1 argv)
                 (main_model io2_ malloc2 free2 rs2 alloc_init2 run2 alloc_count2 argv)
         (fun _ s1 mo1 s2 mo2 => exists X', RX X' s1 mo1 s2 mo2).
Proof.
  intros argv Hargv. unfold main_model.
  assert (Hnth : forall i, zlength (nth i argv []) <= PIECE_MAX).
  { intros i. destruct (nth_in_or_default i argv []) as [Hin| ->]; [exact (proj1 (Forall_forall _ _) Hargv _ Hin)| unfold zlength, PIECE_MAX; cbn; lia]. }
  apply rsimeq_if; intros C.
  { eapply rsimeq_seq; [apply Hdiag; cbn; apply Hnth|]. intros _. apply rsimeq_ret. intros s1 mo1 s2 mo2 Ho. exists []. exact Ho. }
  eapply rsimeq_bind_r; [apply read_all_sim; apply Hnth|]. intros [|buf1 c1] [|buf2 c2]; cbn beta iota; [| apply rsimeq_false| apply rsimeq_false|].
  { apply rsimeq_ret. intros s1 mo1 s2 mo2 [X' Ho]. exists X'. exact Ho. }
  apply rsimeq_pure_r. intros [-> Hlen]. apply rsimeq_exI. intros cap.
  apply rsimeq_if; intros C1.
  { eapply rsimeq_seq; [apply Hdiag; exact I|]. intros _. eapply rsimeq_seq_r; [apply Hf|]. intros _ _. apply rsimeq_ret. intros s1 mo1 s2 mo2 Ho. exists []. exact Ho. }
  apply rsimeq_if; intros C2.
  { eapply rsimeq_seq; [apply Hdiag; exact I|]. intros _. eapply rsimeq_seq_r; [apply Hf|]. intros _ _. apply rsimeq_ret. intros s1 mo1 s2 mo2 Ho. exists []. exact Ho. }
  eapply rsimeq_seq; [apply Hinit|]. intros _.
  eapply rsimeq_seq; [apply (Hrun [(buf1, buf2, cap)]); [cbn; lia|]; etransitivity; [| exact Hlen]; unfold zlength; rewrite length_skipn; lia|]. intros status.
  eapply rsimeq_bind with (Q1 := fun _ => RX [(buf1, buf2, cap)]).
  { destruct (Z.testbit _ 15).
    - eapply rsimeq_seq; [apply Hcount|]. intros n. apply rsimeq_ret. auto.
    - apply rsimeq_ret. auto. }
  intros status'. eapply rsimeq_seq_r; [apply Hf|]. intros _ _. apply rsimeq_ret. intros s1 mo1 s2 mo2 Ho. exists []. exact Ho.
Qed.

Hypothesis Hioexit : forall X, rsimeq (RX X) (io_exit io1_) (io_exit io2_) (fun _ => RX X).
Hypothesis Hexitnode : forall X c (Q : Empty_set -> Empty_set -> rel), rsim (RX X) (msys (NExit c) dec_exit) (msys (NExit c) dec_exit) Q.

Lemma exit_model_sim : forall code (Q : Empty_set -> Empty_set -> rel),
  rsim (fun s1 mo1 s2 mo2 => exists X, RX X s1 mo1 s2 mo2) (exit_model io1_ code) (exit_model io2_ code) Q.
Proof.
  intros code Q. unfold exit_model. apply rsim_exI. intros X.
  eapply rsim_bind; [apply Hioexit|]. intros ? ?. apply rsim_pure. intros _. apply Hexitnode.
Qed.

(* [comment removed for export] *)
Theorem main_exit_sim : forall argv (Q : Empty_set -> Empty_set -> rel), Forall (fun a => zlength a <= PIECE_MAX) argv ->
  rsim (RX []) (code <- main_model io1_ malloc1 free1 rs1 alloc_init1 run1 alloc_count1 argv ;; exit_model io1_ code)
               (code <- main_model io2_ malloc2 free2 rs2 alloc_init2 run2 alloc_count2 argv ;; exit_model io2_ code) Q.
Proof.
  intros argv Q Hargv. eapply rsim_bind; [apply main_model_sim; exact Hargv|]. intros c1 c2.
  apply rsim_pure. intros <-. apply exit_model_sim.
Qed.
End Driver.

End Prog.
