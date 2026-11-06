From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09 YO0g.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import Img0 Contract ContractT AllocPack AllocPack3
  AllocPack3Room AllocBound AllocPack3Ag.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog.CF Require Import SlotInv SlotSteps SlotRes.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import SlotCaps3.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog.CF Require Import SlotRI3.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import RelayRunT RelayRunF ListTr.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog.CF Require Import SlotRun3 SlotFitAg.
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog.CF Require Import SRCF SRCF3.
Import ListNotations.
Local Open Scope Z_scope.

Definition RI3P (OK : astate -> Prop) : res_inv := fun E k V L A => RI3_reply E k V L A /\ OK A.

Lemma RI3P_mono OK : RI_mono (RI3P OK).
Proof.
  intros E k k' V L A [H HO] Hk. split; [exact (RI3_mono E k k' V L A H Hk)|exact HO].
Qed.

Definition RMH (RM : pbound3 -> Z -> Prop) : Prop := forall pl b n, p3_cap b = CS_reply pl -> p3_mcap b = MC_reply ->
  0 <= n <= NMAX -> p3_bytes b + n <= CF_MAX -> RM b n.

Lemma RMH_RM_ag : RMH RM_ag.
Proof. intros pl b n. exact (RMH_ag pl b n). Qed.

Lemma room_run_and (R P : Type) (pdef : P) (rmal : R -> Z -> R) (rfre : R -> Z -> P -> R)
    (rrea : R -> Z -> Z -> P -> P -> R) (R1 R2 : R -> Z -> Prop) qs b j tr :
  room_from R P pdef rmal rfre rrea (fun b n => R1 b n /\ R2 b n) qs b j tr <->
  room_from R P pdef rmal rfre rrea R1 qs b j tr /\ room_from R P pdef rmal rfre rrea R2 qs b j tr.
Proof.
  revert b j. induction tr as [|e tr IH]; intros b j; [cbn [room_from]; tauto|].
  destruct e; cbn [room_from]; rewrite ?IH; tauto.
Qed.

Lemma room_from_true (R P : Type) (pdef : P) (rmal : R -> Z -> R) (rfre : R -> Z -> P -> R)
    (rrea : R -> Z -> Z -> P -> P -> R) qs b j tr :
  room_from R P pdef rmal rfre rrea (fun _ _ => True) qs b j tr.
Proof.
  revert b j. induction tr as [|e tr IH]; intros b j; [exact I|].
  destruct e; cbn [room_from]; try split; first [exact I | apply IH].
Qed.

Lemma roomF_pack3P OK RM qs (b : pbound3) tr : roomF (pack3P OK RM) qs b tr <-> roomF pack3_form qs b tr /\
  room_run pbound3 sptr (SP 0 0) pb3_malloc pb3_free pb3_realloc RM qs b tr.
Proof.
  exact (room_run_and pbound3 sptr (SP 0 0) pb3_malloc pb3_free pb3_realloc room_pack3 RM qs b 0 tr).
Qed.

Lemma runF_pack3P OK RM qs (b : pbound3) tr : runF (pack3P OK RM) qs b tr = runF pack3_form qs b tr.
Proof. reflexivity. Qed.

Lemma res_tr_pack3P_true P A tr :
  res_tr (pack3P (fun _ => True) (fun _ _ => True)) P A tr <-> res_tr pack3_form P A tr.
Proof.
  unfold res_tr. split.
  - intros (bnd & (HR & _) & HRo & HP). exists bnd. split; [exact HR|]. split.
    + intros qs Hq. exact (proj1 (proj1 (roomF_pack3P _ _ qs bnd tr) (HRo qs Hq))).
    + intros L' A' qs Hq HR'. apply (HP L' A' qs Hq). split; [exact HR'|exact I].
  - intros (bnd & HR & HRo & HP). exists bnd. split; [split; [exact HR|exact I]|]. split.
    + intros qs Hq. apply (proj2 (roomF_pack3P (fun _ => True) (fun _ _ => True) qs bnd tr)).
      split; [exact (HRo qs Hq)|]. unfold room_run. apply room_from_true.
    + intros L' A' qs Hq (HR' & _). exact (HP L' A' qs Hq HR').
Qed.

Definition tr_peak (tr : trF) (Bd : Z) : Prop := forall tr1 e tr2, tr = tr1 ++ e :: tr2 ->
  match e with RMalloc n | RRealloc _ n _ => 0 <= n <= NMAX /\ tr_db tr1 + n <= Bd | RFree _ _ => True end.

Lemma tr_db_nil : tr_db [] = 0.
Proof. reflexivity. Qed.

Lemma tr_db_cons e tr : tr_db (e :: tr) = ev_db e + tr_db tr.
Proof. reflexivity. Qed.

Lemma tr_peak_nil Bd : tr_peak [] Bd.
Proof. intros tr1 e tr2 E. destruct tr1; discriminate E. Qed.

Lemma tr_peak_cons e tr Bd : tr_peak (e :: tr) Bd <->
  match e with RMalloc n | RRealloc _ n _ => 0 <= n <= NMAX /\ n <= Bd | RFree _ _ => True end /\
  tr_peak tr (Bd - ev_db e).
Proof.
  split.
  - intros H. split.
    + pose proof (H [] e tr eq_refl) as H0.
      destruct e; cbv beta iota in H0 |- *; rewrite ?tr_db_nil in H0; first [exact I | lia].
    + intros tr1 e' tr2 E. pose proof (H (e :: tr1) e' tr2 ltac:(rewrite E; reflexivity)) as H1.
      destruct e'; cbv beta iota in H1 |- *; rewrite ?tr_db_cons in H1; first [exact I | lia].
  - intros [H0 H] tr1 e' tr2 E. destruct tr1 as [|x tr1].
    + cbn [app] in E. injection E as E1 E2. rewrite <- E1.
      destruct e; cbv beta iota in H0 |- *; rewrite ?tr_db_nil; first [exact I | lia].
    + cbn [app] in E. injection E as E1 E2. pose proof (H tr1 e' tr2 E2) as H1. rewrite <- E1.
      destruct e'; cbv beta iota in H1 |- *; rewrite ?tr_db_cons; first [exact I | lia].
Qed.

Lemma tr_peak_app t1 t2 Bd : tr_peak t1 Bd -> tr_peak t2 (Bd - tr_db t1) -> tr_peak (t1 ++ t2) Bd.
Proof.
  revert Bd. induction t1 as [|e t1 IH]; intros Bd H1 H2.
  - cbn [app]. rewrite tr_db_nil in H2. replace (Bd - 0) with Bd in H2 by lia. exact H2.
  - cbn [app]. apply tr_peak_cons in H1 as [H0 H1]. apply tr_peak_cons. split; [exact H0|].
    apply IH; [exact H1|]. rewrite tr_db_cons in H2. replace (Bd - ev_db e - tr_db t1) with (Bd - (ev_db e + tr_db t1))
      by lia. exact H2.
Qed.

Lemma tr_peak_free n a Bd : tr_peak [RFree n a] Bd.
Proof. apply tr_peak_cons. split; [exact I|apply tr_peak_nil]. Qed.

Lemma RMrun_of_peak RM pl b tr Bd : RMH RM -> p3_cap b = CS_reply pl -> p3_mcap b = MC_reply ->
  p3_bytes b + Bd <= CF_MAX -> tr_peak tr Bd ->
  forall qs, room_run pbound3 sptr (SP 0 0) pb3_malloc pb3_free pb3_realloc RM qs b tr.
Proof.
  intros HRM HC HM HB HP qs. unfold room_run.
  enough (G : forall j, room_from pbound3 sptr (SP 0 0) pb3_malloc pb3_free pb3_realloc RM qs b j tr)
    by exact (G 0%nat).
  revert b Bd HC HM HB HP.
  induction tr as [|e tr IH]; intros b Bd HC HM HB HP j; [exact I|].
  apply tr_peak_cons in HP as [H0 HP].
  pose proof (run3_cap qs b j [e]) as Hc1. pose proof (run3_mcap qs b j [e]) as Hc2.
  pose proof (run3_bytes qs b j [e]) as Hc3. rewrite tr_db_one in Hc3.
  destruct e as [n|n a|k n a]; cbn [run_from ev_db] in Hc1, Hc2, Hc3, HP; cbn [room_from]; cbv beta iota in H0.
  - split; [apply (HRM pl b n HC HM); lia|].
    apply IH with (Bd := Bd - n); [rewrite Hc1; exact HC|rewrite Hc2; exact HM|lia|exact HP].
  - apply IH with (Bd := Bd - - n); [rewrite Hc1; exact HC|rewrite Hc2; exact HM|lia|exact HP].
  - split; [apply (HRM pl b n HC HM); lia|].
    apply IH with (Bd := Bd - (n - k)); [rewrite Hc1; exact HC|rewrite Hc2; exact HM|lia|exact HP].
Qed.
