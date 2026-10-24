(** Transfer pure instruction proofs between register maps with the same
    observable values. No canonical-map premise is added to the driver. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib
  Require Import Exec MState Regs6ss.
Import ListNotations.

Definition canonical_register_state (ms : machine_state) : machine_state :=
  {| ms_regs := mkR_of (ms_regs ms); ms_fregs := ms_fregs ms;
     ms_pc_val := ms_pc_val ms; ms_svc_pending := ms_svc_pending ms;
     ms_resv := ms_resv ms; ms_fcsr := ms_fcsr ms;
     ms_mem := ms_mem ms; ms_rom := ms_rom ms |}.

Lemma canonical_register_state_eqv : forall ms,
  ms_eqv ms (canonical_register_state ms).
Proof.
  intros ms. unfold ms_eqv,canonical_register_state. cbn.
  split; [apply mkR_of_eqv|]. repeat split; reflexivity.
Qed.

Lemma step_register_eqv : forall segs ms ms', ms_eqv ms ms' ->
  res_eqv (RiscvSemantics.step segs ms) (RiscvSemantics.step segs ms').
Proof.
  intros segs ms ms' H. pose proof (step_accesses_eqv segs ms ms' H) as K.
  unfold RiscvSemantics.step.
  destruct (RiscvSemantics.step_accesses segs ms) as [a| |];
  destruct (RiscvSemantics.step_accesses segs ms') as [b| |];
  cbn [rep_eqv res_eqv drop_access_report] in *; try contradiction; try exact I.
  exact (proj1 K).
Qed.

Lemma mstep_register_transport : forall segs ms ms' next,
  ms_eqv ms ms' -> mstep segs ms next ->
  exists next', mstep segs ms' next' /\ ms_eqv next next'.
Proof.
  intros segs ms ms' next H [HP HS].
  pose proof (step_register_eqv segs ms ms' H) as K.
  rewrite HS in K. destruct (RiscvSemantics.step segs ms') as [next'| |] eqn:E;
    cbn [res_eqv] in K; try contradiction.
  exists next'. split; [|exact K]. split; [|exact E].
  destruct H as (_ & _ & _ & Hsvc & _). rewrite <- Hsvc. exact HP.
Qed.

Theorem msteps_register_transport : forall segs ms final,
  msteps segs ms final -> forall ms', ms_eqv ms ms' ->
  exists final', msteps segs ms' final' /\ ms_eqv final final'.
Proof.
  intros segs ms final H. induction H as [ms|ms mid final HS HT IH]; intros ms' HE.
  - exists ms'. split; [constructor|exact HE].
  - destruct (mstep_register_transport segs ms ms' mid HE HS) as [mid' [HS' HE']].
    destruct (IH mid' HE') as [final' [HT' HF]].
    exists final'. split; [econstructor; eassumption|exact HF].
Qed.

Theorem evt_register_transport : forall segs (Q : machine_state -> Prop) ms ms',
  ms_eqv ms ms' -> evt segs Q ms ->
  evt segs (fun actual => exists canonical, Q canonical /\ ms_eqv canonical actual) ms'.
Proof.
  intros segs Q ms ms' HE [final [HS HQ]].
  destruct (msteps_register_transport segs ms final HS ms' HE) as [final' [HS' HF]].
  exists final'. split; [exact HS'|]. exists final. split; assumption.
Qed.

Theorem canonical_contract_transport : forall segs (Q : machine_state -> Prop) ms,
  evt segs Q (canonical_register_state ms) ->
  evt segs (fun actual => exists canonical, Q canonical /\ ms_eqv canonical actual) ms.
Proof.
  intros segs Q ms H. eapply evt_register_transport; [|exact H].
  apply ms_eqv_sym,canonical_register_state_eqv.
Qed.
