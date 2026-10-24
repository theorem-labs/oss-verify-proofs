(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib Require Import PropExec MState Frame.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib Require Import Acfg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition xregs_eqv (R R' : bvmap 5 word) : Prop :=
  forall r : reg, is_x0 r = false -> reg_get R r = reg_get R' r.

(* [comment removed for export] *)
Lemma xregs_eqv_sym : forall R R', xregs_eqv R R' -> xregs_eqv R' R.
Proof. intros R R' H r Hr. symmetry. apply H. exact Hr. Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma reg_get_set : forall (R : bvmap 5 word) (k r : reg) v,
  reg_get (bvmap_set k v R) r = if bv_eqb k r then v else reg_get R r.
Proof.
  intros R k r v. destruct (bv_eqb k r) eqn:E.
  - apply bv_eqb_eq in E. subst. apply reg_get_set_same.
  - apply reg_get_set_other. intros ->. rewrite bv_eqb_refl in E. discriminate.
Qed.

Lemma xregs_eqv_set : forall R R' (k : reg) v,
  xregs_eqv R R' -> xregs_eqv (bvmap_set k v R) (bvmap_set k v R').
Proof. intros R R' k v H r Hr. rewrite !reg_get_set. destruct (bv_eqb k r); [reflexivity|apply H; exact Hr]. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition core_eqv (c c' : core) : Prop :=
  xregs_eqv (c_regs c) (c_regs c') /\ c_fregs c = c_fregs c' /\
  c_pc c = c_pc c' /\ c_fcsr c = c_fcsr c' /\ c_resv c = c_resv c'.

(* [comment removed for export] *)
Inductive eff_eqv : eff -> eff -> Prop :=
| EqvDone : forall c c', core_eqv c c' -> eff_eqv (EDone c) (EDone c')
| EqvIllegal : forall c c', eff_eqv (EIllegal c) (EIllegal c')
| EqvDefinedIllegal : forall c c', eff_eqv (EDefinedIllegal c) (EDefinedIllegal c')   (* [comment removed for export] *)
| EqvEcall : forall c c', eff_eqv (EEcall c) (EEcall c')
| EqvEbreak : forall c c', eff_eqv (EEbreak c) (EEbreak c')
| EqvFault : forall c c', eff_eqv (EFault c) (EFault c')
| EqvLoad : forall n a k k', (forall v, eff_eqv (k v) (k' v)) -> eff_eqv (ELoad n a k) (ELoad n a k')
| EqvStore : forall n a v k k', eff_eqv k k' -> eff_eqv (EStore n a v k) (EStore n a v k').

Lemma core_eqv_mk : forall R R' F pc fc rv, xregs_eqv R R' ->
  core_eqv (Core R F pc fc rv) (Core R' F pc fc rv).
Proof. intros. repeat split; assumption. Qed.

(* [comment removed for export] *)
Lemma rget_eqv : forall R R' F pc fc rv, xregs_eqv R R' ->
  forall r, rget (Core R F pc fc rv) r = rget (Core R' F pc fc rv) r.
Proof.
  intros R R' F pc fc rv H r. unfold rget. cbn [c_regs].
  destruct (is_x0 r) eqn:E; [reflexivity| apply H; exact E].
Qed.

Local Ltac core_tac :=
  unfold core_eqv, rset, fset, with_regs, with_fregs, with_pc, with_fcsr, with_resv,
         accrue, fwrite, inval_resv in *; simpl in *.

Lemma core_eqv_rset : forall r v c c', core_eqv c c' -> core_eqv (rset r v c) (rset r v c').
Proof.
  intros r v [R F p f s] [R' F' p' f' s'] H. core_tac. destruct H as (HR & -> & -> & -> & ->).
  destruct (is_x0 r); simpl; repeat split; auto using xregs_eqv_set.
Qed.
Lemma core_eqv_fset : forall r v c c', core_eqv c c' -> core_eqv (fset r v c) (fset r v c').
Proof.
  intros r v [R F p f s] [R' F' p' f' s'] H. core_tac. destruct H as (HR & -> & -> & -> & ->).
  repeat split; auto.
Qed.
Lemma core_eqv_with_pc : forall v c c', core_eqv c c' -> core_eqv (with_pc v c) (with_pc v c').
Proof. intros v [R F p f s] [R' F' p' f' s'] H. core_tac. destruct H as (HR & -> & -> & -> & ->). repeat split; auto. Qed.
Lemma core_eqv_with_fcsr : forall v c c', core_eqv c c' -> core_eqv (with_fcsr v c) (with_fcsr v c').
Proof. intros v [R F p f s] [R' F' p' f' s'] H. core_tac. destruct H as (HR & -> & -> & -> & ->). repeat split; auto. Qed.
Lemma core_eqv_with_resv : forall v c c', core_eqv c c' -> core_eqv (with_resv v c) (with_resv v c').
Proof. intros v [R F p f s] [R' F' p' f' s'] H. core_tac. destruct H as (HR & -> & -> & -> & ->). repeat split; auto. Qed.
Lemma core_eqv_accrue : forall fl c c', core_eqv c c' -> core_eqv (accrue fl c) (accrue fl c').
Proof. intros fl [R F p f s] [R' F' p' f' s'] H. core_tac. destruct H as (HR & -> & -> & -> & ->). repeat split; auto. Qed.
Lemma core_eqv_fwrite : forall fmt r v c c', core_eqv c c' -> core_eqv (fwrite fmt r v c) (fwrite fmt r v c').
Proof. intros fmt r v c c' H. destruct fmt; apply core_eqv_fset; exact H. Qed.
Lemma core_eqv_inval_resv : forall a c c', core_eqv c c' -> core_eqv (inval_resv a c) (inval_resv a c').
Proof.
  intros a [R F p f s] [R' F' p' f' s'] H. core_tac. destruct H as (HR & -> & -> & -> & ->).
  destruct s' as [r|]; [destruct (Z.eqb _ _)|]; simpl; repeat split; auto.
Qed.
Lemma core_eqv_if : forall (b : bool) c1 c1' c2 c2',
  core_eqv c1 c1' -> core_eqv c2 c2' -> core_eqv (if b then c1 else c2) (if b then c1' else c2').
Proof. intros [] c1 c1' c2 c2' H1 H2; assumption. Qed.

(* [comment removed for export] *)
Local Ltac solve_core HR :=
  repeat first [ apply core_eqv_rset | apply core_eqv_fset | apply core_eqv_with_pc
               | apply core_eqv_with_fcsr | apply core_eqv_with_resv | apply core_eqv_accrue
               | apply core_eqv_fwrite | apply core_eqv_inval_resv | apply core_eqv_if
               | match goal with |- core_eqv (match ?X with _ => _ end) _ => destruct X end ];
  apply (core_eqv_mk _ _ _ _ _ _ HR).

Local Ltac eqv_struct HR :=
  repeat first
    [ apply EqvDone; solve_core HR
    | apply EqvIllegal | apply EqvDefinedIllegal | apply EqvEcall | apply EqvEbreak | apply EqvFault
    | apply EqvLoad; intros ?
    | apply EqvStore
    | match goal with |- eff_eqv (match ?X with _ => _ end) _ => destruct X end
    | match goal with |- eff_eqv (match ?X with _ => _ end _) _ => destruct X end ].

(* [comment removed for export] *)
Local Ltac unfold_exec :=
  cbv beta iota zeta delta [exec fget fread c_regs c_fregs c_pc c_fcsr c_resv
                            with_pc load_val store_val exec_csr resolve_rm frm_of].

(* [comment removed for export] *)
Lemma exec_eqv_core : forall R R' F pc fc rv sz i,
  xregs_eqv R R' ->
  eff_eqv (exec sz i (Core R F pc fc rv)) (exec sz i (Core R' F pc fc rv)).
Proof.
  intros R R' F pc fc rv sz i HR.
  pose proof (rget_eqv R R' F pc fc rv HR) as HG.
  destruct i; unfold_exec; rewrite ?HG; eqv_struct HR.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition ms_eqv (ms ms' : machine_state) : Prop :=
  xregs_eqv (ms_regs ms) (ms_regs ms') /\ ms_fregs ms = ms_fregs ms' /\
  ms_pc_val ms = ms_pc_val ms' /\ ms_svc_pending ms = ms_svc_pending ms' /\
  ms_resv ms = ms_resv ms' /\ ms_fcsr ms = ms_fcsr ms' /\
  ms_mem ms = ms_mem ms' /\ ms_rom ms = ms_rom ms'.

(* [comment removed for export] *)
Lemma ms_eqv_sym : forall ms ms', ms_eqv ms ms' -> ms_eqv ms' ms.
Proof.
  intros ms ms' (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8).
  repeat split; auto using xregs_eqv_sym; congruence.
Qed.
(* [comment removed for export] *)

Definition res_eqv (r r' : machine_result machine_state) : Prop :=
  match r, r' with
  | MachineOk a, MachineOk b => ms_eqv a b
  | MachineFault, MachineFault => True
  | MachineUnmodeled, MachineUnmodeled => True
  | _, _ => False
  end.

(* [comment removed for export] *)
Definition rep_eqv (r r' : machine_result (access_report machine_state)) : Prop :=
  match r, r' with
  | MachineOk a, MachineOk b => ms_eqv (@access_value _ a) (@access_value _ b)
                                /\ @accessed_ranges _ a = @accessed_ranges _ b
  | MachineFault, MachineFault => True
  | MachineUnmodeled, MachineUnmodeled => True
  | _, _ => False
  end.

Lemma ms_reg_eqv : forall ms ms' r, ms_eqv ms ms' -> ms_reg ms r = ms_reg ms' r.
Proof.
  intros ms ms' r (HR & _). unfold ms_reg. destruct (bv_eqb r 0) eqn:E; [reflexivity|].
  apply HR. unfold is_x0. apply Z.eqb_neq. intros H0. 
  assert (r = 0%bv) by (apply bv_eq; rewrite H0; reflexivity). subst r. rewrite bv_eqb_refl in E. discriminate.
Qed.

Section WithSegs.
Variable segs : list Segment.

Lemma interp_eff_accesses_eqv : forall t t', eff_eqv t t' -> forall m,
  match interp_eff_accesses segs t m, interp_eff_accesses segs t' m with
  | MachineOk a, MachineOk b =>
      core_eqv (fst (@access_value _ a)) (fst (@access_value _ b))
      /\ snd (@access_value _ a) = snd (@access_value _ b)
      /\ @accessed_ranges _ a = @accessed_ranges _ b
  | MachineFault, MachineFault => True
  | MachineUnmodeled, MachineUnmodeled => True
  | _, _ => False
  end.
Proof.
  intros t t' H. induction H; intros m; cbn [interp_eff_accesses]; auto.
  - destruct (ov_read_bytes segs m a (width_bytes n)) as [bs|]; [|exact I].
    specialize (H0 (bv_extract 0 n (le_bytes_to_word bs)) m).
    destruct (interp_eff_accesses segs (k _) m) as [ra| |]; destruct (interp_eff_accesses segs (k' _) m) as [rb| |];
      cbn [access_value accessed_ranges] in *; try exact H0; try contradiction.
    destruct H0 as (C & S & ->). repeat split; try apply C; exact S.
  - destruct (store_ok segs m a (width_bytes n)); [|exact I].
    specialize (IHeff_eqv (write_to_mem m a (Z_to_le_bytes (width_bytes n) (bv_unsigned v)))).
    destruct (interp_eff_accesses segs k _) as [ra| |]; destruct (interp_eff_accesses segs k' _) as [rb| |];
      cbn [access_value accessed_ranges] in *; try exact IHeff_eqv; try contradiction.
    destruct IHeff_eqv as (C & S & ->). repeat split; try apply C; exact S.
Qed.


Lemma decode_exec_accesses_eqv : forall ms ms' w, ms_eqv ms ms' ->
  rep_eqv (decode_exec_accesses segs ms w) (decode_exec_accesses segs ms' w).
Proof.
  intros ms ms' w Heqv. pose proof (ms_reg_eqv ms ms' 17 Heqv) as H17.
  destruct ms as [R F pc svc rv fc m ro], ms' as [R' F' pc' svc' rv' fc' m' ro'].
  destruct Heqv as (HR & HF & Hpc & Hsvc & Hrv & Hfc & Hm & Hro); simpl in *; subst.
  unfold decode_exec_accesses. destruct (is_ecall w).
  - simpl. rewrite H17. repeat split; assumption.
  - destruct (decode_any w) as [[i isz]|]; [| destruct (is_defined_illegal w); exact I]. simpl.
    pose proof (interp_eff_accesses_eqv _ _ (exec_eqv_core R R' F' pc' fc' rv' (Z_to_bv 64 isz) i HR) m') as K.
    destruct (interp_eff_accesses segs (exec _ i (Core R F' pc' fc' rv')) m') as [[[c m1] acc]| |];
    destruct (interp_eff_accesses segs (exec _ i (Core R' F' pc' fc' rv')) m') as [[[c' m1'] acc']| |];
    simpl in *; try exact K; try contradiction.
    destruct K as ((H1 & H2 & H3 & H4 & H5) & -> & ->). repeat split; simpl; auto.
Qed.

Lemma step_accesses_eqv : forall ms ms', ms_eqv ms ms' ->
  rep_eqv (RiscvSemantics.step_accesses segs ms) (RiscvSemantics.step_accesses segs ms').
Proof.
  intros ms ms' Heqv. pose proof Heqv as (_ & _ & Hpc & _ & _ & _ & Hm & _).
  unfold RiscvSemantics.step_accesses, ms_pc. rewrite <- Hpc, <- Hm.
  destruct (fetch_word segs (ms_pc_val ms)); [apply decode_exec_accesses_eqv; exact Heqv|].
  destruct (fetch_word_ov segs (ms_mem ms) (ms_pc_val ms)); [apply decode_exec_accesses_eqv; exact Heqv|].
  destruct (fetch_tail_any segs (ms_mem ms) (ms_pc_val ms)); [apply decode_exec_accesses_eqv; exact Heqv|].
  unfold fetch_failure. destruct (negb _); [exact I|]. destruct (_ || _)%bool; exact I.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma syscall_args_eqv : forall ms ms', ms_eqv ms ms' -> syscall_args ms = syscall_args ms'.
Proof.
  intros ms ms' (HR & _). unfold syscall_args, ms_gpr.
  rewrite !HR by reflexivity. reflexivity.
Qed.

Lemma sys_input_eqv : forall ms ms' x8, ms_eqv ms ms' -> sys_input segs ms x8 = sys_input segs ms' x8.
Proof.
  intros ms ms' x8 Heqv. pose proof (syscall_args_eqv ms ms' Heqv) as Ha.
  destruct ms as [R F pc svc rv fc m ro], ms' as [R' F' pc' svc' rv' fc' m' ro'].
  destruct Heqv as (HR & HF & Hpc & Hsvc & Hrv & Hfc & Hm & Hro); simpl in *; subst.
  unfold sys_input. rewrite Ha. reflexivity.
Qed.

Lemma apply_effect_eqv : forall ms ms' eff, ms_eqv ms ms' ->
  ms_eqv (apply_effect ms eff) (apply_effect ms' eff).
Proof.
  intros [R F pc svc rv fc m ro] [R' F' pc' svc' rv' fc' m' ro'] eff
         (HR & HF & Hpc & Hsvc & Hrv & Hfc & Hm & Hro); simpl in *; subst.
  unfold apply_effect, set_reg; simpl. repeat split; simpl; auto using xregs_eqv_set.
Qed.

Lemma advance_past_svc_eqv : forall ms ms', ms_eqv ms ms' ->
  ms_eqv (advance_past_svc ms) (advance_past_svc ms').
Proof.
  intros [R F pc svc rv fc m ro] [R' F' pc' svc' rv' fc' m' ro']
         (HR & HF & Hpc & Hsvc & Hrv & Hfc & Hm & Hro); simpl in *; subst.
  unfold advance_past_svc, ms_pc; simpl. repeat split; auto.
Qed.

Definition cfg_eqv (c c' : config) : Prop :=
  ms_eqv (cfg_ms c) (cfg_ms c') /\ cfg_model c = cfg_model c'.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition to_eqv (X X' : step_to) : Prop :=
  match X, X' with
  | SError, SError => True
  | SNext c, SNext c' => cfg_eqv c c'
  | _, _ => False
  end.

(* [comment removed for export] *)
Definition with_ms_regs (R : bvmap 5 word) (ms : machine_state) : machine_state :=
  {| ms_regs := R; ms_fregs := ms_fregs ms; ms_pc_val := ms_pc_val ms;
     ms_svc_pending := ms_svc_pending ms; ms_resv := ms_resv ms; ms_fcsr := ms_fcsr ms;
     ms_mem := ms_mem ms; ms_rom := ms_rom ms |}.

(* [comment removed for export] *)
Definition xport_cfg (ms ms' : machine_state) (cX : config) : config :=
  mkCfg
    (match ms_svc_pending ms with
     | None => match RiscvSemantics.step segs ms' with MachineOk s => s | _ => ms' end
     | Some _ =>
         match m_halted (cfg_model cX) with
         | Some _ => ms'
         | None => with_ms_regs (bvmap_set 10 (reg_get (ms_regs (cfg_ms cX)) 10) (ms_regs ms')) (cfg_ms cX)
         end
     end) (cfg_model cX).

Definition xport (ms ms' : machine_state) (X : step_to) : step_to :=
  match X with
  | SError => SError
  | SNext cX => SNext (xport_cfg ms ms' cX)
  end.

Lemma materialize_halted : forall m acc m',
  materialize_model_accesses m acc = Some m' -> m_halted m' = m_halted m.
Proof.
  intros m acc m' H. pose proof (materialize_model_accesses_frame m acc m' H) as (_ & _ & _ & _ & _ & Hp & _).
  unfold m_halted. rewrite Hp. reflexivity.
Qed.

Lemma sstep_xport : forall ms ms' mo evs X, ms_eqv ms ms' ->
  sstep_cfg segs ACFG (mkCfg ms mo) evs X ->
  sstep_cfg segs ACFG (mkCfg ms' mo) evs (xport ms ms' X) /\ to_eqv X (xport ms ms' X).
Proof.
  intros ms ms' mo evs X Heqv Hst.
  pose proof (step_accesses_eqv ms ms' Heqv) as Hrep.
  pose proof Heqv as (_ & _ & _ & Hsvc & _ & _ & _ & _).
  inversion Hst; subst.
  - (* [comment removed for export] *)
    unfold mi_account_step in H5.
    destruct (RiscvSemantics.step_accesses segs ms) as [[msa acc]| |] eqn:E; try discriminate.
    cbn [access_value accessed_ranges] in H5.
    destruct (materialize_model_accesses mo acc) as [mo1|] eqn:M; [|discriminate].
    inversion H5; subst.
    destruct (RiscvSemantics.step_accesses segs ms') as [[msb acc']| |] eqn:E'; cbn in Hrep; try contradiction.
    destruct Hrep as [Hab <-].
    assert (HS : RiscvSemantics.step segs ms' = MachineOk msb).
    { unfold RiscvSemantics.step. rewrite E'. reflexivity. }
    unfold xport, xport_cfg; cbn [cfg_ms cfg_model]. match goal with Hs : ms_svc_pending ms = None |- _ => rewrite Hs end. rewrite HS.
    split; [| split; [exact Hab| reflexivity]].
    apply sstep_cfg_instr; [assumption| congruence|].
    unfold mi_account_step. rewrite E'. cbn [access_value accessed_ranges]. rewrite M. reflexivity.
  - unfold mi_account_step in H5.
    destruct (RiscvSemantics.step_accesses segs ms) as [[msa acc]| |] eqn:E; try discriminate.
    + cbn [access_value accessed_ranges] in H5.
      destruct (materialize_model_accesses mo acc) as [mo1|] eqn:M; [discriminate|].
      destruct (RiscvSemantics.step_accesses segs ms') as [[msb acc']| |] eqn:E'; cbn in Hrep; try contradiction.
      destruct Hrep as [Hab <-].
      unfold xport, xport_cfg; cbn [cfg_ms cfg_model]. split; [|exact I].
      apply sstep_cfg_instr_fault; [assumption| congruence|].
      unfold mi_account_step. rewrite E'. cbn [access_value accessed_ranges]. rewrite M. reflexivity.
    + destruct (RiscvSemantics.step_accesses segs ms') as [b| |] eqn:E'; cbn in Hrep; try contradiction.
      unfold xport, xport_cfg; cbn [cfg_ms cfg_model]. split; [|exact I].
      apply sstep_cfg_instr_fault; [assumption| congruence|]. unfold mi_account_step. rewrite E'. reflexivity.
  - unfold mi_account_step in H5.
    destruct (RiscvSemantics.step_accesses segs ms) as [[msa acc]| |] eqn:E; try discriminate.
    + cbn [access_value accessed_ranges] in H5. destruct (materialize_model_accesses mo acc); discriminate.
    + destruct (RiscvSemantics.step_accesses segs ms') as [b| |] eqn:E'; cbn in Hrep; try contradiction.
      unfold xport, xport_cfg; cbn [cfg_ms cfg_model]. split; [|exact I].
      apply sstep_cfg_instr_unmodeled; [assumption| congruence|]. unfold mi_account_step. rewrite E'. reflexivity.
  - (* [comment removed for export] *)
    unfold xport, xport_cfg; cbn [cfg_ms cfg_model]. match goal with Hs : ms_svc_pending ms = Some _ |- _ => rewrite Hs end.
    match goal with Hm : materialize_model_accesses _ _ = Some _ |- _ => rewrite (materialize_halted _ _ _ Hm) end.
    match goal with Hh : m_halted model' = None |- _ => rewrite Hh end.
    assert (EQ : with_ms_regs (bvmap_set 10 (reg_get (ms_regs (advance_past_svc (apply_effect ms eff))) 10) (ms_regs ms'))
                              (advance_past_svc (apply_effect ms eff))
                 = advance_past_svc (apply_effect ms' eff)).
    { destruct ms as [R F pc svc rv fc m ro], ms' as [R' F' pc' svc' rv' fc' m' ro'].
      destruct Heqv as (HR & HF & Hpc & Hsvc' & Hrv & Hfc & Hm & Hro); simpl in *; subst.
      unfold with_ms_regs, advance_past_svc, apply_effect, set_reg, ms_pc; simpl.
      unfold reg_get. rewrite bvmap_get_set_same. reflexivity. }
    rewrite EQ. split.
    + apply (sstep_cfg_syscall segs ACFG ms' mo x8 eff model' model'' evs);
        [assumption| congruence| rewrite <- (sys_input_eqv ms ms' x8 Heqv); assumption
        | rewrite <- (sys_input_eqv ms ms' x8 Heqv); assumption| assumption| assumption].
    + split; [| reflexivity]. apply advance_past_svc_eqv, apply_effect_eqv, Heqv.
  - (* [comment removed for export] *)
    unfold xport, xport_cfg; cbn [cfg_ms cfg_model]. split; [|exact I].
    apply (sstep_cfg_syscall_materialization_fault segs ACFG ms' mo x8 eff model' evs0);
      [assumption| congruence| rewrite <- (sys_input_eqv ms ms' x8 Heqv); assumption
      | rewrite <- (sys_input_eqv ms ms' x8 Heqv); assumption| assumption| assumption].
  - (* [comment removed for export] *)
    unfold xport, xport_cfg; cbn [cfg_ms cfg_model]. match goal with Hs : ms_svc_pending ms = Some _ |- _ => rewrite Hs end.
    match goal with Hh : m_halted model' = Some _ |- _ => rewrite Hh end. split.
    + apply (sstep_cfg_exit segs ACFG ms' mo x8 eff model' evs0 code);
        [assumption| congruence| rewrite <- (sys_input_eqv ms ms' x8 Heqv); assumption| assumption| assumption].
    + split; [exact Heqv| reflexivity].
  - (* [comment removed for export] *)
    unfold xport, xport_cfg; cbn [cfg_ms cfg_model]. match goal with Hs : ms_svc_pending ms = Some _ |- _ => rewrite Hs end.
    assert (Hh : exists c, m_halted model' = Some c).
    { destruct (m_halted model') eqn:E; [eexists; reflexivity|].
      match goal with Hk : m_killed model' = Some _ |- _ => rewrite (m_killed_of_m_halted_none _ E) in Hk; discriminate end. }
    destruct Hh as [c Hc]. rewrite Hc. split.
    + apply (sstep_cfg_killed segs ACFG ms' mo x8 eff model' evs0 sig);
        [assumption| congruence| rewrite <- (sys_input_eqv ms ms' x8 Heqv); assumption| assumption].
    + split; [exact Heqv| reflexivity].
  - unfold xport, xport_cfg; cbn [cfg_ms cfg_model]. split; [|exact I].
    apply (sstep_cfg_syscall_unmodeled segs ACFG ms' mo x8);
      [assumption| congruence| rewrite <- (sys_input_eqv ms ms' x8 Heqv); assumption].
Qed.

(* [comment removed for export] *)
Lemma xport_round_trip : forall ms ms' mo evs X', ms_eqv ms ms' ->
  sstep_cfg segs ACFG (mkCfg ms' mo) evs X' -> xport ms ms' (xport ms' ms X') = X'.
Proof.
  intros ms ms' mo evs X' Heqv Hst0.
  pose proof (sstep_cfg_sub segs ACFG _ _ _ Hst0) as Hst.
  pose proof Heqv as (_ & _ & _ & Hsvc & _ & _ & _ & _).
  inversion Hst; subst; unfold xport, xport_cfg; cbn [cfg_ms cfg_model]; try reflexivity.
  - (* [comment removed for export] *)
    match goal with Hs : ms_svc_pending ms' = None |- _ => rewrite Hsvc, Hs end.
    match goal with Ha : mi_account_step segs ms' mo = MachineOk _ |- _ =>
      pose proof (mi_account_step_projects segs _ _ _ _ Ha) as HS end.
    rewrite HS. reflexivity.
  - (* [comment removed for export] *)
    match goal with Hs : ms_svc_pending ms' = Some _ |- _ => rewrite Hsvc, Hs end.
    match goal with Hm : materialize_model_accesses _ _ = Some _ |- _ => rewrite (materialize_halted _ _ _ Hm) end.
    match goal with Hh : m_halted model' = None |- _ => rewrite Hh end.
    cbn [with_ms_regs ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom].
    destruct ms as [R F pc svc rv fc m ro], ms' as [R' F' pc' svc' rv' fc' m' ro'].
    destruct Heqv as (HR & HF & Hpc & Hsvc' & Hrv & Hfc & Hm & Hro); simpl in *; subst.
    unfold advance_past_svc, apply_effect, set_reg, ms_pc; simpl.
    unfold reg_get. rewrite !bvmap_get_set_same. reflexivity.
  - (* [comment removed for export] *)
    match goal with Hs : ms_svc_pending ms' = Some _ |- _ => rewrite Hsvc, Hs end.
    match goal with Hh : m_halted model' = Some _ |- _ => rewrite Hh end. reflexivity.
  - (* [comment removed for export] *)
    match goal with Hs : ms_svc_pending ms' = Some _ |- _ => rewrite Hsvc, Hs end.
    destruct (m_halted model') eqn:E; [reflexivity|].
    match goal with Hk : m_killed model' = Some _ |- _ => rewrite (m_killed_of_m_halted_none _ E) in Hk; discriminate end.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

End WithSegs.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma reg_of_nat : forall r : reg, exists n, r = Z_to_bv 5 (Z.of_nat n) /\ (n < 32)%nat.
Proof.
  intros r. exists (Z.to_nat (bv_unsigned r)). pose proof (bv_unsigned_in_range 5 r) as Hr.
  unfold bv_modulus in Hr. simpl in Hr. split; [|lia].
  rewrite Z2Nat.id by lia. apply bv_eq. rewrite Z_to_bv_unsigned. symmetry.
  apply bv_wrap_small. unfold bv_modulus. simpl. lia.
Qed.

(* [comment removed for export] *)
Definition mkR_of (R : bvmap 5 word) : bvmap 5 word :=
  mkR (reg_get R 1) (reg_get R 2) (reg_get R 3) (reg_get R 4) (reg_get R 5) (reg_get R 6) (reg_get R 7)
      (reg_get R 8) (reg_get R 9) (reg_get R 10) (reg_get R 11) (reg_get R 12) (reg_get R 13) (reg_get R 14)
      (reg_get R 15) (reg_get R 16) (reg_get R 17) (reg_get R 18) (reg_get R 19) (reg_get R 20) (reg_get R 21)
      (reg_get R 22) (reg_get R 23) (reg_get R 24) (reg_get R 25) (reg_get R 26) (reg_get R 27) (reg_get R 28)
      (reg_get R 29) (reg_get R 30) (reg_get R 31).

Lemma mkR_of_eqv : forall R, xregs_eqv R (mkR_of R).
Proof.
  intros R r Hr. destruct (reg_of_nat r) as (n & -> & Hn).
  destruct n as [|n]; [cbv in Hr; discriminate|].
  do 31 (destruct n as [|n]; [reflexivity|]). lia.
Qed.

Lemma mkR_eqv_of : forall R x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31,
  reg_get R 1 = x1 -> reg_get R 2 = x2 -> reg_get R 3 = x3 -> reg_get R 4 = x4 -> reg_get R 5 = x5 ->
  reg_get R 6 = x6 -> reg_get R 7 = x7 -> reg_get R 8 = x8 -> reg_get R 9 = x9 -> reg_get R 10 = x10 ->
  reg_get R 11 = x11 -> reg_get R 12 = x12 -> reg_get R 13 = x13 -> reg_get R 14 = x14 -> reg_get R 15 = x15 ->
  reg_get R 16 = x16 -> reg_get R 17 = x17 -> reg_get R 18 = x18 -> reg_get R 19 = x19 -> reg_get R 20 = x20 ->
  reg_get R 21 = x21 -> reg_get R 22 = x22 -> reg_get R 23 = x23 -> reg_get R 24 = x24 -> reg_get R 25 = x25 ->
  reg_get R 26 = x26 -> reg_get R 27 = x27 -> reg_get R 28 = x28 -> reg_get R 29 = x29 -> reg_get R 30 = x30 ->
  reg_get R 31 = x31 ->
  xregs_eqv R (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31).
Proof.
  intros. subst. apply mkR_of_eqv.
Qed.
