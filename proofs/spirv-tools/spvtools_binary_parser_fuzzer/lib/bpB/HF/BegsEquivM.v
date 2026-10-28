(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BLPropExec BMState BLFrame.
Import ListNotations.
Open Scope bv_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Definition regs_eqv (R R' : bvmap 5 word) : Prop := forall r : reg, r <> 0%bv -> reg_get R r = reg_get R' r.
Definition fregs_eqv (R R' : bvmap 5 word) : Prop := forall r, reg_get R r = reg_get R' r.

Lemma regs_eqv_sym : forall R R', regs_eqv R R' -> regs_eqv R' R.
Proof. intros R R' H r Hr. symmetry. apply H. exact Hr. Qed.

Lemma fregs_eqv_refl : forall R, fregs_eqv R R.
Proof. intros R r. reflexivity. Qed.
Lemma fregs_eqv_sym : forall R R', fregs_eqv R R' -> fregs_eqv R' R.
Proof. intros R R' H r. symmetry. apply H. Qed.

Lemma reg_get_set : forall (R : bvmap 5 word) (k r : reg) v,
  reg_get (bvmap_set k v R) r = if bv_eqb k r then v else reg_get R r.
Proof.
  intros R k r v. destruct (bv_eqb k r) eqn:E.
  - apply bv_eqb_eq in E. subst. apply reg_get_set_same.
  - apply reg_get_set_other. intros ->. rewrite bv_eqb_refl in E. discriminate.
Qed.

Lemma regs_eqv_set : forall R R' (k : reg) v,
  regs_eqv R R' -> regs_eqv (bvmap_set k v R) (bvmap_set k v R').
Proof. intros R R' k v H r Hr. rewrite !reg_get_set. destruct (bv_eqb k r); [reflexivity|apply H; exact Hr]. Qed.
Lemma fregs_eqv_set : forall R R' (k : reg) v,
  fregs_eqv R R' -> fregs_eqv (bvmap_set k v R) (bvmap_set k v R').
Proof. intros R R' k v H r. rewrite !reg_get_set. destruct (bv_eqb k r); [reflexivity|apply H]. Qed.

Lemma rget_eqv : forall R R', regs_eqv R R' -> forall F pc fc rv r,
  rget (Core R F pc fc rv) r = rget (Core R' F pc fc rv) r.
Proof.
  intros R R' H F pc fc rv r. unfold rget. cbn [c_regs].
  destruct (is_x0 r) eqn:E; [reflexivity|]. apply H.
  intros ->. unfold is_x0 in E. cbn in E. discriminate.
Qed.

Definition core_eqv (c c' : core) : Prop :=
  regs_eqv (c_regs c) (c_regs c') /\ fregs_eqv (c_fregs c) (c_fregs c') /\
  c_pc c = c_pc c' /\ c_fcsr c = c_fcsr c' /\ c_resv c = c_resv c'.

Inductive eff_eqv : eff -> eff -> Prop :=
| EqvDone : forall c c', core_eqv c c' -> eff_eqv (EDone c) (EDone c')
| EqvIllegal : forall c c', eff_eqv (EIllegal c) (EIllegal c')
| EqvEcall : forall c c', eff_eqv (EEcall c) (EEcall c')
| EqvEbreak : forall c c', eff_eqv (EEbreak c) (EEbreak c')
| EqvFault : forall c c', eff_eqv (EFault c) (EFault c')
| EqvDefIllegal : forall c c', eff_eqv (EDefinedIllegal c) (EDefinedIllegal c')
| EqvLoad : forall n a k k', (forall v, eff_eqv (k v) (k' v)) -> eff_eqv (ELoad n a k) (ELoad n a k')
| EqvStore : forall n a v k k', eff_eqv k k' -> eff_eqv (EStore n a v k) (EStore n a v k').

Lemma core_eqv_mk : forall R R' F F' pc fc rv, regs_eqv R R' -> fregs_eqv F F' ->
  core_eqv (Core R F pc fc rv) (Core R' F' pc fc rv).
Proof. intros. repeat split; assumption. Qed.

Local Ltac core_tac :=
  unfold core_eqv, rset, fset, with_regs, with_fregs, with_pc, with_fcsr, with_resv,
         accrue, fwrite, inval_resv in *; simpl in *.

Lemma core_eqv_rset : forall r v c c', core_eqv c c' -> core_eqv (rset r v c) (rset r v c').
Proof.
  intros r v [R F p f s] [R' F' p' f' s'] H. core_tac. destruct H as (HR & HF & -> & -> & ->).
  destruct (is_x0 r); simpl; repeat split; auto using regs_eqv_set.
Qed.
Lemma core_eqv_fset : forall r v c c', core_eqv c c' -> core_eqv (fset r v c) (fset r v c').
Proof.
  intros r v [R F p f s] [R' F' p' f' s'] H. core_tac. destruct H as (HR & HF & -> & -> & ->).
  repeat split; auto using fregs_eqv_set.
Qed.
Lemma core_eqv_with_pc : forall v c c', core_eqv c c' -> core_eqv (with_pc v c) (with_pc v c').
Proof. intros v [R F p f s] [R' F' p' f' s'] H. core_tac. destruct H as (HR & HF & -> & -> & ->). repeat split; auto. Qed.
Lemma core_eqv_with_fcsr : forall v c c', core_eqv c c' -> core_eqv (with_fcsr v c) (with_fcsr v c').
Proof. intros v [R F p f s] [R' F' p' f' s'] H. core_tac. destruct H as (HR & HF & -> & -> & ->). repeat split; auto. Qed.
Lemma core_eqv_with_resv : forall v c c', core_eqv c c' -> core_eqv (with_resv v c) (with_resv v c').
Proof. intros v [R F p f s] [R' F' p' f' s'] H. core_tac. destruct H as (HR & HF & -> & -> & ->). repeat split; auto. Qed.
Lemma core_eqv_accrue : forall fl c c', core_eqv c c' -> core_eqv (accrue fl c) (accrue fl c').
Proof. intros fl [R F p f s] [R' F' p' f' s'] H. core_tac. destruct H as (HR & HF & -> & -> & ->). repeat split; auto. Qed.
Lemma core_eqv_fwrite : forall fmt r v c c', core_eqv c c' -> core_eqv (fwrite fmt r v c) (fwrite fmt r v c').
Proof. intros fmt r v c c' H. destruct fmt; apply core_eqv_fset; exact H. Qed.
Lemma core_eqv_inval_resv : forall a c c', core_eqv c c' -> core_eqv (inval_resv a c) (inval_resv a c').
Proof.
  intros a [R F p f s] [R' F' p' f' s'] H. core_tac. destruct H as (HR & HF & -> & -> & ->).
  destruct s' as [r|]; [destruct (Z.eqb _ _)|]; simpl; repeat split; auto.
Qed.
Lemma core_eqv_if : forall (b : bool) c1 c1' c2 c2',
  core_eqv c1 c1' -> core_eqv c2 c2' -> core_eqv (if b then c1 else c2) (if b then c1' else c2').
Proof. intros [] c1 c1' c2 c2' H1 H2; assumption. Qed.

Local Ltac solve_core HR HF :=
  repeat first [ apply core_eqv_rset | apply core_eqv_fset | apply core_eqv_with_pc
               | apply core_eqv_with_fcsr | apply core_eqv_with_resv | apply core_eqv_accrue
               | apply core_eqv_fwrite | apply core_eqv_inval_resv | apply core_eqv_if
               | match goal with |- core_eqv (match ?X with _ => _ end) _ => destruct X end ];
  apply (core_eqv_mk _ _ _ _ _ _ _ HR HF).

Local Ltac eqv_struct HR HF :=
  repeat first
    [ apply EqvDone; solve_core HR HF
    | apply EqvIllegal | apply EqvEcall | apply EqvEbreak | apply EqvFault | apply EqvDefIllegal
    | apply EqvLoad; intros ?
    | apply EqvStore
    | match goal with |- eff_eqv (match ?X with _ => _ end) _ => destruct X end
    | match goal with |- eff_eqv (match ?X with _ => _ end _) _ => destruct X end ].

Local Ltac unfold_exec :=
  cbv beta iota zeta delta [exec fget fread c_regs c_fregs c_pc c_fcsr c_resv
                            with_pc load_val store_val exec_csr resolve_rm frm_of].
Local Ltac unfold_rget := cbv beta iota zeta delta [rget c_regs].

Lemma exec_eqv_core : forall R R' F F' pc fc rv sz i,
  regs_eqv R R' -> fregs_eqv F F' ->
  eff_eqv (exec sz i (Core R F pc fc rv)) (exec sz i (Core R' F' pc fc rv)).
Proof.
  intros R R' F F' pc fc rv sz i HR HF.
  destruct i; unfold_exec; rewrite ?(rget_eqv R R' HR); unfold_rget; rewrite ?HF; eqv_struct HR HF.
Qed.

Definition ms_eqv (ms ms' : machine_state) : Prop :=
  regs_eqv (ms_regs ms) (ms_regs ms') /\ fregs_eqv (ms_fregs ms) (ms_fregs ms') /\
  ms_pc_val ms = ms_pc_val ms' /\ ms_svc_pending ms = ms_svc_pending ms' /\
  ms_resv ms = ms_resv ms' /\ ms_fcsr ms = ms_fcsr ms' /\
  ms_mem ms = ms_mem ms' /\ ms_rom ms = ms_rom ms'.

Lemma ms_eqv_sym : forall ms ms', ms_eqv ms ms' -> ms_eqv ms' ms.
Proof.
  intros ms ms' (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8).
  repeat split; auto using regs_eqv_sym, fregs_eqv_sym; congruence.
Qed.

Definition res_eqv (r r' : machine_result machine_state) : Prop :=
  match r, r' with
  | MachineOk a, MachineOk b => ms_eqv a b
  | MachineFault, MachineFault => True
  | MachineUnmodeled, MachineUnmodeled => True
  | _, _ => False
  end.

Section WithSegs.
Variable segs : list Segment.

Definition ares_eqv (r r' : machine_result (access_report (core * (word -> option byte)))) : Prop :=
  match r, r' with
  | MachineOk a, MachineOk b =>
      core_eqv (fst (access_value _ a)) (fst (access_value _ b))
      /\ snd (access_value _ a) = snd (access_value _ b)
      /\ accessed_ranges _ a = accessed_ranges _ b
  | MachineFault, MachineFault => True
  | MachineUnmodeled, MachineUnmodeled => True
  | _, _ => False
  end.

Lemma interp_eff_accesses_eqv : forall t t', eff_eqv t t' -> forall m,
  ares_eqv (interp_eff_accesses segs t m) (interp_eff_accesses segs t' m).
Proof.
  intros t t' H.
  induction H as [c c' Hc | c c' | c c' | c c' | c c' | c c' | n a k k' Hk IH | n a v k k' Hk IH]; intros m;
    cbn [interp_eff_accesses]; try exact I.
  - cbn. auto.
  - destruct (ov_read_bytes segs m a (width_bytes n)) as [bs|]; [|exact I].
    specialize (IH (bv_extract 0 n (le_bytes_to_word bs)) m).
    destruct (interp_eff_accesses segs (k _) m) as [ra| |]; destruct (interp_eff_accesses segs (k' _) m) as [rb| |];
      cbn in IH |- *; try exact IH; try contradiction.
    destruct IH as (A & B & C). rewrite C. auto.
  - destruct (store_ok segs m a (width_bytes n)); [|exact I].
    specialize (IH (write_to_mem m a (Z_to_le_bytes (width_bytes n) (bv_unsigned v)))).
    destruct (interp_eff_accesses segs k _) as [ra| |]; destruct (interp_eff_accesses segs k' _) as [rb| |];
      cbn in IH |- *; try exact IH; try contradiction.
    destruct IH as (A & B & C). rewrite C. auto.
Qed.

Lemma ms_reg_eqv : forall ms ms' r, r <> 0%bv -> ms_eqv ms ms' -> ms_reg ms r = ms_reg ms' r.
Proof. intros ms ms' r Hr (HR & _). unfold ms_reg. rewrite (HR r Hr). reflexivity. Qed.

Definition msres_eqv (r r' : machine_result (access_report machine_state)) : Prop :=
  match r, r' with
  | MachineOk a, MachineOk b => ms_eqv (access_value _ a) (access_value _ b) /\ accessed_ranges _ a = accessed_ranges _ b
  | MachineFault, MachineFault => True
  | MachineUnmodeled, MachineUnmodeled => True
  | _, _ => False
  end.

Lemma decode_exec_accesses_eqv : forall ms ms' w, ms_eqv ms ms' ->
  msres_eqv (decode_exec_accesses segs ms w) (decode_exec_accesses segs ms' w).
Proof.
  intros ms ms' w Heqv. pose proof (ms_reg_eqv ms ms' 17 ltac:(intros E; apply (f_equal bv_unsigned) in E; discriminate E) Heqv) as H17.
  destruct ms as [R F pc svc rv fc m ro], ms' as [R' F' pc' svc' rv' fc' m' ro'].
  destruct Heqv as (HR & HF & Hpc & Hsvc & Hrv & Hfc & Hm & Hro); simpl in *; subst.
  unfold decode_exec_accesses. destruct (is_ecall w).
  - simpl. rewrite H17. repeat split; assumption.
  - destruct (decode_any w) as [[i isz]|]; [| destruct (is_defined_illegal w); exact I]. simpl.
    pose proof (interp_eff_accesses_eqv _ _ (exec_eqv_core R R' F F' pc' fc' rv' (Z_to_bv 64 isz) i HR HF) m') as K.
    destruct (interp_eff_accesses segs (exec _ i (Core R F pc' fc' rv')) m') as [[[c m1] acc]| |];
    destruct (interp_eff_accesses segs (exec _ i (Core R' F' pc' fc' rv')) m') as [[[c' m1'] acc']| |];
    simpl in K |- *; try exact K; try contradiction.
    destruct K as ((H1 & H2 & H3 & H4 & H5) & <- & <-). repeat split; simpl; auto.
Qed.

Lemma step_accesses_eqv : forall ms ms', ms_eqv ms ms' ->
  msres_eqv (RiscvSemantics.step_accesses segs ms) (RiscvSemantics.step_accesses segs ms').
Proof.
  intros ms ms' Heqv. pose proof Heqv as (_ & _ & Hpc & _ & _ & _ & Hm & _).
  unfold RiscvSemantics.step_accesses, ms_pc. rewrite <- Hpc, <- Hm.
  destruct (fetch_word segs (ms_pc_val ms)); [apply decode_exec_accesses_eqv; exact Heqv|].
  destruct (fetch_word_ov segs (ms_mem ms) (ms_pc_val ms)); [apply decode_exec_accesses_eqv; exact Heqv|].
  destruct (fetch_tail_any segs (ms_mem ms) (ms_pc_val ms)); [apply decode_exec_accesses_eqv; exact Heqv|].
  unfold fetch_failure. destruct (negb _); [exact I|]. destruct (_ || _)%bool; exact I.
Qed.

Definition mres_eqv (r r' : machine_result (machine_state * Model)) : Prop :=
  match r, r' with
  | MachineOk (a, mo), MachineOk (b, mo') => ms_eqv a b /\ mo = mo'
  | MachineFault, MachineFault => True
  | MachineUnmodeled, MachineUnmodeled => True
  | _, _ => False
  end.

Lemma mi_account_step_eqv : forall ms ms' mo, ms_eqv ms ms' ->
  mres_eqv (mi_account_step segs ms mo) (mi_account_step segs ms' mo).
Proof.
  intros ms ms' mo Heqv. pose proof (step_accesses_eqv ms ms' Heqv) as K.
  unfold mi_account_step.
  destruct (RiscvSemantics.step_accesses segs ms) as [a| |]; destruct (RiscvSemantics.step_accesses segs ms') as [b| |];
    cbn in K |- *; try exact K; try contradiction.
  destruct K as [K1 K2]. rewrite <- K2.
  destruct (materialize_model_accesses mo (accessed_ranges _ a)); [|exact I]. split; [exact K1|reflexivity].
Qed.

Lemma syscall_args_eqv : forall ms ms', ms_eqv ms ms' -> syscall_args ms = syscall_args ms'.
Proof. intros ms ms' (HR & _). unfold syscall_args, ms_gpr. rewrite !HR by (intros E; apply (f_equal bv_unsigned) in E; discriminate E). reflexivity. Qed.

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
  unfold apply_effect, set_reg; simpl. repeat split; simpl; auto using regs_eqv_set.
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

Lemma cfg_eqv_sym : forall c c', cfg_eqv c c' -> cfg_eqv c' c.
Proof. intros c c' [H1 H2]. split; [apply ms_eqv_sym; exact H1| congruence]. Qed.

Definition to_eqv (X X' : step_to) : Prop :=
  match X, X' with
  | SError, SError => True
  | SNext c, SNext c' => cfg_eqv c c'
  | _, _ => False
  end.

Lemma sstep_scfg_eqv : forall scfg ms ms' mo evs X, ms_eqv ms ms' ->
  sstep_cfg segs scfg (mkCfg ms mo) evs X ->
  exists X', sstep_cfg segs scfg (mkCfg ms' mo) evs X' /\ to_eqv X X'.
Proof.
  intros scfg ms ms' mo evs X Heqv Hst.
  pose proof (mi_account_step_eqv ms ms' mo Heqv) as Hres.
  pose proof Heqv as (_ & _ & _ & Hsvc & _ & _ & _ & _).
  inversion Hst; subst.
  -
    rewrite H5 in Hres. destruct (mi_account_step segs ms' mo) as [[ms1' mo1']| |] eqn:E; simpl in Hres; try contradiction.
    destruct Hres as [Hres <-].
    exists (SNext (mkCfg ms1' model')). split; [apply sstep_cfg_instr; auto; congruence|]. split; [exact Hres| reflexivity].
  - rewrite H5 in Hres. destruct (mi_account_step segs ms' mo) as [[ms1' mo1']| |] eqn:E; simpl in Hres; try contradiction.
    exists SError. split; [apply sstep_cfg_instr_fault; auto; congruence| exact I].
  - rewrite H5 in Hres. destruct (mi_account_step segs ms' mo) as [[ms1' mo1']| |] eqn:E; simpl in Hres; try contradiction.
    exists SError. split; [apply sstep_cfg_instr_unmodeled; auto; congruence| exact I].
  -
    exists (SNext (mkCfg (advance_past_svc (apply_effect ms' eff)) model'')). split.
    + apply (sstep_cfg_syscall segs scfg ms' mo x8 eff model' model'' evs);
        [assumption| congruence| rewrite <- (sys_input_eqv ms ms' x8 Heqv); assumption
        | rewrite <- (sys_input_eqv ms ms' x8 Heqv); assumption | assumption| assumption].
    + split; [| reflexivity]. apply advance_past_svc_eqv, apply_effect_eqv, Heqv.
  -
    exists SError. split; [|exact I].
    apply (sstep_cfg_syscall_materialization_fault segs scfg ms' mo x8 eff model' evs0);
      [assumption| congruence| rewrite <- (sys_input_eqv ms ms' x8 Heqv); assumption
      | rewrite <- (sys_input_eqv ms ms' x8 Heqv); assumption| assumption| assumption].
  -
    exists (SNext (mkCfg ms' model')). split.
    + apply (sstep_cfg_exit segs scfg ms' mo x8 eff model' evs0 code);
        [assumption| congruence| rewrite <- (sys_input_eqv ms ms' x8 Heqv); assumption| assumption| assumption].
    + split; [exact Heqv| reflexivity].
  -
    exists (SNext (mkCfg ms' model')). split.
    + apply (sstep_cfg_killed segs scfg ms' mo x8 eff model' evs0 sig);
        [assumption| congruence| rewrite <- (sys_input_eqv ms ms' x8 Heqv); assumption| assumption].
    + split; [exact Heqv| reflexivity].
  - exists SError. split; [|exact I].
    apply (sstep_cfg_syscall_unmodeled segs scfg ms' mo x8);
      [assumption| congruence| rewrite <- (sys_input_eqv ms ms' x8 Heqv); assumption].
Qed.

Lemma sstep_scfg_cfg_eqv : forall scfg c c' evs X, cfg_eqv c c' ->
  sstep_cfg segs scfg c evs X -> exists X', sstep_cfg segs scfg c' evs X' /\ to_eqv X X'.
Proof.
  intros scfg [ms mo] [ms' mo'] evs X [Hms Hmo] Hst; simpl in Hms, Hmo; subst.
  apply (sstep_scfg_eqv scfg ms ms'); assumption.
Qed.

End WithSegs.

Lemma reg_of_nat : forall r : reg, exists n, r = Z_to_bv 5 (Z.of_nat n) /\ (n < 32)%nat.
Proof.
  intros r. exists (Z.to_nat (bv_unsigned r)). pose proof (bv_unsigned_in_range 5 r) as Hr.
  unfold bv_modulus in Hr. simpl in Hr. split; [|lia].
  rewrite Z2Nat.id by lia. apply bv_eq. rewrite Z_to_bv_unsigned. symmetry.
  apply bv_wrap_small. unfold bv_modulus. simpl. lia.
Qed.

Definition mkR_init (sp : word) : bvmap 5 word :=
  mkR w0 sp w0 w0 w0 w0 w0 w0 w0 w0 w0 w0 w0 w0 w0 w0 w0 w0 w0 w0 w0 w0 w0 w0 w0 w0 w0 w0 w0 w0 w0.

Definition mkR_of (R : bvmap 5 word) : bvmap 5 word :=
  mkR (reg_get R 1) (reg_get R 2) (reg_get R 3) (reg_get R 4) (reg_get R 5) (reg_get R 6) (reg_get R 7) (reg_get R 8)
      (reg_get R 9) (reg_get R 10) (reg_get R 11) (reg_get R 12) (reg_get R 13) (reg_get R 14) (reg_get R 15) (reg_get R 16)
      (reg_get R 17) (reg_get R 18) (reg_get R 19) (reg_get R 20) (reg_get R 21) (reg_get R 22) (reg_get R 23) (reg_get R 24)
      (reg_get R 25) (reg_get R 26) (reg_get R 27) (reg_get R 28) (reg_get R 29) (reg_get R 30) (reg_get R 31).

Lemma mkR_of_eqv : forall R, regs_eqv R (mkR_of R).
Proof.
  intros R r Hr. destruct (reg_of_nat r) as (n & -> & Hn).
  destruct n as [|n]; [exfalso; apply Hr; apply bv_eq; reflexivity|].
  do 31 (destruct n as [|n]; [cbn; reflexivity |]). lia.
Qed.
