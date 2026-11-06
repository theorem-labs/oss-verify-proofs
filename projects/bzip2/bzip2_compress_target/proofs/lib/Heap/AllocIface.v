(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require PropExec ShapeAlg.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require MState Frame.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require CpsOpen.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Common Require CfgStep.
Module GlueEqv.
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.PropExec OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.ShapeAlg.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.MState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.Frame.
 Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope bv_scope.
(* [comment removed for export] *)
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.CpsOpen.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition regs_eqv (R R' : bvmap 5 word) : Prop := forall r, reg_get R r = reg_get R' r.

Lemma regs_eqv_refl : forall R, regs_eqv R R.
Proof. intros R r. reflexivity. Qed.
Lemma regs_eqv_sym : forall R R', regs_eqv R R' -> regs_eqv R' R.
Proof. intros R R' H r. symmetry. apply H. Qed.
(* [comment removed for export] *)

Lemma reg_get_set : forall (R : bvmap 5 word) (k r : reg) v,
  reg_get (bvmap_set k v R) r = if bv_eqb k r then v else reg_get R r.
Proof.
  intros R k r v. destruct (bv_eqb k r) eqn:E.
  - apply bv_eqb_eq in E. subst. apply reg_get_set_same.
  - apply reg_get_set_other. intros ->. rewrite bv_eqb_refl in E. discriminate.
Qed.

Lemma regs_eqv_set : forall R R' (k : reg) v,
  regs_eqv R R' -> regs_eqv (bvmap_set k v R) (bvmap_set k v R').
Proof. intros R R' k v H r. rewrite !reg_get_set. destruct (bv_eqb k r); [reflexivity|apply H]. Qed.

(* [comment removed for export] *)
Definition regs_eqv0 (R R' : bvmap 5 word) : Prop := forall r, is_x0 r = false -> reg_get R r = reg_get R' r.

(* [comment removed for export] *)
Lemma regs_eqv0_sym : forall R R', regs_eqv0 R R' -> regs_eqv0 R' R.
Proof. intros R R' H r Hr. symmetry. apply H. exact Hr. Qed.
(* [comment removed for export] *)
Lemma regs_eqv0_set : forall R R' (k : reg) v,
  regs_eqv0 R R' -> regs_eqv0 (bvmap_set k v R) (bvmap_set k v R').
Proof. intros R R' k v H r Hr. rewrite !reg_get_set. destruct (bv_eqb k r); [reflexivity|apply H; exact Hr]. Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma rget_if_eqv : forall R R', regs_eqv0 R R' ->
  forall r, (if is_x0 r then w0 else reg_get R r) = (if is_x0 r then w0 else reg_get R' r).
Proof. intros R R' H r. destruct (is_x0 r) eqn:E; [reflexivity| apply H; exact E]. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition core_eqv (c c' : core) : Prop :=
  regs_eqv0 (c_regs c) (c_regs c') /\ regs_eqv (c_fregs c) (c_fregs c') /\
  c_pc c = c_pc c' /\ c_fcsr c = c_fcsr c' /\ c_resv c = c_resv c'.

Inductive eff_eqv : eff -> eff -> Prop :=
| EqvDone : forall c c', core_eqv c c' -> eff_eqv (EDone c) (EDone c')
| EqvIllegal : forall c c', eff_eqv (EIllegal c) (EIllegal c')
| EqvEcall : forall c c', eff_eqv (EEcall c) (EEcall c')
| EqvEbreak : forall c c', eff_eqv (EEbreak c) (EEbreak c')
| EqvFault : forall c c', eff_eqv (EFault c) (EFault c')
| EqvDefinedIllegal : forall c c', eff_eqv (EDefinedIllegal c) (EDefinedIllegal c')   (* [comment removed for export] *)
| EqvLoad : forall n a k k', (forall v, eff_eqv (k v) (k' v)) -> eff_eqv (ELoad n a k) (ELoad n a k')
| EqvStore : forall n a v k k', eff_eqv k k' -> eff_eqv (EStore n a v k) (EStore n a v k').

Lemma core_eqv_mk : forall R R' F F' pc fc rv, regs_eqv0 R R' -> regs_eqv F F' ->
  core_eqv (Core R F pc fc rv) (Core R' F' pc fc rv).
Proof. intros. repeat split; assumption. Qed.

Local Ltac core_tac :=
  unfold core_eqv, rset, fset, with_regs, with_fregs, with_pc, with_fcsr, with_resv,
         accrue, fwrite, inval_resv in *; simpl in *.

Lemma core_eqv_rset : forall r v c c', core_eqv c c' -> core_eqv (rset r v c) (rset r v c').
Proof.
  intros r v [R F p f s] [R' F' p' f' s'] H. core_tac. cps_destruct H as (HR & HF & -> & -> & ->).
  destruct (is_x0 r); simpl; repeat split; auto using regs_eqv0_set.
Qed.
Lemma core_eqv_fset : forall r v c c', core_eqv c c' -> core_eqv (fset r v c) (fset r v c').
Proof.
  intros r v [R F p f s] [R' F' p' f' s'] H. core_tac. cps_destruct H as (HR & HF & -> & -> & ->).
  repeat split; auto using regs_eqv_set.
Qed.
Lemma core_eqv_with_pc : forall v c c', core_eqv c c' -> core_eqv (with_pc v c) (with_pc v c').
Proof. intros v [R F p f s] [R' F' p' f' s'] H. core_tac. cps_destruct H as (HR & HF & -> & -> & ->). repeat split; auto. Qed.
Lemma core_eqv_with_fcsr : forall v c c', core_eqv c c' -> core_eqv (with_fcsr v c) (with_fcsr v c').
Proof. intros v [R F p f s] [R' F' p' f' s'] H. core_tac. cps_destruct H as (HR & HF & -> & -> & ->). repeat split; auto. Qed.
Lemma core_eqv_with_resv : forall v c c', core_eqv c c' -> core_eqv (with_resv v c) (with_resv v c').
Proof. intros v [R F p f s] [R' F' p' f' s'] H. core_tac. cps_destruct H as (HR & HF & -> & -> & ->). repeat split; auto. Qed.
Lemma core_eqv_accrue : forall fl c c', core_eqv c c' -> core_eqv (accrue fl c) (accrue fl c').
Proof. intros fl [R F p f s] [R' F' p' f' s'] H. core_tac. cps_destruct H as (HR & HF & -> & -> & ->). repeat split; auto. Qed.
Lemma core_eqv_fwrite : forall fmt r v c c', core_eqv c c' -> core_eqv (fwrite fmt r v c) (fwrite fmt r v c').
Proof. intros fmt r v c c' H. destruct fmt; apply core_eqv_fset; exact H. Qed.
Lemma core_eqv_inval_resv : forall a c c', core_eqv c c' -> core_eqv (inval_resv a c) (inval_resv a c').
Proof.
  intros a [R F p f s] [R' F' p' f' s'] H. core_tac. cps_destruct H as (HR & HF & -> & -> & ->).
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
    | apply EqvIllegal | apply EqvEcall | apply EqvEbreak | apply EqvFault | apply EqvDefinedIllegal
    | apply EqvLoad; intros ?
    | apply EqvStore
    | match goal with |- eff_eqv (match ?X with _ => _ end) _ => destruct X end
    | match goal with |- eff_eqv (match ?X with _ => _ end _) _ => destruct X end ].

Local Ltac unfold_exec :=
  cbv beta iota zeta delta [exec rget fget fread c_regs c_fregs c_pc c_fcsr c_resv
                            with_pc load_val store_val exec_csr resolve_rm frm_of].

(* [comment removed for export] *)
Lemma exec_eqv_core : forall R R' F F' pc fc rv sz i,
  regs_eqv0 R R' -> regs_eqv F F' ->
  eff_eqv (exec sz i (Core R F pc fc rv)) (exec sz i (Core R' F' pc fc rv)).
Proof.
  intros R R' F F' pc fc rv sz i HR HF.
  destruct i; unfold_exec; rewrite ?(rget_if_eqv R R' HR), ?HF; eqv_struct HR HF.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition ms_eqv (ms ms' : machine_state) : Prop :=
  regs_eqv0 (ms_regs ms) (ms_regs ms') /\ regs_eqv (ms_fregs ms) (ms_fregs ms') /\
  ms_pc_val ms = ms_pc_val ms' /\ ms_svc_pending ms = ms_svc_pending ms' /\
  ms_resv ms = ms_resv ms' /\ ms_fcsr ms = ms_fcsr ms' /\
  ms_mem ms = ms_mem ms' /\ ms_rom ms = ms_rom ms'.

(* [comment removed for export] *)
Lemma ms_eqv_sym : forall ms ms', ms_eqv ms ms' -> ms_eqv ms' ms.
Proof.
  (intros ms ms'; cps_intros (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8)).
  repeat split; auto using regs_eqv_sym, regs_eqv0_sym; congruence.
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition rep_eqv (r r' : machine_result (access_report (core * (word -> option byte)))) : Prop :=
  match r, r' with
  | MachineOk a, MachineOk b =>
      core_eqv (fst (@access_value _ a)) (fst (@access_value _ b))
      /\ snd (@access_value _ a) = snd (@access_value _ b)
      /\ @accessed_ranges _ a = @accessed_ranges _ b
  | MachineFault, MachineFault => True
  | MachineUnmodeled, MachineUnmodeled => True
  | _, _ => False
  end.

Section WithSegs.
Variable segs : list Segment.

Lemma interp_eff_accesses_eqv : forall t t', eff_eqv t t' -> forall m,
  rep_eqv (interp_eff_accesses segs t m) (interp_eff_accesses segs t' m).
Proof.
  intros t t' H.
  induction H as [c c' Hc | c c' | c c' | c c' | c c' | c c' | n a k k' Hk IH | n a v k k' Hk IH]; intros m;
    cbn [interp_eff_accesses]; try exact I.
  - cbn. cps_destruct Hc as (H1 & H2 & H3 & H4 & H5). repeat split; assumption.
  - destruct (ov_read_bytes segs m a (width_bytes n)) as [bs|]; [|exact I].
    specialize (IH (bv_extract 0 n (le_bytes_to_word bs)) m).
    destruct (interp_eff_accesses segs (k _) m) as [ra| |]; destruct (interp_eff_accesses segs (k' _) m) as [rb| |];
      cbn in IH |- *; try exact IH; try contradiction.
    cps_destruct IH as (H1 & H2 & H3). split; [exact H1|]. split; [exact H2|]. cbn. rewrite H3. reflexivity.
  - destruct (store_ok segs m a (width_bytes n)); [|exact I].
    specialize (IH (write_to_mem m a (Z_to_le_bytes (width_bytes n) (bv_unsigned v)))).
    destruct (interp_eff_accesses segs k _) as [ra| |]; destruct (interp_eff_accesses segs k' _) as [rb| |];
      cbn in IH |- *; try exact IH; try contradiction.
    cps_destruct IH as (H1 & H2 & H3). split; [exact H1|]. split; [exact H2|]. cbn. rewrite H3. reflexivity.
Qed.

(* [comment removed for export] *)
Definition srep_eqv (r r' : machine_result (access_report machine_state)) : Prop :=
  match r, r' with
  | MachineOk a, MachineOk b => ms_eqv (@access_value _ a) (@access_value _ b) /\ @accessed_ranges _ a = @accessed_ranges _ b
  | MachineFault, MachineFault => True
  | MachineUnmodeled, MachineUnmodeled => True
  | _, _ => False
  end.

Lemma ms_reg_eqv : forall ms ms' r, ms_eqv ms ms' -> ms_reg ms r = ms_reg ms' r.
Proof.
  intros ms ms' r (HR & _). unfold ms_reg. rewrite bv_eqb0_is_x0.
  destruct (is_x0 r) eqn:E; [reflexivity|]. rewrite (HR r E). reflexivity.
Qed.

Lemma decode_exec_accesses_eqv : forall ms ms' w, ms_eqv ms ms' ->
  srep_eqv (decode_exec_accesses segs ms w) (decode_exec_accesses segs ms' w).
Proof.
  intros ms ms' w Heqv. pose proof (ms_reg_eqv ms ms' 17 Heqv) as H17.
  destruct ms as [R F pc svc rv fc m ro], ms' as [R' F' pc' svc' rv' fc' m' ro'].
  cps_destruct Heqv as (HR & HF & Hpc & Hsvc & Hrv & Hfc & Hm & Hro); simpl in *; subst.
  unfold decode_exec_accesses. destruct (is_ecall w).
  - simpl. rewrite H17. split; [|reflexivity]. repeat split; assumption.
  - destruct (decode_any w) as [[i isz]|]; [| destruct (is_defined_illegal w); exact I]. simpl.
    pose proof (interp_eff_accesses_eqv _ _ (exec_eqv_core R R' F F' pc' fc' rv' (Z_to_bv 64 isz) i HR HF) m') as K.
    destruct (interp_eff_accesses segs (exec _ i (Core R F pc' fc' rv')) m') as [[[c m1] accs]| |];
    destruct (interp_eff_accesses segs (exec _ i (Core R' F' pc' fc' rv')) m') as [[[c' m1'] accs']| |];
    simpl in K |- *; try exact K; try contradiction.
    cps_destruct K as ((H1 & H2 & H3 & H4 & H5) & -> & ->). split; [|reflexivity]. repeat split; simpl; auto.
Qed.

Lemma step_accesses_eqv : forall ms ms', ms_eqv ms ms' ->
  srep_eqv (RiscvSemantics.step_accesses segs ms) (RiscvSemantics.step_accesses segs ms').
Proof.
  intros ms ms' Heqv. cps_pose Heqv as (_ & _ & Hpc & _ & _ & _ & Hm & _).
  unfold RiscvSemantics.step_accesses, ms_pc. rewrite <- Hpc, <- Hm.
  destruct (fetch_word segs (ms_pc_val ms)); [apply decode_exec_accesses_eqv; exact Heqv|].
  destruct (fetch_word_ov segs (ms_mem ms) (ms_pc_val ms)); [apply decode_exec_accesses_eqv; exact Heqv|].
  destruct (fetch_tail_any segs (ms_mem ms) (ms_pc_val ms)); [apply decode_exec_accesses_eqv; exact Heqv|].
  unfold fetch_failure. destruct (negb _); [exact I|]. destruct (_ || _)%bool; exact I.
Qed.

(* [comment removed for export] *)
Lemma mi_account_step_eqv : forall ms ms' mo, ms_eqv ms ms' ->
  match mi_account_step segs ms mo, mi_account_step segs ms' mo with
  | MachineOk (a, m1), MachineOk (b, m2) => ms_eqv a b /\ m1 = m2
  | MachineFault, MachineFault => True
  | MachineUnmodeled, MachineUnmodeled => True
  | _, _ => False
  end.
Proof.
  intros ms ms' mo Heqv. unfold mi_account_step.
  pose proof (step_accesses_eqv ms ms' Heqv) as K.
  destruct (RiscvSemantics.step_accesses segs ms) as [ra| |]; destruct (RiscvSemantics.step_accesses segs ms') as [rb| |];
    cbn in K; try exact K; try contradiction.
  destruct K as [Hv Hacc]. rewrite <- Hacc.
  destruct (materialize_model_accesses mo (@accessed_ranges _ ra)) as [mo'|]; [|exact I].
  split; [exact Hv| reflexivity].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma syscall_args_eqv : forall ms ms', ms_eqv ms ms' -> syscall_args ms = syscall_args ms'.
Proof. intros ms ms' (HR & _). unfold syscall_args, ms_gpr. cbn -[reg_get]. rewrite !HR by reflexivity. reflexivity. Qed.

Lemma sys_input_eqv : forall ms ms' x8, ms_eqv ms ms' -> sys_input segs ms x8 = sys_input segs ms' x8.
Proof.
  intros ms ms' x8 Heqv. pose proof (syscall_args_eqv ms ms' Heqv) as Ha.
  destruct ms as [R F pc svc rv fc m ro], ms' as [R' F' pc' svc' rv' fc' m' ro'].
  cps_destruct Heqv as (HR & HF & Hpc & Hsvc & Hrv & Hfc & Hm & Hro); simpl in *; subst.
  unfold sys_input. rewrite Ha. reflexivity.
Qed.

Lemma apply_effect_eqv : forall ms ms' eff, ms_eqv ms ms' ->
  ms_eqv (apply_effect ms eff) (apply_effect ms' eff).
Proof.
  (intros [R F pc svc rv fc m ro] [R' F' pc' svc' rv' fc' m' ro'] eff; cps_intros (HR & HF & Hpc & Hsvc & Hrv & Hfc & Hm & Hro)); simpl in *; subst.
  unfold apply_effect, set_reg; simpl. repeat split; simpl; auto using regs_eqv0_set.
Qed.

Lemma advance_past_svc_eqv : forall ms ms', ms_eqv ms ms' ->
  ms_eqv (advance_past_svc ms) (advance_past_svc ms').
Proof.
  (intros [R F pc svc rv fc m ro] [R' F' pc' svc' rv' fc' m' ro']; cps_intros (HR & HF & Hpc & Hsvc & Hrv & Hfc & Hm & Hro)); simpl in *; subst.
  unfold advance_past_svc, ms_pc; simpl. repeat split; auto.
Qed.

Definition cfg_eqv (c c' : config) : Prop :=
  ms_eqv (cfg_ms c) (cfg_ms c') /\ cfg_model c = cfg_model c'.

(* [comment removed for export] *)
Lemma cfg_eqv_sym : forall c c', cfg_eqv c c' -> cfg_eqv c' c.
Proof. intros c c' [H1 H2]. split; [apply ms_eqv_sym; exact H1| congruence]. Qed.
(* [comment removed for export] *)

Definition to_eqv (X X' : step_to) : Prop :=
  match X, X' with
  | SError, SError => True
  | SNext c, SNext c' => cfg_eqv c c'
  | _, _ => False
  end.

Lemma sstep_eqv : forall ms ms' mo evs X, ms_eqv ms ms' ->
  sstep_cfg segs CfgStep.kit_cfg (mkCfg ms mo) evs X ->
  exists X', sstep_cfg segs CfgStep.kit_cfg (mkCfg ms' mo) evs X' /\ to_eqv X X'.
Proof.
  intros ms ms' mo evs X Heqv Hst.
  pose proof (mi_account_step_eqv ms ms' mo Heqv) as Hres.
  cps_pose Heqv as (_ & _ & _ & Hsvc & _ & _ & _ & _).
  remember (mkCfg ms mo) as c0 eqn:Ec.
  destruct Hst as [ms0 m0 ms1 m1 Hh Hp Hacc | ms0 m0 Hh Hp Hacc | ms0 m0 Hh Hp Hacc
                  | ms0 m0 x8 eff m1 m2 evs0 Hh Hp Hspec Hns Hh' Hmat
                  | ms0 m0 x8 eff m1 evs0 Hh Hp Hspec Hns Hh' Hmat
                  | ms0 m0 x8 eff m1 evs0 code Hh Hp Hspec Hh' Hk
                  | ms0 m0 x8 eff m1 evs0 sig Hh Hp Hspec Hk
                  | ms0 m0 x8 Hh Hp Hspec];
    injection Ec as -> ->.
  - (* [comment removed for export] *)
    rewrite Hacc in Hres. destruct (mi_account_step segs ms' mo) as [[ms1' mo1']| |] eqn:E; simpl in Hres; try contradiction.
    destruct Hres as [Hms <-].
    exists (SNext (mkCfg ms1' m1)). split; [apply sstep_cfg_instr; auto; congruence|]. split; [exact Hms| reflexivity].
  - rewrite Hacc in Hres. destruct (mi_account_step segs ms' mo) as [[ms1' mo1']| |] eqn:E; simpl in Hres; try contradiction.
    exists SError. split; [apply sstep_cfg_instr_fault; auto; congruence| exact I].
  - rewrite Hacc in Hres. destruct (mi_account_step segs ms' mo) as [[ms1' mo1']| |] eqn:E; simpl in Hres; try contradiction.
    exists SError. split; [apply sstep_cfg_instr_unmodeled; auto; congruence| exact I].
  - (* [comment removed for export] *)
    exists (SNext (mkCfg (advance_past_svc (apply_effect ms' eff)) m2)). split.
    + apply (sstep_cfg_syscall segs CfgStep.kit_cfg ms' mo x8 eff m1 m2 evs0);
        [assumption| congruence| rewrite <- (sys_input_eqv ms ms' x8 Heqv); assumption
        | rewrite <- (sys_input_eqv ms ms' x8 Heqv); assumption| assumption| assumption].
    + split; [| reflexivity]. apply advance_past_svc_eqv, apply_effect_eqv, Heqv.
  - (* [comment removed for export] *)
    exists SError. split; [|exact I].
    apply (sstep_cfg_syscall_materialization_fault segs CfgStep.kit_cfg ms' mo x8 eff m1 evs0);
      [assumption| congruence| rewrite <- (sys_input_eqv ms ms' x8 Heqv); assumption
      | rewrite <- (sys_input_eqv ms ms' x8 Heqv); assumption| assumption| assumption].
  - (* [comment removed for export] *)
    exists (SNext (mkCfg ms' m1)). split.
    + apply (sstep_cfg_exit segs CfgStep.kit_cfg ms' mo x8 eff m1 evs0 code);
        [assumption| congruence| rewrite <- (sys_input_eqv ms ms' x8 Heqv); assumption| assumption| assumption].
    + split; [exact Heqv| reflexivity].
  - (* [comment removed for export] *)
    exists (SNext (mkCfg ms' m1)). split.
    + apply (sstep_cfg_killed segs CfgStep.kit_cfg ms' mo x8 eff m1 evs0 sig);
        [assumption| congruence| rewrite <- (sys_input_eqv ms ms' x8 Heqv); assumption| assumption].
    + split; [exact Heqv| reflexivity].
  - exists SError. split; [|exact I].
    apply (sstep_cfg_syscall_unmodeled segs CfgStep.kit_cfg ms' mo x8);
      [assumption| congruence| rewrite <- (sys_input_eqv ms ms' x8 Heqv); assumption].
Qed.

Lemma sstep_cfg_eqv : forall c c' evs X, cfg_eqv c c' ->
  sstep_cfg segs CfgStep.kit_cfg c evs X -> exists X', sstep_cfg segs CfgStep.kit_cfg c' evs X' /\ to_eqv X X'.
Proof.
  intros [ms mo] [ms' mo'] evs X [Hms Hmo] Hst; simpl in Hms, Hmo; subst.
  apply (sstep_eqv ms ms'); assumption.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma node_ok_eqv : forall c c' (I : Type) (evs : I -> list event) (nx : I -> config),
  cfg_eqv c c' -> node_ok segs c I evs nx ->
  let I' := { p : I * config | sstep_cfg segs CfgStep.kit_cfg c' (evs (fst p)) (SNext (snd p)) /\ cfg_eqv (nx (fst p)) (snd p) } in
  node_ok segs c' I' (fun p => evs (fst (proj1_sig p))) (fun p => snd (proj1_sig p)).
Proof.
  intros c c' I evs nx Heqv [Hall Honly]. split.
  - intros [[i c2] [Hs Hc2]]. exact Hs.
  - intros e st Hst.
    cps_destruct (sstep_cfg_eqv c' c e st (cfg_eqv_sym _ _ Heqv) Hst) as (X & HstX & HX).
    cps_destruct (Honly e X HstX) as (i & He & HXi). subst e. rewrite HXi in HX.
    destruct st as [c2|]; simpl in HX; [|contradiction].
    unshelve eexists (exist _ (i, c2) _); [split; [exact Hst| apply cfg_eqv_sym; exact HX]|].
    split; reflexivity.
Qed.

Theorem realizes_eqv : forall c T, realizes segs c T -> forall c', cfg_eqv c c' -> realizes segs c' T.
Proof.
  intros c T H. induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh | c T T' H IH Heq]; intros c' Heqv.
  - pose proof (node_ok_eqv c c' I evs nx Heqv Hnode) as Hnode'. cbv beta zeta in Hnode'.
    (* [comment removed for export] *)
    cps_destruct (sstep_cfg_eqv c c' (evs i0) (SNext (nx i0)) Heqv (proj1 Hnode i0)) as (X0 & Hst0 & HX0).
    destruct X0 as [c0|]; simpl in HX0; [|contradiction].
    set (I' := { p : I * config | sstep_cfg segs CfgStep.kit_cfg c' (evs (fst p)) (SNext (snd p)) /\ cfg_eqv (nx (fst p)) (snd p) }).
    assert (i0' : I') by (exists (i0, c0); split; [exact Hst0| exact HX0]).
    eapply rz_conseq.
    + apply (rz_node segs c' I' (fun p => evs (fst (proj1_sig p))) (fun p => snd (proj1_sig p))
                     (fun p => T (fst (proj1_sig p))) i0' Hnode').
      intros [[i c2] [Hs Hc2]]. cbn. apply (IH i). exact Hc2.
    + (* [comment removed for export] *)
      intros tr. unfold t_alt. split.
      * intros ([[i c2] [Hs Hc2]] & Htr). cbn in Htr. exists i. exact Htr.
      * intros (i & Htr).
        cps_destruct (sstep_cfg_eqv c c' (evs i) (SNext (nx i)) Heqv (proj1 Hnode i)) as (X & HstX & HX).
        destruct X as [c2|]; simpl in HX; [|contradiction].
        exists (exist _ (i, c2) (conj HstX HX)). exact Htr.
  - apply rz_halt. destruct Heqv as [_ Hm]. rewrite <- Hm. exact Hh.
  - eapply rz_conseq; [apply IH; exact Heqv| exact Heq].
Qed.

Corollary realizes_ms_eqv : forall ms ms' mo T,
  ms_eqv ms ms' -> realizes segs (mkCfg ms mo) T -> realizes segs (mkCfg ms' mo) T.
Proof. intros ms ms' mo T He Hr. apply (realizes_eqv _ _ Hr). split; [exact He| reflexivity]. Qed.

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
  mkR (getr R 1) (getr R 2) (getr R 3) (getr R 4) (getr R 5) (getr R 6) (getr R 7) (getr R 8)
      (getr R 9) (getr R 10) (getr R 11) (getr R 12) (getr R 13) (getr R 14) (getr R 15) (getr R 16)
      (getr R 17) (getr R 18) (getr R 19) (getr R 20) (getr R 21) (getr R 22) (getr R 23) (getr R 24)
      (getr R 25) (getr R 26) (getr R 27) (getr R 28) (getr R 29) (getr R 30) (getr R 31).

Lemma getr_mkR_of : forall R r, getr (mkR_of R) r = getr R r.
Proof.
  intros R r. cps_destruct (reg_of_nat r) as (n & -> & Hn).
  do 32 (destruct n as [|n]; [vm_compute; reflexivity|]). lia.
Qed.

Lemma regs_eqv0_mkR_of : forall R, regs_eqv0 R (mkR_of R).
Proof.
  intros R r Hr. pose proof (getr_mkR_of R r) as E. unfold getr in E. rewrite bv_eqb0_is_x0, Hr in E.
  symmetry. exact E.
Qed.

(* [comment removed for export] *)
Lemma mkst_MS : forall R pc mem rom, mkst R pc mem rom = MS R bvmap_empty pc (Z_to_bv 32 0) None mem rom.
Proof. reflexivity. Qed.

Lemma ms_eqv_mkst_mkR : forall R pc mem rom,
  ms_eqv (mkst R pc mem rom) (MS (mkR_of R) bvmap_empty pc (Z_to_bv 32 0) None mem rom).
Proof.
  intros. rewrite mkst_MS. split; [apply regs_eqv0_mkR_of|]. repeat split; apply regs_eqv_refl.
Qed.

Section Realizes.
Variable segs : list Segment.

(* [comment removed for export] *)
Lemma realizes_to_mkR : forall R pc mem rom mo T,
  realizes segs (mkCfg (MS (mkR_of R) bvmap_empty pc (Z_to_bv 32 0) None mem rom) mo) T ->
  realizes segs (mkCfg (mkst R pc mem rom) mo) T.
Proof.
  intros. eapply realizes_ms_eqv; [| exact H]. apply ms_eqv_sym. apply ms_eqv_mkst_mkR.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma realizes_getr_ext : forall R R' pc mem rom mo T,
  (forall r, getr R r = getr R' r) ->
  realizes segs (mkCfg (mkst R pc mem rom) mo) T -> realizes segs (mkCfg (mkst R' pc mem rom) mo) T.
Proof.
  intros R R' pc mem rom mo T HG H. eapply realizes_ms_eqv; [| exact H].
  rewrite !mkst_MS. split; [| repeat split; apply regs_eqv_refl].
  intros r Hr. pose proof (HG r) as E. unfold getr in E. rewrite bv_eqb0_is_x0, Hr in E. exact E.
Qed.

End Realizes.
End GlueEqv.

(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec ShapeAlg.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Export Nodes.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil RunW.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
Section ACeilS1. Context {ACEIL__ : ACeil} {RUNW__ : RunW}.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition bid : Type := (N * Z * Z)%type.
Definition bid_eqb (a b : bid) : bool :=
  (N.eqb (fst (fst a)) (fst (fst b)) && Z.eqb (snd (fst a)) (snd (fst b))) && Z.eqb (snd a) (snd b).
Definition ablock : Type := (bid * Z * Z)%type.
Definition blk_id (b : ablock) : bid := fst (fst b).
Definition blk_addr (b : ablock) : Z := snd (fst b).
Definition blk_size (b : ablock) : Z := snd b.

Lemma bid_eqb_spec : forall a b, reflect (a = b) (bid_eqb a b).
Proof.
  intros [[a1 a2] a3] [[b1 b2] b3]. unfold bid_eqb. cbn.
  destruct (N.eqb_spec a1 b1); destruct (Z.eqb_spec a2 b2); destruct (Z.eqb_spec a3 b3); cbn; constructor; congruence.
Qed.
Lemma bid_eqb_refl : forall a, bid_eqb a a = true.
Proof. intros a. destruct (bid_eqb_spec a a); [reflexivity| congruence]. Qed.

(* [comment removed for export] *)
Definition lb_remove (p : bid) (LB : list ablock) : list ablock :=
  List.filter (fun b => negb (bid_eqb (blk_id b) p)) LB.

(* [comment removed for export] *)
Record alloc_layout : Type := mkLayout {
  al_malloc : Z;          (* [comment removed for export] *)
  al_free   : Z;          (* [comment removed for export] *)
  al_tp     : Z;          (* [comment removed for export] *)
  al_img_lo : Z;          (* [comment removed for export] *)
  al_img_hi : Z;
  al_rw_lo  : Z;          (* [comment removed for export] *)
  al_static : Z -> Prop;  (* [comment removed for export] *)
  al_private : Z -> Prop; (* [comment removed for export] *)
  al_globals : list Segment -> (word -> option byte) -> Prop;
                          (* [comment removed for export] *)
  al_stack  : Z           (* [comment removed for export] *)
}.

Definition errno_cell (L : alloc_layout) : Z := al_tp L - 164.

(* [comment removed for export] *)
Definition block_ok (L : alloc_layout) (A n : Z) : Prop :=
  0 < A /\ A mod 16 = 0 /\ 0 <= n /\ A + n <= alloc_ceiling /\ (A + n <= al_img_lo L \/ al_img_hi L <= A).

Definition in_block (LB : list ablock) (a : Z) : Prop :=
  exists b, In b LB /\ blk_addr b <= a < blk_addr b + blk_size b.

(* [comment removed for export] *)
Definition client_addr (L : alloc_layout) (LB : list ablock) (SP : Z) (a : Z) : Prop :=
  SP <= a \/ (al_rw_lo L <= a < al_img_hi L /\ ~ al_private L a /\ ~ (errno_cell L <= a < errno_cell L + 4)) \/ in_block LB a.

Definition heap_pres (segs : list Segment) (L : alloc_layout) (LB : list ablock) (SP : Z) (m m' : word -> option byte) : Prop :=
  forall a : Z, 0 <= a < 2^64 -> client_addr L LB SP a ->
    m' (wa a) = m (wa a) /\ (wview segs m (wa a) <> None -> wview segs m' (wa a) <> None).

(* [comment removed for export] *)
Definition client_range (L : alloc_layout) (LB : list ablock) (SP : Z) (A n : Z) : Prop :=
  SP <= A
  \/ (al_rw_lo L <= A /\ A + n <= al_img_hi L /\ (forall a, A <= a < A + n -> ~ al_private L a)
      /\ (A + n <= errno_cell L \/ errno_cell L + 4 <= A))
  \/ (exists b, In b LB /\ blk_addr b <= A /\ A + n <= blk_addr b + blk_size b).

(* [comment removed for export] *)
Definition client_write_ok (L : alloc_layout) (LB : list ablock) (iv : Z * Z) : Prop :=
  alloc_ceiling <= fst iv
  \/ (al_rw_lo L <= fst iv /\ snd iv <= al_img_hi L /\ (forall a, fst iv <= a < snd iv -> ~ al_static L a))
  \/ (exists b, In b LB /\ blk_addr b <= fst iv /\ snd iv <= blk_addr b + blk_size b).

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section States.
Variable segs : list Segment.

(* [comment removed for export] *)
(* [comment removed for export] *)

End States.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Record AllocIface (segs : list Segment) (L : alloc_layout) : Type := mkAllocIface {
  (* [comment removed for export] *)
  ai_AS  : Type;
  ai_inv : ai_AS -> list ablock -> (word -> option byte) -> Model -> Prop;
  (* [comment removed for export] *)
  ai_aux : (word -> option byte) -> Z -> Prop;
  (* [comment removed for export] *)
  ai_sys_ok : ai_AS -> list ablock -> Z -> Model -> Prop;

  (* [comment removed for export] *)
  ai_inv_model : forall s LB m MD, ai_inv s LB m MD -> m_halted MD = None /\ m_vm_lazy MD = [];
  ai_inv_blocks : forall s LB m MD b, ai_inv s LB m MD -> In b LB -> block_ok L (blk_addr b) (blk_size b);
  ai_inv_disjoint : forall s LB m MD b1 b2, ai_inv s LB m MD -> In b1 LB -> In b2 LB -> b1 <> b2 ->
      blk_addr b1 + blk_size b1 <= blk_addr b2 \/ blk_addr b2 + blk_size b2 <= blk_addr b1;
  ai_inv_nodup : forall s LB m MD, ai_inv s LB m MD -> NoDup (map blk_id LB);
  (* [comment removed for export] *)
  ai_inv_globals : forall s LB m MD, ai_inv s LB m MD -> al_globals L segs m;
  (* [comment removed for export] *)
  ai_inv_frame : forall s LB m m' MD W,
      ai_inv s LB m MD -> munch W m m' -> wmono segs m m' -> Forall (client_write_ok L LB) W -> ai_inv s LB m' MD;
  (* [comment removed for export] *)
  ai_inv_model_frame : forall s LB m MD MD',
      ai_inv s LB m MD -> m_vm MD' = m_vm MD -> m_halted MD' = None -> ai_inv s LB m MD';
  (* [comment removed for export] *)
  ai_aux_frame : forall m m' B W, ai_aux m B -> munch W m m' -> wmono segs m m' ->
      Forall (fun iv => snd iv <= B /\ (forall a, fst iv <= a < snd iv -> ~ al_static L a)) W -> ai_aux m' B;
  ai_aux_weaken : forall m B B', ai_aux m B -> alloc_ceiling <= B' <= B -> ai_aux m B';

  (* [comment removed for export] *)
  ai_malloc_dc : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (MD : Model)
      (s : ai_AS) (LB : list ablock) (n lo B : Z) (errv : word) (T : TSet),
    ai_inv s LB m MD ->
    ai_aux m B -> bv_unsigned sp <= B ->
    stk segs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - al_stack L ->
    rw_cells segs m (errno_cell L) [C4 errv] ->
    mem_inv segs m ->
    tp = Z_to_bv 64 (al_tp L) ->
    a0 = Z_to_bv 64 n -> 0 <= n < 2^32 ->
    (forall (s' : ai_AS) (LB' : list ablock) (m' : word -> option byte) (MD' : Model) (r : Z)
            (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' errv' : word),
        ai_inv s' LB' m' MD' -> vm_only MD MD' ->
        mem_inv segs m' -> stk segs m' lo (bv_unsigned sp) -> rw_cells segs m' (errno_cell L) [C4 errv'] -> ai_aux m' B ->
        heap_pres segs L LB (bv_unsigned sp) m m' ->
        ((r = 0 /\ LB' = LB)
         \/ (r <> 0 /\ block_ok L r n /\ (exists p, LB' = (p, r, n) :: LB /\ ~ In p (map blk_id LB))
             /\ exists junk, rw_cells segs m' r [CB (Z.to_nat n) junk])) ->
        realizes segs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 r) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                                  F (ret_pc ra) fc None m' (seg_rom segs)) MD') T) ->
    realizes segs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                              F (Z_to_bv 64 (al_malloc L)) fc None m (seg_rom segs)) MD) T;

  (* [comment removed for export] *)
  ai_malloc_sys : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (MD : Model)
      (s : ai_AS) (LB : list ablock) (n lo B : Z) (errv : word) (Tok : TSet),
    ai_inv s LB m MD -> ai_sys_ok s LB n MD ->
    ai_aux m B -> bv_unsigned sp <= B ->
    stk segs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - al_stack L ->
    rw_cells segs m (errno_cell L) [C4 errv] ->
    mem_inv segs m ->
    tp = Z_to_bv 64 (al_tp L) ->
    a0 = Z_to_bv 64 n -> 0 < n < 2^32 ->
    (forall (s' : ai_AS) (m' : word -> option byte) (MD' : Model) (r : Z) (p : bid)
            (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' errv' : word) (junk : list byte),
        ai_inv s' ((p, r, n) :: LB) m' MD' -> vm_only MD MD' ->
        mem_inv segs m' -> stk segs m' lo (bv_unsigned sp) -> rw_cells segs m' (errno_cell L) [C4 errv'] -> ai_aux m' B ->
        heap_pres segs L LB (bv_unsigned sp) m m' ->
        r <> 0 -> block_ok L r n -> ~ In p (map blk_id LB) -> rw_cells segs m' r [CB (Z.to_nat n) junk] ->
        realizes segs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 r) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                                  F (ret_pc ra) fc None m' (seg_rom segs)) MD') Tok) ->
    realizes segs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                              F (Z_to_bv 64 (al_malloc L)) fc None m (seg_rom segs)) MD) Tok;

  (* [comment removed for export] *)
  ai_free : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (MD : Model)
      (s : ai_AS) (LB : list ablock) (p : bid) (A n lo B : Z) (errv : word) (T : TSet),
    ai_inv s LB m MD -> In (p, A, n) LB ->
    ai_aux m B -> bv_unsigned sp <= B ->
    stk segs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - al_stack L ->
    rw_cells segs m (errno_cell L) [C4 errv] ->
    mem_inv segs m ->
    tp = Z_to_bv 64 (al_tp L) ->
    a0 = Z_to_bv 64 A ->
    (forall (s' : ai_AS) (m' : word -> option byte) (MD' : Model)
            (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
        ai_inv s' (lb_remove p LB) m' MD' -> vm_only MD MD' ->
        mem_inv segs m' -> stk segs m' lo (bv_unsigned sp) -> rw_cells segs m' (errno_cell L) [C4 errv] -> ai_aux m' B ->
        heap_pres segs L (lb_remove p LB) (bv_unsigned sp) m m' ->
        realizes segs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                                  F (ret_pc ra) fc None m' (seg_rom segs)) MD') T) ->
    realizes segs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                              F (Z_to_bv 64 (al_free L)) fc None m (seg_rom segs)) MD) T;

  (* [comment removed for export] *)
  ai_free_null : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (MD : Model) (T : TSet),
    m_halted MD = None -> m_vm_lazy MD = [] ->
    a0 = Z_to_bv 64 0 ->
    realizes segs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                              F (ret_pc ra) fc None m (seg_rom segs)) MD) T ->
    realizes segs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                              F (Z_to_bv 64 (al_free L)) fc None m (seg_rom segs)) MD) T
}.
End ACeilS1.


Arguments ai_AS {ACEIL__ segs L} _.
Arguments ai_inv {ACEIL__ segs L} _ _ _ _ _.
Arguments ai_aux {ACEIL__ segs L} _ _ _.
Arguments ai_sys_ok {ACEIL__ segs L} _ _ _ _ _.
Arguments ai_inv_model {ACEIL__ segs L} _ [s LB m MD] _.
Arguments ai_inv_blocks {ACEIL__ segs L} _ [s LB m MD b] _ _.
Arguments ai_inv_disjoint {ACEIL__ segs L} _ [s LB m MD b1 b2] _ _ _ _.
Arguments ai_inv_nodup {ACEIL__ segs L} _ [s LB m MD] _.
Arguments ai_inv_globals {ACEIL__ segs L} _ [s LB m MD] _.
Arguments ai_inv_frame {ACEIL__ segs L} _ [s LB m m' MD W] _ _ _ _.
Arguments ai_inv_model_frame {ACEIL__ segs L} _ [s LB m MD MD'] _ _ _.
Arguments ai_aux_frame {ACEIL__ segs L} _ [m m' B W] _ _ _.
Arguments ai_aux_weaken {ACEIL__ segs L} _ [m B B'] _ _.
Arguments ai_malloc_dc {ACEIL__ segs L} _.
Arguments ai_malloc_sys {ACEIL__ segs L} _.
Arguments ai_free {ACEIL__ segs L} _.
Arguments ai_free_null {ACEIL__ segs L} _.
Section ACeilS2. Context {ACEIL__ : ACeil} {RUNW__ : RunW}.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section ClientLemmas.
Variable segs : list Segment.
Variable L : alloc_layout.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma client_range_addr : forall LB SP A n a,
  client_range L LB SP A n -> A <= a < A + n -> client_addr L LB SP a.
Proof.
  intros LB SP A n a HR Ha. unfold client_range, client_addr in *.
  destruct HR as [H|[(H1 & H2 & H3 & H4)|(b & Hb & H1 & H2)]]; [left; lia| right; left| right; right].
  - split; [lia|]. split; [apply H3; lia| lia].
  - exists b. split; [exact Hb|lia].
Qed.

(* [comment removed for export] *)
Lemma heap_pres_bytes_at : forall LB SP m m' A bs,
  heap_pres segs L LB SP m m' -> bytes_at segs m A bs -> client_range L LB SP A (Z.of_nat (length bs)) ->
  bytes_at segs m' A bs.
Proof.
  (intros LB SP m m' A bs HP; cps_intros (H0 & H1 & HB); intros HR). split; [exact H0|]. split; [exact H1|].
  intros i Hi. rewrite <- (HB i Hi). unfold mrd.
  destruct (HP (A + Z.of_nat i) ltac:(lia) ltac:(eapply client_range_addr; [exact HR|lia])) as [E _].
  rewrite E. reflexivity.
Qed.

Lemma heap_pres_wr_at : forall LB SP m m' A n,
  heap_pres segs L LB SP m m' -> wr_at segs m A n -> client_range L LB SP A n -> wr_at segs m' A n.
Proof.
  (intros LB SP m m' A n HP; cps_intros (H0 & H1 & HW); intros HR). split; [exact H0|]. split; [exact H1|].
  intros i Hi. destruct (HP (A + i) ltac:(lia) ltac:(eapply client_range_addr; [exact HR|lia])) as [_ W].
  apply W. apply HW. exact Hi.
Qed.

Lemma heap_pres_rw_cells : forall LB SP m m' A cs,
  heap_pres segs L LB SP m m' -> rw_cells segs m A cs -> client_range L LB SP A (Z.of_nat (cells_size cs)) ->
  rw_cells segs m' A cs.
Proof.
  intros LB SP m m' A cs HP [[Hwf HB] HW] HR. split; [split; [exact Hwf|]|].
  - eapply heap_pres_bytes_at; eauto. rewrite cells_bytes_length by assumption. exact HR.
  - eapply heap_pres_wr_at; eauto.
Qed.

Lemma heap_pres_u8arr : forall LB SP m m' A xs,
  heap_pres segs L LB SP m m' -> u8arr segs m A xs -> client_range L LB SP A (Z.of_nat (length xs)) ->
  u8arr segs m' A xs.
Proof.
  intros LB SP m m' A xs HP H HR. apply (u8arr_of_rw_cells segs m' A (length xs)).
  eapply heap_pres_rw_cells; [exact HP| apply rw_cells_of_u8arr; exact H|].
  cbn [cells_size csize]. rewrite Nat.add_0_r. exact HR.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

Lemma lb_remove_head : forall p A n LB, ~ In p (map blk_id LB) -> lb_remove p ((p, A, n) :: LB) = LB.
Proof.
  intros p A n LB H. unfold lb_remove. cbn [List.filter blk_id fst]. rewrite bid_eqb_refl. cbn [negb].
  induction LB as [|b LB IH]; [reflexivity|]. cbn in *.
  destruct (bid_eqb_spec (blk_id b) p) as [E|NE]; [exfalso; apply H; left; exact E|].
  cbn. f_equal. apply IH. intros K. apply H. right. exact K.
Qed.

(* [comment removed for export] *)
Lemma lb_remove_keep : forall p LB b, In b LB -> blk_id b <> p -> In b (lb_remove p LB).
Proof.
  intros p LB b Hin Hne. unfold lb_remove. apply (proj2 (List.filter_In _ _ _)). split; [exact Hin|].
  destruct (bid_eqb_spec (blk_id b) p); [contradiction| reflexivity].
Qed.

End ClientLemmas.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)  (* [comment removed for export] *)
(* [comment removed for export] *)   (* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

End ACeilS2.
