(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the vDSO arms of sstep and unmodeled_at along ms_eqv, the vvar case of loads and fetches, and init_ms over the launch's entry block). *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import PropExec MState Frame.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition regs_eqv (R R' : bvmap 5 word) : Prop := forall r, reg_get R r = reg_get R' r.

Lemma regs_eqv_refl : forall R, regs_eqv R R.
Proof. intros R r. reflexivity. Qed.
Lemma regs_eqv_sym : forall R R', regs_eqv R R' -> regs_eqv R' R.
Proof. intros R R' H r. symmetry. apply H. Qed.
Lemma regs_eqv_trans : forall R1 R2 R3, regs_eqv R1 R2 -> regs_eqv R2 R3 -> regs_eqv R1 R3.
Proof. intros R1 R2 R3 H1 H2 r. etransitivity; [apply H1|apply H2]. Qed.

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
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition core_eqv (c c' : core) : Prop :=
  regs_eqv (c_regs c) (c_regs c') /\ regs_eqv (c_fregs c) (c_fregs c') /\
  c_pc c = c_pc c' /\ c_fcsr c = c_fcsr c' /\ c_resv c = c_resv c'.

(* [comment removed for export] *)
Inductive eff_eqv : eff -> eff -> Prop :=
| EqvDone : forall c c', core_eqv c c' -> eff_eqv (EDone c) (EDone c')
| EqvIllegal : forall c c', eff_eqv (EIllegal c) (EIllegal c')
| EqvEcall : forall c c', eff_eqv (EEcall c) (EEcall c')
| EqvEbreak : forall c c', eff_eqv (EEbreak c) (EEbreak c')
| EqvFault : forall c c', eff_eqv (EFault c) (EFault c')
| EqvDefIllegal : forall c c', eff_eqv (EDefinedIllegal c) (EDefinedIllegal c')   (* [comment removed for export] *)
| EqvLoad : forall n a k k', (forall v, eff_eqv (k v) (k' v)) -> eff_eqv (ELoad n a k) (ELoad n a k')
| EqvStore : forall n a v k k', eff_eqv k k' -> eff_eqv (EStore n a v k) (EStore n a v k').

Lemma core_eqv_mk : forall R R' F F' pc fc rv, regs_eqv R R' -> regs_eqv F F' ->
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
  repeat split; auto using regs_eqv_set.
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

(* [comment removed for export] *)
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

(* [comment removed for export] *)
Local Ltac unfold_exec :=
  cbv beta iota zeta delta [exec rget fget fread c_regs c_fregs c_pc c_fcsr c_resv
                            with_pc load_val store_val exec_csr resolve_rm frm_of].

(* [comment removed for export] *)
Lemma exec_eqv_core : forall R R' F F' pc fc rv sz i,
  regs_eqv R R' -> regs_eqv F F' ->
  eff_eqv (exec sz i (Core R F pc fc rv)) (exec sz i (Core R' F' pc fc rv)).
Proof.
  intros R R' F F' pc fc rv sz i HR HF.
  destruct i; unfold_exec; rewrite ?HR, ?HF; eqv_struct HR HF.
Qed.

Lemma exec_eqv : forall sz i c c', core_eqv c c' -> eff_eqv (exec sz i c) (exec sz i c').
Proof.
  intros sz i [R F p f s] [R' F' p' f' s'] (HR & HF & Hp & Hf & Hs); simpl in *; subst.
  apply exec_eqv_core; assumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition ms_eqv (ms ms' : machine_state) : Prop :=
  regs_eqv (ms_regs ms) (ms_regs ms') /\ regs_eqv (ms_fregs ms) (ms_fregs ms') /\
  ms_pc_val ms = ms_pc_val ms' /\ ms_svc_pending ms = ms_svc_pending ms' /\
  ms_resv ms = ms_resv ms' /\ ms_fcsr ms = ms_fcsr ms' /\
  ms_mem ms = ms_mem ms' /\ ms_rom ms = ms_rom ms'.

Lemma ms_eqv_refl : forall ms, ms_eqv ms ms.
Proof. intros ms. repeat split; apply regs_eqv_refl. Qed.
Lemma ms_eqv_sym : forall ms ms', ms_eqv ms ms' -> ms_eqv ms' ms.
Proof.
  intros ms ms' (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8).
  repeat split; auto using regs_eqv_sym; congruence.
Qed.
Lemma ms_eqv_trans : forall a b c, ms_eqv a b -> ms_eqv b c -> ms_eqv a c.
Proof.
  intros a b c (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8) (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8).
  repeat split; eauto using regs_eqv_trans; congruence.
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

(* [comment removed for export] *)
Lemma interp_eff_accesses_eqv : forall t t', eff_eqv t t' -> forall m,
  match interp_eff_accesses segs t m, interp_eff_accesses segs t' m with
  | MachineOk rep, MachineOk rep' =>
      core_eqv (fst (access_value _ rep)) (fst (access_value _ rep')) /\
      snd (access_value _ rep) = snd (access_value _ rep') /\
      accessed_ranges _ rep = accessed_ranges _ rep'
  | MachineFault, MachineFault => True
  | MachineUnmodeled, MachineUnmodeled => True
  | _, _ => False
  end.
Proof.
  intros t t' H. induction H; intros m; cbn [interp_eff_accesses]; auto.
  - destruct (ov_read_bytes segs m a (width_bytes n)) as [bs|];
      [|destruct (range_meets_vvar segs a (width_bytes n)); exact I].
    specialize (H0 (bv_extract 0 n (le_bytes_to_word bs)) m).
    destruct (interp_eff_accesses segs (k _) m) as [rep| |]; destruct (interp_eff_accesses segs (k' _) m) as [rep'| |];
      cbn [access_value accessed_ranges] in *; try exact H0; try contradiction.
    destruct H0 as (A & B & C). split; [exact A|]. split; [exact B|]. cbn. f_equal. exact C.
  - destruct (store_ok segs m a (width_bytes n)); [|exact I].
    specialize (IHeff_eqv (write_to_mem m a (Z_to_le_bytes (width_bytes n) (bv_unsigned v)))).
    destruct (interp_eff_accesses segs k _) as [rep| |]; destruct (interp_eff_accesses segs k' _) as [rep'| |];
      cbn [access_value accessed_ranges] in *; try exact IHeff_eqv; try contradiction.
    destruct IHeff_eqv as (A & B & C). split; [exact A|]. split; [exact B|]. cbn. f_equal. exact C.
Qed.

Lemma interp_eff_eqv : forall t t', eff_eqv t t' -> forall m,
  match interp_eff segs t m, interp_eff segs t' m with
  | MachineOk (c, m1), MachineOk (c', m1') => core_eqv c c' /\ m1 = m1'
  | MachineFault, MachineFault => True
  | MachineUnmodeled, MachineUnmodeled => True
  | _, _ => False
  end.
Proof.
  intros t t' H m. pose proof (interp_eff_accesses_eqv t t' H m) as K. unfold interp_eff, drop_access_report.
  destruct (interp_eff_accesses segs t m) as [[[c m1] l]| |]; destruct (interp_eff_accesses segs t' m) as [[[c' m1'] l']| |];
    cbn [access_value accessed_ranges fst snd] in K |- *; try exact K. destruct K as (A & B & _). split; assumption.
Qed.

Lemma ms_reg_eqv : forall ms ms' r, ms_eqv ms ms' -> ms_reg ms r = ms_reg ms' r.
Proof. intros ms ms' r (HR & _). unfold ms_reg. rewrite (HR r). reflexivity. Qed.

(* [comment removed for export] *)
Definition ares_eqv (r r' : machine_result (access_report machine_state)) : Prop :=
  match r, r' with
  | MachineOk rep, MachineOk rep' => ms_eqv (access_value _ rep) (access_value _ rep') /\
                                    accessed_ranges _ rep = accessed_ranges _ rep'
  | MachineFault, MachineFault => True
  | MachineUnmodeled, MachineUnmodeled => True
  | _, _ => False
  end.

Lemma decode_exec_accesses_eqv : forall ms ms' w, ms_eqv ms ms' ->
  ares_eqv (decode_exec_accesses segs ms w) (decode_exec_accesses segs ms' w).
Proof.
  intros ms ms' w Heqv. pose proof (ms_reg_eqv ms ms' 17 Heqv) as H17.
  destruct ms as [R F pc svc rv fc m ro], ms' as [R' F' pc' svc' rv' fc' m' ro'].
  destruct Heqv as (HR & HF & Hpc & Hsvc & Hrv & Hfc & Hm & Hro); simpl in *; subst.
  unfold decode_exec_accesses. destruct (is_ecall w).
  - simpl. rewrite H17. repeat split; assumption.
  - destruct (decode_any w) as [[i isz]|]; [| destruct (is_defined_illegal w); exact I]. simpl.
    pose proof (interp_eff_accesses_eqv _ _ (exec_eqv_core R R' F F' pc' fc' rv' (Z_to_bv 64 isz) i HR HF) m') as K.
    destruct (interp_eff_accesses segs (exec _ i (Core R F pc' fc' rv')) m') as [[[c m1] l]| |];
    destruct (interp_eff_accesses segs (exec _ i (Core R' F' pc' fc' rv')) m') as [[[c2 m2] l2]| |];
    simpl in *; try exact K; try contradiction.
    destruct K as ((H1 & H2 & H3 & H4 & H5) & -> & ->). repeat split; simpl; auto.
Qed.

Lemma step_accesses_eqv : forall ms ms', ms_eqv ms ms' ->
  ares_eqv (RiscvSemantics.step_accesses segs ms) (RiscvSemantics.step_accesses segs ms').
Proof.
  intros ms ms' Heqv. pose proof Heqv as (_ & _ & Hpc & _ & _ & _ & Hm & _).
  unfold RiscvSemantics.step_accesses, ms_pc. rewrite <- Hpc, <- Hm.
  destruct (fetch_word segs (ms_pc_val ms)); [apply decode_exec_accesses_eqv; exact Heqv|].
  destruct (fetch_word_ov segs (ms_mem ms) (ms_pc_val ms)); [apply decode_exec_accesses_eqv; exact Heqv|].
  destruct (fetch_tail_any segs (ms_mem ms) (ms_pc_val ms)); [apply decode_exec_accesses_eqv; exact Heqv|].
  unfold fetch_failure. destruct (vdso_text_at _ _); [exact I|].
  destruct (negb _); [exact I|]. destruct (_ || _)%bool; exact I.
Qed.

Lemma step_eqv : forall ms ms', ms_eqv ms ms' ->
  res_eqv (RiscvSemantics.step segs ms) (RiscvSemantics.step segs ms').
Proof.
  intros ms ms' Heqv. pose proof (step_accesses_eqv ms ms' Heqv) as K.
  unfold RiscvSemantics.step, drop_access_report.
  destruct (RiscvSemantics.step_accesses segs ms) as [rep| |]; destruct (RiscvSemantics.step_accesses segs ms') as [rep'| |];
    cbn in K |- *; tauto.
Qed.

Lemma mi_account_step_eqv : forall ms ms' mo, ms_eqv ms ms' ->
  match mi_account_step segs ms mo, mi_account_step segs ms' mo with
  | MachineOk (a, mo1), MachineOk (b, mo2) => ms_eqv a b /\ mo1 = mo2
  | MachineFault, MachineFault => True
  | MachineUnmodeled, MachineUnmodeled => True
  | _, _ => False
  end.
Proof.
  intros ms ms' mo Heqv. pose proof (step_accesses_eqv ms ms' Heqv) as K. unfold mi_account_step.
  destruct (RiscvSemantics.step_accesses segs ms) as [rep| |]; destruct (RiscvSemantics.step_accesses segs ms') as [rep'| |];
    cbn in K; try exact K; try contradiction.
  destruct K as [Hv <-]. destruct (materialize_model_accesses mo (accessed_ranges _ rep)); [|exact I]. auto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma syscall_args_eqv : forall ms ms', ms_eqv ms ms' -> syscall_args ms = syscall_args ms'.
Proof. intros ms ms' (HR & _). unfold syscall_args, ms_gpr. rewrite !HR. reflexivity. Qed.

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

(* LPS 08b1429: the vDSO arms of [sstep] (port of the zstd tree's RegsEquiv repair) *)
Lemma set_reg_eqv : forall ms ms' r v, ms_eqv ms ms' -> ms_eqv (set_reg ms r v) (set_reg ms' r v).
Proof.
  intros [R F pc svc rv fc m ro] [R' F' pc' svc' rv' fc' m' ro'] r v
         (HR & HF & Hpc & Hsvc & Hrv & Hfc & Hm & Hro); simpl in *; subst.
  unfold set_reg. destruct (bv_eqb r 0); repeat split; simpl; auto using regs_eqv_set.
Qed.

Lemma vdso_write_regs_eqv : forall rs vs ms ms', ms_eqv ms ms' ->
  ms_eqv (vdso_write_regs ms rs vs) (vdso_write_regs ms' rs vs).
Proof.
  induction rs as [|r rs IH]; intros vs ms ms' H; [exact H|].
  destruct vs as [|v vs]; [exact H|].
  cbn [vdso_write_regs]. apply IH, set_reg_eqv, H.
Qed.

Lemma ms_read_byte_eqv : forall ms ms', ms_eqv ms ms' -> ms_read_byte ms = ms_read_byte ms'.
Proof.
  intros [R F pc svc rv fc m ro] [R' F' pc' svc' rv' fc' m' ro']
         (HR & HF & Hpc & Hsvc & Hrv & Hfc & Hm & Hro); simpl in *; subst. reflexivity.
Qed.

Lemma ms_sp_eqv : forall ms ms', ms_eqv ms ms' -> ms_sp ms = ms_sp ms'.
Proof. intros ms ms' (HR & _). unfold ms_sp. apply HR. Qed.

Lemma vdso_read_regs_eqv : forall ms ms', ms_eqv ms ms' -> vdso_read_regs ms = vdso_read_regs ms'.
Proof.
  intros ms ms' H. unfold vdso_read_regs. apply List.map_ext.
  intros r. apply (ms_reg_eqv _ _ _ H).
Qed.

Lemma vdso_with_mem_eqv : forall ms ms' m, ms_eqv ms ms' ->
  ms_eqv (vdso_with_mem ms m) (vdso_with_mem ms' m).
Proof.
  intros [R F pc svc rv fc m0 ro] [R' F' pc' svc' rv' fc' m0' ro'] m
         (HR & HF & Hpc & Hsvc & Hrv & Hfc & Hm & Hro); simpl in *; subst.
  unfold vdso_with_mem. repeat split; simpl; auto.
Qed.

Lemma vdso_set_pc_eqv : forall ms ms' pc, ms_eqv ms ms' ->
  ms_eqv (vdso_set_pc ms pc) (vdso_set_pc ms' pc).
Proof.
  intros [R F pc0 svc rv fc m ro] [R' F' pc0' svc' rv' fc' m' ro'] pc
         (HR & HF & Hpc & Hsvc & Hrv & Hfc & Hm & Hro); simpl in *; subst.
  unfold vdso_set_pc. repeat split; simpl; auto.
Qed.

Lemma vdso_post_eqv : forall ms ms' model fr eff, ms_eqv ms ms' ->
  ms_eqv (vdso_post segs ms model fr eff) (vdso_post segs ms' model fr eff).
Proof.
  intros ms ms' model fr eff H.
  unfold vdso_post. cbv zeta.
  rewrite (ms_reg_eqv _ _ _ H), (ms_sp_eqv _ _ H), (vdso_read_regs_eqv _ _ H), (ms_read_byte_eqv _ _ H).
  match goal with |- ms_eqv (vdso_set_pc (apply_effect (vdso_with_mem (vdso_write_regs ms ?rs ?vs) _) _) _) _ =>
    pose proof (vdso_write_regs_eqv rs vs ms ms' H) as HW end.
  pose proof HW as (_ & _ & _ & _ & _ & _ & Hmw & _). rewrite Hmw.
  apply vdso_set_pc_eqv, apply_effect_eqv, vdso_with_mem_eqv, HW.
Qed.

Lemma vdso_call_unmodeled_eqv : forall ms ms' mo fn, ms_eqv ms ms' ->
  vdso_call_unmodeled segs ms mo fn -> vdso_call_unmodeled segs ms' mo fn.
Proof.
  intros ms ms' mo fn H Hun. unfold vdso_call_unmodeled in *.
  destruct Hun as [Hn0 | [(n0 & Hn0 & Hsp0) | (n0 & e0 & m0 & v0 & Hn0 & Hsp0 & Hor)]].
  - left. exact Hn0.
  - right. left. exists n0. split; [exact Hn0|]. rewrite <- (sys_input_eqv ms ms' _ H). exact Hsp0.
  - right. right. exists n0, e0, m0, v0. split; [exact Hn0|]. split; [|exact Hor].
    rewrite <- (sys_input_eqv ms ms' _ H). exact Hsp0.
Qed.

Lemma sstep_eqv : forall ms ms' mo evs X, ms_eqv ms ms' ->
  sstep segs (mkCfg ms mo) evs X ->
  exists X', sstep segs (mkCfg ms' mo) evs X' /\ to_eqv X X'.
Proof.
  intros ms ms' mo evs X Heqv Hst.
  pose proof (mi_account_step_eqv ms ms' mo Heqv) as Hres.
  pose proof Heqv as (_ & _ & Hpc & Hsvc & _ & _ & _ & _).
  inversion Hst; subst.
  - (* [comment removed for export] *)
    match goal with H : mi_account_step segs ms mo = _ |- _ => rewrite H in Hres end.
    destruct (mi_account_step segs ms' mo) as [[ms1' mo1']| |] eqn:E; simpl in Hres; try contradiction.
    destruct Hres as [Hms <-].
    exists (SNext (mkCfg ms1' model')). split; [apply sstep_instr; auto; congruence|]. split; [exact Hms| reflexivity].
  - match goal with H : mi_account_step segs ms mo = _ |- _ => rewrite H in Hres end.
    destruct (mi_account_step segs ms' mo) as [[ms1' mo1']| |] eqn:E; simpl in Hres; try contradiction.
    exists SError. split; [apply sstep_instr_fault; auto; congruence| exact I].
  - match goal with H : mi_account_step segs ms mo = _ |- _ => rewrite H in Hres end.
    destruct (mi_account_step segs ms' mo) as [[ms1' mo1']| |] eqn:E; simpl in Hres; try contradiction.
    exists SError. split; [|exact I].
    apply sstep_instr_unmodeled; [assumption | congruence | exact E |].
    match goal with Hx : vdso_entry_fn _ (ms_pc ms) = None |- _ =>
      unfold ms_pc in *; rewrite <- Hpc; exact Hx end.
  - match goal with Hx : mi_account_step segs ms mo = _ |- _ => rewrite Hx in Hres end.
    destruct (mi_account_step segs ms' mo) as [[ms1' mo1']| |] eqn:E; simpl in Hres; try contradiction.
    unfold ms_pc in *. rewrite Hpc in *.
    repeat match goal with Hx : context [sys_input segs ms ?x] |- _ => rewrite (sys_input_eqv ms ms' x Heqv) in Hx end.
    eexists. split.
    + eapply sstep_vdso_call; eauto; congruence.
    + cbn [to_eqv cfg_eqv cfg_ms cfg_model]. split; [apply vdso_post_eqv, Heqv | reflexivity].
  - match goal with Hx : mi_account_step segs ms mo = _ |- _ => rewrite Hx in Hres end.
    destruct (mi_account_step segs ms' mo) as [[ms1' mo1']| |] eqn:E; simpl in Hres; try contradiction.
    unfold ms_pc in *. rewrite Hpc in *.
    repeat match goal with Hx : context [sys_input segs ms ?x] |- _ => rewrite (sys_input_eqv ms ms' x Heqv) in Hx end.
    exists SError. split; [eapply sstep_vdso_materialization_fault; eauto; congruence | exact I].
  - match goal with Hx : mi_account_step segs ms mo = _ |- _ => rewrite Hx in Hres end.
    destruct (mi_account_step segs ms' mo) as [[ms1' mo1']| |] eqn:E; simpl in Hres; try contradiction.
    exists SError. split; [|exact I].
    match goal with Hx : vdso_call_unmodeled _ ms mo _ |- _ =>
      pose proof (vdso_call_unmodeled_eqv ms ms' mo _ Heqv Hx) as Hun' end.
    unfold ms_pc in *. rewrite Hpc in *.
    eapply sstep_vdso_unmodeled; eauto; congruence.
  - (* [comment removed for export] *)
    exists (SNext (mkCfg (advance_past_svc (apply_effect ms' eff)) model'')). split.
    + apply (sstep_syscall segs ms' mo x8 eff model' model'' evs);
        [assumption| congruence| rewrite <- (sys_input_eqv ms ms' x8 Heqv); assumption| assumption| assumption].
    + split; [| reflexivity]. apply advance_past_svc_eqv, apply_effect_eqv, Heqv.
  - (* [comment removed for export] *)
    exists SError. split; [|exact I].
    apply (sstep_syscall_materialization_fault segs ms' mo x8 eff model' evs0);
      [assumption| congruence| rewrite <- (sys_input_eqv ms ms' x8 Heqv); assumption| assumption| assumption].
  - (* [comment removed for export] *)
    exists (SNext (mkCfg ms' model')). split.
    + apply (sstep_exit segs ms' mo x8 eff model' evs0 code);
        [assumption| congruence| rewrite <- (sys_input_eqv ms ms' x8 Heqv); assumption| assumption| assumption].
    + split; [exact Heqv| reflexivity].
  - (* [comment removed for export] *)
    exists (SNext (mkCfg ms' model')). split.
    + apply (sstep_killed segs ms' mo x8 eff model' evs0 sig);
        [assumption| congruence| rewrite <- (sys_input_eqv ms ms' x8 Heqv); assumption| assumption].
    + split; [exact Heqv| reflexivity].
  - exists SError. split; [|exact I].
    apply (sstep_syscall_unmodeled segs ms' mo x8);
      [assumption| congruence| rewrite <- (sys_input_eqv ms ms' x8 Heqv); assumption].
Qed.

Lemma sstep_cfg_eqv : forall c c' evs X, cfg_eqv c c' ->
  sstep segs c evs X -> exists X', sstep segs c' evs X' /\ to_eqv X X'.
Proof.
  intros [ms mo] [ms' mo'] evs X [Hms Hmo] Hst; simpl in Hms, Hmo; subst.
  apply (sstep_eqv ms ms'); assumption.
Qed.

Lemma star_eqv : forall c tr c1, star segs c tr c1 ->
  forall c', cfg_eqv c c' -> exists c1', star segs c' tr c1' /\ cfg_eqv c1 c1'.
Proof.
  intros c tr c1 H. induction H as [c | c evs c2 tr c3 Hst Hstar IH]; intros c' Heqv.
  - exists c'. split; [apply star_refl| exact Heqv].
  - destruct (sstep_cfg_eqv c c' evs (SNext c2) Heqv Hst) as (X' & Hst' & HX).
    destruct X' as [c2'|]; simpl in HX; [|contradiction].
    destruct (IH c2' HX) as (c3' & Hstar' & H3).
    exists c3'. split; [eapply star_step; eassumption| exact H3].
Qed.

Lemma obs_trace_eqv : forall c c' tr, cfg_eqv c c' -> obs_trace segs c tr -> obs_trace segs c' tr.
Proof.
  intros c c' tr Heqv (tr' & c1 & Hstar & Hp).
  destruct (star_eqv c tr' c1 Hstar c' Heqv) as (c1' & Hstar' & _).
  exists tr', c1'. split; assumption.
Qed.

Lemma reaches_error_eqv : forall c c', cfg_eqv c c' -> reaches_error segs c -> reaches_error segs c'.
Proof.
  intros c c' Heqv (tr & c1 & evs & Hstar & Hst).
  destruct (star_eqv c tr c1 Hstar c' Heqv) as (c1' & Hstar' & H1).
  destruct (sstep_cfg_eqv c1 c1' evs SError H1 Hst) as (X' & Hst' & HX).
  destruct X'; simpl in HX; [contradiction|].
  exists tr, c1', evs. split; assumption.
Qed.

Lemma unmodeled_at_eqv : forall c c', cfg_eqv c c' -> unmodeled_at segs c -> unmodeled_at segs c'.
Proof.
  intros [ms mo] [ms' mo'] [Hms Hmo] Hun; simpl in Hms, Hmo; subst.
  unfold unmodeled_at in *. cbn [cfg_ms cfg_model] in *. destruct Hun as (Hh & Hcase).
  pose proof Hms as (_ & _ & Hpc & Hsvc & _ & _ & _ & _).
  pose proof (mi_account_step_eqv ms ms' mo' Hms) as Hres.
  split; [exact Hh|].
  destruct Hcase as [(Hnone & Hstep & Hvd) | [(Hnone & Hstep & fn & Hfn & Hun) | (x8 & Hsome & Hspec)]].
  - left. rewrite Hstep in Hres.
    destruct (mi_account_step segs ms' mo') as [[? ?]| |]; simpl in Hres; try contradiction.
    split; [congruence|]. split; [reflexivity|]. unfold ms_pc in *. rewrite <- Hpc. exact Hvd.
  - right. left. rewrite Hstep in Hres.
    destruct (mi_account_step segs ms' mo') as [[? ?]| |]; simpl in Hres; try contradiction.
    split; [congruence|]. split; [reflexivity|]. exists fn. split.
    + unfold ms_pc in *. rewrite <- Hpc. exact Hfn.
    + exact (vdso_call_unmodeled_eqv ms ms' mo' fn Hms Hun).
  - right. right. exists x8. split; [congruence|]. rewrite <- (sys_input_eqv ms ms' x8 Hms). exact Hspec.
Qed.

Lemma reaches_unmodeled_eqv : forall c c', cfg_eqv c c' ->
  reaches_unmodeled segs c -> reaches_unmodeled segs c'.
Proof.
  intros c c' Heqv (tr & c1 & Hstar & Hun).
  destruct (star_eqv c tr c1 Hstar c' Heqv) as (c1' & Hstar' & H1).
  exists tr, c1'. split; [exact Hstar'| eapply unmodeled_at_eqv; eassumption].
Qed.

Lemma all_traces_error_eqv : forall c, all_traces_error segs c ->
  forall c', cfg_eqv c c' -> all_traces_error segs c'.
Proof.
  intros c H. induction H as [c Hprog Hnext IH]; intros c' Heqv.
  constructor.
  - destruct Hprog as (evs & to & Hst).
    destruct (sstep_cfg_eqv c c' evs to Heqv Hst) as (X' & Hst' & _). eauto.
  - intros evs c2' Hst'.
    destruct (sstep_cfg_eqv c' c evs (SNext c2') (cfg_eqv_sym _ _ Heqv) Hst') as (X & Hst & HX).
    destruct X as [c2|]; simpl in HX; [|contradiction].
    apply (IH evs c2 Hst). apply cfg_eqv_sym. exact HX.
Qed.

(* [comment removed for export] *)
Theorem behaviour_eqv : forall ms ms' mo, ms_eqv ms ms' ->
  (forall tr, obs_trace segs (mkCfg ms mo) tr <-> obs_trace segs (mkCfg ms' mo) tr) /\
  (reaches_error segs (mkCfg ms mo) <-> reaches_error segs (mkCfg ms' mo)) /\
  (all_traces_error segs (mkCfg ms mo) <-> all_traces_error segs (mkCfg ms' mo)) /\
  (reaches_unmodeled segs (mkCfg ms mo) <-> reaches_unmodeled segs (mkCfg ms' mo)).
Proof.
  intros ms ms' mo Heqv.
  assert (H1 : cfg_eqv (mkCfg ms mo) (mkCfg ms' mo)) by (split; [exact Heqv| reflexivity]).
  pose proof (cfg_eqv_sym _ _ H1) as H2.
  split; [| split; [| split]]; [intros tr|..]; split; intros H.
  - exact (obs_trace_eqv _ _ tr H1 H).
  - exact (obs_trace_eqv _ _ tr H2 H).
  - exact (reaches_error_eqv _ _ H1 H).
  - exact (reaches_error_eqv _ _ H2 H).
  - exact (all_traces_error_eqv _ H _ H1).
  - exact (all_traces_error_eqv _ H _ H2).
  - exact (reaches_unmodeled_eqv _ _ H1 H).
  - exact (reaches_unmodeled_eqv _ _ H2 H).
Qed.

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
Definition mkR_init (sp : word) : bvmap 5 word :=
  mkR w0 sp w0 w0 w0 w0 w0 w0 w0 w0 w0 w0 w0 w0 w0 w0 w0 w0 w0 w0 w0 w0 w0 w0 w0 w0 w0 w0 w0 w0 w0.

Lemma init_regs_mkR : forall sp : word,
  regs_eqv (bvmap_set 2 sp (bvmap_set 10 (Z_to_bv 64 0) bvmap_empty)) (mkR_init sp).
Proof.
  intros sp r. destruct (reg_of_nat r) as (n & -> & Hn).
  do 32 (destruct n as [|n]; [vm_compute; reflexivity|]). lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition init_ms (segs : list Segment) (pc : N) (ph : PhdrInfo) (sp mbase : word)
    (draw : EntryDraw) (inp : ProcInput) : machine_state :=
  MS (mkR_init sp) bvmap_empty (Z_to_bv 64 (Z.of_N pc)) (Z_to_bv 32 0) None
     (wrap_mem inp mbase ph (Z_to_bv 64 (Z.of_N pc)) sp draw) (seg_rom segs).

Lemma init_machine_state_eqv : forall segs pc ph sp mbase draw inp,
  ms_eqv (init_machine_state segs pc ph sp mbase draw inp) (init_ms segs pc ph sp mbase draw inp).
Proof.
  intros. rewrite init_mkst. unfold mkst, init_ms, MS, regupd.
  split; [apply init_regs_mkR|]. repeat split; apply regs_eqv_refl.
Qed.

(* [comment removed for export] *)
Theorem init_behaviour_eqv : forall segs pc ph sp mbase draw inp mo,
  let c0 := mkCfg (init_machine_state segs pc ph sp mbase draw inp) mo in
  let c0' := mkCfg (init_ms segs pc ph sp mbase draw inp) mo in
  (forall tr, obs_trace segs c0 tr <-> obs_trace segs c0' tr) /\
  (reaches_error segs c0 <-> reaches_error segs c0') /\
  (all_traces_error segs c0 <-> all_traces_error segs c0') /\
  (reaches_unmodeled segs c0 <-> reaches_unmodeled segs c0').
Proof. intros. apply behaviour_eqv. apply init_machine_state_eqv. Qed.
