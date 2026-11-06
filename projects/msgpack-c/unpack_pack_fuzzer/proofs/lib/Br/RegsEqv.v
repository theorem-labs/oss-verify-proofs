(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib Require Import PropExec MState Frame.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require ShapeAlg.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Scfg Require Import Fcfg.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache.

Definition regs_eqv (R R' : bvmap 5 word) : Prop := forall r : reg, getr R r = getr R' r.
Definition fregs_eqv (F F' : bvmap 5 word) : Prop := forall r : reg, reg_get F r = reg_get F' r.

Lemma regs_eqv_refl : forall R, regs_eqv R R.                     Proof. intros R r; reflexivity. Qed.
Lemma regs_eqv_sym : forall R R', regs_eqv R R' -> regs_eqv R' R. Proof. intros R R' H r; symmetry; apply H. Qed.
Lemma regs_eqv_trans : forall R1 R2 R3, regs_eqv R1 R2 -> regs_eqv R2 R3 -> regs_eqv R1 R3.
Proof. intros R1 R2 R3 H1 H2 r. etransitivity; [apply H1 | apply H2]. Qed.
Lemma fregs_eqv_refl : forall F, fregs_eqv F F.                     Proof. intros F r; reflexivity. Qed.
Lemma fregs_eqv_sym : forall F F', fregs_eqv F F' -> fregs_eqv F' F. Proof. intros F F' H r; symmetry; apply H. Qed.
Lemma fregs_eqv_trans : forall F1 F2 F3, fregs_eqv F1 F2 -> fregs_eqv F2 F3 -> fregs_eqv F1 F3.
Proof. intros F1 F2 F3 H1 H2 r. etransitivity; [apply H1 | apply H2]. Qed.

Lemma reg_get_set : forall (R : bvmap 5 word) (k r : reg) v,
  reg_get (bvmap_set k v R) r = if bv_eqb k r then v else reg_get R r.
Proof.
  intros R k r v. destruct (bv_eqb k r) eqn:E.
  - apply bv_eqb_eq in E. subst. apply reg_get_set_same.
  - apply reg_get_set_other. intros ->. rewrite bv_eqb_refl in E. discriminate.
Qed.

Lemma getr_set : forall (R : bvmap 5 word) (k r : reg) v,
  getr (bvmap_set k v R) r = if bv_eqb r 0 then Z_to_bv 64 0 else if bv_eqb k r then v else getr R r.
Proof.
  intros R k r v. unfold getr. rewrite reg_get_set. destruct (bv_eqb r 0); reflexivity.
Qed.

Lemma regs_eqv_set : forall R R' (k : reg) v,
  regs_eqv R R' -> regs_eqv (bvmap_set k v R) (bvmap_set k v R').
Proof. intros R R' k v H r. rewrite !getr_set. destruct (bv_eqb r 0); [reflexivity|]. destruct (bv_eqb k r); [reflexivity | apply H]. Qed.

Lemma fregs_eqv_set : forall F F' (k : reg) v,
  fregs_eqv F F' -> fregs_eqv (bvmap_set k v F) (bvmap_set k v F').
Proof. intros F F' k v H r. rewrite !reg_get_set. destruct (bv_eqb k r); [reflexivity | apply H]. Qed.

Lemma rget_getr : forall R F pc fc rv r, rget (Core R F pc fc rv) r = getr R r.
Proof. reflexivity. Qed.

Lemma if_x0_eqv : forall R R', regs_eqv R R' -> forall r : reg,
  (if is_x0 r then w0 else reg_get R r) = (if is_x0 r then w0 else reg_get R' r).
Proof. intros R R' H r. exact (H r). Qed.

Lemma regs_eqv_reg_get : forall R R' (r : reg), regs_eqv R R' -> bv_eqb r 0 = false -> reg_get R r = reg_get R' r.
Proof. intros R R' r H Hr. specialize (H r). unfold getr in H. rewrite Hr in H. exact H. Qed.

Definition core_eqv (c c' : core) : Prop :=
  regs_eqv (c_regs c) (c_regs c') /\ fregs_eqv (c_fregs c) (c_fregs c') /\
  c_pc c = c_pc c' /\ c_fcsr c = c_fcsr c' /\ c_resv c = c_resv c'.

Inductive eff_eqv : eff -> eff -> Prop :=
| EqvDone : forall c c', core_eqv c c' -> eff_eqv (EDone c) (EDone c')
| EqvIllegal : forall c c', eff_eqv (EIllegal c) (EIllegal c')
| EqvDefinedIllegal : forall c c', eff_eqv (EDefinedIllegal c) (EDefinedIllegal c')
| EqvEcall : forall c c', eff_eqv (EEcall c) (EEcall c')
| EqvEbreak : forall c c', eff_eqv (EEbreak c) (EEbreak c')
| EqvFault : forall c c', eff_eqv (EFault c) (EFault c')
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
    | apply EqvIllegal | apply EqvDefinedIllegal | apply EqvEcall | apply EqvEbreak | apply EqvFault
    | apply EqvLoad; intros ?
    | apply EqvStore
    | match goal with |- eff_eqv (match ?X with _ => _ end) _ => destruct X end
    | match goal with |- eff_eqv (match ?X with _ => _ end _) _ => destruct X end ].

Local Ltac unfold_exec :=
  cbv beta iota zeta delta [exec rget fget fread c_regs c_fregs c_pc c_fcsr c_resv
                            with_pc load_val store_val exec_csr resolve_rm frm_of].

Lemma exec_eqv_core : forall R R' F F' pc fc rv sz i,
  regs_eqv R R' -> fregs_eqv F F' ->
  eff_eqv (exec sz i (Core R F pc fc rv)) (exec sz i (Core R' F' pc fc rv)).
Proof.
  intros R R' F F' pc fc rv sz i HR HF.
  destruct i; unfold_exec; rewrite ?(if_x0_eqv R R' HR), ?HF; eqv_struct HR HF.
Qed.

Lemma exec_eqv : forall sz i c c', core_eqv c c' -> eff_eqv (exec sz i c) (exec sz i c').
Proof.
  intros sz i [R F p f s] [R' F' p' f' s'] (HR & HF & Hp & Hf & Hs); simpl in *; subst.
  apply exec_eqv_core; assumption.
Qed.

Definition ms_eqv (ms ms' : machine_state) : Prop :=
  regs_eqv (ms_regs ms) (ms_regs ms') /\ fregs_eqv (ms_fregs ms) (ms_fregs ms') /\
  ms_pc_val ms = ms_pc_val ms' /\ ms_svc_pending ms = ms_svc_pending ms' /\
  ms_resv ms = ms_resv ms' /\ ms_fcsr ms = ms_fcsr ms' /\
  ms_mem ms = ms_mem ms' /\ ms_rom ms = ms_rom ms'.

Lemma ms_eqv_refl : forall ms, ms_eqv ms ms.
Proof. intros ms. split; [apply regs_eqv_refl|]. split; [apply fregs_eqv_refl|]. repeat split; reflexivity. Qed.
Lemma ms_eqv_sym : forall ms ms', ms_eqv ms ms' -> ms_eqv ms' ms.
Proof.
  intros ms ms' (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8).
  split; [apply regs_eqv_sym; exact H1|]. split; [apply fregs_eqv_sym; exact H2|]. repeat split; congruence.
Qed.
Lemma ms_eqv_trans : forall a b c, ms_eqv a b -> ms_eqv b c -> ms_eqv a c.
Proof.
  intros a b c (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8) (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8).
  split; [eapply regs_eqv_trans; eassumption|]. split; [eapply fregs_eqv_trans; eassumption|]. repeat split; congruence.
Qed.

Definition ares_eqv (r r' : machine_result (access_report machine_state)) : Prop :=
  match r, r' with
  | MachineOk a, MachineOk b => ms_eqv (@access_value _ a) (@access_value _ b) /\ @accessed_ranges _ a = @accessed_ranges _ b
  | MachineFault, MachineFault => True
  | MachineUnmodeled, MachineUnmodeled => True
  | _, _ => False
  end.

Definition res_eqv (r r' : machine_result machine_state) : Prop :=
  match r, r' with
  | MachineOk a, MachineOk b => ms_eqv a b
  | MachineFault, MachineFault => True
  | MachineUnmodeled, MachineUnmodeled => True
  | _, _ => False
  end.

Lemma ares_res_eqv : forall r r', ares_eqv r r' -> res_eqv (drop_access_report r) (drop_access_report r').
Proof. intros [a| |] [b| |] H; cbn in *; try exact H. exact (proj1 H). Qed.

Section WithSegs.
Variable segs : list Segment.

Lemma interp_eff_accesses_eqv : forall t t', eff_eqv t t' -> forall m,
  match interp_eff_accesses segs t m, interp_eff_accesses segs t' m with
  | MachineOk a, MachineOk b =>
      core_eqv (fst (@access_value _ a)) (fst (@access_value _ b)) /\ snd (@access_value _ a) = snd (@access_value _ b)
      /\ @accessed_ranges _ a = @accessed_ranges _ b
  | MachineFault, MachineFault => True
  | MachineUnmodeled, MachineUnmodeled => True
  | _, _ => False
  end.
Proof.
  intros t t' H. induction H; intros m; cbn [interp_eff_accesses fst snd access_value accessed_ranges]; auto.
  - destruct (ov_read_bytes segs m a (width_bytes n)) as [bs|]; [|exact I].
    specialize (H0 (bv_extract 0 n (le_bytes_to_word bs)) m).
    destruct (interp_eff_accesses segs (k _) m) as [[[c1 m1] l1]| |];
    destruct (interp_eff_accesses segs (k' _) m) as [[[c1' m1'] l1']| |]; cbn in *; try exact H0; try contradiction.
    destruct H0 as (Hc & Hm & ->). split; [exact Hc|]. split; [exact Hm|reflexivity].
  - destruct (store_ok segs m a (width_bytes n)); [|exact I].
    specialize (IHeff_eqv (write_to_mem m a (Z_to_le_bytes (width_bytes n) (bv_unsigned v)))).
    destruct (interp_eff_accesses segs k _) as [[[c1 m1] l1]| |];
    destruct (interp_eff_accesses segs k' _) as [[[c1' m1'] l1']| |]; cbn in *; try exact IHeff_eqv; try contradiction.
    destruct IHeff_eqv as (Hc & Hm & ->). split; [exact Hc|]. split; [exact Hm|reflexivity].
Qed.

Lemma ms_reg_eqv : forall ms ms' r, ms_eqv ms ms' -> ms_reg ms r = ms_reg ms' r.
Proof. intros ms ms' r (HR & _). exact (HR r). Qed.

Lemma decode_exec_accesses_eqv : forall ms ms' w, ms_eqv ms ms' ->
  ares_eqv (decode_exec_accesses segs ms w) (decode_exec_accesses segs ms' w).
Proof.
  intros ms ms' w Heqv. pose proof (ms_reg_eqv ms ms' 17 Heqv) as H17.
  destruct ms as [R F pc svc rv fc m ro], ms' as [R' F' pc' svc' rv' fc' m' ro'].
  destruct Heqv as (HR & HF & Hpc & Hsvc & Hrv & Hfc & Hm & Hro); simpl in *; subst.
  unfold decode_exec_accesses. destruct (is_ecall w).
  - cbn. rewrite H17. split; [|reflexivity]. repeat split; assumption.
  - destruct (decode_any w) as [[i isz]|]; [| destruct (is_defined_illegal w); exact I]. cbn [ms_regs ms_fregs ms_pc_val ms_fcsr ms_resv ms_mem ms_rom].
    pose proof (interp_eff_accesses_eqv _ _ (exec_eqv_core R R' F F' pc' fc' rv' (Z_to_bv 64 isz) i HR HF) m') as K.
    destruct (interp_eff_accesses segs (exec _ i (Core R F pc' fc' rv')) m') as [[[c m1] l]| |];
    destruct (interp_eff_accesses segs (exec _ i (Core R' F' pc' fc' rv')) m') as [[[c' m1'] l']| |];
    cbn in *; try exact K; try contradiction.
    destruct K as ((H1 & H2 & H3 & H4 & H5) & -> & ->). split; [|reflexivity]. repeat split; cbn; auto.
Qed.

Lemma step_accesses_eqv : forall ms ms', ms_eqv ms ms' ->
  ares_eqv (RiscvSemantics.step_accesses segs ms) (RiscvSemantics.step_accesses segs ms').
Proof.
  intros ms ms' Heqv. pose proof Heqv as (_ & _ & Hpc & _ & _ & _ & Hm & _).
  unfold RiscvSemantics.step_accesses, ms_pc. rewrite <- Hpc, <- Hm.
  destruct (fetch_word segs (ms_pc_val ms)); [apply decode_exec_accesses_eqv; exact Heqv|].
  destruct (fetch_word_ov segs (ms_mem ms) (ms_pc_val ms)); [apply decode_exec_accesses_eqv; exact Heqv|].
  destruct (fetch_tail_any segs (ms_mem ms) (ms_pc_val ms)); [apply decode_exec_accesses_eqv; exact Heqv|].
  unfold fetch_failure. destruct (negb _); [exact I|]. destruct (_ || _)%bool; exact I.
Qed.

Lemma step_eqv : forall ms ms', ms_eqv ms ms' ->
  res_eqv (RiscvSemantics.step segs ms) (RiscvSemantics.step segs ms').
Proof. intros ms ms' H. unfold RiscvSemantics.step. apply ares_res_eqv, step_accesses_eqv, H. Qed.

Lemma syscall_args_eqv : forall ms ms', ms_eqv ms ms' -> syscall_args ms = syscall_args ms'.
Proof.
  intros ms ms' (HR & _). unfold syscall_args, ms_gpr. cbn [Z.of_nat Z.add Pos.of_succ_nat Pos.add Pos.succ].
  rewrite !(regs_eqv_reg_get _ _ _ HR) by reflexivity. reflexivity.
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
  unfold apply_effect, set_reg; simpl. split; [apply regs_eqv_set; exact HR|]. repeat split; auto.
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

Lemma cfg_eqv_refl : forall c, cfg_eqv c c.
Proof. intros c. split; [apply ms_eqv_refl | reflexivity]. Qed.
Lemma cfg_eqv_sym : forall c c', cfg_eqv c c' -> cfg_eqv c' c.
Proof. intros c c' [H1 H2]. split; [apply ms_eqv_sym; exact H1 | congruence]. Qed.

Definition to_eqv (X X' : step_to) : Prop :=
  match X, X' with
  | SError, SError => True
  | SNext c, SNext c' => cfg_eqv c c'
  | _, _ => False
  end.

Lemma mi_account_step_eqv : forall ms ms' mo, ms_eqv ms ms' ->
  match mi_account_step segs ms mo, mi_account_step segs ms' mo with
  | MachineOk (a, moa), MachineOk (b, mob) => ms_eqv a b /\ moa = mob
  | MachineFault, MachineFault => True
  | MachineUnmodeled, MachineUnmodeled => True
  | _, _ => False
  end.
Proof.
  intros ms ms' mo Heqv. pose proof (step_accesses_eqv ms ms' Heqv) as H.
  unfold mi_account_step.
  destruct (RiscvSemantics.step_accesses segs ms) as [[a la]| |];
  destruct (RiscvSemantics.step_accesses segs ms') as [[b lb]| |]; cbn in H |- *; try exact H; try contradiction.
  destruct H as [Hab <-]. destruct (materialize_model_accesses mo la); [split; [exact Hab | reflexivity] | exact I].
Qed.

Lemma sstep_eqv : forall ms ms' mo evs X, ms_eqv ms ms' ->
  sstep_cfg segs fcfg (mkCfg ms mo) evs X ->
  exists X', sstep_cfg segs fcfg (mkCfg ms' mo) evs X' /\ to_eqv X X'.
Proof.
  intros ms ms' mo evs X Heqv Hst.
  pose proof (mi_account_step_eqv ms ms' mo Heqv) as Hacc.
  pose proof Heqv as (_ & _ & _ & Hsvc & _ & _ & _ & _).
  inversion Hst; subst.
  -
    match goal with Hm : mi_account_step segs ms mo = _ |- _ => rewrite Hm in Hacc end.
    destruct (mi_account_step segs ms' mo) as [[ms1' mo1']| |] eqn:E; cbn in Hacc; try contradiction.
    destruct Hacc as [Hms <-].
    exists (SNext (mkCfg ms1' model')). split; [apply sstep_cfg_instr; auto; congruence|]. split; [exact Hms | reflexivity].
  - match goal with Hm : mi_account_step segs ms mo = _ |- _ => rewrite Hm in Hacc end.
    destruct (mi_account_step segs ms' mo) as [[ms1' mo1']| |] eqn:E; cbn in Hacc; try contradiction.
    exists SError. split; [apply sstep_cfg_instr_fault; auto; congruence | exact I].
  - match goal with Hm : mi_account_step segs ms mo = _ |- _ => rewrite Hm in Hacc end.
    destruct (mi_account_step segs ms' mo) as [[ms1' mo1']| |] eqn:E; cbn in Hacc; try contradiction.
    exists SError. split; [apply sstep_cfg_instr_unmodeled; auto; congruence | exact I].
  -
    exists (SNext (mkCfg (advance_past_svc (apply_effect ms' eff)) model'')). split.
    + apply (sstep_cfg_syscall segs fcfg ms' mo x8 eff model' model'' evs);
        [assumption | congruence | rewrite <- (sys_input_eqv ms ms' x8 Heqv); assumption
        | rewrite <- (sys_input_eqv ms ms' x8 Heqv); assumption | assumption | assumption].
    + split; [| reflexivity]. apply advance_past_svc_eqv, apply_effect_eqv, Heqv.
  -
    exists SError. split; [| exact I].
    apply (sstep_cfg_syscall_materialization_fault segs fcfg ms' mo x8 eff model' evs0);
      [assumption | congruence | rewrite <- (sys_input_eqv ms ms' x8 Heqv); assumption
      | rewrite <- (sys_input_eqv ms ms' x8 Heqv); assumption | assumption | assumption].
  -
    exists (SNext (mkCfg ms' model')). split.
    + apply (sstep_cfg_exit segs fcfg ms' mo x8 eff model' evs0 code);
        [assumption | congruence | rewrite <- (sys_input_eqv ms ms' x8 Heqv); assumption | assumption | assumption].
    + split; [exact Heqv | reflexivity].
  -
    exists (SNext (mkCfg ms' model')). split.
    + apply (sstep_cfg_killed segs fcfg ms' mo x8 eff model' evs0 sig);
        [assumption | congruence | rewrite <- (sys_input_eqv ms ms' x8 Heqv); assumption | assumption].
    + split; [exact Heqv | reflexivity].
  - exists SError. split; [| exact I].
    apply (sstep_cfg_syscall_unmodeled segs fcfg ms' mo x8);
      [assumption | congruence | rewrite <- (sys_input_eqv ms ms' x8 Heqv); assumption].
Qed.

Lemma sstep_cfg_eqv : forall c c' evs X, cfg_eqv c c' ->
  sstep_cfg segs fcfg c evs X -> exists X', sstep_cfg segs fcfg c' evs X' /\ to_eqv X X'.
Proof.
  intros [ms mo] [ms' mo'] evs X [Hms Hmo] Hst; simpl in Hms, Hmo; subst.
  apply (sstep_eqv ms ms'); assumption.
Qed.

Theorem realizes_cfg_eqv : forall c T, ShapeAlg.realizes segs c T ->
  forall c', cfg_eqv c c' -> ShapeAlg.realizes segs c' T.
Proof.
  intros c T H. induction H as [c I evs nx T i0 [Hok1 Hok2] Hcont IH | c Hh | c T T' H IH Heq]; intros c' Heqv.
  -
    pose (I' := { x : I * config | sstep_cfg segs fcfg c' (evs (fst x)) (SNext (snd x)) /\ cfg_eqv (nx (fst x)) (snd x) }).
    assert (Hx0 : exists c0', sstep_cfg segs fcfg c' (evs i0) (SNext c0') /\ cfg_eqv (nx i0) c0').
    { destruct (sstep_cfg_eqv c c' (evs i0) (SNext (nx i0)) Heqv (Hok1 i0)) as (X' & Hs' & HX).
      destruct X' as [c0'|]; cbn in HX; [| contradiction]. exists c0'. split; assumption. }
    destruct Hx0 as (c0' & Hs0 & He0).
    apply (ShapeAlg.rz_conseq segs c' (ShapeAlg.t_alt (fun x : I' => ShapeAlg.t_emit (evs (fst (proj1_sig x))) (T (fst (proj1_sig x)))))).
    + apply (ShapeAlg.rz_node segs c' I' (fun x => evs (fst (proj1_sig x))) (fun x => snd (proj1_sig x))
               (fun x => T (fst (proj1_sig x))) (exist _ (i0, c0') (conj Hs0 He0))).
      * split.
        -- intros [[i ci] [Hs He]]; cbn. exact Hs.
        -- intros e st Hst'.
           destruct (sstep_cfg_eqv c' c e st (cfg_eqv_sym _ _ Heqv) Hst') as (X & Hs & HX).
           destruct (Hok2 e X Hs) as (i & -> & ->).
           destruct st as [ci|]; cbn in HX; [| contradiction].
           exists (exist _ (i, ci) (conj Hst' (cfg_eqv_sym _ _ HX))). cbn. split; reflexivity.
      * intros [[i ci] [Hs He]]; cbn. apply (IH i). exact He.
    + intros tr. split.
      * intros [[[i ci] [Hs He]] Htr]; cbn in Htr. exists i. exact Htr.
      * intros [i Htr].
        destruct (sstep_cfg_eqv c c' (evs i) (SNext (nx i)) Heqv (Hok1 i)) as (X' & Hs' & HX).
        destruct X' as [ci|]; cbn in HX; [| contradiction].
        exists (exist _ (i, ci) (conj Hs' HX)). cbn. exact Htr.
  - apply ShapeAlg.rz_halt. destruct Heqv as [_ <-]. exact Hh.
  - eapply ShapeAlg.rz_conseq; [apply IH; exact Heqv | exact Heq].
Qed.

Theorem realizes_eqv : forall ms ms' mo T, ms_eqv ms ms' ->
  ShapeAlg.realizes segs (mkCfg ms mo) T -> ShapeAlg.realizes segs (mkCfg ms' mo) T.
Proof.
  intros ms ms' mo T Heqv H. apply (realizes_cfg_eqv _ T H). split; [exact Heqv | reflexivity].
Qed.

End WithSegs.

Lemma reg_of_nat : forall r : reg, exists n, r = Z_to_bv 5 (Z.of_nat n) /\ (n < 32)%nat.
Proof.
  intros r. exists (Z.to_nat (bv_unsigned r)). pose proof (bv_unsigned_in_range 5 r) as Hr.
  unfold bv_modulus in Hr. simpl in Hr. split; [|lia].
  rewrite Z2Nat.id by lia. apply bv_eq. rewrite Z_to_bv_unsigned. symmetry.
  apply bv_wrap_small. unfold bv_modulus. simpl. lia.
Qed.

Definition mkR_of (R : bvmap 5 word) : bvmap 5 word :=
  mkR (getr R 1) (getr R 2) (getr R 3) (getr R 4) (getr R 5) (getr R 6) (getr R 7) (getr R 8)
      (getr R 9) (getr R 10) (getr R 11) (getr R 12) (getr R 13) (getr R 14) (getr R 15) (getr R 16)
      (getr R 17) (getr R 18) (getr R 19) (getr R 20) (getr R 21) (getr R 22) (getr R 23) (getr R 24)
      (getr R 25) (getr R 26) (getr R 27) (getr R 28) (getr R 29) (getr R 30) (getr R 31).

Lemma mkR_of_eqv : forall R, regs_eqv R (mkR_of R).
Proof.
  intros R r. destruct (reg_of_nat r) as (n & -> & Hn).
  do 32 (destruct n as [|n]; [reflexivity|]). lia.
Qed.

Lemma MS_mkR_of_eqv : forall R F pc fc rv m ro,
  ms_eqv (MS (mkR_of R) F pc fc rv m ro) (MS R F pc fc rv m ro).
Proof.
  intros. split; [apply regs_eqv_sym, mkR_of_eqv|]. split; [apply fregs_eqv_refl|]. repeat split; reflexivity.
Qed.

Corollary realizes_to_mkR : forall segs R F pc fc m ro mo T,
  ShapeAlg.realizes segs (mkCfg (MS (mkR_of R) F pc fc None m ro) mo) T ->
  ShapeAlg.realizes segs (mkCfg (MS R F pc fc None m ro) mo) T.
Proof. intros segs R F pc fc m ro mo T H. eapply realizes_eqv; [apply MS_mkR_of_eqv | exact H]. Qed.

Corollary realizes_of_mkR : forall segs R F pc fc m ro mo T,
  ShapeAlg.realizes segs (mkCfg (MS R F pc fc None m ro) mo) T ->
  ShapeAlg.realizes segs (mkCfg (MS (mkR_of R) F pc fc None m ro) mo) T.
Proof. intros segs R F pc fc m ro mo T H. eapply realizes_eqv; [apply ms_eqv_sym, MS_mkR_of_eqv | exact H]. Qed.
