(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From Stdlib Require ZArith.
From Stdlib Require NArith.
From Stdlib Require List.
From Stdlib Require Lia.
From Stdlib Require Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase.
From LinuxProcessSemantics.LinuxProcessSem Require RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem Require MemImageType.
From LinuxProcessSemantics.LinuxProcessSem Require StackLayout.
From LinuxProcessSemantics.LinuxProcessSem Require Fs.
From LinuxProcessSemantics.LinuxProcessSem Require State.
From LinuxProcessSemantics.LinuxProcessSem Require Monad.
From LinuxProcessSemantics.LinuxProcessSem Require Specs.
From LinuxProcessSemantics.LinuxProcessSem Require Run.
From LinuxProcessSemantics.Riscv Require Prelude.
From LinuxProcessSemantics.Riscv Require Instr.
From LinuxProcessSemantics.Riscv Require Decode.
From LinuxProcessSemantics.Riscv Require DecodeC.
From LinuxProcessSemantics.Riscv Require Sem.
From LinuxProcessSemantics.Riscv Require Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require PropExec.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require MState.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require RegsEquiv.
Module RegsEqv0.
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.PropExec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.MState.
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
(* [comment removed for export] *)
Definition regs_eqv0 (R R' : bvmap 5 word) : Prop :=
  forall r, is_x0 r = false -> reg_get R r = reg_get R' r.

Lemma regs_eqv0_refl : forall R, regs_eqv0 R R.
Proof. intros R r _. reflexivity. Qed.
Lemma regs_eqv0_sym : forall R R', regs_eqv0 R R' -> regs_eqv0 R' R.
Proof. intros R R' H r Hr. symmetry. apply H. exact Hr. Qed.
Lemma regs_eqv0_trans : forall R1 R2 R3, regs_eqv0 R1 R2 -> regs_eqv0 R2 R3 -> regs_eqv0 R1 R3.
Proof. intros R1 R2 R3 H1 H2 r Hr. etransitivity; [apply H1|apply H2]; exact Hr. Qed.
Lemma regs_eqv_eqv0 : forall R R', regs_eqv R R' -> regs_eqv0 R R'.
Proof. intros R R' H r _. apply H. Qed.
Lemma regs_eqv0_set : forall R R' (k : reg) v,
  regs_eqv0 R R' -> regs_eqv0 (bvmap_set k v R) (bvmap_set k v R').
Proof. intros R R' k v H r Hr. rewrite !reg_get_set. destruct (bv_eqb k r); [reflexivity|apply H; exact Hr]. Qed.

(* [comment removed for export] *)
Lemma regs_eqv0_rget : forall R R', regs_eqv0 R R' ->
  forall r, (if is_x0 r then w0 else reg_get R r) = (if is_x0 r then w0 else reg_get R' r).
Proof. intros R R' H r. destruct (is_x0 r) eqn:E; [reflexivity | apply H; exact E]. Qed.

Definition core_eqv (c c' : core) : Prop :=
  regs_eqv0 (c_regs c) (c_regs c') /\ regs_eqv (c_fregs c) (c_fregs c') /\
  c_pc c = c_pc c' /\ c_fcsr c = c_fcsr c' /\ c_resv c = c_resv c'.

(* [comment removed for export] *)
Inductive eff_eqv : eff -> eff -> Prop :=
| EqvDone : forall c c', core_eqv c c' -> eff_eqv (EDone c) (EDone c')
| EqvIllegal : forall c c', eff_eqv (EIllegal c) (EIllegal c')
| EqvEcall : forall c c', eff_eqv (EEcall c) (EEcall c')
| EqvEbreak : forall c c', eff_eqv (EEbreak c) (EEbreak c')
| EqvFault : forall c c', eff_eqv (EFault c) (EFault c')
| EqvDefIllegal : forall c c', eff_eqv (EDefinedIllegal c) (EDefinedIllegal c')
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
  intros r v [R F p f s] [R' F' p' f' s'] H. core_tac. destruct H as (HR & HF & -> & -> & ->).
  destruct (is_x0 r); simpl; repeat split; auto using regs_eqv0_set.
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
  regs_eqv0 R R' -> regs_eqv F F' ->
  eff_eqv (exec sz i (Core R F pc fc rv)) (exec sz i (Core R' F' pc fc rv)).
Proof.
  intros R R' F F' pc fc rv sz i HR HF. pose proof (regs_eqv0_rget R R' HR) as HRg.
  destruct i; unfold_exec; rewrite ?HRg, ?HF; eqv_struct HR HF.
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
  regs_eqv0 (ms_regs ms) (ms_regs ms') /\ regs_eqv (ms_fregs ms) (ms_fregs ms') /\
  ms_pc_val ms = ms_pc_val ms' /\ ms_svc_pending ms = ms_svc_pending ms' /\
  ms_resv ms = ms_resv ms' /\ ms_fcsr ms = ms_fcsr ms' /\
  ms_mem ms = ms_mem ms' /\ ms_rom ms = ms_rom ms'.

Lemma ms_eqv_refl : forall ms, ms_eqv ms ms.
Proof. intros ms. split; [apply regs_eqv0_refl|]. repeat split; apply regs_eqv_refl. Qed.
Lemma ms_eqv_sym : forall ms ms', ms_eqv ms ms' -> ms_eqv ms' ms.
Proof.
  intros ms ms' (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8).
  repeat split; auto using regs_eqv_sym, regs_eqv0_sym; congruence.
Qed.
Lemma ms_eqv_trans : forall a b c, ms_eqv a b -> ms_eqv b c -> ms_eqv a c.
Proof.
  intros a b c (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8) (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8).
  repeat split; eauto using regs_eqv_trans, regs_eqv0_trans; congruence.
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
  | MachineOk r, MachineOk r' =>
      core_eqv (fst (access_value _ r)) (fst (access_value _ r')) /\
      snd (access_value _ r) = snd (access_value _ r') /\
      accessed_ranges _ r = accessed_ranges _ r'
  | MachineFault, MachineFault => True
  | MachineUnmodeled, MachineUnmodeled => True
  | _, _ => False
  end.
Proof.
  intros t t' H. induction H; intros m; cbn [interp_eff_accesses]; auto.
  - destruct (ov_read_bytes segs m a (width_bytes n)) as [bs|]; [| exact I].
    specialize (H0 (bv_extract 0 n (le_bytes_to_word bs)) m).
    destruct (interp_eff_accesses segs (k _) m) as [r| |];
    destruct (interp_eff_accesses segs (k' _) m) as [r'| |]; cbn; try exact H0.
    destruct H0 as (H1 & H2 & H3). rewrite H3. auto.
  - destruct (store_ok segs m a (width_bytes n)); [| exact I].
    specialize (IHeff_eqv (write_to_mem m a (Z_to_le_bytes (width_bytes n) (bv_unsigned v)))).
    destruct (interp_eff_accesses segs k _) as [r| |];
    destruct (interp_eff_accesses segs k' _) as [r'| |]; cbn; try exact IHeff_eqv.
    destruct IHeff_eqv as (H1 & H2 & H3). rewrite H3. auto.
Qed.

Lemma interp_eff_eqv : forall t t', eff_eqv t t' -> forall m,
  match interp_eff segs t m, interp_eff segs t' m with
  | MachineOk (c, m1), MachineOk (c', m1') => core_eqv c c' /\ m1 = m1'
  | MachineFault, MachineFault => True
  | MachineUnmodeled, MachineUnmodeled => True
  | _, _ => False
  end.
Proof.
  intros t t' H m. pose proof (interp_eff_accesses_eqv t t' H m) as K.
  unfold interp_eff, RiscvSemantics.drop_access_report.
  destruct (interp_eff_accesses segs t m) as [[[c m1] acc]| |];
  destruct (interp_eff_accesses segs t' m) as [[[c' m1'] acc']| |]; cbn in *; try exact K.
  destruct K as (H1 & H2 & H3). auto.
Qed.

Lemma ms_reg_eqv : forall ms ms' r, ms_eqv ms ms' -> ms_reg ms r = ms_reg ms' r.
Proof.
  intros ms ms' r (HR & _). unfold ms_reg. rewrite bv_eqb0_is_x0.
  destruct (is_x0 r) eqn:E; [reflexivity|]. apply HR. exact E.
Qed.

(* [comment removed for export] *)
Definition ares_eqv (r r' : machine_result (access_report machine_state)) : Prop :=
  match r, r' with
  | MachineOk a, MachineOk b => ms_eqv (access_value _ a) (access_value _ b) /\
                                accessed_ranges _ a = accessed_ranges _ b
  | MachineFault, MachineFault => True
  | MachineUnmodeled, MachineUnmodeled => True
  | _, _ => False
  end.

Lemma ares_eqv_drop : forall r r', ares_eqv r r' ->
  res_eqv (RiscvSemantics.drop_access_report r) (RiscvSemantics.drop_access_report r').
Proof. intros [a| |] [b| |] H; cbn in *; try exact H. exact (proj1 H). Qed.

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
    destruct (interp_eff_accesses segs (exec _ i (Core R F pc' fc' rv')) m') as [[[c m1] acc]| |];
    destruct (interp_eff_accesses segs (exec _ i (Core R' F' pc' fc' rv')) m') as [[[c' m1'] acc']| |];
    simpl in *; try exact K; try contradiction.
    destruct K as ((H1 & H2 & H3 & H4 & H5) & -> & ->). repeat split; simpl; auto.
Qed.

Lemma decode_exec_eqv : forall ms ms' w, ms_eqv ms ms' ->
  res_eqv (decode_exec segs ms w) (decode_exec segs ms' w).
Proof. intros. unfold decode_exec. apply ares_eqv_drop, decode_exec_accesses_eqv. assumption. Qed.

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
Proof. intros. unfold RiscvSemantics.step. apply ares_eqv_drop, step_accesses_eqv. assumption. Qed.

(* [comment removed for export] *)
Lemma mi_account_step_eqv : forall ms ms' mo, ms_eqv ms ms' ->
  match mi_account_step segs ms mo, mi_account_step segs ms' mo with
  | MachineOk (ms1, mo1), MachineOk (ms1', mo1') => ms_eqv ms1 ms1' /\ mo1 = mo1'
  | MachineFault, MachineFault => True
  | MachineUnmodeled, MachineUnmodeled => True
  | _, _ => False
  end.
Proof.
  intros ms ms' mo Heqv. pose proof (step_accesses_eqv ms ms' Heqv) as K.
  unfold mi_account_step.
  destruct (RiscvSemantics.step_accesses segs ms) as [a| |];
  destruct (RiscvSemantics.step_accesses segs ms') as [b| |]; cbn in K; try exact K; try contradiction.
  destruct K as [Hab <-].
  destruct (materialize_model_accesses mo (accessed_ranges _ a)) as [mo1|]; [|exact I].
  split; [exact Hab| reflexivity].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma syscall_args_eqv : forall ms ms', ms_eqv ms ms' -> syscall_args ms = syscall_args ms'.
Proof.
  intros ms ms' (HR & _). unfold syscall_args, ms_gpr.
  rewrite !(HR (Z_to_bv 5 (10 + Z.of_nat 0))), !(HR (Z_to_bv 5 (10 + Z.of_nat 1))), !(HR (Z_to_bv 5 (10 + Z.of_nat 2))),
          !(HR (Z_to_bv 5 (10 + Z.of_nat 3))), !(HR (Z_to_bv 5 (10 + Z.of_nat 4))), !(HR (Z_to_bv 5 (10 + Z.of_nat 5)))
    by reflexivity.
  reflexivity.
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
  unfold apply_effect, set_reg; simpl. repeat split; simpl; auto using regs_eqv0_set.
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

End WithSegs.

(* [comment removed for export] *)


Lemma ms_eqv_of_full : forall ms ms',
  OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.RegsEquiv.ms_eqv ms ms' -> ms_eqv ms ms'.
Proof.
  intros ms ms' (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8).
  split; [apply regs_eqv_eqv0; exact H1|]. repeat split; assumption.
Qed.
End RegsEqv0.

(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import MState.
Import RegsEqv0.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require PropExec.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require PropExec.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Cfg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope bv_scope.

Section WithSegs.
Variable segs : list Segment.

(* [comment removed for export] *)
Definition xfer (ms' : machine_state) (mo : Model) (n : config) : config :=
  match ms_svc_pending ms' with
  | None =>
      match mi_account_step segs ms' mo with
      | MachineOk (a, b) => mkCfg a b
      | _ => n
      end
  | Some _ =>
      match ms_svc_pending (cfg_ms n) with
      | Some _ => mkCfg ms' (cfg_model n)
      | None =>
          mkCfg {| ms_regs := bvmap_set 10 (reg_get (ms_regs (cfg_ms n)) 10) (ms_regs ms');
                   ms_fregs := ms_fregs ms';
                   ms_pc_val := ms_pc_val (cfg_ms n);
                   ms_svc_pending := ms_svc_pending (cfg_ms n);
                   ms_resv := ms_resv (cfg_ms n);
                   ms_fcsr := ms_fcsr (cfg_ms n);
                   ms_mem := ms_mem (cfg_ms n);
                   ms_rom := ms_rom (cfg_ms n) |}
                (cfg_model n)
      end
  end.

(* [comment removed for export] *)
Lemma xfer_syscall : forall ms ms' mo eff mo'' x8,
  ms_eqv ms ms' -> ms_svc_pending ms = Some x8 ->
  xfer ms' mo (mkCfg (advance_past_svc (apply_effect ms eff)) mo'')
  = mkCfg (advance_past_svc (apply_effect ms' eff)) mo''
  /\ cfg_eqv (mkCfg (advance_past_svc (apply_effect ms eff)) mo'')
             (mkCfg (advance_past_svc (apply_effect ms' eff)) mo'').
Proof.
  intros [R F pc svc rv fc m ro] [R' F' pc' svc' rv' fc' m' ro'] mo eff mo'' x8
         (HR & HF & Hpc & Hsvc & Hrv & Hfc & Hm & Hro) Hx8; simpl in *; subst.
  unfold xfer, advance_past_svc, apply_effect, set_reg, ms_pc; simpl.
  rewrite reg_get_set_same. split; [reflexivity|].
  split; [|reflexivity]. simpl. repeat split; simpl; auto using regs_eqv0_set.
Qed.

Lemma xfer_exit : forall ms ms' mo mo' x8,
  ms_eqv ms ms' -> ms_svc_pending ms = Some x8 ->
  xfer ms' mo (mkCfg ms mo') = mkCfg ms' mo'
  /\ cfg_eqv (mkCfg ms mo') (mkCfg ms' mo').
Proof.
  intros ms ms' mo mo' x8 Heqv Hx8.
  pose proof Heqv as (_ & _ & _ & Hsvc & _).
  unfold xfer. rewrite <- Hsvc, Hx8. simpl. rewrite Hx8.
  split; [reflexivity|]. split; [exact Heqv|reflexivity].
Qed.

Lemma xfer_instr : forall ms ms' mo ms1 mo1,
  ms_eqv ms ms' -> ms_svc_pending ms = None ->
  mi_account_step segs ms mo = MachineOk (ms1, mo1) ->
  exists ms1', mi_account_step segs ms' mo = MachineOk (ms1', mo1)
    /\ ms_eqv ms1 ms1'
    /\ forall n, xfer ms' mo n = mkCfg ms1' mo1.
Proof.
  intros ms ms' mo ms1 mo1 Heqv Hsvc Hstep.
  pose proof (mi_account_step_eqv segs ms ms' mo Heqv) as K. rewrite Hstep in K.
  destruct (mi_account_step segs ms' mo) as [[ms1' mo1']| |] eqn:E; try contradiction.
  destruct K as [Hms <-]. exists ms1'. split; [reflexivity|]. split; [exact Hms|].
  intros n. pose proof Heqv as (_ & _ & _ & Hsvc' & _).
  unfold xfer. rewrite <- Hsvc', Hsvc, E. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma sstep_xfer : forall ms ms' mo evs n,
  ms_eqv ms ms' ->
  sstep_cfg segs ACFG (mkCfg ms mo) evs (SNext n) ->
  sstep_cfg segs ACFG (mkCfg ms' mo) evs (SNext (xfer ms' mo n)) /\ cfg_eqv n (xfer ms' mo n).
Proof.
  intros ms ms' mo evs n Heqv Hst.
  pose proof Heqv as (_ & _ & _ & Hsvc & _).
  inversion Hst; subst.
  - (* [comment removed for export] *)
    lazymatch goal with
    | Hacc : mi_account_step _ _ _ = MachineOk (?ms1, ?mo1), Hsv : ms_svc_pending ms = None |- _ =>
      destruct (xfer_instr ms ms' mo ms1 mo1 Heqv Hsv Hacc) as (ms1' & E & Hms & Hx);
      rewrite Hx; split;
      [ apply sstep_cfg_instr; [assumption | congruence | exact E]
      | split; [exact Hms | reflexivity] ]
    end.
  - (* [comment removed for export] *)
    lazymatch goal with
    | Hsp : syscall_spec (sys_input _ ms ?x8) mo (Ok ?eff ?mo' ?evs0), Hsv : ms_svc_pending ms = Some _,
      Hmat : materialize_model_accesses _ _ = Some ?mo'' |- _ =>
      destruct (xfer_syscall ms ms' mo eff mo'' x8 Heqv Hsv) as [-> Hc];
      split; [|exact Hc];
      apply (sstep_cfg_syscall segs ACFG ms' mo x8 eff mo' mo'' evs0);
      [assumption | congruence | rewrite <- (sys_input_eqv segs ms ms' x8 Heqv); assumption
      | rewrite <- (sys_input_eqv segs ms ms' x8 Heqv); assumption | assumption | assumption]
    end.
  - (* [comment removed for export] *)
    lazymatch goal with
    | Hsp : syscall_spec (sys_input _ ms ?x8) mo (Ok ?eff ?mo' ?evs0), Hsv : ms_svc_pending ms = Some _,
      Hh : m_halted _ = Some ?code |- _ =>
      destruct (xfer_exit ms ms' mo mo' x8 Heqv Hsv) as [-> Hc];
      split; [|exact Hc];
      apply (sstep_cfg_exit segs ACFG ms' mo x8 eff mo' evs0 code);
      [assumption | congruence | rewrite <- (sys_input_eqv segs ms ms' x8 Heqv); assumption | assumption
      | assumption]
    end.
  - (* [comment removed for export] *)
    lazymatch goal with
    | Hsp : syscall_spec (sys_input _ ms ?x8) mo (Ok ?eff ?mo' ?evs0), Hsv : ms_svc_pending ms = Some _,
      Hk : m_killed _ = Some ?sig |- _ =>
      destruct (xfer_exit ms ms' mo mo' x8 Heqv Hsv) as [-> Hc];
      split; [|exact Hc];
      apply (sstep_cfg_killed segs ACFG ms' mo x8 eff mo' evs0 sig);
      [assumption | congruence | rewrite <- (sys_input_eqv segs ms ms' x8 Heqv); assumption | assumption]
    end.
Qed.

(* [comment removed for export] *)
Lemma sstep_xfer_back : forall ms ms' mo evs st',
  ms_eqv ms ms' ->
  sstep_cfg segs ACFG (mkCfg ms' mo) evs st' ->
  match st' with
  | SNext n' => exists n, sstep_cfg segs ACFG (mkCfg ms mo) evs (SNext n) /\ n' = xfer ms' mo n
  | SError => sstep_cfg segs ACFG (mkCfg ms mo) evs SError
  end.
Proof.
  intros ms ms' mo evs st' Heqv Hst'.
  pose proof (ms_eqv_sym _ _ Heqv) as Heqv'.
  pose proof Heqv as (_ & _ & _ & Hsvc & _).
  inversion Hst'; subst.
  - (* [comment removed for export] *)
    lazymatch goal with
    | Hacc : mi_account_step _ ms' _ = MachineOk (?ms1', ?mo1), Hsv : ms_svc_pending ms' = None |- _ =>
      pose proof (mi_account_step_eqv segs ms' ms mo Heqv') as K; rewrite Hacc in K;
      destruct (mi_account_step segs ms mo) as [[ms1 mo1x]| |] eqn:E; try contradiction;
      destruct K as [Hms <-];
      exists (mkCfg ms1 mo1); split;
      [ apply sstep_cfg_instr; [assumption | congruence | exact E]
      | unfold xfer; rewrite Hsv, Hacc; reflexivity ]
    end.
  - (* [comment removed for export] *)
    lazymatch goal with
    | Hacc : mi_account_step _ ms' _ = MachineFault |- _ =>
      pose proof (mi_account_step_eqv segs ms' ms mo Heqv') as K; rewrite Hacc in K;
      destruct (mi_account_step segs ms mo) as [[ms1 mo1]| |] eqn:E; try contradiction;
      apply sstep_cfg_instr_fault; [assumption | congruence | exact E]
    end.
  - (* [comment removed for export] *)
    lazymatch goal with
    | Hacc : mi_account_step _ ms' _ = MachineUnmodeled |- _ =>
      pose proof (mi_account_step_eqv segs ms' ms mo Heqv') as K; rewrite Hacc in K;
      destruct (mi_account_step segs ms mo) as [[ms1 mo1]| |] eqn:E; try contradiction;
      apply sstep_cfg_instr_unmodeled; [assumption | congruence | exact E]
    end.
  - (* [comment removed for export] *)
    lazymatch goal with
    | Hsp : syscall_spec (sys_input _ ms' ?x8) mo (Ok ?eff ?mo' ?evs0), Hsv : ms_svc_pending ms' = Some _,
      Hmat : materialize_model_accesses _ _ = Some ?mo'' |- _ =>
      exists (mkCfg (advance_past_svc (apply_effect ms eff)) mo''); split;
      [ apply (sstep_cfg_syscall segs ACFG ms mo x8 eff mo' mo'' evs0);
        [assumption | congruence | rewrite (sys_input_eqv segs ms ms' x8 Heqv); assumption
        | rewrite (sys_input_eqv segs ms ms' x8 Heqv); assumption | assumption | assumption]
      | symmetry; apply (xfer_syscall ms ms' mo eff mo'' x8 Heqv); congruence ]
    end.
  - (* [comment removed for export] *)
    lazymatch goal with
    | Hsp : syscall_spec (sys_input _ ms' ?x8) mo (Ok ?eff ?mo' ?evs0), Hsv : ms_svc_pending ms' = Some _,
      Hmat : materialize_model_accesses _ _ = None |- _ =>
      apply (sstep_cfg_syscall_materialization_fault segs ACFG ms mo x8 eff mo' evs0);
      [assumption | congruence | rewrite (sys_input_eqv segs ms ms' x8 Heqv); assumption
      | rewrite (sys_input_eqv segs ms ms' x8 Heqv); assumption | assumption | assumption]
    end.
  - (* [comment removed for export] *)
    lazymatch goal with
    | Hsp : syscall_spec (sys_input _ ms' ?x8) mo (Ok ?eff ?mo' ?evs0), Hsv : ms_svc_pending ms' = Some _,
      Hh : m_halted _ = Some ?code |- _ =>
      exists (mkCfg ms mo'); split;
      [ apply (sstep_cfg_exit segs ACFG ms mo x8 eff mo' evs0 code);
        [assumption | congruence | rewrite (sys_input_eqv segs ms ms' x8 Heqv); assumption | assumption
        | assumption]
      | symmetry; apply (xfer_exit ms ms' mo mo' x8 Heqv); congruence ]
    end.
  - (* [comment removed for export] *)
    lazymatch goal with
    | Hsp : syscall_spec (sys_input _ ms' ?x8) mo (Ok ?eff ?mo' ?evs0), Hsv : ms_svc_pending ms' = Some _,
      Hk : m_killed _ = Some ?sig |- _ =>
      exists (mkCfg ms mo'); split;
      [ apply (sstep_cfg_killed segs ACFG ms mo x8 eff mo' evs0 sig);
        [assumption | congruence | rewrite (sys_input_eqv segs ms ms' x8 Heqv); assumption | assumption]
      | symmetry; apply (xfer_exit ms ms' mo mo' x8 Heqv); congruence ]
    end.
  - (* [comment removed for export] *)
    lazymatch goal with
    | Hsp : syscall_spec (sys_input _ ms' ?x8) mo Unmodeled |- _ =>
      apply (sstep_cfg_syscall_unmodeled segs ACFG ms mo x8);
      [assumption | congruence | rewrite (sys_input_eqv segs ms ms' x8 Heqv); assumption]
    end.
Qed.

(* [comment removed for export] *)
Lemma node_ok_xfer : forall ms ms' mo (I : Type) (evs : I -> list event) (nx : I -> config),
  ms_eqv ms ms' ->
  node_ok segs (mkCfg ms mo) I evs nx ->
  node_ok segs (mkCfg ms' mo) I evs (fun i => xfer ms' mo (nx i))
  /\ (forall i, cfg_eqv (nx i) (xfer ms' mo (nx i))).
Proof.
  intros ms ms' mo I evs nx Heqv [Hsound Hcompl]. split; [split|].
  - intros i. exact (proj1 (sstep_xfer ms ms' mo (evs i) (nx i) Heqv (Hsound i))).
  - intros e st' Hst'.
    pose proof (sstep_xfer_back ms ms' mo e st' Heqv Hst') as K.
    destruct st' as [n'|].
    + destruct K as (n & Hst & ->).
      destruct (Hcompl e (SNext n) Hst) as (i & -> & Hn).
      injection Hn as ->. exists i. split; reflexivity.
    + destruct (Hcompl e SError K) as (i & _ & Habs). discriminate Habs.
  - intros i. exact (proj2 (sstep_xfer ms ms' mo (evs i) (nx i) Heqv (Hsound i))).
Qed.

(* [comment removed for export] *)
Theorem realizes_cfg_eqv : forall c T,
  realizes segs c T -> forall c', cfg_eqv c c' -> realizes segs c' T.
Proof.
  intros c T H. induction H as [c I evs nx T i0 Hnode Hk IH | c Hh | c T T' H IH Heq];
    intros c' Heqv.
  - destruct c as [ms mo], c' as [ms' mo']. destruct Heqv as [Hms Hmo]; simpl in Hms, Hmo; subst mo'.
    destruct (node_ok_xfer ms ms' mo I evs nx Hms Hnode) as [Hnode' Hx].
    apply (rz_node segs (mkCfg ms' mo) I evs (fun i => xfer ms' mo (nx i)) T i0 Hnode').
    intros i. apply (IH i). apply Hx.
  - apply rz_halt. destruct Heqv as [_ <-]. exact Hh.
  - apply (rz_conseq segs c' T T'); [apply IH; exact Heqv | exact Heq].
Qed.

Theorem realizes_ms_eqv : forall ms1 ms2 mo T,
  ms_eqv ms1 ms2 ->
  realizes segs (mkCfg ms1 mo) T -> realizes segs (mkCfg ms2 mo) T.
Proof.
  intros ms1 ms2 mo T Heqv H. apply (realizes_cfg_eqv _ _ H). split; [exact Heqv | reflexivity].
Qed.

Theorem realizes_eqv_iff : forall ms1 ms2 mo T,
  ms_eqv ms1 ms2 ->
  realizes segs (mkCfg ms1 mo) T <-> realizes segs (mkCfg ms2 mo) T.
Proof.
  intros ms1 ms2 mo T Heqv. split; apply realizes_ms_eqv; [exact Heqv | apply ms_eqv_sym; exact Heqv].
Qed.

(* [comment removed for export] *)
Corollary realizes_regs_eqv : forall (regs1 regs2 F : bvmap 5 word) (pc : word) svc rv fc
    (mem rom : word -> option byte) mo T,
  (forall r, is_x0 r = false -> reg_get regs1 r = reg_get regs2 r) ->
  realizes segs (mkCfg {| ms_regs := regs1; ms_fregs := F; ms_pc_val := pc; ms_svc_pending := svc;
                          ms_resv := rv; ms_fcsr := fc; ms_mem := mem; ms_rom := rom |} mo) T <->
  realizes segs (mkCfg {| ms_regs := regs2; ms_fregs := F; ms_pc_val := pc; ms_svc_pending := svc;
                          ms_resv := rv; ms_fcsr := fc; ms_mem := mem; ms_rom := rom |} mo) T.
Proof.
  intros * Hr. apply realizes_eqv_iff. split; [exact Hr|]. split; [apply regs_eqv_refl|]. repeat split; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma getr_reg_get : forall regs (r : reg), is_x0 r = false ->
  OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.PropExec.getr regs r = reg_get regs r.
Proof.
  intros regs r Hr. unfold OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.PropExec.getr.
  rewrite OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.PropExec.bv_eqb0_is_x0, Hr. reflexivity.
Qed.

Corollary realizes_mkst_of_MS : forall (regs R : bvmap 5 word) (pc : word)
    (mem : word -> option byte) mo T,
  (forall r : reg, is_x0 r = false -> OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.PropExec.getr regs r = reg_get R r) ->
  realizes segs (mkCfg (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.MState.MS R bvmap_empty pc (Z_to_bv 32 0) None mem
                          (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.PropExec.seg_rom segs)) mo) T ->
  realizes segs (mkCfg (@OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.PropExec.mkst OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.PropExec.fx0 regs pc mem
                          (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.PropExec.seg_rom segs)) mo) T.
Proof.
  intros regs R pc mem mo T Hr H.
  assert (Hr' : forall r : reg, is_x0 r = false -> reg_get regs r = reg_get R r).
  { intros r E. rewrite <- (getr_reg_get regs r E). apply Hr. exact E. }
  change (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.PropExec.seg_rom segs)
    with (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.PropExec.seg_rom segs).
  unfold OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.PropExec.mkst.
  unfold OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.MState.MS in H.
  exact (proj2 (realizes_regs_eqv regs R bvmap_empty pc None None (Z_to_bv 32 0) mem _ mo T Hr') H).
Qed.

Corollary realizes_MS_of_mkst : forall (regs R : bvmap 5 word) (pc : word)
    (mem : word -> option byte) mo T,
  (forall r : reg, is_x0 r = false -> OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.PropExec.getr regs r = reg_get R r) ->
  realizes segs (mkCfg (@OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.PropExec.mkst OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.PropExec.fx0 regs pc mem
                          (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.PropExec.seg_rom segs)) mo) T ->
  realizes segs (mkCfg (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.MState.MS R bvmap_empty pc (Z_to_bv 32 0) None mem
                          (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.PropExec.seg_rom segs)) mo) T.
Proof.
  intros regs R pc mem mo T Hr H.
  assert (Hr' : forall r : reg, is_x0 r = false -> reg_get regs r = reg_get R r).
  { intros r E. rewrite <- (getr_reg_get regs r E). apply Hr. exact E. }
  change (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.PropExec.seg_rom segs)
    with (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.PropExec.seg_rom segs).
  unfold OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.MState.MS.
  unfold OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.PropExec.mkst in H.
  exact (proj1 (realizes_regs_eqv regs R bvmap_empty pc None None (Z_to_bv 32 0) mem _ mo T Hr') H).
Qed.

(* [comment removed for export] *)
Corollary realizes_ms_eqv_full : forall ms1 ms2 mo T,
  OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.RegsEquiv.ms_eqv ms1 ms2 ->
  realizes segs (mkCfg ms1 mo) T <-> realizes segs (mkCfg ms2 mo) T.
Proof. intros ms1 ms2 mo T H. apply realizes_eqv_iff. apply ms_eqv_of_full. exact H. Qed.

End WithSegs.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Frame.

Definition mkR_of (regs : bvmap 5 word) : bvmap 5 word :=
  let g := OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.PropExec.getr regs in
  OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Frame.mkR
    (g 1) (g 2) (g 3) (g 4) (g 5) (g 6) (g 7) (g 8) (g 9) (g 10) (g 11) (g 12) (g 13) (g 14) (g 15) (g 16)
    (g 17) (g 18) (g 19) (g 20) (g 21) (g 22) (g 23) (g 24) (g 25) (g 26) (g 27) (g 28) (g 29) (g 30) (g 31).

Lemma getr_mkR_of : forall regs (r : reg), is_x0 r = false ->
  OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.PropExec.getr regs r = reg_get (mkR_of regs) r.
Proof.
  intros regs r Hr.
  destruct (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.RegsEquiv.reg_of_nat r) as (n & -> & Hn).
  do 32 (destruct n as [|n]; [first [discriminate Hr | reflexivity] |]). lia.
Qed.

Section Junction.
Variable segs : list Segment.

(* [comment removed for export] *)
Corollary realizes_mkst_of_mkR : forall (regs : bvmap 5 word) (pc : word)
    (mem : word -> option byte) mo T,
  realizes segs (mkCfg (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.MState.MS (mkR_of regs) bvmap_empty pc (Z_to_bv 32 0) None mem
                          (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.PropExec.seg_rom segs)) mo) T ->
  realizes segs (mkCfg (@OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.PropExec.mkst OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.PropExec.fx0 regs pc mem
                          (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.PropExec.seg_rom segs)) mo) T.
Proof.
  intros regs pc mem mo T H. apply (realizes_mkst_of_MS segs regs (mkR_of regs)); [|exact H].
  intros r Hr. apply getr_mkR_of. exact Hr.
Qed.

Corollary realizes_mkR_of_mkst : forall (regs : bvmap 5 word) (pc : word)
    (mem : word -> option byte) mo T,
  realizes segs (mkCfg (@OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.PropExec.mkst OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.PropExec.fx0 regs pc mem
                          (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.PropExec.seg_rom segs)) mo) T ->
  realizes segs (mkCfg (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.MState.MS (mkR_of regs) bvmap_empty pc (Z_to_bv 32 0) None mem
                          (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.PropExec.seg_rom segs)) mo) T.
Proof.
  intros regs pc mem mo T H. apply (realizes_MS_of_mkst segs regs (mkR_of regs)); [|exact H].
  intros r Hr. apply getr_mkR_of. exact Hr.
Qed.
End Junction.
