(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import PropExec MState Frame.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.


Definition regs_eqv (R R' : bvmap 5 word) : Prop := forall r, reg_get R r = reg_get R' r.

Lemma regs_eqv_refl : forall R, regs_eqv R R.
Proof. intros R r. reflexivity. Qed.
Lemma regs_eqv_sym : forall R R', regs_eqv R R' -> regs_eqv R' R.
Proof. intros R R' H r. symmetry. apply H. Qed.
Lemma regs_eqv_trans : forall R1 R2 R3, regs_eqv R1 R2 -> regs_eqv R2 R3 -> regs_eqv R1 R3.
Proof. intros R1 R2 R3 H1 H2 r. etransitivity; [apply H1|apply H2]. Qed.

Definition regs_eqvW (R R' : bvmap 5 word) : Prop := forall r : reg, bv_unsigned r <> 0%Z -> reg_get R r = reg_get R' r.
Lemma regs_eqvW_refl : forall R, regs_eqvW R R.
Proof. intros R r _. reflexivity. Qed.
Lemma regs_eqvW_sym : forall R R', regs_eqvW R R' -> regs_eqvW R' R.
Proof. intros R R' H r Hr. symmetry. apply H. exact Hr. Qed.
Lemma regs_eqvW_trans : forall R1 R2 R3, regs_eqvW R1 R2 -> regs_eqvW R2 R3 -> regs_eqvW R1 R3.
Proof. intros R1 R2 R3 H1 H2 r Hr. etransitivity; [apply H1|apply H2]; exact Hr. Qed.

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

Lemma regs_eqvW_set : forall R R' (k : reg) v,
  regs_eqvW R R' -> regs_eqvW (bvmap_set k v R) (bvmap_set k v R').
Proof. intros R R' k v H r Hr. rewrite !reg_get_set. destruct (bv_eqb k r); [reflexivity|apply H; exact Hr]. Qed.

Definition rgetW (R : bvmap 5 word) (r : reg) : word := if is_x0 r then w0 else reg_get R r.
Lemma rget_core : forall R F pc fc rv r, rget (Core R F pc fc rv) r = rgetW R r.
Proof. reflexivity. Qed.
Lemma rgetW_eqv : forall R R', regs_eqvW R R' -> forall r, rgetW R r = rgetW R' r.
Proof.
  intros R R' H r. unfold rgetW, is_x0. destruct (Z.eqb_spec (bv_unsigned r) 0); [reflexivity|]. apply H. assumption.
Qed.


Definition core_eqv (c c' : core) : Prop :=
  regs_eqvW (c_regs c) (c_regs c') /\ regs_eqv (c_fregs c) (c_fregs c') /\
  c_pc c = c_pc c' /\ c_fcsr c = c_fcsr c' /\ c_resv c = c_resv c'.

Inductive eff_eqv : eff -> eff -> Prop :=
| EqvDone : forall c c', core_eqv c c' -> eff_eqv (EDone c) (EDone c')
| EqvIllegal : forall c c', eff_eqv (EIllegal c) (EIllegal c')
| EqvDefIllegal : forall c c', eff_eqv (EDefinedIllegal c) (EDefinedIllegal c')
| EqvEcall : forall c c', eff_eqv (EEcall c) (EEcall c')
| EqvEbreak : forall c c', eff_eqv (EEbreak c) (EEbreak c')
| EqvFault : forall c c', eff_eqv (EFault c) (EFault c')
| EqvLoad : forall n a k k', (forall v, eff_eqv (k v) (k' v)) -> eff_eqv (ELoad n a k) (ELoad n a k')
| EqvStore : forall n a v k k', eff_eqv k k' -> eff_eqv (EStore n a v k) (EStore n a v k').

Lemma core_eqv_mk : forall R R' F F' pc fc rv, regs_eqvW R R' -> regs_eqv F F' ->
  core_eqv (Core R F pc fc rv) (Core R' F' pc fc rv).
Proof. intros. repeat split; assumption. Qed.

Local Ltac core_tac :=
  unfold core_eqv, rset, fset, with_regs, with_fregs, with_pc, with_fcsr, with_resv,
         accrue, fwrite, inval_resv in *; simpl in *.

Lemma core_eqv_rset : forall r v c c', core_eqv c c' -> core_eqv (rset r v c) (rset r v c').
Proof.
  intros r v [R F p f s] [R' F' p' f' s'] H. core_tac. destruct H as (HR & HF & -> & -> & ->).
  destruct (is_x0 r); simpl; repeat split; auto using regs_eqv_set, regs_eqvW_set.
Qed.
Lemma core_eqv_fset : forall r v c c', core_eqv c c' -> core_eqv (fset r v c) (fset r v c').
Proof.
  intros r v [R F p f s] [R' F' p' f' s'] H. core_tac. destruct H as (HR & HF & -> & -> & ->).
  repeat split; auto using regs_eqv_set, regs_eqvW_set.
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
    | apply EqvIllegal | apply EqvDefIllegal | apply EqvEcall | apply EqvEbreak | apply EqvFault
    | apply EqvLoad; intros ?
    | apply EqvStore
    | match goal with |- eff_eqv (match ?X with _ => _ end) _ => destruct X end
    | match goal with |- eff_eqv (match ?X with _ => _ end _) _ => destruct X end ].

Local Ltac unfold_exec :=
  cbv beta iota zeta delta [exec fget fread c_regs c_fregs c_pc c_fcsr c_resv
                            with_pc load_val store_val exec_csr resolve_rm frm_of];
  rewrite ?rget_core.

Lemma exec_eqv_core : forall R R' F F' pc fc rv sz i,
  regs_eqvW R R' -> regs_eqv F F' ->
  eff_eqv (exec sz i (Core R F pc fc rv)) (exec sz i (Core R' F' pc fc rv)).
Proof.
  intros R R' F F' pc fc rv sz i HR HF.
  destruct i; unfold_exec; rewrite ?(rgetW_eqv R R' HR), ?HF; eqv_struct HR HF.
Qed.

Lemma exec_eqv : forall sz i c c', core_eqv c c' -> eff_eqv (exec sz i c) (exec sz i c').
Proof.
  intros sz i [R F p f s] [R' F' p' f' s'] (HR & HF & Hp & Hf & Hs); simpl in *; subst.
  apply exec_eqv_core; assumption.
Qed.


Definition ms_eqv (ms ms' : machine_state) : Prop :=
  regs_eqvW (ms_regs ms) (ms_regs ms') /\ regs_eqv (ms_fregs ms) (ms_fregs ms') /\
  ms_pc_val ms = ms_pc_val ms' /\ ms_svc_pending ms = ms_svc_pending ms' /\
  ms_resv ms = ms_resv ms' /\ ms_fcsr ms = ms_fcsr ms' /\
  ms_mem ms = ms_mem ms' /\ ms_rom ms = ms_rom ms'.

Lemma ms_eqv_refl : forall ms, ms_eqv ms ms.
Proof. intros ms. repeat split; first [apply regs_eqvW_refl | apply regs_eqv_refl]. Qed.
Lemma ms_eqv_sym : forall ms ms', ms_eqv ms ms' -> ms_eqv ms' ms.
Proof.
  intros ms ms' (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8).
  repeat split; auto using regs_eqv_sym, regs_eqvW_sym; congruence.
Qed.
Lemma ms_eqv_trans : forall a b c, ms_eqv a b -> ms_eqv b c -> ms_eqv a c.
Proof.
  intros a b c (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8) (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8).
  repeat split; eauto using regs_eqv_trans, regs_eqvW_trans; congruence.
Qed.

Definition res_eqv (r r' : machine_result (access_report machine_state)) : Prop :=
  match r, r' with
  | MachineOk a, MachineOk b => ms_eqv (access_value _ a) (access_value _ b) /\ accessed_ranges _ a = accessed_ranges _ b
  | MachineFault, MachineFault => True
  | MachineUnmodeled, MachineUnmodeled => True
  | _, _ => False
  end.

Section WithSegs.
Variable segs : list Segment.

Lemma interp_eff_accesses_eqv : forall t t', eff_eqv t t' -> forall m,
  match interp_eff_accesses segs t m, interp_eff_accesses segs t' m with
  | MachineOk r, MachineOk r' =>
      core_eqv (fst (access_value _ r)) (fst (access_value _ r')) /\ snd (access_value _ r) = snd (access_value _ r')
      /\ accessed_ranges _ r = accessed_ranges _ r'
  | MachineFault, MachineFault => True
  | MachineUnmodeled, MachineUnmodeled => True
  | _, _ => False
  end.
Proof.
  intros t t' H. induction H; intros m; cbn [interp_eff_accesses access_value accessed_ranges fst snd]; auto.
  - destruct (ov_read_bytes segs m a (width_bytes n)) as [bs|]; [|destruct (range_meets_vvar segs a (width_bytes n)); exact I].
    specialize (H0 (bv_extract 0 n (le_bytes_to_word bs)) m).
    destruct (interp_eff_accesses segs (k _) m) as [r| |]; destruct (interp_eff_accesses segs (k' _) m) as [r'| |];
      cbn [access_value accessed_ranges] in *; try exact H0; try contradiction.
    destruct H0 as (H1 & H2 & H3). rewrite H3. auto.
  - destruct (store_ok segs m a (width_bytes n)); [|try destruct (range_meets_vvar segs a (width_bytes n)); exact I].
    specialize (IHeff_eqv (write_to_mem m a (Z_to_le_bytes (width_bytes n) (bv_unsigned v)))).
    destruct (interp_eff_accesses segs k _) as [r| |]; destruct (interp_eff_accesses segs k' _) as [r'| |];
      cbn [access_value accessed_ranges] in *; try exact IHeff_eqv; try contradiction.
    destruct IHeff_eqv as (H1 & H2 & H3). rewrite H3. auto.
Qed.

Lemma ms_reg_eqv : forall ms ms' r, ms_eqv ms ms' -> ms_reg ms r = ms_reg ms' r.
Proof.
  intros ms ms' r (HR & _). unfold ms_reg. destruct (bv_eqb r 0) eqn:E; [reflexivity|]. apply HR.
  intros Hr. assert (E' : bv_eqb r 0 = true) by (apply bv_eqb_eq; apply bv_eq; rewrite Hr; reflexivity). congruence.
Qed.

Lemma decode_exec_accesses_eqv : forall ms ms' w, ms_eqv ms ms' ->
  res_eqv (decode_exec_accesses segs ms w) (decode_exec_accesses segs ms' w).
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

Lemma step_accesses_eqv : forall ms ms', ms_eqv ms ms' ->
  res_eqv (RiscvSemantics.step_accesses segs ms) (RiscvSemantics.step_accesses segs ms').
Proof.
  intros ms ms' Heqv. pose proof Heqv as (_ & _ & Hpc & _ & _ & _ & Hm & _).
  unfold RiscvSemantics.step_accesses, ms_pc. rewrite <- Hpc, <- Hm.
  destruct (fetch_word segs (ms_pc_val ms)); [apply decode_exec_accesses_eqv; exact Heqv|].
  destruct (fetch_word_ov segs (ms_mem ms) (ms_pc_val ms)); [apply decode_exec_accesses_eqv; exact Heqv|].
  destruct (fetch_tail_any segs (ms_mem ms) (ms_pc_val ms)); [apply decode_exec_accesses_eqv; exact Heqv|].
  unfold fetch_failure. repeat match goal with |- context [if ?c then _ else _] => destruct c end; exact I.
Qed.

Lemma mi_account_step_eqv : forall ms ms' mo, ms_eqv ms ms' ->
  match mi_account_step segs ms mo, mi_account_step segs ms' mo with
  | MachineOk (a, moa), MachineOk (b, mob) => ms_eqv a b /\ moa = mob
  | MachineFault, MachineFault => True
  | MachineUnmodeled, MachineUnmodeled => True
  | _, _ => False
  end.
Proof.
  intros ms ms' mo Heqv. pose proof (step_accesses_eqv ms ms' Heqv) as K. unfold mi_account_step.
  destruct (RiscvSemantics.step_accesses segs ms) as [r| |]; destruct (RiscvSemantics.step_accesses segs ms') as [r'| |];
    simpl in K; try exact K; try contradiction.
  destruct K as [Hv <-]. destruct (materialize_model_accesses mo (accessed_ranges _ r)); [auto| exact I].
Qed.


Lemma syscall_args_eqv : forall ms ms', ms_eqv ms ms' -> syscall_args ms = syscall_args ms'.
Proof. intros ms ms' (HR & _). unfold syscall_args, ms_gpr. rewrite !HR by (vm_compute; discriminate). reflexivity. Qed.

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
  unfold apply_effect, set_reg; simpl. repeat split; simpl; auto using regs_eqv_set, regs_eqvW_set.
Qed.

Lemma advance_past_svc_eqv : forall ms ms', ms_eqv ms ms' ->
  ms_eqv (advance_past_svc ms) (advance_past_svc ms').
Proof.
  intros [R F pc svc rv fc m ro] [R' F' pc' svc' rv' fc' m' ro']
         (HR & HF & Hpc & Hsvc & Hrv & Hfc & Hm & Hro); simpl in *; subst.
  unfold advance_past_svc, ms_pc; simpl. repeat split; auto.
Qed.

(* the vDSO call arms of Run.sstep. These seven lemmas are port of
   Lib/RegsEquiv (edition text , l.242-292), carried over with the one change this file needs: the integer
   registers are related by regs_eqvW here, so set_reg_eqv also uses regs_eqvW_set. *)
Lemma set_reg_eqv : forall ms ms' r v, ms_eqv ms ms' -> ms_eqv (set_reg ms r v) (set_reg ms' r v).
Proof.
  intros [R F pc svc rv fc m ro] [R' F' pc' svc' rv' fc' m' ro'] r v
         (HR & HF & Hpc & Hsvc & Hrv & Hfc & Hm & Hro); simpl in *; subst.
  unfold set_reg. destruct (bv_eqb r 0); [repeat split; simpl; auto|].
  repeat split; simpl; auto using regs_eqv_set, regs_eqvW_set.
Qed.

Lemma vdso_write_regs_eqv : forall rs vs ms ms', ms_eqv ms ms' ->
  ms_eqv (vdso_write_regs ms rs vs) (vdso_write_regs ms' rs vs).
Proof.
  induction rs as [|r rs IH]; intros [|v vs] ms ms' H; cbn [vdso_write_regs]; try exact H.
  apply IH. apply set_reg_eqv. exact H.
Qed.

Lemma vdso_with_mem_eqv : forall ms ms' m, ms_eqv ms ms' -> ms_eqv (vdso_with_mem ms m) (vdso_with_mem ms' m).
Proof.
  intros [R F pc svc rv fc m0 ro] [R' F' pc' svc' rv' fc' m0' ro'] m
         (HR & HF & Hpc & Hsvc & Hrv & Hfc & Hm & Hro); simpl in *; subst.
  unfold vdso_with_mem; simpl. repeat split; auto.
Qed.

Lemma vdso_set_pc_eqv : forall ms ms' pc, ms_eqv ms ms' -> ms_eqv (vdso_set_pc ms pc) (vdso_set_pc ms' pc).
Proof.
  intros [R F pc0 svc rv fc m ro] [R' F' pc0' svc' rv' fc' m' ro'] pc
         (HR & HF & Hpc & Hsvc & Hrv & Hfc & Hm & Hro); simpl in *; subst.
  unfold vdso_set_pc; simpl. repeat split; auto.
Qed.

Lemma vdso_read_regs_eqv : forall ms ms', ms_eqv ms ms' -> vdso_read_regs ms = vdso_read_regs ms'.
Proof. intros ms ms' H. unfold vdso_read_regs. apply map_ext. intros r. apply ms_reg_eqv. exact H. Qed.

Lemma vdso_tail_eqv : forall ms1 ms1' lo fr eff ra, ms_eqv ms1 ms1' ->
  ms_eqv (vdso_set_pc (apply_effect (vdso_with_mem ms1 (vdso_write_frame segs (ms_mem ms1) lo fr)) eff) ra)
         (vdso_set_pc (apply_effect (vdso_with_mem ms1' (vdso_write_frame segs (ms_mem ms1') lo fr)) eff) ra).
Proof.
  intros ms1 ms1' lo fr eff ra H. pose proof H as (_ & _ & _ & _ & _ & _ & Hm & _). rewrite <- Hm.
  apply vdso_set_pc_eqv, apply_effect_eqv, vdso_with_mem_eqv, H.
Qed.

Lemma vdso_post_eqv : forall ms ms' mo f eff, ms_eqv ms ms' ->
  ms_eqv (vdso_post segs ms mo f eff) (vdso_post segs ms' mo f eff).
Proof.
  intros ms ms' mo f eff H.
  pose proof (vdso_read_regs_eqv ms ms' H) as Er.
  assert (Era : forall r, ms_reg ms r = ms_reg ms' r) by (intros r; apply ms_reg_eqv; exact H).
  assert (Esp : ms_sp ms = ms_sp ms') by (destruct H as (HR & _); unfold ms_sp; apply HR; vm_compute; discriminate).
  assert (Eb : ms_read_byte ms = ms_read_byte ms').
  { destruct H as (_ & _ & _ & _ & _ & _ & Hm & Hro). unfold ms_read_byte. rewrite Hm, Hro. reflexivity. }
  unfold vdso_post. rewrite Er, ?Era, Esp, Eb. cbv zeta.
  apply vdso_tail_eqv, vdso_write_regs_eqv, H.
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

Lemma sstep_eqv : forall ms ms' mo evs X, ms_eqv ms ms' ->
  sstep segs (mkCfg ms mo) evs X ->
  exists X', sstep segs (mkCfg ms' mo) evs X' /\ to_eqv X X'.
Proof.
  intros ms ms' mo evs X Heqv Hst.
  pose proof (mi_account_step_eqv ms ms' mo Heqv) as Hres.
  pose proof Heqv as (_ & _ & Hpc0 & Hsvc & _ & _ & _ & _).
  inversion Hst; subst.
  -
    match goal with Hm : mi_account_step segs ms mo = _ |- _ => rewrite Hm in Hres end. destruct (mi_account_step segs ms' mo) as [[ms1' mo1']| |] eqn:E; simpl in Hres; try contradiction.
    destruct Hres as [Hres <-].
    exists (SNext (mkCfg ms1' model')). split; [apply sstep_instr; auto; congruence|]. split; [exact Hres| reflexivity].
  - match goal with Hm : mi_account_step segs ms mo = _ |- _ => rewrite Hm in Hres end. destruct (mi_account_step segs ms' mo) as [[ms1' mo1']| |] eqn:E; simpl in Hres; try contradiction.
    exists SError. split; [apply sstep_instr_fault; auto; congruence| exact I].
  - match goal with Hm : mi_account_step segs ms mo = _ |- _ => rewrite Hm in Hres end. destruct (mi_account_step segs ms' mo) as [[ms1' mo1']| |] eqn:E; simpl in Hres; try contradiction.
    exists SError. split; [apply sstep_instr_unmodeled; auto; unfold ms_pc in *; congruence| exact I].
  - (* sstep_vdso_call *)
    match goal with H : mi_account_step segs ms mo = _ |- _ => rewrite H in Hres end.
    destruct (mi_account_step segs ms' mo) as [[ms1' mo1]| |] eqn:E; simpl in Hres; try contradiction.
    eexists. split.
    + apply (sstep_vdso_call segs ms' mo fn n eff model' model'' evs);
        [assumption| congruence| exact E| unfold ms_pc in *; congruence| assumption
        | rewrite <- (sys_input_eqv ms ms' _ Heqv); assumption| assumption| assumption| assumption].
    + split; [apply vdso_post_eqv; exact Heqv| reflexivity].
  - (* sstep_vdso_materialization_fault *)
    match goal with H : mi_account_step segs ms mo = _ |- _ => rewrite H in Hres end.
    destruct (mi_account_step segs ms' mo) as [[ms1' mo1]| |] eqn:E; simpl in Hres; try contradiction.
    exists SError. split; [|exact I].
    apply (sstep_vdso_materialization_fault segs ms' mo fn n eff model' evs0);
      [assumption| congruence| exact E| unfold ms_pc in *; congruence| assumption
      | rewrite <- (sys_input_eqv ms ms' _ Heqv); assumption| assumption| assumption| assumption].
  - (* sstep_vdso_unmodeled *)
    match goal with H : mi_account_step segs ms mo = _ |- _ => rewrite H in Hres end.
    destruct (mi_account_step segs ms' mo) as [[ms1' mo1]| |] eqn:E; simpl in Hres; try contradiction.
    exists SError. split; [|exact I].
    apply (sstep_vdso_unmodeled segs ms' mo fn); [assumption| congruence| exact E| unfold ms_pc in *; congruence|].
    match goal with Hu : vdso_call_unmodeled _ ms mo fn |- _ =>
      destruct Hu as [Hu0 | [(n0 & Hn & Hs) | (n0 & eff0 & mo0 & evs1 & Hn & Hs & Hr)]] end;
      [left; exact Hu0
      | right; left; exists n0; rewrite <- (sys_input_eqv ms ms' _ Heqv); split; assumption
      | right; right; exists n0, eff0, mo0, evs1; rewrite <- (sys_input_eqv ms ms' _ Heqv); repeat split; assumption].
  -
    exists (SNext (mkCfg (advance_past_svc (apply_effect ms' eff)) model'')). split.
    + apply (sstep_syscall segs ms' mo x8 eff model' model'' evs);
        [assumption| congruence| rewrite <- (sys_input_eqv ms ms' x8 Heqv); assumption| assumption| assumption].
    + split; [| reflexivity]. apply advance_past_svc_eqv, apply_effect_eqv, Heqv.
  -
    exists SError. split; [|exact I].
    apply (sstep_syscall_materialization_fault segs ms' mo x8 eff model' evs0);
      [assumption| congruence| rewrite <- (sys_input_eqv ms ms' x8 Heqv); assumption| assumption| assumption].
  -
    exists (SNext (mkCfg ms' model')). split.
    + apply (sstep_exit segs ms' mo x8 eff model' evs0 code);
        [assumption| congruence| rewrite <- (sys_input_eqv ms ms' x8 Heqv); assumption| assumption| assumption].
    + split; [exact Heqv| reflexivity].
  -
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

End WithSegs.
