(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the read case also splits on the new vvar-range test; the fetch-failure proof covers its new vDSO test; sstep_eqv covers the three new vDSO step arms and instr_unmodeled's new vDSO-entry premise, through new equivalence lemmas for the vDSO call; new sys_rob_eqv, so realizes_eqv carries node_ok's third conjunct; imports of Vdso and RomBase). *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Vdso Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Common Require Import SimInv ExitSim.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import PropExec Shape.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Common.Cfg Require RomBase.

(* [comment removed for export] *)
Lemma reg_get_set_same' : forall (R : bvmap 5 word) (r : reg) v, reg_get (bvmap_set r v R) r = v.
Proof. intros. unfold reg_get. rewrite bvmap_get_set_same. reflexivity. Qed.
Lemma reg_get_set_other' : forall (R : bvmap 5 word) (r r' : reg) v, r <> r' -> reg_get (bvmap_set r v R) r' = reg_get R r'.
Proof. intros. unfold reg_get. rewrite bvmap_get_set_other by congruence. reflexivity. Qed.
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

Lemma reg_get_set : forall (R : bvmap 5 word) (k r : reg) v,
  reg_get (bvmap_set k v R) r = if bv_eqb k r then v else reg_get R r.
Proof.
  intros R k r v. destruct (bv_eqb k r) eqn:E.
  - apply bv_eqb_eq in E. subst. apply reg_get_set_same'.
  - apply reg_get_set_other'. intros ->. rewrite bv_eqb_refl in E. discriminate.
Qed.

Lemma regs_eqv_set : forall R R' (k : reg) v,
  regs_eqv R R' -> regs_eqv (bvmap_set k v R) (bvmap_set k v R').
Proof. intros R R' k v H r. rewrite !reg_get_set. destruct (bv_eqb k r); [reflexivity|apply H]. Qed.

(* [comment removed for export] *)
Definition iregs_eqv (R R' : bvmap 5 word) : Prop :=
  forall r : reg, bv_unsigned r <> 0%Z -> reg_get R r = reg_get R' r.

Lemma iregs_eqv_refl : forall R, iregs_eqv R R.
Proof. intros R r _. reflexivity. Qed.
Lemma iregs_eqv_sym : forall R R', iregs_eqv R R' -> iregs_eqv R' R.
Proof. intros R R' H r Hr. symmetry. apply H. exact Hr. Qed.
Lemma iregs_eqv_trans : forall R1 R2 R3, iregs_eqv R1 R2 -> iregs_eqv R2 R3 -> iregs_eqv R1 R3.
Proof. intros R1 R2 R3 H1 H2 r Hr. etransitivity; [apply H1|apply H2]; exact Hr. Qed.
Lemma iregs_eqv_of_regs_eqv : forall R R', regs_eqv R R' -> iregs_eqv R R'.
Proof. intros R R' H r _. apply H. Qed.
Lemma iregs_eqv_set : forall R R' (k : reg) v,
  iregs_eqv R R' -> iregs_eqv (bvmap_set k v R) (bvmap_set k v R').
Proof. intros R R' k v H r Hr. rewrite !reg_get_set. destruct (bv_eqb k r); [reflexivity|apply H; exact Hr]. Qed.
Lemma iregs_rget : forall R R', iregs_eqv R R' -> forall r : reg,
  (if is_x0 r then w0 else reg_get R r) = (if is_x0 r then w0 else reg_get R' r).
Proof.
  intros R R' H r. unfold is_x0. destruct (Z.eqb_spec (bv_unsigned r) 0); [reflexivity|]. apply H. assumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition core_eqv (c c' : core) : Prop :=
  iregs_eqv (c_regs c) (c_regs c') /\ regs_eqv (c_fregs c) (c_fregs c') /\
  c_pc c = c_pc c' /\ c_fcsr c = c_fcsr c' /\ c_resv c = c_resv c'.

Inductive eff_eqv : eff -> eff -> Prop :=
| EqvDone : forall c c', core_eqv c c' -> eff_eqv (EDone c) (EDone c')
| EqvIllegal : forall c c', eff_eqv (EIllegal c) (EIllegal c')
| EqvEcall : forall c c', eff_eqv (EEcall c) (EEcall c')
| EqvEbreak : forall c c', eff_eqv (EEbreak c) (EEbreak c')
| EqvFault : forall c c', eff_eqv (EFault c) (EFault c')
| EqvDefinedIllegal : forall c c', eff_eqv (EDefinedIllegal c) (EDefinedIllegal c')  (* [comment removed for export] *)
| EqvLoad : forall n a k k', (forall v, eff_eqv (k v) (k' v)) -> eff_eqv (ELoad n a k) (ELoad n a k')
| EqvStore : forall n a v k k', eff_eqv k k' -> eff_eqv (EStore n a v k) (EStore n a v k').

Lemma core_eqv_mk : forall R R' F F' pc fc rv, iregs_eqv R R' -> regs_eqv F F' ->
  core_eqv (Core R F pc fc rv) (Core R' F' pc fc rv).
Proof. intros. repeat split; assumption. Qed.

Local Ltac core_tac :=
  unfold core_eqv, rset, fset, with_regs, with_fregs, with_pc, with_fcsr, with_resv,
         accrue, fwrite, inval_resv in *; simpl in *.

Lemma core_eqv_rset : forall r v c c', core_eqv c c' -> core_eqv (rset r v c) (rset r v c').
Proof.
  intros r v [R F p f s] [R' F' p' f' s'] H. core_tac. destruct H as (HR & HF & -> & -> & ->).
  destruct (is_x0 r); simpl; repeat split; auto using iregs_eqv_set.
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

Lemma exec_eqv_core : forall R R' F F' pc fc rv sz i,
  iregs_eqv R R' -> regs_eqv F F' ->
  eff_eqv (exec sz i (Core R F pc fc rv)) (exec sz i (Core R' F' pc fc rv)).
Proof.
  intros R R' F F' pc fc rv sz i HR HF.
  destruct i; unfold_exec; rewrite ?(iregs_rget R R' HR), ?HF; eqv_struct HR HF.
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
  iregs_eqv (ms_regs ms) (ms_regs ms') /\ regs_eqv (ms_fregs ms) (ms_fregs ms') /\
  ms_pc_val ms = ms_pc_val ms' /\ ms_svc_pending ms = ms_svc_pending ms' /\
  ms_resv ms = ms_resv ms' /\ ms_fcsr ms = ms_fcsr ms' /\
  ms_mem ms = ms_mem ms' /\ ms_rom ms = ms_rom ms'.

Lemma ms_eqv_refl : forall ms, ms_eqv ms ms.
Proof. intros ms. repeat split; first [apply iregs_eqv_refl | apply regs_eqv_refl]. Qed.
Lemma ms_eqv_sym : forall ms ms', ms_eqv ms ms' -> ms_eqv ms' ms.
Proof.
  intros ms ms' (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8).
  repeat split; auto using regs_eqv_sym, iregs_eqv_sym; congruence.
Qed.
Lemma ms_eqv_trans : forall a b c, ms_eqv a b -> ms_eqv b c -> ms_eqv a c.
Proof.
  intros a b c (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8) (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8).
  repeat split; eauto using regs_eqv_trans, iregs_eqv_trans; congruence.
Qed.

(* [comment removed for export] *)
Definition ares_eqv {A : Type} (eqv : A -> A -> Prop)
    (r r' : machine_result (access_report A)) : Prop :=
  match r, r' with
  | MachineOk a, MachineOk b =>
      eqv (@access_value _ a) (@access_value _ b) /\ @accessed_ranges _ a = @accessed_ranges _ b
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

Section WithSegs.
Variable segs : list Segment.

#[using="Type"] Lemma interp_eff_accesses_eqv : forall t t', eff_eqv t t' -> forall m,
  ares_eqv (fun cm cm' => core_eqv (fst cm) (fst cm') /\ snd cm = snd cm')
           (interp_eff_accesses segs t m) (interp_eff_accesses segs t' m).
Proof.
  intros t t' H.
  induction H as [c c' Hc | c c' | c c' | c c' | c c' | c c' | n a k k' Hk IH | n a v k k' Hk IH]; intros m;
    cbn [interp_eff_accesses].
  - cbn. auto.
  - exact I.
  - exact I.
  - exact I.
  - exact I.
  - exact I.
  - destruct (ov_read_bytes segs m a (width_bytes n)) as [bs|]; [| destruct (range_meets_vvar segs a (width_bytes n)); exact I].
    specialize (IH (bv_extract 0 n (le_bytes_to_word bs)) m).
    destruct (interp_eff_accesses segs (k _) m) as [rp| |];
      destruct (interp_eff_accesses segs (k' _) m) as [rp'| |]; cbn in *; try tauto.
    destruct IH as [H1 H2]. split; [exact H1|]. rewrite H2. reflexivity.
  - destruct (store_ok segs m a (width_bytes n)); [|exact I].
    specialize (IH (write_to_mem m a (Z_to_le_bytes (width_bytes n) (bv_unsigned v)))).
    destruct (interp_eff_accesses segs k _) as [rp| |];
      destruct (interp_eff_accesses segs k' _) as [rp'| |]; cbn in *; try tauto.
    destruct IH as [H1 H2]. split; [exact H1|]. rewrite H2. reflexivity.
Qed.

#[using="Type"] Lemma ms_reg_eqv : forall ms ms' r, ms_eqv ms ms' -> ms_reg ms r = ms_reg ms' r.
Proof.
  intros ms ms' r (HR & _). unfold ms_reg. destruct (bv_eqb r 0) eqn:E; [reflexivity|].
  apply HR. intros Hz. assert (r = 0%bv) by (apply bv_eq; exact Hz). subst r. rewrite bv_eqb_refl in E. discriminate.
Qed.

#[using="Type"] Lemma decode_exec_accesses_eqv : forall ms ms' w, ms_eqv ms ms' ->
  ares_eqv ms_eqv (decode_exec_accesses segs ms w) (decode_exec_accesses segs ms' w).
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
    destruct K as [[(H1 & H2 & H3 & H4 & H5) Hmm] Hacc]. subst. repeat split; simpl; auto.
Qed.

#[using="Type"] Lemma step_accesses_eqv : forall ms ms', ms_eqv ms ms' ->
  ares_eqv ms_eqv (step_accesses segs ms) (step_accesses segs ms').
Proof.
  intros ms ms' Heqv. pose proof Heqv as (_ & _ & Hpc & _ & _ & _ & Hm & _).
  unfold step_accesses, ms_pc. rewrite <- Hpc, <- Hm.
  destruct (fetch_word segs (ms_pc_val ms)); [apply decode_exec_accesses_eqv; exact Heqv|].
  destruct (fetch_word_ov segs (ms_mem ms) (ms_pc_val ms)); [apply decode_exec_accesses_eqv; exact Heqv|].
  destruct (fetch_tail_any segs (ms_mem ms) (ms_pc_val ms)); [apply decode_exec_accesses_eqv; exact Heqv|].
  (* the revision's [fetch_failure] tests the vDSO text first; every arm is
     a non-[MachineOk] answer on the same pc and memory *)
  unfold fetch_failure.
  repeat match goal with |- context [if ?b then _ else _] => destruct b end; exact I.
Qed.

#[using="Type"] Lemma step_eqv : forall ms ms', ms_eqv ms ms' ->
  res_eqv (RiscvSemantics.step segs ms) (RiscvSemantics.step segs ms').
Proof.
  intros ms ms' Heqv. unfold RiscvSemantics.step, drop_access_report.
  pose proof (step_accesses_eqv ms ms' Heqv) as K.
  destruct (step_accesses segs ms) as [a| |]; destruct (step_accesses segs ms') as [b| |]; cbn in *; tauto.
Qed.

#[using="Type"] Lemma account_step_eqv : forall ms ms' mo, ms_eqv ms ms' ->
  match mi_account_step segs ms mo, mi_account_step segs ms' mo with
  | MachineOk (a, m1), MachineOk (b, m1') => ms_eqv a b /\ m1 = m1'
  | MachineFault, MachineFault => True
  | MachineUnmodeled, MachineUnmodeled => True
  | _, _ => False
  end.
Proof.
  intros ms ms' mo Heqv. unfold mi_account_step.
  pose proof (step_accesses_eqv ms ms' Heqv) as K.
  destruct (step_accesses segs ms) as [a| |]; destruct (step_accesses segs ms') as [b| |]; cbn in K; try tauto.
  destruct K as [K1 K2]. rewrite K2.
  destruct (materialize_model_accesses mo (accessed_ranges machine_state b)); [split; [exact K1|reflexivity] | exact I].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma ms_gpr_eqv : forall ms ms' k, ms_eqv ms ms' -> (k < 6)%nat -> ms_gpr ms k = ms_gpr ms' k.
Proof.
  intros ms ms' k (HR & _) Hk. unfold ms_gpr. apply HR.
  rewrite Z_to_bv_small; [lia|]. unfold bv_modulus. cbn. lia.
Qed.

#[using="Type"] Lemma syscall_args_eqv : forall ms ms', ms_eqv ms ms' -> syscall_args ms = syscall_args ms'.
Proof.
  intros ms ms' H. unfold syscall_args. rewrite !(ms_gpr_eqv ms ms' _ H) by lia. reflexivity.
Qed.

#[using="Type"] Lemma sys_input_eqv : forall ms ms' x8, ms_eqv ms ms' -> sys_input segs ms x8 = sys_input segs ms' x8.
Proof.
  intros ms ms' x8 Heqv. pose proof (syscall_args_eqv ms ms' Heqv) as Ha.
  destruct ms as [R F pc svc rv fc m ro], ms' as [R' F' pc' svc' rv' fc' m' ro'].
  destruct Heqv as (HR & HF & Hpc & Hsvc & Hrv & Hfc & Hm & Hro); simpl in *; subst.
  unfold sys_input. rewrite Ha. reflexivity.
Qed.

#[using="Type"] Lemma apply_effect_eqv : forall ms ms' eff, ms_eqv ms ms' ->
  ms_eqv (apply_effect ms eff) (apply_effect ms' eff).
Proof.
  intros [R F pc svc rv fc m ro] [R' F' pc' svc' rv' fc' m' ro'] eff
         (HR & HF & Hpc & Hsvc & Hrv & Hfc & Hm & Hro); simpl in *; subst.
  unfold apply_effect, set_reg; simpl. repeat split; simpl; auto using regs_eqv_set, iregs_eqv_set.
Qed.

#[using="Type"] Lemma advance_past_svc_eqv : forall ms ms', ms_eqv ms ms' ->
  ms_eqv (advance_past_svc ms) (advance_past_svc ms').
Proof.
  intros [R F pc svc rv fc m ro] [R' F' pc' svc' rv' fc' m' ro']
         (HR & HF & Hpc & Hsvc & Hrv & Hfc & Hm & Hro); simpl in *; subst.
  unfold advance_past_svc, ms_pc; simpl. repeat split; auto.
Qed.

Definition cfg_eqv (c c' : config) : Prop :=
  ms_eqv (cfg_ms c) (cfg_ms c') /\ cfg_model c = cfg_model c'.

#[using="Type"] Lemma cfg_eqv_refl : forall c, cfg_eqv c c.
Proof. intros c. split; [apply ms_eqv_refl | reflexivity]. Qed.
#[using="Type"] Lemma cfg_eqv_sym : forall c c', cfg_eqv c c' -> cfg_eqv c' c.
Proof. intros c c' [H1 H2]. split; [apply ms_eqv_sym; exact H1| congruence]. Qed.

Definition to_eqv (X X' : step_to) : Prop :=
  match X, X' with
  | SError, SError => True
  | SNext c, SNext c' => cfg_eqv c c'
  | _, _ => False
  end.

(* ================================================================= *)
(* The vDSO call arms (LPS 08b1429, #61): [Run.sstep] gained          *)
(* [sstep_vdso_call], [sstep_vdso_materialization_fault] and          *)
(* [sstep_vdso_unmodeled] between the [*_instr] arms and              *)
(* [sstep_syscall].  Everything the three read off the machine state  *)
(* — the pc, the caller-saved registers, the frame below sp and the   *)
(* memory — is fixed by [ms_eqv], so a vDSO step of one state is a    *)
(* vDSO step of any equivalent state, and the states it leaves are    *)
(* equivalent again.                                                  *)
(* ================================================================= *)

#[using="Type"] Lemma ms_sp_eqv : forall ms ms', ms_eqv ms ms' -> ms_sp ms = ms_sp ms'.
Proof.
  intros ms ms' (HR & _). unfold ms_sp. apply HR.
  cbn. intro Hz. discriminate Hz.
Qed.

#[using="Type"] Lemma ms_read_byte_eqv : forall ms ms', ms_eqv ms ms' ->
  ms_read_byte ms = ms_read_byte ms'.
Proof.
  intros ms ms' (_ & _ & _ & _ & _ & _ & Hm & Hro).
  unfold ms_read_byte. rewrite Hm, Hro. reflexivity.
Qed.

#[using="Type"] Lemma vdso_read_regs_eqv : forall ms ms', ms_eqv ms ms' ->
  vdso_read_regs ms = vdso_read_regs ms'.
Proof.
  intros ms ms' Heqv. unfold vdso_read_regs.
  apply map_ext. intro r. apply ms_reg_eqv. exact Heqv.
Qed.

#[using="Type"] Lemma set_reg_eqv : forall ms ms' r v, ms_eqv ms ms' ->
  ms_eqv (set_reg ms r v) (set_reg ms' r v).
Proof.
  intros ms ms' r v Heqv.
  pose proof Heqv as (HR & HF & Hpc & Hsvc & Hrv & Hfc & Hm & Hro).
  unfold set_reg. destruct (bv_eqb r 0); [exact Heqv|].
  repeat split; cbn; auto using iregs_eqv_set.
Qed.

#[using="Type"] Lemma vdso_write_regs_eqv : forall rs vs ms ms', ms_eqv ms ms' ->
  ms_eqv (vdso_write_regs ms rs vs) (vdso_write_regs ms' rs vs).
Proof.
  induction rs as [|r rs IH]; intros vs ms ms' Heqv; [exact Heqv|].
  destruct vs as [|v vs]; cbn; [exact Heqv|].
  apply IH. apply set_reg_eqv. exact Heqv.
Qed.

#[using="Type"] Lemma vdso_with_mem_eqv : forall ms ms' m, ms_eqv ms ms' ->
  ms_eqv (vdso_with_mem ms m) (vdso_with_mem ms' m).
Proof.
  intros ms ms' m (HR & HF & Hpc & Hsvc & Hrv & Hfc & Hm & Hro).
  unfold vdso_with_mem. repeat split; cbn; auto.
Qed.

#[using="Type"] Lemma vdso_set_pc_eqv : forall ms ms' pc, ms_eqv ms ms' ->
  ms_eqv (vdso_set_pc ms pc) (vdso_set_pc ms' pc).
Proof.
  intros ms ms' pc (HR & HF & Hpc & Hsvc & Hrv & Hfc & Hm & Hro).
  unfold vdso_set_pc. repeat split; cbn; auto.
Qed.

#[using="Type"] Lemma vdso_post_eqv : forall ms ms' model f eff, ms_eqv ms ms' ->
  ms_eqv (vdso_post segs ms model f eff) (vdso_post segs ms' model f eff).
Proof.
  intros ms ms' model f eff Heqv.
  unfold vdso_post. cbv zeta.
  rewrite (ms_reg_eqv ms ms' 1 Heqv), (ms_sp_eqv ms ms' Heqv),
          (vdso_read_regs_eqv ms ms' Heqv), (ms_read_byte_eqv ms ms' Heqv).
  pose proof (vdso_write_regs_eqv vdso_caller_saved
                (vl_regs (vdr_draw (m_vdso model) (vdr_calls (m_vdso model))
                   (vdso_read_regs ms')
                   (vdso_read_frame (ms_read_byte ms')
                      (ms_sp ms' - Z_to_bv 64 (Z.of_N f)) (N.to_nat f))
                   (eff_ret eff))) ms ms' Heqv) as H1.
  pose proof H1 as (_ & _ & _ & _ & _ & _ & Hm1 & _).
  apply vdso_set_pc_eqv, apply_effect_eqv.
  rewrite Hm1. apply vdso_with_mem_eqv. exact H1.
Qed.

#[using="Type"] Lemma vdso_call_unmodeled_eqv : forall ms ms' model fn, ms_eqv ms ms' ->
  vdso_call_unmodeled segs ms model fn -> vdso_call_unmodeled segs ms' model fn.
Proof.
  intros ms ms' model fn Heqv H.
  assert (Hsi : forall x8, sys_input segs ms' x8 = sys_input segs ms x8)
    by (intro x8; symmetry; exact (sys_input_eqv ms ms' x8 Heqv)).
  destruct H as [H | [(n & Hn & Hspec) | (n & eff & model' & evs & Hn & Hspec & Hor)]].
  - left; exact H.
  - right; left. exists n. split; [exact Hn | rewrite Hsi; exact Hspec].
  - right; right. exists n, eff, model', evs.
    split; [exact Hn | split; [rewrite Hsi; exact Hspec | exact Hor]].
Qed.

#[using="Type"] Lemma sstep_eqv : forall ms ms' mo evs X, ms_eqv ms ms' ->
  sstep segs (mkCfg ms mo) evs X ->
  exists X', sstep segs (mkCfg ms' mo) evs X' /\ to_eqv X X'.
Proof.
  intros ms ms' mo evs X Heqv Hst.
  pose proof (account_step_eqv ms ms' mo Heqv) as Hres.
  pose proof Heqv as (_ & _ & Hpceq & Hsvc & _ & _ & _ & _).
  inversion Hst; subst.
  - (* [comment removed for export] *)
    match goal with Hacc : mi_account_step segs ms mo = _ |- _ => rewrite Hacc in Hres end. destruct (mi_account_step segs ms' mo) as [[ms1' mo1']| |] eqn:E; simpl in Hres; try contradiction.
    destruct Hres as [Hres ->].
    exists (SNext (mkCfg ms1' mo1')). split; [apply sstep_instr; auto; congruence|]. split; [exact Hres| reflexivity].
  - match goal with Hacc : mi_account_step segs ms mo = _ |- _ => rewrite Hacc in Hres end. destruct (mi_account_step segs ms' mo) as [[ms1' mo1']| |] eqn:E; simpl in Hres; try contradiction.
    exists SError. split; [apply sstep_instr_fault; auto; congruence| exact I].
  - match goal with Hacc : mi_account_step segs ms mo = _ |- _ => rewrite Hacc in Hres end. destruct (mi_account_step segs ms' mo) as [[ms1' mo1']| |] eqn:E; simpl in Hres; try contradiction.
    exists SError. split; [| exact I].
    (* the revision's [sstep_instr_unmodeled] also asks that the pc is NOT an
       exported vDSO entry; the two states share a pc *)
    eapply sstep_instr_unmodeled;
      [ eassumption
      | congruence
      | exact E
      | replace (ms_pc ms') with (ms_pc ms) by (unfold ms_pc; congruence);
        eassumption ].
  - (* sstep_vdso_call: the model declines the instruction and the pc is an
       exported vDSO entry; everything the arm reads is fixed by [ms_eqv] *)
    match goal with Hacc : mi_account_step segs ms mo = _ |- _ => rewrite Hacc in Hres end.
    destruct (mi_account_step segs ms' mo) as [[ms1' mo1']| |] eqn:E; simpl in Hres; try contradiction.
    eexists. split.
    + eapply sstep_vdso_call;
        [ eassumption
        | congruence
        | exact E
        | replace (ms_pc ms') with (ms_pc ms)
            by (unfold ms_pc; congruence);
          eassumption
        | eassumption
        | rewrite (sys_input_eqv ms' ms _ (ms_eqv_sym ms ms' Heqv)); eassumption
        | eassumption
        | eassumption
        | eassumption ].
    + split; [apply vdso_post_eqv; exact Heqv | reflexivity].
  - (* sstep_vdso_materialization_fault *)
    match goal with Hacc : mi_account_step segs ms mo = _ |- _ => rewrite Hacc in Hres end.
    destruct (mi_account_step segs ms' mo) as [[ms1' mo1']| |] eqn:E; simpl in Hres; try contradiction.
    exists SError. split; [| exact I].
    eapply sstep_vdso_materialization_fault;
      [ eassumption
      | congruence
      | exact E
      | replace (ms_pc ms') with (ms_pc ms)
          by (unfold ms_pc; congruence);
        eassumption
      | eassumption
      | rewrite (sys_input_eqv ms' ms _ (ms_eqv_sym ms ms' Heqv)); eassumption
      | eassumption
      | eassumption
      | eassumption ].
  - (* sstep_vdso_unmodeled *)
    match goal with Hacc : mi_account_step segs ms mo = _ |- _ => rewrite Hacc in Hres end.
    destruct (mi_account_step segs ms' mo) as [[ms1' mo1']| |] eqn:E; simpl in Hres; try contradiction.
    exists SError. split; [| exact I].
    eapply sstep_vdso_unmodeled;
      [ eassumption
      | congruence
      | exact E
      | replace (ms_pc ms') with (ms_pc ms)
          by (unfold ms_pc; congruence);
        eassumption
      | eapply vdso_call_unmodeled_eqv; [exact Heqv | eassumption] ].
  - (* [comment removed for export] *)
    exists (SNext (mkCfg (advance_past_svc (apply_effect ms' eff)) model'')). split.
    + apply (sstep_syscall segs ms' mo x8 eff model' model'' evs);
        [assumption| congruence| rewrite <- (sys_input_eqv ms ms' x8 Heqv); assumption| assumption | assumption].
    + split; [| reflexivity]. apply advance_past_svc_eqv, apply_effect_eqv, Heqv.
  - (* [comment removed for export] *)
    exists SError. split; [|exact I].
    apply (sstep_syscall_materialization_fault segs ms' mo x8 eff model' evs0);
      [assumption| congruence| rewrite <- (sys_input_eqv ms ms' x8 Heqv); assumption| assumption | assumption].
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

#[using="Type"] Lemma sstep_cfg_eqv : forall c c' evs X, cfg_eqv c c' ->
  sstep segs c evs X -> exists X', sstep segs c' evs X' /\ to_eqv X X'.
Proof.
  intros [ms mo] [ms' mo'] evs X [Hms Hmo] Hst; simpl in Hms, Hmo; subst.
  apply (sstep_eqv ms ms'); assumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* node_ok's third conjunct ([RomBase.sys_rob]) transfers along [cfg_eqv]: the system-call input
   reads only what [ms_eqv] keeps equal ([sys_input_eqv]), on the state and on its larger backing. *)
#[using="Type"] Lemma sys_rob_eqv : forall c c', cfg_eqv c c' -> RomBase.sys_rob segs c -> RomBase.sys_rob segs c'.
Proof.
  intros [ms mo] [ms' mo'] [Hms Hmo] H r x8 Hr Hs o.
  cbn [cfg_ms cfg_model] in *. subst mo'.
  pose proof Hms as (HR & HF & Hpc & Hsvc & Hrv & Hfc & Hm & Hro).
  assert (Hw : ms_eqv (RomBase.wrom ms r) (RomBase.wrom ms' r)).
  { unfold ms_eqv, RomBase.wrom; cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom].
    repeat split; first [assumption | reflexivity]. }
  rewrite <- (sys_input_eqv _ _ x8 Hw), <- (sys_input_eqv _ _ x8 Hms).
  apply (H r x8); cbn [cfg_ms]; [rewrite Hro; exact Hr | rewrite Hsvc; exact Hs].
Qed.

#[using="Type"] Lemma realizes_eqv : forall c T, realizes segs c T -> forall c', cfg_eqv c c' -> realizes segs c' T.
Proof.
  intros c T H. induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh | c T T' H IH Heq]; intros c' Heqv.
  - (* [comment removed for export] *)
    destruct Hnode as [Hcomp [Hsound Hrob]].
    set (I' := { p : I * config | sstep segs c' (evs (fst p)) (SNext (snd p)) /\ cfg_eqv (nx (fst p)) (snd p) }).
    assert (Hfib : forall i, exists X', sstep segs c' (evs i) (SNext X') /\ cfg_eqv (nx i) X').
    { intros i. destruct (sstep_cfg_eqv c c' (evs i) (SNext (nx i)) Heqv (Hcomp i)) as (X' & Hs & HX).
      destruct X' as [c''|]; cbn in HX; [|contradiction]. exists c''. split; assumption. }
    destruct (Hfib i0) as (X0 & HX0s & HX0e).
    apply (rz_conseq segs c' (t_alt (fun p : I' => t_emit (evs (fst (proj1_sig p))) (T (fst (proj1_sig p)))))).
    + apply (rz_node segs c' I' (fun p => evs (fst (proj1_sig p))) (fun p => snd (proj1_sig p))
               (fun p => T (fst (proj1_sig p))) (exist _ (i0, X0) (conj HX0s HX0e))).
      * split; [|split].
        -- intros [[i X] [Hs HX]]. cbn. exact Hs.
        -- intros e st Hs.
           destruct (sstep_cfg_eqv c' c e st (cfg_eqv_sym _ _ Heqv) Hs) as (X & HsX & HX).
           destruct (Hsound e X HsX) as (i & -> & ->).
           destruct st as [c''|]; cbn in HX; [|contradiction].
           exists (exist _ (i, c'') (conj Hs (cfg_eqv_sym _ _ HX))). cbn. split; reflexivity.
        -- exact (sys_rob_eqv c c' Heqv Hrob).
      * intros [[i X] [Hs HX]]. cbn. apply (IH i). exact HX.
    + intros tr. split.
      * intros [[[i X] [Hs HX]] Htr]. cbn in Htr. exists i. exact Htr.
      * intros [i Htr]. destruct (Hfib i) as (X & Hs & HX).
        exists (exist _ (i, X) (conj Hs HX)). cbn. exact Htr.
  - apply rz_halt. unfold halted_ok in *. destruct Heqv as [_ <-]. exact Hh.
  - eapply rz_conseq; [apply IH; exact Heqv | exact Heq].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma realizes_ms_ext : forall (R R' F F' : bvmap 5 word) pc svc rv fc mem rom mo T,
  (forall r : reg, bv_unsigned r <> 0%Z -> reg_get R r = reg_get R' r) ->
  (forall r, reg_get F r = reg_get F' r) ->
  realizes segs (mkCfg {| ms_regs := R; ms_fregs := F; ms_pc_val := pc; ms_svc_pending := svc;
                          ms_resv := rv; ms_fcsr := fc; ms_mem := mem; ms_rom := rom |} mo) T ->
  realizes segs (mkCfg {| ms_regs := R'; ms_fregs := F'; ms_pc_val := pc; ms_svc_pending := svc;
                          ms_resv := rv; ms_fcsr := fc; ms_mem := mem; ms_rom := rom |} mo) T.
Proof.
  intros R R' F F' pc svc rv fc mem rom mo T HR HF H.
  eapply realizes_eqv; [exact H|]. split; [|reflexivity]. cbn. repeat split; auto.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma realizes_regs_ext0 : forall {fx : FPState} (R R' : bvmap 5 word) pc mem rom mo T,
  (forall r : reg, bv_unsigned r <> 0%Z -> reg_get R r = reg_get R' r) ->
  realizes segs (mkCfg (mkst R pc mem rom) mo) T ->
  realizes segs (mkCfg (mkst R' pc mem rom) mo) T.
Proof.
  intros fx R R' pc mem rom mo T HR H.
  eapply realizes_eqv; [exact H|]. split; [|reflexivity]. cbn. repeat split; auto; intros r; reflexivity.
Qed.

#[using="Type"] Lemma realizes_regs_ext : forall {fx : FPState} (R R' : bvmap 5 word) pc mem rom mo T,
  (forall r, reg_get R r = reg_get R' r) ->
  realizes segs (mkCfg (mkst R pc mem rom) mo) T ->
  realizes segs (mkCfg (mkst R' pc mem rom) mo) T.
Proof.
  intros fx R R' pc mem rom mo T HR H. eapply realizes_regs_ext0; [|exact H]. intros r _. apply HR.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma realizes_getr_ext : forall {fx : FPState} (R R' : bvmap 5 word) pc mem rom mo T,
  (forall r : reg, getr R r = getr R' r) ->
  realizes segs (mkCfg (mkst R pc mem rom) mo) T ->
  realizes segs (mkCfg (mkst R' pc mem rom) mo) T.
Proof.
  intros fx R R' pc mem rom mo T HR H. eapply realizes_regs_ext0; [|exact H].
  intros r Hr. specialize (HR r). unfold getr in HR.
  destruct (bv_eqb r 0) eqn:E; [|exact HR].
  exfalso. apply Hr. unfold bv_eqb in E. apply Z.eqb_eq in E. exact E.
Qed.

End WithSegs.
