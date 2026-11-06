(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: the srz_spin cases of the two srealizes_eqv proofs are closed by the proof of False that srz_spin now takes (lib/Common/SpinAlg.v). *)
(* [comment removed for export] *)
From Stdlib Require Lia.
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require PropExec MState Frame.
From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AsanHexScan__Common.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AllocSim2__Common.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require PropExec__Common.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require SpinAlg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Module RegsEqv0.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState Frame.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition regs_eqv (R R' : bvmap 5 word) : Prop := forall r, reg_get R r = reg_get R' r.
(* [comment removed for export] *)
Definition regs_eqv0 (R R' : bvmap 5 word) : Prop := forall r, is_x0 r = false -> reg_get R r = reg_get R' r.

Lemma regs_eqv_refl : forall R, regs_eqv R R.
Proof. intros R r. reflexivity. Qed.
Lemma regs_eqv_sym : forall R R', regs_eqv R R' -> regs_eqv R' R.
Proof. intros R R' H r. symmetry. apply H. Qed.
Lemma regs_eqv_trans : forall R1 R2 R3, regs_eqv R1 R2 -> regs_eqv R2 R3 -> regs_eqv R1 R3.
Proof. intros R1 R2 R3 H1 H2 r. etransitivity; [apply H1|apply H2]. Qed.
Lemma regs_eqv0_refl : forall R, regs_eqv0 R R.
Proof. intros R r _. reflexivity. Qed.
Lemma regs_eqv0_sym : forall R R', regs_eqv0 R R' -> regs_eqv0 R' R.
Proof. intros R R' H r Hr. symmetry. apply H, Hr. Qed.
Lemma regs_eqv0_trans : forall R1 R2 R3, regs_eqv0 R1 R2 -> regs_eqv0 R2 R3 -> regs_eqv0 R1 R3.
Proof. intros R1 R2 R3 H1 H2 r Hr. etransitivity; [apply H1, Hr|apply H2, Hr]. Qed.
Lemma regs_eqv_eqv0 : forall R R', regs_eqv R R' -> regs_eqv0 R R'.
Proof. intros R R' H r _. apply H. Qed.
(* [comment removed for export] *)
Lemma rget_if_eqv0 : forall R R', regs_eqv0 R R' -> forall r,
  (if is_x0 r then w0 else reg_get R r) = (if is_x0 r then w0 else reg_get R' r).
Proof. intros R R' H r. destruct (is_x0 r) eqn:E; [reflexivity| apply H, E]. Qed.
Lemma is_x0_lit : forall z, (1 <= z < 32)%Z -> is_x0 (Z_to_bv 5 z) = false.
Proof. intros z Hz. unfold is_x0. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn [Z.pow_pos Pos.iter Z.mul Pos.mul]. rewrite Z.mod_small by lia. apply Z.eqb_neq. lia. Qed.

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
Lemma regs_eqv0_set : forall R R' (k : reg) v,
  regs_eqv0 R R' -> regs_eqv0 (bvmap_set k v R) (bvmap_set k v R').
Proof. intros R R' k v H r Hr. rewrite !reg_get_set. destruct (bv_eqb k r); [reflexivity|apply H, Hr]. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition core_eqv (c c' : core) : Prop :=
  regs_eqv0 (c_regs c) (c_regs c') /\ regs_eqv (c_fregs c) (c_fregs c') /\
  c_pc c = c_pc c' /\ c_fcsr c = c_fcsr c' /\ c_resv c = c_resv c'.

(* [comment removed for export] *)
Inductive eff_eqv : eff -> eff -> Prop :=
| EqvDone : forall c c', core_eqv c c' -> eff_eqv (EDone c) (EDone c')
| EqvIllegal : forall c c', eff_eqv (EIllegal c) (EIllegal c')
| EqvDefIllegal : forall c c', eff_eqv (EDefinedIllegal c) (EDefinedIllegal c')   (* [comment removed for export] *)
| EqvEcall : forall c c', eff_eqv (EEcall c) (EEcall c')
| EqvEbreak : forall c c', eff_eqv (EEbreak c) (EEbreak c')
| EqvFault : forall c c', eff_eqv (EFault c) (EFault c')
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
    | apply EqvIllegal | apply EqvDefIllegal | apply EqvEcall | apply EqvEbreak | apply EqvFault
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
  intros R R' F F' pc fc rv sz i HR HF.
  destruct i; unfold_exec; rewrite ?(rget_if_eqv0 R R' HR), ?HF; eqv_struct HR HF.
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
Proof. intros ms. repeat split; first [apply regs_eqv0_refl | apply regs_eqv_refl]. Qed.
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

Section WithSegs.
Variable segs : list Segment.

(* [comment removed for export] *)
#[using="Type"] Lemma interp_eff_accesses_eqv : forall t t', eff_eqv t t' -> forall m,
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
  intros t t' H. induction H; intros m; cbn [interp_eff_accesses access_value accessed_ranges fst snd]; auto.
  - destruct (ov_read_bytes segs m a (width_bytes n)) as [bs|]; [|exact I].
    specialize (H0 (bv_extract 0 n (le_bytes_to_word bs)) m).
    destruct (interp_eff_accesses segs (k _) m) as [rep| |]; destruct (interp_eff_accesses segs (k' _) m) as [rep'| |];
      cbn [access_value accessed_ranges] in *; try exact H0; try contradiction.
    destruct H0 as (H1 & H2 & H3). rewrite H3. auto.
  - destruct (store_ok segs m a (width_bytes n)); [|exact I].
    specialize (IHeff_eqv (write_to_mem m a (Z_to_le_bytes (width_bytes n) (bv_unsigned v)))).
    destruct (interp_eff_accesses segs k _) as [rep| |]; destruct (interp_eff_accesses segs k' _) as [rep'| |];
      cbn [access_value accessed_ranges] in *; try exact IHeff_eqv; try contradiction.
    destruct IHeff_eqv as (H1 & H2 & H3). rewrite H3. auto.
Qed.

#[using="Type"] Lemma ms_reg_eqv : forall ms ms' r, ms_eqv ms ms' -> ms_reg ms r = ms_reg ms' r.
Proof.
  intros ms ms' r (HR & _). unfold ms_reg. destruct (bv_eqb r 0) eqn:E; [reflexivity|].
  apply HR. unfold is_x0. apply Z.eqb_neq. intros Hz. apply Bool.not_true_iff_false in E. apply E.
  apply bv_eqb_eq. apply bv_eq. rewrite Hz. reflexivity.
Qed.

Definition ares_eqv (r r' : machine_result (access_report machine_state)) : Prop :=
  match r, r' with
  | MachineOk rep, MachineOk rep' =>
      ms_eqv (access_value _ rep) (access_value _ rep') /\ accessed_ranges _ rep = accessed_ranges _ rep'
  | MachineFault, MachineFault => True
  | MachineUnmodeled, MachineUnmodeled => True
  | _, _ => False
  end.

#[using="Type"] Lemma decode_exec_accesses_eqv : forall ms ms' w, ms_eqv ms ms' ->
  ares_eqv (decode_exec_accesses segs ms w) (decode_exec_accesses segs ms' w).
Proof.
  intros ms ms' w Heqv. pose proof (ms_reg_eqv ms ms' 17 Heqv) as H17.
  destruct ms as [R F pc svc rv fc m ro], ms' as [R' F' pc' svc' rv' fc' m' ro'].
  destruct Heqv as (HR & HF & Hpc & Hsvc & Hrv & Hfc & Hm & Hro); simpl in *; subst.
  unfold decode_exec_accesses. destruct (is_ecall w).
  - simpl. rewrite H17. repeat split; assumption.
  - destruct (decode_any w) as [[i isz]|]; [| destruct (is_defined_illegal w); exact I]. simpl.
    pose proof (interp_eff_accesses_eqv _ _ (exec_eqv_core R R' F F' pc' fc' rv' (Z_to_bv 64 isz) i HR HF) m') as K.
    destruct (interp_eff_accesses segs (exec _ i (Core R F pc' fc' rv')) m') as [[[c m1] rs]| |];
    destruct (interp_eff_accesses segs (exec _ i (Core R' F' pc' fc' rv')) m') as [[[c' m1'] rs']| |];
    simpl in *; try exact K; try contradiction.
    destruct K as ((H1 & H2 & H3 & H4 & H5) & -> & ->). repeat split; simpl; auto.
Qed.

#[using="Type"] Lemma step_accesses_eqv : forall ms ms', ms_eqv ms ms' ->
  ares_eqv (RiscvSemantics.step_accesses segs ms) (RiscvSemantics.step_accesses segs ms').
Proof.
  intros ms ms' Heqv. pose proof Heqv as (_ & _ & Hpc & _ & _ & _ & Hm & _).
  unfold RiscvSemantics.step_accesses, ms_pc. rewrite <- Hpc, <- Hm.
  destruct (fetch_word segs (ms_pc_val ms)); [apply decode_exec_accesses_eqv; exact Heqv|].
  destruct (fetch_word_ov segs (ms_mem ms) (ms_pc_val ms)); [apply decode_exec_accesses_eqv; exact Heqv|].
  destruct (fetch_tail_any segs (ms_mem ms) (ms_pc_val ms)); [apply decode_exec_accesses_eqv; exact Heqv|].
  unfold fetch_failure. destruct (negb _); [exact I|]. destruct (_ || _)%bool; exact I.
Qed.

Definition res_eqv (r r' : machine_result machine_state) : Prop :=
  match r, r' with
  | MachineOk a, MachineOk b => ms_eqv a b
  | MachineFault, MachineFault => True
  | MachineUnmodeled, MachineUnmodeled => True
  | _, _ => False
  end.

#[using="Type"] Lemma step_eqv : forall ms ms', ms_eqv ms ms' ->
  res_eqv (RiscvSemantics.step segs ms) (RiscvSemantics.step segs ms').
Proof.
  intros ms ms' Heqv. pose proof (step_accesses_eqv ms ms' Heqv) as H.
  unfold RiscvSemantics.step, drop_access_report.
  destruct (RiscvSemantics.step_accesses segs ms) as [rep| |]; destruct (RiscvSemantics.step_accesses segs ms') as [rep'| |];
    cbn in H; try exact H; try contradiction. exact (proj1 H).
Qed.

(* [comment removed for export] *)
Definition mres_eqv (r r' : machine_result (machine_state * Model)) : Prop :=
  match r, r' with
  | MachineOk (a, mo), MachineOk (b, mo') => ms_eqv a b /\ mo = mo'
  | MachineFault, MachineFault => True
  | MachineUnmodeled, MachineUnmodeled => True
  | _, _ => False
  end.

#[using="Type"] Lemma mi_account_step_eqv : forall ms ms' mo, ms_eqv ms ms' ->
  mres_eqv (mi_account_step segs ms mo) (mi_account_step segs ms' mo).
Proof.
  intros ms ms' mo Heqv. pose proof (step_accesses_eqv ms ms' Heqv) as H.
  unfold mi_account_step.
  destruct (RiscvSemantics.step_accesses segs ms) as [rep| |]; destruct (RiscvSemantics.step_accesses segs ms') as [rep'| |];
    cbn in H; try exact H; try contradiction.
  destruct H as [Hms <-]. destruct (materialize_model_accesses mo (accessed_ranges _ rep)); [|exact I].
  split; [exact Hms|reflexivity].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma syscall_args_eqv : forall ms ms', ms_eqv ms ms' -> syscall_args ms = syscall_args ms'.
Proof.
  intros ms ms' (HR & _). unfold syscall_args, ms_gpr. cbn [Z.of_nat Z.add Pos.of_succ_nat Pos.add Pos.succ].
  rewrite !HR by (apply is_x0_lit; lia). reflexivity.
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
  unfold apply_effect, set_reg; simpl. repeat split; simpl; auto using regs_eqv0_set.
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

#[using="Type"] Lemma cfg_eqv_sym : forall c c', cfg_eqv c c' -> cfg_eqv c' c.
Proof. intros c c' [H1 H2]. split; [apply ms_eqv_sym; exact H1| congruence]. Qed.

Definition to_eqv (X X' : step_to) : Prop :=
  match X, X' with
  | SError, SError => True
  | SNext c, SNext c' => cfg_eqv c c'
  | _, _ => False
  end.

#[using="Type"] Lemma sstep_eqv : forall ms ms' mo evs X, ms_eqv ms ms' ->
  sstep segs (mkCfg ms mo) evs X ->
  exists X', sstep segs (mkCfg ms' mo) evs X' /\ to_eqv X X'.
Proof.
  intros ms ms' mo evs X Heqv Hst.
  pose proof (mi_account_step_eqv ms ms' mo Heqv) as Hres.
  pose proof Heqv as (_ & _ & _ & Hsvc & _ & _ & _ & _).
  inversion Hst; subst.
  - (* [comment removed for export] *)
    rewrite H5 in Hres. destruct (mi_account_step segs ms' mo) as [[ms1' mo1']| |] eqn:E; simpl in Hres; try contradiction.
    destruct Hres as [Hms <-].
    exists (SNext (mkCfg ms1' model')). split; [apply sstep_instr; auto; congruence|]. split; [exact Hms| reflexivity].
  - rewrite H5 in Hres. destruct (mi_account_step segs ms' mo) as [[ms1' mo1']| |] eqn:E; simpl in Hres; try contradiction.
    exists SError. split; [apply sstep_instr_fault; auto; congruence| exact I].
  - rewrite H5 in Hres. destruct (mi_account_step segs ms' mo) as [[ms1' mo1']| |] eqn:E; simpl in Hres; try contradiction.
    exists SError. split; [apply sstep_instr_unmodeled; auto; congruence| exact I].
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

#[using="Type"] Lemma sstep_cfg_eqv : forall c c' evs X, cfg_eqv c c' ->
  sstep segs c evs X -> exists X', sstep segs c' evs X' /\ to_eqv X X'.
Proof.
  intros [ms mo] [ms' mo'] evs X [Hms Hmo] Hst; simpl in Hms, Hmo; subst.
  apply (sstep_eqv ms ms'); assumption.
Qed.

#[using="Type"] Lemma star_eqv : forall c tr c1, star segs c tr c1 ->
  forall c', cfg_eqv c c' -> exists c1', star segs c' tr c1' /\ cfg_eqv c1 c1'.
Proof.
  intros c tr c1 H. induction H as [c | c evs c2 tr c3 Hst Hstar IH]; intros c' Heqv.
  - exists c'. split; [apply star_refl| exact Heqv].
  - destruct (sstep_cfg_eqv c c' evs (SNext c2) Heqv Hst) as (X' & Hst' & HX).
    destruct X' as [c2'|]; simpl in HX; [|contradiction].
    destruct (IH c2' HX) as (c3' & Hstar' & H3).
    exists c3'. split; [eapply star_step; eassumption| exact H3].
Qed.

#[using="Type"] Lemma obs_trace_eqv : forall c c' tr, cfg_eqv c c' -> obs_trace segs c tr -> obs_trace segs c' tr.
Proof.
  intros c c' tr Heqv (tr' & c1 & Hstar & Hp).
  destruct (star_eqv c tr' c1 Hstar c' Heqv) as (c1' & Hstar' & _).
  exists tr', c1'. split; assumption.
Qed.

#[using="Type"] Lemma reaches_error_eqv : forall c c', cfg_eqv c c' -> reaches_error segs c -> reaches_error segs c'.
Proof.
  intros c c' Heqv (tr & c1 & evs & Hstar & Hst).
  destruct (star_eqv c tr c1 Hstar c' Heqv) as (c1' & Hstar' & H1).
  destruct (sstep_cfg_eqv c1 c1' evs SError H1 Hst) as (X' & Hst' & HX).
  destruct X'; simpl in HX; [contradiction|].
  exists tr, c1', evs. split; assumption.
Qed.

#[using="Type"] Lemma unmodeled_at_eqv : forall c c', cfg_eqv c c' -> unmodeled_at segs c -> unmodeled_at segs c'.
Proof.
  intros [ms mo] [ms' mo'] [Hms Hmo] Hun; simpl in Hms, Hmo; subst.
  unfold unmodeled_at in *. cbn [cfg_ms cfg_model] in *. destruct Hun as (Hh & Hcase).
  pose proof Hms as (_ & _ & _ & Hsvc & _ & _ & _ & _).
  split; [exact Hh|]. destruct Hcase as [(Hnone & Hstep) | (x8 & Hsome & Hspec)].
  - left. split; [congruence|].
    pose proof (mi_account_step_eqv ms ms' mo' Hms) as Hres. rewrite Hstep in Hres.
    destruct (mi_account_step segs ms' mo') as [[? ?]| |]; simpl in Hres; try contradiction. reflexivity.
  - right. exists x8. split; [congruence|]. rewrite <- (sys_input_eqv ms ms' x8 Hms). exact Hspec.
Qed.

#[using="Type"] Lemma reaches_unmodeled_eqv : forall c c', cfg_eqv c c' ->
  reaches_unmodeled segs c -> reaches_unmodeled segs c'.
Proof.
  intros c c' Heqv (tr & c1 & Hstar & Hun).
  destruct (star_eqv c tr c1 Hstar c' Heqv) as (c1' & Hstar' & H1).
  exists tr, c1'. split; [exact Hstar'| eapply unmodeled_at_eqv; eassumption].
Qed.

#[using="Type"] Lemma all_traces_error_eqv : forall c, all_traces_error segs c ->
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
#[using="Type"] Theorem behaviour_eqv : forall ms ms' mo, ms_eqv ms ms' ->
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

(* [comment removed for export] *)
Section WithCfg.
Variable cfg : SpuriousCfg.

#[using="Type"] Lemma sstepC_eqv : forall ms ms' mo evs X, ms_eqv ms ms' ->
  sstep_cfg segs cfg (mkCfg ms mo) evs X ->
  exists X', sstep_cfg segs cfg (mkCfg ms' mo) evs X' /\ to_eqv X X'.
Proof.
  intros ms ms' mo evs X Heqv Hst.
  pose proof (mi_account_step_eqv ms ms' mo Heqv) as Hres.
  pose proof Heqv as (_ & _ & _ & Hsvc & _ & _ & _ & _).
  inversion Hst; subst.
  - rewrite H5 in Hres. destruct (mi_account_step segs ms' mo) as [[ms1' mo1']| |] eqn:E; simpl in Hres; try contradiction.
    destruct Hres as [Hms <-].
    exists (SNext (mkCfg ms1' model')). split; [apply sstep_cfg_instr; auto; congruence|]. split; [exact Hms| reflexivity].
  - rewrite H5 in Hres. destruct (mi_account_step segs ms' mo) as [[ms1' mo1']| |] eqn:E; simpl in Hres; try contradiction.
    exists SError. split; [apply sstep_cfg_instr_fault; auto; congruence| exact I].
  - rewrite H5 in Hres. destruct (mi_account_step segs ms' mo) as [[ms1' mo1']| |] eqn:E; simpl in Hres; try contradiction.
    exists SError. split; [apply sstep_cfg_instr_unmodeled; auto; congruence| exact I].
  - exists (SNext (mkCfg (advance_past_svc (apply_effect ms' eff)) model'')). split.
    + apply (sstep_cfg_syscall segs cfg ms' mo x8 eff model' model'' evs);
        [assumption| congruence| rewrite <- (sys_input_eqv ms ms' x8 Heqv); assumption
        | rewrite <- (sys_input_eqv ms ms' x8 Heqv); assumption | assumption| assumption].
    + split; [| reflexivity]. apply advance_past_svc_eqv, apply_effect_eqv, Heqv.
  - exists SError. split; [|exact I].
    apply (sstep_cfg_syscall_materialization_fault segs cfg ms' mo x8 eff model' evs0);
      [assumption| congruence| rewrite <- (sys_input_eqv ms ms' x8 Heqv); assumption
      | rewrite <- (sys_input_eqv ms ms' x8 Heqv); assumption | assumption| assumption].
  - exists (SNext (mkCfg ms' model')). split.
    + apply (sstep_cfg_exit segs cfg ms' mo x8 eff model' evs0 code);
        [assumption| congruence| rewrite <- (sys_input_eqv ms ms' x8 Heqv); assumption| assumption| assumption].
    + split; [exact Heqv| reflexivity].
  - exists (SNext (mkCfg ms' model')). split.
    + apply (sstep_cfg_killed segs cfg ms' mo x8 eff model' evs0 sig);
        [assumption| congruence| rewrite <- (sys_input_eqv ms ms' x8 Heqv); assumption| assumption].
    + split; [exact Heqv| reflexivity].
  - exists SError. split; [|exact I].
    apply (sstep_cfg_syscall_unmodeled segs cfg ms' mo x8);
      [assumption| congruence| rewrite <- (sys_input_eqv ms ms' x8 Heqv); assumption].
Qed.

#[using="Type"] Lemma sstepC_cfg_eqv : forall c c' evs X, cfg_eqv c c' ->
  sstep_cfg segs cfg c evs X -> exists X', sstep_cfg segs cfg c' evs X' /\ to_eqv X X'.
Proof.
  intros [ms mo] [ms' mo'] evs X [Hms Hmo] Hst; simpl in Hms, Hmo; subst.
  apply (sstepC_eqv ms ms'); assumption.
Qed.

#[using="Type"] Lemma starC_eqv : forall c tr c1, star_cfg segs cfg c tr c1 ->
  forall c', cfg_eqv c c' -> exists c1', star_cfg segs cfg c' tr c1' /\ cfg_eqv c1 c1'.
Proof.
  intros c tr c1 H. induction H as [c | c evs c2 tr c3 Hst Hstar IH]; intros c' Heqv.
  - exists c'. split; [apply star_cfg_refl| exact Heqv].
  - destruct (sstepC_cfg_eqv c c' evs (SNext c2) Heqv Hst) as (X' & Hst' & HX).
    destruct X' as [c2'|]; simpl in HX; [|contradiction].
    destruct (IH c2' HX) as (c3' & Hstar' & H3).
    exists c3'. split; [eapply star_cfg_step; eassumption| exact H3].
Qed.

#[using="Type"] Lemma obs_traceC_eqv : forall c c' tr, cfg_eqv c c' -> obs_trace_cfg segs cfg c tr -> obs_trace_cfg segs cfg c' tr.
Proof.
  intros c c' tr Heqv (tr' & c1 & Hstar & Hp).
  destruct (starC_eqv c tr' c1 Hstar c' Heqv) as (c1' & Hstar' & _).
  exists tr', c1'. split; assumption.
Qed.

#[using="Type"] Lemma reaches_errorC_eqv : forall c c', cfg_eqv c c' -> reaches_error_cfg segs cfg c -> reaches_error_cfg segs cfg c'.
Proof.
  intros c c' Heqv (tr & c1 & evs & Hstar & Hst).
  destruct (starC_eqv c tr c1 Hstar c' Heqv) as (c1' & Hstar' & H1).
  destruct (sstepC_cfg_eqv c1 c1' evs SError H1 Hst) as (X' & Hst' & HX).
  destruct X'; simpl in HX; [contradiction|].
  exists tr, c1', evs. split; assumption.
Qed.

(* [comment removed for export] *)
#[using="Type"] Theorem behaviourC_eqv : forall ms ms' mo, ms_eqv ms ms' ->
  (forall tr, obs_trace_cfg segs cfg (mkCfg ms mo) tr <-> obs_trace_cfg segs cfg (mkCfg ms' mo) tr) /\
  (reaches_error_cfg segs cfg (mkCfg ms mo) <-> reaches_error_cfg segs cfg (mkCfg ms' mo)).
Proof.
  intros ms ms' mo Heqv.
  assert (H1 : cfg_eqv (mkCfg ms mo) (mkCfg ms' mo)) by (split; [exact Heqv| reflexivity]).
  pose proof (cfg_eqv_sym _ _ H1) as H2.
  split; [intros tr|]; split; intros H.
  - exact (obs_traceC_eqv _ _ tr H1 H).
  - exact (obs_traceC_eqv _ _ tr H2 H).
  - exact (reaches_errorC_eqv _ _ H1 H).
  - exact (reaches_errorC_eqv _ _ H2 H).
Qed.

End WithCfg.

End WithSegs.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MState OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition regs_eqv (R R' : bvmap 5 word) : Prop := forall r, reg_get R r = reg_get R' r.
(* [comment removed for export] *)
Definition regs_eqv0 (R R' : bvmap 5 word) : Prop := forall r, is_x0 r = false -> reg_get R r = reg_get R' r.

Lemma regs_eqv_refl : forall R, regs_eqv R R.
Proof. intros R r. reflexivity. Qed.
Lemma regs_eqv_sym : forall R R', regs_eqv R R' -> regs_eqv R' R.
Proof. intros R R' H r. symmetry. apply H. Qed.
Lemma regs_eqv_trans : forall R1 R2 R3, regs_eqv R1 R2 -> regs_eqv R2 R3 -> regs_eqv R1 R3.
Proof. intros R1 R2 R3 H1 H2 r. etransitivity; [apply H1|apply H2]. Qed.
Lemma regs_eqv0_refl : forall R, regs_eqv0 R R.
Proof. intros R r _. reflexivity. Qed.
Lemma regs_eqv0_sym : forall R R', regs_eqv0 R R' -> regs_eqv0 R' R.
Proof. intros R R' H r Hr. symmetry. apply H, Hr. Qed.
Lemma regs_eqv0_trans : forall R1 R2 R3, regs_eqv0 R1 R2 -> regs_eqv0 R2 R3 -> regs_eqv0 R1 R3.
Proof. intros R1 R2 R3 H1 H2 r Hr. etransitivity; [apply H1, Hr|apply H2, Hr]. Qed.
Lemma regs_eqv_eqv0 : forall R R', regs_eqv R R' -> regs_eqv0 R R'.
Proof. intros R R' H r _. apply H. Qed.
(* [comment removed for export] *)
Lemma rget_if_eqv0 : forall R R', regs_eqv0 R R' -> forall r,
  (if is_x0 r then w0 else reg_get R r) = (if is_x0 r then w0 else reg_get R' r).
Proof. intros R R' H r. destruct (is_x0 r) eqn:E; [reflexivity| apply H, E]. Qed.
Lemma is_x0_lit : forall z, (1 <= z < 32)%Z -> is_x0 (Z_to_bv 5 z) = false.
Proof. intros z Hz. unfold is_x0. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn [Z.pow_pos Pos.iter Z.mul Pos.mul]. rewrite Z.mod_small by lia. apply Z.eqb_neq. lia. Qed.

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
Lemma regs_eqv0_set : forall R R' (k : reg) v,
  regs_eqv0 R R' -> regs_eqv0 (bvmap_set k v R) (bvmap_set k v R').
Proof. intros R R' k v H r Hr. rewrite !reg_get_set. destruct (bv_eqb k r); [reflexivity|apply H, Hr]. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition core_eqv (c c' : core) : Prop :=
  regs_eqv0 (c_regs c) (c_regs c') /\ regs_eqv (c_fregs c) (c_fregs c') /\
  c_pc c = c_pc c' /\ c_fcsr c = c_fcsr c' /\ c_resv c = c_resv c'.

(* [comment removed for export] *)
Inductive eff_eqv : eff -> eff -> Prop :=
| EqvDone : forall c c', core_eqv c c' -> eff_eqv (EDone c) (EDone c')
| EqvIllegal : forall c c', eff_eqv (EIllegal c) (EIllegal c')
| EqvDefIllegal : forall c c', eff_eqv (EDefinedIllegal c) (EDefinedIllegal c')   (* [comment removed for export] *)
| EqvEcall : forall c c', eff_eqv (EEcall c) (EEcall c')
| EqvEbreak : forall c c', eff_eqv (EEbreak c) (EEbreak c')
| EqvFault : forall c c', eff_eqv (EFault c) (EFault c')
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
    | apply EqvIllegal | apply EqvDefIllegal | apply EqvEcall | apply EqvEbreak | apply EqvFault
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
  intros R R' F F' pc fc rv sz i HR HF.
  destruct i; unfold_exec; rewrite ?(rget_if_eqv0 R R' HR), ?HF; eqv_struct HR HF.
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
Proof. intros ms. repeat split; first [apply regs_eqv0_refl | apply regs_eqv_refl]. Qed.
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

Section WithSegs.
Variable segs : list Segment.

(* [comment removed for export] *)
#[using="Type"] Lemma interp_eff_accesses_eqv : forall t t', eff_eqv t t' -> forall m,
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
  intros t t' H. induction H; intros m; cbn [interp_eff_accesses access_value accessed_ranges fst snd]; auto.
  - destruct (ov_read_bytes segs m a (width_bytes n)) as [bs|]; [|exact I].
    specialize (H0 (bv_extract 0 n (le_bytes_to_word bs)) m).
    destruct (interp_eff_accesses segs (k _) m) as [rep| |]; destruct (interp_eff_accesses segs (k' _) m) as [rep'| |];
      cbn [access_value accessed_ranges] in *; try exact H0; try contradiction.
    destruct H0 as (H1 & H2 & H3). rewrite H3. auto.
  - destruct (store_ok segs m a (width_bytes n)); [|exact I].
    specialize (IHeff_eqv (write_to_mem m a (Z_to_le_bytes (width_bytes n) (bv_unsigned v)))).
    destruct (interp_eff_accesses segs k _) as [rep| |]; destruct (interp_eff_accesses segs k' _) as [rep'| |];
      cbn [access_value accessed_ranges] in *; try exact IHeff_eqv; try contradiction.
    destruct IHeff_eqv as (H1 & H2 & H3). rewrite H3. auto.
Qed.

#[using="Type"] Lemma ms_reg_eqv : forall ms ms' r, ms_eqv ms ms' -> ms_reg ms r = ms_reg ms' r.
Proof.
  intros ms ms' r (HR & _). unfold ms_reg. destruct (bv_eqb r 0) eqn:E; [reflexivity|].
  apply HR. unfold is_x0. apply Z.eqb_neq. intros Hz. apply Bool.not_true_iff_false in E. apply E.
  apply bv_eqb_eq. apply bv_eq. rewrite Hz. reflexivity.
Qed.

Definition ares_eqv (r r' : machine_result (access_report machine_state)) : Prop :=
  match r, r' with
  | MachineOk rep, MachineOk rep' =>
      ms_eqv (access_value _ rep) (access_value _ rep') /\ accessed_ranges _ rep = accessed_ranges _ rep'
  | MachineFault, MachineFault => True
  | MachineUnmodeled, MachineUnmodeled => True
  | _, _ => False
  end.

#[using="Type"] Lemma decode_exec_accesses_eqv : forall ms ms' w, ms_eqv ms ms' ->
  ares_eqv (decode_exec_accesses segs ms w) (decode_exec_accesses segs ms' w).
Proof.
  intros ms ms' w Heqv. pose proof (ms_reg_eqv ms ms' 17 Heqv) as H17.
  destruct ms as [R F pc svc rv fc m ro], ms' as [R' F' pc' svc' rv' fc' m' ro'].
  destruct Heqv as (HR & HF & Hpc & Hsvc & Hrv & Hfc & Hm & Hro); simpl in *; subst.
  unfold decode_exec_accesses. destruct (is_ecall w).
  - simpl. rewrite H17. repeat split; assumption.
  - destruct (decode_any w) as [[i isz]|]; [| destruct (is_defined_illegal w); exact I]. simpl.
    pose proof (interp_eff_accesses_eqv _ _ (exec_eqv_core R R' F F' pc' fc' rv' (Z_to_bv 64 isz) i HR HF) m') as K.
    destruct (interp_eff_accesses segs (exec _ i (Core R F pc' fc' rv')) m') as [[[c m1] rs]| |];
    destruct (interp_eff_accesses segs (exec _ i (Core R' F' pc' fc' rv')) m') as [[[c' m1'] rs']| |];
    simpl in *; try exact K; try contradiction.
    destruct K as ((H1 & H2 & H3 & H4 & H5) & -> & ->). repeat split; simpl; auto.
Qed.

#[using="Type"] Lemma step_accesses_eqv : forall ms ms', ms_eqv ms ms' ->
  ares_eqv (RiscvSemantics.step_accesses segs ms) (RiscvSemantics.step_accesses segs ms').
Proof.
  intros ms ms' Heqv. pose proof Heqv as (_ & _ & Hpc & _ & _ & _ & Hm & _).
  unfold RiscvSemantics.step_accesses, ms_pc. rewrite <- Hpc, <- Hm.
  destruct (fetch_word segs (ms_pc_val ms)); [apply decode_exec_accesses_eqv; exact Heqv|].
  destruct (fetch_word_ov segs (ms_mem ms) (ms_pc_val ms)); [apply decode_exec_accesses_eqv; exact Heqv|].
  destruct (fetch_tail_any segs (ms_mem ms) (ms_pc_val ms)); [apply decode_exec_accesses_eqv; exact Heqv|].
  unfold fetch_failure. destruct (negb _); [exact I|]. destruct (_ || _)%bool; exact I.
Qed.

Definition res_eqv (r r' : machine_result machine_state) : Prop :=
  match r, r' with
  | MachineOk a, MachineOk b => ms_eqv a b
  | MachineFault, MachineFault => True
  | MachineUnmodeled, MachineUnmodeled => True
  | _, _ => False
  end.

#[using="Type"] Lemma step_eqv : forall ms ms', ms_eqv ms ms' ->
  res_eqv (RiscvSemantics.step segs ms) (RiscvSemantics.step segs ms').
Proof.
  intros ms ms' Heqv. pose proof (step_accesses_eqv ms ms' Heqv) as H.
  unfold RiscvSemantics.step, drop_access_report.
  destruct (RiscvSemantics.step_accesses segs ms) as [rep| |]; destruct (RiscvSemantics.step_accesses segs ms') as [rep'| |];
    cbn in H; try exact H; try contradiction. exact (proj1 H).
Qed.

(* [comment removed for export] *)
Definition mres_eqv (r r' : machine_result (machine_state * Model)) : Prop :=
  match r, r' with
  | MachineOk (a, mo), MachineOk (b, mo') => ms_eqv a b /\ mo = mo'
  | MachineFault, MachineFault => True
  | MachineUnmodeled, MachineUnmodeled => True
  | _, _ => False
  end.

#[using="Type"] Lemma mi_account_step_eqv : forall ms ms' mo, ms_eqv ms ms' ->
  mres_eqv (mi_account_step segs ms mo) (mi_account_step segs ms' mo).
Proof.
  intros ms ms' mo Heqv. pose proof (step_accesses_eqv ms ms' Heqv) as H.
  unfold mi_account_step.
  destruct (RiscvSemantics.step_accesses segs ms) as [rep| |]; destruct (RiscvSemantics.step_accesses segs ms') as [rep'| |];
    cbn in H; try exact H; try contradiction.
  destruct H as [Hms <-]. destruct (materialize_model_accesses mo (accessed_ranges _ rep)); [|exact I].
  split; [exact Hms|reflexivity].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma syscall_args_eqv : forall ms ms', ms_eqv ms ms' -> syscall_args ms = syscall_args ms'.
Proof.
  intros ms ms' (HR & _). unfold syscall_args, ms_gpr. cbn [Z.of_nat Z.add Pos.of_succ_nat Pos.add Pos.succ].
  rewrite !HR by (apply is_x0_lit; lia). reflexivity.
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
  unfold apply_effect, set_reg; simpl. repeat split; simpl; auto using regs_eqv0_set.
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

#[using="Type"] Lemma cfg_eqv_sym : forall c c', cfg_eqv c c' -> cfg_eqv c' c.
Proof. intros c c' [H1 H2]. split; [apply ms_eqv_sym; exact H1| congruence]. Qed.

Definition to_eqv (X X' : step_to) : Prop :=
  match X, X' with
  | SError, SError => True
  | SNext c, SNext c' => cfg_eqv c c'
  | _, _ => False
  end.

#[using="Type"] Lemma sstep_eqv : forall ms ms' mo evs X, ms_eqv ms ms' ->
  sstep segs (mkCfg ms mo) evs X ->
  exists X', sstep segs (mkCfg ms' mo) evs X' /\ to_eqv X X'.
Proof.
  intros ms ms' mo evs X Heqv Hst.
  pose proof (mi_account_step_eqv ms ms' mo Heqv) as Hres.
  pose proof Heqv as (_ & _ & _ & Hsvc & _ & _ & _ & _).
  inversion Hst; subst.
  - (* [comment removed for export] *)
    rewrite H5 in Hres. destruct (mi_account_step segs ms' mo) as [[ms1' mo1']| |] eqn:E; simpl in Hres; try contradiction.
    destruct Hres as [Hms <-].
    exists (SNext (mkCfg ms1' model')). split; [apply sstep_instr; auto; congruence|]. split; [exact Hms| reflexivity].
  - rewrite H5 in Hres. destruct (mi_account_step segs ms' mo) as [[ms1' mo1']| |] eqn:E; simpl in Hres; try contradiction.
    exists SError. split; [apply sstep_instr_fault; auto; congruence| exact I].
  - rewrite H5 in Hres. destruct (mi_account_step segs ms' mo) as [[ms1' mo1']| |] eqn:E; simpl in Hres; try contradiction.
    exists SError. split; [apply sstep_instr_unmodeled; auto; congruence| exact I].
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

#[using="Type"] Lemma sstep_cfg_eqv : forall c c' evs X, cfg_eqv c c' ->
  sstep segs c evs X -> exists X', sstep segs c' evs X' /\ to_eqv X X'.
Proof.
  intros [ms mo] [ms' mo'] evs X [Hms Hmo] Hst; simpl in Hms, Hmo; subst.
  apply (sstep_eqv ms ms'); assumption.
Qed.

#[using="Type"] Lemma star_eqv : forall c tr c1, star segs c tr c1 ->
  forall c', cfg_eqv c c' -> exists c1', star segs c' tr c1' /\ cfg_eqv c1 c1'.
Proof.
  intros c tr c1 H. induction H as [c | c evs c2 tr c3 Hst Hstar IH]; intros c' Heqv.
  - exists c'. split; [apply star_refl| exact Heqv].
  - destruct (sstep_cfg_eqv c c' evs (SNext c2) Heqv Hst) as (X' & Hst' & HX).
    destruct X' as [c2'|]; simpl in HX; [|contradiction].
    destruct (IH c2' HX) as (c3' & Hstar' & H3).
    exists c3'. split; [eapply star_step; eassumption| exact H3].
Qed.

#[using="Type"] Lemma obs_trace_eqv : forall c c' tr, cfg_eqv c c' -> obs_trace segs c tr -> obs_trace segs c' tr.
Proof.
  intros c c' tr Heqv (tr' & c1 & Hstar & Hp).
  destruct (star_eqv c tr' c1 Hstar c' Heqv) as (c1' & Hstar' & _).
  exists tr', c1'. split; assumption.
Qed.

#[using="Type"] Lemma reaches_error_eqv : forall c c', cfg_eqv c c' -> reaches_error segs c -> reaches_error segs c'.
Proof.
  intros c c' Heqv (tr & c1 & evs & Hstar & Hst).
  destruct (star_eqv c tr c1 Hstar c' Heqv) as (c1' & Hstar' & H1).
  destruct (sstep_cfg_eqv c1 c1' evs SError H1 Hst) as (X' & Hst' & HX).
  destruct X'; simpl in HX; [contradiction|].
  exists tr, c1', evs. split; assumption.
Qed.

#[using="Type"] Lemma unmodeled_at_eqv : forall c c', cfg_eqv c c' -> unmodeled_at segs c -> unmodeled_at segs c'.
Proof.
  intros [ms mo] [ms' mo'] [Hms Hmo] Hun; simpl in Hms, Hmo; subst.
  unfold unmodeled_at in *. cbn [cfg_ms cfg_model] in *. destruct Hun as (Hh & Hcase).
  pose proof Hms as (_ & _ & _ & Hsvc & _ & _ & _ & _).
  split; [exact Hh|]. destruct Hcase as [(Hnone & Hstep) | (x8 & Hsome & Hspec)].
  - left. split; [congruence|].
    pose proof (mi_account_step_eqv ms ms' mo' Hms) as Hres. rewrite Hstep in Hres.
    destruct (mi_account_step segs ms' mo') as [[? ?]| |]; simpl in Hres; try contradiction. reflexivity.
  - right. exists x8. split; [congruence|]. rewrite <- (sys_input_eqv ms ms' x8 Hms). exact Hspec.
Qed.

#[using="Type"] Lemma reaches_unmodeled_eqv : forall c c', cfg_eqv c c' ->
  reaches_unmodeled segs c -> reaches_unmodeled segs c'.
Proof.
  intros c c' Heqv (tr & c1 & Hstar & Hun).
  destruct (star_eqv c tr c1 Hstar c' Heqv) as (c1' & Hstar' & H1).
  exists tr, c1'. split; [exact Hstar'| eapply unmodeled_at_eqv; eassumption].
Qed.

#[using="Type"] Lemma all_traces_error_eqv : forall c, all_traces_error segs c ->
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
#[using="Type"] Theorem behaviour_eqv : forall ms ms' mo, ms_eqv ms ms' ->
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

(* [comment removed for export] *)
Section WithCfg.
Variable cfg : SpuriousCfg.

#[using="Type"] Lemma sstepC_eqv : forall ms ms' mo evs X, ms_eqv ms ms' ->
  sstep_cfg segs cfg (mkCfg ms mo) evs X ->
  exists X', sstep_cfg segs cfg (mkCfg ms' mo) evs X' /\ to_eqv X X'.
Proof.
  intros ms ms' mo evs X Heqv Hst.
  pose proof (mi_account_step_eqv ms ms' mo Heqv) as Hres.
  pose proof Heqv as (_ & _ & _ & Hsvc & _ & _ & _ & _).
  inversion Hst; subst.
  - rewrite H5 in Hres. destruct (mi_account_step segs ms' mo) as [[ms1' mo1']| |] eqn:E; simpl in Hres; try contradiction.
    destruct Hres as [Hms <-].
    exists (SNext (mkCfg ms1' model')). split; [apply sstep_cfg_instr; auto; congruence|]. split; [exact Hms| reflexivity].
  - rewrite H5 in Hres. destruct (mi_account_step segs ms' mo) as [[ms1' mo1']| |] eqn:E; simpl in Hres; try contradiction.
    exists SError. split; [apply sstep_cfg_instr_fault; auto; congruence| exact I].
  - rewrite H5 in Hres. destruct (mi_account_step segs ms' mo) as [[ms1' mo1']| |] eqn:E; simpl in Hres; try contradiction.
    exists SError. split; [apply sstep_cfg_instr_unmodeled; auto; congruence| exact I].
  - exists (SNext (mkCfg (advance_past_svc (apply_effect ms' eff)) model'')). split.
    + apply (sstep_cfg_syscall segs cfg ms' mo x8 eff model' model'' evs);
        [assumption| congruence| rewrite <- (sys_input_eqv ms ms' x8 Heqv); assumption
        | rewrite <- (sys_input_eqv ms ms' x8 Heqv); assumption | assumption| assumption].
    + split; [| reflexivity]. apply advance_past_svc_eqv, apply_effect_eqv, Heqv.
  - exists SError. split; [|exact I].
    apply (sstep_cfg_syscall_materialization_fault segs cfg ms' mo x8 eff model' evs0);
      [assumption| congruence| rewrite <- (sys_input_eqv ms ms' x8 Heqv); assumption
      | rewrite <- (sys_input_eqv ms ms' x8 Heqv); assumption | assumption| assumption].
  - exists (SNext (mkCfg ms' model')). split.
    + apply (sstep_cfg_exit segs cfg ms' mo x8 eff model' evs0 code);
        [assumption| congruence| rewrite <- (sys_input_eqv ms ms' x8 Heqv); assumption| assumption| assumption].
    + split; [exact Heqv| reflexivity].
  - exists (SNext (mkCfg ms' model')). split.
    + apply (sstep_cfg_killed segs cfg ms' mo x8 eff model' evs0 sig);
        [assumption| congruence| rewrite <- (sys_input_eqv ms ms' x8 Heqv); assumption| assumption].
    + split; [exact Heqv| reflexivity].
  - exists SError. split; [|exact I].
    apply (sstep_cfg_syscall_unmodeled segs cfg ms' mo x8);
      [assumption| congruence| rewrite <- (sys_input_eqv ms ms' x8 Heqv); assumption].
Qed.

#[using="Type"] Lemma sstepC_cfg_eqv : forall c c' evs X, cfg_eqv c c' ->
  sstep_cfg segs cfg c evs X -> exists X', sstep_cfg segs cfg c' evs X' /\ to_eqv X X'.
Proof.
  intros [ms mo] [ms' mo'] evs X [Hms Hmo] Hst; simpl in Hms, Hmo; subst.
  apply (sstepC_eqv ms ms'); assumption.
Qed.

#[using="Type"] Lemma starC_eqv : forall c tr c1, star_cfg segs cfg c tr c1 ->
  forall c', cfg_eqv c c' -> exists c1', star_cfg segs cfg c' tr c1' /\ cfg_eqv c1 c1'.
Proof.
  intros c tr c1 H. induction H as [c | c evs c2 tr c3 Hst Hstar IH]; intros c' Heqv.
  - exists c'. split; [apply star_cfg_refl| exact Heqv].
  - destruct (sstepC_cfg_eqv c c' evs (SNext c2) Heqv Hst) as (X' & Hst' & HX).
    destruct X' as [c2'|]; simpl in HX; [|contradiction].
    destruct (IH c2' HX) as (c3' & Hstar' & H3).
    exists c3'. split; [eapply star_cfg_step; eassumption| exact H3].
Qed.

#[using="Type"] Lemma obs_traceC_eqv : forall c c' tr, cfg_eqv c c' -> obs_trace_cfg segs cfg c tr -> obs_trace_cfg segs cfg c' tr.
Proof.
  intros c c' tr Heqv (tr' & c1 & Hstar & Hp).
  destruct (starC_eqv c tr' c1 Hstar c' Heqv) as (c1' & Hstar' & _).
  exists tr', c1'. split; assumption.
Qed.

#[using="Type"] Lemma reaches_errorC_eqv : forall c c', cfg_eqv c c' -> reaches_error_cfg segs cfg c -> reaches_error_cfg segs cfg c'.
Proof.
  intros c c' Heqv (tr & c1 & evs & Hstar & Hst).
  destruct (starC_eqv c tr c1 Hstar c' Heqv) as (c1' & Hstar' & H1).
  destruct (sstepC_cfg_eqv c1 c1' evs SError H1 Hst) as (X' & Hst' & HX).
  destruct X'; simpl in HX; [contradiction|].
  exists tr, c1', evs. split; assumption.
Qed.

(* [comment removed for export] *)
#[using="Type"] Theorem behaviourC_eqv : forall ms ms' mo, ms_eqv ms ms' ->
  (forall tr, obs_trace_cfg segs cfg (mkCfg ms mo) tr <-> obs_trace_cfg segs cfg (mkCfg ms' mo) tr) /\
  (reaches_error_cfg segs cfg (mkCfg ms mo) <-> reaches_error_cfg segs cfg (mkCfg ms' mo)).
Proof.
  intros ms ms' mo Heqv.
  assert (H1 : cfg_eqv (mkCfg ms mo) (mkCfg ms' mo)) by (split; [exact Heqv| reflexivity]).
  pose proof (cfg_eqv_sym _ _ H1) as H2.
  split; [intros tr|]; split; intros H.
  - exact (obs_traceC_eqv _ _ tr H1 H).
  - exact (obs_traceC_eqv _ _ tr H2 H).
  - exact (reaches_errorC_eqv _ _ H1 H).
  - exact (reaches_errorC_eqv _ _ H2 H).
Qed.

End WithCfg.

End WithSegs.
End TwB.
End RegsEqv0.

(* [comment removed for export] *)
Module SrzEqv.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AsanHexScan__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AllocSim2__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require PropExec__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require SpinAlg. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanHexScan__Common.SimInv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AllocSim2__Common.ShapeAlg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.DivergeSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.SpinAlg.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import MState Frame.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.RegsEqv0__AS.RegsEqv0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma tset_tset_same : forall {A} (p : positive) (x y : A) t, tset p x (tset p y t) = tset p x t.
Proof. intros A p. induction p; intros x y [|l v r]; cbn; try rewrite IHp; reflexivity. Qed.

Lemma tset_comm : forall {A} (p q : positive) (x y : A) t, p <> q -> tset p x (tset q y t) = tset q y (tset p x t).
Proof.
  intros A p. induction p; intros [q|q|] x y [|l v r] Hne; cbn; try reflexivity; try congruence;
    try (rewrite (IHp q) by congruence; reflexivity).
Qed.

(* [comment removed for export] *)
Fixpoint tsets {A} (l : list (positive * A)) (t : tree A) : tree A :=
  match l with
  | [] => t
  | (k, v) :: l' => tset k v (tsets l' t)
  end.

Lemma tsets_absorb : forall {A} (l : list (positive * A)) k v t,
  tsets l (tset k v t) = if existsb (Pos.eqb k) (map fst l) then tsets l t else tset k v (tsets l t).
Proof.
  intros A l. induction l as [|[k' v'] l IH]; intros k v t; [reflexivity|].
  cbn [tsets map fst existsb]. rewrite IH. destruct (existsb (Pos.eqb k) (map fst l)).
  - rewrite Bool.orb_true_r. reflexivity.
  - rewrite Bool.orb_false_r. destruct (Pos.eqb_spec k k') as [->|Hne].
    + apply tset_tset_same.
    + apply tset_comm. congruence.
Qed.

Lemma tsets_idem : forall {A} (l : list (positive * A)) t, tsets l (tsets l t) = tsets l t.
Proof.
  intros A l. induction l as [|[k v] l IH]; intros t; [reflexivity|].
  cbn [tsets]. rewrite tsets_absorb. destruct (existsb (Pos.eqb k) (map fst l)).
  - rewrite IH. reflexivity.
  - rewrite IH. apply tset_tset_same.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Shape.
Variables (R R' F F' : bvmap 5 word).

(* [comment removed for export] *)
Definition core_rel (c c' : core) : Prop :=
  exists l lf, c_regs c = tsets l R /\ c_regs c' = tsets l R' /\ c_fregs c = tsets lf F /\ c_fregs c' = tsets lf F'.

Inductive eff_rel : eff -> eff -> Prop :=
| RelDone : forall c c', core_rel c c' -> eff_rel (EDone c) (EDone c')
| RelIllegal : forall c c', eff_rel (EIllegal c) (EIllegal c')
| RelDefIllegal : forall c c', eff_rel (EDefinedIllegal c) (EDefinedIllegal c')
| RelEcall : forall c c', eff_rel (EEcall c) (EEcall c')
| RelEbreak : forall c c', eff_rel (EEbreak c) (EEbreak c')
| RelFault : forall c c', eff_rel (EFault c) (EFault c')
| RelLoad : forall n a k k', (forall v, eff_rel (k v) (k' v)) -> eff_rel (ELoad n a k) (ELoad n a k')
| RelStore : forall n a v k k', eff_rel k k' -> eff_rel (EStore n a v k) (EStore n a v k').

#[using="Type"] Lemma core_rel_mk : forall pc fc rv, core_rel (Core R F pc fc rv) (Core R' F' pc fc rv).
Proof. intros. exists [], []. repeat split; reflexivity. Qed.

Local Ltac core_tac :=
  unfold core_rel, rset, fset, with_regs, with_fregs, with_pc, with_fcsr, with_resv,
         accrue, fwrite, inval_resv in *; simpl in *.

#[using="Type"] Lemma core_rel_rset : forall r v c c', core_rel c c' -> core_rel (rset r v c) (rset r v c').
Proof.
  intros r v [S G p f s] [S' G' p' f' s'] H. core_tac. destruct H as (l & lf & H1 & H2 & H3 & H4). subst.
  destruct (is_x0 r); simpl.
  - exists l, lf. repeat split; reflexivity.
  - exists ((bv_key r, v) :: l), lf. repeat split; reflexivity.
Qed.
#[using="Type"] Lemma core_rel_fset : forall r v c c', core_rel c c' -> core_rel (fset r v c) (fset r v c').
Proof.
  intros r v [S G p f s] [S' G' p' f' s'] H. core_tac. destruct H as (l & lf & H1 & H2 & H3 & H4). subst.
  exists l, ((bv_key r, v) :: lf). repeat split; reflexivity.
Qed.
#[using="Type"] Lemma core_rel_with_pc : forall v v' c c', core_rel c c' -> core_rel (with_pc v c) (with_pc v' c').
Proof. intros v v' [S G p f s] [S' G' p' f' s'] H. core_tac. exact H. Qed.
#[using="Type"] Lemma core_rel_with_fcsr : forall v v' c c', core_rel c c' -> core_rel (with_fcsr v c) (with_fcsr v' c').
Proof. intros v v' [S G p f s] [S' G' p' f' s'] H. core_tac. exact H. Qed.
#[using="Type"] Lemma core_rel_with_resv : forall v v' c c', core_rel c c' -> core_rel (with_resv v c) (with_resv v' c').
Proof. intros v v' [S G p f s] [S' G' p' f' s'] H. core_tac. exact H. Qed.
#[using="Type"] Lemma core_rel_accrue : forall fl fl' c c', core_rel c c' -> core_rel (accrue fl c) (accrue fl' c').
Proof. intros fl fl' [S G p f s] [S' G' p' f' s'] H. core_tac. exact H. Qed.
#[using="Type"] Lemma core_rel_fwrite : forall fmt r v c c', core_rel c c' -> core_rel (fwrite fmt r v c) (fwrite fmt r v c').
Proof. intros fmt r v c c' H. destruct fmt; apply core_rel_fset; exact H. Qed.
#[using="Type"] Lemma core_rel_inval_resv : forall a a' c c', core_rel c c' -> core_rel (inval_resv a c) (inval_resv a' c').
Proof.
  intros a a' [S G p f s] [S' G' p' f' s'] H. core_tac.
  destruct s as [r|]; [destruct (Z.eqb _ _)|]; (destruct s' as [r'|]; [destruct (Z.eqb _ _)|]); simpl; exact H.
Qed.
#[using="Type"] Lemma core_rel_if : forall (b : bool) c1 c1' c2 c2',
  core_rel c1 c1' -> core_rel c2 c2' -> core_rel (if b then c1 else c2) (if b then c1' else c2').
Proof. intros [] c1 c1' c2 c2' H1 H2; assumption. Qed.

Local Ltac solve_core :=
  repeat first [ apply core_rel_rset | apply core_rel_fset | apply core_rel_with_pc
               | apply core_rel_with_fcsr | apply core_rel_with_resv | apply core_rel_accrue
               | apply core_rel_fwrite | apply core_rel_inval_resv | apply core_rel_if
               | match goal with |- core_rel (match ?X with _ => _ end) _ => destruct X end ];
  apply core_rel_mk.

Local Ltac rel_struct :=
  repeat first
    [ apply RelDone; solve_core
    | apply RelIllegal | apply RelDefIllegal | apply RelEcall | apply RelEbreak | apply RelFault
    | apply RelLoad; intros ?
    | apply RelStore
    | match goal with |- eff_rel (match ?X with _ => _ end) _ => destruct X end
    | match goal with |- eff_rel (match ?X with _ => _ end _) _ => destruct X end ].

Local Ltac unfold_exec :=
  cbv beta iota zeta delta [exec rget fget fread c_regs c_fregs c_pc c_fcsr c_resv
                            with_pc load_val store_val exec_csr resolve_rm frm_of].

(* [comment removed for export] *)
#[using="Type"] Lemma exec_rel_core : forall pc fc rv sz i,
  regs_eqv0 R R' -> regs_eqv F F' ->
  eff_rel (exec sz i (Core R F pc fc rv)) (exec sz i (Core R' F' pc fc rv)).
Proof.
  intros pc fc rv sz i HR HF.
  destruct i; unfold_exec; rewrite ?(rget_if_eqv0 R R' HR), ?HF; rel_struct.
Qed.

Section WithSegsI.
Variable segs : list Segment.

#[using="Type"] Lemma interp_eff_accesses_rel : forall t t', eff_rel t t' -> forall m,
  match interp_eff_accesses segs t m, interp_eff_accesses segs t' m with
  | MachineOk rep, MachineOk rep' => core_rel (fst (access_value _ rep)) (fst (access_value _ rep'))
  | _, _ => True
  end.
Proof.
  intros t t' H. induction H; intros m; cbn [interp_eff_accesses access_value accessed_ranges fst snd]; auto.
  - destruct (ov_read_bytes segs m a (width_bytes n)) as [bs|]; [|exact I].
    match goal with |- context [interp_eff_accesses segs (k ?x) m] => pose proof (H0 x m) as K end.
    destruct (interp_eff_accesses segs (k _) m) as [rep| |]; [|exact I|exact I].
    destruct (interp_eff_accesses segs (k' _) m) as [rep'| |]; [|exact I|exact I].
    cbn [access_value accessed_ranges] in *. exact K.
  - destruct (store_ok segs m a (width_bytes n)); [|exact I].
    match goal with |- context [interp_eff_accesses segs k ?x] => pose proof (IHeff_rel x) as K end.
    destruct (interp_eff_accesses segs k _) as [rep| |]; [|exact I|exact I].
    destruct (interp_eff_accesses segs k' _) as [rep'| |]; [|exact I|exact I].
    cbn [access_value accessed_ranges] in *. exact K.
Qed.
End WithSegsI.
End Shape.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition ms_rel (a a' b b' : machine_state) : Prop :=
  exists l lf, ms_regs b = tsets l (ms_regs a) /\ ms_regs b' = tsets l (ms_regs a')
               /\ ms_fregs b = tsets lf (ms_fregs a) /\ ms_fregs b' = tsets lf (ms_fregs a').

Section WithSegs.
Variable segs : list Segment.

Definition ares_rel (a a' : machine_state) (r r' : machine_result (access_report machine_state)) : Prop :=
  match r, r' with
  | MachineOk rep, MachineOk rep' => ms_rel a a' (access_value _ rep) (access_value _ rep')
  | _, _ => True
  end.

#[using="Type"] Lemma decode_exec_accesses_rel : forall ms ms' w, ms_eqv ms ms' ->
  ares_rel ms ms' (decode_exec_accesses segs ms w) (decode_exec_accesses segs ms' w).
Proof.
  intros ms ms' w Heqv.
  destruct ms as [R F pc svc rv fc m ro], ms' as [R' F' pc' svc' rv' fc' m' ro'].
  destruct Heqv as (HR & HF & Hpc & Hsvc & Hrv & Hfc & Hm & Hro); simpl in *; subst.
  unfold decode_exec_accesses. destruct (is_ecall w).
  - simpl. exists [], []. repeat split; reflexivity.
  - destruct (decode_any w) as [[i isz]|]; [| destruct (is_defined_illegal w); exact I]. simpl.
    pose proof (interp_eff_accesses_rel R R' F F' segs _ _ (exec_rel_core R R' F F' pc' fc' rv' (Z_to_bv 64 isz) i HR HF) m') as K.
    destruct (interp_eff_accesses segs (exec _ i (Core R F pc' fc' rv')) m') as [[[c m1] rs]| |];
    destruct (interp_eff_accesses segs (exec _ i (Core R' F' pc' fc' rv')) m') as [[[c' m1'] rs']| |];
    simpl in *; try exact I.
    destruct K as (l & lf & K1 & K2 & K3 & K4). exists l, lf. simpl. repeat split; assumption.
Qed.

#[using="Type"] Lemma step_accesses_rel : forall ms ms', ms_eqv ms ms' ->
  ares_rel ms ms' (RiscvSemantics.step_accesses segs ms) (RiscvSemantics.step_accesses segs ms').
Proof.
  intros ms ms' Heqv. pose proof Heqv as (_ & _ & Hpc & _ & _ & _ & Hm & _).
  unfold RiscvSemantics.step_accesses, ms_pc. rewrite <- Hpc, <- Hm.
  destruct (fetch_word segs (ms_pc_val ms)); [apply decode_exec_accesses_rel; exact Heqv|].
  destruct (fetch_word_ov segs (ms_mem ms) (ms_pc_val ms)); [apply decode_exec_accesses_rel; exact Heqv|].
  destruct (fetch_tail_any segs (ms_mem ms) (ms_pc_val ms)); [apply decode_exec_accesses_rel; exact Heqv|].
  unfold fetch_failure. destruct (negb _); [exact I|]. destruct (_ || _)%bool; exact I.
Qed.

#[using="Type"] Lemma mi_account_step_rel : forall ms ms' mo mo', ms_eqv ms ms' ->
  match mi_account_step segs ms mo, mi_account_step segs ms' mo' with
  | MachineOk (a, _), MachineOk (b, _) => ms_rel ms ms' a b
  | _, _ => True
  end.
Proof.
  intros ms ms' mo mo' Heqv. pose proof (step_accesses_rel ms ms' Heqv) as H.
  unfold mi_account_step.
  destruct (RiscvSemantics.step_accesses segs ms) as [rep| |]; destruct (RiscvSemantics.step_accesses segs ms') as [rep'| |];
    cbn in H; try exact I;
    repeat match goal with |- context [materialize_model_accesses ?m ?r] => destruct (materialize_model_accesses m r) end;
    try exact I; exact H.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma ms_eq_fields : forall a b : machine_state,
  ms_regs a = ms_regs b -> ms_fregs a = ms_fregs b -> ms_pc_val a = ms_pc_val b -> ms_svc_pending a = ms_svc_pending b ->
  ms_resv a = ms_resv b -> ms_fcsr a = ms_fcsr b -> ms_mem a = ms_mem b -> ms_rom a = ms_rom b -> a = b.
Proof. intros [] []; cbn; intros; subst; reflexivity. Qed.

#[using="Type"] Lemma to_spin_eqv : forall ms model, to_spin segs ms model -> forall ms', ms_eqv ms ms' -> to_spin segs ms' model.
Proof.
  induction 1 as [ms model Hsvc Hfix | ms model ms1 model1 Hsvc Hst Hspin IH]; intros ms' Heqv.
  - (* [comment removed for export] *)
    pose proof (mi_account_step_eqv segs ms ms' model Heqv) as K. rewrite Hfix in K.
    destruct (mi_account_step segs ms' model) as [[ms1' mo1']| |] eqn:E1; cbn in K; try contradiction.
    destruct K as [H1 <-].
    pose proof (mi_account_step_eqv segs ms ms1' model H1) as K2. rewrite Hfix in K2.
    destruct (mi_account_step segs ms1' model) as [[ms2' mo2']| |] eqn:E2; cbn in K2; try contradiction.
    destruct K2 as [H2 <-].
    assert (Heq' : ms_eqv ms' ms1') by (eapply ms_eqv_trans; [apply ms_eqv_sym; exact Heqv | exact H1]).
    pose proof (mi_account_step_rel ms' ms1' model model Heq') as S. rewrite E1, E2 in S.
    destruct S as (l & lf & S1 & S2 & S3 & S4).
    pose proof H1 as (_ & _ & P1 & P2 & P3 & P4 & P5 & P6). pose proof H2 as (_ & _ & Q1 & Q2 & Q3 & Q4 & Q5 & Q6).
    assert (EQ : ms2' = ms1').
    { apply ms_eq_fields; try congruence.
      - rewrite S2, S1. apply tsets_idem.
      - rewrite S4, S3. apply tsets_idem. }
    subst ms2'.
    pose proof Heqv as (_ & _ & _ & V & _).
    eapply ts_step; [congruence | exact E1 |]. apply ts_spin; [congruence | exact E2].
  - pose proof (mi_account_step_eqv segs ms ms' model Heqv) as K. rewrite Hst in K.
    destruct (mi_account_step segs ms' model) as [[ms1' mo1']| |] eqn:E1; cbn in K; try contradiction.
    destruct K as [H1 <-]. pose proof Heqv as (_ & _ & _ & V & _).
    eapply ts_step; [congruence | exact E1 | exact (IH ms1' H1)].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma cfg_eqv_refl : forall c, cfg_eqv c c.
Proof. intros [ms mo]. split; [apply ms_eqv_refl | reflexivity]. Qed.

#[using="Type"] Lemma cfg_eqv_trans : forall a b c, cfg_eqv a b -> cfg_eqv b c -> cfg_eqv a c.
Proof.
  intros [? ?] [? ?] [? ?] [H1 H2] [G1 G2]; cbn in *. split; [eapply ms_eqv_trans; eassumption | etransitivity; eassumption].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma sstep_next_eqv : forall c c' e c2,
  cfg_eqv c c' -> sstep_cfg segs CFG c e (SNext c2) -> exists c2', sstep_cfg segs CFG c' e (SNext c2') /\ cfg_eqv c2 c2'.
Proof.
  intros c c' e c2 Heqv Hss.
  destruct (sstepC_cfg_eqv segs CFG c c' e (SNext c2) Heqv Hss) as (X' & Hss' & HX).
  destruct X' as [c2'| ]; cbn in HX; [|contradiction].
  exists c2'. split; assumption.
Qed.

#[using="Type"] Theorem srealizes_eqv : forall c T, srealizes segs c T -> forall c', cfg_eqv c c' -> srealizes segs c' T.
Proof.
  intros c T H.
  induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh | c Hspin Hh | c T T' H IH Heq]; intros c' Heqv.
  - (* [comment removed for export] *)
    destruct Hnode as [Hfwd Hexact].
    set (I' := { p : I * config | sstep_cfg segs CFG c' (evs (fst p)) (SNext (snd p)) /\ cfg_eqv (nx (fst p)) (snd p) }).
    destruct (sstep_next_eqv c c' (evs i0) (nx i0) Heqv (Hfwd i0)) as (c20 & Hs0 & He0).
    pose (q0 := (exist _ (i0, c20) (conj Hs0 He0) : I')).
    apply (srz_conseq segs c' (t_alt (fun q : I' => t_emit (evs (fst (proj1_sig q))) (T (fst (proj1_sig q)))))).
    + apply (srz_node segs c' I' (fun q => evs (fst (proj1_sig q))) (fun q => snd (proj1_sig q))
                      (fun q => T (fst (proj1_sig q))) q0).
      * split.
        -- intros [[i c2] [Hs He]]. cbn. exact Hs.
        -- intros e st Hss.
           destruct (sstepC_cfg_eqv segs CFG c' c e st (cfg_eqv_sym c c' Heqv) Hss) as (X & HssX & HX).
           destruct (Hexact e X HssX) as (j & -> & ->).
           destruct st as [c2|]; cbn in HX; [|contradiction].
           exists (exist _ (j, c2) (conj Hss (cfg_eqv_sym _ _ HX))). cbn. split; reflexivity.
      * intros [[i c2] [Hs He]]. cbn. exact (IH i c2 He).
    + (* [comment removed for export] *)
      intros tr. split.
      * intros [[[i c2] [Hs He]] Ht]. cbn in Ht. exists i. exact Ht.
      * intros [i Ht].
        destruct (sstep_next_eqv c c' (evs i) (nx i) Heqv (Hfwd i)) as (c2 & Hs & He).
        exists (exist _ (i, c2) (conj Hs He)). cbn. exact Ht.
  - (* [comment removed for export] *)
    apply srz_halt. destruct Heqv as [_ Hmo]. rewrite <- Hmo. exact Hh.
  - (* [comment removed for export] *)
    destruct Hspin as [[] _].
  - (* [comment removed for export] *)
    eapply srz_conseq; [apply IH; exact Heqv | exact Heq].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma mkst_MS : forall R pc m ro,
  @OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec.mkst OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec.fx0 R pc m ro
  = MS R bvmap_empty pc (Z_to_bv 32 0) None m ro.
Proof. reflexivity. Qed.

#[using="Type"] Lemma cfg_eqv_regs : forall R R' F pc fc rv m ro mo,
  regs_eqv0 R R' -> cfg_eqv (mkCfg (MS R F pc fc rv m ro) mo) (mkCfg (MS R' F pc fc rv m ro) mo).
Proof.
  intros. split; [|reflexivity]. split; [assumption|]. split; [apply regs_eqv_refl|]. repeat split; reflexivity.
Qed.

End WithSegs.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanHexScan__Common.SimInv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AllocSim2__Common.ShapeAlg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.DivergeSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.SpinAlg.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MState OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.RegsEqv0__AS.RegsEqv0.TwB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma tset_tset_same : forall {A} (p : positive) (x y : A) t, tset p x (tset p y t) = tset p x t.
Proof. intros A p. induction p; intros x y [|l v r]; cbn; try rewrite IHp; reflexivity. Qed.

Lemma tset_comm : forall {A} (p q : positive) (x y : A) t, p <> q -> tset p x (tset q y t) = tset q y (tset p x t).
Proof.
  intros A p. induction p; intros [q|q|] x y [|l v r] Hne; cbn; try reflexivity; try congruence;
    try (rewrite (IHp q) by congruence; reflexivity).
Qed.

(* [comment removed for export] *)
Fixpoint tsets {A} (l : list (positive * A)) (t : tree A) : tree A :=
  match l with
  | [] => t
  | (k, v) :: l' => tset k v (tsets l' t)
  end.

Lemma tsets_absorb : forall {A} (l : list (positive * A)) k v t,
  tsets l (tset k v t) = if existsb (Pos.eqb k) (map fst l) then tsets l t else tset k v (tsets l t).
Proof.
  intros A l. induction l as [|[k' v'] l IH]; intros k v t; [reflexivity|].
  cbn [tsets map fst existsb]. rewrite IH. destruct (existsb (Pos.eqb k) (map fst l)).
  - rewrite Bool.orb_true_r. reflexivity.
  - rewrite Bool.orb_false_r. destruct (Pos.eqb_spec k k') as [->|Hne].
    + apply tset_tset_same.
    + apply tset_comm. congruence.
Qed.

Lemma tsets_idem : forall {A} (l : list (positive * A)) t, tsets l (tsets l t) = tsets l t.
Proof.
  intros A l. induction l as [|[k v] l IH]; intros t; [reflexivity|].
  cbn [tsets]. rewrite tsets_absorb. destruct (existsb (Pos.eqb k) (map fst l)).
  - rewrite IH. reflexivity.
  - rewrite IH. apply tset_tset_same.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Shape.
Variables (R R' F F' : bvmap 5 word).

(* [comment removed for export] *)
Definition core_rel (c c' : core) : Prop :=
  exists l lf, c_regs c = tsets l R /\ c_regs c' = tsets l R' /\ c_fregs c = tsets lf F /\ c_fregs c' = tsets lf F'.

Inductive eff_rel : eff -> eff -> Prop :=
| RelDone : forall c c', core_rel c c' -> eff_rel (EDone c) (EDone c')
| RelIllegal : forall c c', eff_rel (EIllegal c) (EIllegal c')
| RelDefIllegal : forall c c', eff_rel (EDefinedIllegal c) (EDefinedIllegal c')
| RelEcall : forall c c', eff_rel (EEcall c) (EEcall c')
| RelEbreak : forall c c', eff_rel (EEbreak c) (EEbreak c')
| RelFault : forall c c', eff_rel (EFault c) (EFault c')
| RelLoad : forall n a k k', (forall v, eff_rel (k v) (k' v)) -> eff_rel (ELoad n a k) (ELoad n a k')
| RelStore : forall n a v k k', eff_rel k k' -> eff_rel (EStore n a v k) (EStore n a v k').

#[using="Type"] Lemma core_rel_mk : forall pc fc rv, core_rel (Core R F pc fc rv) (Core R' F' pc fc rv).
Proof. intros. exists [], []. repeat split; reflexivity. Qed.

Local Ltac core_tac :=
  unfold core_rel, rset, fset, with_regs, with_fregs, with_pc, with_fcsr, with_resv,
         accrue, fwrite, inval_resv in *; simpl in *.

#[using="Type"] Lemma core_rel_rset : forall r v c c', core_rel c c' -> core_rel (rset r v c) (rset r v c').
Proof.
  intros r v [S G p f s] [S' G' p' f' s'] H. core_tac. destruct H as (l & lf & H1 & H2 & H3 & H4). subst.
  destruct (is_x0 r); simpl.
  - exists l, lf. repeat split; reflexivity.
  - exists ((bv_key r, v) :: l), lf. repeat split; reflexivity.
Qed.
#[using="Type"] Lemma core_rel_fset : forall r v c c', core_rel c c' -> core_rel (fset r v c) (fset r v c').
Proof.
  intros r v [S G p f s] [S' G' p' f' s'] H. core_tac. destruct H as (l & lf & H1 & H2 & H3 & H4). subst.
  exists l, ((bv_key r, v) :: lf). repeat split; reflexivity.
Qed.
#[using="Type"] Lemma core_rel_with_pc : forall v v' c c', core_rel c c' -> core_rel (with_pc v c) (with_pc v' c').
Proof. intros v v' [S G p f s] [S' G' p' f' s'] H. core_tac. exact H. Qed.
#[using="Type"] Lemma core_rel_with_fcsr : forall v v' c c', core_rel c c' -> core_rel (with_fcsr v c) (with_fcsr v' c').
Proof. intros v v' [S G p f s] [S' G' p' f' s'] H. core_tac. exact H. Qed.
#[using="Type"] Lemma core_rel_with_resv : forall v v' c c', core_rel c c' -> core_rel (with_resv v c) (with_resv v' c').
Proof. intros v v' [S G p f s] [S' G' p' f' s'] H. core_tac. exact H. Qed.
#[using="Type"] Lemma core_rel_accrue : forall fl fl' c c', core_rel c c' -> core_rel (accrue fl c) (accrue fl' c').
Proof. intros fl fl' [S G p f s] [S' G' p' f' s'] H. core_tac. exact H. Qed.
#[using="Type"] Lemma core_rel_fwrite : forall fmt r v c c', core_rel c c' -> core_rel (fwrite fmt r v c) (fwrite fmt r v c').
Proof. intros fmt r v c c' H. destruct fmt; apply core_rel_fset; exact H. Qed.
#[using="Type"] Lemma core_rel_inval_resv : forall a a' c c', core_rel c c' -> core_rel (inval_resv a c) (inval_resv a' c').
Proof.
  intros a a' [S G p f s] [S' G' p' f' s'] H. core_tac.
  destruct s as [r|]; [destruct (Z.eqb _ _)|]; (destruct s' as [r'|]; [destruct (Z.eqb _ _)|]); simpl; exact H.
Qed.
#[using="Type"] Lemma core_rel_if : forall (b : bool) c1 c1' c2 c2',
  core_rel c1 c1' -> core_rel c2 c2' -> core_rel (if b then c1 else c2) (if b then c1' else c2').
Proof. intros [] c1 c1' c2 c2' H1 H2; assumption. Qed.

Local Ltac solve_core :=
  repeat first [ apply core_rel_rset | apply core_rel_fset | apply core_rel_with_pc
               | apply core_rel_with_fcsr | apply core_rel_with_resv | apply core_rel_accrue
               | apply core_rel_fwrite | apply core_rel_inval_resv | apply core_rel_if
               | match goal with |- core_rel (match ?X with _ => _ end) _ => destruct X end ];
  apply core_rel_mk.

Local Ltac rel_struct :=
  repeat first
    [ apply RelDone; solve_core
    | apply RelIllegal | apply RelDefIllegal | apply RelEcall | apply RelEbreak | apply RelFault
    | apply RelLoad; intros ?
    | apply RelStore
    | match goal with |- eff_rel (match ?X with _ => _ end) _ => destruct X end
    | match goal with |- eff_rel (match ?X with _ => _ end _) _ => destruct X end ].

Local Ltac unfold_exec :=
  cbv beta iota zeta delta [exec rget fget fread c_regs c_fregs c_pc c_fcsr c_resv
                            with_pc load_val store_val exec_csr resolve_rm frm_of].

(* [comment removed for export] *)
#[using="Type"] Lemma exec_rel_core : forall pc fc rv sz i,
  regs_eqv0 R R' -> regs_eqv F F' ->
  eff_rel (exec sz i (Core R F pc fc rv)) (exec sz i (Core R' F' pc fc rv)).
Proof.
  intros pc fc rv sz i HR HF.
  destruct i; unfold_exec; rewrite ?(rget_if_eqv0 R R' HR), ?HF; rel_struct.
Qed.

Section WithSegsI.
Variable segs : list Segment.

#[using="Type"] Lemma interp_eff_accesses_rel : forall t t', eff_rel t t' -> forall m,
  match interp_eff_accesses segs t m, interp_eff_accesses segs t' m with
  | MachineOk rep, MachineOk rep' => core_rel (fst (access_value _ rep)) (fst (access_value _ rep'))
  | _, _ => True
  end.
Proof.
  intros t t' H. induction H; intros m; cbn [interp_eff_accesses access_value accessed_ranges fst snd]; auto.
  - destruct (ov_read_bytes segs m a (width_bytes n)) as [bs|]; [|exact I].
    match goal with |- context [interp_eff_accesses segs (k ?x) m] => pose proof (H0 x m) as K end.
    destruct (interp_eff_accesses segs (k _) m) as [rep| |]; [|exact I|exact I].
    destruct (interp_eff_accesses segs (k' _) m) as [rep'| |]; [|exact I|exact I].
    cbn [access_value accessed_ranges] in *. exact K.
  - destruct (store_ok segs m a (width_bytes n)); [|exact I].
    match goal with |- context [interp_eff_accesses segs k ?x] => pose proof (IHeff_rel x) as K end.
    destruct (interp_eff_accesses segs k _) as [rep| |]; [|exact I|exact I].
    destruct (interp_eff_accesses segs k' _) as [rep'| |]; [|exact I|exact I].
    cbn [access_value accessed_ranges] in *. exact K.
Qed.
End WithSegsI.
End Shape.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition ms_rel (a a' b b' : machine_state) : Prop :=
  exists l lf, ms_regs b = tsets l (ms_regs a) /\ ms_regs b' = tsets l (ms_regs a')
               /\ ms_fregs b = tsets lf (ms_fregs a) /\ ms_fregs b' = tsets lf (ms_fregs a').

Section WithSegs.
Variable segs : list Segment.

Definition ares_rel (a a' : machine_state) (r r' : machine_result (access_report machine_state)) : Prop :=
  match r, r' with
  | MachineOk rep, MachineOk rep' => ms_rel a a' (access_value _ rep) (access_value _ rep')
  | _, _ => True
  end.

#[using="Type"] Lemma decode_exec_accesses_rel : forall ms ms' w, ms_eqv ms ms' ->
  ares_rel ms ms' (decode_exec_accesses segs ms w) (decode_exec_accesses segs ms' w).
Proof.
  intros ms ms' w Heqv.
  destruct ms as [R F pc svc rv fc m ro], ms' as [R' F' pc' svc' rv' fc' m' ro'].
  destruct Heqv as (HR & HF & Hpc & Hsvc & Hrv & Hfc & Hm & Hro); simpl in *; subst.
  unfold decode_exec_accesses. destruct (is_ecall w).
  - simpl. exists [], []. repeat split; reflexivity.
  - destruct (decode_any w) as [[i isz]|]; [| destruct (is_defined_illegal w); exact I]. simpl.
    pose proof (interp_eff_accesses_rel R R' F F' segs _ _ (exec_rel_core R R' F F' pc' fc' rv' (Z_to_bv 64 isz) i HR HF) m') as K.
    destruct (interp_eff_accesses segs (exec _ i (Core R F pc' fc' rv')) m') as [[[c m1] rs]| |];
    destruct (interp_eff_accesses segs (exec _ i (Core R' F' pc' fc' rv')) m') as [[[c' m1'] rs']| |];
    simpl in *; try exact I.
    destruct K as (l & lf & K1 & K2 & K3 & K4). exists l, lf. simpl. repeat split; assumption.
Qed.

#[using="Type"] Lemma step_accesses_rel : forall ms ms', ms_eqv ms ms' ->
  ares_rel ms ms' (RiscvSemantics.step_accesses segs ms) (RiscvSemantics.step_accesses segs ms').
Proof.
  intros ms ms' Heqv. pose proof Heqv as (_ & _ & Hpc & _ & _ & _ & Hm & _).
  unfold RiscvSemantics.step_accesses, ms_pc. rewrite <- Hpc, <- Hm.
  destruct (fetch_word segs (ms_pc_val ms)); [apply decode_exec_accesses_rel; exact Heqv|].
  destruct (fetch_word_ov segs (ms_mem ms) (ms_pc_val ms)); [apply decode_exec_accesses_rel; exact Heqv|].
  destruct (fetch_tail_any segs (ms_mem ms) (ms_pc_val ms)); [apply decode_exec_accesses_rel; exact Heqv|].
  unfold fetch_failure. destruct (negb _); [exact I|]. destruct (_ || _)%bool; exact I.
Qed.

#[using="Type"] Lemma mi_account_step_rel : forall ms ms' mo mo', ms_eqv ms ms' ->
  match mi_account_step segs ms mo, mi_account_step segs ms' mo' with
  | MachineOk (a, _), MachineOk (b, _) => ms_rel ms ms' a b
  | _, _ => True
  end.
Proof.
  intros ms ms' mo mo' Heqv. pose proof (step_accesses_rel ms ms' Heqv) as H.
  unfold mi_account_step.
  destruct (RiscvSemantics.step_accesses segs ms) as [rep| |]; destruct (RiscvSemantics.step_accesses segs ms') as [rep'| |];
    cbn in H; try exact I;
    repeat match goal with |- context [materialize_model_accesses ?m ?r] => destruct (materialize_model_accesses m r) end;
    try exact I; exact H.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma ms_eq_fields : forall a b : machine_state,
  ms_regs a = ms_regs b -> ms_fregs a = ms_fregs b -> ms_pc_val a = ms_pc_val b -> ms_svc_pending a = ms_svc_pending b ->
  ms_resv a = ms_resv b -> ms_fcsr a = ms_fcsr b -> ms_mem a = ms_mem b -> ms_rom a = ms_rom b -> a = b.
Proof. intros [] []; cbn; intros; subst; reflexivity. Qed.

#[using="Type"] Lemma to_spin_eqv : forall ms model, to_spin segs ms model -> forall ms', ms_eqv ms ms' -> to_spin segs ms' model.
Proof.
  induction 1 as [ms model Hsvc Hfix | ms model ms1 model1 Hsvc Hst Hspin IH]; intros ms' Heqv.
  - (* [comment removed for export] *)
    pose proof (mi_account_step_eqv segs ms ms' model Heqv) as K. rewrite Hfix in K.
    destruct (mi_account_step segs ms' model) as [[ms1' mo1']| |] eqn:E1; cbn in K; try contradiction.
    destruct K as [H1 <-].
    pose proof (mi_account_step_eqv segs ms ms1' model H1) as K2. rewrite Hfix in K2.
    destruct (mi_account_step segs ms1' model) as [[ms2' mo2']| |] eqn:E2; cbn in K2; try contradiction.
    destruct K2 as [H2 <-].
    assert (Heq' : ms_eqv ms' ms1') by (eapply ms_eqv_trans; [apply ms_eqv_sym; exact Heqv | exact H1]).
    pose proof (mi_account_step_rel ms' ms1' model model Heq') as S. rewrite E1, E2 in S.
    destruct S as (l & lf & S1 & S2 & S3 & S4).
    pose proof H1 as (_ & _ & P1 & P2 & P3 & P4 & P5 & P6). pose proof H2 as (_ & _ & Q1 & Q2 & Q3 & Q4 & Q5 & Q6).
    assert (EQ : ms2' = ms1').
    { apply ms_eq_fields; try congruence.
      - rewrite S2, S1. apply tsets_idem.
      - rewrite S4, S3. apply tsets_idem. }
    subst ms2'.
    pose proof Heqv as (_ & _ & _ & V & _).
    eapply ts_step; [congruence | exact E1 |]. apply ts_spin; [congruence | exact E2].
  - pose proof (mi_account_step_eqv segs ms ms' model Heqv) as K. rewrite Hst in K.
    destruct (mi_account_step segs ms' model) as [[ms1' mo1']| |] eqn:E1; cbn in K; try contradiction.
    destruct K as [H1 <-]. pose proof Heqv as (_ & _ & _ & V & _).
    eapply ts_step; [congruence | exact E1 | exact (IH ms1' H1)].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma cfg_eqv_refl : forall c, cfg_eqv c c.
Proof. intros [ms mo]. split; [apply ms_eqv_refl | reflexivity]. Qed.

#[using="Type"] Lemma cfg_eqv_trans : forall a b c, cfg_eqv a b -> cfg_eqv b c -> cfg_eqv a c.
Proof.
  intros [? ?] [? ?] [? ?] [H1 H2] [G1 G2]; cbn in *. split; [eapply ms_eqv_trans; eassumption | etransitivity; eassumption].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma sstep_next_eqv : forall c c' e c2,
  cfg_eqv c c' -> sstep_cfg segs CFG c e (SNext c2) -> exists c2', sstep_cfg segs CFG c' e (SNext c2') /\ cfg_eqv c2 c2'.
Proof.
  intros c c' e c2 Heqv Hss.
  destruct (sstepC_cfg_eqv segs CFG c c' e (SNext c2) Heqv Hss) as (X' & Hss' & HX).
  destruct X' as [c2'| ]; cbn in HX; [|contradiction].
  exists c2'. split; assumption.
Qed.

#[using="Type"] Theorem srealizes_eqv : forall c T, srealizes segs c T -> forall c', cfg_eqv c c' -> srealizes segs c' T.
Proof.
  intros c T H.
  induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh | c Hspin Hh | c T T' H IH Heq]; intros c' Heqv.
  - (* [comment removed for export] *)
    destruct Hnode as [Hfwd Hexact].
    set (I' := { p : I * config | sstep_cfg segs CFG c' (evs (fst p)) (SNext (snd p)) /\ cfg_eqv (nx (fst p)) (snd p) }).
    destruct (sstep_next_eqv c c' (evs i0) (nx i0) Heqv (Hfwd i0)) as (c20 & Hs0 & He0).
    pose (q0 := (exist _ (i0, c20) (conj Hs0 He0) : I')).
    apply (srz_conseq segs c' (t_alt (fun q : I' => t_emit (evs (fst (proj1_sig q))) (T (fst (proj1_sig q)))))).
    + apply (srz_node segs c' I' (fun q => evs (fst (proj1_sig q))) (fun q => snd (proj1_sig q))
                      (fun q => T (fst (proj1_sig q))) q0).
      * split.
        -- intros [[i c2] [Hs He]]. cbn. exact Hs.
        -- intros e st Hss.
           destruct (sstepC_cfg_eqv segs CFG c' c e st (cfg_eqv_sym c c' Heqv) Hss) as (X & HssX & HX).
           destruct (Hexact e X HssX) as (j & -> & ->).
           destruct st as [c2|]; cbn in HX; [|contradiction].
           exists (exist _ (j, c2) (conj Hss (cfg_eqv_sym _ _ HX))). cbn. split; reflexivity.
      * intros [[i c2] [Hs He]]. cbn. exact (IH i c2 He).
    + (* [comment removed for export] *)
      intros tr. split.
      * intros [[[i c2] [Hs He]] Ht]. cbn in Ht. exists i. exact Ht.
      * intros [i Ht].
        destruct (sstep_next_eqv c c' (evs i) (nx i) Heqv (Hfwd i)) as (c2 & Hs & He).
        exists (exist _ (i, c2) (conj Hs He)). cbn. exact Ht.
  - (* [comment removed for export] *)
    apply srz_halt. destruct Heqv as [_ Hmo]. rewrite <- Hmo. exact Hh.
  - (* [comment removed for export] *)
    destruct Hspin as [[] _].
  - (* [comment removed for export] *)
    eapply srz_conseq; [apply IH; exact Heqv | exact Heq].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma mkst_MS : forall R pc m ro,
  @OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec.mkst OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec.fx0 R pc m ro
  = MS R bvmap_empty pc (Z_to_bv 32 0) None m ro.
Proof. reflexivity. Qed.

#[using="Type"] Lemma cfg_eqv_regs : forall R R' F pc fc rv m ro mo,
  regs_eqv0 R R' -> cfg_eqv (mkCfg (MS R F pc fc rv m ro) mo) (mkCfg (MS R' F pc fc rv m ro) mo).
Proof.
  intros. split; [|reflexivity]. split; [assumption|]. split; [apply regs_eqv_refl|]. repeat split; reflexivity.
Qed.

End WithSegs.
End TwB.
End SrzEqv.
