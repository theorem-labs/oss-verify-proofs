(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import IndefiniteDescription.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec ShapeAlg SpinAlg DivergeSim.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib.CJ.Lib Require Import MState Frame.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import BMode.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition regs_eqv (R R' : bvmap 5 word) : Prop :=
  forall r : reg, is_x0 r = false -> reg_get R r = reg_get R' r.

Lemma regs_eqv_refl : forall R, regs_eqv R R.
Proof. intros R r _. reflexivity. Qed.
Lemma regs_eqv_sym : forall R R', regs_eqv R R' -> regs_eqv R' R.
Proof. intros R R' H r Hr. symmetry. apply H, Hr. Qed.
Lemma regs_eqv_trans : forall R1 R2 R3, regs_eqv R1 R2 -> regs_eqv R2 R3 -> regs_eqv R1 R3.
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
Proof. intros R R' k v H r Hr. rewrite !reg_get_set. destruct (bv_eqb k r); [reflexivity|apply H, Hr]. Qed.

Lemma is_x0_bv_eqb : forall r : reg, is_x0 r = bv_eqb r 0.
Proof. intros r. unfold is_x0, bv_eqb. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition core_eqv (c c' : core) : Prop :=
  regs_eqv (c_regs c) (c_regs c') /\ c_fregs c = c_fregs c' /\
  c_pc c = c_pc c' /\ c_fcsr c = c_fcsr c' /\ c_resv c = c_resv c'.

Inductive eff_eqv : eff -> eff -> Prop :=
| EqvDone : forall c c', core_eqv c c' -> eff_eqv (EDone c) (EDone c')
| EqvIllegal : forall c c', eff_eqv (EIllegal c) (EIllegal c')
| EqvDefIllegal : forall c c', eff_eqv (EDefinedIllegal c) (EDefinedIllegal c')   (* [comment removed for export] *)
| EqvEcall : forall c c', eff_eqv (EEcall c) (EEcall c')
| EqvEbreak : forall c c', eff_eqv (EEbreak c) (EEbreak c')
| EqvFault : forall c c', eff_eqv (EFault c) (EFault c')
| EqvLoad : forall n a k k', (forall v, eff_eqv (k v) (k' v)) -> eff_eqv (ELoad n a k) (ELoad n a k')
| EqvStore : forall n a v k k', eff_eqv k k' -> eff_eqv (EStore n a v k) (EStore n a v k').

Lemma core_eqv_mk : forall R R' F pc fc rv, regs_eqv R R' ->
  core_eqv (Core R F pc fc rv) (Core R' F pc fc rv).
Proof. intros. repeat split; assumption. Qed.

Lemma rget_eqv : forall c c' r, core_eqv c c' -> rget c r = rget c' r.
Proof.
  intros c c' r (HR & _). unfold rget. destruct (is_x0 r) eqn:E; [reflexivity|]. apply HR, E.
Qed.
Lemma fget_eqv : forall c c' r, core_eqv c c' -> fget c r = fget c' r.
Proof. intros c c' r (_ & HF & _). unfold fget. rewrite HF. reflexivity. Qed.
Lemma fread_eqv : forall c c' fmt r, core_eqv c c' -> fread c fmt r = fread c' fmt r.
Proof. intros c c' fmt r H. unfold fread. rewrite (fget_eqv c c' r H). reflexivity. Qed.
Lemma c_pc_eqv : forall c c', core_eqv c c' -> c_pc c = c_pc c'.
Proof. intros c c' (_ & _ & H & _). exact H. Qed.
Lemma c_fcsr_eqv : forall c c', core_eqv c c' -> c_fcsr c = c_fcsr c'.
Proof. intros c c' (_ & _ & _ & H & _). exact H. Qed.
Lemma c_resv_eqv : forall c c', core_eqv c c' -> c_resv c = c_resv c'.
Proof. intros c c' (_ & _ & _ & _ & H). exact H. Qed.

Local Ltac core_tac :=
  unfold core_eqv, rset, fset, with_regs, with_fregs, with_pc, with_fcsr, with_resv,
         accrue, fwrite, inval_resv in *; simpl in *.

Lemma core_eqv_rset : forall r v c c', core_eqv c c' -> core_eqv (rset r v c) (rset r v c').
Proof.
  intros r v [R F p f s] [R' F' p' f' s'] H. core_tac. destruct H as (HR & -> & -> & -> & ->).
  destruct (is_x0 r); simpl; repeat split; auto using regs_eqv_set.
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
  first [ apply (core_eqv_mk _ _ _ _ _ _ HR) | assumption ].

Local Ltac eqv_struct HR :=
  repeat first
    [ apply EqvDone; solve_core HR
    | apply EqvIllegal | apply EqvDefIllegal | apply EqvEcall | apply EqvEbreak | apply EqvFault
    | apply EqvLoad; intros ?
    | apply EqvStore
    | match goal with |- eff_eqv (match ?X with _ => _ end) _ => destruct X end
    | match goal with |- eff_eqv (match ?X with _ => _ end _) _ => destruct X end ].

(* [comment removed for export] *)
Local Ltac unfold_exec :=
  cbv beta iota zeta delta [exec fget fread c_regs c_fregs c_pc c_fcsr c_resv
                            with_pc load_val store_val exec_csr resolve_rm frm_of].

Lemma rget_eqvR : forall R R', regs_eqv R R' -> forall F pc fc rv r,
  rget (Core R F pc fc rv) r = rget (Core R' F pc fc rv) r.
Proof. intros R R' HR F pc fc rv r. apply rget_eqv. apply core_eqv_mk. exact HR. Qed.

Lemma exec_eqv_core : forall R R' F pc fc rv sz i,
  regs_eqv R R' ->
  eff_eqv (exec sz i (Core R F pc fc rv)) (exec sz i (Core R' F pc fc rv)).
Proof.
  intros R R' F pc fc rv sz i HR.
  destruct i; unfold_exec; rewrite ?(rget_eqvR R R' HR); eqv_struct HR.
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
  regs_eqv (ms_regs ms) (ms_regs ms') /\ ms_fregs ms = ms_fregs ms' /\
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
Variable segs : list Segment. Context {bmK : BMode}.   (* [comment removed for export] *)

Definition ares_eqv (r r' : machine_result (access_report machine_state)) : Prop :=
  match r, r' with
  | MachineOk a, MachineOk b => ms_eqv (@access_value _ a) (@access_value _ b) /\ @accessed_ranges _ a = @accessed_ranges _ b
  | MachineFault, MachineFault => True
  | MachineUnmodeled, MachineUnmodeled => True
  | _, _ => False
  end.

Lemma interp_eff_accesses_eqv : forall t t', eff_eqv t t' -> forall m,
  match interp_eff_accesses segs t m, interp_eff_accesses segs t' m with
  | MachineOk a, MachineOk b => core_eqv (fst (@access_value _ a)) (fst (@access_value _ b))
                                /\ snd (@access_value _ a) = snd (@access_value _ b)
                                /\ @accessed_ranges _ a = @accessed_ranges _ b
  | MachineFault, MachineFault => True
  | MachineUnmodeled, MachineUnmodeled => True
  | _, _ => False
  end.
Proof.
  intros t t' H. induction H; intros m; cbn [interp_eff_accesses]; auto.
  - destruct (ov_read_bytes segs m a (width_bytes n)) as [bs|]; [| exact I].
    specialize (H0 (bv_extract 0 n (le_bytes_to_word bs)) m).
    destruct (interp_eff_accesses segs (k _) m) as [[[c1 m1] acc1]| |];
    destruct (interp_eff_accesses segs (k' _) m) as [[[c2 m2] acc2]| |]; cbn in *; try exact H0; try contradiction.
    destruct H0 as (A & B & C). subst. split; [exact A|]. split; reflexivity.
  - destruct (store_ok segs m a (width_bytes n)); [| exact I].
    specialize (IHeff_eqv (write_to_mem m a (Z_to_le_bytes (width_bytes n) (bv_unsigned v)))).
    destruct (interp_eff_accesses segs k _) as [[[c1 m1] acc1]| |];
    destruct (interp_eff_accesses segs k' _) as [[[c2 m2] acc2]| |]; cbn in *; try exact IHeff_eqv; try contradiction.
    destruct IHeff_eqv as (A & B & C). subst. split; [exact A|]. split; reflexivity.
Qed.

Lemma ms_reg17_eqv : forall ms ms', ms_eqv ms ms' -> ms_reg ms 17 = ms_reg ms' 17.
Proof. intros ms ms' (HR & _). unfold ms_reg. cbn. apply HR. reflexivity. Qed.

Lemma decode_exec_accesses_eqv : forall ms ms' w, ms_eqv ms ms' ->
  ares_eqv (decode_exec_accesses segs ms w) (decode_exec_accesses segs ms' w).
Proof.
  intros ms ms' w Heqv. pose proof (ms_reg17_eqv ms ms' Heqv) as H17.
  destruct ms as [R F pc svc rv fc m ro], ms' as [R' F' pc' svc' rv' fc' m' ro'].
  destruct Heqv as (HR & HF & Hpc & Hsvc & Hrv & Hfc & Hm & Hro); simpl in *; subst.
  unfold RiscvSemantics.decode_exec_accesses. destruct (is_ecall w).
  - simpl. rewrite H17. repeat split; assumption.
  - destruct (decode_any w) as [[i isz]|]; [| destruct (is_defined_illegal w); exact I]. simpl.
    pose proof (interp_eff_accesses_eqv _ _ (exec_eqv_core R R' F' pc' fc' rv' (Z_to_bv 64 isz) i HR) m') as K.
    destruct (interp_eff_accesses segs (exec _ i (Core R F' pc' fc' rv')) m') as [[[c m1] acc1]| |];
    destruct (interp_eff_accesses segs (exec _ i (Core R' F' pc' fc' rv')) m') as [[[c' m1'] acc2]| |];
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
  unfold fetch_failure. destruct (negb _); [exact I|]. destruct (_ || _)%bool; exact I.
Qed.

Lemma step_eqv : forall ms ms', ms_eqv ms ms' ->
  res_eqv (RiscvSemantics.step segs ms) (RiscvSemantics.step segs ms').
Proof.
  intros ms ms' Heqv. unfold RiscvSemantics.step, RiscvSemantics.drop_access_report.
  pose proof (step_accesses_eqv ms ms' Heqv) as K.
  destruct (RiscvSemantics.step_accesses segs ms) as [a| |], (RiscvSemantics.step_accesses segs ms') as [b| |];
    cbn in *; try exact K; try contradiction. exact (proj1 K).
Qed.

(* [comment removed for export] *)
Definition res2_eqv (r r' : machine_result (machine_state * Model)) : Prop :=
  match r, r' with
  | MachineOk (a, mo), MachineOk (b, mo') => ms_eqv a b /\ mo = mo'
  | MachineFault, MachineFault => True
  | MachineUnmodeled, MachineUnmodeled => True
  | _, _ => False
  end.

Lemma mi_account_step_eqv : forall ms ms' mo, ms_eqv ms ms' ->
  res2_eqv (mi_account_step segs ms mo) (mi_account_step segs ms' mo).
Proof.
  intros ms ms' mo Heqv. unfold mi_account_step.
  pose proof (step_accesses_eqv ms ms' Heqv) as K.
  destruct (RiscvSemantics.step_accesses segs ms) as [a| |], (RiscvSemantics.step_accesses segs ms') as [b| |];
    cbn in *; try exact K; try contradiction.
  destruct K as [K1 <-]. destruct (materialize_model_accesses mo (accessed_ranges machine_state a)); [|exact I].
  split; [exact K1|reflexivity].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma syscall_args_eqv : forall ms ms', ms_eqv ms ms' -> syscall_args ms = syscall_args ms'.
Proof. intros ms ms' (HR & _). unfold syscall_args, ms_gpr. rewrite !HR by reflexivity. reflexivity. Qed.

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

Lemma cfg_eqv_refl : forall c, cfg_eqv c c.
Proof. intros c. split; [apply ms_eqv_refl| reflexivity]. Qed.
Lemma cfg_eqv_sym : forall c c', cfg_eqv c c' -> cfg_eqv c' c.
Proof. intros c c' [H1 H2]. split; [apply ms_eqv_sym; exact H1| congruence]. Qed.
Lemma cfg_eqv_trans : forall a b c, cfg_eqv a b -> cfg_eqv b c -> cfg_eqv a c.
Proof. intros a b c [H1 H2] [G1 G2]. split; [eapply ms_eqv_trans; eassumption| congruence]. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma msteps_eqv : forall ms ms1, CatSim.msteps segs ms ms1 ->
  forall ms', ms_eqv ms ms' -> exists ms1', CatSim.msteps segs ms' ms1' /\ ms_eqv ms1 ms1'.
Proof.
  intros ms ms1 H. induction H as [ms | ms msa msb Hsvc Hstep Hms IH]; intros ms' Heqv.
  - exists ms'. split; [apply CatSim.mst_refl| exact Heqv].
  - pose proof (step_eqv ms ms' Heqv) as K. rewrite Hstep in K.
    destruct (RiscvSemantics.step segs ms') as [msa'| |] eqn:E; simpl in K; try contradiction.
    destruct (IH msa' K) as (msb' & Hms' & Hb).
    exists msb'. split; [|exact Hb].
    eapply CatSim.mst_step; [| exact E | exact Hms'].
    destruct Heqv as (_ & _ & _ & Hs & _). congruence.
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

Definition canon_regs (R : bvmap 5 word) : bvmap 5 word :=
  mkR (getr R 1) (getr R 2) (getr R 3) (getr R 4) (getr R 5) (getr R 6) (getr R 7) (getr R 8)
      (getr R 9) (getr R 10) (getr R 11) (getr R 12) (getr R 13) (getr R 14) (getr R 15) (getr R 16)
      (getr R 17) (getr R 18) (getr R 19) (getr R 20) (getr R 21) (getr R 22) (getr R 23) (getr R 24)
      (getr R 25) (getr R 26) (getr R 27) (getr R 28) (getr R 29) (getr R 30) (getr R 31).

Lemma canon_regs_eqv : forall R, regs_eqv R (canon_regs R).
Proof.
  intros R r Hr. destruct (reg_of_nat r) as (n & -> & Hn).
  do 32 (destruct n as [|n]; [first [discriminate Hr | (unfold canon_regs, getr; cbn; reflexivity)] |]). lia.
Qed.

(* [comment removed for export] *)
Lemma getr_eqv : forall R R' r, regs_eqv R R' -> getr R r = getr R' r.
Proof.
  intros R R' r H. unfold getr. rewrite <- is_x0_bv_eqb. destruct (is_x0 r) eqn:E; [reflexivity|]. apply H, E.
Qed.

