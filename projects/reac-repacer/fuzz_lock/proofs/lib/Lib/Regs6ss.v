(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/varnish/esi_parse_fuzzer/lib/Lib/Regs6ss.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the vvar test on failed loads and the vDSO arms of the step carried through register equivalence). *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.Lib Require Import PropExec MState Frame.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.Lib Require Import Acfg.
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
  - destruct (ov_read_bytes segs m a (width_bytes n)) as [bs|]; [|destruct (range_meets_vvar segs a (width_bytes n)); exact I].
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
  unfold fetch_failure.
  repeat match goal with |- context [if ?b then _ else _] => destruct b end; exact I.
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

Lemma mi_account_step_eqv : forall ms ms' mo, ms_eqv ms ms' ->
  match mi_account_step segs ms mo, mi_account_step segs ms' mo with
  | MachineOk (a, mo1), MachineOk (b, mo2) => ms_eqv a b /\ mo1 = mo2
  | MachineFault, MachineFault => True
  | MachineUnmodeled, MachineUnmodeled => True
  | _, _ => False
  end.
Proof.
  intros ms ms' mo Heqv. pose proof (step_accesses_eqv ms ms' Heqv) as H.
  unfold mi_account_step.
  destruct (RiscvSemantics.step_accesses segs ms) as [a| |];
  destruct (RiscvSemantics.step_accesses segs ms') as [b| |]; cbn in H; try exact H; try contradiction.
  destruct H as [Hv <-].
  destruct (materialize_model_accesses mo (@accessed_ranges _ a)); [|exact I].
  split; [exact Hv|reflexivity].
Qed.

Lemma ms_sp_eqv : forall ms1 ms2, ms_eqv ms1 ms2 -> ms_sp ms1 = ms_sp ms2.
Proof. intros ms1 ms2 H. unfold ms_sp. apply (proj1 H). reflexivity. Qed.

Lemma vdso_read_regs_eqv : forall ms1 ms2, ms_eqv ms1 ms2 -> vdso_read_regs ms1 = vdso_read_regs ms2.
Proof. intros ms1 ms2 H. unfold vdso_read_regs. apply map_ext. intros r. apply ms_reg_eqv, H. Qed.

Lemma ms_read_byte_eqv : forall ms1 ms2, ms_eqv ms1 ms2 -> ms_read_byte ms1 = ms_read_byte ms2.
Proof.
  intros ms1 ms2 H. destruct H as (_ & _ & _ & _ & _ & _ & Hm & Hrom).
  unfold ms_read_byte. rewrite Hm, Hrom. reflexivity.
Qed.

Lemma set_reg_eqv : forall ms1 ms2 r v, ms_eqv ms1 ms2 -> ms_eqv (set_reg ms1 r v) (set_reg ms2 r v).
Proof.
  intros ms1 ms2 r v H. pose proof H as H0. destruct H as (HR & Hf & Hp & Hs & Hrv & Hfc & Hm & Hrom).
  unfold set_reg. destruct (bv_eqb r 0); [exact H0|].
  cbn. repeat split; cbn; auto. apply xregs_eqv_set, HR.
Qed.

Lemma vdso_write_regs_mem : forall rs vs ms, ms_mem (vdso_write_regs ms rs vs) = ms_mem ms.
Proof.
  induction rs as [|r rs IH]; intros [|v vs] ms; cbn; try reflexivity.
  rewrite IH. unfold set_reg. destruct (bv_eqb (Z_to_bv 5 r) 0); reflexivity.
Qed.

Lemma vdso_write_regs_eqv : forall rs vs ms1 ms2, ms_eqv ms1 ms2 ->
  ms_eqv (vdso_write_regs ms1 rs vs) (vdso_write_regs ms2 rs vs).
Proof.
  induction rs as [|r rs IH]; intros [|v vs] ms1 ms2 H; cbn; try exact H.
  apply IH, set_reg_eqv, H.
Qed.

Lemma vdso_with_mem_eqv : forall ms1 ms2 m, ms_eqv ms1 ms2 -> ms_eqv (vdso_with_mem ms1 m) (vdso_with_mem ms2 m).
Proof.
  intros ms1 ms2 m H. destruct H as (HR & Hf & Hp & Hs & Hrv & Hfc & Hm & Hrom).
  unfold vdso_with_mem. repeat split; cbn; auto.
Qed.

Lemma vdso_set_pc_eqv : forall ms1 ms2 pc, ms_eqv ms1 ms2 -> ms_eqv (vdso_set_pc ms1 pc) (vdso_set_pc ms2 pc).
Proof.
  intros ms1 ms2 pc H. destruct H as (HR & Hf & Hp & Hs & Hrv & Hfc & Hm & Hrom).
  unfold vdso_set_pc. repeat split; cbn; auto.
Qed.

Lemma vdso_post_eqv : forall ms1 ms2 model f eff, ms_eqv ms1 ms2 ->
  ms_eqv (vdso_post segs ms1 model f eff) (vdso_post segs ms2 model f eff).
Proof.
  intros ms1 ms2 model f eff H. pose proof H as H0.
  unfold vdso_post.
  rewrite (ms_reg_eqv _ _ 1 H0), (ms_sp_eqv _ _ H0), (vdso_read_regs_eqv _ _ H0), (ms_read_byte_eqv _ _ H0).
  apply vdso_set_pc_eqv. apply apply_effect_eqv.
  rewrite !vdso_write_regs_mem. rewrite (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 H0))))))).
  apply vdso_with_mem_eqv. apply vdso_write_regs_eqv. exact H0.
Qed.

Lemma vdso_call_unmodeled_eqv : forall ms1 ms2 model fn, ms_eqv ms1 ms2 ->
  vdso_call_unmodeled segs ms2 model fn -> vdso_call_unmodeled segs ms1 model fn.
Proof.
  intros ms1 ms2 model fn H Hu.
  destruct Hu as [Hu | [(n & Hn & Hsp) | (n & eff & model' & evs & Hn & Hsp & Hd)]].
  - left; exact Hu.
  - right; left. exists n. split; [exact Hn|]. rewrite (sys_input_eqv ms1 ms2 _ H). exact Hsp.
  - right; right. exists n, eff, model', evs. split; [exact Hn|].
    split; [rewrite (sys_input_eqv ms1 ms2 _ H); exact Hsp | exact Hd].
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

(* vDSO return states depend on the new caller's registers, so transport
   provides a related successor rather than a function of the old successor. *)
Lemma sstep_eqv : forall ms ms' mo evs X, ms_eqv ms ms' ->
  sstep_cfg segs ACFG (mkCfg ms mo) evs X ->
  exists X', sstep_cfg segs ACFG (mkCfg ms' mo) evs X' /\ to_eqv X X'.
Proof.
  intros ms ms' mo evs X Heqv Hst.
  pose proof (mi_account_step_eqv ms ms' mo Heqv) as Hres.
  pose proof Heqv as (_ & _ & Hpc & Hsvc & _ & _ & _ & _).
  assert (Hpc' : ms_pc ms' = ms_pc ms) by (unfold ms_pc; congruence).
  inversion Hst; subst.
  - match goal with H : mi_account_step segs ms mo = _ |- _ => rewrite H in Hres end.
    destruct (mi_account_step segs ms' mo) as [[ms1' mo1]| |] eqn:E; simpl in Hres; try contradiction.
    destruct Hres as [Hres Hmo]. subst mo1.
    exists (SNext (mkCfg ms1' model')). split; [apply sstep_cfg_instr; auto; congruence|]. split; [exact Hres| reflexivity].
  - match goal with H : mi_account_step segs ms mo = _ |- _ => rewrite H in Hres end.
    destruct (mi_account_step segs ms' mo) as [[ms1' mo1]| |] eqn:E; simpl in Hres; try contradiction.
    exists SError. split; [apply sstep_cfg_instr_fault; auto; congruence| exact I].
  - match goal with H : mi_account_step segs ms mo = _ |- _ => rewrite H in Hres end.
    destruct (mi_account_step segs ms' mo) as [[ms1' mo1]| |] eqn:E; simpl in Hres; try contradiction.
    exists SError. split; [|exact I].
    eapply sstep_cfg_instr_unmodeled; first [eassumption | (rewrite Hpc'; eassumption) | congruence].
  - match goal with H : mi_account_step segs ms mo = _ |- _ => rewrite H in Hres end.
    destruct (mi_account_step segs ms' mo) as [[ms1' mo1]| |] eqn:E; simpl in Hres; try contradiction.
    eexists. split.
    + eapply sstep_cfg_vdso_call;
        first [ eassumption | (rewrite Hpc'; eassumption) | congruence | (unfold ms_pc in *; congruence)
              | (rewrite <- (sys_input_eqv ms ms' _ Heqv); eassumption) ].
    + split; [apply vdso_post_eqv, Heqv | reflexivity].
  - match goal with H : mi_account_step segs ms mo = _ |- _ => rewrite H in Hres end.
    destruct (mi_account_step segs ms' mo) as [[ms1' mo1]| |] eqn:E; simpl in Hres; try contradiction.
    exists SError. split; [|exact I].
    eapply sstep_cfg_vdso_materialization_fault;
      first [ eassumption | (rewrite Hpc'; eassumption) | congruence | (unfold ms_pc in *; congruence)
            | (rewrite <- (sys_input_eqv ms ms' _ Heqv); eassumption) ].
  - match goal with H : mi_account_step segs ms mo = _ |- _ => rewrite H in Hres end.
    destruct (mi_account_step segs ms' mo) as [[ms1' mo1]| |] eqn:E; simpl in Hres; try contradiction.
    exists SError. split; [|exact I].
    eapply sstep_cfg_vdso_unmodeled;
      first [ eassumption | (rewrite Hpc'; eassumption) | congruence | (unfold ms_pc in *; congruence)
            | (eapply vdso_call_unmodeled_eqv; [apply ms_eqv_sym, Heqv | eassumption]) ].
  - exists (SNext (mkCfg (advance_past_svc (apply_effect ms' eff)) model'')). split.
    + eapply sstep_cfg_syscall;
        [eassumption | rewrite <- Hsvc; eassumption | rewrite <- (sys_input_eqv ms ms' _ Heqv); eassumption
        | rewrite <- (sys_input_eqv ms ms' _ Heqv); eassumption | eassumption | eassumption].
    + split; [| reflexivity]. apply advance_past_svc_eqv, apply_effect_eqv, Heqv.
  - exists SError. split; [|exact I].
    eapply sstep_cfg_syscall_materialization_fault;
      [eassumption | rewrite <- Hsvc; eassumption | rewrite <- (sys_input_eqv ms ms' _ Heqv); eassumption
      | rewrite <- (sys_input_eqv ms ms' _ Heqv); eassumption | eassumption | eassumption].
  - exists (SNext (mkCfg ms' model')). split.
    + eapply sstep_cfg_exit;
        [eassumption | rewrite <- Hsvc; eassumption | rewrite <- (sys_input_eqv ms ms' _ Heqv); eassumption | eassumption | eassumption].
    + split; [exact Heqv| reflexivity].
  - exists (SNext (mkCfg ms' model')). split.
    + eapply sstep_cfg_killed;
        [eassumption | rewrite <- Hsvc; eassumption | rewrite <- (sys_input_eqv ms ms' _ Heqv); eassumption | eassumption].
    + split; [exact Heqv| reflexivity].
  - exists SError. split; [|exact I].
    eapply sstep_cfg_syscall_unmodeled;
      [eassumption | rewrite <- Hsvc; eassumption | rewrite <- (sys_input_eqv ms ms' _ Heqv); eassumption].
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
