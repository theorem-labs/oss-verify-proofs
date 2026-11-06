(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsjA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsjA. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QEpW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QEpW. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWxq_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq_c1.

Import ListNotations.
Open Scope bv_scope.

Definition regs_eqv (R R' : bvmap 5 word) : Prop := forall r, reg_get R r = reg_get R' r.

Definition iregs_eqv (R R' : bvmap 5 word) : Prop := forall r, getr R r = getr R' r.
Lemma iregs_eqv_refl : forall R, iregs_eqv R R. Proof. intros R r. reflexivity. Qed.
Lemma iregs_eqv_sym : forall R R', iregs_eqv R R' -> iregs_eqv R' R. Proof. intros R R' H r. symmetry. apply H. Qed.
Lemma iregs_eqv_trans : forall R1 R2 R3, iregs_eqv R1 R2 -> iregs_eqv R2 R3 -> iregs_eqv R1 R3.
Proof. intros R1 R2 R3 H1 H2 r. etransitivity; [apply H1|apply H2]. Qed.
Lemma iregs_eqv_nz : forall R R' r, iregs_eqv R R' -> bv_eqb r 0 = false -> reg_get R r = reg_get R' r.
Proof. intros R R' r H E. specialize (H r). unfold getr in H. rewrite E in H. exact H. Qed.
Lemma rget_getr : forall R F pc fc rv r, rget (Core R F pc fc rv) r = getr R r.
Proof. intros. reflexivity. Qed.

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
- apply bv_eqb_eq in E. subst. apply reg_get_set_same.
- apply reg_get_set_other. intros ->. rewrite bv_eqb_refl in E. discriminate.
Qed.

Lemma regs_eqv_set : forall R R' (k : reg) v,
regs_eqv R R' -> regs_eqv (bvmap_set k v R) (bvmap_set k v R').
Proof. intros R R' k v H r. rewrite !reg_get_set. destruct (bv_eqb k r); [reflexivity|apply H]. Qed.
Lemma iregs_eqv_set : forall R R' (k : reg) v,
iregs_eqv R R' -> iregs_eqv (bvmap_set k v R) (bvmap_set k v R').
Proof.
intros R R' k v H r. specialize (H r). unfold getr in *. rewrite !reg_get_set.
destruct (bv_eqb r 0); [reflexivity|]. destruct (bv_eqb k r); [reflexivity| exact H].
Qed.

Definition core_eqv (c c' : core) : Prop :=
iregs_eqv (c_regs c) (c_regs c') /\ regs_eqv (c_fregs c) (c_fregs c') /\
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
| apply EqvIllegal | apply EqvEcall | apply EqvEbreak | apply EqvFault | apply EqvDefIllegal
| apply EqvLoad; intros ?
| apply EqvStore
| match goal with |- eff_eqv (match ?X with _ => _ end) _ => destruct X end
| match goal with |- eff_eqv (match ?X with _ => _ end _) _ => destruct X end ].

Local Ltac unfold_exec :=
cbv beta iota zeta delta [exec fget fread c_regs c_fregs c_pc c_fcsr c_resv
with_pc load_val store_val exec_csr resolve_rm frm_of];
rewrite ?rget_getr.

Lemma exec_eqv_core : forall R R' F F' pc fc rv sz i,
iregs_eqv R R' -> regs_eqv F F' ->
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

Definition res_eqv (r r' : machine_result machine_state) : Prop :=
match r, r' with
| MachineOk a, MachineOk b => ms_eqv a b
| MachineFault, MachineFault => True
| MachineUnmodeled, MachineUnmodeled => True
| _, _ => False
end.

Section WithSegs.
Variable segs : list Segment.

Definition areport_eqv (r r' : machine_result (access_report (core * (word -> option byte)))) : Prop :=
match r, r' with
| MachineOk a, MachineOk b =>
core_eqv (fst (@access_value _ a)) (fst (@access_value _ b)) /\ snd (@access_value _ a) = snd (@access_value _ b)
/\ @accessed_ranges _ a = @accessed_ranges _ b
| MachineFault, MachineFault => True
| MachineUnmodeled, MachineUnmodeled => True
| _, _ => False
end.

#[using="Type"] Lemma interp_eff_accesses_eqv : forall t t', eff_eqv t t' -> forall m,
areport_eqv (interp_eff_accesses segs t m) (interp_eff_accesses segs t' m).
Proof.
intros t t' H. induction H; intros m; cbn [interp_eff_accesses].
- cbn. destruct H as (A1 & A2 & A3 & A4 & A5). repeat split; assumption.
- exact I.
- exact I.
- exact I.
- exact I.
- exact I.
- destruct (ov_read_bytes segs m a (width_bytes n)) as [bs|]; [|exact I].
specialize (H0 (bv_extract 0 n (le_bytes_to_word bs)) m).
destruct (interp_eff_accesses segs (k _) m) as [r| |]; destruct (interp_eff_accesses segs (k' _) m) as [r'| |]; cbn in *; try exact H0; try contradiction.
destruct H0 as (C & M & E). split; [exact C|]. split; [exact M| rewrite E; reflexivity].
- destruct (store_ok segs m a (width_bytes n)); [|exact I].
specialize (IHeff_eqv (write_to_mem m a (Z_to_le_bytes (width_bytes n) (bv_unsigned v)))).
destruct (interp_eff_accesses segs k _) as [r| |]; destruct (interp_eff_accesses segs k' _) as [r'| |]; cbn in *; try exact IHeff_eqv; try contradiction.
destruct IHeff_eqv as (C & M & E). split; [exact C|]. split; [exact M| rewrite E; reflexivity].
Qed.

#[using="Type"] Lemma ms_reg_eqv : forall ms ms' r, ms_eqv ms ms' -> ms_reg ms r = ms_reg ms' r.
Proof. intros ms ms' r (HR & _). exact (HR r). Qed.

Definition msreport_eqv (r r' : machine_result (access_report machine_state)) : Prop :=
match r, r' with
| MachineOk a, MachineOk b => ms_eqv (@access_value _ a) (@access_value _ b) /\ @accessed_ranges _ a = @accessed_ranges _ b
| MachineFault, MachineFault => True
| MachineUnmodeled, MachineUnmodeled => True
| _, _ => False
end.

#[using="Type"] Lemma decode_exec_accesses_eqv : forall ms ms' w, ms_eqv ms ms' ->
msreport_eqv (decode_exec_accesses segs ms w) (decode_exec_accesses segs ms' w).
Proof.
intros ms ms' w Heqv. pose proof (ms_reg_eqv ms ms' 17 Heqv) as H17.
destruct ms as [R F pc svc rv fc m ro], ms' as [R' F' pc' svc' rv' fc' m' ro'].
destruct Heqv as (HR & HF & Hpc & Hsvc & Hrv & Hfc & Hm & Hro); simpl in *; subst.
unfold decode_exec_accesses. destruct (is_ecall w).
- simpl. rewrite H17. split; [| reflexivity]. repeat split; assumption.
- destruct (decode_any w) as [[i isz]|]; [| destruct (is_defined_illegal w); exact I]. simpl.
pose proof (interp_eff_accesses_eqv _ _ (exec_eqv_core R R' F F' pc' fc' rv' (Z_to_bv 64 isz) i HR HF) m') as K.
destruct (interp_eff_accesses segs (exec _ i (Core R F pc' fc' rv')) m') as [[[c m1] acc]| |];
destruct (interp_eff_accesses segs (exec _ i (Core R' F' pc' fc' rv')) m') as [[[c' m1'] acc']| |];
simpl in *; try exact K; try contradiction.
destruct K as ((H1 & H2 & H3 & H4 & H5) & -> & ->). split; [| reflexivity]. repeat split; simpl; auto.
Qed.

#[using="Type"] Lemma step_accesses_eqv : forall ms ms', ms_eqv ms ms' ->
msreport_eqv (step_accesses segs ms) (step_accesses segs ms').
Proof.
intros ms ms' Heqv. pose proof Heqv as (_ & _ & Hpc & _ & _ & _ & Hm & _).
unfold step_accesses, ms_pc. rewrite <- Hpc, <- Hm.
destruct (fetch_word segs (ms_pc_val ms)); [apply decode_exec_accesses_eqv; exact Heqv|].
destruct (fetch_word_ov segs (ms_mem ms) (ms_pc_val ms)); [apply decode_exec_accesses_eqv; exact Heqv|].
destruct (fetch_tail_any segs (ms_mem ms) (ms_pc_val ms)); [apply decode_exec_accesses_eqv; exact Heqv|].
unfold fetch_failure. destruct (negb _); [exact I|]. destruct (_ || _)%bool; exact I.
Qed.

Definition mres_eqv (r r' : machine_result (machine_state * Model)) : Prop :=
match r, r' with
| MachineOk (a, md), MachineOk (b, md') => ms_eqv a b /\ md = md'
| MachineFault, MachineFault => True
| MachineUnmodeled, MachineUnmodeled => True
| _, _ => False
end.

#[using="Type"] Lemma mi_account_step_eqv : forall ms ms' md, ms_eqv ms ms' ->
mres_eqv (mi_account_step segs ms md) (mi_account_step segs ms' md).
Proof.
intros ms ms' md Heqv. unfold mi_account_step. cbn zeta.
pose proof (step_accesses_eqv ms ms' Heqv) as K.
destruct (step_accesses segs ms) as [r| |]; destruct (step_accesses segs ms') as [r'| |]; cbn in K; try contradiction; try exact I.
destruct K as [E <-]. destruct (materialize_model_accesses md (accessed_ranges machine_state r)); [| exact I].
split; [exact E| reflexivity].
Qed.

#[using="Type"] Lemma syscall_args_eqv : forall ms ms', ms_eqv ms ms' -> syscall_args ms = syscall_args ms'.
Proof. intros ms ms' (HR & _). unfold syscall_args, ms_gpr. rewrite !(iregs_eqv_nz _ _ _ HR) by reflexivity. reflexivity. Qed.

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
unfold apply_effect, set_reg; simpl. repeat split; simpl; auto using iregs_eqv_set.
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
Proof. intros c. split; [apply ms_eqv_refl| reflexivity]. Qed.
#[using="Type"] Lemma cfg_eqv_sym : forall c c', cfg_eqv c c' -> cfg_eqv c' c.
Proof. intros c c' [H1 H2]. split; [apply ms_eqv_sym; exact H1| congruence]. Qed.
#[using="Type"] Lemma cfg_eqv_trans : forall a b c, cfg_eqv a b -> cfg_eqv b c -> cfg_eqv a c.
Proof. intros a b c [H1 H2] [G1 G2]. split; [eapply ms_eqv_trans; eassumption| congruence]. Qed.

Definition to_eqv (X X' : step_to) : Prop :=
match X, X' with
| SError, SError => True
| SNext c, SNext c' => cfg_eqv c c'
| _, _ => False
end.

#[using="Type"] Lemma sstep_eqv : forall ms ms' mo evs X, ms_eqv ms ms' ->
sstep_cfg segs (alloc_only_cfg false) (mkCfg ms mo) evs X ->
exists X', sstep_cfg segs (alloc_only_cfg false) (mkCfg ms' mo) evs X' /\ to_eqv X X'.
Proof.
intros ms ms' mo evs X Heqv Hst.
pose proof (mi_account_step_eqv ms ms' mo Heqv) as Hres.
pose proof Heqv as (_ & _ & _ & Hsvc & _ & _ & _ & _).
pose proof (fun x8 => sys_input_eqv ms ms' x8 Heqv) as Hin.
inversion Hst; subst.
- lazymatch goal with HS : mi_account_step _ ms mo = MachineOk (?ms1, ?md1) |- _ =>
rewrite HS in Hres; destruct (mi_account_step segs ms' mo) as [[ms1' md1']| |] eqn:E; simpl in Hres; try contradiction;
destruct Hres as [Hres <-];
exists (SNext (mkCfg ms1' md1)); split; [apply sstep_cfg_instr; auto; congruence|]; split; [exact Hres| reflexivity] end.
- lazymatch goal with HS : mi_account_step _ ms mo = MachineFault |- _ =>
rewrite HS in Hres; destruct (mi_account_step segs ms' mo) as [[ms1' md1']| |] eqn:E; simpl in Hres; try contradiction end.
exists SError. split; [apply sstep_cfg_instr_fault; auto; congruence| exact I].
- lazymatch goal with HS : mi_account_step _ ms mo = MachineUnmodeled |- _ =>
rewrite HS in Hres; destruct (mi_account_step segs ms' mo) as [[ms1' md1']| |] eqn:E; simpl in Hres; try contradiction end.
exists SError. split; [apply sstep_cfg_instr_unmodeled; auto; congruence| exact I].
- exists (SNext (mkCfg (advance_past_svc (apply_effect ms' eff)) model'')). split.
+ eapply (sstep_cfg_syscall segs _ ms' mo x8);
[eassumption| congruence| rewrite <- (Hin x8); eassumption| rewrite <- (Hin x8); eassumption| eassumption| eassumption].
+ split; [| reflexivity]. apply advance_past_svc_eqv, apply_effect_eqv, Heqv.
- exists SError. split; [| exact I].
eapply (sstep_cfg_syscall_materialization_fault segs _ ms' mo x8);
[eassumption| congruence| rewrite <- (Hin x8); eassumption| rewrite <- (Hin x8); eassumption| eassumption| eassumption].
- exists (SNext (mkCfg ms' model')). split.
+ eapply (sstep_cfg_exit segs _ ms' mo x8); [eassumption| congruence| rewrite <- (Hin x8); eassumption| eassumption| eassumption].
+ split; [exact Heqv| reflexivity].
- exists (SNext (mkCfg ms' model')). split.
+ eapply (sstep_cfg_killed segs _ ms' mo x8); [eassumption| congruence| rewrite <- (Hin x8); eassumption| eassumption].
+ split; [exact Heqv| reflexivity].
- exists SError. split; [|exact I].
eapply (sstep_cfg_syscall_unmodeled segs _ ms' mo x8); [eassumption| congruence| rewrite <- (Hin x8); eassumption].
Qed.

#[using="Type"] Lemma sstep_cfg_eqv : forall c c' evs X, cfg_eqv c c' ->
sstep_cfg segs (alloc_only_cfg false) c evs X ->
exists X', sstep_cfg segs (alloc_only_cfg false) c' evs X' /\ to_eqv X X'.
Proof.
intros [ms mo] [ms' mo'] evs X [Hms Hmo] Hst; simpl in Hms, Hmo; subst.
apply (sstep_eqv ms ms'); assumption.
Qed.

#[using="Type"] Lemma star_eqv : forall c tr c1, star_cfg segs (alloc_only_cfg false) c tr c1 ->
forall c', cfg_eqv c c' -> exists c1', star_cfg segs (alloc_only_cfg false) c' tr c1' /\ cfg_eqv c1 c1'.
Proof.
intros c tr c1 H. induction H as [c | c evs c2 tr c3 Hst Hstar IH]; intros c' Heqv.
- exists c'. split; [apply star_cfg_refl| exact Heqv].
- destruct (sstep_cfg_eqv c c' evs (SNext c2) Heqv Hst) as (X' & Hst' & HX).
destruct X' as [c2'|]; simpl in HX; [|contradiction].
destruct (IH c2' HX) as (c3' & Hstar' & H3).
exists c3'. split; [eapply star_cfg_step; eassumption| exact H3].
Qed.

Definition canonR (R : bvmap 5 word) : bvmap 5 word :=
mkR (reg_get R (Z_to_bv 5 1)) (reg_get R (Z_to_bv 5 2)) (reg_get R (Z_to_bv 5 3)) (reg_get R (Z_to_bv 5 4))
(reg_get R (Z_to_bv 5 5)) (reg_get R (Z_to_bv 5 6)) (reg_get R (Z_to_bv 5 7)) (reg_get R (Z_to_bv 5 8))
(reg_get R (Z_to_bv 5 9)) (reg_get R (Z_to_bv 5 10)) (reg_get R (Z_to_bv 5 11)) (reg_get R (Z_to_bv 5 12))
(reg_get R (Z_to_bv 5 13)) (reg_get R (Z_to_bv 5 14)) (reg_get R (Z_to_bv 5 15)) (reg_get R (Z_to_bv 5 16))
(reg_get R (Z_to_bv 5 17)) (reg_get R (Z_to_bv 5 18)) (reg_get R (Z_to_bv 5 19)) (reg_get R (Z_to_bv 5 20))
(reg_get R (Z_to_bv 5 21)) (reg_get R (Z_to_bv 5 22)) (reg_get R (Z_to_bv 5 23)) (reg_get R (Z_to_bv 5 24))
(reg_get R (Z_to_bv 5 25)) (reg_get R (Z_to_bv 5 26)) (reg_get R (Z_to_bv 5 27)) (reg_get R (Z_to_bv 5 28))
(reg_get R (Z_to_bv 5 29)) (reg_get R (Z_to_bv 5 30)) (reg_get R (Z_to_bv 5 31)).

#[using="Type"] Lemma reg_of_nat' : forall r : reg, exists n, r = Z_to_bv 5 (Z.of_nat n) /\ (n < 32)%nat.
Proof.
intros r. exists (Z.to_nat (bv_unsigned r)). pose proof (bv_unsigned_in_range 5 r) as Hr.
unfold bv_modulus in Hr. simpl in Hr. split; [|lia].
rewrite Z2Nat.id by lia. apply bv_eq. rewrite Z_to_bv_unsigned. symmetry.
apply bv_wrap_small. unfold bv_modulus. simpl. lia.
Qed.
#[using="Type"] Lemma canonR_eqv : forall R, iregs_eqv R (canonR R).
Proof.
intros R r. destruct (reg_of_nat' r) as (n & -> & Hn).
do 32 (destruct n as [|n]; [reflexivity|]). lia.
Qed.
#[using="Type"] Lemma ms_eqv_canon : forall R F pc fc rv m ro,
ms_eqv (MS R F pc fc rv m ro) (MS (canonR R) F pc fc rv m ro).
Proof. intros. split; [apply canonR_eqv|]. repeat split; try apply regs_eqv_refl. Qed.
End WithSegs.
