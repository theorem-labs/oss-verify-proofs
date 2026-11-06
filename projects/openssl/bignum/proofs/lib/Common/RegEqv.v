(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Definition regs_eqv (R1 R2 : bvmap 5 word) : Prop := forall r : reg, r <> 0%bv -> reg_get R1 r = reg_get R2 r.

Lemma regs_eqv_refl : forall R, regs_eqv R R. Proof. intros R r _; reflexivity. Qed.

Lemma regs_eqv_set : forall R1 R2 (k : reg) v, regs_eqv R1 R2 -> regs_eqv (bvmap_set k v R1) (bvmap_set k v R2).
Proof.
  intros R1 R2 k v H r Hr. unfold reg_get.
  destruct (decide (k = r)) as [->|Hne].
  - rewrite !bvmap_get_set_same. reflexivity.
  - rewrite !(bvmap_get_set_other _ _ _ _ Hne). apply H, Hr.
Qed.

Lemma is_x0_false_neq : forall r : reg, is_x0 r = false -> r <> 0%bv.
Proof. intros r H Hr. subst r. discriminate H. Qed.

Definition core_eqv (c1 c2 : core) : Prop :=
  regs_eqv (c_regs c1) (c_regs c2) /\ c_fregs c1 = c_fregs c2 /\ c_pc c1 = c_pc c2
  /\ c_fcsr c1 = c_fcsr c2 /\ c_resv c1 = c_resv c2.

Inductive eff_eqv : eff -> eff -> Prop :=
| EQ_done : forall c1 c2, core_eqv c1 c2 -> eff_eqv (EDone c1) (EDone c2)
| EQ_ill : forall c1 c2, core_eqv c1 c2 -> eff_eqv (EIllegal c1) (EIllegal c2)
| EQ_dill : forall c1 c2, core_eqv c1 c2 -> eff_eqv (EDefinedIllegal c1) (EDefinedIllegal c2)
| EQ_ecall : forall c1 c2, core_eqv c1 c2 -> eff_eqv (EEcall c1) (EEcall c2)
| EQ_ebreak : forall c1 c2, core_eqv c1 c2 -> eff_eqv (EEbreak c1) (EEbreak c2)
| EQ_fault : forall c1 c2, core_eqv c1 c2 -> eff_eqv (EFault c1) (EFault c2)
| EQ_load : forall n a k1 k2, (forall v, eff_eqv (k1 v) (k2 v)) -> eff_eqv (ELoad n a k1) (ELoad n a k2)
| EQ_store : forall n a v k1 k2, eff_eqv k1 k2 -> eff_eqv (EStore n a v k1) (EStore n a v k2).

Section CoreLemmas.
  Variables c1 c2 : core.
  Hypothesis H : core_eqv c1 c2.
  Lemma ce_rget : forall r, rget c1 r = rget c2 r.
  Proof. intros r. unfold rget. destruct (is_x0 r) eqn:E; [reflexivity|]. apply (proj1 H), is_x0_false_neq, E. Qed.
  Lemma ce_fget : forall r, fget c1 r = fget c2 r.
  Proof. intros r. unfold fget. rewrite (proj1 (proj2 H)). reflexivity. Qed.
  Lemma ce_fread : forall fmt r, fread c1 fmt r = fread c2 fmt r.
  Proof. intros fmt r. unfold fread. rewrite !ce_fget. reflexivity. Qed.
  Lemma ce_pc : c_pc c1 = c_pc c2. Proof. apply H. Qed.
  Lemma ce_fcsr : c_fcsr c1 = c_fcsr c2. Proof. apply H. Qed.
  Lemma ce_resv : c_resv c1 = c_resv c2. Proof. apply H. Qed.
  Lemma ce_rm : forall rm, resolve_rm rm c1 = resolve_rm rm c2.
  Proof. intros rm. unfold resolve_rm, frm_of. rewrite ce_fcsr. reflexivity. Qed.
End CoreLemmas.

Lemma ce_refl_other : forall R1 R2 f p fc rv, regs_eqv R1 R2 -> core_eqv (Core R1 f p fc rv) (Core R2 f p fc rv).
Proof. intros. repeat split; auto. Qed.

Lemma ce_rset : forall c1 c2 r v, core_eqv c1 c2 -> core_eqv (rset r v c1) (rset r v c2).
Proof.
  intros c1 c2 r v H. unfold rset. destruct (is_x0 r); [exact H|].
  destruct H as (Hr & Hf & Hp & Hc & Hv). unfold with_regs; cbn. repeat split; auto. apply regs_eqv_set, Hr.
Qed.
Lemma ce_fset : forall c1 c2 r v, core_eqv c1 c2 -> core_eqv (fset r v c1) (fset r v c2).
Proof. intros c1 c2 r v (Hr & Hf & Hp & Hc & Hv). unfold fset, with_fregs; cbn. rewrite Hf. repeat split; auto. Qed.
Lemma ce_with_pc : forall c1 c2 p, core_eqv c1 c2 -> core_eqv (with_pc p c1) (with_pc p c2).
Proof. intros c1 c2 p (Hr & Hf & Hp & Hc & Hv). unfold with_pc; cbn. repeat split; auto. Qed.
Lemma ce_with_fcsr : forall c1 c2 p, core_eqv c1 c2 -> core_eqv (with_fcsr p c1) (with_fcsr p c2).
Proof. intros c1 c2 p (Hr & Hf & Hp & Hc & Hv). unfold with_fcsr; cbn. repeat split; auto. Qed.
Lemma ce_with_resv : forall c1 c2 p, core_eqv c1 c2 -> core_eqv (with_resv p c1) (with_resv p c2).
Proof. intros c1 c2 p (Hr & Hf & Hp & Hc & Hv). unfold with_resv; cbn. repeat split; auto. Qed.
Lemma ce_inval_resv : forall c1 c2 a, core_eqv c1 c2 -> core_eqv (inval_resv a c1) (inval_resv a c2).
Proof.
  intros c1 c2 a H. unfold inval_resv. rewrite (ce_resv _ _ H).
  destruct (c_resv c2); [destruct (Z.eqb _ _)|]; auto using ce_with_resv.
Qed.
Lemma ce_accrue : forall c1 c2 fl, core_eqv c1 c2 -> core_eqv (accrue fl c1) (accrue fl c2).
Proof. intros c1 c2 fl H. unfold accrue. rewrite (ce_fcsr _ _ H). apply ce_with_fcsr, H. Qed.
Lemma ce_fwrite : forall c1 c2 fmt r v, core_eqv c1 c2 -> core_eqv (fwrite fmt r v c1) (fwrite fmt r v c2).
Proof. intros c1 c2 fmt r v H. unfold fwrite. destruct fmt; apply ce_fset, H. Qed.

Lemma ee_load_val : forall sz sgn a k1 k2, (forall v, eff_eqv (k1 v) (k2 v)) -> eff_eqv (load_val sz sgn a k1) (load_val sz sgn a k2).
Proof. intros sz sgn a k1 k2 Hk. destruct sz; cbn; constructor; intros v; apply Hk. Qed.
Lemma ee_store_val : forall sz a v k1 k2, eff_eqv k1 k2 -> eff_eqv (store_val sz a v k1) (store_val sz a v k2).
Proof. intros sz a v k1 k2 Hk. destruct sz; cbn; constructor; exact Hk. Qed.
Lemma ee_exec_csr : forall op rd v w csr c1 c2, core_eqv c1 c2 -> eff_eqv (exec_csr op rd v w csr c1) (exec_csr op rd v w csr c2).
Proof.
  intros op rd v w csr c1 c2 H. unfold exec_csr. destruct (csr_slice csr) as [[lo len]|]; [|constructor; exact H].
  rewrite (ce_fcsr _ _ H). constructor. apply ce_rset. destruct w; [apply ce_with_fcsr|]; exact H.
Qed.

Ltac ce_close H HR :=
  repeat first
    [ progress (rewrite ?(ce_rget _ _ H), ?(ce_fget _ _ H), ?(ce_fread _ _ H), ?(ce_pc _ _ H), ?(ce_rm _ _ H), ?(ce_resv _ _ H))
    | apply EQ_done | apply EQ_ill | apply EQ_dill | apply EQ_ecall | apply EQ_ebreak | apply EQ_fault
    | apply EQ_load; intro | apply EQ_store
    | apply ee_load_val; intro | apply ee_store_val | apply ee_exec_csr
    | apply ce_rset | apply ce_fset | apply ce_with_pc | apply ce_with_fcsr | apply ce_with_resv | apply ce_inval_resv
    | apply ce_accrue | apply ce_fwrite | exact H | (apply ce_refl_other; exact HR) ].

Lemma exec_eqv : forall sz i c1 c2, core_eqv c1 c2 -> eff_eqv (exec sz i c1) (exec sz i c2).
Proof.
  intros sz i [R1 f1 p1 fc1 rv1] [R2 f2 p2 fc2 rv2] H.
  pose proof H as H0.
  destruct H as (HR & Hf & Hp & Hfc & Hrv); cbn [c_regs c_fregs c_pc c_fcsr c_resv] in *; subst f2 p2 fc2 rv2.
  assert (Hg : forall f p fc rv r, rget (Core R1 f p fc rv) r = rget (Core R2 f p fc rv) r).
  { intros f p fc rv r. unfold rget; cbn [c_regs]. destruct (is_x0 r) eqn:E; [reflexivity|]. apply HR, is_x0_false_neq, E. }
  destruct i; cbn [exec];
    unfold resolve_rm, frm_of, fread, fget, accrue, inval_resv, with_pc, with_resv, with_fcsr, with_fregs, fwrite, fset;
    cbn [c_pc c_fcsr c_resv c_fregs c_regs]; rewrite ?Hg; ce_close H0 HR;
  repeat (match goal with |- context [match ?x with _ => _ end] => destruct x end; ce_close H0 HR).
Qed.

#[local] Arguments access_value {A} _.
#[local] Arguments accessed_ranges {A} _.

Section Lift.
Variable segs : list Segment.

Definition res_eqv (r1 r2 : machine_result (access_report (core * (word -> option byte)))) : Prop :=
  match r1, r2 with
  | MachineOk a, MachineOk b => accessed_ranges a = accessed_ranges b /\ snd (access_value a) = snd (access_value b)
                                /\ core_eqv (fst (access_value a)) (fst (access_value b))
  | MachineFault, MachineFault => True
  | MachineUnmodeled, MachineUnmodeled => True
  | _, _ => False
  end.

Lemma interp_eqv : forall t1 t2, eff_eqv t1 t2 -> forall m, res_eqv (interp_eff_accesses segs t1 m) (interp_eff_accesses segs t2 m).
Proof.
  induction 1 as [c1 c2 H|c1 c2 H|c1 c2 H|c1 c2 H|c1 c2 H|c1 c2 H|n a k1 k2 Hk IH|n a v k1 k2 Hk IH]; intros m; cbn [interp_eff_accesses res_eqv];
    try exact I.
  - cbn [res_eqv accessed_ranges access_value fst snd]. split; [reflexivity|]. split; [reflexivity|exact H].
  - destruct (ov_read_bytes segs m a (width_bytes n)) as [bs|]; [|exact I].
    specialize (IH (bv_extract 0 n (le_bytes_to_word bs)) m).
    destruct (interp_eff_accesses segs (k1 _) m) as [r1| |], (interp_eff_accesses segs (k2 _) m) as [r2| |];
      cbn in IH |- *; try contradiction; try exact I.
    destruct IH as (E1 & E2 & E3). cbn [accessed_ranges access_value]. rewrite E1. split; [reflexivity|]. split; assumption.
  - destruct (store_ok segs m a (width_bytes n)); [|exact I].
    specialize (IH (write_to_mem m a (Z_to_le_bytes (width_bytes n) (bv_unsigned v)))).
    destruct (interp_eff_accesses segs k1 _) as [r1| |], (interp_eff_accesses segs k2 _) as [r2| |];
      cbn in IH |- *; try contradiction; try exact I.
    destruct IH as (E1 & E2 & E3). cbn [accessed_ranges access_value]. rewrite E1. split; [reflexivity|]. split; assumption.
Qed.

Definition ms_eqv (ms1 ms2 : machine_state) : Prop :=
  regs_eqv (ms_regs ms1) (ms_regs ms2) /\ ms_fregs ms1 = ms_fregs ms2 /\ ms_pc_val ms1 = ms_pc_val ms2
  /\ ms_svc_pending ms1 = ms_svc_pending ms2 /\ ms_resv ms1 = ms_resv ms2 /\ ms_fcsr ms1 = ms_fcsr ms2
  /\ ms_mem ms1 = ms_mem ms2 /\ ms_rom ms1 = ms_rom ms2.

Definition mres_eqv (r1 r2 : machine_result (access_report machine_state)) : Prop :=
  match r1, r2 with
  | MachineOk a, MachineOk b => accessed_ranges a = accessed_ranges b /\ ms_eqv (access_value a) (access_value b)
  | MachineFault, MachineFault => True
  | MachineUnmodeled, MachineUnmodeled => True
  | _, _ => False
  end.

Lemma ms_reg_eqv : forall ms1 ms2 r, ms_eqv ms1 ms2 -> ms_reg ms1 r = ms_reg ms2 r.
Proof.
  intros ms1 ms2 r H. unfold ms_reg. destruct (bv_eqb r 0) eqn:E; [reflexivity|].
  apply (proj1 H). intros ->. discriminate E.
Qed.

Lemma dea_eqv : forall ms1 ms2 w, ms_eqv ms1 ms2 -> mres_eqv (decode_exec_accesses segs ms1 w) (decode_exec_accesses segs ms2 w).
Proof.
  intros ms1 ms2 w H. pose proof H as H0. destruct H as (HR & Hf & Hp & Hs & Hrv & Hfc & Hm & Hrom).
  unfold decode_exec_accesses. destruct (is_ecall w).
  - cbn. split; [reflexivity|]. rewrite (ms_reg_eqv _ _ 17 H0). repeat split; auto.
  - destruct (decode_any w) as [[i isz]|]; [|destruct (is_defined_illegal w); exact I].
    assert (Hc : core_eqv {| c_regs := ms_regs ms1; c_fregs := ms_fregs ms1; c_pc := ms_pc_val ms1; c_fcsr := ms_fcsr ms1; c_resv := ms_resv ms1 |}
                          {| c_regs := ms_regs ms2; c_fregs := ms_fregs ms2; c_pc := ms_pc_val ms2; c_fcsr := ms_fcsr ms2; c_resv := ms_resv ms2 |}).
    { repeat split; cbn; auto. }
    pose proof (interp_eqv _ _ (exec_eqv (Z_to_bv 64 isz) i _ _ Hc) (ms_mem ms1)) as HI.
    rewrite Hm in HI |- *.
    destruct (interp_eff_accesses segs (exec _ i _) (ms_mem ms2)) as [r1| |] eqn:E1;
    destruct (interp_eff_accesses segs (exec _ i {| c_regs := ms_regs ms2; c_fregs := _; c_pc := _; c_fcsr := _; c_resv := _ |}) (ms_mem ms2)) as [r2| |] eqn:E2;
      cbn in HI |- *; try contradiction; try exact I.
    destruct HI as (E3 & E4 & E5). destruct (access_value r1) as [c1 m1] eqn:V1, (access_value r2) as [c2 m2] eqn:V2.
    cbn in E4, E5 |- *. subst m2. split; [exact E3|].
    destruct E5 as (HR' & Hf' & Hp' & Hfc' & Hrv'). repeat split; auto.
Qed.

Lemma step_accesses_eqv : forall ms1 ms2, ms_eqv ms1 ms2 -> mres_eqv (step_accesses segs ms1) (step_accesses segs ms2).
Proof.
  intros ms1 ms2 H. pose proof H as H0. destruct H as (HR & Hf & Hp & Hs & Hrv & Hfc & Hm & Hrom).
  unfold step_accesses. unfold ms_pc. rewrite Hp, Hm.
  destruct (fetch_word segs (ms_pc_val ms2)) as [w|]; [apply dea_eqv, H0|].
  destruct (fetch_word_ov segs (ms_mem ms2) (ms_pc_val ms2)) as [w|]; [apply dea_eqv; exact H0|].
  destruct (fetch_tail_any segs (ms_mem ms2) (ms_pc_val ms2)) as [w|]; [apply dea_eqv; exact H0|].
  destruct (fetch_failure segs (ms_mem ms2) (ms_pc_val ms2)) as [st'| |]; cbn; try exact I.
  split; [reflexivity|]. repeat split; auto using regs_eqv_refl.
Qed.

Lemma mi_account_step_eqv : forall ms1 ms2 model, ms_eqv ms1 ms2 ->
  match mi_account_step segs ms1 model, mi_account_step segs ms2 model with
  | MachineOk (a1, m1), MachineOk (a2, m2) => ms_eqv a1 a2 /\ m1 = m2
  | MachineFault, MachineFault => True
  | MachineUnmodeled, MachineUnmodeled => True
  | _, _ => False
  end.
Proof.
  intros ms1 ms2 model H. unfold mi_account_step. pose proof (step_accesses_eqv ms1 ms2 H) as HS.
  destruct (step_accesses segs ms1) as [r1| |], (step_accesses segs ms2) as [r2| |]; cbn in HS; try contradiction; try exact I.
  destruct HS as [E1 E2]. rewrite E1.
  destruct (materialize_model_accesses model (accessed_ranges r2)); [|exact I]. split; [exact E2 | reflexivity].
Qed.

Lemma sys_input_eqv : forall ms1 ms2 x8, ms_eqv ms1 ms2 -> sys_input segs ms1 x8 = sys_input segs ms2 x8.
Proof.
  intros ms1 ms2 x8 H. pose proof H as H0. destruct H as (HR & Hf & Hp & Hs & Hrv & Hfc & Hm & Hrom).
  unfold sys_input, syscall_args, ms_gpr.
  assert (G : forall i, (i < 6)%nat -> reg_get (ms_regs ms1) (Z_to_bv 5 (10 + Z.of_nat i)) = reg_get (ms_regs ms2) (Z_to_bv 5 (10 + Z.of_nat i))).
  { intros i Hi. apply HR. intros Hc. apply (f_equal (@bv_unsigned 5)) in Hc.
    do 6 (destruct i as [|i]; [vm_compute in Hc; discriminate Hc|]). lia. }
  rewrite (G 0%nat), (G 1%nat), (G 2%nat), (G 3%nat), (G 4%nat), (G 5%nat) by lia.
  unfold ms_read_byte, ms_writable_byte. rewrite Hm, Hrom. reflexivity.
Qed.

Lemma apply_effect_eqv : forall ms1 ms2 eff, ms_eqv ms1 ms2 ->
  ms_eqv (advance_past_svc (apply_effect ms1 eff)) (advance_past_svc (apply_effect ms2 eff)).
Proof.
  intros ms1 ms2 eff H. destruct H as (HR & Hf & Hp & Hs & Hrv & Hfc & Hm & Hrom).
  unfold advance_past_svc, apply_effect, set_reg, ms_pc. cbn.
  destruct (bv_eqb 10 0); cbn; rewrite ?Hf, ?Hp, ?Hrv, ?Hfc, ?Hm, ?Hrom; repeat split; auto.
  apply regs_eqv_set, HR.
Qed.

Definition cfg_eqv (c1 c2 : config) : Prop := ms_eqv (cfg_ms c1) (cfg_ms c2) /\ cfg_model c1 = cfg_model c2.

Definition st_eqv (s1 s2 : step_to) : Prop :=
  match s1, s2 with
  | SNext c1, SNext c2 => cfg_eqv c1 c2
  | SError, SError => True
  | _, _ => False
  end.

End Lift.

