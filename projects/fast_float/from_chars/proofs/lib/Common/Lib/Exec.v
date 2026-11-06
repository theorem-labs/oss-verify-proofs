(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import LiaTuning MState Mem.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Open Scope bv_scope.

Section WithSegs.
Variable segs : list Segment.

Definition mstep (ms ms' : machine_state) : Prop :=
  ms_svc_pending ms = None /\ RiscvSemantics.step segs ms = MachineOk ms'.

Inductive msteps : machine_state -> machine_state -> Prop :=
| msteps_refl : forall ms, msteps ms ms
| msteps_cons : forall ms ms1 ms2, mstep ms ms1 -> msteps ms1 ms2 -> msteps ms ms2.

#[using="Type"] Lemma msteps_one : forall ms ms', mstep ms ms' -> msteps ms ms'.
Proof. LiaFast.lf_pins LiaFast.u0. intros. eapply msteps_cons; [eassumption|apply msteps_refl]. Qed.

#[using="Type"] Lemma msteps_trans : forall a b c, msteps a b -> msteps b c -> msteps a c.
Proof. LiaFast.lf_pins LiaFast.u0. intros a b c H; induction H; intros; [assumption|]. eapply msteps_cons; eauto. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma mstep_det : forall ms a b, mstep ms a -> mstep ms b -> a = b.
Proof. LiaFast.lf_pins LiaFast.u0. intros ms a b [_ Ha] [_ Hb]. congruence. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma mstep_not_svc : forall ms ms', mstep ms ms' -> ms_svc_pending ms = None.
Proof. LiaFast.lf_pins LiaFast.u0. intros ms ms' [H _]; exact H. Qed.

(* [comment removed for export] *)

End WithSegs.

Arguments mstep segs ms ms' /.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition regs_eqv (R R' : bvmap 5 word) : Prop := forall r, getr R r = getr R' r.
Definition fregs_eqv (R R' : bvmap 5 word) : Prop := forall r, reg_get R r = reg_get R' r.

Lemma regs_eqv_refl : forall R, regs_eqv R R.
Proof. intros R r. reflexivity. Qed.
Lemma regs_eqv_sym : forall R R', regs_eqv R R' -> regs_eqv R' R.
Proof. intros R R' H r. symmetry. apply H. Qed.
Lemma regs_eqv_trans : forall R1 R2 R3, regs_eqv R1 R2 -> regs_eqv R2 R3 -> regs_eqv R1 R3.
Proof. intros R1 R2 R3 H1 H2 r. etransitivity; [apply H1|apply H2]. Qed.
Lemma fregs_eqv_refl : forall R, fregs_eqv R R.
Proof. intros R r. reflexivity. Qed.
Lemma fregs_eqv_sym : forall R R', fregs_eqv R R' -> fregs_eqv R' R.
Proof. intros R R' H r. symmetry. apply H. Qed.
Lemma fregs_eqv_trans : forall R1 R2 R3, fregs_eqv R1 R2 -> fregs_eqv R2 R3 -> fregs_eqv R1 R3.
Proof. intros R1 R2 R3 H1 H2 r. etransitivity; [apply H1|apply H2]. Qed.

(* [comment removed for export] *)
Lemma reg_get_set : forall (R : bvmap 5 word) (k r : reg) v,
  reg_get (bvmap_set k v R) r = if bv_eqb k r then v else reg_get R r.
Proof.
  intros R k r v. destruct (bv_eqb k r) eqn:E.
  - apply bv_eqb_eq in E. subst. apply reg_get_set_same.
  - apply reg_get_set_other. intros ->. rewrite bv_eqb_refl in E. discriminate.
Qed.

Lemma getr_set : forall (R : bvmap 5 word) (k r : reg) v,
  getr (bvmap_set k v R) r = if bv_eqb r 0 then Z_to_bv 64 0 else if bv_eqb k r then v else reg_get R r.
Proof. intros R k r v. unfold getr. rewrite reg_get_set. reflexivity. Qed.

Lemma regs_eqv_set : forall R R' (k : reg) v,
  regs_eqv R R' -> regs_eqv (bvmap_set k v R) (bvmap_set k v R').
Proof.
  intros R R' k v H r. rewrite !getr_set. specialize (H r). unfold getr in H.
  destruct (bv_eqb r 0); [reflexivity|]. destruct (bv_eqb k r); [reflexivity|exact H].
Qed.

Lemma fregs_eqv_set : forall R R' (k : reg) v,
  fregs_eqv R R' -> fregs_eqv (bvmap_set k v R) (bvmap_set k v R').
Proof. intros R R' k v H r. rewrite !reg_get_set. destruct (bv_eqb k r); [reflexivity|apply H]. Qed.

(* [comment removed for export] *)
Lemma rget_getr : forall R F pc fc rv r, rget (Core R F pc fc rv) r = getr R r.
Proof. intros. unfold rget, getr. rewrite bv_eqb0_is_x0. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition core_eqv (c c' : core) : Prop :=
  regs_eqv (c_regs c) (c_regs c') /\ fregs_eqv (c_fregs c) (c_fregs c') /\
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
  cbv beta iota zeta delta [exec fget fread c_regs c_fregs c_pc c_fcsr c_resv
                            with_pc load_val store_val exec_csr resolve_rm frm_of];
  rewrite ?rget_getr.

(* [comment removed for export] *)
Lemma exec_eqv_core : forall R R' F F' pc fc rv sz i,
  regs_eqv R R' -> fregs_eqv F F' ->
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
  regs_eqv (ms_regs ms) (ms_regs ms') /\ fregs_eqv (ms_fregs ms) (ms_fregs ms') /\
  ms_pc_val ms = ms_pc_val ms' /\ ms_svc_pending ms = ms_svc_pending ms' /\
  ms_resv ms = ms_resv ms' /\ ms_fcsr ms = ms_fcsr ms' /\
  ms_mem ms = ms_mem ms' /\ ms_rom ms = ms_rom ms'.

Lemma ms_eqv_refl : forall ms, ms_eqv ms ms.
Proof. intros ms. repeat split; first [apply regs_eqv_refl | apply fregs_eqv_refl]. Qed.
Lemma ms_eqv_sym : forall ms ms', ms_eqv ms ms' -> ms_eqv ms' ms.
Proof.
  intros ms ms' (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8).
  repeat split; auto using regs_eqv_sym, fregs_eqv_sym; congruence.
Qed.
Lemma ms_eqv_trans : forall a b c, ms_eqv a b -> ms_eqv b c -> ms_eqv a c.
Proof.
  intros a b c (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8) (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8).
  repeat split; eauto using regs_eqv_trans, fregs_eqv_trans; congruence.
Qed.

Definition res_eqv (r r' : machine_result machine_state) : Prop :=
  match r, r' with
  | MachineOk a, MachineOk b => ms_eqv a b
  | MachineFault, MachineFault => True
  | MachineUnmodeled, MachineUnmodeled => True
  | _, _ => False
  end.

Section WithSegs2.
Variable segs : list Segment.

#[using="Type"] Lemma interp_eff_eqv : forall t t', eff_eqv t t' -> forall m,
  match interp_eff segs t m, interp_eff segs t' m with
  | MachineOk (c, m1), MachineOk (c', m1') => core_eqv c c' /\ m1 = m1'
  | MachineFault, MachineFault => True
  | MachineUnmodeled, MachineUnmodeled => True
  | _, _ => False
  end.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros t t' H m. rewrite !interp_eff_ieff. revert m. induction H; intros m; cbn [ieff]; auto.
  - destruct (ov_read_bytes segs m a (width_bytes n)) as [bs|]; [apply H0| exact I].
  - destruct (store_ok segs m a (width_bytes n)); [apply IHeff_eqv| exact I].
Qed.

#[using="Type"] Lemma ms_reg_eqv : forall ms ms' r, bv_eqb r 0 = false -> ms_eqv ms ms' -> ms_reg ms r = ms_reg ms' r.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros ms ms' r Hr (HR & _). specialize (HR r). unfold getr in HR. rewrite Hr in HR.
  unfold ms_reg. rewrite Hr. exact HR.
Qed.

#[using="Type"] Lemma decode_exec_eqv : forall ms ms' w, ms_eqv ms ms' ->
  res_eqv (decode_exec segs ms w) (decode_exec segs ms' w).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros ms ms' w Heqv. pose proof (ms_reg_eqv ms ms' 17 eq_refl Heqv) as H17.
  destruct ms as [R F pc svc rv fc m ro], ms' as [R' F' pc' svc' rv' fc' m' ro'].
  destruct Heqv as (HR & HF & Hpc & Hsvc & Hrv & Hfc & Hm & Hro); simpl in *; subst.
  rewrite !decode_exec_old. destruct (is_ecall w).
  - simpl. rewrite H17. repeat split; assumption.
  - destruct (decode_any w) as [[i isz]|]; [| destruct (is_defined_illegal w); exact I]. simpl.
    pose proof (interp_eff_eqv _ _ (exec_eqv_core R R' F F' pc' fc' rv' (Z_to_bv 64 isz) i HR HF) m') as K.
    destruct (interp_eff segs (exec _ i (Core R F pc' fc' rv')) m') as [[c m1]| |];
    destruct (interp_eff segs (exec _ i (Core R' F' pc' fc' rv')) m') as [[c' m1']| |];
    simpl; try exact K; try contradiction.
    destruct K as [(H1 & H2 & H3 & H4 & H5) ->]. repeat split; simpl; auto.
Qed.

#[using="Type"] Lemma step_eqv : forall ms ms', ms_eqv ms ms' ->
  res_eqv (RiscvSemantics.step segs ms) (RiscvSemantics.step segs ms').
Proof. LiaFast.lf_pins LiaFast.u0.
  intros ms ms' Heqv. pose proof Heqv as (_ & _ & Hpc & _ & _ & _ & Hm & _).
  rewrite !step_old. unfold ms_pc. rewrite <- Hpc, <- Hm.
  destruct (fetch_word segs (ms_pc_val ms)); [apply decode_exec_eqv; exact Heqv|].
  destruct (fetch_word_ov segs (ms_mem ms) (ms_pc_val ms)); [apply decode_exec_eqv; exact Heqv|].
  destruct (fetch_tail_any segs (ms_mem ms) (ms_pc_val ms)); [apply decode_exec_eqv; exact Heqv|].
  unfold fetch_failure. destruct (negb _); [exact I|]. destruct (_ || _)%bool; exact I.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma mstep_eqv : forall ms ms1 ms', mstep segs ms ms1 -> ms_eqv ms ms' ->
  exists ms1', mstep segs ms' ms1' /\ ms_eqv ms1 ms1'.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros ms ms1 ms' [Hsvc Hst] Heqv.
  pose proof (step_eqv ms ms' Heqv) as Hres. rewrite Hst in Hres.
  pose proof Heqv as (_ & _ & _ & Hsvc' & _).
  destruct (RiscvSemantics.step segs ms') as [ms1'| |] eqn:E; cbn in Hres; try contradiction.
  exists ms1'. split; [split; [congruence| exact E]| exact Hres].
Qed.

#[using="Type"] Lemma msteps_eqv : forall ms ms1, msteps segs ms ms1 ->
  forall ms', ms_eqv ms ms' -> exists ms1', msteps segs ms' ms1' /\ ms_eqv ms1 ms1'.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros ms ms1 H. induction H as [ms | ms ma mb Hst Hrest IH]; intros ms' Heqv.
  - exists ms'. split; [apply msteps_refl| exact Heqv].
  - destruct (mstep_eqv ms ma ms' Hst Heqv) as (ma' & Hst' & Ha).
    destruct (IH ma' Ha) as (mb' & Hrest' & Hb).
    exists mb'. split; [eapply msteps_cons; eassumption| exact Hb].
Qed.

(* [comment removed for export] *)

Definition evt (Q : machine_state -> Prop) (ms : machine_state) : Prop :=
  exists ms1 ms2, msteps segs ms ms1 /\ ms_eqv ms1 ms2 /\ Q ms2.

#[using="Type"] Lemma evt_done : forall (Q : machine_state -> Prop) ms, Q ms -> evt Q ms.
Proof. LiaFast.lf_pins LiaFast.u0. intros Q ms H. exists ms, ms. split; [apply msteps_refl|]. split; [apply ms_eqv_refl| exact H]. Qed.

#[using="Type"] Lemma evt_step : forall Q ms ms1, mstep segs ms ms1 -> evt Q ms1 -> evt Q ms.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros Q ms ms1 H (msa & msb & Hs & He & HQ). exists msa, msb.
  split; [eapply msteps_cons; eauto|]. split; assumption.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma evt_eqv_l : forall Q ms ms', ms_eqv ms ms' -> evt Q ms' -> evt Q ms.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros Q ms ms' Heqv (msa & msb & Hrun & He & HQ).
  destruct (msteps_eqv ms' msa Hrun ms (ms_eqv_sym _ _ Heqv)) as (msa' & Hrun' & Ha).
  exists msa', msb. split; [exact Hrun'|]. split; [| exact HQ].
  eapply ms_eqv_trans; [apply ms_eqv_sym; exact Ha | exact He].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma evt_msteps : forall Q ms ms1, msteps segs ms ms1 -> evt Q ms1 -> evt Q ms.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros Q ms ms1 Hrun (msa & msb & Hs & He & HQ). exists msa, msb.
  split; [eapply msteps_trans; eassumption|]. split; assumption.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma evt_cut : forall (P Q : machine_state -> Prop) ms,
  evt P ms -> (forall ms', P ms' -> evt Q ms') -> evt Q ms.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros P Q ms (ms1 & ms2 & H1 & He & HP) K.
  eapply evt_msteps; [exact H1|]. eapply evt_eqv_l; [exact He|]. apply K, HP.
Qed.

#[using="Type"] Lemma evt_mono : forall (P Q : machine_state -> Prop) ms,
  evt P ms -> (forall ms', P ms' -> Q ms') -> evt Q ms.
Proof. LiaFast.lf_pins LiaFast.u0. intros P Q ms H K. eapply evt_cut; [exact H|]. intros ms' HP. apply evt_done, K, HP. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma evt_eq : forall Q ms ms', ms = ms' -> evt Q ms' -> evt Q ms.
Proof. LiaFast.lf_pins LiaFast.u0. intros; subst; assumption. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma evt_elim : forall Q ms, evt Q ms -> exists ms1, msteps segs ms ms1 /\ exists ms2, Q ms2 /\ ms_eqv ms2 ms1.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros Q ms (ms1 & ms2 & H & He & HQ). exists ms1. split; [exact H|]. exists ms2. split; [exact HQ|].
  apply ms_eqv_sym. exact He.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma evt_eqv : forall Q ms ms', evt Q ms -> ms_eqv ms ms' -> evt Q ms'.
Proof. LiaFast.lf_pins LiaFast.u0. intros Q ms ms' H He. eapply evt_eqv_l; [apply ms_eqv_sym; exact He | exact H]. Qed.

End WithSegs2.

