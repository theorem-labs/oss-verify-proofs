(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Kernel.Time Require Import PosixTimers.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import PropExec MState Mem Exec ITree Nodes.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import MmNodes.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import Scfg RelSpec SReach SReachTree.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Inductive cgnode : Type :=
| CGRealtime (tp : Z).        (* [comment removed for export] *)

Section AtNode.
Variable segs : list Segment.
Definition cg_at_node (n : cgnode) (ms : machine_state) : Prop :=
  match n with
  | CGRealtime tp =>
      ms_svc_pending ms = Some (Z_to_bv 64 113) /\
      areg ms 10 = Z_to_bv 64 0 /\ areg ms 11 = Z_to_bv 64 tp /\
      ms_rom ms = seg_rom segs /\ wr_at segs (ms_mem ms) tp 16
  end.
End AtNode.

Definition cg_nstep (n : cgnode) (mo : Model) (eff : resp) (mo' : Model) (evs : list event) : Prop :=
  match n with
  | CGRealtime tp =>
      evs = [] /\ mo' = mo /\
      exists bs, realtime_ok_b bs = true /\ eff = mkEffect (Z_to_bv 64 0) [(Z_to_bv 64 tp, bs)] []
  end.

Definition cg_nexit (n : cgnode) (mo : Model) (code : word) (mo' : Model) : Prop := False.
Definition cg_safe (n : cgnode) (mo : Model) : Prop := True.

(* [comment removed for export] *)
Lemma realtime_ok_zeros : realtime_ok_b (repeat (Z_to_bv 8 0) 16) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma realtime_ok_length : forall bs, realtime_ok_b bs = true -> length bs = 16%nat.
Proof.
  intros bs H. unfold realtime_ok_b in H. apply andb_prop in H as [H _]. apply andb_prop in H as [H _].
  apply PeanoNat.Nat.eqb_eq in H. exact H.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma syscall_spec_113 : forall i m o,
  bv_unsigned (in_sysno i) = 113 ->
  syscall_spec i m o <-> clock_gettime_spec (clockid32 (in_arg i 0)) (in_arg i 1) i m o.
Proof. intros i m o E; unfold syscall_spec, dispatch; rewrite E; reflexivity. Qed.

Lemma clockid32_realtime : clockid32 (Z_to_bv 64 0) = Z_to_bv 64 0.
Proof. vm_compute. reflexivity. Qed.
Lemma percall_realtime : clockid_percall_b (Z_to_bv 64 0) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma clock_realtime_outcome : forall tp i m o w,
  read_bytes_map (in_wmem i) tp (Z_to_bv 64 16) = Some w ->
  clock_gettime_spec (Z_to_bv 64 0) tp i m o <->
  exists bs, realtime_ok_b bs = true /\ o = Ok (mkEffect (Z_to_bv 64 0) [(tp, bs)] []) m [].
Proof.
  intros tp i m o w Hw. unfold clock_gettime_spec. rewrite percall_realtime. sys_unfold.
  split.
  - destruct o as [x m' evs|]; intros H; inv_sys; rewrite Hw in *; inv_sys.
    eexists. split; [eassumption| reflexivity].
  - intros (bs & Hbs & ->). eexists _, _, _, _. split; [reflexivity|]. rewrite Hw. split; [| reflexivity].
    eexists _, _, _, _. split; [exists bs; split; [exact Hbs| reflexivity]|]. split; reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Sound.
Context {SC : StepCfg} {AF : AllocForced SC}.
Variable segs : list Segment.

#[local] Notation SSTEP := (sstep_cfg segs the_scfg).

Lemma cg_at_node_pending : forall n ms, cg_at_node segs n ms -> ms_svc_pending ms <> None.
Proof. intros [tp] ms (H & _). congruence. Qed.

(* [comment removed for export] *)
Lemma cg_input : forall tp ms x8 mo,
  cg_at_node segs (CGRealtime tp) ms -> ms_svc_pending ms = Some x8 ->
  bv_unsigned (in_sysno (sys_input segs ms x8)) = 113
  /\ clockid32 (in_arg (sys_input segs ms x8) 0) = Z_to_bv 64 0
  /\ in_arg (sys_input segs ms x8) 1 = Z_to_bv 64 tp
  /\ (exists w, read_bytes_map (in_wmem (sys_input segs ms x8)) (Z_to_bv 64 tp) (Z_to_bv 64 16) = Some w)
  /\ (forall o, syscall_spec (sys_input segs ms x8) mo o <->
        exists bs, realtime_ok_b bs = true /\ o = Ok (mkEffect (Z_to_bv 64 0) [(Z_to_bv 64 tp, bs)] []) mo []).
Proof.
  intros tp ms x8 mo (SV & A0 & A1 & ROM & WR) SV'. rewrite SV in SV'. injection SV' as <-.
  assert (NO : bv_unsigned (in_sysno (sys_input segs ms (Z_to_bv 64 113))) = 113) by (rewrite in_sysno_si; reflexivity).
  assert (C0 : clockid32 (in_arg (sys_input segs ms (Z_to_bv 64 113)) 0) = Z_to_bv 64 0) by (rewrite in_a0_si, A0; apply clockid32_realtime).
  assert (C1 : in_arg (sys_input segs ms (Z_to_bv 64 113)) 1 = Z_to_bv 64 tp) by (rewrite in_a1_si, A1; reflexivity).
  assert (W : exists w, read_bytes_map (in_wmem (sys_input segs ms (Z_to_bv 64 113))) (Z_to_bv 64 tp) (Z_to_bv 64 16) = Some w).
  { rewrite in_wmem_si. unfold ms_writable_byte. rewrite read_bytes_map_eq.
    pose proof (read_bytes_aux_wr_at segs (ms_mem ms) tp 16 16 WR ltac:(cbn; lia)) as X.
    change (wa tp) with (Z_to_bv 64 tp) in X. replace (word_to_nat (Z_to_bv 64 16)) with 16%nat by reflexivity.
    destruct (read_bytes_aux (wview segs (ms_mem ms)) (Z_to_bv 64 tp) 16) as [w|]; [exists w; reflexivity| exfalso; apply X; reflexivity]. }
  split; [exact NO|]. split; [exact C0|]. split; [exact C1|]. split; [exact W|].
  intros o. rewrite (syscall_spec_113 _ mo o NO), C0, C1. destruct W as [w Hw]. apply (clock_realtime_outcome _ _ mo o w Hw).
Qed.

(* [comment removed for export] *)
Lemma cg_not_spurious : forall i mo eff, bv_unsigned (in_sysno i) = 113 -> ~ Run.spurious_refusal_cfg the_scfg i mo eff.
Proof.
  intros i mo eff NO (_ & R & _). unfold Run.refusal_b in R. rewrite NO in R. cbn in R. discriminate R.
Qed.

Theorem cg_node_sound : node_sound cgnode segs (cg_at_node segs) cg_nstep cg_nexit mminv cg_safe.
Proof.
  split.
  - apply cg_at_node_pending.
  - (* [comment removed for export] *)
    intros [tp] ms mo evs X AT HH MI _ ST.
    destruct (ms_svc_pending ms) as [x8|] eqn:SV; [| exfalso; exact (cg_at_node_pending _ ms AT SV)].
    destruct (cg_input tp ms x8 mo AT SV) as (NO & _ & _ & _ & SP).
    left. destruct (sstep_svc_inv segs ms mo x8 evs X SV ST)
      as [(eff & mo' & mo'' & S & NS & Hh & MAT & ->)
         |[(eff & mo' & evs0 & S & NS & Hh & MAT & -> & ->)
         |[(eff & mo' & evs0 & code & S & Hh & -> & ->)
         |[(eff & mo' & evs0 & sig & S & Hk & -> & ->)
         |(S & -> & ->)]]]].
    + apply SP in S as (bs & Hbs & E). apply Ok_inj in E as (-> & -> & ->).
      rewrite (materialize_model_accesses_no_lazy _ _ (mminv_lazy _ MI)) in MAT. injection MAT as <-.
      exists (mkEffect (Z_to_bv 64 0) [(Z_to_bv 64 tp, bs)] []), mo. split; [reflexivity|]. cbn. split; [reflexivity|]. split; [reflexivity|]. exists bs. auto.
    + exfalso. apply SP in S as (bs & Hbs & E). apply Ok_inj in E as (-> & -> & ->).
      rewrite (materialize_model_accesses_no_lazy _ _ (mminv_lazy _ MI)) in MAT. discriminate.
    + exfalso. apply SP in S as (bs & Hbs & E). apply Ok_inj in E as (-> & -> & ->). congruence.
    + exfalso. apply SP in S as (bs & Hbs & E). apply Ok_inj in E as (-> & -> & ->).
      rewrite (m_killed_of_m_halted_none mo) in Hk by exact HH. discriminate.
    + exfalso. apply SP in S as (bs & Hbs & E). discriminate E.
  - (* [comment removed for export] *)
    intros [tp] ms mo rsp mo' evs AT HH MI _ NS.
    destruct NS as (-> & -> & bs & Hbs & ->).
    split; [exact HH|]. split; [exact MI|].
    destruct (ms_svc_pending ms) as [x8|] eqn:SV; [| exfalso; exact (cg_at_node_pending _ ms AT SV)].
    destruct (cg_input tp ms x8 mo AT SV) as (NO & _ & _ & _ & SP).
    unfold nret. eapply sstep_cfg_syscall; [exact HH| exact SV| apply SP; exists bs; split; [exact Hbs| reflexivity]| apply cg_not_spurious; exact NO| exact HH|].
    apply materialize_model_accesses_no_lazy. exact (mminv_lazy _ MI).
  - (* [comment removed for export] *)
    intros [tp] ms mo code mo' AT HH MI _ NX. exfalso. exact NX.
  - (* [comment removed for export] *)
    intros [tp] ms mo AT HH MI _. left.
    exists (mkEffect (Z_to_bv 64 0) [(Z_to_bv 64 tp, repeat (Z_to_bv 8 0) 16)] []), mo, [].
    cbn. split; [reflexivity|]. split; [reflexivity|]. exists (repeat (Z_to_bv 8 0) 16). split; [exact realtime_ok_zeros| reflexivity].
Qed.

(* [comment removed for export] *)
Lemma cg_silent : forall n, SReachTree.silent_node cg_nstep cg_nexit n.
Proof. intros [tp]. split; [intros mo code mo' H; exact H| intros mo rsp mo' evs (H & _); exact H]. Qed.
End Sound.
