(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import Dispatch.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Common.BudgetBridge Require Import BBArmsBase BBArms1 BBArms2 BBArms3 BBArms4 BBArms5 BBArms6 BBArms7 BBArms8 BBFit BBMArm.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition arm_ok (c : CheckedArm) : Prop :=
  forall L i eff m, (vm_limit (m_vmmaps m) <= L)%Z -> alloc_budget_refused_b i m = false -> vm_fit (m_vmmaps m) ->
    bv_unsigned (in_sysno i) = ca_no c ->
    ca_check c i eff (relim L m) = map_cr (relim L) (ca_check c i eff m).

Lemma arms_ok : Forall arm_ok checked_table.
Proof.
  unfold checked_table.
  constructor; [ unfold arm_ok; intros L i eff m HL HB Hfit Hn; apply arm_getcwd_relim |].
  constructor; [ unfold arm_ok; intros L i eff m HL HB Hfit Hn; apply arm_eventfd2_relim |].
  constructor; [ unfold arm_ok; intros L i eff m HL HB Hfit Hn; apply arm_epoll_create1_relim |].
  constructor; [ unfold arm_ok; intros L i eff m HL HB Hfit Hn; apply arm_epoll_ctl_relim |].
  constructor; [ unfold arm_ok; intros L i eff m HL HB Hfit Hn; apply arm_epoll_pwait_relim |].
  constructor; [ unfold arm_ok; intros L i eff m HL HB Hfit Hn; apply arm_dup_relim |].
  constructor; [ unfold arm_ok; intros L i eff m HL HB Hfit Hn; apply arm_dup3_relim |].
  constructor; [ unfold arm_ok; intros L i eff m HL HB Hfit Hn; apply arm_fcntl_relim |].
  constructor; [ unfold arm_ok; intros L i eff m HL HB Hfit Hn; apply arm_ioctl_relim |].
  constructor; [ unfold arm_ok; intros L i eff m HL HB Hfit Hn; apply arm_flock_relim |].
  constructor; [ unfold arm_ok; intros L i eff m HL HB Hfit Hn; apply arm_unlinkat_relim |].
  constructor; [ unfold arm_ok; intros L i eff m HL HB Hfit Hn; apply arm_ftruncate_relim |].
  constructor; [ unfold arm_ok; intros L i eff m HL HB Hfit Hn; apply arm_faccessat_relim |].
  constructor; [ unfold arm_ok; intros L i eff m HL HB Hfit Hn; apply arm_openat_relim |].
  constructor; [ unfold arm_ok; intros L i eff m HL HB Hfit Hn; apply arm_close_relim |].
  constructor; [ unfold arm_ok; intros L i eff m HL HB Hfit Hn; apply arm_pipe2_relim |].
  constructor; [ unfold arm_ok; intros L i eff m HL HB Hfit Hn; apply arm_getdents64_relim |].
  constructor; [ unfold arm_ok; intros L i eff m HL HB Hfit Hn; apply arm_lseek_relim |].
  constructor; [ unfold arm_ok; intros L i eff m HL HB Hfit Hn; apply arm_read_relim |].
  constructor; [ unfold arm_ok; intros L i eff m HL HB Hfit Hn; apply arm_write_relim |].
  constructor; [ unfold arm_ok; intros L i eff m HL HB Hfit Hn; apply arm_readv_relim |].
  constructor; [ unfold arm_ok; intros L i eff m HL HB Hfit Hn; apply arm_writev_relim |].
  constructor; [ unfold arm_ok; intros L i eff m HL HB Hfit Hn; apply arm_pread64_relim |].
  constructor; [ unfold arm_ok; intros L i eff m HL HB Hfit Hn; apply arm_pwrite64_relim |].
  constructor; [ unfold arm_ok; intros L i eff m HL HB Hfit Hn; apply arm_pselect6_relim |].
  constructor; [ unfold arm_ok; intros L i eff m HL HB Hfit Hn; apply arm_ppoll_relim |].
  constructor; [ unfold arm_ok; intros L i eff m HL HB Hfit Hn; apply arm_readlinkat_relim |].
  constructor; [ unfold arm_ok; intros L i eff m HL HB Hfit Hn; apply arm_newfstatat_relim |].
  constructor; [ unfold arm_ok; intros L i eff m HL HB Hfit Hn; apply arm_fstat_relim |].
  constructor; [ unfold arm_ok; intros L i eff m HL HB Hfit Hn; apply arm_fsync_relim |].
  constructor; [ unfold arm_ok; intros L i eff m HL HB Hfit Hn; apply arm_fdatasync_relim |].
  constructor; [ unfold arm_ok; intros L i eff m HL HB Hfit Hn; apply arm_timerfd_create_relim |].
  constructor; [ unfold arm_ok; intros L i eff m HL HB Hfit Hn; apply arm_exit_relim |].
  constructor; [ unfold arm_ok; intros L i eff m HL HB Hfit Hn; apply arm_exit_group_relim |].
  constructor; [ unfold arm_ok; intros L i eff m HL HB Hfit Hn; apply arm_set_tid_address_relim |].
  constructor; [ unfold arm_ok; intros L i eff m HL HB Hfit Hn; apply arm_futex_relim |].
  constructor; [ unfold arm_ok; intros L i eff m HL HB Hfit Hn; apply arm_nanosleep_relim |].
  constructor; [ unfold arm_ok; intros L i eff m HL HB Hfit Hn; apply arm_clock_gettime_relim |].
  constructor; [ unfold arm_ok; intros L i eff m HL HB Hfit Hn; apply arm_sched_setscheduler_relim |].
  constructor; [ unfold arm_ok; intros L i eff m HL HB Hfit Hn; apply arm_sched_getaffinity_relim |].
  constructor; [ unfold arm_ok; intros L i eff m HL HB Hfit Hn; apply arm_sched_yield_relim |].
  constructor; [ unfold arm_ok; intros L i eff m HL HB Hfit Hn; apply arm_tkill_relim |].
  constructor; [ unfold arm_ok; intros L i eff m HL HB Hfit Hn; apply arm_tgkill_relim |].
  constructor; [ unfold arm_ok; intros L i eff m HL HB Hfit Hn; apply arm_sigaltstack_relim |].
  constructor; [ unfold arm_ok; intros L i eff m HL HB Hfit Hn; apply arm_rt_sigaction_relim |].
  constructor; [ unfold arm_ok; intros L i eff m HL HB Hfit Hn; apply arm_rt_sigprocmask_relim |].
  constructor; [ unfold arm_ok; intros L i eff m HL HB Hfit Hn; apply arm_setgid_relim |].
  constructor; [ unfold arm_ok; intros L i eff m HL HB Hfit Hn; apply arm_setuid_relim |].
  constructor; [ unfold arm_ok; intros L i eff m HL HB Hfit Hn; apply arm_setresuid_relim |].
  constructor; [ unfold arm_ok; intros L i eff m HL HB Hfit Hn; apply arm_setresgid_relim |].
  constructor; [ unfold arm_ok; intros L i eff m HL HB Hfit Hn; apply arm_setsid_relim |].
  constructor; [ unfold arm_ok; intros L i eff m HL HB Hfit Hn; apply arm_getgroups_relim |].
  constructor; [ unfold arm_ok; intros L i eff m HL HB Hfit Hn; apply arm_setgroups_relim |].
  constructor; [ unfold arm_ok; intros L i eff m HL HB Hfit Hn; apply arm_uname_relim |].
  constructor; [ unfold arm_ok; intros L i eff m HL HB Hfit Hn; apply arm_prctl_relim |].
  constructor; [ unfold arm_ok; intros L i eff m HL HB Hfit Hn; apply arm_gettimeofday_relim |].
  constructor; [ unfold arm_ok; intros L i eff m HL HB Hfit Hn; apply arm_getpid_relim |].
  constructor; [ unfold arm_ok; intros L i eff m HL HB Hfit Hn; apply arm_getuid_relim |].
  constructor; [ unfold arm_ok; intros L i eff m HL HB Hfit Hn; apply arm_geteuid_relim |].
  constructor; [ unfold arm_ok; intros L i eff m HL HB Hfit Hn; apply arm_getgid_relim |].
  constructor; [ unfold arm_ok; intros L i eff m HL HB Hfit Hn; apply arm_getegid_relim |].
  constructor; [ unfold arm_ok; intros L i eff m HL HB Hfit Hn; apply arm_gettid_relim |].
  constructor; [ unfold arm_ok; intros L i eff m HL HB Hfit Hn; apply arm_socket_relim |].
  constructor; [ unfold arm_ok; intros L i eff m HL HB Hfit Hn; apply arm_socketpair_relim |].
  constructor; [ unfold arm_ok; intros L i eff m HL HB Hfit Hn; apply arm_bind_relim |].
  constructor; [ unfold arm_ok; intros L i eff m HL HB Hfit Hn; apply arm_listen_relim |].
  constructor; [ unfold arm_ok; intros L i eff m HL HB Hfit Hn; apply arm_accept_relim |].
  constructor; [ unfold arm_ok; intros L i eff m HL HB Hfit Hn; apply arm_connect_relim |].
  constructor; [ unfold arm_ok; intros L i eff m HL HB Hfit Hn; apply arm_getsockname_relim |].
  constructor; [ unfold arm_ok; intros L i eff m HL HB Hfit Hn; apply arm_getpeername_relim |].
  constructor; [ unfold arm_ok; intros L i eff m HL HB Hfit Hn; apply arm_sendto_relim |].
  constructor; [ unfold arm_ok; intros L i eff m HL HB Hfit Hn; apply arm_recvfrom_relim |].
  constructor; [ unfold arm_ok; intros L i eff m HL HB Hfit Hn; apply arm_setsockopt_relim |].
  constructor; [ unfold arm_ok; intros L i eff m HL HB Hfit Hn; apply arm_getsockopt_relim |].
  constructor; [ unfold arm_ok; intros L i eff m HL HB Hfit Hn; apply arm_shutdown_relim |].
  constructor; [ unfold arm_ok; intros L i eff m HL HB Hfit Hn; apply arm_sendmsg_relim |].
  constructor; [ unfold arm_ok; intros L i eff m HL HB Hfit Hn; apply arm_recvmsg_relim |].
  constructor; [ unfold arm_ok; intros L i eff m HL HB Hfit Hn; apply arm_brk_relim_b; [exact HL | unfold alloc_budget_refused_b in HB; rewrite Hn in HB; simpl in HB; exact HB] |].
  constructor; [ unfold arm_ok; intros L i eff m HL HB Hfit Hn; apply arm_munmap_relim |].
  constructor; [ unfold arm_ok; intros L i eff m HL HB Hfit Hn; apply arm_mremap_relim_fit; [exact HL | unfold alloc_budget_refused_b in HB; rewrite Hn in HB; simpl in HB; exact HB | exact Hfit] |].
  constructor; [ unfold arm_ok; intros L i eff m HL HB Hfit Hn; apply arm_clone_relim |].
  constructor; [ unfold arm_ok; intros L i eff m HL HB Hfit Hn; apply arm_mmap_relim_b; [exact HL | unfold alloc_budget_refused_b in HB; rewrite Hn in HB; simpl in HB; exact HB] |].
  constructor; [ unfold arm_ok; intros L i eff m HL HB Hfit Hn; apply arm_mprotect_relim_b; [exact HL | unfold alloc_budget_refused_b in HB; rewrite Hn in HB; simpl in HB; exact HB] |].
  constructor; [ unfold arm_ok; intros L i eff m HL HB Hfit Hn; apply arm_madvise_relim |].
  constructor; [ unfold arm_ok; intros L i eff m HL HB Hfit Hn; apply arm_accept4_relim |].
  constructor; [ unfold arm_ok; intros L i eff m HL HB Hfit Hn; apply arm_wait4_relim |].
  constructor; [ unfold arm_ok; intros L i eff m HL HB Hfit Hn; apply arm_prlimit64_relim |].
  constructor; [ unfold arm_ok; intros L i eff m HL HB Hfit Hn; apply arm_getrandom_relim |].
  constructor; [ unfold arm_ok; intros L i eff m HL HB Hfit Hn; apply arm_clone3_relim |].
  constructor; [ unfold arm_ok; intros L i eff m HL HB Hfit Hn; apply arm_faccessat2_relim |].
  constructor.
Qed.

Lemma lookup_ca_in : forall t n c, lookup_ca t n = Some c -> In c t /\ ca_no c = n.
Proof.
  induction t as [|c0 t IH]; intros n c H; [discriminate H|].
  cbn [lookup_ca] in H. destruct (Z.eqb (ca_no c0) n) eqn:E.
  - injection H as <-. split; [left; reflexivity | apply Z.eqb_eq; exact E].
  - destruct (IH n c H) as [Hin Hn]. split; [right; exact Hin | exact Hn].
Qed.

Lemma check_syscall_relim : forall L i eff m,
  (vm_limit (m_vmmaps m) <= L)%Z -> alloc_budget_refused_b i m = false -> vm_fit (m_vmmaps m) ->
  check_syscall i eff (relim L m) = map_cr (relim L) (check_syscall i eff m).
Proof.
  intros L i eff m HL HB Hfit. unfold check_syscall.
  destruct (lookup_ca checked_table (bv_unsigned (in_sysno i))) as [c|] eqn:E; [|reflexivity].
  destruct (lookup_ca_in _ _ _ E) as [Hin Hn].
  exact (proj1 (Forall_forall arm_ok checked_table) arms_ok c Hin L i eff m HL HB Hfit (eq_sym Hn)).
Qed.

Lemma relim_self : forall m, relim (vm_limit (m_vmmaps m)) m = m.
Proof. intros [fd [[r mp na sb b lim mb isp] lz mt] io fs pr lm tm]. reflexivity. Qed.

Lemma vm_limit_relim : forall L m, vm_limit (m_vmmaps (relim L m)) = L.
Proof. reflexivity. Qed.

Lemma syscall_spec_relim_ok : forall L i m eff m' evs,
  (vm_limit (m_vmmaps m) <= L)%Z -> alloc_budget_refused_b i m = false -> vm_fit (m_vmmaps m) ->
  syscall_spec i m (Ok eff m' evs) -> syscall_spec i (relim L m) (Ok eff (relim L m') evs).
Proof.
  intros L i m eff m' evs HL HB Hfit H. apply check_syscall_ok_iff in H. apply check_syscall_ok_iff.
  rewrite check_syscall_relim by assumption. rewrite H. reflexivity.
Qed.

Lemma syscall_spec_relim_ok_inv : forall L i m eff m2 evs,
  (vm_limit (m_vmmaps m) <= L)%Z -> alloc_budget_refused_b i m = false -> vm_fit (m_vmmaps m) ->
  syscall_spec i (relim L m) (Ok eff m2 evs) -> exists m', m2 = relim L m' /\ syscall_spec i m (Ok eff m' evs).
Proof.
  intros L i m eff m2 evs HL HB Hfit H. apply check_syscall_ok_iff in H.
  rewrite check_syscall_relim in H by assumption.
  destruct (check_syscall i eff m) as [m' evs'| |] eqn:E; cbn [map_cr] in H; try discriminate H.
  injection H as <- <-. exists m'. split; [reflexivity | apply check_syscall_ok_iff; exact E].
Qed.

Lemma syscall_spec_relim_unm : forall L i m,
  (vm_limit (m_vmmaps m) <= L)%Z -> alloc_budget_refused_b i m = false -> vm_fit (m_vmmaps m) ->
  (syscall_spec i (relim L m) Unmodeled <-> syscall_spec i m Unmodeled).
Proof.
  intros L i m HL HB Hfit. set (eff0 := mkEffect (Z_to_bv 64 0) [] []).
  rewrite <- (check_syscall_err_iff i eff0 (relim L m)), <- (check_syscall_err_iff i eff0 m).
  rewrite check_syscall_relim by assumption.
  destruct (check_syscall i eff0 m); cbn [map_cr]; split; intros H; try discriminate H; reflexivity.
Qed.

Lemma syscall_spec_limit : forall i m eff m' evs, alloc_budget_refused_b i m = false -> vm_fit (m_vmmaps m) ->
  syscall_spec i m (Ok eff m' evs) -> vm_limit (m_vmmaps m') = vm_limit (m_vmmaps m).
Proof.
  intros i m eff m' evs HB Hfit H. apply check_syscall_ok_iff in H.
  pose proof (check_syscall_relim (vm_limit (m_vmmaps m)) i eff m (Z.le_refl _) HB Hfit) as E.
  rewrite relim_self, H in E. cbn [map_cr] in E. injection E as E.
  rewrite E at 1. apply vm_limit_relim.
Qed.

Lemma vm_backing_used_relim : forall L m, vm_backing_used (relim L m) = vm_backing_used m.
Proof. reflexivity. Qed.

Lemma materialize_accesses_mono : forall lz mt u l1 l2 acc p, (l1 <= l2)%Z ->
  materialize_accesses lz mt u l1 acc = Some p -> materialize_accesses lz mt u l2 acc = Some p.
Proof.
  intros lz mt u l1 l2 acc p Hl H. unfold materialize_accesses in *.
  destruct (newly_materialized_pages lz mt acc) as [|q qs]; [exact H|].
  destruct (Z.leb_spec (u + Z.of_nat (length (q :: qs)) * page_size) l1) as [H1|H1]; [|discriminate H].
  destruct (Z.leb_spec (u + Z.of_nat (length (q :: qs)) * page_size) l2); [exact H | lia].
Qed.

Lemma materialize_relim_some : forall L m r m', (vm_limit (m_vmmaps m) <= L)%Z ->
  materialize_model_accesses m r = Some m' -> materialize_model_accesses (relim L m) r = Some (relim L m').
Proof.
  intros L m r m' HL H. unfold materialize_model_accesses in *.
  change (m_vm_lazy (relim L m)) with (m_vm_lazy m). change (m_vm_materialized (relim L m)) with (m_vm_materialized m).
  rewrite vm_backing_used_relim. change (vm_limit (m_vmmaps (relim L m))) with L.
  destruct (materialize_accesses (m_vm_lazy m) (m_vm_materialized m) (vm_backing_used m) (vm_limit (m_vmmaps m)) r)
    as [p|] eqn:E; [|discriminate H].
  injection H as <-. rewrite (materialize_accesses_mono _ _ _ _ _ _ _ HL E). reflexivity.
Qed.

Lemma materialize_relim_none : forall L m r, (vm_limit (m_vmmaps m) <= L)%Z ->
  materialize_model_accesses (relim L m) r = None -> materialize_model_accesses m r = None.
Proof.
  intros L m r HL H. destruct (materialize_model_accesses m r) as [m'|] eqn:E; [|reflexivity].
  rewrite (materialize_relim_some L m r m' HL E) in H. discriminate H.
Qed.

Lemma materialize_relim_inv : forall L m r m2, (vm_limit (m_vmmaps m) <= L)%Z ->
  materialize_model_accesses (relim L m) r = Some m2 ->
  materialize_model_accesses m r = None \/ exists m', materialize_model_accesses m r = Some m' /\ m2 = relim L m'.
Proof.
  intros L m r m2 HL H. destruct (materialize_model_accesses m r) as [m'|] eqn:E; [|left; reflexivity].
  right. exists m'. split; [reflexivity|]. rewrite (materialize_relim_some L m r m' HL E) in H. injection H as <-. reflexivity.
Qed.

Lemma materialize_limit : forall m r m', materialize_model_accesses m r = Some m' ->
  vm_limit (m_vmmaps m') = vm_limit (m_vmmaps m).
Proof. intros m r m' H. destruct (materialize_model_accesses_frame m r m' H) as (_ & H2 & _). rewrite H2. reflexivity. Qed.

Lemma refusal_b_relim : forall L i m ret, refusal_b i (relim L m) ret = refusal_b i m ret.
Proof. reflexivity. Qed.

Lemma spurious_relim : forall cfg L i m eff, (vm_limit (m_vmmaps m) <= L)%Z -> alloc_budget_refused_b i m = false -> vm_fit (m_vmmaps m) ->
  (spurious_refusal_cfg cfg i (relim L m) eff <-> spurious_refusal_cfg cfg i m eff).
Proof.
  intros cfg L i m eff HL HB Hfit. unfold spurious_refusal_cfg. rewrite refusal_b_relim. split.
  - intros (H1 & H2 & eff' & m' & evs' & H3 & H4). split; [exact H1|]. split; [exact H2|].
    destruct (syscall_spec_relim_ok_inv L i m eff' m' evs' HL HB Hfit H3) as (m'' & -> & H5).
    exists eff', m'', evs'. split; [exact H5 | rewrite refusal_b_relim in H4; exact H4].
  - intros (H1 & H2 & eff' & m' & evs' & H3 & H4). split; [exact H1|]. split; [exact H2|].
    exists eff', (relim L m'), evs'. split; [exact (syscall_spec_relim_ok L i m eff' m' evs' HL HB Hfit H3) | rewrite refusal_b_relim; exact H4].
Qed.

Definition relimc (L : Z) (c : config) : config := mkCfg (cfg_ms c) (relim L (cfg_model c)).
Definition relim_to (L : Z) (r : step_to) : step_to :=
  match r with SNext c => SNext (relimc L c) | SError => SError end.
Definition climit (c : config) : Z := vm_limit (m_vmmaps (cfg_model c)).
Definition cfit (c : config) : Prop := vm_fit (m_vmmaps (cfg_model c)).

Lemma nbr_instr : forall segs ms model report, ~ budget_refused_at segs (mkCfg ms model) ->
  m_halted model = None -> ms_svc_pending ms = None ->
  RiscvSemantics.step_accesses segs ms = MachineOk report ->
  materialize_model_accesses model (@accessed_ranges _ report) <> None.
Proof. intros segs ms model report Hn Hh Hs Hst Hm. apply Hn. split; [exact Hh|]. left. split; [exact Hs|]. exists report. split; assumption. Qed.

Lemma nbr_sys_b : forall segs ms model x8, ~ budget_refused_at segs (mkCfg ms model) ->
  m_halted model = None -> ms_svc_pending ms = Some x8 ->
  alloc_budget_refused_b (sys_input segs ms x8) model = false.
Proof.
  intros segs ms model x8 Hn Hh Hs. destruct (alloc_budget_refused_b _ _) eqn:E; [|reflexivity].
  exfalso. apply Hn. split; [exact Hh|]. right. exists x8. split; [exact Hs|]. left. exact E.
Qed.

Lemma nbr_sys_mat : forall segs ms model x8 eff model' evs, ~ budget_refused_at segs (mkCfg ms model) ->
  m_halted model = None -> ms_svc_pending ms = Some x8 ->
  syscall_spec (sys_input segs ms x8) model (Ok eff model' evs) -> m_halted model' = None ->
  materialize_model_accesses model' (syscall_effect_accesses eff) <> None.
Proof.
  intros segs ms model x8 eff model' evs Hn Hh Hs Hspec Hh' Hm. apply Hn. split; [exact Hh|]. right. exists x8.
  split; [exact Hs|]. right. exists eff, model', evs. repeat split; assumption.
Qed.

Lemma account_relim_up : forall segs L ms model ms' model', (vm_limit (m_vmmaps model) <= L)%Z ->
  mi_account_step segs ms model = MachineOk (ms', model') ->
  mi_account_step segs ms (relim L model) = MachineOk (ms', relim L model').
Proof.
  intros segs L ms model ms' model' HL H. unfold mi_account_step in *.
  destruct (RiscvSemantics.step_accesses segs ms) as [report| |]; try discriminate H.
  destruct (materialize_model_accesses model _) as [m1|] eqn:E; [|discriminate H].
  injection H as <- <-. rewrite (materialize_relim_some L model _ m1 HL E). reflexivity.
Qed.

Lemma account_relim_down : forall segs L ms model ms' m2, (vm_limit (m_vmmaps model) <= L)%Z ->
  ~ budget_refused_at segs (mkCfg ms model) -> m_halted model = None -> ms_svc_pending ms = None ->
  mi_account_step segs ms (relim L model) = MachineOk (ms', m2) ->
  exists model', mi_account_step segs ms model = MachineOk (ms', model') /\ m2 = relim L model'.
Proof.
  intros segs L ms model ms' m2 HL Hn Hh Hs H. unfold mi_account_step in *.
  destruct (RiscvSemantics.step_accesses segs ms) as [report| |] eqn:Est; try discriminate H.
  destruct (materialize_model_accesses (relim L model) _) as [m1|] eqn:E; [|discriminate H].
  injection H as <- <-.
  destruct (materialize_relim_inv L model _ m1 HL E) as [E0 | (m' & E1 & ->)].
  - exfalso. exact (nbr_instr segs ms model report Hn Hh Hs Est E0).
  - exists m'. rewrite E1. split; reflexivity.
Qed.

Lemma account_relim_fault_up : forall segs L ms model, (vm_limit (m_vmmaps model) <= L)%Z ->
  ~ budget_refused_at segs (mkCfg ms model) -> m_halted model = None -> ms_svc_pending ms = None ->
  mi_account_step segs ms model = MachineFault -> mi_account_step segs ms (relim L model) = MachineFault.
Proof.
  intros segs L ms model HL Hn Hh Hs H. unfold mi_account_step in *.
  destruct (RiscvSemantics.step_accesses segs ms) as [report| |] eqn:Est; try discriminate H; [|reflexivity].
  destruct (materialize_model_accesses model _) as [m1|] eqn:E; [discriminate H|].
  exfalso. exact (nbr_instr segs ms model report Hn Hh Hs Est E).
Qed.

Lemma account_relim_fault_down : forall segs L ms model, (vm_limit (m_vmmaps model) <= L)%Z ->
  mi_account_step segs ms (relim L model) = MachineFault -> mi_account_step segs ms model = MachineFault.
Proof.
  intros segs L ms model HL H. unfold mi_account_step in *.
  destruct (RiscvSemantics.step_accesses segs ms) as [report| |]; try discriminate H; [|reflexivity].
  destruct (materialize_model_accesses (relim L model) _) as [m1|] eqn:E; [discriminate H|].
  rewrite (materialize_relim_none L model _ HL E). reflexivity.
Qed.

Lemma account_relim_unm : forall segs L ms model,
  mi_account_step segs ms (relim L model) = MachineUnmodeled <-> mi_account_step segs ms model = MachineUnmodeled.
Proof.
  intros segs L ms model. unfold mi_account_step.
  destruct (RiscvSemantics.step_accesses segs ms) as [report| |]; [|split; intros H; discriminate H|tauto].
  destruct (materialize_model_accesses (relim L model) _), (materialize_model_accesses model _);
    split; intros H; discriminate H.
Qed.

Lemma sstep_relim_up : forall segs cfg L c evs r, (climit c <= L)%Z -> ~ budget_refused_at segs c -> cfit c ->
  sstep_cfg segs cfg c evs r -> sstep_cfg segs cfg (relimc L c) evs (relim_to L r).
Proof.
  intros segs cfg L c evs r HL Hn Hf H. unfold climit in HL. unfold cfit in Hf.
  destruct H as [ms model ms' model' Hh Hs Ha | ms model Hh Hs Ha | ms model Hh Hs Ha
                | ms model x8 eff model' model'' evs Hh Hs Hspec Hsp Hh' Hmat
                | ms model x8 eff model' evs Hh Hs Hspec Hsp Hh' Hmat
                | ms model x8 eff model' evs code Hh Hs Hspec Hh' Hk
                | ms model x8 eff model' evs sig Hh Hs Hspec Hk
                | ms model x8 Hh Hs Hspec ]; cbn [relimc relim_to cfg_ms cfg_model] in *.
  - apply sstep_cfg_instr; [exact Hh | exact Hs | exact (account_relim_up segs L ms model ms' model' HL Ha)].
  - apply sstep_cfg_instr_fault; [exact Hh | exact Hs | exact (account_relim_fault_up segs L ms model HL Hn Hh Hs Ha)].
  - apply sstep_cfg_instr_unmodeled; [exact Hh | exact Hs | apply account_relim_unm; exact Ha].
  - pose proof (nbr_sys_b segs ms model x8 Hn Hh Hs) as HB.
    pose proof (syscall_spec_limit _ _ _ _ _ HB Hf Hspec) as Hlim.
    apply (sstep_cfg_syscall segs cfg ms (relim L model) x8 eff (relim L model') (relim L model'') evs);
      [exact Hh | exact Hs | exact (syscall_spec_relim_ok L _ model eff model' evs HL HB Hf Hspec)
      | rewrite spurious_relim by assumption; exact Hsp | exact Hh'
      | apply materialize_relim_some; [rewrite Hlim; exact HL | exact Hmat]].
  - exfalso. exact (nbr_sys_mat segs ms model x8 eff model' evs Hn Hh Hs Hspec Hh' Hmat).
  - pose proof (nbr_sys_b segs ms model x8 Hn Hh Hs) as HB.
    apply (sstep_cfg_exit segs cfg ms (relim L model) x8 eff (relim L model') evs code);
      [exact Hh | exact Hs | exact (syscall_spec_relim_ok L _ model eff model' evs HL HB Hf Hspec) | exact Hh' | exact Hk].
  - pose proof (nbr_sys_b segs ms model x8 Hn Hh Hs) as HB.
    apply (sstep_cfg_killed segs cfg ms (relim L model) x8 eff (relim L model') evs sig);
      [exact Hh | exact Hs | exact (syscall_spec_relim_ok L _ model eff model' evs HL HB Hf Hspec) | exact Hk].
  - pose proof (nbr_sys_b segs ms model x8 Hn Hh Hs) as HB.
    apply (sstep_cfg_syscall_unmodeled segs cfg ms (relim L model) x8); [exact Hh | exact Hs | apply syscall_spec_relim_unm; assumption].
Qed.

Lemma sstep_relim_down : forall segs cfg L c evs r2, (climit c <= L)%Z -> ~ budget_refused_at segs c -> cfit c ->
  sstep_cfg segs cfg (relimc L c) evs r2 -> exists r1, sstep_cfg segs cfg c evs r1 /\ r2 = relim_to L r1.
Proof.
  intros segs cfg L [ms model] evs r2 HL Hn Hf H. unfold climit in HL. unfold cfit in Hf. cbn [cfg_model] in HL, Hf.
  unfold relimc in H. cbn [cfg_ms cfg_model] in H.
  remember (mkCfg ms (relim L model)) as c2 eqn:Ec.
  destruct H as [ms0 model0 ms' m2 Hh Hs Ha | ms0 model0 Hh Hs Ha | ms0 model0 Hh Hs Ha
                | ms0 model0 x8 eff m2' m2'' evs Hh Hs Hspec Hsp Hh' Hmat
                | ms0 model0 x8 eff m2' evs Hh Hs Hspec Hsp Hh' Hmat
                | ms0 model0 x8 eff m2' evs code Hh Hs Hspec Hh' Hk
                | ms0 model0 x8 eff m2' evs sig Hh Hs Hspec Hk
                | ms0 model0 x8 Hh Hs Hspec ];
    injection Ec as -> ->.
  - destruct (account_relim_down segs L ms model ms' m2 HL Hn Hh Hs Ha) as (model' & Ha' & ->).
    exists (SNext (mkCfg ms' model')). split; [apply sstep_cfg_instr; assumption | reflexivity].
  - exists SError. split; [apply sstep_cfg_instr_fault; [exact Hh | exact Hs | exact (account_relim_fault_down segs L ms model HL Ha)] | reflexivity].
  - exists SError. split; [apply sstep_cfg_instr_unmodeled; [exact Hh | exact Hs | apply (account_relim_unm segs L); exact Ha] | reflexivity].
  - pose proof (nbr_sys_b segs ms model x8 Hn Hh Hs) as HB.
    destruct (syscall_spec_relim_ok_inv L _ model eff m2' evs HL HB Hf Hspec) as (model' & -> & Hspec').
    pose proof (syscall_spec_limit _ _ _ _ _ HB Hf Hspec') as Hlim.
    assert (HL' : (vm_limit (m_vmmaps model') <= L)%Z) by (rewrite Hlim; exact HL).
    destruct (materialize_relim_inv L model' _ m2'' HL' Hmat) as [E0 | (model'' & E1 & ->)].
    + exfalso. exact (nbr_sys_mat segs ms model x8 eff model' evs Hn Hh Hs Hspec' Hh' E0).
    + exists (SNext (mkCfg (advance_past_svc (apply_effect ms eff)) model'')). split; [|reflexivity].
      apply (sstep_cfg_syscall segs cfg ms model x8 eff model' model'' evs);
        [exact Hh | exact Hs | exact Hspec' | rewrite <- (spurious_relim cfg L) by assumption; exact Hsp | exact Hh' | exact E1].
  - pose proof (nbr_sys_b segs ms model x8 Hn Hh Hs) as HB.
    destruct (syscall_spec_relim_ok_inv L _ model eff m2' evs HL HB Hf Hspec) as (model' & -> & Hspec').
    pose proof (syscall_spec_limit _ _ _ _ _ HB Hf Hspec') as Hlim.
    assert (HL' : (vm_limit (m_vmmaps model') <= L)%Z) by (rewrite Hlim; exact HL).
    exfalso. exact (nbr_sys_mat segs ms model x8 eff model' evs Hn Hh Hs Hspec' Hh' (materialize_relim_none L model' _ HL' Hmat)).
  - pose proof (nbr_sys_b segs ms model x8 Hn Hh Hs) as HB.
    destruct (syscall_spec_relim_ok_inv L _ model eff m2' evs HL HB Hf Hspec) as (model' & -> & Hspec').
    exists (SNext (mkCfg ms model')). split; [|reflexivity].
    apply (sstep_cfg_exit segs cfg ms model x8 eff model' evs code); assumption.
  - pose proof (nbr_sys_b segs ms model x8 Hn Hh Hs) as HB.
    destruct (syscall_spec_relim_ok_inv L _ model eff m2' evs HL HB Hf Hspec) as (model' & -> & Hspec').
    exists (SNext (mkCfg ms model')). split; [|reflexivity].
    apply (sstep_cfg_killed segs cfg ms model x8 eff model' evs sig); assumption.
  - pose proof (nbr_sys_b segs ms model x8 Hn Hh Hs) as HB.
    exists SError. split; [|reflexivity].
    apply (sstep_cfg_syscall_unmodeled segs cfg ms model x8); [exact Hh | exact Hs | apply (syscall_spec_relim_unm L); assumption].
Qed.

Lemma sstep_limit : forall segs cfg c evs c', ~ budget_refused_at segs c -> cfit c ->
  sstep_cfg segs cfg c evs (SNext c') -> climit c' = climit c.
Proof.
  intros segs cfg c evs c' Hn Hf H. unfold climit. unfold cfit in Hf.
  inversion H as [ms model ms' model' Hh Hs Ha | | | ms model x8 eff model' model'' evs0 Hh Hs Hspec Hsp Hh' Hmat
                 | | ms model x8 eff model' evs0 code Hh Hs Hspec Hh' Hk | ms model x8 eff model' evs0 sig Hh Hs Hspec Hk | ];
    subst; cbn [cfg_model] in *.
  - pose proof (mi_account_step_model_frame segs ms model ms' model' Ha) as Hfr.
    unfold mi_account_step in Ha.
    destruct (RiscvSemantics.step_accesses segs ms) as [report| |]; try discriminate Ha.
    destruct (materialize_model_accesses model _) as [m1|] eqn:E; [|discriminate Ha].
    injection Ha as _ <-. exact (materialize_limit _ _ _ E).
  - pose proof (nbr_sys_b segs ms model x8 Hn Hh Hs) as HB.
    rewrite (materialize_limit _ _ _ Hmat). exact (syscall_spec_limit _ _ _ _ _ HB Hf Hspec).
  - exact (syscall_spec_limit _ _ _ _ _ (nbr_sys_b segs ms model x8 Hn Hh Hs) Hf Hspec).
  - exact (syscall_spec_limit _ _ _ _ _ (nbr_sys_b segs ms model x8 Hn Hh Hs) Hf Hspec).
Qed.

Lemma materialize_vmmaps : forall m r m', materialize_model_accesses m r = Some m' -> m_vmmaps m' = m_vmmaps m.
Proof. intros m r m' H. destruct (materialize_model_accesses_frame m r m' H) as (_ & H2 & _). exact H2. Qed.

Lemma sstep_fit : forall segs cfg c evs c', sstep_cfg segs cfg c evs (SNext c') -> cfit c -> cfit c'.
Proof.
  intros segs cfg c evs c' H Hf. unfold cfit in *.
  inversion H as [ms model ms' model' Hh Hs Ha | | | ms model x8 eff model' model'' evs0 Hh Hs Hspec Hsp Hh' Hmat
                 | | ms model x8 eff model' evs0 code Hh Hs Hspec Hh' Hk | ms model x8 eff model' evs0 sig Hh Hs Hspec Hk | ];
    subst; cbn [cfg_model] in *.
  - unfold mi_account_step in Ha.
    destruct (RiscvSemantics.step_accesses segs ms) as [report| |]; try discriminate Ha.
    destruct (materialize_model_accesses model _) as [m1|] eqn:E; [|discriminate Ha].
    injection Ha as _ <-. rewrite (materialize_vmmaps _ _ _ E). exact Hf.
  - rewrite (materialize_vmmaps _ _ _ Hmat). exact (syscall_spec_preserves_fit _ _ _ _ _ Hspec Hf).
  - exact (syscall_spec_preserves_fit _ _ _ _ _ Hspec Hf).
  - exact (syscall_spec_preserves_fit _ _ _ _ _ Hspec Hf).
Qed.

Lemma star_fit : forall segs cfg c tr c', star_cfg segs cfg c tr c' -> cfit c -> cfit c'.
Proof.
  intros segs cfg c tr c' H. induction H as [c | c1 evs c2 tr c3 Hs Hst IH]; intros Hf; [exact Hf|].
  apply IH. exact (sstep_fit segs cfg c1 evs c2 Hs Hf).
Qed.

Lemma nreach_here : forall segs cfg c, ~ reaches_budget_refused_cfg segs cfg c -> ~ budget_refused_at segs c.
Proof. intros segs cfg c H Hb. apply H. exists [], c. split; [apply star_cfg_refl | exact Hb]. Qed.

Lemma nreach_step : forall segs cfg c evs c', ~ reaches_budget_refused_cfg segs cfg c ->
  sstep_cfg segs cfg c evs (SNext c') -> ~ reaches_budget_refused_cfg segs cfg c'.
Proof.
  intros segs cfg c evs c' H Hs (tr & c2 & Hst & Hb). apply H. exists (evs ++ tr), c2. split; [|exact Hb].
  eapply star_cfg_step; [exact Hs | exact Hst].
Qed.

Lemma star_relim_up : forall segs cfg L c tr c', star_cfg segs cfg c tr c' ->
  (climit c <= L)%Z -> ~ reaches_budget_refused_cfg segs cfg c -> cfit c ->
  star_cfg segs cfg (relimc L c) tr (relimc L c') /\ climit c' = climit c.
Proof.
  intros segs cfg L c tr c' H. induction H as [c | c1 evs c2 tr c3 Hs Hst IH]; intros HL Hn Hf.
  - split; [apply star_cfg_refl | reflexivity].
  - pose proof (nreach_here segs cfg c1 Hn) as Hn1.
    pose proof (sstep_limit segs cfg c1 evs c2 Hn1 Hf Hs) as Hl.
    destruct IH as [IH1 IH2];
      [rewrite Hl; exact HL | exact (nreach_step segs cfg c1 evs c2 Hn Hs) | exact (sstep_fit segs cfg c1 evs c2 Hs Hf) |].
    split; [| rewrite IH2; exact Hl].
    eapply star_cfg_step; [exact (sstep_relim_up segs cfg L c1 evs (SNext c2) HL Hn1 Hf Hs) | exact IH1].
Qed.

Lemma star_relim_down : forall segs cfg L c2 tr c2', star_cfg segs cfg c2 tr c2' ->
  forall c, c2 = relimc L c -> (climit c <= L)%Z -> ~ reaches_budget_refused_cfg segs cfg c -> cfit c ->
  exists c', star_cfg segs cfg c tr c' /\ c2' = relimc L c' /\ climit c' = climit c.
Proof.
  intros segs cfg L c2 tr c2' H. induction H as [c0 | c1 evs c3 tr c4 Hs Hst IH]; intros c E HL Hn Hf.
  - exists c. split; [apply star_cfg_refl | split; [exact E | reflexivity]].
  - subst c1. pose proof (nreach_here segs cfg c Hn) as Hn1.
    destruct (sstep_relim_down segs cfg L c evs (SNext c3) HL Hn1 Hf Hs) as ([c5|] & Hs5 & E5); [|discriminate E5].
    injection E5 as E5. pose proof (sstep_limit segs cfg c evs c5 Hn1 Hf Hs5) as Hl.
    destruct (IH c5 E5 ltac:(rewrite Hl; exact HL) (nreach_step segs cfg c evs c5 Hn Hs5) (sstep_fit segs cfg c evs c5 Hs5 Hf))
      as (c6 & H6 & E6 & L6).
    exists c6. split; [eapply star_cfg_step; [exact Hs5 | exact H6] | split; [exact E6 | rewrite L6; exact Hl]].
Qed.

Lemma obs_relim : forall segs cfg L c, (climit c <= L)%Z -> ~ reaches_budget_refused_cfg segs cfg c -> cfit c ->
  forall tr, obs_trace_cfg segs cfg c tr <-> obs_trace_cfg segs cfg (relimc L c) tr.
Proof.
  intros segs cfg L c HL Hn Hf tr. split.
  - intros (tr' & c' & Hst & Hp). exists tr', (relimc L c').
    split; [exact (proj1 (star_relim_up segs cfg L c tr' c' Hst HL Hn Hf)) | exact Hp].
  - intros (tr' & c2' & Hst & Hp).
    destruct (star_relim_down segs cfg L _ tr' c2' Hst c eq_refl HL Hn Hf) as (c' & H1 & _ & _).
    exists tr', c'. split; [exact H1 | exact Hp].
Qed.

Lemma err_relim : forall segs cfg L c, (climit c <= L)%Z -> ~ reaches_budget_refused_cfg segs cfg c -> cfit c ->
  (reaches_error_cfg segs cfg c <-> reaches_error_cfg segs cfg (relimc L c)).
Proof.
  intros segs cfg L c HL Hn Hf. split.
  - intros (tr & c' & evs & Hst & He).
    destruct (star_relim_up segs cfg L c tr c' Hst HL Hn Hf) as [H1 H2].
    exists tr, (relimc L c'), evs. split; [exact H1|].
    assert (Hn' : ~ budget_refused_at segs c').
    { intros Hb. apply Hn. exists tr, c'. split; assumption. }
    exact (sstep_relim_up segs cfg L c' evs SError ltac:(rewrite H2; exact HL) Hn' (star_fit segs cfg c tr c' Hst Hf) He).
  - intros (tr & c2' & evs & Hst & He).
    destruct (star_relim_down segs cfg L _ tr c2' Hst c eq_refl HL Hn Hf) as (c' & H1 & -> & H3).
    assert (Hn' : ~ budget_refused_at segs c').
    { intros Hb. apply Hn. exists tr, c'. split; assumption. }
    destruct (sstep_relim_down segs cfg L c' evs SError ltac:(rewrite H3; exact HL) Hn' (star_fit segs cfg c tr c' H1 Hf) He)
      as ([c5|] & H5 & E5); [discriminate E5|].
    exists tr, c', evs. split; assumption.
Qed.

Lemma init_config_relim : forall segs pc ph sp brk mb rnd L1 L2 inp,
  relimc L2 (init_config segs pc ph sp brk mb rnd L1 inp) = init_config segs pc ph sp brk mb rnd L2 inp.
Proof. reflexivity. Qed.

Lemma init_config_limit : forall segs pc ph sp brk mb rnd L inp, climit (init_config segs pc ph sp brk mb rnd L inp) = L.
Proof. reflexivity. Qed.

Lemma init_config_fit : forall segs pc ph sp brk mb rnd L inp, cfit (init_config segs pc ph sp brk mb rnd L inp).
Proof.
  intros. unfold cfit, vm_fit, fitl.
  assert (Hm : vm_maps (m_vmmaps (cfg_model (init_config segs pc ph sp brk mb rnd L inp))) = []) by reflexivity.
  rewrite Hm. intros a sz [].
Qed.

Theorem run_budget_bridge : forall cfg img en inp L1 L2, (L1 <= L2)%Z ->
  ~ run_scfg_budget_refused cfg img L1 en inp ->
  (forall tr, bh_traces (run_scfg cfg img L1 en inp) tr <-> bh_traces (run_scfg cfg img L2 en inp) tr)
  /\ (bh_errors (run_scfg cfg img L1 en inp) <-> bh_errors (run_scfg cfg img L2 en inp)).
Proof.
  intros cfg [segs pc ph] [sp brk mb rnd] inp L1 L2 HL Hn. cbn [run_scfg bh_traces bh_errors run_scfg_budget_refused] in *.
  rewrite <- (init_config_relim segs pc ph sp brk mb rnd L1 L2 inp).
  split.
  - apply obs_relim; [rewrite init_config_limit; exact HL | exact Hn | apply init_config_fit].
  - apply err_relim; [rewrite init_config_limit; exact HL | exact Hn | apply init_config_fit].
Qed.

Theorem error_free_scfg_budgets_abort_sanitizer_of_pinned : forall cfg S T,
  (forall en_s en_t inp, valid_entry S en_s inp -> valid_entry T en_t inp -> valid_input_abort inp ->
     strong_equiv_error_free_budgets_scfg_abort cfg source_alloc_limit target_alloc_limit S T en_s en_t inp) ->
  strong_universal_error_free_T_scfg_budgets_abort cfg sanitizer_source_limit target_alloc_limit S T.
Proof.
  intros cfg S T H en_s en_t inp Hs Ht Hv Hb.
  destruct (H en_s en_t inp Hs Ht Hv) as (Hse & Hte & Htr).
  assert (HL : (sanitizer_source_limit <= source_alloc_limit)%Z)
    by (unfold sanitizer_source_limit, source_alloc_limit; lia).
  destruct (run_budget_bridge cfg S en_s inp sanitizer_source_limit source_alloc_limit HL Hb) as [Btr Ber].
  unfold strong_equiv_error_free_budgets_scfg_abort. split; [|split].
  - destruct Hse as (He & Hk). split.
    + intros E. apply He. apply Ber. exact E.
    + intros (tr & sig & fs & Htr1 & Hin). apply Hk. exists tr, sig, fs. split; [apply Btr; exact Htr1 | exact Hin].
  - exact Hte.
  - intros tr. rewrite Btr. apply Htr.
Qed.

