(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import LimBase LimMonad LimStep LimFit LimInv LimArmsAuto1 LimArmsAuto2 LimArmsAuto3 LimArmsVm LimArmsMremap.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section Dispatch.
Variable L : Z.

Definition arm_ok (a : SpecArm) : Prop :=
  forall i m, bv_unsigned (in_sysno i) = sa_no a -> linv m -> L <= mlim m ->
    alloc_budget_refused_b i (sl L m) = false ->
    FR L i m (sa_spec a) (sa_spec a).

(* [comment removed for export] *)
Lemma FR_eta {A} : forall i m (c : SyscallInput -> Sys A),
  FR L i m (c i) (c i) -> FR L i m (fun i0 => c i0 i0) (fun i0 => c i0 i0).
Proof. intros i m c H. exact H. Qed.

Lemma lookup_arm_some : forall t n a, lookup_arm t n = Some a -> In a t /\ sa_no a = n.
Proof.
  induction t as [| b r IH]; intros n a H; cbn [lookup_arm] in H; [discriminate |].
  destruct (Z.eqb (sa_no b) n) eqn:E.
  - injection H as <-. split; [left; reflexivity | apply Z.eqb_eq; exact E].
  - destruct (IH n a H) as [Hin Hn]. split; [right; exact Hin | exact Hn].
Qed.

Lemma dispatch_lt : forall t, Forall arm_ok t ->
  forall i m, linv m -> L <= mlim m -> alloc_budget_refused_b i (sl L m) = false ->
    FR L i m (dispatch t) (dispatch t).
Proof.
  intros t Ht i m HF HL Hb.
  destruct (lookup_arm t (bv_unsigned (in_sysno i))) as [a |] eqn:E.
  - destruct (lookup_arm_some _ _ _ E) as [Hin Hno].
    pose proof (proj1 (Forall_forall _ _) Ht a Hin i m (eq_sym Hno) HF HL Hb) as F.
    unfold FR in *. unfold dispatch. rewrite E. exact F.
  - unfold FR. unfold dispatch. rewrite E. exact (FR_unmodeled L i m).
Qed.

(* [comment removed for export] *)
Lemma mark_brk : forall i m, bv_unsigned (in_sysno i) = 214 ->
  alloc_budget_refused_b i m = false -> brk_budget_refused_b m (in_arg i 0) = false.
Proof. intros i m Hn H. unfold alloc_budget_refused_b in H. rewrite Hn in H. exact H. Qed.
Lemma mark_mremap : forall i m, bv_unsigned (in_sysno i) = 216 ->
  alloc_budget_refused_b i m = false ->
  mremap_budget_refused_b (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) m = false.
Proof. intros i m Hn H. unfold alloc_budget_refused_b in H. rewrite Hn in H. exact H. Qed.
Lemma mark_mmap : forall i m, bv_unsigned (in_sysno i) = 222 ->
  alloc_budget_refused_b i m = false ->
  mmap_budget_refused_b (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) (in_arg i 5) m = false.
Proof. intros i m Hn H. unfold alloc_budget_refused_b in H. rewrite Hn in H. exact H. Qed.
Lemma mark_mprotect : forall i m, bv_unsigned (in_sysno i) = 226 ->
  alloc_budget_refused_b i m = false ->
  mprotect_budget_refused_b (in_arg i 0) (in_arg i 1) (in_arg i 2) m = false.
Proof. intros i m Hn H. unfold alloc_budget_refused_b in H. rewrite Hn in H. exact H. Qed.

Lemma spec_table_ok : Forall arm_ok spec_table.
Proof.
  unfold spec_table.
  (* [comment removed for export] *)
  apply Forall_cons.
  { intros i m Hn HF HL Hb. cbn [sa_no] in Hn. cbn [sa_spec].
    apply (FR_eta i m (fun i => getcwd_spec (in_arg i 1))); cbv beta.
    exact (fr_arm_17 L i m). }
  (* [comment removed for export] *)
  apply Forall_cons.
  { intros i m Hn HF HL Hb. cbn [sa_no] in Hn. cbn [sa_spec].
    apply (FR_eta i m (fun i => eventfd2_spec (flag32 (in_arg i 1)))); cbv beta.
    exact (fr_arm_19 L i m). }
  (* [comment removed for export] *)
  apply Forall_cons.
  { intros i m Hn HF HL Hb. cbn [sa_no] in Hn. cbn [sa_spec].
    apply (FR_eta i m (fun i => epoll_create1_spec (flag32 (in_arg i 0)))); cbv beta.
    exact (fr_arm_20 L i m). }
  (* [comment removed for export] *)
  apply Forall_cons.
  { intros i m Hn HF HL Hb. cbn [sa_no] in Hn. cbn [sa_spec].
    apply (FR_eta i m (fun i => epoll_ctl_spec (fd32 (in_arg i 0)) (int32 (in_arg i 1)) (fd32 (in_arg i 2)) (in_arg i 3))); cbv beta.
    exact (fr_arm_21 L i m). }
  (* [comment removed for export] *)
  apply Forall_cons.
  { intros i m Hn HF HL Hb. cbn [sa_no] in Hn. cbn [sa_spec].
    apply (FR_eta i m (fun i => epoll_pwait_spec (fd32 (in_arg i 0)) (in_arg i 1) (int32 (in_arg i 2)) (in_arg i 4) (in_arg i 5))); cbv beta.
    exact (fr_arm_22 L i m). }
  (* [comment removed for export] *)
  apply Forall_cons.
  { intros i m Hn HF HL Hb. cbn [sa_no] in Hn. cbn [sa_spec].
    apply (FR_eta i m (fun i => dup_spec (fd32 (in_arg i 0)))); cbv beta.
    exact (fr_arm_23 L i m). }
  (* [comment removed for export] *)
  apply Forall_cons.
  { intros i m Hn HF HL Hb. cbn [sa_no] in Hn. cbn [sa_spec].
    apply (FR_eta i m (fun i => dup3_spec (fd32 (in_arg i 0)) (fd32 (in_arg i 1)) (in_arg i 2))); cbv beta.
    exact (fr_arm_24 L i m). }
  (* [comment removed for export] *)
  apply Forall_cons.
  { intros i m Hn HF HL Hb. cbn [sa_no] in Hn. cbn [sa_spec].
    apply (FR_eta i m (fun i => fcntl_spec (fd32 (in_arg i 0)) (cmd32 (in_arg i 1)) (in_arg i 2))); cbv beta.
    exact (fr_arm_25 L i m). }
  (* [comment removed for export] *)
  apply Forall_cons.
  { intros i m Hn HF HL Hb. cbn [sa_no] in Hn. cbn [sa_spec].
    apply (FR_eta i m (fun i => ioctl_spec (fd32 (in_arg i 0)) (cmd32 (in_arg i 1)))); cbv beta.
    exact (fr_arm_29 L i m). }
  (* [comment removed for export] *)
  apply Forall_cons.
  { intros i m Hn HF HL Hb. cbn [sa_no] in Hn. cbn [sa_spec].
    apply (FR_eta i m (fun i => flock_spec (fd32 (in_arg i 0)) (cmd32 (in_arg i 1)))); cbv beta.
    exact (fr_arm_32 L i m). }
  (* [comment removed for export] *)
  apply Forall_cons.
  { intros i m Hn HF HL Hb. cbn [sa_no] in Hn. cbn [sa_spec].
    apply (FR_eta i m (fun i => unlinkat_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2))); cbv beta.
    exact (fr_arm_35 L i m). }
  (* [comment removed for export] *)
  apply Forall_cons.
  { intros i m Hn HF HL Hb. cbn [sa_no] in Hn. cbn [sa_spec].
    apply (FR_eta i m (fun i => ftruncate_spec (fd32 (in_arg i 0)) (in_arg i 1))); cbv beta.
    exact (fr_arm_46 L i m). }
  (* [comment removed for export] *)
  apply Forall_cons.
  { intros i m Hn HF HL Hb. cbn [sa_no] in Hn. cbn [sa_spec].
    apply (FR_eta i m (fun i => faccessat_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2))); cbv beta.
    exact (fr_arm_48 L i m). }
  (* [comment removed for export] *)
  apply Forall_cons.
  { intros i m Hn HF HL Hb. cbn [sa_no] in Hn. cbn [sa_spec].
    apply (FR_eta i m (fun i => openat_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2))); cbv beta.
    exact (fr_arm_56 L i m). }
  (* [comment removed for export] *)
  apply Forall_cons.
  { intros i m Hn HF HL Hb. cbn [sa_no] in Hn. cbn [sa_spec].
    apply (FR_eta i m (fun i => close_spec (fd32 (in_arg i 0)))); cbv beta.
    exact (fr_arm_57 L i m). }
  (* [comment removed for export] *)
  apply Forall_cons.
  { intros i m Hn HF HL Hb. cbn [sa_no] in Hn. cbn [sa_spec].
    apply (FR_eta i m (fun i => pipe2_spec (in_arg i 0) (pipe_flags32 (in_arg i 1)))); cbv beta.
    exact (fr_arm_59 L i m). }
  (* [comment removed for export] *)
  apply Forall_cons.
  { intros i m Hn HF HL Hb. cbn [sa_no] in Hn. cbn [sa_spec].
    apply (FR_eta i m (fun i => getdents64_spec (fd32 (in_arg i 0)) (in_arg i 2))); cbv beta.
    exact (fr_arm_61 L i m). }
  (* [comment removed for export] *)
  apply Forall_cons.
  { intros i m Hn HF HL Hb. cbn [sa_no] in Hn. cbn [sa_spec].
    apply (FR_eta i m (fun i => lseek_spec (fd32 (in_arg i 0)) (in_arg i 1) (whence32 (in_arg i 2)))); cbv beta.
    exact (fr_arm_62 L i m). }
  (* [comment removed for export] *)
  apply Forall_cons.
  { intros i m Hn HF HL Hb. cbn [sa_no] in Hn. cbn [sa_spec].
    apply (FR_eta i m (fun i => read_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2))); cbv beta.
    exact (fr_arm_63 L i m). }
  (* [comment removed for export] *)
  apply Forall_cons.
  { intros i m Hn HF HL Hb. cbn [sa_no] in Hn. cbn [sa_spec].
    apply (FR_eta i m (fun i => write_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2))); cbv beta.
    exact (fr_arm_64 L i m). }
  (* [comment removed for export] *)
  apply Forall_cons.
  { intros i m Hn HF HL Hb. cbn [sa_no] in Hn. cbn [sa_spec].
    apply (FR_eta i m (fun i => readv_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2))); cbv beta.
    exact (fr_arm_65 L i m). }
  (* [comment removed for export] *)
  apply Forall_cons.
  { intros i m Hn HF HL Hb. cbn [sa_no] in Hn. cbn [sa_spec].
    apply (FR_eta i m (fun i => writev_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2))); cbv beta.
    exact (fr_arm_66 L i m). }
  (* [comment removed for export] *)
  apply Forall_cons.
  { intros i m Hn HF HL Hb. cbn [sa_no] in Hn. cbn [sa_spec].
    apply (FR_eta i m (fun i => pread64_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3))); cbv beta.
    exact (fr_arm_67 L i m). }
  (* [comment removed for export] *)
  apply Forall_cons.
  { intros i m Hn HF HL Hb. cbn [sa_no] in Hn. cbn [sa_spec].
    apply (FR_eta i m (fun i => pwrite64_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3))); cbv beta.
    exact (fr_arm_68 L i m). }
  (* [comment removed for export] *)
  apply Forall_cons.
  { intros i m Hn HF HL Hb. cbn [sa_no] in Hn. cbn [sa_spec].
    apply (FR_eta i m (fun i => pselect6_spec (nfds32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) (in_arg i 5))); cbv beta.
    exact (fr_arm_72 L i m). }
  (* [comment removed for export] *)
  apply Forall_cons.
  { intros i m Hn HF HL Hb. cbn [sa_no] in Hn. cbn [sa_spec].
    apply (FR_eta i m (fun i => ppoll_spec (in_arg i 0) (unfds32 (in_arg i 1)) (in_arg i 2) (in_arg i 3) (in_arg i 4))); cbv beta.
    exact (fr_arm_73 L i m). }
  (* [comment removed for export] *)
  apply Forall_cons.
  { intros i m Hn HF HL Hb. cbn [sa_no] in Hn. cbn [sa_spec].
    apply (FR_eta i m (fun i => readlinkat_spec (fd32 (in_arg i 0)))); cbv beta.
    exact (fr_arm_78 L i m). }
  (* [comment removed for export] *)
  apply Forall_cons.
  { intros i m Hn HF HL Hb. cbn [sa_no] in Hn. cbn [sa_spec].
    apply (FR_eta i m (fun i => newfstatat_spec (fd32 (in_arg i 0)) (in_arg i 1) (flag32 (in_arg i 3)))); cbv beta.
    exact (fr_arm_79 L i m). }
  (* [comment removed for export] *)
  apply Forall_cons.
  { intros i m Hn HF HL Hb. cbn [sa_no] in Hn. cbn [sa_spec].
    apply (FR_eta i m (fun i => fstat_spec (fd32 (in_arg i 0)) (in_arg i 1))); cbv beta.
    exact (fr_arm_80 L i m). }
  (* [comment removed for export] *)
  apply Forall_cons.
  { intros i m Hn HF HL Hb. cbn [sa_no] in Hn. cbn [sa_spec].
    apply (FR_eta i m (fun i => fsync_spec (fd32 (in_arg i 0)))); cbv beta.
    exact (fr_arm_82 L i m). }
  (* [comment removed for export] *)
  apply Forall_cons.
  { intros i m Hn HF HL Hb. cbn [sa_no] in Hn. cbn [sa_spec].
    apply (FR_eta i m (fun i => fsync_spec (fd32 (in_arg i 0)))); cbv beta.
    exact (fr_arm_83 L i m). }
  (* [comment removed for export] *)
  apply Forall_cons.
  { intros i m Hn HF HL Hb. cbn [sa_no] in Hn. cbn [sa_spec].
    apply (FR_eta i m (fun i => timerfd_create_spec (clockid32 (in_arg i 0)) (flag32 (in_arg i 1)))); cbv beta.
    exact (fr_arm_85 L i m). }
  (* [comment removed for export] *)
  apply Forall_cons.
  { intros i m Hn HF HL Hb. cbn [sa_no] in Hn. cbn [sa_spec].
    apply (FR_eta i m (fun i => exit_spec (in_arg i 0))); cbv beta.
    exact (fr_arm_93 L i m). }
  (* [comment removed for export] *)
  apply Forall_cons.
  { intros i m Hn HF HL Hb. cbn [sa_no] in Hn. cbn [sa_spec].
    apply (FR_eta i m (fun i => exit_spec (in_arg i 0))); cbv beta.
    exact (fr_arm_94 L i m). }
  (* [comment removed for export] *)
  apply Forall_cons.
  { intros i m Hn HF HL Hb. cbn [sa_no] in Hn. cbn [sa_spec].
    apply (FR_eta i m (fun i => set_tid_address_spec)); cbv beta.
    exact (fr_arm_96 L i m). }
  (* [comment removed for export] *)
  apply Forall_cons.
  { intros i m Hn HF HL Hb. cbn [sa_no] in Hn. cbn [sa_spec].
    apply (FR_eta i m (fun i => futex_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3))); cbv beta.
    exact (fr_arm_98 L i m). }
  (* [comment removed for export] *)
  apply Forall_cons.
  { intros i m Hn HF HL Hb. cbn [sa_no] in Hn. cbn [sa_spec].
    apply (FR_eta i m (fun i => nanosleep_spec (in_arg i 0) (in_arg i 1))); cbv beta.
    exact (fr_arm_101 L i m). }
  (* [comment removed for export] *)
  apply Forall_cons.
  { intros i m Hn HF HL Hb. cbn [sa_no] in Hn. cbn [sa_spec].
    apply (FR_eta i m (fun i => clock_gettime_spec (clockid32 (in_arg i 0)) (in_arg i 1))); cbv beta.
    exact (fr_arm_113 L i m). }
  (* [comment removed for export] *)
  apply Forall_cons.
  { intros i m Hn HF HL Hb. cbn [sa_no] in Hn. cbn [sa_spec].
    apply (FR_eta i m (fun i => sched_setscheduler_spec (in_arg i 0) (in_arg i 1) (in_arg i 2))); cbv beta.
    exact (fr_arm_119 L i m). }
  (* [comment removed for export] *)
  apply Forall_cons.
  { intros i m Hn HF HL Hb. cbn [sa_no] in Hn. cbn [sa_spec].
    apply (FR_eta i m (fun i => sched_getaffinity_spec (in_arg i 1))); cbv beta.
    exact (fr_arm_123 L i m). }
  (* [comment removed for export] *)
  apply Forall_cons.
  { intros i m Hn HF HL Hb. cbn [sa_no] in Hn. cbn [sa_spec].
    apply (FR_eta i m (fun i => sched_yield_spec)); cbv beta.
    exact (fr_arm_124 L i m). }
  (* [comment removed for export] *)
  apply Forall_cons.
  { intros i m Hn HF HL Hb. cbn [sa_no] in Hn. cbn [sa_spec].
    apply (FR_eta i m (fun i => tkill_spec (pid32 (in_arg i 0)) (sig32 (in_arg i 1)))); cbv beta.
    exact (fr_arm_130 L i m). }
  (* [comment removed for export] *)
  apply Forall_cons.
  { intros i m Hn HF HL Hb. cbn [sa_no] in Hn. cbn [sa_spec].
    apply (FR_eta i m (fun i => tgkill_spec (pid32 (in_arg i 0)) (pid32 (in_arg i 1)) (sig32 (in_arg i 2)))); cbv beta.
    exact (fr_arm_131 L i m). }
  (* [comment removed for export] *)
  apply Forall_cons.
  { intros i m Hn HF HL Hb. cbn [sa_no] in Hn. cbn [sa_spec].
    apply (FR_eta i m (fun i => sigaltstack_spec (in_arg i 0) (in_arg i 1))); cbv beta.
    exact (fr_arm_132 L i m). }
  (* [comment removed for export] *)
  apply Forall_cons.
  { intros i m Hn HF HL Hb. cbn [sa_no] in Hn. cbn [sa_spec].
    apply (FR_eta i m (fun i => rt_sigaction_spec (sig32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3))); cbv beta.
    exact (fr_arm_134 L i m). }
  (* [comment removed for export] *)
  apply Forall_cons.
  { intros i m Hn HF HL Hb. cbn [sa_no] in Hn. cbn [sa_spec].
    apply (FR_eta i m (fun i => rt_sigprocmask_spec (how32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3))); cbv beta.
    apply fr_rt_sigprocmask. }
  (* [comment removed for export] *)
  apply Forall_cons.
  { intros i m Hn HF HL Hb. cbn [sa_no] in Hn. cbn [sa_spec].
    apply (FR_eta i m (fun i => setid_spec cred_gids set_cred_gids false (uid32 (in_arg i 0)))); cbv beta.
    exact (fr_arm_144 L i m). }
  (* [comment removed for export] *)
  apply Forall_cons.
  { intros i m Hn HF HL Hb. cbn [sa_no] in Hn. cbn [sa_spec].
    apply (FR_eta i m (fun i => setid_spec cred_uids set_cred_uids true (uid32 (in_arg i 0)))); cbv beta.
    exact (fr_arm_146 L i m). }
  (* [comment removed for export] *)
  apply Forall_cons.
  { intros i m Hn HF HL Hb. cbn [sa_no] in Hn. cbn [sa_spec].
    apply (FR_eta i m (fun i => setresid_spec cred_uids set_cred_uids true (uid32 (in_arg i 0)) (uid32 (in_arg i 1)) (uid32 (in_arg i 2)))); cbv beta.
    exact (fr_arm_147 L i m). }
  (* [comment removed for export] *)
  apply Forall_cons.
  { intros i m Hn HF HL Hb. cbn [sa_no] in Hn. cbn [sa_spec].
    apply (FR_eta i m (fun i => setresid_spec cred_gids set_cred_gids false (uid32 (in_arg i 0)) (uid32 (in_arg i 1)) (uid32 (in_arg i 2)))); cbv beta.
    exact (fr_arm_149 L i m). }
  (* [comment removed for export] *)
  apply Forall_cons.
  { intros i m Hn HF HL Hb. cbn [sa_no] in Hn. cbn [sa_spec].
    apply (FR_eta i m (fun i => setsid_spec)); cbv beta.
    exact (fr_arm_157 L i m). }
  (* [comment removed for export] *)
  apply Forall_cons.
  { intros i m Hn HF HL Hb. cbn [sa_no] in Hn. cbn [sa_spec].
    apply (FR_eta i m (fun i => getgroups_spec (in_arg i 0))); cbv beta.
    exact (fr_arm_158 L i m). }
  (* [comment removed for export] *)
  apply Forall_cons.
  { intros i m Hn HF HL Hb. cbn [sa_no] in Hn. cbn [sa_spec].
    apply (FR_eta i m (fun i => setgroups_spec)); cbv beta.
    exact (fr_arm_159 L i m). }
  (* [comment removed for export] *)
  apply Forall_cons.
  { intros i m Hn HF HL Hb. cbn [sa_no] in Hn. cbn [sa_spec].
    apply (FR_eta i m (fun i => uname_spec (in_arg i 0))); cbv beta.
    exact (fr_arm_160 L i m). }
  (* [comment removed for export] *)
  apply Forall_cons.
  { intros i m Hn HF HL Hb. cbn [sa_no] in Hn. cbn [sa_spec].
    apply (FR_eta i m (fun i => prctl_spec (int32 (in_arg i 0)) (in_arg i 1))); cbv beta.
    exact (fr_arm_167 L i m). }
  (* [comment removed for export] *)
  apply Forall_cons.
  { intros i m Hn HF HL Hb. cbn [sa_no] in Hn. cbn [sa_spec].
    apply (FR_eta i m (fun i => gettimeofday_spec (in_arg i 0) (in_arg i 1))); cbv beta.
    exact (fr_arm_169 L i m). }
  (* [comment removed for export] *)
  apply Forall_cons.
  { intros i m Hn HF HL Hb. cbn [sa_no] in Hn. cbn [sa_spec].
    apply (FR_eta i m (fun i => getpid_spec)); cbv beta.
    exact (fr_arm_172 L i m). }
  (* [comment removed for export] *)
  apply Forall_cons.
  { intros i m Hn HF HL Hb. cbn [sa_no] in Hn. cbn [sa_spec].
    apply (FR_eta i m (fun i => getid_spec cr_uid)); cbv beta.
    exact (fr_arm_174 L i m). }
  (* [comment removed for export] *)
  apply Forall_cons.
  { intros i m Hn HF HL Hb. cbn [sa_no] in Hn. cbn [sa_spec].
    apply (FR_eta i m (fun i => getid_spec cr_euid)); cbv beta.
    exact (fr_arm_175 L i m). }
  (* [comment removed for export] *)
  apply Forall_cons.
  { intros i m Hn HF HL Hb. cbn [sa_no] in Hn. cbn [sa_spec].
    apply (FR_eta i m (fun i => getid_spec cr_gid)); cbv beta.
    exact (fr_arm_176 L i m). }
  (* [comment removed for export] *)
  apply Forall_cons.
  { intros i m Hn HF HL Hb. cbn [sa_no] in Hn. cbn [sa_spec].
    apply (FR_eta i m (fun i => getid_spec cr_egid)); cbv beta.
    exact (fr_arm_177 L i m). }
  (* [comment removed for export] *)
  apply Forall_cons.
  { intros i m Hn HF HL Hb. cbn [sa_no] in Hn. cbn [sa_spec].
    apply (FR_eta i m (fun i => gettid_spec)); cbv beta.
    exact (fr_arm_178 L i m). }
  (* [comment removed for export] *)
  apply Forall_cons.
  { intros i m Hn HF HL Hb. cbn [sa_no] in Hn. cbn [sa_spec].
    apply (FR_eta i m (fun i => socket_spec (in_arg i 0) (in_arg i 1) (in_arg i 2))); cbv beta.
    exact (fr_arm_198 L i m). }
  (* [comment removed for export] *)
  apply Forall_cons.
  { intros i m Hn HF HL Hb. cbn [sa_no] in Hn. cbn [sa_spec].
    apply (FR_eta i m (fun i => socketpair_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3))); cbv beta.
    exact (fr_arm_199 L i m). }
  (* [comment removed for export] *)
  apply Forall_cons.
  { intros i m Hn HF HL Hb. cbn [sa_no] in Hn. cbn [sa_spec].
    apply (FR_eta i m (fun i => bind_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2))); cbv beta.
    exact (fr_arm_200 L i m). }
  (* [comment removed for export] *)
  apply Forall_cons.
  { intros i m Hn HF HL Hb. cbn [sa_no] in Hn. cbn [sa_spec].
    apply (FR_eta i m (fun i => listen_spec (fd32 (in_arg i 0)) (in_arg i 1))); cbv beta.
    exact (fr_arm_201 L i m). }
  (* [comment removed for export] *)
  apply Forall_cons.
  { intros i m Hn HF HL Hb. cbn [sa_no] in Hn. cbn [sa_spec].
    apply (FR_eta i m (fun i => accept4_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (Z_to_bv 64 0))); cbv beta.
    exact (fr_arm_202 L i m). }
  (* [comment removed for export] *)
  apply Forall_cons.
  { intros i m Hn HF HL Hb. cbn [sa_no] in Hn. cbn [sa_spec].
    apply (FR_eta i m (fun i => connect_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2))); cbv beta.
    exact (fr_arm_203 L i m). }
  (* [comment removed for export] *)
  apply Forall_cons.
  { intros i m Hn HF HL Hb. cbn [sa_no] in Hn. cbn [sa_spec].
    apply (FR_eta i m (fun i => getsockname_spec (fd32 (in_arg i 0)))); cbv beta.
    exact (fr_arm_204 L i m). }
  (* [comment removed for export] *)
  apply Forall_cons.
  { intros i m Hn HF HL Hb. cbn [sa_no] in Hn. cbn [sa_spec].
    apply (FR_eta i m (fun i => getpeername_spec (fd32 (in_arg i 0)))); cbv beta.
    exact (fr_arm_205 L i m). }
  (* [comment removed for export] *)
  apply Forall_cons.
  { intros i m Hn HF HL Hb. cbn [sa_no] in Hn. cbn [sa_spec].
    apply (FR_eta i m (fun i => sendto_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) (in_arg i 5))); cbv beta.
    exact (fr_arm_206 L i m). }
  (* [comment removed for export] *)
  apply Forall_cons.
  { intros i m Hn HF HL Hb. cbn [sa_no] in Hn. cbn [sa_spec].
    apply (FR_eta i m (fun i => recvfrom_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2))); cbv beta.
    exact (fr_arm_207 L i m). }
  (* [comment removed for export] *)
  apply Forall_cons.
  { intros i m Hn HF HL Hb. cbn [sa_no] in Hn. cbn [sa_spec].
    apply (FR_eta i m (fun i => setsockopt_spec (fd32 (in_arg i 0)) (int32 (in_arg i 1)) (int32 (in_arg i 4)))); cbv beta.
    exact (fr_arm_208 L i m). }
  (* [comment removed for export] *)
  apply Forall_cons.
  { intros i m Hn HF HL Hb. cbn [sa_no] in Hn. cbn [sa_spec].
    apply (FR_eta i m (fun i => getsockopt_spec (fd32 (in_arg i 0)) (int32 (in_arg i 1)) (in_arg i 4))); cbv beta.
    exact (fr_arm_209 L i m). }
  (* [comment removed for export] *)
  apply Forall_cons.
  { intros i m Hn HF HL Hb. cbn [sa_no] in Hn. cbn [sa_spec].
    apply (FR_eta i m (fun i => shutdown_spec (fd32 (in_arg i 0)) (int32 (in_arg i 1)))); cbv beta.
    exact (fr_arm_210 L i m). }
  (* [comment removed for export] *)
  apply Forall_cons.
  { intros i m Hn HF HL Hb. cbn [sa_no] in Hn. cbn [sa_spec].
    apply (FR_eta i m (fun i => sendmsg_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2))); cbv beta.
    exact (fr_arm_211 L i m). }
  (* [comment removed for export] *)
  apply Forall_cons.
  { intros i m Hn HF HL Hb. cbn [sa_no] in Hn. cbn [sa_spec].
    apply (FR_eta i m (fun i => recvmsg_spec (fd32 (in_arg i 0)) (in_arg i 2))); cbv beta.
    exact (fr_arm_212 L i m). }
  (* [comment removed for export] *)
  apply Forall_cons.
  { intros i m Hn HF HL Hb. cbn [sa_no] in Hn. cbn [sa_spec].
    apply (FR_eta i m (fun i => brk_spec (in_arg i 0))); cbv beta.
    apply fr_brk; [exact HL | exact (mark_brk i (sl L m) Hn Hb)]. }
  (* [comment removed for export] *)
  apply Forall_cons.
  { intros i m Hn HF HL Hb. cbn [sa_no] in Hn. cbn [sa_spec].
    apply (FR_eta i m (fun i => munmap_spec (in_arg i 0) (in_arg i 1))); cbv beta.
    apply fr_munmap. }
  (* [comment removed for export] *)
  apply Forall_cons.
  { intros i m Hn HF HL Hb. cbn [sa_no] in Hn. cbn [sa_spec].
    apply (FR_eta i m (fun i => mremap_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3))); cbv beta.
    apply fr_mremap; [exact HF | exact HL | exact (mark_mremap i (sl L m) Hn Hb)]. }
  (* [comment removed for export] *)
  apply Forall_cons.
  { intros i m Hn HF HL Hb. cbn [sa_no] in Hn. cbn [sa_spec].
    apply (FR_eta i m (fun i => clone_spec (in_arg i 0))); cbv beta.
    exact (fr_arm_220 L i m). }
  (* [comment removed for export] *)
  apply Forall_cons.
  { intros i m Hn HF HL Hb. cbn [sa_no] in Hn. cbn [sa_spec].
    apply (FR_eta i m (fun i => mmap_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) (in_arg i 5))); cbv beta.
    apply fr_mmap; [exact HL | exact (mark_mmap i (sl L m) Hn Hb)]. }
  (* [comment removed for export] *)
  apply Forall_cons.
  { intros i m Hn HF HL Hb. cbn [sa_no] in Hn. cbn [sa_spec].
    apply (FR_eta i m (fun i => mprotect_spec (in_arg i 0) (in_arg i 1) (in_arg i 2))); cbv beta.
    apply fr_mprotect; [exact HL | exact (mark_mprotect i (sl L m) Hn Hb)]. }
  (* [comment removed for export] *)
  apply Forall_cons.
  { intros i m Hn HF HL Hb. cbn [sa_no] in Hn. cbn [sa_spec].
    apply (FR_eta i m (fun i => madvise_spec (in_arg i 0) (in_arg i 1) (int32 (in_arg i 2)))); cbv beta.
    apply fr_madvise. }
  (* [comment removed for export] *)
  apply Forall_cons.
  { intros i m Hn HF HL Hb. cbn [sa_no] in Hn. cbn [sa_spec].
    apply (FR_eta i m (fun i => accept4_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3))); cbv beta.
    exact (fr_arm_242 L i m). }
  (* [comment removed for export] *)
  apply Forall_cons.
  { intros i m Hn HF HL Hb. cbn [sa_no] in Hn. cbn [sa_spec].
    apply (FR_eta i m (fun i => wait4_spec (pid32 (in_arg i 0)) (in_arg i 1) (waitopts32 (in_arg i 2)) (in_arg i 3))); cbv beta.
    exact (fr_arm_260 L i m). }
  (* [comment removed for export] *)
  apply Forall_cons.
  { intros i m Hn HF HL Hb. cbn [sa_no] in Hn. cbn [sa_spec].
    apply (FR_eta i m (fun i => prlimit64_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3))); cbv beta.
    exact (fr_arm_261 L i m). }
  (* [comment removed for export] *)
  apply Forall_cons.
  { intros i m Hn HF HL Hb. cbn [sa_no] in Hn. cbn [sa_spec].
    apply (FR_eta i m (fun i => getrandom_spec (in_arg i 0) (in_arg i 1) (in_arg i 2))); cbv beta.
    exact (fr_arm_278 L i m). }
  (* [comment removed for export] *)
  apply Forall_cons.
  { intros i m Hn HF HL Hb. cbn [sa_no] in Hn. cbn [sa_spec].
    apply (FR_eta i m (fun i => clone3_spec (in_arg i 0) (in_arg i 1))); cbv beta.
    exact (fr_arm_435 L i m). }
  (* [comment removed for export] *)
  apply Forall_cons.
  { intros i m Hn HF HL Hb. cbn [sa_no] in Hn. cbn [sa_spec].
    apply (FR_eta i m (fun i => faccessat2_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3))); cbv beta.
    exact (fr_arm_439 L i m). }
  apply Forall_nil.
Qed.

Theorem syscall_lt_all : syscall_lt linv L.
Proof.
  intros i m HF HL Hb. exact (dispatch_lt spec_table spec_table_ok i m HF HL Hb).
Qed.

End Dispatch.
