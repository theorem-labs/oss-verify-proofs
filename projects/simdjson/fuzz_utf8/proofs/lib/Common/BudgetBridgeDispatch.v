(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem Require Import Sys.SyscallTable.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import BudgetBridgeCore BudgetBridgeTac BudgetBridgeMm BudgetBridgeArms.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib Require TCodec.
Ltac2 tcn__Common_BudgetBridgeDispatch () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.Monad."; "LinuxProcessSemantics.LinuxProcessSem.Run."; "LinuxProcessSemantics.LinuxProcessSem.Specs."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.LinuxProcessSem.Sys.Dispatch."; "LinuxProcessSemantics.LinuxProcessSem.Sys.SyscallTable."; "OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.BudgetBridgeCore."; "OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.BudgetBridgeDispatch.Dispatch."; "OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.BudgetBridgeMm."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1Some"; "1bool"; "1false"; "1list"; "1option"; "2and"; "2eq"; "3Forall"; "4Z"; "0L"; "5Sys"; "6alloc_budget_refused_b"; "7syscall_spec"; "8Model"; "8SyscallEffect"; "8SyscallInput"]; ["8in_sysno"; "8m_vmmaps"; "8vm_limit"; "8vm_maps"; "9SpecArm"; "9dispatch"; "9lookup_arm"; "9sa_no"; "9sa_spec"; ":spec_table"; ";Sim1"; "<arm_good"; "=maps_bounded"; ">In"; "?le"; "0a"]; ["0i"; "0j"; "0m"; "0n"; "0s"; "@bv_unsigned"; "0t"; "0x"]]).
Lemma lookup_arm_in' : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeDispatch "K'3'D%211'8'6'4%115&Fr3r2%3221(0r1%22<1%:3841'5&Mr4%23A91&G%11;%A3B1=%7241p091pR0G1pR8F1pR>H1").
Proof.
induction t as [| x t IH]; intros n a H; [discriminate H |].
cbn in H. destruct (Z.eqb (sa_no x) n) eqn:E.
- injection H as <-. split; [left; reflexivity | apply Z.eqb_eq; exact E].
- destruct (IH n a H) as [Hin Hno]. split; [right; exact Hin | exact Hno].
Qed.
Lemma sim1_dispatch : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeDispatch "Q9'8'3'D%211'?'='6'4%116&Fr4&Q5yR0&@r3%211%5241%8271(0r1%22B1%?3=41&Jr6'>qR@16&Hr2%211%78655411C?p091pR0M1r5&E%11H%=83;;:11E8p051pR6Q01pR2Q21pR>Q41pDQ81").
Proof.
intros L t i m H. unfold dispatch, Sim1.
destruct (lookup_arm t (bv_unsigned (in_sysno i))) as [a |] eqn:E.
- exact (H a eq_refl).
- exact (sim_unmodeled L (fun x : SyscallEffect => x) i m).
Qed.
Lemma sim1_reader : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeDispatch "H'8'?&:'>%211p041'=&Jr4r1qR@71r3r2%211%786;;41125r5%1277qR4@1%;83??81176p051pR6>1pR2D1pR:A1pDG1").
Proof. intros L s i m H. exact H. Qed.
Section Dispatch.
Hypothesis MCLE : move_charge_le_stmt.
Variable L : Z.
Definition arm_good (a : SpecArm) : Prop :=
forall i m,
sa_no a = bv_unsigned (in_sysno i) ->
alloc_budget_refused_b i m = false ->
vm_limit (m_vmmaps m) <= L ->
maps_bounded (vm_maps (m_vmmaps m)) ->
Sim1 L (fun x => x) (sa_spec a) (sa_spec a) i m.
Ltac good_ungated S H :=
let i := fresh "i" in let m := fresh "m" in
intros i m _ _ _ _; cbn [sa_spec];
apply (sim1_reader L S); exact (sim1_of_sim _ _ _ _ (H L i) i m).
Lemma spec_table_good : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeDispatch "5'7'D&K&I%43321").
Proof.
unfold spec_table.
apply Forall_cons; [ good_ungated (fun i : SyscallInput => getcwd_spec (in_arg i 1)) arm_nat_getcwd |].
apply Forall_cons; [ good_ungated (fun i : SyscallInput => eventfd2_spec (flag32 (in_arg i 1))) arm_nat_eventfd2 |].
apply Forall_cons; [ good_ungated (fun i : SyscallInput => epoll_create1_spec (flag32 (in_arg i 0))) arm_nat_epoll_create1 |].
apply Forall_cons; [ good_ungated (fun i : SyscallInput => epoll_ctl_spec (fd32 (in_arg i 0)) (int32 (in_arg i 1)) (fd32 (in_arg i 2)) (in_arg i 3)) arm_nat_epoll_ctl |].
apply Forall_cons; [ good_ungated (fun i : SyscallInput => epoll_pwait_spec (fd32 (in_arg i 0)) (in_arg i 1) (int32 (in_arg i 2)) (in_arg i 4) (in_arg i 5)) arm_nat_epoll_pwait |].
apply Forall_cons; [ good_ungated (fun i : SyscallInput => dup_spec (fd32 (in_arg i 0))) arm_nat_dup |].
apply Forall_cons; [ good_ungated (fun i : SyscallInput => dup3_spec (fd32 (in_arg i 0)) (fd32 (in_arg i 1)) (in_arg i 2)) arm_nat_dup3 |].
apply Forall_cons; [ good_ungated (fun i : SyscallInput => fcntl_spec (fd32 (in_arg i 0)) (cmd32 (in_arg i 1)) (in_arg i 2)) arm_nat_fcntl |].
apply Forall_cons; [ good_ungated (fun i : SyscallInput => ioctl_spec (fd32 (in_arg i 0)) (cmd32 (in_arg i 1))) arm_nat_ioctl |].
apply Forall_cons; [ good_ungated (fun i : SyscallInput => flock_spec (fd32 (in_arg i 0)) (cmd32 (in_arg i 1))) arm_nat_flock |].
apply Forall_cons; [ good_ungated (fun i : SyscallInput => unlinkat_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2)) arm_nat_unlinkat |].
apply Forall_cons; [ good_ungated (fun i : SyscallInput => ftruncate_spec (fd32 (in_arg i 0)) (in_arg i 1)) arm_nat_ftruncate |].
apply Forall_cons; [ good_ungated (fun i : SyscallInput => faccessat_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2)) arm_nat_faccessat |].
apply Forall_cons; [ good_ungated (fun i : SyscallInput => openat_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2)) arm_nat_openat |].
apply Forall_cons; [ good_ungated (fun i : SyscallInput => close_spec (fd32 (in_arg i 0))) arm_nat_close |].
apply Forall_cons; [ good_ungated (fun i : SyscallInput => pipe2_spec (in_arg i 0) (pipe_flags32 (in_arg i 1))) arm_nat_pipe2 |].
apply Forall_cons; [ good_ungated (fun i : SyscallInput => getdents64_spec (fd32 (in_arg i 0)) (in_arg i 2)) arm_nat_getdents64 |].
apply Forall_cons; [ good_ungated (fun i : SyscallInput => lseek_spec (fd32 (in_arg i 0)) (in_arg i 1) (whence32 (in_arg i 2))) arm_nat_lseek |].
apply Forall_cons; [ good_ungated (fun i : SyscallInput => read_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2)) arm_nat_read |].
apply Forall_cons; [ good_ungated (fun i : SyscallInput => write_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2)) arm_nat_write |].
apply Forall_cons; [ good_ungated (fun i : SyscallInput => readv_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2)) arm_nat_readv |].
apply Forall_cons; [ good_ungated (fun i : SyscallInput => writev_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2)) arm_nat_writev |].
apply Forall_cons; [ good_ungated (fun i : SyscallInput => pread64_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3)) arm_nat_pread64 |].
apply Forall_cons; [ good_ungated (fun i : SyscallInput => pwrite64_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3)) arm_nat_pwrite64 |].
apply Forall_cons; [ good_ungated (fun i : SyscallInput => pselect6_spec (nfds32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) (in_arg i 5)) arm_nat_pselect6 |].
apply Forall_cons; [ good_ungated (fun i : SyscallInput => ppoll_spec (in_arg i 0) (unfds32 (in_arg i 1)) (in_arg i 2) (in_arg i 3) (in_arg i 4)) arm_nat_ppoll |].
apply Forall_cons; [ good_ungated (fun i : SyscallInput => readlinkat_spec (fd32 (in_arg i 0))) arm_nat_readlinkat |].
apply Forall_cons; [ good_ungated (fun i : SyscallInput => newfstatat_spec (fd32 (in_arg i 0)) (in_arg i 1) (flag32 (in_arg i 3))) arm_nat_newfstatat |].
apply Forall_cons; [ good_ungated (fun i : SyscallInput => fstat_spec (fd32 (in_arg i 0)) (in_arg i 1)) arm_nat_fstat |].
apply Forall_cons; [ good_ungated (fun i : SyscallInput => fsync_spec (fd32 (in_arg i 0))) arm_nat_fsync |].
apply Forall_cons; [ good_ungated (fun i : SyscallInput => fsync_spec (fd32 (in_arg i 0))) arm_nat_fdatasync |].
apply Forall_cons; [ good_ungated (fun i : SyscallInput => timerfd_create_spec (clockid32 (in_arg i 0)) (flag32 (in_arg i 1))) arm_nat_timerfd_create |].
apply Forall_cons; [ good_ungated (fun i : SyscallInput => exit_spec (in_arg i 0)) arm_nat_exit |].
apply Forall_cons; [ good_ungated (fun i : SyscallInput => exit_spec (in_arg i 0)) arm_nat_exit_group |].
apply Forall_cons; [ good_ungated (fun i : SyscallInput => set_tid_address_spec) arm_nat_set_tid_address |].
apply Forall_cons; [ good_ungated (fun i : SyscallInput => futex_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3)) arm_nat_futex |].
apply Forall_cons; [ good_ungated (fun i : SyscallInput => nanosleep_spec (in_arg i 0) (in_arg i 1)) arm_nat_nanosleep |].
apply Forall_cons; [ good_ungated (fun i : SyscallInput => clock_gettime_spec (clockid32 (in_arg i 0)) (in_arg i 1)) arm_nat_clock_gettime |].
apply Forall_cons; [ good_ungated (fun i : SyscallInput => sched_setscheduler_spec (in_arg i 0) (in_arg i 1) (in_arg i 2)) arm_nat_sched_setscheduler |].
apply Forall_cons; [ good_ungated (fun i : SyscallInput => sched_getaffinity_spec (in_arg i 1)) arm_nat_sched_getaffinity |].
apply Forall_cons; [ good_ungated (fun i : SyscallInput => sched_yield_spec) arm_nat_sched_yield |].
apply Forall_cons; [ good_ungated (fun i : SyscallInput => tkill_spec (pid32 (in_arg i 0)) (sig32 (in_arg i 1))) arm_nat_tkill |].
apply Forall_cons; [ good_ungated (fun i : SyscallInput => tgkill_spec (pid32 (in_arg i 0)) (pid32 (in_arg i 1)) (sig32 (in_arg i 2))) arm_nat_tgkill |].
apply Forall_cons; [ good_ungated (fun i : SyscallInput => sigaltstack_spec (in_arg i 0) (in_arg i 1)) arm_nat_sigaltstack |].
apply Forall_cons; [ good_ungated (fun i : SyscallInput => rt_sigaction_spec (sig32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3)) arm_nat_rt_sigaction |].
apply Forall_cons; [ good_ungated (fun i : SyscallInput => rt_sigprocmask_spec (how32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3)) arm_nat_rt_sigprocmask |].
apply Forall_cons; [ good_ungated (fun i : SyscallInput => setid_spec cred_gids set_cred_gids false (uid32 (in_arg i 0))) arm_nat_setgid |].
apply Forall_cons; [ good_ungated (fun i : SyscallInput => setid_spec cred_uids set_cred_uids true (uid32 (in_arg i 0))) arm_nat_setuid |].
apply Forall_cons; [ good_ungated (fun i : SyscallInput => setresid_spec cred_uids set_cred_uids true (uid32 (in_arg i 0)) (uid32 (in_arg i 1)) (uid32 (in_arg i 2))) arm_nat_setresuid |].
apply Forall_cons; [ good_ungated (fun i : SyscallInput => setresid_spec cred_gids set_cred_gids false (uid32 (in_arg i 0)) (uid32 (in_arg i 1)) (uid32 (in_arg i 2))) arm_nat_setresgid |].
apply Forall_cons; [ good_ungated (fun i : SyscallInput => setsid_spec) arm_nat_setsid |].
apply Forall_cons; [ good_ungated (fun i : SyscallInput => getgroups_spec (in_arg i 0)) arm_nat_getgroups |].
apply Forall_cons; [ good_ungated (fun i : SyscallInput => setgroups_spec) arm_nat_setgroups |].
apply Forall_cons; [ good_ungated (fun i : SyscallInput => uname_spec (in_arg i 0)) arm_nat_uname |].
apply Forall_cons; [ good_ungated (fun i : SyscallInput => prctl_spec (int32 (in_arg i 0)) (in_arg i 1)) arm_nat_prctl |].
apply Forall_cons; [ good_ungated (fun i : SyscallInput => gettimeofday_spec (in_arg i 0) (in_arg i 1)) arm_nat_gettimeofday |].
apply Forall_cons; [ good_ungated (fun i : SyscallInput => getpid_spec) arm_nat_getpid |].
apply Forall_cons; [ good_ungated (fun i : SyscallInput => getid_spec cr_uid) arm_nat_getuid |].
apply Forall_cons; [ good_ungated (fun i : SyscallInput => getid_spec cr_euid) arm_nat_geteuid |].
apply Forall_cons; [ good_ungated (fun i : SyscallInput => getid_spec cr_gid) arm_nat_getgid |].
apply Forall_cons; [ good_ungated (fun i : SyscallInput => getid_spec cr_egid) arm_nat_getegid |].
apply Forall_cons; [ good_ungated (fun i : SyscallInput => gettid_spec) arm_nat_gettid |].
apply Forall_cons; [ good_ungated (fun i : SyscallInput => socket_spec (in_arg i 0) (in_arg i 1) (in_arg i 2)) arm_nat_socket |].
apply Forall_cons; [ good_ungated (fun i : SyscallInput => socketpair_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3)) arm_nat_socketpair |].
apply Forall_cons; [ good_ungated (fun i : SyscallInput => bind_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2)) arm_nat_bind |].
apply Forall_cons; [ good_ungated (fun i : SyscallInput => listen_spec (fd32 (in_arg i 0)) (in_arg i 1)) arm_nat_listen |].
apply Forall_cons; [ good_ungated (fun i : SyscallInput => accept4_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (Z_to_bv 64 0)) arm_nat_accept |].
apply Forall_cons; [ good_ungated (fun i : SyscallInput => connect_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2)) arm_nat_connect |].
apply Forall_cons; [ good_ungated (fun i : SyscallInput => getsockname_spec (fd32 (in_arg i 0))) arm_nat_getsockname |].
apply Forall_cons; [ good_ungated (fun i : SyscallInput => getpeername_spec (fd32 (in_arg i 0))) arm_nat_getpeername |].
apply Forall_cons; [ good_ungated (fun i : SyscallInput => sendto_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) (in_arg i 5)) arm_nat_sendto |].
apply Forall_cons; [ good_ungated (fun i : SyscallInput => recvfrom_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2)) arm_nat_recvfrom |].
apply Forall_cons; [ good_ungated (fun i : SyscallInput => setsockopt_spec (fd32 (in_arg i 0)) (int32 (in_arg i 1)) (int32 (in_arg i 4))) arm_nat_setsockopt |].
apply Forall_cons; [ good_ungated (fun i : SyscallInput => getsockopt_spec (fd32 (in_arg i 0)) (int32 (in_arg i 1)) (in_arg i 4)) arm_nat_getsockopt |].
apply Forall_cons; [ good_ungated (fun i : SyscallInput => shutdown_spec (fd32 (in_arg i 0)) (int32 (in_arg i 1))) arm_nat_shutdown |].
apply Forall_cons; [ good_ungated (fun i : SyscallInput => sendmsg_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2)) arm_nat_sendmsg |].
apply Forall_cons; [ good_ungated (fun i : SyscallInput => recvmsg_spec (fd32 (in_arg i 0)) (in_arg i 2)) arm_nat_recvmsg |].
apply Forall_cons.
{ intros i m Hno Hmk Hle Hb. cbn [sa_no sa_spec] in *.
rewrite (proj1 (alloc_mark_sysnos_dispatched i m) (eq_sym Hno)) in Hmk.
apply (sim1_reader L (fun i => brk_spec (in_arg i 0))).
exact (brk_nat L i m Hmk Hle). }
apply Forall_cons; [ good_ungated (fun i : SyscallInput => munmap_spec (in_arg i 0) (in_arg i 1)) arm_nat_munmap |].
apply Forall_cons.
{ intros i m Hno Hmk Hle Hb. cbn [sa_no sa_spec] in *.
rewrite (proj1 (proj2 (alloc_mark_sysnos_dispatched i m)) (eq_sym Hno)) in Hmk.
apply (sim1_reader L (fun i => mremap_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3))).
exact (mremap_nat MCLE L i m Hmk Hle Hb). }
apply Forall_cons; [ good_ungated (fun i : SyscallInput => clone_spec (in_arg i 0)) arm_nat_clone |].
apply Forall_cons.
{ intros i m Hno Hmk Hle Hb. cbn [sa_no sa_spec] in *.
rewrite (proj1 (proj2 (proj2 (alloc_mark_sysnos_dispatched i m))) (eq_sym Hno)) in Hmk.
apply (sim1_reader L (fun i => mmap_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) (in_arg i 5))).
exact (mmap_nat L i m Hmk Hle). }
apply Forall_cons.
{ intros i m Hno Hmk Hle Hb. cbn [sa_no sa_spec] in *.
rewrite (proj2 (proj2 (proj2 (alloc_mark_sysnos_dispatched i m))) (eq_sym Hno)) in Hmk.
apply (sim1_reader L (fun i => mprotect_spec (in_arg i 0) (in_arg i 1) (in_arg i 2))).
exact (mprotect_nat L i m Hmk Hle). }
apply Forall_cons; [ good_ungated (fun i : SyscallInput => madvise_spec (in_arg i 0) (in_arg i 1) (int32 (in_arg i 2))) arm_nat_madvise |].
apply Forall_cons; [ good_ungated (fun i : SyscallInput => accept4_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3)) arm_nat_accept4 |].
apply Forall_cons; [ good_ungated (fun i : SyscallInput => wait4_spec (pid32 (in_arg i 0)) (in_arg i 1) (waitopts32 (in_arg i 2)) (in_arg i 3)) arm_nat_wait4 |].
apply Forall_cons; [ good_ungated (fun i : SyscallInput => prlimit64_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3)) arm_nat_prlimit64 |].
apply Forall_cons; [ good_ungated (fun i : SyscallInput => getrandom_spec (in_arg i 0) (in_arg i 1) (in_arg i 2)) arm_nat_getrandom |].
apply Forall_cons; [ good_ungated (fun i : SyscallInput => clone3_spec (in_arg i 0) (in_arg i 1)) arm_nat_clone3 |].
apply Forall_cons; [ good_ungated (fun i : SyscallInput => faccessat2_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3)) arm_nat_faccessat2 |].
apply Forall_nil.
Qed.
Theorem syscall_nat : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeDispatch "Q3'?'='6'1&;r2r1%3221(2%73621&N&B&A%118%311v9%6221&L&Cr3%811%311%511&J'>qR@1C&<r5r4%68>5543321p081p0?1p0G1pR6Q01pR2Q21").
Proof.
intros i m Hmk Hle Hb. unfold syscall_spec. apply sim1_dispatch.
intros a Ha. destruct (lookup_arm_in' _ _ _ Ha) as [Hin Hno].
pose proof spec_table_good as G. rewrite Forall_forall in G.
exact (G a Hin i m Hno Hmk Hle Hb).
Qed.
End Dispatch.
