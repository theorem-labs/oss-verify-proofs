(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad Specs.
From LinuxProcessSemantics.LinuxProcessSem Require Import Sys.SyscallTable.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common Require Import BudgetBridgeCore BudgetBridgeTac BudgetBridgeMm BudgetBridgeRun BudgetBridgeInvCore.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib Require TCodec.
Ltac2 tcn__Common_BudgetBridgeInvArms () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.LinuxProcessSem.Sys.Dispatch."; "LinuxProcessSemantics.LinuxProcessSem.Sys.Drivers.Char.Random."; "LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.DPath."; "LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.EventFd."; "LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.EventPoll."; "LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Fcntl."; "LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.File."; "LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Ioctl."; "LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Locks."; "LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Namei."; "LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Open."; "LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Pipe."; "LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.ReadWrite."; "LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Readdir."; "LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Select."; "LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Stat."; "LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Sync."; "LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Timerfd."; "LinuxProcessSemantics.LinuxProcessSem.Sys.Kernel.Exit."; "LinuxProcessSemantics.LinuxProcessSem.Sys.Kernel.Fork."; "LinuxProcessSemantics.LinuxProcessSem.Sys.Kernel.Futex.Syscalls."; "LinuxProcessSemantics.LinuxProcessSem.Sys.Kernel.Groups."; "LinuxProcessSemantics.LinuxProcessSem.Sys.Kernel.Sched.Syscalls."; "LinuxProcessSemantics.LinuxProcessSem.Sys.Kernel.Signal."; "LinuxProcessSemantics.LinuxProcessSem.Sys.Kernel.Sys."; "LinuxProcessSemantics.LinuxProcessSem.Sys.Kernel.Time.Hrtimer."; "LinuxProcessSemantics.LinuxProcessSem.Sys.Kernel.Time.PosixTimers."; "LinuxProcessSemantics.LinuxProcessSem.Sys.Kernel.Time.Time."; "LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Madvise."; "LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap."; "LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mprotect."; "LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mremap."; "LinuxProcessSemantics.LinuxProcessSem.Sys.Net.Socket."; "LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall."; "LinuxProcessSemantics.LinuxProcessSem.Sys.SyscallTable."; "OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.BudgetBridgeInvArms."; "OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.BudgetBridgeInvCore."; "OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.BudgetBridgeRun."; "Stdlib.Lists.List."; "stdpp.bitvector.definitions."], [["1O"; "1Some"; "1false"; "1list"; "1option"; "1true"; "2eq"; "3Forall"; "4Z"; "5Model"; "5SyscallEffect"; "5SyscallInput"; "5cr_egid"; "5cr_euid"; "5cr_gid"; "5cr_uid"]; ["5in_arg"; "6SpecArm"; "6lookup_arm"; "7getrandom_spec"; "8getcwd_spec"; "9eventfd2_spec"; ":epoll_create1_spec"; ":epoll_ctl_spec"; ":epoll_pwait_spec"; ";fcntl_spec"; "<dup3_spec"; "<dup_spec"; "=ioctl_spec"; ">flock_spec"; "?unlinkat_spec"; "@close_spec"]; ["@faccessat2_spec"; "@faccessat_spec"; "@ftruncate_spec"; "@openat_spec"; "Apipe2_spec"; "Blseek_spec"; "Bpread64_spec"; "Bpwrite64_spec"; "Bread_spec"; "Breadv_spec"; "Bwrite_spec"; "Bwritev_spec"; "Cgetdents64_spec"; "Dppoll_spec"; "Dpselect6_spec"; "Efstat_spec"]; ["Enewfstatat_spec"; "Ereadlinkat_spec"; "Ffsync_spec"; "Gtimerfd_create_spec"; "Hexit_spec"; "Hwait4_spec"; "Iclone3_spec"; "Iclone_spec"; "Iset_tid_address_spec"; "Jfutex_spec"; "Kgetgroups_spec"; "Ksetgroups_spec"; "Lsched_getaffinity_spec"; "Lsched_setscheduler_spec"; "Lsched_yield_spec"; "Mrt_sigaction_spec"]; ["Mrt_sigprocmask_spec"; "Msig32"; "Msigaltstack_spec"; "Mtgkill_spec"; "Mtkill_spec"; "Ncred_gids"; "Ncred_uids"; "Ngetid_spec"; "Ngetpid_spec"; "Ngettid_spec"; "Nprctl_spec"; "Nprlimit64_spec"; "Nset_cred_gids"; "Nset_cred_uids"; "Nsetid_spec"; "Nsetresid_spec"]; ["Nsetsid_spec"; "Nuname_spec"; "Onanosleep_spec"; "Pclock_gettime_spec"; "Qgettimeofday_spec"; "Rmadvise_spec"; "Sbrk_spec"; "Smmap_spec"; "Smunmap_spec"; "Tmprotect_spec"; "Umremap_spec"; "Vaccept4_spec"; "Vbind_spec"; "Vconnect_spec"; "Vgetpeername_spec"; "Vgetsockname_spec"]; ["Vgetsockopt_spec"; "Vlisten_spec"; "Vrecvfrom_spec"; "Vrecvmsg_spec"; "Vsendmsg_spec"; "Vsendto_spec"; "Vsetsockopt_spec"; "Vshutdown_spec"; "Vsocket_spec"; "Vsocketpair_spec"; "Wclockid32"; "Wcmd32"; "Wfd32"; "Wflag32"; "Whow32"; "Wint32"]; ["Wnfds32"; "Wpid32"; "Wpipe_flags32"; "Wuid32"; "Wunfds32"; "Wwaitopts32"; "Wwhence32"; "Xspec_table"; "Yarm_bnd"; "ZPres1"; "[bounded_pres_stmt"; "\In"; "0a"; "0i"; "0m"; "0n"]; ["]Z_to_bv"; "0t"]]).
Lemma arm_bnd_getcwd : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeInvArms ">';'9&SI':&D&@r2u1%3221%511r1%948251pWN;1pWL=1").
Proof. intros i m. pres_auto. Qed.
Lemma arm_bnd_eventfd2 : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeInvArms "@';'9&SI':&E&S=&@r2u1%3221%511%711r1%;4:261pWN=1pWL?1").
Proof. intros i m. pres_auto. Qed.
Lemma arm_bnd_epoll_create1 : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeInvArms "@';'9&SI':&F&S=&@r2(0%3221%511%711r1%;4:261pWN=1pWL?1").
Proof. intros i m. pres_auto. Qed.
Lemma arm_bnd_epoll_ctl : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeInvArms "I';'9&SI':&G&S<&@r2(0%3221%511&S?u1%7261%311u2%:291%<11u3%=2<1%@4:631r1%D4C2?1pWNF1pWLH1").
Proof. intros i m. pres_auto. Qed.
Lemma arm_bnd_epoll_pwait : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeInvArms "J';'9&SI':&H&S<&@r2(0%3221%511u1%6251&S?u2%9281%311u4%<2;1u5%>2=1%A5;9531r1%E4D2@1pWNG1pWLI1").
Proof. intros i m. pres_auto. Qed.
Lemma arm_bnd_dup : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeInvArms "@';'9&SI':&K&S<&@r2(0%3221%511%711r1%;4:261pWN=1pWL?1").
Proof. intros i m. pres_auto. Qed.
Lemma arm_bnd_dup3 : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeInvArms "E';'9&SI':&J&S<&@r2(0%3221%511u1%6251%811u2%9281%<3631r1%@4?2;1pWNB1pWLD1").
Proof. intros i m. pres_auto. Qed.
Lemma arm_bnd_fcntl : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeInvArms "F';'9&SI':&I&S<&@r2(0%3221%511&S;u1%7261%311u2%:291%=3731r1%A4@2<1pWNC1pWLE1").
Proof. intros i m. pres_auto. Qed.
Lemma arm_bnd_ioctl : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeInvArms "D';'9&SI':&L&S<&@r2(0%3221%511&S;u1%7261%311%;251r1%?4>2:1pWNA1pWLC1").
Proof. intros i m. pres_auto. Qed.
Lemma arm_bnd_flock : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeInvArms "D';'9&SI':&M&S<&@r2(0%3221%511&S;u1%7261%311%;251r1%?4>2:1pWNA1pWLC1").
Proof. intros i m. pres_auto. Qed.
Lemma arm_bnd_unlinkat : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeInvArms "D';'9&SI':&N&S<&@r2(0%3221%511u1%6251u2%8271%;3531r1%?4>2:1pWNA1pWLC1").
Proof. intros i m. pres_auto. Qed.
Lemma arm_bnd_ftruncate : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeInvArms "B';'9&SI':&Q2&S<&@r2(0%3221%511u1%6251%9231r1%=4<281pWN?1pWLA1").
Proof. intros i m. pres_auto. Qed.
Lemma arm_bnd_faccessat : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeInvArms "D';'9&SI':&Q1&S<&@r2(0%3221%511u1%6251u2%8271%;3531r1%?4>2:1pWNA1pWLC1").
Proof. intros i m. pres_auto. Qed.
Lemma arm_bnd_openat : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeInvArms "D';'9&SI':&Q3&S<&@r2(0%3221%511u1%6251u2%8271%;3531r1%?4>2:1pWNA1pWLC1").
Proof. intros i m. pres_auto. Qed.
Lemma arm_bnd_close : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeInvArms "@';'9&SI':&O&S<&@r2(0%3221%511%711r1%;4:261pWN=1pWL?1").
Proof. intros i m. pres_auto. Qed.
Lemma arm_bnd_pipe2 : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeInvArms "B';'9&SI':&Q4&@r2(0%3221&SBu1%6251%311%9251r1%=4<291pWN?1pWLA1").
Proof. intros i m. pres_auto. Qed.
Lemma arm_bnd_getdents64 : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeInvArms "B';'9&SI':&Q<&S<&@r2(0%3221%511u2%6251%9231r1%=4<281pWN?1pWLA1").
Proof. intros i m. pres_auto. Qed.
Lemma arm_bnd_lseek : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeInvArms "F';'9&SI':&Q5&S<&@r2(0%3221%511u1%6251&SFu2%9281%311%=3751r1%A4@2<1pWNC1pWLE1").
Proof. intros i m. pres_auto. Qed.
Lemma arm_bnd_read : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeInvArms "D';'9&SI':&Q8&S<&@r2(0%3221%511u1%6251u2%8271%;3531r1%?4>2:1pWNA1pWLC1").
Proof. intros i m. pres_auto. Qed.
Lemma arm_bnd_write : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeInvArms "D';'9&SI':&Q:&S<&@r2(0%3221%511u1%6251u2%8271%;3531r1%?4>2:1pWNA1pWLC1").
Proof. intros i m. pres_auto. Qed.
Lemma arm_bnd_readv : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeInvArms "D';'9&SI':&Q9&S<&@r2(0%3221%511u1%6251u2%8271%;3531r1%?4>2:1pWNA1pWLC1").
Proof. intros i m. pres_auto. Qed.
Lemma arm_bnd_writev : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeInvArms "D';'9&SI':&Q;&S<&@r2(0%3221%511u1%6251u2%8271%;3531r1%?4>2:1pWNA1pWLC1").
Proof. intros i m. pres_auto. Qed.
Lemma arm_bnd_pread64 : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeInvArms "F';'9&SI':&Q6&S<&@r2(0%3221%511u1%6251u2%8271u3%:291%=47531r1%A4@2<1pWNC1pWLE1").
Proof. intros i m. pres_auto. Qed.
Lemma arm_bnd_pwrite64 : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeInvArms "F';'9&SI':&Q7&S<&@r2(0%3221%511u1%6251u2%8271u3%:291%=47531r1%A4@2<1pWNC1pWLE1").
Proof. intros i m. pres_auto. Qed.
Lemma arm_bnd_pselect6 : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeInvArms "J';'9&SI':&Q>&S@&@r2(0%3221%511u1%6251u2%8271u3%:291u4%<2;1u5%>2=1%A6;97531r1%E4D2@1pWNG1pWLI1").
Proof. intros i m. pres_auto. Qed.
Lemma arm_bnd_ppoll : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeInvArms "H';'9&SI':&Q=&@r2(0%3221&SDu1%6251%311u2%9281u3%;2:1u4%=2<1%?5;7531r1%C4B2?1pWNE1pWLG1").
Proof. intros i m. pres_auto. Qed.
Lemma arm_bnd_readlinkat : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeInvArms "@';'9&SI':&QA&S<&@r2(0%3221%511%711r1%;4:261pWN=1pWL?1").
Proof. intros i m. pres_auto. Qed.
Lemma arm_bnd_newfstatat : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeInvArms "F';'9&SI':&Q@&S<&@r2(0%3221%511u1%6251&S=u3%9281%311%=3751r1%A4@2<1pWNC1pWLE1").
Proof. intros i m. pres_auto. Qed.
Lemma arm_bnd_fstat : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeInvArms "B';'9&SI':&Q?&S<&@r2(0%3221%511u1%6251%9231r1%=4<281pWN?1pWLA1").
Proof. intros i m. pres_auto. Qed.
Lemma arm_bnd_fsync : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeInvArms "@';'9&SI':&QB&S<&@r2(0%3221%511%711r1%;4:261pWN=1pWL?1").
Proof. intros i m. pres_auto. Qed.
Lemma arm_bnd_fdatasync : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeInvArms "@';'9&SI':&QB&S<&@r2(0%3221%511%711r1%;4:261pWN=1pWL?1").
Proof. intros i m. pres_auto. Qed.
Lemma arm_bnd_timerfd_create : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeInvArms "D';'9&SI':&QC&S:&@r2(0%3221%511&S=u1%7261%311%;251r1%?4>2:1pWNA1pWLC1").
Proof. intros i m. pres_auto. Qed.
Lemma arm_bnd_exit : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeInvArms ">';'9&SI':&QD&@r2(0%3221%511r1%948251pWN;1pWL=1").
Proof. intros i m. pres_auto. Qed.
Lemma arm_bnd_exit_group : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeInvArms ">';'9&SI':&QD&@r2(0%3221%511r1%948251pWN;1pWL=1").
Proof. intros i m. pres_auto. Qed.
Lemma arm_bnd_set_tid_address : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeInvArms ":';'9&SI':&QHr2r1%544321pWN71pWL91").
Proof. intros i m. pres_auto. Qed.
Lemma arm_bnd_futex : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeInvArms "D';'9&SI':&QI&@r2(0%3221u1%5241u2%7261u3%9281%;47531r1%?4>2;1pWNA1pWLC1").
Proof. intros i m. pres_auto. Qed.
Lemma arm_bnd_nanosleep : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeInvArms "@';'9&SI':&RB&@r2(0%3221u1%5241%7231r1%;4:271pWN=1pWL?1").
Proof. intros i m. pres_auto. Qed.
Lemma arm_bnd_clock_gettime : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeInvArms "B';'9&SI':&RC&S:&@r2(0%3221%511u1%6251%9231r1%=4<281pWN?1pWLA1").
Proof. intros i m. pres_auto. Qed.
Lemma arm_bnd_sched_setscheduler : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeInvArms "B';'9&SI':&QM&@r2(0%3221u1%5241u2%7261%93531r1%=4<291pWN?1pWLA1").
Proof. intros i m. pres_auto. Qed.
Lemma arm_bnd_sched_getaffinity : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeInvArms ">';'9&SI':&QL&@r2u1%3221%511r1%948251pWN;1pWL=1").
Proof. intros i m. pres_auto. Qed.
Lemma arm_bnd_sched_yield : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeInvArms ":';'9&SI':&QNr2r1%544321pWN71pWL91").
Proof. intros i m. pres_auto. Qed.
Lemma arm_bnd_tkill : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeInvArms "D';'9&SI':&R4&SA&@r2(0%3221%511&R1u1%7261%311%;251r1%?4>2:1pWNA1pWLC1").
Proof. intros i m. pres_auto. Qed.
Lemma arm_bnd_tgkill : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeInvArms "G';'9&SI':&R3&SA&@r2(0%3221%511u1%6251%811&R1u2%:291%311%>3851r1%B4A2=1pWND1pWLF1").
Proof. intros i m. pres_auto. Qed.
Lemma arm_bnd_sigaltstack : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeInvArms "@';'9&SI':&R2&@r2(0%3221u1%5241%7231r1%;4:271pWN=1pWL?1").
Proof. intros i m. pres_auto. Qed.
Lemma arm_bnd_rt_sigaction : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeInvArms "F';'9&SI':&QO&R1&@r2(0%3221%511u1%6251u2%8271u3%:291%=47531r1%A4@2<1pWNC1pWLE1").
Proof. intros i m. pres_auto. Qed.
Lemma arm_bnd_rt_sigprocmask : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeInvArms "F';'9&SI':&R0&S>&@r2(0%3221%511u1%6251u2%8271u3%:291%=47531r1%A4@2<1pWNC1pWLE1").
Proof. intros i m. pres_auto. Qed.
Lemma arm_bnd_setgid : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeInvArms "C';'9&SI':&R>&R5&R<(2&SC&@r2(0%3221%511%:49871r1%>4=261pWN@1pWLB1").
Proof. intros i m. pres_auto. Qed.
Lemma arm_bnd_setuid : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeInvArms "C';'9&SI':&R>&R6&R=(5&SC&@r2(0%3221%511%:49871r1%>4=261pWN@1pWLB1").
Proof. intros i m. pres_auto. Qed.
Lemma arm_bnd_setresuid : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeInvArms "I';'9&SI':&R?&R6&R=(5&SC&@r2(0%3221%511u1%6251%811u2%9281%;11%@6?>=741r1%D4C2<1pWNF1pWLH1").
Proof. intros i m. pres_auto. Qed.
Lemma arm_bnd_setresgid : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeInvArms "I';'9&SI':&R?&R5&R<(2&SC&@r2(0%3221%511u1%6251%811u2%9281%;11%@6?>=741r1%D4C2<1pWNF1pWLH1").
Proof. intros i m. pres_auto. Qed.
Lemma arm_bnd_setsid : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeInvArms ":';'9&SI':&R@r2r1%544321pWN71pWL91").
Proof. intros i m. pres_auto. Qed.
Lemma arm_bnd_getgroups : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeInvArms ">';'9&SI':&QJ&@r2(0%3221%511r1%948251pWN;1pWL=1").
Proof. intros i m. pres_auto. Qed.
Lemma arm_bnd_setgroups : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeInvArms ":';'9&SI':&QKr2r1%544321pWN71pWL91").
Proof. intros i m. pres_auto. Qed.
Lemma arm_bnd_uname : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeInvArms ">';'9&SI':&RA&@r2(0%3221%511r1%948251pWN;1pWL=1").
Proof. intros i m. pres_auto. Qed.
Lemma arm_bnd_prctl : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeInvArms "B';'9&SI':&R:&S?&@r2(0%3221%511u1%6251%9231r1%=4<281pWN?1pWLA1").
Proof. intros i m. pres_auto. Qed.
Lemma arm_bnd_gettimeofday : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeInvArms "@';'9&SI':&RD&@r2(0%3221u1%5241%7231r1%;4:271pWN=1pWL?1").
Proof. intros i m. pres_auto. Qed.
Lemma arm_bnd_getpid : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeInvArms ":';'9&SI':&R8r2r1%544321pWN71pWL91").
Proof. intros i m. pres_auto. Qed.
Lemma arm_bnd_getuid : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeInvArms "<';'9&SI':&R7&?%211r2r1%746321pWN91pWL;1").
Proof. intros i m. pres_auto. Qed.
Lemma arm_bnd_geteuid : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeInvArms "<';'9&SI':&R7&=%211r2r1%746321pWN91pWL;1").
Proof. intros i m. pres_auto. Qed.
Lemma arm_bnd_getgid : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeInvArms "<';'9&SI':&R7&>%211r2r1%746321pWN91pWL;1").
Proof. intros i m. pres_auto. Qed.
Lemma arm_bnd_getegid : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeInvArms "<';'9&SI':&R7&<%211r2r1%746321pWN91pWL;1").
Proof. intros i m. pres_auto. Qed.
Lemma arm_bnd_gettid : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeInvArms ":';'9&SI':&R9r2r1%544321pWN71pWL91").
Proof. intros i m. pres_auto. Qed.
Lemma arm_bnd_socket : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeInvArms "B';'9&SI':&S8&@r2(0%3221u1%5241u2%7261%93531r1%=4<291pWN?1pWLA1").
Proof. intros i m. pres_auto. Qed.
Lemma arm_bnd_socketpair : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeInvArms "D';'9&SI':&S9&@r2(0%3221u1%5241u2%7261u3%9281%;47531r1%?4>2;1pWNA1pWLC1").
Proof. intros i m. pres_auto. Qed.
Lemma arm_bnd_bind : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeInvArms "D';'9&SI':&RL&S<&@r2(0%3221%511u1%6251u2%8271%;3531r1%?4>2:1pWNA1pWLC1").
Proof. intros i m. pres_auto. Qed.
Lemma arm_bnd_listen : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeInvArms "B';'9&SI':&S1&S<&@r2(0%3221%511u1%6251%9231r1%=4<281pWN?1pWLA1").
Proof. intros i m. pres_auto. Qed.
Lemma arm_bnd_accept : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeInvArms "H';'9&SI':&RK&S<&@r2(0%3221%511u1%6251u2%8271&T0yR0z%3221%?49751r1%C4B2>1pWNE1pWLG1").
Proof. intros i m. pres_auto. Qed.
Lemma arm_bnd_connect : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeInvArms "D';'9&SI':&RM&S<&@r2(0%3221%511u1%6251u2%8271%;3531r1%?4>2:1pWNA1pWLC1").
Proof. intros i m. pres_auto. Qed.
Lemma arm_bnd_getsockname : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeInvArms "@';'9&SI':&RO&S<&@r2(0%3221%511%711r1%;4:261pWN=1pWL?1").
Proof. intros i m. pres_auto. Qed.
Lemma arm_bnd_getpeername : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeInvArms "@';'9&SI':&RN&S<&@r2(0%3221%511%711r1%;4:261pWN=1pWL?1").
Proof. intros i m. pres_auto. Qed.
Lemma arm_bnd_sendto : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeInvArms "J';'9&SI':&S5&S<&@r2(0%3221%511u1%6251u2%8271u3%:291u4%<2;1u5%>2=1%A6;97531r1%E4D2@1pWNG1pWLI1").
Proof. intros i m. pres_auto. Qed.
Lemma arm_bnd_recvfrom : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeInvArms "D';'9&SI':&S2&S<&@r2(0%3221%511u1%6251u2%8271%;3531r1%?4>2:1pWNA1pWLC1").
Proof. intros i m. pres_auto. Qed.
Lemma arm_bnd_setsockopt : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeInvArms "G';'9&SI':&S6&S<&@r2(0%3221%511&S?u1%7261%311u4%:291%611%>3841r1%B4A2=1pWND1pWLF1").
Proof. intros i m. pres_auto. Qed.
Lemma arm_bnd_getsockopt : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeInvArms "F';'9&SI':&S0&S<&@r2(0%3221%511&S?u1%7261%311u4%:291%=3731r1%A4@2<1pWNC1pWLE1").
Proof. intros i m. pres_auto. Qed.
Lemma arm_bnd_shutdown : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeInvArms "D';'9&SI':&S7&S<&@r2(0%3221%511&S?u1%7261%311%;251r1%?4>2:1pWNA1pWLC1").
Proof. intros i m. pres_auto. Qed.
Lemma arm_bnd_sendmsg : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeInvArms "D';'9&SI':&S4&S<&@r2(0%3221%511u1%6251u2%8271%;3531r1%?4>2:1pWNA1pWLC1").
Proof. intros i m. pres_auto. Qed.
Lemma arm_bnd_recvmsg : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeInvArms "B';'9&SI':&S3&S<&@r2(0%3221%511u2%6251%9231r1%=4<281pWN?1pWLA1").
Proof. intros i m. pres_auto. Qed.
Lemma arm_bnd_brk : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeInvArms ">';'9&SI':&RF&@r2(0%3221%511r1%948251pWN;1pWL=1").
Proof. intros i m. pres_auto. Qed.
Lemma arm_bnd_munmap : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeInvArms "@';'9&SI':&RH&@r2(0%3221u1%5241%7231r1%;4:271pWN=1pWL?1").
Proof. intros i m. pres_auto. Qed.
Lemma arm_bnd_mremap : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeInvArms "D';'9&SI':&RJ&@r2(0%3221u1%5241u2%7261u3%9281%;47531r1%?4>2;1pWNA1pWLC1").
Proof. intros i m. pres_auto. Qed.
Lemma arm_bnd_clone : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeInvArms ">';'9&SI':&QG&@r2(0%3221%511r1%948251pWN;1pWL=1").
Proof. intros i m. pres_auto. Qed.
Lemma arm_bnd_mmap : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeInvArms "H';'9&SI':&RG&@r2(0%3221u1%5241u2%7261u3%9281u4%;2:1u5%=2<1%?6;97531r1%C4B2?1pWNE1pWLG1").
Proof. intros i m. pres_auto. Qed.
Lemma arm_bnd_mprotect : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeInvArms "B';'9&SI':&RI&@r2(0%3221u1%5241u2%7261%93531r1%=4<291pWN?1pWLA1").
Proof. intros i m. pres_auto. Qed.
Lemma arm_bnd_madvise : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeInvArms "D';'9&SI':&RE&@r2(0%3221u1%5241&S?u2%8271%311%;3751r1%?4>2;1pWNA1pWLC1").
Proof. intros i m. pres_auto. Qed.
Lemma arm_bnd_accept4 : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeInvArms "F';'9&SI':&RK&S<&@r2(0%3221%511u1%6251u2%8271u3%:291%=47531r1%A4@2<1pWNC1pWLE1").
Proof. intros i m. pres_auto. Qed.
Lemma arm_bnd_wait4 : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeInvArms "H';'9&SI':&QE&SA&@r2(0%3221%511u1%6251&SEu2%9281%311u3%<2;1%?49731r1%C4B2>1pWNE1pWLG1").
Proof. intros i m. pres_auto. Qed.
Lemma arm_bnd_prlimit64 : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeInvArms "D';'9&SI':&R;&@r2(0%3221u1%5241u2%7261u3%9281%;47531r1%?4>2;1pWNA1pWLC1").
Proof. intros i m. pres_auto. Qed.
Lemma arm_bnd_getrandom : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeInvArms "B';'9&SI':&C&@r2(0%3221u1%5241u2%7261%93531r1%=4<291pWN?1pWLA1").
Proof. intros i m. pres_auto. Qed.
Lemma arm_bnd_clone3 : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeInvArms "@';'9&SI':&QF&@r2(0%3221u1%5241%7231r1%;4:271pWN=1pWL?1").
Proof. intros i m. pres_auto. Qed.
Lemma arm_bnd_faccessat2 : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeInvArms "F';'9&SI':&Q0&S<&@r2(0%3221%511u1%6251u2%8271u3%:291%=47531r1%A4@2<1pWNC1pWLE1").
Proof. intros i m. pres_auto. Qed.
Lemma lookup_arm_in_b : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeInvArms "F'3'A%211'8'6'4%115&Br3r2%3221(1r1%22<1%:3841&SKr4%23@81p041pWJB1pX0A1pX4C1").
Proof.
induction t as [| x t IH]; intros n a H; [discriminate H |].
cbn in H. destruct (Z.eqb (sa_no x) n) eqn:E.
- injection H as <-. left; reflexivity.
- right. exact (IH n a H).
Qed.
Definition arm_bnd (a : SpecArm) : Prop := forall i m, Pres1 (sa_spec a) i m.
Lemma spec_table_bnd : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeInvArms "5'7'A&SH&SG%43321").
Proof.
unfold spec_table.
apply Forall_cons; [ intros i m; cbn [sa_spec]; apply (pres1_reader (fun i : SyscallInput => getcwd_spec (in_arg i 1))); exact (arm_bnd_getcwd i m) |].
apply Forall_cons; [ intros i m; cbn [sa_spec]; apply (pres1_reader (fun i : SyscallInput => eventfd2_spec (flag32 (in_arg i 1)))); exact (arm_bnd_eventfd2 i m) |].
apply Forall_cons; [ intros i m; cbn [sa_spec]; apply (pres1_reader (fun i : SyscallInput => epoll_create1_spec (flag32 (in_arg i 0)))); exact (arm_bnd_epoll_create1 i m) |].
apply Forall_cons; [ intros i m; cbn [sa_spec]; apply (pres1_reader (fun i : SyscallInput => epoll_ctl_spec (fd32 (in_arg i 0)) (int32 (in_arg i 1)) (fd32 (in_arg i 2)) (in_arg i 3))); exact (arm_bnd_epoll_ctl i m) |].
apply Forall_cons; [ intros i m; cbn [sa_spec]; apply (pres1_reader (fun i : SyscallInput => epoll_pwait_spec (fd32 (in_arg i 0)) (in_arg i 1) (int32 (in_arg i 2)) (in_arg i 4) (in_arg i 5))); exact (arm_bnd_epoll_pwait i m) |].
apply Forall_cons; [ intros i m; cbn [sa_spec]; apply (pres1_reader (fun i : SyscallInput => dup_spec (fd32 (in_arg i 0)))); exact (arm_bnd_dup i m) |].
apply Forall_cons; [ intros i m; cbn [sa_spec]; apply (pres1_reader (fun i : SyscallInput => dup3_spec (fd32 (in_arg i 0)) (fd32 (in_arg i 1)) (in_arg i 2))); exact (arm_bnd_dup3 i m) |].
apply Forall_cons; [ intros i m; cbn [sa_spec]; apply (pres1_reader (fun i : SyscallInput => fcntl_spec (fd32 (in_arg i 0)) (cmd32 (in_arg i 1)) (in_arg i 2))); exact (arm_bnd_fcntl i m) |].
apply Forall_cons; [ intros i m; cbn [sa_spec]; apply (pres1_reader (fun i : SyscallInput => ioctl_spec (fd32 (in_arg i 0)) (cmd32 (in_arg i 1)))); exact (arm_bnd_ioctl i m) |].
apply Forall_cons; [ intros i m; cbn [sa_spec]; apply (pres1_reader (fun i : SyscallInput => flock_spec (fd32 (in_arg i 0)) (cmd32 (in_arg i 1)))); exact (arm_bnd_flock i m) |].
apply Forall_cons; [ intros i m; cbn [sa_spec]; apply (pres1_reader (fun i : SyscallInput => unlinkat_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2))); exact (arm_bnd_unlinkat i m) |].
apply Forall_cons; [ intros i m; cbn [sa_spec]; apply (pres1_reader (fun i : SyscallInput => ftruncate_spec (fd32 (in_arg i 0)) (in_arg i 1))); exact (arm_bnd_ftruncate i m) |].
apply Forall_cons; [ intros i m; cbn [sa_spec]; apply (pres1_reader (fun i : SyscallInput => faccessat_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2))); exact (arm_bnd_faccessat i m) |].
apply Forall_cons; [ intros i m; cbn [sa_spec]; apply (pres1_reader (fun i : SyscallInput => openat_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2))); exact (arm_bnd_openat i m) |].
apply Forall_cons; [ intros i m; cbn [sa_spec]; apply (pres1_reader (fun i : SyscallInput => close_spec (fd32 (in_arg i 0)))); exact (arm_bnd_close i m) |].
apply Forall_cons; [ intros i m; cbn [sa_spec]; apply (pres1_reader (fun i : SyscallInput => pipe2_spec (in_arg i 0) (pipe_flags32 (in_arg i 1)))); exact (arm_bnd_pipe2 i m) |].
apply Forall_cons; [ intros i m; cbn [sa_spec]; apply (pres1_reader (fun i : SyscallInput => getdents64_spec (fd32 (in_arg i 0)) (in_arg i 2))); exact (arm_bnd_getdents64 i m) |].
apply Forall_cons; [ intros i m; cbn [sa_spec]; apply (pres1_reader (fun i : SyscallInput => lseek_spec (fd32 (in_arg i 0)) (in_arg i 1) (whence32 (in_arg i 2)))); exact (arm_bnd_lseek i m) |].
apply Forall_cons; [ intros i m; cbn [sa_spec]; apply (pres1_reader (fun i : SyscallInput => read_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2))); exact (arm_bnd_read i m) |].
apply Forall_cons; [ intros i m; cbn [sa_spec]; apply (pres1_reader (fun i : SyscallInput => write_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2))); exact (arm_bnd_write i m) |].
apply Forall_cons; [ intros i m; cbn [sa_spec]; apply (pres1_reader (fun i : SyscallInput => readv_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2))); exact (arm_bnd_readv i m) |].
apply Forall_cons; [ intros i m; cbn [sa_spec]; apply (pres1_reader (fun i : SyscallInput => writev_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2))); exact (arm_bnd_writev i m) |].
apply Forall_cons; [ intros i m; cbn [sa_spec]; apply (pres1_reader (fun i : SyscallInput => pread64_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3))); exact (arm_bnd_pread64 i m) |].
apply Forall_cons; [ intros i m; cbn [sa_spec]; apply (pres1_reader (fun i : SyscallInput => pwrite64_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3))); exact (arm_bnd_pwrite64 i m) |].
apply Forall_cons; [ intros i m; cbn [sa_spec]; apply (pres1_reader (fun i : SyscallInput => pselect6_spec (nfds32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) (in_arg i 5))); exact (arm_bnd_pselect6 i m) |].
apply Forall_cons; [ intros i m; cbn [sa_spec]; apply (pres1_reader (fun i : SyscallInput => ppoll_spec (in_arg i 0) (unfds32 (in_arg i 1)) (in_arg i 2) (in_arg i 3) (in_arg i 4))); exact (arm_bnd_ppoll i m) |].
apply Forall_cons; [ intros i m; cbn [sa_spec]; apply (pres1_reader (fun i : SyscallInput => readlinkat_spec (fd32 (in_arg i 0)))); exact (arm_bnd_readlinkat i m) |].
apply Forall_cons; [ intros i m; cbn [sa_spec]; apply (pres1_reader (fun i : SyscallInput => newfstatat_spec (fd32 (in_arg i 0)) (in_arg i 1) (flag32 (in_arg i 3)))); exact (arm_bnd_newfstatat i m) |].
apply Forall_cons; [ intros i m; cbn [sa_spec]; apply (pres1_reader (fun i : SyscallInput => fstat_spec (fd32 (in_arg i 0)) (in_arg i 1))); exact (arm_bnd_fstat i m) |].
apply Forall_cons; [ intros i m; cbn [sa_spec]; apply (pres1_reader (fun i : SyscallInput => fsync_spec (fd32 (in_arg i 0)))); exact (arm_bnd_fsync i m) |].
apply Forall_cons; [ intros i m; cbn [sa_spec]; apply (pres1_reader (fun i : SyscallInput => fsync_spec (fd32 (in_arg i 0)))); exact (arm_bnd_fdatasync i m) |].
apply Forall_cons; [ intros i m; cbn [sa_spec]; apply (pres1_reader (fun i : SyscallInput => timerfd_create_spec (clockid32 (in_arg i 0)) (flag32 (in_arg i 1)))); exact (arm_bnd_timerfd_create i m) |].
apply Forall_cons; [ intros i m; cbn [sa_spec]; apply (pres1_reader (fun i : SyscallInput => exit_spec (in_arg i 0))); exact (arm_bnd_exit i m) |].
apply Forall_cons; [ intros i m; cbn [sa_spec]; apply (pres1_reader (fun i : SyscallInput => exit_spec (in_arg i 0))); exact (arm_bnd_exit_group i m) |].
apply Forall_cons; [ intros i m; cbn [sa_spec]; apply (pres1_reader (fun i : SyscallInput => set_tid_address_spec)); exact (arm_bnd_set_tid_address i m) |].
apply Forall_cons; [ intros i m; cbn [sa_spec]; apply (pres1_reader (fun i : SyscallInput => futex_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3))); exact (arm_bnd_futex i m) |].
apply Forall_cons; [ intros i m; cbn [sa_spec]; apply (pres1_reader (fun i : SyscallInput => nanosleep_spec (in_arg i 0) (in_arg i 1))); exact (arm_bnd_nanosleep i m) |].
apply Forall_cons; [ intros i m; cbn [sa_spec]; apply (pres1_reader (fun i : SyscallInput => clock_gettime_spec (clockid32 (in_arg i 0)) (in_arg i 1))); exact (arm_bnd_clock_gettime i m) |].
apply Forall_cons; [ intros i m; cbn [sa_spec]; apply (pres1_reader (fun i : SyscallInput => sched_setscheduler_spec (in_arg i 0) (in_arg i 1) (in_arg i 2))); exact (arm_bnd_sched_setscheduler i m) |].
apply Forall_cons; [ intros i m; cbn [sa_spec]; apply (pres1_reader (fun i : SyscallInput => sched_getaffinity_spec (in_arg i 1))); exact (arm_bnd_sched_getaffinity i m) |].
apply Forall_cons; [ intros i m; cbn [sa_spec]; apply (pres1_reader (fun i : SyscallInput => sched_yield_spec)); exact (arm_bnd_sched_yield i m) |].
apply Forall_cons; [ intros i m; cbn [sa_spec]; apply (pres1_reader (fun i : SyscallInput => tkill_spec (pid32 (in_arg i 0)) (sig32 (in_arg i 1)))); exact (arm_bnd_tkill i m) |].
apply Forall_cons; [ intros i m; cbn [sa_spec]; apply (pres1_reader (fun i : SyscallInput => tgkill_spec (pid32 (in_arg i 0)) (pid32 (in_arg i 1)) (sig32 (in_arg i 2)))); exact (arm_bnd_tgkill i m) |].
apply Forall_cons; [ intros i m; cbn [sa_spec]; apply (pres1_reader (fun i : SyscallInput => sigaltstack_spec (in_arg i 0) (in_arg i 1))); exact (arm_bnd_sigaltstack i m) |].
apply Forall_cons; [ intros i m; cbn [sa_spec]; apply (pres1_reader (fun i : SyscallInput => rt_sigaction_spec (sig32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3))); exact (arm_bnd_rt_sigaction i m) |].
apply Forall_cons; [ intros i m; cbn [sa_spec]; apply (pres1_reader (fun i : SyscallInput => rt_sigprocmask_spec (how32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3))); exact (arm_bnd_rt_sigprocmask i m) |].
apply Forall_cons; [ intros i m; cbn [sa_spec]; apply (pres1_reader (fun i : SyscallInput => setid_spec cred_gids set_cred_gids false (uid32 (in_arg i 0)))); exact (arm_bnd_setgid i m) |].
apply Forall_cons; [ intros i m; cbn [sa_spec]; apply (pres1_reader (fun i : SyscallInput => setid_spec cred_uids set_cred_uids true (uid32 (in_arg i 0)))); exact (arm_bnd_setuid i m) |].
apply Forall_cons; [ intros i m; cbn [sa_spec]; apply (pres1_reader (fun i : SyscallInput => setresid_spec cred_uids set_cred_uids true (uid32 (in_arg i 0)) (uid32 (in_arg i 1)) (uid32 (in_arg i 2)))); exact (arm_bnd_setresuid i m) |].
apply Forall_cons; [ intros i m; cbn [sa_spec]; apply (pres1_reader (fun i : SyscallInput => setresid_spec cred_gids set_cred_gids false (uid32 (in_arg i 0)) (uid32 (in_arg i 1)) (uid32 (in_arg i 2)))); exact (arm_bnd_setresgid i m) |].
apply Forall_cons; [ intros i m; cbn [sa_spec]; apply (pres1_reader (fun i : SyscallInput => setsid_spec)); exact (arm_bnd_setsid i m) |].
apply Forall_cons; [ intros i m; cbn [sa_spec]; apply (pres1_reader (fun i : SyscallInput => getgroups_spec (in_arg i 0))); exact (arm_bnd_getgroups i m) |].
apply Forall_cons; [ intros i m; cbn [sa_spec]; apply (pres1_reader (fun i : SyscallInput => setgroups_spec)); exact (arm_bnd_setgroups i m) |].
apply Forall_cons; [ intros i m; cbn [sa_spec]; apply (pres1_reader (fun i : SyscallInput => uname_spec (in_arg i 0))); exact (arm_bnd_uname i m) |].
apply Forall_cons; [ intros i m; cbn [sa_spec]; apply (pres1_reader (fun i : SyscallInput => prctl_spec (int32 (in_arg i 0)) (in_arg i 1))); exact (arm_bnd_prctl i m) |].
apply Forall_cons; [ intros i m; cbn [sa_spec]; apply (pres1_reader (fun i : SyscallInput => gettimeofday_spec (in_arg i 0) (in_arg i 1))); exact (arm_bnd_gettimeofday i m) |].
apply Forall_cons; [ intros i m; cbn [sa_spec]; apply (pres1_reader (fun i : SyscallInput => getpid_spec)); exact (arm_bnd_getpid i m) |].
apply Forall_cons; [ intros i m; cbn [sa_spec]; apply (pres1_reader (fun i : SyscallInput => getid_spec cr_uid)); exact (arm_bnd_getuid i m) |].
apply Forall_cons; [ intros i m; cbn [sa_spec]; apply (pres1_reader (fun i : SyscallInput => getid_spec cr_euid)); exact (arm_bnd_geteuid i m) |].
apply Forall_cons; [ intros i m; cbn [sa_spec]; apply (pres1_reader (fun i : SyscallInput => getid_spec cr_gid)); exact (arm_bnd_getgid i m) |].
apply Forall_cons; [ intros i m; cbn [sa_spec]; apply (pres1_reader (fun i : SyscallInput => getid_spec cr_egid)); exact (arm_bnd_getegid i m) |].
apply Forall_cons; [ intros i m; cbn [sa_spec]; apply (pres1_reader (fun i : SyscallInput => gettid_spec)); exact (arm_bnd_gettid i m) |].
apply Forall_cons; [ intros i m; cbn [sa_spec]; apply (pres1_reader (fun i : SyscallInput => socket_spec (in_arg i 0) (in_arg i 1) (in_arg i 2))); exact (arm_bnd_socket i m) |].
apply Forall_cons; [ intros i m; cbn [sa_spec]; apply (pres1_reader (fun i : SyscallInput => socketpair_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3))); exact (arm_bnd_socketpair i m) |].
apply Forall_cons; [ intros i m; cbn [sa_spec]; apply (pres1_reader (fun i : SyscallInput => bind_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2))); exact (arm_bnd_bind i m) |].
apply Forall_cons; [ intros i m; cbn [sa_spec]; apply (pres1_reader (fun i : SyscallInput => listen_spec (fd32 (in_arg i 0)) (in_arg i 1))); exact (arm_bnd_listen i m) |].
apply Forall_cons; [ intros i m; cbn [sa_spec]; apply (pres1_reader (fun i : SyscallInput => accept4_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (Z_to_bv 64 0))); exact (arm_bnd_accept i m) |].
apply Forall_cons; [ intros i m; cbn [sa_spec]; apply (pres1_reader (fun i : SyscallInput => connect_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2))); exact (arm_bnd_connect i m) |].
apply Forall_cons; [ intros i m; cbn [sa_spec]; apply (pres1_reader (fun i : SyscallInput => getsockname_spec (fd32 (in_arg i 0)))); exact (arm_bnd_getsockname i m) |].
apply Forall_cons; [ intros i m; cbn [sa_spec]; apply (pres1_reader (fun i : SyscallInput => getpeername_spec (fd32 (in_arg i 0)))); exact (arm_bnd_getpeername i m) |].
apply Forall_cons; [ intros i m; cbn [sa_spec]; apply (pres1_reader (fun i : SyscallInput => sendto_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) (in_arg i 5))); exact (arm_bnd_sendto i m) |].
apply Forall_cons; [ intros i m; cbn [sa_spec]; apply (pres1_reader (fun i : SyscallInput => recvfrom_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2))); exact (arm_bnd_recvfrom i m) |].
apply Forall_cons; [ intros i m; cbn [sa_spec]; apply (pres1_reader (fun i : SyscallInput => setsockopt_spec (fd32 (in_arg i 0)) (int32 (in_arg i 1)) (int32 (in_arg i 4)))); exact (arm_bnd_setsockopt i m) |].
apply Forall_cons; [ intros i m; cbn [sa_spec]; apply (pres1_reader (fun i : SyscallInput => getsockopt_spec (fd32 (in_arg i 0)) (int32 (in_arg i 1)) (in_arg i 4))); exact (arm_bnd_getsockopt i m) |].
apply Forall_cons; [ intros i m; cbn [sa_spec]; apply (pres1_reader (fun i : SyscallInput => shutdown_spec (fd32 (in_arg i 0)) (int32 (in_arg i 1)))); exact (arm_bnd_shutdown i m) |].
apply Forall_cons; [ intros i m; cbn [sa_spec]; apply (pres1_reader (fun i : SyscallInput => sendmsg_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2))); exact (arm_bnd_sendmsg i m) |].
apply Forall_cons; [ intros i m; cbn [sa_spec]; apply (pres1_reader (fun i : SyscallInput => recvmsg_spec (fd32 (in_arg i 0)) (in_arg i 2))); exact (arm_bnd_recvmsg i m) |].
apply Forall_cons; [ intros i m; cbn [sa_spec]; apply (pres1_reader (fun i : SyscallInput => brk_spec (in_arg i 0))); exact (arm_bnd_brk i m) |].
apply Forall_cons; [ intros i m; cbn [sa_spec]; apply (pres1_reader (fun i : SyscallInput => munmap_spec (in_arg i 0) (in_arg i 1))); exact (arm_bnd_munmap i m) |].
apply Forall_cons; [ intros i m; cbn [sa_spec]; apply (pres1_reader (fun i : SyscallInput => mremap_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3))); exact (arm_bnd_mremap i m) |].
apply Forall_cons; [ intros i m; cbn [sa_spec]; apply (pres1_reader (fun i : SyscallInput => clone_spec (in_arg i 0))); exact (arm_bnd_clone i m) |].
apply Forall_cons; [ intros i m; cbn [sa_spec]; apply (pres1_reader (fun i : SyscallInput => mmap_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) (in_arg i 5))); exact (arm_bnd_mmap i m) |].
apply Forall_cons; [ intros i m; cbn [sa_spec]; apply (pres1_reader (fun i : SyscallInput => mprotect_spec (in_arg i 0) (in_arg i 1) (in_arg i 2))); exact (arm_bnd_mprotect i m) |].
apply Forall_cons; [ intros i m; cbn [sa_spec]; apply (pres1_reader (fun i : SyscallInput => madvise_spec (in_arg i 0) (in_arg i 1) (int32 (in_arg i 2)))); exact (arm_bnd_madvise i m) |].
apply Forall_cons; [ intros i m; cbn [sa_spec]; apply (pres1_reader (fun i : SyscallInput => accept4_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3))); exact (arm_bnd_accept4 i m) |].
apply Forall_cons; [ intros i m; cbn [sa_spec]; apply (pres1_reader (fun i : SyscallInput => wait4_spec (pid32 (in_arg i 0)) (in_arg i 1) (waitopts32 (in_arg i 2)) (in_arg i 3))); exact (arm_bnd_wait4 i m) |].
apply Forall_cons; [ intros i m; cbn [sa_spec]; apply (pres1_reader (fun i : SyscallInput => prlimit64_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3))); exact (arm_bnd_prlimit64 i m) |].
apply Forall_cons; [ intros i m; cbn [sa_spec]; apply (pres1_reader (fun i : SyscallInput => getrandom_spec (in_arg i 0) (in_arg i 1) (in_arg i 2))); exact (arm_bnd_getrandom i m) |].
apply Forall_cons; [ intros i m; cbn [sa_spec]; apply (pres1_reader (fun i : SyscallInput => clone3_spec (in_arg i 0) (in_arg i 1))); exact (arm_bnd_clone3 i m) |].
apply Forall_cons; [ intros i m; cbn [sa_spec]; apply (pres1_reader (fun i : SyscallInput => faccessat2_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3))); exact (arm_bnd_faccessat2 i m) |].
apply Forall_nil.
Qed.
Theorem bounded_pres : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeInvArms "1&SJ").
Proof.
intros i m eff m' evs H Hb. unfold syscall_spec, dispatch in H.
destruct (lookup_arm spec_table (bv_unsigned (in_sysno i))) as [a|] eqn:E; [|discriminate H].
pose proof spec_table_bnd as G. rewrite Forall_forall in G.
exact (G a (lookup_arm_in_b _ _ _ E) i m Hb eff m' evs H).
Qed.
