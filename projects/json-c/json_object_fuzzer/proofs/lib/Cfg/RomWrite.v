(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: the openat part of projects/bzip2/bzip2_compress_target/proofs/lib/Common/Cfg/RomWrite.v with its write-to-channel lemmas cut (json-c reaches no write node), namespace renamed, and json-c's own newfstatat, ioctl and writev cases ([RomBase.sys_rob] at the openat, newfstatat, ioctl and writev nodes). *)
(* json-c copy of the openat part of projects/bzip2/bzip2_compress_target/proofs/lib/Common/Cfg/RomWrite.v
   (namespace renamed; its write-to-channel lemmas left out: json-c reaches no write (64) node), and
   the same argument for newfstatat.  [RomBase.sys_rob] for openat (56) and newfstatat (79): each check
   reads [in_mem] only through the path ([read_cstr] and the copy-in record [cstr_access_len_aux]),
   so a path read that does not fault is the same on a larger backing. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run VdsoCommute.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qn1e.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Cfg Require Import RomBase.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Cfg Require RomWritev.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Local Lemma in_mem_sys_input : forall segs ms x8, in_mem (sys_input segs ms x8) = ms_read_byte ms.
Proof. reflexivity. Qed.

(** openat reads [in_mem] only through the path ([read_cstr] in [check_openat_body] and the
    copy-in record [cstr_access_len_aux]); a path read that does not fault is the same on a
    larger view ([RomBase.read_cstr_ext], [RomBase.cstr_access_len_aux_ext]). *)
Lemma check_openat_ext : forall i mp' dirfd pathp flags eff m,
  mem_ext (in_mem i) mp' -> read_cstr (in_mem i) pathp <> CstrFault ->
  check_openat (with_mem i mp') dirfd pathp flags eff m = check_openat i dirfd pathp flags eff m.
Proof.
  intros i mp' dirfd pathp flags eff m Hx Hnf.
  unfold check_openat, Open.check_openat_body. unfold with_mem. cbn [in_mem].
  rewrite (cstr_access_len_aux_ext path_max (in_mem i) mp' pathp Hx Hnf).
  rewrite (read_cstr_ext (in_mem i) mp' pathp Hx Hnf).
  reflexivity.
Qed.

(* json-c's own, the same argument for newfstatat (79): [Checks/Sys/Fs/Stat.v]'s [check_newfstatat]
   reads [in_mem] only through the path's [read_cstr] and its copy-in record *)
Lemma check_newfstatat_ext : forall i mp' dirfd pathp flag eff m,
  mem_ext (in_mem i) mp' -> read_cstr (in_mem i) pathp <> CstrFault ->
  check_newfstatat (with_mem i mp') dirfd pathp flag eff m = check_newfstatat i dirfd pathp flag eff m.
Proof.
  intros i mp' dirfd pathp flag eff m Hx Hnf.
  unfold check_newfstatat. unfold with_mem. cbn [in_mem].
  rewrite (cstr_access_len_aux_ext path_max (in_mem i) mp' pathp Hx Hnf).
  rewrite (read_cstr_ext (in_mem i) mp' pathp Hx Hnf).
  reflexivity.
Qed.

Lemma check_syscall_79_stat : forall segs ms x8 eff m,
  bv_unsigned x8 = 79%Z ->
  check_syscall (sys_input segs ms x8) eff m
  = check_newfstatat (sys_input segs ms x8) (fd32 (ms_gpr ms 0)) (ms_gpr ms 1) (flag32 (ms_gpr ms 3)) eff m.
Proof.
  intros segs ms x8 eff m Hno. unfold check_syscall.
  change (in_sysno (sys_input segs ms x8)) with x8. rewrite Hno. reflexivity.
Qed.

(* json-c's own: ioctl (29) reads [in_mem] only in SIOCGIFINDEX's arm ([Checks/Sys/Fs/Ioctl.v]'s
   [check_ioctl]), which a terminal-only request never reaches *)
Lemma check_syscall_29_ioctl : forall segs ms x8 eff m,
  bv_unsigned x8 = 29%Z ->
  check_syscall (sys_input segs ms x8) eff m
  = check_ioctl (sys_input segs ms x8) (fd32 (ms_gpr ms 0)) (cmd32 (ms_gpr ms 1)) eff m.
Proof.
  intros segs ms x8 eff m Hno. unfold check_syscall.
  change (in_sysno (sys_input segs ms x8)) with x8. rewrite Hno. reflexivity.
Qed.

Section Seg.
Variable segs : list Segment.

(** An openat node whose path read does not fault. *)
Lemma openat_rob : forall ms model x8,
  ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 56%Z ->
  read_cstr (ms_read_byte ms) (ms_gpr ms 1) <> CstrFault ->
  sys_rob segs (mkCfg ms model).
Proof.
  intros ms model x8 Hs Hno Hnf.
  apply sys_rob_of_check. intros r x8' Hrr Hs' v eff. rewrite Hs in Hs'. injection Hs' as <-.
  rewrite !(Qn1e.check_syscall_56 segs _ x8 eff (with_vdso v model) Hno).
  rewrite sys_input_wrom.
  change (ms_gpr (wrom ms r) 0) with (ms_gpr ms 0). change (ms_gpr (wrom ms r) 1) with (ms_gpr ms 1).
  change (ms_gpr (wrom ms r) 2) with (ms_gpr ms 2).
  apply check_openat_ext.
  - rewrite in_mem_sys_input. apply mem_ext_read_byte_wrom. exact Hrr.
  - rewrite in_mem_sys_input. exact Hnf.
Qed.

(** A newfstatat node whose path read does not fault (json-c's own, as [openat_rob]). *)
Lemma newfstatat_rob : forall ms model x8,
  ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 79%Z ->
  read_cstr (ms_read_byte ms) (ms_gpr ms 1) <> CstrFault ->
  sys_rob segs (mkCfg ms model).
Proof.
  intros ms model x8 Hs Hno Hnf.
  apply sys_rob_of_check. intros r x8' Hrr Hs' v eff. rewrite Hs in Hs'. injection Hs' as <-.
  rewrite !(check_syscall_79_stat segs _ x8 eff (with_vdso v model) Hno).
  rewrite sys_input_wrom.
  change (ms_gpr (wrom ms r) 0) with (ms_gpr ms 0). change (ms_gpr (wrom ms r) 1) with (ms_gpr ms 1).
  change (ms_gpr (wrom ms r) 3) with (ms_gpr ms 3).
  apply check_newfstatat_ext.
  - rewrite in_mem_sys_input. apply mem_ext_read_byte_wrom. exact Hrr.
  - rewrite in_mem_sys_input. exact Hnf.
Qed.

(** An ioctl node with a terminal-only request (json-c's own). *)
Lemma ioctl_tty_rob : forall ms model x8,
  ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 29%Z ->
  tty_only_request (cmd32 (ms_gpr ms 1)) = true ->
  sys_rob segs (mkCfg ms model).
Proof.
  intros ms model x8 Hs Hno Ht.
  apply sys_rob_of_check. intros r x8' Hrr Hs' v eff. rewrite Hs in Hs'. injection Hs' as <-.
  rewrite !(check_syscall_29_ioctl segs _ x8 eff (with_vdso v model) Hno).
  change (ms_gpr (wrom ms r) 0) with (ms_gpr ms 0). change (ms_gpr (wrom ms r) 1) with (ms_gpr ms 1).
  unfold check_ioctl. rewrite Ht.
  destruct (fd_lookup (m_fds (with_vdso v model)) (fd32 (ms_gpr ms 0))) as [[]|]; reflexivity.
Qed.

(* json-c's own: a writev node to a channel whose iovec array and buffers read in full (the check reads
   [in_mem] only through those reads, [RomWritev.check_writev_chan_ext]); with_vdso leaves the descriptor
   table as it is *)
Lemma check_syscall_66_writev : forall ms x8 eff m, bv_unsigned x8 = 66%Z ->
  check_syscall (sys_input segs ms x8) eff m
  = check_writev (sys_input segs ms x8) (fd32 (ms_gpr ms 0)) (ms_gpr ms 1) (ms_gpr ms 2) eff m.
Proof.
  intros ms x8 eff m Hno. unfold check_syscall.
  change (in_sysno (sys_input segs ms x8)) with x8. rewrite Hno. reflexivity.
Qed.

Lemma writev_rob : forall ms model x8 ch iovs bs,
  ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 66%Z ->
  fd_lookup (m_fds model) (fd32 (ms_gpr ms 0)) = Some (FdChannel ch) ->
  import_iovecs (ms_read_byte ms) (ms_gpr ms 1) (iovcnt32 (ms_gpr ms 2)) = ImpOk iovs ->
  gather_iovecs (ms_read_byte ms) (cap_iovecs iovs) = Some bs ->
  sys_rob segs (mkCfg ms model).
Proof.
  intros ms model x8 ch iovs bs Hs Hno Hfd Himp Hg.
  apply sys_rob_of_check. intros r x8' Hr Hs' v eff. cbn [cfg_ms] in Hs'.
  rewrite Hs in Hs'. injection Hs' as <-.
  rewrite (check_syscall_66_writev (wrom ms r) x8 eff (with_vdso v model) Hno).
  rewrite (check_syscall_66_writev ms x8 eff (with_vdso v model) Hno).
  rewrite sys_input_wrom.
  change (ms_gpr (wrom ms r) 0) with (ms_gpr ms 0).
  change (ms_gpr (wrom ms r) 1) with (ms_gpr ms 1).
  change (ms_gpr (wrom ms r) 2) with (ms_gpr ms 2).
  apply (RomWritev.check_writev_chan_ext _ _ _ _ _ eff (with_vdso v model) ch iovs bs Hfd).
  - rewrite in_mem_sys_input. apply mem_ext_read_byte_wrom. exact Hr.
  - rewrite in_mem_sys_input. exact Himp.
  - rewrite in_mem_sys_input. exact Hg.
Qed.
End Seg.
