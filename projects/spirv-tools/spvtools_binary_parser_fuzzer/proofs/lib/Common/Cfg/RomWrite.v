(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from bzip2/bzip2_compress_target's Common/Cfg/RomWrite.v (its openat part, module paths renamed), with the same RomBase.sys_rob facts for ioctl's terminal requests and for writev to a channel, so the walks over the binary's own segments lift to the run's segment list. *)
(* [RomBase.sys_rob] for the memory-reading system calls of this tree's walks: openat (56),
   ioctl (29) with a terminal-only request, and writev (66) to a channel.  Each check reads
   [in_mem] only through reads that succeed at the node (the path: [read_cstr] and
   [cstr_access_len_aux]; the iovec array and the buffers: [RomWritev]), or not at all
   (ioctl's terminal arm), so a larger backing answers it the same way.  The dispatch lemmas
   [check_syscall_NN] are the model's own (Common/FileSim.v, whose theory this tree does not
   require), by the same conversion. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Common.Cfg Require Import RomBase RomWritev.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Local Lemma in_mem_sys_input : forall segs ms x8, in_mem (sys_input segs ms x8) = ms_read_byte ms.
Proof. reflexivity. Qed.

(** ** Dispatch *)

Lemma check_syscall_29 : forall segs ms x8 eff m,
  bv_unsigned x8 = 29%Z ->
  check_syscall (sys_input segs ms x8) eff m
  = check_ioctl (sys_input segs ms x8) (fd32 (ms_gpr ms 0)) (cmd32 (ms_gpr ms 1)) eff m.
Proof.
  intros segs ms x8 eff m Hno. unfold check_syscall.
  change (in_sysno (sys_input segs ms x8)) with x8. rewrite Hno. reflexivity.
Qed.

Lemma check_syscall_56 : forall segs ms x8 eff m,
  bv_unsigned x8 = 56%Z ->
  check_syscall (sys_input segs ms x8) eff m
  = check_openat (sys_input segs ms x8) (fd32 (ms_gpr ms 0)) (ms_gpr ms 1)
                 (ms_gpr ms 2) eff m.
Proof.
  intros segs ms x8 eff m Hno. unfold check_syscall.
  change (in_sysno (sys_input segs ms x8)) with x8. rewrite Hno. reflexivity.
Qed.

Lemma check_syscall_66 : forall segs ms x8 eff m,
  bv_unsigned x8 = 66%Z ->
  check_syscall (sys_input segs ms x8) eff m
  = check_writev (sys_input segs ms x8) (fd32 (ms_gpr ms 0)) (ms_gpr ms 1)
                 (ms_gpr ms 2) eff m.
Proof.
  intros segs ms x8 eff m Hno. unfold check_syscall.
  change (in_sysno (sys_input segs ms x8)) with x8. rewrite Hno. reflexivity.
Qed.

(** ** The checks over a larger view *)

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

(** ioctl reads the input only on a datagram socket past the terminal requests
    ([check_siocgifindex]); a terminal-only request answers every fd without it. *)
Lemma check_ioctl_tty_ext : forall i mp' fd req eff m,
  tty_only_request req = true ->
  check_ioctl (with_mem i mp') fd req eff m = check_ioctl i fd req eff m.
Proof.
  intros i mp' fd req eff m Ht. unfold check_ioctl.
  (* decide the terminal-request test before comparing the two sides: on the datagram arm the
     other branch is [check_siocgifindex], which reads the input, and comparing it there does
     not terminate in reasonable time *)
  rewrite !Ht.
  destruct (fd_lookup (m_fds m) fd) as [[]|]; lazy beta iota; reflexivity.
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
  apply sys_rob_of_check. intros r x8' Hrr Hs' eff. rewrite Hs in Hs'. injection Hs' as <-.
  rewrite !(check_syscall_56 segs _ x8 eff model Hno).
  rewrite sys_input_wrom.
  change (ms_gpr (wrom ms r) 0) with (ms_gpr ms 0). change (ms_gpr (wrom ms r) 1) with (ms_gpr ms 1).
  change (ms_gpr (wrom ms r) 2) with (ms_gpr ms 2).
  apply check_openat_ext.
  - rewrite in_mem_sys_input. apply mem_ext_read_byte_wrom. exact Hrr.
  - rewrite in_mem_sys_input. exact Hnf.
Qed.

(** An ioctl node whose request is a terminal-only one (TIOCGWINSZ among them). *)
Lemma ioctl_tty_rob : forall ms model x8,
  ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 29%Z ->
  tty_only_request (cmd32 (ms_gpr ms 1)) = true ->
  sys_rob segs (mkCfg ms model).
Proof.
  intros ms model x8 Hs Hno Ht.
  apply sys_rob_of_check. intros r x8' Hrr Hs' eff. rewrite Hs in Hs'. injection Hs' as <-.
  rewrite !(check_syscall_29 segs _ x8 eff model Hno).
  rewrite sys_input_wrom.
  change (ms_gpr (wrom ms r) 0) with (ms_gpr ms 0). change (ms_gpr (wrom ms r) 1) with (ms_gpr ms 1).
  apply check_ioctl_tty_ext. exact Ht.
Qed.

(** A writev node to a channel whose iovec array and buffers read in full. *)
Lemma writev_rob : forall ms model x8 ch iovs bs,
  ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 66%Z ->
  fd_lookup (m_fds model) (fd32 (ms_gpr ms 0)) = Some (FdChannel ch) ->
  import_iovecs (ms_read_byte ms) (ms_gpr ms 1) (iovcnt32 (ms_gpr ms 2)) = ImpOk iovs ->
  gather_iovecs (ms_read_byte ms) (cap_iovecs iovs) = Some bs ->
  sys_rob segs (mkCfg ms model).
Proof.
  intros ms model x8 ch iovs bs Hs Hno Hfd Himp Hg.
  apply sys_rob_of_check. intros r x8' Hrr Hs' eff. rewrite Hs in Hs'. injection Hs' as <-.
  rewrite !(check_syscall_66 segs _ x8 eff model Hno).
  rewrite sys_input_wrom.
  change (ms_gpr (wrom ms r) 0) with (ms_gpr ms 0). change (ms_gpr (wrom ms r) 1) with (ms_gpr ms 1).
  change (ms_gpr (wrom ms r) 2) with (ms_gpr ms 2).
  apply (check_writev_chan_ext _ _ _ _ _ eff model ch iovs bs Hfd).
  - rewrite in_mem_sys_input. apply mem_ext_read_byte_wrom. exact Hrr.
  - rewrite in_mem_sys_input. exact Himp.
  - rewrite in_mem_sys_input. exact Hg.
Qed.
End Seg.
