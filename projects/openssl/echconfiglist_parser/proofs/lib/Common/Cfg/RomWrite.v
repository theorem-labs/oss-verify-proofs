(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: added for LPS 727298f3 from leptonica's Common/Cfg/RomWrite.v (the same text in each leptonica unit), with this unit's module paths; it restates the premise lists of Common/CatSim's write lemmas write1_ok_n and write1_ok_inv for the system-call checks of write and openat over a larger read-only backing ([RomBase.sys_rob]). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/pem/lib/Common/Cfg/RomWrite.v, its openat part only, with its module paths and numbers changed, check_syscall_56 proved here and a terminal-ioctl check added; 31 of its 66 lines of code are new or changed and 79 lines of the source are left out; taken from projects/openssl/pem/proofs/lib/Common/Cfg/RomWrite.v, lines 10-13, 15-17, 54-66, 75, 123-137 and 140-141, as in the LPS 727298f3 update. *)
(* Theorem Labs, 2026-11 (LPS 08b1429): [RomBase.sys_rob] for openat (56) and for a terminal
   ioctl (29).  The openat part is openssl/pem's [Common/Cfg/RomWrite.v] with [check_syscall_56] proved here; the ioctl part is pem's
   [Lib/Nodes.ioctl_tty_rob_any] stated for any pending number 29.  Each check reads [in_mem] only
   through reads that succeed at the node, so a larger backing answers them the same way. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Common.Cfg Require Import RomBase.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

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

Section Seg.
Variable segs : list Segment.

Lemma check_syscall_56 : forall ms x8 eff m,
  bv_unsigned x8 = 56%Z ->
  check_syscall (sys_input segs ms x8) eff m
  = check_openat (sys_input segs ms x8) (fd32 (ms_gpr ms 0)) (ms_gpr ms 1) (ms_gpr ms 2) eff m.
Proof.
  intros ms x8 eff m Hno. unfold check_syscall.
  change (in_sysno (sys_input segs ms x8)) with x8. rewrite Hno. reflexivity.
Qed.

(** An openat node whose path read does not fault. *)
Lemma openat_rob : forall ms model x8,
  ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 56%Z ->
  read_cstr (ms_read_byte ms) (ms_gpr ms 1) <> CstrFault ->
  sys_rob segs (mkCfg ms model).
Proof.
  intros ms model x8 Hs Hno Hnf.
  apply sys_rob_of_check. intros r x8' Hrr Hs' eff. rewrite Hs in Hs'. injection Hs' as <-.
  rewrite !(check_syscall_56 _ x8 eff model Hno).
  rewrite sys_input_wrom.
  change (ms_gpr (wrom ms r) 0) with (ms_gpr ms 0). change (ms_gpr (wrom ms r) 1) with (ms_gpr ms 1).
  change (ms_gpr (wrom ms r) 2) with (ms_gpr ms 2).
  apply check_openat_ext.
  - change (in_mem (sys_input segs ms x8)) with (ms_read_byte ms).
    apply mem_ext_read_byte_wrom. exact Hrr.
  - change (in_mem (sys_input segs ms x8)) with (ms_read_byte ms). exact Hnf.
Qed.

Lemma check_syscall_29 : forall ms x8 eff m,
  bv_unsigned x8 = 29%Z ->
  check_syscall (sys_input segs ms x8) eff m
  = check_ioctl (sys_input segs ms x8) (fd32 (ms_gpr ms 0)) (cmd32 (ms_gpr ms 1)) eff m.
Proof.
  intros ms x8 eff m Hno. unfold check_syscall.
  change (in_sysno (sys_input segs ms x8)) with x8. rewrite Hno. reflexivity.
Qed.

(** [check_ioctl] reads the input only for SIOCGIFINDEX on a datagram socket, after
    [tty_only_request] fails; TIOCGWINSZ (0x5413) is a terminal-only request, so the check is the
    same over a larger backing on every fd kind. *)
Lemma ioctl_tty_rob : forall ms model x8,
  ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 29%Z ->
  ms_gpr ms 1 = Z_to_bv 64 21523 ->
  sys_rob segs (mkCfg ms model).
Proof.
  intros ms model x8 Hs Hno H11. apply sys_rob_of_check. intros r x8' Hr Hs' eff.
  rewrite Hs in Hs'. injection Hs' as <-.
  rewrite !(check_syscall_29 _ x8 eff model Hno).
  change (ms_gpr (wrom ms r) 0) with (ms_gpr ms 0).
  change (ms_gpr (wrom ms r) 1) with (ms_gpr ms 1).
  rewrite H11.
  (* decide the terminal-request test first: on the [FdDgram] arm the other branch is
     [check_siocgifindex], which READS the input, and comparing the two sides there does not
     terminate (the hang openssl/hashtable's RomWritev.v met there). *)
  assert (Htty : tty_only_request (cmd32 (Z_to_bv 64 21523)) = true) by (vm_compute; reflexivity).
  (* and reduce the decided [if] before comparing, so no arm keeps a [check_siocgifindex] *)
  unfold check_ioctl. rewrite !Htty. destruct (fd_lookup _ _) as [[]|]; lazy beta iota; reflexivity.
Qed.
End Seg.
