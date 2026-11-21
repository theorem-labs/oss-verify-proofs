(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: added for LPS 727298f3: the system-call check of openat over a larger read-only backing ([RomBase.sys_rob]), with the openat dispatch lemma check_syscall_56 of openssl/ct's VCommon/FileSim.v restated over this file's segment list as check_syscall_56_rob. *)
(* Theorem Labs, 2026-11 (LPS 08b1429): [RomBase.sys_rob] for openat (56).  The openat half of
   openssl/punycode's [Common/Cfg/RomWrite.v], as copied into openssl/ct's
   [VCommon/Cfg/RomWrite.v]; this tree's walks have no write node, and its [VCommon.FileSim]
   has no [check_syscall_56], so the dispatch fact is stated here.  openat reads [in_mem] only
   through the path ([read_cstr] in [check_openat_body] and the copy-in record
   [cstr_access_len_aux]), so a path read that does not fault reads the same over a larger
   backing. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From OSSVerify.Proofs.openssl.bignum.lib.VCommon Require Import SimInv CatSim FileSim.
From OSSVerify.Proofs.openssl.bignum.lib.VCommon.Cfg Require Import RomBase.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

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

Lemma check_syscall_56_rob : forall ms x8 eff m,
  bv_unsigned x8 = 56%Z ->
  check_syscall (sys_input segs ms x8) eff m
  = check_openat (sys_input segs ms x8) (fd32 (ms_gpr ms 0)) (ms_gpr ms 1) (ms_gpr ms 2) eff m.
Proof.
  intros ms x8 eff m Hno.
  unfold check_syscall. rewrite in_sysno_si, Hno. reflexivity.
Qed.

(** An openat node whose path read does not fault. *)
Lemma openat_rob : forall ms model x8,
  ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 56%Z ->
  read_cstr (ms_read_byte ms) (ms_gpr ms 1) <> CstrFault ->
  sys_rob segs (mkCfg ms model).
Proof.
  intros ms model x8 Hs Hno Hnf.
  apply sys_rob_of_check. intros r x8' Hrr Hs' eff. rewrite Hs in Hs'. injection Hs' as <-.
  rewrite !(check_syscall_56_rob _ x8 eff model Hno).
  rewrite sys_input_wrom.
  change (ms_gpr (wrom ms r) 0) with (ms_gpr ms 0). change (ms_gpr (wrom ms r) 1) with (ms_gpr ms 1).
  change (ms_gpr (wrom ms r) 2) with (ms_gpr ms 2).
  apply check_openat_ext.
  - rewrite in_mem_si. apply mem_ext_read_byte_wrom. exact Hrr.
  - rewrite in_mem_si. exact Hnf.
Qed.
End Seg.
