(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made for this tree's Info layer from projects/leptonica/bilateral_fuzzer/proofs/lib/Common/Cfg/RomWrite.v as in the LPS 727298f3 update, lines 51-63 and 125-141 (check_openat_ext and openat_rob: RomBase.sys_rob for openat (56) over a larger read-only backing), with check_syscall_56 copied from projects/skcms/iccprofile_info/proofs/lib/Asan/FileSim.v at theorem-labs/oss-verify-proofs@f92feaf8b7e6, lines 976-984. *)
(* Theorem Labs, 2026-11 (LPS 08b1429): [RomBase.sys_rob] for openat (56), the memory-reading
   system call of the walks besides writev and ioctl ([RomWritev]).  The check reads
   [in_mem] only through reads that succeed at the node ([read_cstr] and
   [cstr_access_len_aux] over the path), so a larger backing answers it the same
   way. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import Prelude.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import CatSim FileSim RomBase.
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

(** [Asan/FileSim.check_syscall_56]; Info's FileSim has no copy. *)
Lemma check_syscall_56 : forall segs ms x8 eff m,
  bv_unsigned x8 = 56%Z ->
  check_syscall (sys_input segs ms x8) eff m
  = check_openat (sys_input segs ms x8) (fd32 (ms_gpr ms 0)) (ms_gpr ms 1)
                 (ms_gpr ms 2) eff m.
Proof.
  intros segs ms x8 eff m Hno.
  unfold check_syscall. rewrite in_sysno_si, Hno. reflexivity.
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
End Seg.
