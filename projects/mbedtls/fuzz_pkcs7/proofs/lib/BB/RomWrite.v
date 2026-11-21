(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: new file, the sys_rob lemmas for write to a channel and for openat, copied from the openssl pem unit's Common/Cfg/RomWrite.v with only its Require lines pointed at this unit's own library. *)
(* Copied (statement and proof) from the openssl/pem unit's
   Common/Cfg/RomWrite.v:1-138; only the Require lines changed,
   to this tree's BB copies of SimInv/CatSim/FileSim. *)
(* Theorem Labs, 2026-11 (LPS 08b1429): [RomBase.sys_rob] for write (64) to a channel and for
   openat (56), the memory-reading system calls of the leptonica chains besides writev and
   ioctl ([RomWritev]).  Each check reads [in_mem] only through reads that succeed at the
   node ([write_source] over the named range under the transfer cap; [read_cstr] and
   [cstr_access_len_aux] over the path), so a larger backing answers them the same way. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Common Require Import SimInv.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.BB Require Import CatSim FileSim.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Common.Cfg Require Import RomBase.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Lemma read_bytes_aux_ext : forall n mp mp' a bs,
  mem_ext mp mp' -> read_bytes_aux mp a n = Some bs -> read_bytes_aux mp' a n = Some bs.
Proof.
  induction n as [|n IH]; intros mp mp' a bs Hx H; [exact H|].
  cbn [read_bytes_aux] in *.
  destruct (mp a) as [b|] eqn:E; [|discriminate H].
  rewrite (Hx a b E).
  destruct (read_bytes_aux mp (a + 1) n) as [rs|] eqn:E2; [|discriminate H].
  rewrite (IH mp mp' (a + 1) rs Hx E2). exact H.
Qed.

Lemma read_bytes_map_ext : forall mp mp' a len bs,
  mem_ext mp mp' -> read_bytes_map mp a len = Some bs -> read_bytes_map mp' a len = Some bs.
Proof. intros mp mp' a len bs Hx. rewrite !read_bytes_map_eq. apply read_bytes_aux_ext. exact Hx. Qed.

(** write's channel arm reads [in_mem] only through [write_source]; under the transfer cap that
    is the whole named range, the same on any view extending one that reads it. *)
Lemma check_write_chan_ext : forall i mp' fd buf count eff m ch bs,
  fd_lookup (m_fds m) fd = Some (FdChannel ch) ->
  (bv_unsigned count <= rw_bytes_max)%Z ->
  read_bytes_map (in_mem i) buf count = Some bs ->
  mem_ext (in_mem i) mp' ->
  check_write (with_mem i mp') fd buf count eff m = check_write i fd buf count eff m.
Proof.
  intros i mp' fd buf count eff m ch bs Hfd Hcw Hr Hx.
  unfold check_write. rewrite Hfd. cbv beta iota.
  unfold with_mem. cbn [in_mem].
  rewrite (write_source_of_rw mp' buf count Hcw), (write_source_of_rw (in_mem i) buf count Hcw).
  rewrite (readable_bytes_full _ _ _ _ Hr), (readable_bytes_full _ _ _ _ (read_bytes_map_ext _ _ _ _ _ Hx Hr)).
  reflexivity.
Qed.

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

(** A write node to a channel whose named range reads in full. *)
Lemma write_rob : forall ms model x8 ch buf,
  ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 64%Z ->
  fd_lookup (m_fds model) (fd32 (ms_gpr ms 0)) = Some (FdChannel ch) ->
  (bv_unsigned (ms_gpr ms 2) <= rw_bytes_max)%Z ->
  ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = Some buf ->
  sys_rob segs (mkCfg ms model).
Proof.
  intros ms model x8 ch buf Hs Hno Hfd Hcw Hr.
  apply sys_rob_of_check. intros r x8' Hrr Hs' eff. rewrite Hs in Hs'. injection Hs' as <-.
  rewrite !(check_syscall_64 segs _ x8 eff model Hno).
  rewrite sys_input_wrom.
  change (ms_gpr (wrom ms r) 0) with (ms_gpr ms 0). change (ms_gpr (wrom ms r) 1) with (ms_gpr ms 1).
  change (ms_gpr (wrom ms r) 2) with (ms_gpr ms 2).
  apply (check_write_chan_ext _ _ _ _ _ eff model ch buf Hfd Hcw).
  - rewrite in_mem_sys_input, read_bytes_map_read_byte. exact Hr.
  - rewrite in_mem_sys_input. apply mem_ext_read_byte_wrom. exact Hrr.
Qed.

(** [write_rob] from the premises of the leptonica write-to-stdout nodes. *)
Lemma write1_rob : forall ms model x8 buf,
  fd1chan model -> ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 64%Z ->
  ms_gpr ms 0 = Z_to_bv 64 1 ->
  ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = Some buf ->
  buf_modeled buf ->
  sys_rob segs (mkCfg ms model).
Proof.
  intros ms model x8 buf Hfd Hs Hno Hg Hr Hbm.
  unfold fd1chan in Hfd. destruct Hfd as [Hfd _].
  assert (Hrb : read_bytes_map (in_mem (sys_input segs ms x8)) (ms_gpr ms 1) (ms_gpr ms 2) = Some buf)
    by (rewrite in_mem_sys_input, read_bytes_map_read_byte; exact Hr).
  pose proof (read_bytes_map_length _ _ _ _ Hrb) as Hlen.
  pose proof (word_unsigned_range (ms_gpr ms 2)) as Hcr.
  assert (Hcw : (bv_unsigned (ms_gpr ms 2) <= rw_bytes_max)%Z) by (unfold buf_modeled in Hbm; lia).
  apply (write_rob ms model x8 (Z_to_bv 64 1) buf Hs Hno); [| exact Hcw | exact Hr].
  rewrite Hg. norm_fd32. exact Hfd.
Qed.

(** [write_rob] from the premises of the general channel write node ([fdchan]). *)
Lemma write_ch_rob : forall ms model x8 fd ch buf,
  fdchan fd ch model -> fd32 fd = fd -> ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 64%Z ->
  ms_gpr ms 0 = fd ->
  ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = Some buf ->
  buf_modeled buf ->
  sys_rob segs (mkCfg ms model).
Proof.
  intros ms model x8 fd ch buf Hfdc H32 Hs Hno Hg Hr Hbm.
  unfold fdchan in Hfdc. destruct Hfdc as [Hfd _].
  assert (Hrb : read_bytes_map (in_mem (sys_input segs ms x8)) (ms_gpr ms 1) (ms_gpr ms 2) = Some buf)
    by (rewrite in_mem_sys_input, read_bytes_map_read_byte; exact Hr).
  pose proof (read_bytes_map_length _ _ _ _ Hrb) as Hlen.
  pose proof (word_unsigned_range (ms_gpr ms 2)) as Hcr.
  assert (Hcw : (bv_unsigned (ms_gpr ms 2) <= rw_bytes_max)%Z) by (unfold buf_modeled in Hbm; lia).
  apply (write_rob ms model x8 ch buf Hs Hno); [| exact Hcw | exact Hr].
  rewrite Hg, H32. exact Hfd.
Qed.

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
