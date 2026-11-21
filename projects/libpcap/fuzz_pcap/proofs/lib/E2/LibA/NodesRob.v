(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: the premise lists of CatSim's write lemmas restated for the system-call checks of write and openat over a larger read-only backing ([RomBase.sys_rob]). *)
(* Modified by Theorem Labs, 2026-11: made from bzip2/bzip2_compress_target's Common/Cfg/RomWrite.v and Common/Cfg/RomWritev.v with this unit's module paths, as [RomBase.sys_rob] at every node [at_nodeA] admits, extended to every descriptor arm of write, writev and readv; taken from projects/bzip2/bzip2_compress_target/proofs/lib/Common/Cfg/RomWrite.v, lines 12-19, 27-34, 45-81, 91, 100, 110-117 and 127 and projects/bzip2/bzip2_compress_target/proofs/lib/Common/Cfg/RomWritev.v, lines 11, 14-30, 33-40, 43-51, 54-63, 77-123, 127-132 and 134-138, as in the LPS 727298f3 update. *)
(* Theorem Labs, 2026-11 (LPS 727298f3): [RomBase.sys_rob] at every node [at_nodeA] admits, the
   [nsA_rob] field of [ITreeA.node_soundA].  Adapted from bzip2/bzip2_compress_target's
   Common/Cfg/RomWrite.v and Common/Cfg/RomWritev.v (namespaces changed), extended to every
   descriptor arm, because the field quantifies over every model and so gives no fd facts.

   A node's check reads [in_mem] only through reads that succeed at the node ([at_node] names
   defined bytes with [ms_rom ms = seg_rom segs]), so a larger view answers them the same way:
   - write (64): [write_source] in most arms, a readable prefix of the named range in the
     stream arm ([check_stream_write]), its first 8 bytes in the eventfd arm;
   - writev (66): [import_iovecs], [import_iovecs_accesses] and [writev_gathered];
   - readv (65): [import_iovecs] and [import_iovecs_accesses]; the delivery reads [in_wmem];
   - openat (56), unlinkat (35): the path ([read_cstr], [cstr_access_len_aux]);
   - ioctl (29): TIOCGWINSZ is terminal-only, and the one arm that reads memory
     (SIOCGIFINDEX on a datagram socket) follows a failed [tty_only_request];
   - every other node's number reads no memory ([RomBase.memfree_NN]). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState Mem Nodes.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import NodesA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require Import RomBase.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

(** ** The dispatch of the memory-reading numbers, for any input *)
Lemma rob_dispatch_29 : forall i eff m, bv_unsigned (in_sysno i) = 29 ->
  check_syscall i eff m = check_ioctl i (fd32 (in_arg i 0)) (cmd32 (in_arg i 1)) eff m.
Proof. intros i eff m H. unfold check_syscall. rewrite H. reflexivity. Qed.

Lemma rob_dispatch_35 : forall i eff m, bv_unsigned (in_sysno i) = 35 ->
  check_syscall i eff m = check_unlinkat i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) eff m.
Proof. intros i eff m H. unfold check_syscall. rewrite H. reflexivity. Qed.

Lemma rob_dispatch_56 : forall i eff m, bv_unsigned (in_sysno i) = 56 ->
  check_syscall i eff m = check_openat i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) eff m.
Proof. intros i eff m H. unfold check_syscall. rewrite H. reflexivity. Qed.

Lemma rob_dispatch_64 : forall i eff m, bv_unsigned (in_sysno i) = 64 ->
  check_syscall i eff m = check_write i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) eff m.
Proof. intros i eff m H. unfold check_syscall. rewrite H. reflexivity. Qed.

Lemma rob_dispatch_65 : forall i eff m, bv_unsigned (in_sysno i) = 65 ->
  check_syscall i eff m = check_readv i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) eff m.
Proof. intros i eff m H. unfold check_syscall. rewrite H. reflexivity. Qed.

Lemma rob_dispatch_66 : forall i eff m, bv_unsigned (in_sysno i) = 66 ->
  check_syscall i eff m = check_writev i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) eff m.
Proof. intros i eff m H. unfold check_syscall. rewrite H. reflexivity. Qed.

(** ** Prefixes of a read that succeeds

    A read of [k] bytes that succeeds on [mp] answers every shorter read, and every readable
    prefix of at most [k] bytes, the same way on a view that extends [mp]. *)
Lemma read_bytes_aux_ext_le : forall k mp mp' a bs j, mem_ext mp mp' ->
  read_bytes_aux mp a k = Some bs -> (j <= k)%nat ->
  read_bytes_aux mp' a j = read_bytes_aux mp a j.
Proof.
  induction k as [|k IH]; intros mp mp' a bs j Hx H Hj.
  - assert (Hj0 : j = 0%nat) by lia. subst j. reflexivity.
  - destruct j as [|j]; [reflexivity|].
    cbn [read_bytes_aux] in H.
    destruct (mp a) as [b|] eqn:E; [|discriminate H].
    lazymatch type of H with
    | context [read_bytes_aux mp ?a' k] =>
        destruct (read_bytes_aux mp a' k) as [r|] eqn:E2; [|discriminate H]
    end.
    cbn [read_bytes_aux]. rewrite E, (Hx a b E).
    rewrite (IH mp mp' _ r j Hx E2 ltac:(lia)). reflexivity.
Qed.

Lemma readable_bytes_aux_ext_le : forall k mp mp' a bs j, mem_ext mp mp' ->
  read_bytes_aux mp a k = Some bs -> (j <= k)%nat ->
  readable_bytes_aux mp' a j = readable_bytes_aux mp a j.
Proof.
  induction k as [|k IH]; intros mp mp' a bs j Hx H Hj.
  - assert (Hj0 : j = 0%nat) by lia. subst j. reflexivity.
  - destruct j as [|j]; [reflexivity|].
    cbn [read_bytes_aux] in H.
    destruct (mp a) as [b|] eqn:E; [|discriminate H].
    lazymatch type of H with
    | context [read_bytes_aux mp ?a' k] =>
        destruct (read_bytes_aux mp a' k) as [r|] eqn:E2; [|discriminate H]
    end.
    cbn [readable_bytes_aux]. rewrite E, (Hx a b E).
    rewrite (IH mp mp' _ r j Hx E2 ltac:(lia)). reflexivity.
Qed.

Lemma read_bytes_map_ext_le : forall mp mp' a len bs len', mem_ext mp mp' ->
  read_bytes_map mp a len = Some bs -> bv_unsigned len' <= bv_unsigned len ->
  read_bytes_map mp' a len' = read_bytes_map mp a len'.
Proof.
  intros mp mp' a len bs len' Hx Hr Hle.
  rewrite !read_bytes_map_eq. rewrite read_bytes_map_eq in Hr.
  apply (read_bytes_aux_ext_le (word_to_nat len) mp mp' a bs (word_to_nat len') Hx Hr).
  pose proof (bv_unsigned_in_range 64 len). pose proof (bv_unsigned_in_range 64 len').
  unfold word_to_nat. lia.
Qed.

Lemma readable_bytes_ext_le : forall mp mp' a len bs len', mem_ext mp mp' ->
  read_bytes_map mp a len = Some bs -> bv_unsigned len' <= bv_unsigned len ->
  readable_bytes mp' a len' = readable_bytes mp a len'.
Proof.
  intros mp mp' a len bs len' Hx Hr Hle.
  rewrite !readable_bytes_eq. rewrite read_bytes_map_eq in Hr.
  apply (readable_bytes_aux_ext_le (word_to_nat len) mp mp' a bs (word_to_nat len') Hx Hr).
  pose proof (bv_unsigned_in_range 64 len). pose proof (bv_unsigned_in_range 64 len').
  unfold word_to_nat. lia.
Qed.

(** [write_source] walks at most the named count ([rw_count_clamp]), with no cap needed. *)
Lemma write_source_ext : forall mp mp' buf count bs, mem_ext mp mp' ->
  read_bytes_map mp buf count = Some bs ->
  write_source mp' buf count = write_source mp buf count.
Proof.
  intros mp mp' buf count bs Hx Hr. unfold write_source.
  apply (readable_bytes_ext_le mp mp' buf count bs _ Hx Hr).
  rewrite rw_count_clamp_word. unfold rw_count_clamp. apply Z.le_min_l.
Qed.

(** ** write (64), every descriptor arm *)

(** [check_stream_send] reads its source only at [Z.min n (s + s / 2 - q)], past the zero
    count and the full queue, which is between 1 and [n]. *)
Lemma check_stream_send_src_ext : forall id side st nb ns n src1 src2 ledger eff m,
  0 <= n ->
  (forall c, 1 <= c <= n -> src1 c = src2 c) ->
  check_stream_send id side st nb ns n src1 ledger eff m
  = check_stream_send id side st nb ns n src2 ledger eff m.
Proof.
  intros id side st nb ns n src1 src2 ledger eff m Hn Hsrc.
  unfold check_stream_send. cbv zeta.
  destruct (stream_peer (m_fds m) id side) as [[pfd pst]|]; cbv beta iota; [|reflexivity].
  destruct (se_shut_wr st); cbv beta iota; [reflexivity|].
  destruct (Z.eqb n 0) eqn:En; cbv beta iota; [reflexivity|].
  destruct (stream_send_full (se_rx_len pst) (se_sndbuf st)) eqn:Ef; cbv beta iota; [reflexivity|].
  apply Z.eqb_neq in En. unfold stream_send_full in Ef. apply Z.leb_gt in Ef.
  assert (Hq : 0 <= se_rx_len pst) by (unfold se_rx_len; lia).
  assert (Hs2 : 0 <= se_sndbuf st / 2) by (apply Z.div_pos; lia).
  lazymatch goal with
  | |- context [src1 ?c] => rewrite (Hsrc c) by lia
  end.
  reflexivity.
Qed.

(** The stream arm's source is a readable prefix of at most the named count. *)
Lemma check_stream_write_ext : forall i mp' buf count bs, mem_ext (in_mem i) mp' ->
  read_bytes_map (in_mem i) buf count = Some bs ->
  forall id side st nb ns eff m,
  check_stream_write id side st nb ns buf count (with_mem i mp') eff m
  = check_stream_write id side st nb ns buf count i eff m.
Proof.
  intros i mp' buf count bs Hx Hr id side st nb ns eff m.
  unfold check_stream_write.
  apply check_stream_send_src_ext; [exact (proj1 (rw_count_clamp_range count))|].
  intros c Hc. cbv beta. change (in_mem (with_mem i mp')) with mp'.
  apply (readable_bytes_ext_le _ _ _ _ _ _ Hx Hr).
  pose proof (rw_count_clamp_range count) as Hcr.
  assert (Hcl : rw_count_clamp count <= bv_unsigned count) by (unfold rw_count_clamp; apply Z.le_min_l).
  unfold MAX_RW_COUNT in Hcr.
  rewrite unsigned_lit by lia. lia.
Qed.

(** The eventfd arm reads the first 8 bytes, and only once the count is 8. *)
Lemma check_eventfd_write_ext : forall i mp' buf count bs, mem_ext (in_mem i) mp' ->
  read_bytes_map (in_mem i) buf count = Some bs ->
  forall fd ctx eff m,
  check_eventfd_write fd ctx buf count (with_mem i mp') eff m
  = check_eventfd_write fd ctx buf count i eff m.
Proof.
  intros i mp' buf count bs Hx Hr fd ctx eff m.
  unfold check_eventfd_write. change (in_mem (with_mem i mp')) with mp'.
  destruct (Z.eqb (rw_count_clamp count) 8) eqn:E8; [|reflexivity].
  apply Z.eqb_eq in E8. unfold rw_count_clamp, MAX_RW_COUNT in E8.
  unfold copy_bytes_map.
  rewrite (read_bytes_map_ext_le _ _ _ _ _ (Z_to_bv 64 8) Hx Hr) by (rewrite unsigned_lit by lia; lia).
  reflexivity.
Qed.

Lemma check_write_ext : forall i mp' fd buf count eff m bs,
  mem_ext (in_mem i) mp' -> read_bytes_map (in_mem i) buf count = Some bs ->
  check_write (with_mem i mp') fd buf count eff m = check_write i fd buf count eff m.
Proof.
  intros i mp' fd buf count eff m bs Hx Hr.
  unfold check_write. change (in_mem (with_mem i mp')) with mp'.
  rewrite (write_source_ext _ _ _ _ _ Hx Hr).
  destruct (fd_lookup (m_fds m) fd) as [[]|]; cbv beta iota;
    first
      [ rewrite (check_stream_write_ext i mp' buf count bs Hx Hr); reflexivity
      | rewrite (check_eventfd_write_ext i mp' buf count bs Hx Hr); reflexivity
      | reflexivity ].
Qed.

(** ** writev (66) and readv (65): the iovec array and the buffers

    As bzip2's [RomWritev] (from openssl/hashtable's): a read that succeeds on a view returns
    the same bytes on any view that extends it, and the copy-in record reads only the
    entries' own words. *)
Lemma read_u64_ext : forall mp mp' a v, mem_ext mp mp' ->
  read_u64 mp a = Some v -> read_u64 mp' a = Some v.
Proof.
  intros mp mp' a v Hx. unfold read_u64.
  destruct (read_bytes_map mp a (Z_to_bv 64 8)) as [bs|] eqn:E; [|intro H; discriminate H].
  rewrite (read_bytes_map_ext mp mp' a _ bs Hx E). intro H; exact H.
Qed.

Lemma read_iovec_entry_ext : forall mp mp' a b n, mem_ext mp mp' ->
  read_iovec_entry mp a = IovEntry b n -> read_iovec_entry mp' a = IovEntry b n.
Proof.
  intros mp mp' a b n Hx. unfold read_iovec_entry.
  destruct (read_u64 mp a) as [v1|] eqn:E1; [|intro H; discriminate H].
  lazymatch goal with
  | |- context [read_u64 mp ?a8] => destruct (read_u64 mp a8) as [v2|] eqn:E2; [|intro H; discriminate H]
  end.
  rewrite (read_u64_ext mp mp' a v1 Hx E1), (read_u64_ext mp mp' _ v2 Hx E2). intro H; exact H.
Qed.

Lemma iovec_entry_accesses_ext : forall mp mp' a b n, mem_ext mp mp' ->
  read_iovec_entry mp a = IovEntry b n ->
  iovec_entry_accesses mp' a = iovec_entry_accesses mp a.
Proof.
  intros mp mp' a b n Hx. unfold read_iovec_entry, iovec_entry_accesses.
  destruct (read_u64 mp a) as [v1|] eqn:E1; [|intro H; discriminate H].
  lazymatch goal with
  | |- context [read_u64 mp ?a8] => destruct (read_u64 mp a8) as [v2|] eqn:E2; [|intro H; discriminate H]
  end.
  intros _. rewrite (read_u64_ext mp mp' a v1 Hx E1), (read_u64_ext mp mp' _ v2 Hx E2). reflexivity.
Qed.

Lemma copy_iovecs_aux_ext : forall k mp mp' a iovs, mem_ext mp mp' ->
  copy_iovecs_aux mp a k = ImpOk iovs -> copy_iovecs_aux mp' a k = ImpOk iovs.
Proof.
  induction k as [|k IH]; intros mp mp' a iovs Hx H; [exact H|].
  cbn [copy_iovecs_aux] in *.
  destruct (read_iovec_entry mp a) as [b n| |] eqn:E; try discriminate H.
  rewrite (read_iovec_entry_ext mp mp' a b n Hx E).
  lazymatch type of H with
  | context [copy_iovecs_aux mp ?a16 k] =>
      destruct (copy_iovecs_aux mp a16 k) as [rest| |] eqn:E2; try discriminate H
  end.
  rewrite (IH mp mp' _ rest Hx E2). exact H.
Qed.

Lemma copy_iovecs_accesses_ext : forall k mp mp' a iovs, mem_ext mp mp' ->
  copy_iovecs_aux mp a k = ImpOk iovs ->
  copy_iovecs_accesses mp' a k = copy_iovecs_accesses mp a k.
Proof.
  induction k as [|k IH]; intros mp mp' a iovs Hx H; [reflexivity|].
  cbn [copy_iovecs_aux copy_iovecs_accesses] in *.
  destruct (read_iovec_entry mp a) as [b n| |] eqn:E; try discriminate H.
  rewrite (iovec_entry_accesses_ext mp mp' a b n Hx E), (read_iovec_entry_ext mp mp' a b n Hx E).
  lazymatch type of H with
  | context [copy_iovecs_aux mp ?a16 k] =>
      destruct (copy_iovecs_aux mp a16 k) as [rest| |] eqn:E2; try discriminate H
  end.
  rewrite (IH mp mp' _ rest Hx E2). reflexivity.
Qed.

Lemma import_iovecs_ext : forall mp mp' a n iovs, mem_ext mp mp' ->
  import_iovecs mp a n = ImpOk iovs -> import_iovecs mp' a n = ImpOk iovs.
Proof.
  intros mp mp' a n iovs Hx. unfold import_iovecs.
  destruct (bv_eqb n (Z_to_bv 64 1)).
  - destruct (negb (access_okb a 16)); [intro H; exact H|].
    destruct (read_iovec_entry mp a) as [b l| |] eqn:E; try (intro H; discriminate H).
    rewrite (read_iovec_entry_ext mp mp' a b l Hx E). intro H; exact H.
  - destruct (bv_eqb n (Z_to_bv 64 0)); [intro H; exact H|].
    destruct (IOV_MAX <? bv_unsigned n)%Z; [intro H; exact H|].
    destruct (negb (access_okb a (16 * bv_unsigned n))); [intro H; exact H|].
    destruct (copy_iovecs_aux mp a (word_to_nat n)) as [l| |] eqn:E; try (intro H; discriminate H).
    rewrite (copy_iovecs_aux_ext _ mp mp' a l Hx E). intro H; exact H.
Qed.

Lemma import_iovecs_accesses_ext : forall mp mp' a n iovs, mem_ext mp mp' ->
  import_iovecs mp a n = ImpOk iovs ->
  import_iovecs_accesses mp' a n = import_iovecs_accesses mp a n.
Proof.
  intros mp mp' a n iovs Hx. unfold import_iovecs, import_iovecs_accesses.
  destruct (bv_eqb n (Z_to_bv 64 1)).
  - destruct (negb (access_okb a 16)); [intros _; reflexivity|].
    destruct (read_iovec_entry mp a) as [b l| |] eqn:E; try (intro H; discriminate H).
    intros _. exact (iovec_entry_accesses_ext mp mp' a b l Hx E).
  - destruct (bv_eqb n (Z_to_bv 64 0)); [intros _; reflexivity|].
    destruct (IOV_MAX <? bv_unsigned n)%Z; [intros _; reflexivity|].
    destruct (negb (access_okb a (16 * bv_unsigned n))); [intros _; reflexivity|].
    destruct (copy_iovecs_aux mp a (word_to_nat n)) as [l| |] eqn:E; try (intro H; discriminate H).
    intros _. exact (copy_iovecs_accesses_ext _ mp mp' a l Hx E).
Qed.

(** [writev_gathered]'s [gather_prefix] is the same on a larger view once every buffer reads
    in full. *)
Lemma gather_prefix_ext : forall iovs mp mp' bs, mem_ext mp mp' ->
  gather_iovecs mp iovs = Some bs -> gather_prefix mp' iovs = gather_prefix mp iovs.
Proof.
  induction iovs as [|[b n] r IH]; intros mp mp' bs Hx H; [reflexivity|].
  cbn [gather_iovecs] in H.
  destruct (read_bytes_map mp b n) as [x|] eqn:E; [|discriminate H].
  destruct (gather_iovecs mp r) as [y|] eqn:E2; [|discriminate H].
  cbn [gather_prefix].
  rewrite (readable_bytes_full _ _ _ _ E), (readable_bytes_full _ _ _ _ (read_bytes_map_ext _ _ _ _ _ Hx E)).
  rewrite (IH mp mp' y Hx E2). reflexivity.
Qed.

(** [check_writev] reads [in_mem] only through [import_iovecs], [import_iovecs_accesses] and
    [writev_gathered], on every descriptor kind (Checks/Sys/Fs/ReadWrite.v). *)
Lemma check_writev_ext : forall i mp' fd iov cnt eff m iovs bs,
  mem_ext (in_mem i) mp' ->
  import_iovecs (in_mem i) iov (iovcnt32 cnt) = ImpOk iovs ->
  gather_iovecs (in_mem i) (cap_iovecs iovs) = Some bs ->
  check_writev (with_mem i mp') fd iov cnt eff m = check_writev i fd iov cnt eff m.
Proof.
  intros i mp' fd iov cnt eff m iovs bs Hx Himp Hg.
  unfold check_writev. change (in_mem (with_mem i mp')) with mp'.
  rewrite (import_iovecs_ext _ _ _ _ _ Hx Himp), Himp.
  rewrite (import_iovecs_accesses_ext _ _ _ _ _ Hx Himp).
  (* reduce the decided import, so the gathered bytes are over [iovs] and under no binder *)
  cbv beta iota zeta.
  unfold writev_gathered. rewrite (gather_prefix_ext _ _ _ _ Hx Hg).
  reflexivity.
Qed.

(** readv reads [in_mem] only through the iovec array's import and its record; the delivery
    ([check_readv_imported]) reads only [in_wmem], the same field of both inputs. *)
Lemma check_readv_ext : forall i mp' fd iov cnt eff m iovs,
  mem_ext (in_mem i) mp' ->
  import_iovecs (in_mem i) iov (iovcnt32 cnt) = ImpOk iovs ->
  check_readv (with_mem i mp') fd iov cnt eff m = check_readv i fd iov cnt eff m.
Proof.
  intros i mp' fd iov cnt eff m iovs Hx Himp.
  unfold check_readv. change (in_mem (with_mem i mp')) with mp'.
  rewrite (import_iovecs_ext _ _ _ _ _ Hx Himp), Himp.
  rewrite (import_iovecs_accesses_ext _ _ _ _ _ Hx Himp).
  reflexivity.
Qed.

(** ** openat (56) and unlinkat (35): the path *)
Lemma check_openat_ext : forall i mp' dirfd pathp flags eff m,
  mem_ext (in_mem i) mp' -> read_cstr (in_mem i) pathp <> CstrFault ->
  check_openat (with_mem i mp') dirfd pathp flags eff m = check_openat i dirfd pathp flags eff m.
Proof.
  intros i mp' dirfd pathp flags eff m Hx Hnf.
  unfold check_openat, LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Fs.Open.check_openat_body.
  change (in_mem (with_mem i mp')) with mp'.
  rewrite (cstr_access_len_aux_ext path_max (in_mem i) mp' pathp Hx Hnf).
  rewrite (read_cstr_ext (in_mem i) mp' pathp Hx Hnf).
  reflexivity.
Qed.

Lemma check_unlinkat_ext : forall i mp' dirfd pathp flags eff m,
  mem_ext (in_mem i) mp' -> read_cstr (in_mem i) pathp <> CstrFault ->
  check_unlinkat (with_mem i mp') dirfd pathp flags eff m = check_unlinkat i dirfd pathp flags eff m.
Proof.
  intros i mp' dirfd pathp flags eff m Hx Hnf.
  unfold check_unlinkat, LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Fs.Namei.check_unlinkat_body.
  change (in_mem (with_mem i mp')) with mp'.
  rewrite (cstr_access_len_aux_ext path_max (in_mem i) mp' pathp Hx Hnf).
  rewrite (read_cstr_ext (in_mem i) mp' pathp Hx Hnf).
  reflexivity.
Qed.

(** ** ioctl (29): a terminal-only request reads no memory on any descriptor kind *)
Lemma check_ioctl_tty_ext : forall i mp fd req eff m,
  tty_only_request req = true ->
  check_ioctl (with_mem i mp) fd req eff m = check_ioctl i fd req eff m.
Proof.
  intros i mp fd req eff m Htty.
  (* decide the terminal-request test first and reduce the decided [if] before comparing, so
     no arm keeps a [check_siocgifindex] (which reads the input) *)
  unfold check_ioctl. rewrite Htty.
  destruct (fd_lookup (m_fds m) fd) as [[]|]; lazy beta iota; reflexivity.
Qed.

(** ** The checks, through the dispatch *)
Lemma check_syscall_write_ext : forall i mp eff m bs,
  bv_unsigned (in_sysno i) = 64 -> mem_ext (in_mem i) mp ->
  read_bytes_map (in_mem i) (in_arg i 1) (in_arg i 2) = Some bs ->
  check_syscall (with_mem i mp) eff m = check_syscall i eff m.
Proof.
  intros i mp eff m bs Hno Hx Hr.
  rewrite (rob_dispatch_64 (with_mem i mp) eff m Hno), (rob_dispatch_64 i eff m Hno).
  exact (check_write_ext i mp (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) eff m bs Hx Hr).
Qed.

Lemma check_syscall_writev_ext : forall i mp eff m iovs bs,
  bv_unsigned (in_sysno i) = 66 -> mem_ext (in_mem i) mp ->
  import_iovecs (in_mem i) (in_arg i 1) (iovcnt32 (in_arg i 2)) = ImpOk iovs ->
  gather_iovecs (in_mem i) (cap_iovecs iovs) = Some bs ->
  check_syscall (with_mem i mp) eff m = check_syscall i eff m.
Proof.
  intros i mp eff m iovs bs Hno Hx Himp Hg.
  rewrite (rob_dispatch_66 (with_mem i mp) eff m Hno), (rob_dispatch_66 i eff m Hno).
  exact (check_writev_ext i mp (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) eff m iovs bs Hx Himp Hg).
Qed.

Lemma check_syscall_readv_ext : forall i mp eff m iovs,
  bv_unsigned (in_sysno i) = 65 -> mem_ext (in_mem i) mp ->
  import_iovecs (in_mem i) (in_arg i 1) (iovcnt32 (in_arg i 2)) = ImpOk iovs ->
  check_syscall (with_mem i mp) eff m = check_syscall i eff m.
Proof.
  intros i mp eff m iovs Hno Hx Himp.
  rewrite (rob_dispatch_65 (with_mem i mp) eff m Hno), (rob_dispatch_65 i eff m Hno).
  exact (check_readv_ext i mp (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) eff m iovs Hx Himp).
Qed.

Lemma check_syscall_openat_ext : forall i mp eff m,
  bv_unsigned (in_sysno i) = 56 -> mem_ext (in_mem i) mp ->
  read_cstr (in_mem i) (in_arg i 1) <> CstrFault ->
  check_syscall (with_mem i mp) eff m = check_syscall i eff m.
Proof.
  intros i mp eff m Hno Hx Hnf.
  rewrite (rob_dispatch_56 (with_mem i mp) eff m Hno), (rob_dispatch_56 i eff m Hno).
  exact (check_openat_ext i mp (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) eff m Hx Hnf).
Qed.

Lemma check_syscall_unlinkat_ext : forall i mp eff m,
  bv_unsigned (in_sysno i) = 35 -> mem_ext (in_mem i) mp ->
  read_cstr (in_mem i) (in_arg i 1) <> CstrFault ->
  check_syscall (with_mem i mp) eff m = check_syscall i eff m.
Proof.
  intros i mp eff m Hno Hx Hnf.
  rewrite (rob_dispatch_35 (with_mem i mp) eff m Hno), (rob_dispatch_35 i eff m Hno).
  exact (check_unlinkat_ext i mp (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) eff m Hx Hnf).
Qed.

Lemma check_syscall_ioctl_ext : forall i mp eff m,
  bv_unsigned (in_sysno i) = 29 -> tty_only_request (cmd32 (in_arg i 1)) = true ->
  check_syscall (with_mem i mp) eff m = check_syscall i eff m.
Proof.
  intros i mp eff m Hno Htty.
  rewrite (rob_dispatch_29 (with_mem i mp) eff m Hno), (rob_dispatch_29 i eff m Hno).
  exact (check_ioctl_tty_ext i mp (fd32 (in_arg i 0)) (cmd32 (in_arg i 1)) eff m Htty).
Qed.

(** ** The nodes *)
Section Rob.
Variable segs : list Segment.

(** A system call whose check reads [in_mem] only through reads that succeed on the state's
    own view: every larger view answers the check the same way. *)
Lemma sys_rob_of_with_mem : forall ms m x8,
  ms_svc_pending ms = Some x8 ->
  (forall mp, mem_ext (ms_read_byte ms) mp -> forall eff,
     check_syscall (with_mem (sys_input segs ms x8) mp) eff m
     = check_syscall (sys_input segs ms x8) eff m) ->
  sys_rob segs (mkCfg ms m).
Proof.
  intros ms m x8 Hs H. apply sys_rob_of_check. intros r x8' Hr Hs' eff.
  rewrite Hs in Hs'. injection Hs' as <-.
  rewrite sys_input_wrom. apply H. apply mem_ext_read_byte_wrom. exact Hr.
Qed.

(** A node whose number reads no memory. *)
Lemma rob_memfree_node : forall ms m no, ms_svc_pending ms = Some (Z_to_bv 64 no) ->
  0 <= no < 2^64 -> memfree no -> sys_rob segs (mkCfg ms m).
Proof.
  intros ms m no Hs Hr Hmf. apply (sys_rob_memfree segs ms m _ Hs).
  rewrite unsigned_lit by exact Hr. exact Hmf.
Qed.

(** writev (66), from the premises the NWritev and NWritevF nodes share. *)
Lemma rob_gather : forall ms m bufs iovs,
  ms_svc_pending ms = Some (Z_to_bv 64 66) ->
  areg ms 12 = Z_to_bv 64 (Z.of_nat (length bufs)) ->
  (1 <= length bufs <= 1024)%nat ->
  bv_unsigned (areg ms 11) + 16 * Z.of_nat (length bufs) <= 2^47 ->
  Z.of_nat (length (concat bufs)) <= max_write ->
  ms_rom ms = seg_rom segs ->
  bytes_at segs (ms_mem ms) (bv_unsigned (areg ms 11)) (iovec_bytes iovs) ->
  Forall2 (fun iov bs => snd iov = Z_to_bv 64 (Z.of_nat (length bs)) /\
                         bv_unsigned (fst iov) + Z.of_nat (length bs) <= 2^47 /\
                         bytes_at segs (ms_mem ms) (bv_unsigned (fst iov)) bs) iovs bufs ->
  sys_rob segs (mkCfg ms m).
Proof.
  intros ms m bufs iovs Hsvc Ha2 Hcnt Harr Htot Hrom Hiov Hbufs.
  unfold max_write in Htot.
  pose proof (iovs_ok_of_at segs _ _ _ Hrom Hbufs ltac:(lia)) as Hok.
  pose proof (iovs_range_of_at segs _ _ _ Hbufs) as Hrng.
  pose proof (Forall2_length Hbufs) as Hleq.
  pose proof (iovs_total_ok _ _ _ Hok) as Htotal.
  assert (Hcnt32 : iovcnt32 (Z_to_bv 64 (Z.of_nat (length bufs))) = Z_to_bv 64 (Z.of_nat (length bufs))).
  { unfold iovcnt32. apply abi_low32_small. lia. }
  assert (Himp : import_iovecs (ms_read_byte ms) (areg ms 11) (iovcnt32 (Z_to_bv 64 (Z.of_nat (length bufs)))) = ImpOk iovs).
  { rewrite Hcnt32, <- Hleq. apply import_iovecs_ok; [lia| rewrite Hleq; exact Harr | eapply bytes_at_in; eassumption | exact Hrng]. }
  assert (Hg : gather_iovecs (ms_read_byte ms) (cap_iovecs iovs) = Some (concat bufs)).
  { rewrite cap_iovecs_id_max by (rewrite Htotal; unfold MAX_RW_COUNT; lia).
    apply gather_iovecs_ok. exact Hok. }
  apply (sys_rob_of_with_mem ms m _ Hsvc). intros mp Hx eff.
  apply (check_syscall_writev_ext _ mp eff m iovs (concat bufs)).
  - rewrite in_sysno_si. apply unsigned_lit. lia.
  - exact Hx.
  - rewrite in_mem_si, in_a1_si, in_a2_si, Ha2. exact Himp.
  - rewrite in_mem_si. exact Hg.
Qed.

(** The path read of an openat or unlinkat node does not fault: it answers the path, or
    [CstrTooLong] past [path_max] bytes. *)
Lemma path_read_ok : forall ms path,
  ~ In (Z_to_bv 8 0) path ->
  bv_unsigned (areg ms 11) + Z.of_nat (length path) + 1 <= 2^47 ->
  ms_rom ms = seg_rom segs ->
  bytes_at segs (ms_mem ms) (bv_unsigned (areg ms 11)) (path ++ [Z_to_bv 8 0]) ->
  read_cstr (ms_read_byte ms) (areg ms 11) <> CstrFault.
Proof.
  intros ms path Hnz Hacc Hrom Hp.
  pose proof (bytes_at_in _ _ _ _ Hrom Hp) as Hin.
  unfold read_cstr. rewrite <- (wa_unsigned_id (areg ms 11)).
  destruct (Nat.leb_spec0 path_max (length path)) as [Hlong|Hshort].
  - assert (E : read_cstr_aux (ms_read_byte ms) (wa (bv_unsigned (areg ms 11))) path_max = CstrTooLong).
    { apply (read_cstr_aux_toolong_bytes_in path_max path); [exact Hlong|exact Hnz| lia |].
      apply bytes_in_app in Hin as [Hin _]. exact Hin. }
    rewrite E. discriminate.
  - assert (E : read_cstr_aux (ms_read_byte ms) (wa (bv_unsigned (areg ms 11))) path_max = CstrOk path).
    { apply (read_cstr_aux_bytes_in path path_max); [lia|exact Hnz|exact Hacc|exact Hin]. }
    rewrite E. discriminate.
Qed.

Lemma rob_openat_of : forall ms m path,
  ms_svc_pending ms = Some (Z_to_bv 64 56) ->
  ~ In (Z_to_bv 8 0) path ->
  bv_unsigned (areg ms 11) + Z.of_nat (length path) + 1 <= 2^47 ->
  ms_rom ms = seg_rom segs ->
  bytes_at segs (ms_mem ms) (bv_unsigned (areg ms 11)) (path ++ [Z_to_bv 8 0]) ->
  sys_rob segs (mkCfg ms m).
Proof.
  intros ms m path Hsvc Hnz Hacc Hrom Hp.
  pose proof (path_read_ok ms path Hnz Hacc Hrom Hp) as Hnf.
  apply (sys_rob_of_with_mem ms m _ Hsvc). intros mp Hx eff.
  apply (check_syscall_openat_ext _ mp eff m).
  - rewrite in_sysno_si. apply unsigned_lit. lia.
  - exact Hx.
  - rewrite in_mem_si, in_a1_si. exact Hnf.
Qed.

Lemma rob_unlinkat_of : forall ms m path,
  ms_svc_pending ms = Some (Z_to_bv 64 35) ->
  ~ In (Z_to_bv 8 0) path ->
  bv_unsigned (areg ms 11) + Z.of_nat (length path) + 1 <= 2^47 ->
  ms_rom ms = seg_rom segs ->
  bytes_at segs (ms_mem ms) (bv_unsigned (areg ms 11)) (path ++ [Z_to_bv 8 0]) ->
  sys_rob segs (mkCfg ms m).
Proof.
  intros ms m path Hsvc Hnz Hacc Hrom Hp.
  pose proof (path_read_ok ms path Hnz Hacc Hrom Hp) as Hnf.
  apply (sys_rob_of_with_mem ms m _ Hsvc). intros mp Hx eff.
  apply (check_syscall_unlinkat_ext _ mp eff m).
  - rewrite in_sysno_si. apply unsigned_lit. lia.
  - exact Hx.
  - rewrite in_mem_si, in_a1_si. exact Hnf.
Qed.

Lemma rob_write : forall ms m fd bs, at_node segs (NWrite fd bs) ms -> sys_rob segs (mkCfg ms m).
Proof.
  intros ms m fd bs (Hsvc & Hfd & Ha0 & Ha2 & Hlen & Hacc & Hrom & Hbs).
  unfold rw_bytes_max in Hlen.
  pose proof (bytes_at_in _ _ _ _ Hrom Hbs) as Hin.
  apply (sys_rob_of_with_mem ms m _ Hsvc). intros mp Hx eff.
  apply (check_syscall_write_ext _ mp eff m bs).
  - rewrite in_sysno_si. apply unsigned_lit. lia.
  - exact Hx.
  - rewrite in_mem_si, in_a1_si, in_a2_si, Ha2. rewrite <- (wa_unsigned_id (areg ms 11)).
    apply read_bytes_map_bytes_in; [exact Hin|lia].
Qed.

Lemma rob_writev : forall ms m fd bufs, at_node segs (NWritev fd bufs) ms -> sys_rob segs (mkCfg ms m).
Proof.
  intros ms m fd bufs (Hsvc & Hfd & Ha0 & Ha2 & Hcnt & Harr & Htot & Hrom & iovs & Hiov & Hbufs).
  exact (rob_gather ms m bufs iovs Hsvc Ha2 Hcnt Harr Htot Hrom Hiov Hbufs).
Qed.

Lemma rob_writevf : forall ms m fd bufs, at_node segs (NWritevF fd bufs) ms -> sys_rob segs (mkCfg ms m).
Proof.
  intros ms m fd bufs (Hsvc & Hfd & Ha0 & Ha2 & Hcnt & Harr & Htot & Hrom & iovs & Hiov & Hbufs).
  exact (rob_gather ms m bufs iovs Hsvc Ha2 Hcnt Harr (proj2 Htot) Hrom Hiov Hbufs).
Qed.

Lemma rob_open : forall ms m path, at_node segs (NOpen path) ms -> sys_rob segs (mkCfg ms m).
Proof.
  intros ms m path (Hsvc & Ha0 & Hfl & Hnz & Hsl & Hdd & Hacc & Hrom & Hp).
  exact (rob_openat_of ms m path Hsvc Hnz Hacc Hrom Hp).
Qed.

Lemma rob_openw : forall ms m path mode, at_node segs (NOpenW path mode) ms -> sys_rob segs (mkCfg ms m).
Proof.
  intros ms m path mode (Hsvc & Ha0 & Hfl & Ha3 & Hnz & Hsl & Hacc & Hrom & Hp).
  exact (rob_openat_of ms m path Hsvc Hnz Hacc Hrom Hp).
Qed.

Lemma rob_unlink : forall ms m path rmdir, at_node segs (NUnlink path rmdir) ms -> sys_rob segs (mkCfg ms m).
Proof.
  intros ms m path rmdir (Hsvc & Ha0 & Ha2 & Hnz & Hne & Hnd & Hndd & Hsl & Hlen & Hacc & Hrom & Hp).
  exact (rob_unlinkat_of ms m path Hsvc Hnz Hacc Hrom Hp).
Qed.

Lemma rob_readv : forall ms m fd dsts, at_node segs (NReadv fd dsts) ms -> sys_rob segs (mkCfg ms m).
Proof.
  intros ms m fd dsts (Hsvc & Hfd & Ha0 & Ha2 & Hn & Harr & Hfirst & Htot & Hdsts & Hrom & Hiov).
  pose proof (bytes_at_in _ _ _ _ Hrom Hiov) as Hin.
  assert (Hr3 : Forall (fun d => 0 <= snd d /\ fst d + snd d <= 2^47 /\ 0 <= fst d) dsts).
  { apply Forall_impl with (2 := Hdsts). intros [b l] (H1 & H2 & (H3 & _ & _)). cbn [fst snd] in *. lia. }
  assert (Hleniovs : length (iovs_of dsts) = length dsts) by apply length_iovs_of.
  assert (Hcnt32 : iovcnt32 (Z_to_bv 64 (Z.of_nat (length dsts))) = Z_to_bv 64 (Z.of_nat (length dsts))).
  { unfold iovcnt32. apply abi_low32_small. lia. }
  assert (Himp : import_iovecs (ms_read_byte ms) (areg ms 11) (Z_to_bv 64 (Z.of_nat (length dsts))) = ImpOk (iovs_of dsts)).
  { rewrite <- Hleniovs. apply import_iovecs_ok; [lia| lia | exact Hin |].
    unfold iovs_of. apply Forall_map. apply Forall_impl with (2 := Hr3).
    intros [b l] (H1 & H2 & H3). cbn [fst snd] in *. rewrite !unsigned_lit by lia. lia. }
  apply (sys_rob_of_with_mem ms m _ Hsvc). intros mp Hx eff.
  apply (check_syscall_readv_ext _ mp eff m (iovs_of dsts)).
  - rewrite in_sysno_si. apply unsigned_lit. lia.
  - exact Hx.
  - rewrite in_mem_si, in_a1_si, in_a2_si, Ha2, Hcnt32. exact Himp.
Qed.

(** ioctl (29) with TIOCGWINSZ (21523), a terminal-only request. *)
Lemma rob_ioctl : forall ms m fd req, at_node segs (NIoctl fd req) ms -> sys_rob segs (mkCfg ms m).
Proof.
  intros ms m fd req (Hsvc & Hfd & Hreq & Ha0 & Ha1).
  assert (Htty : tty_only_request (cmd32 (areg ms 11)) = true).
  { rewrite Ha1. unfold cmd32. rewrite abi_low32_small by lia. subst req. reflexivity. }
  apply (sys_rob_of_with_mem ms m _ Hsvc). intros mp _ eff.
  apply (check_syscall_ioctl_ext _ mp eff m).
  - rewrite in_sysno_si. apply unsigned_lit. lia.
  - rewrite in_a1_si. exact Htty.
Qed.

Lemma rob_read : forall ms m fd buf count, at_node segs (NRead fd buf count) ms -> sys_rob segs (mkCfg ms m).
Proof. intros ms m fd buf count [Hs _]. apply (rob_memfree_node ms m 63 Hs); [lia|exact memfree_63]. Qed.

Lemma rob_close : forall ms m fd, at_node segs (NClose fd) ms -> sys_rob segs (mkCfg ms m).
Proof. intros ms m fd [Hs _]. apply (rob_memfree_node ms m 57 Hs); [lia|exact memfree_57]. Qed.

Lemma rob_mmap : forall ms m addr len prot flags, at_node segs (NMmap addr len prot flags) ms ->
  sys_rob segs (mkCfg ms m).
Proof. intros ms m addr len prot flags [Hs _]. apply (rob_memfree_node ms m 222 Hs); [lia|exact memfree_222]. Qed.

Lemma rob_munmap : forall ms m addr len, at_node segs (NMunmap addr len) ms -> sys_rob segs (mkCfg ms m).
Proof. intros ms m addr len [Hs _]. apply (rob_memfree_node ms m 215 Hs); [lia|exact memfree_215]. Qed.

Lemma rob_lseek : forall ms m fd off whence, at_node segs (NLseek fd off whence) ms -> sys_rob segs (mkCfg ms m).
Proof. intros ms m fd off whence [Hs _]. apply (rob_memfree_node ms m 62 Hs); [lia|exact memfree_62]. Qed.

Lemma rob_exit : forall ms m code, at_node segs (NExit code) ms -> sys_rob segs (mkCfg ms m).
Proof.
  intros ms m code [[Hs|Hs] _].
  - apply (rob_memfree_node ms m 93 Hs); [lia|exact memfree_93].
  - apply (rob_memfree_node ms m 94 Hs); [lia|exact memfree_94].
Qed.

End Rob.

(** [ITreeA.node_soundA]'s [nsA_rob] at [at_nodeA]: on the nodes it does not hold at
    (brk, mprotect, mremap, the no-reserve mmap, set_tid_address, the peek) there is nothing to
    show. *)
Lemma at_nodeA_rob : forall segs n RNG ms mo_,
  at_nodeA segs n RNG ms -> RomBase.sys_rob segs (mkCfg ms mo_).
Proof.
  intros segs n RNG ms mo_ H.
  pose proof (at_nodeA_at_node segs n RNG ms H) as Hat.
  destruct n; cbn [at_nodeA] in H; try contradiction.
  all: lazymatch type of Hat with
       | at_node _ (NWrite _ _) _ => exact (rob_write segs ms mo_ _ _ Hat)
       | at_node _ (NWritev _ _) _ => exact (rob_writev segs ms mo_ _ _ Hat)
       | at_node _ (NOpen _) _ => exact (rob_open segs ms mo_ _ Hat)
       | at_node _ (NRead _ _ _) _ => exact (rob_read segs ms mo_ _ _ _ Hat)
       | at_node _ (NClose _) _ => exact (rob_close segs ms mo_ _ Hat)
       | at_node _ (NIoctl _ _) _ => exact (rob_ioctl segs ms mo_ _ _ Hat)
       | at_node _ (NExit _) _ => exact (rob_exit segs ms mo_ _ Hat)
       | at_node _ (NMmap _ _ _ _) _ => exact (rob_mmap segs ms mo_ _ _ _ _ Hat)
       | at_node _ (NMunmap _ _) _ => exact (rob_munmap segs ms mo_ _ _ Hat)
       | at_node _ (NOpenW _ _) _ => exact (rob_openw segs ms mo_ _ _ Hat)
       | at_node _ (NWritevF _ _) _ => exact (rob_writevf segs ms mo_ _ _ Hat)
       | at_node _ (NReadv _ _) _ => exact (rob_readv segs ms mo_ _ _ Hat)
       | at_node _ (NUnlink _ _) _ => exact (rob_unlink segs ms mo_ _ _ Hat)
       | at_node _ (NLseek _ _ _) _ => exact (rob_lseek segs ms mo_ _ _ _ Hat)
       end.
Qed.
