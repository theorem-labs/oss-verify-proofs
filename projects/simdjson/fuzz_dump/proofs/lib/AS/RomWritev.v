(* SPDX-License-Identifier: MIT *)
(* Theorem Labs, 2026-11: writev's and ioctl's memory reads over a larger read-only backing.
   Copied, namespace aside, from the simdjson family's Common/RomWritev.v as simdjson/fuzz_utf8's
   port tree has it (itself from openssl/hashtable's and leptonica's port trees).  Here only the
   reads of the iovec array and of the buffers and the terminal ioctl; this unit's writev node
   ([Lib/NodesA_wv.v]) derives its [RomBase.sys_rob] from them.

   [check_writev] (Sys/Fs/ReadWrite.v) reads [in_mem] through [import_iovecs] (the iovec array:
   [read_iovec_entry], two [read_u64]), [import_iovecs_accesses] (the array's copy-in record)
   and [gather_iovecs] (the buffers, [read_bytes_map]).  A read that succeeds on a view returns
   the same bytes on any view that extends it, and the record reads only the entries' own words. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import Prelude.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.AS Require Import CatSim FileSim RomBase.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

(* The reads are proved over any two views [mp], [mp'] with [mem_ext mp mp'] and specialised to
   [wrom] only at the end. *)

Lemma wv_read_bytes_aux_ext : forall n mp mp' a bs,
  mem_ext mp mp' -> read_bytes_aux mp a n = Some bs -> read_bytes_aux mp' a n = Some bs.
Proof.
  induction n as [|n IH]; intros mp mp' a bs Hx H; [exact H|].
  cbn [read_bytes_aux] in *.
  destruct (mp a) as [b|] eqn:E; [|discriminate H].
  rewrite (Hx a b E).
  destruct (read_bytes_aux mp (a + 1) n) as [rs|] eqn:E2; [|discriminate H].
  rewrite (IH mp mp' (a + 1) rs Hx E2). exact H.
Qed.

Lemma wv_read_bytes_map_ext : forall mp mp' a len bs,
  mem_ext mp mp' -> read_bytes_map mp a len = Some bs -> read_bytes_map mp' a len = Some bs.
Proof. intros mp mp' a len bs Hx. rewrite !read_bytes_map_eq. apply wv_read_bytes_aux_ext. exact Hx. Qed.

Lemma wv_read_u64_ext : forall mp mp' a v, mem_ext mp mp' ->
  read_u64 mp a = Some v -> read_u64 mp' a = Some v.
Proof.
  intros mp mp' a v Hx. unfold read_u64.
  destruct (read_bytes_map mp a (Z_to_bv 64 8)) as [bs|] eqn:E; [|intro H; discriminate H].
  rewrite (wv_read_bytes_map_ext mp mp' a _ bs Hx E). intro H; exact H.
Qed.

Lemma wv_read_iovec_entry_ext : forall mp mp' a b n, mem_ext mp mp' ->
  read_iovec_entry mp a = IovEntry b n -> read_iovec_entry mp' a = IovEntry b n.
Proof.
  intros mp mp' a b n Hx. unfold read_iovec_entry.
  destruct (read_u64 mp a) as [v1|] eqn:E1; [|intro H; discriminate H].
  destruct (read_u64 mp (a + 8)) as [v2|] eqn:E2; [|intro H; discriminate H].
  rewrite (wv_read_u64_ext mp mp' a v1 Hx E1), (wv_read_u64_ext mp mp' (a + 8) v2 Hx E2). intro H; exact H.
Qed.

Lemma wv_iovec_entry_accesses_ext : forall mp mp' a b n, mem_ext mp mp' ->
  read_iovec_entry mp a = IovEntry b n ->
  iovec_entry_accesses mp' a = iovec_entry_accesses mp a.
Proof.
  intros mp mp' a b n Hx. unfold read_iovec_entry, iovec_entry_accesses.
  destruct (read_u64 mp a) as [v1|] eqn:E1; [|intro H; discriminate H].
  destruct (read_u64 mp (a + 8)) as [v2|] eqn:E2; [|intro H; discriminate H].
  intros _. rewrite (wv_read_u64_ext mp mp' a v1 Hx E1), (wv_read_u64_ext mp mp' (a + 8) v2 Hx E2). reflexivity.
Qed.

Lemma wv_copy_iovecs_aux_ext : forall k mp mp' a iovs, mem_ext mp mp' ->
  copy_iovecs_aux mp a k = ImpOk iovs -> copy_iovecs_aux mp' a k = ImpOk iovs.
Proof.
  induction k as [|k IH]; intros mp mp' a iovs Hx H; [exact H|].
  cbn [copy_iovecs_aux] in *.
  destruct (read_iovec_entry mp a) as [b n| |] eqn:E; try discriminate H.
  rewrite (wv_read_iovec_entry_ext mp mp' a b n Hx E).
  destruct (copy_iovecs_aux mp (a + 16) k) as [rest| |] eqn:E2; try discriminate H.
  rewrite (IH mp mp' (a + 16) rest Hx E2). exact H.
Qed.

Lemma wv_copy_iovecs_accesses_ext : forall k mp mp' a iovs, mem_ext mp mp' ->
  copy_iovecs_aux mp a k = ImpOk iovs ->
  copy_iovecs_accesses mp' a k = copy_iovecs_accesses mp a k.
Proof.
  induction k as [|k IH]; intros mp mp' a iovs Hx H; [reflexivity|].
  cbn [copy_iovecs_aux copy_iovecs_accesses] in *.
  destruct (read_iovec_entry mp a) as [b n| |] eqn:E; try discriminate H.
  rewrite (wv_iovec_entry_accesses_ext mp mp' a b n Hx E), (wv_read_iovec_entry_ext mp mp' a b n Hx E).
  destruct (copy_iovecs_aux mp (a + 16) k) as [rest| |] eqn:E2; try discriminate H.
  rewrite (IH mp mp' (a + 16) rest Hx E2). reflexivity.
Qed.

Lemma wv_gather_iovecs_ext : forall iovs mp mp' bs, mem_ext mp mp' ->
  gather_iovecs mp iovs = Some bs -> gather_iovecs mp' iovs = Some bs.
Proof.
  induction iovs as [|[b n] rest IH]; intros mp mp' bs Hx H; [exact H|].
  cbn [gather_iovecs] in *.
  destruct (read_bytes_map mp b n) as [x|] eqn:E; [|discriminate H].
  rewrite (wv_read_bytes_map_ext mp mp' b n x Hx E).
  destruct (gather_iovecs mp rest) as [y|] eqn:E2; [|discriminate H].
  rewrite (IH mp mp' y Hx E2). exact H.
Qed.

Lemma wv_import_iovecs_ext : forall mp mp' a n iovs, mem_ext mp mp' ->
  import_iovecs mp a n = ImpOk iovs -> import_iovecs mp' a n = ImpOk iovs.
Proof.
  intros mp mp' a n iovs Hx. unfold import_iovecs.
  destruct (bv_eqb n (Z_to_bv 64 1)).
  - destruct (negb (access_okb a 16)); [intro H; exact H|].
    destruct (read_iovec_entry mp a) as [b l| |] eqn:E; try (intro H; discriminate H).
    rewrite (wv_read_iovec_entry_ext mp mp' a b l Hx E). intro H; exact H.
  - destruct (bv_eqb n (Z_to_bv 64 0)); [intro H; exact H|].
    destruct (IOV_MAX <? bv_unsigned n)%Z; [intro H; exact H|].
    destruct (negb (access_okb a (16 * bv_unsigned n))); [intro H; exact H|].
    destruct (copy_iovecs_aux mp a (word_to_nat n)) as [l| |] eqn:E; try (intro H; discriminate H).
    rewrite (wv_copy_iovecs_aux_ext _ mp mp' a l Hx E). intro H; exact H.
Qed.

Lemma wv_import_iovecs_accesses_ext : forall mp mp' a n iovs, mem_ext mp mp' ->
  import_iovecs mp a n = ImpOk iovs ->
  import_iovecs_accesses mp' a n = import_iovecs_accesses mp a n.
Proof.
  intros mp mp' a n iovs Hx. unfold import_iovecs, import_iovecs_accesses.
  destruct (bv_eqb n (Z_to_bv 64 1)).
  - destruct (negb (access_okb a 16)); [reflexivity|].
    destruct (read_iovec_entry mp a) as [b l| |] eqn:E; try (intro H; discriminate H).
    intros _. exact (wv_iovec_entry_accesses_ext mp mp' a b l Hx E).
  - destruct (bv_eqb n (Z_to_bv 64 0)); [reflexivity|].
    destruct (IOV_MAX <? bv_unsigned n)%Z; [reflexivity|].
    destruct (negb (access_okb a (16 * bv_unsigned n))); [reflexivity|].
    destruct (copy_iovecs_aux mp a (word_to_nat n)) as [l| |] eqn:E; try (intro H; discriminate H).
    intros _. exact (wv_copy_iovecs_accesses_ext _ mp mp' a l Hx E).
Qed.

(** The forms the writev nodes use: the larger view is [wrom ms r]. *)
Lemma gather_iovecs_wrom : forall iovs ms r bs, rom_ext (ms_rom ms) r ->
  gather_iovecs (ms_read_byte ms) iovs = Some bs -> gather_iovecs (ms_read_byte (wrom ms r)) iovs = Some bs.
Proof. intros iovs ms r bs Hr. apply wv_gather_iovecs_ext. exact (mem_ext_read_byte_wrom ms r Hr). Qed.

Lemma import_iovecs_wrom : forall ms r a n iovs, rom_ext (ms_rom ms) r ->
  import_iovecs (ms_read_byte ms) a n = ImpOk iovs -> import_iovecs (ms_read_byte (wrom ms r)) a n = ImpOk iovs.
Proof. intros ms r a n iovs Hr. apply wv_import_iovecs_ext. exact (mem_ext_read_byte_wrom ms r Hr). Qed.

Lemma import_iovecs_accesses_wrom : forall ms r a n iovs, rom_ext (ms_rom ms) r ->
  import_iovecs (ms_read_byte ms) a n = ImpOk iovs ->
  import_iovecs_accesses (ms_read_byte (wrom ms r)) a n = import_iovecs_accesses (ms_read_byte ms) a n.
Proof. intros ms r a n iovs Hr. apply wv_import_iovecs_accesses_ext. exact (mem_ext_read_byte_wrom ms r Hr). Qed.

(** writev's channel arm reads [in_mem] only through [import_iovecs], its copy-in record and
    [writev_gathered]; when the array imports and the capped buffers gather in full, a larger
    view gives the same check. *)
Lemma check_writev_chan_ext : forall i mp' fd iov cnt eff m ch iovs bs,
  fd_lookup (m_fds m) fd = Some (FdChannel ch) ->
  mem_ext (in_mem i) mp' ->
  import_iovecs (in_mem i) iov (iovcnt32 cnt) = ImpOk iovs ->
  gather_iovecs (in_mem i) (cap_iovecs iovs) = Some bs ->
  check_writev (with_mem i mp') fd iov cnt eff m = check_writev i fd iov cnt eff m.
Proof.
  intros i mp' fd iov cnt eff m ch iovs bs Hfd Hx Himp Hg.
  unfold check_writev. rewrite Hfd. cbv beta iota.
  unfold with_mem. cbn [in_mem].
  rewrite (wv_import_iovecs_accesses_ext _ _ _ _ _ Hx Himp).
  rewrite (wv_import_iovecs_ext _ _ _ _ _ Hx Himp), Himp. cbv beta iota zeta.
  unfold writev_gathered.
  rewrite (gather_prefix_full _ _ _ (wv_gather_iovecs_ext _ _ _ _ Hx Hg)), (gather_prefix_full _ _ _ Hg).
  reflexivity.
Qed.

Section Seg.
Variable segs : list Segment.

Lemma rob_check_syscall_29 : forall ms x8 eff m,
  bv_unsigned x8 = 29%Z ->
  check_syscall (sys_input segs ms x8) eff m
  = check_ioctl (sys_input segs ms x8) (fd32 (ms_gpr ms 0)) (cmd32 (ms_gpr ms 1)) eff m.
Proof.
  intros ms x8 eff m Hno. unfold check_syscall.
  change (in_sysno (sys_input segs ms x8)) with x8. rewrite Hno. reflexivity.
Qed.

(** An ioctl node whose request is a terminal-only one: every arm of [check_ioctl] answers it
    without reading [in_mem] (-ENOTTY, or unmodeled for /dev/urandom).  Text of cjson's
    RomWrite.v. *)
Lemma ioctl_rob_tty : forall ms model x8,
  ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 29%Z ->
  tty_only_request (cmd32 (ms_gpr ms 1)) = true ->
  sys_rob segs (mkCfg ms model).
Proof.
  intros ms model x8 Hs Hno Ht. apply sys_rob_of_check. intros r x8' Hr Hs' eff.
  rewrite Hs in Hs'. injection Hs' as <-.
  rewrite !(rob_check_syscall_29 _ x8 eff model Hno).
  change (ms_gpr (wrom ms r) 0) with (ms_gpr ms 0). change (ms_gpr (wrom ms r) 1) with (ms_gpr ms 1).
  unfold check_ioctl. rewrite !Ht.
  destruct (fd_lookup (m_fds model) (fd32 (ms_gpr ms 0))) as [[]|]; reflexivity.
Qed.

Lemma rob_check_syscall_66 : forall ms x8 eff m,
  bv_unsigned x8 = 66%Z ->
  check_syscall (sys_input segs ms x8) eff m
  = check_writev (sys_input segs ms x8) (fd32 (ms_gpr ms 0)) (ms_gpr ms 1) (ms_gpr ms 2) eff m.
Proof.
  intros ms x8 eff m Hno. unfold check_syscall.
  change (in_sysno (sys_input segs ms x8)) with x8. rewrite Hno. reflexivity.
Qed.

(** A writev node to a channel whose iovec array imports and whose (capped) buffers gather in
    full: its specification is the same over a larger read-only backing. *)
Lemma writev_rob_of : forall ms model (fd iov cnt : word) ch iovs bs,
  ms_svc_pending ms = Some (Z_to_bv 64 66) ->
  fd32 (ms_gpr ms 0) = fd -> ms_gpr ms 1 = iov -> ms_gpr ms 2 = cnt ->
  fd_lookup (m_fds model) fd = Some (FdChannel ch) ->
  import_iovecs (ms_read_byte ms) iov (iovcnt32 cnt) = ImpOk iovs ->
  gather_iovecs (ms_read_byte ms) (cap_iovecs iovs) = Some bs ->
  sys_rob segs (mkCfg ms model).
Proof.
  intros ms model fd iov cnt ch iovs bs Hs H0 H1 H2 Hfd Himp Hg.
  apply sys_rob_of_check. intros r x8 Hr Hs' eff. rewrite Hs in Hs'. injection Hs' as <-.
  rewrite !(rob_check_syscall_66 _ (Z_to_bv 64 66) eff model eq_refl).
  change (ms_gpr (wrom ms r) 0) with (ms_gpr ms 0). change (ms_gpr (wrom ms r) 1) with (ms_gpr ms 1).
  change (ms_gpr (wrom ms r) 2) with (ms_gpr ms 2).
  rewrite sys_input_wrom. rewrite H0, H1, H2.
  apply (check_writev_chan_ext _ _ _ _ _ eff model ch iovs bs Hfd).
  - rewrite in_mem_sys_input. apply mem_ext_read_byte_wrom. exact Hr.
  - rewrite in_mem_sys_input. exact Himp.
  - rewrite in_mem_sys_input. exact Hg.
Qed.
End Seg.
