(* SPDX-License-Identifier: MIT *)
(* Theorem Labs, 2026-11 (LPS 727298f3): writev's memory reads over a larger read-only backing.
   Copied from double-conversion/string_to_double_fuzzer lib/RomWritev.v
   (itself from openssl/hashtable
   Common/Cfg/RomWritev.v), without its ioctl part (this tree's
   ioctl node closes [sys_rob] by its own check, [YQ0k.rz_ioctl_winsz]), with
   [wv_import_iovecs_accesses_of_copy] added for [YQ0k.writev_rob].

   [check_writev] (Sys/Fs/ReadWrite.v) reads [in_mem] through [import_iovecs] (the iovec array:
   [read_iovec_entry], two [read_u64]), [import_iovecs_accesses] (the array's copy-in record)
   and [gather_iovecs] (the buffers, [read_bytes_map]).  A read that succeeds on a view returns
   the same bytes on any view that extends it, and the record reads only the entries' own words.
   The reads are proved over any two views [mp], [mp'] with [mem_ext mp mp']. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import Prelude Fs.ReadWrite.
From OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.C Require Import YK16 YK0o YK0j RomBase.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.


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

(** The same from the iovec array's copy ([copy_iovecs_aux]), the form [YQ0k.writev_chk_canon]
    takes: a one-entry array is one [read_iovec_entry]. *)
Lemma wv_import_iovecs_accesses_of_copy : forall mp mp' a n iovs, mem_ext mp mp' ->
  copy_iovecs_aux mp a (word_to_nat n) = ImpOk iovs ->
  import_iovecs_accesses mp' a n = import_iovecs_accesses mp a n.
Proof.
  intros mp mp' a n iovs Hx Hc. unfold import_iovecs_accesses.
  destruct (bv_eqb n (Z_to_bv 64 1)) eqn:E1.
  - apply bv_eqb_eq in E1. subst n.
    change (word_to_nat (Z_to_bv 64 1)) with 1%nat in Hc. cbn [copy_iovecs_aux] in Hc.
    destruct (read_iovec_entry mp a) as [b l| |] eqn:E; try discriminate Hc.
    destruct (negb (access_okb a 16)); [reflexivity|].
    exact (wv_iovec_entry_accesses_ext mp mp' a b l Hx E).
  - destruct (bv_eqb n (Z_to_bv 64 0)); [reflexivity|].
    destruct (IOV_MAX <? bv_unsigned n)%Z; [reflexivity|].
    destruct (negb (access_okb a (16 * bv_unsigned n))); [reflexivity|].
    exact (wv_copy_iovecs_accesses_ext _ mp mp' a iovs Hx Hc).
Qed.
