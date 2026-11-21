(* SPDX-License-Identifier: MIT *)
(* Copied from jsoncons/fuzz_bigint's proofs/lib/Common/Cfg/RomWritev.v; module paths renamed to this unit. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Common.Cfg Require Import RomBase.
Import ListNotations.
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
destruct (read_u64 mp (a + 8)) as [v2|] eqn:E2; [|intro H; discriminate H].
rewrite (read_u64_ext mp mp' a v1 Hx E1), (read_u64_ext mp mp' (a + 8) v2 Hx E2). intro H; exact H.
Qed.
Lemma iovec_entry_accesses_ext : forall mp mp' a b n, mem_ext mp mp' ->
read_iovec_entry mp a = IovEntry b n ->
iovec_entry_accesses mp' a = iovec_entry_accesses mp a.
Proof.
intros mp mp' a b n Hx. unfold read_iovec_entry, iovec_entry_accesses.
destruct (read_u64 mp a) as [v1|] eqn:E1; [|intro H; discriminate H].
destruct (read_u64 mp (a + 8)) as [v2|] eqn:E2; [|intro H; discriminate H].
intros _. rewrite (read_u64_ext mp mp' a v1 Hx E1), (read_u64_ext mp mp' (a + 8) v2 Hx E2). reflexivity.
Qed.
Lemma copy_iovecs_aux_ext : forall k mp mp' a iovs, mem_ext mp mp' ->
copy_iovecs_aux mp a k = ImpOk iovs -> copy_iovecs_aux mp' a k = ImpOk iovs.
Proof.
induction k as [|k IH]; intros mp mp' a iovs Hx H; [exact H|].
cbn [copy_iovecs_aux] in *.
destruct (read_iovec_entry mp a) as [b n| |] eqn:E; try discriminate H.
rewrite (read_iovec_entry_ext mp mp' a b n Hx E).
destruct (copy_iovecs_aux mp (a + 16) k) as [rest| |] eqn:E2; try discriminate H.
rewrite (IH mp mp' (a + 16) rest Hx E2). exact H.
Qed.
Lemma copy_iovecs_accesses_ext : forall k mp mp' a iovs, mem_ext mp mp' ->
copy_iovecs_aux mp a k = ImpOk iovs ->
copy_iovecs_accesses mp' a k = copy_iovecs_accesses mp a k.
Proof.
induction k as [|k IH]; intros mp mp' a iovs Hx H; [reflexivity|].
cbn [copy_iovecs_aux copy_iovecs_accesses] in *.
destruct (read_iovec_entry mp a) as [b n| |] eqn:E; try discriminate H.
rewrite (iovec_entry_accesses_ext mp mp' a b n Hx E), (read_iovec_entry_ext mp mp' a b n Hx E).
destruct (copy_iovecs_aux mp (a + 16) k) as [rest| |] eqn:E2; try discriminate H.
rewrite (IH mp mp' (a + 16) rest Hx E2). reflexivity.
Qed.
Lemma gather_iovecs_ext : forall iovs mp mp' bs, mem_ext mp mp' ->
gather_iovecs mp iovs = Some bs -> gather_iovecs mp' iovs = Some bs.
Proof.
induction iovs as [|[b n] rest IH]; intros mp mp' bs Hx H; [exact H|].
cbn [gather_iovecs] in *.
destruct (read_bytes_map mp b n) as [x|] eqn:E; [|discriminate H].
rewrite (read_bytes_map_ext mp mp' b n x Hx E).
destruct (gather_iovecs mp rest) as [y|] eqn:E2; [|discriminate H].
rewrite (IH mp mp' y Hx E2). exact H.
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
- destruct (negb (access_okb a 16)); [reflexivity|].
destruct (read_iovec_entry mp a) as [b l| |] eqn:E; try (intro H; discriminate H).
intros _. exact (iovec_entry_accesses_ext mp mp' a b l Hx E).
- destruct (bv_eqb n (Z_to_bv 64 0)); [reflexivity|].
destruct (IOV_MAX <? bv_unsigned n)%Z; [reflexivity|].
destruct (negb (access_okb a (16 * bv_unsigned n))); [reflexivity|].
destruct (copy_iovecs_aux mp a (word_to_nat n)) as [l| |] eqn:E; try (intro H; discriminate H).
intros _. exact (copy_iovecs_accesses_ext _ mp mp' a l Hx E).
Qed.
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
Lemma check_writev_chan_ext : forall i mp' fd iov cnt eff m ch iovs bs,
fd_lookup (m_fds m) fd = Some (FdChannel ch) ->
mem_ext (in_mem i) mp' ->
import_iovecs (in_mem i) iov (iovcnt32 cnt) = ImpOk iovs ->
gather_iovecs (in_mem i) (cap_iovecs iovs) = Some bs ->
check_writev (with_mem i mp') fd iov cnt eff m = check_writev i fd iov cnt eff m.
Proof.
intros i mp' fd iov cnt eff m ch iovs bs Hfd Hx Himp Hg.
unfold check_writev. rewrite Hfd. unfold with_mem. cbn [in_mem].
rewrite (import_iovecs_ext _ _ _ _ _ Hx Himp), Himp.
rewrite (import_iovecs_accesses_ext _ _ _ _ _ Hx Himp).
unfold writev_gathered. rewrite (gather_prefix_ext _ _ _ _ Hx Hg).
reflexivity.
Qed.
