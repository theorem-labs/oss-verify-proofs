(* SPDX-License-Identifier: MIT *)
(* Theorem Labs, 2026-11 (LPS 727298f3): [RomBase.sys_rob] at the system calls of this harness
   whose checks read [in_mem]: openat (56), writev (66) and ioctl (29).

   A read that succeeds on a view returns the same bytes on any view that extends it
   ([RomBase.mem_ext]).  So:
   - openat: [check_openat] reads [in_mem] only through [read_cstr] (the path) and
     [cstr_access_len_aux] (the path's copy-in record); when the path read does not fault
     ([CstrOk] or [CstrTooLong]), both are the same over a larger view ([check_openat_ext]);
   - writev: [check_writev] reads [in_mem] through [import_iovecs] (the iovec array),
     [import_iovecs_accesses] (its copy-in record) and [writev_gathered] (the buffers); when
     the import succeeds and every buffer of the capped vector is readable, all three are the
     same over a larger view ([check_writev_ext]);
   - ioctl: [check_ioctl] reads [in_mem] only for a datagram socket's SIOCGIFINDEX, never for a
     terminal-only request ([check_ioctl_tty_ext]).
   The iovec lemmas are those of RomWritev.v, stated over [RomBase.mem_ext]. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase MemImageType RiscvSemantics State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RomBase.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RomBase.
Import ListNotations.

(** * The iovec reads over a larger view *)

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

(** * The three checks over a larger view *)

Lemma check_openat_ext : forall i mp dirfd pathp flags eff m,
  mem_ext (in_mem i) mp -> read_cstr (in_mem i) pathp <> CstrFault ->
  check_openat (with_mem i mp) dirfd pathp flags eff m = check_openat i dirfd pathp flags eff m.
Proof.
  intros i mp dirfd pathp flags eff m Hx Hnf.
  unfold check_openat, Open.check_openat_body.
  change (in_mem (with_mem i mp)) with mp.
  rewrite (cstr_access_len_aux_ext path_max (in_mem i) mp pathp Hx Hnf).
  rewrite (read_cstr_ext (in_mem i) mp pathp Hx Hnf).
  reflexivity.
Qed.

Lemma check_writev_ext : forall i mp fd iov cnt eff m iovs bs,
  mem_ext (in_mem i) mp ->
  import_iovecs (in_mem i) iov (iovcnt32 cnt) = ImpOk iovs ->
  gather_iovecs (in_mem i) (cap_iovecs iovs) = Some bs ->
  check_writev (with_mem i mp) fd iov cnt eff m = check_writev i fd iov cnt eff m.
Proof.
  intros i mp fd iov cnt eff m iovs bs Hx Himp Hg.
  unfold check_writev.
  change (in_mem (with_mem i mp)) with mp.
  rewrite (import_iovecs_accesses_ext (in_mem i) mp iov (iovcnt32 cnt) iovs Hx Himp).
  rewrite (import_iovecs_ext (in_mem i) mp iov (iovcnt32 cnt) iovs Hx Himp), Himp.
  cbv beta iota zeta.
  unfold writev_gathered.
  rewrite (gather_prefix_full mp (cap_iovecs iovs) bs
             (gather_iovecs_ext (cap_iovecs iovs) (in_mem i) mp bs Hx Hg)).
  rewrite (gather_prefix_full (in_mem i) (cap_iovecs iovs) bs Hg).
  reflexivity.
Qed.

Lemma check_ioctl_tty_ext : forall i mp fd req eff m,
  tty_only_request req = true ->
  check_ioctl (with_mem i mp) fd req eff m = check_ioctl i fd req eff m.
Proof.
  intros i mp fd req eff m Ht. unfold check_ioctl. rewrite Ht. reflexivity.
Qed.

(** The dispatch at the three numbers, for any input. *)
Lemma check_syscall_at_56 : forall i eff m, bv_unsigned (in_sysno i) = 56%Z ->
  check_syscall i eff m = check_openat i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) eff m.
Proof. intros i eff m H. unfold check_syscall. rewrite H. reflexivity. Qed.

Lemma check_syscall_at_66 : forall i eff m, bv_unsigned (in_sysno i) = 66%Z ->
  check_syscall i eff m = check_writev i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) eff m.
Proof. intros i eff m H. unfold check_syscall. rewrite H. reflexivity. Qed.

Lemma check_syscall_at_29 : forall i eff m, bv_unsigned (in_sysno i) = 29%Z ->
  check_syscall i eff m = check_ioctl i (fd32 (in_arg i 0)) (cmd32 (in_arg i 1)) eff m.
Proof. intros i eff m H. unfold check_syscall. rewrite H. reflexivity. Qed.

(** * [sys_rob] at the three numbers *)

Section Seg.
Variable segs : list Segment.

(** A call whose check is the same over every larger view of the input's memory. *)
Lemma sys_rob_of_ext : forall ms model x8,
  ms_svc_pending ms = Some x8 ->
  (forall mp, mem_ext (ms_read_byte ms) mp -> forall eff,
     check_syscall (with_mem (sys_input segs ms x8) mp) eff model
     = check_syscall (sys_input segs ms x8) eff model) ->
  sys_rob segs (mkCfg ms model).
Proof.
  intros ms model x8 Hsvc H. apply sys_rob_of_check.
  intros r x8' Hr Hs eff. rewrite Hsvc in Hs. injection Hs as <-.
  rewrite sys_input_wrom. apply H. apply mem_ext_read_byte_wrom. exact Hr.
Qed.

(** openat whose path read does not fault. *)
Lemma sys_rob_openat : forall ms model x8,
  ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 56%Z ->
  read_cstr (ms_read_byte ms) (ms_gpr ms 1) <> CstrFault ->
  sys_rob segs (mkCfg ms model).
Proof.
  intros ms model x8 Hsvc Hno Hnf.
  apply (sys_rob_of_ext ms model x8 Hsvc). intros mp Hx eff.
  rewrite (check_syscall_at_56 (with_mem (sys_input segs ms x8) mp) eff model) by exact Hno.
  rewrite (check_syscall_at_56 (sys_input segs ms x8) eff model) by exact Hno.
  exact (check_openat_ext (sys_input segs ms x8) mp _ _ _ eff model Hx Hnf).
Qed.

(** writev whose iovec array imports and whose capped buffers are all readable. *)
Lemma sys_rob_writev : forall ms model x8 iovs bs,
  ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 66%Z ->
  import_iovecs (ms_read_byte ms) (ms_gpr ms 1) (iovcnt32 (ms_gpr ms 2)) = ImpOk iovs ->
  gather_iovecs (ms_read_byte ms) (cap_iovecs iovs) = Some bs ->
  sys_rob segs (mkCfg ms model).
Proof.
  intros ms model x8 iovs bs Hsvc Hno Himp Hg.
  apply (sys_rob_of_ext ms model x8 Hsvc). intros mp Hx eff.
  rewrite (check_syscall_at_66 (with_mem (sys_input segs ms x8) mp) eff model) by exact Hno.
  rewrite (check_syscall_at_66 (sys_input segs ms x8) eff model) by exact Hno.
  exact (check_writev_ext (sys_input segs ms x8) mp _ _ _ eff model iovs bs Hx Himp Hg).
Qed.

(** ioctl with a terminal-only request. *)
Lemma sys_rob_ioctl_tty : forall ms model x8,
  ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 29%Z ->
  tty_only_request (cmd32 (ms_gpr ms 1)) = true ->
  sys_rob segs (mkCfg ms model).
Proof.
  intros ms model x8 Hsvc Hno Ht.
  apply (sys_rob_of_ext ms model x8 Hsvc). intros mp Hx eff.
  rewrite (check_syscall_at_29 (with_mem (sys_input segs ms x8) mp) eff model) by exact Hno.
  rewrite (check_syscall_at_29 (sys_input segs ms x8) eff model) by exact Hno.
  exact (check_ioctl_tty_ext (sys_input segs ms x8) mp _ _ eff model Ht).
Qed.
End Seg.
