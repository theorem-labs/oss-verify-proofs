(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from bzip2/bzip2_compress_target's Common/Cfg/RomBase.v, the read lemmas of its Common/Cfg/RomWritev.v and Common/Cfg/RomWrite.v, and the terminal-ioctl check of its RefNodes.v (with cap_iovecs_aux_id as in RelSpec.v), with this unit's names; the unlinkat, readv and any-descriptor writev checks are this unit's. *)
(* Copied from bzip2/bzip2_compress_target's proof library: its Common/Cfg/RomBase.v (the read-only
   backing and [sys_rob]), the read lemmas of its Common/Cfg/RomWritev.v and Common/Cfg/RomWrite.v
   (writev's iovec reads, openat's path read) and the terminal-ioctl check of its RefNodes.v.  The
   unlinkat, readv and any-descriptor writev checks are this unit's.

   The read-only backing of a state, and system-call specifications that do not change when it
   grows.  [Top.Realize.rz_node] and [Top.SafeReach.sr_node] ask [sys_rob] at each node, so that a
   walk over a binary's own segments lifts to the run's segment list ([Top.RomStable]).

   Only a system call reads [ms_rom]: [Run.sys_input]'s [in_mem] is [ms_read_byte]
   (RiscvSemantics.v: [ms_mem] first, then [ms_rom]); no machine step reads it. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase MemImageType RiscvSemantics State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
Import ListNotations.

Definition wrom (ms : machine_state) (r : word -> option byte) : machine_state :=
  {| ms_regs := ms_regs ms; ms_fregs := ms_fregs ms; ms_pc_val := ms_pc_val ms;
     ms_svc_pending := ms_svc_pending ms; ms_resv := ms_resv ms; ms_fcsr := ms_fcsr ms;
     ms_mem := ms_mem ms; ms_rom := r |}.

Lemma wrom_eta : forall ms, wrom ms (ms_rom ms) = ms.
Proof. intros []; reflexivity. Qed.

Definition cwrom (c : config) (r : word -> option byte) : config :=
  mkCfg (wrom (cfg_ms c) r) (cfg_model c).

(** [r2] answers every byte [r1] answers, the same way. *)
Definition rom_ext (r1 r2 : word -> option byte) : Prop :=
  forall a b, r1 a = Some b -> r2 a = Some b.

Lemma rom_ext_refl : forall r, rom_ext r r.
Proof. intros r a b H. exact H. Qed.

Lemma rom_ext_trans : forall r1 r2 r3, rom_ext r1 r2 -> rom_ext r2 r3 -> rom_ext r1 r3.
Proof. intros r1 r2 r3 H1 H2 a b H. apply H2, H1, H. Qed.

(** The process's read view grows with the backing. *)
Lemma ms_read_byte_wrom_ext : forall ms r a b,
  rom_ext (ms_rom ms) r -> ms_read_byte ms a = Some b -> ms_read_byte (wrom ms r) a = Some b.
Proof.
  intros ms r a b Hr. unfold ms_read_byte. cbn [ms_mem ms_rom wrom].
  destruct (ms_mem ms a); [intro H; exact H | apply Hr].
Qed.

Lemma ms_read_bytes_aux_wrom : forall n ms r a bs,
  rom_ext (ms_rom ms) r -> ms_read_bytes_aux ms a n = Some bs ->
  ms_read_bytes_aux (wrom ms r) a n = Some bs.
Proof.
  induction n as [|n IH]; intros ms r a bs Hr H; [exact H|].
  cbn [ms_read_bytes_aux] in *.
  destruct (ms_read_byte ms a) as [b|] eqn:E; [|discriminate H].
  rewrite (ms_read_byte_wrom_ext ms r a b Hr E).
  destruct (ms_read_bytes_aux ms (a + 1) n) as [rest|] eqn:E2; [|discriminate H].
  rewrite (IH ms r (a + 1) rest Hr E2). exact H.
Qed.

Lemma ms_read_bytes_wrom : forall ms r a len bs,
  rom_ext (ms_rom ms) r -> ms_read_bytes ms a len = Some bs ->
  ms_read_bytes (wrom ms r) a len = Some bs.
Proof. intros ms r a len bs Hr. unfold ms_read_bytes. apply ms_read_bytes_aux_wrom. exact Hr. Qed.

(** ** System calls whose specification does not read [in_mem]

    For every arm that does not read [in_mem] the check is the same function of the input's
    other fields; each [memfree_NN] below is that fact for one number, by conversion. *)
Definition with_mem (i : SyscallInput) (mp : word -> option byte) : SyscallInput :=
  mkInput (in_sysno i) (in_args i) mp (in_wmem i).

Definition memfree (no : Z) : Prop :=
  forall i mp eff m, bv_unsigned (in_sysno i) = no ->
  check_syscall (with_mem i mp) eff m = check_syscall i eff m.

Ltac memfree_tac := intros i mp eff m H; unfold check_syscall; cbn [with_mem in_sysno]; rewrite H; reflexivity.

(** close, lseek, read, exit, exit_group, set_tid_address, brk, munmap, mmap, mremap, mprotect,
    madvise ([check_lseek] takes the arguments only; [check_read] reads only [in_wmem]). *)
Lemma memfree_57 : memfree 57. Proof. memfree_tac. Qed.
Lemma memfree_62 : memfree 62. Proof. memfree_tac. Qed.
Lemma memfree_63 : memfree 63. Proof. memfree_tac. Qed.
Lemma memfree_93 : memfree 93. Proof. memfree_tac. Qed.
Lemma memfree_94 : memfree 94. Proof. memfree_tac. Qed.
Lemma memfree_96 : memfree 96. Proof. memfree_tac. Qed.
Lemma memfree_214 : memfree 214. Proof. memfree_tac. Qed.
Lemma memfree_215 : memfree 215. Proof. memfree_tac. Qed.
Lemma memfree_222 : memfree 222. Proof. memfree_tac. Qed.
Lemma memfree_216 : memfree 216. Proof. memfree_tac. Qed.
Lemma memfree_226 : memfree 226. Proof. memfree_tac. Qed.
Lemma memfree_233 : memfree 233. Proof. memfree_tac. Qed.

(** [memfree NN] for a known number. *)
Ltac memfree_lit :=
  first [ exact memfree_57 | exact memfree_62 | exact memfree_63 | exact memfree_93
        | exact memfree_94 | exact memfree_96 | exact memfree_214 | exact memfree_215
        | exact memfree_222 | exact memfree_216 | exact memfree_226 | exact memfree_233 ].

(** ** Reads that succeed are the same over a larger memory view

    [State.read_cstr_aux] (a path, State.v) reads bytes [a, a+1, ...] until a NUL, each after
    [access_okb]; [State.cstr_access_len_aux] (the path's copy-in record) counts the same bytes.
    When the read does not fault, every byte it reads is defined, so a view that answers those
    bytes the same way gives the same result. *)
Definition mem_ext (mp mp' : word -> option byte) : Prop :=
  forall a b, mp a = Some b -> mp' a = Some b.

Lemma mem_ext_read_byte_wrom : forall ms r,
  rom_ext (ms_rom ms) r -> mem_ext (ms_read_byte ms) (ms_read_byte (wrom ms r)).
Proof. intros ms r Hr a b. apply ms_read_byte_wrom_ext. exact Hr. Qed.

Lemma read_cstr_aux_ext : forall k mp mp' a,
  mem_ext mp mp' -> read_cstr_aux mp a k <> CstrFault ->
  read_cstr_aux mp' a k = read_cstr_aux mp a k.
Proof.
  induction k as [|k IH]; intros mp mp' a Hx Hnf; [reflexivity|].
  cbn [read_cstr_aux] in *.
  destruct (negb (access_okb a 1)); [exfalso; apply Hnf; reflexivity|].
  destruct (mp a) as [b|] eqn:E; [|exfalso; apply Hnf; reflexivity].
  rewrite (Hx a b E).
  destruct (bv_eqb b (Z_to_bv 8 0)); [reflexivity|].
  destruct (read_cstr_aux mp (a + 1) k) as [r| |] eqn:E2.
  - rewrite (IH mp mp' (a + 1) Hx ltac:(rewrite E2; discriminate)), E2. reflexivity.
  - rewrite (IH mp mp' (a + 1) Hx ltac:(rewrite E2; discriminate)), E2. reflexivity.
  - exfalso. apply Hnf. reflexivity.
Qed.

Lemma cstr_access_len_aux_ext : forall k mp mp' a,
  mem_ext mp mp' -> read_cstr_aux mp a k <> CstrFault ->
  cstr_access_len_aux mp' a k = cstr_access_len_aux mp a k.
Proof.
  induction k as [|k IH]; intros mp mp' a Hx Hnf; [reflexivity|].
  cbn [read_cstr_aux cstr_access_len_aux] in *.
  destruct (negb (access_okb a 1)); [reflexivity|].
  destruct (mp a) as [b|] eqn:E; [|exfalso; apply Hnf; reflexivity].
  rewrite (Hx a b E).
  destruct (bv_eqb b (Z_to_bv 8 0)); [reflexivity|].
  rewrite (IH mp mp' (a + 1) Hx); [reflexivity|].
  intro Hf. apply Hnf. rewrite Hf. reflexivity.
Qed.

Lemma read_cstr_ext : forall mp mp' a,
  mem_ext mp mp' -> read_cstr mp a <> CstrFault -> read_cstr mp' a = read_cstr mp a.
Proof. intros mp mp' a. apply read_cstr_aux_ext. Qed.

Lemma read_bytes_aux_ext : forall k mp mp' a bs,
  mem_ext mp mp' -> read_bytes_aux mp a k = Some bs -> read_bytes_aux mp' a k = Some bs.
Proof.
  induction k as [|k IH]; intros mp mp' a bs Hx H; [exact H|].
  cbn [read_bytes_aux] in *.
  destruct (mp a) as [b|] eqn:E; [|discriminate H].
  rewrite (Hx a b E).
  destruct (read_bytes_aux mp (a + 1) k) as [r|] eqn:E2; [|discriminate H].
  rewrite (IH mp mp' (a + 1) r Hx E2). exact H.
Qed.

Lemma read_bytes_map_ext : forall mp mp' a len bs,
  mem_ext mp mp' -> read_bytes_map mp a len = Some bs -> read_bytes_map mp' a len = Some bs.
Proof.
  intros mp mp' a len bs Hx. rewrite !read_bytes_map_eq. apply read_bytes_aux_ext. exact Hx.
Qed.

(** writev and readv read [in_mem] through [import_iovecs] (the iovec array: [read_iovec_entry],
    two [read_u64]), [import_iovecs_accesses] (the array's copy-in record) and writev also through
    [gather_iovecs]/[gather_prefix] (the buffers).  A read that succeeds on a view returns the same
    bytes on any view that extends it, and the record reads only the entries' own words. *)
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

(** [writev_gathered]'s [gather_prefix] is the same on a larger view once every buffer reads in
    full. *)
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

(** Under the aggregate clamp the clamp is the identity. *)
Lemma cap_iovecs_aux_id : forall iovs left,
  (iovs_total iovs <= left)%Z -> cap_iovecs_aux iovs left = iovs.
Proof.
  induction iovs as [|[b n] r IH]; intros left H; [reflexivity|].
  cbn [cap_iovecs_aux iovs_total] in *.
  pose proof (iovs_total_nonneg r) as Hr.
  rewrite Z.min_r by lia. rewrite Z_to_bv_bv_unsigned. f_equal. apply IH. lia.
Qed.

Lemma cap_iovecs_id : forall iovs, (iovs_total iovs <= MAX_RW_COUNT)%Z -> cap_iovecs iovs = iovs.
Proof. intros iovs H. unfold cap_iovecs. apply cap_iovecs_aux_id. exact H. Qed.

(** [check_writev] reads [in_mem] only through [import_iovecs], [import_iovecs_accesses] and
    [writev_gathered], on every descriptor kind. *)
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
  (* reduce the decided import, so the gathered bytes are over [iovs] and no binder *)
  cbv beta iota zeta.
  unfold writev_gathered. rewrite (gather_prefix_ext _ _ _ _ Hx Hg).
  reflexivity.
Qed.

(** openat reads [in_mem] only through the path ([read_cstr] in [check_openat_body] and the
    copy-in record [cstr_access_len_aux]). *)
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

(** unlinkat reads [in_mem] the way openat does ([check_unlinkat_body]'s [read_cstr] and the
    copy-in record). *)
Lemma check_unlinkat_ext : forall i mp' dirfd pathp flags eff m,
  mem_ext (in_mem i) mp' -> read_cstr (in_mem i) pathp <> CstrFault ->
  check_unlinkat (with_mem i mp') dirfd pathp flags eff m = check_unlinkat i dirfd pathp flags eff m.
Proof.
  intros i mp' dirfd pathp flags eff m Hx Hnf.
  unfold check_unlinkat, Namei.check_unlinkat_body. unfold with_mem. cbn [in_mem].
  rewrite (cstr_access_len_aux_ext path_max (in_mem i) mp' pathp Hx Hnf).
  rewrite (read_cstr_ext (in_mem i) mp' pathp Hx Hnf).
  reflexivity.
Qed.

(** readv reads [in_mem] only through the iovec array's import and its record; the delivery
    ([check_readv_imported]) reads only [in_wmem]. *)
Lemma check_readv_ext : forall i mp' fd iov cnt eff m iovs,
  mem_ext (in_mem i) mp' ->
  import_iovecs (in_mem i) iov (iovcnt32 cnt) = ImpOk iovs ->
  check_readv (with_mem i mp') fd iov cnt eff m = check_readv i fd iov cnt eff m.
Proof.
  intros i mp' fd iov cnt eff m iovs Hx Himp.
  unfold check_readv.
  change (in_mem (with_mem i mp')) with mp'.
  rewrite (import_iovecs_ext _ _ _ _ _ Hx Himp), Himp.
  rewrite (import_iovecs_accesses_ext _ _ _ _ _ Hx Himp).
  (* what is left is [check_readv_imported], which reads only [in_wmem]: the same field *)
  reflexivity.
Qed.

(** [check_ioctl] reads the input only for SIOCGIFINDEX on a datagram socket, after
    [tty_only_request] fails; a terminal-only request (TIOCGWINSZ) reads no memory on any
    descriptor kind. *)
Lemma check_ioctl_tty_ext : forall i mp fd req eff m,
  tty_only_request req = true ->
  check_ioctl (with_mem i mp) fd req eff m = check_ioctl i fd req eff m.
Proof.
  intros i mp fd req eff m Htty.
  (* decide the terminal-request test first and reduce the decided [if] before comparing, so
     no arm keeps a [check_siocgifindex] (which reads the input) *)
  unfold check_ioctl. rewrite !Htty. destruct (fd_lookup _ _) as [[]|]; lazy beta iota; reflexivity.
Qed.

(** The dispatch of the memory-reading numbers, for any input. *)
Lemma check_syscall_29 : forall i eff m, bv_unsigned (in_sysno i) = 29%Z ->
  check_syscall i eff m = check_ioctl i (fd32 (in_arg i 0)) (cmd32 (in_arg i 1)) eff m.
Proof. intros i eff m H. unfold check_syscall. rewrite H. reflexivity. Qed.

Lemma check_syscall_35 : forall i eff m, bv_unsigned (in_sysno i) = 35%Z ->
  check_syscall i eff m = check_unlinkat i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) eff m.
Proof. intros i eff m H. unfold check_syscall. rewrite H. reflexivity. Qed.

Lemma check_syscall_56 : forall i eff m, bv_unsigned (in_sysno i) = 56%Z ->
  check_syscall i eff m = check_openat i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) eff m.
Proof. intros i eff m H. unfold check_syscall. rewrite H. reflexivity. Qed.

Lemma check_syscall_65 : forall i eff m, bv_unsigned (in_sysno i) = 65%Z ->
  check_syscall i eff m = check_readv i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) eff m.
Proof. intros i eff m H. unfold check_syscall. rewrite H. reflexivity. Qed.

Lemma check_syscall_66 : forall i eff m, bv_unsigned (in_sysno i) = 66%Z ->
  check_syscall i eff m = check_writev i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) eff m.
Proof. intros i eff m H. unfold check_syscall. rewrite H. reflexivity. Qed.

Section Seg.
Variable segs : list Segment.

(** At a system-call configuration, the specification is the same for every larger backing.
    An instruction configuration has nothing to show. *)
Definition sys_rob (c : config) : Prop :=
  forall r x8, rom_ext (ms_rom (cfg_ms c)) r -> ms_svc_pending (cfg_ms c) = Some x8 ->
  forall o, syscall_spec (sys_input segs (wrom (cfg_ms c) r) x8) (cfg_model c) o
            <-> syscall_spec (sys_input segs (cfg_ms c) x8) (cfg_model c) o.

Lemma sys_rob_instr : forall c, ms_svc_pending (cfg_ms c) = None -> sys_rob c.
Proof. intros c H r x8 _ H'. congruence. Qed.

(** By the executable check: a check that is the same for the larger backing. *)
Lemma sys_rob_of_check : forall ms m,
  (forall r x8, rom_ext (ms_rom ms) r -> ms_svc_pending ms = Some x8 ->
     forall eff, check_syscall (sys_input segs (wrom ms r) x8) eff m
                 = check_syscall (sys_input segs ms x8) eff m) ->
  sys_rob (mkCfg ms m).
Proof.
  intros ms m H r x8 Hr Hs o. cbn [cfg_ms cfg_model] in *.
  destruct o as [eff m' evs|].
  - rewrite <- !check_syscall_ok_iff. rewrite (H r x8 Hr Hs eff). reflexivity.
  - set (e0 := mkEffect (Z_to_bv 64 0) [] []).
    rewrite <- (check_syscall_err_iff (sys_input segs (wrom ms r) x8) e0 m).
    rewrite <- (check_syscall_err_iff (sys_input segs ms x8) e0 m).
    rewrite (H r x8 Hr Hs e0). reflexivity.
Qed.

(** By a characterisation of the outcomes that holds at every larger backing (the original
    backing included). *)
Lemma sys_rob_of_char : forall ms m x8 (Q : outcome SyscallEffect -> Prop),
  ms_svc_pending ms = Some x8 ->
  (forall r, rom_ext (ms_rom ms) r ->
     forall o, syscall_spec (sys_input segs (wrom ms r) x8) m o <-> Q o) ->
  sys_rob (mkCfg ms m).
Proof.
  intros ms m x8 Q Hs HQ r x8' Hr Hs' o. cbn [cfg_ms cfg_model] in *.
  rewrite Hs in Hs'. injection Hs' as <-.
  rewrite (HQ r Hr o).
  pose proof (HQ (ms_rom ms) (rom_ext_refl _) o) as H0. rewrite wrom_eta in H0.
  symmetry. exact H0.
Qed.

Lemma sys_input_wrom : forall ms r x8,
  sys_input segs (wrom ms r) x8 = with_mem (sys_input segs ms x8) (ms_read_byte (wrom ms r)).
Proof. reflexivity. Qed.

(** A system call whose check reads [in_mem] only through reads that succeed on the state's own
    view: every larger view answers the check the same way. *)
Lemma sys_rob_of_with_mem : forall ms m x8,
  ms_svc_pending ms = Some x8 ->
  (forall mp, mem_ext (ms_read_byte ms) mp -> forall eff,
     check_syscall (with_mem (sys_input segs ms x8) mp) eff m
     = check_syscall (sys_input segs ms x8) eff m) ->
  sys_rob (mkCfg ms m).
Proof.
  intros ms m x8 Hs H. apply sys_rob_of_check. intros r x8' Hr Hs' eff.
  rewrite Hs in Hs'. injection Hs' as <-.
  rewrite sys_input_wrom. apply H. apply mem_ext_read_byte_wrom. exact Hr.
Qed.

(** A system call whose specification does not read [in_mem]. *)
Lemma sys_rob_memfree : forall ms m x8,
  ms_svc_pending ms = Some x8 -> memfree (bv_unsigned x8) -> sys_rob (mkCfg ms m).
Proof.
  intros ms m x8 Hs Hmf. apply sys_rob_of_check. intros r x8' Hr Hs' eff.
  rewrite Hs in Hs'. injection Hs' as <-.
  rewrite sys_input_wrom. apply Hmf. reflexivity.
Qed.

(** exit (93) and exit_group (94). *)
Lemma sys_rob_exit : forall ms m x8,
  ms_svc_pending ms = Some x8 -> (bv_unsigned x8 = 93 \/ bv_unsigned x8 = 94)%Z ->
  sys_rob (mkCfg ms m).
Proof.
  intros ms m x8 Hs [E|E]; apply (sys_rob_memfree ms m x8 Hs); rewrite E;
    first [exact memfree_93 | exact memfree_94].
Qed.

(** writev (66) whose iovec array and (clamped) buffers read in full. *)
Lemma sys_rob_writev : forall ms m x8 iovs bs,
  ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 66%Z ->
  import_iovecs (ms_read_byte ms) (in_arg (sys_input segs ms x8) 1)
                (iovcnt32 (in_arg (sys_input segs ms x8) 2)) = ImpOk iovs ->
  gather_iovecs (ms_read_byte ms) (cap_iovecs iovs) = Some bs ->
  sys_rob (mkCfg ms m).
Proof.
  intros ms m x8 iovs bs Hs Hno Himp Hg. apply (sys_rob_of_with_mem ms m x8 Hs). intros mp Hx eff.
  rewrite (check_syscall_66 (with_mem (sys_input segs ms x8) mp) eff m Hno),
          (check_syscall_66 (sys_input segs ms x8) eff m Hno).
  exact (check_writev_ext (sys_input segs ms x8) mp (fd32 (in_arg (sys_input segs ms x8) 0))
           (in_arg (sys_input segs ms x8) 1) (in_arg (sys_input segs ms x8) 2) eff m iovs bs Hx Himp Hg).
Qed.

(** readv (65) whose iovec array reads in full. *)
Lemma sys_rob_readv : forall ms m x8 iovs,
  ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 65%Z ->
  import_iovecs (ms_read_byte ms) (in_arg (sys_input segs ms x8) 1)
                (iovcnt32 (in_arg (sys_input segs ms x8) 2)) = ImpOk iovs ->
  sys_rob (mkCfg ms m).
Proof.
  intros ms m x8 iovs Hs Hno Himp. apply (sys_rob_of_with_mem ms m x8 Hs). intros mp Hx eff.
  rewrite (check_syscall_65 (with_mem (sys_input segs ms x8) mp) eff m Hno),
          (check_syscall_65 (sys_input segs ms x8) eff m Hno).
  exact (check_readv_ext (sys_input segs ms x8) mp (fd32 (in_arg (sys_input segs ms x8) 0))
           (in_arg (sys_input segs ms x8) 1) (in_arg (sys_input segs ms x8) 2) eff m iovs Hx Himp).
Qed.

(** openat (56) whose path read does not fault. *)
Lemma sys_rob_openat : forall ms m x8,
  ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 56%Z ->
  read_cstr (ms_read_byte ms) (in_arg (sys_input segs ms x8) 1) <> CstrFault ->
  sys_rob (mkCfg ms m).
Proof.
  intros ms m x8 Hs Hno Hnf. apply (sys_rob_of_with_mem ms m x8 Hs). intros mp Hx eff.
  rewrite (check_syscall_56 (with_mem (sys_input segs ms x8) mp) eff m Hno),
          (check_syscall_56 (sys_input segs ms x8) eff m Hno).
  exact (check_openat_ext (sys_input segs ms x8) mp (fd32 (in_arg (sys_input segs ms x8) 0))
           (in_arg (sys_input segs ms x8) 1) (in_arg (sys_input segs ms x8) 2) eff m Hx Hnf).
Qed.

(** unlinkat (35) whose path read does not fault. *)
Lemma sys_rob_unlinkat : forall ms m x8,
  ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 35%Z ->
  read_cstr (ms_read_byte ms) (in_arg (sys_input segs ms x8) 1) <> CstrFault ->
  sys_rob (mkCfg ms m).
Proof.
  intros ms m x8 Hs Hno Hnf. apply (sys_rob_of_with_mem ms m x8 Hs). intros mp Hx eff.
  rewrite (check_syscall_35 (with_mem (sys_input segs ms x8) mp) eff m Hno),
          (check_syscall_35 (sys_input segs ms x8) eff m Hno).
  exact (check_unlinkat_ext (sys_input segs ms x8) mp (fd32 (in_arg (sys_input segs ms x8) 0))
           (in_arg (sys_input segs ms x8) 1) (in_arg (sys_input segs ms x8) 2) eff m Hx Hnf).
Qed.

(** ioctl (29) with a terminal-only request. *)
Lemma sys_rob_ioctl_tty : forall ms m x8,
  ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 29%Z ->
  tty_only_request (cmd32 (in_arg (sys_input segs ms x8) 1)) = true ->
  sys_rob (mkCfg ms m).
Proof.
  intros ms m x8 Hs Hno Htty. apply (sys_rob_of_with_mem ms m x8 Hs). intros mp _ eff.
  rewrite (check_syscall_29 (with_mem (sys_input segs ms x8) mp) eff m Hno),
          (check_syscall_29 (sys_input segs ms x8) eff m Hno).
  exact (check_ioctl_tty_ext (sys_input segs ms x8) mp (fd32 (in_arg (sys_input segs ms x8) 0))
           (cmd32 (in_arg (sys_input segs ms x8) 1)) eff m Htty).
Qed.
End Seg.
