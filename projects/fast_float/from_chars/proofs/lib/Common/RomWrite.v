(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: [RomBase.sys_rob] at the openat, ioctl and writev nodes of this tree's walks: the read lemmas and the openat and ioctl parts from cjson/cjson_read_fuzzer's lib/RomWrite.v, the writev part from openssl/bignum's RomWritev.v writev_rob, restated over any two memory views with the dispatch fact proved here. *)
(* Theorem Labs, 2026-11 (LPS 727298f3): [RomBase.sys_rob] for the memory-reading system calls of
   this tree's walks: openat (56), ioctl with a terminal-only request (29) and writev (66).
   The read lemmas and the openat and ioctl parts are cjson/cjson_read_fuzzer lib/RomWrite.v,
   module paths renamed and without the two lemmas [RomBase] already has; the writev part is
   openssl/bignum lib/VCommon/Cfg/RomWritev.v's [writev_rob], restated over any two memory
   views [mp], [mp'] with [mem_ext mp mp'] and with the dispatch fact proved here.

   Each check reads [in_mem] only through reads that succeed at the node ([read_cstr] and
   [cstr_access_len_aux] over openat's path; [import_iovecs], [import_iovecs_accesses] and
   [writev_gathered] over writev's array and buffers), so a larger view answers them the same
   way.  ioctl with a terminal-only request reads no memory at all. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import Prelude.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import RomBase.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

(** * Reads that succeed *)

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

(** * openat *)

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

Lemma rob_check_syscall_56 : forall ms x8 eff m,
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
  rewrite (rob_check_syscall_56 (wrom ms r) x8 eff model Hno), (rob_check_syscall_56 ms x8 eff model Hno).
  rewrite sys_input_wrom.
  change (ms_gpr (wrom ms r) 0) with (ms_gpr ms 0). change (ms_gpr (wrom ms r) 1) with (ms_gpr ms 1).
  change (ms_gpr (wrom ms r) 2) with (ms_gpr ms 2).
  apply check_openat_ext.
  - change (in_mem (sys_input segs ms x8)) with (ms_read_byte ms). apply mem_ext_read_byte_wrom. exact Hrr.
  - change (in_mem (sys_input segs ms x8)) with (ms_read_byte ms). exact Hnf.
Qed.

(** * ioctl *)

Lemma rob_check_syscall_29 : forall ms x8 eff m,
  bv_unsigned x8 = 29%Z ->
  check_syscall (sys_input segs ms x8) eff m
  = check_ioctl (sys_input segs ms x8) (fd32 (ms_gpr ms 0)) (cmd32 (ms_gpr ms 1)) eff m.
Proof.
  intros ms x8 eff m Hno. unfold check_syscall.
  change (in_sysno (sys_input segs ms x8)) with x8. rewrite Hno. reflexivity.
Qed.

(** An ioctl node whose request is a terminal-only one: every arm of [check_ioctl] answers it
    without reading [in_mem] (-ENOTTY, or unmodeled). *)
Lemma ioctl_rob_tty : forall ms model x8,
  ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 29%Z ->
  tty_only_request (cmd32 (ms_gpr ms 1)) = true ->
  sys_rob segs (mkCfg ms model).
Proof.
  intros ms model x8 Hs Hno Ht. apply sys_rob_of_check. intros r x8' Hr Hs' eff.
  rewrite Hs in Hs'. injection Hs' as <-.
  rewrite (rob_check_syscall_29 (wrom ms r) x8 eff model Hno), (rob_check_syscall_29 ms x8 eff model Hno).
  change (ms_gpr (wrom ms r) 0) with (ms_gpr ms 0). change (ms_gpr (wrom ms r) 1) with (ms_gpr ms 1).
  unfold check_ioctl. rewrite !Ht.
  destruct (fd_lookup (m_fds model) (fd32 (ms_gpr ms 0))) as [e|]; [destruct e|]; reflexivity.
Qed.

(** * writev *)

Lemma rob_check_syscall_66 : forall ms x8 eff m,
  bv_unsigned x8 = 66%Z ->
  check_syscall (sys_input segs ms x8) eff m
  = check_writev (sys_input segs ms x8) (fd32 (ms_gpr ms 0)) (ms_gpr ms 1) (ms_gpr ms 2) eff m.
Proof.
  intros ms x8 eff m Hno. unfold check_syscall.
  change (in_sysno (sys_input segs ms x8)) with x8. rewrite Hno. reflexivity.
Qed.

(** A writev node whose iovec array imports and whose buffers read in full: the check's three
    memory reads ([import_iovecs], its copy-in record, [writev_gathered]) are the same at the
    larger view, so the two checks are the same term. *)
Lemma writev_rob : forall ms model x8 iovs bs (iov n : word),
  ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 66%Z ->
  ms_gpr ms 1 = iov -> iovcnt32 (ms_gpr ms 2) = n ->
  import_iovecs (ms_read_byte ms) iov n = ImpOk iovs ->
  cap_iovecs iovs = iovs ->
  gather_iovecs (ms_read_byte ms) iovs = Some bs ->
  sys_rob segs (mkCfg ms model).
Proof.
  intros ms model x8 iovs bs iov n Hs Hno H1 Hn Himp Hcap Hg.
  apply sys_rob_of_check. intros r x8' Hr Hs' eff. rewrite Hs in Hs'. injection Hs' as <-.
  rewrite (rob_check_syscall_66 (wrom ms r) x8 eff model Hno), (rob_check_syscall_66 ms x8 eff model Hno).
  change (ms_gpr (wrom ms r) 0) with (ms_gpr ms 0).
  change (ms_gpr (wrom ms r) 1) with (ms_gpr ms 1).
  change (ms_gpr (wrom ms r) 2) with (ms_gpr ms 2).
  rewrite H1.
  pose proof (mem_ext_read_byte_wrom ms r Hr) as Hx.
  unfold check_writev. rewrite Hn.
  change (in_mem (sys_input segs (wrom ms r) x8)) with (ms_read_byte (wrom ms r)).
  change (in_mem (sys_input segs ms x8)) with (ms_read_byte ms).
  rewrite (import_iovecs_accesses_ext _ _ iov n iovs Hx Himp).
  rewrite (import_iovecs_ext _ _ iov n iovs Hx Himp), Himp.
  cbv beta iota zeta.
  unfold writev_gathered. rewrite Hcap.
  rewrite (gather_prefix_full _ _ _ (gather_iovecs_ext iovs _ _ bs Hx Hg)).
  rewrite (gather_prefix_full _ _ _ Hg).
  reflexivity.
Qed.

(** A writev node whose iovec array imports and whose iovecs total nothing: the check answers
    0 from the array's copy-in record alone. *)
Lemma writev_rob_zero : forall ms model x8 iovs (iov n : word),
  ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 66%Z ->
  ms_gpr ms 1 = iov -> iovcnt32 (ms_gpr ms 2) = n ->
  import_iovecs (ms_read_byte ms) iov n = ImpOk iovs ->
  Z.eqb (iovs_total (cap_iovecs iovs)) 0 = true ->
  sys_rob segs (mkCfg ms model).
Proof.
  intros ms model x8 iovs iov n Hs Hno H1 Hn Himp Htot.
  apply sys_rob_of_check. intros r x8' Hr Hs' eff. rewrite Hs in Hs'. injection Hs' as <-.
  rewrite (rob_check_syscall_66 (wrom ms r) x8 eff model Hno), (rob_check_syscall_66 ms x8 eff model Hno).
  change (ms_gpr (wrom ms r) 0) with (ms_gpr ms 0).
  change (ms_gpr (wrom ms r) 1) with (ms_gpr ms 1).
  change (ms_gpr (wrom ms r) 2) with (ms_gpr ms 2).
  rewrite H1.
  pose proof (mem_ext_read_byte_wrom ms r Hr) as Hx.
  unfold check_writev. rewrite Hn.
  change (in_mem (sys_input segs (wrom ms r) x8)) with (ms_read_byte (wrom ms r)).
  change (in_mem (sys_input segs ms x8)) with (ms_read_byte ms).
  rewrite (import_iovecs_accesses_ext _ _ iov n iovs Hx Himp).
  rewrite (import_iovecs_ext _ _ iov n iovs Hx Himp), Himp.
  cbv beta iota zeta. rewrite Htot. reflexivity.
Qed.

(** A pending system call whose number is a known one that reads no memory. *)
Lemma rob_memfree_no : forall ms model x8 (no : Z),
  ms_svc_pending ms = Some x8 -> bv_unsigned x8 = no -> memfree no ->
  sys_rob segs (mkCfg ms model).
Proof. intros ms model x8 no Hs Hn Hm. apply (sys_rob_memfree segs ms model x8 Hs). rewrite Hn. exact Hm. Qed.

(** [sys_rob] reads a state through [sys_input] and the pending number only: two states that agree
    on the registers, the memory, the backing and the pending call agree on it. *)
Lemma sys_rob_same_input : forall ms ms' model,
  ms_svc_pending ms = ms_svc_pending ms' -> ms_regs ms = ms_regs ms' -> ms_mem ms = ms_mem ms' ->
  ms_rom ms = ms_rom ms' ->
  sys_rob segs (mkCfg ms' model) -> sys_rob segs (mkCfg ms model).
Proof.
  intros [] [] model Hs Hr Hm Hrom H. cbn in Hs, Hr, Hm, Hrom. subst.
  unfold sys_rob in *. cbn [cfg_ms cfg_model] in *. exact H.
Qed.

(** * By the specification: both inputs have the same outcomes *)
Lemma sys_rob_of_spec : forall ms model x8 (S : outcome SyscallEffect -> Prop),
  ms_svc_pending ms = Some x8 ->
  (forall r, rom_ext (ms_rom ms) r ->
     forall o, syscall_spec (sys_input segs (wrom ms r) x8) model o <-> S o) ->
  sys_rob segs (mkCfg ms model).
Proof.
  intros ms model x8 S Hs H r x8' Hr Hs' o. cbn [cfg_ms cfg_model] in *.
  rewrite Hs in Hs'. injection Hs' as <-.
  rewrite (H r Hr o). pose proof (H (ms_rom ms) (rom_ext_refl _) o) as E.
  rewrite wrom_eta in E. symmetry. exact E.
Qed.
End Seg.

(** [sys_rob] at an instruction configuration, or at a system call that reads no memory whose
    number a hypothesis names (as [bv_unsigned x8 = n], as the number of a pending input, or as
    [x8 = Z_to_bv 64 n]). *)
Ltac rob_tac :=
  first
    [ apply sys_rob_instr; cbn [cfg_ms]; first [assumption | reflexivity]
    | eapply sys_rob_memfree; [first [eassumption | reflexivity] |];
      repeat match goal with
             | H : bv_unsigned (in_sysno (sys_input ?s ?m ?x)) = _ |- memfree (bv_unsigned ?x) =>
                 change (bv_unsigned x) with (bv_unsigned (in_sysno (sys_input s m x))); rewrite H
             | H : bv_unsigned ?x = _ |- memfree (bv_unsigned ?x) => rewrite H
             | H : ?x = Z_to_bv 64 _ |- memfree (bv_unsigned ?x) =>
                 rewrite H; rewrite Z_to_bv_unsigned; rewrite bv_wrap_small by (unfold bv_modulus; lia)
             end;
      memfree_lit ].
