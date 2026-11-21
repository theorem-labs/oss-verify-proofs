(* SPDX-License-Identifier: MIT *)
(* Theorem Labs, 2026-11 (LPS 08b1429): writev's and ioctl's memory reads over a larger
   read-only backing.  From openssl/hashtable Common/Cfg/RomWritev.v,
   split for leptonica: the reads of the iovec array and of the buffers
   are here; [writev_check_gen] and [writev_rob] need [LibWritev]'s array facts and are in
   [LibWritev.v] (which this file must not import: [LibWritev]'s writev node uses them).

   [check_writev] (Sys/Fs/ReadWrite.v) reads [in_mem] through [import_iovecs] (the iovec array:
   [read_iovec_entry], two [read_u64]), [import_iovecs_accesses] (the array's copy-in record)
   and [gather_iovecs] (the buffers, [read_bytes_map]).  A read that succeeds on a view returns
   the same bytes on any view that extends it, and the record reads only the entries' own words. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common Require Import CatSim FileSim.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Cfg Require Import RomBase.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

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

Lemma read_bytes_map_wrom : forall ms r a len bs, rom_ext (ms_rom ms) r ->
  read_bytes_map (ms_read_byte ms) a len = Some bs ->
  read_bytes_map (ms_read_byte (wrom ms r)) a len = Some bs.
Proof.
  intros ms r a len bs Hr. rewrite !read_bytes_map_read_byte. unfold ms_read_bytes.
  apply ms_read_bytes_aux_wrom. exact Hr.
Qed.

Lemma read_u64_wrom : forall ms r a v, rom_ext (ms_rom ms) r ->
  read_u64 (ms_read_byte ms) a = Some v -> read_u64 (ms_read_byte (wrom ms r)) a = Some v.
Proof.
  intros ms r a v Hr. unfold read_u64.
  destruct (read_bytes_map (ms_read_byte ms) a (Z_to_bv 64 8)) as [bs|] eqn:E; [|intro H; discriminate H].
  rewrite (read_bytes_map_wrom ms r a _ bs Hr E). intro H; exact H.
Qed.

Lemma read_iovec_entry_wrom : forall ms r a b n, rom_ext (ms_rom ms) r ->
  read_iovec_entry (ms_read_byte ms) a = IovEntry b n ->
  read_iovec_entry (ms_read_byte (wrom ms r)) a = IovEntry b n.
Proof.
  intros ms r a b n Hr. unfold read_iovec_entry.
  destruct (read_u64 (ms_read_byte ms) a) as [v1|] eqn:E1; [|intro H; discriminate H].
  destruct (read_u64 (ms_read_byte ms) (a + 8)) as [v2|] eqn:E2; [|intro H; discriminate H].
  rewrite (read_u64_wrom ms r a v1 Hr E1), (read_u64_wrom ms r (a + 8) v2 Hr E2). intro H; exact H.
Qed.

Lemma iovec_entry_accesses_wrom : forall ms r a b n, rom_ext (ms_rom ms) r ->
  read_iovec_entry (ms_read_byte ms) a = IovEntry b n ->
  iovec_entry_accesses (ms_read_byte (wrom ms r)) a = iovec_entry_accesses (ms_read_byte ms) a.
Proof.
  intros ms r a b n Hr. unfold read_iovec_entry, iovec_entry_accesses.
  destruct (read_u64 (ms_read_byte ms) a) as [v1|] eqn:E1; [|intro H; discriminate H].
  destruct (read_u64 (ms_read_byte ms) (a + 8)) as [v2|] eqn:E2; [|intro H; discriminate H].
  intros _. rewrite (read_u64_wrom ms r a v1 Hr E1), (read_u64_wrom ms r (a + 8) v2 Hr E2). reflexivity.
Qed.

Lemma copy_iovecs_aux_wrom : forall k ms r a iovs, rom_ext (ms_rom ms) r ->
  copy_iovecs_aux (ms_read_byte ms) a k = ImpOk iovs ->
  copy_iovecs_aux (ms_read_byte (wrom ms r)) a k = ImpOk iovs.
Proof.
  induction k as [|k IH]; intros ms r a iovs Hr H; [exact H|].
  cbn [copy_iovecs_aux] in *.
  destruct (read_iovec_entry (ms_read_byte ms) a) as [b n| |] eqn:E; try discriminate H.
  rewrite (read_iovec_entry_wrom ms r a b n Hr E).
  destruct (copy_iovecs_aux (ms_read_byte ms) (a + 16) k) as [rest| |] eqn:E2; try discriminate H.
  rewrite (IH ms r (a + 16) rest Hr E2). exact H.
Qed.

Lemma copy_iovecs_accesses_wrom : forall k ms r a iovs, rom_ext (ms_rom ms) r ->
  copy_iovecs_aux (ms_read_byte ms) a k = ImpOk iovs ->
  copy_iovecs_accesses (ms_read_byte (wrom ms r)) a k = copy_iovecs_accesses (ms_read_byte ms) a k.
Proof.
  induction k as [|k IH]; intros ms r a iovs Hr H; [reflexivity|].
  cbn [copy_iovecs_aux copy_iovecs_accesses] in *.
  destruct (read_iovec_entry (ms_read_byte ms) a) as [b n| |] eqn:E; try discriminate H.
  rewrite (iovec_entry_accesses_wrom ms r a b n Hr E), (read_iovec_entry_wrom ms r a b n Hr E).
  destruct (copy_iovecs_aux (ms_read_byte ms) (a + 16) k) as [rest| |] eqn:E2; try discriminate H.
  rewrite (IH ms r (a + 16) rest Hr E2). reflexivity.
Qed.

Lemma gather_iovecs_wrom : forall iovs ms r bs, rom_ext (ms_rom ms) r ->
  gather_iovecs (ms_read_byte ms) iovs = Some bs -> gather_iovecs (ms_read_byte (wrom ms r)) iovs = Some bs.
Proof.
  induction iovs as [|[b n] rest IH]; intros ms r bs Hr H; [exact H|].
  cbn [gather_iovecs] in *.
  destruct (read_bytes_map (ms_read_byte ms) b n) as [x|] eqn:E; [|discriminate H].
  rewrite (read_bytes_map_wrom ms r b n x Hr E).
  destruct (gather_iovecs (ms_read_byte ms) rest) as [y|] eqn:E2; [|discriminate H].
  rewrite (IH ms r y Hr E2). exact H.
Qed.

Lemma import_iovecs_wrom : forall ms r a n iovs, rom_ext (ms_rom ms) r ->
  import_iovecs (ms_read_byte ms) a n = ImpOk iovs -> import_iovecs (ms_read_byte (wrom ms r)) a n = ImpOk iovs.
Proof.
  intros ms r a n iovs Hr. unfold import_iovecs.
  destruct (bv_eqb n (Z_to_bv 64 1)).
  - destruct (negb (access_okb a 16)); [intro H; exact H|].
    destruct (read_iovec_entry (ms_read_byte ms) a) as [b l| |] eqn:E; try (intro H; discriminate H).
    rewrite (read_iovec_entry_wrom ms r a b l Hr E). intro H; exact H.
  - destruct (bv_eqb n (Z_to_bv 64 0)); [intro H; exact H|].
    destruct (IOV_MAX <? bv_unsigned n)%Z; [intro H; exact H|].
    destruct (negb (access_okb a (16 * bv_unsigned n))); [intro H; exact H|].
    destruct (copy_iovecs_aux (ms_read_byte ms) a (word_to_nat n)) as [l| |] eqn:E; try (intro H; discriminate H).
    rewrite (copy_iovecs_aux_wrom _ ms r a l Hr E). intro H; exact H.
Qed.

Lemma import_iovecs_accesses_wrom : forall ms r a n iovs, rom_ext (ms_rom ms) r ->
  import_iovecs (ms_read_byte ms) a n = ImpOk iovs ->
  import_iovecs_accesses (ms_read_byte (wrom ms r)) a n = import_iovecs_accesses (ms_read_byte ms) a n.
Proof.
  intros ms r a n iovs Hr. unfold import_iovecs, import_iovecs_accesses.
  destruct (bv_eqb n (Z_to_bv 64 1)).
  - destruct (negb (access_okb a 16)); [reflexivity|].
    destruct (read_iovec_entry (ms_read_byte ms) a) as [b l| |] eqn:E; try (intro H; discriminate H).
    intros _. exact (iovec_entry_accesses_wrom ms r a b l Hr E).
  - destruct (bv_eqb n (Z_to_bv 64 0)); [reflexivity|].
    destruct (IOV_MAX <? bv_unsigned n)%Z; [reflexivity|].
    destruct (negb (access_okb a (16 * bv_unsigned n))); [reflexivity|].
    destruct (copy_iovecs_aux (ms_read_byte ms) a (word_to_nat n)) as [l| |] eqn:E; try (intro H; discriminate H).
    intros _. exact (copy_iovecs_accesses_wrom _ ms r a l Hr E).
Qed.

Section Seg.
Variable segs : list Segment.

Lemma rob_check_syscall_29 : forall ms x8 eff m,
  bv_unsigned x8 = 29%Z ->
  check_syscall (sys_input segs ms x8) eff m
  = check_ioctl (sys_input segs ms x8) (fd32 (ms_gpr ms 0)) (cmd32 (ms_gpr ms 1)) eff m.
Proof. intros ms x8 eff m Hno. unfold check_syscall. rewrite in_sysno_si, Hno. reflexivity. Qed.


(* LPS 08b1429, the specialised form.  A terminal request on an fd
   whose kind the CALLER already knows answers -ENOTTY whatever [in_mem] holds, so the node
   reads the same over a larger backing.  Unlike [ioctl_rob] this NEVER FORMS [check_ioctl]'s
   15-arm match: the lookup is a premise, so [rewrite Hl] puts a known constructor in the
   scrutinee and iota picks one arm with no case analysis, and [sys_rob_of_closed] gives the
   check in closed form so the two backings are never compared to each other.  That is why
   there is nothing here for a [reflexivity] to walk into. *)
Lemma ioctl_tty_rob : forall ms model c,
  ms_svc_pending ms = Some (Z_to_bv 64 29) ->
  ms_gpr ms 1 = Z_to_bv 64 21523 ->
  fd_lookup (m_fds model) (fd32 (ms_gpr ms 0)) = Some (FdChannel c) ->
  sys_rob segs (mkCfg ms model).
Proof.
  intros ms model c Hsvc Ha1 Hl.
  apply (sys_rob_of_closed segs ms model
           (fun eff => check_ret_only eff (errno_ret ENOTTY) model [])).
  intros ms' Hr Hregs Hmem Hsp x8 Hs eff.
  rewrite Hsp, Hsvc in Hs. injection Hs as <-.
  rewrite (rob_check_syscall_29 ms' (Z_to_bv 64 29) eff model
             ltac:(change (bv_unsigned (Z_to_bv 64 29)) with 29%Z; reflexivity)).
  unfold check_ioctl, ms_gpr in *. rewrite Hregs, Ha1, Hl.
  lazy beta iota.
  replace (tty_only_request (cmd32 (Z_to_bv 64 21523))) with true
    by (vm_compute; reflexivity).
  reflexivity.
Qed.
End Seg.
