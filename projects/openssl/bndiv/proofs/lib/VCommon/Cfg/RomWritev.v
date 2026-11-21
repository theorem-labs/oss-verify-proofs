(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from openssl/punycode's writev_rob (Lib/Nodes.v) and the read lemmas of openssl/hashtable's Common/Cfg/RomWritev.v, with this unit's module paths, to show that writev's check is the same over a larger read-only backing when the reads it makes succeed. *)
(* Theorem Labs, 2026-11 (LPS 08b1429): writev's check is the same for a larger read-only
   backing, when the reads it makes succeed.

   The read lemmas ([read_bytes_map_wrom] .. [import_iovecs_accesses_wrom]) are openssl/hashtable's
   [Common/Cfg/RomWritev.v], module paths renamed ([ms_read_bytes_aux_wrom] comes from
   [RomBase]).  hashtable's [ioctl_rob] is not taken: these trees' ioctl node discharges [sys_rob] by
   its own characterisation ([Lib.NodesA.ioctl_tty_rob]).  hashtable's [writev_rob] went through its
   tree's [writev_check_gen]; this tree's writev nodes state their facts as [writev_check_nomax]
   does, so [writev_rob] below takes the shape openssl/punycode's [Lib/Nodes.v] [writev_rob_gen] has: rewrite the
   check's three memory reads ([import_iovecs], its copy-in record, [writev_gathered]) at the
   larger view, and the two checks are the same term.

   [check_writev] (Checks/Sys/Fs/ReadWrite.v) reads [in_mem] only through those three. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon Require Import SimInv CatSim FileSim.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon Require LibWritev.
From OSSVerify.Proofs.openssl.bndiv.lib.Lib Require RelSpec.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon.Cfg Require Import RomBase.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

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

(** A writev node whose iovec array imports, whose buffers read in full and whose total is
    under the transfer cap is robust to a larger backing. *)
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
  rewrite (LibWritev.check_syscall_writev (sys_input segs (wrom ms r) x8) eff model) by exact Hno.
  rewrite (LibWritev.check_syscall_writev (sys_input segs ms x8) eff model) by exact Hno.
  rewrite !in_arg0_si, !in_arg1_si, !in_arg2_si.
  change (ms_gpr (wrom ms r) 0) with (ms_gpr ms 0).
  change (ms_gpr (wrom ms r) 1) with (ms_gpr ms 1).
  change (ms_gpr (wrom ms r) 2) with (ms_gpr ms 2).
  rewrite H1.
  unfold check_writev. rewrite !in_mem_si. rewrite Hn.
  rewrite (import_iovecs_accesses_wrom ms r iov n iovs Hr Himp).
  rewrite (import_iovecs_wrom ms r iov n iovs Hr Himp), Himp.
  cbv beta iota zeta.
  unfold writev_gathered. rewrite Hcap.
  rewrite (RelSpec.gather_prefix_full _ _ _ (gather_iovecs_wrom iovs ms r bs Hr Hg)).
  rewrite (RelSpec.gather_prefix_full _ _ _ Hg).
  reflexivity.
Qed.

(** A writev node whose iovec array imports and whose iovecs total nothing: the check answers
    0 from the array's copy-in record alone. *)
Lemma writev_rob_zero : forall ms model x8 iovs (iov n : word),
  ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 66%Z ->
  ms_gpr ms 1 = iov -> iovcnt32 (ms_gpr ms 2) = n ->
  import_iovecs (ms_read_byte ms) iov n = ImpOk iovs ->
  cap_iovecs iovs = iovs ->
  iovs_total iovs = 0%Z ->
  sys_rob segs (mkCfg ms model).
Proof.
  intros ms model x8 iovs iov n Hs Hno H1 Hn Himp Hcap Htot.
  apply sys_rob_of_check. intros r x8' Hr Hs' eff. rewrite Hs in Hs'. injection Hs' as <-.
  rewrite (LibWritev.check_syscall_writev (sys_input segs (wrom ms r) x8) eff model) by exact Hno.
  rewrite (LibWritev.check_syscall_writev (sys_input segs ms x8) eff model) by exact Hno.
  rewrite !in_arg0_si, !in_arg1_si, !in_arg2_si.
  change (ms_gpr (wrom ms r) 0) with (ms_gpr ms 0).
  change (ms_gpr (wrom ms r) 1) with (ms_gpr ms 1).
  change (ms_gpr (wrom ms r) 2) with (ms_gpr ms 2).
  rewrite H1.
  unfold check_writev. rewrite !in_mem_si. rewrite Hn.
  rewrite (import_iovecs_accesses_wrom ms r iov n iovs Hr Himp).
  rewrite (import_iovecs_wrom ms r iov n iovs Hr Himp), Himp.
  cbv beta iota zeta.
  rewrite Hcap, Htot. change (Z.eqb 0 0) with true. cbv beta iota.
  reflexivity.
Qed.
End Seg.
