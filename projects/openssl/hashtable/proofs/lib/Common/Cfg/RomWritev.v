(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (writev's check for a larger read-only backing: [writev_check_gen] and the premises of [writev_rob] are made from projects/openssl/hashtable/proofs/lib/Common/LibWritev.v (lines 212-271, [writev_check], and lines 275-290, the premises of [rz_writev_pending]) as in the LPS 727298f3 update). *)
(* Theorem Labs, 2026-11 (LPS 08b1429): writev's check is the same for a larger read-only
   backing, when the reads it makes succeed.

   [check_writev] (Sys/Fs/ReadWrite.v) reads [in_mem] through [import_iovecs] (the iovec array:
   [read_iovec_entry], two [read_u64]), [import_iovecs_accesses] (the array's copy-in record)
   and [gather_iovecs] (the buffers, [read_bytes_map]).  A read that succeeds on a view returns
   the same bytes on any view that extends it, and the record reads only the entries' own words.
   [writev_rob] is [RomBase.sys_rob] at a writev node from the node's own premises
   ([LibWritev.writev_check]'s). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import
  SimInv ExitSim CatSim CatExec PropExec SeqExec Hoare ShapeAlg Nodes FileSim AgentLib AgentNodes LibWritev RefNodes.
From OSSVerify.Proofs.openssl.hashtable.lib.Common.Cfg Require Import RomBase.
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

(** [LibWritev.writev_check] with its two memory facts as premises. *)
Lemma writev_check_gen : forall ms x8 model (fd : Z) (iov : word) iovs bss,
  fd_lookup (m_fds model) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd)) ->
  m_channel_reader model = true ->
  (0 < fd < 2^31)%Z ->
  bv_unsigned x8 = 66%Z ->
  ms_gpr ms 0 = Z_to_bv 64 fd ->
  ms_gpr ms 1 = iov ->
  ms_gpr ms 2 = Z_to_bv 64 (Z.of_nat (length iovs)) ->
  (1 <= length iovs <= 1024)%nat ->
  import_iovecs (ms_read_byte ms) iov (Z_to_bv 64 (Z.of_nat (length iovs))) = ImpOk iovs ->
  gather_iovecs (ms_read_byte ms) iovs = Some (concat bss) ->
  let bs := concat bss in
  let tot := iovs_total iovs in
  (1 <= tot)%Z -> (tot <= 2 ^ 30)%Z ->
  let CA := import_iovecs_accesses (ms_read_byte ms) iov (Z_to_bv 64 (Z.of_nat (length iovs))) in
  forall eff, check_syscall (sys_input segs ms x8) eff model
    = match eff with
      | mkEffectU ret [] [] [] [] ci =>
          if (1 <=? bv_unsigned ret)%Z && (bv_unsigned ret <=? tot)%Z && negb (addr_is_error_b ret)
          then if access_ranges_eqb ci (CA ++ iov_prefix_accesses iovs (Z.to_nat (bv_unsigned ret)))
               then CheckOk model (map (WriteEv (Z_to_bv 64 fd)) (firstn (Z.to_nat (bv_unsigned ret)) bs))
               else CheckReject
          else CheckReject
      | _ => CheckReject
      end.
Proof.
  intros ms x8 model fd iov iovs bss Hfd Hrdr Hfdr Hno H0 H1 H2 Hcnt Himp Hg bs tot Ht1 Ht30 CA.
  fold bs in Hg.
  pose proof (gather_iovecs_length _ _ _ Hg) as Hlen. fold tot in Hlen.
  intros eff.
  rewrite (check_syscall_writev (sys_input segs ms x8) eff model) by (rewrite in_sysno_si; exact Hno).
  rewrite in_arg0_si, in_arg1_si, in_arg2_si, H0, H1, H2.
  rewrite fd32_id by (rewrite u64_lit; lia).
  assert (Hcnt32 : iovcnt32 (Z_to_bv 64 (Z.of_nat (length iovs))) = Z_to_bv 64 (Z.of_nat (length iovs))).
  { unfold iovcnt32, abi_low32. rewrite u64_lit by lia. rewrite Z.mod_small by lia. reflexivity. }
  unfold check_writev. rewrite Hfd.
  replace (w_is0 (Z_to_bv 64 fd)) with false
    by (symmetry; apply w_is0_pos; rewrite u64_lit; lia).
  rewrite in_mem_si, Hcnt32.
  rewrite Himp.
  assert (Hcap : cap_iovecs iovs = iovs).
  { unfold cap_iovecs. apply cap_iovecs_id. unfold MAX_RW_COUNT. lia. }
  unfold writev_gathered. rewrite Hcap, (gather_prefix_full _ _ _ Hg).
  cbv beta iota zeta. fold tot.
  replace ((tot =? 0)%Z) with false by (symmetry; apply Z.eqb_neq; lia).
  replace ((length bs =? 0)%nat) with false by (symmetry; apply Nat.eqb_neq; lia).
  rewrite Hrdr. change (negb true) with false.
  assert (Hlw : bv_unsigned (len_word bs) = tot).
  { unfold len_word. rewrite Hlen. apply u64_lit. lia. }
  replace (addr_is_error_b (len_word bs)) with false
    by (symmetry; unfold addr_is_error_b, two_pow_64; apply Z.ltb_ge; rewrite Hlw; lia).
  cbv beta iota.
  destruct eff as [ret ws zs us cs ci]. destruct ws; [|reflexivity]. destruct zs; [|reflexivity].
  destruct us; [|reflexivity]. destruct cs; [|reflexivity].
  rewrite Hlen. reflexivity.
Qed.

(** A writev node is robust to a larger backing. *)
Lemma writev_rob : forall ms x8 model (fd : Z) (iov : word) iovs bss,
  ms_rom ms = seg_rom segs ->
  ms_svc_pending ms = Some x8 ->
  fd_lookup (m_fds model) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd)) ->
  m_channel_reader model = true ->
  (0 < fd < 2^31)%Z ->
  bv_unsigned x8 = 66%Z ->
  ms_gpr ms 0 = Z_to_bv 64 fd ->
  ms_gpr ms 1 = iov ->
  ms_gpr ms 2 = Z_to_bv 64 (Z.of_nat (length iovs)) ->
  (1 <= length iovs <= 1024)%nat ->
  (bv_unsigned iov + 16 * Z.of_nat (length iovs) <= TASK_SIZE)%Z ->
  iov_array segs (ms_mem ms) iov iovs ->
  iov_bufs_ok iovs ->
  iov_bufs segs (ms_mem ms) iovs bss ->
  (1 <= iovs_total iovs)%Z -> (iovs_total iovs <= 2 ^ 30)%Z ->
  sys_rob segs (mkCfg ms model).
Proof.
  intros ms x8 model fd iov iovs bss Hrom Hsvc Hfd Hrdr Hfdr Hno H0 H1 H2 Hcnt Hiok Harr Hbok Hbufs Ht1 Ht30.
  apply sys_rob_of_check. intros r x8' Hr Hs eff. rewrite Hsvc in Hs. injection Hs as <-.
  pose proof (import_iovecs_of_array segs ms iovs iov Hrom Hcnt Hiok Harr Hbok) as Himp.
  pose proof (gather_of_bufs segs ms iovs bss Hrom Hbufs) as Hg.
  rewrite (writev_check_gen ms x8 model fd iov iovs bss Hfd Hrdr Hfdr Hno H0 H1 H2 Hcnt Himp Hg Ht1 Ht30 eff).
  rewrite (writev_check_gen (wrom ms r) x8 model fd iov iovs bss Hfd Hrdr Hfdr Hno H0 H1 H2 Hcnt
             (import_iovecs_wrom ms r _ _ iovs Hr Himp) (gather_iovecs_wrom iovs ms r _ Hr Hg) Ht1 Ht30 eff).
  rewrite (import_iovecs_accesses_wrom ms r _ _ iovs Hr Himp). reflexivity.
Qed.

(** [check_ioctl] (Checks/Sys/Fs/Ioctl.v) reads the input only for SIOCGIFINDEX on a datagram
    socket, and only AFTER [tty_only_request] fails.  TIOCGWINSZ (0x5413 = 21523) is a
    terminal-only request, so on every fd kind the check is the same over a larger backing.
    Decide that test FIRST and reduce the decided [if] before comparing: a [reflexivity] over an
    uncollapsed [destruct (fd_lookup ..) as [[]|]] keeps the [FdDgram] branch body, which reads
    the input, inside every other arm's goal term and does not return.  This is the shape of
    echconfiglist_parser's [Common/Cfg/RomWrite.v ioctl_tty_rob], which compiled in that
    unit's repair. *)
Lemma ioctl_tty_rob : forall ms model x8,
  ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 29%Z ->
  ms_gpr ms 1 = Z_to_bv 64 21523 ->
  sys_rob segs (mkCfg ms model).
Proof.
  intros ms model x8 Hs Hno H11. apply sys_rob_of_check. intros r x8' Hr Hs' eff.
  rewrite Hs in Hs'. injection Hs' as <-.
  rewrite !(check_syscall_29 segs _ x8 eff model Hno).
  change (ms_gpr (wrom ms r) 0) with (ms_gpr ms 0).
  change (ms_gpr (wrom ms r) 1) with (ms_gpr ms 1).
  rewrite H11.
  assert (Htty : tty_only_request (cmd32 (Z_to_bv 64 21523)) = true) by (vm_compute; reflexivity).
  unfold check_ioctl. rewrite !Htty. destruct (fd_lookup _ _) as [[]|]; lazy beta iota; reflexivity.
Qed.

End Seg.
