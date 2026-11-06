(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.openssl.bignum.lib.VCommon Require Import
  PropExec SimInv ExitSim CatSim CatExec SeqExec StreamExec FileSim ShapeAlg ShapeAlgCfg Nodes AgentLib AgentNodes
  Hoare StoreOk LibWritev NodesCfg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Lemma rzc_wall : forall segs cfg c (ch : word) (bs : list byte) (K : TSet),
  (1 <= length bs)%nat -> K [] ->
  realizes_cfg segs cfg c (t_alt (fun i : wr_index bs =>
     t_emit (map (WriteEv ch) (firstn (proj1_sig i) bs))
            (t_emit (map (WriteEv ch) (skipn (proj1_sig i) bs)) K))) ->
  realizes_cfg segs cfg c (t_emit (map (WriteEv ch) bs) K).
Proof.
  intros segs cfg c ch bs K Hnb HK H. eapply rzc_conseq; [exact H | apply t_alt_wall; assumption].
Qed.

Section WithSegs.
Context {asanreflect_fx : PropExec.FPState}.
Variable segs : list Segment.
Variable cfg : SpuriousCfg.

Lemma writev_check_nomax : forall ms x8 model (fd : Z) (iov : word) iovs bss,
  ms_rom ms = seg_rom segs ->
  fd_lookup (m_fds model) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd)) ->
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
  let bs := concat bss in
  let tot := iovs_total iovs in
  (1 <= tot)%Z -> (tot <= 2 ^ 30)%Z ->
  let CA := import_iovecs_accesses (ms_read_byte ms) iov (Z_to_bv 64 (Z.of_nat (length iovs))) in
  Z.of_nat (length bs) = tot /\
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
  intros ms x8 model fd iov iovs bss Hrom Hfd Hfdr Hno H0 H1 H2 Hcnt Hiok Harr Hbok Hbufs bs tot Ht1 Ht30 CA.
  pose proof (gather_of_bufs segs ms iovs bss Hrom Hbufs) as Hg. fold bs in Hg.
  pose proof (gather_iovecs_length _ _ _ Hg) as Hlen. fold tot in Hlen.
  split; [exact Hlen|].
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
  rewrite (import_iovecs_of_array segs ms iovs iov Hrom Hcnt Hiok Harr Hbok).

  assert (Hcap : cap_iovecs iovs = iovs).
  { unfold cap_iovecs. apply cap_iovecs_id. unfold MAX_RW_COUNT. lia. }
  unfold writev_gathered. rewrite Hcap, (gather_prefix_full _ _ _ Hg).
  cbv beta iota zeta. fold tot.
  replace ((tot =? 0)%Z) with false by (symmetry; apply Z.eqb_neq; lia).
  replace ((length bs =? 0)%nat) with false by (symmetry; apply Nat.eqb_neq; lia).
  assert (Hlw : bv_unsigned (len_word bs) = tot).
  { unfold len_word. rewrite Hlen. apply u64_lit. lia. }
  replace (addr_is_error_b (len_word bs)) with false
    by (symmetry; unfold addr_is_error_b, two_pow_64; apply Z.ltb_ge; rewrite Hlw; lia).
  cbv beta iota.
  destruct eff as [ret ws zs us cs ci]. destruct ws; [|reflexivity]. destruct zs; [|reflexivity].
  destruct us; [|reflexivity]. destruct cs; [|reflexivity].
  rewrite Hlen. reflexivity.
Qed.

End WithSegs.
