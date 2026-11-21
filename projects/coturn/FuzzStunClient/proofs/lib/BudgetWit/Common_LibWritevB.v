(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from Common/LibWritev.v: the R-typed declarations restated over the budget carrier, with twin modules imported last. *)
(* Modified by Theorem Labs, 2026-11: for LPS 727298f3, the writev node's check is derived once for any state, so the read-only-backing premise follows (sys_rob_of_lite_check), and the iovec ledger is the array's own (iovec_entry_accesses_of_array). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import CheckLite.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import
  SimInv ExitSim CatSim CatExec PropExec SeqExec Hoare ShapeAlg Nodes FileSim AgentLib AgentNodes.
Import ListNotations.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import LibWritev.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.BudgetWit Require Import Common_AgentNodesB Common_NodesB Rzb.
Local Instance libwritev_fx : PropExec.FPState := PropExec.fx0.

Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Open Scope bv_scope.
Lemma rzb_wall : forall segs c (ch : word) (bs : list byte) (K : TSet),
  (1 <= length bs)%nat -> K [] ->
  Rzb.rzb segs c (t_alt (fun i : wr_index bs =>
     t_emit (map (WriteEv ch) (firstn (proj1_sig i) bs))
            (t_emit (map (WriteEv ch) (skipn (proj1_sig i) bs)) K))) ->
  Rzb.rzb segs c (t_emit (map (WriteEv ch) bs) K).
Proof.
  intros segs c ch bs K Hnb HK H. eapply Rzb.rzb_conseq; [exact H | apply t_alt_wall; assumption].
Qed.
Section WithSegs.
Variable segs : list Segment.
Lemma read_u64_rdn : forall ms a v,
  ms_rom ms = seg_rom segs ->
  rdn segs (ms_mem ms) a 8%nat = Some (word_to_le_bytes 8 v) ->
  read_u64 (ms_read_byte ms) a = Some v.
Proof.
  intros ms a v Hrom H. unfold read_u64.
  rewrite read_bytes_map_read_byte, (ms_read_bytes_rdn segs) by exact Hrom.
  change (word_to_nat (Z_to_bv 64 8)) with 8%nat. rewrite H.
  f_equal. apply le_word_v. apply bytes_le_to_Z_8.
Qed.
Lemma read_iovec_entry_of_array : forall ms b n r iov,
  ms_rom ms = seg_rom segs ->
  (LibWritev.iov_array segs) (ms_mem ms) iov ((b, n) :: r) ->
  read_iovec_entry (ms_read_byte ms) iov = IovEntry b n.
Proof.
  intros ms b n r iov Hrom (Hb & Hn & Hlt & _). unfold read_iovec_entry.
  rewrite (read_u64_rdn ms iov b Hrom Hb).
  rewrite LibWritev.bv_add_Zform. change (bv_unsigned (8 : word)) with 8%Z.
  rewrite (read_u64_rdn ms _ n Hrom Hn).
  rewrite (proj2 (Z.leb_gt _ _) Hlt). reflexivity.
Qed.
Lemma rzb_writev1_zero : forall regs (pc : word) mem model w (fd : Z) (iov b1 : word) K,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  fd_lookup (m_fds model) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd)) ->
  (0 < fd < 2^31)%Z ->
  getr regs 17 = Z_to_bv 64 66 ->
  getr regs 10 = Z_to_bv 64 fd ->
  getr regs 11 = iov ->
  getr regs 12 = Z_to_bv 64 1 ->
  rdn segs mem iov 8%nat = Some (word_to_le_bytes 8 b1) ->
  rdn segs mem (Z_to_bv 64 (bv_unsigned iov + 8)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
  (bv_unsigned iov + 16 <= TASK_SIZE)%Z ->
  (bv_unsigned b1 <= TASK_SIZE)%Z ->
  (0 <= rw_bytes_max)%Z ->
  Rzb.rzb segs (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 0)) (v_addi pc 4) mem (seg_rom segs)) model) K ->
  Rzb.rzb segs (mkCfg (mkst regs pc mem (seg_rom segs)) model) K.
Proof.
  intros regs pc mem model w fd iov b1 K HF HE Hh Hlazy Hfd Hfdr H17 H10 H11 H12 Rb1 Rn1 Hiok Hb1 Hmax Hc.
  eapply Common_AgentNodesB.rzb_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
  set (ms := epend regs pc mem (seg_rom segs) (getr regs 17)).
  assert (Hno : bv_unsigned (getr regs 17) = 66%Z) by (rewrite H17; apply u64_lit; lia).
  assert (Harr : (LibWritev.iov_array segs) (ms_mem ms) iov [(b1, Z_to_bv 64 0)]).
  { cbn [LibWritev.iov_array ms_mem ms epend]. refine (conj Rb1 (conj Rn1 (conj _ I))). rewrite u64_lit by lia. lia. }
  (* LPS 08b1429, [Rzb.rzb_node]'s [RomBase.sys_rob]: the check is derived ONCE, generically in
     the state, so the node and its [sys_rob] obligation are the same derivation at [ms] and at
     [RomBase.wrom ms r] -- [Common.LibWritev]'s writev1_zero node, over [rzb].  [wrom] keeps
     [ms_mem] and [ms_regs], and [with_vdso] keeps [m_fds].
     LPS 727298f3: [State.import_iovecs_accesses]'s one-entry arm answers
     [iovec_entry_accesses mp a], not the literal [[(a, 16)]], so the ledger is
     the iovec array's own ([LibWritev.iovec_entry_accesses_of_array]). *)
  assert (Hchkg : forall (ms' : machine_state) (m' : Model),
            LibWritev.rom_covers segs ms' -> ms_mem ms' = ms_mem ms ->
            ms_gpr ms' 0 = Z_to_bv 64 fd -> ms_gpr ms' 1 = iov -> ms_gpr ms' 2 = Z_to_bv 64 1 ->
            fd_lookup (m_fds m') (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd)) ->
            forall eff, check_syscall (sys_input segs ms' (getr regs 17)) eff m'
                        = check_ret_only_copyins [(iov, 16%nat)] eff (Z_to_bv 64 0) m' []).
  { intros ms' m' Hc' Hmem' G0 G1 G2 Hfd' eff.
    assert (Harr' : (LibWritev.iov_array segs) (ms_mem ms') iov [(b1, Z_to_bv 64 0)])
      by (rewrite Hmem'; exact Harr).
    assert (Himp' : import_iovecs (ms_read_byte ms') iov (Z_to_bv 64 1) = ImpOk [(b1, Z_to_bv 64 0)]).
    { unfold import_iovecs. rewrite (proj2 (bv_eqb_eq _ _) eq_refl).
      rewrite (LibWritev.access_okb_of_le iov 16) by lia.
      rewrite (LibWritev.read_iovec_entry_of_array segs ms' b1 (Z_to_bv 64 0) [] iov Hc' Harr').
      rewrite u64_lit by lia. change (Z.min 0 MAX_RW_COUNT) with 0%Z.
      rewrite (LibWritev.access_okb_of_le b1 0) by lia. reflexivity. }
    assert (Hacc' : import_iovecs_accesses (ms_read_byte ms') iov (Z_to_bv 64 1) = [(iov, 16%nat)]).
    { unfold import_iovecs_accesses. rewrite (proj2 (bv_eqb_eq _ _) eq_refl).
      rewrite (LibWritev.access_okb_of_le iov 16) by lia.
      exact (LibWritev.iovec_entry_accesses_of_array segs ms' b1 (Z_to_bv 64 0) [] iov Hc' Harr'). }
    rewrite (LibWritev.check_syscall_writev (sys_input segs ms' (getr regs 17)) eff m')
      by (rewrite in_sysno_si; exact Hno).
    rewrite in_arg0_si, in_arg1_si, in_arg2_si.
    rewrite G0, G1, G2.
    rewrite fd32_id by (rewrite u64_lit; lia).
    unfold check_writev. rewrite Hfd'.
    replace (w_is0 (Z_to_bv 64 fd)) with false by (symmetry; apply w_is0_pos; rewrite u64_lit; lia).
    change (iovcnt32 (Z_to_bv 64 1)) with (Z_to_bv 64 1).
    rewrite in_mem_si, Himp', Hacc'.
    (* [comment removed for export] *)
    unfold cap_iovecs. cbn [cap_iovecs_aux iovs_total].
    change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. rewrite Z.min_r by (unfold MAX_RW_COUNT; lia).
    change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. cbv beta iota zeta.
    change ((0 + 0 =? 0)%Z) with true. cbv beta iota. reflexivity. }
  assert (G0 : ms_gpr ms 0 = Z_to_bv 64 fd) by (unfold ms; rewrite ms_gpr_epend0; exact H10).
  assert (G1 : ms_gpr ms 1 = iov) by (unfold ms; rewrite ms_gpr_epend1; exact H11).
  assert (G2 : ms_gpr ms 2 = Z_to_bv 64 1) by (unfold ms; rewrite ms_gpr_epend2; exact H12).
  assert (Hcov : LibWritev.rom_covers segs ms) by (apply LibWritev.rom_covers_eq; reflexivity).
  eapply (Common_NodesB.rzb_ret_only_copyins_silent segs ms model (getr regs 17) [(iov, 16%nat)] (Z_to_bv 64 0) model);
    [ exact Hh
    | reflexivity
    | apply (sys_rob_of_lite_check segs ms model (getr regs 17) eq_refl
               ltac:(rewrite Hno; reflexivity));
      intros r v eff Hre;
      rewrite (Hchkg (RomBase.wrom ms r) (with_vdso v model)
                 (LibWritev.rom_covers_wrom segs ms r Hcov Hre) eq_refl G0 G1 G2 Hfd eff);
      rewrite (Hchkg ms (with_vdso v model) Hcov eq_refl G0 G1 G2 Hfd eff); reflexivity
    | exact (Hchkg ms model Hcov eq_refl G0 G1 G2 Hfd)
    | exact Hh | exact Hlazy
    | exact (Rzb.budget_ok_num segs ms model (getr regs 17) 66 eq_refl Hno eq_refl)
    | unfold ms; rewrite adv_set_epend; exact Hc].
Qed.
End WithSegs.
