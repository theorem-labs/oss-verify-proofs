(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Classical.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import Amb RelSpec
  SimInv ExitSim PropExec CatExec CatSim SeqExec StreamExec MmapSim AllocSim FileSim
  ShapeAlg Nodes StoreOk AgentLib AgentNodes PlacementGap RefNodes DivergeSim SRealizes.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Section Prim.
Context {fx : FPState}.
Variable segs : list Segment.

#[local] Notation node_det := (Nodes.node_det segs).
#[local] Notation node_ret_only := (Nodes.node_ret_only segs).
#[local] Notation node_ret_only_copyins := (Nodes.node_ret_only_copyins segs).
#[local] Notation node_instr := (ShapeAlg.node_instr segs).
#[local] Notation node_family_cfg := (Nodes.node_family_cfg segs).
#[local] Notation family_cfg_nonempty := (Nodes.family_cfg_nonempty segs).
#[local] Notation node_family_succ := (Nodes.node_family_succ segs).
#[local] Notation node_family_forced := (Nodes.node_family_forced segs).

Lemma srz_exit : forall ms model x8,
  m_halted model = None -> ms_svc_pending ms = Some x8 -> is_exit_no x8 ->
  srealizes segs (mkCfg ms model) (t_exit (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) (m_fs model)).
Proof. intros. apply srealizes_of_realizes. eapply rz_exit; eassumption. Qed.

Lemma srz_ret_only_silent : forall ms model x8 r m' T,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  alloc_sysno_b (bv_unsigned x8) = false ->
  (forall o, syscall_spec (sys_input segs ms x8) model o <-> o = Ok (mkEffect r [] []) m' []) ->
  m_halted m' = None ->
  m_vm_lazy m' = [] ->
  srealizes segs (mkCfg (advance_past_svc (set_gpr0 ms r)) m') T ->
  srealizes segs (mkCfg ms model) T.
Proof.
  intros ms model x8 r m' T Hh Hsvc Hna Hchk Hh' Hlazy Hc.
  eapply srz_silent1; [eapply node_ret_only; eassumption | exact Hc].
Qed.

Lemma srz_ret_only_copyins_silent : forall ms model x8 reads r m' T,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  alloc_sysno_b (bv_unsigned x8) = false ->
  (forall o, syscall_spec (sys_input segs ms x8) model o
             <-> o = Ok (with_copyins reads (mkEffect r [] [])) m' []) ->
  m_halted m' = None ->
  m_vm_lazy m' = [] ->
  srealizes segs (mkCfg (advance_past_svc (set_gpr0 ms r)) m') T ->
  srealizes segs (mkCfg ms model) T.
Proof.
  intros ms model x8 reads r m' T Hh Hsvc Hna Hchk Hh' Hlazy Hc.
  eapply srz_silent1; [eapply node_ret_only_copyins; eassumption | exact Hc].
Qed.

Lemma srz_det : forall ms model x8 eff0 m0 T,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  alloc_sysno_b (bv_unsigned x8) = false ->
  (forall o, syscall_spec (sys_input segs ms x8) model o <-> o = Ok eff0 m0 []) ->
  m_halted m0 = None ->
  m_vm_lazy m0 = [] ->
  srealizes segs (mkCfg (advance_past_svc (apply_effect ms eff0)) m0) T ->
  srealizes segs (mkCfg ms model) T.
Proof.
  intros ms model x8 eff0 m0 T Hh Hsvc Hna Hchk Hh0 Hlazy0 Hc.
  eapply srz_silent1; [eapply node_det; eassumption | exact Hc].
Qed.

Lemma srz_cases : forall c (I : Type) (nx : I -> config) (T : I -> TSet) (i0 : I),
  node_ok segs c I (fun _ => []) nx ->
  (forall i, srealizes segs (nx i) (T i)) ->
  srealizes segs c (t_alt T).
Proof.
  intros c I nx T i0 Hnode Hc.
  apply (srz_conseq segs c (t_alt (fun i => t_emit [] (T i)))).
  - apply (srz_node segs c I (fun _ => []) nx T i0 Hnode Hc).
  - intros tr. split.
    + intros [i Hi]. exists i.
      exact (proj1 (t_emit_nil_eq (T i) (srealizes_nonempty segs _ _ (Hc i)) tr) Hi).
    + intros [i Hi]. exists i.
      exact (proj2 (t_emit_nil_eq (T i) (srealizes_nonempty segs _ _ (Hc i)) tr) Hi).
Qed.

Lemma srz_open : forall ms model x8 reads (mk : word -> Model) A B,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  ms_svc_pending ms = Some x8 ->
  alloc_sysno_b (bv_unsigned x8) = false ->
  (forall o, syscall_spec (sys_input segs ms x8) model o <-> open_out reads model mk o) ->
  (forall fd, m_halted (mk fd) = None) ->
  (forall fd, m_vm_lazy (mk fd) = []) ->
  fd_lookup (m_fds model) (alloc_fd (m_fds model)) = None ->
  (forall e, In e openat_errnos ->
     srealizes segs (mkCfg (advance_past_svc (set_gpr0 ms (errno_ret e))) model) A) ->
  srealizes segs (mkCfg (advance_past_svc (set_gpr0 ms (alloc_fd (m_fds model))))
                       (mk (alloc_fd (m_fds model)))) B ->
  srealizes segs (mkCfg ms model) (t_alt2 A B).
Proof.
  intros ms model x8 reads mk A B Hh Hlazy Hsvc Hna Hchk Hmk Hmklazy Hfree HA HB.
  apply (srz_alt2 segs (mkCfg ms model) {e : Z | In e openat_errnos} unit
           (open_nx ms model mk) A B (exist _ ENOMEM ENOMEM_in_openat_errnos) tt).
  - eapply node_open; eassumption.
  - intros [e He]. cbn [open_nx]. apply HA. exact He.
  - intros []. cbn [open_nx]. exact HB.
Qed.

Lemma srz_sys : forall regs pc mem rom model w T,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  fetch_word segs pc = Some w -> is_ecall w = true ->
  srealizes segs (mkCfg (epend regs pc mem rom (getr regs 17)) model) T ->
  srealizes segs (mkCfg (mkst regs pc mem rom) model) T.
Proof.
  intros regs pc mem rom model w T Hh Hlazy HF HE Hc.
  eapply srz_step; [exact Hh | exact Hlazy | reflexivity | eapply step_ecall_epend; eassumption | exact Hc].
Qed.

End Prim.

Section WithSegs.
Context {fx : FPState}.
Variable segs : list Segment.
#[local] Notation node_brk := (RefNodes.node_brk segs).
#[local] Notation node_set_tid := (RefNodes.node_set_tid segs).
#[local] Notation mmap_noaccess_outcome_si := (RefNodes.mmap_noaccess_outcome_si segs).
#[local] Notation mprotect_outcome_si := (RefNodes.mprotect_outcome_si segs).
#[local] Notation mmap_fixed_outcome_si := (RefNodes.mmap_fixed_outcome_si segs).
#[local] Notation node_open := (Nodes.node_open segs).
#[local] Notation read_file_outcome_si := (RefNodes.read_file_outcome_si segs).

Lemma srz_set_tid : forall regs (pc : word) mem rom model K w,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  getr regs 17 = Z_to_bv 64 96 ->
  m_tid model = None ->
  (forall tid, (0 < bv_unsigned tid < PID_MAX_ENVELOPE)%Z ->
     srealizes segs (mkCfg (mkst (regupd regs 10 tid) (v_addi pc 4) mem rom) (with_tid tid model)) K) ->
  srealizes segs (mkCfg (mkst regs pc mem rom) model) K.
Proof.
  intros regs pc mem rom model K w HF HE Hh Hlazy H17 Htid Hk.
  eapply srz_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
  apply (srz_conseq segs _ (t_alt (fun _ : tid_I => K)));
    [| intros tr; split; [intros [_ Ht]; exact Ht | intros Ht; exists (exist _ (Z_to_bv 64 1) one_tid_ok); exact Ht]].
  eapply srz_cases; [exact (exist _ (Z_to_bv 64 1) one_tid_ok)
                   | eapply node_set_tid; [exact Hh | exact Hlazy | reflexivity | rewrite H17; apply u64_lit; lia | exact Htid] |].
  intros [t Ht]. cbn [proj1_sig]. rewrite adv_set_epend. apply Hk. exact Ht.
Qed.

Lemma srz_exit_at : forall regs (pc : word) mem rom model w code,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  (getr regs 17 = Z_to_bv 64 94 \/ getr regs 17 = Z_to_bv 64 93) ->
  getr regs 10 = code ->
  srealizes segs (mkCfg (mkst regs pc mem rom) model)
           (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model)).
Proof.
  intros regs pc mem rom model w code HF HE Hh Hlazy H17 H10.
  eapply srz_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
  rewrite <- H10, <- (ms_gpr_epend0 regs pc mem rom (getr regs 17)).
  eapply srz_exit; [exact Hh | reflexivity |].
  destruct H17 as [H|H]; [right|left]; rewrite H; reflexivity.
Qed.

Lemma srz_close : forall regs (pc : word) mem model w fd e K,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  getr regs 17 = Z_to_bv 64 57 ->
  getr regs 10 = fd -> (bv_unsigned fd < 2 ^ 32)%Z ->
  fd_lookup (m_fds model) fd = Some e ->
  srealizes segs (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 0)) (v_addi pc 4) mem (seg_rom segs))
                       (with_fds (fd_remove (m_fds model) fd) model)) K ->
  srealizes segs (mkCfg (mkst regs pc mem (seg_rom segs)) model) K.
Proof.
  intros regs pc mem model w fd e K HF HE Hh Hlazy H17 Hfd Hfd32 Hlk Hc.
  eapply srz_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
  eapply srz_ret_only_silent; [exact Hh | reflexivity | nonalloc_tac | | | | rewrite adv_set_epend; exact Hc].
  - intros o. rewrite (syscall_spec_57 _ model o) by (rewrite in_sysno_si, H17; apply u64_lit; lia).
    rewrite in_arg0_si, ms_gpr_epend0, Hfd, (fd32_id fd Hfd32). exact (close_outcome fd _ model e o Hlk).
  - rewrite with_fds_halted'. exact Hh.
  - rewrite with_fds_lazy. exact Hlazy.
Qed.

Lemma srz_ioctl_winsz : forall regs (pc : word) mem model w fd e K,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  getr regs 17 = Z_to_bv 64 29 ->
  getr regs 10 = fd -> (bv_unsigned fd < 2 ^ 32)%Z ->
  fd_lookup (m_fds model) fd = Some e ->
  e <> FdUrandom ->
  getr regs 11 = Z_to_bv 64 0x5413 ->
  srealizes segs (mkCfg (mkst (regupd regs 10 (errno_ret ENOTTY)) (v_addi pc 4) mem (seg_rom segs))
                       model) K ->
  srealizes segs (mkCfg (mkst regs pc mem (seg_rom segs)) model) K.
Proof.
  intros regs pc mem model w fd e K HF HE Hh Hlazy H17 Hfd Hfd32 Hlk Hnd H11 Hc.
  eapply srz_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
  eapply srz_ret_only_silent; [exact Hh | reflexivity | nonalloc_tac | | exact Hh | exact Hlazy | rewrite adv_set_epend; exact Hc].
  intros o. rewrite (syscall_spec_29 _ model o) by (rewrite in_sysno_si, H17; apply u64_lit; lia).
  rewrite in_arg0_si, in_arg1_si, ms_gpr_epend0, ms_gpr_epend1, Hfd, (fd32_id fd Hfd32), H11.
  apply (ioctl_tty_outcome fd _ _ model e o Hlk Hnd). reflexivity.
Qed.

Lemma srz_read_dir : forall regs (pc : word) mem model w fd K,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  getr regs 17 = Z_to_bv 64 63 ->
  getr regs 10 = fd -> (bv_unsigned fd < 2 ^ 32)%Z ->
  fd_lookup (m_fds model) fd = Some FdDir ->
  (bv_unsigned (getr regs 11) + bv_unsigned (getr regs 12) <= TASK_SIZE)%Z ->
  srealizes segs (mkCfg (mkst (regupd regs 10 (errno_ret EISDIR)) (v_addi pc 4) mem (seg_rom segs)) model) K ->
  srealizes segs (mkCfg (mkst regs pc mem (seg_rom segs)) model) K.
Proof.
  intros regs pc mem model w fd K HF HE Hh Hlazy H17 Hfd Hfd32 Hlk Hdir Hc.
  eapply srz_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
  eapply srz_ret_only_silent; [exact Hh | reflexivity | nonalloc_tac | | exact Hh | exact Hlazy | rewrite adv_set_epend; exact Hc].
  intros o. rewrite (syscall_spec_63 _ model o) by (rewrite in_sysno_si, H17; apply u64_lit; lia).
  rewrite in_arg0_si, in_arg1_si, in_arg2_si, ms_gpr_epend0, ms_gpr_epend1, ms_gpr_epend2, Hfd, (fd32_id fd Hfd32).
  apply (read_dir_outcome fd _ _ _ model o Hlk). apply access_okb_intro. exact Hdir.
Qed.

Lemma srz_read_file : forall regs (pc : word) mem model w fd p off data (cnt : Z) K,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  getr regs 17 = Z_to_bv 64 63 ->
  getr regs 10 = fd -> (bv_unsigned fd < 2 ^ 32)%Z ->
  fd_lookup (m_fds model) fd = Some (FdFile p off) ->
  fs_lookup (m_fs model) p = Some data ->
  getr regs 12 = Z_to_bv 64 cnt ->
  (1 <= cnt)%Z -> (cnt <= rw_bytes_max)%Z -> (cnt < 2 ^ 64)%Z ->
  (bv_unsigned (getr regs 11) + cnt <= TASK_SIZE)%Z ->
  store_ok segs mem (getr regs 11) (Z.to_nat cnt) = true ->
  let bs := file_read data off (getr regs 12) in
  srealizes segs (mkCfg (mkst (regupd regs 10 (len_word bs)) (v_addi pc 4)
                              (wbytes mem (getr regs 11) bs) (seg_rom segs))
                       (with_fds (fd_insert (m_fds model) fd (FdFile p (off + len_word bs))) model)) K ->
  srealizes segs (mkCfg (mkst regs pc mem (seg_rom segs)) model) K.
Proof.
  intros regs pc mem model w fd p off data cnt K HF HE Hh Hlazy H17 Hfd Hfd32 Hlk Hfs H12 Hc1 Hmax H64 Hover Hok bs Hc.
  assert (Hno : bv_unsigned (getr regs 17) = 63%Z) by (rewrite H17; apply u64_lit; lia).
  eapply srz_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
  destruct (read_bytes_map_of_store_ok segs mem (getr regs 11) (Z.to_nat cnt) Hok ltac:(lia)) as [wv Hw].
  rewrite Z2Nat.id in Hw by lia.
  set (ms := epend regs pc mem (seg_rom segs) (getr regs 17)).
  assert (Hu2 : bv_unsigned (ms_gpr ms 2) = cnt).
  { unfold ms. rewrite ms_gpr_epend2, H12. apply u64_lit. lia. }
  pose proof (read_file_outcome_si ms (getr regs 17) model fd p off data wv Hno
              ltac:(unfold ms; rewrite ms_gpr_epend0; exact Hfd) Hfd32 Hlk Hfs
              ltac:(unfold ms; rewrite ms_writable_byte_epend, ms_gpr_epend1, ms_gpr_epend2, H12; exact Hw)
              ltac:(rewrite Hu2; lia) ltac:(rewrite Hu2; exact Hmax)
              ltac:(rewrite Hu2; unfold ms; rewrite ms_gpr_epend1; exact Hover)) as Hchk.
  unfold ms in Hchk. rewrite ms_gpr_epend1, ms_gpr_epend2 in Hchk.
  subst bs. revert Hc Hchk.
  generalize (file_read data off (getr regs 12)) as bs. intros bs Hc Hchk.
  eapply (srz_det segs _ model _ (mkEffect (len_word bs) (delivered_writes (getr regs 11) bs) [])
            (with_fds (fd_insert (m_fds model) fd (FdFile p (off + len_word bs))) model));
    [exact Hh | reflexivity | nonalloc_tac | exact Hchk
    | rewrite with_fds_halted'; exact Hh | rewrite with_fds_lazy; exact Hlazy | ].
  destruct bs as [|b bsr]; cbn [delivered_writes].
  - unfold ms. rewrite adv_ret_epend. cbn [wbytes] in Hc. exact Hc.
  - unfold ms. rewrite adv_write1_epend. exact Hc.
Qed.

Section Openat.
  Variables (regs : bvmap 5 word) (pc : word) (mem : word -> option byte) (model : Model).
  Variable w : bv 32.
  Hypothesis HF : fetch_word segs pc = Some w.
  Hypothesis HE : is_ecall w = true.
  Hypothesis Hh : m_halted model = None.
  Hypothesis Hlazy : m_vm_lazy model = [].
  Hypothesis H17 : getr regs 17 = Z_to_bv 64 56.
  Hypothesis H10 : getr regs 10 = AT_FDCWD.

  Hypothesis Hfl : Z.ldiff (bv_unsigned (getr regs 12)) open_ignored_flags = 0%Z.

  Let ms := epend regs pc mem (seg_rom segs) (getr regs 17).
  Let post (r : word) := mkst (regupd regs 10 r) (v_addi pc 4) mem (seg_rom segs).
  Let fds := m_fds model.

  Lemma Hno56 : bv_unsigned (getr regs 17) = 56%Z.
  Proof. rewrite H17. apply u64_lit. lia. Qed.

  Lemma openat_spec_head : forall o,
    syscall_spec (sys_input segs ms (getr regs 17)) model o <->
    openat_spec AT_FDCWD32 (getr regs 11) (getr regs 12) (sys_input segs ms (getr regs 17)) model o.
  Proof.
    intros o. cbv delta [ms].
    rewrite (syscall_spec_56 _ model o) by (rewrite in_sysno_si; exact Hno56).
    rewrite in_arg0_si, in_arg1_si, in_arg2_si, ms_gpr_epend0, ms_gpr_epend1, ms_gpr_epend2, H10.
    reflexivity.
  Qed.

  Lemma open_in_mem : in_mem (sys_input segs ms (getr regs 17)) = mrb segs mem.
  Proof. cbv delta [ms]. rewrite in_mem_si, ms_read_byte_epend. reflexivity. Qed.

  Lemma open_flags_modeled : modeled_open_flags (getr regs 12) = true.
  Proof. exact (modeled_open_flags_rd _ Hfl). Qed.

  Lemma srz_openat_toolong : forall bs K,
    rdn segs mem (getr regs 11) 4096 = Some bs -> ~ In (Z_to_bv 8 0) bs ->
    srealizes segs (mkCfg (post (errno_ret ENAMETOOLONG)) model) K ->
    srealizes segs (mkCfg (mkst regs pc mem (seg_rom segs)) model) K.
  Proof.
    intros bs K Hrd Hnz Hc. cbv delta [post] in *.
    pose proof (read_cstr_toolong_of_rdn segs mem (getr regs 11) bs (rdn_length _ _ _ _ _ Hrd) Hnz Hrd) as Hp.
    eapply srz_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
    eapply srz_ret_only_copyins_silent; [exact Hh | reflexivity | nonalloc_tac | | exact Hh | exact Hlazy | rewrite adv_set_epend; exact Hc].
    intros o. fold ms. rewrite openat_spec_head.
    apply (openat_toolong_outcome _ _ _ _ model open_flags_modeled). rewrite open_in_mem. exact Hp.
  Qed.

  Definition path_at (p : list byte) : Prop :=
    (length p <= 4095)%nat /\ ~ In (Z_to_bv 8 0) p
    /\ rdn segs mem (getr regs 11) (length p + 1) = Some (p ++ [Z_to_bv 8 0]).

  Lemma path_at_cstr : forall p, path_at p -> read_cstr (mrb segs mem) (getr regs 11) = CstrOk p.
  Proof. intros p (H1 & H2 & H3). apply read_cstr_of_rdn; assumption. Qed.

  Lemma srz_openat_empty : forall K,
    path_at [] ->
    srealizes segs (mkCfg (post (errno_ret ENOENT)) model) K ->
    srealizes segs (mkCfg (mkst regs pc mem (seg_rom segs)) model) K.
  Proof.
    intros K Hp Hc. cbv delta [post] in *.
    eapply srz_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
    eapply srz_ret_only_copyins_silent; [exact Hh | reflexivity | nonalloc_tac | | exact Hh | exact Hlazy | rewrite adv_set_epend; exact Hc].
    intros o. fold ms. rewrite openat_spec_head.
    apply (openat_empty_outcome _ _ _ _ model open_flags_modeled). rewrite open_in_mem. exact (path_at_cstr [] Hp).
  Qed.

  Lemma srz_openat_absent : forall p K,
    path_at p -> p <> [] -> path_is_dirref p = false -> path_has_slash p = false ->
    fs_lookup (m_fs model) p = None ->
    srealizes segs (mkCfg (post (errno_ret ENOENT)) model) K ->
    srealizes segs (mkCfg (mkst regs pc mem (seg_rom segs)) model) K.
  Proof.
    intros p K Hp Hne Hnd Hsl Hfs Hc. cbv delta [post] in *.
    eapply srz_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
    eapply srz_ret_only_copyins_silent; [exact Hh | reflexivity | nonalloc_tac | | exact Hh | exact Hlazy | rewrite adv_set_epend; exact Hc].
    intros o. fold ms. rewrite openat_spec_head.
    apply (openat_absent_outcome _ _ _ _ model open_flags_modeled eq_refl Hfl p);
      [rewrite open_in_mem; exact (path_at_cstr p Hp) | exact Hne | exact Hnd | exact Hsl | exact Hfs].
  Qed.

  Hypothesis Hfree : fd_lookup fds (alloc_fd fds) = None.

  Lemma srz_openat_dot : forall KA KB,
    path_at dot_path ->
    (forall e, In e openat_errnos -> srealizes segs (mkCfg (post (errno_ret e)) model) KA) ->
    srealizes segs (mkCfg (post (alloc_fd fds)) (with_fds (fd_insert fds (alloc_fd fds) FdDir) model)) KB ->
    srealizes segs (mkCfg (mkst regs pc mem (seg_rom segs)) model) (t_alt2 KA KB).
  Proof.
    intros KA KB Hp HA HB. cbv delta [post] in *.
    eapply srz_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
    eapply srz_open; [exact Hh | exact Hlazy | reflexivity | nonalloc_tac | | | | exact Hfree | |].
    - intros o. fold ms. rewrite openat_spec_head.
      apply (openat_dot_outcome _ _ _ _ model open_flags_modeled eq_refl Hfl).
      rewrite open_in_mem. exact (path_at_cstr _ Hp).
    - intros fd. cbv beta delta [fds]. rewrite with_fds_halted'. exact Hh.
    - intros fd. cbv beta delta [fds]. rewrite with_fds_lazy. exact Hlazy.
    - intros e He. rewrite adv_set_epend. apply HA. exact He.
    - rewrite adv_set_epend. exact HB.
  Qed.

  Lemma srz_openat_file : forall p d KA KB,
    path_at p -> p <> [] -> path_is_dirref p = false -> path_has_slash p = false ->
    fs_lookup (m_fs model) p = Some d ->
    (forall e, In e openat_errnos -> srealizes segs (mkCfg (post (errno_ret e)) model) KA) ->
    srealizes segs (mkCfg (post (alloc_fd fds))
                         (with_fds (fd_insert fds (alloc_fd fds) (FdFile p (Z_to_bv 64 0))) model)) KB ->
    srealizes segs (mkCfg (mkst regs pc mem (seg_rom segs)) model) (t_alt2 KA KB).
  Proof.
    intros p d KA KB Hp Hne Hnd Hsl Hfs HA HB. cbv delta [post] in *.
    eapply srz_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
    eapply srz_open; [exact Hh | exact Hlazy | reflexivity | nonalloc_tac | | | | exact Hfree | |].
    - intros o. fold ms. rewrite openat_spec_head.
      apply (openat_file_outcome _ _ _ _ model open_flags_modeled eq_refl Hfl p d);
        [rewrite open_in_mem; exact (path_at_cstr p Hp) | exact Hne | exact Hnd | exact Hsl | exact Hfs].
    - intros fd. cbv beta delta [fds]. rewrite with_fds_halted'. exact Hh.
    - intros fd. cbv beta delta [fds]. rewrite with_fds_lazy. exact Hlazy.
    - intros e He. rewrite adv_set_epend. apply HA. exact He.
    - rewrite adv_set_epend. exact HB.
  Qed.
End Openat.

End WithSegs.
