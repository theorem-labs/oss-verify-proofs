(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Mprotect.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSimInv BExitSim BPropExec BCatExec BCatSim BSeqExec BStreamExec BMmapSim BAllocSim BFileSim BShapeAlg BpinAlg BNodes BStoreOk BAgentLib BAgentNodes BllocNodes BothAcct BothAcctShape BothPlacement BackingBlgebra BRelSpec BothRelSpec BothNodesChk Bcfg BothCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BxSymExec3 BxSymExec3Sound BxSymRun3 BothPlanCore BothPlan BothPlanSound.
Import ListNotations.
Open Scope bv_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Section Noacc.
Variable segs : list Segment.
Context {SC : StepCfg}.

Lemma sstep_of_check_noacc : forall ms model x8 eff m' evs,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  syscall_spec (sys_input segs ms x8) model (Ok eff m' evs) ->
  ~ spurious_refusal_cfg the_scfg (sys_input segs ms x8) model eff ->
  m_halted m' = None ->
  syscall_effect_accesses eff = [] ->
  sstep_cfg segs the_scfg (mkCfg ms model) evs (SNext (mkCfg (advance_past_svc (apply_effect ms eff)) m')).
Proof.
  intros ms model x8 eff m' evs Hh Hsvc Hc Hns Hh' Hacc.
  apply (sstep_cfg_syscall segs the_scfg ms model x8 eff m' m' evs Hh Hsvc).
  - exact Hc.
  - exact Hns.
  - exact Hh'.
  - rewrite Hacc. apply materialize_model_accesses_nil.
Qed.

Lemma node_chk_ev_noacc : forall ms model x8 (I : Type)
    (effs : I -> SyscallEffect) (ms' : I -> Model) (evs : I -> list event),
  m_halted model = None -> ms_svc_pending ms = Some x8 ->
  (forall i, syscall_spec (sys_input segs ms x8) model (Ok (effs i) (ms' i) (evs i))) ->
  (forall i, ~ spurious_refusal_cfg the_scfg (sys_input segs ms x8) model (effs i)) ->
  (forall eff m' ev, syscall_spec (sys_input segs ms x8) model (Ok eff m' ev) ->
     ~ spurious_refusal_cfg the_scfg (sys_input segs ms x8) model eff ->
     exists i, eff = effs i /\ m' = ms' i /\ ev = evs i) ->
  (forall eff m' ev, syscall_spec (sys_input segs ms x8) model (Ok eff m' ev) -> m_halted m' = None) ->
  (~ syscall_spec (sys_input segs ms x8) model Unmodeled) ->
  (forall i, syscall_effect_accesses (effs i) = []) ->
  node_ok segs (mkCfg ms model) I evs
          (fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms' i)).
Proof.
  intros ms model x8 I effs ms' evs Hh Hsvc Hok Hnsp Hinv Hnoh Hnu Hacc. split.
  - intros i. apply (sstep_of_check_noacc ms model x8); [exact Hh | exact Hsvc | exact (Hok i) | exact (Hnsp i) | exact (Hnoh _ _ _ (Hok i)) | exact (Hacc i)].
  - intros e st Hss.
    destruct (sstep_cfg_svc_inv segs ms model x8 e st Hsvc Hss)
      as [(eff & model' & ev & Hc & [(m'' & Hh2 & -> & Hns & Hm & ->) | [(Hh2 & -> & Hns & Hm & ->) | [(code & Hh2 & _ & -> & ->) | (sig & Hk & -> & ->)]]])
         | (Hc & -> & ->)].
    + destruct (Hinv _ _ _ Hc Hns) as (i & -> & -> & ->).
      rewrite (Hacc i), materialize_model_accesses_nil in Hm. injection Hm as <-. exists i. split; reflexivity.
    + destruct (Hinv _ _ _ Hc Hns) as (i & -> & -> & ->). rewrite (Hacc i), materialize_model_accesses_nil in Hm. discriminate.
    + rewrite (Hnoh _ _ _ Hc) in Hh2. discriminate.
    + rewrite (m_killed_of_m_halted_none _ (Hnoh _ _ _ Hc)) in Hk. discriminate.
    + exfalso. exact (Hnu Hc).
Qed.

Lemma node_chk_noacc : forall ms model x8 (I : Type) (effs : I -> SyscallEffect) (ms' : I -> Model),
  m_halted model = None -> ms_svc_pending ms = Some x8 ->
  (forall i, syscall_spec (sys_input segs ms x8) model (Ok (effs i) (ms' i) [])) ->
  (forall i, ~ spurious_refusal_cfg the_scfg (sys_input segs ms x8) model (effs i)) ->
  (forall eff m' evs, syscall_spec (sys_input segs ms x8) model (Ok eff m' evs) ->
     ~ spurious_refusal_cfg the_scfg (sys_input segs ms x8) model eff ->
     exists i, eff = effs i /\ m' = ms' i /\ evs = []) ->
  (forall eff m' ev, syscall_spec (sys_input segs ms x8) model (Ok eff m' ev) -> m_halted m' = None) ->
  (~ syscall_spec (sys_input segs ms x8) model Unmodeled) ->
  (forall i, syscall_effect_accesses (effs i) = []) ->
  node_ok segs (mkCfg ms model) I (fun _ => [])
          (fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms' i)).
Proof.
  intros ms model x8 I effs ms' Hh Hsvc Hok Hnsp Hinv Hnoh Hnu Hacc.
  apply (node_chk_ev_noacc ms model x8 I effs ms' (fun _ => []) Hh Hsvc Hok); auto.
Qed.

Lemma node_fam_noacc : forall ms model x8 (I : Type) (effs : I -> SyscallEffect) (ms' : I -> Model)
    (R : outcome SyscallEffect -> Prop),
  m_halted model = None -> ms_svc_pending ms = Some x8 ->
  (forall o, syscall_spec (sys_input segs ms x8) model o <-> R o) ->
  (forall i, R (Ok (effs i) (ms' i) [])) ->
  (forall i, ~ spurious_refusal_cfg the_scfg (sys_input segs ms x8) model (effs i)) ->
  (forall eff m' evs, R (Ok eff m' evs) ->
     ~ spurious_refusal_cfg the_scfg (sys_input segs ms x8) model eff ->
     exists i, eff = effs i /\ m' = ms' i /\ evs = []) ->
  (forall eff m' ev, R (Ok eff m' ev) -> m_halted m' = None) ->
  (~ R Unmodeled) ->
  (forall i, syscall_effect_accesses (effs i) = []) ->
  node_ok segs (mkCfg ms model) I (fun _ => [])
          (fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms' i)).
Proof.
  intros ms model x8 I effs ms' R Hh Hsvc HR Hin Hns Hout Hnh Hnu Hacc.
  apply (node_chk_noacc ms model x8 I effs ms' Hh Hsvc).
  - intros i. apply HR. apply Hin.
  - exact Hns.
  - intros eff m' ev Hc Hs. apply HR in Hc. exact (Hout _ _ _ Hc Hs).
  - intros eff m' ev Hc. apply HR in Hc. exact (Hnh _ _ _ Hc).
  - intros Hc. apply HR in Hc. exact (Hnu Hc).
  - exact Hacc.
Qed.

Lemma node_det_noacc : forall ms model x8 eff0 m0 evs0,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  (forall eff m' evs,
     syscall_spec (sys_input segs ms x8) model (Ok eff m' evs) <->
     (eff = eff0 /\ m' = m0 /\ evs = evs0)) ->
  ~ spurious_refusal_cfg the_scfg (sys_input segs ms x8) model eff0 ->
  (~ syscall_spec (sys_input segs ms x8) model Unmodeled) ->
  m_halted m0 = None ->
  syscall_effect_accesses eff0 = [] ->
  node_ok segs (mkCfg ms model) unit (fun _ => evs0)
          (fun _ => mkCfg (advance_past_svc (apply_effect ms eff0)) m0).
Proof.
  intros ms model x8 eff0 m0 evs0 Hh Hsvc Hchk Hns Hnu Hh0 Hacc.
  apply (node_chk_ev_noacc ms model x8 unit (fun _ => eff0) (fun _ => m0) (fun _ => evs0) Hh Hsvc).
  - intros []. apply (proj2 (Hchk eff0 m0 evs0)). auto.
  - intros []. exact Hns.
  - intros eff m' ev Hc _. apply Hchk in Hc as (-> & -> & ->). exists tt. auto.
  - intros eff m' ev Hc. apply Hchk in Hc as (-> & -> & ->). exact Hh0.
  - exact Hnu.
  - intros []; exact Hacc.
Qed.

Lemma srz_det_noacc : forall ms model x8 eff0 m0 T,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  (forall eff m' evs,
     syscall_spec (sys_input segs ms x8) model (Ok eff m' evs) <->
     (eff = eff0 /\ m' = m0 /\ evs = [])) ->
  ~ spurious_refusal_cfg the_scfg (sys_input segs ms x8) model eff0 ->
  (~ syscall_spec (sys_input segs ms x8) model Unmodeled) ->
  m_halted m0 = None ->
  syscall_effect_accesses eff0 = [] ->
  srealizes segs (mkCfg (advance_past_svc (apply_effect ms eff0)) m0) T ->
  srealizes segs (mkCfg ms model) T.
Proof.
  intros ms model x8 eff0 m0 T Hh Hsvc Hchk Hns Hnu Hh0 Hacc Hc.
  eapply srz_silent1; [eapply node_det_noacc; eassumption | exact Hc].
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

Lemma with_mmap_backing_halted : forall flags a n m,
  m_halted (with_mmap_backing flags a n m) = m_halted m.
Proof. intros. unfold with_mmap_backing. destruct (mmap_noreserve_b flags); reflexivity. Qed.

Lemma forget_vm_ranges_halted : forall ranges m,
  m_halted (forget_vm_ranges ranges m) = m_halted m.
Proof.
  induction ranges as [|[a n] r IH]; intros m; [reflexivity|].
  cbn [forget_vm_ranges]. rewrite IH. apply vm_forget_range_halted.
Qed.

Lemma brk_model_halted : forall req r m, m_halted (brk_model req r m) = m_halted m.
Proof.
  intros. unfold brk_model, with_brk_next. cbv zeta.
  rewrite forget_vm_ranges_halted. apply with_vmmaps_halted.
Qed.

Lemma stepacc_ecall_epend : forall regs pc mem rom w,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  RiscvSemantics.step_accesses segs (mkst regs pc mem rom)
  = MachineOk (@mkAccessReport machine_state (epend regs pc mem rom (getr regs 17)) []).
Proof.
  intros regs pc mem rom w Hfetch Hecall.
  unfold RiscvSemantics.step_accesses. cbn [ms_pc ms_pc_val mkst].
  rewrite Hfetch. cbv beta iota.
  unfold RiscvSemantics.decode_exec_accesses. rewrite Hecall. cbv beta iota.
  reflexivity.
Qed.

Lemma node_instr_noacc : forall ms model ms',
  m_halted model = None ->
  ms_svc_pending ms = None ->
  RiscvSemantics.step_accesses segs ms = MachineOk (@mkAccessReport machine_state ms' []) ->
  node_ok segs (mkCfg ms model) unit (fun _ => []) (fun _ => mkCfg ms' model).
Proof.
  intros ms model ms' Hh Hsvc Hstep.
  assert (Hacc : mi_account_step segs ms model = MachineOk (ms', model)).
  { unfold mi_account_step. rewrite Hstep. cbn [accessed_ranges access_value].
    rewrite materialize_model_accesses_nil. reflexivity. }
  split.
  - intros []. apply (sstep_cfg_instr segs the_scfg ms model ms' model Hh Hsvc Hacc).
  - intros e st Hss. exists tt. apply sstep_cfg_sub in Hss.
    inversion Hss; subst;
      match goal with
      | H : mi_account_step segs ms model = _ |- _ => rewrite Hacc in H; try discriminate; injection H as <- <-; split; reflexivity
      | H : ms_svc_pending ms = Some _ |- _ => rewrite Hsvc in H; discriminate
      end.
Qed.

Lemma epend_len : forall regs pc mem rom (len : Z),
  getr regs 11 = Z_to_bv 64 len -> (0 < len < 2 ^ 64)%Z ->
  bv_unsigned (ms_gpr (epend regs pc mem rom (getr regs 17)) 1) = len
  /\ ms_gpr (epend regs pc mem rom (getr regs 17)) 1 <> Z_to_bv 64 0.
Proof.
  intros regs pc mem rom len H11 Hlen. rewrite ms_gpr_epend1, H11. split.
  - apply u64_lit. lia.
  - intro Hc. apply (f_equal bv_unsigned) in Hc. rewrite u64_lit in Hc by lia.
    change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in Hc. lia.
Qed.

Lemma srz_sys_lazy : forall regs pc mem rom model w T,
  m_halted model = None ->
  fetch_word segs pc = Some w -> is_ecall w = true ->
  srealizes segs (mkCfg (epend regs pc mem rom (getr regs 17)) model) T ->
  srealizes segs (mkCfg (mkst regs pc mem rom) model) T.
Proof.
  intros regs pc mem rom model w T Hh HF HE Hc.
  eapply srz_silent1; [| exact Hc].
  apply node_instr_noacc; [exact Hh | reflexivity | eapply stepacc_ecall_epend; eassumption].
Qed.

Lemma srz_munmap_lazy : forall regs (pc : word) mem rom model w (a : word) (len : Z) K,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None ->
  getr regs 17 = Z_to_bv 64 215 ->
  getr regs 10 = a -> (bv_unsigned a mod page_size = 0)%Z ->
  getr regs 11 = Z_to_bv 64 len -> (0 < len)%Z ->
  (bv_unsigned a + page_round_up_Z len <= TASK_SIZE)%Z ->
  map_has (vm_maps (m_vmmaps model)) a (Z_to_bv 64 (page_round_up_Z len)) = true ->
  srealizes segs (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 0)) (v_addi pc 4)
                             (unfill a (Z_to_bv 64 (page_round_up_Z len)) mem) rom)
                      (munmap_model a (Z_to_bv 64 (page_round_up_Z len)) model)) K ->
  srealizes segs (mkCfg (mkst regs pc mem rom) model) K.
Proof.
  intros regs pc mem rom model w a len K HF HE Hh H17 H10 Hal H11 Hlen Hnw Hhas Hc.
  assert (Hlen' : (len < two_pow_64)%Z).
  { pose proof (page_round_up_Z_bounds len ltac:(lia)). pose proof (u64_range a). unfold TASK_SIZE in Hnw. unfold two_pow_64. lia. }
  eapply srz_sys_lazy; [exact Hh | exact HF | exact HE |].
  set (ms := epend regs pc mem rom (getr regs 17)).
  assert (Hno : bv_unsigned (getr regs 17) = 215%Z) by (rewrite H17; apply u64_lit; lia).
  assert (Hu1 : bv_unsigned (ms_gpr ms 1) = len).
  { unfold ms. rewrite ms_gpr_epend1, H11. apply u64_lit. unfold two_pow_64 in Hlen'. lia. }
  assert (Hpr : page_round_up (ms_gpr ms 1) = Z_to_bv 64 (page_round_up_Z len)).
  { unfold page_round_up. rewrite Hu1. reflexivity. }
  assert (H0 : ms_gpr ms 0 = a) by (unfold ms; rewrite ms_gpr_epend0; exact H10).
  assert (Hargs : munmap_args_ok ms model).
  { unfold munmap_args_ok. rewrite H0, Hu1, Hpr. repeat split; try assumption.
    intro Hz. apply (f_equal bv_unsigned) in Hz. rewrite Hu1 in Hz.
    change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in Hz. lia. }
  pose proof (fun o => munmap_outcome_si segs ms (getr regs 17) model o Hno Hargs) as Hsi.
  unfold munmap_eff in Hsi. rewrite H0, Hpr in Hsi.
  eapply (srz_det_noacc ms model (getr regs 17)
            (mkEffectU (Z_to_bv 64 0) [] [] [(a, Z_to_bv 64 (page_round_up_Z len))] [] [])
            (munmap_model a (Z_to_bv 64 (page_round_up_Z len)) model));
    [exact Hh | reflexivity | | | | | reflexivity |].
  - intros eff m' evs. split.
    + intros Hck. apply Hsi in Hck. apply Ok_inj in Hck as (-> & -> & ->). repeat split; reflexivity.
    + intros (-> & -> & ->). apply Hsi. reflexivity.
  -
    apply not_spurious_none. rewrite in_sysno_sys_input, Hno. apply injected_arm_none_215.
  - intros Hck. apply Hsi in Hck. exact (Unmodeled_Ok _ _ _ Hck).
  - rewrite munmap_model_halted. exact Hh.
  - unfold ms. rewrite adv_unmaps1_epend. exact Hc.
Qed.

Definition brk_eff (ms : machine_state) (model : Model) (r : word) : SyscallEffect :=
  mkEffectU r [] (brk_zeros (ms_gpr ms 0) r (vm_brk (m_vmmaps model)))
               (brk_unmaps r (vm_brk (m_vmmaps model))) [] [].
Definition brk_res_cfg (ms : machine_state) (model : Model) (x8 : word) (r : word) : Prop :=
  brk_resolution_ok model (ms_gpr ms 0) r
  /\ ~ spurious_refusal_cfg the_scfg (sys_input segs ms x8) model (brk_eff ms model r).

Lemma node_brk_lazy : forall ms model x8,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 214%Z ->
  node_ok segs (mkCfg ms model)
    {r : word | brk_res_cfg ms model x8 r}
    (fun _ => [])
    (fun i => mkCfg (advance_past_svc (apply_effect ms (brk_eff ms model (proj1_sig i))))
                    (brk_model (ms_gpr ms 0) (proj1_sig i) model)).
Proof.
  intros ms model x8 Hh Hsvc Hno.
  apply (node_chk_noacc ms model x8 {r : word | brk_res_cfg ms model x8 r}
           (fun i => brk_eff ms model (proj1_sig i))
           (fun i => brk_model (ms_gpr ms 0) (proj1_sig i) model) Hh Hsvc).
  - intros [r [Hr Hns0]]. cbn [proj1_sig].
    exact (brk_ok_intro segs ms x8 model r Hno Hr).
  - intros [r [Hr0 Hns]]. exact Hns.
  - intros eff m' evs Hc Hns.
    apply (brk_ok_iff segs ms x8 model eff m' evs Hno) in Hc as (Heff & -> & Hok & ->).
    assert (Hrc : brk_res_cfg ms model x8 (eff_ret eff)) by (split; [exact Hok | unfold brk_eff; rewrite <- Heff; exact Hns]).
    exists (exist _ (eff_ret eff) Hrc). cbn [proj1_sig]. unfold brk_eff. rewrite <- Heff. repeat split; reflexivity.
  - intros eff m' evs Hc.
    apply (brk_ok_iff segs ms x8 model eff m' evs Hno) in Hc as (_ & _ & _ & ->). rewrite brk_model_halted. exact Hh.
  - exact (brk_no_unmodeled segs ms x8 model Hno).
  - intros [r Hr]. reflexivity.
Qed.

Lemma brk_sysno : forall ms x8, bv_unsigned x8 = 214%Z -> bv_unsigned (in_sysno (sys_input segs ms x8)) = 214%Z.
Proof. intros ms x8 Hno. rewrite in_sysno_sys_input. exact Hno. Qed.

Lemma brk_refusal_unfold : forall ms x8 model r,
  bv_unsigned x8 = 214%Z ->
  refusal_b (sys_input segs ms x8) model r = brk_refusal_b model (ms_gpr ms 0) r.
Proof.
  intros ms x8 model r Hno. rewrite (refusal_b_brk _ model r (brk_sysno ms x8 Hno)), in_arg0_sys_input. reflexivity.
Qed.

Lemma srz_brk_query_lazy : forall regs (pc : word) mem rom model w K,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None ->
  getr regs 17 = Z_to_bv 64 214 ->
  getr regs 10 = Z_to_bv 64 0 ->
  srealizes segs (mkCfg (mkst (regupd regs 10 (vm_brk (m_vmmaps model))) (v_addi pc 4) mem rom) model) K ->
  srealizes segs (mkCfg (mkst regs pc mem rom) model) K.
Proof.
  intros regs pc mem rom model w K HF HE Hh H17 H10 Hc.
  eapply srz_sys_lazy; [exact Hh | exact HF | exact HE |].
  set (ms := epend regs pc mem rom (getr regs 17)).
  assert (Hno : bv_unsigned (getr regs 17) = 214%Z) by (rewrite H17; apply u64_lit; lia).
  assert (H0 : ms_gpr ms 0 = Z_to_bv 64 0) by (unfold ms; rewrite ms_gpr_epend0; exact H10).
  assert (Hcases : forall r, brk_resolution_ok model (ms_gpr ms 0) r <-> r = vm_brk (m_vmmaps model)).
  { intros r. rewrite H0. unfold brk_resolution_ok, Mmap.brk_r_ok. cbv zeta.
    unfold w_is0. rewrite bv_eqb_refl. cbn [orb]. apply bv_eqb_eq. }
  assert (Hq : brk_res_cfg ms model (getr regs 17) (vm_brk (m_vmmaps model))).
  { split; [apply Hcases; reflexivity|].
    apply spurious_refusal_not_refusal. cbn [brk_eff eff_ret]. rewrite (brk_refusal_unfold ms _ model _ Hno).
    unfold brk_refusal_b. rewrite H0. unfold w_is0. rewrite bv_eqb_refl. reflexivity. }
  apply (srz_conseq segs _ (t_alt (fun _ : {r : word | brk_res_cfg ms model (getr regs 17) r} => K)));
    [| intros tr; split; [intros [_ Ht]; exact Ht | intros Ht; exists (exist _ _ Hq); exact Ht]].
  eapply srz_cases; [exact (exist _ _ Hq) | eapply node_brk_lazy; [exact Hh | reflexivity | exact Hno] |].
  intros [r [Hr Hns']]. cbn [proj1_sig]. unfold brk_eff.
  pose proof (proj1 (Hcases r) Hr) as Er. subst r.
  rewrite H0, brk_zeros_query, brk_unmaps_keep.
  rewrite (brk_model_query _ model eq_refl), vmmaps_eta, with_vmmaps_eta.
  unfold ms. rewrite adv_ret_epend. exact Hc.
Qed.

Lemma srz_brk_grow_lazy : forall regs (pc : word) mem rom model w (d : Z) K,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None ->
  getr regs 17 = Z_to_bv 64 214 ->
  let h := m_vmmaps model in
  let b := vm_brk h in
  (bv_unsigned b mod page_size = 0)%Z -> (d mod page_size = 0)%Z -> (0 < d)%Z ->
  (0 < bv_unsigned b)%Z -> (bv_unsigned b + d < 2 ^ 64)%Z ->
  (bv_unsigned (vm_start_brk h) <= bv_unsigned b + d)%Z ->
  getr regs 10 = Z_to_bv 64 (bv_unsigned b + d) ->

  srealizes segs (mkCfg (mkst (regupd regs 10 b) (v_addi pc 4) mem rom) model) K ->

  (Mmap.brk_grow_ok model (Z_to_bv 64 (bv_unsigned b + d)) (Z_to_bv 64 (bv_unsigned b + d)) = true ->
   srealizes segs (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 (bv_unsigned b + d))) (v_addi pc 4)
                             (zfill b (Z_to_bv 64 d) mem) rom)
                       (with_vmmaps (mkVmMapsFull (vm_reserved h) ((b, Z_to_bv 64 d) :: vm_maps h)
                                      (vm_noaccess h) (vm_start_brk h)
                                      (Z_to_bv 64 (bv_unsigned b + d)) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)) model)) K) ->
  srealizes segs (mkCfg (mkst regs pc mem rom) model) K.
Proof.
  intros regs pc mem rom model w d K HF HE Hh H17 h b Hbal Hdal Hd Hb0 Hnw Hs H10 HA HB.
  pose proof (u64_range b) as Hbr.
  set (req := Z_to_bv 64 (bv_unsigned b + d)) in *.
  assert (Hureq : bv_unsigned req = (bv_unsigned b + d)%Z) by (unfold req; apply u64_lit; lia).
  eapply srz_sys_lazy; [exact Hh | exact HF | exact HE |].
  set (ms := epend regs pc mem rom (getr regs 17)).
  assert (Hno : bv_unsigned (getr regs 17) = 214%Z) by (rewrite H17; apply u64_lit; lia).
  assert (H0 : ms_gpr ms 0 = req) by (unfold ms; rewrite ms_gpr_epend0; exact H10).
  assert (Hcases : forall r, brk_resolution_ok model (ms_gpr ms 0) r <-> (r = b \/ (r = req /\ Mmap.brk_grow_ok model req req = true))).
  { intros r. rewrite H0. apply brk_r_ok_grow_cases; fold h; fold b; rewrite ?Hureq; lia. }
  assert (Hneq : req <> b).
  { intros E. apply (f_equal bv_unsigned) in E. rewrite Hureq in E. unfold b in E. lia. }

  assert (Hi0 : exists r, brk_res_cfg ms model (getr regs 17) r).
  { destruct (Bool.bool_dec (Mmap.brk_grow_ok model req req) true) as [Hg|Hg]; [|apply Bool.not_true_is_false in Hg].
    - exists req. split; [apply Hcases; right; split; [reflexivity | exact Hg]|].
      apply spurious_refusal_not_refusal. cbn [brk_eff eff_ret]. rewrite (brk_refusal_unfold ms _ model _ Hno).
      unfold brk_refusal_b. rewrite H0. fold h b. rewrite (bv_eqb_neq _ _ Hneq). rewrite !andb_false_r. reflexivity.
    - exists b. split; [apply Hcases; left; reflexivity|].
      intros (_ & _ & eff' & m' & evs' & Hspec & Hnr).
      apply (brk_ok_iff segs ms _ model eff' m' evs' Hno) in Hspec as (Heff & _ & Hok & _).
      apply Hcases in Hok as [Hok | [Hok Hg']]; [| rewrite Hg in Hg'; discriminate].
      rewrite (brk_refusal_unfold ms _ model _ Hno) in Hnr. unfold brk_refusal_b in Hnr. rewrite H0, Hok in Hnr.
      fold h b in Hnr. rewrite bv_eqb_refl, (bv_eqb_neq _ _ Hneq) in Hnr.
      assert (E0 : w_is0 req = false).
      { unfold w_is0. apply bv_eqb_neq. intros E. apply (f_equal bv_unsigned) in E. rewrite Hureq in E.
        change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in E. lia. }
      rewrite E0 in Hnr. unfold min_brk in Hnr. fold h in Hnr.
      rewrite (proj2 (Z.ltb_ge _ _)) in Hnr by (rewrite Hureq; lia). discriminate Hnr. }
  destruct Hi0 as [r0 Hr0].
  apply (srz_conseq segs _ (t_alt (fun i : {r : word | brk_res_cfg ms model (getr regs 17) r} => K)));
    [| intros tr; split; [intros [_ Ht]; exact Ht | intros Ht; exists (exist _ r0 Hr0); exact Ht]].
  eapply srz_cases; [exact (exist _ r0 Hr0) | eapply node_brk_lazy; [exact Hh | reflexivity | exact Hno] |].
  intros [r [Hr Hns']]. cbn [proj1_sig]. unfold brk_eff. fold h.
  destruct (proj1 (Hcases r) Hr) as [-> | [-> Hg]].
  - fold b. rewrite brk_zeros_keep, brk_unmaps_keep.
    unfold b, h. rewrite brk_model_keep.
    unfold ms. rewrite adv_ret_epend. exact HA.
  - assert (Hlt : (bv_unsigned b < bv_unsigned req)%Z) by (rewrite Hureq; lia).
    assert (Hreq0 : req <> Z_to_bv 64 0).
    { intros E. apply (f_equal bv_unsigned) in E. rewrite Hureq in E.
      change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in E. lia. }
    rewrite H0. fold b. rewrite (brk_zeros_grow req req b Hreq0 Hb0 Hlt), (brk_unmaps_grow req b) by lia.
    unfold brk_page_range.
    rewrite (page_round_up_Z_aligned (bv_unsigned b)) by (first [lia | exact Hbal]).
    rewrite (page_round_up_Z_aligned (bv_unsigned req))
      by (rewrite Hureq; first [lia | rewrite Z.add_mod, Hbal, Hdal by (unfold page_size; lia); reflexivity]).
    rewrite (proj2 (Z.ltb_lt _ _) Hlt).
    replace (Z_to_bv 64 (bv_unsigned b)) with b by (symmetry; apply Z_to_bv_u_eq'; reflexivity).
    rewrite Hureq. replace (bv_unsigned b + d - bv_unsigned b)%Z with d by lia.
    unfold req, b, h. rewrite (brk_model_grow_eq model d) by assumption.
    unfold ms. rewrite adv_zeros1_epend. apply HB. exact Hg.
Qed.

Lemma srz_brk_grow_blocked_lazy : forall regs (pc : word) mem rom model w (req : word) KA,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None ->
  getr regs 17 = Z_to_bv 64 214 ->
  let h := m_vmmaps model in
  let b := vm_brk h in
  getr regs 10 = req ->
  (0 < bv_unsigned req)%Z ->
  (bv_unsigned (vm_start_brk h) <= bv_unsigned req)%Z ->
  (bv_unsigned b <= bv_unsigned req)%Z ->
  Mmap.brk_grow_ok model req req = false ->
  srealizes segs (mkCfg (mkst (regupd regs 10 b) (v_addi pc 4) mem rom) model) KA ->
  srealizes segs (mkCfg (mkst regs pc mem rom) model) KA.
Proof.
  intros regs pc mem rom model w req KA HF HE Hh H17 h b H10 Hpos Hs Hb Hblk HA.
  eapply srz_sys_lazy; [exact Hh | exact HF | exact HE |].
  set (ms := epend regs pc mem rom (getr regs 17)).
  assert (Hno : bv_unsigned (getr regs 17) = 214%Z) by (rewrite H17; apply u64_lit; lia).
  assert (H0 : ms_gpr ms 0 = req) by (unfold ms; rewrite ms_gpr_epend0; exact H10).
  assert (Hcases : forall r, brk_resolution_ok model (ms_gpr ms 0) r <-> r = b).
  { intros r. rewrite H0, (brk_r_ok_grow_cases model req r Hpos Hs Hb). fold h. fold b. split.
    - intros [-> | [-> Hg]]; [reflexivity | rewrite Hblk in Hg; discriminate].
    - intros ->. left. reflexivity. }
  assert (Hkeep : brk_res_cfg ms model (getr regs 17) b).
  { split; [apply Hcases; reflexivity|].
    intros (_ & Hrb & eff' & m' & evs' & Hspec & Hnr).
    apply (brk_ok_iff segs ms _ model eff' m' evs' Hno) in Hspec as (Heff & _ & Hok & _).
    apply Hcases in Hok. cbn [brk_eff eff_ret] in Hrb. rewrite Hok in Hnr. rewrite Hrb in Hnr. discriminate Hnr. }
  apply (srz_conseq segs _ (t_alt (fun _ : {r : word | brk_res_cfg ms model (getr regs 17) r} => KA)));
    [| intros tr; split; [intros [_ Ht]; exact Ht | intros Ht; exists (exist _ _ Hkeep); exact Ht]].
  eapply srz_cases; [exact (exist _ b Hkeep) | eapply node_brk_lazy; [exact Hh | reflexivity | exact Hno] |].
  intros [r [Hr Hns']]. cbn [proj1_sig]. unfold brk_eff. fold h.
  pose proof (proj1 (Hcases r) Hr) as Er. subst r. fold b.
  rewrite brk_zeros_keep, brk_unmaps_keep. unfold b, h. rewrite brk_model_keep.
  unfold ms. rewrite adv_ret_epend. exact HA.
Qed.

Lemma node_set_tid_lazy : forall ms model x8,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 96%Z ->
  m_tid model = None ->
  node_ok segs (mkCfg ms model) tid_I (fun _ => [])
    (fun i => mkCfg (advance_past_svc (apply_effect ms (mkEffectU (proj1_sig i) [] [] [] [] [])))
                    (with_tid (proj1_sig i) model)).
Proof.
  intros ms model x8 Hh Hsvc Hno Htid.
  assert (Hsi : forall o, syscall_spec (sys_input segs ms x8) model o <->
     exists t, (0 < bv_unsigned t < PID_MAX_ENVELOPE)%Z /\ o = Ok (mkEffect t [] []) (with_tid t model) []).
  { intros o. rewrite (syscall_spec_96 _ model o) by (rewrite in_sysno_sys_input; exact Hno).
    apply set_tid_fresh_outcome. exact Htid. }
  apply (node_fam_noacc ms model x8 tid_I
           (fun i => mkEffectU (proj1_sig i) [] [] [] [] [])
           (fun i => with_tid (proj1_sig i) model) _ Hh Hsvc Hsi).
  - intros [t Ht]. cbn [proj1_sig]. exists t. split; [exact Ht | reflexivity].
  -
    intros i. apply not_spurious_none. rewrite in_sysno_sys_input, Hno. apply injected_arm_none_96.
  - intros eff m' ev (t & Ht & E) _. apply Ok_inj in E as (-> & -> & ->).
    exists (exist _ t Ht). repeat split; reflexivity.
  - intros eff m' ev (t & Ht & E). apply Ok_inj in E as (-> & -> & ->). rewrite with_tid_halted. exact Hh.
  - intros (t & _ & E). exact (Unmodeled_Ok _ _ _ E).
  - intros [t Ht]. reflexivity.
Qed.

Lemma srz_set_tid_lazy : forall regs (pc : word) mem rom model K w,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None ->
  getr regs 17 = Z_to_bv 64 96 ->
  m_tid model = None ->
  (forall tid, (0 < bv_unsigned tid < PID_MAX_ENVELOPE)%Z ->
     srealizes segs (mkCfg (mkst (regupd regs 10 tid) (v_addi pc 4) mem rom) (with_tid tid model)) K) ->
  srealizes segs (mkCfg (mkst regs pc mem rom) model) K.
Proof.
  intros regs pc mem rom model K w HF HE Hh H17 Htid Hk.
  eapply srz_sys_lazy; [exact Hh | exact HF | exact HE |].
  apply (srz_conseq segs _ (t_alt (fun _ : tid_I => K)));
    [| intros tr; split; [intros [_ Ht]; exact Ht | intros Ht; exists (exist _ (Z_to_bv 64 1) one_tid_ok); exact Ht]].
  eapply srz_cases; [exact (exist _ (Z_to_bv 64 1) one_tid_ok)
                   | eapply node_set_tid_lazy; [exact Hh | reflexivity | rewrite H17; apply u64_lit; lia | exact Htid] |].
  intros [t Ht]. cbn [proj1_sig].
  change (mkEffectU t [] [] [] [] []) with (mkEffect t [] []).
  rewrite apply_effect_no_write, adv_set_epend. apply Hk. exact Ht.
Qed.

Lemma srz_exit_at_lazy : forall regs (pc : word) mem rom model w code,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None ->
  (getr regs 17 = Z_to_bv 64 94 \/ getr regs 17 = Z_to_bv 64 93) ->
  getr regs 10 = code ->
  srealizes segs (mkCfg (mkst regs pc mem rom) model)
           (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model)).
Proof.
  intros regs pc mem rom model w code HF HE Hh H17 H10.
  eapply srz_sys_lazy; [exact Hh | exact HF | exact HE |].
  rewrite <- H10, <- (ms_gpr_epend0 regs pc mem rom (getr regs 17)).
  eapply srz_exit; [exact Hh | reflexivity |].
  destruct H17 as [H|H]; [right|left]; rewrite H; reflexivity.
Qed.

Lemma mmap_gates_core50 : forall flags prot,
  mmap_flags_core flags = 50%Z ->
  mmap_modeled_b prot flags (Z_to_bv 64 0) = false
  /\ mmap_noaccess_b prot flags (Z_to_bv 64 0) = false
  /\ mmap_fixed_noaccess_b (Z_to_bv 64 0) flags (Z_to_bv 64 0) = true
  /\ mmap_fixed_noaccess_b (Z_to_bv 64 3) flags (Z_to_bv 64 0) = false
  /\ mmap_fixed_rw_b (Z_to_bv 64 3) flags (Z_to_bv 64 0) = true.
Proof.
  intros flags prot Hc. unfold mmap_modeled_b, mmap_noaccess_b, mmap_fixed_noaccess_b, mmap_fixed_rw_b.
  rewrite Hc. repeat split; try (vm_compute; reflexivity).
  all: destruct (bv_unsigned prot =? _)%Z; vm_compute; reflexivity.
Qed.

Definition fixedin_ok_vmmaps (prot : Z) (addr n : word) (h : VmMaps) : VmMaps :=
  if Z.eqb prot 0
  then mkVmMapsFull (vm_reserved h) (vm_maps h)
         ((addr, n) :: maps_subtract (vm_noaccess h) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n))
         (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)
  else mmap_fixed_rw_next h addr n.

Definition fixedin_destroyed_vmmaps (addr n : word) (h : VmMaps) : VmMaps :=
  mkVmMapsFull (vm_reserved h)
    (maps_subtract (vm_maps h) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n))
    (maps_subtract (vm_noaccess h) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n))
    (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h).

Definition fixedin_ok_model (prot : Z) (flags addr n : word) (m : Model) : Model :=
  with_mmap_replacement flags addr n (with_vmmaps (fixedin_ok_vmmaps prot addr n (m_vmmaps m)) m).
Definition fixedin_destroyed_model (addr n : word) (m : Model) : Model :=
  with_mmap_destroyed addr n (fixedin_destroyed_vmmaps addr n (m_vmmaps m)) m.

Definition fixedin_ok_eff (prot : Z) (addr n : word) : SyscallEffect :=
  if Z.eqb prot 0 then mkEffectU addr [] [] [(addr, n)] [] [] else mkEffectU addr [] [(addr, n)] [] [] [].

Lemma with_mmap_replacement_halted' : forall flags a n m,
  m_halted (with_mmap_replacement flags a n m) = m_halted m.
Proof.
  intros. unfold with_mmap_replacement, with_mmap_backing, vm_forget_range.
  destruct (mmap_noreserve_b flags); reflexivity.
Qed.
Lemma with_mmap_destroyed_halted' : forall a n h m,
  m_halted (with_mmap_destroyed a n h m) = m_halted m.
Proof. intros. reflexivity. Qed.

Lemma mmap_fixedin_outcome_si : forall ms x8 model (prot : Z) (flags addr : word) (len : Z),
  bv_unsigned x8 = 222%Z ->
  (prot = 0 \/ prot = 3)%Z ->
  mmap_flags_core flags = 50%Z ->
  ms_gpr ms 0 = addr -> (bv_unsigned addr mod page_size = 0)%Z -> (0 < bv_unsigned addr)%Z ->
  ms_gpr ms 1 = Z_to_bv 64 len -> (0 < len)%Z ->
  ms_gpr ms 2 = Z_to_bv 64 prot -> ms_gpr ms 3 = flags ->
  ms_gpr ms 4 = Z_to_bv 64 (-1) -> ms_gpr ms 5 = Z_to_bv 64 0 ->
  (bv_unsigned addr + page_round_up_Z len <= alloc_top (m_vmmaps model))%Z ->
  let n := Z_to_bv 64 (page_round_up_Z len) in
  region_free (vm_reserved (m_vmmaps model)) addr n = true ->
  map_contains (vm_maps (m_vmmaps model)) addr n = true ->
  (prot = 3%Z -> mmap_fixed_rw_budget_ok flags model addr n = true) ->
  forall o, syscall_spec (sys_input segs ms x8) model o <->
    mmap_err_out model o
    \/ o = Ok (fixedin_ok_eff prot addr n) (fixedin_ok_model prot flags addr n model) []
    \/ (exists e, In e mmap_errnos
         /\ o = Ok (mkEffectU (errno_ret e) [] [] [(addr, n)] [] []) (fixedin_destroyed_model addr n model) []).
Proof.
  intros ms x8 model prot flags addr len Hno Hprot Hcore H0 Hal Hpos H1 Hlen H2 H3 H4 H5 Htop n Hrf Hmc Hbud o.
  pose proof (u64_range (vm_init_sp (m_vmmaps model))) as Hcv. pose proof Htop as Htop'. unfold alloc_top, stack_max_size in Htop'.
  assert (Hlen' : (len < 2 ^ 64)%Z).
  { pose proof (page_round_up_Z_bounds len ltac:(lia)). pose proof (u64_range addr). lia. }
  assert (Hu1 : bv_unsigned (ms_gpr ms 1) = len) by (rewrite H1; apply u64_lit; lia).
  assert (E1 : w_is0 (ms_gpr ms 1) = false).
  { unfold w_is0. apply bv_eqb_neq. intros Hz. rewrite Hz in Hu1. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in Hu1. lia. }
  destruct (mmap_gates_core50 flags (Z_to_bv 64 prot) Hcore) as (G1 & G2 & G3 & G4 & G5).
  rewrite (syscall_spec_222 _ model o) by (rewrite in_sysno_sys_input; exact Hno).
  rewrite in_arg0_si, in_arg1_si, in_arg2_si, in_arg3_sys_input, in_arg4_sys_input, in_arg5_sys_input.
  rewrite H0, H2, H3, H5.
  unfold fixedin_ok_eff, fixedin_ok_model, fixedin_ok_vmmaps, fixedin_destroyed_model. unfold n.
  destruct Hprot as [-> | ->].
  -
    rewrite (mmap_fixed_noaccess_outcome addr (ms_gpr ms 1) (Z_to_bv 64 0) flags (ms_gpr ms 4) (Z_to_bv 64 0) _ model o
               mmap_off_aligned_b_0 (mmap_anon_b_of_core flags _ Hcore eq_refl) E1 G1 G2 G3);
      rewrite ?Hu1; [reflexivity | exact Htop | exact Hal | exact Hpos | exact Hrf | exact Hmc].
  -
    rewrite (mmap_fixed_rw_commit_outcome addr (ms_gpr ms 1) (Z_to_bv 64 3) flags (ms_gpr ms 4) (Z_to_bv 64 0) _ model o
               mmap_off_aligned_b_0 (mmap_anon_b_of_core flags _ Hcore eq_refl) E1 G1 G2 G4 G5);
      rewrite ?Hu1; [| exact Htop | exact Hal | exact Hpos | exact Hrf | exact Hmc].
    cbn [Z.eqb]. split.
    + intros [He | [(_ & ->) | Hd]]; [left; exact He | right; left; reflexivity | right; right; exact Hd].
    + intros [He | [-> | Hd]]; [left; exact He | right; left; split; [exact (Hbud eq_refl) | reflexivity] | right; right; exact Hd].
Qed.

Lemma srz_mmap_fixedin_lazy {AF : AllocForced SC} :
  forall regs (pc : word) mem rom model w (prot : Z) (flags addr : word) (len : Z) KB,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None ->
  getr regs 17 = Z_to_bv 64 222 ->
  (prot = 0 \/ prot = 3)%Z -> mmap_flags_core flags = 50%Z ->
  getr regs 10 = addr -> (bv_unsigned addr mod page_size = 0)%Z -> (0 < bv_unsigned addr)%Z ->
  getr regs 11 = Z_to_bv 64 len -> (0 < len)%Z ->
  (bv_unsigned addr + page_round_up_Z len <= alloc_top (m_vmmaps model))%Z ->
  getr regs 12 = Z_to_bv 64 prot -> getr regs 13 = flags ->
  getr regs 14 = Z_to_bv 64 (-1) -> getr regs 15 = Z_to_bv 64 0 ->
  let n := Z_to_bv 64 (page_round_up_Z len) in
  region_free (vm_reserved (m_vmmaps model)) addr n = true ->
  map_contains (vm_maps (m_vmmaps model)) addr n = true ->
  (prot = 3%Z -> mmap_fixed_rw_budget_ok flags model addr n = true) ->
  srealizes segs (mkCfg (mkst (regupd regs 10 addr) (v_addi pc 4)
                             (if Z.eqb prot 0 then unfill addr n mem else zfill addr n mem) rom)
                       (fixedin_ok_model prot flags addr n model)) KB ->
  srealizes segs (mkCfg (mkst regs pc mem rom) model) KB.
Proof.
  intros regs pc mem rom model w prot flags addr len KB HF HE Hh H17 Hprot Hcore H10 Hal Hpos H11 Hlen Htop H12 H13 H14 H15 n Hrf Hmc Hbud HB.
  pose proof (u64_range (vm_init_sp (m_vmmaps model))) as Hcv. pose proof (u64_range addr) as Har.
  pose proof Htop as Htop'. unfold alloc_top, stack_max_size in Htop'.
  eapply srz_sys_lazy; [exact Hh | exact HF | exact HE |].
  set (ms := epend regs pc mem rom (getr regs 17)).
  assert (Hno : bv_unsigned (getr regs 17) = 222%Z) by (rewrite H17; apply u64_lit; lia).
  assert (Hno' : bv_unsigned (in_sysno (sys_input segs ms (getr regs 17))) = 222%Z) by (rewrite in_sysno_sys_input; exact Hno).
  assert (Hlen' : (len < 2 ^ 64)%Z) by (pose proof (page_round_up_Z_bounds len ltac:(lia)); lia).
  pose proof (mmap_fixedin_outcome_si ms (getr regs 17) model prot flags addr len Hno Hprot Hcore
                           ltac:(unfold ms; rewrite ms_gpr_epend0; exact H10) Hal Hpos
                           ltac:(unfold ms; rewrite ms_gpr_epend1; exact H11) Hlen
                           ltac:(unfold ms; rewrite ms_gpr_epend2; exact H12)
                           ltac:(unfold ms; rewrite ms_gpr_epend3; exact H13)
                           ltac:(unfold ms; rewrite ms_gpr_epend4; exact H14)
                           ltac:(unfold ms; rewrite ms_gpr_epend5; exact H15)
                           Htop Hrf Hmc Hbud) as Hsi.
  cbv zeta in Hsi. fold n in Hsi.
  assert (Haddr_ne : addr <> errno_ret ENOMEM).
  { intros E. apply (f_equal bv_unsigned) in E. rewrite (errno_ret_unsigned ENOMEM) in E by (unfold ENOMEM; lia).
    unfold two_pow_64, ENOMEM in E. pose proof (page_round_up_Z_bounds len ltac:(lia)). lia. }

  assert (Hok : syscall_spec (sys_input segs ms (getr regs 17)) model
                  (Ok (fixedin_ok_eff prot addr n) (fixedin_ok_model prot flags addr n model) [])).
  { apply Hsi. right; left. reflexivity. }
  assert (Hokr : refusal_b (sys_input segs ms (getr regs 17)) model (eff_ret (fixedin_ok_eff prot addr n)) = false).
  { rewrite (refusal_b_mmap _ model _ Hno'). unfold fixedin_ok_eff. destruct (Z.eqb prot 0); cbn [eff_ret];
      apply bv_eqb_neq; exact Haddr_ne. }
  assert (Hspur : forall ws zs us cs ci,
            spurious_refusal_cfg the_scfg (sys_input segs ms (getr regs 17)) model (mkEffectU (errno_ret ENOMEM) ws zs us cs ci)).
  { intros ws zs us cs ci.
    apply (alloc_refusal_spurious _ model _ (fixedin_ok_eff prot addr n) (fixedin_ok_model prot flags addr n model) []).
    - apply family_off_mmap_true. exact Hno'.
    - cbn [eff_ret]. apply errno_is_refusal_mmap. exact Hno'.
    - exact Hok.
    - exact Hokr. }
  apply (srz_silent_all segs (mkCfg ms model) unit
           (fun _ => mkCfg (advance_past_svc (apply_effect ms (fixedin_ok_eff prot addr n))) (fixedin_ok_model prot flags addr n model)) KB tt).
  - apply (node_fam_noacc ms model (getr regs 17) unit (fun _ => fixedin_ok_eff prot addr n)
             (fun _ => fixedin_ok_model prot flags addr n model) _ Hh eq_refl Hsi).
    + intros []. right; left. reflexivity.
    + intros []. apply spurious_refusal_not_refusal. exact Hokr.
    + intros eff m' evs [He | [E | (e & He & E)]] Hns.
      *
        exfalso. apply Hns. apply mmap_err_out_enomem in He. apply Ok_inj in He as (-> & -> & ->). apply Hspur.
      * apply Ok_inj in E as (-> & -> & ->). exists tt. repeat split; reflexivity.
      *
        exfalso. apply Hns. apply Ok_inj in E as (-> & -> & ->).
        assert (He' : e = ENOMEM) by (destruct He as [<-|[]]; reflexivity). subst e. apply Hspur.
    +
      intros eff m' evs [He | [E | (e & He & E)]].
      * apply mmap_err_out_enomem in He. apply Ok_inj in He as (-> & -> & ->). exact Hh.
      * apply Ok_inj in E as (-> & -> & ->).
        unfold fixedin_ok_model; rewrite with_mmap_replacement_halted', with_vmmaps_halted; exact Hh.
      * apply Ok_inj in E as (-> & -> & ->).
        unfold fixedin_destroyed_model. rewrite with_mmap_destroyed_halted'. exact Hh.
    + intros [He | [E | (e & He & E)]];
        [apply mmap_err_out_enomem in He; exact (Unmodeled_Ok _ _ _ He) | exact (Unmodeled_Ok _ _ _ E) | exact (Unmodeled_Ok _ _ _ E)].
    + intros []. unfold fixedin_ok_eff. destruct (Z.eqb prot 0); reflexivity.
  - intros []. unfold ms, fixedin_ok_eff. destruct (Z.eqb prot 0).
    + rewrite adv_unmaps1_epend. exact HB.
    + rewrite adv_zeros1_epend. exact HB.
Qed.

End Noacc.

Open Scope Z_scope.
Import AX2 AX2S AP APS.

Lemma is_ecall_at_sound : forall SEGS cs,
  is_ecall_at SEGS cs = true ->
  0 <= pc cs /\ pc cs + 4 < two64 /\
  exists w, fetch_word SEGS (Z_to_bv 64 (pc cs)) = Some w /\ is_ecall w = true.
Proof.
  intros SEGS cs H. unfold is_ecall_at in H.
  apply andb_prop in H as [H Hf]. apply andb_prop in H as [H0 H4].
  apply Z.leb_le in H0. apply Z.ltb_lt in H4.
  destruct (fetch_word SEGS (Z_to_bv 64 (pc cs))) as [w|] eqn:Hw; [|discriminate].
  repeat split; try assumption. exists w. auto.
Qed.

Lemma bv_and_255 : forall c0, 0 <= c0 < two64 ->
  bv_and (Z_to_bv 64 c0) (Z_to_bv 64 255) = Z_to_bv 64 (Z.land c0 255).
Proof.
  intros c0 Hc. apply bv_eq. rewrite bv_and_unsigned, !u64_lit by (unfold two64 in *; lia).
  change 255%Z with (Z.ones 8). rewrite Z.land_ones by lia.
  symmetry. apply u64_lit. unfold two64 in *.
  pose proof (Z.mod_pos_bound c0 (2 ^ 8) ltac:(lia)). lia.
Qed.

Lemma Some_inj : forall {T : Type} (a b : T), Some a = Some b -> a = b.
Proof. intros T a b H. congruence. Qed.

Lemma v_addi_pc : forall p, 0 <= p -> p + 4 < two64 ->
  v_addi (Z_to_bv 64 p) 4 = Z_to_bv 64 (p + 4).
Proof.
  intros p H0 H4. unfold v_addi. f_equal. unfold two64 in *. rewrite u64_lit by lia. reflexivity.
Qed.

Section CsOk.
Variable SEGS : list Segment.
Variable A : atable.
Variable nx0 : nat.
Variable LIMIT : Z.
Variable SINV : env -> (word -> option byte) -> Prop.
Variable argH : env -> word -> bool.
Variable FS0 : Fs.Fs.
#[local] Notation cs_ok := (APS.cs_ok SEGS A LIMIT SINV argH FS0).

End CsOk.
