(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.ASN Require Import
  SimInv ExitSim PropExec CatExec CatSim SeqExec StreamExec MmapSim AllocSim FileSim
  ShapeAlg SpinAlg Nodes StoreOk AgentLib AgentNodes RefNodes
  AsanAcct AsanAcctShape AsanPlacement BackingAlgebra.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.ASN Require Import AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.ASN Require Import AsanCeil.

Unset Lia Cache.
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.
Import ListNotations.
Open Scope bv_scope.

Section Noacc.
Variable segs : list Segment.

#[using="Type"] Lemma sstep_of_check_noacc : forall ms model x8 eff m' evs,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  check_syscall (sys_input segs ms x8) eff model = CheckOk m' evs ->
  m_halted m' = None ->
  syscall_effect_accesses eff = [] ->
  sstep segs (mkCfg ms model) evs (SNext (mkCfg (advance_past_svc (apply_effect ms eff)) m')).
Proof.
  intros ms model x8 eff m' evs Hh Hsvc Hc Hh' Hacc.
  apply (sstep_syscall segs ms model x8 eff m' m' evs Hh Hsvc).
  - apply check_syscall_ok_iff. exact Hc.
  - exact Hh'.
  - rewrite Hacc. apply materialize_model_accesses_nil.
Qed.

#[using="Type"] Lemma node_chk_ev_noacc : forall ms model x8 (I : Type)
    (effs : I -> SyscallEffect) (ms' : I -> Model) (evs : I -> list event),
  m_halted model = None -> ms_svc_pending ms = Some x8 ->
  (forall i, check_syscall (sys_input segs ms x8) (effs i) model = CheckOk (ms' i) (evs i)) ->
  (forall i, ~ spurious_refusal_cfg ACFG (sys_input segs ms x8) model (effs i)) ->
  (forall eff m' ev, check_syscall (sys_input segs ms x8) eff model = CheckOk m' ev ->
     spec_step_ok (sys_input segs ms x8) model (Ok eff m' ev) ->
     exists i, eff = effs i /\ m' = ms' i /\ ev = evs i) ->
  (forall eff, check_syscall (sys_input segs ms x8) eff model <> CheckUnmodeled) ->
  (forall i, m_halted (ms' i) = None) ->
  (forall i, syscall_effect_accesses (effs i) = []) ->
  node_ok segs (mkCfg ms model) I evs
          (fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms' i)).
Proof.
  intros ms model x8 I effs ms' evs running pending accepts genuine only_these modeled
    stay_running touch_free.
  assert (pick : forall eff m1 ev0,
             syscall_spec_acfg (sys_input segs ms x8) model (Ok eff m1 ev0) ->
             exists i, eff = effs i /\ m1 = ms' i /\ ev0 = evs i).
  { intros eff m1 ev0 [in_spec spec_fine].
    apply only_these; [apply check_syscall_ok_iff; exact in_spec | exact spec_fine]. }
  split.
  - intro i.
    apply (sstep_cfg_syscall segs ACFG ms model x8 (effs i) (ms' i) (ms' i) (evs i) running pending).
    + apply check_syscall_ok_iff. apply accepts.
    + apply genuine.
    + apply stay_running.
    + rewrite touch_free. apply materialize_model_accesses_nil.
  - intros e st stepped.
    destruct (sstep_cfg_sys_inv_acfg segs ms model x8 e st pending stepped)
      as [[eff [m1 [ev0 [legal [_ landing]]]]]
         | [[eff [m1 [ev0 [code [legal [stopped _]]]]]]
         | [[eff [m1 [ev0 [sig [legal [slain _]]]]]]
         | [unmod _]]]].
    + destruct (pick eff m1 ev0 legal) as [k [-> [-> ->]]].
      rewrite touch_free, materialize_model_accesses_nil in landing.
      destruct landing as [-> ->].
      exists k. split; reflexivity.
    + exfalso. destruct (pick eff m1 ev0 legal) as [k [_ [-> _]]].
      rewrite stay_running in stopped. discriminate stopped.
    + exfalso. destruct (pick eff m1 ev0 legal) as [k [_ [-> _]]].
      rewrite (m_killed_of_m_halted_none _ (stay_running k)) in slain. discriminate slain.
    + exfalso. apply (modeled (mkEffect (Z_to_bv 64 0) [] [])).
      apply check_syscall_complete_unmodeled.
      exact (proj1 (syscall_spec_acfg_unmodeled _ _) unmod).
Qed.

#[using="Type"] Lemma node_chk_noacc : forall ms model x8 (I : Type) (effs : I -> SyscallEffect) (ms' : I -> Model),
  m_halted model = None -> ms_svc_pending ms = Some x8 ->
  (forall i, check_syscall (sys_input segs ms x8) (effs i) model = CheckOk (ms' i) []) ->
  (forall i, ~ spurious_refusal_cfg ACFG (sys_input segs ms x8) model (effs i)) ->
  (forall eff m' evs, check_syscall (sys_input segs ms x8) eff model = CheckOk m' evs ->
     spec_step_ok (sys_input segs ms x8) model (Ok eff m' evs) ->
     exists i, eff = effs i /\ m' = ms' i /\ evs = []) ->
  (forall eff, check_syscall (sys_input segs ms x8) eff model <> CheckUnmodeled) ->
  (forall i, m_halted (ms' i) = None) ->
  (forall i, syscall_effect_accesses (effs i) = []) ->
  node_ok segs (mkCfg ms model) I (fun _ => [])
          (fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms' i)).
Proof.
  intros ms model x8 I effs ms' running pending accepts genuine only_these modeled
    stay_running touch_free.
  exact (node_chk_ev_noacc ms model x8 I effs ms' (fun _ => []) running pending accepts genuine
           only_these modeled stay_running touch_free).
Qed.

#[using="Type"] Lemma node_det_noacc : forall ms model x8 eff0 m0 evs0,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  (forall eff m' evs,
     check_syscall (sys_input segs ms x8) eff model = CheckOk m' evs <->
     (eff = eff0 /\ m' = m0 /\ evs = evs0)) ->
  (forall eff, check_syscall (sys_input segs ms x8) eff model <> CheckUnmodeled) ->
  m_halted m0 = None ->
  syscall_effect_accesses eff0 = [] ->
  node_ok segs (mkCfg ms model) unit (fun _ => evs0)
          (fun _ => mkCfg (advance_past_svc (apply_effect ms eff0)) m0).
Proof.
  intros ms model x8 eff0 m0 evs0 running pending exact_outcome modeled m0_running touch_free.
  apply (node_chk_ev_noacc ms model x8 unit (fun _ => eff0) (fun _ => m0) (fun _ => evs0)
           running pending).
  - intros _. apply exact_outcome. repeat split.
  - intros _. exact (check_det_nonspurious _ model eff0 m0 evs0 exact_outcome).
  - intros eff m' ev accepted _. exists tt. exact (proj1 (exact_outcome eff m' ev) accepted).
  - exact modeled.
  - intros _. exact m0_running.
  - intros _. exact touch_free.
Qed.

#[using="Type"] Lemma rz_det_noacc : forall ms model x8 eff0 m0 T,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  (forall eff m' evs,
     check_syscall (sys_input segs ms x8) eff model = CheckOk m' evs <->
     (eff = eff0 /\ m' = m0 /\ evs = [])) ->
  (forall eff, check_syscall (sys_input segs ms x8) eff model <> CheckUnmodeled) ->
  m_halted m0 = None ->
  syscall_effect_accesses eff0 = [] ->
  realizes segs (mkCfg (advance_past_svc (apply_effect ms eff0)) m0) T ->
  realizes segs (mkCfg ms model) T.
Proof.
  intros ms model x8 eff0 m0 T Hh Hsvc Hchk Hnu Hh0 Hacc Hc.
  eapply rz_silent1; [eapply node_det_noacc; eassumption | exact Hc].
Qed.

#[using="Type"] Lemma srz_det_noacc : forall ms model x8 eff0 m0 T,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  (forall eff m' evs,
     check_syscall (sys_input segs ms x8) eff model = CheckOk m' evs <->
     (eff = eff0 /\ m' = m0 /\ evs = [])) ->
  (forall eff, check_syscall (sys_input segs ms x8) eff model <> CheckUnmodeled) ->
  m_halted m0 = None ->
  syscall_effect_accesses eff0 = [] ->
  srealizes segs (mkCfg (advance_past_svc (apply_effect ms eff0)) m0) T ->
  srealizes segs (mkCfg ms model) T.
Proof.
  intros ms model x8 eff0 m0 T Hh Hsvc Hchk Hnu Hh0 Hacc Hc.
  eapply srz_silent1; [eapply node_det_noacc; eassumption | exact Hc].
Qed.

#[using="Type"] Lemma srz_cases : forall c (I : Type) (nx : I -> config) (T : I -> TSet) (i0 : I),
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

#[using="Type"] Lemma with_vm_backing_halted : forall l p m, m_halted (with_vm_backing l p m) = m_halted m.
Proof. reflexivity. Qed.

#[using="Type"] Lemma vm_add_lazy_halted : forall a n m, m_halted (vm_add_lazy a n m) = m_halted m.
Proof. reflexivity. Qed.

#[using="Type"] Lemma with_mmap_backing_halted : forall flags a n m,
  m_halted (with_mmap_backing flags a n m) = m_halted m.
Proof. intros. unfold with_mmap_backing. destruct (mmap_noreserve_b flags); reflexivity. Qed.

#[using="Type"] Lemma with_mmap_replacement_halted : forall flags a n m,
  m_halted (with_mmap_replacement flags a n m) = m_halted m.
Proof.
  intros. unfold with_mmap_replacement. rewrite with_mmap_backing_halted.
  apply vm_forget_range_halted.
Qed.

#[using="Type"] Lemma with_mmap_destroyed_halted : forall a n h m,
  m_halted (with_mmap_destroyed a n h m) = m_halted m.
Proof. intros. unfold with_mmap_destroyed. rewrite vm_forget_range_halted. apply with_vmmaps_halted. Qed.


#[using="Type"] Lemma stepacc_ecall_epend : forall regs pc mem rom w,
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

#[using="Type"] Lemma node_instr_noacc : forall ms model ms',
  m_halted model = None ->
  ms_svc_pending ms = None ->
  RiscvSemantics.step_accesses segs ms = MachineOk (@mkAccessReport machine_state ms' []) ->
  node_ok segs (mkCfg ms model) unit (fun _ => []) (fun _ => mkCfg ms' model).
Proof.
  intros ms model ms' running no_svc clean_step.
  assert (acct : mi_account_step segs ms model = MachineOk (ms', model))
    by exact (DivergeSim.mi_account_step_no_access segs ms model ms' clean_step).
  split.
  - intros []. exact (sstep_cfg_instr segs ACFG ms model ms' model running no_svc acct).
  - intros e st stepped. exists tt.
    exact (sstep_instr_det segs ms model ms' model e st no_svc acct (sstep_of_cfg segs _ e st stepped)).
Qed.

#[using="Type"] Lemma rz_sys_lazy : forall regs pc mem rom model w T,
  m_halted model = None ->
  fetch_word segs pc = Some w -> is_ecall w = true ->
  realizes segs (mkCfg (epend regs pc mem rom (getr regs 17)) model) T ->
  realizes segs (mkCfg (mkst regs pc mem rom) model) T.
Proof.
  intros regs pc mem rom model w T Hh HF HE Hc.
  eapply rz_silent1; [| exact Hc].
  apply node_instr_noacc; [exact Hh | reflexivity | eapply stepacc_ecall_epend; eassumption].
Qed.

#[using="Type"] Lemma epend_len : forall regs pc mem rom (len : Z),
  getr regs 11 = Z_to_bv 64 len -> (0 < len < 2 ^ 64)%Z ->
  bv_unsigned (ms_gpr (epend regs pc mem rom (getr regs 17)) 1) = len
  /\ ms_gpr (epend regs pc mem rom (getr regs 17)) 1 <> Z_to_bv 64 0.
Proof.
  intros regs pc mem rom len H11 Hlen. rewrite ms_gpr_epend1, H11. split.
  - apply u64_lit. lia.
  - intro Hc. apply (f_equal bv_unsigned) in Hc. rewrite u64_lit in Hc by lia.
    change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in Hc. lia.
Qed.

#[using="Type"] Lemma srz_sys_lazy : forall regs pc mem rom model w T,
  m_halted model = None ->
  fetch_word segs pc = Some w -> is_ecall w = true ->
  srealizes segs (mkCfg (epend regs pc mem rom (getr regs 17)) model) T ->
  srealizes segs (mkCfg (mkst regs pc mem rom) model) T.
Proof.
  intros regs pc mem rom model w T Hh HF HE Hc.
  eapply srz_silent1; [| exact Hc].
  apply node_instr_noacc; [exact Hh | reflexivity | eapply stepacc_ecall_epend; eassumption].
Qed.

#[using="Type"] Lemma srz_munmap_lazy : forall regs (pc : word) mem rom model w (a : word) (len : Z) K,
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
  { pose proof (page_round_up_Z_bounds len ltac:(lia)). pose proof (u64_range a). unfold TASK_SIZE, two_pow_64 in *. lia. }
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
  pose proof (fun eff => eq_trans (munmap_check segs ms (getr regs 17) model eff Hno) (munmap_check_modeled ms model eff Hargs)) as Hchk.
  rewrite H0, Hpr in Hchk.
  eapply (srz_det_noacc ms model (getr regs 17)
            (mkEffectU (Z_to_bv 64 0) [] [] [(a, Z_to_bv 64 (page_round_up_Z len))] [] [])
            (munmap_model a (Z_to_bv 64 (page_round_up_Z len)) model));
    [exact Hh | reflexivity | | | | reflexivity |].
  - intros eff m' evs. split.
    + intros Hck. rewrite Hchk in Hck. destruct eff as [r ws zs us cs ci].
      destruct ws; [|discriminate]. destruct zs; [|discriminate].
      destruct cs; [|discriminate]. destruct ci; [|discriminate].
      destruct (w_is0 r) eqn:E0; [|discriminate].
      destruct (listNN_eqb us [(a, Z_to_bv 64 (page_round_up_Z len))]) eqn:Hl; [|discriminate].
      apply listNN_eqb_eq in Hl. subst us. cbn [andb] in Hck. injection Hck as <- <-.
      unfold w_is0 in E0. apply bv_eqb_eq in E0. subst r. repeat split; reflexivity.
    + intros (-> & -> & ->). rewrite Hchk. unfold w_is0. rewrite bv_eqb_refl.
      rewrite (proj2 (listNN_eqb_eq _ _) eq_refl). reflexivity.
  - intros eff Hck. rewrite Hchk in Hck. destruct eff as [r ws zs us cs ci].
    destruct ws; [|discriminate]. destruct zs; [|discriminate].
    destruct cs; [|discriminate]. destruct ci; [|discriminate].
    destruct (w_is0 r && listNN_eqb us _)%bool; discriminate.
  - rewrite munmap_model_halted. exact Hh.
  - unfold ms. rewrite adv_unmaps1_epend. exact Hc.
Qed.

#[using="Type"] Lemma node_brk_lazy : forall ms model x8,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 214%Z ->
  node_ok segs (mkCfg ms model)
    {r : word | brk_res_acfg model (ms_gpr ms 0) r}
    (fun _ => [])
    (fun i => mkCfg (advance_past_svc (apply_effect ms
                       (mkEffectU (proj1_sig i) []
                          (brk_zeros (ms_gpr ms 0) (proj1_sig i) (vm_brk (m_vmmaps model)))
                          (brk_unmaps (proj1_sig i) (vm_brk (m_vmmaps model))) [] [])))
                    (brk_model (ms_gpr ms 0) (proj1_sig i) model)).
Proof.
  intros ms model x8 running pending is_brk.
  assert (granted : forall r, brk_res_acfg model (ms_gpr ms 0) r ->
            syscall_spec_acfg (sys_input segs ms x8) model
              (Ok (mkEffectU r [] (brk_zeros (ms_gpr ms 0) r (vm_brk (m_vmmaps model)))
                     (brk_unmaps r (vm_brk (m_vmmaps model))) [] [])
                  (brk_model (ms_gpr ms 0) r model) [])).
  { intros r chosen. apply (proj2 (brk_acfg_iff segs ms x8 model _ _ _ running is_brk)).
    exact (conj eq_refl (conj eq_refl (conj chosen eq_refl))). }
  apply (node_chk_noacc ms model x8 {r : word | brk_res_acfg model (ms_gpr ms 0) r}
           (fun i => mkEffectU (proj1_sig i) [] (brk_zeros (ms_gpr ms 0) (proj1_sig i) (vm_brk (m_vmmaps model)))
                       (brk_unmaps (proj1_sig i) (vm_brk (m_vmmaps model))) [] [])
           (fun i => brk_model (ms_gpr ms 0) (proj1_sig i) model) running pending).
  - intros [r chosen]. apply check_syscall_ok_iff. exact (proj1 (granted r chosen)).
  - intros [r chosen]. apply (acfg_outcome_ok_nonspurious _ _ _ _ _ (granted r chosen)).
    rewrite brk_model_halted. exact running.
  - intros eff m' evs accepted fine.
    destruct (proj1 (brk_acfg_iff segs ms x8 model eff m' evs running is_brk)
                (conj (proj1 (check_syscall_ok_iff _ _ _ _ _) accepted) fine))
      as [shape [-> [chosen ->]]].
    exists (exist _ (eff_ret eff) chosen). split; [exact shape | split; reflexivity].
  - intros eff unmod.
    exact (brk_no_unmodeled segs ms x8 model is_brk (check_syscall_sound_unmodeled _ eff model unmod)).
  - intros [r chosen]. exact (eq_trans (brk_model_halted _ _ _) running).
  - intros i. reflexivity.
Qed.

#[using="Type"] Lemma srz_brk_query_lazy : forall regs (pc : word) mem rom model w K,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None ->
  getr regs 17 = Z_to_bv 64 214 ->
  getr regs 10 = Z_to_bv 64 0 ->
  srealizes segs (mkCfg (mkst (regupd regs 10 (vm_brk (m_vmmaps model))) (v_addi pc 4) mem rom) model) K ->
  srealizes segs (mkCfg (mkst regs pc mem rom) model) K.
Proof.
  intros regs pc mem rom model w K fetched ecall running sys214 arg_zero cont.
  eapply srz_sys_lazy; [exact running | exact fetched | exact ecall |].
  set (ms := epend regs pc mem rom (getr regs 17)).
  assert (is_brk : bv_unsigned (getr regs 17) = 214%Z) by (rewrite sys214; reflexivity).
  assert (req0 : ms_gpr ms 0 = Z_to_bv 64 0) by (unfold ms; rewrite ms_gpr_epend0; exact arg_zero).
  assert (null_req : w_is0 (Z_to_bv 64 0) = true) by reflexivity.
  assert (only_old : forall r, brk_res_acfg model (ms_gpr ms 0) r -> r = vm_brk (m_vmmaps model)).
  { intros r [resolved _]. unfold brk_resolution_ok, Mmap.brk_r_ok in resolved.
    rewrite req0, null_req in resolved. cbn [orb] in resolved.
    apply bv_eqb_eq. exact resolved. }
  assert (old_ok : brk_res_acfg model (ms_gpr ms 0) (vm_brk (m_vmmaps model))).
  { split.
    - unfold brk_resolution_ok, Mmap.brk_r_ok. rewrite req0, null_req. cbn [orb].
      apply bv_eqb_refl.
    - intro refused. unfold brk_refusal_b in refused. rewrite req0, null_req in refused.
      cbn [negb andb] in refused. discriminate refused. }
  apply (srz_conseq segs _ (t_alt (fun _ : {r : word | brk_res_acfg model (ms_gpr ms 0) r} => K))).
  - eapply (srz_cases _ _ _ (fun _ => K) (exist _ _ old_ok)).
    + exact (node_brk_lazy ms model (getr regs 17) running (epend_svc _ _ _ _ _) is_brk).
    + intros [r chosen]. cbn [proj1_sig].
      apply only_old in chosen. subst r.
      rewrite brk_zeros_keep, brk_unmaps_keep, brk_model_keep.
      unfold ms. rewrite adv_eff_ret_epend. exact cont.
  - intro tr. split.
    + intros [_ took]. exact took.
    + intro took. exists (exist _ _ old_ok). exact took.
Qed.

#[using="Type"] Lemma srz_brk_grow_lazy : forall regs (pc : word) mem rom model w (d : Z) KB,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None ->
  getr regs 17 = Z_to_bv 64 214 ->
  let h := m_vmmaps model in
  let b := vm_brk h in
  (bv_unsigned b mod page_size = 0)%Z -> (d mod page_size = 0)%Z -> (0 < d)%Z ->
  (0 < bv_unsigned b)%Z -> (bv_unsigned b + d < 2 ^ 64)%Z ->
  (bv_unsigned (vm_start_brk h) <= bv_unsigned b + d)%Z ->
  getr regs 10 = Z_to_bv 64 (bv_unsigned b + d) ->
  Mmap.brk_grow_ok model (Z_to_bv 64 (bv_unsigned b + d)) (Z_to_bv 64 (bv_unsigned b + d)) = true ->


  srealizes segs (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 (bv_unsigned b + d))) (v_addi pc 4)
                             (zfill b (Z_to_bv 64 d) mem) rom)
                       (with_vmmaps (mkVmMapsFull (vm_reserved h) ((b, Z_to_bv 64 d) :: vm_maps h)
                                      (vm_noaccess h) (vm_start_brk h)
                                      (Z_to_bv 64 (bv_unsigned b + d)) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)) model)) KB ->
  srealizes segs (mkCfg (mkst regs pc mem rom) model) KB.
Proof.
  intros regs pc mem rom model w d KB fetched ecall running sys214 h b b_page d_page d_pos b_pos
    fits above_start arg_top grows grown.
  subst b h.
  eapply srz_sys_lazy; [exact running | exact fetched | exact ecall |].
  set (ms := epend regs pc mem rom (getr regs 17)).
  assert (is_brk : bv_unsigned (getr regs 17) = 214%Z) by (rewrite sys214; reflexivity).
  pose proof (u64_range (vm_brk (m_vmmaps model))) as old_range.
  pose proof (brk_model_grow_eq model d d_pos b_pos fits b_page d_page) as grown_model.
  set (top := Z_to_bv 64 (bv_unsigned (vm_brk (m_vmmaps model)) + d)) in *.
  assert (top_val : bv_unsigned top = (bv_unsigned (vm_brk (m_vmmaps model)) + d)%Z)
    by (unfold top; apply u64_lit; unfold two_pow_64 in *; lia).
  assert (arg0 : ms_gpr ms 0 = top) by (unfold ms; rewrite ms_gpr_epend0; exact arg_top).
  assert (top_live : w_is0 top = false) by (apply w_is0_pos; rewrite top_val; lia).
  assert (top_nz : top <> Z_to_bv 64 0).
  { intro is_zero. apply (f_equal bv_unsigned) in is_zero.
    rewrite top_val, (u64_lit 0) in is_zero by lia. lia. }
  assert (top_differs : bv_eqb top (vm_brk (m_vmmaps model)) = false).
  { destruct (bv_eqb top (vm_brk (m_vmmaps model))) eqn:same; [|reflexivity].
    apply bv_eqb_eq in same. apply (f_equal bv_unsigned) in same. rewrite top_val in same. lia. }
  assert (top_not_low : (bv_unsigned top <? bv_unsigned (vm_start_brk (m_vmmaps model)))%Z = false)
    by (apply Z.ltb_ge; rewrite top_val; exact above_start).
  assert (refusal_is_old : forall ret, brk_refusal_b model top ret = bv_eqb ret (vm_brk (m_vmmaps model))).
  { intro ret. unfold brk_refusal_b, min_brk. cbv zeta.
    rewrite top_live, top_not_low, top_differs. reflexivity. }
  assert (cases : forall r, brk_resolution_ok model top r <->
                   r = vm_brk (m_vmmaps model) \/ (r = top /\ Mmap.brk_grow_ok model top top = true)).
  { intro r. apply brk_r_ok_grow_cases; rewrite top_val; lia. }
  assert (top_ok : brk_res_acfg model (ms_gpr ms 0) top).
  { rewrite arg0. split.
    - apply cases. right. split; [reflexivity | exact grows].
    - intro refused. rewrite refusal_is_old, top_differs in refused. discriminate refused. }
  assert (only_top : forall r, brk_res_acfg model (ms_gpr ms 0) r -> r = top).
  { intros r chosen. rewrite arg0 in chosen. destruct chosen as [resolved no_better].
    apply cases in resolved as [is_old | [is_top _]]; [|exact is_top].
    exfalso. subst r.
    assert (old_refused : brk_refusal_b model top (vm_brk (m_vmmaps model)) = true)
      by (rewrite refusal_is_old; apply bv_eqb_refl).
    pose proof (no_better old_refused top (proj2 (cases top) (or_intror (conj eq_refl grows))))
      as top_refused.
    rewrite refusal_is_old, top_differs in top_refused. discriminate top_refused. }
  assert (zeros_eq : brk_zeros top top (vm_brk (m_vmmaps model)) = [(vm_brk (m_vmmaps model), Z_to_bv 64 d)]).
  { rewrite brk_zeros_aligned_grow; [| exact top_nz | exact b_pos | rewrite top_val; lia | exact b_page].
    rewrite top_val, page_round_up_Z_aligned.
    - do 3 f_equal. lia.
    - lia.
    - rewrite Z.add_mod, b_page, d_page by (unfold page_size; lia). reflexivity. }
  assert (unmaps_eq : brk_unmaps top (vm_brk (m_vmmaps model)) = [])
    by (apply brk_unmaps_grow; rewrite top_val; lia).
  apply (srz_conseq segs _ (t_alt (fun _ : {r : word | brk_res_acfg model (ms_gpr ms 0) r} => KB))).
  - eapply (srz_cases _ _ _ (fun _ => KB) (exist _ _ top_ok)).
    + exact (node_brk_lazy ms model (getr regs 17) running (epend_svc _ _ _ _ _) is_brk).
    + intros [r chosen]. cbn [proj1_sig].
      apply only_top in chosen. subst r.
      rewrite arg0, zeros_eq, unmaps_eq, grown_model.
      unfold ms. rewrite adv_zeros1_epend. exact grown.
  - intro tr. split.
    + intros [_ took]. exact took.
    + intro took. exists (exist _ _ top_ok). exact took.
Qed.

#[using="Type"] Lemma srz_brk_grow_lazy_same : forall regs (pc : word) mem rom model w (d : Z) K,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None ->
  getr regs 17 = Z_to_bv 64 214 ->
  let h := m_vmmaps model in
  let b := vm_brk h in
  (bv_unsigned b mod page_size = 0)%Z -> (d mod page_size = 0)%Z -> (0 < d)%Z ->
  (0 < bv_unsigned b)%Z -> (bv_unsigned b + d < 2 ^ 64)%Z ->
  (bv_unsigned (vm_start_brk h) <= bv_unsigned b + d)%Z ->
  getr regs 10 = Z_to_bv 64 (bv_unsigned b + d) ->
  Mmap.brk_grow_ok model (Z_to_bv 64 (bv_unsigned b + d)) (Z_to_bv 64 (bv_unsigned b + d)) = true ->
  srealizes segs (mkCfg (mkst (regupd regs 10 b) (v_addi pc 4) mem rom) model) K ->
  srealizes segs (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 (bv_unsigned b + d))) (v_addi pc 4)
                             (zfill b (Z_to_bv 64 d) mem) rom)
                       (with_vmmaps (mkVmMapsFull (vm_reserved h) ((b, Z_to_bv 64 d) :: vm_maps h)
                                      (vm_noaccess h) (vm_start_brk h)
                                      (Z_to_bv 64 (bv_unsigned b + d)) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)) model)) K ->
  srealizes segs (mkCfg (mkst regs pc mem rom) model) K.
Proof.
  intros regs pc mem rom model w d K fetched ecall running sys214 h b b_page d_page d_pos b_pos
    fits above_start arg_top grows _ grown.
  exact (srz_brk_grow_lazy regs pc mem rom model w d K fetched ecall running sys214
           b_page d_page d_pos b_pos fits above_start arg_top grows grown).
Qed.

#[using="Type"] Lemma srz_brk_grow_blocked_lazy : forall regs (pc : word) mem rom model w (req : word) KA,
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
  intros regs pc mem rom model w req KA fetched ecall running sys214 h b arg_req req_pos
    above_start above_old blocked cont.
  subst b h.
  eapply srz_sys_lazy; [exact running | exact fetched | exact ecall |].
  set (ms := epend regs pc mem rom (getr regs 17)).
  assert (is_brk : bv_unsigned (getr regs 17) = 214%Z) by (rewrite sys214; reflexivity).
  assert (arg0 : ms_gpr ms 0 = req) by (unfold ms; rewrite ms_gpr_epend0; exact arg_req).
  pose proof (fun r => brk_r_ok_grow_cases model req r req_pos above_start above_old) as cases.
  assert (only_old : forall r, brk_res_acfg model (ms_gpr ms 0) r -> r = vm_brk (m_vmmaps model)).
  { intros r chosen. rewrite arg0 in chosen. destruct chosen as [resolved _].
    apply cases in resolved as [is_old | [_ grows]]; [exact is_old |].
    rewrite blocked in grows. discriminate grows. }
  assert (old_ok : brk_res_acfg model (ms_gpr ms 0) (vm_brk (m_vmmaps model))).
  { rewrite arg0. split.
    - apply cases. left. reflexivity.
    - intros refused alt alt_ok.
      apply cases in alt_ok as [-> | [_ grows]]; [exact refused |].
      rewrite blocked in grows. discriminate grows. }
  apply (srz_conseq segs _ (t_alt (fun _ : {r : word | brk_res_acfg model (ms_gpr ms 0) r} => KA))).
  - eapply (srz_cases _ _ _ (fun _ => KA) (exist _ _ old_ok)).
    + exact (node_brk_lazy ms model (getr regs 17) running (epend_svc _ _ _ _ _) is_brk).
    + intros [r chosen]. cbn [proj1_sig].
      apply only_old in chosen. subst r.
      rewrite brk_zeros_keep, brk_unmaps_keep, brk_model_keep.
      unfold ms. rewrite adv_eff_ret_epend. exact cont.
  - intro tr. split.
    + intros [_ took]. exact took.
    + intro took. exists (exist _ _ old_ok). exact took.
Qed.

#[using="Type"] Lemma node_set_tid_lazy : forall ms model x8,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 96%Z ->
  m_tid model = None ->
  node_ok segs (mkCfg ms model) tid_I (fun _ => [])
    (fun i => mkCfg (advance_past_svc (apply_effect ms (mkEffectU (proj1_sig i) [] [] [] [] [])))
                    (with_tid (proj1_sig i) model)).
Proof.
  intros ms model x8 running pending is_settid fresh.
  assert (chk : forall eff, check_syscall (sys_input segs ms x8) eff model = check_set_tid_address eff model)
    by (intro eff; apply check_syscall_96; exact is_settid).
  apply (node_chk_noacc ms model x8 tid_I (fun i => mkEffect (proj1_sig i) [] [])
           (fun i => with_tid (proj1_sig i) model) running pending).
  - intros [t [lo hi]]. rewrite chk. cbn [proj1_sig]. unfold check_set_tid_address. rewrite fresh.
    apply Z.ltb_lt in lo. apply Z.ltb_lt in hi. rewrite lo, hi. reflexivity.
  - intros t. exact (acfg_nonspurious_no segs ms x8 96%Z model _ is_settid eq_refl).
  - intros eff m' evs accepted _.
    rewrite chk in accepted. unfold check_set_tid_address in accepted. rewrite fresh in accepted.
    destruct eff as [r [|w ws] [|z zs] [|u us] [|c cs] [|ci cis]];
      cbv beta iota in accepted; try discriminate accepted.
    destruct ((0 <? bv_unsigned r)%Z && (bv_unsigned r <? PID_MAX_ENVELOPE)%Z) eqn:in_range;
      [|discriminate accepted].
    injection accepted as <- <-.
    apply andb_prop in in_range as [lo hi].
    exists (exist _ r (conj (proj1 (Z.ltb_lt _ _) lo) (proj1 (Z.ltb_lt _ _) hi))).
    repeat split.
  - intros eff. rewrite chk. unfold check_set_tid_address. rewrite fresh.
    destruct eff as [r [|w ws] [|z zs] [|u us] [|c cs] [|ci cis]]; cbv beta iota; try discriminate.
    destruct (_ && _); discriminate.
  - intros i. exact (eq_trans (with_tid_halted _ _) running).
  - intros i. reflexivity.
Qed.

#[using="Type"] Lemma srz_set_tid_lazy : forall regs (pc : word) mem rom model K w,
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

#[using="Type"] Lemma srz_exit_at_lazy : forall regs (pc : word) mem rom model w code,
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

#[using="Type"] Lemma mmap_gates_core50 : forall flags prot,
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

#[using="Type"] Lemma srz_alt3 : forall c (nx : three -> config) (A B C : TSet),
  node_ok segs c three (fun _ => []) nx ->
  srealizes segs (nx T1) A -> srealizes segs (nx T2) B -> srealizes segs (nx T3) C ->
  srealizes segs c (t_alt3 A B C).
Proof.
  intros c nx A B C Hnode HA HB HC.
  apply (srz_conseq segs c (t_alt (fun i => match i with T1 => A | T2 => B | T3 => C end))).
  - apply (srz_cases c three nx _ T1 Hnode). intros [| |]; assumption.
  - intros tr. unfold t_alt3, t_alt2, t_alt. split.
    + intros [[| |] H]; tauto.
    + intros [H | [H | H]]; [exists T1 | exists T2 | exists T3]; exact H.
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

#[using="Type"] Lemma with_mmap_replacement_halted' : forall flags a n m,
  m_halted (with_mmap_replacement flags a n m) = m_halted m.
Proof.
  intros. unfold with_mmap_replacement, with_mmap_backing, vm_forget_range.
  destruct (mmap_noreserve_b flags); reflexivity.
Qed.
#[using="Type"] Lemma with_mmap_destroyed_halted' : forall a n h m,
  m_halted (with_mmap_destroyed a n h m) = m_halted m.
Proof. intros. reflexivity. Qed.

#[using="Type"] Lemma mmap_fixedin_check : forall ms x8 model eff (prot : Z) (flags addr : word) (len : Z),
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
  check_syscall (sys_input segs ms x8) (fixedin_ok_eff prot addr n) model
    = CheckOk (fixedin_ok_model prot flags addr n model) []
  /\ (forall m' ev, check_syscall (sys_input segs ms x8) eff model = CheckOk m' ev ->
        (errno_ret_in mmap_errnos (eff_ret eff) = true /\ m_halted m' = m_halted model)
        \/ (eff = fixedin_ok_eff prot addr n /\ m' = fixedin_ok_model prot flags addr n model /\ ev = []))
  /\ check_syscall (sys_input segs ms x8) eff model <> CheckUnmodeled.
Proof.
  intros ms x8 model eff prot flags addr len is_mmap prot_cases core50 gpr0 addr_page addr_pos
    gpr1 len_pos gpr2 gpr3 gpr4 gpr5 fits n free_res inside_maps budget.
  subst n.
  pose proof (alloc_top_lt (m_vmmaps model)) as top_bound.
  pose proof (page_round_up_Z_bounds len ltac:(lia)) as round_bounds.
  pose proof (u64_range addr) as addr_range.
  unfold two_pow_64 in *.
  assert (len_val : bv_unsigned (Z_to_bv 64 len) = len) by (apply u64_lit; lia).
  assert (chk : forall e, check_syscall (sys_input segs ms x8) e model =
            check_mmap addr (Z_to_bv 64 len) (Z_to_bv 64 prot) flags (Z_to_bv 64 (-1)) (Z_to_bv 64 0) e model).
  { intro e. rewrite (mmap_check segs ms x8 model e is_mmap), gpr0, gpr1, gpr2, gpr3, gpr4, gpr5.
    reflexivity. }
  rewrite !chk.
  assert (off_ok : mmap_off_aligned_b (Z_to_bv 64 0) = true) by reflexivity.
  assert (anon : mmap_anon_b flags = true) by exact (mmap_anon_b_of_core flags 50 core50 eq_refl).
  assert (len_live : w_is0 (Z_to_bv 64 len) = false) by (apply w_is0_pos; rewrite len_val; exact len_pos).
  assert (no_wrap : (2 ^ 64 <=? bv_unsigned addr + page_round_up_Z len)%Z = false) by (apply Z.leb_gt; lia).
  assert (under_top : (bv_unsigned addr + page_round_up_Z len <=? alloc_top (m_vmmaps model))%Z = true)
    by (apply Z.leb_le; exact fits).
  assert (page_ok : (bv_unsigned addr mod page_size =? 0)%Z = true) by (apply Z.eqb_eq; exact addr_page).
  assert (above_null : (0 <? bv_unsigned addr)%Z = true) by (apply Z.ltb_lt; exact addr_pos).
  destruct (mmap_gates_core50 flags (Z_to_bv 64 prot) core50) as [not_modeled [not_noaccess [na0 [na3 rw3]]]].
  unfold check_mmap. cbv zeta.
  rewrite off_ok, anon, len_live, not_modeled, not_noaccess, len_val.
  assert (addr_not_errno : errno_ret_in mmap_errnos addr = false).
  { rewrite errno_ret_in_eq. exact (ret_in_errnos_ENOMEM_aligned addr addr_page). }
  assert (same_span : listNN_eqb [(addr, Z_to_bv 64 (page_round_up_Z len))]
                                 [(addr, Z_to_bv 64 (page_round_up_Z len))] = true)
    by (apply listNN_eqb_eq; reflexivity).
  destruct prot_cases as [-> | ->].
  - rewrite na0. unfold two_pow_64. rewrite no_wrap, under_top, page_ok, above_null, free_res, inside_maps.
    cbn [negb andb orb]. unfold fixedin_ok_eff, fixedin_ok_model, fixedin_ok_vmmaps. cbn [Z.eqb].
    split; [| split].
    + cbv beta iota. rewrite addr_not_errno, bv_eqb_refl, same_span. reflexivity.
    + intros m' ev accepted.
      destruct eff as [r [|w ws] [|z zs] us [|c cs] [|ci cis]];
        cbv beta iota in accepted; try discriminate accepted.
      cbn [eff_ret].
      destruct (errno_ret_in mmap_errnos r) eqn:refusal.
      * left. split; [reflexivity |].
        destruct us as [|u rest].
        -- injection accepted as <- _. reflexivity.
        -- destruct (listNN_eqb _ _) in accepted; [| discriminate accepted].
           injection accepted as <- _. apply with_mmap_destroyed_halted.
      * right.
        destruct (bv_eqb r addr) eqn:same_ret; [| discriminate accepted].
        destruct (listNN_eqb us _) eqn:same_us; [| discriminate accepted].
        apply bv_eqb_eq in same_ret. apply listNN_eqb_eq in same_us. subst r us.
        injection accepted as <- <-. repeat split.
    + destruct eff as [r [|w ws] [|z zs] us [|c cs] [|ci cis]]; cbv beta iota; try discriminate.
      repeat match goal with
             | |- context [if ?c then _ else _] => destruct c
             | |- context [match ?l with [] => _ | _ :: _ => _ end] => destruct l
             end; discriminate.
  - rewrite na3, rw3. unfold two_pow_64.
    rewrite no_wrap, under_top, page_ok, above_null, free_res, inside_maps.
    cbn [negb andb orb]. unfold fixedin_ok_eff, fixedin_ok_model, fixedin_ok_vmmaps. cbn [Z.eqb].
    specialize (budget eq_refl).
    split; [| split].
    + cbv beta iota. rewrite addr_not_errno, bv_eqb_refl, same_span, budget. reflexivity.
    + intros m' ev accepted.
      destruct eff as [r [|w ws] zs us [|c cs] [|ci cis]];
        cbv beta iota in accepted; try discriminate accepted.
      cbn [eff_ret].
      destruct (errno_ret_in mmap_errnos r) eqn:refusal.
      * left. split; [reflexivity |].
        destruct zs as [|z rest_z]; [| discriminate accepted].
        destruct us as [|u rest].
        -- injection accepted as <- _. reflexivity.
        -- destruct (listNN_eqb _ _) in accepted; [| discriminate accepted].
           injection accepted as <- _. apply with_mmap_destroyed_halted.
      * right.
        destruct us as [|u rest]; [| discriminate accepted].
        destruct (bv_eqb r addr) eqn:same_ret; [| discriminate accepted].
        destruct (listNN_eqb zs _) eqn:same_zs; [| discriminate accepted].
        rewrite budget in accepted.
        apply bv_eqb_eq in same_ret. apply listNN_eqb_eq in same_zs. subst r zs.
        injection accepted as <- <-. repeat split.
    + destruct eff as [r [|w ws] zs us [|c cs] [|ci cis]]; cbv beta iota; try discriminate.
      repeat match goal with
             | |- context [if ?c then _ else _] => destruct c
             | |- context [match ?l with [] => _ | _ :: _ => _ end] => destruct l
             end; discriminate.
Qed.

#[using="Type"] Lemma srz_mmap_fixedin_lazy : forall regs (pc : word) mem rom model w (prot : Z) (flags addr : word) (len : Z) KB,
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
  intros regs pc mem rom model w prot flags addr len KB fetched ecall running sys222 prot_cases core50
    arg_addr addr_page addr_pos arg_len len_pos fits arg_prot arg_flags arg_fd arg_off n free_res
    inside_maps budget cont.
  eapply srz_sys_lazy; [exact running | exact fetched | exact ecall |].
  set (ms := epend regs pc mem rom (getr regs 17)).
  assert (is_mmap : bv_unsigned (getr regs 17) = 222%Z) by (rewrite sys222; reflexivity).
  pose proof (fun eff => mmap_fixedin_check ms (getr regs 17) model eff prot flags addr len is_mmap
                prot_cases core50 (eq_trans (ms_gpr_epend0 _ _ _ _ _) arg_addr) addr_page addr_pos
                (eq_trans (ms_gpr_epend1 _ _ _ _ _) arg_len) len_pos
                (eq_trans (ms_gpr_epend2 _ _ _ _ _) arg_prot) (eq_trans (ms_gpr_epend3 _ _ _ _ _) arg_flags)
                (eq_trans (ms_gpr_epend4 _ _ _ _ _) arg_fd) (eq_trans (ms_gpr_epend5 _ _ _ _ _) arg_off)
                fits free_res inside_maps budget) as facts.
  assert (ok_check : check_syscall (sys_input segs ms (getr regs 17)) (fixedin_ok_eff prot addr n) model
                     = CheckOk (fixedin_ok_model prot flags addr n model) [])
    by exact (proj1 (facts (fixedin_ok_eff prot addr n))).
  assert (ok_ret : eff_ret (fixedin_ok_eff prot addr n) = addr)
    by (unfold fixedin_ok_eff; destruct (Z.eqb prot 0); reflexivity).
  assert (ok_not_refusal : refusal_b (sys_input segs ms (getr regs 17)) model (eff_ret (fixedin_ok_eff prot addr n)) = false).
  { rewrite refusal_b_222 by exact is_mmap. rewrite ok_ret.
    exact (ret_in_errnos_ENOMEM_aligned addr addr_page). }
  assert (ok_halted : m_halted (fixedin_ok_model prot flags addr n model) = None).
  { unfold fixedin_ok_model. rewrite with_mmap_replacement_halted, with_vmmaps_halted. exact running. }
  eapply srz_silent1; [| exact cont].
  replace (mkst (regupd regs 10 addr) (v_addi pc 4) (if Z.eqb prot 0 then unfill addr n mem else zfill addr n mem) rom)
    with (advance_past_svc (apply_effect ms (fixedin_ok_eff prot addr n))).
  - apply (node_chk_noacc ms model (getr regs 17) unit (fun _ => fixedin_ok_eff prot addr n)
             (fun _ => fixedin_ok_model prot flags addr n model) running (epend_svc _ _ _ _ _)).
    + intros _. exact ok_check.
    + intros _. exact (spurious_refusal_not_refusal _ _ _ _ ok_not_refusal).
    + intros eff m' ev accepted fine.
      destruct (proj1 (proj2 (facts eff)) m' ev accepted)
        as [[refused same_halt] | [-> [-> ->]]]; [exfalso | exists tt; repeat split].
      rewrite running in same_halt.
      apply (fine same_halt).
      apply (refusal_spurious_of_grant ACFG _ model eff (fixedin_ok_eff prot addr n)
               (fixedin_ok_model prot flags addr n model) []).
      * unfold injected_family_off.
        change (in_sysno (sys_input segs ms (getr regs 17))) with (getr regs 17).
        rewrite is_mmap. reflexivity.
      * rewrite refusal_b_222 by exact is_mmap. rewrite <- errno_ret_in_eq. exact refused.
      * apply check_syscall_ok_iff. exact ok_check.
      * exact ok_not_refusal.
    + exact (fun eff => proj2 (proj2 (facts eff))).
    + intros _. exact ok_halted.
    + intros _. unfold fixedin_ok_eff. destruct (Z.eqb prot 0); reflexivity.
  - unfold ms, fixedin_ok_eff. destruct (Z.eqb prot 0).
    + apply adv_unmaps1_epend.
    + apply adv_zeros1_epend.
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

#[using="Type"] Lemma cs_ok_refuse : forall E cs R FULL model,
  cs_ok E cs R FULL model ->
  cs_ok E (refuse cs) (regupd R 10 (Z_to_bv 64 ENOMEM_RET)) FULL model.
Proof.
  intros E cs R FULL model HC.
  assert (HMr : Mr A argH E (refuse cs) model FULL = Mr A argH E cs model FULL) by reflexivity.
  assert (HA : allowA A E (refuse cs) = allowA A E cs) by reflexivity.
  destruct HC; constructor; unfold refuse, set_pc, set_reg, with_ss, mk_ss in *;
    cbn [a_ss a_maps a_totsz a_ylo a_eager a_vis a_ghost a_abytes a_brk a_fd a_tidset kn s_regs s_log s_know s_pc s_next] in *;
    try assumption; try reflexivity.
  apply regs_ok_set_n; [exact co_regs0 | lia | rewrite edenot_lit; reflexivity].
Qed.

#[using="Type"] Lemma pc_refuse : forall cs, pc (refuse cs) = pc cs + 4.
Proof. reflexivity. Qed.
#[using="Type"] Lemma nxt_refuse : forall cs, nxt (refuse cs) = nxt cs.
Proof. reflexivity. Qed.
End CsOk.
