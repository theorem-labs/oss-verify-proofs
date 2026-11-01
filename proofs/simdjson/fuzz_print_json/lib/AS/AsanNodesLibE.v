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
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.AS Require Import
  SimInv ExitSim PropExec CatExec CatSim SeqExec StreamExec MmapSim AllocSim FileSim
  ShapeAlg SpinAlg Nodes StoreOk AgentLib AgentNodes RefNodes
  AsanAcct AsanAcctShape AsanPlacement BackingAlgebra.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.AS Require Import AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.AS Require Import AsanCeil.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.
Import ListNotations.
Open Scope bv_scope.

Lemma errno_ret_in_nil : forall r, errno_ret_in [] r = false.
Proof. intros r. reflexivity. Qed.

Section Noacc.
Variable segs : list Segment.

Lemma sstep_of_check_noacc : forall ms model x8 eff m' evs,
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

Lemma node_chk_ev_noacc : forall ms model x8 (I : Type)
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
  intros ms model x8 I effs ms' evs live pend accepted genuine covered modeled
    live_after no_acc.
  apply node_of_iff.
  - intro k.
    apply (sstep_cfg_syscall segs ACFG ms model x8 (effs k) (ms' k) (ms' k) (evs k) live pend);
      [ apply check_syscall_ok_iff, accepted | apply genuine | apply live_after | ].
    rewrite no_acc. apply materialize_model_accesses_nil.
  - intros e st stp.
    pose proof (sstep_cfg_sys_inv segs ACFG ms model x8 e st pend stp) as shape.
    cbv zeta in shape.
    destruct shape as [(eff & m1 & e1 & spec1 & genuine1 & _ & mat1)
                      | [(eff & m1 & e1 & code & spec1 & stop1 & _ & _ & _)
                      | [(eff & m1 & e1 & sig & spec1 & kill1 & _ & _)
                      | (unm & _ & _)]]].
    + apply check_syscall_ok_iff in spec1.
      destruct (covered eff m1 e1 spec1 (fun _ => genuine1)) as (k & -> & -> & ->).
      rewrite no_acc, materialize_model_accesses_nil in mat1.
      destruct mat1 as [-> ->].
      exists k. split; reflexivity.
    + exfalso. apply check_syscall_ok_iff in spec1.
      assert (stopped : m_halted m1 <> None) by (rewrite stop1; discriminate).
      destruct (covered eff m1 e1 spec1 (fun up => False_ind _ (stopped up)))
        as (k & _ & m1_k & _).
      apply stopped. rewrite m1_k. apply live_after.
    + exfalso. apply check_syscall_ok_iff in spec1.
      assert (stopped : m_halted m1 <> None).
      { intro up. rewrite (m_killed_of_m_halted_none m1 up) in kill1. discriminate. }
      destruct (covered eff m1 e1 spec1 (fun up => False_ind _ (stopped up)))
        as (k & _ & m1_k & _).
      apply stopped. rewrite m1_k. apply live_after.
    + exfalso. apply (modeled (mkEffect (Z_to_bv 64 0) [] [])).
      apply check_syscall_complete_unmodeled. exact unm.
Qed.

Lemma node_chk_noacc : forall ms model x8 (I : Type) (effs : I -> SyscallEffect) (ms' : I -> Model),
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
  intros ms model x8 I effs ms'.
  exact (node_chk_ev_noacc ms model x8 I effs ms' (fun _ => [])).
Qed.

Lemma node_det_noacc : forall ms model x8 eff0 m0 evs0,
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
  intros ms model x8 eff0 m0 evs0 live pend exactly modeled live0 no_acc0.
  pose proof (proj2 (exactly eff0 m0 evs0) (conj eq_refl (conj eq_refl eq_refl))) as only0.
  assert (honest : ~ spurious_refusal_cfg ACFG (sys_input segs ms x8) model eff0).
  { intros (_ & refused0 & eff' & m' & evs' & spec' & granted').
    apply check_syscall_ok_iff, exactly in spec'.
    destruct spec' as (-> & _ & _).
    rewrite refused0 in granted'. discriminate. }
  apply (node_chk_ev_noacc ms model x8 unit (fun _ => eff0) (fun _ => m0) (fun _ => evs0));
    [ exact live | exact pend | intros _; exact only0 | intros _; exact honest
    | | exact modeled | intros _; exact live0 | intros _; exact no_acc0 ].
  intros eff m' evs found _.
  exists tt. apply exactly. exact found.
Qed.

Lemma rz_det_noacc : forall ms model x8 eff0 m0 T,
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

Lemma srz_det_noacc : forall ms model x8 eff0 m0 T,
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

Lemma with_vm_backing_halted : forall l p m, m_halted (with_vm_backing l p m) = m_halted m.
Proof. reflexivity. Qed.

Lemma vm_add_lazy_halted : forall a n m, m_halted (vm_add_lazy a n m) = m_halted m.
Proof. reflexivity. Qed.

Lemma with_mmap_backing_halted : forall flags a n m,
  m_halted (with_mmap_backing flags a n m) = m_halted m.
Proof. intros. unfold with_mmap_backing. destruct (mmap_noreserve_b flags); reflexivity. Qed.

Lemma with_mmap_replacement_halted : forall flags a n m,
  m_halted (with_mmap_replacement flags a n m) = m_halted m.
Proof.
  intros. unfold with_mmap_replacement. rewrite with_mmap_backing_halted.
  apply vm_forget_range_halted.
Qed.

Lemma with_mmap_destroyed_halted : forall a n h m,
  m_halted (with_mmap_destroyed a n h m) = m_halted m.
Proof. intros. unfold with_mmap_destroyed. rewrite vm_forget_range_halted. apply with_vmmaps_halted. Qed.



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
  intros ms model ms' live idle stepped.
  apply (node_instr_disjoint segs ms model ms' [] live idle stepped).
  intros a n lo sz nowhere. destruct nowhere.
Qed.

Lemma rz_sys_lazy : forall regs pc mem rom model w T,
  m_halted model = None ->
  fetch_word segs pc = Some w -> is_ecall w = true ->
  realizes segs (mkCfg (epend regs pc mem rom (getr regs 17)) model) T ->
  realizes segs (mkCfg (mkst regs pc mem rom) model) T.
Proof.
  intros regs pc mem rom model w T Hh HF HE Hc.
  eapply rz_silent1; [| exact Hc].
  apply node_instr_noacc; [exact Hh | reflexivity | eapply stepacc_ecall_epend; eassumption].
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

Lemma node_brk_lazy : forall ms model x8,
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
  intros ms model x8 live pend sysno.
  apply node_chk_noacc with (x8 := x8);
    [ exact live | exact pend | | | | | intros i; rewrite brk_model_halted; exact live
    | intros i; reflexivity ].
  - intros [r acfg_r]. apply check_syscall_ok_iff.
    exact (brk_ok_intro segs ms x8 model r sysno (proj1 acfg_r)).
  - intros [r acfg_r].
    apply (acfg_outcome_ok_nonspurious _ _ _ (brk_model (ms_gpr ms 0) r model) []).
    + apply (brk_acfg_iff segs ms x8 model _ _ _ live sysno).
      split; [reflexivity |]. split; [reflexivity |]. split; [exact acfg_r | reflexivity].
    + rewrite brk_model_halted. exact live.
  - intros eff m' evs found guard.
    apply check_syscall_ok_iff in found.
    destruct (proj1 (brk_acfg_iff segs ms x8 model eff m' evs live sysno) (conj found guard))
      as (shape & -> & acfg_r & ->).
    exists (exist _ (eff_ret eff) acfg_r). cbn [proj1_sig].
    split; [exact shape | split; reflexivity].
  - intros eff unm. apply check_syscall_sound_unmodeled in unm.
    exact (brk_no_unmodeled segs ms x8 model sysno unm).
Qed.

Lemma srz_brk_query_lazy : forall regs (pc : word) mem rom model w K,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None ->
  getr regs 17 = Z_to_bv 64 214 ->
  getr regs 10 = Z_to_bv 64 0 ->
  srealizes segs (mkCfg (mkst (regupd regs 10 (vm_brk (m_vmmaps model))) (v_addi pc 4) mem rom) model) K ->
  srealizes segs (mkCfg (mkst regs pc mem rom) model) K.
Proof.
  intros regs pc mem rom model w K fetched ecall live a7 a0 after.
  apply (srz_sys_lazy regs pc mem rom model w K live fetched ecall).
  pose (ms := epend regs pc mem rom (getr regs 17)).
  assert (sysno : bv_unsigned (getr regs 17) = 214%Z) by (rewrite a7; reflexivity).
  assert (req0 : ms_gpr ms 0 = Z_to_bv 64 0) by (unfold ms; rewrite ms_gpr_epend0; exact a0).
  assert (ok_cur : forall r,
            brk_resolution_ok model (ms_gpr ms 0) r <-> r = vm_brk (m_vmmaps model)).
  { intro r. unfold brk_resolution_ok, Mmap.brk_r_ok. rewrite req0. cbv zeta.
    change (w_is0 (Z_to_bv 64 0)) with true. cbn [orb]. apply bv_eqb_eq. }
  assert (acfg_cur : brk_res_acfg model (ms_gpr ms 0) (vm_brk (m_vmmaps model))).
  { split; [apply ok_cur; reflexivity |].
    intro refused. unfold brk_refusal_b in refused. rewrite req0 in refused. cbv zeta in refused.
    change (w_is0 (Z_to_bv 64 0)) with true in refused. cbn [negb andb] in refused.
    discriminate refused. }
  apply (srz_conseq segs _ (t_alt (fun _ : {r : word | brk_res_acfg model (ms_gpr ms 0) r} => K))).
  - apply (srz_cases _ _ _ (fun _ => K) (exist _ _ acfg_cur)
             (node_brk_lazy ms model (getr regs 17) live eq_refl sysno)).
    intros [r acfg_r]. cbn [proj1_sig].
    rewrite (proj1 (ok_cur r) (proj1 acfg_r)), req0.
    assert (calm : brk_unmaps (vm_brk (m_vmmaps model)) (vm_brk (m_vmmaps model)) = []).
    { unfold brk_unmaps, brk_page_range. cbv zeta. rewrite Z.ltb_irrefl.
      destruct (0 <? bv_unsigned (vm_brk (m_vmmaps model)))%Z; reflexivity. }
    rewrite calm, brk_model_keep.
    change (brk_zeros (Z_to_bv 64 0) (vm_brk (m_vmmaps model)) (vm_brk (m_vmmaps model)))
      with (@nil (word * word)).
    unfold ms. rewrite adv_ret_epend. exact after.
  - intro tr. split; [intros [_ in_k]; exact in_k | intro in_k; exists (exist _ _ acfg_cur); exact in_k].
Qed.

Lemma srz_brk_grow_lazy : forall regs (pc : word) mem rom model w (d : Z) KB,
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
  intros regs pc mem rom model w d KB fetched ecall live a7. cbv zeta.
  intros b_al d_al d_pos b_pos fits above_start a0 grows after.
  apply (srz_sys_lazy regs pc mem rom model w KB live fetched ecall).
  set (b := vm_brk (m_vmmaps model)) in *.
  set (top := Z_to_bv 64 (bv_unsigned b + d)) in *.
  pose (ms := epend regs pc mem rom (getr regs 17)).
  assert (sysno : bv_unsigned (getr regs 17) = 214%Z) by (rewrite a7; reflexivity).
  assert (req_top : ms_gpr ms 0 = top) by (unfold ms; rewrite ms_gpr_epend0; exact a0).
  pose proof (u64_range b) as b_range.
  assert (top_val : bv_unsigned top = (bv_unsigned b + d)%Z) by (unfold top; apply u64_lit; lia).
  assert (top_al : ((bv_unsigned b + d) mod page_size = 0)%Z).
  { rewrite Z.add_mod by (unfold page_size; lia). rewrite b_al, d_al. reflexivity. }
  assert (top_ne0 : top <> Z_to_bv 64 0).
  { intro zero. apply (f_equal bv_unsigned) in zero. rewrite top_val in zero.
    change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in zero. lia. }
  assert (top_ne_b : bv_eqb top b = false).
  { destruct (bv_eqb top b) eqn:same; [| reflexivity].
    apply bv_eqb_eq, (f_equal bv_unsigned) in same. rewrite top_val in same. lia. }
  assert (refuse_b : brk_refusal_b model top b = true).
  { unfold brk_refusal_b, min_brk, w_is0. cbv zeta. fold b. rewrite top_ne_b, bv_eqb_refl.
    destruct (bv_eqb top (Z_to_bv 64 0)) eqn:zero; [apply bv_eqb_eq in zero; contradiction |].
    rewrite (proj2 (Z.ltb_ge (bv_unsigned top) (bv_unsigned (vm_start_brk (m_vmmaps model)))))
      by (rewrite top_val; exact above_start).
    reflexivity. }
  assert (grant_top : brk_refusal_b model top top = false).
  { unfold brk_refusal_b. cbv zeta. fold b. rewrite top_ne_b. apply andb_false_r. }
  assert (ok_iff : forall r, brk_resolution_ok model top r <->
                             r = b \/ (r = top /\ Mmap.brk_grow_ok model top top = true)).
  { intro r. apply (brk_r_ok_grow_cases model top r); fold b; rewrite top_val; lia. }
  assert (only_top : forall r, brk_res_acfg model (ms_gpr ms 0) r -> r = top).
  { rewrite req_top. intros r [ok_r excl]. apply ok_iff in ok_r.
    destruct ok_r as [-> | [-> _]]; [exfalso | reflexivity].
    rewrite (excl refuse_b top (proj2 (ok_iff top) (or_intror (conj eq_refl grows)))) in grant_top.
    discriminate grant_top. }
  assert (acfg_top : brk_res_acfg model (ms_gpr ms 0) top).
  { rewrite req_top. split; [apply ok_iff; right; split; [reflexivity | exact grows] |].
    intro bad. rewrite grant_top in bad. discriminate bad. }
  apply (srz_conseq segs _ (t_alt (fun _ : {r : word | brk_res_acfg model (ms_gpr ms 0) r} => KB))).
  - apply (srz_cases _ _ _ (fun _ => KB) (exist _ _ acfg_top)
             (node_brk_lazy ms model (getr regs 17) live eq_refl sysno)).
    intros [r acfg_r]. cbn [proj1_sig].
    rewrite (only_top r acfg_r), req_top. fold b.
    assert (b_lt_top : (bv_unsigned b < bv_unsigned top)%Z) by (rewrite top_val; lia).
    rewrite (brk_zeros_aligned_grow top top b top_ne0 b_pos b_lt_top b_al), top_val,
      (page_round_up_Z_aligned (bv_unsigned b + d) ltac:(lia) top_al).
    replace (bv_unsigned b + d - bv_unsigned b)%Z with d by ring.
    assert (no_unmaps : brk_unmaps top b = []).
    { unfold brk_unmaps, brk_page_range. cbv zeta.
      rewrite top_val, (page_round_up_Z_aligned (bv_unsigned b + d) ltac:(lia) top_al),
        (page_round_up_Z_aligned (bv_unsigned b) ltac:(lia) b_al).
      rewrite (proj2 (Z.ltb_ge (bv_unsigned b + d) (bv_unsigned b))) by lia.
      destruct (0 <? bv_unsigned b)%Z; reflexivity. }
    rewrite no_unmaps.
    rewrite (brk_model_grow_eq model d d_pos b_pos fits b_al d_al : brk_model top top model = _).
    unfold ms. rewrite adv_zeros1_epend. exact after.
  - intro tr. split; [intros [_ in_kb]; exact in_kb | intro in_kb; exists (exist _ _ acfg_top); exact in_kb].
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
  intros regs pc mem rom model w req KA fetched ecall live a7. cbv zeta.
  intros a0 req_pos above_start above_brk blocked after.
  apply (srz_sys_lazy regs pc mem rom model w KA live fetched ecall).
  pose (ms := epend regs pc mem rom (getr regs 17)).
  assert (sysno : bv_unsigned (getr regs 17) = 214%Z) by (rewrite a7; reflexivity).
  assert (req_is : ms_gpr ms 0 = req) by (unfold ms; rewrite ms_gpr_epend0; exact a0).
  assert (stays : forall r, brk_resolution_ok model (ms_gpr ms 0) r -> r = vm_brk (m_vmmaps model)).
  { rewrite req_is. intros r ok_r.
    apply (brk_r_ok_grow_cases model req r req_pos above_start above_brk) in ok_r.
    destruct ok_r as [kept | [_ grew]]; [exact kept |].
    rewrite blocked in grew. discriminate grew. }
  assert (acfg_cur : brk_res_acfg model (ms_gpr ms 0) (vm_brk (m_vmmaps model))).
  { split.
    - rewrite req_is. apply (brk_r_ok_grow_cases model req _ req_pos above_start above_brk).
      left. reflexivity.
    - intros refused r' ok'. rewrite (stays r' ok'). exact refused. }
  apply (srz_conseq segs _ (t_alt (fun _ : {r : word | brk_res_acfg model (ms_gpr ms 0) r} => KA))).
  - apply (srz_cases _ _ _ (fun _ => KA) (exist _ _ acfg_cur)
             (node_brk_lazy ms model (getr regs 17) live eq_refl sysno)).
    intros [r acfg_r]. cbn [proj1_sig]. rewrite (stays r (proj1 acfg_r)).
    assert (no_zeros : brk_zeros (ms_gpr ms 0) (vm_brk (m_vmmaps model)) (vm_brk (m_vmmaps model)) = []).
    { unfold brk_zeros, brk_is_grow. rewrite Z.ltb_irrefl, andb_false_r. reflexivity. }
    assert (no_unmaps : brk_unmaps (vm_brk (m_vmmaps model)) (vm_brk (m_vmmaps model)) = []).
    { unfold brk_unmaps, brk_page_range. cbv zeta. rewrite Z.ltb_irrefl.
      destruct (0 <? bv_unsigned (vm_brk (m_vmmaps model)))%Z; reflexivity. }
    rewrite no_zeros, no_unmaps, brk_model_keep.
    unfold ms. rewrite adv_ret_epend. exact after.
  - intro tr. split; [intros [_ in_ka]; exact in_ka | intro in_ka; exists (exist _ _ acfg_cur); exact in_ka].
Qed.

Lemma node_set_tid_lazy : forall ms model x8,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 96%Z ->
  m_tid model = None ->
  node_ok segs (mkCfg ms model) tid_I (fun _ => [])
    (fun i => mkCfg (advance_past_svc (apply_effect ms (mkEffectU (proj1_sig i) [] [] [] [] [])))
                    (with_tid (proj1_sig i) model)).
Proof.
  intros ms model x8 live pend sysno no_tid.
  assert (via_tid : forall e, check_syscall (sys_input segs ms x8) e model = check_set_tid_address e model)
    by (intro e; apply check_syscall_96; exact sysno).
  assert (fresh_ok : forall t : tid_I,
            check_syscall (sys_input segs ms x8) (mkEffect (proj1_sig t) [] []) model
            = CheckOk (with_tid (proj1_sig t) model) []).
  { intros [t [lo hi]]. cbn [proj1_sig]. rewrite via_tid. unfold check_set_tid_address.
    rewrite no_tid. apply Z.ltb_lt in lo. apply Z.ltb_lt in hi. rewrite lo, hi. reflexivity. }
  apply node_chk_noacc with (x8 := x8);
    [ exact live | exact pend | exact fresh_ok | | | | intros t; rewrite with_tid_halted; exact live
    | intros t; reflexivity ].
  - intros t. apply (acfg_outcome_ok_nonspurious _ _ _ (with_tid (proj1_sig t) model) []).
    + apply (syscall_spec_acfg_no segs ms x8 96 model _ sysno eq_refl).
      apply check_syscall_ok_iff. exact (fresh_ok t).
    + rewrite with_tid_halted. exact live.
  - intros eff m' evs found _.
    rewrite via_tid in found. unfold check_set_tid_address in found.
    destruct eff as [ret ws zs us cs ci]. destruct ws, zs, us, cs, ci; try discriminate found.
    rewrite no_tid in found. cbv beta iota in found.
    destruct ((0 <? bv_unsigned ret) && (bv_unsigned ret <? PID_MAX_ENVELOPE))%Z eqn:bounds;
      [| discriminate found].
    injection found as <- <-.
    apply andb_prop in bounds. destruct bounds as [lo hi].
    apply Z.ltb_lt in lo. apply Z.ltb_lt in hi.
    exists (exist _ ret (conj lo hi)). split; [reflexivity | split; reflexivity].
  - intros eff unm. rewrite via_tid in unm. unfold check_set_tid_address in unm.
    destruct eff as [ret ws zs us cs ci]. destruct ws, zs, us, cs, ci; try discriminate unm.
    rewrite no_tid in unm. cbv beta iota in unm.
    destruct (_ && _); discriminate unm.
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

Lemma srz_alt3 : forall c (nx : three -> config) (A B C : TSet),
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

Lemma with_mmap_replacement_halted' : forall flags a n m,
  m_halted (with_mmap_replacement flags a n m) = m_halted m.
Proof.
  intros. unfold with_mmap_replacement, with_mmap_backing, vm_forget_range.
  destruct (mmap_noreserve_b flags); reflexivity.
Qed.
Lemma with_mmap_destroyed_halted' : forall a n h m,
  m_halted (with_mmap_destroyed a n h m) = m_halted m.
Proof. intros. reflexivity. Qed.

Lemma atop_room : forall h, alloc_top h + 8388608 < 2 ^ 64.
Proof. intros h. pose proof (alloc_top_room h) as R. unfold stack_max_size, two_pow_64 in R. lia. Qed.

Lemma mmap_fixedin_check : forall ms x8 model eff (prot : Z) (flags addr : word) (len : Z),
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
  intros ms x8 model eff prot flags addr len sysno prot_cases core arg0 a_al a_pos arg1 len_pos
    arg2 arg3 arg4 arg5 fits n free_res inside budget.
  pose proof (u64_range (vm_init_sp (m_vmmaps model))) as sp_range.
  pose proof (page_round_up_Z_bounds len ltac:(lia)) as len_round.
  assert (room : (bv_unsigned addr + page_round_up_Z len < two_pow_64)%Z).
  { unfold alloc_top, stack_max_size in fits. unfold two_pow_64. lia. }
  assert (len_val : bv_unsigned (Z_to_bv 64 len) = len).
  { apply u64_lit. pose proof (u64_range addr). unfold two_pow_64 in room. lia. }
  assert (as_mmap : forall e, check_syscall (sys_input segs ms x8) e model
            = check_mmap addr (Z_to_bv 64 len) (Z_to_bv 64 prot) flags (Z_to_bv 64 (-1))
                (Z_to_bv 64 0) e model).
  { intro e. rewrite mmap_check by exact sysno. rewrite arg0, arg1, arg2, arg3, arg4, arg5.
    reflexivity. }
  assert (off_ok : mmap_off_aligned_b (Z_to_bv 64 0) = true) by reflexivity.
  assert (anon : mmap_anon_b flags = true) by (apply (mmap_anon_b_of_core flags 50 core); reflexivity).
  assert (len_nz : w_is0 (Z_to_bv 64 len) = false).
  { unfold w_is0. destruct (bv_eqb (Z_to_bv 64 len) (Z_to_bv 64 0)) eqn:zero; [| reflexivity].
    apply bv_eqb_eq, (f_equal bv_unsigned) in zero. rewrite len_val in zero.
    change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in zero. lia. }
  assert (no_wrap : (two_pow_64 <=? bv_unsigned addr + page_round_up_Z len)%Z = false)
    by (apply Z.leb_gt; exact room).
  assert (under_top : (bv_unsigned addr + page_round_up_Z len <=? alloc_top (m_vmmaps model))%Z = true)
    by (apply Z.leb_le; exact fits).
  assert (al_b : (bv_unsigned addr mod page_size =? 0)%Z = true) by (apply Z.eqb_eq; exact a_al).
  assert (pos_b : (0 <? bv_unsigned addr)%Z = true) by (apply Z.ltb_lt; exact a_pos).
  assert (not_err : errno_ret_in mmap_errnos addr = false).
  { unfold errno_ret_in, mmap_errnos. cbn [existsb]. rewrite (page_aligned_not_ENOMEM addr a_al).
    reflexivity. }
  rewrite !as_mmap.
  destruct prot_cases as [-> | ->].
  - destruct (mmap_gates_core50 flags (Z_to_bv 64 0) core) as (no_plain & no_na & fixed_na & _ & _).
    unfold check_mmap. cbv beta.
    rewrite off_ok, anon, len_nz, no_plain, no_na, fixed_na. cbn [negb].
    rewrite len_val, no_wrap, under_top, al_b, pos_b. cbn [negb].
    change (Z_to_bv 64 (page_round_up_Z len)) with n.
    rewrite free_res, inside. cbn [andb].
    change (fixedin_ok_eff 0 addr n) with (mkEffectU addr [] [] [(addr, n)] [] []).
    split; [| split].
    + cbv beta iota. rewrite not_err, bv_eqb_refl, (proj2 (listNN_eqb_eq _ _) eq_refl).
      reflexivity.
    + intros m' ev found.
      destruct eff as [r ws zs us cs ci]. destruct ws, zs, cs, ci; try discriminate found.
      cbv beta iota in found. cbn [eff_ret].
      destruct (errno_ret_in mmap_errnos r) eqn:refusal.
      * left. split; [reflexivity |].
        destruct us as [| u rest]; [injection found as <- _; reflexivity |].
        destruct (listNN_eqb (u :: rest) [(addr, n)]); [| discriminate found].
        injection found as <- _. apply with_mmap_destroyed_halted.
      * right.
        destruct (bv_eqb r addr) eqn:r_addr; [| discriminate found].
        destruct (listNN_eqb us [(addr, n)]) eqn:us_one; [| discriminate found].
        apply bv_eqb_eq in r_addr. apply listNN_eqb_eq in us_one. subst r us.
        cbn [andb] in found. injection found as <- <-.
        split; [reflexivity | split; reflexivity].
    + intro unm.
      destruct eff as [r ws zs us cs ci]. destruct ws, zs, cs, ci; try discriminate unm.
      cbv beta iota in unm.
      destruct (errno_ret_in mmap_errnos r).
      * destruct us as [| u rest]; [discriminate unm |].
        destruct (listNN_eqb (u :: rest) [(addr, n)]); discriminate unm.
      * destruct (bv_eqb r addr && listNN_eqb us [(addr, n)]); discriminate unm.
  - destruct (mmap_gates_core50 flags (Z_to_bv 64 3) core)
      as (no_plain & no_na & _ & not_fixed_na & fixed_rw).
    pose proof (budget eq_refl) as afford.
    unfold check_mmap. cbv beta.
    rewrite off_ok, anon, len_nz, no_plain, no_na, not_fixed_na, fixed_rw. cbn [negb].
    rewrite len_val, no_wrap, under_top, al_b, pos_b. cbn [negb].
    change (Z_to_bv 64 (page_round_up_Z len)) with n.
    rewrite free_res, inside. cbn [andb].
    change (fixedin_ok_eff 3 addr n) with (mkEffectU addr [] [(addr, n)] [] [] []).
    split; [| split].
    + cbv beta iota.
      rewrite not_err, bv_eqb_refl, (proj2 (listNN_eqb_eq _ _) eq_refl), afford.
      reflexivity.
    + intros m' ev found.
      destruct eff as [r ws zs us cs ci]. destruct ws, cs, ci; try discriminate found.
      cbv beta iota in found. cbn [eff_ret].
      destruct (errno_ret_in mmap_errnos r) eqn:refusal.
      * left. split; [reflexivity |].
        destruct zs; [| discriminate found].
        destruct us as [| u rest]; [injection found as <- _; reflexivity |].
        destruct (listNN_eqb (u :: rest) [(addr, n)]); [| discriminate found].
        injection found as <- _. apply with_mmap_destroyed_halted.
      * right. destruct us; [| discriminate found].
        destruct (bv_eqb r addr) eqn:r_addr; [| discriminate found].
        destruct (listNN_eqb zs [(addr, n)]) eqn:zs_one; [| discriminate found].
        rewrite afford in found. cbn [andb] in found.
        apply bv_eqb_eq in r_addr. apply listNN_eqb_eq in zs_one. subst r zs.
        injection found as <- <-.
        split; [reflexivity | split; reflexivity].
    + intro unm.
      destruct eff as [r ws zs us cs ci]. destruct ws, cs, ci; try discriminate unm.
      cbv beta iota in unm.
      destruct (errno_ret_in mmap_errnos r).
      * destruct zs; [| discriminate unm].
        destruct us as [| u rest]; [discriminate unm |].
        destruct (listNN_eqb (u :: rest) [(addr, n)]); discriminate unm.
      * destruct us; [| discriminate unm].
        destruct (bv_eqb r addr && listNN_eqb zs [(addr, n)] && mmap_fixed_rw_budget_ok flags model addr n);
          discriminate unm.
Qed.

Lemma srz_mmap_fixedin_lazy : forall regs (pc : word) mem rom model w (prot : Z) (flags addr : word) (len : Z) KB,
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
  intros regs pc mem rom model w prot flags addr len KB fetched ecall live a7 prot_cases core
    a0 a_al a_pos a1 len_pos fits a2 a3 a4 a5 n free_res inside budget after.
  apply (srz_sys_lazy regs pc mem rom model w KB live fetched ecall).
  pose (ms := epend regs pc mem rom (getr regs 17)).
  assert (sysno : bv_unsigned (getr regs 17) = 222%Z) by (rewrite a7; reflexivity).
  pose proof (fun eff => mmap_fixedin_check ms (getr regs 17) model eff prot flags addr len sysno
                prot_cases core (eq_trans (ms_gpr_epend0 _ _ _ _ _) a0) a_al a_pos
                (eq_trans (ms_gpr_epend1 _ _ _ _ _) a1) len_pos
                (eq_trans (ms_gpr_epend2 _ _ _ _ _) a2) (eq_trans (ms_gpr_epend3 _ _ _ _ _) a3)
                (eq_trans (ms_gpr_epend4 _ _ _ _ _) a4) (eq_trans (ms_gpr_epend5 _ _ _ _ _) a5)
                fits free_res inside budget) as verdict.
  set (good := fixedin_ok_eff prot addr n) in *.
  set (grown := fixedin_ok_model prot flags addr n model) in *.
  destruct (verdict good) as (accepted & _ & _).
  assert (good_ret : eff_ret good = addr)
    by (unfold good, fixedin_ok_eff; destruct (Z.eqb prot 0); reflexivity).
  assert (addr_ok : ret_in_errnos mmap_errnos addr = false).
  { rewrite <- errno_ret_in_eq. unfold errno_ret_in, mmap_errnos. cbn [existsb].
    rewrite (page_aligned_not_ENOMEM addr a_al). reflexivity. }
  assert (refusal_iff : forall r,
            refusal_b (sys_input segs ms (getr regs 17)) model r = ret_in_errnos mmap_errnos r)
    by (intro r; apply refusal_b_222; exact sysno).
  apply (srz_silent1 segs _ (mkCfg (advance_past_svc (apply_effect ms good)) grown)).
  - apply (node_chk_noacc ms model (getr regs 17) unit (fun _ => good) (fun _ => grown) live eq_refl).
    + intros _. exact accepted.
    + intros _ (_ & refused & _). rewrite refusal_iff, good_ret, addr_ok in refused.
      discriminate refused.
    + intros eff m' evs found guard.
      destruct (proj1 (proj2 (verdict eff)) m' evs found) as [(err & same_halt) | (-> & -> & ->)].
      * exfalso. refine (guard _ _); [rewrite same_halt; exact live |].
        unfold spurious_refusal_cfg. split; [| split].
        -- unfold injected_family_off.
           change (in_sysno (sys_input segs ms (getr regs 17))) with (getr regs 17).
           rewrite sysno. reflexivity.
        -- rewrite refusal_iff, <- errno_ret_in_eq. exact err.
        -- exists good, grown, []. split; [apply check_syscall_ok_iff; exact accepted |].
           rewrite refusal_iff, good_ret. exact addr_ok.
      * exists tt. split; [reflexivity | split; reflexivity].
    + intro eff. exact (proj2 (proj2 (verdict eff))).
    + intros _. unfold grown, fixedin_ok_model.
      rewrite with_mmap_replacement_halted, with_vmmaps_halted. exact live.
    + intros _. unfold good, fixedin_ok_eff. destruct (Z.eqb prot 0); reflexivity.
  - unfold ms, good, grown. destruct prot_cases as [-> | ->].
    + change (fixedin_ok_eff 0 addr n) with (mkEffectU addr [] [] [(addr, n)] [] []).
      rewrite adv_unmaps1_epend. exact after.
    + change (fixedin_ok_eff 3 addr n) with (mkEffect addr [] [(addr, n)]).
      rewrite adv_zeros1_epend. exact after.
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
#[local] Notation cs_ok := (APS.cs_ok SEGS A nx0 LIMIT SINV argH FS0).

Lemma cs_ok_refuse : forall E cs R FULL model,
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

Lemma pc_refuse : forall cs, pc (refuse cs) = pc cs + 4.
Proof. reflexivity. Qed.
Lemma nxt_refuse : forall cs, nxt (refuse cs) = nxt cs.
Proof. reflexivity. Qed.
End CsOk.
