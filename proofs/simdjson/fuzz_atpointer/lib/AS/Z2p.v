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
From OssFuzzTheorems.Proofs.simdjson.fuzz_atpointer.lib.AS Require Import
  SimInv Z8t Zg2 Z7g CatSim Zp6 Z10w Zfa Z16 Zb7
  Zp7 Z10a Nodes Z10r Z14 Z15 Zp2
  Z1b Z1e Z2x Z7c.
From OssFuzzTheorems.Proofs.simdjson.fuzz_atpointer.lib.AS Require Import Z78 Z7a Z7b Z2z Z2y Z33.
From OssFuzzTheorems.Proofs.simdjson.fuzz_atpointer.lib.AS Require Import Z1f.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Instance asanreflect_fx : Zg2.FPState := Zg2.fx0.
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
  intros ms model x8 I effs ms' evs live_in pend accepts genuine covers modeled live_out silent.
  assert (lands : forall i, materialize_model_accesses (ms' i) (syscall_effect_accesses (effs i)) = Some (ms' i)).
  { intros i. rewrite (silent i). apply materialize_model_accesses_nil. }
  assert (pick : forall eff m' ev,
            syscall_spec (sys_input segs ms x8) model (Ok eff m' ev) ->
            (m_halted m' = None -> ~ spurious_refusal_cfg ACFG (sys_input segs ms x8) model eff) ->
            exists i, eff = effs i /\ m' = ms' i /\ ev = evs i).
  { intros eff m' ev spec keep. exact (covers eff m' ev (check_syscall_complete_ok _ _ _ _ _ spec) keep). }
  assert (stopped : forall eff m' ev,
            syscall_spec (sys_input segs ms x8) model (Ok eff m' ev) -> m_halted m' <> None -> False).
  { intros eff m' ev spec halts.
    destruct (pick eff m' ev spec (fun up => False_ind _ (halts up))) as (i & _ & -> & _).
    exact (halts (live_out i)). }
  split.
  { intros i.
    refine (sstep_cfg_syscall segs ACFG ms model x8 (effs i) (ms' i) (ms' i) (evs i) live_in pend _ (genuine i) (live_out i) (lands i)).
    apply check_syscall_sound_ok. exact (accepts i). }
  intros e st step.
  remember (mkCfg ms model) as here eqn:at_here.
  destruct step as [ m1 d1 m2 d2 up1 idle1 acct1
                   | m1 d1 up1 idle1 acct1
                   | m1 d1 up1 idle1 acct1
                   | m1 d1 y1 f1 d2 d3 v1 up1 pend1 spec1 genuine1 up2 mat1
                   | m1 d1 y1 f1 d2 v1 up1 pend1 spec1 genuine1 up2 mat1
                   | m1 d1 y1 f1 d2 v1 code1 up1 pend1 spec1 halt1 nokill1
                   | m1 d1 y1 f1 d2 v1 sig1 up1 pend1 spec1 kill1
                   | m1 d1 y1 up1 pend1 unm1 ];
    injection at_here as -> ->; try congruence.
  - rewrite pend in pend1. injection pend1 as <-.
    destruct (pick f1 d2 v1 spec1 (fun _ => genuine1)) as (i & -> & -> & ->).
    rewrite (lands i) in mat1. injection mat1 as <-.
    exists i. split; reflexivity.
  - rewrite pend in pend1. injection pend1 as <-.
    destruct (pick f1 d2 v1 spec1 (fun _ => genuine1)) as (i & -> & -> & _).
    rewrite (lands i) in mat1. discriminate mat1.
  - rewrite pend in pend1. injection pend1 as <-.
    destruct (stopped f1 d2 v1 spec1 ltac:(congruence)).
  - rewrite pend in pend1. injection pend1 as <-.
    destruct (stopped f1 d2 v1 spec1).
    intro up. rewrite (m_killed_of_m_halted_none d2 up) in kill1. discriminate kill1.
  - rewrite pend in pend1. injection pend1 as <-.
    exfalso. exact (modeled (mkEffectU (Z_to_bv 64 0) [] [] [] [] [])
                            (check_syscall_complete_unmodeled _ _ _ unm1)).
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
  intros ms model x8 I effs ms' live_in pend accepts genuine covers modeled live_out silent.
  exact (node_chk_ev_noacc ms model x8 I effs ms' (fun _ => [])
           live_in pend accepts genuine covers modeled live_out silent).
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
  intros ms model x8 eff0 m0 evs0 live_in pend exact_iff modeled live0 silent0.
  apply (node_chk_ev_noacc ms model x8 unit (fun _ => eff0) (fun _ => m0) (fun _ => evs0) live_in pend);
    [ intros _; apply exact_iff; split; [|split]; reflexivity
    | intros _ (_ & refused & alt & m_alt & ev_alt & spec_alt & fresh)
    | intros eff m' ev accepted _; exists tt; exact (proj1 (exact_iff eff m' ev) accepted)
    | exact modeled
    | intros _; exact live0
    | intros _; exact silent0 ].
  apply check_syscall_complete_ok in spec_alt.
  destruct (proj1 (exact_iff alt m_alt ev_alt) spec_alt) as (same & _ & _).
  rewrite same, refused in fresh. discriminate fresh.
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
  intros ms model ms' live idle fetched.
  assert (acct : mi_account_step segs ms model = MachineOk (ms', model)).
  { unfold mi_account_step. cbv zeta. rewrite fetched. cbn [accessed_ranges access_value].
    rewrite materialize_model_accesses_nil. reflexivity. }
  split.
  - intros _. exact (sstep_cfg_instr segs ACFG ms model ms' model live idle acct).
  - intros e st step.
    remember (mkCfg ms model) as here eqn:at_here.
    destruct step as [ m1 d1 m2 d2 up1 idle1 acct1 | m1 d1 up1 idle1 acct1 | m1 d1 up1 idle1 acct1
                     | m1 d1 y1 | m1 d1 y1 | m1 d1 y1 | m1 d1 y1 | m1 d1 y1 ];
      injection at_here as -> ->; try congruence.
    rewrite acct in acct1. injection acct1 as <- <-.
    exists tt. split; reflexivity.
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
  intros ms model x8 live pend sys214.
  assert (granted : forall r, brk_res_acfg model (ms_gpr ms 0) r ->
            syscall_spec_acfg (sys_input segs ms x8) model
              (Ok (mkEffectU r [] (brk_zeros (ms_gpr ms 0) r (vm_brk (m_vmmaps model)))
                     (brk_unmaps r (vm_brk (m_vmmaps model))) [] [])
                  (brk_model (ms_gpr ms 0) r model) [])).
  { intros r adm. apply (brk_acfg_iff segs ms x8 model _ _ _ live sys214).
    split; [reflexivity | split; [reflexivity | split; [exact adm | reflexivity]]]. }
  refine (node_chk_noacc ms model x8 _
            (fun i => mkEffectU (proj1_sig i) []
                        (brk_zeros (ms_gpr ms 0) (proj1_sig i) (vm_brk (m_vmmaps model)))
                        (brk_unmaps (proj1_sig i) (vm_brk (m_vmmaps model))) [] [])
            (fun i => brk_model (ms_gpr ms 0) (proj1_sig i) model)
            live pend _ _ _ _ _ _).
  - intros [r adm]. apply check_syscall_complete_ok. exact (proj1 (granted r adm)).
  - intros [r adm]. exact (proj2 (granted r adm) (eq_trans (brk_model_halted _ _ _) live)).
  - intros eff m' evs accepted keep.
    destruct (proj1 (brk_acfg_iff segs ms x8 model eff m' evs live sys214)
                    (conj (check_syscall_sound_ok _ _ _ _ _ accepted) keep)) as (shape & noevs & adm & next).
    exists (exist _ (eff_ret eff) adm). split; [exact shape | split; [exact next | exact noevs]].
  - intros eff unm.
    exact (brk_no_unmodeled segs ms x8 model sys214 (check_syscall_sound_unmodeled _ _ _ unm)).
  - intros i. rewrite brk_model_halted. exact live.
  - intros i. reflexivity.
Qed.

Lemma srz_brk_query_lazy : forall regs (pc : word) mem rom model w K,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None ->
  getr regs 17 = Z_to_bv 64 214 ->
  getr regs 10 = Z_to_bv 64 0 ->
  srealizes segs (mkCfg (mkst (regupd regs 10 (vm_brk (m_vmmaps model))) (v_addi pc 4) mem rom) model) K ->
  srealizes segs (mkCfg (mkst regs pc mem rom) model) K.
Proof.
  intros regs pc mem rom model w K fetch ecall live a7 a0 after.
  refine (srz_sys_lazy regs pc mem rom model w K live fetch ecall _).
  assert (sys214 : bv_unsigned (getr regs 17) = 214%Z) by (rewrite a7; apply u64_lit; lia).
  assert (req0 : ms_gpr (epend regs pc mem rom (getr regs 17)) 0 = Z_to_bv 64 0)
    by (rewrite ms_gpr_epend0; exact a0).
  assert (forced : forall r, brk_resolution_ok model (Z_to_bv 64 0) r <-> r = vm_brk (m_vmmaps model)).
  { intros r. unfold brk_resolution_ok, Mmap.brk_r_ok. cbv zeta.
    change (w_is0 (Z_to_bv 64 0)) with true. cbn [orb]. apply bv_eqb_eq. }
  apply (srz_det_noacc _ model (getr regs 17) (mkEffectU (vm_brk (m_vmmaps model)) [] [] [] [] []) model);
    [exact live | reflexivity | | | exact live | reflexivity |].
  - intros eff m' evs. split.
    + intros accepted. apply check_syscall_sound_ok in accepted.
      apply (brk_ok_iff segs _ _ model eff m' evs sys214) in accepted as (shape & -> & res & ->).
      rewrite req0 in shape, res |- *. apply forced in res.
      rewrite res, brk_zeros_keep, brk_unmaps_keep in shape. rewrite res, brk_model_keep.
      split; [exact shape | split; reflexivity].
    + intros (-> & -> & ->). apply check_syscall_complete_ok.
      pose proof (brk_ok_intro segs (epend regs pc mem rom (getr regs 17)) (getr regs 17) model
                    (vm_brk (m_vmmaps model)) sys214) as grant.
      rewrite req0, brk_zeros_keep, brk_unmaps_keep, brk_model_keep in grant.
      apply grant. apply forced. reflexivity.
  - intros eff unm.
    exact (brk_no_unmodeled segs _ _ model sys214 (check_syscall_sound_unmodeled _ _ _ unm)).
  - rewrite adv_ret_epend. exact after.
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
  intros regs pc mem rom model w d KB fetch ecall live a7 h b b_al d_al d_pos b_pos fits above a0 can_grow after.
  subst b; subst h.
  refine (srz_sys_lazy regs pc mem rom model w KB live fetch ecall _).
  assert (sys214 : bv_unsigned (getr regs 17) = 214%Z) by (rewrite a7; apply u64_lit; lia).
  pose proof (u64_range (vm_brk (m_vmmaps model))) as old_rng.
  assert (top_u : bv_unsigned (Z_to_bv 64 (bv_unsigned (vm_brk (m_vmmaps model)) + d))
                  = (bv_unsigned (vm_brk (m_vmmaps model)) + d)%Z) by (apply u64_lit; lia).
  assert (top_ne0 : Z_to_bv 64 (bv_unsigned (vm_brk (m_vmmaps model)) + d) <> Z_to_bv 64 0).
  { intros zero. apply (f_equal bv_unsigned) in zero. rewrite top_u in zero.
    change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in zero. lia. }
  assert (top_old : Z_to_bv 64 (bv_unsigned (vm_brk (m_vmmaps model)) + d) <> vm_brk (m_vmmaps model)).
  { intros same. apply (f_equal bv_unsigned) in same. rewrite top_u in same. lia. }
  assert (grow_res : forall r,
            brk_resolution_ok model (Z_to_bv 64 (bv_unsigned (vm_brk (m_vmmaps model)) + d)) r <->
            r = vm_brk (m_vmmaps model) \/ r = Z_to_bv 64 (bv_unsigned (vm_brk (m_vmmaps model)) + d)).
  { intros r.
    pose proof (brk_r_ok_grow_cases model (Z_to_bv 64 (bv_unsigned (vm_brk (m_vmmaps model)) + d)) r
                  ltac:(rewrite top_u; lia) ltac:(rewrite top_u; exact above) ltac:(rewrite top_u; lia))
      as cases.
    rewrite can_grow in cases. split.
    - intros res. destruct (proj1 cases res) as [at_old | [at_top _]]; [left | right]; assumption.
    - intros [at_old | at_top]; apply cases; [left | right]; [exact at_old | split; [exact at_top | reflexivity]]. }
  assert (refused_old : brk_refusal_b model (Z_to_bv 64 (bv_unsigned (vm_brk (m_vmmaps model)) + d))
                          (vm_brk (m_vmmaps model)) = true).
  { unfold brk_refusal_b, w_is0, min_brk. cbv zeta.
    rewrite (bv_eqb_neq _ _ top_ne0), (bv_eqb_neq _ _ top_old), bv_eqb_refl.
    rewrite (proj2 (Z.ltb_ge _ _)) by (rewrite top_u; exact above). reflexivity. }
  assert (fresh_top : brk_refusal_b model (Z_to_bv 64 (bv_unsigned (vm_brk (m_vmmaps model)) + d))
                        (Z_to_bv 64 (bv_unsigned (vm_brk (m_vmmaps model)) + d)) = false).
  { unfold brk_refusal_b. cbv zeta. rewrite (bv_eqb_neq _ _ top_old). apply andb_false_r. }
  assert (req_at : ms_gpr (epend regs pc mem rom (getr regs 17)) 0
                   = Z_to_bv 64 (bv_unsigned (vm_brk (m_vmmaps model)) + d))
    by (rewrite ms_gpr_epend0; exact a0).
  assert (fam : injected_family_off ACFG (sys_input segs (epend regs pc mem rom (getr regs 17)) (getr regs 17)) = true).
  { unfold injected_family_off. rewrite in_sysno_sys_input, sys214. vm_compute. reflexivity. }
  assert (spec_top : syscall_spec (sys_input segs (epend regs pc mem rom (getr regs 17)) (getr regs 17)) model
            (Ok (mkEffectU (Z_to_bv 64 (bv_unsigned (vm_brk (m_vmmaps model)) + d)) []
                   (brk_zeros (ms_gpr (epend regs pc mem rom (getr regs 17)) 0)
                      (Z_to_bv 64 (bv_unsigned (vm_brk (m_vmmaps model)) + d)) (vm_brk (m_vmmaps model)))
                   (brk_unmaps (Z_to_bv 64 (bv_unsigned (vm_brk (m_vmmaps model)) + d)) (vm_brk (m_vmmaps model)))
                   [] [])
                (brk_model (ms_gpr (epend regs pc mem rom (getr regs 17)) 0)
                   (Z_to_bv 64 (bv_unsigned (vm_brk (m_vmmaps model)) + d)) model) [])).
  { apply brk_ok_intro; [exact sys214 |]. rewrite req_at. apply grow_res. right. reflexivity. }
  assert (lone : forall r, brk_res_acfg model (ms_gpr (epend regs pc mem rom (getr regs 17)) 0) r ->
                 r = Z_to_bv 64 (bv_unsigned (vm_brk (m_vmmaps model)) + d)).
  { intros r adm.
    destruct (proj2 (brk_acfg_iff segs (epend regs pc mem rom (getr regs 17)) (getr regs 17) model
                       (mkEffectU r [] (brk_zeros (ms_gpr (epend regs pc mem rom (getr regs 17)) 0) r
                                         (vm_brk (m_vmmaps model)))
                                  (brk_unmaps r (vm_brk (m_vmmaps model))) [] [])
                       (brk_model (ms_gpr (epend regs pc mem rom (getr regs 17)) 0) r model) [] live sys214)
                    (conj eq_refl (conj eq_refl (conj adm eq_refl)))) as [spec_r keep_r].
    apply (brk_ok_iff segs _ _ model _ _ _ sys214) in spec_r as (_ & _ & res & _).
    cbn [eff_ret] in res. rewrite req_at in res.
    apply grow_res in res as [at_old | at_top]; [| exact at_top].
    exfalso. subst r.
    apply (spec_step_ok_refuted _ model _ _ [] _ _ _ fam spec_top) in keep_r; [exact keep_r | | | ].
    - cbn [eff_ret]. rewrite (refusal_b_brk segs _ _ model _ sys214), req_at. exact fresh_top.
    - cbn [eff_ret]. rewrite (refusal_b_brk segs _ _ model _ sys214), req_at. exact refused_old.
    - rewrite brk_model_halted. exact live. }
  assert (adm_at : brk_res_acfg model (ms_gpr (epend regs pc mem rom (getr regs 17)) 0)
                     (Z_to_bv 64 (bv_unsigned (vm_brk (m_vmmaps model)) + d))).
  { refine (proj1 (proj2 (proj2 (proj1 (brk_acfg_iff segs (epend regs pc mem rom (getr regs 17)) (getr regs 17)
                                           model _ _ _ live sys214) (conj spec_top _))))).
    intros _ (_ & refused & _). cbn [eff_ret] in refused.
    rewrite (refusal_b_brk segs _ _ model _ sys214), req_at, fresh_top in refused. discriminate refused. }
  assert (collapse : forall (I : Type) (nx : I -> config) (c c' : config),
            I -> node_ok segs c I (fun _ => []) nx -> (forall i, nx i = c') ->
            node_ok segs c unit (fun _ => []) (fun _ => c')).
  { intros I nx c c' i0 [reach cover] same. split.
    - intros _. rewrite <- (same i0). exact (reach i0).
    - intros e st step. destruct (cover e st step) as (i & -> & ->).
      exists tt. rewrite (same i). split; reflexivity. }
  eapply srz_silent1; [| exact after].
  refine (collapse _ _ _ _ (exist _ _ adm_at)
            (node_brk_lazy (epend regs pc mem rom (getr regs 17)) model (getr regs 17) live eq_refl sys214) _).
  intros [r adm]. cbn [proj1_sig].
  rewrite (lone r adm), req_at.
  assert (top_al : ((bv_unsigned (vm_brk (m_vmmaps model)) + d) mod page_size = 0)%Z).
  { rewrite Z.add_mod, b_al, d_al by (unfold page_size; lia). reflexivity. }
  rewrite (brk_zeros_aligned_grow _ (Z_to_bv 64 (bv_unsigned (vm_brk (m_vmmaps model)) + d)) _
             top_ne0 b_pos ltac:(rewrite top_u; lia) b_al).
  rewrite (brk_unmaps_grow (Z_to_bv 64 (bv_unsigned (vm_brk (m_vmmaps model)) + d)) (vm_brk (m_vmmaps model))
             ltac:(rewrite top_u; lia)).
  rewrite (brk_model_grow_eq model d d_pos b_pos fits b_al d_al).
  rewrite top_u, (page_round_up_Z_aligned (bv_unsigned (vm_brk (m_vmmaps model)) + d) ltac:(lia) top_al).
  replace (bv_unsigned (vm_brk (m_vmmaps model)) + d - bv_unsigned (vm_brk (m_vmmaps model)))%Z with d by lia.
  rewrite adv_zeros1_epend. reflexivity.
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
  intros regs pc mem rom model w req KA fetch ecall live a7 h b a0 req_pos start_le old_le stuck after.
  refine (srz_sys_lazy regs pc mem rom model w KA live fetch ecall _).
  assert (sys214 : bv_unsigned (getr regs 17) = 214%Z) by (rewrite a7; apply u64_lit; lia).
  assert (req_at : ms_gpr (epend regs pc mem rom (getr regs 17)) 0 = req)
    by (rewrite ms_gpr_epend0; exact a0).
  assert (forced : forall r, brk_resolution_ok model req r <-> r = vm_brk (m_vmmaps model)).
  { intros r. pose proof (brk_r_ok_grow_cases model req r req_pos start_le old_le) as cases.
    rewrite stuck in cases. split.
    - intros res. destruct (proj1 cases res) as [same | [_ wrong]]; [exact same | discriminate wrong].
    - intros same. apply cases. left. exact same. }
  subst b; subst h.
  apply (srz_det_noacc _ model (getr regs 17) (mkEffectU (vm_brk (m_vmmaps model)) [] [] [] [] []) model);
    [exact live | reflexivity | | | exact live | reflexivity |].
  - intros eff m' evs. split.
    + intros accepted. apply check_syscall_sound_ok in accepted.
      apply (brk_ok_iff segs _ _ model eff m' evs sys214) in accepted as (shape & -> & res & ->).
      rewrite req_at in shape, res |- *. apply forced in res.
      rewrite res, brk_zeros_keep, brk_unmaps_keep in shape. rewrite res, brk_model_keep.
      split; [exact shape | split; reflexivity].
    + intros (-> & -> & ->). apply check_syscall_complete_ok.
      pose proof (brk_ok_intro segs (epend regs pc mem rom (getr regs 17)) (getr regs 17) model
                    (vm_brk (m_vmmaps model)) sys214) as grant.
      rewrite req_at, brk_zeros_keep, brk_unmaps_keep, brk_model_keep in grant.
      apply grant. apply forced. reflexivity.
  - intros eff unm.
    exact (brk_no_unmodeled segs _ _ model sys214 (check_syscall_sound_unmodeled _ _ _ unm)).
  - rewrite adv_ret_epend. exact after.
Qed.

Lemma node_set_tid_lazy : forall ms model x8,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 96%Z ->
  m_tid model = None ->
  node_ok segs (mkCfg ms model) tid_I (fun _ => [])
    (fun i => mkCfg (advance_past_svc (apply_effect ms (mkEffectU (proj1_sig i) [] [] [] [] [])))
                    (with_tid (proj1_sig i) model)).
Proof.
  intros ms model x8 live pend sys96 no_tid.
  refine (node_chk_noacc ms model x8 tid_I (fun i => mkEffectU (proj1_sig i) [] [] [] [] [])
            (fun i => with_tid (proj1_sig i) model) live pend _ _ _ _ _ _).
  - intros [t [lo hi]]. cbn [proj1_sig].
    rewrite (check_syscall_96 segs ms x8 _ model sys96).
    unfold check_set_tid_address. rewrite no_tid.
    apply Z.ltb_lt in lo. apply Z.ltb_lt in hi. rewrite lo, hi. reflexivity.
  - intros i (fam & _).
    unfold injected_family_off in fam. rewrite in_sysno_sys_input, sys96 in fam.
    vm_compute in fam. discriminate fam.
  - intros eff m' evs accepted _.
    rewrite (check_syscall_96 segs ms x8 eff model sys96) in accepted.
    destruct eff as [r ws zs us cs ci].
    destruct ws, zs, us, cs, ci; cbn in accepted; try discriminate accepted.
    rewrite no_tid in accepted.
    destruct (_ && _) eqn:range; [| discriminate accepted].
    injection accepted as <- <-.
    apply andb_prop in range as [lo hi]. apply Z.ltb_lt in lo. apply Z.ltb_lt in hi.
    exists (exist _ r (conj lo hi)). split; [reflexivity | split; reflexivity].
  - intros eff unm.
    rewrite (check_syscall_96 segs ms x8 eff model sys96) in unm.
    destruct eff as [r ws zs us cs ci].
    destruct ws, zs, us, cs, ci; cbn in unm; try discriminate unm.
    rewrite no_tid in unm. destruct (_ && _); discriminate unm.
  - intros i. rewrite with_tid_halted. exact live.
  - intros i. reflexivity.
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
  intros ms x8 model eff prot flags addr len sys222 prot01 core a0 al pos a1 lenpos a2 a3 a4 a5 room n free inside budget.
  subst n.
  pose proof (page_round_up_Z_bounds len ltac:(lia)) as round_rng.
  pose proof (alloc_top_room (m_vmmaps model)) as top_rng.
  pose proof (u64_range addr) as addr_rng.
  assert (len_u : bv_unsigned (Z_to_bv 64 len) = len) by (apply u64_lit; unfold two_pow_64, stack_max_size in *; lia).
  assert (shape : forall e, check_syscall (sys_input segs ms x8) e model
                  = check_mmap addr (Z_to_bv 64 len) (Z_to_bv 64 prot) flags (Z_to_bv 64 (-1)) (Z_to_bv 64 0) e model).
  { intros e. rewrite (mmap_check segs ms x8 model e sys222), a0, a1, a2, a3, a4, a5. reflexivity. }
  assert (anon : mmap_anon_b flags = true) by (apply (mmap_anon_b_of_core flags 50 core); reflexivity).
  assert (len_nz : w_is0 (Z_to_bv 64 len) = false).
  { apply bv_eqb_neq. intros zero. apply (f_equal bv_unsigned) in zero. rewrite len_u in zero.
    change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in zero. lia. }
  assert (fits : (two_pow_64 <=? bv_unsigned addr + page_round_up_Z len) = false)
    by (apply Z.leb_gt; unfold two_pow_64, stack_max_size in *; lia).
  assert (below : (bv_unsigned addr + page_round_up_Z len <=? alloc_top (m_vmmaps model)) = true)
    by (apply Z.leb_le; exact room).
  assert (aligned : (bv_unsigned addr mod page_size =? 0) = true) by (apply Z.eqb_eq; exact al).
  assert (above0 : (0 <? bv_unsigned addr) = true) by (apply Z.ltb_lt; exact pos).
  assert (not_err : errno_ret_in mmap_errnos addr = false).
  { unfold errno_ret_in, mmap_errnos. cbn [existsb]. rewrite orb_false_r. apply bv_eqb_neq.
    intros same. apply (f_equal bv_unsigned) in same. rewrite same in al. vm_compute in al. discriminate al. }
  destruct (mmap_gates_core50 flags (Z_to_bv 64 prot) core) as (no_rw & no_na & fna0 & fna3 & frw3).
  unfold check_mmap in shape.
  rewrite mmap_off_aligned_b_0, anon, len_nz, len_u, no_rw, no_na in shape.
  destruct prot01 as [-> | ->].
  - rewrite fna0, fits, below, aligned, above0, free, inside in shape. cbn [negb andb] in shape.
    split; [| split].
    + rewrite shape. unfold fixedin_ok_eff. cbn [Z.eqb].
      rewrite not_err, bv_eqb_refl, (proj2 (listNN_eqb_eq _ _) eq_refl). reflexivity.
    + intros m' ev accepted. rewrite shape in accepted.
      destruct eff as [r ws zs us cs ci].
      destruct ws; [| discriminate accepted]. destruct zs; [| discriminate accepted].
      destruct cs; [| discriminate accepted]. destruct ci; [| discriminate accepted].
      destruct (errno_ret_in mmap_errnos r) eqn:err.
      * left. split; [exact err |].
        destruct us as [| u rest].
        -- injection accepted as <- _. reflexivity.
        -- destruct (listNN_eqb (u :: rest) _); [| discriminate accepted].
           injection accepted as <- _. apply with_mmap_destroyed_halted.
      * right.
        destruct (bv_eqb r addr) eqn:same_r; [| discriminate accepted].
        destruct (listNN_eqb us _) eqn:same_us; [| discriminate accepted].
        apply bv_eqb_eq in same_r. apply listNN_eqb_eq in same_us. subst r us.
        injection accepted as <- <-. split; [reflexivity | split; reflexivity].
    + intros unm. rewrite shape in unm.
      destruct eff as [r ws zs us cs ci].
      destruct ws; [| discriminate unm]. destruct zs; [| discriminate unm].
      destruct cs; [| discriminate unm]. destruct ci; [| discriminate unm].
      destruct (errno_ret_in mmap_errnos r).
      * destruct us as [| u rest]; [discriminate unm |].
        destruct (listNN_eqb (u :: rest) _); discriminate unm.
      * destruct (bv_eqb r addr && _); discriminate unm.
  - rewrite fna3, frw3, fits, below, aligned, above0, free, inside, (budget eq_refl) in shape. cbn [negb andb] in shape.
    split; [| split].
    + rewrite shape. unfold fixedin_ok_eff. cbn [Z.eqb].
      rewrite not_err, bv_eqb_refl, (proj2 (listNN_eqb_eq _ _) eq_refl). reflexivity.
    + intros m' ev accepted. rewrite shape in accepted.
      destruct eff as [r ws zs us cs ci].
      destruct ws; [| discriminate accepted].
      destruct cs; [| discriminate accepted]. destruct ci; [| discriminate accepted].
      destruct (errno_ret_in mmap_errnos r) eqn:err.
      * left. split; [exact err |].
        destruct zs; [| discriminate accepted].
        destruct us as [| u rest].
        -- injection accepted as <- _. reflexivity.
        -- destruct (listNN_eqb (u :: rest) _); [| discriminate accepted].
           injection accepted as <- _. apply with_mmap_destroyed_halted.
      * right.
        destruct us; [| discriminate accepted].
        destruct (bv_eqb r addr) eqn:same_r; [| discriminate accepted].
        destruct (listNN_eqb zs _) eqn:same_zs; [| discriminate accepted].
        apply bv_eqb_eq in same_r. apply listNN_eqb_eq in same_zs. subst r zs.
        injection accepted as <- <-. split; [reflexivity | split; reflexivity].
    + intros unm. rewrite shape in unm.
      destruct eff as [r ws zs us cs ci].
      destruct ws; [| discriminate unm].
      destruct cs; [| discriminate unm]. destruct ci; [| discriminate unm].
      destruct (errno_ret_in mmap_errnos r).
      * destruct zs; [| discriminate unm].
        destruct us as [| u rest]; [discriminate unm |].
        destruct (listNN_eqb (u :: rest) _); discriminate unm.
      * destruct us; [| discriminate unm].
        destruct (bv_eqb r addr && _ && _); discriminate unm.
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
  intros regs pc mem rom model w prot flags addr len KB fetch ecall live a7 prot01 core a0 al pos a1 lenpos room
    a2 a3 a4 a5 n free inside budget after.
  refine (srz_sys_lazy regs pc mem rom model w KB live fetch ecall _).
  assert (sys222 : bv_unsigned (getr regs 17) = 222%Z) by (rewrite a7; apply u64_lit; lia).
  pose proof (fun eff => mmap_fixedin_check (epend regs pc mem rom (getr regs 17)) (getr regs 17) model eff
                prot flags addr len sys222 prot01 core (eq_trans (ms_gpr_epend0 _ _ _ _ _) a0) al pos
                (eq_trans (ms_gpr_epend1 _ _ _ _ _) a1) lenpos (eq_trans (ms_gpr_epend2 _ _ _ _ _) a2)
                (eq_trans (ms_gpr_epend3 _ _ _ _ _) a3) (eq_trans (ms_gpr_epend4 _ _ _ _ _) a4)
                (eq_trans (ms_gpr_epend5 _ _ _ _ _) a5) room free inside budget) as facts.
  assert (ok_spec : syscall_spec (sys_input segs (epend regs pc mem rom (getr regs 17)) (getr regs 17)) model
                      (Ok (fixedin_ok_eff prot addr n) (fixedin_ok_model prot flags addr n model) [])).
  { apply check_syscall_sound_ok. exact (proj1 (facts (fixedin_ok_eff prot addr n))). }
  assert (ret_ok : eff_ret (fixedin_ok_eff prot addr n) = addr)
    by (unfold fixedin_ok_eff; destruct (Z.eqb prot 0); reflexivity).
  assert (fam : injected_family_off ACFG (sys_input segs (epend regs pc mem rom (getr regs 17)) (getr regs 17)) = true).
  { unfold injected_family_off. rewrite in_sysno_sys_input, sys222. vm_compute. reflexivity. }
  assert (refusal_is : forall r,
            refusal_b (sys_input segs (epend regs pc mem rom (getr regs 17)) (getr regs 17)) model r
            = errno_ret_in mmap_errnos r).
  { intros r. unfold refusal_b. rewrite in_sysno_sys_input, sys222. reflexivity. }
  assert (addr_fresh : errno_ret_in mmap_errnos addr = false).
  { unfold errno_ret_in, mmap_errnos. cbn [existsb]. rewrite orb_false_r. apply bv_eqb_neq.
    intros same. apply (f_equal bv_unsigned) in same. rewrite same in al. vm_compute in al. discriminate al. }
  apply (srz_silent1 segs _ (mkCfg (advance_past_svc (apply_effect (epend regs pc mem rom (getr regs 17))
                                                       (fixedin_ok_eff prot addr n)))
                                   (fixedin_ok_model prot flags addr n model))).
  - refine (node_chk_noacc (epend regs pc mem rom (getr regs 17)) model (getr regs 17) unit
              (fun _ => fixedin_ok_eff prot addr n)
              (fun _ => fixedin_ok_model prot flags addr n model) live eq_refl _ _ _ _ _ _).
    + intros _. exact (proj1 (facts (fixedin_ok_eff prot addr n))).
    + intros _ (_ & refused & _). rewrite refusal_is, ret_ok, addr_fresh in refused. discriminate refused.
    + intros eff m' ev accepted keep.
      destruct (proj1 (proj2 (facts eff)) m' ev accepted) as [(err & halt_same) | (-> & -> & ->)].
      * exfalso.
        refine (spec_step_ok_refuted _ model eff m' ev _ _ _ fam ok_spec _ _ _ keep).
        -- rewrite refusal_is, ret_ok. exact addr_fresh.
        -- rewrite refusal_is. exact err.
        -- rewrite halt_same. exact live.
      * exists tt. split; [reflexivity | split; reflexivity].
    + intros eff. exact (proj2 (proj2 (facts eff))).
    + intros _. unfold fixedin_ok_model. rewrite with_mmap_replacement_halted, with_vmmaps_halted. exact live.
    + intros _. unfold fixedin_ok_eff. destruct (Z.eqb prot 0); reflexivity.
  - revert after. unfold fixedin_ok_eff. destruct (Z.eqb prot 0); intros after.
    + rewrite adv_unmaps1_epend. exact after.
    + rewrite adv_zeros1_epend. exact after.
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
