(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Mprotect.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import Prelude.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import PropExec CatExec CatSim SeqExec ExitSim.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import ShapeAlg ShapeAlgCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.XQ Require Import DivergeSim AgentLib AgentNodes Nodes CfgLift.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import AllocSim MmapSim.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.XQ Require Import AsanPlacement RefNodes NoReserve AsanNodesLibE AsanNodesMmLib AsanCeil.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Instance nodeslibcfg_fx : PropExec.FPState := PropExec.fx0.
Import ListNotations.
Open Scope Z_scope.

Section CfgNodes.
Variable cfg : SpuriousCfg.
Variable segs : list Segment.
#[local] Notation RZ := (realizes_cfg cfg segs).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma node_ok_const_silent_cfg : forall c (I : Type) (nx : I -> config) (i0 : I),
  node_ok segs c I (fun _ => []) nx -> (forall i, nx i = nx i0) ->
  node_ok_cfg cfg segs c I (fun _ => []) nx.
Proof.
  intros c I nx i0 [Hcomp Hexact] Hconst.
  assert (U : node_ok segs c unit (fun _ => []) (fun _ => nx i0)).
  { split; [intros []; exact (Hcomp i0)|].
    intros e st Hss. destruct (Hexact e st Hss) as (i & -> & ->). exists tt. rewrite (Hconst i). split; reflexivity. }
  pose proof (node_ok_unit_silent_cfg cfg segs c (nx i0) U) as [Uc Ue].
  split; [|intros e st Hss; apply Hexact; eapply sstep_cfg_sub; exact Hss].
  intros i. rewrite (Hconst i). exact (Uc tt).
Qed.

(* [comment removed for export] *)
Lemma node_ok_cfg_no_arm : forall ms mo x8 (I : Type) (evs : I -> list event) (nx : I -> config),
  ms_svc_pending ms = Some x8 -> injected_arm (bv_unsigned x8) = None ->
  node_ok segs (mkCfg ms mo) I evs nx -> node_ok_cfg cfg segs (mkCfg ms mo) I evs nx.
Proof.
  intros ms mo x8 I evs nx Hsvc Harm Hn. apply node_ok_cfg_lift; [exact Hn|].
  intros i. apply (sstep_cfg_of_sstep_no_arm cfg segs ms mo x8); [exact Hsvc | exact Harm | exact (proj1 Hn i)].
Qed.

Lemma injected_arm_96 : injected_arm 96 = None. Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma crz_det_noacc : forall ms model x8 eff0 m0 T,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  (forall eff m' evs,
     check_syscall (sys_input segs ms x8) eff model = CheckOk m' evs <->
     (eff = eff0 /\ m' = m0 /\ evs = [])) ->
  (forall eff, check_syscall (sys_input segs ms x8) eff model <> CheckUnmodeled) ->
  m_halted m0 = None ->
  syscall_effect_accesses eff0 = [] ->
  RZ (mkCfg (advance_past_svc (apply_effect ms eff0)) m0) T ->
  RZ (mkCfg ms model) T.
Proof.
  intros ms model x8 eff0 m0 T Hh Hsvc Hchk Hnu Hh0 Hacc Hc.
  eapply rz_silent1_unit_cfg; [eapply node_det_noacc; eassumption | exact Hc].
Qed.

(* [comment removed for export] *)
Lemma crz_cases_const : forall c (I : Type) (nx : I -> config) (T : TSet) (i0 : I),
  node_ok segs c I (fun _ => []) nx -> (forall i, nx i = nx i0) ->
  RZ (nx i0) T -> RZ c T.
Proof.
  intros c I nx T i0 Hn Hconst Hc.
  eapply (rz_silent_cfg cfg segs c I nx T i0); [apply (node_ok_const_silent_cfg c I nx i0 Hn Hconst)|].
  intros i. rewrite (Hconst i). exact Hc.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma crz_munmap_lazy : forall regs (pc : word) mem rom model w (a : word) (len : Z) K,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None ->
  getr regs 17 = Z_to_bv 64 215 ->
  getr regs 10 = a -> (bv_unsigned a mod page_size = 0)%Z ->
  getr regs 11 = Z_to_bv 64 len -> (0 < len)%Z ->
  (bv_unsigned a + page_round_up_Z len <= TASK_SIZE)%Z ->
  map_has (vm_maps (m_vmmaps model)) a (Z_to_bv 64 (page_round_up_Z len)) = true ->
  RZ (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 0)) (v_addi pc 4)
                 (unfill a (Z_to_bv 64 (page_round_up_Z len)) mem) rom)
          (munmap_model a (Z_to_bv 64 (page_round_up_Z len)) model)) K ->
  RZ (mkCfg (mkst regs pc mem rom) model) K.
Proof.
  intros regs pc mem rom model w a len K HF HE Hh H17 H10 Hal H11 Hlen Hnw Hhas Hc.
  assert (Hlen' : (len < two_pow_64)%Z).
  { pose proof (page_round_up_Z_bounds len ltac:(lia)). pose proof (u64_range a). unfold TASK_SIZE, two_pow_64 in *. lia. }
  eapply rz_sys_lazy_cfg; [exact Hh | exact HF | exact HE |].
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
  eapply (crz_det_noacc ms model (getr regs 17)
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

Lemma crz_set_tid_lazy : forall regs (pc : word) mem rom model K w,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None ->
  getr regs 17 = Z_to_bv 64 96 ->
  m_tid model = None ->
  (forall tid, (0 < bv_unsigned tid < PID_MAX_ENVELOPE)%Z ->
     RZ (mkCfg (mkst (regupd regs 10 tid) (v_addi pc 4) mem rom) (with_tid tid model)) K) ->
  RZ (mkCfg (mkst regs pc mem rom) model) K.
Proof.
  intros regs pc mem rom model K w HF HE Hh H17 Htid Hk.
  eapply rz_sys_lazy_cfg; [exact Hh | exact HF | exact HE |].
  assert (Hno : bv_unsigned (getr regs 17) = 96%Z) by (rewrite H17; apply u64_lit; lia).
  eapply (rz_silent_cfg cfg segs _ tid_I _ K (exist _ (Z_to_bv 64 1) one_tid_ok)).
  - eapply node_ok_cfg_no_arm; [reflexivity | rewrite Hno; apply injected_arm_96 |].
    eapply node_set_tid_lazy; [exact Hh | reflexivity | exact Hno | exact Htid].
  - intros [t Ht]. cbn [proj1_sig].
    change (mkEffectU t [] [] [] [] []) with (mkEffect t [] []).
    rewrite apply_effect_no_write, adv_set_epend. apply Hk. exact Ht.
Qed.

Lemma crz_exit_at_lazy : forall regs (pc : word) mem rom model w code,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None ->
  (getr regs 17 = Z_to_bv 64 94 \/ getr regs 17 = Z_to_bv 64 93) ->
  getr regs 10 = code ->
  RZ (mkCfg (mkst regs pc mem rom) model) (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model)).
Proof.
  intros regs pc mem rom model w code HF HE Hh H17 H10.
  eapply rz_sys_lazy_cfg; [exact Hh | exact HF | exact HE |].
  rewrite <- H10, <- (ms_gpr_epend0 regs pc mem rom (getr regs 17)).
  eapply rz_exit_cfg; [exact Hh | reflexivity |].
  destruct H17 as [H|H]; [right|left]; rewrite H; reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma crz_brk_query_lazy : forall regs (pc : word) mem rom model w K,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None ->
  getr regs 17 = Z_to_bv 64 214 ->
  getr regs 10 = Z_to_bv 64 0 ->
  RZ (mkCfg (mkst (regupd regs 10 (vm_brk (m_vmmaps model))) (v_addi pc 4) mem rom) model) K ->
  RZ (mkCfg (mkst regs pc mem rom) model) K.
Proof.
  intros regs pc mem rom model w K HF HE Hh H17 H10 Hc.
  eapply rz_sys_lazy_cfg; [exact Hh | exact HF | exact HE |].
  set (ms := epend regs pc mem rom (getr regs 17)).
  assert (Hno : bv_unsigned (getr regs 17) = 214%Z) by (rewrite H17; apply u64_lit; lia).
  assert (H0 : ms_gpr ms 0 = Z_to_bv 64 0) by (unfold ms; rewrite ms_gpr_epend0; exact H10).
  assert (Hcases : forall r, brk_resolution_ok model (ms_gpr ms 0) r <-> r = vm_brk (m_vmmaps model)).
  { intros r. rewrite H0. unfold brk_resolution_ok, Mmap.brk_r_ok. cbv zeta.
    unfold w_is0. rewrite bv_eqb_refl. cbn [orb]. apply bv_eqb_eq. }
  assert (Hq : brk_resolution_ok model (ms_gpr ms 0) (vm_brk (m_vmmaps model))) by (apply Hcases; reflexivity).
  eapply (crz_cases_const _ _ _ K (exist _ _ Hq)); [eapply node_brk_lazy; [exact Hh | reflexivity | exact Hno] | |].
  - intros [r Hr]. cbn [proj1_sig]. pose proof (proj1 (Hcases r) Hr) as Er. subst r. reflexivity.
  - cbn [proj1_sig]. rewrite H0, brk_zeros_query, brk_unmaps_keep.
    rewrite (brk_model_query _ model eq_refl), vmmaps_eta, with_vmmaps_eta.
    unfold ms. rewrite adv_ret_epend. exact Hc.
Qed.

(* [comment removed for export] *)
Lemma crz_brk_grow_blocked_lazy : forall regs (pc : word) mem rom model w (req : word) KA,
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
  RZ (mkCfg (mkst (regupd regs 10 b) (v_addi pc 4) mem rom) model) KA ->
  RZ (mkCfg (mkst regs pc mem rom) model) KA.
Proof.
  intros regs pc mem rom model w req KA HF HE Hh H17 h b H10 Hpos Hs Hb Hblk HA.
  eapply rz_sys_lazy_cfg; [exact Hh | exact HF | exact HE |].
  set (ms := epend regs pc mem rom (getr regs 17)).
  assert (Hno : bv_unsigned (getr regs 17) = 214%Z) by (rewrite H17; apply u64_lit; lia).
  assert (H0 : ms_gpr ms 0 = req) by (unfold ms; rewrite ms_gpr_epend0; exact H10).
  assert (Hcases : forall r, brk_resolution_ok model (ms_gpr ms 0) r <-> r = b).
  { intros r. rewrite H0, (brk_r_ok_grow_cases model req r Hpos Hs Hb). fold h. fold b. split.
    - intros [-> | [-> Hg]]; [reflexivity | rewrite Hblk in Hg; discriminate].
    - intros ->. left. reflexivity. }
  assert (Hkeep : brk_resolution_ok model (ms_gpr ms 0) b) by (apply Hcases; reflexivity).
  eapply (crz_cases_const _ _ _ KA (exist _ b Hkeep)); [eapply node_brk_lazy; [exact Hh | reflexivity | exact Hno] | |].
  - intros [r Hr]. cbn [proj1_sig]. pose proof (proj1 (Hcases r) Hr) as Er. subst r. reflexivity.
  - cbn [proj1_sig]. fold h. fold b.
    rewrite brk_zeros_keep, brk_unmaps_keep. unfold b, h. rewrite brk_model_keep.
    unfold ms. rewrite adv_ret_epend. exact HA.
Qed.

(* [comment removed for export] *)
Hypothesis ALLOC_OFF : family_may_fail cfg FamAlloc = false.

Lemma injected_arm_214 : injected_arm 214 = Some (mkInjectedArm 214 FamAlloc []).
Proof. reflexivity. Qed.
Lemma injected_family_off_brk : forall i,
  bv_unsigned (in_sysno i) = 214 -> injected_family_off cfg i = true.
Proof. intros i H. unfold injected_family_off. rewrite H, injected_arm_214. cbn [ia_family negb]. rewrite ALLOC_OFF. reflexivity. Qed.
Lemma refusal_b_brk : forall i m r,
  bv_unsigned (in_sysno i) = 214 -> refusal_b i m r = Run.brk_refusal_b m (in_arg i 0) r.
Proof. intros i m r H. unfold refusal_b. rewrite H. reflexivity. Qed.

(* [comment removed for export] *)
Lemma crz_brk_grow_granted : forall regs (pc : word) mem rom model w (d : Z) KB,
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
  RZ (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 (bv_unsigned b + d))) (v_addi pc 4)
                 (zfill b (Z_to_bv 64 d) mem) rom)
          (with_vmmaps (mkVmMapsFull (vm_reserved h) ((b, Z_to_bv 64 d) :: vm_maps h)
                         (vm_noaccess h) (vm_start_brk h)
                         (Z_to_bv 64 (bv_unsigned b + d)) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)) model)) KB ->
  RZ (mkCfg (mkst regs pc mem rom) model) KB.
Proof.
  intros regs pc mem rom model w d KB HF HE Hh H17 h b Hbal Hdal Hd Hb0 Hnw Hs H10 Hadm HB.
  pose proof (u64_range b) as Hbr.
  set (req := Z_to_bv 64 (bv_unsigned b + d)) in *.
  assert (Hureq : bv_unsigned req = (bv_unsigned b + d)%Z) by (unfold req; apply u64_lit; lia).
  eapply rz_sys_lazy_cfg; [exact Hh | exact HF | exact HE |].
  set (ms := epend regs pc mem rom (getr regs 17)).
  assert (Hno : bv_unsigned (getr regs 17) = 214%Z) by (rewrite H17; apply u64_lit; lia).
  assert (H0 : ms_gpr ms 0 = req) by (unfold ms; rewrite ms_gpr_epend0; exact H10).
  assert (Hsys : bv_unsigned (in_sysno (sys_input segs ms (getr regs 17))) = 214) by (rewrite in_sysno_sys_input; exact Hno).
  assert (Harg0 : in_arg (sys_input segs ms (getr regs 17)) 0 = req) by (rewrite in_arg0_sys_input; exact H0).
  assert (Hneq : req <> b).
  { intros E. apply (f_equal bv_unsigned) in E. rewrite Hureq in E. unfold b in E. lia. }
  assert (Hreq0 : req <> Z_to_bv 64 0).
  { intros E. apply (f_equal bv_unsigned) in E. rewrite Hureq in E. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in E. lia. }
  assert (REF : forall r, refusal_b (sys_input segs ms (getr regs 17)) model r = bv_eqb r b).
  { intros r. rewrite (refusal_b_brk _ _ _ Hsys), Harg0. unfold Run.brk_refusal_b. fold h. fold b.
    unfold w_is0. rewrite (bv_eqb_neq _ _ Hreq0), (bv_eqb_neq _ _ Hneq). cbn [negb andb].
    replace (bv_unsigned req <? bv_unsigned (Mmap.min_brk h))%Z with false; [destruct (bv_eqb r b); reflexivity|].
    symmetry. apply Z.ltb_ge. unfold Mmap.min_brk. rewrite Hureq. lia. }
  assert (RES : forall r, brk_resolution_ok model (ms_gpr ms 0) r <-> (r = b \/ (r = req /\ Mmap.brk_grow_ok model req req = true))).
  { intros r. rewrite H0. apply brk_r_ok_grow_cases; fold h; fold b; rewrite ?Hureq; lia. }
  pose (eff1 := mkEffectU req [] (brk_zeros (ms_gpr ms 0) req (vm_brk (m_vmmaps model))) (brk_unmaps req (vm_brk (m_vmmaps model))) [] []).
  eapply (rz_silent_cfg cfg segs (mkCfg ms model) unit
            (fun _ => mkCfg (advance_past_svc (apply_effect ms eff1)) (brk_model (ms_gpr ms 0) req model)) KB tt).
  - apply (node_chk_grant_cfg cfg segs ms model (getr regs 17) unit (fun _ => eff1) (fun _ => brk_model (ms_gpr ms 0) req model) (fun _ => []) tt
             Hh eq_refl (injected_family_off_brk _ Hsys)).
    + intros []. apply check_syscall_ok_iff. apply (brk_ok_intro segs ms _ model req Hno). apply RES. right. split; [reflexivity | exact Hadm].
    + intros []. cbv beta delta [eff_ret eff1]. rewrite REF. apply bv_eqb_neq. exact Hneq.
    + intros eff m' ev Hc Hr. apply check_syscall_ok_iff in Hc.
      apply (brk_ok_iff segs ms _ model eff m' ev Hno) in Hc as (Heff & -> & Hok & ->).
      rewrite REF in Hr. apply RES in Hok as [E | [E _]].
      * rewrite E, bv_eqb_refl in Hr. discriminate Hr.
      * exists tt. unfold eff1. rewrite Heff, E. repeat split; reflexivity.
    + intros eff m' ev Hc Hr. apply check_syscall_ok_iff in Hc.
      apply (brk_ok_iff segs ms _ model eff m' ev Hno) in Hc as (Heff & -> & Hok & ->). rewrite brk_model_halted. exact Hh.
    + intros eff Hc. apply (brk_no_unmodeled segs ms _ model Hno). exact (proj1 (check_syscall_err_iff _ _ _) Hc).
    + intros []. rewrite brk_model_halted. exact Hh.
    + intros []. reflexivity.
  - intros []. unfold eff1.
    assert (Hlt : (bv_unsigned b < bv_unsigned req)%Z) by (rewrite Hureq; lia).
    rewrite H0. fold h. fold b.
    rewrite (brk_zeros_grow req req b Hreq0 Hb0 Hlt), (brk_unmaps_grow req b) by lia.
    unfold brk_page_range.
    rewrite (page_round_up_Z_aligned (bv_unsigned b)) by (first [lia | exact Hbal]).
    rewrite (page_round_up_Z_aligned (bv_unsigned req))
      by (rewrite Hureq; first [lia | rewrite Z.add_mod, Hbal, Hdal by (unfold page_size; lia); reflexivity]).
    rewrite (proj2 (Z.ltb_lt _ _) Hlt).
    replace (Z_to_bv 64 (bv_unsigned b)) with b by (symmetry; apply Z_to_bv_u_eq'; reflexivity).
    rewrite Hureq. replace (bv_unsigned b + d - bv_unsigned b)%Z with d by lia.
    unfold req, b, h. rewrite (brk_model_grow_eq model d) by assumption.
    unfold ms. rewrite adv_zeros1_epend. exact HB.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma injected_arm_226 : injected_arm 226 = Some (mkInjectedArm 226 FamAlloc mprotect_errnos).
Proof. reflexivity. Qed.
Lemma injected_family_off_mprotect : forall i,
  bv_unsigned (in_sysno i) = 226 -> injected_family_off cfg i = true.
Proof. intros i H. unfold injected_family_off. rewrite H, injected_arm_226. cbn [ia_family negb]. rewrite ALLOC_OFF. reflexivity. Qed.
Lemma refusal_b_mprotect : forall i m r,
  bv_unsigned (in_sysno i) = 226 -> refusal_b i m r = errno_ret_in mprotect_errnos r.
Proof. intros i m r H. unfold refusal_b. rewrite H, injected_arm_226. reflexivity. Qed.

(* [comment removed for export] *)
Lemma grant_pin_not_errno : forall model a n,
  0 <= n -> grant_ok_na_pin model a n = true -> errno_ret_in mmap_errnos a = false.
Proof.
  intros model a n Hn Hg. unfold grant_ok_na_pin in Hg.
  apply andb_true_iff in Hg as [Hg _]. apply andb_true_iff in Hg as [Hg Htop]. apply Z.leb_le in Htop.
  pose proof (alloc_top_room (m_vmmaps model)) as Hr.
  apply errno_ret_in_below; [reflexivity|].
  rewrite stack_max_size_val in Hr. lia.
Qed.

(* [comment removed for export] *)
Lemma rz_mmap_rw1_cfg : forall regs (pc : word) mem rom model w (len : Z) (flags : word) KB,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None ->
  getr regs 17 = Z_to_bv 64 222 ->
  getr regs 11 = Z_to_bv 64 len -> (0 < len < 2 ^ 64)%Z ->
  getr regs 12 = Z_to_bv 64 3 -> getr regs 13 = flags -> mmap_flags_core flags = 34%Z ->
  getr regs 14 = Z_to_bv 64 (-1) -> getr regs 15 = Z_to_bv 64 0 ->
  let nZ := page_round_up_Z len in
  let n := Z_to_bv 64 nZ in
  (exists a, grant_ok_na_pin model a nZ = true) ->
  mmap_noreserve_backed_ok flags model nZ = true ->
  (forall a, grant_ok_na_pin model a nZ = true ->
     realizes_cfg cfg segs (mkCfg (mkst (regupd regs 10 a) (v_addi pc 4) (zfill a n mem) rom)
                                 (with_mmap_backing flags a n (mmap_model a n model))) KB) ->
  realizes_cfg cfg segs (mkCfg (mkst regs pc mem rom) model) KB.
Proof.
  intros regs pc mem rom model w len flags KB HF HE Hh H17 H11 Hlen H12 H13 Hcore H14 H15 nZ n (a0 & Ha0) Hb0 HB.
  eapply (rz_sys_lazy_cfg cfg segs); [exact Hh | exact HF | exact HE |].
  set (ms := epend regs pc mem rom (getr regs 17)).
  assert (Hno : bv_unsigned (getr regs 17) = 222%Z) by (rewrite H17; apply u64_lit; lia).
  destruct (epend_len regs pc mem rom len H11 Hlen) as [Hl1 Hne1]. fold ms in Hl1, Hne1.
  pose proof (fun eff => mmap_rw_check segs ms (getr regs 17) model eff flags Hno Hne1
                           ltac:(unfold ms; rewrite ms_gpr_epend2; exact H12)
                           ltac:(unfold ms; rewrite ms_gpr_epend3; exact H13) Hcore
                           ltac:(unfold ms; rewrite ms_gpr_epend4; exact H14)
                           ltac:(unfold ms; rewrite ms_gpr_epend5; exact H15)) as Hchk.
  cbv zeta in Hchk. rewrite Hl1 in Hchk. fold nZ n in Hchk. rewrite Hb0 in Hchk.
  assert (Hn0 : (0 <= nZ)%Z) by (unfold nZ; apply page_round_up_Z_nonneg; lia).
  assert (Hsys : bv_unsigned (in_sysno (sys_input segs ms (getr regs 17))) = 222) by (rewrite in_sysno_sys_input; exact Hno).
  pose (IB := {a : word | grant_ok_na_pin model a nZ = true}).
  pose (effs := fun i : IB => match i with exist _ a _ => mkEffectU a [] [(a, n)] [] [] [] end).
  pose (ms' := fun i : IB => match i with exist _ a _ => with_mmap_backing flags a n (mmap_model a n model) end).
  eapply (rz_silent_cfg cfg segs (mkCfg ms model) IB
            (fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms' i)) KB (exist _ a0 Ha0)).
  - apply (node_chk_grant_cfg cfg segs ms model (getr regs 17) IB effs ms' (fun _ => []) (exist _ a0 Ha0) Hh eq_refl
             (injected_family_off_mmap cfg ALLOC_OFF _ Hsys)).
    + intros [a Ha]; cbn [effs ms']. rewrite Hchk.
      rewrite (grant_pin_not_errno model a nZ Hn0 Ha), Ha. cbn [andb].
      rewrite (proj2 (listNN_eqb_eq _ _) eq_refl). reflexivity.
    + intros [a Ha]; cbn [effs eff_ret]. rewrite (refusal_b_mmap _ _ _ Hsys). exact (grant_pin_not_errno model a nZ Hn0 Ha).
    + intros [r ws zs us cs ci] m' evs Hc Hr. rewrite (refusal_b_mmap _ _ _ Hsys) in Hr. cbn [eff_ret] in Hr.
      rewrite Hchk in Hc.
      destruct ws; [|discriminate]. destruct us; [|destruct zs; discriminate].
      destruct cs; [|destruct zs; discriminate]. destruct ci; [|destruct zs; discriminate].
      rewrite Hr in Hc.
      destruct (grant_ok_na_pin model r nZ) eqn:Hg; [|discriminate].
      cbn [andb] in Hc.
      destruct (listNN_eqb zs [(r, n)]) eqn:Hl; [|discriminate].
      apply listNN_eqb_eq in Hl. subst zs. injection Hc as <- <-.
      exists (exist _ r Hg). repeat split; reflexivity.
    + intros [r ws zs us cs ci] m' evs Hc Hr. rewrite (refusal_b_mmap _ _ _ Hsys) in Hr. cbn [eff_ret] in Hr.
      rewrite Hchk in Hc.
      destruct ws; [|discriminate]. destruct us; [|destruct zs; discriminate].
      destruct cs; [|destruct zs; discriminate]. destruct ci; [|destruct zs; discriminate].
      rewrite Hr in Hc. destruct zs; [|discriminate]. injection Hc as <- <-. exact Hh.
    + intros [r ws zs us cs ci] Hc. rewrite Hchk in Hc.
      destruct ws; [|discriminate]. destruct us; [|destruct zs; discriminate].
      destruct cs; [|destruct zs; discriminate]. destruct ci; [|destruct zs; discriminate].
      destruct (errno_ret_in mmap_errnos r); [destruct zs; discriminate|].
      destruct (grant_ok_na_pin model r nZ && true && listNN_eqb zs [(r, n)])%bool; discriminate.
    + intros [a Ha]; cbn [ms']. rewrite with_mmap_backing_halted. unfold mmap_model. rewrite with_vmmaps_halted. exact Hh.
    + intros [a Ha]; reflexivity.
  - intros [a Ha]. cbn [effs ms']. unfold ms. rewrite adv_zeros1_epend. apply HB. exact Ha.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma rz_mmap_none1_cfg : forall regs (pc : word) mem rom model w (len : Z) (flags : word) KB,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None ->
  getr regs 17 = Z_to_bv 64 222 ->
  getr regs 11 = Z_to_bv 64 len -> (0 < len < 2 ^ 64)%Z ->
  getr regs 12 = Z_to_bv 64 0 -> getr regs 13 = flags -> mmap_flags_core flags = 34%Z ->
  getr regs 14 = Z_to_bv 64 (-1) -> getr regs 15 = Z_to_bv 64 0 ->
  let nZ := page_round_up_Z len in
  let n := Z_to_bv 64 nZ in
  (exists a, grant_ok_na_pin model a nZ = true) ->
  (forall a, grant_ok_na_pin model a nZ = true ->
     realizes_cfg cfg segs (mkCfg (mkst (regupd regs 10 a) (v_addi pc 4) (unfill a n mem) rom)
                                 (with_mmap_backing flags a n (noaccess_model a n model))) KB) ->
  realizes_cfg cfg segs (mkCfg (mkst regs pc mem rom) model) KB.
Proof.
  intros regs pc mem rom model w len flags KB HF HE Hh H17 H11 Hlen H12 H13 Hcore H14 H15 nZ n (a0 & Ha0) HB.
  eapply (rz_sys_lazy_cfg cfg segs); [exact Hh | exact HF | exact HE |].
  set (ms := epend regs pc mem rom (getr regs 17)).
  assert (Hno : bv_unsigned (getr regs 17) = 222%Z) by (rewrite H17; apply u64_lit; lia).
  destruct (epend_len regs pc mem rom len H11 Hlen) as [Hl1 Hne1]. fold ms in Hl1, Hne1.
  pose proof (fun eff => mmap_none_check segs ms (getr regs 17) model eff flags Hno Hne1
                           ltac:(unfold ms; rewrite ms_gpr_epend2; exact H12)
                           ltac:(unfold ms; rewrite ms_gpr_epend3; exact H13) Hcore
                           ltac:(unfold ms; rewrite ms_gpr_epend4; exact H14)
                           ltac:(unfold ms; rewrite ms_gpr_epend5; exact H15)) as Hchk.
  cbv zeta in Hchk. rewrite Hl1 in Hchk. fold nZ n in Hchk.
  assert (Hn0 : (0 <= nZ)%Z) by (unfold nZ; apply page_round_up_Z_nonneg; lia).
  assert (Hsys : bv_unsigned (in_sysno (sys_input segs ms (getr regs 17))) = 222) by (rewrite in_sysno_sys_input; exact Hno).
  pose (IB := {a : word | grant_ok_na_pin model a nZ = true}).
  pose (effs := fun i : IB => match i with exist _ a _ => mkEffectU a [] [] [(a, n)] [] [] end).
  pose (ms' := fun i : IB => match i with exist _ a _ => with_mmap_backing flags a n (noaccess_model a n model) end).
  eapply (rz_silent_cfg cfg segs (mkCfg ms model) IB
            (fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms' i)) KB (exist _ a0 Ha0)).
  - apply (node_chk_grant_cfg cfg segs ms model (getr regs 17) IB effs ms' (fun _ => []) (exist _ a0 Ha0) Hh eq_refl
             (injected_family_off_mmap cfg ALLOC_OFF _ Hsys)).
    + intros [a Ha]; cbn [effs ms']. rewrite Hchk.
      rewrite (grant_pin_not_errno model a nZ Hn0 Ha), Ha. cbn [andb].
      rewrite (proj2 (listNN_eqb_eq _ _) eq_refl). reflexivity.
    + intros [a Ha]; cbn [effs eff_ret]. rewrite (refusal_b_mmap _ _ _ Hsys). exact (grant_pin_not_errno model a nZ Hn0 Ha).
    + intros [r ws zs us cs ci] m' evs Hc Hr. rewrite (refusal_b_mmap _ _ _ Hsys) in Hr. cbn [eff_ret] in Hr.
      rewrite Hchk in Hc.
      destruct ws; [|discriminate]. destruct zs; [|discriminate].
      destruct cs; [|destruct us; discriminate]. destruct ci; [|destruct us; discriminate].
      rewrite Hr in Hc.
      destruct (grant_ok_na_pin model r nZ) eqn:Hg; [|discriminate].
      destruct (listNN_eqb us [(r, n)]) eqn:Hl; [|discriminate].
      apply listNN_eqb_eq in Hl. subst us. injection Hc as <- <-.
      exists (exist _ r Hg). repeat split; reflexivity.
    + intros [r ws zs us cs ci] m' evs Hc Hr. rewrite (refusal_b_mmap _ _ _ Hsys) in Hr. cbn [eff_ret] in Hr.
      rewrite Hchk in Hc.
      destruct ws; [|discriminate]. destruct zs; [|discriminate].
      destruct cs; [|destruct us; discriminate]. destruct ci; [|destruct us; discriminate].
      rewrite Hr in Hc. destruct us; [|discriminate]. injection Hc as <- <-. exact Hh.
    + intros [r ws zs us cs ci] Hc. rewrite Hchk in Hc.
      destruct ws; [|discriminate]. destruct zs; [|discriminate].
      destruct cs; [|destruct us; discriminate]. destruct ci; [|destruct us; discriminate].
      destruct (errno_ret_in mmap_errnos r); [destruct us; discriminate|].
      destruct (grant_ok_na_pin model r nZ && listNN_eqb us [(r, n)])%bool; discriminate.
    + intros [a Ha]; cbn [ms']. rewrite with_mmap_backing_halted. unfold noaccess_model. rewrite with_vmmaps_halted. exact Hh.
    + intros [a Ha]; reflexivity.
  - intros [a Ha]. cbn [effs ms']. unfold ms. rewrite adv_unmaps1_epend. apply HB. exact Ha.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma grant_witness_of_totals : forall model nZ tot,
  0 < nZ -> nZ mod page_size = 0 ->
  init_sp_ok (m_vmmaps model) ->
  gw_sizes (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model)) <= tot ->
  bottomup_floor + nZ + tot
    + Z.of_nat (length (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model))) * (nZ + 4095)
    <= alloc_ceiling ->
  exists a, grant_ok_na_pin model a nZ = true.
Proof.
  intros model nZ tot HnZ Hal Hisp Htot Hband.
  destruct (free_gap_of_totals (m_vmmaps model) nZ tot ltac:(lia) Htot Hband) as (g & Hgal & Hfl & Hc & Hfree & _).
  pose proof (alloc_ceiling_le_alloc_top _ Hisp) as Htop.
  assert (Hg64 : 0 <= g < 2 ^ 64) by (rewrite bottomup_floor_val in Hfl; unfold alloc_ceiling in Hc; lia).
  exists (Z_to_bv 64 g). unfold grant_ok_na_pin.
  rewrite u64_lit by lia. rewrite Hfree.
  rewrite (proj2 (Z.eqb_eq _ _) Hgal).
  assert (H0 : 0 < g) by (rewrite bottomup_floor_val in Hfl; lia). rewrite (proj2 (Z.ltb_lt _ _) H0).
  assert (Hle : g + nZ <= alloc_top (m_vmmaps model)) by lia. rewrite (proj2 (Z.leb_le _ _) Hle). reflexivity.
Qed.


(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma addr_below_ceiling_not_errno : forall (addr : word) len,
  0 < len -> bv_unsigned addr + page_round_up_Z len <= alloc_ceiling -> errno_ret_in mmap_errnos addr = false.
Proof.
  intros addr len Hlen Hce. apply errno_ret_in_below; [reflexivity|]. pose proof alloc_ceiling_val.
  pose proof (page_round_up_Z_bounds len ltac:(lia)). unfold two_pow_64. lia.
Qed.

Lemma crz_mmap_fixed_rw_free1 : forall regs (pc : word) mem rom model w (addr : word) (len : Z) (flags : word) KB,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None ->
  getr regs 17 = Z_to_bv 64 222 ->
  getr regs 10 = addr -> (bv_unsigned addr mod page_size = 0)%Z -> (0 < bv_unsigned addr)%Z ->
  getr regs 11 = Z_to_bv 64 len -> (0 < len)%Z ->
  (bv_unsigned addr + page_round_up_Z len <= alloc_ceiling)%Z -> init_sp_ok (m_vmmaps model) ->
  getr regs 12 = Z_to_bv 64 3 -> getr regs 13 = flags -> mmap_flags_core flags = 50%Z ->
  getr regs 14 = Z_to_bv 64 (-1) -> getr regs 15 = Z_to_bv 64 0 ->
  let nZ := page_round_up_Z len in let n := Z_to_bv 64 nZ in
  region_free (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model)) addr n = true ->
  mmap_noreserve_backed_ok flags model nZ = true ->
  RZ (mkCfg (mkst (regupd regs 10 addr) (v_addi pc 4) (zfill addr n mem) rom)
          (with_mmap_backing flags addr n (mmap_model addr n model))) KB ->
  RZ (mkCfg (mkst regs pc mem rom) model) KB.
Proof.
  intros regs pc mem rom model w addr len flags KB HF HE Hh H17 H10 Hal Hpos H11 Hlen Hce Hisp H12 H13 Hcore H14 H15
         nZ n Hrf Hbk HB.
  eapply (rz_sys_lazy_cfg cfg segs); [exact Hh | exact HF | exact HE |].
  set (ms := epend regs pc mem rom (getr regs 17)).
  assert (Hno : bv_unsigned (getr regs 17) = 222%Z) by (rewrite H17; apply u64_lit; lia).
  assert (Hsys : bv_unsigned (in_sysno (sys_input segs ms (getr regs 17))) = 222) by (rewrite in_sysno_sys_input; exact Hno).
  pose proof (fun eff => mmap_fixed_rw_free_check segs ms (getr regs 17) model eff flags addr len Hno
                ltac:(unfold ms; rewrite ms_gpr_epend0; exact H10) Hal Hpos
                ltac:(unfold ms; rewrite ms_gpr_epend1; exact H11) Hlen Hce Hisp
                ltac:(unfold ms; rewrite ms_gpr_epend2; exact H12)
                ltac:(unfold ms; rewrite ms_gpr_epend3; exact H13) Hcore
                ltac:(unfold ms; rewrite ms_gpr_epend4; exact H14)
                ltac:(unfold ms; rewrite ms_gpr_epend5; exact H15) Hrf) as Hchk.
  cbv zeta in Hchk. fold nZ in Hchk. fold n in Hchk. rewrite Hbk in Hchk.
  pose proof (addr_below_ceiling_not_errno addr len Hlen Hce) as Hna.
  pose (eff1 := mkEffectU addr [] [(addr, n)] [] [] []).
  eapply (rz_silent_cfg cfg segs (mkCfg ms model) unit
            (fun _ => mkCfg (advance_past_svc (apply_effect ms eff1)) (with_mmap_backing flags addr n (mmap_model addr n model))) KB tt).
  - apply (node_chk_grant_cfg cfg segs ms model (getr regs 17) unit (fun _ => eff1) (fun _ => with_mmap_backing flags addr n (mmap_model addr n model))
             (fun _ => []) tt Hh eq_refl (injected_family_off_mmap cfg ALLOC_OFF _ Hsys)).
    + intros []. cbv beta delta [eff1]. rewrite Hchk. cbv beta iota. rewrite Hna, bv_eqb_refl, (proj2 (listNN_eqb_eq _ _) eq_refl). reflexivity.
    + intros []. cbv beta delta [eff_ret eff1]. rewrite (refusal_b_mmap _ _ _ Hsys). exact Hna.
    + intros [r ws zs us cs ci] m' evs Hc Hr. rewrite (refusal_b_mmap _ _ _ Hsys) in Hr. cbn [eff_ret] in Hr. rewrite Hchk in Hc.
      destruct ws; [|discriminate]. destruct us; [|destruct zs; discriminate].
      destruct cs; [|destruct zs; discriminate]. destruct ci; [|destruct zs; discriminate].
      rewrite Hr in Hc. destruct (bv_eqb r addr) eqn:Eb; [|discriminate].
      destruct (listNN_eqb zs [(addr, n)]) eqn:Hl; [|discriminate].
      apply bv_eqb_eq in Eb. apply listNN_eqb_eq in Hl. subst r zs. cbn [andb] in Hc. injection Hc as <- <-.
      exists tt. repeat split; reflexivity.
    + intros [r ws zs us cs ci] m' evs Hc Hr. rewrite (refusal_b_mmap _ _ _ Hsys) in Hr. cbn [eff_ret] in Hr. rewrite Hchk in Hc.
      destruct ws; [|discriminate]. destruct us; [|destruct zs; discriminate].
      destruct cs; [|destruct zs; discriminate]. destruct ci; [|destruct zs; discriminate].
      rewrite Hr in Hc. destruct zs; [|discriminate]. injection Hc as <- <-. exact Hh.
    + intros [r ws zs us cs ci] Hc. rewrite Hchk in Hc.
      destruct ws; [|discriminate]. destruct us; [|destruct zs; discriminate].
      destruct cs; [|destruct zs; discriminate]. destruct ci; [|destruct zs; discriminate].
      destruct (errno_ret_in mmap_errnos r); [destruct zs; discriminate|].
      destruct (bv_eqb r addr && listNN_eqb zs [(addr, n)] && true)%bool; discriminate.
    + intros []. rewrite with_mmap_backing_halted. unfold mmap_model. rewrite with_vmmaps_halted. exact Hh.
    + intros []. reflexivity.
  - intros []. cbv beta delta [eff1]. unfold ms. rewrite adv_zeros1_epend. exact HB.
Qed.

Lemma crz_mmap_fixed_none_free1 : forall regs (pc : word) mem rom model w (addr : word) (len : Z) (flags : word) KB,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None ->
  getr regs 17 = Z_to_bv 64 222 ->
  getr regs 10 = addr -> (bv_unsigned addr mod page_size = 0)%Z -> (0 < bv_unsigned addr)%Z ->
  getr regs 11 = Z_to_bv 64 len -> (0 < len)%Z ->
  (bv_unsigned addr + page_round_up_Z len <= alloc_ceiling)%Z -> init_sp_ok (m_vmmaps model) ->
  getr regs 12 = Z_to_bv 64 0 -> getr regs 13 = flags -> mmap_flags_core flags = 50%Z ->
  getr regs 14 = Z_to_bv 64 (-1) -> getr regs 15 = Z_to_bv 64 0 ->
  let nZ := page_round_up_Z len in let n := Z_to_bv 64 nZ in
  region_free (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model)) addr n = true ->
  RZ (mkCfg (mkst (regupd regs 10 addr) (v_addi pc 4) (unfill addr n mem) rom)
          (with_mmap_backing flags addr n (noaccess_model addr n model))) KB ->
  RZ (mkCfg (mkst regs pc mem rom) model) KB.
Proof.
  intros regs pc mem rom model w addr len flags KB HF HE Hh H17 H10 Hal Hpos H11 Hlen Hce Hisp H12 H13 Hcore H14 H15
         nZ n Hrf HB.
  eapply (rz_sys_lazy_cfg cfg segs); [exact Hh | exact HF | exact HE |].
  set (ms := epend regs pc mem rom (getr regs 17)).
  assert (Hno : bv_unsigned (getr regs 17) = 222%Z) by (rewrite H17; apply u64_lit; lia).
  assert (Hsys : bv_unsigned (in_sysno (sys_input segs ms (getr regs 17))) = 222) by (rewrite in_sysno_sys_input; exact Hno).
  pose proof (fun eff => mmap_fixed_none_free_check segs ms (getr regs 17) model eff flags addr len Hno
                ltac:(unfold ms; rewrite ms_gpr_epend0; exact H10) Hal Hpos
                ltac:(unfold ms; rewrite ms_gpr_epend1; exact H11) Hlen Hce Hisp
                ltac:(unfold ms; rewrite ms_gpr_epend2; exact H12)
                ltac:(unfold ms; rewrite ms_gpr_epend3; exact H13) Hcore
                ltac:(unfold ms; rewrite ms_gpr_epend4; exact H14)
                ltac:(unfold ms; rewrite ms_gpr_epend5; exact H15) Hrf) as Hchk.
  cbv zeta in Hchk. fold nZ in Hchk. fold n in Hchk.
  pose proof (addr_below_ceiling_not_errno addr len Hlen Hce) as Hna.
  pose (eff1 := mkEffectU addr [] [] [(addr, n)] [] []).
  eapply (rz_silent_cfg cfg segs (mkCfg ms model) unit
            (fun _ => mkCfg (advance_past_svc (apply_effect ms eff1)) (with_mmap_backing flags addr n (noaccess_model addr n model))) KB tt).
  - apply (node_chk_grant_cfg cfg segs ms model (getr regs 17) unit (fun _ => eff1) (fun _ => with_mmap_backing flags addr n (noaccess_model addr n model))
             (fun _ => []) tt Hh eq_refl (injected_family_off_mmap cfg ALLOC_OFF _ Hsys)).
    + intros []. cbv beta delta [eff1]. rewrite Hchk. cbv beta iota. rewrite Hna, bv_eqb_refl, (proj2 (listNN_eqb_eq _ _) eq_refl). reflexivity.
    + intros []. cbv beta delta [eff_ret eff1]. rewrite (refusal_b_mmap _ _ _ Hsys). exact Hna.
    + intros [r ws zs us cs ci] m' evs Hc Hr. rewrite (refusal_b_mmap _ _ _ Hsys) in Hr. cbn [eff_ret] in Hr. rewrite Hchk in Hc.
      destruct ws; [|discriminate]. destruct zs; [|discriminate].
      destruct cs; [|destruct us; discriminate]. destruct ci; [|destruct us; discriminate].
      rewrite Hr in Hc. destruct (bv_eqb r addr) eqn:Eb; [|discriminate].
      destruct (listNN_eqb us [(addr, n)]) eqn:Hl; [|discriminate].
      apply bv_eqb_eq in Eb. apply listNN_eqb_eq in Hl. subst r us. cbn [andb] in Hc. injection Hc as <- <-.
      exists tt. repeat split; reflexivity.
    + intros [r ws zs us cs ci] m' evs Hc Hr. rewrite (refusal_b_mmap _ _ _ Hsys) in Hr. cbn [eff_ret] in Hr. rewrite Hchk in Hc.
      destruct ws; [|discriminate]. destruct zs; [|discriminate].
      destruct cs; [|destruct us; discriminate]. destruct ci; [|destruct us; discriminate].
      rewrite Hr in Hc. destruct us; [|discriminate]. injection Hc as <- <-. exact Hh.
    + intros [r ws zs us cs ci] Hc. rewrite Hchk in Hc.
      destruct ws; [|discriminate]. destruct zs; [|discriminate].
      destruct cs; [|destruct us; discriminate]. destruct ci; [|destruct us; discriminate].
      destruct (errno_ret_in mmap_errnos r); [destruct us; discriminate|].
      destruct (bv_eqb r addr && listNN_eqb us [(addr, n)])%bool; discriminate.
    + intros []. rewrite with_mmap_backing_halted. unfold noaccess_model. rewrite with_vmmaps_halted. exact Hh.
    + intros []. reflexivity.
  - intros []. cbv beta delta [eff1]. unfold ms. rewrite adv_unmaps1_epend. exact HB.
Qed.

(* [comment removed for export] *)

Lemma crz_mprotect1 : forall regs (pc : word) mem rom model w (addr : word) (len : Z) KB,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None ->
  getr regs 17 = Z_to_bv 64 226 ->
  getr regs 10 = addr -> (bv_unsigned addr mod page_size = 0)%Z ->
  getr regs 11 = Z_to_bv 64 len -> (0 < len)%Z ->
  (bv_unsigned addr + page_round_up_Z len < two_pow_64)%Z ->
  getr regs 12 = Z_to_bv 64 3 ->
  let n := Z_to_bv 64 (page_round_up_Z len) in
  map_contains (vm_noaccess (m_vmmaps model)) addr n = true ->
  map_contains (vm_maps (m_vmmaps model)) addr n = true ->
  mprotect_budget_ok model addr n = true ->
  RZ (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 0)) (v_addi pc 4) (zfill addr n mem) rom)
          (mprotect_model addr n model)) KB ->
  RZ (mkCfg (mkst regs pc mem rom) model) KB.
Proof.
  intros regs pc mem rom model w addr len KB HF HE Hh H17 H10 Hal H11 Hlen Hnw H12 n Hna Hma Hbud HB.
  eapply (rz_sys_lazy_cfg cfg segs); [exact Hh | exact HF | exact HE |].
  set (ms := epend regs pc mem rom (getr regs 17)).
  assert (Hno : bv_unsigned (getr regs 17) = 226%Z) by (rewrite H17; apply u64_lit; lia).
  assert (Hsys : bv_unsigned (in_sysno (sys_input segs ms (getr regs 17))) = 226) by (rewrite in_sysno_sys_input; exact Hno).
  pose proof (fun eff => mprotect_check segs ms (getr regs 17) model eff addr len Hno
                           ltac:(unfold ms; rewrite ms_gpr_epend0; exact H10) Hal
                           ltac:(unfold ms; rewrite ms_gpr_epend1; exact H11) Hlen Hnw
                           ltac:(unfold ms; rewrite ms_gpr_epend2; exact H12) Hna Hma) as Hchk.
  cbv zeta in Hchk. fold n in Hchk. rewrite Hbud in Hchk.
  pose (eff1 := mkEffectU (Z_to_bv 64 0) [] [(addr, n)] [] [] []).
  assert (Hz : errno_ret_in mprotect_errnos (Z_to_bv 64 0) = false) by reflexivity.
  eapply (rz_silent_cfg cfg segs (mkCfg ms model) unit
            (fun _ => mkCfg (advance_past_svc (apply_effect ms eff1)) (mprotect_model addr n model)) KB tt).
  - apply (node_chk_grant_cfg cfg segs ms model (getr regs 17) unit (fun _ => eff1) (fun _ => mprotect_model addr n model)
             (fun _ => []) tt Hh eq_refl (injected_family_off_mprotect _ Hsys)).
    + intros []. cbv beta delta [eff1]. rewrite Hchk. cbv beta iota. rewrite Hz. unfold w_is0. rewrite bv_eqb_refl, (proj2 (listNN_eqb_eq _ _) eq_refl). reflexivity.
    + intros []. cbv beta delta [eff_ret eff1]. rewrite (refusal_b_mprotect _ _ _ Hsys). exact Hz.
    + intros [r ws zs us cs ci] m' evs Hc Hr. rewrite (refusal_b_mprotect _ _ _ Hsys) in Hr. cbn [eff_ret] in Hr. rewrite Hchk in Hc.
      destruct ws; [|discriminate]. destruct us; [|discriminate].
      destruct cs; [|discriminate]. destruct ci; [|discriminate].
      rewrite Hr in Hc. cbn [andb] in Hc. destruct (w_is0 r) eqn:E0; [|discriminate].
      destruct (listNN_eqb zs [(addr, n)]) eqn:Hl; [|discriminate].
      apply listNN_eqb_eq in Hl. subst zs. injection Hc as <- <-.
      unfold w_is0 in E0. apply bv_eqb_eq in E0. subst r. exists tt. repeat split; reflexivity.
    + intros [r ws zs us cs ci] m' evs Hc Hr. rewrite (refusal_b_mprotect _ _ _ Hsys) in Hr. cbn [eff_ret] in Hr. rewrite Hchk in Hc.
      destruct ws; [|discriminate]. destruct us; [|discriminate].
      destruct cs; [|discriminate]. destruct ci; [|discriminate].
      rewrite Hr in Hc. destruct zs; [|discriminate]. injection Hc as <- <-. exact Hh.
    + intros [r ws zs us cs ci] Hc. rewrite Hchk in Hc.
      destruct ws; [|discriminate]. destruct us; [|discriminate].
      destruct cs; [|discriminate]. destruct ci; [|discriminate].
      destruct (errno_ret_in mprotect_errnos r); [destruct zs; discriminate|].
      cbn [andb] in Hc. destruct (w_is0 r && listNN_eqb zs [(addr, n)])%bool; discriminate.
    + intros []. unfold mprotect_model. rewrite with_vmmaps_halted. exact Hh.
    + intros []. reflexivity.
  - intros []. cbv beta delta [eff1]. unfold ms. rewrite adv_zeros1_epend. exact HB.
Qed.


(* [comment removed for export] *)

Lemma mmap_flags_core_104022 : mmap_flags_core (Z_to_bv 64 1064994) = 1048610%Z. Proof. vm_compute. reflexivity. Qed.
Lemma mmap_noreserve_b_104022 : mmap_noreserve_b (Z_to_bv 64 1064994) = true. Proof. vm_compute. reflexivity. Qed.
Lemma mmap_gates_core_noreplace : forall flags prot,
  mmap_flags_core flags = 1048610%Z ->
  mmap_modeled_b prot flags (Z_to_bv 64 0) = false
  /\ mmap_noaccess_b prot flags (Z_to_bv 64 0) = false
  /\ mmap_fixed_noaccess_b prot flags (Z_to_bv 64 0) = false
  /\ mmap_fixed_rw_b prot flags (Z_to_bv 64 0) = false
  /\ mmap_noreplace_noaccess_b (Z_to_bv 64 0) flags (Z_to_bv 64 0) = true
  /\ mmap_noreplace_noaccess_b (Z_to_bv 64 3) flags (Z_to_bv 64 0) = false
  /\ mmap_noreplace_rw_b (Z_to_bv 64 3) flags (Z_to_bv 64 0) = true
  /\ mmap_noreplace_rw_b (Z_to_bv 64 0) flags (Z_to_bv 64 0) = false.
Proof.
  intros flags prot Hc. unfold mmap_modeled_b, mmap_noaccess_b, mmap_fixed_noaccess_b, mmap_fixed_rw_b, mmap_noreplace_noaccess_b, mmap_noreplace_rw_b, mmap_noreplace_flags_b.
  rewrite Hc. repeat split; try (vm_compute; reflexivity).
  all: destruct (bv_unsigned prot =? _)%Z; vm_compute; reflexivity.
Qed.

Lemma mmap_noreplace_check : forall ms x8 model eff (prot : Z) flags (addr : word) (len : Z),
  bv_unsigned x8 = 222%Z -> (prot = 0 \/ prot = 3)%Z ->
  ms_gpr ms 0 = addr -> (bv_unsigned addr mod page_size = 0)%Z -> (0 < bv_unsigned addr)%Z ->
  ms_gpr ms 1 = Z_to_bv 64 len -> (0 < len)%Z ->
  (bv_unsigned addr + page_round_up_Z len <= alloc_ceiling)%Z -> init_sp_ok (m_vmmaps model) ->
  ms_gpr ms 2 = Z_to_bv 64 prot -> ms_gpr ms 3 = flags -> mmap_flags_core flags = 1048610%Z ->
  ms_gpr ms 4 = Z_to_bv 64 (-1) -> ms_gpr ms 5 = Z_to_bv 64 0 ->
  let nZ := page_round_up_Z len in let n := Z_to_bv 64 nZ in
  region_free (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model)) addr n = true ->
  check_syscall (sys_input segs ms x8) eff model
  = if Z.eqb prot 0 then
      match eff with
      | mkEffectU r [] [] us [] [] =>
          if errno_ret_in mmap_errnos r
          then match us with [] => CheckOk model [] | _ => CheckReject end
          else if bv_eqb r addr && listNN_eqb us [(addr, n)]
          then CheckOk (with_mmap_backing flags addr n (noaccess_model addr n model)) []
          else CheckReject
      | _ => CheckReject
      end
    else
      match eff with
      | mkEffectU r [] zs [] [] [] =>
          if errno_ret_in mmap_errnos r
          then match zs with [] => CheckOk model [] | _ => CheckReject end
          else if bv_eqb r addr && listNN_eqb zs [(addr, n)] && mmap_noreserve_backed_ok flags model nZ
          then CheckOk (with_mmap_backing flags addr n (mmap_model addr n model)) []
          else CheckReject
      | _ => CheckReject
      end.
Proof.
  intros ms x8 model eff prot flags addr len Hno Hprot H0 Hal Hpos H1 Hlen Hce Hisp H2 H3 Hcore H4 H5 nZ n Hrf.
  destruct (mmap_fixed_gate_open (m_vmmaps model) addr len Hal Hpos Hlen Hce Hisp) as (G1 & G2 & G3 & G4 & Hlen' & HnZ).
  destruct (mmap_gates_core_noreplace flags (Z_to_bv 64 prot) Hcore) as (Gm & Gn & Gfn & Gfr & N0 & N3 & R3 & R0).
  assert (Hu1 : bv_unsigned (ms_gpr ms 1) = len) by (rewrite H1; apply u64_lit; lia).
  assert (E1 : w_is0 (ms_gpr ms 1) = false).
  { unfold w_is0. apply bv_eqb_neq. intros E. apply (f_equal bv_unsigned) in E.
    rewrite Hu1 in E. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in E. lia. }
  rewrite (mmap_check segs ms x8 model eff Hno). unfold check_mmap.
  rewrite E1, H2, H3, H5, H0, Hu1, mmap_off_aligned_b_0, (mmap_anon_b_of_core flags _ Hcore eq_refl), Gm, Gn, Gfn, Gfr. cbn [negb]. cbv beta iota zeta.
  destruct Hprot as [-> | ->].
  - rewrite N0. cbv beta iota zeta. rewrite G1, G2, G3, G4. fold nZ. fold n. rewrite Hrf. cbn [Z.eqb].
    destruct eff as [r ws zs us cs ci]. destruct ws; [|reflexivity].
    destruct zs; [|destruct (errno_ret_in mmap_errnos r); reflexivity].
    destruct cs; [|destruct (errno_ret_in mmap_errnos r); destruct us; reflexivity]. destruct ci; [|destruct (errno_ret_in mmap_errnos r); destruct us; reflexivity].
    unfold noaccess_model. reflexivity.
  - rewrite N3, R3. cbv beta iota zeta. rewrite G1, G2, G3, G4. fold nZ. fold n. rewrite Hrf. cbn [Z.eqb Pos.eqb].
    destruct eff as [r ws zs us cs ci]. destruct ws; [|reflexivity].
    destruct us; [|destruct (errno_ret_in mmap_errnos r); [destruct zs|]; reflexivity].
    destruct cs; [|reflexivity]. destruct ci; [|reflexivity].
    unfold mmap_model. reflexivity.
Qed.


Lemma crz_mmap_noreplace_rw1 : forall regs (pc : word) mem rom model w (addr : word) (len : Z) (flags : word) KB,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None ->
  getr regs 17 = Z_to_bv 64 222 ->
  getr regs 10 = addr -> (bv_unsigned addr mod page_size = 0)%Z -> (0 < bv_unsigned addr)%Z ->
  getr regs 11 = Z_to_bv 64 len -> (0 < len)%Z ->
  (bv_unsigned addr + page_round_up_Z len <= alloc_ceiling)%Z -> init_sp_ok (m_vmmaps model) ->
  getr regs 12 = Z_to_bv 64 3 -> getr regs 13 = flags -> mmap_flags_core flags = 1048610%Z ->
  getr regs 14 = Z_to_bv 64 (-1) -> getr regs 15 = Z_to_bv 64 0 ->
  let nZ := page_round_up_Z len in let n := Z_to_bv 64 nZ in
  region_free (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model)) addr n = true ->
  mmap_noreserve_backed_ok flags model nZ = true ->
  RZ (mkCfg (mkst (regupd regs 10 addr) (v_addi pc 4) (zfill addr n mem) rom)
          (with_mmap_backing flags addr n (mmap_model addr n model))) KB ->
  RZ (mkCfg (mkst regs pc mem rom) model) KB.
Proof.
  intros regs pc mem rom model w addr len flags KB HF HE Hh H17 H10 Hal Hpos H11 Hlen Hce Hisp H12 H13 Hcore H14 H15
         nZ n Hrf Hbk HB.
  eapply (rz_sys_lazy_cfg cfg segs); [exact Hh | exact HF | exact HE |].
  set (ms := epend regs pc mem rom (getr regs 17)).
  assert (Hno : bv_unsigned (getr regs 17) = 222%Z) by (rewrite H17; apply u64_lit; lia).
  assert (Hsys : bv_unsigned (in_sysno (sys_input segs ms (getr regs 17))) = 222) by (rewrite in_sysno_sys_input; exact Hno).
  pose proof (fun eff => mmap_noreplace_check ms (getr regs 17) model eff 3 flags addr len Hno ltac:(right; reflexivity)
                ltac:(unfold ms; rewrite ms_gpr_epend0; exact H10) Hal Hpos
                ltac:(unfold ms; rewrite ms_gpr_epend1; exact H11) Hlen Hce Hisp
                ltac:(unfold ms; rewrite ms_gpr_epend2; exact H12)
                ltac:(unfold ms; rewrite ms_gpr_epend3; exact H13) Hcore
                ltac:(unfold ms; rewrite ms_gpr_epend4; exact H14)
                ltac:(unfold ms; rewrite ms_gpr_epend5; exact H15) Hrf) as Hchk.
  cbv zeta in Hchk. cbn [Z.eqb Pos.eqb] in Hchk. fold nZ in Hchk. fold n in Hchk. rewrite Hbk in Hchk.
  pose proof (addr_below_ceiling_not_errno addr len Hlen Hce) as Hna.
  pose (eff1 := mkEffectU addr [] [(addr, n)] [] [] []).
  eapply (rz_silent_cfg cfg segs (mkCfg ms model) unit
            (fun _ => mkCfg (advance_past_svc (apply_effect ms eff1)) (with_mmap_backing flags addr n (mmap_model addr n model))) KB tt).
  - apply (node_chk_grant_cfg cfg segs ms model (getr regs 17) unit (fun _ => eff1) (fun _ => with_mmap_backing flags addr n (mmap_model addr n model))
             (fun _ => []) tt Hh eq_refl (injected_family_off_mmap cfg ALLOC_OFF _ Hsys)).
    + intros []. cbv beta delta [eff1]. rewrite Hchk. cbv beta iota. rewrite Hna, bv_eqb_refl, (proj2 (listNN_eqb_eq _ _) eq_refl). reflexivity.
    + intros []. cbv beta delta [eff_ret eff1]. rewrite (refusal_b_mmap _ _ _ Hsys). exact Hna.
    + intros [r ws zs us cs ci] m' evs Hc Hr. rewrite (refusal_b_mmap _ _ _ Hsys) in Hr. cbn [eff_ret] in Hr. rewrite Hchk in Hc.
      destruct ws; [|discriminate]. destruct us; [|destruct zs; discriminate].
      destruct cs; [|destruct zs; discriminate]. destruct ci; [|destruct zs; discriminate].
      rewrite Hr in Hc. destruct (bv_eqb r addr) eqn:Eb; [|discriminate].
      destruct (listNN_eqb zs [(addr, n)]) eqn:Hl; [|discriminate].
      apply bv_eqb_eq in Eb. apply listNN_eqb_eq in Hl. subst r zs. cbn [andb] in Hc. injection Hc as <- <-.
      exists tt. repeat split; reflexivity.
    + intros [r ws zs us cs ci] m' evs Hc Hr. rewrite (refusal_b_mmap _ _ _ Hsys) in Hr. cbn [eff_ret] in Hr. rewrite Hchk in Hc.
      destruct ws; [|discriminate]. destruct us; [|destruct zs; discriminate].
      destruct cs; [|destruct zs; discriminate]. destruct ci; [|destruct zs; discriminate].
      rewrite Hr in Hc. destruct zs; [|discriminate]. injection Hc as <- <-. exact Hh.
    + intros [r ws zs us cs ci] Hc. rewrite Hchk in Hc.
      destruct ws; [|discriminate]. destruct us; [|destruct zs; discriminate].
      destruct cs; [|destruct zs; discriminate]. destruct ci; [|destruct zs; discriminate].
      destruct (errno_ret_in mmap_errnos r); [destruct zs; discriminate|].
      destruct (bv_eqb r addr && listNN_eqb zs [(addr, n)] && true)%bool; discriminate.
    + intros []. rewrite with_mmap_backing_halted. unfold mmap_model. rewrite with_vmmaps_halted. exact Hh.
    + intros []. reflexivity.
  - intros []. cbv beta delta [eff1]. unfold ms. rewrite adv_zeros1_epend. exact HB.
Qed.

Lemma crz_mmap_noreplace_none1 : forall regs (pc : word) mem rom model w (addr : word) (len : Z) (flags : word) KB,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None ->
  getr regs 17 = Z_to_bv 64 222 ->
  getr regs 10 = addr -> (bv_unsigned addr mod page_size = 0)%Z -> (0 < bv_unsigned addr)%Z ->
  getr regs 11 = Z_to_bv 64 len -> (0 < len)%Z ->
  (bv_unsigned addr + page_round_up_Z len <= alloc_ceiling)%Z -> init_sp_ok (m_vmmaps model) ->
  getr regs 12 = Z_to_bv 64 0 -> getr regs 13 = flags -> mmap_flags_core flags = 1048610%Z ->
  getr regs 14 = Z_to_bv 64 (-1) -> getr regs 15 = Z_to_bv 64 0 ->
  let nZ := page_round_up_Z len in let n := Z_to_bv 64 nZ in
  region_free (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model)) addr n = true ->
  RZ (mkCfg (mkst (regupd regs 10 addr) (v_addi pc 4) (unfill addr n mem) rom)
          (with_mmap_backing flags addr n (noaccess_model addr n model))) KB ->
  RZ (mkCfg (mkst regs pc mem rom) model) KB.
Proof.
  intros regs pc mem rom model w addr len flags KB HF HE Hh H17 H10 Hal Hpos H11 Hlen Hce Hisp H12 H13 Hcore H14 H15
         nZ n Hrf HB.
  eapply (rz_sys_lazy_cfg cfg segs); [exact Hh | exact HF | exact HE |].
  set (ms := epend regs pc mem rom (getr regs 17)).
  assert (Hno : bv_unsigned (getr regs 17) = 222%Z) by (rewrite H17; apply u64_lit; lia).
  assert (Hsys : bv_unsigned (in_sysno (sys_input segs ms (getr regs 17))) = 222) by (rewrite in_sysno_sys_input; exact Hno).
  pose proof (fun eff => mmap_noreplace_check ms (getr regs 17) model eff 0 flags addr len Hno ltac:(left; reflexivity)
                ltac:(unfold ms; rewrite ms_gpr_epend0; exact H10) Hal Hpos
                ltac:(unfold ms; rewrite ms_gpr_epend1; exact H11) Hlen Hce Hisp
                ltac:(unfold ms; rewrite ms_gpr_epend2; exact H12)
                ltac:(unfold ms; rewrite ms_gpr_epend3; exact H13) Hcore
                ltac:(unfold ms; rewrite ms_gpr_epend4; exact H14)
                ltac:(unfold ms; rewrite ms_gpr_epend5; exact H15) Hrf) as Hchk.
  cbv zeta in Hchk. cbn [Z.eqb Pos.eqb] in Hchk. fold nZ in Hchk. fold n in Hchk.
  pose proof (addr_below_ceiling_not_errno addr len Hlen Hce) as Hna.
  pose (eff1 := mkEffectU addr [] [] [(addr, n)] [] []).
  eapply (rz_silent_cfg cfg segs (mkCfg ms model) unit
            (fun _ => mkCfg (advance_past_svc (apply_effect ms eff1)) (with_mmap_backing flags addr n (noaccess_model addr n model))) KB tt).
  - apply (node_chk_grant_cfg cfg segs ms model (getr regs 17) unit (fun _ => eff1) (fun _ => with_mmap_backing flags addr n (noaccess_model addr n model))
             (fun _ => []) tt Hh eq_refl (injected_family_off_mmap cfg ALLOC_OFF _ Hsys)).
    + intros []. cbv beta delta [eff1]. rewrite Hchk. cbv beta iota. rewrite Hna, bv_eqb_refl, (proj2 (listNN_eqb_eq _ _) eq_refl). reflexivity.
    + intros []. cbv beta delta [eff_ret eff1]. rewrite (refusal_b_mmap _ _ _ Hsys). exact Hna.
    + intros [r ws zs us cs ci] m' evs Hc Hr. rewrite (refusal_b_mmap _ _ _ Hsys) in Hr. cbn [eff_ret] in Hr. rewrite Hchk in Hc.
      destruct ws; [|discriminate]. destruct zs; [|discriminate].
      destruct cs; [|destruct us; discriminate]. destruct ci; [|destruct us; discriminate].
      rewrite Hr in Hc. destruct (bv_eqb r addr) eqn:Eb; [|discriminate].
      destruct (listNN_eqb us [(addr, n)]) eqn:Hl; [|discriminate].
      apply bv_eqb_eq in Eb. apply listNN_eqb_eq in Hl. subst r us. cbn [andb] in Hc. injection Hc as <- <-.
      exists tt. repeat split; reflexivity.
    + intros [r ws zs us cs ci] m' evs Hc Hr. rewrite (refusal_b_mmap _ _ _ Hsys) in Hr. cbn [eff_ret] in Hr. rewrite Hchk in Hc.
      destruct ws; [|discriminate]. destruct zs; [|discriminate].
      destruct cs; [|destruct us; discriminate]. destruct ci; [|destruct us; discriminate].
      rewrite Hr in Hc. destruct us; [|discriminate]. injection Hc as <- <-. exact Hh.
    + intros [r ws zs us cs ci] Hc. rewrite Hchk in Hc.
      destruct ws; [|discriminate]. destruct zs; [|discriminate].
      destruct cs; [|destruct us; discriminate]. destruct ci; [|destruct us; discriminate].
      destruct (errno_ret_in mmap_errnos r); [destruct us; discriminate|].
      destruct (bv_eqb r addr && listNN_eqb us [(addr, n)])%bool; discriminate.
    + intros []. rewrite with_mmap_backing_halted. unfold noaccess_model. rewrite with_vmmaps_halted. exact Hh.
    + intros []. reflexivity.
  - intros []. cbv beta delta [eff1]. unfold ms. rewrite adv_unmaps1_epend. exact HB.
Qed.

(* [comment removed for export] *)
Lemma crz_mmap_fixedin1 : forall regs (pc : word) mem rom model w (prot : Z) (flags addr : word) (len : Z) KB,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None ->
  getr regs 17 = Z_to_bv 64 222 ->
  (prot = 0 \/ prot = 3)%Z -> mmap_flags_core flags = 50%Z ->
  getr regs 10 = addr -> (bv_unsigned addr mod page_size = 0)%Z -> (0 < bv_unsigned addr)%Z ->
  getr regs 11 = Z_to_bv 64 len -> (0 < len)%Z ->
  (bv_unsigned addr + page_round_up_Z len <= alloc_ceiling)%Z -> init_sp_ok (m_vmmaps model) ->
  getr regs 12 = Z_to_bv 64 prot -> getr regs 13 = flags ->
  getr regs 14 = Z_to_bv 64 (-1) -> getr regs 15 = Z_to_bv 64 0 ->
  let n := Z_to_bv 64 (page_round_up_Z len) in
  region_free (vm_reserved (m_vmmaps model)) addr n = true ->
  map_contains (vm_maps (m_vmmaps model)) addr n = true ->
  (prot = 3%Z -> mmap_fixed_rw_budget_ok flags model addr n = true) ->
  RZ (mkCfg (mkst (regupd regs 10 addr) (v_addi pc 4)
                 (if Z.eqb prot 0 then unfill addr n mem else zfill addr n mem) rom)
          (fixedin_ok_model prot flags addr n model)) KB ->
  RZ (mkCfg (mkst regs pc mem rom) model) KB.
Proof.
  intros regs pc mem rom model w prot flags addr len KB HF HE Hh H17 Hprot Hcore H10 Hal Hpos H11 Hlen Hce Hisp H12 H13 H14 H15 n Hrf Hmc Hbud HB.
  pose proof alloc_ceiling_val as Hcv. pose proof (u64_range addr) as Har.
  eapply (rz_sys_lazy_cfg cfg segs); [exact Hh | exact HF | exact HE |].
  set (ms := epend regs pc mem rom (getr regs 17)).
  assert (Hno : bv_unsigned (getr regs 17) = 222%Z) by (rewrite H17; apply u64_lit; lia).
  assert (Hsys : bv_unsigned (in_sysno (sys_input segs ms (getr regs 17))) = 222) by (rewrite in_sysno_sys_input; exact Hno).
  assert (Hlen' : (len < 2 ^ 64)%Z) by (pose proof (page_round_up_Z_bounds len ltac:(lia)); lia).
  pose proof (fun eff => mmap_fixedin_check segs ms (getr regs 17) model eff prot flags addr len Hno Hprot Hcore
                           ltac:(unfold ms; rewrite ms_gpr_epend0; exact H10) Hal Hpos
                           ltac:(unfold ms; rewrite ms_gpr_epend1; exact H11) Hlen
                           ltac:(unfold ms; rewrite ms_gpr_epend2; exact H12)
                           ltac:(unfold ms; rewrite ms_gpr_epend3; exact H13)
                           ltac:(unfold ms; rewrite ms_gpr_epend4; exact H14)
                           ltac:(unfold ms; rewrite ms_gpr_epend5; exact H15)
                           Hce Hisp Hrf Hmc Hbud) as Hchk.
  cbv zeta in Hchk. fold n in Hchk.
  pose proof (addr_below_ceiling_not_errno addr len Hlen Hce) as Haddr_ne.
  assert (Hp0 : Z.eqb prot 0 = true <-> prot = 0%Z) by (apply Z.eqb_eq).
  eapply (rz_silent_cfg cfg segs (mkCfg ms model) unit
            (fun _ => mkCfg (advance_past_svc (apply_effect ms (fixedin_ok_eff prot addr n))) (fixedin_ok_model prot flags addr n model)) KB tt).
  - apply (node_chk_grant_cfg cfg segs ms model (getr regs 17) unit (fun _ => fixedin_ok_eff prot addr n) (fun _ => fixedin_ok_model prot flags addr n model)
             (fun _ => []) tt Hh eq_refl (injected_family_off_mmap cfg ALLOC_OFF _ Hsys)).
    + intros []. cbv beta. unfold fixedin_ok_eff. destruct (Z.eqb prot 0) eqn:Ep; rewrite Hchk; cbv beta iota; rewrite Haddr_ne, ?Ep, bv_eqb_refl, (proj2 (listNN_eqb_eq _ _) eq_refl); reflexivity.
    + intros []. cbv beta. rewrite (refusal_b_mmap _ _ _ Hsys). unfold fixedin_ok_eff. destruct (Z.eqb prot 0); cbn [eff_ret]; exact Haddr_ne.
    + intros [r ws zs us cs ci] m' evs Hc Hr. rewrite (refusal_b_mmap _ _ _ Hsys) in Hr. cbn [eff_ret] in Hr. rewrite Hchk in Hc.
      destruct ws; [|discriminate]. destruct cs; [|discriminate]. destruct ci; [|discriminate].
      rewrite Hr in Hc.
      destruct (Z.eqb prot 0) eqn:Ep.
      * destruct zs; [|discriminate].
        destruct (bv_eqb r addr) eqn:Eb; [|discriminate].
        destruct (listNN_eqb us [(addr, n)]) eqn:Hl; [|discriminate].
        apply bv_eqb_eq in Eb. apply listNN_eqb_eq in Hl. subst. cbn [andb] in Hc. injection Hc as <- <-.
        exists tt. unfold fixedin_ok_eff. rewrite Ep. repeat split; reflexivity.
      * destruct us; [|discriminate].
        destruct (bv_eqb r addr) eqn:Eb; [|discriminate].
        destruct (listNN_eqb zs [(addr, n)]) eqn:Hl; [|discriminate].
        apply bv_eqb_eq in Eb. apply listNN_eqb_eq in Hl. subst. cbn [andb] in Hc. injection Hc as <- <-.
        exists tt. unfold fixedin_ok_eff. rewrite Ep. repeat split; reflexivity.
    + intros [r ws zs us cs ci] m' evs Hc Hr. rewrite (refusal_b_mmap _ _ _ Hsys) in Hr. cbn [eff_ret] in Hr. rewrite Hchk in Hc.
      destruct ws; [|discriminate]. destruct cs; [|discriminate]. destruct ci; [|discriminate].
      rewrite Hr in Hc. destruct zs; [|discriminate]. destruct us.
      * injection Hc as <- <-. exact Hh.
      * destruct (listNN_eqb (p :: us) [(addr, n)]); [|discriminate]. injection Hc as <- <-.
        unfold fixedin_destroyed_model. rewrite with_mmap_destroyed_halted'. cbn. exact Hh.
    + intros [r ws zs us cs ci] Hc. rewrite Hchk in Hc.
      destruct ws; [|discriminate]. destruct cs; [|discriminate]. destruct ci; [|discriminate].
      destruct (errno_ret_in mmap_errnos r); [destruct zs; [|discriminate]; destruct us; [discriminate|]; destruct (listNN_eqb _ _); discriminate|].
      destruct (Z.eqb prot 0); [destruct zs; [|discriminate] | destruct us; [|discriminate]];
        destruct (bv_eqb r addr && listNN_eqb _ _)%bool; discriminate.
    + intros []. unfold fixedin_ok_model. rewrite with_mmap_replacement_halted', with_vmmaps_halted. exact Hh.
    + intros []. unfold fixedin_ok_eff. destruct (Z.eqb prot 0); reflexivity.
  - intros []. cbv beta. unfold ms, fixedin_ok_eff. destruct (Z.eqb prot 0).
    + rewrite adv_unmaps1_epend. exact HB.
    + rewrite adv_zeros1_epend. exact HB.
Qed.

(* [comment removed for export] *)
Lemma mmap_fixedin_check_top : forall ms x8 model eff (prot : Z) (flags addr : word) (len : Z),
  bv_unsigned x8 = 222%Z ->
  (prot = 0 \/ prot = 3)%Z ->
  mmap_flags_core flags = 50%Z ->
  ms_gpr ms 0 = addr -> (bv_unsigned addr mod page_size = 0)%Z -> (0 < bv_unsigned addr)%Z ->
  ms_gpr ms 1 = Z_to_bv 64 len -> (0 < len)%Z ->
  ms_gpr ms 2 = Z_to_bv 64 prot -> ms_gpr ms 3 = flags ->
  ms_gpr ms 4 = Z_to_bv 64 (-1) -> ms_gpr ms 5 = Z_to_bv 64 0 ->
  (bv_unsigned addr + page_round_up_Z len <= alloc_top (m_vmmaps model))%Z ->   (* [comment removed for export] *)
  let n := Z_to_bv 64 (page_round_up_Z len) in
  region_free (vm_reserved (m_vmmaps model)) addr n = true ->
  map_contains (vm_maps (m_vmmaps model)) addr n = true ->
  (prot = 3%Z -> mmap_fixed_rw_budget_ok flags model addr n = true) ->
  check_syscall (sys_input segs ms x8) eff model
  = match eff with
    | mkEffectU r [] zs us [] [] =>
        if errno_ret_in mmap_errnos r
        then match zs, us with
             | [], [] => CheckOk model []
             | [], _ => if listNN_eqb us [(addr, n)]
                        then CheckOk (fixedin_destroyed_model addr n model) []
                        else CheckReject
             | _, _ => CheckReject
             end
        else if (Z.eqb prot 0)
             then match zs with
                  | [] => if bv_eqb r addr && listNN_eqb us [(addr, n)]
                          then CheckOk (fixedin_ok_model prot flags addr n model) []
                          else CheckReject
                  | _ => CheckReject
                  end
             else match us with
                  | [] => if bv_eqb r addr && listNN_eqb zs [(addr, n)]
                          then CheckOk (fixedin_ok_model prot flags addr n model) []
                          else CheckReject
                  | _ => CheckReject
                  end
    | _ => CheckReject
    end.
Proof.
  intros ms x8 model eff prot flags addr len Hno Hprot Hcore H0 Hal Hpos H1 Hlen H2 H3 H4 H5 Htop n Hrf Hmc Hbud.
  pose proof (alloc_top_lt (m_vmmaps model)) as Htl. unfold two_pow_64 in Htl.
    assert (Hlen' : (len < 2 ^ 64)%Z).
  { pose proof (page_round_up_Z_bounds len ltac:(lia)). pose proof (u64_range addr). lia. }
  assert (Hu1 : bv_unsigned (ms_gpr ms 1) = len) by (rewrite H1; apply u64_lit; lia).
  rewrite (mmap_check segs ms x8 model eff Hno). unfold check_mmap.
  assert (E1 : w_is0 (ms_gpr ms 1) = false).
  { unfold w_is0. apply bv_eqb_neq. intros Hz. rewrite Hz in Hu1. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in Hu1. lia. }
  rewrite E1, H2, H3, H5, H0, Hu1.
  destruct (mmap_gates_core50 flags (Z_to_bv 64 prot) Hcore) as (G1 & G2 & G3 & G4 & G5).
  rewrite G1, G2, mmap_off_aligned_b_0, (mmap_anon_b_of_core flags _ Hcore eq_refl). cbn [negb].
  pose proof (u64_range addr) as Har.
  destruct Hprot as [-> | ->].
  - (* [comment removed for export] *)
    rewrite G3. cbv beta iota zeta.
    rewrite (proj2 (Z.leb_gt _ _)) by (unfold two_pow_64; lia).
    rewrite (proj2 (Z.leb_le _ _) Htop). cbn [negb].
    rewrite (proj2 (Z.eqb_eq _ _) Hal). cbn [negb].
    rewrite (proj2 (Z.ltb_lt _ _) Hpos). cbn [negb]. fold n. rewrite Hrf, Hmc. cbn [andb Z.eqb].
    destruct eff as [r ws zs us cs ci]. destruct ws; [|reflexivity].
    destruct cs; [|destruct (errno_ret_in mmap_errnos r); destruct zs; destruct us; reflexivity].
    destruct ci; [|destruct (errno_ret_in mmap_errnos r); destruct zs; destruct us; reflexivity].
    destruct zs; [|destruct (errno_ret_in mmap_errnos r); destruct us; reflexivity].
    reflexivity.
  - (* [comment removed for export] *)
    rewrite G4, G5. cbv beta iota zeta.
    rewrite (proj2 (Z.leb_gt _ _)) by (unfold two_pow_64; lia).
    rewrite (proj2 (Z.leb_le _ _) Htop). cbn [negb].
    rewrite (proj2 (Z.eqb_eq _ _) Hal). cbn [negb].
    rewrite (proj2 (Z.ltb_lt _ _) Hpos). cbn [negb]. fold n. rewrite Hrf, Hmc. cbn [andb Z.eqb].
    rewrite (Hbud eq_refl).
    destruct eff as [r ws zs us cs ci]. destruct ws; [|reflexivity].
    destruct cs; [|destruct (errno_ret_in mmap_errnos r); destruct zs; destruct us; reflexivity].
    destruct ci; [|destruct (errno_ret_in mmap_errnos r); destruct zs; destruct us; reflexivity].
    destruct (errno_ret_in mmap_errnos r); [reflexivity|].
    destruct us; [|reflexivity]. rewrite andb_true_r. reflexivity.
Qed.

Lemma crz_mmap_fixedin1_top : forall regs (pc : word) mem rom model w (prot : Z) (flags addr : word) (len : Z) KB,
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
  RZ (mkCfg (mkst (regupd regs 10 addr) (v_addi pc 4)
                 (if Z.eqb prot 0 then unfill addr n mem else zfill addr n mem) rom)
          (fixedin_ok_model prot flags addr n model)) KB ->
  RZ (mkCfg (mkst regs pc mem rom) model) KB.
Proof.
  intros regs pc mem rom model w prot flags addr len KB HF HE Hh H17 Hprot Hcore H10 Hal Hpos H11 Hlen Htop H12 H13 H14 H15 n Hrf Hmc Hbud HB.
  pose proof (alloc_top_lt (m_vmmaps model)) as Htl. unfold two_pow_64 in Htl.
  pose proof (u64_range addr) as Har.
  eapply (rz_sys_lazy_cfg cfg segs); [exact Hh | exact HF | exact HE |].
  set (ms := epend regs pc mem rom (getr regs 17)).
  assert (Hno : bv_unsigned (getr regs 17) = 222%Z) by (rewrite H17; apply u64_lit; lia).
  assert (Hsys : bv_unsigned (in_sysno (sys_input segs ms (getr regs 17))) = 222) by (rewrite in_sysno_sys_input; exact Hno).
  assert (Hlen' : (len < 2 ^ 64)%Z) by (pose proof (page_round_up_Z_bounds len ltac:(lia)); lia).
  pose proof (fun eff => mmap_fixedin_check_top ms (getr regs 17) model eff prot flags addr len Hno Hprot Hcore
                           ltac:(unfold ms; rewrite ms_gpr_epend0; exact H10) Hal Hpos
                           ltac:(unfold ms; rewrite ms_gpr_epend1; exact H11) Hlen
                           ltac:(unfold ms; rewrite ms_gpr_epend2; exact H12)
                           ltac:(unfold ms; rewrite ms_gpr_epend3; exact H13)
                           ltac:(unfold ms; rewrite ms_gpr_epend4; exact H14)
                           ltac:(unfold ms; rewrite ms_gpr_epend5; exact H15)
                           Htop Hrf Hmc Hbud) as Hchk.
  cbv zeta in Hchk. fold n in Hchk.
  assert (Haddr_ne : errno_ret_in mmap_errnos addr = false).
  { apply errno_ret_in_below; [reflexivity|]. unfold two_pow_64. pose proof (page_round_up_Z_bounds len ltac:(lia)). pose proof (alloc_top_room (m_vmmaps model)) as Hr. rewrite stack_max_size_val in Hr. unfold two_pow_64 in Hr. lia. }
  assert (Hp0 : Z.eqb prot 0 = true <-> prot = 0%Z) by (apply Z.eqb_eq).
  eapply (rz_silent_cfg cfg segs (mkCfg ms model) unit
            (fun _ => mkCfg (advance_past_svc (apply_effect ms (fixedin_ok_eff prot addr n))) (fixedin_ok_model prot flags addr n model)) KB tt).
  - apply (node_chk_grant_cfg cfg segs ms model (getr regs 17) unit (fun _ => fixedin_ok_eff prot addr n) (fun _ => fixedin_ok_model prot flags addr n model)
             (fun _ => []) tt Hh eq_refl (injected_family_off_mmap cfg ALLOC_OFF _ Hsys)).
    + intros []. cbv beta. unfold fixedin_ok_eff. destruct (Z.eqb prot 0) eqn:Ep; rewrite Hchk; cbv beta iota; rewrite Haddr_ne, ?Ep, bv_eqb_refl, (proj2 (listNN_eqb_eq _ _) eq_refl); reflexivity.
    + intros []. cbv beta. rewrite (refusal_b_mmap _ _ _ Hsys). unfold fixedin_ok_eff. destruct (Z.eqb prot 0); cbn [eff_ret]; exact Haddr_ne.
    + intros [r ws zs us cs ci] m' evs Hc Hr. rewrite (refusal_b_mmap _ _ _ Hsys) in Hr. cbn [eff_ret] in Hr. rewrite Hchk in Hc.
      destruct ws; [|discriminate]. destruct cs; [|discriminate]. destruct ci; [|discriminate].
      rewrite Hr in Hc.
      destruct (Z.eqb prot 0) eqn:Ep.
      * destruct zs; [|discriminate].
        destruct (bv_eqb r addr) eqn:Eb; [|discriminate].
        destruct (listNN_eqb us [(addr, n)]) eqn:Hl; [|discriminate].
        apply bv_eqb_eq in Eb. apply listNN_eqb_eq in Hl. subst. cbn [andb] in Hc. injection Hc as <- <-.
        exists tt. unfold fixedin_ok_eff. rewrite Ep. repeat split; reflexivity.
      * destruct us; [|discriminate].
        destruct (bv_eqb r addr) eqn:Eb; [|discriminate].
        destruct (listNN_eqb zs [(addr, n)]) eqn:Hl; [|discriminate].
        apply bv_eqb_eq in Eb. apply listNN_eqb_eq in Hl. subst. cbn [andb] in Hc. injection Hc as <- <-.
        exists tt. unfold fixedin_ok_eff. rewrite Ep. repeat split; reflexivity.
    + intros [r ws zs us cs ci] m' evs Hc Hr. rewrite (refusal_b_mmap _ _ _ Hsys) in Hr. cbn [eff_ret] in Hr. rewrite Hchk in Hc.
      destruct ws; [|discriminate]. destruct cs; [|discriminate]. destruct ci; [|discriminate].
      rewrite Hr in Hc. destruct zs; [|discriminate]. destruct us.
      * injection Hc as <- <-. exact Hh.
      * destruct (listNN_eqb (p :: us) [(addr, n)]); [|discriminate]. injection Hc as <- <-.
        unfold fixedin_destroyed_model. rewrite with_mmap_destroyed_halted'. cbn. exact Hh.
    + intros [r ws zs us cs ci] Hc. rewrite Hchk in Hc.
      destruct ws; [|discriminate]. destruct cs; [|discriminate]. destruct ci; [|discriminate].
      destruct (errno_ret_in mmap_errnos r); [destruct zs; [|discriminate]; destruct us; [discriminate|]; destruct (listNN_eqb _ _); discriminate|].
      destruct (Z.eqb prot 0); [destruct zs; [|discriminate] | destruct us; [|discriminate]];
        destruct (bv_eqb r addr && listNN_eqb _ _)%bool; discriminate.
    + intros []. unfold fixedin_ok_model. rewrite with_mmap_replacement_halted', with_vmmaps_halted. exact Hh.
    + intros []. unfold fixedin_ok_eff. destruct (Z.eqb prot 0); reflexivity.
  - intros []. cbv beta. unfold ms, fixedin_ok_eff. destruct (Z.eqb prot 0).
    + rewrite adv_unmaps1_epend. exact HB.
    + rewrite adv_zeros1_epend. exact HB.
Qed.
End CfgNodes.
