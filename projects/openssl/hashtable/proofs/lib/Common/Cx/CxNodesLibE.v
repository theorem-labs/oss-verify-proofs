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
From OSSVerify.Proofs.openssl.hashtable.lib Require Import
  SimInv ExitSim PropExec CatExec CatSim SeqExec StreamExec MmapSim AllocSim FileSim
  ShapeAlg SpinAlg Nodes StoreOk AgentLib AgentNodes RefNodesC
  AsanAcct AsanAcctShape AsanPlacement BackingAlgebra AsanNodesLibE AsanNodesMmLib.
From OSSVerify.Proofs.openssl.hashtable.lib.Common.Cfg Require Import ShapeAlgBase ShapeCfg NodesCfg.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import CxRel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Section Noacc.
Variable segs : list Segment.

Lemma crz_det_noacc : forall ms model x8 eff0 m0 T,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  (forall eff m' evs,
     check_syscall (sys_input segs ms x8) eff model = CheckOk m' evs <->
     (eff = eff0 /\ m' = m0 /\ evs = [])) ->
  (forall eff, check_syscall (sys_input segs ms x8) eff model <> CheckUnmodeled) ->
  m_halted m0 = None ->
  syscall_effect_accesses eff0 = [] ->
  crz segs (mkCfg (advance_past_svc (apply_effect ms eff0)) m0) T ->
  crz segs (mkCfg ms model) T.
Proof.
  intros ms model x8 eff0 m0 T Hh Hsvc Hchk Hnu Hh0 Hacc Hc.
  eapply crz_silent1; [eapply node_det_noacc; eassumption | exact Hc].
Qed.

Lemma crz_sys_lazy : forall regs pc mem rom model w T,
  m_halted model = None ->
  fetch_word segs pc = Some w -> is_ecall w = true ->
  crz segs (mkCfg (epend regs pc mem rom (getr regs 17)) model) T ->
  crz segs (mkCfg (mkst regs pc mem rom) model) T.
Proof.
  intros regs pc mem rom model w T Hh HF HE Hc.
  eapply crz_silent1; [| exact Hc].
  apply node_instr_noacc; [exact Hh | reflexivity | eapply stepacc_ecall_epend; eassumption].
Qed.

(* [comment removed for export] *)
Lemma crz_munmap_lazy : forall regs (pc : word) mem rom model w (a : word) (len : Z) K,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None ->
  getr regs 17 = Z_to_bv 64 215 ->
  getr regs 10 = a -> (bv_unsigned a mod page_size = 0)%Z ->
  getr regs 11 = Z_to_bv 64 len -> (0 < len)%Z ->
  (bv_unsigned a + page_round_up_Z len <= TASK_SIZE)%Z ->
  map_has (vm_maps (m_vmmaps model)) a (Z_to_bv 64 (page_round_up_Z len)) = true ->
  crz segs (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 0)) (v_addi pc 4)
                             (unfill a (Z_to_bv 64 (page_round_up_Z len)) mem) rom)
                      (munmap_model a (Z_to_bv 64 (page_round_up_Z len)) model)) K ->
  crz segs (mkCfg (mkst regs pc mem rom) model) K.
Proof.
  intros regs pc mem rom model w a len K HF HE Hh H17 H10 Hal H11 Hlen Hnw Hhas Hc.
  assert (Hlen' : (len < two_pow_64)%Z).
  { pose proof (page_round_up_Z_bounds len ltac:(lia)). pose proof (u64_range a). unfold TASK_SIZE, two_pow_64 in *. lia. }
  eapply crz_sys_lazy; [exact Hh | exact HF | exact HE |].
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

(* [comment removed for export] *)
Lemma crz_exit_at_lazy : forall regs (pc : word) mem rom model w code,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None ->
  (getr regs 17 = Z_to_bv 64 94 \/ getr regs 17 = Z_to_bv 64 93) ->
  getr regs 10 = code ->
  crz segs (mkCfg (mkst regs pc mem rom) model)
           (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model)).
Proof.
  intros regs pc mem rom model w code HF HE Hh H17 H10.
  eapply crz_sys_lazy; [exact Hh | exact HF | exact HE |].
  rewrite <- H10, <- (ms_gpr_epend0 regs pc mem rom (getr regs 17)).
  eapply crz_exit; [exact Hh | reflexivity |].
  destruct H17 as [H|H]; [right|left]; rewrite H; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma crz_set_tid_lazy : forall regs (pc : word) mem rom model K w,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None ->
  getr regs 17 = Z_to_bv 64 96 ->
  m_tid model = None ->
  (forall tid, (0 < bv_unsigned tid < PID_MAX_ENVELOPE)%Z ->
     crz segs (mkCfg (mkst (regupd regs 10 tid) (v_addi pc 4) mem rom) (with_tid tid model)) K) ->
  crz segs (mkCfg (mkst regs pc mem rom) model) K.
Proof.
  intros regs pc mem rom model K w HF HE Hh H17 Htid Hk.
  eapply crz_sys_lazy; [exact Hh | exact HF | exact HE |].
  apply (crz_conseq segs _ (t_alt (fun _ : tid_I => K)));
    [| intros tr; split; [intros [_ Ht]; exact Ht | intros Ht; exists (exist _ (Z_to_bv 64 1) one_tid_ok); exact Ht]].
  eapply (crz_cases_on segs _ tid_I _ _ (exist _ (Z_to_bv 64 1) one_tid_ok));
    [eapply node_set_tid_lazy; [exact Hh | reflexivity | rewrite H17; apply u64_lit; lia | exact Htid] | |].
  - apply (fam_on_sysno _ (getr regs 17)); [reflexivity | | | |]; rewrite H17, u64_lit by lia; lia.
  - intros [t Ht]. cbn [proj1_sig].
    change (mkEffectU t [] [] [] [] []) with (mkEffect t [] []).
    rewrite apply_effect_no_write, adv_set_epend. apply Hk. exact Ht.
Qed.


(* [comment removed for export] *)
Lemma crz_chk_fo : forall ms model x8 (IA IB : Type) (effs : IA + IB -> SyscallEffect) (ms' : IA + IB -> Model) (B : TSet) (b0 : IB),
  m_halted model = None -> ms_svc_pending ms = Some x8 ->
  (bv_unsigned x8 = 222 \/ bv_unsigned x8 = 226 \/ bv_unsigned x8 = 216)%Z ->
  (forall i, check_syscall (sys_input segs ms x8) (effs i) model = CheckOk (ms' i) []) ->
  (forall eff m' ev, check_syscall (sys_input segs ms x8) eff model = CheckOk m' ev ->
     exists i, eff = effs i /\ m' = ms' i /\ ev = []) ->
  (forall eff, check_syscall (sys_input segs ms x8) eff model <> CheckUnmodeled) ->
  (forall i, m_halted (ms' i) = None) ->
  (forall i, syscall_effect_accesses (effs i) = []) ->
  (forall a, eff_ret (effs (inl a)) = errno_ret ENOMEM) ->
  (forall b, bv_eqb (eff_ret (effs (inr b))) (errno_ret ENOMEM) = false) ->
  (forall b, crz segs (mkCfg (advance_past_svc (apply_effect ms (effs (inr b)))) (ms' (inr b))) B) ->
  crz segs (mkCfg ms model) B.
Proof.
  intros ms model x8 IA IB effs ms' B b0 Hh Hsvc Hno Hok Hinv Hnu Hh' Hacc HL HR Hk.
  assert (Harm : bv_unsigned (in_sysno (sys_input segs ms x8)) = 216%Z \/ bv_unsigned (in_sysno (sys_input segs ms x8)) = 222%Z
                 \/ bv_unsigned (in_sysno (sys_input segs ms x8)) = 226%Z).
  { rewrite in_sysno_sys_input. destruct Hno as [H|[H|H]]; rewrite H; auto. }
  eapply (crz_alt2_fo segs ms model x8 IA IB
            (fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms' i)) B b0 Hsvc).
  - rewrite sysno_family_off_alloc_only. destruct Hno as [H|[H|H]]; rewrite H; reflexivity.
  - exact (AsanNodesMmLib.node_chk_ev_mat segs ms model x8 (IA + IB) effs ms' (fun _ => []) Hh Hsvc Hok Hinv Hnu Hh' Hacc).
  - intros i. cbn [cfg_model]. exact (Hh' i).
  - intros a. cbn [cfg_ms]. rewrite ms_gpr0_apply_effect, (refusal_b_enomem_arm _ _ _ Harm), (HL a). apply bv_eqb_refl.
  - intros b. cbn [cfg_ms]. rewrite ms_gpr0_apply_effect, (refusal_b_enomem_arm _ _ _ Harm). exact (HR b).
  - exact Hk.
Qed.


(* [comment removed for export] *)
Lemma node_ok_unique : forall c (I : Type) (evs : I -> list event) (nx : I -> config) (i0 : I),
  node_ok segs c I evs nx -> (forall i, evs i = evs i0 /\ nx i = nx i0) ->
  node_ok segs c unit (fun _ => evs i0) (fun _ => nx i0).
Proof.
  intros c I evs nx i0 [H1 H2] Hu. split.
  - intros _. exact (H1 i0).
  - intros e st Hs. destruct (H2 e st Hs) as (i & -> & ->). exists tt. destruct (Hu i) as [-> ->]. split; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma crz_brk_query_lazy : forall regs (pc : word) mem rom model w K,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None ->
  getr regs 17 = Z_to_bv 64 214 ->
  getr regs 10 = Z_to_bv 64 0 ->
  crz segs (mkCfg (mkst (regupd regs 10 (vm_brk (m_vmmaps model))) (v_addi pc 4) mem rom) model) K ->
  crz segs (mkCfg (mkst regs pc mem rom) model) K.
Proof.
  intros regs pc mem rom model w K HF HE Hh H17 H10 Hc.
  eapply crz_sys_lazy; [exact Hh | exact HF | exact HE |].
  set (ms := epend regs pc mem rom (getr regs 17)).
  assert (Hno : bv_unsigned (getr regs 17) = 214%Z) by (rewrite H17; apply u64_lit; lia).
  assert (H0 : ms_gpr ms 0 = Z_to_bv 64 0) by (unfold ms; rewrite ms_gpr_epend0; exact H10).
  assert (Hcases : forall r, brk_resolution_ok model (ms_gpr ms 0) r <-> r = vm_brk (m_vmmaps model)).
  { intros r. rewrite H0. unfold brk_resolution_ok, Mmap.brk_r_ok. cbv zeta.
    unfold w_is0. rewrite bv_eqb_refl. cbn [orb]. apply bv_eqb_eq. }
  assert (Hq : brk_resolution_ok model (ms_gpr ms 0) (vm_brk (m_vmmaps model))) by (apply Hcases; reflexivity).
  pose proof (node_brk_lazy segs ms model (getr regs 17) Hh eq_refl Hno) as Hn.
  eapply crz_silent1.
  - apply (node_ok_unique _ _ _ _ (exist _ _ Hq) Hn). intros [r Hr]. cbn [proj1_sig].
    pose proof (proj1 (Hcases r) Hr) as Er. subst r. split; reflexivity.
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
  crz segs (mkCfg (mkst (regupd regs 10 b) (v_addi pc 4) mem rom) model) KA ->
  crz segs (mkCfg (mkst regs pc mem rom) model) KA.
Proof.
  intros regs pc mem rom model w req KA HF HE Hh H17 h b H10 Hpos Hs Hb Hblk HA.
  eapply crz_sys_lazy; [exact Hh | exact HF | exact HE |].
  set (ms := epend regs pc mem rom (getr regs 17)).
  assert (Hno : bv_unsigned (getr regs 17) = 214%Z) by (rewrite H17; apply u64_lit; lia).
  assert (H0 : ms_gpr ms 0 = req) by (unfold ms; rewrite ms_gpr_epend0; exact H10).
  assert (Hcases : forall r, brk_resolution_ok model (ms_gpr ms 0) r <-> r = b).
  { intros r. rewrite H0, (brk_r_ok_grow_cases model req r Hpos Hs Hb). fold h. fold b. split.
    - intros [-> | [-> Hg]]; [reflexivity | rewrite Hblk in Hg; discriminate].
    - intros ->. left. reflexivity. }
  assert (Hkeep : brk_resolution_ok model (ms_gpr ms 0) b) by (apply Hcases; reflexivity).
  pose proof (node_brk_lazy segs ms model (getr regs 17) Hh eq_refl Hno) as Hn.
  eapply crz_silent1.
  - apply (node_ok_unique _ _ _ _ (exist _ _ Hkeep) Hn). intros [r Hr]. cbn [proj1_sig].
    pose proof (proj1 (Hcases r) Hr) as Er. subst r. split; reflexivity.
  - cbn [proj1_sig]. fold h. fold b.
    rewrite brk_zeros_keep, brk_unmaps_keep. unfold b, h. rewrite brk_model_keep.
    unfold ms. rewrite adv_ret_epend. exact HA.
Qed.

(* [comment removed for export] *)
Lemma crz_brk_grow_lazy : forall regs (pc : word) mem rom model w (d : Z) KB,
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
  crz segs (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 (bv_unsigned b + d))) (v_addi pc 4)
                             (zfill b (Z_to_bv 64 d) mem) rom)
                       (with_vmmaps (mkVmMapsFull (vm_reserved h) ((b, Z_to_bv 64 d) :: vm_maps h)
                                      (vm_noaccess h) (vm_start_brk h)
                                      (Z_to_bv 64 (bv_unsigned b + d)) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)) model)) KB ->
  crz segs (mkCfg (mkst regs pc mem rom) model) KB.
Proof.
  intros regs pc mem rom model w d KB HF HE Hh H17 h b Hbal Hdal Hd Hb0 Hnw Hs H10 Hadm HB.
  pose proof (u64_range b) as Hbr.
  set (req := Z_to_bv 64 (bv_unsigned b + d)) in *.
  assert (Hureq : bv_unsigned req = (bv_unsigned b + d)%Z) by (unfold req; apply u64_lit; lia).
  eapply crz_sys_lazy; [exact Hh | exact HF | exact HE |].
  set (ms := epend regs pc mem rom (getr regs 17)).
  assert (Hno : bv_unsigned (getr regs 17) = 214%Z) by (rewrite H17; apply u64_lit; lia).
  assert (H0 : ms_gpr ms 0 = req) by (unfold ms; rewrite ms_gpr_epend0; exact H10).
  assert (Hcases : forall r, brk_resolution_ok model (ms_gpr ms 0) r <-> (r = b \/ (r = req /\ Mmap.brk_grow_ok model req req = true))).
  { intros r. rewrite H0. apply brk_r_ok_grow_cases; fold h; fold b; rewrite ?Hureq; lia. }
  assert (Hgrow : brk_resolution_ok model (ms_gpr ms 0) req) by (apply Hcases; right; split; [reflexivity | exact Hadm]).
  assert (Hneq : req <> b).
  { intros E. apply (f_equal bv_unsigned) in E. rewrite Hureq in E. unfold b in E. lia. }
  assert (Hreq0 : req <> Z_to_bv 64 0).
  { intros E. apply (f_equal bv_unsigned) in E. rewrite Hureq in E.
    change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in E. lia. }
  pose proof (node_brk_lazy segs ms model (getr regs 17) Hh eq_refl Hno) as Hn.
  assert (Hsys : bv_unsigned (in_sysno (sys_input segs ms (getr regs 17))) = 214%Z) by (rewrite in_sysno_sys_input; exact Hno).
  assert (Hrb : forall ret, refusal_b (sys_input segs ms (getr regs 17)) model ret = bv_eqb ret b).
  { intros ret. rewrite (refusal_b_brk _ _ _ Hsys), in_arg0_sys_input, H0. unfold brk_refusal_b. fold h. fold b.
    unfold w_is0. rewrite (bv_eqb_neq _ _ Hreq0), (bv_eqb_neq _ _ Hneq). cbn [negb andb].
    unfold Mmap.min_brk. replace (Z.ltb (bv_unsigned req) (bv_unsigned (vm_start_brk h))) with false; [reflexivity|].
    symmetry. apply Z.ltb_ge. rewrite Hureq. exact Hs. }
  apply (crz_conseq segs _ (t_alt (fun _ : unit => KB)));
    [| intros tr; split; [intros [_ Ht]; exact Ht | intros Ht; exists tt; exact Ht]].
  eapply (crz_cases_filter segs ms model (getr regs 17) _ unit _ (fun _ => exist _ req Hgrow) (fun _ => KB) tt eq_refl).
  - rewrite Hno. reflexivity.
  - exact Hn.
  - intros [r Hr]. cbn [cfg_model proj1_sig]. rewrite brk_model_halted. exact Hh.
  - intros _. cbn [cfg_ms proj1_sig]. rewrite ms_gpr0_apply_effect. cbn [eff_ret]. rewrite Hrb. exact (bv_eqb_neq _ _ Hneq).
  - intros [r Hr]. destruct (proj1 (Hcases r) Hr) as [-> | [-> Hg]].
    + right. cbn [cfg_ms proj1_sig]. rewrite ms_gpr0_apply_effect. cbn [eff_ret]. rewrite Hrb. apply bv_eqb_refl.
    + left. exists tt. f_equal. unfold brk_resolution_ok in *. apply (Eqdep_dec.UIP_dec Bool.bool_dec).
  - intros _. cbn [proj1_sig]. fold h.
    assert (Hlt : (bv_unsigned b < bv_unsigned req)%Z) by (rewrite Hureq; lia).
    rewrite H0. fold b. rewrite (brk_zeros_grow req req b Hreq0 Hb0 Hlt), (brk_unmaps_grow req b) by lia.
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

End Noacc.
