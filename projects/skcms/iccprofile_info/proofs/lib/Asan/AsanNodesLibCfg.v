(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require Import
  SimInv ExitSim PropExec CatExec CatSim SeqExec StreamExec MmapSim AllocSim FileSim
  ShapeAlg SpinAlg Nodes StoreOk AgentLib AgentNodes RefNodes
  AsanAcct AsanAcctShape AsanPlacement BackingAlgebra.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require Import AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require Import AsanCeil AsanNodesLibE AsanNodesMmLib AsanNodesNR.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require Import SpinAlgCfg.
Unset Nia Cache.  (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache.

Section WithFP.
Context {FP : PropExec.FPState}.
Variable segs : list Segment.
Let mmap_fixedin_check := AsanNodesLibE.mmap_fixedin_check segs.
Let node_chk_noacc := AsanNodesLibE.node_chk_noacc segs.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma srz_cfg_chk_nonref : forall ms model x8 (I : Type) (effs : I -> SyscallEffect) (ms' : I -> Model) (B : TSet) (i0 : I),
  ms_svc_pending ms = Some x8 ->
  injected_family_off CFG (sys_input segs ms x8) = true ->
  node_ok segs (mkCfg ms model) I (fun _ => []) (fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms' i)) ->
  refusal_b (sys_input segs ms x8) model (eff_ret (effs i0)) = false ->
  (forall i, refusal_b (sys_input segs ms x8) model (eff_ret (effs i)) = false ->
     srealizes_cfg segs (mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms' i)) B) ->
  srealizes_cfg segs (mkCfg ms model) B.
Proof.
  intros ms model x8 I effs ms' B i0 Hsvc Hoff Hnode Hr0 HB.
  apply (srz_cfg_silent_nonref segs ms model x8 I _ B i0 Hsvc Hoff Hnode).
  - intros i. reflexivity.
  - cbn [cfg_ms]. rewrite gpr0_adv_apply. exact Hr0.
  - intros i Hi. cbn [cfg_ms] in Hi. rewrite gpr0_adv_apply in Hi. exact (HB i Hi).
Qed.

(* [comment removed for export] *)
Lemma srz_cfg_sys_lazy : forall regs pc mem rom model w T,
  m_halted model = None ->
  fetch_word segs pc = Some w -> is_ecall w = true ->
  srealizes_cfg segs (mkCfg (epend regs pc mem rom (getr regs 17)) model) T ->
  srealizes_cfg segs (mkCfg (mkst regs pc mem rom) model) T.
Proof.
  intros regs pc mem rom model w T Hh HF HE Hc.
  eapply srz_cfg_silent1; [| exact Hc].
  apply AsanNodesLibE.node_instr_noacc; [exact Hh | reflexivity | eapply AsanNodesLibE.stepacc_ecall_epend; eassumption].
Qed.

(* [comment removed for export] *)
Lemma srz_cfg_det_noacc : forall ms model x8 eff0 m0 T,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  (forall eff m' evs,
     check_syscall (sys_input segs ms x8) eff model = CheckOk m' evs <->
     (eff = eff0 /\ m' = m0 /\ evs = [])) ->
  (forall eff, check_syscall (sys_input segs ms x8) eff model <> CheckUnmodeled) ->
  m_halted m0 = None ->
  syscall_effect_accesses eff0 = [] ->
  srealizes_cfg segs (mkCfg (advance_past_svc (apply_effect ms eff0)) m0) T ->
  srealizes_cfg segs (mkCfg ms model) T.
Proof.
  intros ms model x8 eff0 m0 T Hh Hsvc Hchk Hnu Hh0 Hacc Hc.
  eapply srz_cfg_silent1; [eapply AsanNodesLibE.node_det_noacc; eassumption | exact Hc].
Qed.

(* [comment removed for export] *)
Lemma refusal_b_in222 : forall ms x8 m ret,
  bv_unsigned x8 = 222%Z -> refusal_b (sys_input segs ms x8) m ret = errno_ret_in mmap_errnos ret.
Proof. intros ms x8 m ret Hno. unfold refusal_b. cbn [in_sysno sys_input]. rewrite Hno. reflexivity. Qed.

Lemma refusal_b_in226 : forall ms x8 m ret,
  bv_unsigned x8 = 226%Z -> refusal_b (sys_input segs ms x8) m ret = errno_ret_in mprotect_errnos ret.
Proof. intros ms x8 m ret Hno. unfold refusal_b. cbn [in_sysno sys_input]. rewrite Hno. reflexivity. Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma srz_cfg_munmap_lazy : forall regs (pc : word) mem rom model w (a : word) (len : Z) K,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None ->
  getr regs 17 = Z_to_bv 64 215 ->
  getr regs 10 = a -> (bv_unsigned a mod page_size = 0)%Z ->
  getr regs 11 = Z_to_bv 64 len -> (0 < len)%Z ->
  (bv_unsigned a + page_round_up_Z len <= TASK_SIZE)%Z ->
  map_has (vm_maps (m_vmmaps model)) a (Z_to_bv 64 (page_round_up_Z len)) = true ->
  srealizes_cfg segs (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 0)) (v_addi pc 4)
                             (unfill a (Z_to_bv 64 (page_round_up_Z len)) mem) rom)
                      (munmap_model a (Z_to_bv 64 (page_round_up_Z len)) model)) K ->
  srealizes_cfg segs (mkCfg (mkst regs pc mem rom) model) K.
Proof.
  intros regs pc mem rom model w a len K HF HE Hh H17 H10 Hal H11 Hlen Hnw Hhas Hc.
  assert (Hlen' : (len < two_pow_64)%Z).
  { pose proof (page_round_up_Z_bounds len ltac:(lia)). pose proof (u64_range a). unfold TASK_SIZE, two_pow_64 in *. lia. }
  eapply srz_cfg_sys_lazy; [exact Hh | exact HF | exact HE |].
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
  eapply (srz_cfg_det_noacc ms model (getr regs 17)
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
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma srz_cfg_brk_query_lazy : forall regs (pc : word) mem rom model w K,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None ->
  getr regs 17 = Z_to_bv 64 214 ->
  getr regs 10 = Z_to_bv 64 0 ->
  srealizes_cfg segs (mkCfg (mkst (regupd regs 10 (vm_brk (m_vmmaps model))) (v_addi pc 4) mem rom) model) K ->
  srealizes_cfg segs (mkCfg (mkst regs pc mem rom) model) K.
Proof.
  intros regs pc mem rom model w K HF HE Hh H17 H10 Hc.
  eapply srz_cfg_sys_lazy; [exact Hh | exact HF | exact HE |].
  set (ms := epend regs pc mem rom (getr regs 17)).
  assert (Hno : bv_unsigned (getr regs 17) = 214%Z) by (rewrite H17; apply u64_lit; lia).
  assert (H0 : ms_gpr ms 0 = Z_to_bv 64 0) by (unfold ms; rewrite ms_gpr_epend0; exact H10).
  assert (Hcases : forall r, brk_resolution_ok model (ms_gpr ms 0) r <-> r = vm_brk (m_vmmaps model)).
  { intros r. rewrite H0. unfold brk_resolution_ok, Mmap.brk_r_ok. cbv zeta.
    unfold w_is0. rewrite bv_eqb_refl. cbn [orb]. apply bv_eqb_eq. }
  assert (Hq : brk_resolution_ok model (ms_gpr ms 0) (vm_brk (m_vmmaps model))) by (apply Hcases; reflexivity).
  pose proof (AsanNodesLibE.node_brk_lazy segs ms model (getr regs 17) Hh eq_refl Hno) as Hnode.
  eapply (srz_cfg_same segs _ _ _ K (exist _ _ Hq)).
  - apply (node_ok_cfg_nonref segs ms model (getr regs 17) _ _ _ (exist _ _ Hq) eq_refl Hnode).
    + intros i. reflexivity.
    + intros [r Hr]. cbn [cfg_ms proj1_sig]. rewrite gpr0_adv_apply. cbn [eff_ret].
      rewrite (refusal_b_brk segs ms (getr regs 17) model r Hno), H0. unfold brk_refusal_b.
      unfold w_is0. rewrite bv_eqb_refl. reflexivity.
  - intros [r Hr]. cbn [proj1_sig].
    pose proof (proj1 (Hcases r) Hr) as Er. subst r.
    rewrite H0, brk_zeros_query, brk_unmaps_keep.
    rewrite (brk_model_query _ model eq_refl), vmmaps_eta, with_vmmaps_eta.
    unfold ms. rewrite adv_ret_epend. exact Hc.
Qed.

(* [comment removed for export] *)
Lemma srz_cfg_brk_grow_lazy : forall regs (pc : word) mem rom model w (d : Z) KB,
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
  srealizes_cfg segs (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 (bv_unsigned b + d))) (v_addi pc 4)
                             (zfill b (Z_to_bv 64 d) mem) rom)
                       (with_vmmaps (mkVmMapsFull (vm_reserved h) ((b, Z_to_bv 64 d) :: vm_maps h)
                                      (vm_noaccess h) (vm_start_brk h)
                                      (Z_to_bv 64 (bv_unsigned b + d)) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)) model)) KB ->
  srealizes_cfg segs (mkCfg (mkst regs pc mem rom) model) KB.
Proof.
  intros regs pc mem rom model w d KB HF HE Hh H17 h b Hbal Hdal Hd Hb0 Hnw Hs H10 Hadm HB.
  pose proof (u64_range b) as Hbr.
  set (req := Z_to_bv 64 (bv_unsigned b + d)) in *.
  assert (Hureq : bv_unsigned req = (bv_unsigned b + d)%Z) by (unfold req; apply u64_lit; lia).
  eapply srz_cfg_sys_lazy; [exact Hh | exact HF | exact HE |].
  set (ms := epend regs pc mem rom (getr regs 17)).
  assert (Hno : bv_unsigned (getr regs 17) = 214%Z) by (rewrite H17; apply u64_lit; lia).
  assert (H0 : ms_gpr ms 0 = req) by (unfold ms; rewrite ms_gpr_epend0; exact H10).
  assert (Hcases : forall r, brk_resolution_ok model (ms_gpr ms 0) r <-> (r = b \/ (r = req /\ Mmap.brk_grow_ok model req req = true))).
  { intros r. rewrite H0. apply brk_r_ok_grow_cases; fold h; fold b; rewrite ?Hureq; lia. }
  assert (Hgrow : brk_resolution_ok model (ms_gpr ms 0) req) by (apply Hcases; right; split; [reflexivity | exact Hadm]).
  assert (Hneq : req <> b).
  { intros E. apply (f_equal bv_unsigned) in E. rewrite Hureq in E. unfold b in E. lia. }
  pose proof (AsanNodesLibE.node_brk_lazy segs ms model (getr regs 17) Hh eq_refl Hno) as Hnode.
  apply (srz_cfg_silent_nonref segs ms model (getr regs 17) _ _ KB (exist _ req Hgrow) eq_refl
           (injected_family_off_no segs ms (getr regs 17) 214 Hno eq_refl) Hnode).
  - intros i. reflexivity.
  - cbn [cfg_ms proj1_sig]. rewrite gpr0_adv_apply. cbn [eff_ret].
    rewrite (refusal_b_brk segs ms (getr regs 17) model req Hno), H0. unfold brk_refusal_b.
    change (vm_brk (m_vmmaps model)) with b. rewrite (bv_eqb_neq _ _ Hneq). rewrite !andb_false_r. reflexivity.
  - intros [r Hr] Hnr. cbn [cfg_ms proj1_sig] in Hnr |- *. fold h.
    rewrite gpr0_adv_apply in Hnr. cbn [eff_ret] in Hnr.
    destruct (proj1 (Hcases r) Hr) as [-> | [-> Hg]].
    + exfalso. rewrite (refusal_b_brk segs ms (getr regs 17) model b Hno), H0 in Hnr. unfold brk_refusal_b in Hnr.
      fold h b in Hnr.
      assert (Hreq0 : w_is0 req = false).
      { unfold w_is0. apply bv_eqb_neq. intros E. apply (f_equal bv_unsigned) in E. rewrite Hureq in E.
        change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in E. lia. }
      change (vm_brk (m_vmmaps model)) with b in Hnr.
      rewrite Hreq0 in Hnr. rewrite (bv_eqb_neq req b Hneq) in Hnr. rewrite bv_eqb_refl in Hnr. cbn [negb andb] in Hnr.
      destruct (Z.ltb (bv_unsigned req) (bv_unsigned (min_brk h))) eqn:Hmin; [| discriminate Hnr].
      (* [comment removed for export] *)
      apply Z.ltb_lt in Hmin.
      unfold min_brk in Hmin. rewrite Hureq in Hmin.
      pose proof (u64_range (vm_start_brk h)) as Hsr. lia.
    + assert (Hlt : (bv_unsigned b < bv_unsigned req)%Z) by (rewrite Hureq; lia).
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
      unfold ms. rewrite adv_zeros1_epend. exact HB.
Qed.

(* [comment removed for export] *)
Lemma srz_cfg_brk_grow_blocked_lazy : forall regs (pc : word) mem rom model w (req : word) KA,
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
  srealizes_cfg segs (mkCfg (mkst (regupd regs 10 b) (v_addi pc 4) mem rom) model) KA ->
  srealizes_cfg segs (mkCfg (mkst regs pc mem rom) model) KA.
Proof.
  intros regs pc mem rom model w req KA HF HE Hh H17 h b H10 Hpos Hs Hb Hblk HA.
  eapply srz_cfg_sys_lazy; [exact Hh | exact HF | exact HE |].
  set (ms := epend regs pc mem rom (getr regs 17)).
  assert (Hno : bv_unsigned (getr regs 17) = 214%Z) by (rewrite H17; apply u64_lit; lia).
  assert (H0 : ms_gpr ms 0 = req) by (unfold ms; rewrite ms_gpr_epend0; exact H10).
  assert (Hcases : forall r, brk_resolution_ok model (ms_gpr ms 0) r <-> r = b).
  { intros r. rewrite H0, (brk_r_ok_grow_cases model req r Hpos Hs Hb). fold h. fold b. split.
    - intros [-> | [-> Hg]]; [reflexivity | rewrite Hblk in Hg; discriminate].
    - intros ->. left. reflexivity. }
  assert (Hkeep : brk_resolution_ok model (ms_gpr ms 0) b) by (apply Hcases; reflexivity).
  pose proof (AsanNodesLibE.node_brk_lazy segs ms model (getr regs 17) Hh eq_refl Hno) as Hnode.
  eapply (srz_cfg_same segs _ _ _ KA (exist _ b Hkeep)).
  - apply (node_ok_cfg_uniform segs ms model _ _ _ Hnode).
    + intros i. reflexivity.
    + intros [r Hr] [r' Hr']. cbn [cfg_ms proj1_sig]. rewrite !gpr0_adv_apply. cbn [eff_ret].
      rewrite (proj1 (Hcases r) Hr), (proj1 (Hcases r') Hr'). reflexivity.
  - intros [r Hr]. cbn [proj1_sig]. fold h.
    pose proof (proj1 (Hcases r) Hr) as Er. subst r. fold b.
    rewrite brk_zeros_keep, brk_unmaps_keep. unfold b, h. rewrite brk_model_keep.
    unfold ms. rewrite adv_ret_epend. exact HA.
Qed.

(* [comment removed for export] *)
Lemma srz_cfg_brk_grow_unk_lazy : forall regs (pc : word) mem rom model w (d : Z) K,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None ->
  getr regs 17 = Z_to_bv 64 214 ->
  let h := m_vmmaps model in
  let b := vm_brk h in
  (bv_unsigned b mod page_size = 0)%Z -> (d mod page_size = 0)%Z -> (0 < d)%Z ->
  (0 < bv_unsigned b)%Z -> (bv_unsigned b + d < 2 ^ 64)%Z ->
  (bv_unsigned (vm_start_brk h) <= bv_unsigned b + d)%Z ->
  getr regs 10 = Z_to_bv 64 (bv_unsigned b + d) ->
  (* [comment removed for export] *)
  srealizes_cfg segs (mkCfg (mkst (regupd regs 10 b) (v_addi pc 4) mem rom) model) K ->
  (* [comment removed for export] *)
  (Mmap.brk_grow_ok model (Z_to_bv 64 (bv_unsigned b + d)) (Z_to_bv 64 (bv_unsigned b + d)) = true ->
   srealizes_cfg segs (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 (bv_unsigned b + d))) (v_addi pc 4)
                              (zfill b (Z_to_bv 64 d) mem) rom)
                        (with_vmmaps (mkVmMapsFull (vm_reserved h) ((b, Z_to_bv 64 d) :: vm_maps h)
                                       (vm_noaccess h) (vm_start_brk h)
                                       (Z_to_bv 64 (bv_unsigned b + d)) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)) model)) K) ->
  srealizes_cfg segs (mkCfg (mkst regs pc mem rom) model) K.
Proof.
  intros regs pc mem rom model w d K HF HE Hh H17 h b Hbal Hdal Hd Hb0 Hnw Hs H10 HA HB.
  pose proof (u64_range b) as Hbr.
  destruct (Mmap.brk_grow_ok model (Z_to_bv 64 (bv_unsigned b + d)) (Z_to_bv 64 (bv_unsigned b + d))) eqn:Hg.
  - exact (srz_cfg_brk_grow_lazy regs pc mem rom model w d K HF HE Hh H17 Hbal Hdal Hd Hb0 Hnw Hs H10 Hg (HB eq_refl)).
  - unfold b, h in *.
    assert (Hu : bv_unsigned (Z_to_bv 64 (bv_unsigned (vm_brk (m_vmmaps model)) + d)) = (bv_unsigned (vm_brk (m_vmmaps model)) + d)%Z)
      by (apply u64_lit; lia).
    eapply (srz_cfg_brk_grow_blocked_lazy regs pc mem rom model w (Z_to_bv 64 (bv_unsigned (vm_brk (m_vmmaps model)) + d)) K HF HE Hh H17);
      [exact H10 | rewrite Hu; lia | rewrite Hu; exact Hs | rewrite Hu; lia | exact Hg | exact HA].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma srz_cfg_set_tid_lazy : forall regs (pc : word) mem rom model K w,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None ->
  getr regs 17 = Z_to_bv 64 96 ->
  m_tid model = None ->
  (forall tid, (0 < bv_unsigned tid < PID_MAX_ENVELOPE)%Z ->
     srealizes_cfg segs (mkCfg (mkst (regupd regs 10 tid) (v_addi pc 4) mem rom) (with_tid tid model)) K) ->
  srealizes_cfg segs (mkCfg (mkst regs pc mem rom) model) K.
Proof.
  intros regs pc mem rom model K w HF HE Hh H17 Htid Hk.
  eapply srz_cfg_sys_lazy; [exact Hh | exact HF | exact HE |].
  assert (Hno : bv_unsigned (getr regs 17) = 96%Z) by (rewrite H17; apply u64_lit; lia).
  eapply (srz_cfg_same segs _ tid_I _ K (exist _ (Z_to_bv 64 1) one_tid_ok)).
  - apply node_ok_cfg_of_nonalloc.
    + apply (nonalloc_no segs (epend regs pc mem rom (getr regs 17)) model (getr regs 17) eq_refl). rewrite Hno. reflexivity.
    + eapply AsanNodesLibE.node_set_tid_lazy; [exact Hh | reflexivity | exact Hno | exact Htid].
  - intros [t Ht]. cbn [proj1_sig].
    change (mkEffectU t [] [] [] [] []) with (mkEffect t [] []).
    rewrite apply_effect_no_write, adv_set_epend. apply Hk. exact Ht.
Qed.

Lemma srz_cfg_exit_at_lazy : forall regs (pc : word) mem rom model w code,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None ->
  (getr regs 17 = Z_to_bv 64 94 \/ getr regs 17 = Z_to_bv 64 93) ->
  getr regs 10 = code ->
  srealizes_cfg segs (mkCfg (mkst regs pc mem rom) model)
           (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model)).
Proof.
  intros regs pc mem rom model w code HF HE Hh H17 H10.
  eapply srz_cfg_sys_lazy; [exact Hh | exact HF | exact HE |].
  rewrite <- H10, <- (ms_gpr_epend0 regs pc mem rom (getr regs 17)).
  eapply srz_cfg_exit; [exact Hh | reflexivity |].
  destruct H17 as [H|H]; [right|left]; rewrite H; reflexivity.
Qed.

Lemma srz_cfg_mmap_fixedin_lazy : forall regs (pc : word) mem rom model w (prot : Z) (flags addr : word) (len : Z) KB,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None ->
  getr regs 17 = Z_to_bv 64 222 ->
  (prot = 0 \/ prot = 3)%Z -> mmap_flags_core flags = 50%Z ->
  getr regs 10 = addr -> (bv_unsigned addr mod page_size = 0)%Z -> (0 < bv_unsigned addr)%Z ->
  getr regs 11 = Z_to_bv 64 len -> (0 < len)%Z ->
  (bv_unsigned addr + page_round_up_Z len <= alloc_top (m_vmmaps model))%Z -> init_sp_ok (m_vmmaps model) ->   (* [comment removed for export] *)
  getr regs 12 = Z_to_bv 64 prot -> getr regs 13 = flags ->
  getr regs 14 = Z_to_bv 64 (-1) -> getr regs 15 = Z_to_bv 64 0 ->
  let n := Z_to_bv 64 (page_round_up_Z len) in
  region_free (vm_reserved (m_vmmaps model)) addr n = true ->
  map_contains (vm_maps (m_vmmaps model)) addr n = true ->
  (prot = 3%Z -> mmap_fixed_rw_budget_ok flags model addr n = true) ->
  srealizes_cfg segs (mkCfg (mkst (regupd regs 10 addr) (v_addi pc 4)
                             (if Z.eqb prot 0 then unfill addr n mem else zfill addr n mem) rom)
                       (fixedin_ok_model prot flags addr n model)) KB ->
  srealizes_cfg segs (mkCfg (mkst regs pc mem rom) model) KB.
Proof.
  intros regs pc mem rom model w prot flags addr len KB HF HE Hh H17 Hprot Hcore H10 Hal Hpos H11 Hlen Hce Hisp H12 H13 H14 H15 n Hrf Hmc Hbud HB.
  pose proof (alloc_top_room (m_vmmaps model)) as Hcv. unfold stack_max_size, two_pow_64 in Hcv. pose proof (u64_range addr) as Har.
  eapply srz_cfg_sys_lazy; [exact Hh | exact HF | exact HE |].
  set (ms := epend regs pc mem rom (getr regs 17)).
  assert (Hno : bv_unsigned (getr regs 17) = 222%Z) by (rewrite H17; apply u64_lit; lia).
  assert (Hlen' : (len < 2 ^ 64)%Z) by (pose proof (page_round_up_Z_bounds len ltac:(lia)); lia).
  pose proof (fun eff => mmap_fixedin_check ms (getr regs 17) model eff prot flags addr len Hno Hprot Hcore
                           ltac:(unfold ms; rewrite ms_gpr_epend0; exact H10) Hal Hpos
                           ltac:(unfold ms; rewrite ms_gpr_epend1; exact H11) Hlen
                           ltac:(unfold ms; rewrite ms_gpr_epend2; exact H12)
                           ltac:(unfold ms; rewrite ms_gpr_epend3; exact H13)
                           ltac:(unfold ms; rewrite ms_gpr_epend4; exact H14)
                           ltac:(unfold ms; rewrite ms_gpr_epend5; exact H15)
                           Hce Hisp Hrf Hmc Hbud) as Hchk.
  cbv zeta in Hchk. fold n in Hchk.
  assert (Haddr_ne : errno_ret_in mmap_errnos addr = false).
  { apply errno_ret_in_below; [reflexivity|]. unfold two_pow_64.
    pose proof (page_round_up_Z_bounds len ltac:(lia)). lia. }
  pose (effs := fun i : three => match i with
                           | T1 => mkEffectU (errno_ret ENOMEM) [] [] [] [] []
                           | T2 => fixedin_ok_eff prot addr n
                           | T3 => mkEffectU (errno_ret ENOMEM) [] [] [(addr, n)] [] [] end).
  pose (ms' := fun i : three => match i with
                          | T1 => model
                          | T2 => fixedin_ok_model prot flags addr n model
                          | T3 => fixedin_destroyed_model addr n model end).
  assert (Herr : forall e, In e mmap_errnos -> e = ENOMEM) by (intros e [<-|[]]; reflexivity).
  assert (Hp0 : Z.eqb prot 0 = true <-> prot = 0%Z) by (apply Z.eqb_eq).
  assert (Hnode : ShapeAlg.node_ok segs (mkCfg ms model) three (fun _ => [])
            (fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms' i))).
  { apply (node_chk_noacc ms model (getr regs 17) three effs ms' Hh eq_refl).
    + intros [| |]; cbn [effs ms'].
      * rewrite Hchk. rewrite (errno_ret_in_intro _ _ ENOMEM_in_mmap_errnos). reflexivity.
      * unfold fixedin_ok_eff. destruct (Z.eqb prot 0) eqn:Ep; rewrite Hchk, Haddr_ne, ?Ep, bv_eqb_refl, (proj2 (listNN_eqb_eq _ _) eq_refl); reflexivity.
      * rewrite Hchk. rewrite (errno_ret_in_intro _ _ ENOMEM_in_mmap_errnos), (proj2 (listNN_eqb_eq _ _) eq_refl). reflexivity.
    + intros [r ws zs us cs ci] m' evs Hc. rewrite Hchk in Hc.
      destruct ws; [|discriminate]. destruct cs; [|discriminate]. destruct ci; [|discriminate].
      destruct (errno_ret_in mmap_errnos r) eqn:Er.
      * destruct (proj1 (errno_ret_in_true _ _) Er) as (e & He & ->). rewrite (Herr e He).
        destruct zs; [|discriminate]. destruct us.
        -- injection Hc as <- <-. exists T1. repeat split; reflexivity.
        -- destruct (listNN_eqb (p :: us) [(addr, n)]) eqn:Hl; [|discriminate].
           apply listNN_eqb_eq in Hl. rewrite Hl. injection Hc as <- <-. exists T3. repeat split; reflexivity.
      * destruct (Z.eqb prot 0) eqn:Ep.
        -- destruct zs; [|discriminate].
           destruct (bv_eqb r addr) eqn:Eb; [|discriminate].
           destruct (listNN_eqb us [(addr, n)]) eqn:Hl; [|discriminate].
           apply bv_eqb_eq in Eb. apply listNN_eqb_eq in Hl. subst. injection Hc as <- <-.
           exists T2. cbn [effs ms']. unfold fixedin_ok_eff. rewrite Ep. repeat split; reflexivity.
        -- destruct us; [|discriminate].
           destruct (bv_eqb r addr) eqn:Eb; [|discriminate].
           destruct (listNN_eqb zs [(addr, n)]) eqn:Hl; [|discriminate].
           apply bv_eqb_eq in Eb. apply listNN_eqb_eq in Hl. subst. injection Hc as <- <-.
           exists T2. cbn [effs ms']. unfold fixedin_ok_eff. rewrite Ep. repeat split; reflexivity.
    + intros [r ws zs us cs ci] Hc. rewrite Hchk in Hc.
      destruct ws; [|discriminate]. destruct cs; [|discriminate]. destruct ci; [|discriminate].
      destruct (errno_ret_in mmap_errnos r); [destruct zs; [|discriminate]; destruct us; [discriminate|]; destruct (listNN_eqb _ _); discriminate|].
      destruct (Z.eqb prot 0); [destruct zs; [|discriminate] | destruct us; [|discriminate]];
        destruct (bv_eqb r addr && listNN_eqb _ _)%bool; discriminate.
    + intros [| |]; cbn [ms']; [exact Hh | unfold fixedin_ok_model; rewrite with_mmap_replacement_halted', with_vmmaps_halted; exact Hh
                              | unfold fixedin_destroyed_model; rewrite with_mmap_destroyed_halted'; cbn; exact Hh].
    + intros [| |]; cbn [effs]; unfold fixedin_ok_eff; [reflexivity | destruct (Z.eqb prot 0); reflexivity | reflexivity]. }
  apply (srz_cfg_chk_nonref ms model (getr regs 17) three effs ms' KB T2 eq_refl
           (injected_family_off_no segs ms (getr regs 17) 222 Hno eq_refl) Hnode).
  - cbn [effs]. unfold fixedin_ok_eff. rewrite (refusal_b_in222 ms (getr regs 17) model _ Hno).
    destruct (Z.eqb prot 0); exact Haddr_ne.
  - intros [| |] Hnr.
    + exfalso. cbn [effs eff_ret] in Hnr. rewrite (refusal_b_in222 ms (getr regs 17) model _ Hno), (errno_ret_in_intro _ _ ENOMEM_in_mmap_errnos) in Hnr.
      discriminate Hnr.
    + cbn [effs ms']. unfold ms, fixedin_ok_eff. destruct (Z.eqb prot 0).
      * rewrite adv_unmaps1_epend. exact HB.
      * rewrite adv_zeros1_epend. exact HB.
    + exfalso. cbn [effs eff_ret] in Hnr. rewrite (refusal_b_in222 ms (getr regs 17) model _ Hno), (errno_ret_in_intro _ _ ENOMEM_in_mmap_errnos) in Hnr.
      discriminate Hnr.
Qed.

End WithFP.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section WithFPmm.
Context {FP : PropExec.FPState}.
Variable segs : list Segment.
Let mmap_rw_check := AsanNodesMmLib.mmap_rw_check segs.
Let mmap_none_check := AsanNodesMmLib.mmap_none_check segs.
Let mmap_fixed_rw_free_check := AsanNodesMmLib.mmap_fixed_rw_free_check segs.
Let mmap_fixed_none_free_check := AsanNodesMmLib.mmap_fixed_none_free_check segs.
Let mmap_noreplace_rw_free_check := AsanNodesNR.mmap_noreplace_rw_free_check segs.
Let mmap_noreplace_none_free_check := AsanNodesNR.mmap_noreplace_none_free_check segs.

Lemma srz_cfg_mmap_rw2 : forall regs (pc : word) mem rom model w (len : Z) (flags : word) KB,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> init_sp_ok (m_vmmaps model) ->
  getr regs 17 = Z_to_bv 64 222 ->
  getr regs 11 = Z_to_bv 64 len -> (0 < len < 2 ^ 64)%Z ->
  getr regs 12 = Z_to_bv 64 3 -> getr regs 13 = flags -> mmap_flags_core flags = 34%Z ->
  getr regs 14 = Z_to_bv 64 (-1) -> getr regs 15 = Z_to_bv 64 0 ->
  let nZ := page_round_up_Z len in
  let n := Z_to_bv 64 nZ in
  (exists a, grant_ok_na_pin model a nZ = true /\ mmap_noreserve_backed_ok flags model nZ = true) ->
  (forall a, grant_ok_na_pin model a nZ = true -> mmap_noreserve_backed_ok flags model nZ = true ->
     srealizes_cfg segs (mkCfg (mkst (regupd regs 10 a) (v_addi pc 4) (zfill a n mem) rom)
                          (with_mmap_backing flags a n (mmap_model a n model))) KB) ->
  srealizes_cfg segs (mkCfg (mkst regs pc mem rom) model) KB.
Proof.
  intros regs pc mem rom model w len flags KB HF HE Hh Hisp H17 H11 Hlen H12 H13 Hcore H14 H15 nZ n (a0 & Ha0 & Hb0) HB.
  eapply srz_cfg_sys_lazy; [exact Hh | exact HF | exact HE |].
  set (ms := epend regs pc mem rom (getr regs 17)).
  assert (Hno : bv_unsigned (getr regs 17) = 222%Z) by (rewrite H17; apply u64_lit; lia).
  destruct (epend_len regs pc mem rom len H11 Hlen) as [Hl1 Hne1]. fold ms in Hl1, Hne1.
  pose proof (fun eff => mmap_rw_check ms (getr regs 17) model eff flags Hno Hne1
                           ltac:(unfold ms; rewrite ms_gpr_epend2; exact H12)
                           ltac:(unfold ms; rewrite ms_gpr_epend3; exact H13) Hcore
                           ltac:(unfold ms; rewrite ms_gpr_epend4; exact H14)
                           ltac:(unfold ms; rewrite ms_gpr_epend5; exact H15)) as Hchk.
  cbv zeta in Hchk. rewrite Hl1 in Hchk. fold nZ n in Hchk.
  assert (H0 : ms_gpr ms 0 = getr regs 10) by (unfold ms; rewrite ms_gpr_epend0; reflexivity).
  rewrite Hb0 in Hchk.
  assert (Hn0 : (0 <= nZ)%Z) by (unfold nZ; apply page_round_up_Z_nonneg; lia).
  assert (HnZpos : (0 < nZ)%Z) by (unfold nZ; apply page_round_up_Z_pos'; lia).
  assert (HnZal : (nZ mod page_size = 0)%Z) by (unfold nZ; apply page_round_up_Z_aligned').
  pose (IB := {a : word | grant_ok_na_pin model a nZ = true}).
  pose (effs := fun i : unit + IB => match i with
                           | inl _ => mkEffectU (errno_ret ENOMEM) [] [] [] [] []
                           | inr (exist _ a _) => mkEffectU a [] [(a, n)] [] [] [] end).
  pose (ms' := fun i : unit + IB => match i with
                          | inl _ => model
                          | inr (exist _ a _) => with_mmap_backing flags a n (mmap_model a n model) end).
  assert (Hnode : ShapeAlg.node_ok segs (mkCfg ms model) (unit + IB) (fun _ => [])
            (fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms' i))).
  { apply (node_chk_ev_mat segs ms model (getr regs 17) (unit + IB) effs ms' (fun _ => []) Hh eq_refl).
    + intros [[] | [a Ha]]; cbn [effs ms']; rewrite Hchk.
      * rewrite (errno_ret_in_intro _ _ ENOMEM_in_mmap_errnos). reflexivity.
      * rewrite (grant_na_pin_not_errno model a nZ Hn0 Ha), Ha. cbn [andb].
        rewrite (proj2 (listNN_eqb_eq _ _) eq_refl). reflexivity.
    + intros [r ws zs us cs ci] m' evs Hc. rewrite Hchk in Hc.
      destruct ws; [|discriminate]. destruct us; [|discriminate].
      destruct cs; [|discriminate]. destruct ci; [|discriminate].
      destruct (errno_ret_in mmap_errnos r) eqn:Er.
      * destruct zs; [|discriminate]. injection Hc as <- <-.
        destruct (proj1 (errno_ret_in_true _ _) Er) as (e & He & ->).
        rewrite (mmap_errnos_ENOMEM e He). exists (inl tt). repeat split; reflexivity.
      * destruct (grant_ok_na_pin model r nZ) eqn:Hg; [|discriminate].
        cbn [andb] in Hc.
        destruct (listNN_eqb zs [(r, n)]) eqn:Hl; [|discriminate].
        apply listNN_eqb_eq in Hl. subst zs. injection Hc as <- <-.
        exists (inr (exist _ r Hg)). repeat split; reflexivity.
    + intros [r ws zs us cs ci] Hc. rewrite Hchk in Hc.
      destruct ws; [|discriminate]. destruct us; [|discriminate].
      destruct cs; [|discriminate]. destruct ci; [|discriminate].
      destruct (errno_ret_in mmap_errnos r); [destruct zs; discriminate|].
      destruct (grant_ok_na_pin model r nZ && true && listNN_eqb zs [(r, n)])%bool; discriminate.
    + intros [[] | [a Ha]]; cbn [ms']; [exact Hh | rewrite with_mmap_backing_halted; unfold mmap_model; rewrite with_vmmaps_halted; exact Hh].
    + intros [[] | [a Ha]]; reflexivity. }
  apply (srz_cfg_chk_nonref segs ms model (getr regs 17) (unit + IB) effs ms' KB (inr (exist _ a0 Ha0)) eq_refl
           (injected_family_off_no segs ms (getr regs 17) 222 Hno eq_refl) Hnode).
  - cbn [effs eff_ret]. rewrite (refusal_b_in222 segs ms (getr regs 17) model _ Hno). exact (grant_na_pin_not_errno model a0 nZ Hn0 Ha0).
  - intros [[] | [a Ha]] Hnr.
    + exfalso. cbn [effs eff_ret] in Hnr. rewrite (refusal_b_in222 segs ms (getr regs 17) model _ Hno), (errno_ret_in_intro _ _ ENOMEM_in_mmap_errnos) in Hnr.
      discriminate Hnr.
    + cbn [effs ms']. unfold ms. rewrite adv_zeros1_epend. apply HB; [exact Ha | exact Hb0].
Qed.

Lemma srz_cfg_mmap_none2 : forall regs (pc : word) mem rom model w (len : Z) (flags : word) KB,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> init_sp_ok (m_vmmaps model) ->
  getr regs 17 = Z_to_bv 64 222 ->
  getr regs 11 = Z_to_bv 64 len -> (0 < len < 2 ^ 64)%Z ->
  getr regs 12 = Z_to_bv 64 0 -> getr regs 13 = flags -> mmap_flags_core flags = 34%Z ->
  getr regs 14 = Z_to_bv 64 (-1) -> getr regs 15 = Z_to_bv 64 0 ->
  let nZ := page_round_up_Z len in
  let n := Z_to_bv 64 nZ in
  (exists a, grant_ok_na_pin model a nZ = true) ->
  (forall a, grant_ok_na_pin model a nZ = true ->
     srealizes_cfg segs (mkCfg (mkst (regupd regs 10 a) (v_addi pc 4) (unfill a n mem) rom)
                          (with_mmap_backing flags a n (noaccess_model a n model))) KB) ->
  srealizes_cfg segs (mkCfg (mkst regs pc mem rom) model) KB.
Proof.
  intros regs pc mem rom model w len flags KB HF HE Hh Hisp H17 H11 Hlen H12 H13 Hcore H14 H15 nZ n (a0 & Ha0) HB.
  eapply srz_cfg_sys_lazy; [exact Hh | exact HF | exact HE |].
  set (ms := epend regs pc mem rom (getr regs 17)).
  assert (Hno : bv_unsigned (getr regs 17) = 222%Z) by (rewrite H17; apply u64_lit; lia).
  destruct (epend_len regs pc mem rom len H11 Hlen) as [Hl1 Hne1]. fold ms in Hl1, Hne1.
  pose proof (fun eff => mmap_none_check ms (getr regs 17) model eff flags Hno Hne1
                           ltac:(unfold ms; rewrite ms_gpr_epend2; exact H12)
                           ltac:(unfold ms; rewrite ms_gpr_epend3; exact H13) Hcore
                           ltac:(unfold ms; rewrite ms_gpr_epend4; exact H14)
                           ltac:(unfold ms; rewrite ms_gpr_epend5; exact H15)) as Hchk.
  cbv zeta in Hchk. rewrite Hl1 in Hchk. fold nZ n in Hchk.
  assert (H0 : ms_gpr ms 0 = getr regs 10) by (unfold ms; rewrite ms_gpr_epend0; reflexivity).
  assert (Hn0 : (0 <= nZ)%Z) by (unfold nZ; apply page_round_up_Z_nonneg; lia).
  assert (HnZpos : (0 < nZ)%Z) by (unfold nZ; apply page_round_up_Z_pos'; lia).
  assert (HnZal : (nZ mod page_size = 0)%Z) by (unfold nZ; apply page_round_up_Z_aligned').
  pose (IB := {a : word | grant_ok_na_pin model a nZ = true}).
  pose (effs := fun i : unit + IB => match i with
                           | inl _ => mkEffectU (errno_ret ENOMEM) [] [] [] [] []
                           | inr (exist _ a _) => mkEffectU a [] [] [(a, n)] [] [] end).
  pose (ms' := fun i : unit + IB => match i with
                          | inl _ => model
                          | inr (exist _ a _) => with_mmap_backing flags a n (noaccess_model a n model) end).
  assert (Hnode : ShapeAlg.node_ok segs (mkCfg ms model) (unit + IB) (fun _ => [])
            (fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms' i))).
  { apply (node_chk_ev_mat segs ms model (getr regs 17) (unit + IB) effs ms' (fun _ => []) Hh eq_refl).
    + intros [[] | [a Ha]]; cbn [effs ms']; rewrite Hchk.
      * rewrite (errno_ret_in_intro _ _ ENOMEM_in_mmap_errnos). reflexivity.
      * rewrite (grant_na_pin_not_errno model a nZ Hn0 Ha), Ha. cbn [andb].
        rewrite (proj2 (listNN_eqb_eq _ _) eq_refl). reflexivity.
    + intros [r ws zs us cs ci] m' evs Hc. rewrite Hchk in Hc.
      destruct ws; [|discriminate]. destruct zs; [|discriminate].
      destruct cs; [|destruct us; discriminate]. destruct ci; [|destruct us; discriminate].
      destruct (errno_ret_in mmap_errnos r) eqn:Er.
      * destruct us; [|discriminate]. injection Hc as <- <-.
        destruct (proj1 (errno_ret_in_true _ _) Er) as (e & He & ->).
        rewrite (mmap_errnos_ENOMEM e He). exists (inl tt). repeat split; reflexivity.
      * destruct (grant_ok_na_pin model r nZ) eqn:Hg; [|discriminate].
        destruct (listNN_eqb us [(r, n)]) eqn:Hl; [|discriminate].
        apply listNN_eqb_eq in Hl. subst us. injection Hc as <- <-.
        exists (inr (exist _ r Hg)). repeat split; reflexivity.
    + intros [r ws zs us cs ci] Hc. rewrite Hchk in Hc.
      destruct ws; [|discriminate]. destruct zs; [|discriminate].
      destruct cs; [|destruct us; discriminate]. destruct ci; [|destruct us; discriminate].
      destruct (errno_ret_in mmap_errnos r); [destruct us; discriminate|].
      destruct (grant_ok_na_pin model r nZ && listNN_eqb us [(r, n)])%bool; discriminate.
    + intros [[] | [a Ha]]; cbn [ms']; [exact Hh | rewrite with_mmap_backing_halted; unfold noaccess_model; rewrite with_vmmaps_halted; exact Hh].
    + intros [[] | [a Ha]]; reflexivity. }
  apply (srz_cfg_chk_nonref segs ms model (getr regs 17) (unit + IB) effs ms' KB (inr (exist _ a0 Ha0)) eq_refl
           (injected_family_off_no segs ms (getr regs 17) 222 Hno eq_refl) Hnode).
  - cbn [effs eff_ret]. rewrite (refusal_b_in222 segs ms (getr regs 17) model _ Hno). exact (grant_na_pin_not_errno model a0 nZ Hn0 Ha0).
  - intros [[] | [a Ha]] Hnr.
    + exfalso. cbn [effs eff_ret] in Hnr. rewrite (refusal_b_in222 segs ms (getr regs 17) model _ Hno), (errno_ret_in_intro _ _ ENOMEM_in_mmap_errnos) in Hnr.
      discriminate Hnr.
    + cbn [effs ms']. unfold ms. rewrite adv_unmaps1_epend. apply HB. exact Ha.
Qed.

Lemma srz_cfg_mmap_fixed_rw_free2 : forall regs (pc : word) mem rom model w (addr : word) (len : Z) (flags : word) KB,
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
  srealizes_cfg segs (mkCfg (mkst (regupd regs 10 addr) (v_addi pc 4) (zfill addr n mem) rom)
                       (with_mmap_backing flags addr n (mmap_model addr n model))) KB ->
  srealizes_cfg segs (mkCfg (mkst regs pc mem rom) model) KB.
Proof.
  intros regs pc mem rom model w addr len flags KB HF HE Hh H17 H10 Hal Hpos H11 Hlen Hce Hisp H12 H13 Hcore H14 H15
         nZ n Hrf Hbk HB.
  eapply srz_cfg_sys_lazy; [exact Hh | exact HF | exact HE |].
  set (ms := epend regs pc mem rom (getr regs 17)).
  assert (Hno : bv_unsigned (getr regs 17) = 222%Z) by (rewrite H17; apply u64_lit; lia).
  pose proof (fun eff => mmap_fixed_rw_free_check ms (getr regs 17) model eff flags addr len Hno
                ltac:(unfold ms; rewrite ms_gpr_epend0; exact H10) Hal Hpos
                ltac:(unfold ms; rewrite ms_gpr_epend1; exact H11) Hlen Hce Hisp
                ltac:(unfold ms; rewrite ms_gpr_epend2; exact H12)
                ltac:(unfold ms; rewrite ms_gpr_epend3; exact H13) Hcore
                ltac:(unfold ms; rewrite ms_gpr_epend4; exact H14)
                ltac:(unfold ms; rewrite ms_gpr_epend5; exact H15) Hrf) as Hchk.
  cbv zeta in Hchk. fold nZ in Hchk. fold n in Hchk. rewrite Hbk in Hchk.
  destruct (mmap_fixed_gate_open (m_vmmaps model) addr len Hal Hpos Hlen Hce Hisp) as (_ & _ & _ & _ & _ & HnZ). fold nZ in HnZ.
  assert (Hna : errno_ret_in mmap_errnos addr = false).
  { apply errno_ret_in_below; [reflexivity|]. pose proof alloc_ceiling_val. unfold two_pow_64. lia. }
  pose (effs := fun i : unit + unit => match i with
                           | inl _ => mkEffectU (errno_ret ENOMEM) [] [] [] [] []
                           | inr _ => mkEffectU addr [] [(addr, n)] [] [] [] end).
  pose (ms' := fun i : unit + unit => match i with
                          | inl _ => model
                          | inr _ => with_mmap_backing flags addr n (mmap_model addr n model) end).
  assert (Hnode : ShapeAlg.node_ok segs (mkCfg ms model) (unit + unit) (fun _ => [])
            (fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms' i))).
  { apply (node_chk_ev_mat segs ms model (getr regs 17) (unit + unit) effs ms' (fun _ => []) Hh eq_refl).
    + intros [[] | []]; cbn [effs ms']; rewrite Hchk.
      * rewrite (errno_ret_in_intro _ _ ENOMEM_in_mmap_errnos). reflexivity.
      * rewrite Hna, bv_eqb_refl, (proj2 (listNN_eqb_eq _ _) eq_refl). reflexivity.
    + intros [r ws zs us cs ci] m' evs Hc. rewrite Hchk in Hc.
      destruct ws; [|discriminate]. destruct us; [|discriminate].
      destruct cs; [|discriminate]. destruct ci; [|discriminate].
      destruct (errno_ret_in mmap_errnos r) eqn:Er.
      * destruct zs; [|discriminate]. injection Hc as <- <-.
        destruct (proj1 (errno_ret_in_true _ _) Er) as (e & He & ->).
        rewrite (mmap_errnos_ENOMEM e He). exists (inl tt). repeat split; reflexivity.
      * destruct (bv_eqb r addr) eqn:Eb; [|discriminate].
        destruct (listNN_eqb zs [(addr, n)]) eqn:Hl; [|discriminate].
        apply bv_eqb_eq in Eb. apply listNN_eqb_eq in Hl. subst r zs. cbn [andb] in Hc. injection Hc as <- <-.
        exists (inr tt). repeat split; reflexivity.
    + intros [r ws zs us cs ci] Hc. rewrite Hchk in Hc.
      destruct ws; [|discriminate]. destruct us; [|discriminate].
      destruct cs; [|discriminate]. destruct ci; [|discriminate].
      destruct (errno_ret_in mmap_errnos r); [destruct zs; discriminate|].
      destruct (bv_eqb r addr && listNN_eqb zs [(addr, n)] && true)%bool; discriminate.
    + intros [[] | []]; cbn [ms']; [exact Hh | rewrite with_mmap_backing_halted; unfold mmap_model; rewrite with_vmmaps_halted; exact Hh].
    + intros [[] | []]; reflexivity. }
  apply (srz_cfg_chk_nonref segs ms model (getr regs 17) (unit + unit) effs ms' KB (inr tt) eq_refl
           (injected_family_off_no segs ms (getr regs 17) 222 Hno eq_refl) Hnode).
  - cbn [effs eff_ret]. rewrite (refusal_b_in222 segs ms (getr regs 17) model _ Hno). exact Hna.
  - intros [[] | []] Hnr.
    + exfalso. cbn [effs eff_ret] in Hnr. rewrite (refusal_b_in222 segs ms (getr regs 17) model _ Hno), (errno_ret_in_intro _ _ ENOMEM_in_mmap_errnos) in Hnr.
      discriminate Hnr.
    + cbn [effs ms']. unfold ms. rewrite adv_zeros1_epend. exact HB.
Qed.

Lemma srz_cfg_mmap_fixed_none_free2 : forall regs (pc : word) mem rom model w (addr : word) (len : Z) (flags : word) KB,
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
  srealizes_cfg segs (mkCfg (mkst (regupd regs 10 addr) (v_addi pc 4) (unfill addr n mem) rom)
                       (with_mmap_backing flags addr n (noaccess_model addr n model))) KB ->
  srealizes_cfg segs (mkCfg (mkst regs pc mem rom) model) KB.
Proof.
  intros regs pc mem rom model w addr len flags KB HF HE Hh H17 H10 Hal Hpos H11 Hlen Hce Hisp H12 H13 Hcore H14 H15
         nZ n Hrf HB.
  eapply srz_cfg_sys_lazy; [exact Hh | exact HF | exact HE |].
  set (ms := epend regs pc mem rom (getr regs 17)).
  assert (Hno : bv_unsigned (getr regs 17) = 222%Z) by (rewrite H17; apply u64_lit; lia).
  pose proof (fun eff => mmap_fixed_none_free_check ms (getr regs 17) model eff flags addr len Hno
                ltac:(unfold ms; rewrite ms_gpr_epend0; exact H10) Hal Hpos
                ltac:(unfold ms; rewrite ms_gpr_epend1; exact H11) Hlen Hce Hisp
                ltac:(unfold ms; rewrite ms_gpr_epend2; exact H12)
                ltac:(unfold ms; rewrite ms_gpr_epend3; exact H13) Hcore
                ltac:(unfold ms; rewrite ms_gpr_epend4; exact H14)
                ltac:(unfold ms; rewrite ms_gpr_epend5; exact H15) Hrf) as Hchk.
  cbv zeta in Hchk. fold nZ in Hchk. fold n in Hchk.
  destruct (mmap_fixed_gate_open (m_vmmaps model) addr len Hal Hpos Hlen Hce Hisp) as (_ & _ & _ & _ & _ & HnZ). fold nZ in HnZ.
  assert (Hna : errno_ret_in mmap_errnos addr = false).
  { apply errno_ret_in_below; [reflexivity|]. pose proof alloc_ceiling_val. unfold two_pow_64. lia. }
  pose (effs := fun i : unit + unit => match i with
                           | inl _ => mkEffectU (errno_ret ENOMEM) [] [] [] [] []
                           | inr _ => mkEffectU addr [] [] [(addr, n)] [] [] end).
  pose (ms' := fun i : unit + unit => match i with
                          | inl _ => model
                          | inr _ => with_mmap_backing flags addr n (noaccess_model addr n model) end).
  assert (Hnode : ShapeAlg.node_ok segs (mkCfg ms model) (unit + unit) (fun _ => [])
            (fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms' i))).
  { apply (node_chk_ev_mat segs ms model (getr regs 17) (unit + unit) effs ms' (fun _ => []) Hh eq_refl).
    + intros [[] | []]; cbn [effs ms']; rewrite Hchk.
      * rewrite (errno_ret_in_intro _ _ ENOMEM_in_mmap_errnos). reflexivity.
      * rewrite Hna, bv_eqb_refl, (proj2 (listNN_eqb_eq _ _) eq_refl). reflexivity.
    + intros [r ws zs us cs ci] m' evs Hc. rewrite Hchk in Hc.
      destruct ws; [|discriminate]. destruct zs; [|discriminate].
      destruct cs; [|destruct us; discriminate]. destruct ci; [|destruct us; discriminate].
      destruct (errno_ret_in mmap_errnos r) eqn:Er.
      * destruct us; [|discriminate]. injection Hc as <- <-.
        destruct (proj1 (errno_ret_in_true _ _) Er) as (e & He & ->).
        rewrite (mmap_errnos_ENOMEM e He). exists (inl tt). repeat split; reflexivity.
      * destruct (bv_eqb r addr) eqn:Eb; [|discriminate].
        destruct (listNN_eqb us [(addr, n)]) eqn:Hl; [|discriminate].
        apply bv_eqb_eq in Eb. apply listNN_eqb_eq in Hl. subst r us. injection Hc as <- <-.
        exists (inr tt). repeat split; reflexivity.
    + intros [r ws zs us cs ci] Hc. rewrite Hchk in Hc.
      destruct ws; [|discriminate]. destruct zs; [|discriminate].
      destruct cs; [|destruct us; discriminate]. destruct ci; [|destruct us; discriminate].
      destruct (errno_ret_in mmap_errnos r); [destruct us; discriminate|].
      destruct (bv_eqb r addr && listNN_eqb us [(addr, n)])%bool; discriminate.
    + intros [[] | []]; cbn [ms']; [exact Hh | rewrite with_mmap_backing_halted; unfold noaccess_model; rewrite with_vmmaps_halted; exact Hh].
    + intros [[] | []]; reflexivity. }
  apply (srz_cfg_chk_nonref segs ms model (getr regs 17) (unit + unit) effs ms' KB (inr tt) eq_refl
           (injected_family_off_no segs ms (getr regs 17) 222 Hno eq_refl) Hnode).
  - cbn [effs eff_ret]. rewrite (refusal_b_in222 segs ms (getr regs 17) model _ Hno). exact Hna.
  - intros [[] | []] Hnr.
    + exfalso. cbn [effs eff_ret] in Hnr. rewrite (refusal_b_in222 segs ms (getr regs 17) model _ Hno), (errno_ret_in_intro _ _ ENOMEM_in_mmap_errnos) in Hnr.
      discriminate Hnr.
    + cbn [effs ms']. unfold ms. rewrite adv_unmaps1_epend. exact HB.
Qed.

Lemma srz_cfg_mprotect2 : forall regs (pc : word) mem rom model w (addr : word) (len : Z) KB,
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
  srealizes_cfg segs (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 0)) (v_addi pc 4) (zfill addr n mem) rom)
                       (mprotect_model addr n model)) KB ->
  srealizes_cfg segs (mkCfg (mkst regs pc mem rom) model) KB.
Proof.
  intros regs pc mem rom model w addr len KB HF HE Hh H17 H10 Hal H11 Hlen Hnw H12 n Hna Hma Hbud HB.
  eapply srz_cfg_sys_lazy; [exact Hh | exact HF | exact HE |].
  set (ms := epend regs pc mem rom (getr regs 17)).
  assert (Hno : bv_unsigned (getr regs 17) = 226%Z) by (rewrite H17; apply u64_lit; lia).
  pose proof (fun eff => mprotect_check segs ms (getr regs 17) model eff addr len Hno
                           ltac:(unfold ms; rewrite ms_gpr_epend0; exact H10) Hal
                           ltac:(unfold ms; rewrite ms_gpr_epend1; exact H11) Hlen Hnw
                           ltac:(unfold ms; rewrite ms_gpr_epend2; exact H12) Hna Hma) as Hchk.
  cbv zeta in Hchk. fold n in Hchk. rewrite Hbud in Hchk.
  pose (effs := fun i : unit + unit => match i with
                           | inl _ => mkEffectU (errno_ret ENOMEM) [] [] [] [] []
                           | inr _ => mkEffectU (Z_to_bv 64 0) [] [(addr, n)] [] [] [] end).
  pose (ms' := fun i : unit + unit => match i with inl _ => model | inr _ => mprotect_model addr n model end).
  assert (Hnode : ShapeAlg.node_ok segs (mkCfg ms model) (unit + unit) (fun _ => [])
            (fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms' i))).
  { apply (node_chk_ev_mat segs ms model (getr regs 17) (unit + unit) effs ms' (fun _ => []) Hh eq_refl).
    + intros [[] | []]; cbn [effs ms']; rewrite Hchk.
      * rewrite (errno_ret_in_intro _ _ ENOMEM_in_mprotect_errnos). reflexivity.
      * change (errno_ret_in mprotect_errnos (Z_to_bv 64 0)) with false.
        unfold w_is0. rewrite bv_eqb_refl. rewrite (proj2 (listNN_eqb_eq _ _) eq_refl). reflexivity.
    + intros [r ws zs us cs ci] m' evs Hc. rewrite Hchk in Hc.
      destruct ws; [|discriminate]. destruct us; [|discriminate].
      destruct cs; [|discriminate]. destruct ci; [|discriminate].
      destruct (errno_ret_in mprotect_errnos r) eqn:Er.
      * destruct zs; [|discriminate]. injection Hc as <- <-.
        destruct (proj1 (errno_ret_in_true _ _) Er) as (e & He & ->).
        rewrite (mprotect_errnos_ENOMEM e He). exists (inl tt). repeat split; reflexivity.
      * cbn [andb] in Hc. destruct (w_is0 r) eqn:E0; [|discriminate].
        destruct (listNN_eqb zs [(addr, n)]) eqn:Hl; [|discriminate].
        apply listNN_eqb_eq in Hl. subst zs. injection Hc as <- <-.
        unfold w_is0 in E0. apply bv_eqb_eq in E0. subst r.
        exists (inr tt). repeat split; reflexivity.
    + intros [r ws zs us cs ci] Hc. rewrite Hchk in Hc.
      destruct ws; [|discriminate]. destruct us; [|discriminate].
      destruct cs; [|discriminate]. destruct ci; [|discriminate].
      destruct (errno_ret_in mprotect_errnos r); [destruct zs; discriminate|].
      cbn [andb] in Hc. destruct (w_is0 r && listNN_eqb zs [(addr, n)])%bool; discriminate.
    + intros [[] | []]; cbn [ms']; [exact Hh | unfold mprotect_model; rewrite with_vmmaps_halted; exact Hh].
    + intros [[] | []]; reflexivity. }
  apply (srz_cfg_chk_nonref segs ms model (getr regs 17) (unit + unit) effs ms' KB (inr tt) eq_refl
           (injected_family_off_no segs ms (getr regs 17) 226 Hno eq_refl) Hnode).
  - cbn [effs eff_ret]. rewrite (refusal_b_in226 segs ms (getr regs 17) model _ Hno). reflexivity.
  - intros [[] | []] Hnr.
    + exfalso. cbn [effs eff_ret] in Hnr. rewrite (refusal_b_in226 segs ms (getr regs 17) model _ Hno), (errno_ret_in_intro _ _ ENOMEM_in_mprotect_errnos) in Hnr.
      discriminate Hnr.
    + cbn [effs ms']. unfold ms. rewrite adv_zeros1_epend. exact HB.
Qed.

Lemma srz_cfg_mmap_noreplace_rw_free2 : forall regs (pc : word) mem rom model w (addr : word) (len : Z) (flags : word) KB,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None ->
  getr regs 17 = Z_to_bv 64 222 ->
  getr regs 10 = addr -> (bv_unsigned addr mod page_size = 0)%Z -> (0 < bv_unsigned addr)%Z ->
  getr regs 11 = Z_to_bv 64 len -> (0 < len)%Z ->
  (bv_unsigned addr + page_round_up_Z len <= alloc_ceiling)%Z -> init_sp_ok (m_vmmaps model) ->
  getr regs 12 = Z_to_bv 64 3 -> getr regs 13 = flags -> nr_core flags ->
  getr regs 14 = Z_to_bv 64 (-1) -> getr regs 15 = Z_to_bv 64 0 ->
  let nZ := page_round_up_Z len in let n := Z_to_bv 64 nZ in
  region_free (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model)) addr n = true ->
  mmap_noreserve_backed_ok flags model nZ = true ->
  srealizes_cfg segs (mkCfg (mkst (regupd regs 10 addr) (v_addi pc 4) (zfill addr n mem) rom)
                       (with_mmap_backing flags addr n (mmap_model addr n model))) KB ->
  srealizes_cfg segs (mkCfg (mkst regs pc mem rom) model) KB.
Proof.
  intros regs pc mem rom model w addr len flags KB HF HE Hh H17 H10 Hal Hpos H11 Hlen Hce Hisp H12 H13 Hcore H14 H15
         nZ n Hrf Hbk HB.
  eapply srz_cfg_sys_lazy; [exact Hh | exact HF | exact HE |].
  set (ms := epend regs pc mem rom (getr regs 17)).
  assert (Hno : bv_unsigned (getr regs 17) = 222%Z) by (rewrite H17; apply u64_lit; lia).
  pose proof (fun eff => mmap_noreplace_rw_free_check ms (getr regs 17) model eff flags addr len Hno
                ltac:(unfold ms; rewrite ms_gpr_epend0; exact H10) Hal Hpos
                ltac:(unfold ms; rewrite ms_gpr_epend1; exact H11) Hlen Hce Hisp
                ltac:(unfold ms; rewrite ms_gpr_epend2; exact H12)
                ltac:(unfold ms; rewrite ms_gpr_epend3; exact H13) Hcore
                ltac:(unfold ms; rewrite ms_gpr_epend4; exact H14)
                ltac:(unfold ms; rewrite ms_gpr_epend5; exact H15) Hrf) as Hchk.
  cbv zeta in Hchk. fold nZ in Hchk. fold n in Hchk. rewrite Hbk in Hchk.
  destruct (mmap_fixed_gate_open (m_vmmaps model) addr len Hal Hpos Hlen Hce Hisp) as (_ & _ & _ & _ & _ & HnZ). fold nZ in HnZ.
  assert (Hna : errno_ret_in mmap_errnos addr = false).
  { apply errno_ret_in_below; [reflexivity|]. pose proof alloc_ceiling_val. unfold two_pow_64. lia. }
  pose (effs := fun i : unit + unit => match i with
                           | inl _ => mkEffectU (errno_ret ENOMEM) [] [] [] [] []
                           | inr _ => mkEffectU addr [] [(addr, n)] [] [] [] end).
  pose (ms' := fun i : unit + unit => match i with
                          | inl _ => model
                          | inr _ => with_mmap_backing flags addr n (mmap_model addr n model) end).
  assert (Hnode : ShapeAlg.node_ok segs (mkCfg ms model) (unit + unit) (fun _ => [])
            (fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms' i))).
  { apply (node_chk_ev_mat segs ms model (getr regs 17) (unit + unit) effs ms' (fun _ => []) Hh eq_refl).
    + intros [[] | []]; cbn [effs ms']; rewrite Hchk.
      * rewrite (errno_ret_in_intro _ _ ENOMEM_in_mmap_errnos). reflexivity.
      * rewrite Hna, bv_eqb_refl, (proj2 (listNN_eqb_eq _ _) eq_refl). reflexivity.
    + intros [r ws zs us cs ci] m' evs Hc. rewrite Hchk in Hc.
      destruct ws; [|discriminate]. destruct us; [|discriminate].
      destruct cs; [|discriminate]. destruct ci; [|discriminate].
      destruct (errno_ret_in mmap_errnos r) eqn:Er.
      * destruct zs; [|discriminate]. injection Hc as <- <-.
        destruct (proj1 (errno_ret_in_true _ _) Er) as (e & He & ->).
        rewrite (mmap_errnos_ENOMEM e He). exists (inl tt). repeat split; reflexivity.
      * destruct (bv_eqb r addr) eqn:Eb; [|discriminate].
        destruct (listNN_eqb zs [(addr, n)]) eqn:Hl; [|discriminate].
        apply bv_eqb_eq in Eb. apply listNN_eqb_eq in Hl. subst r zs. cbn [andb] in Hc. injection Hc as <- <-.
        exists (inr tt). repeat split; reflexivity.
    + intros [r ws zs us cs ci] Hc. rewrite Hchk in Hc.
      destruct ws; [|discriminate]. destruct us; [|discriminate].
      destruct cs; [|discriminate]. destruct ci; [|discriminate].
      destruct (errno_ret_in mmap_errnos r); [destruct zs; discriminate|].
      destruct (bv_eqb r addr && listNN_eqb zs [(addr, n)] && true)%bool; discriminate.
    + intros [[] | []]; cbn [ms']; [exact Hh | rewrite with_mmap_backing_halted; unfold mmap_model; rewrite with_vmmaps_halted; exact Hh].
    + intros [[] | []]; reflexivity. }
  apply (srz_cfg_chk_nonref segs ms model (getr regs 17) (unit + unit) effs ms' KB (inr tt) eq_refl
           (injected_family_off_no segs ms (getr regs 17) 222 Hno eq_refl) Hnode).
  - cbn [effs eff_ret]. rewrite (refusal_b_in222 segs ms (getr regs 17) model _ Hno). exact Hna.
  - intros [[] | []] Hnr.
    + exfalso. cbn [effs eff_ret] in Hnr. rewrite (refusal_b_in222 segs ms (getr regs 17) model _ Hno), (errno_ret_in_intro _ _ ENOMEM_in_mmap_errnos) in Hnr.
      discriminate Hnr.
    + cbn [effs ms']. unfold ms. rewrite adv_zeros1_epend. exact HB.
Qed.

Lemma srz_cfg_mmap_noreplace_none_free2 : forall regs (pc : word) mem rom model w (addr : word) (len : Z) (flags : word) KB,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None ->
  getr regs 17 = Z_to_bv 64 222 ->
  getr regs 10 = addr -> (bv_unsigned addr mod page_size = 0)%Z -> (0 < bv_unsigned addr)%Z ->
  getr regs 11 = Z_to_bv 64 len -> (0 < len)%Z ->
  (bv_unsigned addr + page_round_up_Z len <= alloc_ceiling)%Z -> init_sp_ok (m_vmmaps model) ->
  getr regs 12 = Z_to_bv 64 0 -> getr regs 13 = flags -> nr_core flags ->
  getr regs 14 = Z_to_bv 64 (-1) -> getr regs 15 = Z_to_bv 64 0 ->
  let nZ := page_round_up_Z len in let n := Z_to_bv 64 nZ in
  region_free (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model)) addr n = true ->
  srealizes_cfg segs (mkCfg (mkst (regupd regs 10 addr) (v_addi pc 4) (unfill addr n mem) rom)
                       (with_mmap_backing flags addr n (noaccess_model addr n model))) KB ->
  srealizes_cfg segs (mkCfg (mkst regs pc mem rom) model) KB.
Proof.
  intros regs pc mem rom model w addr len flags KB HF HE Hh H17 H10 Hal Hpos H11 Hlen Hce Hisp H12 H13 Hcore H14 H15
         nZ n Hrf HB.
  eapply srz_cfg_sys_lazy; [exact Hh | exact HF | exact HE |].
  set (ms := epend regs pc mem rom (getr regs 17)).
  assert (Hno : bv_unsigned (getr regs 17) = 222%Z) by (rewrite H17; apply u64_lit; lia).
  pose proof (fun eff => mmap_noreplace_none_free_check ms (getr regs 17) model eff flags addr len Hno
                ltac:(unfold ms; rewrite ms_gpr_epend0; exact H10) Hal Hpos
                ltac:(unfold ms; rewrite ms_gpr_epend1; exact H11) Hlen Hce Hisp
                ltac:(unfold ms; rewrite ms_gpr_epend2; exact H12)
                ltac:(unfold ms; rewrite ms_gpr_epend3; exact H13) Hcore
                ltac:(unfold ms; rewrite ms_gpr_epend4; exact H14)
                ltac:(unfold ms; rewrite ms_gpr_epend5; exact H15) Hrf) as Hchk.
  cbv zeta in Hchk. fold nZ in Hchk. fold n in Hchk.
  destruct (mmap_fixed_gate_open (m_vmmaps model) addr len Hal Hpos Hlen Hce Hisp) as (_ & _ & _ & _ & _ & HnZ). fold nZ in HnZ.
  assert (Hna : errno_ret_in mmap_errnos addr = false).
  { apply errno_ret_in_below; [reflexivity|]. pose proof alloc_ceiling_val. unfold two_pow_64. lia. }
  pose (effs := fun i : unit + unit => match i with
                           | inl _ => mkEffectU (errno_ret ENOMEM) [] [] [] [] []
                           | inr _ => mkEffectU addr [] [] [(addr, n)] [] [] end).
  pose (ms' := fun i : unit + unit => match i with
                          | inl _ => model
                          | inr _ => with_mmap_backing flags addr n (noaccess_model addr n model) end).
  assert (Hnode : ShapeAlg.node_ok segs (mkCfg ms model) (unit + unit) (fun _ => [])
            (fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms' i))).
  { apply (node_chk_ev_mat segs ms model (getr regs 17) (unit + unit) effs ms' (fun _ => []) Hh eq_refl).
    + intros [[] | []]; cbn [effs ms']; rewrite Hchk.
      * rewrite (errno_ret_in_intro _ _ ENOMEM_in_mmap_errnos). reflexivity.
      * rewrite Hna, bv_eqb_refl, (proj2 (listNN_eqb_eq _ _) eq_refl). reflexivity.
    + intros [r ws zs us cs ci] m' evs Hc. rewrite Hchk in Hc.
      destruct ws; [|discriminate]. destruct zs; [|discriminate].
      destruct cs; [|destruct us; discriminate]. destruct ci; [|destruct us; discriminate].
      destruct (errno_ret_in mmap_errnos r) eqn:Er.
      * destruct us; [|discriminate]. injection Hc as <- <-.
        destruct (proj1 (errno_ret_in_true _ _) Er) as (e & He & ->).
        rewrite (mmap_errnos_ENOMEM e He). exists (inl tt). repeat split; reflexivity.
      * destruct (bv_eqb r addr) eqn:Eb; [|discriminate].
        destruct (listNN_eqb us [(addr, n)]) eqn:Hl; [|discriminate].
        apply bv_eqb_eq in Eb. apply listNN_eqb_eq in Hl. subst r us. injection Hc as <- <-.
        exists (inr tt). repeat split; reflexivity.
    + intros [r ws zs us cs ci] Hc. rewrite Hchk in Hc.
      destruct ws; [|discriminate]. destruct zs; [|discriminate].
      destruct cs; [|destruct us; discriminate]. destruct ci; [|destruct us; discriminate].
      destruct (errno_ret_in mmap_errnos r); [destruct us; discriminate|].
      destruct (bv_eqb r addr && listNN_eqb us [(addr, n)])%bool; discriminate.
    + intros [[] | []]; cbn [ms']; [exact Hh | rewrite with_mmap_backing_halted; unfold noaccess_model; rewrite with_vmmaps_halted; exact Hh].
    + intros [[] | []]; reflexivity. }
  apply (srz_cfg_chk_nonref segs ms model (getr regs 17) (unit + unit) effs ms' KB (inr tt) eq_refl
           (injected_family_off_no segs ms (getr regs 17) 222 Hno eq_refl) Hnode).
  - cbn [effs eff_ret]. rewrite (refusal_b_in222 segs ms (getr regs 17) model _ Hno). exact Hna.
  - intros [[] | []] Hnr.
    + exfalso. cbn [effs eff_ret] in Hnr. rewrite (refusal_b_in222 segs ms (getr regs 17) model _ Hno), (errno_ret_in_intro _ _ ENOMEM_in_mmap_errnos) in Hnr.
      discriminate Hnr.
    + cbn [effs ms']. unfold ms. rewrite adv_unmaps1_epend. exact HB.
Qed.

End WithFPmm.
