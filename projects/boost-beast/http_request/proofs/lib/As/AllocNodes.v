(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.boost_beast.http_request.lib.Common Require KReplay.
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import Scfg Amb RelSpec
  SimInv ExitSim PropExec CatExec CatSim SeqExec StreamExec MmapSim AllocSim FileSim
  ShapeAlg Nodes StoreOk AgentLib AgentNodes Gap04 RefNodes.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section ModelLevel.
  Context {SC : StepCfg}.

  (* [comment removed for export] *)
  Lemma mmap_grant_not_refusal : forall i m hint a nZ,
    bv_unsigned (in_sysno i) = 222%Z ->
    grant_ok hint m a nZ = true -> (0 <= nZ)%Z ->
    refusal_b i m a = false.
  Proof.
    intros i m hint a nZ Hno Hg HnZ. rewrite (refusal_b_mmap i m a Hno).
    apply bv_eqb_neq. apply (grant_ok_not_errno hint m a nZ ENOMEM Hg HnZ). unfold ENOMEM. lia.
  Qed.

  Lemma place_not_refusal : forall i m a nZ,
    bv_unsigned (in_sysno i) = 222%Z ->
    place_ok (m_vmmaps m) a nZ = true -> (0 <= nZ)%Z ->
    refusal_b i m a = false.
  Proof.
    intros i m a nZ Hno Hp HnZ. rewrite (refusal_b_mmap i m a Hno).
    apply bv_eqb_neq. intros ->.
    destruct (place_ok_unpack _ _ _ Hp) as (_ & _ & Htop & _).
    pose proof (alloc_top_lt (m_vmmaps m)) as Hlt.
    rewrite (errno_ret_unsigned ENOMEM) in Htop by (unfold ENOMEM; lia).
    unfold ENOMEM, alloc_top, stack_max_size, two_pow_64 in *.
    pose proof (word_unsigned_range (vm_init_sp (m_vmmaps m))). unfold two_pow_64 in *. lia.
  Qed.

  Lemma errno_is_refusal_mmap : forall i m,
    bv_unsigned (in_sysno i) = 222%Z ->
    refusal_b i m (errno_ret ENOMEM) = true.
  Proof. intros i m Hno. rewrite (refusal_b_mmap i m _ Hno). apply bv_eqb_refl. Qed.

  Lemma errno_is_refusal_mprotect : forall i m,
    bv_unsigned (in_sysno i) = 226%Z ->
    refusal_b i m (errno_ret ENOMEM) = true.
  Proof. intros i m Hno. rewrite (refusal_b_mprotect i m _ Hno). apply bv_eqb_refl. Qed.

  Lemma zero_not_refusal_mprotect : forall i m,
    bv_unsigned (in_sysno i) = 226%Z ->
    refusal_b i m (Z_to_bv 64 0) = false.
  Proof.
    intros i m Hno. rewrite (refusal_b_mprotect i m _ Hno). apply bv_eqb_neq.
    intros E. apply (f_equal bv_unsigned) in E. rewrite (errno_ret_unsigned ENOMEM) in E by (unfold ENOMEM; lia).
    change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in E. unfold ENOMEM, two_pow_64 in E. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma alloc_refusal_spurious {AF : AllocForced SC} : forall i m eff eff' m' evs',
    injected_family_off the_scfg i = true ->
    refusal_b i m (eff_ret eff) = true ->
    syscall_spec i m (Ok eff' m' evs') ->
    refusal_b i m (eff_ret eff') = false ->
    spurious_refusal_cfg the_scfg i m eff.
  Proof.
    intros i m eff eff' m' evs' Hoff Hr Hspec Hnr. split; [exact Hoff|]. split; [exact Hr|].
    exists eff', m', evs'. auto.
  Qed.
End ModelLevel.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section WithSegs.
Variable segs : list Segment.
Context {SC : StepCfg} {AF : AllocForced SC}.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma node_mmap_grant : forall ms model x8,
  m_halted model = None -> m_vm_lazy model = [] ->
  ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 222%Z ->
  mmap_args_ok ms ->
  let nZ := page_round_up_Z (bv_unsigned (ms_gpr ms 1)) in
  let n := page_round_up (ms_gpr ms 1) in
  (exists a, grant_ok (ms_gpr ms 0) model a nZ = true) ->
  node_ok segs (mkCfg ms model) {a : word | grant_ok (ms_gpr ms 0) model a nZ = true} (fun _ => [])
    (fun i => mkCfg (advance_past_svc (apply_effect ms (mkEffect (proj1_sig i) [] [(proj1_sig i, n)])))
                    (mmap_model (proj1_sig i) n model)).
Proof.
  intros ms model x8 Hh Hlazy Hsvc Hno Hargs nZ n (a0 & Ha0).
  assert (HnZ : (0 <= nZ)%Z).
  { unfold nZ. apply page_round_up_Z_nonneg. apply (proj1 (word_unsigned_range _)). }
  assert (Hno' : bv_unsigned (in_sysno (sys_input segs ms x8)) = 222%Z) by (rewrite in_sysno_sys_input; exact Hno).
  apply (node_family_cfg segs ms model x8 {a : word | grant_ok (ms_gpr ms 0) model a nZ = true}
           (fun i => mkEffect (proj1_sig i) [] [(proj1_sig i, n)])
           (fun i => mmap_model (proj1_sig i) n model) (fun _ => []) _
           Hh Hsvc (fun o => mmap_outcome_si segs ms x8 model o Hno Hargs)).
  - intros [a Ha]. right. exists a. split; [exact Ha | reflexivity].
  - intros [a Ha]. apply spurious_refusal_not_refusal. cbn [proj1_sig eff_ret].
    exact (mmap_grant_not_refusal _ model (ms_gpr ms 0) a nZ Hno' Ha HnZ).
  - intros eff m' ev [He | (a & Ha & E)] Hns.
    + exfalso. apply Hns. apply mmap_err_out_enomem in He. apply Ok_inj in He as (-> & -> & ->).
      apply (alloc_refusal_spurious _ model _ (mkEffect a0 [] [(a0, n)]) (mmap_model a0 n model) []).
      * apply family_off_mmap_true. exact Hno'.
      * cbn [eff_ret]. apply errno_is_refusal_mmap. exact Hno'.
      * apply (mmap_succ_ok segs ms x8 model a0 Hno Hargs Ha0).
      * cbn [eff_ret]. exact (mmap_grant_not_refusal _ model (ms_gpr ms 0) a0 nZ Hno' Ha0 HnZ).
    + apply Ok_inj in E as (-> & -> & ->). exists (exist _ a Ha). cbn [proj1_sig]. auto.
  - intros eff m' ev [He | (a & Ha & E)].
    + apply mmap_err_out_enomem in He. apply Ok_inj in He as (-> & -> & ->). exact Hh.
    + apply Ok_inj in E as (-> & -> & ->). rewrite mmap_model_halted. exact Hh.
  - intros [He | (a & _ & E)]; [apply mmap_err_out_enomem in He; discriminate He | discriminate E].
  - intros [a Ha]. rewrite mmap_model_lazy. exact Hlazy.
Qed.

Lemma rz_mmap : forall ms model x8 B,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 222%Z ->
  mmap_args_ok ms ->
  (exists a, grant_ok (ms_gpr ms 0) model a (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true) ->
  (forall a, grant_ok (ms_gpr ms 0) model a (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true ->
     realizes segs (mkCfg (advance_past_svc
                            (apply_effect ms (mkEffect a [] [(a, page_round_up (ms_gpr ms 1))])))
                          (mmap_model a (page_round_up (ms_gpr ms 1)) model)) B) ->
  realizes segs (mkCfg ms model) B.
Proof.
  intros ms model x8 B Hh Hlazy Hsvc Hno Hargs Hex HB.
  destruct Hex as [a0 Ha0].
  apply (rz_conseq segs (mkCfg ms model) (t_alt (fun _ : {a : word | grant_ok (ms_gpr ms 0) model a (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true} => B))).
  - eapply (rz_cases segs _ _ _ (fun _ => B) (exist _ a0 Ha0)).
    + apply (node_mmap_grant ms model x8 Hh Hlazy Hsvc Hno Hargs). exists a0. exact Ha0.
    + intros [a Ha]. cbn [proj1_sig]. apply HB. exact Ha.
  - intros tr. split; [intros [_ Ht]; exact Ht | intros Ht; exists (exist _ a0 Ha0); exact Ht].
Qed.

(* [comment removed for export] *)
Lemma node_mmap_refused : forall ms model x8,
  m_halted model = None -> m_vm_lazy model = [] ->
  ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 222%Z ->
  mmap_args_ok ms ->
  (forall a, grant_ok (ms_gpr ms 0) model a (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = false) ->
  node_ok segs (mkCfg ms model) unit (fun _ => [])
    (fun _ => mkCfg (advance_past_svc (set_gpr0 ms (errno_ret ENOMEM))) model).
Proof.
  intros ms model x8 Hh Hlazy Hsvc Hno Hargs Hng.
  rewrite <- (apply_effect_no_write ms (errno_ret ENOMEM)).
  apply (node_det segs ms model x8 (mkEffect (errno_ret ENOMEM) [] []) model []); try assumption.
  intros o. pose proof (mmap_outcome_si segs ms x8 model o Hno Hargs) as Hsi. cbv zeta in Hsi. rewrite Hsi. rewrite mmap_err_out_enomem.
  split; [| intros ->; left; reflexivity].
  intros [-> | (a & Ha & _)]; [reflexivity | rewrite Hng in Ha; discriminate Ha].
Qed.

Lemma rz_mmap_refused : forall ms model x8 A,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 222%Z ->
  mmap_args_ok ms ->
  (forall a, grant_ok (ms_gpr ms 0) model a (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = false) ->
  (forall e, In e mmap_errnos ->
     realizes segs (mkCfg (advance_past_svc (set_gpr0 ms (errno_ret e))) model) A) ->
  realizes segs (mkCfg ms model) A.
Proof.
  intros ms model x8 A Hh Hlazy Hsvc Hno Hargs Hng HA.
  eapply rz_silent1; [eapply node_mmap_refused; eassumption | apply HA; left; reflexivity].
Qed.

(* [comment removed for export] *)
Lemma no_grant_over_budget : forall hint model nZ,
  (vm_limit (m_vmmaps model) < vm_backing_used model + nZ)%Z ->
  forall a, grant_ok hint model a nZ = false.
Proof. intros hint model nZ H a. apply grant_ok_over_budget. exact H. Qed.

(* [comment removed for export] *)

Lemma mmap_noaccess_args_gates : forall ms,
  mmap_noaccess_args_ok ms ->
  mmap_off_aligned_b (ms_gpr ms 5) = true /\ mmap_anon_b (ms_gpr ms 3) = true /\
  w_is0 (ms_gpr ms 1) = false /\
  mmap_modeled_b (ms_gpr ms 2) (ms_gpr ms 3) (ms_gpr ms 5) = false /\
  mmap_noaccess_b (ms_gpr ms 2) (ms_gpr ms 3) (ms_gpr ms 5) = true.
Proof.
  intros ms (H1 & H2 & H3 & H4 & H5). rewrite H2, H3, H5.
  split; [vm_compute; reflexivity|]. split; [vm_compute; reflexivity|].
  split; [unfold w_is0; apply bv_eqb_neq; exact H1|]. split; vm_compute; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma mmap_noaccess_outcome_si : forall ms x8 model,
  bv_unsigned x8 = 222%Z -> mmap_noaccess_args_ok ms ->
  let nZ := page_round_up_Z (bv_unsigned (ms_gpr ms 1)) in
  let n := page_round_up (ms_gpr ms 1) in
  forall o, syscall_spec (sys_input segs ms x8) model o <->
    mmap_err_out model o
    \/ exists a, grant_ok_na (ms_gpr ms 0) model a nZ = true
                 /\ o = Ok (mkEffectU a [] [] [(a, n)] [] []) (noaccess_model a n model) [].
Proof.
  intros ms x8 model Hno Hargs nZ n o.
  destruct (mmap_noaccess_args_gates ms Hargs) as (Hoff & Hanon & Hl & Hmb & Hna).
  destruct Hargs as (_ & _ & H3 & _ & _).
  rewrite (syscall_spec_222 _ model o) by (rewrite in_sysno_sys_input; exact Hno).
  rewrite in_arg0_si, in_arg1_si, in_arg2_si,
          in_arg3_sys_input, in_arg4_sys_input, in_arg5_sys_input.
  rewrite (mmap_noaccess_outcome _ _ _ _ _ _ _ model o Hoff Hanon Hl Hmb Hna).
  rewrite H3. unfold grant_ok_na, place_ok, noaccess_model. fold nZ. fold n.
  split.
  - intros [He | (a & (G1 & G2 & G3 & G4) & ->)]; [left; exact He | right].
    exists a. rewrite with_mmap_backing_34.
    rewrite (proj2 (Z.eqb_eq _ _) G1), (proj2 (Z.ltb_lt _ _) G2), (proj2 (Z.leb_le _ _) G3), G4.
    split; reflexivity.
  - intros [He | (a & Hg & ->)]; [left; exact He | right].
    exists a. rewrite with_mmap_backing_34.
    rewrite !andb_true_iff in Hg. destruct Hg as [[[G1 G2] G3] G4].
    apply Z.eqb_eq in G1. apply Z.ltb_lt in G2. apply Z.leb_le in G3.
    split; [repeat split; assumption | reflexivity].
Qed.

Lemma node_mmap_noaccess_grant : forall ms model x8,
  m_halted model = None -> m_vm_lazy model = [] ->
  ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 222%Z ->
  mmap_noaccess_args_ok ms ->
  let nZ := page_round_up_Z (bv_unsigned (ms_gpr ms 1)) in
  let n := page_round_up (ms_gpr ms 1) in
  (exists a, grant_ok_na (ms_gpr ms 0) model a nZ = true) ->
  node_ok segs (mkCfg ms model) {a : word | grant_ok_na (ms_gpr ms 0) model a nZ = true} (fun _ => [])
    (fun i => mkCfg (advance_past_svc (apply_effect ms (mkEffectU (proj1_sig i) [] [] [(proj1_sig i, n)] [] [])))
                    (noaccess_model (proj1_sig i) n model)).
Proof.
  intros ms model x8 Hh Hlazy Hsvc Hno Hargs nZ n (a0 & Ha0).
  assert (HnZ : (0 <= nZ)%Z).
  { unfold nZ. apply page_round_up_Z_nonneg. apply (proj1 (word_unsigned_range _)). }
  assert (Hno' : bv_unsigned (in_sysno (sys_input segs ms x8)) = 222%Z) by (rewrite in_sysno_sys_input; exact Hno).
  pose proof (mmap_noaccess_outcome_si ms x8 model Hno Hargs) as Hsi. cbv zeta in Hsi. fold nZ n in Hsi.
  apply (node_family_cfg segs ms model x8 {a : word | grant_ok_na (ms_gpr ms 0) model a nZ = true}
           (fun i => mkEffectU (proj1_sig i) [] [] [(proj1_sig i, n)] [] [])
           (fun i => noaccess_model (proj1_sig i) n model) (fun _ => []) _
           Hh Hsvc Hsi).
  - intros [a Ha]. right. exists a. split; [exact Ha | reflexivity].
  - intros [a Ha]. apply spurious_refusal_not_refusal. cbn [proj1_sig eff_ret].
    exact (place_not_refusal _ model a nZ Hno' Ha HnZ).
  - intros eff m' ev [He | (a & Ha & E)] Hns.
    + exfalso. apply Hns. apply mmap_err_out_enomem in He. apply Ok_inj in He as (-> & -> & ->).
      apply (alloc_refusal_spurious _ model _ (mkEffectU a0 [] [] [(a0, n)] [] []) (noaccess_model a0 n model) []).
      * apply family_off_mmap_true. exact Hno'.
      * cbn [eff_ret]. apply errno_is_refusal_mmap. exact Hno'.
      * apply (proj2 (Hsi _)). right. exists a0. auto.
      * cbn [eff_ret]. exact (place_not_refusal _ model a0 nZ Hno' Ha0 HnZ).
    + apply Ok_inj in E as (-> & -> & ->). exists (exist _ a Ha). cbn [proj1_sig]. auto.
  - intros eff m' ev [He | (a & _ & E)].
    + apply mmap_err_out_enomem in He. apply Ok_inj in He as (-> & -> & ->). exact Hh.
    + apply Ok_inj in E as (-> & -> & ->). exact Hh.
  - intros [He | (a & _ & E)]; [apply mmap_err_out_enomem in He; discriminate He | discriminate E].
  - intros [a Ha]. unfold noaccess_model. rewrite with_vmmaps_lazy'. exact Hlazy.
Qed.

Lemma node_mmap_noaccess_refused : forall ms model x8,
  m_halted model = None -> m_vm_lazy model = [] ->
  ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 222%Z ->
  mmap_noaccess_args_ok ms ->
  (forall a, grant_ok_na (ms_gpr ms 0) model a (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = false) ->
  node_ok segs (mkCfg ms model) unit (fun _ => [])
    (fun _ => mkCfg (advance_past_svc (set_gpr0 ms (errno_ret ENOMEM))) model).
Proof.
  intros ms model x8 Hh Hlazy Hsvc Hno Hargs Hng.
  rewrite <- (apply_effect_no_write ms (errno_ret ENOMEM)).
  apply (node_det segs ms model x8 (mkEffect (errno_ret ENOMEM) [] []) model []); try assumption.
  intros o. pose proof (mmap_noaccess_outcome_si ms x8 model Hno Hargs o) as Hsi. cbv zeta in Hsi.
  rewrite Hsi. rewrite mmap_err_out_enomem.
  split; [| intros ->; left; reflexivity].
  intros [-> | (a & Ha & _)]; [reflexivity | rewrite Hng in Ha; discriminate Ha].
Qed.

(* [comment removed for export] *)

Lemma mmap_fixed_args_gates : forall ms,
  mmap_fixed_args_ok ms ->
  mmap_off_aligned_b (ms_gpr ms 5) = true /\ mmap_anon_b (ms_gpr ms 3) = true /\
  w_is0 (ms_gpr ms 1) = false /\
  mmap_modeled_b (ms_gpr ms 2) (ms_gpr ms 3) (ms_gpr ms 5) = false /\
  mmap_noaccess_b (ms_gpr ms 2) (ms_gpr ms 3) (ms_gpr ms 5) = false /\
  mmap_fixed_noaccess_b (ms_gpr ms 2) (ms_gpr ms 3) (ms_gpr ms 5) = true.
Proof.
  intros ms (H1 & H2 & H3 & H4 & H5). rewrite H2, H3, H5.
  split; [vm_compute; reflexivity|]. split; [vm_compute; reflexivity|].
  split; [unfold w_is0; apply bv_eqb_neq; exact H1|]. split; [vm_compute; reflexivity|].
  split; vm_compute; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma mmap_fixed_outcome_si : forall ms x8 model (addr : word) (len : Z),
  bv_unsigned x8 = 222%Z -> mmap_fixed_args_ok ms ->
  ms_gpr ms 0 = addr -> ms_gpr ms 1 = Z_to_bv 64 len -> (0 < len < 2 ^ 64)%Z ->
  let n := Z_to_bv 64 (page_round_up_Z len) in
  (bv_unsigned addr + page_round_up_Z len <= alloc_top (m_vmmaps model))%Z ->
  (bv_unsigned addr mod page_size = 0)%Z -> (0 < bv_unsigned addr)%Z ->
  region_free (vm_reserved (m_vmmaps model)) addr n = true ->
  map_contains (vm_maps (m_vmmaps model)) addr n = true ->
  forall o, syscall_spec (sys_input segs ms x8) model o <->
    mmap_err_out model o
    \/ o = Ok (mkEffectU addr [] [] [(addr, n)] [] []) (fixed_noaccess_model addr n model) []
    \/ o = Ok (mkEffectU (errno_ret ENOMEM) [] [] [(addr, n)] [] []) (fixed_destroyed_model addr n model) [].
Proof.
  intros ms x8 model addr len Hno Hargs H0 H1 Hlen n Htop Hal Hpos Hrf Hmc o.
  destruct (mmap_fixed_args_gates ms Hargs) as (Hoff & Hanon & Hl & Hmb & Hna & Hfx).
  destruct Hargs as (_ & _ & H3 & _ & _).
  assert (Hu1 : bv_unsigned (ms_gpr ms 1) = len) by (rewrite H1; apply u64_lit; lia).
  rewrite (syscall_spec_222 _ model o) by (rewrite in_sysno_sys_input; exact Hno).
  rewrite in_arg0_si, in_arg1_si, in_arg2_si,
          in_arg3_sys_input, in_arg4_sys_input, in_arg5_sys_input, H0.
  rewrite (mmap_fixed_noaccess_outcome addr (ms_gpr ms 1) _ _ _ _ _ model o Hoff Hanon Hl Hmb Hna Hfx);
    rewrite ?Hu1; try assumption.
  rewrite H3. fold n. unfold fixed_noaccess_model, fixed_destroyed_model, with_mmap_replacement,
                         with_mmap_destroyed, mmap_fixed_destroyed_next.
  rewrite with_mmap_backing_34 || idtac.
  replace (with_mmap_backing (Z_to_bv 64 50) addr n) with (fun m : Model => m).
  2:{ apply functional_extensionality. intros m0. unfold with_mmap_backing.
      replace (mmap_noreserve_b (Z_to_bv 64 50)) with false by (vm_compute; reflexivity). reflexivity. }
  cbv beta.
  split.
  - intros [He | [-> | (e & He & ->)]]; [left; exact He | right; left; reflexivity | right; right].
    unfold mmap_errnos in He. destruct He as [<- | []]. reflexivity.
  - intros [He | [-> | ->]]; [left; exact He | right; left; reflexivity | right; right].
    exists ENOMEM. split; [left; reflexivity | reflexivity].
Qed.
Scheme kc__1 := Elimination for Corelib.Init.Logic.and Sort Prop.
Scheme kc__2 := Elimination for Corelib.Init.Datatypes.unit Sort Prop.
Scheme kc__3 := Elimination for Corelib.Init.Logic.or Sort Prop.

(* [comment removed for export] *)
Lemma node_mmap_fixed_noaccess : forall ms model x8 (addr : word) (len : Z),
  m_halted model = None -> m_vm_lazy model = [] ->
  ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 222%Z ->
  mmap_fixed_args_ok ms ->
  ms_gpr ms 0 = addr -> ms_gpr ms 1 = Z_to_bv 64 len -> (0 < len < 2 ^ 64)%Z ->
  let n := Z_to_bv 64 (page_round_up_Z len) in
  (bv_unsigned addr + page_round_up_Z len <= alloc_top (m_vmmaps model))%Z ->
  (bv_unsigned addr mod page_size = 0)%Z -> (0 < bv_unsigned addr)%Z ->
  region_free (vm_reserved (m_vmmaps model)) addr n = true ->
  map_contains (vm_maps (m_vmmaps model)) addr n = true ->
  node_ok segs (mkCfg ms model) unit (fun _ => [])
    (fun _ => mkCfg (advance_past_svc (apply_effect ms (mkEffectU addr [] [] [(addr, n)] [] [])))
                    (fixed_noaccess_model addr n model)).
Proof.
  ltac2:(KReplay.runc [|constr:(@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.Model); constr:(@stdpp.bitvector.definitions.bv); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@Corelib.Numbers.BinNums.Z); constr:(@Corelib.Init.Logic.eq); constr:(@Corelib.Init.Datatypes.option); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.m_halted); constr:(@Corelib.Init.Datatypes.None); constr:(@Corelib.Init.Datatypes.list); constr:(@Corelib.Init.Datatypes.prod); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.m_vm_lazy); constr:(@Corelib.Init.Datatypes.nil); constr:(@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.ms_svc_pending); constr:(@Corelib.Init.Datatypes.Some); constr:(@stdpp.bitvector.definitions.bv_unsigned); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Numbers.BinNums.xI); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.RefNodes.mmap_fixed_args_ok); constr:(@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.ms_gpr); constr:(@Corelib.Init.Datatypes.O); constr:(@Corelib.Init.Datatypes.S); constr:(@stdpp.bitvector.definitions.Z_to_bv); constr:(@Corelib.Init.Logic.and); constr:(@Stdlib.ZArith.BinInt.Z.lt); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@Stdlib.ZArith.BinInt.Z.pow); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.page_round_up_Z); constr:(@Stdlib.ZArith.BinInt.Z.le); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.alloc_top); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.m_vmmaps); constr:(@Stdlib.ZArith.BinInt.Z.modulo); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.page_size); constr:(@Corelib.Init.Datatypes.bool); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.region_free); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.vm_reserved); constr:(@Corelib.Init.Datatypes.true); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.map_contains); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.vm_maps); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.in_sysno); constr:(@LinuxProcessSemantics.LinuxProcessSem.Run.sys_input); constr:(segs); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.ExitSim.in_sysno_sys_input); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AllocNodes.WithSegs.mmap_fixed_outcome_si); constr:(@LinuxProcessSemantics.LinuxProcessSem.Monad.outcome); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.SyscallEffect); constr:(@Corelib.Init.Logic.iff); constr:(@LinuxProcessSemantics.LinuxProcessSem.Specs.syscall_spec); constr:(@Corelib.Init.Logic.or); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.RelSpec.mmap_err_out); constr:(@LinuxProcessSemantics.LinuxProcessSem.Monad.Ok); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.mkEffectU); constr:(@Corelib.Init.Datatypes.cons); constr:(@Corelib.Init.Datatypes.pair); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.MemCopy); constr:(@Corelib.Init.Datatypes.nat); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.RefNodes.fixed_noaccess_model); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.event); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.errno_ret); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.ENOMEM); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.RefNodes.fixed_destroyed_model); constr:(@LinuxProcessSemantics.Riscv.Prelude.bv_eqb); constr:(@Corelib.Init.Datatypes.false); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.PropExec.bv_eqb_neq); constr:(@Corelib.Init.Logic.False); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.alloc_top_room); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.stack_max_size); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.two_pow_64); constr:(@Corelib.Init.Logic.eq_ind); constr:(@Stdlib.ZArith.BinInt.Z.sub); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.RelSpec.errno_ret_unsigned); constr:(@Stdlib.micromega.ZMicromega.ZArithProof); constr:(@Stdlib.micromega.VarMap.Empty); constr:(@Stdlib.micromega.VarMap.t); constr:(@Stdlib.micromega.Tauto.A); constr:(@Stdlib.micromega.RingMicromega.Formula); constr:(@Stdlib.micromega.Tauto.eKind); constr:(@Corelib.Init.Datatypes.unit); constr:(@Stdlib.micromega.Tauto.isProp); constr:(@Stdlib.micromega.RingMicromega.Build_Formula); constr:(@Stdlib.micromega.EnvRing.PEc); constr:(@Stdlib.micromega.RingMicromega.OpLe); constr:(@Corelib.Init.Datatypes.tt); constr:(@Stdlib.micromega.Tauto.BFormula); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker_sound); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker); constr:(@Stdlib.micromega.VarMap.find); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.RelSpec.page_round_up_Z_nonneg); constr:(@Stdlib.ZArith.BinInt.Z.pow_pos_nonneg); constr:(@Corelib.Init.Logic.True); constr:(@Stdlib.ZArith.BinInt.Z.pow_nonneg); constr:(@Stdlib.micromega.SatDivMod.Z_mod_nonneg_nonneg); constr:(@Stdlib.ZArith.BinInt.Z.div_mod); constr:(@Corelib.Init.Logic.not); constr:(@Stdlib.ZArith.BinInt.Z.mul); constr:(@Stdlib.ZArith.BinInt.Z.div); constr:(@Stdlib.ZArith.BinInt.Z.mod_pos_bound); constr:(@Stdlib.ZArith.BinInt.Z.mod_neg_bound); constr:(@Stdlib.omega.PreOmega.Z.div_0_r_ext); constr:(@Stdlib.omega.PreOmega.Z.mod_0_r_ext); constr:(@kc__1); constr:(@Stdlib.micromega.VarMap.Elt); constr:(@Stdlib.micromega.Tauto.IMPL); constr:(@Stdlib.micromega.Tauto.AND); constr:(@Stdlib.micromega.RingMicromega.OpLt); constr:(@Stdlib.micromega.EnvRing.PEX); constr:(@Stdlib.micromega.Tauto.X); constr:(@Stdlib.micromega.ZMicromega.RatProof); constr:(@Stdlib.micromega.RingMicromega.PsatzAdd); constr:(@Stdlib.micromega.RingMicromega.PsatzIn); constr:(@Stdlib.micromega.ZMicromega.DoneProof); constr:(@Stdlib.micromega.VarMap.Branch); constr:(@Stdlib.micromega.EnvRing.PEadd); constr:(@Stdlib.micromega.EnvRing.PEmul); constr:(@Stdlib.micromega.EnvRing.PEpow); constr:(@Stdlib.micromega.EnvRing.PEsub); constr:(@LinuxProcessSemantics.LinuxProcessSem.Run.refusal_b); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Scfg.refusal_b_mmap); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Nodes.node_family_cfg); constr:(SC); constr:(@kc__2); constr:(@Corelib.Init.Logic.or_intror); constr:(@Corelib.Init.Logic.or_introl); constr:(@LinuxProcessSemantics.LinuxProcessSem.Run.spurious_refusal_cfg); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Scfg.the_scfg); constr:(@LinuxProcessSemantics.LinuxProcessSem.Run.spurious_refusal_not_refusal); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.eff_ret); constr:(@kc__3); constr:(@Corelib.Init.Logic.ex); constr:(@Corelib.Init.Logic.False_ind); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.RelSpec.mmap_err_out_enomem); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.RelSpec.Ok_inj); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AllocNodes.alloc_refusal_spurious); constr:(AF); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Scfg.family_off_mmap_true); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AllocNodes.errno_is_refusal_mmap); constr:(@Corelib.Init.Logic.proj2); constr:(@Corelib.Init.Logic.ex_intro); constr:(@Corelib.Init.Logic.conj); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.with_vmmaps); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.mkVmMapsFull); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.maps_subtract); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.vm_noaccess); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.vm_start_brk); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.vm_brk); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.vm_limit); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.vm_mmap_base); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.vm_init_sp); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.vm_forget_range); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.RefNodes.vm_forget_range_halted); constr:(@LinuxProcessSemantics.LinuxProcessSem.Monad.Unmodeled); constr:(@Corelib.Init.Logic.I); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.RefNodes.vm_forget_range_lazy_nil); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.RefNodes.with_vmmaps_lazy')|] [|@b; @o; @Hsi; @Hmc; @Hrf; @Hpos; @Hal; @Htop; @H0; @addr; @z; @__ff; @__varmap; @__wit; @__arith; @Ha; @__x1; @__p1; @H6; @H2; @__sat11; @r; @q; @H5; @H4; @H3; @H; @__sat9; @__sat10; @__x2; @__x3; @__x4; @__x5; @__p2; @H7; @Hlt; @u; @i; @m; @Hns; @eff; @He; @m'; @ev; @E; @x; @evs; @e; @l; @Haddr; @Hno'; @n; @Hlen; @H1; @Hargs; @Hno; @Hsvc; @Hlazy; @Hh; @len; @x8; @model; @ms|] "#0}#S%8###\$K$+#W#$#q#y#*$L$J#)#(#8#?#3#6#%#>#+#'#-#z$'#<#,#/#5#4#J#&#.#7#9#;#2#=#@$P#D$>#F#:#H#0#}#1#A#B#E#S#C#G$g#I$9$O$$$v#K#[#l$<#b#m#n#{#~$,$E$X$i$l$w%(%$%0%/%.%:#Y#X#`$*$7$8$A$C$Z$[$^$_$`$a$b$f#N$k$p$o$y$x#L%'%-%1%2%3%4%5%6%7%8#^#e#f#j#r$%$($)$4$5$;$?$@$F$G$I$Q$T$U$R$D$W$Y$V$j$m$q$r#R#O$=$t${$|%%%)%*%+%,%9%<%;$u#V#]#o$1$0#t$.#p$2$6$:$3$/#i#g$c$&#Z#w$z#u$\#_$M$H%##h#s$e#v$N#d$S$h%&$~#c#|$#$-$s#a#k#x$B$]$d$n$}U$d&$e%$f)$g'$h%$i%$j%$k&$l&$m&$n'$o%$p$$q%$r($s&$t$$u$$v'$w%$x$$y$$z'${*#\)$|%$}$$~$%#+%$$%%%%&$%'%%(%%)+%*)%+$%,$%-$%.&%/&%0$%1%%2%%3)%4%%5%##&%6'%7$3SO3#3#3#3#3#USc#USd#UT(#8S1USe%#%$#VSR''L#GS'B%#%$#UT)NVT*-S'#-$#00O/SO3#/#/#/#/#3#=##D+#UT+S&MS,SP#;#NUSSSPMS(#VST?N#?$#)IK=s#(=s#$VT,$#)K#$'#>S&VSTs#(#0s#)S(>S,6$#4S-@#'%#0s#/S2N#J#D#I0s#2S-)I#4S6H#WSU#S?S1#S)#S@4RI#WSV#SAS'#S)#S@0s#<C#D#s#'j#$s#=#2S*S.RUT-#WT.S*S.R;s#AR&S($#0s#C%#D#s#.cT/S#S/S.RS6S2S(S,S&KOS'S1S$HUSfF2S*S3S.J#S#C.S#CUScs#NUSd#L#VSRs#L#B#>RVSTs#P#-s#Ps#PS/#*s#L#s#IBT0VSRs#ST1B#%S/*s#M&%#+S/)S#BSg&F%$##6C#UShSJ%#0s#S,+),S//S#&F$#(#;C#((#(:#VSW<#k#%?#WT2s#dS/+#S)CSQj#$S)##s#fS/.MS4SP#s#h#C0s#jH>S#6$#4S4@#'%#0s#pS$N#J#D#I0s#sS1)I#4S+H#WSU#S'S?#S)#S@4S7I#WSV#OSA#S)#S@2S*S8S%J#QC.QC-s$#s$#KR*s#{#s#x%Ks#6s#y#s#1s#/+KRQ&F$#s#.#s#AC#%s#-s#:s#}'s#5s#3,KRQ&F$#s#2#s#EC#('#(.#VSW0#k#%s#I#k#&#S;k#'5#k#(:#k#)?#k#*B#k#+s#&#k#,s#-#j#-s$8#MPSP#s$:#s#>0s$<s#?>S.6$#4P@#'%#N(J#D#I)I*4S5H#WSU#s#JS-#S)#S@Is#2WSV#s#MS?#S)#S@2S*QS7J#S%C.S%C-s$Ns$Ns#RS6*s$J#s$G%s#Ts#as$H#s#\s#Z+s#US6S%&F$#s#Y#s#lC#,s#XS6S%&F'#s#\#s#oC#(&#(-#VSW/#k#%s#s#4S%UT3#@$6#T4)#Si>S76C#4S8@#'%#j#.D#VSjSiSJBSXLSXUT5DUT6DUT7D=SOAD#3s$_=#AD#9D&SK#:)MEEL#S9VT8*LCS)S@VT9CS$#S)#S@m$%#WT:DIHXT;CS$$#l#/*)#l#043#l#176#'30l#2$#C'5SJm#$#/s$s/#/#/#/#/#/#/#/#/#=#AD#9D?SK#:s#%MEEL#S9l#/#>8l#0s#)s#(#l#1s#,s#+#'s#%)l#2$#C'SJ+m#$#WT<SJ8#ODs#^s#4Ns#3#>S+6s#5#4Q@#'%#VT=s$~s$})Is%#'Is%#)Is%#k##$#k##&#'Is%(WT>s%)s%(Hj##SY#j#3%#'Is%*k##SY#k#3(#VSks#qJ'Is#r'IJ'Is#nk##$#k##&#VSls#wJ#DJI7#VSms#zJPJ#6#s#v#Ds#}#k##'#VSns$#J)IJ)s#{J$0#k##%#VSos$(J)JI)Js$$'s$%I$$#k##&#VSps$.J#D3Ik##6#VSqs$1J#Ds$,s$2k##9#UOS6'IC)CJ$$#US(R'IS$)S$J$$#'IS0j##$#)S1J'IS')OJQDHADIDDSO9D$SH#:s#qMEEL#S9ZSZs#rMEELS1[Srs#sMEEL$#USeE9D)SK(:s#vMEEL#S9?s#wMEEL&%#l#/#s#ps#jl#0.s#z#l#1s#~s#}#j#4D#j#5SE#)IC$#H'IHk##$#k#4D#k#5SE#)Sss%oR#SsS<l#2+%#j#6<#j#7>#V#HCj##A#j##s#'#1s#(s#'s#$#Hl#8s#*s#V#l#7s#/s#,#l#9s$\D#l#:s#GD#l#;s#5s#3#l#<s#9s#7#l#=s#@s#;#l#7s#Fs#B#l#>s#Os#H#l#?s#Vs#Q#l#@s#[s#X#l#8s#es#`#VT?S7#'Is$HUShs$:0s&M#VSk#J'I$N%J'I#k##s#_#k##&#VSl)JVSm*JPJ#6#)#D-#k##s#`#VSn/J)-J$-#k##s#]#VSo3J)J1'2I$$#k##s#]#VSp8J#D1Ik##s#m#VSq;J#D9<k##s#p#UORUS,S/j##s#TS;USSs&QUSS#VS[D#VS[D%VS[Ds&UWStD$#WStD&#VT@#TA*SX#s$jQDOSD#S$s$jQDS'SD$O#QDS1SD#Hs$nSD%O#DDs'$9D#SHs#_:s$pMEEL#S9DDs'(9D&SH#:s$sMEEL#S9ZSZs$tMEELK[Srs$uMEEL$#?s$vMEEL(s#`#9D(SH+:s$xMEEL#S9/s'1DD#9Ds#kSK#:s$|MEEL#S9DDs&{=s'4AD#3s'33#3#3#=#AD#WSuD)#WSuD#$WSvD-#ADs&wWTBD#s'<9D%SH#:s%0MEEL#S9WTCD%s%,WSvD#69D#SK4:s%4MEEL#S9DDs'49Ds$&SH#:s%7MEEL#S9ZSZs%8MEELS&?s%9MEEL$s$##?s%:MEEL(s$$#?s%;MEEL-s$%#?s%<MEEL>s$&#?s%=MEELs##s$'#?s%>MEELs#&s$(#l#/#s%7s%1l#0s#1s%A#l#1s#9s%D#j#4D#j#AD#j#BD#j#CD#j#DD#j#5SE#j#ESE#)S'I)OS$$#Nk##%#)S$OPs#.s#(P#s#)6N#)#s'=VSjs'>s%N6#N'#K)IOk###S-k##%#k##)#k##s$L#k##/#k##1#k#4D#k#AD#k#BD#k#CD#k#DD#k#5SE#k#ESE#'KI4TD@#>TEaCS;&J$#Ks$*S2HS/S#S.S=l#2B(#j#Fs$[#j#=s$]#V#HCj##s$`#j##s$f#1s$gs$fs#o#Hl#@s#qs%9#l#=s#ss$k#l#9s$1D#l#:s$-D#l#6s#ys#w#l#;s#}s#{#l#<s$'s$##l#=s$,s$)#l#7s$3s$.#l#?s%=s%:#l#@s%Gs%B#l#8s$<s$7#m##S;l#>s$Bs$A#l#+s%Qs%L#l#Gs&1s&.#j#&s&4#j#'s&E#j#(s&I#j#)s&N#j#*s&P#j#+s&S#j#,s&Z#aSLs(7s';s&]#S.CS2KNOS'S1Hj#>s'0#7s'1m#$#XTFs(<S/s'?#Ks'TS#S/XTGs'US#S/H;S)s'9s'7%$##S)%SQ-s(@s(@S#S,*s(<#s(9%S#s'Ss(:#s'Ns'Lj##E#+S#S,Pj##E#j##Es'M.PC&F(&s'O#s'bC#%s'Ns'[s(B+s'Vs'T,S#S,P&F$#s'S#s'fC#('#(*#j#%s'i#-s(Qs(QS3S(*s(M#s(J%S3s'ds(K#s'_s']+S3S(S4&F$#s'\.S4##s'p$$%s'\s'is(P(s'ds'b,S3S(S4&F$#s'a#s't(#('#()#j#HE#.P9#s'y::#s'z;7($#Cs'|=WSw&%#WSx(%#WS\*#Cj#IE#UTHSM2S*S=P5$#S497#j#HE#2S*S4S3Ts#.K$P##S)#SQm#H#YTI,'Ps#2#WS\)#Cj#IE#LSg&FS$HC.S=#-s(xs(xPS2*s(t#s(q%Ps(/s(r#s(*s((+PS2S=&F$#s('#s(:)#%s(&s(3s(v's(.s(,,PS2S=&F$#s(+#s(>-#('#(.#&FS1S$H.S5#-s)*s)*S4S-*s)&#s)#%S4s(=s)$#s(8s(6+S4S-S5&F$#s(5#s(H)#%s(4s(As)('s(<s(:,S4S-S5&F$#s(9#s(L-#('#(.#2S*S7S55s#-#S+S'7#-s)9s)9S+S6*s)5#s)2%S+s(Ls)3#s(Gs(E#FN#+S+S6S%#GO##s#(S's(F$$#$'#j#IE#<E#k##.#j##2#&FS'S1S$.S+#2S*S%S+5s#?#S7O7#-s)Ks)KS7R*s)G#s)D%S7s(^s)E#s(Ys(W#FK#+S7RQ#GN##s#:Os(X$$#$'#j#IE#<E#.HC%s([s(hs)Os)Os(cs(a&F#S$s(_#s(rH#k##&#&F&Hs(b#s(uC#.S$Hk##$#$'#&F+S1s(g#s(zS$#k##'#j##&#.S1S$k##.#j###Hj##/#VTJHC11-($#j#%s)'#j#JG#k#%s))4k#JG#&FKNORQ#S$&F;Qs(w#s).%#EFS&=KS8Ns(yC#FS&>#GKS8#s#^Ns(|$$#$&##FS,s###GS&SB#s#cKs)%$$#$&#2S*SFSB5s#t#SCS(j##%##GS,SC#s#jS&s),$$##FS2s#.2S*S<S:5s#{#SDC7##GS?S<#s#qS-s)3$$#2S*S>S<5s$%#SGS$k##%#k#K)#j#LF#2S*SDSF5s$*#S:s#;7##GS-SD#s#|S2s)>$$#5s$/-SGs#@j##/##s$$S?s)B#GS6S>#s$&S6s)D2S*SNSI-s*?s*?S>S%*s*;#s*8%S>s)Rs*9#s)Ms)K+S>S%S0XTKSMS]'PWTL(S0PTs#LK*S0##S)#S@m#&#&F*)s)PJ.S0#-s*Ks*KSIQ*s*G#s*D%SIs)^s*E#s)Ys)W+SIQSN&F$#s)V.SN##s)j$$%s)Vs)cs*J(s)^s)\,SIQSN&F$#s)[#s)n(#('#()#k##0#.S02#s)s33%s)_s)ls*S=s)gs)e,S>S%S0&F$#s)d#s)w7#('#()#2S*SyS0J#SN5k##%#US3=Cs)~>WSw.*#WSx0*#XTM2'&#Ts#*Ks#.S0##S)#SQm#S##`SzSMS]s#1S0s#ts#.s#-s)ts#,s#''#j#>s#3#j#>s#5#V#HCj##s#8#j##s#I#1s#Js#Is#;#Cj#>s#>#j#Ks#B#[SLFs#}s#F#S-CNj#>s#R#V#HCj##s#U#j##s#`#1s#as#^s#Z#Cl#Ms#hs#c#l#Ms#ls#j#l#>s#qs#o#UC#VS^s$-#j#Ks$9#j#Ms$=#U#Cj##s$]#-s+)s+)S=S?*s+%#s*~%S=s*<s+##s*7s*5+S=S?S+&F$#s*4#s*Gs$F#%s*3s*@s+''s*;s*9,S=S?S+&F$#s*8#s*Ks$J#('#&FOS'S1-s+5s+5S5SA*s+1#s+.%S5s*Hs+/#s*Cs*A+S5SAS7&F$#s*@#s*S(#%s*?s*Ls+3's*Gs*E,S5SAS7&F$#s*D#s*W,#('#5s%6s)SS%N7#-s+Bs+BS%S/*s+>#s+;%S%s*Us+<#s*Ps*N#FS&#+S%S/S8#GK#$#s$1$&#j#IE#<E#k##-#j##0#&FNOS'&Fs$rs$ps*V#s*i$#5s%Gs*3QK7#EFS&1K/Ns*ZH-s+Ts+TQS.*s+P#s+M%Qs*gs+N#s*bs*`#FS,#+QS.SB#GS&#$#s$>$&#-s+\s+\SBS3*s+X#s+U%SBs*os+V#s*js*h#FS2#+SBS3SF#GS(##s%KS,s*i$$#$'#j#IE#<E#j##.#+S8S#SC#GS,#$#s$G-s+ks+kSCP*s+g#s+d%SCs*~s+e#s*ys*w+S:S=S<#GS?#$#s$F-s+qs+qS<S+*s+m#s+j%S<s+(s+k#s+#s*}#FS1#+S<S+S>#GS6##s%`SAs*~$$#$'#j#IE#<E#k##.#k#Ks$U#j#LF#5s%us$NS:47#+SFS4SD#GS-#$#s$N#F33$#/j#IE#<E#j##:#+SGS7SI#s%sRs+5-s,/s,/S0S8*s,+#s,(%S0s+Bs,)#s+=s+;#F##+S0S8Sy#GS$##s%zS.s+<$$#$'#j#IE#<E#k##.#j#NG##G++#s&&Hs+D$$#$/#j#IE#<E#j#Os&+##Fs$Ts$T#Gs$Ts$T#s&.s+Ls+L$$#$&#j#IE##Fs$fs$f#Gs$fs$f$#(CFs$iCGs$iCs&7s+UXS{',$#XS{)'&#XTNE+S9#;s&;s+Y2#RCj#>s$t#;Gs#);#RCj#>s#=#V#HCj##s$z#j##s#G#1s#Hs%/s#/#Cj#>s#5#j#Ks#9#[SLFs#Ms#<#S-CS'j#>s#\#V#HCj##s#S#j##s#g#1s#hs#es#X#Cl#Ps#ms#w#j#Ks#o#j#Ps#r#U#Cj##s$.#%s+ks+xs,_s&/s+ss+q,S+S6S%&F$#s+p#s,'s#z#j#IEs#n<E#%s+qs+~s,es$,s+ys+w,S%S/S8EFS&$K#Ns+vH#FS&%#GK%$#s%[$%#%s+xs,)s,ls#}s,$s+~#FS,#,QS.SB#GS&#$#s%\$&#j###s%Z,S8S#SC#GS,#$#s%Z%s,&s,3s,vs$#s,.s,,#FS2#%s,(s,5s,xs#rs,0s,.,S:S=S<#GS?#$#s%Yk###s%Wk#Ks%]#j#LF#5s&}s%VS:)7#,SFS4SD#GS-#$#s%V-s-0s-0SDS5*s-,#s-)%s,6s,Cs-*#s,>s,<5s')s%cSG#j##/#,S<S+S>#GS6#Ts%:Ks%XS0##S)#S@m#s%T#`SzSMS]s%[S0s%>s%Xs%Ws,Bs%V#s%1s%-j#>s%]#j#>)#V#HCj##s%b#j##<#1=s%s/#Cj#>5#j#K9#[SLFB<#S-CS'j#>s#$#V#HCj##s#(#j##s#1#1s#2s#/s#-#Cl#Ps#9s#5#UC#VS^s#>#j#Ks$Y#j#Ps#B#U#Cj##s$p#Fs$us$qs$bs#I#Cj#>s$}#U#Cj##s&~#Fs'.s'#s&ns%/#Cj#>s'1#j#Os'@#j#NG#j#LF#j##s''s-VRS%s$kH&Fs&cS%s,c#s,vs$m#EFKs&eNQOs,eC#FKs&f#GNQ$#s&n$%#8S&#s-c#s-aj##s&L##FS(s&m#GS(SF$#s$d#GS2S:#s'SS(s,q$$#8S-#s-l#s-jj##%#8H#s-o#s-mk##s$X#j#NG#j#>s&:S:;GSG$#SACj#>s&L#V#HCj##s&B#j##1#121-#Cj#>4#j#>7#V#HCj##s&`#j##s&i#1s&js&g<#Cl#Ms#$@#l#Ms#(s#&#l#>s&us&s#j#Ms'>#U#Cj##s'^#8O#s.*#s.(j##s%K#EFKs'>Ns'<Os-4Cj##s%Cs#(-s./s./S8S#*s.+#s.(%S8s-Bs.)#s-=s-;#FS(#+SCPS:#GS2#$#s#)j###s#'+SDS5SG4S>H#I$US|%0s.=S<0s.>S+6$#WS_&%#*s.;s%-#US}+US~,UT#-UT$.UT%/\S`/.('&%$#VSa#S>8##s.HCs.Fj#%s.I#WT&1/&8#WT'31(;s.M(&S:$#8s%8#s.O#s.Mm#%#j#>s&u#;G>s#?#SACj#>s%C#V#HCj##s&}#j##s#%#1s#&s#Ls#$#Cj#>s%T#j#>s#*#V#HCj##s%`#j##s%v#1s%ws%ts#2#Cl#Ps#4s'j#j#Ps%n#U#Cj##s&*#%s-gs-ts.[s'us-os-m,S7RQEFK$N#Os-lC#FK%#GN%$#s'u$%#j##s$Us#d%s-os-|s.cs#=s-ws-u#FS(#,SBS3SF#GS(#$#s%k,SCPS:#GS2#$#s#fj###s#d,SDS5SGWS_s#=s#;s#9\S`s#?#s#9s#7s#6s#5s#4s#3VSa#S>8#WT&s#?s#=$8#WT's#As#?&;s.{&s#4S:$#8s$J#s.}#s.{m#%#j#>s'G#;G/s#m#SACj#>s$^#V#HCj##s'O#j##6#17s#z5#Cj#>:#j#>>#V#HCj##s$p#j##s$y#1s$zs$xs#$#Cl#Ps#*s#&#j#Ps%&#U#Cj##s&T#Fs&Ys&Us#gs#1#Cj#>s&a#U#Cj##s(b#Fs(ns(cs$=s#n#Cj#>s(q#j#Os)$#j#NG#j#LF#UTOF.S3#-s/@s/@S.S&*s/<#s/9%S.s.Ss/:#s.Ns.L+S.S&S3&F$#s.K#s.^)#%s.Js.Ws/>'s.Rs.P,S.S&S3&F$#s.O#s.b-#('#(.#.P0#s.f1s)c#s.g2s)`($#(&#j###S;.S46RS57H&Fs([S5s.[#s.n9#nSf$F$#%SEC#%&#Q#J#RS;#SYj#Ss.p#&Fs(_S+s._Os.r=$Sb#CVS^S;Cl#>$S;#l#M+)#l#>s(Ps(N#j#M.#U#Cj##6##s.zs#%s)j#s.{s#&s)f($##s.}s#(s)F#s.~s#)s)C($#j###S;#s/%s#,s)<Os/&s#-4Sbs'>Cl#>#S;2j#P%#U#Cj##+##s/+s#2s)>Os/,s#3:Sbs'@Cl#>#S;8j#P%#U#Cj##0#F21/)#Cj#>4#U#Cj##s#*#Fs#.s#+s#):#Cj#>s#0#7s#1m#$#Gs**#s/w#s/uj#HE#0s0$S#0s0%S,6$#Hs.FIs.GUS|s.HWS_#(&*s0%s*H#US}s.KUS~s.LUT#s.MUT$s.NUT%s.O\S`,+('&%$#VSa#PGP#s0-Cs0+j#Ts0.#G&VTP(P;s01'%R$#XTQ75)#Gs*S#s04#s02m#%#WS\<#Cj#IE#gTRS*SMPS3S#Es*Ys*Ws*Vs*LRSAHs*5s*(s%Cs#_A#l#Us*_s*^#l#&s/Zs/<#l#Vs/^s/\#j#'s/f#j#(s/k#j#)s/p#j#*s/s#j#+s/w#l#Ws/~s0G#j#Xs0%#j#Ys0,#j#,s01#j#Zs04#j#[s06#j#\s0A#j#]s0E#j#^s0K#j#_D#j#-s0Q#j#`s0R#j#aG#j#bTS##"). Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma mprotect_outcome_si : forall ms x8 model (addr : word) (len : Z),
  bv_unsigned x8 = 226%Z ->
  ms_gpr ms 0 = addr -> ms_gpr ms 1 = Z_to_bv 64 len -> ms_gpr ms 2 = Z_to_bv 64 3 ->
  (0 < len)%Z -> (bv_unsigned addr + page_round_up_Z len < 2 ^ 64)%Z ->
  (bv_unsigned addr mod page_size = 0)%Z ->
  let n := Z_to_bv 64 (page_round_up_Z len) in
  map_contains (vm_noaccess (m_vmmaps model)) addr n = true ->
  map_contains (vm_maps (m_vmmaps model)) addr n = true ->
  forall o, syscall_spec (sys_input segs ms x8) model o <->
    mprotect_err_out model o
    \/ (mprotect_budget_ok model addr n = true
        /\ o = Ok (mkEffect (Z_to_bv 64 0) [] [(addr, n)]) (mprotect_model addr n model) []).
Proof.
  ltac2:(KReplay.runc [|constr:(@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state); constr:(@stdpp.bitvector.definitions.bv); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.Model); constr:(@Corelib.Numbers.BinNums.Z); constr:(@Corelib.Init.Logic.eq); constr:(@stdpp.bitvector.definitions.bv_unsigned); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Numbers.BinNums.xI); constr:(@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.ms_gpr); constr:(@Corelib.Init.Datatypes.O); constr:(@Corelib.Init.Datatypes.S); constr:(@stdpp.bitvector.definitions.Z_to_bv); constr:(@Stdlib.ZArith.BinInt.Z.lt); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.page_round_up_Z); constr:(@Stdlib.ZArith.BinInt.Z.pow); constr:(@Stdlib.ZArith.BinInt.Z.modulo); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.page_size); constr:(@Corelib.Init.Datatypes.bool); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.map_contains); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.vm_noaccess); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.m_vmmaps); constr:(@Corelib.Init.Datatypes.true); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.vm_maps); constr:(@LinuxProcessSemantics.LinuxProcessSem.Monad.outcome); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.SyscallEffect); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.PropExec.u64_range); constr:(@Corelib.Init.Logic.and); constr:(@Stdlib.ZArith.BinInt.Z.le); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.AllocSim.page_round_up_Z_bounds); constr:(@Stdlib.ZArith.BinInt.Z.pow_pos_nonneg); constr:(@Corelib.Init.Logic.True); constr:(@Stdlib.ZArith.BinInt.Z.pow_nonneg); constr:(@Stdlib.micromega.SatDivMod.Z_mod_nonneg_nonneg); constr:(@Stdlib.ZArith.BinInt.Z.div_mod); constr:(@Corelib.Init.Logic.not); constr:(@Stdlib.ZArith.BinInt.Z.mul); constr:(@Stdlib.ZArith.BinInt.Z.div); constr:(@Stdlib.ZArith.BinInt.Z.mod_pos_bound); constr:(@Stdlib.ZArith.BinInt.Z.mod_neg_bound); constr:(@Stdlib.omega.PreOmega.Z.div_0_r_ext); constr:(@Stdlib.omega.PreOmega.Z.mod_0_r_ext); constr:(@kc__1); constr:(@Corelib.Init.Datatypes.nil); constr:(@Stdlib.micromega.ZMicromega.ZArithProof); constr:(@Corelib.Init.Datatypes.list); constr:(@Stdlib.micromega.VarMap.Elt); constr:(@Stdlib.micromega.VarMap.t); constr:(@Stdlib.micromega.Tauto.IMPL); constr:(@Stdlib.micromega.RingMicromega.Formula); constr:(@Stdlib.micromega.Tauto.eKind); constr:(@Corelib.Init.Datatypes.unit); constr:(@Stdlib.micromega.Tauto.isProp); constr:(@Stdlib.micromega.Tauto.A); constr:(@Stdlib.micromega.RingMicromega.Build_Formula); constr:(@Stdlib.micromega.EnvRing.PEc); constr:(@Stdlib.micromega.RingMicromega.OpLt); constr:(@Stdlib.micromega.EnvRing.PEX); constr:(@Corelib.Init.Datatypes.tt); constr:(@Corelib.Init.Datatypes.None); constr:(@Stdlib.micromega.RingMicromega.OpLe); constr:(@Stdlib.micromega.Tauto.BFormula); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker_sound); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker); constr:(@Stdlib.micromega.VarMap.find); constr:(@Stdlib.ZArith.BinInt.Z.sub); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.AgentLib.u64_lit); constr:(@Corelib.Init.Datatypes.cons); constr:(@Stdlib.micromega.ZMicromega.RatProof); constr:(@Stdlib.micromega.RingMicromega.PsatzAdd); constr:(@Stdlib.micromega.RingMicromega.PsatzIn); constr:(@Stdlib.micromega.ZMicromega.DoneProof); constr:(@Stdlib.micromega.VarMap.Branch); constr:(@Stdlib.micromega.RingMicromega.OpEq); constr:(@Stdlib.micromega.Tauto.AND); constr:(@Stdlib.micromega.Tauto.X); constr:(@Stdlib.micromega.Tauto.NOT); constr:(@Stdlib.micromega.EnvRing.PEadd); constr:(@Stdlib.micromega.EnvRing.PEmul); constr:(@Stdlib.micromega.EnvRing.PEsub); constr:(@Stdlib.micromega.EnvRing.PEpow); constr:(@Corelib.Init.Logic.False); constr:(@Corelib.Init.Logic.iff); constr:(@LinuxProcessSemantics.LinuxProcessSem.Specs.syscall_spec); constr:(@LinuxProcessSemantics.LinuxProcessSem.Run.sys_input); constr:(segs); constr:(@LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mprotect.mprotect_spec); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.in_arg); constr:(@Corelib.Classes.Morphisms.trans_co_eq_inv_impl_morphism); constr:(@Corelib.Classes.RelationClasses.iff_Transitive); constr:(@Corelib.Init.Logic.or); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.RelSpec.mprotect_err_out); constr:(@LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mprotect.mprotect_budget_ok); constr:(@LinuxProcessSemantics.LinuxProcessSem.Monad.Ok); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.mkEffectU); constr:(@Corelib.Init.Datatypes.prod); constr:(@Corelib.Init.Datatypes.pair); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.MemCopy); constr:(@Corelib.Init.Datatypes.nat); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.RefNodes.mprotect_model); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.event); constr:(@Corelib.Classes.Morphisms.eq_proper_proxy); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.RelSpec.syscall_spec_226); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.in_sysno); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.ExitSim.in_sysno_sys_input); constr:(@Corelib.Init.Logic.eq_ind); constr:(@LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mprotect.mprotect_model_next); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.RelSpec.mprotect_expose_outcome); constr:(@Corelib.Init.Datatypes.false); constr:(@LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mprotect.mprotect_grows_conflict_b); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.PropExec.bv_eqb_neq); constr:(@Corelib.Init.Logic.f_equal); constr:(@Stdlib.micromega.VarMap.Empty); constr:(@LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall.w_is0); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.two_pow_64); constr:(@LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mprotect.mprotect_modeled_b); constr:(@Corelib.Classes.RelationClasses.reflexivity); constr:(@Corelib.Classes.RelationClasses.iff_Reflexive); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.RefNodes.mprotect_model_next_eq); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.FileSim.in_arg2_si); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.FileSim.in_arg1_si); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.FileSim.in_arg0_si)|] [|@Ha; @__ff; @__varmap; @__wit; @__x1; @__arith; @__sat9; @H8; @H; @r; @q; @H7; @H6; @H5; @H4; @H3; @__sat10; @__sat11; @b; @__x2; @__x3; @__x4; @__x5; @__x6; @__p1; @__p2; @H9; @lemma; @m; @z; @E; @Hu1; @o; @Hma; @Hna; @n; @Hal; @Hnw; @Hlen; @H2; @H1; @H0; @Hno; @len; @addr; @model; @x8; @ms|] "#+T#E$i#N$##]#X$$#~###3#4#'$*#x#*#$#)#^#&#2#b#-#E#5#%#/$(#(#,#e#T#1$;$G#.#6#;#+#L#:$,#0$D#?$C#@#M$^#J#I#`#c#k#o#7#9#<#y$/$2#A$F$E$M$U$W$J$K#P$[$d#[#d#f#j#l#8#=#{#}$+$-$0$1$.#i#>$6$9$>$@$A$B$4$S$T$V$Y$Z$X$_$a#B$b#D$`$c$e$]$f$g$h$i$j$k#H#O#W#h#g$5$&$%#|#Y#K#S#\$3#Z#q$H#V$)$O$L#U#w#z$I#Q#p$:$N$R$P$\#R#_#m#n#r#s#t#u#v$8$<$?#a$'$7$=$QU$9&$:%$;%#e%$<%$=&$>'$?*$@+$A%$B$$C%$D%$E)$F$$G%$H)#K%$I%$J%$K'$L%$M$$N$$O%$P%$Q$$R%$S'$T&$U'$V)$W&$X$$Y&$Z%$[%$\%$]%$^%$_%$`($a%$b*$c&$d$$e%$f&$g)$h%-S7-#-#-#-#-#USA#USB#&$S#DS7D#-#-#-#D#-#=##C+#.S,S/#.#S)9S/.Q#52S)#2$#9&.O#=357##7%#$FL&:Q1S,,$#=s##=?VSX$#$&#&AO/#E#C#F1O5s#%#PS&USC#E#S-I#R#S%PS3USD#E#S&P#R#S%USYS.USZS*&s#0S*%F#$$5'$#VS[98$F:%F:$F:k##$#k##&#%F?WS\@?Pj##SE#j#$%#%FAk##SE#k#$(#&s#AS$F#E%F$%FE&s#EK/#E%F#k##&#k##(#&s#JJG#E#CEFUSF#2+E>E#,#,#C.#k##'#H0E$FE&s#US(/#E%F#$$E'$#k##(#I(E$EF&s#]S4/#E$E#%$F'$#k##(#J(E&s#dSG2#E#C#Fk##=#K&E&s#iS]/#E#C#$k##B#2&E&s#nSH/#E&s#pS8%F#$$s#U'$#%FS8j##$#&s#vS5$#s#Z&s#xSI%F#&s#zS^$#s#^US3P%FS,k##s#<#:NUSJN;CPUS_CUS`CQCF6CS7)C$S+#*&HDDG#MUSaD)C'S9&*)HDDG#M+*HDDG&%#VSb+GVSKRS%VScIS)#R#S%m$%#WSdCFPXSeIS)$#l#%*)#l#&54#l#'87#j#(C#$FI%FPk##$#k#(C#VIS<S8l#)($#l#*s##A#j#+s#%#j#,s#(#V#PIj##s#,#j##s#3#Ls#4s#3s#0#S&l#-s#7C#l#.s#:C#l#/s#@s#<#l#0s#Fs#B#l#1s#Os#H#l#2s#Xs#Q#l#3s#as#Z#l#*s#ks#d#l#4s#qs#n#l#5s#{s#v#VSfS*#1S*%S*#,S*E=S7VSL$#%'#''#5s$ZS:&s$[I#C#S0j#6s$\#Fs#rE%Fs#sk##s#zs#gk##$#Gs#{E2s#lE>E#,#s#m#Cs#o#k##s#x#Hs#qE%Fs#i$s#jE'$#k##s#v#Is#nE/s#hE$E#%$F'$#k##s#t#Js#mE#Cs#eFk##s$+#Ks#kE#Cs#fs#gk##s$.#2s#iE/s#hE%Fs#c'#s#c%FS5$S5s$a'$#j##&#$s#gs$d%Fs#f&s%'Sg$#s$g9s$s9#9#9#MC#MC&MCs$yMCS/RC$#RC&#RC(#VSh#Si(N#s#p(N$#(N%#(N&#(N'#(N(#(N)#(N*#(N+#(N,#(N-#(N.#(N/#(N0#(N1#;CS#;CS,?C$Q#;CL;CQ?C$S)#?C&P#-s%H6C#)C#S1s$'*s$)HDDG#MDs%U6C#6Cs%N)C$S1#*s$.HDDG#M+s$/HDDG(s$*#6Cs%Q)C#S1s$0*s$2HDDG#M+s$3HDDG,s$.#)C/S+s$3*s$5HDDG#M)C1S+-*s$7HDDG#MSs$8HDDGS6Ns$9HDDG$#+s$:HDDG's$5#)Cs$:S+6*s$<HDDG#MSs$=HDDGS-)C5S+9*s$?HDDG#MNs$@HDDG%#+s$AHDDG's$<#ZSjs$BHDDG;WSkC>5OC#;)C;S1#*s$FHDDG#M+s$GHDDG's$B#6Cs%r)Cs$GS9#*s$JHDDG#MOCs$Is#&QCs#yWSlC$#)C(S9#*s$OHDDG#MNs$PHDDG(#)Cs$PS9s#'*s$RHDDG#M)Cs#*S1s$R*s$THDDG#MOCs#+/QCs%`WSmC#s%|)C%S+#*s$YHDDG#M)Cs$XS+%*s$[HDDG#MNs$\HDDGs$U#+s$]HDDGs$Ys$X#+s$^HDDG's$Y#+s$_HDDG-s$Z#+s$`HDDG0s$[#+s$aHDDG3s$\#+s$bHDDG=s$]#+s$cHDDGs#$s$^#+s$dHDDGs#,s$_#+s$eHDDGs#4s$`#+s$fHDDGs#9s$a#l#%#s$^s$Xl#&s#Es$i#l#'s#Ms$l#j#(C#j#7C#j#8C#j#9C#j#:C#j#;C#j#<S'#j#=S'##CLF#CLS)k##$##CS,F#COFk##$#$QF$OQ'#S-k##%#$FO$OS6'S3#k##%##CS6Fk###S=>S-S&,#S6#CQ#k##&#%S,O,S,S-VSL#s$Y%O#'&#%FO#CS&F,S-S&$#s&:$FS-%FS&$S&s&='$#k##&#k##(#k##+#k##-#k##/#k##5#k##<#k##A#k##s#&#k##s#*#k#(C#k#7C#k#8C#k#9C#k#:C#k#;C#k#<S'#k#=S'#%FQ%QF1S>&s&qSMfI&%OEQ$#S>S6S-S&S3S*JS#SHS8S5l#)s#;(#l#*s%Vs%T#j#>s$O#j#,s$R#V#PIj##s$U#j##s$\#Ls$]s%as$X#S3l#-s$_C#l#.s$aC#l#+s$es$c#l#/s$is$g#l#0s$ps$k#l#1s$vs$r#l#2s$}s$x#l#*s%&s%##l#4s&Hs&E#l#5s&Rs&M#VSnS:#.Ks&x0s'*s%/s%,$#S&&s',$#C#S:WSNS2S(KWSO#JS#<$S/<%s'#<&s&|3%$#'JS#4'#WSNS2S4S(WSO#KL<$S/<%s'*<&s''3%$#'KLVSPKL@KJO#R#S%5s'>FUSAs'CUSB#USJ#Ts'A#:#Ts'Cs'CAs'Ds'DJO:$(%$#:SoTs'HSp:#B/*&'%#WSQJOK:Sq7S.%$##s'#L#'5#88#VSRS'#]SSS'S;ST?;I$$#j#?B##Cs%Xs'Kj#6s'U#USrs#+WSsS2S(K0s'XK%S:$#XSts#.JS##.S(S/3Is#&s#%s#)KL4#.j#6s']#.S(s'Q.S4S/3#Is#*s#.KL4#3j#6s'b#.S(s'R.S4s'W3(#Is#3KL4#8j#6s'g#.S4s'W3I'#s#7KL4#<j#6s'k#3J*Is#:KL4#?j#6s'n#CJS$Q3J.s'\s#>KL7S.s#)Is#'#s'GL#'s#9#8s#<#4'#j#@S?#3S$;s'cs#LJS#VSPJS#&s'z=1#5s'|#@JS$##R#S%As'~s'~S$%(s#>#s#<Bs#Es#@#s#=s#;s#9CJS$(7S.$#s#8#s'XS##')#8/#41#&s(,s#%1#5s(.#@KJ##R#S%As(0s(0J%(s#L#s#JBs#Ss#N#s#Ks#Is#GCKJ(7S.$#s#F#s'fL#')#8s#[#CKJO7S.s#M#s#K#s'kL#'s#]#8s#`#VSRS'#]SSS'S;STs#,)I$$#j#?7#VSKRS@USus(-#R#S@m$%##s(Ds#Ds#eUSUs(FZSvs(FC#s#@s#gI&s(Hs#h#C?#.SGs(<&s(K##CI&j#AC#ZSVC%#IJS)#CJ)Fs'JE%Fs'K%Fs'Ak##s'm#k##%#Gs'JE>Es&;,#s'F#Cs'H#k##s'j#Hs'JE%Fs&?$s&@E'$#k##s'h#Is'ME/s'HE$E#%$F'$#k##s'f#Js'ME2s'LE#C#Fk##s'z#Ks'OE/s'NE#C#s'Ok##s'~#2s'QE/s&IE&s(oS<%F#$$s(T'$#j###S=&s(tS>$#s(X%Fs$c&s(wSw$#s([USxC?Cs'WP#6Cs)%)C#S1s'V*s'XHDDG#M)Cs'XS+%*s'ZHDDG#MSs'[HDDGS#+s'\HDDG$s'W#+s']HDDG's'X#l#%#s'Us'Ol#&,s'`#l#'s'ds'c#j#(C#j#<S'##CIF$FPk###S#k##%#k#(C#k#<S'#XIS=SyJS<l#)*$#l#*s'rs'p#j#>;#j#,>#V#PIj##A#j##s#'#Ls#(s#'s#%#S$l#-s#+C#l#.s#-C#l#+s#2s#/#l#/s#7s#4#l#0s#>s#9#l#1s#Ds#@#l#2s#Js#F#l#*s#Ps#L#l#4s(ds(a#l#5s(ns(i#l#Bs#Us#T#l#Bs#]s#[#j#Bs#`#USFs#am#$#XSzs)Js$Is$j#US{s$J#R#S@m#%#1I,s(c#$#SWj#AC#Fs(kE%Fs(lk##s(ns'Ik##$#Gs(_E2s(XE>E#,#s(Y#Cs([#k##s(l#Hs(]E%Fs'M$s'NE'$#k##s(j#Is([E$Es(V%s(WF'$#k##s(g#Js([E#Cs'LFk##s(z#Ks(YE#Cs'Ns(Xk##s(}#2s(ZE's(Rs'J1SI,s(S#$#s)Sj##&#%Fs'M;CS)?C#Ps#YOCs(Ns#X)C#S+s&X*s(RHDDG#M+s(SHDDG#s(N#l#%#s(Ks(El#&(s(V#l#'s(Zs(Y#j#(C#j#7C#,IP$#s)b,PS)$#s)dk##%#k#(C#k#7C#1SMWI#s#mS5l#),%#l#*s(js(h#j#>s#v#j#,:#V#PIj##s(o#j##s(r#Ls(ss'k?#S*l#-s$1C#l#.s#&C#l#+s#*s#(#l#/s#.s#,#l#0s#4s#0#l#1s#:s#6#l#2s#As#<#l#*s#Fs#C#l#4s)\s)Y#l#5s)fs)a#1S0,s)[#$#SWm#&#0CS0s#N#s%%IUS|s*-#R#S%m$s(q#PKUSC#5s*Gs#WE$J##R#S%j#AC#0CS0#S,s%/IUSD)E#J(#R#S%j#AC#0CS0#Ls%4IaS}S$s%Ps*<s&%JS#s$kOs#b2/(#@KJ-#R#S%As*Ss*SJ/(s%o#s%mBs%vs%q#s%ns%ls%jCKJ27S.$#s%i#s*-L#')#8s%~#4#s$}j#AC#@JS$Q#R#S%As*_s*_S$Q(s%{#s%yBs&&s%}#s%zs%xs%v7S.#s%Qs%t#s*8S##'(#8s%K#XS~S'S;T##0CS0-#s%LIVs%+:#WSQS$QJWT$JS$QZSVS?s%Zs%S%$#0s*ls*Xs%\#s%gS&0s*mS$s%`#s%qS*WT%S2S(K0s*os%js%f$s&@#WT&S2S(K0s*qs%qs%m$s&C#WT'S2S(K0s*ss%ws%t$s&F#Vs&#s%y#l#Cs&Ms&K#l#3s)'s(|#l#,s*Ks*G#j#Ds*M#j#Es*O#j#Fs*T#l#Gs*Ys*{#j#Hs*\#j#Is*`#j#Js*h#j#Ks*j#j#Ls*p#j#Ms*u#j#Ns*x#j#OC#j#Ps+(#j#QS?#j#Rs+*#j#ST(##"). Qed.

Lemma node_mprotect_ok : forall ms model x8 (addr : word) (len : Z),
  m_halted model = None -> m_vm_lazy model = [] ->
  ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 226%Z ->
  ms_gpr ms 0 = addr -> ms_gpr ms 1 = Z_to_bv 64 len -> ms_gpr ms 2 = Z_to_bv 64 3 ->
  (0 < len)%Z -> (bv_unsigned addr + page_round_up_Z len < 2 ^ 64)%Z ->
  (bv_unsigned addr mod page_size = 0)%Z ->
  let n := Z_to_bv 64 (page_round_up_Z len) in
  map_contains (vm_noaccess (m_vmmaps model)) addr n = true ->
  map_contains (vm_maps (m_vmmaps model)) addr n = true ->
  mprotect_budget_ok model addr n = true ->
  node_ok segs (mkCfg ms model) unit (fun _ => [])
    (fun _ => mkCfg (advance_past_svc (apply_effect ms (mkEffect (Z_to_bv 64 0) [] [(addr, n)])))
                    (mprotect_model addr n model)).
Proof.
  intros ms model x8 addr len Hh Hlazy Hsvc Hno H0 H1 H2 Hlen Hnw Hal n Hna Hma Hb.
  assert (Hno' : bv_unsigned (in_sysno (sys_input segs ms x8)) = 226%Z) by (rewrite in_sysno_sys_input; exact Hno).
  pose proof (mprotect_outcome_si ms x8 model addr len Hno H0 H1 H2 Hlen Hnw Hal Hna Hma) as Hsi. cbv zeta in Hsi. fold n in Hsi.
  apply (node_family_cfg segs ms model x8 unit
           (fun _ => mkEffect (Z_to_bv 64 0) [] [(addr, n)])
           (fun _ => mprotect_model addr n model) (fun _ => []) _ Hh Hsvc Hsi).
  - intros []. right. split; [exact Hb | reflexivity].
  - intros []. apply spurious_refusal_not_refusal. cbn [eff_ret]. apply zero_not_refusal_mprotect. exact Hno'.
  - intros eff m' ev [He | (_ & E)] Hns.
    + exfalso. apply Hns. apply mprotect_err_out_enomem in He. apply Ok_inj in He as (-> & -> & ->).
      eapply (alloc_refusal_spurious _ model _ (mkEffect (Z_to_bv 64 0) [] [(addr, n)]));
        [apply family_off_mprotect_true; exact Hno' | cbn [eff_ret]; apply errno_is_refusal_mprotect; exact Hno'
        | apply (proj2 (Hsi _)); right; split; [exact Hb | reflexivity]
        | cbn [eff_ret]; apply zero_not_refusal_mprotect; exact Hno'].
    + apply Ok_inj in E as (-> & -> & ->). exists tt. auto.
  - intros eff m' ev [He | (_ & E)].
    + apply mprotect_err_out_enomem in He. apply Ok_inj in He as (-> & -> & ->). exact Hh.
    + apply Ok_inj in E as (-> & -> & ->). exact Hh.
  - intros [He | (_ & E)]; [apply mprotect_err_out_enomem in He; discriminate He | discriminate E].
  - intros []. unfold mprotect_model. rewrite with_vmmaps_lazy'. exact Hlazy.
Qed.

Lemma node_mprotect_blocked : forall ms model x8 (addr : word) (len : Z),
  m_halted model = None -> m_vm_lazy model = [] ->
  ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 226%Z ->
  ms_gpr ms 0 = addr -> ms_gpr ms 1 = Z_to_bv 64 len -> ms_gpr ms 2 = Z_to_bv 64 3 ->
  (0 < len)%Z -> (bv_unsigned addr + page_round_up_Z len < 2 ^ 64)%Z ->
  (bv_unsigned addr mod page_size = 0)%Z ->
  let n := Z_to_bv 64 (page_round_up_Z len) in
  map_contains (vm_noaccess (m_vmmaps model)) addr n = true ->
  map_contains (vm_maps (m_vmmaps model)) addr n = true ->
  mprotect_budget_ok model addr n = false ->
  node_ok segs (mkCfg ms model) unit (fun _ => [])
    (fun _ => mkCfg (advance_past_svc (set_gpr0 ms (errno_ret ENOMEM))) model).
Proof.
  ltac2:(KReplay.runc [|constr:(@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.Model); constr:(@stdpp.bitvector.definitions.bv); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@Corelib.Numbers.BinNums.Z); constr:(@Corelib.Init.Logic.eq); constr:(@Corelib.Init.Datatypes.option); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.m_halted); constr:(@Corelib.Init.Datatypes.None); constr:(@Corelib.Init.Datatypes.list); constr:(@Corelib.Init.Datatypes.prod); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.m_vm_lazy); constr:(@Corelib.Init.Datatypes.nil); constr:(@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.ms_svc_pending); constr:(@Corelib.Init.Datatypes.Some); constr:(@stdpp.bitvector.definitions.bv_unsigned); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Numbers.BinNums.xI); constr:(@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.ms_gpr); constr:(@Corelib.Init.Datatypes.O); constr:(@Corelib.Init.Datatypes.S); constr:(@stdpp.bitvector.definitions.Z_to_bv); constr:(@Stdlib.ZArith.BinInt.Z.lt); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.page_round_up_Z); constr:(@Stdlib.ZArith.BinInt.Z.pow); constr:(@Stdlib.ZArith.BinInt.Z.modulo); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.page_size); constr:(@Corelib.Init.Datatypes.bool); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.map_contains); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.vm_noaccess); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.m_vmmaps); constr:(@Corelib.Init.Datatypes.true); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.vm_maps); constr:(@LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mprotect.mprotect_budget_ok); constr:(@Corelib.Init.Datatypes.false); constr:(@Corelib.Init.Logic.eq_ind); constr:(@LinuxProcessSemantics.LinuxProcessSem.Run.apply_effect); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.mkEffectU); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.errno_ret); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.ENOMEM); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.MemCopy); constr:(@Corelib.Init.Datatypes.nat); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.ShapeAlg.node_ok); constr:(segs); constr:(SC); constr:(@LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg); constr:(@Corelib.Init.Datatypes.unit); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.event); constr:(@LinuxProcessSemantics.LinuxProcessSem.Run.advance_past_svc); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Nodes.node_det); constr:(@LinuxProcessSemantics.LinuxProcessSem.Monad.outcome); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.SyscallEffect); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AllocNodes.WithSegs.mprotect_outcome_si); constr:(@Corelib.Init.Logic.iff); constr:(@LinuxProcessSemantics.LinuxProcessSem.Specs.syscall_spec); constr:(@LinuxProcessSemantics.LinuxProcessSem.Run.sys_input); constr:(@Corelib.Init.Logic.or); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.RelSpec.mprotect_err_out); constr:(@Corelib.Init.Logic.and); constr:(@LinuxProcessSemantics.LinuxProcessSem.Monad.Ok); constr:(@Corelib.Init.Datatypes.cons); constr:(@Corelib.Init.Datatypes.pair); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.RefNodes.mprotect_model); constr:(@Corelib.Classes.Morphisms.trans_co_eq_inv_impl_morphism); constr:(@Corelib.Classes.RelationClasses.iff_Transitive); constr:(@Corelib.Classes.Morphisms.eq_proper_proxy); constr:(@Corelib.Classes.Morphisms_Prop.or_iff_morphism); constr:(@Corelib.Classes.Morphisms.reflexive_proper_proxy); constr:(@Corelib.Classes.Morphisms.reflexive_reflexive_proxy); constr:(@Corelib.Classes.RelationClasses.iff_Reflexive); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.RelSpec.mprotect_err_out_enomem); constr:(@Corelib.Init.Logic.conj); constr:(@kc__3); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@Corelib.Init.Logic.eq_refl); constr:(@kc__1); constr:(@Corelib.Init.Logic.False); constr:(@Corelib.Init.Logic.True); constr:(@Corelib.Init.Logic.I); constr:(@Corelib.Init.Logic.False_ind); constr:(@Corelib.Init.Logic.or_introl); constr:(@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.set_gpr0); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.CatSim.apply_effect_no_write)|] [|@m; @lemma; @Hsi; @o; @H; @b; @e; @Hb'; @_H; @Hb; @Hma; @Hna; @n; @Hal; @Hnw; @Hlen; @H2; @H1; @H0; @Hno; @Hsvc; @Hlazy; @Hh; @len; @addr; @x8; @model; @ms|] "#&2#@$;###b#z#5#6#$#f#7#8#(#r#9#:#,#%#4#+#-#*#3#@#&#)#|#'#i#.#;#I#\#/#2#0#u#C#H#F#E#N#X#Y#[#e#1#c#t#s$*$+$5$4$7#K#L#M#P#R#S#]#_#`#a#d#g#m#n#o#p#k#v#w#q#y#{$,$/$0$.$-$1#<#=$8$9#?$:$6$3$;$2#x$<$=#D#J$&$%#G$##h#l#}$$$($'$)#~#Q#Z#U#O#T#V#W#^#j:$%&$&'$'%$($$)%$*&$+)$,&$-%$.'$/&$0&#:%$1&$2$$3%$4$$5%$6%$7$$8%$9$$:)&S6&#&#&#&#&#US7#US8#USG#USHS(USI%#%$#4''US9#USJS+1%#%$#USKS)VSL-S+#-$#50L6S66#&#&#&#6#&#3##S/+#7S#S:#:#LUS;S:7P#2>L#>$#US;&7S$#332s####s##%#VS<S0S%5s#&P8S#VSM$#3s#/3s#+VSN$#VS<&#5s#-S$VSO#SP#S/#S08S$2s#1#US=S>USQ#WS?#S1C#D#IUS=S2USR#WS?#S3H#D#I(S&S>Q#D#S,USSSTUS7s#AUS8#US9#4s#?#1#1SU4s#BSV1#)+&s#<s#<%#VSWF#VS@GF1SXj##S4#USYHVS@#Gj##S4#ZSZMSA(S4&#j#$S5#US[EcS\GRFS&S2S-S$PS#S%S)LS(QC0MGR*#FC+FC8S22s#U#(FS&##D#I2s#XS0,s#Xs#XS&&-s#T#s#Q)%<#s#R;9.S&)F$E$#7#1C#%*#'/#/1#0MJF*#GH+GH(GRL#D#I,s#fs#fRL-s#b#s#_)3s#*#s#`s#)s#'.RLG$E$#s#%#?H#%)#',#/.#0MKG*#JQ+JQ(JFS)#D#I,s#ts#tFS)-s#p#s#m)As#8#s#ns#7s#5.FS)J$E$#s#3#s#-Q#%)#',#$Es#:Js#7#s#1Q#VS]S'#]SBS'S*SC1&C$$#j#%4#$Es#?Gs#<#s#6H#/B#'),WS^S'S*S_XS`S'S*#.ZSa8,C//#]SBS'S*SC/&#--,j#%(#VSbGH'+Ak###1k##-+$Es#LKs#I#s#CS(#j##.#$Es#ONs#L0MS.N*#OC+OC(OKP#D#I,s$;s$;KP-s$7#s$4)s#Ds#[#s$5s#Zs#X.KPO$E$#s#V#s#PC#%)#',#/.#$Es#^S.s#[#s#UH#k#&%#j#'s#W#0MOK*#N6+N7(NJS##D#I,s$Ms$MJS#-s$I#s$F)s#Vs#m#s$Gs#ls#j.JS#N$E$#s#h#s#b?#%)#',#/.#$Es#pOs#mVSDs#g#j#&%#[SEs#is#&4#S+CS(j#(s#)#U#Cj##s#=#(KGS%#D#I,s$_s$_GS%-s$[#s$X)s#hs$##s$Ys#~s#|.GS%K$E$#s#z#s#tS(#%)##s#vS+7%=##s#xL4j##$##s#zLs#-(S.NS$#D#I,s$ms$mOS--s$i#s$f)s#vs$1#s$gs$0s$..OS-Sc$E$#s$,#s$&S%#(SdS.S1#DCIj#)D#9D%#HS,P#DS,InD#$#)S'C#%#SF#Sej#*D#9DS,#SfIC$Es$9Sgs$6#s$0S$#VSh#Cl#(&SF#l#++*#j#,0#j#+7#V#HCj##;#j##s#:#YSis#;A>#Cj#(s###U#Cj##s#l#ZSjs#js#ms#Ws#/#Cj#(s#]#0MNJ*#KC+KC#s$BCs#-%s#3#'%#/'##s$FHs#_#s$GHs#D%s#J#'%#k#&'#j#'s$K#*s$+Js#z+Js#{#s$Ns#|s$$%s$*#'%#/'##s$Rs#ns#n#s$Ss#os#>%s#D#VSDs$Us#qWSk&$#j#&(#[SEs$Xs$*/#QCHj#(s$%#XSls#xs#w>#Vs#|s#{#Vs$*C#l#&s$\s$K#j#'s$^#aSmMSAFRS&s$iRs$fS3S-#S3S1VSnFs$sVSoFs$t9S5s$ks$c%$#j#-s$w#j#.s$z#j#/s%##l#0s%(s%V#j#1s%+#j#2s%/#j#3s%7#j#4s%9#j#5s%?#j#6s%D#j#7s%G#j#8s%R#j#9s%V#j#:s%\#j#;S/#j#<s%b#j#=s%c#j#>Sp#j#?S5##"). Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma node_brk_query : forall ms model x8,
  m_halted model = None -> m_vm_lazy model = [] ->
  ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 214%Z ->
  ms_gpr ms 0 = Z_to_bv 64 0 ->
  node_ok segs (mkCfg ms model) unit (fun _ => [])
    (fun _ => mkCfg (advance_past_svc (set_gpr0 ms (vm_brk (m_vmmaps model)))) model).
Proof.
  intros ms model x8 Hh Hlazy Hsvc Hno H0.
  set (b := vm_brk (m_vmmaps model)).
  assert (ND : node_ok segs (mkCfg ms model) unit (fun _ => [])
     (fun _ => mkCfg (advance_past_svc (apply_effect ms
                        (mkEffectU b [] (brk_zeros (Z_to_bv 64 0) b b) (brk_unmaps b b) [] [])))
                     (brk_model (Z_to_bv 64 0) b model))).
  2:{ revert ND. rewrite brk_zeros_keep, brk_unmaps_keep.
      change (mkEffectU b [] [] [] [] []) with (mkEffect b [] []). rewrite apply_effect_no_write.
      unfold b. rewrite brk_model_keep. exact (fun H => H). }
  apply (node_det segs ms model x8); try assumption.
  - intros o. rewrite (syscall_spec_214 _ model o) by (rewrite in_sysno_sys_input; exact Hno).
    rewrite in_arg0_sys_input, H0. rewrite (brk_outcome (Z_to_bv 64 0) _ model o).
    unfold brk_model. split.
    + intros (r & Hr & ->). unfold Mmap.brk_r_ok in Hr. cbn [w_is0 bv_eqb] in Hr.
      change (bv_unsigned (Z_to_bv 64 0) =? bv_unsigned (Z_to_bv 64 0))%Z with true in Hr. cbn [orb] in Hr.
      apply bv_eqb_eq in Hr. subst r. reflexivity.
    + intros ->. exists (vm_brk (m_vmmaps model)). split; [|reflexivity].
      unfold Mmap.brk_r_ok. cbn [w_is0 bv_eqb].
      change (bv_unsigned (Z_to_bv 64 0) =? bv_unsigned (Z_to_bv 64 0))%Z with true. cbn [orb]. apply bv_eqb_refl.
  - unfold b. rewrite brk_model_keep. exact Hh.
  - unfold b. rewrite brk_model_keep. exact Hlazy.
Qed.

(* [comment removed for export] *)
Lemma brk_refusal_b_grow : forall model req r,
  (0 < bv_unsigned req)%Z ->
  (bv_unsigned (vm_start_brk (m_vmmaps model)) <= bv_unsigned req)%Z ->
  (bv_unsigned (vm_brk (m_vmmaps model)) < bv_unsigned req)%Z ->
  brk_refusal_b model req r = bv_eqb r (vm_brk (m_vmmaps model)).
Proof.
  intros model req r Hpos Hs Hlt. unfold brk_refusal_b, min_brk. cbv zeta.
  replace (w_is0 req) with false.
  2:{ symmetry. unfold w_is0. apply bv_eqb_neq. intros E. apply (f_equal bv_unsigned) in E.
      change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in E. lia. }
  rewrite (proj2 (Z.ltb_ge _ _)) by lia.
  replace (bv_eqb req (vm_brk (m_vmmaps model))) with false.
  2:{ symmetry. apply bv_eqb_neq. intros E. apply (f_equal bv_unsigned) in E. lia. }
  reflexivity.
Qed.

(* [comment removed for export] *)
Lemma node_brk_grow : forall ms model x8 req,
  m_halted model = None -> m_vm_lazy model = [] -> m_vm_materialized model = [] ->
  ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 214%Z ->
  ms_gpr ms 0 = req ->
  (0 < bv_unsigned req)%Z ->
  (bv_unsigned (vm_start_brk (m_vmmaps model)) <= bv_unsigned req)%Z ->
  (bv_unsigned (vm_brk (m_vmmaps model)) < bv_unsigned req)%Z ->
  Mmap.brk_grow_ok model req req = true ->
  node_ok segs (mkCfg ms model) unit (fun _ => [])
    (fun _ => mkCfg (advance_past_svc (apply_effect ms
                 (mkEffectU req [] (brk_zeros req req (vm_brk (m_vmmaps model)))
                                   (brk_unmaps req (vm_brk (m_vmmaps model))) [] [])))
                    (brk_model req req model)).
Proof.
  intros ms model x8 req Hh Hlazy Hmat Hsvc Hno H0 Hpos Hs Hlt Hg.
  assert (Hno' : bv_unsigned (in_sysno (sys_input segs ms x8)) = 214%Z) by (rewrite in_sysno_sys_input; exact Hno).
  set (b := vm_brk (m_vmmaps model)).
  assert (Hsi : forall o, syscall_spec (sys_input segs ms x8) model o <->
            exists r, (r = b \/ (r = req /\ Mmap.brk_grow_ok model req req = true))
                      /\ o = Ok (mkEffectU r [] (brk_zeros req r b) (brk_unmaps r b) [] []) (brk_model req r model) []).
  { intros o. rewrite (syscall_spec_214 _ model o) by (rewrite in_sysno_sys_input; exact Hno).
    rewrite in_arg0_sys_input, H0. rewrite (brk_outcome req _ model o). unfold brk_model. fold b.
    split; intros (r & Hr & ->); exists r; (split; [|reflexivity]).
    - apply (brk_r_ok_grow_cases model req r Hpos Hs ltac:(lia)). exact Hr.
    - apply (brk_r_ok_grow_cases model req r Hpos Hs ltac:(lia)). exact Hr. }
  assert (Hrq : refusal_b (sys_input segs ms x8) model req = false).
  { rewrite (refusal_b_brk _ model req Hno'), in_arg0_sys_input, H0, (brk_refusal_b_grow model req req Hpos Hs Hlt).
    apply bv_eqb_neq. intros E. apply (f_equal bv_unsigned) in E. subst b. lia. }
  apply (node_family_cfg segs ms model x8 unit
           (fun _ => mkEffectU req [] (brk_zeros req req b) (brk_unmaps req b) [] [])
           (fun _ => brk_model req req model) (fun _ => []) _ Hh Hsvc Hsi).
  - intros []. exists req. split; [right; auto | reflexivity].
  - intros []. apply spurious_refusal_not_refusal. cbn [eff_ret]. exact Hrq.
  - intros eff m' ev (r & [-> | [-> _]] & E) Hns; apply Ok_inj in E as (-> & -> & ->).
    + exfalso. apply Hns.
      eapply (alloc_refusal_spurious _ model _ (mkEffectU req [] (brk_zeros req req b) (brk_unmaps req b) [] []));
        [apply family_off_brk_true; exact Hno'
        | cbn [eff_ret]; rewrite (refusal_b_brk _ model b Hno'), in_arg0_sys_input, H0,
            (brk_refusal_b_grow model req b Hpos Hs Hlt); apply bv_eqb_refl
        | apply (proj2 (Hsi _)); exists req; split; [right; auto | reflexivity]
        | cbn [eff_ret]; exact Hrq].
    + exists tt. auto.
  - intros eff m' ev (r & _ & E). apply Ok_inj in E as (-> & -> & ->).
    unfold brk_model, with_brk_next. cbv zeta.
    destruct (forget_vm_ranges_frame (brk_unmaps r (vm_brk (m_vmmaps model)))
                (with_vmmaps (brk_model_next (m_vmmaps model) req r) model)) as (Hh1 & _ & _ & _).
    rewrite Hh1, with_vmmaps_halted. exact Hh.
  - intros (r & _ & E). discriminate E.
  - intros []. unfold brk_model, with_brk_next. cbv zeta.
    destruct (forget_vm_ranges_frame (brk_unmaps req (vm_brk (m_vmmaps model)))
                (with_vmmaps (brk_model_next (m_vmmaps model) req req) model)) as (_ & _ & _ & Hl1).
    apply Hl1. rewrite with_vmmaps_lazy'. exact Hlazy.
Qed.
Scheme kc__4 := Elimination for Corelib.Init.Logic.ex Sort Prop.

(* [comment removed for export] *)
Lemma node_brk_grow_blocked : forall ms model x8 req,
  m_halted model = None -> m_vm_lazy model = [] ->
  ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 214%Z ->
  ms_gpr ms 0 = req ->
  (0 < bv_unsigned req)%Z ->
  (bv_unsigned (vm_start_brk (m_vmmaps model)) <= bv_unsigned req)%Z ->
  (bv_unsigned (vm_brk (m_vmmaps model)) <= bv_unsigned req)%Z ->
  Mmap.brk_grow_ok model req req = false ->
  node_ok segs (mkCfg ms model) unit (fun _ => [])
    (fun _ => mkCfg (advance_past_svc (set_gpr0 ms (vm_brk (m_vmmaps model)))) model).
Proof.
  ltac2:(KReplay.runc [|constr:(@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.Model); constr:(@stdpp.bitvector.definitions.bv); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@Corelib.Init.Logic.eq); constr:(@Corelib.Init.Datatypes.option); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.m_halted); constr:(@Corelib.Init.Datatypes.None); constr:(@Corelib.Init.Datatypes.list); constr:(@Corelib.Init.Datatypes.prod); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.m_vm_lazy); constr:(@Corelib.Init.Datatypes.nil); constr:(@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.ms_svc_pending); constr:(@Corelib.Init.Datatypes.Some); constr:(@Corelib.Numbers.BinNums.Z); constr:(@stdpp.bitvector.definitions.bv_unsigned); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Numbers.BinNums.xI); constr:(@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.ms_gpr); constr:(@Corelib.Init.Datatypes.O); constr:(@Stdlib.ZArith.BinInt.Z.lt); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@Stdlib.ZArith.BinInt.Z.le); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.vm_start_brk); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.m_vmmaps); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.vm_brk); constr:(@Corelib.Init.Datatypes.bool); constr:(@LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap.brk_grow_ok); constr:(@Corelib.Init.Datatypes.false); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Nodes.node_det); constr:(segs); constr:(SC); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.mkEffectU); constr:(@LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap.brk_zeros); constr:(@LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap.brk_unmaps); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.MemCopy); constr:(@Corelib.Init.Datatypes.nat); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.AllocSim.brk_model); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.event); constr:(@LinuxProcessSemantics.LinuxProcessSem.Monad.outcome); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.SyscallEffect); constr:(@Corelib.Init.Logic.iff); constr:(@LinuxProcessSemantics.LinuxProcessSem.Specs.syscall_spec); constr:(@LinuxProcessSemantics.LinuxProcessSem.Run.sys_input); constr:(@LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap.brk_spec); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.in_arg); constr:(@Corelib.Classes.Morphisms.trans_co_eq_inv_impl_morphism); constr:(@Corelib.Classes.RelationClasses.iff_Transitive); constr:(@LinuxProcessSemantics.LinuxProcessSem.Monad.Ok); constr:(@Corelib.Classes.Morphisms.eq_proper_proxy); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.RelSpec.syscall_spec_214); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.in_sysno); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.ExitSim.in_sysno_sys_input); constr:(@Corelib.Init.Logic.ex); constr:(@Corelib.Init.Logic.and); constr:(@LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap.brk_r_ok); constr:(@Corelib.Init.Datatypes.true); constr:(@LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap.with_brk_next); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.RelSpec.brk_outcome); constr:(@Corelib.Init.Logic.conj); constr:(@kc__4); constr:(@kc__1); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.AllocSim.brk_resolution_ok); constr:(@Corelib.Init.Logic.or); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.RefNodes.brk_r_ok_grow_cases); constr:(@kc__3); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Corelib.Init.Logic.eq_ind); constr:(@Corelib.Init.Logic.False); constr:(@Corelib.Init.Logic.True); constr:(@Corelib.Init.Logic.I); constr:(@Corelib.Init.Logic.False_ind); constr:(@Corelib.Init.Logic.ex_intro); constr:(@Corelib.Init.Logic.or_introl); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.ExitSim.in_arg0_sys_input); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.RefNodes.brk_model_keep); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.ShapeAlg.node_ok); constr:(@LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg); constr:(@Corelib.Init.Datatypes.unit); constr:(@LinuxProcessSemantics.LinuxProcessSem.Run.advance_past_svc); constr:(@LinuxProcessSemantics.LinuxProcessSem.Run.apply_effect); constr:(@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.set_gpr0); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.CatSim.apply_effect_no_write); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.AllocSim.brk_unmaps_keep); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.AllocSim.brk_zeros_keep); constr:(@kc__4 ((@stdpp.bitvector.definitions.bv) ((@Corelib.Numbers.BinNums.Npos) ((@Corelib.Numbers.BinNums.xO) ((@Corelib.Numbers.BinNums.xO) ((@Corelib.Numbers.BinNums.xO) ((@Corelib.Numbers.BinNums.xO) ((@Corelib.Numbers.BinNums.xO) ((@Corelib.Numbers.BinNums.xO) (@Corelib.Numbers.BinNums.xH))))))))))|] [|@lemma; @b; @r; @o; @H; @e; @Hg'; @Hr; @x; @m; @ND; @l; @Hg; @Hle; @Hs; @Hpos; @H0; @Hno; @Hsvc; @Hlazy; @Hh; @req; @x8; @model; @ms|] "#)'#D$A###$#1#0#/#q#c#2$<$&#.#%#g#&#3#7#*#(#6#<#+#:#h#'#-#4#9#A#)#8#;#>#H#,#@#\#e#D#5#=#r#B#C#G#L#J#I#Q#W#[#_#t#s#v#w#x$.#?$1$2$)$9#|#N#P#U#V#Y#]#^#`#l#m#o#p#z#}#~#{$($3$4$5$/$*$7$6$8#f$@$A$B#M#i#y#j#k$'#a#b$$$;#d$=$:#K#X$%$?#n$,#T#u$-#Z$+$>#O#R#S$#$0C$#&$$)$%'$&&$'%$(&$)$$*$$+%$,%#a)$-&$.$$/)$0$$1%$2&$3%$4&$5&$6$$7'$8%$9$#K%$:($;%$<$$=%$>$$?%$@%1S?1#1#1#1#1#US@#USA#USR#>NUSS%#%$#?''USB#@P7%#%$#USTS$VSU-P#-$#20S*:S?1#:#1#:#:#1#USV##SC+#VSDS#S6#:#S*2<S$VSWSX#)S'USY#2@#2AS/VSE$#)S4*#2s#%#2s#&S#VSE$#.S+S'S'#I#S7)M*#US@s#0USA#USB#?s#.#7#&S+CC'CC7SZ?s#3S[7#$C('&%#5S+CG7S\US]HWSFOEGWSG#FCVSH$S68#%FC;%#WSFOJFWSG#EDVSH$S68#%ED&GNN'NN$N7$#425GNE%H$#1#1D#VS^S8#]SIS8S;SJ,*C$$#j#$/#2s#LC#SC#s#7j#%s#M#US_7WS`OEG-s#PG%S#$#XSa:FC#VSDES68C7ED;#/j#%s#U#8M?FC3EGC#I#L)E*#&GC#'C$$Cs#0$#s#-s#+(EGC%H$#s#*#s#*D#++#j#&s#b#As#c#;0#8Gs#)ED3JFC#I#L)J*#&FC#'C$$Cs#?$#s#<s#:(JFC%H$#s#9#s#9N#++#j#&s#q#As#r#]SIS8S;SJ0#Cs#.s#.s#-j#$2#XSbMs#>FC(EGN%Hs#5#s#B#s#BD#k##8#&MDD'DD$Ds#O$#s#Ls#J(FMD%H$#s#I#s#IC#k###0&FPP'PP$Ps#V$#s#Ss#Q(JFP%H$#s#P#s#PN#j##7#3QEC#I#L)Q*#&EC#'C$$Cs#a$#s#^s#\(QEC%H$#s#[#s#[P#++#j#&s$7#U#C3S,JC#I#L)S,*#&JC#'C$$Cs#n$#s#ks#i(S,JC%H$#s#h#s#hS*#++#3S9QD#I#L)S9*#&QD#'D$$Ds#y$#s#vs#t(S9QD%H$#s#s#s#sS$#++#&S,S#S#'S#S#$S#s$$$#s#}s#{(S%S,S#%H$#s#z#s#zS/#j##)#)S%*#&S,N#'N$$Ns$-$#s$*s$((S%S,N%H$#s$'#s$'S/#3RS9P#I#L)S0*#&S%S*#'S*$$S*s$7$#s$4s$2(S0S%S*%H$#s$1#s$1S'#)S-*#&RS$#'S$$$S$s$?$#s$<s$:(S-RS$%H$#s$9&S0MM'MM$Ms$D$#s$As$?(S(S0M%H$#s$>#s$>C#j#'s$?#6S-RS$)S(*##s$yS/##s$zS/S0.S(S0S0#I#L+%#9'#k##+##s%$S$9#s%%S$R.S-RR#I#L+%#9'#6S(S0S/k##$#++#)S1*##s%/S###s%0S#S-.S1S-S-#I#L+%#9'#k##-#j##,#6S1S-S#k##8#j###Dj##9#ZSKS-RS$EFG<;3($#UCN)S&*#&S(S'#'S'$$S's$q$#s$ns$l(S&S(S'%H$#s$k&S(FF'FF$Fs$v$#s$ss$q(S&S(F%H$#s$p#s$p(#j##9##s%LS'/)S:*#)S2*#&S&C#'C$$Cs%&$#s%#s$}(S2S&C%H$#s$|&S&JJ'JJ$Js%+$#s%(s%&(S2S&J%H$#s%%#s%%(#j#&s%\#&S1EE'EE$Es%2$#s%/s%-(S:S1E%H$#s%,Bs%,#-s%c7)#S4Cj#(:#U#Cj##s#9##s%gS'S(.S&S(S(#I#L+%##s%kS4S1.S:S1S1#I#L+%#&S&S+A'S+B$S+s%D$#s%As%?(S2S&S+%H$#s%>#s%>#<j##)#.S2S&S&#I#L#s%xMS:.S.SLSL#I#L)S<*#&S5D#'D$$Ds%R$#s%Os%M(S<S5D%H$#s%L&S5S%S%'S%S%$S%s%W$#s%Ts%R(S<S5S%%H$#s%Q#s%Q(#k##0#j#&s&-#.S5S2S2#I#L#ICLj#%I#ZSMI7#CS7S%#IS7LnI#$#%S8C#%#SN#Scj#)I#ZSMIS7#SdLC)S=*#&S.S.#'S.$$S.s%j$#s%gs%e(S=S.S.%H$#s%d&S.RR'RR$Rs%o$#s%ls%j(S=S.R%H$#s%i#s%i(#VSe#Cl#(1SN#l#*65#j#*:#-s&HS2=#GCj#(s#/#V#DCj##s#2#j##s#?#<s#@s#>s#6#Cj#(s#B#U#Cj##s#{#ZSfs$$s#|s#ds#I#Cl#+s#ss$2#l#(s#us$2#-s%zs$Ds$=#S4Cj#(s$L#j#+s$U#V#DCj##s$Y#j##s$r#<s$ss$ks$c#Cj#(s$v#j#&s&\#V#DCj##s%(#j#,s&_#YSgs&`s%Ms%7#Cj#(s%\##s&,Ds%0+s%8#j#&s&d#As&e#j#'s&0##s&1s%@s%W+s%_#j#&s&i#3EGs%n#I#L&Gs%ps%p's%qs%q$s%rs&A$#s&>s&<(EGs%s%H$#s&;#s&;s%X#6EGs%v#s&ss%hs%h#s&ts%iF.JFF#I#L+%#9'#k##)##s&zs%~s%~#s&{s&#G.EGG#I#L+%#9'#6JFs%uk##$#++#6QEs%Vk##.#j##%#j##$Cj##0#ZSKEGs&0S/S$S*<2*&$#Bs'.s&#WSh:6#UC#l#(&.#Bs&X@XSOs#&@$#XSis'4s#)s&8#-s&[s%xs#-#DCj#(s%q#XSOs%xs%qs#4#5MDF%Hs%w#s&`#s&`C#;s&6#m#'#Vs&'s&&#-s'>Ms&G#s&JS/WSjOEG-s'@s&Ls&I$s&c#Vs&Us&N#j#'s&h#>C#s'C#s'Aj#-S3#)G*#5S+#GVSPGS+-S3G'S4$#>s&s#s'K#s'Im#%#@C#s'I#s'Gj#-S3#-S3G#S'+*@s&z#s'M#s'Km#%#aSkOS)FGMs&~s&}s&|S4S#5*#,FGj##Ks&~=Es&:/#,#s#$j##K#0OS)(K'#,JE$Ps'1Ds&:s'.s',=Q#/#5FPJ,$#j##K#0OS))K/#,QJ4S,S*/#,#Qj##K#0OS)'K5#k#.)#j#/s'f#$Ps'@s'eDs'=s';=Q#/#,#1j##K#0OS)7K=#k#.#+j#/s'n#4ED/D,#8j##K#0OS)>Ks#$#k#.#2j#-S>#4Qs&q/#,#Dj##K#0OS)s#%Ks#+#4S,s&T/#,#Qj##K#0OS)BKs#0#k#.(#j#-S3#,EF4Js'1/#,#Ej##K#0OS)'Ks#8#j#(#C)F*#5M#FVSPFM-S3F.'$#4JN/#,#s'Sj##K#0OS)2Ks#C#4QP/#,#Jj##K#0OS)s#BKs#H#k#.(#m#.#$Ds'ss(<s(<s'ps'n=E#VSlED-S>s#0s#*&$#USmD-s(Cs(As#3$s',#VSnMD[SQs(Es(Cs#=$s'/#Cl#.s#Us#N#l#%s(%s(M#j#0s((#j#1s(+#j#2s(1#j#3s(7#j#4s(:#j#5s(=#j#6s(H#j#7s(L#j#8s(R#j#9s(W#j#:s(X#j#;S3#j#<S>##"). Qed.

End WithSegs.
