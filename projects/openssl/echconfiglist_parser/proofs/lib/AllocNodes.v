(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import Scfg Amb RelSpec
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
  intros ms model x8 addr len Hh Hlazy Hsvc Hno Hargs H0 H1 Hlen n Htop Hal Hpos Hrf Hmc.
  assert (Hno' : bv_unsigned (in_sysno (sys_input segs ms x8)) = 222%Z) by (rewrite in_sysno_sys_input; exact Hno).
  pose proof (mmap_fixed_outcome_si ms x8 model addr len Hno Hargs H0 H1 Hlen Htop Hal Hpos Hrf Hmc) as Hsi.
  cbv zeta in Hsi. fold n in Hsi.
  assert (Haddr : refusal_b (sys_input segs ms x8) model addr = false).
  { rewrite (refusal_b_mmap _ model addr Hno'). apply bv_eqb_neq. intros ->.
    pose proof (alloc_top_room (m_vmmaps model)) as Hlt.
    rewrite (errno_ret_unsigned ENOMEM) in Htop by (unfold ENOMEM; lia).
    pose proof (page_round_up_Z_nonneg len ltac:(lia)). unfold ENOMEM, two_pow_64, stack_max_size in *. lia. }
  apply (node_family_cfg segs ms model x8 unit
           (fun _ => mkEffectU addr [] [] [(addr, n)] [] [])
           (fun _ => fixed_noaccess_model addr n model) (fun _ => []) _ Hh Hsvc Hsi).
  - intros []. right; left. reflexivity.
  - intros []. apply spurious_refusal_not_refusal. cbn [eff_ret]. exact Haddr.
  - intros eff m' ev [He | [E | E]] Hns.
    + exfalso. apply Hns. apply mmap_err_out_enomem in He. apply Ok_inj in He as (-> & -> & ->).
      eapply (alloc_refusal_spurious _ model _ (mkEffectU addr [] [] [(addr, n)] [] []));
        [apply family_off_mmap_true; exact Hno' | cbn [eff_ret]; apply errno_is_refusal_mmap; exact Hno'
        | apply (proj2 (Hsi _)); right; left; reflexivity | cbn [eff_ret]; exact Haddr].
    + apply Ok_inj in E as (-> & -> & ->). exists tt. auto.
    + exfalso. apply Hns. apply Ok_inj in E as (-> & -> & ->).
      eapply (alloc_refusal_spurious _ model _ (mkEffectU addr [] [] [(addr, n)] [] []));
        [apply family_off_mmap_true; exact Hno' | cbn [eff_ret]; apply errno_is_refusal_mmap; exact Hno'
        | apply (proj2 (Hsi _)); right; left; reflexivity | cbn [eff_ret]; exact Haddr].
  - intros eff m' ev [He | [E | E]].
    + apply mmap_err_out_enomem in He. apply Ok_inj in He as (-> & -> & ->). exact Hh.
    + apply Ok_inj in E as (-> & -> & ->). unfold fixed_noaccess_model. rewrite vm_forget_range_halted. exact Hh.
    + apply Ok_inj in E as (-> & -> & ->). unfold fixed_destroyed_model. rewrite vm_forget_range_halted. exact Hh.
  - intros [He | [E | E]]; [apply mmap_err_out_enomem in He; discriminate He | discriminate E | discriminate E].
  - intros []. unfold fixed_noaccess_model. apply vm_forget_range_lazy_nil. rewrite with_vmmaps_lazy'. exact Hlazy.
Qed.

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
  intros ms x8 model addr len Hno H0 H1 H2 Hlen Hnw Hal n Hna Hma o.
  pose proof (u64_range addr). pose proof (page_round_up_Z_bounds len ltac:(lia)).
  assert (Hu1 : bv_unsigned (ms_gpr ms 1) = len) by (rewrite H1; apply u64_lit; lia).
  rewrite (syscall_spec_226 _ model o) by (rewrite in_sysno_sys_input; exact Hno).
  rewrite in_arg0_si, in_arg1_si, in_arg2_si, H0, H2.
  rewrite <- mprotect_model_next_eq.
  rewrite (mprotect_expose_outcome addr (ms_gpr ms 1) (Z_to_bv 64 3) _ model o); rewrite ?Hu1;
    [reflexivity | vm_compute; reflexivity | exact Hal | unfold w_is0; apply bv_eqb_neq; intros E;
     apply (f_equal bv_unsigned) in E; rewrite Hu1 in E; change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in E; lia
    | unfold two_pow_64; lia | vm_compute; reflexivity | exact Hna | exact Hma].
Qed.

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
  intros ms model x8 addr len Hh Hlazy Hsvc Hno H0 H1 H2 Hlen Hnw Hal n Hna Hma Hb.
  rewrite <- (apply_effect_no_write ms (errno_ret ENOMEM)).
  apply (node_det segs ms model x8 (mkEffect (errno_ret ENOMEM) [] []) model []); try assumption.
  intros o. pose proof (mprotect_outcome_si ms x8 model addr len Hno H0 H1 H2 Hlen Hnw Hal Hna Hma o) as Hsi.
  cbv zeta in Hsi. fold n in Hsi. rewrite Hsi. rewrite mprotect_err_out_enomem.
  split; [| intros ->; left; reflexivity].
  intros [-> | (Hb' & _)]; [reflexivity | rewrite Hb in Hb'; discriminate Hb'].
Qed.

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
  intros ms model x8 req Hh Hlazy Hsvc Hno H0 Hpos Hs Hle Hg.
  set (b := vm_brk (m_vmmaps model)).
  assert (ND : node_ok segs (mkCfg ms model) unit (fun _ => [])
     (fun _ => mkCfg (advance_past_svc (apply_effect ms
                        (mkEffectU b [] (brk_zeros req b b) (brk_unmaps b b) [] [])))
                     (brk_model req b model))).
  2:{ revert ND. rewrite brk_zeros_keep, brk_unmaps_keep.
      change (mkEffectU b [] [] [] [] []) with (mkEffect b [] []). rewrite apply_effect_no_write.
      unfold b. rewrite brk_model_keep. exact (fun H => H). }
  apply (node_det segs ms model x8); try assumption.
  - intros o. rewrite (syscall_spec_214 _ model o) by (rewrite in_sysno_sys_input; exact Hno).
    rewrite in_arg0_sys_input, H0. rewrite (brk_outcome req _ model o). unfold brk_model. split.
    + intros (r & Hr & ->). apply (brk_r_ok_grow_cases model req r Hpos Hs Hle) in Hr.
      destruct Hr as [-> | [-> Hg']]; [reflexivity | rewrite Hg in Hg'; discriminate Hg'].
    + intros ->. exists (vm_brk (m_vmmaps model)). split; [|reflexivity].
      apply (brk_r_ok_grow_cases model req _ Hpos Hs Hle). left. reflexivity.
  - unfold b. rewrite brk_model_keep. exact Hh.
  - unfold b. rewrite brk_model_keep. exact Hlazy.
Qed.

End WithSegs.
