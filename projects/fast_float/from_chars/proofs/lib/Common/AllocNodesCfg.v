(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import ShapeSet RealizesCfg PlacementCount.

Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)

Lemma materialize_nil : forall m, materialize_model_accesses m [] = Some m.
Proof.
  intros [fd [h lazy mat] io fsys proc lim time].
  unfold materialize_model_accesses, materialize_accesses, newly_materialized_pages.
  reflexivity.
Qed.

Lemma accesses_alloc_eff : forall r zs us,
  syscall_effect_accesses (mkEffectU r [] zs us [] []) = [].
Proof. reflexivity. Qed.

Lemma errno_ret_unsigned : forall e, (1 <= e <= 4095)%Z ->
  bv_unsigned (errno_ret e) = (2 ^ 64 - e)%Z.
Proof.
  intros e He. unfold errno_ret. rewrite Z_to_bv_unsigned.
  unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64)%Z.
  rewrite <- (Z.mod_add (- e) 1 (2 ^ 64)) by lia.
  rewrite Z.mod_small; lia.
Qed.

(* [comment removed for export] *)
Lemma below_top_not_errno : forall (h : VmMaps) (a : word) e,
  (1 <= e <= 4095)%Z ->
  (bv_unsigned a <= alloc_top h)%Z ->
  bv_eqb a (errno_ret e) = false.
Proof.
  intros h a e He Ha. unfold bv_eqb. rewrite errno_ret_unsigned by exact He.
  pose proof (alloc_top_room h). unfold two_pow_64, stack_max_size in *.
  apply Z.eqb_neq. lia.
Qed.

Section Forced.
Variable segs : list Segment.
Variable cfg : SpuriousCfg.

(* [comment removed for export] *)
Definition has_success (i : SyscallInput) (m : Model) : Prop :=
  exists eff' m' evs',
    syscall_spec i m (Ok eff' m' evs') /\ refusal_b i m (eff_ret eff') = false.

#[using="Type"] Lemma spurious_of_success : forall i m eff,
  injected_family_off cfg i = true ->
  has_success i m ->
  refusal_b i m (eff_ret eff) = true ->
  spurious_refusal_cfg cfg i m eff.
Proof. intros i m eff Hoff Hs Hr. split; [exact Hoff | split; [exact Hr | exact Hs]]. Qed.

#[using="Type"] Lemma not_spurious_forced : forall i m eff,
  ~ has_success i m -> ~ spurious_refusal_cfg cfg i m eff.
Proof. intros i m eff Hn (_ & _ & Hs). exact (Hn Hs). Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma node_forced_success : forall ms model x8 (I : Type)
    (E : I -> SyscallEffect) (M MM : I -> Model) (EV : I -> list event) (i0 : I),
  injected_family_off cfg (sys_input segs ms x8) = true ->
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  (forall i, syscall_spec (sys_input segs ms x8) model (Ok (E i) (M i) (EV i))) ->
  (forall i, refusal_b (sys_input segs ms x8) model (eff_ret (E i)) = false) ->
  (forall eff m' evs, syscall_spec (sys_input segs ms x8) model (Ok eff m' evs) ->
     refusal_b (sys_input segs ms x8) model (eff_ret eff) = false ->
     exists i, eff = E i /\ m' = M i /\ evs = EV i) ->
  ~ syscall_spec (sys_input segs ms x8) model Unmodeled ->
  (forall eff m' evs, syscall_spec (sys_input segs ms x8) model (Ok eff m' evs) ->
     m_halted m' = None) ->
  (forall i, materialize_model_accesses (M i) (syscall_effect_accesses (E i)) = Some (MM i)) ->
  node_ok_cfg segs cfg (mkCfg ms model) I EV
    (fun i => mkCfg (advance_past_svc (apply_effect ms (E i))) (MM i)).
Proof.
  intros ms model x8 I E M MM EV i0 Hoff Hh Hsvc Hcomp Hnr Hsound Hnu Hnh Hmat.
  apply (node_sys_cfg segs cfg ms model x8 I E M MM EV Hh Hsvc Hcomp); try assumption.
  - intro i. apply spurious_refusal_not_refusal. apply Hnr.
  - intros eff m' evs Hs Hns.
    destruct (refusal_b (sys_input segs ms x8) model (eff_ret eff)) eqn:Hr.
    + exfalso. apply Hns. apply spurious_of_success; [exact Hoff | | exact Hr].
      exists (E i0), (M i0), (EV i0). split; [apply Hcomp | apply Hnr].
    + exact (Hsound eff m' evs Hs Hr).
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma node_forced_refusal : forall ms model x8 (I : Type)
    (E : I -> SyscallEffect) (M MM : I -> Model) (EV : I -> list event),
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  (forall i, syscall_spec (sys_input segs ms x8) model (Ok (E i) (M i) (EV i))) ->
  (forall eff m' evs, syscall_spec (sys_input segs ms x8) model (Ok eff m' evs) ->
     refusal_b (sys_input segs ms x8) model (eff_ret eff) = true) ->
  (forall eff m' evs, syscall_spec (sys_input segs ms x8) model (Ok eff m' evs) ->
     exists i, eff = E i /\ m' = M i /\ evs = EV i) ->
  ~ syscall_spec (sys_input segs ms x8) model Unmodeled ->
  (forall eff m' evs, syscall_spec (sys_input segs ms x8) model (Ok eff m' evs) ->
     m_halted m' = None) ->
  (forall i, materialize_model_accesses (M i) (syscall_effect_accesses (E i)) = Some (MM i)) ->
  node_ok_cfg segs cfg (mkCfg ms model) I EV
    (fun i => mkCfg (advance_past_svc (apply_effect ms (E i))) (MM i)).
Proof.
  intros ms model x8 I E M MM EV Hh Hsvc Hcomp Hall Hsound Hnu Hnh Hmat.
  assert (Hns : forall eff, ~ spurious_refusal_cfg cfg (sys_input segs ms x8) model eff).
  { intro eff. apply not_spurious_forced. intros (eff' & m' & evs' & Hs & Hr).
    rewrite (Hall _ _ _ Hs) in Hr. discriminate Hr. }
  apply (node_sys_cfg segs cfg ms model x8 I E M MM EV Hh Hsvc Hcomp); try assumption.
  - intro i. apply Hns.
  - intros eff m' evs Hs _. exact (Hsound eff m' evs Hs).
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma node_det_nonrefusal : forall ms model x8 eff0 m0,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  syscall_spec (sys_input segs ms x8) model (Ok eff0 m0 []) ->
  refusal_b (sys_input segs ms x8) model (eff_ret eff0) = false ->
  (forall eff m' evs, syscall_spec (sys_input segs ms x8) model (Ok eff m' evs) ->
     refusal_b (sys_input segs ms x8) model (eff_ret eff) = false ->
     eff = eff0 /\ m' = m0 /\ evs = []) ->
  ~ syscall_spec (sys_input segs ms x8) model Unmodeled ->
  (forall eff m' evs, syscall_spec (sys_input segs ms x8) model (Ok eff m' evs) ->
     m_halted m' = None) ->
  syscall_effect_accesses eff0 = [] ->
  injected_family_off cfg (sys_input segs ms x8) = true ->
  node_ok_cfg segs cfg (mkCfg ms model) unit (fun _ => [])
    (fun _ => mkCfg (advance_past_svc (apply_effect ms eff0)) m0).
Proof.
  intros ms model x8 eff0 m0 Hh Hsvc Hs0 Hr0 Hsound Hnu Hnh Hacc Hoff.
  apply (node_forced_success ms model x8 unit (fun _ => eff0) (fun _ => m0) (fun _ => m0)
           (fun _ => []) tt Hoff Hh Hsvc).
  - intros []. exact Hs0.
  - intros []. exact Hr0.
  - intros eff m' evs Hs Hr. destruct (Hsound eff m' evs Hs Hr) as (-> & -> & ->).
    exists tt. auto.
  - exact Hnu.
  - exact Hnh.
  - intros []. rewrite Hacc. apply materialize_nil.
Qed.

End Forced.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition vm_only (m m' : Model) : Prop :=
  m_fd m' = m_fd m /\ m_io m' = m_io m /\ m_fsys m' = m_fsys m
  /\ m_proc m' = m_proc m /\ m_lim m' = m_lim m /\ m_time m' = m_time m.

Lemma vm_only_refl : forall m, vm_only m m.
Proof. intros m. repeat split. Qed.

Lemma vm_only_trans : forall m1 m2 m3, vm_only m1 m2 -> vm_only m2 m3 -> vm_only m1 m3.
Proof.
  intros m1 m2 m3 (a1 & b1 & c1 & d1 & e1 & f1) (a2 & b2 & c2 & d2 & e2 & f2).
  repeat split; congruence.
Qed.

Lemma vm_only_with_vmmaps : forall h m, vm_only m (with_vmmaps h m).
Proof. intros h m. repeat split. Qed.

Lemma vm_only_with_vm_backing : forall l mt m, vm_only m (with_vm_backing l mt m).
Proof. intros l mt m. repeat split. Qed.

Lemma vm_only_vm_forget_range : forall lo hi m, vm_only m (vm_forget_range lo hi m).
Proof. intros lo hi m. repeat split. Qed.

Lemma vm_only_forget_vm_ranges : forall rs m, vm_only m (forget_vm_ranges rs m).
Proof.
  induction rs as [|[a n] rs IH]; intro m; cbn [forget_vm_ranges]; [apply vm_only_refl|].
  eapply vm_only_trans; [apply vm_only_vm_forget_range | apply IH].
Qed.

Lemma vm_only_vm_add_lazy : forall a n m, vm_only m (vm_add_lazy a n m).
Proof. intros a n m. repeat split. Qed.

Lemma vm_only_with_brk_next : forall m req r, vm_only m (with_brk_next m req r).
Proof.
  intros m req r. unfold with_brk_next.
  eapply vm_only_trans; [apply vm_only_with_vmmaps | apply vm_only_forget_vm_ranges].
Qed.

Lemma vm_only_halted : forall m m', vm_only m m' -> m_halted m' = m_halted m.
Proof. intros m m' (_ & _ & _ & Hp & _). unfold m_halted. rewrite Hp. reflexivity. Qed.

Lemma vm_only_fs : forall m m', vm_only m m' -> m_fs m' = m_fs m.
Proof. intros m m' (_ & _ & Hf & _). unfold m_fs. rewrite Hf. reflexivity. Qed.

Lemma vm_only_fds : forall m m', vm_only m m' -> m_fds m' = m_fds m.
Proof. intros m m' (Hd & _). unfold m_fds. rewrite Hd. reflexivity. Qed.

Lemma vm_only_stdin : forall m m', vm_only m m' -> m_stdin m' = m_stdin m.
Proof. intros m m' (_ & Hi & _). unfold m_stdin. rewrite Hi. reflexivity. Qed.

(* [comment removed for export] *)

Lemma syscall_spec_brk : forall segs ms x8 model o,
  bv_unsigned x8 = 214%Z ->
  (syscall_spec (sys_input segs ms x8) model o
   <-> brk_spec (ms_gpr ms 0) (sys_input segs ms x8) model o).
Proof.
  intros segs ms x8 model o Hno. unfold syscall_spec, dispatch.
  change (in_sysno (sys_input segs ms x8)) with x8. rewrite Hno. reflexivity.
Qed.

(* [comment removed for export] *)
Definition brk_eff (req r b : word) : SyscallEffect :=
  mkEffectU r [] (brk_zeros req r b) (brk_unmaps r b) [] [].

Lemma brk_spec_ok_iff : forall req i m eff m' evs,
  brk_spec req i m (Ok eff m' evs) <->
  exists r, brk_r_ok m req r = true /\ eff = brk_eff req r (vm_brk (m_vmmaps m))
            /\ m' = with_brk_next m req r /\ evs = [].
Proof.
  intros req i m eff m' evs. unfold brk_spec, brk_eff.
  rewrite bind_get_model.
  unfold bind, choose, modify, pure. split.
  - intros H. sys_destruct. eexists. split; [eassumption|].
    split; [reflexivity|]. split; [reflexivity|]. reflexivity.
  - intros (r & Hr & -> & -> & ->).
    exists r, m, [], []. split; [exists r; split; [exact Hr | reflexivity]|].
    split; [| reflexivity].
    exists tt, (with_brk_next m req r), [], []. split; [reflexivity|]. split; reflexivity.
Qed.

Lemma brk_spec_no_unmodeled : forall req i m, ~ brk_spec req i m Unmodeled.
Proof.
  intros req i m H. unfold brk_spec in H. rewrite bind_get_model in H.
  unfold bind, choose, modify, pure in H. sys_destruct.
Qed.

(* [comment removed for export] *)
Lemma refusal_b_brk : forall segs ms x8 m r,
  bv_unsigned x8 = 214%Z ->
  refusal_b (sys_input segs ms x8) m r = brk_refusal_b m (ms_gpr ms 0) r.
Proof.
  intros segs ms x8 m r Hno. unfold refusal_b.
  change (in_sysno (sys_input segs ms x8)) with x8. rewrite Hno. reflexivity.
Qed.

Lemma brk_family_off : forall segs cfg ms x8,
  bv_unsigned x8 = 214%Z -> sc_alloc cfg = false ->
  injected_family_off cfg (sys_input segs ms x8) = true.
Proof.
  intros segs cfg ms x8 Hno Hoff. rewrite injected_family_off_sys_input, Hno.
  unfold injected_family_off_no. cbn. rewrite Hoff. reflexivity.
Qed.

Lemma brk_outcome_halted : forall segs ms x8 model eff m' evs,
  bv_unsigned x8 = 214%Z ->
  syscall_spec (sys_input segs ms x8) model (Ok eff m' evs) ->
  m_halted m' = m_halted model.
Proof.
  intros segs ms x8 model eff m' evs Hno Hs.
  apply (proj1 (syscall_spec_brk segs ms x8 model _ Hno)) in Hs.
  apply brk_spec_ok_iff in Hs as (r & _ & _ & -> & _).
  apply vm_only_halted, vm_only_with_brk_next.
Qed.

Lemma brk_eff_accesses : forall req r b, syscall_effect_accesses (brk_eff req r b) = [].
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma brk_r_ok_grow_cases : forall m req r,
  w_is0 req = false ->
  (bv_unsigned (min_brk (m_vmmaps m)) <= bv_unsigned req)%Z ->
  (bv_unsigned (vm_brk (m_vmmaps m)) <= bv_unsigned req)%Z ->
  brk_r_ok m req r = true ->
  (r = req /\ brk_grow_ok m req req = true) \/ r = vm_brk (m_vmmaps m).
Proof.
  intros m req r H0 Hmin Hge Hr. unfold brk_r_ok in Hr. rewrite H0 in Hr.
  destruct (Z.ltb (bv_unsigned req) (bv_unsigned (min_brk (m_vmmaps m)))) eqn:E1;
    [apply Z.ltb_lt in E1; lia|]. cbn [orb] in Hr.
  destruct (Z.ltb (bv_unsigned req) (bv_unsigned (vm_brk (m_vmmaps m)))) eqn:E2;
    [apply Z.ltb_lt in E2; lia|].
  apply andb_true_iff in Hr as [Hr Hg].
  apply orb_true_iff in Hr as [Hr | Hr]; apply bv_eqb_eq in Hr; subst r.
  - left. split; [reflexivity | exact Hg].
  - right. reflexivity.
Qed.

Lemma brk_refusal_b_old : forall m req,
  w_is0 req = false ->
  (bv_unsigned (min_brk (m_vmmaps m)) <= bv_unsigned req)%Z ->
  req <> vm_brk (m_vmmaps m) ->
  brk_refusal_b m req (vm_brk (m_vmmaps m)) = true.
Proof.
  intros m req H0 Hmin Hne. unfold brk_refusal_b. rewrite H0.
  destruct (Z.ltb (bv_unsigned req) (bv_unsigned (min_brk (m_vmmaps m)))) eqn:E1;
    [apply Z.ltb_lt in E1; lia|].
  destruct (bv_eqb req (vm_brk (m_vmmaps m))) eqn:E2;
    [apply bv_eqb_eq in E2; contradiction|].
  cbn. unfold bv_eqb. rewrite Z.eqb_refl. reflexivity.
Qed.

Lemma brk_refusal_b_new : forall m req,
  req <> vm_brk (m_vmmaps m) -> brk_refusal_b m req req = false.
Proof.
  intros m req Hne. unfold brk_refusal_b.
  destruct (bv_eqb req (vm_brk (m_vmmaps m))) eqn:E2;
    [apply bv_eqb_eq in E2; contradiction|].
  rewrite !andb_false_r. reflexivity.
Qed.

Section BrkNodes.
Variable segs : list Segment.
Variable cfg : SpuriousCfg.
Hypothesis Hoff : sc_alloc cfg = false.

(* [comment removed for export] *)
#[using="Hoff"] Lemma node_brk_grow : forall ms model x8 req,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 214%Z ->
  ms_gpr ms 0 = req ->
  w_is0 req = false ->
  (bv_unsigned (min_brk (m_vmmaps model)) <= bv_unsigned req)%Z ->
  (bv_unsigned (vm_brk (m_vmmaps model)) < bv_unsigned req)%Z ->
  brk_grow_ok model req req = true ->
  node_ok_cfg segs cfg (mkCfg ms model) unit (fun _ => [])
    (fun _ => mkCfg (advance_past_svc (apply_effect ms (brk_eff req req (vm_brk (m_vmmaps model)))))
                    (with_brk_next model req req)).
Proof.
  intros ms model x8 req Hh Hsvc Hno Ha0 H0 Hmin Hgt Hg.
  assert (Hne : req <> vm_brk (m_vmmaps model)) by (intro E; rewrite E in Hgt; lia).
  apply (node_forced_success segs cfg ms model x8 unit
           (fun _ => brk_eff req req (vm_brk (m_vmmaps model)))
           (fun _ => with_brk_next model req req) (fun _ => with_brk_next model req req)
           (fun _ => []) tt (brk_family_off segs cfg ms x8 Hno Hoff) Hh Hsvc).
  - intros []. apply (proj2 (syscall_spec_brk segs ms x8 model _ Hno)). rewrite Ha0.
    apply brk_spec_ok_iff. exists req. split; [| split; [reflexivity | split; reflexivity]].
    unfold brk_r_ok. rewrite H0.
    destruct (Z.ltb (bv_unsigned req) (bv_unsigned (min_brk (m_vmmaps model)))) eqn:E1;
      [apply Z.ltb_lt in E1; lia|].
    destruct (Z.ltb (bv_unsigned req) (bv_unsigned (vm_brk (m_vmmaps model)))) eqn:E2;
      [apply Z.ltb_lt in E2; lia|].
    cbn [orb]. unfold bv_eqb at 1. rewrite Z.eqb_refl. cbn [orb andb]. exact Hg.
  - intros []. rewrite refusal_b_brk by exact Hno. rewrite Ha0. cbn [eff_ret brk_eff].
    apply brk_refusal_b_new. exact Hne.
  - intros eff m' evs Hs Hr.
    rewrite refusal_b_brk in Hr by exact Hno. rewrite Ha0 in Hr.
    apply (proj1 (syscall_spec_brk segs ms x8 model _ Hno)) in Hs. rewrite Ha0 in Hs.
    apply brk_spec_ok_iff in Hs as (r & Hr' & -> & -> & ->).
    destruct (brk_r_ok_grow_cases model req r H0 Hmin ltac:(lia) Hr') as [[-> _] | ->].
    + exists tt. auto.
    + exfalso. cbn [eff_ret brk_eff] in Hr.
      rewrite (brk_refusal_b_old model req H0 Hmin Hne) in Hr. discriminate Hr.
  - intro Hu. apply (proj1 (syscall_spec_brk segs ms x8 model _ Hno)) in Hu.
    exact (brk_spec_no_unmodeled _ _ _ Hu).
  - intros eff m' evs Hs. rewrite (brk_outcome_halted segs ms x8 model eff m' evs Hno Hs). exact Hh.
  - intros []. rewrite brk_eff_accesses. apply materialize_nil.
Qed.

#[using="Type"] Lemma brk_unmaps_old : forall b, brk_unmaps b b = [].
Proof.
  intros b. unfold brk_unmaps, brk_page_range. rewrite Z.ltb_irrefl.
  destruct (0 <? bv_unsigned b)%Z; reflexivity.
Qed.

#[using="Type"] Lemma brk_zeros_old : forall req b, brk_zeros req b b = [].
Proof.
  intros req b. unfold brk_zeros, brk_is_grow. rewrite Z.ltb_irrefl, andb_false_r. reflexivity.
Qed.

#[using="Type"] Lemma brk_model_next_old : forall h req, brk_model_next h req (vm_brk h) = h.
Proof.
  intros [res maps noacc sbrk b limit mb isp] req.
  unfold brk_model_next, brk_maps_next, brk_grants.
  cbn [vm_reserved vm_maps vm_noaccess vm_start_brk vm_brk vm_limit vm_mmap_base vm_init_sp].
  rewrite brk_unmaps_old. unfold brk_is_grow. rewrite !Z.ltb_irrefl, !andb_false_r.
  reflexivity.
Qed.

#[using="Type"] Lemma with_vmmaps_same : forall m, with_vmmaps (m_vmmaps m) m = m.
Proof. intros [fd [h lazy mat] io fsys proc lim time]. reflexivity. Qed.

#[using="Type"] Lemma with_brk_next_old : forall m req,
  with_brk_next m req (vm_brk (m_vmmaps m)) = m.
Proof.
  intros m req. unfold with_brk_next. rewrite brk_unmaps_old. cbn [forget_vm_ranges].
  rewrite brk_model_next_old. apply with_vmmaps_same.
Qed.

#[using="Type"] Lemma brk_eff_old : forall req b, brk_eff req b b = mkEffect b [] [].
Proof. intros req b. unfold brk_eff. rewrite brk_zeros_old, brk_unmaps_old. reflexivity. Qed.


(* [comment removed for export] *)
#[using="Type"] Lemma node_brk_grow_forced_fail : forall ms model x8 req,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 214%Z ->
  ms_gpr ms 0 = req ->
  w_is0 req = false ->
  (bv_unsigned (min_brk (m_vmmaps model)) <= bv_unsigned req)%Z ->
  (bv_unsigned (vm_brk (m_vmmaps model)) < bv_unsigned req)%Z ->
  brk_grow_ok model req req = false ->
  node_ok_cfg segs cfg (mkCfg ms model) unit (fun _ => [])
    (fun _ => mkCfg (advance_past_svc (apply_effect ms (mkEffect (vm_brk (m_vmmaps model)) [] [])))
                    model).
Proof.
  intros ms model x8 req Hh Hsvc Hno Ha0 H0 Hmin Hgt Hg.
  assert (Hne : req <> vm_brk (m_vmmaps model)) by (intro E; rewrite E in Hgt; lia).
  apply (node_forced_refusal segs cfg ms model x8 unit
           (fun _ => mkEffect (vm_brk (m_vmmaps model)) [] [])
           (fun _ => model) (fun _ => model) (fun _ => []) Hh Hsvc).
  - intros []. apply (proj2 (syscall_spec_brk segs ms x8 model _ Hno)). rewrite Ha0.
    assert (Hs : brk_spec req (sys_input segs ms x8) model
                   (Ok (brk_eff req (vm_brk (m_vmmaps model)) (vm_brk (m_vmmaps model)))
                       (with_brk_next model req (vm_brk (m_vmmaps model))) [])).
    2: { rewrite brk_eff_old, with_brk_next_old in Hs. exact Hs. }
    apply brk_spec_ok_iff. exists (vm_brk (m_vmmaps model)).
    split; [| split; [reflexivity | split; reflexivity]].
    unfold brk_r_ok. rewrite H0.
    destruct (Z.ltb (bv_unsigned req) (bv_unsigned (min_brk (m_vmmaps model)))) eqn:E1;
      [apply Z.ltb_lt in E1; lia|].
    destruct (Z.ltb (bv_unsigned req) (bv_unsigned (vm_brk (m_vmmaps model)))) eqn:E2;
      [apply Z.ltb_lt in E2; lia|].
    cbn [orb]. unfold bv_eqb at 2. rewrite Z.eqb_refl, orb_true_r. cbn [andb].
    unfold brk_grow_ok. rewrite Z.ltb_irrefl, andb_false_r. reflexivity.
  - intros eff m' evs Hs.
    rewrite refusal_b_brk by exact Hno. rewrite Ha0.
    apply (proj1 (syscall_spec_brk segs ms x8 model _ Hno)) in Hs. rewrite Ha0 in Hs.
    apply brk_spec_ok_iff in Hs as (r & Hr' & -> & -> & ->).
    destruct (brk_r_ok_grow_cases model req r H0 Hmin ltac:(lia) Hr') as [[-> Hg'] | ->].
    + rewrite Hg in Hg'. discriminate Hg'.
    + cbn [eff_ret brk_eff]. apply brk_refusal_b_old; assumption.
  - intros eff m' evs Hs.
    apply (proj1 (syscall_spec_brk segs ms x8 model _ Hno)) in Hs. rewrite Ha0 in Hs.
    apply brk_spec_ok_iff in Hs as (r & Hr' & -> & -> & ->).
    destruct (brk_r_ok_grow_cases model req r H0 Hmin ltac:(lia) Hr') as [[-> Hg'] | ->].
    + rewrite Hg in Hg'. discriminate Hg'.
    + exists tt. rewrite brk_eff_old, with_brk_next_old. auto.
  - intro Hu. apply (proj1 (syscall_spec_brk segs ms x8 model _ Hno)) in Hu.
    exact (brk_spec_no_unmodeled _ _ _ Hu).
  - intros eff m' evs Hs. rewrite (brk_outcome_halted segs ms x8 model eff m' evs Hno Hs). exact Hh.
  - intros []. apply materialize_nil.
Qed.

(* [comment removed for export] *)
#[using="Hoff"] Lemma node_brk_shrink : forall ms model x8 req,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 214%Z ->
  ms_gpr ms 0 = req ->
  w_is0 req = false ->
  (bv_unsigned (min_brk (m_vmmaps model)) <= bv_unsigned req)%Z ->
  (bv_unsigned req < bv_unsigned (vm_brk (m_vmmaps model)))%Z ->
  node_ok_cfg segs cfg (mkCfg ms model) unit (fun _ => [])
    (fun _ => mkCfg (advance_past_svc (apply_effect ms (brk_eff req req (vm_brk (m_vmmaps model)))))
                    (with_brk_next model req req)).
Proof.
  intros ms model x8 req Hh Hsvc Hno Ha0 H0 Hmin Hlt.
  assert (Hne : req <> vm_brk (m_vmmaps model)) by (intro E; rewrite E in Hlt; lia).
  assert (Hcases : forall r, brk_r_ok model req r = true -> r = req \/ r = vm_brk (m_vmmaps model)).
  { intros r Hr. unfold brk_r_ok in Hr. rewrite H0 in Hr.
    destruct (Z.ltb (bv_unsigned req) (bv_unsigned (min_brk (m_vmmaps model)))) eqn:E1;
      [apply Z.ltb_lt in E1; lia|]. cbn [orb] in Hr.
    destruct (Z.ltb (bv_unsigned req) (bv_unsigned (vm_brk (m_vmmaps model)))) eqn:E2;
      [|apply Z.ltb_ge in E2; lia].
    apply orb_true_iff in Hr as [Hr | Hr]; apply bv_eqb_eq in Hr; auto. }
  apply (node_forced_success segs cfg ms model x8 unit
           (fun _ => brk_eff req req (vm_brk (m_vmmaps model)))
           (fun _ => with_brk_next model req req) (fun _ => with_brk_next model req req)
           (fun _ => []) tt (brk_family_off segs cfg ms x8 Hno Hoff) Hh Hsvc).
  - intros []. apply (proj2 (syscall_spec_brk segs ms x8 model _ Hno)). rewrite Ha0.
    apply brk_spec_ok_iff. exists req. split; [| split; [reflexivity | split; reflexivity]].
    unfold brk_r_ok. rewrite H0.
    destruct (Z.ltb (bv_unsigned req) (bv_unsigned (min_brk (m_vmmaps model)))) eqn:E1;
      [apply Z.ltb_lt in E1; lia|].
    destruct (Z.ltb (bv_unsigned req) (bv_unsigned (vm_brk (m_vmmaps model)))) eqn:E2;
      [|apply Z.ltb_ge in E2; lia].
    cbn [orb]. unfold bv_eqb at 1. rewrite Z.eqb_refl. reflexivity.
  - intros []. rewrite refusal_b_brk by exact Hno. rewrite Ha0. cbn [eff_ret brk_eff].
    apply brk_refusal_b_new. exact Hne.
  - intros eff m' evs Hs Hr.
    rewrite refusal_b_brk in Hr by exact Hno. rewrite Ha0 in Hr.
    apply (proj1 (syscall_spec_brk segs ms x8 model _ Hno)) in Hs. rewrite Ha0 in Hs.
    apply brk_spec_ok_iff in Hs as (r & Hr' & -> & -> & ->).
    destruct (Hcases r Hr') as [-> | ->].
    + exists tt. auto.
    + exfalso. cbn [eff_ret brk_eff] in Hr.
      rewrite (brk_refusal_b_old model req H0 Hmin Hne) in Hr. discriminate Hr.
  - intro Hu. apply (proj1 (syscall_spec_brk segs ms x8 model _ Hno)) in Hu.
    exact (brk_spec_no_unmodeled _ _ _ Hu).
  - intros eff m' evs Hs. rewrite (brk_outcome_halted segs ms x8 model eff m' evs Hno Hs). exact Hh.
  - intros []. rewrite brk_eff_accesses. apply materialize_nil.
Qed.

End BrkNodes.

(* [comment removed for export] *)
Lemma node_brk_query : forall segs cfg ms model x8 req,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 214%Z ->
  ms_gpr ms 0 = req ->
  (w_is0 req = true \/ (bv_unsigned req < bv_unsigned (min_brk (m_vmmaps model)))%Z
   \/ req = vm_brk (m_vmmaps model)) ->
  node_ok_cfg segs cfg (mkCfg ms model) unit (fun _ => [])
    (fun _ => mkCfg (advance_past_svc (apply_effect ms (mkEffect (vm_brk (m_vmmaps model)) [] [])))
                    model).
Proof.
  intros segs cfg ms model x8 req Hh Hsvc Hno Ha0 Hq.
  set (b := vm_brk (m_vmmaps model)).
  assert (Hcases : forall r, brk_r_ok model req r = true -> r = b).
  { intros r Hr. unfold brk_r_ok in Hr.
    destruct (w_is0 req || Z.ltb (bv_unsigned req) (bv_unsigned (min_brk (m_vmmaps model)))) eqn:E1.
    - apply bv_eqb_eq in Hr. exact Hr.
    - apply orb_false_iff in E1 as [E1a E1b].
      destruct Hq as [Hq | [Hq | Hq]]; [congruence | apply Z.ltb_ge in E1b; lia|].
      rewrite Hq in Hr. fold b in Hr. rewrite Z.ltb_irrefl in Hr.
      apply andb_true_iff in Hr as [Hr _].
      apply orb_true_iff in Hr as [Hr | Hr]; apply bv_eqb_eq in Hr; exact Hr. }
  assert (Hadm : brk_r_ok model req b = true).
  { unfold brk_r_ok.
    destruct (w_is0 req || Z.ltb (bv_unsigned req) (bv_unsigned (min_brk (m_vmmaps model)))) eqn:E1.
    - unfold bv_eqb. apply Z.eqb_refl.
    - apply orb_false_iff in E1 as [E1a E1b].
      destruct Hq as [Hq | [Hq | Hq]]; [congruence | apply Z.ltb_ge in E1b; lia|].
      rewrite Hq. fold b. rewrite Z.ltb_irrefl.
      unfold bv_eqb. rewrite Z.eqb_refl. cbn [orb andb].
      unfold brk_grow_ok. fold b. rewrite Z.ltb_irrefl, andb_false_r. reflexivity. }
  assert (Hnr : brk_refusal_b model req b = false).
  { unfold brk_refusal_b. fold b.
    destruct Hq as [Hq | [Hq | Hq]].
    - rewrite Hq. reflexivity.
    - apply Z.ltb_lt in Hq. rewrite Hq. rewrite andb_false_r. reflexivity.
    - rewrite Hq. unfold bv_eqb at 1. rewrite Z.eqb_refl. cbn [negb]. rewrite !andb_false_r.
      reflexivity. }
  apply (node_sys_cfg segs cfg ms model x8 unit
           (fun _ => mkEffect b [] []) (fun _ => model) (fun _ => model) (fun _ => []) Hh Hsvc).
  - intros []. apply (proj2 (syscall_spec_brk segs ms x8 model _ Hno)). rewrite Ha0.
    assert (Hs : brk_spec req (sys_input segs ms x8) model
                   (Ok (brk_eff req b b) (with_brk_next model req b) [])).
    2: { rewrite brk_eff_old in Hs. unfold b in Hs at 2. rewrite with_brk_next_old in Hs. exact Hs. }
    apply brk_spec_ok_iff. exists b. split; [exact Hadm | split; [reflexivity | split; reflexivity]].
  - intros []. apply spurious_refusal_not_refusal.
    rewrite refusal_b_brk by exact Hno. rewrite Ha0. exact Hnr.
  - intros eff m' evs Hs _.
    apply (proj1 (syscall_spec_brk segs ms x8 model _ Hno)) in Hs. rewrite Ha0 in Hs.
    apply brk_spec_ok_iff in Hs as (r & Hr' & -> & -> & ->).
    rewrite (Hcases r Hr'). exists tt. rewrite brk_eff_old. unfold b at 2. rewrite with_brk_next_old.
    auto.
  - intro Hu. apply (proj1 (syscall_spec_brk segs ms x8 model _ Hno)) in Hu.
    exact (brk_spec_no_unmodeled _ _ _ Hu).
  - intros eff m' evs Hs. rewrite (brk_outcome_halted segs ms x8 model eff m' evs Hno Hs). exact Hh.
  - intros []. apply materialize_nil.
Qed.


(* [comment removed for export] *)

Lemma syscall_spec_mmap : forall segs ms x8 model o,
  bv_unsigned x8 = 222%Z ->
  (syscall_spec (sys_input segs ms x8) model o
   <-> mmap_spec (ms_gpr ms 0) (ms_gpr ms 1) (ms_gpr ms 2) (ms_gpr ms 3)
         (ms_gpr ms 4) (ms_gpr ms 5) (sys_input segs ms x8) model o).
Proof.
  intros segs ms x8 model o Hno. unfold syscall_spec, dispatch.
  change (in_sysno (sys_input segs ms x8)) with x8. rewrite Hno. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma refusal_b_mmap : forall segs ms x8 m r,
  bv_unsigned x8 = 222%Z ->
  refusal_b (sys_input segs ms x8) m r = bv_eqb r (errno_ret ENOMEM).
Proof.
  intros segs ms x8 m r Hno. unfold refusal_b.
  change (in_sysno (sys_input segs ms x8)) with x8. rewrite Hno. cbn.
  rewrite orb_false_r. reflexivity.
Qed.

Lemma mmap_family_off : forall segs cfg ms x8,
  bv_unsigned x8 = 222%Z -> sc_alloc cfg = false ->
  injected_family_off cfg (sys_input segs ms x8) = true.
Proof.
  intros segs cfg ms x8 Hno Hoff. rewrite injected_family_off_sys_input, Hno.
  unfold injected_family_off_no. cbn. rewrite Hoff. reflexivity.
Qed.

Lemma ENOMEM_range : (1 <= ENOMEM <= 4095)%Z.
Proof. unfold ENOMEM. lia. Qed.

Lemma EEXIST_not_ENOMEM : bv_eqb (errno_ret EEXIST) (errno_ret ENOMEM) = false.
Proof. reflexivity. Qed.

Lemma EINVAL_not_ENOMEM : bv_eqb (errno_ret EINVAL) (errno_ret ENOMEM) = false.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma errno_arm_ok : forall es i m eff m' evs,
  (e <- errno_from es ;; err_ret e)%sys i m (Ok eff m' evs) <->
  exists e, In e es /\ eff = mkEffect (errno_ret e) [] [] /\ m' = m /\ evs = [].
Proof.
  intros es i m eff m' evs. unfold errno_from, err_ret, ret_only, bind, choose, pure. split.
  - intros H. sys_destruct. eexists. split; [eassumption|]. repeat split; reflexivity.
  - intros (e & He & -> & -> & ->). exists e, m, [], []. split; [exists e; auto|]. auto.
Qed.

Lemma errno_arm_unmodeled : forall es i m,
  ~ (e <- errno_from es ;; err_ret e)%sys i m Unmodeled.
Proof.
  intros es i m H. unfold errno_from, err_ret, ret_only, bind, choose, pure in H. sys_destruct.
Qed.

Lemma choose_arm_ok : forall {A : Type} (G : A -> Prop) (F : A -> Model) (E : A -> SyscallEffect)
                             i m eff m' evs,
  (a <- choose G ;; modify (fun _ => F a) ;; pure (E a))%sys i m (Ok eff m' evs) <->
  exists a, G a /\ eff = E a /\ m' = F a /\ evs = [].
Proof.
  intros A G F E i m eff m' evs. unfold bind, choose, modify, pure. split.
  - intros H. sys_destruct. eexists. split; [eassumption|]. repeat split; reflexivity.
  - intros (a & Ha & -> & -> & ->). exists a, m, [], []. split; [exists a; auto|].
    split; [| reflexivity]. exists tt, (F a), [], []. auto.
Qed.

Lemma choose_arm_unmodeled : forall {A : Type} (G : A -> Prop) (F : A -> Model) (E : A -> SyscallEffect)
                                    i m,
  ~ (a <- choose G ;; modify (fun _ => F a) ;; pure (E a))%sys i m Unmodeled.
Proof. intros A G F E i m H. unfold bind, choose, modify, pure in H. sys_destruct. Qed.

Lemma modify_arm_ok : forall (F : Model) (E : SyscallEffect) i m eff m' evs,
  (modify (fun _ => F) ;; pure E)%sys i m (Ok eff m' evs) <-> eff = E /\ m' = F /\ evs = [].
Proof.
  intros F E i m eff m' evs. unfold bind, modify, pure. split.
  - intros H. sys_destruct. repeat split; reflexivity.
  - intros (-> & -> & ->). exists tt, F, [], []. auto.
Qed.

Lemma modify_arm_unmodeled : forall (F : Model) (E : SyscallEffect) i m,
  ~ (modify (fun _ => F) ;; pure E)%sys i m Unmodeled.
Proof. intros F E i m H. unfold bind, modify, pure in H. sys_destruct. Qed.

Lemma destr_arm_ok : forall es (F : Model) (U : list (word * word)) i m eff m' evs,
  (e <- errno_from es ;; modify (fun _ => F) ;; pure (mkEffectU (errno_ret e) [] [] U [] []))%sys
    i m (Ok eff m' evs) <->
  exists e, In e es /\ eff = mkEffectU (errno_ret e) [] [] U [] [] /\ m' = F /\ evs = [].
Proof.
  intros es F U i m eff m' evs. unfold errno_from, bind, choose, modify, pure. split.
  - intros H. sys_destruct. eexists. split; [eassumption|]. repeat split; reflexivity.
  - intros (e & He & -> & -> & ->). exists e, m, [], []. split; [exists e; auto|].
    split; [| reflexivity]. exists tt, F, [], []. auto.
Qed.

Lemma destr_arm_unmodeled : forall es (F : Model) (U : list (word * word)) i m,
  ~ (e <- errno_from es ;; modify (fun _ => F) ;; pure (mkEffectU (errno_ret e) [] [] U [] []))%sys
      i m Unmodeled.
Proof. intros es F U i m H. unfold errno_from, bind, choose, modify, pure in H. sys_destruct. Qed.

(* [comment removed for export] *)
Definition place_ok (m : Model) (nZ : Z) (a : word) : Prop :=
  (bv_unsigned a mod page_size = 0)%Z /\ (0 < bv_unsigned a)%Z
  /\ (bv_unsigned a + nZ <= alloc_top (m_vmmaps m))%Z
  /\ region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) a (Z_to_bv 64 nZ) = true.

(* [comment removed for export] *)
Definition fresh_rw_guard (flags : word) (m : Model) (nZ : Z) (a : word) : Prop :=
  (bv_unsigned a mod page_size = 0)%Z /\ (0 < bv_unsigned a)%Z
  /\ (bv_unsigned a + nZ <= alloc_top (m_vmmaps m))%Z
  /\ region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) a (Z_to_bv 64 nZ) = true
  /\ mmap_noreserve_backed_ok flags m nZ = true.

Lemma fresh_rw_guard_iff : forall flags m nZ a,
  fresh_rw_guard flags m nZ a <-> place_ok m nZ a /\ mmap_noreserve_backed_ok flags m nZ = true.
Proof. intros. unfold fresh_rw_guard, place_ok. tauto. Qed.

(* [comment removed for export] *)
Definition fresh_rw_next (flags a n : word) (m : Model) : Model :=
  with_mmap_backing flags a n
    (with_vmmaps
       (mkVmMapsFull (vm_reserved (m_vmmaps m)) ((a, n) :: vm_maps (m_vmmaps m))
          (vm_noaccess (m_vmmaps m)) (vm_start_brk (m_vmmaps m)) (vm_brk (m_vmmaps m))
          (vm_limit (m_vmmaps m)) (vm_mmap_base (m_vmmaps m)) (vm_init_sp (m_vmmaps m))) m).

(* [comment removed for export] *)
Definition fresh_na_next (flags a n : word) (m : Model) : Model :=
  with_mmap_backing flags a n
    (with_vmmaps
       (mkVmMapsFull (vm_reserved (m_vmmaps m)) ((a, n) :: vm_maps (m_vmmaps m))
          ((a, n) :: vm_noaccess (m_vmmaps m)) (vm_start_brk (m_vmmaps m)) (vm_brk (m_vmmaps m))
          (vm_limit (m_vmmaps m)) (vm_mmap_base (m_vmmaps m)) (vm_init_sp (m_vmmaps m))) m).

Lemma vm_only_with_mmap_backing : forall flags a n m, vm_only m (with_mmap_backing flags a n m).
Proof.
  intros flags a n m. unfold with_mmap_backing.
  destruct (mmap_noreserve_b flags); [apply vm_only_vm_add_lazy | apply vm_only_refl].
Qed.

Lemma vm_only_fresh_rw_next : forall flags a n m, vm_only m (fresh_rw_next flags a n m).
Proof.
  intros. unfold fresh_rw_next.
  eapply vm_only_trans; [apply vm_only_with_vmmaps | apply vm_only_with_mmap_backing].
Qed.

Lemma vm_only_fresh_na_next : forall flags a n m, vm_only m (fresh_na_next flags a n m).
Proof.
  intros. unfold fresh_na_next.
  eapply vm_only_trans; [apply vm_only_with_vmmaps | apply vm_only_with_mmap_backing].
Qed.

(* [comment removed for export] *)
Lemma mmap_spec_fresh_rw : forall addr len prot flags fd off i m o,
  mmap_off_aligned_b off = true -> mmap_anon_b flags = true -> w_is0 len = false ->
  mmap_modeled_b prot flags off = true ->
  (mmap_spec addr len prot flags fd off i m o <->
   alt (e <- errno_from mmap_errnos ;; err_ret e)%sys
       (a <- choose (fresh_rw_guard flags m (page_round_up_Z (bv_unsigned len))) ;;
        modify (fun _ => fresh_rw_next flags a (Z_to_bv 64 (page_round_up_Z (bv_unsigned len))) m) ;;
        pure (mkEffect a [] [(a, Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))]))%sys i m o).
Proof.
  intros addr len prot flags fd off i m o Ho Ha Hl Hm.
  unfold mmap_spec. rewrite Ho, Ha, Hl, Hm. cbn [negb].
  unfold alt. rewrite bind_get_model. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma mmap_spec_fresh_na : forall addr len prot flags fd off i m o,
  mmap_off_aligned_b off = true -> mmap_anon_b flags = true -> w_is0 len = false ->
  mmap_modeled_b prot flags off = false -> mmap_noaccess_b prot flags off = true ->
  (mmap_spec addr len prot flags fd off i m o <->
   alt (e <- errno_from mmap_errnos ;; err_ret e)%sys
       (a <- choose (place_ok m (page_round_up_Z (bv_unsigned len))) ;;
        modify (fun _ => fresh_na_next flags a (Z_to_bv 64 (page_round_up_Z (bv_unsigned len))) m) ;;
        pure (mkEffectU a [] [] [(a, Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))] [] []))%sys i m o).
Proof.
  intros addr len prot flags fd off i m o Ho Ha Hl Hm Hn.
  unfold mmap_spec. rewrite Ho, Ha, Hl, Hm, Hn. cbn [negb].
  unfold alt. rewrite bind_get_model. reflexivity.
Qed.

(* [comment removed for export] *)
Section MmapGeneric.
Variable segs : list Segment.
Variable cfg : SpuriousCfg.
Hypothesis Hoff : sc_alloc cfg = false.

#[using="Hoff"] Lemma node_mmap_success : forall ms model x8 (I : Type) (E : I -> SyscallEffect) (M : I -> Model)
                                 (i0 : I),
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 222%Z ->
  (forall i, syscall_spec (sys_input segs ms x8) model (Ok (E i) (M i) [])) ->
  (forall i, bv_eqb (eff_ret (E i)) (errno_ret ENOMEM) = false) ->
  (forall eff m' evs, syscall_spec (sys_input segs ms x8) model (Ok eff m' evs) ->
     evs = [] /\ (bv_eqb (eff_ret eff) (errno_ret ENOMEM) = true \/ exists i, eff = E i /\ m' = M i)) ->
  ~ syscall_spec (sys_input segs ms x8) model Unmodeled ->
  (forall eff m' evs, syscall_spec (sys_input segs ms x8) model (Ok eff m' evs) ->
     vm_only model m') ->
  (forall i, syscall_effect_accesses (E i) = []) ->
  node_ok_cfg segs cfg (mkCfg ms model) I (fun _ => [])
    (fun i => mkCfg (advance_past_svc (apply_effect ms (E i))) (M i)).
Proof.
  intros ms model x8 I E M i0 Hh Hsvc Hno Hcomp Hnr Hchar Hnu Hframe Hacc.
  apply (node_forced_success segs cfg ms model x8 I E M M (fun _ => []) i0
           (mmap_family_off segs cfg ms x8 Hno Hoff) Hh Hsvc Hcomp).
  - intro i. rewrite refusal_b_mmap by exact Hno. apply Hnr.
  - intros eff m' evs Hs Hr. rewrite refusal_b_mmap in Hr by exact Hno.
    destruct (Hchar eff m' evs Hs) as (-> & [Hbad | (i & -> & ->)]);
      [rewrite Hbad in Hr; discriminate Hr|].
    exists i. auto.
  - exact Hnu.
  - intros eff m' evs Hs. rewrite (vm_only_halted _ _ (Hframe _ _ _ Hs)). exact Hh.
  - intro i. rewrite Hacc. apply materialize_nil.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma node_mmap_forced : forall ms model x8 (I : Type) (E : I -> SyscallEffect) (M : I -> Model),
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 222%Z ->
  (forall i, syscall_spec (sys_input segs ms x8) model (Ok (E i) (M i) [])) ->
  (forall eff m' evs, syscall_spec (sys_input segs ms x8) model (Ok eff m' evs) ->
     evs = [] /\ bv_eqb (eff_ret eff) (errno_ret ENOMEM) = true /\ exists i, eff = E i /\ m' = M i) ->
  ~ syscall_spec (sys_input segs ms x8) model Unmodeled ->
  (forall eff m' evs, syscall_spec (sys_input segs ms x8) model (Ok eff m' evs) ->
     vm_only model m') ->
  (forall i, syscall_effect_accesses (E i) = []) ->
  node_ok_cfg segs cfg (mkCfg ms model) I (fun _ => [])
    (fun i => mkCfg (advance_past_svc (apply_effect ms (E i))) (M i)).
Proof.
  intros ms model x8 I E M Hh Hsvc Hno Hcomp Hchar Hnu Hframe Hacc.
  apply (node_forced_refusal segs cfg ms model x8 I E M M (fun _ => []) Hh Hsvc Hcomp).
  - intros eff m' evs Hs. rewrite refusal_b_mmap by exact Hno.
    exact (proj1 (proj2 (Hchar eff m' evs Hs))).
  - intros eff m' evs Hs. destruct (Hchar eff m' evs Hs) as (-> & _ & (i & -> & ->)).
    exists i. auto.
  - exact Hnu.
  - intros eff m' evs Hs. rewrite (vm_only_halted _ _ (Hframe _ _ _ Hs)). exact Hh.
  - intro i. rewrite Hacc. apply materialize_nil.
Qed.

End MmapGeneric.

Lemma page_round_up_Z_nonneg' : forall z, (0 <= z)%Z -> (0 <= page_round_up_Z z)%Z.
Proof. intros z Hz. pose proof (page_round_up_Z_bounds z). lia. Qed.

Lemma len_nZ_nonneg : forall len : word, (0 <= page_round_up_Z (bv_unsigned len))%Z.
Proof. intros len. apply page_round_up_Z_nonneg'. apply bv_unsigned_in_range. Qed.

Section MmapFresh.
Variable segs : list Segment.
Variable cfg : SpuriousCfg.
Hypothesis Hoff : sc_alloc cfg = false.

(* [comment removed for export] *)
#[using="Hoff"] Lemma node_mmap_fresh_rw : forall ms model x8,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 222%Z ->
  mmap_off_aligned_b (ms_gpr ms 5) = true ->
  mmap_anon_b (ms_gpr ms 3) = true ->
  w_is0 (ms_gpr ms 1) = false ->
  mmap_modeled_b (ms_gpr ms 2) (ms_gpr ms 3) (ms_gpr ms 5) = true ->
  (exists a, fresh_rw_guard (ms_gpr ms 3) model (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) a) ->
  node_ok_cfg segs cfg (mkCfg ms model)
    {a : word | fresh_rw_guard (ms_gpr ms 3) model (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) a}
    (fun _ => [])
    (fun a => mkCfg (advance_past_svc (apply_effect ms
                       (mkEffect (proj1_sig a) []
                          [(proj1_sig a, Z_to_bv 64 (page_round_up_Z (bv_unsigned (ms_gpr ms 1))))])))
                    (fresh_rw_next (ms_gpr ms 3) (proj1_sig a)
                       (Z_to_bv 64 (page_round_up_Z (bv_unsigned (ms_gpr ms 1)))) model)).
Proof.
  intros ms model x8 Hh Hsvc Hno Ho Ha Hl Hm [a0 Ha0].
  set (nZ := page_round_up_Z (bv_unsigned (ms_gpr ms 1))).
  pose proof (len_nZ_nonneg (ms_gpr ms 1)) as HnZ. fold nZ in HnZ.
  apply (node_mmap_success segs cfg Hoff ms model x8 _
           (fun a => mkEffect (proj1_sig a) [] [(proj1_sig a, Z_to_bv 64 nZ)])
           (fun a => fresh_rw_next (ms_gpr ms 3) (proj1_sig a) (Z_to_bv 64 nZ) model)
           (exist _ a0 Ha0) Hh Hsvc Hno).
  - intros [a Hga]. cbn [proj1_sig].
    apply (proj2 (syscall_spec_mmap segs ms x8 model _ Hno)).
    apply (proj2 (mmap_spec_fresh_rw _ _ _ _ _ _ _ _ _ Ho Ha Hl Hm)).
    right. apply choose_arm_ok. exists a. auto.
  - intros [a Hga]. cbn [proj1_sig eff_ret].
    apply (below_top_not_errno (m_vmmaps model)); [exact ENOMEM_range|].
    destruct Hga as (_ & _ & Htop & _). fold nZ in Htop. lia.
  - intros eff m' evs Hs.
    apply (proj1 (syscall_spec_mmap segs ms x8 model _ Hno)) in Hs.
    apply (proj1 (mmap_spec_fresh_rw _ _ _ _ _ _ _ _ _ Ho Ha Hl Hm)) in Hs.
    destruct Hs as [Hs | Hs].
    + apply errno_arm_ok in Hs as (e & [<- | []] & -> & -> & ->).
      split; [reflexivity|]. left. unfold bv_eqb. apply Z.eqb_refl.
    + apply choose_arm_ok in Hs as (a & Hga & -> & -> & ->).
      split; [reflexivity|]. right. exists (exist _ a Hga). auto.
  - intro Hu.
    apply (proj1 (syscall_spec_mmap segs ms x8 model _ Hno)) in Hu.
    apply (proj1 (mmap_spec_fresh_rw _ _ _ _ _ _ _ _ _ Ho Ha Hl Hm)) in Hu.
    destruct Hu as [Hu | Hu]; [exact (errno_arm_unmodeled _ _ _ Hu) | exact (choose_arm_unmodeled _ _ _ _ _ Hu)].
  - intros eff m' evs Hs.
    apply (proj1 (syscall_spec_mmap segs ms x8 model _ Hno)) in Hs.
    apply (proj1 (mmap_spec_fresh_rw _ _ _ _ _ _ _ _ _ Ho Ha Hl Hm)) in Hs.
    destruct Hs as [Hs | Hs].
    + apply errno_arm_ok in Hs as (e & _ & -> & -> & ->). apply vm_only_refl.
    + apply choose_arm_ok in Hs as (a & _ & -> & -> & ->). apply vm_only_fresh_rw_next.
  - intros i. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma node_mmap_fresh_rw_forced : forall ms model x8,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 222%Z ->
  mmap_off_aligned_b (ms_gpr ms 5) = true ->
  mmap_anon_b (ms_gpr ms 3) = true ->
  w_is0 (ms_gpr ms 1) = false ->
  mmap_modeled_b (ms_gpr ms 2) (ms_gpr ms 3) (ms_gpr ms 5) = true ->
  ~ (exists a, fresh_rw_guard (ms_gpr ms 3) model (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) a) ->
  node_ok_cfg segs cfg (mkCfg ms model) unit (fun _ => [])
    (fun _ => mkCfg (advance_past_svc (apply_effect ms (mkEffect (errno_ret ENOMEM) [] []))) model).
Proof.
  intros ms model x8 Hh Hsvc Hno Ho Ha Hl Hm Hnex.
  apply (node_mmap_forced segs cfg ms model x8 unit
           (fun _ => mkEffect (errno_ret ENOMEM) [] []) (fun _ => model) Hh Hsvc Hno).
  - intros []. apply (proj2 (syscall_spec_mmap segs ms x8 model _ Hno)).
    apply (proj2 (mmap_spec_fresh_rw _ _ _ _ _ _ _ _ _ Ho Ha Hl Hm)).
    left. apply errno_arm_ok. exists ENOMEM. split; [now left|]. auto.
  - intros eff m' evs Hs.
    apply (proj1 (syscall_spec_mmap segs ms x8 model _ Hno)) in Hs.
    apply (proj1 (mmap_spec_fresh_rw _ _ _ _ _ _ _ _ _ Ho Ha Hl Hm)) in Hs.
    destruct Hs as [Hs | Hs].
    + apply errno_arm_ok in Hs as (e & [<- | []] & -> & -> & ->).
      split; [reflexivity|]. split; [unfold bv_eqb; apply Z.eqb_refl|]. exists tt. auto.
    + apply choose_arm_ok in Hs as (a & Hga & _ & _ & _). exfalso. apply Hnex. exists a. exact Hga.
  - intro Hu.
    apply (proj1 (syscall_spec_mmap segs ms x8 model _ Hno)) in Hu.
    apply (proj1 (mmap_spec_fresh_rw _ _ _ _ _ _ _ _ _ Ho Ha Hl Hm)) in Hu.
    destruct Hu as [Hu | Hu]; [exact (errno_arm_unmodeled _ _ _ Hu) | exact (choose_arm_unmodeled _ _ _ _ _ Hu)].
  - intros eff m' evs Hs.
    apply (proj1 (syscall_spec_mmap segs ms x8 model _ Hno)) in Hs.
    apply (proj1 (mmap_spec_fresh_rw _ _ _ _ _ _ _ _ _ Ho Ha Hl Hm)) in Hs.
    destruct Hs as [Hs | Hs].
    + apply errno_arm_ok in Hs as (e & _ & -> & -> & ->). apply vm_only_refl.
    + apply choose_arm_ok in Hs as (a & _ & -> & -> & ->). apply vm_only_fresh_rw_next.
  - intros i. reflexivity.
Qed.

End MmapFresh.

(* [comment removed for export] *)
Section MmapAltChoose.
Variable segs : list Segment.
Variable cfg : SpuriousCfg.
Hypothesis Hoff : sc_alloc cfg = false.

Definition mmap_alt_choose (G : word -> Prop) (F : word -> Model) (E : word -> SyscallEffect)
    : Sys SyscallEffect :=
  alt (e <- errno_from mmap_errnos ;; err_ret e)%sys
      (a <- choose G ;; modify (fun _ => F a) ;; pure (E a))%sys.

#[using="Type"] Lemma mmap_alt_choose_ok : forall G F E i m eff m' evs,
  mmap_alt_choose G F E i m (Ok eff m' evs) <->
  evs = [] /\ ((eff = mkEffect (errno_ret ENOMEM) [] [] /\ m' = m)
               \/ exists a, G a /\ eff = E a /\ m' = F a).
Proof.
  intros G F E i m eff m' evs. unfold mmap_alt_choose, alt. split.
  - intros [Hs | Hs].
    + apply errno_arm_ok in Hs as (e & [<- | []] & -> & -> & ->). split; [reflexivity|]. left. auto.
    + apply choose_arm_ok in Hs as (a & Ha & -> & -> & ->). split; [reflexivity|]. right. eauto.
  - intros (-> & [(-> & ->) | (a & Ha & -> & ->)]).
    + left. apply errno_arm_ok. exists ENOMEM. split; [now left|]. auto.
    + right. apply choose_arm_ok. exists a. auto.
Qed.

#[using="Type"] Lemma mmap_alt_choose_unmodeled : forall G F E i m, ~ mmap_alt_choose G F E i m Unmodeled.
Proof.
  intros G F E i m [Hu | Hu];
    [exact (errno_arm_unmodeled _ _ _ Hu) | exact (choose_arm_unmodeled _ _ _ _ _ Hu)].
Qed.

#[using="Hoff"] Lemma node_mmap_alt_choose : forall ms model x8 (G : word -> Prop) (F : word -> Model)
                                    (E : word -> SyscallEffect),
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 222%Z ->
  (forall o, syscall_spec (sys_input segs ms x8) model o <->
             mmap_alt_choose G F E (sys_input segs ms x8) model o) ->
  (forall a, G a -> bv_eqb (eff_ret (E a)) (errno_ret ENOMEM) = false) ->
  (forall a, vm_only model (F a)) ->
  (forall a, syscall_effect_accesses (E a) = []) ->
  (exists a, G a) ->
  node_ok_cfg segs cfg (mkCfg ms model) {a : word | G a} (fun _ => [])
    (fun a => mkCfg (advance_past_svc (apply_effect ms (E (proj1_sig a)))) (F (proj1_sig a))).
Proof.
  intros ms model x8 G F E Hh Hsvc Hno Hbr Hnr Hfr Hacc [a0 Ha0].
  apply (node_mmap_success segs cfg Hoff ms model x8 _ (fun a => E (proj1_sig a))
           (fun a => F (proj1_sig a)) (exist _ a0 Ha0) Hh Hsvc Hno).
  - intros [a Ha]. apply Hbr. apply mmap_alt_choose_ok. split; [reflexivity|]. right. eauto.
  - intros [a Ha]. apply Hnr. exact Ha.
  - intros eff m' evs Hs. apply Hbr, mmap_alt_choose_ok in Hs as (-> & [(-> & ->) | (a & Ha & -> & ->)]).
    + split; [reflexivity|]. left. unfold bv_eqb. apply Z.eqb_refl.
    + split; [reflexivity|]. right. exists (exist _ a Ha). auto.
  - intro Hu. apply Hbr in Hu. exact (mmap_alt_choose_unmodeled _ _ _ _ _ Hu).
  - intros eff m' evs Hs. apply Hbr, mmap_alt_choose_ok in Hs as (-> & [(-> & ->) | (a & Ha & -> & ->)]).
    + apply vm_only_refl.
    + apply Hfr.
  - intros a. apply Hacc.
Qed.

#[using="Type"] Lemma node_mmap_alt_choose_forced : forall ms model x8 (G : word -> Prop) (F : word -> Model)
                                           (E : word -> SyscallEffect),
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 222%Z ->
  (forall o, syscall_spec (sys_input segs ms x8) model o <->
             mmap_alt_choose G F E (sys_input segs ms x8) model o) ->
  (forall a, vm_only model (F a)) ->
  ~ (exists a, G a) ->
  node_ok_cfg segs cfg (mkCfg ms model) unit (fun _ => [])
    (fun _ => mkCfg (advance_past_svc (apply_effect ms (mkEffect (errno_ret ENOMEM) [] []))) model).
Proof.
  intros ms model x8 G F E Hh Hsvc Hno Hbr Hfr Hnex.
  apply (node_mmap_forced segs cfg ms model x8 unit
           (fun _ => mkEffect (errno_ret ENOMEM) [] []) (fun _ => model) Hh Hsvc Hno).
  - intros []. apply Hbr. apply mmap_alt_choose_ok. split; [reflexivity|]. left. auto.
  - intros eff m' evs Hs. apply Hbr, mmap_alt_choose_ok in Hs as (-> & [(-> & ->) | (a & Ha & -> & ->)]).
    + split; [reflexivity|]. split; [unfold bv_eqb; apply Z.eqb_refl|]. exists tt. auto.
    + exfalso. apply Hnex. exists a. exact Ha.
  - intro Hu. apply Hbr in Hu. exact (mmap_alt_choose_unmodeled _ _ _ _ _ Hu).
  - intros eff m' evs Hs. apply Hbr, mmap_alt_choose_ok in Hs as (-> & [(-> & ->) | (a & Ha & -> & ->)]).
    + apply vm_only_refl.
    + apply Hfr.
  - intros []. reflexivity.
Qed.

End MmapAltChoose.

(* [comment removed for export] *)
Lemma node_mmap_fresh_na : forall segs cfg (Hoff : sc_alloc cfg = false) ms model x8,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 222%Z ->
  mmap_off_aligned_b (ms_gpr ms 5) = true ->
  mmap_anon_b (ms_gpr ms 3) = true ->
  w_is0 (ms_gpr ms 1) = false ->
  mmap_modeled_b (ms_gpr ms 2) (ms_gpr ms 3) (ms_gpr ms 5) = false ->
  mmap_noaccess_b (ms_gpr ms 2) (ms_gpr ms 3) (ms_gpr ms 5) = true ->
  (exists a, place_ok model (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) a) ->
  node_ok_cfg segs cfg (mkCfg ms model)
    {a : word | place_ok model (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) a}
    (fun _ => [])
    (fun a => mkCfg (advance_past_svc (apply_effect ms
                       (mkEffectU (proj1_sig a) [] []
                          [(proj1_sig a, Z_to_bv 64 (page_round_up_Z (bv_unsigned (ms_gpr ms 1))))] [] [])))
                    (fresh_na_next (ms_gpr ms 3) (proj1_sig a)
                       (Z_to_bv 64 (page_round_up_Z (bv_unsigned (ms_gpr ms 1)))) model)).
Proof.
  intros segs cfg Hoff ms model x8 Hh Hsvc Hno Ho Ha Hl Hm Hn Hex.
  pose proof (len_nZ_nonneg (ms_gpr ms 1)) as HnZ.
  apply (node_mmap_alt_choose segs cfg Hoff ms model x8
           (place_ok model (page_round_up_Z (bv_unsigned (ms_gpr ms 1))))
           (fun a => fresh_na_next (ms_gpr ms 3) a
                       (Z_to_bv 64 (page_round_up_Z (bv_unsigned (ms_gpr ms 1)))) model)
           (fun a => mkEffectU a [] []
                       [(a, Z_to_bv 64 (page_round_up_Z (bv_unsigned (ms_gpr ms 1))))] [] [])
           Hh Hsvc Hno).
  - intro o. rewrite (syscall_spec_mmap segs ms x8 model o Hno).
    exact (mmap_spec_fresh_na _ _ _ _ _ _ _ _ _ Ho Ha Hl Hm Hn).
  - intros a Hga. cbn [eff_ret].
    apply (below_top_not_errno (m_vmmaps model)); [exact ENOMEM_range|].
    destruct Hga as (_ & _ & Htop & _). lia.
  - intros a. apply vm_only_fresh_na_next.
  - intros a. reflexivity.
  - exact Hex.
Qed.

Lemma node_mmap_fresh_na_forced : forall segs cfg (Hoff : sc_alloc cfg = false) ms model x8,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 222%Z ->
  mmap_off_aligned_b (ms_gpr ms 5) = true ->
  mmap_anon_b (ms_gpr ms 3) = true ->
  w_is0 (ms_gpr ms 1) = false ->
  mmap_modeled_b (ms_gpr ms 2) (ms_gpr ms 3) (ms_gpr ms 5) = false ->
  mmap_noaccess_b (ms_gpr ms 2) (ms_gpr ms 3) (ms_gpr ms 5) = true ->
  ~ (exists a, place_ok model (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) a) ->
  node_ok_cfg segs cfg (mkCfg ms model) unit (fun _ => [])
    (fun _ => mkCfg (advance_past_svc (apply_effect ms (mkEffect (errno_ret ENOMEM) [] []))) model).
Proof.
  intros segs cfg Hoff ms model x8 Hh Hsvc Hno Ho Ha Hl Hm Hn Hnex.
  apply (node_mmap_alt_choose_forced segs cfg ms model x8
           (place_ok model (page_round_up_Z (bv_unsigned (ms_gpr ms 1))))
           (fun a => fresh_na_next (ms_gpr ms 3) a
                       (Z_to_bv 64 (page_round_up_Z (bv_unsigned (ms_gpr ms 1)))) model)
           (fun a => mkEffectU a [] []
                       [(a, Z_to_bv 64 (page_round_up_Z (bv_unsigned (ms_gpr ms 1))))] [] [])
           Hh Hsvc Hno).
  - intro o. rewrite (syscall_spec_mmap segs ms x8 model o Hno).
    exact (mmap_spec_fresh_na _ _ _ _ _ _ _ _ _ Ho Ha Hl Hm Hn).
  - intros a. apply vm_only_fresh_na_next.
  - exact Hnex.
Qed.

(* [comment removed for export] *)
Lemma place_ok_exists : forall (m : Model) (nZ : Z),
  (0 < nZ)%Z ->
  (page_size + ledger_size (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m))
   + Z.of_nat (length (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m))) * (nZ + page_size) + nZ
   <= alloc_top (m_vmmaps m))%Z ->
  exists a, place_ok m nZ a.
Proof.
  intros m nZ HnZ Hb. destruct (null_hint_placement (m_vmmaps m) nZ HnZ Hb) as (a & H1 & H2 & H3 & H4).
  exists a. unfold place_ok. auto.
Qed.

Lemma fresh_rw_guard_exists : forall (flags : word) (m : Model) (nZ : Z),
  (0 < nZ)%Z ->
  mmap_noreserve_backed_ok flags m nZ = true ->
  (page_size + ledger_size (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m))
   + Z.of_nat (length (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m))) * (nZ + page_size) + nZ
   <= alloc_top (m_vmmaps m))%Z ->
  exists a, fresh_rw_guard flags m nZ a.
Proof.
  intros flags m nZ HnZ Hbud Hb. destruct (place_ok_exists m nZ HnZ Hb) as (a & Ha).
  exists a. apply fresh_rw_guard_iff. auto.
Qed.

(* [comment removed for export] *)
Lemma len_nZ_pos : forall len : word, w_is0 len = false -> (0 < page_round_up_Z (bv_unsigned len))%Z.
Proof.
  intros len Hl. pose proof (page_round_up_Z_bounds (bv_unsigned len)).
  assert (bv_unsigned len <> 0%Z).
  { intro E. unfold w_is0, bv_eqb in Hl. rewrite E in Hl. discriminate Hl. }
  pose proof (bv_unsigned_in_range 64 len). lia.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition fixed_na_next (flags addr n : word) (m : Model) : Model :=
  with_mmap_replacement flags addr n
    (with_vmmaps (mkVmMapsFull (vm_reserved (m_vmmaps m)) (vm_maps (m_vmmaps m))
       ((addr, n) :: maps_subtract (vm_noaccess (m_vmmaps m))
                       (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n))
       (vm_start_brk (m_vmmaps m)) (vm_brk (m_vmmaps m)) (vm_limit (m_vmmaps m))
       (vm_mmap_base (m_vmmaps m)) (vm_init_sp (m_vmmaps m))) m).

Definition fixed_rw_next (flags addr n : word) (m : Model) : Model :=
  with_mmap_replacement flags addr n (with_vmmaps (mmap_fixed_rw_next (m_vmmaps m) addr n) m).

Definition fixed_destroyed (addr n : word) (m : Model) : Model :=
  with_mmap_destroyed addr n (mmap_fixed_destroyed_next (m_vmmaps m) addr n) m.

Lemma vm_only_with_mmap_replacement : forall flags a n m, vm_only m (with_mmap_replacement flags a n m).
Proof.
  intros. unfold with_mmap_replacement.
  eapply vm_only_trans; [apply vm_only_vm_forget_range | apply vm_only_with_mmap_backing].
Qed.

Lemma vm_only_fixed_na_next : forall flags a n m, vm_only m (fixed_na_next flags a n m).
Proof.
  intros. unfold fixed_na_next.
  eapply vm_only_trans; [apply vm_only_with_vmmaps | apply vm_only_with_mmap_replacement].
Qed.

Lemma vm_only_fixed_rw_next : forall flags a n m, vm_only m (fixed_rw_next flags a n m).
Proof.
  intros. unfold fixed_rw_next.
  eapply vm_only_trans; [apply vm_only_with_vmmaps | apply vm_only_with_mmap_replacement].
Qed.

Lemma vm_only_fixed_destroyed : forall a n m, vm_only m (fixed_destroyed a n m).
Proof.
  intros. unfold fixed_destroyed, with_mmap_destroyed.
  eapply vm_only_trans; [apply vm_only_with_vmmaps | apply vm_only_vm_forget_range].
Qed.

(* [comment removed for export] *)
Definition fixed_gate (m : Model) (addr len : word) : Prop :=
  (bv_unsigned addr + page_round_up_Z (bv_unsigned len) <= alloc_top (m_vmmaps m))%Z
  /\ (bv_unsigned addr mod page_size = 0)%Z /\ (0 < bv_unsigned addr)%Z.

Lemma fixed_gate_bools : forall m addr len, fixed_gate m addr len ->
  (two_pow_64 <=? bv_unsigned addr + page_round_up_Z (bv_unsigned len))%Z = false
  /\ (bv_unsigned addr + page_round_up_Z (bv_unsigned len) <=? alloc_top (m_vmmaps m))%Z = true
  /\ Z.eqb (bv_unsigned addr mod page_size) 0 = true
  /\ (0 <? bv_unsigned addr)%Z = true.
Proof.
  intros m addr len (H1 & H2 & H3). pose proof (alloc_top_lt (m_vmmaps m)).
  split; [apply Z.leb_gt; lia|]. split; [apply Z.leb_le; lia|].
  split; [apply Z.eqb_eq; exact H2 | apply Z.ltb_lt; exact H3].
Qed.

(* [comment removed for export] *)
Definition mmap_alt3 (SUCC : Sys SyscallEffect) (Fd : Model) (U : list (word * word))
    : Sys SyscallEffect :=
  alt (e <- errno_from mmap_errnos ;; err_ret e)%sys
      (alt SUCC
         (e <- errno_from mmap_errnos ;; modify (fun _ => Fd) ;;
          pure (mkEffectU (errno_ret e) [] [] U [] []))%sys).

Lemma mmap_alt3_ok : forall SUCC Fd U i m eff m' evs,
  mmap_alt3 SUCC Fd U i m (Ok eff m' evs) <->
  (evs = [] /\ eff = mkEffect (errno_ret ENOMEM) [] [] /\ m' = m)
  \/ SUCC i m (Ok eff m' evs)
  \/ (evs = [] /\ eff = mkEffectU (errno_ret ENOMEM) [] [] U [] [] /\ m' = Fd).
Proof.
  intros SUCC Fd U i m eff m' evs. unfold mmap_alt3, alt. split.
  - intros [Hs | [Hs | Hs]].
    + apply errno_arm_ok in Hs as (e & [<- | []] & -> & -> & ->). left. auto.
    + right. left. exact Hs.
    + apply destr_arm_ok in Hs as (e & [<- | []] & -> & -> & ->). right. right. auto.
  - intros [(-> & -> & ->) | [Hs | (-> & -> & ->)]].
    + left. apply errno_arm_ok. exists ENOMEM. split; [now left | auto].
    + right. left. exact Hs.
    + right. right. apply destr_arm_ok. exists ENOMEM. split; [now left | auto].
Qed.

Lemma mmap_alt3_unmodeled : forall SUCC Fd U i m,
  ~ SUCC i m Unmodeled -> ~ mmap_alt3 SUCC Fd U i m Unmodeled.
Proof.
  intros SUCC Fd U i m Hs [Hu | [Hu | Hu]];
    [exact (errno_arm_unmodeled _ _ _ Hu) | exact (Hs Hu) | exact (destr_arm_unmodeled _ _ _ _ _ Hu)].
Qed.

(* [comment removed for export] *)
Lemma mmap_spec_fixed_na_contained : forall addr len prot flags fd off i m o,
  mmap_off_aligned_b off = true -> mmap_anon_b flags = true -> w_is0 len = false ->
  mmap_modeled_b prot flags off = false -> mmap_noaccess_b prot flags off = false ->
  mmap_fixed_noaccess_b prot flags off = true ->
  fixed_gate m addr len ->
  region_free (vm_reserved (m_vmmaps m)) addr (Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))
  && map_contains (vm_maps (m_vmmaps m)) addr (Z_to_bv 64 (page_round_up_Z (bv_unsigned len))) = true ->
  (mmap_spec addr len prot flags fd off i m o <->
   mmap_alt3
     (modify (fun _ => fixed_na_next flags addr (Z_to_bv 64 (page_round_up_Z (bv_unsigned len))) m) ;;
      pure (mkEffectU addr [] [] [(addr, Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))] [] []))%sys
     (fixed_destroyed addr (Z_to_bv 64 (page_round_up_Z (bv_unsigned len))) m)
     [(addr, Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))] i m o).
Proof.
  intros addr len prot flags fd off i m o Ho Ha Hl Hm Hn Hf Hg Hc.
  destruct (fixed_gate_bools m addr len Hg) as (G1 & G2 & G3 & G4).
  unfold mmap_spec. rewrite Ho, Ha, Hl, Hm, Hn, Hf. cbn [negb]. rewrite G1.
  rewrite bind_get_model. rewrite G2, G3, G4. cbn [negb]. rewrite Hc. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma mmap_spec_fixed_rw_contained : forall addr len prot flags fd off i m o,
  mmap_off_aligned_b off = true -> mmap_anon_b flags = true -> w_is0 len = false ->
  mmap_modeled_b prot flags off = false -> mmap_noaccess_b prot flags off = false ->
  mmap_fixed_noaccess_b prot flags off = false -> mmap_fixed_rw_b prot flags off = true ->
  fixed_gate m addr len ->
  region_free (vm_reserved (m_vmmaps m)) addr (Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))
  && map_contains (vm_maps (m_vmmaps m)) addr (Z_to_bv 64 (page_round_up_Z (bv_unsigned len))) = true ->
  (mmap_spec addr len prot flags fd off i m o <->
   mmap_alt3
     (_ <- choose (fun _ : unit =>
             mmap_fixed_rw_budget_ok flags m addr (Z_to_bv 64 (page_round_up_Z (bv_unsigned len))) = true) ;;
      modify (fun _ => fixed_rw_next flags addr (Z_to_bv 64 (page_round_up_Z (bv_unsigned len))) m) ;;
      pure (mkEffect addr [] [(addr, Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))]))%sys
     (fixed_destroyed addr (Z_to_bv 64 (page_round_up_Z (bv_unsigned len))) m)
     [(addr, Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))] i m o).
Proof.
  intros addr len prot flags fd off i m o Ho Ha Hl Hm Hn Hf Hfrw Hg Hc.
  destruct (fixed_gate_bools m addr len Hg) as (G1 & G2 & G3 & G4).
  unfold mmap_spec. rewrite Ho, Ha, Hl, Hm, Hn, Hf, Hfrw. cbn [negb]. rewrite G1.
  rewrite bind_get_model. rewrite G2, G3, G4. cbn [negb]. rewrite Hc. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma mmap_spec_fixed_na_free : forall addr len prot flags fd off i m o,
  mmap_off_aligned_b off = true -> mmap_anon_b flags = true -> w_is0 len = false ->
  mmap_modeled_b prot flags off = false -> mmap_noaccess_b prot flags off = false ->
  mmap_fixed_noaccess_b prot flags off = true ->
  fixed_gate m addr len ->
  region_free (vm_reserved (m_vmmaps m)) addr (Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))
  && map_contains (vm_maps (m_vmmaps m)) addr (Z_to_bv 64 (page_round_up_Z (bv_unsigned len))) = false ->
  region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) addr
    (Z_to_bv 64 (page_round_up_Z (bv_unsigned len))) = true ->
  (mmap_spec addr len prot flags fd off i m o <->
   mmap_alt_choose (fun a => a = addr)
     (fun a => fresh_na_next flags a (Z_to_bv 64 (page_round_up_Z (bv_unsigned len))) m)
     (fun a => mkEffectU a [] [] [(a, Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))] [] [])
     i m o).
Proof.
  intros addr len prot flags fd off i m o Ho Ha Hl Hm Hn Hf Hg Hc Hfr.
  destruct (fixed_gate_bools m addr len Hg) as (G1 & G2 & G3 & G4).
  unfold mmap_spec. rewrite Ho, Ha, Hl, Hm, Hn, Hf. cbn [negb]. rewrite G1.
  rewrite bind_get_model. rewrite G2, G3, G4. cbn [negb]. rewrite Hc, Hfr. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma mmap_spec_fixed_rw_free : forall addr len prot flags fd off i m o,
  mmap_off_aligned_b off = true -> mmap_anon_b flags = true -> w_is0 len = false ->
  mmap_modeled_b prot flags off = false -> mmap_noaccess_b prot flags off = false ->
  mmap_fixed_noaccess_b prot flags off = false -> mmap_fixed_rw_b prot flags off = true ->
  fixed_gate m addr len ->
  region_free (vm_reserved (m_vmmaps m)) addr (Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))
  && map_contains (vm_maps (m_vmmaps m)) addr (Z_to_bv 64 (page_round_up_Z (bv_unsigned len))) = false ->
  region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) addr
    (Z_to_bv 64 (page_round_up_Z (bv_unsigned len))) = true ->
  (mmap_spec addr len prot flags fd off i m o <->
   mmap_alt_choose
     (fun a => a = addr /\ mmap_noreserve_backed_ok flags m (page_round_up_Z (bv_unsigned len)) = true)
     (fun a => fresh_rw_next flags a (Z_to_bv 64 (page_round_up_Z (bv_unsigned len))) m)
     (fun a => mkEffect a [] [(a, Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))])
     i m o).
Proof.
  intros addr len prot flags fd off i m o Ho Ha Hl Hm Hn Hf Hfrw Hg Hc Hfr.
  destruct (fixed_gate_bools m addr len Hg) as (G1 & G2 & G3 & G4).
  unfold mmap_spec. rewrite Ho, Ha, Hl, Hm, Hn, Hf, Hfrw. cbn [negb]. rewrite G1.
  rewrite bind_get_model. rewrite G2, G3, G4. cbn [negb]. rewrite Hc, Hfr. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma mmap_spec_noreplace_na_free : forall addr len prot flags fd off i m o,
  mmap_off_aligned_b off = true -> mmap_anon_b flags = true -> w_is0 len = false ->
  mmap_modeled_b prot flags off = false -> mmap_noaccess_b prot flags off = false ->
  mmap_fixed_noaccess_b prot flags off = false -> mmap_fixed_rw_b prot flags off = false ->
  mmap_noreplace_noaccess_b prot flags off = true ->
  fixed_gate m addr len ->
  region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) addr
    (Z_to_bv 64 (page_round_up_Z (bv_unsigned len))) = true ->
  (mmap_spec addr len prot flags fd off i m o <->
   mmap_alt_choose (fun a => a = addr)
     (fun a => fresh_na_next flags a (Z_to_bv 64 (page_round_up_Z (bv_unsigned len))) m)
     (fun a => mkEffectU a [] [] [(a, Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))] [] [])
     i m o).
Proof.
  intros addr len prot flags fd off i m o Ho Ha Hl Hm Hn Hf Hfrw Hnr Hg Hfr.
  destruct (fixed_gate_bools m addr len Hg) as (G1 & G2 & G3 & G4).
  unfold mmap_spec. rewrite Ho, Ha, Hl, Hm, Hn, Hf, Hfrw, Hnr. cbn [negb]. rewrite G1.
  rewrite bind_get_model. rewrite G2, G3, G4. cbn [negb]. rewrite Hfr. reflexivity.
Qed.

Lemma mmap_spec_noreplace_rw_free : forall addr len prot flags fd off i m o,
  mmap_off_aligned_b off = true -> mmap_anon_b flags = true -> w_is0 len = false ->
  mmap_modeled_b prot flags off = false -> mmap_noaccess_b prot flags off = false ->
  mmap_fixed_noaccess_b prot flags off = false -> mmap_fixed_rw_b prot flags off = false ->
  mmap_noreplace_noaccess_b prot flags off = false -> mmap_noreplace_rw_b prot flags off = true ->
  fixed_gate m addr len ->
  region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) addr
    (Z_to_bv 64 (page_round_up_Z (bv_unsigned len))) = true ->
  (mmap_spec addr len prot flags fd off i m o <->
   mmap_alt_choose
     (fun a => a = addr /\ mmap_noreserve_backed_ok flags m (page_round_up_Z (bv_unsigned len)) = true)
     (fun a => fresh_rw_next flags a (Z_to_bv 64 (page_round_up_Z (bv_unsigned len))) m)
     (fun a => mkEffect a [] [(a, Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))])
     i m o).
Proof.
  intros addr len prot flags fd off i m o Ho Ha Hl Hm Hn Hf Hfrw Hnr Hnrw Hg Hfr.
  destruct (fixed_gate_bools m addr len Hg) as (G1 & G2 & G3 & G4).
  unfold mmap_spec. rewrite Ho, Ha, Hl, Hm, Hn, Hf, Hfrw, Hnr, Hnrw. cbn [negb]. rewrite G1.
  rewrite bind_get_model. rewrite G2, G3, G4. cbn [negb]. rewrite Hfr. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma mmap_spec_noreplace_occupied : forall addr len prot flags fd off i m o,
  mmap_off_aligned_b off = true -> mmap_anon_b flags = true -> w_is0 len = false ->
  mmap_modeled_b prot flags off = false -> mmap_noaccess_b prot flags off = false ->
  mmap_fixed_noaccess_b prot flags off = false -> mmap_fixed_rw_b prot flags off = false ->
  (mmap_noreplace_noaccess_b prot flags off = true \/
   (mmap_noreplace_noaccess_b prot flags off = false /\ mmap_noreplace_rw_b prot flags off = true)) ->
  fixed_gate m addr len ->
  region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) addr
    (Z_to_bv 64 (page_round_up_Z (bv_unsigned len))) = false ->
  (mmap_spec addr len prot flags fd off i m o <->
   alt (e <- errno_from mmap_errnos ;; err_ret e)%sys (err_ret EEXIST) i m o).
Proof.
  intros addr len prot flags fd off i m o Ho Ha Hl Hm Hn Hf Hfrw Hsel Hg Hfr.
  destruct (fixed_gate_bools m addr len Hg) as (G1 & G2 & G3 & G4).
  unfold mmap_spec. rewrite Ho, Ha, Hl, Hm, Hn, Hf, Hfrw. cbn [negb].
  destruct Hsel as [Hnr | (Hnr & Hnrw)].
  - rewrite Hnr. rewrite G1. rewrite bind_get_model. rewrite G2, G3, G4. cbn [negb].
    rewrite Hfr. reflexivity.
  - rewrite Hnr, Hnrw. rewrite G1. rewrite bind_get_model. rewrite G2, G3, G4. cbn [negb].
    rewrite Hfr. reflexivity.
Qed.

Section MmapFixedNodes.
Variable segs : list Segment.
Variable cfg : SpuriousCfg.
Hypothesis Hoff : sc_alloc cfg = false.

(* [comment removed for export] *)
#[using="Hoff"] Lemma node_mmap_alt_choose_at : forall ms model x8 (addr : word) (G : word -> Prop)
                                       (F : word -> Model) (E : word -> SyscallEffect),
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 222%Z ->
  (forall o, syscall_spec (sys_input segs ms x8) model o <->
             mmap_alt_choose G F E (sys_input segs ms x8) model o) ->
  (forall a, G a -> a = addr) -> G addr ->
  bv_eqb (eff_ret (E addr)) (errno_ret ENOMEM) = false ->
  (forall a, vm_only model (F a)) ->
  syscall_effect_accesses (E addr) = [] ->
  node_ok_cfg segs cfg (mkCfg ms model) unit (fun _ => [])
    (fun _ => mkCfg (advance_past_svc (apply_effect ms (E addr))) (F addr)).
Proof.
  intros ms model x8 addr G F E Hh Hsvc Hno Hbr HG Hga Hnr Hfr Hacc.
  apply (node_mmap_success segs cfg Hoff ms model x8 unit (fun _ => E addr) (fun _ => F addr)
           tt Hh Hsvc Hno).
  - intros []. apply Hbr. apply mmap_alt_choose_ok. split; [reflexivity|]. right. eauto.
  - intros []. exact Hnr.
  - intros eff m' evs Hs. apply Hbr, mmap_alt_choose_ok in Hs as (-> & [(-> & ->) | (a & Ha & -> & ->)]).
    + split; [reflexivity|]. left. unfold bv_eqb. apply Z.eqb_refl.
    + split; [reflexivity|]. right. exists tt. rewrite (HG a Ha). auto.
  - intro Hu. apply Hbr in Hu. exact (mmap_alt_choose_unmodeled _ _ _ _ _ Hu).
  - intros eff m' evs Hs. apply Hbr, mmap_alt_choose_ok in Hs as (-> & [(-> & ->) | (a & Ha & -> & ->)]).
    + apply vm_only_refl.
    + apply Hfr.
  - intros []. exact Hacc.
Qed.

(* [comment removed for export] *)
#[using="Hoff"] Lemma node_mmap_fixed_rw_free : forall ms model x8,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 222%Z ->
  (forall o, syscall_spec (sys_input segs ms x8) model o <->
     mmap_alt_choose
       (fun a => a = ms_gpr ms 0
                 /\ mmap_noreserve_backed_ok (ms_gpr ms 3) model (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true)
       (fun a => fresh_rw_next (ms_gpr ms 3) a (Z_to_bv 64 (page_round_up_Z (bv_unsigned (ms_gpr ms 1)))) model)
       (fun a => mkEffect a [] [(a, Z_to_bv 64 (page_round_up_Z (bv_unsigned (ms_gpr ms 1))))])
       (sys_input segs ms x8) model o) ->
  fixed_gate model (ms_gpr ms 0) (ms_gpr ms 1) ->
  mmap_noreserve_backed_ok (ms_gpr ms 3) model (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true ->
  node_ok_cfg segs cfg (mkCfg ms model) unit (fun _ => [])
    (fun _ => mkCfg (advance_past_svc (apply_effect ms
                       (mkEffect (ms_gpr ms 0) [] [(ms_gpr ms 0, Z_to_bv 64 (page_round_up_Z (bv_unsigned (ms_gpr ms 1))))])))
                    (fresh_rw_next (ms_gpr ms 3) (ms_gpr ms 0)
                       (Z_to_bv 64 (page_round_up_Z (bv_unsigned (ms_gpr ms 1)))) model)).
Proof.
  intros ms model x8 Hh Hsvc Hno Hbr Hg Hbud.
  pose proof (len_nZ_nonneg (ms_gpr ms 1)) as HnZ.
  apply (node_mmap_alt_choose_at ms model x8 (ms_gpr ms 0) _ _ _ Hh Hsvc Hno Hbr).
  - intros a [-> _]. reflexivity.
  - split; [reflexivity | exact Hbud].
  - cbn [eff_ret]. apply (below_top_not_errno (m_vmmaps model)); [exact ENOMEM_range|].
    destruct Hg as (Htop & _). lia.
  - intros a. apply vm_only_fresh_rw_next.
  - reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Hoff"] Lemma node_mmap_fixed_na_free : forall ms model x8,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 222%Z ->
  (forall o, syscall_spec (sys_input segs ms x8) model o <->
     mmap_alt_choose (fun a => a = ms_gpr ms 0)
       (fun a => fresh_na_next (ms_gpr ms 3) a (Z_to_bv 64 (page_round_up_Z (bv_unsigned (ms_gpr ms 1)))) model)
       (fun a => mkEffectU a [] [] [(a, Z_to_bv 64 (page_round_up_Z (bv_unsigned (ms_gpr ms 1))))] [] [])
       (sys_input segs ms x8) model o) ->
  fixed_gate model (ms_gpr ms 0) (ms_gpr ms 1) ->
  node_ok_cfg segs cfg (mkCfg ms model) unit (fun _ => [])
    (fun _ => mkCfg (advance_past_svc (apply_effect ms
                       (mkEffectU (ms_gpr ms 0) [] []
                          [(ms_gpr ms 0, Z_to_bv 64 (page_round_up_Z (bv_unsigned (ms_gpr ms 1))))] [] [])))
                    (fresh_na_next (ms_gpr ms 3) (ms_gpr ms 0)
                       (Z_to_bv 64 (page_round_up_Z (bv_unsigned (ms_gpr ms 1)))) model)).
Proof.
  intros ms model x8 Hh Hsvc Hno Hbr Hg.
  pose proof (len_nZ_nonneg (ms_gpr ms 1)) as HnZ.
  apply (node_mmap_alt_choose_at ms model x8 (ms_gpr ms 0) _ _ _ Hh Hsvc Hno Hbr).
  - intros a ->. reflexivity.
  - reflexivity.
  - cbn [eff_ret]. apply (below_top_not_errno (m_vmmaps model)); [exact ENOMEM_range|].
    destruct Hg as (Htop & _). lia.
  - intros a. apply vm_only_fresh_na_next.
  - reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Hoff"] Lemma node_mmap_noreplace_occupied : forall ms model x8,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 222%Z ->
  (forall o, syscall_spec (sys_input segs ms x8) model o <->
     alt (e <- errno_from mmap_errnos ;; err_ret e)%sys (err_ret EEXIST) (sys_input segs ms x8) model o) ->
  node_ok_cfg segs cfg (mkCfg ms model) unit (fun _ => [])
    (fun _ => mkCfg (advance_past_svc (apply_effect ms (mkEffect (errno_ret EEXIST) [] []))) model).
Proof.
  intros ms model x8 Hh Hsvc Hno Hbr.
  assert (Hch : forall eff m' evs, syscall_spec (sys_input segs ms x8) model (Ok eff m' evs) ->
            evs = [] /\ m' = model /\ (eff = mkEffect (errno_ret ENOMEM) [] [] \/ eff = mkEffect (errno_ret EEXIST) [] [])).
  { intros eff m' evs Hs. apply Hbr in Hs. destruct Hs as [Hs | Hs].
    - apply errno_arm_ok in Hs as (e & [<- | []] & -> & -> & ->). auto.
    - unfold err_ret, ret_only, pure in Hs. injection Hs as -> -> ->. auto. }
  apply (node_mmap_success segs cfg Hoff ms model x8 unit
           (fun _ => mkEffect (errno_ret EEXIST) [] []) (fun _ => model) tt Hh Hsvc Hno).
  - intros []. apply Hbr. right. reflexivity.
  - intros []. reflexivity.
  - intros eff m' evs Hs. destruct (Hch eff m' evs Hs) as (-> & -> & [-> | ->]).
    + split; [reflexivity|]. left. reflexivity.
    + split; [reflexivity|]. right. exists tt. auto.
  - intro Hu. apply Hbr in Hu. destruct Hu as [Hu | Hu];
      [exact (errno_arm_unmodeled _ _ _ Hu) | unfold err_ret, ret_only, pure in Hu; discriminate Hu].
  - intros eff m' evs Hs. destruct (Hch eff m' evs Hs) as (_ & -> & _). apply vm_only_refl.
  - intros []. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Hoff"] Lemma node_mmap_fixed_na_contained : forall ms model x8 (addr n : word) (flags : word),
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 222%Z ->
  (bv_unsigned addr <= alloc_top (m_vmmaps model))%Z ->
  (forall o, syscall_spec (sys_input segs ms x8) model o <->
     mmap_alt3 (modify (fun _ => fixed_na_next flags addr n model) ;;
                pure (mkEffectU addr [] [] [(addr, n)] [] []))%sys
               (fixed_destroyed addr n model) [(addr, n)] (sys_input segs ms x8) model o) ->
  node_ok_cfg segs cfg (mkCfg ms model) unit (fun _ => [])
    (fun _ => mkCfg (advance_past_svc (apply_effect ms (mkEffectU addr [] [] [(addr, n)] [] [])))
                    (fixed_na_next flags addr n model)).
Proof.
  intros ms model x8 addr n flags Hh Hsvc Hno Htop Hbr.
  apply (node_mmap_success segs cfg Hoff ms model x8 unit
           (fun _ => mkEffectU addr [] [] [(addr, n)] [] []) (fun _ => fixed_na_next flags addr n model)
           tt Hh Hsvc Hno).
  - intros []. apply Hbr, mmap_alt3_ok. right. left. apply modify_arm_ok. auto.
  - intros []. cbn [eff_ret]. exact (below_top_not_errno (m_vmmaps model) addr ENOMEM ENOMEM_range Htop).
  - intros eff m' evs Hs. apply Hbr, mmap_alt3_ok in Hs as [(-> & -> & ->) | [Hs | (-> & -> & ->)]].
    + split; [reflexivity|]. left. reflexivity.
    + apply modify_arm_ok in Hs as (-> & -> & ->). split; [reflexivity|]. right. exists tt. auto.
    + split; [reflexivity|]. left. reflexivity.
  - intro Hu. apply Hbr in Hu. apply (mmap_alt3_unmodeled _ _ _ _ _ (modify_arm_unmodeled _ _ _ _) Hu).
  - intros eff m' evs Hs. apply Hbr, mmap_alt3_ok in Hs as [(-> & -> & ->) | [Hs | (-> & -> & ->)]].
    + apply vm_only_refl.
    + apply modify_arm_ok in Hs as (-> & -> & ->). apply vm_only_fixed_na_next.
    + apply vm_only_fixed_destroyed.
  - intros []. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Hoff"] Lemma node_mmap_fixed_rw_contained : forall ms model x8 (addr n flags : word),
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 222%Z ->
  (bv_unsigned addr <= alloc_top (m_vmmaps model))%Z ->
  (forall o, syscall_spec (sys_input segs ms x8) model o <->
     mmap_alt3 (_ <- choose (fun _ : unit => mmap_fixed_rw_budget_ok flags model addr n = true) ;;
                modify (fun _ => fixed_rw_next flags addr n model) ;;
                pure (mkEffect addr [] [(addr, n)]))%sys
               (fixed_destroyed addr n model) [(addr, n)] (sys_input segs ms x8) model o) ->
  mmap_fixed_rw_budget_ok flags model addr n = true ->
  node_ok_cfg segs cfg (mkCfg ms model) unit (fun _ => [])
    (fun _ => mkCfg (advance_past_svc (apply_effect ms (mkEffect addr [] [(addr, n)])))
                    (fixed_rw_next flags addr n model)).
Proof.
  intros ms model x8 addr n flags Hh Hsvc Hno Htop Hbr Hbud.
  apply (node_mmap_success segs cfg Hoff ms model x8 unit
           (fun _ => mkEffect addr [] [(addr, n)]) (fun _ => fixed_rw_next flags addr n model)
           tt Hh Hsvc Hno).
  - intros []. apply Hbr, mmap_alt3_ok. right. left.
    apply (choose_arm_ok (fun _ : unit => mmap_fixed_rw_budget_ok flags model addr n = true)
             (fun _ => fixed_rw_next flags addr n model) (fun _ => mkEffect addr [] [(addr, n)])).
    exists tt. auto.
  - intros []. cbn [eff_ret]. exact (below_top_not_errno (m_vmmaps model) addr ENOMEM ENOMEM_range Htop).
  - intros eff m' evs Hs. apply Hbr, mmap_alt3_ok in Hs as [(-> & -> & ->) | [Hs | (-> & -> & ->)]].
    + split; [reflexivity|]. left. reflexivity.
    + apply (choose_arm_ok (fun _ : unit => mmap_fixed_rw_budget_ok flags model addr n = true)
               (fun _ => fixed_rw_next flags addr n model) (fun _ => mkEffect addr [] [(addr, n)])) in Hs
        as (u & _ & -> & -> & ->).
      split; [reflexivity|]. right. exists tt. auto.
    + split; [reflexivity|]. left. reflexivity.
  - intro Hu. apply Hbr in Hu. apply (mmap_alt3_unmodeled _ _ _ _ _ (choose_arm_unmodeled _ _ _ _ _) Hu).
  - intros eff m' evs Hs. apply Hbr, mmap_alt3_ok in Hs as [(-> & -> & ->) | [Hs | (-> & -> & ->)]].
    + apply vm_only_refl.
    + apply (choose_arm_ok (fun _ : unit => mmap_fixed_rw_budget_ok flags model addr n = true)
               (fun _ => fixed_rw_next flags addr n model) (fun _ => mkEffect addr [] [(addr, n)])) in Hs
        as (u & _ & -> & -> & ->).
      apply vm_only_fixed_rw_next.
    + apply vm_only_fixed_destroyed.
  - intros []. reflexivity.
Qed.

End MmapFixedNodes.

(* [comment removed for export] *)

Lemma syscall_spec_mprotect : forall segs ms x8 model o,
  bv_unsigned x8 = 226%Z ->
  (syscall_spec (sys_input segs ms x8) model o
   <-> mprotect_spec (ms_gpr ms 0) (ms_gpr ms 1) (ms_gpr ms 2) (sys_input segs ms x8) model o).
Proof.
  intros segs ms x8 model o Hno. unfold syscall_spec, dispatch.
  change (in_sysno (sys_input segs ms x8)) with x8. rewrite Hno. reflexivity.
Qed.

Lemma refusal_b_mprotect : forall segs ms x8 m r,
  bv_unsigned x8 = 226%Z ->
  refusal_b (sys_input segs ms x8) m r = bv_eqb r (errno_ret ENOMEM).
Proof.
  intros segs ms x8 m r Hno. unfold refusal_b.
  change (in_sysno (sys_input segs ms x8)) with x8. rewrite Hno. cbn.
  rewrite orb_false_r. reflexivity.
Qed.

Lemma mprotect_family_off : forall segs cfg ms x8,
  bv_unsigned x8 = 226%Z -> sc_alloc cfg = false ->
  injected_family_off cfg (sys_input segs ms x8) = true.
Proof.
  intros segs cfg ms x8 Hno Hoff. rewrite injected_family_off_sys_input, Hno.
  unfold injected_family_off_no. cbn. rewrite Hoff. reflexivity.
Qed.

Lemma vm_only_mprotect_model_next : forall m a n, vm_only m (mprotect_model_next m a n).
Proof. intros. unfold mprotect_model_next. apply vm_only_with_vmmaps. Qed.

(* [comment removed for export] *)
Lemma mprotect_spec_expose : forall addr len prot i m o,
  mprotect_grows_conflict_b prot = false ->
  Z.eqb (bv_unsigned addr mod page_size) 0 = true ->
  w_is0 len = false ->
  (two_pow_64 <=? bv_unsigned addr + page_round_up_Z (bv_unsigned len))%Z = false ->
  mprotect_modeled_b prot = true ->
  map_contains (vm_noaccess (m_vmmaps m)) addr (Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))
  && map_contains (vm_maps (m_vmmaps m)) addr (Z_to_bv 64 (page_round_up_Z (bv_unsigned len))) = true ->
  (mprotect_spec addr len prot i m o <->
   alt (e <- errno_from mprotect_errnos ;; err_ret e)%sys
     (_ <- choose (fun _ : unit =>
             mprotect_budget_ok m addr (Z_to_bv 64 (page_round_up_Z (bv_unsigned len))) = true) ;;
      modify (fun _ => mprotect_model_next m addr (Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))) ;;
      pure (mkEffect (Z_to_bv 64 0) [] [(addr, Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))]))%sys
     i m o).
Proof.
  intros addr len prot i m o Hgc Hal Hl Hov Hmod Hc.
  unfold mprotect_spec. rewrite Hgc, Hal, Hl, Hov, Hmod. cbn [negb].
  rewrite bind_get_model. rewrite Hc. reflexivity.
Qed.

Section MprotectNodes.
Variable segs : list Segment.
Variable cfg : SpuriousCfg.
Hypothesis Hoff : sc_alloc cfg = false.

Definition mprotect_expose_spec (m : Model) (addr n : word) : Sys SyscallEffect :=
  alt (e <- errno_from mprotect_errnos ;; err_ret e)%sys
     (_ <- choose (fun _ : unit => mprotect_budget_ok m addr n = true) ;;
      modify (fun _ => mprotect_model_next m addr n) ;;
      pure (mkEffect (Z_to_bv 64 0) [] [(addr, n)]))%sys.

#[using="Type"] Lemma mprotect_expose_ok : forall m addr n i eff m' evs,
  mprotect_expose_spec m addr n i m (Ok eff m' evs) <->
  evs = [] /\ ((eff = mkEffect (errno_ret ENOMEM) [] [] /\ m' = m)
               \/ (mprotect_budget_ok m addr n = true /\ eff = mkEffect (Z_to_bv 64 0) [] [(addr, n)]
                   /\ m' = mprotect_model_next m addr n)).
Proof.
  intros m addr n i eff m' evs. unfold mprotect_expose_spec, alt. split.
  - intros [Hs | Hs].
    + apply errno_arm_ok in Hs as (e & [<- | []] & -> & -> & ->). auto.
    + apply (choose_arm_ok (fun _ : unit => mprotect_budget_ok m addr n = true)
               (fun _ => mprotect_model_next m addr n) (fun _ => mkEffect (Z_to_bv 64 0) [] [(addr, n)])) in Hs
        as (u & Hb & -> & -> & ->). auto.
  - intros (-> & [(-> & ->) | (Hb & -> & ->)]).
    + left. apply errno_arm_ok. exists ENOMEM. split; [now left | auto].
    + right. apply (choose_arm_ok (fun _ : unit => mprotect_budget_ok m addr n = true)
               (fun _ => mprotect_model_next m addr n) (fun _ => mkEffect (Z_to_bv 64 0) [] [(addr, n)])).
      exists tt. auto.
Qed.

#[using="Type"] Lemma mprotect_expose_unmodeled : forall m addr n i, ~ mprotect_expose_spec m addr n i m Unmodeled.
Proof.
  intros m addr n i [Hu | Hu]; [exact (errno_arm_unmodeled _ _ _ Hu) | exact (choose_arm_unmodeled _ _ _ _ _ Hu)].
Qed.

(* [comment removed for export] *)
#[using="Hoff"] Lemma node_mprotect_expose : forall ms model x8 (addr n : word),
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 226%Z ->
  (forall o, syscall_spec (sys_input segs ms x8) model o <->
             mprotect_expose_spec model addr n (sys_input segs ms x8) model o) ->
  mprotect_budget_ok model addr n = true ->
  node_ok_cfg segs cfg (mkCfg ms model) unit (fun _ => [])
    (fun _ => mkCfg (advance_past_svc (apply_effect ms (mkEffect (Z_to_bv 64 0) [] [(addr, n)])))
                    (mprotect_model_next model addr n)).
Proof.
  intros ms model x8 addr n Hh Hsvc Hno Hbr Hbud.
  apply (node_forced_success segs cfg ms model x8 unit
           (fun _ => mkEffect (Z_to_bv 64 0) [] [(addr, n)]) (fun _ => mprotect_model_next model addr n)
           (fun _ => mprotect_model_next model addr n) (fun _ => []) tt
           (mprotect_family_off segs cfg ms x8 Hno Hoff) Hh Hsvc).
  - intros []. apply Hbr, mprotect_expose_ok. split; [reflexivity|]. right. auto.
  - intros []. rewrite refusal_b_mprotect by exact Hno. reflexivity.
  - intros eff m' evs Hs Hr. rewrite refusal_b_mprotect in Hr by exact Hno.
    apply Hbr, mprotect_expose_ok in Hs as (-> & [(-> & ->) | (_ & -> & ->)]).
    + cbn [eff_ret] in Hr. unfold bv_eqb in Hr. rewrite Z.eqb_refl in Hr. discriminate Hr.
    + exists tt. auto.
  - intro Hu. apply Hbr in Hu. exact (mprotect_expose_unmodeled _ _ _ _ Hu).
  - intros eff m' evs Hs. apply Hbr, mprotect_expose_ok in Hs as (-> & [(-> & ->) | (_ & -> & ->)]).
    + exact Hh.
    + rewrite (vm_only_halted _ _ (vm_only_mprotect_model_next model addr n)). exact Hh.
  - intros []. apply materialize_nil.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma node_mprotect_expose_forced : forall ms model x8 (addr n : word),
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 226%Z ->
  (forall o, syscall_spec (sys_input segs ms x8) model o <->
             mprotect_expose_spec model addr n (sys_input segs ms x8) model o) ->
  mprotect_budget_ok model addr n = false ->
  node_ok_cfg segs cfg (mkCfg ms model) unit (fun _ => [])
    (fun _ => mkCfg (advance_past_svc (apply_effect ms (mkEffect (errno_ret ENOMEM) [] []))) model).
Proof.
  intros ms model x8 addr n Hh Hsvc Hno Hbr Hbud.
  apply (node_forced_refusal segs cfg ms model x8 unit
           (fun _ => mkEffect (errno_ret ENOMEM) [] []) (fun _ => model) (fun _ => model)
           (fun _ => []) Hh Hsvc).
  - intros []. apply Hbr, mprotect_expose_ok. split; [reflexivity|]. left. auto.
  - intros eff m' evs Hs. rewrite refusal_b_mprotect by exact Hno.
    apply Hbr, mprotect_expose_ok in Hs as (-> & [(-> & ->) | (Hb & _ & _)]).
    + cbn [eff_ret]. unfold bv_eqb. apply Z.eqb_refl.
    + rewrite Hbud in Hb. discriminate Hb.
  - intros eff m' evs Hs. apply Hbr, mprotect_expose_ok in Hs as (-> & [(-> & ->) | (Hb & _ & _)]).
    + exists tt. auto.
    + rewrite Hbud in Hb. discriminate Hb.
  - intro Hu. apply Hbr in Hu. exact (mprotect_expose_unmodeled _ _ _ _ Hu).
  - intros eff m' evs Hs. apply Hbr, mprotect_expose_ok in Hs as (-> & [(-> & ->) | (Hb & _ & _)]).
    + exact Hh.
    + rewrite Hbud in Hb. discriminate Hb.
  - intros []. apply materialize_nil.
Qed.

End MprotectNodes.

(* [comment removed for export] *)

Lemma syscall_spec_munmap : forall segs ms x8 model o,
  bv_unsigned x8 = 215%Z ->
  (syscall_spec (sys_input segs ms x8) model o
   <-> munmap_spec (ms_gpr ms 0) (ms_gpr ms 1) (sys_input segs ms x8) model o).
Proof.
  intros segs ms x8 model o Hno. unfold syscall_spec, dispatch.
  change (in_sysno (sys_input segs ms x8)) with x8. rewrite Hno. reflexivity.
Qed.

(* [comment removed for export] *)
Definition munmap_next (addr n : word) (m : Model) : Model :=
  vm_forget_range (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n)
    (with_vmmaps (mkVmMapsFull (vm_reserved (m_vmmaps m)) (map_remove (vm_maps (m_vmmaps m)) addr)
                    (maps_subtract (vm_noaccess (m_vmmaps m))
                       (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n))
                    (vm_start_brk (m_vmmaps m)) (vm_brk (m_vmmaps m)) (vm_limit (m_vmmaps m))
                    (vm_mmap_base (m_vmmaps m)) (vm_init_sp (m_vmmaps m))) m).

Lemma vm_only_munmap_next : forall a n m, vm_only m (munmap_next a n m).
Proof.
  intros. unfold munmap_next.
  eapply vm_only_trans; [apply vm_only_with_vmmaps | apply vm_only_vm_forget_range].
Qed.

Lemma bind_get_vmmaps {A} (k : VmMaps -> Sys A) : forall i m o,
  bind get_vmmaps k i m o <-> k (m_vmmaps m) i m o.
Proof.
  intros i m o. unfold bind, get_vmmaps. destruct o as [x m2 evs|]; split.
  - intros (x0 & m1 & evs1 & evs2 & H1 & H2 & H3).
    injection H1 as -> -> ->. cbn in H3. subst evs. exact H2.
  - intros H. exists (m_vmmaps m), m, [], evs. split; [reflexivity|].
    split; [exact H | reflexivity].
  - intros [H | (x0 & m1 & evs1 & H1 & H2)]; [discriminate|].
    injection H1 as -> -> ->. exact H2.
  - intros H. right. exists (m_vmmaps m), m, []. split; [reflexivity | exact H].
Qed.

Lemma munmap_spec_exact_ok : forall addr len i m eff m' evs,
  Z.eqb (bv_unsigned addr mod page_size) 0 = true ->
  w_is0 len = false ->
  (TASK_SIZE <? bv_unsigned addr + page_round_up_Z (bv_unsigned len))%Z = false ->
  map_has (vm_maps (m_vmmaps m)) addr (Z_to_bv 64 (page_round_up_Z (bv_unsigned len))) = true ->
  (munmap_spec addr len i m (Ok eff m' evs) <->
   eff = mkEffectU (Z_to_bv 64 0) [] [] [(addr, Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))] [] []
   /\ m' = munmap_next addr (Z_to_bv 64 (page_round_up_Z (bv_unsigned len))) m /\ evs = []).
Proof.
  intros addr len i m eff m' evs Hal Hl Hts Hhas.
  unfold munmap_spec. rewrite Hal, Hl. cbn [negb orb].
  rewrite bind_get_vmmaps. rewrite Hts, Hhas.
  unfold set_vmmaps, forget_vm_range, bind, modify, pure. split.
  - intros H. sys_destruct. repeat split; reflexivity.
  - intros (-> & -> & ->).
    eexists tt, _, [], []. split; [reflexivity|]. split; [| reflexivity].
    eexists tt, _, [], []. split; [reflexivity|]. split; reflexivity.
Qed.

Lemma munmap_spec_exact_unmodeled : forall addr len i m,
  Z.eqb (bv_unsigned addr mod page_size) 0 = true ->
  w_is0 len = false ->
  (TASK_SIZE <? bv_unsigned addr + page_round_up_Z (bv_unsigned len))%Z = false ->
  map_has (vm_maps (m_vmmaps m)) addr (Z_to_bv 64 (page_round_up_Z (bv_unsigned len))) = true ->
  ~ munmap_spec addr len i m Unmodeled.
Proof.
  intros addr len i m Hal Hl Hts Hhas H.
  unfold munmap_spec in H. rewrite Hal, Hl in H. cbn [negb orb] in H.
  rewrite bind_get_vmmaps in H. rewrite Hts, Hhas in H.
  unfold set_vmmaps, forget_vm_range, bind, modify, pure in H. sys_destruct.
Qed.

(* [comment removed for export] *)
Lemma node_munmap_exact : forall segs cfg ms model x8,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 215%Z ->
  Z.eqb (bv_unsigned (ms_gpr ms 0) mod page_size) 0 = true ->
  w_is0 (ms_gpr ms 1) = false ->
  (TASK_SIZE <? bv_unsigned (ms_gpr ms 0) + page_round_up_Z (bv_unsigned (ms_gpr ms 1)))%Z = false ->
  map_has (vm_maps (m_vmmaps model)) (ms_gpr ms 0)
    (Z_to_bv 64 (page_round_up_Z (bv_unsigned (ms_gpr ms 1)))) = true ->
  node_ok_cfg segs cfg (mkCfg ms model) unit (fun _ => [])
    (fun _ => mkCfg (advance_past_svc (apply_effect ms
                       (mkEffectU (Z_to_bv 64 0) [] []
                          [(ms_gpr ms 0, Z_to_bv 64 (page_round_up_Z (bv_unsigned (ms_gpr ms 1))))] [] [])))
                    (munmap_next (ms_gpr ms 0) (Z_to_bv 64 (page_round_up_Z (bv_unsigned (ms_gpr ms 1)))) model)).
Proof.
  intros segs cfg ms model x8 Hh Hsvc Hno Hal Hl Hts Hhas.
  set (n := Z_to_bv 64 (page_round_up_Z (bv_unsigned (ms_gpr ms 1)))).
  apply (node_sys_cfg segs cfg ms model x8 unit
           (fun _ => mkEffectU (Z_to_bv 64 0) [] [] [(ms_gpr ms 0, n)] [] [])
           (fun _ => munmap_next (ms_gpr ms 0) n model) (fun _ => munmap_next (ms_gpr ms 0) n model)
           (fun _ => []) Hh Hsvc).
  - intros []. apply (proj2 (syscall_spec_munmap segs ms x8 model _ Hno)).
    apply munmap_spec_exact_ok; auto.
  - intros []. apply spurious_refusal_family_on.
    rewrite injected_family_off_sys_input, Hno. reflexivity.
  - intros eff m' evs Hs _. apply (proj1 (syscall_spec_munmap segs ms x8 model _ Hno)) in Hs.
    apply munmap_spec_exact_ok in Hs as (-> & -> & ->); auto. exists tt. auto.
  - intro Hu. apply (proj1 (syscall_spec_munmap segs ms x8 model _ Hno)) in Hu.
    exact (munmap_spec_exact_unmodeled _ _ _ _ Hal Hl Hts Hhas Hu).
  - intros eff m' evs Hs. apply (proj1 (syscall_spec_munmap segs ms x8 model _ Hno)) in Hs.
    apply munmap_spec_exact_ok in Hs as (-> & -> & ->);
      [rewrite (vm_only_halted _ _ (vm_only_munmap_next _ _ _)); exact Hh | exact Hal | exact Hl
      | exact Hts | exact Hhas].
  - intros []. apply materialize_nil.
Qed.

(* [comment removed for export] *)
Lemma mmap_spec_len0_ok : forall addr len prot flags fd off i m eff m' evs,
  mmap_off_aligned_b off = true -> mmap_anon_b flags = true -> w_is0 len = true ->
  mmap_plain_anon_b flags = true ->
  (mmap_spec addr len prot flags fd off i m (Ok eff m' evs) <->
   eff = mkEffect (errno_ret EINVAL) [] [] /\ m' = m /\ evs = []).
Proof.
  intros addr len prot flags fd off i m eff m' evs Ho Ha Hl Hp.
  unfold mmap_spec. rewrite Ho, Ha, Hl, Hp. cbn [negb].
  unfold err_ret, ret_only, pure. split; [intros H; injection H as -> -> ->; auto|].
  intros (-> & -> & ->). reflexivity.
Qed.

Lemma node_mmap_len0 : forall segs cfg ms model x8,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 222%Z ->
  mmap_off_aligned_b (ms_gpr ms 5) = true ->
  mmap_anon_b (ms_gpr ms 3) = true ->
  w_is0 (ms_gpr ms 1) = true ->
  mmap_plain_anon_b (ms_gpr ms 3) = true ->
  node_ok_cfg segs cfg (mkCfg ms model) unit (fun _ => [])
    (fun _ => mkCfg (advance_past_svc (apply_effect ms (mkEffect (errno_ret EINVAL) [] []))) model).
Proof.
  intros segs cfg ms model x8 Hh Hsvc Hno Ho Ha Hl Hp.
  apply (node_sys_cfg segs cfg ms model x8 unit (fun _ => mkEffect (errno_ret EINVAL) [] [])
           (fun _ => model) (fun _ => model) (fun _ => []) Hh Hsvc).
  - intros []. apply (proj2 (syscall_spec_mmap segs ms x8 model _ Hno)).
    apply mmap_spec_len0_ok; auto.
  - intros []. apply spurious_refusal_not_refusal. rewrite refusal_b_mmap by exact Hno. reflexivity.
  - intros eff m' evs Hs _. apply (proj1 (syscall_spec_mmap segs ms x8 model _ Hno)) in Hs.
    apply mmap_spec_len0_ok in Hs as (-> & -> & ->); auto. exists tt. auto.
  - intro Hu. apply (proj1 (syscall_spec_mmap segs ms x8 model _ Hno)) in Hu.
    unfold mmap_spec in Hu. rewrite Ho, Ha, Hl, Hp in Hu. cbn [negb] in Hu.
    unfold err_ret, ret_only, pure in Hu. discriminate Hu.
  - intros eff m' evs Hs. apply (proj1 (syscall_spec_mmap segs ms x8 model _ Hno)) in Hs.
    apply mmap_spec_len0_ok in Hs as (-> & -> & ->); auto.
  - intros []. apply materialize_nil.
Qed.

(* [comment removed for export] *)
Lemma mmap_spec_fixed_overflow_ok : forall addr len prot flags fd off i m eff m' evs,
  mmap_off_aligned_b off = true -> mmap_anon_b flags = true -> w_is0 len = false ->
  mmap_modeled_b prot flags off = false -> mmap_noaccess_b prot flags off = false ->
  (mmap_fixed_noaccess_b prot flags off = true
   \/ (mmap_fixed_noaccess_b prot flags off = false /\ mmap_fixed_rw_b prot flags off = true)
   \/ (mmap_fixed_noaccess_b prot flags off = false /\ mmap_fixed_rw_b prot flags off = false
       /\ mmap_noreplace_noaccess_b prot flags off = true)
   \/ (mmap_fixed_noaccess_b prot flags off = false /\ mmap_fixed_rw_b prot flags off = false
       /\ mmap_noreplace_noaccess_b prot flags off = false /\ mmap_noreplace_rw_b prot flags off = true)) ->
  (two_pow_64 <= bv_unsigned addr + page_round_up_Z (bv_unsigned len))%Z ->
  (mmap_spec addr len prot flags fd off i m (Ok eff m' evs) <->
   eff = mkEffect (errno_ret ENOMEM) [] [] /\ m' = m /\ evs = []).
Proof.
  intros addr len prot flags fd off i m eff m' evs Ho Ha Hl Hm Hn Hsel Hov.
  apply Z.leb_le in Hov.
  unfold mmap_spec. rewrite Ho, Ha, Hl, Hm, Hn. cbn [negb].
  destruct Hsel as [H1 | [(H1 & H2) | [(H1 & H2 & H3) | (H1 & H2 & H3 & H4)]]];
    rewrite ?H1, ?H2, ?H3, ?H4; rewrite Hov;
    unfold err_ret, ret_only, pure; (split; [intros H; injection H as -> -> ->; auto |
                                           intros (-> & -> & ->); reflexivity]).
Qed.

(* [comment removed for export] *)

Section Wrappers.
Variable segs : list Segment.
Variable cfg : SpuriousCfg.
Hypothesis Hoff : sc_alloc cfg = false.

#[using="Hoff"] Lemma rzc_brk_grow : forall ms model x8 req T,
  m_halted model = None -> ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 214%Z ->
  ms_gpr ms 0 = req -> w_is0 req = false ->
  (bv_unsigned (min_brk (m_vmmaps model)) <= bv_unsigned req)%Z ->
  (bv_unsigned (vm_brk (m_vmmaps model)) < bv_unsigned req)%Z ->
  brk_grow_ok model req req = true ->
  realizes_cfg segs cfg
    (mkCfg (advance_past_svc (apply_effect ms (brk_eff req req (vm_brk (m_vmmaps model)))))
           (with_brk_next model req req)) T ->
  realizes_cfg segs cfg (mkCfg ms model) T.
Proof.
  intros. eapply rzc_silent1; [eapply (node_brk_grow segs cfg Hoff); eassumption | assumption].
Qed.

#[using="Type"] Lemma rzc_brk_grow_forced_fail : forall ms model x8 req T,
  m_halted model = None -> ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 214%Z ->
  ms_gpr ms 0 = req -> w_is0 req = false ->
  (bv_unsigned (min_brk (m_vmmaps model)) <= bv_unsigned req)%Z ->
  (bv_unsigned (vm_brk (m_vmmaps model)) < bv_unsigned req)%Z ->
  brk_grow_ok model req req = false ->
  realizes_cfg segs cfg
    (mkCfg (advance_past_svc (apply_effect ms (mkEffect (vm_brk (m_vmmaps model)) [] []))) model) T ->
  realizes_cfg segs cfg (mkCfg ms model) T.
Proof.
  intros. eapply rzc_silent1; [eapply (node_brk_grow_forced_fail segs cfg); eassumption | assumption].
Qed.

#[using="Hoff"] Lemma rzc_brk_shrink : forall ms model x8 req T,
  m_halted model = None -> ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 214%Z ->
  ms_gpr ms 0 = req -> w_is0 req = false ->
  (bv_unsigned (min_brk (m_vmmaps model)) <= bv_unsigned req)%Z ->
  (bv_unsigned req < bv_unsigned (vm_brk (m_vmmaps model)))%Z ->
  realizes_cfg segs cfg
    (mkCfg (advance_past_svc (apply_effect ms (brk_eff req req (vm_brk (m_vmmaps model)))))
           (with_brk_next model req req)) T ->
  realizes_cfg segs cfg (mkCfg ms model) T.
Proof.
  intros. eapply rzc_silent1; [eapply (node_brk_shrink segs cfg Hoff); eassumption | assumption].
Qed.

#[using="Type"] Lemma rzc_brk_query : forall ms model x8 req T,
  m_halted model = None -> ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 214%Z ->
  ms_gpr ms 0 = req ->
  (w_is0 req = true \/ (bv_unsigned req < bv_unsigned (min_brk (m_vmmaps model)))%Z
   \/ req = vm_brk (m_vmmaps model)) ->
  realizes_cfg segs cfg
    (mkCfg (advance_past_svc (apply_effect ms (mkEffect (vm_brk (m_vmmaps model)) [] []))) model) T ->
  realizes_cfg segs cfg (mkCfg ms model) T.
Proof.
  intros. eapply rzc_silent1; [eapply (node_brk_query segs cfg); eassumption | assumption].
Qed.

(* [comment removed for export] *)
#[using="Hoff"] Lemma rzc_mmap_fresh_rw : forall ms model x8 T,
  m_halted model = None -> ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 222%Z ->
  mmap_off_aligned_b (ms_gpr ms 5) = true -> mmap_anon_b (ms_gpr ms 3) = true ->
  w_is0 (ms_gpr ms 1) = false ->
  mmap_modeled_b (ms_gpr ms 2) (ms_gpr ms 3) (ms_gpr ms 5) = true ->
  (exists a, fresh_rw_guard (ms_gpr ms 3) model (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) a) ->
  (forall a, fresh_rw_guard (ms_gpr ms 3) model (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) a ->
     realizes_cfg segs cfg
       (mkCfg (advance_past_svc (apply_effect ms
                 (mkEffect a [] [(a, Z_to_bv 64 (page_round_up_Z (bv_unsigned (ms_gpr ms 1))))])))
              (fresh_rw_next (ms_gpr ms 3) a (Z_to_bv 64 (page_round_up_Z (bv_unsigned (ms_gpr ms 1)))) model))
       T) ->
  realizes_cfg segs cfg (mkCfg ms model) T.
Proof.
  intros ms model x8 T Hh Hsvc Hno Ho Ha Hl Hm Hex Hc.
  destruct Hex as [a0 Ha0].
  eapply (rzc_silent_const segs cfg _ _ _ T (exist _ a0 Ha0)).
  - apply (node_mmap_fresh_rw segs cfg Hoff ms model x8 Hh Hsvc Hno Ho Ha Hl Hm). exists a0. exact Ha0.
  - intros [a Hga]. apply Hc. exact Hga.
Qed.

(* [comment removed for export] *)
#[using="Hoff"] Lemma rzc_mmap_fresh_na : forall ms model x8 T,
  m_halted model = None -> ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 222%Z ->
  mmap_off_aligned_b (ms_gpr ms 5) = true -> mmap_anon_b (ms_gpr ms 3) = true ->
  w_is0 (ms_gpr ms 1) = false ->
  mmap_modeled_b (ms_gpr ms 2) (ms_gpr ms 3) (ms_gpr ms 5) = false ->
  mmap_noaccess_b (ms_gpr ms 2) (ms_gpr ms 3) (ms_gpr ms 5) = true ->
  (exists a, place_ok model (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) a) ->
  (forall a, place_ok model (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) a ->
     realizes_cfg segs cfg
       (mkCfg (advance_past_svc (apply_effect ms
                 (mkEffectU a [] [] [(a, Z_to_bv 64 (page_round_up_Z (bv_unsigned (ms_gpr ms 1))))] [] [])))
              (fresh_na_next (ms_gpr ms 3) a (Z_to_bv 64 (page_round_up_Z (bv_unsigned (ms_gpr ms 1)))) model))
       T) ->
  realizes_cfg segs cfg (mkCfg ms model) T.
Proof.
  intros ms model x8 T Hh Hsvc Hno Ho Ha Hl Hm Hn Hex Hc.
  destruct Hex as [a0 Ha0].
  eapply (rzc_silent_const segs cfg _ _ _ T (exist _ a0 Ha0)).
  - apply (node_mmap_fresh_na segs cfg Hoff ms model x8 Hh Hsvc Hno Ho Ha Hl Hm Hn). exists a0. exact Ha0.
  - intros [a Hga]. apply Hc. exact Hga.
Qed.

#[using="Type"] Lemma rzc_munmap_exact : forall ms model x8 T,
  m_halted model = None -> ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 215%Z ->
  Z.eqb (bv_unsigned (ms_gpr ms 0) mod page_size) 0 = true ->
  w_is0 (ms_gpr ms 1) = false ->
  (TASK_SIZE <? bv_unsigned (ms_gpr ms 0) + page_round_up_Z (bv_unsigned (ms_gpr ms 1)))%Z = false ->
  map_has (vm_maps (m_vmmaps model)) (ms_gpr ms 0)
    (Z_to_bv 64 (page_round_up_Z (bv_unsigned (ms_gpr ms 1)))) = true ->
  realizes_cfg segs cfg
    (mkCfg (advance_past_svc (apply_effect ms
              (mkEffectU (Z_to_bv 64 0) [] []
                 [(ms_gpr ms 0, Z_to_bv 64 (page_round_up_Z (bv_unsigned (ms_gpr ms 1))))] [] [])))
           (munmap_next (ms_gpr ms 0) (Z_to_bv 64 (page_round_up_Z (bv_unsigned (ms_gpr ms 1)))) model)) T ->
  realizes_cfg segs cfg (mkCfg ms model) T.
Proof.
  intros. eapply rzc_silent1; [eapply (node_munmap_exact segs cfg); eassumption | assumption].
Qed.

#[using="Hoff"] Lemma rzc_mprotect_expose : forall ms model x8 (addr n : word) T,
  m_halted model = None -> ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 226%Z ->
  (forall o, syscall_spec (sys_input segs ms x8) model o <->
             mprotect_expose_spec model addr n (sys_input segs ms x8) model o) ->
  mprotect_budget_ok model addr n = true ->
  realizes_cfg segs cfg
    (mkCfg (advance_past_svc (apply_effect ms (mkEffect (Z_to_bv 64 0) [] [(addr, n)])))
           (mprotect_model_next model addr n)) T ->
  realizes_cfg segs cfg (mkCfg ms model) T.
Proof.
  intros. eapply rzc_silent1; [eapply (node_mprotect_expose segs cfg Hoff); eassumption | assumption].
Qed.

End Wrappers.

(* [comment removed for export] *)

Section SysBranches.
Variable segs : list Segment.

#[using="Type"] Lemma branch_fixed_na_contained : forall ms x8 model,
  bv_unsigned x8 = 222%Z ->
  mmap_off_aligned_b (ms_gpr ms 5) = true -> mmap_anon_b (ms_gpr ms 3) = true ->
  w_is0 (ms_gpr ms 1) = false ->
  mmap_modeled_b (ms_gpr ms 2) (ms_gpr ms 3) (ms_gpr ms 5) = false ->
  mmap_noaccess_b (ms_gpr ms 2) (ms_gpr ms 3) (ms_gpr ms 5) = false ->
  mmap_fixed_noaccess_b (ms_gpr ms 2) (ms_gpr ms 3) (ms_gpr ms 5) = true ->
  fixed_gate model (ms_gpr ms 0) (ms_gpr ms 1) ->
  region_free (vm_reserved (m_vmmaps model)) (ms_gpr ms 0) (Z_to_bv 64 (page_round_up_Z (bv_unsigned (ms_gpr ms 1))))
  && map_contains (vm_maps (m_vmmaps model)) (ms_gpr ms 0)
       (Z_to_bv 64 (page_round_up_Z (bv_unsigned (ms_gpr ms 1)))) = true ->
  forall o, syscall_spec (sys_input segs ms x8) model o <->
    mmap_alt3
      (modify (fun _ => fixed_na_next (ms_gpr ms 3) (ms_gpr ms 0)
                          (Z_to_bv 64 (page_round_up_Z (bv_unsigned (ms_gpr ms 1)))) model) ;;
       pure (mkEffectU (ms_gpr ms 0) [] []
               [(ms_gpr ms 0, Z_to_bv 64 (page_round_up_Z (bv_unsigned (ms_gpr ms 1))))] [] []))%sys
      (fixed_destroyed (ms_gpr ms 0) (Z_to_bv 64 (page_round_up_Z (bv_unsigned (ms_gpr ms 1)))) model)
      [(ms_gpr ms 0, Z_to_bv 64 (page_round_up_Z (bv_unsigned (ms_gpr ms 1))))]
      (sys_input segs ms x8) model o.
Proof.
  intros ms x8 model Hno Ho Ha Hl Hm Hn Hf Hg Hc o.
  rewrite (syscall_spec_mmap segs ms x8 model o Hno).
  exact (mmap_spec_fixed_na_contained _ _ _ _ _ _ _ _ _ Ho Ha Hl Hm Hn Hf Hg Hc).
Qed.

#[using="Type"] Lemma branch_fixed_rw_contained : forall ms x8 model,
  bv_unsigned x8 = 222%Z ->
  mmap_off_aligned_b (ms_gpr ms 5) = true -> mmap_anon_b (ms_gpr ms 3) = true ->
  w_is0 (ms_gpr ms 1) = false ->
  mmap_modeled_b (ms_gpr ms 2) (ms_gpr ms 3) (ms_gpr ms 5) = false ->
  mmap_noaccess_b (ms_gpr ms 2) (ms_gpr ms 3) (ms_gpr ms 5) = false ->
  mmap_fixed_noaccess_b (ms_gpr ms 2) (ms_gpr ms 3) (ms_gpr ms 5) = false ->
  mmap_fixed_rw_b (ms_gpr ms 2) (ms_gpr ms 3) (ms_gpr ms 5) = true ->
  fixed_gate model (ms_gpr ms 0) (ms_gpr ms 1) ->
  region_free (vm_reserved (m_vmmaps model)) (ms_gpr ms 0) (Z_to_bv 64 (page_round_up_Z (bv_unsigned (ms_gpr ms 1))))
  && map_contains (vm_maps (m_vmmaps model)) (ms_gpr ms 0)
       (Z_to_bv 64 (page_round_up_Z (bv_unsigned (ms_gpr ms 1)))) = true ->
  forall o, syscall_spec (sys_input segs ms x8) model o <->
    mmap_alt3
      (_ <- choose (fun _ : unit =>
              mmap_fixed_rw_budget_ok (ms_gpr ms 3) model (ms_gpr ms 0)
                (Z_to_bv 64 (page_round_up_Z (bv_unsigned (ms_gpr ms 1)))) = true) ;;
       modify (fun _ => fixed_rw_next (ms_gpr ms 3) (ms_gpr ms 0)
                          (Z_to_bv 64 (page_round_up_Z (bv_unsigned (ms_gpr ms 1)))) model) ;;
       pure (mkEffect (ms_gpr ms 0) [] [(ms_gpr ms 0, Z_to_bv 64 (page_round_up_Z (bv_unsigned (ms_gpr ms 1))))]))%sys
      (fixed_destroyed (ms_gpr ms 0) (Z_to_bv 64 (page_round_up_Z (bv_unsigned (ms_gpr ms 1)))) model)
      [(ms_gpr ms 0, Z_to_bv 64 (page_round_up_Z (bv_unsigned (ms_gpr ms 1))))]
      (sys_input segs ms x8) model o.
Proof.
  intros ms x8 model Hno Ho Ha Hl Hm Hn Hf Hfrw Hg Hc o.
  rewrite (syscall_spec_mmap segs ms x8 model o Hno).
  exact (mmap_spec_fixed_rw_contained _ _ _ _ _ _ _ _ _ Ho Ha Hl Hm Hn Hf Hfrw Hg Hc).
Qed.

#[using="Type"] Lemma branch_fixed_na_free : forall ms x8 model,
  bv_unsigned x8 = 222%Z ->
  mmap_off_aligned_b (ms_gpr ms 5) = true -> mmap_anon_b (ms_gpr ms 3) = true ->
  w_is0 (ms_gpr ms 1) = false ->
  mmap_modeled_b (ms_gpr ms 2) (ms_gpr ms 3) (ms_gpr ms 5) = false ->
  mmap_noaccess_b (ms_gpr ms 2) (ms_gpr ms 3) (ms_gpr ms 5) = false ->
  mmap_fixed_noaccess_b (ms_gpr ms 2) (ms_gpr ms 3) (ms_gpr ms 5) = true ->
  fixed_gate model (ms_gpr ms 0) (ms_gpr ms 1) ->
  region_free (vm_reserved (m_vmmaps model)) (ms_gpr ms 0) (Z_to_bv 64 (page_round_up_Z (bv_unsigned (ms_gpr ms 1))))
  && map_contains (vm_maps (m_vmmaps model)) (ms_gpr ms 0)
       (Z_to_bv 64 (page_round_up_Z (bv_unsigned (ms_gpr ms 1)))) = false ->
  region_free (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model)) (ms_gpr ms 0)
    (Z_to_bv 64 (page_round_up_Z (bv_unsigned (ms_gpr ms 1)))) = true ->
  forall o, syscall_spec (sys_input segs ms x8) model o <->
     mmap_alt_choose (fun a => a = ms_gpr ms 0)
       (fun a => fresh_na_next (ms_gpr ms 3) a (Z_to_bv 64 (page_round_up_Z (bv_unsigned (ms_gpr ms 1)))) model)
       (fun a => mkEffectU a [] [] [(a, Z_to_bv 64 (page_round_up_Z (bv_unsigned (ms_gpr ms 1))))] [] [])
       (sys_input segs ms x8) model o.
Proof.
  intros ms x8 model Hno Ho Ha Hl Hm Hn Hf Hg Hc Hfr o.
  rewrite (syscall_spec_mmap segs ms x8 model o Hno).
  exact (mmap_spec_fixed_na_free _ _ _ _ _ _ _ _ _ Ho Ha Hl Hm Hn Hf Hg Hc Hfr).
Qed.

#[using="Type"] Lemma branch_fixed_rw_free : forall ms x8 model,
  bv_unsigned x8 = 222%Z ->
  mmap_off_aligned_b (ms_gpr ms 5) = true -> mmap_anon_b (ms_gpr ms 3) = true ->
  w_is0 (ms_gpr ms 1) = false ->
  mmap_modeled_b (ms_gpr ms 2) (ms_gpr ms 3) (ms_gpr ms 5) = false ->
  mmap_noaccess_b (ms_gpr ms 2) (ms_gpr ms 3) (ms_gpr ms 5) = false ->
  mmap_fixed_noaccess_b (ms_gpr ms 2) (ms_gpr ms 3) (ms_gpr ms 5) = false ->
  mmap_fixed_rw_b (ms_gpr ms 2) (ms_gpr ms 3) (ms_gpr ms 5) = true ->
  fixed_gate model (ms_gpr ms 0) (ms_gpr ms 1) ->
  region_free (vm_reserved (m_vmmaps model)) (ms_gpr ms 0) (Z_to_bv 64 (page_round_up_Z (bv_unsigned (ms_gpr ms 1))))
  && map_contains (vm_maps (m_vmmaps model)) (ms_gpr ms 0)
       (Z_to_bv 64 (page_round_up_Z (bv_unsigned (ms_gpr ms 1)))) = false ->
  region_free (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model)) (ms_gpr ms 0)
    (Z_to_bv 64 (page_round_up_Z (bv_unsigned (ms_gpr ms 1)))) = true ->
  forall o, syscall_spec (sys_input segs ms x8) model o <->
     mmap_alt_choose
       (fun a => a = ms_gpr ms 0
                 /\ mmap_noreserve_backed_ok (ms_gpr ms 3) model (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true)
       (fun a => fresh_rw_next (ms_gpr ms 3) a (Z_to_bv 64 (page_round_up_Z (bv_unsigned (ms_gpr ms 1)))) model)
       (fun a => mkEffect a [] [(a, Z_to_bv 64 (page_round_up_Z (bv_unsigned (ms_gpr ms 1))))])
       (sys_input segs ms x8) model o.
Proof.
  intros ms x8 model Hno Ho Ha Hl Hm Hn Hf Hfrw Hg Hc Hfr o.
  rewrite (syscall_spec_mmap segs ms x8 model o Hno).
  exact (mmap_spec_fixed_rw_free _ _ _ _ _ _ _ _ _ Ho Ha Hl Hm Hn Hf Hfrw Hg Hc Hfr).
Qed.

#[using="Type"] Lemma branch_noreplace_na_free : forall ms x8 model,
  bv_unsigned x8 = 222%Z ->
  mmap_off_aligned_b (ms_gpr ms 5) = true -> mmap_anon_b (ms_gpr ms 3) = true ->
  w_is0 (ms_gpr ms 1) = false ->
  mmap_modeled_b (ms_gpr ms 2) (ms_gpr ms 3) (ms_gpr ms 5) = false ->
  mmap_noaccess_b (ms_gpr ms 2) (ms_gpr ms 3) (ms_gpr ms 5) = false ->
  mmap_fixed_noaccess_b (ms_gpr ms 2) (ms_gpr ms 3) (ms_gpr ms 5) = false ->
  mmap_fixed_rw_b (ms_gpr ms 2) (ms_gpr ms 3) (ms_gpr ms 5) = false ->
  mmap_noreplace_noaccess_b (ms_gpr ms 2) (ms_gpr ms 3) (ms_gpr ms 5) = true ->
  fixed_gate model (ms_gpr ms 0) (ms_gpr ms 1) ->
  region_free (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model)) (ms_gpr ms 0)
    (Z_to_bv 64 (page_round_up_Z (bv_unsigned (ms_gpr ms 1)))) = true ->
  forall o, syscall_spec (sys_input segs ms x8) model o <->
     mmap_alt_choose (fun a => a = ms_gpr ms 0)
       (fun a => fresh_na_next (ms_gpr ms 3) a (Z_to_bv 64 (page_round_up_Z (bv_unsigned (ms_gpr ms 1)))) model)
       (fun a => mkEffectU a [] [] [(a, Z_to_bv 64 (page_round_up_Z (bv_unsigned (ms_gpr ms 1))))] [] [])
       (sys_input segs ms x8) model o.
Proof.
  intros ms x8 model Hno Ho Ha Hl Hm Hn Hf Hfrw Hnr Hg Hfr o.
  rewrite (syscall_spec_mmap segs ms x8 model o Hno).
  exact (mmap_spec_noreplace_na_free _ _ _ _ _ _ _ _ _ Ho Ha Hl Hm Hn Hf Hfrw Hnr Hg Hfr).
Qed.

#[using="Type"] Lemma branch_noreplace_rw_free : forall ms x8 model,
  bv_unsigned x8 = 222%Z ->
  mmap_off_aligned_b (ms_gpr ms 5) = true -> mmap_anon_b (ms_gpr ms 3) = true ->
  w_is0 (ms_gpr ms 1) = false ->
  mmap_modeled_b (ms_gpr ms 2) (ms_gpr ms 3) (ms_gpr ms 5) = false ->
  mmap_noaccess_b (ms_gpr ms 2) (ms_gpr ms 3) (ms_gpr ms 5) = false ->
  mmap_fixed_noaccess_b (ms_gpr ms 2) (ms_gpr ms 3) (ms_gpr ms 5) = false ->
  mmap_fixed_rw_b (ms_gpr ms 2) (ms_gpr ms 3) (ms_gpr ms 5) = false ->
  mmap_noreplace_noaccess_b (ms_gpr ms 2) (ms_gpr ms 3) (ms_gpr ms 5) = false ->
  mmap_noreplace_rw_b (ms_gpr ms 2) (ms_gpr ms 3) (ms_gpr ms 5) = true ->
  fixed_gate model (ms_gpr ms 0) (ms_gpr ms 1) ->
  region_free (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model)) (ms_gpr ms 0)
    (Z_to_bv 64 (page_round_up_Z (bv_unsigned (ms_gpr ms 1)))) = true ->
  forall o, syscall_spec (sys_input segs ms x8) model o <->
     mmap_alt_choose
       (fun a => a = ms_gpr ms 0
                 /\ mmap_noreserve_backed_ok (ms_gpr ms 3) model (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true)
       (fun a => fresh_rw_next (ms_gpr ms 3) a (Z_to_bv 64 (page_round_up_Z (bv_unsigned (ms_gpr ms 1)))) model)
       (fun a => mkEffect a [] [(a, Z_to_bv 64 (page_round_up_Z (bv_unsigned (ms_gpr ms 1))))])
       (sys_input segs ms x8) model o.
Proof.
  intros ms x8 model Hno Ho Ha Hl Hm Hn Hf Hfrw Hnr Hnrw Hg Hfr o.
  rewrite (syscall_spec_mmap segs ms x8 model o Hno).
  exact (mmap_spec_noreplace_rw_free _ _ _ _ _ _ _ _ _ Ho Ha Hl Hm Hn Hf Hfrw Hnr Hnrw Hg Hfr).
Qed.

#[using="Type"] Lemma branch_noreplace_occupied : forall ms x8 model,
  bv_unsigned x8 = 222%Z ->
  mmap_off_aligned_b (ms_gpr ms 5) = true -> mmap_anon_b (ms_gpr ms 3) = true ->
  w_is0 (ms_gpr ms 1) = false ->
  mmap_modeled_b (ms_gpr ms 2) (ms_gpr ms 3) (ms_gpr ms 5) = false ->
  mmap_noaccess_b (ms_gpr ms 2) (ms_gpr ms 3) (ms_gpr ms 5) = false ->
  mmap_fixed_noaccess_b (ms_gpr ms 2) (ms_gpr ms 3) (ms_gpr ms 5) = false ->
  mmap_fixed_rw_b (ms_gpr ms 2) (ms_gpr ms 3) (ms_gpr ms 5) = false ->
  (mmap_noreplace_noaccess_b (ms_gpr ms 2) (ms_gpr ms 3) (ms_gpr ms 5) = true \/
   (mmap_noreplace_noaccess_b (ms_gpr ms 2) (ms_gpr ms 3) (ms_gpr ms 5) = false
    /\ mmap_noreplace_rw_b (ms_gpr ms 2) (ms_gpr ms 3) (ms_gpr ms 5) = true)) ->
  fixed_gate model (ms_gpr ms 0) (ms_gpr ms 1) ->
  region_free (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model)) (ms_gpr ms 0)
    (Z_to_bv 64 (page_round_up_Z (bv_unsigned (ms_gpr ms 1)))) = false ->
  forall o, syscall_spec (sys_input segs ms x8) model o <->
     alt (e <- errno_from mmap_errnos ;; err_ret e)%sys (err_ret EEXIST) (sys_input segs ms x8) model o.
Proof.
  intros ms x8 model Hno Ho Ha Hl Hm Hn Hf Hfrw Hsel Hg Hfr o.
  rewrite (syscall_spec_mmap segs ms x8 model o Hno).
  exact (mmap_spec_noreplace_occupied _ _ _ _ _ _ _ _ _ Ho Ha Hl Hm Hn Hf Hfrw Hsel Hg Hfr).
Qed.

#[using="Type"] Lemma branch_mprotect_expose : forall ms x8 model,
  bv_unsigned x8 = 226%Z ->
  mprotect_grows_conflict_b (ms_gpr ms 2) = false ->
  Z.eqb (bv_unsigned (ms_gpr ms 0) mod page_size) 0 = true ->
  w_is0 (ms_gpr ms 1) = false ->
  (two_pow_64 <=? bv_unsigned (ms_gpr ms 0) + page_round_up_Z (bv_unsigned (ms_gpr ms 1)))%Z = false ->
  mprotect_modeled_b (ms_gpr ms 2) = true ->
  map_contains (vm_noaccess (m_vmmaps model)) (ms_gpr ms 0)
    (Z_to_bv 64 (page_round_up_Z (bv_unsigned (ms_gpr ms 1))))
  && map_contains (vm_maps (m_vmmaps model)) (ms_gpr ms 0)
       (Z_to_bv 64 (page_round_up_Z (bv_unsigned (ms_gpr ms 1)))) = true ->
  forall o, syscall_spec (sys_input segs ms x8) model o <->
    mprotect_expose_spec model (ms_gpr ms 0) (Z_to_bv 64 (page_round_up_Z (bv_unsigned (ms_gpr ms 1))))
      (sys_input segs ms x8) model o.
Proof.
  intros ms x8 model Hno Hgc Hal Hl Hov Hmod Hc o.
  rewrite (syscall_spec_mprotect segs ms x8 model o Hno).
  exact (mprotect_spec_expose _ _ _ _ _ _ Hgc Hal Hl Hov Hmod Hc).
Qed.

End SysBranches.
