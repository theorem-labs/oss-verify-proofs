(* AS/NodesFO = our text + 's own edits to theories/Common/NodesFO.v, 3-way merged (proposal md5 ); the old text is kept aside *)
(** * AS.NodesFO — lazy-syscall node lemmas over the filtered step at memory forced-only

    The ASan node libraries of submissions 14, 16 and 21 ([AS.AsanNodesLibE], [AS.AsanNodesMmLib])
    build each syscall node from a characterisation of [check_syscall]: every checked outcome is one
    of the node's successors and conversely.  Under the filtered step [Run.sstep_cfg alloc_forced_cfg]
    the successors are the checked outcomes that are not spurious refusals, so the converse only has
    to cover those ([node_chk_fo]); an exit step is never filtered, so every checked outcome must
    leave the process running.  For an allocation arm whose successors are its grants, a refusal is
    spurious as soon as one grant exists ([node_chk_fo_w]): the converse then only has to cover the
    non-refusal answers, which is how the release spec's always-offered errnos drop out. *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs RiscvSemantics MemImageType State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Mprotect.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_agrees_alloc_forced_only.FO Require Import FOCore FOStep.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_agrees_alloc_forced_only.AS Require Import ShapeAlg SpinAlg DivergeSim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

(* alloc_sysnos now holds 215 (munmap; CHANGE-LIST row 1), so membership is found, not counted *)
Lemma in_alloc_brk : In 214%Z alloc_sysnos.
Proof. unfold alloc_sysnos. simpl. auto 10. Qed.
Lemma in_alloc_mremap : In 216%Z alloc_sysnos.
Proof. unfold alloc_sysnos. simpl. auto 10. Qed.
Lemma in_alloc_mmap : In 222%Z alloc_sysnos.
Proof. unfold alloc_sysnos. simpl. auto 10. Qed.
Lemma in_alloc_mprotect : In 226%Z alloc_sysnos.
Proof. unfold alloc_sysnos. simpl. auto 10. Qed.

(** An allocation syscall's family is off at [alloc_forced_cfg]. *)
Lemma family_off_sysno : forall segs ms x8,
  In (bv_unsigned x8) alloc_sysnos -> injected_family_off alloc_forced_cfg (sys_input segs ms x8) = true.
Proof.
  intros segs ms x8 H. unfold injected_family_off. rewrite in_sysno_sys_input_fo.
  unfold alloc_sysnos in H. simpl in H.
  destruct H as [H|[H|[H|[H|[H|[]]]]]]; rewrite <- H; reflexivity.
Qed.

(** A refusal of a family that is off is spurious as soon as the spec admits one non-refusal answer. *)
Lemma spurious_of_witness : forall i m eff eff0 m0 evs0,
  injected_family_off alloc_forced_cfg i = true ->
  refusal_b i m (eff_ret eff) = true ->
  syscall_spec i m (Ok eff0 m0 evs0) -> refusal_b i m (eff_ret eff0) = false ->
  spurious_refusal_cfg alloc_forced_cfg i m eff.
Proof.
  intros i m eff eff0 m0 evs0 Hoff Hr Hs Hn.
  split; [exact Hoff | split; [exact Hr | exists eff0, m0, evs0; split; assumption]].
Qed.

Section NodesFO.
Variable segs : list Segment.

Lemma sstep_of_check_fo : forall ms model x8 eff m' evs,
  ~ spurious_refusal_cfg alloc_forced_cfg (sys_input segs ms x8) model eff ->
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  check_syscall (sys_input segs ms x8) eff model = CheckOk m' evs ->
  m_halted m' = None ->
  syscall_effect_accesses eff = [] ->
  sstep_cfg segs alloc_forced_cfg (mkCfg ms model) evs (SNext (mkCfg (advance_past_svc (apply_effect ms eff)) m')).
Proof.
  intros ms model x8 eff m' evs Hns Hh Hsvc Hc Hh' Hacc.
  apply (sstep_cfg_syscall_ns segs alloc_forced_cfg ms model x8 eff m' m' evs Hns Hh Hsvc).
  - apply check_syscall_ok_iff. exact Hc.
  - exact Hh'.
  - rewrite Hacc. apply materialize_model_accesses_nil.
Qed.

Lemma node_chk_fo : forall ms model x8 (I : Type)
    (effs : I -> SyscallEffect) (ms' : I -> Model) (evs : I -> list event),
  m_halted model = None -> ms_svc_pending ms = Some x8 ->
  (forall i, check_syscall (sys_input segs ms x8) (effs i) model = CheckOk (ms' i) (evs i)) ->
  (forall i, ~ spurious_refusal_cfg alloc_forced_cfg (sys_input segs ms x8) model (effs i)) ->
  (forall eff m' ev, check_syscall (sys_input segs ms x8) eff model = CheckOk m' ev ->
     ~ spurious_refusal_cfg alloc_forced_cfg (sys_input segs ms x8) model eff ->
     exists i, eff = effs i /\ m' = ms' i /\ ev = evs i) ->
  (forall eff, check_syscall (sys_input segs ms x8) eff model <> CheckUnmodeled) ->
  (forall eff m' ev, check_syscall (sys_input segs ms x8) eff model = CheckOk m' ev -> m_halted m' = None) ->
  (forall i, syscall_effect_accesses (effs i) = []) ->
  ShapeAlg.node_ok segs (mkCfg ms model) I evs
    (fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms' i)).
Proof.
  intros ms model x8 I effs ms' evs Hh Hsvc Hok Hns Hinv Hnu Hhalt Hacc. split.
  - intros i. exact (sstep_of_check_fo ms model x8 (effs i) (ms' i) (evs i) (Hns i) Hh Hsvc (Hok i)
                       (Hhalt _ _ _ (Hok i)) (Hacc i)).
  - intros e st Hss.
    inversion Hss; subst; try congruence;
      match goal with H : ms_svc_pending ms = Some ?y |- _ => rewrite Hsvc in H; inversion H; subst end.
    + match goal with
      | Hs : syscall_spec _ _ (Ok ?eff ?m1 ?ev), Hn : ~ spurious_refusal_cfg _ _ _ ?eff,
        Hm : materialize_model_accesses ?m1 _ = Some _ |- _ =>
          apply check_syscall_ok_iff in Hs; destruct (Hinv _ _ _ Hs Hn) as (i & -> & -> & ->);
          rewrite (Hacc i), materialize_model_accesses_nil in Hm; injection Hm as <-;
          exists i; split; reflexivity
      end.
    + match goal with
      | Hs : syscall_spec _ _ (Ok ?eff ?m1 ?ev), Hn : ~ spurious_refusal_cfg _ _ _ ?eff,
        Hm : materialize_model_accesses ?m1 _ = None |- _ =>
          apply check_syscall_ok_iff in Hs; destruct (Hinv _ _ _ Hs Hn) as (i & -> & -> & ->);
          rewrite (Hacc i), materialize_model_accesses_nil in Hm; discriminate Hm
      end.
    + match goal with
      | Hs : syscall_spec _ _ (Ok ?eff ?m1 ?ev), Hc : m_halted ?m1 = Some _ |- _ =>
          apply check_syscall_ok_iff in Hs; rewrite (Hhalt _ _ _ Hs) in Hc; discriminate Hc
      end.
    + match goal with
      | Hs : syscall_spec _ _ (Ok ?eff ?m1 ?ev), Hk : m_killed ?m1 = Some _ |- _ =>
          apply check_syscall_ok_iff in Hs;
          rewrite (m_killed_of_m_halted_none _ (Hhalt _ _ _ Hs)) in Hk; discriminate Hk
      end.
    + exfalso. apply (Hnu (mkEffect (Z_to_bv 64 0) [] [])). apply check_syscall_err_iff. assumption.
Qed.

(** An allocation arm whose successors are its grants (non-refusals), with at least one grant. *)
Lemma node_chk_fo_w : forall ms model x8 (I : Type)
    (effs : I -> SyscallEffect) (ms' : I -> Model) (evs : I -> list event) (i0 : I),
  m_halted model = None -> ms_svc_pending ms = Some x8 ->
  injected_family_off alloc_forced_cfg (sys_input segs ms x8) = true ->
  (forall i, check_syscall (sys_input segs ms x8) (effs i) model = CheckOk (ms' i) (evs i)) ->
  (forall i, refusal_b (sys_input segs ms x8) model (eff_ret (effs i)) = false) ->
  (forall eff m' ev, check_syscall (sys_input segs ms x8) eff model = CheckOk m' ev ->
     refusal_b (sys_input segs ms x8) model (eff_ret eff) = false ->
     exists i, eff = effs i /\ m' = ms' i /\ ev = evs i) ->
  (forall eff, check_syscall (sys_input segs ms x8) eff model <> CheckUnmodeled) ->
  (forall eff m' ev, check_syscall (sys_input segs ms x8) eff model = CheckOk m' ev -> m_halted m' = None) ->
  (forall i, syscall_effect_accesses (effs i) = []) ->
  ShapeAlg.node_ok segs (mkCfg ms model) I evs
    (fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms' i)).
Proof.
  intros ms model x8 I effs ms' evs i0 Hh Hsvc Hoff Hok Hnr Hinv Hnu Hhalt Hacc.
  apply (node_chk_fo ms model x8 I effs ms' evs Hh Hsvc Hok).
  - intros i. apply spurious_refusal_not_refusal. exact (Hnr i).
  - intros eff m' ev Hc Hn.
    destruct (refusal_b (sys_input segs ms x8) model (eff_ret eff)) eqn:Er; [| exact (Hinv eff m' ev Hc Er)].
    exfalso. apply Hn. apply (spurious_of_witness _ _ _ (effs i0) (ms' i0) (evs i0) Hoff Er).
    + apply check_syscall_ok_iff. exact (Hok i0).
    + exact (Hnr i0).
  - exact Hnu.
  - exact Hhalt.
  - exact Hacc.
Qed.

Lemma node_det_fo : forall ms model x8 eff0 m0 evs0,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  check_syscall (sys_input segs ms x8) eff0 model = CheckOk m0 evs0 ->
  ~ spurious_refusal_cfg alloc_forced_cfg (sys_input segs ms x8) model eff0 ->
  (forall eff m' evs, check_syscall (sys_input segs ms x8) eff model = CheckOk m' evs ->
     ~ spurious_refusal_cfg alloc_forced_cfg (sys_input segs ms x8) model eff ->
     eff = eff0 /\ m' = m0 /\ evs = evs0) ->
  (forall eff, check_syscall (sys_input segs ms x8) eff model <> CheckUnmodeled) ->
  (forall eff m' evs, check_syscall (sys_input segs ms x8) eff model = CheckOk m' evs -> m_halted m' = None) ->
  syscall_effect_accesses eff0 = [] ->
  ShapeAlg.node_ok segs (mkCfg ms model) unit (fun _ => evs0)
    (fun _ => mkCfg (advance_past_svc (apply_effect ms eff0)) m0).
Proof.
  intros ms model x8 eff0 m0 evs0 Hh Hsvc Hok Hns Hinv Hnu Hhalt Hacc.
  apply (node_chk_fo ms model x8 unit (fun _ => eff0) (fun _ => m0) (fun _ => evs0) Hh Hsvc).
  - intros []. exact Hok.
  - intros []. exact Hns.
  - intros eff m' ev Hc Hn. destruct (Hinv eff m' ev Hc Hn) as (-> & -> & ->). exists tt. auto.
  - exact Hnu.
  - exact Hhalt.
  - intros []. exact Hacc.
Qed.

Lemma srz_det_fo : forall ms model x8 eff0 m0 T,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  check_syscall (sys_input segs ms x8) eff0 model = CheckOk m0 [] ->
  ~ spurious_refusal_cfg alloc_forced_cfg (sys_input segs ms x8) model eff0 ->
  (forall eff m' evs, check_syscall (sys_input segs ms x8) eff model = CheckOk m' evs ->
     ~ spurious_refusal_cfg alloc_forced_cfg (sys_input segs ms x8) model eff ->
     eff = eff0 /\ m' = m0 /\ evs = []) ->
  (forall eff, check_syscall (sys_input segs ms x8) eff model <> CheckUnmodeled) ->
  (forall eff m' evs, check_syscall (sys_input segs ms x8) eff model = CheckOk m' evs -> m_halted m' = None) ->
  syscall_effect_accesses eff0 = [] ->
  srealizes segs (mkCfg (advance_past_svc (apply_effect ms eff0)) m0) T ->
  srealizes segs (mkCfg ms model) T.
Proof.
  intros ms model x8 eff0 m0 T Hh Hsvc Hok Hns Hinv Hnu Hhalt Hacc Hc.
  eapply srz_silent1; [exact (node_det_fo ms model x8 eff0 m0 [] Hh Hsvc Hok Hns Hinv Hnu Hhalt Hacc) | exact Hc].
Qed.

(** The refusals of the allocation arms at a pending syscall. *)
Lemma refusal_b_mmap_fo : forall ms model x8 r,
  bv_unsigned x8 = 222%Z -> refusal_b (sys_input segs ms x8) model r = errno_ret_in mmap_errnos r.
Proof. intros ms model x8 r Hno. unfold refusal_b. rewrite in_sysno_sys_input_fo, Hno. reflexivity. Qed.

Lemma refusal_b_mprotect_fo : forall ms model x8 r,
  bv_unsigned x8 = 226%Z -> refusal_b (sys_input segs ms x8) model r = errno_ret_in mprotect_errnos r.
Proof. intros ms model x8 r Hno. unfold refusal_b. rewrite in_sysno_sys_input_fo, Hno. reflexivity. Qed.

Lemma refusal_b_brk_fo : forall ms model x8 r,
  bv_unsigned x8 = 214%Z -> refusal_b (sys_input segs ms x8) model r = brk_refusal_b model (ms_gpr ms 0) r.
Proof. intros ms model x8 r Hno. unfold refusal_b. rewrite in_sysno_sys_input_fo, Hno. reflexivity. Qed.

Lemma family_off_fo : forall ms x8 (n : Z),
  bv_unsigned x8 = n -> In n alloc_sysnos -> injected_family_off alloc_forced_cfg (sys_input segs ms x8) = true.
Proof. intros ms x8 n Hno Hin. apply family_off_sysno. rewrite Hno. exact Hin. Qed.

End NodesFO.

Lemma bv_eqb_neq_fo : forall {n} (a b : bv n), a <> b -> bv_eqb a b = false.
Proof. intros n a b H. destruct (bv_eqb a b) eqn:E; [apply bv_eqb_eq in E; contradiction | reflexivity]. Qed.

Lemma bv_eqb_refl_fo : forall {n} (a : bv n), bv_eqb a a = true.
Proof. intros n a. apply bv_eqb_eq. reflexivity. Qed.

(** brk: keeping the old break on a request to move it is a refusal; any other answer is not. *)
Lemma brk_keep_refusal_fo : forall model req,
  req <> Z_to_bv 64 0 ->
  (bv_unsigned (vm_start_brk (m_vmmaps model)) <= bv_unsigned req)%Z ->
  req <> vm_brk (m_vmmaps model) ->
  brk_refusal_b model req (vm_brk (m_vmmaps model)) = true.
Proof.
  intros model req H0 Hs Hne. unfold brk_refusal_b. cbv zeta.
  assert (Ew : w_is0 req = false) by (unfold w_is0; apply bv_eqb_neq_fo; exact H0).
  rewrite Ew, (bv_eqb_neq_fo _ _ Hne), bv_eqb_refl_fo.
  match goal with |- context [Z.ltb (bv_unsigned req) ?x] =>
    replace (Z.ltb (bv_unsigned req) x) with false by (symmetry; apply Z.ltb_ge; exact Hs) end.
  reflexivity.
Qed.

Lemma brk_ne_refusal_fo : forall model req r,
  r <> vm_brk (m_vmmaps model) -> brk_refusal_b model req r = false.
Proof.
  intros model req r Hne. unfold brk_refusal_b. cbv zeta. rewrite (bv_eqb_neq_fo _ _ Hne). apply andb_false_r.
Qed.
