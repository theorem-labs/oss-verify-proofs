(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.openssl.ct.lib.VCommon Require Import
  PropExec SimInv ExitSim CatSim CatExec SeqExec StreamExec FileSim ShapeAlg ShapeAlgCfg AgentLib AgentNodes.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope bv_scope.


Section WithCfg.
Context {fx : PropExec.FPState}.
Variable segs : list Segment.
Variable cfg : SpuriousCfg.

(* [comment removed for export] *)
Definition cfg_nonalloc_on : Prop :=
  sc_fs cfg = true /\ sc_fd cfg = true /\ sc_net cfg = true /\ sc_cred cfg = true /\ sc_intr cfg = true.

Lemma cfg_nonalloc_on_lit : forall b, cfg = mkSpuriousCfg b true true true true true -> cfg_nonalloc_on.
Proof. intros b H. unfold cfg_nonalloc_on. rewrite H. cbn. repeat split; reflexivity. Qed.

Lemma nospur_nonalloc : forall ms x8 model eff,
  cfg_nonalloc_on ->
  ~ In (bv_unsigned x8) alloc_mark_sysnos ->
  ~ spurious_refusal_cfg cfg (sys_input segs ms x8) model eff.
Proof.
  intros ms x8 model eff (H1 & H2 & H3 & H4 & H5) Hnin.
  apply spurious_refusal_family_on. apply injected_family_off_nonalloc; try assumption.
Qed.

Lemma not_alloc_sysno : forall (x8 : word) (z : Z),
  bv_unsigned x8 = z -> negb (existsb (Z.eqb z) alloc_mark_sysnos) = true ->
  ~ In (bv_unsigned x8) alloc_mark_sysnos.
Proof.
  intros x8 z Hz Hb Hin. rewrite Hz in Hin. apply negb_true_iff in Hb.
  assert (existsb (Z.eqb z) alloc_mark_sysnos = true) by (apply existsb_exists; exists z; split; [exact Hin | apply Z.eqb_refl]).
  congruence.
Qed.

(* [comment removed for export] *)

Lemma node_chk_cfg : forall ms model x8 (chk : SyscallEffect -> check_result) (I : Type)
    (E : I -> SyscallEffect) (M : I -> Model) (EV : I -> list event),
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  (forall eff, check_syscall (sys_input segs ms x8) eff model = chk eff) ->
  (forall i, chk (E i) = CheckOk (M i) (EV i)) ->
  (forall i, ~ spurious_refusal_cfg cfg (sys_input segs ms x8) model (E i)) ->
  (forall eff m' evs, chk eff = CheckOk m' evs ->
     ~ spurious_refusal_cfg cfg (sys_input segs ms x8) model eff ->
     exists i, eff = E i /\ m' = M i /\ evs = EV i) ->
  (forall eff m' evs, chk eff = CheckOk m' evs -> m_halted m' = None) ->
  (forall eff, chk eff <> CheckUnmodeled) ->
  (forall i, m_vm_lazy (M i) = []) ->
  node_ok_cfg segs cfg (mkCfg ms model) I EV
          (fun i => mkCfg (advance_past_svc (apply_effect ms (E i))) (M i)).
Proof.
  intros ms model x8 chk I E M EV Hh Hsvc Hchk Hok Hns Hinv Hnh Hnu Hnl.
  apply (node_sys_cfg segs cfg ms model x8 I E M EV Hh Hsvc).
  - intro i. apply check_syscall_ok_iff. rewrite Hchk. apply Hok.
  - exact Hns.
  - intros eff m' evs Hs Hn. apply check_syscall_ok_iff in Hs. rewrite Hchk in Hs.
    exact (Hinv _ _ _ Hs Hn).
  - intro Hs.
    pose proof (proj2 (check_syscall_err_iff (sys_input segs ms x8)
                         (mkEffect (Z_to_bv 64 0) [] []) model) Hs) as Hs'.
    rewrite Hchk in Hs'. exact (Hnu _ Hs').
  - intros eff m' evs Hs. apply check_syscall_ok_iff in Hs. rewrite Hchk in Hs.
    exact (Hnh _ _ _ Hs).
  - exact Hnl.
Qed.

(* [comment removed for export] *)
Lemma rzc_chk : forall ms model x8 (chk : SyscallEffect -> check_result) (I : Type)
    (E : I -> SyscallEffect) (M : I -> Model) (EV : I -> list event) (T : I -> TSet) (i0 : I),
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  (forall eff, check_syscall (sys_input segs ms x8) eff model = chk eff) ->
  (forall i, chk (E i) = CheckOk (M i) (EV i)) ->
  (forall i, ~ spurious_refusal_cfg cfg (sys_input segs ms x8) model (E i)) ->
  (forall eff m' evs, chk eff = CheckOk m' evs ->
     ~ spurious_refusal_cfg cfg (sys_input segs ms x8) model eff ->
     exists i, eff = E i /\ m' = M i /\ evs = EV i) ->
  (forall eff m' evs, chk eff = CheckOk m' evs -> m_halted m' = None) ->
  (forall eff, chk eff <> CheckUnmodeled) ->
  (forall i, m_vm_lazy (M i) = []) ->
  (forall i, realizes_cfg segs cfg (mkCfg (advance_past_svc (apply_effect ms (E i))) (M i)) (T i)) ->
  realizes_cfg segs cfg (mkCfg ms model) (t_alt (fun i => t_emit (EV i) (T i))).
Proof.
  intros ms model x8 chk I E M EV T i0 Hh Hsvc Hchk Hok Hns Hinv Hnh Hnu Hnl Hcont.
  apply (rzc_node segs cfg (mkCfg ms model) I EV
           (fun i => mkCfg (advance_past_svc (apply_effect ms (E i))) (M i)) T i0).
  - eapply node_chk_cfg; eassumption.
  - exact Hcont.
Qed.

(* [comment removed for export] *)
Lemma rzc_ret_chk : forall ms model x8 r m' evs T,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  (forall eff, check_syscall (sys_input segs ms x8) eff model = check_ret_only eff r m' evs) ->
  (~ spurious_refusal_cfg cfg (sys_input segs ms x8) model (mkEffect r [] [])) ->
  m_halted m' = None ->
  m_vm_lazy m' = [] ->
  realizes_cfg segs cfg (mkCfg (advance_past_svc (apply_effect ms (mkEffect r [] []))) m') T ->
  realizes_cfg segs cfg (mkCfg ms model) (t_emit evs T).
Proof.
  intros ms model x8 r m' evs T Hh Hsvc Hchk Hns Hh' Hnl' Hcont.
  eapply rzc_conseq.
  - apply (rzc_chk ms model x8 (fun eff => check_ret_only eff r m' evs) unit
             (fun _ => mkEffect r [] []) (fun _ => m') (fun _ => evs) (fun _ => T) tt
             Hh Hsvc Hchk).
    + intros []. apply check_ret_only_ok_iff. auto.
    + intros []. exact Hns.
    + intros eff m2 evs2 Hc _. apply check_ret_only_ok_iff in Hc.
      destruct Hc as (-> & -> & ->). exists tt. auto.
    + intros eff m2 evs2 Hc. apply check_ret_only_ok_iff in Hc. destruct Hc as (_ & -> & _). exact Hh'.
    + intros eff. apply check_ret_only_no_unmodeled.
    + intros []. exact Hnl'.
    + intros []. exact Hcont.
  - apply t_alt_unit.
Qed.

(* [comment removed for export] *)

Lemma rzc_sys : forall regs pc mem rom model w T,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  fetch_word segs pc = Some w -> is_ecall w = true ->
  realizes_cfg segs cfg (mkCfg (epend regs pc mem rom (getr regs 17)) model) T ->
  realizes_cfg segs cfg (mkCfg (mkst regs pc mem rom) model) T.
Proof.
  intros regs pc mem rom model w T Hh Hlazy HF HE Hc.
  eapply rzc_step; [exact Hh | exact Hlazy | reflexivity | eapply step_ecall_epend; eassumption | exact Hc].
Qed.

(* [comment removed for export] *)

Lemma rzc_exit : forall ms model x8,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  is_exit_no x8 ->
  realizes_cfg segs cfg (mkCfg ms model)
           (t_exit (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) (m_fs model)).
Proof.
  intros ms model x8 Hh Hsvc Hx8.
  set (code := bv_and (ms_gpr ms 0) (Z_to_bv 64 255)).
  unfold t_exit.
  eapply (rzc_emit1 segs cfg (mkCfg ms model) (mkCfg ms (with_halted code model))).
  - split.
    + intros []. cbn.
      replace [ExitEv code (m_fs model)]
        with ([] ++ [ExitEv code (m_fs (with_halted code model))]) by reflexivity.
      apply (sstep_cfg_exit segs cfg ms model x8 (mkEffect (Z_to_bv 64 0) [] [])
               (with_halted code model) [] code);
        [exact Hh | exact Hsvc
         | apply (exit_dispatch_ok (sys_input segs ms x8) model);
           rewrite in_sysno_sys_input; exact Hx8
         | reflexivity
         | apply m_killed_with_halted ].
    + intros e st Hss.
      destruct (sstep_exit_inv segs ms model x8 e st Hh Hsvc Hx8 (sstep_cfg_sub segs cfg _ _ _ Hss)) as [-> ->].
      exists tt. split; reflexivity.
  - apply rzc_halt. cbn. discriminate.
Qed.

Lemma rzc_exit_at : forall regs (pc : word) mem rom model w code,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  (getr regs 17 = Z_to_bv 64 94 \/ getr regs 17 = Z_to_bv 64 93) ->
  getr regs 10 = code ->
  realizes_cfg segs cfg (mkCfg (mkst regs pc mem rom) model)
           (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model)).
Proof.
  intros regs pc mem rom model w code HF HE Hh Hlazy H17 H10.
  eapply rzc_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
  rewrite <- H10, <- (ms_gpr_epend0 regs pc mem rom (getr regs 17)).
  eapply rzc_exit; [exact Hh | reflexivity |].
  destruct H17 as [H|H]; [right|left]; rewrite H; reflexivity.
Qed.

Lemma rzc_exit_at_lit : forall regs (pc : word) mem rom model w (code : Z),
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  (getr regs 17 = Z_to_bv 64 94 \/ getr regs 17 = Z_to_bv 64 93) ->
  getr regs 10 = Z_to_bv 64 code -> (0 <= code < 256)%Z ->
  realizes_cfg segs cfg (mkCfg (mkst regs pc mem rom) model) (t_exit (Z_to_bv 64 code) (m_fs model)).
Proof.
  intros regs pc mem rom model w code HF HE Hh Hlazy H17 H10 Hc.
  rewrite <- (bv_and_255_small code Hc). eapply rzc_exit_at; eassumption.
Qed.

End WithCfg.
