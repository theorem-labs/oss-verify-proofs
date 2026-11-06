(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uapi.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.openssl.bignum.lib.VCommon Require Import ShapeAlg ShapeAlgCfg.
From OSSVerify.Proofs.openssl.bignum.lib.VCommon.Ax Require Import AsanWLazy AsanWAcc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Local Open Scope Z_scope.

Section Node.
Variable segs : list Segment.
Variable cfg : SpuriousCfg.

Notation INP ms x8 := (sys_input segs ms x8).

Definition sys_ix (ms : machine_state) (model : Model) (x8 : word) : Type :=
  { x : SyscallEffect * Model * list event * Model |
    syscall_spec (INP ms x8) model (Ok (fst (fst (fst x))) (snd (fst (fst x))) (snd (fst x)))
    /\ ~ spurious_refusal_cfg cfg (INP ms x8) model (fst (fst (fst x)))
    /\ materialize_model_accesses (snd (fst (fst x))) (syscall_effect_accesses (fst (fst (fst x)))) = Some (snd x) }.

Definition ix_eff {ms model x8} (i : sys_ix ms model x8) : SyscallEffect := fst (fst (fst (proj1_sig i))).
Definition ix_evs {ms model x8} (i : sys_ix ms model x8) : list event := snd (fst (proj1_sig i)).
Definition ix_mod {ms model x8} (i : sys_ix ms model x8) : Model := snd (proj1_sig i).

Lemma node_all (ms : machine_state) (model : Model) (x8 : word) :
  m_halted model = None -> ms_svc_pending ms = Some x8 ->
  ~ syscall_spec (INP ms x8) model Unmodeled ->
  (forall eff m' evs, syscall_spec (INP ms x8) model (Ok eff m' evs) -> m_halted m' = None) ->
  (forall eff m' evs, syscall_spec (INP ms x8) model (Ok eff m' evs) -> ~ spurious_refusal_cfg cfg (INP ms x8) model eff ->
     materialize_model_accesses m' (syscall_effect_accesses eff) <> None) ->
  node_ok_cfg segs cfg (mkCfg ms model) (sys_ix ms model x8) ix_evs
    (fun i => mkCfg (advance_past_svc (apply_effect ms (ix_eff i))) (ix_mod i)).
Proof.
  intros Hh Hsvc Hnu Hnh Hmat. split.
  - intros [[[[eff m'] evs] m''] (Hs & Hns & Hm)]. unfold ix_evs, ix_eff, ix_mod. cbn [proj1_sig fst snd] in *.
    exact (sstep_cfg_syscall segs cfg ms model x8 eff m' m'' evs Hh Hsvc Hs Hns (Hnh _ _ _ Hs) Hm).
  - intros e st Hss. inversion Hss; subst;
      try (match goal with H1 : ms_svc_pending ms = None |- _ => rewrite Hsvc in H1; discriminate H1 end);
      match goal with H1 : ms_svc_pending ms = Some ?y |- _ =>
        rewrite Hsvc in H1; injection H1; intro; subst y end.
    + match goal with
      | Hs : syscall_spec _ _ (Ok ?eff ?m1 ?e1), Hn : ~ spurious_refusal_cfg _ _ _ ?eff,
        Hm : materialize_model_accesses ?m1 _ = Some ?m2 |- _ =>
          exists (exist _ (eff, m1, e1, m2) (conj Hs (conj Hn Hm))); split; reflexivity
      end.
    + exfalso. match goal with
      | Hs : syscall_spec _ _ (Ok ?eff ?m1 ?e1), Hn : ~ spurious_refusal_cfg _ _ _ ?eff,
        Hm : materialize_model_accesses ?m1 _ = None |- _ => exact (Hmat _ _ _ Hs Hn Hm)
      end.
    + exfalso. match goal with
      | Hs : syscall_spec _ _ (Ok ?eff ?m1 ?e1), Hc : m_halted ?m1 = Some _ |- _ =>
          rewrite (Hnh _ _ _ Hs) in Hc; discriminate Hc
      end.
    + exfalso. match goal with
      | Hs : syscall_spec _ _ (Ok ?eff ?m1 ?e1), Hk : m_killed ?m1 = Some _ |- _ =>
          rewrite (m_killed_of_m_halted_none _ (Hnh _ _ _ Hs)) in Hk; discriminate Hk
      end.
    + exfalso. apply Hnu. assumption.
Qed.

Theorem rzc_all_silent (ms : machine_state) (model : Model) (x8 : word) (T : TSet) :
  m_halted model = None -> ms_svc_pending ms = Some x8 ->
  ~ syscall_spec (INP ms x8) model Unmodeled ->
  (forall eff m' evs, syscall_spec (INP ms x8) model (Ok eff m' evs) -> evs = [] /\ m_halted m' = None) ->
  (exists eff m' evs, syscall_spec (INP ms x8) model (Ok eff m' evs) /\ ~ spurious_refusal_cfg cfg (INP ms x8) model eff) ->
  (forall eff m', syscall_spec (INP ms x8) model (Ok eff m' []) -> ~ spurious_refusal_cfg cfg (INP ms x8) model eff ->
     exists m'', materialize_model_accesses m' (syscall_effect_accesses eff) = Some m''
                 /\ realizes_cfg segs cfg (mkCfg (advance_past_svc (apply_effect ms eff)) m'') T) ->
  realizes_cfg segs cfg (mkCfg ms model) T.
Proof.
  intros Hh Hsvc Hnu Hsil [eff0 [m0 [evs0 [Hs0 Hns0]]]] Hcont.
  assert (Hnh : forall eff m' evs, syscall_spec (INP ms x8) model (Ok eff m' evs) -> m_halted m' = None)
    by (intros eff m' evs Hs; exact (proj2 (Hsil _ _ _ Hs))).
  assert (Hmat : forall eff m' evs, syscall_spec (INP ms x8) model (Ok eff m' evs) -> ~ spurious_refusal_cfg cfg (INP ms x8) model eff ->
            materialize_model_accesses m' (syscall_effect_accesses eff) <> None).
  { intros eff m' evs Hs Hns. pose proof (proj1 (Hsil _ _ _ Hs)) as ->. destruct (Hcont eff m' Hs Hns) as [m'' [E _]]. rewrite E. discriminate. }
  pose proof (node_all ms model x8 Hh Hsvc Hnu Hnh Hmat) as Hnode.
  assert (Hev : forall i : sys_ix ms model x8, ix_evs i = []).
  { intros [[[[eff m'] evs] m''] (Hs & Hns & Hm)]. unfold ix_evs. cbn [proj1_sig fst snd]. exact (proj1 (Hsil _ _ _ Hs)). }
  assert (Hnode' : node_ok_cfg segs cfg (mkCfg ms model) (sys_ix ms model x8) (fun _ => [])
                     (fun i => mkCfg (advance_past_svc (apply_effect ms (ix_eff i))) (ix_mod i))).
  { destruct Hnode as [N1 N2]. split.
    - intros i. rewrite <- (Hev i). apply N1.
    - intros e st Hss. destruct (N2 e st Hss) as [i [-> ->]]. exists i. split; [apply Hev | reflexivity]. }
  assert (Hall : forall i : sys_ix ms model x8, realizes_cfg segs cfg (mkCfg (advance_past_svc (apply_effect ms (ix_eff i))) (ix_mod i)) T).
  { intros [[[[eff m'] evs] m''] (Hs & Hns & Hm)]. unfold ix_eff, ix_mod. cbn [proj1_sig fst snd] in *.
    pose proof (proj1 (Hsil _ _ _ Hs)) as E. subst evs. destruct (Hcont eff m' Hs Hns) as [m2 [E2 HT]].
    rewrite Hm in E2. injection E2 as <-. exact HT. }
  pose proof (proj1 (Hsil _ _ _ Hs0)) as E0. subst evs0.
  destruct (Hcont eff0 m0 Hs0 Hns0) as [m2 [E2 _]].
  exact (rzc_silent_all segs cfg _ _ _ T (exist _ (eff0, m0, [], m2) (conj Hs0 (conj Hns0 E2))) Hnode' Hall).
Qed.

Theorem rzc_chk_silent (ms : machine_state) (model : Model) (x8 : word) (T : TSet) :
  m_halted model = None -> ms_svc_pending ms = Some x8 ->
  check_syscall (INP ms x8) (mkEffect (Z_to_bv 64 0) [] []) model <> CheckUnmodeled ->
  (forall eff m' evs, check_syscall (INP ms x8) eff model = CheckOk m' evs -> evs = [] /\ m_halted m' = None) ->
  (exists eff m', check_syscall (INP ms x8) eff model = CheckOk m' [] /\ ~ spurious_refusal_cfg cfg (INP ms x8) model eff) ->
  (forall eff m', check_syscall (INP ms x8) eff model = CheckOk m' [] -> ~ spurious_refusal_cfg cfg (INP ms x8) model eff ->
     exists m'', materialize_model_accesses m' (syscall_effect_accesses eff) = Some m''
                 /\ realizes_cfg segs cfg (mkCfg (advance_past_svc (apply_effect ms eff)) m'') T) ->
  realizes_cfg segs cfg (mkCfg ms model) T.
Proof.
  intros Hh Hsvc Hnu Hsil [eff0 [m0 [Hc0 Hr0]]] Hcont.
  apply (rzc_all_silent ms model x8 T Hh Hsvc).
  - intros Hs. apply Hnu. exact (proj2 (check_syscall_err_iff _ _ _) Hs).
  - intros eff m' evs Hs. apply check_syscall_ok_iff in Hs. exact (Hsil _ _ _ Hs).
  - exists eff0, m0, []. split; [apply check_syscall_ok_iff; exact Hc0 | exact Hr0].
  - intros eff m' Hs Hns. exact (Hcont eff m' (proj2 (check_syscall_ok_iff _ _ _ _ _) Hs) Hns).
Qed.

Lemma forced_not_spurious (ms : machine_state) (model : Model) (x8 : word) (eff : SyscallEffect) :
  (forall eff' m' evs', check_syscall (INP ms x8) eff' model = CheckOk m' evs' -> refusal_b (INP ms x8) model (eff_ret eff') = true) ->
  ~ spurious_refusal_cfg cfg (INP ms x8) model eff.
Proof.
  intros Hall (_ & _ & [eff' [m' [evs' [Hs Hr]]]]). apply check_syscall_ok_iff in Hs. rewrite (Hall _ _ _ Hs) in Hr. discriminate Hr.
Qed.

Theorem rzc_sys_silent (ms : machine_state) (model : Model) (x8 : word) (T : TSet) :
  m_halted model = None -> ms_svc_pending ms = Some x8 ->
  check_syscall (INP ms x8) (mkEffect (Z_to_bv 64 0) [] []) model <> CheckUnmodeled ->
  (forall eff m' evs, check_syscall (INP ms x8) eff model = CheckOk m' evs -> evs = [] /\ m_halted m' = None) ->
  (exists eff m', check_syscall (INP ms x8) eff model = CheckOk m' [] /\ refusal_b (INP ms x8) model (eff_ret eff) = false) ->
  (forall eff m', check_syscall (INP ms x8) eff model = CheckOk m' [] ->
     (injected_family_off cfg (INP ms x8) = true -> refusal_b (INP ms x8) model (eff_ret eff) = false) ->
     exists m'', materialize_model_accesses m' (syscall_effect_accesses eff) = Some m''
                 /\ realizes_cfg segs cfg (mkCfg (advance_past_svc (apply_effect ms eff)) m'') T) ->
  realizes_cfg segs cfg (mkCfg ms model) T.
Proof.
  intros Hh Hsvc Hnu Hsil [eff0 [m0 [Hc0 Hr0]]] Hcont.
  apply (rzc_all_silent ms model x8 T Hh Hsvc).
  - intros Hs. apply Hnu. exact (proj2 (check_syscall_err_iff _ _ _) Hs).
  - intros eff m' evs Hs. apply check_syscall_ok_iff in Hs. exact (Hsil _ _ _ Hs).
  - exists eff0, m0, []. split; [apply check_syscall_ok_iff; exact Hc0 | apply spurious_refusal_not_refusal; exact Hr0].
  - intros eff m' Hs Hns. apply (Hcont eff m' (proj2 (check_syscall_ok_iff _ _ _ _ _) Hs)).
    intros Hoff. destruct (refusal_b (INP ms x8) model (eff_ret eff)) eqn:Er; [|reflexivity].
    exfalso. apply Hns. split; [exact Hoff|]. split; [exact Er|].
    exists eff0, m0, []. split; [apply check_syscall_ok_iff; exact Hc0 | exact Hr0].
Qed.

Lemma rzc_latch (ms : machine_state) (model : Model) (w : bv 32) (T : TSet) :
  m_halted model = None -> ms_svc_pending ms = None ->
  fetch_word segs (ms_pc_val ms) = Some w -> is_ecall w = true ->
  realizes_cfg segs cfg (mkCfg (latch ms) model) T ->
  realizes_cfg segs cfg (mkCfg ms model) T.
Proof.
  intros Hh Hsvc HF HE Hc.
  eapply rzc_acc; [exact Hh | exact Hsvc | eapply wacc_Ecall; [exact HF | exact HE] | apply acc_ok_nil | exact Hc].
Qed.

Lemma check_syscall_96 (ms : machine_state) (x8 : word) (eff : SyscallEffect) (m : Model) :
  bv_unsigned x8 = 96 -> check_syscall (INP ms x8) eff m = check_set_tid_address eff m.
Proof. intros Hno. unfold check_syscall. change (in_sysno (INP ms x8)) with x8. rewrite Hno. reflexivity. Qed.

Lemma check_syscall_222 (ms : machine_state) (x8 : word) (eff : SyscallEffect) (m : Model) :
  bv_unsigned x8 = 222 ->
  check_syscall (INP ms x8) eff m = check_mmap (ms_gpr ms 0) (ms_gpr ms 1) (ms_gpr ms 2) (ms_gpr ms 3) (ms_gpr ms 4) (ms_gpr ms 5) eff m.
Proof. intros Hno. unfold check_syscall. change (in_sysno (INP ms x8)) with x8. rewrite Hno. reflexivity. Qed.

Lemma check_syscall_214 (ms : machine_state) (x8 : word) (eff : SyscallEffect) (m : Model) :
  bv_unsigned x8 = 214 -> check_syscall (INP ms x8) eff m = check_brk (ms_gpr ms 0) eff m.
Proof. intros Hno. unfold check_syscall. change (in_sysno (INP ms x8)) with x8. rewrite Hno. reflexivity. Qed.

Lemma check_syscall_215 (ms : machine_state) (x8 : word) (eff : SyscallEffect) (m : Model) :
  bv_unsigned x8 = 215 -> check_syscall (INP ms x8) eff m = check_munmap (ms_gpr ms 0) (ms_gpr ms 1) eff m.
Proof. intros Hno. unfold check_syscall. change (in_sysno (INP ms x8)) with x8. rewrite Hno. reflexivity. Qed.

Lemma check_syscall_226 (ms : machine_state) (x8 : word) (eff : SyscallEffect) (m : Model) :
  bv_unsigned x8 = 226 -> check_syscall (INP ms x8) eff m = check_mprotect (ms_gpr ms 0) (ms_gpr ms 1) (ms_gpr ms 2) eff m.
Proof. intros Hno. unfold check_syscall. change (in_sysno (INP ms x8)) with x8. rewrite Hno. reflexivity. Qed.

Lemma family_off_alloc (ms : machine_state) (x8 : word) :
  sc_alloc cfg = false -> In (bv_unsigned x8) [214; 215; 222; 226] -> bv_unsigned x8 <> 215 ->
  injected_family_off cfg (INP ms x8) = true.
Proof.
  intros Hoff Hin H215. unfold injected_family_off. change (in_sysno (INP ms x8)) with x8.
  destruct Hin as [H|[H|[H|[H|[]]]]]; try (exfalso; exact (H215 (eq_sym H))); rewrite <- H; cbn; rewrite Hoff; reflexivity.
Qed.

Lemma refusal_b_222 (ms : machine_state) (x8 : word) (model : Model) (r : word) :
  bv_unsigned x8 = 222 -> refusal_b (INP ms x8) model r = ret_in_errnos [ENOMEM] r.
Proof. intros Hno. unfold refusal_b. change (in_sysno (INP ms x8)) with x8. rewrite Hno. reflexivity. Qed.

Lemma refusal_b_226 (ms : machine_state) (x8 : word) (model : Model) (r : word) :
  bv_unsigned x8 = 226 -> refusal_b (INP ms x8) model r = ret_in_errnos [ENOMEM] r.
Proof. intros Hno. unfold refusal_b. change (in_sysno (INP ms x8)) with x8. rewrite Hno. reflexivity. Qed.

Lemma refusal_b_214 (ms : machine_state) (x8 : word) (model : Model) (r : word) :
  bv_unsigned x8 = 214 -> refusal_b (INP ms x8) model r = brk_refusal_b model (ms_gpr ms 0) r.
Proof. intros Hno. unfold refusal_b. change (in_sysno (INP ms x8)) with x8. rewrite Hno. reflexivity. Qed.

Lemma refusal_b_uninjected (ms : machine_state) (x8 : word) (model : Model) (r : word) :
  bv_unsigned x8 <> 214 -> injected_arm (bv_unsigned x8) = None -> refusal_b (INP ms x8) model r = false.
Proof.
  intros H214 Hno. unfold refusal_b. change (in_sysno (INP ms x8)) with x8.
  rewrite (proj2 (Z.eqb_neq _ _) H214), Hno. reflexivity.
Qed.

End Node.
