(** * FOU.BrkFO — the modeled brk over the filtered step at memory forced-only (submissions 1 and 2)

    [AllocSim.sstep_brk_inv] over [Run.sstep_cfg alloc_forced_cfg], keeping what the filter adds: the
    outcome taken is not a spurious refusal ([sstep_cfg_brk_inv]).  A request to move the break is
    refused by keeping the old one; when the model can grow the break that refusal is spurious, so the
    filtered step grows ([brk_keep_spurious]). *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import Mm.Mmap.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound Require Import SimInv ExitSim PropExec CatSim AllocSim.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.FO Require Import FOCore.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Lemma bv_eqb_neq_fou : forall {n} (a b : bv n), a <> b -> bv_eqb a b = false.
Proof. intros n a b H. destruct (bv_eqb a b) eqn:E; [apply bv_eqb_eq in E; contradiction | reflexivity]. Qed.

Lemma bv_eqb_refl_fou : forall {n} (a : bv n), bv_eqb a a = true.
Proof. intros n a. apply bv_eqb_eq. reflexivity. Qed.

(** Keeping the old break on a request to move it is a refusal; any other answer is not. *)
Lemma brk_keep_refusal : forall model req,
  req <> Z_to_bv 64 0 ->
  (bv_unsigned (vm_start_brk (m_vmmaps model)) <= bv_unsigned req)%Z ->
  req <> vm_brk (m_vmmaps model) ->
  brk_refusal_b model req (vm_brk (m_vmmaps model)) = true.
Proof.
  intros model req H0 Hs Hne. unfold brk_refusal_b. cbv zeta.
  assert (Ew : w_is0 req = false) by (unfold w_is0; apply bv_eqb_neq_fou; exact H0).
  rewrite Ew, (bv_eqb_neq_fou _ _ Hne), bv_eqb_refl_fou.
  match goal with |- context [Z.ltb (bv_unsigned req) ?x] =>
    replace (Z.ltb (bv_unsigned req) x) with false by (symmetry; apply Z.ltb_ge; exact Hs) end.
  reflexivity.
Qed.

Lemma brk_ne_refusal : forall model req r,
  r <> vm_brk (m_vmmaps model) -> brk_refusal_b model req r = false.
Proof.
  intros model req r Hne. unfold brk_refusal_b. cbv zeta. rewrite (bv_eqb_neq_fou _ _ Hne). apply andb_false_r.
Qed.

Section WithFP.
Context {fx : FPState}.

Lemma brk_family_off : forall segs ms x8,
  bv_unsigned x8 = 214%Z -> injected_family_off alloc_forced_cfg (sys_input segs ms x8) = true.
Proof. intros segs ms x8 Hno. unfold injected_family_off. rewrite in_sysno_sys_input, Hno. reflexivity. Qed.

Lemma brk_refusal_sys : forall segs ms x8 model r,
  bv_unsigned x8 = 214%Z ->
  refusal_b (sys_input segs ms x8) model r = brk_refusal_b model (ms_gpr ms 0) r.
Proof. intros segs ms x8 model r Hno. unfold refusal_b. rewrite in_sysno_sys_input, Hno. reflexivity. Qed.

(** Beside a resolution that is not a refusal, every refusing resolution is spurious. *)
Lemma brk_refusal_spurious : forall segs ms x8 model r r0,
  bv_unsigned x8 = 214%Z ->
  brk_resolution_ok model (ms_gpr ms 0) r0 ->
  brk_refusal_b model (ms_gpr ms 0) r0 = false ->
  brk_refusal_b model (ms_gpr ms 0) r = true ->
  spurious_refusal_cfg alloc_forced_cfg (sys_input segs ms x8) model
    (mkEffectU r [] (brk_zeros (ms_gpr ms 0) r (vm_brk (m_vmmaps model)))
                    (brk_unmaps r (vm_brk (m_vmmaps model))) [] []).
Proof.
  intros segs ms x8 model r r0 Hno Hok0 Hnr0 Hr. split; [exact (brk_family_off segs ms x8 Hno)|]. split.
  - rewrite (brk_refusal_sys segs ms x8 model _ Hno). exact Hr.
  - exists (mkEffectU r0 [] (brk_zeros (ms_gpr ms 0) r0 (vm_brk (m_vmmaps model)))
                         (brk_unmaps r0 (vm_brk (m_vmmaps model))) [] []),
      (brk_model (ms_gpr ms 0) r0 model), []. split.
    + exact (brk_ok_intro segs ms x8 model r0 Hno Hok0).
    + rewrite (brk_refusal_sys segs ms x8 model _ Hno). exact Hnr0.
Qed.

Section WithSegs.
Variable segs : list Segment.

(** [sstep_brk_inv] over the filtered step: the outcome taken is not a spurious refusal. *)
Lemma sstep_cfg_brk_inv : forall ms model x8 evs st,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 214%Z ->
  sstep_cfg segs alloc_forced_cfg (mkCfg ms model) evs st ->
  exists eff model',
    syscall_spec (sys_input segs ms x8) model (Ok eff model' []) /\
    ~ spurious_refusal_cfg alloc_forced_cfg (sys_input segs ms x8) model eff /\
    evs = [] /\
    st = SNext (mkCfg (advance_past_svc (apply_effect ms eff)) model').
Proof.
  intros ms model x8 evs st Hh Hlazy Hsvc Hno Hss.
  inversion Hss; subst; try congruence.
  - match goal with
    | Hsvc' : ms_svc_pending ms = Some ?x,
      Hspec : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
      Hn : ~ spurious_refusal_cfg _ _ _ _,
      Hmat : materialize_model_accesses ?model' _ = Some ?m2 |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      destruct (brk_step_shape segs ms x8 model eff model' evs0 Hh Hlazy Hno Hspec)
        as (He & _ & _ & _ & Hlazy'); subst evs0;
      rewrite (materialize_model_accesses_no_lazy _ _ (eq_trans Hlazy' Hlazy)) in Hmat;
      injection Hmat as Hm2; subst m2;
      exists eff, model'; split; [exact Hspec | split; [exact Hn | split; reflexivity]]
    end.
  - exfalso.
    match goal with
    | Hspec : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
      Hmat : materialize_model_accesses ?model' _ = None |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      destruct (brk_step_shape segs ms x8 model eff model' evs0 Hh Hlazy Hno Hspec)
        as (He & _ & _ & _ & Hlazy'); subst evs0;
      rewrite (materialize_model_accesses_no_lazy _ _ (eq_trans Hlazy' Hlazy)) in Hmat;
      discriminate
    end.
  - exfalso.
    match goal with
    | Hsvc' : ms_svc_pending ms = Some ?x,
      Hspec : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
      Hhalt : m_halted ?model' = Some ?code |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      destruct (brk_step_shape segs ms x8 model eff model' evs0 Hh Hlazy Hno Hspec) as (_ & Hm & _ & _);
      congruence
    end.
  - exfalso.
    match goal with
    | Hsvc' : ms_svc_pending ms = Some ?x,
      Hspec : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
      Hkill : m_killed ?model' = Some ?sig |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      destruct (brk_step_shape segs ms x8 model eff model' evs0 Hh Hlazy Hno Hspec) as (_ & Hm & _ & _);
      assert (Hhn : m_halted model' = None) by congruence;
      rewrite (m_killed_of_m_halted_none _ Hhn) in Hkill; discriminate
    end.
  - exfalso.
    match goal with
    | Hsvc' : ms_svc_pending ms = Some ?x,
      Hspec : syscall_spec (sys_input segs ms ?x) model Unmodeled |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      exact (brk_no_unmodeled segs ms x8 model Hno Hspec)
    end.
Qed.

End WithSegs.
End WithFP.
