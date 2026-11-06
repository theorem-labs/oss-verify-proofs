(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Classical_Prop.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uapi Syscall Dispatch SyscallTable.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Mprotect Mremap.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
Import ListNotations.
Open Scope bv_scope.

Definition ACFG : SpuriousCfg := alloc_only_cfg false.

(* Under ACFG only the allocation family is forced-only, and every
   allocation arm carries a number on alloc_mark_sysnos. *)
Lemma acfg_family_off_in (sysin : SyscallInput) :
  injected_family_off ACFG sysin = true ->
  In (bv_unsigned (in_sysno sysin)) alloc_mark_sysnos.
Proof.
  unfold injected_family_off.
  destruct (injected_arm (bv_unsigned (in_sysno sysin))) as [entry |] eqn:entry_eq;
    [| intros no_entry; discriminate no_entry].
  intros fam_forced.
  apply (alloc_family_dispatched _ entry entry_eq).
  revert fam_forced. unfold ACFG, alloc_only_cfg.
  destruct (ia_family entry); cbn; intros fam_forced;
    first [reflexivity | discriminate fam_forced].
Qed.

Lemma acfg_family_on_notin (sysin : SyscallInput)
    (sysnum_outside : ~ In (bv_unsigned (in_sysno sysin)) alloc_mark_sysnos) :
  injected_family_off ACFG sysin = false.
Proof.
  destruct (injected_family_off ACFG sysin) eqn:fam_verdict; [| reflexivity].
  destruct (sysnum_outside (acfg_family_off_in sysin fam_verdict)).
Qed.

Lemma acfg_nonspurious (sysin : SyscallInput) (kmod : Model) (outc : SyscallEffect) :
  ~ In (bv_unsigned (in_sysno sysin)) alloc_mark_sysnos ->
  ~ spurious_refusal_cfg ACFG sysin kmod outc.
Proof.
  intros sysnum_outside.
  exact (spurious_refusal_family_on ACFG sysin kmod outc
           (acfg_family_on_notin sysin sysnum_outside)).
Qed.

Definition alloc_no_b (n : Z) : bool :=
  existsb (fun k => Z.eqb n k) alloc_mark_sysnos.

(* Each listed number makes the test compute to true. *)
Lemma alloc_no_b_false (sysnum : Z) (test_false : alloc_no_b sysnum = false) :
  ~ In sysnum alloc_mark_sysnos.
Proof.
  unfold alloc_mark_sysnos. cbn [In].
  intros [<- | [<- | [<- | [<- | []]]]];
    vm_compute in test_false; discriminate test_false.
Qed.

Lemma acfg_nonspurious_no lsegs mstate sysw (sysnum : Z) (kmod : Model) (outc : SyscallEffect) :
  bv_unsigned sysw = sysnum ->
  alloc_no_b sysnum = false ->
  ~ spurious_refusal_cfg ACFG (sys_input lsegs mstate sysw) kmod outc.
Proof.
  intros sysnum_is test_false. subst sysnum.
  apply acfg_nonspurious. cbn [sys_input in_sysno].
  exact (alloc_no_b_false _ test_false).
Qed.

Lemma acfg_family_off_222 (sysin : SyscallInput) :
  bv_unsigned (in_sysno sysin) = 222%Z ->
  injected_family_off ACFG sysin = true.
Proof. intros no_eq. unfold injected_family_off. now rewrite no_eq. Qed.

Lemma acfg_family_off_226 (sysin : SyscallInput) :
  bv_unsigned (in_sysno sysin) = 226%Z ->
  injected_family_off ACFG sysin = true.
Proof. intros no_eq. unfold injected_family_off. now rewrite no_eq. Qed.

Lemma acfg_family_off_216 (sysin : SyscallInput) :
  bv_unsigned (in_sysno sysin) = 216%Z ->
  injected_family_off ACFG sysin = true.
Proof. intros no_eq. unfold injected_family_off. now rewrite no_eq. Qed.

Lemma acfg_family_off_214 (sysin : SyscallInput) :
  bv_unsigned (in_sysno sysin) = 214%Z ->
  injected_family_off ACFG sysin = true.
Proof. intros no_eq. unfold injected_family_off. now rewrite no_eq. Qed.

Lemma refusal_b_222 (sysin : SyscallInput) (kmod : Model) (answer : word) :
  bv_unsigned (in_sysno sysin) = 222%Z ->
  refusal_b sysin kmod answer = ret_in_errnos mmap_errnos answer.
Proof. intros no_eq. unfold refusal_b. now rewrite no_eq. Qed.

Lemma refusal_b_226 (sysin : SyscallInput) (kmod : Model) (answer : word) :
  bv_unsigned (in_sysno sysin) = 226%Z ->
  refusal_b sysin kmod answer = ret_in_errnos mprotect_errnos answer.
Proof. intros no_eq. unfold refusal_b. now rewrite no_eq. Qed.

Lemma refusal_b_216 (sysin : SyscallInput) (kmod : Model) (answer : word) :
  bv_unsigned (in_sysno sysin) = 216%Z ->
  refusal_b sysin kmod answer = ret_in_errnos mremap_errnos answer.
Proof. intros no_eq. unfold refusal_b. now rewrite no_eq. Qed.

Lemma refusal_b_214 (sysin : SyscallInput) (kmod : Model) (answer : word) :
  bv_unsigned (in_sysno sysin) = 214%Z ->
  refusal_b sysin kmod answer = brk_refusal_b kmod (in_arg sysin 0) answer.
Proof. intros no_eq. unfold refusal_b. now rewrite no_eq. Qed.

Lemma ret_in_errnos_ENOMEM (answer : word) :
  ret_in_errnos [ENOMEM] answer = bv_eqb answer (errno_ret ENOMEM).
Proof.
  unfold ret_in_errnos. cbn [existsb].
  now destruct (bv_eqb answer (errno_ret ENOMEM)).
Qed.

Lemma ret_in_errnos_errno (errs : list Z) (err : Z) :
  In err errs -> ret_in_errnos errs (errno_ret err) = true.
Proof.
  unfold ret_in_errnos.
  induction errs as [| first_err more_errs more_ih]; cbn [In existsb];
    intros err_listed.
  - destruct err_listed.
  - destruct err_listed as [first_is | in_more].
    + subst first_err. unfold bv_eqb. now rewrite Z.eqb_refl.
    + now rewrite (more_ih in_more), orb_true_r.
Qed.

(* A refusal is spurious as soon as the family is off and some allowed
   outcome is not a refusal. *)
Lemma refusal_spurious_of_grant (scfg : SpuriousCfg) (sysin : SyscallInput) (kmod : Model)
    (outc wit_out : SyscallEffect) (wit_kmod : Model) wit_evl :
  injected_family_off scfg sysin = true ->
  refusal_b sysin kmod (eff_ret outc) = true ->
  syscall_spec sysin kmod (Ok wit_out wit_kmod wit_evl) ->
  refusal_b sysin kmod (eff_ret wit_out) = false ->
  spurious_refusal_cfg scfg sysin kmod outc.
Proof.
  intros fam_forced refuses wit_allowed wit_accepts.
  refine (conj fam_forced (conj refuses _)).
  now exists wit_out, wit_kmod, wit_evl.
Qed.

Lemma nonspurious_not_refusal_of_grant (scfg : SpuriousCfg) (sysin : SyscallInput) (kmod : Model)
    (outc wit_out : SyscallEffect) (wit_kmod : Model) wit_evl :
  injected_family_off scfg sysin = true ->
  ~ spurious_refusal_cfg scfg sysin kmod outc ->
  syscall_spec sysin kmod (Ok wit_out wit_kmod wit_evl) ->
  refusal_b sysin kmod (eff_ret wit_out) = false ->
  refusal_b sysin kmod (eff_ret outc) = false.
Proof.
  intros fam_forced not_filtered wit_allowed wit_accepts.
  apply not_true_is_false. intros refuses.
  exact (not_filtered (refusal_spurious_of_grant scfg sysin kmod outc wit_out wit_kmod wit_evl
                         fam_forced refuses wit_allowed wit_accepts)).
Qed.

Lemma nonspurious_refusal_no_grant (scfg : SpuriousCfg) (sysin : SyscallInput) (kmod : Model)
    (outc : SyscallEffect) :
  ~ spurious_refusal_cfg scfg sysin kmod outc ->
  injected_family_off scfg sysin = true ->
  refusal_b sysin kmod (eff_ret outc) = true ->
  forall (wit_out : SyscallEffect) (wit_kmod : Model) wit_evl,
    syscall_spec sysin kmod (Ok wit_out wit_kmod wit_evl) ->
    refusal_b sysin kmod (eff_ret wit_out) = true.
Proof.
  intros not_filtered fam_forced refuses alt_out alt_kmod alt_evl alt_allowed.
  destruct (refusal_b sysin kmod (eff_ret alt_out)) eqn:alt_verdict; [reflexivity |].
  exfalso. apply not_filtered.
  exact (refusal_spurious_of_grant scfg sysin kmod outc alt_out alt_kmod alt_evl
           fam_forced refuses alt_allowed alt_verdict).
Qed.

Lemma not_spurious_forced (scfg : SpuriousCfg) (sysin : SyscallInput) (kmod : Model)
    (outc : SyscallEffect) :
  (forall wit_out wit_kmod wit_evl,
     syscall_spec sysin kmod (Ok wit_out wit_kmod wit_evl) ->
     refusal_b sysin kmod (eff_ret wit_out) = true) ->
  ~ spurious_refusal_cfg scfg sysin kmod outc.
Proof.
  intros every_refuses (_ & _ & alt_out & alt_kmod & alt_evl & alt_allowed & alt_accepts).
  specialize (every_refuses alt_out alt_kmod alt_evl alt_allowed).
  congruence.
Qed.

(* The filter reads an input only through its number, its first argument
   and the spec's outcomes at it; one direction suffices, by symmetry. *)
Lemma spurious_refusal_transport (scfg : SpuriousCfg) (left_in right_in : SyscallInput)
    (kmod : Model) (outc : SyscallEffect) :
  in_sysno left_in = in_sysno right_in ->
  in_arg left_in 0 = in_arg right_in 0 ->
  (forall wit_out wit_kmod wit_evl,
     syscall_spec left_in kmod (Ok wit_out wit_kmod wit_evl)
     <-> syscall_spec right_in kmod (Ok wit_out wit_kmod wit_evl)) ->
  spurious_refusal_cfg scfg left_in kmod outc <-> spurious_refusal_cfg scfg right_in kmod outc.
Proof.
  assert (one_way : forall from_in to_in : SyscallInput,
            in_sysno from_in = in_sysno to_in ->
            in_arg from_in 0 = in_arg to_in 0 ->
            (forall alt_out alt_kmod alt_evl,
               syscall_spec from_in kmod (Ok alt_out alt_kmod alt_evl) ->
               syscall_spec to_in kmod (Ok alt_out alt_kmod alt_evl)) ->
            spurious_refusal_cfg scfg from_in kmod outc ->
            spurious_refusal_cfg scfg to_in kmod outc).
  { intros from_in to_in same_no same_first spec_carry
      (fam_part & refusal_part & alt_out & alt_kmod & alt_evl & alt_allowed & alt_accepts).
    assert (verdict_same : forall answer,
              refusal_b from_in kmod answer = refusal_b to_in kmod answer).
    { intros answer. unfold refusal_b. now rewrite same_no, same_first. }
    refine (conj _ (conj _ (ex_intro _ alt_out (ex_intro _ alt_kmod (ex_intro _ alt_evl
              (conj (spec_carry _ _ _ alt_allowed) _)))))).
    - unfold injected_family_off in *. rewrite <- same_no. exact fam_part.
    - rewrite <- verdict_same. exact refusal_part.
    - rewrite <- verdict_same. exact alt_accepts. }
  intros same_no same_first spec_same. split.
  - apply (one_way left_in right_in same_no same_first).
    intros alt_out alt_kmod alt_evl. exact (proj1 (spec_same alt_out alt_kmod alt_evl)).
  - apply (one_way right_in left_in (eq_sym same_no) (eq_sym same_first)).
    intros alt_out alt_kmod alt_evl. exact (proj2 (spec_same alt_out alt_kmod alt_evl)).
Qed.

(* Either the spec allows some grant at this input, and a grant is never
   filtered, or it allows none, and then every allowed outcome is forced. *)
Lemma exists_nonspurious (scfg : SpuriousCfg) (sysin : SyscallInput) (kmod : Model)
    (outc : SyscallEffect) (post_kmod : Model) post_evl :
  syscall_spec sysin kmod (Ok outc post_kmod post_evl) ->
  exists wit_out wit_kmod wit_evl,
    syscall_spec sysin kmod (Ok wit_out wit_kmod wit_evl) /\ ~ spurious_refusal_cfg scfg sysin kmod wit_out.
Proof.
  intros outc_allowed.
  destruct (classic (exists alt_out alt_kmod alt_evl,
                       syscall_spec sysin kmod (Ok alt_out alt_kmod alt_evl)
                       /\ refusal_b sysin kmod (eff_ret alt_out) = false))
    as [(alt_out & alt_kmod & alt_evl & alt_allowed & alt_accepts) | no_grant].
  - exists alt_out, alt_kmod, alt_evl. split; [exact alt_allowed |].
    exact (spurious_refusal_not_refusal scfg sysin kmod alt_out alt_accepts).
  - exists outc, post_kmod, post_evl. split; [exact outc_allowed |].
    apply not_spurious_forced. intros alt_out alt_kmod alt_evl alt_allowed.
    destruct (refusal_b sysin kmod (eff_ret alt_out)) eqn:alt_verdict; [reflexivity |].
    exfalso. apply no_grant.
    exists alt_out, alt_kmod, alt_evl. split; assumption.
Qed.

Section Steps.
Variable segs : list Segment.

Lemma sstep_of_cfg (scfg : SpuriousCfg) (conf : config) (evl : list event) (dest : step_to) :
  sstep_cfg segs scfg conf evl dest -> sstep segs conf evl dest.
Proof. exact (sstep_cfg_sub segs scfg conf evl dest). Qed.

Lemma star_of_cfg (scfg : SpuriousCfg) (conf : config) (trc : list event) (conf_end : config) :
  star_cfg segs scfg conf trc conf_end -> star segs conf trc conf_end.
Proof. exact (star_cfg_sub segs scfg conf trc conf_end). Qed.

Definition cfg_transparent (c : config) : Prop :=
  forall (e : list event) (st : step_to),
    sstep segs c e st -> sstep_cfg segs ACFG c e st.

(* With no pending syscall only the three instruction rules apply, and
   they carry no filter premise. *)
Lemma transparent_instr (mstate : machine_state) (kmod : Model) :
  ms_svc_pending mstate = None -> cfg_transparent (mkCfg mstate kmod).
Proof.
  intros no_svc evl dest unfiltered.
  inversion unfiltered; subst; try congruence.
  - apply sstep_cfg_instr; assumption.
  - apply sstep_cfg_instr_fault; assumption.
  - apply sstep_cfg_instr_unmodeled; assumption.
Qed.

(* With the pending syscall's family on, nothing is spurious, so each
   syscall rule carries over. *)
Lemma transparent_family_on (mstate : machine_state) (kmod : Model) sysw :
  ms_svc_pending mstate = Some sysw ->
  injected_family_off ACFG (sys_input segs mstate sysw) = false ->
  cfg_transparent (mkCfg mstate kmod).
Proof.
  intros svc_is fam_free evl dest unfiltered.
  assert (never_filtered : forall pending_no any_out, ms_svc_pending mstate = Some pending_no ->
            ~ spurious_refusal_cfg ACFG (sys_input segs mstate pending_no) kmod any_out).
  { intros pending_no any_out pending_is.
    rewrite svc_is in pending_is. injection pending_is as <-.
    exact (spurious_refusal_family_on ACFG _ kmod any_out fam_free). }
  inversion unfiltered; subst; try congruence; clear svc_is fam_free;
    [ econstructor 4 | econstructor 5 | econstructor 6 | econstructor 7 | econstructor 8 ];
    eauto.
Qed.

Lemma transparent_nonalloc (mstate : machine_state) (kmod : Model) sysw :
  ms_svc_pending mstate = Some sysw ->
  ~ In (bv_unsigned sysw) alloc_mark_sysnos ->
  cfg_transparent (mkCfg mstate kmod).
Proof.
  exact (fun svc_is sysnum_outside =>
           transparent_family_on mstate kmod sysw svc_is
             (acfg_family_on_notin (sys_input segs mstate sysw) sysnum_outside)).
Qed.

Lemma transparent_nonalloc_no (mstate : machine_state) (kmod : Model) sysw (sysnum : Z) :
  ms_svc_pending mstate = Some sysw -> bv_unsigned sysw = sysnum -> alloc_no_b sysnum = false ->
  cfg_transparent (mkCfg mstate kmod).
Proof.
  intros svc_is sysnum_is test_false.
  rewrite <- sysnum_is in test_false.
  apply (transparent_nonalloc mstate kmod sysw svc_is).
  apply alloc_no_b_false. exact test_false.
Qed.

Lemma sstep_cfg_syscall_nonrefusal (scfg : SpuriousCfg) (mstate : machine_state) (kmod : Model)
    sysw (outc : SyscallEffect) (kmod_post kmod_mat : Model) (evl : list event) :
  m_halted kmod = None ->
  ms_svc_pending mstate = Some sysw ->
  syscall_spec (sys_input segs mstate sysw) kmod (Ok outc kmod_post evl) ->
  refusal_b (sys_input segs mstate sysw) kmod (eff_ret outc) = false ->
  m_halted kmod_post = None ->
  materialize_model_accesses kmod_post (syscall_effect_accesses outc) = Some kmod_mat ->
  sstep_cfg segs scfg (mkCfg mstate kmod) evl
    (SNext (mkCfg (advance_past_svc (apply_effect mstate outc)) kmod_mat)).
Proof.
  intros running svc_is outc_allowed outc_accepts still_running charged.
  exact (sstep_cfg_syscall segs scfg mstate kmod sysw outc kmod_post kmod_mat evl
           running svc_is outc_allowed
           (spurious_refusal_not_refusal scfg _ kmod outc outc_accepts)
           still_running charged).
Qed.

End Steps.

Section Star.
Variable segs : list Segment.
Variable cfg : SpuriousCfg.

Lemma star_cfg_one (conf : config) (evl : list event) (conf_end : config) :
  sstep_cfg segs cfg conf evl (SNext conf_end) -> star_cfg segs cfg conf evl conf_end.
Proof.
  intros one_step.
  pose proof (star_cfg_step segs cfg conf evl conf_end [] conf_end one_step
                (star_cfg_refl segs cfg conf_end)) as padded.
  rewrite app_nil_r in padded. exact padded.
Qed.

Lemma star_cfg_trans (conf_a : config) (trc_a : list event) (conf_b : config)
    (trc_b : list event) (conf_c : config) :
  star_cfg segs cfg conf_a trc_a conf_b ->
  star_cfg segs cfg conf_b trc_b conf_c ->
  star_cfg segs cfg conf_a (trc_a ++ trc_b) conf_c.
Proof.
  intros first_leg second_leg. revert second_leg.
  induction first_leg as [stay | from_c step_ev via_c rest_tr to_c via_step via_star via_ih];
    intros second_leg.
  - exact second_leg.
  - rewrite <- app_assoc.
    exact (star_cfg_step segs cfg from_c step_ev via_c (rest_tr ++ trc_b) conf_c
             via_step (via_ih second_leg)).
Qed.

Lemma obs_trace_cfg_nil (conf : config) : obs_trace_cfg segs cfg conf [].
Proof. exact (ex_intro _ [] (ex_intro _ conf (conj (star_cfg_refl segs cfg conf) I))). Qed.

Lemma sstep_cfg_halted_none (conf : config) (evl : list event) (dest : step_to) :
  sstep_cfg segs cfg conf evl dest -> m_halted (cfg_model conf) = None.
Proof. intros one_step. destruct one_step; cbn [cfg_model]; assumption. Qed.

Lemma star_cfg_halted_nil (conf : config) (trc : list event) (conf_end : config) :
  m_halted (cfg_model conf) <> None ->
  star_cfg segs cfg conf trc conf_end ->
  trc = [] /\ conf_end = conf.
Proof.
  intros halted path. revert halted.
  destruct path as [stay | from_c step_ev via_c rest_tr to_c via_step _]; intros halted.
  - split; reflexivity.
  - exfalso. exact (halted (sstep_cfg_halted_none from_c step_ev (SNext via_c) via_step)).
Qed.

Lemma reaches_error_cfg_here (conf : config) (evl : list event) :
  sstep_cfg segs cfg conf evl SError -> reaches_error_cfg segs cfg conf.
Proof.
  exact (fun err_step =>
           ex_intro _ [] (ex_intro _ conf (ex_intro _ evl
             (conj (star_cfg_refl segs cfg conf) err_step)))).
Qed.

Lemma reaches_error_cfg_step (conf : config) (evl : list event) (conf_next : config) :
  sstep_cfg segs cfg conf evl (SNext conf_next) ->
  reaches_error_cfg segs cfg conf_next ->
  reaches_error_cfg segs cfg conf.
Proof.
  unfold reaches_error_cfg.
  intros one_step (rest_tr & err_c & err_ev & path & err_step).
  exists (evl ++ rest_tr), err_c, err_ev.
  exact (conj (star_cfg_step segs cfg conf evl conf_next rest_tr err_c one_step path)
              err_step).
Qed.

End Star.
