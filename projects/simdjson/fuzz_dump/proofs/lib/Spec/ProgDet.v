(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Specs Run.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.Lib Require Import PropExec MState Mem ITree Nodes Decode Ceiling Image Stage.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib Require Import TopLevel Obligations.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.Spec Require Import Prelim Monad Stdio Driver Prog Canon ModelInv ModelInvN MallocSome.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.Spec Require Import ProgDetIface ProgDetLogic ProgDetNodes ProgDetMalloc ProgDetStdio ProgDetTarget ProgDetDriver.
From OSSVerify.simdjson.fuzz_dump.images Require Import Plain.
From OSSVerify.simdjson.fuzz_dump.images Require Import Ubsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Ltac splits := repeat (lazymatch goal with |- _ /\ _ => split | |- _ => fail end).

Definition Xcanon (sel : option bool) (argv : list (list Z)) (fs : Fs) (tr : list event) : Prop :=
  exists b, compat sel b /\ tr = ct_events fs (ctrace_of argv fs b).

Lemma ct_code_cases : forall argv fs b, ct_code (ctrace_of argv fs b) = 0 \/ ct_code (ctrace_of argv fs b) = 2.
Proof.
  intros argv fs b. unfold ctrace_of. destruct (negb _); [right; reflexivity|].
  destruct (if b then open_class _ fs else OCFail) as [| |data]; try (right; reflexivity).
  unfold file_trace. repeat match goal with |- context [if ?c then _ else _] => destruct c end; cbn; auto.
Qed.

Lemma exit_code_small : forall c, c = 0 \/ c = 2 -> exit_code c = Z_to_bv 64 c.
Proof. intros c [->| ->]; apply bv_eq; vm_compute; reflexivity. Qed.

Section Whole.
Context {CE__ : Ceiling}.
Variable sel : option bool.
Variable rstage : Z.
Variable fs : Fs.
Variable argv : list (list Z).
Hypothesis Hargv : Forall (fun a => zlength a < 2^32) argv.

Let X := Xcanon sel argv fs.

Lemma startup_E : forall (P : assnE PState),
  (forall s mo tr mo', P s mo tr -> m_fds mo' = m_fds mo -> m_fs mo' = m_fs mo -> P s mo' tr) ->
  mspecE sel X P startup (fun _ => P).
Proof.
  intros P HP. unfold startup.
  eapply mspecE_seq with (R := P); [|intros _; apply mspecE_ret; auto].
  apply msysE_node; [exact I| intros; apply nprog_set_tid|].
  intros s mo tr rsp mo' evs a H Hst _. destruct (stepR_set_tid sel mo rsp mo' evs Hst) as (-> & Hfd & Hfs).
  rewrite app_nil_r. eapply HP; eauto.
Qed.

Lemma exit_model_E : forall code,
  mspecE sel X (Qmain sel fs [] argv code) (exit_model Prog.io code) (fun _ _ _ _ => False).
Proof.
  intros code. unfold exit_model. apply mspecE_pointwise. intros s0 mo0 tr0 (b & Hb & Hcode & Hfs & Hl & Htr).
  eapply mspecE_seq.
  { eapply mspecE_pre; [apply (stdout_exit_flush_E ps_so set_so_ps sel X (fun _ _ => eq_refl) (fun mo => m_fs mo = fs) (ps_so s0) tr0 Hl)|].
    intros s mo tr (-> & -> & ->). unfold SoA. auto. }
  intros _. apply msysE_exit. intros s mo tr (Hfs' & ->). exists b. split; [exact Hb|].
  rewrite Htr, Hfs', Hcode, exit_code_small by apply ct_code_cases. unfold ct_events. cbn [app]. reflexivity.
Qed.

Lemma prog_with_E : forall (P0 : assnE PState),
  (forall s mo tr, P0 s mo tr -> m_fds mo = fds_std /\ m_fs mo = fs /\ ps_so s = stdout_init /\ tr = []) ->
  mspecE sel X P0 (prog_with rstage argv) (fun _ _ _ _ => False).
Proof.
  intros P0 HP0. unfold prog_with.
  eapply mspecE_seq with (R := fun s mo tr => m_fds mo = fds_std /\ m_fs mo = fs /\ ps_so s = stdout_init /\ tr = []).
  { eapply mspecE_pre; [apply startup_E|exact HP0]. intros s mo tr mo' (H1 & H2 & H3 & H4) E1 E2. splits; congruence. }
  intros _. eapply mspecE_bind; [apply (main_model_E sel X rstage fs [] argv Hargv)|].
  intros code. apply exit_model_E.
Qed.

End Whole.

Lemma prog_twfE : forall {CE__ : Ceiling} sel segs rstage argv mo,
  Forall (fun a => zlength a < 2^32) (argv_Z argv) -> m_fds mo = fds_std ->
  twfE sel (Xcanon sel (argv_Z argv) (m_fs mo)) (prog segs rstage argv) mo [] (fun _ _ _ => True).
Proof.
  intros CE sel segs rstage argv mo Hargv Hfd. unfold prog. apply twfE_ebind.
  eapply twfE_mono.
  - apply (prog_with_E sel rstage (m_fs mo) (argv_Z argv) Hargv (fun s mo' tr => s = ps_init (reservedZ segs) /\ mo' = mo /\ tr = [])).
    + intros s mo' tr (-> & -> & ->). splits; auto.
    + auto.
  - intros p mo' tr' [].
Qed.

Lemma run_ceiling_eq : forall segs pc ph en inp,
  in_va_size inp = Sv48 ->
  valid_entry (mkImage segs pc ph) en inp ->
  bv_unsigned (en_sp en) - stack_max_size = @alloc_ceiling (run_ceiling en).
Proof.
  intros segs pc ph en inp Hsv48 Hve. rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hve.
  destruct en as [sp brk mb rnd]. destruct Hve as (Hsp & _ & _ & _). destruct Hsp as (H1 & H2 & H3).
  cbn [en_sp]. unfold run_ceiling, sp_window_lo, sp_window_hi, stack_max_size in *. cbn [en_sp].
  rewrite ceiling_of_sp_eq; [reflexivity| lia| exact H3].
Qed.

Theorem prog_det_gen : forall segs rstage pc ph lim,
  segs_pu segs ->
  prog_no_enomem_stmt segs rstage pc ph lim ->
  forall en inp, valid_entry (mkImage segs pc ph) en inp -> valid_input_either inp ->
  forall t', resolves t' (the_prog segs rstage inp en) ->
  forall tr, tree_traces t' (mo0 segs lim en inp) tr
             <-> canonT (argv_Z (in_argv inp)) (in_fs inp) tr.
Proof.
  intros segs rstage pc ph lim Hsegs Hne en inp Hve Hvi t' Hres tr.
  pose proof (prog_model_ok (CE__ := run_ceiling en) (raw_malloc_some (CE__ := run_ceiling en)) segs rstage pc ph lim en inp Hsegs Hve Hvi
                (run_ceiling_eq segs pc ph en inp (vie_va_size _ Hvi) Hve) (Hne en inp Hve Hvi)) as [Hl0 Hs0].
  pose proof (Hne en inp Hve Hvi) as Hne'. unfold the_prog in *.
  set (t := @prog (run_ceiling en) segs rstage (in_argv inp)) in *.
  set (mo := mo0 segs lim en inp) in *.
  assert (HPn0 : tsafe nstep Pn t mo) by (apply tsafe_Pn; [exact Hs0| exact Hne'| apply mo0_minv| apply mo0_not_halted]).
  pose proof (tsafe_resolves _ _ _ t' t Hres mo HPn0) as HPn.
  pose proof (leaves_unreachable_m_resolves _ _ t' t Hres mo Hl0) as Hl.
  assert (Hargv : Forall (fun a => zlength a < 2^32) (argv_Z (in_argv inp))) by (apply argv_Z_short; exact (proj1 Hvi)).
  assert (Hfd : m_fds mo = fds_std) by (unfold mo, TopLevel.mo0; rewrite m_fds_init_model; reflexivity).
  assert (Hfs : m_fs mo = in_fs inp) by (unfold mo, TopLevel.mo0; rewrite m_fs_init_model; reflexivity).
  split.
  - intros (full & Hfull & Hp).
    apply ttrace_split in Hfull. destruct Hfull as [Hx|(r & mo' & Hpath)]; [|exfalso; exact (Hl _ _ _ Hpath)].
    pose proof (texit_nstep_stepR t' mo full HPn Hx) as HxR.
    pose proof (twfE_texit None _ t' mo [] _ full
                  (twfE_resolves None _ t' t Hres mo [] _ (prog_twfE (CE__ := run_ceiling en) None segs rstage (in_argv inp) mo Hargv Hfd)) HxR) as (b & _ & E).
    cbn [app] in E. rewrite Hfs in E. apply canonT_iff. exists b. rewrite <- E. exact Hp.
  - intros Hc. apply canonT_iff in Hc. destruct Hc as (ok & Hp).
    pose proof (twfE_resolves (Some ok) _ t' t Hres mo [] _ (prog_twfE (CE__ := run_ceiling en) (Some ok) segs rstage (in_argv inp) mo Hargv Hfd)) as Htw.
    destruct (twfE_exists (Some ok) _ t' mo [] _ Htw HPn Hl) as (full & Hx).
    pose proof (twfE_texit (Some ok) _ t' mo [] _ full Htw Hx) as (b & Hb & E).
    rewrite (Hb ok eq_refl) in E. cbn [app] in E. rewrite Hfs in E.
    exists full. split; [apply ttrace_split; left; exact (texit_stepR_nstep (Some ok) t' mo full Hx)|]. rewrite E. exact Hp.
Qed.

Theorem prog_det :
  prog_no_enomem_stmt psegs pstage Plain.M.init_pc Plain.M.phdrs source_alloc_limit ->
  forall en inp,
    valid_entry (mkImage psegs Plain.M.init_pc Plain.M.phdrs) en inp ->
    valid_input_either inp ->
  forall t', resolves t' (the_prog psegs pstage inp en) ->
  forall tr, tree_traces t' (mo0 psegs source_alloc_limit en inp) tr
             <-> canonT (argv_Z (in_argv inp)) (in_fs inp) tr.
Proof. intros Hne. apply prog_det_gen; [apply segs_pu_P| exact Hne]. Qed.

Theorem prog_det_U :
  prog_no_enomem_stmt usegs ustage Ubsan.M.init_pc Ubsan.M.phdrs target_alloc_limit ->
  forall en inp,
    valid_entry (mkImage usegs Ubsan.M.init_pc Ubsan.M.phdrs) en inp ->
    valid_input_either inp ->
  forall t', resolves t' (the_prog usegs ustage inp en) ->
  forall tr, tree_traces t' (mo0 usegs target_alloc_limit en inp) tr
             <-> canonT (argv_Z (in_argv inp)) (in_fs inp) tr.
Proof. intros Hne. apply prog_det_gen; [apply segs_pu_U| exact Hne]. Qed.

Corollary trees_equiv_of_no_enomem :
  prog_no_enomem_stmt psegs pstage Plain.M.init_pc Plain.M.phdrs source_alloc_limit ->
  prog_no_enomem_stmt usegs ustage Ubsan.M.init_pc Ubsan.M.phdrs target_alloc_limit ->
  forall (enP enU : ExecEntry) (inp : ProcInput),
    valid_entry (mkImage psegs Plain.M.init_pc Plain.M.phdrs) enP inp ->
    valid_entry (mkImage usegs Ubsan.M.init_pc Ubsan.M.phdrs) enU inp ->
    valid_input_either inp ->
    forall tP tU, resolves tP (the_prog psegs pstage inp enP) -> resolves tU (the_prog usegs ustage inp enU) ->
    trace_equiv (tree_traces tP (mo0 psegs source_alloc_limit enP inp))
                (tree_traces tU (mo0 usegs target_alloc_limit enU inp)).
Proof.
  intros HP HU enP enU inp HvP HvU Hvi tP tU HrP HrU tr.
  rewrite (prog_det HP enP inp HvP Hvi tP HrP tr). rewrite (prog_det_U HU enU inp HvU Hvi tU HrU tr). reflexivity.
Qed.

