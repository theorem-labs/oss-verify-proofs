(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit HaltsAllowed.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.openssl.bndiv.lib.Lib Require Import PropExec MState Frame Exec ITree Nodes RegsEquiv ITreeHalts.
From OSSVerify.Proofs.openssl.bndiv.lib.AS Require ShapeHalts.
From OSSVerify.Proofs.openssl.bndiv.lib Require Import TopLevel Obligations ProofBaseG TopE TopSides TopSidesG.
From OSSVerify.Proofs.openssl.bndiv.lib.Spec Require Import Prelim Driver Prog ModelInv Unforced LibProg LibSafe LibOps ProgG ProgGSafe ProgGDet Canon CanonNoKill.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition codes02 : list word := [Z_to_bv 64 0; Z_to_bv 64 2].

(* [comment removed for export] *)
Lemma ctrace_of_code : forall argv fs ok, ct_code (ctrace_of argv fs ok) = 0 \/ ct_code (ctrace_of argv fs ok) = 2.
Proof.
  intros argv fs ok. unfold ctrace_of, file_trace.
  repeat match goal with
         | |- context [if ?b then _ else _] => destruct b
         | |- context [match ?x with OCFail => _ | OCDir => _ | OCFile _ => _ end] => destruct x
         end; cbn [ct_code]; auto.
Qed.

Lemma evw_no_exit : forall fd bs code fs, ~ In (ExitEv code fs) (evw fd bs).
Proof. intros fd bs code fs H. unfold evw in H. apply in_map_iff in H as (b & E & _). discriminate E. Qed.

Lemma canonT_exits02 : forall argv fs tr, canonT argv fs tr ->
  forall tr0 code fs', tr = tr0 ++ [ExitEv code fs'] -> In code codes02.
Proof.
  intros argv fs tr HT tr0 code fs' E. apply canonT_iff in HT as (ok & Hp).
  assert (Hin : In (ExitEv code fs') (ct_events fs (ctrace_of argv fs ok))).
  { apply (in_is_prefix (ExitEv code fs') tr _ Hp). rewrite E. apply in_or_app. right. left. reflexivity. }
  unfold ct_events in Hin. apply in_app_or in Hin as [Hin | [Hin | []]].
  - destruct (evw_no_exit _ _ _ _ Hin).
  - injection Hin as Hc _. subst code. unfold codes02.
    destruct (ctrace_of_code argv fs ok) as [-> | ->]; cbn; auto.
Qed.

(* [comment removed for export] *)
Lemma must_exit_in_at_cfg_eqv : forall segs cfg S c, must_exit_in_at_cfg cfg segs S c ->
  forall c', cfg_eqv c c' -> must_exit_in_at_cfg cfg segs S c'.
Proof.
  intros segs cfg S c H. induction H as [c code Hh Hin Hk | c Hnone (evs & st & Hss) Hnoerr _ IH]; intros c' He.
  - destruct He as [_ Hm]. apply (must_exit_in_at_cfg_halted cfg segs S c' code); [rewrite <- Hm; exact Hh | exact Hin | rewrite <- Hm; exact Hk].
  - apply must_exit_in_at_cfg_running.
    + destruct He as [_ Hm]. rewrite <- Hm. exact Hnone.
    + destruct (sstep_scfg_cfg_eqv segs cfg c c' evs st He Hss) as (X' & Hss' & _). exists evs, X'. exact Hss'.
    + intros evs' Herr.
      destruct (sstep_scfg_cfg_eqv segs cfg c' c evs' SError (cfg_eqv_sym _ _ He) Herr) as (X & HssX & HX).
      destruct X as [d|]; [destruct HX | exact (Hnoerr evs' HssX)].
    + intros evs' d' Hss'.
      destruct (sstep_scfg_cfg_eqv segs cfg c' c evs' (SNext d') (cfg_eqv_sym _ _ He) Hss') as (X & HssX & HX).
      destruct X as [d|]; [| destruct HX]. cbn in HX.
      exact (IH evs' d HssX d' (cfg_eqv_sym _ _ HX)).
Qed.

Section HaltsG.
Context {LM : LibModel}.
Variable P : Z -> Z.
Variable T : list Z.
Variables NBLK BSZ : Z.
Variable linv : LS -> list (bptr * Z) -> Prop.
Hypothesis HP0 : forall c, 0 <= P c.
Hypothesis HC : caps_ok P T NBLK BSZ.
Hypothesis H_init : lwf (okT T) lib_init [] (fun ls Li => linv ls [] /\ subms (map snd Li) T).
Hypothesis H_one : forall ls d X, linv ls X -> zlength d <= MAX_INPUT ->
  lwf (okB NBLK BSZ) (lib_one ls d) X (fun r X' => linv (fst r) X').
Hypothesis H_rc : forall ls d, lleaves (lib_one ls d) (fun r => snd r = 0).

Theorem G_must_exit_ncfg : forall segs pc ph rstage lim,
  image_low segs -> KLIM + SMALLREQ <= lim -> implG_stmt segs pc ph rstage ->
  forall en inp, valid_entry (mkImage segs pc ph) en inp -> valid_input_either inp ->
    must_exit_in_at_cfg ncfg segs codes02 (mkCfg (ms0 segs pc ph en inp) (mo0 segs lim en inp)).
Proof.
  intros segs pc ph rstage lim Hlow Hlim HI en inp He Hi.
  destruct (progG_model_ok_run P T NBLK BSZ linv HP0 HC H_init H_one H_rc segs rstage pc ph lim Hlow Hlim en inp He Hi) as [Hl Hs].
  pose proof (G_side P T NBLK BSZ linv HP0 HC H_init H_one H_rc segs pc ph rstage lim Hlow Hlim HI en inp He Hi) as [Htr _].
  apply (impl_must_exit node segs ncfg (at_node segs) nstep nexit minv nsafe (nodes_sound segs) codes02
           (the_progG segs rstage inp en) (epost the_post)).
  - split; [exact (HI en inp He Hi)|]. split; [exact Hl|]. split; [apply mo0_not_halted|]. split; [apply mo0_minv| exact Hs].
  - (* [comment removed for export] *)
    intros tr c' Hstar tr0 code fs E.
    apply (canonT_exits02 (argv_Z (in_argv inp)) (in_fs inp) tr) with (tr0 := tr0) (fs' := fs); [| exact E].
    apply Htr. rewrite run_scfg_eq. cbn [bh_traces].
    destruct (init_behaviour_scfg_eqv segs ncfg pc ph (en_sp en) (en_draw en) (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) (mo0 segs lim en inp))
      as (Ht & _).
    apply Ht. exists tr, c'. split; [exact Hstar | apply is_prefix_refl].
Qed.

Theorem G_must_exit : forall segs pc ph rstage lim,
  image_low segs -> KLIM + SMALLREQ <= lim -> implG_stmt segs pc ph rstage ->
  forall en inp, valid_entry (mkImage segs pc ph) en inp -> valid_input inp ->
    must_exit_in_scfg forced_only_cfg codes02 (mkImage segs pc ph) lim en inp.
Proof.
  intros segs pc ph rstage lim Hlow Hlim HI en inp He Hi.
  pose proof (G_must_exit_ncfg segs pc ph rstage lim Hlow Hlim HI en inp He (valid_input_either_of_valid_input _ Hi)) as H.
  destruct en as [sp brk mb rnd]. cbn [must_exit_in_scfg].
  apply (must_exit_in_at_cfg_mono forced_only_cfg ncfg segs codes02); [apply forced_only_cfg_least | apply ShapeHalts.decided_from_classic |].
  change (init_config segs pc ph sp brk mb rnd lim inp)
    with (mkCfg (init_machine_state segs pc ph sp rnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) (mo0 segs lim (mkEntry sp brk mb rnd) inp)).
  apply (must_exit_in_at_cfg_eqv segs ncfg codes02 _ H).
  split; [| reflexivity]. cbn [cfg_ms]. apply ms_eqv_sym. apply init_machine_state_eqv.
Qed.

(* [comment removed for export] *)
Corollary G_halts : forall segs pc ph rstage lim,
  image_low segs -> KLIM + SMALLREQ <= lim -> implG_stmt segs pc ph rstage ->
  halts_allowed_T_scfg_budgets forced_only_cfg lim codes02 (mkImage segs pc ph).
Proof. intros segs pc ph rstage lim Hlow Hlim HI en inp He Hi _. exact (G_must_exit segs pc ph rstage lim Hlow Hlim HI en inp He Hi). Qed.

End HaltsG.
