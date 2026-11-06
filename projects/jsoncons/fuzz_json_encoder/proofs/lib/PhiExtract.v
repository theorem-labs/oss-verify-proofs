(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit HaltsAllowed.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import ShapeAlg DivergeSim VmLimitFrame Scfg SpinAlg HaltsBridge.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section WithSegs.
Variable segs : list Segment.
Variable scfg : SpuriousCfg.

Definition has_exit (tr : list event) : Prop := exists code fs, In (ExitEv code fs) tr.

(* [comment removed for export] *)
Definition t_phi (T : TSet) (Phi : Prop) : TSet := fun tr => T tr /\ (has_exit tr -> Phi).

Lemma t_phi_sub : forall T Phi tr, t_phi T Phi tr -> T tr.
Proof. intros T Phi tr [H _]. exact H. Qed.

Lemma t_phi_eq : forall T (Phi : Prop), Phi -> t_eq (t_phi T Phi) T.
Proof. intros T Phi HPhi tr. split; [intros [H _]; exact H | intros H; split; [exact H | intros _; exact HPhi]]. Qed.

Lemma t_phi_intro : forall T (Phi : Prop) tr, T tr -> (has_exit tr -> Phi) -> t_phi T Phi tr.
Proof. intros T Phi tr H1 H2. split; assumption. Qed.

(* [comment removed for export] *)
Lemma t_phi_noexit : forall T (Phi : Prop) tr, T tr -> ~ has_exit tr -> t_phi T Phi tr.
Proof. intros T Phi tr H Hn. split; [exact H | intros He; exfalso; exact (Hn He)]. Qed.

Lemma codes_ok_phi : forall S T Phi, codes_ok S T -> codes_ok S (t_phi T Phi).
Proof. intros S T Phi H tr code fs [Htr _] Hin. exact (H tr code fs Htr Hin). Qed.

Lemma nokill_phi : forall T Phi, nokill T -> nokill (t_phi T Phi).
Proof. intros T Phi H tr sig fs [Htr _]. exact (H tr sig fs Htr). Qed.

(* [comment removed for export] *)
Lemma reaches_exit : forall S c,
  must_exit_in_at_cfg scfg segs S c ->
  m_halted (cfg_model c) = None ->
  exists tr code fs c',
    In code S /\ star_cfg segs scfg c (tr ++ [ExitEv code fs]) c' /\ m_halted (cfg_model c') = Some code.
Proof.
  intros S c Hme.
  induction Hme as [c code Hh Hin Hk | c Hnone Hprog Hnoerr Hnext IH]; intros Hrun.
  - congruence.
  - destruct Hprog as (evs & st & Hss). destruct st as [c1 |]; [| exfalso; exact (Hnoerr evs Hss)].
    pose proof (Hnext evs c1 Hss) as Hme1.
    destruct (m_halted (cfg_model c1)) as [k |] eqn:Hh1.
    + destruct (must_exit_in_at_cfg_halted_inv _ _ _ _ _ Hme1 Hh1) as (Hin1 & Hnk).
      destruct (sstep_cfg_next_halts_by_exit _ _ _ _ _ Hss)
        as [Hnone1 | [(evs0 & code0 & Hevs & Hcode0 & _) | (evs0 & sig & Hevs & Hsig)]]; [congruence | | congruence].
      assert (Hcc : code0 = k) by congruence. subst code0.
      exists evs0, k, (m_fs (cfg_model c1)), c1.
      split; [exact Hin1 | split; [| exact Hh1]].
      rewrite <- Hevs. rewrite <- (app_nil_r evs). eapply star_cfg_step; [exact Hss | apply star_cfg_refl].
    + destruct (IH evs c1 Hss Hh1) as (tr & code & fs & c' & Hin' & Hstar & Hh').
      exists (evs ++ tr), code, fs, c'.
      split; [exact Hin' | split; [| exact Hh']].
      rewrite <- app_assoc. eapply star_cfg_step; [exact Hss | exact Hstar].
Qed.

(* [comment removed for export] *)
Theorem phi_extract : forall S c T (Phi : Prop),
  srealizes segs scfg c (t_phi T Phi) ->
  Safe segs scfg c ->
  ~ spin_site_present segs ->
  m_halted (cfg_model c) = None ->
  codes_ok S T -> nokill T ->
  Phi.
Proof.
  intros S c T Phi Hsrz Hsafe Hns Hrun Hcodes Hnk.
  assert (Hme : must_exit_in_at_cfg scfg segs S c).
  { apply (srealizes_must_exit segs scfg S c (t_phi T Phi) Hsrz Hsafe Hns).
    - left. exact Hrun.
    - apply codes_ok_phi. exact Hcodes.
    - apply nokill_phi. exact Hnk. }
  destruct (reaches_exit S c Hme Hrun) as (tr & code & fs & c' & _ & Hstar & _).
  destruct (srealizes_star_only segs scfg c (t_phi T Phi) Hsrz Hsafe _ _ Hstar) as [_ HPhi].
  apply HPhi. exists code, fs. apply in_app_iff. right. left. reflexivity.
Qed.

(* [comment removed for export] *)
Corollary srealizes_of_phi : forall S c T (Phi : Prop),
  srealizes segs scfg c (t_phi T Phi) ->
  Safe segs scfg c -> ~ spin_site_present segs -> m_halted (cfg_model c) = None -> codes_ok S T -> nokill T ->
  Phi /\ srealizes segs scfg c T.
Proof.
  intros S c T Phi Hsrz Hsafe Hns Hrun Hcodes Hnk.
  pose proof (phi_extract S c T Phi Hsrz Hsafe Hns Hrun Hcodes Hnk) as HPhi.
  split; [exact HPhi |].
  eapply srz_conseq; [exact Hsrz | apply t_phi_eq; exact HPhi].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition has_halt_ev (tr : list event) : Prop := exists fs, (exists code, In (ExitEv code fs) tr) \/ (exists sig, In (KillEv sig fs) tr).

Definition guard_after (S : TSet) (t0 : list event) (Phi : Prop) : Prop := forall tr, S (t0 ++ tr) -> tr <> [] -> Phi.

Lemma is_prefix_split {A} : forall (l1 l2 : list A), is_prefix l1 l2 -> exists r, l2 = l1 ++ r.
Proof.
  induction l1 as [|x l1 IH]; intros l2 H.
  - exists l2. reflexivity.
  - destruct l2 as [|y l2]; cbn in H; [contradiction |]. destruct H as [-> H].
    destruct (IH l2 H) as [r ->]. exists r. reflexivity.
Qed.

Lemma must_exit_in_at_cfg_step : forall S c evs c',
  must_exit_in_at_cfg scfg segs S c -> sstep_cfg segs scfg c evs (SNext c') -> must_exit_in_at_cfg scfg segs S c'.
Proof.
  intros S c evs c' Hme Hss. destruct Hme as [c code Hh Hin Hk | c Hnone Hprog Hnoerr Hnext].
  - exfalso. pose proof (sstep_cfg_not_halted _ _ _ _ _ Hss). congruence.
  - exact (Hnext evs c' Hss).
Qed.

Lemma must_exit_in_at_cfg_star : forall S c tr c',
  must_exit_in_at_cfg scfg segs S c -> star_cfg segs scfg c tr c' -> must_exit_in_at_cfg scfg segs S c'.
Proof.
  intros S c tr c' Hme Hstar. induction Hstar as [c | c1 evs c2 tr2 c3 Hss Hstar IH].
  - exact Hme.
  - apply IH. eapply must_exit_in_at_cfg_step; [exact Hme | exact Hss].
Qed.

(* [comment removed for export] *)
Lemma star_into_halted_has_halt_ev : forall c tr c',
  star_cfg segs scfg c tr c' -> m_halted (cfg_model c) = None -> m_halted (cfg_model c') <> None -> has_halt_ev tr.
Proof.
  intros c tr c' Hstar. induction Hstar as [c | c1 evs c2 tr2 c3 Hss Hstar IH]; intros Hrun Hh.
  - congruence.
  - destruct (m_halted (cfg_model c2)) as [k|] eqn:Hh2.
    + destruct (sstep_cfg_next_halts_by_exit _ _ _ _ _ Hss) as [Hn | [(evs0 & code & He & _ & _) | (evs0 & sig & He & _)]]; [congruence | |].
      * exists (m_fs (cfg_model c2)). left. exists code. rewrite He. apply in_app_iff. left. apply in_app_iff. right. left. reflexivity.
      * exists (m_fs (cfg_model c2)). right. exists sig. rewrite He. apply in_app_iff. left. apply in_app_iff. right. left. reflexivity.
    + destruct (IH eq_refl Hh) as (fs & [(code & Hin) | (sig & Hin)]); exists fs; [left; exists code | right; exists sig]; apply in_app_iff; right; exact Hin.
Qed.

Theorem phi_extract_after : forall S c T t0 (Phi : Prop),
  srealizes segs scfg c T ->
  Safe segs scfg c ->
  ~ spin_site_present segs ->
  m_halted (cfg_model c) = None ->
  codes_ok S T -> nokill T ->
  T t0 -> ~ has_halt_ev t0 ->
  guard_after T t0 Phi ->
  Phi.
Proof.
  intros S c T t0 Phi Hsrz Hsafe Hns Hrun Hcodes Hnk Ht0 Hnoh G.
  pose proof (srealizes_must_exit segs scfg S c T Hsrz Hsafe Hns (or_introl Hrun) Hcodes Hnk) as Hme.
  destruct (srealizes_admits segs scfg c T Hsrz Hsafe t0 Ht0) as (tr' & c' & Hstar & Hpre).
  destruct (is_prefix_split t0 tr' Hpre) as [rest ->].
  pose proof (must_exit_in_at_cfg_star S c (t0 ++ rest) c' Hme Hstar) as Hme'.
  destruct (m_halted (cfg_model c')) as [k|] eqn:Hh'.
  - (* [comment removed for export] *)
    destruct rest as [|e rest'].
    + exfalso. apply Hnoh. rewrite app_nil_r in Hstar.
      apply (star_into_halted_has_halt_ev c t0 c' Hstar Hrun). congruence.
    + apply (G (e :: rest')); [| discriminate]. exact (srealizes_star_only segs scfg c T Hsrz Hsafe _ _ Hstar).
  - destruct (reaches_exit S c' Hme' Hh') as (u & code & fs & c'' & _ & Hstar2 & _).
    pose proof (star_cfg_trans segs scfg c (t0 ++ rest) c' (u ++ [ExitEv code fs]) c'' Hstar Hstar2) as Hall.
    rewrite <- app_assoc in Hall.
    apply (G (rest ++ (u ++ [ExitEv code fs]))).
    + exact (srealizes_star_only segs scfg c T Hsrz Hsafe _ _ Hall).
    + destruct rest; [destruct u; discriminate | discriminate].
Qed.
End WithSegs.
