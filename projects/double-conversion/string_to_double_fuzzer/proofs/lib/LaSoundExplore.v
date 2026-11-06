(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia Wellfounded.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import PropExec CatSim.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import LxLin LxOrder LxOrderWf.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import LaState LaMem LaStep LaCheck LaSem LaWf LaSoundVal LaSoundMem LaSoundMem2 LaSoundStep LaSoundMatch.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import LXL LAS LAM LAI LAC LASEM LAWF LASV LASM.
Open Scope Z_scope.

Module LASE.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma cuts_at_In : forall cs pc k j cp, In (j, cp) (cuts_at cs pc k) -> In cp cs /\ cp_pc cp = pc.
Proof.
  induction cs as [|c r IH]; intros pc k j cp H; [destruct H|]. cbn [cuts_at] in H.
  apply in_app_iff in H as [H|H].
  - destruct (Z.eqb_spec (cp_pc c) pc); [|destruct H]. destruct H as [H|[]]. injection H as _ <-. split; [left; reflexivity | assumption].
  - destruct (IH pc (S k) j cp H) as [H1 H2]. split; [right; exact H1 | exact H2].
Qed.

Lemma Forall_suffix : forall (A : Type) (P : A -> Prop) (l1 l2 : list A), Forall P (l1 ++ l2) -> Forall P l2.
Proof. intros A P l1 l2 H. apply Forall_app in H as [_ H]. exact H. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma explore_app : forall Un i start fuel forks st steps path acc,
  exists new, explore Un i start fuel forks st steps path acc = new ++ acc.
Proof.
  intros Un i start fuel. induction fuel as [|fuel IH]; intros forks st steps path acc.
  - eexists [_]. reflexivity.
  - cbn [explore].
    Ltac one := eexists [_]; reflexivity.
    Ltac two IH :=
      lazymatch goal with
      | |- exists new, explore _ _ _ _ ?k ?s ?n ?p (explore _ _ _ _ ?k2 ?s2 ?m2 ?p2 ?acc) = new ++ ?acc =>
          let l1 := fresh "l" in let E1 := fresh "E" in let l2 := fresh "l" in let E2 := fresh "E" in
          destruct (IH k2 s2 m2 p2 acc) as [l1 E1]; rewrite E1;
          destruct (IH k s n p (l1 ++ acc)) as [l2 E2]; rewrite E2; exists (l2 ++ l1); rewrite app_assoc; reflexivity
      end.
    Ltac go IH :=
      lazymatch goal with
      | |- exists new, ?l :: ?acc = new ++ ?acc => one
      | |- exists new, explore _ _ _ _ _ _ _ _ (explore _ _ _ _ _ _ _ _ _) = new ++ _ => two IH
      | |- exists new, explore _ _ _ _ ?k ?s ?n ?p ?acc = new ++ ?acc => exact (IH k s n p acc)
      | |- exists new, (match ?e with _ => _ end) = new ++ _ => destruct e; go IH
      end.
    destruct (wf_state st); cbn [negb]; [|one].
    destruct (ctx_contra (s_ctx st) None); [one|].
    destruct (match steps with O => None | S _ => _ end); [destruct (degrade_regs st all_xregs); one|].
    destruct (sum_at (un_sums Un) (s_pc st)) as [sk|].
    { destruct sk; try one;
      first [ destruct (apply_cbd (un_env Un) st) as [S'|]; [|one]
            | destruct (apply_malloc (un_env Un) st _) as [S'|]; [|one]
            | destruct (apply_memset (un_env Un) st) as [S'|]; [|one] ]; (destruct (wf_state S'); [apply IH | one]). }
    destruct (match dirs_at _ _ with [] => _ | _ => _ end) as [S1 | c S0 | w]; [ | | one].
    + destruct (LAI.step _ S1) as [S'|St Sf|S'|p r]; [apply IH | destruct forks; [one | two IH] | one | one].
    + destruct forks as [|forks']; [one|].
      destruct (wf_state (learn_cond S0 c true) &&& wf_state (learn_cond S0 c false))%bool; cbn [negb]; [|one].
      cbv beta.
      (* [comment removed for export] *)
      assert (ARM : forall (b : bool) (acc0 : list leaf), exists n1,
                 match LAI.step (un_env Un) (learn_cond S0 c b) with
                 | SNext S' => explore Un i start fuel forks' S' (S steps) (b :: path) acc0
                 | SFork S1 S2 =>
                     match forks' with
                     | O => LFail (s_pc st) (rev (b :: path)) R_FORKS (set_depth (learn_cond S0 c b) steps) :: acc0
                     | Datatypes.S forks'' =>
                         explore Un i start fuel forks'' S2 (if Z.eqb (s_pc S2) (s_pc st) then steps else S steps) (false :: b :: path)
                                 (explore Un i start fuel forks'' S1 (if Z.eqb (s_pc S1) (s_pc st) then steps else S steps) (true :: b :: path) acc0)
                     end
                 | SExit S' => LExit (rev (b :: path)) (exit_ok Un S') S' :: acc0
                 | SFail p r => LFail p (rev (b :: path)) r (learn_cond S0 c b) :: acc0
                 end = n1 ++ acc0).
      { intros b acc0. destruct (LAI.step _ (learn_cond S0 c b)) as [S'|S1 S2|S'|p r]; [apply IH | | one | one].
        destruct forks' as [|forks'']; [one | two IH]. }
      destruct (ARM true acc) as [n1 E1]. rewrite E1.
      destruct (ARM false (n1 ++ acc)) as [n2 E2]. rewrite E2.
      exists (n2 ++ n1). rewrite app_assoc. reflexivity.
Qed.

Lemma explore_suffix : forall Un i start fuel forks st steps path acc (P : leaf -> Prop),
  Forall P (explore Un i start fuel forks st steps path acc) -> Forall P acc.
Proof.
  intros. destruct (explore_app Un i start fuel forks st steps path acc) as [new E]. rewrite E in H.
  eapply Forall_suffix. exact H.
Qed.

(* [comment removed for export] *)
Lemma explore_ok_wf : forall Un i start fuel forks st steps path acc,
  Forall (fun l => leaf_ok l = true) (explore Un i start fuel forks st steps path acc) -> wf_state st = true.
Proof.
  intros Un i start fuel forks st steps path acc H. destruct fuel as [|fuel].
  - cbn [explore] in H. apply Forall_inv in H. discriminate.
  - cbn [explore] in H. destruct (wf_state st); [reflexivity|]. cbn [negb] in H. apply Forall_inv in H. discriminate.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section WithUnit.
  Variable Un : unitT.
  Variable G : sym -> Z.
  Variable M0 : word -> option byte.
  Variable FS : Z.
  Let U := un_env Un.
  Hypothesis UOK : uenv_ok U.
  Hypothesis SCOK : scells_ok U G M0.   (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition apply_sum (sk : sumkind) (S : astate) : option astate :=
    match sk with SumCBD => apply_cbd U S | SumMalloc k => apply_malloc U S k | SumMemset => apply_memset U S | _ => None end.
  Hypothesis SUM : forall sk rho S S' ms,
      wf_state S = true -> R U G FS M0 rho S ms -> apply_sum sk S = Some S' ->
      exists ms' rho', msteps (ue_segs U) ms ms' /\ R U G FS M0 rho' S' ms' /\ agree (s_next S) rho rho' /\ (s_next S <= s_next S')%nat.

  (* [comment removed for export] *)
  Definition reaches (rho0 : valuation) (start : cutpoint) (ms : machine_state) : Prop :=
    exists ms', msteps (ue_segs U) ms ms' /\
      ( (exists S rho', exit_ok Un S = true /\ R U G FS M0 rho' (set_pc S (rho' SYM_RA)) ms')
        \/ (exists cp rhoT, In cp (un_cuts Un) /\ R U G FS M0 rhoT (set_pc (cp_st cp) (cp_pc cp)) ms'
              /\ (un_total Un = true -> LXO.mu_lt (map (evl rhoT) (cp_mu cp)) (map (evl rho0) (cp_mu start)))) ).

  Lemma reaches_msteps : forall rho0 start ms ms',
    msteps (ue_segs U) ms ms' -> reaches rho0 start ms' -> reaches rho0 start ms.
  Proof.
    intros rho0 start ms ms' Hms (ms'' & Hms' & X). exists ms''. split; [eapply msteps_trans; [exact Hms | exact Hms'] | exact X].
  Qed.

  Lemma reaches_cstep : forall rho0 start rho st ms ms',
    R U G FS M0 rho st ms -> LASS.cstep U ms ms' -> reaches rho0 start ms' -> reaches rho0 start ms.
  Proof.
    intros rho0 start rho st ms ms' HR Hc Hr. eapply reaches_msteps; [|exact Hr].
    apply msteps_one; [exact (r_svc _ _ _ _ _ _ _ HR) | exact Hc].
  Qed.

  Lemma leaf_fail : forall (A : Prop) pc path r S acc,
    Forall (fun l => leaf_ok l = true) (LFail pc path r S :: acc) -> A.
  Proof. intros A pc path r S acc H. apply Forall_inv in H. discriminate. Qed.

  (* [comment removed for export] *)
  Lemma eval_operand_shape : forall S o v S', eval_operand S o = Some (v, S') ->
    S' = S /\ (wf_state S = true -> aval_below v (s_next S) = true).
  Proof.
    intros S o v S' H. destruct o as [r|z|off w]; cbn in H; try discriminate; injection H as <- <-.
    - split; [reflexivity|]. intros Hwf. apply LASS.getreg_below. exact Hwf.
    - split; [reflexivity|]. intros _. apply alit_below.
  Qed.

  Lemma mk_cond_shape : forall S k a b c, wf_state S = true -> mk_cond S k a b = Some c ->
    let '(n, k', x, y) := c in lin_below x (s_next S) = true /\ lin_below y (s_next S) = true.
  Proof.
    intros S k a b c Hwf H. unfold mk_cond in H.
    destruct (eval_operand S a) as [[va Sa]|] eqn:Ea; [|discriminate].
    destruct va as [|x|? ? ? ?|? ?]; try discriminate.
    destruct (eval_operand S b) as [[vb Sb]|] eqn:Eb; [|discriminate].
    destruct vb as [|y|? ? ? ?|? ?]; try discriminate.
    pose proof (proj2 (eval_operand_shape _ _ _ _ Ea) Hwf) as Bx. pose proof (proj2 (eval_operand_shape _ _ _ _ Eb) Hwf) as By.
    cbn in Bx, By.
    destruct k; [destruct (uexact _ _ &&& uexact _ _)%bool; [|discriminate] | destruct (sexact _ _ &&& sexact _ _)%bool; [|discriminate] |];
      injection H as <-; split; assumption.
  Qed.

  (* [comment removed for export] *)
  Lemma R_vext_same : forall rho st st' ms,
    R U G FS M0 rho st ms -> vext rho st rho st' -> VS rho st' -> s_next st' = s_next st -> R U G FS M0 rho st' ms.
  Proof.
    intros rho st st' ms HR (Ha & Hn & Hpc & Hregs & Hstk & Harrs & Habs & Hresv & Hdepth & Hpc' & Hpay & Hframes) [HC HB] Hnx.
    destruct HR; constructor; rewrite ?Hpc, ?Hregs, ?Hstk, ?Harrs, ?Habs, ?Hresv, ?Hpc', ?Hpay, ?Hnx, ?Hframes; try assumption.
    split; [exact HC | rewrite <- Hnx; exact HB].
  Qed.

  Lemma apply_dir_sound : forall rho S ms d,
    wf_state S = true -> R U G FS M0 rho S ms ->
    match apply_dir U S d with
    | DOk S' => R U G FS M0 rho S' ms /\ s_next S' = s_next S
    | DFork c S0 => S0 = S /\ (let '(n, k, x, y) := c in lin_below x (s_next S) = true /\ lin_below y (s_next S) = true)
    | DFail _ => True
    end.
  Proof.
    intros rho S ms d Hwf HR. pose proof (r_vs _ _ _ _ _ _ _ HR) as HVS.
    destruct d as [lo hi | i lo hi | k a b | k a b fk]; cbn [apply_dir].
    - destruct (sp_off S) as [k|]; [|exact I]. destruct (declare_array U S (k + lo) (k + hi)) as [S'|] eqn:E; [|exact I].
      destruct (LASM2.declare_array_sound U G M0 FS rho S ms _ _ S' Hwf HR E) as (HR' & Hn & _). split; [exact HR' | exact Hn].
    - destruct (declare_frame_array S i lo hi) as [S'|] eqn:E; [|exact I].
      destruct (LASM2.declare_frame_array_sound U G M0 FS rho S ms i _ _ S' Hwf HR E) as (HR' & Hn & _). split; [exact HR' | exact Hn].
    - destruct (mk_cond S k a b) as [c|] eqn:E; [|exact I]. split; [reflexivity|]. exact (mk_cond_shape S k a b c Hwf E).
    - destruct (mk_cond S k a b) as [[[[n k'] x] y]|] eqn:E; [|exact I].
      pose proof (mk_cond_shape S k a b _ Hwf E) as [Bx By]. cbv beta iota in Bx, By.
      assert (Bd : lin_below (lsub x y) (s_next S) = true) by (apply lsub_below; assumption).
      destruct k'.
      + destruct (entails (s_ctx S) (laddc (lsub y x) (-1)) (Some fk)) eqn:E1; [|exact I].
        pose proof (entails_sound rho _ _ _ (proj1 HVS) E1) as P.
        destruct (learn_sound rho S (laddc (lsub y x) (-1)) HVS ltac:(apply laddc_below; apply lsub_below; assumption) P) as [V1 V2].
        split; [eapply R_vext_same; [exact HR | exact V1 | exact V2 | reflexivity] | reflexivity].
      + destruct (entails (s_ctx S) (laddc (lsub y x) (-1)) (Some fk)) eqn:E1; [|exact I].
        pose proof (entails_sound rho _ _ _ (proj1 HVS) E1) as P.
        destruct (learn_sound rho S (laddc (lsub y x) (-1)) HVS ltac:(apply laddc_below; apply lsub_below; assumption) P) as [V1 V2].
        split; [eapply R_vext_same; [exact HR | exact V1 | exact V2 | reflexivity] | reflexivity].
      + destruct (entails (s_ctx S) (lsub x y) (Some fk) &&& entails (s_ctx S) (lneg (lsub x y)) (Some fk))%bool eqn:E1; [|exact I].
        apply andb_prop in E1 as [E1 E2].
        pose proof (entails_sound rho _ _ _ (proj1 HVS) E1) as P1. pose proof (entails_sound rho _ _ _ (proj1 HVS) E2) as P2.
        rewrite lneg_sound in P2.
        destruct (learn_eq_sound rho S (lsub x y) HVS Bd ltac:(lia)) as [V1 V2].
        split; [eapply R_vext_same; [exact HR | exact V1 | exact V2 | reflexivity] | reflexivity].
  Qed.

  Lemma apply_dirs_sound : forall ds rho S ms,
    wf_state S = true -> R U G FS M0 rho S ms ->
    match apply_dirs U S ds with
    | DOk S' => R U G FS M0 rho S' ms /\ s_next S' = s_next S /\ wf_state S' = true
    | DFork c S0 => R U G FS M0 rho S0 ms /\ s_next S0 = s_next S /\ wf_state S0 = true
                    /\ (let '(n, k, x, y) := c in lin_below x (s_next S0) = true /\ lin_below y (s_next S0) = true)
    | DFail _ => True
    end.
  Proof.
    induction ds as [|d r IH]; intros rho S ms Hwf HR; cbn [apply_dirs].
    - split; [exact HR|]. split; [reflexivity | exact Hwf].
    - pose proof (apply_dir_sound rho S ms d Hwf HR) as X.
      destruct (apply_dir U S d) as [S' | c S0 | w]; [| | exact I].
      + destruct X as [HR' Hn]. destruct (wf_state S') eqn:Hwf'; [|exact I].
        pose proof (IH rho S' ms Hwf' HR') as Y.
        destruct (apply_dirs U S' r) as [S'' | c S0 | w]; [| | exact I].
        * destruct Y as (Y1 & Y2 & Y3). split; [exact Y1|]. split; [congruence | exact Y3].
        * destruct Y as (Y1 & Y2 & Y3 & Y4). split; [exact Y1|]. split; [congruence|]. split; [exact Y3 | exact Y4].
      + destruct X as [-> Hc]. split; [exact HR|]. split; [reflexivity|]. split; [exact Hwf | exact Hc].
  Qed.

  (* [comment removed for export] *)
  Lemma fork_child_sound : forall rho S0 ms (c : cond),
    wf_state S0 = true -> R U G FS M0 rho S0 ms ->
    (let '(n, k, x, y) := c in lin_below x (s_next S0) = true /\ lin_below y (s_next S0) = true) ->
    exists b : bool, R U G FS M0 rho (learn_cond S0 c b) ms /\ s_next (learn_cond S0 c b) = s_next S0.
  Proof.
    intros rho S0 ms [[[n k] x] y] Hwf HR [Bx By].
    set (b := xorb n (cmp_holds rho k x y)). exists b.
    destruct (LASS.learn_cond_sound rho S0 (n, k, x, y) b (r_vs _ _ _ _ _ _ _ HR) ltac:(split; [exact Bx | split; [exact By | reflexivity]])) as [V1 V2].
    pose proof (LASS.s_next_learn_cond S0 (n, k, x, y) b) as Hn.
    split; [eapply R_vext_same; [exact HR | exact V1 | exact V2 | exact Hn] | exact Hn].
  Qed.

  (* [comment removed for export] *)
  Section Start.
    Variable i : nat.
    Variable start : cutpoint.
    Variable rho0 : valuation.
    Hypothesis TOKS : forallb (template_okb U) (un_cuts Un) = true.
    Hypothesis TOK0 : template_okb U start = true.
    Let n0 := s_next (cp_st start).

    Lemma mu_start_agree : forall rho, agree n0 rho0 rho -> map (evl rho) (cp_mu start) = map (evl rho0) (cp_mu start).
    Proof.
      intros rho Hag. pose proof TOK0 as T. unfold template_okb in T.
      apply andb_prop in T as [T _]. apply andb_prop in T as [_ Tmu].
      apply map_ext_in. intros m Hm. apply (evl_agree n0 rho0 rho); [|exact Hag].
      exact (proj1 (forallb_forall _ _) Tmu m Hm).
    Qed.

    Lemma explore_sound_ind : forall fuel forks st steps path acc rho ms,
      Forall (fun l => leaf_ok l = true) (explore Un i start fuel forks st steps path acc) ->
      R U G FS M0 rho st ms -> agree n0 rho0 rho -> (n0 <= s_next st)%nat ->
      reaches rho0 start ms.
    Proof.
      induction fuel as [|fuel IH]; intros forks st steps path acc rho ms HL HR Hag Hn0.
      { cbn [explore] in HL. eapply leaf_fail; exact HL. }
      pose proof (explore_ok_wf _ _ _ _ _ _ _ _ _ HL) as Hwf.
      cbn [explore] in HL. rewrite Hwf in HL. cbn [negb] in HL.
      (* [comment removed for export] *)
      destruct (ctx_contra (s_ctx st) None) eqn:Hcc.
      { exfalso. exact (ctx_contra_sound rho (s_ctx st) None (proj1 (r_vs _ _ _ _ _ _ _ HR)) Hcc). }
      (* [comment removed for export] *)
      destruct (match steps with O => None | S _ => _ end) as [cps|] eqn:Harr.
      { destruct (degrade_regs st all_xregs) as [st'|] eqn:Hdg; [|eapply leaf_fail; exact HL].
        destruct (LASS.degrade_regs_sound U G M0 FS all_xregs rho st ms st' LASS.all_xregs_range Hwf HR Hdg) as (rho1 & HR1 & Hag1 & Hn1 & Hwf1).
        apply Forall_inv in HL. cbn [leaf_ok] in HL. apply existsb_exists in HL as ([j rep] & Hin & Hrep). cbn [snd] in Hrep.
        destruct rep; [|discriminate].
        apply in_map_iff in Hin as ([j' cp] & Ejc & Hin). cbn in Ejc. injection Ejc as Ej Erep.
        assert (Hcuts : In cp (un_cuts Un) /\ cp_pc cp = s_pc st).
        { destruct steps; [discriminate|]. destruct (existsb (Z.eqb (s_pc st)) (un_stops Un)); [|discriminate].
          injection Harr as <-. eapply cuts_at_In. exact Hin. }
        destruct Hcuts as [Hcp _].
        pose proof (proj1 (forallb_forall _ _) TOKS cp Hcp) as TOKcp.
        assert (Erep' : match_report (un_total Un) st' cp (cp_mu start) (hint_for (cp_hints cp) i (rev path)) = []).
        { destruct (un_diag Un); [exact Erep | apply match_report_fast_empty; exact Erep]. }
        destruct (LASMT.match_sound U G M0 FS UOK (un_total Un) st' cp (cp_mu start) _ rho1 ms Hwf1 HR1 TOKcp Erep') as (rhoT & HRT & HMU).
        exists ms. split; [apply mst_refl|]. right. exists cp, rhoT. split; [exact Hcp|]. split; [exact HRT|].
        intros Htot. rewrite <- (mu_start_agree rho1 ltac:(eapply agree_trans; [exact Hn0 | exact Hag | exact Hag1])). exact (HMU Htot). }
      clear Harr.
      (* [comment removed for export] *)
      destruct (sum_at (un_sums Un) (s_pc st)) as [sk|].
      { assert (GEN : forall sk' S', apply_sum sk' st = Some S' ->
                  Forall (fun l => leaf_ok l = true) (if wf_state S' then explore Un i start fuel forks S' (S steps) path acc else LFail (s_pc st) (rev path) (R_SUMMARY 2) st :: acc) ->
                  reaches rho0 start ms).
        { intros sk' S' Hsum HL'. destruct (wf_state S') eqn:Hwf'; [|eapply leaf_fail; exact HL'].
          destruct (SUM sk' rho st S' ms Hwf HR Hsum) as (ms' & rho' & Hms & HR' & Hag' & Hn').
          eapply reaches_msteps; [exact Hms|].
          eapply (IH forks S' (S steps) path acc rho' ms' HL' HR'); [|lia].
          eapply agree_trans; [exact Hn0 | exact Hag | exact Hag']. }
        destruct sk as [| |k| |]; try (eapply leaf_fail; exact HL).
        - destruct (apply_cbd (un_env Un) st) as [S'|] eqn:Hsum; [exact (GEN SumCBD S' Hsum HL) | eapply leaf_fail; exact HL].
        - destruct (apply_malloc (un_env Un) st k) as [S'|] eqn:Hsum; [exact (GEN (SumMalloc k) S' Hsum HL) | eapply leaf_fail; exact HL].
        - destruct (apply_memset (un_env Un) st) as [S'|] eqn:Hsum; [exact (GEN SumMemset S' Hsum HL) | eapply leaf_fail; exact HL]. }
      (* [comment removed for export] *)
      remember (match dirs_at (un_dirs Un) (s_pc st) with
                | [] => DOk st
                | ds => match apply_dirs (un_env Un) st ds with
                        | DOk S1 => if wf_state S1 then DOk S1 else DFail 9
                        | other => other
                        end
                end) as r eqn:Hr.
      assert (DIRS : match r with
                     | DOk S1 => R U G FS M0 rho S1 ms /\ s_next S1 = s_next st /\ wf_state S1 = true
                     | DFork c S0 => R U G FS M0 rho S0 ms /\ s_next S0 = s_next st /\ wf_state S0 = true
                                     /\ (let '(n, k, x, y) := c in lin_below x (s_next S0) = true /\ lin_below y (s_next S0) = true)
                     | DFail _ => True
                     end).
      { destruct (dirs_at (un_dirs Un) (s_pc st)) as [|d ds].
        - subst r. split; [exact HR|]. split; [reflexivity | exact Hwf].
        - pose proof (apply_dirs_sound (d :: ds) rho st ms Hwf HR) as X. change U with (un_env Un) in X.
          destruct (apply_dirs (un_env Un) st (d :: ds)) as [S1 | c S0 | w]; subst r; [| exact X | exact I].
          destruct X as (X1 & X2 & X3). rewrite X3. split; [exact X1|]. split; [exact X2 | exact X3]. }
      clear Hr. destruct r as [S1 | c S0 | w].
      3:{ eapply leaf_fail; exact HL. }
      - (* [comment removed for export] *)
        destruct DIRS as (HR1 & Hn1 & Hwf1).
        pose proof (LASS.step_sound U G M0 FS UOK SCOK rho S1 ms Hwf1 HR1) as STEP. change U with (un_env Un) in STEP.
        destruct (LAI.step (un_env Un) S1) as [S'|St Sf|S'|p r'].
        + destruct STEP as (ms' & rho' & Hc & HR' & Hag' & Hn'). eapply reaches_cstep; [exact HR1 | exact Hc |].
          eapply (IH _ _ _ _ _ rho' ms' HL HR'); [|lia]. eapply agree_trans; [ | exact Hag | exact Hag']. lia.
        + destruct forks as [|forks']; [eapply leaf_fail; exact HL|].
          pose proof (explore_suffix _ _ _ _ _ _ _ _ _ _ HL) as HLt.
          destruct STEP as [(rho' & HRx & Hag' & Hn1' & Hn2') | (ms' & rho' & Hc & HRx & Hag' & Hn1' & Hn2')].
          * destruct HRx as [HRt | HRf].
            -- eapply (IH _ _ _ _ _ rho' ms HLt HRt); [|lia]. eapply agree_trans; [ | exact Hag | exact Hag']. lia.
            -- eapply (IH _ _ _ _ _ rho' ms HL HRf); [|lia]. eapply agree_trans; [ | exact Hag | exact Hag']. lia.
          * eapply reaches_cstep; [exact HR1 | exact Hc |]. destruct HRx as [HRt | HRf].
            -- eapply (IH _ _ _ _ _ rho' ms' HLt HRt); [|lia]. eapply agree_trans; [ | exact Hag | exact Hag']. lia.
            -- eapply (IH _ _ _ _ _ rho' ms' HL HRf); [|lia]. eapply agree_trans; [ | exact Hag | exact Hag']. lia.
        + destruct STEP as (ms' & Hc & HR' & Hn'). apply Forall_inv in HL. cbn [leaf_ok] in HL.
          eapply reaches_cstep; [exact HR1 | exact Hc |].
          exists ms'. split; [apply mst_refl|]. left. exists S', rho. split; [exact HL | exact HR'].
        + eapply leaf_fail; exact HL.
      - (* [comment removed for export] *)
        destruct DIRS as (HR0 & Hn0' & Hwf0 & Hc).
        destruct forks as [|forks']; [eapply leaf_fail; exact HL|].
        destruct (wf_state (learn_cond S0 c true)) eqn:Wt; [|cbn [negb] in HL; eapply leaf_fail; exact HL].
        destruct (wf_state (learn_cond S0 c false)) eqn:Wf; [|cbn [negb] in HL; eapply leaf_fail; exact HL].
        cbn [negb] in HL.
        destruct (fork_child_sound rho S0 ms c Hwf0 HR0 Hc) as (b & HRb & Hnb).
        assert (Hwfb : wf_state (learn_cond S0 c b) = true) by (destruct b; assumption).
        pose proof (LASS.step_sound U G M0 FS UOK SCOK rho _ ms Hwfb HRb) as STEP. change U with (un_env Un) in STEP.
        cbv beta in HL.
        (* [comment removed for export] *)
        assert (ARM : forall bb (accb : list leaf),
          Forall (fun l => leaf_ok l = true)
            (match LAI.step (un_env Un) (learn_cond S0 c bb) with
             | SNext S' => explore Un i start fuel forks' S' (S steps) (bb :: path) accb
             | SFork S1 S2 =>
                 match forks' with
                 | O => LFail (s_pc st) (rev (bb :: path)) R_FORKS (set_depth (learn_cond S0 c bb) steps) :: accb
                 | Datatypes.S forks'' =>
                     explore Un i start fuel forks'' S2 (if Z.eqb (s_pc S2) (s_pc st) then steps else S steps) (false :: bb :: path)
                             (explore Un i start fuel forks'' S1 (if Z.eqb (s_pc S1) (s_pc st) then steps else S steps) (true :: bb :: path) accb)
                 end
             | SExit S' => LExit (rev (bb :: path)) (exit_ok Un S') S' :: accb
             | SFail p r' => LFail p (rev (bb :: path)) r' (learn_cond S0 c bb) :: accb
             end) ->
          bb = b -> reaches rho0 start ms).
        { intros bb accb HLb ->.
          destruct (LAI.step (un_env Un) (learn_cond S0 c b)) as [S'|S1 S2|S'|p r'].
          * destruct STEP as (ms' & rho' & Hcs & HR' & Hag' & Hn'). eapply reaches_cstep; [exact HRb | exact Hcs |].
            eapply (IH _ _ _ _ _ rho' ms' HLb HR'); [|lia]. eapply agree_trans; [ | exact Hag | exact Hag']. lia.
          * destruct forks' as [|forks'']; [eapply leaf_fail; exact HLb|].
            pose proof (explore_suffix _ _ _ _ _ _ _ _ _ _ HLb) as HLt.
            destruct STEP as [(rho' & HRx & Hag' & Hn1' & Hn2') | (ms' & rho' & Hc' & HRx & Hag' & Hn1' & Hn2')].
            -- destruct HRx as [HRt | HRf].
               ++ eapply (IH _ _ _ _ _ rho' ms HLt HRt); [|lia]. eapply agree_trans; [ | exact Hag | exact Hag']. lia.
               ++ eapply (IH _ _ _ _ _ rho' ms HLb HRf); [|lia]. eapply agree_trans; [ | exact Hag | exact Hag']. lia.
            -- eapply reaches_cstep; [exact HRb | exact Hc' |]. destruct HRx as [HRt | HRf].
               ++ eapply (IH _ _ _ _ _ rho' ms' HLt HRt); [|lia]. eapply agree_trans; [ | exact Hag | exact Hag']. lia.
               ++ eapply (IH _ _ _ _ _ rho' ms' HLb HRf); [|lia]. eapply agree_trans; [ | exact Hag | exact Hag']. lia.
          * destruct STEP as (ms' & Hcs & HR' & Hn'). apply Forall_inv in HLb. cbn [leaf_ok] in HLb.
            eapply reaches_cstep; [exact HRb | exact Hcs |].
            exists ms'. split; [apply mst_refl|]. left. exists S', rho. split; [exact HLb | exact HR'].
          * eapply leaf_fail; exact HLb. }
        (* [comment removed for export] *)
        match type of HL with Forall _ ?whole =>
          match whole with
          | context [explore Un i start fuel forks' _ (S steps) (true :: path) acc] => idtac
          | _ => idtac
          end
        end.
        destruct b.
        + (* [comment removed for export] *)
          eapply (ARM true acc); [|reflexivity].
          destruct (LAI.step (un_env Un) (learn_cond S0 c false)) as [S'|S1 S2|S'|p r'].
          * eapply explore_suffix; exact HL.
          * destruct forks' as [|forks'']; [apply Forall_inv_tail in HL; exact HL|].
            eapply explore_suffix. eapply explore_suffix. exact HL.
          * apply Forall_inv_tail in HL; exact HL.
          * apply Forall_inv_tail in HL; exact HL.
        + (* [comment removed for export] *)
          eapply (ARM false); [exact HL | reflexivity].
    Qed.
  End Start.

  Theorem explore_sound : forall i start fuel forks st steps path acc rho0 rho ms,
    Forall (fun l => leaf_ok l = true) (explore Un i start fuel forks st steps path acc) ->
    forallb (template_okb U) (un_cuts Un) = true ->
    template_okb U start = true ->
    wf_state st = true -> R U G FS M0 rho st ms ->
    agree (s_next (cp_st start)) rho0 rho -> (s_next (cp_st start) <= s_next st)%nat ->
    reaches rho0 start ms.
  Proof.
    intros i start fuel forks st steps path acc rho0 rho ms HL TOKS TOK0 _ HR Hag Hn.
    exact (explore_sound_ind i start rho0 TOKS TOK0 fuel forks st steps path acc rho ms HL HR Hag Hn).
  Qed.

  (* [comment removed for export] *)
  Lemma run_cuts_ok : forall cps k,
    forallb (fun il : nat * list leaf => forallb leaf_ok (snd il)) (run_cuts Un k cps) = true ->
    forall cp, In cp cps -> exists j, Forall (fun l => leaf_ok l = true) (run_cut Un j cp).
  Proof.
    induction cps as [|c r IH]; intros k H cp Hin; [destruct Hin|]. cbn [run_cuts forallb snd] in H.
    apply andb_prop in H as [H1 H2]. destruct Hin as [<-|Hin]; [|exact (IH (S k) H2 cp Hin)].
    exists k. apply Forall_forall. intros x Hx. exact (proj1 (forallb_forall _ _) H1 x Hx).
  Qed.

  Theorem unit_sound : check_unit Un = true -> un_total Un = true ->
    forall rho ms, (exists cp, In cp (un_cuts Un) /\ R U G FS M0 rho (set_pc (cp_st cp) (cp_pc cp)) ms) ->
    exists ms' S rho', msteps (ue_segs U) ms ms' /\ exit_ok Un S = true /\ R U G FS M0 rho' (set_pc S (rho' SYM_RA)) ms'.
  Proof.
    intros CHK TOT rho ms (cp & Hcp & HR).
    unfold check_unit in CHK. apply andb_prop in CHK as [CHK RUN]. apply andb_prop in CHK as [_ TOKS].
    change (un_env Un) with U in TOKS, RUN.
    remember (map (evl rho) (cp_mu cp)) as m eqn:Hm.
    revert cp rho ms Hcp HR Hm.
    induction (LXOW.mu_lt_wf m) as [m _ IH]. intros cp rho ms Hcp HR Hm.
    destruct (run_cuts_ok (un_cuts Un) 0 RUN cp Hcp) as [j HL].
    pose proof (proj1 (forallb_forall _ _) TOKS cp Hcp) as TOK0.
    unfold run_cut in HL.
    assert (HRn : R U G FS M0 rho (norm_st (set_pc (cp_st cp) (cp_pc cp))) ms).
    { destruct HR as [Rglob Rpc Rsvc Rregs Rvs Rstk Rarrs Rwin Rpay Rabs Rresv Rfrm Rframe Rsp0 Ralign Rra Rdata].
      constructor; cbn; try assumption. destruct Rvs as [V1 V2]. split; [apply ctx_norm_sound; exact V1 | apply LAWF.ctx_norm_below; exact V2]. }
    destruct (explore_sound_ind j cp rho TOKS TOK0 _ _ _ _ _ _ rho ms HL HRn (agree_refl _ _) (Nat.le_refl _))
      as (ms' & Hms & [(S & rho' & HE & HR') | (cp' & rhoT & Hcp' & HR' & HMU)]).
    - exists ms', S, rho'. split; [exact Hms|]. split; [exact HE | exact HR'].
    - destruct (IH (map (evl rhoT) (cp_mu cp')) ltac:(subst m; exact (HMU TOT)) cp' rhoT ms' Hcp' HR' eq_refl)
        as (ms'' & S & rho'' & Hms' & HE & HR'').
      exists ms'', S, rho''. split; [eapply msteps_trans; [exact Hms | exact Hms'] |]. split; [exact HE | exact HR''].
  Qed.

End WithUnit.

End LASE.
