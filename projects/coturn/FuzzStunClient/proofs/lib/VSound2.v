(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool String Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import PropExec CatExec CatSim StoreOk.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import Frame.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import Hoare.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import VLinalg VState VLogic VGamma VAbs VAbsSound VStep VStepMem VStepSound VCert VItab VDriverMatch VContract VDriver VSound VState2 VStepMem2 VCert2 VContract2 VDriverMatch2 VDriver2 VGamma2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Unset Lia Cache.
#[local] Existing Instance PropExec.fx0.  (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma cstate2_wf_next cs : cstate2_wf_b cs = true -> (FIRST_FRESH2 <= cs_next (c1 cs))%positive /\ cstate_wf (c1 cs) = true.
Proof.
  intros H. destruct (cstate2_wf_parts _ H) as (H1 & H2 & _). auto.
Qed.

Lemma cstate2_ok_parts P cs :
  cstate2_ok P cs = true -> cstate_ok (p1 P) (c1 cs) = true /\ cstate2_wf_b cs = true /\ (globs_fcells_ok P cs && shadow_disp_ok P cs) = true.
Proof.
  unfold cstate2_ok. intros H. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2]. auto.
Qed.

Lemma load_cstate2_next P cs pc ctx : vs2_next (load_cstate2 P cs pc ctx) = cs_next (c1 cs).
Proof. reflexivity. Qed.

Lemma load_cstate2_pc P cs pc ctx : vs2_pc (load_cstate2 P cs pc ctx) = pc.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition unit_ret2 (U : vunit2) (E : venv2) : Z := unit_ret (u1 U) (ev1 E).

Section Core2.
  Variable SEGS : list Segment.
  Variable G : genv2.
  Variable rom : word -> option byte.

  Definition PU2 (U : vunit2) : vparams2 := unit_params2 G U.
  Definition gammaU2 (U : vunit2) (E : venv2) (mem0 : word -> option byte) := gamma2 SEGS (PU2 U) E mem0.
  Definition regionsU2 (U : vunit2) (E : venv2) : list (word * Z) := unit_regions2 (PU2 U) E.

  (* [comment removed for export] *)
  Definition exit_regs2 (U : vunit2) (nu : val) (regs' : bvmap 5 word) : Prop :=
    bv_unsigned (getr regs' 2%bv) = zwrap 64 (nu SP0 + u_sp (u1 U))
    /\ bv_unsigned (getr regs' 3%bv) = zwrap 64 (nu GP)
    /\ bv_unsigned (getr regs' 4%bv) = zwrap 64 (ge2_tp G)
    /\ (forall r i, In (r, i) sreg_idx -> bv_unsigned (getr regs' (Z_to_bv 5 r)) = zwrap 64 (nu (SREG i))).

  Lemma exit_regs2_ext U nu nu' regs' : ext FIRST_FRESH2 nu nu' -> exit_regs2 U nu' regs' -> exit_regs2 U nu regs'.
  Proof.
    intros X (H1&H2&H3&H4). unfold exit_regs2.
    rewrite <- (X SP0), <- (X GP) by (unfold SP0, GP, FIRST_FRESH2; lia).
    split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
    intros r i Hin. rewrite <- (X (SREG i)); [apply H4; exact Hin|].
    unfold sreg_idx in Hin. simpl in Hin. unfold SREG, FIRST_FRESH2.
    repeat (destruct Hin as [Hin|Hin]; [inversion Hin; subst; simpl; lia|]). destruct Hin.
  Qed.

  (* [comment removed for export] *)
  Definition fl_inv (U : vunit2) (E : venv2) (A : vstate2) (nu : val) (mem_e mem : word -> option byte) : Prop :=
    forall a, in_flags_zone (PU2 U) E a ->
      (~ In a (own_flags A nu) -> mem (wordZ a) = mem_e (wordZ a))
      /\ (In a (own_flags A nu) -> exists b, mem_e (wordZ a) = Some b /\ bv_unsigned b = 0).

  (* [comment removed for export] *)
  Definition gammaE (U : vunit2) (E : venv2) (mem0 mem_e : word -> option byte)
             (A : vstate2) (nu : val) (regs : bvmap 5 word) (mem : word -> option byte) : Prop :=
    gammaU2 U E mem0 A nu regs mem /\ fl_inv U E A nu mem_e mem.

  Lemma fl_inv_entry U E A nu mem : own_flags A nu = [] -> fl_inv U E A nu mem mem.
  Proof. intros H a Ha. rewrite H. split; [reflexivity|intros []]. Qed.

  Lemma fl_inv_step U E A A' nu nu' mem_e mem mem' :
    fl_inv U E A nu mem_e mem -> flags_step (PU2 U) E A A' nu nu' mem mem' -> fl_inv U E A' nu' mem_e mem'.
  Proof.
    intros HI HS a Ha. destruct (HI a Ha) as [I1 I2].
    destruct (HS a Ha) as [[EQV EQM]|[(IN' & NIN & Hb)|(IN & NIN' & Hb)]].
    - split.
      + intros N'. rewrite EQM. apply I1. intros IN. apply N'. apply EQV. exact IN.
      + intros IN'. apply I2. apply EQV. exact IN'.
    - split.
      + intros N'. exfalso. exact (N' IN').
      + intros _. rewrite <- (I1 NIN). exact Hb.
    - split.
      + intros _. destruct Hb as [b [Hb Hb0]]. destruct (I2 IN) as [b' [Hb' Hb0']]. rewrite Hb, Hb'.
        f_equal. apply bv_eq. rewrite Hb0, Hb0'. reflexivity.
      + intros IN'. exfalso. exact (NIN' IN').
  Qed.

  (* [comment removed for export] *)
  Lemma fl_inv_exit U E A nu mem_e mem :
    fl_inv U E A nu mem_e mem -> own_flags A nu = [] ->
    forall a, in_flags_zone (PU2 U) E a -> mem (wordZ a) = mem_e (wordZ a).
  Proof. intros HI H a Ha. apply (proj1 (HI a Ha)). rewrite H. intros []. Qed.

  Definition EXIT2 (U : vunit2) (E : venv2) (mem0 mem_e : word -> option byte)
             (nu : val) (mem : word -> option byte)
             (regs' : bvmap 5 word) (mem' : word -> option byte) : Prop :=
    exists X nu',
      In X (u2_exits U)
      /\ gammaE U E mem0 mem_e (load_cstate2 (PU2 U) X (unit_ret2 U E) []) nu' regs' mem'
      /\ ext FIRST_FRESH2 nu nu'
      /\ getr regs' 1%bv = wordZ (unit_ret2 U E)
      /\ exit_regs2 U nu regs'
      /\ frame_mod mem mem' (regionsU2 U E)
      /\ (forall a, in_flags_zone (PU2 U) E a -> mem' (wordZ a) = mem_e (wordZ a)).

  Definition unit_ok2 (U : vunit2) : Prop :=
    forall E mem0 nu regs mem,
      ret_ok (wordZ (unit_ret2 U E)) ->
      gammaU2 U E mem0 (load_cstate2 (PU2 U) (u2_pre U) (u_entry (u1 U)) []) nu regs mem ->
      exists regs' mem',
        msteps SEGS (mkst regs (wordZ (u_entry (u1 U))) mem rom) (mkst regs' (wordZ (unit_ret2 U E)) mem' rom)
        /\ EXIT2 U E mem0 mem nu mem regs' mem'.

  Definition CUT2 (U : vunit2) (E : venv2) (mem0 mem_e : word -> option byte) (Rstart : lin)
             (nu : val) (mem : word -> option byte)
             (regs' : bvmap 5 word) (pc' : word) (mem' : word -> option byte) : Prop :=
    exists c i X R nu',
      In c (u2_cuts U) /\ nth_error (cut2_states c) i = Some X /\ nth_error (cut2_ranks c) i = Some R
      /\ pc' = wordZ (cut2_pc c)
      /\ gammaE U E mem0 mem_e (load_cstate2 (PU2 U) X (cut2_pc c) (cut2_ctx c)) nu' regs' mem'
      /\ ext FIRST_FRESH2 nu nu'
      /\ eval nu' R <= eval nu Rstart - 1
      /\ frame_mod mem mem' (regionsU2 U E).

  Definition outcome2 (U : vunit2) (E : venv2) (mem0 mem_e : word -> option byte) (Rstart : lin)
             (nu : val) (regs : bvmap 5 word) (pc : word) (mem : word -> option byte) : Prop :=
    exists regs' pc' mem',
      msteps SEGS (mkst regs pc mem rom) (mkst regs' pc' mem' rom)
      /\ ((pc' = wordZ (unit_ret2 U E) /\ EXIT2 U E mem0 mem_e nu mem regs' mem')
          \/ CUT2 U E mem0 mem_e Rstart nu mem regs' pc' mem').

  Definition safe_state2 (U : vunit2) (E : venv2) (mem0 mem_e : word -> option byte) (Rstart : lin) (A : vstate2) : Prop :=
    forall nu regs (pc : word) mem,
      lin_below Rstart (vs2_next A) = true -> (FIRST_FRESH2 <= vs2_next A)%positive ->
      vs2_pc A = bv_unsigned pc ->
      gammaE U E mem0 mem_e A nu regs mem ->
      outcome2 U E mem0 mem_e Rstart nu regs pc mem.

  (* [comment removed for export] *)
  Definition dstep_post2 (U : vunit2) (E : venv2) (mem0 mem_e : word -> option byte)
             (A : vstate2) (succs : list vstate2) (nu : val) (regs : bvmap 5 word) (pc : word) (mem : word -> option byte) : Prop :=
    (exists regs' pc' mem' A' nu',
        msteps SEGS (mkst regs pc mem rom) (mkst regs' pc' mem' rom)
        /\ In A' succs /\ vs2_pc A' = bv_unsigned pc'
        /\ ext (vs2_next A) nu nu' /\ (vs2_next A <= vs2_next A')%positive
        /\ frame_mod mem mem' (regionsU2 U E)
        /\ gammaE U E mem0 mem_e A' nu' regs' mem')
    \/ (exists regs' mem',
        msteps SEGS (mkst regs pc mem rom) (mkst regs' (wordZ (unit_ret2 U E)) mem' rom)
        /\ EXIT2 U E mem0 mem_e nu mem regs' mem').

  (* [comment removed for export] *)
  Section Unit2.
    Variable done : list vunit2.
    Variable U : vunit2.
    Variable E : venv2.
    Variables mem0 mem_e : word -> option byte.
    Let D := mk_denv2 G done U.

    Hypothesis RANKS : ge2_ranks G = true.

    Hypothesis DS : forall A succs nu regs pc mem,
      dstep2 D A = SN2 succs ->
      (FIRST_FRESH2 <= vs2_next A)%positive ->
      vs2_pc A = bv_unsigned pc ->
      gammaE U E mem0 mem_e A nu regs mem ->
      dstep_post2 U E mem0 mem_e A succs nu regs pc mem.

    Hypothesis STATIC : unit_static_ok2 G (PU2 U) U = None.

    (* [comment removed for export] *)
    Hypothesis MATCH : forall A X pc ctx sigma nu regs mem,
      gammaU2 U E mem0 A nu regs mem ->
      cstate2_ok (PU2 U) X = true ->
      match_state2 isv_join2 no_skip false MM_cut pm_empty (load_cstate2 (PU2 U) X pc ctx) A = MOk sigma ->
      gammaU2 U E mem0 (load_cstate2 (PU2 U) X pc ctx) (vsubst nu sigma) regs mem /\ ext FIRST_FRESH2 nu (vsubst nu sigma)
      /\ (forall a, In a (own_flags (load_cstate2 (PU2 U) X pc ctx) (vsubst nu sigma)) <-> In a (own_flags A nu)).

    Lemma fl_inv_same A A' nu nu' mem :
      (forall a, In a (own_flags A' nu') <-> In a (own_flags A nu)) ->
      fl_inv U E A nu mem_e mem -> fl_inv U E A' nu' mem_e mem.
    Proof.
      intros EQ HI a Ha. destruct (HI a Ha) as [I1 I2]. split.
      - intros N. apply I1. intros IN. apply N. apply EQ. exact IN.
      - intros IN. apply I2. apply EQ. exact IN.
    Qed.

    Lemma static_facts2 :
      cstate2_ok (PU2 U) (u2_pre U) = true
      /\ (forall c, In c (u2_cuts U) -> pc_ok (cut2_pc c) = true /\ forall X, In X (cut2_states c) -> cstate2_ok (PU2 U) X = true)
      /\ pc_ok (u_entry (u1 U)) = true
      /\ (forall X, In X (u2_exits U) -> cstate2_ok (PU2 U) X = true)
      /\ (forall c, In c (u2_cuts U) -> length (cut2_ranks c) = length (cut2_states c) /\ rank_nonneg2 (PU2 U) c = true).
    Proof.
      unfold unit_static_ok2 in STATIC. rewrite RANKS in STATIC.
      destruct (cstate2_ok (PU2 U) (u2_pre U) && cstate2_iface_b (u2_pre U) && wrgn_ok U (u2_pre U)) eqn:C0; [|discriminate].
      destruct (pre_canonical2 G (PU2 U) U); [|discriminate].
      destruct (forallb (fun c => pc_ok (cut2_pc c) && forallb (fun cs => cstate2_ok (PU2 U) cs && wrgn_ok U cs) (cut2_states c)) (u2_cuts U)) eqn:C1; [|discriminate].
      destruct (pc_ok (u_entry (u1 U))); [|discriminate].
      destruct (forallb (fun cs => cstate2_ok (PU2 U) cs && cstate2_iface_b cs && wrgn_ok U cs) (u2_exits U)) eqn:C3; [|discriminate].
      cbn [negb andb] in STATIC.
      destruct (forallb (fun c => Nat.eqb (length (cut2_ranks c)) (length (cut2_states c)) && rank_nonneg2 (PU2 U) c) (u2_cuts U)) eqn:C2; [|discriminate].
      apply andb_prop in C0 as [C0 _]. apply andb_prop in C0 as [C0 _].
      split; [exact C0|]. split.
      { intros c Hc. rewrite forallb_forall in C1. specialize (C1 _ Hc). apply andb_prop in C1 as [A1 A2]. split; [exact A1|].
        intros X HX. rewrite forallb_forall in A2. specialize (A2 _ HX). apply andb_prop in A2 as [A2 _]. exact A2. }
      split; [reflexivity|]. split.
      { intros X HX. rewrite forallb_forall in C3. specialize (C3 _ HX). apply andb_prop in C3 as [C3 _]. apply andb_prop in C3 as [C3 _]. exact C3. }
      intros c Hc. rewrite forallb_forall in C2. specialize (C2 _ Hc). apply andb_prop in C2 as [A1 A2].
      apply Nat.eqb_eq in A1. auto.
    Qed.

    (* [comment removed for export] *)
    Lemma cuts_by_pc2_in : forall l m k cs c,
      pm_get k (cuts_by_pc2 l m) = Some cs -> In c cs ->
      In c l \/ (exists cs0, pm_get k m = Some cs0 /\ In c cs0).
    Proof.
      induction l as [|c0 t IH]; simpl; intros m k cs c Hg Hin; [right; eauto|].
      destruct (IH _ _ _ _ Hg Hin) as [H|[cs0 [Hg0 Hin0]]]; [auto|].
      rewrite pm_get_set in Hg0. destruct (Pos.eqb_spec k (zkey (cut2_pc c0))).
      - inversion Hg0; subst cs0. apply in_app_iff in Hin0 as [H|H]; [|simpl in H; destruct H as [H|H]; [auto|tauto]].
        right. destruct (pm_get (zkey (cut2_pc c0)) m) as [l'|] eqn:G0; [|destruct H]. exists l'. rewrite <- e in G0. auto.
      - right; eauto.
    Qed.

    Lemma find_cut2_spec pc ctx c :
      find_cut2 D pc ctx = Some c -> In c (u2_cuts U) /\ cut2_pc c = pc.
    Proof.
      unfold find_cut2. destruct (Z.ltb 0 pc); [|discriminate]. cbn [negb].
      unfold D, mk_denv2; cbn [de2_cuts].
      destruct (pm_get (zkey pc) (cuts_by_pc2 (u2_cuts U) pm_empty)) as [l|] eqn:G0; [|discriminate].
      intros Hf. apply find_some in Hf as [Hin Hb]. apply andb_prop in Hb as [Hb _]. apply Z.eqb_eq in Hb.
      destruct (cuts_by_pc2_in _ _ _ _ _ G0 Hin) as [H|[cs0 [H _]]]; [auto|].
      rewrite pm_get_empty in H. discriminate.
    Qed.

    Lemma try_disjuncts2_none Rstart A c : forall sts rks msgs,
      try_disjuncts2 D Rstart A c sts rks msgs = None ->
      exists i X R sigma,
        nth_error sts i = Some X /\ nth_error rks i = Some R
        /\ match_state2 isv_join2 no_skip false MM_cut pm_empty (load_cstate2 (PU2 U) X (cut2_pc c) (cut2_ctx c)) A = MOk sigma
        /\ qge (v1 A) (lsub Rstart (lsubst sigma R)) 1 = true.
    Proof.
      induction sts as [|X t IH]; intros rks msgs H; cbn [try_disjuncts2] in H; [discriminate|].
      change (de2_P D) with (PU2 U) in H. change (de2_G D) with G in H.
      assert (STEP : forall rks' msgs', try_disjuncts2 D Rstart A c t rks' msgs' = None ->
                     rks' = match rks with _ :: r' => r' | [] => [] end ->
                     exists i X0 R sigma, nth_error (X :: t) i = Some X0 /\ nth_error rks i = Some R /\
                       match_state2 isv_join2 no_skip false MM_cut pm_empty (load_cstate2 (PU2 U) X0 (cut2_pc c) (cut2_ctx c)) A = MOk sigma /\
                       qge (v1 A) (lsub Rstart (lsubst sigma R)) 1 = true).
      { intros rks' msgs' H' ->. destruct (IH _ _ H') as (i & X0 & R & sigma & N1 & N2 & M & Q).
        exists (S i), X0, R, sigma. simpl. destruct rks as [|r0 r']; [destruct i; discriminate|]. auto. }
      destruct (prematch2 X A); cbn [negb] in H; [|eapply STEP; [exact H|reflexivity]].
      destruct (match_state2 isv_join2 no_skip false MM_cut pm_empty (load_cstate2 (PU2 U) X (cut2_pc c) (cut2_ctx c)) A) as [sigma|m] eqn:M.
      - rewrite RANKS in H.
        destruct rks as [|r rks'].
        + eapply STEP; [exact H|reflexivity].
        + destruct (qge (v1 A) (lsub Rstart (lsubst sigma r)) 1) eqn:Q.
          * exists O, X, r, sigma. simpl. auto.
          * eapply STEP; [exact H|reflexivity].
      - eapply STEP; [exact H|reflexivity].
    Qed.

    Lemma cut_states_ok c X : In c (u2_cuts U) -> In X (cut2_states c) -> cstate2_ok (PU2 U) X = true.
    Proof. intros Hc HX. exact (proj2 (proj1 (proj2 static_facts2) c Hc) X HX). Qed.

    Lemma gamma2_lgamma A nu regs mem : gammaU2 U E mem0 A nu regs mem -> lgamma (v1 A) nu.
    Proof. intros H. apply gamma2_v1 in H. exact (gamma_lgamma _ _ _ _ _ _ _ _ H). Qed.

    (* [comment removed for export] *)
    Lemma arrival_sound Rstart A c nu regs pc mem i X R sigma :
      find_cut2 D (vs2_pc A) (vs_ctx (v1 A)) = Some c ->
      nth_error (cut2_states c) i = Some X -> nth_error (cut2_ranks c) i = Some R ->
      match_state2 isv_join2 no_skip false MM_cut pm_empty (load_cstate2 (PU2 U) X (cut2_pc c) (cut2_ctx c)) A = MOk sigma ->
      qge (v1 A) (lsub Rstart (lsubst sigma R)) 1 = true ->
      vs2_pc A = bv_unsigned pc ->
      gammaE U E mem0 mem_e A nu regs mem ->
      outcome2 U E mem0 mem_e Rstart nu regs pc mem.
    Proof.
      intros Hf N1 N2 M Q Hpc [HGm HFI].
      destruct (find_cut2_spec _ _ _ Hf) as [Hin Hpc'].
      assert (HX : cstate2_ok (PU2 U) X = true) by (eapply cut_states_ok; [exact Hin|eapply nth_error_In; eauto]).
      destruct (MATCH _ _ _ _ _ _ _ _ HGm HX M) as (HG' & EXT & OWN).
      exists regs, pc, mem. split; [apply mst_refl|]. right.
      exists c, i, X, R, (vsubst nu sigma).
      split; [exact Hin|]. split; [exact N1|]. split; [exact N2|]. split.
      { rewrite Hpc', Hpc. unfold wordZ. symmetry. apply Z_to_bv_bv_unsigned. }
      split; [split; [exact HG'|eapply fl_inv_same; [exact OWN|exact HFI]]|]. split; [exact EXT|]. split.
      { pose proof (qge_sound (v1 A) nu _ _ (gamma2_lgamma _ _ _ _ HGm) Q) as HQ.
        rewrite eval_lsub, eval_lsubst in HQ. lia. }
      apply frame_mod_refl.
    Qed.

    Lemma cut_arrival2_sound Rstart A c nu regs pc mem :
      find_cut2 D (vs2_pc A) (vs_ctx (v1 A)) = Some c ->
      cut_arrival2 D Rstart A c = SN2 [] ->
      vs2_pc A = bv_unsigned pc ->
      gammaE U E mem0 mem_e A nu regs mem ->
      outcome2 U E mem0 mem_e Rstart nu regs pc mem.
    Proof.
      intros Hf Hc Hpc HG.
      unfold cut_arrival2 in Hc.
      destruct (try_disjuncts2 D Rstart A c (cut2_states c) (cut2_ranks c) []) as [msgs|] eqn:T; [discriminate|].
      destruct (try_disjuncts2_none _ _ _ _ _ _ T) as (i & X & R & sigma & N1 & N2 & M & Q).
      exact (arrival_sound Rstart A c nu regs pc mem i X R sigma Hf N1 N2 M Q Hpc HG).
    Qed.

    Lemma pick2_nth : forall sts rks h X R, pick2 sts rks h = Some (X, R) ->
      exists i, nth_error sts i = Some X /\ nth_error rks i = Some R.
    Proof.
      induction sts as [|X0 t IH]; intros rks h X R H; [discriminate|].
      destruct rks as [|r rt]; [discriminate|]. cbn [pick2] in H.
      destruct (Z.eqb h 0).
      - injection H as <- <-. exists O. auto.
      - destruct (IH _ _ _ _ H) as [i [H1 H2]]. exists (S i). auto.
    Qed.

    Lemma try_hint2_true Rstart A c h :
      try_hint2 D Rstart A c h = true ->
      exists i X R sigma,
        nth_error (cut2_states c) i = Some X /\ nth_error (cut2_ranks c) i = Some R
        /\ match_state2 isv_join2 no_skip false MM_cut pm_empty (load_cstate2 (PU2 U) X (cut2_pc c) (cut2_ctx c)) A = MOk sigma
        /\ qge (v1 A) (lsub Rstart (lsubst sigma R)) 1 = true.
    Proof.
      unfold try_hint2. change (de2_P D) with (PU2 U). change (de2_G D) with G. rewrite RANKS.
      destruct (pick2 (cut2_states c) (cut2_ranks c) h) as [[X R]|] eqn:P; [|discriminate].
      destruct (match_state2 isv_join2 no_skip false MM_cut pm_empty (load_cstate2 (PU2 U) X (cut2_pc c) (cut2_ctx c)) A) as [sigma|m] eqn:M; [|discriminate].
      intros Q. destruct (pick2_nth _ _ _ _ _ P) as [i [N1 N2]]. exists i, X, R, sigma. auto.
    Qed.

    Lemma cut_arrival2h_nil Rstart A c tape l : cut_arrival2h D Rstart A c tape = SN2 l -> l = [].
    Proof.
      unfold cut_arrival2h, cut_arrival2.
      destruct tape as [|h t]; [|destruct (try_hint2 D Rstart A c h); [intros H; injection H as <-; reflexivity|]];
        destruct (try_disjuncts2 _ _ _ _ _ _ _); congruence.
    Qed.

    Lemma cut_arrival2h_sound Rstart A c tape nu regs pc mem :
      find_cut2 D (vs2_pc A) (vs_ctx (v1 A)) = Some c ->
      cut_arrival2h D Rstart A c tape = SN2 [] ->
      vs2_pc A = bv_unsigned pc ->
      gammaE U E mem0 mem_e A nu regs mem ->
      outcome2 U E mem0 mem_e Rstart nu regs pc mem.
    Proof.
      intros Hf Hc Hpc HG. unfold cut_arrival2h in Hc.
      destruct tape as [|h t]; [exact (cut_arrival2_sound _ _ _ _ _ _ _ Hf Hc Hpc HG)|].
      destruct (try_hint2 D Rstart A c h) eqn:TH; [|exact (cut_arrival2_sound _ _ _ _ _ _ _ Hf Hc Hpc HG)].
      destruct (try_hint2_true _ _ _ _ TH) as (i & X & R & sigma & N1 & N2 & M & Q).
      exact (arrival_sound Rstart A c nu regs pc mem i X R sigma Hf N1 N2 M Q Hpc HG).
    Qed.

    Lemma outcome2_after A A' Rstart nu nu' regs regs1 pc pc1 mem mem1 :
      lin_below Rstart (vs2_next A) = true -> (FIRST_FRESH2 <= vs2_next A)%positive ->
      msteps SEGS (mkst regs pc mem rom) (mkst regs1 pc1 mem1 rom) ->
      ext (vs2_next A) nu nu' -> (vs2_next A <= vs2_next A')%positive ->
      frame_mod mem mem1 (regionsU2 U E) ->
      outcome2 U E mem0 mem_e Rstart nu' regs1 pc1 mem1 ->
      outcome2 U E mem0 mem_e Rstart nu regs pc mem.
    Proof.
      intros HR HJ Hms Hext Hle Hfm (regs' & pc' & mem' & Hms' & Hout).
      exists regs', pc', mem'. split; [eapply msteps_trans; eauto|].
      destruct Hout as [[Hpc (X & nu'' & HX & HG & Hext' & Hra & Hxr & Hfm' & Hfl')]
                       |(c & i & X & R & nu'' & Hc & HX & HRk & Hpc & HG & Hext' & Hlt & Hfm')].
      - left. split; auto. exists X, nu''. split; [exact HX|]. split; [exact HG|]. split; [|split; [exact Hra|split; [|split]]].
        + eapply (ext_trans FIRST_FRESH2 FIRST_FRESH2); [lia | eapply ext_mono; [exact HJ|exact Hext] | exact Hext'].
        + eapply exit_regs2_ext; [eapply ext_mono; [exact HJ|exact Hext]|exact Hxr].
        + eapply frame_mod_trans_same; eauto.
        + exact Hfl'.
      - right. exists c, i, X, R, nu''. split; [exact Hc|]. split; [exact HX|]. split; [exact HRk|]. split; [exact Hpc|].
        split; [exact HG|]. split; [|split].
        + eapply (ext_trans FIRST_FRESH2 FIRST_FRESH2); [lia | eapply ext_mono; [exact HJ|exact Hext] | exact Hext'].
        + rewrite <- (eval_ext_below _ _ _ _ Hext HR). exact Hlt.
        + eapply frame_mod_trans_same; eauto.
    Qed.

    Theorem explore2_sound : forall fuel origin Rstart work tape,
      explore2 D fuel origin Rstart work tape = R2Ok ->
      forall first A, In (first, A) work ->
        safe_state2 U E mem0 mem_e Rstart A.
    Proof.
      induction fuel as [|f IH]; intros origin Rstart work tape Hx first A Hin.
      - simpl in Hx. destruct work as [|[b B] t]; [destruct Hin|discriminate].
      - simpl in Hx. destruct work as [|[b B] t]; [destruct Hin|].
        destruct Hin as [Hin|Hin].
        + inversion Hin; subst b B.
          destruct (if first then None else find_cut2 D (vs2_pc A) (vs_ctx (v1 A))) as [c|] eqn:Fc.
          * destruct (cut_arrival2h D Rstart A c tape) as [l|m] eqn:Ca; [|discriminate].
            intros nu regs pc mem HR HJ Hpc HG.
            destruct first; [discriminate|].
            pose proof (cut_arrival2h_nil _ _ _ _ _ Ca) as L. subst l.
            eapply cut_arrival2h_sound; eauto.
          * destruct (dstep2 D A) as [succs|m] eqn:St; [|discriminate].
            intros nu regs pc mem HR HJ Hpc HG.
            destruct (DS _ _ _ _ _ _ St HJ Hpc HG)
              as [(regs1 & pc1 & mem1 & A' & nu' & Hms & Hin' & Hpc' & Hext & Hle & Hfm & HG')|(regs' & mem' & Hms & HEX)].
            -- eapply outcome2_after; eauto.
               eapply (IH _ _ _ _ Hx false A'); auto.
               ++ apply in_app_iff. left. apply in_map_iff. exists A'; auto.
               ++ eapply lin_below_mono; eauto.
               ++ lia.
            -- exists regs', (wordZ (unit_ret2 U E)), mem'. split; auto.
        + destruct (if b then None else find_cut2 D (vs2_pc B) (vs_ctx (v1 B))) as [c|].
          * destruct (cut_arrival2h D Rstart B c tape); [|discriminate]. eapply IH; eauto.
          * destruct (dstep2 D B); [|discriminate]. eapply IH; eauto. apply in_app_iff; right; eauto.
    Qed.

    Lemma rank_facts2 c i X R :
      In c (u2_cuts U) -> nth_error (cut2_states c) i = Some X -> nth_error (cut2_ranks c) i = Some R ->
      qge (v1 (load_cstate2 (PU2 U) X (cut2_pc c) (cut2_ctx c))) R 0 = true /\ lin_below R (cs_next (c1 X)) = true.
    Proof.
      intros Hc HX HR. destruct (proj2 (proj2 (proj2 (proj2 static_facts2))) c Hc) as [Hlen Hnn].
      unfold rank_nonneg2 in Hnn. rewrite forallb_forall in Hnn.
      assert (Hin : In (X, R) (combine (cut2_states c) (cut2_ranks c))).
      { revert HX HR. clear. revert i. generalize (cut2_ranks c) as rks. generalize (cut2_states c) as sts.
        induction sts as [|x t IH]; intros rks [|i] HX HR; simpl in *; try discriminate.
        - inversion HX; subst. destruct rks; [discriminate|]. inversion HR; subst. simpl; auto.
        - destruct rks; [discriminate|]. simpl. right. eapply IH; eauto. }
      specialize (Hnn _ Hin). cbn beta in Hnn. apply andb_prop in Hnn as [A1 A2]. auto.
    Qed.

    Lemma check_cut_states2_ok fuel c : forall sts rks tps,
      check_cut_states2 D fuel c sts rks tps = R2Ok ->
      forall i X R, nth_error sts i = Some X -> nth_error rks i = Some R ->
        exists T, explore2 D fuel "cut" R [(true, load_cstate2 (PU2 U) X (cut2_pc c) (cut2_ctx c))] T = R2Ok.
    Proof.
      induction sts as [|X t IH]; intros rks tps H i X0 R HX HR; cbn [check_cut_states2] in H; [destruct i; discriminate|].
      change (de2_P D) with (PU2 U) in H.
      destruct rks as [|r rks']; [destruct i; discriminate|].
      destruct (explore2 D fuel "cut" r [(true, load_cstate2 (PU2 U) X (cut2_pc c) (cut2_ctx c))]
                  (match tps with p :: _ => p | [] => [] end)) eqn:Ex; [|discriminate].
      destruct i as [|i]; simpl in *.
      - inversion HX; inversion HR; subst. eexists; exact Ex.
      - eapply IH; eauto.
    Qed.

    Lemma check_cuts2_ok fuel : forall l,
      check_cuts2 D fuel l = R2Ok ->
      forall c i X R, In c l -> nth_error (cut2_states c) i = Some X -> nth_error (cut2_ranks c) i = Some R ->
        exists T, explore2 D fuel "cut" R [(true, load_cstate2 (PU2 U) X (cut2_pc c) (cut2_ctx c))] T = R2Ok.
    Proof.
      induction l as [|c0 t IH]; simpl; intros H c i X R Hin HX HR; [destruct Hin|].
      destruct (check_cut_states2 D fuel c0 (cut2_states c0) (cut2_ranks c0) (cut2_tapes c0)) eqn:E0; [|discriminate].
      destruct Hin as [<-|Hin]; [eapply check_cut_states2_ok; eauto| eapply IH; eauto].
    Qed.

    Section Reach2.
      Variable fuel : nat.
      Hypothesis CUTS : check_cuts2 D fuel (u2_cuts U) = R2Ok.

      Lemma cuts_reach2 : forall n c i X R nu regs mem,
        In c (u2_cuts U) -> nth_error (cut2_states c) i = Some X -> nth_error (cut2_ranks c) i = Some R ->
        gammaE U E mem0 mem_e (load_cstate2 (PU2 U) X (cut2_pc c) (cut2_ctx c)) nu regs mem ->
        (Z.to_nat (eval nu R) < n)%nat ->
        exists regs' mem',
          msteps SEGS (mkst regs (wordZ (cut2_pc c)) mem rom) (mkst regs' (wordZ (unit_ret2 U E)) mem' rom)
          /\ EXIT2 U E mem0 mem_e nu mem regs' mem'.
      Proof.
        induction n as [|n IH]; intros c i X R nu regs mem Hc HX HR HG Hn; [lia|].
        destruct (check_cuts2_ok _ _ CUTS _ _ _ _ Hc HX HR) as [T Ex].
        destruct (rank_facts2 _ _ _ _ Hc HX HR) as [Q B].
        pose proof (cut_states_ok _ _ Hc (nth_error_In _ _ HX)) as XOK.
        destruct (cstate2_ok_parts _ _ XOK) as (_ & XWF & _). destruct (cstate2_wf_next _ XWF) as [J0 _].
        assert (SAFE : safe_state2 U E mem0 mem_e R (load_cstate2 (PU2 U) X (cut2_pc c) (cut2_ctx c))).
        { eapply explore2_sound; eauto. simpl; auto. }
        destruct (SAFE nu regs (wordZ (cut2_pc c)) mem) as (regs1 & pc1 & mem1 & Hms & Hout); auto.
        { cbn. symmetry. apply pc_ok_u. apply (proj1 (proj1 (proj2 static_facts2) c Hc)). }
        destruct Hout as [[-> HEX]|(c' & i' & X' & R' & nu' & Hc' & HX' & HR' & -> & HG' & EXT & LT & FM)].
        - exists regs1, mem1. auto.
        - destruct (rank_facts2 _ _ _ _ Hc' HX' HR') as [Q' _].
          pose proof (qge_sound _ nu' _ _ (gamma2_lgamma _ _ _ _ (proj1 HG')) Q') as NN.
          destruct (IH c' i' X' R' nu' regs1 mem1 Hc' HX' HR' HG') as (regs' & mem' & Hms' & HEX'); [lia|].
          exists regs', mem'. split; [eapply msteps_trans; eauto|].
          destruct HEX' as (Xe & nu'' & HXe & HGe & EXT' & Hra & Hxr & FM' & FL').
          exists Xe, nu''. split; [exact HXe|]. split; [exact HGe|]. split.
          { eapply (ext_trans FIRST_FRESH2 FIRST_FRESH2); [lia|exact EXT|exact EXT']. }
          split; [exact Hra|]. split; [eapply exit_regs2_ext; eauto|].
          split; [eapply frame_mod_trans_same; eauto|exact FL'].
      Qed.
    End Reach2.

    Theorem check_unit2_sound_E nu regs mem :
      check_unit2 G done U = R2Ok ->
      gammaE U E mem0 mem_e (load_cstate2 (PU2 U) (u2_pre U) (u_entry (u1 U)) []) nu regs mem ->
      exists regs' mem',
        msteps SEGS (mkst regs (wordZ (u_entry (u1 U))) mem rom) (mkst regs' (wordZ (unit_ret2 U E)) mem' rom)
        /\ EXIT2 U E mem0 mem_e nu mem regs' mem'.
    Proof.
      unfold check_unit2. fold D. change (de2_P D) with (PU2 U). rewrite STATIC.
      destruct (explore2 D (N.to_nat (u_fuel (u1 U))) "entry" RANK_TOP [(true, load_cstate2 (PU2 U) (u2_pre U) (u_entry (u1 U)) [])] (u2_tape U)) eqn:Ex; try discriminate.
      intros CUTS HG.
      destruct (cstate2_ok_parts _ _ (proj1 static_facts2)) as (_ & PWF & _). destruct (cstate2_wf_next _ PWF) as [J0 _].
      assert (SAFE : safe_state2 U E mem0 mem_e RANK_TOP (load_cstate2 (PU2 U) (u2_pre U) (u_entry (u1 U)) [])).
      { eapply explore2_sound; eauto. simpl; auto. }
      destruct (SAFE nu regs (wordZ (u_entry (u1 U))) mem) as (regs1 & pc1 & mem1 & Hms & Hout); auto.
      { cbn. symmetry. apply pc_ok_u. apply (proj1 (proj2 (proj2 static_facts2))). }
      destruct Hout as [[-> HEX]|(c' & i' & X' & R' & nu' & Hc' & HX' & HR' & -> & HG' & EXT & LT & FM)].
      - exists regs1, mem1. auto.
      - destruct (cuts_reach2 _ CUTS (S (Z.to_nat (eval nu' R'))) c' i' X' R' nu' regs1 mem1 Hc' HX' HR' HG')
          as (regs' & mem' & Hms' & HEX'); [lia|].
        exists regs', mem'. split; [eapply msteps_trans; eauto|].
        destruct HEX' as (Xe & nu'' & HXe & HGe & EXT' & Hra & Hxr & FM' & FL').
        exists Xe, nu''. split; [exact HXe|]. split; [exact HGe|]. split.
        { eapply (ext_trans FIRST_FRESH2 FIRST_FRESH2); [lia|exact EXT|exact EXT']. }
        split; [exact Hra|]. split; [eapply exit_regs2_ext; eauto|].
        split; [eapply frame_mod_trans_same; eauto|exact FL'].
    Qed.
  End Unit2.
End Core2.
