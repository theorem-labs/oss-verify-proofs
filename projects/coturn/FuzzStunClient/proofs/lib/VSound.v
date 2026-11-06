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
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import VLinalg VState VLogic VGamma VAbs VAbsSound VStep VStepMem VStepSound VCert VItab VDriverMatch VContract VDriver VSoundMatch.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Existing Instance PropExec.fx0.  (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma cells_below_b_sound m b : cells_below_b m b = true -> cells_below m b.
Proof.
  unfold cells_below_b. rewrite forallb_forall. intros H k w e Hin. exact (H _ Hin).
Qed.

Lemma vstate_below_b_sound A : vstate_below_b A = true -> state_below A.
Proof.
  unfold vstate_below_b. intros H.
  repeat (apply andb_prop in H as [H ?X]).
  split; [apply Pos.ltb_lt; exact H|].
  split; [exact X5|].
  split; [intros r e Hr; exact (pm_forallb_sound _ _ X4 r Hr)|].
  split; [apply cells_below_b_sound; exact X3|].
  split; [apply cells_below_b_sound; exact X2|].
  split; [|split].
  - intros b k x y Hb. pose proof (pm_forallb_sound _ _ X1 b Hb) as Y. simpl in Y.
    apply andb_prop in Y as [Y Y3]. apply andb_prop in Y as [Y1 Y2]. apply Pos.ltb_lt in Y1. auto.
  - intros r x m Hr. pose proof (pm_forallb_sound _ _ X0 r Hr) as Y. simpl in Y.
    apply andb_prop in Y as [Y1 Y2]. apply Pos.ltb_lt in Y1. auto.
  - intros s0 vs Hs. pose proof (pm_forallb_sound _ _ X s0 Hs) as Y. simpl in Y. now apply Pos.ltb_lt.
Qed.

Lemma load_cstate_below cs pc ctx :
  cstate_wf cs = true -> state_below (load_cstate cs pc ctx) /\ (JOIN0 <= cs_next cs)%positive.
Proof.
  unfold cstate_wf. intros H. apply andb_prop in H as [H1 H2]. apply Pos.leb_le in H1.
  split; [|exact H1]. apply vstate_below_b_sound. exact H2.
Qed.

Lemma cm_of_list_in l k w v : In (k, (w, v)) (cm_of_list l) -> exists e, v = Some e /\ In (k, (w, e)) l.
Proof.
  induction l as [|[k' [w' e']] t IH]; simpl; [tauto|].
  intros [H|H].
  - inversion H; subst. eauto.
  - destruct (IH H) as [e [-> Hin]]. eauto.
Qed.

Lemma cstate_ok_slots P cs pc ctx off w v :
  cstate_ok P cs = true -> In (off, (w, v)) (vs_slots (load_cstate cs pc ctx)) ->
  - vp_frame P <= off /\ 0 < w /\ off + w <= 0 /\ v <> None.
Proof.
  unfold cstate_ok, cells_in_window. intros H Hin. simpl in Hin.
  apply andb_prop in H as [H _]. apply andb_prop in H as [H _]. apply andb_prop in H as [_ H].
  rewrite forallb_forall in H. destruct (cm_of_list_in _ _ _ _ Hin) as [e [-> Hin']].
  specialize (H _ Hin'). simpl in H. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply Z.leb_le in H1. apply Z.ltb_lt in H2. apply Z.leb_le in H3. repeat split; try lia; congruence.
Qed.

Lemma cstate_ok_globs P cs pc ctx a w v :
  cstate_ok P cs = true -> In (a, (w, v)) (vs_globs (load_cstate cs pc ctx)) ->
  0 <= a /\ 0 < w /\ a + w <= vp_splo P - vp_frame P /\ v <> None.
Proof.
  unfold cstate_ok, globs_in_range. intros H Hin. simpl in Hin.
  apply andb_prop in H as [H _]. apply andb_prop in H as [_ H].
  rewrite forallb_forall in H. destruct (cm_of_list_in _ _ _ _ Hin) as [e [-> Hin']].
  specialize (H _ Hin'). simpl in H. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply Z.leb_le in H1. apply Z.ltb_lt in H2. apply Z.leb_le in H3. repeat split; try lia; congruence.
Qed.

Lemma cstate_ok_wf P cs : cstate_ok P cs = true -> cstate_wf cs = true.
Proof. unfold cstate_ok. intros H. apply andb_prop in H as [H _]. apply andb_prop in H as [H _]. apply andb_prop in H as [H _]. apply cstate_wf_f_sound. exact H. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition unit_ret (U : vunit) (E : venv) : Z :=
  match u_root U with Some c => c | None => e_ra E end.

Section Core.
  Variable SEGS : list Segment.
  Variable G : genv.
  Variable rom : word -> option byte.

  Definition PU (U : vunit) : vparams := unit_params G U.
  Definition gammaU (U : vunit) (E : venv) (mem0 : word -> option byte) := gamma SEGS (PU U) E mem0.
  Definition regionsU (U : vunit) (E : venv) : list (word * Z) := unit_regions (PU U) E.

  (* [comment removed for export] *)
  Definition exit_regs (U : vunit) (nu : val) (regs' : bvmap 5 word) : Prop :=
    bv_unsigned (getr regs' 2%bv) = zwrap 64 (nu SP0 + u_sp U)
    /\ bv_unsigned (getr regs' 3%bv) = zwrap 64 (nu GP)
    /\ bv_unsigned (getr regs' 4%bv) = zwrap 64 (ge_tp G)
    /\ (forall r i, In (r, i) sreg_idx -> bv_unsigned (getr regs' (Z_to_bv 5 r)) = zwrap 64 (nu (SREG i))).

  Lemma exit_regs_ext U nu nu' regs' : ext JOIN0 nu nu' -> exit_regs U nu' regs' -> exit_regs U nu regs'.
  Proof.
    intros X (H1&H2&H3&H4). unfold exit_regs.
    rewrite <- (X SP0), <- (X GP) by (unfold SP0, GP, JOIN0; lia).
    split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
    intros r i Hin. rewrite <- (X (SREG i)); [apply H4; exact Hin|].
    unfold sreg_idx in Hin. simpl in Hin. unfold SREG, JOIN0.
    repeat (destruct Hin as [Hin|Hin]; [inversion Hin; subst; simpl; lia|]). destruct Hin.
  Qed.

  (* [comment removed for export] *)
  Definition EXIT (U : vunit) (E : venv) (mem0 : word -> option byte)
             (nu : val) (mem : word -> option byte)
             (regs' : bvmap 5 word) (mem' : word -> option byte) : Prop :=
    exists X nu',
      In X (u_exits U)
      /\ gammaU U E mem0 (load_cstate X (unit_ret U E) []) nu' regs' mem'
      /\ ext JOIN0 nu nu'
      /\ getr regs' 1%bv = wordZ (unit_ret U E)
      /\ exit_regs U nu regs'
      /\ frame_mod mem mem' (regionsU U E).

  Definition unit_ok (U : vunit) : Prop :=
    forall E mem0 nu regs mem,
      ret_ok (wordZ (unit_ret U E)) ->
      gammaU U E mem0 (load_cstate (u_pre U) (u_entry U) []) nu regs mem ->
      exists regs' mem',
        msteps SEGS (mkst regs (wordZ (u_entry U)) mem rom) (mkst regs' (wordZ (unit_ret U E)) mem' rom)
        /\ EXIT U E mem0 nu mem regs' mem'.

  (* [comment removed for export] *)
  Definition CUT (U : vunit) (E : venv) (mem0 : word -> option byte) (Rstart : lin)
             (nu : val) (mem : word -> option byte)
             (regs' : bvmap 5 word) (pc' : word) (mem' : word -> option byte) : Prop :=
    exists c i X R nu',
      In c (u_cuts U) /\ nth_error (cut_states c) i = Some X /\ nth_error (cut_ranks c) i = Some R
      /\ pc' = wordZ (cut_pc c)
      /\ gammaU U E mem0 (load_cstate X (cut_pc c) (cut_ctx c)) nu' regs' mem'
      /\ ext JOIN0 nu nu'
      /\ eval nu' R <= eval nu Rstart - 1
      /\ frame_mod mem mem' (regionsU U E).

  Definition outcome (U : vunit) (E : venv) (mem0 : word -> option byte) (Rstart : lin)
             (nu : val) (regs : bvmap 5 word) (pc : word) (mem : word -> option byte) : Prop :=
    exists regs' pc' mem',
      msteps SEGS (mkst regs pc mem rom) (mkst regs' pc' mem' rom)
      /\ ((pc' = wordZ (unit_ret U E) /\ EXIT U E mem0 nu mem regs' mem')
          \/ CUT U E mem0 Rstart nu mem regs' pc' mem').

  Definition safe_state (U : vunit) (E : venv) (mem0 : word -> option byte) (Rstart : lin) (A : vstate) : Prop :=
    forall nu regs (pc : word) mem,
      lin_below Rstart (vs_next A) = true -> (JOIN0 <= vs_next A)%positive ->
      vs_pc A = bv_unsigned pc ->
      gammaU U E mem0 A nu regs mem ->
      outcome U E mem0 Rstart nu regs pc mem.

  (* [comment removed for export] *)
  Definition dstep_post (U : vunit) (E : venv) (mem0 : word -> option byte)
             (A : vstate) (succs : list vstate) (nu : val) (regs : bvmap 5 word) (pc : word) (mem : word -> option byte) : Prop :=
    (exists regs' pc' mem' A' nu',
        msteps SEGS (mkst regs pc mem rom) (mkst regs' pc' mem' rom)
        /\ In A' succs /\ vs_pc A' = bv_unsigned pc'
        /\ ext (vs_next A) nu nu' /\ (vs_next A <= vs_next A')%positive
        /\ frame_mod mem mem' (regionsU U E)
        /\ gammaU U E mem0 A' nu' regs' mem')
    \/ (exists regs' mem',
        msteps SEGS (mkst regs pc mem rom) (mkst regs' (wordZ (unit_ret U E)) mem' rom)
        /\ EXIT U E mem0 nu mem regs' mem').

  (* [comment removed for export] *)
  Section Unit.
    Variable done : list vunit.
    Variable U : vunit.
    Variable E : venv.
    Variable mem0 : word -> option byte.
    Let D := mk_denv G done U.

    Hypothesis RANKS : ge_ranks G = true.

    Hypothesis DS : forall A succs nu regs pc mem,
      dstep D A = SN succs ->
      (JOIN0 <= vs_next A)%positive ->
      vs_pc A = bv_unsigned pc ->
      gammaU U E mem0 A nu regs mem ->
      dstep_post U E mem0 A succs nu regs pc mem.

    (* [comment removed for export] *)
    Hypothesis STATIC : unit_static_ok G (PU U) U = None.

    Lemma static_facts :
      cstate_ok (PU U) (u_pre U) = true
      /\ (forall c, In c (u_cuts U) -> pc_ok (cut_pc c) = true /\ forallb (cstate_ok (PU U)) (cut_states c) = true)
      /\ pc_ok (u_entry U) = true
      /\ forallb (cstate_ok (PU U)) (u_exits U) = true
      /\ (forall c, In c (u_cuts U) -> length (cut_ranks c) = length (cut_states c) /\ rank_nonneg c = true).
    Proof.
      unfold unit_static_ok in STATIC. rewrite RANKS in STATIC.
      destruct (cstate_ok (PU U) (u_pre U)); [|discriminate].
      destruct (pre_canonical G U); [|discriminate].
      destruct (forallb (fun c => pc_ok (cut_pc c) && forallb (cstate_ok (PU U)) (cut_states c)) (u_cuts U)) eqn:C1; [|discriminate].
      destruct (pc_ok (u_entry U)); [|discriminate].
      destruct (forallb (cstate_ok (PU U)) (u_exits U)); [|discriminate].
      simpl in STATIC.
      destruct (forallb (fun c => Nat.eqb (length (cut_ranks c)) (length (cut_states c)) && rank_nonneg c) (u_cuts U)) eqn:C2; [|discriminate].
      split; [reflexivity|]. split.
      { intros c Hc. rewrite forallb_forall in C1. specialize (C1 _ Hc). apply andb_prop in C1 as [A1 A2]. auto. }
      split; [reflexivity|]. split; [reflexivity|].
      intros c Hc. rewrite forallb_forall in C2. specialize (C2 _ Hc). apply andb_prop in C2 as [A1 A2].
      apply Nat.eqb_eq in A1. auto.
    Qed.

    Lemma CUTS_OK : forall c, In c (u_cuts U) -> forallb (cstate_ok (PU U)) (cut_states c) = true.
    Proof. intros c Hc. apply (proj1 (proj2 static_facts)); auto. Qed.

    (* [comment removed for export] *)
    Lemma cuts_by_pc_in : forall l m k cs c,
      pm_get k (cuts_by_pc l m) = Some cs -> In c cs ->
      In c l \/ (exists cs0, pm_get k m = Some cs0 /\ In c cs0).
    Proof.
      induction l as [|c0 t IH]; simpl; intros m k cs c Hg Hin; [right; eauto|].
      destruct (IH _ _ _ _ Hg Hin) as [H|[cs0 [Hg0 Hin0]]]; [auto|].
      rewrite pm_get_set in Hg0. destruct (Pos.eqb_spec k (zkey (cut_pc c0))).
      - inversion Hg0; subst cs0. apply in_app_iff in Hin0 as [H|H]; [|simpl in H; destruct H as [H|H]; [auto|tauto]].
        right. destruct (pm_get (zkey (cut_pc c0)) m) as [l'|] eqn:G0; [|destruct H]. exists l'. rewrite <- e in G0. auto.
      - right; eauto.
    Qed.

    Lemma find_cut_spec pc ctx c :
      find_cut D pc ctx = Some c -> In c (u_cuts U) /\ cut_pc c = pc /\ cut_ctx c = cut_ctx c.
    Proof.
      unfold find_cut. destruct (Z.ltb 0 pc); [|discriminate]. simpl.
      unfold D, mk_denv; simpl.
      destruct (pm_get (zkey pc) (cuts_by_pc (u_cuts U) pm_empty)) as [l|] eqn:G0; [|discriminate].
      intros Hf. apply find_some in Hf as [Hin Hb]. apply andb_prop in Hb as [Hb _]. apply Z.eqb_eq in Hb.
      destruct (cuts_by_pc_in _ _ _ _ _ G0 Hin) as [H|[cs0 [H _]]]; [auto|].
      rewrite pm_get_empty in H. discriminate.
    Qed.

    Lemma try_disjuncts_none Rstart A c : forall sts rks msgs,
      try_disjuncts D Rstart A c sts rks msgs = None ->
      exists i X R sigma,
        nth_error sts i = Some X /\ nth_error rks i = Some R
        /\ match_state isv_join no_skip false pm_empty (load_cstate X (cut_pc c) (cut_ctx c)) A = MOk sigma
        /\ qge A (lsub Rstart (lsubst sigma R)) 1 = true.
    Proof.
      induction sts as [|X t IH]; simpl; intros rks msgs H; [discriminate|].
      assert (STEP : forall rks' msgs', try_disjuncts D Rstart A c t rks' msgs' = None ->
                     rks' = match rks with _ :: r' => r' | [] => [] end ->
                     exists i X0 R sigma, nth_error (X :: t) i = Some X0 /\ nth_error rks i = Some R /\
                       match_state isv_join no_skip false pm_empty (load_cstate X0 (cut_pc c) (cut_ctx c)) A = MOk sigma /\
                       qge A (lsub Rstart (lsubst sigma R)) 1 = true).
      { intros rks' msgs' H' ->. destruct (IH _ _ H') as (i & X0 & R & sigma & N1 & N2 & M & Q).
        exists (S i), X0, R, sigma. simpl. destruct rks as [|r0 r']; [destruct i; discriminate|]. auto. }
      destruct (match_state isv_join no_skip false pm_empty (load_cstate X (cut_pc c) (cut_ctx c)) A) as [sigma|m] eqn:M.
      - unfold D, mk_denv in H; simpl in H. rewrite RANKS in H.
        destruct rks as [|r rks'].
        + eapply STEP; [exact H|reflexivity].
        + destruct (qge A (lsub Rstart (lsubst sigma r)) 1) eqn:Q.
          * exists O, X, r, sigma. simpl. auto.
          * eapply STEP; [exact H|reflexivity].
      - eapply STEP; [exact H|reflexivity].
    Qed.

    (* [comment removed for export] *)
    Lemma gamma_stored A X pc ctx sigma nu regs mem :
      gammaU U E mem0 A nu regs mem ->
      cstate_ok (PU U) X = true ->
      match_state isv_join no_skip false pm_empty (load_cstate X pc ctx) A = MOk sigma ->
      gammaU U E mem0 (load_cstate X pc ctx) (vsubst nu sigma) regs mem /\ ext JOIN0 nu (vsubst nu sigma).
    Proof.
      intros HGm HX HM.
      pose proof HGm as (HE&HMC&HF&HS&HC&HMo&HV&HR&HSl&HGl&HN&HB).
      destruct (match_state_sound SEGS (PU U) (PU U) E E eq_refl eq_refl eq_refl
                  isv_join no_skip false pm_empty (load_cstate X pc ctx) A sigma nu regs mem
                  HM HS HC HMo HV HR HSl HGl HN) as (Sub & BO & S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8).
      { intros; eapply cstate_ok_slots; eauto. }
      { intros; eapply cstate_ok_globs; eauto. }
      assert (EXT : ext JOIN0 nu (vsubst nu sigma)).
      { intros s Hs. unfold vsubst. destruct (pm_get s sigma) as [e|] eqn:Gs; [|reflexivity].
        destruct (BO _ _ Gs) as [Hg|Hv]; [rewrite pm_get_empty in Hg; discriminate|].
        unfold isv_join in Hv. apply Pos.leb_le in Hv. lia. }
      split; [|exact EXT].
      destruct (load_cstate_below X pc ctx (cstate_ok_wf _ _ HX)) as [BEL _].
      split; [exact HE|]. split; [exact HMC|]. split.
      { eapply gamma_fix_ext; [| exact EXT | exact HF]. unfold JOIN0, LAST_FIXED; lia. }
      split; [exact S1|]. split; [exact S2|]. split; [exact S3|]. split; [exact S4|].
      split; [intros r e Hr He; apply S5; auto|].
      split; [exact S6|]. split; [exact S7|]. split; [exact S8|exact BEL].
    Qed.

    (* [comment removed for export] *)
    Lemma cut_arrival_sound Rstart A c nu regs pc mem :
      find_cut D (vs_pc A) (vs_ctx A) = Some c ->
      cut_arrival D Rstart A c = SN [] ->
      vs_pc A = bv_unsigned pc ->
      gammaU U E mem0 A nu regs mem ->
      outcome U E mem0 Rstart nu regs pc mem.
    Proof.
      intros Hf Hc Hpc HGm.
      destruct (find_cut_spec _ _ _ Hf) as (Hin & Hpc' & _).
      unfold cut_arrival in Hc.
      destruct (try_disjuncts D Rstart A c (cut_states c) (cut_ranks c) []) as [msgs|] eqn:T; [discriminate|].
      destruct (try_disjuncts_none _ _ _ _ _ _ T) as (i & X & R & sigma & N1 & N2 & M & Q).
      assert (HX : cstate_ok (PU U) X = true).
      { pose proof (CUTS_OK _ Hin) as CO. rewrite forallb_forall in CO. apply CO. eapply nth_error_In; eauto. }
      destruct (gamma_stored _ _ _ _ _ _ _ _ HGm HX M) as [HG' EXT].
      exists regs, pc, mem. split; [apply mst_refl|]. right.
      exists c, i, X, R, (vsubst nu sigma).
      split; [exact Hin|]. split; [exact N1|]. split; [exact N2|]. split.
      { rewrite Hpc', Hpc. unfold wordZ. symmetry. apply Z_to_bv_bv_unsigned. }
      split; [exact HG'|]. split; [exact EXT|]. split.
      { pose proof (qge_sound A nu _ _ (gamma_lgamma _ _ _ _ _ _ _ _ HGm) Q) as HQ.
        rewrite eval_lsub, eval_lsubst in HQ. lia. }
      apply frame_mod_refl.
    Qed.

    Lemma ext_JOIN0 A nu nu' :
      (JOIN0 <= vs_next A)%positive -> ext (vs_next A) nu nu' -> ext JOIN0 nu nu'.
    Proof. intros H1 H2. eapply ext_mono; eauto. Qed.

    Lemma outcome_after A A' Rstart nu nu' regs regs1 pc pc1 mem mem1 :
      lin_below Rstart (vs_next A) = true -> (JOIN0 <= vs_next A)%positive ->
      msteps SEGS (mkst regs pc mem rom) (mkst regs1 pc1 mem1 rom) ->
      ext (vs_next A) nu nu' -> (vs_next A <= vs_next A')%positive ->
      frame_mod mem mem1 (regionsU U E) ->
      outcome U E mem0 Rstart nu' regs1 pc1 mem1 ->
      outcome U E mem0 Rstart nu regs pc mem.
    Proof.
      intros HR HJ Hms Hext Hle Hfm (regs' & pc' & mem' & Hms' & Hout).
      exists regs', pc', mem'. split; [eapply msteps_trans; eauto|].
      destruct Hout as [[Hpc (X & nu'' & HX & HG & Hext' & Hra & Hxr & Hfm')]|(c & i & X & R & nu'' & Hc & HX & HRk & Hpc & HG & Hext' & Hlt & Hfm')].
      - left. split; auto. exists X, nu''. split; [exact HX|]. split; [exact HG|]. split; [|split; [exact Hra|split]].
        + eapply (ext_trans JOIN0 JOIN0); [lia | eapply ext_mono; [exact HJ|exact Hext] | exact Hext'].
        + eapply exit_regs_ext; [eapply ext_mono; [exact HJ|exact Hext]|exact Hxr].
        + eapply frame_mod_trans_same; eauto.
      - right. exists c, i, X, R, nu''. split; [exact Hc|]. split; [exact HX|]. split; [exact HRk|]. split; [exact Hpc|].
        split; [exact HG|]. split; [|split].
        + eapply (ext_trans JOIN0 JOIN0); [lia | eapply ext_mono; [exact HJ|exact Hext] | exact Hext'].
        + rewrite <- (eval_ext_below _ _ _ _ Hext HR). exact Hlt.
        + eapply frame_mod_trans_same; eauto.
    Qed.

    Theorem explore_sound : forall fuel origin Rstart work,
      explore D fuel origin Rstart work = ROk ->
      forall first A, In (first, A) work ->
        (first = true \/ find_cut D (vs_pc A) (vs_ctx A) = None \/ True) ->
        safe_state U E mem0 Rstart A.
    Proof.
      induction fuel as [|f IH]; intros origin Rstart work Hx first A Hin _.
      - simpl in Hx. destruct work as [|[b B] t]; [destruct Hin|discriminate].
      - simpl in Hx. destruct work as [|[b B] t]; [destruct Hin|].
        destruct Hin as [Hin|Hin].
        + inversion Hin; subst b B.
          destruct (if first then None else find_cut D (vs_pc A) (vs_ctx A)) as [c|] eqn:Fc.
          * destruct (cut_arrival D Rstart A c) as [l|m] eqn:Ca; [|discriminate].
            intros nu regs pc mem HR HJ Hpc HG.
            destruct first; [discriminate|].
            assert (l = []) by (unfold cut_arrival in Ca; destruct (try_disjuncts _ _ _ _ _ _ _); congruence). subst l.
            eapply cut_arrival_sound; eauto.
          * destruct (dstep D A) as [succs|m] eqn:St; [|discriminate].
            intros nu regs pc mem HR HJ Hpc HG.
            destruct (DS _ _ _ _ _ _ St HJ Hpc HG)
              as [(regs1 & pc1 & mem1 & A' & nu' & Hms & Hin' & Hpc' & Hext & Hle & Hfm & HG')|(regs' & mem' & Hms & HEX)].
            -- eapply outcome_after; eauto.
               eapply (IH _ _ _ Hx false A'); auto.
               ++ apply in_app_iff. left. apply in_map_iff. exists A'; auto.
               ++ eapply lin_below_mono; eauto.
               ++ lia.
            -- exists regs', (wordZ (unit_ret U E)), mem'. split; auto.
        + destruct (if b then None else find_cut D (vs_pc B) (vs_ctx B)) as [c|].
          * destruct (cut_arrival D Rstart B c); [|discriminate]. eapply IH; eauto.
          * destruct (dstep D B); [|discriminate]. eapply IH; eauto. apply in_app_iff; right; eauto.
    Qed.

    (* [comment removed for export] *)
    Lemma rank_facts c i X R :
      In c (u_cuts U) -> nth_error (cut_states c) i = Some X -> nth_error (cut_ranks c) i = Some R ->
      qge (load_cstate X (cut_pc c) (cut_ctx c)) R 0 = true /\ lin_below R (cs_next X) = true.
    Proof.
      intros Hc HX HR. destruct (proj2 (proj2 (proj2 (proj2 static_facts))) c Hc) as [Hlen Hnn].
      unfold rank_nonneg in Hnn. rewrite forallb_forall in Hnn.
      assert (Hin : In (X, R) (combine (cut_states c) (cut_ranks c))).
      { revert HX HR. clear. revert i. generalize (cut_ranks c) as rks. generalize (cut_states c) as sts.
        induction sts as [|x t IH]; intros rks [|i] HX HR; simpl in *; try discriminate.
        - inversion HX; subst. destruct rks; [discriminate|]. inversion HR; subst. simpl; auto.
        - destruct rks; [discriminate|]. simpl. right. eapply IH; eauto. }
      specialize (Hnn _ Hin). simpl in Hnn. apply andb_prop in Hnn as [A1 A2]. auto.
    Qed.

    Lemma pc_ok_u pc : pc_ok pc = true -> bv_unsigned (wordZ pc) = pc.
    Proof.
      unfold pc_ok. intros H. apply andb_prop in H as [H1 H2]. apply Z.ltb_lt in H1. apply Z.ltb_lt in H2.
      unfold wordZ. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. apply Z.mod_small. lia.
    Qed.

    Lemma check_cut_states_ok fuel c : forall sts rks k,
      check_cut_states D fuel c sts rks k = ROk ->
      forall i X R, nth_error sts i = Some X -> nth_error rks i = Some R ->
        explore D fuel "cut" R [(true, load_cstate X (cut_pc c) (cut_ctx c))] = ROk.
    Proof.
      induction sts as [|X t IH]; simpl; intros rks k H i X0 R HX HR; [destruct i; discriminate|].
      destruct rks as [|r rks']; [destruct i; discriminate|].
      destruct (explore D fuel "cut" r [(true, load_cstate X (cut_pc c) (cut_ctx c))]) eqn:Ex; [|discriminate].
      destruct i as [|i]; simpl in *.
      - inversion HX; inversion HR; subst. exact Ex.
      - eapply IH; eauto.
    Qed.

    Lemma check_cuts_ok fuel : forall l,
      check_cuts D fuel l = ROk ->
      forall c i X R, In c l -> nth_error (cut_states c) i = Some X -> nth_error (cut_ranks c) i = Some R ->
        explore D fuel "cut" R [(true, load_cstate X (cut_pc c) (cut_ctx c))] = ROk.
    Proof.
      induction l as [|c0 t IH]; simpl; intros H c i X R Hin HX HR; [destruct Hin|].
      destruct (check_cut_states D fuel c0 (cut_states c0) (cut_ranks c0) 0) eqn:E0; [|discriminate].
      destruct Hin as [<-|Hin]; [eapply check_cut_states_ok; eauto| eapply IH; eauto].
    Qed.

    Section Reach.
      Variable fuel : nat.
      Hypothesis CUTS : check_cuts D fuel (u_cuts U) = ROk.

      Lemma cuts_reach : forall n c i X R nu regs mem,
        In c (u_cuts U) -> nth_error (cut_states c) i = Some X -> nth_error (cut_ranks c) i = Some R ->
        gammaU U E mem0 (load_cstate X (cut_pc c) (cut_ctx c)) nu regs mem ->
        (Z.to_nat (eval nu R) < n)%nat ->
        exists regs' mem',
          msteps SEGS (mkst regs (wordZ (cut_pc c)) mem rom) (mkst regs' (wordZ (unit_ret U E)) mem' rom)
          /\ EXIT U E mem0 nu mem regs' mem'.
      Proof.
        induction n as [|n IH]; intros c i X R nu regs mem Hc HX HR HG Hn; [lia|].
        pose proof (check_cuts_ok _ _ CUTS _ _ _ _ Hc HX HR) as Ex.
        destruct (rank_facts _ _ _ _ Hc HX HR) as [Q B].
        destruct (load_cstate_below X (cut_pc c) (cut_ctx c)) as [BEL J0].
        { eapply cstate_ok_wf. pose proof (CUTS_OK _ Hc) as CO. rewrite forallb_forall in CO. apply CO. eapply nth_error_In; eauto. }
        assert (SAFE : safe_state U E mem0 R (load_cstate X (cut_pc c) (cut_ctx c))).
        { eapply explore_sound; eauto. simpl; auto. }
        destruct (SAFE nu regs (wordZ (cut_pc c)) mem) as (regs1 & pc1 & mem1 & Hms & Hout); auto.
        { simpl. symmetry. apply pc_ok_u. apply (proj1 (proj1 (proj2 static_facts) c Hc)). }
        destruct Hout as [[-> HEX]|(c' & i' & X' & R' & nu' & Hc' & HX' & HR' & -> & HG' & EXT & LT & FM)].
        - exists regs1, mem1. auto.
        - destruct (rank_facts _ _ _ _ Hc' HX' HR') as [Q' _].
          pose proof (qge_sound _ nu' _ _ (gamma_lgamma _ _ _ _ _ _ _ _ HG') Q') as NN.
          destruct (IH c' i' X' R' nu' regs1 mem1 Hc' HX' HR' HG') as (regs' & mem' & Hms' & HEX'); [lia|].
          exists regs', mem'. split; [eapply msteps_trans; eauto|].
          destruct HEX' as (Xe & nu'' & HXe & HGe & EXT' & Hra & Hxr & FM').
          exists Xe, nu''. split; [exact HXe|]. split; [exact HGe|]. split.
          { eapply (ext_trans JOIN0 JOIN0); [lia|exact EXT|exact EXT']. }
          split; [exact Hra|]. split; [eapply exit_regs_ext; eauto|]. eapply frame_mod_trans_same; eauto.
      Qed.
    End Reach.

    Theorem check_unit_sound_E nu regs mem :
      check_unit G done U = ROk ->
      gammaU U E mem0 (load_cstate (u_pre U) (u_entry U) []) nu regs mem ->
      exists regs' mem',
        msteps SEGS (mkst regs (wordZ (u_entry U)) mem rom) (mkst regs' (wordZ (unit_ret U E)) mem' rom)
        /\ EXIT U E mem0 nu mem regs' mem'.
    Proof.
      unfold check_unit. fold D. change (de_P D) with (PU U). rewrite STATIC.
      destruct (explore D (N.to_nat (u_fuel U)) "entry" RANK_TOP [(true, load_cstate (u_pre U) (u_entry U) [])]) eqn:Ex; try discriminate.
      intros CUTS HG.
      destruct (load_cstate_below (u_pre U) (u_entry U) []) as [BEL J0].
      { eapply cstate_ok_wf. apply (proj1 static_facts). }
      assert (SAFE : safe_state U E mem0 RANK_TOP (load_cstate (u_pre U) (u_entry U) [])).
      { eapply explore_sound; eauto. simpl; auto. }
      destruct (SAFE nu regs (wordZ (u_entry U)) mem) as (regs1 & pc1 & mem1 & Hms & Hout); auto.
      { simpl. symmetry. apply pc_ok_u. apply (proj1 (proj2 (proj2 static_facts))). }
      destruct Hout as [[-> HEX]|(c' & i' & X' & R' & nu' & Hc' & HX' & HR' & -> & HG' & EXT & LT & FM)].
      - exists regs1, mem1. auto.
      - destruct (cuts_reach _ CUTS (S (Z.to_nat (eval nu' R'))) c' i' X' R' nu' regs1 mem1 Hc' HX' HR' HG')
          as (regs' & mem' & Hms' & HEX'); [lia|].
        exists regs', mem'. split; [eapply msteps_trans; eauto|].
        destruct HEX' as (Xe & nu'' & HXe & HGe & EXT' & Hra & Hxr & FM').
        exists Xe, nu''. split; [exact HXe|]. split; [exact HGe|]. split.
        { eapply (ext_trans JOIN0 JOIN0); [lia|exact EXT|exact EXT']. }
        split; [exact Hra|]. split; [eapply exit_regs_ext; eauto|]. eapply frame_mod_trans_same; eauto.
    Qed.
  End Unit.
End Core.
