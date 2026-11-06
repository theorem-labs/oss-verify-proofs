(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool String Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import PropExec CatExec CatSim StoreOk.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import Frame.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import Hoare SeqExec.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import VLinalg VState VLogic VGamma VAbs VAbsSound VAbsSound2 VAbsSound3 VStep VStepMem VStepSound VStepMemSound VCert VItab VDriverMatch VContract VDriver VSoundMatch VSound.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import LiaKeep.  (* [comment removed for export] *)
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import LiaKeepCb.  (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Existing Instance PropExec.fx0.  (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition unit_okS (SEGS : list Segment) (G : genv) (rom : word -> option byte) (V : vunit) : Prop :=
  unit_static_ok G (unit_params G V) V = None /\ unit_ok SEGS G rom V.

Section Call.
  Variable SEGS : list Segment.
  Variable G : genv.
  Variable rom : word -> option byte.
  Variable done : list vunit.
  Variable U : vunit.
  Variable E : venv.
  Variable mem0 : word -> option byte.

  Let D := mk_denv G done U.
  Let P := unit_params G U.
  Notation gammaP := (gamma SEGS P E mem0).

  Hypothesis DONE : Forall (unit_okS SEGS G rom) done.

  Hypothesis VSTEP : forall A i succs nu regs mem (pc : word) w,
    vstep P A i = VR_next succs ->
    gammaP A nu regs mem -> vs_pc A = bv_unsigned pc ->
    fetch_word SEGS pc = Some w -> is_ecall w = false -> decode_any w = Some (i, 4) ->
    step_post SEGS P E mem0 A nu succs regs mem pc rom.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma gamma_regs_getr Px Ex A nu regs1 regs2 mem :
    (forall r, getr regs2 r = getr regs1 r) ->
    gamma SEGS Px Ex mem0 A nu regs1 mem -> gamma SEGS Px Ex mem0 A nu regs2 mem.
  Proof.
    intros Hr (HE&HM&HF&HS&HC&HMo&HV&HR&HSl&HG&HN&HB).
    split; [exact HE|]. split; [exact HM|]. split; [exact HF|]. split; [exact HS|]. split; [exact HC|].
    split; [exact HMo|]. split; [exact HV|]. split; [|split; [exact HSl|split; [exact HG|split; [exact HN|exact HB]]]].
    intros r e Hr0 Hg. rewrite Hr. now apply HR.
  Qed.

  Lemma regupd_same_getr regs (r : reg) r' : r <> 0%bv -> getr (regupd regs r (getr regs r)) r' = getr regs r'.
  Proof.
    intros Hr. destruct (base.decide (r' = r)) as [->|Hne].
    - apply getr_same; auto.
    - apply getr_other; auto.
  Qed.

  (* [comment removed for export] *)
  Lemma materialize_step A nu regs mem (r : reg) :
    gammaP A nu regs mem -> rz r <> 0 ->
    exists nu1,
      gammaP (materialize1 A (rz r)) nu1 regs mem
      /\ ext (vs_next A) nu nu1
      /\ (vs_next A <= vs_next (materialize1 A (rz r)))%positive.
  Proof.
    intros HG Hr. unfold materialize1. destruct (get_reg A (rz r)) as [e|] eqn:Gr.
    - exists nu. split; [exact HG|]. split; [apply ext_refl|lia].
    - pose proof (afresh_sound A nu itv_top (bv_unsigned (getr regs r)) (gamma_lgamma _ _ _ _ _ _ _ _ HG) (in_itv_top _)) as X.
      destruct (afresh A itv_top) as [v A'] eqn:Ea.
      destruct X as (nu1 & HX & HL & Hv). destruct v as [e'|]; [|destruct Hv].
      destruct Hv as [Hev Hbl].
      exists nu1.
      assert (HG' : gammaP (set_pc (set_reg A' (rz r) (Some e')) (vs_pc A)) nu1 (regupd regs r (getr regs r)) mem).
      { eapply gamma_upd; eauto. split; [|exact Hbl]. rewrite Hev. symmetry. apply zwrap_id. 
        pose proof (bv_unsigned_in_range 64 (getr regs r)) as R. unfold bv_modulus in R. simpl in R. lia. }
      split.
      + apply (gamma_regs_getr P E _ nu1 (regupd regs r (getr regs r)) regs mem).
        { intros r'. symmetry. apply regupd_same_getr. intros ->. apply Hr. reflexivity. }
        exact HG'.
      + destruct HX as (HX1 & HX2 & _). split; [exact HX1|]. rewrite vs_next_set_reg. exact HX2.
  Qed.

  Lemma materialize_sound A nu regs mem : forall l,
    (forall r i, In (r, i) l -> 0 < r < 32) ->
    gammaP A nu regs mem ->
    exists nu1, gammaP (materialize A l) nu1 regs mem /\ ext (vs_next A) nu nu1
                /\ (vs_next A <= vs_next (materialize A l))%positive.
  Proof.
    intros l. revert A nu. induction l as [|[r i] t IH]; intros A nu Hl HG; cbn [materialize].
    - exists nu. split; [exact HG|]. split; [apply ext_refl|lia].
    - assert (Hr : 0 < r < 32) by (apply (Hl r i); now left).
      assert (Er : rz (Z_to_bv 5 r) = r).
      { unfold rz. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. simpl. lia. }
      destruct (materialize_step A nu regs mem (Z_to_bv 5 r) HG) as (nu1 & HG1 & X1 & L1); [rewrite Er; lia|].
      rewrite Er in HG1, L1.
      destruct (IH _ nu1 ltac:(intros; eapply Hl; right; eauto) HG1) as (nu2 & HG2 & X2 & L2).
      exists nu2. split; [exact HG2|]. split; [|lia].
      eapply ext_trans; [exact L1|exact X1|exact X2].
  Qed.

  Lemma sreg_idx_range r i : In (r, i) sreg_idx -> 0 < r < 32.
  Proof.
    unfold sreg_idx. simpl. intros H.
    repeat (destruct H as [H|H]; [inversion H; subst; lia|]). destruct H.
  Qed.

  (* [comment removed for export] *)
  Lemma try_variants_sound A spoff npc : forall l msgs succs,
    try_variants D A l spoff npc msgs = SN succs ->
    exists V, In V l /\ try_variant D A V spoff npc = SN succs.
  Proof.
    induction l as [|V t IH]; simpl; intros msgs succs H; [discriminate|].
    destruct (try_variant D A V spoff npc) as [s|m] eqn:T.
    - inversion H; subst. exists V. auto.
    - destruct (IH _ _ H) as [V' [Hin HT]]. exists V'. auto.
  Qed.

  Lemma insert_prio_in V l x : In x (insert_prio V l) -> x = V \/ In x l.
  Proof.
    induction l as [|W t IH]; simpl.
    - intros [H|[]]; auto.
    - destruct (Z.ltb (u_prio V) (u_prio W)); simpl; intros H.
      + destruct H as [H|H]; auto.
      + destruct H as [H|H]; [auto|]. destruct (IH H); auto.
  Qed.

  Lemma hinted_variants_in calls pc all V : In V (hinted_variants calls pc all) -> In V all.
  Proof.
    induction calls as [|c t IH]; simpl; [tauto|]. destruct (Z.eqb (call_pc c) pc); [|exact IH].
    intros H. apply in_app_or in H as [H|H]; [|exact (IH H)]. apply filter_In in H. tauto.
  Qed.

  Lemma call_variants_in pc tgt V :
    In V (call_variants D pc tgt) -> In V done /\ u_entry V = tgt.
  Proof.
    unfold call_variants. change (de_done D) with done.
    assert (GEN : forall l, In V (fold_right insert_prio [] l) -> In V l).
    { induction l as [|W t IH]; simpl; [tauto|]. intros H. apply insert_prio_in in H as [->|H]; auto. }
    intros H. apply in_app_or in H as [H|H].
    - apply hinted_variants_in in H. apply GEN in H. apply filter_In in H as [H1 H2]. apply Z.eqb_eq in H2. auto.
    - apply GEN in H. apply filter_In in H as [H1 H2]. apply Z.eqb_eq in H2. auto.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Definition sregs_of (nuV : val) : list Z := map (fun i => nuV (SREG i)) (map Z.of_nat (seq 0 12)).

  Definition callee_env (npc : Z) (nuV : val) : venv :=
    mkEnv (e_sp0 E) (e_data E) (e_size E) npc (e_tp E) (e_gp E) (sregs_of nuV).

  Lemma fix_val_callee npc nuV s z :
    fix_val (callee_env npc nuV) s = Some z ->
    (s = SP0 /\ z = e_sp0 E) \/ (s = DATA /\ z = e_data E) \/ (s = SIZE /\ z = e_size E)
    \/ (s = RA /\ z = npc) \/ (s = TP /\ z = e_tp E) \/ (s = GP /\ z = e_gp E)
    \/ (exists i, 0 <= i < 12 /\ s = SREG i /\ z = nuV (SREG i)).
  Proof.
    unfold fix_val, callee_env. cbn [e_sp0 e_data e_size e_ra e_tp e_gp e_sregs].
    destruct (Pos.eqb_spec s SP0); [intros X; inversion X; subst; auto 20|].
    destruct (Pos.eqb_spec s DATA); [intros X; inversion X; subst; auto 20|].
    destruct (Pos.eqb_spec s SIZE); [intros X; inversion X; subst; auto 20|].
    destruct (Pos.eqb_spec s RA); [intros X; inversion X; subst; auto 20|].
    destruct (Pos.eqb_spec s TP); [intros X; inversion X; subst; auto 20|].
    destruct (Pos.eqb_spec s GP); [intros X; inversion X; subst; auto 20|].
    destruct (Pos.leb_spec 5 s); destruct (Pos.leb_spec s 16); simpl; try discriminate.
    intros X. do 6 right.
    exists (Z.pos s - 5). split; [lia|]. split; [unfold SREG; lia|].
    unfold sregs_of in X.
    assert (R : forall k, (k < 12)%nat ->
              nth_error (map (fun i : Z => nuV (SREG i)) (map Z.of_nat (seq 0 12))) k = Some (nuV (SREG (Z.of_nat k)))).
    { intros k Hk. rewrite nth_error_map, nth_error_map, nth_error_seq.
      destruct (PeanoNat.Nat.ltb_spec k 12); [reflexivity|lia]. }
    rewrite R in X by lia. inversion X; subst. f_equal. f_equal. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma sigma_sregs_other A l sigma s :
    (forall r i, In (r, i) l -> SREG i <> s) -> pm_get s (sigma_sregs A l sigma) = pm_get s sigma.
  Proof.
    revert sigma. induction l as [|[r i] t IH]; intros sigma Hn; simpl; [reflexivity|].
    rewrite IH by (intros; eapply Hn; right; eauto).
    destruct (get_reg A r); [|reflexivity]. rewrite pm_get_set_other; [reflexivity|].
    intros X. apply (Hn r i); [now left|auto].
  Qed.

  Fixpoint snd_distinct (l : list (Z * Z)) : Prop :=
    match l with
    | [] => True
    | (_, i) :: t => (forall r' i', In (r', i') t -> SREG i' <> SREG i) /\ snd_distinct t
    end.

  Lemma sigma_sregs_in A : forall l sigma r i e,
    snd_distinct l -> In (r, i) l -> get_reg A r = Some e ->
    pm_get (SREG i) (sigma_sregs A l sigma) = Some e.
  Proof.
    induction l as [|[r0 i0] t IH]; intros sigma r i e Hd Hin Hg; simpl; [destruct Hin|].
    destruct Hd as [Hd1 Hd2]. destruct Hin as [Hin|Hin].
    - inversion Hin; subst. rewrite Hg. rewrite sigma_sregs_other; [apply pm_get_set_same|].
      intros r' i' Hin'. exact (Hd1 _ _ Hin').
    - eapply IH; eauto.
  Qed.

  Lemma sreg_idx_distinct : snd_distinct sreg_idx.
  Proof.
    unfold sreg_idx. cbn [snd_distinct].
    repeat split; intros r' i' H; simpl in H;
      repeat (destruct H as [H|H]; [inversion H; subst; unfold SREG; simpl; discriminate|]); destruct H.
  Qed.

  Lemma materialize1_regs_other A r r' : r' <> r -> 0 < r' -> 0 < r -> get_reg (materialize1 A r) r' = get_reg A r'.
  Proof.
    intros Hne Hz Hz'. unfold materialize1. destruct (get_reg A r); [reflexivity|].
    destruct (afresh A itv_top) as [v A'] eqn:Ea.
    unfold afresh, fresh_lin in Ea. simpl in Ea.
    unfold get_reg, set_reg. destruct (Z.eqb_spec r' 0); [lia|].
    destruct (Z.eqb_spec r 0).
    - inversion Ea; subst. reflexivity.
    - inversion Ea; subst. simpl. rewrite pm_get_set_other; [reflexivity|].
      unfold reg_key. intros X. apply Hne. lia.
  Qed.

  Lemma materialize1_reg_some A r : 0 < r -> exists e, get_reg (materialize1 A r) r = Some e.
  Proof.
    intros Hr. unfold materialize1. destruct (get_reg A r) as [e|] eqn:G0; [eauto|].
    unfold afresh, fresh_lin. simpl. unfold get_reg, set_reg. destruct (Z.eqb_spec r 0); [lia|].
    simpl. rewrite pm_get_set_same. eauto.
  Qed.

  Lemma materialize_regs_some : forall l A r,
    (forall r i, In (r, i) l -> 0 < r < 32) ->
    (In r (map fst l) \/ exists e, get_reg A r = Some e) -> 0 < r ->
    exists e, get_reg (materialize A l) r = Some e.
  Proof.
    induction l as [|[r0 i0] t IH]; intros A r Hl Hr Hz; cbn [materialize].
    - destruct Hr as [[]|H]; exact H.
    - apply IH; [intros; eapply Hl; right; eauto| |exact Hz].
      simpl in Hr. destruct (Z.eq_dec r r0) as [->|Hne].
      + right. apply materialize1_reg_some. lia.
      + destruct Hr as [[H|H]|[e He]]; [congruence|now left|].
        right. exists e. assert (0 < r0 < 32) by (eapply Hl; now left). rewrite materialize1_regs_other; auto; lia.
  Qed.

  Lemma get_reg_set_reg_other A r r' v : r' <> r -> 0 < r' -> 0 < r -> get_reg (set_reg A r v) r' = get_reg A r'.
  Proof.
    intros Hne H1 H2. unfold get_reg, set_reg. destruct (Z.eqb_spec r' 0); [lia|]. destruct (Z.eqb_spec r 0); [lia|].
    simpl. destruct v; [rewrite pm_get_set_other|rewrite pm_get_remove_other]; auto; unfold reg_key; intros X; apply Hne; lia.
  Qed.

  Lemma is_sreg_key_spec k : is_sreg_key k = true -> exists r i, In (r, i) sreg_idx /\ k = zkey r.
  Proof.
    unfold is_sreg_key. rewrite existsb_exists. intros [[r i] [Hin Hb]]. simpl in Hb. apply Pos.eqb_eq in Hb. eauto.
  Qed.

  Lemma gamma_set_pc Px Ex X p nu regs mem :
    gamma SEGS Px Ex mem0 (set_pc X p) nu regs mem -> gamma SEGS Px Ex mem0 X nu regs mem.
  Proof. intros H. destruct X. exact H. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Section Callee.
    Variable V : vunit.
    Hypothesis VIN : In V done.
    Let PV := unit_params G V.

    Lemma V_ok : unit_okS SEGS G rom V.
    Proof. rewrite Forall_forall in DONE. apply DONE. exact VIN. Qed.

    Lemma V_static :
      cstate_ok PV (u_pre V) = true /\ pre_canonical G V = true /\ forallb (cstate_ok PV) (u_exits V) = true.
    Proof.
      destruct V_ok as [ST _]. unfold unit_static_ok in ST. fold PV in ST.
      destruct (cstate_ok PV (u_pre V)); [|discriminate].
      destruct (pre_canonical G V); [|discriminate].
      destruct (forallb (fun c => pc_ok (cut_pc c) && forallb (cstate_ok PV) (cut_states c)) (u_cuts V)); [|discriminate].
      destruct (pc_ok (u_entry V)); [|discriminate].
      destruct (forallb (cstate_ok PV) (u_exits V)); [|discriminate]. auto.
    Qed.

    Variables (A : vstate) (npc : Z) (sigma : pmap lin).
    Let Am := materialize A sreg_idx.
    Let A0 := set_reg Am 1 (Some (lconst npc)).
    Let S := load_cstate (u_pre V) (u_entry V) [].
    Let sigma0 := sigma_sregs A0 sreg_idx (pm_set RA (lconst npc) pm_empty).
    Hypothesis MATCH : match_state isv_call is_sreg_key true sigma0 S A0 = MOk sigma.
    Hypothesis NPC : 0 <= npc < 2 ^ 64.

    Lemma A0_sregs r i : In (r, i) sreg_idx -> exists e, get_reg A0 r = Some e /\ pm_get (SREG i) sigma0 = Some e.
    Proof.
      intros Hin. pose proof (sreg_idx_range _ _ Hin) as Hr.
      assert (Hr1 : r <> 1).
      { unfold sreg_idx in Hin. simpl in Hin. repeat (destruct Hin as [Hin|Hin]; [inversion Hin; subst; lia|]). destruct Hin. }
      destruct (materialize_regs_some sreg_idx A r sreg_idx_range) as [e He]; [left; apply in_map_iff; exists (r, i); auto|lia|].
      exists e. split.
      - unfold A0. rewrite get_reg_set_reg_other; auto; lia.
      - unfold sigma0. eapply sigma_sregs_in; [apply sreg_idx_distinct|exact Hin|].
        unfold A0. rewrite get_reg_set_reg_other; auto; lia.
    Qed.

    Lemma sigma0_fixed s : isv_call s = false -> pm_get s sigma0 = None.
    Proof.
      intros Hs. unfold sigma0. rewrite sigma_sregs_other.
      - rewrite pm_get_set_other; [apply pm_get_empty|]. intros X. subst. cbv in Hs. discriminate.
      - intros r i Hin. unfold sreg_idx in Hin. simpl in Hin. intros X. subst s.
        repeat (destruct Hin as [Hin|Hin]; [inversion Hin; subst; cbv in Hs; discriminate|]). destruct Hin.
    Qed.

    Lemma sigma0_RA : pm_get RA sigma0 = Some (lconst npc).
    Proof.
      unfold sigma0. rewrite sigma_sregs_other; [apply pm_get_set_same|].
      intros r i Hin. unfold sreg_idx in Hin. simpl in Hin.
      repeat (destruct Hin as [Hin|Hin]; [inversion Hin; subst; discriminate|]). destruct Hin.
    Qed.

    #[using="rom done DONE VIN MATCH NPC"] Lemma callee_entry nu1 regs1 mem1 :
      gammaP A0 nu1 regs1 mem1 ->
      let nuV := vsubst nu1 sigma in
      gamma SEGS PV (callee_env npc nuV) mem0 S nuV regs1 mem1
      /\ sub_sigma sigma0 sigma /\ binds_only isv_call sigma0 sigma.
    Proof.
      intros HGm. cbv zeta.
      pose proof HGm as (HE&HMC&HF&HS&HC&HMo&HV&HR&HSl&HGl&HN&HB).
      destruct V_static as (ST1 & ST2 & ST3).
      destruct (match_state_sound SEGS P PV E (callee_env npc (vsubst nu1 sigma)) eq_refl eq_refl eq_refl
                  isv_call is_sreg_key true sigma0 S A0 sigma nu1 regs1 mem1
                  MATCH HS HC HMo HV HR HSl HGl HN) as (Sub & BO & S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8).
      { intros; eapply cstate_ok_slots; eauto. }
      { intros; eapply cstate_ok_globs; eauto. }
      split; [|split; [exact Sub|exact BO]].
      assert (UNB : forall s, isv_call s = false -> vsubst nu1 sigma s = nu1 s).
      { intros s Hs. unfold vsubst. destruct (pm_get s sigma) as [e|] eqn:Gs; [|reflexivity].
        destruct (BO _ _ Gs) as [Hg|Hv]; [rewrite (sigma0_fixed _ Hs) in Hg; discriminate|congruence]. }
      destruct (load_cstate_below (u_pre V) (u_entry V) [] (cstate_ok_wf _ _ ST1)) as [BEL J0].
      split.
      { (* [comment removed for export] *) destruct HE as (E1&E2&E3&E4&E5&E6&E7&E8&E9&E10&E11). unfold env_ok, callee_env; simpl.
        unfold P in E2, E3, E11. simpl in E2, E3, E11.
        repeat split; auto; try (ltac2:(LK.k [@NPC; @E2; @E3; @E7; @E8; @E9; @E10; @E4; @E5]); lia). }
      split; [exact HMC|].
      split.
      { (* [comment removed for export] *)
        intros s z Hfz. apply fix_val_callee in Hfz.
        destruct Hfz as [[-> ->]|[[-> ->]|[[-> ->]|[[-> ->]|[[-> ->]|[[-> ->]|(i & Hi & -> & ->)]]]]]];
          try (rewrite UNB by reflexivity; apply HF; reflexivity).
        - unfold vsubst. rewrite (Sub _ _ sigma0_RA). apply eval_lconst.
        - reflexivity. }
      split; [exact S1|]. split; [exact S2|]. split; [exact S3|]. split; [exact S4|].
      split.
      { (* [comment removed for export] *)
        intros r e Hr0 Hg. destruct (is_sreg_key (reg_key (bv_unsigned r))) eqn:SK; [|apply S5; auto].
        destruct (is_sreg_key_spec _ SK) as (ri & i & Hin & Hk).
        pose proof (sreg_idx_range _ _ Hin) as Hri.
        assert (Hrz : bv_unsigned r = ri).
        { unfold reg_key, zkey in Hk. pose proof (bv_unsigned_in_range 5 r). lia. }
        destruct (A0_sregs _ _ Hin) as (ei & Gei & Sei).
        (* [comment removed for export] *)
        unfold pre_canonical in ST2. apply andb_prop in ST2 as [ST2 _]. apply andb_prop in ST2 as [ST2 _].
        apply andb_prop in ST2 as [_ ST2].
        unfold sregs_intact in ST2. rewrite forallb_forall in ST2. specialize (ST2 _ Hin). simpl in ST2.
        unfold absval_eqb, get_reg in ST2. fold S in ST2.
        destruct (Z.eqb_spec ri 0); [lia|].
        rewrite <- Hrz in ST2. rewrite Hg in ST2. apply lin_eqb_eq in ST2. subst e.
        rewrite eval_lsym. unfold vsubst. rewrite (Sub _ _ Sei).
        apply (HR r ei Hr0). unfold get_reg in Gei. rewrite Hrz. destruct (Z.eqb_spec ri 0); [lia|]. exact Gei. }
      split; [exact S6|]. split; [exact S7|]. split; [exact S8|exact BEL].
    Qed.
  End Callee.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma sigma_joins_get : forall n j b sigma s,
    pm_get s (sigma_joins j b n sigma) =
      if Z.leb (Z.pos j) (Z.pos s) && Z.ltb (Z.pos s) (Z.pos j + Z.of_nat n)
      then Some (lsym (Z.to_pos (Z.pos b + (Z.pos s - Z.pos j)))) else pm_get s sigma.
  Proof.
    induction n as [|n IH]; intros j b sigma s; cbn [sigma_joins].
    - destruct (Z.leb_spec (Z.pos j) (Z.pos s)); destruct (Z.ltb_spec (Z.pos s) (Z.pos j + Z.of_nat 0)); simpl; try reflexivity.
      all: try (exfalso; simpl in *; lia).
    - rewrite IH. rewrite pm_get_set.
      destruct (Z.leb_spec (Z.pos (Pos.succ j)) (Z.pos s)); destruct (Z.ltb_spec (Z.pos s) (Z.pos (Pos.succ j) + Z.of_nat n));
        destruct (Pos.eqb_spec s j); destruct (Z.leb_spec (Z.pos j) (Z.pos s));
        destruct (Z.ltb_spec (Z.pos s) (Z.pos j + Z.of_nat (S n))); simpl; subst; try reflexivity; try (exfalso; lia).
      all: try (f_equal; f_equal; lia).
      all: match goal with |- ?g => idtac g end.
  Qed.

  Definition sigma_below (sigma : pmap lin) (b : positive) : Prop :=
    forall s e, pm_get s sigma = Some e -> lin_below e b = true.

  Lemma terms_subst_below sigma b : forall l acc,
    lin_below acc b = true -> sigma_below sigma b ->
    (forall s, In s (map fst l) -> pm_get s sigma = None -> (s < b)%positive) ->
    lin_below (terms_subst sigma l acc) b = true.
  Proof.
    induction l as [|[s k] t IH]; intros acc Hacc Hs Hl; simpl; [exact Hacc|].
    apply IH; [|exact Hs|intros; apply Hl; simpl; auto].
    apply lin_below_laxpy; [exact Hacc|].
    destruct (pm_get s sigma) as [e|] eqn:G0; [exact (Hs _ _ G0)|].
    apply lin_below_lsym. apply Hl; simpl; auto.
  Qed.

  Lemma lsubst_below sigma b e :
    sigma_below sigma b ->
    (forall s, In s (lsyms e) -> pm_get s sigma = None -> (s < b)%positive) ->
    lin_below (lsubst sigma e) b = true.
  Proof. intros. unfold lsubst. apply terms_subst_below; auto using lin_below_lconst. Qed.

  Lemma eval_lsubst_agree' sigma nu nu' e :
    (forall s, In s (lsyms e) -> vsubst nu sigma s = nu' s) -> eval nu (lsubst sigma e) = eval nu' e.
  Proof. intros H. rewrite eval_lsubst. apply eval_ext. exact H. Qed.


  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma set_tops_eq : forall l A, set_tops A l = set_regs A (regs_tops (vs_regs A) l).
  Proof.
    induction l as [|r t IH]; intros A; simpl.
    - destruct A; reflexivity.
    - rewrite IH. unfold set_reg. destruct (Z.eqb r 0); destruct A; reflexivity.
  Qed.

  Lemma regs_tops_get : forall l m k e,
    pm_get k (regs_tops m l) = Some e -> pm_get k m = Some e /\ forall r, In r l -> r <> 0 -> k <> reg_key r.
  Proof.
    induction l as [|r t IH]; intros m k e H; simpl in *; [auto|].
    destruct (IH _ _ _ H) as [H1 H2]. destruct (Z.eqb_spec r 0).
    - split; [exact H1|]. intros r' [<-|Hin] Hr'; [lia|auto].
    - rewrite pm_get_remove in H1. destruct (Pos.eqb_spec k (reg_key r)); [discriminate|].
      split; [exact H1|]. intros r' [<-|Hin] Hr'; auto.
  Qed.

  Lemma kill_ranges_in : forall l m x, In x (kill_ranges m l) ->
    In x m /\ forall lo hi, In (lo, hi) l -> ~ (fst x < hi /\ lo < fst x + fst (snd x)).
  Proof.
    induction l as [|[lo hi] t IH]; intros m [k [w v]] H; simpl in *; [tauto|].
    destruct (IH _ _ H) as [H1 H2]. split; [eapply cm_kill_sub; eauto|].
    intros lo' hi' [X|X]; [inversion X; subst|apply H2; auto]. simpl. eapply cm_kill_disjoint; eauto.
  Qed.

  Lemma kill_cells_in : forall l m x, In x (kill_cells m l) ->
    In x m /\ forall a n, In (a, n) l -> ~ (fst x < a + n /\ a < fst x + fst (snd x)).
  Proof.
    induction l as [|[a n] t IH]; intros m [k [w v]] H; simpl in *; [tauto|].
    destruct (IH _ _ H) as [H1 H2]. split; [eapply cm_kill_sub; eauto|].
    intros a' n' [X|X]; [inversion X; subst|apply H2; auto]. simpl. eapply cm_kill_disjoint; eauto.
  Qed.

  Lemma set_exit_slots_in sigma spoff : forall l sl x, In x (set_exit_slots sl sigma spoff l) ->
    In x sl \/ exists v0 e, In (fst x, (fst (snd x), v0)) l /\ spoff <= fst x /\ osubst_v sigma v0 = Some e /\ snd (snd x) = Some e.
  Proof.
    induction l as [|[off [w v]] t IH]; intros sl [k [w' v']] H; simpl in *; [auto|].
    destruct (Z.leb_spec spoff off).
    - destruct (IH _ _ H) as [H1|(v0 & e & A1 & A2 & A3 & A4)].
      + destruct (osubst_v sigma v) as [e'|] eqn:Ho.
        * apply cm_set_in in H1 as [H1|H1].
          -- inversion H1; subst. right. exists v, e'. simpl. auto.
          -- left. eapply cm_kill_sub; eauto.
        * left. eapply cm_kill_sub; eauto.
      + right. exists v0, e. simpl in *. auto 10.
    - destruct (IH _ _ H) as [H1|(v0 & e & A1 & A2 & A3 & A4)]; [auto|]. right. exists v0, e. simpl in *. auto 10.
  Qed.

  Lemma set_exit_globs_in sigma : forall l gl x, In x (set_exit_globs gl sigma l) ->
    In x gl \/ exists v0, In (fst x, (fst (snd x), v0)) l /\ snd (snd x) = osubst_v sigma v0.
  Proof.
    induction l as [|[a [w v]] t IH]; intros gl [k [w' v']] H; simpl in *; [auto|].
    destruct (IH _ _ H) as [H1|(v0 & A1 & A2)].
    - apply cm_set_in in H1 as [H1|H1].
      + inversion H1; subst. right. exists v. simpl. auto.
      + left. eapply cm_kill_sub; eauto.
    - right. exists v0. simpl in *. auto.
  Qed.

  Lemma add_exit_nuls_in spoff : forall l nl f, In f (add_exit_nuls nl spoff l) -> In f nl \/ In f l.
  Proof.
    unfold add_exit_nuls. induction l as [|g t IH]; intros nl f H; simpl in *; [auto|].
    destruct (IH _ _ H) as [H1|H1]; [|auto].
    destruct (Z.leb spoff (fst g)); [|auto]. destruct (nul_implied nl g); [auto|].
    destruct H1 as [<-|H1]; auto.
  Qed.

  Lemma set_exit_valsets_get sigma : forall l vs s' zs, pm_get s' (set_exit_valsets vs sigma l) = Some zs ->
    pm_get s' vs = Some zs \/ exists s, In (s, zs) l /\ sym_image sigma s = Some s' /\ pm_mem s sigma = true.
  Proof.
    induction l as [|[s0 zs0] t IH]; intros vs s' zs H; simpl in *; [auto|].
    destruct (IH _ _ _ H) as [H1|(s & A1 & A2 & A3)]; [|right; exists s; auto].
    destruct (sym_image sigma s0) as [s1|] eqn:SI; [|auto].
    destruct (pm_mem s0 sigma) eqn:PM; [|auto].
    rewrite pm_get_set in H1. destruct (Pos.eqb_spec s' s1); [|auto].
    inversion H1; subst. right. exists s0. auto.
  Qed.

  Lemma vs_next_set_tops A l : vs_next (set_tops A l) = vs_next A.
  Proof. rewrite set_tops_eq. reflexivity. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Section PostCall.
    Variable V : vunit.
    Hypothesis VIN : In V done.
    Let PV := unit_params G V.
    Variables (A : vstate) (spoff npc : Z) (sigma : pmap lin).
    Let Am := materialize A sreg_idx.
    Let A0 := set_reg Am 1 (Some (lconst npc)).
    Let S := load_cstate (u_pre V) (u_entry V) [].
    Let sigma0 := sigma_sregs A0 sreg_idx (pm_set RA (lconst npc) pm_empty).
    Hypothesis MATCH : match_state isv_call is_sreg_key true sigma0 S A0 = MOk sigma.
    Hypothesis NPC : 0 <= npc < 2 ^ 64.
    Hypothesis SIGB : sigma_below sigma (vs_next A0).
    Hypothesis FP : footprint_ok D V spoff = true.
    Hypothesis ROOT : u_root V = None.
    Hypothesis SPO : sp_offset A = Some spoff.
    Hypothesis PO : params_ok SEGS P.

    Variables (nu1 : val) (regs1 : bvmap 5 word) (mem1 : word -> option byte).
    Hypothesis HGm : gammaP A0 nu1 regs1 mem1.
    Let nuV := vsubst nu1 sigma.
    Let EV := callee_env npc nuV.

    (* [comment removed for export] *)
    Variables (X : cstate) (nuV' : val) (regs2 : bvmap 5 word) (mem2 : word -> option byte).
    Let SX := load_cstate X npc [].
    Hypothesis XIN : In X (u_exits V).
    Hypothesis XG : gamma SEGS PV EV mem0 SX nuV' regs2 mem2.
    Hypothesis XEXT : ext JOIN0 nuV nuV'.
    Hypothesis XRA : getr regs2 1%bv = wordZ npc.
    Hypothesis XREGS : exit_regs G V nuV regs2.
    Hypothesis XFM : frame_mod mem1 mem2 (unit_regions PV EV).

    Let B := call_base D A0 V spoff npc.
    (* [comment removed for export] *)
    Variables (b b' : positive) (nJ : nat).
    Hypothesis HB : b = vs_next A0.
    Hypothesis HJ0 : (JOIN0 <= b)%positive.      (* [comment removed for export] *)
    Hypothesis NX : Z.pos (cs_next X) = Z.pos JOIN0 + Z.of_nat nJ.
    Hypothesis HB' : Z.pos b' = Z.pos b + Z.of_nat nJ.
    Let sigmax := sigma_joins JOIN0 b nJ sigma.
    Definition nu2 : val := fun s =>
      let k := Z.pos s - Z.pos b in
      if Z.leb 0 k && Z.ltb k (Z.of_nat nJ) then nuV' (Z.to_pos (Z.pos JOIN0 + k)) else nu1 s.

    Lemma call_facts : sub_sigma sigma0 sigma /\ binds_only isv_call sigma0 sigma
                       /\ gamma SEGS PV EV mem0 S nuV regs1 mem1.
    Proof.
      destruct (callee_entry V VIN A npc sigma MATCH NPC nu1 regs1 mem1 HGm) as (G1 & G2 & G3). auto.
    Qed.

    Lemma X_static : cstate_ok PV X = true.
    Proof.
      destruct (V_static V VIN) as (_ & _ & ST3). rewrite forallb_forall in ST3. apply ST3. exact XIN.
    Qed.

    Lemma nu2_old s : (s < b)%positive -> nu2 s = nu1 s.
    Proof. intros Hs. unfold nu2. destruct (Z.leb_spec 0 (Z.pos s - Z.pos b)) as [Y|Y]; [exfalso; clear -Hs Y; lia|reflexivity]. Qed.

    Lemma nu2_join s : (JOIN0 <= s)%positive -> (s < cs_next X)%positive ->
      vsubst nu2 sigmax s = nuV' s.
    Proof.
      intros H1 H2. unfold vsubst, sigmax, nu2. rewrite sigma_joins_get.
      destruct (Z.leb_spec (Z.pos JOIN0) (Z.pos s)); [|lia]. destruct (Z.ltb_spec (Z.pos s) (Z.pos JOIN0 + Z.of_nat nJ)); [|lia].
      simpl. rewrite eval_lsym.
      replace (Z.pos (Z.to_pos (Z.pos b + (Z.pos s - Z.pos JOIN0))) - Z.pos b) with (Z.pos s - Z.pos JOIN0) by lia.
      destruct (Z.leb_spec 0 (Z.pos s - Z.pos JOIN0)); [|lia]. destruct (Z.ltb_spec (Z.pos s - Z.pos JOIN0) (Z.of_nat nJ)); [|lia].
      simpl. f_equal. lia.
    Qed.

    (* [comment removed for export] *)
    Lemma lsubst_eval_x e :
      lin_below e (cs_next X) = true -> eval nu2 (lsubst sigmax e) = eval nuV' e.
    Proof.
      intros Hb. destruct call_facts as (Sub & BO & GV).
      apply eval_lsubst_agree'. intros s Hs.
      pose proof (proj1 (lin_below_iff _ _) Hb s Hs) as Hsb.
      destruct (Pos.ltb_spec s JOIN0) as [Hlo|Hhi]; [|apply nu2_join; auto].
      unfold vsubst, sigmax. rewrite sigma_joins_get.
      destruct (Z.leb_spec (Z.pos JOIN0) (Z.pos s)); [lia|]. simpl.
      rewrite (XEXT s Hlo). unfold nuV, vsubst.
      destruct (pm_get s sigma) as [es|] eqn:Gs.
      - apply eval_ext. intros s' Hs'. apply nu2_old. rewrite HB. exact (proj1 (lin_below_iff _ _) (SIGB _ _ Gs) s' Hs').
      - apply nu2_old. clear -Hlo HJ0. unfold JOIN0 in *. lia.
    Qed.

    Lemma osubst_eval e e' :
      lin_below e (cs_next X) = true -> osubst sigmax e = Some e' -> eval nu2 e' = eval nuV' e.
    Proof.
      intros Hb Ho. unfold osubst in Ho.
      match type of Ho with (if ?c then _ else _) = _ => destruct c; [|discriminate] end.
      inversion Ho; subst e'. apply lsubst_eval_x; auto.
    Qed.

    Lemma nu2_new s : (JOIN0 <= s)%positive -> (s < cs_next X)%positive ->
      nu2 (Z.to_pos (Z.pos b + (Z.pos s - Z.pos JOIN0))) = nuV' s.
    Proof.
      intros H1 H2.  unfold nu2.
      replace (Z.pos (Z.to_pos (Z.pos b + (Z.pos s - Z.pos JOIN0))) - Z.pos b) with (Z.pos s - Z.pos JOIN0) by lia.
      destruct (Z.leb_spec 0 (Z.pos s - Z.pos JOIN0)); [|lia]. destruct (Z.ltb_spec (Z.pos s - Z.pos JOIN0) (Z.of_nat nJ)); [|lia].
      simpl. f_equal. lia.
    Qed.

    Lemma ext_b : ext b nu1 nu2.
    Proof. intros s Hs. apply nu2_old. exact Hs. Qed.

    Lemma XBEL : state_below SX.
    Proof. exact (proj1 (load_cstate_below X npc [] (cstate_ok_wf _ _ X_static))). Qed.

    #[using="A npc Am A0 NPC SIGB X HB HJ0 HB'"] Lemma sigmax_below : sigma_below sigmax b'.
    Proof.
      intros s e. unfold sigmax. rewrite sigma_joins_get. 
      destruct (Z.leb (Z.pos JOIN0) (Z.pos s) && Z.ltb (Z.pos s) (Z.pos JOIN0 + Z.of_nat nJ)) eqn:C.
      - intros Y; inversion Y; subst e. apply lin_below_lsym. apply andb_prop in C as [C1 C2].
        apply Z.leb_le in C1. apply Z.ltb_lt in C2. lia.
      - intros Gs. eapply lin_below_mono; [|exact (SIGB _ _ Gs)]. subst b. (ltac2:(LK.k [@NPC; @HB']); lia).
    Qed.

    #[using="A npc Am A0 NPC SIGB HB HJ0 NX HB'"] Lemma lsubst_x_below e : lin_below e (cs_next X) = true -> lin_below (lsubst sigmax e) b' = true.
    Proof.
      intros Hb. apply lsubst_below; [apply sigmax_below|].  
      intros s Hs Hn. pose proof (proj1 (lin_below_iff _ _) Hb s Hs).
      unfold sigmax in Hn. rewrite sigma_joins_get in Hn.
      destruct (Z.leb_spec (Z.pos JOIN0) (Z.pos s)); destruct (Z.ltb_spec (Z.pos s) (Z.pos JOIN0 + Z.of_nat nJ)); simpl in Hn; try discriminate; subst b; (ltac2:(LK.k [@NPC; @NX; @H; @H1; @HJ0; @HB']); LKcb; lia).
    Qed.

    Lemma osubst_below e e' : lin_below e (cs_next X) = true -> osubst sigmax e = Some e' -> lin_below e' b' = true.
    Proof.
      intros Hb Ho. unfold osubst in Ho.
      match type of Ho with (if ?c then _ else _) = _ => destruct c; [|discriminate] end.
      inversion Ho; subst e'. apply lsubst_x_below; auto.
    Qed.

    (* [comment removed for export] *)
    Lemma store_below_add_in_itv S0 c i S1 :
      store_below S0 b' = true -> lin_below c b' = true -> add_in_itv S0 c i = Some S1 -> store_below S1 b' = true.
    Proof.
      intros H1 H2. unfold add_in_itv.
      destruct (snd i) as [hi|].
      - destruct (add_constraint S0 (laddc c (- hi))) as [S2|] eqn:E1; [|discriminate].
        pose proof (store_below_add_constraint _ _ _ _ H1 (lin_below_laddc _ _ _ H2) E1) as H3.
        destruct (fst i) as [lo|]; [|intros Y; inversion Y; now subst].
        intros E2. eapply store_below_add_constraint; [exact H3| |exact E2].
        apply lin_below_laddc, lin_below_lneg, H2.
      - destruct (fst i) as [lo|]; [|intros Y; inversion Y; now subst].
        intros E2. eapply store_below_add_constraint; [exact H1| |exact E2].
        apply lin_below_laddc, lin_below_lneg, H2.
    Qed.

    Lemma add_boxes_sound : forall l S0,
      sat nu2 S0 -> store_below S0 b' = true ->
      (forall s i, In (s, i) l -> pm_get s (sbox (vs_store SX)) = Some i) ->
      exists S1, add_boxes S0 sigmax l = Some S1 /\ sat nu2 S1 /\ store_below S1 b' = true.
    Proof.
      induction l as [|[s i] t IH]; intros S0 HS HSB Hl; simpl; [eauto|].
      assert (Hsi : pm_get s (sbox (vs_store SX)) = Some i) by (apply Hl; now left).
      assert (Hin : in_itv (nuV' s) i).
      { destruct XG as (_&_&_&XS&_). exact (sat_box _ _ XS _ _ Hsi). }
      assert (Hs : (s < cs_next X)%positive).
      { destruct XBEL as (_&SB&_). eapply store_below_sound; [exact SB|]. left. eauto. }
     
      destruct (isv_join s) eqn:J.
      - unfold isv_join in J. apply Pos.leb_le in J.
        unfold sigmax at 1. rewrite sigma_joins_get.
        destruct (Z.leb_spec (Z.pos JOIN0) (Z.pos s)); [|lia]. destruct (Z.ltb_spec (Z.pos s) (Z.pos JOIN0 + Z.of_nat nJ)); [|lia].
        simpl. apply IH; [| |intros; apply Hl; now right].
        + apply sat_set_box; [exact HS|]. rewrite nu2_new; auto.
        + apply store_below_set_box; [exact HSB|]. clear -H H0 HB' NX J Hs. unfold JOIN0 in *. lia.
      - destruct (osubst sigmax (lsym s)) as [e|] eqn:Ho; [|apply IH; auto; intros; apply Hl; now right].
        assert (He : eval nu2 e = nuV' s).
        { rewrite (osubst_eval _ _ (lin_below_lsym _ _ Hs) Ho). apply eval_lsym. }
        destruct (sat_add_in_itv nu2 S0 e i HS) as [S1 [E1 HS1]]; [rewrite He; exact Hin|].
        rewrite E1. apply IH; [exact HS1| |intros; apply Hl; now right].
        eapply store_below_add_in_itv; [exact HSB| |exact E1]. eapply osubst_below; [apply lin_below_lsym; exact Hs|exact Ho].
    Qed.

    Lemma add_congs_sound : forall l S0,
      sat nu2 S0 -> store_below S0 b' = true ->
      (forall s mr, In (s, mr) l -> pm_get s (scong (vs_store SX)) = Some mr) ->
      exists S1, add_congs S0 sigmax l = Some S1 /\ sat nu2 S1 /\ store_below S1 b' = true.
    Proof.
      induction l as [|[s [m r]] t IH]; intros S0 HS HSB Hl; simpl; [eauto|].
      assert (Hsi : pm_get s (scong (vs_store SX)) = Some (m, r)) by (apply Hl; now left).
      assert (Hd : (m | nuV' s - r)).
      { destruct XG as (_&_&_&XS&_). exact (sat_cong _ _ XS _ _ _ Hsi). }
      assert (Hs : (s < cs_next X)%positive).
      { destruct XBEL as (_&SB&_). eapply store_below_sound; [exact SB|]. right; right. eauto. }
     
      destruct (isv_join s) eqn:J; [|apply IH; auto; intros; apply Hl; now right].
      unfold isv_join in J. apply Pos.leb_le in J.
      unfold sigmax at 1. rewrite sigma_joins_get.
      destruct (Z.leb_spec (Z.pos JOIN0) (Z.pos s)); [|lia]. destruct (Z.ltb_spec (Z.pos s) (Z.pos JOIN0 + Z.of_nat nJ)); [|lia].
      simpl.
      destruct (sat_add_cong nu2 S0 (Z.to_pos (Z.pos b + (Z.pos s - Z.pos JOIN0))) m r HS) as [S1 [E1 HS1]]; [rewrite nu2_new; auto|].
      rewrite E1. apply IH; [exact HS1| |intros; apply Hl; now right].
      eapply store_below_add_cong; [exact HSB| |exact E1]. clear -H H0 HB' NX J Hs. unfold JOIN0 in *. lia.
    Qed.

    Lemma add_conss_sound : forall l S0,
      sat nu2 S0 -> store_below S0 b' = true ->
      (forall c, In c l -> In c (scons (vs_store SX))) ->
      exists S1, add_conss S0 sigmax l = Some S1 /\ sat nu2 S1 /\ store_below S1 b' = true.
    Proof.
      induction l as [|c t IH]; intros S0 HS HSB Hl; simpl; [eauto|].
      assert (Hc : In c (scons (vs_store SX))) by (apply Hl; now left).
      assert (Hle : eval nuV' c <= 0).
      { destruct XG as (_&_&_&XS&_). exact (sat_cons_in _ _ _ XS Hc). }
      assert (Hcb : lin_below c (cs_next X) = true).
      { destruct XBEL as (_&SB&_). apply (proj2 (lin_below_iff _ _)). intros s Hs.
        eapply store_below_sound; [exact SB|]. right; left. eauto. }
      destruct (osubst sigmax c) as [c'|] eqn:Ho; [|apply IH; auto; intros; apply Hl; now right].
      pose proof (osubst_eval _ _ Hcb Ho) as He.
      destruct (lin_is_const c') eqn:Hk.
      - rewrite (eval_is_const nu2 c' Hk) in He.
        destruct (Z.leb_spec (lc c') 0); [|lia]. apply IH; auto. intros; apply Hl; now right.
      - destruct (sat_add_constraint nu2 S0 c' HS) as [S1 [E1 HS1]]; [lia|].
        rewrite E1. apply IH; [exact HS1| |intros; apply Hl; now right].
        eapply store_below_add_constraint; [exact HSB| |exact E1]. eapply osubst_below; eauto.
    Qed.

    (* [comment removed for export] *)
    Lemma conddef_ext (m : pmap (ckind * lin * lin)) nu nu' (bnd : positive) :
      (forall bb k x y, pm_get bb m = Some (k, x, y) -> nu bb = (if cond_holds k (eval nu x) (eval nu y) then 1 else 0)) ->
      (forall bb k x y, pm_get bb m = Some (k, x, y) -> (bb < bnd)%positive /\ lin_below x bnd = true /\ lin_below y bnd = true) ->
      ext bnd nu nu' ->
      forall bb k x y, pm_get bb m = Some (k, x, y) -> nu' bb = (if cond_holds k (eval nu' x) (eval nu' y) then 1 else 0).
    Proof.
      intros H1 H2 HX bb k x y Hg. destruct (H2 _ _ _ _ Hg) as (B1&B2&B3).
      rewrite (HX bb B1), (eval_ext_below _ _ _ _ HX B2), (eval_ext_below _ _ _ _ HX B3). apply H1; auto.
    Qed.

    Lemma moddef_ext (m : pmap (lin * Z)) nu nu' (bnd : positive) :
      (forall r x md, pm_get r m = Some (x, md) -> 0 < md /\ nu r = eval nu x mod md) ->
      (forall r x md, pm_get r m = Some (x, md) -> (r < bnd)%positive /\ lin_below x bnd = true) ->
      ext bnd nu nu' ->
      forall r x md, pm_get r m = Some (x, md) -> 0 < md /\ nu' r = eval nu' x mod md.
    Proof.
      intros H1 H2 HX r x md Hg. destruct (H2 _ _ _ Hg) as (B1&B2). destruct (H1 _ _ _ Hg) as [C1 C2].
      rewrite (HX r B1), (eval_ext_below _ _ _ _ HX B2). auto.
    Qed.

    (* [comment removed for export] *)
    Lemma kept_reg (r : reg) e :
      rz r <> 0 -> (rz r = 2 \/ rz r = 3 \/ rz r = 4 \/ In (rz r) (map fst sreg_idx)) ->
      pm_get (reg_key (rz r)) (vs_regs A0) = Some e ->
      bv_unsigned (getr regs2 r) = zwrap 64 (eval nu1 e).
    Proof.
      intros Hr0 Hin Hg.
      destruct call_facts as (Sub & BO & GV).
      pose proof HGm as (_&_&_&_&_&_&_&HR&_). rewrite <- (HR r e Hr0 Hg).
      pose proof GV as (_&_&_&_&_&_&_&GR&_).
      destruct (V_static V VIN) as (_ & PC & _). unfold pre_canonical in PC.
      apply andb_prop in PC as [PC P4]. apply andb_prop in PC as [PC P3]. apply andb_prop in PC as [PC P5]. apply andb_prop in PC as [P1 P2].
      fold S in P2, P3, P4, P5.
      destruct XREGS as (X2 & X3 & X4 & X5).
      assert (GETS : forall (z : Z) (l : lin), rz r = z -> absval_eqb (get_reg S z) l = true ->
                     bv_unsigned (getr regs1 r) = zwrap 64 (eval nuV l)).
      { intros z l Hz Hb. unfold absval_eqb, get_reg in Hb. rewrite <- Hz in Hb.
        destruct (Z.eqb_spec (rz r) 0); [lia|].
        destruct (pm_get (reg_key (rz r)) (vs_regs S)) as [l'|] eqn:G'; [|discriminate]. apply lin_eqb_eq in Hb. subst l'.
        exact (GR r l Hr0 G'). }
      destruct Hin as [H|[H|[H|Hin]]].
      - assert (r = 2%bv) by (apply bv_eq; unfold rz in H; rewrite H; reflexivity). subst r.
        rewrite (GETS 2 _ eq_refl P2), eval_lsymc. exact X2.
      - assert (r = 3%bv) by (apply bv_eq; unfold rz in H; rewrite H; reflexivity). subst r.
        rewrite (GETS 3 _ eq_refl P3), eval_lsym. exact X3.
      - assert (r = 4%bv) by (apply bv_eq; unfold rz in H; rewrite H; reflexivity). subst r.
        rewrite (GETS 4 _ eq_refl P4), eval_lconst. exact X4.
      - apply in_map_iff in Hin as [[ri i] [Hri Hin]]. simpl in Hri. subst ri.
        unfold sregs_intact in P5. rewrite forallb_forall in P5. specialize (P5 _ Hin). simpl in P5.
        rewrite (GETS _ _ eq_refl P5), eval_lsym.
        assert (r = Z_to_bv 5 (rz r)) by (apply bv_eq; rewrite Z_to_bv_unsigned; symmetry; apply bv_wrap_small; apply bv_unsigned_in_range).
        rewrite H. apply X5. exact Hin.
    Qed.

    Lemma in_CALLER_SAVED_dec (z : Z) : 0 < z < 32 ->
      In z CALLER_SAVED \/ (z = 2 \/ z = 3 \/ z = 4 \/ In z (map fst sreg_idx)).
    Proof.
      intros Hz. unfold CALLER_SAVED, sreg_idx. simpl.
      assert (H : z = 1 \/ z = 2 \/ z = 3 \/ z = 4 \/ z = 5 \/ z = 6 \/ z = 7 \/ z = 8 \/ z = 9 \/ z = 10 \/ z = 11 \/ z = 12 \/ z = 13
                  \/ z = 14 \/ z = 15 \/ z = 16 \/ z = 17 \/ z = 18 \/ z = 19 \/ z = 20 \/ z = 21 \/ z = 22 \/ z = 23 \/ z = 24
                  \/ z = 25 \/ z = 26 \/ z = 27 \/ z = 28 \/ z = 29 \/ z = 30 \/ z = 31) by lia.
      repeat (destruct H as [H|H]; [subst; tauto|]). subst; tauto.
    Qed.

    (* [comment removed for export] *)
    Lemma wcells_V_in_P c : In c (vp_wcells PV) -> exists c', In c' (vp_wcells P) /\ fst c' <= fst c /\ fst c + snd c <= fst c' + snd c'.
    Proof.
      unfold PV, P, unit_params, unit_wcells. simpl. intros Hin.
      unfold footprint_ok in FP. apply andb_prop in FP as [FP FE]. apply andb_prop in FP as [FP FG].
      apply in_app_iff in Hin as [Hin|Hin].
      - destruct (u_errno V) eqn:EV'; [|destruct Hin]. simpl in FE. destruct Hin as [<-|[]].
        destruct (u_errno U) eqn:EU; [|discriminate].
        exists (ci_errno (ge_CI G), 4). simpl. split; [|lia]. now left.
      - rewrite forallb_forall in FG. specialize (FG _ Hin). apply in_cells_sound in FG as [c' (H1&H2&H3)].
        exists c'. auto.
    Qed.

    (* [comment removed for export] *)
    #[using="SEGS done mem0 D A Am A0 NPC FP PO regs1 mem1 HGm X b b' nJ HB"] Lemma outside_V (a len : Z) :
      0 <= a -> a + len <= 2 ^ 64 -> 0 <= len ->
      (e_sp0 E + spoff <= a \/ a + len <= e_sp0 E - vp_frame P) ->
      (forall lo hi, In (lo, hi) (u_wstack V) -> a + len <= e_sp0 E + lo \/ e_sp0 E + hi <= a) ->
      (forall c, In c (vp_wcells PV) -> a + len <= fst c \/ fst c + snd c <= a) ->
      forall i, 0 <= i < len -> outside (wordZ (a + i)) (unit_regions PV EV).
    Proof.
      intros Ha Hal Hlen Hst Hws Hwc i Hi.
      pose proof HGm as (HE&_). destruct HE as (E1&E2&E3&E4&E5&E6&E7&E8&E9&E10&E11). unfold P in E2, E11. simpl in E2, E11.
      pose proof PO as (P0&P1&_). unfold P in P0, P1; simpl in P0, P1.
      unfold unit_regions. apply outside_app. split.
      - unfold PV, unit_params. cbn [vp_wstack]. unfold EV, callee_env. cbn [e_sp0].
        unfold footprint_ok in FP. apply andb_prop in FP as [FP _]. apply andb_prop in FP as [FP FW]. apply andb_prop in FP as [FP FS].
        apply andb_prop in FP as [F1 F2]. apply Z.leb_le in F1. apply Z.eqb_eq in F2.
        simpl. split.
        + unfold in_rng. rewrite !u_wordZ by (ltac2:(LK.k [@NPC; @HB; @Hi; @E1; @E2; @E3; @E4; @E5; @E7; @E8; @E9; @E10; @E11; @P0; @P1; @Ha; @Hal]); lia). unfold P in Hst; simpl in Hst. lia.
        + pose proof PO as (_&_&_&_&_&PW&_). unfold P in PW; simpl in PW.
          rewrite forallb_forall in FS.
          assert (GENW : forall l,
                    (forall lo hi, In (lo, hi) l -> a + len <= e_sp0 E + lo \/ e_sp0 E + hi <= a) ->
                    (forall r, In r l -> in_ranges (vp_wstack (de_P D)) (fst r) (snd r - fst r) = true) ->
                    outside (wordZ (a + i)) (map (fun r : Z * Z => (wordZ (e_sp0 E + fst r), snd r - fst r)) l)).
          { induction l as [|[lo hi] t IH]; intros Hl1 Hl2; simpl; [exact I|].
            split; [|apply IH; intros; [apply Hl1|apply Hl2]; simpl; auto].
            unfold in_rng. pose proof (Hl1 lo hi ltac:(now left)) as Hr.
            pose proof (Hl2 (lo, hi) ltac:(now left)) as FW1. cbn [fst snd] in FW1.
            apply in_ranges_sound in FW1 as (lo' & hi' & Hin' & L1 & L2).
            change (de_P D) with P in Hin'. unfold P, unit_params in Hin'. cbn [vp_wstack] in Hin'.
            assert (HW : - vp_frame (ge_P0 G) <= lo' /\ hi' <= 0).
            { exact (PW _ Hin'). }
            pose proof (bv_unsigned_in_range 64 (wordZ (e_sp0 E + lo))) as BR.
            rewrite (u_wordZ (a + i)) by lia.
            destruct (Z.lt_decidable lo hi) as [Hlh|Hlh]; [|lia].
            rewrite !u_wordZ by lia. lia. }
          apply GENW; [exact Hws|exact FS].
      - unfold cells_regions. 
        assert (GEN : forall l, (forall c, In c l -> In c (vp_wcells PV)) ->
                       outside (wordZ (a + i)) (map (fun c : Z * Z => (wordZ (fst c), snd c)) l)).
        { induction l as [|c t IH]; intros Hl; simpl; [exact I|]. split; [|apply IH; intros; apply Hl; now right].
          pose proof (Hl c ltac:(now left)) as HcV. specialize (Hwc _ HcV).
          destruct (wcells_V_in_P _ HcV) as [c' (C1&C2&C3)].
          pose proof PO as (_&_&_&PF&PWC&_). destruct (PWC _ C1) as [f (F1&F2&F3)]. destruct (PF _ F1) as (G1&G2&_).
          unfold P in G2; simpl in G2.
          unfold in_rng. pose proof (bv_unsigned_in_range 64 (wordZ (fst c))) as BR.
          rewrite (u_wordZ (a + i)) by lia.
          destruct (Z.lt_decidable 0 (snd c)) as [Hc0|Hc0]; [|lia].
          rewrite !u_wordZ by (ltac2:(LK.k [@NPC; @HB; @Hi; @E1; @E2; @E3; @E4; @E5; @E7; @E8; @E9; @E10; @E11; @P0; @P1; @C2; @C3; @F2; @F3; @G1; @G2; @BR; @Hc0]); lia). lia. }
        apply GEN. auto.
    Qed.

    Lemma rdn_unchanged (a : Z) (n : nat) :
      0 <= a < 2 ^ 64 -> a + Z.of_nat n <= 2 ^ 64 ->
      (e_sp0 E + spoff <= a \/ a + Z.of_nat n <= e_sp0 E - vp_frame P) ->
      (forall lo hi, In (lo, hi) (u_wstack V) -> a + Z.of_nat n <= e_sp0 E + lo \/ e_sp0 E + hi <= a) ->
      (forall c, In c (vp_wcells PV) -> a + Z.of_nat n <= fst c \/ fst c + snd c <= a) ->
      rdn SEGS mem2 (wordZ a) n = rdn SEGS mem1 (wordZ a) n.
    Proof.
      intros. eapply frame_mod_rdn; [exact XFM| |rewrite u_wordZ by lia; lia].
      intros i Hi. rewrite u_wordZ by lia. eapply outside_V; eauto; lia.
    Qed.

    Lemma call_base_shape (Ax : vstate) :
      let Bx := call_base D Ax V spoff npc in
      vs_store Bx = vs_store Ax /\ vs_next Bx = vs_next Ax /\ vs_conddef Bx = vs_conddef Ax /\ vs_moddef Bx = vs_moddef Ax
      /\ vs_valset Bx = vs_valset Ax /\ vs_pc Bx = npc
      /\ vs_regs Bx = pm_set (reg_key 1) (lconst npc) (regs_tops (vs_regs Ax) CALLER_SAVED)
      /\ vs_slots Bx = kill_ranges (cm_kill (vs_slots Ax) STACK_BOTTOM spoff) (u_wstack V)
      /\ vs_globs Bx = (let gl0 := kill_cells (vs_globs Ax) (u_wglobs V) in
                        if u_errno V then cm_kill gl0 (ci_errno (ge_CI (de_G D))) (ci_errno (ge_CI (de_G D)) + 4) else gl0)
      /\ vs_nul Bx = List.filter (nul_survives spoff (u_wstack V)) (vs_nul Ax).
    Proof. repeat split; reflexivity. Qed.

    Lemma wcells_PV_bound c : In c (vp_wcells PV) -> 0 <= fst c /\ fst c + snd c <= vp_splo P - vp_frame P.
    Proof.
      intros Hc. destruct (wcells_V_in_P _ Hc) as [c' (C1&C2&C3)].
      pose proof PO as (_&_&_&PF&PWC&_). destruct (PWC _ C1) as [f (F1&F2&F3)]. destruct (PF _ F1) as (G1&G2&_). lia.
    Qed.

    Lemma wstack_V_bound lo hi : In (lo, hi) (u_wstack V) -> - vp_frame P <= lo.
    Proof.
      intros Hin. pose proof FP as FQ. unfold footprint_ok in FQ.
      apply andb_prop in FQ as [FQ _]. apply andb_prop in FQ as [FQ _]. apply andb_prop in FQ as [_ FS].
      rewrite forallb_forall in FS. specialize (FS _ Hin). cbn [fst snd] in FS.
      apply in_ranges_sound in FS as (lo' & hi' & Hin' & L1 & L2).
      pose proof PO as (_&_&_&_&_&PW&_). specialize (PW _ Hin'). simpl in PW. unfold P; simpl. lia.
    Qed.

    Lemma lin_single_in e s k : lin_single e = Some (s, k) -> In s (lsyms e).
    Proof. unfold lin_single, lsyms. destruct (lt e) as [|[s' k'] [|? ?]]; try discriminate. intros Y; inversion Y; subst. now left. Qed.

    Lemma reg_upd_get m r v k e :
      pm_get k (reg_upd m r v) = Some e ->
      (k = reg_key r /\ v = Some e) \/ (k <> reg_key r /\ pm_get k m = Some e).
    Proof.
      unfold reg_upd. destruct v as [e'|]; [rewrite pm_get_set|rewrite pm_get_remove]; destruct (Pos.eqb_spec k (reg_key r)); intros Hg.
      - left. inversion Hg; subst; auto.
      - right; auto.
      - discriminate.
      - right; auto.
    Qed.

    Lemma reg_key_eq a1 a2 : 0 < a1 -> 0 < a2 -> reg_key a1 = reg_key a2 -> a1 = a2.
    Proof. unfold reg_key. intros. lia. Qed.

    Lemma rz_pos_of (r : reg) : rz r <> 0 -> 0 < rz r < 32.
    Proof. intros H. pose proof (bv_unsigned_in_range 5 r) as R. unfold bv_modulus in R. unfold rz in *. simpl in R. lia. Qed.

    #[using="rom DONE VIN PV S sigma0 MATCH NPC SIGB FP PO regs1 mem1 HGm nuV EV XIN XG XEXT XRA XREGS XFM HB HJ0 NX HB' sigmax"] Theorem apply_exit_sound :
      exists B', apply_exit B sigma spoff SX = Some B' /\ (vstate_below_b B' = true -> gammaP B' nu2 regs2 mem2)
                 /\ vs_pc B' = npc /\ vs_next B' = b'.
    Proof.
      destruct call_facts as (Sub & BO & GV).
      pose proof HGm as (HE&HMC&HF&HS&HC&HMo&HV&HR&HSl&HGl&HN&HB0). pose proof HB0 as (B10&B11&B12&B13&B14&(B15&B16&B17)).
      pose proof XG as (_&XMC&_&XS&_&_&XV&XR&XSl&XGl&XN&_). pose proof XBEL as (Y10&Y11&Y12&Y13&Y14&(Y15&Y16&Y17)).
      (* [comment removed for export] *)
      assert (B10b : (LAST_FIXED < b)%positive) by (rewrite HB; exact B10). clear B10 Y10.
      destruct (call_base_shape A0) as (Q1&Q2&Q3&Q4&Q5&Q6&Q7&Q8&Q9&Q10). fold B in Q1, Q2, Q3, Q4, Q5, Q6, Q7, Q8, Q9, Q10.
      pose proof HE as (E1&E2&E3&E4&E5&E6&E7&E8&E9&E10&E11). unfold P in E2, E11; simpl in E2, E11.
      pose proof PO as (P0&P1&_). unfold P in P0, P1; simpl in P0, P1.
      assert (HPf : vp_frame P = vp_frame (ge_P0 G)) by reflexivity.
      assert (HPs : vp_splo P = vp_splo (ge_P0 G)) by reflexivity.
      assert (EnJ : (Pos.to_nat (vs_next SX) - Pos.to_nat JOIN0)%nat = nJ).
      { unfold SX. simpl. clear -NX. unfold JOIN0 in *. lia. }
      assert (Eb' : Pos.of_nat (Pos.to_nat b + nJ) = b') by (clear -HB'; lia).
      assert (SAT0 : sat nu2 (vs_store A0)).
      { eapply sat_ext; [|exact HS]. intros s Hs. symmetry. apply nu2_old. rewrite HB. eapply store_below_sound; eauto. }
      assert (SB0 : store_below (vs_store A0) b' = true).
      { eapply store_below_mono; [|exact B11]. rewrite <- HB. clear -HB'; lia. }
      unfold apply_exit. rewrite Q2, <- HB, EnJ, Eb'. fold sigmax. cbn [vs_store set_next]. rewrite Q1.
      destruct (add_boxes_sound (pm_elements (sbox (vs_store SX))) (vs_store A0) SAT0 SB0) as (S1 & E1' & SAT1 & SB1);
        [intros; apply pm_elements_sound; auto|]. rewrite E1'.
      destruct (add_congs_sound (pm_elements (scong (vs_store SX))) S1 SAT1 SB1) as (S2 & E2' & SAT2 & SB2);
        [intros; apply pm_elements_sound; auto|]. rewrite E2'.
      destruct (add_conss_sound (scons (vs_store SX)) S2 SAT2 SB2) as (S3 & E3' & SAT3 & SB3); [auto|]. rewrite E3'.
      eexists. split; [reflexivity|].
      (* [comment removed for export] *)
      match goal with |- (_ -> gammaP ?Bf _ _ _) /\ _ => set (BF := Bf) end.
      assert (FS : vs_store BF = S3) by reflexivity.
      assert (FN : vs_next BF = b') by reflexivity.
      assert (FPc : vs_pc BF = npc) by reflexivity.
      split; [|split; [exact FPc|exact FN]].
      assert (FC : vs_conddef BF = vs_conddef A0) by reflexivity.
      assert (FM : vs_moddef BF = vs_moddef A0) by reflexivity.
      assert (FV : vs_valset BF = set_exit_valsets (vs_valset A0) sigmax (pm_elements (vs_valset SX))) by reflexivity.
      assert (FR : vs_regs BF = reg_upd (reg_upd (vs_regs B) 10 (osubst_v sigmax (get_reg SX 10))) 11 (osubst_v sigmax (get_reg SX 11))) by reflexivity.
      assert (FSl : vs_slots BF = set_exit_slots (vs_slots B) sigmax spoff (vs_slots SX)) by reflexivity.
      assert (FG : vs_globs BF = set_exit_globs (vs_globs B) sigmax (vs_globs SX)) by reflexivity.
      assert (FNl : vs_nul BF = add_exit_nuls (vs_nul B) spoff (vs_nul SX)) by reflexivity.
      clearbody BF.
      assert (HJb : (JOIN0 <= b)%positive) by exact HJ0.
      intros HWF. apply vstate_below_b_sound in HWF.
      split; [exact HE|]. split; [exact XMC|]. split.
      { eapply gamma_fix_ext; [|exact ext_b|exact HF]. exact B10b. }
      split; [rewrite FS; exact SAT3|]. split.
      { intros bb k x y Hg. rewrite FC in Hg. eapply (conddef_ext (vs_conddef A0) nu1 nu2 b); eauto.
        - intros; rewrite HB; eapply B15; eauto.
        - apply ext_b. }
      split.
      { intros r x md Hg. rewrite FM in Hg. eapply (moddef_ext (vs_moddef A0) nu1 nu2 b); eauto.
        - intros; rewrite HB; eapply B16; eauto.
        - apply ext_b. }
      split.
      { (* [comment removed for export] *)
        intros s zs Hg. rewrite FV in Hg. apply set_exit_valsets_get in Hg as [Hg|(s0 & Hin0 & SI & PM)].
        - rewrite nu2_old; [apply HV; exact Hg|]. rewrite HB. eapply B17; eauto.
        - apply pm_elements_sound in Hin0. pose proof (XV _ _ Hin0) as Hv.
          assert (Hs0 : (s0 < cs_next X)%positive) by exact (Y17 _ _ Hin0).
          pose proof (lsubst_eval_x (lsym s0) (lin_below_lsym _ _ Hs0)) as EV0. rewrite eval_lsym in EV0.
          rewrite eval_lsubst, eval_lsym in EV0. unfold vsubst in EV0.
          unfold sym_image in SI. unfold pm_mem in PM. destruct (pm_get s0 sigmax) as [e0|] eqn:G0; [|discriminate].
          destruct (lin_single e0) as [[s1 k1]|] eqn:LS; [|discriminate].
          destruct (Z.eqb_spec k1 1); [|discriminate]. destruct (Z.eqb_spec (lc e0) 0); [|discriminate].
          simpl in SI. inversion SI; subst s1. rewrite (eval_single _ _ _ _ LS) in EV0.
          replace (nu2 s) with (nuV' s0) by (ltac2:(LK.k [@NPC; @HB; @HB'; @Q2; @E1; @E3; @E4; @E5; @E7; @E8; @E9; @E10; @E11; @P0; @EnJ; @Eb'; @FN; @HJb; @EV0; @e; @e1]); lia). exact Hv. }
      split.
      { (* [comment removed for export] *)
        intros r e Hr0 Hg. rewrite FR in Hg.
        pose proof (rz_pos_of r Hr0) as RP. change (bv_unsigned r) with (rz r) in Hg |- *.
        assert (GEN10 : forall z e0 e', get_reg SX z = Some e0 -> osubst sigmax e0 = Some e' -> rz r = z ->
                        bv_unsigned (getr regs2 r) = zwrap 64 (eval nu2 e')).
        { intros z e0 e' Hz Ho Hrz. unfold get_reg in Hz. destruct (Z.eqb_spec z 0) as [Ez|Ez]; [exfalso; clear -Ez Hrz Hr0; unfold rz in *; lia|].
          rewrite <- Hrz in Hz. rewrite (osubst_eval _ _ (Y12 _ _ Hz) Ho). exact (XR r e0 Hr0 Hz). }
        apply reg_upd_get in Hg as [[K11 V11]|[K11 Hg]].
        { destruct (get_reg SX 11) as [e0|] eqn:G11; [|discriminate]. simpl in V11.
          eapply (GEN10 11); eauto. apply reg_key_eq; auto; [clear -RP|clear]; lia. }
        apply reg_upd_get in Hg as [[K10 V10]|[K10 Hg]].
        { destruct (get_reg SX 10) as [e0|] eqn:G10; [|discriminate]. simpl in V10.
          eapply (GEN10 10); eauto. apply reg_key_eq; auto; [clear -RP|clear]; lia. }
        rewrite Q7, pm_get_set in Hg.
        destruct (Pos.eqb_spec (reg_key (rz r)) (reg_key 1)) as [K1|K1].
        { inversion Hg; subst e. rewrite eval_lconst.
          assert (r = 1%bv).
          { apply bv_eq. apply reg_key_eq in K1; [|clear -RP; lia|clear; lia]. unfold rz in K1. rewrite K1. reflexivity. }
          subst r. rewrite XRA. rewrite u_wordZ by (clear -NPC; lia). symmetry. apply zwrap_id. clear -NPC; lia. }
        apply regs_tops_get in Hg as [Hg Hnot].
        rewrite (eval_ext_below _ _ _ _ ext_b) by (rewrite HB; exact (B12 _ _ Hg)).
        apply kept_reg; [exact Hr0| |exact Hg].
        destruct (in_CALLER_SAVED_dec (rz r) RP) as [Hcs|Hk]; [|exact Hk].
        exfalso. apply (Hnot _ Hcs); [clear -RP Hcs|reflexivity].
        unfold CALLER_SAVED in Hcs. simpl in Hcs. lia. }
      split.
      { (* [comment removed for export] *)
        intros off w v Hin. rewrite FSl in Hin. apply set_exit_slots_in in Hin as [Hin|(v0 & e & Hin & Hoff & Ho & Hv)]; cbn [fst snd] in Hin; [|cbn [fst snd] in Hoff, Ho, Hv; subst v].
        - rewrite Q8 in Hin. apply kill_ranges_in in Hin as [Hin Hdis]. cbn [fst snd] in Hdis.
          pose proof (cm_kill_disjoint _ _ _ _ _ _ Hin) as Hbot. apply cm_kill_sub in Hin.
          destruct (HSl _ _ _ Hin) as [(R1&R2&R3) CH]. unfold P in R1; simpl in R1. split; [unfold P; simpl; (ltac2:(LK.k [@NPC; @HB; @Q2; @E3; @E4; @E5; @E7; @E8; @E9; @E10; @EnJ; @Eb'; @FN; @R1; @R2; @R3]); lia)|].
          assert (Hoff : spoff <= off) by (unfold STACK_BOTTOM in Hbot; (ltac2:(LK.k [@NPC; @HB; @Q2; @E1; @E2; @E3; @E4; @E5; @E7; @E8; @E9; @E10; @E11; @P1; @EnJ; @Eb'; @FN; @Hbot; @R1; @R2]); lia)).
          destruct v as [e|]; [|exact I]. cbn [cell_holds] in CH |- *.
          rewrite (eval_ext_below _ _ _ _ ext_b) by (rewrite HB; exact (B13 _ _ _ Hin)).
          rewrite rdn_unchanged; [exact CH|rewrite ?HPf, ?HPs; (ltac2:(LK.k [@NPC; @HB; @HB'; @Q2; @E1; @E2; @E3; @E4; @E5; @E7; @E8; @E9; @E10; @E11; @P0; @P1; @EnJ; @Eb'; @FN; @HJb; @R1; @R2; @R3; @Hoff]); lia)|rewrite ?HPf, ?HPs; (ltac2:(LK.k [@NPC; @HB; @HB'; @Q2; @E1; @E2; @E3; @E4; @E5; @E7; @E8; @E9; @E10; @E11; @P0; @P1; @EnJ; @Eb'; @FN; @HJb; @R1; @R2; @R3; @Hoff]); lia)|rewrite ?HPf, ?HPs; (ltac2:(LK.k [@NPC; @HB; @HB'; @Q2; @E1; @E2; @E3; @E4; @E5; @E7; @E8; @E9; @E10; @E11; @P0; @P1; @EnJ; @Eb'; @FN; @HJb; @R1; @R2; @R3; @Hoff]); lia)| |].
          + intros lo hi Hr. specialize (Hdis _ _ Hr). (ltac2:(LK.k [@NPC; @HB; @HB'; @Q2; @E1; @E3; @E4; @E5; @E7; @E8; @E9; @E10; @E11; @P0; @EnJ; @Eb'; @FN; @HJb; @Hdis; @R2]); lia).
          + intros c Hc. pose proof (wcells_PV_bound _ Hc). unfold P in H; simpl in H. (ltac2:(LK.k [@NPC; @HB; @HB'; @Q2; @E1; @E2; @E3; @E4; @E5; @E7; @E8; @E9; @E10; @EnJ; @Eb'; @FN; @HJb; @R1; @R2; @R3; @H]); lia).
        - destruct (XSl _ _ _ Hin) as [(R1&R2&R3) CH]. split; [unfold P; simpl; unfold PV in R1, R3; simpl in R1, R3; (ltac2:(LK.k [@NPC; @HB; @Q2; @E3; @E4; @E5; @E7; @E8; @E9; @E10; @EnJ; @Eb'; @FN; @R1; @R2; @R3]); lia)|].
          destruct v0 as [e0|]; [|discriminate]. simpl in Ho. cbn [cell_holds] in CH |- *.
          rewrite (osubst_eval _ _ (Y13 _ _ _ Hin) Ho). exact CH. }
      split.
      { (* [comment removed for export] *)
        intros a w v Hin. rewrite FG in Hin. apply set_exit_globs_in in Hin as [Hin|(v0 & Hin & Hv)]; cbn [fst snd] in Hin; [|cbn [fst snd] in Hv; subst v].
        - rewrite Q9 in Hin. change (de_G D) with G in Hin.
          assert (Hin' : In (a, (w, v)) (kill_cells (vs_globs A0) (u_wglobs V))
                         /\ (u_errno V = true -> ~ (a < ci_errno (ge_CI G) + 4 /\ ci_errno (ge_CI G) < a + w))).
          { destruct (u_errno V); [|split; [exact Hin|discriminate]].
            split; [eapply cm_kill_sub; eauto|]. intros _. exact (cm_kill_disjoint _ _ _ _ _ _ Hin). }
          clear Hin. destruct Hin' as [Hin Herr]. apply kill_cells_in in Hin as [Hin Hdis]. cbn [fst snd] in Hdis.
          destruct (HGl _ _ _ Hin) as [(R1&R2&R3) CH]. unfold P in R3; simpl in R3. split; [unfold P; simpl; (ltac2:(LK.k [@NPC; @HB; @Q2; @E3; @E4; @E5; @E7; @E8; @E9; @E10; @EnJ; @Eb'; @FN; @R1; @R2; @R3]); lia)|].
          destruct v as [e|]; [|exact I]. cbn [cell_holds] in CH |- *.
          rewrite (eval_ext_below _ _ _ _ ext_b) by (rewrite HB; exact (B14 _ _ _ Hin)).
          replace a with (0 + a) by (ltac2:(LK.k [@NPC; @HB; @Q2; @E3; @E7; @E8; @E9; @E10; @EnJ; @Eb'; @FN]); lia).
          rewrite rdn_unchanged; [exact CH|rewrite ?HPf, ?HPs; (ltac2:(LK.k [@NPC; @HB; @Q2; @E1; @E2; @E3; @E4; @E5; @E7; @E8; @E9; @E10; @P0; @P1; @EnJ; @Eb'; @FN; @R1; @R2; @R3; @HB'; @E11; @HJb]); lia)|rewrite ?HPf, ?HPs; (ltac2:(LK.k [@NPC; @HB; @Q2; @E1; @E2; @E3; @E4; @E5; @E7; @E8; @E9; @E10; @P0; @P1; @EnJ; @Eb'; @FN; @R1; @R2; @R3; @HB'; @E11; @HJb]); lia)|rewrite ?HPf, ?HPs; (ltac2:(LK.k [@NPC; @HB; @Q2; @E1; @E2; @E3; @E4; @E5; @E7; @E8; @E9; @E10; @P0; @P1; @EnJ; @Eb'; @FN; @R1; @R2; @R3; @HB'; @E11; @HJb]); lia)| |].
          + intros lo hi Hr. pose proof (wstack_V_bound _ _ Hr). unfold P in H; simpl in H. (ltac2:(LK.k [@NPC; @HB; @HB'; @Q2; @E1; @E2; @E3; @E4; @E5; @E7; @E8; @E9; @E10; @E11; @P0; @EnJ; @Eb'; @FN; @HJb; @R2; @R3; @H]); lia).
          + intros c Hc. unfold PV, unit_params, unit_wcells in Hc. simpl in Hc. apply in_app_iff in Hc as [Hc|Hc].
            * destruct (u_errno V); [|destruct Hc]. destruct Hc as [<-|[]]. simpl. specialize (Herr eq_refl). (ltac2:(LK.k [@NPC; @HB; @HB'; @Q2; @E1; @E3; @E4; @E5; @E7; @E8; @E9; @E10; @E11; @P0; @EnJ; @Eb'; @FN; @HJb; @Herr; @R2]); lia).
            * destruct c as [ca cn]. specialize (Hdis _ _ Hc). simpl. (ltac2:(LK.k [@NPC; @HB; @HB'; @Q2; @E1; @E3; @E4; @E5; @E7; @E8; @E9; @E10; @E11; @P0; @EnJ; @Eb'; @FN; @HJb; @Hdis; @R2]); lia).
        - destruct (XGl _ _ _ Hin) as [(R1&R2&R3) CH]. split; [unfold P; simpl; unfold PV in R3; simpl in R3; (ltac2:(LK.k [@NPC; @HB; @Q2; @E3; @E4; @E5; @E7; @E8; @E9; @E10; @EnJ; @Eb'; @FN; @R1; @R2; @R3]); lia)|].
          destruct v0 as [e0|]; [|exact I]. simpl. cbn [cell_holds] in CH |- *.
          destruct (osubst sigmax e0) as [e|] eqn:Ho; [|exact I]. cbn [cell_holds].
          rewrite (osubst_eval _ _ (Y14 _ _ _ Hin) Ho). exact CH. }
      split.
      { (* [comment removed for export] *)
        intros lo hi Hin. rewrite FNl in Hin. apply add_exit_nuls_in in Hin as [Hin|Hin].
        - rewrite Q10 in Hin. apply filter_In in Hin as [Hin Hsv]. unfold nul_survives in Hsv. cbn [fst snd] in Hsv.
          apply andb_prop in Hsv as [Hs1 Hs2]. apply Z.leb_le in Hs1. apply Bool.negb_true_iff in Hs2.
          destruct (HN _ _ Hin) as (off & b0 & H1 & H2 & H3 & H4). unfold P in H2; simpl in H2.
          exists off, b0. split; [exact H1|]. split; [unfold P; simpl; (ltac2:(LK.k [@NPC; @HB; @Q2; @E3; @E4; @E5; @E7; @E8; @E9; @E10; @EnJ; @Eb'; @FN; @H2]); lia)|]. split; [|exact H4].
          rewrite <- H3. apply (rdn_unchanged (e_sp0 E + off) 1); simpl; rewrite ?HPf, ?HPs; try (ltac2:(LK.k [@NPC; @HB; @HB'; @Q2; @E1; @E2; @E3; @E4; @E5; @E7; @E8; @E9; @E10; @E11; @P0; @P1; @EnJ; @Eb'; @FN; @HJb; @H2; @Hs1; @H1]); lia).
          + intros lo' hi' Hr.
            assert (NE : ~ (lo < hi' /\ lo' <= hi)).
            { intros Y1.
              assert (X1 : existsb (fun r : Z * Z => (lo <? snd r) && (fst r <=? hi)) (u_wstack V) = true).
              { apply existsb_exists. exists (lo', hi'). split; [exact Hr|]. cbn [fst snd].
                apply andb_true_intro. split; [apply Z.ltb_lt|apply Z.leb_le]; (ltac2:(LK.k [@NPC; @HB; @Q2; @E3; @E4; @E5; @E7; @E8; @E9; @E10; @EnJ; @Eb'; @FN; @Y1]); lia). }
              rewrite X1 in Hs2. discriminate. }
            clear -NE H1 Hs1. lia.
          + intros c Hc. pose proof (wcells_PV_bound _ Hc). unfold P in H; simpl in H. (ltac2:(LK.k [@NPC; @HB; @HB'; @Q2; @E1; @E2; @E3; @E4; @E5; @E7; @E8; @E9; @E10; @EnJ; @Eb'; @FN; @HJb; @H2; @H]); lia).
        - destruct (XN _ _ Hin) as (off & b0 & H1 & H2 & H3 & H4). exists off, b0. unfold PV in H2; simpl in H2.
          split; [exact H1|]. split; [unfold P; simpl; (ltac2:(LK.k [@NPC; @HB; @Q2; @E3; @E4; @E5; @E7; @E8; @E9; @E10; @EnJ; @Eb'; @FN; @H2]); lia)|]. split; [exact H3|exact H4]. }
      (* [comment removed for export] *)
      exact HWF.
    Qed.

  End PostCall.

End Call.
