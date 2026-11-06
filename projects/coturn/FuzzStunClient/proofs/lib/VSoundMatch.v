(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool String Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import PropExec SeqExec.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import VLinalg VState VLogic VGamma VStepMem VStepMemSound VStepMemSound2 VCert VDriverMatch.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Unset Lia Cache.
#[local] Existing Instance PropExec.fx0.  (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition sub_sigma (s1 s2 : pmap lin) : Prop :=
  forall k e, pm_get k s1 = Some e -> pm_get k s2 = Some e.

Definition binds_only (isv : sym -> bool) (s0 s : pmap lin) : Prop :=
  forall k e, pm_get k s = Some e -> pm_get k s0 = Some e \/ isv k = true.

Lemma sub_sigma_refl s : sub_sigma s s. Proof. now intros k e. Qed.
Lemma sub_sigma_trans a b c : sub_sigma a b -> sub_sigma b c -> sub_sigma a c.
Proof. intros H1 H2 k e Hk. auto. Qed.

Lemma unbound_vars_isv isv sigma e J k :
  In (J, k) (unbound_vars isv sigma e) -> isv J = true /\ pm_mem J sigma = false.
Proof.
  unfold unbound_vars. rewrite filter_In. simpl. intros [_ H].
  apply andb_prop in H as [H1 H2]. split; auto. now destruct (pm_mem J sigma).
Qed.

Lemma match_loc_keep isv (sigma : pmap lin) (defer : list (lin * lin)) e e' :
  let acc' := (sigma, (e, e') :: defer) in
  sub_sigma sigma (fst acc') /\ incl defer (snd acc') /\ In (e, e') (snd acc')
  /\ (forall s0, binds_only isv s0 sigma -> binds_only isv s0 (fst acc')).
Proof.
  simpl. split; [apply sub_sigma_refl|]. split; [apply incl_tl, incl_refl|]. split; [now left|auto].
Qed.

Lemma match_loc_spec isv acc e e' :
  let acc' := match_loc isv acc e e' in
  sub_sigma (fst acc) (fst acc') /\ incl (snd acc) (snd acc') /\ In (e, e') (snd acc')
  /\ (forall s0, binds_only isv s0 (fst acc) -> binds_only isv s0 (fst acc')).
Proof.
  unfold match_loc. destruct acc as [sigma defer].
  destruct (unbound_vars isv sigma e) as [|[J k] [|x t]] eqn:U; try apply match_loc_keep.
  destruct (Z.eqb k 1); [|apply match_loc_keep].
  assert (HJ : isv J = true /\ pm_mem J sigma = false).
  { apply (unbound_vars_isv isv sigma e J k). rewrite U. now left. }
  destruct HJ as [HJ1 HJ2]. simpl.
  split; [|split; [apply incl_tl, incl_refl| split; [now left|]]].
  - intros k' e0 Hk. rewrite pm_get_set. destruct (Pos.eqb_spec k' J); [|auto].
    subst. exfalso. unfold pm_mem in HJ2. rewrite Hk in HJ2. discriminate.
  - intros s0 HB k' e0. rewrite pm_get_set. destruct (Pos.eqb_spec k' J); [|apply HB].
    subst. intros _. now right.
Qed.

Lemma match_regs_spec isv skip P : forall l acc acc',
  match_regs isv skip l P acc = inl acc' ->
  sub_sigma (fst acc) (fst acc') /\ incl (snd acc) (snd acc')
  /\ (forall s0, binds_only isv s0 (fst acc) -> binds_only isv s0 (fst acc'))
  /\ (forall r e, In (r, e) l -> skip r = false ->
        exists e', pm_get r (vs_regs P) = Some e' /\ In (e, e') (snd acc')).
Proof.
  induction l as [|[r e] t IH]; simpl; intros acc acc' H.
  - inversion H; subst. repeat split; auto using sub_sigma_refl, incl_refl. intros; tauto.
  - destruct (skip r) eqn:Sk.
    + destruct (IH _ _ H) as (A1&A2&A3&A4). repeat split; auto.
      intros r0 e0 [X|X] Hs; [inversion X; subst; congruence|eauto].
    + destruct (pm_get r (vs_regs P)) as [e'|] eqn:G; [|discriminate].
      destruct (IH _ _ H) as (A1&A2&A3&A4).
      destruct (match_loc_spec isv acc e e') as (B1&B2&B3&B4).
      repeat split.
      * eapply sub_sigma_trans; eauto.
      * eapply incl_tran; eauto.
      * auto.
      * intros r0 e0 [X|X] Hs; [|eauto]. inversion X; subst. exists e'. split; auto.
Qed.

Lemma match_cells_spec isv cs P pm : forall l acc acc',
  match_cells isv cs P l pm acc = inl acc' ->
  sub_sigma (fst acc) (fst acc') /\ incl (snd acc) (snd acc')
  /\ (forall s0, binds_only isv s0 (fst acc) -> binds_only isv s0 (fst acc'))
  /\ (forall k w e, In (k, (w, Some e)) l ->
        exists e', path_cell cs P pm k w = Some e' /\ In (e, e') (snd acc')).
Proof.
  induction l as [|[k [w [e|]]] t IH]; simpl; intros acc acc' H.
  - inversion H; subst. repeat split; auto using sub_sigma_refl, incl_refl. intros; tauto.
  - destruct (path_cell cs P pm k w) as [e'|] eqn:G; try discriminate.
    destruct (IH _ _ H) as (A1&A2&A3&A4).
    destruct (match_loc_spec isv acc e e') as (B1&B2&B3&B4).
    repeat split.
    + eapply sub_sigma_trans; eauto.
    + eapply incl_tran; eauto.
    + auto.
    + intros k0 w0 e0 [X|X]; [|eauto]. inversion X; subst. exists e'. split; auto.
  - destruct (IH _ _ H) as (A1&A2&A3&A4). repeat split; auto.
    intros k0 w0 e0 [X|X]; [inversion X|eauto].
Qed.

(* [comment removed for export] *)
Section PathCell.
  Variable SEGS : list Segment.

  Lemma zwrap_mod_eq n a b : 0 <= n -> a mod 2 ^ n = b mod 2 ^ n -> zwrap n a = zwrap n b.
  Proof. intros. unfold zwrap. auto. Qed.

  Lemma norm_w_sound P nu w e e' :
    sat nu (vs_store P) -> 0 < w -> norm_w P w e = Some e' ->
    zwrap (8 * w) (eval nu e') = zwrap (8 * w) (eval nu e).
  Proof.
    intros HS Hw. unfold norm_w.
    destruct (Z.leb_spec 8 w); [intros X; inversion X; now subst|].
    pose proof (pow2_pos (8 * w) ltac:(lia)) as M.
    destruct (lin_is_const e) eqn:Hc.
    - intros X; inversion X; subst. rewrite eval_lconst, (eval_is_const nu e Hc).
      unfold zwrap. apply Z.mod_mod. lia.
    - destruct (lin_cong (scong (vs_store P)) e) as [m r] eqn:LC. simpl.
      destruct (Z.ltb 1 m && Z.eqb (m mod 2 ^ (8 * w)) 0) eqn:Cg.
      + intros X; inversion X; subst. rewrite eval_lconst.
        apply andb_prop in Cg as [C1 C2]. apply Z.ltb_lt in C1. apply Z.eqb_eq in C2.
        pose proof (lin_cong_divide nu (scong (vs_store P)) e (sat_cong _ _ HS)) as Hd. rewrite LC in Hd. simpl in Hd.
        unfold zwrap. rewrite Z.mod_mod by lia.
        apply Z.mod_divide in C2; [|lia]. destruct Hd as [q Hq]. destruct C2 as [q' Hq'].
        replace (eval nu e) with (r + q * (q' * 2 ^ (8 * w))) by lia.
        rewrite Z.mul_assoc, Z.mod_add by lia. reflexivity.
      + destruct (lp_bounds (vs_store P) e) as [[lo|] [hi|]] eqn:LB; try discriminate.
        destruct (Z.eqb_spec (lo / 2 ^ (8 * w)) (hi / 2 ^ (8 * w))); [|discriminate].
        intros X; inversion X; subst. rewrite eval_laddc.
        unfold zwrap. replace (eval nu e + - (lo / 2 ^ (8 * w) * 2 ^ (8 * w))) with (eval nu e + (- (lo / 2 ^ (8 * w))) * 2 ^ (8 * w)) by lia.
        rewrite Z.mod_add by lia. reflexivity.
  Qed.

  Lemma const_slice_cell_sound pm k w e' nu mem (base : Z) :
    const_slice_cell pm k w = Some e' -> 0 < w ->
    (forall k0 w0 v0, In (k0, (w0, v0)) pm -> cell_holds SEGS nu mem (base + k0) w0 v0) ->
    cell_holds SEGS nu mem (base + k) w (Some e').
  Proof.
    intros Hc Hw Hpm. unfold const_slice_cell in Hc.
    match type of Hc with (match find ?f ?l with _ => _ end = _) => destruct (find f l) as [[o2 [w2 [v2|]]]|] eqn:Ef end;
      try discriminate.
    inversion Hc; subst e'; clear Hc.
    apply find_some in Ef as [Hin Hp]. apply cm_overlapping_in in Hin.
    apply andb_prop in Hp as [Hp Hk]. apply andb_prop in Hp as [Hp1 Hp2]. apply Z.leb_le in Hp1. apply Z.leb_le in Hp2.
    pose proof (Hpm _ _ _ Hin) as CH. cbn [cell_holds] in CH. destruct CH as [bs2 [Hbs2 Hval2]].
    pose proof (rdn_length _ _ _ _ _ Hbs2) as Hlen2.
    set (kk := Z.to_nat (k - o2)).
    pose proof (rdn_skipn SEGS mem _ _ _ kk Hbs2 ltac:(unfold kk; lia)) as Hsk.
    rewrite wordZ_add_nat in Hsk. replace (base + o2 + Z.of_nat kk) with (base + k) in Hsk by (unfold kk; lia).
    pose proof (rdn_firstn SEGS mem _ _ _ (Z.to_nat w) Hsk ltac:(unfold kk; lia)) as Hrd.
    cbn [cell_holds]. exists (firstn (Z.to_nat w) (skipn kk bs2)). split; [exact Hrd|].
    rewrite bytes_le_firstn by (rewrite length_skipn; unfold kk; lia).
    rewrite bytes_le_skipn by (unfold kk; lia). rewrite Hval2.
    replace (Z.of_nat (Z.to_nat w)) with w by lia.
    replace (Z.of_nat kk) with (k - o2) by (unfold kk; lia).
    rewrite (eval_is_const nu v2 Hk), eval_lconst.
    replace (zwrap (8 * w2) (lc v2) / 2 ^ (8 * (k - o2))) with (lc v2 mod 2 ^ (8 * w2) / 2 ^ (8 * (k - o2))) by reflexivity.
    rewrite <- (const_slice_eq (lc v2) w2 (k - o2) w) by lia.
    unfold zwrap. symmetry. apply Z.mod_small. apply const_slice_range; lia.
  Qed.

  Lemma path_cell_sound cs P pm k w e' nu mem (base : Z) :
    path_cell cs P pm k w = Some e' -> 0 < w -> sat nu (vs_store P) ->
    (forall k0 w0 v0, In (k0, (w0, v0)) pm -> cell_holds SEGS nu mem (base + k0) w0 v0) ->
    cell_holds SEGS nu mem (base + k) w (Some e').
  Proof.
    intros Hp Hw HS Hpm. unfold path_cell in Hp.
    destruct (cm_get pm k) as [[w' [e0|]]|] eqn:G.
    - apply cm_get_in in G. destruct (Z.eqb_spec w w').
      + subst w'. pose proof (Hpm _ _ _ G) as CH. cbn [cell_holds] in CH |- *. destruct CH as [bs [Hbs Hv]].
        exists bs. split; [exact Hbs|]. rewrite Hv.
        destruct cs; [|inversion Hp; now subst]. symmetry. eapply norm_w_sound; eauto.
      + destruct cs; [|discriminate]. eapply const_slice_cell_sound; eauto.
    - discriminate.
    - destruct cs; [|discriminate]. eapply const_slice_cell_sound; eauto.
  Qed.
End PathCell.

Lemma check_defer_sound sigma : forall l, check_defer sigma l = true ->
  forall e e', In (e, e') l -> lsubst sigma e = e'.
Proof.
  induction l as [|[a b] t IH]; simpl; intros H e e' Hin; [tauto|].
  apply andb_prop in H as [H1 H2]. destruct Hin as [X|X]; [|eauto].
  inversion X; subst. now apply lin_eqb_eq.
Qed.

Lemma incl_list_sound a b x : incl_list a b = true -> In x a -> In x b.
Proof.
  unfold incl_list. rewrite forallb_forall. intros H Hin. specialize (H _ Hin).
  rewrite existsb_exists in H. destruct H as [y [Hy E]]. apply Z.eqb_eq in E. now subst.
Qed.

Lemma sym_image_eval sigma s s' nu :
  sym_image sigma s = Some s' -> vsubst nu sigma s = nu s'.
Proof.
  unfold sym_image, vsubst. destruct (pm_get s sigma) as [e|] eqn:G.
  - destruct (lin_single e) as [[s1 k]|] eqn:Ls; [|discriminate].
    destruct (Z.eqb_spec k 1); [|discriminate]. destruct (Z.eqb_spec (lc e) 0); [|discriminate].
    simpl. intros X; inversion X; subst.
    rewrite (eval_single _ _ _ _ Ls). lia.
  - intros X; inversion X; now subst.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section Sound.
  Variable SEGS : list Segment.
  Variables P P' : vparams.          (* [comment removed for export] *)
  Variables E E' : venv.
  Hypothesis Hframe : vp_frame P' = vp_frame P.
  Hypothesis Hsplo : vp_splo P' = vp_splo P.
  Hypothesis Hsp0 : e_sp0 E' = e_sp0 E.

  Theorem match_state_sound isv skip cs sigma0 S Pst sigma nu regs mem :
    match_state isv skip cs sigma0 S Pst = MOk sigma ->
    sat nu (vs_store Pst) -> gamma_conddef nu Pst -> gamma_moddef nu Pst -> gamma_valset nu Pst ->
    gamma_regs nu Pst regs -> gamma_slots SEGS P E nu Pst mem -> gamma_globs SEGS P nu Pst mem ->
    gamma_nul SEGS P E Pst mem ->
    (* [comment removed for export] *)
    (forall off w v, In (off, (w, v)) (vs_slots S) -> - vp_frame P <= off /\ 0 < w /\ off + w <= 0 /\ v <> None) ->
    (forall a w v, In (a, (w, v)) (vs_globs S) -> 0 <= a /\ 0 < w /\ a + w <= vp_splo P - vp_frame P /\ v <> None) ->
    let nu' := vsubst nu sigma in
    sub_sigma sigma0 sigma /\ binds_only isv sigma0 sigma
    /\ sat nu' (vs_store S) /\ gamma_conddef nu' S /\ gamma_moddef nu' S /\ gamma_valset nu' S
    /\ (forall (r : reg) e, bv_unsigned r <> 0 -> skip (reg_key (bv_unsigned r)) = false ->
          pm_get (reg_key (bv_unsigned r)) (vs_regs S) = Some e ->
          bv_unsigned (getr regs r) = zwrap 64 (eval nu' e))
    /\ gamma_slots SEGS P' E' nu' S mem /\ gamma_globs SEGS P' nu' S mem /\ gamma_nul SEGS P' E' S mem.
  Proof.
    rewrite match_state_v1_eq. unfold match_state_v1. intros HM HS HC HMo HV HR HSl HG HN WS WG.
    destruct (match_regs isv skip (pm_elements (vs_regs S)) Pst (sigma0, [])) as [acc1|] eqn:M1; [|discriminate].
    destruct (match_cells isv cs Pst (vs_slots S) (vs_slots Pst) acc1) as [acc2|] eqn:M2; [|discriminate].
    destruct (match_cells isv cs Pst (vs_globs S) (vs_globs Pst) acc2) as [[sg defer]|] eqn:M3; [|discriminate].
    destruct (check_defer sg defer) eqn:CD; [|discriminate].
    destruct (forallb (nul_implied (vs_nul Pst)) (vs_nul S)) eqn:NI; [|discriminate].
    destruct (match_valsets sg S Pst) eqn:MV; [|discriminate].
    destruct (match_conddefs sg S Pst) eqn:MCd; [|discriminate].
    destruct (match_moddefs sg S Pst) eqn:MMd; [|discriminate].
    destruct (store_entails (vs_store Pst) sg (vs_store S)) eqn:SE; [|discriminate].
    simpl in HM. inversion HM; subst sg. clear HM.
    destruct (match_regs_spec isv skip Pst _ _ _ M1) as (R1&R2&R3&R4).
    destruct (match_cells_spec isv cs Pst (vs_slots Pst) _ _ _ M2) as (S1&S2&S3&S4).
    destruct (match_cells_spec isv cs Pst (vs_globs Pst) _ _ _ M3) as (G1&G2&G3&G4).
    simpl in *.
    pose proof (check_defer_sound _ _ CD) as DEF.
    assert (BO : binds_only isv sigma0 sigma).
    { apply G3, S3, R3. intros k e Hk; now left. }
    split; [|split; [exact BO|]].
    { eapply sub_sigma_trans; [|exact G1]. eapply sub_sigma_trans; [|exact S1]. exact R1. }
    split; [exact (store_entails_sound nu (vs_store Pst) HS sigma (vs_store S) SE)|].
    split.
    { (* [comment removed for export] *)
      intros b k x y Hb. unfold match_conddefs in MCd. rewrite forallb_forall in MCd.
      specialize (MCd _ (pm_elements_complete _ _ Hb)). simpl in MCd.
      destruct (sym_image sigma b) as [b'|] eqn:SI; [|discriminate].
      destruct (pm_get b' (vs_conddef Pst)) as [[[k' x'] y']|] eqn:Gb; [|discriminate].
      apply andb_prop in MCd as [MCd Ey]. apply andb_prop in MCd as [Ek Ex].
      apply lin_eqb_eq in Ex. apply lin_eqb_eq in Ey.
      rewrite (sym_image_eval _ _ _ nu SI). rewrite (HC _ _ _ _ Gb).
      rewrite <- !eval_lsubst, Ex, Ey. destruct k, k'; try discriminate; reflexivity. }
    split.
    { (* [comment removed for export] *)
      intros r x m Hr. unfold match_moddefs in MMd. rewrite forallb_forall in MMd.
      specialize (MMd _ (pm_elements_complete _ _ Hr)). simpl in MMd.
      destruct (sym_image sigma r) as [r'|] eqn:SI; [|discriminate].
      destruct (pm_get r' (vs_moddef Pst)) as [[x' m']|] eqn:Gr; [|discriminate].
      apply andb_prop in MMd as [Em Ex]. apply Z.eqb_eq in Em. apply lin_eqb_eq in Ex. subst m'.
      rewrite (sym_image_eval _ _ _ nu SI). destruct (HMo _ _ _ Gr) as [Hm Hv]. split; auto.
      rewrite Hv, <- eval_lsubst, Ex. reflexivity. }
    split.
    { (* [comment removed for export] *)
      intros s vs Hs. unfold match_valsets in MV. rewrite forallb_forall in MV.
      specialize (MV _ (pm_elements_complete _ _ Hs)). simpl in MV.
      destruct (sym_image sigma s) as [s'|] eqn:SI; [|discriminate].
      destruct (pm_get s' (vs_valset Pst)) as [vs'|] eqn:Gs; [|discriminate].
      rewrite (sym_image_eval _ _ _ nu SI). eapply incl_list_sound; eauto. }
    split.
    { (* [comment removed for export] *)
      intros r e Hr0 Hsk Hr.
      destruct (R4 _ _ (pm_elements_complete _ _ Hr) Hsk) as [e' [Ge' Hin]].
      rewrite (HR r e' Hr0 Ge'). f_equal.
      rewrite <- (DEF _ _ (G2 _ (S2 _ Hin))). apply eval_lsubst. }
    split.
    { (* [comment removed for export] *)
      intros off w v Hin. destruct (WS _ _ _ Hin) as (W1&W2&W3&W4).
      split; [rewrite Hframe; lia|].
      destruct v as [e|]; [|congruence].
      destruct (S4 _ _ _ Hin) as [e' [Gc Hin']].
      assert (CH : cell_holds SEGS nu mem (e_sp0 E + off) w (Some e')).
      { eapply path_cell_sound; eauto. intros k0 w0 v0 Hin0. exact (proj2 (HSl _ _ _ Hin0)). }
      simpl in CH |- *. rewrite Hsp0. destruct CH as [bs [Hbs Hv]]. exists bs. split; auto.
      rewrite Hv. f_equal. rewrite <- (DEF _ _ (G2 _ Hin')). apply eval_lsubst. }
    split.
    { (* [comment removed for export] *)
      intros a w v Hin. destruct (WG _ _ _ Hin) as (W1&W2&W3&W4).
      split; [rewrite Hsplo, Hframe; lia|].
      destruct v as [e|]; [|congruence].
      destruct (G4 _ _ _ Hin) as [e' [Gc Hin']].
      assert (CH : cell_holds SEGS nu mem (0 + a) w (Some e')).
      { eapply path_cell_sound; eauto. intros k0 w0 v0 Hin0. simpl. exact (proj2 (HG _ _ _ Hin0)). }
      simpl in CH |- *. destruct CH as [bs [Hbs Hv]]. exists bs. split; auto.
      rewrite Hv. f_equal. rewrite <- (DEF _ _ Hin'). apply eval_lsubst. }
    { (* [comment removed for export] *)
      intros lo hi Hin. rewrite forallb_forall in NI. specialize (NI _ Hin).
      unfold nul_implied in NI. rewrite existsb_exists in NI. destruct NI as [[lo2 hi2] [Hin2 Hb]].
      simpl in Hb. apply andb_prop in Hb as [B1 B2]. apply Z.leb_le in B1. apply Z.leb_le in B2.
      destruct (HN _ _ Hin2) as [off [b (X1&X2&X3&X4)]].
      exists off, b. rewrite Hframe, Hsp0. repeat split; auto; lia. }
  Qed.
End Sound.
