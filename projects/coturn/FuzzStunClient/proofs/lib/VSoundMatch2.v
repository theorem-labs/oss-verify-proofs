(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool String Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import PropExec CatExec StoreOk.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import Frame.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import VLinalg VState VLogic VGamma VAbs VAbsSound VStepMem VStepSound VStepMemSound VCert VDriverMatch VDriver VSoundMatch VSound VState2 VStepMem2 VCert2 VDriverMatch2 VDriver2 VGamma2 VSound2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import LiaKeep.  (* [comment removed for export] *)
Unset Lia Cache.
#[local] Existing Instance PropExec.fx0.  (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma bind_sym_spec isv sigma s s' sigma' :
  bind_sym isv sigma s s' = Some sigma' ->
  sub_sigma sigma sigma' /\ (forall s0, binds_only isv s0 sigma -> binds_only isv s0 sigma')
  /\ (pm_get s sigma' = Some (lsym s') \/ (pm_get s sigma' = None /\ s = s' /\ isv s = false)).
Proof.
  unfold bind_sym. destruct (pm_get s sigma) as [e|] eqn:G.
  - destruct (lin_eqb e (lsym s')) eqn:EQ; [|discriminate]. intros X; injection X as <-.
    apply lin_eqb_eq in EQ; subst e. split; [apply sub_sigma_refl|]. split; [auto|]. left; exact G.
  - destruct (isv s) eqn:IS.
    + intros X; injection X as <-. split.
      { intros k e Hk. rewrite pm_get_set. destruct (Pos.eqb_spec k s); [subst; congruence|exact Hk]. }
      split.
      { intros s0 HB k e. rewrite pm_get_set. destruct (Pos.eqb_spec k s); [intros _; subst; right; exact IS|apply HB]. }
      left. apply pm_get_set_same.
    + destruct (Pos.eqb_spec s s'); [|discriminate]. intros X; injection X as <-.
      split; [apply sub_sigma_refl|]. split; [auto|]. right. auto.
Qed.

Lemma bind_osym_spec isv sigma s s' sigma' :
  bind_osym isv sigma s s' = Some sigma' ->
  sub_sigma sigma sigma' /\ (forall s0, binds_only isv s0 sigma -> binds_only isv s0 sigma')
  /\ match s, s' with
     | Some x, Some y => pm_get x sigma' = Some (lsym y) \/ (pm_get x sigma' = None /\ x = y /\ isv x = false)
     | None, _ => True
     | Some _, None => False
     end.
Proof.
  unfold bind_osym. destruct s as [x|]; [destruct s' as [y|]; [|discriminate]|].
  - apply bind_sym_spec.
  - intros X; injection X as <-. split; [apply sub_sigma_refl|]. split; auto.
Qed.

(* [comment removed for export] *)
Lemma bound_sym_eval sigma' sigma nu s s' :
  sub_sigma sigma' sigma ->
  (pm_get s sigma' = Some (lsym s') \/ (pm_get s sigma' = None /\ s = s' /\ True)) ->
  (pm_get s sigma' = None -> pm_get s sigma = None) ->
  vsubst nu sigma s = nu s'.
Proof.
  intros SUB [G|(G & -> & _)] KEEP; unfold vsubst.
  - rewrite (SUB _ _ G). apply eval_lsym.
  - rewrite (KEEP G). reflexivity.
Qed.

(* [comment removed for export] *)
Definition BF (isv : sym -> bool) (sigma : pmap lin) (s s' : sym) : Prop :=
  pm_get s sigma = Some (lsym s') \/ (isv s = false /\ s = s').

Lemma BF_mono isv sg sg' s s' : sub_sigma sg sg' -> BF isv sg s s' -> BF isv sg' s s'.
Proof. intros SUB [H|H]; [left; exact (SUB _ _ H)|right; exact H]. Qed.

Lemma BF_eval isv sigma nu s s' :
  binds_only isv pm_empty sigma -> BF isv sigma s s' -> vsubst nu sigma s = nu s'.
Proof.
  intros BO [G|[NI ->]]; unfold vsubst.
  - rewrite G. apply eval_lsym.
  - destruct (pm_get s' sigma) as [e|] eqn:G; [|reflexivity].
    destruct (BO _ _ G) as [X|X]; [rewrite pm_get_empty in X; discriminate|congruence].
Qed.

Lemma bind_sym_BF isv sigma s s' sigma' :
  bind_sym isv sigma s s' = Some sigma' -> BF isv sigma' s s'.
Proof.
  intros H. destruct (bind_sym_spec _ _ _ _ _ H) as (_ & _ & [G|(G & E & NI)]); [left; exact G|right; auto].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition BL (isv : sym -> bool) (sigma : pmap lin) (s : sym) (e : lin) : Prop :=
  (exists e', pm_get s sigma = Some e' /\ forall nu, eval nu e' = eval nu e) \/ (isv s = false /\ pm_get s sigma = None /\ forall nu, eval nu e = nu s).

Lemma BL_mono isv sg sg' s e : sub_sigma sg sg' -> binds_only isv pm_empty sg' -> BL isv sg s e -> BL isv sg' s e.
Proof.
  intros SUB BO [(e' & G & EV)|(NI & G & EV)]; [left; exists e'; split; [exact (SUB _ _ G)|exact EV]|right].
  split; [exact NI|]. split; [|exact EV]. destruct (pm_get s sg') as [e1|] eqn:G'; [|reflexivity].
  destruct (BO _ _ G') as [X|X]; [rewrite pm_get_empty in X; discriminate|congruence].
Qed.

Lemma BL_eval isv sigma nu s e : BL isv sigma s e -> vsubst nu sigma s = eval nu e.
Proof. intros [(e' & G & EV)|(NI & G & EV)]; unfold vsubst; rewrite G; [apply EV|symmetry; apply EV]. Qed.

Lemma bind_lin_spec isv sigma s e sigma' :
  bind_lin isv sigma s e = Some sigma' ->
  sub_sigma sigma sigma' /\ (forall s0, binds_only isv s0 sigma -> binds_only isv s0 sigma') /\ BL isv sigma' s e.
Proof.
  unfold bind_lin. destruct (pm_get s sigma) as [e'|] eqn:G.
  - destruct (lin_eqb e' e) eqn:LE; [|discriminate]. intros X; injection X as <-.
    split; [apply sub_sigma_refl|]. split; [auto|]. left. exists e'. split; [exact G|]. intros nu. exact (lin_eqb_sound nu _ _ LE).
  - destruct (isv s) eqn:IS.
    + intros X; injection X as <-. split.
      { intros k v Hk. rewrite pm_get_set_other; [exact Hk|]. intros ->. congruence. }
      split.
      { intros s0 BO k v Hk. rewrite pm_get_set in Hk. destruct (Pos.eqb_spec k s) as [->|]; [right; exact IS|exact (BO _ _ Hk)]. }
      left. exists e. split; [apply pm_get_set_same|]. intros; reflexivity.
    + destruct (lin_eqb e (lsym s)) eqn:LE; [|discriminate]. intros X; injection X as <-.
      split; [apply sub_sigma_refl|]. split; [auto|]. right. split; [exact IS|]. split; [exact G|].
      intros nu. rewrite (lin_eqb_sound nu _ _ LE). apply eval_lsym.
Qed.

Definition cells_fact (cs : bool) (P : vstate2) (sr pr : vregion) (c : Z) (defer : list (lin * lin)) : Prop :=
  if is_shadow sr then
    forall k w e, In (k, (w, Some e)) (vr_cells sr) ->
      (lin_is_const e = true /\
       forall p, k + c <= p < k + c + w ->
         exists k' w' e', In (k', (w', Some e')) (vr_cells pr) /\ k' <= p < k' + w' /\ lin_is_const e' = true /\ lc e' = lc e)
      \/ (lin_is_const e = false /\ w = 1 /\ exists e', In (k + c, (1, Some e')) (vr_cells pr) /\ In (e, e') defer)
  else
    forall k w e, In (k, (w, Some e)) (vr_cells sr) ->
      exists e', path_cell cs (v1 P) (vr_cells pr) (k + c) w = Some e' /\ In (e, e') defer.

Definition rc_fact (cs exact : bool) (P : vstate2) (sr pr : vregion) (c : Z) (defer : list (lin * lin)) : Prop :=
  vr_disp sr = vr_disp pr
  /\ (exact = true -> c = 0 /\ vr_lo sr = vr_lo pr /\ vr_hi sr = vr_hi pr)
  /\ vr_lo pr <= vr_lo sr + c /\ vr_hi sr + c <= vr_hi pr
  /\ ranges_incl (vr_w sr) (vr_w pr) c = true
  /\ rnul_incl (vr_nul sr) (vr_nul pr) c = true
  /\ cells_fact cs P sr pr c defer.

Lemma cells_fact_mono cs P sr pr c d d' : incl d d' -> cells_fact cs P sr pr c d -> cells_fact cs P sr pr c d'.
Proof.
  unfold cells_fact. intros INC H. destruct (is_shadow sr).
  - intros k w e Hin. destruct (H k w e Hin) as [X|(X1 & X2 & e' & G & IN)]; [left; exact X|right].
    split; [exact X1|]. split; [exact X2|]. exists e'. auto.
  - intros k w e Hin. destruct (H k w e Hin) as (e' & G & IN). exists e'. auto.
Qed.

Lemma rc_fact_mono cs ex P sr pr c d d' : incl d d' -> rc_fact cs ex P sr pr c d -> rc_fact cs ex P sr pr c d'.
Proof.
  intros INC (A1&A2&A3&A4&A5&A6&A7). split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. split; [exact A4|].
  split; [exact A5|]. split; [exact A6|]. eapply cells_fact_mono; eauto.
Qed.

Lemma sh_cover_in0 m o k w v : sh_cover m o = Some (k, (w, v)) -> In (k, (w, v)) m /\ k <= o < k + w.
Proof.
  unfold sh_cover. intros H. apply find_some in H as [H1 H2]. split; [eapply cm_overlapping_in; eauto|].
  apply andb_prop in H2 as [H2 H3]. apply Z.leb_le in H2. apply Z.ltb_lt in H3. lia.
Qed.

(* [comment removed for export] *)
Lemma sh_drop_incl pm pos : incl (sh_drop pm pos) pm.
Proof.
  induction pm as [|[k [w v]] t IH]; cbn [sh_drop]; [apply incl_refl|].
  destruct (Z.leb (k + w) pos); [apply incl_tl; exact IH|apply incl_refl].
Qed.

Lemma sh_run_cover2_sound b : forall fuel pm pos stop pm',
  sh_run_cover2 pm pos stop b fuel = Some pm' ->
  incl pm' pm /\
  forall p, pos <= p < stop ->
    exists k' w' e', In (k', (w', Some e')) pm /\ k' <= p < k' + w' /\ lin_is_const e' = true /\ lc e' = b.
Proof.
  induction fuel as [|f IH]; intros pm pos stop pm' H; cbn [sh_run_cover2] in H.
  - destruct (Z.leb_spec stop pos); [|discriminate]. injection H as <-. split; [apply incl_refl|]. intros; lia.
  - destruct (Z.leb_spec stop pos). { injection H as <-. split; [apply incl_refl|]. intros; lia. }
    pose proof (sh_drop_incl pm pos) as DI.
    destruct (sh_drop pm pos) as [|[k' [w' [e'|]]] t] eqn:SD; try discriminate.
    destruct (lin_is_const e' && Z.eqb (lc e') b && Z.leb k' pos) eqn:C; [|discriminate].
    apply andb_prop in C as [C C3]. apply andb_prop in C as [C1 C2]. apply Z.eqb_eq in C2. apply Z.leb_le in C3.
    assert (INH : In (k', (w', Some e')) pm) by (apply DI; left; reflexivity).
    (* [comment removed for export] *)
    assert (HW : pos < k' + w').
    { clear - SD. revert SD. induction pm as [|[k0 [w0 v0]] t0 IH0]; cbn [sh_drop]; [discriminate|].
      destruct (Z.leb_spec (k0 + w0) pos); [exact IH0|]. intros X. injection X as -> -> -> ->. lia. }
    destruct (IH _ _ _ _ H) as [INC COV].
    split; [eapply incl_tran; [exact INC|exact DI]|].
    intros p Hp. destruct (Z.lt_decidable p (k' + w')) as [LT|GE].
    + exists k', w', e'. repeat split; auto; lia.
    + destruct (COV p ltac:(lia)) as (k2 & w2 & e2 & IN2 & R2 & CE2 & LC2). exists k2, w2, e2. split; [apply DI; exact IN2|auto].
Qed.

Lemma match_sh_cells_spec isv n c : forall l pm acc acc',
  match_sh_cells isv n c l pm acc = inl acc' ->
  sub_sigma (fst acc) (fst acc') /\ incl (snd acc) (snd acc')
  /\ (forall s0, binds_only isv s0 (fst acc) -> binds_only isv s0 (fst acc'))
  /\ (forall k w e, In (k, (w, Some e)) l ->
        (lin_is_const e = true /\
         forall p, k + c <= p < k + c + w ->
           exists k' w' e', In (k', (w', Some e')) pm /\ k' <= p < k' + w' /\ lin_is_const e' = true /\ lc e' = lc e)
        \/ (lin_is_const e = false /\ w = 1 /\ exists e', In (k + c, (1, Some e')) pm /\ In (e, e') (snd acc'))).
Proof.
  induction l as [|[k [w [e|]]] t IH]; intros pm acc acc' H; cbn [match_sh_cells] in H.
  - injection H as <-. repeat split; auto using sub_sigma_refl, incl_refl. intros ? ? ? [].
  - destruct (lin_is_const e) eqn:CE.
    + destruct (sh_run_cover2 pm (k + c) (k + c + w) (lc e) n) as [pm'|] eqn:CK; [|discriminate].
      destruct (sh_run_cover2_sound _ _ _ _ _ _ CK) as [INC COV].
      destruct (IH _ _ _ H) as (A1&A2&A3&A4).
      split; [exact A1|]. split; [exact A2|]. split; [exact A3|].
      intros k0 w0 e0 [X|X].
      * injection X as <- <- <-. left. split; [exact CE|]. exact COV.
      * destruct (A4 _ _ _ X) as [(Y1 & Y2)|(Y1 & Y2 & e' & IN & INd)]; [left|right].
        -- split; [exact Y1|]. intros p Hp. destruct (Y2 p Hp) as (k2 & w2 & e2 & IN2 & REST). exists k2, w2, e2. split; [apply INC; exact IN2|exact REST].
        -- split; [exact Y1|]. split; [exact Y2|]. exists e'. split; [apply INC; exact IN|exact INd].
    + pose proof (sh_drop_incl pm (k + c)) as DI.
      destruct (sh_drop pm (k + c)) as [|[k' [w' [e'|]]] t'] eqn:SD; try discriminate.
      destruct (Z.eqb k' (k + c) && Z.eqb w w' && Z.eqb w 1) eqn:W; [|discriminate].
      apply andb_prop in W as [W W2]. apply andb_prop in W as [W0 W1]. apply Z.eqb_eq in W0. apply Z.eqb_eq in W1. apply Z.eqb_eq in W2. subst w' k'.
      destruct (IH _ _ _ H) as (A1&A2&A3&A4). destruct (match_loc_spec isv acc e e') as (B1&B2&B3&B4).
      split; [eapply sub_sigma_trans; eauto|]. split; [eapply incl_tran; eauto|]. split; [auto|].
      intros k0 w0 e0 [X|X].
      * injection X as <- <- <-. right. split; [exact CE|]. split; [exact W2|]. exists e'. split; [apply DI; left; rewrite W2; reflexivity|]. apply A2. exact B3.
      * destruct (A4 _ _ _ X) as [(Y1 & Y2)|(Y1 & Y2 & e2 & IN & INd)]; [left|right].
        -- split; [exact Y1|]. intros p Hp. destruct (Y2 p Hp) as (k2 & w2 & e3 & IN2 & REST). exists k2, w2, e3. split; [apply DI; exact IN2|exact REST].
        -- split; [exact Y1|]. split; [exact Y2|]. exists e2. split; [apply DI; exact IN|exact INd].
  - destruct (IH _ _ _ H) as (A1&A2&A3&A4). repeat split; auto. intros k0 w0 e0 [X|X]; [discriminate|eauto].
Qed.

Lemma shift_cells_in c l k w v : In (k, (w, v)) l -> In (k + c, (w, v)) (shift_cells c l).
Proof. intros H. unfold shift_cells. apply in_map_iff. exists (k, (w, v)). auto. Qed.

Lemma match_region_cells_spec isv cs exact P sr pr c acc acc' :
  match_region_cells isv cs exact P sr pr c acc = inl acc' ->
  sub_sigma (fst acc) (fst acc') /\ incl (snd acc) (snd acc')
  /\ (forall s0, binds_only isv s0 (fst acc) -> binds_only isv s0 (fst acc'))
  /\ rc_fact cs exact P sr pr c (snd acc').
Proof.
  unfold match_region_cells.
  destruct (Z.eqb_spec (vr_disp sr) (vr_disp pr)) as [ED|]; [|discriminate]. cbn [negb].
  match goal with |- (if negb ?b then _ else _) = _ -> _ => destruct b eqn:EX; [|discriminate] end. cbn [negb].
  destruct (ranges_incl (vr_w sr) (vr_w pr) c) eqn:RI; [|discriminate]. cbn [negb].
  destruct (rnul_incl (vr_nul sr) (vr_nul pr) c) eqn:NI; [|discriminate]. cbn [negb].
  assert (EXT : (exact = true -> c = 0 /\ vr_lo sr = vr_lo pr /\ vr_hi sr = vr_hi pr) /\ vr_lo pr <= vr_lo sr + c /\ vr_hi sr + c <= vr_hi pr).
  { destruct exact.
    - apply andb_prop in EX as [EX E3]. apply andb_prop in EX as [E1 E2].
      apply Z.eqb_eq in E1. apply Z.eqb_eq in E2. apply Z.eqb_eq in E3. repeat split; auto; lia.
    - apply andb_prop in EX as [E1 E2]. apply Z.leb_le in E1. apply Z.leb_le in E2. repeat split; auto; discriminate. }
  destruct EXT as (EX1 & EX2 & EX3).
  unfold rc_fact, cells_fact. destruct (is_shadow sr) eqn:SH; intros H.
  - rewrite match_sh_cells_h_eq in H by (first [discriminate | intros x X; discriminate]).   (* [comment removed for export] *)
    destruct (match_sh_cells_spec isv _ c _ (vr_cells pr) _ _ H) as (A1&A2&A3&A4).
    split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. split; [exact ED|]. split; [exact EX1|].
    split; [exact EX2|]. split; [exact EX3|]. split; [exact RI|]. split; [exact NI|]. exact A4.
  - rewrite match_cells_h_eq in H by (intros _ p X; discriminate). rewrite match_cells_f_eq in H by exact I.   (* [comment removed for export] *)
    destruct (match_cells_spec isv cs (v1 P) (vr_cells pr) _ _ _ H) as (A1&A2&A3&A4).
    split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. split; [exact ED|]. split; [exact EX1|].
    split; [exact EX2|]. split; [exact EX3|]. split; [exact RI|]. split; [exact NI|].
    intros k w e Hin. exact (A4 _ _ _ (shift_cells_in c _ _ _ _ Hin)).
Qed.

(* [comment removed for export] *)

Definition b8_fact (isv : sym -> bool) (sigma : pmap lin) (x y : option sym) : Prop :=
  match x, y with
  | Some a, Some b => BF isv sigma a b
  | None, _ => True
  | Some _, None => False
  end.

Lemma b8_fact_mono isv sg sg' x y : sub_sigma sg sg' -> b8_fact isv sg x y -> b8_fact isv sg' x y.
Proof. unfold b8_fact. destruct x, y; auto. apply BF_mono. Qed.

Definition fake_fact (isv : sym -> bool) (cs : bool) (P : vstate2) (sigma : pmap lin) (defer : list (lin * lin)) (sr pr : vregion) : Prop :=
  exists cid flS flP,
    vr_kind sr = RK_fake cid flS /\ vr_kind pr = RK_fake cid flP
    /\ BF isv sigma (vr_base sr) (vr_base pr) /\ BF isv sigma flS flP /\ b8_fact isv sigma (vr_b8 sr) (vr_b8 pr)
    /\ rc_fact cs true P sr pr 0 defer.

Lemma fake_fact_mono isv cs P sg sg' d d' sr pr :
  sub_sigma sg sg' -> incl d d' -> fake_fact isv cs P sg d sr pr -> fake_fact isv cs P sg' d' sr pr.
Proof.
  intros SUB INC (cid & flS & flP & K1 & K2 & B1 & B2 & B3 & RC). exists cid, flS, flP.
  split; [exact K1|]. split; [exact K2|]. split; [eapply BF_mono; eauto|]. split; [eapply BF_mono; eauto|].
  split; [eapply b8_fact_mono; eauto|]. eapply rc_fact_mono; eauto.
Qed.

Lemma match_fakes_spec isv cs P : forall ls lp acc acc',
  match_fakes isv cs P ls lp acc = inl acc' ->
  sub_sigma (fst acc) (fst acc') /\ incl (snd acc) (snd acc')
  /\ (forall s0, binds_only isv s0 (fst acc) -> binds_only isv s0 (fst acc'))
  /\ length ls = length lp
  /\ (forall i sr pr, nth_error ls i = Some sr -> nth_error lp i = Some pr -> fake_fact isv cs P (fst acc') (snd acc') sr pr).
Proof.
  induction ls as [|sr ls' IH]; intros [|pr lp'] acc acc' H; cbn [match_fakes] in H; try discriminate.
  - injection H as <-. split; [apply sub_sigma_refl|]. split; [apply incl_refl|]. split; [auto|]. split; [reflexivity|].
    intros [|i] ? ? X; discriminate.
  - destruct (vr_kind sr) as [cid flS| | | |] eqn:KS; try discriminate.
    destruct (vr_kind pr) as [cid' flP| | | |] eqn:KP; try discriminate.
    destruct (Z.eqb_spec cid cid') as [<-|]; [|discriminate]. cbn [negb] in H.
    destruct (bind_sym isv (fst acc) (vr_base sr) (vr_base pr)) as [s1|] eqn:B1; [|discriminate].
    destruct (bind_sym isv s1 flS flP) as [s2|] eqn:B2; [|discriminate].
    destruct (bind_osym isv s2 (vr_b8 sr) (vr_b8 pr)) as [s3|] eqn:B3; [|discriminate].
    destruct (match_region_cells isv cs true P sr pr 0 (s3, snd acc)) as [acc1|m] eqn:MC; [|discriminate].
    destruct (bind_sym_spec _ _ _ _ _ B1) as (U1 & O1 & F1).
    destruct (bind_sym_spec _ _ _ _ _ B2) as (U2 & O2 & F2).
    destruct (bind_osym_spec _ _ _ _ _ B3) as (U3 & O3 & F3).
    destruct (match_region_cells_spec _ _ _ _ _ _ _ _ _ MC) as (U4 & I4 & O4 & RC). cbn [fst snd] in U4, I4, O4, RC.
    destruct (IH _ _ _ H) as (U5 & I5 & O5 & LEN & FF).
    assert (SUB3 : sub_sigma (fst acc) (fst acc1)).
    { eapply sub_sigma_trans; [exact U1|]. eapply sub_sigma_trans; [exact U2|]. eapply sub_sigma_trans; [exact U3|exact U4]. }
    split; [eapply sub_sigma_trans; [exact SUB3|exact U5]|].
    split; [eapply incl_tran; [exact I4|exact I5]|].
    split; [intros s0 HB; apply O5, O4, O3, O2, O1; exact HB|].
    split; [cbn; rewrite LEN; reflexivity|].
    intros [|i] sr0 pr0 X Y; cbn in X, Y.
    + injection X as <-. injection Y as <-.
      eapply fake_fact_mono; [exact U5|exact I5|].
      exists cid, flS, flP. split; [exact KS|]. split; [exact KP|]. split.
      { eapply BF_mono; [|destruct F1 as [G|(G&E&N)]; [left; exact G|right; auto]].
        eapply sub_sigma_trans; [exact U2|]. eapply sub_sigma_trans; [exact U3|exact U4]. }
      split.
      { eapply BF_mono; [|destruct F2 as [G|(G&E&N)]; [left; exact G|right; auto]]. eapply sub_sigma_trans; [exact U3|exact U4]. }
      split.
      { eapply b8_fact_mono; [exact U4|]. unfold b8_fact. destruct (vr_b8 sr) as [x|]; destruct (vr_b8 pr) as [y|]; auto.
        destruct F3 as [G|(G&E&N)]; [left; exact G|right; auto]. }
      exact RC.
    + eapply FF; eauto.
Qed.

(* [comment removed for export] *)
Definition RB (isv : sym -> bool) (A : vstate2) (sigma : pmap lin) (s b' : sym) (c : Z) : Prop :=
  (exists e, pm_get s sigma = Some e /\ (forall nu, eval nu e = nu b' + c) /\ is_base A b' = true)
  \/ (pm_get s sigma = None /\ isv s = false /\ s = b' /\ c = 0 /\ is_base A s = true).

Lemma RB_mono isv A sg sg' s b' c : sub_sigma sg sg' -> binds_only isv pm_empty sg' -> RB isv A sg s b' c -> RB isv A sg' s b' c.
Proof.
  intros SUB BO [(e & G & EV & IB)|(G & NI & E & C & IB)].
  - left. exists e. auto.
  - right. split; [|auto]. destruct (pm_get s sg') as [e|] eqn:G'; [|reflexivity].
    destruct (BO _ _ G') as [X|X]; [rewrite pm_get_empty in X; discriminate|congruence].
Qed.

Lemma eval_single_term nu e b' :
  List.filter (fun t : sym * Z => negb (Z.eqb (snd t) 0)) (lt e) = [(b', 1)] -> eval nu e = nu b' + lc e.
Proof.
  intros H. unfold eval.
  assert (GEN : forall l, List.filter (fun t : sym * Z => negb (Z.eqb (snd t) 0)) l = [(b', 1)] -> eval_terms nu l = nu b').
  { clear H. induction l as [|[x k] t IH]; cbn; intros H; [discriminate|].
    destruct (Z.eqb_spec k 0) as [->|NZ]; cbn in H.
    - rewrite (IH H). lia.
    - injection H as -> -> T.
      assert (Z0 : eval_terms nu t = 0).
      { clear IH. induction t as [|[y j] u IHu]; cbn in *; [reflexivity|].
        destruct (Z.eqb_spec j 0) as [->|]; cbn in T; [|discriminate]. rewrite (IHu T). lia. }
      rewrite Z0. lia. }
  rewrite (GEN _ H). lia.
Qed.

Lemma lin_single_lsym e s : lin_single e = Some (s, 1) -> lc e = 0 -> lsym s = e.
Proof.
  unfold lin_single. destruct e as [c [|[s' k] [|? ?]]]; cbn; try discriminate.
  intros X; injection X as -> ->. intros ->. reflexivity.
Qed.

Lemma resolve_base_spec isv A sigma s b' c :
  resolve_base isv A sigma s = Some (b', c) -> RB isv A sigma s b' c.
Proof.
  unfold resolve_base. destruct (pm_get s sigma) as [e|] eqn:G.
  - destruct (List.filter (fun t : sym * Z => negb (Z.eqb (snd t) 0)) (lt e)) as [|[b1 k] [|? ?]] eqn:F; try discriminate.
    destruct (Z.eqb_spec k 1) as [->|]; [|discriminate]. destruct (is_base A b1) eqn:IB; [|discriminate]. cbn [andb].
    intros X; injection X as <- <-. left. exists e. split; [exact G|]. split; [|exact IB].
    intros nu. apply eval_single_term. exact F.
  - destruct (isv s) eqn:IS; [discriminate|]. destruct (is_base A s) eqn:IB; [|discriminate]. cbn [negb andb].
    intros X; injection X as <- <-. right. auto.
Qed.

Lemma bsym_image_spec isv sigma s s' : bsym_image isv sigma s = Some s' -> BF isv sigma s s'.
Proof.
  unfold bsym_image. destruct (pm_get s sigma) as [e|] eqn:G.
  - destruct (lin_single e) as [[s1 k]|] eqn:LS; [|discriminate].
    destruct (Z.eqb_spec k 1) as [->|]; [|discriminate]. destruct (Z.eqb_spec (lc e) 0) as [Z0|]; [|discriminate]. cbn [andb].
    intros X; injection X as <-. left. rewrite G. f_equal. symmetry. apply (lin_single_lsym _ _ LS Z0).
  - destruct (isv s) eqn:IS; [discriminate|]. intros X; injection X as <-. right. auto.
Qed.

Definition other_fact (isv : sym -> bool) (cs : bool) (mode : mmode) (P : vstate2) (sigma : pmap lin) (defer : list (lin * lin)) (sr : vregion) : Prop :=
  match vr_kind sr with
  | RK_fake _ _ => True
  | RK_fs => exists pr, rgn_get (vs_rgn P) FSB = Some pr /\ vr_kind pr = RK_fs /\ rc_fact cs true P sr pr 0 defer
  | RK_arg => exists b' c pr, RB isv P sigma (vr_base sr) b' c /\ rgn_get (vs_rgn P) b' = Some pr
                              /\ (vr_kind pr = RK_arg \/ (mode = MM_call /\ exists cid fl, vr_kind pr = RK_fake cid fl))
                              /\ rc_fact cs false P sr pr c defer
  | RK_flag owner => exists owner' b' pr, BF isv sigma owner owner' /\ BF isv sigma (vr_base sr) b'
                                       /\ rgn_get (vs_rgn P) b' = Some pr /\ vr_kind pr = RK_flag owner'
                                       /\ rc_fact cs true P sr pr 0 defer
  | RK_shadow of_ => exists of' c pr, (((of_ = SP0 \/ of_ = DATA) /\ of' = of_ /\ c = 0)
                                        \/ (of_ <> SP0 /\ of_ <> DATA /\ of' <> SP0 /\ of' <> DATA /\ of' <> FSB /\ RB isv P sigma of_ of' c))
                                   /\ Pos.eqb of' DATA = Pos.eqb of_ DATA /\ c mod 8 = 0
                                   /\ rgn_shadow_of (vs_rgn P) of' = Some pr
                                   /\ match mode with
                                      | MM_cut => c = 0 /\ BF isv sigma (vr_base sr) (vr_base pr) /\ rc_fact cs (negb (Pos.eqb of' SP0)) P sr pr 0 defer
                                      | MM_call => BL isv sigma (vr_base sr) (laddc (lsym (vr_base pr)) (c / 8)) /\ rc_fact cs (Pos.eqb of_ DATA) P sr pr (c / 8) defer
                                      end
  end.

Lemma other_fact_mono isv cs mode P sg sg' d d' sr :
  sub_sigma sg sg' -> binds_only isv pm_empty sg' -> incl d d' -> other_fact isv cs mode P sg d sr -> other_fact isv cs mode P sg' d' sr.
Proof.
  intros SUB BO INC. unfold other_fact. destruct (vr_kind sr); intros H.
  - exact I.
  - destruct H as (b' & c & pr & R & G & K & RC). exists b', c, pr. split; [eapply RB_mono; eauto|]. split; [exact G|]. split; [exact K|]. eapply rc_fact_mono; eauto.
  - destruct H as (o' & b' & pr & B1 & B2 & G & K & RC). exists o', b', pr. split; [eapply BF_mono; eauto|]. split; [eapply BF_mono; eauto|].
    split; [exact G|]. split; [exact K|]. eapply rc_fact_mono; eauto.
  - destruct H as (of' & c & pr & R & DD & CM & G & MM). exists of', c, pr. split.
    { destruct R as [R|(N1 & N2 & N3 & N4 & N5 & R)]; [left; exact R|right]. repeat (split; [assumption|]). eapply RB_mono; eauto. }
    split; [exact DD|]. split; [exact CM|]. split; [exact G|].
    destruct mode.
    + destruct MM as (C0 & B & RC). split; [exact C0|]. split; [eapply BF_mono; eauto|]. eapply rc_fact_mono; eauto.
    + destruct MM as (B & RC). split; [eapply BL_mono; eauto|]. eapply rc_fact_mono; eauto.
  - destruct H as (pr & G & K & RC). exists pr. split; [exact G|]. split; [exact K|]. eapply rc_fact_mono; eauto.
Qed.

Lemma match_others_spec isv cs mode P : forall ls acc acc',
  match_others isv cs mode P ls acc = inl acc' ->
  binds_only isv pm_empty (fst acc') ->
  sub_sigma (fst acc) (fst acc') /\ incl (snd acc) (snd acc')
  /\ (forall s0, binds_only isv s0 (fst acc) -> binds_only isv s0 (fst acc'))
  /\ (forall sr, In sr ls -> other_fact isv cs mode P (fst acc') (snd acc') sr).
Proof.
  induction ls as [|sr ls' IH]; intros acc acc' H BO; cbn [match_others] in H.
  - injection H as <-. split; [apply sub_sigma_refl|]. split; [apply incl_refl|]. split; [auto|]. intros ? [].
  - assert (CONT : forall acc1, match_others isv cs mode P ls' acc1 = inl acc' ->
              sub_sigma (fst acc) (fst acc1) -> incl (snd acc) (snd acc1) ->
              (forall s0, binds_only isv s0 (fst acc) -> binds_only isv s0 (fst acc1)) ->
              (sub_sigma (fst acc1) (fst acc') -> incl (snd acc1) (snd acc') -> other_fact isv cs mode P (fst acc') (snd acc') sr) ->
              sub_sigma (fst acc) (fst acc') /\ incl (snd acc) (snd acc')
              /\ (forall s0, binds_only isv s0 (fst acc) -> binds_only isv s0 (fst acc'))
              /\ (forall x, In x (sr :: ls') -> other_fact isv cs mode P (fst acc') (snd acc') x)).
    { intros acc1 H1 U1 I1 O1 OF. destruct (IH _ _ H1 BO) as (U2 & I2 & O2 & OF2).
      split; [eapply sub_sigma_trans; eauto|]. split; [eapply incl_tran; eauto|]. split; [auto|].
      intros x [<-|Hx]; [apply OF; auto|apply OF2; exact Hx]. }
    destruct (vr_kind sr) as [cid fl| |owner|of_|] eqn:K.
    + (* [comment removed for export] *) eapply CONT; [exact H|apply sub_sigma_refl|apply incl_refl|auto|]. intros _ _. unfold other_fact. rewrite K. exact I.
    + (* [comment removed for export] *)
      destruct (resolve_base isv P (fst acc) (vr_base sr)) as [[b' c]|] eqn:RBq; [|discriminate].
      destruct (rgn_get (vs_rgn P) b') as [pr|] eqn:GP; [|discriminate].
      assert (KOK : (vr_kind pr = RK_arg \/ (mode = MM_call /\ exists cid fl, vr_kind pr = RK_fake cid fl))
                    /\ exists acc1, match_region_cells isv cs false P sr pr c acc = inl acc1 /\ match_others isv cs mode P ls' acc1 = inl acc').
      { destruct (vr_kind pr) as [cid fl| | | |] eqn:KP; destruct mode; try discriminate.
        all: destruct (match_region_cells isv cs false P sr pr c acc) as [acc1|] eqn:MC; try discriminate.
        all: split; [| exists acc1; split; [reflexivity| exact H]].
        - right. split; [reflexivity|]. exists cid, fl. reflexivity.
        - left; reflexivity.
        - left; reflexivity. }
      destruct KOK as (KK & acc1 & MC & H1).
      destruct (match_region_cells_spec _ _ _ _ _ _ _ _ _ MC) as (U4 & I4 & O4 & RC).
      eapply CONT; [exact H1|exact U4|exact I4|exact O4|]. intros U5 I5. unfold other_fact. rewrite K.
      exists b', c, pr. split.
      { eapply RB_mono; [|exact BO|apply (resolve_base_spec _ _ _ _ _ _ RBq)]. eapply sub_sigma_trans; eauto. }
      split; [exact GP|]. split; [exact KK|]. eapply rc_fact_mono; [exact I5|exact RC].
    + (* [comment removed for export] *)
      destruct (bsym_image isv (fst acc) owner) as [owner'|] eqn:S1; [|discriminate].
      destruct (bsym_image isv (fst acc) (vr_base sr)) as [b'|] eqn:S2; [|discriminate].
      destruct (rgn_get (vs_rgn P) b') as [pr|] eqn:GP; [|discriminate].
      destruct (vr_kind pr) as [| |o'| |] eqn:KP; try discriminate.
      destruct (Pos.eqb_spec o' owner') as [->|]; [|discriminate].
      destruct (match_region_cells isv cs true P sr pr 0 acc) as [acc1|] eqn:MC; [|discriminate].
      destruct (match_region_cells_spec _ _ _ _ _ _ _ _ _ MC) as (U4 & I4 & O4 & RC).
      eapply CONT; [exact H|exact U4|exact I4|exact O4|]. intros U5 I5. unfold other_fact. rewrite K.
      exists owner', b', pr.
      split; [eapply BF_mono; [eapply sub_sigma_trans; [exact U4|exact U5]|exact (bsym_image_spec _ _ _ _ S1)]|].
      split; [eapply BF_mono; [eapply sub_sigma_trans; [exact U4|exact U5]|exact (bsym_image_spec _ _ _ _ S2)]|].
      split; [exact GP|]. split; [exact KP|]. eapply rc_fact_mono; [exact I5|exact RC].
    + (* [comment removed for export] *)
      match type of H with (match ?x with _ => _ end) = _ => destruct x as [[of' c]|] eqn:RS; [|discriminate] end.
      destruct (Bool.eqb (Pos.eqb of' DATA) (Pos.eqb of_ DATA)) eqn:DD; [|discriminate]. cbn [negb] in H.
      destruct (Z.eqb_spec (c mod 8) 0) as [CM|]; [|discriminate]. cbn [negb] in H.
      destruct (rgn_shadow_of (vs_rgn P) of') as [pr|] eqn:GP; [|discriminate].
      assert (CASES : forall sg, sub_sigma (fst acc) sg -> binds_only isv pm_empty sg ->
                ((of_ = SP0 \/ of_ = DATA) /\ of' = of_ /\ c = 0)
                \/ (of_ <> SP0 /\ of_ <> DATA /\ of' <> SP0 /\ of' <> DATA /\ of' <> FSB /\ RB isv P sg of_ of' c)).
      { intros sg SUBg BOg.
        destruct (Pos.eqb_spec of_ SP0) as [->|N1]; [left; split; [now left|]|destruct (Pos.eqb_spec of_ DATA) as [->|N2]; [left; split; [now right|]|right]].
        - cbn in RS. injection RS as <- <-. auto.
        - cbn in RS. injection RS as <- <-. auto.
        - cbn [orb] in RS. destruct (resolve_base isv P (fst acc) of_) as [[of1 c1]|] eqn:RS1; [|discriminate].
          destruct (Pos.eqb_spec of1 SP0); [discriminate|]. destruct (Pos.eqb_spec of1 DATA); [discriminate|]. destruct (Pos.eqb_spec of1 FSB); [discriminate|].
          cbn [orb] in RS. injection RS as <- <-.
          split; [exact N1|]. split; [exact N2|]. repeat (split; [assumption|]).
          eapply RB_mono; [exact SUBg|exact BOg|apply (resolve_base_spec _ _ _ _ _ _ RS1)]. }
      assert (DD' : Pos.eqb of' DATA = Pos.eqb of_ DATA) by (destruct (Pos.eqb of' DATA), (Pos.eqb of_ DATA); try reflexivity; discriminate).
      destruct mode.
      * destruct (bind_sym isv (fst acc) (vr_base sr) (vr_base pr)) as [s1|] eqn:B1; [|discriminate].
        destruct (Z.eqb_spec c 0) as [C0|]; [|discriminate]. cbn [negb] in H.
        destruct (match_region_cells isv cs (negb (Pos.eqb of' SP0)) P sr pr 0 (s1, snd acc)) as [acc1|] eqn:MC; [|discriminate].
        destruct (bind_sym_spec _ _ _ _ _ B1) as (U1 & O1 & F1).
        destruct (match_region_cells_spec _ _ _ _ _ _ _ _ _ MC) as (U4 & I4 & O4 & RC). cbn [fst snd] in U4, I4, O4, RC.
        eapply CONT; [exact H|eapply sub_sigma_trans; [exact U1|exact U4]|exact I4|intros s0 HB; apply O4, O1; exact HB|].
        intros U5 I5. unfold other_fact. rewrite K. exists of', c, pr. split.
        { apply CASES; [|exact BO]. eapply sub_sigma_trans; [exact U1|]. eapply sub_sigma_trans; [exact U4|exact U5]. }
        split; [exact DD'|]. split; [exact CM|]. split; [exact GP|]. split; [exact C0|]. split.
        { eapply BF_mono; [eapply sub_sigma_trans; [exact U4|exact U5]|]. exact (bind_sym_BF _ _ _ _ _ B1). }
        eapply rc_fact_mono; [exact I5|exact RC].
      * destruct (bind_lin isv (fst acc) (vr_base sr) (laddc (lsym (vr_base pr)) (c / 8))) as [s1|] eqn:B1; [|discriminate].
        destruct (match_region_cells isv cs (Pos.eqb of_ DATA) P sr pr (c / 8) (s1, snd acc)) as [acc1|] eqn:MC; [|discriminate].
        destruct (bind_lin_spec _ _ _ _ _ B1) as (U1 & O1 & F1).
        destruct (match_region_cells_spec _ _ _ _ _ _ _ _ _ MC) as (U4 & I4 & O4 & RC). cbn [fst snd] in U4, I4, O4, RC.
        eapply CONT; [exact H|eapply sub_sigma_trans; [exact U1|exact U4]|exact I4|intros s0 HB; apply O4, O1; exact HB|].
        intros U5 I5. unfold other_fact. rewrite K. exists of', c, pr. split.
        { apply CASES; [|exact BO]. eapply sub_sigma_trans; [exact U1|]. eapply sub_sigma_trans; [exact U4|exact U5]. }
        split; [exact DD'|]. split; [exact CM|]. split; [exact GP|]. split.
        { eapply BL_mono; [eapply sub_sigma_trans; [exact U4|exact U5]|exact BO|exact F1]. }
        eapply rc_fact_mono; [exact I5|exact RC].
    + (* [comment removed for export] *)
      destruct (rgn_get (vs_rgn P) FSB) as [pr|] eqn:GP; [|discriminate].
      destruct (vr_kind pr) as [| | | |] eqn:KP; try discriminate.
      destruct (match_region_cells isv cs true P sr pr 0 acc) as [acc1|] eqn:MC; [|discriminate].
      destruct (match_region_cells_spec _ _ _ _ _ _ _ _ _ MC) as (U4 & I4 & O4 & RC).
      eapply CONT; [exact H|exact U4|exact I4|exact O4|]. intros U5 I5. unfold other_fact. rewrite K.
      exists pr. split; [exact GP|]. split; [exact KP|]. eapply rc_fact_mono; [exact I5|exact RC].
Qed.

(* [comment removed for export] *)
Lemma match_others_binds_only isv cs mode P : forall l acc1 accx,
  match_others isv cs mode P l acc1 = inl accx -> binds_only isv pm_empty (fst acc1) -> binds_only isv pm_empty (fst accx).
Proof.
  induction l as [|sr t IH]; intros acc1 accx Hx BO1; cbn [match_others] in Hx.
  - injection Hx as <-. exact BO1.
  - destruct (vr_kind sr).
    + eapply IH; eauto.
    + destruct (resolve_base _ _ _ _) as [[b' c]|]; [|discriminate]. destruct (rgn_get _ _) as [pr|]; [|discriminate].
      destruct (vr_kind pr); destruct mode; try discriminate; destruct (match_region_cells _ _ _ _ _ _ _ _) as [acc2|] eqn:MC; try discriminate;
        destruct (match_region_cells_spec _ _ _ _ _ _ _ _ _ MC) as (_ & _ & O4 & _); eapply IH; eauto.
    + destruct (bsym_image _ _ _) as [o'|]; [|discriminate]. destruct (bsym_image _ _ _) as [b'|]; [|discriminate].
      destruct (rgn_get _ _) as [pr|]; [|discriminate]. destruct (vr_kind pr); try discriminate. destruct (Pos.eqb _ _); [|discriminate].
      destruct (match_region_cells _ _ _ _ _ _ _ _) as [acc2|] eqn:MC; try discriminate.
      destruct (match_region_cells_spec _ _ _ _ _ _ _ _ _ MC) as (_ & _ & O4 & _); eapply IH; eauto.
    + match type of Hx with (match ?x with _ => _ end) = _ => destruct x as [[of' c]|]; [|discriminate] end.
      destruct (Bool.eqb (Pos.eqb of' DATA) (Pos.eqb of_ DATA)); [|discriminate]. cbn [negb] in Hx.
      destruct (Z.eqb (c mod 8) 0); [|discriminate]. cbn [negb] in Hx.
      destruct (rgn_shadow_of (vs_rgn P) of') as [pr|]; [|discriminate]. cbn iota in Hx.
      destruct mode.
      * destruct (bind_sym isv (fst acc1) (vr_base sr) (vr_base pr)) as [s1|] eqn:B1; [|discriminate].
        destruct (Z.eqb c 0); [|discriminate]. cbn [negb] in Hx.
        destruct (match_region_cells _ _ _ _ _ _ _ _) as [acc2|] eqn:MC; try discriminate.
        destruct (bind_sym_spec _ _ _ _ _ B1) as (_ & Ob & _).
        destruct (match_region_cells_spec _ _ _ _ _ _ _ _ _ MC) as (_ & _ & O4 & _). cbn [fst] in O4. eapply IH; eauto.
      * destruct (bind_lin isv (fst acc1) (vr_base sr) (laddc (lsym (vr_base pr)) (c / 8))) as [s1|] eqn:B1; [|discriminate].
        destruct (match_region_cells _ _ _ _ _ _ _ _) as [acc2|] eqn:MC; try discriminate.
        destruct (bind_lin_spec _ _ _ _ _ B1) as (_ & Ob & _).
        destruct (match_region_cells_spec _ _ _ _ _ _ _ _ _ MC) as (_ & _ & O4 & _). cbn [fst] in O4. eapply IH; eauto.
    + destruct (rgn_get _ _) as [pr|]; [|discriminate]. destruct (vr_kind pr); try discriminate.
      destruct (match_region_cells _ _ _ _ _ _ _ _) as [acc2|] eqn:MC; try discriminate.
      destruct (match_region_cells_spec _ _ _ _ _ _ _ _ _ MC) as (_ & _ & O4 & _); eapply IH; eauto.
Qed.

Lemma match_regions_spec_cut isv cs S P sigma1 defer1 :
  match_regions isv cs MM_cut S P (pm_empty, []) = inl (sigma1, defer1) ->
  bases_distinct (map vr_base (fakes_of (vs_rgn P))) = true
  /\ binds_only isv pm_empty sigma1
  /\ length (fakes_of (vs_rgn S)) = length (fakes_of (vs_rgn P))
  /\ (forall i sr pr, nth_error (fakes_of (vs_rgn S)) i = Some sr -> nth_error (fakes_of (vs_rgn P)) i = Some pr ->
        fake_fact isv cs P sigma1 defer1 sr pr)
  /\ (forall sr, In sr (vs_rgn S) -> other_fact isv cs MM_cut P sigma1 defer1 sr).
Proof.
  unfold match_regions.
  destruct (bases_distinct (map vr_base (fakes_of (vs_rgn P)))) eqn:BD; [|discriminate]. cbn [negb].
  destruct (match_fakes isv cs P (fakes_of (vs_rgn S)) (fakes_of (vs_rgn P)) (pm_empty, [])) as [acc1|] eqn:MF; [|discriminate].
  intros H.
  destruct (match_fakes_spec _ _ _ _ _ _ _ MF) as (U1 & I1 & O1 & LEN & FF). cbn [fst snd] in U1, I1, O1.
  assert (BO1 : binds_only isv pm_empty (fst acc1)) by (apply O1; intros k e Hk; left; exact Hk).
  pose proof (match_others_binds_only _ _ _ _ _ _ _ H BO1) as BOF. cbn [fst] in BOF.
  destruct (match_others_spec _ _ _ _ _ _ _ H BOF) as (U2 & I2 & O2 & OF). cbn [fst snd] in U2, I2, OF.
  split; [reflexivity|]. split; [exact BOF|]. split; [exact LEN|]. split; [|exact OF].
  intros i sr pr X Y. eapply fake_fact_mono; [exact U2|exact I2|]. eapply FF; eauto.
Qed.

(* [comment removed for export] *)
Lemma match_regions_spec_call isv cs S P sigma0 sigma1 defer1 :
  match_regions isv cs MM_call S P (sigma0, []) = inl (sigma1, defer1) ->
  binds_only isv pm_empty sigma0 ->
  fakes_of (vs_rgn S) = []
  /\ bases_distinct (map vr_base (fakes_of (vs_rgn P))) = true
  /\ sub_sigma sigma0 sigma1 /\ binds_only isv pm_empty sigma1
  /\ (forall sr, In sr (vs_rgn S) -> other_fact isv cs MM_call P sigma1 defer1 sr).
Proof.
  unfold match_regions.
  destruct (bases_distinct (map vr_base (fakes_of (vs_rgn P)))) eqn:BD; [|discriminate]. cbn [negb].
  destruct (fakes_of (vs_rgn S)) as [|f0 ft] eqn:FS; [|discriminate].
  intros H BO0.
  pose proof (match_others_binds_only _ _ _ _ _ _ _ H BO0) as BOF. cbn [fst] in BOF.
  destruct (match_others_spec _ _ _ _ _ _ _ H BOF) as (U2 & I2 & O2 & OF). cbn [fst snd] in U2, I2, OF.
  split; [reflexivity|]. split; [reflexivity|]. split; [exact U2|]. split; [exact BOF|exact OF].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma cons_entailed_f_sound SP sigma cs nu :
  sat nu SP -> cons_entailed_f SP sigma cs = true -> Forall (fun c => eval (vsubst nu sigma) c <= 0) cs.
Proof.
  intros HS H. unfold cons_entailed_f in H. rewrite forallb_l_eq, forallb_forall in H. apply Forall_forall. intros c Hc.
  specialize (H c Hc). cbv zeta in H. rewrite <- eval_lsubst.
  assert (H' : con_weaker_in (lsubst sigma c) (scons SP) = true \/ check_nonpos SP (lsubst sigma c) = true).
  { destruct (con_weaker_in (lsubst sigma c) (scons SP)); [left; reflexivity|right; exact H]. }
  clear H. destruct H' as [H|H].
  - unfold con_weaker_in in H. rewrite existsb_l_eq in H. apply existsb_exists in H as [p [Hp Hw]].
    destruct (terms_eqb (lt (lsubst sigma c)) (lt p)) eqn:T; [|discriminate]. rename Hw into L.
    apply terms_eqb_sound in T. apply Z.leb_le in L.
    pose proof (proj1 (proj2 HS)) as HC. rewrite Forall_forall in HC. specialize (HC p Hp).
    unfold eval in HC |- *. rewrite T. lia.
  - exact (check_nonpos_sound nu SP HS _ H).
Qed.

Section SoundF.
  Variable SEGS : list Segment.
  Variables P P' : vparams.
  Variables E E' : venv.
  Hypothesis Hframe : vp_frame P' = vp_frame P.
  Hypothesis Hsplo : vp_splo P' = vp_splo P.
  Hypothesis Hsp0 : e_sp0 E' = e_sp0 E.

  Theorem match_state_f_sound isv skip cs sigma0 S Pst sigma nu regs mem :
    match_state_f isv skip cs sigma0 S Pst = MOk sigma ->
    sat nu (vs_store Pst) -> gamma_conddef nu Pst -> gamma_moddef nu Pst -> gamma_valset nu Pst ->
    gamma_regs nu Pst regs -> gamma_slots SEGS P E nu Pst mem -> gamma_globs SEGS P nu Pst mem ->
    gamma_nul SEGS P E Pst mem ->
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
    unfold match_state_f. intros HM HS HC HMo HV HR HSl HG HN WS WG. rewrite match_state_g_eq in HM.
    set (S0 := set_store S (drop_cons (vs_store S))) in HM.
    destruct (match_state isv skip cs sigma0 S0 Pst) as [sg|] eqn:M0; [|discriminate].
    destruct (cons_entailed_f (vs_store Pst) sg (scons (vs_store S))) eqn:CE; [|discriminate].
    injection HM as ->.
    destruct (match_state_sound SEGS P P' E E' Hframe Hsplo Hsp0 isv skip cs sigma0 S0 Pst sigma nu regs mem
                M0 HS HC HMo HV HR HSl HG HN WS WG) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10).
    split; [exact A1|]. split; [exact A2|]. split; [|exact (conj A4 (conj A5 (conj A6 (conj A7 (conj A8 (conj A9 A10))))))].
    destruct A3 as (B1 & _ & B3). split; [exact B1|]. split; [|exact B3].
    exact (cons_entailed_f_sound _ _ _ _ HS CE).
  Qed.
End SoundF.

Section Sound2.
  Variable SEGS : list Segment.
  Variable P : vparams2.
  Variable E : venv2.
  Variable mem0 : word -> option byte.

  Local Notation gammaP := (gamma2 SEGS P E mem0).

  (* [comment removed for export] *)
  Lemma load_cstate2_v1_facts X pc ctx :
    cstate2_ok P X = true ->
    (forall off w v, In (off, (w, v)) (vs_slots (v1 (load_cstate2 P X pc ctx))) -> - vp_frame (p1 P) <= off /\ 0 < w /\ off + w <= 0 /\ v <> None)
    /\ (forall a w v, In (a, (w, v)) (vs_globs (v1 (load_cstate2 P X pc ctx))) -> 0 <= a /\ 0 < w /\ a + w <= vp_splo (p1 P) - vp_frame (p1 P) /\ v <> None)
    /\ state_below (v1 (load_cstate2 P X pc ctx)) /\ (FIRST_FRESH2 <= cs_next (c1 X))%positive.
  Proof.
    intros HX. destruct (cstate2_ok_parts _ _ HX) as (H1 & H2 & _). destruct (cstate2_wf_next _ H2) as [J0 WF].
    rewrite load_cstate2_v1. split; [|split; [|split; [|exact J0]]].
    - intros; eapply cstate_ok_slots; eauto.
    - intros; eapply cstate_ok_globs; eauto.
    - apply (proj1 (load_cstate_below (c1 X) pc ctx WF)).
  Qed.

  Lemma fix_val2_le E0 s z : fix_val2 E0 s = Some z -> (s <= LAST_FIXED2)%positive.
  Proof.
    unfold fix_val2. destruct (fix_val (ev1 E0) s) as [z0|] eqn:F.
    - intros _. pose proof (fix_val_fixed _ _ _ F). unfold LAST_FIXED, LAST_FIXED2 in *. lia.
    - unfold SP8, DATA8, FSB, FS8, LAST_FIXED2.
      destruct (Pos.eqb_spec s 64); [subst; intros; simpl; lia|].
      destruct (Pos.eqb_spec s 65); [subst; intros; simpl; lia|].
      destruct (Pos.eqb_spec s 66); [subst; intros; simpl; lia|].
      destruct (Pos.eqb_spec s 67); [subst; intros; simpl; lia|].
      destruct (Pos.leb_spec 19 s); destruct (Pos.leb_spec s 26); simpl; try discriminate. intros; lia.
  Qed.

  Lemma gamma_fix2_ext E0 nu nu' : ext FIRST_FRESH2 nu nu' -> gamma_fix2 E0 nu -> gamma_fix2 E0 nu'.
  Proof.
    intros X H s z Hs. rewrite (X s); [exact (H s z Hs)|].
    pose proof (fix_val2_le _ _ _ Hs). unfold LAST_FIXED2, FIRST_FRESH2 in *. lia.
  Qed.

  Lemma binds_only_ext nu sigma :
    binds_only isv_join2 pm_empty sigma -> ext FIRST_FRESH2 nu (vsubst nu sigma).
  Proof.
    intros BO s Hs. unfold vsubst. destruct (pm_get s sigma) as [e|] eqn:Gs; [|reflexivity].
    destruct (BO _ _ Gs) as [Hg|Hv]; [rewrite pm_get_empty in Hg; discriminate|].
    unfold isv_join2 in Hv. apply Pos.leb_le in Hv. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma match_divdefs_sound sigma S A nu :
    match_divdefs sigma S A = true -> gamma_divdef nu A -> gamma_divdef (vsubst nu sigma) S.
  Proof.
    intros H GA q x m Hq. unfold match_divdefs in H. rewrite forallb_forall in H.
    specialize (H _ (pm_elements_complete (vs_divdef S) q Hq)). cbn beta iota in H.
    destruct (sym_image sigma q) as [q'|] eqn:SI; [|discriminate].
    destruct (pm_get q' (vs_divdef A)) as [[x' m']|] eqn:Hq'; [|discriminate].
    apply andb_prop in H as [Hm Hx]. apply Z.eqb_eq in Hm. subst m'. apply lin_eqb_eq in Hx.
    destruct (GA _ _ _ Hq') as [M0 V]. split; [exact M0|].
    rewrite (sym_image_eval _ _ _ _ SI), V, <- Hx, eval_lsubst. reflexivity.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition rgn_wf (r : vregion) : Prop :=
    vr_lo r <= vr_hi r
    /\ (forall off w v, In (off, (w, v)) (vr_cells r) -> vr_lo r <= off /\ 0 < w /\ off + w <= vr_hi r)
    /\ (forall lo hi, In (lo, hi) (vr_w r) -> vr_lo r <= lo /\ hi <= vr_hi r)
    /\ (forall lo hi, In (lo, hi) (vr_nul r) -> vr_lo r <= lo /\ lo <= hi /\ hi < vr_hi r)
    /\ (is_data_shadow r = true -> vr_cells r = [] /\ vr_w r = [] /\ vr_nul r = []).

  Lemma land_255_zwrap8 x : Z.land x 255 = zwrap 8 x.
  Proof. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. unfold zwrap. reflexivity. Qed.

  Lemma sh_cover_in m o x : sh_cover m o = Some x -> In x m.
  Proof. unfold sh_cover. intros H. apply find_some in H as [H _]. eapply cm_overlapping_in; eauto. Qed.

  Lemma run_holds_sub mem a w b a' w' :
    run_holds SEGS mem a w b -> a <= a' -> a' + w' <= a + w -> run_holds SEGS mem a' w' b.
  Proof. intros H H1 H2 i Hi. replace (a' + i) with (a + (a' - a + i)) by lia. apply H. lia. Qed.

  Lemma region_transfer nu sigma defer (A : vstate2) mem sr pr c exact :
    (forall e e', In (e, e') defer -> lsubst sigma e = e') ->
    rc_fact false exact A sr pr c defer ->
    rgn_wf sr ->
    is_shadow sr = is_shadow pr ->
    is_data_shadow pr = false \/ is_data_shadow sr = true ->
    rbase (vsubst nu sigma) sr = rbase nu pr + c ->
    region_ok SEGS P E nu A mem pr ->
    let nu' := vsubst nu sigma in
    0 <= rbase nu' sr + vr_lo sr /\ rbase nu' sr + vr_hi sr <= 2 ^ 64 /\ vr_lo sr <= vr_hi sr
    /\ (is_data_shadow sr = true -> vr_cells sr = [] /\ vr_w sr = [] /\ vr_nul sr = [])
    /\ region_cells_ok SEGS nu' mem sr
    /\ region_perm_ok SEGS P E nu' mem sr
    /\ region_nul_ok SEGS nu' mem sr.
  Proof.
    intros DEF (ED & _ & LO & HI & WI & NI & CF) (W0 & W1 & W2 & W3 & W4) SHEQ DSH RB (B1 & B2 & B3 & RD & RC & RP & RN & _).
    cbn zeta. rewrite RB.
    split; [lia|]. split; [lia|]. split; [exact W0|]. split; [exact W4|]. split; [|split].
    - (* [comment removed for export] *)
      intros off w v Hin. rewrite RB. destruct (W1 _ _ _ Hin) as (X1 & X2 & X3). split; [exact X1|]. split; [exact X2|]. split; [exact X3|].
      destruct v as [e|]; [|exact I].
      unfold cells_fact in CF. rewrite SHEQ in *. unfold rcell_holds. destruct (is_shadow pr) eqn:SHP.
      + destruct (CF _ _ _ Hin) as [(CE & COVR)|(CE & -> & e' & G & IN)].
        * rewrite CE. cbn [andb]. intros i Hi.
          destruct (COVR (off + c + i) ltac:(lia)) as (k' & w' & e' & INC & K12 & CE' & LCE).
          pose proof (RC _ _ _ INC) as (_ & _ & _ & RH).
          unfold rcell_holds in RH. rewrite SHP, CE' in RH. cbn [andb] in RH. rewrite <- LCE.
          destruct (RH (off + c + i - k') ltac:(lia)) as (kk & Hk & Hkv). exists kk. split; [|exact Hkv].
          rewrite <- Hk. f_equal. f_equal. lia.
        * rewrite CE. cbn [andb]. pose proof (RC _ _ _ G) as (_ & _ & _ & RH).
          unfold rcell_holds in RH. rewrite SHP in RH. cbn [andb] in RH.
          assert (EV : eval (vsubst nu sigma) e = eval nu e') by (rewrite <- eval_lsubst, (DEF _ _ IN); reflexivity).
          unfold cell_holds. rewrite EV. replace (rbase nu pr + c + off) with (rbase nu pr + (off + c)) by lia.
          destruct (lin_is_const e') eqn:CE'.
          -- destruct (RH 0 ltac:(lia)) as [k [Hk Hkv]]. exists [k]. rewrite Z.add_0_r in Hk. split; [cbn [Z.to_nat Pos.to_nat Pos.iter_op]; exact Hk|].
             rewrite bytes_le_single, Hkv, land_255_zwrap8, (eval_is_const _ _ CE'). reflexivity.
          -- exact RH.
      + destruct (CF _ _ _ Hin) as (e' & PC & IN).
        unfold path_cell in PC. destruct (cm_get (vr_cells pr) (off + c)) as [[w' [e''|]]|] eqn:G; try discriminate.
        destruct (Z.eqb_spec w w'); [|discriminate]. injection PC as ->. subst w'.
        pose proof (RC _ _ _ (cm_get_in _ _ _ G)) as (_ & _ & _ & RH). unfold rcell_holds in RH. rewrite SHP in RH. cbn [andb] in RH.
        assert (EV : eval (vsubst nu sigma) e = eval nu e') by (rewrite <- eval_lsubst, (DEF _ _ IN); reflexivity).
        unfold cell_holds in RH |- *. rewrite EV. replace (rbase nu pr + c + off) with (rbase nu pr + (off + c)) by lia. exact RH.
    - (* [comment removed for export] *)
      intros NDS. destruct DSH as [DSH|DSH]; [|rewrite DSH in NDS; discriminate]. destruct (RP DSH) as [RP1 RP2]. split.
      + intros off Hoff. rewrite RB. replace (rbase nu pr + c + off) with (rbase nu pr + (off + c)) by lia. apply RP1. lia.
      + intros lo hi off Hw Hoff. destruct (W2 _ _ Hw) as [Y1 Y2].
        unfold ranges_incl in WI. rewrite forallb_forall in WI. specialize (WI _ Hw). cbn [fst snd] in WI.
        destruct (in_ranges_sound _ _ _ WI) as (lo' & hi' & Hw' & Z1 & Z2).
        destruct (RP2 lo' hi' (off + c) Hw' ltac:(lia)) as (Q1 & Q2 & Q3 & Q4).
        rewrite RB. replace (rbase nu pr + c + off) with (rbase nu pr + (off + c)) by lia.
        split; [lia|]. split; [exact Q2|]. split; [exact Q3|exact Q4].
    - (* [comment removed for export] *)
      intros lo hi Hn. destruct (W3 _ _ Hn) as (Y1 & Y2 & Y3).
      unfold rnul_incl in NI. rewrite forallb_forall in NI. specialize (NI _ Hn). cbn [fst snd] in NI.
      unfold nul_implied in NI. apply existsb_exists in NI as [[lo2 hi2] [Hn2 Hb]]. cbn [fst snd] in Hb.
      apply andb_prop in Hb as [Hb1 Hb2]. apply Z.leb_le in Hb1. apply Z.leb_le in Hb2.
      destruct (RN _ _ Hn2) as (off & b & O1 & O2 & O3 & O4).
      exists (off - c), b. split; [lia|]. split; [lia|]. split; [|exact O4].
      rewrite RB. replace (rbase nu pr + c + (off - c)) with (rbase nu pr + off) by lia. exact O3.
  Qed.

  Lemma region_transfer_gen cs (P' : vparams2) (E' : venv2) nu sigma defer (A : vstate2) mem sr pr c exact :
    (forall e e', In (e, e') defer -> lsubst sigma e = e') ->
    sat nu (vs_store (v1 A)) ->
    rc_fact cs exact A sr pr c defer ->
    rgn_wf sr ->
    is_shadow sr = is_shadow pr ->
    is_data_shadow pr = false \/ is_data_shadow sr = true ->
    rbase (vsubst nu sigma) sr = rbase nu pr + c ->
    region_ok SEGS P E nu A mem pr ->
    (forall a, in_any_zone P' E' a = in_any_zone P E a) ->
    (forall a, in_rw_zones P' E' a = in_rw_zones P E a) ->
    (forall lo hi off, In (lo, hi) (vr_w sr) -> lo <= off < hi -> covered (unit_regions2 P' E') (rbase (vsubst nu sigma) sr + off) 1) ->
    let nu' := vsubst nu sigma in
    0 <= rbase nu' sr + vr_lo sr /\ rbase nu' sr + vr_hi sr <= 2 ^ 64 /\ vr_lo sr <= vr_hi sr
    /\ (is_data_shadow sr = true -> vr_cells sr = [] /\ vr_w sr = [] /\ vr_nul sr = [])
    /\ region_cells_ok SEGS nu' mem sr
    /\ region_perm_ok SEGS P' E' nu' mem sr
    /\ region_nul_ok SEGS nu' mem sr.
  Proof.
    intros DEF SAT (ED & _ & LO & HI & WI & NI & CF) (W0 & W1 & W2 & W3 & W4) SHEQ DSH RB (B1 & B2 & B3 & RD & RC & RP & RN & _) ZA ZW COV.
    cbn zeta. rewrite RB.
    split; [lia|]. split; [lia|]. split; [exact W0|]. split; [exact W4|]. split; [|split].
    - (* [comment removed for export] *)
      intros off w v Hin. rewrite RB. destruct (W1 _ _ _ Hin) as (X1 & X2 & X3). split; [exact X1|]. split; [exact X2|]. split; [exact X3|].
      destruct v as [e|]; [|exact I].
      unfold cells_fact in CF. rewrite SHEQ in *. unfold rcell_holds. destruct (is_shadow pr) eqn:SHP.
      + destruct (CF _ _ _ Hin) as [(CE & COVR)|(CE & -> & e' & G & IN)].
        * rewrite CE. cbn [andb]. intros i Hi.
          destruct (COVR (off + c + i) ltac:(lia)) as (k' & w' & e' & INC & K12 & CE' & LCE).
          pose proof (RC _ _ _ INC) as (_ & _ & _ & RH).
          unfold rcell_holds in RH. rewrite SHP, CE' in RH. cbn [andb] in RH. rewrite <- LCE.
          destruct (RH (off + c + i - k') ltac:(lia)) as (kk & Hk & Hkv). exists kk. split; [|exact Hkv].
          rewrite <- Hk. f_equal. f_equal. lia.
        * rewrite CE. cbn [andb]. pose proof (RC _ _ _ G) as (_ & _ & _ & RH).
          unfold rcell_holds in RH. rewrite SHP in RH. cbn [andb] in RH.
          assert (EV : eval (vsubst nu sigma) e = eval nu e') by (rewrite <- eval_lsubst, (DEF _ _ IN); reflexivity).
          unfold cell_holds. rewrite EV. replace (rbase nu pr + c + off) with (rbase nu pr + (off + c)) by lia.
          destruct (lin_is_const e') eqn:CE'.
          -- destruct (RH 0 ltac:(lia)) as [k [Hk Hkv]]. exists [k]. rewrite Z.add_0_r in Hk. split; [cbn [Z.to_nat Pos.to_nat Pos.iter_op]; exact Hk|].
             rewrite bytes_le_single, Hkv, land_255_zwrap8, (eval_is_const _ _ CE'). reflexivity.
          -- exact RH.
      + destruct (CF _ _ _ Hin) as (e' & PC & IN).
        assert (RH : cell_holds SEGS nu mem (rbase nu pr + (off + c)) w (Some e')).
        { eapply (path_cell_sound SEGS cs (v1 A) (vr_cells pr)); [exact PC|exact X2|exact SAT|].
          intros k0 w0 v0 Hk0. pose proof (RC _ _ _ Hk0) as (_ & _ & _ & RH0). unfold rcell_holds in RH0. rewrite SHP in RH0. cbn [andb] in RH0.
          destruct v0; [exact RH0|exact I]. }
        assert (EV : eval (vsubst nu sigma) e = eval nu e') by (rewrite <- eval_lsubst, (DEF _ _ IN); reflexivity).
        unfold cell_holds in RH |- *. rewrite EV. replace (rbase nu pr + c + off) with (rbase nu pr + (off + c)) by lia. exact RH.
    - (* [comment removed for export] *)
      intros NDS. destruct DSH as [DSH|DSH]; [|rewrite DSH in NDS; discriminate]. destruct (RP DSH) as [RP1 RP2]. split.
      + intros off Hoff. rewrite ZA, RB. replace (rbase nu pr + c + off) with (rbase nu pr + (off + c)) by lia. apply RP1. lia.
      + intros lo hi off Hw Hoff. destruct (W2 _ _ Hw) as [Y1 Y2].
        unfold ranges_incl in WI. rewrite forallb_forall in WI. specialize (WI _ Hw). cbn [fst snd] in WI.
        destruct (in_ranges_sound _ _ _ WI) as (lo' & hi' & Hw' & Z1 & Z2).
        destruct (RP2 lo' hi' (off + c) Hw' ltac:(lia)) as (Q1 & Q2 & Q3 & Q4).
        pose proof (COV _ _ _ Hw Hoff) as Q5. rewrite ZW. rewrite RB in Q5 |- *. replace (rbase nu pr + c + off) with (rbase nu pr + (off + c)) in Q5 |- * by lia.
        split; [lia|]. split; [exact Q2|]. split; [exact Q3|exact Q5].
    - (* [comment removed for export] *)
      intros lo hi Hn. destruct (W3 _ _ Hn) as (Y1 & Y2 & Y3).
      unfold rnul_incl in NI. rewrite forallb_forall in NI. specialize (NI _ Hn). cbn [fst snd] in NI.
      unfold nul_implied in NI. apply existsb_exists in NI as [[lo2 hi2] [Hn2 Hb]]. cbn [fst snd] in Hb.
      apply andb_prop in Hb as [Hb1 Hb2]. apply Z.leb_le in Hb1. apply Z.leb_le in Hb2.
      destruct (RN _ _ Hn2) as (off & b & O1 & O2 & O3 & O4).
      exists (off - c), b. split; [lia|]. split; [lia|]. split; [|exact O4].
      rewrite RB. replace (rbase nu pr + c + (off - c)) with (rbase nu pr + off) by lia. exact O3.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma bases_distinct_nodup : forall l, bases_distinct l = true -> List.NoDup l.
  Proof.
    induction l as [|x t IH]; cbn [bases_distinct]; intros H; [constructor|].
    apply andb_prop in H as [H1 H2]. constructor; [|exact (IH H2)].
    intros Hin.
    assert (X : existsb (Pos.eqb x) t = true) by (apply existsb_exists; exists x; split; [exact Hin|apply Pos.eqb_refl]).
    rewrite X in H1. discriminate.
  Qed.


  Lemma load_regions_in l r :
    In r (load_regions P l) -> (exists s, In s l /\ r = vregion_of s) \/ In r (std_regions P).
  Proof.
    unfold load_regions. intros H. apply in_app_iff in H as [H|H]; [left|right; exact H].
    apply in_map_iff in H as [s [Hs Hin]]. exists s. auto.
  Qed.

  Lemma std_regions_cases r :
    In r (std_regions P) -> (r = SHD P /\ has_asan P = true) \/ (r = FSR /\ has_asan P = true).
  Proof.
    unfold std_regions. destruct (has_asan P) eqn:HA.
    - intros [<-|[<-|[]]]; [left|right]; auto.
    - intros [].
  Qed.

  Lemma vregion_of_cells s k w v : In (k, (w, v)) (vr_cells (vregion_of s)) -> exists e, v = Some e /\ In (k, (w, e)) (sr_cells s).
  Proof. cbn [vregion_of vr_cells]. apply cm_of_list_in. Qed.

  Lemma reserved_base_false s :
    reserved_base s = false -> s <> SP0 /\ s <> DATA /\ s <> SP8 /\ s <> DATA8 /\ s <> FSB /\ s <> FS8.
  Proof.
    unfold reserved_base. intros H.
    repeat (apply Bool.orb_false_elim in H as [H ?X]).
    repeat split; intros ->; rewrite Pos.eqb_refl in *; discriminate.
  Qed.

  (* [comment removed for export] *)
  Lemma stored_not_data X s :
    cstate2_wf_b X = true -> In s (cs_rgn X) -> is_data_shadow (vregion_of s) = false.
  Proof.
    intros WF Hs. destruct (cstate2_wf_parts _ WF) as (_ & _ & _ & RB0 & _ & _ & _ & _ & SK).
    unfold is_data_shadow. cbn [vregion_of vr_kind]. destruct (sr_kind s) as [| | |o] eqn:K; cbn [rkind_of]; try reflexivity.
    destruct (Pos.eqb_spec o DATA) as [->|]; [|reflexivity]. exfalso.
    specialize (SK _ Hs). unfold skind_struct_ok in SK. rewrite K in SK. apply Bool.orb_prop in SK as [SK|SK].
    - apply andb_prop in SK as [SK _]. discriminate.
    - apply existsb_exists in SK as [t [Ht Hb]]. apply andb_prop in Hb as [Hb _]. apply andb_prop in Hb as [Hb _].
      apply Pos.eqb_eq in Hb.
      destruct (RB0 _ Ht) as [R|(o' & _ & _ & R)]; [|rewrite Hb in R; discriminate].
      destruct (reserved_base_false _ R) as (_ & ND & _). exact (ND Hb).
  Qed.

  Lemma srgn_wf_rgn_wf X s :
    cstate2_wf_b X = true -> In s (cs_rgn X) -> rgn_wf (vregion_of s).
  Proof.
    intros WF Hs. destruct (cstate2_wf_parts _ WF) as (_ & _ & BW & _).
    destruct (BW _ Hs) as [_ W]. unfold srgn_wf in W.
    apply andb_prop in W as [W W3]. apply andb_prop in W as [W W2]. apply andb_prop in W as [W0 W1].
    apply Z.leb_le in W0. rewrite forallb_forall in W1, W2, W3.
    split; [exact W0|]. split.
    { intros off w v Hin. destruct (vregion_of_cells _ _ _ _ Hin) as [e [-> Hin']].
      specialize (W1 _ Hin'). cbn beta iota in W1. apply andb_prop in W1 as [W1 C]. apply andb_prop in W1 as [A B].
      apply Z.leb_le in A. apply Z.ltb_lt in B. apply Z.leb_le in C. cbn [vregion_of vr_lo vr_hi]. lia. }
    split.
    { intros lo hi Hin. specialize (W2 _ Hin). cbn [fst snd] in W2. apply andb_prop in W2 as [A B]. apply Z.leb_le in A. apply Z.leb_le in B. cbn. lia. }
    split.
    { intros lo hi Hin. specialize (W3 _ Hin). cbn [fst snd] in W3. apply andb_prop in W3 as [W3 C]. apply andb_prop in W3 as [A B].
      apply Z.leb_le in A. apply Z.leb_le in B. apply Z.ltb_lt in C. cbn. lia. }
    intros DS. rewrite (stored_not_data _ _ WF Hs) in DS. discriminate.
  Qed.

  Lemma load_rgn_wf X pc ctx r :
    cstate2_ok P X = true -> In r (vs_rgn (load_cstate2 P X pc ctx)) -> rgn_wf r.
  Proof.
    intros HX Hin. destruct (cstate2_ok_parts _ _ HX) as (_ & WF & _).
    cbn [load_cstate2 vs_rgn] in Hin. apply load_regions_in in Hin as [[s [Hs ->]]|Hstd]; [eapply srgn_wf_rgn_wf; eauto|].
    apply std_regions_cases in Hstd as [[-> _]|[-> _]].
    - unfold rgn_wf, SHD. cbn. split; [lia|]. split; [intros ? ? ? []|]. split; [intros ? ? []|]. split; [intros ? ? []|]. intros _; auto.
    - unfold rgn_wf, FSR. cbn. split; [lia|]. split; [intros ? ? ? []|]. split; [intros lo hi [Y|[]]; injection Y as <- <-; lia|].
      split; [intros ? ? []|]. intros Y; discriminate.
  Qed.

  Lemma rgn_get_nodup l r : List.NoDup (map vr_base l) -> In r l -> rgn_get l (vr_base r) = Some r.
  Proof.
    induction l as [|x t IH]; intros ND Hin; [destruct Hin|]. cbn [map] in ND. inversion ND as [|y u NI ND']; subst.
    cbn [rgn_get]. destruct Hin as [<-|Hin]; [now rewrite Pos.eqb_refl|].
    destruct (Pos.eqb_spec (vr_base x) (vr_base r)) as [EQ|NE]; [|exact (IH ND' Hin)].
    exfalso. apply NI. rewrite EQ. apply in_map_iff. exists r; auto.
  Qed.

  Lemma map_base_load l : map vr_base (load_regions P l) = (map sr_base l ++ map vr_base (std_regions P))%list.
  Proof. unfold load_regions. rewrite map_app, map_map. reflexivity. Qed.

  Lemma load_bases_nodup X pc ctx :
    cstate2_wf_b X = true -> List.NoDup (map vr_base (vs_rgn (load_cstate2 P X pc ctx))).
  Proof.
    intros WF. destruct (cstate2_wf_parts _ WF) as (_ & _ & _ & RB0 & BD & _).
    cbn [load_cstate2 vs_rgn]. rewrite map_base_load.
    assert (ST : forall b, In b (map sr_base (cs_rgn X)) -> b <> DATA8 /\ b <> FSB).
    { intros b Hb. apply in_map_iff in Hb as [s0 [<- Hs0]].
      destruct (RB0 _ Hs0) as [R|(o & _ & _ & R)]; [|rewrite R; split; discriminate].
      destruct (reserved_base_false _ R) as (_&_&_&A&B&_). auto. }
    apply List.NoDup_app.
    - apply bases_distinct_nodup. exact BD.
    - unfold std_regions. destruct (has_asan P); cbn; repeat constructor; cbn; try tauto.
      intros [X1|[]]. discriminate.
    - intros b Hb Hstd. destruct (ST _ Hb) as [N1 N2].
      unfold std_regions in Hstd. destruct (has_asan P); cbn in Hstd; intuition congruence.
  Qed.

  Lemma stored_in_loaded X pc ctx t : In t (cs_rgn X) -> In (vregion_of t) (vs_rgn (load_cstate2 P X pc ctx)).
  Proof. intros H. cbn [load_cstate2 vs_rgn]. unfold load_regions. apply in_app_iff. left. apply in_map_iff. exists t; auto. Qed.

  Lemma stored_rgn_get X pc ctx t :
    cstate2_wf_b X = true -> In t (cs_rgn X) -> rgn_get (vs_rgn (load_cstate2 P X pc ctx)) (sr_base t) = Some (vregion_of t).
  Proof.
    intros WF Ht. change (sr_base t) with (vr_base (vregion_of t)).
    apply rgn_get_nodup; [apply load_bases_nodup; exact WF|apply stored_in_loaded; exact Ht].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma fakes_of_in l r : In r (fakes_of l) -> In r l /\ exists cid fl, vr_kind r = RK_fake cid fl.
  Proof.
    induction l as [|x t IH]; cbn [fakes_of]; [intros []|].
    destruct (vr_kind x) as [cid fl| | | |] eqn:K; intros H;
      try (destruct (IH H) as [H1 H2]; split; [right; exact H1|exact H2]).
    destruct H as [<-|H]; [split; [now left|exists cid, fl; exact K]|].
    destruct (IH H) as [H1 H2]; split; [right; exact H1|exact H2].
  Qed.

  Lemma in_fakes_of l r cid fl : In r l -> vr_kind r = RK_fake cid fl -> In r (fakes_of l).
  Proof.
    induction l as [|x t IH]; cbn [fakes_of]; [intros []|].
    intros [<-|H] K.
    - rewrite K. now left.
    - specialize (IH H K). destruct (vr_kind x); [right|..]; exact IH.
  Qed.

  Lemma fakes_of_spec l r : In r (fakes_of l) <-> In r l /\ exists cid fl, vr_kind r = RK_fake cid fl.
  Proof.
    split; [apply fakes_of_in|]. intros [H [cid [fl K]]]. eapply in_fakes_of; eauto.
  Qed.

  Lemma in_nth_error {T} (l : list T) x : In x l -> exists i, nth_error l i = Some x.
  Proof. intros H. apply In_nth_error in H. exact H. Qed.

  Lemma nth_error_len {T U} (l1 : list T) (l2 : list U) i x :
    nth_error l1 i = Some x -> length l1 = length l2 -> exists y, nth_error l2 i = Some y.
  Proof.
    intros H L. destruct (nth_error l2 i) as [y|] eqn:EN; [eauto|].
    apply nth_error_None in EN. assert (i < length l1)%nat by (apply nth_error_Some; congruence). lia.
  Qed.

  Lemma map_ext_nth {T U V} (f : T -> V) (g : U -> V) : forall (l1 : list T) (l2 : list U),
    length l1 = length l2 -> (forall i x y, nth_error l1 i = Some x -> nth_error l2 i = Some y -> f x = g y) -> map f l1 = map g l2.
  Proof.
    induction l1 as [|a t IH]; intros [|b u] L H; cbn in *; try discriminate; [reflexivity|].
    f_equal; [exact (H O a b eq_refl eq_refl)|]. apply IH; [lia|]. intros i x y X Y. exact (H (S i) x y X Y).
  Qed.

  Lemma own_flags_fakes (A : vstate2) nu :
    own_flags A nu = map (fun r => match vr_kind r with RK_fake _ fl => nu fl | _ => 0 end) (fakes_of (vs_rgn A)).
  Proof.
    unfold own_flags. induction (vs_rgn A) as [|x t IH]; [reflexivity|]. cbn [flat_map fakes_of].
    destruct (vr_kind x) eqn:K; cbn [map app]; rewrite ?K, IH; reflexivity.
  Qed.

  Lemma live_matches_eq : forall l live, live_matches live l = true -> live = map sr_base (List.filter is_fake l).
  Proof.
    induction l as [|s t IH]; intros live H; cbn [live_matches List.filter] in H |- *.
    - destruct live; [reflexivity|discriminate].
    - destruct (is_fake s).
      + destruct live as [|x l']; [discriminate|]. apply andb_prop in H as [H1 H2]. apply Pos.eqb_eq in H1. subst x.
        cbn [map]. f_equal. apply IH. exact H2.
      + apply IH. exact H.
  Qed.

  Lemma bases_distinct_filter f : forall l, bases_distinct (map sr_base l) = true -> bases_distinct (map sr_base (List.filter f l)) = true.
  Proof.
    induction l as [|s t IH]; cbn [map bases_distinct List.filter]; intros H; [reflexivity|].
    apply andb_prop in H as [H1 H2]. destruct (f s); cbn [map bases_distinct]; [|exact (IH H2)].
    rewrite (IH H2), Bool.andb_true_r.
    destruct (existsb (Pos.eqb (sr_base s)) (map sr_base (List.filter f t))) eqn:EX; [|reflexivity].
    apply existsb_exists in EX as [b [Hb Hbb]]. apply in_map_iff in Hb as [s' [<- Hs']]. apply filter_In in Hs' as [Hs' _].
    assert (X : existsb (Pos.eqb (sr_base s)) (map sr_base t) = true).
    { apply existsb_exists. exists (sr_base s'). split; [apply in_map_iff; exists s'; auto|exact Hbb]. }
    rewrite X in H1. discriminate.
  Qed.

  Lemma fakes_of_load X pc ctx r :
    In r (fakes_of (vs_rgn (load_cstate2 P X pc ctx))) <-> exists t, In t (cs_rgn X) /\ is_fake t = true /\ r = vregion_of t.
  Proof.
    rewrite fakes_of_spec. cbn [load_cstate2 vs_rgn]. split.
    - intros [Hin [cid [fl K]]]. apply load_regions_in in Hin as [[t [Ht ->]]|Hstd].
      + exists t. split; [exact Ht|]. split; [|reflexivity]. unfold is_fake. cbn [vregion_of vr_kind] in K.
        destruct (sr_kind t); cbn in K; try discriminate. reflexivity.
      + exfalso. apply std_regions_cases in Hstd as [[-> _]|[-> _]]; cbn in K; discriminate.
    - intros (t & Ht & Fk & ->). split; [apply (stored_in_loaded X pc ctx); exact Ht|].
      unfold is_fake in Fk. cbn [vregion_of vr_kind]. destruct (sr_kind t) as [cid fl| | |]; try discriminate. exists cid, fl. reflexivity.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma binds_only_trans isv (s0 s1 s2 : pmap lin) :
    binds_only isv s0 s1 -> binds_only isv s1 s2 -> binds_only isv s0 s2.
  Proof. intros B1 B2 k e Hk. destruct (B2 _ _ Hk) as [H|H]; [|right; exact H]. exact (B1 _ _ H). Qed.

  Lemma srgn_below_facts s b :
    srgn_below_b s b = true ->
    (sr_base s < b)%positive /\ (forall x, In x (skind_syms (sr_kind s)) -> (x < b)%positive)
    /\ (forall k w e, In (k, (w, e)) (sr_cells s) -> lin_below e b = true).
  Proof.
    unfold srgn_below_b. intros H. apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
    apply Pos.ltb_lt in H1. rewrite forallb_forall in H2, H4. split; [exact H1|]. split.
    - intros x Hx. apply Pos.ltb_lt. exact (H2 _ Hx).
    - intros k w e Hin. exact (H4 _ Hin).
  Qed.

  Lemma rgn_shadow_of_in : forall l s r, rgn_shadow_of l s = Some r -> In r l /\ vr_kind r = RK_shadow s.
  Proof.
    induction l as [|x t IH]; cbn [rgn_shadow_of]; intros s r H; [discriminate|].
    destruct (vr_kind x) as [c f| |ow|sof|] eqn:K; try (destruct (IH _ _ H); split; [right|]; assumption).
    destruct (Pos.eqb_spec sof s) as [->|]; [injection H as <-; split; [now left|exact K]|]. destruct (IH _ _ H); split; [right|]; assumption.
  Qed.

  Lemma nodup_map_nth {T} (f : T -> sym) (l : list T) i j x y :
    List.NoDup (map f l) -> nth_error l i = Some x -> nth_error l j = Some y -> i <> j -> f x <> f y.
  Proof.
    intros ND Hi Hj NE EQ. apply NE. rewrite List.NoDup_nth_error in ND.
    apply (ND i j); [rewrite length_map; apply nth_error_Some; congruence|].
    rewrite !nth_error_map, Hi, Hj. cbn. congruence.
  Qed.

  Lemma nodup_map_inj {T} (f : T -> sym) (l : list T) x y :
    List.NoDup (map f l) -> In x l -> In y l -> f x = f y -> x = y.
  Proof.
    intros ND Hx Hy EQ. destruct (in_nth_error _ _ Hx) as [i Hi]. destruct (in_nth_error _ _ Hy) as [j Hj].
    destruct (Nat.eq_dec i j) as [->|NE]; [congruence|]. exfalso. exact (nodup_map_nth f l i j x y ND Hi Hj NE EQ).
  Qed.

  (* [comment removed for export] *)
  Lemma RB_BF_same isv A0 sg s b b' c : binds_only isv pm_empty sg -> RB isv A0 sg s b' c -> BF isv sg s b -> b = b'.
  Proof.
    intros BO [(e & G & EV & _)|(G & NI & E0 & C0 & _)] [F|[NI' E1]].
    - rewrite G in F. injection F as ->.
      pose proof (EV (fun _ => 0)) as E0. rewrite eval_lsym in E0.
      pose proof (EV (fun x => if Pos.eqb x b then 1 else 0)) as E1. rewrite eval_lsym, Pos.eqb_refl in E1.
      destruct (Pos.eqb_spec b' b) as [->|]; [reflexivity|lia].
    - destruct (BO _ _ G) as [X|X]; [rewrite pm_get_empty in X; discriminate|congruence].
    - congruence.
    - congruence.
  Qed.

  Lemma ranges_incl_nil l c : ranges_incl l [] c = true -> l = [].
  Proof. destruct l as [|x t]; [reflexivity|]. unfold ranges_incl. cbn. discriminate. Qed.

  (* [comment removed for export] *)
  Lemma load_globs_ok2 X pc ctx : globs_fcells_ok P X = true -> globs_ok2 P (load_cstate2 P X pc ctx).
  Proof.
    unfold globs_fcells_ok, globs_ok2. change (has_asan P) with (asan_mode P). intros H AM a w v Hin.
    rewrite AM in H. cbn [negb orb] in H. rewrite forallb_forall in H.
    change (vs_globs (v1 (load_cstate2 P X pc ctx))) with (cm_of_list (cs_globs (c1 X))) in Hin.
    apply cm_of_list_in in Hin as (e & -> & Hin).
    specialize (H _ Hin). cbn beta iota in H. apply in_cells_sound in H as (f & Hf & F1 & F2). exists f. auto.
  Qed.

  #[using="Type"] Theorem match_state2_sound_cut A X pc ctx sigma nu regs mem :
    params_ok2 SEGS P ->
    gammaP A nu regs mem ->
    cstate2_ok P X = true ->
    match_state2 isv_join2 no_skip false MM_cut pm_empty (load_cstate2 P X pc ctx) A = MOk sigma ->
    gammaP (load_cstate2 P X pc ctx) (vsubst nu sigma) regs mem /\ ext FIRST_FRESH2 nu (vsubst nu sigma)
    /\ (forall a, In a (own_flags (load_cstate2 P X pc ctx) (vsubst nu sigma)) <-> In a (own_flags A nu)).
  Proof.
    intros PO HGm HX HM.
    set (S := load_cstate2 P X pc ctx) in *.
    pose proof HGm as (HV1 & HE2 & HMC2 & HF2 & HDD & HRG & HLV & HB2 & HGL2 & HFLI & HMEM).
    pose proof HV1 as (HEnv & HMCv & HFix & HS & HC & HMo & HVs & HR & HSl & HGl & HN & HBel).
    destruct (cstate2_ok_parts _ _ HX) as (HX1 & WF & HX3). apply andb_prop in HX3 as [GF SD].
    destruct (cstate2_wf_parts _ WF) as (WF1 & J0 & WBW & WRB & WBD & WDD & WLB & WLM & WSK).
    destruct (load_cstate2_v1_facts X pc ctx HX) as (WS & WG & BEL & _).
    (* [comment removed for export] *)
    unfold match_state2 in HM.
    destruct (match_regions isv_join2 false MM_cut S A (pm_empty, [])) as [[sigma1 defer1]|] eqn:MR; [|discriminate].
    destruct (match_state_f isv_join2 no_skip false sigma1 (v1 S) (v1 A)) as [sg|] eqn:M1; [|discriminate].
    rewrite check_defer_f_eq in HM.   (* [comment removed for export] *)
    destruct (check_defer sg defer1) eqn:CD; [|discriminate].
    destruct (match_divdefs sg S A) eqn:MD; [|discriminate].
    destruct (match_live isv_join2 sg (vs_live S) (vs_live A)) eqn:ML; [|discriminate].
    cbn [negb] in HM. injection HM as ->.
    destruct (match_regions_spec_cut _ _ _ _ _ _ MR) as (BD & BO1 & LEN & FF & OF).
    destruct (match_state_f_sound SEGS (p1 P) (p1 P) (ev1 E) (ev1 E) eq_refl eq_refl eq_refl
                isv_join2 no_skip false sigma1 (v1 S) (v1 A) sigma nu regs mem
                M1 HS HC HMo HVs HR HSl HGl HN WS WG) as (SUB & BO & S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8).
    pose proof (binds_only_trans _ _ _ _ BO1 BO) as BOF.
    pose proof (binds_only_ext nu sigma BOF) as EXT.
    pose proof (check_defer_sound _ _ CD) as DEF.
    set (nu' := vsubst nu sigma) in *.
    (* [comment removed for export] *)
    assert (FAKE : forall r, In r (vs_rgn S) -> forall cid fl, vr_kind r = RK_fake cid fl ->
              exists i pr, nth_error (fakes_of (vs_rgn S)) i = Some r /\ nth_error (fakes_of (vs_rgn A)) i = Some pr
                           /\ In pr (vs_rgn A) /\ fake_fact isv_join2 false A sigma defer1 r pr).
    { intros r Hr cid fl K.
      destruct (in_nth_error _ _ (in_fakes_of _ _ _ _ Hr K)) as [i Hi].
      destruct (nth_error_len _ _ _ _ Hi LEN) as [pr Hpr].
      exists i, pr. split; [exact Hi|]. split; [exact Hpr|]. split.
      - apply (proj1 (fakes_of_in _ _ (nth_error_In _ _ Hpr))).
      - eapply fake_fact_mono; [exact SUB|apply incl_refl|]. exact (FF _ _ _ Hi Hpr). }
    assert (RBASE : forall r pr c, vr_disp r = vr_disp pr -> nu' (vr_base r) = nu (vr_base pr) + c -> rbase nu' r = rbase nu pr + c).
    { intros r pr c D B. unfold rbase. rewrite D, B. lia. }
    assert (OWN : own_flags S nu' = own_flags A nu).
    { rewrite !own_flags_fakes. apply map_ext_nth; [exact LEN|].
      intros i x y Hx Hy. pose proof (FF _ _ _ Hx Hy) as FFi. apply (fake_fact_mono _ _ _ _ _ _ defer1 _ _ SUB (incl_refl _)) in FFi.
      destruct FFi as (cid & flS & flP & KS & KP & _ & BFL & _). rewrite KS, KP. exact (BF_eval _ _ _ _ _ BOF BFL). }
    assert (LIVE_EQ : vs_live S = map sr_base (List.filter is_fake (cs_rgn X))).
    { change (vs_live S) with (cs_live X). apply live_matches_eq. exact WLM. }
    assert (LIVE_I : forall x, In x (vs_live S) <-> exists r, In r (vs_rgn S) /\ vr_base r = x /\ match vr_kind r with RK_fake _ _ => True | _ => False end).
    { intros x. rewrite LIVE_EQ. split.
      - intros Hx. apply in_map_iff in Hx as [t [<- Ht]]. apply filter_In in Ht as [Ht Fk].
        exists (vregion_of t). split; [apply (stored_in_loaded X pc ctx); exact Ht|]. split; [reflexivity|].
        unfold is_fake in Fk. cbn [vregion_of vr_kind]. destruct (sr_kind t); try discriminate. exact I.
      - intros (r & Hr & <- & K). destruct (vr_kind r) as [cid fl| | | |] eqn:Kr; try contradiction.
        destruct (proj1 (fakes_of_load X pc ctx r) (in_fakes_of _ _ _ _ Hr Kr)) as (t & Ht & Fk & ->).
        apply in_map_iff. exists t. split; [reflexivity|]. apply filter_In. auto. }
    pose proof (load_bases_nodup X pc ctx WF) as NDB. change (vs_rgn (load_cstate2 P X pc ctx)) with (vs_rgn S) in NDB.
    split; [|split; [exact EXT|intros a; rewrite OWN; tauto]].
    (* [comment removed for export] *)
    split.
    { (* [comment removed for export] *)
      split; [exact HEnv|]. split; [exact HMCv|]. split.
      { eapply gamma_fix_ext; [|exact EXT|exact HFix]. unfold LAST_FIXED, FIRST_FRESH2; lia. }
      split; [exact S1|]. split; [exact S2|]. split; [exact S3|]. split; [exact S4|].
      split; [intros r e Hr He; apply S5; auto|]. split; [exact S6|]. split; [exact S7|]. split; [exact S8|exact BEL]. }
    split; [exact HE2|]. split; [exact HMC2|]. split; [eapply gamma_fix2_ext; [exact EXT|exact HF2]|].
    split; [apply (match_divdefs_sound _ _ _ _ MD HDD)|].
    split.
    2:{ split.
        - (* [comment removed for export] *)
          split; [exact LIVE_I|]. split.
          { rewrite LIVE_EQ. apply NoDup_ListNoDup. apply bases_distinct_nodup. apply bases_distinct_filter. exact WBD. }
          split.
          { intros r1 r2 Hr1 Hr2. destruct (vr_kind r1) as [c1f f1| | | |] eqn:K1; try exact I. destruct (vr_kind r2) as [c2 f2| | | |] eqn:K2; try exact I.
            intros NE. destruct (FAKE _ Hr1 _ _ K1) as (i1 & pr1 & N1 & Q1 & I1 & F1). destruct (FAKE _ Hr2 _ _ K2) as (i2 & pr2 & N2 & Q2 & I2 & F2).
            destruct F1 as (? & ? & flP1 & KS1 & KP1 & B1 & _ & _ & (D1 & _)). destruct F2 as (? & ? & flP2 & KS2 & KP2 & B2 & _ & _ & (D2 & _)).
            rewrite (RBASE r1 pr1 0 D1 ltac:(rewrite Z.add_0_r; exact (BF_eval _ _ _ _ _ BOF B1))).
            rewrite (RBASE r2 pr2 0 D2 ltac:(rewrite Z.add_0_r; exact (BF_eval _ _ _ _ _ BOF B2))).
            rewrite !Z.add_0_r.
            assert (NEI : i1 <> i2) by (intros ->; rewrite N1 in N2; injection N2 as ->; exact (NE eq_refl)).
            pose proof (nodup_map_nth vr_base _ _ _ _ _ (bases_distinct_nodup _ BD) Q1 Q2 NEI) as NEP.
            destruct HLV as (_ & _ & LV3 & _). specialize (LV3 pr1 pr2 I1 I2). rewrite KP1, KP2 in LV3. exact (LV3 NEP). }
          { exact NDB. }
        - split; [|split; [exact (load_globs_ok2 X pc ctx GF)|split; [|intros ma mn mv []]]].
          2:{ intros NZ c p Hc Hp NL NO. apply (HFLI NZ c p Hc Hp NL). rewrite <- OWN. exact NO. }
          (* [comment removed for export] *)
          split; [change (vs_next (v1 S)) with (cs_next (c1 X)); unfold LAST_FIXED2, FIRST_FRESH2 in *; lia|].
          split.
          { intros r Hr. change (vs_next (v1 S)) with (cs_next (c1 X)).
            apply load_regions_in in Hr as [[t [Ht ->]]|Hstd].
            - destruct (WBW _ Ht) as [BLW _]. destruct (srgn_below_facts _ _ BLW) as (Y1 & Y2 & Y3).
              split; [exact Y1|]. split.
              + intros k w e Hin. destruct (vregion_of_cells _ _ _ _ Hin) as [e' [E' Hin']]. injection E' as ->. exact (Y3 _ _ _ Hin').
              + cbn [vregion_of vr_kind]. destruct (sr_kind t) as [cid fl| | |] eqn:K; cbn [rkind_of]; try exact I.
                apply Y2. rewrite ?K. cbn. now left.
            - apply std_regions_cases in Hstd as [[-> _]|[-> _]]; cbn; (split; [unfold DATA8, FSB, FIRST_FRESH2 in *; lia|]); split; try exact I; intros ? ? ? [].
          }
          split; [intros x Hx; change (vs_next (v1 S)) with (cs_next (c1 X)); exact (WLB _ Hx)|].
          split; [|intros ma mn mv []].
          intros q x m Hq. change (vs_next (v1 S)) with (cs_next (c1 X)). change (vs_divdef S) with (pm_of_list (cs_divdef X)) in Hq.
          apply pm_of_list_get_in in Hq. destruct (WDD _ _ _ Hq) as (Q1 & Q2 & _). auto. }
    (* [comment removed for export] *)
    intros r Hr. pose proof Hr as HrS.
    pose proof (load_rgn_wf X pc ctx r HX Hr) as RWF.
    assert (NOTJ : forall q, (q <= LAST_FIXED2)%positive -> pm_get q sigma = None).
    { intros q Hq. destruct (pm_get q sigma) as [e|] eqn:G; [|reflexivity]. destruct (BOF _ _ G) as [Z0|Z0]; [rewrite pm_get_empty in Z0; discriminate|].
      unfold isv_join2 in Z0. apply Pos.leb_le in Z0. unfold LAST_FIXED2, FIRST_FRESH2 in *. lia. }
    (* [comment removed for export] *)
    assert (GEN : forall pr c exact,
              rc_fact false exact A r pr c defer1 ->
              is_shadow r = is_shadow pr ->
              (is_data_shadow pr = false \/ is_data_shadow r = true) ->
              nu' (vr_base r) = nu (vr_base pr) + c ->
              In pr (vs_rgn A) ->
              0 <= rbase nu' r + vr_lo r /\ rbase nu' r + vr_hi r <= 2 ^ 64 /\ vr_lo r <= vr_hi r
              /\ (is_data_shadow r = true -> vr_cells r = [] /\ vr_w r = [] /\ vr_nul r = [])
              /\ region_cells_ok SEGS nu' mem r /\ region_perm_ok SEGS P E nu' mem r /\ region_nul_ok SEGS nu' mem r).
    { intros pr c exact RC SH DS NB Hpr.
      apply (region_transfer nu sigma defer1 A mem r pr c exact DEF RC RWF SH DS); [|exact (HRG _ Hpr)].
      apply RBASE; [exact (proj1 RC)|exact NB]. }
    assert (FIN : forall pr c exact,
              rc_fact false exact A r pr c defer1 -> is_shadow r = is_shadow pr -> (is_data_shadow pr = false \/ is_data_shadow r = true) ->
              nu' (vr_base r) = nu (vr_base pr) + c -> In pr (vs_rgn A) ->
              kind_ok SEGS P E nu' S mem r -> region_ok SEGS P E nu' S mem r).
    { intros pr c exact RC SH DS NB Hpr KO. destruct (GEN pr c exact RC SH DS NB Hpr) as (G1 & G2 & G3 & G4 & G5 & G6 & G7).
      split; [exact G1|]. split; [exact G2|]. split; [exact G3|]. split; [exact G4|]. split; [exact G5|]. split; [exact G6|]. split; [exact G7|exact KO]. }
    apply load_regions_in in Hr as [[t [Ht Er]]|Hstd].
    - (* [comment removed for export] *)
      pose proof (WSK _ Ht) as SK. unfold skind_struct_ok in SK.
      pose proof (OF r ltac:(rewrite Er; apply (stored_in_loaded X pc ctx); exact Ht)) as OFr.
      apply (other_fact_mono _ _ _ _ _ _ _ defer1 _ SUB BOF (incl_refl _)) in OFr. unfold other_fact in OFr.
      assert (KR : vr_kind r = rkind_of (sr_kind t)) by (rewrite Er; reflexivity).
      destruct (sr_kind t) as [cid fl| |owner|of_] eqn:KT; cbn [rkind_of] in KR; rewrite KR in OFr.
      + (* [comment removed for export] *)
        destruct (FAKE _ HrS _ _ KR) as (i & pr & Ni & Mi & Hpr & FFr).
        destruct FFr as (cid' & flS & flP & KS & KP & BB & BFL & B8 & RC).
        rewrite KR in KS. injection KS as <- <-.
        assert (NB : nu' (vr_base r) = nu (vr_base pr) + 0) by (rewrite Z.add_0_r; exact (BF_eval _ _ _ _ _ BOF BB)).
        apply (FIN pr 0 true RC ltac:(unfold is_shadow; rewrite KR, KP; reflexivity) ltac:(left; unfold is_data_shadow; rewrite KP; reflexivity) NB Hpr).
        pose proof (HRG _ Hpr) as (_ & _ & _ & _ & _ & _ & _ & KOp). unfold kind_ok in KOp. rewrite KP in KOp.
        destruct KOp as (F1 & F2 & F3 & F4 & F5 & pos & P1 & P2 & P3 & P4 & P5 & P6).
        destruct RC as (ED & EX & _). destruct (EX eq_refl) as (_ & ELO & EHI).
        unfold kind_ok. rewrite KR. split; [exact F1|]. split; [exact F2|]. split; [rewrite ELO; exact F3|]. split; [rewrite EHI; exact F4|]. split.
        { apply andb_prop in SK as [_ SK6]. apply Pos.leb_le in SK6. rewrite Er. cbn [vregion_of vr_base]. unfold LAST_FIXED2, FIRST_FRESH2 in *. lia. }
        exists pos. split; [exact P1|]. split; [rewrite (RBASE r pr 0 ED NB), Z.add_0_r; exact P2|].
        replace (nu' fl) with (nu flP) by (symmetry; exact (BF_eval _ _ _ _ _ BOF BFL)). split; [exact P3|]. split; [exact P4|]. split; [exact P5|].
        apply (proj2 (LIVE_I (vr_base r))). exists r. split; [exact HrS|]. split; [reflexivity|]. rewrite KR. exact I.
      + (* [comment removed for export] *)
        destruct OFr as (b' & c & pr & RBr & Gpr & Kpr & RC).
        destruct (rgn_get_in _ _ _ Gpr) as [Hpr Bpr].
        assert (BLE : (vr_base r <= LAST_FIXED2)%positive).
        { apply andb_prop in SK as [SK _]. apply andb_prop in SK as [SK _]. apply andb_prop in SK as [SKa SKb]. apply Pos.leb_le in SKb. rewrite Er. cbn [vregion_of vr_base]. unfold LAST_FIXED2. lia. }
        assert (CB : c = 0 /\ b' = vr_base r).
        { destruct RBr as [(e & G & _ & _)|(G & _ & E0 & C0 & _)]; [|auto]. rewrite (NOTJ _ BLE) in G. discriminate. }
        destruct CB as [-> ->].
        assert (Kpr' : vr_kind pr = RK_arg) by (destruct Kpr as [K|[K _]]; [exact K|discriminate]).
        assert (NB : nu' (vr_base r) = nu (vr_base pr) + 0).
        { rewrite Bpr, Z.add_0_r. unfold nu', vsubst. rewrite (NOTJ _ BLE). reflexivity. }
        apply (FIN pr 0 false RC ltac:(unfold is_shadow; rewrite KR, Kpr'; reflexivity) ltac:(left; unfold is_data_shadow; rewrite Kpr'; reflexivity) NB Hpr).
        pose proof (HRG _ Hpr) as (_ & _ & _ & _ & _ & _ & _ & KOp). unfold kind_ok in KOp. rewrite Kpr' in KOp.
        destruct KOp as (F1 & (cidL & posL & L1 & L2 & L3) & (i & I1 & I2 & I3)).
        destruct RC as (ED & _ & LO & HI & WI & _).
        unfold kind_ok. rewrite KR. split; [exact F1|]. split.
        { exists cidL, posL. split; [exact L1|]. rewrite (RBASE r pr 0 ED NB). lia. }
        exists i. split; [exact I1|]. split; [rewrite <- Bpr; exact I2|].
        intros lo hi Hw. unfold ranges_incl in WI. rewrite forallb_forall in WI. specialize (WI _ Hw). cbn [fst snd] in WI.
        destruct (in_ranges_sound _ _ _ WI) as (lo2 & hi2 & Hw2 & Z1 & Z2).
        destruct (I3 _ _ Hw2) as (lo' & hi' & Hw' & Z3 & Z4). exists lo', hi'. split; [exact Hw'|lia].
      + (* [comment removed for export] *)
        destruct OFr as (owner' & b' & pr & BO' & BB & Gpr & Kpr & RC).
        destruct (rgn_get_in _ _ _ Gpr) as [Hpr Bpr].
        assert (NB : nu' (vr_base r) = nu (vr_base pr) + 0) by (rewrite Bpr, Z.add_0_r; exact (BF_eval _ _ _ _ _ BOF BB)).
        apply (FIN pr 0 true RC ltac:(unfold is_shadow; rewrite KR, Kpr; reflexivity) ltac:(left; unfold is_data_shadow; rewrite Kpr; reflexivity) NB Hpr).
        apply andb_prop in SK as [SK SK5]. apply andb_prop in SK as [SK SK4]. apply andb_prop in SK as [SK SK3]. apply andb_prop in SK as [SK1 SK2].
        apply Z.eqb_eq in SK1. apply Z.eqb_eq in SK2. apply Z.eqb_eq in SK3.
        unfold kind_ok. rewrite KR, Er. cbn [vregion_of vr_lo vr_hi vr_disp vr_cells vr_base].
        split; [exact SK1|]. split; [exact SK2|]. split; [exact SK3|]. split; [destruct (sr_cells t); [reflexivity|discriminate]|].
        apply existsb_exists in SK5 as [t' [Ht' Hb]]. apply andb_prop in Hb as [Hb1 Hb2]. apply Pos.eqb_eq in Hb1.
        destruct (sr_kind t') as [cid' fl'| | |] eqn:KT'; try discriminate. apply Pos.eqb_eq in Hb2.
        exists (vregion_of t'), cid', fl'. split; [rewrite <- Hb1; apply stored_rgn_get; [exact WF|exact Ht']|].
        split; [cbn [vregion_of vr_kind]; rewrite KT'; reflexivity|symmetry; exact Hb2].
      + (* [comment removed for export] *)
        destruct OFr as (of' & c0 & pr & CASES & DD & _ & Gpr & (C00 & BB & RC)). subst c0.
        assert (CASES' : (of_ = SP0 \/ of_ = DATA) /\ of' = of_ \/ of_ <> SP0 /\ of_ <> DATA /\ RB isv_join2 A sigma of_ of' 0) by (clear - CASES; tauto).
        clear CASES. rename CASES' into CASES.
        destruct (rgn_shadow_of_in _ _ _ Gpr) as [Hpr Kpr].
        assert (NB : nu' (vr_base r) = nu (vr_base pr) + 0) by (rewrite Z.add_0_r; exact (BF_eval _ _ _ _ _ BOF BB)).
        assert (DSr : is_data_shadow r = Pos.eqb of_ DATA) by (unfold is_data_shadow; rewrite KR; reflexivity).
        assert (DSp : is_data_shadow pr = Pos.eqb of' DATA) by (unfold is_data_shadow; rewrite Kpr; reflexivity).
        apply (FIN pr 0 (negb (Pos.eqb of' SP0)) RC ltac:(unfold is_shadow; rewrite KR, Kpr; reflexivity)
                 ltac:(rewrite DSr, DSp, DD; destruct (Pos.eqb of_ DATA); auto) NB Hpr).
        apply Bool.orb_prop in SK.
        unfold kind_ok. rewrite KR.
        (* [comment removed for export] *)
        unfold shadow_disp_ok in SD. rewrite forallb_forall in SD. specialize (SD _ Ht). rewrite KT in SD. apply andb_prop in SD as [SD1 SD2]. apply Z.eqb_eq in SD1.
        assert (DISP : vr_disp r = vp_shoff P) by (rewrite Er; exact SD1).
        assert (SPX : of_ = SP0 -> sr_base t = SP8 /\ sr_lo t = - (vp_frame (p1 P) / 8) - 8 /\ sr_hi t = 1).
        { intros ->. rewrite Pos.eqb_refl in SD2. cbn [negb orb] in SD2.
          apply andb_prop in SD2 as [SD2 _]. apply andb_prop in SD2 as [SD2 X3]. apply andb_prop in SD2 as [X1 X2].
          apply Pos.eqb_eq in X1. apply Z.eqb_eq in X2. apply Z.eqb_eq in X3. auto. }
        (* [comment removed for export] *)
        assert (NORES : forall t', In t' (cs_rgn X) -> sr_base t' <> SP0 /\ sr_base t' <> DATA /\ sr_base t' <> FSB).
        { intros t' Ht'. destruct (WRB _ Ht') as [R|(o & _ & _ & R)]; [|rewrite R; repeat split; discriminate].
          destruct (reserved_base_false _ R) as (N1 & N2 & _ & _ & N5 & _). auto. }
        assert (ALT : (of_ = SP0 /\ sr_base t = SP8)
                      \/ (of_ <> SP0 /\ of_ <> DATA /\ of_ <> FSB /\
                          exists t' b8, In t' (cs_rgn X) /\ sr_base t' = of_ /\ sr_b8 t' = Some b8 /\ b8 = sr_base t /\
                                        match sr_kind t' with
                                        | SK_fake _ _ => true
                                        | SK_arg => match sr_w t with [] => true | _ => false end
                                        | _ => false end = true)).
        { destruct SK as [SK|SK].
          - apply andb_prop in SK as [SKo SKb]. apply Pos.eqb_eq in SKo. apply Pos.eqb_eq in SKb. left; auto.
          - apply existsb_exists in SK as [t' [Ht' Hb]].
            apply andb_prop in Hb as [Hb E3]. apply andb_prop in Hb as [E1 E2]. apply Pos.eqb_eq in E1.
            destruct (sr_b8 t') as [b8|] eqn:EB; [|discriminate]. apply Pos.eqb_eq in E3.
            right. destruct (NORES _ Ht') as (N1 & N2 & N3). rewrite E1 in N1, N2, N3.
            split; [exact N1|]. split; [exact N2|]. split; [exact N3|]. exists t', b8. auto 10. }
        (* [comment removed for export] *)
        pose proof (HRG _ Hpr) as (_ & _ & _ & _ & _ & _ & _ & KOp). unfold kind_ok in KOp. rewrite Kpr in KOp.
        destruct KOp as (F1 & _ & _ & _ & _ & OWK).
        split; [exact F1|]. split; [exact DISP|].
        split. { intros Eo. destruct (SPX Eo) as (B1 & L1 & H1). rewrite Er. cbn [vregion_of vr_base vr_lo vr_hi]. rewrite B1, L1, H1. split; [reflexivity|(ltac2:(LK.k [@LEN; @CASES; @SPX; @ALT; @OWK; @Eo; @B1]); lia)]. }
        split. { intros ->. exfalso. destruct ALT as [[X0 _]|(_ & X0 & _)]; [discriminate|exact (X0 eq_refl)]. }
        split. { intros ->. destruct ALT as [[X0 _]|(_ & _ & X0 & _)]; [discriminate|exact (X0 eq_refl)]. }
        intros N1 N2 N3. destruct ALT as [[X0 _]|(_ & _ & _ & t' & b8 & Ht' & E1 & EB & E3 & E2)]; [exfalso; exact (N1 X0)|].
        exists (vregion_of t'). split; [rewrite <- E1; apply stored_rgn_get; [exact WF|exact Ht']|].
        split; [cbn [vregion_of vr_b8]; rewrite EB, E3, Er; reflexivity|].
        assert (RBo : RB isv_join2 A sigma of_ of' 0) by (destruct CASES as [[[X0|X0] _]|(_ & _ & X0)]; [exfalso; exact (N1 X0)|exfalso; exact (N2 X0)|exact X0]).
        destruct HLV as (_ & _ & _ & NDA).
        assert (EXT0 : of' <> SP0 -> vr_lo r = vr_lo pr /\ vr_hi r = vr_hi pr).
        { intros NS. destruct RC as (_ & EX & _). destruct (Pos.eqb_spec of' SP0) as [X0|X0]; [exfalso; exact (NS X0)|]. destruct (EX eq_refl) as (_ & ELO & EHI). auto. }
        assert (EDt : forall pr', rc_fact false true A (vregion_of t') pr' 0 defer1 \/ rc_fact false false A (vregion_of t') pr' 0 defer1 -> sr_disp t' = vr_disp pr').
        { intros pr' [RC'|RC']; exact (proj1 RC'). }
        cbn [vregion_of vr_kind].
        destruct (sr_kind t') as [cid' fl'| | |] eqn:KT'; try discriminate E2.
        -- (* [comment removed for export] *)
           assert (KR' : vr_kind (vregion_of t') = RK_fake cid' fl') by (cbn [vregion_of vr_kind]; rewrite KT'; reflexivity).
           destruct (FAKE (vregion_of t') (stored_in_loaded X pc ctx _ Ht') _ _ KR') as (i' & pr' & Ni' & Mi' & Hpr' & FF').
           destruct FF' as (cid2 & flS2 & flP2 & KS2 & KP2 & BB2 & BFL2 & B82 & RC2).
           rewrite KR' in KS2. injection KS2 as <- <-.
           cbn [vregion_of vr_base] in BB2. rewrite E1 in BB2.
           pose proof (RB_BF_same _ _ _ _ _ _ _ BOF RBo BB2) as Eof'.
           pose proof (HRG _ Hpr') as (_ & _ & _ & _ & _ & _ & _ & KOp'). unfold kind_ok in KOp'. rewrite KP2 in KOp'.
           destruct KOp' as (_ & _ & _ & _ & LF & _). rewrite Eof' in LF.
           assert (Q1 : of' <> SP0) by (intros X0; rewrite X0 in LF; unfold LAST_FIXED2, SP0 in LF; (ltac2:(LK.k [@LEN; @CASES; @SPX; @E1; @E3; @OWK; @N1; @N2; @N3; @EXT0; @Eof'; @LF; @X0]); lia)).
           assert (Q2 : of' <> DATA) by (intros X0; rewrite X0 in LF; unfold LAST_FIXED2, DATA in LF; (ltac2:(LK.k [@LEN; @CASES; @SPX; @E1; @E3; @OWK; @N1; @N2; @N3; @EXT0; @Eof'; @LF; @Q1; @X0]); lia)).
           assert (Q3 : of' <> FSB) by (intros X0; rewrite X0 in LF; unfold LAST_FIXED2, FSB in LF; (ltac2:(LK.k [@LEN; @CASES; @SPX; @E1; @E3; @OWK; @N1; @N2; @N3; @EXT0; @Eof'; @LF; @Q1; @Q2; @X0]); lia)).
           destruct (OWK Q1 Q2 Q3) as (roA & GroA & B8A & MK).
           destruct (rgn_get_in _ _ _ GroA) as [HroA BroA].
           assert (roA = pr') as -> by (apply (nodup_map_inj vr_base _ _ _ NDA HroA Hpr'); rewrite BroA, Eof'; reflexivity).
           rewrite KP2 in MK. destruct MK as (MK1 & MK2 & MK3).
           destruct (EXT0 Q1) as [-> ->]. split; [|split; [exact MK2|exact MK3]].
           unfold rbase in *. cbn [vregion_of vr_base vr_disp]. rewrite E1.
           rewrite (EDt pr' (or_introl RC2)), NB, Z.add_0_r, MK1.
           change (nu' of_) with (vsubst nu sigma of_). rewrite (BF_eval _ _ _ _ _ BOF BB2). reflexivity.
        -- (* [comment removed for export] *)
           assert (KR' : vr_kind (vregion_of t') = RK_arg) by (cbn [vregion_of vr_kind]; rewrite KT'; reflexivity).
           pose proof (OF (vregion_of t') (stored_in_loaded X pc ctx _ Ht')) as OF'.
           apply (other_fact_mono _ _ _ _ _ _ _ defer1 _ SUB BOF (incl_refl _)) in OF'. unfold other_fact in OF'. rewrite KR' in OF'.
           destruct OF' as (b2 & c2 & pr' & RBr2 & Gpr2 & Kpr2 & RC2).
           pose proof (WSK _ Ht') as SK'. unfold skind_struct_ok in SK'. rewrite KT' in SK'.
           apply andb_prop in SK' as [SK' _]. apply andb_prop in SK' as [SK' _]. apply andb_prop in SK' as [_ SKb']. apply Pos.leb_le in SKb'.
           assert (BLE' : (of_ <= LAST_FIXED2)%positive) by (rewrite <- E1; unfold LAST_FIXED2; (ltac2:(LK.k [@LEN; @CASES; @SPX; @E1; @E3; @OWK; @N1; @N2; @N3; @EXT0; @SKb']); lia)).
           cbn [vregion_of vr_base] in RBr2. rewrite E1 in RBr2.
           assert (Hb2 : b2 = of_ /\ c2 = 0).
           { destruct RBr2 as [(e & G & _)|(G & _ & E0 & C0 & _)]; [rewrite (NOTJ _ BLE') in G; discriminate|auto]. }
           destruct Hb2 as [-> ->].
           assert (Eof' : of' = of_).
           { destruct RBo as [(e & G & _)|(G & _ & E0 & _)]; [rewrite (NOTJ _ BLE') in G; discriminate|symmetry; exact E0]. }
           subst of'.
           destruct (OWK N1 N2 N3) as (roA & GroA & B8A & MK).
           rewrite Gpr2 in GroA. injection GroA as E4. subst roA.
           assert (Kpr2' : vr_kind pr' = RK_arg) by (destruct Kpr2 as [K|[K _]]; [exact K|discriminate]).
           rewrite Kpr2' in MK. destruct MK as (MK1 & MK2 & cidL & posL & L1 & L2 & L3).
           destruct (EXT0 N1) as [-> ->].
           destruct (rgn_get_in _ _ _ Gpr2) as [_ Bpr2].
           split.
           { unfold rbase in *. cbn [vregion_of vr_base vr_disp]. rewrite E1.
             rewrite (EDt pr' (or_intror RC2)), NB, Z.add_0_r, MK1, Bpr2.
             change (nu' of_) with (vsubst nu sigma of_). unfold vsubst. rewrite (NOTJ _ BLE'). reflexivity. }
           split.
           { destruct RC as (_ & _ & _ & _ & WI & _). rewrite MK2 in WI. exact (ranges_incl_nil _ _ WI). }
           exists cidL, posL. split; [exact L1|]. rewrite NB, Z.add_0_r. split; [exact L2|exact L3].
    - (* [comment removed for export] *)
      pose proof (OF r ltac:(cbn [load_cstate2 vs_rgn]; unfold load_regions; apply in_app_iff; right; exact Hstd)) as OFr.
      apply (other_fact_mono _ _ _ _ _ _ _ defer1 _ SUB BOF (incl_refl _)) in OFr. unfold other_fact in OFr.
      apply std_regions_cases in Hstd as [[Er HAS]|[Er HAS]]; subst r; cbn [SHD FSR vr_kind] in OFr.
      + (* [comment removed for export] *)
        destruct OFr as (of' & c0 & pr & CASES & DD & _ & Gpr & (C00 & BB & RC)). subst c0.
        assert (CASES' : (DATA = SP0 \/ DATA = DATA) /\ of' = DATA \/ DATA <> SP0 /\ DATA <> DATA /\ RB isv_join2 A sigma DATA of' 0) by (clear - CASES; tauto).
        clear CASES. rename CASES' into CASES.
        assert (of' = DATA) as -> by (destruct CASES as [[_ ->]|(_ & ND & _)]; [reflexivity|exfalso; exact (ND eq_refl)]).
        destruct (rgn_shadow_of_in _ _ _ Gpr) as [Hpr Kpr].
        assert (NB : nu' DATA8 = nu (vr_base pr) + 0).
        { rewrite Z.add_0_r. exact (BF_eval _ _ _ _ _ BOF BB). }
        apply (FIN pr 0 (negb (Pos.eqb DATA SP0)) RC ltac:(unfold is_shadow; rewrite Kpr; reflexivity) ltac:(right; reflexivity) NB Hpr).
        pose proof (HRG _ Hpr) as (_ & _ & _ & _ & _ & _ & _ & KOp). unfold kind_ok in KOp. rewrite Kpr in KOp.
        unfold kind_ok. cbn [SHD vr_kind vr_disp vr_base]. split; [exact (proj1 KOp)|]. split; [reflexivity|]. split; [intros X0; discriminate|]. split; [reflexivity|].
        split; [intros X0; discriminate|]. intros _ ND _. exfalso. exact (ND eq_refl).
      + (* [comment removed for export] *)
        destruct OFr as (pr & Gpr & Kpr & RC).
        destruct (rgn_get_in _ _ _ Gpr) as [Hpr Bpr].
        assert (NB : nu' FSB = nu (vr_base pr) + 0).
        { rewrite Bpr, Z.add_0_r. unfold nu', vsubst. rewrite (NOTJ FSB ltac:(unfold FSB, LAST_FIXED2; lia)). reflexivity. }
        apply (FIN pr 0 true RC ltac:(unfold is_shadow; rewrite Kpr; reflexivity) ltac:(left; unfold is_data_shadow; rewrite Kpr; reflexivity) NB Hpr).
        pose proof (HRG _ Hpr) as (_ & _ & _ & _ & _ & _ & _ & KOp). unfold kind_ok in KOp. rewrite Kpr in KOp.
        unfold kind_ok. cbn [FSR vr_kind vr_base vr_disp vr_lo vr_hi]. split; [exact (proj1 KOp)|]. repeat split; reflexivity.
  Qed.
End Sound2.
