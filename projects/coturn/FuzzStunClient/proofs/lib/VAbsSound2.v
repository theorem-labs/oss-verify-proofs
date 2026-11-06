(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Bool Lia.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import VLinalg VState VLogic VAbs VAbsSound.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Unset Lia Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition wval (nu : val) (v : absval) (u : Z) : Prop :=
  0 <= u < 2 ^ 64 /\ match v with Some e => u = zwrap 64 (eval nu e) | None => True end.

(* [comment removed for export] *)
Definition rdg (signed : bool) (u : Z) : Z := if signed then zswrap 64 u else u.

Lemma wval_some nu e u : wval nu (Some e) u -> u = zwrap 64 (eval nu e).
Proof. intros [_ H]; exact H. Qed.

Lemma wval_of_eval nu e : wval nu (Some e) (zwrap 64 (eval nu e)).
Proof. split; [apply zwrap_range; lia|reflexivity]. Qed.

Lemma wval_none nu u : 0 <= u < 2 ^ 64 -> wval nu None u.
Proof. intros; split; auto. Qed.

Lemma wval_ext nu nu' b v u :
  ext b nu nu' -> match v with Some e => lin_below e b = true | None => True end ->
  wval nu v u -> wval nu' v u.
Proof.
  intros He Hb [Hu Hv]. split; auto. destruct v as [e|]; auto.
  rewrite (eval_ext_below b nu nu' e); auto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma zone_sound lo hi signed x rlo rhi sh :
  zone (Some lo) (Some hi) signed = RZone rlo rhi sh ->
  lo <= x <= hi ->
  rdg signed (zwrap 64 x) = x + sh /\ rlo <= x + sh <= rhi.
Proof.
  unfold zone, rdg, TWO63, TWO64. intros H Hx.
  destruct signed.
  - destruct (Z.leb_spec (- 2 ^ 63) lo); destruct (Z.ltb_spec hi (2 ^ 63)); cbn [andb] in H.
    + inversion H; subst; clear H. rewrite zswrap_zwrap_id by (simpl; lia). lia.
    + destruct (Z.leb_spec (2 ^ 63) lo); destruct (Z.ltb_spec hi (2 ^ 64)); cbn [andb] in H; try discriminate.
      inversion H; subst; clear H. split; [|lia].
      rewrite zswrap_zwrap by lia.
      rewrite <- (zswrap_congr 64 (x - 2 ^ 64) x) by (try lia; exists (-1); lia).
      rewrite zswrap_id; simpl; lia.
    + destruct (Z.leb_spec (2 ^ 63) lo); destruct (Z.ltb_spec hi (2 ^ 64)); cbn [andb] in H; try discriminate.
      inversion H; subst; clear H. lia.
    + destruct (Z.leb_spec (2 ^ 63) lo); destruct (Z.ltb_spec hi (2 ^ 64)); cbn [andb] in H; try discriminate.
      inversion H; subst; clear H. split; [|lia].
      rewrite zswrap_zwrap by lia.
      rewrite <- (zswrap_congr 64 (x - 2 ^ 64) x) by (try lia; exists (-1); lia).
      rewrite zswrap_id; simpl; lia.
  - destruct (Z.leb_spec 0 lo); destruct (Z.ltb_spec hi (2 ^ 64)); cbn [andb] in H.
    + inversion H; subst; clear H. rewrite zwrap_id by lia. lia.
    + destruct (Z.ltb_spec (- 2 ^ 64) lo); destruct (Z.ltb_spec hi 0); cbn [andb] in H; try discriminate.
      inversion H; subst; lia.
    + destruct (Z.ltb_spec (- 2 ^ 64) lo); destruct (Z.ltb_spec hi 0); cbn [andb] in H; try discriminate.
      inversion H; subst; clear H. split; [|lia].
      rewrite <- (zwrap_plus_k 64 x 1) by lia. rewrite zwrap_id by lia. lia.
    + destruct (Z.ltb_spec (- 2 ^ 64) lo); destruct (Z.ltb_spec hi 0); cbn [andb] in H; try discriminate.
      inversion H; subst; clear H. split; [|lia].
      rewrite <- (zwrap_plus_k 64 x 1) by lia. rewrite zwrap_id by lia. lia.
Qed.

Lemma zone_none_l hi s : zone None hi s = RNone.
Proof. reflexivity. Qed.
Lemma zone_none_r lo s : zone lo None s = RNone.
Proof. destruct lo; reflexivity. Qed.

Lemma zone_not_bot lo hi s : zone lo hi s <> RBot.
Proof.
  unfold zone. destruct lo, hi; try discriminate.
  destruct s; repeat (destruct (_ && _)); discriminate.
Qed.

Lemma readings_sound A nu v u signed rlo rhi sh :
  lgamma A nu -> wval nu v u ->
  readings A v signed = RZone rlo rhi sh ->
  exists e, v = Some e /\ rdg signed u = eval nu e + sh /\ rlo <= eval nu e + sh <= rhi.
Proof.
  intros HG Hw. unfold readings. destruct v as [e|]; [|discriminate].
  pose proof (wval_some _ _ _ Hw) as Hu. subst u.
  set (first := if lin_is_const e then RNone else let '(lo, hi) := lin_range (sbox (vs_store A)) e in zone lo hi signed).
  assert (Hfirst : forall rlo rhi sh, first = RZone rlo rhi sh ->
             rdg signed (zwrap 64 (eval nu e)) = eval nu e + sh /\ rlo <= eval nu e + sh <= rhi).
  { unfold first. destruct (lin_is_const e); [discriminate|].
    pose proof (sat_range nu (vs_store A) e (lg_sat _ _ HG)) as Hr.
    destruct (lin_range (sbox (vs_store A)) e) as [[lo|] [hi|]]; try (rewrite ?zone_none_l, ?zone_none_r; discriminate).
    intros rlo0 rhi0 sh0 Hz. destruct Hr as [H1 H2]; simpl in *. eapply zone_sound; eauto. }
  destruct first eqn:Ef.
  - intros H. destruct (negb (lin_is_const e) && itv_empty (bnd A e)); [discriminate|].
    pose proof (bnd_sound A nu e HG) as Hb. destruct (bnd A e) as [[lo|] [hi|]]; simpl in H;
      try (rewrite ?zone_none_l, ?zone_none_r in H; discriminate).
    destruct Hb as [H1 H2]; simpl in *. exists e. split; auto. eapply zone_sound; eauto.
  - intros H. destruct (negb (lin_is_const e) && itv_empty (bnd A e)); [discriminate|].
    pose proof (bnd_sound A nu e HG) as Hb. destruct (bnd A e) as [[lo|] [hi|]]; simpl in H;
      try (rewrite ?zone_none_l, ?zone_none_r in H; discriminate).
    destruct Hb as [H1 H2]; simpl in *. exists e. split; auto. eapply zone_sound; eauto.
  - intros H. exists e. split; auto.
Qed.

Lemma readings_not_bot A nu v signed : lgamma A nu -> readings A v signed = RBot -> False.
Proof.
  intros HG. unfold readings. destruct v as [e|]; [|discriminate].
  destruct (if lin_is_const e then RNone else _) eqn:Ef.
  - destruct (negb (lin_is_const e) && itv_empty (bnd A e)) eqn:E.
    + apply andb_prop in E as [E1 E2]. destruct (lin_is_const e) eqn:Ec; [discriminate|].
      unfold bnd in E2. rewrite Ec in E2. rewrite (lp_bounds_not_empty' A nu e HG) in E2. discriminate.
    + intros X. exact (zone_not_bot _ _ _ X).
  - destruct (lin_is_const e); [discriminate|].
    destruct (lin_range _ _) as [lo hi] in Ef. exfalso. exact (zone_not_bot _ _ _ Ef).
  - discriminate.
Qed.

Lemma mixed_sound A nu v oh lo hi : lgamma A nu -> mixed A v oh = Some (lo, hi) ->
  exists e, v = Some e /\ lo <= eval nu e <= hi /\ lo < 0 /\ 0 <= hi < 2 ^ 64 /\ oh < lo + 2 ^ 64.
Proof.
  intros HG. unfold mixed, TWO64. destruct v as [e|]; [|discriminate].
  destruct (negb (lin_is_const e) && itv_empty (bnd A e)); [discriminate|].
  pose proof (bnd_sound A nu e HG) as Hb.
  destruct (bnd A e) as [[l|] [h|]]; try discriminate. destruct Hb as [H1 H2]; cbn [fst snd lo_le hi_ge] in H1, H2.
  destruct (Z.ltb_spec l 0); destruct (Z.leb_spec 0 h); destruct (Z.ltb_spec h (2 ^ 64)); destruct (Z.ltb_spec oh (l + 2 ^ 64));
    cbn [andb]; try discriminate.
  intros X; inversion X; subst; clear X. exists e. repeat split; auto; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma cmp_lt_sound A nu a b ua ub signed r :
  lgamma A nu -> wval nu a ua -> wval nu b ub ->
  cmp_lt A a b signed = Some r -> r = Z.ltb (rdg signed ua) (rdg signed ub).
Proof.
  intros HG Ha Hb. unfold cmp_lt.
  destruct (readings A a signed) as [| |alo ahi ash] eqn:Ea;
  destruct (readings A b signed) as [| |blo bhi bsh] eqn:Eb; try discriminate;
  try (intros; exfalso; eapply readings_not_bot; eauto; fail).
  destruct (readings_sound A nu a ua signed _ _ _ HG Ha Ea) as [ea (->&Ra&Ba)].
  destruct (readings_sound A nu b ub signed _ _ _ HG Hb Eb) as [eb (->&Rb&Bb)].
  destruct (Z.eqb_spec ash bsh).
  - subst. set (d := lsub ea eb).
    assert (Ed : eval nu d = eval nu ea - eval nu eb) by (unfold d; apply eval_lsub).
    destruct (lin_is_const d) eqn:Ec.
    + intros X; inversion X; subst; clear X. rewrite (eval_is_const nu d Ec) in Ed. rewrite Ra, Rb.
      unfold d in *. cbn [lc lsub] in *.
      destruct (Z.leb_spec (lc ea - lc eb) (-1)); destruct (Z.ltb_spec (eval nu ea + bsh) (eval nu eb + bsh)); auto; lia.
    + destruct (qle A d (-1)) eqn:E1.
      * intros X; inversion X; subst; clear X. apply (qle_sound A nu) in E1; auto. rewrite Ra, Rb.
        symmetry. apply Z.ltb_lt. lia.
      * destruct (qge A d 0) eqn:E2; [|discriminate].
        intros X; inversion X; subst; clear X. apply (qge_sound A nu) in E2; auto. rewrite Ra, Rb.
        symmetry. apply Z.ltb_ge. lia.
  - destruct (Z.ltb_spec ahi blo).
    + intros X; inversion X; subst; clear X. rewrite Ra, Rb. symmetry. apply Z.ltb_lt. lia.
    + destruct (Z.leb_spec bhi alo); [|discriminate].
      intros X; inversion X; subst; clear X. rewrite Ra, Rb. symmetry. apply Z.ltb_ge. lia.
Qed.

Lemma eqb_iff_prop (r : bool) (P : Prop) (b : bool) :
  (b = true <-> P) -> (r = true <-> P) -> r = b.
Proof.
  intros H1 H2. destruct r, b; auto.
  - symmetry. apply H1. apply H2. reflexivity.
  - apply H2. apply H1. reflexivity.
Qed.

Lemma eval_eq_sound A nu a b ua ub r :
  lgamma A nu -> wval nu a ua -> wval nu b ub ->
  eval_eq A a b = Some r -> r = Z.eqb ua ub.
Proof.
  intros HG Ha Hb. unfold eval_eq, TWO64, M64.
  destruct a as [ea|]; [|discriminate]. destruct b as [eb|]; [|discriminate].
  rewrite (wval_some _ _ _ Ha), (wval_some _ _ _ Hb).
  set (d := lsub ea eb).
  assert (Ed : eval nu d = eval nu ea - eval nu eb) by (unfold d; apply eval_lsub).
  assert (Hw : Z.eqb (zwrap 64 (eval nu ea)) (zwrap 64 (eval nu eb)) = true <-> (2 ^ 64 | eval nu d)).
  { rewrite Ed, Z.eqb_eq. apply zwrap_eq_iff. lia. }
  intros H. apply (eqb_iff_prop r (2 ^ 64 | eval nu d)); auto. clear Hw.
  destruct (lin_is_const d) eqn:Ec.
  - inversion H; subst; clear H. rewrite (eval_is_const nu d Ec). rewrite Z.eqb_eq.
    apply Z.mod_divide. lia.
  - destruct (qwithin A d 0 0) eqn:E0.
    + inversion H; subst; clear H. apply (qwithin_sound A nu) in E0; auto. split; auto. intros _.
      exists 0. lia.
    + rewrite !if_andb, if_orb in H.
      destruct ((qge A d 1 && qle A d (2 ^ 64 - 1)) || (qle A d (-1) && qge A d (- (2 ^ 64 - 1)))) eqn:E1.
      * inversion H; subst; clear H. split; [discriminate|]. intros [q Hq]. exfalso.
        apply orb_prop in E1. destruct E1 as [E1|E1]; apply andb_prop in E1 as [X1 X2].
        -- apply (qge_sound A nu) in X1; auto. apply (qle_sound A nu) in X2; auto. nia.
        -- apply (qle_sound A nu) in X1; auto. apply (qge_sound A nu) in X2; auto. nia.
      * pose proof (lin_cong_sound nu (scong (vs_store A)) d (sat_cong _ _ (lg_sat _ _ HG))) as HC.
        destruct (lin_cong (scong (vs_store A)) d) as [m rr]. destruct HC as (Hdiv&Hm&Hr).
        rewrite !if_andb in H.
        destruct (Z.ltb 1 m && negb (Z.eqb (rr mod m) 0) && qwithin A d (- (2 ^ 64 - 1)) (2 ^ 64 - 1)) eqn:E2; [|discriminate].
        inversion H; subst; clear H. split; [discriminate|]. intros [q Hq]. exfalso.
        apply andb_prop in E2 as [E2 X3]. apply andb_prop in E2 as [X1 X2].
        apply Z.ltb_lt in X1. apply (qwithin_sound A nu) in X3; auto.
        assert (q = 0) by (destruct (Z.lt_trichotomy q 0) as [Hl|[He|Hg]]; [exfalso; nia|auto|exfalso; nia]).
        subst q. assert (E00 : eval nu d = 0) by lia.
        rewrite E00 in Hdiv. destruct Hdiv as [q' Hq']. 
        specialize (Hr ltac:(lia)).
        assert (Hrr : rr mod m = 0).
        { rewrite Z.mod_small by lia.
          destruct (Z.lt_trichotomy q' 0) as [Hl|[He|Hg]]; [exfalso; nia|subst; lia|exfalso; nia]. }
        rewrite Hrr in X2. discriminate.
Qed.

(* [comment removed for export] *)
Definition wcond (k : ckind) (ua ub : Z) : bool :=
  match k with
  | CK_eq => Z.eqb ua ub
  | CK_lt => Z.ltb (zswrap 64 ua) (zswrap 64 ub)
  | CK_ltu => Z.ltb ua ub
  end.

Lemma eval_cond_sound A nu c a b ua ub r :
  lgamma A nu -> wval nu a ua -> wval nu b ub ->
  eval_cond A c a b = Some r -> r = xorb (wcond (fst c) ua ub) (snd c).
Proof.
  intros HG Ha Hb. unfold eval_cond. destruct c as [k neg]. simpl.
  destruct k.
  - destruct (cmp_lt A a b true) eqn:E; [|discriminate]. intros X; inversion X; subst; clear X.
    rewrite (cmp_lt_sound A nu a b ua ub true _ HG Ha Hb E). reflexivity.
  - destruct (cmp_lt A a b false) eqn:E; [|discriminate]. intros X; inversion X; subst; clear X.
    rewrite (cmp_lt_sound A nu a b ua ub false _ HG Ha Hb E). reflexivity.
  - destruct (eval_eq A a b) eqn:E; [|discriminate]. intros X; inversion X; subst; clear X.
    rewrite (eval_eq_sound A nu a b ua ub _ HG Ha Hb E). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma wcond_cond_holds k nu x y :
  wcond k (zwrap 64 (eval nu x)) (zwrap 64 (eval nu y)) = cond_holds k (eval nu x) (eval nu y).
Proof.
  destruct k; simpl; auto. rewrite !zswrap_zwrap by lia. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition vbelow (v : absval) (b : positive) : Prop :=
  match v with Some e => lin_below e b = true | None => True end.

Lemma refine0_sound A nu c a b ua ub :
  lgamma A nu -> wval nu a ua -> wval nu b ub ->
  vbelow a (vs_next A) -> vbelow b (vs_next A) ->
  xorb (wcond (fst c) ua ub) (snd c) = true ->
  fst (refine0 A c a b) = true /\ lgamma (snd (refine0 A c a b)) nu /\ aext A (snd (refine0 A c a b)) nu nu
  /\ vs_next (snd (refine0 A c a b)) = vs_next A.
Proof.
  intros HG Ha Hb Bea Beb Hc.
  assert (TRIV : fst (true, A) = true /\ lgamma (snd (true, A)) nu /\ aext A (snd (true, A)) nu nu /\ vs_next (snd (true, A)) = vs_next A).
  { simpl. split; [reflexivity|]. split; [exact HG|]. split; [apply aext_refl|reflexivity]. }
  unfold refine0. destruct a as [ea|]; [|exact TRIV]. destruct b as [eb|]; [|exact TRIV].
  simpl in Bea, Beb.
  pose proof (wval_some _ _ _ Ha) as Ua. pose proof (wval_some _ _ _ Hb) as Ub.
  destruct c as [k neg]. simpl in Hc.
  assert (ORD : forall signed,
    Z.ltb (rdg signed ua) (rdg signed ub) = negb neg ->
    let r := (let ra := readings A (Some ea) signed in
          let rb := readings A (Some eb) signed in
          match ra, rb with
          | RZone _ _ ash, RZone _ _ bsh =>
              let d := lsub (laddc ea ash) (laddc eb bsh) in
              if negb neg then aassume A (laddc d 1)
              else aassume A (lneg d)
          | RBot, (RBot | RZone _ _ _) | RZone _ _ _, RBot => (false, A)
          | RNone, RZone blo bhi bsh =>
              if signed then (true, A) else
              match mixed A (Some ea) bhi with
              | Some (malo, mahi) =>
                  if Z.eqb bsh 0 then
                    (if negb neg then
                       aassume2 A (lneg ea) (laddc (lsub ea eb) 1)
                     else (true, A))
                  else (true, A)
              | None => (true, A)
              end
          | RZone alo ahi ash, RNone =>
              if signed then (true, A) else
              match mixed A (Some eb) ahi with
              | Some (mblo, mbhi) =>
                  if Z.eqb ash 0 then
                    (if neg then
                       aassume2 A (lneg eb) (lsub eb ea)
                     else (true, A))
                  else (true, A)
              | None => (true, A)
              end
          | _, _ => (true, A)
          end) in
    fst r = true /\ lgamma (snd r) nu /\ aext A (snd r) nu nu /\ vs_next (snd r) = vs_next A).
  { intros signed Hlt. cbn zeta.
    destruct (readings A (Some ea) signed) as [| |alo ahi ash] eqn:Ea;
    destruct (readings A (Some eb) signed) as [| |blo bhi bsh] eqn:Eb;
    try exact TRIV; try (exfalso; eapply readings_not_bot; eauto; fail).
    - (* [comment removed for export] *)
      destruct signed; [exact TRIV|].
      destruct (mixed A (Some ea) bhi) as [[malo mahi]|] eqn:Em; [|exact TRIV].
      destruct (Z.eqb_spec bsh 0); [|exact TRIV].
      destruct neg; [exact TRIV|]. cbn [negb].
      destruct (mixed_sound A nu (Some ea) bhi malo mahi HG Em) as [ea' (Eea&Hxa&Hlo&Hhi&Hoh)]. inversion Eea; subst ea'; clear Eea.
      destruct (readings_sound A nu (Some eb) ub false _ _ _ HG Hb Eb) as [eb' (Eeb&Rb&Bb)]. inversion Eeb; subst eb'; clear Eeb.
      unfold rdg in Hlt, Rb. simpl in Hlt. apply Z.ltb_lt in Hlt.
      rewrite Ua in Hlt. pose proof (proj1 Hb) as Rub. pose proof (proj1 Ha) as Rua.
      assert (Hxa0 : 0 <= eval nu ea).
      { destruct (Z_lt_le_dec (eval nu ea) 0); auto. exfalso.
        rewrite <- (zwrap_plus_k 64 (eval nu ea) 1) in Hlt by lia. rewrite zwrap_id in Hlt by lia. lia. }
      rewrite zwrap_id in Hlt by lia.
      pose proof (aassume2_sound A nu (lneg ea) (laddc (lsub ea eb) 1) HG
                    ltac:(rewrite eval_lneg; lia) ltac:(rewrite eval_laddc, eval_lsub; lia)
                    ltac:(now apply lin_below_lneg) ltac:(apply lin_below_laddc; now apply lin_below_lsub)) as (F&L&X).
      split; [exact F|]. split; [exact L|]. split; [exact X|apply aassume2_next].
    - (* [comment removed for export] *)
      destruct signed; [exact TRIV|].
      destruct (mixed A (Some eb) ahi) as [[mblo mbhi]|] eqn:Em; [|exact TRIV].
      destruct (Z.eqb_spec ash 0); [|exact TRIV].
      destruct neg; [|exact TRIV].
      destruct (mixed_sound A nu (Some eb) ahi mblo mbhi HG Em) as [eb' (Eeb&Hxb&Hlo&Hhi&Hoh)]. inversion Eeb; subst eb'; clear Eeb.
      destruct (readings_sound A nu (Some ea) ua false _ _ _ HG Ha Ea) as [ea' (Eea&Ra&Ba)]. inversion Eea; subst ea'; clear Eea.
      unfold rdg in Hlt, Ra. simpl in Hlt. apply Z.ltb_ge in Hlt.
      rewrite Ub in Hlt. pose proof (proj1 Hb) as Rub. pose proof (proj1 Ha) as Rua.
      assert (Hxb0 : 0 <= eval nu eb).
      { destruct (Z_lt_le_dec (eval nu eb) 0); auto. exfalso.
        rewrite <- (zwrap_plus_k 64 (eval nu eb) 1) in Hlt by lia. rewrite zwrap_id in Hlt by lia. lia. }
      rewrite zwrap_id in Hlt by lia.
      pose proof (aassume2_sound A nu (lneg eb) (lsub eb ea) HG
                    ltac:(rewrite eval_lneg; lia) ltac:(rewrite eval_lsub; lia)
                    ltac:(now apply lin_below_lneg) ltac:(now apply lin_below_lsub)) as (F&L&X).
      split; [exact F|]. split; [exact L|]. split; [exact X|apply aassume2_next].
    - (* [comment removed for export] *)
      destruct (readings_sound A nu (Some ea) ua signed _ _ _ HG Ha Ea) as [ea' (Eea&Ra&Ba)]. inversion Eea; subst ea'; clear Eea.
      destruct (readings_sound A nu (Some eb) ub signed _ _ _ HG Hb Eb) as [eb' (Eeb&Rb&Bb)]. inversion Eeb; subst eb'; clear Eeb.
      rewrite Ra, Rb in Hlt.
      set (d := lsub (laddc ea ash) (laddc eb bsh)).
      assert (Ed : eval nu d = (eval nu ea + ash) - (eval nu eb + bsh)) by (unfold d; rewrite eval_lsub, !eval_laddc; lia).
      assert (Bd : lin_below d (vs_next A) = true) by (unfold d; apply lin_below_lsub; now apply lin_below_laddc).
      destruct neg; cbn [negb] in *.
      + apply Z.ltb_ge in Hlt.
        pose proof (aassume_sound A nu (lneg d) HG ltac:(rewrite eval_lneg; lia) ltac:(now apply lin_below_lneg)) as (F&L&X).
        split; [exact F|]. split; [exact L|]. split; [exact X|apply aassume_next].
      + apply Z.ltb_lt in Hlt.
        pose proof (aassume_sound A nu (laddc d 1) HG ltac:(rewrite eval_laddc; lia) ltac:(now apply lin_below_laddc)) as (F&L&X).
        split; [exact F|]. split; [exact L|]. split; [exact X|apply aassume_next]. }
  assert (XB : forall x y : bool, xorb x y = true -> x = negb y) by (intros [|] [|]; simpl; congruence).
  destruct k.
  - (* [comment removed for export] *) apply (ORD true). apply XB. exact Hc.
  - apply (ORD false). apply XB. exact Hc.
  - (* [comment removed for export] *)
    set (d := lsub ea eb).
    assert (Ed : eval nu d = eval nu ea - eval nu eb) by (unfold d; apply eval_lsub).
    assert (Bd : lin_below d (vs_next A) = true) by (unfold d; now apply lin_below_lsub).
    simpl in Hc. rewrite Ua, Ub in Hc.
    assert (Hiff : (zwrap 64 (eval nu ea) =? zwrap 64 (eval nu eb)) = true <-> (2 ^ 64 | eval nu d)).
    { rewrite Ed, Z.eqb_eq. apply zwrap_eq_iff. lia. }
    destruct (lin_is_const d) eqn:Ec.
    + rewrite (eval_is_const nu d Ec) in Hiff.
      assert (E2 : (lc d mod TWO64 =? 0) = (zwrap 64 (eval nu ea) =? zwrap 64 (eval nu eb))).
      { apply (eqb_iff_prop _ (2 ^ 64 | lc d)); [exact Hiff|]. unfold TWO64. rewrite Z.eqb_eq.
        split; intros; apply Z.mod_divide; auto; lia. }
      rewrite E2, Hc. exact TRIV.
    + pose proof (bnd_sound A nu d HG) as Hbd.
      destruct (itv_empty (bnd A d)) eqn:Ee; [exfalso; exact (itv_empty_sound _ _ Ee Hbd)|].
      destruct (bnd A d) as [[lo|] [hi|]]; try exact TRIV. destruct Hbd as [Hlo Hhi]; simpl in Hlo, Hhi.
      destruct (Z.leb lo (- TWO64) || Z.leb TWO64 hi) eqn:Er; [exact TRIV|].
      unfold TWO64 in Er. apply orb_false_iff in Er as [Er1 Er2]. apply Z.leb_gt in Er1. apply Z.leb_gt in Er2.
      destruct neg; simpl.
      * (* [comment removed for export] *)
        assert (Hne : eval nu d <> 0).
        { intros E0. assert (X : (2 ^ 64 | eval nu d)) by (exists 0; lia). apply Hiff in X.
          rewrite X in Hc. discriminate. }
        destruct (Z.eqb_spec lo 0).
        -- pose proof (aassume_sound A nu (laddc (lneg d) 1) HG ltac:(rewrite eval_laddc, eval_lneg; lia)
                        ltac:(apply lin_below_laddc; now apply lin_below_lneg)) as (F&L&X).
           split; [exact F|]. split; [exact L|]. split; [exact X|apply aassume_next].
        -- destruct (Z.eqb_spec hi 0); [|exact TRIV].
           pose proof (aassume_sound A nu (laddc d 1) HG ltac:(rewrite eval_laddc; lia)
                        ltac:(now apply lin_below_laddc)) as (F&L&X).
           split; [exact F|]. split; [exact L|]. split; [exact X|apply aassume_next].
      * (* [comment removed for export] *)
        assert (Hdz : eval nu d = 0).
        { assert (X : (2 ^ 64 | eval nu d)) by (apply Hiff; destruct (_ =? _); auto).
          destruct X as [q Hq]. assert (q = 0) by nia. subst; lia. }
        pose proof (aassume2_sound A nu d (lneg d) HG ltac:(lia) ltac:(rewrite eval_lneg; lia) Bd
                     ltac:(now apply lin_below_lneg)) as (F&L&X).
        split; [exact F|]. split; [exact L|]. split; [exact X|apply aassume2_next].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma lgamma_remove_conddef A nu b :
  lgamma A nu -> lgamma (set_conddef A (pm_remove b (vs_conddef A))) nu.
Proof.
  intros (HS&HC&HM&HV&(B0&B1&B2&B3&B4&(C1&C2&C3))).
  split; [exact HS|]. split.
  { intros b' k x y Hg. simpl in Hg. rewrite pm_get_remove in Hg. destruct (Pos.eqb b' b); [discriminate|]. now apply HC. }
  split; [exact HM|]. split; [exact HV|].
  split; [exact B0|]. split; [exact B1|]. split; [exact B2|]. split; [exact B3|]. split; [exact B4|].
  split; [|split; [exact C2|exact C3]].
  intros b' k x y Hg. simpl in Hg. rewrite pm_get_remove in Hg. destruct (Pos.eqb b' b); [discriminate|]. exact (C1 _ _ _ _ Hg).
Qed.

Lemma lgamma_remove_moddef A nu r :
  lgamma A nu -> lgamma (set_moddef A (pm_remove r (vs_moddef A))) nu.
Proof.
  intros (HS&HC&HM&HV&(B0&B1&B2&B3&B4&(C1&C2&C3))).
  split; [exact HS|]. split; [exact HC|]. split.
  { intros r' x m Hg. simpl in Hg. rewrite pm_get_remove in Hg. destruct (Pos.eqb r' r); [discriminate|]. now apply HM. }
  split; [exact HV|].
  split; [exact B0|]. split; [exact B1|]. split; [exact B2|]. split; [exact B3|]. split; [exact B4|].
  split; [exact C1|]. split; [|exact C3].
  intros r' x m Hg. simpl in Hg. rewrite pm_get_remove in Hg. destruct (Pos.eqb r' r); [discriminate|]. exact (C2 _ _ _ Hg).
Qed.

Lemma point_of_sound i v x : point_of i = Some v -> in_itv x i -> x = v.
Proof.
  unfold point_of. destruct i as [[lo|] [hi|]]; try discriminate.
  destruct (Z.eqb_spec lo hi); [|discriminate]. intros X [H1 H2]; inversion X; subst; simpl in *; lia.
Qed.

Lemma fire_moddefs_sound l : forall A nu,
  lgamma A nu -> lgamma (fire_moddefs A l) nu /\ aext A (fire_moddefs A l) nu nu /\ vs_next (fire_moddefs A l) = vs_next A.
Proof.
  induction l as [|[r xm] t IH]; intros A nu HG; simpl.
  - split; [exact HG|]. split; [apply aext_refl|reflexivity].
  - destruct (pm_get r (vs_moddef A)) as [[x m]|] eqn:Hg; [|now apply IH].
    destruct (point_of (agetbox A r)) as [v|] eqn:Hp; [|now apply IH].
    pose proof (point_of_sound _ _ _ Hp (agetbox_sound A nu r HG)) as Hv.
    pose proof HG as HG'. destruct HG' as (HS&HC&HM&HV&HB).
    destruct (HM _ _ _ Hg) as [Hm Hr].
    destruct HB as (B0&B1&B2&B3&B4&(C1&C2&C3)).
    destruct (C2 _ _ _ Hg) as [Hrb Hxb].
    pose proof (lgamma_remove_moddef A nu r HG) as HG1.
    set (A1 := set_moddef A (pm_remove r (vs_moddef A))) in *.
    assert (N1 : vs_next A1 = vs_next A) by reflexivity.
    assert (X1 : aext A A1 nu nu) by (apply aext_keep; [reflexivity|apply same_shape_set_moddef]).
    assert (STEP : forall A2, lgamma A2 nu -> aext A A2 nu nu -> vs_next A2 = vs_next A ->
              lgamma (fire_moddefs A2 t) nu /\ aext A (fire_moddefs A2 t) nu nu /\ vs_next (fire_moddefs A2 t) = vs_next A).
    { intros A2 HG2 X2 N2. destruct (IH A2 nu HG2) as (L&X&N). split; [exact L|]. split; [eapply aext_trans; eauto|congruence]. }
    destruct (lin_single x) as [[s k]|] eqn:Es; [|now apply STEP].
    destruct (Z.eqb_spec (Z.abs k) 1); [|now apply STEP].
    assert (Ex : eval nu x = lc x + k * nu s) by (apply eval_single; exact Es).
    assert (Hs : (s < vs_next A1)%positive).
    { rewrite N1. apply (proj1 (lin_below_iff x (vs_next A)) Hxb). unfold lsyms, lin_single in *.
      destruct (lt x) as [|[s' k'] [|]]; try discriminate. inversion Es; subst. simpl; auto. }
    assert (Hd : (m | nu s - (k * (v - lc x)) mod m)).
    { assert (H1 : (m | nu s - k * (v - lc x))).
      { rewrite Hv in Hr. (* [comment removed for export] *)
        rewrite Ex in Hr.
        pose proof (Z.div_mod (lc x + k * nu s) m ltac:(lia)) as Hdm. rewrite <- Hr in Hdm.
        assert (k = 1 \/ k = -1) by lia.
        destruct H as [-> | ->].
        - exists ((lc x + 1 * nu s) / m). nia.
        - exists (- ((lc x + -1 * nu s) / m)). nia. }
      destruct H1 as [q Hq]. exists (q + (k * (v - lc x)) / m).
      pose proof (Z.div_mod (k * (v - lc x)) m ltac:(lia)). nia. }
    pose proof (ameet_cong_sound A1 nu s m _ HG1 Hd Hs) as (F&L&X).
    pose proof (ameet_cong_next A1 s m ((k * (v - lc x)) mod m)) as N.
    apply STEP; [exact L|exact (aext_trans _ _ _ _ _ _ X1 X)|congruence].
Qed.

Lemma trigger_sound fuel : forall A nu,
  lgamma A nu -> lgamma (trigger fuel A) nu /\ aext A (trigger fuel A) nu nu /\ vs_next (trigger fuel A) = vs_next A.
Proof.
  induction fuel as [|fuel IH]; intros A nu HG; cbn [trigger].
  - split; [exact HG|]. split; [apply aext_refl|reflexivity].
  - destruct (find _ (pm_elements (vs_conddef A))) as [[b [[k x] y]]|] eqn:Ef; [|now apply fire_moddefs_sound].
    apply find_some in Ef as [Hin Hdec]. cbn [fst] in Hdec.
    apply pm_elements_sound in Hin.
    destruct (point_of (agetbox A b)) as [v|] eqn:Hp; [|discriminate].
    pose proof (point_of_sound _ _ _ Hp (agetbox_sound A nu b HG)) as Hv.
    pose proof HG as HG'. destruct HG' as (HS&HC&HM&HV&HB).
    pose proof (HC _ _ _ _ Hin) as Hb.
    destruct HB as (B0&B1&B2&B3&B4&(C1&C2&C3)).
    destruct (C1 _ _ _ _ Hin) as (Bb&Bx&By).
    pose proof (lgamma_remove_conddef A nu b HG) as HG1.
    set (A1 := set_conddef A (pm_remove b (vs_conddef A))) in *.
    subst v.
    assert (Hc : xorb (wcond k (zwrap 64 (eval nu x)) (zwrap 64 (eval nu y))) (negb (Z.eqb (nu b) 1)) = true).
    { rewrite wcond_cond_holds. rewrite Hb. destruct (cond_holds k (eval nu x) (eval nu y)); reflexivity. }
    pose proof (refine0_sound A1 nu (k, negb (Z.eqb (nu b) 1)) (Some x) (Some y) _ _ HG1
                  (wval_of_eval nu x) (wval_of_eval nu y) Bx By Hc) as (F&L&X&N).
    destruct (refine0 A1 _ _ _) as [ok A2]. simpl in F, L, X, N.
    destruct (IH A2 nu L) as (L3&X3&N3).
    split; [exact L3|]. split; [|congruence].
    assert (X0 : aext A A1 nu nu) by (apply aext_keep; [reflexivity|apply same_shape_set_conddef]).
    exact (aext_trans _ _ _ _ _ _ X0 (aext_trans _ _ _ _ _ _ X X3)).
Qed.

Theorem refine_sound A nu c a b ua ub :
  lgamma A nu -> wval nu a ua -> wval nu b ub ->
  vbelow a (vs_next A) -> vbelow b (vs_next A) ->
  xorb (wcond (fst c) ua ub) (snd c) = true ->
  fst (refine A c a b) = true /\ lgamma (snd (refine A c a b)) nu /\ aext A (snd (refine A c a b)) nu nu
  /\ vs_next (snd (refine A c a b)) = vs_next A.
Proof.
  intros HG Ha Hb Ba Bb Hc. unfold refine.
  pose proof (refine0_sound A nu c a b ua ub HG Ha Hb Ba Bb Hc) as (F&L&X&N).
  destruct (refine0 A c a b) as [ok A1]. cbn [fst snd] in F, L, X, N. subst ok.
  destruct a; destruct b; cbn [fst snd]; try (split; [reflexivity|]; split; [exact L|]; split; [exact X|exact N]).
  destruct (trigger_sound (trigger_fuel A1) A1 nu L) as (L2&X2&N2).
  split; [reflexivity|]. split; [exact L2|]. split; [eapply aext_trans; eauto|].
  rewrite N2; exact N.
Qed.
