(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Bool Lia.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import VLinalg VWord2 VState VLogic VAbs VAbsSound VAbsSound2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Unset Lia Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition res_exact (A : vstate) (nu : val) (rA : absval * vstate) (x : Z) : Prop :=
  let '(r, A') := rA in
  exists nu', aext A A' nu nu' /\ lgamma A' nu' /\
    match r with Some e => eval nu' e = x /\ lin_below e (vs_next A') = true | None => True end.

(* [comment removed for export] *)
Definition res_word (A : vstate) (nu : val) (rA : absval * vstate) (u : Z) : Prop :=
  let '(r, A') := rA in
  exists nu', aext A A' nu nu' /\ lgamma A' nu' /\
    match r with Some e => u = zwrap 64 (eval nu' e) /\ lin_below e (vs_next A') = true | None => True end.

Lemma res_exact_word A nu rA x :
  res_exact A nu rA x -> res_word A nu rA (zwrap 64 x).
Proof.
  unfold res_exact, res_word. destruct rA as [r A']. intros [nu' (X&L&R)]. exists nu'.
  split; [exact X|]. split; [exact L|]. destruct r; auto. destruct R as [-> B]; auto.
Qed.

Lemma res_word_none A nu A' u : lgamma A' nu -> aext A A' nu nu -> res_word A nu (None, A') u.
Proof. intros HL HX. exists nu. split; [exact HX|]. split; [exact HL|exact I]. Qed.

Lemma res_top A nu u : lgamma A nu -> res_word A nu (None, A) u.
Proof. intros HL. exists nu. split; [apply aext_refl|]. split; [exact HL|exact I]. Qed.

Lemma res_exact_same A nu e x :
  lgamma A nu -> eval nu e = x -> lin_below e (vs_next A) = true -> res_exact A nu (Some e, A) x.
Proof. intros HL HE HB. exists nu. split; [apply aext_refl|]. split; [exact HL|]. split; [exact HE|exact HB]. Qed.

Lemma res_exact_fresh A nu b x :
  lgamma A nu -> in_itv x b -> res_exact A nu (afresh A b) x.
Proof.
  intros HG Hx. unfold res_exact. pose proof (afresh_sound A nu b x HG Hx) as H.
  destruct (afresh A b) as [v A']. destruct H as [nu' (X&L&R)]. exists nu'.
  split; [exact X|]. split; [exact L|]. destruct v; [exact R|destruct R].
Qed.

Lemma afresh_some A b : exists e A', afresh A b = (Some e, A').
Proof. unfold afresh. destruct (fresh_lin A b) as [e A']. eauto. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma floor_seg x lo hi m : 0 < m -> lo <= x <= hi -> fdiv lo m = fdiv hi m ->
  x mod m = x - (fdiv lo m) * m.
Proof.
  intros Hm Hx E. unfold fdiv in *.
  assert (H1 : lo / m <= x / m) by (apply Z.div_le_mono; lia).
  assert (H2 : x / m <= hi / m) by (apply Z.div_le_mono; lia).
  assert (Eq : x / m = lo / m) by lia.
  rewrite Z.mod_eq by lia. rewrite Eq. lia.
Qed.

Lemma zswrap32_seg x lo hi : lo <= x <= hi ->
  fdiv (lo + TWO31) TWO32 = fdiv (hi + TWO31) TWO32 ->
  zswrap 32 x = x - (fdiv (lo + TWO31) TWO32) * TWO32.
Proof.
  intros Hx E. unfold zswrap, TWO31, TWO32 in *.
  change (2 ^ (32 - 1)) with (2 ^ 31).
  rewrite (floor_seg (x + 2 ^ 31) (lo + 2 ^ 31) (hi + 2 ^ 31) (2 ^ 32)); try lia; auto.
Qed.

Lemma zswrap32_of_zwrap c : zswrap 32 c = (let x := Z.land c (TWO32 - 1) in if Z.leb TWO31 x then x - TWO32 else x).
Proof.
  unfold TWO32, TWO31. rewrite land_lowmask by lia. cbn zeta.
  pose proof (Z.mod_pos_bound c (2 ^ 32) ltac:(lia)) as Hr.
  pose proof (zswrap_divide_self 32 c ltac:(lia)) as [q Hq].
  pose proof (zswrap_range 32 c ltac:(lia)) as Hs. change (2 ^ (32 - 1)) with (2 ^ 31) in Hs.
  pose proof (zwrap_divide_self 32 c ltac:(lia)) as [p Hp]. unfold zwrap in Hp.
  (* [comment removed for export] *)
  destruct (Z.leb_spec (2 ^ 31) (c mod 2 ^ 32)); nia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Theorem azext_sound A nu v x nbits :
  lgamma A nu -> 0 <= nbits ->
  match v with Some e => eval nu e = x /\ lin_below e (vs_next A) = true | None => True end ->
  res_exact A nu (azext A v nbits) (zwrap nbits x).
Proof.
  intros HG Hn Hv. unfold azext.
  pose proof (zwrap_range nbits x Hn) as Hr.
  assert (Hitv : in_itv (zwrap nbits x) (Some 0, Some (2 ^ nbits - 1))) by (split; simpl; lia).
  destruct v as [e|].
  - destruct Hv as [Hx Hb].
    destruct (lin_is_const e) eqn:Ec.
    + apply res_exact_same; auto. rewrite eval_lconst. rewrite (eval_is_const nu e Ec) in Hx. subst x.
      unfold zwrap. rewrite <- land_lowmask by lia. reflexivity.
    + rewrite (lp_bounds_not_empty' A nu e HG).
      pose proof (lp_bounds_sound nu (vs_store A) (lg_sat _ _ HG) e) as Hbd.
      assert (CONG : forall r, lin_low_bits (scong (vs_store A)) e nbits = Some r ->
                 res_exact A nu (Some (lconst r), A) (zwrap nbits x)).
      { intros r Hlb. apply res_exact_same; auto. rewrite eval_lconst.
        destruct (lin_low_bits_sound nu (scong (vs_store A)) e nbits r (sat_cong _ _ (lg_sat _ _ HG)) Hn Hlb) as [E _].
        unfold zwrap. rewrite <- Hx. symmetry. exact E. }
      destruct (lp_bounds (vs_store A) e) as [[lo|] [hi|]];
        try (destruct (lin_low_bits _ _ _) eqn:El; [now apply CONG|(apply res_exact_fresh; [exact HG|exact Hitv])]).
      destruct Hbd as [Hlo Hhi]; simpl in Hlo, Hhi.
      destruct (Z.eqb_spec (fdiv lo (2 ^ nbits)) (fdiv hi (2 ^ nbits))).
      * apply res_exact_same; [exact HG| |now apply lin_below_laddc].
        rewrite eval_laddc, Hx. unfold zwrap. pose proof (pow2_pos nbits Hn).
        rewrite (floor_seg x lo hi (2 ^ nbits)); lia.
      * destruct (lin_low_bits _ _ _) eqn:El; [now apply CONG|(apply res_exact_fresh; [exact HG|exact Hitv])].
  - (apply res_exact_fresh; [exact HG|exact Hitv]).
Qed.

Lemma azext_some A v n : exists e A', azext A v n = (Some e, A').
Proof.
  unfold azext. destruct v as [e|]; [|apply afresh_some].
  destruct (lin_is_const e); [eauto|]. destruct (itv_empty _); [eauto|].
  destruct (lp_bounds _ _) as [[lo|] [hi|]]; try (destruct (lin_low_bits _ _ _); [eauto|apply afresh_some]).
  destruct (Z.eqb _ _); [eauto|]. destruct (lin_low_bits _ _ _); [eauto|apply afresh_some].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Theorem asext32_sound A nu v x :
  lgamma A nu ->
  match v with Some e => eval nu e = x /\ lin_below e (vs_next A) = true | None => True end ->
  res_exact A nu (asext32 A v) (zswrap 32 x).
Proof.
  intros HG Hv. unfold asext32.
  pose proof (zswrap_range 32 x ltac:(lia)) as Hr. change (2 ^ (32 - 1)) with (2 ^ 31) in Hr.
  assert (Hitv : in_itv (zswrap 32 x) (Some (- TWO31), Some (TWO31 - 1))) by (unfold TWO31; split; simpl; lia).
  destruct v as [e|]; [|(apply res_exact_fresh; [exact HG|exact Hitv])].
  destruct Hv as [Hx Hb].
  destruct (lin_is_const e) eqn:Ec.
  - apply res_exact_same; auto. rewrite eval_lconst. rewrite (eval_is_const nu e Ec) in Hx. subst x.
    rewrite zswrap32_of_zwrap. reflexivity.
  - rewrite (lp_bounds_not_empty' A nu e HG).
    pose proof (lp_bounds_sound nu (vs_store A) (lg_sat _ _ HG) e) as Hbd.
    destruct (lp_bounds (vs_store A) e) as [[lo|] [hi|]]; try (apply res_exact_fresh; [exact HG|exact Hitv]).
    destruct Hbd as [Hlo Hhi]; simpl in Hlo, Hhi.
    destruct (Z.eqb_spec (fdiv (lo + TWO31) TWO32) (fdiv (hi + TWO31) TWO32)); [|(apply res_exact_fresh; [exact HG|exact Hitv])].
    apply res_exact_same; [exact HG| |now apply lin_below_laddc].
    rewrite eval_laddc, Hx. rewrite (zswrap32_seg x lo hi); lia.
Qed.

Lemma asext32_some A v : exists e A', asext32 A v = (Some e, A').
Proof.
  unfold asext32. destruct v as [e|]; [|apply afresh_some].
  destruct (lin_is_const e); [eauto|]. destruct (itv_empty _); [eauto|].
  destruct (lp_bounds _ _) as [[lo|] [hi|]]; try apply afresh_some.
  destruct (Z.eqb _ _); [eauto|apply afresh_some].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition denotes (nu : val) (b : positive) (v : absval) (u : Z) : Prop :=
  match v with Some e => u = zwrap 64 (eval nu e) /\ lin_below e b = true | None => True end.

Definition ares_sound (A : vstate) (nu : val) (r : ares) (u : Z) : Prop :=
  match r with
  | AR v A' => res_word A nu (v, A') u
  | AFork bsym v0 v1 blo A' =>
      A' = A /\ (bsym < vs_next A)%positive /\ (nu bsym = blo \/ nu bsym = blo + 1) /\
      (nu bsym = blo -> denotes nu (vs_next A) v0 u) /\
      (nu bsym = blo + 1 -> denotes nu (vs_next A) v1 u)
  end.

Lemma zm64_zwrap c : zm64 c = zwrap 64 c.
Proof. unfold zm64, M64. apply land_lowmask. lia. Qed.

Lemma mask01_sound A nu x s m0 m1 lo u :
  lgamma A nu -> wval nu x u -> vbelow x (vs_next A) ->
  mask01 A x = Some (s, m0, m1, lo) ->
  (s < vs_next A)%positive /\ (nu s = lo \/ nu s = lo + 1) /\
  (nu s = lo -> u = zwrap 64 m0) /\ (nu s = lo + 1 -> u = zwrap 64 m1).
Proof.
  intros HG Hw Hb. unfold mask01. destruct x as [e|]; [|discriminate].
  destruct (lin_is_const e); [discriminate|].
  destruct (lin_single e) as [[s' k]|] eqn:Es; [|discriminate].
  pose proof (agetbox_sound A nu s' HG) as Hbox.
  destruct (agetbox A s') as [[blo|] [bhi|]]; try discriminate.
  destruct (Z.eqb_spec (bhi - blo) 1); [|discriminate].
  intros X; inversion X; subst; clear X.
  destruct Hbox as [H1 H2]; simpl in H1, H2.
  pose proof (wval_some _ _ _ Hw) as Hu. rewrite (eval_single nu e s k Es) in Hu.
  simpl in Hb.
  assert (Hs : (s < vs_next A)%positive).
  { apply (proj1 (lin_below_iff e (vs_next A)) Hb). unfold lsyms, lin_single in *.
    destruct (lt e) as [|[s1 k1] [|]]; try discriminate. inversion Es; subst. simpl; auto. }
  split; [exact Hs|]. split; [lia|]. split; intros E; rewrite Hu, E; f_equal; lia.
Qed.

Lemma wval_land_range nu a b ua ub : wval nu a ua -> wval nu b ub -> 0 <= Z.land ua ub < 2 ^ 64.
Proof. intros [Ha _] [Hb _]. apply land_upper64; lia. Qed.

Lemma and_mask_sound A nu x m u :
  lgamma A nu -> u = zwrap 64 (eval nu x) -> lin_below x (vs_next A) = true ->
  0 < m < 2 ^ 64 ->
  ares_sound A nu (and_mask A x m) (Z.land u m).
Proof.
  intros HG Hu Hb Hm. unfold and_mask.
  pose proof (zwrap_range 64 (eval nu x) ltac:(lia)) as Hur. rewrite <- Hu in Hur.
  pose proof (land_upper u m ltac:(lia) ltac:(lia)) as [Hl1 Hl2].
  pose proof (lp_bounds_sound nu (vs_store A) (lg_sat _ _ HG) x) as Hbd.
  pose proof (lin_cong_sound nu (scong (vs_store A)) x (sat_cong _ _ (lg_sat _ _ HG))) as HC.
  destruct (is_lowmask m) eqn:Elm.
  - (* [comment removed for export] *)
    unfold is_lowmask, is_pow2, log2_exact in Elm.
    destruct (Z.ltb_spec 0 (m + 1)); [|discriminate].
    destruct (Z.eqb_spec (m + 1) (2 ^ Z.log2 (m + 1))); [|discriminate]. clear Elm.
    set (k := Z.log2 (m + 1)) in *. pose proof (Z.log2_nonneg (m + 1)) as Hk. fold k in Hk.
    assert (Hk64 : k <= 64).
    { destruct (Z_lt_le_dec 64 k); auto. exfalso.
      assert (2 ^ 64 < 2 ^ k) by (apply Z.pow_lt_mono_r; lia). lia. }
    assert (Pk64 : 2 ^ k <= 2 ^ 64) by (apply Z.pow_le_mono_r; lia).
    assert (Eland : Z.land u m = (eval nu x) mod 2 ^ k).
    { replace m with (2 ^ k - 1) by lia. rewrite land_lowmask by lia. rewrite Hu. unfold zwrap.
      apply Z.mod_mod_divide. apply pow2_divide. lia. }
    pose proof (Z.mod_pos_bound (eval nu x) (2 ^ k) ltac:(apply pow2_pos; lia)) as Hmr.
    rewrite (lp_bounds_not_empty' A nu x HG).
    (* [comment removed for export] *)
    match goal with |- ares_sound _ _ (if ?c then _ else _) _ => destruct c eqn:Einseg end.
    + destruct (lp_bounds (vs_store A) x) as [[lo|] [hi|]]; try discriminate.
      destruct Hbd as [Hlo Hhi]; simpl in Hlo, Hhi. apply Z.eqb_eq in Einseg.
      exists nu. split; [apply aext_refl|]. split; [exact HG|]. split; [|now apply lin_below_laddc].
      rewrite eval_laddc, Eland. replace (m + 1) with (2 ^ k) in * by lia.
      pose proof (pow2_pos k Hk) as Pk.
      rewrite (floor_seg (eval nu x) lo hi (2 ^ k)) in Hmr |- * by (auto; lia).
      rewrite zwrap_id; lia.
    + clear Einseg. destruct (lin_cong (scong (vs_store A)) x) as [cm cr]. destruct HC as (Hdiv&Hcm&Hcr).
      destruct ((cm =? 0) || ((0 <? cm) && (cm mod (m + 1) =? 0))) eqn:Ecg.
      * exists nu. split; [apply aext_refl|]. split; [exact HG|]. split; [|reflexivity].
        rewrite eval_lconst, Eland. replace (m + 1) with (2 ^ k) in * by lia.
        assert (Hk1 : (2 ^ k | eval nu x - cr)).
        { apply orb_prop in Ecg. destruct Ecg as [E0|E1].
          - apply Z.eqb_eq in E0. subst cm. destruct Hdiv as [q Hq]. exists 0. lia.
          - apply andb_prop in E1 as [E1 E2]. apply Z.ltb_lt in E1. apply Z.eqb_eq in E2.
            exact (divide_mod_0 cm (2 ^ k) _ (pow2_pos k Hk) E2 Hdiv). }
        rewrite (divide_mod_eq (2 ^ k) (eval nu x) cr (pow2_pos k Hk) Hk1).
        pose proof (Z.mod_pos_bound cr (2 ^ k) (pow2_pos k Hk)). rewrite zwrap_id; lia.
      * (* [comment removed for export] *)
        set (top := match lp_bounds (vs_store A) x with
                    | (Some lo, Some hi) => if lo <? 0 then m else Z.min m hi | _ => m end).
        assert (Htop : in_itv ((eval nu x) mod 2 ^ k) (Some 0, Some top)).
        { split; simpl; [lia|]. unfold top. destruct (lp_bounds (vs_store A) x) as [[lo|] [hi|]]; try lia.
          destruct Hbd as [Hlo Hhi]; simpl in Hlo, Hhi. destruct (Z.ltb_spec lo 0); [lia|].
          apply Z.min_glb; [lia|]. eapply Z.le_trans; [apply Z.mod_le; try lia; apply pow2_pos; lia|lia]. }
        pose proof (fresh_sym_box_sound A nu (Some 0, Some top) ((eval nu x) mod 2 ^ k) HG Htop) as FS.
        destruct (fresh_sym A) as [rs A1] eqn:Efs.
        destruct FS as (X2&L2&V2&S2&N2).
        set (A2 := asetbox A1 rs (Some 0, Some top)) in *.
        set (nu2 := vupd nu rs (eval nu x mod 2 ^ k)) in *.
        assert (Ex2 : eval nu2 x = eval nu x) by (apply (eval_ext_below (vs_next A)); [apply X2|exact Hb]).
        (* [comment removed for export] *)
        set (A3 := if (1 <? cm) && ((m + 1) mod cm =? 0) then snd (ameet_cong A2 rs cm cr) else A2).
        assert (L3 : lgamma A3 nu2 /\ aext A A3 nu nu2 /\ vs_next A3 = vs_next A2).
        { unfold A3. destruct ((1 <? cm) && ((m + 1) mod cm =? 0)) eqn:Ec3; [|split; [exact L2|split; [exact X2|reflexivity]]].
          apply andb_prop in Ec3 as [Ec1 Ec2]. apply Z.ltb_lt in Ec1. apply Z.eqb_eq in Ec2.
          assert (Hd : (cm | nu2 rs - cr)).
          { rewrite V2. replace (m + 1) with (2 ^ k) in Ec2 by lia.
            (* [comment removed for export] *)
            assert (H1 : (cm | eval nu x mod 2 ^ k - eval nu x)).
            { eapply divide_mod_0; [lia|exact Ec2|]. exists (- (eval nu x / 2 ^ k)).
              pose proof (Z.div_mod (eval nu x) (2 ^ k) ltac:(pose proof (pow2_pos k Hk); lia)). lia. }
            destruct H1 as [q1 Hq1]. destruct Hdiv as [q2 Hq2]. exists (q1 + q2). lia. }
          pose proof (ameet_cong_sound A2 nu2 rs cm cr L2 Hd S2) as (F&L&X).
          split; [exact L|]. split; [eapply aext_trans; eauto|apply ameet_cong_next]. }
        destruct L3 as (L3'&X3&N3).
        (* [comment removed for export] *)
        exists nu2. split; [|split].
        -- eapply aext_trans; [exact X3|]. apply aext_keep; [reflexivity|apply same_shape_set_moddef].
        -- destruct L3' as (HS&HC&HM&HV&(B0&B1&B2&B3&B4&(C1&C2&C3))).
           split; [exact HS|]. split; [exact HC|]. split.
           { intros r x0 m0 Hg. simpl in Hg. rewrite pm_get_set in Hg. destruct (Pos.eqb_spec r rs).
             - inversion Hg; subst. split; [pose proof (pow2_pos k Hk); lia|]. rewrite V2, Ex2. f_equal. lia.
             - exact (HM _ _ _ Hg). }
           split; [exact HV|]. split; [exact B0|]. split; [exact B1|]. split; [exact B2|]. split; [exact B3|]. split; [exact B4|].
           split; [exact C1|]. split; [|exact C3].
           intros r x0 m0 Hg. simpl in Hg. rewrite pm_get_set in Hg. destruct (Pos.eqb_spec r rs).
           ++ inversion Hg; subst. simpl. split; [rewrite N3; exact S2|]. rewrite N3. eapply lin_below_mono; [|exact Hb].
              destruct X2 as (_&HH&_). exact HH.
           ++ exact (C2 _ _ _ Hg).
        -- simpl. split; [|apply lin_below_lsym; simpl; rewrite N3; exact S2].
           rewrite eval_lsym, V2, Eland. rewrite zwrap_id; [reflexivity|lia].
  - destruct (is_pow2 (TWO64 - m)) eqn:Ep2.
    + (* [comment removed for export] *)
      unfold is_pow2, log2_exact in Ep2.
      destruct (Z.ltb_spec 0 (TWO64 - m)); [|discriminate].
      destruct (Z.eqb_spec (TWO64 - m) (2 ^ Z.log2 (TWO64 - m))); [|discriminate]. clear Ep2.
      set (k := Z.log2 (TWO64 - m)) in *. pose proof (Z.log2_nonneg (TWO64 - m)) as Hk. fold k in Hk.
      unfold TWO64 in *.
      assert (Hk64 : k <= 64).
      { destruct (Z_lt_le_dec 64 k); auto. exfalso. assert (2 ^ 64 < 2 ^ k) by (apply Z.pow_lt_mono_r; lia). lia. }
      pose proof (pow2_pos k Hk) as Pk.
      assert (Pk64 : 2 ^ k <= 2 ^ 64) by (apply Z.pow_le_mono_r; lia).
      assert (Eland : Z.land u m = u - u mod 2 ^ k).
      { replace m with (2 ^ 64 - 2 ^ k) by lia. apply land_alignmask; lia. }
      assert (Emod : u mod 2 ^ k = (eval nu x) mod 2 ^ k).
      { rewrite Hu. unfold zwrap. apply Z.mod_mod_divide. apply pow2_divide. lia. }
      pose proof (Z.mod_pos_bound (eval nu x) (2 ^ k) Pk) as Hmr.
      assert (Ewrap : zwrap 64 (eval nu x - eval nu x mod 2 ^ k) = u - u mod 2 ^ k).
      { rewrite Emod.
        assert (Hur2 : 0 <= u - eval nu x mod 2 ^ k < 2 ^ 64).
        { rewrite <- Emod. pose proof (Z.mod_le u (2 ^ k) ltac:(lia) Pk). pose proof (Z.mod_pos_bound u (2 ^ k) Pk). lia. }
        rewrite <- (zwrap_id 64 (u - eval nu x mod 2 ^ k) Hur2).
        apply zwrap_congr; [lia|]. rewrite Hu at 1.
        destruct (zwrap_divide_self 64 (eval nu x) ltac:(lia)) as [q Hq]. exists (- q). lia. }
      destruct (lin_cong (scong (vs_store A)) x) as [cm cr]. destruct HC as (Hdiv&Hcm&Hcr).
      replace (2 ^ 64 - (2 ^ 64 - m)) with m by lia.
      destruct ((cm =? 0) || ((0 <? cm) && (cm mod (2 ^ 64 - m) =? 0))) eqn:Ecg.
      * exists nu. split; [apply aext_refl|]. split; [exact HG|]. split; [|now apply lin_below_laddc].
        rewrite eval_laddc. replace (2 ^ 64 - m) with (2 ^ k) in * by lia.
        assert (Hk1 : (2 ^ k | eval nu x - cr)).
        { apply orb_prop in Ecg. destruct Ecg as [E0|E1].
          - apply Z.eqb_eq in E0. subst cm. destruct Hdiv as [q Hq]. exists 0. lia.
          - apply andb_prop in E1 as [E1 E2]. apply Z.ltb_lt in E1. apply Z.eqb_eq in E2.
            exact (divide_mod_0 cm (2 ^ k) _ Pk E2 Hdiv). }
        rewrite <- (divide_mod_eq (2 ^ k) (eval nu x) cr Pk Hk1).
        replace (eval nu x + - (eval nu x mod 2 ^ k)) with (eval nu x - eval nu x mod 2 ^ k) by lia.
        rewrite Ewrap. exact Eland.
      * (* [comment removed for export] *)
        replace (2 ^ 64 - m) with (2 ^ k) by lia.
        set (qb := (match fst (lp_bounds (vs_store A) x) with Some lo => Some (lo - (2 ^ k - 1)) | None => None end,
                    snd (lp_bounds (vs_store A) x))).
        set (qv := eval nu x - eval nu x mod 2 ^ k).
        assert (Hqb : in_itv qv qb).
        { unfold qb, qv. destruct (lp_bounds (vs_store A) x) as [[lo|] [hi|]]; destruct Hbd as [Hlo Hhi];
          cbn [fst snd lo_le hi_ge] in Hlo, Hhi; split; cbn [fst snd lo_le hi_ge]; try exact I; lia. }
        pose proof (fresh_sym_box_sound A nu qb qv HG Hqb) as FS.
        destruct (fresh_sym A) as [q A1] eqn:Efs. destruct FS as (X2&L2&V2&S2&N2).
        set (A2 := asetbox A1 q qb) in *. set (nu2 := vupd nu q qv) in *.
        assert (Ex2 : eval nu2 x = eval nu x) by (apply (eval_ext_below (vs_next A)); [apply X2|exact Hb]).
        assert (Hd : (2 ^ k | nu2 q - 0)).
        { rewrite V2. unfold qv. exists (eval nu x / 2 ^ k). pose proof (Z.div_mod (eval nu x) (2 ^ k) ltac:(lia)). lia. }
        pose proof (ameet_cong_sound A2 nu2 q (2 ^ k) 0 L2 Hd S2) as (F3&L3&X3). pose proof (ameet_cong_next A2 q (2 ^ k) 0) as N3.
        set (A3 := snd (ameet_cong A2 q (2 ^ k) 0)) in *.
        assert (Bx3 : lin_below x (vs_next A3) = true).
        { rewrite N3. eapply lin_below_mono; [|exact Hb]. destruct X2 as (_&HH&_); exact HH. }
        assert (Bq3 : lin_below (lsym q) (vs_next A3) = true) by (apply lin_below_lsym; rewrite N3; exact S2).
        pose proof (aassume_sound A3 nu2 (lsub (lsym q) x) L3 ltac:(rewrite eval_lsub, eval_lsym, V2, Ex2; unfold qv; lia)
                      ltac:(now apply lin_below_lsub)) as (F4&L4&X4). pose proof (aassume_next A3 (lsub (lsym q) x)) as N4.
        set (A4 := snd (aassume A3 (lsub (lsym q) x))) in *.
        pose proof (aassume_sound A4 nu2 (laddc (lsub x (lsym q)) (- (2 ^ k - 1))) L4
                      ltac:(rewrite eval_laddc, eval_lsub, eval_lsym, V2, Ex2; unfold qv; lia)
                      ltac:(rewrite N4; apply lin_below_laddc; now apply lin_below_lsub)) as (F5&L5&X5).
        pose proof (aassume_next A4 (laddc (lsub x (lsym q)) (- (2 ^ k - 1)))) as N5.
        exists nu2. split; [|split; [exact L5|]].
        -- eapply aext_trans; [exact X2|]. eapply aext_trans; [exact X3|]. eapply aext_trans; [exact X4|exact X5].
        -- split; [|apply lin_below_lsym; rewrite N5, N4, N3; exact S2].
           rewrite eval_lsym, V2. unfold qv. rewrite Ewrap. exact Eland.
    + destruct (Z.ltb_spec m TWO63); [|apply res_top; exact HG].
      set (top := match lp_bounds (vs_store A) x with
                  | (Some lo, Some hi) => if lo <? 0 then m else Z.min m hi | _ => m end).
      assert (Htop : in_itv (Z.land u m) (Some 0, Some top)).
      { split; simpl; [lia|]. unfold top. destruct (lp_bounds (vs_store A) x) as [[lo|] [hi|]]; try lia.
        destruct Hbd as [Hlo Hhi]; simpl in Hlo, Hhi. destruct (Z.ltb_spec lo 0); [lia|].
        apply Z.min_glb; [lia|]. rewrite Hu in Hl2 |- *. unfold zwrap in *.
        pose proof (Z.mod_le (eval nu x) (2 ^ 64) ltac:(lia) ltac:(lia)). lia. }
      pose proof (afresh_sound A nu (Some 0, Some top) (Z.land u m) HG Htop) as HF.
      destruct (afresh A (Some 0, Some top)) as [v A1]. destruct HF as [nu' (X&L&R)].
      exists nu'. split; [exact X|]. split; [exact L|]. destruct v as [e|]; [|exact I].
      destruct R as [He HB]. split; [|exact HB]. rewrite He. rewrite zwrap_id; [reflexivity|lia].
Qed.

Lemma res_word_fresh A nu b u :
  lgamma A nu -> 0 <= u < 2 ^ 64 -> in_itv u b ->
  res_word A nu (afresh A b) u.
Proof.
  intros HG Hu Hb. pose proof (res_exact_fresh A nu b u HG Hb) as H.
  apply res_exact_word in H. rewrite zwrap_id in H by lia. exact H.
Qed.

Lemma ares_sound_pair A nu v A' u : res_word A nu (v, A') u -> ares_sound A nu (AR v A') u.
Proof. intros H; exact H. Qed.

Lemma ares_fresh A nu b u :
  lgamma A nu -> 0 <= u < 2 ^ 64 -> in_itv u b ->
  ares_sound A nu (let '(v, A1) := afresh A b in AR v A1) u.
Proof.
  intros. pose proof (res_word_fresh A nu b u H H0 H1) as R. destruct (afresh A b) as [v A1]. exact R.
Qed.

Lemma ares_same A nu e u :
  lgamma A nu -> u = zwrap 64 (eval nu e) -> lin_below e (vs_next A) = true -> ares_sound A nu (AR (Some e) A) u.
Proof. intros. exists nu. split; [apply aext_refl|]. split; [exact H|]. split; auto. Qed.

Lemma and_const_sound A nu x ux c :
  lgamma A nu -> wval nu x ux -> vbelow x (vs_next A) ->
  ares_sound A nu (and_const A x c) (Z.land ux (zwrap 64 c)).
Proof.
  intros HG Hx Hb. unfold and_const. rewrite zm64_zwrap.
  pose proof (zwrap_range 64 c ltac:(lia)) as Hc. destruct Hx as [Hux Hx].
  pose proof (land_upper ux (zwrap 64 c) ltac:(lia) ltac:(lia)) as [Hl1 Hl2].
  destruct (Z.eqb_spec (zwrap 64 c) 0) as [E0|E0].
  { rewrite E0, Z.land_0_r. apply ares_same; auto. }
  destruct (Z.eqb_spec (zwrap 64 c) M64) as [E1|E1].
  { unfold M64 in E1. rewrite E1, land_lowmask, Z.mod_small by lia.
    exists nu. split; [apply aext_refl|]. split; [exact HG|]. destruct x as [e|]; [|exact I]. split; [exact Hx|exact Hb]. }
  destruct x as [xe|].
  - destruct (lin_is_const xe) eqn:Ec.
    + apply ares_same; auto. rewrite eval_lconst. rewrite Hx, (eval_is_const nu xe Ec).
      rewrite <- (land_low64 (lc xe) (zwrap 64 c)) by lia. symmetry. apply zwrap_id.
      rewrite (land_low64 (lc xe) (zwrap 64 c)) by lia. apply land_upper64; [apply zwrap_range|]; lia.
    + apply and_mask_sound; auto. unfold M64 in E1. lia.
  - destruct (Z.ltb_spec (zwrap 64 c) TWO63); [|apply res_top; exact HG].
    apply ares_fresh; [exact HG|lia|split; simpl; lia].
Qed.

Lemma const_of_sound nu v u c : wval nu v u -> const_of v = Some c -> u = zwrap 64 c.
Proof.
  unfold const_of. destruct v as [e|]; [|discriminate]. destruct (lin_is_const e) eqn:Ec; [|discriminate].
  intros Hw X; inversion X; subst. rewrite (wval_some _ _ _ Hw). now rewrite (eval_is_const nu e Ec).
Qed.

Lemma sel_and_sound A nu x y ux uy r :
  lgamma A nu -> wval nu x ux -> wval nu y uy -> vbelow x (vs_next A) -> vbelow y (vs_next A) ->
  sel_and A x y = Some r -> ares_sound A nu r (Z.land ux uy).
Proof.
  intros HG Hx Hy Bx By. unfold sel_and.
  destruct (mask01 A x) as [[[[bsym m0] m1] blo]|] eqn:Em; [|discriminate].
  destruct y as [ye|]; [|discriminate].
  pose proof (mask01_sound A nu x bsym m0 m1 blo ux HG Hx Bx Em) as (Sb&Cases&V0&V1).
  rewrite !zm64_zwrap.
  destruct Hy as [Huy Hy]. simpl in By.
  assert (SEL : forall z, ux = zwrap 64 z -> (zwrap 64 z = 0 \/ zwrap 64 z = M64) ->
            denotes nu (vs_next A) (if zwrap 64 z =? 0 then Some lzero else Some ye) (Z.land ux uy)).
  { intros z Hz [E|E]; rewrite E, Hz, E.
    - rewrite Z.eqb_refl. cbn [denotes]. split; [|reflexivity]. rewrite Z.land_0_l. reflexivity.
    - unfold M64. rewrite (proj2 (Z.eqb_neq (2 ^ 64 - 1) 0)) by lia. cbn [denotes].
      split; [|exact By]. rewrite Z.land_comm, land_lowmask, Z.mod_small by lia. exact Hy. }
  destruct ((zwrap 64 m0 =? 0) && (zwrap 64 m1 =? M64) || (zwrap 64 m0 =? M64) && (zwrap 64 m1 =? 0)) eqn:Ez; [|discriminate].
  intros X; inversion X; subst; clear X. cbn [ares_sound].
  split; [reflexivity|]. split; [exact Sb|]. split; [exact Cases|].
  assert (Hz01 : (zwrap 64 m0 = 0 \/ zwrap 64 m0 = M64) /\ (zwrap 64 m1 = 0 \/ zwrap 64 m1 = M64)).
  { apply orb_prop in Ez. destruct Ez as [Ez|Ez]; apply andb_prop in Ez as [E1 E2];
      apply Z.eqb_eq in E1; apply Z.eqb_eq in E2; auto. }
  destruct Hz01 as [Hz0 Hz1].
  split; intros E; [apply (SEL m0); auto|apply (SEL m1); auto].
Qed.

(* [comment removed for export] *)

Lemma zwrap_f_land j x y : 0 <= j -> zwrap j (Z.land x y) = Z.land (zwrap j x) (zwrap j y).
Proof.
  intros Hj. unfold zwrap. apply Z.bits_inj'. intros k Hk. rewrite !Z.land_spec.
  destruct (Z.lt_ge_cases k j).
  - rewrite !Z.mod_pow2_bits_low by lia. apply Z.land_spec.
  - rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.

Lemma zwrap_f_lor j x y : 0 <= j -> zwrap j (Z.lor x y) = Z.lor (zwrap j x) (zwrap j y).
Proof.
  intros Hj. unfold zwrap. apply Z.bits_inj'. intros k Hk. rewrite !Z.lor_spec.
  destruct (Z.lt_ge_cases k j).
  - rewrite !Z.mod_pow2_bits_low by lia. apply Z.lor_spec.
  - rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.

Lemma bitcong_mod_sound A nu ea eb m ra rb :
  lgamma A nu -> bitcong_mod A ea eb = (m, ra, rb, true) ->
  exists j, 1 <= j <= 16 /\ m = 2 ^ j /\ (m | eval nu ea - ra) /\ (m | eval nu eb - rb).
Proof.
  intros HG. unfold bitcong_mod.
  pose proof (lin_cong_sound nu (scong (vs_store A)) ea (sat_cong _ _ (lg_sat _ _ HG))) as Ca.
  pose proof (lin_cong_sound nu (scong (vs_store A)) eb (sat_cong _ _ (lg_sat _ _ HG))) as Cb.
  destruct (lin_cong (scong (vs_store A)) ea) as [ma ra']. destruct (lin_cong (scong (vs_store A)) eb) as [mb rb'].
  destruct Ca as (Da&_). destruct Cb as (Db&_).
  intros X. injection X as Em Era Erb Eok. subst ra' rb'. rewrite Em in Eok.
  unfold bitcong_ok, is_pow2, log2_exact in Eok.
  apply andb_prop in Eok as [Eok E4]. apply andb_prop in Eok as [Eok E3]. apply andb_prop in Eok as [E1 E2].
  apply Z.ltb_lt in E1. apply Z.eqb_eq in E3. apply Z.eqb_eq in E4.
  destruct (Z.ltb_spec 0 m); [|discriminate]. destruct (Z.eqb_spec m (2 ^ Z.log2 m)) as [Epow|]; [|discriminate]. clear E2.
  set (j := Z.log2 m) in *. pose proof (Z.log2_nonneg m) as Hj. fold j in Hj.
  assert (Hcap : forall x, cap16 x <= 65536) by (intros x; unfold cap16; destruct (Z.eqb x 0); destruct (Z.ltb_spec 65536 x); cbn [orb]; lia).
  assert (Hm16 : m <= 2 ^ 16).
  { rewrite <- Em. change (2 ^ 16) with 65536. pose proof (Hcap ma). pose proof (Hcap mb). lia. }
  exists j. split; [|split; [exact Epow|split]].
  - split.
    + destruct (Z_lt_le_dec j 1); [|lia]. exfalso. assert (j = 0) by lia. rewrite H0 in Epow. cbn in Epow. lia.
    + destruct (Z_lt_le_dec 16 j); [|lia]. exfalso. assert (2 ^ 16 < 2 ^ j) by (apply Z.pow_lt_mono_r; lia). lia.
  - eapply Z.divide_trans; [|exact Da]. apply Z.mod_divide; [lia|exact E3].
  - eapply Z.divide_trans; [|exact Db]. apply Z.mod_divide; [lia|exact E4].
Qed.

(* [comment removed for export] *)
Lemma bitcong_fact j x y ra rb (f : Z -> Z -> Z) :
  1 <= j <= 16 ->
  (forall i a b, 0 <= i -> zwrap i (f a b) = f (zwrap i a) (zwrap i b)) ->
  (2 ^ j | x - ra) -> (2 ^ j | y - rb) ->
  (2 ^ j | f (zwrap 64 x) (zwrap 64 y) - (f (ra mod 2 ^ j) (rb mod 2 ^ j)) mod 2 ^ j).
Proof.
  intros Hj Hf Dx Dy. pose proof (pow2_pos j ltac:(lia)) as Pj.
  apply mod_eq_divide; [lia|]. rewrite Z.mod_mod by lia.
  change ((f (zwrap 64 x) (zwrap 64 y)) mod 2 ^ j) with (zwrap j (f (zwrap 64 x) (zwrap 64 y))).
  rewrite Hf, !zwrap_zwrap by lia.
  rewrite (zwrap_congr j x ra), (zwrap_congr j y rb) by (try lia; auto).
  change ((f (ra mod 2 ^ j) (rb mod 2 ^ j)) mod 2 ^ j) with (zwrap j (f (zwrap j ra) (zwrap j rb))).
  rewrite <- Hf by lia. rewrite zwrap_idem by lia. reflexivity.
Qed.

Lemma abitcong_sound A nu v ea eb (f : Z -> Z -> Z) u :
  lgamma A nu ->
  match v with Some e => eval nu e = u /\ lin_below e (vs_next A) = true | None => True end ->
  u = f (zwrap 64 (eval nu ea)) (zwrap 64 (eval nu eb)) ->
  (forall i a b, 0 <= i -> zwrap i (f a b) = f (zwrap i a) (zwrap i b)) ->
  lgamma (abitcong A v ea eb f) nu /\ aext A (abitcong A v ea eb f) nu nu /\ vs_next (abitcong A v ea eb f) = vs_next A.
Proof.
  intros HG Hv Hu Hf.
  assert (TRIV : lgamma A nu /\ aext A A nu nu /\ vs_next A = vs_next A) by (split; [exact HG|split; [apply aext_refl|reflexivity]]).
  unfold abitcong. destruct v as [r|]; [|exact TRIV].
  destruct (lin_single r) as [[s k]|] eqn:Es; [|exact TRIV].
  destruct (Z.eqb_spec k 1); [|exact TRIV]. destruct (Z.eqb_spec (lc r) 0); [|exact TRIV]. cbn [andb]. subst k.
  destruct (bitcong_mod A ea eb) as [[[m ra] rb] ok] eqn:Ebm. destruct ok; [|exact TRIV].
  destruct (bitcong_mod_sound A nu ea eb m ra rb HG Ebm) as [j (Hj&Em&Da&Db)].
  destruct Hv as [Hr Hb].
  assert (Hs : nu s = u). { rewrite (eval_single nu r s 1 Es) in Hr. lia. }
  assert (Hsb : (s < vs_next A)%positive).
  { apply (proj1 (lin_below_iff r (vs_next A)) Hb). unfold lsyms, lin_single in *.
    destruct (lt r) as [|[s' k'] [|? ?]]; try discriminate. injection Es as -> _. left; reflexivity. }
  subst m.
  pose proof (ameet_cong_sound A nu s (2 ^ j) ((f (ra mod 2 ^ j) (rb mod 2 ^ j)) mod 2 ^ j) HG
                ltac:(rewrite Hs, Hu; apply bitcong_fact; auto) Hsb) as (F&L&X).
  split; [exact L|]. split; [exact X|apply ameet_cong_next].
Qed.

Lemma and_generic_sound A nu a b ua ub :
  lgamma A nu -> wval nu a ua -> wval nu b ub -> vbelow a (vs_next A) -> vbelow b (vs_next A) ->
  ares_sound A nu (and_generic A a b) (Z.land ua ub).
Proof.
  intros HG Ha Hb Ba Bb. unfold and_generic.
  pose proof (wval_land_range nu a b ua ub Ha Hb) as Hr.
  destruct Ha as [Hua Ha]. destruct Hb as [Hub Hb].
  pose proof (land_upper ua ub ltac:(lia) ltac:(lia)) as [L1 L2].
  pose proof (land_upper ub ua ltac:(lia) ltac:(lia)) as [L3 L4]. rewrite Z.land_comm in L3, L4.
  assert (ONE : forall x ux', ux' = ua \/ ux' = ub -> ux' = zwrap 64 (eval nu x) ->
     ares_sound A nu (if inU A x then match snd (lp_bounds (vs_store A) x) with
                                    | Some h => let '(v, A1) := afresh A (Some 0, Some h) in AR v A1
                                    | None => AR None A end else AR None A) (Z.land ua ub)).
  { intros x ux' Hux' Hx. destruct (inU A x) eqn:EU; [|apply res_top; exact HG].
    pose proof (inU_sound A nu x HG EU) as HU. rewrite zwrap_id in Hx by lia.
    pose proof (lp_bounds_sound nu (vs_store A) (lg_sat _ _ HG) x) as Hbd.
    destruct (lp_bounds (vs_store A) x) as [lo [h|]]; [|apply res_top; exact HG]. cbn [snd].
    destruct Hbd as [_ Hh]; simpl in Hh. apply ares_fresh; [exact HG|lia|split; simpl; lia]. }
  destruct a as [ea|]; destruct b as [eb|]; try (apply res_top; exact HG).
  - rewrite ?if_andb; destruct (inU A ea && inU A eb) eqn:EU; [|apply res_top; exact HG].
    apply andb_prop in EU as [EUa EUb].
    pose proof (inU_sound A nu ea HG EUa) as HUa. pose proof (inU_sound A nu eb HG EUb) as HUb.
    rewrite zwrap_id in Ha by lia. rewrite zwrap_id in Hb by lia.
    pose proof (lp_bounds_sound nu (vs_store A) (lg_sat _ _ HG) ea) as Hba.
    pose proof (lp_bounds_sound nu (vs_store A) (lg_sat _ _ HG) eb) as Hbb.
    destruct (lp_bounds (vs_store A) ea) as [loa [ha|]]; [|apply res_top; exact HG].
    destruct (lp_bounds (vs_store A) eb) as [lob [hb|]]; [|apply res_top; exact HG]. cbn [snd].
    destruct Hba as [_ Hha]; destruct Hbb as [_ Hhb]; simpl in Hha, Hhb. simpl in Ba, Bb.
    pose proof (afresh_sound A nu (Some 0, Some (Z.min ha hb)) (Z.land ua ub) HG
                  ltac:(split; simpl; [lia|apply Z.min_glb; lia])) as FR.
    destruct (afresh A (Some 0, Some (Z.min ha hb))) as [v A1]. destruct FR as [nu1 (X1&K1&V1)].
    assert (Eea : eval nu1 ea = eval nu ea) by (apply (eval_ext_below (vs_next A)); [exact (proj1 X1)|exact Ba]).
    assert (Eeb : eval nu1 eb = eval nu eb) by (apply (eval_ext_below (vs_next A)); [exact (proj1 X1)|exact Bb]).
    destruct (abitcong_sound A1 nu1 v ea eb Z.land (Z.land ua ub) K1
                ltac:(destruct v; [exact V1|exact I])
                ltac:(rewrite Eea, Eeb, <- Ha, <- Hb, !zwrap_id by lia; reflexivity)
                zwrap_f_land) as (K2&X2&N2).
    exists nu1. split; [eapply aext_trans; [exact X1|exact X2]|]. split; [exact K2|].
    destruct v as [e|]; [|exact I]. destruct V1 as [V1 B1]. split; [rewrite V1; symmetry; apply zwrap_id; lia|].
    rewrite N2. exact B1.
  - apply (ONE ea ua); auto.
  - apply (ONE eb ub); auto.
Qed.

Theorem do_and_sound A nu a b ua ub :
  lgamma A nu -> wval nu a ua -> wval nu b ub -> vbelow a (vs_next A) -> vbelow b (vs_next A) ->
  ares_sound A nu (do_and A a b) (Z.land ua ub).
Proof.
  intros HG Ha Hb Ba Bb. unfold do_and.
  destruct (const_of b) as [cb|] eqn:Ecb.
  - rewrite (const_of_sound nu b ub cb Hb Ecb).
    destruct a; destruct b; try discriminate; apply and_const_sound; auto.
  - destruct (const_of a) as [ca|] eqn:Eca.
    + rewrite (const_of_sound nu a ua ca Ha Eca), Z.land_comm.
      destruct a; destruct b; try discriminate; apply and_const_sound; auto.
    + destruct (sel_and A a b) as [r|] eqn:Es1.
      * pose proof (sel_and_sound A nu a b ua ub r HG Ha Hb Ba Bb Es1) as R. destruct a; destruct b; try exact R. apply res_top; exact HG.
      * destruct (sel_and A b a) as [r|] eqn:Es2.
        -- pose proof (sel_and_sound A nu b a ub ua r HG Hb Ha Bb Ba Es2) as R. rewrite Z.land_comm in R.
           destruct a; destruct b; try exact R. apply res_top; exact HG.
        -- pose proof (and_generic_sound A nu a b ua ub HG Ha Hb Ba Bb) as R. destruct a; destruct b; try exact R.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma next_pow2_spec h : 0 <= h -> exists j, 0 <= j /\ next_pow2 h = 2 ^ j /\ h < 2 ^ j.
Proof.
  intros Hh. unfold next_pow2. destruct (Z.leb_spec h 0).
  - exists 0. simpl. lia.
  - exists (Z.log2 h + 1). pose proof (Z.log2_nonneg h). pose proof (Z.log2_spec h ltac:(lia)) as [_ H2].
    replace (Z.log2 h + 1) with (Z.succ (Z.log2 h)) by lia.
    split; [lia|]. split; [reflexivity|lia].
Qed.

Lemma terms_divisible_sound nu l m : m <> 0 -> terms_divisible l m = true -> (m | eval_terms nu l).
Proof.
  intros Hm. induction l as [|[s k] t IH]; simpl.
  - intros _. exists 0; lia.
  - intros H. apply andb_prop in H as [H1 H2]. apply Z.eqb_eq in H1.
    apply Z.divide_add_r; [|auto]. apply Z.divide_mul_l. apply Z.mod_divide; auto.
Qed.

Lemma ldivisible_sound nu e m : m <> 0 -> ldivisible e m = true -> (m | eval nu e).
Proof.
  intros Hm H. unfold ldivisible in H. apply andb_prop in H as [H1 H2]. apply Z.eqb_eq in H1.
  unfold eval. apply Z.divide_add_r; [apply Z.mod_divide; auto|now apply terms_divisible_sound].
Qed.

Lemma lor_allones u : 0 <= u < 2 ^ 64 -> Z.lor (2 ^ 64 - 1) u = 2 ^ 64 - 1.
Proof.
  intros Hu. pose proof (lor_lower (2 ^ 64 - 1) u ltac:(lia) ltac:(lia)) as [L1 L2].
  pose proof (lor_upper (2 ^ 64 - 1) u 64 ltac:(lia) ltac:(lia) Hu). lia.
Qed.

Lemma zwrap64_m1 : zwrap 64 (-1) = 2 ^ 64 - 1.
Proof. reflexivity. Qed.

Lemma sel_or_sound A nu x y ux uy r :
  lgamma A nu -> wval nu x ux -> wval nu y uy -> vbelow x (vs_next A) -> vbelow y (vs_next A) ->
  sel_or A x y = Some r -> ares_sound A nu r (Z.lor ux uy).
Proof.
  intros HG Hx Hy Bx By. unfold sel_or.
  destruct (mask01 A x) as [[[[bsym m0] m1] blo]|] eqn:Em; [|discriminate].
  pose proof (mask01_sound A nu x bsym m0 m1 blo ux HG Hx Bx Em) as (Sb&Cases&V0&V1).
  rewrite !zm64_zwrap. destruct Hy as [Huy Hy].
  assert (SEL : forall z, ux = zwrap 64 z -> (zwrap 64 z = 0 \/ zwrap 64 z = M64) ->
            denotes nu (vs_next A) (if zwrap 64 z =? 0 then y else Some (lconst (-1))) (Z.lor ux uy)).
  { intros z Hz [E|E]; rewrite E, Hz, E.
    - rewrite Z.eqb_refl. rewrite Z.lor_0_l. destruct y as [ye|]; cbn [denotes]; [|exact I]. split; [exact Hy|exact By].
    - unfold M64. rewrite (proj2 (Z.eqb_neq (2 ^ 64 - 1) 0)) by lia. cbn [denotes].
      split; [|reflexivity]. rewrite eval_lconst, zwrap64_m1. apply lor_allones. lia. }
  destruct ((zwrap 64 m0 =? 0) && (zwrap 64 m1 =? M64) || (zwrap 64 m0 =? M64) && (zwrap 64 m1 =? 0)) eqn:Ez; [|discriminate].
  intros X; inversion X; subst; clear X. cbn [ares_sound].
  split; [reflexivity|]. split; [exact Sb|]. split; [exact Cases|].
  assert (Hz01 : (zwrap 64 m0 = 0 \/ zwrap 64 m0 = M64) /\ (zwrap 64 m1 = 0 \/ zwrap 64 m1 = M64)).
  { apply orb_prop in Ez. destruct Ez as [Ez|Ez]; apply andb_prop in Ez as [E1 E2];
      apply Z.eqb_eq in E1; apply Z.eqb_eq in E2; auto. }
  destruct Hz01 as [Hz0 Hz1].
  split; intros E; [apply (SEL m0); auto|apply (SEL m1); auto].
Qed.

Lemma or_disjoint_sound A nu x y ux uy r :
  lgamma A nu -> ux = zwrap 64 (eval nu x) -> uy = zwrap 64 (eval nu y) ->
  lin_below x (vs_next A) = true -> lin_below y (vs_next A) = true ->
  or_disjoint A x y = Some r -> ares_sound A nu r (Z.lor ux uy).
Proof.
  intros HG Hx Hy Bx By. unfold or_disjoint.
  pose proof (bnd_sound A nu y HG) as Hb.
  destruct (bnd A y) as [[lo|] [hi|]]; try discriminate. destruct Hb as [Hlo Hhi]; simpl in Hlo, Hhi.
  destruct (negb (lin_is_const y) && itv_empty (Some lo, Some hi)); [discriminate|].
  destruct (Z.leb_spec 0 lo); [|discriminate].
  destruct (next_pow2_spec hi ltac:(lia)) as [j (Hj&Ek&Hhj)]. rewrite Ek.
  destruct (ldivisible x (2 ^ j)) eqn:Ed; [|discriminate].
  intros X; inversion X; subst; clear X.
  pose proof (ldivisible_sound nu x (2 ^ j) ltac:(pose proof (pow2_pos j Hj); lia) Ed) as Hdiv.
  apply ares_same; auto; [|now apply lin_below_ladd].
  rewrite eval_ladd.
  pose proof (zwrap_range 64 (eval nu x) ltac:(lia)) as Rx.
  destruct (Z_lt_le_dec 64 j).
  - (* [comment removed for export] *)
    assert (H64 : (2 ^ 64 | eval nu x)).
    { eapply Z.divide_trans; [|exact Hdiv]. apply pow2_divide. lia. }
    assert (Ex : zwrap 64 (eval nu x) = 0).
    { unfold zwrap. apply Z.mod_divide; [lia|exact H64]. }
    rewrite Ex, Z.lor_0_l. apply zwrap_congr; [lia|]. destruct H64 as [q Hq]. exists (- q). lia.
  - pose proof (pow2_le j 64 ltac:(lia)) as Pj. pose proof (pow2_pos j Hj) as Pj0.
    assert (Ey : zwrap 64 (eval nu y) = eval nu y) by (apply zwrap_id; lia).
    rewrite Ey.
    assert (Hm : zwrap 64 (eval nu x) mod 2 ^ j = 0).
    { unfold zwrap. rewrite Z.mod_mod_divide by (apply pow2_divide; lia). apply Z.mod_divide; [lia|exact Hdiv]. }
    rewrite (lor_disjoint (zwrap 64 (eval nu x)) (eval nu y) j); try lia.
    (* [comment removed for export] *)
    assert (zwrap 64 (eval nu x) + eval nu y < 2 ^ 64).
    { pose proof (Z.div_mod (zwrap 64 (eval nu x)) (2 ^ j) ltac:(lia)) as E1. rewrite Hm in E1.
      assert (E2 : 2 ^ 64 = 2 ^ j * 2 ^ (64 - j)) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
      assert (zwrap 64 (eval nu x) / 2 ^ j < 2 ^ (64 - j)).
      { apply Z.div_lt_upper_bound; [lia|]. rewrite <- E2. lia. }
      nia. }
    symmetry. rewrite <- (zwrap_id 64 (zwrap 64 (eval nu x) + eval nu y)) by lia.
    symmetry. apply zwrap_add_l. lia.
Qed.

Lemma or_generic_sound A nu ea eb ua ub :
  lgamma A nu -> wval nu (Some ea) ua -> wval nu (Some eb) ub ->
  lin_below ea (vs_next A) = true -> lin_below eb (vs_next A) = true ->
  ares_sound A nu (or_generic A ea eb) (Z.lor ua ub).
Proof.
  intros HG Ha Hb Ba Bb. unfold or_generic.
  rewrite ?if_andb; destruct (inU A ea && inU A eb) eqn:EU.
  2: { (* [comment removed for export] *)
    pose proof (wval_some _ _ _ Ha) as Hua. pose proof (wval_some _ _ _ Hb) as Hub.
    destruct (bitcong_mod A ea eb) as [[[m ra] rb] ok] eqn:Ebm. destruct ok; [|apply res_top; exact HG].
    destruct (bitcong_mod_sound A nu ea eb m ra rb HG Ebm) as [j (Hj&Em&Da&Db)].
    pose proof (fresh_sym_top_sound A nu (Z.lor ua ub) HG) as FS.
    destruct (fresh_sym A) as [s A1]. destruct FS as (X1&L1&V1&S1&N1).
    assert (Eea : eval (vupd nu s (Z.lor ua ub)) ea = eval nu ea) by (apply (eval_ext_below (vs_next A)); [exact (proj1 X1)|exact Ba]).
    assert (Eeb : eval (vupd nu s (Z.lor ua ub)) eb = eval nu eb) by (apply (eval_ext_below (vs_next A)); [exact (proj1 X1)|exact Bb]).
    subst m.
    pose proof (ameet_cong_sound A1 (vupd nu s (Z.lor ua ub)) s (2 ^ j) ((Z.lor (ra mod 2 ^ j) (rb mod 2 ^ j)) mod 2 ^ j) L1
                  ltac:(rewrite V1, Hua, Hub; apply bitcong_fact; auto; exact zwrap_f_lor) S1) as (F&L&X).
    exists (vupd nu s (Z.lor ua ub)). split; [eapply aext_trans; [exact X1|exact X]|]. split; [exact L|].
    split; [rewrite eval_lsym, V1; symmetry; apply zwrap_id; destruct Ha as [R _]; destruct Hb as [R' _];
            pose proof (lor_upper ua ub 64 ltac:(lia) R R'); lia|].
    apply lin_below_lsym. rewrite ameet_cong_next. exact S1. }
  apply andb_prop in EU as [EUa EUb].
  pose proof (inU_sound A nu ea HG EUa) as HUa. pose proof (inU_sound A nu eb HG EUb) as HUb.
  pose proof (wval_some _ _ _ Ha) as Hua. pose proof (wval_some _ _ _ Hb) as Hub.
  rewrite zwrap_id in Hua by lia. rewrite zwrap_id in Hub by lia.
  pose proof (lp_bounds_sound nu (vs_store A) (lg_sat _ _ HG) ea) as Hba.
  pose proof (lp_bounds_sound nu (vs_store A) (lg_sat _ _ HG) eb) as Hbb.
  destruct (lp_bounds (vs_store A) ea) as [[la|] [ha|]]; try (apply res_top; exact HG).
  destruct (lp_bounds (vs_store A) eb) as [[lb|] [hb|]]; try (apply res_top; exact HG).
  destruct Hba as [Hla Hha]; destruct Hbb as [Hlb Hhb]; simpl in Hla, Hha, Hlb, Hhb.
  destruct (next_pow2_spec (Z.max ha hb) ltac:(lia)) as [j (Hj&Ek&Hhj)]. rewrite Ek.
  pose proof (lor_lower ua ub ltac:(lia) ltac:(lia)) as [L1 L2].
  pose proof (lor_upper ua ub j Hj ltac:(lia) ltac:(lia)) as L3.
  pose proof (pow2_le j 64) as Pj.
  assert (Hu64 : 0 <= Z.lor ua ub < 2 ^ 64).
  { destruct (Z_lt_le_dec 64 j); [|lia]. pose proof (lor_upper ua ub 64 ltac:(lia) ltac:(lia) ltac:(lia)). lia. }
  pose proof (afresh_sound A nu (Some (Z.max la lb), Some (2 ^ j - 1)) (Z.lor ua ub) HG ltac:(split; simpl; lia)) as FR.
  destruct (afresh A (Some (Z.max la lb), Some (2 ^ j - 1))) as [v A1]. destruct FR as [nu1 (X1&K1&V1)].
  assert (Eea : eval nu1 ea = eval nu ea) by (apply (eval_ext_below (vs_next A)); [exact (proj1 X1)|exact Ba]).
  assert (Eeb : eval nu1 eb = eval nu eb) by (apply (eval_ext_below (vs_next A)); [exact (proj1 X1)|exact Bb]).
  destruct (abitcong_sound A1 nu1 v ea eb Z.lor (Z.lor ua ub) K1
              ltac:(destruct v; [exact V1|exact I])
              ltac:(rewrite Eea, Eeb, <- Hua, <- Hub, !zwrap_id by lia; reflexivity)
              zwrap_f_lor) as (K2&X2&N2).
  exists nu1. split; [eapply aext_trans; [exact X1|exact X2]|]. split; [exact K2|].
  destruct v as [e|]; [|exact I]. destruct V1 as [V1 B1]. split; [rewrite V1; symmetry; apply zwrap_id; lia|].
  rewrite N2. exact B1.
Qed.

Theorem do_or_sound A nu a b ua ub :
  lgamma A nu -> wval nu a ua -> wval nu b ub -> vbelow a (vs_next A) -> vbelow b (vs_next A) ->
  ares_sound A nu (do_or A a b) (Z.lor ua ub).
Proof.
  intros HG Ha Hb Ba Bb. unfold do_or.
  destruct a as [ea|]; [|apply res_top; exact HG]. destruct b as [eb|]; [|apply res_top; exact HG].
  pose proof (wval_some _ _ _ Ha) as Hua. pose proof (wval_some _ _ _ Hb) as Hub. simpl in Ba, Bb.
  destruct Ha as [Rua _]. destruct Hb as [Rub _].
  destruct (lin_is_const eb && (zm64 (lc eb) =? 0)) eqn:E1.
  { apply andb_prop in E1 as [E1 E2]. apply Z.eqb_eq in E2. rewrite zm64_zwrap in E2.
    rewrite Hub, (eval_is_const nu eb E1), E2, Z.lor_0_r. apply ares_same; auto. }
  destruct (lin_is_const ea && (zm64 (lc ea) =? 0)) eqn:E2.
  { apply andb_prop in E2 as [E2 E3]. apply Z.eqb_eq in E3. rewrite zm64_zwrap in E3.
    rewrite Hua, (eval_is_const nu ea E2), E3, Z.lor_0_l. apply ares_same; auto. }
  destruct (lin_is_const ea && lin_is_const eb) eqn:E3.
  { apply andb_prop in E3 as [E3 E4]. apply ares_same; auto.
    rewrite eval_lconst, zm64_zwrap, zwrap_idem, zwrap_lor by lia.
    rewrite Hua, Hub, (eval_is_const nu ea E3), (eval_is_const nu eb E4). reflexivity. }
  assert (Ha' : wval nu (Some ea) ua) by (split; auto). assert (Hb' : wval nu (Some eb) ub) by (split; auto).
  destruct (sel_or A (Some ea) (Some eb)) as [r|] eqn:Es1; [eapply sel_or_sound; eauto|].
  destruct (sel_or A (Some eb) (Some ea)) as [r|] eqn:Es2.
  { rewrite Z.lor_comm. eapply sel_or_sound; eauto. }
  destruct (or_disjoint A ea eb) as [r|] eqn:Ed1; [eapply or_disjoint_sound; eauto|].
  destruct (or_disjoint A eb ea) as [r|] eqn:Ed2.
  { rewrite Z.lor_comm. eapply or_disjoint_sound; eauto. }
  apply or_generic_sound; auto; split; auto.
Qed.

Lemma res_word_same A nu e u :
  lgamma A nu -> u = zwrap 64 (eval nu e) -> lin_below e (vs_next A) = true -> res_word A nu (Some e, A) u.
Proof. intros HL HE HB. exists nu. split; [apply aext_refl|]. split; [exact HL|]. split; [exact HE|exact HB]. Qed.

Lemma xor_const_sound A nu x y ux uy r :
  lgamma A nu -> ux = zwrap 64 (eval nu x) -> uy = zwrap 64 (eval nu y) ->
  lin_below x (vs_next A) = true ->
  xor_const A x y = Some r -> res_word A nu r (Z.lxor ux uy).
Proof.
  intros HG Hx Hy Bx. unfold xor_const.
  pose proof (zwrap_range 64 (eval nu x) ltac:(lia)) as Rx. rewrite <- Hx in Rx.
  destruct (lin_is_const y) eqn:Ecy; [|discriminate].
  rewrite zm64_zwrap. rewrite (eval_is_const nu y Ecy) in Hy.
  destruct (Z.eqb_spec (zwrap 64 (lc y)) 0) as [E0|E0].
  { intros X; injection X as <-. rewrite Hy, E0, Z.lxor_0_r. apply res_word_same; auto. }
  destruct (Z.eqb_spec (zwrap 64 (lc y)) M64) as [E1|E1].
  { intros X; injection X as <-. unfold M64 in E1. rewrite Hy, E1.
    exists nu. split; [apply aext_refl|]. split; [exact HG|]. split; [|apply lin_below_lsub; [reflexivity|exact Bx]].
    rewrite lxor_allones by lia. rewrite eval_lsub, eval_lconst.
    rewrite <- (zwrap_sub_r 64) by lia. rewrite <- Hx. symmetry.
    rewrite <- (zwrap_plus_k 64 (-1 - ux) 1) by lia.
    replace (-1 - ux + 1 * 2 ^ 64) with (2 ^ 64 - 1 - ux) by lia. apply zwrap_id. lia. }
  destruct (lin_is_const x) eqn:Ecx; [|discriminate].
  intros X; injection X as <-.
  exists nu. split; [apply aext_refl|]. split; [exact HG|]. split; [|reflexivity].
  rewrite eval_lconst, zm64_zwrap, zwrap_idem, zwrap_lxor by lia.
  rewrite Hx, Hy, (eval_is_const nu x Ecx). reflexivity.
Qed.

Theorem do_xor_sound A nu a b ua ub :
  lgamma A nu -> wval nu a ua -> wval nu b ub -> vbelow a (vs_next A) -> vbelow b (vs_next A) ->
  res_word A nu (do_xor A a b) (Z.lxor ua ub).
Proof.
  intros HG Ha Hb Ba Bb. unfold do_xor.
  destruct a as [ea|]; [|apply res_top; exact HG]. destruct b as [eb|]; [|apply res_top; exact HG].
  pose proof (wval_some _ _ _ Ha) as Hua. pose proof (wval_some _ _ _ Hb) as Hub. simpl in Ba, Bb.
  destruct Ha as [Rua _]. destruct Hb as [Rub _].
  destruct (xor_const A ea eb) as [r|] eqn:E1; [eapply xor_const_sound; eauto|].
  destruct (xor_const A eb ea) as [r|] eqn:E2.
  { rewrite Z.lxor_comm. eapply xor_const_sound; eauto. }
  unfold xor_generic. destruct (lin_eqb ea eb) eqn:Ee.
  { apply lin_eqb_eq in Ee. subst eb. rewrite Hua, <- Hub, Z.lxor_nilpotent. apply res_word_same; auto. }
  rewrite ?if_andb; destruct (inU A ea && inU A eb) eqn:EU; [|apply res_top; exact HG].
  apply andb_prop in EU as [EUa EUb].
  pose proof (inU_sound A nu ea HG EUa) as HUa. pose proof (inU_sound A nu eb HG EUb) as HUb.
  rewrite zwrap_id in Hua by lia. rewrite zwrap_id in Hub by lia.
  pose proof (lp_bounds_sound nu (vs_store A) (lg_sat _ _ HG) ea) as Hba.
  pose proof (lp_bounds_sound nu (vs_store A) (lg_sat _ _ HG) eb) as Hbb.
  destruct (lp_bounds (vs_store A) ea) as [la [ha|]]; [|apply res_top; exact HG].
  destruct (lp_bounds (vs_store A) eb) as [lb [hb|]]; [|apply res_top; exact HG].
  destruct Hba as [_ Hha]; destruct Hbb as [_ Hhb]; simpl in Hha, Hhb.
  destruct (next_pow2_spec (Z.max ha hb) ltac:(lia)) as [j (Hj&Ek&Hhj)]. rewrite Ek.
  pose proof (lxor_upper ua ub j Hj ltac:(lia) ltac:(lia)) as L3.
  apply res_word_fresh; [exact HG| |split; simpl; lia].
  destruct (Z_lt_le_dec 64 j); [|pose proof (pow2_le j 64); lia].
  pose proof (lxor_upper ua ub 64 ltac:(lia) ltac:(lia) ltac:(lia)). lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma ashr_sound A nu a v k width :
  lgamma A nu -> eval nu a = v -> 0 <= v < 2 ^ width -> 0 <= k -> 0 <= width ->
  lin_below a (vs_next A) = true ->
  res_exact A nu (ashr A a k width) (v / 2 ^ k).
Proof.
  intros HG Hv Hr Hk Hw Hb. unfold ashr. pose proof (pow2_pos k Hk) as Pk.
  destruct (Z.eqb_spec k 0) as [->|Hk0].
  { apply res_exact_same; [exact HG| |exact Hb]. rewrite Hv. change (2 ^ 0) with 1. now rewrite Z.div_1_r. }
  destruct (lin_is_const a) eqn:Ec.
  { apply res_exact_same; [exact HG| |reflexivity]. rewrite eval_lconst, <- Hv, (eval_is_const nu a Ec). apply Z.shiftr_div_pow2. lia. }
  pose proof (lp_bounds_sound nu (vs_store A) (lg_sat _ _ HG) a) as Hbd. rewrite Hv in Hbd.
  apply res_exact_fresh; auto. rewrite !Z.shiftr_div_pow2 by lia.
  destruct (lp_bounds (vs_store A) a) as [lo hi]. destruct Hbd as [Hlo Hhi]. split; cbn [fst snd lo_le hi_ge] in *.
  - destruct lo as [lo|]; cbn [lo_le] in Hlo.
    + destruct (Z.ltb_spec lo 0); [apply Z.div_pos; lia|apply Z.div_le_mono; lia].
    + apply Z.div_pos; lia.
  - destruct hi as [hi|]; cbn [hi_ge] in Hhi; apply Z.div_le_mono; lia.
Qed.

Lemma ashr_signed_sound A nu a v k :
  lgamma A nu -> eval nu a = v -> - 2 ^ 63 <= v < 2 ^ 63 -> 0 <= k <= 63 ->
  lin_below a (vs_next A) = true ->
  res_exact A nu (ashr_signed A a k) (Z.shiftr v k).
Proof.
  intros HG Hv Hr Hk Hb. unfold ashr_signed. pose proof (pow2_pos k ltac:(lia)) as Pk.
  destruct (Z.eqb_spec k 0) as [->|Hk0].
  { apply res_exact_same; [exact HG| |exact Hb]. rewrite Hv, Z.shiftr_0_r. reflexivity. }
  destruct (lin_is_const a) eqn:Ec.
  { apply res_exact_same; [exact HG| |reflexivity]. rewrite eval_lconst, <- Hv, (eval_is_const nu a Ec). reflexivity. }
  pose proof (lp_bounds_sound nu (vs_store A) (lg_sat _ _ HG) a) as Hbd. rewrite Hv in Hbd.
  rewrite !Z.shiftr_div_pow2 by lia.
  destruct (lp_bounds (vs_store A) a) as [[lo|] [hi|]].
  - destruct Hbd as [Hlo Hhi]; cbn [fst snd lo_le hi_ge] in Hlo, Hhi.
    apply res_exact_fresh; auto. rewrite !Z.shiftr_div_pow2 by lia. split; cbn [fst snd lo_le hi_ge]; apply Z.div_le_mono; lia.
  - apply res_exact_fresh; auto.
    assert (E : 2 ^ 63 = 2 ^ k * 2 ^ (63 - k)) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
    split; cbn [fst snd lo_le hi_ge].
    + apply Z.div_le_lower_bound; [lia|]. nia.
    + assert (v / 2 ^ k < 2 ^ (63 - k)); [apply Z.div_lt_upper_bound; [lia|nia]|lia].
  - apply res_exact_fresh; auto.
    assert (E : 2 ^ 63 = 2 ^ k * 2 ^ (63 - k)) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
    split; cbn [fst snd lo_le hi_ge].
    + apply Z.div_le_lower_bound; [lia|]. nia.
    + assert (v / 2 ^ k < 2 ^ (63 - k)); [apply Z.div_lt_upper_bound; [lia|nia]|lia].
  - apply res_exact_fresh; auto.
    assert (E : 2 ^ 63 = 2 ^ k * 2 ^ (63 - k)) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
    split; cbn [fst snd lo_le hi_ge].
    + apply Z.div_le_lower_bound; [lia|]. nia.
    + assert (v / 2 ^ k < 2 ^ (63 - k)); [apply Z.div_lt_upper_bound; [lia|nia]|lia].
Qed.

Lemma terms_shiftr_eval nu l k : 0 <= k -> terms_divisible l (2 ^ k) = true ->
  eval_terms nu (terms_shiftr l k) * 2 ^ k = eval_terms nu l.
Proof.
  intros Hk. pose proof (pow2_pos k Hk) as Pk. induction l as [|[s c] t IH]; simpl; [lia|].
  intros H. apply andb_prop in H as [H1 H2]. apply Z.eqb_eq in H1.
  rewrite Z.mul_add_distr_r, IH by auto. rewrite Z.shiftr_div_pow2 by lia.
  pose proof (Z.div_exact c (2 ^ k) ltac:(lia)) as [_ X]. specialize (X H1). nia.
Qed.

Lemma lshiftr_eval nu e k : 0 <= k -> ldivisible e (2 ^ k) = true ->
  eval nu (lshiftr e k) = eval nu e / 2 ^ k.
Proof.
  intros Hk H. pose proof (pow2_pos k Hk) as Pk. unfold ldivisible in H. apply andb_prop in H as [H1 H2].
  apply Z.eqb_eq in H1. unfold lshiftr, eval. cbn [lc lt].
  pose proof (terms_shiftr_eval nu (lt e) k Hk H2) as E. rewrite Z.shiftr_div_pow2 by lia.
  pose proof (Z.div_exact (lc e) (2 ^ k) ltac:(lia)) as [_ X]. specialize (X H1).
  apply Z.div_unique_exact; [lia|]. nia.
Qed.

Lemma lin_below_lshiftr e k n : lin_below e n = true -> lin_below (lshiftr e k) n = true.
Proof.
  intros H. apply (proj2 (lin_below_iff _ _)). intros s Hs. apply (proj1 (lin_below_iff e n) H).
  unfold lshiftr, lsyms in Hs. simpl in Hs. unfold lsyms.
  clear H. induction (lt e) as [|[s' c] t IH]; simpl in *; auto. destruct Hs; auto.
Qed.

(* [comment removed for export] *)
Definition shift_conc (op : shop) (width : Z) (ua amt : Z) : Z :=
  if Z.eqb width 32 then
    match op with
    | SH_sll => zwrap 64 (zswrap 32 (ua * 2 ^ amt))
    | SH_srl => zwrap 64 (zswrap 32 (zwrap 32 ua / 2 ^ amt))
    | SH_sra => zwrap 64 (zswrap 32 (Z.shiftr (zswrap 32 ua) amt))
    end
  else
    match op with
    | SH_sll => zwrap 64 (ua * 2 ^ amt)
    | SH_srl => ua / 2 ^ amt
    | SH_sra => zwrap 64 (Z.shiftr (zswrap 64 ua) amt)
    end.

Lemma s32range_itv x : - 2 ^ 31 <= x < 2 ^ 31 -> in_itv x s32range.
Proof. intros. unfold s32range, TWO31. split; simpl; lia. Qed.

Lemma zswrap32_range x : - 2 ^ 31 <= zswrap 32 x < 2 ^ 31.
Proof. pose proof (zswrap_range 32 x ltac:(lia)) as H. exact H. Qed.

Lemma res_word_of_exact_wrap A nu rA x :
  res_exact A nu rA x -> res_word A nu rA (zwrap 64 x).
Proof. apply res_exact_word. Qed.

Lemma shiftr_signed_range n v k : 0 < n -> - 2 ^ (n - 1) <= v < 2 ^ (n - 1) -> 0 <= k ->
  - 2 ^ (n - 1) <= Z.shiftr v k < 2 ^ (n - 1).
Proof.
  intros Hn Hv Hk. rewrite Z.shiftr_div_pow2 by lia. pose proof (pow2_pos k Hk).
  pose proof (pow2_pos (n - 1) ltac:(lia)).
  split.
  - apply Z.div_le_lower_bound; [lia|nia].
  - apply Z.div_lt_upper_bound; [lia|nia].
Qed.

Theorem do_shift_sound A nu a kb ua ukb op width :
  lgamma A nu -> wval nu a ua -> wval nu kb ukb -> vbelow a (vs_next A) -> vbelow kb (vs_next A) ->
  (width = 32 \/ width = 64) ->
  res_word A nu (do_shift A a kb op width) (shift_conc op width ua (ukb mod width)).
Proof.
  intros HG Ha Hkb Ba Bkb Hw.
  assert (Hw0 : 0 < width) by lia.
  pose proof (Z.mod_pos_bound ukb width Hw0) as Hamt.
  destruct Ha as [Rua Hua].
  assert (S32 : forall x, in_itv (zswrap 32 x) s32range) by (intros; apply s32range_itv, zswrap32_range).
  unfold do_shift.
  set (kconst := match kb with Some e => if lin_is_const e then Some (lc e) else None | None => None end).
  assert (Hkc : forall kc, kconst = Some kc -> Z.land kc (width - 1) = ukb mod width).
  { intros kc. unfold kconst. destruct kb as [e|]; [|discriminate]. destruct (lin_is_const e) eqn:Ec; [|discriminate].
    intros X; inversion X; subst. pose proof (wval_some _ _ _ Hkb) as Hu. rewrite (eval_is_const nu e Ec) in Hu.
    rewrite Hu. unfold zwrap.
    destruct Hw as [-> | ->].
    - change (32 - 1) with (2 ^ 5 - 1). rewrite land_lowmask by lia. replace (2 ^ 5) with 32 by reflexivity.
      symmetry. apply Z.mod_mod_divide. exists (2 ^ 59). reflexivity.
    - change (64 - 1) with (2 ^ 6 - 1). rewrite land_lowmask by lia. replace (2 ^ 6) with 64 by reflexivity.
      symmetry. apply Z.mod_mod_divide. exists (2 ^ 58). reflexivity. }
  destruct kconst as [kc|] eqn:Ekc.
  - specialize (Hkc kc eq_refl). rewrite Hkc. set (k := ukb mod width) in *.
    assert (Hk : 0 <= k < width) by (unfold k; lia).
    pose proof (pow2_pos k ltac:(lia)) as Pk.
    destruct a as [ea|].
    + simpl in Ba. destruct (Z.eqb_spec width 32) as [W32|W64].
      * (* [comment removed for export] *)
        unfold shift_conc. rewrite W32, Z.eqb_refl. rewrite W32 in Hk.
        destruct op.
        -- apply res_word_of_exact_wrap.
           pose proof (asext32_sound A nu (Some (lscale (2 ^ k) ea)) (eval nu ea * 2 ^ k) HG
                         ltac:(split; [rewrite eval_lscale; lia|now apply lin_below_lscale])) as R.
           replace (zswrap 32 (ua * 2 ^ k)) with (zswrap 32 (eval nu ea * 2 ^ k)); [exact R|].
           apply zswrap_congr; [lia|]. rewrite Hua.
           destruct (zwrap_divide_self 64 (eval nu ea) ltac:(lia)) as [q Hq].
           exists (- q * 2 ^ k * 2 ^ 32). change (2 ^ 64) with (2 ^ 32 * 2 ^ 32) in Hq. nia.
        -- pose proof (azext_sound A nu (Some ea) (eval nu ea) 32 HG ltac:(lia) ltac:(split; auto)) as R1.
           destruct (azext A (Some ea) 32) as [a32 A1] eqn:Ez. destruct R1 as [nu1 (X1&L1&R1)].
           destruct a32 as [e32|]; [|pose proof (azext_some A (Some ea) 32) as [? [? E]]; rewrite Ez in E; discriminate].
           destruct R1 as [E32 B32].
           pose proof (zwrap_range 32 (eval nu ea) ltac:(lia)) as R32.
           pose proof (ashr_sound A1 nu1 e32 (zwrap 32 (eval nu ea)) k 32 L1 E32 R32 ltac:(lia) ltac:(lia) B32) as R2.
           destruct (ashr A1 e32 k 32) as [r A2] eqn:Es. destruct R2 as [nu2 (X2&L2&R2)].
           assert (Hr : match r with Some e => eval nu2 e = zwrap 32 (eval nu ea) / 2 ^ k /\ lin_below e (vs_next A2) = true | None => True end)
             by (destruct r; [exact R2|exact I]).
           pose proof (asext32_sound A2 nu2 r (zwrap 32 (eval nu ea) / 2 ^ k) L2 Hr) as R3.
           destruct (asext32 A2 r) as [r3 A3] eqn:E3. destruct R3 as [nu3 (X3&L3&R3)].
           exists nu3. split; [eapply aext_trans; [exact X1|eapply aext_trans; [exact X2|exact X3]]|].
           split; [exact L3|]. destruct r3 as [e3|]; [|exact I]. destruct R3 as [E3' B3]. split; [|exact B3].
           rewrite E3'. rewrite Hua. rewrite (zwrap_zwrap 32 64) by lia. reflexivity.
        -- pose proof (asext32_sound A nu (Some ea) (eval nu ea) HG ltac:(split; auto)) as R1.
           destruct (asext32 A (Some ea)) as [s32 A1] eqn:Ez. destruct R1 as [nu1 (X1&L1&R1)].
           destruct s32 as [e32|]; [|pose proof (asext32_some A (Some ea)) as [? [? E]]; rewrite Ez in E; discriminate].
           destruct R1 as [E32 B32].
           pose proof (zswrap32_range (eval nu ea)) as R32.
           pose proof (ashr_signed_sound A1 nu1 e32 (zswrap 32 (eval nu ea)) k L1 E32 ltac:(lia) ltac:(lia) B32) as R2.
           destruct (ashr_signed A1 e32 k) as [r A2] eqn:Es. destruct R2 as [nu2 (X2&L2&R2)].
           exists nu2. split; [eapply aext_trans; [exact X1|exact X2]|]. split; [exact L2|].
           destruct r as [e2|]; [|exact I]. destruct R2 as [E2 B2]. split; [|exact B2].
           rewrite E2, Hua, (zswrap_zwrap 32 64) by lia.
           rewrite (zswrap_id 32 (Z.shiftr _ _)); [reflexivity|lia|].
           apply (shiftr_signed_range 32); [lia|exact R32|lia].
      * (* [comment removed for export] *)
        assert (W64' : width = 64) by lia. unfold shift_conc. rewrite W64' in Hk |- *.
        change (64 =? 32) with false. cbn iota.
        destruct op.
        -- apply res_word_same; auto; [|now apply lin_below_lscale].
           rewrite eval_lscale, Hua, (Z.mul_comm (2 ^ k) (eval nu ea)). rewrite zwrap_mul_l by lia. reflexivity.
        -- destruct (lin_is_const ea) eqn:Ec.
           { apply res_word_same; auto. rewrite eval_lconst, zm64_zwrap, Hua, (eval_is_const nu ea Ec).
             rewrite Z.shiftr_div_pow2 by lia. symmetry. apply zwrap_id.
             pose proof (zwrap_range 64 (lc ea) ltac:(lia)). split; [apply Z.div_pos; lia|].
             apply Z.div_lt_upper_bound; [lia|nia]. }
           destruct (ldivisible ea (2 ^ k)) eqn:Ed.
           { pose proof (azext_sound A nu (Some (lshiftr ea k)) (eval nu ea / 2 ^ k) (64 - k) HG ltac:(lia)
                           ltac:(split; [apply lshiftr_eval; [lia|exact Ed]|now apply lin_below_lshiftr])) as R.
             destruct (azext A (Some (lshiftr ea k)) (64 - k)) as [r A1]. destruct R as [nu1 (X1&L1&R1)].
             exists nu1. split; [exact X1|]. split; [exact L1|]. destruct r as [e1|]; [|exact I].
             destruct R1 as [E1 B1]. split; [|exact B1]. rewrite E1, Hua, <- shiftr_zwrap64 by lia.
             symmetry. apply zwrap_id. pose proof (zwrap_range 64 (eval nu ea) ltac:(lia)).
             split; [apply Z.div_pos; lia|apply Z.div_lt_upper_bound; [lia|nia]]. }
           destruct (inU A ea) eqn:EU.
           { pose proof (inU_sound A nu ea HG EU) as HU.
             pose proof (ashr_sound A nu ea (eval nu ea) k 64 HG eq_refl HU ltac:(lia) ltac:(lia) Ba) as R.
             apply res_exact_word in R. rewrite Hua, (zwrap_id 64 (eval nu ea)) by lia.
             rewrite zwrap_id in R; [exact R|].
             split; [apply Z.div_pos; lia|apply Z.div_lt_upper_bound; [lia|nia]]. }
           assert (Hw1 : wval nu (Some ea) ua) by (split; auto).
           destruct (readings A (Some ea) false) as [| |rlo rhi sh] eqn:Er.
           ++ apply res_word_fresh; auto.
              ** split; [apply Z.div_pos; lia|apply Z.div_lt_upper_bound; [lia|]].
                 assert (2 ^ 64 <= 2 ^ k * 2 ^ (64 - k)) by (rewrite <- Z.pow_add_r by lia; apply Z.pow_le_mono_r; lia). nia.
              ** split; cbn [fst snd lo_le hi_ge]; [apply Z.div_pos; lia|].
                 assert (ua / 2 ^ k < 2 ^ (64 - k)); [|lia].
                 apply Z.div_lt_upper_bound; [lia|]. rewrite <- Z.pow_add_r by lia. replace (k + (64 - k)) with 64 by lia. lia.
           ++ exfalso. eapply readings_not_bot; eauto.
           ++ destruct (readings_sound A nu (Some ea) ua false rlo rhi sh HG Hw1 Er) as [ea' (Eea&Rd&Bd)].
              inversion Eea; subst ea'; clear Eea. unfold rdg in Rd. cbn iota in Rd.
              apply res_word_fresh; auto.
              ** split; [apply Z.div_pos; lia|apply Z.div_lt_upper_bound; [lia|]].
                 assert (2 ^ 64 <= 2 ^ k * 2 ^ (64 - k)) by (rewrite <- Z.pow_add_r by lia; apply Z.pow_le_mono_r; lia). nia.
              ** rewrite !Z.shiftr_div_pow2 by lia. split; cbn [fst snd lo_le hi_ge]; apply Z.div_le_mono; lia.
        -- (* [comment removed for export] *)
           destruct (lin_is_const ea) eqn:Ec.
           { apply res_word_same; auto. rewrite eval_lconst. f_equal. rewrite Hua, (eval_is_const nu ea Ec).
             rewrite zm64_zwrap. f_equal. unfold zswrap, TWO63, TWO64.
             pose proof (zwrap_range 64 (lc ea) ltac:(lia)) as Rr. unfold zwrap in *.
             change (2 ^ (64 - 1)) with (2 ^ 63).
             destruct (Z.leb_spec (2 ^ 63) (lc ea mod 2 ^ 64)).
             - rewrite <- (Z.mod_add _ (-1)) by lia. rewrite Z.mod_small by lia. lia.
             - rewrite Z.mod_small by lia. lia. }
           set (try_div := if ldivisible ea (2 ^ k) then _ else None).
           assert (TD : forall r, try_div = Some r -> res_word A nu r (zwrap 64 (Z.shiftr (zswrap 64 ua) k))).
           { intros r. unfold try_div. destruct (ldivisible ea (2 ^ k)) eqn:Ed; [|discriminate].
             pose proof (lshiftr_eval nu ea k ltac:(lia) Ed) as Eq.
             pose proof (lp_bounds_sound nu (vs_store A) (lg_sat _ _ HG) (lshiftr ea k)) as Hbd.
             destruct (lp_bounds (vs_store A) (lshiftr ea k)) as [[lo|] [hi|]]; try discriminate.
             destruct Hbd as [Hlo Hhi]; cbn [fst snd lo_le hi_ge] in Hlo, Hhi.
             destruct (Z.leb (- 2 ^ (63 - k)) lo && Z.ltb hi (2 ^ (63 - k)) && negb (itv_empty (Some lo, Some hi))) eqn:Et; [|discriminate].
             intros X; injection X as <-.
             apply andb_prop in Et as [Et _]. apply andb_prop in Et as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
             apply res_word_same; auto; [|now apply lin_below_lshiftr].
             rewrite Eq in *. rewrite Hua. f_equal.
             assert (E63 : 2 ^ 63 = 2 ^ k * 2 ^ (63 - k)) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
             pose proof (ldivisible_sound nu ea (2 ^ k) ltac:(lia) Ed) as [q Hq].
             assert (Hqe : eval nu ea / 2 ^ k = q) by (rewrite Hq; apply Z.div_mul; lia).
             rewrite Hqe in *.
             assert (Hr64 : - 2 ^ 63 <= eval nu ea < 2 ^ 63) by nia.
             rewrite zswrap_zwrap_id by (simpl; lia). rewrite Z.shiftr_div_pow2 by lia. rewrite Hq. rewrite Z.div_mul by lia. reflexivity. }
           destruct try_div as [r|] eqn:Etd; [now apply TD|]. clear TD Etd.
           set (sign63 := if Z.eqb k 63 && ldivisible ea (2 ^ k) then _ else None).
           assert (SG : forall r, sign63 = Some r -> res_word A nu r (zwrap 64 (Z.shiftr (zswrap 64 ua) k))).
           { intros r. unfold sign63. destruct (Z.eqb_spec k 63) as [K63|]; [|discriminate].
             destruct (ldivisible ea (2 ^ k)) eqn:Ed; [|discriminate]. cbn [andb].
             pose proof (lshiftr_eval nu ea k ltac:(lia) Ed) as Eq.
             pose proof (ldivisible_sound nu ea (2 ^ k) ltac:(lia) Ed) as [q Hq].
             assert (Hqe : eval nu (lshiftr ea k) = q) by (rewrite Eq, Hq; apply Z.div_mul; lia).
             assert (Wq : wval nu (Some (lshiftr ea k)) (zwrap 64 q)).
             { split; [apply zwrap_range; lia|]. rewrite Hqe. reflexivity. }
             pose proof (and_const_sound A nu (Some (lshiftr ea k)) (zwrap 64 q) 1 HG Wq ltac:(now apply lin_below_lshiftr)) as R.
             destruct (and_const A (Some (lshiftr ea k)) 1) as [[r0|] A1| ]; try discriminate.
             intros X; injection X as <-. destruct R as [nu1 (X1&L1&V1&B1)].
             exists nu1. split; [exact X1|]. split; [exact L1|]. split; [|now apply lin_below_lneg].
             rewrite eval_lneg, <- (zwrap_neg 64 (eval nu1 r0)), <- V1 by lia.
             (* [comment removed for export] *)
             rewrite (zwrap_id 64 1) by lia.
             replace (Z.land (zwrap 64 q) 1) with (Z.land (zwrap 64 q) (Z.ones 1)) by reflexivity.
             rewrite Z.land_ones by lia. change (2 ^ 1) with 2.
             assert (Et : zwrap 64 q mod 2 = q mod 2).
             { unfold zwrap. rewrite Z.mod_mod_divide; [reflexivity|]. exists (2 ^ 63). reflexivity. }
             rewrite Et.
             assert (Eua : ua = 2 ^ 63 * (q mod 2)).
             { rewrite Hua, Hq, K63. unfold zwrap. change (2 ^ 64) with (2 ^ 63 * 2).
               rewrite (Z.mul_comm q (2 ^ 63)), Z.mul_mod_distr_l by lia. reflexivity. }
             f_equal. rewrite Eua, K63. pose proof (Z.mod_pos_bound q 2 ltac:(lia)) as Hm2.
             unfold zswrap. change (2 ^ (64 - 1)) with (2 ^ 63). rewrite Z.shiftr_div_pow2 by lia.
             destruct (Z.eq_dec (q mod 2) 0) as [E0|E1].
             - rewrite E0. reflexivity.
             - assert (E1' : q mod 2 = 1) by lia. rewrite E1'. reflexivity. }
           destruct sign63 as [r|] eqn:Esg; [now apply SG|]. clear SG Esg.
           destruct (inS A ea) eqn:ES.
           { pose proof (inS_sound A nu ea HG ES) as HS.
             pose proof (ashr_signed_sound A nu ea (eval nu ea) k HG eq_refl HS ltac:(lia) Ba) as R.
             apply res_exact_word in R. rewrite Hua, zswrap_zwrap_id by (simpl; lia). exact R. }
           apply res_word_of_exact_wrap. apply res_exact_fresh; auto.
           pose proof (zswrap_range 64 ua ltac:(lia)) as Rs. change (2 ^ (64 - 1)) with (2 ^ 63) in Rs.
           pose proof (shiftr_signed_range 64 (zswrap 64 ua) k ltac:(lia) Rs ltac:(lia)) as Rr. change (2 ^ (64 - 1)) with (2 ^ 63) in Rr.
           assert (E63 : 2 ^ 63 = 2 ^ k * 2 ^ (63 - k)) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
           rewrite Z.shiftr_div_pow2 in * by lia.
           split; cbn [fst snd lo_le hi_ge].
           ** apply Z.div_le_lower_bound; [lia|nia].
           ** assert (zswrap 64 ua / 2 ^ k < 2 ^ (63 - k)); [apply Z.div_lt_upper_bound; [lia|nia]|lia].
    + (* [comment removed for export] *)
      destruct op.
      * destruct (Z.eqb_spec width 64) as [W|W].
        -- apply res_top; exact HG.
        -- assert (W32 : width = 32) by lia. unfold shift_conc. rewrite W32, Z.eqb_refl. apply res_word_of_exact_wrap. apply res_exact_fresh; auto.
      * destruct (Z.eqb_spec width 64) as [W|W].
        -- unfold shift_conc. rewrite W. change (64 =? 32) with false. cbn iota. rewrite W in Hk.
           apply res_word_fresh; auto.
           ++ split; [apply Z.div_pos; lia|apply Z.div_lt_upper_bound; [lia|]].
              assert (2 ^ 64 <= 2 ^ k * 2 ^ (64 - k)) by (rewrite <- Z.pow_add_r by lia; apply Z.pow_le_mono_r; lia). nia.
           ++ split; cbn [fst snd lo_le hi_ge]; [apply Z.div_pos; lia|].
              assert (ua / 2 ^ k < 2 ^ (64 - k)); [|lia].
              apply Z.div_lt_upper_bound; [lia|]. rewrite <- Z.pow_add_r by lia. replace (k + (64 - k)) with 64 by lia. lia.
        -- assert (W32 : width = 32) by lia. unfold shift_conc. rewrite W32, Z.eqb_refl. rewrite W32 in Hk.
           apply res_word_of_exact_wrap.
           destruct (Z.ltb_spec 0 k).
           ++ apply res_exact_fresh; auto.
              pose proof (zwrap_range 32 ua ltac:(lia)) as R32.
              assert (Hq : 0 <= zwrap 32 ua / 2 ^ k < 2 ^ (32 - k)).
              { split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|].
                rewrite <- Z.pow_add_r by lia. replace (k + (32 - k)) with 32 by lia. lia. }
              assert (2 ^ (32 - k) <= 2 ^ 31) by (apply Z.pow_le_mono_r; lia).
              rewrite zswrap_id by (simpl; lia). split; cbn [fst snd lo_le hi_ge]; lia.
           ++ apply res_exact_fresh; auto.
      * unfold shift_conc. destruct (Z.eqb_spec width 32) as [W|W].
        -- rewrite W in Hk |- *. apply res_word_of_exact_wrap. apply res_exact_fresh; auto.
           pose proof (shiftr_signed_range 32 (zswrap 32 ua) k ltac:(lia) (zswrap32_range ua) ltac:(lia)) as Rr.
           change (2 ^ (32 - 1)) with (2 ^ 31) in Rr. rewrite (zswrap_id 32) by (simpl; lia).
           assert (E31 : 2 ^ 31 = 2 ^ k * 2 ^ (31 - k)) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
           pose proof (zswrap32_range ua).
           rewrite Z.shiftr_div_pow2 in * by lia. replace (32 - 1 - k) with (31 - k) by lia.
           split; cbn [fst snd lo_le hi_ge].
           ++ apply Z.div_le_lower_bound; [lia|nia].
           ++ assert (zswrap 32 ua / 2 ^ k < 2 ^ (31 - k)); [apply Z.div_lt_upper_bound; [lia|nia]|lia].
        -- assert (W64 : width = 64) by lia. rewrite W64 in Hk |- *.
           apply res_word_of_exact_wrap. apply res_exact_fresh; auto.
           pose proof (zswrap_range 64 ua ltac:(lia)) as Rs. change (2 ^ (64 - 1)) with (2 ^ 63) in Rs.
           pose proof (shiftr_signed_range 64 (zswrap 64 ua) k ltac:(lia) Rs ltac:(lia)) as Rr. change (2 ^ (64 - 1)) with (2 ^ 63) in Rr.
           assert (E63 : 2 ^ 63 = 2 ^ k * 2 ^ (63 - k)) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
           rewrite Z.shiftr_div_pow2 in * by lia. replace (64 - 1 - k) with (63 - k) by lia.
           split; cbn [fst snd lo_le hi_ge].
           ++ apply Z.div_le_lower_bound; [lia|nia].
           ++ assert (zswrap 64 ua / 2 ^ k < 2 ^ (63 - k)); [apply Z.div_lt_upper_bound; [lia|nia]|lia].
  - (* [comment removed for export] *)
    destruct op; try (destruct (Z.eqb_spec width 64) as [W|W];
                      [apply res_top; exact HG
                      |assert (W32 : width = 32) by lia; unfold shift_conc; rewrite W32, Z.eqb_refl;
                       apply res_word_of_exact_wrap; apply res_exact_fresh; auto]).
    destruct a as [ea|].
    + destruct (inU A ea) eqn:EU.
      * pose proof (inU_sound A nu ea HG EU) as HU. rewrite zwrap_id in Hua by lia.
        pose proof (lp_bounds_sound nu (vs_store A) (lg_sat _ _ HG) ea) as Hbd.
        destruct (lp_bounds (vs_store A) ea) as [lo [h|]]; cbn [snd].
        -- destruct Hbd as [_ Hh]; cbn [snd hi_ge] in Hh.
           pose proof (pow2_pos (ukb mod width) ltac:(lia)) as Pk.
           assert (Hdiv : 0 <= ua / 2 ^ (ukb mod width) <= ua).
           { split; [apply Z.div_pos; lia|]. apply Z.div_le_upper_bound; [lia|nia]. }
           destruct (Z.eqb width 64 || Z.ltb h TWO31) eqn:Eo.
           ++ unfold shift_conc. destruct (Z.eqb_spec width 32) as [W|W].
              ** rewrite W in Eo. cbn [Z.eqb Pos.eqb orb] in Eo. apply Z.ltb_lt in Eo. unfold TWO31 in Eo.
                 apply res_word_of_exact_wrap. apply res_exact_fresh; auto.
                 rewrite (zwrap_id 32) by lia.
                 assert (Hq : 0 <= ua / 2 ^ (ukb mod width) <= ua) by exact Hdiv.
                 rewrite (zswrap_id 32) by (simpl; lia). split; cbn [fst snd lo_le hi_ge]; lia.
              ** apply res_word_fresh; auto; [lia|]. split; cbn [fst snd lo_le hi_ge]; lia.
           ++ apply orb_false_iff in Eo as [Eo _]. destruct (Z.eqb_spec width 64); [discriminate|].
              assert (W32 : width = 32) by lia. unfold shift_conc. rewrite W32, Z.eqb_refl.
              apply res_word_of_exact_wrap. apply res_exact_fresh; auto.
        -- destruct (Z.eqb_spec width 64) as [W|W]; [apply res_top; exact HG|].
           assert (W32 : width = 32) by lia. unfold shift_conc. rewrite W32, Z.eqb_refl.
           apply res_word_of_exact_wrap. apply res_exact_fresh; auto.
      * destruct (Z.eqb_spec width 64) as [W|W]; [apply res_top; exact HG|].
        assert (W32 : width = 32) by lia. unfold shift_conc. rewrite W32, Z.eqb_refl.
        apply res_word_of_exact_wrap. apply res_exact_fresh; auto.
    + destruct (Z.eqb_spec width 64) as [W|W]; [apply res_top; exact HG|].
      assert (W32 : width = 32) by lia. unfold shift_conc. rewrite W32, Z.eqb_refl.
      apply res_word_of_exact_wrap. apply res_exact_fresh; auto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Theorem do_slt_sound A nu a b ua ub signed :
  lgamma A nu -> wval nu a ua -> wval nu b ub -> vbelow a (vs_next A) -> vbelow b (vs_next A) ->
  res_word A nu (do_slt A a b signed) (if Z.ltb (rdg signed ua) (rdg signed ub) then 1 else 0).
Proof.
  intros HG Ha Hb Ba Bb. unfold do_slt.
  destruct (cmp_lt A a b signed) as [r|] eqn:Ec.
  { rewrite <- (cmp_lt_sound A nu a b ua ub signed r HG Ha Hb Ec). destruct r; apply res_word_same; auto. }
  set (bv := if Z.ltb (rdg signed ua) (rdg signed ub) then 1 else 0).
  assert (Hbv : in_itv bv (Some 0, Some 1)) by (unfold bv; destruct (_ <? _); split; simpl; lia).
  pose proof (fresh_sym_box_sound A nu (Some 0, Some 1) bv HG Hbv) as FS.
  destruct (fresh_sym A) as [bsym A1] eqn:Efs. destruct FS as (X2&L2&V2&S2&N2).
  set (A2 := asetbox A1 bsym (Some 0, Some 1)) in *. set (nu2 := vupd nu bsym bv) in *.
  assert (BASE : res_word A nu (Some (lsym bsym), A2) (if rdg signed ua <? rdg signed ub then 1 else 0)).
  { exists nu2. split; [exact X2|]. split; [exact L2|]. split; [|apply lin_below_lsym; exact S2].
    rewrite eval_lsym, V2. unfold bv. destruct (_ <? _); reflexivity. }
  destruct a as [ea|]; [|exact BASE]. destruct b as [eb|]; [|exact BASE].
  simpl in Ba, Bb.
  exists nu2. split; [|split].
  - eapply aext_trans; [exact X2|]. apply aext_keep; [reflexivity|apply same_shape_set_conddef].
  - destruct L2 as (HS&HC&HM&HV&(B0&B1&B2&B3&B4&(C1&C2&C3))).
    assert (Exa : eval nu2 ea = eval nu ea) by (apply (eval_ext_below (vs_next A)); [apply X2|exact Ba]).
    assert (Exb : eval nu2 eb = eval nu eb) by (apply (eval_ext_below (vs_next A)); [apply X2|exact Bb]).
    split; [exact HS|]. split.
    { intros b' k x y Hg. simpl in Hg. rewrite pm_get_set in Hg. destruct (Pos.eqb_spec b' bsym).
      - inversion Hg; subst. rewrite V2. unfold bv. rewrite Exa, Exb, <- wcond_cond_holds.
        rewrite <- (wval_some _ _ _ Ha), <- (wval_some _ _ _ Hb). unfold rdg. destruct signed; reflexivity.
      - exact (HC _ _ _ _ Hg). }
    split; [exact HM|]. split; [exact HV|]. split; [exact B0|]. split; [exact B1|]. split; [exact B2|].
    split; [exact B3|]. split; [exact B4|]. split; [|split; [exact C2|exact C3]].
    intros b' k x y Hg. simpl in Hg. rewrite pm_get_set in Hg. destruct (Pos.eqb_spec b' bsym).
    + inversion Hg; subst. simpl. split; [exact S2|].
      destruct X2 as (_&HH&_). split; eapply lin_below_mono; eauto.
    + exact (C1 _ _ _ _ Hg).
  - simpl. split; [|apply lin_below_lsym; exact S2]. rewrite eval_lsym, V2. unfold bv. destruct (_ <? _); reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition muldiv_conc (op : mop) (ua ub : Z) : Z :=
  match op with
  | MO_mul => zwrap 64 (ua * ub)
  | MO_mulhu => ua * ub / 2 ^ 64
  | MO_divu => if Z.eqb ub 0 then 2 ^ 64 - 1 else ua / ub
  | MO_remu => if Z.eqb ub 0 then ua else ua mod ub
  | MO_div => zwrap 64 (if Z.eqb ub 0 then -1 else Z.quot (zswrap 64 ua) (zswrap 64 ub))
  | MO_rem => zwrap 64 (if Z.eqb ub 0 then zswrap 64 ua else Z.rem (zswrap 64 ua) (zswrap 64 ub))
  | _ => 0
  end.

Lemma mul_interval_bound x y la ha lb hb :
  la <= x <= ha -> lb <= y <= hb ->
  Z.min (Z.min (la * lb) (la * hb)) (Z.min (ha * lb) (ha * hb)) <= x * y <=
  Z.max (Z.max (la * lb) (la * hb)) (Z.max (ha * lb) (ha * hb)).
Proof.
  intros Hx Hy.
  assert (H1 : Z.min (la * y) (ha * y) <= x * y <= Z.max (la * y) (ha * y)).
  { destruct (Z_lt_le_dec y 0); [split; [apply Z.le_trans with (ha * y); [apply Z.le_min_r|nia] | apply Z.le_trans with (la * y); [nia|apply Z.le_max_l]]
                                 |split; [apply Z.le_trans with (la * y); [apply Z.le_min_l|nia] | apply Z.le_trans with (ha * y); [nia|apply Z.le_max_r]]]. }
  assert (H2 : forall c, Z.min (c * lb) (c * hb) <= c * y <= Z.max (c * lb) (c * hb)).
  { intros c. destruct (Z_lt_le_dec c 0); [split; [apply Z.le_trans with (c * hb); [apply Z.le_min_r|nia] | apply Z.le_trans with (c * lb); [nia|apply Z.le_max_l]]
                                         |split; [apply Z.le_trans with (c * lb); [apply Z.le_min_l|nia] | apply Z.le_trans with (c * hb); [nia|apply Z.le_max_r]]]. }
  pose proof (H2 la) as Hla. pose proof (H2 ha) as Hha. lia.
Qed.

Theorem do_muldiv_sound A nu op a b ua ub width :
  lgamma A nu -> wval nu a ua -> wval nu b ub -> vbelow a (vs_next A) -> vbelow b (vs_next A) ->
  match op with MO_mulh | MO_mulhsu => False | _ => True end ->
  res_word A nu (do_muldiv A op a b width) (muldiv_conc op ua ub).
Proof.
  intros HG Ha Hb Ba Bb Hop. unfold do_muldiv.
  destruct Ha as [Rua Hua]. destruct Hb as [Rub Hub].
  destruct op; try contradiction; cbn [muldiv_conc].
  - (* [comment removed for export] *)
    destruct a as [ea|]; [|apply res_top; exact HG]. destruct b as [eb|]; [|apply res_top; exact HG]. simpl in Ba, Bb.
    assert (Hprod : zwrap 64 (ua * ub) = zwrap 64 (eval nu ea * eval nu eb)).
    { rewrite Hua, Hub. apply zwrap_mul. lia. }
    rewrite Hprod.
    destruct (lin_is_const ea) eqn:Eca.
    { apply res_word_same; auto; [|now apply lin_below_lscale]. rewrite eval_lscale, (eval_is_const nu ea Eca). reflexivity. }
    destruct (lin_is_const eb) eqn:Ecb.
    { apply res_word_same; auto; [|now apply lin_below_lscale]. rewrite eval_lscale, (eval_is_const nu eb Ecb). f_equal. lia. }
    pose proof (lp_bounds_sound nu (vs_store A) (lg_sat _ _ HG) ea) as Hba.
    pose proof (lp_bounds_sound nu (vs_store A) (lg_sat _ _ HG) eb) as Hbb.
    destruct (lp_bounds (vs_store A) ea) as [[la|] [ha|]]; try (apply res_top; exact HG).
    destruct (lp_bounds (vs_store A) eb) as [[lb|] [hb|]]; try (apply res_top; exact HG).
    destruct Hba as [Hla Hha]; destruct Hbb as [Hlb Hhb]; cbn [fst snd lo_le hi_ge] in Hla, Hha, Hlb, Hhb.
    apply res_word_of_exact_wrap. apply res_exact_fresh; auto.
    pose proof (mul_interval_bound (eval nu ea) (eval nu eb) la ha lb hb ltac:(lia) ltac:(lia)) as HB.
    split; cbn [fst snd lo_le hi_ge]; lia.
  - (* [comment removed for export] *)
    destruct a as [ea|]; [|apply res_top; exact HG]. destruct b as [eb|]; [|apply res_top; exact HG].
    rewrite ?if_andb; destruct (inU A ea && inU A eb) eqn:EU; [|apply res_top; exact HG]. apply andb_prop in EU as [EUa EUb].
    pose proof (inU_sound A nu ea HG EUa) as HUa. pose proof (inU_sound A nu eb HG EUb) as HUb.
    rewrite zwrap_id in Hua by lia. rewrite zwrap_id in Hub by lia.
    pose proof (bnd_sound A nu ea HG) as Hba. pose proof (bnd_sound A nu eb HG) as Hbb.
    destruct (bnd A ea) as [[la|] [ha|]]; try (apply res_top; exact HG).
    destruct (bnd A eb) as [[lb|] [hb|]]; try (apply res_top; exact HG).
    destruct Hba as [Hla Hha]; destruct Hbb as [Hlb Hhb]; cbn [fst snd lo_le hi_ge] in Hla, Hha, Hlb, Hhb.
    rewrite !Z.shiftr_div_pow2 by lia.
    assert (Hprod : 0 <= ua * ub < 2 ^ 64 * 2 ^ 64).
    { split; [nia|]. apply Z.mul_lt_mono_nonneg; lia. }
    apply res_word_fresh; auto.
    + split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; lia.
    + split; cbn [fst snd lo_le hi_ge]; apply Z.div_le_mono; try lia.
      * rewrite Hua, Hub. apply Z.mul_le_mono_nonneg; lia.
      * rewrite Hua, Hub. apply Z.mul_le_mono_nonneg; lia.
  - (* [comment removed for export] *)
    destruct a as [ea|]; [|apply res_top; exact HG]. destruct b as [eb|]; [|apply res_top; exact HG].
    rewrite ?if_andb; destruct (inS A ea && inS A eb) eqn:ES; [|apply res_top; exact HG]. apply andb_prop in ES as [ESa ESb].
    pose proof (inS_sound A nu ea HG ESa) as HSa. pose proof (inS_sound A nu eb HG ESb) as HSb.
    pose proof (bnd_sound A nu ea HG) as Hba. pose proof (bnd_sound A nu eb HG) as Hbb.
    destruct (bnd A ea) as [[la|] [ha|]]; try (apply res_top; exact HG).
    destruct (bnd A eb) as [[lb|] [hb|]]; try (apply res_top; exact HG).
    destruct Hba as [Hla Hha]; destruct Hbb as [Hlb Hhb]; cbn [fst snd lo_le hi_ge] in Hla, Hha, Hlb, Hhb.
    destruct (Z.leb 0 la && Z.leb 1 lb) eqn:El; [|apply res_top; exact HG]. apply andb_prop in El as [El1 El2].
    apply Z.leb_le in El1. apply Z.leb_le in El2.
    rewrite Hua, Hub, !zswrap_zwrap_id by (simpl; lia).
    rewrite (zwrap_id 64 (eval nu eb)) by lia.
    destruct (Z.eqb_spec (eval nu eb) 0); [lia|].
    rewrite Z.quot_div_nonneg by lia.
    destruct (lin_is_const ea && lin_is_const eb) eqn:Ec.
    + apply andb_prop in Ec as [Ec1 Ec2]. apply res_word_same; auto. rewrite eval_lconst.
      rewrite <- (eval_is_const nu ea Ec1), <- (eval_is_const nu eb Ec2). reflexivity.
    + apply res_word_of_exact_wrap. apply res_exact_fresh; auto. split; cbn [fst snd lo_le hi_ge].
      * apply Z.le_trans with (eval nu ea / hb); [apply Z.div_le_mono; lia|apply Z.div_le_compat_l; lia].
      * apply Z.le_trans with (eval nu ea / lb); [apply Z.div_le_compat_l; lia|apply Z.div_le_mono; lia].
  - (* [comment removed for export] *)
    destruct a as [ea|]; [|destruct b; apply res_top; exact HG]. destruct b as [eb|]; [|apply res_top; exact HG].
    rewrite ?if_andb; destruct (inU A ea && inU A eb) eqn:EU; [|apply res_top; exact HG]. apply andb_prop in EU as [EUa EUb].
    pose proof (inU_sound A nu ea HG EUa) as HUa. pose proof (inU_sound A nu eb HG EUb) as HUb.
    rewrite zwrap_id in Hua by lia. rewrite zwrap_id in Hub by lia.
    pose proof (bnd_sound A nu ea HG) as Hba. pose proof (bnd_sound A nu eb HG) as Hbb.
    destruct (bnd A ea) as [[la|] [ha|]]; try (apply res_top; exact HG).
    destruct (bnd A eb) as [[lb|] [hb|]]; try (apply res_top; exact HG).
    destruct Hba as [Hla Hha]; destruct Hbb as [Hlb Hhb]; cbn [fst snd lo_le hi_ge] in Hla, Hha, Hlb, Hhb.
    destruct (Z.leb_spec 1 lb); [|apply res_top; exact HG].
    rewrite Hua, Hub. destruct (Z.eqb_spec (eval nu eb) 0); [lia|].
    destruct (lin_is_const ea && lin_is_const eb) eqn:Ec.
    + apply andb_prop in Ec as [Ec1 Ec2]. apply res_word_same; auto. rewrite eval_lconst.
      rewrite <- (eval_is_const nu ea Ec1), <- (eval_is_const nu eb Ec2). symmetry. apply zwrap_id.
      split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|nia].
    + apply res_word_fresh; auto.
      * split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|nia].
      * split; cbn [fst snd lo_le hi_ge].
        -- apply Z.le_trans with (eval nu ea / hb); [apply Z.div_le_mono; lia|apply Z.div_le_compat_l; lia].
        -- apply Z.le_trans with (eval nu ea / lb); [apply Z.div_le_compat_l; lia|apply Z.div_le_mono; lia].
  - (* [comment removed for export] *)
    destruct a as [ea|]; [|apply res_top; exact HG]. destruct b as [eb|]; [|apply res_top; exact HG].
    rewrite ?if_andb; destruct (inS A ea && inS A eb) eqn:ES; [|apply res_top; exact HG]. apply andb_prop in ES as [ESa ESb].
    pose proof (inS_sound A nu ea HG ESa) as HSa. pose proof (inS_sound A nu eb HG ESb) as HSb.
    pose proof (bnd_sound A nu ea HG) as Hba. pose proof (bnd_sound A nu eb HG) as Hbb.
    destruct (bnd A ea) as [[la|] [ha|]]; try (apply res_top; exact HG).
    destruct (bnd A eb) as [[lb|] [hb|]]; try (apply res_top; exact HG).
    destruct Hba as [Hla Hha]; destruct Hbb as [Hlb Hhb]; cbn [fst snd lo_le hi_ge] in Hla, Hha, Hlb, Hhb.
    destruct (Z.leb 0 la && Z.leb 1 lb) eqn:El; [|apply res_top; exact HG]. apply andb_prop in El as [El1 El2].
    apply Z.leb_le in El1. apply Z.leb_le in El2.
    rewrite Hua, Hub, !zswrap_zwrap_id by (simpl; lia).
    rewrite (zwrap_id 64 (eval nu eb)) by lia.
    destruct (Z.eqb_spec (eval nu eb) 0); [lia|].
    rewrite Z.rem_mod_nonneg by lia.
    pose proof (Z.mod_pos_bound (eval nu ea) (eval nu eb) ltac:(lia)) as Hm.
    pose proof (Z.mod_le (eval nu ea) (eval nu eb) ltac:(lia) ltac:(lia)) as Hm2.
    destruct (lin_is_const ea && lin_is_const eb) eqn:Ec.
    + apply andb_prop in Ec as [Ec1 Ec2]. apply res_word_same; auto. rewrite eval_lconst.
      rewrite <- (eval_is_const nu ea Ec1), <- (eval_is_const nu eb Ec2). reflexivity.
    + apply res_word_of_exact_wrap. apply res_exact_fresh; auto. split; cbn [fst snd lo_le hi_ge]; [lia|].
      apply Z.min_glb; lia.
  - (* [comment removed for export] *)
    destruct a as [ea|].
    + destruct b as [eb|]; [|apply res_top; exact HG].
      rewrite ?if_andb; destruct (inU A ea && inU A eb) eqn:EU; [|apply res_top; exact HG]. apply andb_prop in EU as [EUa EUb].
      pose proof (inU_sound A nu ea HG EUa) as HUa. pose proof (inU_sound A nu eb HG EUb) as HUb.
      rewrite zwrap_id in Hua by lia. rewrite zwrap_id in Hub by lia. simpl in Ba, Bb.
      pose proof (bnd_sound A nu ea HG) as Hba. pose proof (bnd_sound A nu eb HG) as Hbb.
      destruct (bnd A ea) as [[la|] [ha|]]; try (apply res_top; exact HG).
      destruct (bnd A eb) as [[lb|] [hb|]]; try (apply res_top; exact HG).
      destruct Hba as [Hla Hha]; destruct Hbb as [Hlb Hhb]; cbn [fst snd lo_le hi_ge] in Hla, Hha, Hlb, Hhb.
      rewrite Hua, Hub.
      destruct (Z.leb_spec 1 lb).
      * destruct (Z.eqb_spec (eval nu eb) 0); [lia|].
        pose proof (Z.mod_pos_bound (eval nu ea) (eval nu eb) ltac:(lia)) as Hm.
        pose proof (Z.mod_le (eval nu ea) (eval nu eb) ltac:(lia) ltac:(lia)) as Hm2.
        destruct (lin_is_const ea && lin_is_const eb) eqn:Ec.
        { apply andb_prop in Ec as [Ec1 Ec2]. apply res_word_same; auto. rewrite eval_lconst.
          rewrite <- (eval_is_const nu ea Ec1), <- (eval_is_const nu eb Ec2). symmetry. apply zwrap_id. lia. }
        destruct (Z.ltb_spec ha lb).
        { apply res_word_same; auto. rewrite Z.mod_small by lia. symmetry. apply zwrap_id. lia. }
        set (rv := eval nu ea mod eval nu eb).
        assert (Hrv : in_itv rv (Some 0, Some (Z.min ha (hb - 1)))) by (split; cbn [fst snd lo_le hi_ge]; [lia|apply Z.min_glb; lia]).
        pose proof (fresh_sym_box_sound A nu (Some 0, Some (Z.min ha (hb - 1))) rv HG Hrv) as FS.
        destruct (fresh_sym A) as [r A1] eqn:Efs. destruct FS as (X2&L2&V2&S2&N2).
        set (A2 := asetbox A1 r (Some 0, Some (Z.min ha (hb - 1)))) in *. set (nu2 := vupd nu r rv) in *.
        assert (Exa : eval nu2 ea = eval nu ea) by (apply (eval_ext_below (vs_next A)); [apply X2|exact Ba]).
        assert (Exb : eval nu2 eb = eval nu eb) by (apply (eval_ext_below (vs_next A)); [apply X2|exact Bb]).
        destruct X2 as (X2a&X2b&X2c).
        assert (Br : lin_below (lsym r) (vs_next A2) = true) by (apply lin_below_lsym; exact S2).
        assert (Bea : lin_below ea (vs_next A2) = true) by (eapply lin_below_mono; [exact X2b|exact Ba]).
        assert (Beb : lin_below eb (vs_next A2) = true) by (eapply lin_below_mono; [exact X2b|exact Bb]).
        set (A3 := if lin_is_const eb then A2 else snd (aassume A2 (laddc (lsub (lsym r) eb) 1))).
        assert (L3 : lgamma A3 nu2 /\ aext A2 A3 nu2 nu2 /\ vs_next A3 = vs_next A2).
        { unfold A3. destruct (lin_is_const eb). { split; [exact L2|]. split; [apply aext_refl|reflexivity]. }
          pose proof (aassume_sound A2 nu2 (laddc (lsub (lsym r) eb) 1) L2
                        ltac:(rewrite eval_laddc, eval_lsub, eval_lsym, V2, Exb; unfold rv; lia)
                        ltac:(apply lin_below_laddc; now apply lin_below_lsub)) as (F&L&X).
          split; [exact L|]. split; [exact X|apply aassume_next]. }
        destruct L3 as (L3a&X3&N3).
        set (A4 := if lin_is_const ea then A3 else snd (aassume A3 (lsub (lsym r) ea))).
        assert (L4 : lgamma A4 nu2 /\ aext A3 A4 nu2 nu2 /\ vs_next A4 = vs_next A3).
        { unfold A4. destruct (lin_is_const ea). { split; [exact L3a|]. split; [apply aext_refl|reflexivity]. }
          pose proof (aassume_sound A3 nu2 (lsub (lsym r) ea) L3a
                        ltac:(rewrite eval_lsub, eval_lsym, V2, Exa; unfold rv; lia)
                        ltac:(rewrite N3; now apply lin_below_lsub)) as (F&L&X).
          split; [exact L|]. split; [exact X|apply aassume_next]. }
        destruct L4 as (L4a&X4&N4).
        exists nu2. split; [|split; [exact L4a|]].
        -- eapply aext_trans; [split; [exact X2a|split; [exact X2b|exact X2c]]|]. eapply aext_trans; [exact X3|exact X4].
        -- split; [|apply lin_below_lsym; rewrite N4, N3; exact S2]. rewrite eval_lsym, V2. unfold rv. symmetry. apply zwrap_id. lia.
      * (* [comment removed for export] *)
        apply res_word_fresh; auto.
        -- destruct (Z.eqb_spec (eval nu eb) 0); [lia|]. pose proof (Z.mod_pos_bound (eval nu ea) (eval nu eb) ltac:(lia)). lia.
        -- destruct (Z.eqb_spec (eval nu eb) 0).
           ++ split; cbn [fst snd lo_le hi_ge]; [lia|]. destruct (Z.leb_spec 1 hb); lia.
           ++ pose proof (Z.mod_pos_bound (eval nu ea) (eval nu eb) ltac:(lia)).
              pose proof (Z.mod_le (eval nu ea) (eval nu eb) ltac:(lia) ltac:(lia)).
              split; cbn [fst snd lo_le hi_ge]; [lia|]. destruct (Z.leb_spec 1 hb); lia.
    + (* [comment removed for export] *)
      destruct b as [eb|]; [|apply res_top; exact HG].
      destruct (inU A eb) eqn:EUb; [|apply res_top; exact HG].
      pose proof (inU_sound A nu eb HG EUb) as HUb. rewrite zwrap_id in Hub by lia. simpl in Bb.
      pose proof (bnd_sound A nu eb HG) as Hbb.
      destruct (bnd A eb) as [[lb|] [hb|]]; try (apply res_top; exact HG).
      destruct Hbb as [Hlb Hhb]; cbn [fst snd lo_le hi_ge] in Hlb, Hhb.
      destruct (Z.leb_spec 1 lb); [|apply res_top; exact HG].
      rewrite Hub. destruct (Z.eqb_spec (eval nu eb) 0); [lia|].
      pose proof (Z.mod_pos_bound ua (eval nu eb) ltac:(lia)) as Hm.
      set (rv := ua mod eval nu eb).
      assert (Hrv : in_itv rv (Some 0, Some (hb - 1))) by (split; cbn [fst snd lo_le hi_ge]; lia).
      pose proof (fresh_sym_box_sound A nu (Some 0, Some (hb - 1)) rv HG Hrv) as FS.
      destruct (fresh_sym A) as [r A1] eqn:Efs. destruct FS as (X2&L2&V2&S2&N2).
      set (A2 := asetbox A1 r (Some 0, Some (hb - 1))) in *. set (nu2 := vupd nu r rv) in *.
      assert (Exb : eval nu2 eb = eval nu eb) by (apply (eval_ext_below (vs_next A)); [apply X2|exact Bb]).
      destruct X2 as (X2a&X2b&X2c).
      assert (Beb : lin_below eb (vs_next A2) = true) by (eapply lin_below_mono; [exact X2b|exact Bb]).
      set (A3 := if lin_is_const eb then A2 else snd (aassume A2 (laddc (lsub (lsym r) eb) 1))).
      assert (L3 : lgamma A3 nu2 /\ aext A2 A3 nu2 nu2 /\ vs_next A3 = vs_next A2).
      { unfold A3. destruct (lin_is_const eb). { split; [exact L2|]. split; [apply aext_refl|reflexivity]. }
        pose proof (aassume_sound A2 nu2 (laddc (lsub (lsym r) eb) 1) L2
                      ltac:(rewrite eval_laddc, eval_lsub, eval_lsym, V2, Exb; unfold rv; lia)
                      ltac:(apply lin_below_laddc; apply lin_below_lsub; [apply lin_below_lsym; exact S2|exact Beb])) as (F&L&X).
        split; [exact L|]. split; [exact X|apply aassume_next]. }
      destruct L3 as (L3a&X3&N3).
      exists nu2. split; [|split; [exact L3a|]].
      * eapply aext_trans; [split; [exact X2a|split; [exact X2b|exact X2c]]|exact X3].
      * split; [|apply lin_below_lsym; rewrite N3; exact S2]. rewrite eval_lsym, V2. unfold rv. symmetry. apply zwrap_id. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma zrange_in lo n x : In x (zrange lo n) <-> lo <= x < lo + Z.of_nat n.
Proof.
  revert lo. induction n as [|n IH]; intros lo; simpl.
  - lia.
  - rewrite IH. lia.
Qed.

Lemma enum_values_sound A nu e ts :
  lgamma A nu -> enum_values A e = Some ts -> 0 <= eval nu e < 2 ^ 64 -> In (eval nu e) ts.
Proof.
  intros HG He Hr. unfold enum_values in He.
  assert (Hz : forall x, 0 <= x < 2 ^ 64 -> zm64 x = x) by (intros; rewrite zm64_zwrap; apply zwrap_id; lia).
  destruct (lin_is_const e) eqn:Ec.
  { inversion He; subst. rewrite (eval_is_const nu e Ec) in *. left. apply Hz. lia. }
  set (vs := match lin_single e with
             | Some (s, k) => if k =? 1 then match pm_get s (vs_valset A) with Some xs => Some (map (fun x => zm64 (x + lc e)) xs) | None => None end else None
             | None => None end) in He.
  assert (Hvs : forall l, vs = Some l -> In (eval nu e) l).
  { intros l. unfold vs. destruct (lin_single e) as [[s k]|] eqn:Es; [|discriminate].
    destruct (Z.eqb_spec k 1); [|discriminate]. subst k.
    destruct (pm_get s (vs_valset A)) as [xs|] eqn:Eg; [|discriminate]. intros X; inversion X; subst; clear X.
    destruct HG as (_&_&_&HV&_). specialize (HV _ _ Eg).
    rewrite (eval_single nu e s 1 Es) in *. rewrite <- (Hz (lc e + 1 * nu s)) by lia.
    apply in_map_iff. exists (nu s). split; [f_equal; lia|exact HV]. }
  destruct vs as [l|]; [inversion He; subst; now apply Hvs|]. clear Hvs.
  pose proof (lp_bounds_sound nu (vs_store A) (lg_sat _ _ HG) e) as Hb.
  destruct (lp_bounds (vs_store A) e) as [[lo|] [hi|]]; try discriminate.
  destruct Hb as [Hlo Hhi]; cbn [fst snd lo_le hi_ge] in Hlo, Hhi.
  destruct (Z.leb (hi - lo) 64 && Z.leb lo hi) eqn:El; [|discriminate]. inversion He; subst; clear He.
  rewrite <- (Hz (eval nu e)) by lia. apply in_map. apply zrange_in. rewrite Z2Nat.id by lia. lia.
Qed.

Lemma assume_eq_sound A nu e c :
  lgamma A nu -> eval nu e = c -> lin_below e (vs_next A) = true ->
  fst (assume_eq A e c) = true /\ lgamma (snd (assume_eq A e c)) nu /\ aext A (snd (assume_eq A e c)) nu nu.
Proof.
  intros HG Hc Hb. unfold assume_eq.
  destruct (lin_is_const (laddc e (- c))) eqn:Ek.
  { cbn [fst snd]. split; [|split; [exact HG|apply aext_refl]].
    pose proof (eval_is_const nu _ Ek) as X. rewrite eval_laddc in X. apply Z.eqb_eq. rewrite <- X. lia. }
  pose proof (aassume2_sound A nu (laddc e (- c)) (lneg (laddc e (- c))) HG
                ltac:(rewrite eval_laddc; lia) ltac:(rewrite eval_lneg, eval_laddc; lia)
                ltac:(now apply lin_below_laddc) ltac:(apply lin_below_lneg; now apply lin_below_laddc)) as (F&L&X).
  pose proof (aassume2_next A (laddc e (- c)) (lneg (laddc e (- c)))) as N.
  destruct (aassume2 A _ _) as [ok A1]. cbn [fst snd] in F, L, X, N |- *. subst ok.
  destruct (lin_single e) as [[s k]|] eqn:Es; [|split; [reflexivity|split; [exact L|exact X]]].
  destruct (Z.eqb_spec k 1); [|split; [reflexivity|split; [exact L|exact X]]]. subst k.
  destruct (pm_get s (vs_valset A1)) as [xs|] eqn:Eg; [|split; [reflexivity|split; [exact L|exact X]]].
  split; [reflexivity|]. split.
  - destruct L as (HS&HC&HM&HV&(B0&B1&B2&B3&B4&(C1&C2&C3))).
    split; [exact HS|]. split; [exact HC|]. split; [exact HM|]. split.
    { intros s' vs Hg'. cbn [vs_valset set_valset] in Hg'. rewrite pm_get_set in Hg'.
      destruct (Pos.eqb_spec s' s); [|exact (HV _ _ Hg')]. injection Hg' as <-. subst s'. left.
      rewrite (eval_single nu e s 1 Es) in Hc. lia. }
    split; [exact B0|]. split; [exact B1|]. split; [exact B2|]. split; [exact B3|]. split; [exact B4|].
    split; [exact C1|]. split; [exact C2|].
    intros s' vs Hg'. cbn [vs_valset set_valset vs_next] in Hg' |- *. rewrite pm_get_set in Hg'.
    destruct (Pos.eqb_spec s' s); [subst; exact (C3 _ _ Eg)|exact (C3 _ _ Hg')].
  - eapply aext_trans; [exact X|]. apply aext_keep; [reflexivity|apply same_shape_set_valset].
Qed.
