(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Monad Run Specs.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec ShapeSet RealizesCfg AsanAcct PlacementCount AllocNodesCfg SysNodesCfg.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLin FxCore.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound FxMem FxRgs FxFacts FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSubst FxEnt FxLoop FxPlan FxFrame FxEcall.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChDen.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound.FxGlue OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxMem OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxRgs OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEnt OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEcall OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen.FxAcct.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxBacking FxChDen FxChLib.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChNull.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChSep.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChNull.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChNull FxChFix FxChUnmap FxChain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChSplit.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxBacking OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChLib OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull.FxChSeg OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChSep OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull.FxChNode OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChFix OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChUnmap OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChain OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChain.FxChSys OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChSplit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition split_pieces_s (R : region) (o : Z) (p m : lin) (t : option lin) : list region :=
  (if Z.eqb o 0 then [] else [RG (rg_base R) (lconst o) (rg_kind R) (cut_below o (rg_cont R))]) ++
  RG p m RW TEmpty :: match t with Some tl => [RG (ladd p m) tl RW TEmpty] | None => [] end.
(* [comment removed for export] *)
Definition split_chk_s (fs : list fact) (n : positive) (R : region) (p m : lin) : option (Z * option lin) :=
  match lin_off p (rg_base R) with
  | Some o =>
      let '(mlo, mhi) := irange fs m in
      let zhi := snd (irange fs (rg_size R)) in
      if (rk_rwz (rg_kind R) && Z.leb 0 o && Z.leb 1 mlo && lwf n p && lwf n m && lwf n (rg_size R) &&
          Z.ltb (snd (irange fs (rg_base R)) + zhi) two64 && Z.ltb (o + mhi) two64)%bool
      then if lin_eqb (laddc m o) (rg_size R) then Some (o, None)
           else let tl := lsub (rg_size R) (laddc m o) in let '(tlo, thi) := irange fs tl in
                if (Z.leb 1 tlo && Z.ltb (thi + mhi + o) two64)%bool then Some (o, Some tl) else None
      else None
  | None => None
  end.
Definition split_post_s (S : sst) (i : nat) (p m : lin) : option sst :=
  match nth_error (s_rgs S) i with
  | Some R => match split_chk_s (s_facts S) (s_next S) R p m with
              | Some (o, t) => Some (SST (s_pc S) (s_regs S) (split_pieces_s R o p m t ++ remove_nth i (s_rgs S)) (s_facts S) (s_next S) (s_resv S))
              | None => None
              end
  | None => None
  end.

(* [comment removed for export] *)
Definition geo_s (E : valu) (R : region) (o : Z) (p m : lin) (t : option lin) (z : Z) : Prop :=
  rsz E R = z /\ 0 <= o /\ 1 <= uE E m /\ uE E p = uE E (rg_base R) + o /\ uE E (rg_base R) + z < two64 /\
  match t with Some tl => 1 <= uE E tl /\ o + uE E m + uE E tl = z | None => o + uE E m = z end.

Lemma base_suf_s : forall E R o p m t z, geo_s E R o p m t z -> uE E (ladd p m) = uE E (rg_base R) + o + uE E m.
Proof.
  intros E R o p m t z (Hz & Ho & Hm & Hp & Hw & Ht). pose proof (uE_range E (rg_base R)) as Rb. pose proof (uE_range E m) as Rm.
  assert (Hl : bv_unsigned (lden E (ladd p m)) = (uE E p + uE E m) mod two64).
  { rewrite lden_ladd, bv_add_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with two64. reflexivity. }
  unfold uE at 1. rewrite Hl, Hp. apply Z.mod_small. destruct t as [tl|]; [pose proof (uE_range E tl)|]; lia.
Qed.
Lemma rsz_pre_s : forall E R o, 0 <= o < two64 -> rsz E (RG (rg_base R) (lconst o) (rg_kind R) (cut_below o (rg_cont R))) = o.
Proof. intros E R o Ho. unfold rsz. cbn [rg_size]. rewrite lden_lconst. apply u_small64. exact Ho. Qed.
Lemma geo_o_lt : forall E R o p m t z, geo_s E R o p m t z -> 0 <= o < z /\ z < two64.
Proof. intros E R o p m t z (Hz & Ho & Hm & Hp & Hw & Ht). pose proof (uE_range E (rg_base R)). destruct t as [tl|]; lia. Qed.

Lemma pieces_pts_s : forall E R o p m t z, geo_s E R o p m t z ->
  forall R', In R' (split_pieces_s R o p m t) ->
  0 < rsz E R' /\ exists d, 0 <= d /\ uE E (rg_base R') = uE E (rg_base R) + d /\ d + rsz E R' <= z.
Proof.
  intros E R o p m t z G R' HR'. pose proof (geo_o_lt _ _ _ _ _ _ _ G) as [Ho Hz64]. pose proof (base_suf_s _ _ _ _ _ _ _ G) as Hbs.
  destruct G as (Hz & _ & Hm & Hp & Hw & Ht).
  unfold split_pieces_s in HR'. apply in_app_iff in HR' as [HR'|HR'].
  - destruct (Z.eqb o 0) eqn:Ho0; [destruct HR'|]. destruct HR' as [<-|[]]. apply Z.eqb_neq in Ho0.
    rewrite (rsz_pre_s E R o ltac:(lia)). split; [lia|]. exists 0. cbn [rg_base]. lia.
  - destruct HR' as [<-|HR'].
    + rewrite rsz_mid. split; [lia|]. exists o. cbn [rg_base]. rewrite Hp. destruct t; lia.
    + destruct t as [tl|]; [|destruct HR']. destruct HR' as [<-|[]]. unfold rsz at 1 2. cbn [rg_size rg_base]. fold (uE E tl).
      split; [lia|]. exists (o + uE E m). rewrite Hbs. lia.
Qed.
Lemma pt_in_pieces_s : forall E R o p m t z, geo_s E R o p m t z ->
  forall w, uE E (rg_base R) <= w < uE E (rg_base R) + z ->
  exists R', In R' (split_pieces_s R o p m t) /\ uE E (rg_base R') <= w < uE E (rg_base R') + rsz E R'.
Proof.
  intros E R o p m t z G w Hw0. pose proof (geo_o_lt _ _ _ _ _ _ _ G) as [Ho Hz64]. pose proof (base_suf_s _ _ _ _ _ _ _ G) as Hbs.
  destruct G as (Hz & _ & Hm & Hp & Hw & Ht). unfold split_pieces_s.
  destruct (Z_lt_le_dec w (uE E (rg_base R) + o)) as [H1|H1].
  - destruct (Z.eqb o 0) eqn:Ho0; [apply Z.eqb_eq in Ho0; lia|].
    exists (RG (rg_base R) (lconst o) (rg_kind R) (cut_below o (rg_cont R))). split; [apply in_or_app; left; left; reflexivity|].
    rewrite (rsz_pre_s E R o ltac:(lia)). cbn [rg_base]. lia.
  - destruct (Z_lt_le_dec w (uE E (rg_base R) + o + uE E m)) as [H2|H2].
    + exists (RG p m RW TEmpty). split; [apply in_or_app; right; left; reflexivity|]. rewrite rsz_mid. cbn [rg_base]. rewrite Hp. lia.
    + destruct t as [tl|]; [|lia].
      exists (RG (ladd p m) tl RW TEmpty). split; [apply in_or_app; right; right; left; reflexivity|].
      unfold rsz. cbn [rg_size rg_base]. fold (uE E tl). rewrite Hbs. lia.
Qed.
Lemma pieces_disj_s : forall E R o p m t z, geo_s E R o p m t z -> rgs_disj E (split_pieces_s R o p m t).
Proof.
  intros E R o p m t z G. pose proof (geo_o_lt _ _ _ _ _ _ _ G) as [Ho Hz64]. pose proof (base_suf_s _ _ _ _ _ _ _ G) as Hbs.
  destruct G as (Hz & _ & Hm & Hp & Hw & Ht).
  assert (Hmid : forall tl, t = Some tl -> rg_disj E (RG p m RW TEmpty) (RG (ladd p m) tl RW TEmpty)).
  { intros tl _. unfold rg_disj. cbv zeta. cbn [rg_base]. fold (uE E p) (uE E (ladd p m)). rewrite rsz_mid, Hbs, Hp. lia. }
  unfold split_pieces_s. destruct (Z.eqb o 0) eqn:Ho0; cbn [app].
  - destruct t as [tl|]; cbn [rgs_disj].
    + split; [constructor; [exact (Hmid tl eq_refl)|constructor]|split; [constructor | exact I]].
    + split; [constructor | exact I].
  - apply Z.eqb_neq in Ho0. pose proof (rsz_pre_s E R o ltac:(lia)) as Hps.
    assert (Hpm : rg_disj E (RG (rg_base R) (lconst o) (rg_kind R) (cut_below o (rg_cont R))) (RG p m RW TEmpty)).
    { unfold rg_disj. cbv zeta. cbn [rg_base]. fold (uE E (rg_base R)) (uE E p). rewrite Hps, rsz_mid, Hp. lia. }
    destruct t as [tl|]; cbn [rgs_disj].
    + split; [constructor; [exact Hpm|constructor; [|constructor]]|split; [constructor; [exact (Hmid tl eq_refl)|constructor]|split; [constructor | exact I]]].
      unfold rg_disj. cbv zeta. cbn [rg_base]. fold (uE E (rg_base R)) (uE E (ladd p m)). rewrite Hps, Hbs. unfold rsz. cbn [rg_size]. fold (uE E tl). lia.
    + split; [constructor; [exact Hpm|constructor]|split; [constructor | exact I]].
Qed.
Lemma pieces_ok_s : forall segs E mem R o p m t z, rg_ok segs E mem R -> rk_rwz (rg_kind R) = true -> geo_s E R o p m t z ->
  Forall (rg_ok segs E mem) (split_pieces_s R o p m t).
Proof.
  intros segs E mem R o p m t z Hok Hk G. pose proof (geo_o_lt _ _ _ _ _ _ _ G) as [Ho Hz64]. pose proof (base_suf_s _ _ _ _ _ _ _ G) as Hbs.
  destruct G as (Hz & _ & Hm & Hp & Hws & Ht).
  destruct Hok as (Hs & Hw & Hbytes & Hc). fold (uE E (rg_base R)) in Hw, Hbytes, Hc. rewrite Hz in Hs, Hw, Hbytes, Hc.
  assert (Hrw : forall i, 0 <= i < z -> rd1 segs mem (Z_to_bv 64 (uE E (rg_base R) + i)) <> None /\ wview segs mem (Z_to_bv 64 (uE E (rg_base R) + i)) <> None).
  { intros i Hi. specialize (Hbytes i Hi). destruct (rg_kind R); try discriminate; [exact Hbytes | exact (proj1 Hbytes)]. }
  apply Forall_forall. intros R' HR'. unfold split_pieces_s in HR'. apply in_app_iff in HR' as [HR'|HR'].
  - destruct (Z.eqb o 0) eqn:Ho0; [destruct HR'|]. destruct HR' as [<-|[]]. apply Z.eqb_neq in Ho0.
    unfold rg_ok. fold (rsz E (RG (rg_base R) (lconst o) (rg_kind R) (cut_below o (rg_cont R)))).
    rewrite (rsz_pre_s E R o ltac:(lia)). cbn [rg_base rg_kind rg_cont]. fold (uE E (rg_base R)).
    split; [lia|]. split; [lia|]. split.
    + intros i Hi. specialize (Hbytes i ltac:(destruct t; lia)). destruct (rg_kind R); try discriminate; [exact Hbytes|].
      destruct Hbytes as [H1 H2]. split; [exact H1|]. intros Hn. apply H2. rewrite tget_cut_below in Hn.
      replace (Z.ltb (Zpos (okey i) - 1) o) with true in Hn by (symmetry; apply Z.ltb_lt; unfold okey; rewrite Z2Pos.id by lia; lia). exact Hn.
    + intros k v Hkv. rewrite tget_cut_below in Hkv. destruct (Z.ltb (Zpos k - 1) o) eqn:Hlt; [|discriminate].
      apply Z.ltb_lt in Hlt. destruct (Hc k v Hkv) as [_ Hv]. split; [lia | exact Hv].
  - destruct HR' as [<-|HR'].
    + unfold rg_ok. fold (rsz E (RG p m RW TEmpty)). rewrite (rsz_mid E p m). cbn [rg_base rg_kind rg_cont]. fold (uE E p). rewrite Hp.
      split; [lia|]. split; [destruct t; lia|]. split.
      * intros i Hi. replace (uE E (rg_base R) + o + i) with (uE E (rg_base R) + (o + i)) by lia. exact (Hrw (o + i) ltac:(destruct t; lia)).
      * intros k v Hkv. rewrite tget_empty in Hkv. discriminate.
    + destruct t as [tl|]; [|destruct HR']. destruct HR' as [<-|[]].
      unfold rg_ok, rsz. cbv zeta. cbn [rg_base rg_kind rg_cont rg_size]. unfold uE in *. rewrite Hbs.
      split; [lia|]. split; [lia|]. split.
      * intros i Hi. replace (bv_unsigned (lden E (rg_base R)) + o + bv_unsigned (lden E m) + i) with (bv_unsigned (lden E (rg_base R)) + (o + bv_unsigned (lden E m) + i)) by lia.
        exact (Hrw (o + bv_unsigned (lden E m) + i) ltac:(lia)).
      * intros k v Hkv. rewrite tget_empty in Hkv. discriminate.
Qed.

(* [comment removed for export] *)
Section SplitS.
Variable segs : list Segment.
Variable LIMIT : Z.
Variable mem0 : word -> option byte.

(* [comment removed for export] *)
#[using="Type"] Lemma uE_laddc_small : forall E l c, 0 <= uE E l + c < two64 -> uE E (laddc l c) = uE E l + c.
Proof. LiaFast.lf_pins LiaFast.u0. intros E l c H. unfold uE in *. rewrite lden_laddc. apply u_small64. exact H. Qed.
#[using="Type"] Lemma split_chk_s_geo : forall fs n R p m o t, split_chk_s fs n R p m = Some (o, t) ->
  rk_rwz (rg_kind R) = true /\ lwf n p = true /\ lwf n m = true /\ (forall tl, t = Some tl -> lwf n tl = true) /\
  forall E, Forall (fact_ok E) fs -> geo_s E R o p m t (rsz E R).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros fs n R p m o t H. unfold split_chk_s in H. destruct (lin_off p (rg_base R)) as [o0|] eqn:Ho0; [|discriminate].
  destruct (irange fs m) as [mlo mhi] eqn:Him.
  destruct (rk_rwz (rg_kind R) && Z.leb 0 o0 && Z.leb 1 mlo && lwf n p && lwf n m && lwf n (rg_size R) &&
            Z.ltb (snd (irange fs (rg_base R)) + snd (irange fs (rg_size R))) two64 && Z.ltb (o0 + mhi) two64)%bool eqn:Hb; [|discriminate].
  repeat match type of Hb with ((_ && _)%bool = true) => apply andb_prop in Hb as [Hb ?Hx] end.
  rename Hb into Hk.
  repeat match goal with
         | H' : Z.leb _ _ = true |- _ => apply Z.leb_le in H'
         | H' : Z.ltb _ _ = true |- _ => apply Z.ltb_lt in H'
         end.
  match goal with H' : lwf n p = true |- _ => rename H' into Hwp end.
  match goal with H' : lwf n m = true |- _ => rename H' into Hwm end.
  match goal with H' : lwf n (rg_size R) = true |- _ => rename H' into Hwz end.
  assert (Hbase : forall E, Forall (fact_ok E) fs -> 1 <= uE E m <= mhi /\ uE E (rg_base R) + rsz E R < two64).
  { intros E HF. pose proof (irange_sound E fs m HF) as Im. rewrite Him in Im. cbn [fst snd] in Im. fold (uE E m) in Im.
    pose proof (irange_sound E fs (rg_base R) HF) as Ib. fold (uE E (rg_base R)) in Ib.
    pose proof (irange_sound E fs (rg_size R) HF) as Iz. fold (rsz E R) in Iz. lia. }
  assert (Hfin : forall E, o0 <= rsz E R -> uE E (rg_base R) + rsz E R < two64 -> uE E p = uE E (rg_base R) + o0).
  { intros E Hle Hbz. unfold uE. apply (lin_off_u E p (rg_base R) o0 Ho0). pose proof (uE_range E (rg_base R)) as Rb. unfold uE in *. lia. }
  destruct (lin_eqb (laddc m o0) (rg_size R)) eqn:Hex.
  - (* [comment removed for export] *)
    injection H as <- <-. apply lin_eqb_eq in Hex.
    split; [exact Hk|]. split; [exact Hwp|]. split; [exact Hwm|]. split; [intros tl Ht; discriminate Ht|].
    intros E HF. destruct (Hbase E HF) as [Hm Hbz]. pose proof (uE_range E m) as Rm.
    assert (Hz : rsz E R = uE E m + o0) by (unfold rsz; rewrite <- Hex; fold (uE E (laddc m o0)); apply uE_laddc_small; lia).
    unfold geo_s. split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [apply Hfin; lia|]. split; [exact Hbz|]. lia.
  - destruct (irange fs (lsub (rg_size R) (laddc m o0))) as [tlo thi] eqn:Hit.
    destruct (Z.leb 1 tlo && Z.ltb (thi + mhi + o0) two64)%bool eqn:Hb2; [|discriminate]. injection H as <- <-.
    apply andb_prop in Hb2 as [T1 T2]. apply Z.leb_le in T1. apply Z.ltb_lt in T2.
    split; [exact Hk|]. split; [exact Hwp|]. split; [exact Hwm|].
    split; [intros tl Ht; injection Ht as <-; apply lwf_lsub_s; [exact Hwz | apply lwf_laddc; exact Hwm]|].
    intros E HF. destruct (Hbase E HF) as [Hm Hbz]. pose proof (uE_range E m) as Rm. pose proof (uE_range E (rg_base R)) as Rb.
    pose proof (irange_sound E fs (lsub (rg_size R) (laddc m o0)) HF) as It. rewrite Hit in It. cbn [fst snd] in It.
    fold (uE E (lsub (rg_size R) (laddc m o0))) in It.
    assert (Hmo : uE E (laddc m o0) = uE E m + o0) by (apply uE_laddc_small; lia).
    assert (Hrs : 0 <= rsz E R < two64) by (unfold rsz; apply uE_range).
    assert (Htv : uE E (lsub (rg_size R) (laddc m o0)) = rsz E R - (uE E m + o0)).
    { destruct (small_diff E (rg_size R) (laddc m o0) _ _ It) as [[Hl He]|[Hl He]]; change (uE E (rg_size R)) with (rsz E R) in Hl, He; rewrite Hmo in Hl, He; [lia|].
      exfalso. unfold two64 in *. lia. }
    unfold geo_s. split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [apply Hfin; lia|]. split; [exact Hbz|]. lia.
Qed.

#[using="Type"] Theorem den_split_s : forall model0 E S M ms model i p m S', DEN segs LIMIT model0 mem0 E S M ms model -> split_post_s S i p m = Some S' ->
  DEN segs LIMIT model0 mem0 E S' M ms model.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros model0 E S M ms model i p m S' Hd Hp. unfold split_post_s in Hp.
  destruct (nth_error (s_rgs S) i) as [R|] eqn:Hi; [|discriminate]. destruct (split_chk_s (s_facts S) (s_next S) R p m) as [[o t]|] eqn:Hc; [|discriminate].
  injection Hp as <-.
  destruct (split_chk_s_geo _ _ _ _ _ _ _ Hc) as (Hk & Hwp & Hwm & Hwt & Hgeo0).
  pose proof Hd as Hd0.
  destruct Hd0 as [Hsd Hwf Hbw Hh Hawf Hanz Hminv Hhoff Hres Hlim Hsp Hspok Hbrk Hsbrk Htid Hmaps Hgsh Hgtop Hivwf Hpd Hmres Hkind Hlzm Hzrsh Hzrm Hzr Hrl Hvmo Hproc Hfrz Hrom Hown Hblob].
  set (pcs := split_pieces_s R o p m t) in *.
  set (S2 := SST (s_pc S) (s_regs S) (pcs ++ remove_nth i (s_rgs S)) (s_facts S) (s_next S) (s_resv S)).
  assert (HF0 : Forall (fact_ok E) (s_facts S)) by (destruct (sden_0 _ _ _ _ Hsd) as (_ & _ & _ & _ & _ & _ & X & _); exact X).
  pose proof (Hgeo0 E HF0) as G.
  assert (Hpts : forall E', Forall (fact_ok E') (s_facts S) -> forall w,
            (exists R', In R' pcs /\ uE E' (rg_base R') <= w < uE E' (rg_base R') + rsz E' R') <-> uE E' (rg_base R) <= w < uE E' (rg_base R) + rsz E' R).
  { intros E' HF' w. pose proof (Hgeo0 E' HF') as G'. split.
    - intros (R' & HR' & Hw). destruct (pieces_pts_s E' R o p m t _ G' R' HR') as (_ & d & Hd0' & Hb' & Hdz). lia.
    - intros Hw. exact (pt_in_pieces_s E' R o p m t _ G' w Hw). }
  assert (Hbw2 : bases_wf (s_next S) (pcs ++ remove_nth i (s_rgs S)) = true).
  { unfold bases_wf in *. rewrite forallb_app. apply andb_true_intro. split.
    - unfold pcs, split_pieces_s. rewrite forallb_app. apply andb_true_intro. split.
      + destruct (Z.eqb o 0); cbn [forallb rg_base rg_size]; [reflexivity|]. rewrite forallb_forall in Hbw.
        destruct (andb_prop _ _ (Hbw R (nth_error_In _ _ Hi))) as [Hb1 _]. rewrite Hb1, lwf_lconst. reflexivity.
      + cbn [forallb rg_base rg_size]. rewrite Hwp, Hwm. cbn [andb]. destruct t as [tl|]; cbn [forallb rg_base rg_size]; [|reflexivity].
        assert (Hl1 : lwf (s_next S) (ladd p m) = true) by (apply lwf_ladd; assumption).
        rewrite Hl1, (Hwt tl eq_refl). reflexivity.
    - apply forallb_forall. intros R0 HR0. rewrite forallb_forall in Hbw. exact (Hbw R0 (remove_nth_In i _ R0 HR0)). }
  assert (Hout : forall x, outside E (s_rgs S2) x <-> outside E (s_rgs S) x)
    by (intros x; cbn [S2 s_rgs]; exact (outside_split E (s_rgs S) i R pcs Hi (Hpts E HF0) x)).
  constructor; try assumption.
  - intros E'' Ha''. destruct (Hsd E'' Ha'') as (H1 & H2 & H3 & H4 & HG & HD & HF & H8).
    pose proof (Hgeo0 E'' HF) as G''.
    unfold sden0. cbn [S2 s_pc s_regs s_rgs s_facts s_resv].
    split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [|split; [|split; [exact HF | exact H8]]].
    + apply Forall_app. split.
      * rewrite Forall_forall in HG. exact (pieces_ok_s segs E'' _ R o p m t _ (HG R (nth_error_In _ _ Hi)) Hk G'').
      * apply remove_nth_Forall. exact HG.
    + apply rgs_disj_app; [exact (pieces_disj_s E'' R o p m t _ G'') | exact (rgs_disj_remove E'' _ i HD) |].
      intros R1 R2 HR1 HR2. destruct (remove_nth_pos _ i R2 HR2) as (j & Hne & Hj).
      pose proof (rgs_disj_nth E'' _ i j R R2 HD (not_eq_sym Hne) Hi Hj) as Hd2. unfold rg_disj in *. cbv zeta in *.
      destruct (pieces_pts_s E'' R o p m t _ G'' R1 HR1) as (Hp1 & d & Hd1 & Hb1 & Hdz).
      fold (uE E'' (rg_base R1)) (uE E'' (rg_base R2)) (uE E'' (rg_base R)) in *. lia.
  - intros w Hw Hout' Hnow Hnb. apply (Hzr w Hw); [|exact Hnow | exact Hnb]. exact (proj1 (Hout _) Hout').
  - cbn [S2 s_rgs]. apply Forall_app. split.
    + rewrite Forall_forall in Hrl |- *. intros R' HR'. destruct (Hrl R (nth_error_In _ _ Hi)) as [Hpos [Happ | (Hoff & HX & Hpc)]].
      * destruct (pieces_pts_s E R o p m t _ G R' HR') as (Hp1 & d & Hd1 & Hb1 & Hdz). split; [exact Hp1|]. left.
        intros w Hw. apply Happ. lia.
      * destruct (pieces_pts_s E R o p m t _ G R' HR') as (Hp1 & d & Hd1 & Hb1 & Hdz). split; [exact Hp1|]. right.
        fold (uE E (rg_base R')) in *. fold (uE E (rg_base R)) in *. split; [lia|]. split.
        -- intros x Hxr. apply HX. lia.
        -- intros w Hw. apply Hpc. lia.
    + rewrite Forall_forall in Hrl |- *. intros R0 HR0. exact (Hrl R0 (remove_nth_In i _ R0 HR0)).
  - apply (frz_keep mem0 E E S S2 M M ms ms model model Hwf (agree_refl _ _) eq_refl eq_refl); [| | exact Hfrz].
    + intros w _ Ho'. exact (proj2 (Hout _) Ho').
    + intros w _ _. reflexivity.
  - apply (own_keep mem0 E E S S2 M M ms ms model model Hwf (agree_refl _ _) eq_refl); [| | | exact Hown].
    + intros w Ho'. exact (proj1 (Hout _) Ho').
    + intros w _. reflexivity.
    + intros x Hxx. exact Hxx.
Qed.
End SplitS.
(* [comment removed for export] *)
