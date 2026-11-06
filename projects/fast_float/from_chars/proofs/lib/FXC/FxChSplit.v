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
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxBacking OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChLib OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull.FxChSeg OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChSep OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull.FxChNode OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChFix OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChUnmap OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChain OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChain.FxChSys.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma lwf_lsub_s : forall n a b, lwf n a = true -> lwf n b = true -> lwf n (lsub a b) = true.
Proof. intros n a b Ha Hb. unfold lsub. rewrite lneg_eq. apply lwf_ladd; [exact Ha | apply lwf_lscale; exact Hb]. Qed.
Lemma rsz_is_const_s : forall E R n, is_const (rg_size R) = Some n -> rsz E R = n.
Proof. intros E R n H. unfold rsz. exact (is_const_u E _ n H). Qed.

(* [comment removed for export] *)
Definition cut_below (o : Z) (t : tree bval) : tree bval := tfilter (fun k => Z.ltb (Zpos k - 1) o) t.
Definition split_pieces (R : region) (o : Z) (p m : lin) (z : Z) : list region :=
  (if Z.eqb o 0 then [] else [RG (rg_base R) (lconst o) (rg_kind R) (cut_below o (rg_cont R))]) ++
  [RG p m RW TEmpty; RG (ladd p m) (lsub (lconst (z - o)) m) RW TEmpty].
Definition rk_rwz (k : rkind) : bool := match k with RW | RZ => true | _ => false end.
(* [comment removed for export] *)
Definition split_chk (fs : list fact) (n : positive) (R : region) (p m : lin) : option (Z * Z) :=
  match is_const (rg_size R), lin_off p (rg_base R) with
  | Some z, Some o =>
      let '(lo, hi) := irange fs m in
      if (rk_rwz (rg_kind R) && Z.leb 0 o && Z.ltb o z && Z.leb 1 lo && Z.ltb (o + hi) z && Z.ltb z two64 &&
          lwf n p && lwf n m && Z.ltb (snd (irange fs (rg_base R)) + z) two64)%bool
      then Some (o, z) else None
  | _, _ => None
  end.
Definition split_post (S : sst) (i : nat) (p m : lin) : option sst :=
  match nth_error (s_rgs S) i with
  | Some R => match split_chk (s_facts S) (s_next S) R p m with
              | Some (o, z) => Some (SST (s_pc S) (s_regs S) (split_pieces R o p m z ++ remove_nth i (s_rgs S)) (s_facts S) (s_next S) (s_resv S))
              | None => None
              end
  | None => None
  end.

(* [comment removed for export] *)
Lemma rsz_mid : forall E p m, rsz E (RG p m RW TEmpty) = uE E m.
Proof. reflexivity. Qed.
Lemma base_suf : forall E R o z p m, 0 <= o < z -> 1 <= uE E m /\ o + uE E m < z -> uE E p = uE E (rg_base R) + o ->
  uE E (rg_base R) + z < two64 -> uE E (ladd p m) = uE E (rg_base R) + o + uE E m.
Proof.
  intros E R o z p m Ho Hm Hp Hw. pose proof (uE_range E (rg_base R)) as Rb.
  assert (Hl : bv_unsigned (lden E (ladd p m)) = (uE E p + uE E m) mod two64).
  { rewrite lden_ladd, bv_add_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with two64. reflexivity. }
  unfold uE at 1. rewrite Hl, Hp. apply Z.mod_small. lia.
Qed.
Lemma rsz_suf : forall E R o z p m, 0 <= o < z -> 1 <= uE E m /\ o + uE E m < z -> uE E (rg_base R) + z < two64 ->
  rsz E (RG (ladd p m) (lsub (lconst (z - o)) m) RW TEmpty) = z - o - uE E m.
Proof.
  intros E R o z p m Ho Hm Hw.
  unfold rsz. cbn [rg_size]. rewrite lden_lsub, bv_sub_unsigned, lden_lconst. rewrite u_small64 by (unfold two64 in *; pose proof (uE_range E (rg_base R)); lia).
  fold (uE E m). unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with two64. apply Z.mod_small. unfold two64 in *. pose proof (uE_range E (rg_base R)). lia.
Qed.
Lemma rsz_pre : forall E R o z, 0 <= o < z -> uE E (rg_base R) + z < two64 ->
  rsz E (RG (rg_base R) (lconst o) (rg_kind R) (cut_below o (rg_cont R))) = o.
Proof. intros E R o z Ho Hw. unfold rsz. cbn [rg_size]. rewrite lden_lconst. apply u_small64. unfold two64 in *. pose proof (uE_range E (rg_base R)). lia. Qed.

(* [comment removed for export] *)
Lemma pieces_pts : forall E R o z p m, 0 <= o < z -> 1 <= uE E m /\ o + uE E m < z -> uE E p = uE E (rg_base R) + o ->
  uE E (rg_base R) + z < two64 ->
  forall R', In R' (split_pieces R o p m z) ->
  0 < rsz E R' /\ exists d, 0 <= d /\ uE E (rg_base R') = uE E (rg_base R) + d /\ d + rsz E R' <= z.
Proof.
  intros E R o z p m Ho Hm Hp Hw R' HR'. unfold split_pieces in HR'. apply in_app_iff in HR' as [HR'|HR'].
  - destruct (Z.eqb o 0) eqn:Ho0; [destruct HR'|]. destruct HR' as [<-|[]]. apply Z.eqb_neq in Ho0.
    rewrite (rsz_pre E R o z Ho Hw). split; [lia|]. exists 0. cbn [rg_base]. lia.
  - destruct HR' as [<-|[<-|[]]].
    + rewrite rsz_mid. split; [lia|]. exists o. cbn [rg_base]. rewrite Hp. lia.
    + rewrite (rsz_suf E R o z p m Ho Hm Hw). split; [lia|]. exists (o + uE E m). cbn [rg_base]. rewrite (base_suf E R o z p m Ho Hm Hp Hw). lia.
Qed.
(* [comment removed for export] *)
Lemma pt_in_pieces : forall E R o z p m, 0 <= o < z -> 1 <= uE E m /\ o + uE E m < z -> uE E p = uE E (rg_base R) + o ->
  uE E (rg_base R) + z < two64 ->
  forall w, uE E (rg_base R) <= w < uE E (rg_base R) + z ->
  exists R', In R' (split_pieces R o p m z) /\ uE E (rg_base R') <= w < uE E (rg_base R') + rsz E R'.
Proof.
  intros E R o z p m Ho Hm Hp Hw w Hw0. unfold split_pieces.
  destruct (Z_lt_le_dec w (uE E (rg_base R) + o)) as [H1|H1].
  - destruct (Z.eqb o 0) eqn:Ho0; [apply Z.eqb_eq in Ho0; lia|].
    exists (RG (rg_base R) (lconst o) (rg_kind R) (cut_below o (rg_cont R))). split; [apply in_or_app; left; left; reflexivity|].
    rewrite (rsz_pre E R o z Ho Hw). cbn [rg_base]. lia.
  - destruct (Z_lt_le_dec w (uE E (rg_base R) + o + uE E m)) as [H2|H2].
    + exists (RG p m RW TEmpty). split; [apply in_or_app; right; left; reflexivity|]. rewrite rsz_mid. cbn [rg_base]. rewrite Hp. lia.
    + exists (RG (ladd p m) (lsub (lconst (z - o)) m) RW TEmpty). split; [apply in_or_app; right; right; left; reflexivity|].
      rewrite (rsz_suf E R o z p m Ho Hm Hw). cbn [rg_base]. rewrite (base_suf E R o z p m Ho Hm Hp Hw). lia.
Qed.
(* [comment removed for export] *)
Lemma pieces_disj : forall E R o z p m, 0 <= o < z -> 1 <= uE E m /\ o + uE E m < z -> uE E p = uE E (rg_base R) + o ->
  uE E (rg_base R) + z < two64 -> rgs_disj E (split_pieces R o p m z).
Proof.
  intros E R o z p m Ho Hm Hp Hw.
  pose proof (base_suf E R o z p m Ho Hm Hp Hw) as Hbs. pose proof (rsz_suf E R o z p m Ho Hm Hw) as Hss.
  unfold split_pieces. destruct (Z.eqb o 0) eqn:Ho0; cbn [app rgs_disj].
  - split; [constructor; [|constructor]|split; [constructor | exact I]].
    unfold rg_disj. cbv zeta. cbn [rg_base]. fold (uE E p) (uE E (ladd p m)). rewrite rsz_mid, Hbs, Hp. lia.
  - apply Z.eqb_neq in Ho0. pose proof (rsz_pre E R o z Ho Hw) as Hps.
    split; [constructor; [|constructor; [|constructor]]|split; [constructor; [|constructor]|split; [constructor | exact I]]].
    + unfold rg_disj. cbv zeta. cbn [rg_base]. fold (uE E (rg_base R)) (uE E p). rewrite Hps, rsz_mid, Hp. lia.
    + unfold rg_disj. cbv zeta. cbn [rg_base]. fold (uE E (rg_base R)) (uE E (ladd p m)). rewrite Hps, Hss, Hbs. lia.
    + unfold rg_disj. cbv zeta. cbn [rg_base]. fold (uE E p) (uE E (ladd p m)). rewrite rsz_mid, Hss, Hbs, Hp. lia.
Qed.

(* [comment removed for export] *)
Lemma tget_cut_below : forall o t k, tget k (cut_below o t) = if Z.ltb (Zpos k - 1) o then tget k t else None.
Proof. intros o t k. unfold cut_below. rewrite tget_tfilter. destruct (tget k t); destruct (Z.ltb (Zpos k - 1) o); reflexivity. Qed.

Lemma pieces_ok : forall segs E mem R o z p m, rg_ok segs E mem R -> rk_rwz (rg_kind R) = true ->
  rsz E R = z -> 0 <= o < z -> 1 <= uE E m /\ o + uE E m < z -> uE E p = uE E (rg_base R) + o -> uE E (rg_base R) + z < two64 ->
  Forall (rg_ok segs E mem) (split_pieces R o p m z).
Proof.
  intros segs E mem R o z p m Hok Hk Hz Ho Hm Hp Hws.
  destruct Hok as (Hs & Hw & Hbytes & Hc). fold (uE E (rg_base R)) in Hw, Hbytes, Hc. rewrite Hz in Hs, Hw, Hbytes, Hc.
  assert (Hrw : forall i, 0 <= i < z -> rd1 segs mem (Z_to_bv 64 (uE E (rg_base R) + i)) <> None /\ wview segs mem (Z_to_bv 64 (uE E (rg_base R) + i)) <> None).
  { intros i Hi. specialize (Hbytes i Hi). destruct (rg_kind R); try discriminate; [exact Hbytes | exact (proj1 Hbytes)]. }
  apply Forall_forall. intros R' HR'. unfold split_pieces in HR'. apply in_app_iff in HR' as [HR'|HR'].
  - destruct (Z.eqb o 0) eqn:Ho0; [destruct HR'|]. destruct HR' as [<-|[]]. apply Z.eqb_neq in Ho0.
    unfold rg_ok. fold (rsz E (RG (rg_base R) (lconst o) (rg_kind R) (cut_below o (rg_cont R)))).
    rewrite (rsz_pre E R o z Ho Hws). cbn [rg_base rg_kind rg_cont]. fold (uE E (rg_base R)).
    split; [lia|]. split; [lia|]. split.
    + intros i Hi. specialize (Hbytes i ltac:(lia)). destruct (rg_kind R); try discriminate; [exact Hbytes|].
      destruct Hbytes as [H1 H2]. split; [exact H1|]. intros Hn. apply H2. rewrite tget_cut_below in Hn.
      replace (Z.ltb (Zpos (okey i) - 1) o) with true in Hn by (symmetry; apply Z.ltb_lt; unfold okey; rewrite Z2Pos.id by lia; lia). exact Hn.
    + intros k v Hkv. rewrite tget_cut_below in Hkv. destruct (Z.ltb (Zpos k - 1) o) eqn:Hlt; [|discriminate].
      apply Z.ltb_lt in Hlt. destruct (Hc k v Hkv) as [_ Hv]. split; [lia | exact Hv].
  - destruct HR' as [<-|[<-|[]]].
    + unfold rg_ok. fold (rsz E (RG p m RW TEmpty)). rewrite (rsz_mid E p m). cbn [rg_base rg_kind rg_cont]. fold (uE E p). rewrite Hp.
      split; [lia|]. split; [lia|]. split.
      * intros i Hi. replace (uE E (rg_base R) + o + i) with (uE E (rg_base R) + (o + i)) by lia. exact (Hrw (o + i) ltac:(lia)).
      * intros k v Hkv. rewrite tget_empty in Hkv. discriminate.
    + unfold rg_ok. fold (rsz E (RG (ladd p m) (lsub (lconst (z - o)) m) RW TEmpty)). rewrite (rsz_suf E R o z p m Ho Hm Hws).
      cbn [rg_base rg_kind rg_cont]. fold (uE E (ladd p m)). rewrite (base_suf E R o z p m Ho Hm Hp Hws).
      split; [lia|]. split; [lia|]. split.
      * intros i Hi. replace (uE E (rg_base R) + o + uE E m + i) with (uE E (rg_base R) + (o + uE E m + i)) by lia. exact (Hrw (o + uE E m + i) ltac:(lia)).
      * intros k v Hkv. rewrite tget_empty in Hkv. discriminate.
Qed.

(* [comment removed for export] *)
Lemma rgs_disj_nth : forall E rgs i j R1 R2, rgs_disj E rgs -> i <> j -> nth_error rgs i = Some R1 -> nth_error rgs j = Some R2 -> rg_disj E R1 R2.
Proof.
  intros E rgs. induction rgs as [|x r IH]; intros i j R1 R2 H Hne H1 H2; [destruct i; discriminate|].
  destruct H as [Hx Hr]. destruct i as [|i], j as [|j]; cbn [nth_error] in H1, H2; try lia.
  - injection H1 as <-. rewrite Forall_forall in Hx. exact (Hx R2 (nth_error_In _ _ H2)).
  - injection H2 as <-. rewrite Forall_forall in Hx. pose proof (Hx R1 (nth_error_In _ _ H1)) as Hd. unfold rg_disj in *. lia.
  - exact (IH i j R1 R2 Hr ltac:(lia) H1 H2).
Qed.
Lemma rgs_disj_remove : forall E rgs i, rgs_disj E rgs -> rgs_disj E (remove_nth i rgs).
Proof.
  intros E rgs. induction rgs as [|x r IH]; intros [|i] H; cbn [remove_nth]; try exact H; [exact (proj2 H)|].
  destruct H as [Hx Hr]. split; [|exact (IH i Hr)]. apply Forall_forall. intros y Hy. rewrite Forall_forall in Hx. exact (Hx y (remove_nth_In i r y Hy)).
Qed.
Lemma outside_split : forall E rgs i R pcs, nth_error rgs i = Some R ->
  (forall w, (exists R', In R' pcs /\ uE E (rg_base R') <= w < uE E (rg_base R') + rsz E R') <-> uE E (rg_base R) <= w < uE E (rg_base R) + rsz E R) ->
  forall x, outside E (pcs ++ remove_nth i rgs) x <-> outside E rgs x.
Proof.
  intros E rgs i R pcs Hi Hpts x. unfold outside. rewrite Forall_app. split.
  - intros [Hp Hr]. apply Forall_forall. intros R0 HR0. destruct (In_nth_error _ _ HR0) as (j & Hj).
    destruct (Nat.eq_dec j i) as [->|Hne].
    + rewrite Hi in Hj. injection Hj as <-.
      destruct (Z_lt_le_dec (bv_unsigned x) (uE E (rg_base R))) as [Hl|Hl]; [left; exact Hl|].
      destruct (Z_lt_le_dec (bv_unsigned x) (uE E (rg_base R) + rsz E R)) as [Hl2|Hl2]; [|right; exact Hl2].
      exfalso. destruct (proj2 (Hpts (bv_unsigned x)) ltac:(lia)) as (R' & HR' & Hw). rewrite Forall_forall in Hp.
      destruct (Hp R' HR') as [H1|H1]; unfold uE in *; lia.
    + rewrite Forall_forall in Hr. exact (Hr R0 (nth_remove_In rgs j i R0 Hj Hne)).
  - intros H. rewrite Forall_forall in H. split.
    + apply Forall_forall. intros R' HR'.
      destruct (Z_lt_le_dec (bv_unsigned x) (uE E (rg_base R'))) as [Hl|Hl]; [left; exact Hl|].
      destruct (Z_lt_le_dec (bv_unsigned x) (uE E (rg_base R') + rsz E R')) as [Hl2|Hl2]; [|right; exact Hl2].
      exfalso.
      assert (Hex : exists R0, In R0 pcs /\ uE E (rg_base R0) <= bv_unsigned x < uE E (rg_base R0) + rsz E R0) by (exists R'; split; [exact HR' | lia]).
      destruct (proj1 (Hpts (bv_unsigned x)) Hex) as [Hw1 Hw2].
      destruct (H R (nth_error_In _ _ Hi)) as [H1|H1]; unfold uE in *; lia.
    + apply Forall_forall. intros R0 HR0. exact (H R0 (remove_nth_In i rgs R0 HR0)).
Qed.

(* [comment removed for export] *)
Section Split.
Variable segs : list Segment.
Variable LIMIT : Z.
Variable mem0 : word -> option byte.

#[using="Type"] Theorem den_split : forall model0 E S M ms model i p m S', DEN segs LIMIT model0 mem0 E S M ms model -> split_post S i p m = Some S' ->
  DEN segs LIMIT model0 mem0 E S' M ms model.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros model0 E S M ms model i p m S' Hd Hp. unfold split_post in Hp.
  destruct (nth_error (s_rgs S) i) as [R|] eqn:Hi; [|discriminate]. destruct (split_chk (s_facts S) (s_next S) R p m) as [[o z]|] eqn:Hc; [|discriminate].
  injection Hp as <-.
  unfold split_chk in Hc. destruct (is_const (rg_size R)) as [z0|] eqn:Hz0; [|discriminate]. destruct (lin_off p (rg_base R)) as [o0|] eqn:Ho0; [|discriminate].
  destruct (irange (s_facts S) m) as [lo hi] eqn:Hir.
  destruct (rk_rwz (rg_kind R) && Z.leb 0 o0 && Z.ltb o0 z0 && Z.leb 1 lo && Z.ltb (o0 + hi) z0 && Z.ltb z0 two64 &&
            lwf (s_next S) p && lwf (s_next S) m && Z.ltb (snd (irange (s_facts S) (rg_base R)) + z0) two64)%bool eqn:Hb; [|discriminate].
  injection Hc as -> ->.
  repeat match type of Hb with ((_ && _)%bool = true) => apply andb_prop in Hb as [Hb ?Hx] end.
  rename Hb into Hk.
  repeat match goal with
         | H' : Z.leb _ _ = true |- _ => apply Z.leb_le in H'
         | H' : Z.ltb _ _ = true |- _ => apply Z.ltb_lt in H'
         end.
  match goal with H' : lwf (s_next S) p = true |- _ => rename H' into Hwp end.
  match goal with H' : lwf (s_next S) m = true |- _ => rename H' into Hwm end.
  pose proof Hd as Hd0.
  destruct Hd0 as [Hsd Hwf Hbw Hh Hawf Hanz Hminv Hhoff Hres Hlim Hsp Hspok Hbrk Hsbrk Htid Hmaps Hgsh Hgtop Hivwf Hpd Hmres Hkind Hlzm Hzrsh Hzrm Hzr Hrl Hvmo Hproc Hfrz Hrom Hown Hblob].
  set (pcs := split_pieces R o p m z) in *.
  set (S2 := SST (s_pc S) (s_regs S) (pcs ++ remove_nth i (s_rgs S)) (s_facts S) (s_next S) (s_resv S)).
  (* [comment removed for export] *)
  assert (Hgeo : forall E', agree (s_next S) E E' -> Forall (fact_ok E') (s_facts S) ->
            rsz E' R = z /\ 0 <= o < z /\ (1 <= uE E' m /\ o + uE E' m < z) /\ uE E' p = uE E' (rg_base R) + o /\ uE E' (rg_base R) + z < two64).
  { intros E' Ha HF'. pose proof (irange_sound E' (s_facts S) m HF') as Im. rewrite Hir in Im. cbn [fst snd] in Im.
    pose proof (irange_sound E' (s_facts S) (rg_base R) HF') as Ib.
    assert (Hrz : rsz E' R = z) by (exact (rsz_is_const_s E' R z Hz0)).
    assert (Hbz : uE E' (rg_base R) + z < two64) by (unfold uE; lia).
    split; [exact Hrz|]. split; [lia|]. split; [unfold uE; lia|]. split; [|exact Hbz].
    unfold uE. apply (lin_off_u E' p (rg_base R) o Ho0). unfold uE in Hbz. lia. }
  assert (HF0 : Forall (fact_ok E) (s_facts S)) by (destruct (sden_0 _ _ _ _ Hsd) as (_ & _ & _ & _ & _ & _ & X & _); exact X).
  destruct (Hgeo E (agree_refl _ _) HF0) as (Hrz & Ho & Hm & Hpo & Hbz).
  assert (Hpts : forall E', agree (s_next S) E E' -> Forall (fact_ok E') (s_facts S) -> forall w,
            (exists R', In R' pcs /\ uE E' (rg_base R') <= w < uE E' (rg_base R') + rsz E' R') <-> uE E' (rg_base R) <= w < uE E' (rg_base R) + rsz E' R).
  { intros E' Ha HF' w. destruct (Hgeo E' Ha HF') as (Hrz' & Ho' & Hm' & Hpo' & Hbz'). rewrite Hrz'. split.
    - intros (R' & HR' & Hw). destruct (pieces_pts E' R o z p m Ho' Hm' Hpo' Hbz' R' HR') as (_ & d & Hd0' & Hb' & Hdz). lia.
    - intros Hw. exact (pt_in_pieces E' R o z p m Ho' Hm' Hpo' Hbz' w Hw). }
  assert (Hbw2 : bases_wf (s_next S) (pcs ++ remove_nth i (s_rgs S)) = true).
  { unfold bases_wf in *. rewrite forallb_app. apply andb_true_intro. split.
    - unfold pcs, split_pieces. rewrite forallb_app. apply andb_true_intro. split.
      + destruct (Z.eqb o 0); cbn [forallb rg_base rg_size]; [reflexivity|]. rewrite forallb_forall in Hbw.
        destruct (andb_prop _ _ (Hbw R (nth_error_In _ _ Hi))) as [Hb1 _]. rewrite Hb1, lwf_lconst. reflexivity.
      + cbn [forallb rg_base rg_size]. rewrite Hwp, Hwm. cbn [andb].
        assert (Hl1 : lwf (s_next S) (ladd p m) = true) by (apply lwf_ladd; assumption).
        assert (Hl2 : lwf (s_next S) (lsub (lconst (z - o)) m) = true) by (apply lwf_lsub_s; [apply lwf_lconst | exact Hwm]).
        rewrite Hl1, Hl2. reflexivity.
    - apply forallb_forall. intros R0 HR0. rewrite forallb_forall in Hbw. exact (Hbw R0 (remove_nth_In i _ R0 HR0)). }
  assert (Hout : forall x, outside E (s_rgs S2) x <-> outside E (s_rgs S) x)
    by (intros x; cbn [S2 s_rgs]; exact (outside_split E (s_rgs S) i R pcs Hi (Hpts E (agree_refl _ _) HF0) x)).
  constructor; try assumption.
  - (* [comment removed for export] *)
    intros E'' Ha''. destruct (Hsd E'' Ha'') as (H1 & H2 & H3 & H4 & HG & HD & HF & H8).
    destruct (Hgeo E'' Ha'' HF) as (Hrz'' & Ho'' & Hm'' & Hpo'' & Hbz'').
    unfold sden0. cbn [S2 s_pc s_regs s_rgs s_facts s_resv].
    split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [|split; [|split; [exact HF | exact H8]]].
    + apply Forall_app. split.
      * rewrite Forall_forall in HG. exact (pieces_ok segs E'' _ R o z p m (HG R (nth_error_In _ _ Hi)) Hk Hrz'' Ho'' Hm'' Hpo'' Hbz'').
      * apply remove_nth_Forall. exact HG.
    + apply rgs_disj_app; [exact (pieces_disj E'' R o z p m Ho'' Hm'' Hpo'' Hbz'') | exact (rgs_disj_remove E'' _ i HD) |].
      intros R1 R2 HR1 HR2. destruct (remove_nth_pos _ i R2 HR2) as (j & Hne & Hj).
      pose proof (rgs_disj_nth E'' _ i j R R2 HD (not_eq_sym Hne) Hi Hj) as Hd2. unfold rg_disj in *. cbv zeta in *.
      destruct (pieces_pts E'' R o z p m Ho'' Hm'' Hpo'' Hbz'' R1 HR1) as (Hp1 & d & Hd1 & Hb1 & Hdz).
      fold (uE E'' (rg_base R1)) (uE E'' (rg_base R2)) (uE E'' (rg_base R)) in *. rewrite Hrz'' in Hd2. lia.
  - intros w Hw Hout' Hnow. apply (Hzr w Hw); [|exact Hnow]. exact (proj1 (Hout _) Hout').
  - (* [comment removed for export] *)
    cbn [S2 s_rgs]. apply Forall_app. split.
    + rewrite Forall_forall in Hrl |- *. intros R' HR'. destruct (Hrl R (nth_error_In _ _ Hi)) as [Hpos [Happ | (Hoff & HX & Hpc)]].
      * destruct (pieces_pts E R o z p m Ho Hm Hpo Hbz R' HR') as (Hp1 & d & Hd1 & Hb1 & Hdz). split; [exact Hp1|]. left.
        intros w Hw. apply Happ. rewrite Hrz. lia.
      * destruct (pieces_pts E R o z p m Ho Hm Hpo Hbz R' HR') as (Hp1 & d & Hd1 & Hb1 & Hdz). split; [exact Hp1|]. right.
        fold (uE E (rg_base R')) in *. fold (uE E (rg_base R)) in *. rewrite Hrz in HX, Hpc. split; [lia|]. split.
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
End Split.

(* [comment removed for export] *)
Definition tempty_b {A} (t : tree A) : bool := match t with TEmpty => true | _ => false end.
Definition rz_zero_post (S : sst) (j : nat) : option sst :=
  match nth_error (s_rgs S) j with
  | Some R => if (rkind_eqb (rg_kind R) RW && tempty_b (rg_cont R))%bool
              then Some (SST (s_pc S) (s_regs S) (upd_nth (s_rgs S) j (RG (rg_base R) (rg_size R) RZ TEmpty)) (s_facts S) (s_next S) (s_resv S))
              else None
  | None => None
  end.

Section RzZero.
Variable segs : list Segment.
Variable LIMIT : Z.
Variable mem0 : word -> option byte.

#[using="Type"] Theorem den_rz_zero : forall model0 E S M ms model j R S', DEN segs LIMIT model0 mem0 E S M ms model ->
  nth_error (s_rgs S) j = Some R -> rz_zero_post S j = Some S' ->
  (forall i, 0 <= i < rsz E R -> ms_mem ms (Z_to_bv 64 (uE E (rg_base R) + i)) = Some (Z_to_bv 8 0)) ->
  DEN segs LIMIT model0 mem0 E S' M ms model.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros model0 E S M ms model j R S' Hd Hj Hp Hz0. unfold rz_zero_post in Hp. rewrite Hj in Hp.
  destruct (rkind_eqb (rg_kind R) RW && tempty_b (rg_cont R))%bool eqn:Hb; [|discriminate]. injection Hp as <-.
  apply andb_prop in Hb as [Hkw Hte]. assert (Hk : rg_kind R = RW) by (destruct (rg_kind R); try discriminate; reflexivity).
  assert (Hc : rg_cont R = TEmpty) by (destruct (rg_cont R); [reflexivity | discriminate]).
  set (R' := RG (rg_base R) (rg_size R) RZ TEmpty).
  assert (Hb' : rg_base R' = rg_base R) by reflexivity. assert (Hs' : rg_size R' = rg_size R) by reflexivity.
  pose proof Hd as Hd0.
  destruct Hd0 as [Hsd Hwf Hbw Hh Hawf Hanz Hminv Hhoff Hres Hlim Hsp Hspok Hbrk Hsbrk Htid Hmaps Hgsh Hgtop Hivwf Hpd Hmres Hkind Hlzm Hzrsh Hzrm Hzr Hrl Hvmo Hproc Hfrz Hrom Hown Hblob].
  set (S2 := SST (s_pc S) (s_regs S) (upd_nth (s_rgs S) j R') (s_facts S) (s_next S) (s_resv S)).
  assert (Hshape : shape (s_rgs S2) = shape (s_rgs S)) by (cbn [S2 s_rgs]; exact (shape_upd (s_rgs S) j R' R Hj Hb' Hs')).
  assert (HbE : forall E'', agree (s_next S) E E'' -> uE E'' (rg_base R) = uE E (rg_base R) /\ rsz E'' R = rsz E R).
  { intros E'' Ha''. unfold uE, rsz. unfold bases_wf in Hbw. rewrite forallb_forall in Hbw. destruct (andb_prop _ _ (Hbw R (nth_error_In _ _ Hj))) as [Hb1 Hb2].
    rewrite (lden_agree_wf _ E E'' _ Hb1 Ha''), (lden_agree_wf _ E E'' _ Hb2 Ha''). split; reflexivity. }
  constructor; try assumption.
  - intros E'' Ha''. destruct (Hsd E'' Ha'') as (H1 & H2 & H3 & H4 & HG & HD & HF & H8).
    unfold sden0. cbn [S2 s_pc s_regs s_rgs s_facts s_resv].
    split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [|split; [|split; [exact HF | exact H8]]].
    + apply Forall_forall. intros R0 HR0. destruct (In_nth_error _ _ HR0) as (k & Hk0).
      destruct (Nat.eq_dec k j) as [->|Hne].
      * rewrite (nth_upd_same _ _ _ _ Hj) in Hk0. injection Hk0 as <-.
        rewrite Forall_forall in HG. pose proof (HG R (nth_error_In _ _ Hj)) as Hok.
        pose proof (rg_ok_visible segs (Hof E M model) (ms_mem ms) E'' R Hhoff Hok) as Hvis.
        destruct Hok as (Ho1 & Ho2 & Ho3 & Ho4). unfold rg_ok. cbn [rg_base rg_size rg_kind rg_cont]. fold (rsz E'' R).
        split; [exact Ho1|]. split; [exact Ho2|]. split.
        -- intros i Hi. specialize (Ho3 i Hi). rewrite Hk in Ho3. split; [exact Ho3|]. intros _.
           change (rg_base R') with (rg_base R). change (rsz E'' R') with (rsz E'' R) in Hi.
           unfold rd1. cbn [ms_mem restrict]. unfold mrestrict. fold (uE E'' (rg_base R)). rewrite (Hvis i Hi).
           destruct (HbE E'' Ha'') as [HbE1 HbE2]. fold (uE E'' (rg_base R)). rewrite HbE1.
           rewrite (Hz0 i ltac:(rewrite <- HbE2; exact Hi)). reflexivity.
        -- intros k0 v Hkv. unfold R' in Hkv. cbn [rg_cont] in Hkv. rewrite tget_empty in Hkv. discriminate.
      * rewrite (nth_upd_other _ _ _ _ (not_eq_sym Hne)) in Hk0. rewrite Forall_forall in HG. exact (HG R0 (nth_error_In _ _ Hk0)).
    + eapply rgs_disj_upd; [exact Hj | exact Hb' | exact Hs' | exact HD].
  - eapply bases_wf_shape; [|exact Hshape|exact Hbw]. cbn [S2 s_next]. lia.
  - intros w Hw Hout' Hnow. apply (Hzr w Hw); [|exact Hnow].
    exact (outside_agree_shape (s_next S) E E (s_rgs S) _ _ Hbw (agree_refl _ _) Hshape Hout').
  - exact (rl_ok_agree_shape (s_next S) E E model model (s_rgs S) _ Hbw (agree_refl _ _) Hshape eq_refl Hrl).
  - apply (frz_keep mem0 E E S S2 M M ms ms model model Hwf (agree_refl _ _) eq_refl eq_refl); [| | exact Hfrz].
    + intros w _ Ho'. unfold outside in *. rewrite Forall_forall in *. intros R0 HR0.
      destruct (In_nth_error _ _ HR0) as (k & Hk0). cbn [S2 s_rgs] in Hk0.
      destruct (Nat.eq_dec k j) as [->|Hne].
      * rewrite (nth_upd_same _ _ _ _ Hj) in Hk0. injection Hk0 as <-. unfold rsz in *. rewrite Hb', Hs'. exact (Ho' R (nth_error_In _ _ Hj)).
      * rewrite (nth_upd_other _ _ _ _ (not_eq_sym Hne)) in Hk0. exact (Ho' R0 (nth_error_In _ _ Hk0)).
    + intros w _ _. reflexivity.
  - apply (own_keep mem0 E E S S2 M M ms ms model model Hwf (agree_refl _ _) eq_refl); [| | | exact Hown].
    + intros w Ho'. exact (outside_agree_shape (s_next S) E E (s_rgs S) _ _ Hbw (agree_refl _ _) Hshape Ho').
    + intros w _. reflexivity.
    + intros x Hxx. exact Hxx.
Qed.
End RzZero.
