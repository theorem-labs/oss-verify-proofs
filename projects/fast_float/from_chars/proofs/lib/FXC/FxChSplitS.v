(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
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
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChSplit FxChTwoC.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxBacking OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChLib OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull.FxChSeg OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChSep OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull.FxChNode OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChFix OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChUnmap OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChain OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChain.FxChSys OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChSplit OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChTwoC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma rg_disj_sym : forall E R1 R2, rg_disj E R1 R2 -> rg_disj E R2 R1.
Proof. intros E R1 R2 H. unfold rg_disj in *. lia. Qed.
Lemma rgs_disj_iff : forall E l, rgs_disj E l <-> (forall i j R1 R2, i <> j -> nth_error l i = Some R1 -> nth_error l j = Some R2 -> rg_disj E R1 R2).
Proof.
  intros E l. split; [intros H i j R1 R2 Hne H1 H2; exact (rgs_disj_nth E l i j R1 R2 H Hne H1 H2)|].
  induction l as [|x r IH]; intros H; [exact I|]. split.
  - apply Forall_forall. intros y Hy. destruct (List.In_nth_error _ _ Hy) as (j & Hj). exact (H 0%nat (Datatypes.S j) x y ltac:(lia) eq_refl Hj).
  - apply IH. intros i j R1 R2 Hne H1 H2. exact (H (Datatypes.S i) (Datatypes.S j) R1 R2 ltac:(lia) H1 H2).
Qed.
Lemma rgs_disj_perm : forall E l l', Permutation l l' -> rgs_disj E l -> rgs_disj E l'.
Proof.
  intros E l l' Hp. induction Hp as [|x l l' Hp IH|x y l|l l' l'' H1 IH1 H2 IH2]; intros H.
  - exact I.
  - destruct H as [Hx Hr]. split; [|exact (IH Hr)]. rewrite Forall_forall in Hx |- *. intros z Hz. apply Hx. eapply Permutation_in; [symmetry; exact Hp | exact Hz].
  - destruct H as [Hy [Hx Hr]]. apply Forall_cons_iff in Hy as [Hyx Hy]. split.
    + constructor; [exact (rg_disj_sym E y x Hyx) | exact Hx].
    + split; [exact Hy | exact Hr].
  - exact (IH2 (IH1 H)).
Qed.
Lemma outside_perm : forall E l l' x, Permutation l l' -> outside E l x -> outside E l' x.
Proof. intros E l l' x Hp H. unfold outside in *. rewrite Forall_forall in H |- *. intros R HR. apply H. eapply Permutation_in; [symmetry; exact Hp | exact HR]. Qed.
Lemma bases_wf_perm : forall n l l', Permutation l l' -> bases_wf n l = true -> bases_wf n l' = true.
Proof.
  intros n l l' Hp H. unfold bases_wf in *. rewrite forallb_forall in H |- *. intros R HR. apply H. eapply Permutation_in; [symmetry; exact Hp | exact HR].
Qed.
Lemma Forall_perm' : forall {A} (P : A -> Prop) l l', Permutation l l' -> Forall P l -> Forall P l'.
Proof. intros A P l l' Hp H. rewrite Forall_forall in H |- *. intros x Hx. apply H. eapply Permutation_in; [symmetry; exact Hp | exact Hx]. Qed.

(* [comment removed for export] *)
Definition repl_nth {A} (i : nat) (pcs l : list A) : list A := firstn i l ++ pcs ++ skipn (Datatypes.S i) l.
Lemma remove_nth_split : forall {A} (l : list A) i x, nth_error l i = Some x -> remove_nth i l = firstn i l ++ skipn (Datatypes.S i) l.
Proof.
  intros A l. induction l as [|y r IH]; intros [|i] x H; cbn in H |- *; try discriminate; [reflexivity|].
  rewrite (IH i x H). reflexivity.
Qed.
Lemma repl_nth_perm : forall {A} (l pcs : list A) i x, nth_error l i = Some x -> Permutation (pcs ++ remove_nth i l) (repl_nth i pcs l).
Proof.
  intros A l pcs i x H. rewrite (remove_nth_split l i x H). unfold repl_nth.
  rewrite !app_assoc. apply Permutation_app_tail. apply Permutation_app_comm.
Qed.

(* [comment removed for export] *)
Definition lzero_b (l : lin) : bool := match is_const l with Some 0 => true | _ => false end.
Definition pcs_s (R : region) (p m : lin) : list region :=
  let b := rg_base R in let z := rg_size R in let k := rg_kind R in
  let d := lsub p b in let e := lsub (ladd b z) (ladd p m) in
  (if lzero_b d then [] else [RG b d k TEmpty]) ++ [RG p m k TEmpty] ++ (if lzero_b e then [] else [RG (ladd p m) e k TEmpty]).
Definition rk_split (R : region) : bool := match rg_kind R with RW => true | RZ => tempty_b (rg_cont R) | _ => false end.
Definition small_pos (fs : list fact) (l : lin) : bool := let '(lo, hi) := irange fs l in (Z.leb 1 lo && Z.ltb hi (2 ^ 62))%bool.
Definition split_s_chk (fs : list fact) (n : positive) (R : region) (p m : lin) : bool :=
  let b := rg_base R in let z := rg_size R in
  let d := lsub p b in let e := lsub (ladd b z) (ladd p m) in
  (rk_split R && lwf n p && lwf n m && Z.ltb (snd (irange fs b)) (2 ^ 62) && Z.ltb (snd (irange fs b) + snd (irange fs z)) two64 &&
   (lzero_b d || small_pos fs d) && small_pos fs m && (lzero_b e || small_pos fs e))%bool.
Definition split_s_post (S : sst) (i : nat) (p m : lin) : option sst :=
  match nth_error (s_rgs S) i with
  | Some R => if split_s_chk (s_facts S) (s_next S) R p m
              then Some (SST (s_pc S) (s_regs S) (repl_nth i (pcs_s R p m) (s_rgs S)) (s_facts S) (s_next S) (s_resv S))
              else None
  | None => None
  end.

Lemma lzero_b_u : forall E l, lzero_b l = true -> uE E l = 0.
Proof.
  intros E l H. unfold lzero_b in H. destruct (is_const l) as [z|] eqn:Hc; [|discriminate]. destruct z; try discriminate.
  unfold uE. rewrite (proj1 (is_const_sound E l 0 Hc)). reflexivity.
Qed.
Lemma small_pos_sound : forall E fs l, Forall (fact_ok E) fs -> small_pos fs l = true -> 1 <= uE E l < 2 ^ 62.
Proof.
  intros E fs l HF H. unfold small_pos in H. pose proof (irange_sound E fs l HF) as R. destruct (irange fs l) as [lo hi].
  apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. cbn [fst snd] in R. fold (uE E l) in R. lia.
Qed.
Lemma uE_ladd' : forall E a b, uE E (ladd a b) = (uE E a + uE E b) mod two64.
Proof. intros E a b. unfold uE. rewrite lden_ladd, bv_add_unsigned. unfold bv_wrap, bv_modulus. reflexivity. Qed.
Lemma uE_lsub' : forall E a b, uE E (lsub a b) = (uE E a - uE E b) mod two64.
Proof. intros E a b. unfold uE. rewrite lden_lsub, bv_sub_unsigned. unfold bv_wrap, bv_modulus. reflexivity. Qed.

(* [comment removed for export] *)
Record geo (E : valu) (R : region) (p m : lin) : Prop := GEO {
  g_bz : uE E (rg_base R) + rsz E R < two64;
  g_p  : uE E p = uE E (rg_base R) + uE E (lsub p (rg_base R)) /\ 0 <= uE E (lsub p (rg_base R)) < 2 ^ 62;
  g_d  : lzero_b (lsub p (rg_base R)) = false -> 1 <= uE E (lsub p (rg_base R));
  g_m  : 1 <= uE E m < 2 ^ 62;
  g_pm : uE E (ladd p m) = uE E p + uE E m;
  g_e  : uE E (ladd p m) + uE E (lsub (ladd (rg_base R) (rg_size R)) (ladd p m)) = uE E (rg_base R) + rsz E R;
  g_e1 : lzero_b (lsub (ladd (rg_base R) (rg_size R)) (ladd p m)) = false -> 1 <= uE E (lsub (ladd (rg_base R) (rg_size R)) (ladd p m)) }.

Lemma geo_of : forall E fs n R p m, Forall (fact_ok E) fs -> split_s_chk fs n R p m = true -> geo E R p m.
Proof.
  intros E fs n R p m HF H. unfold split_s_chk in H.
  repeat match type of H with ((_ && _)%bool = true) => apply andb_prop in H as [H ?Hc] end.
  match goal with Hx : Z.ltb _ two64 = true |- _ => apply Z.ltb_lt in Hx; rename Hx into Hnw end.
  match goal with Hx : Z.ltb (snd (irange fs (rg_base R))) (2 ^ 62) = true |- _ => apply Z.ltb_lt in Hx; rename Hx into Hb62 end.
  match goal with Hx : small_pos fs m = true |- _ => rename Hx into Hm end.
  match goal with Hx : (lzero_b (lsub p (rg_base R)) || _)%bool = true |- _ => rename Hx into Hd end.
  match goal with Hx : (lzero_b (lsub (ladd (rg_base R) (rg_size R)) (ladd p m)) || _)%bool = true |- _ => rename Hx into He end.
  pose proof (irange_sound E fs (rg_base R) HF) as Rb. pose proof (irange_sound E fs (rg_size R) HF) as Rz.
  fold (uE E (rg_base R)) in Rb. fold (uE E (rg_size R)) in Rz.
  pose proof (uE_range E (rg_base R)) as Ub. pose proof (uE_range E (rg_size R)) as Uz. pose proof (uE_range E p) as Up.
  pose proof (uE_range E m) as Um.
  pose proof (small_pos_sound E fs m HF Hm) as Hm'.
  assert (Hrz : rsz E R = uE E (rg_size R)) by reflexivity.
  assert (Hbz : uE E (rg_base R) + rsz E R < two64) by (unfold rsz; fold (uE E (rg_size R)); lia).
  (* [comment removed for export] *)
  assert (HD : uE E p = uE E (rg_base R) + uE E (lsub p (rg_base R)) /\ 0 <= uE E (lsub p (rg_base R)) < 2 ^ 62 /\
               (lzero_b (lsub p (rg_base R)) = false -> 1 <= uE E (lsub p (rg_base R)))).
  { destruct (lzero_b (lsub p (rg_base R))) eqn:Hz0.
    - pose proof (lzero_b_u E _ Hz0) as X. rewrite uE_lsub' in X.
      assert (Hpb : uE E p = uE E (rg_base R)).
      { destruct (Z_le_gt_dec (uE E (rg_base R)) (uE E p)) as [Hle|Hgt].
        - rewrite Z.mod_small in X by (unfold two64 in *; lia). lia.
        - rewrite <- (Z.mod_unique (uE E p - uE E (rg_base R)) two64 (-1) (uE E p - uE E (rg_base R) + two64)) in X by (unfold two64 in *; lia).
          unfold two64 in *. lia. }
      rewrite (lzero_b_u E _ Hz0). split; [lia|]. split; [lia|]. discriminate.
    - cbn [orb] in Hd. pose proof (small_pos_sound E fs _ HF Hd) as Hd'.
      destruct (small_diff E p (rg_base R) 1 (2 ^ 62) ltac:(lia)) as [[Y1 Y2]|[Y1 Y2]]; [|unfold two64 in *; lia].
      split; [lia|]. split; [lia|]. intros _. lia. }
  destruct HD as (HD1 & HD2 & HD3).
  assert (Hpm : uE E (ladd p m) = uE E p + uE E m).
  { rewrite uE_ladd'. apply Z.mod_small. unfold two64 in *. lia. }
  assert (HE : uE E (ladd p m) + uE E (lsub (ladd (rg_base R) (rg_size R)) (ladd p m)) = uE E (rg_base R) + rsz E R /\
               (lzero_b (lsub (ladd (rg_base R) (rg_size R)) (ladd p m)) = false -> 1 <= uE E (lsub (ladd (rg_base R) (rg_size R)) (ladd p m)))).
  { assert (Hbz' : uE E (ladd (rg_base R) (rg_size R)) = uE E (rg_base R) + rsz E R).
    { rewrite uE_ladd'. unfold rsz. fold (uE E (rg_size R)). apply Z.mod_small. unfold two64 in *. lia. }
    destruct (lzero_b (lsub (ladd (rg_base R) (rg_size R)) (ladd p m))) eqn:Hz1.
    - pose proof (lzero_b_u E _ Hz1) as X. rewrite uE_lsub', Hbz', Hpm in X. rewrite (lzero_b_u E _ Hz1). split; [|discriminate].
      destruct (Z_le_gt_dec (uE E p + uE E m) (uE E (rg_base R) + rsz E R)) as [Hle|Hgt].
      + rewrite Z.mod_small in X by (unfold two64 in *; lia). rewrite Hpm. lia.
      + rewrite <- (Z.mod_unique (uE E (rg_base R) + rsz E R - (uE E p + uE E m)) two64 (-1) (uE E (rg_base R) + rsz E R - (uE E p + uE E m) + two64)) in X
          by (unfold two64 in *; lia). unfold two64 in *. lia.
    - cbn [orb] in He. pose proof (small_pos_sound E fs _ HF He) as He'.
      destruct (small_diff E (ladd (rg_base R) (rg_size R)) (ladd p m) 1 (2 ^ 62) ltac:(lia)) as [[Y1 Y2]|[Y1 Y2]];
        rewrite Hbz', Hpm in Y1, Y2; [|unfold two64 in *; lia].
      split; [rewrite Hpm; lia | intros _; lia]. }
  destruct HE as [HE1 HE2].
  exact (GEO E R p m Hbz (conj HD1 HD2) HD3 Hm' Hpm HE1 HE2).
Qed.

Lemma rsz_RG : forall E b s k c, rsz E (RG b s k c) = uE E s.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma pcs_pts : forall E R p m, geo E R p m -> forall R', In R' (pcs_s R p m) ->
  rg_kind R' = rg_kind R /\ rg_cont R' = TEmpty /\ 1 <= rsz E R' /\
  exists d, 0 <= d /\ uE E (rg_base R') = uE E (rg_base R) + d /\ d + rsz E R' <= rsz E R.
Proof.
  intros E R p m G R' HR'. destruct G as [Hbz [Hp1 Hp2] Hd Hm Hpm He He1]. pose proof (uE_range E (lsub (ladd (rg_base R) (rg_size R)) (ladd p m))) as Ue. pose proof (uE_range E (rg_base R)) as Ub. unfold pcs_s in HR'. cbv zeta in HR'.
  apply in_app_iff in HR' as [HR'|HR'].
  - destruct (lzero_b (lsub p (rg_base R))) eqn:Hz; [destruct HR'|]. destruct HR' as [<-|[]].
    cbn [rg_kind rg_cont rg_base]. rewrite rsz_RG. split; [reflexivity|]. split; [reflexivity|]. split; [exact (Hd eq_refl)|].
    exists 0. split; [lia|]. split; [lia|]. lia.
  - apply in_app_iff in HR' as [HR'|HR'].
    + destruct HR' as [<-|[]]. cbn [rg_kind rg_cont rg_base]. rewrite rsz_RG. split; [reflexivity|]. split; [reflexivity|]. split; [lia|].
      exists (uE E (lsub p (rg_base R))). split; [lia|]. split; [lia|]. lia.
    + destruct (lzero_b (lsub (ladd (rg_base R) (rg_size R)) (ladd p m))) eqn:Hz; [destruct HR'|]. destruct HR' as [<-|[]].
      cbn [rg_kind rg_cont rg_base]. rewrite rsz_RG. split; [reflexivity|]. split; [reflexivity|]. split; [exact (He1 eq_refl)|].
      exists (uE E (lsub p (rg_base R)) + uE E m). split; [lia|]. split; [lia|]. lia.
Qed.
Lemma pt_in_pcs : forall E R p m, geo E R p m -> forall w, uE E (rg_base R) <= w < uE E (rg_base R) + rsz E R ->
  exists R', In R' (pcs_s R p m) /\ uE E (rg_base R') <= w < uE E (rg_base R') + rsz E R'.
Proof.
  intros E R p m G w Hw. destruct G as [Hbz [Hp1 Hp2] Hd Hm Hpm He He1]. pose proof (uE_range E (lsub (ladd (rg_base R) (rg_size R)) (ladd p m))) as Ue. pose proof (uE_range E (rg_base R)) as Ub. unfold pcs_s. cbv zeta.
  destruct (Z_lt_le_dec w (uE E p)) as [H1|H1].
  - destruct (lzero_b (lsub p (rg_base R))) eqn:Hz; [pose proof (lzero_b_u E _ Hz); lia|].
    exists (RG (rg_base R) (lsub p (rg_base R)) (rg_kind R) TEmpty). split; [apply in_or_app; left; left; reflexivity|].
    rewrite rsz_RG. cbn [rg_base]. lia.
  - destruct (Z_lt_le_dec w (uE E p + uE E m)) as [H2|H2].
    + exists (RG p m (rg_kind R) TEmpty). split; [apply in_or_app; right; apply in_or_app; left; left; reflexivity|]. rewrite rsz_RG. cbn [rg_base]. lia.
    + destruct (lzero_b (lsub (ladd (rg_base R) (rg_size R)) (ladd p m))) eqn:Hz; [pose proof (lzero_b_u E _ Hz); lia|].
      exists (RG (ladd p m) (lsub (ladd (rg_base R) (rg_size R)) (ladd p m)) (rg_kind R) TEmpty).
      split; [apply in_or_app; right; apply in_or_app; right; left; reflexivity|]. rewrite rsz_RG. cbn [rg_base]. lia.
Qed.
Lemma pcs_disj : forall E R p m, geo E R p m -> rgs_disj E (pcs_s R p m).
Proof.
  intros E R p m G. destruct G as [Hbz [Hp1 Hp2] Hd Hm Hpm He He1]. pose proof (uE_range E (lsub (ladd (rg_base R) (rg_size R)) (ladd p m))) as Ue. pose proof (uE_range E (rg_base R)) as Ub. unfold pcs_s. cbv zeta.
  destruct (lzero_b (lsub p (rg_base R))) eqn:Hz0; destruct (lzero_b (lsub (ladd (rg_base R) (rg_size R)) (ladd p m))) eqn:Hz1;
    cbn [app rgs_disj]; repeat split; repeat constructor; unfold rg_disj; cbv zeta; cbn [rg_base]; rewrite ?rsz_RG; fold (uE E p) (uE E (ladd p m));
    fold (uE E (rg_base R)); rewrite ?Hpm; lia.
Qed.
Lemma pcs_ok : forall segs E mem R p m, geo E R p m -> rg_ok segs E mem R -> rk_split R = true -> Forall (rg_ok segs E mem) (pcs_s R p m).
Proof.
  intros segs E mem R p m G Hok Hk. apply Forall_forall. intros R' HR'.
  destruct (pcs_pts E R p m G R' HR') as (Hk' & Hc' & Hs' & d & Hd0 & Hb' & Hdz).
  destruct Hok as (Hs & Hw & Hbytes & Hc). fold (uE E (rg_base R)) in Hw, Hbytes, Hc.
  unfold rg_ok. fold (uE E (rg_base R')). rewrite Hb', Hk', Hc'.
  split; [lia|]. split; [lia|]. split.
  - intros i Hi. specialize (Hbytes (d + i) ltac:(lia)). replace (uE E (rg_base R) + d + i) with (uE E (rg_base R) + (d + i)) by lia.
    unfold rk_split in Hk. destruct (rg_kind R); try discriminate; [exact Hbytes|]. destruct Hbytes as [H1 H2]. split; [exact H1|].
    intros _. apply H2. unfold tempty_b in Hk. destruct (rg_cont R); [apply tget_empty | discriminate].
  - intros k v Hkv. rewrite tget_empty in Hkv. discriminate.
Qed.
Lemma pcs_rl : forall E model R p m, geo E R p m -> rl_ok E model R -> Forall (rl_ok E model) (pcs_s R p m).
Proof.
  intros E model R p m G Hrl. apply Forall_forall. intros R' HR'.
  destruct (pcs_pts E R p m G R' HR') as (_ & _ & Hs' & d & Hd0 & Hb' & Hdz).
  destruct Hrl as [Hpos [Happ | (Hoff & HX & Hpc)]]; unfold rl_ok; cbv zeta; rewrite Hb'; split; [lia| |lia|].
  - left. intros w Hw. apply Happ. lia.
  - right. fold (uE E (rg_base R)) in *. split; [lia|]. split.
    + intros x Hx. apply HX. lia.
    + intros w Hw. apply Hpc. lia.
Qed.
Lemma pcs_lwf : forall n R p m, lwf n (rg_base R) = true -> lwf n (rg_size R) = true -> lwf n p = true -> lwf n m = true ->
  bases_wf n (pcs_s R p m) = true.
Proof.
  intros n R p m Hb Hz Hp Hm. unfold bases_wf, pcs_s. cbv zeta. rewrite !forallb_app.
  assert (Hd : lwf n (lsub p (rg_base R)) = true) by (apply lwf_lsub_s; assumption).
  assert (Hpm : lwf n (ladd p m) = true) by (apply lwf_ladd; assumption).
  assert (He : lwf n (lsub (ladd (rg_base R) (rg_size R)) (ladd p m)) = true) by (apply lwf_lsub_s; [apply lwf_ladd; assumption | exact Hpm]).
  destruct (lzero_b (lsub p (rg_base R))); destruct (lzero_b (lsub (ladd (rg_base R) (rg_size R)) (ladd p m)));
    cbn [forallb rg_base rg_size]; rewrite ?Hb, ?Hd, ?Hp, ?Hm, ?Hpm, ?He; reflexivity.
Qed.

Section Split.
Variable segs : list Segment.
Variable LIMIT : Z.
Variable mem0 : word -> option byte.

#[using="Type"] Theorem den_split_s : forall model0 E S M ms model i p m S', DEN segs LIMIT model0 mem0 E S M ms model -> split_s_post S i p m = Some S' ->
  DEN segs LIMIT model0 mem0 E S' M ms model.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros model0 E S M ms model i p m S' Hd Hp. unfold split_s_post in Hp.
  destruct (nth_error (s_rgs S) i) as [R|] eqn:Hi; [|discriminate].
  destruct (split_s_chk (s_facts S) (s_next S) R p m) eqn:Hc; [|discriminate]. injection Hp as <-.
  assert (Hk : rk_split R = true) by (unfold split_s_chk in Hc; repeat match type of Hc with ((_ && _)%bool = true) => apply andb_prop in Hc as [Hc ?Hx] end; exact Hc).
  assert (Hwpm : lwf (s_next S) p = true /\ lwf (s_next S) m = true).
  { unfold split_s_chk in Hc. repeat match type of Hc with ((_ && _)%bool = true) => apply andb_prop in Hc as [Hc ?Hx] end. split; assumption. }
  pose proof Hd as Hd0.
  destruct Hd0 as [Hsd Hwf Hbw Hh Hawf Hanz Hminv Hhoff Hres Hlim Hsp Hspok Hbrk Hsbrk Htid Hmaps Hgsh Hgtop Hivwf Hpd Hmres Hkind Hlzm Hzrsh Hzrm Hzr Hrl Hvmo Hproc Hfrz Hrom Hown Hblob].
  set (pcs := pcs_s R p m) in *.
  set (S2 := SST (s_pc S) (s_regs S) (repl_nth i pcs (s_rgs S)) (s_facts S) (s_next S) (s_resv S)).
  pose proof (repl_nth_perm (s_rgs S) pcs i R Hi) as Hperm.
  assert (HF0 : Forall (fact_ok E) (s_facts S)) by (destruct (sden_0 _ _ _ _ Hsd) as (_ & _ & _ & _ & _ & _ & X & _); exact X).
  assert (Hgeo : forall E', agree (s_next S) E E' -> Forall (fact_ok E') (s_facts S) -> geo E' R p m)
    by (intros E' _ HF'; exact (geo_of E' _ _ R p m HF' Hc)).
  pose proof (Hgeo E (agree_refl _ _) HF0) as G0.
  assert (Hpts : forall E', geo E' R p m -> forall w,
            (exists R', In R' pcs /\ uE E' (rg_base R') <= w < uE E' (rg_base R') + rsz E' R') <-> uE E' (rg_base R) <= w < uE E' (rg_base R) + rsz E' R).
  { intros E' G w. split.
    - intros (R' & HR' & Hw). destruct (pcs_pts E' R p m G R' HR') as (_ & _ & _ & d & Hd0' & Hb' & Hdz). lia.
    - intros Hw. exact (pt_in_pcs E' R p m G w Hw). }
  assert (Hbw2 : bases_wf (s_next S) (repl_nth i pcs (s_rgs S)) = true).
  { apply (bases_wf_perm _ _ _ Hperm). unfold bases_wf in *. rewrite forallb_app. apply andb_true_intro. split.
    - rewrite forallb_forall in Hbw. destruct (andb_prop _ _ (Hbw R (nth_error_In _ _ Hi))) as [Hb1 Hb2].
      exact (pcs_lwf _ R p m Hb1 Hb2 (proj1 Hwpm) (proj2 Hwpm)).
    - apply forallb_forall. intros R0 HR0. rewrite forallb_forall in Hbw. exact (Hbw R0 (remove_nth_In i _ R0 HR0)). }
  assert (Hout : forall x, outside E (s_rgs S2) x <-> outside E (s_rgs S) x).
  { intros x. cbn [S2 s_rgs]. split.
    - intros Ho'. apply (outside_split E (s_rgs S) i R pcs Hi (Hpts E G0) x). exact (outside_perm E _ _ x (Permutation_sym Hperm) Ho').
    - intros Ho'. apply (outside_perm E _ _ x Hperm). exact (proj2 (outside_split E (s_rgs S) i R pcs Hi (Hpts E G0) x) Ho'). }
  constructor; try assumption.
  - intros E'' Ha''. destruct (Hsd E'' Ha'') as (H1 & H2 & H3 & H4 & HG & HD & HF & H8).
    pose proof (Hgeo E'' Ha'' HF) as G''.
    unfold sden0. cbn [S2 s_pc s_regs s_rgs s_facts s_resv].
    split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [|split; [|split; [exact HF | exact H8]]].
    + apply (Forall_perm' _ _ _ Hperm). apply Forall_app. split.
      * rewrite Forall_forall in HG. exact (pcs_ok segs E'' _ R p m G'' (HG R (nth_error_In _ _ Hi)) Hk).
      * apply remove_nth_Forall. exact HG.
    + apply (rgs_disj_perm E'' _ _ Hperm).
      apply rgs_disj_app; [exact (pcs_disj E'' R p m G'') | exact (rgs_disj_remove E'' _ i HD) |].
      intros R1 R2 HR1 HR2. destruct (remove_nth_pos _ i R2 HR2) as (j & Hne & Hj).
      pose proof (rgs_disj_nth E'' _ i j R R2 HD (not_eq_sym Hne) Hi Hj) as Hd2. unfold rg_disj in *. cbv zeta in *.
      destruct (pcs_pts E'' R p m G'' R1 HR1) as (_ & _ & Hp1 & d & Hd1 & Hb1 & Hdz).
      fold (uE E'' (rg_base R1)) (uE E'' (rg_base R2)) (uE E'' (rg_base R)) in *. lia.
  - intros w Hw Hout' Hnow. apply (Hzr w Hw); [|exact Hnow]. exact (proj1 (Hout _) Hout').
  - cbn [S2 s_rgs]. apply (Forall_perm' _ _ _ Hperm). apply Forall_app. split.
    + rewrite Forall_forall in Hrl. exact (pcs_rl E model R p m G0 (Hrl R (nth_error_In _ _ Hi))).
    + apply remove_nth_Forall. exact Hrl.
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
(* [comment removed for export] *)
Definition hull_class (fs : list fact) (b e : lin) : bool :=
  let '(blo, _) := irange fs b in
  let '(_, ehi) := irange fs e in
  ((Z.leb SH_LO blo && Z.leb ehi SH_HI) || Z.leb ehi SH_LO || Z.leb SH_HI blo)%bool.
Definition merge2_chk (fs : list fact) (R1 R2 : region) : bool :=
  let shi := snd (irange fs (rg_size R1)) + snd (irange fs (rg_size R2)) in
  (lin_eqb (rg_base R2) (ladd (rg_base R1) (rg_size R1)) && rkind_eqb (rg_kind R1) (rg_kind R2) &&
   tempty_b (rg_cont R1) && tempty_b (rg_cont R2) && Z.ltb (snd (irange fs (rg_base R1)) + shi) two64 &&
   (* [comment removed for export] *)
   (if hull_class fs (rg_base R1) (ladd (rg_base R1) (ladd (rg_size R1) (rg_size R2))) then true else twoc_ns fs (rg_base R1) shi))%bool.
Definition repl2 {A} (i : nat) (x : A) (l : list A) : list A := firstn i l ++ [x] ++ skipn (i + 2) l.
Definition merge2_post (S : sst) (i : nat) : option sst :=
  match nth_error (s_rgs S) i, nth_error (s_rgs S) (Datatypes.S i) with
  | Some R1, Some R2 =>
      if merge2_chk (s_facts S) R1 R2
      then Some (SST (s_pc S) (s_regs S) (repl2 i (RG (rg_base R1) (ladd (rg_size R1) (rg_size R2)) (rg_kind R1) TEmpty) (s_rgs S))
                     (s_facts S) (s_next S) (s_resv S))
      else None
  | _, _ => None
  end.
Definition merge_s_post (S : sst) (i n : nat) : option sst :=
  match n with
  | 2%nat => merge2_post S i
  | 3%nat => match merge2_post S (Datatypes.S i) with Some S1 => merge2_post S1 i | None => None end
  | _ => None
  end.

Lemma repl2_perm : forall {A} (l : list A) i x y z, nth_error l i = Some y -> nth_error l (Datatypes.S i) = Some z ->
  Permutation l (y :: z :: (firstn i l ++ skipn (i + 2) l)) /\ Permutation (repl2 i x l) (x :: (firstn i l ++ skipn (i + 2) l)).
Proof.
  intros A l i x y z Hy Hz. assert (Hl : l = firstn i l ++ y :: z :: skipn (i + 2) l).
  { revert i Hy Hz. induction l as [|a r IH]; intros [|i] Hy Hz; cbn in Hy, Hz |- *; try discriminate.
    - injection Hy as <-. destruct r as [|b r']; [discriminate|]. injection Hz as <-. reflexivity.
    - f_equal. exact (IH i Hy Hz). }
  split.
  - rewrite Hl at 1. apply Permutation_sym. apply Permutation_cons_app. apply Permutation_cons_app. reflexivity.
  - unfold repl2. cbn [app]. apply Permutation_sym. apply Permutation_cons_app. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma merge2_geo : forall E fs R1 R2, Forall (fact_ok E) fs -> merge2_chk fs R1 R2 = true ->
  uE E (rg_base R2) = uE E (rg_base R1) + rsz E R1 /\ uE E (rg_base R1) + rsz E R1 + rsz E R2 < two64 /\
  uE E (ladd (rg_size R1) (rg_size R2)) = rsz E R1 + rsz E R2 /\ rg_kind R2 = rg_kind R1 /\ rg_cont R1 = TEmpty /\ rg_cont R2 = TEmpty /\
  ((SH_LO <= uE E (rg_base R1) /\ uE E (rg_base R1) + rsz E R1 + rsz E R2 <= SH_HI) \/
   uE E (rg_base R1) + rsz E R1 + rsz E R2 <= SH_LO \/ SH_HI <= uE E (rg_base R1)).
Proof.
  intros E fs R1 R2 HF H. unfold merge2_chk in H. cbv zeta in H.
  apply andb_prop in H as [H Hcl]. apply andb_prop in H as [H Hnw]. apply andb_prop in H as [H Hc2]. apply andb_prop in H as [H Hc1].
  apply andb_prop in H as [Hb Hk]. apply Z.ltb_lt in Hnw. apply lin_eqb_eq in Hb.
  pose proof (irange_sound E fs (rg_base R1) HF) as Rb. pose proof (irange_sound E fs (rg_size R1) HF) as Rz1.
  pose proof (irange_sound E fs (rg_size R2) HF) as Rz2.
  fold (uE E (rg_base R1)) in Rb. fold (uE E (rg_size R1)) in Rz1. fold (uE E (rg_size R2)) in Rz2.
  assert (Hr1 : rsz E R1 = uE E (rg_size R1)) by reflexivity. assert (Hr2 : rsz E R2 = uE E (rg_size R2)) by reflexivity.
  pose proof (uE_range E (rg_base R1)). pose proof (uE_range E (rg_size R1)). pose proof (uE_range E (rg_size R2)).
  split; [rewrite Hb, uE_ladd'; rewrite Z.mod_small by (unfold two64 in *; lia); lia|].
  split; [lia|]. split; [rewrite uE_ladd'; rewrite Z.mod_small by (unfold two64 in *; lia); lia|].
  split; [destruct (rg_kind R1), (rg_kind R2); try discriminate; reflexivity|].
  split; [unfold tempty_b in Hc1; destruct (rg_cont R1); [reflexivity | discriminate]|].
  split; [unfold tempty_b in Hc2; destruct (rg_cont R2); [reflexivity | discriminate]|].
  pose proof (irange_sound E fs (ladd (rg_base R1) (ladd (rg_size R1) (rg_size R2))) HF) as Re.
  fold (uE E (ladd (rg_base R1) (ladd (rg_size R1) (rg_size R2)))) in Re.
  assert (He : uE E (ladd (rg_base R1) (ladd (rg_size R1) (rg_size R2))) = uE E (rg_base R1) + rsz E R1 + rsz E R2).
  { rewrite uE_ladd', uE_ladd'. rewrite (Z.mod_small (uE E (rg_size R1) + uE E (rg_size R2))) by (unfold two64 in *; lia).
    rewrite Z.mod_small by (unfold two64 in *; lia). rewrite Hr1, Hr2. lia. }
  rewrite He in Re.
  destruct (hull_class fs (rg_base R1) (ladd (rg_base R1) (ladd (rg_size R1) (rg_size R2)))) eqn:Hhc.
  2:{ (* [comment removed for export] *)
      destruct (twoc_ns_sound E fs (rg_base R1) _ HF Hcl ltac:(pose proof (uE_range E (rg_size R1)); pose proof (uE_range E (rg_size R2)); lia)) as [L|[Hh _]];
        [right; left; lia | right; right; lia]. }
  clear Hcl. rename Hhc into Hcl.
  unfold hull_class in Hcl. destruct (irange fs (rg_base R1)) as [blo bhi] eqn:Hir. cbn [fst snd] in Rb.
  destruct (irange fs (ladd (rg_base R1) (ladd (rg_size R1) (rg_size R2)))) as [elo ehi] eqn:Hie. cbn [fst snd] in Re.
  apply orb_prop in Hcl as [Hcl|Hcl]; [apply orb_prop in Hcl as [Hcl|Hcl]|].
  - apply andb_prop in Hcl as [X1 X2]. apply Z.leb_le in X1, X2. left. lia.
  - apply Z.leb_le in Hcl. right; left. lia.
  - apply Z.leb_le in Hcl. right; right. lia.
Qed.

(* [comment removed for export] *)
Definition kbyte (segs : list Segment) (m : word -> option byte) (k : rkind) (a : Z) : Prop :=
  match k with
  | RW => rd1 segs m (Z_to_bv 64 a) <> None /\ wview segs m (Z_to_bv 64 a) <> None
  | RO => m (Z_to_bv 64 a) = None /\ seg_rom segs (Z_to_bv 64 a) <> None
  | RZ => (rd1 segs m (Z_to_bv 64 a) <> None /\ wview segs m (Z_to_bv 64 a) <> None) /\ rd1 segs m (Z_to_bv 64 a) = Some (Z_to_bv 8 0)
  | RI => (rd1 segs m (Z_to_bv 64 a) <> None /\ wview segs m (Z_to_bv 64 a) <> None) /\ rd1 segs m (Z_to_bv 64 a) = seg_rom segs (Z_to_bv 64 a)
  | RT => rd1 segs m (Z_to_bv 64 a) <> None
  end.
Lemma kbyte_of_rg : forall segs E m R i, rg_ok segs E m R -> rg_cont R = TEmpty -> 0 <= i < rsz E R ->
  kbyte segs m (rg_kind R) (uE E (rg_base R) + i).
Proof.
  intros segs E m R i (_ & _ & H & _) Hc Hi. specialize (H i Hi). unfold kbyte. unfold uE. rewrite Hc in H.
  destruct (rg_kind R); try exact H; (destruct H as [H1 H2]; split; [exact H1 | apply H2; apply tget_empty]).
Qed.
Lemma rg_of_kbyte : forall segs E m b s k, 0 <= rsz E (RG b s k TEmpty) -> uE E b + rsz E (RG b s k TEmpty) <= two64 ->
  (forall i, 0 <= i < rsz E (RG b s k TEmpty) -> kbyte segs m k (uE E b + i)) -> rg_ok segs E m (RG b s k TEmpty).
Proof.
  intros segs E m b s k H1 H2 H. unfold rg_ok. cbn [rg_base rg_kind rg_cont]. fold (uE E b).
  split; [exact H1|]. split; [exact H2|]. split.
  - intros i Hi. specialize (H i Hi). unfold kbyte in H. destruct k; try exact H; (destruct H as [X1 X2]; split; [exact X1 | intros _; exact X2]).
  - intros p v Hp. rewrite tget_empty in Hp. discriminate.
Qed.

Section Merge.
Variable segs : list Segment.
Variable LIMIT : Z.
Variable mem0 : word -> option byte.

#[using="Type"] Theorem den_merge2 : forall model0 E S M ms model i S', DEN segs LIMIT model0 mem0 E S M ms model -> merge2_post S i = Some S' ->
  DEN segs LIMIT model0 mem0 E S' M ms model.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros model0 E S M ms model i S' Hd Hp. unfold merge2_post in Hp.
  destruct (nth_error (s_rgs S) i) as [R1|] eqn:Hi1; [|discriminate].
  destruct (nth_error (s_rgs S) (Datatypes.S i)) as [R2|] eqn:Hi2; [|discriminate].
  destruct (merge2_chk (s_facts S) R1 R2) eqn:Hc; [|discriminate]. injection Hp as <-.
  pose proof Hd as Hd0.
  destruct Hd0 as [Hsd Hwf Hbw Hh Hawf Hanz Hminv Hhoff Hres Hlim Hsp Hspok Hbrk Hsbrk Htid Hmaps Hgsh Hgtop Hivwf Hpd Hmres Hkind Hlzm Hzrsh Hzrm Hzr Hrl Hvmo Hproc Hfrz Hrom Hown Hblob].
  set (Rm := RG (rg_base R1) (ladd (rg_size R1) (rg_size R2)) (rg_kind R1) TEmpty) in *.
  set (rest := firstn i (s_rgs S) ++ skipn (i + 2) (s_rgs S)) in *.
  destruct (repl2_perm (s_rgs S) i Rm R1 R2 Hi1 Hi2) as [Hpa Hpb]. fold rest in Hpa, Hpb.
  set (S2 := SST (s_pc S) (s_regs S) (repl2 i Rm (s_rgs S)) (s_facts S) (s_next S) (s_resv S)).
  assert (HF0 : Forall (fact_ok E) (s_facts S)) by (destruct (sden_0 _ _ _ _ Hsd) as (_ & _ & _ & _ & _ & _ & X & _); exact X).
  assert (Hrsm : forall E', Forall (fact_ok E') (s_facts S) -> rsz E' Rm = rsz E' R1 + rsz E' R2).
  { intros E' HF'. destruct (merge2_geo E' _ R1 R2 HF' Hc) as (_ & _ & X & _). exact X. }
  (* [comment removed for export] *)
  assert (Hpts : forall E', Forall (fact_ok E') (s_facts S) -> forall w : Z,
            (uE E' (rg_base Rm) <= w < uE E' (rg_base Rm) + rsz E' Rm) <->
            ((uE E' (rg_base R1) <= w < uE E' (rg_base R1) + rsz E' R1) \/ (uE E' (rg_base R2) <= w < uE E' (rg_base R2) + rsz E' R2))).
  { intros E' HF' w. destruct (merge2_geo E' _ R1 R2 HF' Hc) as (G1 & G2 & G3 & _). rewrite (Hrsm E' HF'). cbn [rg_base Rm].
    pose proof (uE_range E' (rg_size R1)). pose proof (uE_range E' (rg_size R2)). change (rsz E' R1) with (uE E' (rg_size R1)) in *. change (rsz E' R2) with (uE E' (rg_size R2)) in *. lia. }
  (* [comment removed for export] *)
  assert (Hout : forall x, outside E (repl2 i Rm (s_rgs S)) x <-> outside E (s_rgs S) x).
  { intros x. split; intros Ho'.
    - apply (outside_perm E _ _ x (Permutation_sym Hpa)). apply (outside_perm E _ _ x Hpb) in Ho'.
      unfold outside in Ho' |- *. apply Forall_cons_iff in Ho' as [Hm Hr].
      pose proof (Hpts E HF0 (bv_unsigned x)) as X. fold (uE E (rg_base Rm)) (uE E (rg_base R1)) (uE E (rg_base R2)) in *.
      constructor; [|constructor; [|exact Hr]]; unfold uE in *; lia.
    - apply (outside_perm E _ _ x (Permutation_sym Hpb)). apply (outside_perm E _ _ x Hpa) in Ho'.
      unfold outside in Ho' |- *. apply Forall_cons_iff in Ho' as [H1 Ho']. apply Forall_cons_iff in Ho' as [H2 Hr].
      pose proof (Hpts E HF0 (bv_unsigned x)) as X. unfold uE in *. constructor; [lia | exact Hr]. }
  assert (Hbw2 : bases_wf (s_next S) (repl2 i Rm (s_rgs S)) = true).
  { apply (bases_wf_perm _ _ _ (Permutation_sym Hpb)). apply (bases_wf_perm _ _ _ Hpa) in Hbw.
    unfold bases_wf in *. cbn [forallb] in Hbw |- *. apply andb_prop in Hbw as [B1 Hbw]. apply andb_prop in Hbw as [B2 Hbw].
    apply andb_prop in B1 as [B1b B1s]. apply andb_prop in B2 as [_ B2s]. cbn [Rm rg_base rg_size]. rewrite B1b, (lwf_ladd _ _ _ B1s B2s). exact Hbw. }
  constructor; try assumption.
  - intros E'' Ha''. destruct (Hsd E'' Ha'') as (H1 & H2 & H3 & H4 & HG & HD & HF & H8).
    destruct (merge2_geo E'' _ R1 R2 HF Hc) as (G1 & G2 & G3 & Gk & Gc1 & Gc2 & _).
    unfold sden0. cbn [S2 s_pc s_regs s_rgs s_facts s_resv].
    split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [|split; [|split; [exact HF | exact H8]]].
    + apply (Forall_perm' _ _ _ (Permutation_sym Hpb)). apply (Forall_perm' _ _ _ Hpa) in HG.
      apply Forall_cons_iff in HG as [G1ok HG]. apply Forall_cons_iff in HG as [G2ok HG]. constructor; [|exact HG].
      pose proof G1ok as (F1 & F2 & _ & _). pose proof G2ok as (F3 & F4 & _ & _).
      assert (Hrs'' : rsz E'' Rm = rsz E'' R1 + rsz E'' R2) by exact (Hrsm E'' HF).
      apply rg_of_kbyte; fold Rm; [rewrite Hrs''; lia | fold (uE E'' (rg_base R1)); rewrite Hrs''; unfold uE in *; lia|].
      intros j Hj. rewrite Hrs'' in Hj. fold (uE E'' (rg_base R1)).
      destruct (Z_lt_le_dec j (rsz E'' R1)) as [Hl|Hl].
      * exact (kbyte_of_rg segs E'' _ R1 j G1ok Gc1 ltac:(lia)).
      * pose proof (kbyte_of_rg segs E'' _ R2 (j - rsz E'' R1) G2ok Gc2 ltac:(lia)) as X. rewrite Gk, G1 in X.
        replace (uE E'' (rg_base R1) + rsz E'' R1 + (j - rsz E'' R1)) with (uE E'' (rg_base R1) + j) in X by lia. exact X.
    + apply (rgs_disj_perm E'' _ _ (Permutation_sym Hpb)). apply (rgs_disj_perm E'' _ _ Hpa) in HD.
      destruct HD as [Hd1 [Hd2 Hdr]]. apply Forall_cons_iff in Hd1 as [_ Hd1]. split; [|exact Hdr].
      apply Forall_forall. intros R0 HR0. rewrite Forall_forall in Hd1, Hd2. pose proof (Hd1 R0 HR0) as X1. pose proof (Hd2 R0 HR0) as X2.
      (* [comment removed for export] *)
      assert (Hpos : 0 < rsz E'' R0).
      { apply (Forall_perm' _ _ _ Hpa) in Hrl. apply Forall_cons_iff in Hrl as [_ Hrl]. apply Forall_cons_iff in Hrl as [_ Hrl].
        rewrite Forall_forall in Hrl. destruct (Hrl R0 HR0) as [Hp0 _].
        unfold bases_wf in Hbw. rewrite forallb_forall in Hbw.
        assert (HR0' : In R0 (s_rgs S)) by (eapply Permutation_in; [symmetry; exact Hpa | right; right; exact HR0]).
        destruct (andb_prop _ _ (Hbw R0 HR0')) as [_ Bs]. unfold rsz in *. rewrite (lden_agree_wf _ E E'' _ Bs Ha''). exact Hp0. }
      unfold rg_disj in *. cbv zeta in *. cbn [Rm rg_base]. rewrite (Hrsm E'' HF). fold (uE E'' (rg_base R1)) (uE E'' (rg_base R2)) (uE E'' (rg_base R0)) in *. lia.
  - intros w Hw Hout' Hnow. apply (Hzr w Hw); [|exact Hnow]. exact (proj1 (Hout _) Hout').
  - (* [comment removed for export] *)
    cbn [S2 s_rgs]. apply (Forall_perm' _ _ _ (Permutation_sym Hpb)). apply (Forall_perm' _ _ _ Hpa) in Hrl.
    apply Forall_cons_iff in Hrl as [Hr1 Hrl]. apply Forall_cons_iff in Hrl as [Hr2 Hrl]. constructor; [|exact Hrl].
    destruct (merge2_geo E _ R1 R2 HF0 Hc) as (G1 & G2 & G3 & Gk & Gc1 & Gc2 & Gcl).
    pose proof (Hrsm E HF0) as HsR.
    destruct Hr1 as [Hp1 Hc1']. destruct Hr2 as [Hp2 Hc2']. unfold rl_ok. cbv zeta. cbn [Rm rg_base]. rewrite HsR. split; [lia|].
    fold (uE E (rg_base R1)) (uE E (rg_base R2)) in *.
    destruct Gcl as [(X1 & X2) | [X1 | X1]].
    + (* [comment removed for export] *)
      destruct Hc1' as [Happ1 | (Ho1 & HX1 & Hpc1)]; [exfalso; destruct (Happ1 (uE E (rg_base R1)) ltac:(lia)) as (_ & Hs & _); unfold in_shadow in Hs;
        apply andb_false_iff in Hs as [Hs|Hs]; [apply Z.leb_gt in Hs | apply Z.ltb_ge in Hs]; lia|].
      destruct Hc2' as [Happ2 | (Ho2 & HX2 & Hpc2)]; [exfalso; destruct (Happ2 (uE E (rg_base R2)) ltac:(lia)) as (_ & Hs & _); unfold in_shadow in Hs;
        apply andb_false_iff in Hs as [Hs|Hs]; [apply Z.leb_gt in Hs | apply Z.ltb_ge in Hs]; lia|].
      right. split; [exact Ho1|]. split.
      * intros x Hx. destruct (Z_lt_le_dec x (8 * (uE E (rg_base R1) - SH_OFF + rsz E R1))) as [Hl|Hl]; [apply HX1; lia | apply HX2; lia].
      * intros w Hw. destruct (Z_lt_le_dec w (uE E (rg_base R1) + rsz E R1)) as [Hl|Hl]; [apply Hpc1; lia | apply Hpc2; lia].
    + (* [comment removed for export] *)
      left. destruct Hc1' as [Happ1 | (_ & _ & Hpc1)]; [|exfalso; destruct (Hpc1 (uE E (rg_base R1)) ltac:(lia)) as (Hs & _); unfold in_shadow in Hs;
        apply andb_prop in Hs as [Hs1 Hs2]; apply Z.leb_le in Hs1; apply Z.ltb_lt in Hs2; lia].
      destruct Hc2' as [Happ2 | (_ & _ & Hpc2)]; [|exfalso; destruct (Hpc2 (uE E (rg_base R2)) ltac:(lia)) as (Hs & _); unfold in_shadow in Hs;
        apply andb_prop in Hs as [Hs1 Hs2]; apply Z.leb_le in Hs1; apply Z.ltb_lt in Hs2; lia].
      intros w Hw. destruct (Z_lt_le_dec w (uE E (rg_base R1) + rsz E R1)) as [Hl|Hl]; [apply Happ1; lia | apply Happ2; lia].
    + (* [comment removed for export] *)
      left. destruct Hc1' as [Happ1 | (_ & _ & Hpc1)]; [|exfalso; destruct (Hpc1 (uE E (rg_base R1)) ltac:(lia)) as (Hs & _); unfold in_shadow in Hs;
        apply andb_prop in Hs as [Hs1 Hs2]; apply Z.leb_le in Hs1; apply Z.ltb_lt in Hs2; lia].
      destruct Hc2' as [Happ2 | (_ & _ & Hpc2)]; [|exfalso; destruct (Hpc2 (uE E (rg_base R2)) ltac:(lia)) as (Hs & _); unfold in_shadow in Hs;
        apply andb_prop in Hs as [Hs1 Hs2]; apply Z.leb_le in Hs1; apply Z.ltb_lt in Hs2; lia].
      intros w Hw. destruct (Z_lt_le_dec w (uE E (rg_base R1) + rsz E R1)) as [Hl|Hl]; [apply Happ1; lia | apply Happ2; lia].
  - apply (frz_keep mem0 E E S S2 M M ms ms model model Hwf (agree_refl _ _) eq_refl eq_refl); [| | exact Hfrz].
    + intros w _ Ho'. exact (proj2 (Hout _) Ho').
    + intros w _ _. reflexivity.
  - apply (own_keep mem0 E E S S2 M M ms ms model model Hwf (agree_refl _ _) eq_refl); [| | | exact Hown].
    + intros w Ho'. exact (proj1 (Hout _) Ho').
    + intros w _. reflexivity.
    + intros x Hxx. exact Hxx.
Qed.

#[using="Type"] Theorem den_merge_s : forall model0 E S M ms model i n S', DEN segs LIMIT model0 mem0 E S M ms model -> merge_s_post S i n = Some S' ->
  DEN segs LIMIT model0 mem0 E S' M ms model.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros model0 E S M ms model i n S' Hd Hp. unfold merge_s_post in Hp.
  destruct n as [|[|[|[|n]]]]; try discriminate.
  - exact (den_merge2 model0 E S M ms model i S' Hd Hp).
  - destruct (merge2_post S (Datatypes.S i)) as [S1|] eqn:H1; [|discriminate].
    exact (den_merge2 model0 E S1 M ms model i S' (den_merge2 model0 E S M ms model (Datatypes.S i) S1 Hd H1) Hp).
Qed.
End Merge.

(* [comment removed for export] *)
Definition retype_ok (stop : Z) (fs : list fact) (R : region) (k : rkind) : bool :=
  match k, rg_kind R with
  | RT, RW | RT, RZ | RT, RI | RT, RO => true
  | RW, RT => Z.leb stop (fst (irange fs (rg_base R)))
  | _, _ => false
  end.
Definition retype_post (stop : Z) (S : sst) (i : nat) (k : rkind) : option sst :=
  match nth_error (s_rgs S) i with
  | Some R => if retype_ok stop (s_facts S) R k
              then Some (SST (s_pc S) (s_regs S) (upd_nth (s_rgs S) i (RG (rg_base R) (rg_size R) k (rg_cont R))) (s_facts S) (s_next S) (s_resv S))
              else None
  | None => None
  end.

Section Retype.
Variable segs : list Segment.
Variable LIMIT : Z.
Variable mem0 : word -> option byte.
Variable stop : Z.
Hypothesis Hbelow : segs_below_b segs stop = true.

#[using="Hbelow"] Lemma rg_ok_retype : forall E m fs R k, Forall (fact_ok E) fs -> retype_ok stop fs R k = true -> rg_ok segs E m R ->
  rg_ok segs E m (RG (rg_base R) (rg_size R) k (rg_cont R)).
Proof. LiaFast.lf_pins (fun (Hbelow : LiaFast.U) => LiaFast.u0).
  intros E m fs R k HF Hk (H1 & H2 & H3 & H4). unfold rg_ok. cbn [rg_base rg_size rg_kind rg_cont].
  change (rsz E (RG (rg_base R) (rg_size R) k (rg_cont R))) with (rsz E R).
  split; [exact H1|]. split; [exact H2|]. split; [|exact H4].
  intros i Hi. specialize (H3 i Hi). unfold retype_ok in Hk.
  destruct k; destruct (rg_kind R); try discriminate.
  - (* [comment removed for export] *)
    apply Z.leb_le in Hk. pose proof (irange_sound E fs (rg_base R) HF) as Rb. fold (uE E (rg_base R)) in Rb.
    pose proof (uE_range E (rg_base R)) as Ub.
    assert (Hrom : seg_rom segs (Z_to_bv 64 (bv_unsigned (lden E (rg_base R)) + i)) = None).
    { change (uE E (rg_base R)) with (bv_unsigned (lden E (rg_base R))) in *.
      apply (seg_rom_none segs). apply (find_segment1_none_above _ stop _ Hbelow). rewrite u_small64 by (unfold two64 in *; lia). lia. }
    unfold rd1 in H3 |- *. destruct (m (Z_to_bv 64 (bv_unsigned (lden E (rg_base R)) + i))) as [b|] eqn:Hmb; [|rewrite Hrom in H3; exact (False_ind _ (H3 eq_refl))].
    split; [discriminate|]. unfold wview. rewrite Hmb. discriminate.
  - exact (proj1 H3).
  - unfold rd1. destruct H3 as [H3a H3b]. rewrite H3a. exact H3b.
  - exact (proj1 (proj1 H3)).
  - exact (proj1 (proj1 H3)).
Qed.

#[using="Hbelow"] Theorem den_retype : forall model0 E S M ms model i k S', DEN segs LIMIT model0 mem0 E S M ms model -> retype_post stop S i k = Some S' ->
  DEN segs LIMIT model0 mem0 E S' M ms model.
Proof. LiaFast.lf_pins (fun (Hbelow : LiaFast.U) => LiaFast.u0).
  intros model0 E S M ms model i k S' Hd Hp. unfold retype_post in Hp.
  destruct (nth_error (s_rgs S) i) as [R|] eqn:Hj; [|discriminate].
  destruct (retype_ok stop (s_facts S) R k) eqn:Hk; [|discriminate]. injection Hp as <-.
  set (R' := RG (rg_base R) (rg_size R) k (rg_cont R)).
  assert (Hb' : rg_base R' = rg_base R) by reflexivity. assert (Hs' : rg_size R' = rg_size R) by reflexivity.
  pose proof Hd as Hd0.
  destruct Hd0 as [Hsd Hwf Hbw Hh Hawf Hanz Hminv Hhoff Hres Hlim Hsp Hspok Hbrk Hsbrk Htid Hmaps Hgsh Hgtop Hivwf Hpd Hmres Hkind Hlzm Hzrsh Hzrm Hzr Hrl Hvmo Hproc Hfrz Hrom Hown Hblob].
  set (S2 := SST (s_pc S) (s_regs S) (upd_nth (s_rgs S) i R') (s_facts S) (s_next S) (s_resv S)).
  assert (Hshape : shape (s_rgs S2) = shape (s_rgs S)) by (cbn [S2 s_rgs]; exact (shape_upd (s_rgs S) i R' R Hj Hb' Hs')).
  constructor; try assumption.
  - intros E'' Ha''. destruct (Hsd E'' Ha'') as (H1 & H2 & H3 & H4 & HG & HD & HF & H8).
    unfold sden0. cbn [S2 s_pc s_regs s_rgs s_facts s_resv].
    split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [|split; [|split; [exact HF | exact H8]]].
    + apply Forall_forall. intros R0 HR0. destruct (List.In_nth_error _ _ HR0) as (j & Hk0).
      destruct (Nat.eq_dec j i) as [->|Hne].
      * rewrite (nth_upd_same _ _ _ _ Hj) in Hk0. injection Hk0 as <-.
        rewrite Forall_forall in HG. exact (rg_ok_retype E'' _ _ R k HF Hk (HG R (nth_error_In _ _ Hj))).
      * rewrite (nth_upd_other _ _ _ _ (not_eq_sym Hne)) in Hk0. rewrite Forall_forall in HG. exact (HG R0 (nth_error_In _ _ Hk0)).
    + eapply rgs_disj_upd; [exact Hj | exact Hb' | exact Hs' | exact HD].
  - eapply bases_wf_shape; [|exact Hshape|exact Hbw]. cbn [S2 s_next]. lia.
  - intros w Hw Hout' Hnow. apply (Hzr w Hw); [|exact Hnow].
    exact (outside_agree_shape (s_next S) E E (s_rgs S) _ _ Hbw (agree_refl _ _) Hshape Hout').
  - exact (rl_ok_agree_shape (s_next S) E E model model (s_rgs S) _ Hbw (agree_refl _ _) Hshape eq_refl Hrl).
  - apply (frz_keep mem0 E E S S2 M M ms ms model model Hwf (agree_refl _ _) eq_refl eq_refl); [| | exact Hfrz].
    + intros w _ Ho'. unfold outside in *. rewrite Forall_forall in *. intros R0 HR0.
      destruct (List.In_nth_error _ _ HR0) as (j & Hk0). cbn [S2 s_rgs] in Hk0.
      destruct (Nat.eq_dec j i) as [->|Hne].
      * rewrite (nth_upd_same _ _ _ _ Hj) in Hk0. injection Hk0 as <-. unfold rsz in *. rewrite Hb', Hs'. exact (Ho' R (nth_error_In _ _ Hj)).
      * rewrite (nth_upd_other _ _ _ _ (not_eq_sym Hne)) in Hk0. exact (Ho' R0 (nth_error_In _ _ Hk0)).
    + intros w _ _. reflexivity.
  - apply (own_keep mem0 E E S S2 M M ms ms model model Hwf (agree_refl _ _) eq_refl); [| | | exact Hown].
    + intros w Ho'. exact (outside_agree_shape (s_next S) E E (s_rgs S) _ _ Hbw (agree_refl _ _) Hshape Ho').
    + intros w _. reflexivity.
    + intros x Hxx. exact Hxx.
Qed.
End Retype.
