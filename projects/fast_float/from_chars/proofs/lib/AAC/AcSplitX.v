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
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require Import AcSplitS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition split_pieces_x (R : region) (o : Z) (p m : lin) : list region :=
  (if Z.eqb o 0 then [] else [RG (rg_base R) (lconst o) (rg_kind R) (cut_below o (rg_cont R))]) ++ [RG p m RW TEmpty].
(* [comment removed for export] *)
Definition split_chk_x (fs : list fact) (n : positive) (R : region) (p m : lin) : option (Z * Z) :=
  match is_const (rg_size R), lin_off p (rg_base R), is_const m with
  | Some z, Some o, Some mz =>
      if (rk_rwz (rg_kind R) && Z.leb 0 o && Z.leb 1 mz && Z.eqb (o + mz) z && Z.ltb z two64 &&
          lwf n p && lwf n m && Z.ltb (snd (irange fs (rg_base R)) + z) two64)%bool
      then Some (o, z) else None
  | _, _, _ => None
  end.
Definition split_post_x (S : sst) (i : nat) (p m : lin) : option sst :=
  match nth_error (s_rgs S) i with
  | Some R => match split_chk_x (s_facts S) (s_next S) R p m with
              | Some (o, z) => Some (SST (s_pc S) (s_regs S) (split_pieces_x R o p m ++ remove_nth i (s_rgs S)) (s_facts S) (s_next S) (s_resv S))
              | None => None
              end
  | None => None
  end.

(* [comment removed for export] *)
Lemma pieces_pts_x : forall E R o z p m, 0 <= o < z -> 1 <= uE E m /\ o + uE E m = z -> uE E p = uE E (rg_base R) + o ->
  uE E (rg_base R) + z < two64 ->
  forall R', In R' (split_pieces_x R o p m) ->
  0 < rsz E R' /\ exists d, 0 <= d /\ uE E (rg_base R') = uE E (rg_base R) + d /\ d + rsz E R' <= z.
Proof.
  intros E R o z p m Ho Hm Hp Hw R' HR'. unfold split_pieces_x in HR'. apply in_app_iff in HR' as [HR'|HR'].
  - destruct (Z.eqb o 0) eqn:Ho0; [destruct HR'|]. destruct HR' as [<-|[]]. apply Z.eqb_neq in Ho0.
    rewrite (rsz_pre E R o z Ho Hw). split; [lia|]. exists 0. cbn [rg_base]. lia.
  - destruct HR' as [<-|[]].
    rewrite rsz_mid. split; [lia|]. exists o. cbn [rg_base]. rewrite Hp. lia.
Qed.
Lemma pt_in_pieces_x : forall E R o z p m, 0 <= o < z -> 1 <= uE E m /\ o + uE E m = z -> uE E p = uE E (rg_base R) + o ->
  uE E (rg_base R) + z < two64 ->
  forall w, uE E (rg_base R) <= w < uE E (rg_base R) + z ->
  exists R', In R' (split_pieces_x R o p m) /\ uE E (rg_base R') <= w < uE E (rg_base R') + rsz E R'.
Proof.
  intros E R o z p m Ho Hm Hp Hw w Hw0. unfold split_pieces_x.
  destruct (Z_lt_le_dec w (uE E (rg_base R) + o)) as [H1|H1].
  - destruct (Z.eqb o 0) eqn:Ho0; [apply Z.eqb_eq in Ho0; lia|].
    exists (RG (rg_base R) (lconst o) (rg_kind R) (cut_below o (rg_cont R))). split; [apply in_or_app; left; left; reflexivity|].
    rewrite (rsz_pre E R o z Ho Hw). cbn [rg_base]. lia.
  - exists (RG p m RW TEmpty). split; [apply in_or_app; right; left; reflexivity|]. rewrite rsz_mid. cbn [rg_base]. rewrite Hp. lia.
Qed.
Lemma pieces_disj_x : forall E R o z p m, 0 <= o < z -> 1 <= uE E m /\ o + uE E m = z -> uE E p = uE E (rg_base R) + o ->
  uE E (rg_base R) + z < two64 -> rgs_disj E (split_pieces_x R o p m).
Proof.
  intros E R o z p m Ho Hm Hp Hw.
  unfold split_pieces_x. destruct (Z.eqb o 0) eqn:Ho0; cbn [app rgs_disj].
  - split; [constructor | exact I].
  - apply Z.eqb_neq in Ho0. pose proof (rsz_pre E R o z Ho Hw) as Hps.
    split; [constructor; [|constructor]|split; [constructor | exact I]].
    unfold rg_disj. cbv zeta. cbn [rg_base]. fold (uE E (rg_base R)) (uE E p). rewrite Hps, rsz_mid, Hp. lia.
Qed.
Lemma pieces_ok_x : forall segs E mem R o z p m, rg_ok segs E mem R -> rk_rwz (rg_kind R) = true ->
  rsz E R = z -> 0 <= o < z -> 1 <= uE E m /\ o + uE E m = z -> uE E p = uE E (rg_base R) + o -> uE E (rg_base R) + z < two64 ->
  Forall (rg_ok segs E mem) (split_pieces_x R o p m).
Proof.
  intros segs E mem R o z p m Hok Hk Hz Ho Hm Hp Hws.
  destruct Hok as (Hs & Hw & Hbytes & Hc). fold (uE E (rg_base R)) in Hw, Hbytes, Hc. rewrite Hz in Hs, Hw, Hbytes, Hc.
  assert (Hrw : forall i, 0 <= i < z -> rd1 segs mem (Z_to_bv 64 (uE E (rg_base R) + i)) <> None /\ wview segs mem (Z_to_bv 64 (uE E (rg_base R) + i)) <> None).
  { intros i Hi. specialize (Hbytes i Hi). destruct (rg_kind R); try discriminate; [exact Hbytes | exact (proj1 Hbytes)]. }
  apply Forall_forall. intros R' HR'. unfold split_pieces_x in HR'. apply in_app_iff in HR' as [HR'|HR'].
  - destruct (Z.eqb o 0) eqn:Ho0; [destruct HR'|]. destruct HR' as [<-|[]]. apply Z.eqb_neq in Ho0.
    unfold rg_ok. fold (rsz E (RG (rg_base R) (lconst o) (rg_kind R) (cut_below o (rg_cont R)))).
    rewrite (rsz_pre E R o z Ho Hws). cbn [rg_base rg_kind rg_cont]. fold (uE E (rg_base R)).
    split; [lia|]. split; [lia|]. split.
    + intros i Hi. specialize (Hbytes i ltac:(lia)). destruct (rg_kind R); try discriminate; [exact Hbytes|].
      destruct Hbytes as [H1 H2]. split; [exact H1|]. intros Hn. apply H2. rewrite tget_cut_below in Hn.
      replace (Z.ltb (Zpos (okey i) - 1) o) with true in Hn by (symmetry; apply Z.ltb_lt; unfold okey; rewrite Z2Pos.id by lia; lia). exact Hn.
    + intros k v Hkv. rewrite tget_cut_below in Hkv. destruct (Z.ltb (Zpos k - 1) o) eqn:Hlt; [|discriminate].
      apply Z.ltb_lt in Hlt. destruct (Hc k v Hkv) as [_ Hv]. split; [lia | exact Hv].
  - destruct HR' as [<-|[]].
    unfold rg_ok. fold (rsz E (RG p m RW TEmpty)). rewrite (rsz_mid E p m). cbn [rg_base rg_kind rg_cont]. fold (uE E p). rewrite Hp.
    split; [lia|]. split; [lia|]. split.
    + intros i Hi. replace (uE E (rg_base R) + o + i) with (uE E (rg_base R) + (o + i)) by lia. exact (Hrw (o + i) ltac:(lia)).
    + intros k v Hkv. rewrite tget_empty in Hkv. discriminate.
Qed.

(* [comment removed for export] *)
Section SplitX.
Variable segs : list Segment.
Variable LIMIT : Z.
Variable mem0 : word -> option byte.

#[using="Type"] Theorem den_split_x : forall model0 E S M ms model i p m S', DEN segs LIMIT model0 mem0 E S M ms model -> split_post_x S i p m = Some S' ->
  DEN segs LIMIT model0 mem0 E S' M ms model.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros model0 E S M ms model i p m S' Hd Hp. unfold split_post_x in Hp.
  destruct (nth_error (s_rgs S) i) as [R|] eqn:Hi; [|discriminate]. destruct (split_chk_x (s_facts S) (s_next S) R p m) as [[o z]|] eqn:Hc; [|discriminate].
  injection Hp as <-.
  unfold split_chk_x in Hc. destruct (is_const (rg_size R)) as [z0|] eqn:Hz0; [|discriminate]. destruct (lin_off p (rg_base R)) as [o0|] eqn:Ho0; [|discriminate].
  destruct (is_const m) as [mz|] eqn:Hmz; [|discriminate].
  destruct (rk_rwz (rg_kind R) && Z.leb 0 o0 && Z.leb 1 mz && Z.eqb (o0 + mz) z0 && Z.ltb z0 two64 &&
            lwf (s_next S) p && lwf (s_next S) m && Z.ltb (snd (irange (s_facts S) (rg_base R)) + z0) two64)%bool eqn:Hb; [|discriminate].
  injection Hc as -> ->.
  repeat match type of Hb with ((_ && _)%bool = true) => apply andb_prop in Hb as [Hb ?Hx] end.
  rename Hb into Hk.
  repeat match goal with
         | H' : Z.leb _ _ = true |- _ => apply Z.leb_le in H'
         | H' : Z.ltb _ _ = true |- _ => apply Z.ltb_lt in H'
         | H' : Z.eqb _ _ = true |- _ => apply Z.eqb_eq in H'
         end.
  match goal with H' : lwf (s_next S) p = true |- _ => rename H' into Hwp end.
  match goal with H' : lwf (s_next S) m = true |- _ => rename H' into Hwm end.
  pose proof Hd as Hd0.
  destruct Hd0 as [Hsd Hwf Hbw Hh Hawf Hanz Hminv Hhoff Hres Hlim Hsp Hspok Hbrk Hsbrk Htid Hmaps Hgsh Hgtop Hivwf Hpd Hmres Hkind Hlzm Hzrsh Hzrm Hzr Hrl Hvmo Hproc Hfrz Hrom Hown Hblob].
  set (pcs := split_pieces_x R o p m) in *.
  set (S2 := SST (s_pc S) (s_regs S) (pcs ++ remove_nth i (s_rgs S)) (s_facts S) (s_next S) (s_resv S)).
  assert (Hgeo : forall E', agree (s_next S) E E' -> Forall (fact_ok E') (s_facts S) ->
            rsz E' R = z /\ 0 <= o < z /\ (1 <= uE E' m /\ o + uE E' m = z) /\ uE E' p = uE E' (rg_base R) + o /\ uE E' (rg_base R) + z < two64).
  { intros E' Ha HF'. pose proof (irange_sound E' (s_facts S) (rg_base R) HF') as Ib.
    assert (Hrz : rsz E' R = z) by (exact (rsz_is_const_s E' R z Hz0)).
    assert (Hum : uE E' m = mz) by (unfold uE; exact (is_const_u E' m mz Hmz)).
    assert (Hbz : uE E' (rg_base R) + z < two64) by (unfold uE; lia).
    split; [exact Hrz|]. split; [lia|]. split; [rewrite Hum; lia|]. split; [|exact Hbz].
    unfold uE. apply (lin_off_u E' p (rg_base R) o Ho0). unfold uE in Hbz. lia. }
  assert (HF0 : Forall (fact_ok E) (s_facts S)) by (destruct (sden_0 _ _ _ _ Hsd) as (_ & _ & _ & _ & _ & _ & X & _); exact X).
  destruct (Hgeo E (agree_refl _ _) HF0) as (Hrz & Ho & Hm & Hpo & Hbz).
  assert (Hpts : forall E', agree (s_next S) E E' -> Forall (fact_ok E') (s_facts S) -> forall w,
            (exists R', In R' pcs /\ uE E' (rg_base R') <= w < uE E' (rg_base R') + rsz E' R') <-> uE E' (rg_base R) <= w < uE E' (rg_base R) + rsz E' R).
  { intros E' Ha HF' w. destruct (Hgeo E' Ha HF') as (Hrz' & Ho' & Hm' & Hpo' & Hbz'). rewrite Hrz'. split.
    - intros (R' & HR' & Hw). destruct (pieces_pts_x E' R o z p m Ho' Hm' Hpo' Hbz' R' HR') as (_ & d & Hd0' & Hb' & Hdz). lia.
    - intros Hw. exact (pt_in_pieces_x E' R o z p m Ho' Hm' Hpo' Hbz' w Hw). }
  assert (Hbw2 : bases_wf (s_next S) (pcs ++ remove_nth i (s_rgs S)) = true).
  { unfold bases_wf in *. rewrite forallb_app. apply andb_true_intro. split.
    - unfold pcs, split_pieces_x. rewrite forallb_app. apply andb_true_intro. split.
      + destruct (Z.eqb o 0); cbn [forallb rg_base rg_size]; [reflexivity|]. rewrite forallb_forall in Hbw.
        destruct (andb_prop _ _ (Hbw R (nth_error_In _ _ Hi))) as [Hb1 _]. rewrite Hb1, lwf_lconst. reflexivity.
      + cbn [forallb rg_base rg_size]. rewrite Hwp, Hwm. reflexivity.
    - apply forallb_forall. intros R0 HR0. rewrite forallb_forall in Hbw. exact (Hbw R0 (remove_nth_In i _ R0 HR0)). }
  assert (Hout : forall x, outside E (s_rgs S2) x <-> outside E (s_rgs S) x)
    by (intros x; cbn [S2 s_rgs]; exact (outside_split E (s_rgs S) i R pcs Hi (Hpts E (agree_refl _ _) HF0) x)).
  constructor; try assumption.
  - intros E'' Ha''. destruct (Hsd E'' Ha'') as (H1 & H2 & H3 & H4 & HG & HD & HF & H8).
    destruct (Hgeo E'' Ha'' HF) as (Hrz'' & Ho'' & Hm'' & Hpo'' & Hbz'').
    unfold sden0. cbn [S2 s_pc s_regs s_rgs s_facts s_resv].
    split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [|split; [|split; [exact HF | exact H8]]].
    + apply Forall_app. split.
      * rewrite Forall_forall in HG. exact (pieces_ok_x segs E'' _ R o z p m (HG R (nth_error_In _ _ Hi)) Hk Hrz'' Ho'' Hm'' Hpo'' Hbz'').
      * apply remove_nth_Forall. exact HG.
    + apply rgs_disj_app; [exact (pieces_disj_x E'' R o z p m Ho'' Hm'' Hpo'' Hbz'') | exact (rgs_disj_remove E'' _ i HD) |].
      intros R1 R2 HR1 HR2. destruct (remove_nth_pos _ i R2 HR2) as (j & Hne & Hj).
      pose proof (rgs_disj_nth E'' _ i j R R2 HD (not_eq_sym Hne) Hi Hj) as Hd2. unfold rg_disj in *. cbv zeta in *.
      destruct (pieces_pts_x E'' R o z p m Ho'' Hm'' Hpo'' Hbz'' R1 HR1) as (Hp1 & d & Hd1 & Hb1 & Hdz).
      fold (uE E'' (rg_base R1)) (uE E'' (rg_base R2)) (uE E'' (rg_base R)) in *. rewrite Hrz'' in Hd2. lia.
  - intros w Hw Hout' Hnow Hnb. apply (Hzr w Hw); [|exact Hnow | exact Hnb]. exact (proj1 (Hout _) Hout').
  - cbn [S2 s_rgs]. apply Forall_app. split.
    + rewrite Forall_forall in Hrl |- *. intros R' HR'. destruct (Hrl R (nth_error_In _ _ Hi)) as [Hpos [Happ | (Hoff & HX & Hpc)]].
      * destruct (pieces_pts_x E R o z p m Ho Hm Hpo Hbz R' HR') as (Hp1 & d & Hd1 & Hb1 & Hdz). split; [exact Hp1|]. left.
        intros w Hw. apply Happ. rewrite Hrz. lia.
      * destruct (pieces_pts_x E R o z p m Ho Hm Hpo Hbz R' HR') as (Hp1 & d & Hd1 & Hb1 & Hdz). split; [exact Hp1|]. right.
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
End SplitX.

(* [comment removed for export] *)
Fixpoint find_split_acc (fs : list fact) (n : positive) (rgs : list region) (p m : lin) (i : nat) : option nat :=
  match rgs with
  | [] => None
  | R :: r => match split_chk fs n R p m with Some _ => Some i | None => find_split_acc fs n r p m (Datatypes.S i) end
  end.
Definition find_split (S : sst) (p m : lin) : option nat := find_split_acc (s_facts S) (s_next S) (s_rgs S) p m O.
Fixpoint find_split_x_acc (fs : list fact) (n : positive) (rgs : list region) (p m : lin) (i : nat) : option nat :=
  match rgs with
  | [] => None
  | R :: r => match split_chk_x fs n R p m with Some _ => Some i | None => find_split_x_acc fs n r p m (Datatypes.S i) end
  end.
Definition find_split_x (S : sst) (p m : lin) : option nat := find_split_x_acc (s_facts S) (s_next S) (s_rgs S) p m O.
Fixpoint find_split_s_acc (fs : list fact) (n : positive) (rgs : list region) (p m : lin) (i : nat) : option nat :=
  match rgs with
  | [] => None
  | R :: r => match split_chk_s fs n R p m with Some _ => Some i | None => find_split_s_acc fs n r p m (Datatypes.S i) end
  end.
Definition find_split_s (S : sst) (p m : lin) : option nat := find_split_s_acc (s_facts S) (s_next S) (s_rgs S) p m O.
Definition mid_ix (o : Z) : nat := if Z.eqb o 0 then O else 1%nat.
(* [comment removed for export] *)
Definition msplit (S : sst) (p m : lin) : option (sst * nat) :=
  match find_split S p m with
  | Some i => match nth_error (s_rgs S) i with
              | Some R => match lin_off p (rg_base R), split_post S i p m with Some o, Some S1 => Some (S1, mid_ix o) | _, _ => None end
              | None => None
              end
  | None => match find_split_x S p m with
            | Some i => match nth_error (s_rgs S) i with
                        | Some R => match lin_off p (rg_base R), split_post_x S i p m with Some o, Some S1 => Some (S1, mid_ix o) | _, _ => None end
                        | None => None
                        end
            | None => (* [comment removed for export] *)
                match find_split_s S p m with
                | Some i => match nth_error (s_rgs S) i with
                            | Some R => match lin_off p (rg_base R), split_post_s S i p m with Some o, Some S1 => Some (S1, mid_ix o) | _, _ => None end
                            | None => None
                            end
                | None => None
                end
            end
  end.

Lemma split_post_shape : forall S i p m S1 R o, split_post S i p m = Some S1 -> nth_error (s_rgs S) i = Some R -> lin_off p (rg_base R) = Some o ->
  s_pc S1 = s_pc S /\ s_regs S1 = s_regs S /\ s_facts S1 = s_facts S /\ s_next S1 = s_next S /\ s_resv S1 = s_resv S /\
  nth_error (s_rgs S1) (mid_ix o) = Some (RG p m RW TEmpty) /\ lwf (s_next S) p = true /\ lwf (s_next S) m = true.
Proof.
  intros S i p m S1 R o Hp Hi Ho. unfold split_post in Hp. rewrite Hi in Hp.
  destruct (split_chk (s_facts S) (s_next S) R p m) as [[o' z]|] eqn:Hc; [|discriminate]. injection Hp as <-.
  unfold split_chk in Hc. rewrite Ho in Hc. destruct (is_const (rg_size R)) as [z0|]; [|discriminate].
  destruct (irange (s_facts S) m) as [lo hi].
  destruct (rk_rwz (rg_kind R) && Z.leb 0 o && Z.ltb o z0 && Z.leb 1 lo && Z.ltb (o + hi) z0 && Z.ltb z0 two64 &&
            lwf (s_next S) p && lwf (s_next S) m && Z.ltb (snd (irange (s_facts S) (rg_base R)) + z0) two64)%bool eqn:Hb; [|discriminate].
  injection Hc as <- <-.
  repeat match goal with H : (_ && _)%bool = true |- _ => apply andb_prop in H as [? ?] end.
  cbn [s_pc s_regs s_facts s_next s_resv s_rgs]. repeat split; try reflexivity; try assumption.
  unfold split_pieces, mid_ix. destruct (Z.eqb o 0); reflexivity.
Qed.
Lemma split_post_x_shape : forall S i p m S1 R o, split_post_x S i p m = Some S1 -> nth_error (s_rgs S) i = Some R -> lin_off p (rg_base R) = Some o ->
  s_pc S1 = s_pc S /\ s_regs S1 = s_regs S /\ s_facts S1 = s_facts S /\ s_next S1 = s_next S /\ s_resv S1 = s_resv S /\
  nth_error (s_rgs S1) (mid_ix o) = Some (RG p m RW TEmpty) /\ lwf (s_next S) p = true /\ lwf (s_next S) m = true.
Proof.
  intros S i p m S1 R o Hp Hi Ho. unfold split_post_x in Hp. rewrite Hi in Hp.
  destruct (split_chk_x (s_facts S) (s_next S) R p m) as [[o' z]|] eqn:Hc; [|discriminate]. injection Hp as <-.
  unfold split_chk_x in Hc. rewrite Ho in Hc. destruct (is_const (rg_size R)) as [z0|]; [|discriminate].
  destruct (is_const m) as [mz|]; [|discriminate].
  destruct (rk_rwz (rg_kind R) && Z.leb 0 o && Z.leb 1 mz && Z.eqb (o + mz) z0 && Z.ltb z0 two64 &&
            lwf (s_next S) p && lwf (s_next S) m && Z.ltb (snd (irange (s_facts S) (rg_base R)) + z0) two64)%bool eqn:Hb; [|discriminate].
  injection Hc as <- <-.
  repeat match goal with H : (_ && _)%bool = true |- _ => apply andb_prop in H as [? ?] end.
  cbn [s_pc s_regs s_facts s_next s_resv s_rgs]. repeat split; try reflexivity; try assumption.
  unfold split_pieces_x, mid_ix. destruct (Z.eqb o 0); reflexivity.
Qed.

Lemma split_post_s_shape : forall S i p m S1 R o, split_post_s S i p m = Some S1 -> nth_error (s_rgs S) i = Some R -> lin_off p (rg_base R) = Some o ->
  s_pc S1 = s_pc S /\ s_regs S1 = s_regs S /\ s_facts S1 = s_facts S /\ s_next S1 = s_next S /\ s_resv S1 = s_resv S /\
  nth_error (s_rgs S1) (mid_ix o) = Some (RG p m RW TEmpty) /\ lwf (s_next S) p = true /\ lwf (s_next S) m = true.
Proof.
  intros S i p m S1 R o Hp Hi Ho. unfold split_post_s in Hp. rewrite Hi in Hp.
  destruct (split_chk_s (s_facts S) (s_next S) R p m) as [[o' t]|] eqn:Hc; [|discriminate]. injection Hp as <-.
  destruct (split_chk_s_geo _ _ _ _ _ _ _ Hc) as (_ & Hwp & Hwm & _ & _).
  assert (Eo : o' = o).
  { unfold split_chk_s in Hc. rewrite Ho in Hc. destruct (irange (s_facts S) m) as [mlo mhi]. destruct (_ && _)%bool; [|discriminate].
    destruct (lin_eqb _ _); [injection Hc as <- _; reflexivity|]. destruct (irange (s_facts S) _) as [tlo thi]. destruct (_ && _)%bool; [|discriminate].
    injection Hc as <- _. reflexivity. }
  subst o'. cbn [s_pc s_regs s_facts s_next s_resv s_rgs]. repeat split; try reflexivity; try assumption.
  unfold split_pieces_s, mid_ix. destruct (Z.eqb o 0); reflexivity.
Qed.

Theorem msplit_sound : forall segs LIMIT mem0 model0 E S M ms model p m S1 jm, msplit S p m = Some (S1, jm) ->
  DEN segs LIMIT model0 mem0 E S M ms model ->
  DEN segs LIMIT model0 mem0 E S1 M ms model /\
  s_pc S1 = s_pc S /\ s_regs S1 = s_regs S /\ s_facts S1 = s_facts S /\ s_next S1 = s_next S /\ s_resv S1 = s_resv S /\
  nth_error (s_rgs S1) jm = Some (RG p m RW TEmpty) /\ lwf (s_next S) p = true /\ lwf (s_next S) m = true.
Proof.
  intros segs LIMIT mem0 model0 E S M ms model p m S1 jm H Hd. unfold msplit in H.
  destruct (find_split S p m) as [i|].
  - destruct (nth_error (s_rgs S) i) as [R|] eqn:Hi; [|discriminate].
    destruct (lin_off p (rg_base R)) as [o|] eqn:Ho; [|discriminate]. destruct (split_post S i p m) as [S1'|] eqn:Hs; [|discriminate].
    injection H as <- <-. split; [exact (den_split segs LIMIT mem0 model0 E S M ms model i p m S1' Hd Hs)|].
    exact (split_post_shape S i p m S1' R o Hs Hi Ho).
  - destruct (find_split_x S p m) as [i|].
    + destruct (nth_error (s_rgs S) i) as [R|] eqn:Hi; [|discriminate].
      destruct (lin_off p (rg_base R)) as [o|] eqn:Ho; [|discriminate]. destruct (split_post_x S i p m) as [S1'|] eqn:Hs; [|discriminate].
      injection H as <- <-. split; [exact (den_split_x segs LIMIT mem0 model0 E S M ms model i p m S1' Hd Hs)|].
      exact (split_post_x_shape S i p m S1' R o Hs Hi Ho).
    + destruct (find_split_s S p m) as [i|]; [|discriminate].
      destruct (nth_error (s_rgs S) i) as [R|] eqn:Hi; [|discriminate].
      destruct (lin_off p (rg_base R)) as [o|] eqn:Ho; [|discriminate]. destruct (split_post_s S i p m) as [S1'|] eqn:Hs; [|discriminate].
      injection H as <- <-. split; [exact (den_split_s segs LIMIT mem0 model0 E S M ms model i p m S1' Hd Hs)|].
      exact (split_post_s_shape S i p m S1' R o Hs Hi Ho).
Qed.
