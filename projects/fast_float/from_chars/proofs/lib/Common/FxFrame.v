(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLin FxCore FxSound FxMem FxFold FxRgs FxFacts FxImg FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSubst FxEnt FxLoop FxPlan.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxMem OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFold OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxRgs OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxImg OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEnt OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma rgs_ent_outside : forall E rs rp σ x, rgs_ent rs rp σ = true -> (outside E rs x <-> outside (ecomp E σ) rp x).
Proof.
  intros E rs. induction rs as [|R rs IH]; intros [|R' rp] σ x H; cbn [rgs_ent] in H; try discriminate.
  - unfold outside. split; intros; constructor.
  - apply andb_prop in H as [H1 H2]. destruct (rg_ent_parts _ _ _ H1) as (Hb & Hs & _).
    unfold outside in *. split; intros HF; inversion HF as [|? ? Hx HF']; subst; constructor.
    + unfold rsz in *. rewrite <- !lden_lsubst, <- Hb, <- Hs. exact Hx.
    + apply (IH rp σ x H2). exact HF'.
    + unfold rsz in *. rewrite Hb, Hs, !lden_lsubst. exact Hx.
    + apply (IH rp σ x H2). exact HF'.
Qed.

Lemma state_wf_bases : forall P, state_wf P = true -> bases_wf (s_next P) (s_rgs P) = true.
Proof.
  intros P H. unfold state_wf in H. apply andb_prop in H as [H _]. apply andb_prop in H as [H _]. apply andb_prop in H as [_ H].
  unfold bases_wf. rewrite forallb_forall in *. intros R HR. pose proof (H R HR) as HR'. unfold rwf in HR'.
  apply andb_prop in HR' as [HR' _]. exact HR'.
Qed.

Lemma tsum_params : forall E E' (ps : list positive) t, forallb (fun '(y, _) => existsb (Pos.eqb y) ps) t = true ->
  (forall y, In y ps -> E' y = E y) -> tsum E t = tsum E' t.
Proof.
  intros E E' ps t. induction t as [|[y k] t IH]; intros H He; cbn [tsum]; [reflexivity|].
  cbn [forallb] in H. apply andb_prop in H as [H1 H2]. apply existsb_exists in H1 as (y' & Hy' & Hyy). apply Pos.eqb_eq in Hyy. subst y'.
  unfold vz. rewrite (He y Hy'), (IH H2 He). reflexivity.
Qed.

Lemma outside_params : forall E E' (ps : list positive) rgs x,
  forallb (fun R => forallb (fun '(y, _) => existsb (Pos.eqb y) ps) (l_t (rg_base R) ++ l_t (rg_size R))) rgs = true ->
  (forall y, In y ps -> E' y = E y) -> (outside E rgs x <-> outside E' rgs x).
Proof.
  intros E E' ps rgs x H He. unfold outside. rewrite forallb_forall in H.
  assert (Hb : forall R, In R rgs -> lden E (rg_base R) = lden E' (rg_base R) /\ lden E (rg_size R) = lden E' (rg_size R)).
  { intros R HR. pose proof (H R HR) as HR'. rewrite forallb_app in HR'. apply andb_prop in HR' as [H1 H2].
    unfold lden, lz. rewrite (tsum_params E E' ps _ H1 He), (tsum_params E E' ps _ H2 He). split; reflexivity. }
  split; intros HF; apply Forall_forall; intros R HR; rewrite Forall_forall in HF; specialize (HF R HR); cbv beta in *; unfold rsz in *.
  - rewrite <- (proj1 (Hb R HR)), <- (proj2 (Hb R HR)). exact HF.
  - rewrite (proj1 (Hb R HR)), (proj2 (Hb R HR)). exact HF.
Qed.

(* [comment removed for export] *)
Lemma fr_pt_agree : forall n E E' rgs x, bases_wf n rgs = true -> agree n E E' -> fr_pt E rgs x -> fr_pt E' rgs x.
Proof.
  intros n E E' rgs x Hw Ha [H|H]; [left; exact (proj1 (outside_agree n E E' rgs x Hw Ha) H)|right].
  unfold bases_wf in Hw. rewrite forallb_forall in Hw. apply Exists_exists in H as (R & HR & Hk & Hin). apply Exists_exists. exists R.
  split; [exact HR|]. split; [exact Hk|]. destruct (andb_prop _ _ (Hw R HR)) as [Hb0 Hs0]. unfold in_rg, rsz in *.
  rewrite <- (lden_agree n E E' _ Hb0 Ha), <- (lden_agree n E E' _ Hs0 Ha). exact Hin.
Qed.

Lemma rkind_le_rt : forall a b, rkind_le a b = true -> is_rt a = is_rt b.
Proof. intros [] [] H; cbn in H; try discriminate; reflexivity. Qed.

Lemma rt_in_ent : forall E rs rp σ x, rgs_ent rs rp σ = true ->
  (Exists (fun R => is_rt (rg_kind R) = true /\ in_rg E R x) rs <-> Exists (fun R => is_rt (rg_kind R) = true /\ in_rg (ecomp E σ) R x) rp).
Proof.
  intros E rs. induction rs as [|R rs IH]; intros [|R' rp] σ x H; cbn [rgs_ent] in H; try discriminate.
  - split; intros H'; inversion H'.
  - apply andb_prop in H as [H1 H2]. destruct (rg_ent_parts _ _ _ H1) as (Hb & Hs & Hk & _).
    pose proof (rkind_le_rt _ _ Hk) as Hrt.
    assert (Hin : in_rg E R x <-> in_rg (ecomp E σ) R' x) by (unfold in_rg, rsz; rewrite <- !lden_lsubst, <- Hb, <- Hs; reflexivity).
    rewrite !Exists_cons, (IH rp σ x H2), Hrt, Hin. reflexivity.
Qed.

Lemma fr_pt_ent : forall E rs rp σ x, rgs_ent rs rp σ = true -> (fr_pt E rs x <-> fr_pt (ecomp E σ) rp x).
Proof.
  intros E rs rp σ x H. unfold fr_pt. rewrite (rgs_ent_outside E rs rp σ x H), (rt_in_ent E rs rp σ x H). reflexivity.
Qed.

Lemma rgs_ent_rtm : forall rs rp σ, rgs_ent rs rp σ = true -> rtm rs = rtm rp.
Proof.
  induction rs as [|R rs IH]; intros [|R' rp] σ H; cbn [rgs_ent] in H; try discriminate; [reflexivity|].
  apply andb_prop in H as [H1 H2]. destruct (rg_ent_parts _ _ _ H1) as (_ & _ & Hk & _).
  unfold rtm. cbn [List.map]. rewrite (rkind_le_rt _ _ Hk). f_equal. exact (IH rp σ H2).
Qed.

Lemma fr_pt_params : forall E E' (ps : list positive) rgs x,
  forallb (fun R => forallb (fun '(y, _) => existsb (Pos.eqb y) ps) (l_t (rg_base R) ++ l_t (rg_size R))) rgs = true ->
  (forall y, In y ps -> E' y = E y) -> (fr_pt E rgs x <-> fr_pt E' rgs x).
Proof.
  intros E E' ps rgs x H He. unfold fr_pt. rewrite (outside_params E E' ps rgs x H He).
  assert (Hb : forall R, In R rgs -> lden E (rg_base R) = lden E' (rg_base R) /\ lden E (rg_size R) = lden E' (rg_size R)).
  { intros R HR. rewrite forallb_forall in H. pose proof (H R HR) as HR'. rewrite forallb_app in HR'. apply andb_prop in HR' as [H1 H2].
    unfold lden, lz. rewrite (tsum_params E E' ps _ H1 He), (tsum_params E E' ps _ H2 He). split; reflexivity. }
  assert (Hx : Exists (fun R => is_rt (rg_kind R) = true /\ in_rg E R x) rgs <-> Exists (fun R => is_rt (rg_kind R) = true /\ in_rg E' R x) rgs).
  { rewrite !Exists_exists. split; intros (R & HR & Hk & Hin); exists R; split; [exact HR| |exact HR|]; split; [exact Hk| |exact Hk|];
      unfold in_rg, rsz in *; destruct (Hb R HR) as [E1 E2]; [rewrite <- E1, <- E2; exact Hin | rewrite E1, E2; exact Hin]. }
  rewrite Hx. reflexivity.
Qed.

Section WithSegs.
Variable segs : list Segment.

#[using="Type"] Theorem explore_frame2_frp : forall t img fuel stops s acc E ms,
  tbl_ok segs t -> img_ok segs img -> sden segs E s ms -> bases_wf (s_next s) (s_rgs s) = true ->
  exists L ms' E', In L (fx_explore t img fuel stops s acc) /\ isteps segs ms ms' /\ sden segs E' L ms' /\ agree (s_next s) E E' /\
    (forall x, fr_pt E (s_rgs s) x -> ms_mem ms' x = ms_mem ms x) /\ shape (s_rgs L) = shape (s_rgs s) /\
    (s_next s <= s_next L)%positive /\ rtm (s_rgs L) = rtm (s_rgs s) /\ fpc t ms ms'.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros t img fuel. induction fuel as [|f IH]; intros stops s acc E ms Ht Himg Hden Hwf; cbn [fx_explore].
  - exists s, ms, E. split; [left; reflexivity|]. split; [constructor|]. split; [exact Hden|]. split; [apply agree_refl|].
    split; [intros; reflexivity | split; [reflexivity | split; [lia | split; [reflexivity | apply fpc_refl]]]].
  - destruct (fx_step t img s) as [s'| c a b tgt | l c |] eqn:Hs.
    + destruct (fx_step_fr segs t img s s' E ms Ht Himg Hs Hden) as (ms1 & E1 & Hst & Hsvc & Ha1 & Hn1 & Hd1 & Hfr1 & Hsh1 & Hrt1).
      pose proof (fx_step_fpc segs t img s s' E ms ms1 Ht Himg Hs Hden Hst) as Hfp1.
      assert (Hwf1 : bases_wf (s_next s') (s_rgs s') = true) by exact (bases_wf_shape _ _ _ _ Hn1 Hsh1 Hwf).
      destruct (existsb (Z.eqb (s_pc s')) stops).
      * exists s', ms1, E1. split; [left; reflexivity|]. split; [econstructor; [exact Hsvc | exact Hst | constructor]|].
        split; [exact Hd1|]. split; [exact Ha1|]. split; [exact Hfr1 | split; [exact Hsh1 | split; [exact Hn1 | split; [exact Hrt1 | exact Hfp1]]]].
      * destruct (IH stops s' acc E1 ms1 Ht Himg Hd1 Hwf1) as (L & ms2 & E2 & HL & Hst2 & Hd2 & Ha2 & Hfr2 & Hsh2 & Hn2 & Hrt2 & Hfp2).
        exists L, ms2, E2. split; [exact HL|]. split; [econstructor; [exact Hsvc | exact Hst | exact Hst2]|]. split; [exact Hd2|].
        split; [eapply agree_trans; [exact Ha1 | eapply agree_mono; [exact Hn1 | exact Ha2]]|].
        split; [|split; [rewrite Hsh2; exact Hsh1 | split; [lia | split; [rewrite Hrt2; exact Hrt1 | exact (fpc_trans _ _ _ _ Hfp1 Hfp2)]]]].
        intros x Hx. rewrite Hfr2; [exact (Hfr1 x Hx)|].
        apply (fr_pt_agree (s_next s) E E1 (s_rgs s') x); [exact (bases_wf_shape _ _ _ _ (Pos.le_refl _) Hsh1 Hwf) | exact Ha1 |].
        exact (fr_pt_shape E _ _ x Hsh1 Hrt1 Hx).
    + destruct (fx_step_br segs t img s c a b tgt E ms Ht Hs Hden) as (ms1 & Hst & Hsvc & Hd1 & Hm1).
      pose proof (fx_step_br_fpc segs t img s c a b tgt E ms ms1 Ht Hs Hden Hst) as Hfp1.
      set (s1 := with_pc_fact s tgt (FCond c a b true)). set (s2 := with_pc_fact s (s_pc s + 4) (FCond c a b false)).
      set (acc1 := if existsb (Z.eqb (s_pc s1)) stops then s1 :: acc else fx_explore t img f stops s1 acc).
      assert (Hfin : forall L, In L acc1 -> In L (if existsb (Z.eqb (s_pc s2)) stops then s2 :: acc1 else fx_explore t img f stops s2 acc1)).
      { intros L HL. destruct (existsb (Z.eqb (s_pc s2)) stops); [right; exact HL | apply explore_acc; exact HL]. }
      assert (Hwfb : forall sb, s_rgs sb = s_rgs s -> s_next sb = s_next s -> bases_wf (s_next sb) (s_rgs sb) = true)
        by (intros sb H1 H2; rewrite H1, H2; exact Hwf).
      destruct (branch_taken c (lden E a) (lden E b)) eqn:Htk.
      * assert (Hx : exists L ms2 E2, In L acc1 /\ isteps segs ms1 ms2 /\ sden segs E2 L ms2 /\ agree (s_next s) E E2 /\
                       (forall x, fr_pt E (s_rgs s) x -> ms_mem ms2 x = ms_mem ms1 x) /\ shape (s_rgs L) = shape (s_rgs s) /\
                       (s_next s <= s_next L)%positive /\ rtm (s_rgs L) = rtm (s_rgs s) /\ fpc t ms1 ms2).
        { unfold acc1. destruct (existsb (Z.eqb (s_pc s1)) stops).
          - exists s1, ms1, E. split; [left; reflexivity|]. split; [constructor|]. split; [exact Hd1|]. split; [apply agree_refl|].
            split; [intros; reflexivity | split; [reflexivity | split; [cbn; lia | split; [reflexivity | apply fpc_refl]]]].
          - destruct (IH stops s1 acc E ms1 Ht Himg Hd1 (Hwfb s1 eq_refl eq_refl)) as (L & ms2 & E2 & HL & Hst2 & Hd2 & Ha2 & Hfr2 & Hsh2 & Hn2 & Hrt2 & Hfp2).
            exists L, ms2, E2. split; [exact HL|]. split; [exact Hst2|]. split; [exact Hd2|]. split; [exact Ha2|].
            split; [exact Hfr2 | split; [exact Hsh2 | split; [exact Hn2 | split; [exact Hrt2 | exact Hfp2]]]]. }
        destruct Hx as (L & ms2 & E2 & HL & Hst2 & Hd2 & Ha2 & Hfr2 & Hsh2 & Hn2 & Hrt2 & Hfp2).
        exists L, ms2, E2. split; [apply Hfin; exact HL|].
        split; [econstructor; [exact Hsvc | exact Hst | exact Hst2]|]. split; [exact Hd2|]. split; [exact Ha2|].
        split; [intros x Hx; rewrite Hfr2, Hm1 by exact Hx; reflexivity | split; [exact Hsh2 | split; [exact Hn2 | split; [exact Hrt2 | exact (fpc_trans _ _ _ _ Hfp1 Hfp2)]]]].
      * destruct (existsb (Z.eqb (s_pc s2)) stops) eqn:Hs2.
        -- exists s2, ms1, E. split; [left; reflexivity|]. split; [econstructor; [exact Hsvc | exact Hst | constructor]|].
           split; [exact Hd1|]. split; [apply agree_refl|]. split; [intros x Hx; rewrite Hm1; reflexivity | split; [reflexivity | split; [cbn; lia | split; [reflexivity | exact Hfp1]]]].
        -- destruct (IH stops s2 acc1 E ms1 Ht Himg Hd1 (Hwfb s2 eq_refl eq_refl)) as (L & ms2 & E2 & HL & Hst2 & Hd2 & Ha2 & Hfr2 & Hsh2 & Hn2 & Hrt2 & Hfp2).
           exists L, ms2, E2. split; [exact HL|].
           split; [econstructor; [exact Hsvc | exact Hst | exact Hst2]|]. split; [exact Hd2|]. split; [exact Ha2|].
           split; [intros x Hx; rewrite Hfr2, Hm1 by exact Hx; reflexivity | split; [exact Hsh2 | split; [exact Hn2 | split; [exact Hrt2 | exact (fpc_trans _ _ _ _ Hfp1 Hfp2)]]]].
    + pose proof (fx_step_split_inv t img s l c Hs) as Hcl.
      destruct (branch_taken BC_LTU (lden E l) (lden E (lconst c))) eqn:Htk.
      * destruct (IH stops (with_pc_fact s (s_pc s) (FCond BC_LTU l (lconst c) true)) acc E ms Ht Himg (split_child segs E s ms l c true Hden Hcl Htk) Hwf)
          as (L & ms2 & E2 & HL & Hst2 & Hd2 & Ha2 & Hfr2 & Hsh2 & Hn2 & Hrt2 & Hfp2).
        exists L, ms2, E2. split; [apply explore_acc; exact HL|]. split; [exact Hst2|]. split; [exact Hd2|]. split; [exact Ha2|].
        split; [exact Hfr2 | split; [exact Hsh2 | split; [exact Hn2 | split; [exact Hrt2 | exact Hfp2]]]].
      * destruct (IH stops (with_pc_fact s (s_pc s) (FCond BC_LTU l (lconst c) false)) (fx_explore t img f stops (with_pc_fact s (s_pc s) (FCond BC_LTU l (lconst c) true)) acc)
                     E ms Ht Himg (split_child segs E s ms l c false Hden Hcl Htk) Hwf)
          as (L & ms2 & E2 & HL & Hst2 & Hd2 & Ha2 & Hfr2 & Hsh2 & Hn2 & Hrt2 & Hfp2).
        exists L, ms2, E2. split; [exact HL|]. split; [exact Hst2|]. split; [exact Hd2|]. split; [exact Ha2|].
        split; [exact Hfr2 | split; [exact Hsh2 | split; [exact Hn2 | split; [exact Hrt2 | exact Hfp2]]]].
    + exists s, ms, E. split; [left; reflexivity|]. split; [constructor|]. split; [exact Hden|]. split; [apply agree_refl|].
      split; [intros; reflexivity | split; [reflexivity | split; [lia | split; [reflexivity | apply fpc_refl]]]].
Qed.
#[using="Type"] Theorem explore_frame2_fr : forall t img fuel stops s acc E ms,
  tbl_ok segs t -> img_ok segs img -> sden segs E s ms -> bases_wf (s_next s) (s_rgs s) = true ->
  exists L ms' E', In L (fx_explore t img fuel stops s acc) /\ isteps segs ms ms' /\ sden segs E' L ms' /\ agree (s_next s) E E' /\
    (forall x, fr_pt E (s_rgs s) x -> ms_mem ms' x = ms_mem ms x) /\ shape (s_rgs L) = shape (s_rgs s) /\
    (s_next s <= s_next L)%positive /\ rtm (s_rgs L) = rtm (s_rgs s).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros t img fuel stops s acc E ms Ht Himg Hd Hw.
  destruct (explore_frame2_frp t img fuel stops s acc E ms Ht Himg Hd Hw) as (L & ms' & E' & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & _).
  exists L, ms', E'. exact (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj H6 (conj H7 H8))))))).
Qed.


#[using="Type"] Theorem explore_frame2 : forall t img fuel stops s acc E ms,
  tbl_ok segs t -> img_ok segs img -> sden segs E s ms -> bases_wf (s_next s) (s_rgs s) = true ->
  exists L ms' E', In L (fx_explore t img fuel stops s acc) /\ isteps segs ms ms' /\ sden segs E' L ms' /\ agree (s_next s) E E' /\
    (forall x, outside E (s_rgs s) x -> ms_mem ms' x = ms_mem ms x) /\ shape (s_rgs L) = shape (s_rgs s) /\
    (s_next s <= s_next L)%positive.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros t img fuel stops s acc E ms Ht Himg Hden Hwf.
  destruct (explore_frame2_fr t img fuel stops s acc E ms Ht Himg Hden Hwf) as (L & ms' & E' & H1 & H2 & H3 & H4 & Hfr & H6 & H7 & _).
  exists L, ms', E'. split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|].
  split; [intros x Hx; exact (Hfr x (or_introl Hx)) | split; [exact H6 | exact H7]].
Qed.

#[using="Type"] Theorem loop_frame_frp : forall t img ls exits, tbl_ok segs t -> img_ok segs img -> loop_check t img ls = Some exits ->
  forall E ms, sden segs E (ls_inv ls) ms ->
  exists L ms' E', In L exits /\ isteps segs ms ms' /\ sden segs E' L ms' /\ (forall x, In x (ls_params ls) -> E' x = E x) /\
    (forall x, fr_pt E (s_rgs (ls_inv ls)) x -> ms_mem ms' x = ms_mem ms x) /\ shape (s_rgs L) = shape (s_rgs (ls_inv ls)) /\
    (s_next (ls_inv ls) <= s_next L)%positive /\ rtm (s_rgs L) = rtm (s_rgs (ls_inv ls)) /\ fpc t ms ms'.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros t img ls exits Ht Himg Hck. unfold loop_check in Hck.
  set (P := ls_inv ls) in *. set (m := ls_meas ls) in *.
  destruct (state_wf P && lwf (s_next P) m && forallb (fun x => Pos.ltb x (s_next P)) (ls_params ls))%bool eqn:Hw; [|discriminate].
  apply andb_prop in Hw as [Hw Hps]. apply andb_prop in Hw as [HwP Hwm]. rewrite forallb_forall in Hps.
  pose proof (state_wf_bases P HwP) as HbP.
  destruct (forallb (fun L => if Z.eqb (s_pc L) (s_pc P) then back_ok P m (ls_params ls) L else true) (loop_leaves t img ls)) eqn:Hall;
    [|discriminate].
  injection Hck as <-. rewrite forallb_forall in Hall.
  assert (Hind : forall n, forall E ms, Z.to_nat (bv_unsigned (lden E m)) = n -> sden segs E P ms ->
            exists L ms' E', In L (List.filter (fun L => negb (Z.eqb (s_pc L) (s_pc P))) (loop_leaves t img ls)) /\
                             isteps segs ms ms' /\ sden segs E' L ms' /\ (forall x, In x (ls_params ls) -> E' x = E x) /\
                             (forall x, fr_pt E (s_rgs P) x -> ms_mem ms' x = ms_mem ms x) /\ shape (s_rgs L) = shape (s_rgs P) /\
                             (s_next P <= s_next L)%positive /\ rtm (s_rgs L) = rtm (s_rgs P) /\ fpc t ms ms').
  { intros n. induction n as [n IH] using (well_founded_induction lt_wf). intros E ms Hn Hden.
    destruct (explore_frame2_frp t img (ls_fuel ls) (s_pc P :: ls_stops ls) P [] E ms Ht Himg Hden HbP)
      as (L & ms1 & E1 & HL & Hst1 & Hd1 & Ha1 & Hfr1 & Hsh1 & Hn1 & Hrt1 & Hfp1).
    assert (Hpar : forall x, In x (ls_params ls) -> E1 x = E x) by (intros x Hx; symmetry; apply Ha1; apply Pos.ltb_lt, Hps, Hx).
    pose proof (Hall L HL) as HLok.
    destruct (Z.eqb (s_pc L) (s_pc P)) eqn:Hpc.
    - unfold back_ok in HLok. set (σ := match_st L P) in HLok.
      apply andb_prop in HLok as [HLok Hdec]. apply andb_prop in HLok as [Hent Hfix].
      pose proof (sden_0 _ _ _ _ Hd1) as Hd10.
      pose proof (entails_sden segs E1 L P σ ms1 Hd10 Hent HwP) as HdP.
      destruct Hd10 as (_ & _ & _ & _ & _ & _ & HF1 & _).
      pose proof (meas_dec_sound E1 L σ m HF1 Hdec) as Hlt. rewrite lden_lsubst in Hlt.
      rewrite (lden_agree (s_next P) E1 E m Hwm (fun x Hx => eq_sym (Ha1 x Hx))) in Hlt.
      destruct (IH (Z.to_nat (bv_unsigned (lden (ecomp E1 σ) m))) ltac:(pose proof (u_range (ecomp E1 σ) m); lia) (ecomp E1 σ) ms1 eq_refl HdP)
        as (L2 & ms2 & E2 & HL2 & Hst2 & Hd2 & Hpar2 & Hfr2 & Hsh2 & Hn2 & Hrt2 & Hfp2).
      exists L2, ms2, E2. split; [exact HL2|]. split; [eapply isteps_trans; [exact Hst1 | exact Hst2]|]. split; [exact Hd2|].
      split; [intros x Hx; rewrite (Hpar2 x Hx); rewrite (params_fixed_sound E1 σ _ x Hfix Hx); apply Hpar; exact Hx|].
      split; [|split; [exact Hsh2 | split; [exact Hn2 | split; [exact Hrt2 | exact (fpc_trans _ _ _ _ Hfp1 Hfp2)]]]].
      intros x Hx. rewrite Hfr2; [exact (Hfr1 x Hx)|].
      unfold entails in Hent. apply andb_prop in Hent as [Hent _]. apply andb_prop in Hent as [Hent _]. apply andb_prop in Hent as [_ Hrg].
      apply (fr_pt_ent E1 (s_rgs L) (s_rgs P) σ x Hrg).
      apply (fr_pt_shape E1 (s_rgs P) (s_rgs L) x Hsh1 Hrt1).
      apply (fr_pt_agree (s_next P) E E1 (s_rgs P) x HbP Ha1). exact Hx.
    - exists L, ms1, E1. split; [apply (proj2 (filter_In _ _ _)); split; [exact HL | rewrite Hpc; reflexivity]|].
      split; [exact Hst1|]. split; [exact Hd1|]. split; [exact Hpar|]. split; [exact Hfr1 | split; [exact Hsh1 | split; [exact Hn1 | split; [exact Hrt1 | exact Hfp1]]]]. }
  intros E ms Hden. exact (Hind _ E ms eq_refl Hden).
Qed.
#[using="Type"] Theorem loop_frame_fr : forall t img ls exits, tbl_ok segs t -> img_ok segs img -> loop_check t img ls = Some exits ->
  forall E ms, sden segs E (ls_inv ls) ms ->
  exists L ms' E', In L exits /\ isteps segs ms ms' /\ sden segs E' L ms' /\ (forall x, In x (ls_params ls) -> E' x = E x) /\
    (forall x, fr_pt E (s_rgs (ls_inv ls)) x -> ms_mem ms' x = ms_mem ms x) /\ shape (s_rgs L) = shape (s_rgs (ls_inv ls)) /\
    (s_next (ls_inv ls) <= s_next L)%positive /\ rtm (s_rgs L) = rtm (s_rgs (ls_inv ls)).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros t img ls exits Ht Himg Hck E ms Hd.
  destruct (loop_frame_frp t img ls exits Ht Himg Hck E ms Hd) as (L & ms' & E' & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & _).
  exists L, ms', E'. exact (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj H6 (conj H7 H8))))))).
Qed.


#[using="Type"] Theorem loop_frame : forall t img ls exits, tbl_ok segs t -> img_ok segs img -> loop_check t img ls = Some exits ->
  forall E ms, sden segs E (ls_inv ls) ms ->
  exists L ms' E', In L exits /\ isteps segs ms ms' /\ sden segs E' L ms' /\ (forall x, In x (ls_params ls) -> E' x = E x) /\
    (forall x, outside E (s_rgs (ls_inv ls)) x -> ms_mem ms' x = ms_mem ms x) /\ shape (s_rgs L) = shape (s_rgs (ls_inv ls)) /\
    (s_next (ls_inv ls) <= s_next L)%positive.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros t img ls exits Ht Himg Hck E ms Hden.
  destruct (loop_frame_fr t img ls exits Ht Himg Hck E ms Hden) as (L & ms' & E' & H1 & H2 & H3 & H4 & Hfr & H6 & H7 & _).
  exists L, ms', E'. split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|].
  split; [intros x Hx; exact (Hfr x (or_introl Hx)) | split; [exact H6 | exact H7]].
Qed.

#[using="Type"] Lemma shape_eqb_eq : forall a b, shape_eqb a b = true -> shape a = shape b.
Proof. LiaFast.lf_pins LiaFast.u0.
  induction a as [|R a IH]; intros [|R' b] H; cbn [shape_eqb] in H; try discriminate; [reflexivity|].
  apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2]. apply lin_eqb_eq in H1. apply lin_eqb_eq in H2.
  cbn [shape List.map]. rewrite H1, H2. f_equal. exact (IH b H3).
Qed.

#[using="Type"] Lemma gen_rg_base : forall R0 Rs, rg_base (gen_rg R0 Rs) = rg_base R0.
Proof. LiaFast.lf_pins LiaFast.u0. intros R0 Rs. unfold gen_rg. reflexivity. Qed.
#[using="Type"] Lemma gen_rg_size : forall R0 Rs, rg_size (gen_rg R0 Rs) = rg_size R0.
Proof. LiaFast.lf_pins LiaFast.u0. intros R0 Rs. unfold gen_rg. reflexivity. Qed.
#[using="Type"] Lemma gen_rgs_shape : forall r0 rss, shape (gen_rgs r0 rss) = shape r0.
Proof. LiaFast.lf_pins LiaFast.u0.
  induction r0 as [|R r0 IH]; intros rss; [reflexivity|]. cbn [gen_rgs shape List.map].
  rewrite gen_rg_base, gen_rg_size. f_equal. apply IH.
Qed.

#[using="Type"] Lemma gen2_rgs : forall L0 Lrs, s_rgs (fst (gen2 L0 Lrs)) = gen_rgs (s_rgs L0) (List.map s_rgs Lrs).
Proof. LiaFast.lf_pins LiaFast.u0. intros L0 Lrs. reflexivity. Qed.
#[using="Type"] Lemma gen2_shape : forall L0 Lrs P k, gen2 L0 Lrs = (P, k) -> shape (s_rgs P) = shape (s_rgs L0).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros L0 Lrs P k H. assert (HP : P = fst (gen2 L0 Lrs)) by (rewrite H; reflexivity). subst P.
  rewrite gen2_rgs. apply gen_rgs_shape.
Qed.

Definition bases_ins (ins : list positive) (rgs : list region) : bool :=
  forallb (fun R => forallb (fun '(y, _) => existsb (Pos.eqb y) ins) (l_t (rg_base R) ++ l_t (rg_size R))) rgs.

#[using="Type"] Lemma bases_ins_shape : forall ins rgs rgs', shape rgs' = shape rgs -> bases_ins ins rgs = true -> bases_ins ins rgs' = true.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros ins rgs. induction rgs as [|R rs IH]; intros [|R' rs'] Hs H; cbn in *; try discriminate; [reflexivity|].
  injection Hs as Hb Hsz Hrs. apply andb_prop in H as [H1 H2]. apply andb_true_intro. split; [rewrite Hb, Hsz; exact H1 | exact (IH rs' Hrs H2)].
Qed.

#[using="Type"] Theorem check_frame_frp : forall t img ins depth p s finals,
  tbl_ok segs t -> img_ok segs img -> check t img ins depth p s = Some finals ->
  forall E ms, sden segs E s ms -> bases_wf (s_next s) (s_rgs s) = true -> bases_ins ins (s_rgs s) = true ->
  exists L ms' E', In L finals /\ isteps segs ms ms' /\ sden segs E' L ms' /\ (forall x, In x ins -> E' x = E x) /\
    (forall x, fr_pt E (s_rgs s) x -> ms_mem ms' x = ms_mem ms x) /\ shape (s_rgs L) = shape (s_rgs s) /\
    (s_next s <= s_next L)%positive /\ rtm (s_rgs L) = rtm (s_rgs s) /\ fpc t ms ms'.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros t img ins depth. induction depth as [|d IH]; intros p s finals Ht Himg Hck E ms Hden Hwf Hbi; cbn [check] in Hck; [discriminate|].
  destruct p as [| fuel stops ks | ls ks | fuel stops jpc pj ks | fuel wstops ks | x lo hi p].
  - injection Hck as <-. exists s, ms, E. split; [left; reflexivity|]. split; [constructor|]. split; [exact Hden|].
    split; [reflexivity | split; [intros; reflexivity | split; [reflexivity | split; [lia | split; [reflexivity | apply fpc_refl]]]]].
  - destruct (ins_below ins s) eqn:Hins; [|discriminate].
    destruct (explore_frame2_frp t img fuel stops s [] E ms Ht Himg Hden Hwf) as (L & ms1 & E1 & HL & Hst1 & Hd1 & Ha1 & Hfr1 & Hsh1 & Hn1 & Hrt1 & Hfp1).
    destruct (check_all_sound _ _ _ _ Hck L HL) as (f1 & Hf1 & Hsub).
    destruct (IH _ _ _ Ht Himg Hf1 E1 ms1 Hd1 (bases_wf_shape _ _ _ _ Hn1 Hsh1 Hwf) (bases_ins_shape _ _ _ Hsh1 Hbi))
      as (L2 & ms2 & E2 & HL2 & Hst2 & Hd2 & Hi2 & Hfr2 & Hsh2 & Hn2 & Hrt2 & Hfp2).
    exists L2, ms2, E2. split; [exact (Hsub L2 HL2)|]. split; [eapply isteps_trans; [exact Hst1 | exact Hst2]|]. split; [exact Hd2|].
    split; [|split; [|split; [rewrite Hsh2; exact Hsh1 | split; [lia | split; [rewrite Hrt2; exact Hrt1 | exact (fpc_trans _ _ _ _ Hfp1 Hfp2)]]]]].
    + intros y Hy. rewrite (Hi2 y Hy). symmetry. apply Ha1. unfold ins_below in Hins. rewrite forallb_forall in Hins.
      apply Pos.ltb_lt. exact (Hins y Hy).
    + intros y Hy. rewrite Hfr2; [exact (Hfr1 y Hy)|].
      apply (fr_pt_shape E1 (s_rgs s) (s_rgs L) y Hsh1 Hrt1). apply (fr_pt_agree (s_next s) E E1 (s_rgs s) y Hwf Ha1). exact Hy.
  - set (σ := match_st s (ls_inv ls)) in Hck.
    destruct (entails s (ls_inv ls) σ && params_fixed σ ins && ins_in_params ins ls && bases_params ls && shape_eqb (s_rgs s) (s_rgs (ls_inv ls))
              && Pos.leb (s_next s) (s_next (ls_inv ls)))%bool eqn:He; [|discriminate].
    apply andb_prop in He as [He HnP]. apply Pos.leb_le in HnP.
    apply andb_prop in He as [He Hsheq]. apply andb_prop in He as [He Hbp]. apply andb_prop in He as [He Hpar]. apply andb_prop in He as [Hent Hfix].
    pose proof (shape_eqb_eq _ _ Hsheq) as HshP.
    destruct (loop_check t img ls) as [exits|] eqn:Hlc; [|discriminate].
    pose proof (loop_check_wf _ _ _ _ Hlc) as HwP.
    pose proof (entails_sden segs E s (ls_inv ls) σ ms (sden_0 _ _ _ _ Hden) Hent HwP) as HdP.
    destruct (loop_frame_frp t img ls exits Ht Himg Hlc (ecomp E σ) ms HdP) as (L & ms1 & E1 & HL & Hst1 & Hd1 & Hp1 & Hfr1 & Hsh1 & Hn1 & Hrt1 & Hfp1).
    destruct (check_all_sound _ _ _ _ Hck L HL) as (f1 & Hf1 & Hsub).
    assert (HwL : bases_wf (s_next L) (s_rgs L) = true) by exact (bases_wf_shape _ _ _ _ Hn1 Hsh1 (state_wf_bases _ HwP)).
    assert (HbL : bases_ins ins (s_rgs L) = true).
    { apply (bases_ins_shape ins (s_rgs s)); [rewrite Hsh1; symmetry; exact HshP | exact Hbi]. }
    destruct (IH _ _ _ Ht Himg Hf1 E1 ms1 Hd1 HwL HbL) as (L2 & ms2 & E2 & HL2 & Hst2 & Hd2 & Hi2 & Hfr2 & Hsh2 & Hn2 & Hrt2 & Hfp2).
    exists L2, ms2, E2. split; [exact (Hsub L2 HL2)|]. split; [eapply isteps_trans; [exact Hst1 | exact Hst2]|]. split; [exact Hd2|].
    assert (HrtP : rtm (s_rgs s) = rtm (s_rgs (ls_inv ls))).
    { unfold entails in Hent. apply andb_prop in Hent as [Hent _]. apply andb_prop in Hent as [Hent _]. apply andb_prop in Hent as [_ Hrg].
      exact (rgs_ent_rtm _ _ _ Hrg). }
    split; [|split; [|split; [rewrite Hsh2, Hsh1; symmetry; exact HshP | split; [lia | split; [rewrite Hrt2, Hrt1; symmetry; exact HrtP | exact (fpc_trans _ _ _ _ Hfp1 Hfp2)]]]]].
    + intros y Hy. rewrite (Hi2 y Hy). unfold ins_in_params in Hpar. rewrite forallb_forall in Hpar.
      pose proof (Hpar y Hy) as Hyp. apply existsb_exists in Hyp as (z & Hz & Hyz). apply Pos.eqb_eq in Hyz. subst z.
      rewrite (Hp1 y Hz). apply (params_fixed_sound E σ ins y Hfix Hy).
    + intros y Hy.
      assert (HyP : fr_pt (ecomp E σ) (s_rgs (ls_inv ls)) y).
      { unfold entails in Hent. apply andb_prop in Hent as [Hent _]. apply andb_prop in Hent as [Hent _]. apply andb_prop in Hent as [_ Hrg].
        exact (proj1 (fr_pt_ent E (s_rgs s) (s_rgs (ls_inv ls)) σ y Hrg) Hy). }
      rewrite Hfr2; [exact (Hfr1 y HyP)|].
      apply (fr_pt_shape E1 (s_rgs (ls_inv ls)) (s_rgs L) y Hsh1 Hrt1).
      apply (proj1 (fr_pt_params (ecomp E σ) E1 (ls_params ls) (s_rgs (ls_inv ls)) y Hbp Hp1)). exact HyP.
  - (* [comment removed for export] *)
    destruct (ins_below ins s) eqn:Hins; [|discriminate].
    destruct (explore_frame2_frp t img fuel (jpc :: stops) s [] E ms Ht Himg Hden Hwf) as (L & ms1 & E1 & HL & Hst1 & Hd1 & Ha1 & Hfr1 & Hsh1 & Hn1 & Hrt1 & Hfp1).
    assert (Hin : forall x, In x ins -> E1 x = E x).
    { intros x Hx. symmetry. apply Ha1. unfold ins_below in Hins. rewrite forallb_forall in Hins. apply Pos.ltb_lt. exact (Hins x Hx). }
    set (Ls := fx_explore t img fuel (jpc :: stops) s []) in *.
    destruct (check_all (check t img ins d) ks (List.filter (fun L => negb (Z.eqb (s_pc L) jpc)) Ls)) as [fo|] eqn:Hfo; [|discriminate].
    assert (Hreach : exists L' ms' E', isteps segs ms ms' /\ sden segs E' L' ms' /\ (forall x, In x ins -> E' x = E x) /\
              (forall y, fr_pt E (s_rgs s) y -> ms_mem ms' y = ms_mem ms y) /\ shape (s_rgs L') = shape (s_rgs s) /\
              (s_next s <= s_next L')%positive /\ rtm (s_rgs L') = rtm (s_rgs s) /\ fpc t ms ms' /\
              ((Z.eqb (s_pc L') jpc = true /\ In L' (List.filter (fun L => Z.eqb (s_pc L) jpc) Ls ++ List.filter (fun L => Z.eqb (s_pc L) jpc) fo)) \/
               (Z.eqb (s_pc L') jpc = false /\ In L' fo))).
    { destruct (Z.eqb (s_pc L) jpc) eqn:Hpc.
      - exists L, ms1, E1. split; [exact Hst1|]. split; [exact Hd1|]. split; [exact Hin|]. split; [exact Hfr1|]. split; [exact Hsh1|].
        split; [exact Hn1|]. split; [exact Hrt1|]. split; [exact Hfp1|]. left. split; [exact Hpc|].
        apply in_or_app. left. apply filter_In. split; [exact HL | exact Hpc].
      - assert (HLo : In L (List.filter (fun L => negb (Z.eqb (s_pc L) jpc)) Ls)) by (apply filter_In; split; [exact HL | rewrite Hpc; reflexivity]).
        destruct (check_all_sound _ _ _ _ Hfo L HLo) as (f1 & Hf1 & Hsub).
        destruct (IH _ _ _ Ht Himg Hf1 E1 ms1 Hd1 (bases_wf_shape _ _ _ _ Hn1 Hsh1 Hwf) (bases_ins_shape _ _ _ Hsh1 Hbi))
          as (L2 & ms2 & E2 & HL2 & Hst2 & Hd2 & Hi2 & Hfr2 & Hsh2 & Hn2 & Hrt2 & Hfp2).
        exists L2, ms2, E2. split; [eapply isteps_trans; [exact Hst1 | exact Hst2]|]. split; [exact Hd2|].
        split; [intros x Hx; rewrite (Hi2 x Hx); exact (Hin x Hx)|].
        split; [intros y Hy; rewrite Hfr2; [exact (Hfr1 y Hy)|];
                apply (fr_pt_shape E1 (s_rgs s) (s_rgs L) y Hsh1 Hrt1); apply (fr_pt_agree (s_next s) E E1 (s_rgs s) y Hwf Ha1); exact Hy|].
        split; [rewrite Hsh2; exact Hsh1|]. split; [lia|]. split; [rewrite Hrt2; exact Hrt1|]. split; [exact (fpc_trans _ _ _ _ Hfp1 Hfp2)|].
        destruct (Z.eqb (s_pc L2) jpc) eqn:Hpc2.
        + left. split; [reflexivity|]. apply in_or_app. right. apply filter_In. split; [exact (Hsub L2 HL2) | exact Hpc2].
        + right. split; [reflexivity | exact (Hsub L2 HL2)]. }
    destruct Hreach as (L' & ms' & E' & Hst' & Hd' & Hi' & Hfr' & Hsh' & Hn' & Hrt' & Hfp' & Hcase).
    destruct (List.filter (fun L => Z.eqb (s_pc L) jpc) Ls ++ List.filter (fun L => Z.eqb (s_pc L) jpc) fo) as [|L0 Lrs] eqn:HJ.
    + injection Hck as <-. destruct Hcase as [(_ & Hn)|(Hpc' & Hfo')]; [destruct Hn|].
      exists L', ms', E'. split; [apply filter_In; split; [exact Hfo' | rewrite Hpc'; reflexivity]|]. split; [exact Hst'|]. split; [exact Hd'|].
      split; [exact Hi'|]. split; [exact Hfr'|]. split; [exact Hsh' | split; [exact Hn' | split; [exact Hrt' | exact Hfp']]].
    + destruct (gen2 L0 Lrs) as [P k] eqn:Hgen. set (n := max_next Lrs (s_next L0)) in *.
      destruct (state_wf P && forallb (fun L => (join_ent L P (match_st L P) n k && params_fixed (match_st L P) ins)%bool) (L0 :: Lrs)
                && shape_eqb (s_rgs s) (s_rgs P) && Pos.leb (s_next s) (s_next P))%bool eqn:Hw; [|discriminate].
      apply andb_prop in Hw as [Hw HnP]. apply andb_prop in Hw as [Hw HshP]. apply Pos.leb_le in HnP. apply shape_eqb_eq in HshP.
      apply andb_prop in Hw as [Hwf' Hall]. rewrite forallb_forall in Hall.
      destruct (check t img ins d pj P) as [f1|] eqn:Hf1; [|discriminate]. injection Hck as <-.
      destruct Hcase as [(Hpc' & HLJ)|(Hpc' & Hfo')].
      * pose proof (Hall L' HLJ) as HLe. apply andb_prop in HLe as [Hje Hfix].
        pose proof (sden0_sden segs P (ecomp E' (match_st L' P)) ms' Hwf' (join_ent_sound segs E' L' P (match_st L' P) n k ms' (sden_0 _ _ _ _ Hd') Hje)) as HdP.
        assert (HbP : bases_ins ins (s_rgs P) = true) by (apply (bases_ins_shape ins (s_rgs s)); [symmetry; exact HshP | exact Hbi]).
        destruct (IH _ _ _ Ht Himg Hf1 _ ms' HdP (state_wf_bases _ Hwf') HbP) as (L2 & ms2 & E2 & HL2 & Hst2 & Hd2 & Hi2 & Hfr2 & Hsh2 & Hn2 & Hrt2 & Hfp2).
        exists L2, ms2, E2. split; [apply in_or_app; left; exact HL2|]. split; [eapply isteps_trans; [exact Hst' | exact Hst2]|].
        split; [exact Hd2|]. split; [intros x Hx; rewrite (Hi2 x Hx), (params_fixed_sound E' _ ins x Hfix Hx); exact (Hi' x Hx)|].
        assert (HrtP : rtm (s_rgs L') = rtm (s_rgs P)).
        { unfold join_ent in Hje. apply andb_prop in Hje as [Hje0 _]. apply andb_prop in Hje0 as [Hje0 _]. apply andb_prop in Hje0 as [Hje0 _].
          apply andb_prop in Hje0 as [Hje0 _]. apply andb_prop in Hje0 as [Hje0 _]. apply andb_prop in Hje0 as [_ Hrg0].
          exact (rgs_ent_rtm _ _ _ Hrg0). }
        split; [|split; [rewrite Hsh2; symmetry; exact HshP | split; [lia | split; [rewrite Hrt2, <- HrtP; exact Hrt' | exact (fpc_trans _ _ _ _ Hfp' Hfp2)]]]].
        intros y Hy. rewrite Hfr2; [exact (Hfr' y Hy)|].
        unfold join_ent in Hje. apply andb_prop in Hje as [Hje _]. apply andb_prop in Hje as [Hje _]. apply andb_prop in Hje as [Hje _].
        apply andb_prop in Hje as [Hje _]. apply andb_prop in Hje as [Hje _]. apply andb_prop in Hje as [_ Hrg].
        apply (fr_pt_ent E' (s_rgs L') (s_rgs P) (match_st L' P) y Hrg).
        apply (fr_pt_shape E' (s_rgs s) (s_rgs L') y Hsh' Hrt').
        apply (proj1 (fr_pt_params E E' ins (s_rgs s) y Hbi Hi')). exact Hy.
      * exists L', ms', E'. split; [apply in_or_app; right; apply filter_In; split; [exact Hfo' | rewrite Hpc'; reflexivity]|].
        split; [exact Hst'|]. split; [exact Hd'|]. split; [exact Hi'|]. split; [exact Hfr'|]. split; [exact Hsh' | split; [exact Hn' | split; [exact Hrt' | exact Hfp']]].
  - destruct (List.find (fun L => Z.eqb (s_pc L) (s_pc s)) (fx_explore t img fuel (s_pc s :: wstops) s [])) as [s1|]; [|discriminate].
    destruct (widen s s1 fuel wstops) as [ls|]; [|discriminate].
    destruct (check t img ins d (PLoop ls ks) s) as [f|] eqn:Hc1.
    + injection Hck as <-. exact (IH _ _ _ Ht Himg Hc1 E ms Hden Hwf Hbi).
    + exact (IH _ _ _ Ht Himg Hck E ms Hden Hwf Hbi).
  - (* [comment removed for export] *)
    destruct (irange (s_facts s) x) as [a b] eqn:Hir.
    destruct (Z.leb lo a && Z.leb b hi && Z.leb (hi - lo) 255 && lwf (s_next s) x)%bool eqn:Hc; [|discriminate].
    apply andb_prop in Hc as [Hc Hwx]. apply andb_prop in Hc as [Hc _]. apply andb_prop in Hc as [Hla Hbh]. apply Z.leb_le in Hla, Hbh.
    pose proof (sden_0 _ _ _ _ Hden) as Hd0. destruct Hd0 as (_ & _ & _ & _ & _ & _ & HF & _).
    pose proof (irange_sound E (s_facts s) x HF) as Hr. rewrite Hir in Hr. cbn [fst snd] in Hr.
    set (kv := bv_unsigned (lden E x)) in *.
    assert (Hk : In kv (z_upto (Z.to_nat (hi - lo + 1)) lo [])).
    { assert (Hgen : forall n acc, In kv acc \/ (lo <= kv < lo + Z.of_nat n) -> In kv (z_upto n lo acc)).
      { induction n as [|n IHn]; intros acc Hx; cbn [z_upto]; [destruct Hx as [Hx|Hx]; [exact Hx | lia]|].
        apply IHn. destruct Hx as [Hx|Hx]; [left; right; exact Hx|].
        destruct (Z.eq_dec kv (lo + Z.of_nat n)) as [->|Hne]; [left; left; reflexivity | right; lia]. }
      apply Hgen. right. lia. }
    assert (Hcc : forall ks fin, check_cases (check t img ins d p) s x ks = Some fin -> In kv ks ->
              exists f1, check t img ins d p (add_fact s (FRange x kv kv)) = Some f1 /\ (forall y, In y f1 -> In y fin)).
    { induction ks as [|k0 ks IHks]; intros fin Hf Hin; [destruct Hin|]. cbn [check_cases] in Hf.
      destruct (check t img ins d p (add_fact s (FRange x k0 k0))) as [f1|] eqn:H1; [|discriminate].
      destruct (check_cases (check t img ins d p) s x ks) as [f2|] eqn:H2; [|discriminate]. injection Hf as <-.
      destruct Hin as [->|Hin].
      - exists f1. split; [exact H1|]. intros y Hy. apply in_or_app. left. exact Hy.
      - destruct (IHks f2 eq_refl Hin) as (f & Hf & Hsub). exists f. split; [exact Hf|]. intros y Hy. apply in_or_app. right. exact (Hsub y Hy). }
    destruct (Hcc _ _ Hck Hk) as (f1 & Hf1 & Hsub).
    assert (Hd' : sden segs E (add_fact s (FRange x kv kv)) ms).
    { intros E' Ha'. destruct (Hden E' Ha') as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8).
      unfold sden0; cbn [s_pc s_regs s_rgs s_facts s_resv add_fact]. split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
      split; [exact H4|]. split; [exact H5|]. split; [exact H6|]. split; [|exact H8]. constructor; [|exact H7].
      cbn [fact_ok]. rewrite <- (lden_agree (s_next s) E E' x Hwx Ha'). unfold kv. lia. }
    destruct (IH _ _ _ Ht Himg Hf1 E ms Hd' Hwf Hbi) as (L2 & ms2 & E2 & HL2 & Hst2 & Hd2 & Hi2 & Hfr2 & Hsh2 & Hn2 & Hrt2 & Hfp2).
    exists L2, ms2, E2. split; [exact (Hsub L2 HL2)|]. split; [exact Hst2|]. split; [exact Hd2|]. split; [exact Hi2|].
    split; [exact Hfr2 | split; [exact Hsh2 | split; [exact Hn2 | split; [exact Hrt2 | exact Hfp2]]]].
Qed.
#[using="Type"] Theorem check_frame_fr : forall t img ins depth p s finals,
  tbl_ok segs t -> img_ok segs img -> check t img ins depth p s = Some finals ->
  forall E ms, sden segs E s ms -> bases_wf (s_next s) (s_rgs s) = true -> bases_ins ins (s_rgs s) = true ->
  exists L ms' E', In L finals /\ isteps segs ms ms' /\ sden segs E' L ms' /\ (forall x, In x ins -> E' x = E x) /\
    (forall x, fr_pt E (s_rgs s) x -> ms_mem ms' x = ms_mem ms x) /\ shape (s_rgs L) = shape (s_rgs s) /\
    (s_next s <= s_next L)%positive /\ rtm (s_rgs L) = rtm (s_rgs s).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros t img ins depth p s finals Ht Himg Hck E ms Hd Hw Hbi.
  destruct (check_frame_frp t img ins depth p s finals Ht Himg Hck E ms Hd Hw Hbi) as (L & ms' & E' & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & _).
  exists L, ms', E'. exact (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj H6 (conj H7 H8))))))).
Qed.


#[using="Type"] Theorem check_frame : forall t img ins depth p s finals,
  tbl_ok segs t -> img_ok segs img -> check t img ins depth p s = Some finals ->
  forall E ms, sden segs E s ms -> bases_wf (s_next s) (s_rgs s) = true -> bases_ins ins (s_rgs s) = true ->
  exists L ms' E', In L finals /\ isteps segs ms ms' /\ sden segs E' L ms' /\ (forall x, In x ins -> E' x = E x) /\
    (forall x, outside E (s_rgs s) x -> ms_mem ms' x = ms_mem ms x) /\ shape (s_rgs L) = shape (s_rgs s) /\
    (s_next s <= s_next L)%positive.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros t img ins depth p s finals Ht Himg Hck E ms Hden Hwf Hbi.
  destruct (check_frame_fr t img ins depth p s finals Ht Himg Hck E ms Hden Hwf Hbi) as (L & ms' & E' & H1 & H2 & H3 & H4 & Hfr & H6 & H7 & _).
  exists L, ms', E'. split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|].
  split; [intros x Hx; exact (Hfr x (or_introl Hx)) | split; [exact H6 | exact H7]].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma fr_pt_rt : forall E rgs R x, In R rgs -> rg_kind R = RT -> in_rg E R x -> fr_pt E rgs x.
Proof. LiaFast.lf_pins LiaFast.u0. intros E rgs R x HR Hk Hin. right. apply Exists_exists. exists R. split; [exact HR|]. rewrite Hk. split; [reflexivity | exact Hin]. Qed.

End WithSegs.
