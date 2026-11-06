(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.fast_float.from_chars.images Require Import Asan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec ShapeSet RealizesCfg AsanAcct PlacementCount AllocNodesCfg.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import FxLin FxCore FxSound FxMem FxSubst FxEnt FxCall.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require Import FxBacking FxChDen FxWvC FxChMain.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcPri.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcAst AcHA AcFam AcPri AcFam2 AcFam2Ok.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcHA.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcFam3.

Module AcLvLib.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.fast_float.from_chars.images Require Import Asan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec ShapeSet RealizesCfg FxLin FxCore FxSound FxMem FxFacts FxSubst FxEnt FxDrv.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require Import FxBacking FxChDen FxChLib FxChMain.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcPri.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcAst.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcHA.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcHA AcPri.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcPriSepOk.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcPriSepOk AcPriStep AcMALp AcMALlib AcNPop.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcFam2.
Import OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcPri.AcDepSep OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcAst OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcHA.AcLv OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcHA OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcPri OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcPriSepOk.AcPriSep OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcPriSepOk OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcPriStep OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcMALp OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcMALlib OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcNPop OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcFam2.AcExt.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcFam3.
Import OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcFam3.AcLvN.
Import ListNotations.
Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma lv_okb_ok : forall a, lv_okb a = true -> lv_ok a.
Proof.
  intros a H. unfold lv_okb in H. apply orb_prop in H as [H|H]; [left; apply Nat.eqb_eq; exact H|].
  apply andb_prop in H as [H1 H2]. right. split; [apply Nat.eqb_eq; exact H1 | apply Nat.leb_le; exact H2].
Qed.

(* [comment removed for export] *)
Lemma rng_disj_upd : forall l l' i r',
  (forall j, j <> i -> nth_error l' j = nth_error l j) -> nth_error l' i = Some r' -> rng_disj l ->
  (forall j q, j <> i -> nth_error l j = Some q -> forall x, ~ (in_rg r' x /\ in_rg q x)) -> rng_disj l'.
Proof.
  intros l l' i r' Hoth Hi HD Hnew a b p q Hab Ha Hb x [X1 X2].
  destruct (Nat.eq_dec a i) as [->|Na]; destruct (Nat.eq_dec b i) as [->|Nb].
  - exact (Hab eq_refl).
  - rewrite Hi in Ha. injection Ha as <-. rewrite (Hoth b Nb) in Hb. exact (Hnew b q Nb Hb x (conj X1 X2)).
  - rewrite Hi in Hb. injection Hb as <-. rewrite (Hoth a Na) in Ha. exact (Hnew a p Na Ha x (conj X2 X1)).
  - rewrite (Hoth a Na) in Ha. rewrite (Hoth b Nb) in Hb. exact (HD a b p q Hab Ha Hb x (conj X1 X2)).
Qed.

(* [comment removed for export] *)
Lemma lv_put_other : forall a k B XP f n c n8 k' i, lv_ok a -> (k < LV_N)%nat -> k' <> k -> (6 * k' <= i < 6 * k' + 6)%nat ->
  lv_nth (lv_put a k B XP f n c n8) i = lv_nth a i.
Proof.
  intros a k B XP f n c n8 k' i Hok Hk Hne Hi. rewrite (lv_put_nth a k B XP f n c n8 _ Hok Hk).
  destruct (Nat.leb (6 * k) i) eqn:E1; [|reflexivity]. destruct (Nat.ltb i (6 * k + 6)) eqn:E2; [|reflexivity].
  apply Nat.leb_le in E1. apply Nat.ltb_lt in E2. exfalso. lia.
Qed.
Lemma lv_put_at : forall a k B XP f n c n8 j, lv_ok a -> (k < LV_N)%nat -> (j < 6)%nat ->
  lv_nth (lv_put a k B XP f n c n8) (6 * k + j) = nth j [B; XP; f; n; c; n8] lc0.
Proof.
  intros a k B XP f n c n8 j Hok Hk Hj. rewrite (lv_put_nth a k B XP f n c n8 _ Hok Hk).
  replace (Nat.leb (6 * k) (6 * k + j) && Nat.ltb (6 * k + j) (6 * k + 6))%bool with true
    by (symmetry; apply andb_true_intro; split; [apply Nat.leb_le | apply Nat.ltb_lt]; lia).
  replace (6 * k + j - 6 * k)%nat with j by lia. reflexivity.
Qed.
Lemma lv_put_self : forall a k B XP f n c n8, lv_ok a -> (k < LV_N)%nat -> let a' := lv_put a k B XP f n c n8 in
  lv_B a' k = B /\ lv_XP a' k = XP /\ lv_f a' k = f /\ lv_n a' k = n /\ lv_c a' k = c /\ lv_n8 a' k = n8.
Proof.
  intros a k B XP f n c n8 Hok Hk. cbv zeta. unfold lv_B, lv_XP, lv_f, lv_n, lv_c, lv_n8.
  replace (6 * k)%nat with (6 * k + 0)%nat at 1 by lia.
  rewrite !(lv_put_at a k B XP f n c n8 _ Hok Hk) by lia. repeat split; reflexivity.
Qed.
Lemma lv_rng_other : forall E a k B XP f n c n8 k', lv_ok a -> (k < LV_N)%nat -> k' <> k ->
  lv_rng E (lv_put a k B XP f n c n8) k' = lv_rng E a k'.
Proof.
  intros E a k B XP f n c n8 k' Hok Hk Hne. unfold lv_rng, lv_lo, lv_sz, lv_XP, lv_B, lv_n8.
  rewrite !(lv_put_other a k B XP f n c n8 k' _ Hok Hk Hne) by lia. reflexivity.
Qed.
Lemma lv_sem_other : forall E pz m0 a k B XP f n c n8 k', lv_ok a -> (k < LV_N)%nat -> k' <> k ->
  lv_sem E pz m0 a k' -> lv_sem E pz m0 (lv_put a k B XP f n c n8) k'.
Proof.
  intros E pz m0 a k B XP f n c n8 k' Hok Hk Hne H. unfold lv_sem, lv_lo, lv_sz, lv_XP, lv_B, lv_n8, lv_f, lv_n, lv_c in *.
  rewrite !(lv_put_other a k B XP f n c n8 k' _ Hok Hk Hne) by lia. exact H.
Qed.

(* [comment removed for export] *)
Lemma lv_rngs_nth : forall E a t, nth_error (List.map (lv_rng E a) (seq 0 LV_N)) t = if Nat.ltb t LV_N then Some (lv_rng E a t) else None.
Proof. intros E a t. unfold LV_N. destruct t as [|[|[|t]]]; try reflexivity. cbn [seq List.map nth_error]. destruct t; reflexivity. Qed.
Theorem lv_inv_put : forall E a m0 k B XP f n c n8, lv_ok a -> (k < LV_N)%nat -> lv_inv E a m0 ->
  let a' := lv_put a k B XP f n c n8 in
  lv_sem E (pden E a) m0 a' k ->
  (forall q, (In q (e_rngs E a) \/ exists k', (k' < LV_N)%nat /\ k' <> k /\ q = lv_rng E a k') -> forall x, ~ (in_rg (lv_rng E a' k) x /\ in_rg q x)) ->
  lv_inv E a' m0.
Proof.
  intros E a m0 k B XP f n c n8 Hok Hk [HS HD]. cbv zeta. intros Hnew Hap.
  destruct (lv_put_rest a k B XP f n c n8) as (_ & _ & _ & _ & _ & Epr & Eext). cbv zeta in Epr, Eext.
  assert (Epd : pden E (lv_put a k B XP f n c n8) = pden E a) by (unfold pden; rewrite Epr; reflexivity).
  split.
  - intros k' Hk'. rewrite Epd. destruct (Nat.eq_dec k' k) as [->|Hne]; [exact Hnew|].
    exact (lv_sem_other E _ m0 a k B XP f n c n8 k' Hok Hk Hne (HS k' Hk')).
  - set (a' := lv_put a k B XP f n c n8) in *.
    assert (Ee : e_rngs E a' = e_rngs E a) by (unfold e_rngs; rewrite Eext; reflexivity).
    apply (rng_disj_upd (x_rngs E a) (x_rngs E a') (List.length (e_rngs E a) + k)%nat (lv_rng E a' k)); [| |exact HD|].
    + intros j Hj. unfold x_rngs. rewrite Ee. destruct (Nat.lt_ge_cases j (List.length (e_rngs E a))) as [Hl|Hg].
      * rewrite !nth_error_app1 by exact Hl. reflexivity.
      * rewrite !nth_error_app2 by exact Hg. set (t := (j - List.length (e_rngs E a))%nat) in *.
        assert (Ht : t <> k) by (unfold t; lia). rewrite !lv_rngs_nth.
        destruct (Nat.ltb t LV_N); [|reflexivity]. unfold a'. rewrite (lv_rng_other E a k B XP f n c n8 t Hok Hk Ht). reflexivity.
    + unfold x_rngs. rewrite Ee, nth_error_app2 by lia. replace (List.length (e_rngs E a) + k - List.length (e_rngs E a))%nat with k by lia.
      rewrite lv_rngs_nth. rewrite (proj2 (Nat.ltb_lt k LV_N) Hk). reflexivity.
    + intros j q Hj Hq. apply Hap. unfold x_rngs in Hq. destruct (Nat.lt_ge_cases j (List.length (e_rngs E a))) as [Hl|Hg].
      * rewrite nth_error_app1 in Hq by exact Hl. left. exact (nth_error_In _ _ Hq).
      * rewrite nth_error_app2 in Hq by exact Hg. set (t := (j - List.length (e_rngs E a))%nat) in *. right.
        rewrite lv_rngs_nth in Hq. destruct (Nat.ltb t LV_N) eqn:Et; [|discriminate]. apply Nat.ltb_lt in Et.
        exists t. split; [exact Et|]. split; [unfold t; lia|]. injection Hq as <-. reflexivity.
Qed.
(* [comment removed for export] *)
Corollary lv_inv_put0 : forall E a m0 k B XP f n c n8, lv_ok a -> (k < LV_N)%nat -> uE E B = 0 -> lv_inv E a m0 -> lv_inv E (lv_put a k B XP f n c n8) m0.
Proof.
  intros E a m0 k B XP f n c n8 Hok Hk HB Hlv. apply (lv_inv_put E a m0 k B XP f n c n8 Hok Hk Hlv).
  - unfold lv_sem. destruct (lv_put_self a k B XP f n c n8 Hok Hk) as (-> & _). rewrite HB. split; [lia | intros X; discriminate X].
  - intros q _ x [X _]. unfold in_rg, lv_rng in X. cbn [fst snd] in X.
    destruct (lv_put_self a k B XP f n c n8 Hok Hk) as (EB & _). rewrite EB, HB in X. lia.
Qed.
(* [comment removed for export] *)
Lemma x_rngs_put0_in : forall E a k B XP f n c n8 q x, lv_ok a -> (k < LV_N)%nat -> uE E B = 0 ->
  In q (x_rngs E (lv_put a k B XP f n c n8)) -> in_rg q x ->
  exists j, j <> (List.length (e_rngs E a) + k)%nat /\ nth_error (x_rngs E a) j = Some q.
Proof.
  intros E a k B XP f n c n8 q x Hok Hk HB Hq Hx. apply In_nth_error in Hq as (t & Ht).
  destruct (lv_put_rest a k B XP f n c n8) as (_ & _ & _ & _ & _ & _ & Eext). cbv zeta in Eext.
  assert (Ee : e_rngs E (lv_put a k B XP f n c n8) = e_rngs E a) by (unfold e_rngs; rewrite Eext; reflexivity).
  unfold x_rngs in Ht. rewrite Ee in Ht. exists t. unfold x_rngs.
  destruct (Nat.lt_ge_cases t (List.length (e_rngs E a))) as [Hl|Hg].
  - rewrite nth_error_app1 in Ht by exact Hl. rewrite nth_error_app1 by exact Hl. split; [lia | exact Ht].
  - rewrite nth_error_app2 in Ht by exact Hg. rewrite nth_error_app2 by exact Hg. set (t' := (t - List.length (e_rngs E a))%nat) in *.
    rewrite lv_rngs_nth in Ht. rewrite lv_rngs_nth. destruct (Nat.ltb t' LV_N) eqn:Et; [|discriminate]. injection Ht as <-.
    destruct (Nat.eq_dec t' k) as [->|Hne].
    + exfalso. unfold in_rg, lv_rng in Hx. cbn [fst snd] in Hx. destruct (lv_put_self a k B XP f n c n8 Hok Hk) as (EB & _). rewrite EB, HB in Hx. lia.
    + split; [unfold t' in Hne; lia|]. rewrite (lv_rng_other E a k B XP f n c n8 t' Hok Hk Hne). reflexivity.
Qed.
(* [comment removed for export] *)
Lemma rng_disj_app_l : forall l r, rng_disj (l ++ r) -> rng_disj l.
Proof.
  intros l r H i j p q Hij Hi Hj. apply (H i j p q Hij); rewrite nth_error_app1; first [exact Hi | exact Hj | apply nth_error_Some; congruence].
Qed.
Corollary lv_inv_clear : forall E a m0, lv_inv E a m0 -> lv_inv E (lv_clear a) m0.
Proof.
  intros E a m0 [_ HD]. apply lv_inv_none; [reflexivity|]. change (e_rngs E (lv_clear a)) with (e_rngs E a). exact (rng_disj_app_l _ _ HD).
Qed.

(* [comment removed for export] *)
Lemma HA_on_lv : forall E M a a' m0, HA_on E M a m0 ->
  a_on a' = a_on a -> a_rgs a' = a_rgs a -> a_own a' = a_own a -> a_dep a' = a_dep a -> a_nl a' = a_nl a -> a_pri a' = a_pri a ->
  (forall p, In p (a_live a') -> In p (a_live a) \/ snd p = lc0) ->
  (a_pri a <> [] -> lv_inv E a m0 -> lv_inv E a' m0) ->
  HA_on E M a' m0.
Proof.
  intros E M a a' m0 [Hdep Hown Hownx Hhi HgD HgB Hpri] Eon Erg Eow Edp Enl Epr Hlive Hlvx.
  assert (Epd : pden E a' = pden E a) by (unfold pden; rewrite Epr; reflexivity).
  assert (Eext : a_ext a' = a_ext a) by (unfold a_ext; rewrite Erg; reflexivity).
  constructor.
  - unfold dD1, dB1. rewrite Edp, Enl. exact Hdep.
  - unfold dD1, dB1. rewrite Edp. exact Hown.
  - rewrite Eow, Hownx. unfold aown_of. rewrite Edp, Epr. unfold pri_own, cls_own, l_cb, l_rip, l_rb, l_fa, l_shu, l_shf, p_ca, p_sb, p_sh, p_z, p_nth. rewrite Epr. reflexivity.
  - unfold dD1, dB1. rewrite Edp. exact Hhi.
  - rewrite Edp. exact HgD.
  - rewrite Edp. exact HgB.
  - intros Hne. rewrite Epr in Hne. destruct (Hpri Hne) as [Hi Ho Hp Ht Hz Hs Hxt Hlv Hsd]. constructor; [| | | | | | |exact (Hlvx Hne Hlv)|].
    + unfold INV_A. rewrite Epd. exact Hi.
    + intros x Hx0 Hf. unfold pri_foot in Hf. rewrite Epd in Hf. exact (Ho x Hx0 Hf).
    + unfold p_pg, p_nth. rewrite Epr. exact Hp.
    + unfold p_tg, p_nth. rewrite Epr. exact Ht.
    + intros x Hx0. apply Hz. unfold pri_shadow in *. rewrite Epd in Hx0. exact Hx0.
    + intros p Hp'. rewrite Epd. destruct (Hlive p Hp') as [Hin|Hz0]; [exact (Hs p Hin) | exact (po_sep_carrier E _ p Hz0)].
    + intros p Hp'. rewrite Eext in Hp'. rewrite Epd. exact (Hxt p Hp').
    + intros p Hp' x Hx0. unfold dD1, dB1. rewrite Edp.
      destruct (Hlive p Hp') as [Hin|Hz0]; [exact (Hsd p Hin x Hx0) | exact (po_sepd_carrier E _ _ p Hz0 x Hx0)].
Qed.
End AcLvLib.

Module AcLvNil.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.fast_float.from_chars.images Require Import Asan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec ShapeSet RealizesCfg FxLin FxCore FxSound FxMem FxFacts FxSubst FxEnt FxDrv.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require Import FxBacking FxChDen FxChLib FxChMain.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcPri.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcAst.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcHA.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcHA AcPri.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcPriSepOk.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcPriSepOk AcPriStep AcMALp AcMALlib AcNPop.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcFam2.
Import OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcPri.AcDepSep OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcAst OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcHA.AcLv OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcHA OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcPri OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcPriSepOk.AcPriSep OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcPriSepOk OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcPriStep OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcMALp OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcMALlib OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcNPop OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcFam2.AcExt.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcFam3.
Import OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcFam3.AcLvN OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcFam3Ok.AcLvLib.
Import ListNotations.
Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section LvNil.
Variable cfg : SpuriousCfg.
Variable LIMIT : Z.
Variable model0 : Model.

(* [comment removed for export] *)
#[using="Type"] Lemma lv_write_node : forall S M a a' mem0 E ms model T,
  DEN ASEGS LIMIT model0 mem0 E S M ms model -> HA E M a mem0 ->
  a_on a' = a_on a -> a_rgs a' = a_rgs a -> a_own a' = a_own a -> a_dep a' = a_dep a -> a_nl a' = a_nl a -> a_pri a' = a_pri a ->
  (forall p, In p (a_live a') -> In p (a_live a) \/ snd p = lc0) ->
  (lv_inv E a mem0 -> lv_inv E a' mem0) ->
  (forall E' mem0' ms' model', agree (s_next S) E E' -> frz_same E M mem0 mem0' -> DEN ASEGS LIMIT model0 mem0' E' S M ms' model' ->
     HA E' M a' mem0' -> realizes_cfg ASEGS cfg (mkCfg ms' model') T) ->
  realizes_cfg ASEGS cfg (mkCfg ms model) T.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros S M a a' mem0 E ms model T Hd HHA Eon Erg Eow Edp Enl Epr Hlive Hlv Hk.
  apply (Hk E mem0 ms model); [apply agree_refl | intros p Hp w Hw; reflexivity | exact Hd |].
  intros Hon. rewrite Eon in Hon.
  exact (HA_on_lv E M a a' mem0 (HHA Hon) Eon Erg Eow Edp Enl Epr Hlive (fun _ => Hlv)).
Qed.

#[using="Type"] Theorem nstashnil_node : forall k r S M a S' M' a', apost_stashnil k r S M a = Some (S', M', a') ->
  forall mem0 E ms model T, DEN ASEGS LIMIT model0 mem0 E S M ms model -> awf (s_next S) a = true -> HA E M a mem0 ->
  (forall E' mem0' ms' model', agree (s_next S) E E' -> frz_same E M mem0 mem0' -> DEN ASEGS LIMIT model0 mem0' E' S' M' ms' model' ->
     HA E' M' a' mem0' -> realizes_cfg ASEGS cfg (mkCfg ms' model') T) ->
  realizes_cfg ASEGS cfg (mkCfg ms model) T.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros k r S M a S' M' a' H mem0 E ms model T Hd Haw HHA Hk. unfold apost_stashnil in H.
  apply obool_some in H as (Hc & H). injection H as <- <- <-.
  apply andb_prop in Hc as [Hc _]. apply andb_prop in Hc as [Hc _]. apply andb_prop in Hc as [Hc CB]. apply andb_prop in Hc as [_ Hfree].
  unfold lv_free_b in Hfree. apply andb_prop in Hfree as [Hfree _]. apply andb_prop in Hfree as [Hokb Hkb].
  pose proof (lv_okb_ok a Hokb) as Hok. apply Nat.ltb_lt in Hkb.
  set (XP := match cell8 (s_rgs S) (laddc (rget (s_regs S) (rkz r)) 16) with Some l => l | None => lc0 end) in *.
  set (Bl := rget (s_regs S) LVB_KEY) in *. set (Fl := rget (s_regs S) LVF_KEY) in *.
  pose proof (sden_0 _ _ _ _ (dn_sden _ _ _ _ _ _ _ _ _ Hd)) as (_ & _ & _ & _ & _ & _ & HF0 & _).
  apply andb_prop in CB as [CB1 CB2]. apply Z.eqb_eq in CB1, CB2.
  pose proof (irange_sound E (s_facts S) Bl HF0) as RB. fold (uE E Bl) in RB. rewrite CB1, CB2 in RB.
  assert (HB : uE E Bl = 0) by (clear - RB; lia).
  destruct (lv_put_rest a k Bl XP Fl lc0 lc0 lc0) as (R1 & R2 & R3 & R4 & R5 & R6 & _). cbv zeta in R1, R2, R3, R4, R5, R6.
  apply (lv_write_node S M a (lv_put a k Bl XP Fl lc0 lc0 lc0) mem0 E ms model T Hd HHA R1 R2 R3 R4 R5 R6); [| |exact Hk].
  - exact (lv_put_live_in a k Bl XP Fl lc0 lc0 lc0).
  - exact (lv_inv_put0 E a mem0 k Bl XP Fl lc0 lc0 lc0 Hok Hkb HB).
Qed.

#[using="Type"] Theorem nlvdrop_node : forall k S M a S' M' a', apost_lvdrop k S M a = Some (S', M', a') ->
  forall mem0 E ms model T, DEN ASEGS LIMIT model0 mem0 E S M ms model -> awf (s_next S) a = true -> HA E M a mem0 ->
  (forall E' mem0' ms' model', agree (s_next S) E E' -> frz_same E M mem0 mem0' -> DEN ASEGS LIMIT model0 mem0' E' S' M' ms' model' ->
     HA E' M' a' mem0' -> realizes_cfg ASEGS cfg (mkCfg ms' model') T) ->
  realizes_cfg ASEGS cfg (mkCfg ms model) T.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros k S M a S' M' a' H mem0 E ms model T Hd Haw HHA Hk. unfold apost_lvdrop in H.
  apply obool_some in H as (Hc & H). injection H as <- <- <-.
  apply andb_prop in Hc as [Hc Hkb]. apply andb_prop in Hc as [_ Hokb].
  pose proof (lv_okb_ok a Hokb) as Hok. apply Nat.ltb_lt in Hkb.
  destruct (lv_put_rest a k lc0 lc0 lc0 lc0 lc0 lc0) as (R1 & R2 & R3 & R4 & R5 & R6 & _). cbv zeta in R1, R2, R3, R4, R5, R6.
  apply (lv_write_node S M a (lv_put a k lc0 lc0 lc0 lc0 lc0 lc0) mem0 E ms model T Hd HHA R1 R2 R3 R4 R5 R6); [| |exact Hk].
  - exact (lv_put_live_in a k lc0 lc0 lc0 lc0 lc0 lc0).
  - exact (lv_inv_put0 E a mem0 k lc0 lc0 lc0 lc0 lc0 lc0 Hok Hkb eq_refl).
Qed.

#[using="Type"] Theorem nlvclear_node : forall S M a S' M' a', apost_lvclear S M a = Some (S', M', a') ->
  forall mem0 E ms model T, DEN ASEGS LIMIT model0 mem0 E S M ms model -> awf (s_next S) a = true -> HA E M a mem0 ->
  (forall E' mem0' ms' model', agree (s_next S) E E' -> frz_same E M mem0 mem0' -> DEN ASEGS LIMIT model0 mem0' E' S' M' ms' model' ->
     HA E' M' a' mem0' -> realizes_cfg ASEGS cfg (mkCfg ms' model') T) ->
  realizes_cfg ASEGS cfg (mkCfg ms model) T.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros S M a S' M' a' H mem0 E ms model T Hd Haw HHA Hk. unfold apost_lvclear in H.
  apply obool_some in H as (_ & H). injection H as <- <- <-.
  destruct (lv_clear_rest a) as (R1 & R2 & R3 & R4 & R5 & R6 & _). cbv zeta in R1, R2, R3, R4, R5, R6.
  apply (lv_write_node S M a (lv_clear a) mem0 E ms model T Hd HHA R1 R2 R3 R4 R5 R6); [| |exact Hk].
  - intros p Hp. left. exact (lv_clear_live_in a p Hp).
  - exact (lv_inv_clear E a mem0).
Qed.
End LvNil.
End AcLvNil.


Module AcLvStash.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.fast_float.from_chars.images Require Import Asan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec ShapeSet RealizesCfg AsanAcct FxLin FxCore FxSound FxMem FxFacts FxStep FxSubst FxEnt FxDrv.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require Import FxBacking FxChDen FxChLib FxChMain.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require Import AXG_put AXG_put3 AXG_np AXG_nf1 AXG_npf.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcPri.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcDepDen.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcPriHA.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcAst.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcHA.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcHA AcPri.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcPriSepOk.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcPriSepOk.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChAdd.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcMALp AcMALlib AcNPop.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcFam2.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcConvA.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcDenW AcPriStep AcUnwApp.
Import OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcPri.AcDepSep OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcDepDen OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcPriHA.AcPriGrant OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcAst OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcHA.AcLv OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcHA OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcPri OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcPriSepOk.AcPriSep OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcPriSepOk OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChAdd.AcAddOwn OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcMALp OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcMALlib OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcNPop OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcFam2.AcExt OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcConvA.AcPriDen OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcDenW OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcPriStep OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcUnwApp.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcFam2Ok.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcFam2Ok.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcFam2Ok.
Import OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcFam2Ok.AcFrameLive OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcFam2Ok.AcGiveX OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcFam2Ok.AcExtN.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcFam3.
Import OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcFam3.AcLvN OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcFam3Ok.AcLvLib.
Import ListNotations.
Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma sort3_in : forall a b c j, In j (sort3 a b c) -> j = a \/ j = b \/ j = c.
Proof. intros a b c j H. unfold sort3 in H. cbv zeta in H. cbn [In] in H. lia. Qed.

(* [comment removed for export] *)
Lemma hdr_read_cont : forall ct f n c, hdr_read ct = Some (f, n, c) -> ct = hdr_cont f n c.
Proof.
  intros ct f n c H. unfold hdr_read in H.
  destruct (tget (okey 1) ct) as [[|f0 j0]|]; try discriminate. destruct j0; try discriminate.
  destruct (tget (okey 4) ct) as [[|n0 j1]|]; try discriminate. destruct j1; try discriminate.
  destruct (tget (okey 8) ct) as [[|c0 j2]|]; try discriminate. destruct j2; try discriminate.
  destruct (tree_eqb bval_eqb ct (hdr_cont f0 n0 c0)) eqn:Ht; [|discriminate]. injection H as <- <- <-.
  exact (tree_eqb_eq bval_eqb bval_eqb_eq _ _ Ht).
Qed.
Lemma hdr_cont_get : forall f n c i v, nth_error (lv_hdr f n c) i = Some v -> tget (okey (Z.of_nat i)) (hdr_cont f n c) = Some v.
Proof.
  intros f n c i v H. unfold hdr_cont. rewrite put_bytes_spec by lia.
  assert (Hi : (i < 16)%nat) by (rewrite <- (lv_hdr_len f n c); apply nth_error_Some; rewrite H; discriminate).
  unfold okey. rewrite Z2Pos.id by lia. rewrite lv_hdr_len.
  replace (Z.leb 0 (Z.of_nat i + 1 - 1) && Z.ltb (Z.of_nat i + 1 - 1) (0 + Z.of_nat 16))%bool with true
    by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
  replace (Z.to_nat (Z.of_nat i + 1 - 1 - 0)) with i by lia. exact H.
Qed.

Lemma uE_lscale_s : forall E k x, 0 <= k * uE E x < two64 -> uE E (lscale k x) = k * uE E x.
Proof. intros E k x H. unfold uE in *. rewrite lden_lscale. apply u_small64. exact H. Qed.
Lemma uE_lsub_m : forall E a b, uE E (lsub a b) = (uE E a - uE E b) mod two64.
Proof. intros E a b. unfold uE. rewrite lden_lsub, bv_sub_unsigned. unfold bv_wrap, bv_modulus. reflexivity. Qed.
(* [comment removed for export] *)
Lemma e_rngs_drop : forall E a i q, In q (e_rngs E (ext_drop a i)) -> exists j, j <> i /\ nth_error (e_rngs E a) j = Some q.
Proof.
  intros E a i q H. apply In_nth_error in H as (t & Ht).
  assert (Ed : e_rngs E (ext_drop a i) = drop_nth i (e_rngs E a)).
  { unfold e_rngs, a_ext, ext_drop. cbn [a_rgs]. rewrite !map_drop_nth. reflexivity. }
  rewrite Ed, nth_error_drop_nth in Ht. exists (if Nat.ltb t i then t else Datatypes.S t). split; [|exact Ht].
  destruct (Nat.ltb t i) eqn:El; [apply Nat.ltb_lt in El | apply Nat.ltb_ge in El]; lia.
Qed.

Lemma sort3_has : forall a b c, In a (sort3 a b c) /\ In b (sort3 a b c) /\ In c (sort3 a b c).
Proof. intros a b c. unfold sort3. cbv zeta. cbn [In]. lia. Qed.
Lemma rd1_restrict_ms : forall (Hh : word -> bool) ms x b, 2^33 <= x < 2^64 ->
  rd1 ASEGS (ms_mem (restrict Hh ms)) (Z_to_bv 64 x) = Some b -> ms_mem ms (Z_to_bv 64 x) = Some b.
Proof.
  intros Hh ms x b Hx H.
  assert (Hrom : seg_rom ASEGS (Z_to_bv 64 x) = None).
  { apply (seg_rom_above ASEGS (2^33)); [vm_compute; reflexivity|]. rewrite u_small64 by (unfold two64; lia). lia. }
  unfold rd1 in H. cbn [restrict ms_mem] in H. unfold mrestrict in H. destruct (Hh (Z_to_bv 64 x)); [rewrite Hrom in H; discriminate|].
  destruct (ms_mem ms (Z_to_bv 64 x)); [exact H | rewrite Hrom in H; discriminate].
Qed.

Section Stash.
Variable cfg : SpuriousCfg.
Variable LIMIT : Z.
Variable model0 : Model.

#[using="Type"] Theorem nstash_node : forall k i h u z S M a S' M' a', apost_stash k i h u z S M a = Some (S', M', a') ->
  forall mem0 E ms model T, DEN ASEGS LIMIT model0 mem0 E S M ms model -> awf (s_next S) a = true -> HA E M a mem0 ->
  (forall E' mem0' ms' model', agree (s_next S) E E' -> frz_same E M mem0 mem0' -> DEN ASEGS LIMIT model0 mem0' E' S' M' ms' model' ->
     HA E' M' a' mem0' -> realizes_cfg ASEGS cfg (mkCfg ms' model') T) ->
  realizes_cfg ASEGS cfg (mkCfg ms model) T.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros k i h u z S M a S' M' a' H mem0 E ms model T Hd Haw HHA Hk. unfold apost_stash in H.
  apply obind_some in H as (e & He & H). cbv beta in H.
  apply obind_some in H as (RH & HRH & H). cbv beta in H.
  apply obind_some in H as (RU & HRU & H). cbv beta in H.
  apply obind_some in H as (RS & HRS & H). cbv beta in H.
  apply obind_some in H as (fnc & Hhdr & H). destruct fnc as [[F N] C]. cbv beta iota zeta in H.
  apply obool_some in H as (Hc & H). injection H as <- <- <-.
  set (hb := rg_base RH) in *. set (XP := laddc hb 16) in *. set (N8 := rg_size RS) in *. set (Bl := rget (s_regs S) LVB_KEY) in *.
  change (remove_nth _ (remove_nth _ (remove_nth _ (s_rgs S)))) with (remove_ixs (sort3 h u z) (s_rgs S)) in Hk.
  set (ix := sort3 h u z) in *.
  apply andb_prop in Hc as [Hc _]. apply andb_prop in Hc as [Hc CBl].
  apply andb_prop in Hc as [Hc Cn8hi]. apply andb_prop in Hc as [Hc Cn8lo]. apply andb_prop in Hc as [Hc Cfn]. apply andb_prop in Hc as [Hc Cmod].
  apply andb_prop in Hc as [Hc Cins]. apply andb_prop in Hc as [Hc CeS]. apply andb_prop in Hc as [Hc CeU]. apply andb_prop in Hc as [Hc CeH].
  apply andb_prop in Hc as [Hc _]. apply andb_prop in Hc as [Hc CszU]. apply andb_prop in Hc as [Hc CbU]. apply andb_prop in Hc as [Hc CszH].
  apply andb_prop in Hc as [Hc Cfree]. apply andb_prop in Hc as [Hhdr0 Cinc].
  unfold givex_hdr_ok in Hhdr0. apply andb_prop in Hhdr0 as [Hhdr0 Hown_eq]. apply andb_prop in Hhdr0 as [Hon Hlen]. apply Nat.eqb_eq in Hlen.
  unfold lv_free_b in Cfree. apply andb_prop in Cfree as [Cfree _]. apply andb_prop in Cfree as [Cokb Ckb].
  pose proof (lv_okb_ok a Cokb) as Hok. apply Nat.ltb_lt in Ckb.
  apply lin_eqb_eq in CszH, CbU, CszU. apply Z.leb_le in Cn8lo, Cn8hi.
  pose proof (hdr_read_cont _ _ _ _ Hhdr) as HcH.
  pose proof (HHA Hon) as HA0.
  assert (Hne : a_pri a <> []) by (intros Hn; rewrite Hn in Hlen; discriminate).
  pose proof (ha_pri _ _ _ _ HA0 Hne) as HP0. pose proof (po_inv _ _ _ _ HP0) as HI. unfold INV_A in HI. set (pz := pden E a) in *.
  pose proof (tg_pg_disj LIMIT model0 mem0 E S M ms model a mem0 Hd HP0) as Hdisj. fold pz in Hdisj.
  pose proof (az_geo pz mem0 HI) as G.
  set (Hh := Hof E M model) in *. set (mr := ms_mem (restrict Hh ms)) in *.
  pose proof (sden_0 _ _ _ _ (dn_sden _ _ _ _ _ _ _ _ _ Hd)) as (_ & _ & _ & _ & HRG & _ & HF0 & _). fold Hh in HRG. fold mr in HRG.
  rewrite Forall_forall in HRG.
  assert (Hein : In e (a_ext a)) by exact (nth_error_In _ _ He).
  assert (Call : forall j, In j ix -> match nth_error (s_rgs S) j with Some R => ext_in (s_facts S) a R | None => false end = true).
  { intros j Hj. destruct (sort3_in _ _ _ _ Hj) as [ -> | [ -> | -> ] ]; [rewrite HRH | rewrite HRU | rewrite HRS];
      unfold ext_in; rewrite existsb_l_eq; apply existsb_exists; exists e; (split; [exact Hein | assumption]). }
  (* [comment removed for export] *)
  assert (Hlive : forall j R, In j ix -> nth_error (s_rgs S) j = Some R -> forall x, uE E (rg_base R) <= x < uE E (rg_base R) + rsz E R ->
            (live_u pz x \/ live_s pz x) /\ pri_foot_z pz x /\ 0 <= x < 2^47).
  { intros j R Hj HR x Hx. pose proof (Call j Hj) as Ci. rewrite HR in Ci.
    pose proof (HRG R (nth_error_In _ _ HR)) as (Hz0 & _).
    destruct (ext_in_route E (s_facts S) HF0 a mem0 HI (po_ext _ _ _ _ HP0) R Hz0 Ci) as (p & Hp & Hsem & Hside). fold pz in Hsem.
    destruct Hside as [[U1 U2]|(c & Hcin & (V1 & V2 & V3))].
    - destruct Hsem as ((c & Hcin & X1 & X2 & X3) & XB & XG). pose proof (in_cls_rng c Hcin) as Hcr.
      destruct (cls_jb pz mem0 HI c Hcin) as (K0 & K1 & K2 & _).
      assert (Hj1 : 1 <= z_j pz c).
      { destruct (Z_le_gt_dec 1 (z_j pz c)) as [Y|Y]; [exact Y|]. exfalso. assert (z_j pz c = 0) by (clear - K0 Y; lia).
        rewrite H in X2. clear - X1 X2 U1 U2 Hx. lia. }
      assert (Zc : z_z pz c = 262144).
      { destruct (iz_cls _ _ HI c Hcin) as [(J0 & _)|(_ & Z1 & _)]; [clear - J0 Hj1; lia | exact Z1]. }
      split; [left; exists c; split; [exact Hcin|]; split; [clear - X1 X2 U1 U2 Hx; lia|]; split|split].
      + intros Hq Hb. destruct (XB Hq) as [Y|Y]; clear - Y Hb U1 U2 Hx; lia.
      + intros Hg Hb. destruct (XG Hg) as [Y|Y]; clear - Y Hb U1 U2 Hx; lia.
      + right. right. right. exists c. split; [exact Hcin|]. left. rewrite Zc. clear - X1 X2 U1 U2 Hx K1. lia.
      + clear - X1 X2 U1 U2 Hx K1 G Hcr. lia.
    - pose proof (in_cls_rng c Hcin) as Hcr. fold pz in V1, V2, V3.
      split; [right; exists c; split; [exact Hcin | clear - V1 V2 Hx; lia]|]. split.
      + right. right. right. exists c. split; [exact Hcin|]. right. right. left. clear - V1 V2 V3 Hx. lia.
      + clear - V1 V2 V3 Hx G Hcr. lia. }
  (* [comment removed for export] *)
  set (Db := in_ix E (s_rgs S) ix). set (hyb := hyb_p Db (ms_mem ms) mem0).
  assert (Hhyb_in : forall x, 0 <= x < 2^64 -> Db x = true -> hyb (wa x) = ms_mem ms (wa x)).
  { intros x Hx Hb. unfold hyb, hyb_p. rewrite u_wa_small by exact Hx. rewrite Hb. reflexivity. }
  assert (Hhyb_out : forall x, 0 <= x < 2^64 -> Db x = false -> hyb (wa x) = mem0 (wa x)).
  { intros x Hx Hb. unfold hyb, hyb_p. rewrite u_wa_small by exact Hx. rewrite Hb. reflexivity. }
  assert (Hout_nd : forall w : word, outside E (s_rgs S) w -> Db (bv_unsigned w) = false).
  { intros w Hout. destruct (Db (bv_unsigned w)) eqn:Eb; [|reflexivity]. exfalso. apply in_ix_spec in Eb as (j & R & Hj & HR & Hx).
    unfold outside in Hout. rewrite Forall_forall in Hout. specialize (Hout R (nth_error_In _ _ HR)). unfold uE in Hx. clear - Hout Hx. lia. }
  assert (HD1 : DEN ASEGS LIMIT model0 hyb E S M ms model).
  { apply (den_snap ASEGS LIMIT model0 mem0 hyb E S M ms model Hd).
    - intros w (q & Hq & Hqw). destruct (dn_frz _ _ _ _ _ _ _ _ _ Hd q Hq w Hqw) as (_ & Hout & _).
      unfold hyb, hyb_p. rewrite (Hout_nd _ Hout). reflexivity.
    - intros w _ Hout. unfold hyb, hyb_p. rewrite (Hout_nd _ Hout). reflexivity. }
  assert (HD2 : DEN ASEGS LIMIT model0 hyb E (with_rgs S (remove_ixs ix (s_rgs S))) M ms model).
  { apply (den_drop_ixs LIMIT model0 hyb E M ms model ix S Cinc HD1). intros j Hj.
    pose proof (Call j Hj) as Ci. destruct (nth_error (s_rgs S) j) as [R|] eqn:HR; [|discriminate]. exists R. split; [reflexivity|].
    intros w Hw. destruct (Hlive j R Hj HR w Hw) as (_ & Hf & Hr). split.
    - exact (po_own _ _ _ _ HP0 w ltac:(clear - Hr; lia) Hf).
    - change (Z_to_bv 64 w) with (wa w). symmetry. apply Hhyb_in; [clear - Hr; lia|]. apply in_ix_spec. exists j, R. split; [exact Hj|]. split; [exact HR | exact Hw]. }
  (* [comment removed for export] *)
  destruct (sort3_has h u z) as (HinH & HinU & _). fold ix in HinH, HinU.
  pose proof (irange_sound E (s_facts S) N8 HF0) as Rn8. fold (uE E N8) in Rn8.
  assert (Hn8 : 1 <= uE E N8 <= 8192) by (clear - Rn8 Cn8lo Cn8hi; lia).
  pose proof (po_ext _ _ _ _ HP0 e Hein) as Hee. fold pz in Hee.
  assert (Hb48 : uE E (fst e) + uE E (snd e) < 2^48).
  { destruct Hee as ((c & Hcin & X1 & X2 & _) & _). pose proof (in_cls_rng c Hcin) as Hcr.
    destruct (cls_jb pz mem0 HI c Hcin) as (_ & K1 & _). clear - X2 K1 G Hcr. lia. }
  assert (Hlo : 17594333495296 <= uE E (fst e)).
  { destruct Hee as ((c & Hcin & X1 & _) & _). pose proof (in_cls_rng c Hcin) as Hcr. clear - X1 G Hcr. lia. }
  assert (Hsz : uE E (laddc (lscale 8 N8) 16) = 8 * uE E N8 + 16).
  { rewrite uE_laddc_z; rewrite uE_lscale_s; unfold two64; clear - Hn8; lia. }
  destruct (inside_lin_sound E (s_facts S) HF0 hb (laddc (lscale 8 N8) 16) (fst e) (snd e) Cins Hb48) as [I1 I2]. rewrite Hsz in I2.
  assert (HXP : uE E XP = uE E hb + 16) by (unfold XP; apply uE_laddc_z; pose proof (uE_rng E hb) as Hr0; unfold two64 in *; clear - I2 Hb48 Hr0 Hn8; lia).
  pose proof (fact_implied_ok E _ _ HF0 Cmod) as Hmod. cbn [fact_ok] in Hmod. change (2^3) with 8 in Hmod. fold (uE E hb) in Hmod.
  assert (HszH : rsz E RH = 16) by (unfold rsz; rewrite CszH; apply (uE_lc E 16); lia).
  assert (HszU : rsz E RU = 8 * uE E N8) by (unfold rsz; rewrite CszU; apply uE_lscale_s; unfold two64; clear - Hn8; lia).
  assert (HbU : uE E (rg_base RU) = uE E hb + 16) by (rewrite CbU; exact HXP).
  (* [comment removed for export] *)
  assert (HDbH : forall x, uE E hb <= x < uE E hb + 16 -> Db x = true).
  { intros x Hx. apply in_ix_spec. exists h, RH. split; [exact HinH|]. split; [exact HRH|]. rewrite HszH. exact Hx. }
  assert (HDbU : forall x, uE E hb + 16 <= x < uE E hb + 16 + 8 * uE E N8 -> Db x = true).
  { intros x Hx. apply in_ix_spec. exists u, RU. split; [exact HinU|]. split; [exact HRU|]. rewrite HbU, HszU. exact Hx. }
  assert (Hmapped : forall R x, In R (s_rgs S) -> uE E (rg_base R) <= x < uE E (rg_base R) + rsz E R -> 2^33 <= x < 2^64 -> ms_mem ms (wa x) <> None).
  { intros R x HR Hx Hx33. pose proof (HRG R HR) as (Hz0 & Hz1 & Hpt & _).
    specialize (Hpt (x - uE E (rg_base R)) ltac:(clear - Hx; lia)). unfold uE in Hpt.
    replace (bv_unsigned (lden E (rg_base R)) + (x - bv_unsigned (lden E (rg_base R)))) with x in Hpt by ring.
    assert (Hrom : seg_rom ASEGS (Z_to_bv 64 x) = None).
    { apply (seg_rom_above ASEGS (2^33)); [vm_compute; reflexivity|]. rewrite u_small64 by (unfold two64; clear - Hx33; lia). clear - Hx33. lia. }
    assert (Hrd : rd1 ASEGS mr (Z_to_bv 64 x) <> None).
    { destruct (rg_kind R); first [exact (proj1 Hpt) | exact (proj1 (proj1 Hpt)) | exact Hpt | exfalso; destruct Hpt as [_ X]; exact (X Hrom)]. }
    destruct (rd1 ASEGS mr (Z_to_bv 64 x)) as [b|] eqn:Er; [|exfalso; apply Hrd; reflexivity].
    unfold wa. rewrite (rd1_restrict_ms Hh ms x b Hx33 Er). discriminate. }
  change (remove_ixs ix (s_rgs S)) with (remove_ixs ix (s_rgs S)) in Hk.
  apply (Hk E hyb ms model); [apply agree_refl | | exact HD2 |].
  - intros q Hq w Hqw. destruct (dn_frz _ _ _ _ _ _ _ _ _ Hd q Hq w Hqw) as (_ & Hout & _).
    unfold hyb, hyb_p. rewrite (Hout_nd _ Hout). reflexivity.
  - intros _.
    (* [comment removed for export] *)
    assert (HS : HA_on E M a hyb).
    { apply (HA_on_snap E M a mem0 hyb HA0).
      - intros x Hx Hdw. apply (Hhyb_out x Hx). destruct (Db x) eqn:Eb; [|reflexivity]. exfalso.
        apply in_ix_spec in Eb as (j & R & Hj & HR & Hxr). destruct (Hlive j R Hj HR x Hxr) as (_ & Hf & _).
        exact (pri_not_downed LIMIT model0 mem0 E S M ms model a mem0 Hd HA0 Hne x Hf Hdw).
      - intros _. unfold INV_A. fold pz. apply (INV_Az_frame_live pz mem0 hyb HI Hdisj).
        + intros x Hf Hnu Hns. pose proof (pri_foot_rng E a mem0 HI x Hf) as Rx. apply (Hhyb_out x ltac:(clear - Rx; lia)).
          destruct (Db x) eqn:Eb; [|reflexivity]. exfalso. apply in_ix_spec in Eb as (j & R & Hj & HR & Hxr).
          destruct (Hlive j R Hj HR x Hxr) as ([L|L] & _); [exact (Hnu L) | exact (Hns L)].
        + intros x Hs. assert (Hx47 : 2199291686912 <= x < 2^47).
          { destruct Hs as (c & Hcin & L1). pose proof (in_cls_rng c Hcin) as Hcr. destruct (cls_jb pz mem0 HI c Hcin) as (K0 & _ & K2 & _). clear - L1 G Hcr K0 K2. lia. }
          destruct (Db x) eqn:Eb.
          * rewrite (Hhyb_in x ltac:(clear - Hx47; lia) Eb). apply in_ix_spec in Eb as (j & R & Hj & HR & Hxr).
            exact (Hmapped R x (nth_error_In _ _ HR) Hxr ltac:(clear - Hx47; lia)).
          * rewrite (Hhyb_out x ltac:(clear - Hx47; lia) Eb). destruct Hs as (c & Hcin & L1).
            destruct (iz_cls _ _ HI c Hcin) as [(J0 & _)|(_ & _ & _ & _ & HPo)]; [rewrite J0 in L1; clear - L1; lia|].
            destruct (cls_jb pz mem0 HI c Hcin) as (_ & _ & K2 & _).
            apply (pc_shm _ _ _ _ _ _ HPo x). unfold SHX. clear - L1 K2. lia.
      - intros _ k0 x Hkk HB Hxr. pose proof (po_lv _ _ _ _ HP0) as Hlv. destruct (proj1 Hlv k0 Hkk) as [_ L]. destruct (L HB) as (L3 & _).
        pose proof (ext_sem_foot _ mem0 _ _ HI L3 x Hxr) as Hf. pose proof (pri_foot_rng E a mem0 HI x Hf) as Rx.
        apply (Hhyb_out x ltac:(clear - Rx; lia)). destruct (Db x) eqn:Eb; [|reflexivity]. exfalso.
        apply in_ix_spec in Eb as (j & R & Hj & HR & Hxi). pose proof (Call j Hj) as Ci. rewrite HR in Ci.
        pose proof (HRG R (nth_error_In _ _ HR)) as (Hz0 & _).
        destruct (ext_in_route E (s_facts S) HF0 a mem0 HI (po_ext _ _ _ _ HP0) R Hz0 Ci) as (p & Hp & Hsem & Hside).
        destruct Hside as [[U1 U2]|(c & Hcin & (V1 & V2 & V3))].
        + apply (lv_apart_entry E a mem0 p k0 Hlv Hp Hkk HB x). split; [clear - U1 U2 Hxi; lia | exact Hxr].
        + destruct L3 as ((c' & Hcin' & X1 & X2 & _) & _). fold pz in X1, X2, V1, V2, V3.
          pose proof (in_cls_rng c Hcin) as Hcr. pose proof (in_cls_rng c' Hcin') as Hcr'.
          destruct (cls_jb pz mem0 HI c' Hcin') as (_ & K1 & _). clear - V1 V2 V3 X1 X2 K1 Hxi Hxr G Hcr Hcr'. lia. }
    (* [comment removed for export] *)
    set (a1 := ext_drop a i).
    assert (HS1 : HA_on E M a1 hyb).
    { apply (HA_on_ext E M a a1 hyb HS); try reflexivity.
      - intros _ p Hp. exact (po_ext _ _ _ _ (ha_pri _ _ _ _ HS Hne) p (In_ext_drop a i p Hp)).
      - intros _ Hlv. exact (lv_inv_ext_drop E a hyb i Hlv). }
    (* [comment removed for export] *)
    assert (Hok1 : lv_ok a1) by exact Hok.
    destruct (lv_put_rest a1 k Bl XP F N C N8) as (R1 & R2 & R3 & R4 & R5 & R6 & _). cbv zeta in R1, R2, R3, R4, R5, R6.
    apply (HA_on_lv E M a1 (lv_put a1 k Bl XP F N C N8) hyb HS1 R1 R2 R3 R4 R5 R6); [exact (lv_put_live_in a1 k Bl XP F N C N8)|].
    intros _ Hlv1. pose proof (po_lv _ _ _ _ (ha_pri _ _ _ _ HS Hne)) as Hlv0.
    destruct (lv_put_self a1 k Bl XP F N C N8 Hok1 Ckb) as (SB & SXP & SF & SN & SC & SN8). cbv zeta in SB, SXP, SF, SN, SC, SN8.
    assert (HB1 : uE E Bl = 1).
    { apply andb_prop in CBl as [CB1 CB2]. apply Z.eqb_eq in CB1, CB2.
      pose proof (irange_sound E (s_facts S) Bl HF0) as RB. fold (uE E Bl) in RB. rewrite CB1, CB2 in RB. clear - RB. lia. }
    apply (lv_inv_put E a1 hyb k Bl XP F N C N8 Hok1 Ckb Hlv1).
    + (* [comment removed for export] *)
      unfold lv_sem, lv_lo, lv_sz. rewrite SB, SXP, SF, SN, SC, SN8, HB1, HXP. split; [lia|]. intros _.
      replace (uE E hb + 16 - 16) with (uE E hb) by ring.
      change (pden E a1) with pz. split; [|split; [|split; [|split]]].
      * apply (ext_sem_sub pz _ _ _ _ Hee I1); [clear - I2; lia | exact Hmod].
      * pose proof (fact_implied_ok E _ _ HF0 Cfn) as Hfn. cbn [fact_ok] in Hfn. fold (uE E (lsub (lscale 8 N8) N)) in Hfn.
        rewrite uE_lsub_m, uE_lscale_s in Hfn by (unfold two64; clear - Hn8; lia).
        pose proof (uE_rng E N) as RN. unfold two64 in *.
        destruct (mod64_cases (8 * uE E N8 - uE E N) ltac:(unfold two64; clear - Hn8 RN; lia)) as [[Em _]|[[Em _]|[Em Ex]]]; unfold two64 in *.
        -- rewrite Em in Hfn. clear - Hfn Hn8. lia.
        -- rewrite Em in Hfn. exfalso. clear - Hfn Hn8 RN. lia.
        -- exfalso. clear - Ex Hn8 RN. lia.
      * intros t v Hv. assert (Ht : (t < 16)%nat) by (rewrite <- (lv_hdr_len F N C); apply nth_error_Some; rewrite Hv; discriminate).
        assert (Hx33 : 2^33 <= uE E hb + Z.of_nat t < 2^64) by (clear - I1 I2 Hlo Hb48 Ht Hn8; lia).
        rewrite (Hhyb_in (uE E hb + Z.of_nat t) ltac:(clear - Hx33; lia) (HDbH (uE E hb + Z.of_nat t) ltac:(clear - Ht; lia))).
        pose proof (HRG RH (nth_error_In _ _ HRH)) as (_ & _ & _ & Hct).
        pose proof (hdr_cont_get F N C t v Hv) as Hg. rewrite <- HcH in Hg. destruct (Hct _ _ Hg) as [_ Hrd].
        unfold okey in Hrd. rewrite Z2Pos.id in Hrd by lia. replace (Z.of_nat t + 1 - 1) with (Z.of_nat t) in Hrd by ring.
        exact (rd1_restrict_ms Hh ms _ _ Hx33 Hrd).
      * intros x Hx. assert (Hx33 : 2^33 <= x < 2^64) by (clear - I1 I2 Hlo Hb48 Hx Hn8; lia).
        destruct (Z_lt_le_dec x (uE E hb + 16)) as [Hl|Hl].
        -- rewrite (Hhyb_in x ltac:(clear - Hx33; lia) (HDbH x ltac:(clear - Hx Hl; lia))).
           apply (Hmapped RH x (nth_error_In _ _ HRH)); [rewrite HszH; fold hb; clear - Hx Hl; lia | exact Hx33].
        -- rewrite (Hhyb_in x ltac:(clear - Hx33; lia) (HDbU x ltac:(clear - Hx Hl; lia))).
           apply (Hmapped RU x (nth_error_In _ _ HRU)); [rewrite HbU, HszU; clear - Hx Hl; lia | exact Hx33].
      * exact Hn8.
    + (* [comment removed for export] *)
      intros q Hq x [X1 X2]. unfold in_rg, lv_rng, lv_lo, lv_sz in X1. cbn [fst snd] in X1. rewrite SB, SXP, SN8, HB1, HXP in X1.
      assert (Xe : in_rg (uE E (fst e), uE E (snd e)) x) by (unfold in_rg; cbn [fst snd]; clear - X1 I1 I2; lia).
      destruct Hlv0 as [_ HD0].
      assert (Hie : nth_error (x_rngs E a) i = Some (uE E (fst e), uE E (snd e))).
      { unfold x_rngs. rewrite nth_error_app1 by (unfold e_rngs; rewrite length_map; apply nth_error_Some; rewrite He; discriminate).
        unfold e_rngs. rewrite nth_error_map, He. reflexivity. }
      destruct Hq as [Hq|(k' & Hk' & Hnk & ->)].
      * destruct (e_rngs_drop E a i q Hq) as (j & Hji & Hj).
        apply (HD0 i j _ q (fun X => Hji (eq_sym X)) Hie ltac:(unfold x_rngs; rewrite nth_error_app1 by (apply nth_error_Some; rewrite Hj; discriminate); exact Hj) x (conj Xe X2)).
      * assert (Hlen2 : (i < List.length (e_rngs E a))%nat) by (unfold e_rngs; rewrite length_map; apply nth_error_Some; rewrite He; discriminate).
        assert (Hjk : nth_error (x_rngs E a) (List.length (e_rngs E a) + k')%nat = Some (lv_rng E a k')).
        { unfold x_rngs. rewrite nth_error_app2 by lia. replace (List.length (e_rngs E a) + k' - List.length (e_rngs E a))%nat with k' by lia.
          rewrite lv_rngs_nth, (proj2 (Nat.ltb_lt k' LV_N) Hk'). reflexivity. }
        exact (HD0 i (List.length (e_rngs E a) + k')%nat _ (lv_rng E a k') ltac:(clear - Hlen2; lia) Hie Hjk x (conj Xe X2)).
Qed.
End Stash.
End AcLvStash.


Module AcLvTake.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.fast_float.from_chars.images Require Import Asan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require PropExec ShapeSet RealizesCfg AsanAcct FxLin FxCore FxSound FxMem FxFacts FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSubst FxEnt FxDrv.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.PropExec OSSVerify.Proofs.fast_float.from_chars.lib.Common.ShapeSet OSSVerify.Proofs.fast_float.from_chars.lib.Common.RealizesCfg OSSVerify.Proofs.fast_float.from_chars.lib.Common.AsanAcct OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxMem OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEnt OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxDrv.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require Import FxBacking FxChDen FxChLib FxChEnt FxChSep FxChMain.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require Import AXG_put AXG_put3 AXG_np AXG_nf1 AXG_npf.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcPri.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcDepDen.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcPriHA.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcCarve.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChLib.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcAst.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcHA.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcHA AcPri.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcPriSepOk.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcPriSepOk.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChAdd.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcMALp AcMALlib AcNPop.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcFam2.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcConvA.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcDenW AcPriStep AcUnwApp.
Import OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcPri.AcDepSep OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcDepDen OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcPriHA.AcPriGrant OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcCarve OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChLib.AcFacts OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcAst OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcHA.AcLv OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcHA OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcPri OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcPriSepOk.AcPriSep OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcPriSepOk OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChAdd.AcAddOwn OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcMALp OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcMALlib OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcNPop OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcFam2.AcExt OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcConvA.AcPriDen OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcDenW OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcPriStep OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcUnwApp.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcFam2Ok.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcFam2Ok.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcFam2Ok.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcNPopGLib.
Import OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcFam2Ok.AcFrameLive OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcFam2Ok.AcGiveX OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcFam2Ok.AcExtN OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcNPopGLib.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcFam3.
Import OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcFam3.AcLvN OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcFam3Ok.AcLvLib OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcFam3Ok.AcLvStash.
Import ListNotations.
Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Lemma ext_in1_geo : forall E fs, Forall (fact_ok E) fs -> forall R p, ext_in1 fs R p = true -> uE E (fst p) + uE E (snd p) < 2^48 ->
  (uE E (fst p) <= uE E (rg_base R) /\ uE E (rg_base R) + rsz E R <= uE E (fst p) + uE E (snd p)) \/
  (SH_OFF <= uE E (rg_base R) /\ uE E (fst p) <= 8 * (uE E (rg_base R) - SH_OFF) /\
   8 * (uE E (rg_base R) - SH_OFF) + 8 * rsz E R <= uE E (fst p) + uE E (snd p)).
Proof.
  intros E fs HF R p H1 Hb48. unfold ext_in1 in H1.
  destruct (inside_lin fs (rg_base R) (rg_size R) (fst p) (snd p)) eqn:HA.
  - left. destruct (inside_lin_sound E fs HF _ _ _ _ HA Hb48) as [L1 L2]. unfold rsz. fold (uE E (rg_size R)). split; lia.
  - right. destruct (inside_lin fs (lscale 8 (laddc (rg_base R) (- SH_OFF))) (lscale 8 (rg_size R)) (fst p) (snd p)) eqn:HB; [|discriminate].
    destruct (Z.ltb (snd (irange fs (rg_base R))) 281474976710656) eqn:H0; [|discriminate].
    apply Z.ltb_lt in H0, H1. pose proof (irange_sound E fs (rg_base R) HF) as Rb. fold (uE E (rg_base R)) in Rb.
    pose proof (irange_sound E fs (rg_size R) HF) as Rzz. fold (uE E (rg_size R)) in Rzz.
    destruct (inside_lin_sound E fs HF _ _ _ _ HB Hb48) as [L1 L2].
    pose proof (uE_rng E (rg_base R)) as B1. pose proof (uE_rng E (rg_size R)) as B3. pose proof (uE_rng E (fst p)) as B4. pose proof (uE_rng E (snd p)) as B5.
    unfold rsz. fold (uE E (rg_size R)).
    set (s := uE E (rg_base R)) in *. set (zv := uE E (rg_size R)) in *.
    assert (Hs : SH_OFF <= s).
    { destruct (Z_lt_le_dec s SH_OFF) as [Hlt|Hge]; [exfalso|exact Hge].
      rewrite uE_lscale_mod, uE_laddc_mod in L2. fold s in L2. rewrite Z.mul_mod_idemp_r in L2 by (unfold two64; lia).
      pose proof (Z.mod_pos_bound (8 * zv) two64 ltac:(unfold two64; lia)) as Bz. rewrite uE_lscale_mod in L2. fold zv in L2.
      destruct (mod64_cases (8 * (s + - SH_OFF)) ltac:(unfold SH_OFF, two64 in *; lia)) as [[N1 N2]|[[N1 N2]|[N1 N2]]]; rewrite N1 in L2;
        unfold SH_OFF, two64 in *; lia. }
    assert (EA : uE E (lscale 8 (laddc (rg_base R) (- SH_OFF))) = 8 * (s - SH_OFF)).
    { rewrite uE_lscale_mod, uE_laddc_mod. fold s. rewrite (Z.mod_small (s + - SH_OFF)) by (unfold SH_OFF, two64 in *; lia).
      rewrite Z.mod_small by (unfold SH_OFF, two64 in *; lia). lia. }
    assert (EZ : uE E (lscale 8 (rg_size R)) = 8 * zv) by (rewrite uE_lscale_mod; fold zv; apply Z.mod_small; unfold two64 in *; lia).
    rewrite EA, EZ in L2. rewrite EA in L1. split; [exact Hs|]. split; [exact L1 | exact L2].
Qed.

(* [comment removed for export] *)
Lemma hdr_cont_inv : forall f n c p v, tget p (hdr_cont f n c) = Some v ->
  exists i, (i < 16)%nat /\ Zpos p - 1 = Z.of_nat i /\ nth_error (lv_hdr f n c) i = Some v.
Proof.
  intros f n c p v H. unfold hdr_cont in H. rewrite put_bytes_spec in H by lia. rewrite lv_hdr_len in H.
  destruct (Z.leb 0 (Zpos p - 1) && Z.ltb (Zpos p - 1) (0 + Z.of_nat 16))%bool eqn:Eb; [|rewrite tget_empty in H; discriminate].
  apply andb_prop in Eb as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
  exists (Z.to_nat (Zpos p - 1 - 0)). split; [lia|]. split; [lia | exact H].
Qed.
Lemma lv_hdr_bwf : forall m f n c, lwf m f = true -> lwf m n = true -> lwf m c = true -> forall v, In v (lv_hdr f n c) -> bwf m v = true.
Proof.
  intros m f n c Hf Hn Hc v H. unfold lv_hdr in H. cbn [In] in H.
  repeat (destruct H as [<-|H]; [cbn [bwf]; first [reflexivity | exact Hf | exact Hn | exact Hc]|]). destruct H.
Qed.

Section Take.
Variable cfg : SpuriousCfg.
Variable LIMIT : Z.
Variable model0 : Model.

#[using="Type"] Theorem ntake_node : forall k S M a S' M' a', apost_take k S M a = Some (S', M', a') ->
  forall mem0 E ms model T, DEN ASEGS LIMIT model0 mem0 E S M ms model -> awf (s_next S) a = true -> HA E M a mem0 ->
  (forall E' mem0' ms' model', agree (s_next S) E E' -> frz_same E M mem0 mem0' -> DEN ASEGS LIMIT model0 mem0' E' S' M' ms' model' ->
     HA E' M' a' mem0' -> realizes_cfg ASEGS cfg (mkCfg ms' model') T) ->
  realizes_cfg ASEGS cfg (mkCfg ms model) T.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros k S M a S' M' a' H mem0 E ms model T Hd Haw HHA Hk. unfold apost_take in H. cbv zeta in H.
  apply obind_some in H as (jP & HjP & H). cbv beta in H. apply obind_some in H as (jT & HjT & H). cbv beta in H.
  apply obool_some in H as (Hc & H). injection H as <- <- <-.
  set (B := lv_B a k) in *. set (XP := lv_XP a k) in *. set (N := lv_n a k) in *. set (F := lv_f a k) in *. set (C := lv_c a k) in *. set (N8 := lv_n8 a k) in *.
  set (VQ := s_next S) in *. set (EV := (s_next S + 1)%positive) in *.
  set (P8 := lscale 8 (lvar VQ)) in *. set (U8 := lscale 8 N8) in *. set (NS := lsub U8 (lvar EV)) in *.
  apply andb_prop in Hc as [Hc Call]. apply andb_prop in Hc as [Hc CB]. apply andb_prop in Hc as [Hc Ca0]. apply andb_prop in Hc as [Hc Cpc].
  apply andb_prop in Hc as [Hc Ckb]. apply andb_prop in Hc as [Hhdr0 Cokb].
  unfold givex_hdr_ok in Hhdr0. apply andb_prop in Hhdr0 as [Hhdr0 Hown_eq]. apply andb_prop in Hhdr0 as [Hon Hlen]. apply Nat.eqb_eq in Hlen.
  pose proof (lv_okb_ok a Cokb) as Hok. apply Nat.ltb_lt in Ckb. apply lin_eqb_eq in Ca0. apply Z.eqb_eq in Cpc.
  apply andb_prop in CB as [CB1 CB2]. apply Z.eqb_eq in CB1, CB2. rewrite forallb_l_eq in Call. rewrite forallb_forall in Call.
  pose proof (HHA Hon) as HA0.
  assert (Hne : a_pri a <> []) by (intros Hn; rewrite Hn in Hlen; discriminate).
  pose proof (ha_pri _ _ _ _ HA0 Hne) as HP0. pose proof (po_inv _ _ _ _ HP0) as HI. unfold INV_A in HI. set (pz := pden E a) in *.
  pose proof (az_geo pz mem0 HI) as G.
  pose proof (sden_0 _ _ _ _ (dn_sden _ _ _ _ _ _ _ _ _ Hd)) as (_ & _ & _ & _ & HRG & _ & HF0 & _).
  rewrite Forall_forall in HRG.
  (* [comment removed for export] *)
  pose proof (po_lv _ _ _ _ HP0) as Hlv. destruct (proj1 Hlv k Ckb) as [_ L].
  pose proof (irange_sound E (s_facts S) B HF0) as RB. fold (uE E B) in RB. rewrite CB1, CB2 in RB.
  assert (HB : uE E B = 1) by (clear - RB; lia).
  destruct (L HB) as (L3 & L4 & L2 & L2m & L5). fold N8 in L5.
  unfold lv_lo, lv_sz in L3, L2, L2m. fold XP in L3, L2, L2m. fold N8 in L3, L4, L2m. fold N in L4. fold F N C in L2.
  set (xp := uE E XP) in *. set (n8 := uE E N8) in *. set (n := uE E N) in *.
  pose proof L3 as L3e.
  destruct L3 as ((c & Hcin & X1 & X2 & X3) & XBq & XGq). pose proof (in_cls_rng c Hcin) as Hcr. fold pz in X1, X2, L3e.
  destruct (cls_jb pz mem0 HI c Hcin) as (K0 & K1 & K2 & K3).
  destruct (cls_tbl c Hcin) as (Hszp & Hs8 & Hsz8 & _).
  (* [comment removed for export] *)
  set (xq := xp / 8) in *.
  assert (Exq : xp = 8 * xq).
  { pose proof (Z.div_mod xp 8 ltac:(clear; lia)) as Ed. fold xq in Ed.
    assert (Hm : xp mod 8 = 0).
    { replace xp with ((xp - 16) + 2 * 8) by ring. rewrite Z.mod_add by (clear; lia). exact X3. }
    rewrite Hm, Z.add_0_r in Ed. exact Ed. }
  set (K := z_sb pz / 8) in *.
  assert (EK : z_sb pz = 8 * K).
  { destruct G as (_ & _ & _ & _ & _ & G6 & _). pose proof (Z.div_mod (z_sb pz) 8 ltac:(clear; lia)) as Ed. fold K in Ed. rewrite G6, Z.add_0_r in Ed. exact Ed. }
  assert (Esh : z_sh pz = K + SH_OFF) by (destruct G as (_ & _ & _ & _ & _ & _ & G7 & _); unfold K, SH_OFF; exact G7).
  set (PJ := sz_tbl c / 8 * z_j pz c) in *.
  assert (EPJ : sz_tbl c * z_j pz c = 8 * PJ) by (unfold PJ; rewrite Hs8 at 1; ring).
  assert (Hgeo : K + 536870912 * c + 2 <= xq /\ xq + n8 <= K + 536870912 * c + PJ /\ 0 <= PJ <= 32768 /\ 2199291686912 <= K <= 17592186044416 - 17179869184).
  { destruct G as (_ & _ & _ & _ & _ & _ & _ & G8 & G9 & _). fold K in G8, G9. rewrite EPJ in X2, K1. clear - X1 X2 K1 K0 Exq EK L5 G8 G9 Hsz8 EPJ. unfold PJ in *. nia. }
  destruct Hgeo as (Q1 & Q2 & Q3 & Q4).
  (* [comment removed for export] *)
  destruct (find_grant_sound _ _ _ _ HjP) as (kp & Hgp). destruct (find_grant_sound _ _ _ _ HjT) as (kt & Hgt).
  assert (Hroute : forall R, In R (s_rgs S) ->
            (forall w, uE E (rg_base R) <= w < uE E (rg_base R) + rsz E R -> ~ FPmax pz w) \/ exists p, In p (a_ext a) /\ ext_in1 (s_facts S) R p = true).
  { intros R HR. pose proof (HRG R HR) as (Hz0 & Hz1 & _).
    destruct (pri_sep_t_route E (s_facts S) (sm_maps M) model (sm_sp M) _ HF0 (dn_maps _ _ _ _ _ _ _ _ _ Hd) (dn_pd _ _ _ _ _ _ _ _ _ Hd)
                (dn_gsh _ _ _ _ _ _ _ _ _ Hd) (dn_gtop _ _ _ _ _ _ _ _ _ Hd) (dn_sp _ _ _ _ _ _ _ _ _ Hd) (proj2 (dn_spok _ _ _ _ _ _ _ _ _ Hd))
                (proj1 (dn_spok _ _ _ _ _ _ _ _ _ Hd)) (dn_mres _ _ _ _ _ _ _ _ _ Hd) ASEGSR (dn_res _ _ _ _ _ _ _ _ _ Hd) gq_res a mem0 HI jP jT _ _
                Hgp eq_refl eq_refl Hgt eq_refl eq_refl (po_sep _ _ _ _ HP0) R Hz0 Hz1 (Call R HR)) as [X|X]; [left; exact X|right].
    unfold ext_in in X. rewrite existsb_l_eq in X. apply existsb_exists in X. exact X. }
  assert (Hent : forall p, In p (a_ext a) -> uE E (fst p) + uE E (snd p) < 2^48 /\ 17594333495296 <= uE E (fst p) /\ uE E (fst p) + uE E (snd p) <= 2^47).
  { intros p Hp. destruct (po_ext _ _ _ _ HP0 p Hp) as ((c' & Hcin' & Y1 & Y2 & _) & _). fold pz in Y1, Y2. pose proof (in_cls_rng c' Hcin') as Hcr'.
    destruct (cls_jb pz mem0 HI c' Hcin') as (_ & K1' & _). clear - Y1 Y2 K1' G Hcr'. lia. }
  (* [comment removed for export] *)
  assert (Happ : forall x, xp - 16 <= x < xp + 8 * n8 ->
            pri_foot_z pz x /\ own_pt E M x /\ outside E (s_rgs S) (Z_to_bv 64 x) /\ 17594333495296 <= x < 2^47).
  { intros x Hx. assert (Hf : pri_foot_z pz x) by (apply (ext_sem_foot pz mem0 _ _ HI L3e x); clear - Hx; lia).
    assert (Hr : 17594333495296 <= x < 2^47) by (clear - Hx X1 X2 K1 G Hcr; lia).
    split; [exact Hf|]. split; [exact (po_own _ _ _ _ HP0 x ltac:(clear - Hr; lia) Hf)|]. split; [|exact Hr].
    unfold outside. apply Forall_forall. intros R HR. rewrite u_small64 by (unfold two64; clear - Hr; lia).
    change (bv_unsigned (lden E (rg_base R))) with (uE E (rg_base R)).
    destruct (Z_lt_le_dec x (uE E (rg_base R))) as [Hl|Hl]; [left; exact Hl|]. destruct (Z_lt_le_dec x (uE E (rg_base R) + rsz E R)) as [Hu|Hu]; [exfalso|right; exact Hu].
    destruct (Hroute R HR) as [Hfp|(p & Hp & Hp1)].
    - apply (Hfp x (conj Hl Hu)). left. unfold PG_SIZE. clear - Hx X1 X2 K1 G Hcr. lia.
    - destruct (Hent p Hp) as (E48 & Elo & Ehi). destruct (ext_in1_geo E (s_facts S) HF0 R p Hp1 E48) as [[U1 U2]|(V0 & V1 & V2)].
      + apply (lv_apart_entry E a mem0 p k Hlv Hp Ckb HB x). unfold lv_lo, lv_sz. fold XP N8 xp n8. split; [clear - U1 U2 Hl Hu; lia | clear - Hx; lia].
      + unfold SH_OFF in *. clear - V0 V1 V2 Hl Hu Hr Ehi. lia. }
  (* [comment removed for export] *)
  assert (Hshp : forall y, xq + SH_OFF <= y < xq + SH_OFF + n8 ->
            pri_foot_z pz y /\ own_pt E M y /\ outside E (s_rgs S) (Z_to_bv 64 y) /\ 2199291686912 <= y < 17594333495296 /\
            z_sh pz + 536870912 * c <= y < z_sh pz + 536870912 * c + PJ).
  { intros y Hy. assert (Hyc : z_sh pz + 536870912 * c <= y < z_sh pz + 536870912 * c + PJ) by (rewrite Esh; clear - Hy Q1 Q2; lia).
    assert (Hf : pri_foot_z pz y).
    { right. right. right. exists c. split; [exact Hcin|]. right. right. left. clear - Hyc Q3. lia. }
    assert (Hr : 2199291686912 <= y < 17594333495296) by (rewrite Esh in Hyc; unfold SH_OFF in *; clear - Hyc Q3 Q4 Hcr; lia).
    split; [exact Hf|]. split; [exact (po_own _ _ _ _ HP0 y ltac:(clear - Hr; lia) Hf)|]. split; [|split; [exact Hr | exact Hyc]].
    unfold outside. apply Forall_forall. intros R HR. rewrite u_small64 by (unfold two64; clear - Hr; lia).
    change (bv_unsigned (lden E (rg_base R))) with (uE E (rg_base R)).
    destruct (Z_lt_le_dec y (uE E (rg_base R))) as [Hl|Hl]; [left; exact Hl|]. destruct (Z_lt_le_dec y (uE E (rg_base R) + rsz E R)) as [Hu|Hu]; [exfalso|right; exact Hu].
    destruct (Hroute R HR) as [Hfp|(p & Hp & Hp1)].
    - apply (Hfp y (conj Hl Hu)). right. right. left. clear - Hyc Q3 Hcr. lia.
    - destruct (Hent p Hp) as (E48 & Elo & Ehi). destruct (ext_in1_geo E (s_facts S) HF0 R p Hp1 E48) as [[U1 U2]|(V0 & V1 & V2)].
      + clear - U1 U2 Hl Hu Hr Elo. lia.
      + apply (lv_apart_entry E a mem0 p k Hlv Hp Ckb HB (8 * (y - SH_OFF))). unfold lv_lo, lv_sz. fold XP N8 xp n8.
        split; [clear - V0 V1 V2 Hl Hu; lia | rewrite Exq; clear - Hy; lia]. }
  (* [comment removed for export] *)
  set (E1 := upd (upd E VQ (wa xq)) EV (wa (8 * n8 - n))).
  assert (Hag : agree (s_next S) E E1).
  { intros v Hv. unfold E1, upd. destruct (Pos.eqb_spec v EV) as [->|_]; [unfold EV in Hv; lia|]. destruct (Pos.eqb_spec v VQ) as [->|_]; [unfold VQ in Hv; lia | reflexivity]. }
  assert (Evq : E1 VQ = wa xq).
  { unfold E1, upd. destruct (Pos.eqb_spec VQ EV) as [X|_]; [unfold EV, VQ in X; lia|]. rewrite Pos.eqb_refl. reflexivity. }
  assert (Eev : E1 EV = wa (8 * n8 - n)) by (unfold E1, upd; rewrite Pos.eqb_refl; reflexivity).
  set (nfin := (s_next S + 2)%positive).
  assert (Hvq : (VQ < nfin)%positive) by (unfold VQ, nfin; lia). assert (Hev : (EV < nfin)%positive) by (unfold EV, nfin; lia).
  assert (Hsn : (s_next S <= nfin)%positive) by (unfold nfin; lia).
  pose proof (den_agree ASEGS LIMIT model0 mem0 E E1 S M ms model Hd Hag) as HD1.
  pose proof (den_bump ASEGS LIMIT model0 mem0 E1 S M ms model nfin HD1 Hsn) as HD2.
  pose proof (dn_wf _ _ _ _ _ _ _ _ _ Hd) as HwfM.
  (* [comment removed for export] *)
  assert (Hxq : 0 <= xq < 2^61) by (clear - Q1 Q2 Q3 Q4 Hcr L5; lia).
  assert (Hwl : forall i, lwf (s_next S) (lv_nth a i) = true) by exact (awf_lv (s_next S) a Haw).
  assert (HwXP : lwf (s_next S) XP = true) by exact (Hwl _). assert (HwN : lwf (s_next S) N = true) by exact (Hwl _).
  assert (HwF : lwf (s_next S) F = true) by exact (Hwl _). assert (HwC : lwf (s_next S) C = true) by exact (Hwl _). assert (HwN8 : lwf (s_next S) N8 = true) by exact (Hwl _).
  assert (Hold : forall E3 l, agree nfin E1 E3 -> lwf (s_next S) l = true -> uE E3 l = uE E l).
  { intros E3 l Ha3 Hl. unfold uE. rewrite (lden_agree_wf (s_next S) E E3 l Hl); [reflexivity|].
    apply (agree_trans _ E E1 E3 Hag). exact (agree_mono _ nfin E1 E3 Hsn Ha3). }
  assert (Hvq3 : forall E3, agree nfin E1 E3 -> uE E3 (lvar VQ) = xq).
  { intros E3 Ha3. apply uE_lvar_wa; [rewrite <- (Ha3 VQ Hvq); exact Evq | clear - Hxq; lia]. }
  assert (Hev3 : forall E3, agree nfin E1 E3 -> uE E3 (lvar EV) = 8 * n8 - n).
  { intros E3 Ha3. apply uE_lvar_wa; [rewrite <- (Ha3 EV Hev); exact Eev | clear - L4 L5; lia]. }
  assert (Hp83 : forall E3, agree nfin E1 E3 -> uE E3 P8 = xp).
  { intros E3 Ha3. unfold P8. rewrite uE_lscale_s; rewrite (Hvq3 E3 Ha3); [symmetry; exact Exq | unfold two64; clear - Hxq; lia]. }
  assert (Hu83 : forall E3, agree nfin E1 E3 -> uE E3 U8 = 8 * n8).
  { intros E3 Ha3. unfold U8. rewrite uE_lscale_s; rewrite (Hold E3 N8 Ha3 HwN8); fold n8; [reflexivity | unfold two64; clear - L5; lia]. }
  assert (Hns3 : forall E3, agree nfin E1 E3 -> uE E3 NS = n).
  { intros E3 Ha3. unfold NS. rewrite uE_lsub_m, (Hu83 E3 Ha3), (Hev3 E3 Ha3). replace (8 * n8 - (8 * n8 - n)) with n by ring.
    apply Z.mod_small. exact (uE_rng E N). }
  assert (Hrefl : agree nfin E1 E1) by (intros v _; reflexivity).
  (* [comment removed for export] *)
  assert (Hrk : rkz 10 <> xH) by (intros Hc0; vm_compute in Hc0; discriminate).
  assert (Hch : forall E3, agree (s_next (bump S nfin)) E1 E3 -> lden E3 P8 = lden E3 (rget (s_regs (bump S nfin)) (rkz 10))).
  { intros E3 Ha3. cbn [bump s_next s_regs] in *. rewrite Ca0.
    rewrite <- (Z_to_bv_bv_unsigned 64 (lden E3 P8)), <- (Z_to_bv_bv_unsigned 64 (lden E3 XP)). f_equal.
    change (uE E3 P8 = uE E3 XP). rewrite (Hp83 E3 Ha3), (Hold E3 XP Ha3 HwXP). reflexivity. }
  pose proof (den_reg_eq ASEGS LIMIT model0 mem0 E1 _ M ms model (rkz 10) P8 HD2 Hrk Hch) as HD3.
  set (Y1 := with_reg (bump S nfin) (rkz 10) P8) in *.
  (* [comment removed for export] *)
  assert (Hwsb : lwf (s_next S) (p_sb a) = true) by (apply lwf_p_nth; exact (awf_pri _ a Haw)).
  pose proof (irange_sound E (s_facts S) (p_sb a) HF0) as Rsb. fold (uE E (p_sb a)) in Rsb.
  assert (Esb : uE E (p_sb a) = z_sb pz) by (symmetry; apply zn_pden). rewrite Esb in Rsb.
  set (sbr := irange (s_facts S) (p_sb a)) in *.
  set (newfacts := [FRange (lsub XP P8) 0 0; FRange (lvar EV) 0 7; FRange (lsub NS N) 0 0; FRange N8 1 8192;
                    FRange (lvar VQ) ((fst sbr + 4294967296) / 8) ((snd sbr + 4294967296 * 30 + 262144) / 8);
                    FRange (lsub P8 (p_sb a)) 4294967296 (4294967296 * 30 + 262144)]).
  assert (Hnfacts : forall E3, agree (s_next Y1) E1 E3 -> Forall (fact_ok E3) newfacts).
  { intros E3 Ha3. change (s_next Y1) with nfin in Ha3. unfold newfacts.
    pose proof (Hp83 E3 Ha3) as V1. pose proof (Hold E3 XP Ha3 HwXP) as V2. fold xp in V2. pose proof (Hev3 E3 Ha3) as V3.
    pose proof (Hns3 E3 Ha3) as V4. pose proof (Hold E3 N Ha3 HwN) as V5. fold n in V5. pose proof (Hold E3 N8 Ha3 HwN8) as V6. fold n8 in V6.
    pose proof (Hvq3 E3 Ha3) as V7. pose proof (Hold E3 (p_sb a) Ha3 Hwsb) as V8. rewrite Esb in V8.
    constructor; [|constructor; [|constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]]]]; cbn [fact_ok].
    - change (0 <= uE E3 (lsub XP P8) <= 0). rewrite uE_lsub_m, V1, V2, Z.sub_diag. rewrite Z.mod_0_l by (unfold two64; clear; lia). clear; lia.
    - change (0 <= uE E3 (lvar EV) <= 7). rewrite V3. clear - L4. lia.
    - change (0 <= uE E3 (lsub NS N) <= 0). rewrite uE_lsub_m, V4, V5, Z.sub_diag. rewrite Z.mod_0_l by (unfold two64; clear; lia). clear; lia.
    - change (1 <= uE E3 N8 <= 8192). rewrite V6. exact L5.
    - change (((fst sbr + 4294967296) / 8) <= uE E3 (lvar VQ) <= ((snd sbr + 4294967296 * 30 + 262144) / 8)). rewrite V7. unfold xq.
      split; apply Z.div_le_mono; try (clear; lia); clear - Rsb X1 X2 K1 Hcr L5; lia.
    - change (4294967296 <= uE E3 (lsub P8 (p_sb a)) <= 4294967296 * 30 + 262144). rewrite uE_lsub_m, V1, V8.
      rewrite Z.mod_small by (unfold two64; clear - X1 X2 K1 Hcr L5 G; lia). clear - X1 X2 K1 Hcr L5. lia. }
  pose proof (den_add_facts ASEGS LIMIT model0 mem0 E1 Y1 M ms model newfacts HD3 Hnfacts) as HD4.
  set (Y2 := with_facts Y1 (s_facts Y1 ++ newfacts)) in *.
  (* [comment removed for export] *)
  pose proof (dn_bases _ _ _ _ _ _ _ _ _ Hd) as HbwS.
  assert (Hpt : forall w, own_pt E M w -> outside E (s_rgs S) (Z_to_bv 64 w) ->
            own_pt E1 M w /\ outside E1 (s_rgs S) (Z_to_bv 64 w) /\ ms_mem ms (Z_to_bv 64 w) = mem0 (Z_to_bv 64 w)).
  { intros w Ho Hout. split; [exact (proj2 (own_pt_agree (s_next S) E E1 M w HwfM Hag) Ho)|]. split; [exact (proj1 (outside_agree (s_next S) E E1 _ _ HbwS Hag) Hout)|].
    destruct Ho as (q & Hq & Hqw). exact (proj2 (dn_own _ _ _ _ _ _ _ _ _ Hd q Hq w Hqw) Hout). }
  assert (Happ2 : forall x, xp - 16 <= x < xp + 8 * n8 ->
            own_pt E1 M x /\ outside E1 (s_rgs S) (Z_to_bv 64 x) /\ ms_mem ms (Z_to_bv 64 x) = mem0 (Z_to_bv 64 x) /\ mem0 (Z_to_bv 64 x) <> None /\
            app_pt model x /\ x < alloc_top (m_vmmaps model) /\ 17594333495296 <= x < 2^47).
  { intros x Hx. destruct (Happ x Hx) as (Hf & Ho & Hout & Hr). destruct (Hpt x Ho Hout) as (P1 & P2 & P3).
    assert (Hns : in_shadow x = false) by (unfold in_shadow, SH_LO, SH_HI; apply andb_false_iff; right; apply Z.ltb_ge; clear - Hr; lia).
    assert (Hcov : covered (vm_maps (m_vmmaps model)) x = true).
    { apply (pri_covered LIMIT model0 mem0 E S M ms model a mem0 Hd HA0 Hne x Hf Hns). clear - Hr. lia. }
    split; [exact P1|]. split; [exact P2|]. split; [exact P3|]. split; [exact (L2m x ltac:(clear - Hx; lia))|]. split; [|split; [|exact Hr]].
    - split; [left; unfold covered in *; rewrite existsb_app; rewrite Hcov; apply orb_true_r|]. split; [exact Hns | clear - Hr; lia].
    - exact (covered_below_top ASEGS LIMIT model0 mem0 E S M ms model x Hd Hcov). }
  assert (Hshp2 : forall y, xq + SH_OFF <= y < xq + SH_OFF + n8 ->
            own_pt E1 M y /\ outside E1 (s_rgs S) (Z_to_bv 64 y) /\ ms_mem ms (Z_to_bv 64 y) <> None /\
            in_shadow y = true /\ covered (vm_maps (m_vmmaps model)) y = true /\ y < alloc_top (m_vmmaps model) /\ 2199291686912 <= y < 17594333495296).
  { intros y Hy. destruct (Hshp y Hy) as (Hf & Ho & Hout & Hr & Hyc). destruct (Hpt y Ho Hout) as (P1 & P2 & P3).
    assert (Hzr : in_zr (sm_zr M) y = true).
    { apply (po_zr _ _ _ _ HP0). exists c. split; [exact Hcin|]. left. fold pz. clear - Hyc Q3. lia. }
    pose proof (dn_zrm _ _ _ _ _ _ _ _ _ Hd y Hzr) as Hcov.
    split; [exact P1|]. split; [exact P2|]. split; [|split; [exact (dn_zrsh _ _ _ _ _ _ _ _ _ Hd y Hzr)|split; [exact Hcov|split; [|exact Hr]]]].
    - rewrite P3. destruct (iz_cls _ _ HI c Hcin) as [(J0 & _)|(_ & _ & _ & _ & HPo)]; [exfalso; unfold PJ in Hyc; rewrite J0 in Hyc; clear - Hyc; lia|].
      apply (pc_shm _ _ _ _ _ _ HPo y). unfold SHX. clear - Hyc Q3. lia.
    - exact (covered_below_top ASEGS LIMIT model0 mem0 E S M ms model y Hd Hcov). }
  (* [comment removed for export] *)
  set (R3 := RG (laddc (lvar VQ) SH_OFF) N8 RW TEmpty). set (R2 := RG P8 U8 RW TEmpty). set (R1 := RG (laddc P8 (-16)) (lconst 16) RW (hdr_cont F NS C)).
  assert (Hny2 : s_next Y2 = nfin) by reflexivity. assert (Hrgs2 : s_rgs Y2 = s_rgs S) by reflexivity.
  assert (Hwn : forall l, lwf (s_next S) l = true -> lwf nfin l = true) by (intros l Hl; exact (lwf_mono' (s_next S) nfin l Hsn Hl)).
  assert (Eb3 : uE E1 (rg_base R3) = xq + SH_OFF).
  { unfold R3. cbn [rg_base]. rewrite uE_laddc_z; rewrite (Hvq3 E1 Hrefl); [reflexivity | unfold two64, SH_OFF; clear - Hxq; lia]. }
  assert (Ez3 : rsz E1 R3 = n8) by (unfold rsz, R3; cbn [rg_size]; exact (Hold E1 N8 Hrefl HwN8)).
  assert (Eb2 : uE E1 (rg_base R2) = xp) by exact (Hp83 E1 Hrefl).
  assert (Ez2 : rsz E1 R2 = 8 * n8) by exact (Hu83 E1 Hrefl).
  assert (Eb1 : uE E1 (rg_base R1) = xp - 16).
  { unfold R1. cbn [rg_base]. rewrite uE_laddc_z; rewrite (Hp83 E1 Hrefl); [ring | unfold two64; clear - X1 X2 K1 L5 G Hcr; lia]. }
  assert (Ez1 : rsz E1 R1 = 16) by (unfold rsz, R1; cbn [rg_size]; apply (uE_lc E1 16); clear; lia).
  assert (HD5 : DEN ASEGS LIMIT model0 mem0 E1 (addo_post Y2 R3) M ms model).
  { apply (den_add_own ASEGS LIMIT model0 mem0 E1 Y2 M ms model R3 HD4).
    - rewrite Hny2. apply lwf_laddc. apply lwf_lvar. exact Hvq.
    - rewrite Hny2. exact (Hwn _ HwN8).
    - reflexivity.
    - intros p v Hp. unfold R3 in Hp. cbn [rg_cont] in Hp. rewrite tget_empty in Hp. discriminate.
    - rewrite Ez3. clear - L5. lia.
    - rewrite Eb3, Ez3. unfold SH_OFF. clear - Q1 Q2 Q3 Q4 Hcr. lia.
    - intros x Hx. rewrite Eb3, Ez3 in Hx. destruct (Hshp2 x Hx) as (N1 & _ & N3 & _ & _ & N6 & _). split; [exact N1|]. split; [exact N3 | exact N6].
    - intros p b Hp. unfold R3 in Hp. cbn [rg_cont] in Hp. rewrite tget_empty in Hp. discriminate.
    - intros R' HR' w Hw Hc0. rewrite Eb3, Ez3 in Hc0. rewrite Hrgs2 in HR'. destruct (Hshp2 w Hc0) as (_ & N2 & _ & _ & _ & _ & N7).
      unfold outside in N2. rewrite Forall_forall in N2. specialize (N2 R' HR'). rewrite u_small64 in N2 by (unfold two64; clear - N7; lia).
      unfold uE in Hw. clear - N2 Hw. lia.
    - unfold rl_ok. cbv zeta. rewrite Eb3, Ez3. split; [clear - L5; lia|]. right. split; [clear - Hxq; lia|]. split.
      + intros x Hx. destruct (Happ2 x ltac:(rewrite Exq; clear - Hx; lia)) as (_ & _ & _ & _ & N5 & _). exact N5.
      + intros w Hw. destruct (Hshp2 w Hw) as (_ & _ & _ & N4 & N5 & _). split; [exact N4 | exact N5]. }
  assert (HD6 : DEN ASEGS LIMIT model0 mem0 E1 (addo_post (addo_post Y2 R3) R2) M ms model).
  { apply (den_add_own ASEGS LIMIT model0 mem0 E1 (addo_post Y2 R3) M ms model R2 HD5).
    - cbn [addo_post s_next]. rewrite Hny2. unfold R2, P8. cbn [rg_base]. apply lwf_lscale. apply lwf_lvar. exact Hvq.
    - cbn [addo_post s_next]. rewrite Hny2. unfold R2, U8. cbn [rg_size]. apply lwf_lscale. exact (Hwn _ HwN8).
    - reflexivity.
    - intros p v Hp. unfold R2 in Hp. cbn [rg_cont] in Hp. rewrite tget_empty in Hp. discriminate.
    - rewrite Ez2. clear - L5. lia.
    - rewrite Eb2, Ez2. clear - X2 K1 G Hcr. lia.
    - intros x Hx. rewrite Eb2, Ez2 in Hx. destruct (Happ2 x ltac:(clear - Hx; lia)) as (N1 & _ & N3 & N4 & _ & N6 & _). split; [exact N1|]. split; [rewrite N3; exact N4 | exact N6].
    - intros p b Hp. unfold R2 in Hp. cbn [rg_cont] in Hp. rewrite tget_empty in Hp. discriminate.
    - intros R' HR' w Hw Hc0. rewrite Eb2, Ez2 in Hc0. cbn [addo_post s_rgs] in HR'. destruct HR' as [<-|HR'].
      + rewrite Eb3, Ez3 in Hw. destruct (Hshp2 w Hw) as (_ & _ & _ & _ & _ & _ & N7). destruct (Happ2 w ltac:(clear - Hc0; lia)) as (_ & _ & _ & _ & _ & _ & N8'). clear - N7 N8'. lia.
      + rewrite Hrgs2 in HR'. destruct (Happ2 w ltac:(clear - Hc0; lia)) as (_ & N2 & _ & _ & _ & _ & N7).
        unfold outside in N2. rewrite Forall_forall in N2. specialize (N2 R' HR'). rewrite u_small64 in N2 by (unfold two64; clear - N7; lia).
        unfold uE in Hw. clear - N2 Hw. lia.
    - unfold rl_ok. cbv zeta. rewrite Eb2, Ez2. split; [clear - L5; lia|]. left.
      intros w Hw. destruct (Happ2 w ltac:(clear - Hw; lia)) as (_ & _ & _ & _ & N5 & _). exact N5. }
  assert (Hhdr1 : List.map (bden E1) (lv_hdr F NS C) = List.map (bden E) (lv_hdr F N C)).
  { apply lv_hdr_bden; [exact (Hold E1 F Hrefl HwF) | exact (Hns3 E1 Hrefl) | exact (Hold E1 C Hrefl HwC)]. }
  assert (HwNS : lwf nfin NS = true).
  { unfold NS, U8. apply lwf_lsub; [apply lwf_lscale; exact (Hwn _ HwN8) | apply lwf_lvar; exact Hev]. }
  assert (HD7 : DEN ASEGS LIMIT model0 mem0 E1 (addo_post (addo_post (addo_post Y2 R3) R2) R1) M ms model).
  { apply (den_add_own_v ASEGS LIMIT model0 mem0 E1 (addo_post (addo_post Y2 R3) R2) M ms model R1 HD6).
    - cbn [addo_post s_next]. rewrite Hny2. unfold R1, P8. cbn [rg_base]. apply lwf_laddc. apply lwf_lscale. apply lwf_lvar. exact Hvq.
    - cbn [addo_post s_next]. rewrite Hny2. reflexivity.
    - left. reflexivity.
    - intros p v Hp. cbn [addo_post s_next]. rewrite Hny2. unfold R1 in Hp. cbn [rg_cont] in Hp.
      destruct (hdr_cont_inv _ _ _ _ _ Hp) as (i & _ & _ & Hi). exact (lv_hdr_bwf nfin F NS C (Hwn _ HwF) HwNS (Hwn _ HwC) v (nth_error_In _ _ Hi)).
    - rewrite Ez1. clear. lia.
    - rewrite Eb1, Ez1. clear - X2 K1 G Hcr L5. lia.
    - intros x Hx. rewrite Eb1, Ez1 in Hx. destruct (Happ2 x ltac:(clear - Hx L5; lia)) as (N1 & _ & N3 & N4 & _ & N6 & _). split; [exact N1|]. split; [rewrite N3; exact N4 | exact N6].
    - intros p v Hp. unfold R1 in Hp. cbn [rg_cont] in Hp. destruct (hdr_cont_inv _ _ _ _ _ Hp) as (i & Hi16 & Hpi & Hi).
      rewrite Ez1, Eb1, Hpi. split; [clear - Hi16; lia|].
      destruct (Happ2 (xp - 16 + Z.of_nat i) ltac:(clear - Hi16 L5; lia)) as (_ & _ & N3 & _). rewrite N3.
      assert (Hm : nth_error (List.map (bden E1) (lv_hdr F NS C)) i = Some (bden E1 v)) by (rewrite nth_error_map, Hi; reflexivity).
      rewrite Hhdr1, nth_error_map in Hm. destruct (nth_error (lv_hdr F N C) i) as [v0|] eqn:Ev0; [|discriminate]. cbn [option_map] in Hm. injection Hm as Hm.
      rewrite <- Hm. exact (L2 i v0 Ev0).
    - intros R' HR' w Hw Hc0. rewrite Eb1, Ez1 in Hc0. cbn [addo_post s_rgs] in HR'. destruct HR' as [<-|[<-|HR']].
      + rewrite Eb2, Ez2 in Hw. clear - Hw Hc0. lia.
      + rewrite Eb3, Ez3 in Hw. destruct (Hshp2 w Hw) as (_ & _ & _ & _ & _ & _ & N7). destruct (Happ2 w ltac:(clear - Hc0 L5; lia)) as (_ & _ & _ & _ & _ & _ & N8'). clear - N7 N8'. lia.
      + rewrite Hrgs2 in HR'. destruct (Happ2 w ltac:(clear - Hc0 L5; lia)) as (_ & N2 & _ & _ & _ & _ & N7).
        unfold outside in N2. rewrite Forall_forall in N2. specialize (N2 R' HR'). rewrite u_small64 in N2 by (unfold two64; clear - N7; lia).
        unfold uE in Hw. clear - N2 Hw. lia.
    - unfold rl_ok. cbv zeta. rewrite Eb1, Ez1. split; [clear; lia|]. left.
      intros w Hw. destruct (Happ2 w ltac:(clear - Hw L5; lia)) as (_ & _ & _ & _ & N5 & _). exact N5. }
  apply (Hk E1 mem0 ms model); [exact Hag | intros p Hp w Hw; reflexivity | exact HD7 |].
  intros _.
  pose proof (HA_on_agree (s_next S) E E1 M a mem0 HA0 HwfM Haw Hag) as HA1.
  set (a0 := lv_put a k lc0 lc0 lc0 lc0 lc0 lc0).
  destruct (lv_put_rest a k lc0 lc0 lc0 lc0 lc0 lc0) as (R01 & R02 & R03 & R04 & R05 & R06 & R07). cbv zeta in R01, R02, R03, R04, R05, R06, R07. fold a0 in R01, R02, R03, R04, R05, R06, R07.
  assert (HA2 : HA_on E1 M a0 mem0).
  { apply (HA_on_lv E1 M a a0 mem0 HA1 R01 R02 R03 R04 R05 R06); [exact (lv_put_live_in a k lc0 lc0 lc0 lc0 lc0 lc0)|].
    intros _ Hlv1. exact (lv_inv_put0 E1 a mem0 k lc0 lc0 lc0 lc0 lc0 lc0 Hok Ckb eq_refl Hlv1). }
  assert (Epz1 : pden E1 a = pz) by exact (pden_agree (s_next S) E E1 a Haw Hag).
  assert (Eu16 : uE E1 (laddc U8 16) = 8 * n8 + 16).
  { rewrite uE_laddc_z; rewrite (Hu83 E1 Hrefl); [reflexivity | unfold two64; clear - L5; lia]. }
  apply (HA_on_ext_add E1 M a0 mem0 (laddc P8 (-16)) (laddc U8 16) HA2).
  - intros _. unfold pden. rewrite R06. fold (pden E1 a). rewrite Epz1. change (laddc P8 (-16)) with (rg_base R1). rewrite Eb1, Eu16.
    replace (8 * n8 + 16) with (16 + 8 * n8) by ring. exact L3e.
  - intros _ q Hq x [Xa Xq]. change (laddc P8 (-16)) with (rg_base R1) in Xa. rewrite Eb1, Eu16 in Xa.
    destruct (x_rngs_put0_in E1 a k lc0 lc0 lc0 lc0 lc0 lc0 q x Hok Ckb eq_refl Hq Xq) as (j & Hj & Hjq).
    rewrite (x_rngs_agree (s_next S) E E1 a Haw Hag) in Hjq. rewrite (e_rngs_agree (s_next S) E E1 a Haw Hag) in Hj.
    assert (Hkq : nth_error (x_rngs E a) (List.length (e_rngs E a) + k)%nat = Some (lv_rng E a k)).
    { unfold x_rngs. rewrite nth_error_app2 by lia. replace (List.length (e_rngs E a) + k - List.length (e_rngs E a))%nat with k by (clear; lia).
      rewrite lv_rngs_nth, (proj2 (Nat.ltb_lt k LV_N) Ckb). reflexivity. }
    apply (proj2 Hlv _ _ _ _ Hj Hjq Hkq x). split; [exact Xq|].
    unfold in_rg, lv_rng, lv_lo, lv_sz. cbn [fst snd]. fold B XP N8 xp n8. rewrite HB. clear - Xa. lia.
Qed.
End Take.
End AcLvTake.

From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcPsr.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcFam3.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcCache AcFam3.
Import OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcPri.AcDepSep OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcAst OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcHA OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcFam OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcPri OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcFam2 OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcFam2Ok OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcHA.AcLv OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcFam3.AcLvN OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcFam3Ok.AcLvNil OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcFam3Ok.AcLvStash OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcFam3Ok.AcLvTake OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcPsr OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcFam3.AcQjPos OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcCache OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcFam3.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section Fam3.
Variable cfg : SpuriousCfg.
Variable LIMIT : Z.
Hypothesis Hwx : wx_segs_nowrap ASEGS.
Hypothesis Hsegb : segs_below_b ASEGS 0x800000000000 = true.
Hypothesis Hoff : sc_alloc cfg = false.
Hypothesis Hrespos : Forall (fun p => 0 < bv_unsigned (snd p)) (segments_reserved ASEGS).
Hypothesis Hreswf : ivs_wf (segments_reserved ASEGS).

#[using="Hwx Hsegb Hoff Hrespos Hreswf"] Theorem alloc3_anode_ok : forall nk, anode_ok ASEGS cfg LIMIT (apost_alloc3 LIMIT) awf HA nk.
Proof. LiaFast.lf_pins (fun (Hwx Hsegb Hoff Hrespos Hreswf : LiaFast.U) => LiaFast.u0).
  intros [nk|k i h u z|k r|k| |i|k| | |n|kk] S M a S' M' a' H model0 mem0 E ms model T Hd Haw HHA Hk; cbn [apost_alloc3] in H.
  - exact (alloc2_anode_ok cfg LIMIT Hwx Hsegb Hoff Hrespos Hreswf nk S M a S' M' a' H model0 mem0 E ms model T Hd Haw HHA Hk).
  - exact (nstash_node cfg LIMIT model0 k i h u z S M a S' M' a' H mem0 E ms model T Hd Haw HHA Hk).
  - exact (nstashnil_node cfg LIMIT model0 k r S M a S' M' a' H mem0 E ms model T Hd Haw HHA Hk).
  - exact (nlvdrop_node cfg LIMIT model0 k S M a S' M' a' H mem0 E ms model T Hd Haw HHA Hk).
  - exact (nlvclear_node cfg LIMIT model0 S M a S' M' a' H mem0 E ms model T Hd Haw HHA Hk).
  - exact (npsr_node cfg LIMIT model0 i S M a S' M' a' H mem0 E ms model T Hd Haw HHA Hk).
  - exact (ntake_node cfg LIMIT model0 k S M a S' M' a' H mem0 E ms model T Hd Haw HHA Hk).
  - exact (nqjpos_node cfg LIMIT model0 S M a S' M' a' H mem0 E ms model T Hd Haw HHA Hk).
  - exact (ncacheadd_node cfg LIMIT model0 S M a S' M' a' H mem0 E ms model T Hd Haw HHA Hk).
  - exact (ncachedrop_node cfg LIMIT model0 n S M a S' M' a' H mem0 E ms model T Hd Haw HHA Hk).
  - exact (ncachekeep_node cfg LIMIT model0 kk S M a S' M' a' H mem0 E ms model T Hd Haw HHA Hk).
Qed.
End Fam3.
