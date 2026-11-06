(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.fast_float.from_chars.images Require Import Asan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec FxLin FxCore FxSound FxMem FxSubst FxEnt.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require Import FxBacking FxChDen FxChEntM.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require Import AXG_put.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcAst AcPri.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcHA.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcHA.
Import OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcAst OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcPri OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcHA.AcLv OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcHA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition esubst (σ : tree lin) (R : region) : region := RG (lsubst σ (rg_base R)) (lsubst σ (rg_size R)) (rg_kind R) (tmap (bsubst σ) (rg_cont R)).
Definition asubst (σ : tree lin) (a : ast) : ast :=
  AST (a_on a) (List.map (esubst σ) (a_rgs a)) (a_fcts a) (List.map (ppsubst σ) (a_own a)) (ppsubst σ (a_dep a)) (lsubst σ (a_nl a)) (List.map (ppsubst σ) (a_live a))
      (List.map (lsubst σ) (a_pri a)).
Lemma a_ext_sub : forall σ a, a_ext (asubst σ a) = List.map (ppsubst σ) (a_ext a).
Proof. intros σ a. unfold a_ext, asubst. cbn [a_rgs]. rewrite !map_map. reflexivity. Qed.

(* [comment removed for export] *)
Definition plins (l : list (lin * lin)) : list lin := List.flat_map (fun p => [fst p; snd p]) l.
Fixpoint pfill (l : list (lin * lin)) (ls : list lin) : list (lin * lin) * list lin :=
  match l with
  | [] => ([], ls)
  | p :: r => match ls with
              | x :: y :: ls' => let '(r', rest) := pfill r ls' in ((x, y) :: r', rest)
              | _ => (p :: r, ls)
              end
  end.
(* [comment removed for export] *)
Fixpoint rfill (l : list region) (ls : list lin) : list region :=
  match l with
  | [] => []
  | R :: r => match ls with
              | x :: y :: ls' => RG x y (rg_kind R) (rg_cont R) :: rfill r ls'
              | _ => R :: r
              end
  end.
Definition alins_a (a : ast) : list lin := a_nl a :: fst (a_dep a) :: snd (a_dep a) :: plins (a_own a) ++ plins (a_live a) ++ a_pri a ++ plins (a_ext a).
Definition aset_a (a : ast) (ls : list lin) : ast :=
  match ls with
  | nl :: d1 :: b1 :: ls1 =>
      let '(own', ls2) := pfill (a_own a) ls1 in
      let '(live', ls3) := pfill (a_live a) ls2 in
      AST (a_on a) (rfill (a_rgs a) (skipn (List.length (a_pri a)) ls3)) (a_fcts a) own' (d1, b1) nl live' (firstn (List.length (a_pri a)) ls3)
  | _ => a
  end.
Lemma pfill_plins : forall l rest, pfill l (plins l ++ rest) = (l, rest).
Proof. induction l as [|[x y] r IH]; intros rest; cbn; [reflexivity|]. rewrite IH. reflexivity. Qed.
Lemma rfill_plins : forall l, rfill l (plins (List.map (fun R => (rg_base R, rg_size R)) l)) = l.
Proof. induction l as [|[b z k c] r IH]; [reflexivity|]. cbn [List.map plins flat_map rg_base rg_size fst snd app rfill rg_kind rg_cont]. fold (plins (List.map (fun R => (rg_base R, rg_size R)) r)). rewrite IH. reflexivity. Qed.
Lemma aset_alins : forall a, aset_a a (alins_a a) = a.
Proof.
  intros [o r f w [d1 b1] n l p]. unfold aset_a, alins_a, a_ext. cbn [a_dep a_own a_live a_pri fst snd a_on a_rgs a_fcts a_nl].
  rewrite pfill_plins, pfill_plins. rewrite firstn_app, Nat.sub_diag, firstn_all. cbn [firstn]. rewrite app_nil_r.
  rewrite skipn_app, Nat.sub_diag, skipn_all. cbn [skipn app]. rewrite rfill_plins. reflexivity.
Qed.

(* [comment removed for export] *)
Definition gent_b (b : lin) (z : Z) (g : lin * lin * gkind) : bool := (lin_eqb (fst (fst g)) b && lin_eqb (snd (fst g)) (lconst z))%bool.
Definition ag_ok (M : smodel) (a : ast) : bool :=
  (existsb (gent_b (fst (a_dep a)) 1048576) (sm_maps M) && existsb (gent_b (snd (a_dep a)) 8388608) (sm_maps M) &&
   list_eqb pair_eqb (a_own a) (aown_of a) &&
   match a_pri a with [] => true | _ => (existsb (gent_b (p_pg a) PG_SIZE) (sm_maps M) && existsb (gent_b (p_tg a) TG_SIZE) (sm_maps M))%bool end)%bool.

(* [comment removed for export] *)
Lemma lsubst_lc0 : forall σ, lsubst σ lc0 = lc0.
Proof. intros σ. reflexivity. Qed.
Lemma p_nth_sub : forall σ a k, p_nth (asubst σ a) k = lsubst σ (p_nth a k).
Proof. intros σ a k. unfold p_nth, asubst. cbn [a_pri]. rewrite <- (lsubst_lc0 σ) at 1. apply map_nth. Qed.
Lemma pden_sub : forall E σ a, pden (ecomp E σ) a = pden E (asubst σ a).
Proof. intros E σ a. unfold pden, asubst. cbn [a_pri]. rewrite map_map. apply map_ext. intros l. apply uE_sub. Qed.
Lemma pri_nil_sub : forall σ a, a_pri (asubst σ a) <> [] <-> a_pri a <> [].
Proof. intros σ a. unfold asubst. cbn [a_pri]. destruct (a_pri a); cbn; split; intros H; try exact H; congruence. Qed.

Lemma gent_in : forall b z (gs : list (lin * lin * gkind)), existsb (gent_b b z) gs = true -> exists k, In (b, lconst z, k) gs.
Proof.
  intros b z gs H. apply existsb_exists in H as ([[b' z'] k] & Hin & Hg). unfold gent_b in Hg. cbn [fst snd] in Hg.
  apply andb_prop in Hg as [H1 H2]. apply lin_eqb_eq in H1, H2. subst. exists k. exact Hin.
Qed.

(* [comment removed for export] *)
Lemma lv_nth_sub : forall σ a i, lv_nth (asubst σ a) i = lsubst σ (lv_nth a i).
Proof.
  intros σ a i. unfold lv_nth, lv_car, lv_pairs, lv_cnt, asubst. cbn [a_live a_fcts]. rewrite length_map, skipn_map, map_map.
  rewrite <- (lsubst_lc0 σ) at 1. rewrite <- (map_nth (lsubst σ)). rewrite map_map. reflexivity.
Qed.
Lemma lv_inv_sub : forall E σ a m0, lv_inv E (asubst σ a) m0 <-> lv_inv (ecomp E σ) a m0.
Proof.
  intros E σ a m0.
  assert (Hv : forall i, uE (ecomp E σ) (lv_nth a i) = uE E (lv_nth (asubst σ a) i)) by (intros i; rewrite lv_nth_sub; apply uE_sub).
  assert (He : e_rngs (ecomp E σ) a = e_rngs E (asubst σ a)).
  { unfold e_rngs. rewrite a_ext_sub, map_map. apply map_ext. intros p. unfold ppsubst. cbn [fst snd]. rewrite !uE_sub. reflexivity. }
  split; intros H.
  - apply (lv_inv_mono E (ecomp E σ) (asubst σ a) a m0 m0); [exact Hv | exact He | intros b z X; rewrite pden_sub; exact X | intros b z _ x _; reflexivity | exact H].
  - apply (lv_inv_mono (ecomp E σ) E a (asubst σ a) m0 m0); [intros i; symmetry; exact (Hv i) | symmetry; exact He | intros b z X; rewrite <- pden_sub; exact X | intros b z _ x _; reflexivity | exact H].
Qed.

Theorem HA_subst : forall E σ M a m0, ag_ok M a = true -> HA E (msubst σ M) (asubst σ a) m0 -> HA (ecomp E σ) M a m0.
Proof.
  intros E σ M a m0 Hag H Hon. specialize (H Hon). destruct H as [Hdep Hown Hownx Hhi _ _ Hpri].
  assert (E1 : dD1 (ecomp E σ) a = dD1 E (asubst σ a)) by (unfold dD1, asubst, ppsubst; cbn [a_dep fst]; apply uE_sub).
  assert (E2 : dB1 (ecomp E σ) a = dB1 E (asubst σ a)) by (unfold dB1, asubst, ppsubst; cbn [a_dep snd]; apply uE_sub).
  assert (E0 : uE (ecomp E σ) (a_nl a) = uE E (a_nl (asubst σ a))) by (unfold asubst; cbn [a_nl]; apply uE_sub).
  unfold ag_ok in Hag. apply andb_prop in Hag as [Hag Hgp]. apply andb_prop in Hag as [Hag Hao]. apply andb_prop in Hag as [Hg1 Hg2]. apply (list_eqb_eq pair_eqb pair_eqb_eq) in Hao.
  constructor; rewrite ?E1, ?E2, ?E0.
  - exact Hdep.
  - intros x Hx Hdw. apply own_pt_sub. exact (Hown x Hx Hdw).
  - exact Hao.
  - exact Hhi.
  - exact (gent_in _ _ _ Hg1).
  - exact (gent_in _ _ _ Hg2).
  - intros Hne. destruct (Hpri (proj2 (pri_nil_sub σ a) Hne)) as [Hi Hox _ _ Hz Hs Hxt Hlv Hsd].
    assert (Hgp' : existsb (gent_b (p_pg a) PG_SIZE) (sm_maps M) = true /\ existsb (gent_b (p_tg a) TG_SIZE) (sm_maps M) = true).
    { destruct (a_pri a); [exfalso; apply Hne; reflexivity|]. apply andb_prop in Hgp. exact Hgp. }
    constructor.
    + unfold INV_A. rewrite pden_sub. exact Hi.
    + intros x Hx Hf. apply own_pt_sub. apply (Hox x Hx). unfold pri_foot in *. rewrite <- pden_sub. exact Hf.
    + exact (gent_in _ _ _ (proj1 Hgp')).
    + exact (gent_in _ _ _ (proj2 Hgp')).
    + intros x Hx. apply Hz. unfold pri_shadow in *. rewrite <- pden_sub. exact Hx.
    + intros p Hp. rewrite pden_sub. pose proof (Hs (ppsubst σ p) ltac:(unfold asubst; cbn [a_live]; apply in_map; exact Hp)) as X.
      unfold ppsubst in X. cbn [fst snd] in X. rewrite <- !uE_sub in X. exact X.
    + intros p Hp. rewrite pden_sub. pose proof (Hxt (ppsubst σ p) ltac:(rewrite a_ext_sub; apply in_map; exact Hp)) as X.
      unfold ppsubst in X. cbn [fst snd] in X. rewrite <- !uE_sub in X. exact X.
    + exact (proj1 (lv_inv_sub E σ a m0) Hlv).
    + intros p Hp x Hx. pose proof (Hsd (ppsubst σ p) ltac:(unfold asubst; cbn [a_live]; apply in_map; exact Hp) x) as X.
      unfold ppsubst in X. cbn [fst snd] in X. rewrite <- !uE_sub in X. rewrite E1, E2. exact (X Hx).
Qed.

(* [comment removed for export] *)
Lemma asubst_on : forall σ a, a_on (asubst σ a) = a_on a.
Proof. reflexivity. Qed.
Lemma asubst_nl : forall σ a, a_nl (asubst σ a) = lsubst σ (a_nl a).
Proof. reflexivity. Qed.
