(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run Fs.
From OssFuzzTheorems.Proofs.openssl.ct.lib.AS Require Import AsanAcct.

From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout RT_iface RT_state RT_main_shape.
From OssFuzzTheorems.Proofs.openssl.ct.lib.VCommon Require Import FastWord.
From OssFuzzTheorems.Proofs.openssl.ct.lib.VCommon.Ax Require Import ExTrie AxLazy AxLin AxVal AxMem AxZZ AxState AxSys AxAcct AxMeasure AxEntryRel AxFd AxModelRel.
From OssFuzzTheorems.Proofs.openssl.ct.lib.AxA Require Import AxExportM AxExportH FinMain1 FinMain2.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtAxA Require Import AxExportS AxExportF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
#[local] Arguments Uint63Axioms.to_Z : simpl never.
#[local] Arguments Uint63Axioms.of_Z : simpl never.

(* [comment removed for export] *)
Fixpoint contig (l : list (Z * Z)) (cur hi : Z) : bool :=
  match l with
  | [] => cur =? hi
  | q :: r => (fst q =? cur) &&& (0 <? snd q) &&& contig r (fst q + snd q) hi
  end.

Lemma contig_out (b n lo : Z) : 0 < n -> forall (l : list (Z * Z)) (cur hi : Z), contig l cur hi = true ->
  (forall q, In q l -> b + n <= fst q \/ fst q + snd q <= b) -> (b + n <= lo \/ cur <= b) -> b + n <= lo \/ hi <= b.
Proof.
  intros Hn. induction l as [|q r IH]; intros cur hi H Hd Hinv; cbn [contig] in H.
  - apply Z.eqb_eq in H. subst hi. exact Hinv.
  - apply land_true in H as [H H3]. apply land_true in H as [H1 H2]. apply Z.eqb_eq in H1. apply Z.ltb_lt in H2.
    apply (IH _ _ H3); [intros q' Hq'; apply Hd; right; exact Hq'|].
    destruct (Hd q (or_introl eq_refl)) as [D|D]; [|right; exact D]. destruct Hinv as [I|I]; [left; exact I | lia].
Qed.

(* [comment removed for export] *)
Definition alk (k : Z) (f : lin) : bool := (fst f mod k =? 0) &&& forallb (fun t => snd t mod k =? 0) (snd f).

Lemma alk_sound (ρ : valuation) (k : Z) (f : lin) : 0 < k -> alk k f = true -> leval ρ f mod k = 0.
Proof.
  intros Hk H. apply land_true in H as [H1 H2]. apply Z.eqb_eq in H1. unfold leval.
  assert (Ht : teval ρ (snd f) mod k = 0).
  { clear H1. induction (snd f) as [|[x a] r IH]; [apply Z.mod_0_l; lia|]. cbn [forallb snd] in H2. apply andb_prop in H2 as [A1 A2].
    apply Z.eqb_eq in A1. cbn [teval]. rewrite Z.add_mod, (IH A2), Z.add_0_r, Z.mod_mod by lia.
    rewrite Z.mul_mod, A1 by lia. rewrite Z.mul_0_l. apply Z.mod_0_l. lia. }
  rewrite Z.add_mod, H1, Ht by lia. reflexivity.
Qed.

Section Layout.
Hypothesis Hlow : segs_low ctasegs.
Variable fs0 : Fs.Fs.
Variable LIM : Z.
Variable ρ : valuation.
Variable B : AST.
Variable ms : machine_state.
Variable model : Model.
Hypothesis HR : R ctasegs amodel (MR ctasegs fs0 ρ) LIM ρ B (mkCfg ms model).
Variable W : list (lin * Z).
Variable J : Z.
Variable F : bforms.

Local Notation L := (Lm ρ W J F (vm_maps (m_vmmaps model))).
Let HM : MR ctasegs fs0 ρ (a_model B) model := r_model _ _ _ _ _ _ _ HR.
Let Hsat : sat ρ (a_facts B) := r_sat _ _ _ _ _ _ _ HR.

(* [comment removed for export] *)
Variable RES : list (Z * Z).
Hypothesis HRES : map (fun q : word * word => (bv_unsigned (fst q), bv_unsigned (snd q))) (segments_reserved ctasegs) = RES.
Hypothesis Hcontig : match RES with q :: r => (fst q =? 0x10000) &&& (0 <? snd q) &&& contig r (fst q + snd q) SEGTOP_A | [] => false end = true.

Definition grants : list (lin * Z) :=
  [ (bf_PRB F, 0x2000011000); (bf_PAB F, 0x800000); (bf_T F, 4096); (bf_TCX F, 0x10000); (bf_DTV F, 4096); (bf_FSB F, 0xb09000);
    (bf_DNB F, 0x100000); (bf_SSB F, 0x800000) ].

Definition find_ent (g : lin * Z) : bool :=
  existsb (fun e => lin_eqb (ae_base e) (fst g) &&& (ae_size e =? snd g) &&& var_ent e) (am_maps (a_model B)).

Fixpoint forms_distinct (l : list (lin * Z)) : bool :=
  match l with [] => true | g :: r => forallb (fun h => negb (lin_eqb (fst g) (fst h))) r &&& forms_distinct r end.

Definition in_rng (f : lin) (lo hi : Z) : bool :=
  match lrange (a_facts B) f with Some (l, h) => (lo <=? l) &&& (h <=? hi) | None => false end.

Lemma in_rng_sound (f : lin) (lo hi : Z) : in_rng f lo hi = true -> lo <= leval ρ f <= hi.
Proof.
  unfold in_rng. destruct (lrange (a_facts B) f) as [[l h]|] eqn:E; [|discriminate]. intros H. apply land_true in H as [H1 H2].
  apply Z.leb_le in H1. apply Z.leb_le in H2. pose proof (lrange_sound ρ _ _ Hsat _ E) as X. cbn [fst snd] in X. lia.
Qed.

Definition lay_ok : bool :=
  forallb (fun g => find_ent g &&& alk 4096 (fst g)) grants &&& forms_distinct grants
  &&& am_shadow (a_model B)
  &&& lin_eqb (am_atop (a_model B)) (laddc (bf_sp0 F) (- 8388608))
  &&& lin_eqb (bf_sp0 F) (0, sp_terms) &&& existsb is_entry (a_mem B)
  &&& alk 4096 (bf_top F) &&& in_rng (lsub (bf_top F) (bf_sp0 F)) (- 160) (- 160 + 4095)
  &&& alk 65536 (bf_SB F) &&& in_rng (lsub (bf_SB F) (bf_PRB F)) 0 65536
  &&& ((bf_f0 F =? 2) ||| (bf_f0 F =? 3)) &&& in_rng (bf_tid F) 1 2147483647
  &&& (Z.of_nat (length (am_maps (a_model B))) <=? 64) &&& (ents_total (am_maps (a_model B)) <=? 35184372088832)
  &&& forallb w_ok W &&& (0 <=? J) &&& (J mod 4096 =? 0) &&& (J + wins_bytes W <=? 68719476736).


Lemma find_ent_sound (g : lin * Z) : find_ent g = true ->
  exists e, In e (am_maps (a_model B)) /\ ae_base e = fst g /\ ae_size e = snd g /\ var_ent e = true.
Proof.
  unfold find_ent. intros H. apply existsb_exists in H as [e [He Hb]]. apply land_true in Hb as [Hb H3]. apply land_true in Hb as [H1 H2].
  exists e. split; [exact He|]. split; [exact (lin_eqb_eq _ _ H1)|]. split; [apply Z.eqb_eq; exact H2 | exact H3].
Qed.

(* [comment removed for export] *)
Lemma ent_disj (l : list aent) : pw_disj (map (ent_val ρ) l) -> forall e1 e2, In e1 l -> In e2 l ->
  e1 = e2 \/ bas (ent_val ρ e1) + bsz (ent_val ρ e1) <= bas (ent_val ρ e2) \/ bas (ent_val ρ e2) + bsz (ent_val ρ e2) <= bas (ent_val ρ e1).
Proof.
  induction l as [|p r IH]; intros Hpw e1 e2 H1 H2; [destruct H1|]. cbn [map] in Hpw. destruct (pw_disj_inv _ _ Hpw) as [Hd Hr].
  destruct H1 as [<-|H1]; destruct H2 as [<-|H2].
  - left. reflexivity.
  - right. pose proof (Hd (ent_val ρ e2) (in_map _ _ _ H2)) as D. unfold iv_disj in D. lia.
  - right. pose proof (Hd (ent_val ρ e1) (in_map _ _ _ H1)) as D. unfold iv_disj in D. lia.
  - exact (IH Hr e1 e2 H1 H2).
Qed.

Lemma apart_of (g1 g2 : lin * Z) : find_ent g1 = true -> find_ent g2 = true -> lin_eqb (fst g1) (fst g2) = false ->
  apart (leval ρ (fst g1)) (snd g1) (leval ρ (fst g2)) (snd g2).
Proof.
  intros F1 F2 Hne. destruct (find_ent_sound g1 F1) as (e1 & I1 & B1 & S1 & _). destruct (find_ent_sound g2 F2) as (e2 & I2 & B2 & S2 & _).
  pose proof (mr_pw ctasegs fs0 ρ _ model HM) as Hpw. rewrite (mr_maps ctasegs fs0 ρ _ model HM) in Hpw.
  pose proof (MR_ent ctasegs fs0 ρ _ model e1 HM I1) as O1. pose proof (MR_ent ctasegs fs0 ρ _ model e2 HM I2) as O2.
  destruct (ent_disj _ Hpw e1 e2 I1 I2) as [E|D].
  - exfalso. subst e2. rewrite <- B1, <- B2, lin_eqb_refl in Hne. discriminate Hne.
  - rewrite !(ent_val_bas ρ _ O1), !(ent_val_bsz ρ _ O1), !(ent_val_bas ρ _ O2), !(ent_val_bsz ρ _ O2) in D.
    unfold apart. rewrite <- B1, <- B2, <- S1, <- S2. lia.
Qed.

Lemma fop_grants (gl : list (lin * Z)) : forallb find_ent gl = true -> forms_distinct gl = true ->
  ForallOrdPairs (fun a b : Z * Z => apart (fst a) (snd a) (fst b) (snd b)) (map (fun g => (leval ρ (fst g), snd g)) gl).
Proof.
  induction gl as [|g r IH]; intros Hf Hd; cbn [map]; [constructor|]. cbn [forallb] in Hf. apply andb_prop in Hf as [F1 F2].
  cbn [forms_distinct] in Hd. apply land_true in Hd as [D1 D2]. constructor; [|exact (IH F2 D2)].
  apply Forall_forall. intros q Hq. apply in_map_iff in Hq as [h [<- Hh]]. cbn [fst snd].
  rewrite forallb_forall in D1, F2. apply (apart_of g h F1 (F2 h Hh)). apply negb_true_iff. exact (D1 h Hh).
Qed.

Lemma fop_nth {X : Type} (P : X -> X -> Prop) (l : list X) : ForallOrdPairs P l ->
  forall i j x y, (i < j)%nat -> nth_error l i = Some x -> nth_error l j = Some y -> P x y.
Proof.
  induction 1 as [|a r Ha Hr IH]; intros i j x y Hij Hi Hj; [destruct i; discriminate|].
  destruct j as [|j]; [lia|]. cbn [nth_error] in Hj. destruct i as [|i]; cbn [nth_error] in Hi.
  - injection Hi as <-. exact (proj1 (Forall_forall _ _) Ha y (nth_error_In _ _ Hj)).
  - exact (IH i j x y ltac:(lia) Hi Hj).
Qed.

(* [comment removed for export] *)
Lemma grant_facts (g : lin * Z) : find_ent g = true -> alk 4096 (fst g) = true -> am_shadow (a_model B) = true ->
  leval ρ (am_atop (a_model B)) = l_ACEIL L -> grant_ok L (leval ρ (fst g)) (snd g).
Proof.
  intros Hf Hal Hsh Hat. destruct (find_ent_sound g Hf) as (e & He & Eb & Es & Hv).
  pose proof (MR_ent ctasegs fs0 ρ _ model e HM He) as (O1 & O2 & O3). rewrite Eb, Es in *.
  pose proof (MR_ent_in ctasegs fs0 ρ _ model e HM He) as HIn.
  pose proof (mr_top ctasegs fs0 ρ _ model HM _ HIn) as Ht.
  rewrite (ent_val_bas ρ e (MR_ent ctasegs fs0 ρ _ model e HM He)), (ent_val_bsz ρ e (MR_ent ctasegs fs0 ρ _ model e HM He)),
          (mr_atop ctasegs fs0 ρ _ model HM), Eb, Es, Hat in Ht.
  pose proof (mr_span ctasegs fs0 ρ _ model HM Hsh e He Hv) as Hs. rewrite Eb, Es in Hs.
  unfold grant_ok. split; [exact O1|]. split; [exact (alk_sound ρ 4096 _ ltac:(lia) Hal)|]. split; [exact Ht|].
  split; [unfold K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi, sh_lo, sh_hi in *; exact Hs|].
  (* [comment removed for export] *)
  assert (Hdq : forall q, In q RES -> leval ρ (fst g) + snd g <= fst q \/ fst q + snd q <= leval ρ (fst g)).
  { intros q Hq. rewrite <- HRES in Hq. apply in_map_iff in Hq as [q0 [<- Hq0]]. cbn [fst snd].
    rewrite <- (mr_res ctasegs fs0 ρ _ model HM) in Hq0. pose proof (mr_disj ctasegs fs0 ρ _ model HM _ q0 HIn Hq0) as D.
    rewrite (ent_val_bas ρ e (MR_ent ctasegs fs0 ρ _ model e HM He)), (ent_val_bsz ρ e (MR_ent ctasegs fs0 ρ _ model e HM He)), Eb, Es in D.
    unfold iv_disj, bas, bsz in D. lia. }
  destruct RES as [|q0 r]; [discriminate Hcontig|]. apply land_true in Hcontig as [Hc H3]. apply land_true in Hc as [H1 H2].
  apply Z.eqb_eq in H1. apply Z.ltb_lt in H2.
  apply (contig_out (leval ρ (fst g)) (snd g) 0x10000 O2 r _ _ H3); [intros q Hq; apply Hdq; right; exact Hq|].
  destruct (Hdq q0 (or_introl eq_refl)) as [D|D]; [left; lia | right; exact D].
Qed.

Lemma lay_ok_parts : lay_ok = true -> existsb is_entry (a_mem B) = true /\ J + wins_bytes W <= 2 ^ 36.
Proof.
  unfold lay_ok. intros H.
  apply land_true in H as [H K18]. do 11 (apply land_true in H as [H _]). apply land_true in H as [_ K6].
  split; [exact K6|]. apply Z.leb_le in K18. change (2 ^ 36) with 68719476736. exact K18.
Qed.

(* [comment removed for export] *)
Lemma ex_eb_facts : existsb is_entry (a_mem B) = true -> eb_facts ρ.
Proof.
  intros H. apply existsb_exists in H as [Rq [HIn He]]. pose proof (r_mem _ _ _ _ _ _ _ HR) as [_ HF]. cbn [cfg_ms] in HF.
  pose proof (proj1 (Forall_forall _ _) HF Rq HIn) as HRq. unfold RRegion in HRq. unfold is_entry in He.
  destruct (rg_kind Rq); try discriminate He. exact (proj1 HRq).
Qed.

Theorem ex_layout_ok : lay_ok = true -> layout_ok L /\ leval ρ (am_atop (a_model B)) = l_ACEIL L /\ l_sp0 L = sp_val ρ /\ eb_facts ρ.
Proof.
  unfold lay_ok. intros H.
  apply land_true in H as [H K18]. apply land_true in H as [H K17]. apply land_true in H as [H K16]. apply land_true in H as [H K15].
  apply land_true in H as [H K14]. apply land_true in H as [H K13]. apply land_true in H as [H K12]. apply land_true in H as [H K11].
  apply land_true in H as [H K10]. apply land_true in H as [H K9]. apply land_true in H as [H K8]. apply land_true in H as [H K7].
  apply land_true in H as [H K6]. apply land_true in H as [H K5]. apply land_true in H as [H K4]. apply land_true in H as [H K3].
  apply land_true in H as [K1 K2].
  (* [comment removed for export] *)
  pose proof (lin_eqb_eq _ _ K4) as Eat. pose proof (lin_eqb_eq _ _ K5) as Esp. pose proof (ex_eb_facts K6) as Heb.
  assert (Esp0 : l_sp0 L = sp_val ρ).
  { unfold Lm, L_of. cbn [l_sp0]. rewrite Esp. unfold leval, sp_val. cbn [fst snd]. lia. }
  assert (Hat : leval ρ (am_atop (a_model B)) = l_ACEIL L).
  { rewrite Eat, leval_laddc. unfold l_ACEIL, STACK_WIN, Lm, L_of. cbn [l_sp0]. lia. }
  split; [|split; [exact Hat | split; [exact Esp0 | exact Heb]]].
  assert (Hgf : forallb find_ent grants = true /\ forallb (fun g => alk 4096 (fst g)) grants = true).
  { clear -K1. induction grants as [|g r IH]; [split; reflexivity|]. cbn [forallb] in *. apply andb_prop in K1 as [A1 A2].
    apply land_true in A1 as [A11 A12]. destruct (IH A2) as [I1 I2]. rewrite A11, A12, I1, I2. split; reflexivity. }
  destruct Hgf as [Hgf Hga].
  assert (HG : forall g, In g grants -> grant_ok L (leval ρ (fst g)) (snd g)).
  { intros g Hg. rewrite forallb_forall in Hgf, Hga. exact (grant_facts g (Hgf g Hg) (Hga g Hg) K3 Hat). }
  assert (PA : pairwise_apart (startup_grants L)).
  { intros i j g1 g2 Hij H1 H2. exact (fop_nth _ _ (fop_grants grants Hgf K2) i j g1 g2 Hij H1 H2). }
  destruct Heb as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hs1 & Hs2).
  pose proof (in_rng_sound _ _ _ K8) as Rtop. rewrite leval_lsub in Rtop.
  pose proof (in_rng_sound _ _ _ K10) as RSB. rewrite leval_lsub in RSB.
  pose proof (in_rng_sound _ _ _ K12) as Rtid.
  unfold layout_ok.
  assert (G := fun k g (E : nth_error grants k = Some g) => HG g (nth_error_In _ _ E)).
  split; [rewrite Esp0; pose proof (Zle_0_nat (length (eb_image (mkPhdrInfo 0 0 0) ρ))); lia|].
  split; [rewrite Esp0; unfold sp_val, sp_terms; cbn [teval]; rewrite Z.add_0_r;
          replace (16 * ρ v_x0 + (64 * ρ v_x1 + (4096 * ρ v_x2 + 32768 * ρ v_x3))) with ((ρ v_x0 + 4 * ρ v_x1 + 256 * ρ v_x2 + 2048 * ρ v_x3) * 16) by lia;
          apply Z_mod_mult|].
  split; [unfold Lm, L_of; cbn [l_sp0 l_top]; lia|].
  split; [unfold Lm, L_of; cbn [l_top]; exact (alk_sound ρ 4096 _ ltac:(lia) K7)|].
  split; [exact (G 0%nat _ eq_refl)|].
  split; [unfold Lm, L_of; cbn [l_SB]; exact (alk_sound ρ 65536 _ ltac:(lia) K9)|].
  split; [unfold Lm, L_of; cbn [l_SB l_PRB]; lia|].
  split; [exact (G 1%nat _ eq_refl)|]. split; [exact (G 2%nat _ eq_refl)|]. split; [exact (G 3%nat _ eq_refl)|].
  split; [exact (G 4%nat _ eq_refl)|]. split; [exact (G 5%nat _ eq_refl)|]. split; [exact (G 6%nat _ eq_refl)|].
  split; [exact (G 7%nat _ eq_refl)|].
  split; [exact (PA 0%nat 1%nat _ _ ltac:(lia) eq_refl eq_refl)|]. split; [exact (PA 0%nat 2%nat _ _ ltac:(lia) eq_refl eq_refl)|].
  split; [exact (PA 0%nat 3%nat _ _ ltac:(lia) eq_refl eq_refl)|]. split; [exact (PA 0%nat 5%nat _ _ ltac:(lia) eq_refl eq_refl)|].
  split; [exact (PA 0%nat 6%nat _ _ ltac:(lia) eq_refl eq_refl)|]. split; [exact (PA 0%nat 7%nat _ _ ltac:(lia) eq_refl eq_refl)|].
  split; [exact (PA 2%nat 3%nat _ _ ltac:(lia) eq_refl eq_refl)|]. split; [exact (PA 2%nat 5%nat _ _ ltac:(lia) eq_refl eq_refl)|].
  split; [exact (PA 3%nat 5%nat _ _ ltac:(lia) eq_refl eq_refl)|]. split; [exact (PA 1%nat 5%nat _ _ ltac:(lia) eq_refl eq_refl)|].
  split; [unfold Lm, L_of; cbn [l_f0]; apply lor_true in K11 as [X|X]; apply Z.eqb_eq in X; [left | right]; exact X|].
  split; [unfold Lm, L_of; cbn [l_tid]; lia|].
  apply Z.leb_le in K16. apply Z.eqb_eq in K17. apply Z.leb_le in K18.
  split; [unfold Lm, L_of; cbn [l_al0]; exact (A_wf_A' ρ W J K16 K17 K15)|].
  split; [unfold Lm, L_of; cbn [l_al0]; unfold A'; cbn [A_bytes fst snd]; pose proof (hull_bytes ρ W K15); lia|].
  split; [exact (PA 6%nat 7%nat _ _ ltac:(lia) eq_refl eq_refl)|].
  split; [|exact PA].
  (* [comment removed for export] *)
  assert (ESG : startup_grants L = map (fun g => (leval ρ (fst g), snd g)) grants) by reflexivity.
  unfold maps0_ok. rewrite ESG. change (l_maps0 L) with (vm_maps (m_vmmaps model)).
  split; [|split; [|split]].
  - apply Forall_app. split.
    + apply Forall_forall. intros q Hq.
      apply in_map_iff in Hq as [g [<- Hg]]. cbn [fst snd]. rewrite forallb_forall in Hgf.
      destruct (find_ent_sound g (Hgf g Hg)) as (e & He & Eb & Es & _). rewrite <- Eb, <- Es.
      exact (MR_ent_in ctasegs fs0 ρ _ model e HM He).
    + destruct (mr_shadow ctasegs fs0 ρ _ model HM K3) as (S1 & S2 & S3).
      repeat constructor; cbn [fst snd].
      * exact (MR_ent_in ctasegs fs0 ρ _ model _ HM S1).
      * exact (MR_ent_in ctasegs fs0 ρ _ model _ HM S2).
      * exact (MR_ent_in ctasegs fs0 ρ _ model _ HM S3).
  - rewrite (mr_maps ctasegs fs0 ρ _ model HM), length_map. apply Z.leb_le. exact K13.
  - rewrite (mr_maps ctasegs fs0 ρ _ model HM), (MR_live ρ _ (mr_ents ctasegs fs0 ρ _ model HM)). apply Z.leb_le in K14.
    change (2 ^ 45) with 35184372088832. exact K14.
  - exact (ex_maps_pos ctasegs fs0 LIM ρ B ms model HR).
Qed.

End Layout.
