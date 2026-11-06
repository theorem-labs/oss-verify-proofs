(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Spec Require Import STree Malloc MallocCtrl KLedger JLedger
  MI_Tree MI_Inv MI_Kit MI_WFree2 MI_Ledger MI_WAMeta MI_Joint1.
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition jcoh (J : jled) (eG eC : ev) : Prop :=
  match eG, eC with
  | EMunmap aG _, EMunmap aC _ => jg_coherent aG aC (j_groups J)
  | EMprotect aG _ _, EMprotect aC _ _ => jm_coherent aG aC (j_metas J)
  | _, _ => True
  end.

Lemma projC_post_coh J eG eC zG zC : jev_rel J eG eC -> jcoh J eG eC -> same_class eG eC zG zC = true ->
  projC (jevent_post J eG eC zG zC) = event_post (projC J) eC zC.
Proof.
  intros HR HC CL. apply projC_post; [exact HR| exact CL| |].
  - intros aG aC len len' -> ->. exact HC.
  - intros aG aC len len' p p' -> ->. exact HC.
Qed.

Fixpoint jsim {R1 R2} (J : jled) (tG : M R1) (tC : M R2) (Post : jled -> R1 -> R2 -> Prop) {struct tG} : Prop :=
  match tG, tC with
  | SRet x, SRet y => Post J x y
  | SVis (EUndef _) _, SVis (EUndef _) _ => True
  | SVis eG kG, SVis eC kC =>
      jev_rel J eG eC /\ jcoh J eG eC /\
      forall zG zC, jans_ok J eG eC zG zC = true -> jsim (jevent_post J eG eC zG zC) (kG zG) (kC zC) Post
  | _, _ => False
  end.

Lemma jsim_ret {R1 R2} J (x : R1) (y : R2) Post : Post J x y -> jsim J (SRet x) (SRet y) Post.
Proof. intros H. exact H. Qed.

Lemma jsim_undef {R1 R2} J w w' (kG : Z -> M R1) (kC : Z -> M R2) Post : jsim J (SVis (EUndef w) kG) (SVis (EUndef w') kC) Post.
Proof. exact I. Qed.

Lemma jev_rel_not_undef J eG eC : jev_rel J eG eC -> is_undef eG = false /\ is_undef eC = false.
Proof. destruct eG, eC; cbn; intros H; try contradiction; auto. Qed.

Lemma jsim_vis {R1 R2} J eG eC (kG : Z -> M R1) (kC : Z -> M R2) Post :
  jev_rel J eG eC -> jcoh J eG eC ->
  (forall zG zC, jans_ok J eG eC zG zC = true -> jsim (jevent_post J eG eC zG zC) (kG zG) (kC zC) Post) ->
  jsim J (SVis eG kG) (SVis eC kC) Post.
Proof. intros HR HC HK. destruct eG, eC; cbn in HR; try contradiction; cbn; auto. Qed.

Lemma jsim_vis_inv {R1 R2} J eG eC (kG : Z -> M R1) (kC : Z -> M R2) Post :
  jsim J (SVis eG kG) (SVis eC kC) Post ->
  (is_undef eG = true /\ is_undef eC = true)
  \/ (jev_rel J eG eC /\ jcoh J eG eC /\ forall zG zC, jans_ok J eG eC zG zC = true -> jsim (jevent_post J eG eC zG zC) (kG zG) (kC zC) Post).
Proof. destruct eG, eC; cbn; intros H; try contradiction; auto. Qed.

Lemma jsim_mono {R1 R2} (Post Post' : jled -> R1 -> R2 -> Prop) :
  (forall J x y, Post J x y -> Post' J x y) -> forall tG tC J, jsim J tG tC Post -> jsim J tG tC Post'.
Proof.
  intros HP. induction tG as [x|eG kG IH]; intros tC J H; destruct tC as [y|eC kC]; cbn in H |- *; try contradiction.
  - apply HP. exact H.
  - destruct eG; try exact H.
  - apply jsim_vis_inv in H as [[UG UC]|(HR & HC & HK)].
    + destruct eG, eC; cbn in UG, UC; try discriminate. exact I.
    + apply jsim_vis; [exact HR| exact HC|]. intros zG zC Hz. apply IH. apply HK. exact Hz.
Qed.

Lemma jsim_steq {R1 R2} J (tG tG' : M R1) (tC tC' : M R2) Post :
  steq tG tG' -> steq tC tC' -> jsim J tG tC Post -> jsim J tG' tC' Post.
Proof.
  intros HG. revert J tC tC'. induction HG as [x|eG kG kG' HkG IH]; intros J tC tC' HC H; destruct HC as [y|eC kC kC' HkC].
  - exact H.
  - cbn in H. contradiction.
  - cbn in H. destruct eG; contradiction.
  - apply jsim_vis_inv in H as [[UG UC]|(HR & HC & HK)].
    + destruct eG, eC; cbn in UG, UC; try discriminate. exact I.
    + apply jsim_vis; [exact HR| exact HC|]. intros zG zC Hz. apply (IH zG _ (kC zC)). { apply HkC. } apply HK. exact Hz.
Qed.

Lemma jsim_bind {R1 R2 S1 S2} (tG : M R1) (tC : M R2) (f : R1 -> M S1) (g : R2 -> M S2) Post Q J :
  jsim J tG tC Post -> (forall J' x y, Post J' x y -> jsim J' (f x) (g y) Q) -> jsim J (sbind tG f) (sbind tC g) Q.
Proof.
  revert J tC. induction tG as [x|eG kG IH]; intros J tC H Hf; destruct tC as [y|eC kC]; cbn [sbind] in *; try (cbn in H; contradiction).
  - apply Hf. exact H.
  - cbn in H. destruct eG; contradiction.
  - apply jsim_vis_inv in H as [[UG UC]|(HR & HC & HK)].
    + destruct eG, eC; cbn in UG, UC; try discriminate. exact I.
    + apply jsim_vis; [exact HR| exact HC|]. intros zG zC Hz. apply IH; [apply HK; exact Hz| exact Hf].
Qed.

Lemma jsim_jtree_ok {R1 R2} (tG : M R1) : forall (tC : M R2) J Post PG Post2,
  jsim J tG tC Post -> ptree (projG J) tG PG ->
  (forall J' x y, Post J' x y -> PG (projG J') x -> Post2 J' x y) ->
  jtree_ok J tG tC Post2.
Proof.
  induction tG as [x|eG kG IH]; intros tC J Post PG Post2 H PT HP; destruct tC as [y|eC kC]; cbn in H; try contradiction.
  - cbn. apply HP; [exact H| exact PT].
  - destruct eG; contradiction.
  - apply jsim_vis_inv in H as [[UG UC]|(HR & HC & HK)].
    + destruct eG; cbn in UG; try discriminate. cbn in PT. destruct PT.
    + cbn. split; [exact HR|]. intros zG zC Hz.
      assert (AG : answer_ok (projG J) eG zG = true) by exact (jans_ok_G _ _ _ _ _ Hz).
      apply (IH zG (kC zC) _ Post PG Post2); [apply HK; exact Hz| | exact HP].
      rewrite (projG_post J eG eC zG zC HR (jans_ok_class _ _ _ _ _ Hz)).
      destruct (jev_rel_not_undef _ _ _ HR) as [NU _].
      destruct eG; cbn in NU; try discriminate; cbn [ptree] in PT; destruct PT as [_ PT]; specialize (PT zG); rewrite AG in PT; exact PT.
Qed.

Lemma jsim_jcpath {R1 R2} (tG : M R1) : forall (tC : M R2) J Post J' x y,
  jsim J tG tC Post -> jcpath J tG tC J' x y -> Post J' x y.
Proof.
  induction tG as [x0|eG kG IH]; intros tC J Post J' x y H CP.
  - inversion CP; subst. cbn in H. exact H.
  - inversion CP; subst. apply jsim_vis_inv in H as [[UG UC]|(HR & HC & HK)].
    + destruct eG; cbn in UG; discriminate.
    + eapply IH; [apply HK; eassumption| eassumption].
Qed.

Lemma jcpath_cpath_G {R1 R2} (tG : M R1) : forall (tC : M R2) J J' x y Post,
  jsim J tG tC Post -> jcpath J tG tC J' x y -> cpath (projG J) tG (projG J') x.
Proof.
  induction tG as [x0|eG kG IH]; intros tC J J' x y Post H CP.
  - inversion CP; subst. constructor.
  - inversion CP; subst. apply jsim_vis_inv in H as [[UG UC]|(HR & HC & HK)].
    + destruct eG; cbn in UG; discriminate.
    + econstructor; [exact (jans_ok_G _ _ _ _ _ H3)|].
      rewrite <- (projG_post J eG eC zG zC HR (jans_ok_class _ _ _ _ _ H3)). eapply IH; [apply HK; exact H3| eassumption].
Qed.

Lemma jcpath_cpath_C {R1 R2} (tG : M R1) : forall (tC : M R2) J J' x y Post,
  jsim J tG tC Post -> jcpath J tG tC J' x y -> cpath (projC J) tC (projC J') y.
Proof.
  induction tG as [x0|eG kG IH]; intros tC J J' x y Post H CP.
  - inversion CP; subst. constructor.
  - inversion CP; subst. apply jsim_vis_inv in H as [[UG UC]|(HR & HC & HK)].
    + destruct eG; cbn in UG; discriminate.
    + econstructor; [exact (jans_ok_C _ _ _ _ _ H3)|].
      rewrite <- (projC_post_coh J eG eC zG zC HR HC (jans_ok_class _ _ _ _ _ H3)). eapply IH; [apply HK; exact H3| eassumption].
Qed.

Lemma jsim_bind_path {R1 R2 S1 S2} (tG : M R1) : forall (tC : M R2) (f : R1 -> M S1) (g : R2 -> M S2) Post Q J,
  jsim J tG tC Post ->
  (forall J' x y, Post J' x y -> jcpath J tG tC J' x y -> jsim J' (f x) (g y) Q) ->
  jsim J (sbind tG f) (sbind tC g) Q.
Proof.
  induction tG as [x|eG kG IH]; intros tC f g Post Q J H Hf; destruct tC as [y|eC kC]; cbn [sbind] in *; try (cbn in H; contradiction).
  - apply Hf; [exact H| constructor].
  - cbn in H. destruct eG; contradiction.
  - apply jsim_vis_inv in H as [[UG UC]|(HR & HC & HK)].
    + destruct eG, eC; cbn in UG, UC; try discriminate. exact I.
    + apply jsim_vis; [exact HR| exact HC|]. intros zG zC Hz. apply (IH zG (kC zC) f g Post Q); [apply HK; exact Hz|].
      intros J' x y HP CP. apply Hf; [exact HP|]. econstructor; [exact Hz| exact CP].
Qed.

Definition isG (kr : N * region) : bool := match r_kind (snd kr) with RKGroup => true | _ => false end.
Definition isM (kr : N * region) : bool := match r_kind (snd kr) with RKMeta => true | _ => false end.
Definition jG (rho : N -> Z) (kr : N * region) : Z * Z * Z := (r_base (snd kr), rho (fst kr), r_len (snd kr)).

Definition m3 (e : Z * Z * Z * Z) : Z * Z * Z := fst e.

Record JR (J : jled) (rho : N -> Z) (sG sC : mstate) : Prop := mkJR {
  jr_rc : RC rho (j_resvC J) (j_ceilC J) sG sC;
  jr_groups : Permutation (j_groups J) (map (jG rho) (List.filter isG (map_to_list (s_regions sG))));
  jr_metas : Permutation (map m3 (j_metas J)) (map (jG rho) (List.filter isM (map_to_list (s_regions sG))));
  jr_brkreg : forall bG bC l, j_brkreg J = Some (bG, bC, l) <->
      exists rid r, s_regions sG !! rid = Some r /\ r_kind r = RKBrk /\ r_base r = bG /\ rho rid = bC /\ r_len r = l;
  jr_brk : match c_brk (s_ctx sG) with
           | BrkUntried => j_brk J = JUntried | BrkLive _ _ => j_brk J = JLive | BrkDead => j_brk J = JDead end
}.

Lemma frontier_same st st' : c_avail_meta_areas (s_ctx st') = c_avail_meta_areas (s_ctx st) ->
  forall rid r, frontier st' rid r = frontier st rid r.
Proof. intros E rid r. unfold frontier. rewrite E. reflexivity. Qed.

Lemma JR_frame J rho sG sC sG' sC' : JR J rho sG sC ->
  s_regions sG' = s_regions sG -> c_brk (s_ctx sG') = c_brk (s_ctx sG) -> c_avail_meta_areas (s_ctx sG') = c_avail_meta_areas (s_ctx sG) ->
  RC rho (j_resvC J) (j_ceilC J) sG' sC' -> JR J rho sG' sC'.
Proof.
  intros [R1 R2 R3 R4 R5] ER EB EC RC'. constructor.
  - exact RC'.
  - rewrite ER. exact R2.
  - rewrite ER. exact R3.
  - rewrite ER. exact R4.
  - rewrite EB. exact R5.
Qed.

Lemma JR_reinv J rho sG sC sG' sC' XG X' : JR J rho sG sC -> inv_R XG sG (projG J) -> inv_R X' sG' (projG J) ->
  s_regions sG' = s_regions sG -> RC rho (j_resvC J) (j_ceilC J) sG' sC' -> JR J rho sG' sC'.
Proof.
  intros [R1 R2 R3 R4 R5] IR IR' ER RC'. constructor.
  - exact RC'.
  - rewrite ER. exact R2.
  - rewrite ER. exact R3.
  - rewrite ER. exact R4.
  - pose proof (ir_brk _ _ _ IR) as B. pose proof (ir_brk _ _ _ IR') as B'. cbn [ld_brk projG] in B, B'.
    destruct (c_brk (s_ctx sG)) as [| |q o]; destruct (c_brk (s_ctx sG')) as [| |q' o'];
      try exact R5; rewrite R5 in *; cbn in B, B';
      repeat match goal with H : _ /\ _ |- _ => destruct H end; congruence.
Qed.

Lemma JR_Jframe J J' rho sG sC : JR J rho sG sC ->
  j_resvC J' = j_resvC J -> j_groups J' = j_groups J -> j_metas J' = j_metas J -> j_brkreg J' = j_brkreg J -> j_brk J' = j_brk J ->
  j_ceilC J' = j_ceilC J ->
  JR J' rho sG sC.
Proof.
  intros [R1 R2 R3 R4 R5] E1 E2 E3 E4 E5 E6. constructor; rewrite ?E1, ?E2, ?E3, ?E4, ?E5, ?E6; auto.
Qed.

Lemma In_filter_mtl (F : N * region -> bool) st rid r :
  In (rid, r) (List.filter F (map_to_list (s_regions st))) <-> s_regions st !! rid = Some r /\ F (rid, r) = true.
Proof. rewrite filter_In, In_map_to_list_regions. tauto. Qed.

Lemma jr_group_in J rho sG sC rid r : JR J rho sG sC -> s_regions sG !! rid = Some r -> r_kind r = RKGroup ->
  In (r_base r, rho rid, r_len r) (j_groups J).
Proof.
  intros R Hr K. eapply Permutation_in; [apply Permutation_sym; exact (jr_groups _ _ _ _ R)|].
  apply in_map_iff. exists (rid, r). split; [reflexivity|]. apply In_filter_mtl. unfold isG. cbn. rewrite K. auto.
Qed.

Lemma jr_group_of J rho sG sC g : JR J rho sG sC -> In g (j_groups J) ->
  exists rid r, s_regions sG !! rid = Some r /\ r_kind r = RKGroup /\ g = (r_base r, rho rid, r_len r).
Proof.
  intros R Hg. pose proof (Permutation_in _ (jr_groups _ _ _ _ R) Hg) as H. apply in_map_iff in H as ([rid r] & <- & H).
  apply In_filter_mtl in H as [Hr K]. unfold isG in K. cbn in K. exists rid, r. split; [exact Hr|]. split; [destruct (r_kind r); try discriminate; reflexivity| reflexivity].
Qed.

Lemma jr_meta_in J rho sG sC rid r : JR J rho sG sC -> s_regions sG !! rid = Some r -> r_kind r = RKMeta ->
  exists k, In (r_base r, rho rid, r_len r, k) (j_metas J).
Proof.
  intros R Hr K.
  assert (H : In (r_base r, rho rid, r_len r) (map m3 (j_metas J))).
  { eapply Permutation_in; [apply Permutation_sym; exact (jr_metas _ _ _ _ R)|].
    apply in_map_iff. exists (rid, r). split; [reflexivity|]. apply In_filter_mtl. unfold isM. cbn. rewrite K. auto. }
  apply in_map_iff in H as ([[[bG bC] l] k] & E & Hin). unfold m3 in E. cbn in E. inversion E. subst. exists k. exact Hin.
Qed.

Lemma jr_meta_of J rho sG sC e : JR J rho sG sC -> In e (j_metas J) ->
  exists rid r, s_regions sG !! rid = Some r /\ r_kind r = RKMeta /\ m3 e = (r_base r, rho rid, r_len r).
Proof.
  intros R He. pose proof (Permutation_in _ (jr_metas _ _ _ _ R) (in_map m3 _ _ He)) as H. apply in_map_iff in H as ([rid r] & E & H).
  apply In_filter_mtl in H as [Hr K]. unfold isM in K. cbn in K. exists rid, r. split; [exact Hr|]. split; [destruct (r_kind r); try discriminate; reflexivity| symmetry; exact E].
Qed.

Section DISTINCT.
Variables (XG XC : extras) (LG LC : mled) (rho : N -> Z) (resv : list (Z * Z)) (ceil : Z) (sG sC : mstate).
Hypothesis IRG : inv_R XG sG LG.
Hypothesis IRC : inv_R XC sC LC.
Hypothesis HRC : RC rho resv ceil sG sC.

#[using="XG LG IRG"] Lemma baseG_inj rid1 rid2 r1 r2 : s_regions sG !! rid1 = Some r1 -> s_regions sG !! rid2 = Some r2 ->
  r_kind r1 <> RKBrk -> r_kind r2 <> RKBrk -> r_base r1 = r_base r2 -> rid1 = rid2.
Proof.
  intros H1 H2 K1 K2 E. destruct (N.eq_dec rid1 rid2) as [->|NE]; [reflexivity|]. exfalso.
  pose proof (ir_disj _ _ _ IRG _ _ _ _ H1 H2 NE) as D. unfold region_live_range in D.
  destruct (ir_shape _ _ _ IRG _ _ H1) as (_ & _ & L1 & _). destruct (ir_shape _ _ _ IRG _ _ H2) as (_ & _ & L2 & _).
  pose proof (MI_WFree2.round_up_ge (r_len r1)). pose proof (MI_WFree2.round_up_ge (r_len r2)).
  destruct (r_kind r1); [congruence| |]; destruct (r_kind r2); try congruence; cbn in D; lia.
Qed.

#[using="XC LC resv ceil sC IRC HRC"] Lemma baseC_inj rid1 rid2 r1 r2 : s_regions sG !! rid1 = Some r1 -> s_regions sG !! rid2 = Some r2 ->
  r_kind r1 <> RKBrk -> r_kind r2 <> RKBrk -> rho rid1 = rho rid2 -> rid1 = rid2.
Proof.
  intros H1 H2 K1 K2 E. destruct (N.eq_dec rid1 rid2) as [->|NE]; [reflexivity|]. exfalso.
  pose proof (RC_region rho resv ceil sG sC rid1 HRC) as C1. rewrite H1 in C1. cbn in C1.
  pose proof (RC_region rho resv ceil sG sC rid2 HRC) as C2. rewrite H2 in C2. cbn in C2.
  pose proof (ir_disj _ _ _ IRC _ _ _ _ C1 C2 NE) as D. unfold region_live_range, rebase_region in D. cbn in D.
  destruct (ir_shape _ _ _ IRC _ _ C1) as (_ & _ & L1 & _). destruct (ir_shape _ _ _ IRC _ _ C2) as (_ & _ & L2 & _). cbn in L1, L2.
  pose proof (MI_WFree2.round_up_ge (r_len r1)). pose proof (MI_WFree2.round_up_ge (r_len r2)).
  destruct (r_kind r1); [congruence| |]; destruct (r_kind r2); try congruence; cbn in D; lia.
Qed.

#[using="XG LG IRG"] Lemma pointG_inj rid1 rid2 r1 r2 d1 d2 : s_regions sG !! rid1 = Some r1 -> s_regions sG !! rid2 = Some r2 ->
  r_kind r1 <> RKBrk -> r_kind r2 <> RKBrk -> 0 < d1 <= r_len r1 -> 0 < d2 <= r_len r2 ->
  r_base r1 + d1 = r_base r2 + d2 -> rid1 = rid2.
Proof.
  intros H1 H2 K1 K2 D1 D2 E. destruct (N.eq_dec rid1 rid2) as [->|NE]; [reflexivity|]. exfalso.
  pose proof (ir_disj _ _ _ IRG _ _ _ _ H1 H2 NE) as D. unfold region_live_range in D.
  pose proof (MI_WFree2.round_up_ge (r_len r1)). pose proof (MI_WFree2.round_up_ge (r_len r2)).
  destruct (r_kind r1); [congruence| |]; destruct (r_kind r2); try congruence; cbn in D; lia.
Qed.

#[using="XC LC resv ceil sC IRC HRC"] Lemma pointC_inj rid1 rid2 r1 r2 d1 d2 : s_regions sG !! rid1 = Some r1 -> s_regions sG !! rid2 = Some r2 ->
  r_kind r1 <> RKBrk -> r_kind r2 <> RKBrk -> 0 < d1 <= r_len r1 -> 0 < d2 <= r_len r2 ->
  rho rid1 + d1 = rho rid2 + d2 -> rid1 = rid2.
Proof.
  intros H1 H2 K1 K2 D1 D2 E. destruct (N.eq_dec rid1 rid2) as [->|NE]; [reflexivity|]. exfalso.
  pose proof (RC_region rho resv ceil sG sC rid1 HRC) as C1. rewrite H1 in C1. cbn in C1.
  pose proof (RC_region rho resv ceil sG sC rid2 HRC) as C2. rewrite H2 in C2. cbn in C2.
  pose proof (ir_disj _ _ _ IRC _ _ _ _ C1 C2 NE) as D. unfold region_live_range, rebase_region in D. cbn in D.
  pose proof (MI_WFree2.round_up_ge (r_len r1)). pose proof (MI_WFree2.round_up_ge (r_len r2)).
  destruct (r_kind r1); [congruence| |]; destruct (r_kind r2); try congruence; cbn in D; lia.
Qed.
End DISTINCT.

Lemma map_jG_ext rho rho' l : (forall kr, In kr l -> rho' (fst kr) = rho (fst kr)) -> map (jG rho') l = map (jG rho) l.
Proof. intros H. apply map_ext_in. intros kr Hk. unfold jG. rewrite (H kr Hk). reflexivity. Qed.

Lemma next_rid_fresh X st L : inv_R X st L -> s_regions st !! s_next_rid st = None.
Proof.
  intros IR. destruct (s_regions st !! s_next_rid st) as [r|] eqn:E; [| reflexivity]. exfalso.
  pose proof (ir_ids _ _ _ IR _ _ E). lia.
Qed.

Lemma nupd_other rho rid b q : q <> rid -> nupd rho rid b q = rho q.
Proof. intros NE. unfold nupd. destruct (N.eqb_spec q rid); [congruence| reflexivity]. Qed.
Lemma nupd_same rho rid b : nupd rho rid b rid = b.
Proof. unfold nupd. rewrite N.eqb_refl. reflexivity. Qed.

Lemma JR_new_group J rho sG sC zG zC len XG LG :
  JR J rho sG sC -> inv_R XG sG LG ->
  JR (jset_groups ((zG, zC, len) :: j_groups J) J) (nupd rho (s_next_rid sG) zC)
     (fst (new_region RKGroup zG len sG)) (fst (new_region RKGroup zC len sC)).
Proof.
  intros R IRG. pose proof R as [R1 R2 R3 R4 R5]. set (rid := s_next_rid sG).
  pose proof (next_rid_fresh _ _ _ IRG) as FR. fold rid in FR.
  assert (OLD : forall kr, In kr (map_to_list (s_regions sG)) -> fst kr <> rid).
  { intros [q rq] Hin E. cbn in E. subst q. apply In_map_to_list_regions in Hin. rewrite FR in Hin. discriminate. }
  constructor.
  - cbn. exact (proj1 (RC_new_region rho (j_resvC J) (j_ceilC J) RKGroup zG zC len sG sC R1)).
  - cbn. fold rid.
    eapply Permutation_trans; [| apply Permutation_map; apply Permutation_sym; apply (regions_insert_perm sG rid _ isG FR)].
    cbn. unfold jG at 1. cbn. rewrite nupd_same. apply perm_skip.
    rewrite (map_jG_ext rho); [exact R2|]. intros kr Hk. apply filter_In in Hk as [Hk _]. apply nupd_other. exact (OLD kr Hk).
  - cbn. fold rid.
    eapply Permutation_trans; [| apply Permutation_map; apply Permutation_sym; apply (regions_insert_perm sG rid _ isM FR)].
    cbn. rewrite (map_jG_ext rho); [exact R3|]. intros kr Hk. apply filter_In in Hk as [Hk _]. apply nupd_other. exact (OLD kr Hk).
  - cbn. intros bG bC l. rewrite R4. split; intros (q & rq & Hq & K & E1 & E2 & E3); exists q, rq.
    + rewrite lookup_new_region. fold rid. destruct (N.eqb_spec q rid) as [->|NE]; [rewrite FR in Hq; discriminate|]. rewrite nupd_other by exact NE. auto 10.
    + rewrite lookup_new_region in Hq. fold rid in Hq. destruct (N.eqb_spec q rid) as [->|NE]; [inversion Hq; subst; discriminate|]. rewrite nupd_other in E2 by exact NE. auto 10.
  - cbn. exact R5.
Qed.

Lemma jg_remove_notin aG l : (forall y, In y l -> fst (fst y) <> aG) -> jg_remove aG l = l.
Proof.
  induction l as [|y l IH]; intros H; cbn; [reflexivity|].
  destruct (Z.eqb_spec (fst (fst y)) aG) as [E|NE]; [exfalso; exact (H y ltac:(left; reflexivity) E)|].
  f_equal. apply IH. intros y' Hy'. apply H. right. exact Hy'.
Qed.

Lemma jg_remove_perm x : forall l l', Permutation l (x :: l') ->
  (forall y, In y l -> fst (fst y) = fst (fst x) -> y = x) -> ~ In x l' ->
  Permutation (jg_remove (fst (fst x)) l) l'.
Proof.
  induction l as [|y l IH]; intros l' P U NI.
  - apply Permutation_nil_cons in P. destruct P.
  - cbn. destruct (Z.eqb_spec (fst (fst y)) (fst (fst x))) as [E|NE].
    + rewrite (U y ltac:(left; reflexivity) E) in P. exact (Permutation.Permutation_cons_inv P).
    + assert (Hy : In y l') by (pose proof (Permutation_in y P ltac:(left; reflexivity)) as [Hx|Hin]; [exfalso; apply NE; rewrite Hx; reflexivity| exact Hin]).
      apply in_split in Hy as (l1 & l2 & ->).
      assert (P2 : Permutation l (x :: l1 ++ l2)).
      { apply (@Permutation.Permutation_cons_inv _ l (x :: l1 ++ l2) y). eapply Permutation_trans; [exact P|].
        apply Permutation_sym. change (x :: l1 ++ y :: l2) with (x :: (l1 ++ y :: l2)). eapply Permutation_trans; [apply perm_swap|]. apply perm_skip. apply Permutation_middle. }
      eapply Permutation_trans; [| apply Permutation_middle]. apply perm_skip.
      apply IH; [exact P2| intros y' Hy'; apply U; right; exact Hy'|].
      intros Hin. apply NI. apply in_app_iff in Hin as [Hin|Hin]; apply in_app_iff; [left; exact Hin| right; right; exact Hin].
Qed.

Lemma JR_drop_group J rho sG sC rid r XG LG XC LC :
  JR J rho sG sC -> inv_R XG sG LG -> inv_R XC sC LC -> s_regions sG !! rid = Some r -> r_kind r = RKGroup ->
  JR (jset_groups (jg_remove (r_base r) (j_groups J)) J) rho (drop_region rid sG) (drop_region rid sC).
Proof.
  intros R IRG IRC Hr K. pose proof R as [R1 R2 R3 R4 R5].
  constructor.
  - cbn. apply RC_drop_region. exact R1.
  - cbn. pose proof (Permutation_trans R2 (Permutation_map (jG rho) (MI_WFree2.regions_delete_perm sG rid r isG Hr))) as P. cbn in P. unfold isG in P at 1. cbn in P. rewrite K in P. cbn in P.
    change (r_base r) with (fst (fst (jG rho (rid, r)))).
    apply (jg_remove_perm (jG rho (rid, r)) _ _ P).
    + intros y Hy E. destruct (jr_group_of _ _ _ _ y R Hy) as (q & rq & Hq & Kq & ->). unfold jG in E |- *. cbn in E |- *.
      pose proof (baseG_inj XG LG sG IRG q rid rq r Hq Hr ltac:(rewrite Kq; discriminate) ltac:(rewrite K; discriminate) E) as ->.
      rewrite Hr in Hq. inversion Hq. reflexivity.
    + intros Hin. apply in_map_iff in Hin as ([q rq] & E & Hin). apply filter_In in Hin as [Hin Kq]. unfold isG in Kq. cbn in Kq.
      assert (Hq : delete rid (s_regions sG) !! q = Some rq) by (apply elem_of_map_to_list; apply list_elem_of_In; exact Hin).
      destruct (N.eq_dec q rid) as [->|NE]; [rewrite lookup_delete_eq in Hq; discriminate|]. rewrite lookup_delete_ne in Hq by congruence.
      unfold jG in E. cbn in E. inversion E.
      exact (NE (baseG_inj XG LG sG IRG q rid rq r Hq Hr ltac:(destruct (r_kind rq); discriminate) ltac:(rewrite K; discriminate) ltac:(assumption))).
  - cbn. eapply Permutation_trans; [exact R3|].
    eapply Permutation_trans; [apply Permutation_map; apply (MI_WFree2.regions_delete_perm sG rid r isM Hr)|].
    cbn. unfold isM at 1. cbn. rewrite K. cbn. apply Permutation_refl.
  - cbn. intros bG bC l. rewrite R4. split; intros (q & rq & Hq & Kq & E1 & E2 & E3); exists q, rq.
    + rewrite lookup_delete_ne; [auto 10|]. intros ->. rewrite Hr in Hq. inversion Hq; subst. rewrite K in Kq. discriminate.
    + destruct (N.eq_dec rid q) as [->|NE]; [rewrite lookup_delete_eq in Hq; discriminate|]. rewrite lookup_delete_ne in Hq by exact NE. auto 10.
  - cbn. exact R5.
Qed.

Lemma regions_filter_perm (F : N * region -> bool) (m m' : gmap N region) :
  (forall q rq, F (q, rq) = true -> (m !! q = Some rq <-> m' !! q = Some rq)) ->
  Permutation (List.filter F (map_to_list m)) (List.filter F (map_to_list m')).
Proof.
  intros H. apply Permutation.NoDup_Permutation.
  - apply List.NoDup_filter. apply NoDup_ListNoDup. apply NoDup_map_to_list.
  - apply List.NoDup_filter. apply NoDup_ListNoDup. apply NoDup_map_to_list.
  - intros [q rq]. rewrite !filter_In. split; intros [Hin Fq]; (split; [| exact Fq]).
    + apply (proj1 (list_elem_of_In _ _)). apply elem_of_map_to_list. apply (proj1 (H q rq Fq)). apply elem_of_map_to_list. apply list_elem_of_In. exact Hin.
    + apply (proj1 (list_elem_of_In _ _)). apply elem_of_map_to_list. apply (proj2 (H q rq Fq)). apply elem_of_map_to_list. apply list_elem_of_In. exact Hin.
Qed.

Lemma JR_regions J J' rho rho' sG sC sG' sC' :
  JR J rho sG sC ->
  (forall q rq, r_kind rq <> RKBrk -> (s_regions sG !! q = Some rq <-> s_regions sG' !! q = Some rq)) ->
  (forall q rq, s_regions sG !! q = Some rq -> r_kind rq <> RKBrk -> rho' q = rho q) ->
  j_resvC J' = j_resvC J -> j_groups J' = j_groups J -> j_metas J' = j_metas J ->
  (forall bG bC l, j_brkreg J' = Some (bG, bC, l) <->
     exists q rq, s_regions sG' !! q = Some rq /\ r_kind rq = RKBrk /\ r_base rq = bG /\ rho' q = bC /\ r_len rq = l) ->
  match c_brk (s_ctx sG') with BrkUntried => j_brk J' = JUntried | BrkLive _ _ => j_brk J' = JLive | BrkDead => j_brk J' = JDead end ->
  RC rho' (j_resvC J') (j_ceilC J') sG' sC' -> JR J' rho' sG' sC'.
Proof.
  intros [R1 R2 R3 R4 R5] SAME RHO E1 E2 E3 BR BK RC'.
  assert (PF : forall F, (forall q rq, F (q, rq) = true -> r_kind rq <> RKBrk) ->
            Permutation (List.filter F (map_to_list (s_regions sG))) (List.filter F (map_to_list (s_regions sG')))).
  { intros F HF. apply regions_filter_perm. intros q rq Fq. apply SAME. exact (HF q rq Fq). }
  constructor.
  - exact RC'.
  - rewrite E2. eapply Permutation_trans; [exact R2|].
    erewrite map_ext_in; [apply Permutation_map; apply PF; intros q rq Fq; unfold isG in Fq; cbn in Fq; destruct (r_kind rq); discriminate|].
    intros [q rq] Hin. apply filter_In in Hin as [Hin Fq]. apply In_map_to_list_regions in Hin. unfold isG in Fq. cbn in Fq.
    unfold jG. cbn. rewrite (RHO q rq Hin) by (destruct (r_kind rq); discriminate). reflexivity.
  - rewrite E3. eapply Permutation_trans; [exact R3|].
    erewrite map_ext_in; [apply Permutation_map; apply PF; intros q rq Fq; unfold isM in Fq; cbn in Fq; destruct (r_kind rq); discriminate|].
    intros [q rq] Hin. apply filter_In in Hin as [Hin Fq]. apply In_map_to_list_regions in Hin. unfold isM in Fq. cbn in Fq.
    unfold jG. cbn. rewrite (RHO q rq Hin) by (destruct (r_kind rq); discriminate). reflexivity.
  - exact BR.
  - exact BK.
Qed.

Section NEW_META2.
Variables (X : extras) (LG : mled) (J : jled) (rho : N -> Z) (sG sC : mstate) (zG zC : Z).
Hypothesis IRG : inv_R X sG LG.
Hypothesis R : JR J rho sG sC.
Let n : Z := Z.shiftl 2 (c_meta_alloc_shift (s_ctx sG)).
Let len : Z := n * PGSZ.
Let rid := s_next_rid sG.
Let F (q : N) := fun c => set_meta_alloc_shift (c_meta_alloc_shift c + 1) (set_avail_meta_area_count (n - 1) (set_avail_meta_areas (Some (q, PGSZ)) c)).
Let sG2 := upd_ctx (F (s_next_rid sG)) (fst (new_region RKMeta zG len sG)).
Let sC2 := upd_ctx (F (s_next_rid sC)) (fst (new_region RKMeta zC len sC)).
Let J' := jset_metas ((zG, zC, len, 0) :: j_metas J) J.

#[using="X LG IRG R"] Lemma JR_new_meta : JR J' (nupd rho rid zC) sG2 sC2.
Proof.
  pose proof R as [R1 R2 R3 R4 R5].
  pose proof (next_rid_fresh _ _ _ IRG) as FR. fold rid in FR.
  assert (OLD : forall kr, In kr (map_to_list (s_regions sG)) -> fst kr <> rid).
  { intros [q rq] Hin E. cbn in E. subst q. apply In_map_to_list_regions in Hin. rewrite FR in Hin. discriminate. }
  constructor.
  - cbn. unfold sG2, sC2. rewrite (RC_next_rid _ _ _ _ _ R1). apply RC_upd_ctx. exact (proj1 (RC_new_region rho (j_resvC J) (j_ceilC J) RKMeta zG zC len sG sC R1)).
  - cbn. fold rid.
    eapply Permutation_trans; [| apply Permutation_map; apply Permutation_sym; apply (regions_insert_perm sG rid _ isG FR)].
    cbn. rewrite (map_jG_ext rho); [exact R2|]. intros kr Hk. apply filter_In in Hk as [Hk _]. apply nupd_other. exact (OLD kr Hk).
  - cbn. fold rid.
    eapply Permutation_trans; [| apply Permutation_map; apply Permutation_sym; apply (regions_insert_perm sG rid _ isM FR)].
    cbn. unfold jG at 1. cbn. rewrite nupd_same. apply perm_skip.
    rewrite (map_jG_ext rho); [exact R3|]. intros kr Hk. apply filter_In in Hk as [Hk _]. apply nupd_other. exact (OLD kr Hk).
  - cbn. fold rid. intros bG bC l. rewrite R4. split; intros (q & rq & Hq & K & E1 & E2 & E3); exists q, rq.
    + destruct (N.eq_dec q rid) as [->|NE]; [rewrite FR in Hq; discriminate|]. rewrite lookup_insert_ne by congruence. rewrite nupd_other by exact NE. auto 10.
    + destruct (N.eq_dec q rid) as [->|NE]; [rewrite lookup_insert_eq in Hq; inversion Hq; subst; discriminate|].
      rewrite lookup_insert_ne in Hq by congruence. rewrite nupd_other in E2 by exact NE. auto 10.
  - cbn. exact R5.
Qed.
End NEW_META2.

Lemma map_m3_jbump aG l : map m3 (map (jbump aG) l) = map m3 l.
Proof.
  induction l as [|[[[bG bC] n] k] l IH]; cbn; [reflexivity|]. rewrite IH. unfold jbump. cbn. destruct (bG + (1 + k) * PGSZ =? aG); reflexivity.
Qed.

Lemma JR_meta_adv J rho sG sC p aG : JR J rho sG sC -> JR (jset_metas (map (jbump aG) (j_metas J)) J) rho (adv sG p) (adv sC p).
Proof.
  intros R. pose proof R as [R1 R2 R3 R4 R5]. constructor; cbn.
  - apply RC_upd_ctx. exact R1.
  - exact R2.
  - rewrite map_m3_jbump. exact R3.
  - exact R4.
  - exact R5.
Qed.

Section COH.
Variables (X : extras) (BLG : list blk) (LSG : lhead -> list aptr) (J : jled) (rho : N -> Z) (sG sC : mstate).
Hypothesis INVG : INVL X sG (projG J) BLG LSG.
Hypothesis IRC : inv_R X sC (projC J).
Hypothesis R : JR J rho sG sC.
Let IRG : inv_R X sG (projG J) := proj1 INVG.
Let HRC := jr_rc _ _ _ _ R.

#[using="X BLG LSG sC INVG IRC R IRG HRC"] Lemma coh_munmap rid r : s_regions sG !! rid = Some r -> r_kind r = RKGroup ->
  jg_coherent (r_base r) (rho rid) (j_groups J).
Proof.
  intros Hr K g Hg. destruct (jr_group_of _ _ _ _ g R Hg) as (q & rq & Hq & Kq & ->). cbn. split; intros E.
  - pose proof (baseG_inj X (projG J) sG IRG q rid rq r Hq Hr ltac:(rewrite Kq; discriminate) ltac:(rewrite K; discriminate) E) as EQ. subst q. reflexivity.
  - pose proof (baseC_inj X (projC J) rho (j_resvC J) (j_ceilC J) sG sC IRC HRC q rid rq r Hq Hr ltac:(rewrite Kq; discriminate) ltac:(rewrite K; discriminate) E) as EQ. subst q.
    rewrite Hr in Hq. inversion Hq. reflexivity.
Qed.

#[using="X BLG LSG sC INVG R IRG"] Lemma jmeta_entry bG bC n k : In (bG, bC, n, k) (j_metas J) ->
  exists q rq, s_regions sG !! q = Some rq /\ r_kind rq = RKMeta /\ bG = r_base rq /\ bC = rho q /\ n = r_len rq
    /\ (1 + k) * PGSZ = frontier sG q rq /\ PGSZ <= frontier sG q rq <= r_len rq.
Proof.
  intros Hin. destruct (jr_meta_of _ _ _ _ _ R Hin) as (q & rq & Hq & Kq & E). unfold m3 in E. cbn in E. inversion E. subst bG bC n. clear E.
  assert (HG : In (r_base rq, r_len rq, k) (ld_metas (projG J))).
  { cbn. apply in_map_iff. exists (r_base rq, rho q, r_len rq, k). auto. }
  pose proof (Permutation_in _ (ir_metas _ _ _ IRG) HG) as H2. apply in_map_iff in H2 as ([q' rq'] & E2 & Hin2).
  apply In_filter_mtl in Hin2 as [Hq' M']. cbn in E2, M'. inversion E2.
  assert (KM' : r_kind rq' = RKMeta) by (destruct (r_kind rq'); try discriminate; reflexivity).
  pose proof (baseG_inj X (projG J) sG IRG q' q rq' rq Hq' Hq ltac:(rewrite KM'; discriminate) ltac:(rewrite Kq; discriminate) ltac:(assumption)) as ->.
  rewrite Hq in Hq'. inversion Hq'. subst rq'.
  destruct (ir_metalen _ _ _ IRG q rq Hq Kq) as (_ & FB & FM).
  exists q, rq. repeat split; auto; try lia.
Qed.

#[using="X BLG LSG rho INVG IRC R IRG HRC"] Lemma coh_mprotect rid off : c_avail_meta_areas (s_ctx sG) = Some (rid, off) -> 0 < c_avail_meta_area_count (s_ctx sG) ->
  jm_coherent (conc sG (rid, off)) (conc sC (rid, off)) (j_metas J).
Proof.
  intros Hcur Hcnt bG bC n k Hin.
  destruct (ma_region X sG (projG J) BLG LSG rid off INVG Hcur Hcnt) as (r & Hr & K & P1 & P2 & P3 & P4 & P5 & P6).
  pose proof (proj1 (ir_cursor _ _ _ IRG)) as C0.
  destruct (jmeta_entry bG bC n k Hin) as (q & rq & Hq & Kq & -> & -> & -> & FR & FB).
  rewrite (RC_conc rho (j_resvC J) (j_ceilC J) sG sC (rid, off) HRC). cbn [fst snd]. rewrite Hr.
  unfold conc, get_region. cbn [fst snd]. rewrite Hr. rewrite FR.
  rewrite (ma_frontier sG rid off Hcur) in FR, FB |- *.
  destruct (N.eqb_spec rid q) as [<-|NE].
  - rewrite Hr in Hq. inversion Hq. subst rq. split; intros; lia.
  - destruct (ir_shape _ _ _ IRG _ _ Hq) as (_ & _ & L0 & _).
    split; intros E; exfalso; apply NE; symmetry.
    + apply (pointG_inj X (projG J) sG IRG q rid rq r (r_len rq) off Hq Hr ltac:(rewrite Kq; discriminate) ltac:(rewrite K; discriminate)); unfold PGSZ in *; lia.
    + apply (pointC_inj X (projC J) rho (j_resvC J) (j_ceilC J) sG sC IRC HRC q rid rq r (r_len rq) off Hq Hr ltac:(rewrite Kq; discriminate) ltac:(rewrite K; discriminate)); unfold PGSZ in *; lia.
Qed.

#[using="X BLG LSG sC INVG R IRG"] Lemma jmeta_cursor rid off : c_avail_meta_areas (s_ctx sG) = Some (rid, off) -> 0 < c_avail_meta_area_count (s_ctx sG) ->
  exists r, s_regions sG !! rid = Some r /\ In (r_base r, rho rid, r_len r, off / PGSZ - 1) (j_metas J)
    /\ PGSZ <= off /\ off mod PGSZ = 0 /\ off + PGSZ <= r_len r.
Proof.
  intros Hcur Hcnt.
  destruct (ma_region X sG (projG J) BLG LSG rid off INVG Hcur Hcnt) as (r & Hr & K & P1 & P2 & P3 & P4 & P5 & P6).
  exists r. split; [exact Hr|].
  destruct (jr_meta_in _ _ _ _ _ _ R Hr K) as [k Hin].
  destruct (jmeta_entry _ _ _ _ Hin) as (q & rq & Hq & Kq & Eb & _ & _ & FR & FB).
  pose proof (baseG_inj X (projG J) sG IRG rid q r rq Hr Hq ltac:(rewrite K; discriminate) ltac:(rewrite Kq; discriminate) Eb) as <-.
  rewrite Hr in Hq. inversion Hq. subst rq. rewrite (ma_frontier sG rid off Hcur), N.eqb_refl in FR.
  replace (off / PGSZ - 1) with k by (unfold PGSZ in *; pose proof (Z.div_mod off 4096 ltac:(lia)); nia).
  split; [exact Hin|]. unfold PGSZ in *. lia.
Qed.
End COH.
