(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run Specs.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec ShapeSet RealizesCfg AsanAcct PlacementCount AllocNodesCfg SysNodesCfg.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLin FxCore.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound FxMem FxRgs FxFacts FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSubst FxEnt FxLoop FxPlan FxFrame FxEcall.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChDen.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound.FxGlue OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxMem OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxRgs OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEnt OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEcall OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen.FxAcct.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require Import FxBacking FxChDen.

Module AcFacts.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec ShapeSet RealizesCfg AsanAcct PlacementCount AllocNodesCfg.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import FxLin FxCore FxSound FxMem FxFacts FxSubst FxEnt.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require Import FxBacking FxChDen.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Definition with_facts (S : sst) (fs : list fact) : sst := SST (s_pc S) (s_regs S) (s_rgs S) fs (s_next S) (s_resv S).

Section Facts.
Variable segs : list Segment.
Variable LIMIT : Z.
Variable model0 : Model.
Variable mem0 : word -> option byte.

(* [comment removed for export] *)
#[using="Type"] Theorem den_facts : forall E S M ms model fs',
  DEN segs LIMIT model0 mem0 E S M ms model ->
  (forall E', agree (s_next S) E E' -> Forall (fact_ok E') (s_facts S) -> Forall (fact_ok E') fs') ->
  DEN segs LIMIT model0 mem0 E (with_facts S fs') M ms model.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E S M ms model fs' Hd Hf.
  destruct Hd as [Hsd Hwf Hbw Hh Hawf Hanz Hminv Hhoff Hres Hlim Hsp Hspok Hbrk Hsbrk Htid Hmaps Hgsh Hgtop Hivwf Hpd Hmres Hkind Hlzm Hzrsh Hzrm Hzr Hrl Hvmo Hproc Hfrz Hrom Hown Hblob].
  constructor; cbn [with_facts s_rgs s_next]; try assumption.
  intros E' Ha. destruct (Hsd E' Ha) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8). unfold sden0; cbn [with_facts s_pc s_regs s_rgs s_facts s_resv].
  exact (conj A1 (conj A2 (conj A3 (conj A4 (conj A5 (conj A6 (conj (Hf E' Ha A7) A8))))))).
Qed.

(* [comment removed for export] *)
#[using="Type"] Theorem den_sub_facts : forall E S M ms model fs',
  DEN segs LIMIT model0 mem0 E S M ms model -> forallb (fact_implied (s_facts S)) fs' = true ->
  DEN segs LIMIT model0 mem0 E (with_facts S fs') M ms model.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E S M ms model fs' Hd Hi. apply (den_facts E S M ms model fs' Hd).
  intros E' _ HF. rewrite Forall_forall. rewrite forallb_forall in Hi. intros f Hf. exact (fact_implied_ok E' _ f HF (Hi f Hf)).
Qed.

(* [comment removed for export] *)
#[using="Type"] Theorem den_add_facts : forall E S M ms model fs,
  DEN segs LIMIT model0 mem0 E S M ms model -> (forall E', agree (s_next S) E E' -> Forall (fact_ok E') fs) ->
  DEN segs LIMIT model0 mem0 E (with_facts S (s_facts S ++ fs)) M ms model.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E S M ms model fs Hd Hf. apply (den_facts E S M ms model _ Hd).
  intros E' Ha HF. apply Forall_app. split; [exact HF | exact (Hf E' Ha)].
Qed.
(* [comment removed for export] *)
Definition sp_fact (M : smodel) : fact := FRange (sm_sp M) sp_window_lo sp_window_hi.
#[using="Type"] Theorem den_sp_fact : forall E S M ms model,
  DEN segs LIMIT model0 mem0 E S M ms model -> DEN segs LIMIT model0 mem0 E (with_facts S (s_facts S ++ [sp_fact M])) M ms model.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E S M ms model Hd. apply (den_add_facts E S M ms model _ Hd). intros E' Ha. constructor; [|constructor].
  pose proof (dn_wf _ _ _ _ _ _ _ _ _ Hd) as Hwf. unfold sm_wf in Hwf.
  repeat match goal with H : (_ && _)%bool = true |- _ => apply andb_prop in H as [? ?] end.
  assert (Hl : lwf (s_next S) (sm_sp M) = true) by assumption.
  cbn [sp_fact fact_ok]. rewrite (lden_agree_wf _ E E' _ Hl Ha).
  rewrite <- (dn_sp _ _ _ _ _ _ _ _ _ Hd). destruct (dn_spok _ _ _ _ _ _ _ _ _ Hd) as [Hlo Hhi]. unfold init_sp_ok in Hlo. lia.
Qed.
End Facts.
End AcFacts.

Module FxKeep.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import FxLin FxCore.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require Import FxChDen.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Definition keep_ok (model' : Model) (M M' : smodel) (m0 m0' : word -> option byte) : Prop :=
  incl (sm_maps M) (sm_maps M') /\ incl (sm_own M) (sm_own M') /\
  (forall x, 0 <= x < alloc_top (m_vmmaps model') -> m0' (Z_to_bv 64 x) = m0 (Z_to_bv 64 x)) /\
  (forall x, in_zr (sm_zr M) x = true -> in_zr (sm_zr M') x = true).   (* [comment removed for export] *)

Lemma keep_ok_refl : forall model M m0, keep_ok model M M m0 m0.
Proof. intros model M m0. split; [apply incl_refl | split; [apply incl_refl | split; [reflexivity | intros x Hx; exact Hx]]]. Qed.
(* [comment removed for export] *)
End FxKeep.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition a0r : reg := Z_to_bv 5 10.

(* [comment removed for export] *)
Lemma unrestrict_svc : forall H ms, unrestrict H (ms_mem ms) (svc_set (restrict H ms)) = svc_set ms.
Proof. intros H ms. destruct ms. unfold unrestrict, svc_set, restrict. cbn. rewrite munrestrict_mrestrict. reflexivity. Qed.

Lemma restrict_adv_eff : forall H ms v zs us ci pcz, ms_pc_val ms = Z_to_bv 64 pcz ->
  restrict H (advance_past_svc (apply_effect (svc_set ms) (mkEffectU v [] zs us [] ci))) =
  mks (ms_fregs ms) (ms_fcsr ms) (rupd (ms_regs ms) a0r v) (Z_to_bv 64 (pcz + 4)) (ms_resv ms)
      (mrestrict H (apply_zeros (apply_unmaps (ms_mem ms) us) zs)) (ms_rom ms).
Proof.
  intros H ms v zs us ci pcz Hpc. destruct ms as [rg fr pcv sv rv fc mem rom]. cbn in Hpc. subst pcv.
  unfold restrict, advance_past_svc, apply_effect, svc_set, set_reg, mks, rupd, regupd, a0r, ms_pc.
  cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom eff_ret eff_writes eff_zeros eff_unmaps eff_copies apply_writes apply_copies].
  assert (E10 : @bv_eqb 5 10 0 = false) by reflexivity. rewrite E10.
  cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom].
  rewrite pc_plus4. reflexivity.
Qed.

Lemma adv_eff_mem : forall ms v zs us ci,
  ms_mem (advance_past_svc (apply_effect (svc_set ms) (mkEffectU v [] zs us [] ci))) = apply_zeros (apply_unmaps (ms_mem ms) us) zs.
Proof.
  intros ms v zs us ci. destruct ms as [rg fr pcv sv rv fc mem rom].
  unfold advance_past_svc, apply_effect, svc_set, set_reg.
  assert (E10 : @bv_eqb 5 10 0 = false) by reflexivity. rewrite E10. reflexivity.
Qed.

Definition in_zs (zs : list (word * word)) (w : word) : bool := zeros_cover zs w.

Lemma apply_zeros_out : forall mem zs w, zeros_cover zs w = false -> apply_zeros mem zs w = mem w.
Proof. intros mem [|z zs] w H; [reflexivity|]. cbn [apply_zeros]. rewrite H. reflexivity. Qed.
Lemma apply_zeros_in : forall mem zs w, zeros_cover zs w = true -> apply_zeros mem zs w = Some (Z_to_bv 8 0).
Proof. intros mem [|z zs] w H; [discriminate|]. cbn [apply_zeros]. rewrite H. reflexivity. Qed.
Lemma apply_unmaps_out : forall mem us w, zeros_cover us w = false -> apply_unmaps mem us w = mem w.
Proof. intros mem [|z us] w H; [reflexivity|]. cbn [apply_unmaps]. rewrite H. reflexivity. Qed.
Lemma apply_unmaps_in : forall mem us w, zeros_cover us w = true -> apply_unmaps mem us w = None.
Proof. intros mem [|z us] w H; [discriminate|]. cbn [apply_unmaps]. rewrite H. reflexivity. Qed.

Lemma zeros_cover_one : forall (a n w : word),
  zeros_cover [(a, n)] w = ((bv_unsigned a <=? bv_unsigned w) && (bv_unsigned w <? bv_unsigned a + bv_unsigned n))%bool.
Proof. intros. unfold zeros_cover. cbn. rewrite orb_false_r. reflexivity. Qed.

(* [comment removed for export] *)
Section Rg.
Variable segs : list Segment.

#[using="Type"] Lemma seg_rom_none : forall a, find_segment segs (bv_unsigned a) 1 = None -> seg_rom segs a = None.
Proof. LiaFast.lf_pins LiaFast.u0. intros a H. unfold seg_rom, memory_read. change (Z.of_N 1%N) with 1%Z. rewrite H. reflexivity. Qed.

Definition rg_pt (E : valu) (R : region) (w : Z) : Prop := uE E (rg_base R) <= w < uE E (rg_base R) + rsz E R.

#[using="Type"] Lemma rg_ok_visible : forall H full E R, H_off_segments segs H -> rg_ok segs E (mrestrict H full) R ->
  forall i, 0 <= i < rsz E R -> H (Z_to_bv 64 (uE E (rg_base R) + i)) = false.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros H full E R Hoff Hok i Hi. destruct Hok as (_ & _ & Hb & _). specialize (Hb i Hi).
  destruct (H (Z_to_bv 64 (uE E (rg_base R) + i))) eqn:Hh; [|reflexivity]. exfalso.
  assert (Hn : seg_rom segs (Z_to_bv 64 (uE E (rg_base R) + i)) = None) by (apply seg_rom_none; apply Hoff; exact Hh).
  assert (Hm : mrestrict H full (Z_to_bv 64 (uE E (rg_base R) + i)) = None) by (unfold mrestrict; rewrite Hh; reflexivity).
  unfold uE in *. destruct (rg_kind R); unfold rd1 in Hb; rewrite ?Hm, ?Hn in Hb; tauto.
Qed.

#[using="Type"] Lemma rg_ok_mem_eq : forall E m m' R, rg_ok segs E m R ->
  (forall i, 0 <= i < rsz E R -> m' (Z_to_bv 64 (uE E (rg_base R) + i)) = m (Z_to_bv 64 (uE E (rg_base R) + i))) ->
  rg_ok segs E m' R.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E m m' R (Hs & Hw & Hb & Hc) Heq. unfold uE in Heq. split; [exact Hs|]. split; [exact Hw|]. split.
  - intros i Hi. specialize (Hb i Hi). specialize (Heq i Hi). unfold rd1, wview in *. rewrite Heq. exact Hb.
  - intros p v Hp. destruct (Hc p v Hp) as [Hp1 Hp2]. split; [exact Hp1|].
    assert (Hi : 0 <= Zpos p - 1 < rsz E R) by lia. specialize (Heq _ Hi). unfold rd1 in *. rewrite Heq. exact Hp2.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rg_ok_fresh_rz : forall E m (b : lin) n,
  0 <= n < two64 -> uE E b + n <= two64 ->
  (forall i, 0 <= i < n -> m (Z_to_bv 64 (uE E b + i)) = Some (Z_to_bv 8 0)) ->
  rg_ok segs E m (RGz b n RZ TEmpty).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E m b n Hn Hw Hz. unfold rg_ok. rewrite rsz_RGz by exact Hn. destruct Hn as [Hn _].
  unfold RGz. cbn [rg_base rg_size rg_kind rg_cont]. unfold uE in *.
  split; [exact Hn|]. split; [exact Hw|]. split.
  - intros i Hi. specialize (Hz i Hi). unfold rd1, wview. rewrite Hz. split; [split; discriminate|]. intros _. reflexivity.
  - intros p v Hp. rewrite tget_empty in Hp. discriminate.
Qed.
End Rg.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma gsz_const : forall E g z, gsz_c g = Some z -> gsz E g = z.
Proof. intros E g z H. unfold gsz, uE. destruct (is_const_sound E _ z H) as [H1 H2]. rewrite H1. apply u_small64. exact H2. Qed.
Lemma gsz_c_range : forall g z, gsz_c g = Some z -> 0 <= z < two64.
Proof. intros g z H. exact (proj2 (is_const_sound (fun _ => Z_to_bv 64 0) _ z H)). Qed.
(* [comment removed for export] *)
Definition gsz_hi (fs : list fact) (g : lin * lin * gkind) : Z :=
  match gsz_c g with Some z => z | None => Z.max 0 (snd (irange fs (snd (fst g)))) end.
Definition gsz_lo (fs : list fact) (g : lin * lin * gkind) : Z :=
  match gsz_c g with Some z => z | None => Z.max 0 (fst (irange fs (snd (fst g)))) end.
Lemma gsz_bounds : forall E fs g, Forall (fact_ok E) fs -> gsz_lo fs g <= gsz E g <= gsz_hi fs g.
Proof.
  intros E fs g HF. unfold gsz_lo, gsz_hi. destruct (gsz_c g) as [z|] eqn:Hz; [rewrite (gsz_const E g z Hz); lia|].
  unfold gsz, uE. pose proof (irange_sound E fs (snd (fst g)) HF) as H.
  pose proof (bv_unsigned_in_range _ (lden E (snd (fst g)))). lia.
Qed.
Lemma gsz_lo_nonneg : forall fs g, 0 <= gsz_lo fs g.
Proof. intros fs g. unfold gsz_lo. destruct (gsz_c g) as [z|] eqn:Hz; [exact (proj1 (gsz_c_range g z Hz)) | lia]. Qed.
Lemma gsz_hi_nonneg : forall fs g, 0 <= gsz_hi fs g.
Proof. intros fs g. unfold gsz_hi. destruct (gsz_c g) as [z|] eqn:Hz; [exact (proj1 (gsz_c_range g z Hz)) | lia]. Qed.

Definition eager_sum (fs : list fact) (gs : list (lin * lin * gkind)) : Z :=
  fold_right (fun g acc => (if gkind_eqb (snd g) GE then gsz_hi fs g else 0) + acc) 0 gs.

Lemma eager_sum_nonneg : forall fs gs, 0 <= eager_sum fs gs.
Proof.
  intros fs gs. induction gs as [|g gs IH]; cbn [eager_sum fold_right]; [lia|].
  fold (eager_sum fs gs). destruct (gkind_eqb (snd g) GE); [|lia].
  pose proof (gsz_hi_nonneg fs g). lia.
Qed.

Lemma gden_S : forall E g, gshape_ok E g -> S (gden E g) = gsz E g.
Proof. intros E g _. reflexivity. Qed.
Lemma gden_B : forall E g, B (gden E g) = uE E (fst (fst g)).
Proof. reflexivity. Qed.

Lemma ivs_wf_gden : forall E gs, Forall (gshape_ok E) gs -> ivs_wf (List.map (gden E) gs).
Proof.
  intros E gs H q Hq. apply in_map_iff in Hq as (g & <- & Hg). rewrite Forall_forall in H. specialize (H g Hg).
  unfold iv_wf. rewrite gden_S, gden_B by exact H. destruct H as (_ & _ & _ & H4). lia.
Qed.

(* [comment removed for export] *)
Lemma ivs_wf_blob : forall model BL, Forall (blob_ent_ok model) BL -> ivs_wf BL.
Proof.
  intros model BL H q Hq. rewrite Forall_forall in H. destruct (H q Hq) as (_ & _ & _ & _ & Ht). unfold iv_wf, B, S.
  pose proof (alloc_top_lt (m_vmmaps model)) as Hat. unfold two_pow_64 in Hat. lia.
Qed.
Lemma ivs_wf_lden : forall E model BL gs, Forall (gshape_ok E) gs -> Forall (blob_ent_ok model) BL -> ivs_wf (lden_maps E BL gs).
Proof.
  intros E model BL gs H HB q Hq. apply lden_maps_inv in Hq as [(g & Hg & _ & ->) | (Hq & _)].
  - exact (ivs_wf_gden E gs H _ (in_map (gden E) gs g Hg)).
  - exact (ivs_wf_blob model BL HB q Hq).
Qed.
Lemma sum_count_le_size : forall P l, sum_count P l <= ledger_size l.
Proof.
  intros P l. induction l as [|[b n] r IH]; [cbn; lia|]. cbn [sum_count ledger_size]. unfold iv_count, S. cbn [snd].
  pose proof (zcount_le_len P (B (b, n)) (Z.to_nat (bv_unsigned n))) as Hl. pose proof (bv_unsigned_in_range _ n). rewrite Z2Nat.id in Hl by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma pdisj_app_r : forall l1 l2, pdisj (l1 ++ l2) -> pdisj l2.
Proof. induction l1 as [|x r IH]; intros l2 H; [exact H|]. destruct H as [_ H]. exact (IH l2 H). Qed.
Lemma pdisj_app_l : forall l1 l2 p q, pdisj (l1 ++ l2) -> In p l1 -> In q l2 -> iv_disj p q.
Proof.
  induction l1 as [|x r IH]; intros l2 p q H Hp Hq; [destruct Hp|]. destruct H as [Hx H]. destruct Hp as [->|Hp].
  - rewrite Forall_forall in Hx. apply Hx. apply in_or_app. right. exact Hq.
  - exact (IH l2 p q H Hp Hq).
Qed.
Lemma iv_disj_sym : forall p q, iv_disj p q -> iv_disj q p.
Proof. intros p q H. unfold iv_disj in *. lia. Qed.
Lemma pdisj_lden_nth : forall E BL gs i j gi gj, pdisj (lden_maps E BL gs) ->
  nth_error gs i = Some gi -> nth_error gs j = Some gj -> i <> j -> is_mark gi = false -> is_mark gj = false ->
  iv_disj (gden E gi) (gden E gj).
Proof.
  intros E BL gs. induction gs as [|g r IH]; intros i j gi gj Hpd Hi Hj Hne Hmi Hmj; [destruct i; discriminate|].
  cbn [lden_maps] in Hpd. destruct (is_mark g) eqn:Hm.
  - apply pdisj_app_r in Hpd. destruct i as [|i]; [cbn in Hi; injection Hi as <-; rewrite Hm in Hmi; discriminate|].
    destruct j as [|j]; [cbn in Hj; injection Hj as <-; rewrite Hm in Hmj; discriminate|].
    exact (IH i j gi gj Hpd Hi Hj ltac:(lia) Hmi Hmj).
  - destruct Hpd as [Hx Hr]. rewrite Forall_forall in Hx. destruct i as [|i], j as [|j]; cbn [nth_error] in Hi, Hj; try lia.
    + injection Hi as <-. apply Hx. exact (lden_maps_in E BL r gj (nth_error_In _ _ Hj) Hmj).
    + injection Hj as <-. apply iv_disj_sym. apply Hx. exact (lden_maps_in E BL r gi (nth_error_In _ _ Hi) Hmi).
    + exact (IH i j gi gj Hr Hi Hj ltac:(lia) Hmi Hmj).
Qed.
Lemma pdisj_lden_blob : forall E BL gs g q, pdisj (lden_maps E BL gs) -> In g gs -> is_mark g = false -> In q BL -> nomark gs = false ->
  iv_disj (gden E g) q.
Proof.
  intros E BL gs. induction gs as [|g0 r IH]; intros g q Hpd Hg Hm Hq Hn; [destruct Hg|]. cbn [lden_maps] in Hpd.
  destruct (is_mark g0) eqn:Hm0.
  - destruct Hg as [->|Hg]; [rewrite Hm0 in Hm; discriminate|].
    apply iv_disj_sym. apply (pdisj_app_l BL (lden_maps E BL r) q (gden E g) Hpd Hq). exact (lden_maps_in E BL r g Hg Hm).
  - destruct Hpd as [Hx Hr]. cbn [nomark forallb] in Hn. rewrite Hm0 in Hn. cbn [negb andb] in Hn. destruct Hg as [->|Hg].
    + rewrite Forall_forall in Hx. apply Hx. clear -Hq Hn. induction r as [|g1 r IH]; [discriminate|]. cbn [lden_maps]. cbn [nomark forallb] in Hn.
      destruct (is_mark g1); [apply in_or_app; left; exact Hq|]. cbn [negb andb] in Hn. right. exact (IH Hn).
    + exact (IH g q Hr Hg Hm Hq Hn).
Qed.

(* [comment removed for export] *)
Lemma blob_sh_grant : forall E M model BL j g (a n y : Z), vm_maps (m_vmmaps model) = lden_maps E BL (sm_maps M) ->
  pdisj (vm_maps (m_vmmaps model)) -> blob_ok E M model BL -> nth_error (sm_maps M) j = Some g -> is_mark g = false ->
  uE E (fst (fst g)) <= a -> a + n <= uE E (fst (fst g)) + gsz E g ->
  a / 8 + SH_OFF <= y < (a + n) / 8 + SH_OFF -> ~ blob_sh BL y.
Proof.
  intros E M model BL j g a n y Hm Hpd Hb Hj Hgm Hlo Hhi Hy ([b k] & Hq & Hs). unfold SHz in Hs. cbn [fst snd] in Hs.
  assert (Hnm : nomark (sm_maps M) = false).
  { destruct (nomark (sm_maps M)) eqn:Hn; [|reflexivity]. rewrite (proj1 (proj2 Hb) Hn) in Hq. destruct Hq. }
  rewrite Hm in Hpd. pose proof (pdisj_lden_blob E BL _ g (b, k) Hpd (nth_error_In _ _ Hj) Hgm Hq Hnm) as Hd.
  unfold iv_disj, B, S, gden in Hd. cbn [fst snd] in Hd. unfold gsz, uE in *. destruct Hd as [Hd|Hd].
  - assert ((a + n) / 8 <= bv_unsigned b / 8) by (apply Z.div_le_mono; lia). lia.
  - assert ((bv_unsigned b + bv_unsigned k) / 8 <= a / 8) by (apply Z.div_le_mono; lia). lia.
Qed.

Lemma eager_used_sem_maps : forall m, ivs_wf (vm_maps (m_vmmaps m)) ->
  eager_used m = sum_count (fun x => negb (covered (vm_noaccess (m_vmmaps m) ++ m_vm_lazy m) x)) (vm_maps (m_vmmaps m)).
Proof.
  intros m Hw. pose proof (vm_backing_used_sem_maps m Hw) as H. rewrite vm_backing_used_split in H. lia.
Qed.

(* [comment removed for export] *)
Lemma In_maps_subtract_disj : forall l (a sz : word) (lo hi : Z), In (a, sz) l -> lo <= hi ->
  (bv_unsigned a + bv_unsigned sz <= lo \/ hi <= bv_unsigned a) -> 0 < bv_unsigned sz ->
  In (a, sz) (maps_subtract l lo hi).
Proof.
  induction l as [|[b s] l IH]; intros a sz lo hi Hin Hlh Hd Hs; [destruct Hin|]. cbn [maps_subtract]. apply in_or_app.
  destruct Hin as [Heq|Hin]; [|right; exact (IH a sz lo hi Hin Hlh Hd Hs)]. injection Heq as Hb0 Hs0. subst b s. left.
  unfold iv_subtract. cbv zeta. pose proof (bv_unsigned_in_range _ a) as Ra. pose proof (bv_unsigned_in_range _ sz) as Rs.
  apply in_or_app. destruct Hd as [Hd|Hd].
  - left. replace (bv_unsigned a <? lo) with true by (symmetry; apply Z.ltb_lt; lia). left. f_equal.
    rewrite Z.min_l by lia. apply Z_to_bv_bv_unsigned.
  - right. replace (hi <? bv_unsigned a + bv_unsigned sz) with true by (symmetry; apply Z.ltb_lt; lia). left.
    rewrite Z.max_l by lia. rewrite Z_to_bv_bv_unsigned. f_equal. replace (bv_unsigned a + bv_unsigned sz - bv_unsigned a) with (bv_unsigned sz) by lia.
    apply Z_to_bv_bv_unsigned.
Qed.

(* [comment removed for export] *)
Lemma A_bytes_app : forall A1 A2, A_bytes (A1 ++ A2) = A_bytes A1 + A_bytes A2.
Proof. induction A1 as [|iv r IH]; intros A2; cbn [app A_bytes]; [lia | rewrite IH; lia]. Qed.
Lemma A_bytes_blobA : forall model BL, Forall (blob_ent_ok model) BL -> A_bytes (blobA BL) <= 3 * ledger_size BL.
Proof.
  intros model BL H. induction H as [|[b n] r Hp Hr IH]; [cbn; lia|]. cbn [blobA List.map A_bytes ledger_size]. fold (blobA r).
  destruct Hp as (Hlo & Hbal & Hpos & Hnal & _). cbn [fst snd] in *. unfold blobA1, SHz. cbn [fst snd].
  set (ub := bv_unsigned b) in *. set (un := bv_unsigned n) in *.
  assert (Hb8 : ub = 8 * (ub / 8)) by (pose proof (Z.div_mod ub 4096 ltac:(lia)); pose proof (Z.div_mod ub 8 ltac:(lia));
    assert (ub mod 8 = 0) by (replace ub with (4096 * (ub / 4096)) by lia; replace (4096 * (ub / 4096)) with ((512 * (ub / 4096)) * 8) by lia; apply Z_mod_mult); lia).
  assert (Hn8 : un = 8 * (un / 8)) by (pose proof (Z.div_mod un 4096 ltac:(lia)); pose proof (Z.div_mod un 8 ltac:(lia));
    assert (un mod 8 = 0) by (replace un with (4096 * (un / 4096)) by lia; replace (4096 * (un / 4096)) with ((512 * (un / 4096)) * 8) by lia; apply Z_mod_mult); lia).
  assert (Hsum : (ub + un) / 8 = ub / 8 + un / 8) by (rewrite Hb8, Hn8 at 1; rewrite <- Z.mul_add_distr_l, Z.mul_comm, Z.div_mul by lia; reflexivity).
  rewrite Hsum. set (x := SH_OFF + ub / 8). replace (SH_OFF + (ub / 8 + un / 8)) with (x + un / 8) by (unfold x; lia).
  pose proof (Z.mul_div_le x 4096 ltac:(lia)). pose proof (Z.mod_pos_bound x 4096 ltac:(lia)). pose proof (Z.div_mod x 4096 ltac:(lia)).
  pose proof (Z.mod_pos_bound (x + un / 8 + 4095) 4096 ltac:(lia)). pose proof (Z.div_mod (x + un / 8 + 4095) 4096 ltac:(lia)).
  assert (4096 <= un) by (pose proof (Z.div_mod un 4096 ltac:(lia)); nia). lia.
Qed.
Theorem eager_le : forall E M model fs BL, Forall (fact_ok E) fs ->
  vm_maps (m_vmmaps model) = lden_maps E BL (sm_maps M) -> Forall (gshape_ok E) (sm_maps M) -> Forall (kind_ok E model) (sm_maps M) ->
  blob_ok E M model BL ->
  eager_used model + A_bytes (blobA BL) <= eager_sum fs (sm_maps M).
Proof.
  intros E M model fs BL HF Hm Hsh Hk (HB & Hnil & HT).
  rewrite eager_used_sem_maps by (rewrite Hm; exact (ivs_wf_lden E model BL _ Hsh HB)). rewrite Hm. clear Hm.
  pose proof (A_bytes_blobA model BL HB) as HAb.
  destruct (nomark (sm_maps M)) eqn:Hnm.
  { rewrite (Hnil eq_refl) in *. cbn [blobA List.map A_bytes]. rewrite (lden_maps_nomark E [] _ Hnm). clear HT Hnil HAb HB Hnm.
    induction (sm_maps M) as [|g gs IH]; cbn [List.map sum_count eager_sum fold_right]; [lia|].
    inversion Hsh as [|? ? Hg Hgs]; subst. inversion Hk as [|? ? Hkg Hks]; subst. fold (eager_sum fs gs).
    specialize (IH Hgs Hks). cbn [List.map] in IH.
    assert (Hc : iv_count (fun x => negb (covered (vm_noaccess (m_vmmaps model) ++ m_vm_lazy model) x)) (gden E g)
                 <= (if gkind_eqb (snd g) GE then gsz_hi fs g else 0)); [|lia].
    destruct (gkind_eqb (snd g) GE) eqn:Hge.
    - unfold iv_count. rewrite (gden_S E g Hg).
      pose proof (zcount_le_len (fun x => negb (covered (vm_noaccess (m_vmmaps model) ++ m_vm_lazy model) x))
                                     (B (gden E g)) (Z.to_nat (gsz E g))) as Hl.
      pose proof (gsz_bounds E fs g HF) as Hb.
      destruct Hg as (H1 & _). rewrite Z2Nat.id in Hl by lia. lia.
    - assert (Hne : snd g <> GE) by (intros He; rewrite He in Hge; discriminate).
      unfold iv_count. rewrite zcount_false; [lia|]. intros x Hx. rewrite Z2Nat.id in Hx by (pose proof (S_range (gden E g)); lia).
      rewrite (proj1 Hkg Hne x); [reflexivity|]. unfold in_iv, in_rng. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
  (* [comment removed for export] *)
  assert (Hgen : forall gs, Forall (gshape_ok E) gs -> Forall (kind_ok E model) gs ->
            (forall g, In g gs -> is_mark g = true -> snd g = GE /\ 4 * ledger_size BL <= gsz E g) ->
            sum_count (fun x => negb (covered (vm_noaccess (m_vmmaps model) ++ m_vm_lazy model) x)) (lden_maps E BL gs)
            + (if nomark gs then 0 else 3 * ledger_size BL) <= eager_sum fs gs).
  { clear Hsh Hk HT Hnm. intros gs Hsh Hk HT. induction gs as [|g gs IH]; cbn [lden_maps sum_count eager_sum fold_right nomark forallb]; [lia|].
    inversion Hsh as [|? ? Hg Hgs]; subst. inversion Hk as [|? ? Hkg Hks]; subst. fold (eager_sum fs gs). fold (nomark gs).
    specialize (IH Hgs Hks (fun g' Hg' => HT g' (or_intror Hg'))).
    destruct (is_mark g) eqn:Hmk.
    - cbn [negb andb]. rewrite sum_count_app.
      pose proof (sum_count_le_size (fun x => negb (covered (vm_noaccess (m_vmmaps model) ++ m_vm_lazy model) x)) BL) as Hb.
      pose proof (HT g (or_introl eq_refl) Hmk) as Hgz. pose proof (gsz_bounds E fs g HF) as Hgb.
      destruct Hgz as [Hgk Hgz]. rewrite Hgk. cbn [gkind_eqb]. pose proof (ledger_size_nonneg BL). destruct (nomark gs); lia.
    - cbn [negb andb sum_count].
      assert (Hc : iv_count (fun x => negb (covered (vm_noaccess (m_vmmaps model) ++ m_vm_lazy model) x)) (gden E g)
                   <= (if gkind_eqb (snd g) GE then gsz_hi fs g else 0)); [|destruct (nomark gs); lia].
      destruct (gkind_eqb (snd g) GE) eqn:Hge.
      + unfold iv_count. rewrite (gden_S E g Hg).
        pose proof (zcount_le_len (fun x => negb (covered (vm_noaccess (m_vmmaps model) ++ m_vm_lazy model) x))
                                       (B (gden E g)) (Z.to_nat (gsz E g))) as Hl.
        pose proof (gsz_bounds E fs g HF) as Hb.
        destruct Hg as (H1 & _). rewrite Z2Nat.id in Hl by lia. lia.
      + assert (Hne : snd g <> GE) by (intros He; rewrite He in Hge; discriminate).
        unfold iv_count. rewrite zcount_false; [lia|]. intros x Hx. rewrite Z2Nat.id in Hx by (pose proof (S_range (gden E g)); lia).
        rewrite (proj1 Hkg Hne x); [reflexivity|]. unfold in_iv, in_rng. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
  specialize (Hgen (sm_maps M) Hsh Hk HT). rewrite Hnm in Hgen. lia.
Qed.


(* [comment removed for export] *)
Theorem eager_le_old : forall E model fs gs, Forall (fact_ok E) fs ->
  vm_maps (m_vmmaps model) = List.map (gden E) gs -> Forall (gshape_ok E) gs -> Forall (kind_ok E model) gs ->
  eager_used model <= eager_sum fs gs.
Proof.
  intros E model fs gs HF Hm Hsh Hk. rewrite eager_used_sem_maps by (rewrite Hm; exact (ivs_wf_gden E gs Hsh)). rewrite Hm. clear Hm.
  induction gs as [|g gs IH]; cbn [List.map sum_count eager_sum fold_right]; [lia|].
  inversion Hsh as [|? ? Hg Hgs]; subst. inversion Hk as [|? ? Hkg Hks]; subst. fold (eager_sum fs gs).
  specialize (IH Hgs Hks). cbn [List.map] in IH.
  assert (Hc : iv_count (fun x => negb (covered (vm_noaccess (m_vmmaps model) ++ m_vm_lazy model) x)) (gden E g)
               <= (if gkind_eqb (snd g) GE then gsz_hi fs g else 0)).
  { destruct (gkind_eqb (snd g) GE) eqn:Hge.
    - unfold iv_count. rewrite (gden_S E g Hg).
      pose proof (zcount_le_len (fun x => negb (covered (vm_noaccess (m_vmmaps model) ++ m_vm_lazy model) x))
                                     (B (gden E g)) (Z.to_nat (gsz E g))) as Hl.
      pose proof (gsz_bounds E fs g HF) as Hb.
      destruct Hg as (H1 & _). rewrite Z2Nat.id in Hl by lia. lia.
    - assert (Hne : snd g <> GE) by (intros He; rewrite He in Hge; discriminate).
      unfold iv_count. rewrite zcount_false; [lia|]. intros x Hx. rewrite Z2Nat.id in Hx by (pose proof (S_range (gden E g)); lia).
      rewrite (proj1 Hkg Hne x); [reflexivity|]. unfold in_iv, in_rng. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
  lia.
Qed.

(* [comment removed for export] *)
Lemma allow1_wf : forall E p, 0 <= snd p -> let q := allow1 E p in fst q <= snd q /\ fst q mod 4096 = 0 /\ snd q mod 4096 = 0.
Proof.
  intros E [b k] Hk. unfold allow1. cbn [fst snd] in *. pose proof (bv_unsigned_in_range _ (lden E b)) as Hb. unfold uE.
  split; [|split; apply Z_mod_mult].
  assert (H1 : bv_unsigned (lden E b) / 4096 * 4096 <= bv_unsigned (lden E b)) by (pose proof (Z.mul_div_le (bv_unsigned (lden E b)) 4096 ltac:(lia)); lia).
  assert (H2 : bv_unsigned (lden E b) <= (bv_unsigned (lden E b) + k + 4095) / 4096 * 4096).
  { pose proof (Z.mod_pos_bound (bv_unsigned (lden E b) + k + 4095) 4096 ltac:(lia)).
    pose proof (Z.div_mod (bv_unsigned (lden E b) + k + 4095) 4096 ltac:(lia)). lia. }
  lia.
Qed.

Lemma allow1_bytes : forall E p, 0 <= snd p -> snd (allow1 E p) - fst (allow1 E p) <= snd p + 8192.
Proof.
  intros E [b k] Hk. unfold allow1. cbn [fst snd] in *. unfold uE. set (u := bv_unsigned (lden E b)).
  pose proof (Z.mod_pos_bound u 4096 ltac:(lia)). pose proof (Z.div_mod u 4096 ltac:(lia)).
  pose proof (Z.mod_pos_bound (u + k + 4095) 4096 ltac:(lia)). pose proof (Z.div_mod (u + k + 4095) 4096 ltac:(lia)). lia.
Qed.

Definition allow_bound (al : list (lin * Z)) : Z := fold_right (fun p acc => snd p + 8192 + acc) 0 al.

Lemma A_bytes_allowA : forall E M, Forall (fun p => 0 <= snd p) (sm_allow M) -> A_bytes (allowA E M) <= allow_bound (sm_allow M).
Proof.
  intros E M H. unfold allowA. induction H as [|p al Hp Hal IH]; cbn [List.map A_bytes allow_bound fold_right]; [lia|].
  fold (allow_bound al). pose proof (allow1_bytes E p Hp). lia.
Qed.

Lemma A_wf_allowA : forall E M, Forall (fun p => 0 <= snd p) (sm_allow M) -> A_wf (allowA E M).
Proof.
  intros E M H. unfold A_wf, allowA. apply Forall_map. eapply Forall_impl; [|exact H]. intros p Hp. exact (allow1_wf E p Hp).
Qed.

(* [comment removed for export] *)
Lemma vm_backing_used_le : forall A m, MInv A m -> A_wf A -> vm_backing_used m <= eager_used m + A_bytes A.
Proof.
  intros A m [N1 N2 N3 N4 N5] Hwf. rewrite vm_backing_used_split.
  pose proof (allowed_pages_bound A (m_vm_materialized m) Hwf N1 N2 N3). lia.
Qed.
Lemma den_backing_le : forall segs LIMIT model0 mem0 E S M ms model fs, DEN segs LIMIT model0 mem0 E S M ms model -> Forall (fact_ok E) fs ->
  vm_backing_used model <= eager_sum fs (sm_maps M) + allow_bound (sm_allow M).
Proof.
  intros segs LIMIT model0 mem0 E S M ms model fs Hd HF.
  destruct Hd as [Hsd Hwf Hbw Hh Hawf Hanz Hminv Hhoff Hres Hlim Hsp Hspok Hbrk Hsbrk Htid Hmaps Hgsh Hgtop Hivwf Hpd Hmres Hkind Hlzm Hzrsh Hzrm Hzr Hrl Hvmo Hproc Hfrz Hrom Hown Hblob].
  pose proof (vm_backing_used_le _ _ Hminv (A_wf_app _ _ Hawf (A_wf_blobA _))) as Hv. unfold AM in Hv. rewrite A_bytes_app in Hv.
  pose proof (eager_le E M model fs _ HF Hmaps Hgsh Hkind Hblob) as He. pose proof (A_bytes_allowA E M Hanz) as Hb. lia.
Qed.

(* [comment removed for export] *)
Lemma fg64' : forall z, 0 <= z < two64 -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros z Hz. apply fg_lit. unfold two64 in Hz. change (2 ^ 64) with 18446744073709551616. lia. Qed.

Lemma pb_bounds : forall w : word, bv_unsigned (page_base w) <= bv_unsigned w < bv_unsigned (page_base w) + 4096
  /\ bv_unsigned (page_base w) mod 4096 = 0.
Proof.
  intros w. unfold page_base, page_base_of, page_size.
  assert (Hw : 0 <= bv_unsigned w < two64) by exact (bv_unsigned_in_range _ w).
  pose proof (Z.mod_pos_bound (bv_unsigned w) 4096 ltac:(lia)). pose proof (Z.div_mod (bv_unsigned w) 4096 ltac:(lia)).
  rewrite fg64' by (unfold two64 in *; lia).
  split; [lia|]. apply Z_mod_mult.
Qed.

Lemma page_in_covered : forall p L x, page_in_ranges p L = true -> bv_unsigned p <= x < bv_unsigned p + 4096 -> covered L x = true.
Proof.
  intros p L x Hp Hx. unfold page_in_ranges in Hp. apply existsb_exists in Hp as (r & Hin & Hr).
  apply andb_prop in Hr as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. unfold page_size in H2.
  unfold covered. apply existsb_exists. exists r. split; [exact Hin|]. unfold in_iv, in_rng, B, S.
  apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
Qed.

Lemma find_segment_In : forall segs x n seg, find_segment segs x n = Some seg ->
  In seg segs /\ Z.of_N (seg_base seg) <= x /\ x + n <= Z.of_N (seg_base seg) + Z.of_N (seg_size seg).
Proof.
  induction segs as [|s l IH]; intros x n seg H; cbn [find_segment] in H; [discriminate|].
  destruct (Z.of_N (seg_base s) <=? x)%Z eqn:E1, (x + n <=? Z.of_N (seg_base s) + Z.of_N (seg_size s))%Z eqn:E2; cbn in H;
    try (destruct (IH x n seg H) as (H1 & H2 & H3); split; [right; exact H1 | lia]).
  injection H as <-. apply Z.leb_le in E1, E2. split; [left; reflexivity | lia].
Qed.

Lemma seg_covered : forall segs x, segs_below_b segs 0x800000000000 = true -> 0 <= x ->
  find_segment segs x 1 <> None -> covered (segments_reserved segs) x = true.
Proof.
  intros segs x Hb Hx Hf. destruct (find_segment segs x 1) as [seg|] eqn:Hs; [|congruence].
  destruct (find_segment_In _ _ _ _ Hs) as (Hin & H1 & H2).
  unfold segs_below_b in Hb. rewrite forallb_forall in Hb. specialize (Hb seg Hin). apply Z.leb_le in Hb.
  unfold seg_top in Hb.
  unfold covered. apply existsb_exists. exists (segment_reservation seg). split; [apply in_map; exact Hin|].
  unfold segment_reservation, in_iv, in_rng, B, S, page_round_down_Z, page_round_up_Z, page_size. cbn [fst snd].
  set (b := Z.of_N (seg_base seg)) in *. set (k := Z.of_N (seg_size seg)) in *.
  assert (Hk : 0 <= k) by apply N2Z.is_nonneg. assert (Hb0 : 0 <= b) by apply N2Z.is_nonneg.
  pose proof (Z.mod_pos_bound b 4096 ltac:(lia)). pose proof (Z.div_mod b 4096 ltac:(lia)).
  pose proof (Z.mod_pos_bound (b + k + 4096 - 1) 4096 ltac:(lia)). pose proof (Z.div_mod (b + k + 4096 - 1) 4096 ltac:(lia)).
  rewrite !fg64' by (unfold two64; lia). apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
Qed.

(* [comment removed for export] *)
Lemma hoff_of : forall segs (L : list (word * word)) A (maps res : list (word * word)),
  segs_below_b segs 0x800000000000 = true -> res = segments_reserved segs ->
  (forall x, covered L x = true -> covered maps x = true) ->
  (forall x, covered maps x = true -> covered res x = false) ->
  H_off_segments segs (mkH L A).
Proof.
  intros segs L A maps res Hb Hres HL Hm w Hw. unfold mkH in Hw. apply andb_prop in Hw as [Hp _].
  destruct (pb_bounds w) as [Hpb _].
  assert (Hc : covered L (bv_unsigned w) = true) by exact (page_in_covered _ _ _ Hp Hpb).
  destruct (find_segment segs (bv_unsigned w) 1) as [seg|] eqn:Hs; [|reflexivity]. exfalso.
  assert (Hcr : covered (segments_reserved segs) (bv_unsigned w) = true).
  { apply seg_covered; [exact Hb | apply bv_unsigned_in_range | congruence]. }
  rewrite <- Hres in Hcr. rewrite (Hm _ (HL _ Hc)) in Hcr. discriminate.
Qed.

(* [comment removed for export] *)
Lemma iv_pts_disj : forall A1 s1 A2 s2, 0 < s1 -> 0 < s2 ->
  (forall w, A1 <= w < A1 + s1 -> A2 <= w < A2 + s2 -> False) -> A1 + s1 <= A2 \/ A2 + s2 <= A1.
Proof.
  intros A1 s1 A2 s2 H1 H2 H. destruct (Z_le_gt_dec (A1 + s1) A2) as [|Ha]; [left; exact l|].
  destruct (Z_le_gt_dec (A2 + s2) A1) as [|Hb]; [right; exact l|]. exfalso. apply (H (Z.max A1 A2)); lia.
Qed.

Lemma covered_cons : forall p l x, covered (p :: l) x = (in_iv p x || covered l x)%bool.
Proof. reflexivity. Qed.

Lemma in_iv_word : forall (a n : word) x, in_iv (a, n) x = ((bv_unsigned a <=? x) && (x <? bv_unsigned a + bv_unsigned n))%bool.
Proof. reflexivity. Qed.

Lemma page_allowedb_app_r : forall A1 A2 p, page_allowedb A2 p = true -> page_allowedb (A1 ++ A2) p = true.
Proof. intros A1 A2 p H. unfold page_allowedb in *. rewrite existsb_app, H, orb_true_r. reflexivity. Qed.

Lemma page_in_ranges_app : forall p l1 l2, page_in_ranges p (l1 ++ l2) = (page_in_ranges p l1 || page_in_ranges p l2)%bool.
Proof. intros. unfold page_in_ranges. apply existsb_app. Qed.

Lemma page_allowedb_app_l : forall A1 A2 p, page_allowedb A1 p = true -> page_allowedb (A1 ++ A2) p = true.
Proof. intros A1 A2 p H. unfold page_allowedb in *. rewrite existsb_app, H. reflexivity. Qed.

Lemma mkH_allowed : forall L A w, page_allowedb A (page_base w) = true -> mkH L A w = false.
Proof. intros L A w H. unfold mkH. rewrite H, andb_false_r. reflexivity. Qed.

Lemma mkH_notlazy : forall L A w, page_in_ranges (page_base w) L = false -> mkH L A w = false.
Proof. intros L A w H. unfold mkH. rewrite H. reflexivity. Qed.

Lemma mkH_grow : forall L1 L A1 A w, mkH L A w = false -> (page_in_ranges (page_base w) L1 = true -> False) ->
  mkH (L1 ++ L) (A1 ++ A) w = false.
Proof.
  intros L1 L A1 A w H H1. unfold mkH in *. rewrite page_in_ranges_app.
  destruct (page_in_ranges (page_base w) L1) eqn:E1; [exfalso; exact (H1 eq_refl)|]. cbn [orb].
  destruct (page_in_ranges (page_base w) L) eqn:E2; [|reflexivity]. cbn [andb] in *.
  apply negb_false_iff in H. rewrite (page_allowedb_app_r A1 A _ H). reflexivity.
Qed.

Lemma page_in_one : forall (a n w : word), page_in_ranges (page_base w) [(a, n)] = true ->
  bv_unsigned a <= bv_unsigned w < bv_unsigned a + bv_unsigned n.
Proof.
  intros a n w H. destruct (pb_bounds w) as [Hb _]. pose proof (page_in_covered _ _ _ H Hb) as Hc.
  rewrite covered_cons in Hc. cbn [covered existsb] in Hc. rewrite orb_false_r in Hc. rewrite in_iv_word in Hc.
  apply andb_prop in Hc as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. lia.
Qed.

(* [comment removed for export] *)
Lemma allow1_covers : forall E p y, 0 <= y < two64 -> uE E (fst p) <= y < uE E (fst p) + snd p ->
  page_allowedb [allow1 E p] (page_base (Z_to_bv 64 y)) = true.
Proof.
  intros E [b k] y Hy Hin. cbn [fst snd] in Hin. unfold page_allowedb, allow1, page_size. cbn [existsb fst snd]. rewrite orb_false_r.
  destruct (pb_bounds (Z_to_bv 64 y)) as [Hb Hal]. rewrite fg64' in Hb by exact Hy.
  set (p := bv_unsigned (page_base (Z_to_bv 64 y))) in *. set (u := uE E b) in *.
  pose proof (Z.mod_pos_bound u 4096 ltac:(lia)). pose proof (Z.div_mod u 4096 ltac:(lia)).
  pose proof (Z.mod_pos_bound (u + k + 4095) 4096 ltac:(lia)). pose proof (Z.div_mod (u + k + 4095) 4096 ltac:(lia)).
  pose proof (Z.div_mod p 4096 ltac:(lia)). rewrite Hal in *.
  apply andb_true_intro. split; apply Z.leb_le.
  - (* [comment removed for export] *)
    assert (u / 4096 * 4096 < p + 4096) by lia.
    assert (u / 4096 <= p / 4096) by lia. lia.
  - assert (p < (u + k + 4095) / 4096 * 4096) by lia.
    assert (p / 4096 < (u + k + 4095) / 4096) by lia. lia.
Qed.

Lemma A_wf_map_allow1 : forall E X, Forall (fun p => 0 <= snd p) X -> A_wf (List.map (allow1 E) X).
Proof. intros E X H. unfold A_wf. apply Forall_map. eapply Forall_impl; [|exact H]. intros p Hp. exact (allow1_wf E p Hp). Qed.

(* [comment removed for export] *)
Definition twf (n : positive) (t : list (positive * Z)) : bool := forallb (fun '(x, _) => Pos.ltb x n) t.

Lemma tadd_wf : forall n a b, twf n a = true -> twf n b = true -> twf n (tadd a b) = true.
Proof.
  intros n a. induction a as [|[x kx] a IHa]; intros b Ha Hb; [exact Hb|].
  cbn [twf forallb] in Ha. apply andb_prop in Ha as [Hx Ha].
  induction b as [|[y ky] b IHb]; [rewrite tadd_nil_r; cbn [twf forallb]; rewrite Hx; exact Ha|].
  cbn [twf forallb] in Hb. apply andb_prop in Hb as [Hy Hb].
  rewrite tadd_cons_cons. destruct (Pos.compare x y); cbv zeta.
  - destruct (Z.eqb (w64 (kx + ky)) 0); [apply IHa; [exact Ha | exact Hb]|]. cbn [twf forallb]. rewrite Hx. apply IHa; [exact Ha | exact Hb].
  - cbn [twf forallb]. rewrite Hx. apply IHa; [exact Ha|]. cbn [twf forallb]. rewrite Hy. exact Hb.
  - cbn [twf forallb]. rewrite Hy. apply IHb. exact Hb.
Qed.

Lemma tscale_wf : forall n k t, twf n t = true -> twf n (tscale k t) = true.
Proof.
  intros n k t. induction t as [|[x c] t IH]; intros H; [reflexivity|]. cbn [twf forallb] in H. apply andb_prop in H as [Hx Ht].
  cbn [tscale]. cbv zeta. destruct (Z.eqb (w64 (k * c)) 0); [apply IH; exact Ht|]. cbn [twf forallb]. rewrite Hx. apply IH. exact Ht.
Qed.

Lemma lwf_ladd : forall n a b, lwf n a = true -> lwf n b = true -> lwf n (ladd a b) = true.
Proof. intros n a b Ha Hb. unfold lwf, ladd in *. cbn [l_t]. apply (tadd_wf n); assumption. Qed.
Lemma lwf_lscale : forall n k a, lwf n a = true -> lwf n (lscale k a) = true.
Proof. intros n k a Ha. unfold lwf, lscale in *. cbn [l_t]. apply (tscale_wf n); assumption. Qed.
Lemma lwf_laddc : forall n a z, lwf n a = true -> lwf n (laddc a z) = true.
Proof. intros n a z Ha. unfold lwf, laddc in *. cbn [l_t]. exact Ha. Qed.
Lemma lwf_lvar : forall n x, (x < n)%positive -> lwf n (lvar x) = true.
Proof. intros n x H. unfold lwf, lvar. cbn. rewrite andb_true_r. apply Pos.ltb_lt. exact H. Qed.
Lemma lwf_lconst : forall n z, lwf n (lconst z) = true.
Proof. reflexivity. Qed.

Lemma sm_wf_cons : forall n M g al, sm_wf n M = true -> lwf n (fst (fst g)) = true -> lwf n (snd (fst g)) = true -> forallb (fun p => lwf n (fst p)) al = true ->
  sm_wf n (SM (g :: sm_maps M) (al ++ sm_allow M) (sm_zr M) (sm_tid M) (sm_brk M) (sm_sbrk M) (sm_sp M) (sm_frz M) []) = true.
Proof.
  intros n M g al H Hg Hgs Hal. unfold sm_wf in *. cbn [sm_maps sm_allow sm_tid sm_brk sm_sbrk sm_sp sm_own forallb].
  rewrite forallb_app, Hg, Hgs, Hal. cbn [andb]. rewrite andb_true_r. apply andb_prop in H as [H _]. exact H.
Qed.

Lemma sm_wf_cons_own : forall n M g al, sm_wf n M = true -> lwf n (fst (fst g)) = true -> lwf n (snd (fst g)) = true -> forallb (fun p => lwf n (fst p)) al = true ->
  sm_wf n (SM (g :: sm_maps M) (al ++ sm_allow M) (sm_zr M) (sm_tid M) (sm_brk M) (sm_sbrk M) (sm_sp M) (sm_frz M) (sm_own M)) = true.
Proof.
  intros n M g al H Hg Hgs Hal. unfold sm_wf in *. cbn [sm_maps sm_allow sm_tid sm_brk sm_sbrk sm_sp sm_own forallb].
  rewrite forallb_app, Hg, Hgs, Hal. cbn [andb]. exact H.
Qed.

Lemma rl_ok_mono : forall E model model' R,
  (forall x, covered (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model)) x = true ->
             covered (vm_reserved (m_vmmaps model') ++ vm_maps (m_vmmaps model')) x = true) ->
  (forall x, covered (vm_maps (m_vmmaps model)) x = true -> covered (vm_maps (m_vmmaps model')) x = true) ->
  alloc_top (m_vmmaps model') = alloc_top (m_vmmaps model) ->
  rl_ok E model R -> rl_ok E model' R.
Proof.
  intros E model model' R H1 H2 H3 [Hpos [Happ | (Hoff & HX & Hpc)]]; split; [exact Hpos| |exact Hpos|].
  - left. intros w Hw. destruct (Happ w Hw) as (Hc & Hs & Hb). split; [|split; assumption].
    rewrite (atop_pg_eq _ _ H3). destruct Hc as [Hc|Hc]; [left; exact (H1 w Hc) | right; exact Hc].
  - right. split; [exact Hoff|]. split.
    + intros x Hx. destruct (HX x Hx) as (Hc & Hs & Hb). split; [|split; assumption].
      rewrite (atop_pg_eq _ _ H3). destruct Hc as [Hc|Hc]; [left; exact (H1 x Hc) | right; exact Hc].
    + intros w Hw. destruct (Hpc w Hw) as [Hs Hc]. split; [exact Hs | exact (H2 w Hc)].
Qed.

Lemma rl_ok_agree : forall n E E' model R, lwf n (rg_base R) = true -> lwf n (rg_size R) = true -> agree n E E' ->
  rl_ok E model R -> rl_ok E' model R.
Proof.
  intros n E E' model R Hb Hs Ha H. unfold rl_ok, uE, rsz in *. rewrite (lden_agree_wf n E E' _ Hb Ha), (lden_agree_wf n E E' _ Hs Ha). exact H.
Qed.

(* [comment removed for export] *)
Lemma rg_ok_fresh_rz_gen : forall segs E m (b sz : lin),
  uE E b + bv_unsigned (lden E sz) <= two64 ->
  (forall i, 0 <= i < bv_unsigned (lden E sz) -> m (Z_to_bv 64 (uE E b + i)) = Some (Z_to_bv 8 0)) ->
  rg_ok segs E m (RG b sz RZ TEmpty).
Proof.
  intros segs E m b sz Hw Hz. unfold rg_ok, rsz. cbn [rg_base rg_size rg_kind rg_cont]. unfold uE in *.
  split; [apply bv_unsigned_in_range|]. split; [exact Hw|]. split.
  - intros i Hi. specialize (Hz i Hi). unfold rd1, wview. rewrite Hz. split; [split; discriminate|]. intros _. reflexivity.
  - intros p v Hp. rewrite tget_empty in Hp. discriminate.
Qed.
