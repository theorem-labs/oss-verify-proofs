(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec ShapeSet RealizesCfg FxLin FxCore FxSound FxMem FxFacts FxSubst FxEnt FxDrv.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require Import FxBacking FxChDen FxChLib FxChSep FxChMain.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require Import AXG_put AXG_np AXG_nf1 AXG_npf.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcPri.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcDepDen AcCarve AcFacts AcAst.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcHA.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcHA AcPri.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcPriSepOk.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcPriSepOk AcMALp AcMALlib AcNPop.
Import OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcPri.AcDepSep OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcDepDen OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcCarve OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcFacts OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcAst OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcHA.AcLv OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcHA OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcPri OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcPriSepOk.AcPriSep OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcPriSepOk OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcMALp OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcMALlib OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcNPop.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition with_live (a : ast) (live : list (lin * lin)) : ast :=
  AST (a_on a) (a_rgs a) (a_fcts a) (a_own a) (a_dep a) (a_nl a) live (a_pri a).
Definition cacheable (fs : list fact) (gs : list (lin * lin * gkind)) (res : list (word * word)) (jP jT : nat) (sp : lin) (a : ast) (R : region) : bool :=
  negb (sep_cached a R) &&& negb (ext_in fs a R) &&& pri_sep_t fs gs res jP jT sp a R.
(* [comment removed for export] *)
Definition cache_new (fs : list fact) (gs : list (lin * lin * gkind)) (res : list (word * word)) (jP jT : nat) (sp : lin) (a : ast) (dc : region -> bool) (rgs : list region) : list (lin * lin) :=
  List.map (fun R => (rg_base R, rg_size R)) (List.filter (fun R => cacheable fs gs res jP jT sp a R &&& dc R) rgs).
Definition cache_hdr_ok (a : ast) : bool :=
  a_on a &&& Nat.eqb (List.length (a_pri a)) PRI_LEN &&& Nat.leb (lv_cnt a) (List.length (a_live a)).
Definition apost_cacheadd (S : sst) (M : smodel) (a : ast) : option (sst * smodel * ast) :=
  obool (cache_hdr_ok a) (
  obind (find_grant (sm_maps M) (p_pg a) PG_SIZE) (fun jP =>
  obind (find_grant (sm_maps M) (p_tg a) TG_SIZE) (fun jT =>
  obind (find_grant (sm_maps M) (fst (a_dep a)) 1048576) (fun jD1 =>
  obind (find_grant (sm_maps M) (snd (a_dep a)) 8388608) (fun jB1 =>
  let nsD := sep_noshadow_b (s_facts S) (RGz (fst (a_dep a)) 1048576 RZ TEmpty) in
  let nsB := sep_noshadow_b (s_facts S) (RGz (snd (a_dep a)) 8388608 RZ TEmpty) in
  Some (S, M, with_live a (cache_new (s_facts S) (sm_maps M) ASEGSR jP jT (sm_sp M) a (dep_cacheable (s_facts S) M a jD1 jB1 nsD nsB) (s_rgs S) ++ a_live a))))))).
Definition apost_cachedrop (n : nat) (S : sst) (M : smodel) (a : ast) : option (sst * smodel * ast) :=
  obool (cache_hdr_ok a &&& Nat.leb (n + lv_cnt a) (List.length (a_live a))) (Some (S, M, with_live a (skipn n (a_live a)))).
(* [comment removed for export] *)
Definition apost_cachekeep (k : nat) (S : sst) (M : smodel) (a : ast) : option (sst * smodel * ast) :=
  obool (Nat.leb (lv_cnt a) k &&& Nat.leb k (List.length (a_live a))) (apost_cachedrop (List.length (a_live a) - k) S M a).

(* [comment removed for export] *)
Lemma lv_pairs_prefix : forall a l, (lv_cnt a <= List.length (a_live a))%nat -> lv_pairs (with_live a (l ++ a_live a)) = lv_pairs a.
Proof.
  intros a l H. unfold lv_pairs, lv_cnt, with_live in *. cbn [a_live a_fcts]. rewrite length_app.
  replace (List.length l + List.length (a_live a) - List.length (a_fcts a))%nat with (List.length l + (List.length (a_live a) - List.length (a_fcts a)))%nat by lia.
  rewrite skipn_app. rewrite skipn_all2 by lia. cbn [app].
  replace (List.length l + (List.length (a_live a) - List.length (a_fcts a)) - List.length l)%nat with (List.length (a_live a) - List.length (a_fcts a))%nat by lia. reflexivity.
Qed.
Lemma lv_pairs_skipn : forall a n, (n + lv_cnt a <= List.length (a_live a))%nat -> lv_pairs (with_live a (skipn n (a_live a))) = lv_pairs a.
Proof.
  intros a n H. unfold lv_pairs, lv_cnt, with_live in *. cbn [a_live a_fcts]. rewrite length_skipn, skipn_skipn. f_equal. lia.
Qed.

Section Cache.
Variable cfg : SpuriousCfg.
Variable LIMIT : Z.
Variable model0 : Model.

(* [comment removed for export] *)
#[using="Type"] Lemma HA_with_live : forall E M a m0 live, a_on a = true -> a_pri a <> [] -> HA E M a m0 ->
  lv_pairs (with_live a live) = lv_pairs a ->
  (forall p, In p live -> uE E (fst p) + uE E (snd p) <= two64 /\
     forall x, uE E (fst p) <= x < uE E (fst p) + uE E (snd p) -> ~ FPmax (pden E a) x) ->
  (forall p, In p live -> forall x, uE E (fst p) <= x < uE E (fst p) + uE E (snd p) -> ~ downed (dD1 E a) (dB1 E a) x) ->
  HA E M (with_live a live) m0.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E M a m0 live Hon Hne HHA Hlp Hnew Hnewd _. destruct (HHA Hon) as [Hdep Hown Haown Hhi Hg1 Hg2 Hpri].
  constructor; try assumption. intros _. destruct (Hpri Hne) as [Hi Ho Hp Ht Hz Hs Hxt Hlv Hsd].
  constructor; try assumption.
  apply (lv_inv_mono E E a (with_live a live) m0 m0); [| reflexivity | intros b z H; exact H | intros b z _ x _; reflexivity | exact Hlv].
  intros i. unfold lv_nth, lv_car. rewrite Hlp. reflexivity.
Qed.

#[using="Type"] Theorem ncacheadd_node : forall S M a S' M' a', apost_cacheadd S M a = Some (S', M', a') ->
  forall mem0 E ms model T, DEN ASEGS LIMIT model0 mem0 E S M ms model -> awf (s_next S) a = true -> HA E M a mem0 ->
  (forall E' mem0' ms' model', agree (s_next S) E E' -> frz_same E M mem0 mem0' -> DEN ASEGS LIMIT model0 mem0' E' S' M' ms' model' ->
     HA E' M' a' mem0' -> realizes_cfg ASEGS cfg (mkCfg ms' model') T) ->
  realizes_cfg ASEGS cfg (mkCfg ms model) T.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros S M a S' M' a' H mem0 E ms model T Hd Haw HHA Hk. unfold apost_cacheadd in H.
  apply obool_some in H as (Hc & H). apply obind_some in H as (jP & HjP & H). cbv beta in H. apply obind_some in H as (jT & HjT & H). cbv beta in H.
  apply obind_some in H as (jD1 & HjD1 & H). cbv beta in H. apply obind_some in H as (jB1 & HjB1 & H). cbv beta zeta in H.
  injection H as <- <- <-.
  unfold cache_hdr_ok in Hc. destruct (a_on a) eqn:Hon; [|discriminate]. destruct (Nat.eqb (List.length (a_pri a)) PRI_LEN) eqn:Hlen; [|discriminate].
  apply Nat.leb_le in Hc. apply Nat.eqb_eq in Hlen.
  assert (Hne : a_pri a <> []) by (intros Hn; rewrite Hn in Hlen; discriminate).
  pose proof (HHA Hon) as HA0. pose proof (ha_pri _ _ _ _ HA0 Hne) as HP0. pose proof (po_inv _ _ _ _ HP0) as HI. unfold INV_A in HI.
  pose proof (sden_0 _ _ _ _ (dn_sden _ _ _ _ _ _ _ _ _ Hd)) as (_ & _ & _ & _ & HRG & _ & HF0 & _). rewrite Forall_forall in HRG.
  destruct (find_grant_sound _ _ _ _ HjP) as (kp & Hgp). destruct (find_grant_sound _ _ _ _ HjT) as (kt & Hgt).
  apply (Hk E mem0 ms model); [apply agree_refl | intros p Hp w Hw; reflexivity | exact Hd |].
  apply HA_with_live; [exact Hon | exact Hne | exact HHA | apply lv_pairs_prefix; exact Hc | |].
  2:{ intros p Hp. apply in_app_or in Hp as [Hp|Hp]; [|exact (po_sepd _ _ _ _ HP0 p Hp)].
      unfold cache_new in Hp. apply in_map_iff in Hp as (R & <- & HRf). apply filter_In in HRf as [HR Hck]. cbn [fst snd].
      destruct (cacheable (s_facts S) (sm_maps M) ASEGSR jP jT (sm_sp M) a R); [|discriminate]. cbv iota in Hck.
      pose proof (HRG R HR) as (Hz0 & Hz1 & _). fold (rsz E R).
      exact (dep_cacheable_pts LIMIT model0 mem0 E S M ms model a mem0 jD1 jB1 R Hd HA0 HjD1 HjB1 Hz0 Hz1 Hck). }
  intros p Hp. apply in_app_or in Hp as [Hp|Hp]; [|exact (po_sep _ _ _ _ HP0 p Hp)].
  unfold cache_new in Hp. apply in_map_iff in Hp as (R & <- & HRf). apply filter_In in HRf as [HR Hck]. cbn [fst snd].
  destruct (cacheable (s_facts S) (sm_maps M) ASEGSR jP jT (sm_sp M) a R) eqn:Hck0; [|discriminate]. clear Hck. rename Hck0 into Hck.
  unfold cacheable in Hck. destruct (negb (sep_cached a R)); [|discriminate]. destruct (ext_in (s_facts S) a R) eqn:Hx; [discriminate|]. cbn [negb] in Hck.
  pose proof (HRG R HR) as (Hz0 & Hz1 & _). fold (rsz E R). split; [exact Hz1|].
  destruct (pri_sep_t_route E (s_facts S) (sm_maps M) model (sm_sp M) _ HF0 (dn_maps _ _ _ _ _ _ _ _ _ Hd) (dn_pd _ _ _ _ _ _ _ _ _ Hd)
              (dn_gsh _ _ _ _ _ _ _ _ _ Hd) (dn_gtop _ _ _ _ _ _ _ _ _ Hd) (dn_sp _ _ _ _ _ _ _ _ _ Hd) (proj2 (dn_spok _ _ _ _ _ _ _ _ _ Hd))
              (proj1 (dn_spok _ _ _ _ _ _ _ _ _ Hd)) (dn_mres _ _ _ _ _ _ _ _ _ Hd) ASEGSR (dn_res _ _ _ _ _ _ _ _ _ Hd) gq_res a mem0 HI jP jT _ _
              Hgp eq_refl eq_refl Hgt eq_refl eq_refl (po_sep _ _ _ _ HP0) R Hz0 Hz1 Hck) as [X|X]; [exact X | rewrite X in Hx; discriminate].
Qed.

#[using="Type"] Theorem ncachedrop_node : forall n S M a S' M' a', apost_cachedrop n S M a = Some (S', M', a') ->
  forall mem0 E ms model T, DEN ASEGS LIMIT model0 mem0 E S M ms model -> awf (s_next S) a = true -> HA E M a mem0 ->
  (forall E' mem0' ms' model', agree (s_next S) E E' -> frz_same E M mem0 mem0' -> DEN ASEGS LIMIT model0 mem0' E' S' M' ms' model' ->
     HA E' M' a' mem0' -> realizes_cfg ASEGS cfg (mkCfg ms' model') T) ->
  realizes_cfg ASEGS cfg (mkCfg ms model) T.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros n S M a S' M' a' H mem0 E ms model T Hd Haw HHA Hk. unfold apost_cachedrop in H.
  apply obool_some in H as (Hc & H). injection H as <- <- <-.
  destruct (cache_hdr_ok a) eqn:Hh; [|discriminate]. apply Nat.leb_le in Hc.
  unfold cache_hdr_ok in Hh. destruct (a_on a) eqn:Hon; [|discriminate]. destruct (Nat.eqb (List.length (a_pri a)) PRI_LEN) eqn:Hlen; [|discriminate].
  apply Nat.eqb_eq in Hlen. assert (Hne : a_pri a <> []) by (intros Hn; rewrite Hn in Hlen; discriminate).
  pose proof (HHA Hon) as HA0. pose proof (ha_pri _ _ _ _ HA0 Hne) as HP0.
  apply (Hk E mem0 ms model); [apply agree_refl | intros p Hp w Hw; reflexivity | exact Hd |].
  apply HA_with_live; [exact Hon | exact Hne | exact HHA | apply lv_pairs_skipn; exact Hc | |].
  - intros p Hp. apply (po_sep _ _ _ _ HP0 p). rewrite <- (firstn_skipn n (a_live a)). apply in_or_app. right. exact Hp.
  - intros p Hp. apply (po_sepd _ _ _ _ HP0 p). rewrite <- (firstn_skipn n (a_live a)). apply in_or_app. right. exact Hp.
Qed.

#[using="Type"] Theorem ncachekeep_node : forall k S M a S' M' a', apost_cachekeep k S M a = Some (S', M', a') ->
  forall mem0 E ms model T, DEN ASEGS LIMIT model0 mem0 E S M ms model -> awf (s_next S) a = true -> HA E M a mem0 ->
  (forall E' mem0' ms' model', agree (s_next S) E E' -> frz_same E M mem0 mem0' -> DEN ASEGS LIMIT model0 mem0' E' S' M' ms' model' ->
     HA E' M' a' mem0' -> realizes_cfg ASEGS cfg (mkCfg ms' model') T) ->
  realizes_cfg ASEGS cfg (mkCfg ms model) T.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros k S M a S' M' a' H. unfold apost_cachekeep in H. apply obool_some in H as (_ & H).
  exact (ncachedrop_node _ S M a S' M' a' H).
Qed.
End Cache.
(* [comment removed for export] *)
