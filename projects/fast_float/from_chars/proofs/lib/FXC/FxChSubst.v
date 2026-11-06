(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Monad Run Specs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require PropExec ShapeSet RealizesCfg AsanAcct FxLin FxCore FxSound FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSubst FxEnt FxLoop.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.PropExec OSSVerify.Proofs.fast_float.from_chars.lib.Common.ShapeSet OSSVerify.Proofs.fast_float.from_chars.lib.Common.RealizesCfg OSSVerify.Proofs.fast_float.from_chars.lib.Common.AsanAcct OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEnt OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require Import FxBacking FxChDen FxChLib FxChain FxChEnt FxChEntM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition rsubst (σ : tree lin) (R : region) : region := RG (lsubst σ (rg_base R)) (lsubst σ (rg_size R)) (rg_kind R) (tmap (bsubst σ) (rg_cont R)).
Definition rvsubst (σ : tree lin) (r : rsv) : rsv := match r with RAt l => RAt (lsubst σ l) | x => x end.
Definition ssubst (σ : tree lin) (n : positive) (F : sst) : sst :=
  SST (s_pc F) (tmap (lsubst σ) (s_regs F)) (List.map (rsubst σ) (s_rgs F)) (List.map (fsubst σ) (s_facts F)) n (rvsubst σ (s_resv F)).

Lemma lsubst_lc0 : forall σ, lsubst σ lc0 = lc0.
Proof. intros σ. reflexivity. Qed.
Lemma rget_tmap_sub : forall σ R k, rget (tmap (lsubst σ) R) k = lsubst σ (rget R k).
Proof.
  intros σ R k. unfold rget. destruct k as [k|k|]; [| |reflexivity]; rewrite tget_tmap; destruct (tget _ R); reflexivity.
Qed.
Lemma rsz_sub : forall E σ R, rsz E (rsubst σ R) = rsz (ecomp E σ) R.
Proof. intros E σ R. unfold rsz, rsubst. cbn [rg_size]. rewrite lden_lsubst. reflexivity. Qed.
Lemma base_sub : forall E σ R, lden E (rg_base (rsubst σ R)) = lden (ecomp E σ) (rg_base R).
Proof. intros E σ R. unfold rsubst. cbn [rg_base]. apply lden_lsubst. Qed.
Lemma uE_base_sub : forall E σ R, uE E (rg_base (rsubst σ R)) = uE (ecomp E σ) (rg_base R).
Proof. intros E σ R. unfold uE. rewrite base_sub. reflexivity. Qed.

Section Sub.
Variable segs : list Segment.

#[using="Type"] Lemma rg_ok_sub : forall E σ m R, rg_ok segs E m (rsubst σ R) <-> rg_ok segs (ecomp E σ) m R.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E σ m R. unfold rg_ok. rewrite rsz_sub, base_sub. cbn [rg_kind rsubst rg_cont]. split.
  - intros (H1 & H2 & H3 & H4). split; [exact H1|]. split; [exact H2|]. split.
    + intros i Hi. specialize (H3 i Hi). destruct (rg_kind R); try exact H3.
      * destruct H3 as [Hv Hz]. split; [exact Hv|]. intros Hn. apply Hz. rewrite tget_tmap, Hn. reflexivity.
      * destruct H3 as [Hv Hz]. split; [exact Hv|]. intros Hn. apply Hz. rewrite tget_tmap, Hn. reflexivity.
    + intros p v Hp. destruct (H4 p (bsubst σ v) ltac:(rewrite tget_tmap, Hp; reflexivity)) as [Hlt Hrd].
      split; [exact Hlt|]. rewrite Hrd. f_equal. apply bden_bsubst.
  - intros (H1 & H2 & H3 & H4). split; [exact H1|]. split; [exact H2|]. split.
    + intros i Hi. specialize (H3 i Hi). destruct (rg_kind R); try exact H3.
      * destruct H3 as [Hv Hz]. split; [exact Hv|]. intros Hn. apply Hz. rewrite tget_tmap in Hn. destruct (tget (okey i) (rg_cont R)); [discriminate | reflexivity].
      * destruct H3 as [Hv Hz]. split; [exact Hv|]. intros Hn. apply Hz. rewrite tget_tmap in Hn. destruct (tget (okey i) (rg_cont R)); [discriminate | reflexivity].
    + intros p v Hp. rewrite tget_tmap in Hp. destruct (tget p (rg_cont R)) as [v0|] eqn:Hp0; [|discriminate].
      injection Hp as <-. destruct (H4 p v0 Hp0) as [Hlt Hrd]. split; [exact Hlt|]. rewrite Hrd. f_equal. symmetry. apply bden_bsubst.
Qed.
End Sub.

Lemma rg_disj_sub : forall E σ R1 R2, rg_disj E (rsubst σ R1) (rsubst σ R2) <-> rg_disj (ecomp E σ) R1 R2.
Proof. intros E σ R1 R2. unfold rg_disj. rewrite !rsz_sub, !base_sub. reflexivity. Qed.
Lemma rgs_disj_sub : forall E σ rgs, rgs_disj E (List.map (rsubst σ) rgs) <-> rgs_disj (ecomp E σ) rgs.
Proof.
  intros E σ rgs. induction rgs as [|R rs IH]; cbn [List.map rgs_disj]; [tauto|]. rewrite IH. rewrite Forall_map.
  split; intros [H1 H2]; split; try exact H2; rewrite Forall_forall in *; intros R' HR'; apply rg_disj_sub; exact (H1 R' HR').
Qed.
Lemma regs_ok_sub : forall E σ R regs, regs_ok E (tmap (lsubst σ) R) regs <-> regs_ok (ecomp E σ) R regs.
Proof.
  intros E σ R regs. unfold regs_ok. split; intros H r; rewrite (H r).
  - rewrite rget_tmap_sub, lden_lsubst. reflexivity.
  - rewrite rget_tmap_sub, lden_lsubst. reflexivity.
Qed.
Lemma rsv_ok_sub : forall E σ r v, rsv_ok E (rvsubst σ r) v <-> rsv_ok (ecomp E σ) r v.
Proof. intros E σ [|l|] v; cbn [rvsubst rsv_ok]; [tauto | rewrite lden_lsubst; tauto | tauto]. Qed.
Lemma facts_sub : forall E σ fs, Forall (fact_ok E) (List.map (fsubst σ) fs) <-> Forall (fact_ok (ecomp E σ)) fs.
Proof.
  intros E σ fs. rewrite Forall_map. split; intros H; rewrite Forall_forall in *; intros f Hf; apply fact_ok_fsubst; exact (H f Hf).
Qed.
Lemma outside_sub : forall E σ rgs x, outside E (List.map (rsubst σ) rgs) x <-> outside (ecomp E σ) rgs x.
Proof.
  intros E σ rgs x. unfold outside. rewrite Forall_map.
  split; intros H; rewrite Forall_forall in *; intros R HR; specialize (H R HR); rewrite ?rsz_sub, ?base_sub in *; exact H.
Qed.

(* [comment removed for export] *)
Definition sig_wf (σ : tree lin) (m n : positive) : Prop := forall x, (x < m)%positive -> lwf n (svar σ x) = true.
Lemma lwf_tsubst : forall σ m n t, sig_wf σ m n -> forallb (fun '(x, _) => Pos.ltb x m) t = true -> lwf n (tsubst σ t) = true.
Proof.
  intros σ m n t Hs. induction t as [|[x k] t IH]; intros Ht; [reflexivity|]. cbn [forallb] in Ht. apply andb_prop in Ht as [Hx Ht].
  apply Pos.ltb_lt in Hx. cbn [tsubst]. apply lwf_ladd; [apply lwf_lscale; exact (Hs x Hx) | exact (IH Ht)].
Qed.
Lemma lwf_lsubst : forall σ m n l, sig_wf σ m n -> lwf m l = true -> lwf n (lsubst σ l) = true.
Proof. intros σ m n l Hs Hl. unfold lsubst. apply lwf_laddc. exact (lwf_tsubst σ m n (l_t l) Hs Hl). Qed.

(* [comment removed for export] *)
Section Sden.
Variable segs : list Segment.
#[using="Type"] Lemma sden0_sub : forall E σ n F ms, sden0 segs E (ssubst σ n F) ms <-> sden0 segs (ecomp E σ) F ms.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E σ n F ms. unfold sden0, ssubst. cbn [s_pc s_regs s_rgs s_facts s_resv].
  rewrite rsv_ok_sub, regs_ok_sub, rgs_disj_sub, facts_sub. rewrite Forall_map.
  assert (HG : Forall (fun R => rg_ok segs E (ms_mem ms) (rsubst σ R)) (s_rgs F) <-> Forall (rg_ok segs (ecomp E σ) (ms_mem ms)) (s_rgs F)).
  { split; intros H; rewrite Forall_forall in *; intros R HR; apply (rg_ok_sub segs); exact (H R HR). }
  rewrite HG. reflexivity.
Qed.
#[using="Type"] Lemma sden_sub : forall E σ n F ms, sig_wf σ (s_next F) n -> sden segs (ecomp E σ) F ms -> sden segs E (ssubst σ n F) ms.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E σ n F ms Hs Hd E' Ha'. apply sden0_sub. apply Hd.
  intros x Hx. unfold ecomp. exact (lden_agree n E E' (svar σ x) (Hs x Hx) Ha').
Qed.
End Sden.

(* [comment removed for export] *)
Lemma sm_wf_msubst : forall σ m n M, sig_wf σ m n -> sm_wf m M = true -> sm_wf n (msubst σ M) = true.
Proof.
  intros σ m n M Hs Hw. unfold sm_wf, msubst in *. cbn [sm_maps sm_allow sm_tid sm_brk sm_sbrk sm_sp sm_frz sm_own].
  apply andb_prop in Hw as [Hw Ho]. apply andb_prop in Hw as [Hw Hf]. apply andb_prop in Hw as [Hw Hsp]. apply andb_prop in Hw as [Hw Hsb].
  apply andb_prop in Hw as [Hw Hb]. apply andb_prop in Hw as [Hw Ht]. apply andb_prop in Hw as [Hm Ha].
  rewrite forallb_forall in Hm, Ha, Hf, Ho.
  repeat (apply andb_true_intro; split).
  - rewrite forallb_forall. intros g Hg. apply in_map_iff in Hg as (g0 & <- & Hg0). specialize (Hm g0 Hg0). apply andb_prop in Hm as [W1 W2].
    unfold gsubst. cbn [fst snd]. rewrite (lwf_lsubst σ m n _ Hs W1), (lwf_lsubst σ m n _ Hs W2). reflexivity.
  - rewrite forallb_forall. intros g Hg. apply in_map_iff in Hg as (g0 & <- & Hg0). specialize (Ha g0 Hg0).
    unfold psubst. cbn [fst]. exact (lwf_lsubst σ m n _ Hs Ha).
  - destruct (sm_tid M) as [l|]; cbn [option_map]; [exact (lwf_lsubst σ m n _ Hs Ht) | reflexivity].
  - exact (lwf_lsubst σ m n _ Hs Hb).
  - exact (lwf_lsubst σ m n _ Hs Hsb).
  - exact (lwf_lsubst σ m n _ Hs Hsp).
  - rewrite forallb_forall. intros p Hp. apply in_map_iff in Hp as (p0 & <- & Hp0). specialize (Hf p0 Hp0). apply andb_prop in Hf as [W1 W2].
    unfold ppsubst. cbn [fst snd]. rewrite (lwf_lsubst σ m n _ Hs W1), (lwf_lsubst σ m n _ Hs W2). reflexivity.
  - rewrite forallb_forall. intros p Hp. apply in_map_iff in Hp as (p0 & <- & Hp0). specialize (Ho p0 Hp0). apply andb_prop in Ho as [W1 W2].
    unfold ppsubst. cbn [fst snd]. rewrite (lwf_lsubst σ m n _ Hs W1), (lwf_lsubst σ m n _ Hs W2). reflexivity.
Qed.
Lemma bases_wf_rsubst : forall σ m n rgs, sig_wf σ m n -> bases_wf m rgs = true -> bases_wf n (List.map (rsubst σ) rgs) = true.
Proof.
  intros σ m n rgs Hs Hw. unfold bases_wf in *. rewrite forallb_forall in *. intros R HR. apply in_map_iff in HR as (R0 & <- & HR0).
  specialize (Hw R0 HR0). apply andb_prop in Hw as [W1 W2]. unfold rsubst. cbn [rg_base rg_size].
  rewrite (lwf_lsubst σ m n _ Hs W1), (lwf_lsubst σ m n _ Hs W2). reflexivity.
Qed.
Lemma rl_ok_sub : forall E σ model R, rl_ok (ecomp E σ) model R -> rl_ok E model (rsubst σ R).
Proof. intros E σ model R H. unfold rl_ok in *. rewrite rsz_sub, uE_base_sub. exact H. Qed.

Section DenSub.
Variable segs : list Segment.
Variable LIMIT : Z.
Variable model0 : Model.
Variable mem0 : word -> option byte.

(* [comment removed for export] *)
#[using="Type"] Theorem den_subst : forall E σ F MF n ms model, sig_wf σ (s_next F) n -> marks_ok σ (sm_maps MF) = true ->
  DEN segs LIMIT model0 mem0 (ecomp E σ) F MF ms model -> DEN segs LIMIT model0 mem0 E (ssubst σ n F) (msubst σ MF) ms model.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E σ F MF n ms model Hs Hmk Hd.
  destruct Hd as [Hsd Hwf Hbw Hh Hawf Hanz Hminv Hhoff Hres Hlim Hsp Hspok Hbrk Hsbrk Htid Hmaps Hgsh Hgtop Hivwf Hpd Hmres Hkind Hlzm Hzrsh Hzrm Hzr Hrl Hvmo Hproc Hfrz Hrom Hown Hblob].
  assert (HA : allowA (ecomp E σ) MF = allowA E (msubst σ MF)) by exact (allowA_sub E σ MF).
  assert (HH : Hof (ecomp E σ) MF model = Hof E (msubst σ MF) model) by exact (Hof_sub E σ MF model).
  constructor.
  - rewrite <- HH. exact (sden_sub segs E σ n F _ Hs Hsd).
  - exact (sm_wf_msubst σ (s_next F) n MF Hs Hwf).
  - exact (bases_wf_rsubst σ (s_next F) n (s_rgs F) Hs Hbw).
  - exact Hh.
  - rewrite <- HA. exact Hawf.
  - unfold msubst. cbn [sm_allow]. rewrite Forall_map. rewrite Forall_forall in *. intros p Hp. exact (Hanz p Hp).
  - rewrite <- (AM_sub model0 E σ MF). exact Hminv.
  - rewrite <- HH. exact Hhoff.
  - exact Hres.
  - exact Hlim.
  - rewrite Hsp. unfold msubst. cbn [sm_sp]. rewrite lden_lsubst. reflexivity.
  - exact Hspok.
  - rewrite Hbrk. unfold msubst. cbn [sm_brk]. rewrite lden_lsubst. reflexivity.
  - rewrite Hsbrk. unfold msubst. cbn [sm_sbrk]. rewrite lden_lsubst. reflexivity.
  - rewrite Htid. unfold msubst. cbn [sm_tid]. destruct (sm_tid MF) as [l|]; [cbn; f_equal; rewrite lden_lsubst; reflexivity | reflexivity].
  - rewrite Hmaps. unfold msubst. cbn [sm_maps]. exact (lden_maps_sub E σ _ _ Hmk).
  - unfold msubst. cbn [sm_maps]. rewrite Forall_map. rewrite Forall_forall in *. intros g Hg. specialize (Hgsh g Hg).
    unfold gshape_ok, gsz, gsubst in *. cbn [fst snd] in *. rewrite <- !uE_sub. exact Hgsh.
  - unfold msubst. cbn [sm_maps]. rewrite Forall_map. rewrite Forall_forall in *. intros g Hg. specialize (Hgtop g Hg).
    unfold gsz, gsubst in *. cbn [fst snd] in *. rewrite <- !uE_sub. exact Hgtop.
  - exact Hivwf.
  - exact Hpd.
  - exact Hmres.
  - unfold msubst. cbn [sm_maps]. rewrite Forall_map. rewrite Forall_forall in *. intros g Hg. specialize (Hkind g Hg).
    unfold kind_ok in *. rewrite <- gden_sub. unfold gsubst. cbn [snd]. exact Hkind.
  - exact Hlzm.
  - exact Hzrsh.
  - exact Hzrm.
  - intros w Hw Hout Hnow Hnb. apply (Hzr w Hw).
    + apply (proj1 (outside_sub E σ (s_rgs F) _)). exact Hout.
    + intros Ho. apply Hnow. apply (proj1 (own_pt_sub E σ MF w)). exact Ho.
    + exact Hnb.
  - unfold ssubst. cbn [s_rgs]. rewrite Forall_map. rewrite Forall_forall in *. intros R HR. exact (rl_ok_sub E σ model R (Hrl R HR)).
  - exact Hvmo.
  - exact Hproc.
  - intros q Hq w Hw. unfold msubst in Hq. cbn [sm_frz] in Hq. apply in_map_iff in Hq as (p & <- & Hp).
    unfold ppsubst in Hw. cbn [fst snd] in Hw. rewrite <- !uE_sub in Hw.
    destruct (Hfrz p Hp w Hw) as (Htp & Hout & Hm). split; [exact Htp|]. split; [|exact Hm].
    unfold ssubst. cbn [s_rgs]. apply (proj2 (outside_sub E σ (s_rgs F) _)). exact Hout.
  - exact Hrom.
  - intros q Hq w Hw. unfold msubst in Hq. cbn [sm_own] in Hq. apply in_map_iff in Hq as (p & <- & Hp).
    unfold ppsubst in Hw. cbn [fst snd] in Hw. rewrite <- !uE_sub in Hw.
    destruct (Hown p Hp w Hw) as [Hv Hm]. split; [rewrite <- HH; exact Hv|]. intros Hout.
    apply Hm. unfold ssubst in Hout. cbn [s_rgs] in Hout. apply (proj1 (outside_sub E σ (s_rgs F) _)). exact Hout.
  - exact (blob_ok_sub_rev E σ MF model _ Hmk Hblob).
Qed.
End DenSub.

(* [comment removed for export] *)
Definition frz_covs (E : valu) (M : smodel) (E' : valu) (M' : smodel) : Prop :=
  forall p, In p (sm_frz M) -> exists p', In p' (sm_frz M') /\ uE E' (fst p') = uE E (fst p) /\ uE E' (snd p') = uE E (snd p).
Lemma frz_covs_trans : forall E1 M1 E2 M2 E3 M3, frz_covs E1 M1 E2 M2 -> frz_covs E2 M2 E3 M3 -> frz_covs E1 M1 E3 M3.
Proof.
  intros E1 M1 E2 M2 E3 M3 H12 H23 p Hp. destruct (H12 p Hp) as (q & Hq & Hq1 & Hq2). destruct (H23 q Hq) as (r & Hr & Hr1 & Hr2).
  exists r. split; [exact Hr|]. split; [rewrite Hr1; exact Hq1 | rewrite Hr2; exact Hq2].
Qed.
Lemma frz_covs_agree : forall n E E' M M', sm_wf n M = true -> agree n E E' -> sm_frz M' = sm_frz M -> frz_covs E M E' M'.
Proof.
  intros n E E' M M' Hwf Ha Hfz p Hp. exists p. split; [rewrite Hfz; exact Hp|].
  assert (Hw : lwf n (fst p) = true /\ lwf n (snd p) = true).
  { unfold sm_wf in Hwf. apply andb_prop in Hwf as [Hwf _]. apply andb_prop in Hwf as [_ Hfr].
    rewrite forallb_forall in Hfr. specialize (Hfr p Hp). cbv beta in Hfr. apply andb_prop in Hfr. exact Hfr. }
  unfold uE. rewrite (lden_agree_wf n E E' (fst p) (proj1 Hw) Ha), (lden_agree_wf n E E' (snd p) (proj2 Hw) Ha). split; reflexivity.
Qed.
Lemma frz_covs_msubst : forall E σ MP, frz_covs E (msubst σ MP) (ecomp E σ) MP.
Proof.
  intros E σ MP p Hp. unfold msubst in Hp. cbn [sm_frz] in Hp. apply in_map_iff in Hp as (q & <- & Hq).
  exists q. split; [exact Hq|]. unfold ppsubst. cbn [fst snd]. rewrite !uE_sub. split; reflexivity.
Qed.

(* [comment removed for export] *)
Definition use_val (σ : tree lin) (nb nT nS x : positive) : lin :=
  match (if Pos.ltb x nT then tget x σ else None) with Some l => l | None => lvar (Z.to_pos (Zpos x + Zpos nS - Zpos nb)) end.
Fixpoint use_acc (σ : tree lin) (nb nT nS : positive) (k : nat) (x : positive) (acc : tree lin) : tree lin :=
  match k with O => acc | Datatypes.S k' => use_acc σ nb nT nS k' (Pos.succ x) (tset x (use_val σ nb nT nS x) acc) end.
Definition use_sig (σ : tree lin) (nb nT nF nS : positive) : tree lin := use_acc σ nb nT nS (Pos.to_nat nF - Pos.to_nat nb) nb TEmpty.
Definition use_next (nb nF nS : positive) : positive := Z.to_pos (Zpos nS + Zpos nF - Zpos nb).

Lemma tget_use_acc : forall σ nb nT nS k x acc y,
  tget y (use_acc σ nb nT nS k x acc) = if (Z.leb (Zpos x) (Zpos y) && Z.ltb (Zpos y) (Zpos x + Z.of_nat k))%bool then Some (use_val σ nb nT nS y) else tget y acc.
Proof.
  intros σ nb nT nS k. induction k as [|k IH]; intros x acc y; cbn [use_acc].
  - destruct (Z.leb (Zpos x) (Zpos y) && Z.ltb (Zpos y) (Zpos x + Z.of_nat 0))%bool eqn:H; [|reflexivity]. apply andb_prop in H as [H1 H2].
    apply Z.leb_le in H1. apply Z.ltb_lt in H2. cbn [Z.of_nat] in H2. lia.
  - rewrite IH. destruct (Pos.eq_dec y x) as [->|Hne].
    + rewrite tget_tset_same.
      destruct (Z.leb (Zpos (Pos.succ x)) (Zpos x) && Z.ltb (Zpos x) (Zpos (Pos.succ x) + Z.of_nat k))%bool eqn:H1.
      { apply andb_prop in H1 as [H1 _]. apply Z.leb_le in H1. lia. }
      destruct (Z.leb (Zpos x) (Zpos x) && Z.ltb (Zpos x) (Zpos x + Z.of_nat (Datatypes.S k)))%bool eqn:H2; [reflexivity|].
      exfalso. apply andb_false_iff in H2 as [H2|H2]; [apply Z.leb_gt in H2; lia | apply Z.ltb_ge in H2; lia].
    + rewrite tget_tset_other by (intros H; apply Hne; symmetry; exact H).
      assert (Hne' : Zpos y <> Zpos x) by (intros H; injection H as H; exact (Hne H)).
      destruct (Z.leb (Zpos (Pos.succ x)) (Zpos y) && Z.ltb (Zpos y) (Zpos (Pos.succ x) + Z.of_nat k))%bool eqn:H1;
      destruct (Z.leb (Zpos x) (Zpos y) && Z.ltb (Zpos y) (Zpos x + Z.of_nat (Datatypes.S k)))%bool eqn:H2; try reflexivity.
      * exfalso. apply andb_prop in H1 as [H1a H1b]. apply Z.leb_le in H1a. apply Z.ltb_lt in H1b.
        apply andb_false_iff in H2 as [H2|H2]; [apply Z.leb_gt in H2; lia | apply Z.ltb_ge in H2; lia].
      * exfalso. apply andb_prop in H2 as [H2a H2b]. apply Z.leb_le in H2a. apply Z.ltb_lt in H2b.
        apply andb_false_iff in H1 as [H1|H1]; [apply Z.leb_gt in H1; lia | apply Z.ltb_ge in H1; lia].
Qed.

(* [comment removed for export] *)
Definition use_env (E E' : valu) (nb nS : positive) : valu := fun y => if Pos.ltb y nS then E y else E' (Z.to_pos (Zpos y - Zpos nS + Zpos nb)).

Lemma use_sig_ecomp : forall E E' σ nb nT nF nS x,
  (nb <= nT)%positive -> (nb <= nS)%positive -> (nT <= nF)%positive -> params_fixed σ (pos_below nb) = true ->
  (forall y l, (nb <= y < nT)%positive -> tget y σ = Some l -> lwf nS l = true) ->
  agree nT (ecomp E σ) E' -> (x < nF)%positive ->
  lden (use_env E E' nb nS) (svar (use_sig σ nb nT nF nS) x) = E' x.
Proof.
  intros E E' σ nb nT nF nS x Hbt Hbs Htf Hpf Hbw Ha Hx.
  set (E2 := use_env E E' nb nS).
  assert (HE2 : agree nS E E2) by (intros y Hy; unfold E2, use_env; rewrite (proj2 (Pos.ltb_lt y nS) Hy); reflexivity).
  unfold svar, use_sig. rewrite tget_use_acc. rewrite tget_empty.
  destruct (Z.leb (Zpos nb) (Zpos x) && Z.ltb (Zpos x) (Zpos nb + Z.of_nat (Pos.to_nat nF - Pos.to_nat nb)))%bool eqn:Hr.
  - apply andb_prop in Hr as [Hr1 _]. apply Z.leb_le in Hr1.
    unfold use_val. destruct (Pos.ltb x nT) eqn:HxT.
    + apply Pos.ltb_lt in HxT. destruct (tget x σ) as [l|] eqn:Hl.
      * rewrite <- (lden_agree nS E E2 l (Hbw x l ltac:(lia) Hl) HE2).
        rewrite <- (Ha x HxT). unfold ecomp, svar. rewrite Hl. reflexivity.
      * rewrite lden_lvar. unfold E2, use_env. destruct (Pos.ltb (Z.to_pos (Zpos x + Zpos nS - Zpos nb)) nS) eqn:Hlt.
        { exfalso. apply Pos.ltb_lt in Hlt. lia. }
        f_equal. lia.
    + rewrite lden_lvar. unfold E2, use_env. destruct (Pos.ltb (Z.to_pos (Zpos x + Zpos nS - Zpos nb)) nS) eqn:Hlt.
      { exfalso. apply Pos.ltb_lt in Hlt. lia. }
      f_equal. lia.
  - assert (Hxb : (x < nb)%positive).
    { apply andb_false_iff in Hr as [Hr|Hr]; [apply Z.leb_gt in Hr; lia | apply Z.ltb_ge in Hr; lia]. }
    rewrite lden_lvar. unfold E2, use_env. rewrite (proj2 (Pos.ltb_lt x nS) ltac:(lia)).
    rewrite <- (Ha x ltac:(lia)). symmetry. exact (params_fixed_sound E σ (pos_below nb) x Hpf (pos_below_In nb x Hxb)).
Qed.

Lemma use_env_agree : forall E E' nb nS, agree nS E (use_env E E' nb nS).
Proof. intros E E' nb nS y Hy. unfold use_env. rewrite (proj2 (Pos.ltb_lt y nS) Hy). reflexivity. Qed.
Lemma use_next_ge : forall nb nF nS, (nb <= nF)%positive -> (nS <= use_next nb nF nS)%positive.
Proof. intros nb nF nS H. unfold use_next. lia. Qed.
Lemma use_sig_wf : forall σ nb nT nF nS, (nb <= nS)%positive -> (nb <= nF)%positive ->
  (forall y l, (nb <= y < nT)%positive -> tget y σ = Some l -> lwf nS l = true) ->
  sig_wf (use_sig σ nb nT nF nS) nF (use_next nb nF nS).
Proof.
  intros σ nb nT nF nS Hbs Hbf Hbw x Hx. unfold svar, use_sig. rewrite tget_use_acc, tget_empty.
  assert (Hn : (nS <= use_next nb nF nS)%positive) by exact (use_next_ge nb nF nS Hbf).
  destruct (Z.leb (Zpos nb) (Zpos x) && Z.ltb (Zpos x) (Zpos nb + Z.of_nat (Pos.to_nat nF - Pos.to_nat nb)))%bool eqn:Hr.
  - apply andb_prop in Hr as [Hr1 _]. apply Z.leb_le in Hr1. unfold use_val.
    destruct (Pos.ltb x nT) eqn:HxT; [destruct (tget x σ) as [l|] eqn:Hl|].
    + apply Pos.ltb_lt in HxT. exact (lwf_mono _ _ _ Hn (Hbw x l ltac:(lia) Hl)).
    + unfold lvar, lwf, use_next. cbn [l_t forallb]. rewrite andb_true_r. apply Pos.ltb_lt. lia.
    + unfold lvar, lwf, use_next. cbn [l_t forallb]. rewrite andb_true_r. apply Pos.ltb_lt. lia.
  - assert (Hxb : (x < nb)%positive).
    { apply andb_false_iff in Hr as [Hr|Hr]; [apply Z.leb_gt in Hr; lia | apply Z.ltb_ge in Hr; lia]. }
    unfold lvar, lwf. cbn [l_t forallb]. rewrite andb_true_r. apply Pos.ltb_lt. lia.
Qed.
(* [comment removed for export] *)
Lemma frz_covs_inst : forall E' E2 σ' n MF, sm_wf n MF = true -> (forall x, (x < n)%positive -> lden E2 (svar σ' x) = E' x) ->
  frz_covs E' MF E2 (msubst σ' MF).
Proof.
  intros E' E2 σ' n MF Hwf He p Hp. exists (ppsubst σ' p). split; [unfold msubst; cbn [sm_frz]; apply in_map; exact Hp|].
  pose proof (sm_wf_frz _ MF Hwf) as Hz. rewrite Forall_forall in Hz. destruct (Hz p Hp) as [W1 W2].
  assert (Hag : agree n E' (ecomp E2 σ')) by (intros x Hx; unfold ecomp; symmetry; exact (He x Hx)).
  unfold ppsubst. cbn [fst snd]. rewrite <- !uE_sub. unfold uE.
  rewrite <- (lden_agree_wf n E' (ecomp E2 σ') _ W1 Hag), <- (lden_agree_wf n E' (ecomp E2 σ') _ W2 Hag). split; reflexivity.
Qed.

(* [comment removed for export] *)
Definition use_bwf (σ : tree lin) (nb nT nS : positive) : bool :=
  tforall (fun x l => if (Pos.leb nb x && Pos.ltb x nT)%bool then lwf nS l else true) σ.
Lemma use_bwf_spec : forall σ nb nT nS, use_bwf σ nb nT nS = true ->
  forall y l, (nb <= y < nT)%positive -> tget y σ = Some l -> lwf nS l = true.
Proof.
  intros σ nb nT nS H y l Hy Hl. unfold use_bwf in H. pose proof (tforall_spec _ σ H y l Hl) as Hx. cbv beta in Hx.
  destruct (Pos.leb nb y && Pos.ltb y nT)%bool eqn:Hb; [exact Hx|].
  exfalso. apply andb_false_iff in Hb as [Hb|Hb]; [apply Pos.leb_gt in Hb; lia | apply Pos.ltb_ge in Hb; lia].
Qed.
