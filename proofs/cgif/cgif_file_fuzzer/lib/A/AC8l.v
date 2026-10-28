(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04 YI08 YI0t YI0m YI0n YI0s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YCbw YCbx.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0d YP0c YI0w YI0y YC4a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC80 YC1f YC1g YC81 YC4b YC44.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AC94.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AC8a AC93 AC9g AC95 AC91 AC99 AC92 AC9b AC96 AC9j AC9h AC9i AC9c AC9d AC9e.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC20.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI00 YI0u YI0v YO07.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC88.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AC90 AC8p AC8r AC8m AC8z AC8y AC8t AC8u Niset.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg lib_asan3_1_listing}.
Context {RO : YC20.ro_below_ofl (@pa_segs _ lib_asan3_1_listing PI) (@pa_relro_lo _ lib_asan3_1_listing PI) (@pa_relro_hi _ lib_asan3_1_listing PI)}.
#[local] Notation SEGS := (@pa_segs _ lib_asan3_1_listing PI).
#[local] Notation VAL := (@pa_val _ lib_asan3_1_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_asan3_1_listing PI).
#[local] Notation BASE := (@pa_val _ lib_asan3_1_listing PI A_TEXT).
Ltac eimg_low := rewrite ?Eimg_low by (unfold A_TEXT; lia).
Section S.
Variable B : asyms.
Hypothesis TL : PALib B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis AMEMSET : aintrin_realizes SEGS B OSet (SIGMA AS_asan_memset).
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL. Let errno_low := pal_env B TL. Let HBfree := pal_free B TL. Let HBmalloc := pal_malloc B TL.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_asan3_1) (PI := PI).
Hypothesis HUL : forall t, In t (lzw_traces (as_code B) BASE) -> In t (as_universe B).
Let PBASE := @pa_B_ok _ _ PI. Let PBLO := @pa_base_lo _ _ PL_asan3_1 PI.
Lemma dp_leX : forall cx X, lzw_inv (z_idl cx) (z_nP cx) X -> la_dp X <= 4096.
Proof.
intros cx [TI LM LI TM s lp dp mp Cn R] HI. cbn [la_dp]. destruct HI as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hdp & _). lia.
Qed.
Section d.
Variables (cx : lzw_acx) (lyc : alayout) (Sc : astate) (W : world SEGS) (memc : word -> option byte) (mdc : Model)
(ly7 : alayout) (S7 : astate) (W7 : world SEGS) (regs0 : bvmap 5 word) (m0 : word -> option byte).
Variables (PIX : list Z) (FIN : option lzw_st).
Hypothesis HCX : acx_ok cx.
Hypothesis HRG : acx_ranges cx.
Hypothesis HSEP : acx_seps cx.
Hypothesis HBL : acx_blk (ablocks B ly7 S7) cx.
Hypothesis HTOK : acx_tok cx (ablocks B lyc Sc).
Hypothesis Hzgp : z_gp cx = as_gp B.
Hypothesis Hztp : z_tp cx = as_tp B.
Hypothesis M0 : alzw_slots m0 cx /\ alzw_sslots m0 cx /\ tlzw_frame m0 (z_sp cx) regs0.
Let J (mem : word -> option byte) (md : Model) : Prop := ajournal SEGS B LZW_TSTK (z_sp cx) [] lyc Sc W memc mdc [] ly7 S7 W7 mem md 7.
Let mr (mem : word -> option byte) : word -> option byte := mrestrict (w_H W7) mem.
Lemma minv : forall mem, aabove_eq cx m0 (mr mem) ->
alzw_slots (mr mem) cx /\ alzw_sslots (mr mem) cx /\ tlzw_frame (mr mem) (z_sp cx) regs0.
Proof.
intros mem HA. destruct M0 as (M1 & M2 & M3). pose proof HCX as (_ & _ & _ & _ & _ & _ & _ & Hsphi & _).
split; [exact (alzw_slots_kept _ _ _ M1 HA Hsphi)|]. split; [exact (alzw_sslots_kept _ _ _ M2 HA Hsphi) | exact (tlzw_frame_keptA _ _ _ _ M3 HA Hsphi)].
Qed.
Lemma Hidl_cx : 2 <= z_idl cx <= 256.
Proof. exact (proj1 HCX). Qed.
Lemma s_nonneg : forall X, lzw_inv (z_idl cx) (z_nP cx) X -> 0 <= la_s X.
Proof.
intros [TI LM LI TM s lp dp mp Cn R] HI. destruct HI as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hs). cbn [la_s]. lia.
Qed.
Lemma sim_ctx_of : forall mem X V, vtabs_at SEGS mem cx PIX V -> vinv cx PIX X V -> sim_ctx (z_idl cx) (z_nP cx) PIX.
Proof.
intros mem X V HVT (_ & LenPIX & _). split; [exact Hidl_cx|]. split; [exact LenPIX | exact (vtabs_px SEGS _ _ _ _ HVT)].
Qed.
Lemma vinv_typec : forall X V q, vinv cx PIX X V -> vinv cx PIX (st_typec (z_nP cx) X) (mkLV (v_LC V) (v_LD V ++ [q])).
Proof.
intros [TI LM LI TM s lp dp mp Cn R] V q (H1 & H2 & H3). unfold vinv in *. cbn [st_typec la_lp v_LC v_LD] in *.
rewrite length_app. cbn [length]. split; [exact H1|]. split; [exact H2 | lia].
Qed.
Lemma vinv_ti : forall X V c1 c2 k, vinv cx PIX X V -> vinv cx PIX (st_ti (z_idl cx) X c1 c2 k) (mkLV (v_LC V) (v_LD V ++ [c1])).
Proof.
intros [TI LM LI TM s lp dp mp Cn R] V c1 c2 k (H1 & H2 & H3). unfold vinv in *. cbn [st_ti la_lp v_LC v_LD] in *.
rewrite length_app. cbn [length]. split; [exact H1|]. split; [exact H2 | lia].
Qed.
Lemma vinv_map : forall X V m c s1 q, vinv cx PIX X V -> vinv cx PIX (vx_map (z_idl cx) X m c s1) (mkLV (v_LC V) (v_LD V ++ [q])).
Proof.
intros [TI LM LI TM s lp dp mp Cn R] V m c s1 q (H1 & H2 & H3). unfold vinv in *. cbn [vx_map la_lp v_LC v_LD] in *.
rewrite length_app. cbn [length]. split; [exact H1|]. split; [exact H2 | lia].
Qed.
Lemma vinv_first : forall X V q c s1, vinv cx PIX X V -> vinv cx PIX (vx_first X q s1) (mkLV (updn (v_LC V) (Z.to_nat q) c) (v_LD V ++ [q])).
Proof.
intros [TI LM LI TM s lp dp mp Cn R] V q c s1 (H1 & H2 & H3). unfold vinv in *. cbn [vx_first la_lp v_LC v_LD] in *.
rewrite length_app, updn_length. cbn [length]. split; [exact H1|]. split; [exact H2 | lia].
Qed.
Lemma vinv_switch : forall X V q c s1, vinv cx PIX X V -> vinv cx PIX (vx_switch (z_idl cx) X q c s1) (mkLV (v_LC V) (v_LD V ++ [q])).
Proof.
intros [TI LM LI TM s lp dp mp Cn R] V q c s1 (H1 & H2 & H3). unfold vinv in *. cbn [vx_switch la_lp v_LC v_LD] in *.
rewrite length_app. cbn [length]. split; [exact H1|]. split; [exact H2 | lia].
Qed.
Lemma vinv_reset : forall X V q k, vinv cx PIX X V -> vinv cx PIX (st_reset (z_idl cx) X k) (mkLV (repeat 0 4096) ((v_LD V ++ [q]) ++ [z_idl cx])).
Proof.
intros [TI LM LI TM s lp dp mp Cn R] V q k (H1 & H2 & H3). unfold vinv in *. cbn [st_reset la_lp v_LC v_LD] in *.
rewrite !length_app, repeat_length. cbn [length]. split; [reflexivity|]. split; [exact H2 | lia].
Qed.
Inductive crawl_res := CR_eidx (X' : lzw_abs) | CR_head (X' : lzw_abs) (V' : lzw_v) | CR_exit (X' : lzw_abs) (V' : lzw_v).
Definition cr_pc (r : crawl_res) : Z :=
match r with CR_eidx _ => PC_EIDX | CR_head _ _ => PC_HEAD | CR_exit _ _ => PC_EPI end.
Definition cr_post (X : lzw_abs) (c' : config) (r : crawl_res) : Prop :=
exists regs' mem' md',
c' = mkCfg (mkst regs' (Z_to_bv 64 (BASE + cr_pc r)) mem' (seg_rom SEGS)) md' /\ J mem' md' /\ aabove_eq cx m0 (mr mem') /\
match r with
| CR_eidx X' => alzw_regs_core regs' cx /\
agen_at (mr mem') cx (la_lp X') (la_dp X') (la_mp X') /\ lzw_inv (z_idl cx) (z_nP cx) X' /\ FIN = None
| CR_head X' V' => alzw_regs_head regs' cx /\ agen_at (mr mem') cx (la_lp X') (la_dp X') (la_mp X') /\ atables_at (mr mem') cx X' /\
lzw_inv (z_idl cx) (z_nP cx) X' /\ la_s X < la_s X' < z_nP cx /\ getr regs' 23 = w64 (la_s X') /\
vtabs_at SEGS (mr mem') cx PIX V' /\ vinv cx PIX X' V' /\ sim_head (z_idl cx) PIX X' V' FIN
| CR_exit X' V' => alzw_regs_head regs' cx /\ agen_at (mr mem') cx (la_lp X') (la_dp X') (la_mp X') /\
lzw_inv (z_idl cx) (z_nP cx) X' /\ la_s X' = z_nP cx /\
vtabs_at SEGS (mr mem') cx PIX V' /\ vinv cx PIX X' V' /\ sim_exit (z_idl cx) X' V' FIN
end.
Definition not_eidx (r : crawl_res) : Prop := match r with CR_eidx _ => False | _ => True end.
Definition tail_sim (X' : lzw_abs) (V' : lzw_v) : Prop :=
if la_s X' <? z_nP cx then sim_head (z_idl cx) PIX X' V' FIN else sim_exit (z_idl cx) X' V' FIN.
Lemma tail_sim_head : forall X' V', la_s X' < z_nP cx -> sim_head (z_idl cx) PIX X' V' FIN -> tail_sim X' V'.
Proof. intros X' V' Hs H. unfold tail_sim. destruct (Z.ltb_spec (la_s X') (z_nP cx)); [exact H | lia]. Qed.
Lemma tail_sim_exit : forall X' V', z_nP cx <= la_s X' -> sim_exit (z_idl cx) X' V' FIN -> tail_sim X' V'.
Proof. intros X' V' Hs H. unfold tail_sim. destruct (Z.ltb_spec (la_s X') (z_nP cx)); [lia | exact H]. Qed.
Lemma tail_cr : forall X memT (c' : config) X' V',
aabove_eq cx m0 (mr memT) ->
(exists regs' mem' md',
c' = mkCfg (mkst regs' (Z_to_bv 64 (BASE + atail_pc cx X')) mem' (seg_rom SEGS)) md' /\ J mem' md' /\
aabove_eq cx (mr memT) (mr mem') /\ atail_post cx X regs' (mr mem') X' /\ vtabs_at SEGS (mr mem') cx PIX V') ->
vinv cx PIX X' V' -> tail_sim X' V' ->
exists r, cr_post X c' r /\ not_eidx r.
Proof.
intros X memT c' X' V' HA (regs' & mem' & md' & -> & HJ' & HA' & (HFH & HG & HT & HI & H26 & Hs) & HVT) HVI HSIM.
unfold atail_pc. unfold tail_sim in HSIM. destruct (Z.ltb_spec (la_s X') (z_nP cx)) as [Hlt | Hge].
- exists (CR_head X' V'). split; [|exact I]. exists regs', mem', md'. split; [reflexivity|]. split; [exact HJ'|].
split; [exact (aabove_eq_trans _ _ _ _ HA HA')|]. repeat (split; [assumption|]). split; [lia|]. split; [exact H26|].
split; [exact HVT|]. split; [exact HVI | exact HSIM].
- exists (CR_exit X' V'). split; [|exact I]. exists regs', mem', md'. split; [reflexivity|]. split; [exact HJ'|].
split; [exact (aabove_eq_trans _ _ _ _ HA HA')|]. repeat (split; [assumption|]). split; [lia|].
split; [exact HVT|]. split; [exact HVI | exact HSIM].
Qed.
Lemma inner_loop : forall (k : nat) X V regs memT mdT s1 q,
(Z.to_nat (z_nP cx - s1) <= k)%nat ->
J memT mdT -> alzw_regs_core regs cx -> agen_at (mr memT) cx (la_lp X) (la_dp X) (la_mp X) -> atables_at (mr memT) cx X ->
lzw_inv (z_idl cx) (z_nP cx) X -> tin_pre cx regs s1 q -> la_s X < s1 <= z_nP cx - 1 -> 0 <= q < 4096 -> aabove_eq cx m0 (mr memT) ->
vtabs_at SEGS (mr memT) cx PIX V -> vinv cx PIX X V -> sim_inner (z_idl cx) PIX X V s1 q FIN ->
SRr SEGS W7 (mkCfg (mkst regs (Z_to_bv 64 (BASE + PC_INNER)) memT (seg_rom SEGS)) mdT)
(fun W' c' => W' = W7 /\ exists regs' md' o s1' q1,
c' = mkCfg (mkst regs' (Z_to_bv 64 (BASE + tio_pc o)) memT (seg_rom SEGS)) md' /\
J memT md' /\ alzw_regs_core regs' cx /\ s1 <= s1' <= z_nP cx - 1 /\ 0 <= q1 < 4096 /\
tio_post cx X s1' q1 (mr memT) regs' o /\ tio_val (z_idl cx) X V PIX s1' q1 o /\ sim_inner (z_idl cx) PIX X V s1' q1 FIN /\
match o with TIO_cont _ => False | _ => True end).
Proof.
induction k as [|k IH]; intros X V regs memT mdT s1 q Hk HJ HF HG HT HI HPRE Hs1 Hq HA HVT HVI HSIM; [lia|].
destruct (minv memT HA) as (HSL & HSS & HFR).
pose proof (sim_ctx_of _ _ _ HVT HVI) as HSC. pose proof (s_nonneg X HI) as Hs0.
eapply SRr_bind.
{ eapply (tinner_iterX B LAWS cx lyc Sc W memc mdc ly7 S7 W7 regs memT mdT regs0 X s1 q PIX V); eassumption. }
cbv beta. intros W' c' _ (-> & regs' & md' & o & -> & HJ' & HF' & HP & HV).
destruct o as [|q'|q'|c].
2:{
destruct HP as (HPRE' & Hq' & Hs2). destruct HV as (Vc & Vq & Vq0).
pose proof (sim_inner_cont (z_idl cx) (z_nP cx) PIX HSC X V FIN s1 q q' HSIM HI Hq ltac:(lia) Vc Vq Vq0) as HSIM'.
eapply SRr_mono.
{ eapply (IH X V regs' memT md' (s1 + 1) q'); try eassumption; lia. }
cbv beta. intros W'' c'' _ (-> & regs'' & md'' & o & s1' & q1 & -> & HJ'' & HF'' & Hs1' & Hq1 & HP' & HV' & HSIM'' & Ho).
split; [reflexivity|]. exists regs'', md'', o, s1', q1. split; [reflexivity|]. split; [exact HJ''|]. split; [exact HF''|].
split; [lia|]. split; [exact Hq1|]. split; [exact HP'|]. split; [exact HV'|]. split; [exact HSIM'' | exact Ho]. }
all: apply SRr_ret; split; [reflexivity|]; exists regs', md'; eexists; exists s1, q;
(split; [reflexivity|]); (split; [exact HJ'|]); (split; [exact HF'|]); (split; [lia|]); (split; [lia|]);
(split; [exact HP|]); (split; [exact HV|]); (split; [exact HSIM | exact I]).
Qed.
Lemma crawl_step : forall X V regs memT mdT,
J memT mdT -> alzw_regs_head regs cx -> agen_at (mr memT) cx (la_lp X) (la_dp X) (la_mp X) -> atables_at (mr memT) cx X ->
lzw_inv (z_idl cx) (z_nP cx) X -> getr regs 23 = w64 (la_s X) -> la_s X < z_nP cx -> aabove_eq cx m0 (mr memT) ->
vtabs_at SEGS (mr memT) cx PIX V -> vinv cx PIX X V -> sim_head (z_idl cx) PIX X V FIN ->
SRr SEGS W7 (mkCfg (mkst regs (Z_to_bv 64 (BASE + PC_HEAD)) memT (seg_rom SEGS)) mdT)
(fun W' c' => W' = W7 /\ exists r, cr_post X c' r).
Proof.
intros X V regs memT mdT HJ HFH HG HT HI H24 Hs HA HVT HVI HSIM.
destruct (minv memT HA) as (HSL & HSS & HFR). pose proof HFH as (HFX & H30 & H16). pose proof (alzw_regs_core_of_fix _ _ HFX) as HFC.
pose proof (dp_leX cx X HI) as Hdp.
pose proof (sim_ctx_of _ _ _ HVT HVI) as HSC. pose proof (s_nonneg X HI) as Hs0. pose proof HVI as (LenLC & LenPIX & LenLD).
pose proof HCX as (Hidl & HnP & HMR & HMR0 & _).
pose proof (maxres_bounds (z_idl cx) (z_nP cx) Hidl ltac:(lia)) as [HMR1 HMR2].
pose proof (lp_head_bound (z_idl cx) (z_nP cx) (z_MR cx) X ltac:(unfold lzw_par; lia) HI Hs) as Hlpb.
Local Ltac weaken X :=
apply (SRr_mono SEGS _ _ (fun W' c' => W' = W7 /\ exists r, cr_post X c' r /\ not_eidx r));
[| cbv beta; let r := fresh "r" in let Hr := fresh "Hr" in intros ? ? _ (-> & r & Hr & _); split; [reflexivity | exists r; exact Hr]].
Local Ltac eidx X regs' memT md' HJ' HA :=
apply SRr_ret; split; [reflexivity|]; exists (CR_eidx X); exists regs', memT, md'; split; [reflexivity|]; split; [exact HJ'|];
split; [exact HA|].
Local Ltac tcr E HJx HAx HTP HVT :=
eexists _, _, _; split; [first [exact E | reflexivity]|]; split; [exact HJx|]; split; [exact HAx|]; split; [exact HTP | exact HVT].
eapply SRr_bind.
{ eapply (thead_segX B LAWS cx lyc Sc W memc mdc ly7 S7 W7 regs memT mdT regs0 X PIX V); eassumption. }
cbv beta. intros W' c' _ (-> & regs' & md' & o & -> & HJ' & HF' & HP & HV).
pose proof (alzw_regs_core_of_fix _ _ HF') as HFC'.
destruct o as [|q|c1 c2|q].
-
cbn [tho_val] in HV. pose proof (sim_head_eidx (z_idl cx) (z_nP cx) PIX HSC X V FIN HSIM ltac:(lia) HV) as HFIN.
eidx X regs' memT md' HJ' HA. split; [exact HFC'|]. split; [exact HG|]. split; [exact HI | exact HFIN].
-
destruct HP as (P23 & P15 & Hq & P30). cbn [tho_val] in HV. destruct HV as (Vc1 & HV).
pose proof (sim_head_emitc (z_idl cx) (z_nP cx) PIX HSC X V FIN q HSIM ltac:(lia) Vc1 HV) as HEX.
weaken X. eapply SRr_mono.
{ eapply (temitc_segX B LAWS cx lyc Sc W memc mdc ly7 S7 W7 regs' memT md' regs0 X q PIX V); try eassumption. }
cbv beta. intros W'' c'' _ [-> HQ]. split; [reflexivity|].
destruct HQ as (regs'' & mem'' & md'' & X' & E'' & HJ'' & HA'' & HTP & -> & HVT'').
eapply (tail_cr X memT c'' _ _ HA); [tcr E'' HJ'' HA'' HTP HVT'' | apply vinv_typec; exact HVI |].
apply tail_sim_exit; [destruct X as [TI LM LI TM s lp dp mp Cn R]; cbn [st_typec la_s]; lia | exact HEX].
-
destruct HP as (P23 & P15 & P17 & P11 & P14 & P7 & P30 & Hc1 & Hc2 & HTI0 & Hs1 & HC2). cbn [tho_val] in HV. destruct HV as (Vc1 & Vc2).
weaken X. eapply SRr_bind.
{ eapply (ttimiss_segX B LAWS cx lyc Sc W memc mdc ly7 S7 W7 regs' memT md' regs0 X c1 c2 PIX V); try eassumption. }
cbv beta. intros W'' c'' _ (-> & regs'' & mem'' & md'' & X' & full & -> & HJ'' & HA'' & HP').
pose proof (aabove_eq_trans _ _ _ _ HA HA'') as HA2.
destruct full.
+
destruct HP' as ((HRP & HCC) & HVT''). assert (Hfull : la_dp X = 4096) by (destruct HRP as (_ & _ & _ & _ & _ & _ & _ & Hd & _); exact Hd).
destruct (minv mem'' HA2) as (HSL2 & HSS2 & HFR2).
eapply SRr_mono.
{ eapply (trst_segX B LAWS AMEMSET true cx lyc Sc W memc mdc ly7 S7 W7 regs'' mem'' md'' regs0 X (la_s X + 1) PIX (v_LD V ++ [c1]));
try eassumption.
- exact (proj1 (proj2 HVT'')).
- exact (proj2 (proj2 HVT'')).
- cbn [v_LD]. rewrite length_app. cbn [length]. lia. }
cbv beta. intros W3 c3 _ [-> HQ]. split; [reflexivity|]. destruct HQ as (regs3 & mem3 & md3 & E3 & HJ3 & HA3 & HTP & Hs3 & HVT3).
eapply (tail_cr X mem'' c3 _ _ HA2); [tcr E3 HJ3 HA3 HTP HVT3 | apply vinv_reset; exact HVI |].
apply tail_sim_head; [lia|].
eapply (sim_head_timiss_rst (z_idl cx) (z_nP cx) PIX HSC X V FIN c1 c2); try eassumption; try lia; reflexivity.
+ destruct HP' as ((HTP & ->) & HVT'').
apply SRr_ret. split; [reflexivity|].
eapply (tail_cr X memT _ _ _ HA); [tcr HJ'' HJ'' HA'' HTP HVT'' | apply vinv_ti; exact HVI |].
assert (Hnf : la_dp X < 4096).
{ destruct X as [TI LM LI TM s lp dp mp Cn R]. cbn [st_ti la_dp] in HTP |- *.
destruct HTP as (_ & _ & _ & HI' & _). destruct HI' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hdp' & _). cbn [la_dp] in Hdp'. lia. }
apply tail_sim_head; [destruct X as [TI LM LI TM s lp dp mp Cn R]; cbn [st_ti la_s] in *; lia|].
eapply (sim_head_timiss_add (z_idl cx) (z_nP cx) PIX HSC X V FIN c1 c2); try eassumption; lia.
-
destruct HP as (P23 & P15 & P7 & P13 & P16 & Hq & Hs2). cbn [tho_val] in HV. destruct HV as (Vc1 & Vc2 & Vq & Vq0).
pose proof (sim_head_inner (z_idl cx) (z_nP cx) PIX HSC X V FIN q HSIM Vc1 Vc2 Vq Vq0 Hs0 ltac:(lia)) as HSI.
eapply SRr_bind.
{ eapply (tisetup_seg B LAWS cx lyc Sc W memc mdc ly7 S7 W7 regs' memT md' regs0 X q); try eassumption; lia. }
cbv beta. intros Wi ci _ (-> & regsi & memi & mdi & -> & HJi & Hfri & HV48 & HFi & HPREi).
destruct (iset_frame cx W7 HCX HRG memT memi X Hfri HG HT HI) as (HAi & HGi & HTi).
pose proof (aabove_eq_trans _ _ _ _ HA HAi) as HA1.
assert (HVTi : vtabs_at SEGS (mr memi) cx PIX V).
{ eapply vtabs_keep with (W := fun a => z_sp cx - 320 + 8 <= a < z_sp cx - 320 + 56); [exact HVT | exact HVI | lia | exact Hfri |].
pose proof HRG as (HR & (Hbi0 & _) & Hbi1 & Hbi2 & Hbi3). cbn [ranges acx_tabs lzw_tabs app] in HR.
destruct HR as (((Rld1 & _) & Rld2 & Rld3 & Rld4) & _ & _ & ((Rlc1 & _) & Rlc2 & Rlc3 & _) & _).
pose proof HCX as (_ & _ & _ & _ & _ & _ & Hsplo & Hsphi & _ & _ & _ & _ & _ & EMR).
assert (HTS : LZW_TSTK = 336 + ASTACK) by reflexivity. assert (Has : ASTACK = 16384) by reflexivity.
rewrite HTS, Has in Hsplo. rewrite <- EMR in Rld2. unfold cap in Hlpb. pose proof (req_size_pos (z_Li cx)) as HrLi.
unfold voff. cbn beta. split; [|split]; intros a Ha; (split; [lia|]); lia. }
clear HVT. rename HVTi into HVT.
eapply SRr_bind.
{ eapply (inner_loop (Z.to_nat (z_nP cx - (la_s X + 2))) X V regsi memi mdi (la_s X + 2) q); try eassumption; try lia. }
cbv beta. intros W'' c'' _ (-> & regs'' & md'' & o & s1' & q1 & -> & HJ'' & HF'' & Hs1' & Hq1 & HP' & HV' & HSI' & Ho).
destruct o as [|q'|q'|c]; [| destruct Ho | |].
+
cbn [tio_val] in HV'. pose proof (sim_inner_eidx (z_idl cx) (z_nP cx) PIX HSC X V FIN s1' q1 HSI' ltac:(lia) HV') as HFIN.
eidx X regs'' memi md'' HJ'' HA1. split; [exact HF''|]. split; [exact HGi|]. split; [exact HI | exact HFIN].
+ destruct HP' as (P23' & P15' & Hq' & Hs1e & P30'). cbn [tio_val] in HV'. destruct HV' as (Vc & Vq' & Vq0').
pose proof (sim_inner_emitc (z_idl cx) (z_nP cx) PIX HSC X V FIN s1' q1 q' HSI' HI Hq1 ltac:(lia) Hs1e Vc Vq' Vq0') as HEX.
weaken X. destruct (minv memi HA1) as (HSLi & HSSi & HFRi). eapply SRr_mono.
{ eapply (temitc_segX B LAWS cx lyc Sc W memc mdc ly7 S7 W7 regs'' memi md'' regs0 X q' PIX V); try eassumption; try lia. }
cbv beta. intros W3 c3 _ [-> HQ]. split; [reflexivity|].
destruct HQ as (regs3 & mem3 & md3 & X' & E3 & HJ3 & HA3 & HTP & -> & HVT3).
eapply (tail_cr X memi c3 _ _ HA1); [tcr E3 HJ3 HA3 HTP HVT3 | apply vinv_typec; exact HVI |].
apply tail_sim_exit; [destruct X as [TI LM LI TM s lp dp mp Cn R]; cbn [st_typec la_s]; lia | exact HEX].
+
destruct HP' as (HPRE' & Hc & HC). cbn [tio_val] in HV'. destruct HV' as (Vcc & Vc & Vch).
destruct (minv memi HA1) as (HSLi & HSSi & HFRi).
assert (HH : tmiss_hyps B cx lyc Sc W memc mdc ly7 S7 W7 regs'' memi md'' regs0 X s1' q1 c).
{ unfold tmiss_hyps. repeat (split; [first [assumption | lia]|]). exact HV48. }
destruct (Z.eq_dec (la_dp X) 4096) as [Hfull | Hnf].
* weaken X. eapply SRr_bind; [eapply (tmiss_fullX B LAWS); [exact HH | exact Hfull | exact HVT | exact HVI]|].
cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HA3 & HPRE3 & HCC3 & HVT3).
pose proof (aabove_eq_trans _ _ _ _ HA1 HA3) as HA2. destruct (minv mem3 HA2) as (HSL3 & HSS3 & HFR3).
eapply SRr_mono.
{ eapply (trst_segX B LAWS AMEMSET false cx lyc Sc W memc mdc ly7 S7 W7 regs3 mem3 md3 regs0 X s1' PIX (v_LD V ++ [q1]));
try eassumption.
- exact (proj1 (proj2 HVT3)).
- exact (proj2 (proj2 HVT3)).
- cbn [v_LD]. rewrite length_app. cbn [length]. lia. }
cbv beta. intros W4 c4 _ [-> HQ]. split; [reflexivity|]. destruct HQ as (regs4 & mem4 & md4 & E4 & HJ4 & HA4 & HTP & Hs4 & HVT4).
eapply (tail_cr X mem3 c4 _ _ HA2); [tcr E4 HJ4 HA4 HTP HVT4 | apply vinv_reset; exact HVI |].
apply tail_sim_head; [lia|].
eapply (sim_miss_rst (z_idl cx) (z_nP cx) PIX HSC X V FIN s1' q1 c); first [eassumption | reflexivity | rewrite Vcc; exact Vch | lia].
* destruct (Z.eq_dec (nth (Z.to_nat q1) (la_LM X) 0) 0) as [HLM0 | HLM1].
-- destruct (Z.eq_dec (nth (Z.to_nat q1) (la_LI X) 0) 0) as [HLI0 | HLI1].
++ weaken X. eapply SRr_mono; [eapply (tmiss_firstX B LAWS); [exact HH | lia | exact HLM0 | exact HLI0 | exact HVT | exact HVI]|].
cbv beta. intros W3 c3 _ [-> HQ]. split; [reflexivity|]. destruct HQ as (regs3 & mem3 & md3 & E3 & HJ3 & HA3 & HTP & Hs3 & HVT3).
eapply (tail_cr X memi c3 _ _ HA1); [tcr E3 HJ3 HA3 HTP HVT3 | apply vinv_first; exact HVI |].
apply tail_sim_head; [lia|].
eapply (sim_miss_first (z_idl cx) (z_nP cx) PIX HSC X V FIN s1' q1 c); first [eassumption | reflexivity | rewrite Vcc; exact Vch | lia].
++ weaken X. eapply SRr_mono; [eapply (tmiss_swX B LAWS AMEMSET); [exact HH | lia | exact HLM0 | exact HLI1 | exact Hzgp | exact Hztp | exact HVT | exact HVI]|].
cbv beta. intros W3 c3 _ [-> HQ]. split; [reflexivity|]. destruct HQ as (regs3 & mem3 & md3 & E3 & HJ3 & HA3 & HTP & Hs3 & HVT3).
eapply (tail_cr X memi c3 _ _ HA1); [tcr E3 HJ3 HA3 HTP HVT3 | apply vinv_switch; exact HVI |].
apply tail_sim_head; [lia|].
eapply (sim_miss_switch (z_idl cx) (z_nP cx) PIX HSC X V FIN s1' q1 c); first [eassumption | reflexivity | rewrite Vcc; exact Vch | lia].
-- weaken X. eapply SRr_mono; [eapply (tmiss_mapX B LAWS); [exact HH | lia | exact HLM1 | exact HVT | exact HVI]|].
cbv beta. intros W3 c3 _ [-> HQ]. split; [reflexivity|]. destruct HQ as (regs3 & mem3 & md3 & E3 & HJ3 & HA3 & HTP & Hs3 & HVT3).
eapply (tail_cr X memi c3 _ _ HA1); [tcr E3 HJ3 HA3 HTP HVT3 | apply vinv_map; exact HVI |].
apply tail_sim_head; [lia|].
eapply (sim_miss_map (z_idl cx) (z_nP cx) PIX HSC X V FIN s1' q1 c); first [eassumption | reflexivity | rewrite Vcc; exact Vch | lia].
Qed.
Lemma crawl_loop : forall (k : nat) X V regs memT mdT,
(Z.to_nat (z_nP cx - la_s X) <= k)%nat ->
J memT mdT -> alzw_regs_head regs cx -> agen_at (mr memT) cx (la_lp X) (la_dp X) (la_mp X) -> atables_at (mr memT) cx X ->
lzw_inv (z_idl cx) (z_nP cx) X -> getr regs 23 = w64 (la_s X) -> la_s X < z_nP cx -> aabove_eq cx m0 (mr memT) ->
vtabs_at SEGS (mr memT) cx PIX V -> vinv cx PIX X V -> sim_head (z_idl cx) PIX X V FIN ->
SRr SEGS W7 (mkCfg (mkst regs (Z_to_bv 64 (BASE + PC_HEAD)) memT (seg_rom SEGS)) mdT)
(fun W' c' => W' = W7 /\ exists r, cr_post X c' r /\ match r with CR_head _ _ => False | _ => True end).
Proof.
induction k as [|k IH]; intros X V regs memT mdT Hk HJ HF HG HT HI H24 Hs HA HVT HVI HSIM; [lia|].
eapply SRr_bind; [eapply (crawl_step X V regs memT mdT); eassumption|].
cbv beta. intros W' c' _ (-> & r & HP). destruct r as [X'|X' V'|X' V'].
- apply SRr_ret. split; [reflexivity|]. exists (CR_eidx X'). split; [exact HP | exact I].
- destruct HP as (regs' & mem' & md' & -> & HJ' & HA' & HF' & HG' & HT' & HI' & Hs' & P26 & HVT' & HVI' & HSIM').
eapply SRr_mono; [eapply (IH X' V' regs' mem' md'); try eassumption; lia|].
cbv beta. intros W'' c'' _ (-> & r & HP' & Hr). split; [reflexivity|]. exists r. split; [|exact Hr].
destruct HP' as (regs'' & mem'' & md'' & E'' & HJ'' & HA'' & HR). exists regs'', mem'', md''.
split; [exact E''|]. split; [exact HJ''|]. split; [exact HA''|].
destruct r as [X''|X'' V''|X'' V'']; [| destruct Hr |].
+ destruct HR as (R1 & R2 & R3 & R4). repeat (split; [assumption|]). exact R4.
+ destruct HR as (R1 & R2 & R3 & R4 & R5 & R6 & R7). repeat (split; [assumption|]). exact R7.
- apply SRr_ret. split; [reflexivity|]. exists (CR_exit X' V'). split; [exact HP | exact I].
Qed.
End d.
End S.
End b.
End a.
