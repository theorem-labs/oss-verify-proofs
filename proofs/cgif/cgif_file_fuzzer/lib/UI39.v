(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YM06 YK0s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YN32 YK0w.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0i YO0f YO0x YO0d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import UH00 UH03 UH02 UN3b UN3c
YI06 UI5b YI09 YI08 YI0t YI0r YI0o UI3n UI3o.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI0u UI30 UI36 UI38 UI31 UI3j UI3c UI3d UI3i UI3g UI3h.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO07.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI0h YI0v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import UIZ2.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section S.
Variable API : AllocAPI ubs0_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws ubs0_msyms MR := aa_laws API.
Hypothesis IMG : img_laws ubs0_msyms MR.
Hypothesis RESET : reset_specV API.
Section b.
Variables (cx : lzw_tcx) (STK sp0 : Z) (FP : list (Z * Z)) (L : layout) (A : astate) (mem : word -> option byte) (md : Model)
(Lc : layout) (Ac : astate) (mdc : Model).
Variables (PIX : list Z) (FIN : option lzw_st).
Hypothesis HCX : tcx_ok cx.
Hypothesis HRG : tcx_ranges cx.
Hypothesis HSEP : tcx_seps cx.
Hypothesis HBL : tcx_blocks cx (blocks Lc Ac).
Hypothesis HWIN : tcx_win STK sp0 cx.
Hypothesis HWT : tcx_wtok STK sp0 FP (blocks L A) cx.
Let J := journal ubs0_msyms MR STK sp0 FP L A mem md Lc Ac.
Inductive crawl_res := CR_eidx (X' : lzw_abs) | CR_head (X' : lzw_abs) (V' : lzw_v) | CR_exit (X' : lzw_abs) (V' : lzw_v).
Definition cr_pc (r : crawl_res) : Z := match r with CR_eidx _ => TPC_EIDX | CR_head _ _ => TPC_HEAD | CR_exit _ _ => TPC_EXIT end.
Definition cr_post (X : lzw_abs) (memc : word -> option byte) (c' : config) (r : crawl_res) : Prop :=
exists regs' mem',
c' = mkCfg (mkst regs' (Z_to_bv 64 (cr_pc r)) mem' (seg_rom ubs0segs)) mdc /\
J mem' mdc /\ tabove_eq cx memc mem' /\ tlzw_regs_fix regs' cx /\
match r with
| CR_eidx X' => gen_at mem' cx (la_lp X') (la_dp X') (la_mp X') /\ lzw_inv (y_idl cx) (y_nP cx) X' /\ FIN = None
| CR_head X' V' => gen_at mem' cx (la_lp X') (la_dp X') (la_mp X') /\ ttables_at mem' cx X' /\ lzw_inv (y_idl cx) (y_nP cx) X' /\
la_s X < la_s X' < y_nP cx /\ getr regs' 22 = Z_to_bv 64 (la_s X') /\ getr regs' 11 = Z_to_bv 64 (y_nP cx) /\
vtabs_at mem' cx PIX V' /\ vinv cx PIX X' V' /\ sim_head (y_idl cx) PIX X' V' FIN
| CR_exit X' V' => gen_at mem' cx (la_lp X') (la_dp X') (la_mp X') /\ lzw_inv (y_idl cx) (y_nP cx) X' /\ la_s X' = y_nP cx /\
vtabs_at mem' cx PIX V' /\ vinv cx PIX X' V' /\ sim_exit (y_idl cx) X' V' FIN
end.
Lemma cr_weak : forall X m1 m2 c' r, tabove_eq cx m1 m2 -> cr_post X m2 c' r -> cr_post X m1 c' r.
Proof using.
intros X m1 m2 c' r HA (regs' & mem' & Hc & HJ' & HA' & HR).
exists regs', mem'. split; [exact Hc|]. split; [exact HJ'|]. split; [eapply tabove_eq_trans; [exact HA | exact HA'] | exact HR].
Qed.
Definition not_eidx (r : crawl_res) : Prop := match r with CR_eidx _ => False | _ => True end.
Lemma cr_weak_ex : forall X m1 m2 c', tabove_eq cx m1 m2 ->
(exists r, cr_post X m2 c' r /\ not_eidx r) -> (exists r, cr_post X m1 c' r /\ not_eidx r).
Proof using. intros X m1 m2 c' HA (r & H & Hr). exists r. split; [eapply cr_weak; [exact HA | exact H] | exact Hr]. Qed.
Lemma Hidl_cx : 2 <= y_idl cx <= 256.
Proof using HCX. exact (proj1 HCX). Qed.
Lemma vinv_typec : forall X V q, vinv cx PIX X V -> vinv cx PIX (st_typec (y_nP cx) X) (mkLV (v_LC V) (v_LD V ++ [q])).
Proof using.
intros [TI LM LI TM s lp dp mp Cn R] V q (H1 & H2 & H3). unfold vinv in *. cbn [st_typec la_lp v_LC v_LD] in *.
rewrite length_app. cbn [length]. split; [exact H1|]. split; [exact H2 | lia].
Qed.
Lemma vinv_ti : forall X V c1 c2 k, vinv cx PIX X V -> vinv cx PIX (st_ti (y_idl cx) X c1 c2 k) (mkLV (v_LC V) (v_LD V ++ [c1])).
Proof using.
intros [TI LM LI TM s lp dp mp Cn R] V c1 c2 k (H1 & H2 & H3). unfold vinv in *. cbn [st_ti la_lp v_LC v_LD] in *.
rewrite length_app. cbn [length]. split; [exact H1|]. split; [exact H2 | lia].
Qed.
Lemma vinv_map : forall X V m c s1 q, vinv cx PIX X V -> vinv cx PIX (vx_map (y_idl cx) X m c s1) (mkLV (v_LC V) (v_LD V ++ [q])).
Proof using.
intros [TI LM LI TM s lp dp mp Cn R] V m c s1 q (H1 & H2 & H3). unfold vinv in *. cbn [vx_map la_lp v_LC v_LD] in *.
rewrite length_app. cbn [length]. split; [exact H1|]. split; [exact H2 | lia].
Qed.
Lemma vinv_first : forall X V q c s1, vinv cx PIX X V -> vinv cx PIX (vx_first X q s1) (mkLV (updn (v_LC V) (Z.to_nat q) c) (v_LD V ++ [q])).
Proof using.
intros [TI LM LI TM s lp dp mp Cn R] V q c s1 (H1 & H2 & H3). unfold vinv in *. cbn [vx_first la_lp v_LC v_LD] in *.
rewrite length_app, updn_length. cbn [length]. split; [exact H1|]. split; [exact H2 | lia].
Qed.
Lemma vinv_switch : forall X V q c s1, vinv cx PIX X V -> vinv cx PIX (vx_switch (y_idl cx) X q c s1) (mkLV (v_LC V) (v_LD V ++ [q])).
Proof using.
intros [TI LM LI TM s lp dp mp Cn R] V q c s1 (H1 & H2 & H3). unfold vinv in *. cbn [vx_switch la_lp v_LC v_LD] in *.
rewrite length_app. cbn [length]. split; [exact H1|]. split; [exact H2 | lia].
Qed.
Lemma vinv_reset : forall X V q k, vinv cx PIX X V -> vinv cx PIX (st_reset (y_idl cx) X k) (mkLV (repeat 0 4096) ((v_LD V ++ [q]) ++ [y_idl cx])).
Proof using.
intros [TI LM LI TM s lp dp mp Cn R] V q k (H1 & H2 & H3). unfold vinv in *. cbn [st_reset la_lp v_LC v_LD] in *.
rewrite !length_app, repeat_length. cbn [length]. split; [reflexivity|]. split; [exact H2 | lia].
Qed.
Lemma dp_lt_of_inv : forall X X', lzw_inv (y_idl cx) (y_nP cx) X' -> la_dp X' = la_dp X + 1 -> la_dp X < 4096.
Proof using.
intros X [TI LM LI TM s lp dp mp Cn R] HI E. destruct HI as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hdp & _). cbn [la_dp] in E. lia.
Qed.
Lemma s_nonneg : forall X, lzw_inv (y_idl cx) (y_nP cx) X -> 0 <= la_s X.
Proof using.
intros [TI LM LI TM s lp dp mp Cn R] HI. destruct HI as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hs). cbn [la_s]. lia.
Qed.
Definition tail_sim (X' : lzw_abs) (V' : lzw_v) : Prop :=
if la_s X' <? y_nP cx then sim_head (y_idl cx) PIX X' V' FIN else sim_exit (y_idl cx) X' V' FIN.
Lemma tail_sim_head : forall X' V', la_s X' < y_nP cx -> sim_head (y_idl cx) PIX X' V' FIN -> tail_sim X' V'.
Proof using. intros X' V' Hs H. unfold tail_sim. destruct (Z.ltb_spec (la_s X') (y_nP cx)); [exact H | lia]. Qed.
Lemma tail_sim_exit : forall X' V', y_nP cx <= la_s X' -> sim_exit (y_idl cx) X' V' FIN -> tail_sim X' V'.
Proof using. intros X' V' Hs H. unfold tail_sim. destruct (Z.ltb_spec (la_s X') (y_nP cx)); [lia | exact H]. Qed.
Lemma from_tail : forall X regs memc X' V',
J memc mdc -> ttail_post cx X regs memc X' ->
vtabs_at memc cx PIX V' -> vinv cx PIX X' V' -> tail_sim X' V' ->
SR ubs0segs (mkCfg (mkst regs (Z_to_bv 64 TPC_TAIL) memc (seg_rom ubs0segs)) mdc)
(fun c' => exists r, cr_post X memc c' r /\ not_eidx r).
Proof using HCX HRG HWIN IMG.
intros X regs memc X' V' HJ (HF & HG & HT & HI & H22 & Hs) HVT HVI HSIM.
pose proof HCX as (Hidl & HnP & HMR & HMR0 & _).
assert (HMRle : y_MR cx <= 26055).
{ assert (y_MR cx * 3838 <= y_MR cx * (4094 - y_idl cx)) by (apply Z.mul_le_mono_nonneg_l; lia). lia. }
pose proof (lp_exit_bound (y_idl cx) (y_nP cx) (y_MR cx) X' ltac:(unfold lzw_par; lia) HI) as Hlpx. unfold cap in Hlpx.
pose proof (mp_bound (y_idl cx) (y_nP cx) X' ltac:(lia) HI) as Hmpb.
assert (Hdpb : 4 <= la_dp X' <= 4096 /\ 0 <= la_s X' <= y_nP cx).
{ destruct X' as [TI LM LI TM s lp dp mp Cn R]. cbn [la_dp la_s].
destruct HI as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hdp & _ & _ & _ & _ & _ & _ & Hs0). lia. }
eapply SR_mono.
{ eapply (ttail_seg API IMG cx STK sp0 FP L A mem md Lc Ac mdc regs memc (la_lp X') (la_s X') (la_dp X') (la_mp X'));
try eassumption; lia. }
cbv beta. intros c' (regs' & mem' & -> & HJ' & Hm & HF' & H22' & H11').
pose proof (vtabs_at_eq _ _ cx PIX V' HVT Hm) as HVT'. unfold tail_sim in HSIM.
destruct (Z.ltb_spec (la_s X') (y_nP cx)) as [Hlt | Hge].
- exists (CR_head X' V'). split; [|exact I]. exists regs', mem'. split; [reflexivity|]. split; [exact HJ'|].
split; [apply tabove_eq_of_eq; exact Hm|]. split; [exact HF'|].
split; [eapply gen_at_eq; eassumption|]. split; [eapply ttables_at_eq; eassumption|]. split; [exact HI|].
split; [lia|]. split; [exact H22'|]. split; [exact H11'|]. split; [exact HVT'|]. split; [exact HVI | exact HSIM].
- exists (CR_exit X' V'). split; [|exact I]. exists regs', mem'. split; [reflexivity|]. split; [exact HJ'|].
split; [apply tabove_eq_of_eq; exact Hm|]. split; [exact HF'|].
split; [eapply gen_at_eq; eassumption|]. split; [exact HI|]. split; [lia|]. split; [exact HVT'|]. split; [exact HVI | exact HSIM].
Qed.
Lemma from_rst : forall X V q s' regs memc,
J memc mdc -> trst_pre cx X s' regs memc -> s' < y_nP cx ->
vtabs_at memc cx PIX (mkLV (v_LC V) (v_LD V ++ [q])) -> vinv cx PIX X V ->
sim_head (y_idl cx) PIX (st_reset (y_idl cx) X (s' - 1)) (mkLV (repeat 0 4096) ((v_LD V ++ [q]) ++ [y_idl cx])) FIN ->
SR ubs0segs (mkCfg (mkst regs (Z_to_bv 64 TPC_RST) memc (seg_rom ubs0segs)) mdc)
(fun c' => exists r, cr_post X memc c' r /\ not_eidx r).
Proof using HBL HCX HRG HSEP HWIN HWT IMG RESET.
intros X V q s' regs memc HJ HPRE Hs' HVT HVI HSIM.
pose proof HVI as (LenLC & LenPIX & LenLD).
eapply SR_bind.
{ eapply (trst_segV API IMG RESET cx STK sp0 FP L A mem md Lc Ac mdc regs memc X s' PIX (mkLV (v_LC V) (v_LD V ++ [q]))); try eassumption.
cbn [v_LD]. rewrite length_app. cbn [length]. lia. }
cbv beta. intros c' (regs' & mem' & X' & -> & HJ' & HA & HTP & HsX' & -> & HVT').
eapply SR_mono.
{ eapply (from_tail X regs' mem' _ _ HJ' HTP HVT'); [apply vinv_reset; exact HVI|].
apply tail_sim_head; [lia | exact HSIM]. }
cbv beta. intros c''. apply cr_weak_ex. exact HA.
Qed.
Lemma inner_loop : forall (k : nat) X V regs memc s1 q,
(Z.to_nat (y_nP cx - s1) <= k)%nat ->
J memc mdc -> tlzw_regs_fix regs cx -> gen_at memc cx (la_lp X) (la_dp X) (la_mp X) -> ttables_at memc cx X ->
lzw_inv (y_idl cx) (y_nP cx) X ->
tin_pre cx regs s1 q -> la_s X < s1 <= y_nP cx - 1 -> 0 <= q < 4096 ->
vtabs_at memc cx PIX V -> vinv cx PIX X V -> sim_inner (y_idl cx) PIX X V s1 q FIN ->
SR ubs0segs (mkCfg (mkst regs (Z_to_bv 64 TPC_INNER) memc (seg_rom ubs0segs)) mdc)
(fun c' => exists regs' mem' o s1' q1,
c' = mkCfg (mkst regs' (Z_to_bv 64 (tio_pc o)) mem' (seg_rom ubs0segs)) mdc /\
J mem' mdc /\ (forall x, mem' x = memc x) /\ tlzw_regs_fix regs' cx /\
s1 <= s1' <= y_nP cx - 1 /\ 0 <= q1 < 4096 /\
tio_post cx X s1' q1 memc regs' o /\ tio_val (y_idl cx) X V PIX s1' q1 o /\ sim_inner (y_idl cx) PIX X V s1' q1 FIN /\
match o with TIO_cont _ => False | _ => True end).
Proof using A FP HBL HCX HRG HSEP HWIN IMG L md mem.
induction k as [|k IH]; intros X V regs memc s1 q Hk HJ HF HG HT HI HPRE Hs1 Hq HVT HVI HSIM; [lia|].
pose proof HVI as (LenLC & LenPIX & LenLD). pose proof (vtabs_px _ _ _ _ HVT) as HPX. pose proof (s_nonneg X HI) as Hs0.
assert (HSC : sim_ctx (y_idl cx) (y_nP cx) PIX) by (split; [exact Hidl_cx | split; [exact LenPIX | exact HPX]]).
eapply SR_bind.
{ eapply (tinner_iterV API IMG cx STK sp0 FP L A mem md Lc Ac mdc regs memc X s1 q PIX V); eassumption. }
cbv beta. intros c' (regs' & mem' & o & -> & HJ' & Hm & HF' & HP & HV).
destruct o as [|q'|q'|c].
2:{
destruct HP as (HPRE' & Hq' & Hs2). destruct HV as (Vc & Vq & Vq0).
pose proof (sim_inner_cont (y_idl cx) (y_nP cx) PIX HSC X V FIN s1 q q' HSIM HI Hq ltac:(lia) Vc Vq Vq0) as HSIM'.
eapply SR_mono.
{ eapply (IH X V regs' mem' (s1 + 1) q'); try eassumption; try lia.
- eapply gen_at_eq; eassumption.
- eapply ttables_at_eq; eassumption.
- eapply vtabs_at_eq; eassumption. }
cbv beta. intros c'' (regs'' & mem'' & o & s1' & q1 & -> & HJ'' & Hm' & HF'' & Hs1' & Hq1 & HP' & HV' & HSIM'' & Ho).
exists regs'', mem'', o, s1', q1. split; [reflexivity|]. split; [exact HJ''|].
split; [intros x; rewrite Hm'; apply Hm|]. split; [exact HF''|]. split; [lia|]. split; [exact Hq1|].
split; [| split; [exact HV' | split; [exact HSIM'' | exact Ho]]].
destruct o; cbn [tio_post] in HP' |- *; try exact HP'.
destruct HP' as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9). repeat split; try assumption; try lia.
intros j Hj. unfold mbyte. rewrite <- Hm. apply P9. exact Hj. }
all: apply SR_ret; exists regs', mem'; eexists; exists s1, q;
(split; [reflexivity|]); (split; [exact HJ'|]); (split; [exact Hm|]); (split; [exact HF'|]);
(split; [lia|]); (split; [lia|]); (split; [exact HP|]); (split; [exact HV|]); (split; [exact HSIM | exact I]).
Qed.
Lemma crawl_step : forall X V regs memc,
J memc mdc -> tlzw_regs_fix regs cx -> gen_at memc cx (la_lp X) (la_dp X) (la_mp X) -> ttables_at memc cx X ->
lzw_inv (y_idl cx) (y_nP cx) X ->
getr regs 11 = Z_to_bv 64 (y_nP cx) -> getr regs 22 = Z_to_bv 64 (la_s X) -> la_s X < y_nP cx ->
vtabs_at memc cx PIX V -> vinv cx PIX X V -> sim_head (y_idl cx) PIX X V FIN ->
SR ubs0segs (mkCfg (mkst regs (Z_to_bv 64 TPC_HEAD) memc (seg_rom ubs0segs)) mdc)
(fun c' => exists r, cr_post X memc c' r).
Proof using HBL HCX HRG HSEP HWIN HWT IMG RESET.
intros X V regs memc HJ HF HG HT HI H11 H22 Hs HVT HVI HSIM.
pose proof HVI as (LenLC & LenPIX & LenLD). pose proof (vtabs_px _ _ _ _ HVT) as HPX. pose proof (s_nonneg X HI) as Hs0.
pose proof Hidl_cx as Hidl.
assert (HSC : sim_ctx (y_idl cx) (y_nP cx) PIX) by (split; [exact Hidl | split; [exact LenPIX | exact HPX]]).
Local Ltac weaken HA := lazymatch type of HA with tabove_eq _ _ ?m => lazymatch goal with |- SR _ _ (fun c0 => exists r, cr_post ?X ?m0 c0 r) =>
apply (SR_mono _ _ (fun c' => exists r, cr_post X m c' r /\ not_eidx r));
[|cbv beta; intros c'' (r & Hr & _); exists r; eapply cr_weak; [exact HA | exact Hr]] end end.
eapply SR_bind.
{ eapply (thead_segV API IMG cx STK sp0 FP L A mem md Lc Ac mdc regs memc X PIX V); eassumption. }
cbv beta. intros c' (regs' & mem' & o & -> & HJ' & Hm & HF' & HP & HV).
pose proof (gen_at_eq _ _ cx _ _ _ HG Hm) as HG'. pose proof (ttables_at_eq _ _ _ _ HT Hm) as HT'.
pose proof (vtabs_at_eq _ _ cx PIX V HVT Hm) as HVT'.
pose proof (tabove_eq_of_eq cx _ _ Hm) as HAm.
destruct o as [|q|c1 c2|q].
-
cbn [tho_val] in HV. pose proof (sim_head_eidx (y_idl cx) (y_nP cx) PIX HSC X V FIN HSIM ltac:(lia) HV) as HFIN.
apply SR_ret. exists (CR_eidx X). exists regs', mem'. split; [reflexivity|]. split; [exact HJ'|].
split; [exact HAm|]. split; [exact HF'|]. split; [exact HG'|]. split; [exact HI | exact HFIN].
-
destruct HP as (P22 & P10 & Hq). cbn [tho_val] in HV. destruct HV as (Vc1 & HV).
pose proof (sim_head_emitc (y_idl cx) (y_nP cx) PIX HSC X V FIN q HSIM ltac:(lia) Vc1 HV) as HEX.
eapply SR_bind.
{ eapply (temitc_segV API IMG cx STK sp0 FP L A mem md Lc Ac mdc regs' mem' X q PIX V); try eassumption. }
cbv beta. intros c'' (regs'' & mem'' & X' & -> & HJ'' & HA2 & HTP & -> & HVT'').
pose proof (tabove_eq_trans cx _ _ _ HAm HA2) as HA. weaken HA.
eapply (from_tail X regs'' mem'' _ _ HJ'' HTP HVT''); [apply vinv_typec; exact HVI|].
apply tail_sim_exit; [destruct X as [TI LM LI TM s lp dp mp Cn R]; cbn [st_typec la_s]; lia | exact HEX].
-
destruct HP as (P22 & P10 & P14 & P15 & P13 & Hc1 & Hc2 & HTI0 & Hs1 & HC2). cbn [tho_val] in HV. destruct HV as (Vc1 & Vc2).
eapply SR_bind.
{ eapply (ttimiss_segV API IMG cx STK sp0 FP L A mem md Lc Ac mdc regs' mem' X c1 c2 PIX V); try eassumption.
intros j Hj. unfold mbyte. rewrite Hm. apply HC2. exact Hj. }
cbv beta. intros c'' (regs'' & mem'' & full & -> & HJ'' & HA2 & HP' & HVT'').
pose proof (tabove_eq_trans cx _ _ _ HAm HA2) as HA. weaken HA.
destruct full.
+ assert (Hfull : la_dp X = 4096) by (destruct HP' as (_ & _ & _ & _ & Hd & _); exact Hd).
eapply (from_rst X V c1 _); [exact HJ'' | exact HP' | lia | exact HVT'' | exact HVI |].
eapply (sim_head_timiss_rst (y_idl cx) (y_nP cx) PIX HSC X V FIN c1 c2); try eassumption; try lia; reflexivity.
+ destruct HP' as (X' & HTP & ->).
assert (Hnf : la_dp X < 4096).
{ eapply (dp_lt_of_inv X); [exact (proj1 (proj2 (proj2 (proj2 HTP)))) | destruct X as [TI LM LI TM s lp dp mp Cn R]; reflexivity]. }
eapply (from_tail X regs'' mem'' _ _ HJ'' HTP HVT''); [apply vinv_ti; exact HVI|].
apply tail_sim_head; [destruct X as [TI LM LI TM s lp dp mp Cn R]; cbn [st_ti la_s] in *; lia|].
eapply (sim_head_timiss_add (y_idl cx) (y_nP cx) PIX HSC X V FIN c1 c2); try eassumption; lia.
-
destruct HP as (P22 & P10 & P12 & P15 & P11 & P16 & Hq & Hs2). cbn [tho_val] in HV. destruct HV as (Vc1 & Vc2 & Vq & Vq0).
pose proof (sim_head_inner (y_idl cx) (y_nP cx) PIX HSC X V FIN q HSIM Vc1 Vc2 Vq Vq0 Hs0 ltac:(lia)) as HSI.
eapply SR_bind.
{ eapply (inner_loop (Z.to_nat (y_nP cx - (la_s X + 2))) X V regs' mem' (la_s X + 2) q); try eassumption; try lia.
unfold tin_pre. rewrite P22, P10, P12, P15, P11, P16. repeat split; f_equal; unfold y_nimg; lia. }
cbv beta. intros c'' (regs'' & mem'' & o & s1' & q1 & -> & HJ'' & Hm' & HF'' & Hs1' & Hq1 & HP' & HV' & HSI' & Ho).
pose proof (gen_at_eq _ _ cx _ _ _ HG' Hm') as HG''. pose proof (ttables_at_eq _ _ _ _ HT' Hm') as HT''.
pose proof (vtabs_at_eq _ _ cx PIX V HVT' Hm') as HVT''.
pose proof (tabove_eq_trans cx _ _ _ HAm (tabove_eq_of_eq cx _ _ Hm')) as HAm2.
destruct o as [|q'|q'|c]; [| destruct Ho | |].
+ cbn [tio_val] in HV'. pose proof (sim_inner_eidx (y_idl cx) (y_nP cx) PIX HSC X V FIN s1' q1 HSI' ltac:(lia) HV') as HFIN.
apply SR_ret. exists (CR_eidx X). exists regs'', mem''. split; [reflexivity|]. split; [exact HJ''|].
split; [exact HAm2|]. split; [exact HF''|]. split; [exact HG''|]. split; [exact HI | exact HFIN].
+ destruct HP' as (P22' & P10' & Hq' & Hs1e). cbn [tio_val] in HV'. destruct HV' as (Vc & Vq' & Vq0').
pose proof (sim_inner_emitc (y_idl cx) (y_nP cx) PIX HSC X V FIN s1' q1 q' HSI' HI Hq1 ltac:(lia) Hs1e Vc Vq' Vq0') as HEX.
eapply SR_bind.
{ eapply (temitc_segV API IMG cx STK sp0 FP L A mem md Lc Ac mdc regs'' mem'' X q' PIX V); try eassumption; lia. }
cbv beta. intros c3 (regs3 & mem3 & X' & -> & HJ3 & HA3 & HTP & -> & HVT3).
pose proof (tabove_eq_trans cx _ _ _ HAm2 HA3) as HA. weaken HA.
eapply (from_tail X regs3 mem3 _ _ HJ3 HTP HVT3); [apply vinv_typec; exact HVI|].
apply tail_sim_exit; [destruct X as [TI LM LI TM s lp dp mp Cn R]; cbn [st_typec la_s]; lia | exact HEX].
+ destruct HP' as (P22' & P10' & P17' & P14' & P12' & P23' & P13' & Hc & HC). cbn [tio_val] in HV'. destruct HV' as (Vcc & Vc & Vch). subst c.
eapply SR_bind.
{ eapply (tmiss_segV API IMG cx STK sp0 FP L A mem md Lc Ac mdc regs'' mem'' X s1' q1 (px PIX s1') PIX V); try eassumption.
- unfold tmiss_pre. repeat split; assumption.
- lia.
- intros j Hj. unfold mbyte. rewrite Hm'. apply HC. exact Hj. }
cbv beta. intros c3 (regs3 & mem3 & o & -> & HJ3 & HA3 & HP3 & HV3).
pose proof (tabove_eq_trans cx _ _ _ HAm2 HA3) as HA.
destruct o as [|X'|].
* cbn [tmo_val] in HV3. destruct HV3 as (Hfull & HVT3). weaken HA.
eapply (from_rst X V q1 _); [exact HJ3 | exact HP3 | lia | exact HVT3 | exact HVI |].
eapply (sim_miss_rst (y_idl cx) (y_nP cx) PIX HSC X V FIN s1' q1 (px PIX s1')); try eassumption; try reflexivity; lia.
* cbn [tmo_val] in HV3. destruct HV3 as (Hnf & [(HLM & -> & HVT3) | (HLM & HLI & -> & HVT3)]); weaken HA; destruct HP3 as [HTP HsX'].
-- eapply (from_tail X regs3 mem3 _ _ HJ3 HTP HVT3); [apply vinv_map; exact HVI|].
apply tail_sim_head; [lia|].
eapply (sim_miss_map (y_idl cx) (y_nP cx) PIX HSC X V FIN s1' q1 (px PIX s1')); try eassumption; try reflexivity; lia.
-- eapply (from_tail X regs3 mem3 _ _ HJ3 HTP HVT3); [apply vinv_first; exact HVI|].
apply tail_sim_head; [lia|].
eapply (sim_miss_first (y_idl cx) (y_nP cx) PIX HSC X V FIN s1' q1 (px PIX s1')); try eassumption; try reflexivity; lia.
* cbn [tmo_val] in HV3. destruct HV3 as (Hnf & HLM & HLI & HVT3).
eapply SR_bind.
{ eapply (tsw2_segV API IMG cx STK sp0 FP L A mem md Lc Ac mdc regs3 mem3 X s1' q1 (px PIX s1') PIX (mkLV (v_LC V) (v_LD V ++ [q1]))); try eassumption.
cbn [v_LD]. rewrite length_app. cbn [length]. lia. }
cbv beta. intros c4 (regs4 & mem4 & X' & -> & HJ4 & HA4 & HTP & HsX' & -> & HVT4).
pose proof (tabove_eq_trans cx _ _ _ HA HA4) as HA'. weaken HA'.
eapply (from_tail X regs4 mem4 _ _ HJ4 HTP HVT4); [apply vinv_switch; exact HVI|].
apply tail_sim_head; [lia|].
eapply (sim_miss_switch (y_idl cx) (y_nP cx) PIX HSC X V FIN s1' q1 (px PIX s1')); try eassumption; try reflexivity; lia.
Qed.
Lemma crawl_loop : forall (k : nat) X V regs memc,
(Z.to_nat (y_nP cx - la_s X) <= k)%nat ->
J memc mdc -> tlzw_regs_fix regs cx -> gen_at memc cx (la_lp X) (la_dp X) (la_mp X) -> ttables_at memc cx X ->
lzw_inv (y_idl cx) (y_nP cx) X ->
getr regs 11 = Z_to_bv 64 (y_nP cx) -> getr regs 22 = Z_to_bv 64 (la_s X) -> la_s X < y_nP cx ->
vtabs_at memc cx PIX V -> vinv cx PIX X V -> sim_head (y_idl cx) PIX X V FIN ->
SR ubs0segs (mkCfg (mkst regs (Z_to_bv 64 TPC_HEAD) memc (seg_rom ubs0segs)) mdc)
(fun c' => exists r, cr_post X memc c' r /\ match r with CR_head _ _ => False | _ => True end).
Proof using HBL HCX HRG HSEP HWIN HWT IMG RESET.
induction k as [|k IH]; intros X V regs memc Hk HJ HF HG HT HI H11 H22 Hs HVT HVI HSIM; [lia|].
eapply SR_bind; [eapply (crawl_step X V regs memc); eassumption|].
cbv beta. intros c' (r & HP). destruct r as [X'|X' V'|X' V'].
- apply SR_ret. exists (CR_eidx X'). split; [exact HP | exact I].
- destruct HP as (regs' & mem' & -> & HJ' & HA' & HF' & HG' & HT' & HI' & Hs' & P22 & P11 & HVT' & HVI' & HSIM').
eapply SR_mono; [eapply (IH X' V' regs' mem'); try eassumption; lia|].
cbv beta. intros c'' (r & HP' & Hr). exists r. split; [|exact Hr].
destruct r as [X''|X'' V''|X'' V'']; [| destruct Hr |].
+ eapply cr_weak; [exact HA' | exact HP'].
+ eapply cr_weak; [exact HA' | exact HP'].
- apply SR_ret. exists (CR_exit X' V'). split; [exact HP | exact I].
Qed.
End b.
End S.
End a.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
