(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YN06 YK0s.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YO38 YK0w.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP0j YP0g YP0r YP0c.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import UH04 UH07 UH06 UO3m UO3n
YI00 YI02 YI01 YI07 YI03 YI04 UI2a UI2b
UI2c UI2e UI27 UI2o UI2h UI2i UI2n UI2k UI2l UIYs.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section a. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section S.
Variable API : AllocAPI ubs2_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws ubs2_msyms MR := aa_laws API.
Hypothesis IMG : img_laws ubs2_msyms MR.
Hypothesis RESET : reset_spec API.
Section b.
Variables (cx : lzw_tcx) (STK sp0 : Z) (FP : list (Z * Z)) (L : layout) (A : astate) (mem : word -> option byte) (md : Model)
(Lc : layout) (Ac : astate) (mdc : Model).
Hypothesis HCX : tcx_ok cx.
Hypothesis HRG : tcx_ranges cx.
Hypothesis HSEP : tcx_seps cx.
Hypothesis HBL : tcx_blocks cx (blocks Lc Ac).
Hypothesis HWIN : tcx_win STK sp0 cx.
Hypothesis HWT : tcx_wtok STK sp0 FP (blocks L A) cx.
Let J := journal ubs2_msyms MR STK sp0 FP L A mem md Lc Ac.
Inductive crawl_res := CR_eidx (X' : lzw_abs) | CR_head (X' : lzw_abs) | CR_exit (X' : lzw_abs).
Definition cr_pc (r : crawl_res) : Z := match r with CR_eidx _ => TPC_EIDX | CR_head _ => TPC_HEAD | CR_exit _ => TPC_EXIT end.
Definition cr_post (X : lzw_abs) (memc : word -> option byte) (c' : config) (r : crawl_res) : Prop :=
exists regs' mem',
c' = mkCfg (mkst regs' (Z_to_bv 64 (cr_pc r)) mem' (seg_rom ubs2segs)) mdc /\
J mem' mdc /\ tabove_eq cx memc mem' /\ tlzw_regs_fix regs' cx /\
match r with
| CR_eidx X' => gen_at mem' cx (la_lp X') (la_dp X') (la_mp X') /\ lzw_inv (y_idl cx) (y_nP cx) X'
| CR_head X' => gen_at mem' cx (la_lp X') (la_dp X') (la_mp X') /\ ttables_at mem' cx X' /\ lzw_inv (y_idl cx) (y_nP cx) X' /\
la_s X < la_s X' < y_nP cx /\ getr regs' 22 = Z_to_bv 64 (la_s X') /\ getr regs' 11 = Z_to_bv 64 (y_nP cx)
| CR_exit X' => gen_at mem' cx (la_lp X') (la_dp X') (la_mp X') /\ lzw_inv (y_idl cx) (y_nP cx) X' /\ la_s X' = y_nP cx
end.
Lemma cr_weak : forall X m1 m2 c' r, tabove_eq cx m1 m2 -> cr_post X m2 c' r -> cr_post X m1 c' r.
Proof.
intros X m1 m2 c' r HA (regs' & mem' & Hc & HJ' & HA' & HR).
exists regs', mem'. split; [exact Hc|]. split; [exact HJ'|]. split; [eapply tabove_eq_trans; [exact HA | exact HA'] | exact HR].
Qed.
Definition not_eidx (r : crawl_res) : Prop := match r with CR_eidx _ => False | _ => True end.
Lemma cr_weak_ex : forall X m1 m2 c', tabove_eq cx m1 m2 ->
(exists r, cr_post X m2 c' r /\ not_eidx r) -> (exists r, cr_post X m1 c' r /\ not_eidx r).
Proof. intros X m1 m2 c' HA (r & H & Hr). exists r. split; [eapply cr_weak; [exact HA | exact H] | exact Hr]. Qed.
Lemma from_tail : forall X regs memc X',
J memc mdc -> ttail_post cx X regs memc X' ->
SR ubs2segs (mkCfg (mkst regs (Z_to_bv 64 TPC_TAIL) memc (seg_rom ubs2segs)) mdc)
(fun c' => exists r, cr_post X memc c' r /\ not_eidx r).
Proof.
intros X regs memc X' HJ (HF & HG & HT & HI & H22 & Hs).
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
destruct (Z.ltb_spec (la_s X') (y_nP cx)) as [Hlt | Hge].
- exists (CR_head X'). split; [|exact I]. exists regs', mem'. split; [reflexivity|]. split; [exact HJ'|].
split; [apply tabove_eq_of_eq; exact Hm|]. split; [exact HF'|].
split; [eapply gen_at_eq; eassumption|]. split; [eapply ttables_at_eq; eassumption|]. split; [exact HI|].
split; [lia|]. repeat split; assumption.
- exists (CR_exit X'). split; [|exact I]. exists regs', mem'. split; [reflexivity|]. split; [exact HJ'|].
split; [apply tabove_eq_of_eq; exact Hm|]. split; [exact HF'|].
split; [eapply gen_at_eq; eassumption|]. split; [exact HI | lia].
Qed.
Lemma from_rst : forall X s' regs memc,
J memc mdc -> trst_pre cx X s' regs memc ->
SR ubs2segs (mkCfg (mkst regs (Z_to_bv 64 TPC_RST) memc (seg_rom ubs2segs)) mdc)
(fun c' => exists r, cr_post X memc c' r /\ not_eidx r).
Proof.
intros X s' regs memc HJ HPRE.
eapply SR_bind; [eapply (trst_seg API IMG RESET cx STK sp0 FP L A mem md Lc Ac mdc); eassumption|].
cbv beta. intros c' (regs' & mem' & X' & -> & HJ' & HA & HTP & _).
eapply SR_mono; [eapply from_tail; eassumption|]. cbv beta. intros c''. apply cr_weak_ex. exact HA.
Qed.
Lemma inner_loop : forall (k : nat) X regs memc s1 q,
(Z.to_nat (y_nP cx - s1) <= k)%nat ->
J memc mdc -> tlzw_regs_fix regs cx -> gen_at memc cx (la_lp X) (la_dp X) (la_mp X) -> ttables_at memc cx X ->
lzw_inv (y_idl cx) (y_nP cx) X ->
tin_pre cx regs s1 q -> la_s X < s1 <= y_nP cx - 1 -> 0 <= q < 4096 ->
SR ubs2segs (mkCfg (mkst regs (Z_to_bv 64 TPC_INNER) memc (seg_rom ubs2segs)) mdc)
(fun c' => exists regs' mem' o s1' q1,
c' = mkCfg (mkst regs' (Z_to_bv 64 (tio_pc o)) mem' (seg_rom ubs2segs)) mdc /\
J mem' mdc /\ (forall x, mem' x = memc x) /\ tlzw_regs_fix regs' cx /\
s1 <= s1' <= y_nP cx - 1 /\ 0 <= q1 < 4096 /\
tio_post cx X s1' q1 memc regs' o /\ match o with TIO_cont _ => False | _ => True end).
Proof.
induction k as [|k IH]; intros X regs memc s1 q Hk HJ HF HG HT HI HPRE Hs1 Hq; [lia|].
eapply SR_bind.
{ eapply (tinner_iter API IMG cx STK sp0 FP L A mem md Lc Ac mdc regs memc X s1 q); eassumption. }
cbv beta. intros c' (regs' & mem' & o & -> & HJ' & Hm & HF' & HP).
destruct o as [|q'|q'|c].
2:{
destruct HP as (HPRE' & Hq' & Hs2).
eapply SR_mono.
{ eapply (IH X regs' mem' (s1 + 1) q'); try eassumption; try lia.
- eapply gen_at_eq; eassumption.
- eapply ttables_at_eq; eassumption. }
cbv beta. intros c'' (regs'' & mem'' & o & s1' & q1 & -> & HJ'' & Hm' & HF'' & Hs1' & Hq1 & HP' & Ho).
exists regs'', mem'', o, s1', q1. split; [reflexivity|]. split; [exact HJ''|].
split; [intros x; rewrite Hm'; apply Hm|]. split; [exact HF''|]. split; [lia|]. split; [exact Hq1|]. split; [| exact Ho].
destruct o; cbn [tio_post] in HP' |- *; try exact HP'.
destruct HP' as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9). repeat split; try assumption; try lia.
intros j Hj. unfold mbyte. rewrite <- Hm. apply P9. exact Hj. }
all: apply SR_ret; exists regs', mem'; eexists; exists s1, q;
(split; [reflexivity|]); (split; [exact HJ'|]); (split; [exact Hm|]); (split; [exact HF'|]);
(split; [lia|]); (split; [lia|]); (split; [exact HP | exact I]).
Qed.
Lemma crawl_step : forall X regs memc,
J memc mdc -> tlzw_regs_fix regs cx -> gen_at memc cx (la_lp X) (la_dp X) (la_mp X) -> ttables_at memc cx X ->
lzw_inv (y_idl cx) (y_nP cx) X ->
getr regs 11 = Z_to_bv 64 (y_nP cx) -> getr regs 22 = Z_to_bv 64 (la_s X) -> la_s X < y_nP cx ->
SR ubs2segs (mkCfg (mkst regs (Z_to_bv 64 TPC_HEAD) memc (seg_rom ubs2segs)) mdc)
(fun c' => exists r, cr_post X memc c' r).
Proof.
intros X regs memc HJ HF HG HT HI H11 H22 Hs.
Local Ltac weaken HA := lazymatch type of HA with tabove_eq _ _ ?m => lazymatch goal with |- SR _ _ (fun c0 => exists r, cr_post ?X ?m0 c0 r) =>
apply (SR_mono _ _ (fun c' => exists r, cr_post X m c' r /\ not_eidx r));
[|cbv beta; intros c'' (r & Hr & _); exists r; eapply cr_weak; [exact HA | exact Hr]] end end.
Local Ltac eidx X regs' mem' HJ' HF' HG HI Hm :=
apply SR_ret; exists (CR_eidx X); exists regs', mem'; split; [reflexivity|]; split; [exact HJ'|];
split; [apply tabove_eq_of_eq; exact Hm|]; split; [exact HF'|];
split; [eapply gen_at_eq; [exact HG | exact Hm] | exact HI].
eapply SR_bind.
{ eapply (thead_seg API IMG cx STK sp0 FP L A mem md Lc Ac mdc regs memc X); eassumption. }
cbv beta. intros c' (regs' & mem' & o & -> & HJ' & Hm & HF' & HP).
pose proof (gen_at_eq _ _ cx _ _ _ HG Hm) as HG'. pose proof (ttables_at_eq _ _ _ _ HT Hm) as HT'.
pose proof (tabove_eq_of_eq cx _ _ Hm) as HAm.
destruct o as [|q|c1 c2|q].
-
eidx X regs' mem' HJ' HF' HG HI Hm.
-
destruct HP as (P22 & P10 & Hq).
eapply SR_bind.
{ eapply (temitc_seg API IMG cx STK sp0 FP L A mem md Lc Ac mdc regs' mem' X q); try eassumption. }
cbv beta. intros c'' (regs'' & mem'' & X' & -> & HJ'' & HA2 & HTP).
pose proof (tabove_eq_trans cx _ _ _ HAm HA2) as HA. weaken HA. eapply from_tail; eassumption.
-
destruct HP as (P22 & P10 & P14 & P15 & P13 & Hc1 & Hc2 & HTI0 & Hs1 & HC2).
eapply SR_bind.
{ eapply (ttimiss_seg API IMG cx STK sp0 FP L A mem md Lc Ac mdc regs' mem' X c1 c2); try eassumption.
intros j Hj. unfold mbyte. rewrite Hm. apply HC2. exact Hj. }
cbv beta. intros c'' (regs'' & mem'' & full & -> & HJ'' & HA2 & HP').
pose proof (tabove_eq_trans cx _ _ _ HAm HA2) as HA. weaken HA.
destruct full.
+ eapply (from_rst X _); [exact HJ'' | exact HP'].
+ destruct HP' as (X' & HTP). eapply from_tail; eassumption.
-
destruct HP as (P22 & P10 & P12 & P15 & P11 & P16 & Hq & Hs2).
eapply SR_bind.
{ eapply (inner_loop (Z.to_nat (y_nP cx - (la_s X + 2))) X regs' mem' (la_s X + 2) q); try eassumption; try lia.
unfold tin_pre. rewrite P22, P10, P12, P15, P11, P16. repeat split; f_equal; unfold y_nimg; lia. }
cbv beta. intros c'' (regs'' & mem'' & o & s1' & q1 & -> & HJ'' & Hm' & HF'' & Hs1' & Hq1 & HP' & Ho).
pose proof (gen_at_eq _ _ cx _ _ _ HG' Hm') as HG''. pose proof (ttables_at_eq _ _ _ _ HT' Hm') as HT''.
pose proof (tabove_eq_trans cx _ _ _ HAm (tabove_eq_of_eq cx _ _ Hm')) as HAm2.
destruct o as [|q'|q'|c]; [| destruct Ho | |].
+ apply SR_ret. exists (CR_eidx X). exists regs'', mem''. split; [reflexivity|]. split; [exact HJ''|].
split; [exact HAm2|]. split; [exact HF''|]. split; [exact HG'' | exact HI].
+ destruct HP' as (P22' & P10' & Hq' & Hs1e).
eapply SR_bind.
{ eapply (temitc_seg API IMG cx STK sp0 FP L A mem md Lc Ac mdc regs'' mem'' X q'); try eassumption; lia. }
cbv beta. intros c3 (regs3 & mem3 & X' & -> & HJ3 & HA3 & HTP).
pose proof (tabove_eq_trans cx _ _ _ HAm2 HA3) as HA. weaken HA. eapply from_tail; eassumption.
+ destruct HP' as (P22' & P10' & P17' & P14' & P12' & P23' & P13' & Hc & HC).
eapply SR_bind.
{ eapply (tmiss_seg API IMG cx STK sp0 FP L A mem md Lc Ac mdc regs'' mem'' X s1' q1 c); try eassumption.
- unfold tmiss_pre. repeat split; assumption.
- lia.
- intros j Hj. unfold mbyte. rewrite Hm'. apply HC. exact Hj. }
cbv beta. intros c3 (regs3 & mem3 & o & -> & HJ3 & HA3 & HP3).
pose proof (tabove_eq_trans cx _ _ _ HAm2 HA3) as HA.
destruct o as [|X'|].
* weaken HA. eapply (from_rst X _); [exact HJ3 | exact HP3].
* weaken HA. destruct HP3 as [HTP _]. eapply from_tail; eassumption.
* eapply SR_bind.
{ eapply (tsw2_seg API IMG cx STK sp0 FP L A mem md Lc Ac mdc regs3 mem3 X s1' q1 c); eassumption. }
cbv beta. intros c4 (regs4 & mem4 & X' & -> & HJ4 & HA4 & HTP & _).
pose proof (tabove_eq_trans cx _ _ _ HA HA4) as HA'. weaken HA'. eapply from_tail; eassumption.
Qed.
Lemma crawl_loop : forall (k : nat) X regs memc,
(Z.to_nat (y_nP cx - la_s X) <= k)%nat ->
J memc mdc -> tlzw_regs_fix regs cx -> gen_at memc cx (la_lp X) (la_dp X) (la_mp X) -> ttables_at memc cx X ->
lzw_inv (y_idl cx) (y_nP cx) X ->
getr regs 11 = Z_to_bv 64 (y_nP cx) -> getr regs 22 = Z_to_bv 64 (la_s X) -> la_s X < y_nP cx ->
SR ubs2segs (mkCfg (mkst regs (Z_to_bv 64 TPC_HEAD) memc (seg_rom ubs2segs)) mdc)
(fun c' => exists r, cr_post X memc c' r /\ match r with CR_head _ => False | _ => True end).
Proof.
induction k as [|k IH]; intros X regs memc Hk HJ HF HG HT HI H11 H22 Hs; [lia|].
eapply SR_bind; [eapply (crawl_step X regs memc); eassumption|].
cbv beta. intros c' (r & HP). destruct r as [X'|X'|X'].
- apply SR_ret. exists (CR_eidx X'). split; [exact HP | exact I].
- destruct HP as (regs' & mem' & -> & HJ' & HA' & HF' & HG' & HT' & HI' & Hs' & P22 & P11).
eapply SR_mono; [eapply (IH X' regs' mem'); try eassumption; lia|].
cbv beta. intros c'' (r & HP' & Hr). exists r. split; [|exact Hr].
destruct r as [X''|X''|X'']; [| destruct Hr |].
+ eapply cr_weak; [exact HA' | exact HP'].
+ eapply cr_weak; [exact HA' | exact HP'].
- apply SR_ret. exists (CR_exit X'). split; [exact HP | exact I].
Qed.
End b.
End S.
End a.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
