(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: ported from libreac/fuzz_disco lib/A/Rt/StackFree6.v (itself ported from proofs/cgif/cgif_rgb_fuzzer/lib/YF3h.v and YF9b.v) and restated onto lib/Reusable/StackFreeDef.v's astack_free_realizes; the fill pattern at 0x10350 is read through the AR constant cell that lib/A/Rt/StackFree6Tbl.v's sf_rodata row checks, as cgif_rgb_fuzzer YF3h.v's sf_rodata rows are; every address and class constant is cited from StackFree6Tbl.v; module names. *)
(* Modified by Theorem Labs, 2026-10: the asan-ubsan twin of lib/A/Rt/StackFree6S.v, relocated to libreac/fuzz_disco's asan-ubsan build: the same text over that image's addresses and the asan-ubsan core's module names. *)
(* Modified by Theorem Labs, 2026-10: relocated from a working branch cb2a0ebe89b proofs/libreac/fuzz_disco/lib/Y/Rt/StackFree6S.v to libreac/fuzz_grant image B (asan-ubsan): module paths only; this file holds no image number, every address and class constant comes from StackFree6Tbl.v. *)
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0k YK0s YK0n YP0n YK1d.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP04 YP0g YP01.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0v YO0f.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YG05 YG0s YG0t.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import YB1v YE34 YF0l YF0m YF0x YE2y.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import StackFreeDef.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Rt Require Import StackFree6Tbl.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section e. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section d.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis TB : GrantSyms B.
Theorem tfib_stack_free_6S : astack_free_realizes tfibsegs B SF_ENTRY CID.
Proof.
intros ly S W regs mem md pos n HPRE Hin G10 G11 Hn Hn8 HTR.
pose proof (sf_span_cid n) as SPAN.
pose proof HPRE as (HAR & Hra & Hal16 & Hslo & Htop & HpresE & Hgp & Htp).
pose proof YF0x.Hwx_tfa as Hwx.
destruct gconsts as (KMB & KME & KSB & KSE & KLE & KHS & KFS & KSO & KES & KIL & KRO & KI1 & KI2 & KI3 & KB & KN & KFR & KFL & KW & KSH & KFN).
set (H := w_H W) in *. set (sp0 := spZ regs) in *.
rewrite SPAN. rewrite fbytes_6 in Hn, HTR.
pose proof (proj1 HAR) as M.
pose proof (am_layout B ly S _ M) as HLY.
pose proof (lo_top ly HLY) as (Lbot & Ltop & _ & Lhi & _ & _ & Lbeg).
pose proof (lo_stk_ceil ly HLY) as SC. unfold ASAN_CEIL in SC.
pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as CR. unfold ASAN_CEIL in CR.
pose proof (img_cover_of_ledger ly _ _ (proj1 (proj2 HAR))) as IMG.
assert (ZF : zone3 (ly_F ly) kFakeStackSize).
{ pose proof (proj1 (Forall_forall _ _) (lo_app ly HLY) (ly_F ly, kFakeStackSize)
ltac:(unfold owned_extents; cbn; tauto)) as IA. cbn [fst snd] in IA.
assert (D9 : zdisjoint (ly_F ly, kFakeStackSize) (ly_img ly)).
{ pose proof (lo_disj ly HLY) as PD.
exact (pairwise_In zdisjoint (static_extents ly) (ly_F ly, kFakeStackSize) (ly_img ly)
(owned_extents ly ++ [(ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly)]) [ly_img ly]
ltac:(unfold static_extents; rewrite <- app_assoc; reflexivity) PD
ltac:(apply in_app_iff; left; unfold owned_extents; cbn; tauto) ltac:(left; reflexivity)). }
exact (zone3_intro ly (ly_F ly) kFakeStackSize IMG ltac:(lia) IA D9). }
destruct ZF as (HF1 & HF2 & HFz). unfold ASAN_CEIL in HF2.
assert (ZONE : exists hi : bool,
(hi = true /\ kHighMemBeg <= ly_F ly /\ ly_F ly + kFakeStackSize <= alloc_ceiling) \/
(hi = false /\ YF0x.TFIB_IMG_END <= ly_F ly /\ ly_F ly + kFakeStackSize <= kLowShadowBeg)).
{ unfold zone3cases, ASAN_CEIL in HFz. destruct HFz as [X|[X|X]].
- exfalso. lia.
- exists false. right. split; [reflexivity | exact X].
- exists true. left. split; [reflexivity | exact X]. }
destruct ZONE as [hi HZ].
set (F := ly_F ly) in *.
assert (HFlo : YF0x.TFIB_IMG_END <= F) by (destruct HZ as [(_ & X1 & X2) | (_ & X1 & X2)]; lia).
assert (HFhi : F + kFakeStackSize <= alloc_ceiling) by (destruct HZ as [(_ & X1 & X2) | (_ & X1 & X2)]; lia).
assert (HPOS : 0 <= pos < FS_N).
{ pose proof (proj1 (Forall_forall _ _) (wfs_live _ (wf_fakestack _ _ _ _ _ (am_wf B ly S _ M))) (CID, pos) Hin) as [_ X].
cbn [fst snd] in X. rewrite frames_6 in X. exact X. }
set (fa := frame_addr ly CID pos) in *.
set (flg := flag_addr ly CID pos) in *.
assert (Efa : fa = F + FS_FROFF + pos * FS_B)
by (unfold fa, frame_addr; rewrite frame_off_6; lia).
assert (Eflg : flg = F + FS_FLOFF + pos)
by (unfold flg, flag_addr; rewrite flag_off_6; lia).
destruct (al_frames _ _ LAWS ly S W mem md CID pos HAR Hin) as (Hal32 & Happ & Hfr & Hsh).
destruct (al_flag _ _ LAWS ly S W mem md CID pos HAR Hin) as (Hflp & Hflo & Hflapp & Hflc).
fold fa in Hal32, Happ, Hfr, Hsh. fold flg in Hflp, Hflo, Hflapp, Hflc.
rewrite fbytes_6 in Hfr, Hsh, Happ. change (FS_B / 8) with SH_N in Hsh.
assert (Hfar : YF0x.TFIB_IMG_END <= fa /\ fa + FS_B <= F + kFakeStackSize)
by (rewrite Efa; lia).
assert (Hflgr : F <= flg < F + kFakeStackSize) by (rewrite Eflg; lia).
assert (Hsp : alloc_ceiling + ESTACK <= sp0) by lia.
assert (Hsphi : sp0 <= kHighMemEnd) by lia.
assert (Hsplo : kHighMemBeg + SF_WIN <= sp0) by lia.
set (sh := shadow_addr fa) in *.
assert (HQE : exists q, sh = SHADOW_OFF + q /\ 8 * q <= fa < 8 * q + 8).
{ exists (fa / 8). split; [reflexivity|].
pose proof (Z.div_mod fa 8 ltac:(lia)). pose proof (Z.mod_pos_bound fa 8 ltac:(lia)). lia. }
destruct HQE as (q8 & Esh & HQ).
assert (HSHlo : kLowMemEnd <= sh) by (rewrite Esh; lia).
assert (HSHhi : sh + SH_N <= kHighMemBeg) by (rewrite Esh; lia).
assert (HSHb : RO_END < sh /\ sh + SH_N <= sp0 - ESTACK) by lia.
assert (HSHff : sh + SH_N <= fa \/ fa + FS_B <= sh)
by (destruct HZ as [(_ & X1 & X2) | (_ & X1 & X2)]; [left; lia | right; lia]).
assert (HSHflg : sh + SH_N <= flg \/ flg < sh)
by (destruct HZ as [(_ & X1 & X2) | (_ & X1 & X2)]; [left; lia | right; lia]).
assert (HSHu : 0 <= sh /\ sh + SH_N < 2 ^ 64) by lia.
set (E := Ereg regs [w64 flg; w64 sh]).
assert (EEreg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew E i = getr regs r)
by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (E2 : bv_unsigned (ew E 2) = sp0) by (rewrite (EEreg 2%nat 2%bv eq_refl); reflexivity).
assert (E10 : bv_unsigned (ew E 10) = fa)
by (rewrite (EEreg 10%nat 10%bv eq_refl), G10; apply unsigned_lit_small; lia).
assert (EF : ew E aFLG = w64 flg) by (subst E; exact (ew_Ereg_extra regs _ 0)).
assert (ES : ew E aSH = w64 sh) by (subst E; exact (ew_Ereg_extra regs _ 1)).
assert (UF : bv_unsigned (ew E aFLG) = flg) by (rewrite EF; apply unsigned_lit_small; lia).
assert (US : bv_unsigned (ew E aSH) = sh) by (rewrite ES; apply unsigned_lit_small; lia).
pose proof UF as UFn. pose proof US as USn. unfold aFLG in UFn. unfold aSH in USn.
assert (HS0 : st_ok tfibsegs E (ss0 hi) (restrict H (mkst regs (Z_to_bv 64 SF_ENTRY) mem (seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx. unfold ss0, sf_mem.
apply (entry_st_ok_full tfibsegs); change (Ereg regs [w64 flg; w64 sh]) with E.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- change (stk :: rFF :: rFLG :: map ro_region sf_rodata)
with ([stk; rFF; rFLG] ++ map ro_region sf_rodata).
apply Forall_app. split; [|exact (rodata_ok B TB sf_rodata ly S H mem E (sf_rodata_chk ly) M)].
repeat apply Forall_cons; try apply Forall_nil.
+ unfold stk. apply (region_ok_stack tfibsegs E _ 2 sp0 (- SF_WIN)); [exact E2 | lia | lia |].
intros a Ha. apply (YF0x.apresent_writable H); [lia|].
apply HpresE. lia.
+ unfold rFF, region_ok.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite E10. unfold FF_OFF.
split; [lia|]. split; [lia|].
split; [intros o Ho; exfalso; lia|]. apply Forall_cons; [|apply Forall_nil].
eapply (chunk_ok_val tfibsegs E _ fa FF_OFF 8%N (SOff aFLG 0) flg);
[cbn [sv_denot]; rewrite ?UF, ?UFn, Z.add_0_r; reflexivity | unfold FF_OFF; cbn; lia | unfold FF_OFF; cbn; lia |].
change (N.to_nat 8) with 8%nat. replace (fa + FF_OFF) with (fa + FS_B - 8) by (unfold FF_OFF; lia).
exact (YE2y.val_mem_of_rdword H mem _ _ HTR).
+ unfold rFLG, region_ok.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite ?UF, ?UFn.
split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
intros o Ho. replace (flg + o) with flg by lia.
apply (YF0x.apresent_writable H); [lia | exact Hflp].
- apply pairwise_disjoint_of_extents.
unfold stk, rFF, rFLG, sf_rodata, icpt_rodata, ro_region, extent_of_region, SF_K, FF_OFF.
cbn [map app fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val Z.of_N].
rewrite ?E2, ?E10, ?UF, ?UFn.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
repeat split; lia.
- split; [|split; exact I].
cbn [f_atoms atoms_ok sf_facts]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite ?E2, ?E10, ?UF, ?UFn.
destruct al_pows as (P4 & P5 & P0). rewrite ?P4, ?P5, ?P0.
destruct HZ as [(Eh & X1 & X2) | (Eh & X1 & X2)]; subst hi; cbn [ffLO ffHI];
repeat split; first [exact Hal16 | exact Hal32 | apply Z.mod_1_r | lia]. }
unfold cfg_at. change (w64 SF_ENTRY) with (Z_to_bv 64 SF_ENTRY).
eapply SRr_bind; [apply (sf_phase_to W E SF_FILL _ _ _ _ _ HS0 (r_1 hi))|].
cbv beta. intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HFm1 & HFrm1).
assert (MEQ1 : forall z : word, ~ (sp0 - SF_WIN <= bv_unsigned z < sp0) -> bv_unsigned z <> flg -> ms_mem ms1 z = mem z).
{ intros z Hz1 Hz2. apply HFm1. intros Hw.
cbn [ss_mem ss0] in Hw. destruct (sf_windows E _ Hw) as [X|X]; [rewrite E2 in X; lia | rewrite UF in X; lia]. }
clear HFm1 HFrm1.
destruct (e1_facts hi) as (Hpc1 & Hrv1 & Hr10).
assert (A10 : getr (ms_regs ms1) 10 = w64 sh).
{ rewrite (YF0x.st_ok_reg_denot H E (e1 hi) ms1 10%bv HS1).
change (sr_get (ss_regs (e1 hi)) 10%bv) with (RG (e1 hi) 10). rewrite Hr10.
rewrite (a0e_denot E fa E10 ltac:(lia)). reflexivity. }
assert (HSH1 : forall i, 0 <= i < SH_N -> apresent H (ms_mem ms1) (sh + i)).
{ intros i Hi. apply (YF0x.apresent_same H mem); [|exact (proj1 (Hsh i Hi))].
apply MEQ1; rewrite unsigned_lit_small by lia; [lia | destruct HSHflg; lia]. }
assert (HSA : st_ok tfibsegs E
(mkSS (ss_pc (e1 hi)) (ss_regs (e1 hi)) (rSH :: ss_mem (e1 hi)) (ss_resv (e1 hi)) (ss_facts (e1 hi)))
(restrict H ms1)).
{ apply st_ok_add_region; [exact HS1 | exact rSH_wf | |].
- unfold rSH, region_ok.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite ?US, ?USn.
split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
intros o Ho. cbn [ms_mem restrict].
apply (YF0x.apresent_writable H); [lia|]. exact (HSH1 o Ho).
- rewrite (e1_mem hi). unfold memE1, rSH.
cbn [all_disjoint]. unfold extent_disjoint.
cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val].
rewrite ?US, ?USn, ?E2, ?E10, ?UFn, ?UF.
repeat split; lia. }
assert (HSC : st_ok tfibsegs E (ssC hi) (restrict H ms1)).
{ unfold ssC.
exact (YF0x.st_ok_pin_reg E _ (restrict H ms1) 10%bv (SOff aSH 0) HSA ltac:(discriminate)
ltac:(cbn [sv_denot ms_regs restrict]; rewrite ?US, ?USn, Z.add_0_r, A10; reflexivity)). }
eapply SRr_bind; [apply (sf_phase W E (ssC hi) _ _ _ _ HSC (r_2 hi))|].
cbv beta. intros W2 c2 _ (-> & ms2 & mat2 & -> & HS2 & HFm2 & HFrm2).
rewrite wvb_collapse.
assert (MEQ2 : forall z : word, ~ (sh <= bv_unsigned z < sh + SH_N) -> ~ (sp0 - SF_WIN <= bv_unsigned z < sp0) ->
bv_unsigned z <> flg -> ms_mem ms2 z = ms_mem ms1 z).
{ intros z Hz0 Hz1 Hz2. apply HFm2. intros Hw. destruct (ssC_windows hi E _ Hw) as [X|[X|X]];
[rewrite US in X; lia | rewrite E2 in X; lia | rewrite UF in X; lia]. }
clear HFm2 HFrm2.
assert (MEQ : forall z : word, ~ (sh <= bv_unsigned z < sh + SH_N) -> ~ (sp0 - SF_WIN <= bv_unsigned z < sp0) ->
bv_unsigned z <> flg -> ms_mem ms2 z = mem z).
{ intros z Ha Hb Hc. rewrite (MEQ2 z Ha Hb Hc). exact (MEQ1 z Hb Hc). }
destruct (e2_facts hi) as (Hpc2 & Hrv2 & Hkeep2).
destruct (e2_regions hi) as (NR0 & NR1 & NR2 & NR3).
eapply (SRr_ret_at tfibsegs tbl_sf tbl_sf_ok Hwx W E (e2 hi) ms2);
[exact HS2 | exact Hrv2 | rewrite Hpc2; exact ret_at_end |].
intros mat'. rewrite wvb_collapse.
set (regs2 := ms_regs ms2) in *. set (mem2 := ms_mem ms2) in *.
assert (KEEP : forall rz, In rz sf_keep ->
getr regs2 (Z_to_bv 5 rz) = getr regs (Z_to_bv 5 rz)).
{ intros rz Hrz. rewrite forallb_forall in Hkeep2. specialize (Hkeep2 rz Hrz). cbn beta in Hkeep2.
apply sv_eqb_eq in Hkeep2.
destruct (sf_keep_ok rz Hrz) as (Hr0 & U5).
unfold regs2. rewrite (YF0x.st_ok_reg_denot H E (e2 hi) ms2 (Z_to_bv 5 rz) HS2).
change (sr_get (ss_regs (e2 hi)) (Z_to_bv 5 rz)) with (RG (e2 hi) rz). rewrite Hkeep2.
cbn [sv_denot]. rewrite (EEreg (Z.to_nat rz) (Z_to_bv 5 rz)) by (rewrite U5; lia).
rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
pose proof (KEEP 1 ltac:(unfold sf_keep; cbn; tauto)) as Q1.
replace (Z_to_bv 5 1) with (1%bv : bv 5) in Q1 by (apply bv_eq; reflexivity).
assert (PW2 : forall a, sp0 - SF_WIN <= a < sp0 -> apresent H mem2 a).
{ intros a Ha. destruct rSTK2_shape as (Bs & Ws1 & Ws2).
apply (YF0x.st_ok_window_apresent H E (e2 hi) ms2 1 rSTK2 a HS2 NR1).
- rewrite Bs, Ws1, Ws2. cbn [base_val]. rewrite E2. lia.
- lia. }
assert (PWE : forall a, sp0 - ESTACK <= a < sp0 -> apresent H mem2 a).
{ intros a Ha. destruct (Z_lt_le_dec a (sp0 - SF_WIN)) as [L|L]; [|apply PW2; lia].
apply (YF0x.apresent_same H mem mem2 a).
- apply MEQ; rewrite unsigned_lit_small by lia.
+ lia.
+ lia.
+ lia.
- apply HpresE. lia. }
assert (ZSH : forall i, 0 <= i < SH_N -> aview tfibsegs H mem2 (sh + i) = Some SH_REL).
{ intros i Hi.
assert (Hq : 0 <= i / 8 < FILL_N) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
pose proof (YF0x.st_ok_chunk_val H E (e2 hi) ms2 0 rSH2 (Z.to_nat (FILL_N - 1 - i / 8)) (8 * (i / 8)) 8%N (SLit F5W) F5W
HS2 NR0 (rSH2_nth (i / 8) Hq) eq_refl F5W_range ltac:(cbn; lia)) as VM.
rewrite (proj1 rSH2_shape) in VM. cbn [base_val] in VM. rewrite ?US, ?USn in VM.
change (N.to_nat 8) with 8%nat in VM.
pose proof (Z.mod_pos_bound i 8 ltac:(lia)) as Hmod.
pose proof (aview_of_val_mem H mem2 (sh + 8 * (i / 8)) (Z.to_nat (i mod 8)) 8 F5W VM ltac:(lia)) as X.
rewrite Z2Nat.id in X by (apply Z.mod_pos_bound; lia).
replace (sh + 8 * (i / 8) + i mod 8) with (sh + i) in X by (pose proof (Z.div_mod i 8 ltac:(lia)); lia).
rewrite X, f5_byte by lia. reflexivity. }
assert (FL2 : aview tfibsegs H mem2 flg = Some 0).
{ destruct rFLG2_shape as (Bf & Wf1 & Wf2 & Cf).
pose proof (YF0x.st_ok_chunk_val H E (e2 hi) ms2 3 rFLG2 0 0 1%N (SLit 0) 0 HS2 NR3 Cf eq_refl
ltac:(cbn; lia) ltac:(cbn; lia)) as VM.
rewrite Bf in VM. cbn [base_val] in VM. rewrite ?UF, ?UFn, Z.add_0_r in VM.
change (N.to_nat 1) with 1%nat in VM.
pose proof (aview_of_val_mem H mem2 flg 0%nat 1 0 VM ltac:(lia)) as X.
cbn [Z.of_nat] in X. rewrite Z.add_0_r in X. rewrite X. reflexivity. }
assert (AVout : forall a, 0 <= a < 2 ^ 64 -> ~ (sh <= a < sh + SH_N) -> a <> flg ->
~ (sp0 - ESTACK <= a < sp0) -> aview tfibsegs H mem2 a = aview tfibsegs H mem a).
{ intros a Ha X1 X2 X3. apply (YF0x.aview_same H mem mem2 a).
apply MEQ; rewrite unsigned_lit_small by exact Ha;
[exact X1 | lia | exact X2]. }
pose proof (same_but_materialized_frame md _ (with_vm_backing_same md mat')) as MF.
replace (v_jalr (getr regs2 1) 0) with (w64 (raZ regs))
by (rewrite Q1, Hra; unfold raZ, w64; rewrite Z_to_bv_bv_unsigned; reflexivity).
split; [reflexivity|].
exists regs2, mem2, (with_vm_backing (m_vm_lazy md) mat' md).
split; [unfold cfg_at; reflexivity|].
split; [|split; [|split; [exact (with_vm_backing_same md mat') | split; [|split]]]].
-
apply (astack_free_law_ok tfibsegs B ly S W mem md mem2 _ CID pos HAR Hin).
+ exact FL2.
+ intros a Hr Hown Hnf. apply AVout; [exact Hr | | exact Hnf |].
* intros Hc. apply (proj2 (Hsh (a - sh) ltac:(lia))). replace (sh + (a - sh)) with a by lia. exact Hown.
* intros Hc. exact (al_stack _ _ LAWS ly S W mem md a HAR ltac:(lia) Hown).
+ intros a Hvw. fold H in Hvw |- *.
rewrite (YE2y.aview_mod H mem2 a). rewrite (YE2y.aview_mod H mem a) in Hvw.
pose proof (Z.mod_pos_bound a (2 ^ 64) ltac:(lia)) as Hr. set (a' := a mod 2 ^ 64) in *. clearbody a'.
destruct (Z.eq_dec a' flg) as [->|Hnf]; [rewrite FL2; discriminate|].
destruct (Z_lt_le_dec a' sh) as [L1|L1]; [| destruct (Z_lt_le_dec a' (sh + SH_N)) as [L2|L2]].
2:{ replace a' with (sh + (a' - sh)) by lia. rewrite ZSH by lia. discriminate. }
all: destruct (Z_lt_le_dec a' (sp0 - ESTACK)) as [L3|L3];
[rewrite AVout by lia; exact Hvw|].
all: destruct (Z_lt_le_dec a' sp0) as [L4|L4];
[| rewrite AVout by lia; exact Hvw].
all: apply YE2y.aview_some_of_apresent; apply PWE; lia.
+ apply MF.
+ apply MF.
+ apply MF.
+ intros a Hb Hh.
refine (hs_kept_gen H mem mem2 (fun b => (sh <= b < sh + SH_N) \/ (sp0 - SF_WIN <= b < sp0) \/ b = flg) _ _ a Hb Hh).
* intros z Hz. apply MEQ; intros Hc; apply Hz; tauto.
* intros b Hb'. exists mem. destruct Hb' as [Hb' | Hb2].
-- replace b with (sh + (b - sh)) by lia. exact (proj1 (Hsh (b - sh) ltac:(lia))).
-- destruct Hb2 as [Hb2 | Hb3].
++ apply HpresE. lia.
++ rewrite Hb3. exact Hflp.
-
intros r Hr. apply KEEP. exact (sf_keep_callee r Hr).
-
intros i Hi. exact (ZSH i Hi).
-
intros a Ha X1 X2 X3. apply AVout; [exact Ha | exact X1 | exact X2 | exact X3].
-
intros a Ha. apply PWE. exact Ha.
Qed.
End d.
End e.
Section f. Context {rc : YM05.RunCeil}.
Theorem disco_stack_free6_shared : forall (fq : YK11.FPState) B,
AR_laws tfibsegs B -> GrantSyms B ->
astack_free_realizes (fx := fq) tfibsegs B SF6_ENTRY 6.
Proof.
intros fq B LAWS TB. rewrite SF6_ENTRY_eq.
exact (@tfib_stack_free_6S fq rc B LAWS TB).
Qed.
End f.
