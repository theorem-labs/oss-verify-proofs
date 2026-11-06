(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0p YK0i YK0j YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ0f YC02.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00 YI02 YI01.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YC01 YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YG00 YG0a YG01 YG0h YG0u YG0d YG0e YCcz YCd0 YCd1.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YI1i YI08 YI0c.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB1u YCe7 YF9i YCeb YCe8 YCfq YCdy YCfr YCe9 YCfx YChv YChx YChn YCf6 YCft YCey YCe4 YCi1 YCrr YCib YCrn YCrm YCrt YCrs YCru YCro YCrb.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section e.
Variable B : asyms.
Hypothesis TL : TrbLib B.
Hypothesis LAWS : AR_laws trbsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis AMEMSET : aintrin_realizes trbsegs B OSet A_asan_memset.
Hypothesis ASM0 : astack_malloc_sz_realizes trbsegs B A_stack_malloc_0 0.
Hypothesis SMP : stack_malloc_progressP B.
Let HBcode := tl_code B TL. Let errno_low := tl_env B TL. Let HBgot := tl_got_shadow B TL. Let HBcell := tl_shadow_cell B TL.
Let HBguar := tl_got_uar B TL. Let HBuar := tl_uar_cell B TL.
Theorem trrfc_A : rf_from B ss_R1 (INV_R B 35) -> trrfc_spec B.
Proof.
intros RB. unfold trrfc_spec.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs Bb st dst N pdata nb cur cid pos ch
HJ Hsub HPerm Hpd Hra Hra4 Hgp Htp G10 G11 G12 HCH HCTX Hcnt Hal16 Hwlo Hwhi Hown Hcid Hfal Hdst1 Hdst2 Hdst8 Hst1 Hst2 Hst8 RAst RAdst HN Hcur Hnb Wp Wn Wc Hev Hlive.
change RGBFC_SIZE with 24 in Hdst2, RAdst.
pose proof Hwx_tfa as Hwx. pose proof trb_segs_low as Hsegs.
pose proof HJ as (HAR & Hly & _ & _ & _ & Hfrs & Hnev & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). assert (HTS : TRRFC_STK = 176 + ASTACK) by reflexivity. assert (ASTACK = 16384) as Has by reflexivity.
assert (Hes : ESTACK = 4096) by reflexivity.
assert (Hpdc : In (pdata, nb) (ablocks B lyc Sc)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm | exact Hpd]).
destruct (al_blocks _ _ LAWS _ _ _ _ _ pdata nb HAR Hpdc) as (Hp16 & Hp4096 & Hpceil & [Hph Hpapp] & Hppres & _ & HnbM).
unfold zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hpapp.
pose proof (blk_off_img _ _ _ _ _ _ pdata nb HAR Hpdc) as Hph_img.
pose proof (req_size_pos nb ltac:(lia)) as [Hrq1 Hrq2]. unfold MALLOC_MAX in HnbM.
assert (Hfin : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_app_iff; left; exact Hown).
destruct (al_frames _ _ LAWS _ _ _ _ _ cid pos HAR Hfin) as (_ & [HFhi1 HFhi2] & HFpres & HFSpres). ceil; unfold ASAN_CEIL, kLowShadowBeg, kHighMemBeg in HFhi2. pose proof (fs_frame_bytes_nonneg cid) as HFB.
pose proof (frm_off_img _ _ _ _ _ _ _ _ HAR Hfin) as HFhi2_img.
assert (HlyF : ly_F lyc = ly_F ly) by (destruct Hly as (_ & _ & _ & _ & _ & -> & _); reflexivity).
assert (HSPB : alloc_ceiling <= spZ regs - TRRFC_STK /\ spZ regs <= 2 ^ 47) by (clear - Hwlo Hwhi Hceil Hslo Hshi H47 Hstk0; lia).
assert (Hsd : rboxed (st + 24 <= dst \/ dst + 24 <= st)) by (unfold rboxed; right; clear - Hst1 HSPB Hdst2 HFhi2 HTS Has C1; lia).
assert (HSEP : rfc_sep (spZ regs) Bb lyc Sc st dst) by (eapply (rfc_sep_intro B LAWS); [exact HAR | exact HPerm | exact Hfin | clear - Hst1 HSPB HTS Has C1; lia | exact Hdst1 | exact Hdst2]).
assert (HSTB : spZ regs <= st /\ st + 24 <= 2 ^ 47 /\ alloc_ceiling <= st) by (clear - Hst1 Hst2 Hwlo Hwhi Hceil Hslo Hshi H47 Hstk0 HTS Has C1; lia).
assert (HDSTB : (4096 <= dst /\ (dst + 24 <= 65536 \/ 6156288 <= dst) /\ (dst + 24 <= 2147446784 \/ 17594333495296 <= dst)) /\ dst + 24 <= alloc_ceiling) by (try generalize HFhi2_img; clear - Hdst1 Hdst2 HFhi1 HFhi2 C1 C3; unfold off_img; intros; lia).
remember (Ereg regs (rfc_extra pdata nb cur)) as E eqn:HE.
pose proof (rfc_entry B TL LAWS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs Bb st dst N pdata nb cur cid pos
HJ HPerm Hpd G10 G11 G12 Hal16 Hwlo Hwhi Hown Hcid Hdst1 Hdst2 Hdst8 Hst1 Hst2 Hst8 HN Hcur Hnb Wp Wn Wc) as HS. rewrite <- HE in HS.
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r) by (intros n r Hn; rewrite HE; apply ew_Ereg_nat; exact Hn).
assert (E2 : ew E 2 = getr regs 2) by (exact (EE 2%nat 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 st) by (rewrite (EE 10%nat 10%bv eq_refl); exact G10).
assert (E11 : ew E 11 = Z_to_bv 64 dst) by (rewrite (EE 11%nat 11%bv eq_refl); exact G11).
assert (E12 : ew E 12 = Z_to_bv 64 N) by (rewrite (EE 12%nat 12%bv eq_refl); exact G12).
assert (E3 : ew E 3 = Z_to_bv 64 (as_gp B)) by (rewrite (EE 3%nat 3%bv eq_refl); exact Hgp).
assert (E4 : ew E 4 = Z_to_bv 64 (as_tp B)) by (rewrite (EE 4%nat 4%bv eq_refl); exact Htp).
assert (EX : forall j, ew E (32 + j) = nth j (rfc_extra pdata nb cur) (Z_to_bv 64 0)) by (intros j; rewrite HE; apply ew_Ereg_extra).
pose proof (EX 0%nat) as E32. pose proof (EX 1%nat) as E33. pose proof (EX 2%nat) as E34. pose proof (EX 3%nat) as E35. pose proof (EX 4%nat) as E36.
cbn [Nat.add nth rfc_extra map app] in E32, E33, E34, E35, E36.
clear EX.
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite (EE 2%nat 2%bv eq_refl); reflexivity).
assert (B10 : bv_unsigned (ew E 10) = st) by (rewrite E10; apply unsigned_lit_small; lia).
assert (B11 : bv_unsigned (ew E 11) = dst) by (rewrite E11; apply unsigned_lit_small; lia).
assert (AG : forall n, (n < 33)%nat -> ew E n = ew E n) by (intros; reflexivity).
pose proof (conj E32 (conj E33 (conj E34 (conj E35 E36)))) as EXT0.
clear HE.
shok_auto SHOK RBx E (mrestrict (w_H W) memc).
unfold cfg_at. change (w64 A_rread_frameconfig) with (Z_to_bv 64 A_rread_frameconfig).
pose proof HJ as HJc.
change memc with (ms_mem (mkst regs (Z_to_bv 64 A_rread_frameconfig) memc (seg_rom trbsegs))) in HJ.
assert (EFA0 : forall c p, frame_addr lyc c p = frame_addr lyc c p) by reflexivity.
aj_run_to_tok trbtbl_lib_ok HS HJ SHOK RBspan 0x816a4.
{ awrRFC Usp E10 E11 Hown EFA0. }
unrun HFr (fun a => spZ regs - TRRFC_STK <= a < spZ regs \/ dst <= a < dst + 24 \/ st + 16 <= a < st + 24) Usp B10 B11 HTS Has UN0.
pose proof (rfc_kept_step _ _ _ _ _ _ _ _ _ _ _ _ (rfc_kept_refl W memc (spZ regs) Bb lyc Sc st dst) HSEP UN0 ltac:(intros a Ha; exact Ha) ltac:(clear - HSPB; lia)) as KEPT0.
lazymatch type of KEPT0 with rfc_kept _ _ _ ?mN _ _ _ _ _ _ =>
assert (SHK0 : forall a, 2147450880 <= a < kHighShadowEnd -> aview trbsegs (w_H W) mN a = aview trbsegs (w_H W) memc a)
by (intros a Ha; apply UN0; [clear - Ha C1 C2 C3 C4 C5; lia | cbn beta; clear - Ha HTS Has HSPB HSTB HDSTB C1 C2 C3; lia]) end.
pose proof (RA_kept_low _ _ st 24 SHK0 ltac:(clear - HSTB C1; lia) ltac:(clear - HSTB C4; lia) RAst) as RAst0.
pose proof (RA_kept_low _ _ dst 24 SHK0 ltac:(clear - HDSTB; lia) ltac:(clear - HDSTB C1 C4; lia) RAdst) as RAdst0.
lazymatch type of KEPT0 with rfc_kept _ _ _ ?mN _ _ _ _ _ _ =>
assert (UP0 : forall a, st + 24 <= a < 2 ^ 64 -> aview trbsegs (w_H W) mN a = aview trbsegs (w_H W) memc a)
by (intros a Ha; apply UN0; [clear - Ha HSTB C1; lia | cbn beta; clear - Ha HSTB HDSTB; lia]) end.
clear UN0 SHK0. clear_frames.
set (sp1 := 32 * ((spZ regs + -160) / 32)).
destruct (sp1_facts (spZ regs + -160) ltac:(clear - HSPB HTS Has C1; lia)
ltac:(rewrite <- Zplus_mod_idemp_l, Hal16; reflexivity)) as (Hsp1r & Hsp1al & Hsp1al16). fold sp1 in Hsp1r, Hsp1al, Hsp1al16.
assert (Hsp1 : spZ regs - 176 <= sp1 <= spZ regs - 160) by (clear - Hsp1r; lia). clear Hsp1r.
lazymatch type of HS with st_ok _ ?Ev _ _ =>
rreg_by HS (2%bv : bv 5) (Z_to_bv 64 sp1)
(denot_and_m32 Ev 2 (spZ regs) (-160) ltac:(rewrite E2; symmetry; apply Z_to_bv_bv_unsigned)
ltac:(clear - HSPB HTS Has C1; lia) ltac:(clear - HSPB; lia) ltac:(clear - HSPB HTS Has C1; lia)) R2 end.
lazymatch type of HS with st_ok _ ?Ev ?ssv ?msv =>
pose proof (st_ok_agree trbsegs 70 Ev (havoc Ev 70 [Z_to_bv 64 sp1]) ssv msv HS
(env_agree_havoc_ge 70 70 Ev Ev _ ltac:(lia) (env_agree_refl 70 Ev)) ltac:(vm_compute; reflexivity)) as HS3 end.
clear HS. rename HS3 into HS. rebaseE HS AG HEv.
lazymatch type of HS with st_ok _ ?Ev _ _ =>
assert (E70 : ew Ev 70 = Z_to_bv 64 sp1) by (rewrite HEv; exact (ew_havoc_new _ 70 [Z_to_bv 64 sp1] 0 (Z_to_bv 64 0) ltac:(cbn; lia))) end.
clear HEv.
lazymatch type of HS with st_ok _ ?Ev ?ssx ?msx =>
pose proof (ast_ok_set_reg_fp trbsegs Ev ssx msx (2%bv : bv 5) (SOff 70 0) HS ltac:(vm_compute; reflexivity)
ltac:(cbn [sv_denot ms_regs restrict mkst]; rewrite E70, Z.add_0_r, R2; rewrite unsigned_lit_small by (clear - Hsp1 HSPB HTS Has C1; lia); reflexivity)) as HS3;
clear HS; rename HS3 into HS end.
norm_ss HS. clear R2.
lazymatch type of HS with st_ok _ ?Ev ?ssx ?msx =>
pose proof (st_ok_add_fact trbsegs Ev ssx msx 70%nat (mkAF (2 ^ 46 - 512) (2 ^ 47) 5) HS
ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E70, unsigned_lit_small by (clear - Hsp1 HSPB HTS Has C1; lia); change (2 ^ 5) with 32;
clear - Hsp1 Hsp1al HSPB HTS Has C1 C3; lia)) as HS3;
clear HS; rename HS3 into HS end.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJpres & _).
lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
let rs := eval vm_compute in (ss_mem ssx) in
let rs' := eval vm_compute in (trim_stack rs (-104) 0) in
pose proof (st_ok_submem trbsegs Ex ssx (restrict (w_H W) msX) rs' HS ltac:(cbn [ss_mem]; submem_to) ltac:(vm_compute; reflexivity)) as HS3;
clear HS; rename HS3 into HS end.
norm_ss HS.
lazymatch type of HS with st_ok _ ?Ev _ _ =>
pose proof (ast_ok_add_region trbsegs Ev _ _ (YQ0b.mkRegion (Some 70%nat) 0 56 0 56 []) HS eq_refl
ltac:(unfold region_ok; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val ms_mem restrict mkst];
rewrite E70, unsigned_lit_small by (clear - Hsp1 HSPB HTS Has C1; lia); split; [clear - Hsp1 HSPB HTS Has C1; lia|]; split; [clear - Hsp1 HSPB; lia|]; split; [|apply Forall_nil];
intros o Ho; apply (apresent_writable trbsegs); apply HJpres; clear - Ho Hsp1 Hwlo Hwhi HTS Has; lia)
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val];
evalE AG; unfold A_GOT_shadow, A_shadow_glob, A_GOT_uar, A_uar_glob; unfold rboxed in Hsd;
clear - Hsp1 HSPB HSTB HDSTB Hsd HTS Has C1; repeat split; zone_lia)) as HS3; clear HJpres;
clear HS; rename HS3 into HS end.
norm_ss HS.
reshok HS. unfold RBx in *.
aj_run_to_tok trbtbl_lib_ok HS HJ SHOK RBspan A_stack_malloc_0.
{ awrRFB AG 0 0 EFA0 ltac:(exact Hown). }
unrunB HFr (fun a => spZ regs - TRRFC_STK <= a < spZ regs \/ dst <= a < dst + 24 \/ st + 16 <= a < st + 24) AG 0 UN1.
pose proof (rfc_kept_step _ _ _ _ _ _ _ _ _ _ _ _ KEPT0 HSEP UN1 ltac:(intros a Ha; exact Ha) ltac:(clear - HSPB; lia)) as KEPT1.
lazymatch type of KEPT1 with rfc_kept _ _ _ ?mN _ _ _ _ _ _ =>
assert (UP1 : forall a, st + 24 <= a < 2 ^ 64 -> aview trbsegs (w_H W) mN a = aview trbsegs (w_H W) memc a)
by (intros a Ha; rewrite <- (UP0 a Ha); apply UN1; [clear - Ha HSTB C1; lia | cbn beta; clear - Ha HSTB HDSTB; lia]) end.
clear UN1 KEPT0 UP0 RAst0 RAdst0. clear_frames.
aconstsF HJ Kgot0 Kcell0 Kguar0 Kuar0.
rreg HS (2%bv : bv 5) R2. rreg HS (3%bv : bv 5) R3. rreg HS (4%bv : bv 5) R4. rreg HS (1%bv : bv 5) R1. rreg HS (10%bv : bv 5) R10.
rewrite (st_ok_restrict_mkst trbsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
change (Z_to_bv 64 249852) with (Z_to_bv 64 A_stack_malloc_0).
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
eapply (aj_stack_malloc_sz_atD trbsegs B LAWS Hsegs errno_low ML SMP A_stack_malloc_0 0 ASM0 ltac:(lia) W (ms_regs msX) (ms_mem msX) STK sp0 FP ly S W0 mem0 md0 own lyc Sc _ k (sp1 - sp0) _ 64 HJ) end.
- unfold spZ at 1. rewrite R2. evalE AG.
- rewrite <- Zminus_mod_idemp_l, Hsp1al16, <- Zminus_mod_idemp_r, Hsp0al. reflexivity.
- clear - Hsp1 Hwhi; lia. - rewrite Hes; clear - Hsp1 Hwlo HTS Has; lia.
- rewrite R3. evalE AG. - rewrite R4. evalE AG.
- exact R1. - vm_compute. reflexivity.
- rewrite R10. reflexivity.
- change (fs_frame_bytes 0) with 64. clear; lia. - reflexivity.
- exact Hcnt. }
cbv beta. clear R2 R3 R4 R1 R10 SHOK.
intros W2 c2 _ (-> & S2 & regs2 & mem2 & md2 & fpos & -> & HJ2 & HP2 & Ha0 & Eab & Hfrs2 & Hnin & Hnev2 & HBD0 & Hbb2 & Hz & Hflag & HK).
rewrite Hes in HK. replace (sp0 + (sp1 - sp0) - 4096) with (sp1 - 4096) in HK by (clear; lia).
replace (sp0 + (sp1 - sp0)) with sp1 in HK by (clear; lia).
pose proof (proj1 HJ2) as HAR2.
assert (HBb0 : forall b m, In (b, m) Bb -> In (b, m) (ablocks B lyc Sc))
by (intros b m Hb; eapply Permutation_in; [apply Permutation_sym; exact HPerm | exact Hb]).
lazymatch type of HK with acall_kept _ _ _ _ _ ?mT _ _ _ _ _ =>
assert (KEPT2 : rfc_kept W memc W mem2 (spZ regs) Bb lyc Sc st dst)
by (eapply (rfc_kept_call B W memc W mT W mem2 (spZ regs) Bb lyc Sc lyc Sc st dst _ _ _ KEPT1 HK ltac:(clear - Hsp1 HTS Has; lia) ltac:(clear - Hsp1; lia) HBb0
ltac:(intros b m i _ _ F; exact F) eq_refl ltac:(intros c p; reflexivity) ltac:(intros c p a _ _ F; exact F))) end.
assert (UP2 : forall a, st + 24 <= a < 2 ^ 64 -> aview trbsegs (w_H W) mem2 a = aview trbsegs (w_H W) memc a).
{ intros a Ha. rewrite <- (UP1 a Ha). pose proof HK as (K1 & _). apply K1; clear - Ha Hsp1 HSTB C1; lia. }
clear UP1 KEPT1.
aconstsF HJ2 Kgot2 Kcell2 Kguar2 Kuar2.
assert (Hfin2 : In (cid, pos) (frames S2)) by (rewrite Hfrs2; right; exact Hfin).
assert (Hfin0 : In (0, fpos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
destruct (al_frames _ _ LAWS _ _ _ _ _ cid pos HAR2 Hfin2) as (_ & _ & HFpres2 & _).
destruct (al_frames _ _ LAWS _ _ _ _ _ 0 fpos HAR2 Hfin0) as (HF0al & [HF0hi _] & HF0pres & HF0Spres).
destruct (frames_bounds trbsegs B LAWS _ _ _ _ _ 0 fpos HAR2 Hfin0) as (HF4096 & HFceil & HFhigh).
pose proof (frm_off_img _ _ _ _ _ _ _ _ HAR2 Hfin0) as HFhigh_img.
change (fs_frame_bytes 0) with 64 in *. change (64 / 8) with 8 in HF0Spres.
set (F := frame_addr lyc 0 fpos) in *. set (FL := flag_addr lyc 0 fpos) in *.
pose proof (rf_fsep_intro B LAWS lyc S2 W mem2 md2 lyc Sc Bb fpos HAR2 Hfrs2 ltac:(intros c p; reflexivity)
ltac:(intros [b m] Hb; rewrite Eab; exact (HBb0 b m Hb))) as HFSEP.
assert (DFF : rboxed (F + 64 <= frame_addr lyc cid pos \/ frame_addr lyc cid pos + fs_frame_bytes cid <= F)).
{ destruct (in_split _ _ Hfin) as (l2 & l3 & El).
pose proof (sep_frames_pos trbsegs B LAWS _ _ _ _ _ (0, fpos) (cid, pos) [] l2 l3 HAR2 ltac:(rewrite Hfrs2, El; reflexivity)) as D.
unfold zdisjoint, frame_rng in D. cbn [fst snd] in D. fold F in D. change (fs_frame_bytes 0) with 64 in D. exact D. }
reseat HS HJ2 HP2 [0; 1; 2; 3; 4; 5; 6; 7; 8]%nat AG
ltac:(idtac; first [ keptRFB HK HJ2 AG Kgot0 Kgot2 Kcell0 Kcell2 Kguar0 Kguar2 Kuar0 Kuar2 Hfin Hfin HFpres2 HFpres2 HFpres2 ltac:(exact (fun Hn : False => Hn))
| match goal with |- ?g => idtac "KEPTFAIL" g end]).
rreg HS (10%bv : bv 5) RF. cbn [ms_regs] in RF. rewrite Ha0 in RF. symmetry in RF. unfold w64 in RF. fold F in RF.
lazymatch type of HS with st_ok _ ?Ev ?ssv ?msv =>
pose proof (st_ok_agree trbsegs 87 Ev (havoc Ev 87 [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)]) ssv msv HS
(env_agree_havoc_ge 87 87 Ev Ev _ ltac:(lia) (env_agree_refl 87 Ev)) ltac:(vm_compute; reflexivity)) as HS3 end.
clear HS. rename HS3 into HS. rebaseE HS AG HEv.
lazymatch type of HS with st_ok _ ?Ev _ _ =>
assert (E87 : ew Ev 87 = Z_to_bv 64 FL) by (rewrite HEv; exact (ew_havoc_new _ 87 [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)] 0 (Z_to_bv 64 0) ltac:(cbn; lia)));
assert (E88 : ew Ev 88 = Z_to_bv 64 (SB + F / 8)) by (rewrite HEv; exact (ew_havoc_new _ 87 [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)] 1 (Z_to_bv 64 0) ltac:(cbn; lia))) end.
clear HEv.
lazymatch type of HS with st_ok _ ?Ev _ _ => assert (E32' : ew Ev 32 = Z_to_bv 64 SB) by (rewrite (AG 32%nat) by lia; exact E32) end.
assert (HFq : F = 32 * (F / 32)) by (pose proof (Z.div_mod F 32 ltac:(lia)); lia).
assert (HF8 : F / 8 = 4 * (F / 32)) by (rewrite HFq at 1; replace (32 * (F / 32)) with (4 * (F / 32) * 8) by lia; rewrite Z.div_mul by lia; reflexivity).
assert (HF8lo : 512 <= F / 8) by (apply Z.div_le_lower_bound; lia).
assert (HF8hi : F / 8 <= 17592184995832) by (apply Z.div_le_upper_bound; [lia | clear - HFceil C1; lia]).
destruct (al_flag _ _ LAWS lyc S2 W mem2 md2 0 fpos HAR2 Hfin0) as (HFLpres & HFLown & HFLapp & HFLceil). fold FL in HFLpres, HFLown, HFLapp, HFLceil.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFLapp.
pose proof HFhigh as HFapp. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFhigh. unfold off_img in HFhigh_img. pose proof (proj1 HFLapp) as HFL4096. rbox HFLapp. rbox HFhigh. rbox HFhigh_img.
lazymatch type of HS with st_ok _ ?Ev _ _ =>
pose proof (st_ok_add_fact trbsegs Ev _ _ 75 (HPTR 5) HS
ltac:(unfold afact_ok, HPTR; cbn [af_lo af_hi af_al2]; rewrite RF, unsigned_lit_small by lia; change (2 ^ 5) with 32; lia)) as HS3;
clear HS; rename HS3 into HS;
pose proof (st_ok_add_fact trbsegs Ev _ _ 87 (HPTR 0) HS
ltac:(unfold afact_ok, HPTR; cbn [af_lo af_hi af_al2]; rewrite E87, unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r; lia)) as HS3;
clear HS; rename HS3 into HS;
pose proof (st_ok_add_fact trbsegs Ev _ _ 88 (mkAF (SB + 512) (SB + 17592184995832) 2) HS
ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E88, unsigned_lit_small by (unfold SB; lia); change (2 ^ 2) with 4; unfold SB;
split; [lia|]; split; [rewrite HF8; replace (2147450880 + 4 * (F / 32)) with ((536862720 + F / 32) * 4) by lia; apply Z_mod_mult | lia])) as HS3;
clear HS; rename HS3 into HS;
pose proof (st_ok_add_alias trbsegs Ev _ _ _ _ HS (shadow_decl_ok Ev 75 32 88 F SB RF ltac:(lia) E32' E88)) as HS3;
clear HS; rename HS3 into HS;
idtac end.
lazymatch type of HS with st_ok _ ?Ev _ _ =>
pose proof (ast_ok_add_region trbsegs Ev _ _ (YQ0b.mkRegion (Some 75%nat) 56 64 0 0 [YQ0b.mkChunk 56 (CVal 8 (SOff 87 0))]) HS eq_refl
ltac:(unfold region_ok; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val ms_mem restrict mkst app];
rewrite RF, unsigned_lit_small by lia; split; [lia|]; split; [lia|]; split;
[ intros o Ho; exfalso; clear - Ho; lia
| apply Forall_cons; [|apply Forall_nil]; apply (chunk_ok_val trbsegs Ev _ F 56 8 _ FL);
[cbn [sv_denot]; rewrite E87, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | replace (F + 56) with (F + 64 - 8) by lia; exact (val_mem_of_rdword trbsegs _ _ _ _ Hflag)] ])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val];
rewrite RF; evalE AG; unfold A_GOT_shadow, A_shadow_glob, A_GOT_uar, A_uar_glob; unfold rboxed in Hsd, DFF, HFhigh, HFhigh_img;
clear - Hsp1 HSPB HSTB HDSTB Hsd DFF Hdst1 Hdst2 HF4096 HFceil HFhigh HFhigh_img HTS Has C1 C3; repeat split; zone_lia)) as HS3;
clear HS; rename HS3 into HS end.
norm_ss HS.
lazymatch type of HS with st_ok _ ?Ev _ _ =>
pose proof (ast_ok_add_region trbsegs Ev _ _ (YQ0b.mkRegion (Some 75%nat) 32 40 32 40 []) HS eq_refl
ltac:(unfold region_ok; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val ms_mem restrict mkst app];
rewrite RF, unsigned_lit_small by lia; split; [lia|]; split; [lia|]; split; [|apply Forall_nil];
intros o Ho; apply (apresent_writable trbsegs); apply (proj1 (HF0pres (F + o) ltac:(lia))))
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val];
rewrite RF; evalE AG; unfold A_GOT_shadow, A_shadow_glob, A_GOT_uar, A_uar_glob; unfold rboxed in Hsd, DFF, HFhigh, HFhigh_img;
clear - Hsp1 HSPB HSTB HDSTB Hsd DFF Hdst1 Hdst2 HF4096 HFceil HFhigh HFhigh_img HTS Has C1 C3; repeat split; zone_lia)) as HS3;
clear HS; rename HS3 into HS end.
norm_ss HS.
lazymatch type of HS with st_ok _ ?Ev _ _ =>
pose proof (ast_ok_add_region trbsegs Ev _ _ (YQ0b.mkRegion (Some 75%nat) 0 32 0 32 []) HS eq_refl
ltac:(unfold region_ok; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val ms_mem restrict mkst app];
rewrite RF, unsigned_lit_small by lia; split; [lia|]; split; [lia|]; split; [|apply Forall_nil];
intros o Ho; apply (apresent_writable trbsegs); apply (proj1 (HF0pres (F + o) ltac:(lia))))
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val];
rewrite RF; evalE AG; unfold A_GOT_shadow, A_shadow_glob, A_GOT_uar, A_uar_glob; unfold rboxed in Hsd, DFF, HFhigh, HFhigh_img;
clear - Hsp1 HSPB HSTB HDSTB Hsd DFF Hdst1 Hdst2 HF4096 HFceil HFhigh HFhigh_img HTS Has C1 C3; repeat split; zone_lia)) as HS3;
clear HS; rename HS3 into HS end.    assert (ZS : forall j, 0 <= j < 8 -> val_mem trbsegs (mrestrict (w_H W) mem2) (SB + F / 8 + j) 1 0).
{ intros j Hj. apply val_mem1_of_aview. unfold zero_shadow, shadow_of_addr in Hz. rewrite <- SB_SHADOW_OFF in Hz. apply Hz. change (64 / 8) with 8. exact Hj. }
lazymatch type of HS with st_ok _ ?Ev _ _ =>
pose proof (ast_ok_add_region trbsegs Ev _ _
(fshadow_region 88 0 0 8 (map (fun off => YQ0b.mkChunk off (CVal 1 (SLit 0))) [0; 1; 2; 3; 4; 5; 6; 7])) HS eq_refl
ltac:(unfold region_ok, fshadow_region; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val ms_mem restrict mkst app map];
change (fs_frame_bytes 0 / 8) with 8; rewrite E88, unsigned_lit_small by (unfold SB; lia); split; [unfold SB; lia|]; split; [unfold SB; lia|]; split;
[ intros o Ho; apply (apresent_writable trbsegs); unfold shadow_addr in HF0Spres; rewrite <- SB_SHADOW_OFF in HF0Spres;
apply (proj1 (HF0Spres o ltac:(lia)))
| repeat (apply Forall_cons; [apply (chunk_ok_val trbsegs Ev _ (SB + F / 8) _ 1 (SLit 0) 0); [reflexivity | zside | zside | apply ZS; lia] |]);
apply Forall_nil ])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint, fshadow_region; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val];
change (fs_frame_bytes 0 / 8) with 8; rewrite E88, RF; evalE AG;
unfold A_GOT_shadow, A_shadow_glob, A_GOT_uar, A_uar_glob, SB; unfold rboxed in HFhigh, HFhigh_img;
clear - Hsp1 HSPB HSTB HDSTB HF4096 HFceil HFhigh HFhigh_img HF8lo HF8hi HFq HF8 HTS Has C1 C3; repeat split; zone_lia)) as HS3;
clear HS; rename HS3 into HS end.
norm_ss HS.
aj_run_to_sh trbtbl_lib_ok HS HJ2 A_asan_memset.
{ awrRFB AG fpos F EFA0 ltac:(right; exact Hown). }
destruct HFSEP as [HFSB HFSF].
unrunB HFr (fun a => spZ regs - TRRFC_STK <= a < spZ regs \/ dst <= a < dst + 24 \/ st + 16 <= a < st + 24 \/
(in_zr a (frame_rng lyc (0, fpos)) \/ in_zr a (shadow_addr (frame_addr lyc 0 fpos), fs_frame_bytes 0 / 8))) AG F UN3.
pose proof (rfc_kept_stepE _ _ _ _ _ _ _ _ _ _ _ _ (fun a => in_zr a (frame_rng lyc (0, fpos)) \/ in_zr a (shadow_addr (frame_addr lyc 0 fpos), fs_frame_bytes 0 / 8))
KEPT2 HSEP UN3 ltac:(intros a Ha; exact Ha) ltac:(clear - HSPB; lia)
ltac:(intros a Ha; revert Ha; unfold in_zr, frame_rng, shadow_addr; cbn [fst snd]; rewrite <- SB_SHADOW_OFF; change (fs_frame_bytes 0 / 8) with 8; change (fs_frame_bytes 0) with 64; fold F; unfold SB;
clear - HFceil HF8hi C1; lia)
HFSB HFSF) as KEPT3.
lazymatch type of KEPT3 with rfc_kept _ _ _ ?mN _ _ _ _ _ _ =>
assert (UP3 : forall a, st + 24 <= a < 2 ^ 64 -> aview trbsegs (w_H W) mN a = aview trbsegs (w_H W) memc a)
by (intros a Ha; rewrite <- (UP2 a Ha); apply UN3; [clear - Ha HSTB C1; lia |];
cbn beta; unfold in_zr, frame_rng, shadow_addr; cbn [fst snd]; rewrite <- SB_SHADOW_OFF; change (fs_frame_bytes 0 / 8) with 8; change (fs_frame_bytes 0) with 64; fold F; unfold SB;
clear - Ha HSTB HDSTB HFceil HF8hi C1; lia) end.
clear UN3 KEPT2 UP2. clear_frames.
clear Kgot2 Kcell2 Kguar2 Kuar2. aconstsF HJ2 Kgot2 Kcell2 Kguar2 Kuar2.
pose proof (RA_dst_kept _ _ _ _ _ _ _ _ _ _ cid pos KEPT3 Hfin Hcid Hfal Hdst1 Hdst2 (proj1 (proj2 (al_frames _ _ LAWS _ _ _ _ _ cid pos HAR Hfin)))
ltac:(clear - HFhi2 C1; lia) ltac:(clear - HSTB; lia) RAdst) as RAdst3.
rreg HS (10%bv : bv 5) Ra0. rreg HS (11%bv : bv 5) Ra1. rreg HS (12%bv : bv 5) Ra2. rreg HS (1%bv : bv 5) Rra.
rreg HS (2%bv : bv 5) Rsp. rreg HS (3%bv : bv 5) Rgp. rreg HS (4%bv : bv 5) Rtp.
rewrite (st_ok_restrict_mkst trbsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
change (Z_to_bv 64 337168) with (Z_to_bv 64 A_asan_memset).
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
eapply (aj_intrin_at trbsegs B LAWS Hsegs OSet A_asan_memset AMEMSET _ (ms_regs msX) (ms_mem msX) STK sp0 FP ly S W0 mem0 md0 ((0, fpos) :: own)
lyc S2 _ k dst 0 24 (sp1 - sp0) (Z_to_bv 64 RRFC_MS) HJ2);
[ rewrite Ra0; evalE AG
| rewrite Ra1; reflexivity
| rewrite Ra2; reflexivity
| lia | clear - HDSTB; lia | clear - HDSTB C1; lia
| unfold spZ; rewrite Rsp; evalE AG
| rewrite <- Zminus_mod_idemp_l, Hsp1al16, <- Zminus_mod_idemp_r, Hsp0al; reflexivity
| clear - Hsp1 Hwhi; lia
| rewrite Hes; clear - Hsp1 Hwlo HTS Has; lia
| rewrite Rgp; evalE AG
| rewrite Rtp; evalE AG
| exact Rra
| vm_compute; reflexivity
| intros a Ha; split; [right; right; right; exists cid, pos; split; [right; exact Hown | left; unfold in_zr; cbn [fst snd]; clear - Ha Hdst1 Hdst2; lia] | rewrite Hes; clear - Ha HDSTB Hsp1 HSPB HTS Has C1; lia]
| apply amem_range_high; [clear; lia | clear - HDSTB; lia | clear - HDSTB C1; lia]
| exact RAdst3
| intros _; eapply (shadow_hull_vis_of_frame trbsegs B LAWS lyc S2 W _ _ cid pos dst 24 (proj1 HJ2) Hfin2); clear - Hdst1 Hdst2; lia
| exact I ] end. }
cbv beta. intros W1 c1 _ (-> & regs1 & mem1 & md1 & -> & HJ1 & HP1 & Ha01 & Heff1 & Hfr1 & Hpres1).
rewrite Hes in Hfr1. replace (sp0 + (sp1 - sp0)) with sp1 in Hfr1 by (clear; lia).
aconstsF HJ1 Kgot1 Kcell1 Kguar1 Kuar1.
clear Ra0 Ra1 Ra2 Rra Rsp Rgp Rtp.
lazymatch type of KEPT3 with rfc_kept _ _ _ ?mN _ _ _ _ _ _ =>
pose proof (rfc_kept_stepE _ _ _ mN mem1 _ _ _ _ _ _ (fun a => (dst <= a < dst + 24) \/ (sp1 - 4096 <= a < sp1)) (fun _ => False) KEPT3 HSEP
ltac:(intros a Ha Hn; apply Hfr1; [exact Ha | clear - Hn; tauto | clear - Hn; tauto])
ltac:(intros a Ha; cbn beta in *; clear - Ha Hsp1 HTS Has; lia) ltac:(clear - HSPB; lia)
ltac:(intros a F0; destruct F0) ltac:(intros b m i _ _ F0; exact F0) ltac:(intros c p a _ _ F0; exact F0)) as KEPT4 end.
assert (UP4 : forall a, st + 24 <= a < 2 ^ 64 -> aview trbsegs (w_H W) mem1 a = aview trbsegs (w_H W) memc a).
{ intros a Ha. rewrite <- (UP3 a Ha). apply Hfr1; [clear - Ha HSTB C1; lia | clear - Ha HSTB HDSTB; lia | clear - Ha HSTB Hsp1; lia]. }
pose proof (proj1 HJ1) as HAR1.
pose proof (RA_dst_kept _ _ _ _ _ _ _ _ _ _ cid pos KEPT4 Hfin Hcid Hfal Hdst1 Hdst2 (proj1 (proj2 (al_frames _ _ LAWS _ _ _ _ _ cid pos HAR Hfin)))
ltac:(clear - HFhi2 C1; lia) ltac:(clear - HSTB; lia) RAdst) as RAdst4.
assert (RAst4 : range_addressable (aview trbsegs (w_H W) mem1) SHADOW_OFF st 24).
{ pose proof (proj1 (proj2 HJ1)) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Elo1 & Ehi1 & _).
apply (RA_stack B LAWS lyc S2 W mem1 _ st 24 HAR1); [rewrite Elo1; clear - Hst1 Hwlo Hslo Hstk0 HTS Has; lia | rewrite Ehi1; clear - Hst2 Hshi; lia | exact Hst8 | reflexivity | clear; lia]. }
reseat HS HJ1 HP1 [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11]%nat AG
ltac:(first [ eapply region_kept_aview; [evalE AG | intros a Ha; apply Hfr1;
[ clear - Ha Hsp1 HSPB HSTB HDSTB HF4096 HFceil HF8lo HF8hi HTS Has C1 C3; unfold SB in *; lia
| unfold rboxed in DFF, Hsd; clear - Ha Hsp1 HSPB HSTB HDSTB DFF Hsd Hdst1 Hdst2 HF4096 HFceil HF8lo HF8hi HTS Has C1 C3; unfold SB in *; lia
| clear - Ha Hsp1 HSPB HSTB HDSTB HF4096 HFceil HF8lo HF8hi HTS Has C1 C3; unfold SB in *; lia ] | exact Hpres1]
| apply (region_kept_val trbsegs _ _ _ A_GOT_shadow 8 A_shadow_glob); [exact Kgot2 | exact Kgot1 | lia]
| apply (region_kept_val trbsegs _ _ _ A_shadow_glob 8 SHADOW_OFF); [exact Kcell2 | exact Kcell1 | lia]
| apply (region_kept_val trbsegs _ _ _ A_GOT_uar 8 A_uar_glob); [exact Kguar2 | exact Kguar1 | lia]
| apply (region_kept_val trbsegs _ _ _ A_uar_glob 4 1); [exact Kuar2 | exact Kuar1 | lia]
| match goal with |- ?g => idtac "KEPTFAIL" g end ]).
destruct (al_frames _ _ LAWS _ _ _ _ _ cid pos HAR1 Hfin2) as (_ & _ & HFpres1 & _).
assert (Hz8 : val_mem trbsegs (mrestrict (w_H W) mem1) (dst + 0) 8 0).
{ apply val_mem_zero8. intros i Hi. replace (dst + 0 + i) with (dst + (0 + i)) by lia. rewrite (Heff1 (0 + i)) by lia. reflexivity. }
assert (Hz4 : val_mem trbsegs (mrestrict (w_H W) mem1) (dst + 8) 4 0).
{ intros j Hj. destruct (aview_byte trbsegs (w_H W) mem1 (dst + 8 + Z.of_nat j) 0 ltac:(replace (dst + 8 + Z.of_nat j) with (dst + (8 + Z.of_nat j)) by lia; rewrite (Heff1 (8 + Z.of_nat j)) by lia; reflexivity)) as (bb & Hbb & Hv & _).
rewrite Hbb. f_equal. apply bv_eq. rewrite Z_to_bv_unsigned. unfold YP0g.le_byte, bv_wrap.
repeat (rewrite Z.shiftr_0_l || rewrite Z.mod_0_l by (vm_compute; discriminate)). lia. }
lazymatch type of HS with st_ok _ ?Ex _ _ =>
assert (B11' : bv_unsigned (ew Ex 11) = dst) by (evalE AG) end.
lazymatch type of HS with st_ok _ ?Ex _ _ =>
pose proof (ast_ok_add_region trbsegs Ex _ _
(YQ0b.mkRegion (Some 11%nat) 0 12 0 12 [YQ0b.mkChunk 0 (CVal 8 (SLit 0)); YQ0b.mkChunk 8 (CVal 4 (SLit 0))])
HS eq_refl
ltac:(unfold region_ok; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val ms_mem restrict mkst map];
rewrite B11'; split; [clear - HDSTB; lia|]; split; [clear - HDSTB C1; lia|];
split; [intros o Ho; apply (apresent_writable trbsegs); apply (proj1 (HFpres1 (dst + o) ltac:(clear - Ho Hdst1 Hdst2; lia)))|];
apply Forall_cons; [apply (chunk_ok_val trbsegs Ex _ dst _ 8 (SLit 0) 0); [reflexivity | zside | zside | exact Hz8] |];
apply Forall_cons; [apply (chunk_ok_val trbsegs Ex _ dst _ 4 (SLit 0) 0); [reflexivity | zside | zside | exact Hz4] |];
apply Forall_nil)
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val];
rewrite B11'; evalE AG; unfold A_GOT_shadow, A_shadow_glob, A_GOT_uar, A_uar_glob, SB; unfold rboxed in Hsd, DFF;
clear - Hsd DFF Hsp1 HSPB HSTB HDSTB Hdst1 Hdst2 HF4096 HFceil HF8lo HF8hi C1 C3 HTS Has; repeat split; zone_lia)) as HS3;
clear HS; rename HS3 into HS end.
norm_ss HS.
fs_roF HS.
lazymatch type of HS with st_ok _ ?Ev _ _ => assert (E32f : ew Ev 32 = Z_to_bv 64 SB) by (rewrite (AG 32%nat) by lia; exact (proj1 EXT0)) end.
lazymatch goal with |- SRr _ ?Wg (mkCfg ?msF ?mdF) _ =>
lazymatch type of HS with st_ok _ ?Ev _ _ =>
eapply (RB (mkRFCX STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs Bb st dst N pdata nb cur cid pos ch fpos sp1 E) Ev k _ _ Wg msF mdF) end end.
- unfold rf_base. cbn [x_STK x_sp0 x_FP x_ly x_S x_W0 x_mem0 x_md0 x_own x_lyc x_Sc x_W x_memc x_mdc x_k x_regs x_Bb x_st x_dst x_N x_pdata x_nb x_cur x_cid x_pos x_ch x_fpos x_sp1 x_E0].
change RGBFC_SIZE with 24. destruct EXT0 as (X32 & X33 & X34 & X35 & X36).
repeat match goal with |- _ /\ _ => split end; try assumption; try reflexivity; try exact HJc; try (clear - HN Hcur; lia).
- unfold rf_E, rf_F, rf_FL. cbn [x_E0 x_pdata x_nb x_cur x_sp1 x_fpos x_lyc]. fold F FL. split; [exact AG|]. repeat (split; [eassumption|]). eassumption.
- cbn [x_STK x_sp0 x_FP x_ly x_S x_W0 x_mem0 x_md0 x_own x_fpos]. exact HJ1.
- cbn [x_Sc x_k]. rewrite Z.sub_diag. apply (jbud_of_bud Sc S2 0 0 0 0 0 (Z.le_refl 0) HBD0); [clear; lia | clear; lia | clear; lia | unfold HULL_UNIT; clear; lia].
- cbn [x_Sc x_fpos]. exact Hfrs2.
- cbn [x_Sc x_fpos]. exact Hnin.
- unfold rf_fsep, rf_Er, rf_F. cbn [x_Bb x_Sc x_lyc x_fpos]. split; [exact HFSB | exact HFSF].
- cbn [x_W x_memc x_regs x_Bb x_lyc x_Sc x_st x_dst]. exact KEPT4.
- cbn [x_st]. exact RAst4.
- cbn [x_dst]. exact RAdst4.
- split; [reflexivity|]. split; [cbn [x_lyc x_Sc]; exact Eab|]. exists cur. cbn [x_cur x_nb]. split; [exact E35 | clear - Hcur; lia].
- exact HS.
Qed.
End e.
End d.
