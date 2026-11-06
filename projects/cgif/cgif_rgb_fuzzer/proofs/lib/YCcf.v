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
YG00 YG0a YG01 YG0h YG0u YG0d YC04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YI1i YI08 YI0c.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB0z YC19 YF8z YC1d YC1a YC2o YC10 YC2p YC1b YC2u YC4o YC4q YC4h YC27 YC2r YC20 YC16 YC4u YCct YC4z YCcq YCcp YCcv YCcu YCcw.
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
Hypothesis TL : TraLib B.
Hypothesis LAWS : AR_laws trasegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis AMEMSET : aintrin_realizes trasegs B OSet A_asan_memset.
Let HBcode := tl_code B TL. Let errno_low := tl_env B TL. Let HBgot := tl_got_shadow B TL. Let HBcell := tl_shadow_cell B TL.
Theorem trrfc_A : rf_from B ss_R1 (INV_R0 B) -> trrfc_spec B.
Proof.
intros RB. unfold trrfc_spec.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs Bb st dst N pdata nb cur cid pos
HJ Hsub HPerm Hpd Hra Hra4 Hgp Htp G10 G11 G12 Hal16 Hwlo Hwhi Hown Hcid Hfal Hdst1 Hdst2 Hdst8 Hst1 Hst2 Hst8 RAst RAdst HN Hcur Hnb Wp Wn Wc HXU Hev Hlive.
change RGBFC_SIZE with 24 in Hdst2, RAdst.
pose proof Hwx_tfa as Hwx. pose proof tra_segs_low as Hsegs.
pose proof HJ as (HAR & Hly & _ & _ & _ & Hfrs & Hnev & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). assert (HTS : TRRFC_STK = 128 + ASTACK) by reflexivity. assert (ASTACK = 16384) as Has by reflexivity.
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
assert (HDSTB : (4096 <= dst /\ (dst + 24 <= 65536 \/ 6287360 <= dst) /\ (dst + 24 <= 2147446784 \/ 17594333495296 <= dst)) /\ dst + 24 <= alloc_ceiling) by (try generalize HFhi2_img; clear - Hdst1 Hdst2 HFhi1 HFhi2 C1 C3; unfold off_img; intros; lia).
remember (Ereg regs (rfc_extra pdata nb cur)) as E eqn:HE.
pose proof (rfc_entry B TL LAWS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs Bb st dst N pdata nb cur cid pos
HJ HPerm Hpd G10 G11 G12 Hal16 Hwlo Hwhi Hown Hcid Hdst1 Hdst2 Hdst8 Hst1 Hst2 Hst8 HN Hcur Hnb Wp Wn Wc) as HS. rewrite <- HE in HS.
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r) by (intros n r Hn; rewrite HE; apply ew_Ereg_nat; exact Hn).
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
assert (B36 : bv_unsigned (ew E 36) = pdata + cur) by (rewrite E36; apply unsigned_lit_small; lia).
assert (AG : forall n, (n < 33)%nat -> ew E n = ew E n) by (intros; reflexivity).
clear HE.
shok_auto SHOK RBx E (mrestrict (w_H W) memc).
unfold cfg_at. change (w64 A_rread_frameconfig) with (Z_to_bv 64 A_rread_frameconfig).
pose proof HJ as HJc.
change memc with (ms_mem (mkst regs (Z_to_bv 64 A_rread_frameconfig) memc (seg_rom trasegs))) in HJ.
aj_run_tok tratbl_lib_ok HS HJ SHOK RBspan.
assert (EFA0 : forall c p, frame_addr lyc c p = frame_addr lyc c p) by reflexivity.
{ awrRFC Usp E10 E11 Hown EFA0. }
rreg HS (10%bv : bv 5) Ra0. rreg HS (11%bv : bv 5) Ra1. rreg HS (12%bv : bv 5) Ra2. rreg HS (1%bv : bv 5) Rra.
rreg HS (2%bv : bv 5) Rsp. rreg HS (3%bv : bv 5) Rgp. rreg HS (4%bv : bv 5) Rtp.
rewrite (st_ok_restrict_mkst trasegs _ _ _ _ HS eq_refl). cbn [ss_pc].
change (Z_to_bv 64 336460) with (Z_to_bv 64 A_asan_memset).
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
eapply (aj_intrin_at trasegs B LAWS Hsegs OSet A_asan_memset AMEMSET _ (ms_regs msX) (ms_mem msX) STK sp0 FP ly S W0 mem0 md0 own
lyc Sc _ k dst 0 24 (spZ regs - 128 - sp0) (Z_to_bv 64 RRFC_MS) HJ);
[ rewrite Ra0, E11; reflexivity
| rewrite Ra1; reflexivity
| rewrite Ra2; reflexivity
| lia | lia | lia
| unfold spZ; rewrite Rsp, Usp; fold (spZ regs); rewrite unsigned_lit_small by lia; lia
| replace (spZ regs - 128 - sp0) with (spZ regs - sp0 + (-8) * 16) by lia; rewrite Z_mod_plus_full, Zminus_mod, Hal16, Hsp0al; reflexivity
| lia
| unfold ESTACK; lia
| rewrite Rgp, E3; reflexivity
| rewrite Rtp, E4; reflexivity
| exact Rra
| vm_compute; reflexivity
| intros a Ha; split; [right; right; right; exists cid, pos; split; [exact Hown | left; unfold in_zr; cbn [fst snd]; lia] | unfold ESTACK; lia]
| apply amem_range_high; zone_lia
| eapply range_addressable_agree; [|exact RAdst]; intros x Hx; apply (aview_eq_of trasegs); apply HFr; rewrite unsigned_lit_small by (pose proof (shadow_addr_bounds x ltac:(lia)); unfold shadow_of_addr, shadow_addr in *; lia);
intros Hin; destruct (in_wrange_windows E _ _ Hin) as (b & wlo & whi & Ht & Hw); vm_compute in Ht;
repeat (destruct Ht as [Hq | Ht]; [injection Hq as <- <- <-; cbn [base_val] in Hw; rewrite ?Usp, ?B10, ?B11 in Hw; pose proof (shadow_addr_bounds x ltac:(lia)); unfold shadow_of_addr, shadow_addr in *; clear - Hw H HTS Has HSPB HSTB HDSTB C1 C2 C3 C4 C5; lia |]); destruct Ht
| intros _; eapply (shadow_hull_vis_of_frame trasegs B LAWS lyc Sc W _ _ cid pos dst 24 (proj1 HJ) Hfin); lia
| exact I ] end. }
cbv beta. intros W1 c1 _ (-> & regs1 & mem1 & md1 & -> & HJ1 & HP1 & Ha01 & Heff1 & Hfr1 & Hpres1).
replace (sp0 + (spZ regs - 128 - sp0)) with (spZ regs - 128) in Hfr1 by lia.
destruct (al_const _ _ LAWS _ _ _ _ _ (proj1 HJ)) as (Kcell0 & _ & Kgot0 & _). rewrite HBgot, HBcell in Kgot0. rewrite HBcell in Kcell0.
destruct (al_const _ _ LAWS _ _ _ _ _ (proj1 HJ1)) as (Kcell1 & _ & Kgot1 & _). rewrite HBgot, HBcell in Kgot1. rewrite HBcell in Kcell1.
clear Ra0 Ra1 Ra2 Rra Rsp Rgp Rtp.
unrun HFr (fun a => spZ regs - TRRFC_STK <= a < spZ regs \/ dst <= a < dst + 24 \/ st + 16 <= a < st + 24) Usp B10 B11 HTS Has UN0.
clear HF HFr HG.
pose proof (rfc_kept_step _ _ _ _ _ _ _ _ _ _ _ _ (rfc_kept_refl W memc (spZ regs) Bb lyc Sc st dst) HSEP UN0 ltac:(intros a Ha; exact Ha) ltac:(clear - HSPB; lia)) as KEPT0.
pose proof (rfc_kept_stepE _ _ _ _ _ _ _ _ _ _ _ (fun a => (dst <= a < dst + 24) \/ (spZ regs - 128 - ESTACK <= a < spZ regs - 128)) (fun _ => False) KEPT0 HSEP
ltac:(intros a Ha Hn; apply Hfr1; [exact Ha | clear - Hn; tauto | clear - Hn; tauto])
ltac:(intros a Ha; cbn beta in *; clear - Ha HTS Has; unfold ESTACK in Ha; lia) ltac:(clear - HSPB; lia)
ltac:(intros a F; destruct F) ltac:(intros b m i _ _ F; exact F) ltac:(intros c p a _ _ F; exact F)) as KEPT1.
assert (SHK1 : forall a, 2147450880 <= a < kHighShadowEnd -> aview trasegs (w_H W) mem1 a = aview trasegs (w_H W) memc a).
{ intros a Ha. rewrite (Hfr1 a) by (clear - Ha HSPB HDSTB C1 C2 C3 HTS Has; unfold ESTACK; lia).
apply UN0; [clear - Ha C1 C2 C3 C4 C5; lia|]. cbn beta. clear - Ha HTS Has HSPB HSTB HDSTB C1 C2 C3. lia. }
assert (RAdst1 : range_addressable (aview trasegs (w_H W) mem1) SHADOW_OFF dst 24) by (apply (RA_kept_low _ _ dst 24 SHK1); [lia | lia | exact RAdst]).
assert (RAst1 : range_addressable (aview trasegs (w_H W) mem1) SHADOW_OFF st 24) by (apply (RA_kept_low _ _ st 24 SHK1); [lia | lia | exact RAst]).
pose proof (conj E33 (conj E34 (conj E35 E36))) as EXT0.
reseat HS HJ1 HP1 [0; 1; 2; 3]%nat AG
ltac:(first [ eapply region_kept_aview; [evalER AG | intros a Ha; apply Hfr1; [clear - Ha HSPB HSTB HDSTB HTS Has C1 C3; lia | clear - Ha HSPB HSTB HDSTB Hsd HTS Has; unfold rboxed in Hsd; lia | clear - Ha HSPB HSTB HDSTB HTS Has; unfold ESTACK; lia] | exact Hpres1]
| apply (region_kept_val trasegs _ _ _ A_GOT_shadow 8 A_shadow_glob); [exact (val_mem_of_rdword trasegs _ _ _ _ Kgot0) | exact (val_mem_of_rdword trasegs _ _ _ _ Kgot1) | lia]
| apply (region_kept_val trasegs _ _ _ A_shadow_glob 8 SHADOW_OFF); [exact (val_mem_of_rdword trasegs _ _ _ _ Kcell0) | exact (val_mem_of_rdword trasegs _ _ _ _ Kcell1) | lia]
| match goal with |- ?g => idtac "KEPTFAIL" g end ]).
destruct (al_frames _ _ LAWS _ _ _ _ _ cid pos (proj1 HJ1) Hfin) as (_ & _ & HFpres1 & _).
assert (Hz8 : forall off, 0 <= off -> off + 8 <= 24 -> val_mem trasegs (mrestrict (w_H W) mem1) (dst + off) 8 0).
{ intros off H1 H2. apply val_mem_zero8. intros i Hi. replace (dst + off + i) with (dst + (off + i)) by lia. rewrite (Heff1 (off + i)) by lia. reflexivity. }
assert (Hz4 : forall off, 0 <= off -> off + 4 <= 24 -> val_mem trasegs (mrestrict (w_H W) mem1) (dst + off) 4 0).
{ intros off H1 H2. intros j Hj. destruct (aview_byte trasegs (w_H W) mem1 (dst + off + Z.of_nat j) 0 ltac:(replace (dst + off + Z.of_nat j) with (dst + (off + Z.of_nat j)) by lia; rewrite (Heff1 (off + Z.of_nat j)) by lia; reflexivity)) as (bb & Hbb & Hv & _).
rewrite Hbb. f_equal. apply bv_eq. rewrite Z_to_bv_unsigned. unfold YP0g.le_byte, bv_wrap.
repeat (rewrite Z.shiftr_0_l || rewrite Z.mod_0_l by (vm_compute; discriminate)). lia. }
assert (Hz1 : forall off, 0 <= off < 24 -> val_mem trasegs (mrestrict (w_H W) mem1) (dst + off) 1 0).
{ intros off Ho. apply val_mem1_of_aview. rewrite (Heff1 off) by lia. reflexivity. }
pose proof E11 as E11'; rewrite <- (AG 11%nat) in E11' by lia. pose proof E10 as E10'; rewrite <- (AG 10%nat) in E10' by lia.
pose proof Usp as Usp'; rewrite <- (AG 2%nat) in Usp' by lia.
assert (B10' : bv_unsigned (ew E0 10) = st) by (rewrite E10'; apply unsigned_lit_small; lia).
assert (B11' : bv_unsigned (ew E0 11) = dst) by (rewrite E11'; apply unsigned_lit_small; lia).
assert (E32' : ew E0 32 = Z_to_bv 64 SB) by (rewrite (AG 32%nat) by lia; exact E32).
lazymatch type of HS with st_ok _ ?Ex _ _ =>
pose proof (ast_ok_add_region trasegs Ex _ _
(YQ0b.mkRegion (Some 11%nat) 0 24 0 24
(YQ0b.mkChunk 0 (CVal 8 (SLit 0)) :: YQ0b.mkChunk 8 (CVal 4 (SLit 0)) :: map (fun off => YQ0b.mkChunk off (CVal 1 (SLit 0))) [12;13;14;15;16;17;18;19;20;21;22;23]))
HS eq_refl
ltac:(unfold region_ok; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val ms_mem restrict mkst map];
rewrite B11'; split; [lia|]; split; [lia|];
split; [intros o Ho; apply (apresent_writable trasegs); apply (proj1 (HFpres1 (dst + o) ltac:(lia)))|];
repeat (apply Forall_cons; [first [ apply (chunk_ok_val trasegs Ex _ dst _ 8 (SLit 0) 0); [reflexivity | zside | zside | apply Hz8; lia]
| apply (chunk_ok_val trasegs Ex _ dst _ 4 (SLit 0) 0); [reflexivity | zside | zside | apply Hz4; lia]
| apply (chunk_ok_val trasegs Ex _ dst _ 1 (SLit 0) 0); [reflexivity | zside | zside | apply Hz1; lia] ] |]);
apply Forall_nil)
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val];
rewrite B11', B10', Usp'; unfold A_GOT_shadow, A_shadow_glob; unfold rboxed in Hsd;
clear - Hsd HSPB HSTB HDSTB C1 C3 HTS Has; repeat split; zone_lia)) as HS3;
clear HS; rename HS3 into HS end.
norm_ss HS.
lazymatch goal with |- SRr _ ?Wg (mkCfg ?msF ?mdF) _ =>
lazymatch type of HS with st_ok _ ?Ev _ _ =>
eapply (RB (mkRFCX STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs Bb st dst N pdata nb cur cid pos E) Ev k _ _ Wg msF mdF) end end.
- unfold rf_base. cbn [x_STK x_sp0 x_FP x_ly x_S x_W0 x_mem0 x_md0 x_own x_lyc x_Sc x_W x_memc x_mdc x_k x_regs x_Bb x_st x_dst x_N x_pdata x_nb x_cur x_cid x_pos x_E0].
change RGBFC_SIZE with 24. destruct EXT0 as (X33 & X34 & X35 & X36).
repeat match goal with |- _ /\ _ => split end; try assumption; try reflexivity; try exact HJc; try (clear - HN Hcur; lia).
- unfold rf_E. cbn [x_E0 x_pdata x_nb x_cur]. split; [exact AG|]. repeat (split; [assumption|]). assumption.
- cbn [x_STK x_sp0 x_FP x_ly x_S x_W0 x_mem0 x_md0 x_own]. exact HJ1.
- cbn [x_Sc]. reflexivity.
- cbn [x_Sc x_k]. rewrite Z.sub_diag. apply jbud_refl.
- cbn [x_W x_memc x_regs x_Bb x_lyc x_Sc x_st x_dst]. exact KEPT1.
- cbn [x_st]. exact RAst1.
- cbn [x_dst]. exact RAdst1.
- split; [reflexivity | cbn [x_lyc x_Sc]; first [reflexivity | idtac "A-BLK"]].
- exact HS.
Qed.
End e.
End d.
