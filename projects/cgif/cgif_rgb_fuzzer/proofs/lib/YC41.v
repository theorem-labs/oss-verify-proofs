(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ0f YC02.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00 YI02 YI01 YI04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YC01 YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YG00 YG0a YG01 YG0h YG0u YG0d YC04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB0z YC19 YF8z YC1d YC1a YC2o YC10 YC2p YC0x YC1b YC2u YC4o YC4q YC4p YC3g YC46 YC4g YC4c YC4d YC4e YC4f YC4h YC4a YC47 YC48.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section b. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section d.
Variable B : asyms.
Hypothesis TL : TraLib B.
Hypothesis LAWS : AR_laws trasegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis AMEMCPY : aintrin_realizes trasegs B OCpy A_asan_memcpy.
Hypothesis TLZW : tlzw_spec B.
Let HBcode := tl_code B TL. Let errno_low := tl_env B TL.
Let HBgot := tl_got_shadow B TL. Let HBcell := tl_shadow_cell B TL. Let HBguar := tl_got_uar B TL. Let HBuar := tl_uar_cell B TL.
Lemma ra_L_aux : ra_from B ss_M (INV_M B) -> ra_from B ss_L (INV_L B).
Proof.
intros RM. ra_prelude.
pose proof HINV as (Hk3 & (K1 & EK & HK1r & HK1s) & (pI & E400 & HpI4096 & Eab3 & ApI & TpI)).
assert (HnP32 : h * w < 2 ^ 32) by (clear - HnP; lia). assert (HnP1 : 1 <= h * w) by (clear - Hw Hh; nia).
assert (Hrq : req_size (h * w) = h * w) by (unfold req_size; destruct (Z.eqb_spec (h * w) 0); [exfalso; clear - HnP1 e; lia | reflexivity]).
assert (HPerm3 : Permutation (ablocks B ly3 S3) ((pI, h * w) :: (raw, RAW_SIZE) :: (g, CGIF_SIZE) :: (img, Nimg) :: rest)).
{ rewrite Eab3. eapply Permutation_trans; [apply Permutation_sym; apply Permutation_cons_append|]. apply perm_skip. exact HPerm. }
assert (HpI3 : In (pI, h * w) (ablocks B ly3 S3)) by (rewrite Eab3; apply in_app_iff; right; left; reflexivity).
assert (Hraw3 : In (raw, RAW_SIZE) (ablocks B ly3 S3)) by (rewrite Eab3; apply in_app_iff; left; exact Hraw_in).
assert (Hing3 : In (g, CGIF_SIZE) (ablocks B ly3 S3)) by (rewrite Eab3; apply in_app_iff; left; exact Hing).
assert (Himg3 : In (img, Nimg) (ablocks B ly3 S3)) by (rewrite Eab3; apply in_app_iff; left; exact Himg_in).
ra_blocks3 Hraw3 Hing3. fold F in HdFR, HdFG.
destruct (al_blocks _ _ LAWS _ _ _ _ _ pI (h * w) HAR3 HpI3) as (Hp16 & _ & Hpceil & Hph_ia & Hppres & _). pose proof (proj1 Hph_ia) as Hph. rewrite Hrq in Hpceil, Hppres, Hph_ia.
pose proof (blk_off_img _ _ _ _ _ _ _ _ HAR3 HpI3) as Hph_img.      rewrite Hrq in Hph_img.
destruct (al_blocks _ _ LAWS _ _ _ _ _ img Nimg HAR3 Himg3) as (Hi16 & Hi4096 & Hiceil & Hih_ia & Hipres & _). pose proof (proj1 Hih_ia) as Hih.
pose proof (blk_off_img _ _ _ _ _ _ img Nimg HAR3 Himg3) as Hih_img.
pose proof (sep_blocks_perm trasegs B LAWS _ _ _ _ _ (pI, h * w) (raw, RAW_SIZE) _ HAR3 HPerm3) as HdPR.
pose proof (sep_blocks_perm trasegs B LAWS _ _ _ _ _ (pI, h * w) (g, CGIF_SIZE) _ HAR3 ltac:(eapply Permutation_trans; [exact HPerm3 | apply perm_skip; apply perm_swap])) as HdPG.
pose proof (sep_blocks_perm trasegs B LAWS _ _ _ _ _ (pI, h * w) (img, Nimg) _ HAR3
ltac:(eapply Permutation_trans; [exact HPerm3 | apply perm_skip; eapply Permutation_trans; [apply perm_skip; apply perm_swap | apply perm_swap]])) as HdPI.
unfold zdisjoint, block_rng in HdPR, HdPG, HdPI. cbn [fst snd] in HdPR, HdPG, HdPI. rewrite Hrq in HdPR, HdPG, HdPI.
change (req_size RAW_SIZE) with 48 in HdPR. change (req_size CGIF_SIZE) with 96 in HdPG.
pose proof (sep_block_frame trasegs B LAWS ly3 S3 _ _ _ pI (h * w) 1 fpos HAR3 HpI3 Hfin3) as HdPF.
unfold zdisjoint in HdPF. cbn [fst snd] in HdPF. rewrite Hrq in HdPF. change (fs_frame_bytes 1) with 128 in HdPF. rewrite EFA3 in HdPF. fold F in HdPF.
pose proof (sep_block_frame trasegs B LAWS ly3 S3 _ _ _ pI (h * w) cid pos HAR3 HpI3 HfinS3) as HdPC.
unfold zdisjoint in HdPC. cbn [fst snd] in HdPC. rewrite Hrq in HdPC. rewrite EFA3 in HdPC.
box HdPR. box HdPG. box HdPI. box HdPF. box HdPC.
relowC HS AG E10 E11 E32 E10n E11n E32n.
rreg HS (2%bv : bv 5) Rsp. rreg HS (3%bv : bv 5) Rgp. rreg HS (4%bv : bv 5) Rtp.
rreg HS (18%bv : bv 5) R18. rreg HS (27%bv : bv 5) R27. rewrite E400 in R27.
assert (Hcfp47 : 0 <= cfp /\ cfp + 40 < 2 ^ 47) by (clear - Hflo Hfhi Hf4096 Hfceil C1; lia).
rreg HS (25%bv : bv 5) R25. rewrite E11n in R25. rewrite unsigned_lit_small in R25 by (clear - Hcfp47; lia).
rreg HS (21%bv : bv 5) R21. rewrite E11n in R21. rewrite unsigned_lit_small in R21 by (clear - Hcfp47; lia).
rreg HS (22%bv : bv 5) R22. rewrite E11n in R22. rewrite unsigned_lit_small in R22 by (clear - Hcfp47; lia).
lazymatch type of HS with st_ok _ ?Ev _ _ =>
rreg_by HS (26%bv : bv 5) (Z_to_bv 64 (SB + (cfp + 8) / 8)) (denot_shadow_of Ev 11 40 cfp 8 E11n E40 ltac:(clear - Hcfp47; lia) ltac:(clear - Hcfp47; lia) ltac:(clear; lia)) R26;
rreg_by HS (19%bv : bv 5) (Z_to_bv 64 (SB + (cfp + 20) / 8)) (denot_shadow_of Ev 11 40 cfp 20 E11n E40 ltac:(clear - Hcfp47; lia) ltac:(clear - Hcfp47; lia) ltac:(clear; lia)) R19;
rreg_by HS (24%bv : bv 5) (Z_to_bv 64 (SB + (cfp + 22) / 8)) (denot_shadow_of Ev 11 40 cfp 22 E11n E40 ltac:(clear - Hcfp47; lia) ltac:(clear - Hcfp47; lia) ltac:(clear; lia)) R24 end.
assert (Usp3 : bv_unsigned (ew E 2) = spZ regs) by (rewrite (AG 2%nat) by lia; exact Usp).
lazymatch type of Rsp with getr ?rg 2 = _ =>
assert (EspX : spZ rg = spZ regs - 320) by (unfold spZ at 1; rewrite Rsp, Usp3, unsigned_lit_small by (clear - Hceil Hslo Hstk0 FFS Hshi H47 C1; lia); clear; lia) end.
lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
let rs := eval vm_compute in (ss_mem ssx) in
let i := idx_of_base rs 11%nat in let i := eval vm_compute in i in
let r := eval vm_compute in (nth i rs got_region) in
pose proof (st_ok_region_nth Ex ssx (restrict (w_H W3) msX) i r HS ltac:(vm_compute; reflexivity)) as HRc; cbn [ms_mem restrict] in HRc;
lazymatch type of HRc with region_ok _ _ _ (YQ0b.mkRegion (Some 11%nat) ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 11 cfp cs lo hi wlo whi 8 8%N (SOff 42 0) img HRc ltac:(evalE AG) ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E42, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
ltac:(clear - Rimg; cbn; lia) ltac:(cbn; lia)) as Mimg;
pose proof (field_of_region Ex _ 11 cfp cs lo hi wlo whi 20 2%N (SOff 44 0) w HRc ltac:(evalE AG) ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E44, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
ltac:(clear - Rw; cbn; lia) ltac:(cbn; lia)) as Mw;
pose proof (field_of_region Ex _ 11 cfp cs lo hi wlo whi 22 2%N (SOff 45 0) h HRc ltac:(evalE AG) ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E45, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
ltac:(clear - Rh; cbn; lia) ltac:(cbn; lia)) as Mh end;
clear HRc end.
rewrite (st_ok_restrict_mkst trasegs _ _ _ _ HS eq_refl). cbn [ss_pc].
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ (ms_mem _) _) ?mdX) _ =>
eapply (ra_il_all B LAWS AMEMCPY W3 (ms_regs msX) (ms_mem msX) mdX (spZ regs) ly S W mem md ly3 S3 k fpos raw pI (h * w) img Nimg w h cfp cid pos) end.
- clear - Hw Rw; lia. - clear - Hh Rh; lia. - clear; lia. - exact HnPN. - exact HJ3. - exact HpI3. - exact Himg3.
- intros blc lyq ownq a Hbl Ha. replace a with (pI + (a - pI)) by (clear; lia). apply (ApI blc lyq ownq (a - pI) Hbl). clear - Ha; lia.
- rewrite Hrq. clear - HdPI; unbox; lia.
- rewrite Hrq. clear - HdPC Hflo Hfhi; unbox; lia.
- exact Hrapp.
- exact HAR. - exact Hfin. - exact Hcid0. - exact Hfal. - exact Hflo. - exact Hfhi. - exact Hcal. - exact HRA.
- exact Mimg. - exact Mw. - exact Mh.
- exact EspX. - clear - Hceil Hslo Hstk0 FFS C1; lia. - clear - H47 Hshi; lia.
- rewrite Rgp. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite (AG 3%nat) by lia. rewrite (EE 3%nat 3%bv eq_refl). exact Hgp.
- rewrite Rtp. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite (AG 4%nat) by lia. rewrite (EE 4%nat 4%bv eq_refl). exact Htp.
- exact R25. - exact R26. - exact R21. - exact R19. - exact R22. - exact R24. - exact R27. - exact R18. }
cbv beta. intros W5 c5 Hwle5 (-> & regs5 & mem5 & md5 & -> & HJ5 & P27 & P10 & HK5 & Hout5 & Hpres5).
clear Rsp EspX Rgp Rtp R21 R22 R24 R25 R26 R27 R18 R19 Mimg Mw Mh P27.
assert (HF8c : 8 * (F / 8) <= F) by (apply Z.mul_div_le; clear; lia).
lazymatch type of HS with st_ok _ ?Ev ?ssx (restrict _ ?msX) =>
let kk := eval vm_compute in (run_K 0 (SOff 32 0) [] ssx) in
jafter_stretch_keep HS kk regs5 (mrestrict (w_H W3) mem5) IL_CLOB 0x890d8 [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12]%nat HS2;
lazymatch type of HS2 with _ -> Forall _ ?rs -> _ =>
assert (HRK : Forall (fun r => 0 <= base_val Ev (YQ0b.r_base r) + YQ0b.r_lo r /\ base_val Ev (YQ0b.r_base r) + YQ0b.r_hi r <= 2 ^ 64 /\
(base_val Ev (YQ0b.r_base r) + YQ0b.r_hi r <= pI \/ pI + w * h <= base_val Ev (YQ0b.r_base r) + YQ0b.r_lo r) /\
(base_val Ev (YQ0b.r_base r) + YQ0b.r_hi r <= spZ regs - 320 - ESTACK \/ spZ regs - 320 <= base_val Ev (YQ0b.r_base r) + YQ0b.r_lo r)) rs);
[ repeat apply Forall_cons; try apply Forall_nil; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val];
cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia;
rewrite ?RF, ?E70, ?E400; rewrite ?(AG 2%nat), ?(AG 10%nat), ?(AG 11%nat), ?(AG 32%nat) by lia; rewrite ?Usp, ?E10, ?E11, ?E32;
rewrite ?unsigned_lit_small by (unfold SB; lia);
unfold A_GOT_shadow, A_shadow_glob, A_GOT_uar, A_uar_glob, A_GOT_rawadd, CGIF_SIZE, SB, ESTACK;
clear - HFceil HFhigh HF8lo HF8hi HF8c Hceil Hslo Hstk0 Hshi H47 Hrh Hrceil Hgh Hgceil Hfceil Hfhigh Hflo Hfhi C1 C2 C3 C4 C5 FFS HpI4096 Hph Hph_img Hph_ia Hpceil HnP1 HdPR HdPG HdPF HdPC;
unbox; first [zone_lia | match goal with |- ?g => idtac "HRK-FAIL" g; fail end]
| specialize (HS2 HK5 (regions_kept_out2 Ev (w_H W3) (ms_mem msX) mem5 pI (pI + w * h) (spZ regs - 320 - ESTACK) (spZ regs - 320) _ Hout5 Hpres5 HRK)) ] end end.
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS. rebaseE HS AG HEv. clear HEv.
lazymatch type of HS with st_ok _ ?Ev ?ssx ?msx =>
pose proof (ast_ok_set_reg_fp trasegs Ev ssx msx (10%bv : bv 5) (SOff 45 0) HS ltac:(vm_compute; reflexivity)
ltac:(cbn [sv_denot ms_regs restrict mkst]; rewrite E45, Z.add_0_r, P10, Z_to_bv_bv_unsigned; reflexivity)) as HS3;
clear HS; rename HS3 into HS end.
norm_ss HS. clear P10.
lazymatch type of HUP with forall a, _ -> aview _ _ ?m3 a = _ =>
assert (HUP5 : forall a, spZ regs <= a < 2 ^ 64 -> aview trasegs (w_H W3) mem5 a = aview trasegs (w_H W) mem a)
by (intros a Ha; rewrite (Hout5 a); [apply HUP; exact Ha | clear - Ha Hbot Hslo Hceil Hstk0 C1 FFS; lia | clear - Ha Hpceil HnP1 C1 Hceil Hslo Hstk0 FFS; lia | clear - Ha; lia]) end.
clear HUP. rename HUP5 into HUP.
relowC HS AG E10 E11 E32 E10n E11n E32n. reshok_bx HS 40%nat.
clear Kgot3 Kcell3 Kguar3 Kuar3 Vgr3. aconstsA HROD HJ5 Kgot3 Kcell3 Kguar3 Kuar3 Vgr3.
aj_run_to_tok tratbl_lib_ok HS HJ5 SHOK RABspan A_LZW.
all: try (oblFA HJ5 E11n E40 HRA HAR Hfin Hcid0 Hflo Hfhi Hfal).
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: awrRA AG fpos F EFA3.
upd_aboveW HUP HFr AG. clear HF HFr HG.
rebaseE HS AG HEv. clear HEv.
lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
let rs := eval vm_compute in (ss_mem ssx) in
let i := idx_of_base rs 2%nat in let i := eval vm_compute in i in
let r := eval vm_compute in (nth i rs got_region) in
pose proof (st_ok_region_nth Ex ssx (restrict (w_H W3) msX) i r HS ltac:(vm_compute; reflexivity)) as HRstk; cbn [ms_mem restrict] in HRstk;
let rs' := eval vm_compute in (trim_stack rs (-104) 0) in
pose proof (st_ok_submem trasegs Ex ssx (restrict (w_H W3) msX) rs' HS ltac:(cbn [ss_mem]; submem_to) ltac:(vm_compute; reflexivity)) as HS3;
clear HS; rename HS3 into HS end.
lazymatch type of HS with st_ok _ ?Ev _ _ =>
lazymatch type of HRstk with region_ok _ _ _ ?rfull =>
let rlo := eval vm_compute in (trim_region rfull (-320) (-120)) in
pose proof (ast_ok_add_region trasegs Ev _ _ rlo HS eq_refl
ltac:(apply (region_ok_sub trasegs Ev _ rfull); [subregion_tac | cbn; lia | exact HRstk])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val];
evalE AG; unfold A_GOT_shadow, A_shadow_glob, A_GOT_uar, A_uar_glob, A_GOT_rawadd, CGIF_SIZE; repeat split; zone_lia)) as HS3;
clear HS HRstk; rename HS3 into HS end end.
norm_ss HS.
rreg HS (1%bv : bv 5) Rra. rreg HS (2%bv : bv 5) Rsp. rreg HS (3%bv : bv 5) Rgp. rreg HS (4%bv : bv 5) Rtp. rreg HS (8%bv : bv 5) Rs0.
rreg HS (10%bv : bv 5) Ra0. rreg HS (12%bv : bv 5) Ra2. rreg HS (13%bv : bv 5) Ra3. rreg HS (14%bv : bv 5) Ra4.
rewrite E400 in Ra2.
fact_of HS 355%nat F355. fact_of HS 356%nat F356.
clear Usp3.
lazymatch type of HS with st_ok _ ?Ev _ _ =>
assert (Usp3 : bv_unsigned (ew Ev 2) = spZ regs) by (rewrite (AG 2%nat) by lia; exact Usp);
set (idl := bv_unsigned (ew Ev 355)) in F355; set (icl := bv_unsigned (ew Ev 356)) in F356;
assert (E355 : ew Ev 355 = Z_to_bv 64 idl) by (symmetry; apply Z_to_bv_bv_unsigned);
assert (E356 : ew Ev 356 = Z_to_bv 64 icl) by (symmetry; apply Z_to_bv_bv_unsigned) end.
rewrite E355 in Ra3. rewrite E356 in Ra4.
assert (HnP31 : h * w < 2 ^ 31) by (clear - HnP; lia).
lazymatch type of HS with st_ok _ ?Ev _ _ =>
rreg_by HS (11%bv : bv 5) (Z_to_bv 64 (h * w)) (denot_mulw_hw Ev 45 44 h w E45 E44 ltac:(clear - Rh; lia) ltac:(clear - Rw; lia) HnP31) Ra1 end.
assert (Hchne : ch <> []) by (intros Hn; rewrite Hn in Hctx; cbn in Hctx; clear - Hctx; intuition discriminate).
pose proof Hch as Hch'. destruct Hch' as [(_ & Hn) | (Qs0lo & Qs0hi & Qs0al & _ & _)]; [exfalso; exact (Hchne Hn)|].
assert (Qtop64 : ly_top ly <= 2 ^ 64) by lia.
assert (Qra : 0 <= raZ regs < 2 ^ 64) by (unfold raZ; pose proof (bv_unsigned_in_range 64 (getr regs 1)) as Hq; change (bv_modulus 64) with (2 ^ 64) in Hq; exact Hq).
assert (Qs0 : 0 <= s0Z regs < 2 ^ 64) by (unfold s0Z; pose proof (bv_unsigned_in_range 64 (getr regs 8)) as Hq; change (bv_modulus 64) with (2 ^ 64) in Hq; exact Hq).
assert (Qal8 : spZ regs mod 8 = 0) by (pose proof (Z.div_mod (spZ regs) 32 ltac:(lia)) as D; rewrite Hal32, Z.add_0_r in D; rewrite D; replace (32 * (spZ regs / 32)) with ((4 * (spZ regs / 32)) * 8) by lia; apply Z_mod_mult).
lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
let rs := eval vm_compute in (ss_mem ssx) in
let ih := idx_of_base_lo rs 2%nat (-104) in let ih := eval vm_compute in ih in
let rh := eval vm_compute in (nth ih rs got_region) in
pose proof (st_ok_region_nth Ex ssx (restrict (w_H W3) msX) ih rh HS ltac:(vm_compute; reflexivity)) as HRstk; cbn [ms_mem restrict] in HRstk;
lazymatch type of HRstk with region_ok _ _ _ (YQ0b.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 2 (spZ regs) cs lo hi wlo whi (-8) 8%N (SOff 1 0) (raZ regs) HRstk
Usp3 ltac:(cbn; tauto) ltac:(cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by lia; rewrite ?ew_ewset_other by lia; rewrite (AG 1%nat) by lia; rewrite (EE 1%nat 1%bv eq_refl), Z.add_0_r; reflexivity)
ltac:(unfold raZ; pose proof (bv_unsigned_in_range 64 (getr regs 1)) as Hq; change (bv_modulus 64) with (2 ^ (8 * Z.of_N 8)) in Hq; exact Hq) ltac:(cbn; lia)) as Vra;
pose proof (field_of_region Ex _ 2 (spZ regs) cs lo hi wlo whi (-16) 8%N (SOff 8 0) (s0Z regs) HRstk
Usp3 ltac:(cbn; tauto) ltac:(cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by lia; rewrite ?ew_ewset_other by lia; rewrite (AG 8%nat) by lia; rewrite (EE 8%nat 8%bv eq_refl), Z.add_0_r; reflexivity)
ltac:(unfold s0Z; pose proof (bv_unsigned_in_range 64 (getr regs 8)) as Hq; change (bv_modulus 64) with (2 ^ (8 * Z.of_N 8)) in Hq; exact Hq) ltac:(cbn; lia)) as Vs0 end;
clear HRstk;
assert (Hch1 : achain ly3 (aview trasegs (w_H W3) (ms_mem msX)) (spZ regs - 320) (spZ regs) ((spZ regs, raZ regs, s0Z regs) :: ch));
[ apply (achain_ly_top ly); [pose proof (proj1 (proj2 HJ5)) as LY; destruct LY as (_ & _ & _ & _ & _ & _ & _ & _ & LT & _); exact LT|];
replace (spZ regs + -8) with (spZ regs - 8) in Vra by lia; replace (spZ regs + -16) with (spZ regs - 16) in Vs0 by lia;
exact (achain_push ly _ _ (spZ regs) (s0Z regs) (raZ regs) _ (spZ regs - 320) Hch Qtop64 HUP
(rdword_of_val_mem trasegs _ _ _ _ Vra Qra) (rdword_of_val_mem trasegs _ _ _ _ Vs0 Qs0) Hra4 ltac:(clear - Hceil Hslo Hstk0 FFS; lia) Qal8
ltac:(clear - Qs0lo Qs0hi; lia) ltac:(clear; lia))
| ] end.
pose proof HJ5 as (_ & HLY5 & _ & _ & _ & _ & Hnev5 & _ & _ & _ & _ & _ & _ & Hpres5' & _).
rewrite (st_ok_restrict_mkst trasegs _ _ _ _ HS eq_refl). cbn [ss_pc].
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ (ms_mem _) _) ?mdX) _ =>
pose proof (TLZW TRAWADD_STK (spZ regs) [(raw + 40, raw + 44)] ly S W mem md [(1, fpos)] ly3 S3 W3 (ms_mem msX) mdX k (ms_regs msX)
(spZ regs - 120) (h * w) pI idl icl pI (h * w) ((spZ regs, raZ regs, s0Z regs) :: ch) HJ5) as CALL end.
unfold cfg_at in CALL. change (w64 A_LZW) with (Z_to_bv 64 563128) in CALL. apply CALL; clear CALL.
- eapply arodata_ok_journal; [exact HJ5 | exact HROD].
- rewrite Rra. apply ret_ok_even. vm_compute. reflexivity.
- unfold raZ. rewrite Rra, unsigned_lit_small by (clear; lia). clear; lia.
- rewrite Rgp. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite (AG 3%nat) by lia. rewrite (EE 3%nat 3%bv eq_refl). exact Hgp.
- rewrite Rtp. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite (AG 4%nat) by lia. rewrite (EE 4%nat 4%bv eq_refl). exact Htp.
- rewrite Ra0. unfold w64. f_equal. rewrite Usp3. clear; lia.
- exact Ra1.
- exact Ra2.
- exact Ra3.
- exact Ra4.
- unfold spZ at 1. unfold s0Z. rewrite Rsp, Rs0. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia.
rewrite Usp3, !unsigned_lit_small by (clear - Hceil Hslo Hstk0 FFS Hshi H47 C1; lia). replace (spZ regs + -320) with (spZ regs - 320) by (clear; lia). exact Hch1.
- unfold raZ at 1. rewrite Rra, unsigned_lit_small by (clear; lia). cbn [spine map fst snd]. apply ctx_lzw2. exact Hctx.
- unfold spZ at 1. rewrite Rsp, Usp3, unsigned_lit_small by (clear - Hceil Hslo Hstk0 FFS Hshi H47 C1; lia).
pose proof (Z.div_mod (spZ regs) 32 ltac:(clear; lia)) as D. rewrite Hal32, Z.add_0_r in D. rewrite D.
replace (32 * (spZ regs / 32) + -320) with ((2 * (spZ regs / 32) - 20) * 16) by (clear; lia). apply Z_mod_mult.
- unfold spZ at 2. rewrite Rsp, Usp3, unsigned_lit_small by (clear - Hceil Hslo Hstk0 FFS Hshi H47 C1; lia). rewrite FFS. unfold LZW_TSTK, ASTACK. clear; lia.
- unfold spZ at 1. rewrite Rsp, Usp3, unsigned_lit_small by (clear - Hceil Hslo Hstk0 FFS Hshi H47 C1; lia). clear; lia.
- pose proof (Z.div_mod (spZ regs) 32 ltac:(clear; lia)) as D. rewrite Hal32, Z.add_0_r in D. rewrite D.
replace (32 * (spZ regs / 32) - 120) with ((4 * (spZ regs / 32) - 15) * 8) by (clear; lia). apply Z_mod_mult.
- left. unfold spZ at 1. rewrite Rsp, Usp3, unsigned_lit_small by (clear - Hceil Hslo Hstk0 FFS Hshi H47 C1; lia). clear; lia.
- clear - Hceil Hslo Hstk0 FFS C1. lia.
- clear - Hshi H47. lia.
- intros a Ha. split; [left; rewrite FFS; clear - Ha; lia | apply Hpres5'; rewrite FFS; clear - Ha; lia].
- right. destruct HLY5 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & SL & SH & _). rewrite SL, SH. clear - Hslo Hshi FFS. lia.
- clear - HnP HnP1. lia.
- clear - F355. lia.
- clear - F356. lia.
- exact HpI3.
- clear; lia.
- rewrite Hrq. clear; lia.
- rewrite HEV in Hev. unfold LZW_EV. clear - Hnev5 Hk3 Hev. lia.
- rewrite (blocks_bytes_bsum B ly3 S3), Eab3, bsum_app, <- (blocks_bytes_bsum B ly S). cbn [bsum fold_right snd]. unfold LIVE_RAWADD in Hlive. clear - Hlive HnP. lia. }
cbv beta. intros W6 c6 Hwle6 (ly6 & S6 & regs6 & mem6 & md6 & res & -> & HJ6 & HP6 & Ha06 & Hfrs6 & Hres).
lazymatch type of Rsp with getr ?rg 2 = _ =>
assert (EspY : spZ rg = spZ regs - 320) by (unfold spZ at 1; rewrite Rsp, Usp3, unsigned_lit_small by (clear - Hceil Hslo Hstk0 FFS Hshi H47 C1; lia); clear; lia) end.
rewrite EspY in Hres. rewrite Rra.
clear Rra Rsp Rgp Rtp Rs0 Ra0 Ra1 Ra2 Ra3 Ra4 Vra Vs0 Hch1 Hchne Qs0lo Qs0hi Qs0al Qtop64 Qra Qs0 Qal8 HLY5 Hnev5 Hpres5'.
pose proof (proj1 HJ6) as HAR6.
pose proof HJ6 as (_ & HLY6 & _ & _ & _ & _ & Hnev6 & _ & _ & _ & _ & _ & _ & Hpres6' & _).
destruct (al_layout _ _ LAWS _ _ _ _ _ ly6 HAR HLY6) as (_ & EFA6 & _).
assert (EFL6 : forall c p, flag_addr ly6 c p = flag_addr ly c p) by (intros c p; unfold flag_addr; pose proof (EFA6 c p) as X; unfold frame_addr in X; lia).
assert (Hfin6 : In (1, fpos) (frames S6)) by (rewrite Hfrs6; exact Hfin3).
assert (Hfrs6' : frames S6 = (1, fpos) :: frames S) by (rewrite Hfrs6; exact Hfrs3).
assert (HfinS6 : In (cid, pos) (frames S6)) by (rewrite Hfrs6; exact HfinS3).
frame_pres HJ6 Hfin6 EFA6 F HFpres6 HFSpres6.
clear Kgot3 Kcell3 Kguar3 Kuar3 Vgr3. aconstsA HROD HJ5 Kgot3 Kcell3 Kguar3 Kuar3 Vgr3. aconstsA HROD HJ6 Kgot6 Kcell6 Kguar6 Kuar6 Vgr6.
destruct Hres as [(Hres0 & bb & Lbb & M & HPerm6 & Hbb4096 & HM & Abb & Tbb & Vbb & VM & HK) | (Hres25 & HPerm6 & HK & HpR)].
+
assert (Hraw6 : In (raw, RAW_SIZE) (ablocks B ly6 S6)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm6|]; right; exact Hraw3).
assert (Hing6 : In (g, CGIF_SIZE) (ablocks B ly6 S6)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm6|]; right; exact Hing3).
assert (HpI6 : In (pI, h * w) (ablocks B ly6 S6)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm6|]; right; exact HpI3).
assert (Hbb6 : In (bb, Lbb) (ablocks B ly6 S6)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm6|]; left; reflexivity).
pose proof (sep_blocks_perm trasegs B LAWS _ _ _ _ _ (bb, Lbb) (raw, RAW_SIZE) _ HAR6 ltac:(eapply Permutation_trans; [exact HPerm6 | apply perm_skip; eapply Permutation_trans; [exact HPerm3 | apply perm_swap]])) as HdBR.
pose proof (sep_blocks_perm trasegs B LAWS _ _ _ _ _ (bb, Lbb) (g, CGIF_SIZE) _ HAR6
ltac:(eapply Permutation_trans; [exact HPerm6 | apply perm_skip; eapply Permutation_trans; [exact HPerm3 | eapply Permutation_trans; [apply perm_skip; apply perm_swap | apply perm_swap]]])) as HdBG.
unfold zdisjoint, block_rng in HdBR, HdBG. cbn [fst snd] in HdBR, HdBG. change (req_size RAW_SIZE) with 48 in HdBR. change (req_size CGIF_SIZE) with 96 in HdBG.
box HdBR. box HdBG.
destruct (al_blocks _ _ LAWS _ _ _ _ _ raw RAW_SIZE HAR6 Hraw6) as (_ & _ & _ & _ & Hrpres6 & _). change (req_size RAW_SIZE) with 48 in Hrpres6.
destruct (al_blocks _ _ LAWS _ _ _ _ _ bb Lbb HAR6 Hbb6) as (Hbb16 & _ & Hbbceil & Hbbh_ia & Hbbpres & _). pose proof (proj1 Hbbh_ia) as Hbbh.
pose proof (blk_off_img _ _ _ _ _ _ bb Lbb HAR6 Hbb6) as Hbbh_img.
pose proof (req_size_pos Lbb ltac:(clear - HM; lia)) as [_ HLbb].
reseat HS HJ6 HP6 [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13]%nat AG
ltac:(idtac; first [ keptLZW HK AG Hpres6' Hfin3 HfinS3 EFA3 F HFpres6 Hraw3 Hing3 Hrpres6
ltac:(intros a Ha Hx; clear - Ha Hx HdBR; unbox; lia) ltac:(intros a Ha Hx; clear - Ha Hx HdBG; unbox; lia)
Kgot3 Kgot6 Kcell3 Kcell6 Kguar3 Kguar6 Kuar3 Kuar6 Vgr3 Vgr6
| match goal with |- ?g => idtac "KEPTFAIL" g end ]).
relowC HS AG E10 E11 E32 E10n E11n E32n. norm_ss HS.
rreg HS (10%bv : bv 5) Qa0.
lazymatch type of Qa0 with _ = ?v => assert (Hv504 : v = Z_to_bv 64 0) by (rewrite <- Qa0; cbn [ms_regs]; rewrite Ha06, Hres0; reflexivity) end.
ra_join HS ss_M 500%nat ra_deads_M ltac:(idtac; ra_join_val HS 500%nat 4%nat Qa0 Eres). rewrite Hv504 in Eres.
ra_hand RM HS. split; [unfold LZW_EV; clear - Hk3; lia|].
split; [exists K1; split; [rewrite ew_havoc_old by (clear; lia); exact EK | split; [exact HK1r | exact HK1s]]|].
exists pI, 0. split; [rewrite ew_havoc_old by (clear; lia); exact E400|]. split; [exact Eres|]. split; [exact HpI4096|].
split; [exact HpI6|]. split; [exact TpI|].
left. split; [reflexivity|]. exists bb, Lbb, M. split; [rewrite <- Eab3; exact HPerm6|]. split; [exact Hbb4096|]. split; [exact HM|].
split; [exact Abb|]. split; [exact Tbb|]. split; [exact Vbb | exact VM].
+
assert (Hraw6 : In (raw, RAW_SIZE) (ablocks B ly6 S6)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm6|]; exact Hraw3).
assert (Hing6 : In (g, CGIF_SIZE) (ablocks B ly6 S6)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm6|]; exact Hing3).
assert (HpI6 : In (pI, h * w) (ablocks B ly6 S6)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm6|]; exact HpI3).
destruct (al_blocks _ _ LAWS _ _ _ _ _ raw RAW_SIZE HAR6 Hraw6) as (_ & _ & _ & _ & Hrpres6 & _). change (req_size RAW_SIZE) with 48 in Hrpres6.
reseat HS HJ6 HP6 [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13]%nat AG
ltac:(idtac; first [ keptLZW HK AG Hpres6' Hfin3 HfinS3 EFA3 F HFpres6 Hraw3 Hing3 Hrpres6
ltac:(intros a Ha Hx; exact Hx) ltac:(intros a Ha Hx; exact Hx)
Kgot3 Kgot6 Kcell3 Kcell6 Kguar3 Kguar6 Kuar3 Kuar6 Vgr3 Vgr6
| match goal with |- ?g => idtac "KEPTFAIL" g end ]).
relowC HS AG E10 E11 E32 E10n E11n E32n. norm_ss HS.
rreg HS (10%bv : bv 5) Qa0.
lazymatch type of Qa0 with _ = ?v => assert (Hv504 : v = Z_to_bv 64 res) by (rewrite <- Qa0; cbn [ms_regs]; rewrite Ha06; reflexivity) end.
ra_join HS ss_M 500%nat ra_deads_M ltac:(idtac; ra_join_val HS 500%nat 4%nat Qa0 Eres). rewrite Hv504 in Eres.
ra_hand RM HS. split; [unfold LZW_EV; clear - Hk3; lia|].
split; [exists K1; split; [rewrite ew_havoc_old by (clear; lia); exact EK | split; [exact HK1r | exact HK1s]]|].
exists pI, res. split; [rewrite ew_havoc_old by (clear; lia); exact E400|]. split; [exact Eres|]. split; [exact HpI4096|].
split; [exact HpI6|]. split; [exact TpI|].
right. split; [exact Hres25|]. rewrite <- Eab3. exact HPerm6.
Qed.
Lemma ra_L : ra_from B ss_M (INV_M B) -> ra_from B ss_L (INV_L B).
Proof. exact ra_L_aux. Qed.
End d.
End b.
