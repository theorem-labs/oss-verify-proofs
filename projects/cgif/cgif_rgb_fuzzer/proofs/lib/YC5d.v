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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00 YI02 YI04 YI1i YI08.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YC01 YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YG00 YG0a YG01 YG0h YG0u YG0d YC04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB0z YC19 YF8z YC1d YC1a YC2o YC10 YC1b YC2u
YC4u YC4z YC52 YC53 YC51.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK0p YI0c YM01 YG0e YC05.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCaq YC6j YCbj YCas YCat.
Section b. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section PA.
Variable B : asyms.
Hypothesis TL : TraLib B.
Hypothesis LAWS : AR_laws trasegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis SMP : stack_malloc_progressP B.
Hypothesis FFL : frame_flag_lawP trasegs B.
Hypothesis ASM7 : astack_malloc_sz_realizes trasegs B A_stack_malloc_7 7.
Hypothesis ASSF8 : aset_shadow_realizes trasegs B A_set_shadow_f8 0xf8.
Hypothesis ASS00 : aset_shadow_realizes trasegs B A_set_shadow_00 0.
Hypothesis AMEMSET : aintrin_realizes trasegs B OSet A_asan_memset.
Let HBcode := tl_code B TL. Let errno_low := tl_env B TL.
Lemma rga_A : rga_fromA B ss_E1 (fun _ => INV_0 B 0) -> trgb_addframe_specV B.
Proof.
intros RD.
unfold trgb_addframe_specV.
intros ly S W regs mem md ch r cfp g wfn ctx path attr gen loops Wd Hd bef beffmt cur s N img fmt fattr fgen delay rest
HPRE Hal32 Hctx Hroom Htop32 HROD Hfrm H10 H11 HFO Hcfg Hrgb Hcg Hwf HcW HcH HN Hbef HPerm Hev Hlive.
pose proof Hwx_tfa as Hwx. pose proof tra_segs_low as Hsegs.
assert (Hrin : In (r, RGB_SIZE) (ablocks B ly S)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm|]; left; reflexivity).
pose proof (rga_entry B TL LAWS W ly S regs mem md ch r cfp g wfn ctx path attr gen loops Wd Hd bef beffmt cur img fmt fattr fgen delay
HPRE Hal32 HROD H10 H11 HFO Hcfg Hrgb Hrin) as HS.
pose proof (ajournal_init trasegs B TRGBADD_STK (ablocks_fp [(r, RGB_SIZE)]) ly S W regs mem md ch HPRE) as HJ.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (FFS : TRGBADD_STK = 25088) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity.
remember (Ereg regs (rga_extra g wfn ctx path attr gen loops Wd Hd bef beffmt cur img fmt fattr fgen delay)) as E eqn:HE.
assert (EE : forall n (r0 : bv 5), Z.of_nat n = bv_unsigned r0 -> ew E n = getr regs r0) by (intros n r0 Hn; rewrite HE; apply ew_Ereg_nat; exact Hn).
assert (EX : forall j, (j < 18)%nat -> ew E (32 + j) = Z_to_bv 64 (nth j (rga_vals g wfn ctx path attr gen loops Wd Hd bef beffmt cur img fmt fattr fgen delay) 0)).
{ intros j Hj. rewrite HE, ew_Ereg_extra. unfold rga_extra. apply nth_error_nth. apply map_nth_error. apply nth_error_nth'. cbn [rga_vals length]. exact Hj. }
assert (E2 : ew E 2 = getr regs 2) by (exact (EE 2%nat 2%bv eq_refl)).
assert (E3 : ew E 3 = getr regs 3) by (exact (EE 3%nat 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regs 4) by (exact (EE 4%nat 4%bv eq_refl)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (E10 : ew E 10 = Z_to_bv 64 r) by (rewrite (EE 10%nat 10%bv eq_refl); exact H10).
assert (E11 : ew E 11 = Z_to_bv 64 cfp) by (rewrite (EE 11%nat 11%bv eq_refl); exact H11).
pose proof (EX 0%nat ltac:(lia)) as E32.
pose proof (EX 1%nat ltac:(lia)) as E33.
pose proof (EX 2%nat ltac:(lia)) as E34.
pose proof (EX 3%nat ltac:(lia)) as E35.
pose proof (EX 4%nat ltac:(lia)) as E36.
pose proof (EX 5%nat ltac:(lia)) as E37.
pose proof (EX 6%nat ltac:(lia)) as E38.
pose proof (EX 7%nat ltac:(lia)) as E39.
pose proof (EX 8%nat ltac:(lia)) as E40.
pose proof (EX 9%nat ltac:(lia)) as E41.
pose proof (EX 10%nat ltac:(lia)) as E42.
pose proof (EX 11%nat ltac:(lia)) as E43.
pose proof (EX 12%nat ltac:(lia)) as E44.
pose proof (EX 13%nat ltac:(lia)) as E45.
pose proof (EX 14%nat ltac:(lia)) as E46.
pose proof (EX 15%nat ltac:(lia)) as E47.
pose proof (EX 16%nat ltac:(lia)) as E48.
pose proof (EX 17%nat ltac:(lia)) as E49.
cbn [Nat.add nth rga_vals] in E32, E33, E34, E35, E36, E37, E38, E39, E40, E41, E42, E43, E44, E45, E46, E47, E48, E49.
destruct (al_blocks _ _ LAWS ly S W mem md r RGB_SIZE HAR Hrin) as (Hr16 & Hr4096 & Hrceil & [Hrh Hrapp] & Hrpres & _).
pose proof (blk_off_img _ _ _ _ _ _ r RGB_SIZE HAR Hrin) as Hrh_img.
change (req_size RGB_SIZE) with 64 in Hrceil, Hrpres, Hrh, Hrapp, Hrh_img. unfold RGB_SIZE in Hrin.
gboxh Hrapp. gboxh Hrh_img.
assert (Ar : forall blc (lyq : alayout) (ownq : list (Z * Z)) i, In (r, 64) blc -> 0 <= i < 64 ->
awr_byte TRGBADD_STK (spZ regs) (ablocks_fp [(r, RGB_SIZE)]) (ablocks B ly S) blc lyq ownq (r + i)).
{ intros blc lyq ownq i Hb Hi. right. left. split.
- apply (inFP_ablocks_fp _ r RGB_SIZE); [left; reflexivity | change (req_size RGB_SIZE) with 64; exact Hi].
- exists r, 64. split; [exact Hb | change (req_size 64) with 64; lia]. }
unfold cfg_at. change (w64 A_cgif_rgb_addframe) with (Z_to_bv 64 A_cgif_rgb_addframe).
shok_auto SHOK GBx E (mrestrict (w_H W) mem).
aj_run_tok tratbl_lib_ok HS HJ SHOK GBspan.
{ lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp0 fp b0 bc ly own) end.
repeat first
[ apply awr_ok_nil
| apply awr_ok_cons_ro; [azlit_tac|]
| eapply awr_ok_cons_stack; [reflexivity | exact Usp | azlit_tac | azlit_tac |]
| eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 10%nat); [reflexivity | rewrite E10; apply unsigned_lit_small; lia | | ];
[ cbn [YQ0b.r_wlo YQ0b.r_whi]; intros a Ha; replace a with (r + (a - r)) by lia; apply Ar; [exact Hrin | lia] | ] ]. }
clear HF HFr HG.
rreg HS (2%bv : bv 5) Q2. rreg HS (3%bv : bv 5) Q3. rreg HS (4%bv : bv 5) Q4. rreg HS (1%bv : bv 5) Q1. rreg HS (10%bv : bv 5) Q10.
rewrite (st_ok_restrict_mkst trasegs _ _ _ _ HS eq_refl). cbn [ss_pc].
change 250328 with A_stack_malloc_7.
pose proof (count_cid_le_length 7 (frames S)) as Hcnt.
ga_aconsts HROD HJ Kgot0 Kcell0 Kguar0 Kuar0 Vgr0.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
eapply (aj_stack_malloc_sz_at trasegs B LAWS Hsegs errno_low ML SMP A_stack_malloc_7 7 ASM7 ltac:(lia) W (ms_regs msX) (ms_mem msX) TRGBADD_STK (spZ regs)
(ablocks_fp [(r, RGB_SIZE)]) ly S W mem md [] ly S _ 0 (-512) _ 5216 HJ) end.
- unfold spZ. rewrite Q2, E2. fold (spZ regs). rewrite unsigned_lit_small by lia. lia.
- reflexivity. - lia. - rewrite FFS, Hes; lia.
- rewrite Q3, E3. exact Hgp. - rewrite Q4, E4. exact Htp.
- exact Q1. - vm_compute. reflexivity.
- exact Q10.
- change (fs_frame_bytes 7) with 8192. lia.
- reflexivity.
- let v := eval vm_compute in (fs_frames 7) in change (fs_frames 7) with v. lia. }
cbv beta. clear Q2 Q3 Q4 Q1 Q10 HJ SHOK.
intros W2 c2 _ (-> & S2 & regs2 & mem2 & md2 & fpos & -> & HJ2 & HP2 & Ha0 & Eab & Hfrs2 & Hnin & Hnev2 & Hbb2 & Hz & Hflag & HK).
rewrite Hes in HK. replace (spZ regs + -512 - 4096) with (spZ regs - 4608) in HK by lia. replace (spZ regs + -512) with (spZ regs - 512) in HK by lia.
destruct HFO as ((cid & pos & Hfin & Hcid0 & Hfal & Hflo & Hfhi) & Hcal & HRA). unfold RGBFC_SIZE in Hfhi, HRA.
destruct (frames_bounds trasegs B LAWS ly S W mem md cid pos HAR Hfin) as (Hf4096 & Hfceil & Hfhigh).
pose proof (frm_off_img _ _ _ _ _ _ _ _ HAR Hfin) as Hfhigh_img.
gboxh Hfhigh. gboxh Hfhigh_img.
assert (EFA0 : forall c p, frame_addr ly c p = frame_addr ly c p) by reflexivity.
assert (Hrin2 : In (r, 64) (ablocks B ly S2)) by (rewrite Eab; exact Hrin).
ga_aconsts HROD HJ2 Kgot2 Kcell2 Kguar2 Kuar2 Vgr2.
assert (AG : forall n, (n < 33)%nat -> ew E n = ew E n) by (intros; reflexivity).
reseat HS HJ2 HP2 [0; 1; 2; 3; 4; 5; 6; 7]%nat AG
ltac:(idtac; first [ lazymatch goal with
| |- region_kept _ _ _ _ (YQ0b.mkRegion (Some 2%nat) _ _ _ _ _) =>
eapply (region_kept_stack_aj trasegs _); [exact HK | exact HJ2 | cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?(AG 2%nat) by lia; exact Usp
| lia | unfold TRGBADD_STK, TRGBADD_FRAME, FDT_STK, TREE_HMAX, ASTACK; lia | lia | lia | lia]
| |- region_kept _ _ _ _ (YQ0b.mkRegion (Some 11%nat) _ _ _ _ _) =>
eapply (region_kept_frame_aj trasegs _); [exact HK | cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?(AG 11%nat) by lia; rewrite E11; apply unsigned_lit_small; lia
| exact Hfin | rewrite ?EFA0; lia | rewrite ?EFA0; lia | lia | intros a Ha Hn; exact Hn]
| |- region_kept _ _ _ _ (YQ0b.mkRegion (Some 10%nat) _ _ _ _ _) =>
eapply (region_kept_block_ajw2 trasegs _ LAWS); [exact HK | exact (proj1 HJ2) | exact Hrin2 | cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?(AG 10%nat) by lia; rewrite E10; apply unsigned_lit_small; lia
| exact Hrin | lia | change (req_size 64) with 64; lia | lia | lia | intros a Ha Hn; exact Hn]
| |- region_kept _ _ _ _ (YQ0b.mkRegion None _ _ _ _ _) => ga_kept_consts Kgot0 Kgot2 Kcell0 Kcell2 Kguar0 Kguar2 Kuar0 Kuar2 Vgr0 Vgr2 end
| match goal with |- ?g => idtac "KEPTFAIL" g end; fail ]).
clear Kgot0 Kcell0 Kguar0 Kuar0 Vgr0. rename Kgot2 into Kgot0. rename Kcell2 into Kcell0. rename Kguar2 into Kguar0. rename Kuar2 into Kuar0. rename Vgr2 into Vgr0.
rreg HS (10%bv : bv 5) RF. cbn [ms_regs] in RF. rewrite Ha0 in RF. symmetry in RF. unfold w64 in RF.
pose proof (proj1 HJ2) as HAR2.
assert (Hfin2 : In (7, fpos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
assert (HfinS2 : In (cid, pos) (frames S2)) by (rewrite Hfrs2; right; exact Hfin).
destruct (al_frames _ _ LAWS _ _ _ _ _ 7 fpos HAR2 Hfin2) as (HFal & [HFhi _] & HFpres & HFSpres).
destruct (frames_bounds trasegs B LAWS _ _ _ _ _ 7 fpos HAR2 Hfin2) as (HF4096 & HFceil & HFhigh).
pose proof (frm_off_img _ _ _ _ _ _ _ _ HAR2 Hfin2) as HFhigh_img.
change (fs_frame_bytes 7) with 8192 in *.
set (F := frame_addr ly 7 fpos) in *. set (FL := flag_addr ly 7 fpos) in *.
lazymatch type of HS with st_ok _ ?Ev ?ssv ?msv =>
pose proof (st_ok_agree trasegs 66 Ev (havoc Ev 66 [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)]) ssv msv HS
(env_agree_havoc_ge 66 66 Ev Ev _ ltac:(lia) (env_agree_refl 66 Ev)) ltac:(vm_compute; reflexivity)) as HS3 end.
clear HS. rename HS3 into HS. ga_rebaseE HS AG HEv.
lazymatch type of HS with st_ok _ ?Ev _ _ =>
assert (E66 : ew Ev 66 = Z_to_bv 64 FL) by (rewrite HEv; exact (ew_havoc_new _ 66 [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)] 0 (Z_to_bv 64 0) ltac:(cbn; lia)));
assert (E67 : ew Ev 67 = Z_to_bv 64 (SB + F / 8)) by (rewrite HEv; exact (ew_havoc_new _ 66 [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)] 1 (Z_to_bv 64 0) ltac:(cbn; lia))) end.
clear HEv.
assert (HFq : F = 32 * (F / 32)) by (pose proof (Z.div_mod F 32 ltac:(lia)); lia).
assert (HF8 : F / 8 = 4 * (F / 32)) by (rewrite HFq at 1; replace (32 * (F / 32)) with (4 * (F / 32) * 8) by lia; rewrite Z.div_mul by lia; reflexivity).
assert (HF8lo : 512 <= F / 8) by (apply Z.div_le_lower_bound; lia).
assert (HF8hi : F / 8 < 17592186044416) by (apply Z.div_lt_upper_bound; lia).
assert (HFrng : 0 <= F < 2 ^ 64) by (clear - HF4096 HFceil C1; lia).
gboxh HFhigh. gboxh HFhigh_img.
destruct (FFL ly S2 W mem2 md2 7 fpos HAR2 Hfin2) as (HFLpres & HFLown & HFLrng). fold FL in HFLpres, HFLown, HFLrng.
destruct (in_split _ _ Hfin) as (fl1 & fl2 & Efl).
pose proof (sep_frames_pos trasegs B LAWS ly S2 W mem2 md2 (7, fpos) (cid, pos) [] fl1 fl2 HAR2 ltac:(rewrite Hfrs2, Efl; reflexivity)) as HdFC.
unfold zdisjoint, frame_rng in HdFC. cbn [fst snd] in HdFC. change (fs_frame_bytes 7) with 8192 in HdFC. fold F in HdFC.
pose proof (sep_block_frame trasegs B LAWS ly S2 W mem2 md2 r 64 7 fpos HAR2 Hrin2 Hfin2) as HdFR.
unfold zdisjoint in HdFR. cbn [fst snd] in HdFR. change (req_size 64) with 64 in HdFR. change (fs_frame_bytes 7) with 8192 in HdFR. fold F in HdFR.
gboxh HdFC. gboxh HdFR.
clear fl1 fl2 Efl.
lazymatch type of HS with st_ok _ ?Ev _ _ =>
pose proof (st_ok_add_fact trasegs Ev _ _ 54 (HPTR 5) HS
ltac:(unfold afact_ok, HPTR; cbn [af_lo af_hi af_al2]; rewrite RF, unsigned_lit_small by lia; change (2 ^ 5) with 32; lia)) as HS3;
clear HS; rename HS3 into HS;
pose proof (st_ok_add_fact trasegs Ev _ _ 66 (HPTR 0) HS
ltac:(unfold afact_ok, HPTR; cbn [af_lo af_hi af_al2]; rewrite E66, unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r; lia)) as HS3;
clear HS; rename HS3 into HS;
pose proof (st_ok_add_fact trasegs Ev _ _ 67 (mkAF (SB + 512) (SB + 17592186044416) 2) HS
ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E67, unsigned_lit_small by (unfold SB; lia); change (2 ^ 2) with 4; unfold SB;
split; [lia|]; split; [rewrite HF8; replace (2147450880 + 4 * (F / 32)) with ((536862720 + F / 32) * 4) by lia; apply Z_mod_mult | lia])) as HS3;
clear HS; rename HS3 into HS;
pose proof (st_ok_add_alias trasegs Ev _ _ _ _ HS (shadow_decl_ok Ev 54 44 67 F SB RF HFrng E44 E67)) as HS3;
clear HS; rename HS3 into HS end.
lazymatch type of HS with st_ok _ ?Ev _ _ =>
pose proof (ast_ok_add_region trasegs Ev _ _ (fframe_region 54 66 7 []) HS eq_refl
ltac:(unfold region_ok, fframe_region; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val ms_mem restrict mkst app];
change (fs_frame_bytes 7) with 8192; rewrite RF, unsigned_lit_small by lia; split; [lia|]; split; [lia|]; split;
[ intros o Ho; apply (apresent_writable trasegs); apply (proj1 (HFpres (F + o) ltac:(lia)))
| apply Forall_cons; [|apply Forall_nil]; apply (chunk_ok_val trasegs Ev _ F (8192 - 8) 8 _ FL);
[cbn [sv_denot]; rewrite E66, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | replace (F + (8192 - 8)) with (F + 8192 - 8) by lia; exact (val_mem_of_rdword trasegs _ _ _ _ Hflag)] ])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint, fframe_region; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val];
change (fs_frame_bytes 7) with 8192;
rewrite RF, ?(AG 2%nat), ?(AG 10%nat), ?(AG 11%nat), ?Usp, ?E10, ?E11, !unsigned_lit_small by lia; unfold A_GOT_shadow, A_shadow_glob, A_GOT_uar, A_uar_glob, A_GOT_rgb_addframe;
repeat split; first [ga_zlia | match goal with |- ?g => idtac "DISJ1" g; fail end])) as HS3;
clear HS; rename HS3 into HS end.
norm_ss HS.
lazymatch type of HS with st_ok _ ?Ev _ _ =>
pose proof (ast_ok_add_region trasegs Ev _ _ (YQ0b.mkRegion (Some 67%nat) 0 4 0 4 []) HS eq_refl
ltac:(unfold region_ok; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val ms_mem restrict mkst app];
ga_evalE0 AG; split; [lia|]; split; [lia|]; split;
[ intros o Ho; apply (apresent_writable trasegs); unfold shadow_addr in HFSpres; rewrite <- ?SB_SHADOW_OFF in HFSpres; unfold SB in HFSpres;
apply (proj1 (HFSpres o ltac:(change (8192 / 8) with 1024; lia)))
| apply Forall_nil ])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val];
ga_evalE0 AG; repeat split; first [ga_zlia | match goal with |- ?g => idtac "DISJ2" g; fail end])) as HS3;
clear HS; rename HS3 into HS end.
norm_ss HS.
aj_run_to_sh tratbl_lib_ok HS HJ2 A_set_shadow_f8. { ga_awrR AG fpos F EFA0 54%nat 67%nat. }
clear HF HFr HG.
rreg HS (10%bv : bv 5) Ra0. rreg HS (11%bv : bv 5) Ra1. rreg HS (1%bv : bv 5) Rra.
rreg HS (2%bv : bv 5) Rsp. rreg HS (3%bv : bv 5) Rgp. rreg HS (4%bv : bv 5) Rtp.
rewrite (st_ok_restrict_mkst trasegs _ _ _ _ HS eq_refl). cbn [ss_pc].
change (Z_to_bv 64 348376) with (Z_to_bv 64 A_set_shadow_f8).
clear Kgot0 Kcell0 Kguar0 Kuar0 Vgr0. ga_aconsts HROD HJ2 Kgot0 Kcell0 Kguar0 Kuar0 Vgr0.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
eapply (aj_set_shadow_at trasegs B LAWS Hsegs A_set_shadow_f8 0xf8 ASSF8 _ (ms_regs msX) (ms_mem msX) TRGBADD_STK (spZ regs)
(ablocks_fp [(r, RGB_SIZE)]) ly S W mem md [(7, fpos)] ly S2 _ _ 7 fpos (SB + F / 8 + 4) 512 (-512) (Z_to_bv 64 0x82094) HJ2) end.
- left; reflexivity.
- rewrite Ra0. cbn [sv_denot]. ga_evalE0 AG. reflexivity.
- exact Ra1.
- lia.
- fold F. unfold shadow_addr. rewrite <- SB_SHADOW_OFF. unfold SB. lia.
- fold F. unfold shadow_addr. rewrite <- SB_SHADOW_OFF. change (fs_frame_bytes 7 / 8) with 1024. unfold SB. lia.
- unfold spZ at 1. rewrite Rsp. ga_evalE AG.
- reflexivity. - lia. - rewrite FFS. unfold ESTACK. lia.
- rewrite Rgp. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite (AG 3%nat) by lia. rewrite (EE 3%nat 3%bv eq_refl). exact Hgp.
- rewrite Rtp. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite (AG 4%nat) by lia. rewrite (EE 4%nat 4%bv eq_refl). exact Htp.
- exact Rra.
- vm_compute. reflexivity. }
cbv beta. intros W4 c4 _ (-> & regs4 & mem4 & md4 & -> & HJ4 & HP4 & Heff4 & Hfr4 & Hoff4).
clear Ra0 Ra1 Rra Rsp Rgp Rtp.
ga_aconsts HROD HJ4 Kgot4 Kcell4 Kguar4 Kuar4 Vgr4.
reseat HS HJ4 HP4 [1; 2; 3; 4; 5; 6; 7; 8; 9]%nat AG
ltac:(idtac; first [ ga_keptV Hfr4 Hoff4 AG Kgot0 Kgot4 Kcell0 Kcell4 Kguar0 Kguar4 Kuar0 Kuar4 Vgr0 Vgr4 | match goal with |- ?g => idtac "KEPTFAIL" g end; fail ]).
clear Kgot0 Kcell0 Kguar0 Kuar0 Vgr0. rename Kgot4 into Kgot0. rename Kcell4 into Kcell0. rename Kguar4 into Kguar0. rename Kuar4 into Kuar0. rename Vgr4 into Vgr0.
destruct (al_frames _ _ LAWS _ _ _ _ _ 7 fpos (proj1 HJ4) Hfin2) as (_ & _ & HFpres4 & HFSpres4).
change (fs_frame_bytes 7) with 8192 in HFpres4, HFSpres4. fold F in HFpres4, HFSpres4.
lazymatch type of HS with st_ok _ ?Ev _ _ =>
pose proof (ast_ok_add_region trasegs Ev _ _ (YQ0b.mkRegion (Some 67%nat) 516 532 516 532 []) HS eq_refl
ltac:(unfold region_ok; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val ms_mem restrict mkst app];
ga_evalE0 AG; split; [lia|]; split; [lia|]; split;
[ intros o Ho; apply (apresent_writable trasegs); unfold shadow_addr in HFSpres4; rewrite <- ?SB_SHADOW_OFF in HFSpres4; unfold SB in HFSpres4;
apply (proj1 (HFSpres4 o ltac:(change (8192 / 8) with 1024; lia)))
| apply Forall_nil ])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val];
ga_evalE0 AG; repeat split; first [ga_zlia | match goal with |- ?g => idtac "DISJ2" g; fail end])) as HS3;
clear HS; rename HS3 into HS end.
norm_ss HS.
aj_run_to_sh tratbl_lib_ok HS HJ4 A_set_shadow_f8. { ga_awrR AG fpos F EFA0 54%nat 67%nat. }
clear HF HFr HG.
rreg HS (10%bv : bv 5) Ra0. rreg HS (11%bv : bv 5) Ra1. rreg HS (1%bv : bv 5) Rra.
rreg HS (2%bv : bv 5) Rsp. rreg HS (3%bv : bv 5) Rgp. rreg HS (4%bv : bv 5) Rtp.
rewrite (st_ok_restrict_mkst trasegs _ _ _ _ HS eq_refl). cbn [ss_pc].
change (Z_to_bv 64 348376) with (Z_to_bv 64 A_set_shadow_f8).
clear Kgot0 Kcell0 Kguar0 Kuar0 Vgr0. ga_aconsts HROD HJ4 Kgot0 Kcell0 Kguar0 Kuar0 Vgr0.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
eapply (aj_set_shadow_at trasegs B LAWS Hsegs A_set_shadow_f8 0xf8 ASSF8 _ (ms_regs msX) (ms_mem msX) TRGBADD_STK (spZ regs)
(ablocks_fp [(r, RGB_SIZE)]) ly S W mem md [(7, fpos)] ly S2 _ _ 7 fpos (SB + F / 8 + 532) 96 (-512) (Z_to_bv 64 0x820e8) HJ4) end.
- left; reflexivity.
- rewrite Ra0. cbn [sv_denot]. ga_evalE0 AG. reflexivity.
- exact Ra1.
- lia.
- fold F. unfold shadow_addr. rewrite <- SB_SHADOW_OFF. unfold SB. lia.
- fold F. unfold shadow_addr. rewrite <- SB_SHADOW_OFF. change (fs_frame_bytes 7 / 8) with 1024. unfold SB. lia.
- unfold spZ at 1. rewrite Rsp. ga_evalE AG.
- reflexivity. - lia. - rewrite FFS. unfold ESTACK. lia.
- rewrite Rgp. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite (AG 3%nat) by lia. rewrite (EE 3%nat 3%bv eq_refl). exact Hgp.
- rewrite Rtp. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite (AG 4%nat) by lia. rewrite (EE 4%nat 4%bv eq_refl). exact Htp.
- exact Rra.
- vm_compute. reflexivity. }
cbv beta. intros W5 c5 _ (-> & regs5 & mem5 & md5 & -> & HJ5 & HP5 & Heff5 & Hfr5 & Hoff5).
clear Ra0 Ra1 Rra Rsp Rgp Rtp.
ga_aconsts HROD HJ5 Kgot5 Kcell5 Kguar5 Kuar5 Vgr5.
reseat HS HJ5 HP5 [1; 2; 3; 4; 5; 6; 7; 8; 9]%nat AG
ltac:(idtac; first [ ga_keptV Hfr5 Hoff5 AG Kgot0 Kgot5 Kcell0 Kcell5 Kguar0 Kguar5 Kuar0 Kuar5 Vgr0 Vgr5 | match goal with |- ?g => idtac "KEPTFAIL" g end; fail ]).
clear Kgot0 Kcell0 Kguar0 Kuar0 Vgr0. rename Kgot5 into Kgot0. rename Kcell5 into Kcell0. rename Kguar5 into Kguar0. rename Kuar5 into Kuar0. rename Vgr5 into Vgr0.
destruct (al_frames _ _ LAWS _ _ _ _ _ 7 fpos (proj1 HJ5) Hfin2) as (_ & _ & HFpres5 & HFSpres5).
change (fs_frame_bytes 7) with 8192 in HFpres5, HFSpres5. fold F in HFpres5, HFSpres5.
lazymatch type of HS with st_ok _ ?Ev _ _ =>
pose proof (ast_ok_add_region trasegs Ev _ _ (YQ0b.mkRegion (Some 67%nat) 628 652 628 652 []) HS eq_refl
ltac:(unfold region_ok; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val ms_mem restrict mkst app];
ga_evalE0 AG; split; [lia|]; split; [lia|]; split;
[ intros o Ho; apply (apresent_writable trasegs); unfold shadow_addr in HFSpres5; rewrite <- ?SB_SHADOW_OFF in HFSpres5; unfold SB in HFSpres5;
apply (proj1 (HFSpres5 o ltac:(change (8192 / 8) with 1024; lia)))
| apply Forall_nil ])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val];
ga_evalE0 AG; repeat split; first [ga_zlia | match goal with |- ?g => idtac "DISJ2" g; fail end])) as HS3;
clear HS; rename HS3 into HS end.
norm_ss HS.
aj_run_to_sh tratbl_lib_ok HS HJ5 A_set_shadow_00. { ga_awrR AG fpos F EFA0 54%nat 67%nat. }
clear HF HFr HG.
rreg HS (10%bv : bv 5) Ra0. rreg HS (11%bv : bv 5) Ra1. rreg HS (1%bv : bv 5) Rra.
rreg HS (2%bv : bv 5) Rsp. rreg HS (3%bv : bv 5) Rgp. rreg HS (4%bv : bv 5) Rtp.
rewrite (st_ok_restrict_mkst trasegs _ _ _ _ HS eq_refl). cbn [ss_pc].
change (Z_to_bv 64 348088) with (Z_to_bv 64 A_set_shadow_00).
clear Kgot0 Kcell0 Kguar0 Kuar0 Vgr0. ga_aconsts HROD HJ5 Kgot0 Kcell0 Kguar0 Kuar0 Vgr0.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
eapply (aj_set_shadow_at trasegs B LAWS Hsegs A_set_shadow_00 0 ASS00 _ (ms_regs msX) (ms_mem msX) TRGBADD_STK (spZ regs)
(ablocks_fp [(r, RGB_SIZE)]) ly S W mem md [(7, fpos)] ly S2 _ _ 7 fpos (SB + F / 8 + 532) 96 (-512) (Z_to_bv 64 0x8215c) HJ5) end.
- left; reflexivity.
- rewrite Ra0. cbn [sv_denot]. ga_evalE0 AG. reflexivity.
- exact Ra1.
- lia.
- fold F. unfold shadow_addr. rewrite <- SB_SHADOW_OFF. unfold SB. lia.
- fold F. unfold shadow_addr. rewrite <- SB_SHADOW_OFF. change (fs_frame_bytes 7 / 8) with 1024. unfold SB. lia.
- unfold spZ at 1. rewrite Rsp. ga_evalE AG.
- reflexivity. - lia. - rewrite FFS. unfold ESTACK. lia.
- rewrite Rgp. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite (AG 3%nat) by lia. rewrite (EE 3%nat 3%bv eq_refl). exact Hgp.
- rewrite Rtp. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite (AG 4%nat) by lia. rewrite (EE 4%nat 4%bv eq_refl). exact Htp.
- exact Rra.
- vm_compute. reflexivity. }
cbv beta. intros W6 c6 _ (-> & regs6 & mem6 & md6 & -> & HJ6 & HP6 & Heff6 & Hfr6 & Hoff6).
clear Ra0 Ra1 Rra Rsp Rgp Rtp.
ga_aconsts HROD HJ6 Kgot6 Kcell6 Kguar6 Kuar6 Vgr6.
reseat HS HJ6 HP6 [1; 2; 3; 4; 5; 6; 7; 8; 9]%nat AG
ltac:(idtac; first [ ga_keptV Hfr6 Hoff6 AG Kgot0 Kgot6 Kcell0 Kcell6 Kguar0 Kguar6 Kuar0 Kuar6 Vgr0 Vgr6 | match goal with |- ?g => idtac "KEPTFAIL" g end; fail ]).
clear Kgot0 Kcell0 Kguar0 Kuar0 Vgr0. rename Kgot6 into Kgot0. rename Kcell6 into Kcell0. rename Kguar6 into Kguar0. rename Kuar6 into Kuar0. rename Vgr6 into Vgr0.
destruct (al_frames _ _ LAWS _ _ _ _ _ 7 fpos (proj1 HJ6) Hfin2) as (_ & _ & HFpres6 & HFSpres6).
change (fs_frame_bytes 7) with 8192 in HFpres6, HFSpres6. fold F in HFpres6, HFSpres6.
assert (ZS6 : forall j, 0 <= j < 12 -> val_mem trasegs (mrestrict (w_H W) mem6) (SB + F / 8 + (532 + 8 * j)) 8 0).
{ intros j Hj. apply val_mem_zero8. intros i Hi.
replace (SB + F / 8 + (532 + 8 * j) + i) with (SB + F / 8 + 532 + (8 * j + i)) by lia. apply Heff6. lia. }
lazymatch type of HS with st_ok _ ?Ev _ _ =>
pose proof (ast_ok_add_region trasegs Ev _ _
(YQ0b.mkRegion (Some 67%nat) 532 628 0 0
[YQ0b.mkChunk 532 (CVal 8 (SLit 0)); YQ0b.mkChunk 540 (CVal 8 (SLit 0)); YQ0b.mkChunk 548 (CVal 8 (SLit 0)); YQ0b.mkChunk 556 (CVal 8 (SLit 0));
YQ0b.mkChunk 564 (CVal 8 (SLit 0)); YQ0b.mkChunk 572 (CVal 8 (SLit 0)); YQ0b.mkChunk 580 (CVal 8 (SLit 0)); YQ0b.mkChunk 588 (CVal 8 (SLit 0));
YQ0b.mkChunk 596 (CVal 8 (SLit 0)); YQ0b.mkChunk 604 (CVal 8 (SLit 0)); YQ0b.mkChunk 612 (CVal 8 (SLit 0)); YQ0b.mkChunk 620 (CVal 8 (SLit 0))]) HS eq_refl
ltac:(unfold region_ok; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val ms_mem restrict mkst app];
ga_evalE0 AG; split; [lia|]; split; [lia|]; split; [intros o Ho; lia|];
repeat (apply Forall_cons; [
lazymatch goal with |- YQ0b.chunk_ok _ _ _ _ (YQ0b.mkChunk ?off _) =>
apply (chunk_ok_val trasegs Ev _ (SB + F / 8) off 8 _ 0); [reflexivity | zside | zside |
let j := eval vm_compute in ((off - 532) / 8) in
replace (SB + F / 8 + off) with (SB + F / 8 + (532 + 8 * j)) by lia; apply ZS6; lia] end |]);
apply Forall_nil)
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val];
ga_evalE0 AG; repeat split; first [ga_zlia | match goal with |- ?g => idtac "DISJ3" g; fail end])) as HS3;
clear HS; rename HS3 into HS end.
norm_ss HS.
aj_run_to_sh tratbl_lib_ok HS HJ6 A_asan_memset. { ga_awrR AG fpos F EFA0 54%nat 67%nat. }
clear HF HFr HG.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msX) =>
assert (HpresF : forall a, F <= a < F + 8192 -> apresent (w_H W) (ms_mem msX) a) end.
{ destruct (al_frames _ _ LAWS _ _ _ _ _ 7 fpos (proj1 HJ6) Hfin2) as (_ & _ & HFpresX & _). change (fs_frame_bytes 7) with 8192 in HFpresX. fold F in HFpresX.
intros a Ha. exact (proj1 (HFpresX a Ha)). }
lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
let rs := eval vm_compute in (ss_mem ssx) in
let i := ga_idx_of_base rs 54%nat in let i := eval vm_compute in i in
pose proof (st_ok_submem trasegs Ex ssx msx (firstn i (ss_mem ssx) ++ trim_lo (nth i (ss_mem ssx) got_region) 5184 :: skipn (Datatypes.S i) (ss_mem ssx)) HS
ltac:(cbn [ss_mem nth skipn firstn app]; repeat (apply submem_keep; [first [apply subregion_trim_lo | apply subregion_refl]|]); apply submem_refl)
ltac:(vm_compute; reflexivity)) as HS3;
clear HS; rename HS3 into HS end.
norm_ss HS.
lazymatch type of HS with st_ok _ ?Ex _ _ =>
pose proof (ast_ok_add_region trasegs Ex _ _ (YQ0b.mkRegion (Some 54%nat) 32 4256 32 4256 []) HS eq_refl
ltac:(unfold region_ok; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val ms_mem restrict mkst];
ga_evalE0 AG; split; [lia|]; split; [lia|]; split; [|apply Forall_nil];
intros o Ho; apply (apresent_writable trasegs); apply HpresF; lia)
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val];
ga_evalE0 AG; repeat split; first [ga_zlia | match goal with |- ?g => idtac "DISJ4" g; fail end])) as HS3;
clear HS; rename HS3 into HS end.
norm_ss HS.
lazymatch type of HS with st_ok _ ?Ex _ _ =>
pose proof (ast_ok_add_region trasegs Ex _ _ (YQ0b.mkRegion (Some 54%nat) 0 32 0 32 []) HS eq_refl
ltac:(unfold region_ok; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val ms_mem restrict mkst];
ga_evalE0 AG; split; [lia|]; split; [lia|]; split; [|apply Forall_nil];
intros o Ho; apply (apresent_writable trasegs); apply HpresF; lia)
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val];
ga_evalE0 AG; repeat split; first [ga_zlia | match goal with |- ?g => idtac "DISJ4" g; fail end])) as HS3;
clear HS; rename HS3 into HS end.
norm_ss HS.
lazymatch type of HS with st_ok _ ?Ex _ _ =>
pose proof (ast_ok_add_region trasegs Ex _ _ (YQ0b.mkRegion (Some 54%nat) 5152 5168 5152 5168 []) HS eq_refl
ltac:(unfold region_ok; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val ms_mem restrict mkst];
ga_evalE0 AG; split; [lia|]; split; [lia|]; split; [|apply Forall_nil];
intros o Ho; apply (apresent_writable trasegs); apply HpresF; lia)
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val];
ga_evalE0 AG; repeat split; first [ga_zlia | match goal with |- ?g => idtac "DISJ4" g; fail end])) as HS3;
clear HS; rename HS3 into HS end.
norm_ss HS.
ga_ra_frame HS AG HFq F 532 532 96 HRApal7.
rreg HS (10%bv : bv 5) Ra0. rreg HS (11%bv : bv 5) Ra1. rreg HS (12%bv : bv 5) Ra2. rreg HS (1%bv : bv 5) Rra.
rreg HS (2%bv : bv 5) Rsp. rreg HS (3%bv : bv 5) Rgp. rreg HS (4%bv : bv 5) Rtp.
rewrite (st_ok_restrict_mkst trasegs _ _ _ _ HS eq_refl). cbn [ss_pc].
change (Z_to_bv 64 336460) with (Z_to_bv 64 A_asan_memset).
clear Kgot0 Kcell0 Kguar0 Kuar0 Vgr0. ga_aconsts HROD HJ6 Kgot0 Kcell0 Kguar0 Kuar0 Vgr0.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
eapply (aj_intrin_at trasegs B LAWS Hsegs OSet A_asan_memset AMEMSET _ (ms_regs msX) (ms_mem msX) TRGBADD_STK (spZ regs)
(ablocks_fp [(r, RGB_SIZE)]) ly S W mem md [(7, fpos)] ly S2 _ _ (F + 4256) 0 768 (-512) (Z_to_bv 64 0x8216c) HJ6) end.
- rewrite Ra0. cbn [sv_denot]. ga_evalE0 AG. first [reflexivity | unfold w64; f_equal; lia].
- exact Ra1.
- exact Ra2.
- lia. - lia. - lia.
- unfold spZ at 1. rewrite Rsp. ga_evalE AG.
- reflexivity. - lia. - rewrite FFS. unfold ESTACK. lia.
- rewrite Rgp. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite (AG 3%nat) by lia. rewrite (EE 3%nat 3%bv eq_refl). exact Hgp.
- rewrite Rtp. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite (AG 4%nat) by lia. rewrite (EE 4%nat 4%bv eq_refl). exact Htp.
- exact Rra.
- vm_compute. reflexivity.
- intros a Ha. split; [| unfold ESTACK; ga_zlia_k F]. right. right. right. exists 7, fpos. split; [left; reflexivity|]. left.
unfold in_zr, frame_rng. cbn [fst snd]. change (fs_frame_bytes 7) with 8192. fold F. lia.
- apply amem_range_high; [clear; lia | unfold gbox in HFhigh; destruct HFhigh as [_ HFz]; unfold kLowShadowBeg, kHighMemBeg in HFz; clear - HFz; lia | clear - HFceil; lia].
- replace (F + 4256) with (F + 8 * 532) by lia. replace 768 with (8 * 96) by lia. exact HRApal7.
- intros _. eapply (shadow_hull_vis_of_frame trasegs B LAWS ly S2 _ _ _ 7 fpos (F + 4256) 768 (proj1 HJ6) Hfin2);
[fold F; lia | fold F; change (fs_frame_bytes 7) with 8192; lia | lia].
- exact I. }
cbv beta. intros W7 c7 _ (-> & regs7 & mem7 & md7 & -> & HJ7 & HP7 & Ha07 & Heff7 & Hfr7 & Hpres7).
clear Ra0 Ra1 Ra2 Rra Rsp Rgp Rtp.
ga_aconsts HROD HJ7 Kgot7 Kcell7 Kguar7 Kuar7 Vgr7.
reseat HS HJ7 HP7 [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12]%nat AG
ltac:(idtac; first [ ga_keptI2 Hfr7 Hpres7 AG Kgot0 Kgot7 Kcell0 Kcell7 Kguar0 Kguar7 Kuar0 Kuar7 Vgr0 Vgr7 | match goal with |- ?g => idtac "KEPTFAIL" g end; fail ]).
clear Kgot0 Kcell0 Kguar0 Kuar0 Vgr0. rename Kgot7 into Kgot0. rename Kcell7 into Kcell0. rename Kguar7 into Kguar0. rename Kuar7 into Kuar0. rename Vgr7 into Vgr0.
destruct (al_frames _ _ LAWS _ _ _ _ _ 7 fpos (proj1 HJ7) Hfin2) as (_ & _ & HFpres7 & HFSpres7).
change (fs_frame_bytes 7) with 8192 in HFpres7, HFSpres7. fold F in HFpres7, HFSpres7.
lazymatch type of HS with st_ok _ ?Ev _ _ =>
pose proof (ast_ok_add_region trasegs Ev _ _ (YQ0b.mkRegion (Some 67%nat) 644 648 644 648 []) HS eq_refl
ltac:(unfold region_ok; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val ms_mem restrict mkst app];
ga_evalE0 AG; split; [lia|]; split; [lia|]; split;
[ intros o Ho; apply (apresent_writable trasegs); unfold shadow_addr in HFSpres7; rewrite <- ?SB_SHADOW_OFF in HFSpres7; unfold SB in HFSpres7;
apply (proj1 (HFSpres7 o ltac:(change (8192 / 8) with 1024; lia)))
| apply Forall_nil ])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val];
ga_evalE0 AG; repeat split; first [ga_zlia | match goal with |- ?g => idtac "DISJ2" g; fail end])) as HS3;
clear HS; rename HS3 into HS end.
norm_ss HS.
aj_run_to_sh tratbl_lib_ok HS HJ7 A_asan_memset. { ga_awrR AG fpos F EFA0 54%nat 67%nat. }
clear HF HFr HG.
ga_fs_ro_lo HS 644.
ga_ra_frame HS AG HFq F 644 646 2 HRAcfg8.
rreg HS (10%bv : bv 5) Ra0. rreg HS (11%bv : bv 5) Ra1. rreg HS (12%bv : bv 5) Ra2. rreg HS (1%bv : bv 5) Rra.
rreg HS (2%bv : bv 5) Rsp. rreg HS (3%bv : bv 5) Rgp. rreg HS (4%bv : bv 5) Rtp.
rewrite (st_ok_restrict_mkst trasegs _ _ _ _ HS eq_refl). cbn [ss_pc].
change (Z_to_bv 64 336460) with (Z_to_bv 64 A_asan_memset).
clear Kgot0 Kcell0 Kguar0 Kuar0 Vgr0. ga_aconsts HROD HJ7 Kgot0 Kcell0 Kguar0 Kuar0 Vgr0.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
eapply (aj_intrin_at trasegs B LAWS Hsegs OSet A_asan_memset AMEMSET _ (ms_regs msX) (ms_mem msX) TRGBADD_STK (spZ regs)
(ablocks_fp [(r, RGB_SIZE)]) ly S W mem md [(7, fpos)] ly S2 _ _ (F + 5168) 0 16 (-512) (Z_to_bv 64 0x8218c) HJ7) end.
- rewrite Ra0. cbn [sv_denot]. ga_evalE0 AG. first [reflexivity | unfold w64; f_equal; lia].
- exact Ra1.
- exact Ra2.
- lia. - lia. - lia.
- unfold spZ at 1. rewrite Rsp. ga_evalE AG.
- reflexivity. - lia. - rewrite FFS. unfold ESTACK. lia.
- rewrite Rgp. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite (AG 3%nat) by lia. rewrite (EE 3%nat 3%bv eq_refl). exact Hgp.
- rewrite Rtp. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite (AG 4%nat) by lia. rewrite (EE 4%nat 4%bv eq_refl). exact Htp.
- exact Rra.
- vm_compute. reflexivity.
- intros a Ha. split; [| unfold ESTACK; ga_zlia_k F]. right. right. right. exists 7, fpos. split; [left; reflexivity|]. left.
unfold in_zr, frame_rng. cbn [fst snd]. change (fs_frame_bytes 7) with 8192. fold F. lia.
- apply amem_range_high; [clear; lia | unfold gbox in HFhigh; destruct HFhigh as [_ HFz]; unfold kLowShadowBeg, kHighMemBeg in HFz; clear - HFz; lia | clear - HFceil; lia].
- replace (F + 5168) with (F + 8 * 646) by lia. replace 16 with (8 * 2) by lia. exact HRAcfg8.
- intros _. eapply (shadow_hull_vis_of_frame trasegs B LAWS ly S2 _ _ _ 7 fpos (F + 5168) 16 (proj1 HJ7) Hfin2);
[fold F; lia | fold F; change (fs_frame_bytes 7) with 8192; lia | lia].
- exact I. }
cbv beta. intros W8 c8 _ (-> & regs8 & mem8 & md8 & -> & HJ8 & HP8 & Ha08 & Heff8 & Hfr8 & Hpres8).
clear Ra0 Ra1 Ra2 Rra Rsp Rgp Rtp.
ga_aconsts HROD HJ8 Kgot8 Kcell8 Kguar8 Kuar8 Vgr8.
reseat HS HJ8 HP8 [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13]%nat AG
ltac:(idtac; first [ ga_keptI2 Hfr8 Hpres8 AG Kgot0 Kgot8 Kcell0 Kcell8 Kguar0 Kguar8 Kuar0 Kuar8 Vgr0 Vgr8 | match goal with |- ?g => idtac "KEPTFAIL" g end; fail ]).
clear Kgot0 Kcell0 Kguar0 Kuar0 Vgr0. rename Kgot8 into Kgot0. rename Kcell8 into Kcell0. rename Kguar8 into Kguar0. rename Kuar8 into Kuar0. rename Vgr8 into Vgr0.
destruct (al_frames _ _ LAWS _ _ _ _ _ 7 fpos (proj1 HJ8) Hfin2) as (_ & _ & HFpres8 & HFSpres8).
change (fs_frame_bytes 7) with 8192 in HFpres8, HFSpres8. fold F in HFpres8, HFSpres8.
assert (ZC : forall o (n : nat), 5168 <= o -> o + Z.of_nat n <= 5184 -> val_mem trasegs (mrestrict (w_H W) mem8) (F + o) n 0).
{ intros o n Ho1 Ho2. apply rg_val_mem_zero. intros i Hi. replace (F + o + i) with (F + 5168 + (o - 5168 + i)) by lia.
rewrite (Heff8 (o - 5168 + i) ltac:(lia)). reflexivity. }
lazymatch type of HS with st_ok _ ?Ex _ _ =>
pose proof (ast_ok_add_region trasegs Ex _ _
(YQ0b.mkRegion (Some 54%nat) 5168 5184 5168 5184
[YQ0b.mkChunk 5168 (CVal 4 (SLit 0)); YQ0b.mkChunk 5172 (CVal 4 (SLit 0)); YQ0b.mkChunk 5176 (CVal 2 (SLit 0));
YQ0b.mkChunk 5178 (CVal 2 (SLit 0)); YQ0b.mkChunk 5180 (CVal 1 (SLit 0))]) HS eq_refl
ltac:(unfold region_ok; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val ms_mem restrict mkst];
ga_evalE0 AG; split; [lia|]; split; [lia|]; split;
[ intros o Ho; apply (apresent_writable trasegs); apply (proj1 (HFpres8 (F + o) ltac:(lia)))
| repeat (apply Forall_cons; [
lazymatch goal with |- YQ0b.chunk_ok _ _ _ _ (YQ0b.mkChunk ?off (CVal ?w _)) =>
apply (chunk_ok_val trasegs Ex _ F off w _ 0); [reflexivity | zside | zside | apply ZC; cbn; lia] end |]);
apply Forall_nil ])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val];
ga_evalE0 AG; repeat split; first [ga_zlia | match goal with |- ?g => idtac "DISJ5" g; fail end])) as HS3;
clear HS; rename HS3 into HS end.
norm_ss HS.
lazymatch type of HS with st_ok _ _ ?ssx _ => first [change ssx with ss_E1 in HS | idtac "HANDOVER-MISMATCH"] end.
lazymatch goal with |- SRr _ ?W3 (mkCfg ?ms3 ?md3) _ =>
lazymatch type of HS with st_ok _ ?Ev _ _ =>
eapply (RD fx (mkRGCX ly S W regs mem md ch r cfp g wfn ctx path attr gen loops Wd Hd bef beffmt cur s N img fmt fattr fgen delay rest cid pos fpos E)
Ev 0 ly S2 W3 ms3 md3) end end.
- unfold rga_base, rgc_vals.
cbn [c_ly c_S c_W c_regs c_mem c_md c_ch c_r c_cfp c_g c_wfn c_ctx c_path c_attr c_gen c_loops c_Wd c_Hd c_bef c_beffmt c_cur c_s c_N
c_img c_fmt c_fattr c_fgen c_delay c_rest c_cid c_pos c_fpos c_E0].
gunbox. unfold RGB_SIZE.
repeat match goal with |- _ /\ _ => split end; try assumption.
all: first [ exact Hrgb | exact Hcfg | idtac ].
- unfold rga_E, rgc_vals, rga_F, rga_FL.
cbn [c_ly c_S c_W c_regs c_mem c_md c_ch c_r c_cfp c_g c_wfn c_ctx c_path c_attr c_gen c_loops c_Wd c_Hd c_bef c_beffmt c_cur c_s c_N
c_img c_fmt c_fattr c_fgen c_delay c_rest c_cid c_pos c_fpos c_E0].
split; [exact AG|]. split.
{ intros j Hj. do 18 (destruct j as [|j]; [cbn [Nat.add nth rga_vals]; first [assumption | rewrite AG by lia; assumption]|]). lia. }
split; [exact RF|]. split; [exact E66 | exact E67].
- exact Hfrm.
- unfold rgc_FPs. cbn [c_ly c_S c_W c_regs c_mem c_md c_r c_g c_s c_N c_bef c_beffmt c_fpos ms_mem]. exact HJ8.
- cbn [c_fpos c_S]. exact Hfrs2.
- unfold INV_0. cbn [c_ly c_S]. split; [split; [lia | unfold rga_bud; cbn [c_S]; eapply bud_le_mono; [eapply ajournal_bud; exact HJ8 | clear; lia ..]]|]. split; [exact Eab | exact Hbb2].
- exact HS.
Qed.
End PA.
End b.
