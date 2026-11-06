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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00 YI02 YI1i YI08 YI0c.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YC01 YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YG00 YG0a YG01 YG0h YG0u YG0d YC04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB0z YC19 YF8z YC1d YC1a YC2o YC10 YC1b YC2u
YC4u YC4z YC53.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCaq.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Definition A_GOT_rgb_addframe : Z := 0xa2df8.
Definition A_stack_malloc_7 : Z := 0x3d1d8.
Definition A_stack_free_7 : Z := 0x3d354.
Definition A_set_shadow_00 : Z := 0x54fb8.
Definition A_set_shadow_f8 : Z := 0x550d8.
Definition A_wrap_realloc : Z := 0x53108.
Definition RGA_FRAME_BYTES : Z := 5216.
Definition GBx : sv := SOff 44 0.
Definition GBspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition rga_vals (g wfn ctx path attr gen loops Wd Hd bef beffmt cur img fmt fattr fgen delay : Z) : list Z :=
[g; wfn; ctx; path; attr; gen; loops; Wd; Hd; bef; beffmt; cur; SB; img; fmt; fattr; fgen; delay].
Definition rga_extra (g wfn ctx path attr gen loops Wd Hd bef beffmt cur img fmt fattr fgen delay : Z) : list word :=
map (Z_to_bv 64) (rga_vals g wfn ctx path attr gen loops Wd Hd bef beffmt cur img fmt fattr fgen delay).
Definition rga_r_region : YQ0b.region :=
YQ0b.mkRegion (Some 10%nat) 0 64 48 64
[YQ0b.mkChunk 0 (CVal 8 (SOff 32 0)); YQ0b.mkChunk 8 (CVal 8 (SOff 33 0)); YQ0b.mkChunk 16 (CVal 8 (SOff 34 0));
YQ0b.mkChunk 24 (CVal 8 (SOff 35 0)); YQ0b.mkChunk 32 (CVal 4 (SOff 36 0)); YQ0b.mkChunk 36 (CVal 4 (SOff 37 0));
YQ0b.mkChunk 40 (CVal 2 (SOff 38 0)); YQ0b.mkChunk 42 (CVal 2 (SOff 39 0)); YQ0b.mkChunk 44 (CVal 2 (SOff 40 0));
YQ0b.mkChunk 48 (CVal 8 (SOff 41 0)); YQ0b.mkChunk 56 (CVal 4 (SOff 42 0)); YQ0b.mkChunk 60 (CVal 4 (SOff 43 0))].
Definition rga_cfg_region : YQ0b.region :=
YQ0b.mkRegion (Some 11%nat) 0 24 0 0
[YQ0b.mkChunk 0 (CVal 8 (SOff 45 0)); YQ0b.mkChunk 8 (CVal 4 (SOff 46 0)); YQ0b.mkChunk 12 (CVal 4 (SOff 47 0));
YQ0b.mkChunk 16 (CVal 4 (SOff 48 0)); YQ0b.mkChunk 20 (CVal 2 (SOff 49 0))].
Definition rga_regions0 : smem :=
[ stack_region 512; got_region; bcell_region 44; uar_got_region; uar_cell_region; const8_region A_GOT_rgb_addframe A_cgif_rgb_addframe;
rga_r_region; rga_cfg_region ].
Definition rga_atoms0 : list (nat * afact) :=
[ (2%nat, mkAF (2^46) (2^47) 5); (10%nat, HPTR 4); (11%nat, HPTR 3);
(32%nat, mkAF 0 (2^64 - 1) 0); (36%nat, mkAF 0 (2^32 - 1) 0); (37%nat, mkAF 0 (2^32 - 1) 0); (38%nat, mkAF 0 65535 0);
(39%nat, mkAF 0 65535 0); (40%nat, mkAF 0 65535 0); (41%nat, mkAF 0 (2^64 - 1) 0); (42%nat, mkAF 0 (2^32 - 1) 0); (43%nat, mkAF 0 (2^32 - 1) 0);
(44%nat, mkAF SB SB 0); (45%nat, mkAF 0 (2^64 - 1) 0); (46%nat, mkAF 0 (2^32 - 1) 0); (47%nat, mkAF 0 (2^32 - 1) 0);
(48%nat, mkAF 0 (2^32 - 1) 0); (49%nat, mkAF 0 65535 0) ].
Definition ss_rga0 : sstate := mkSS A_cgif_rgb_addframe sr_atoms rga_regions0 None (mkFacts rga_atoms0 [] []).
Section a. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section b.
Variable B : asyms.
Hypothesis TL : TraLib B.
Hypothesis LAWS : AR_laws trasegs B.
Let HBcode := tl_code B TL. Let HBgot := tl_got_shadow B TL. Let HBcell := tl_shadow_cell B TL.
Let HBguar := tl_got_uar B TL. Let HBuar := tl_uar_cell B TL.
Lemma rga_entry : forall W ly S regs mem md ch r cfp g wfn ctx path attr gen loops Wd Hd bef beffmt cur img fmt fattr fgen delay,
afn_pre trasegs B TRGBADD_STK ly S W regs mem md ch -> spZ regs mod 32 = 0 ->
arodata_ok B (aview trasegs (w_H W) mem) ->
getr regs 10 = w64 r -> getr regs 11 = w64 cfp ->
afobj B ly S W mem cfp RGBFC_SIZE ->
obj_at trasegs (mrestrict (w_H W) mem) cfp LAY_RgbFrameConfig [img; fmt; fattr; fgen; delay] ->
obj_at trasegs (mrestrict (w_H W) mem) r LAY_Rgb [g; wfn; ctx; path; attr; gen; loops; Wd; Hd; bef; beffmt; cur] ->
In (r, RGB_SIZE) (ablocks B ly S) ->
st_ok trasegs (Ereg regs (rga_extra g wfn ctx path attr gen loops Wd Hd bef beffmt cur img fmt fattr fgen delay)) ss_rga0
(restrict (w_H W) (mkst regs (Z_to_bv 64 A_cgif_rgb_addframe) mem (seg_rom trasegs))).
Proof.
intros W ly S regs mem md ch r cfp g wfn ctx path attr gen loops Wd Hd bef beffmt cur img fmt fattr fgen delay
HPRE Hal32 HROD H10 H11 HFO Hcfg Hrgb Hrin.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (FFS : TRGBADD_STK = 25088) by reflexivity.
unfold RGBFC_SIZE in HFO.
destruct HFO as ((cid & pos & Hfin & Hcid0 & Hfal & Hflo & Hfhi) & Hcal & HRA).
destruct (frames_bounds trasegs B LAWS ly S W mem md cid pos HAR Hfin) as (Hf4096 & Hfceil & Hfhigh).
pose proof (frm_off_img _ _ _ _ _ _ _ _ HAR Hfin) as Hfhigh_img.
destruct (al_blocks _ _ LAWS ly S W mem md r RGB_SIZE HAR Hrin) as (Hr16 & Hr4096 & Hrceil & [Hrh Hrapp] & Hrpres & _).
pose proof (blk_off_img _ _ _ _ _ _ r RGB_SIZE HAR Hrin) as Hrh_img.
change (req_size RGB_SIZE) with 64 in Hrceil, Hrpres, Hrh, Hrh_img.
pose proof (sep_block_frame trasegs B LAWS ly S W mem md r RGB_SIZE cid pos HAR Hrin Hfin) as HdRC.
unfold zdisjoint in HdRC. cbn [fst snd] in HdRC. change (req_size RGB_SIZE) with 64 in HdRC.
destruct (al_const _ _ LAWS ly S W mem md HAR) as (Kcell & Kuar & Kgot & Kguar).
rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell. rewrite HBguar, HBuar in Kguar. rewrite HBuar in Kuar.
pose proof Hcfg as Hcfg'. cbn [obj_at LAY_RgbFrameConfig] in Hcfg'.
destruct Hcfg' as ([C0 CR0] & [C8 CR8] & [C12 CR12] & [C16 CR16] & [C20 CR20] & _).
cbn [fst snd N.to_nat Z.of_N] in C0, C8, C12, C16, C20, CR0, CR8, CR12, CR16, CR20.
pose proof Hrgb as Hrgb'. cbn [obj_at LAY_Rgb] in Hrgb'.
destruct Hrgb' as ([V0 R0v] & [V8 R8v] & [V16 R16v] & [V24 R24v] & [V32 R32v] & [V36 R36v] & [V40 R40v] & [V42 R42v] & [V44 R44v] & [V48 R48v] & [V56 R56v] & [V60 R60v] & _).
cbn [fst snd N.to_nat Z.of_N] in V0, V8, V16, V24, V32, V36, V40, V42, V44, V48, V56, V60, R0v, R8v, R16v, R24v, R32v, R36v, R40v, R42v, R44v, R48v, R56v, R60v.
change (2 ^ (8 * 8)) with (2 ^ 64) in *. change (2 ^ (8 * 4)) with (2 ^ 32) in *. change (2 ^ (8 * 2)) with 65536 in *.
rewrite restrict_mkst_fx.
set (E := Ereg regs (rga_extra g wfn ctx path attr gen loops Wd Hd bef beffmt cur img fmt fattr fgen delay)).
assert (E2 : ew E 2 = getr regs 2) by (subst E; exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 r) by (subst E; rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E11 : ew E 11 = Z_to_bv 64 cfp) by (subst E; rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (EX : forall j, ew E (32 + j) = nth j (rga_extra g wfn ctx path attr gen loops Wd Hd bef beffmt cur img fmt fattr fgen delay) (Z_to_bv 64 0))
by (intros j; subst E; apply ew_Ereg_extra).
pose proof (EX 0%nat) as E32. pose proof (EX 1%nat) as E33. pose proof (EX 2%nat) as E34. pose proof (EX 3%nat) as E35.
pose proof (EX 4%nat) as E36. pose proof (EX 5%nat) as E37. pose proof (EX 6%nat) as E38. pose proof (EX 7%nat) as E39.
pose proof (EX 8%nat) as E40. pose proof (EX 9%nat) as E41. pose proof (EX 10%nat) as E42. pose proof (EX 11%nat) as E43.
pose proof (EX 12%nat) as E44. pose proof (EX 13%nat) as E45. pose proof (EX 14%nat) as E46. pose proof (EX 15%nat) as E47.
pose proof (EX 16%nat) as E48. pose proof (EX 17%nat) as E49.
cbn [Nat.add nth rga_extra rga_vals map] in E32, E33, E34, E35, E36, E37, E38, E39, E40, E41, E42, E43, E44, E45, E46, E47, E48, E49. clear EX.
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
Local Ltac ck HE M := eapply chunk_ok_val; [ cbn [sv_denot]; rewrite HE, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | first [exact M | rewrite Z.add_0_r; exact M] ].
unfold ss_rga0. apply (entry_st_ok_full trasegs);
change (Ereg regs (rga_extra g wfn ctx path attr gen loops Wd Hd bef beffmt cur img fmt fattr fgen delay)) with E.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- unfold rga_regions0, stack_region, got_region, bcell_region, uar_got_region, uar_cell_region, const8_region, rga_r_region, rga_cfg_region.
repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks].
+ cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
intros o Ho. apply (apresent_writable trasegs). apply Hpres. lia.
+ cbn [base_val]. unfold A_GOT_shadow. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor]. rewrite <- (Z.add_0_l 663904) at 1.
apply (chunk_ok_val trasegs E _ 0 663904 8 (SLit A_shadow_glob) A_shadow_glob); [reflexivity | unfold A_shadow_glob; zside | zside |].
exact (val_mem_of_rdword trasegs (w_H W) mem _ _ Kgot).
+ cbn [base_val]. unfold A_shadow_glob. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor]. rewrite <- (Z.add_0_l 696760) at 1.
apply (chunk_ok_val trasegs E _ 0 696760 8 (SOff 44 0) SB);
[cbn [sv_denot]; rewrite E44, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | zside |].
exact (val_mem_of_rdword trasegs (w_H W) mem _ _ Kcell).
+ cbn [base_val]. unfold A_GOT_uar. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor]. rewrite <- (Z.add_0_l 663992) at 1.
apply (chunk_ok_val trasegs E _ 0 663992 8 (SLit A_uar_glob) A_uar_glob); [reflexivity | unfold A_uar_glob; zside | zside |].
exact (val_mem_of_rdword trasegs (w_H W) mem _ _ Kguar).
+ cbn [base_val]. unfold A_uar_glob. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor]. rewrite <- (Z.add_0_l 696768) at 1.
apply (chunk_ok_val trasegs E _ 0 696768 4 (SLit 1) 1); [reflexivity | zside | zside |].
exact (val_mem_of_rd32 trasegs (w_H W) mem _ _ Kuar).
+ cbn [base_val]. unfold A_GOT_rgb_addframe. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor]. rewrite <- (Z.add_0_l 667128) at 1.
apply (chunk_ok_val trasegs E _ 0 667128 8 (SLit A_cgif_rgb_addframe) A_cgif_rgb_addframe); [reflexivity | unfold A_cgif_rgb_addframe; zside | zside |].
eapply (arodata_val8 B (w_H W) mem 667128 A_cgif_rgb_addframe TL HROD); [lia | lia | intros x Hx; unfold lib_const_addr; lia |].
intros k Hk. do 8 (destruct k as [|k]; [vm_compute; reflexivity|]). lia.
+ rewrite (VB 10%nat r E10) by lia. split; [lia|]. split; [lia|].
split; [intros o Ho; apply (apresent_writable trasegs); apply Hrpres; lia|].
constructor; [ck E32 V0|]. constructor; [ck E33 V8|]. constructor; [ck E34 V16|]. constructor; [ck E35 V24|].
constructor; [ck E36 V32|]. constructor; [ck E37 V36|]. constructor; [ck E38 V40|]. constructor; [ck E39 V42|].
constructor; [ck E40 V44|]. constructor; [ck E41 V48|]. constructor; [ck E42 V56|]. constructor; [ck E43 V60|]. constructor.
+ rewrite (VB 11%nat cfp E11) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [ck E45 C0|]. constructor; [ck E46 C8|]. constructor; [ck E47 C12|]. constructor; [ck E48 C16|].
constructor; [ck E49 C20|]. constructor.
- apply pairwise_disjoint_of_extents.
unfold rga_regions0, stack_region, got_region, bcell_region, uar_got_region, uar_cell_region, const8_region, rga_r_region, rga_cfg_region, extent_of_region.
cbn [map YQ0b.r_base YQ0b.r_lo YQ0b.r_hi]. rewrite (VB 10%nat r E10), (VB 11%nat cfp E11) by lia. cbn [base_val]. rewrite Usp.
unfold A_GOT_shadow, A_shadow_glob, A_GOT_uar, A_uar_glob, A_GOT_rgb_addframe.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
revert Hslo Hshi H47 Hceil Hfceil Hfhigh Hfhigh_img Hflo Hfhi Hr4096 Hrceil Hrh Hrh_img HdRC C1 C3 FFS Hstk0. clear.
unfold zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kLowShadowBeg, kHighMemBeg. intros. repeat split; lia.
- split; [|split; [exact I | exact I]].
cbn [f_atoms atoms_ok rga_atoms0]. unfold afact_ok, HPTR. cbn [af_lo af_hi af_al2].
rewrite Usp, E10, E11, E32, E36, E37, E38, E39, E40, E41, E42, E43, E44, E45, E46, E47, E48, E49, !unsigned_lit_small by (unfold SB; lia).
change (2 ^ 5) with 32. change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
assert (Hc8 : cfp mod 8 = 0) by exact Hcal.
revert Hslo Hshi H47 Hceil Hfceil Hfhigh Hflo Hfhi Hal32 Hc8 Hr16 Hr4096 Hrceil Hrh R0v R32v R36v R40v R42v R44v R48v R56v R60v CR0 CR8 CR12 CR16 CR20 C1 C3 FFS Hstk0. clear.
unfold SB, zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kLowShadowBeg, kHighMemBeg. intros.
repeat match goal with |- _ /\ _ => split end; lia.
Qed.
End b.
End a.
