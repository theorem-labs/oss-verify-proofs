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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00 YI02 YI1i YI08.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YC01 YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YG00 YG0a YG01 YG0h YG0u YG0d YC04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB0z YC19 YF8z YC1d YC1a YC2o YC10 YC1b YC2u
YC4u YC4z YC52.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Definition A_GOT_rgb_newgif : Z := 0xa2df0.
Definition A_stack_malloc_1 : Z := 0x3ceac.
Definition A_wrap_free : Z := 0x53100.
Definition A_asan_memcpy : Z := 0x51db0.
Definition RBx : sv := SOff 35 0.
Definition RBspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition rng_extra (attr gen loops Wd Hd : Z) : list word := map (Z_to_bv 64) [attr; gen; loops; SB; Wd; Hd].
Definition rcfg_region : YQ0b.region :=
YQ0b.mkRegion (Some 10%nat) 0 40 0 0
[YQ0b.mkChunk 0 (CVal 8 (SLit A_writecb)); YQ0b.mkChunk 8 (CVal 8 (SLit 0)); YQ0b.mkChunk 16 (CVal 8 (SLit 0));
YQ0b.mkChunk 24 (CVal 4 (SOff 32 0)); YQ0b.mkChunk 28 (CVal 4 (SOff 33 0));
YQ0b.mkChunk 32 (CVal 2 (SOff 34 0)); YQ0b.mkChunk 34 (CVal 2 (SOff 36 0)); YQ0b.mkChunk 36 (CVal 2 (SOff 37 0))].
Definition rng_regions0 : smem :=
[ stack_region 96; got_region; bcell_region 35; uar_got_region; uar_cell_region; const8_region A_GOT_rgb_newgif A_cgif_rgb_newgif;
rcfg_region ].
Definition rng_atoms0 : list (nat * afact) :=
[ (2%nat, mkAF (2^46) (2^47) 5); (10%nat, HPTR 3); (32%nat, mkAF 0 (2^32 - 1) 0); (33%nat, mkAF 0 (2^32 - 1) 0);
(34%nat, mkAF 0 65535 0); (35%nat, mkAF SB SB 0); (36%nat, mkAF 0 65535 0); (37%nat, mkAF 0 65535 0) ].
Definition ss_rng0 : sstate := mkSS A_cgif_rgb_newgif sr_atoms rng_regions0 None (mkFacts rng_atoms0 [] []).
Section a. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section b.
Variable B : asyms.
Hypothesis TL : TraLib B.
Hypothesis LAWS : AR_laws trasegs B.
Let HBcode := tl_code B TL. Let HBgot := tl_got_shadow B TL. Let HBcell := tl_shadow_cell B TL.
Let HBguar := tl_got_uar B TL. Let HBuar := tl_uar_cell B TL.
Lemma rng_entry : forall W ly S regs mem md ch cfgp attr gen loops Wd Hd,
afn_pre trasegs B TRGBNEWGIF_STK ly S W regs mem md ch -> spZ regs mod 32 = 0 ->
arodata_ok B (aview trasegs (w_H W) mem) ->
getr regs 10 = w64 cfgp ->
afobj B ly S W mem cfgp RGBCONFIG_SIZE ->
obj_at trasegs (mrestrict (w_H W) mem) cfgp LAY_RgbConfig [A_writecb; 0; 0; attr; gen; loops; Wd; Hd] ->
st_ok trasegs (Ereg regs (rng_extra attr gen loops Wd Hd)) ss_rng0
(restrict (w_H W) (mkst regs (Z_to_bv 64 A_cgif_rgb_newgif) mem (seg_rom trasegs))).
Proof.
intros W ly S regs mem md ch cfgp attr gen loops Wd Hd HPRE Hal32 HROD H10 HFO Hcfg.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (FFS : TRGBNEWGIF_STK = 16864) by reflexivity.
unfold RGBCONFIG_SIZE in HFO.
destruct HFO as ((cid & pos & Hfin & Hcid0 & Hfal & Hflo & Hfhi) & Hcal & HRA).
destruct (frames_bounds trasegs B LAWS ly S W mem md cid pos HAR Hfin) as (Hf4096 & Hfceil & Hfhigh).
pose proof (frm_off_img _ _ _ _ _ _ _ _ HAR Hfin) as Hfhigh_img.
destruct (al_const _ _ LAWS ly S W mem md HAR) as (Kcell & Kuar & Kgot & Kguar).
rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell. rewrite HBguar, HBuar in Kguar. rewrite HBuar in Kuar.
pose proof Hcfg as Hcfg'. cbn [obj_at LAY_RgbConfig] in Hcfg'.
destruct Hcfg' as ([V0 _] & [V8 _] & [V16 _] & [V24 R24] & [V28 R28] & [V32 R32] & [V34 R34] & [V36 R36] & _).
cbn [fst snd N.to_nat Z.of_N] in V0, V8, V16, V24, V28, V32, V34, V36, R24, R28, R32, R34, R36.
change (2 ^ (8 * 4)) with (2 ^ 32) in *. change (2 ^ (8 * 2)) with 65536 in *.
rewrite restrict_mkst_fx.
set (E := Ereg regs (rng_extra attr gen loops Wd Hd)).
assert (E2 : ew E 2 = getr regs 2) by (subst E; exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 cfgp) by (subst E; rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (EX : forall j, ew E (32 + j) = nth j (rng_extra attr gen loops Wd Hd) (Z_to_bv 64 0)) by (intros j; subst E; apply ew_Ereg_extra).
pose proof (EX 0%nat) as E32. pose proof (EX 1%nat) as E33. pose proof (EX 2%nat) as E34. pose proof (EX 3%nat) as E35.
pose proof (EX 4%nat) as E36. pose proof (EX 5%nat) as E37.
cbn [Nat.add nth rng_extra map] in E32, E33, E34, E35, E36, E37. clear EX.
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
Local Ltac ck HE M := eapply chunk_ok_val; [ cbn [sv_denot]; rewrite HE, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | first [exact M | rewrite Z.add_0_r; exact M] ].
unfold ss_rng0. apply (entry_st_ok_full trasegs); change (Ereg regs (rng_extra attr gen loops Wd Hd)) with E.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- unfold rng_regions0, stack_region, got_region, bcell_region, uar_got_region, uar_cell_region, const8_region, rcfg_region.
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
apply (chunk_ok_val trasegs E _ 0 696760 8 (SOff 35 0) SB);
[cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | zside |].
exact (val_mem_of_rdword trasegs (w_H W) mem _ _ Kcell).
+ cbn [base_val]. unfold A_GOT_uar. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor]. rewrite <- (Z.add_0_l 663992) at 1.
apply (chunk_ok_val trasegs E _ 0 663992 8 (SLit A_uar_glob) A_uar_glob); [reflexivity | unfold A_uar_glob; zside | zside |].
exact (val_mem_of_rdword trasegs (w_H W) mem _ _ Kguar).
+ cbn [base_val]. unfold A_uar_glob. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor]. rewrite <- (Z.add_0_l 696768) at 1.
apply (chunk_ok_val trasegs E _ 0 696768 4 (SLit 1) 1); [reflexivity | zside | zside |].
exact (val_mem_of_rd32 trasegs (w_H W) mem _ _ Kuar).
+ cbn [base_val]. unfold A_GOT_rgb_newgif. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor]. rewrite <- (Z.add_0_l 667120) at 1.
apply (chunk_ok_val trasegs E _ 0 667120 8 (SLit A_cgif_rgb_newgif) A_cgif_rgb_newgif); [reflexivity | unfold A_cgif_rgb_newgif; zside | zside |].
eapply (arodata_val8 B (w_H W) mem 667120 A_cgif_rgb_newgif TL HROD); [lia | lia | intros x Hx; unfold lib_const_addr; lia |].
intros k Hk. do 8 (destruct k as [|k]; [vm_compute; reflexivity|]). lia.
+ rewrite (VB 10%nat cfgp E10) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [apply (chunk_ok_val trasegs E _ cfgp 0 8 _ A_writecb); [reflexivity | unfold A_writecb; zside | zside | exact V0]|].
constructor; [apply (chunk_ok_val trasegs E _ cfgp 8 8 _ 0); [reflexivity | zside | zside | exact V8]|].
constructor; [apply (chunk_ok_val trasegs E _ cfgp 16 8 _ 0); [reflexivity | zside | zside | exact V16]|].
constructor; [ck E32 V24|]. constructor; [ck E33 V28|]. constructor; [ck E34 V32|].
constructor; [ck E36 V34|]. constructor; [ck E37 V36|]. constructor.
- apply pairwise_disjoint_of_extents.
unfold rng_regions0, stack_region, got_region, bcell_region, uar_got_region, uar_cell_region, const8_region, rcfg_region, extent_of_region.
cbn [map YQ0b.r_base YQ0b.r_lo YQ0b.r_hi]. rewrite (VB 10%nat cfgp E10) by lia. cbn [base_val]. rewrite Usp.
unfold A_GOT_shadow, A_shadow_glob, A_GOT_uar, A_uar_glob, A_GOT_rgb_newgif.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
revert Hslo Hshi H47 Hceil Hfceil Hfhigh Hfhigh_img Hflo Hfhi C1 C3 FFS Hstk0. clear. unfold zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kLowShadowBeg, kHighMemBeg. intros. repeat split; lia.
- split; [|split; [exact I | exact I]].
cbn [f_atoms atoms_ok rng_atoms0]. unfold afact_ok, HPTR. cbn [af_lo af_hi af_al2].
rewrite Usp, E10, E32, E33, E34, E35, E36, E37, !unsigned_lit_small by (unfold SB; lia).
change (2 ^ 5) with 32. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
assert (Hc8 : cfgp mod 8 = 0) by exact Hcal.
revert Hslo Hshi H47 Hceil Hfceil Hfhigh Hflo Hfhi Hal32 Hc8 R24 R28 R32 R34 R36 C1 C3 FFS Hstk0. clear. unfold SB, zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kLowShadowBeg, kHighMemBeg. intros.
repeat match goal with |- _ /\ _ => split end; lia.
Qed.
End b.
End a.
