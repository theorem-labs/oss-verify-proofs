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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00 YI02.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YC01 YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YG00 YG0a YG01 YG0h YG0u YG0d YCcz.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB1u YCe7 YF9i YCeb YCe8 YCe9 YCi1 YCib.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YI1i YI08.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section e.
Variable B : asyms.
Hypothesis TL : TrbLib B.
Hypothesis LAWS : AR_laws trbsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis AFREE : afree_realizes trbsegs B.
Hypothesis TCLOSE : tclose_spec B.
Let HBcode := tl_code B TL. Let HBgot := tl_got_shadow B TL. Let HBcell := tl_shadow_cell B TL. Let errno_low := tl_env B TL.
Local Abbreviation code := (as_code B).
Definition Bx : sv := SOff 35 0.
Definition rgc_regions : smem :=
[ stack_region 32; got_region; bcell_region 35;
YQ0b.mkRegion (Some 10%nat) 0 RGB_SIZE 0 0
[YQ0b.mkChunk 0 (CVal 8 (SOff 32 0)); YQ0b.mkChunk 48 (CVal 8 (SOff 33 0))] ].
Definition rgc_facts : facts :=
mkFacts [ (2%nat, mkAF (2^46) (2^47) 4); (10%nat, mkAF 4096 140737479966720 4);
(32%nat, mkAF 0 (2^64 - 1) 0); (33%nat, mkAF 0 (2^64 - 1) 0); (35%nat, mkAF SB SB 0) ] [] [].
Definition ss_rgc : sstate := mkSS A_cgif_rgb_close sr_atoms rgc_regions None rgc_facts.
Definition rgc_SH : list shent := [ mkSHE 10 0 RGB_SIZE ].
Definition Bspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition rgc_extra (g bef : Z) : list word := map (Z_to_bv 64) [g; bef; 0; SB].
Lemma rgc_entry : forall W ly S regs mem md ch r g bef rest,
afn_pre trbsegs B TRGBCLOSE_STK ly S W regs mem md ch ->
getr regs 10 = w64 r ->
Permutation (ablocks B ly S) ((r, RGB_SIZE) :: rest) ->
val_mem trbsegs (mrestrict (w_H W) mem) r 8 g -> 0 <= g < 2 ^ 64 ->
val_mem trbsegs (mrestrict (w_H W) mem) (r + 48) 8 bef -> 0 <= bef < 2 ^ 64 ->
st_ok trbsegs (Ereg regs (rgc_extra g bef)) ss_rgc
(restrict (w_H W) (mkst regs (Z_to_bv 64 A_cgif_rgb_close) mem (seg_rom trbsegs)))
/\ sh_ok trbsegs Bx rgc_SH (Ereg regs (rgc_extra g bef)) (mrestrict (w_H W) mem).
Proof.
intros W ly S regs mem md ch r g bef rest HPRE H10 HPerm Mg Rg Mbef Rbef.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (FFS : TRGBCLOSE_STK = 17552) by reflexivity.
assert (Hinr : In (r, RGB_SIZE) (ablocks B ly S)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm|]. left. reflexivity. }
destruct (al_blocks _ _ LAWS ly S W mem md r RGB_SIZE HAR Hinr) as (Hr16 & Hr4096 & Hrceil & Hrh_ia & _ & _). pose proof (proj1 Hrh_ia) as Hrh.
pose proof (blk_off_img _ _ _ _ _ _ r RGB_SIZE HAR Hinr) as Hrh_img.
change (req_size RGB_SIZE) with 64 in *.
destruct (al_const _ _ LAWS ly S W mem md HAR) as (Kcell & _ & Kgot & _). rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
rewrite restrict_mkst_fx.
set (E := Ereg regs (rgc_extra g bef)).
assert (E2 : ew E 2 = getr regs 2) by (subst E; exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 r) by (subst E; rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (EX : forall j, ew E (32 + j) = nth j (rgc_extra g bef) (Z_to_bv 64 0)) by (intros j; subst E; apply ew_Ereg_extra).
pose proof (EX 0%nat) as E32. pose proof (EX 1%nat) as E33. pose proof (EX 3%nat) as E35.
cbn [Nat.add nth rgc_extra map] in E32, E33, E35. clear EX.
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
split.
- unfold ss_rgc. apply (entry_st_ok_full trbsegs); change (Ereg regs (rgc_extra g bef)) with E.
+ apply regs_ok_Ereg.
+ vm_compute. reflexivity.
+ unfold rgc_regions, stack_region, got_region, bcell_region.
repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks].
* cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
intros o Ho. apply (apresent_writable trbsegs). apply Hpres. lia.
* cbn [base_val]. unfold A_GOT_shadow. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor]. rewrite <- (Z.add_0_l 668240) at 1.
apply (chunk_ok_val trbsegs E _ 0 668240 8 (SLit A_shadow_glob) A_shadow_glob); [reflexivity | unfold A_shadow_glob; zside | zside |].
exact (val_mem_of_rdword trbsegs (w_H W) mem _ _ Kgot).
* cbn [base_val]. unfold A_shadow_glob. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor]. rewrite <- (Z.add_0_l 701048) at 1.
apply (chunk_ok_val trbsegs E _ 0 701048 8 Bx SB);
[cbn [sv_denot Bx]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | zside |].
exact (val_mem_of_rdword trbsegs (w_H W) mem _ _ Kcell).
* rewrite (VB 10%nat r E10) by lia. unfold RGB_SIZE. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor; [|constructor]].
-- apply (chunk_ok_val trbsegs E _ r 0 8 _ g); [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | rewrite Z.add_0_r; exact Mg].
-- apply (chunk_ok_val trbsegs E _ r 48 8 _ bef); [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Mbef].
+ apply pairwise_disjoint_of_extents. unfold rgc_regions, stack_region, got_region, bcell_region, extent_of_region.
cbn [map YQ0b.r_base YQ0b.r_lo YQ0b.r_hi]. rewrite (VB 10%nat r E10) by lia. cbn [base_val]. rewrite Usp.
unfold A_GOT_shadow, A_shadow_glob, RGB_SIZE.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
revert Hslo Hshi H47 Hceil Hrceil Hrh Hrh_img Hr4096 C1 C3 FFS Hstk0. clear. unfold zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kLowShadowBeg, kHighMemBeg. intros. repeat split; lia.
+ split; [|split; [exact I | exact I]].
cbn [rgc_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite Usp, E10, E32, E33, E35, !unsigned_lit_small by (unfold SB; lia).
change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
revert Hslo Hshi H47 Hceil Hrceil Hrh Hrh_img Hr4096 Hr16 Hal16 Rg Rbef C1 C3 FFS Hstk0. clear. unfold SB, zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kLowShadowBeg, kHighMemBeg. intros.
repeat match goal with |- _ /\ _ => split end; lia.
- unfold sh_ok, rgc_SH. constructor; [|constructor].
apply (shent_ok_of_block trbsegs B LAWS ly S W mem md E Bx 10 r RGB_SIZE 0 RGB_SIZE HAR Hinr).
* unfold U, Bx. cbn [sv_denot]. rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
* unfold U. cbn [sv_denot]. rewrite E10, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by lia. reflexivity.
* lia.
* change (req_size RGB_SIZE) with 64. unfold RGB_SIZE. lia.
Qed.
Theorem trb_cgif_rgb_close : trgb_close_spec B.
Proof.
unfold trgb_close_spec.
intros ly S W regs mem md ch r g s N bef nbef rest HPRE HCTX Hfrs HROD H10 Mg Mbef Rbef Hat Hwf HPerm Hev Hlive.
pose proof Hwx_tfa as Hwx. pose proof trb_segs_low as Hsegs.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5). assert (FFS : TRGBCLOSE_STK = 17552) by reflexivity.
assert (Hing : In (g, CGIF_SIZE) (ablocks B ly S)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm|]. right. left. reflexivity. }
assert (Hinr : In (r, RGB_SIZE) (ablocks B ly S)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm|]. left. reflexivity. }
destruct (al_blocks _ _ LAWS ly S W mem md g CGIF_SIZE HAR Hing) as (Hg16 & Hg4096 & Hgceil & Hgh_ia & _ & _).
assert (Rg : 0 <= g < 2 ^ 64) by (clear - Hg4096 Hgceil C1; change (req_size CGIF_SIZE) with 96 in Hgceil; lia).
destruct (rgc_entry W ly S regs mem md ch r g bef _ HPRE H10 HPerm Mg Rg Mbef Rbef) as [HS SHOK].
pose proof (ajournal_init trbsegs B TRGBCLOSE_STK (ablocks_fp ((r, RGB_SIZE) :: cgif_blocks g s N ++ optb bef nbef)) ly S W regs mem md ch HPRE) as HJ.
remember (Ereg regs (rgc_extra g bef)) as E eqn:HE.
assert (E1 : ew E 1 = getr regs 1) by (subst E; exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (subst E; exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E3 : ew E 3 = getr regs 3) by (subst E; exact (ew_Ereg_nat regs _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regs 4) by (subst E; exact (ew_Ereg_nat regs _ 4 4%bv eq_refl)).
assert (E8 : ew E 8 = getr regs 8) by (subst E; exact (ew_Ereg_nat regs _ 8 8%bv eq_refl)).
assert (E9 : ew E 9 = getr regs 9) by (subst E; exact (ew_Ereg_nat regs _ 9 9%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 r) by (subst E; rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E32 : ew E 32 = Z_to_bv 64 g) by (subst E; exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 bef) by (subst E; exact (ew_Ereg_extra regs _ 1)).
assert (E35 : ew E 35 = Z_to_bv 64 SB) by (subst E; exact (ew_Ereg_extra regs _ 3)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (HAE : env_agree 32 (Ereg regs (rgc_extra g bef)) E) by (rewrite HE; split; [intros n Hn; reflexivity | reflexivity]).
clear HE.
unfold cfg_at. change (w64 A_cgif_rgb_close) with (Z_to_bv 64 A_cgif_rgb_close).
aj_run_to_tok trbtbl_lib_ok HS HJ SHOK Bspan A_cgif_close. { awr_ok_tac; exact Usp. }
pose proof (proj1 HJ) as HARc.
assert (Hcg : forall x, In x (cgif_blocks g s N) -> In x (ablocks B ly S)).
{ intros x Hx. eapply Permutation_in; [apply Permutation_sym; exact HPerm|]. right. apply in_app_iff. left. exact Hx. }
assert (KA : forall b sz, In (b, sz) (cgif_blocks g s N) -> rg_blk_kept (w_H W) (w_H W) mem (ms_mem ms) b (req_size sz)).
{ intros b sz Hb. pose proof (Hcg _ Hb) as Hbx.
destruct (al_blocks _ _ LAWS ly S W mem md b sz HAR Hbx) as (_ & Hb4096 & Hbceil & _).
apply (rg_blk_kept_frame E _ (w_H W) mem (ms_mem ms) b (req_size sz) HFr).
intros a Ha. split; [clear - Ha Hb4096 Hbceil C1; lia|].
intros (rr & Hin & Hr). cbn [ss_mem ss_rgc rgc_regions] in Hin.
unfold stack_region, got_region, bcell_region in Hin. cbn [In] in Hin.
destruct Hin as [<- | [<- | [<- | [<- | []]]]]; unfold stack_region, got_region, bcell_region in Hr;
cbn [YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi base_val] in Hr; try rewrite Usp in Hr;
clear - Hr Ha Hbceil Hceil Hslo Hstk0 FFS; lia. }
pose proof (rg_tcgif_at_blocks_kept (w_H W) (w_H W) mem (ms_mem ms) g s N Hat KA) as Hat1.
destruct (al_blocks _ _ LAWS ly S W mem md r RGB_SIZE HAR Hinr) as (Hr16 & Hr4096 & Hrceil & Hrh_ia & _ & _).
change (req_size RGB_SIZE) with 64 in Hrceil.
lazymatch goal with |- SRr _ _ (mkCfg ?ms ?mdc) _ =>
lazymatch type of HS with st_ok _ _ ?ssX _ =>
rreg HS (2%bv : bv 5) R2; rreg HS (10%bv : bv 5) R10; rreg HS (3%bv : bv 5) R3; rreg HS (4%bv : bv 5) R4;
rreg HS (1%bv : bv 5) R1; rreg HS (8%bv : bv 5) R8;
eapply SRr_bind;
[ eapply (aj_call trbsegs B LAWS Hsegs W E ssX ms TRGBCLOSE_STK (spZ regs) _ ly S W mem md [] ly S mdc 0
TCLOSE_STK (ablocks_fp (cgif_blocks g s N)) EV_CLOSE (-32) (ew E 2) (Z_to_bv 64 0x85038) []
(fun ly2 S2 W2 regs2 mem2 md2 => Permutation (ablocks B ly2 S2) ((r, RGB_SIZE) :: optb bef nbef ++ rest)) HS eq_refl HJ);
[ first [ exact (st_ok_restrict_reg trbsegs (w_H W) E _ _ 2%bv HS) | match goal with |- ?gg => idtac "AJ1" gg end ]
| first [ reflexivity | idtac "AJ2" ]
| first [ exact Usp | idtac "AJ3" ]
| first [ reflexivity | idtac "AJ4" ]
| first [ lia | idtac "AJ5" ]
| first [ apply Zle_bool_imp_le; vm_compute; reflexivity | idtac "AJ6" ]
| first [ unfold TRGBCLOSE_STK; lia | match goal with |- ?gg => idtac "AJ7" gg end ]
| first [ rewrite R3, E3; exact Hgp | idtac "AJ8" ]
| first [ rewrite R4, E4; exact Htp | idtac "AJ9" ]
| first [ exact R1 | match goal with |- ?gg => idtac "AJ10" gg end ]
| first [ vm_compute; reflexivity | apply ret_ok_even; vm_compute; reflexivity | match goal with |- ?gg => idtac "AJ11" gg end ]
| first [ rewrite unsigned_lit_small by (clear; lia); clear; lia | idtac "AJ12" ]
| first [ apply achain_low; unfold s0Z; rewrite R8, E10, unsigned_lit_small by (clear - Hr4096 Hrceil C1; lia); clear - Hrceil; lia | match goal with |- ?gg => idtac "AJ13" gg end ]
| intros HPRE1; eapply SRr_mono;
[ pose proof (TCLOSE ly S W (ms_regs ms) (ms_mem ms) mdc [] g s N ((r, RGB_SIZE) :: optb bef nbef ++ rest) HPRE1) as CALL;
unfold cfg_at, apost_base in CALL; cbn [ss_pc]; change (w64 A_cgif_close) with (Z_to_bv 64 559924) in CALL;
apply CALL; clear CALL;
[ first [ unfold raZ; rewrite R1; cbn [spine map]; rewrite unsigned_lit_small by (clear; lia); vm_compute; tauto | match goal with |- ?gg => idtac "CA2" gg end ]
| first [ exact Hfrs | idtac "CA3" ]
| first [ eapply arodata_ok_journal; [exact HJ | exact HROD] | match goal with |- ?gg => idtac "CA4" gg end ]
| first [ rewrite R10, E32; reflexivity | match goal with |- ?gg => idtac "CA5" gg end ]
| first [ exact Hat1 | match goal with |- ?gg => idtac "CA9" gg end ]
| first [ exact Hwf | idtac "CA10" ]
| first [ eapply Permutation_trans; [exact HPerm|]; apply Permutation_middle | match goal with |- ?gg => idtac "CA12" gg end ]
| first [ unfold EV_RGBCLOSE in Hev; clear - Hev; lia | match goal with |- ?gg => idtac "CA21" gg end ]
| first [ exact Hlive | idtac "CA22" ] ]
| cbv beta; intros W4 c4 _ (ly4 & S4 & regs4 & mem4 & md4 & -> & HJc & HPc & Hpost);
exists ly4, S4, regs4, mem4, md4; split; [rewrite R1; reflexivity|]; split; [exact HJc|];
split; [exact HPc|]; exact Hpost ]
| first [ intros a Ha; left; split;
[ destruct (inFP_ablocks_fp_inv _ a Ha) as (pb & nb & Hpb & Hab); replace a with (pb + (a - pb)) by (clear; lia);
apply (inFP_ablocks_fp _ pb nb (a - pb)); [right; apply in_app_iff; left; exact Hpb | clear - Hab; lia]
| destruct (inFP_ablocks_fp_inv _ a Ha) as (pb & nb & Hpb & Hab); exists pb, nb; split; [exact (Hcg _ Hpb) | exact Hab] ]
| match goal with |- ?g => idtac "AJ15" g end ] ]
| ] end end.
clear HJ SHOK R2 R10 R3 R4 R1 R8.
cbv beta. intros W2 c2 Hwle2 (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ & HJc & HP2 & HPerm2).
replace (spZ regs + -32) with (spZ regs - 32) in HJc by (clear; lia).
pose proof (proj1 HJ) as HAR2.
destruct (al_const _ _ LAWS _ _ _ _ _ HARc) as (Kcell & _ & Kgot & _). rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
destruct (al_const _ _ LAWS _ _ _ _ _ HAR2) as (Kcell2 & _ & Kgot2 & _). rewrite HBgot, HBcell in Kgot2. rewrite HBcell in Kcell2.
assert (Hinr2 : In (r, RGB_SIZE) (ablocks B ly2 S2)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm2|]. left. reflexivity. }
jafter_call_keep HS 36%nat regs2 (mrestrict (w_H W2) mem2) HP2 [0; 1; 2; 3]%nat HS2.
match type of HS2 with ?t -> _ => assert (HRK : t); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; [| | | | apply Forall_nil].
- eapply (region_kept_stack_sub trbsegs B); [exact HJc | exact HJ | exact Usp | clear; lia | rewrite FFS; clear; lia | clear; lia | clear; lia | clear; lia].
- apply (region_kept_val trbsegs E _ _ A_GOT_shadow 8 A_shadow_glob);
[exact (val_mem_of_rdword trbsegs _ _ _ _ Kgot) | exact (val_mem_of_rdword trbsegs _ _ _ _ Kgot2) | lia].
- apply (region_kept_val trbsegs E _ _ A_shadow_glob 8 SHADOW_OFF);
[exact (val_mem_of_rdword trbsegs _ _ _ _ Kcell) | exact (val_mem_of_rdword trbsegs _ _ _ _ Kcell2) | lia].
- eapply (region_kept_block_sub trbsegs B); [exact HJc | rewrite E10; apply unsigned_lit_small; clear - Hr4096 Hrceil C1; lia | exact Hinr | exact Hinr2
| clear; lia | change (req_size RGB_SIZE) with 64; unfold RGB_SIZE; clear; lia | clear; lia | ].
intros a Ha Hin. destruct (inFP_ablocks_fp_inv _ a Hin) as (pb & nb & Hpb & Hab).
pose proof (rg_sep_head_in B LAWS ly S W mem md (r, RGB_SIZE) _ (pb, nb) HAR HPerm ltac:(apply in_app_iff; left; exact Hpb)) as Hd.
unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd. change (req_size RGB_SIZE) with 64 in Hd. clear - Hd Ha Hab. lia. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E 36 (map (getr regs2) CLOB)) as E2' eqn:HE2' in HS.
assert (OLD2 : forall n, (n < 36)%nat -> ew E2' n = ew E n) by (intros n Hn; rewrite HE2'; apply YO3v.ew_havoc_old; exact Hn).
assert (HAE2 : env_agree 32 (Ereg regs (rgc_extra g bef)) E2') by (rewrite HE2'; apply env_agree_havoc_ge; [cbv; lia | exact HAE]).
clear HE2'.
assert (F1 : ew E2' 1 = getr regs 1) by (rewrite OLD2 by (cbv; lia); exact E1).
assert (Usp2 : bv_unsigned (ew E2' 2) = spZ regs) by (rewrite OLD2 by (cbv; lia); exact Usp).
shok_auto_with SHOK Bx E2' (mrestrict (w_H W2) mem2) rgc_SH
ltac:(apply (shent_ok_of_block trbsegs B LAWS ly2 S2 W2 mem2 md2 E2' Bx 10 r RGB_SIZE 0 RGB_SIZE HAR2 Hinr2);
[ unfold U, Bx; cbn [sv_denot]; rewrite OLD2 by (cbv; lia); rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; rewrite unsigned_lit_small by (unfold SB; lia); reflexivity
| unfold U; cbn [sv_denot]; rewrite OLD2 by (cbv; lia); rewrite E10, Z.add_0_r, Z_to_bv_bv_unsigned; rewrite unsigned_lit_small by (clear - Hr4096 Hrceil C1; lia); reflexivity
| lia | change (req_size RGB_SIZE) with 64; unfold RGB_SIZE; lia ]).
aj_run_tok trbtbl_lib_ok HS HJ SHOK Bspan. { awr_ok_tac. exact Usp2. }
assert (HU1 : In [pc_free_ra0 Trb_code; 0x85058] (as_universe B)) by (rewrite (tl_universe B TL); apply memZL_In; vm_compute; reflexivity).
assert (HU2 : In [pc_free_ra0 Trb_code; 0x85060] (as_universe B)) by (rewrite (tl_universe B TL); apply memZL_In; vm_compute; reflexivity).
pose proof HJ as (_ & _ & _ & _ & _ & _ & Hnev2 & _).
pose proof (proj1 HJ) as HARc2.
assert (F3 : ew E2' 3 = getr regs 3) by (rewrite OLD2 by (cbv; lia); exact E3).
assert (F4 : ew E2' 4 = getr regs 4) by (rewrite OLD2 by (cbv; lia); exact E4).
assert (F10 : ew E2' 10 = Z_to_bv 64 r) by (rewrite OLD2 by (cbv; lia); exact E10).
assert (F33 : ew E2' 33 = Z_to_bv 64 bef) by (rewrite OLD2 by (cbv; lia); exact E33).
assert (F35 : ew E2' 35 = Z_to_bv 64 SB) by (rewrite OLD2 by (cbv; lia); exact E35).
lazymatch goal with |- SRr _ _ (mkCfg ?ms ?mdc) _ =>
rreg HS (2%bv : bv 5) R2; rreg HS (10%bv : bv 5) R10; rreg HS (3%bv : bv 5) R3; rreg HS (4%bv : bv 5) R4;
rreg HS (1%bv : bv 5) R1; rreg HS (8%bv : bv 5) R8;
eapply SRr_bind;
[ eapply (rg_aj_free_opt B LAWS Hsegs errno_low ML AFREE W2 E2' _ ms TRGBCLOSE_STK (spZ regs) _ ly S W mem md [] ly2 S2 _ _
bef nbef (-32) (ew E2' 2) (Z_to_bv 64 0x85058) [] ((r, RGB_SIZE) :: rest));
[ exact HS | rewrite HBcode; reflexivity | reflexivity | exact HJ
| eapply Permutation_trans; [exact HPerm2 | apply Permutation_middle]
| rewrite R10, F33; reflexivity
| exact (st_ok_restrict_reg trbsegs (w_H W2) E2' _ _ 2%bv HS)
| reflexivity | exact Usp2 | reflexivity | lia | rewrite FFS; replace ASTACK with 16384 by reflexivity; lia
| rewrite R3, F3; exact Hgp | rewrite R4, F4; exact Htp
| exact R1 | vm_compute; reflexivity | unfold EV_RGBCLOSE in Hev; clear - Hev Hnev2; lia
| eapply (achain_chain_pre ly2 _ (spZ regs - 32) r []);
[ apply achain_low; clear - Hrceil; lia
| change (spZ (ms_regs ms)) with (bv_unsigned (getr (ms_regs ms) 2)); rewrite R2, unsigned_lit_small by lia; lia
| unfold s0Z; rewrite R8, F10; apply unsigned_lit_small; clear - Hr4096 Hrceil C1; lia
| unfold raZ; rewrite R1; rewrite unsigned_lit_small by lia; lia ]
| rewrite call_trace_nil; unfold raZ; rewrite R1, unsigned_lit_small by lia; rewrite HBcode; cbn; exact HU1
| intros Hb0 _ i Hi; apply (inFP_ablocks_fp _ bef nbef i); [right; apply in_app_iff; right; unfold optb; rewrite (proj2 (Z.eqb_neq bef 0) Hb0); left; reflexivity | exact Hi] ]
| ]
end.
clear HJ SHOK R2 R10 R3 R4 R1 R8 Hnev2.
cbv beta. intros W3 c3 Hwle3 (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ & HP3 & HPerm3 & Hfrs3 & HK).
pose proof (proj1 HJ) as HAR3.
destruct (al_const _ _ LAWS _ _ _ _ _ HARc2) as (Kcell3a & _ & Kgot3a & _). rewrite HBgot, HBcell in Kgot3a. rewrite HBcell in Kcell3a.
destruct (al_const _ _ LAWS _ _ _ _ _ HAR3) as (Kcell3 & _ & Kgot3 & _). rewrite HBgot, HBcell in Kgot3. rewrite HBcell in Kcell3.
assert (Hinr3 : In (r, RGB_SIZE) (ablocks B ly3 S3)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm3|]. left. reflexivity. }
jafter_call_keep HS 52%nat regs3 (mrestrict (w_H W3) mem3) HP3 [0; 1; 2; 3]%nat HS3.
match type of HS3 with ?t -> _ => assert (HRK : t); [|specialize (HS3 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; [| | | | apply Forall_nil].
- eapply (region_kept_stack_aj trbsegs B); [exact HK | exact HJ | exact Usp2 | lia | rewrite FFS; replace ASTACK with 16384 by reflexivity; lia | lia | lia | lia].
- apply (region_kept_val trbsegs E2' _ _ A_GOT_shadow 8 A_shadow_glob);
[exact (val_mem_of_rdword trbsegs _ _ _ _ Kgot3a) | exact (val_mem_of_rdword trbsegs _ _ _ _ Kgot3) | lia].
- apply (region_kept_val trbsegs E2' _ _ A_shadow_glob 8 SHADOW_OFF);
[exact (val_mem_of_rdword trbsegs _ _ _ _ Kcell3a) | exact (val_mem_of_rdword trbsegs _ _ _ _ Kcell3) | lia].
- eapply (region_kept_block_aj trbsegs B); [exact HK | rewrite F10; apply unsigned_lit_small; clear - Hr4096 Hrceil C1; lia | exact Hinr2 | lia
| change (req_size RGB_SIZE) with 64; unfold RGB_SIZE; lia | lia | ].
intros a Ha [Hb0 Hb].
pose proof (rg_sep_head_in B LAWS ly2 S2 W2 _ _ (r, RGB_SIZE) _ (bef, nbef) HARc2 HPerm2
ltac:(apply in_app_iff; left; unfold optb; rewrite (proj2 (Z.eqb_neq bef 0) Hb0); left; reflexivity)) as Hd.
unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd. change (req_size RGB_SIZE) with 64 in Hd. unfold RGB_SIZE in Ha. clear - Hd Ha Hb. lia. }
clear HS. rewrite <- restrict_mkst_fx in HS3. rename HS3 into HS.
remember (havoc E2' 52 (map (getr regs3) CLOB)) as E3' eqn:HE3' in HS.
assert (OLD3 : forall n, (n < 52)%nat -> ew E3' n = ew E2' n) by (intros n Hn; rewrite HE3'; apply YO3v.ew_havoc_old; exact Hn).
assert (HAE3 : env_agree 32 (Ereg regs (rgc_extra g bef)) E3') by (rewrite HE3'; apply env_agree_havoc_ge; [cbv; lia | exact HAE2]).
clear HE3'.
assert (G1 : ew E3' 1 = getr regs 1) by (rewrite OLD3 by (cbv; lia); exact F1).
assert (G3 : ew E3' 3 = getr regs 3) by (rewrite OLD3 by (cbv; lia); exact F3).
assert (G4 : ew E3' 4 = getr regs 4) by (rewrite OLD3 by (cbv; lia); exact F4).
assert (G10 : ew E3' 10 = Z_to_bv 64 r) by (rewrite OLD3 by (cbv; lia); exact F10).
assert (Usp3 : bv_unsigned (ew E3' 2) = spZ regs) by (rewrite OLD3 by (cbv; lia); exact Usp2).
shok_auto SHOK Bx E3' (mrestrict (w_H W3) mem3).
aj_run_tok trbtbl_lib_ok HS HJ SHOK Bspan. { awr_ok_tac. exact Usp3. }
pose proof HJ as (_ & _ & _ & _ & _ & _ & Hnev3 & _).
pose proof (proj1 HJ) as HARc3.
lazymatch goal with |- SRr _ _ (mkCfg ?ms ?mdc) _ =>
rreg HS (2%bv : bv 5) R2; rreg HS (10%bv : bv 5) R10; rreg HS (3%bv : bv 5) R3; rreg HS (4%bv : bv 5) R4;
rreg HS (1%bv : bv 5) R1; rreg HS (8%bv : bv 5) R8;
eapply SRr_bind;
[ eapply (aj_free trbsegs B LAWS Hsegs errno_low ML AFREE W3 E3' _ ms TRGBCLOSE_STK (spZ regs) _ ly S W mem md [] ly3 S3 _ _
r RGB_SIZE (-32) (ew E3' 2) (Z_to_bv 64 0x85060) []);
[ exact HS | rewrite HBcode; reflexivity | reflexivity | exact HJ | exact Hinr3
| rewrite R10, G10; reflexivity
| exact (st_ok_restrict_reg trbsegs (w_H W3) E3' _ _ 2%bv HS)
| reflexivity | exact Usp3 | reflexivity | lia | rewrite FFS; replace ASTACK with 16384 by reflexivity; lia
| rewrite R3, G3; exact Hgp | rewrite R4, G4; exact Htp
| exact R1 | vm_compute; reflexivity | unfold EV_RGBCLOSE in Hev; clear - Hev Hnev3; lia
| eapply (achain_chain_pre ly3 _ (spZ regs - 32) r []);
[ apply achain_low; clear - Hrceil; lia
| change (spZ (ms_regs ms)) with (bv_unsigned (getr (ms_regs ms) 2)); rewrite R2, unsigned_lit_small by lia; lia
| unfold s0Z; rewrite R8, G10; apply unsigned_lit_small; clear - Hr4096 Hrceil C1; lia
| unfold raZ; rewrite R1; rewrite unsigned_lit_small by lia; lia ]
| rewrite call_trace_nil; unfold raZ; rewrite R1, unsigned_lit_small by lia; rewrite HBcode; cbn; exact HU2
| intros _ i Hi; apply (inFP_ablocks_fp _ r RGB_SIZE i); [left; reflexivity | exact Hi] ]
| ]
end.
clear HJ SHOK R2 R10 R3 R4 R1 R8 Hnev3.
cbv beta. intros W4 c4 Hwle4 (ly4 & S4 & regs4 & mem4 & md4 & -> & HJ & HP4 & (l1 & l2 & Ebl & Ebl4) & Hfrs4 & HK4).
pose proof (proj1 HJ) as HAR4.
destruct (al_const _ _ LAWS _ _ _ _ _ HARc3) as (Kcell4a & _ & Kgot4a & _). rewrite HBgot, HBcell in Kgot4a. rewrite HBcell in Kcell4a.
destruct (al_const _ _ LAWS _ _ _ _ _ HAR4) as (Kcell4 & _ & Kgot4 & _). rewrite HBgot, HBcell in Kgot4. rewrite HBcell in Kcell4.
assert (HPerm4 : Permutation (ablocks B ly4 S4) rest).
{ rewrite Ebl4. apply Permutation_sym. apply (@Permutation_cons_app_inv _ _ l1 l2 (r, RGB_SIZE)). rewrite <- Ebl.
apply Permutation_sym. exact HPerm3. }
jafter_call_keep HS 68%nat regs4 (mrestrict (w_H W4) mem4) HP4 [0; 1; 2]%nat HS4.
match type of HS4 with ?t -> _ => assert (HRK : t); [|specialize (HS4 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; [| | | apply Forall_nil].
- eapply (region_kept_stack_aj trbsegs B); [exact HK4 | exact HJ | exact Usp3 | lia | rewrite FFS; replace ASTACK with 16384 by reflexivity; lia | lia | lia | lia].
- apply (region_kept_val trbsegs E3' _ _ A_GOT_shadow 8 A_shadow_glob);
[exact (val_mem_of_rdword trbsegs _ _ _ _ Kgot4a) | exact (val_mem_of_rdword trbsegs _ _ _ _ Kgot4) | lia].
- apply (region_kept_val trbsegs E3' _ _ A_shadow_glob 8 SHADOW_OFF);
[exact (val_mem_of_rdword trbsegs _ _ _ _ Kcell4a) | exact (val_mem_of_rdword trbsegs _ _ _ _ Kcell4) | lia]. }
clear HS. rewrite <- restrict_mkst_fx in HS4. rename HS4 into HS.
remember (havoc E3' 68 (map (getr regs4) CLOB)) as E4' eqn:HE4' in HS.
assert (OLD4 : forall n, (n < 68)%nat -> ew E4' n = ew E3' n) by (intros n Hn; rewrite HE4'; apply YO3v.ew_havoc_old; exact Hn).
assert (HAE4 : env_agree 32 (Ereg regs (rgc_extra g bef)) E4') by (rewrite HE4'; apply env_agree_havoc_ge; [cbv; lia | exact HAE3]).
clear HE4'.
assert (K1 : ew E4' 1 = getr regs 1) by (rewrite OLD4 by (cbv; lia); exact G1).
assert (Usp4 : bv_unsigned (ew E4' 2) = spZ regs) by (rewrite OLD4 by (cbv; lia); exact Usp3).
shok_auto SHOK Bx E4' (mrestrict (w_H W4) mem4).
aj_run_tok trbtbl_lib_ok HS HJ SHOK Bspan. { awr_ok_tac. exact Usp4. }
rreg HS (1%bv : bv 5) R1.
eapply (SRr_ret_at trbsegs trbtbl_lib trbtbl_lib_ok Hwx W4 _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'. lazymatch goal with |- apost_base _ _ _ _ _ _ _ _ _ _ _ _ (mkCfg (mkst ?rr _ ?m _) ?d) => exists ly4, S4, rr, m, d end.
split; [cbn [ms_regs]; rewrite R1, K1, Hra; reflexivity|].
split; [|split].
- cbn [ms_mem]. replace EV_RGBCLOSE with (0 + EV_CLOSE + 1 + 1) by (unfold EV_RGBCLOSE; lia).
apply (ajournal_materialize trbsegs B LAWS Hsegs). exact HJ.
- eapply (aregs_preserved_of_st_ok trbsegs _ E4' _ _ regs (rgc_extra g bef) HS); [exact HAE4 | vm_compute; reflexivity].
- exact HPerm4.
Qed.
End e.
End c.
