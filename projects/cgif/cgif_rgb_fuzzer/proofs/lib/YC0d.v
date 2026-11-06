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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00 YI02 YI03 YI04 YI1i YI20 YI1k YI1h YI16.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YC01 YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YG00 YG0a YG01 YG0h YG0u YG0d YC04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB0z YC19 YF8z YC1d YC1a YC1b YC2q YC2u YC4r YC13 YC2o YC16 YC12 YC20 YC3q YC17 YC18 YC0u YC0w YC0j YC0v YC0t YC0k YC0q YC0i.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Ltac af_E_names HEB sp0 g :=
lazymatch type of HEB with af_EB _ _ _ _ _ _ _ _ _ _ _ _ ?E =>
pose proof HEB as (HE & E67 & E70 & E71 & E72);
pose proof HE as (EEo & E32 & E33 & E34 & E35 & E36 & E37 & E38 & E39 & E40 & E41 & E42 & E43 & E44 & E45 & E46 & E47 & E48 & E49 & E50 & E51 & E52 & E53);
assert (Usp : bv_unsigned (ew E 2) = sp0) by (rewrite (EEo 2%nat 2%bv eq_refl); reflexivity);
assert (E32u : bv_unsigned (ew E 32) = g) by (rewrite E32; apply unsigned_lit_small; lia);
assert (HAE54 : env_agree 54 E E) by (split; [intros; reflexivity | reflexivity]) end.
Ltac evalE := cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by lia.
Ltac range_app_of Hia :=
let x := fresh "x" in let Hx := fresh "Hx" in
intros x Hx; cbn [Z.min Z.max] in Hx; generalize Hia; clear - Hx; unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL; intros; lia.
Section b. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section c.
Variable B : asyms.
Hypothesis TL : TraLib B.
Hypothesis LAWS : AR_laws trasegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis ABCMP : abcmp_realizes trasegs B A_bcmp_icpt.
Let HBcode := tl_code B TL. Let HBgot := tl_got_shadow B TL. Let HBcell := tl_shadow_cell B TL.
Lemma af_B2 : AF_C_stmt B -> AF_L_stmt B -> AF_SM_stmt B -> AF_Bi_stmt B 2.
Proof.
intros PC PL PSM ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest E0 ms1 md1 f Hihv CX HE0 HPX Hn HS0 SHOK0.
destruct (af_B_ext B LAWS ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest E0 ms1 md1 f CX HE0 HPX Hn HS0 SHOK0)
as (HEB & HPB & HS & SHOK).
set (E := havoc E0 70 [Z_to_bv 64 (fr_img f); Z_to_bv 64 (fr_attr f); Z_to_bv 64 (fr_delay f)]) in HEB, HS, SHOK.
clear HS0 SHOK0 HE0.
af_B_names LAWS CX HEB HPB Hn. clear Hih. rename Hihv into Hih.
rewrite Hih in HS, SHOK, Hn; change (Z.to_nat 2) with 2%nat in Hn; change (33 + Z.to_nat 2)%nat with 35%nat in HS, SHOK; cbn [Z.mul Pos.mul] in HS.
assert (B35 : bv_unsigned (ew E 35) = fr_ptr f) by (rewrite E35, Hn; cbn [frame_ptr]; apply unsigned_lit_small; clear - Hh4096 Hhceil C1; lia).
assert (Hfne : nth_error (cg_frames s) 2 = Some (Some f)).
{ clear - Hlen Hn. destruct (cg_frames s) as [|o0 [|o1 [|o2 [|x l]]]]; cbn in Hlen; try discriminate. cbn in Hn |- *. rewrite Hn. reflexivity. }
pose proof (proj2 HSD f HfIn) as HOBf.
assert (UH : U E (SExt false 16 (SOff 43 0)) = cg_H s) by (apply (U_zext_small E 16 _ _ (U_atom E 43 _ E43 ltac:(clear - RH; lia))); [clear - RH; lia | cbn; clear; lia]).
assert (UW : U E (SExt false 16 (SOff 42 0)) = cg_W s) by (apply (U_zext_small E 16 _ _ (U_atom E 42 _ E42 ltac:(clear - RW; lia))); [clear - RW; lia | cbn; clear; lia]).
aj_run_tok tratbl_lib_ok HS HJ SHOK RBspanA; [awr_b Usp E32u Hing HTS 35%nat B35 Hfb Hfq |].
side_step HSD HGK HZr HZf HZg Usp E32u; clear_frames.
srr_branch_tok tratbl_lib_ok HS SHOK RBspanA.
{
aj_run_to_tok tratbl_lib_ok HS HJ SHOK RBspanA AF_C; [awr_b Usp E32u Hing HTS 35%nat B35 Hfb Hfq |].
side_step HSD HGK HZr HZf HZg Usp E32u; clear_frames.
af_rejoin HS (ss_C 2 16 35) 200%nat;
lazymatch type of HS with st_ok _ ?E' _ (restrict _ ?msF) =>
eapply (PC ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest E' msF _ CX);
[ apply (af_E_agree _ _ _ _ _ _ _ _ _ _ _ E); [exact HE | agreeE_tac]
| apply (af_pre_agree B _ _ _ _ _ _ _ _ _ _ _ E); [| agreeE_tac];
split; [exact HJ | split; [exact HSD | split; [exact HGK | split; [exact Hcur | split; [exact HnoTab | split; [exact E67 | rewrite Hih; clear; lia]]]]]]
| rewrite Hih; exact HS
| lazymatch type of SHOK with sh_ok _ _ _ ?E1 _ =>
let HAG1 := fresh "HAG1" in
assert (HAG1 : env_agree 54 E1 E') by (apply env_agree_havoc_ge; [clear; cbv; lia | (split; [intros; reflexivity | reflexivity]) || env_agree_chain HAE54]);
exact (sh_ok_agree trasegs Bxa af_SH 54 E1 E' _ HAG1 eq_refl (proj1 (proj1 (Forall_app _ _ _) SHOK))) end ] end. }
aj_run_tok tratbl_lib_ok HS HJ SHOK RBspanA; [awr_b Usp E32u Hing HTS 35%nat B35 Hfb Hfq |].
side_step HSD HGK HZr HZf HZg Usp E32u; clear_frames.
srr_branch_tok tratbl_lib_ok HS SHOK RBspanA.
{
aj_run_to_tok tratbl_lib_ok HS HJ SHOK RBspanA AF_C; [awr_b Usp E32u Hing HTS 35%nat B35 Hfb Hfq |].
side_step HSD HGK HZr HZf HZg Usp E32u; clear_frames.
af_rejoin HS (ss_C 2 16 35) 200%nat;
lazymatch type of HS with st_ok _ ?E' _ (restrict _ ?msF) =>
eapply (PC ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest E' msF _ CX);
[ apply (af_E_agree _ _ _ _ _ _ _ _ _ _ _ E); [exact HE | agreeE_tac]
| apply (af_pre_agree B _ _ _ _ _ _ _ _ _ _ _ E); [| agreeE_tac];
split; [exact HJ | split; [exact HSD | split; [exact HGK | split; [exact Hcur | split; [exact HnoTab | split; [exact E67 | rewrite Hih; clear; lia]]]]]]
| rewrite Hih; exact HS
| lazymatch type of SHOK with sh_ok _ _ _ ?E1 _ =>
let HAG1 := fresh "HAG1" in
assert (HAG1 : env_agree 54 E1 E') by (apply env_agree_havoc_ge; [clear; cbv; lia | (split; [intros; reflexivity | reflexivity]) || env_agree_chain HAE54]);
exact (sh_ok_agree trasegs Bxa af_SH 54 E1 E' _ HAG1 eq_refl (proj1 (proj1 (Forall_app _ _ _) SHOK))) end ] end. }
aj_run_tok tratbl_lib_ok HS HJ SHOK RBspanA; [awr_b Usp E32u Hing HTS 35%nat B35 Hfb Hfq |].
side_step HSD HGK HZr HZf HZg Usp E32u; clear_frames.
srr_branch_tok tratbl_lib_ok HS SHOK RBspanA.
{
aj_run_tok tratbl_lib_ok HS HJ SHOK RBspanA; [awr_b Usp E32u Hing HTS 35%nat B35 Hfb Hfq |].
side_step HSD HGK HZr HZf HZg Usp E32u; clear_frames.
srr_branch_tok tratbl_lib_ok HS SHOK RBspanA.
{
exfalso.
lazymatch goal with H : branch_taken _ _ _ = true |- _ =>
rewrite branch_eq_U in H; rewrite U_lit in H by (clear; lia);
rewrite (U_mulw_small E _ _ (cg_H s) (cg_W s) UH UW) in H by (clear - RW RH HNWH HN1; nia);
apply (proj1 (Z.eqb_eq _ _)) in H; clear - H HNWH HN1; nia end. }
aj_run_to_tok tratbl_lib_ok HS HJ SHOK RBspanA AF_LOOP; [awr_b Usp E32u Hing HTS 35%nat B35 Hfb Hfq |].
side_step HSD HGK HZr HZf HZg Usp E32u; clear_frames.
rreg HS (19%bv : bv 5) R19. rreg HS (25%bv : bv 5) R24. rregD HS (20%bv : bv 5) R9.
cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub] in R19, R24.
rewrite ?ew_ewset_other in R19 by (clear; lia). rewrite ?ew_ewset_other in R24 by (clear; lia).
af_rejoin HS (ss_L0 2 16 35) 200%nat.
lazymatch type of HS with st_ok _ ?E' _ (restrict _ ?msF) =>
eapply (PL (Z.to_nat N) ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest E' msF _ f 0 CX);
[ apply (af_EB_agree _ _ _ _ _ _ _ _ _ _ _ _ E); [exact HEB | agreeE_tac]
| split; [exact HJ | split; [exact HSD | split; [exact HGK | split; [exact Hcur | split; [exact HnoTab | rewrite Hih; clear; lia]]]]]
| rewrite Hih; exact Hn
| rewrite Hih; exact HS
| rewrite Hih; change (33 + Z.to_nat 2)%nat with 35%nat;
lazymatch type of SHOK with sh_ok _ _ _ ?E1 _ =>
let HAG1 := fresh "HAG1" in
assert (HAG1 : env_agree 73 E1 E') by (apply env_agree_havoc_ge; [clear; cbv; lia | (split; [intros; reflexivity | reflexivity]) || env_agree_chain HAE54]);
exact (sh_ok_agree trasegs Bxa (af_SHB 35) 73 E1 E' _ HAG1 eq_refl SHOK) end
|
change 213%nat with (200 + 13)%nat; rewrite (YO3v.ew_havoc_new _ 200 _ 13 (Z_to_bv 64 0)) by (cbn; clear; lia); cbn [nth];
rewrite R19; evalE; rewrite ?E48, ?E70; unfold w64; f_equal; clear; lia
|
change 214%nat with (200 + 14)%nat; rewrite (YO3v.ew_havoc_new _ 200 _ 14 (Z_to_bv 64 0)) by (cbn; clear; lia); cbn [nth];
rewrite R24; evalE; rewrite ?E48, ?E70; unfold w64; f_equal; clear; lia
|
change 204%nat with (200 + 4)%nat; rewrite (YO3v.ew_havoc_new _ 200 _ 4 (Z_to_bv 64 0)) by (cbn; clear; lia); cbn [nth];
rewrite R9; rewrite denot_lit_U; unfold w64; f_equal; rewrite Z2Nat.id by (clear - HN1; lia);
apply (U_zext32_shifts _ _ N); [| clear - HN1; lia];
lazymatch goal with |- U ?E9 ?v9 = _ =>
tryif constr_eq E9 E then idtac else (
let HAG := fresh "HAG" in assert (HAG : env_agree 54 E E9) by (env_agree_chain HAE54);
rewrite (U_agree 54 E E9 v9 HAG eq_refl); clear HAG) end;
rewrite (U_mulw_small E _ _ (cg_H s) (cg_W s) UH UW) by (clear - RW RH HNWH HN1; nia); clear - HNWH; lia
| clear; lia
| rewrite Z2Nat.id by (clear - HN1; lia); clear; lia
| clear - HN1; lia ] end. }
aj_run_tok tratbl_lib_ok HS HJ SHOK RBspanA; [awr_b Usp E32u Hing HTS 35%nat B35 Hfb Hfq |].
side_step HSD HGK HZr HZf HZg Usp E32u; clear_frames.
srr_branch_tok tratbl_lib_ok HS SHOK RBspanA.
2: {
aj_run_tok tratbl_lib_ok HS HJ SHOK RBspanA; [awr_b Usp E32u Hing HTS 35%nat B35 Hfb Hfq |].
side_step HSD HGK HZr HZf HZg Usp E32u; clear_frames.
srr_branch_tok tratbl_lib_ok HS SHOK RBspanA.
{
exfalso.
lazymatch goal with H : branch_taken _ _ _ = true |- _ =>
rewrite branch_eq_U in H; rewrite U_lit in H by (clear; lia);
rewrite (U_mulw_small E _ _ (cg_H s) (cg_W s) UH UW) in H by (clear - RW RH HNWH HN1; nia);
apply (proj1 (Z.eqb_eq _ _)) in H; clear - H HNWH HN1; nia end. }
aj_run_to_tok tratbl_lib_ok HS HJ SHOK RBspanA AF_LOOP; [awr_b Usp E32u Hing HTS 35%nat B35 Hfb Hfq |].
side_step HSD HGK HZr HZf HZg Usp E32u; clear_frames.
rreg HS (19%bv : bv 5) R19. rreg HS (25%bv : bv 5) R24. rregD HS (20%bv : bv 5) R9.
cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub] in R19, R24.
rewrite ?ew_ewset_other in R19 by (clear; lia). rewrite ?ew_ewset_other in R24 by (clear; lia).
af_rejoin HS (ss_L0 2 16 35) 200%nat.
lazymatch type of HS with st_ok _ ?E' _ (restrict _ ?msF) =>
eapply (PL (Z.to_nat N) ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest E' msF _ f 0 CX);
[ apply (af_EB_agree _ _ _ _ _ _ _ _ _ _ _ _ E); [exact HEB | agreeE_tac]
| split; [exact HJ | split; [exact HSD | split; [exact HGK | split; [exact Hcur | split; [exact HnoTab | rewrite Hih; clear; lia]]]]]
| rewrite Hih; exact Hn
| rewrite Hih; exact HS
| rewrite Hih; change (33 + Z.to_nat 2)%nat with 35%nat;
lazymatch type of SHOK with sh_ok _ _ _ ?E1 _ =>
let HAG1 := fresh "HAG1" in
assert (HAG1 : env_agree 73 E1 E') by (apply env_agree_havoc_ge; [clear; cbv; lia | (split; [intros; reflexivity | reflexivity]) || env_agree_chain HAE54]);
exact (sh_ok_agree trasegs Bxa (af_SHB 35) 73 E1 E' _ HAG1 eq_refl SHOK) end
|
change 213%nat with (200 + 13)%nat; rewrite (YO3v.ew_havoc_new _ 200 _ 13 (Z_to_bv 64 0)) by (cbn; clear; lia); cbn [nth];
rewrite R19; evalE; rewrite ?E48, ?E70; unfold w64; f_equal; clear; lia
|
change 214%nat with (200 + 14)%nat; rewrite (YO3v.ew_havoc_new _ 200 _ 14 (Z_to_bv 64 0)) by (cbn; clear; lia); cbn [nth];
rewrite R24; evalE; rewrite ?E48, ?E70; unfold w64; f_equal; clear; lia
|
change 204%nat with (200 + 4)%nat; rewrite (YO3v.ew_havoc_new _ 200 _ 4 (Z_to_bv 64 0)) by (cbn; clear; lia); cbn [nth];
rewrite R9; rewrite denot_lit_U; unfold w64; f_equal; rewrite Z2Nat.id by (clear - HN1; lia);
apply (U_zext32_shifts _ _ N); [| clear - HN1; lia];
lazymatch goal with |- U ?E9 ?v9 = _ =>
tryif constr_eq E9 E then idtac else (
let HAG := fresh "HAG" in assert (HAG : env_agree 54 E E9) by (env_agree_chain HAE54);
rewrite (U_agree 54 E E9 v9 HAG eq_refl); clear HAG) end;
rewrite (U_mulw_small E _ _ (cg_H s) (cg_W s) UH UW) by (clear - RW RH HNWH HN1; nia); clear - HNWH; lia
| clear; lia
| rewrite Z2Nat.id by (clear - HN1; lia); clear; lia
| clear - HN1; lia ] end. }
aj_run_to_tok tratbl_lib_ok HS HJ SHOK RBspanA A_bcmp_icpt; [awr_b Usp E32u Hing HTS 35%nat B35 Hfb Hfq |].
side_step HSD HGK HZr HZf HZg Usp E32u; clear_frames.
destruct (al_blocks _ _ LAWS _ _ _ _ _ img N (proj1 HJ) Himg) as (_ & _ & _ & _ & HiP & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ (fr_img f) N (proj1 HJ) Hfimg) as (_ & _ & _ & _ & HfiP & _).
rreg HS (10%bv : bv 5) Ra0. rreg HS (11%bv : bv 5) Ra1. rregD HS (12%bv : bv 5) Ra2. rreg HS (1%bv : bv 5) Rra.
rreg HS (2%bv : bv 5) Qsp. rreg HS (3%bv : bv 5) Qgp. rreg HS (4%bv : bv 5) Qtp.
lazymatch type of Qsp with getr ?rg _ = _ => assert (HspU : spZ rg = sp0 - 224) by (unfold spZ; rewrite Qsp; cbn [sv_denot]; evalE; rewrite Usp; apply unsigned_lit_small; clear - Hceil Hslo Hshi H47 HTS C1; lia) end.
lazymatch goal with |- SRr _ _ (mkCfg ?msq _) _ => rewrite (st_ok_restrict_mkst trasegs (w_H W) _ _ msq HS eq_refl) end. cbn [ss_pc].
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ (ms_mem _) _) ?mdX) _ =>
eapply (aj_bcmp_at trasegs B LAWS Hsegs A_bcmp_icpt ABCMP W (ms_regs msX) (ms_mem msX) TADDFRAME_STK sp0 (FPa g s N) ly S W mem md []
ly S mdX 0 img (fr_img f) N (-224) (Z_to_bv 64 0x860fc) HJ);
[ rewrite Ra0; cbn [sv_denot]; evalE; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; exact E48
| rewrite Ra1; cbn [sv_denot]; evalE; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; exact E70
| rewrite Ra2; rewrite denot_lit_U; unfold w64; f_equal; rewrite U_mul_smallD by (rewrite UH, UW; clear - RW RH; nia); rewrite UH, UW; clear - HNWH; lia
| clear - HN1; lia | clear - Hi4096; lia | clear - Hiceil HrN C1; lia | clear - Hfi4096; lia | clear - Hficeil HrN C1; lia
| rewrite HspU; clear; lia
| reflexivity | clear; lia | rewrite HTS, HES; clear; lia
| rewrite Qgp; cbn [sv_denot]; evalE; rewrite (EEo 3%nat 3%bv eq_refl); exact Hgp
| rewrite Qtp; cbn [sv_denot]; evalE; rewrite (EEo 4%nat 4%bv eq_refl); exact Htp
| exact Rra
| apply ret_ok_even; vm_compute; reflexivity
| intros a Ha; split; [apply (aview_some_of_apresent trasegs); apply (proj1 (HiP a ltac:(clear - Ha HrN; lia))) | rewrite HspU, HES; intro; clear - Ha H Hi4096 Hiceil HrN Hceil Hslo HTS C1; lia]
| intros a Ha; split; [apply (aview_some_of_apresent trasegs); apply (proj1 (HfiP a ltac:(clear - Ha HrN; lia))) | rewrite HspU, HES; intro; clear - Ha H Hfi4096 Hficeil HrN Hceil Hslo HTS C1; lia]
| intros a Ha; rewrite HES; clear - Ha Hi4096 Hiceil HrN Hceil Hslo HTS C1; lia
| intros a Ha; rewrite HES; clear - Ha Hfi4096 Hficeil HrN Hceil Hslo HTS C1; lia
| apply (amem_range_of_block trasegs B LAWS ly S W _ _ img N _ _ (proj1 HJ) Himg); clear - HN1 HrN; lia
| apply (amem_range_of_block trasegs B LAWS ly S W _ _ (fr_img f) N _ _ (proj1 HJ) Hfimg); clear - HN1 HrN; lia
| apply (range_addressable_of_block trasegs B LAWS ly S W _ _ img N _ _ (proj1 HJ) Himg); clear - HN1 HrN; lia
| intros _; apply (shadow_hull_vis_of_block trasegs B LAWS ly S W _ _ img N _ _ (proj1 HJ) Himg); clear - HN1 HrN; lia
| apply (range_addressable_of_block trasegs B LAWS ly S W _ _ (fr_img f) N _ _ (proj1 HJ) Hfimg); clear - HN1 HrN; lia
| intros _; apply (shadow_hull_vis_of_block trasegs B LAWS ly S W _ _ (fr_img f) N _ _ (proj1 HJ) Hfimg); clear - HN1 HrN; lia ] end. }
cbv beta. clear Ra0 Ra1 Ra2 Qgp Qtp.
intros W2 c2 _ (-> & regs2 & mem2 & md2 & v & -> & HJ2 & HP2 & Hv & Hcmp & Hfr2 & Hpres2).
destruct (al_const _ _ LAWS _ _ _ _ _ (proj1 HJ)) as (Kcellb & _ & Kgotb & _). rewrite HBgot, HBcell in Kgotb. rewrite HBcell in Kcellb.
destruct (al_const _ _ LAWS _ _ _ _ _ (proj1 HJ2)) as (Kcell2 & _ & Kgot2 & _). rewrite HBgot, HBcell in Kgot2. rewrite HBcell in Kcell2.
let K := lazymatch type of HS with st_ok _ _ ?ss _ => eval vm_compute in (run_K 0 Bxa (af_SHB 35) ss) end in
jafter_call_keep HS K regs2 (mrestrict (w_H W) mem2) HP2 [0; 1; 2; 3; 4; 5; 6]%nat HS2.
match type of HS2 with ?tt -> _ => assert (HRK : tt); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil;
first
[ eapply region_kept_aview;
[ first [exact B35 | exact Usp | exact E32u | rewrite E46; apply unsigned_lit_small; clear - Hcfp C1; lia]
| intros a Ha; cbn [YQ0b.r_lo YQ0b.r_hi] in Ha; apply Hfr2;
[ clear - Ha Hh4096 Hhceil HZg Hgceil Hcfp Hceil Hslo Hshi H47 HTS C1; lia
| rewrite HES; clear - Ha Hh4096 Hhceil HZg Hgceil Hcfp Hceil Hslo Hshi H47 HTS C1; lia ]
| exact Hpres2 ]
| apply (region_kept_val trasegs _ _ _ A_GOT_shadow 8 A_shadow_glob);
[exact (val_mem_of_rdword trasegs _ _ _ _ Kgotb) | exact (val_mem_of_rdword trasegs _ _ _ _ Kgot2) | clear; lia]
| apply (region_kept_val trasegs _ _ _ A_shadow_glob 8 SHADOW_OFF);
[exact (val_mem_of_rdword trasegs _ _ _ _ Kcellb) | exact (val_mem_of_rdword trasegs _ _ _ _ Kcell2) | clear; lia]
| match goal with |- ?gg => idtac "KEPTFAIL" gg end ]. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E 73 (map (getr regs2) CLOB)) as E2 eqn:HE2 in HS.
assert (OLD2 : forall n, (n < 73)%nat -> ew E2 n = ew E n) by (intros n Hn0; rewrite HE2; apply YO3v.ew_havoc_old; exact Hn0).
assert (E77 : ew E2 77 = v) by (rewrite HE2; change 77%nat with (73 + 4)%nat; rewrite (YO3v.ew_havoc_new E 73 _ 4 (Z_to_bv 64 0)) by (cbn; lia); cbn [nth map]; exact Hv).
assert (HAE2 : env_agree 73 E E2) by (rewrite HE2; apply env_agree_havoc_ge; [clear; lia | apply env_agree_refl]).
clear HE2.
pose proof (af_EB_agree _ _ _ _ _ _ _ _ _ _ _ _ E E2 HEB (fun n Hn0 => OLD2 n Hn0)) as HEB2.
pose proof (af_side_sep B LAWS ly S W mem md g s N _ ly sp0 (fun a => sp0 - 224 - 2 * ESTACK <= a < sp0 - 224) HAR HPerm Hstk
ltac:(intros a Ha; cbv beta in Ha; left; rewrite HES in Ha; clear - Ha HTS; lia)) as [HZr2 HZf2].
replace (sp0 + -224) with (sp0 - 224) in Hfr2 by (clear; lia).
pose proof (af_side_kept _ _ _ _ _ (fun a => sp0 - 224 - 2 * ESTACK <= a < sp0 - 224) HSD Hfr2 HZr2 HZf2) as HSD2. clear HSD HZr2 HZf2. rename HSD2 into HSD.
assert (HGK2 : forall i, 0 <= i < 96 -> ~ (88 <= i < 92) -> mbyte trasegs (mrestrict (w_H W) mem2) (g + i) = mbyte trasegs (mrestrict (w_H W) mem) (g + i)).
{ intros i Hi Hni. etransitivity; [| exact (HGK i Hi Hni)]. apply (mbyte_of_aview trasegs). apply Hfr2; [| rewrite HES]; clear - Hi HZg Hgceil Hceil Hslo HTS C1; lia. }
clear HGK. rename HGK2 into HGK.
clear HJ. rename HJ2 into HJ.
clear SHOK B35 HEB. try clear HE E67 E70 E71 E72 EEo E32 E33 E34 E35 E36 E37 E38 E39 E40 E41 E42 E43 E44 E45 E46 E47 E48 E49 E50 E51 E52 E53 Usp E32u HAE54 UH UW.
rename HEB2 into HEB. af_E_names HEB sp0 g.
assert (B35 : bv_unsigned (ew E2 35) = fr_ptr f) by (rewrite E35, Hn; cbn [frame_ptr]; apply unsigned_lit_small; clear - Hh4096 Hhceil C1; lia).
assert (SHOK : sh_ok trasegs Bxa (af_SHB 35) E2 (mrestrict (w_H W) mem2)).
{ pose proof (afobj_journal B LAWS sp0 ly S W mem md [] ly S W _ _ _ g s N _ cfp 32 HJ HAR HPerm HFO) as (_ & _ & HRA2).
unfold sh_ok, af_SHB, af_SH. cbn [app]. constructor; [|constructor; [|constructor; [|constructor]]].
- apply (shent_ok_of_block trasegs B LAWS ly S W mem2 md2 E2 Bxa 32 g CGIF_SIZE 0 CGIF_SIZE (proj1 HJ) Hing).
+ unfold U, Bxa. cbn [sv_denot]. rewrite E38, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
+ unfold U. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact E32u.
+ lia.
+ change (req_size CGIF_SIZE) with 96. unfold CGIF_SIZE. lia.
- apply (shent_ok_of_range trasegs (w_H W) mem2 E2 Bxa 46 cfp 32 cfp 0 32 HRA2).
+ unfold U, Bxa. cbn [sv_denot]. rewrite E38, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
+ unfold U. cbn [sv_denot]. rewrite E46, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by lia. reflexivity.
+ lia. + lia. + range_app_of Hcfp_ia.
- apply (shent_ok_of_block trasegs B LAWS ly S W mem2 md2 E2 Bxa 35 (fr_ptr f) FRAME_SIZE 0 FRAME_SIZE (proj1 HJ) Hfb).
+ unfold U, Bxa. cbn [sv_denot]. rewrite E38, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
+ unfold U. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact B35.
+ lia.
+ rewrite HFS. change (req_size 40) with 40. lia. }
assert (HPB2 : af_preB B ly S W regs mem md g cfp s N fattr (mkst regs2 (Z_to_bv 64 0x860fc) mem2 (seg_rom trasegs)) md2).
{ split; [exact HJ|]. split; [exact HSD|]. split; [exact HGK|]. split; [exact Hcur|]. split; [exact HnoTab | rewrite Hih; clear; lia]. }
srr_branch_tok tratbl_lib_ok HS SHOK RBspanA.
{
aj_run_to_tok tratbl_lib_ok HS HJ SHOK RBspanA AF_SAME; [awr_b Usp E32u Hing HTS 35%nat B35 Hfb Hfq |].
side_step HSD HGK HZr HZf HZg Usp E32u; clear_frames.
af_rejoin HS (ss_SM 2 16 35) 200%nat.
lazymatch type of HS with st_ok _ ?E' _ (restrict _ ?msF) =>
eapply (PSM ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest E' msF _ f CX);
[ apply (af_EB_agree _ _ _ _ _ _ _ _ _ _ _ _ E2); [exact HEB | agreeE_tac]
| split; [exact HJ | split; [exact HSD | split; [exact HGK | split; [exact Hcur | split; [exact HnoTab | rewrite Hih; clear; lia]]]]]
| rewrite Hih; exact Hn
| rewrite Hih; exact HS
| rewrite Hih; change (33 + Z.to_nat 2)%nat with 35%nat;
lazymatch type of SHOK with sh_ok _ _ _ ?E1 _ =>
let HAG1 := fresh "HAG1" in
assert (HAG1 : env_agree 73 E1 E') by (apply env_agree_havoc_ge; [clear; cbv; lia | (split; [intros; reflexivity | reflexivity]) || env_agree_chain HAE54]);
exact (sh_ok_agree trasegs Bxa (af_SHB 35) 73 E1 E' _ HAG1 eq_refl SHOK) end ] end. }
aj_run_to_tok tratbl_lib_ok HS HJ SHOK RBspanA AF_C; [awr_b Usp E32u Hing HTS 35%nat B35 Hfb Hfq |].
side_step HSD HGK HZr HZf HZg Usp E32u; clear_frames.
af_rejoin HS (ss_C 2 16 35) 200%nat;
lazymatch type of HS with st_ok _ ?E2' _ (restrict _ ?msF) =>
eapply (PC ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest E2' msF _ CX);
[ apply (af_E_agree _ _ _ _ _ _ _ _ _ _ _ E2); [exact HE | agreeE_tac]
| apply (af_pre_agree B _ _ _ _ _ _ _ _ _ _ _ E2); [| agreeE_tac];
split; [exact HJ | split; [exact HSD | split; [exact HGK | split; [exact Hcur | split; [exact HnoTab | split; [exact E67 | rewrite Hih; clear; lia]]]]]]
| rewrite Hih; exact HS
| lazymatch type of SHOK with sh_ok _ _ _ ?E1 _ =>
let HAG1 := fresh "HAG1" in
assert (HAG1 : env_agree 54 E1 E2') by (apply env_agree_havoc_ge; [clear; cbv; lia | (split; [intros; reflexivity | reflexivity]) || env_agree_chain HAE54]);
exact (sh_ok_agree trasegs Bxa af_SH 54 E1 E2' _ HAG1 eq_refl (proj1 (proj1 (Forall_app _ _ _) SHOK))) end ] end.
Qed.
End c.
End b.
