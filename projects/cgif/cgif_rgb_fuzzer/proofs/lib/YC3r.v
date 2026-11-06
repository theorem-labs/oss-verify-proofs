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
YG00 YG0a YG01 YG0h YG0u YG0d YC04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB0z YC19 YF8z YC1d YC1a YC10 YC2p YC1b.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section b. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section RC.
Variable B : asyms.
Hypothesis TL : TraLib B.
Hypothesis LAWS : AR_laws trasegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis AFREE : afree_realizes trasegs B.
Let HBcode := tl_code B TL. Let HBgot := tl_got_shadow B TL. Let HBcell := tl_shadow_cell B TL. Let errno_low := tl_env B TL.
Local Notation code := (as_code B).
Definition Bx : sv := SOff 35 0.
Definition rc_regions : smem :=
[ stack_region 32; YQ0b.mkRegion (Some 2%nat) (-48) (-32) (-48) (-32) []; got_region; bcell_region 35;
YQ0b.mkRegion (Some 10%nat) 0 RAW_SIZE 0 0
[YQ0b.mkChunk 0 (CVal 8 (SLit A_cgif_writecb)); YQ0b.mkChunk 8 (CVal 8 (SOff 32 0)); YQ0b.mkChunk 40 (CVal 4 (SOff 33 0))];
YQ0b.mkRegion (Some 32%nat) 0 CGIF_SIZE 0 0
[YQ0b.mkChunk 56 (CVal 8 (SLit A_writecb)); YQ0b.mkChunk 64 (CVal 8 (SOff 34 0)); YQ0b.mkChunk 80 (CVal 8 (SLit 0))] ].
Definition rc_facts : facts :=
mkFacts [ (2%nat, mkAF (2^46) (2^47) 4); (10%nat, mkAF 4096 140737479966720 4); (32%nat, mkAF 4096 140737479966720 4);
(33%nat, mkAF 0 (2^32 - 1) 0); (34%nat, mkAF 0 (2^64 - 1) 0); (35%nat, mkAF SB SB 0) ] [] [].
Definition ss_rc : sstate := mkSS A_cgif_raw_close sr_atoms rc_regions None rc_facts.
Definition rc_SH : list shent := [ mkSHE 10 0 RAW_SIZE; mkSHE 32 0 CGIF_SIZE ].
Definition Bspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition rc_extra (g rcur ctx : Z) : list word := map (Z_to_bv 64) [g; rcur; ctx; SB].
Lemma rc_entry : forall W ly S regs mem md ch raw g rcur ctx rest,
afn_pre trasegs B TRAWCLOSE_STK ly S W regs mem md ch ->
getr regs 10 = w64 raw ->
Permutation (ablocks B ly S) ((raw, RAW_SIZE) :: (g, CGIF_SIZE) :: rest) ->
val_mem trasegs (mrestrict (w_H W) mem) raw 8 A_cgif_writecb ->
val_mem trasegs (mrestrict (w_H W) mem) (raw + 8) 8 g ->
val_mem trasegs (mrestrict (w_H W) mem) (raw + 40) 4 rcur -> 0 <= rcur < 2 ^ 32 ->
val_mem trasegs (mrestrict (w_H W) mem) (g + 56) 8 A_writecb ->
val_mem trasegs (mrestrict (w_H W) mem) (g + 64) 8 ctx -> 0 <= ctx < 2 ^ 64 ->
val_mem trasegs (mrestrict (w_H W) mem) (g + 80) 8 0 ->
st_ok trasegs (Ereg regs (rc_extra g rcur ctx)) ss_rc
(restrict (w_H W) (mkst regs (Z_to_bv 64 A_cgif_raw_close) mem (seg_rom trasegs)))
/\ sh_ok trasegs Bx rc_SH (Ereg regs (rc_extra g rcur ctx)) (mrestrict (w_H W) mem).
Proof.
intros W ly S regs mem md ch raw g rcur ctx rest HPRE H10 HPerm Mwfn Mctx Mcur Rcur Mgw Mgf Rctx Mg80.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (FFS : TRAWCLOSE_STK = 16416) by reflexivity.
assert (Hinr : In (raw, RAW_SIZE) (ablocks B ly S)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm|]. left. reflexivity. }
assert (Hing : In (g, CGIF_SIZE) (ablocks B ly S)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm|]. right. left. reflexivity. }
destruct (al_blocks _ _ LAWS ly S W mem md raw RAW_SIZE HAR Hinr) as (Hr16 & Hr4096 & Hrceil & Hrh_ia & _ & _). pose proof (proj1 Hrh_ia) as Hrh.
pose proof (blk_off_img _ _ _ _ _ _ raw RAW_SIZE HAR Hinr) as Hrh_img.
destruct (al_blocks _ _ LAWS ly S W mem md g CGIF_SIZE HAR Hing) as (Hg16 & Hg4096 & Hgceil & Hgh_ia & _ & _). pose proof (proj1 Hgh_ia) as Hgh.
pose proof (blk_off_img _ _ _ _ _ _ g CGIF_SIZE HAR Hing) as Hgh_img.
change (req_size RAW_SIZE) with 48 in *. change (req_size CGIF_SIZE) with 96 in *.
pose proof (sep_blocks_perm trasegs B LAWS ly S W mem md _ _ _ HAR HPerm) as Hd1. unfold zdisjoint, block_rng in Hd1. cbn [fst snd] in Hd1.
change (req_size RAW_SIZE) with 48 in Hd1. change (req_size CGIF_SIZE) with 96 in Hd1.
destruct (al_const _ _ LAWS ly S W mem md HAR) as (Kcell & _ & Kgot & _). rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
rewrite restrict_mkst_fx.
set (E := Ereg regs (rc_extra g rcur ctx)).
assert (E2 : ew E 2 = getr regs 2) by (subst E; exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 raw) by (subst E; rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (EX : forall j, ew E (32 + j) = nth j (rc_extra g rcur ctx) (Z_to_bv 64 0)) by (intros j; subst E; apply ew_Ereg_extra).
pose proof (EX 0%nat) as E32. pose proof (EX 1%nat) as E33. pose proof (EX 2%nat) as E34. pose proof (EX 3%nat) as E35.
cbn [Nat.add nth rc_extra map] in E32, E33, E34, E35. clear EX.
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
split.
- unfold ss_rc. apply (entry_st_ok_full trasegs); change (Ereg regs (rc_extra g rcur ctx)) with E.
+ apply regs_ok_Ereg.
+ vm_compute. reflexivity.
+ unfold rc_regions, stack_region, got_region, bcell_region.
repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks].
* cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
intros o Ho. apply (apresent_writable trasegs). apply Hpres. lia.
* cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
intros o Ho. apply (apresent_writable trasegs). apply Hpres. lia.
* cbn [base_val]. unfold A_GOT_shadow. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor]. rewrite <- (Z.add_0_l 663904) at 1.
apply (chunk_ok_val trasegs E _ 0 663904 8 (SLit A_shadow_glob) A_shadow_glob); [reflexivity | unfold A_shadow_glob; zside | zside |].
exact (val_mem_of_rdword trasegs (w_H W) mem _ _ Kgot).
* cbn [base_val]. unfold A_shadow_glob. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor]. rewrite <- (Z.add_0_l 696760) at 1.
apply (chunk_ok_val trasegs E _ 0 696760 8 Bx SB);
[cbn [sv_denot Bx]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | zside |].
exact (val_mem_of_rdword trasegs (w_H W) mem _ _ Kcell).
* rewrite (VB 10%nat raw E10) by lia. unfold RAW_SIZE. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor; [|constructor; [|constructor]]].
-- apply (chunk_ok_val trasegs E _ raw 0 8 _ A_cgif_writecb); [reflexivity | unfold A_cgif_writecb; zside | zside | rewrite Z.add_0_r; exact Mwfn].
-- apply (chunk_ok_val trasegs E _ raw 8 8 _ g); [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Mctx].
-- apply (chunk_ok_val trasegs E _ raw 40 4 _ rcur); [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Mcur].
* rewrite (VB 32%nat g E32) by lia. unfold CGIF_SIZE. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor; [|constructor; [|constructor]]].
-- apply (chunk_ok_val trasegs E _ g 56 8 _ A_writecb); [reflexivity | unfold A_writecb; zside | zside | exact Mgw].
-- apply (chunk_ok_val trasegs E _ g 64 8 _ ctx); [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Mgf].
-- apply (chunk_ok_val trasegs E _ g 80 8 _ 0); [reflexivity | zside | zside | exact Mg80].
+ apply pairwise_disjoint_of_extents. unfold rc_regions, stack_region, got_region, bcell_region, extent_of_region.
cbn [map YQ0b.r_base YQ0b.r_lo YQ0b.r_hi]. rewrite (VB 10%nat raw E10), (VB 32%nat g E32) by lia. cbn [base_val]. rewrite Usp.
unfold A_GOT_shadow, A_shadow_glob, RAW_SIZE, CGIF_SIZE.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
revert Hslo Hshi H47 Hceil Hrceil Hrh Hrh_img Hr4096 Hgceil Hgh Hgh_img Hg4096 Hd1 C1 C3 FFS Hstk0. clear. unfold zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kLowShadowBeg, kHighMemBeg. intros. repeat split; lia.
+ split; [|split; [exact I | exact I]].
cbn [rc_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite Usp, E10, E32, E33, E34, E35, !unsigned_lit_small by (unfold SB; lia).
change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
revert Hslo Hshi H47 Hceil Hrceil Hrh Hrh_img Hr4096 Hr16 Hgceil Hgh Hgh_img Hg4096 Hg16 Hal16 Rcur Rctx C1 C3 FFS Hstk0. clear. unfold SB, zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kLowShadowBeg, kHighMemBeg. intros.
repeat match goal with |- _ /\ _ => split end; lia.
- unfold sh_ok, rc_SH. constructor; [|constructor; [|constructor]].
+ apply (shent_ok_of_block trasegs B LAWS ly S W mem md E Bx 10 raw RAW_SIZE 0 RAW_SIZE HAR Hinr).
* unfold U, Bx. cbn [sv_denot]. rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
* unfold U. cbn [sv_denot]. rewrite E10, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by lia. reflexivity.
* lia.
* change (req_size RAW_SIZE) with 48. unfold RAW_SIZE. lia.
+ apply (shent_ok_of_block trasegs B LAWS ly S W mem md E Bx 32 g CGIF_SIZE 0 CGIF_SIZE HAR Hing).
* unfold U, Bx. cbn [sv_denot]. rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
* unfold U. cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by lia. reflexivity.
* lia.
* change (req_size CGIF_SIZE) with 96. unfold CGIF_SIZE. lia.
Qed.
Theorem tra_cgif_raw_close : trawclose_spec B.
Proof.
unfold trawclose_spec.
intros ly S W regs mem md ch raw g rcur ctx rest HPRE H10 HPerm Mwfn Mctx Mcur Rcur Mgw Mgf Rctx Mg80 Hev HU1.
pose proof Hwx_tfa as Hwx. pose proof tra_segs_low as Hsegs.
destruct (rc_entry W ly S regs mem md ch raw g rcur ctx rest HPRE H10 HPerm Mwfn Mctx Mcur Rcur Mgw Mgf Rctx Mg80) as [HS SHOK].
pose proof (ajournal_init trasegs B TRAWCLOSE_STK (ablocks_fp [(raw, RAW_SIZE)]) ly S W regs mem md ch HPRE) as HJ.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5). assert (FFS : TRAWCLOSE_STK = 16416) by reflexivity.
assert (HEV : EV_RAWCLOSE = 1) by reflexivity.
remember (Ereg regs (rc_extra g rcur ctx)) as E eqn:HE.
assert (E1 : ew E 1 = getr regs 1) by (subst E; exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (subst E; exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E3 : ew E 3 = getr regs 3) by (subst E; exact (ew_Ereg_nat regs _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regs 4) by (subst E; exact (ew_Ereg_nat regs _ 4 4%bv eq_refl)).
assert (E8 : ew E 8 = getr regs 8) by (subst E; exact (ew_Ereg_nat regs _ 8 8%bv eq_refl)).
assert (E9 : ew E 9 = getr regs 9) by (subst E; exact (ew_Ereg_nat regs _ 9 9%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 raw) by (subst E; rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E32 : ew E 32 = Z_to_bv 64 g) by (subst E; exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 rcur) by (subst E; exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 ctx) by (subst E; exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 SB) by (subst E; exact (ew_Ereg_extra regs _ 3)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (HAE : env_agree 32 (Ereg regs (rc_extra g rcur ctx)) E) by (rewrite HE; split; [intros n Hn; reflexivity | reflexivity]).
clear HE.
assert (Hinr : In (raw, RAW_SIZE) (ablocks B ly S)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm|]. left. reflexivity. }
assert (Hing : In (g, CGIF_SIZE) (ablocks B ly S)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm|]. right. left. reflexivity. }
destruct (al_blocks _ _ LAWS ly S W mem md raw RAW_SIZE HAR Hinr) as (Hr16 & Hr4096 & Hrceil & Hrh_ia & _ & _). pose proof (proj1 Hrh_ia) as Hrh.
pose proof (blk_off_img _ _ _ _ _ _ raw RAW_SIZE HAR Hinr) as Hrh_img.
destruct (al_blocks _ _ LAWS ly S W mem md g CGIF_SIZE HAR Hing) as (Hg16 & Hg4096 & Hgceil & Hgh_ia & _ & _). pose proof (proj1 Hgh_ia) as Hgh.
pose proof (blk_off_img _ _ _ _ _ _ g CGIF_SIZE HAR Hing) as Hgh_img.
change (req_size RAW_SIZE) with 48 in Hrceil, Hrh, Hrh_img. change (req_size CGIF_SIZE) with 96 in Hgceil, Hgh, Hgh_img.
pose proof (sep_blocks_perm trasegs B LAWS ly S W mem md _ _ _ HAR HPerm) as Hd1. unfold zdisjoint, block_rng in Hd1. cbn [fst snd] in Hd1.
change (req_size RAW_SIZE) with 48 in Hd1. change (req_size CGIF_SIZE) with 96 in Hd1.
unfold cfg_at. change (w64 A_cgif_raw_close) with (Z_to_bv 64 A_cgif_raw_close).
aj_run_tok tratbl_lib_ok HS HJ SHOK Bspan. { awr_ok_tac; exact Usp. }
pose proof (proj1 HJ) as HARc.
lazymatch goal with |- SRr _ _ (mkCfg ?ms ?mdc) _ =>
rreg HS (2%bv : bv 5) R2; rreg HS (10%bv : bv 5) R10; rreg HS (3%bv : bv 5) R3; rreg HS (4%bv : bv 5) R4;
rreg HS (1%bv : bv 5) R1; rreg HS (8%bv : bv 5) R8;
eapply SRr_bind;
[ eapply (aj_free trasegs B LAWS Hsegs errno_low ML AFREE W E _ ms TRAWCLOSE_STK (spZ regs) _ ly S W mem md [] ly S _ 0
raw RAW_SIZE (-32) (ew E 2) (Z_to_bv 64 0x8a91c) []);
[ exact HS | rewrite HBcode; reflexivity | reflexivity | exact HJ | exact Hinr
| rewrite R10, E10; reflexivity
| exact (st_ok_restrict_reg trasegs (w_H W) E _ _ 2%bv HS)
| reflexivity | exact Usp | reflexivity | lia | unfold TRAWCLOSE_STK; lia
| rewrite R3, E3; exact Hgp | rewrite R4, E4; exact Htp
| exact R1 | vm_compute; reflexivity | lia
| eapply (achain_chain_pre ly _ (spZ regs - 32) raw []);
[ apply achain_low; lia
| change (spZ (ms_regs ms)) with (bv_unsigned (getr (ms_regs ms) 2)); rewrite R2, unsigned_lit_small by lia; lia
| unfold s0Z; rewrite R8, E10; apply unsigned_lit_small; lia
| unfold raZ; rewrite R1; rewrite unsigned_lit_small by lia; lia ]
| rewrite call_trace_nil; unfold raZ; rewrite R1, unsigned_lit_small by lia; rewrite HBcode; cbn; exact HU1
| intros _ i Hi; apply (inFP_ablocks_fp _ raw RAW_SIZE i); [left; reflexivity | exact Hi] ]
| ]
end.
clear HJ SHOK R2 R10 R3 R4 R1 R8.
intros W2 c2 Hwle2 (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ & HP2 & (l1 & l2 & Ebl & Ebl2) & Hfrs2 & HK).
pose proof (proj1 HJ) as HAR2.
destruct (al_const _ _ LAWS _ _ _ _ _ HARc) as (Kcell & _ & Kgot & _). rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
destruct (al_const _ _ LAWS _ _ _ _ _ HAR2) as (Kcell2 & _ & Kgot2 & _). rewrite HBgot, HBcell in Kgot2. rewrite HBcell in Kcell2.
assert (HPerm2 : Permutation (ablocks B ly2 S2) ((g, CGIF_SIZE) :: rest)).
{ rewrite Ebl2. apply Permutation_sym. apply (@Permutation_cons_app_inv _ _ l1 l2 (raw, RAW_SIZE)). rewrite <- Ebl.
apply Permutation_sym. exact HPerm. }
jafter_call_keep HS 36%nat regs2 (mrestrict (w_H W2) mem2) HP2 [0; 2; 3; 5]%nat HS2.
match type of HS2 with ?t -> _ => assert (HRK : t); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; [| | | | apply Forall_nil].
- eapply (region_kept_stack_aj trasegs B); [exact HK | exact HJ | exact Usp | lia | unfold TRAWCLOSE_STK, ASTACK; lia | lia | lia | lia].
- apply (region_kept_val trasegs E _ _ A_GOT_shadow 8 A_shadow_glob);
[exact (val_mem_of_rdword trasegs _ _ _ _ Kgot) | exact (val_mem_of_rdword trasegs _ _ _ _ Kgot2) | lia].
- apply (region_kept_val trasegs E _ _ A_shadow_glob 8 SHADOW_OFF);
[exact (val_mem_of_rdword trasegs _ _ _ _ Kcell) | exact (val_mem_of_rdword trasegs _ _ _ _ Kcell2) | lia].
- eapply (region_kept_block_aj trasegs B); [exact HK | rewrite E32; apply unsigned_lit_small; lia | exact Hing | lia
| change (req_size CGIF_SIZE) with 96; unfold CGIF_SIZE; lia | lia | unfold CGIF_SIZE; intros a Ha HE'; change (req_size RAW_SIZE) with 48 in HE'; lia]. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E 36 (map (getr regs2) CLOB)) as E2' eqn:HE2' in HS.
assert (OLD2 : forall n, (n < 36)%nat -> ew E2' n = ew E n) by (intros n Hn; rewrite HE2'; apply YO3v.ew_havoc_old; exact Hn).
assert (HAE2 : env_agree 32 (Ereg regs (rc_extra g rcur ctx)) E2') by (rewrite HE2'; apply env_agree_havoc_ge; [cbv; lia | exact HAE]).
clear HE2'.
assert (F1 : ew E2' 1 = getr regs 1) by (rewrite OLD2 by (cbv; lia); exact E1).
assert (Usp2 : bv_unsigned (ew E2' 2) = spZ regs) by (rewrite OLD2 by (cbv; lia); exact Usp).
shok_auto SHOK Bx E2' (mrestrict (w_H W2) mem2).
aj_run_tok tratbl_lib_ok HS HJ SHOK Bspan. { awr_ok_tac. exact Usp2. }
rreg HS (1%bv : bv 5) R1.
eapply (SRr_ret_at trasegs tratbl_lib tratbl_lib_ok Hwx W2 _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'. lazymatch goal with |- apost_base _ _ _ _ _ _ _ _ _ _ _ _ (mkCfg (mkst ?r _ ?m _) ?d) => exists ly2, S2, r, m, d end.
split; [cbn [ms_regs]; rewrite R1, F1, Hra; reflexivity|].
split; [|split].
- cbn [ms_mem]. rewrite HEV. apply (ajournal_materialize trasegs B LAWS Hsegs). exact HJ.
- eapply (aregs_preserved_of_st_ok trasegs _ E2' _ _ regs (rc_extra g rcur ctx) HS); [exact HAE2 | vm_compute; reflexivity].
- exact HPerm2.
Qed.
End RC.
End b.
