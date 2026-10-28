(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04 YI09.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0d YP0c YI0w YI0y YC4a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC80 YC1f YC81 YC4b.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC20.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section c.
Context {PI : PAImg lib_asan3_1_listing}.
Context {RO : YC20.ro_below_ofl (@pa_segs _ lib_asan3_1_listing PI) (@pa_relro_lo _ lib_asan3_1_listing PI) (@pa_relro_hi _ lib_asan3_1_listing PI)}.
#[local] Notation SEGS := (@pa_segs _ lib_asan3_1_listing PI).
#[local] Notation VAL := (@pa_val _ lib_asan3_1_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_asan3_1_listing PI).
#[local] Notation BASE := (@pa_val _ lib_asan3_1_listing PI A_TEXT).
Ltac eimg_low := rewrite ?Eimg_low by (unfold A_TEXT; lia).
Definition A_cgif_raw_close : Z := AF_asan3_cgif_raw_close.
Definition A_cgif_raw_closeP : Z := BASE + A_cgif_raw_close.
Lemma st_ok_pi_region_nth : forall E ss ms i r,
st_ok_pi SEGS VAL E ss ms -> nth_error (ss_mem ss) i = Some r -> region_ok SEGS E (ms_mem ms) r.
Proof. intros E ss ms i r HS Hi. exact (st_ok_region_nth E (abs_ss VAL ss) ms i r HS ltac:(destruct ss; exact Hi)). Qed.
Section RC.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis AFREE : afree_realizes SEGS B.
Variables wfn hw : Z.
Hypothesis Rwfn : 0 <= wfn < 2 ^ 64 /\ wfn mod 2 = 0.
Hypothesis Rhw : 0 <= hw < 2 ^ 64.
Hypothesis WFN : twcb_spec SEGS B wfn hw.
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL. Let errno_low := pal_env B TL. Let HBfree := pal_free B TL.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_asan3_1) (PI := PI).
Local Notation code := (as_code B).
Definition Bx : sv := SOff 35 0.
Definition rc_regions : smem :=
[ stack_region 32; got_regionP; bcell_regionP 35;
YP09.mkRegion (Some 10%nat) 0 RAW_SIZE 0 0
[YP09.mkChunk 0 (CVal 8 (SOff 36 0)); YP09.mkChunk 8 (CVal 8 (SOff 32 0)); YP09.mkChunk 40 (CVal 4 (SOff 33 0))];
YP09.mkRegion (Some 32%nat) 0 CGIF_SIZE 0 0
[YP09.mkChunk 56 (CVal 8 (SOff 37 0)); YP09.mkChunk 64 (CVal 8 (SOff 34 0)); YP09.mkChunk 80 (CVal 8 (SLit 0))] ].
Definition rc_facts : facts :=
mkFacts [ (2%nat, mkAF (2^46) (2^47) 4); (10%nat, mkAF 4096 140737479966720 4); (32%nat, mkAF 4096 140737479966720 4);
(33%nat, mkAF 0 (2^32 - 1) 0); (34%nat, mkAF 0 (2^64 - 1) 0); (35%nat, mkAF SB SB 0);
(36%nat, mkAF 0 (2^64 - 1) 1); (37%nat, mkAF 0 (2^64 - 1) 0) ] [] [].
Definition ss_rc : sstate := mkSS A_cgif_raw_close sr_atoms rc_regions None rc_facts.
Definition rc_SH : list shent := [ mkSHE 10 0 RAW_SIZE; mkSHE 32 0 CGIF_SIZE ].
Definition Bspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition rc_extra (g rcur ctx : Z) : list word := map (Z_to_bv 64) [g; rcur; ctx; SB; wfn; hw].
Lemma rc_entry : forall W ly S regs mem md ch raw g rcur ctx rest,
afn_pre SEGS B TRAWCLOSE_STK ly S W regs mem md ch ->
getr regs 10 = w64 raw ->
Permutation (ablocks B ly S) ((raw, RAW_SIZE) :: (g, CGIF_SIZE) :: rest) ->
val_mem SEGS (mrestrict (w_H W) mem) raw 8 wfn ->
val_mem SEGS (mrestrict (w_H W) mem) (raw + 8) 8 g ->
val_mem SEGS (mrestrict (w_H W) mem) (raw + 40) 4 rcur -> 0 <= rcur < 2 ^ 32 ->
val_mem SEGS (mrestrict (w_H W) mem) (g + 56) 8 hw ->
val_mem SEGS (mrestrict (w_H W) mem) (g + 64) 8 ctx -> 0 <= ctx < 2 ^ 64 ->
val_mem SEGS (mrestrict (w_H W) mem) (g + 80) 8 0 ->
st_ok_pi SEGS VAL (Eimg (Ereg regs (rc_extra g rcur ctx))) ss_rc
(restrict (w_H W) (mkst regs (Z_to_bv 64 A_cgif_raw_closeP) mem (seg_rom SEGS)))
/\ sh_ok SEGS Bx rc_SH (Eimg (Ereg regs (rc_extra g rcur ctx))) (mrestrict (w_H W) mem).
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
pose proof (blk_off_imgP _ _ _ _ _ _ raw RAW_SIZE HAR Hinr) as Hrh_img.
destruct (al_blocks _ _ LAWS ly S W mem md g CGIF_SIZE HAR Hing) as (Hg16 & Hg4096 & Hgceil & Hgh_ia & _ & _). pose proof (proj1 Hgh_ia) as Hgh.
pose proof (blk_off_imgP _ _ _ _ _ _ g CGIF_SIZE HAR Hing) as Hgh_img.
change (req_size RAW_SIZE) with 48 in *. change (req_size CGIF_SIZE) with 96 in *.
pose proof (sep_blocks_perm SEGS B LAWS ly S W mem md _ _ _ HAR HPerm) as Hd1. unfold zdisjoint, block_rng in Hd1. cbn [fst snd] in Hd1.
change (req_size RAW_SIZE) with 48 in Hd1. change (req_size CGIF_SIZE) with 96 in Hd1.
destruct (al_const _ _ LAWS ly S W mem md HAR) as (Kcell & _ & Kgot & _). rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs (rc_extra g rcur ctx))). pose proof pa_B_ok as HBASE.
assert (E2 : ew E 2 = getr regs 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 raw) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E32 : ew E 32 = Z_to_bv 64 g) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 rcur) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 ctx) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
assert (E36 : ew E 36 = Z_to_bv 64 wfn) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 4)).
assert (E37 : ew E 37 = Z_to_bv 64 hw) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 5)).
pose proof Rwfn as [Rwfn0 Ewfn].
assert (E241 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E253 : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
pose proof (pa_obj_img 12 ltac:(lia)) as HcellR. pose proof (pal_got_cell B TL) as HgcD. pose proof (pa_obj_img 0 ltac:(lia)) as HgotR.
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
split.
- unfold ss_rc, A_cgif_raw_closeP, A_cgif_raw_close. apply pa_entry_st_ok_full.
+ apply regs_ok_Eimg_Ereg.
+ vm_compute. reflexivity.
+ unfold rc_regions, stack_region, got_regionP, bcell_regionP.
repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
* cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
* rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (pose proof (pa_val_range (A_OBJ 0)); lia). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
[cbn [sv_denot]; rewrite E253, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | pose proof (pa_val_range (A_OBJ 12)); zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS _ _ _ _ Kgot).
* rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) E253) by (pose proof (pa_val_range (A_OBJ 12)); lia). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 12)) 0 8 Bx SB);
[cbn [sv_denot Bx]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS _ _ _ _ Kcell).
* rewrite (VB 10%nat raw E10) by lia. unfold RAW_SIZE. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor; [|constructor; [|constructor]]].
-- apply (chunk_ok_val SEGS E _ raw 0 8 _ wfn); [cbn [sv_denot]; rewrite E36, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | rewrite Z.add_0_r; exact Mwfn].
-- apply (chunk_ok_val SEGS E _ raw 8 8 _ g); [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Mctx].
-- apply (chunk_ok_val SEGS E _ raw 40 4 _ rcur); [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Mcur].
* rewrite (VB 32%nat g E32) by lia. unfold CGIF_SIZE. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor; [|constructor; [|constructor]]].
-- apply (chunk_ok_val SEGS E _ g 56 8 _ hw); [cbn [sv_denot]; rewrite E37, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Mgw].
-- apply (chunk_ok_val SEGS E _ g 64 8 _ ctx); [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Mgf].
-- apply (chunk_ok_val SEGS E _ g 80 8 _ 0); [reflexivity | zside | zside | exact Mg80].
+ apply pairwise_disjoint_of_extents. unfold rc_regions, stack_region, got_regionP, bcell_regionP, extent_of_region.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite (VB 10%nat raw E10), (VB 32%nat g E32) by lia. rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (pose proof (pa_val_range (A_OBJ 0)); lia). rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) E253) by (pose proof (pa_val_range (A_OBJ 12)); lia). cbn [base_val]. rewrite Usp.
unfold RAW_SIZE, CGIF_SIZE.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
revert Hslo Hshi H47 Hceil Hrceil Hrh Hrh_img Hr4096 Hgceil Hgh Hgh_img Hg4096 Hd1 C1 C3 FFS Hstk0 HcellR HgcD HgotR. clear. unfold zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kLowShadowBeg, kHighMemBeg. intros. repeat split; lia.
+ split; [|split; [exact I | exact I]].
cbn [rc_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite Usp, E10, E32, E33, E34, E35, E36, E37, !unsigned_lit_small by (unfold SB; lia).
change (2 ^ 4) with 16. change (2 ^ 1) with 2. rewrite !Z.pow_0_r, !Z.mod_1_r.
revert Hslo Hshi H47 Hceil Hrceil Hrh Hrh_img Hr4096 Hr16 Hgceil Hgh Hgh_img Hg4096 Hg16 Hal16 Rcur Rctx C1 C3 FFS Hstk0 Rwfn0 Ewfn Rhw. clear. unfold SB, zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kLowShadowBeg, kHighMemBeg. intros.
repeat match goal with |- _ /\ _ => split end; lia.
- unfold sh_ok, rc_SH. constructor; [|constructor; [|constructor]].
+ apply (shent_ok_of_block SEGS B LAWS ly S W mem md E Bx 10 raw RAW_SIZE 0 RAW_SIZE HAR Hinr).
* unfold U, Bx. cbn [sv_denot]. rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
* unfold U. cbn [sv_denot]. rewrite E10, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by lia. reflexivity.
* lia.
* change (req_size RAW_SIZE) with 48. unfold RAW_SIZE. lia.
+ apply (shent_ok_of_block SEGS B LAWS ly S W mem md E Bx 32 g CGIF_SIZE 0 CGIF_SIZE HAR Hing).
* unfold U, Bx. cbn [sv_denot]. rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
* unfold U. cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by lia. reflexivity.
* lia.
* change (req_size CGIF_SIZE) with 96. unfold CGIF_SIZE. lia.
Qed.
Theorem pb_raw_close : trawclose_spec SEGS B A_cgif_raw_closeP [pc_free_ra0 code; BASE + 0x25a8] wfn hw.
Proof.
unfold trawclose_spec.
intros ly S W regs mem md ch raw g rcur ctx rest HPRE H10 HPerm Mwfn Mctx Mcur Rcur Mgw Mgf Rctx Mg80 Hev HU1.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof Rwfn as [Rwfn0 Ewfn].
destruct (rc_entry W ly S regs mem md ch raw g rcur ctx rest HPRE H10 HPerm Mwfn Mctx Mcur Rcur Mgw Mgf Rctx Mg80) as [HS SHOK].
pose proof (ajournal_init SEGS B TRAWCLOSE_STK (ablocks_fp [(raw, RAW_SIZE)]) ly S W regs mem md ch HPRE) as HJ.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5). assert (FFS : TRAWCLOSE_STK = 16416) by reflexivity.
assert (HEV : EV_RAWCLOSE = 1) by reflexivity.
remember (Eimg (Ereg regs (rc_extra g rcur ctx))) as E eqn:HE. assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (E1 : ew E 1 = getr regs 1) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E3 : ew E 3 = getr regs 3) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regs 4) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 4 4%bv eq_refl)).
assert (E8 : ew E 8 = getr regs 8) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 8 8%bv eq_refl)).
assert (E9 : ew E 9 = getr regs 9) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 9 9%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 raw) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E32 : ew E 32 = Z_to_bv 64 g) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 rcur) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 ctx) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
assert (E36 : ew E 36 = Z_to_bv 64 wfn) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 4)).
assert (E37 : ew E 37 = Z_to_bv 64 hw) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 5)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (HAE : env_agree 32 (Ereg regs (rc_extra g rcur ctx)) E) by (rewrite HE; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
clear HE.
assert (Hinr : In (raw, RAW_SIZE) (ablocks B ly S)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm|]. left. reflexivity. }
assert (Hing : In (g, CGIF_SIZE) (ablocks B ly S)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm|]. right. left. reflexivity. }
destruct (al_blocks _ _ LAWS ly S W mem md raw RAW_SIZE HAR Hinr) as (Hr16 & Hr4096 & Hrceil & Hrh_ia & _ & _). pose proof (proj1 Hrh_ia) as Hrh.
pose proof (blk_off_imgP _ _ _ _ _ _ raw RAW_SIZE HAR Hinr) as Hrh_img.
destruct (al_blocks _ _ LAWS ly S W mem md g CGIF_SIZE HAR Hing) as (Hg16 & Hg4096 & Hgceil & Hgh_ia & Hgpres & _). pose proof (proj1 Hgh_ia) as Hgh.
pose proof (blk_off_imgP _ _ _ _ _ _ g CGIF_SIZE HAR Hing) as Hgh_img.
change (req_size RAW_SIZE) with 48 in Hrceil, Hrh, Hrh_img. change (req_size CGIF_SIZE) with 96 in Hgceil, Hgh, Hgh_img, Hgpres.
pose proof (sep_blocks_perm SEGS B LAWS ly S W mem md _ _ _ HAR HPerm) as Hd1. unfold zdisjoint, block_rng in Hd1. cbn [fst snd] in Hd1.
change (req_size RAW_SIZE) with 48 in Hd1. change (req_size CGIF_SIZE) with 96 in Hd1.
unfold cfg_at. change (w64 A_cgif_raw_closeP) with (Z_to_bv 64 A_cgif_raw_closeP). unfold A_cgif_raw_closeP, A_cgif_raw_close.
paj_run_tok RUN HS HJ SHOK Bspan. { awr_ok_tac; exact Usp. }
pose proof (proj1 HJ) as HARc.
prreg HS (2%bv : bv 5) Q2. prreg HS (13%bv : bv 5) Q13. prreg HS (10%bv : bv 5) Q10. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
prreg HS (8%bv : bv 5) Q8.
lazymatch type of HS with st_ok_pi _ _ _ ?ssx (restrict _ ?msx) =>
let r := eval vm_compute in (nth 4 (ss_mem ssx) got_regionP) in
pose proof (st_ok_pi_region_nth E ssx (restrict _ msx) 4 r HS ltac:(vm_compute; reflexivity)) as HRg; cbn [ms_mem restrict mkst] in HRg end.
assert (Ug : bv_unsigned (ew E 32) = g) by (rewrite E32; apply unsigned_lit_small; lia).
pose proof (field_of_region E _ 32 g _ _ _ _ _ 56 8 (SOff 37 0) hw HRg Ug ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; rewrite E37, unsigned_lit_small, Z.add_0_r by lia; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as Vhw.
pose proof (field_of_region E _ 32 g _ _ _ _ _ 64 8 (SOff 34 0) ctx HRg Ug ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; rewrite E34, unsigned_lit_small, Z.add_0_r by lia; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as Vctx.
pose proof (field_of_region E _ 32 g _ _ _ _ _ 80 8 (SLit 0) 0 HRg Ug ltac:(cbn; tauto)
ltac:(reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as Vpf.
clear HRg.
lazymatch type of HS with st_ok_pi _ _ _ ?ssj _ =>
let pcj := eval vm_compute in (ss_pc ssj) in
let wj := eval vm_compute in (match plookup asan3_1_tpi pcj with Some (PW x) => x | _ => 0 end) in
eapply (SRr_jalr_call_pi (PL:=PL_asan3_1) W E ssj _ _ _ wj (1%bv : bv 5) (13%bv : bv 5) wfn HEI HS eq_refl);
[ vm_compute; reflexivity | vm_refl_bv | reflexivity | cbn [ss_pc]; lia | rewrite Q13, E36; reflexivity | exact Rwfn0 | exact Ewfn |]
end.
clear HS. intros mat1 ms1 Ems1 HS1. pose proof HS1 as HS.
prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4. prreg HS (8%bv : bv 5) P8.
prreg HS (10%bv : bv 5) P10.
lazymatch type of HS with st_ok _ _ (mkSST _ (sr_set (ss_regs ?ssj) _ _) _ _ _ _) _ =>
lazymatch goal with |- SRr _ _ (mkCfg ?msq ?mdq) _ =>
eapply SRr_bind;
[ eapply (aj_call SEGS B LAWS Hsegs W E _ msq TRAWCLOSE_STK (spZ regs) (ablocks_fp [(raw, RAW_SIZE)]) ly S W mem md [] ly S mdq 0
WCB_STK [] 0 (-32) (ew E 2) _ [] (fun ly2 S2 W2 regs2 mem2 md2 => getr regs2 10 = w64 0 /\ Permutation (ablocks B ly2 S2) (ablocks B ly S)) HS eq_refl);
[ rewrite Ems1; cbn [ms_mem mkst]; apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJ
| exact P2 | reflexivity | exact Usp | reflexivity | lia | unfold WCB_STK; lia | rewrite FFS; unfold WCB_STK; lia
| rewrite P3, E3; exact Hgp | rewrite P4, E4; exact Htp
| exact P1 | apply ret_ok_codeptr_v; [lia | reflexivity] | rewrite unsigned_lit_small by lia; lia
| apply achain_low; unfold s0Z; rewrite P8, E10, unsigned_lit_small by lia; lia
| intros HPRE1;
eapply SRr_mono;
[ pose proof (WFN W ly S _ _ _ [] g ctx HPRE1) as HC; unfold cfg_at in HC;
replace (w64 wfn) with (Z_to_bv 64 (ss_pc (mkSST wfn (sr_set (ss_regs ssj) 1 (SOff A_TEXT (ss_pc ssj + 4))) (ss_fregs ssj) (ss_mem ssj) None (ss_facts ssj)))) in HC by reflexivity;
eapply HC; [ rewrite P10, E32; reflexivity | exact Hing | | | | exact Rctx ]; rewrite Ems1; cbn [ms_mem mkst]; [exact Vhw | exact Vctx | exact Vpf]
| cbv beta; unfold wcb_post; intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ1 & HP & HK);
exists ly2, S2, regs2, mem2, md2; split; [rewrite P1; reflexivity | split; [exact HJ1 | split; [exact HP | exact HK]]] ]
| intros a (r & Hr & _); destruct Hr ]
| ] end end.
clear HS SHOK. cbv beta. intros W2 c2 Hwle2 (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HJc & HP2 & Ha0 & HPb).
pose proof (proj1 HJ2) as HAR2.
destruct (al_const _ _ LAWS _ _ _ _ _ HARc) as (Kcell & _ & Kgot & _). rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
destruct (al_const _ _ LAWS _ _ _ _ _ HAR2) as (Kcell2 & _ & Kgot2 & _). rewrite HBgot, HBcell in Kgot2. rewrite HBcell in Kcell2.
assert (HPerm2 : Permutation (ablocks B ly2 S2) ((raw, RAW_SIZE) :: (g, CGIF_SIZE) :: rest)).
{ eapply Permutation_trans; [exact HPb | exact HPerm]. }
assert (Hinr2 : In (raw, RAW_SIZE) (ablocks B ly2 S2)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm2|]; left; reflexivity).
assert (Hing2 : In (g, CGIF_SIZE) (ablocks B ly2 S2)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm2|]; right; left; reflexivity).
jafter_call_keep_pi HS1 38%nat regs2 (mrestrict (w_H W2) mem2) HP2 [0; 1; 2; 3; 4]%nat HS2.
rewrite Ems1 in HS2, HJc. cbn [ms_mem ms_regs restrict mkst] in HS2, HJc.
match type of HS2 with ?tq -> _ => assert (HRK : tq); [|specialize (HS2 HRK); clear HRK] end.
{ repeat apply Forall_cons; [| | | | | apply Forall_nil].
- eapply (region_kept_stack_sub SEGS B); [exact HJc | exact HJ2 | exact Usp | lia | rewrite FFS; lia | lia | cbn; lia | cbn; lia].
- apply (region_kept_val_at E _ _ (A_OBJ 0) (VAL (A_OBJ 0)) 8 (VAL (A_OBJ 12)));
[exact (HEI (A_OBJ 0) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) | exact (val_mem_of_rdword SEGS _ _ _ _ Kgot) | exact (val_mem_of_rdword SEGS _ _ _ _ Kgot2) | lia].
- apply (region_kept_val_at E _ _ (A_OBJ 12) (VAL (A_OBJ 12)) 8 SHADOW_OFF);
[exact (HEI (A_OBJ 12) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) | exact (val_mem_of_rdword SEGS _ _ _ _ Kcell) | exact (val_mem_of_rdword SEGS _ _ _ _ Kcell2) | lia].
- eapply (region_kept_block_sub SEGS B); [exact HJc | rewrite E10; apply unsigned_lit_small; lia | exact Hinr | exact Hinr2 | lia
| change (req_size RAW_SIZE) with 48; unfold RAW_SIZE; lia | lia | intros a Ha (r & Hr & _); destruct Hr].
- eapply (region_kept_block_sub SEGS B); [exact HJc | rewrite E32; apply unsigned_lit_small; lia | exact Hing | exact Hing2 | lia
| change (req_size CGIF_SIZE) with 96; unfold CGIF_SIZE; lia | lia | intros a Ha (r & Hr & _); destruct Hr]. }
clear HS1. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E 38 (map (getr regs2) CLOB)) as E2' eqn:HE2' in HS. assert (HEI2p : img_env VAL A_LIM E2') by (rewrite HE2'; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLD2 : forall n, (n < 38)%nat -> ew E2' n = ew E n) by (intros n Hn; rewrite HE2'; apply YN3v.ew_havoc_old; exact Hn).
assert (HAE2 : env_agree 32 (Ereg regs (rc_extra g rcur ctx)) E2') by (rewrite HE2'; apply env_agree_havoc_ge; [cbv; lia | exact HAE]).
clear HE2'.
assert (F1 : ew E2' 1 = getr regs 1) by (rewrite OLD2 by (cbv; lia); exact E1).
assert (F3 : ew E2' 3 = getr regs 3) by (rewrite OLD2 by (cbv; lia); exact E3).
assert (F4 : ew E2' 4 = getr regs 4) by (rewrite OLD2 by (cbv; lia); exact E4).
assert (F10 : ew E2' 10 = Z_to_bv 64 raw) by (rewrite OLD2 by (cbv; lia); exact E10).
assert (F32 : ew E2' 32 = Z_to_bv 64 g) by (rewrite OLD2 by (cbv; lia); exact E32).
assert (F35 : ew E2' 35 = Z_to_bv 64 SB) by (rewrite OLD2 by (cbv; lia); exact E35).
assert (Usp2 : bv_unsigned (ew E2' 2) = spZ regs) by (rewrite OLD2 by (cbv; lia); exact Usp).
lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msr) =>
pose proof (st_ok_pi_pin_reg' _ _ _ (10%bv : bv 5) 0 HS ltac:(cbn [ms_regs mkst restrict]; exact Ha0) eq_refl) as HS0 end.
clear HS. rename HS0 into HS.
lazymatch type of HS with st_ok_pi _ _ _ ?ss3 _ => let v := eval vm_compute in ss3 in change ss3 with v in HS end.
assert (SHOK : sh_ok SEGS Bx rc_SH E2' (mrestrict (w_H W2) mem2)).
{ unfold sh_ok, rc_SH. constructor; [|constructor; [|constructor]].
+ apply (shent_ok_of_block SEGS B LAWS ly2 S2 W2 mem2 md2 E2' Bx 10 raw RAW_SIZE 0 RAW_SIZE HAR2 Hinr2).
* unfold U, Bx. cbn [sv_denot]. rewrite F35, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
* unfold U. cbn [sv_denot]. rewrite F10, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by lia. reflexivity.
* lia.
* change (req_size RAW_SIZE) with 48. unfold RAW_SIZE. lia.
+ apply (shent_ok_of_block SEGS B LAWS ly2 S2 W2 mem2 md2 E2' Bx 32 g CGIF_SIZE 0 CGIF_SIZE HAR2 Hing2).
* unfold U, Bx. cbn [sv_denot]. rewrite F35, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
* unfold U. cbn [sv_denot]. rewrite F32, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by lia. reflexivity.
* lia.
* change (req_size CGIF_SIZE) with 96. unfold CGIF_SIZE. lia. }
paj_run_tok RUN HS HJ2 SHOK Bspan. { awr_ok_tac; exact Usp2. }
pose proof (proj1 HJ2) as HARd.
destruct (al_const _ _ LAWS _ _ _ _ _ HARd) as (Kcelld & _ & Kgotd & _). rewrite HBgot, HBcell in Kgotd. rewrite HBcell in Kcelld.
lazymatch goal with |- SRr _ _ (mkCfg ?ms ?mdc) _ =>
prreg HS (2%bv : bv 5) R2; prreg HS (10%bv : bv 5) R10; prreg HS (3%bv : bv 5) R3; prreg HS (4%bv : bv 5) R4;
prreg HS (1%bv : bv 5) R1; prreg HS (8%bv : bv 5) R8;
eapply SRr_bind;
[ eapply (aj_free SEGS B LAWS Hsegs errno_low ML AFREE W2 E2' _ ms TRAWCLOSE_STK (spZ regs) _ ly S W mem md [] ly2 S2 _ (0 + 0)
raw RAW_SIZE (-32) (ew E2' 2) (Z_to_bv 64 (BASE + 0x25a8)) []);
[ exact HS | exact HBfree | reflexivity | exact HJ2 | exact Hinr2
| rewrite R10, F10; reflexivity
| exact (st_ok_restrict_reg SEGS (w_H W2) E2' _ _ 2%bv HS)
| reflexivity | exact Usp2 | reflexivity | lia | unfold TRAWCLOSE_STK; lia
| rewrite R3, F3; exact Hgp | rewrite R4, F4; exact Htp
| exact R1 | apply ret_ok_codeptr_v; [lia | reflexivity] | destruct HJ2 as (_ & _ & _ & _ & _ & _ & Hnev2 & _); rewrite HEV in Hev; lia
| eapply (achain_chain_pre ly2 _ (spZ regs - 32) raw []);
[ apply achain_low; lia
| change (spZ (ms_regs ms)) with (bv_unsigned (getr (ms_regs ms) 2)); rewrite R2, unsigned_lit_small by lia; lia
| unfold s0Z; rewrite R8, F10; apply unsigned_lit_small; lia
| unfold raZ; rewrite R1; rewrite unsigned_lit_small by lia; lia ]
| rewrite call_trace_nil; unfold raZ; rewrite R1, unsigned_lit_small by lia; rewrite (proj2 (Z.eqb_neq _ _)) by (pose proof (proj1 (pal_rt_below B TL)); lia); exact HU1
| intros _ i Hi; apply (inFP_ablocks_fp _ raw RAW_SIZE i); [left; reflexivity | exact Hi] ]
| ]
end.
clear HJ2 SHOK R2 R10 R3 R4 R1 R8.
intros W3 c3 Hwle3 (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & HP3 & (l1 & l2 & Ebl & Ebl2) & Hfrs3 & HK3).
pose proof (proj1 HJ3) as HAR3.
destruct (al_const _ _ LAWS _ _ _ _ _ HAR3) as (Kcell3 & _ & Kgot3 & _). rewrite HBgot, HBcell in Kgot3. rewrite HBcell in Kcell3.
assert (HPerm3 : Permutation (ablocks B ly3 S3) ((g, CGIF_SIZE) :: rest)).
{ rewrite Ebl2. apply Permutation_sym. apply (@Permutation_cons_app_inv _ _ l1 l2 (raw, RAW_SIZE)). rewrite <- Ebl.
apply Permutation_sym. exact HPerm2. }
assert (Hing3 : In (g, CGIF_SIZE) (ablocks B ly3 S3)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm3|]; left; reflexivity).
jafter_call_keep_pi HS 54%nat regs3 (mrestrict (w_H W3) mem3) HP3 [0; 1; 2; 4]%nat HS3.
match type of HS3 with ?tq -> _ => assert (HRK : tq); [|specialize (HS3 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; [| | | | apply Forall_nil].
- eapply (region_kept_stack_aj SEGS B); [exact HK3 | exact HJ3 | exact Usp2 | lia | unfold TRAWCLOSE_STK, ASTACK; lia | lia | lia | lia].
- apply (region_kept_val_at E2' _ _ (A_OBJ 0) (VAL (A_OBJ 0)) 8 (VAL (A_OBJ 12)));
[exact (HEI2p (A_OBJ 0) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) | exact (val_mem_of_rdword SEGS _ _ _ _ Kgotd) | exact (val_mem_of_rdword SEGS _ _ _ _ Kgot3) | lia].
- apply (region_kept_val_at E2' _ _ (A_OBJ 12) (VAL (A_OBJ 12)) 8 SHADOW_OFF);
[exact (HEI2p (A_OBJ 12) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) | exact (val_mem_of_rdword SEGS _ _ _ _ Kcelld) | exact (val_mem_of_rdword SEGS _ _ _ _ Kcell3) | lia].
- eapply (region_kept_block_aj SEGS B); [exact HK3 | rewrite F32; apply unsigned_lit_small; lia | exact Hing2 | lia
| change (req_size CGIF_SIZE) with 96; unfold CGIF_SIZE; lia | lia | unfold CGIF_SIZE; intros a Ha HE'; change (req_size RAW_SIZE) with 48 in HE'; lia]. }
clear HS. rewrite <- restrict_mkst_fx in HS3. rename HS3 into HS.
remember (havoc E2' 54 (map (getr regs3) CLOB)) as E3' eqn:HE3' in HS. assert (HEI3p : img_env VAL A_LIM E3') by (rewrite HE3'; apply img_env_havoc; [exact HEI2p | cbv; lia]).
assert (OLD3 : forall n, (n < 54)%nat -> ew E3' n = ew E2' n) by (intros n Hn; rewrite HE3'; apply YN3v.ew_havoc_old; exact Hn).
assert (HAE3 : env_agree 32 (Ereg regs (rc_extra g rcur ctx)) E3') by (rewrite HE3'; apply env_agree_havoc_ge; [cbv; lia | exact HAE2]).
clear HE3'.
assert (G1 : ew E3' 1 = getr regs 1) by (rewrite OLD3 by (cbv; lia); exact F1).
assert (Usp3 : bv_unsigned (ew E3' 2) = spZ regs) by (rewrite OLD3 by (cbv; lia); exact Usp2).
shok_auto SHOK Bx E3' (mrestrict (w_H W3) mem3).
paj_run_tok RUN HS HJ3 SHOK Bspan. { awr_ok_tac. exact Usp3. }
prreg HS (1%bv : bv 5) R1.
eapply (RET W3 _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'. lazymatch goal with |- apost_base _ _ _ _ _ _ _ _ _ _ _ _ _ (mkCfg (mkst ?r _ ?m _) ?d) => exists ly3, S3, r, m, d end.
split; [cbn [ms_regs]; rewrite R1, G1, Hra; reflexivity|].
split; [|split].
- cbn [ms_mem]. rewrite HEV. apply (ajournal_materialize SEGS B LAWS Hsegs). exact HJ3.
- eapply (aregs_preserved_of_st_ok SEGS _ E3' _ _ regs (rc_extra g rcur ctx) HS); [exact HAE3 | vm_compute; reflexivity].
- exact HPerm3.
Qed.
End RC.
End c.
End b.
