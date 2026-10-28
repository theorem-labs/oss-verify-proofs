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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04 YI09 YI08.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0d YP0c YI0w YI0y YC4a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC80 YC1f YC1g YC1h YC81 YC4b YC44 YC44.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACbk.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC20.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI16 YE00.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACab.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg lib_asan3_1_listing}.
Context {RO : YC20.ro_below_ofl (@pa_segs _ lib_asan3_1_listing PI) (@pa_relro_lo _ lib_asan3_1_listing PI) (@pa_relro_hi _ lib_asan3_1_listing PI)}.
#[local] Notation SEGS := (@pa_segs _ lib_asan3_1_listing PI).
#[local] Notation VAL := (@pa_val _ lib_asan3_1_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_asan3_1_listing PI).
#[local] Notation BASE := (@pa_val _ lib_asan3_1_listing PI A_TEXT).
Ltac eimg_low := rewrite ?Eimg_low by (unfold A_TEXT; lia).
Definition ra_extraX (g gct rattr Wd Hd sgct loops rcur lct img fattr w h top left delay slct disp tidx ctx wfn hw uar pf : Z) : list word :=
ra_extra g gct rattr Wd Hd sgct loops rcur lct img fattr w h top left delay slct disp tidx ctx wfn hw uar ++ map (Z_to_bv 64) [pf].
Definition ra_g_regionX : YP09.region :=
YP09.mkRegion (Some 32%nat) 0 CGIF_SIZE 0 0
[YP09.mkChunk 56 (CVal 8 (SOff 54 0)); YP09.mkChunk 64 (CVal 8 (SOff 52 0)); YP09.mkChunk 80 (CVal 8 (SOff 56 0))].
Definition ra_regions0X : smem :=
[ stack_region 320; got_regionP; bcell_regionP 40; uar_got_regionP 55; uar_cell_regionP 55; obj8_region 9 (SOff A_TEXT AF_asan3_cgif_raw_addframe);
ra_raw_region; ra_cfg_region; ra_g_regionX ].
Definition ra_atoms0X : list (nat * afact) :=
[ (2%nat, mkAF (2^46) (2^47) 5); (10%nat, HPTR 4); (11%nat, HPTR 3); (32%nat, HPTR 4);
(33%nat, mkAF 0 (2^64 - 1) 0); (34%nat, mkAF 0 (2^32 - 1) 0); (35%nat, mkAF 0 65535 0); (36%nat, mkAF 0 65535 0);
(37%nat, mkAF 0 256 0); (38%nat, mkAF 0 65535 0); (39%nat, mkAF 0 (2^32 - 1) 0); (40%nat, mkAF SB SB 0);
(41%nat, mkAF 0 (2^64 - 1) 0); (42%nat, HPTR 4); (43%nat, mkAF 0 (2^32 - 1) 0); (44%nat, mkAF 1 65535 0); (45%nat, mkAF 1 65535 0);
(46%nat, mkAF 0 65535 0); (47%nat, mkAF 0 65535 0); (48%nat, mkAF 0 65535 0); (49%nat, mkAF 0 65535 0);
(50%nat, mkAF 0 255 0); (51%nat, mkAF 0 255 0); (52%nat, mkAF 0 (2^64 - 1) 0);
(53%nat, mkAF 0 (2^64 - 1) 1); (54%nat, mkAF 0 (2^64 - 1) 0); (55%nat, mkAF 0x10000 0x5fb000 2) ].
Definition ss_ra0X : sstate := mkSS AF_asan3_cgif_raw_addframe sr_atoms ra_regions0X None (mkFacts ra_atoms0X [] []).
Section c.
Variable B : asyms.
Hypothesis TL : PALib B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TLF : PALibF B.
Variables wfn hw : Z.
Hypothesis Rwfn : 0 <= wfn < 2 ^ 64 /\ wfn mod 2 = 0.
Hypothesis Rhw : 0 <= hw < 2 ^ 64.
Hypothesis HGOT9 : forall (H : word -> bool) mem, arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS H mem) ->
val_mem SEGS (mrestrict H mem) (VAL (A_OBJ 9)) 8 (BASE + AF_asan3_cgif_raw_addframe).
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL. Let errno_low := pal_env B TL. Let HBfree := pal_free B TL. Let HBmalloc := pal_malloc B TL.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_asan3_1) (PI := PI).
Let PBASE := @pa_B_ok _ _ PI. Let PBLO := @pa_base_lo _ _ PL_asan3_1 PI.
Lemma ra_entryX : forall W ly S regs mem md ch raw g cfp gct rattr Wd Hd sgct loops rcur ctx lct img fattr w h top left delay slct disp tidx Nimg rest pf,
afn_pre SEGS B TRAWADD_STK ly S W regs mem md ch -> spZ regs mod 32 = 0 ->
arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) ->
getr regs 10 = w64 raw -> getr regs 11 = w64 cfp ->
afobj SEGS B ly S W mem cfp 40 ->
obj_at SEGS (mrestrict (w_H W) mem) cfp LAY_RawFrameConfig [lct; img; fattr; w; h; top; left; delay; slct; disp; tidx] ->
obj_at SEGS (mrestrict (w_H W) mem) raw LAY_Raw [wfn; g; gct; rattr; Wd; Hd; sgct; loops; rcur] ->
sgct <= 256 ->
val_mem SEGS (mrestrict (w_H W) mem) (g + 56) 8 hw ->
val_mem SEGS (mrestrict (w_H W) mem) (g + 64) 8 ctx -> 0 <= ctx < 2 ^ 64 ->
val_mem SEGS (mrestrict (w_H W) mem) (g + 80) 8 pf ->
1 <= w -> 1 <= h -> w * h <= 100000000 -> w * h <= Nimg ->
Permutation (ablocks B ly S) ((raw, RAW_SIZE) :: (g, CGIF_SIZE) :: (img, Nimg) :: rest) ->
In (pf, FILE_BLOCK) (ablocks B ly S) ->
st_ok_pi SEGS VAL (Eimg (Ereg regs (ra_extraX g gct rattr Wd Hd sgct loops rcur lct img fattr w h top left delay slct disp tidx ctx wfn hw (as_uar_cell B) pf))) ss_ra0X
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_asan3_cgif_raw_addframe)) mem (seg_rom SEGS))).
Proof.
intros W ly S regs mem md ch raw g cfp gct rattr Wd Hd sgct loops rcur ctx lct img fattr w h top left delay slct disp tidx Nimg rest pf
HPRE Hal32 HROD H10 H11 HFO Hcfg Hraw Hsg Mgw Mgf Rctx Mg80 Hw Hh HnP HnPN HPerm Hinf.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (FFS : TRAWADD_STK = 17040) by reflexivity.
destruct HFO as ((cid & pos & Hfin & Hcid0 & Hfal & Hflo & Hfhi) & Hcal & HRA).
destruct (frames_bounds SEGS B LAWS ly S W mem md cid pos HAR Hfin) as (Hf4096 & Hfceil & Hfhigh).
pose proof (frm_off_imgP _ _ _ _ _ _ _ _ HAR Hfin) as Hfhigh_img.
assert (Hraw_in : In (raw, RAW_SIZE) (ablocks B ly S)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm|]; left; reflexivity).
assert (Hing : In (g, CGIF_SIZE) (ablocks B ly S)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm|]; right; left; reflexivity).
assert (Himg : In (img, Nimg) (ablocks B ly S)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm|]; right; right; left; reflexivity).
destruct (al_blocks _ _ LAWS ly S W mem md g CGIF_SIZE HAR Hing) as (Hg16 & Hg4096 & Hgceil & Hgh_ia & _ & _). pose proof (proj1 Hgh_ia) as Hgh.
pose proof (blk_off_imgP _ _ _ _ _ _ g CGIF_SIZE HAR Hing) as Hgh_img.
destruct (al_blocks _ _ LAWS ly S W mem md raw RAW_SIZE HAR Hraw_in) as (Hr16 & Hr4096 & Hrceil & [Hrh Hrapp] & Hrpres & _).
pose proof (blk_off_imgP _ _ _ _ _ _ raw RAW_SIZE HAR Hraw_in) as Hrh_img.
destruct (al_blocks _ _ LAWS ly S W mem md img Nimg HAR Himg) as (Hi16 & Hi4096 & Hiceil & Hih_ia & _ & _). pose proof (proj1 Hih_ia) as Hih.
pose proof (blk_off_imgP _ _ _ _ _ _ img Nimg HAR Himg) as Hih_img.
change (req_size CGIF_SIZE) with 96 in *. change (req_size RAW_SIZE) with 48 in *.
destruct (al_blocks _ _ LAWS ly S W mem md pf FILE_BLOCK HAR Hinf) as (Hp16 & Hp4096 & Hpceil & _). change (req_size FILE_BLOCK) with 1264 in *.
assert (Hqi : 1 <= req_size Nimg) by (unfold req_size; destruct (Z.eqb_spec Nimg 0); lia).
destruct (al_const _ _ LAWS ly S W mem md HAR) as (Kcell & Kuar & Kgot & Kguar).
rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell. rewrite (palf_got_uar B TLF) in Kguar.
pose proof (sep_blocks_perm SEGS B LAWS ly S W mem md (raw, RAW_SIZE) (g, CGIF_SIZE) _ HAR HPerm) as Srg.
assert (HPerm2 : Permutation (ablocks B ly S) ((raw, RAW_SIZE) :: (img, Nimg) :: (g, CGIF_SIZE) :: rest)).
{ eapply Permutation_trans; [exact HPerm|]. apply perm_skip. apply perm_swap. }
pose proof (sep_blocks_perm SEGS B LAWS ly S W mem md (raw, RAW_SIZE) (img, Nimg) _ HAR HPerm2) as Sri.
assert (HPerm3 : Permutation (ablocks B ly S) ((g, CGIF_SIZE) :: (img, Nimg) :: (raw, RAW_SIZE) :: rest)).
{ eapply Permutation_trans; [exact HPerm|]. eapply Permutation_trans; [apply perm_swap|]. apply perm_skip. apply perm_swap. }
pose proof (sep_blocks_perm SEGS B LAWS ly S W mem md (g, CGIF_SIZE) (img, Nimg) _ HAR HPerm3) as Sgi.
unfold zdisjoint, block_rng in Srg, Sri, Sgi. cbn [fst snd] in Srg, Sri, Sgi. change (req_size RAW_SIZE) with 48 in Srg, Sri. change (req_size CGIF_SIZE) with 96 in Srg, Sgi.
pose proof (sep_block_frame SEGS B LAWS ly S W mem md raw RAW_SIZE cid pos HAR Hraw_in Hfin) as Frc.
pose proof (sep_block_frame SEGS B LAWS ly S W mem md g CGIF_SIZE cid pos HAR Hing Hfin) as Fgc.
unfold zdisjoint in Frc, Fgc. cbn [fst snd] in Frc, Fgc. change (req_size RAW_SIZE) with 48 in Frc. change (req_size CGIF_SIZE) with 96 in Fgc.
pose proof Hcfg as Hc'. cbn [obj_at LAY_RawFrameConfig] in Hc'.
destruct Hc' as ([V0 R0] & [V8 R8] & [V16 R16] & [V20 R20] & [V22 R22] & [V24 R24] & [V26 R26] & [V28 R28] & [V30 R30] & [V32 R32] & [V33 R33] & _).
cbn [fst snd N.to_nat Z.of_N] in V0, V8, V16, V20, V22, V24, V26, V28, V30, V32, V33, R0, R8, R16, R20, R22, R24, R26, R28, R30, R32, R33.
pose proof Hraw as Hq'. cbn [obj_at LAY_Raw LAY_RawConfig app] in Hq'.
destruct Hq' as ([Q0 _] & [Q8 T8] & [Q16 T16] & [Q24 T24] & [Q28 T28] & [Q30 T30] & [Q32 T32] & [Q34 T34] & [Q40 T40] & _).
cbn [fst snd N.to_nat Z.of_N] in Q0, Q8, Q16, Q24, Q28, Q30, Q32, Q34, Q40, T8, T16, T24, T28, T30, T32, T34, T40.
change (2 ^ (8 * 8)) with (2 ^ 64) in *. change (2 ^ (8 * 4)) with (2 ^ 32) in *. change (2 ^ (8 * 2)) with 65536 in *. change (2 ^ (8 * 1)) with 256 in *.
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs (ra_extraX g gct rattr Wd Hd sgct loops rcur lct img fattr w h top left delay slct disp tidx ctx wfn hw (as_uar_cell B) pf))). pose proof pa_B_ok as HBASE.
assert (E2 : ew E 2 = getr regs 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 raw) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E11 : ew E 11 = Z_to_bv 64 cfp) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (EX : forall j, (j < 25)%nat -> ew E (32 + j) = nth j (ra_extraX g gct rattr Wd Hd sgct loops rcur lct img fattr w h top left delay slct disp tidx ctx wfn hw (as_uar_cell B) pf) (Z_to_bv 64 0))
by (intros j Hj; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 1%nat ltac:(lia)) as E33. pose proof (EX 2%nat ltac:(lia)) as E34. pose proof (EX 3%nat ltac:(lia)) as E35.
pose proof (EX 4%nat ltac:(lia)) as E36. pose proof (EX 5%nat ltac:(lia)) as E37. pose proof (EX 6%nat ltac:(lia)) as E38. pose proof (EX 7%nat ltac:(lia)) as E39.
pose proof (EX 8%nat ltac:(lia)) as E40. pose proof (EX 9%nat ltac:(lia)) as E41. pose proof (EX 10%nat ltac:(lia)) as E42. pose proof (EX 11%nat ltac:(lia)) as E43.
pose proof (EX 12%nat ltac:(lia)) as E44. pose proof (EX 13%nat ltac:(lia)) as E45. pose proof (EX 14%nat ltac:(lia)) as E46. pose proof (EX 15%nat ltac:(lia)) as E47.
pose proof (EX 16%nat ltac:(lia)) as E48. pose proof (EX 17%nat ltac:(lia)) as E49. pose proof (EX 18%nat ltac:(lia)) as E50. pose proof (EX 19%nat ltac:(lia)) as E51.
pose proof (EX 20%nat ltac:(lia)) as E52. pose proof (EX 21%nat ltac:(lia)) as E53. pose proof (EX 22%nat ltac:(lia)) as E54. pose proof (EX 23%nat ltac:(lia)) as E55.
pose proof (EX 24%nat ltac:(lia)) as E56.
cbn [Nat.add nth ra_extraX ra_extra map app] in E32, E33, E34, E35, E36, E37, E38, E39, E40, E41, E42, E43, E44, E45, E46, E47, E48, E49, E50, E51, E52, E53, E54, E55, E56. clear EX.
assert (E240 : ew E A_TEXT = Z_to_bv 64 BASE) by (subst E; apply Eimg_img; unfold A_TEXT, A_LIM; lia).
assert (E241 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E242 : ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E250 : ew E (A_OBJ 9) = Z_to_bv 64 (VAL (A_OBJ 9))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E253 : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
pose proof (pa_obj_img 0 ltac:(lia)) as Hob0. pose proof (pa_obj_img 1 ltac:(lia)) as Hob1. pose proof (pa_obj_img 9 ltac:(lia)) as Hob9.
pose proof (pa_obj_img 12 ltac:(lia)) as Hob12. pose proof (palf_uar_img B TLF) as Huar. pose proof (palf_uar_al B TLF) as Huar4.
pose proof (palf_sep B TLF) as Hsep. cbn [zseps zseps_from fst snd] in Hsep.
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
Local Ltac ck HE M := eapply chunk_ok_val; [ cbn [sv_denot]; rewrite HE, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | first [exact M | rewrite Z.add_0_r; exact M] ].
unfold ss_ra0X. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold ra_regions0X, ra_g_regionX, stack_region, got_regionP, bcell_regionP, uar_got_regionP, uar_cell_regionP, obj8_region, ra_raw_region, ra_cfg_region, ra_g_region.
repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
+ cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
+ rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (pose proof (pa_val_range (A_OBJ 0)); lia). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
[cbn [sv_denot]; rewrite E253, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | pose proof (pa_val_range (A_OBJ 12)); zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
+ rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) E253) by (pose proof (pa_val_range (A_OBJ 12)); lia). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 12)) 0 8 (SOff 40 0) SB);
[cbn [sv_denot]; rewrite E40, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
+ rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) E242) by (pose proof (pa_val_range (A_OBJ 1)); lia). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 1)) 0 8 (SOff 55 0) (as_uar_cell B));
[cbn [sv_denot]; rewrite E55, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kguar).
+ rewrite (VB 55%nat (as_uar_cell B) E55) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (as_uar_cell B) 0 4 (SLit 1) 1); [reflexivity | zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rd32 SEGS (w_H W) mem _ _ Kuar).
+ rewrite (VB (A_OBJ 9) (VAL (A_OBJ 9)) E250) by (pose proof (pa_val_range (A_OBJ 9)); lia). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 9)) 0 8 (SOff A_TEXT AF_asan3_cgif_raw_addframe) (BASE + AF_asan3_cgif_raw_addframe));
[cbn [sv_denot]; rewrite E240, unsigned_lit_small by lia; reflexivity | unfold AF_asan3_cgif_raw_addframe; zside | zside |].
rewrite Z.add_0_r. exact (HGOT9 (w_H W) mem HROD).
+ rewrite (VB 10%nat raw E10) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; apply (apresent_writable SEGS); apply (proj1 (Hrpres (raw + o) ltac:(lia)))|].
constructor; [ck E53 Q0|].
constructor; [ck E32 Q8|]. constructor; [ck E33 Q16|]. constructor; [ck E34 Q24|]. constructor; [ck E35 Q28|].
constructor; [ck E36 Q30|]. constructor; [ck E37 Q32|]. constructor; [ck E38 Q34|]. constructor; [ck E39 Q40|]. constructor.
+ rewrite (VB 11%nat cfp E11) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [ck E41 V0|]. constructor; [ck E42 V8|]. constructor; [ck E43 V16|]. constructor; [ck E44 V20|].
constructor; [ck E45 V22|]. constructor; [ck E46 V24|]. constructor; [ck E47 V26|]. constructor; [ck E48 V28|].
constructor; [ck E49 V30|]. constructor; [ck E50 V32|]. constructor; [ck E51 V33|]. constructor.
+ rewrite (VB 32%nat g E32) by lia. unfold CGIF_SIZE. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [ck E54 Mgw|].
constructor; [ck E52 Mgf|].
constructor; [apply (chunk_ok_val SEGS E _ g 80 8 _ pf); [cbn [sv_denot]; rewrite E56, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Mg80] | constructor].
- apply pairwise_disjoint_of_extents.
unfold ra_regions0X, ra_g_regionX, stack_region, got_regionP, bcell_regionP, uar_got_regionP, uar_cell_regionP, obj8_region, ra_raw_region, ra_cfg_region, ra_g_region, extent_of_region.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite (VB 10%nat raw E10), (VB 11%nat cfp E11), (VB 32%nat g E32), (VB 55%nat (as_uar_cell B) E55) by lia.
rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (pose proof (pa_val_range (A_OBJ 0)); lia).
rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) E253) by (pose proof (pa_val_range (A_OBJ 12)); lia).
rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) E242) by (pose proof (pa_val_range (A_OBJ 1)); lia).
rewrite (VB (A_OBJ 9) (VAL (A_OBJ 9)) E250) by (pose proof (pa_val_range (A_OBJ 9)); lia).
cbn [base_val]. rewrite Usp. unfold CGIF_SIZE.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
assert (Hgf : cfp + 40 <= g \/ g + 96 <= cfp) by (revert Fgc Hflo Hfhi; clear; intros; lia).
assert (Hrf : cfp + 40 <= raw \/ raw + 48 <= cfp) by (revert Frc Hflo Hfhi; clear; intros; lia).
revert Hslo Hshi H47 Hceil Hgceil Hgh Hgh_img Hg4096 Hrceil Hrh Hrh_img Hr4096 Hfceil Hfhigh Hfhigh_img Hflo Hfhi Hgf Hrf Srg C1 C3 FFS Hstk0 Hob0 Hob1 Hob9 Hob12 Huar Hsep. clear. unfold zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kLowShadowBeg, kHighMemBeg. intros.
rewrite !Z.add_0_r. repeat match goal with H : _ /\ _ |- _ => destruct H as [? ?] end.
repeat split; first [ assumption | (apply or_comm; assumption)
| (repeat match goal with H : pa_val (A_OBJ _) + 8 <= _ \/ _ |- _ => clear H | H : as_uar_cell _ + 4 <= _ \/ _ |- _ => clear H end; lia) ].
- split; [|split; [exact I | exact I]].
cbn [f_atoms atoms_ok ra_atoms0X]. unfold afact_ok, HPTR. cbn [af_lo af_hi af_al2].
rewrite Usp, E10, E11, E32, E33, E34, E35, E36, E37, E38, E39, E40, E41, E42, E43, E44, E45, E46, E47, E48, E49, E50, E51, E52, E53, E54, E55, !unsigned_lit_small by (unfold SB; lia).
change (2 ^ 5) with 32. change (2 ^ 4) with 16. change (2 ^ 3) with 8. change (2 ^ 2) with 4. change (2 ^ 1) with 2. rewrite !Z.pow_0_r, !Z.mod_1_r.
assert (Hc8 : cfp mod 8 = 0) by exact Hcal.
revert Hslo Hshi H47 Hceil Hgceil Hgh Hgh_img Hg4096 Hg16 Hrceil Hrh Hrh_img Hr4096 Hr16 Hiceil Hih Hih_img Hi4096 Hi16 Hqi Hfceil Hfhigh Hfhigh_img Hflo Hfhi Hal32 Hc8
R0 R8 R16 R20 R22 R24 R26 R28 R30 R32 R33 T8 T16 T24 T28 T30 T32 T34 T40 Hsg Rctx Hw Hh C1 C3 FFS Hstk0 Huar Huar4 Rwfn Rhw. clear. unfold SB, zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kLowShadowBeg, kHighMemBeg. intros.
repeat match goal with |- _ /\ _ => split end; lia.
Qed.
End c.
End b.
End a.
