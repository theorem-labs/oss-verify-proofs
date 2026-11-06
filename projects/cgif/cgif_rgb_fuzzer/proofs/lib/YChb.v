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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00 YI02 YI01.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YC01 YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YG00 YG0a YG01 YG0h YG0u YG0d YCcz.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB1u YF9i YCeb YCe8 YCfq YCdy YCfr YCe9.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Definition A_GOT_rawadd : Z := 0xa3ed8.
Definition A_stack_malloc_1 : Z := 0x3d170.
Section b. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Definition RABx : sv := SOff 40 0.
Definition RABspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition ra_extra (g gct rattr Wd Hd sgct loops rcur lct img fattr w h top left delay slct disp tidx ctx : Z) : list word :=
map (Z_to_bv 64) [g; gct; rattr; Wd; Hd; sgct; loops; rcur; SB; lct; img; fattr; w; h; top; left; delay; slct; disp; tidx; ctx].
Definition ra_raw_region : YQ0b.region :=
YQ0b.mkRegion (Some 10%nat) 0 48 40 44
[YQ0b.mkChunk 0 (CVal 8 (SLit A_cgif_writecb)); YQ0b.mkChunk 8 (CVal 8 (SOff 32 0)); YQ0b.mkChunk 16 (CVal 8 (SOff 33 0));
YQ0b.mkChunk 24 (CVal 4 (SOff 34 0)); YQ0b.mkChunk 28 (CVal 2 (SOff 35 0)); YQ0b.mkChunk 30 (CVal 2 (SOff 36 0));
YQ0b.mkChunk 32 (CVal 2 (SOff 37 0)); YQ0b.mkChunk 34 (CVal 2 (SOff 38 0)); YQ0b.mkChunk 40 (CVal 4 (SOff 39 0))].
Definition ra_cfg_region : YQ0b.region :=
YQ0b.mkRegion (Some 11%nat) 0 40 0 0
[YQ0b.mkChunk 0 (CVal 8 (SOff 41 0)); YQ0b.mkChunk 8 (CVal 8 (SOff 42 0)); YQ0b.mkChunk 16 (CVal 4 (SOff 43 0));
YQ0b.mkChunk 20 (CVal 2 (SOff 44 0)); YQ0b.mkChunk 22 (CVal 2 (SOff 45 0)); YQ0b.mkChunk 24 (CVal 2 (SOff 46 0));
YQ0b.mkChunk 26 (CVal 2 (SOff 47 0)); YQ0b.mkChunk 28 (CVal 2 (SOff 48 0)); YQ0b.mkChunk 30 (CVal 2 (SOff 49 0));
YQ0b.mkChunk 32 (CVal 1 (SOff 50 0)); YQ0b.mkChunk 33 (CVal 1 (SOff 51 0))].
Definition ra_g_region : YQ0b.region :=
YQ0b.mkRegion (Some 32%nat) 0 CGIF_SIZE 0 0
[YQ0b.mkChunk 56 (CVal 8 (SLit A_writecb)); YQ0b.mkChunk 64 (CVal 8 (SOff 52 0)); YQ0b.mkChunk 80 (CVal 8 (SLit 0))].
Definition ra_regions0 : smem :=
[ stack_region 320; got_region; bcell_region 40; uar_got_region; uar_cell_region; const8_region A_GOT_rawadd A_cgif_raw_addframe;
ra_raw_region; ra_cfg_region; ra_g_region ].
Definition ra_atoms0 : list (nat * afact) :=
[ (2%nat, mkAF (2^46) (2^47) 5); (10%nat, HPTR 4); (11%nat, HPTR 3); (32%nat, HPTR 4);
(33%nat, mkAF 0 (2^64 - 1) 0); (34%nat, mkAF 0 (2^32 - 1) 0); (35%nat, mkAF 0 65535 0); (36%nat, mkAF 0 65535 0);
(37%nat, mkAF 0 256 0); (38%nat, mkAF 0 65535 0); (39%nat, mkAF 0 (2^32 - 1) 0); (40%nat, mkAF SB SB 0);
(41%nat, mkAF 0 (2^64 - 1) 0); (42%nat, HPTR 4); (43%nat, mkAF 0 (2^32 - 1) 0); (44%nat, mkAF 1 65535 0); (45%nat, mkAF 1 65535 0);
(46%nat, mkAF 0 65535 0); (47%nat, mkAF 0 65535 0); (48%nat, mkAF 0 65535 0); (49%nat, mkAF 0 65535 0);
(50%nat, mkAF 0 255 0); (51%nat, mkAF 0 255 0); (52%nat, mkAF 0 (2^64 - 1) 0) ].
Definition ss_ra0 : sstate := mkSS A_cgif_raw_addframe sr_atoms ra_regions0 None (mkFacts ra_atoms0 [] []).
Lemma U_sext32 : forall E a r, U E a = r -> 0 <= r < 2 ^ 32 ->
U E (SExt true 32 a) = (if r <? 2 ^ 31 then r else r - 2 ^ 32 + 2 ^ 64).
Proof.
intros E a r Ha Hr. rewrite U_SExt, Ha. change (2 ^ Z.of_N 32) with (2 ^ 32). rewrite (Z.mod_small r) by lia.
unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 32) with (2 ^ 32). change (2 ^ 32 / 2) with (2 ^ 31).
destruct (Z.ltb_spec r (2 ^ 31)) as [Hl | Hh].
- rewrite (Z.mod_small (r + 2 ^ 31)) by lia. replace (r + 2 ^ 31 - 2 ^ 31) with r by lia. apply zcanon_id. unfold M64. lia.
- replace ((r + 2 ^ 31) mod 2 ^ 32) with (r + 2 ^ 31 - 2 ^ 32).
2:{ replace (r + 2 ^ 31) with ((r + 2 ^ 31 - 2 ^ 32) + 1 * 2 ^ 32) at 2 by lia. rewrite Z_mod_plus_full. rewrite Z.mod_small by lia. reflexivity. }
unfold zcanon, M64. replace (r + 2 ^ 31 - 2 ^ 32 - 2 ^ 31) with ((r - 2 ^ 32 + 2 ^ 64) + (-1) * 2 ^ 64) by lia.
rewrite Z_mod_plus_full. apply Z.mod_small. lia.
Qed.

Section RA.
Variable B : asyms.
Hypothesis TL : TrbLib B.
Hypothesis LAWS : AR_laws trbsegs B.
Let HBcode := tl_code B TL. Let HBgot := tl_got_shadow B TL. Let HBcell := tl_shadow_cell B TL.
Let HBguar := tl_got_uar B TL. Let HBuar := tl_uar_cell B TL.
Lemma ra_entry : forall W ly S regs mem md ch raw g cfp gct rattr Wd Hd sgct loops rcur ctx lct img fattr w h top left delay slct disp tidx Nimg rest,
afn_pre trbsegs B TRAWADD_STK ly S W regs mem md ch -> spZ regs mod 32 = 0 ->
arodata_ok B (aview trbsegs (w_H W) mem) ->
getr regs 10 = w64 raw -> getr regs 11 = w64 cfp ->
afobj B ly S W mem cfp 40 ->
obj_at trbsegs (mrestrict (w_H W) mem) cfp LAY_RawFrameConfig [lct; img; fattr; w; h; top; left; delay; slct; disp; tidx] ->
obj_at trbsegs (mrestrict (w_H W) mem) raw LAY_Raw [A_cgif_writecb; g; gct; rattr; Wd; Hd; sgct; loops; rcur] ->
sgct <= 256 ->
val_mem trbsegs (mrestrict (w_H W) mem) (g + 56) 8 A_writecb ->
val_mem trbsegs (mrestrict (w_H W) mem) (g + 64) 8 ctx -> 0 <= ctx < 2 ^ 64 ->
val_mem trbsegs (mrestrict (w_H W) mem) (g + 80) 8 0 ->
1 <= w -> 1 <= h -> w * h <= 100000000 -> w * h <= Nimg ->
Permutation (ablocks B ly S) ((raw, RAW_SIZE) :: (g, CGIF_SIZE) :: (img, Nimg) :: rest) ->
st_ok trbsegs (Ereg regs (ra_extra g gct rattr Wd Hd sgct loops rcur lct img fattr w h top left delay slct disp tidx ctx)) ss_ra0
(restrict (w_H W) (mkst regs (Z_to_bv 64 A_cgif_raw_addframe) mem (seg_rom trbsegs))).
Proof.
intros W ly S regs mem md ch raw g cfp gct rattr Wd Hd sgct loops rcur ctx lct img fattr w h top left delay slct disp tidx Nimg rest
HPRE Hal32 HROD H10 H11 HFO Hcfg Hraw Hsg Mgw Mgf Rctx Mg80 Hw Hh HnP HnPN HPerm.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (FFS : TRAWADD_STK = 17040) by reflexivity.
destruct HFO as ((cid & pos & Hfin & Hcid0 & Hfal & Hflo & Hfhi) & Hcal & HRA).
destruct (frames_bounds trbsegs B LAWS ly S W mem md cid pos HAR Hfin) as (Hf4096 & Hfceil & Hfhigh).
pose proof (frm_off_img _ _ _ _ _ _ _ _ HAR Hfin) as Hfhigh_img.
assert (Hraw_in : In (raw, RAW_SIZE) (ablocks B ly S)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm|]; left; reflexivity).
assert (Hing : In (g, CGIF_SIZE) (ablocks B ly S)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm|]; right; left; reflexivity).
assert (Himg : In (img, Nimg) (ablocks B ly S)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm|]; right; right; left; reflexivity).
destruct (al_blocks _ _ LAWS ly S W mem md g CGIF_SIZE HAR Hing) as (Hg16 & Hg4096 & Hgceil & Hgh_ia & _ & _). pose proof (proj1 Hgh_ia) as Hgh.
pose proof (blk_off_img _ _ _ _ _ _ g CGIF_SIZE HAR Hing) as Hgh_img.
destruct (al_blocks _ _ LAWS ly S W mem md raw RAW_SIZE HAR Hraw_in) as (Hr16 & Hr4096 & Hrceil & [Hrh Hrapp] & Hrpres & _).
pose proof (blk_off_img _ _ _ _ _ _ raw RAW_SIZE HAR Hraw_in) as Hrh_img.
destruct (al_blocks _ _ LAWS ly S W mem md img Nimg HAR Himg) as (Hi16 & Hi4096 & Hiceil & Hih_ia & _ & _). pose proof (proj1 Hih_ia) as Hih.
pose proof (blk_off_img _ _ _ _ _ _ img Nimg HAR Himg) as Hih_img.
change (req_size CGIF_SIZE) with 96 in *. change (req_size RAW_SIZE) with 48 in *.
assert (Hqi : 1 <= req_size Nimg) by (unfold req_size; destruct (Z.eqb_spec Nimg 0); lia).
destruct (al_const _ _ LAWS ly S W mem md HAR) as (Kcell & Kuar & Kgot & Kguar).
rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell. rewrite HBguar, HBuar in Kguar. rewrite HBuar in Kuar.
pose proof (sep_blocks_perm trbsegs B LAWS ly S W mem md (raw, RAW_SIZE) (g, CGIF_SIZE) _ HAR HPerm) as Srg.
assert (HPerm2 : Permutation (ablocks B ly S) ((raw, RAW_SIZE) :: (img, Nimg) :: (g, CGIF_SIZE) :: rest)).
{ eapply Permutation_trans; [exact HPerm|]. apply perm_skip. apply perm_swap. }
pose proof (sep_blocks_perm trbsegs B LAWS ly S W mem md (raw, RAW_SIZE) (img, Nimg) _ HAR HPerm2) as Sri.
assert (HPerm3 : Permutation (ablocks B ly S) ((g, CGIF_SIZE) :: (img, Nimg) :: (raw, RAW_SIZE) :: rest)).
{ eapply Permutation_trans; [exact HPerm|]. eapply Permutation_trans; [apply perm_swap|]. apply perm_skip. apply perm_swap. }
pose proof (sep_blocks_perm trbsegs B LAWS ly S W mem md (g, CGIF_SIZE) (img, Nimg) _ HAR HPerm3) as Sgi.
unfold zdisjoint, block_rng in Srg, Sri, Sgi. cbn [fst snd] in Srg, Sri, Sgi. change (req_size RAW_SIZE) with 48 in Srg, Sri. change (req_size CGIF_SIZE) with 96 in Srg, Sgi.
pose proof (sep_block_frame trbsegs B LAWS ly S W mem md raw RAW_SIZE cid pos HAR Hraw_in Hfin) as Frc.
pose proof (sep_block_frame trbsegs B LAWS ly S W mem md g CGIF_SIZE cid pos HAR Hing Hfin) as Fgc.
unfold zdisjoint in Frc, Fgc. cbn [fst snd] in Frc, Fgc. change (req_size RAW_SIZE) with 48 in Frc. change (req_size CGIF_SIZE) with 96 in Fgc.
pose proof Hcfg as Hc'. cbn [obj_at LAY_RawFrameConfig] in Hc'.
destruct Hc' as ([V0 R0] & [V8 R8] & [V16 R16] & [V20 R20] & [V22 R22] & [V24 R24] & [V26 R26] & [V28 R28] & [V30 R30] & [V32 R32] & [V33 R33] & _).
cbn [fst snd N.to_nat Z.of_N] in V0, V8, V16, V20, V22, V24, V26, V28, V30, V32, V33, R0, R8, R16, R20, R22, R24, R26, R28, R30, R32, R33.
pose proof Hraw as Hq'. cbn [obj_at LAY_Raw LAY_RawConfig app] in Hq'.
destruct Hq' as ([Q0 _] & [Q8 T8] & [Q16 T16] & [Q24 T24] & [Q28 T28] & [Q30 T30] & [Q32 T32] & [Q34 T34] & [Q40 T40] & _).
cbn [fst snd N.to_nat Z.of_N] in Q0, Q8, Q16, Q24, Q28, Q30, Q32, Q34, Q40, T8, T16, T24, T28, T30, T32, T34, T40.
change (2 ^ (8 * 8)) with (2 ^ 64) in *. change (2 ^ (8 * 4)) with (2 ^ 32) in *. change (2 ^ (8 * 2)) with 65536 in *. change (2 ^ (8 * 1)) with 256 in *.
rewrite restrict_mkst_fx.
set (E := Ereg regs (ra_extra g gct rattr Wd Hd sgct loops rcur lct img fattr w h top left delay slct disp tidx ctx)).
assert (E2 : ew E 2 = getr regs 2) by (subst E; exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 raw) by (subst E; rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E11 : ew E 11 = Z_to_bv 64 cfp) by (subst E; rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (EX : forall j, ew E (32 + j) = nth j (ra_extra g gct rattr Wd Hd sgct loops rcur lct img fattr w h top left delay slct disp tidx ctx) (Z_to_bv 64 0)) by (intros j; subst E; apply ew_Ereg_extra).
pose proof (EX 0%nat) as E32. pose proof (EX 1%nat) as E33. pose proof (EX 2%nat) as E34. pose proof (EX 3%nat) as E35.
pose proof (EX 4%nat) as E36. pose proof (EX 5%nat) as E37. pose proof (EX 6%nat) as E38. pose proof (EX 7%nat) as E39. pose proof (EX 8%nat) as E40.
pose proof (EX 9%nat) as E41. pose proof (EX 10%nat) as E42. pose proof (EX 11%nat) as E43. pose proof (EX 12%nat) as E44. pose proof (EX 13%nat) as E45.
pose proof (EX 14%nat) as E46. pose proof (EX 15%nat) as E47. pose proof (EX 16%nat) as E48. pose proof (EX 17%nat) as E49. pose proof (EX 18%nat) as E50.
pose proof (EX 19%nat) as E51. pose proof (EX 20%nat) as E52.
cbn [Nat.add nth ra_extra map] in E32, E33, E34, E35, E36, E37, E38, E39, E40, E41, E42, E43, E44, E45, E46, E47, E48, E49, E50, E51, E52. clear EX.
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
Local Ltac ck HE M := eapply chunk_ok_val; [ cbn [sv_denot]; rewrite HE, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | first [exact M | rewrite Z.add_0_r; exact M] ].
unfold ss_ra0. apply (entry_st_ok_full trbsegs); change (Ereg regs (ra_extra g gct rattr Wd Hd sgct loops rcur lct img fattr w h top left delay slct disp tidx ctx)) with E.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- unfold ra_regions0, stack_region, got_region, bcell_region, uar_got_region, uar_cell_region, const8_region, ra_raw_region, ra_cfg_region, ra_g_region.
repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks].
+ cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
intros o Ho. apply (apresent_writable trbsegs). apply Hpres. lia.
+ cbn [base_val]. unfold A_GOT_shadow. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor]. rewrite <- (Z.add_0_l 668240) at 1.
apply (chunk_ok_val trbsegs E _ 0 668240 8 (SLit A_shadow_glob) A_shadow_glob); [reflexivity | unfold A_shadow_glob; zside | zside |].
exact (val_mem_of_rdword trbsegs (w_H W) mem _ _ Kgot).
+ cbn [base_val]. unfold A_shadow_glob. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor]. rewrite <- (Z.add_0_l 701048) at 1.
apply (chunk_ok_val trbsegs E _ 0 701048 8 (SOff 40 0) SB);
[cbn [sv_denot]; rewrite E40, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | zside |].
exact (val_mem_of_rdword trbsegs (w_H W) mem _ _ Kcell).
+ cbn [base_val]. unfold A_GOT_uar. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor]. rewrite <- (Z.add_0_l 668328) at 1.
apply (chunk_ok_val trbsegs E _ 0 668328 8 (SLit A_uar_glob) A_uar_glob); [reflexivity | unfold A_uar_glob; zside | zside |].
exact (val_mem_of_rdword trbsegs (w_H W) mem _ _ Kguar).
+ cbn [base_val]. unfold A_uar_glob. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor]. rewrite <- (Z.add_0_l 701056) at 1.
apply (chunk_ok_val trbsegs E _ 0 701056 4 (SLit 1) 1); [reflexivity | zside | zside |].
exact (val_mem_of_rd32 trbsegs (w_H W) mem _ _ Kuar).
+ cbn [base_val]. unfold A_GOT_rawadd. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor]. rewrite <- (Z.add_0_l 671448) at 1.
apply (chunk_ok_val trbsegs E _ 0 671448 8 (SLit A_cgif_raw_addframe) A_cgif_raw_addframe); [reflexivity | unfold A_cgif_raw_addframe; zside | zside |].
eapply (arodata_val8 B (w_H W) mem 671448 A_cgif_raw_addframe TL HROD); [lia | lia | intros x Hx; unfold lib_const_addr; lia |].
intros k Hk. do 8 (destruct k as [|k]; [vm_compute; reflexivity|]). lia.
+ rewrite (VB 10%nat raw E10) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; apply (apresent_writable trbsegs); apply (proj1 (Hrpres (raw + o) ltac:(lia)))|].
constructor; [apply (chunk_ok_val trbsegs E _ raw 0 8 _ A_cgif_writecb); [reflexivity | unfold A_cgif_writecb; zside | zside | exact Q0]|].
constructor; [ck E32 Q8|]. constructor; [ck E33 Q16|]. constructor; [ck E34 Q24|]. constructor; [ck E35 Q28|].
constructor; [ck E36 Q30|]. constructor; [ck E37 Q32|]. constructor; [ck E38 Q34|]. constructor; [ck E39 Q40|]. constructor.
+ rewrite (VB 11%nat cfp E11) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [ck E41 V0|]. constructor; [ck E42 V8|]. constructor; [ck E43 V16|]. constructor; [ck E44 V20|].
constructor; [ck E45 V22|]. constructor; [ck E46 V24|]. constructor; [ck E47 V26|]. constructor; [ck E48 V28|].
constructor; [ck E49 V30|]. constructor; [ck E50 V32|]. constructor; [ck E51 V33|]. constructor.
+ rewrite (VB 32%nat g E32) by lia. unfold CGIF_SIZE. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [apply (chunk_ok_val trbsegs E _ g 56 8 _ A_writecb); [reflexivity | unfold A_writecb; zside | zside | exact Mgw]|].
constructor; [ck E52 Mgf|].
constructor; [apply (chunk_ok_val trbsegs E _ g 80 8 _ 0); [reflexivity | zside | zside | exact Mg80] | constructor].
- apply pairwise_disjoint_of_extents.
unfold ra_regions0, stack_region, got_region, bcell_region, uar_got_region, uar_cell_region, const8_region, ra_raw_region, ra_cfg_region, ra_g_region, extent_of_region.
cbn [map YQ0b.r_base YQ0b.r_lo YQ0b.r_hi]. rewrite (VB 10%nat raw E10), (VB 11%nat cfp E11), (VB 32%nat g E32) by lia. cbn [base_val]. rewrite Usp.
unfold A_GOT_shadow, A_shadow_glob, A_GOT_uar, A_uar_glob, A_GOT_rawadd, CGIF_SIZE.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
assert (Hgf : cfp + 40 <= g \/ g + 96 <= cfp) by lia.
assert (Hrf : cfp + 40 <= raw \/ raw + 48 <= cfp) by lia.
revert Hslo Hshi H47 Hceil Hgceil Hgh Hgh_img Hg4096 Hrceil Hrh Hrh_img Hr4096 Hfceil Hfhigh Hfhigh_img Hflo Hfhi Hgf Hrf Srg C1 C3 FFS Hstk0. clear. unfold zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kLowShadowBeg, kHighMemBeg. intros. repeat split; lia.
- split; [|split; [exact I | exact I]].
cbn [f_atoms atoms_ok ra_atoms0]. unfold afact_ok, HPTR. cbn [af_lo af_hi af_al2].
rewrite Usp, E10, E11, E32, E33, E34, E35, E36, E37, E38, E39, E40, E41, E42, E43, E44, E45, E46, E47, E48, E49, E50, E51, E52, !unsigned_lit_small by (unfold SB; lia).
change (2 ^ 5) with 32. change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
assert (Hc8 : cfp mod 8 = 0) by exact Hcal.
revert Hslo Hshi H47 Hceil Hgceil Hgh Hgh_img Hg4096 Hg16 Hrceil Hrh Hrh_img Hr4096 Hr16 Hiceil Hih Hih_img Hi4096 Hi16 Hqi Hfceil Hfhigh Hfhigh_img Hflo Hfhi Hal32 Hc8
R0 R8 R16 R20 R22 R24 R26 R28 R30 R32 R33 T8 T16 T24 T28 T30 T32 T34 T40 Hsg Rctx Hw Hh C1 C3 FFS Hstk0. clear. unfold SB, zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kLowShadowBeg, kHighMemBeg. intros.
repeat match goal with |- _ /\ _ => split end; lia.
Qed.
End RA.
End b.
