(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the walk of reac_ctrl_stamp_headamp on fuzz_grant.asan, written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACam.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACbf.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACf6.v, proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v, with its module paths, module names and numbers changed; 681 of its 854 lines of code are new or changed and 1105 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/Y/Prog/ClassifyCoreHead.v, with its module paths and module names changed; 162 of its 214 lines of code are new or changed and 802 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YA0o YCbm YA0q YG0s YC85 YC4b.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import JtokIs.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP09 YI04 YI09 YI08 YI00 YN3v YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0b YP0a YP0c YP0d YP07 YC80 YI0w YI0z YI12 YC4a YC8i YC1f.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YC8g YRo.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt Require Import ConstsViewDef StrlenDef MemchrDef.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_jscalar_model.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import JsonScalarCore.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg lib_both3_0_listing}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_both3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_0_listing PI A_TEXT).
#[local] Notation VAL := (@pa_val _ lib_both3_0_listing PI).
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.
Section h.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis ABCMP : forall fq : YK11.FPState, abcmp_realizes (fx := fq) SEGS B (SIGMA AS___interceptor_trampoline_bcmp).
Variables MC_CONSTS_LO MC_CONSTS_HI : Z.
Hypothesis ASTRLEN : forall fq : YK11.FPState, astrlen_realizesM (fx := fq) SEGS B MC_CONSTS_LO MC_CONSTS_HI (SIGMA AS___interceptor_trampoline_strlen).
Hypothesis AMEMCHR : forall fq : YK11.FPState, amemchr_realizesM (fx := fq) SEGS B MC_CONSTS_LO MC_CONSTS_HI (SIGMA AS___interceptor_trampoline_memchr).
Hypothesis MCROM : forall a, MC_CONSTS_LO <= a < MC_CONSTS_HI -> in_rom SEGS a.
Hypothesis GLOBS : globs_marked SEGS B tfib_globs.
Hypothesis IMGV : img_shadow_vis SEGS B.
Hypothesis ROU : tfib_ro_unowned B.
#[local] Notation tjson_scalar_str := (@tjson_scalar_str rc PI).
#[local] Notation tjson_scalar_img := (@tjson_scalar_img rc PI).

Section w.
Context {fx : YK11.FPState}.
Variables (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (Sa : astate) (W0 : world SEGS) (mem0 : word -> option byte)
  (md0 : Model) (own : list (Z * Z)) (lyc : alayout) (Sc : astate) (W : world SEGS) (memc : word -> option byte)
  (kk : Z) (b i n v spe : Z) (BS : list byte).
#[local] Notation BZ := (@BZ BS).
Hypothesis ZL : Z.of_nat (length BS) = n.
Hypothesis Zin : 0 <= i < n.
Hypothesis Zb0 : 0 < b.
Hypothesis Zbm : amem_range b n.
Hypothesis ZBg : garr8 SEGS (mrestrict (w_H W) memc) b BZ.
Hypothesis Zbra : range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF b n.
Hypothesis Zbsh : shadow_hull_vis (aview SEGS (w_H W) memc) b n.
Hypothesis Zbw : b + n <= spe - TJSON_SCALAR_STK \/ spe <= b.
Hypothesis Zboi : off_img b n.
Hypothesis Zbv : b + n <= v \/ v + 20 <= b.
Hypothesis Zv0 : 0 < v.
Hypothesis Zv8 : v mod 8 = 0.
Hypothesis Zvm : amem_range v 20.
Hypothesis Zvw : spe <= v \/ v + 20 <= spe - TJSON_SCALAR_STK.
Hypothesis Zvoi : off_img v 20.
Hypothesis Zvwr : forall a, v <= a < v + 20 ->
  awr_byte STK sp0 FP (ablocks B ly Sa) (ablocks B lyc Sc) lyc own a /\ apresent (w_H W) memc a.
Hypothesis Zvra : range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF v 20.
Hypothesis Zvsh : shadow_hull_vis (aview SEGS (w_H W) memc) v 20.
Hypothesis Zspa : alloc_ceiling <= spe - TJSON_SCALAR_STK.
Hypothesis Zsp47 : spe <= 2 ^ 47.
Hypothesis Zsp16 : spe mod 16 = 0.
Hypothesis ZspS : sp0 - STK <= spe - TJSON_SCALAR_STK.
Hypothesis Zsp0 : spe <= sp0.
Hypothesis Zsp016 : sp0 mod 16 = 0.
Hypothesis ZIMG : tjson_scalar_img W memc.
Hypothesis ZCV : consts_view SEGS MC_CONSTS_LO MC_CONSTS_HI W memc.
#[local] Notation JW := (@JW rc PI W memc spe).
#[local] Notation MK := (@MK rc PI W spe).
#[local] Notation SEGPOST := (@SEGPOST rc SK PI B fx STK sp0 FP ly Sa W0 mem0 md0 own lyc Sc W kk b v spe).
#[local] Notation js_nums := (@js_nums rc sp0 b i n v spe BS Zin Zbm Zbw Zbv Zv0 Zv8 Zvm Zvw Zspa Zsp47 Zsp16 Zsp0 Zsp016).
#[local] Notation jw_low := (@jw_low rc PI sp0 W memc i n v spe BS Zin Zv0 Zsp47).
#[local] Notation jw_of_mk := (@jw_of_mk rc PI sp0 W memc i n v spe BS Zin).
#[local] Notation mk_refl := (@mk_refl rc PI W spe).
#[local] Notation mk_trans := (@mk_trans rc PI W b i n v spe Zin Zbw Zbv Zvw).
#[local] Notation mk_frame := (@mk_frame rc PI sp0 W b i n v spe BS Zin Zbw Zbv Zvw).
#[local] Notation mk_call := (@mk_call rc PI sp0 W b i n v spe BS Zin Zb0 Zbw Zbv Zv0 Zvw Zsp16 Zsp0 Zsp016).
#[local] Notation seg_chain := (@seg_chain rc SK PI B fx STK sp0 FP ly Sa W0 mem0 md0 own lyc Sc W kk b i n v spe Zin Zbw Zbv Zvw).
#[local] Notation jw_B := (@jw_B rc PI sp0 W memc b i n v spe BS ZL Zin Zb0 Zbm ZBg Zbw Zbv Zv0 Zv8 Zvm Zvw Zspa Zsp47 Zsp16 Zsp0 Zsp016).
#[local] Notation jw_Bra := (@jw_Bra rc PI sp0 W memc b i n v spe BS Zin Zb0 Zbm Zbra Zbw Zbv Zv0 Zv8 Zvm Zvw Zspa Zsp47 Zsp16 Zsp0 Zsp016).
#[local] Notation jw_vra := (@jw_vra rc PI sp0 W memc b i n v spe BS Zin Zbm Zbw Zbv Zv0 Zv8 Zvm Zvw Zvra Zspa Zsp47 Zsp16 Zsp0 Zsp016).
#[local] Notation jw_vpres := (@jw_vpres rc PI B STK sp0 FP ly Sa own lyc Sc W memc v spe Zvwr).
#[local] Notation jw_cv := (@jw_cv rc PI MC_CONSTS_LO MC_CONSTS_HI MCROM sp0 W memc b i n v spe BS Zin Zbm Zbw Zbv Zv0 Zv8 Zvm Zvw Zspa Zsp47 Zsp16 Zsp0 Zsp016 ZCV).
#[local] Notation jw_imgaddr := (@jw_imgaddr rc PI sp0 W memc b i n v spe BS Zin Zbm Zbw Zbv Zv0 Zv8 Zvm Zvw Zspa Zsp47 Zsp16 Zsp0 Zsp016).
#[local] Notation jw_tstr := (@jw_tstr rc PI sp0 W memc b i n v spe BS Zin Zbm Zbw Zbv Zv0 Zv8 Zvm Zvw Zspa Zsp47 Zsp16 Zsp0 Zsp016).
#[local] Notation jw_litab := (@jw_litab rc PI sp0 W memc b i n v spe BS Zin Zbm Zbw Zbv Zv0 Zv8 Zvm Zvw Zspa Zsp47 Zsp16 Zsp0 Zsp016 ZIMG).
#[local] Notation jw_str14 := (@jw_str14 rc PI sp0 W memc b i n v spe BS Zin Zbm Zbw Zbv Zv0 Zv8 Zvm Zvw Zspa Zsp47 Zsp16 Zsp0 Zsp016 ZIMG).
#[local] Notation jstr_fuel := (@jstr_fuel sp0 i n v spe BS Zin).
#[local] Notation jstr_fuel_eq := (@jstr_fuel_eq sp0 i n v spe BS Zin Zv0).
#[local] Notation jstr_fuel_any := (@jstr_fuel_any sp0 i n v spe BS Zin Zv0).
#[local] Notation jdigits_fuel := (@jdigits_fuel sp0 i n v spe BS Zin).
#[local] Notation jdigits_fuel_any := (@jdigits_fuel_any sp0 i n v spe BS Zin Zv0).
#[local] Notation ew_EiR := (@ew_EiR rc PI sp0 i n v spe BS Zin).
#[local] Notation ew_EiX := (@ew_EiX rc PI sp0 i n v spe BS Zin).
#[local] Notation js_awr_v := (@js_awr_v rc PI B STK sp0 FP ly Sa own lyc Sc W memc v Zvwr).
#[local] Notation js_v_app := (@js_v_app rc sp0 i n v spe BS Zin Zv0 Zv8 Zvm).
#[local] Notation jrest_exp := (@jrest_exp i BS).
#[local] Notation jrest_frac := (@jrest_frac i BS).
#[local] Notation jx_extra := (@jx_extra b BS).
#[local] Notation jbyte_range := (@jbyte_range sp0 i n v spe BS Zin).
#[local] Notation garr8_at := (@garr8_at rc PI sp0 i n v spe BS Zin Zv0).
#[local] Notation st_ok_pi_add_cond := (@st_ok_pi_add_cond rc PI fx).
#[local] Notation U_offm := (@U_offm sp0 i n v spe BS Zin).
#[local] Notation z256 := (@z256 sp0 i n v spe BS Zin Zv0).
#[local] Notation bf_digit_ltu := (@bf_digit_ltu sp0 i n v spe BS Zin Zv0).
#[local] Notation jlen_BZ := (@jlen_BZ n BS ZL).
#[local] Notation jdigits_nd := (@jdigits_nd sp0 i n v spe BS ZL Zin Zv0).
#[local] Notation jdigits_d := (@jdigits_d sp0 i n v spe BS ZL Zin Zv0).
#[local] Notation jdigits_n := (@jdigits_n n BS ZL).
#[local] Notation jrest_exp_n := (@jrest_exp_n i n BS ZL).
#[local] Notation add_breg := (@add_breg rc PI fx sp0 W memc b i n v spe BS ZL Zin Zb0 Zbm ZBg Zbw Zbv Zv0 Zv8 Zvm Zvw Zspa Zsp47 Zsp16 Zsp0 Zsp016).
#[local] Notation obl_B := (@obl_B rc PI sp0 W memc b i n v spe BS Zin Zb0 Zbm Zbra Zbw Zbv Zv0 Zv8 Zvm Zvw Zspa Zsp47 Zsp16 Zsp0 Zsp016).
#[local] Notation jdig_at_ge := (@jdig_at_ge sp0 i n v spe BS ZL Zin).
#[local] Notation jdig_at_lt := (@jdig_at_lt sp0 i n v spe BS ZL Zin).
#[local] Notation jstr_ge := (@jstr_ge sp0 i n v spe BS ZL Zin).
#[local] Notation bf_hex2 := (@bf_hex2 sp0 i n v spe BS Zin Zv0).
#[local] Notation bf_hex1 := (@bf_hex1 sp0 i n v spe BS Zin Zv0).
#[local] Notation SLP := (@SLP rc SK PI B fx STK sp0 FP ly Sa W0 mem0 md0 own lyc Sc W memc kk b i n v spe BS).
#[local] Notation HXP := (@HXP rc SK PI B fx STK sp0 FP ly Sa W0 mem0 md0 own lyc Sc W memc kk b i n v spe).
#[local] Notation jm_extra := (@jm_extra b i BS).
Ltac ereg q r H := rewrite (ew_EiR _ _ q r) by (cbv; first [lia | reflexivity]); exact H.
Lemma jm_entry : forall (regs : bvmap 5 word) mdc,
  ajournal SEGS B STK sp0 FP ly Sa W0 mem0 md0 own lyc Sc W memc mdc kk ->
  getr regs 10 = w64 b -> getr regs 11 = w64 i -> getr regs 12 = w64 n -> getr regs 13 = w64 v -> spZ regs = spe ->
  st_ok_pi SEGS VAL (Eimg (Ereg regs jm_extra)) ss_jm
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_both3_json_scalar)) memc (seg_rom SEGS))).
Proof.
intros regs mdc HJ H10 H11 H12 H13 Hsp.
pose proof js_nums as (N1 & N2 & N3 & N4 & N5). pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
destruct (al_const _ _ LAWS lyc Sc W memc mdc HAR) as (Kcell & _ & Kgot & _). rewrite (pal_got_shadow B TL), (pal_cell B TL) in Kgot. rewrite (pal_cell B TL) in Kcell.
pose proof (pa_obj_img 12 ltac:(lia)) as HcellR. pose proof (pal_got_cell B TL) as HgcD. pose proof (pa_obj_img 0 ltac:(lia)) as HgotR.
unfold YImgTop.IMG_LO, YImgTop.IMG_TOP in HcellR, HgotR.
pose proof (jbyte_range i) as RBi.
destruct (garr8_at _ _ _ (i + 0) ZBg ltac:(unfold BZ; rewrite length_map; lia)) as [VB0 _]. rewrite Z.add_0_r in VB0.
pose proof Zboi as Hoi. unfold off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP in Hoi.
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs jm_extra)).
assert (E2 : ew E 2 = Z_to_bv 64 spe) by (subst E; rewrite (ew_EiR _ _ 2 (2%bv : bv 5)) by (cbv; first [lia | reflexivity]); unfold spZ in Hsp; rewrite <- Hsp; symmetry; apply Z_to_bv_bv_unsigned).
assert (E10 : ew E 10 = Z_to_bv 64 b) by (subst E; ereg 10%nat (10%bv : bv 5) H10).
assert (E11 : ew E 11 = Z_to_bv 64 i) by (subst E; ereg 11%nat (11%bv : bv 5) H11).
assert (E12 : ew E 12 = Z_to_bv 64 n) by (subst E; ereg 12%nat (12%bv : bv 5) H12).
assert (E13 : ew E 13 = Z_to_bv 64 v) by (subst E; ereg 13%nat (13%bv : bv 5) H13).
assert (E32 : ew E 32 = Z_to_bv 64 (b + i)) by (subst E; exact (ew_EiX regs jm_extra 0 ltac:(cbv; lia))).
assert (E33 : ew E 33 = Z_to_bv 64 (jbyte BZ i)) by (subst E; exact (ew_EiX regs jm_extra 1 ltac:(cbv; lia))).
assert (E34 : ew E 34 = Z_to_bv 64 (2 ^ 64 - 1 - b)) by (subst E; exact (ew_EiX regs jm_extra 2 ltac:(cbv; lia))).
assert (E35 : ew E 35 = Z_to_bv 64 SHADOW_OFF) by (subst E; exact (ew_EiX regs jm_extra 3 ltac:(cbv; lia))).
assert (E241 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E253 : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (VB : forall k v', ew E k = Z_to_bv 64 v' -> 0 <= v' < 2 ^ 64 -> base_val E (Some k) = v').
{ intros k v' Hk Hv. cbn [base_val]. rewrite Hk. apply unsigned_lit_small. exact Hv. }
unfold ss_jm. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold jm_regions, stack_region, got_regionP, bcell_regionP, breg.
  repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  + rewrite (VB 2%nat spe E2) by lia. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
  + rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
    [cbn [sv_denot]; rewrite E253, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) memc _ _ Kgot).
  + rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) E253) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 12)) 0 8 (SOff 35 0) SHADOW_OFF);
    [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SHADOW_OFF; zside | zside |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) memc _ _ Kcell).
  + rewrite (VB 32%nat (b + i) E32) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (b + i) 0 1 (SOff 33 0) (jbyte BZ i));
    [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | change (2 ^ (8 * Z.of_N 1)) with 256; lia | lia |].
    rewrite Z.add_0_r. exact VB0.
- apply pairwise_disjoint_of_extents. unfold jm_regions, stack_region, got_regionP, bcell_regionP, breg, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
  rewrite (VB 2%nat spe E2) by lia. rewrite (VB 32%nat (b + i) E32) by lia.
  rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by lia. rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) E253) by lia.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  pose proof Zbw. repeat split; lia.
- split; [|split].
  + cbn [jm_facts f_atoms atoms_ok]. unfold afact_ok, jSP, jPTR, jIDX, jVP, jSB, jNOTP, jBYTE. cbn [af_lo af_hi af_al2].
    rewrite E2, E10, E11, E12, E13, E32, E33, E34, E35, !unsigned_lit_small by (unfold SHADOW_OFF; lia).
    change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
    pose proof Zsp16. pose proof Zv8. unfold SHADOW_OFF. repeat split; lia.
  + cbn [jm_facts f_conds conds_ok]. split; [|exact I]. unfold acond_ok. cbn [ac_c ac_a ac_b].
    rewrite branch_ltu_U, (U_atom E 11 i E11), (U_atom E 12 n E12) by lia. apply Z.ltb_lt. lia.
  + cbn [jm_facts f_alias alias_ok]. split; [|split; [|exact I]].
    * apply U_inj. rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom E 10 b E10), (U_atom E 34 (2 ^ 64 - 1 - b) E34), U_SLit by lia.
      unfold zcanon, M64. change ((-1) mod 2 ^ 64) with (2 ^ 64 - 1).
      rewrite lxor_allones by lia. rewrite Z.mod_small by lia. reflexivity.
    * apply U_inj. rewrite U_SAlu. cbn [zalu_raw].
      rewrite (U_atom E 10 b E10), (U_atom E 11 i E11), (U_atom E 32 (b + i) E32) by lia. apply zcanon_id. unfold M64. lia.
Qed.
End w.
End h.
End f.
End d.
