(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS Require Import X0mx X0k2.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1da X1dg X1df X1ck.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1nt X1rh X1re.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1cg.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0bp X0j9 X0ec X001 X00b X04b X07z X05o X05p X05s X05l X09e X08y X06i.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X12c X14x X0r0 X0ra X0v9 X0yr X0wl X0zq X0xa.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14x OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0r0 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ra OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0v9 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0yr OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0wl OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0zq OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0xa.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section FpCPS.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Context {ptr : Type}.

Theorem forced_pitch_ltp : @ltp_unquant_cps RT ptr LtpForcedPitchUnquant.
Proof using AF.
intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
A D b EB e0 e32 pv pg start fin PAR off lo P0 N0 PD ND fq fa kq ka eb e32s pgs opv stk8
FDO MST -> -> -> -> -> -> -> -> -> REP OKB ST1 ST2 FIN OFF _ XE E0a E0b E4 INL PL PH X32 L32 XPV XPG LPG INQ (Q1 & Q2 & Q3 & Q4) (V1 & V2 & V3 & V4) (G1 & G2 & G3 & G4)
HXV HXG HVG INA (A1 & A2 & A3 & A4) IND DL DH HDP HAX HAV HAG ARGS ART0 MI0 FRM0 ST0 LOW LOR SPT SPA.
intros T c Hc Hk.
set (usp := bv_unsigned sp) in *.
assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned).
unfold entry_st in Hc. rewrite ESP in Hc. cbn [ltp_entryA ltp_pitch_span ltp_pitch ltp_bits] in *.
destruct (live_below_lo RT AF Σ m P0 N0 lo ART0 INL LOW) as (BL0 & BL1 & BL2).
destruct (live_facts RT AF Σ m P0 N0 ART0 INL) as (LP0 & _ & LI & LS).
destruct (frame_below_lo RT AF Σ m fq kq lo ART0 INQ LOW) as (FB1 & _ & _).
pose proof (frame_facts RT AF Σ m fq kq ART0 INQ) as (FQ0 & FQ64 & FQI & _ & FQS & _).
destruct (frame_live_apart RT AF Σ m fq kq P0 N0 ART0 INQ INL) as (FLA & _).
destruct (af_acc_live RT AF Σ m P0 N0 ART0 INL) as (_ & ACL).
pose proof (af_client_consts RT AF Σ m ART0) as CC0.
pose proof (pres_fp_refl (rt_live RT Σ) (rt_frames RT Σ) usp [(EB + 4 * e0, EB + 4 * e0 + 160); (e32, e32 + 160); (pv, pv + 4); (pg, pg + 12); (A, A + BITS_SIZEOF)] m) as PF.
pose proof (fun a => aclient_split RT AF Σ m usp a ART0) as SPL.
pose proof (rw_cells_bound _ _ _ _ XE) as BE. rewrite cells_size_f32 in BE.
cps_norm. unfold LTP_STACK, BITS_SIZEOF in *.
destruct REP as ((rj & Lrj & OBJ) & (bs & DAT & Hbs) & SIDE).
assert (Lbs : Z.of_nat (length bs) = sb_buf_size b) by (pose proof OKB as OK'; unfold bits_ok in OK'; rewrite Hbs, zlength_map_unsigned in OK'; clear - OK'; lia).
unfold bits_cells in OBJ. unfold ltp_args_cells in ARGS.
assert (FSZ : 64 <= fs_size kq) by (unfold fs_size; rewrite Z.shiftl_mul_pow2 by lia; pose proof (Z.pow_pos_nonneg 2 (Z.of_nat kq) ltac:(lia) ltac:(lia)); lia).
assert (T1 : P0 + N0 <= lo) by exact BL1. assert (T2 : lo <= usp) by lia. assert (T3 : usp <= 140737488355328) by lia. assert (T4 : EB + 4 * Z.of_nat (length eb) <= P0 + N0) by exact PH.
assert (OBE : aobj bsegs m EB (4 * Z.of_nat (length eb))) by (split; [lia|]; split; [unfold APP_TOP; lia|]; apply (acc_sub bsegs m P0 N0 _ _ ACL); lia).
assert (OB32 : aobj bsegs m e32 160) by (split; [lia|]; split; [unfold APP_TOP; lia| exact Q3]).
assert (OBPV : aobj bsegs m pv 4) by (split; [lia|]; split; [unfold APP_TOP; lia| exact V3]).
assert (OBPG : aobj bsegs m pg 12) by (split; [lia|]; split; [unfold APP_TOP; lia| exact G3]).
destruct (frame_live_apart RT AF Σ m fa ka P0 N0 ART0 INA INL) as (FLAA & _).
destruct (frame_live_apart RT AF Σ m fq kq PD ND ART0 INQ IND) as (FLQD & _).
destruct (live_below_lo RT AF Σ m PD ND lo ART0 IND LOW) as (BD0 & BD1 & _).
destruct (frame_below_lo RT AF Σ m fa ka lo ART0 INA LOW) as (FBA & _ & _).
cps_seg (forced_pitch_unquant_walk EB e0 e32 pv pg usp lo start (length eb) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m OBE OB32 OBPV OBPG E4 Q4 V4 G4).
{ unfold hidp, SH_LO, SH_HI. clear - LS PL PH. lia. }
{ unfold hidp, SH_LO, SH_HI. clear - FQS Q1 Q2 FSZ. lia. }
{ unfold hidp, SH_LO, SH_HI. clear - FQS V1 V2 FSZ. lia. }
{ unfold hidp, SH_LO, SH_HI. clear - FQS G1 G2 FSZ. lia. }
{ unfold hidp. clear - FLA PL PH Q1 Q2. lia. }
{ unfold hidp. clear - FLA PL PH V1 V2. lia. }
{ unfold hidp. clear - FLA PL PH G1 G2. lia. }
all: try (clear - LP0 PL; lia).
all: try (clear - FQ0 Q1; lia). all: try (clear - FQ0 V1; lia). all: try (clear - FQ0 G1; lia).
unfold forced_pitch_post in POST.
destruct POST as (x0 & x1 & x2 & y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & x3 & x4 & x5 & x6 & F' & fc' & m1 & eb' & e32' & pg' & -> & MU1 & WM1 & MI1 & ST1' & FRM1 & XE1 & LE1 & X321 & L321 & XPV1 & XPG1 & LPG1).
assert (OF1 : offsh [(EB + 4 * e0, EB + 4 * e0 + 160); (e32, e32 + 160); (pv, pv + 4); (pg, pg + 12); (usp + -16, usp)])
by (cbn; unfold SH_LO, SH_HI; clear - LS PL PH E0a E0b FQS Q1 Q2 V1 V2 G1 G2 FSZ BL2 LOR; lia).
pose proof (aobj_munch bsegs _ m m1 e32 160 OB32 MU1 (shfree_of_aobj bsegs _ m e32 160 OF1 OB32)) as (_ & _ & AC32).
pose proof (aobj_munch bsegs _ m m1 pv 4 OBPV MU1 (shfree_of_aobj bsegs _ m pv 4 OF1 OBPV)) as (_ & _ & ACPV).
pose proof (aobj_munch bsegs _ m m1 pg 12 OBPG MU1 (shfree_of_aobj bsegs _ m pg 12 OF1 OBPG)) as (_ & _ & ACPG).
pose proof (frame_facts RT AF Σ m fa ka ART0 INA) as (FA0 & _). assert (FSZA : 64 <= fs_size ka) by (unfold fs_size; rewrite Z.shiftl_mul_pow2 by lia; pose proof (Z.pow_pos_nonneg 2 (Z.of_nat ka) ltac:(lia) ltac:(lia)); lia).
assert (OBA0 : aobj bsegs m A BITS_SIZEOF) by (split; [unfold BITS_SIZEOF in *; lia|]; split; [unfold APP_TOP, BITS_SIZEOF in *; pose proof (frame_below_lo RT AF Σ m fa ka lo ART0 INA LOW) as (X & _); lia| exact A3]).
pose proof (aobj_munch bsegs _ m m1 A _ OBA0 MU1 (shfree_of_aobj bsegs _ m A _ OF1 OBA0)) as (_ & _ & ACA).
clear XPG XPV X32 XE.
unfold hidp in *.
apply (rw_cells_transport bsegs [(EB + 4 * e0, EB + 4 * e0 + 160); (e32, e32 + 160); (pv, pv + 4); (pg, pg + 12); (usp + -16, usp)] m m1 _ _) in OBJ; [ | exact MU1 | exact WM1 | cbn [disjoint_from]; simpl_sizes; clear - FLAA HAX HAV HAG A1 A2 PL PH E0a E0b FBA LOR; lia ].
apply (u8arr_transport bsegs [(EB + 4 * e0, EB + 4 * e0 + 160); (e32, e32 + 160); (pv, pv + 4); (pg, pg + 12); (usp + -16, usp)] m m1 _ _) in DAT;
[ | exact MU1 | exact WM1 | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; clear - HDP FLQD DL DH Lbs PL PH E0a E0b Q1 Q2 V1 V2 G1 G2 BD1 LOR; lia ].
cps_hide.
cps_seg_post.
apply Hk. exists Σ. split; [| repeat split; reflexivity].
eapply ASTA_conseq; [eassumption|]. intros ms <-. exists y0, m1, eb', e32', pg'.
split; [rewrite ESP; unfold ret_stL; do 16 eexists; split; [reflexivity| exact FRM1]|].
split. { split; [assumption|]. split; [exact MI1|]. split; [cps_wmono| exact ST1']. }
split; [exact PF|].
split; [exact XE1|]. split; [exact LE1|]. split; [exact X321|]. split; [exact L321|]. split; [exact XPV1|]. split; [exact XPG1|]. split; [exact LPG1|].
split; [split; [exists rj; split; [exact Lrj| exact OBJ]| split; [exists bs; split; [exact DAT| exact Hbs]| exact SIDE]]|].
split; [exact OKB|]. split; [exact ARGS|]. split; [exact AC32|]. split; [exact ACPV|]. split; [exact ACPG| exact ACA].
Qed.
End FpCPS.
End B_TWIN.

Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section FpCPS.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Context {ptr : Type}.

Theorem forced_pitch_ltp : @ltp_unquant_cps RT ptr LtpForcedPitchUnquant.
Proof using AF.
intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
A D b EB e0 e32 pv pg start fin PAR off lo P0 N0 PD ND fq fa kq ka eb e32s pgs opv stk8
FDO MST -> -> -> -> -> -> -> -> -> REP OKB ST1 ST2 FIN OFF _ XE E0a E0b E4 INL PL PH X32 L32 XPV XPG LPG INQ (Q1 & Q2 & Q3 & Q4) (V1 & V2 & V3 & V4) (G1 & G2 & G3 & G4)
HXV HXG HVG INA (A1 & A2 & A3 & A4) IND DL DH HDP HAX HAV HAG ARGS ART0 MI0 FRM0 ST0 LOW LOR SPT SPA.
intros T c Hc Hk.
set (usp := bv_unsigned sp) in *.
assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned).
unfold entry_st in Hc. rewrite ESP in Hc. cbn [ltp_entryA ltp_pitch_span ltp_pitch ltp_bits] in *.
destruct (live_below_lo RT AF Σ m P0 N0 lo ART0 INL LOW) as (BL0 & BL1 & BL2).
destruct (live_facts RT AF Σ m P0 N0 ART0 INL) as (_ & _ & LI & LS).
destruct (frame_below_lo RT AF Σ m fq kq lo ART0 INQ LOW) as (FB1 & _ & _).
pose proof (frame_facts RT AF Σ m fq kq ART0 INQ) as (FQ0 & FQ64 & FQI & _ & FQS & _).
destruct (frame_live_apart RT AF Σ m fq kq P0 N0 ART0 INQ INL) as (FLA & _).
destruct (af_acc_live RT AF Σ m P0 N0 ART0 INL) as (_ & ACL).
pose proof (af_client_consts RT AF Σ m ART0) as CC0.
pose proof (pres_fp_refl (rt_live RT Σ) (rt_frames RT Σ) usp [(EB + 4 * e0, EB + 4 * e0 + 160); (e32, e32 + 160); (pv, pv + 4); (pg, pg + 12); (A, A + BITS_SIZEOF)] m) as PF.
pose proof (fun a => aclient_split RT AF Σ m usp a ART0) as SPL.
pose proof (rw_cells_bound _ _ _ _ XE) as BE. rewrite cells_size_f32 in BE.
cps_norm. unfold LTP_STACK, BITS_SIZEOF in *.
destruct REP as ((rj & Lrj & OBJ) & (bs & DAT & Hbs) & SIDE).
assert (Lbs : Z.of_nat (length bs) = sb_buf_size b) by (pose proof OKB as OK'; unfold bits_ok in OK'; rewrite Hbs, zlength_map_unsigned in OK'; clear - OK'; lia).
unfold bits_cells in OBJ. unfold ltp_args_cells in ARGS.
assert (FSZ : 64 <= fs_size kq) by (unfold fs_size; rewrite Z.shiftl_mul_pow2 by lia; pose proof (Z.pow_pos_nonneg 2 (Z.of_nat kq) ltac:(lia) ltac:(lia)); lia).
assert (T1 : P0 + N0 <= lo) by exact BL1. assert (T2 : lo <= usp) by lia. assert (T3 : usp <= 140737488355328) by lia. assert (T4 : EB + 4 * Z.of_nat (length eb) <= P0 + N0) by exact PH.
assert (OBE : aobj asegs m EB (4 * Z.of_nat (length eb))) by (split; [lia|]; split; [unfold APP_TOP; lia|]; apply (acc_sub asegs m P0 N0 _ _ ACL); lia).
assert (OB32 : aobj asegs m e32 160) by (split; [lia|]; split; [unfold APP_TOP; lia| exact Q3]).
assert (OBPV : aobj asegs m pv 4) by (split; [lia|]; split; [unfold APP_TOP; lia| exact V3]).
assert (OBPG : aobj asegs m pg 12) by (split; [lia|]; split; [unfold APP_TOP; lia| exact G3]).
destruct (frame_live_apart RT AF Σ m fa ka P0 N0 ART0 INA INL) as (FLAA & _).
destruct (frame_live_apart RT AF Σ m fq kq PD ND ART0 INQ IND) as (FLQD & _).
destruct (live_below_lo RT AF Σ m PD ND lo ART0 IND LOW) as (BD0 & BD1 & _).
destruct (frame_below_lo RT AF Σ m fa ka lo ART0 INA LOW) as (FBA & _ & _).
cps_seg (forced_pitch_unquant_walk EB e0 e32 pv pg usp lo start (length eb) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m OBE OB32 OBPV OBPG E4 Q4 V4 G4).
{ unfold hidp, SH_LO, SH_HI. clear - LS PL PH. lia. }
{ unfold hidp, SH_LO, SH_HI. clear - FQS Q1 Q2 FSZ. lia. }
{ unfold hidp, SH_LO, SH_HI. clear - FQS V1 V2 FSZ. lia. }
{ unfold hidp, SH_LO, SH_HI. clear - FQS G1 G2 FSZ. lia. }
{ unfold hidp. clear - FLA PL PH Q1 Q2. lia. }
{ unfold hidp. clear - FLA PL PH V1 V2. lia. }
{ unfold hidp. clear - FLA PL PH G1 G2. lia. }
unfold forced_pitch_post in POST.
destruct POST as (x0 & x1 & x2 & y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & x3 & x4 & x5 & x6 & F' & fc' & m1 & eb' & e32' & pg' & -> & MU1 & WM1 & MI1 & ST1' & FRM1 & XE1 & LE1 & X321 & L321 & XPV1 & XPG1 & LPG1).
assert (OF1 : offsh [(EB + 4 * e0, EB + 4 * e0 + 160); (e32, e32 + 160); (pv, pv + 4); (pg, pg + 12); (usp + -16, usp)])
by (cbn; unfold SH_LO, SH_HI; clear - LS PL PH E0a E0b FQS Q1 Q2 V1 V2 G1 G2 FSZ BL2 LOR; lia).
pose proof (aobj_munch asegs _ m m1 e32 160 OB32 MU1 (shfree_of_aobj asegs _ m e32 160 OF1 OB32)) as (_ & _ & AC32).
pose proof (aobj_munch asegs _ m m1 pv 4 OBPV MU1 (shfree_of_aobj asegs _ m pv 4 OF1 OBPV)) as (_ & _ & ACPV).
pose proof (aobj_munch asegs _ m m1 pg 12 OBPG MU1 (shfree_of_aobj asegs _ m pg 12 OF1 OBPG)) as (_ & _ & ACPG).
pose proof (frame_facts RT AF Σ m fa ka ART0 INA) as (FA0 & _). assert (FSZA : 64 <= fs_size ka) by (unfold fs_size; rewrite Z.shiftl_mul_pow2 by lia; pose proof (Z.pow_pos_nonneg 2 (Z.of_nat ka) ltac:(lia) ltac:(lia)); lia).
assert (OBA0 : aobj asegs m A BITS_SIZEOF) by (split; [unfold BITS_SIZEOF in *; lia|]; split; [unfold APP_TOP, BITS_SIZEOF in *; pose proof (frame_below_lo RT AF Σ m fa ka lo ART0 INA LOW) as (X & _); lia| exact A3]).
pose proof (aobj_munch asegs _ m m1 A _ OBA0 MU1 (shfree_of_aobj asegs _ m A _ OF1 OBA0)) as (_ & _ & ACA).
clear XPG XPV X32 XE.
unfold hidp in *.
apply (rw_cells_transport asegs [(EB + 4 * e0, EB + 4 * e0 + 160); (e32, e32 + 160); (pv, pv + 4); (pg, pg + 12); (usp + -16, usp)] m m1 _ _) in OBJ; [ | exact MU1 | exact WM1 | cbn [disjoint_from]; simpl_sizes; clear - FLAA HAX HAV HAG A1 A2 PL PH E0a E0b FBA LOR; lia ].
apply (u8arr_transport asegs [(EB + 4 * e0, EB + 4 * e0 + 160); (e32, e32 + 160); (pv, pv + 4); (pg, pg + 12); (usp + -16, usp)] m m1 _ _) in DAT;
[ | exact MU1 | exact WM1 | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; clear - HDP FLQD DL DH Lbs PL PH E0a E0b Q1 Q2 V1 V2 G1 G2 BD1 LOR; lia ].
cps_hide.
cps_seg_post.
apply Hk. exists Σ. split; [| repeat split; reflexivity].
eapply ASTA_conseq; [eassumption|]. intros ms <-. exists y0, m1, eb', e32', pg'.
split; [rewrite ESP; unfold ret_stL; do 16 eexists; split; [reflexivity| exact FRM1]|].
split. { split; [assumption|]. split; [exact MI1|]. split; [cps_wmono| exact ST1']. }
split; [exact PF|].
split; [exact XE1|]. split; [exact LE1|]. split; [exact X321|]. split; [exact L321|]. split; [exact XPV1|]. split; [exact XPG1|]. split; [exact LPG1|].
split; [split; [exists rj; split; [exact Lrj| exact OBJ]| split; [exists bs; split; [exact DAT| exact Hbs]| exact SIDE]]|].
split; [exact OKB|]. split; [exact ARGS|]. split; [exact AC32|]. split; [exact ACPV|]. split; [exact ACPG| exact ACA].
Qed.
End FpCPS.
