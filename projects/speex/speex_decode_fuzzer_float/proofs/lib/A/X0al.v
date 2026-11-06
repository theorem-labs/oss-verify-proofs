(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS Require Import X0mx X0k2.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1da X1dg X1df X1ck.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1nt X1rh X1re.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1cg.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0bp X0j9 X0ec X001 X00b X04b X07z X05o X05p X05s X05l X09e X082 X08y
X0am X0an.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X12c X14x X0r0 X0ra X0v9 X0yr X0wl X0yt X0zq X117 X118.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14x OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0r0 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ra OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0v9 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0yr OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0wl OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0yt OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0zq OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X117 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X118.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section P3CPS.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis MEMS : memset_icontract RT e_asan_memset.
Context {ptr : Type}.

Theorem pitch3_ltp : forall p, ltp_params_ok p -> @ltp_unquant_cps RT ptr (LtpPitchUnquant3tap p).
Proof using AF MEMS.
intros p (PB & GB & GS).
intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
A D b EB e0 e32 pv pg start fin PAR off lo P0 N0 PD ND fq fa kq ka eb e32s pgs opv stk8
FDO MST -> -> -> -> -> -> -> -> -> REP OKB ST1 ST2 FIN OFF (XPAR & PAR8 & PARLO & PARI & PARL) XE E0a E0b E4 INL PL PH X32 L32 XPV XPG LPG INQ (Q1 & Q2 & Q3 & Q4) (V1 & V2 & V3 & V4) (G1 & G2 & G3 & G4)
HXV HXG HVG INA (A1 & A2 & A3 & A4) IND DL DH HDP HAX HAV HAG ARGS ART0 MI0 FRM0 ST0 LOW LOR SPT SPA.
intros T c Hc Hk.
set (usp := bv_unsigned sp) in *.
assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned).
unfold entry_st in Hc. rewrite ESP in Hc. cbn [ltp_entryA ltp_pitch_span ltp_pitch ltp_bits] in *.
set (gbits := ltp_gain_bits p) in *. set (pbits := ltp_pitch_bits p) in *. set (G := gain_cdbk_addrA (ltp_gain_cdbk p)) in *.
destruct (live_below_lo RT AF Σ m P0 N0 lo ART0 INL LOW) as (BL0 & BL1 & BL2).
destruct (live_facts RT AF Σ m P0 N0 ART0 INL) as (LP0 & _ & LI & LS).
destruct (frame_below_lo RT AF Σ m fq kq lo ART0 INQ LOW) as (FB1 & _ & _).
pose proof (frame_facts RT AF Σ m fq kq ART0 INQ) as (FQ0 & FQ64 & FQI & _ & FQS & _).
destruct (frame_live_apart RT AF Σ m fq kq P0 N0 ART0 INQ INL) as (FLA & _).
destruct (af_acc_live RT AF Σ m P0 N0 ART0 INL) as (_ & ACL).
destruct (af_acc_live RT AF Σ m PD ND ART0 IND) as (_ & ACD).
pose proof (af_client_consts RT AF Σ m ART0) as CC0.
pose proof (pres_fp_refl (rt_live RT Σ) (rt_frames RT Σ) usp [(EB + 4 * e0, EB + 4 * e0 + 160); (e32, e32 + 160); (pv, pv + 4); (pg, pg + 12); (A, A + BITS_SIZEOF)] m) as PF.
pose proof (fun a => aclient_split RT AF Σ m usp a ART0) as SPL.
pose proof (rw_cells_bound _ _ _ _ XE) as BE. rewrite cells_size_f32 in BE.
destruct (frame_live_apart RT AF Σ m fa ka P0 N0 ART0 INA INL) as (FLAA & _).
destruct (frame_live_apart RT AF Σ m fq kq PD ND ART0 INQ IND) as (FLQD & _).
destruct (frame_live_apart RT AF Σ m fa ka PD ND ART0 INA IND) as (FLAD & _).
destruct (live_below_lo RT AF Σ m PD ND lo ART0 IND LOW) as (BD0 & BD1 & _).
destruct (live_facts RT AF Σ m PD ND ART0 IND) as (_ & _ & LID & LSD).
destruct (frame_below_lo RT AF Σ m fa ka lo ART0 INA LOW) as (FBA & _ & _).
pose proof (frame_facts RT AF Σ m fa ka ART0 INA) as (FA0 & FA64 & FAI & _ & FAS & _).
assert (P2 : 1 <= 2 ^ pbits) by (apply (Z.pow_le_mono_r 2 0 pbits); lia).
assert (G2a : 1 <= 2 ^ gbits <= 128) by (split; [apply (Z.pow_le_mono_r 2 0 gbits); lia | change 128 with (2^7); apply Z.pow_le_mono_r; lia]).
pose proof (gain_tab_lit (ltp_gain_cdbk p)) as GLIT. rewrite GS in GLIT. fold G in GLIT.
pose proof (gain_tab_len (ltp_gain_cdbk p)) as GLEN. rewrite GS in GLEN.
pose proof (gain_tab_ro (ltp_gain_cdbk p) m MI0) as GRO. fold G in GRO.
assert (GRNG : 0x10000 <= G /\ G + 4 * 2 ^ gbits <= IMG_TOP_B) by (rewrite <- GS; unfold G, IMG_TOP_B; destruct (ltp_gain_cdbk p); cbn; lia).
pose proof GRNG as GRNG'. unfold IMG_TOP_B in GRNG'.
cps_norm. unfold LTP_STACK, BITS_SIZEOF in *.
assert (FSZ : 64 <= fs_size kq) by (unfold fs_size; rewrite Z.shiftl_mul_pow2 by lia; pose proof (Z.pow_pos_nonneg 2 (Z.of_nat kq) ltac:(lia) ltac:(lia)); lia).
assert (FSZA : 64 <= fs_size ka) by (unfold fs_size; rewrite Z.shiftl_mul_pow2 by lia; pose proof (Z.pow_pos_nonneg 2 (Z.of_nat ka) ltac:(lia) ltac:(lia)); lia).
assert (OBE : aobj bsegs m EB (4 * Z.of_nat (length eb))) by (split; [lia|]; split; [unfold APP_TOP; lia|]; apply (acc_sub bsegs m P0 N0 _ _ ACL); lia).
assert (OB32 : aobj bsegs m e32 160) by (split; [lia|]; split; [unfold APP_TOP; lia| exact Q3]).
pose proof OB32 as (O320 & O321 & _). unfold APP_TOP in O321.
assert (OBPV : aobj bsegs m pv 4) by (split; [lia|]; split; [unfold APP_TOP; lia| exact V3]).
assert (OBPG : aobj bsegs m pg 12) by (split; [lia|]; split; [unfold APP_TOP; lia| exact G3]).
assert (OBA0 : aobj bsegs m A 48) by (split; [lia|]; split; [unfold APP_TOP; lia| exact A3]).
assert (SZ0 : 0 <= sb_buf_size b).
{ destruct REP as (_ & (bs & _ & Hbs) & _). pose proof OKB as OK'. unfold bits_ok in OK'. rewrite Hbs, zlength_map_unsigned in OK'. clear - OK'. lia. }
assert (OBD0 : aobj bsegs m D (sb_buf_size b)) by (split; [lia|]; split; [unfold APP_TOP; lia|]; apply (acc_sub bsegs m PD ND _ _ ACD); lia).
assert (OBPAR : aobj bsegs m PAR 16) by (apply (aobj_lit RT AF Σ m PAR 16 ART0 PARL); unfold APP_TOP; lia).
assert (OBG : aobj bsegs m G (4 * 2 ^ gbits)) by (apply (aobj_lit RT AF Σ m G _ ART0 GLIT); unfold APP_TOP; lia).
unfold ltp_par_cellsA in XPAR. unfold ltp_args_cells in ARGS.
assert (ASH : hidp (A + 48 <= SH_LO \/ SH_HI <= A)) by (unfold hidp, SH_LO, SH_HI; clear - FAS A1 A2 FSZA; lia).
assert (ALO : A + 48 <= lo) by (clear - FBA A2; lia).
assert (DLO : D + sb_buf_size b <= lo) by (clear - BD1 DH; lia).
assert (ST17 : 17 <= start <= 144) by (clear - ST1 ST2 P2; lia).
assert (ATOP : IMG_TOP_B <= A) by (unfold IMG_TOP_B, SEGTOP_A in *; clear - FAI A1; lia).
assert (PARIB : PAR + 16 <= IMG_TOP_B) by (unfold IMG_TOP_B; clear - PARI; lia).
assert (EPOS : 0 < EB) by (clear - LP0 PL; lia). assert (XPOS : 0 < e32) by (clear - FQ0 Q1; lia).
assert (VPOS : 0 < pv) by (clear - FQ0 V1; lia). assert (GPOS : 0 < pg) by (clear - FQ0 G1; lia).
assert (VSH : hidp (pv + 4 <= SH_LO \/ SH_HI <= pv)) by (unfold hidp, SH_LO, SH_HI; clear - FQS V1 V2 FSZ; lia).
assert (GSH : hidp (pg + 12 <= SH_LO \/ SH_HI <= pg)) by (unfold hidp, SH_LO, SH_HI; clear - FQS G1 G2 FSZ; lia).
assert (XSH : hidp (e32 + 160 <= SH_LO \/ SH_HI <= e32)) by (unfold hidp, SH_LO, SH_HI; clear - FQS Q1 Q2 FSZ; lia).
assert (EXH : hidp (EB + 4 * Z.of_nat (length eb) <= e32 \/ e32 + 160 <= EB)) by (unfold hidp; clear - FLA PL PH Q1 Q2; lia).
assert (VAP : pv + 4 <= lo) by (clear - FB1 V2; lia). assert (GAP : pg + 12 <= lo) by (clear - FB1 G2; lia). assert (XAP : e32 + 160 <= lo) by (clear - FB1 Q2; lia).
assert (OF1 : offsh [(A, A + 48); (usp + -192, usp)]) by (cbn; unfold SH_LO, SH_HI; clear - FAS A1 A2 FSZA BL2 LOR; lia).
pose proof (HAX : _ \/ _) as HAX'. pose proof (HAV : _ \/ _) as HAV'. pose proof (HAG : _ \/ _) as HAG'.
pose proof (HXV : _ \/ _) as HXV'. pose proof (HXG : _ \/ _) as HXG'. pose proof (HVG : _ \/ _) as HVG'. pose proof (EXH : _ \/ _) as EXH'.
assert (LO160 : lo <= usp - 144 - 48) by (clear - LOR; lia). assert (LO128 : lo <= usp - 144) by (clear - LOR; lia). assert (SPH : usp + 40 < 2^63) by (clear - SPT; lia).
assert (SPH63 : usp < 2^63) by (clear - SPT; lia). assert (SPH62 : usp < 2^62) by (clear - SPT; lia).
cps_hide.
cps_seg (p3_w1a A D EB e0 e32 pv pg usp lo start fin PAR G (4 * 2 ^ gbits) gbits pbits off b _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m REP OKB OBA0 OBD0 OBPAR PAR8 PARIB PARLO OBG eq_refl (proj2 GRNG) (proj1 GRNG) ST17 LO160 BL2 SPH ASH ATOP ALO DLO).
destruct POST as (ra1 & x0 & x1 & x2 & y0 & y1 & y2 & y3 & y4 & y5 & y7 & r3 & r4 & r5 & r7 & r10 & r11 & x3 & x4 & x5 & x6 & g0 & g1 & g2 & j0 & j16 & F1 & fc1 & m1 & POST).
cbv zeta in POST. fold (uv b pbits) (ub b pbits) in POST. fold (ub (ub b pbits) gbits) in POST.
destruct POST as (-> & MU1 & WM1 & MI1 & ST1' & FRM1 & FR1 & REP1 & OKB1 & SZ1 & V1R).
destruct REP1 as ((rj & Lrj & OBJ) & (bs & DAT & Hbs) & SIDE). unfold bits_cells in OBJ. apply (proj1 (u8arr_rw_CB m1 D bs)) in DAT.
assert (Lbs : Z.of_nat (length bs) = sb_buf_size b) by (pose proof OKB1 as OK'; unfold bits_ok in OK'; rewrite Hbs, zlength_map_unsigned in OK'; clear - OK' SZ1; lia).
clear ST0 REP. cps_seg_post.

pose proof (aobj_munch bsegs _ m m1 pv 4 OBPV MU1 (shfree_of_aobj bsegs _ m pv 4 OF1 OBPV)) as OBPV1.
pose proof (aobj_munch bsegs _ m m1 pg 12 OBPG MU1 (shfree_of_aobj bsegs _ m pg 12 OF1 OBPG)) as OBPG1.
pose proof (aobj_munch bsegs _ m m1 e32 160 OB32 MU1 (shfree_of_aobj bsegs _ m e32 160 OF1 OB32)) as OB321.
pose proof (aobj_munch bsegs _ m m1 EB _ OBE MU1 (shfree_of_aobj bsegs _ m EB _ OF1 OBE)) as OBE1.
pose proof (aobj_munch bsegs _ m m1 A 48 OBA0 MU1 (shfree_of_aobj bsegs _ m A 48 OF1 OBA0)) as OBA1.
destruct pgs as [|q0 [|q1 [|q2 [|? ?]]]]; try (cbn [length] in LPG; lia).
assert (V1R128 : 0 <= uv b pbits < 128) by (clear - V1R PB; assert (2 ^ pbits <= 2^7) by (apply Z.pow_le_mono_r; lia); lia).
assert (PIT : 0 <= uv b pbits + start < 2^31) by (clear - V1R ST17 PB; assert (2 ^ pbits <= 2^7) by (apply Z.pow_le_mono_r; lia); lia).
cps_seg (p3_w1b pv pg usp lo e32 (uv b pbits + start) _ _ _ _ _ _ _ _ _ m1 OBPV1 OBPG1 V4 G4 LO128 BL2 SPH63 VSH GSH VAP GAP HVG PIT VPOS GPOS).
destruct POST as (x0' & x1' & x2' & y3' & y4' & y5' & y6' & y7' & x3' & x4' & x5' & x6' & F2 & fc2 & m2 & pg' & -> & MU2 & WM2 & MI2 & ST2' & FRM2 & FR2 & XPV2 & XPG2 & LPG2).
clear XPV XPG FR1. cps_seg_post.

assert (OF2 : offsh [(pv, pv + 4); (pg, pg + 12)]) by (cbn; pose proof (VSH : _ \/ _) as Y1; pose proof (GSH : _ \/ _) as Y2; clear - Y1 Y2; unfold SH_LO, SH_HI in *; lia).
pose proof (aobj_munch bsegs _ m1 m2 e32 160 OB321 MU2 (shfree_of_aobj bsegs _ m1 e32 160 OF2 OB321)) as (_ & _ & AC322).
pose proof (aobj_munch bsegs _ m1 m2 pv 4 OBPV1 MU2 (shfree_of_aobj bsegs _ m1 pv 4 OF2 OBPV1)) as (_ & _ & ACPV2).
pose proof (aobj_munch bsegs _ m1 m2 pg 12 OBPG1 MU2 (shfree_of_aobj bsegs _ m1 pg 12 OF2 OBPG1)) as (_ & _ & ACPG2).
pose proof (aobj_munch bsegs _ m1 m2 A 48 OBA1 MU2 (shfree_of_aobj bsegs _ m1 A 48 OF2 OBA1)) as (_ & _ & ACA2).
pose proof X32 as [_ WRW]. rewrite cells_size_f32, L32 in WRW. change (Z.of_nat (4 * 40)) with 160 in WRW.
cps_rt (MEMS Σ PMc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m2 e32 160 z8 lo).
{ unfold checked_dst. rewrite unsigned_lit by ulc. split; [intros _; split|split].
- exact AC322.
- right; left. exists fq, kq. split; [exact INQ|]. split; [exact Q1| exact Q2].
- intros i Hi. right; right; right; left. exists fq, kq. split; [exact INQ|]. clear - Q1 Q2 Hi. lia.
- exact WRW. }
{ cps_callok. }
intros c4 Hc4.
cps_unpack Hc4 as (m4 & RS4 & (ART4 & MI4 & WM4 & ST4) & PRES4 & BYW).
assert (X32z : exists e32z, length e32z = 40%nat /\ rw_cells bsegs m4 e32 (f32 e32z)).
{ apply (rw_cells_CB_f32 bsegs m4 e32 40 (repeat z8 160)).
split; [split; [split; [reflexivity| exact I]| cbn [cells_bytes cbytes app]; rewrite app_nil_r; exact BYW]|].
cbn [cells_size csize Nat.add]. exact (wr_at_transport bsegs m2 m4 _ _ WRW WM4). }
destruct X32z as (e32z & L32z & X32z). clear WRW BYW.

destruct (af_acc_live RT AF Σ m4 P0 N0 ART4 INL) as (_ & ACL4).
assert (OBE4 : aobj bsegs m4 EB (4 * Z.of_nat (length eb))) by (split; [exact (proj1 OBE)|]; split; [exact (proj1 (proj2 OBE))|]; apply (acc_sub bsegs m4 P0 N0 _ _ ACL4); clear - PL PH; lia).
assert (AC324 : acc bsegs m4 e32 160).
{ apply (acc_pres_ex_frame _ _ _ _ _ m2 m4 fq kq e32 160 PRES4 INQ (mod64_mod8 _ FQ64) (fs_size_mod8 kq)); [clear - FQ0; lia | exact Q1 | clear - Q2; lia | exact (proj1 (proj2 OB32)) | exact XSH | exact AC322]. }
assert (OB324 : aobj bsegs m4 e32 160) by (split; [exact (proj1 OB32)|]; split; [exact (proj1 (proj2 OB32))| exact AC324]).
assert (PITR : 17 <= uv b pbits + start <= 271) by (clear - V1R128 ST17; lia).
unfold p3_frameB in FR2.
cps_seg (p3B_w2 EB e0 e32 usp lo (uv b pbits + start) (length eb) _ _ m4 OBE4 OB324 E4 Q4 EXH XSH XAP LO128 BL2 SPH62 E0a E0b PITR EPOS XPOS).
destruct POST as (z0 & z1 & z2 & w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & z3 & z4 & z5 & z6 & F5 & fc5 & m5 & e32' & -> & MU5 & WM5 & MI5 & ST5 & FRM5 & X325 & L325).
clear X32z FR2 ST4. cps_seg_post.

assert (OF5 : offsh [(e32, e32 + 160)]) by (cbn; pose proof (XSH : _ \/ _) as Y1; clear - Y1; unfold SH_LO, SH_HI in *; lia).
assert (ACX : forall f k o n, In (f, k) (rt_frames RT Σ) -> f mod 64 = 0 -> 0 < f -> f <= o -> o + n <= f + fs_size k -> 0 <= o -> o + n <= APP_TOP ->
acc bsegs m2 o n -> acc bsegs m5 o n).
{ intros f k o n Hin F64 F0 Ho Hn O0 OT AC2.
assert (AC4 : acc bsegs m4 o n) by (apply (acc_pres_ex_frame _ _ _ _ _ m2 m4 f k o n PRES4 Hin (mod64_mod8 _ F64) (fs_size_mod8 k)); [lia | exact Ho | exact Hn | exact OT | exact XSH | exact AC2]).
assert (OB4 : aobj bsegs m4 o n) by (split; [exact O0|]; split; [exact OT| exact AC4]).
exact (proj2 (proj2 (aobj_munch bsegs _ m4 m5 o n OB4 MU5 (shfree_of_aobj bsegs _ m4 o n OF5 OB4)))). }
apply Hk. exists Σ. split; [| repeat split; reflexivity].
eapply ASTA_conseq; [eassumption|]. intros ms <-. exists w0, m5, eb, e32', pg'.
split; [rewrite ESP; unfold ret_stL; do 16 eexists; split; [reflexivity| exact FRM5]|].
split. { split; [assumption|]. split; [exact MI5|]. split; [cps_wmono| exact ST5]. }
split; [exact PF|].
split; [exact XE|]. split; [reflexivity|]. split; [exact X325|]. split; [exact L325|]. split; [exact XPV2|]. split; [exact XPG2|]. split; [exact LPG2|].
split; [split; [exists rj; split; [exact Lrj| exact OBJ]| split; [exists bs; split; [exact (proj2 (u8arr_rw_CB m5 D bs) DAT)| exact Hbs]| exact SIDE]]|].
split; [exact OKB1|]. split; [exact ARGS|].
split; [apply (ACX fq kq e32 160 INQ FQ64 FQ0 Q1); [clear - Q2; lia | exact (proj1 OB32) | exact (proj1 (proj2 OB32)) | exact AC322]|].
split; [apply (ACX fq kq pv 4 INQ FQ64 FQ0 V1); [clear - V2; lia | exact (proj1 OBPV) | exact (proj1 (proj2 OBPV)) | exact ACPV2]|].
split; [apply (ACX fq kq pg 12 INQ FQ64 FQ0 G1); [clear - G2; lia | exact (proj1 OBPG) | exact (proj1 (proj2 OBPG)) | exact ACPG2]|].
apply (ACX fa ka A 48 INA FA64 FA0 A1); [clear - A2; lia | exact (proj1 OBA0) | exact (proj1 (proj2 OBA0)) | exact ACA2].
Qed.
End P3CPS.
End B_TWIN.

Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section P3CPS.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis MEMS : memset_icontract RT e_asan_memset.
Context {ptr : Type}.

Theorem pitch3_ltp : forall p, ltp_params_ok p -> @ltp_unquant_cps RT ptr (LtpPitchUnquant3tap p).
Proof using AF MEMS.
intros p (PB & GB & GS).
intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
A D b EB e0 e32 pv pg start fin PAR off lo P0 N0 PD ND fq fa kq ka eb e32s pgs opv stk8
FDO MST -> -> -> -> -> -> -> -> -> REP OKB ST1 ST2 FIN OFF (XPAR & PAR8 & PARLO & PARI & PARL) XE E0a E0b E4 INL PL PH X32 L32 XPV XPG LPG INQ (Q1 & Q2 & Q3 & Q4) (V1 & V2 & V3 & V4) (G1 & G2 & G3 & G4)
HXV HXG HVG INA (A1 & A2 & A3 & A4) IND DL DH HDP HAX HAV HAG ARGS ART0 MI0 FRM0 ST0 LOW LOR SPT SPA.
intros T c Hc Hk.
set (usp := bv_unsigned sp) in *.
assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned).
unfold entry_st in Hc. rewrite ESP in Hc. cbn [ltp_entryA ltp_pitch_span ltp_pitch ltp_bits] in *.
set (gbits := ltp_gain_bits p) in *. set (pbits := ltp_pitch_bits p) in *. set (G := gain_cdbk_addrA (ltp_gain_cdbk p)) in *.
destruct (live_below_lo RT AF Σ m P0 N0 lo ART0 INL LOW) as (BL0 & BL1 & BL2).
destruct (live_facts RT AF Σ m P0 N0 ART0 INL) as (_ & _ & LI & LS).
destruct (frame_below_lo RT AF Σ m fq kq lo ART0 INQ LOW) as (FB1 & _ & _).
pose proof (frame_facts RT AF Σ m fq kq ART0 INQ) as (FQ0 & FQ64 & FQI & _ & FQS & _).
destruct (frame_live_apart RT AF Σ m fq kq P0 N0 ART0 INQ INL) as (FLA & _).
destruct (af_acc_live RT AF Σ m P0 N0 ART0 INL) as (_ & ACL).
destruct (af_acc_live RT AF Σ m PD ND ART0 IND) as (_ & ACD).
pose proof (af_client_consts RT AF Σ m ART0) as CC0.
pose proof (pres_fp_refl (rt_live RT Σ) (rt_frames RT Σ) usp [(EB + 4 * e0, EB + 4 * e0 + 160); (e32, e32 + 160); (pv, pv + 4); (pg, pg + 12); (A, A + BITS_SIZEOF)] m) as PF.
pose proof (fun a => aclient_split RT AF Σ m usp a ART0) as SPL.
pose proof (rw_cells_bound _ _ _ _ XE) as BE. rewrite cells_size_f32 in BE.
destruct (frame_live_apart RT AF Σ m fa ka P0 N0 ART0 INA INL) as (FLAA & _).
destruct (frame_live_apart RT AF Σ m fq kq PD ND ART0 INQ IND) as (FLQD & _).
destruct (frame_live_apart RT AF Σ m fa ka PD ND ART0 INA IND) as (FLAD & _).
destruct (live_below_lo RT AF Σ m PD ND lo ART0 IND LOW) as (BD0 & BD1 & _).
destruct (live_facts RT AF Σ m PD ND ART0 IND) as (_ & _ & LID & LSD).
destruct (frame_below_lo RT AF Σ m fa ka lo ART0 INA LOW) as (FBA & _ & _).
pose proof (frame_facts RT AF Σ m fa ka ART0 INA) as (FA0 & FA64 & FAI & _ & FAS & _).
assert (P2 : 1 <= 2 ^ pbits) by (apply (Z.pow_le_mono_r 2 0 pbits); lia).
assert (G2a : 1 <= 2 ^ gbits <= 128) by (split; [apply (Z.pow_le_mono_r 2 0 gbits); lia | change 128 with (2^7); apply Z.pow_le_mono_r; lia]).
pose proof (gain_tab_lit (ltp_gain_cdbk p)) as GLIT. rewrite GS in GLIT. fold G in GLIT.
pose proof (gain_tab_len (ltp_gain_cdbk p)) as GLEN. rewrite GS in GLEN.
pose proof (gain_tab_ro (ltp_gain_cdbk p) m MI0) as GRO. fold G in GRO.
assert (GRNG : 0x10000 <= G /\ G + 4 * 2 ^ gbits <= IMG_TOP) by (rewrite <- GS; unfold G, IMG_TOP; destruct (ltp_gain_cdbk p); cbn; lia).
cps_norm. unfold LTP_STACK, BITS_SIZEOF in *.
assert (FSZ : 64 <= fs_size kq) by (unfold fs_size; rewrite Z.shiftl_mul_pow2 by lia; pose proof (Z.pow_pos_nonneg 2 (Z.of_nat kq) ltac:(lia) ltac:(lia)); lia).
assert (FSZA : 64 <= fs_size ka) by (unfold fs_size; rewrite Z.shiftl_mul_pow2 by lia; pose proof (Z.pow_pos_nonneg 2 (Z.of_nat ka) ltac:(lia) ltac:(lia)); lia).
assert (OBE : aobj asegs m EB (4 * Z.of_nat (length eb))) by (split; [lia|]; split; [unfold APP_TOP; lia|]; apply (acc_sub asegs m P0 N0 _ _ ACL); lia).
assert (OB32 : aobj asegs m e32 160) by (split; [lia|]; split; [unfold APP_TOP; lia| exact Q3]).
pose proof OB32 as (O320 & O321 & _). unfold APP_TOP in O321.
assert (OBPV : aobj asegs m pv 4) by (split; [lia|]; split; [unfold APP_TOP; lia| exact V3]).
assert (OBPG : aobj asegs m pg 12) by (split; [lia|]; split; [unfold APP_TOP; lia| exact G3]).
assert (OBA0 : aobj asegs m A 48) by (split; [lia|]; split; [unfold APP_TOP; lia| exact A3]).
assert (SZ0 : 0 <= sb_buf_size b).
{ destruct REP as (_ & (bs & _ & Hbs) & _). pose proof OKB as OK'. unfold bits_ok in OK'. rewrite Hbs, zlength_map_unsigned in OK'. clear - OK'. lia. }
assert (OBD0 : aobj asegs m D (sb_buf_size b)) by (split; [lia|]; split; [unfold APP_TOP; lia|]; apply (acc_sub asegs m PD ND _ _ ACD); lia).
assert (OBPAR : aobj asegs m PAR 16) by (apply (aobj_lit RT AF Σ m PAR 16 ART0 PARL); unfold APP_TOP; lia).
assert (OBG : aobj asegs m G (4 * 2 ^ gbits)) by (apply (aobj_lit RT AF Σ m G _ ART0 GLIT); unfold APP_TOP; lia).
unfold ltp_par_cellsA in XPAR. unfold ltp_args_cells in ARGS.
assert (ASH : hidp (A + 48 <= SH_LO \/ SH_HI <= A)) by (unfold hidp, SH_LO, SH_HI; clear - FAS A1 A2 FSZA; lia).
assert (ALO : A + 48 <= lo) by (clear - FBA A2; lia).
assert (DLO : D + sb_buf_size b <= lo) by (clear - BD1 DH; lia).
assert (ST17 : 17 <= start <= 144) by (clear - ST1 ST2 P2; lia).
assert (ATOP : IMG_TOP <= A) by (unfold IMG_TOP; clear - FAI A1; lia).
assert (VSH : hidp (pv + 4 <= SH_LO \/ SH_HI <= pv)) by (unfold hidp, SH_LO, SH_HI; clear - FQS V1 V2 FSZ; lia).
assert (GSH : hidp (pg + 12 <= SH_LO \/ SH_HI <= pg)) by (unfold hidp, SH_LO, SH_HI; clear - FQS G1 G2 FSZ; lia).
assert (XSH : hidp (e32 + 160 <= SH_LO \/ SH_HI <= e32)) by (unfold hidp, SH_LO, SH_HI; clear - FQS Q1 Q2 FSZ; lia).
assert (EXH : hidp (EB + 4 * Z.of_nat (length eb) <= e32 \/ e32 + 160 <= EB)) by (unfold hidp; clear - FLA PL PH Q1 Q2; lia).
assert (VAP : pv + 4 <= lo) by (clear - FB1 V2; lia). assert (GAP : pg + 12 <= lo) by (clear - FB1 G2; lia). assert (XAP : e32 + 160 <= lo) by (clear - FB1 Q2; lia).
assert (OF1 : offsh [(A, A + 48); (usp + -160, usp)]) by (cbn; unfold SH_LO, SH_HI; clear - FAS A1 A2 FSZA BL2 LOR; lia).
pose proof (HAX : _ \/ _) as HAX'. pose proof (HAV : _ \/ _) as HAV'. pose proof (HAG : _ \/ _) as HAG'.
pose proof (HXV : _ \/ _) as HXV'. pose proof (HXG : _ \/ _) as HXG'. pose proof (HVG : _ \/ _) as HVG'. pose proof (EXH : _ \/ _) as EXH'.
assert (LO160 : lo <= usp - 128 - 32) by (clear - LOR; lia). assert (LO128 : lo <= usp - 128) by (clear - LOR; lia). assert (SPH : usp + 40 < 2^63) by (clear - SPT; lia).
cps_hide.
cps_seg (p3_w1a A D EB e0 e32 pv pg usp lo start fin PAR G (4 * 2 ^ gbits) gbits pbits off b _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m REP OKB OBA0 OBD0 OBPAR PAR8 PARI OBG eq_refl (proj2 GRNG) ST17 LO160 BL2 SPH ASH ATOP ALO DLO).
destruct POST as (ra1 & x0 & x1 & x2 & y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & x3 & x4 & x5 & x6 & g0 & g1 & g2 & j0 & F1 & fc1 & m1 & POST).
cbv zeta in POST. fold (uv b pbits) (ub b pbits) in POST. fold (ub (ub b pbits) gbits) in POST.
destruct POST as (-> & MU1 & WM1 & MI1 & ST1' & FRM1 & FR1 & REP1 & OKB1 & SZ1 & V1R).
destruct REP1 as ((rj & Lrj & OBJ) & (bs & DAT & Hbs) & SIDE). unfold bits_cells in OBJ. apply (proj1 (u8arr_rw_CB m1 D bs)) in DAT.
assert (Lbs : Z.of_nat (length bs) = sb_buf_size b) by (pose proof OKB1 as OK'; unfold bits_ok in OK'; rewrite Hbs, zlength_map_unsigned in OK'; clear - OK' SZ1; lia).
clear ST0 REP. cps_seg_post.

pose proof (aobj_munch asegs _ m m1 pv 4 OBPV MU1 (shfree_of_aobj asegs _ m pv 4 OF1 OBPV)) as OBPV1.
pose proof (aobj_munch asegs _ m m1 pg 12 OBPG MU1 (shfree_of_aobj asegs _ m pg 12 OF1 OBPG)) as OBPG1.
pose proof (aobj_munch asegs _ m m1 e32 160 OB32 MU1 (shfree_of_aobj asegs _ m e32 160 OF1 OB32)) as OB321.
pose proof (aobj_munch asegs _ m m1 EB _ OBE MU1 (shfree_of_aobj asegs _ m EB _ OF1 OBE)) as OBE1.
pose proof (aobj_munch asegs _ m m1 A 48 OBA0 MU1 (shfree_of_aobj asegs _ m A 48 OF1 OBA0)) as OBA1.
destruct pgs as [|q0 [|q1 [|q2 [|? ?]]]]; try (cbn [length] in LPG; lia).
assert (V1R128 : 0 <= uv b pbits < 128) by (clear - V1R PB; assert (2 ^ pbits <= 2^7) by (apply Z.pow_le_mono_r; lia); lia).
assert (PIT : 0 <= uv b pbits + start < 2^31) by (clear - V1R ST17 PB; assert (2 ^ pbits <= 2^7) by (apply Z.pow_le_mono_r; lia); lia).
cps_seg (p3_w1b pv pg usp lo e32 (uv b pbits + start) _ _ _ _ _ _ _ _ _ m1 OBPV1 OBPG1 V4 G4 LO128 BL2 VSH GSH VAP GAP HVG PIT).
destruct POST as (x0' & x1' & x2' & y3' & y4' & y5' & y6' & y7' & x3' & x4' & x5' & x6' & F2 & fc2 & m2 & pg' & -> & MU2 & WM2 & MI2 & ST2' & FRM2 & FR2 & XPV2 & XPG2 & LPG2).
clear XPV XPG FR1. cps_seg_post.

assert (OF2 : offsh [(pv, pv + 4); (pg, pg + 12)]) by (cbn; pose proof (VSH : _ \/ _) as Y1; pose proof (GSH : _ \/ _) as Y2; clear - Y1 Y2; unfold SH_LO, SH_HI in *; lia).
pose proof (aobj_munch asegs _ m1 m2 e32 160 OB321 MU2 (shfree_of_aobj asegs _ m1 e32 160 OF2 OB321)) as (_ & _ & AC322).
pose proof (aobj_munch asegs _ m1 m2 pv 4 OBPV1 MU2 (shfree_of_aobj asegs _ m1 pv 4 OF2 OBPV1)) as (_ & _ & ACPV2).
pose proof (aobj_munch asegs _ m1 m2 pg 12 OBPG1 MU2 (shfree_of_aobj asegs _ m1 pg 12 OF2 OBPG1)) as (_ & _ & ACPG2).
pose proof (aobj_munch asegs _ m1 m2 A 48 OBA1 MU2 (shfree_of_aobj asegs _ m1 A 48 OF2 OBA1)) as (_ & _ & ACA2).
pose proof X32 as [_ WRW]. rewrite cells_size_f32, L32 in WRW. change (Z.of_nat (4 * 40)) with 160 in WRW.
cps_rt (MEMS Σ PMc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m2 e32 160 z8 lo).
{ unfold checked_dst. rewrite unsigned_lit by ulc. split; [intros _; split|split].
- exact AC322.
- right; left. exists fq, kq. split; [exact INQ|]. split; [exact Q1| exact Q2].
- intros i Hi. right; right; right; left. exists fq, kq. split; [exact INQ|]. clear - Q1 Q2 Hi. lia.
- exact WRW. }
{ cps_callok. }
intros c4 Hc4.
cps_unpack Hc4 as (m4 & RS4 & (ART4 & MI4 & WM4 & ST4) & PRES4 & BYW).
assert (X32z : exists e32z, length e32z = 40%nat /\ rw_cells asegs m4 e32 (f32 e32z)).
{ apply (rw_cells_CB_f32 asegs m4 e32 40 (repeat z8 160)).
split; [split; [split; [reflexivity| exact I]| cbn [cells_bytes cbytes app]; rewrite app_nil_r; exact BYW]|].
cbn [cells_size csize Nat.add]. exact (wr_at_transport asegs m2 m4 _ _ WRW WM4). }
destruct X32z as (e32z & L32z & X32z). clear WRW BYW.

destruct (af_acc_live RT AF Σ m4 P0 N0 ART4 INL) as (_ & ACL4).
assert (OBE4 : aobj asegs m4 EB (4 * Z.of_nat (length eb))) by (split; [exact (proj1 OBE)|]; split; [exact (proj1 (proj2 OBE))|]; apply (acc_sub asegs m4 P0 N0 _ _ ACL4); clear - PL PH; lia).
assert (AC324 : acc asegs m4 e32 160).
{ apply (acc_pres_ex_frame _ _ _ _ _ m2 m4 fq kq e32 160 PRES4 INQ (mod64_mod8 _ FQ64) (fs_size_mod8 kq)); [clear - FQ0; lia | exact Q1 | clear - Q2; lia | exact (proj1 (proj2 OB32)) | exact XSH | exact AC322]. }
assert (OB324 : aobj asegs m4 e32 160) by (split; [exact (proj1 OB32)|]; split; [exact (proj1 (proj2 OB32))| exact AC324]).
cps_seg (p3_w2 EB e0 e32 usp lo start (uv b pbits) (length eb) _ _ m4 OBE4 OB324 E4 Q4 EXH XSH XAP LO128 BL2 E0a E0b ST17 V1R128).
destruct POST as (z0 & z1 & z2 & w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & z3 & z4 & z5 & z6 & F5 & fc5 & m5 & e32' & -> & MU5 & WM5 & MI5 & ST5 & FRM5 & X325 & L325).
clear X32z FR2 ST4. cps_seg_post.

assert (OF5 : offsh [(e32, e32 + 160)]) by (cbn; pose proof (XSH : _ \/ _) as Y1; clear - Y1; unfold SH_LO, SH_HI in *; lia).
assert (ACX : forall f k o n, In (f, k) (rt_frames RT Σ) -> f mod 64 = 0 -> 0 < f -> f <= o -> o + n <= f + fs_size k -> 0 <= o -> o + n <= APP_TOP ->
acc asegs m2 o n -> acc asegs m5 o n).
{ intros f k o n Hin F64 F0 Ho Hn O0 OT AC2.
assert (AC4 : acc asegs m4 o n) by (apply (acc_pres_ex_frame _ _ _ _ _ m2 m4 f k o n PRES4 Hin (mod64_mod8 _ F64) (fs_size_mod8 k)); [lia | exact Ho | exact Hn | exact OT | exact XSH | exact AC2]).
assert (OB4 : aobj asegs m4 o n) by (split; [exact O0|]; split; [exact OT| exact AC4]).
exact (proj2 (proj2 (aobj_munch asegs _ m4 m5 o n OB4 MU5 (shfree_of_aobj asegs _ m4 o n OF5 OB4)))). }
apply Hk. exists Σ. split; [| repeat split; reflexivity].
eapply ASTA_conseq; [eassumption|]. intros ms <-. exists w0, m5, eb, e32', pg'.
split; [rewrite ESP; unfold ret_stL; do 16 eexists; split; [reflexivity| exact FRM5]|].
split. { split; [assumption|]. split; [exact MI5|]. split; [cps_wmono| exact ST5]. }
split; [exact PF|].
split; [exact XE|]. split; [reflexivity|]. split; [exact X325|]. split; [exact L325|]. split; [exact XPV2|]. split; [exact XPG2|]. split; [exact LPG2|].
split; [split; [exists rj; split; [exact Lrj| exact OBJ]| split; [exists bs; split; [exact (proj2 (u8arr_rw_CB m5 D bs) DAT)| exact Hbs]| exact SIDE]]|].
split; [exact OKB1|]. split; [exact ARGS|].
split; [apply (ACX fq kq e32 160 INQ FQ64 FQ0 Q1); [clear - Q2; lia | exact (proj1 OB32) | exact (proj1 (proj2 OB32)) | exact AC322]|].
split; [apply (ACX fq kq pv 4 INQ FQ64 FQ0 V1); [clear - V2; lia | exact (proj1 OBPV) | exact (proj1 (proj2 OBPV)) | exact ACPV2]|].
split; [apply (ACX fq kq pg 12 INQ FQ64 FQ0 G1); [clear - G2; lia | exact (proj1 OBPG) | exact (proj1 (proj2 OBPG)) | exact ACPG2]|].
apply (ACX fa ka A 48 INA FA64 FA0 A1); [clear - A2; lia | exact (proj1 OBA0) | exact (proj1 (proj2 OBA0)) | exact ACA2].
Qed.
End P3CPS.
