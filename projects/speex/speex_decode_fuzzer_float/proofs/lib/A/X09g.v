(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS Require Import X0mx X0k2.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1da X1dg X1df X1ck.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1nt X1rh X1re.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1cg.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0bp X0j9 X0ec X001 X00b X04b X07z X05o X05p X05s X05l X09e X082 X08y X09h.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X12c X14x X0r0 X0ra X0v9 X0yr X0wl X0yt X0zq X104.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14x OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0r0 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ra OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0v9 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0yr OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0wl OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0yt OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0zq OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X104.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section NoiseCPS.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Context {ptr : Type}.

Theorem noise_cb_innov : @innov_unquant_cps RT ptr InnovNoiseCodebookUnquant.
Proof using AF.
intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
A D b inn seedp PAR lo P0 N0 PD ND fa ka is0 seed0 stk8
FDO MST -> -> -> -> -> -> -> REP OKB _ XI LI DST XS INL SL SH S4 INA (A1 & A2 & A3 & A4) IND DL DH HDP HAI ART0 MI0 FRM0 ST0 LOW LOR SPT SPA POA.
intros T c Hc Hk.
set (usp := bv_unsigned sp) in *.
assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned).
unfold entry_st in Hc. rewrite ESP in Hc. cbn [innov_entryA innov_bits] in *.
assert (LU : lo <= usp) by (unfold RT_STACK, INNOV_STACK in LOR; clear - LOR; lia).
destruct (dst_obj_facts RT AF Σ m inn 160 lo usp ART0 LOW LU SPT POA ltac:(reflexivity) DST) as (Q3 & I0 & IT & ISH & IAP & ITOP & Q4 & _ & _ & ILA).
destruct (live_below_lo RT AF Σ m P0 N0 lo ART0 INL LOW) as (BL0 & BL1 & BL2).
destruct (live_facts RT AF Σ m P0 N0 ART0 INL) as (_ & _ & LIM & LS).
destruct (frame_live_apart RT AF Σ m fa ka P0 N0 ART0 INA INL) as (FLAA & _).
destruct (live_below_lo RT AF Σ m PD ND lo ART0 IND LOW) as (BD0 & BD1 & _).
destruct (frame_below_lo RT AF Σ m fa ka lo ART0 INA LOW) as (FBA & _ & _).
pose proof (frame_facts RT AF Σ m fa ka ART0 INA) as (FA0 & FA64 & FAI & _ & FAS & _).
destruct (af_acc_live RT AF Σ m P0 N0 ART0 INL) as (_ & ACL).
pose proof (af_client_consts RT AF Σ m ART0) as CC0.
pose proof (pres_fp_refl (rt_live RT Σ) (rt_frames RT Σ) usp [(inn, inn + 160); (seedp, seedp + 4); (A, A + BITS_SIZEOF)] m) as PF.
pose proof (fun a => aclient_split RT AF Σ m usp a ART0) as SPL.
pose proof (fs_size_ge64 ka) as FSZA.
pose proof (ILA P0 N0 INL) as ILP. pose proof (ILA PD ND IND) as ILD. clear ILA.

assert (DCL : (exists fq kq, In (fq, kq) (rt_frames RT Σ) /\ fq <= inn /\ inn + 160 <= fq + fs_size kq - 8) \/ (usp <= inn /\ inn + 160 <= USTACK_TOP)).
{ destruct DST as [(fq & kq & INQ & (Q1 & Q2 & _)) | INP]; [left; exists fq, kq; auto|].
right. pose proof (af_pois_range RT AF Σ m inn 160 ART0 INP) as (_ & _ & _ & R2). pose proof (POA (inn, 160) INP) as PA. unfold pz_lo in PA; cbn [fst] in PA.
assert (RR : inn + 160 <= alloca_rr inn 160) by (unfold alloca_rr; clear; Z.div_mod_to_equations; lia). clear - R2 PA RR. lia. }
clear DST.
cps_norm. unfold INNOV_STACK, BITS_SIZEOF in *.
assert (OBI : aobj bsegs m inn 160) by (split; [clear - I0; lia|]; split; [exact IT| exact Q3]).
assert (OBS : aobj bsegs m seedp 4) by (split; [clear - BL0 SL; lia|]; split; [unfold APP_TOP; clear - SH BL1 LOR SPT; lia|]; apply (acc_sub bsegs m P0 N0 _ _ ACL); clear - SL SH; lia).
assert (OBA0 : aobj bsegs m A 48) by (split; [clear - FA0 A1; lia|]; split; [unfold APP_TOP; clear - A2 FBA LOR SPT; lia| exact A3]).
assert (SSH : seedp + 4 <= SH_LO \/ SH_HI <= seedp) by (unfold SH_LO, SH_HI; clear - LS SL SH; lia).
assert (ISA : inn + 160 <= seedp \/ seedp + 4 <= inn) by (clear - ILP SL SH; lia).
assert (STOP : seedp + 4 <= 65536 \/ IMG_TOP_B <= seedp) by (unfold IMG_TOP_B, SEGTOP_A in *; clear - LIM SL SH; lia).
assert (SPOS : 0 < seedp) by (clear - BL0 SL; lia).
assert (OF1 : offsh [(inn, inn + 160); (seedp, seedp + 4); (usp + -16, usp)]) by (cbn; unfold SH_LO, SH_HI in *; clear - ISH SSH BL2 LOR; lia).
assert (HAS : A + 48 <= seedp \/ seedp + 4 <= A) by (clear - FLAA A1 A2 SL SH; lia).
assert (HDI : D + sb_buf_size b <= inn \/ inn + 160 <= D) by (clear - ILD DL DH; lia).
assert (HDS : D + sb_buf_size b <= seedp \/ seedp + 4 <= D) by (pose proof (HDP : _ \/ _) as Y; clear - Y DL DH SL SH; lia).
pose proof (HAI : _ \/ _) as HAI'.
destruct REP as ((rj & Lrj & OBJ) & (bs & DAT & Hbs) & SIDE). unfold bits_cells in OBJ. apply (proj1 (u8arr_rw_CB m D bs)) in DAT.
assert (Lbs : Z.of_nat (length bs) = sb_buf_size b) by (pose proof OKB as OK'; unfold bits_ok in OK'; rewrite Hbs, zlength_map_unsigned in OK'; clear - OK'; lia).
assert (LO16 : lo <= usp - 16) by (clear - LOR; lia).
assert (SPH : usp < 2^63) by (clear - SPT; lia).
assert (SAP : seedp + 4 <= lo \/ usp <= seedp) by (left; clear - BL1 SH; lia).
pose proof (noise_cb_walk inn seedp usp lo ra gp (Z_to_bv 64 0x638c98) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m OBI OBS Q4 S4 LO16 BL2 SPH ISH SSH IAP SAP ISA) as WALK.
destruct DCL as [(fq & kq & INQ & Q1 & Q2) | (IU & ITT)];
[ pose proof (frame_facts RT AF Σ m fq kq ART0 INQ) as (_ & _ & FQI & _);
assert (ITOPB : IMG_TOP_B <= inn) by (unfold IMG_TOP_B, SEGTOP_A in *; clear - FQI Q1; lia); clear FQI
| assert (ITOPB : IMG_TOP_B <= inn) by (unfold IMG_TOP_B; ulc) ].
all: cps_hide.
all: cps_seg (WALK is0 seed0).
all: unfold noise_cb_post in POST.
all: destruct POST as (x0 & x1 & x2 & y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & x3 & x4 & x5 & x6 & F' & fc' & m1 & is' & seed' & -> & MU1 & WM1 & MI1 & ST1' & FRM1 & XI1 & LI1 & XS1).
all: pose proof (aobj_munch bsegs _ m m1 inn 160 OBI MU1 (shfree_of_aobj bsegs _ m inn 160 OF1 OBI)) as (_ & _ & ACI).
all: pose proof (aobj_munch bsegs _ m m1 A 48 OBA0 MU1 (shfree_of_aobj bsegs _ m A 48 OF1 OBA0)) as (_ & _ & ACA).
all: clear XI XS ST0 WALK.
all: cps_seg_post.
all: apply Hk.
all: exists Σ.
all: (split; [| repeat split; reflexivity]).
all: (eapply ASTA_conseq; [eassumption|]).
all: intros ms <-.
all: exists y0, m1, is', seed'.
all: (split; [rewrite ESP; unfold ret_stL; do 16 eexists; split; [reflexivity| exact FRM1]|]).
all: (split; [split; [assumption|]; split; [exact MI1|]; split; [cps_wmono| exact ST1']|]).
all: (split; [exact PF|]).
all: (split; [exact XI1|]; split; [exact LI1|]; split; [exact XS1|]).
all: (split; [split; [exists rj; split; [exact Lrj| exact OBJ]| split; [exists bs; split; [exact (proj2 (u8arr_rw_CB m1 D bs) DAT)| exact Hbs]| exact SIDE]]|]).
all: (split; [exact OKB|]; split; [exact ACI| exact ACA]).
Qed.
End NoiseCPS.
End B_TWIN.

Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section NoiseCPS.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Context {ptr : Type}.

Theorem noise_cb_innov : @innov_unquant_cps RT ptr InnovNoiseCodebookUnquant.
Proof using AF.
intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
A D b inn seedp PAR lo P0 N0 PD ND fa ka is0 seed0 stk8
FDO MST -> -> -> -> -> -> -> REP OKB _ XI LI DST XS INL SL SH S4 INA (A1 & A2 & A3 & A4) IND DL DH HDP HAI ART0 MI0 FRM0 ST0 LOW LOR SPT SPA POA.
intros T c Hc Hk.
set (usp := bv_unsigned sp) in *.
assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned).
unfold entry_st in Hc. rewrite ESP in Hc. cbn [innov_entryA innov_bits] in *.
assert (LU : lo <= usp) by (unfold RT_STACK, INNOV_STACK in LOR; clear - LOR; lia).
destruct (dst_obj_facts RT AF Σ m inn 160 lo usp ART0 LOW LU SPT POA ltac:(reflexivity) DST) as (Q3 & I0 & IT & ISH & IAP & ITOP & Q4 & _ & _ & ILA).
destruct (live_below_lo RT AF Σ m P0 N0 lo ART0 INL LOW) as (BL0 & BL1 & BL2).
destruct (live_facts RT AF Σ m P0 N0 ART0 INL) as (_ & _ & LIM & LS).
destruct (frame_live_apart RT AF Σ m fa ka P0 N0 ART0 INA INL) as (FLAA & _).
destruct (live_below_lo RT AF Σ m PD ND lo ART0 IND LOW) as (BD0 & BD1 & _).
destruct (frame_below_lo RT AF Σ m fa ka lo ART0 INA LOW) as (FBA & _ & _).
pose proof (frame_facts RT AF Σ m fa ka ART0 INA) as (FA0 & FA64 & FAI & _ & FAS & _).
destruct (af_acc_live RT AF Σ m P0 N0 ART0 INL) as (_ & ACL).
pose proof (af_client_consts RT AF Σ m ART0) as CC0.
pose proof (pres_fp_refl (rt_live RT Σ) (rt_frames RT Σ) usp [(inn, inn + 160); (seedp, seedp + 4); (A, A + BITS_SIZEOF)] m) as PF.
pose proof (fun a => aclient_split RT AF Σ m usp a ART0) as SPL.
pose proof (fs_size_ge64 ka) as FSZA.
pose proof (ILA P0 N0 INL) as ILP. pose proof (ILA PD ND IND) as ILD. clear ILA.

assert (DCL : (exists fq kq, In (fq, kq) (rt_frames RT Σ) /\ fq <= inn /\ inn + 160 <= fq + fs_size kq - 8) \/ (usp <= inn /\ inn + 160 <= USTACK_TOP)).
{ destruct DST as [(fq & kq & INQ & (Q1 & Q2 & _)) | INP]; [left; exists fq, kq; auto|].
right. pose proof (af_pois_range RT AF Σ m inn 160 ART0 INP) as (_ & _ & _ & R2). pose proof (POA (inn, 160) INP) as PA. unfold pz_lo in PA; cbn [fst] in PA.
assert (RR : inn + 160 <= alloca_rr inn 160) by (unfold alloca_rr; clear; Z.div_mod_to_equations; lia). clear - R2 PA RR. lia. }
clear DST.
cps_norm. unfold INNOV_STACK, BITS_SIZEOF in *.
assert (OBI : aobj asegs m inn 160) by (split; [clear - I0; lia|]; split; [exact IT| exact Q3]).
assert (OBS : aobj asegs m seedp 4) by (split; [clear - BL0 SL; lia|]; split; [unfold APP_TOP; clear - SH BL1 LOR SPT; lia|]; apply (acc_sub asegs m P0 N0 _ _ ACL); clear - SL SH; lia).
assert (OBA0 : aobj asegs m A 48) by (split; [clear - FA0 A1; lia|]; split; [unfold APP_TOP; clear - A2 FBA LOR SPT; lia| exact A3]).
assert (SSH : seedp + 4 <= SH_LO \/ SH_HI <= seedp) by (unfold SH_LO, SH_HI; clear - LS SL SH; lia).
assert (ISA : inn + 160 <= seedp \/ seedp + 4 <= inn) by (clear - ILP SL SH; lia).
assert (STOP : seedp + 4 <= 65536 \/ IMG_TOP <= seedp) by (unfold IMG_TOP; clear - LIM SL SH; lia).
assert (OF1 : offsh [(inn, inn + 160); (seedp, seedp + 4); (usp + -16, usp)]) by (cbn; unfold SH_LO, SH_HI in *; clear - ISH SSH BL2 LOR; lia).
assert (HAS : A + 48 <= seedp \/ seedp + 4 <= A) by (clear - FLAA A1 A2 SL SH; lia).
assert (HDI : D + sb_buf_size b <= inn \/ inn + 160 <= D) by (clear - ILD DL DH; lia).
assert (HDS : D + sb_buf_size b <= seedp \/ seedp + 4 <= D) by (pose proof (HDP : _ \/ _) as Y; clear - Y DL DH SL SH; lia).
pose proof (HAI : _ \/ _) as HAI'.
destruct REP as ((rj & Lrj & OBJ) & (bs & DAT & Hbs) & SIDE). unfold bits_cells in OBJ. apply (proj1 (u8arr_rw_CB m D bs)) in DAT.
assert (Lbs : Z.of_nat (length bs) = sb_buf_size b) by (pose proof OKB as OK'; unfold bits_ok in OK'; rewrite Hbs, zlength_map_unsigned in OK'; clear - OK'; lia).
assert (LO16 : lo <= usp - 16) by (clear - LOR; lia).
assert (SPH : usp < 2^63) by (clear - SPT; lia).
assert (SAP : seedp + 4 <= lo \/ usp <= seedp) by (left; clear - BL1 SH; lia).
pose proof (noise_cb_walk inn seedp usp lo ra gp (Z_to_bv 64 6489176) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m OBI OBS Q4 S4 LO16 BL2 SPH ISH SSH IAP SAP ISA) as WALK.
destruct DCL as [(fq & kq & INQ & Q1 & Q2) | (IU & ITT)].
all: cps_hide.
all: cps_seg (WALK is0 seed0).
all: unfold noise_cb_post in POST.
all: destruct POST as (x0 & x1 & x2 & y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & x3 & x4 & x5 & x6 & F' & fc' & m1 & is' & seed' & -> & MU1 & WM1 & MI1 & ST1' & FRM1 & XI1 & LI1 & XS1).
all: pose proof (aobj_munch asegs _ m m1 inn 160 OBI MU1 (shfree_of_aobj asegs _ m inn 160 OF1 OBI)) as (_ & _ & ACI).
all: pose proof (aobj_munch asegs _ m m1 A 48 OBA0 MU1 (shfree_of_aobj asegs _ m A 48 OF1 OBA0)) as (_ & _ & ACA).
all: clear XI XS ST0 WALK.
all: cps_seg_post.
all: apply Hk.
all: exists Σ.
all: (split; [| repeat split; reflexivity]).
all: (eapply ASTA_conseq; [eassumption|]).
all: intros ms <-.
all: exists y0, m1, is', seed'.
all: (split; [rewrite ESP; unfold ret_stL; do 16 eexists; split; [reflexivity| exact FRM1]|]).
all: (split; [split; [assumption|]; split; [exact MI1|]; split; [cps_wmono| exact ST1']|]).
all: (split; [exact PF|]).
all: (split; [exact XI1|]; split; [exact LI1|]; split; [exact XS1|]).
all: (split; [split; [exists rj; split; [exact Lrj| exact OBJ]| split; [exists bs; split; [exact (proj2 (u8arr_rw_CB m1 D bs) DAT)| exact Hbs]| exact SIDE]]|]).
all: (split; [exact OKB|]; split; [exact ACI| exact ACA]).
Qed.
End NoiseCPS.
