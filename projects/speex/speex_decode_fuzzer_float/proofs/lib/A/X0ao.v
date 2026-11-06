(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS Require Import X0mx X0k2.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1da X1dg X1cg X1df X1ck.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0bp X0j9 X0ec X001 X00b X04b X07z X05o X05p X05s X089 X0ap X0as X0at X0ar.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X12c X14x X0r0 X0ra X0v9 X0yr X0wl X11a X11d X11c.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14x OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0r0 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ra OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0v9 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0yr OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0wl OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X11a OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X11d OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X11c.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma qmf_rr : forall a n, a mod 32 = 0 -> n mod 32 = 0 -> 0 <= n -> alloca_rr a n = a + n + 32.
Proof. intros a n H1 H2 H3. unfold alloca_rr. Z.div_mod_to_equations. lia. Qed.

Section QMF.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis APO : alloca_poison_contract RT.
Hypothesis AUN : allocas_unpoison_contract RT.

Ltac fold_qmfB H :=
lazymatch type of H with
| rw_cells ?sg ?mm ?A [?k0; ?k8; ?k16; C8 ?vs; C8 ?g1; C8 ?g0; C8 ?y; C8 ?m2; C8 ?top; CB 8 ?j72; CB 8 ?j80; CB 8 ?j88; CB 8 ?j96;
C8 ?c11; C8 ?c10; C8 ?c9; C8 ?c8; C8 ?c7; C8 ?c6; C8 ?c5; C8 ?c4; C8 ?c3; C8 ?c2; C8 ?c1; C8 ?c0; C8 ?cra] =>
change (rw_cells sg mm A (qmf_frameB k0 k8 k16 vs g1 g0 y m2 top j72 j80 j88 j96 c11 c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra)) in H
end.

Theorem qmf_synth16_ok_320 : qmf_synth_cps16 RT 320.
Proof using AF APO AUN.
intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m Y G0 G1 lo fp P0 N0 P1 N1 kp ys g0l g1l
FDO MST -> -> -> -> -> -> -> -> -> XY LY INF FPY YFP ACY Y4 XG0 LG0 INL0 PL0 PH0 G04 XG1 LG1 INL1 PL1 PH1 G14 SG01 POA FRM ART0 MI0 ST0 LOW LOR SPT U32.
intros T c Hc Hk.
set (usp := bv_unsigned sp) in *.
assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned).
unfold entry_st in Hc. rewrite ESP in Hc.
assert (FRN : rt_frames RT Σ <> []) by (intros E; rewrite E in INF; exact INF).
destruct (live_below_lo RT AF Σ m P0 N0 lo ART0 INL0 LOW) as (BL00 & BL01 & LOSH).
destruct (live_below_lo RT AF Σ m P1 N1 lo ART0 INL1 LOW) as (BL10 & BL11 & _).
destruct (frame_below_lo RT AF Σ m fp kp lo ART0 INF LOW) as (BF0 & _ & _).
pose proof (frame_facts RT AF Σ m fp kp ART0 INF) as (FF0 & _ & FF2 & _ & FF4 & _).
pose proof (live_facts RT AF Σ m P0 N0 ART0 INL0) as (_ & _ & _ & LSH0).
pose proof (live_facts RT AF Σ m P1 N1 ART0 INL1) as (_ & _ & _ & LSH1).
destruct (frame_live_apart RT AF Σ m fp kp P0 N0 ART0 INF INL0) as (FL0 & _).
destruct (frame_live_apart RT AF Σ m fp kp P1 N1 ART0 INF INL1) as (FL1 & _).
pose proof (pres_fp_refl (rt_live RT Σ) (rt_frames RT Σ) usp [(Y, Y + 4 * 320); (G0, G0 + 256); (G1, G1 + 256)] m) as PF.
pose proof (fun a => aclient_split RT AF Σ m usp a ART0) as SPL.
pose proof (af_client_consts RT AF Σ m ART0) as CC0.
assert (FSZ : 0 <= fs_size kp) by (unfold fs_size; apply Z.shiftl_nonneg; lia).
cps_norm. cps_hide.

cps_seg (qmf_w1B_320 Y G0 G1 usp lo).
destruct POST as (j0 & j1 & j72 & j80 & j88 & j96 & jh & m1 & -> & MU1 & WM1 & MI1 & ST1 & FR1 & HULL1).
assert (ACY1 : acc bsegs m1 Y (4 * 320)).
{ refine (proj2 (proj2 (aobj_munch bsegs _ m m1 Y (4 * 320) _ MU1 _))); [split; [ulc|]; split; [ulc| exact ACY]|].
apply shfree_of_offsh; [cbn; unfold SH_LO, SH_HI; repeat split; ulc| ulc| ulc]. }
unfold qmf_frameB in FR1. cps_seg_post.

assert (EU1 : bv_unsigned (Z_to_bv 64 (usp + -1040)) = usp + -1040) by (apply unsigned_lit; ulc).
assert (RR1 : alloca_rr (usp + -1008) 768 = usp + -208) by (rewrite qmf_rr; [clear; lia | clear - U32; Z.div_mod_to_equations; lia | reflexivity | lia]).
cps_rt (APO Σ PMc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 (usp + -1008) 768 lo).
{ rewrite RR1. apply (pois_above_le _ usp); [exact POA| clear; lia]. }
{ cps_callok. }
intros c2 (Σ1 & Hc2 & PO1 & LV1 & FRS1 & SP1 & CR1).
cps_unpack Hc2 as (m2 & v1 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2 & ACX1 & ACT2).
cps_sigma LV1 FRS1 SP1.
assert (INX1 : In (usp + -1008, 768) (rt_pois RT Σ1)) by (rewrite PO1; left; reflexivity).
assert (ACY2 : acc bsegs m2 Y (4 * 320)) by (apply (ACT2 Y (4 * 320) ACY1); [ulc| left; ulc]).

fold_qmfB FR1.
cps_seg (qmf_w2B_320 Y G0 G1 usp lo).
destruct POST as (jh2 & m3 & -> & MU3 & WM3 & MI3 & ST3 & FR3 & HULL2).
assert (ACY3 : acc bsegs m3 Y (4 * 320)).
{ refine (proj2 (proj2 (aobj_munch bsegs _ m2 m3 Y (4 * 320) _ MU3 _))); [split; [ulc|]; split; [ulc| exact ACY2]|].
apply shfree_of_offsh; [cbn; unfold SH_LO, SH_HI; repeat split; ulc| ulc| ulc]. }
clear FR1. unfold qmf_frameB in FR3. cps_seg_post.

assert (EU2 : bv_unsigned (Z_to_bv 64 (usp + -1872)) = usp + -1872) by (apply unsigned_lit; ulc).
assert (RR2 : alloca_rr (usp + -1840) 768 = usp + -1040) by (rewrite qmf_rr; [clear; lia | clear - U32; Z.div_mod_to_equations; lia | reflexivity | lia]).
cps_rt (APO Σ1 PMc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m3 (usp + -1840) 768 lo).
{ rewrite RR2, PO1. apply pois_above_cons; [rewrite RR1; apply (pois_above_le _ usp); [exact POA| clear; lia]| clear; lia| clear; lia]. }
{ rewrite FRS1. exact FRN. }
{ cps_callok. }
intros c4 (Σ2 & Hc4 & PO2 & LV2 & FRS2 & SP2 & CR2).
cps_unpack Hc4 as (m4 & v4 & RS4 & (ART4 & MI4 & WM4 & ST4) & PRES4 & ACX2 & ACT4).
cps_sigma LV2 FRS2 SP2.
assert (INX2 : In (usp + -1840, 768) (rt_pois RT Σ2)) by (rewrite PO2; left; reflexivity).
assert (INX1' : In (usp + -1008, 768) (rt_pois RT Σ2)) by (rewrite PO2; right; exact INX1).
assert (ACY4 : acc bsegs m4 Y (4 * 320)) by (apply (ACT4 Y (4 * 320) ACY3); [ulc| left; ulc]).

cbn [Z.to_nat Pos.to_nat Pos.iter_op Nat.add] in HULL1, HULL2.
apply (rw_cells_split_CB bsegs _ _ [] 832 _ [] [32; 640; 128; 32]%nat) in HULL1; [| reflexivity]. cbn [mk_CB_cells app] in HULL1.
chunk_uncons HULL1 as RZ1. chunk_uncons HULL1 as XA1. chunk_uncons HULL1 as XB1. rename HULL1 into PAD1.
apply (rw_cells_split_CB bsegs _ _ [] 832 _ [] [32; 640; 128; 32]%nat) in HULL2; [| reflexivity]. cbn [mk_CB_cells app] in HULL2.
chunk_uncons HULL2 as RZ2. chunk_uncons HULL2 as XA2. chunk_uncons HULL2 as XB2. rename HULL2 into PAD2.
replace (usp + -1040 + 32) with (usp + -1008) in * by (clear; lia). replace (usp + -1008 + 640 + 128) with (usp + -240) in * by (clear; lia).
replace (usp + -1872 + 32) with (usp + -1840) in * by (clear; lia). replace (usp + -1840 + 640 + 128) with (usp + -1072) in * by (clear; lia).
destruct (rw_cells_CB_f32 bsegs _ _ 160%nat _ XA1) as (xa1 & LXA1 & XA1f). destruct (rw_cells_CB_f32 bsegs _ _ 32%nat _ XB1) as (xb1 & LXB1 & XB1f).
destruct (rw_cells_CB_f32 bsegs _ _ 160%nat _ XA2) as (xa2 & LXA2 & XA2f). destruct (rw_cells_CB_f32 bsegs _ _ 32%nat _ XB2) as (xb2 & LXB2 & XB2f).
clear XA1 XB1 XA2 XB2.
assert (LXA1z : Z.of_nat (length xa1) = 2 * 80) by (rewrite LXA1; reflexivity). assert (LXA2z : Z.of_nat (length xa2) = 2 * 80) by (rewrite LXA2; reflexivity).

destruct (af_acc_live RT AF Σ2 m4 P0 N0 ART4 INL0) as (_ & ACL0). destruct (af_acc_live RT AF Σ2 m4 P1 N1 ART4 INL1) as (_ & ACL1).
assert (OBY : aobj bsegs m4 Y (16 * 80)) by (split; [ulc|]; split; [ulc|]; exact ACY4).
assert (OBG0 : aobj bsegs m4 G0 256) by (split; [ulc|]; split; [ulc|]; exact (acc_sub bsegs m4 P0 N0 G0 256 ACL0 PL0 PH0)).
assert (OBG1 : aobj bsegs m4 G1 256) by (split; [ulc|]; split; [ulc|]; exact (acc_sub bsegs m4 P1 N1 G1 256 ACL1 PL1 PH1)).
assert (OB1 : aobj bsegs m4 (usp + -1008) (8 * 80 + 128)) by (split; [ulc|]; split; [ulc|]; exact (af_acc_pois RT AF Σ2 m4 _ _ ART4 INX1')).
assert (OB2 : aobj bsegs m4 (usp + -1840) (8 * 80 + 128)) by (split; [ulc|]; split; [ulc|]; exact (af_acc_pois RT AF Σ2 m4 _ _ ART4 INX2)).
assert (OBA : aobj bsegs m4 A_H0 256) by (apply (aobj_lit RT AF Σ2 m4 A_H0 256 ART4); [unfold ACC_LITS, A_H0; cbn [In]; repeat (first [left; reflexivity | right]) | unfold A_H0; lia | unfold A_H0, APP_TOP; lia]).
chunk_uncons FR3 as FZ. chunk_uncons FR3 as S1c. chunk_uncons FR3 as S2c. chunk_uncons FR3 as S3c. chunk_uncons FR3 as S4c.
chunk_uncons FR3 as S5c. chunk_uncons FR3 as S6c. chunk_uncons FR3 as S7c. chunk_uncons FR3 as S8c.
chunk_cat S1c S2c. chunk_cat S1c S3c. chunk_cat S1c S4c. chunk_cat S1c S5c. chunk_cat S1c S6c. chunk_cat S1c S7c. chunk_cat S1c S8c.
cps_seg (qmf_body16B (usp + -208) lo (usp + -1008) (usp + -1840) (usp + -1872) Y G0 G1 80 _ _ _ ys g0l g1l xa1 xb1 xa2 xb2).
{ unfold IMG_TOP_B; ulc. }
destruct POST as (ra' & t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & s2' & s3' & s4' & s5' & s6' & s7' & s8' & s9' & s10' & s11' & t3' & t4' & t5' & t6'
& F' & fc' & m5 & w8 & w16 & ys' & g0' & g1' & x1' & x2' & -> & MU5 & WM5 & MI5 & FRM5 & FR5 & XY5 & LY5 & XG05 & LG05 & XG15 & LG15 & XL1 & LXL1 & XL2 & LXL2).
assert (ACY5 : acc bsegs m5 Y (4 * 320)).
{ refine (proj2 (proj2 (aobj_munch bsegs _ m4 m5 Y (4 * 320) _ MU5 _))); [split; [ulc|]; split; [ulc| exact ACY4]|].
apply shfree_of_offsh; [cbn; unfold SH_LO, SH_HI; repeat split; ulc| ulc| ulc]. }
clear S1c XY XG0 XG1 XA1f XB1f XA2f XB2f OBY OBG0 OBG1 OB1 OB2 OBA ACL0 ACL1.
cps_seg_post.

chunk_cat FZ FR5. chunk_cat FZ FR3.
fold_qmfB FZ.
cps_seg (qmf_w5B usp lo (usp + -1872)).
subst ms.
cps_rt (AUN Σ2 PMc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m5 (usp + -1872) (usp + -144) lo).
{ rewrite PO2, PO1. intros e [<-|[<-|He]].
- left. unfold pz_lo, pz_hi. cbn [fst snd]. rewrite RR2. clear. lia.
- left. unfold pz_lo, pz_hi. cbn [fst snd]. rewrite RR1. clear. lia.
- right. pose proof (POA e He). lia. }
{ cps_callok. }
intros c6 (Σ3 & Hc6 & PO3 & LV3 & FRS3 & SP3 & CR3).
cps_unpack Hc6 as (m6 & v6 & RS6 & (ART6 & MI6 & WM6 & ST6) & PRES6 & ACT6).
assert (ACY6 : acc bsegs m6 Y (4 * 320)) by (apply (ACT6 Y (4 * 320) ACY5); [ulc| left; ulc]).

assert (L1n : length x1' = 192%nat) by (clear - LXL1; lia). assert (L2n : length x2' = 192%nat) by (clear - LXL2; lia).
apply rw_cells_f32_CB in XL1. rewrite L1n in XL1. change (4 * 192)%nat with 768%nat in XL1.
apply rw_cells_f32_CB in XL2. rewrite L2n in XL2. change (4 * 192)%nat with 768%nat in XL2.
chunk_cat RZ1 XL1. chunk_cat RZ1 PAD1. apply rw_cells_to_CB in RZ1. cbn [cells_size csize Nat.add] in RZ1.
chunk_cat RZ2 XL2. chunk_cat RZ2 PAD2. apply rw_cells_to_CB in RZ2. cbn [cells_size csize Nat.add] in RZ2.
cps_seg (qmf_w6B_320 usp lo).
destruct POST as (-> & ST9).
apply Hk. exists Σ3. split.
2:{ split; [congruence|]. split; [congruence|]. split; [congruence|]. split; [congruence|].
rewrite PO3, PO2, PO1. rewrite !pois_drop_cons_below by (unfold pz_lo; cbn [fst]; clear; lia).
apply pois_drop_above. apply (pois_above_le _ usp); [exact POA| clear; lia]. }
eapply ASTA_conseq; [eassumption|]. intros ms <-. exists v6, m6, ys', g0', g1'.
split; [rewrite ESP; unfold ret_stL; do 16 eexists; split; [reflexivity| exact FRM5]|].
split. { split; [exact ART6|]. split; [exact MI6|]. split; [cps_wmono| exact ST9]. }
split; [exact PF|]. split; [exact XY5|]. split; [exact LY5|]. split; [exact XG05|]. split; [exact LG05|]. split; [exact XG15|]. split; [exact LG15| exact ACY6].
Qed.

Theorem qmf_synth16_ok_640 : qmf_synth_cps16 RT 640.
Proof using AF APO AUN.
intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m Y G0 G1 lo fp P0 N0 P1 N1 kp ys g0l g1l
FDO MST -> -> -> -> -> -> -> -> -> XY LY INF FPY YFP ACY Y4 XG0 LG0 INL0 PL0 PH0 G04 XG1 LG1 INL1 PL1 PH1 G14 SG01 POA FRM ART0 MI0 ST0 LOW LOR SPT U32.
intros T c Hc Hk.
set (usp := bv_unsigned sp) in *.
assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned).
unfold entry_st in Hc. rewrite ESP in Hc.
assert (FRN : rt_frames RT Σ <> []) by (intros E; rewrite E in INF; exact INF).
destruct (live_below_lo RT AF Σ m P0 N0 lo ART0 INL0 LOW) as (BL00 & BL01 & LOSH).
destruct (live_below_lo RT AF Σ m P1 N1 lo ART0 INL1 LOW) as (BL10 & BL11 & _).
destruct (frame_below_lo RT AF Σ m fp kp lo ART0 INF LOW) as (BF0 & _ & _).
pose proof (frame_facts RT AF Σ m fp kp ART0 INF) as (FF0 & _ & FF2 & _ & FF4 & _).
pose proof (live_facts RT AF Σ m P0 N0 ART0 INL0) as (_ & _ & _ & LSH0).
pose proof (live_facts RT AF Σ m P1 N1 ART0 INL1) as (_ & _ & _ & LSH1).
destruct (frame_live_apart RT AF Σ m fp kp P0 N0 ART0 INF INL0) as (FL0 & _).
destruct (frame_live_apart RT AF Σ m fp kp P1 N1 ART0 INF INL1) as (FL1 & _).
pose proof (pres_fp_refl (rt_live RT Σ) (rt_frames RT Σ) usp [(Y, Y + 4 * 640); (G0, G0 + 256); (G1, G1 + 256)] m) as PF.
pose proof (fun a => aclient_split RT AF Σ m usp a ART0) as SPL.
pose proof (af_client_consts RT AF Σ m ART0) as CC0.
assert (FSZ : 0 <= fs_size kp) by (unfold fs_size; apply Z.shiftl_nonneg; lia).
cps_norm. cps_hide.

cps_seg (qmf_w1B_640 Y G0 G1 usp lo).
destruct POST as (j0 & j1 & j72 & j80 & j88 & j96 & jh & m1 & -> & MU1 & WM1 & MI1 & ST1 & FR1 & HULL1).
assert (ACY1 : acc bsegs m1 Y (4 * 640)).
{ refine (proj2 (proj2 (aobj_munch bsegs _ m m1 Y (4 * 640) _ MU1 _))); [split; [ulc|]; split; [ulc| exact ACY]|].
apply shfree_of_offsh; [cbn; unfold SH_LO, SH_HI; repeat split; ulc| ulc| ulc]. }
unfold qmf_frameB in FR1. cps_seg_post.

assert (EU1 : bv_unsigned (Z_to_bv 64 (usp + -1680)) = usp + -1680) by (apply unsigned_lit; ulc).
assert (RR1 : alloca_rr (usp + -1648) 1408 = usp + -208) by (rewrite qmf_rr; [clear; lia | clear - U32; Z.div_mod_to_equations; lia | reflexivity | lia]).
cps_rt (APO Σ PMc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 (usp + -1648) 1408 lo).
{ rewrite RR1. apply (pois_above_le _ usp); [exact POA| clear; lia]. }
{ cps_callok. }
intros c2 (Σ1 & Hc2 & PO1 & LV1 & FRS1 & SP1 & CR1).
cps_unpack Hc2 as (m2 & v1 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2 & ACX1 & ACT2).
cps_sigma LV1 FRS1 SP1.
assert (INX1 : In (usp + -1648, 1408) (rt_pois RT Σ1)) by (rewrite PO1; left; reflexivity).
assert (ACY2 : acc bsegs m2 Y (4 * 640)) by (apply (ACT2 Y (4 * 640) ACY1); [ulc| left; ulc]).

fold_qmfB FR1.
cps_seg (qmf_w2B_640 Y G0 G1 usp lo).
destruct POST as (jh2 & m3 & -> & MU3 & WM3 & MI3 & ST3 & FR3 & HULL2).
assert (ACY3 : acc bsegs m3 Y (4 * 640)).
{ refine (proj2 (proj2 (aobj_munch bsegs _ m2 m3 Y (4 * 640) _ MU3 _))); [split; [ulc|]; split; [ulc| exact ACY2]|].
apply shfree_of_offsh; [cbn; unfold SH_LO, SH_HI; repeat split; ulc| ulc| ulc]. }
clear FR1. unfold qmf_frameB in FR3. cps_seg_post.

assert (EU2 : bv_unsigned (Z_to_bv 64 (usp + -3152)) = usp + -3152) by (apply unsigned_lit; ulc).
assert (RR2 : alloca_rr (usp + -3120) 1408 = usp + -1680) by (rewrite qmf_rr; [clear; lia | clear - U32; Z.div_mod_to_equations; lia | reflexivity | lia]).
cps_rt (APO Σ1 PMc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m3 (usp + -3120) 1408 lo).
{ rewrite RR2, PO1. apply pois_above_cons; [rewrite RR1; apply (pois_above_le _ usp); [exact POA| clear; lia]| clear; lia| clear; lia]. }
{ rewrite FRS1. exact FRN. }
{ cps_callok. }
intros c4 (Σ2 & Hc4 & PO2 & LV2 & FRS2 & SP2 & CR2).
cps_unpack Hc4 as (m4 & v4 & RS4 & (ART4 & MI4 & WM4 & ST4) & PRES4 & ACX2 & ACT4).
cps_sigma LV2 FRS2 SP2.
assert (INX2 : In (usp + -3120, 1408) (rt_pois RT Σ2)) by (rewrite PO2; left; reflexivity).
assert (INX1' : In (usp + -1648, 1408) (rt_pois RT Σ2)) by (rewrite PO2; right; exact INX1).
assert (ACY4 : acc bsegs m4 Y (4 * 640)) by (apply (ACT4 Y (4 * 640) ACY3); [ulc| left; ulc]).

cbn [Z.to_nat Pos.to_nat Pos.iter_op Nat.add] in HULL1, HULL2.
apply (rw_cells_split_CB bsegs _ _ [] 1472 _ [] [32; 1280; 128; 32]%nat) in HULL1; [| reflexivity]. cbn [mk_CB_cells app] in HULL1.
chunk_uncons HULL1 as RZ1. chunk_uncons HULL1 as XA1. chunk_uncons HULL1 as XB1. rename HULL1 into PAD1.
apply (rw_cells_split_CB bsegs _ _ [] 1472 _ [] [32; 1280; 128; 32]%nat) in HULL2; [| reflexivity]. cbn [mk_CB_cells app] in HULL2.
chunk_uncons HULL2 as RZ2. chunk_uncons HULL2 as XA2. chunk_uncons HULL2 as XB2. rename HULL2 into PAD2.
replace (usp + -1680 + 32) with (usp + -1648) in * by (clear; lia). replace (usp + -1648 + 1280 + 128) with (usp + -240) in * by (clear; lia).
replace (usp + -3152 + 32) with (usp + -3120) in * by (clear; lia). replace (usp + -3120 + 1280 + 128) with (usp + -1712) in * by (clear; lia).
destruct (rw_cells_CB_f32 bsegs _ _ 320%nat _ XA1) as (xa1 & LXA1 & XA1f). destruct (rw_cells_CB_f32 bsegs _ _ 32%nat _ XB1) as (xb1 & LXB1 & XB1f).
destruct (rw_cells_CB_f32 bsegs _ _ 320%nat _ XA2) as (xa2 & LXA2 & XA2f). destruct (rw_cells_CB_f32 bsegs _ _ 32%nat _ XB2) as (xb2 & LXB2 & XB2f).
clear XA1 XB1 XA2 XB2.
assert (LXA1z : Z.of_nat (length xa1) = 2 * 160) by (rewrite LXA1; reflexivity). assert (LXA2z : Z.of_nat (length xa2) = 2 * 160) by (rewrite LXA2; reflexivity).

destruct (af_acc_live RT AF Σ2 m4 P0 N0 ART4 INL0) as (_ & ACL0). destruct (af_acc_live RT AF Σ2 m4 P1 N1 ART4 INL1) as (_ & ACL1).
assert (OBY : aobj bsegs m4 Y (16 * 160)) by (split; [ulc|]; split; [ulc|]; exact ACY4).
assert (OBG0 : aobj bsegs m4 G0 256) by (split; [ulc|]; split; [ulc|]; exact (acc_sub bsegs m4 P0 N0 G0 256 ACL0 PL0 PH0)).
assert (OBG1 : aobj bsegs m4 G1 256) by (split; [ulc|]; split; [ulc|]; exact (acc_sub bsegs m4 P1 N1 G1 256 ACL1 PL1 PH1)).
assert (OB1 : aobj bsegs m4 (usp + -1648) (8 * 160 + 128)) by (split; [ulc|]; split; [ulc|]; exact (af_acc_pois RT AF Σ2 m4 _ _ ART4 INX1')).
assert (OB2 : aobj bsegs m4 (usp + -3120) (8 * 160 + 128)) by (split; [ulc|]; split; [ulc|]; exact (af_acc_pois RT AF Σ2 m4 _ _ ART4 INX2)).
assert (OBA : aobj bsegs m4 A_H0 256) by (apply (aobj_lit RT AF Σ2 m4 A_H0 256 ART4); [unfold ACC_LITS, A_H0; cbn [In]; repeat (first [left; reflexivity | right]) | unfold A_H0; lia | unfold A_H0, APP_TOP; lia]).
chunk_uncons FR3 as FZ. chunk_uncons FR3 as S1c. chunk_uncons FR3 as S2c. chunk_uncons FR3 as S3c. chunk_uncons FR3 as S4c.
chunk_uncons FR3 as S5c. chunk_uncons FR3 as S6c. chunk_uncons FR3 as S7c. chunk_uncons FR3 as S8c.
chunk_cat S1c S2c. chunk_cat S1c S3c. chunk_cat S1c S4c. chunk_cat S1c S5c. chunk_cat S1c S6c. chunk_cat S1c S7c. chunk_cat S1c S8c.
cps_seg (qmf_body16B (usp + -208) lo (usp + -1648) (usp + -3120) (usp + -3152) Y G0 G1 160 _ _ _ ys g0l g1l xa1 xb1 xa2 xb2).
{ unfold IMG_TOP_B; ulc. }
destruct POST as (ra' & t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & s2' & s3' & s4' & s5' & s6' & s7' & s8' & s9' & s10' & s11' & t3' & t4' & t5' & t6'
& F' & fc' & m5 & w8 & w16 & ys' & g0' & g1' & x1' & x2' & -> & MU5 & WM5 & MI5 & FRM5 & FR5 & XY5 & LY5 & XG05 & LG05 & XG15 & LG15 & XL1 & LXL1 & XL2 & LXL2).
assert (ACY5 : acc bsegs m5 Y (4 * 640)).
{ refine (proj2 (proj2 (aobj_munch bsegs _ m4 m5 Y (4 * 640) _ MU5 _))); [split; [ulc|]; split; [ulc| exact ACY4]|].
apply shfree_of_offsh; [cbn; unfold SH_LO, SH_HI; repeat split; ulc| ulc| ulc]. }
clear S1c XY XG0 XG1 XA1f XB1f XA2f XB2f OBY OBG0 OBG1 OB1 OB2 OBA ACL0 ACL1.
cps_seg_post.

chunk_cat FZ FR5. chunk_cat FZ FR3.
fold_qmfB FZ.
cps_seg (qmf_w5B usp lo (usp + -3152)).
subst ms.
cps_rt (AUN Σ2 PMc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m5 (usp + -3152) (usp + -144) lo).
{ rewrite PO2, PO1. intros e [<-|[<-|He]].
- left. unfold pz_lo, pz_hi. cbn [fst snd]. rewrite RR2. clear. lia.
- left. unfold pz_lo, pz_hi. cbn [fst snd]. rewrite RR1. clear. lia.
- right. pose proof (POA e He). lia. }
{ cps_callok. }
intros c6 (Σ3 & Hc6 & PO3 & LV3 & FRS3 & SP3 & CR3).
cps_unpack Hc6 as (m6 & v6 & RS6 & (ART6 & MI6 & WM6 & ST6) & PRES6 & ACT6).
assert (ACY6 : acc bsegs m6 Y (4 * 640)) by (apply (ACT6 Y (4 * 640) ACY5); [ulc| left; ulc]).

assert (L1n : length x1' = 352%nat) by (clear - LXL1; lia). assert (L2n : length x2' = 352%nat) by (clear - LXL2; lia).
apply rw_cells_f32_CB in XL1. rewrite L1n in XL1. change (4 * 352)%nat with 1408%nat in XL1.
apply rw_cells_f32_CB in XL2. rewrite L2n in XL2. change (4 * 352)%nat with 1408%nat in XL2.
chunk_cat RZ1 XL1. chunk_cat RZ1 PAD1. apply rw_cells_to_CB in RZ1. cbn [cells_size csize Nat.add] in RZ1.
chunk_cat RZ2 XL2. chunk_cat RZ2 PAD2. apply rw_cells_to_CB in RZ2. cbn [cells_size csize Nat.add] in RZ2.
cps_seg (qmf_w6B_640 usp lo).
destruct POST as (-> & ST9).
apply Hk. exists Σ3. split.
2:{ split; [congruence|]. split; [congruence|]. split; [congruence|]. split; [congruence|].
rewrite PO3, PO2, PO1. rewrite !pois_drop_cons_below by (unfold pz_lo; cbn [fst]; clear; lia).
apply pois_drop_above. apply (pois_above_le _ usp); [exact POA| clear; lia]. }
eapply ASTA_conseq; [eassumption|]. intros ms <-. exists v6, m6, ys', g0', g1'.
split; [rewrite ESP; unfold ret_stL; do 16 eexists; split; [reflexivity| exact FRM5]|].
split. { split; [exact ART6|]. split; [exact MI6|]. split; [cps_wmono| exact ST9]. }
split; [exact PF|]. split; [exact XY5|]. split; [exact LY5|]. split; [exact XG05|]. split; [exact LG05|]. split; [exact XG15|]. split; [exact LG15| exact ACY6].
Qed.

Theorem qmf_synth16_ok : forall N, N = 320 \/ N = 640 -> qmf_synth_cps16 RT N.
Proof using AF APO AUN. intros N [-> | ->]; [exact qmf_synth16_ok_320 | exact qmf_synth16_ok_640]. Qed.
End QMF.
End B_TWIN.

Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma qmf_rr : forall a n, a mod 32 = 0 -> n mod 32 = 0 -> 0 <= n -> alloca_rr a n = a + n + 32.
Proof. intros a n H1 H2 H3. unfold alloca_rr. Z.div_mod_to_equations. lia. Qed.

Section QMF.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis APO : alloca_poison_contract RT.
Hypothesis AUN : allocas_unpoison_contract RT.

Ltac fold_qmf16 H :=
lazymatch type of H with
| rw_cells ?sg ?mm ?A [CB 8 ?j0; C8 ?x1; C8 ?x2; C8 ?g0; C8 ?top; CB 8 ?j1; CB 8 ?j2; CB 8 ?j3; CB 8 ?j4; C8 ?c11; C8 ?c10; C8 ?c9; C8 ?c8; C8 ?c7; C8 ?c6; C8 ?c5; C8 ?c4;
C8 ?c3; C8 ?c2; C8 ?c1; C8 ?c0; C8 ?cra] =>
change (rw_cells sg mm A (qmf_frame16 top x1 x2 g0 j0 j1 j2 j3 j4 c11 c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra)) in H
end.

Theorem qmf_synth16_ok_320 : qmf_synth_cps16 RT 320.
Proof using AF APO AUN.
intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m Y G0 G1 lo fp P0 N0 P1 N1 kp ys g0l g1l
FDO MST -> -> -> -> -> -> -> -> -> XY LY INF FPY YFP ACY Y4 XG0 LG0 INL0 PL0 PH0 G04 XG1 LG1 INL1 PL1 PH1 G14 SG01 POA FRM ART0 MI0 ST0 LOW LOR SPT U32.
intros T c Hc Hk.
set (usp := bv_unsigned sp) in *.
assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned).
unfold entry_st in Hc. rewrite ESP in Hc.
assert (FRN : rt_frames RT Σ <> []) by (intros E; rewrite E in INF; exact INF).
destruct (live_below_lo RT AF Σ m P0 N0 lo ART0 INL0 LOW) as (BL00 & BL01 & LOSH).
destruct (live_below_lo RT AF Σ m P1 N1 lo ART0 INL1 LOW) as (BL10 & BL11 & _).
destruct (frame_below_lo RT AF Σ m fp kp lo ART0 INF LOW) as (BF0 & _ & _).
pose proof (frame_facts RT AF Σ m fp kp ART0 INF) as (FF0 & _ & FF2 & _ & FF4 & _).
pose proof (live_facts RT AF Σ m P0 N0 ART0 INL0) as (_ & _ & _ & LSH0).
pose proof (live_facts RT AF Σ m P1 N1 ART0 INL1) as (_ & _ & _ & LSH1).
destruct (frame_live_apart RT AF Σ m fp kp P0 N0 ART0 INF INL0) as (FL0 & _).
destruct (frame_live_apart RT AF Σ m fp kp P1 N1 ART0 INF INL1) as (FL1 & _).
pose proof (pres_fp_refl (rt_live RT Σ) (rt_frames RT Σ) usp [(Y, Y + 4 * 320); (G0, G0 + 256); (G1, G1 + 256)] m) as PF.
pose proof (fun a => aclient_split RT AF Σ m usp a ART0) as SPL.
pose proof (af_client_consts RT AF Σ m ART0) as CC0.
assert (FSZ : 0 <= fs_size kp) by (unfold fs_size; apply Z.shiftl_nonneg; lia).
cps_norm. cps_hide.

cps_seg (qmf_w1_16_320 Y G0 G1 usp lo).
destruct POST as (j0 & j1 & j2 & j3 & j4 & jh & m1 & -> & MU1 & WM1 & MI1 & ST1 & FR1 & HULL1).
assert (ACY1 : acc asegs m1 Y (4 * 320)).
{ refine (proj2 (proj2 (aobj_munch asegs _ m m1 Y (4 * 320) _ MU1 _))); [split; [ulc|]; split; [ulc| exact ACY]|].
apply shfree_of_offsh; [cbn; unfold SH_LO, SH_HI; repeat split; ulc| ulc| ulc]. }
unfold qmf_frame16 in FR1. cps_seg_post.

assert (EU1 : bv_unsigned (Z_to_bv 64 (usp + -1008)) = usp + -1008) by (apply unsigned_lit; ulc).
assert (RR1 : alloca_rr (usp + -976) 768 = usp + -176) by (rewrite qmf_rr; [clear; lia | clear - U32; Z.div_mod_to_equations; lia | reflexivity | lia]).
cps_rt (APO Σ PMc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 (usp + -976) 768 lo).
{ rewrite RR1. apply (pois_above_le _ usp); [exact POA| clear; lia]. }
{ cps_callok. }
intros c2 (Σ1 & Hc2 & PO1 & LV1 & FRS1 & SP1 & CR1).
cps_unpack Hc2 as (m2 & v1 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2 & ACX1 & ACT2).
cps_sigma LV1 FRS1 SP1.
assert (INX1 : In (usp + -976, 768) (rt_pois RT Σ1)) by (rewrite PO1; left; reflexivity).
assert (ACY2 : acc asegs m2 Y (4 * 320)) by (apply (ACT2 Y (4 * 320) ACY1); [ulc| left; ulc]).

fold_qmf16 FR1.
cps_seg (qmf_w2_16_320 Y G0 G1 usp lo).
destruct POST as (jh2 & m3 & -> & MU3 & WM3 & MI3 & ST3 & FR3 & HULL2).
assert (ACY3 : acc asegs m3 Y (4 * 320)).
{ refine (proj2 (proj2 (aobj_munch asegs _ m2 m3 Y (4 * 320) _ MU3 _))); [split; [ulc|]; split; [ulc| exact ACY2]|].
apply shfree_of_offsh; [cbn; unfold SH_LO, SH_HI; repeat split; ulc| ulc| ulc]. }
clear FR1. unfold qmf_frame16 in FR3. cps_seg_post.

assert (EU2 : bv_unsigned (Z_to_bv 64 (usp + -1840)) = usp + -1840) by (apply unsigned_lit; ulc).
assert (RR2 : alloca_rr (usp + -1808) 768 = usp + -1008) by (rewrite qmf_rr; [clear; lia | clear - U32; Z.div_mod_to_equations; lia | reflexivity | lia]).
cps_rt (APO Σ1 PMc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m3 (usp + -1808) 768 lo).
{ rewrite RR2, PO1. apply pois_above_cons; [rewrite RR1; apply (pois_above_le _ usp); [exact POA| clear; lia]| clear; lia| clear; lia]. }
{ rewrite FRS1. exact FRN. }
{ cps_callok. }
intros c4 (Σ2 & Hc4 & PO2 & LV2 & FRS2 & SP2 & CR2).
cps_unpack Hc4 as (m4 & v4 & RS4 & (ART4 & MI4 & WM4 & ST4) & PRES4 & ACX2 & ACT4).
cps_sigma LV2 FRS2 SP2.
assert (INX2 : In (usp + -1808, 768) (rt_pois RT Σ2)) by (rewrite PO2; left; reflexivity).
assert (INX1' : In (usp + -976, 768) (rt_pois RT Σ2)) by (rewrite PO2; right; exact INX1).
assert (ACY4 : acc asegs m4 Y (4 * 320)) by (apply (ACT4 Y (4 * 320) ACY3); [ulc| left; ulc]).

cbn [Z.to_nat Pos.to_nat Pos.iter_op Nat.add] in HULL1, HULL2.
apply (rw_cells_split_CB asegs _ _ [] 832 _ [] [32; 640; 128; 32]%nat) in HULL1; [| reflexivity]. cbn [mk_CB_cells app] in HULL1.
chunk_uncons HULL1 as RZ1. chunk_uncons HULL1 as XA1. chunk_uncons HULL1 as XB1. rename HULL1 into PAD1.
apply (rw_cells_split_CB asegs _ _ [] 832 _ [] [32; 640; 128; 32]%nat) in HULL2; [| reflexivity]. cbn [mk_CB_cells app] in HULL2.
chunk_uncons HULL2 as RZ2. chunk_uncons HULL2 as XA2. chunk_uncons HULL2 as XB2. rename HULL2 into PAD2.
replace (usp + -1008 + 32) with (usp + -976) in * by (clear; lia). replace (usp + -976 + 640 + 128) with (usp + -208) in * by (clear; lia).
replace (usp + -1840 + 32) with (usp + -1808) in * by (clear; lia). replace (usp + -1808 + 640 + 128) with (usp + -1040) in * by (clear; lia).
destruct (rw_cells_CB_f32 asegs _ _ 160%nat _ XA1) as (xa1 & LXA1 & XA1f). destruct (rw_cells_CB_f32 asegs _ _ 32%nat _ XB1) as (xb1 & LXB1 & XB1f).
destruct (rw_cells_CB_f32 asegs _ _ 160%nat _ XA2) as (xa2 & LXA2 & XA2f). destruct (rw_cells_CB_f32 asegs _ _ 32%nat _ XB2) as (xb2 & LXB2 & XB2f).
clear XA1 XB1 XA2 XB2.
assert (LXA1z : Z.of_nat (length xa1) = 2 * 80) by (rewrite LXA1; reflexivity). assert (LXA2z : Z.of_nat (length xa2) = 2 * 80) by (rewrite LXA2; reflexivity).

destruct (af_acc_live RT AF Σ2 m4 P0 N0 ART4 INL0) as (_ & ACL0). destruct (af_acc_live RT AF Σ2 m4 P1 N1 ART4 INL1) as (_ & ACL1).
assert (OBY : aobj asegs m4 Y (16 * 80)) by (split; [ulc|]; split; [ulc|]; exact ACY4).
assert (OBG0 : aobj asegs m4 G0 256) by (split; [ulc|]; split; [ulc|]; exact (acc_sub asegs m4 P0 N0 G0 256 ACL0 PL0 PH0)).
assert (OBG1 : aobj asegs m4 G1 256) by (split; [ulc|]; split; [ulc|]; exact (acc_sub asegs m4 P1 N1 G1 256 ACL1 PL1 PH1)).
assert (OB1 : aobj asegs m4 (usp + -976) (8 * 80 + 128)) by (split; [ulc|]; split; [ulc|]; exact (af_acc_pois RT AF Σ2 m4 _ _ ART4 INX1')).
assert (OB2 : aobj asegs m4 (usp + -1808) (8 * 80 + 128)) by (split; [ulc|]; split; [ulc|]; exact (af_acc_pois RT AF Σ2 m4 _ _ ART4 INX2)).
assert (OBA : aobj asegs m4 A_H0 256) by (apply (aobj_lit RT AF Σ2 m4 A_H0 256 ART4); [unfold ACC_LITS, A_H0; cbn [In]; repeat (first [left; reflexivity | right]) | unfold A_H0; lia | unfold A_H0, APP_TOP; lia]).
chunk_uncons FR3 as FZ. chunk_uncons FR3 as S1c. chunk_uncons FR3 as S2c. chunk_uncons FR3 as S3c. chunk_uncons FR3 as S4c.
chunk_cat S1c S2c. chunk_cat S1c S3c. chunk_cat S1c S4c.
cps_seg (qmf_body (usp + -176) lo (usp + -976) (usp + -1808) (usp + -1840) Y G0 G1 80 _ _ ys g0l g1l xa1 xb1 xa2 xb2).
destruct POST as (ra' & t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & s2' & s3' & s4' & s5' & s6' & s7' & s8' & s9' & s10' & t3' & t4' & t5' & t6'
& F' & fc' & m5 & ys' & g0' & g1' & x1' & x2' & -> & MU5 & WM5 & MI5 & FRM5 & FR5 & XY5 & LY5 & XG05 & LG05 & XG15 & LG15 & XL1 & LXL1 & XL2 & LXL2).
assert (ACY5 : acc asegs m5 Y (4 * 320)).
{ refine (proj2 (proj2 (aobj_munch asegs _ m4 m5 Y (4 * 320) _ MU5 _))); [split; [ulc|]; split; [ulc| exact ACY4]|].
apply shfree_of_offsh; [cbn; unfold SH_LO, SH_HI; repeat split; ulc| ulc| ulc]. }
clear S1c XY XG0 XG1 XA1f XB1f XA2f XB2f OBY OBG0 OBG1 OB1 OB2 OBA ACL0 ACL1.
cps_seg_post.

chunk_cat FZ FR5. chunk_cat FZ FR3.
fold_qmf16 FZ.
cps_seg (qmf_w5_16 usp lo (usp + -1840)).
subst ms.
cps_rt (AUN Σ2 PMc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m5 (usp + -1840) (usp + -144) lo).
{ rewrite PO2, PO1. intros e [<-|[<-|He]].
- left. unfold pz_lo, pz_hi. cbn [fst snd]. rewrite RR2. clear. lia.
- left. unfold pz_lo, pz_hi. cbn [fst snd]. rewrite RR1. clear. lia.
- right. pose proof (POA e He). lia. }
{ cps_callok. }
intros c6 (Σ3 & Hc6 & PO3 & LV3 & FRS3 & SP3 & CR3).
cps_unpack Hc6 as (m6 & v6 & RS6 & (ART6 & MI6 & WM6 & ST6) & PRES6 & ACT6).
assert (ACY6 : acc asegs m6 Y (4 * 320)) by (apply (ACT6 Y (4 * 320) ACY5); [ulc| left; ulc]).

assert (L1n : length x1' = 192%nat) by (clear - LXL1; lia). assert (L2n : length x2' = 192%nat) by (clear - LXL2; lia).
apply rw_cells_f32_CB in XL1. rewrite L1n in XL1. change (4 * 192)%nat with 768%nat in XL1.
apply rw_cells_f32_CB in XL2. rewrite L2n in XL2. change (4 * 192)%nat with 768%nat in XL2.
chunk_cat RZ1 XL1. chunk_cat RZ1 PAD1. apply rw_cells_to_CB in RZ1. cbn [cells_size csize Nat.add] in RZ1.
chunk_cat RZ2 XL2. chunk_cat RZ2 PAD2. apply rw_cells_to_CB in RZ2. cbn [cells_size csize Nat.add] in RZ2.
cps_seg (qmf_w6_16_320 usp lo).
destruct POST as (-> & ST9).
apply Hk. exists Σ3. split.
2:{ split; [congruence|]. split; [congruence|]. split; [congruence|]. split; [congruence|].
rewrite PO3, PO2, PO1. rewrite !pois_drop_cons_below by (unfold pz_lo; cbn [fst]; clear; lia).
apply pois_drop_above. apply (pois_above_le _ usp); [exact POA| clear; lia]. }
eapply ASTA_conseq; [eassumption|]. intros ms <-. exists v6, m6, ys', g0', g1'.
split; [rewrite ESP; unfold ret_stL; do 16 eexists; split; [reflexivity| exact FRM5]|].
split. { split; [exact ART6|]. split; [exact MI6|]. split; [cps_wmono| exact ST9]. }
split; [exact PF|]. split; [exact XY5|]. split; [exact LY5|]. split; [exact XG05|]. split; [exact LG05|]. split; [exact XG15|]. split; [exact LG15| exact ACY6].
Qed.

Theorem qmf_synth16_ok_640 : qmf_synth_cps16 RT 640.
Proof using AF APO AUN.
intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m Y G0 G1 lo fp P0 N0 P1 N1 kp ys g0l g1l
FDO MST -> -> -> -> -> -> -> -> -> XY LY INF FPY YFP ACY Y4 XG0 LG0 INL0 PL0 PH0 G04 XG1 LG1 INL1 PL1 PH1 G14 SG01 POA FRM ART0 MI0 ST0 LOW LOR SPT U32.
intros T c Hc Hk.
set (usp := bv_unsigned sp) in *.
assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned).
unfold entry_st in Hc. rewrite ESP in Hc.
assert (FRN : rt_frames RT Σ <> []) by (intros E; rewrite E in INF; exact INF).
destruct (live_below_lo RT AF Σ m P0 N0 lo ART0 INL0 LOW) as (BL00 & BL01 & LOSH).
destruct (live_below_lo RT AF Σ m P1 N1 lo ART0 INL1 LOW) as (BL10 & BL11 & _).
destruct (frame_below_lo RT AF Σ m fp kp lo ART0 INF LOW) as (BF0 & _ & _).
pose proof (frame_facts RT AF Σ m fp kp ART0 INF) as (FF0 & _ & FF2 & _ & FF4 & _).
pose proof (live_facts RT AF Σ m P0 N0 ART0 INL0) as (_ & _ & _ & LSH0).
pose proof (live_facts RT AF Σ m P1 N1 ART0 INL1) as (_ & _ & _ & LSH1).
destruct (frame_live_apart RT AF Σ m fp kp P0 N0 ART0 INF INL0) as (FL0 & _).
destruct (frame_live_apart RT AF Σ m fp kp P1 N1 ART0 INF INL1) as (FL1 & _).
pose proof (pres_fp_refl (rt_live RT Σ) (rt_frames RT Σ) usp [(Y, Y + 4 * 640); (G0, G0 + 256); (G1, G1 + 256)] m) as PF.
pose proof (fun a => aclient_split RT AF Σ m usp a ART0) as SPL.
pose proof (af_client_consts RT AF Σ m ART0) as CC0.
assert (FSZ : 0 <= fs_size kp) by (unfold fs_size; apply Z.shiftl_nonneg; lia).
cps_norm. cps_hide.

cps_seg (qmf_w1_16_640 Y G0 G1 usp lo).
destruct POST as (j0 & j1 & j2 & j3 & j4 & jh & m1 & -> & MU1 & WM1 & MI1 & ST1 & FR1 & HULL1).
assert (ACY1 : acc asegs m1 Y (4 * 640)).
{ refine (proj2 (proj2 (aobj_munch asegs _ m m1 Y (4 * 640) _ MU1 _))); [split; [ulc|]; split; [ulc| exact ACY]|].
apply shfree_of_offsh; [cbn; unfold SH_LO, SH_HI; repeat split; ulc| ulc| ulc]. }
unfold qmf_frame16 in FR1. cps_seg_post.

assert (EU1 : bv_unsigned (Z_to_bv 64 (usp + -1648)) = usp + -1648) by (apply unsigned_lit; ulc).
assert (RR1 : alloca_rr (usp + -1616) 1408 = usp + -176) by (rewrite qmf_rr; [clear; lia | clear - U32; Z.div_mod_to_equations; lia | reflexivity | lia]).
cps_rt (APO Σ PMc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 (usp + -1616) 1408 lo).
{ rewrite RR1. apply (pois_above_le _ usp); [exact POA| clear; lia]. }
{ cps_callok. }
intros c2 (Σ1 & Hc2 & PO1 & LV1 & FRS1 & SP1 & CR1).
cps_unpack Hc2 as (m2 & v1 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2 & ACX1 & ACT2).
cps_sigma LV1 FRS1 SP1.
assert (INX1 : In (usp + -1616, 1408) (rt_pois RT Σ1)) by (rewrite PO1; left; reflexivity).
assert (ACY2 : acc asegs m2 Y (4 * 640)) by (apply (ACT2 Y (4 * 640) ACY1); [ulc| left; ulc]).

fold_qmf16 FR1.
cps_seg (qmf_w2_16_640 Y G0 G1 usp lo).
destruct POST as (jh2 & m3 & -> & MU3 & WM3 & MI3 & ST3 & FR3 & HULL2).
assert (ACY3 : acc asegs m3 Y (4 * 640)).
{ refine (proj2 (proj2 (aobj_munch asegs _ m2 m3 Y (4 * 640) _ MU3 _))); [split; [ulc|]; split; [ulc| exact ACY2]|].
apply shfree_of_offsh; [cbn; unfold SH_LO, SH_HI; repeat split; ulc| ulc| ulc]. }
clear FR1. unfold qmf_frame16 in FR3. cps_seg_post.

assert (EU2 : bv_unsigned (Z_to_bv 64 (usp + -3120)) = usp + -3120) by (apply unsigned_lit; ulc).
assert (RR2 : alloca_rr (usp + -3088) 1408 = usp + -1648) by (rewrite qmf_rr; [clear; lia | clear - U32; Z.div_mod_to_equations; lia | reflexivity | lia]).
cps_rt (APO Σ1 PMc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m3 (usp + -3088) 1408 lo).
{ rewrite RR2, PO1. apply pois_above_cons; [rewrite RR1; apply (pois_above_le _ usp); [exact POA| clear; lia]| clear; lia| clear; lia]. }
{ rewrite FRS1. exact FRN. }
{ cps_callok. }
intros c4 (Σ2 & Hc4 & PO2 & LV2 & FRS2 & SP2 & CR2).
cps_unpack Hc4 as (m4 & v4 & RS4 & (ART4 & MI4 & WM4 & ST4) & PRES4 & ACX2 & ACT4).
cps_sigma LV2 FRS2 SP2.
assert (INX2 : In (usp + -3088, 1408) (rt_pois RT Σ2)) by (rewrite PO2; left; reflexivity).
assert (INX1' : In (usp + -1616, 1408) (rt_pois RT Σ2)) by (rewrite PO2; right; exact INX1).
assert (ACY4 : acc asegs m4 Y (4 * 640)) by (apply (ACT4 Y (4 * 640) ACY3); [ulc| left; ulc]).

cbn [Z.to_nat Pos.to_nat Pos.iter_op Nat.add] in HULL1, HULL2.
apply (rw_cells_split_CB asegs _ _ [] 1472 _ [] [32; 1280; 128; 32]%nat) in HULL1; [| reflexivity]. cbn [mk_CB_cells app] in HULL1.
chunk_uncons HULL1 as RZ1. chunk_uncons HULL1 as XA1. chunk_uncons HULL1 as XB1. rename HULL1 into PAD1.
apply (rw_cells_split_CB asegs _ _ [] 1472 _ [] [32; 1280; 128; 32]%nat) in HULL2; [| reflexivity]. cbn [mk_CB_cells app] in HULL2.
chunk_uncons HULL2 as RZ2. chunk_uncons HULL2 as XA2. chunk_uncons HULL2 as XB2. rename HULL2 into PAD2.
replace (usp + -1648 + 32) with (usp + -1616) in * by (clear; lia). replace (usp + -1616 + 1280 + 128) with (usp + -208) in * by (clear; lia).
replace (usp + -3120 + 32) with (usp + -3088) in * by (clear; lia). replace (usp + -3088 + 1280 + 128) with (usp + -1680) in * by (clear; lia).
destruct (rw_cells_CB_f32 asegs _ _ 320%nat _ XA1) as (xa1 & LXA1 & XA1f). destruct (rw_cells_CB_f32 asegs _ _ 32%nat _ XB1) as (xb1 & LXB1 & XB1f).
destruct (rw_cells_CB_f32 asegs _ _ 320%nat _ XA2) as (xa2 & LXA2 & XA2f). destruct (rw_cells_CB_f32 asegs _ _ 32%nat _ XB2) as (xb2 & LXB2 & XB2f).
clear XA1 XB1 XA2 XB2.
assert (LXA1z : Z.of_nat (length xa1) = 2 * 160) by (rewrite LXA1; reflexivity). assert (LXA2z : Z.of_nat (length xa2) = 2 * 160) by (rewrite LXA2; reflexivity).

destruct (af_acc_live RT AF Σ2 m4 P0 N0 ART4 INL0) as (_ & ACL0). destruct (af_acc_live RT AF Σ2 m4 P1 N1 ART4 INL1) as (_ & ACL1).
assert (OBY : aobj asegs m4 Y (16 * 160)) by (split; [ulc|]; split; [ulc|]; exact ACY4).
assert (OBG0 : aobj asegs m4 G0 256) by (split; [ulc|]; split; [ulc|]; exact (acc_sub asegs m4 P0 N0 G0 256 ACL0 PL0 PH0)).
assert (OBG1 : aobj asegs m4 G1 256) by (split; [ulc|]; split; [ulc|]; exact (acc_sub asegs m4 P1 N1 G1 256 ACL1 PL1 PH1)).
assert (OB1 : aobj asegs m4 (usp + -1616) (8 * 160 + 128)) by (split; [ulc|]; split; [ulc|]; exact (af_acc_pois RT AF Σ2 m4 _ _ ART4 INX1')).
assert (OB2 : aobj asegs m4 (usp + -3088) (8 * 160 + 128)) by (split; [ulc|]; split; [ulc|]; exact (af_acc_pois RT AF Σ2 m4 _ _ ART4 INX2)).
assert (OBA : aobj asegs m4 A_H0 256) by (apply (aobj_lit RT AF Σ2 m4 A_H0 256 ART4); [unfold ACC_LITS, A_H0; cbn [In]; repeat (first [left; reflexivity | right]) | unfold A_H0; lia | unfold A_H0, APP_TOP; lia]).
chunk_uncons FR3 as FZ. chunk_uncons FR3 as S1c. chunk_uncons FR3 as S2c. chunk_uncons FR3 as S3c. chunk_uncons FR3 as S4c.
chunk_cat S1c S2c. chunk_cat S1c S3c. chunk_cat S1c S4c.
cps_seg (qmf_body (usp + -176) lo (usp + -1616) (usp + -3088) (usp + -3120) Y G0 G1 160 _ _ ys g0l g1l xa1 xb1 xa2 xb2).
destruct POST as (ra' & t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & s2' & s3' & s4' & s5' & s6' & s7' & s8' & s9' & s10' & t3' & t4' & t5' & t6'
& F' & fc' & m5 & ys' & g0' & g1' & x1' & x2' & -> & MU5 & WM5 & MI5 & FRM5 & FR5 & XY5 & LY5 & XG05 & LG05 & XG15 & LG15 & XL1 & LXL1 & XL2 & LXL2).
assert (ACY5 : acc asegs m5 Y (4 * 640)).
{ refine (proj2 (proj2 (aobj_munch asegs _ m4 m5 Y (4 * 640) _ MU5 _))); [split; [ulc|]; split; [ulc| exact ACY4]|].
apply shfree_of_offsh; [cbn; unfold SH_LO, SH_HI; repeat split; ulc| ulc| ulc]. }
clear S1c XY XG0 XG1 XA1f XB1f XA2f XB2f OBY OBG0 OBG1 OB1 OB2 OBA ACL0 ACL1.
cps_seg_post.

chunk_cat FZ FR5. chunk_cat FZ FR3.
fold_qmf16 FZ.
cps_seg (qmf_w5_16 usp lo (usp + -3120)).
subst ms.
cps_rt (AUN Σ2 PMc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m5 (usp + -3120) (usp + -144) lo).
{ rewrite PO2, PO1. intros e [<-|[<-|He]].
- left. unfold pz_lo, pz_hi. cbn [fst snd]. rewrite RR2. clear. lia.
- left. unfold pz_lo, pz_hi. cbn [fst snd]. rewrite RR1. clear. lia.
- right. pose proof (POA e He). lia. }
{ cps_callok. }
intros c6 (Σ3 & Hc6 & PO3 & LV3 & FRS3 & SP3 & CR3).
cps_unpack Hc6 as (m6 & v6 & RS6 & (ART6 & MI6 & WM6 & ST6) & PRES6 & ACT6).
assert (ACY6 : acc asegs m6 Y (4 * 640)) by (apply (ACT6 Y (4 * 640) ACY5); [ulc| left; ulc]).

assert (L1n : length x1' = 352%nat) by (clear - LXL1; lia). assert (L2n : length x2' = 352%nat) by (clear - LXL2; lia).
apply rw_cells_f32_CB in XL1. rewrite L1n in XL1. change (4 * 352)%nat with 1408%nat in XL1.
apply rw_cells_f32_CB in XL2. rewrite L2n in XL2. change (4 * 352)%nat with 1408%nat in XL2.
chunk_cat RZ1 XL1. chunk_cat RZ1 PAD1. apply rw_cells_to_CB in RZ1. cbn [cells_size csize Nat.add] in RZ1.
chunk_cat RZ2 XL2. chunk_cat RZ2 PAD2. apply rw_cells_to_CB in RZ2. cbn [cells_size csize Nat.add] in RZ2.
cps_seg (qmf_w6_16_640 usp lo).
destruct POST as (-> & ST9).
apply Hk. exists Σ3. split.
2:{ split; [congruence|]. split; [congruence|]. split; [congruence|]. split; [congruence|].
rewrite PO3, PO2, PO1. rewrite !pois_drop_cons_below by (unfold pz_lo; cbn [fst]; clear; lia).
apply pois_drop_above. apply (pois_above_le _ usp); [exact POA| clear; lia]. }
eapply ASTA_conseq; [eassumption|]. intros ms <-. exists v6, m6, ys', g0', g1'.
split; [rewrite ESP; unfold ret_stL; do 16 eexists; split; [reflexivity| exact FRM5]|].
split. { split; [exact ART6|]. split; [exact MI6|]. split; [cps_wmono| exact ST9]. }
split; [exact PF|]. split; [exact XY5|]. split; [exact LY5|]. split; [exact XG05|]. split; [exact LG05|]. split; [exact XG15|]. split; [exact LG15| exact ACY6].
Qed.

Theorem qmf_synth16_ok : forall N, N = 320 \/ N = 640 -> qmf_synth_cps16 RT N.
Proof using AF APO AUN. intros N [-> | ->]; [exact qmf_synth16_ok_320 | exact qmf_synth16_ok_640]. Qed.
End QMF.
