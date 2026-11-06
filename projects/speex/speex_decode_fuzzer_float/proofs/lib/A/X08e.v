(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS Require Import X0mx X0k2.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1da X1dg X1cg X1df X1ck.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0bp X0j9 X0ec X001 X00b X04b X07z X05o X05p X05s X05t X05l X089
X07y X07t X07s X08f X08g X08i X08j.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X12c X14x X0r0 X0ra X0v9 X0yr X0wl X0wm X12a X0yq X0yl X0yk X0z7 X0z8 X0z9 X0za.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14x OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0r0 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ra OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0v9 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0yr OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0wl OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0wm OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12a OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0yq OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0yl OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0yk OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0z7 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0z8 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0z9 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0za.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma mc_rr : forall a n, a mod 32 = 0 -> n mod 32 = 0 -> 0 <= n -> alloca_rr a n = a + n + 32.
Proof. intros a n H1 H2 H3. unfold alloca_rr. Z.div_mod_to_equations. lia. Qed.

Ltac fold_mc_frame H :=
lazymatch type of H with
| rw_cells ?sg ?mm ?A [C8 (Z_to_bv 64 0); ?k8; ?k16; ?k24; ?k32; ?k40; C8 ?f8; C8 ?f7; C8 ?f6; C8 ?f5; C8 ?f4; C8 ?f3; C8 ?f2; C8 ?f1; C8 ?f0;
C8 ?c11; C8 ?c10; C8 ?c9; C8 ?c8; C8 ?c7; C8 ?c6; C8 ?c5; C8 ?c4; C8 ?c3; C8 ?c2; C8 ?c1; C8 ?c0; C8 ?cra] =>
change (rw_cells sg mm A (mc_frame k8 k16 k24 k32 k40 f8 f7 f6 f5 f4 f3 f2 f1 f0 c11 c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra)) in H
end.

Section MCCPS.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis APO : alloca_poison_contract RT.
Hypothesis AUN : allocas_unpoison_contract RT.
Hypothesis SM2 : stack_malloc_contract RT 2.

Theorem multicomb_ok : multicomb_cps RT.
Proof using AF APO AUN SM2.
intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m EB eoff ne pitch lo fp P0 N0 kp eb ns
FDO MST -> -> -> -> -> -> XEB LEB INL PL PH E4 EOFF HP XNE LNS INF FPN NFP ACN N4 FRMX CR0 POA ART0 MI0 FRM ST0 LOW LOR SPT U32.
intros T c Hc Hk.
set (usp := bv_unsigned sp) in *.
assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned).
unfold entry_st in Hc. rewrite ESP in Hc. unfold MULTICOMB_STACK in LOR.
assert (FRN : rt_frames RT Σ <> []) by (intros E; rewrite E in INF; exact INF).
destruct (live_below_lo RT AF Σ m P0 N0 lo ART0 INL LOW) as (BL0 & BL1 & LOSH).
destruct (frame_below_lo RT AF Σ m fp kp lo ART0 INF LOW) as (BF0 & _ & _).
pose proof (frame_facts RT AF Σ m fp kp ART0 INF) as (FF0 & FF1 & FF2 & _ & FF4 & _).
destruct (frame_live_apart RT AF Σ m fp kp P0 N0 ART0 INF INL) as (FL0 & _).
pose proof (pres_fp_refl (rt_live RT Σ) (rt_frames RT Σ) usp [(ne, ne + 320)] m) as PF.
pose proof (fun a => aclient_split RT AF Σ m usp a ART0) as SPL.
pose proof (af_client_consts RT AF Σ m ART0) as CC0.
assert (FSZ : 0 <= fs_size kp) by (unfold fs_size; apply Z.shiftl_nonneg; lia).
assert (EOR : 0 <= eoff /\ eoff + 80 <= 500) by (clear - EOFF; lia).
cps_norm.
assert (FP8 : fp mod 8 = 0) by (clear - FF1; Z.div_mod_to_equations; lia).
pose proof (fs_size_mod8 kp) as FS8.
assert (NSHD : forall i, 0 <= i < 320 -> SH_LO <= shad (ne + i) < SH_HI).
{ intros i Hi. unfold shad, SHB, SH_LO, SH_HI. assert (0 <= (ne + i) / 8 < 17592186044416) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; [lia|]; clear - Hi NFP BF0 LOR SPT; lia]). lia. }
cps_hide.

cps_seg (mc_w1 (EB + 4 * eoff) ne pitch usp lo).
destruct POST as (j8 & j16 & j40 & jh & m1 & -> & MU1 & WM1 & MI1 & ST1 & FR1 & HULL1).
assert (ACN1 : acc bsegs m1 ne 320).
{ refine (proj2 (proj2 (aobj_munch bsegs _ m m1 ne 320 _ MU1 _))); [split; [ulc|]; split; [ulc| exact ACN]|].
apply shfree_of_offsh; [cbn; unfold SH_LO, SH_HI; repeat split; ulc| ulc| ulc]. }
unfold mc_frame in FR1. cps_seg_post.

assert (EU1 : bv_unsigned (Z_to_bv 64 (usp + -928)) = usp + -928) by (apply unsigned_lit; ulc).
assert (RR1 : alloca_rr (usp + -896) 640 = usp + -224) by (rewrite mc_rr; [clear; lia | clear - U32; Z.div_mod_to_equations; lia | reflexivity | lia]).
cps_rt (APO Σ PMc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 (usp + -896) 640 lo).
{ rewrite RR1. apply (pois_above_le _ usp); [exact POA| clear; lia]. }
{ cps_callok. }
intros c2 (Σ1 & Hc2 & PO1 & LV1 & FRS1 & SP1 & CR1).
cps_unpack Hc2 as (m2 & v1 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2 & ACX1 & ACT2).
cps_sigma LV1 FRS1 SP1.
assert (INX1 : In (usp + -896, 640) (rt_pois RT Σ1)) by (rewrite PO1; left; reflexivity).
assert (ACN2 : acc bsegs m2 ne 320) by (apply (ACT2 ne 320 ACN1); [ulc| left; ulc]).

fold_mc_frame FR1.
cps_seg (mc_w2 (EB + 4 * eoff) ne pitch usp lo).
destruct POST as (m3 & -> & MU3 & WM3 & MI3 & FR3).
assert (ACN3 : acc bsegs m3 ne 320).
{ refine (proj2 (proj2 (aobj_munch bsegs _ m2 m3 ne 320 _ MU3 _))); [split; [ulc|]; split; [ulc| exact ACN2]|].
apply shfree_of_offsh; [cbn; unfold SH_LO, SH_HI; repeat split; ulc| ulc| ulc]. }
clear FR1. unfold mc_frame in FR3. cps_seg_post.

apply (rw_cells_split_CB bsegs _ _ [] 704 _ [] [32; 320; 320; 32]%nat) in HULL1; [| reflexivity]. cbn [mk_CB_cells app] in HULL1.
chunk_uncons HULL1 as RZ1. chunk_uncons HULL1 as XI1. chunk_uncons HULL1 as XI2. rename HULL1 into PAD1.
replace (usp + -928 + 32) with (usp + -896) in * by (clear; lia). replace (usp + -896 + 320) with (usp + -576) in * by (clear; lia).
replace (usp + -576 + 320) with (usp + -256) in * by (clear; lia).
destruct (rw_cells_CB_f32 bsegs _ _ 80%nat _ XI1) as (i1l & LI1 & XI1f). destruct (rw_cells_CB_f32 bsegs _ _ 80%nat _ XI2) as (i2l & LI2 & XI2f).
clear XI1 XI2.

cps_rt (interp_pitch_ok RT AF SM2 Σ1 PMc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m3 EB eoff pitch (usp + -896) P0 N0 (usp + -896) 640 lo eb i1l).
{ rewrite FRS1. exact FRMX. }
{ rewrite EU1. eassumption. }
intros c4 (Σ2 & Hc4 & LV2 & FRS2 & SP2 & CR2 & PO2).
cps_unpack_lib Hc4 as (v4 & m4 & ip1' & RS4 & (ART4 & MI4 & WM4 & ST4) & PRES4 & XI1' & LI1').
replace (usp + -896 + 320) with (usp + -576) in PRES4 by (clear; lia).
clear XI1f.
cps_tr_lib PRES4.
cps_pf_lib PRES4 SPL.
assert (ACN4 : acc bsegs m4 ne 320).
{ apply (acc_pres_fp_frame _ _ _ _ m3 m4 fp kp ne 320 PRES4); [exact INF | exact FP8 | exact FS8 | ulc | exact FPN | ulc | | exact ACN3].
intros i Hi. cbn [outside]. split; [| exact I]. pose proof (NSHD i Hi) as [_ HS]. intros [Ha Hb]. clear - HS Ha LOSH LOR. unfold SH_HI in *. lia. }
cps_sigma LV2 FRS2 SP2.
assert (INX2 : In (usp + -896, 640) (rt_pois RT Σ2)) by (rewrite PO2; exact INX1).

cps_seg (mc_w3 (EB + 4 * eoff) ne pitch usp).
subst ms.
assert (P2R : 0 <= eoff - mc_p2 pitch - 6 /\ eoff - mc_p2 pitch <= 414).
{ unfold mc_p2. pose proof (EOFF : eoff = 294 \/ eoff = 374) as EOFF2. clear - EOFF2 HP. destruct (40 <? pitch) eqn:B; [apply Z.ltb_lt in B | apply Z.ltb_ge in B]; lia. }
destruct P2R as (P2a & P2b).

cps_rt (interp_pitch_ok RT AF SM2 Σ2 PMc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m4 EB eoff (mc_p2 pitch) (usp + -576) P0 N0 (usp + -896) 640 lo eb i2l).
{ rewrite FRS2, FRS1. exact FRMX. }
{ rewrite CR2, CR1. clear - CR0. lia. }
{ rewrite EU1. eassumption. }
intros c6 (Σ3 & Hc6 & LV3 & FRS3 & SP3 & CR3 & PO3).
cps_unpack_lib Hc6 as (v6 & m6 & ip2' & RS6 & (ART6 & MI6 & WM6 & ST6) & PRES6 & XI2' & LI2').
replace (usp + -576 + 320) with (usp + -256) in PRES6 by (clear; lia).
clear XI2f.
cps_tr_lib PRES6.
cps_pf_lib PRES6 SPL.
assert (ACN6 : acc bsegs m6 ne 320).
{ apply (acc_pres_fp_frame _ _ _ _ m4 m6 fp kp ne 320 PRES6); [exact INF | exact FP8 | exact FS8 | ulc | exact FPN | ulc | | exact ACN4].
intros i Hi. cbn [outside]. split; [| exact I]. pose proof (NSHD i Hi) as [_ HS]. intros [Ha Hb]. clear - HS Ha LOSH LOR. unfold SH_HI in *. lia. }
cps_sigma LV3 FRS3 SP3.
assert (INX3 : In (usp + -896, 640) (rt_pois RT Σ3)) by (rewrite PO3; exact INX2).

destruct (eb_window m6 EB eb eoff XEB LEB ltac:(clear - EOR; lia) ltac:(clear - EOR; lia)) as [XW LXW].
set (xw := firstn 80 (skipn (Z.to_nat eoff) eb)) in *.
assert (LI1z : Z.of_nat (length ip1') = 4 * 20) by (rewrite LI1'; reflexivity). assert (LI2z : Z.of_nat (length ip2') = 4 * 20) by (rewrite LI2'; reflexivity).
assert (HI2 : usp + -576 = usp + -896 + 320) by (clear; lia).
assert (XBR : EB <= EB + 4 * eoff /\ EB + 4 * eoff + 320 <= EB + 2000) by (clear - EOR; lia).
assert (X4 : (EB + 4 * eoff) mod 4 = 0) by (clear - E4; Z.div_mod_to_equations; lia).
assert (I4 : (usp + -896) mod 4 = 0) by (clear - U32; Z.div_mod_to_equations; lia).
assert (EO0 : 0 < EB) by ulc.
assert (NE0 : 0 < ne /\ ne + 320 < 2 ^ 62) by (split; ulc).
destruct (af_acc_live RT AF Σ3 m6 P0 N0 ART6 INL) as (_ & ACL).
assert (OBE : aobj bsegs m6 EB 2000) by (split; [ulc|]; split; [ulc|]; exact (acc_sub bsegs m6 P0 N0 EB 2000 ACL PL PH)).
assert (OBI : aobj bsegs m6 (usp + -896) 640) by (split; [ulc|]; split; [ulc|]; exact (af_acc_pois RT AF Σ3 m6 _ _ ART6 INX3)).
pose proof (af_client_consts RT AF Σ3 m6 ART6) as CC6.
fold_mc_frame FR3.
cps_seg (mc_mid EB (EB + 4 * eoff) (usp + -896) (usp + -576) ne pitch usp lo xw ip1' ip2' _ _ LXW LI1z LI2z HP eq_refl HI2 XBR X4 N4 EO0 NE0).
destruct POST as (ra7 & t27 & a07 & a17 & a27 & t37 & t47 & t57 & t67 & F7 & fc7 & m7 & -> & MU7 & WM7 & MI7 & FRM7 & ST7 & FR7).
assert (ACN7 : acc bsegs m7 ne 320).
{ refine (proj2 (proj2 (aobj_munch bsegs _ m6 m7 ne 320 _ MU7 _))); [split; [ulc|]; split; [ulc| exact ACN6]|].
apply shfree_of_offsh; [cbn; unfold SH_LO, SH_HI; repeat split; ulc| ulc| ulc]. }
clear FR3. cps_seg_post.

assert (SEPE : ne + 320 <= EB \/ EB + 2000 <= ne) by ulc.
assert (SEPI : ne + 320 <= usp + -896 \/ usp + -896 + 640 <= ne) by (left; ulc).
assert (NI : IMG_TOP_B <= ne) by (unfold IMG_TOP_B; ulc).
assert (NSH : ne + 320 <= SH_LO \/ SH_HI <= ne) by ulc.
assert (NLO : ne + 320 <= lo) by ulc.
assert (XLO : EB + 4 * eoff + 320 <= lo) by ulc.
destruct (af_acc_live RT AF Σ3 m7 P0 N0 ART INL) as (_ & ACL7).
assert (OBE7 : aobj bsegs m7 EB 2000) by (split; [ulc|]; split; [ulc|]; exact (acc_sub bsegs m7 P0 N0 EB 2000 ACL7 PL PH)).
assert (OBI7 : aobj bsegs m7 (usp + -896) 640) by (split; [ulc|]; split; [ulc|]; exact (af_acc_pois RT AF Σ3 m7 _ _ ART INX3)).
assert (OBN7 : aobj bsegs m7 ne 320) by (split; [ulc|]; split; [ulc|]; exact ACN7).
assert (LXWn : length xw = 80%nat) by (clear - LXW; lia).
pose proof (af_client_consts RT AF Σ3 m7 ART) as CC7.
cps_seg (mc_tail EB (EB + 4 * eoff) (usp + -896) (usp + -576) ne pitch usp lo _ _ eq_refl HI2 XBR E4 X4 I4 N4 SEPE SEPI NI NSH EO0 NE0 NLO XLO xw ip1' ip2' ns).
destruct POST as (ra8 & t08 & t18 & t28 & a08 & a18 & a28 & a38 & a48 & a58 & a68 & a78 & s28 & s38 & s48 & s58 & s68 & s78 & s88 & s98 & s118 & t38 & t48 & t58 & t68
& F8 & fc8 & m8 & ns' & -> & MU8 & WM8 & MI8 & FRM8 & ST8 & LNS' & XNE8).
assert (ACN8 : acc bsegs m8 ne 320).
{ refine (proj2 (proj2 (aobj_munch bsegs _ m7 m8 ne 320 _ MU8 _))); [split; [ulc|]; split; [ulc| exact ACN7]|].
apply shfree_of_offsh; [cbn; unfold SH_LO, SH_HI; repeat split; ulc| ulc| ulc]. }
clear XNE OBE7 OBI7 OBN7 ACL7 CC7. cps_seg_post.

try fold_mc_frame FR7.
cps_seg (mc_w5 usp lo _ _ (usp + -928)).
subst ms.
cps_rt (AUN Σ3 PMc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m8 (usp + -928) (usp + -192) lo).
{ rewrite PO3, PO2, PO1. intros e [<-|He].
- left. unfold pz_lo, pz_hi. cbn [fst snd]. rewrite RR1. clear. lia.
- right. pose proof (POA e He). lia. }
{ cps_callok. }
intros c10 (Σ4 & Hc10 & PO4 & LV4 & FRS4 & SP4 & CR4).
cps_unpack Hc10 as (m10 & v10 & RS10 & (ART10 & MI10 & WM10 & ST10) & PRES10 & ACT10).
assert (ACN10 : acc bsegs m10 ne 320) by (apply (ACT10 ne 320 ACN8); [ulc| left; ulc]).

assert (L1n : length ip1' = 80%nat) by exact LI1'. assert (L2n : length ip2' = 80%nat) by exact LI2'.
apply rw_cells_f32_CB in XI1'. rewrite L1n in XI1'. change (4 * 80)%nat with 320%nat in XI1'.
apply rw_cells_f32_CB in XI2'. rewrite L2n in XI2'. change (4 * 80)%nat with 320%nat in XI2'.
chunk_cat RZ1 XI1'. chunk_cat RZ1 XI2'. chunk_cat RZ1 PAD1. apply rw_cells_to_CB in RZ1. cbn [cells_size csize Nat.add] in RZ1.
cps_seg (mc_w6 usp lo _ _).
destruct POST as (F10 & -> & ST11).
apply Hk. exists Σ4. split.
2:{ split; [congruence|]. split; [congruence|]. split; [congruence|]. split; [rewrite CR4, CR3, CR2, CR1; clear; lia|].
rewrite PO4, PO3, PO2, PO1. rewrite !pois_drop_cons_below by (unfold pz_lo; cbn [fst]; clear; lia).
apply pois_drop_above. apply (pois_above_le _ usp); [exact POA| clear; lia]. }
eapply ASTA_conseq; [eassumption|]. intros ms <-. exists v10, m10, ns'.
split; [rewrite ESP; unfold ret_stL; do 16 eexists; split; [reflexivity| exact FRM8]|].
split. { split; [exact ART10|]. split; [exact MI10|]. split; [cps_wmono| exact ST11]. }
split; [exact PF|]. split; [exact XNE8|]. split; [exact LNS'| exact ACN10].
Qed.
End MCCPS.
End B_TWIN.

Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma mc_rr : forall a n, a mod 32 = 0 -> n mod 32 = 0 -> 0 <= n -> alloca_rr a n = a + n + 32.
Proof. intros a n H1 H2 H3. unfold alloca_rr. Z.div_mod_to_equations. lia. Qed.

Ltac fold_mc_frame H :=
lazymatch type of H with
| rw_cells ?sg ?mm ?A [C8 ?top; CB 8 ?a1; CB 8 ?a2; CB 8 ?a3; C8 ?f8; C8 ?f7; C8 ?f6; C8 ?f5; C8 ?f4; C8 ?f3; C8 ?f2; C8 ?f1; C8 ?f0;
C8 ?c9; C8 ?c8; C8 ?c7; C8 ?c6; C8 ?c5; C8 ?c4; C8 ?c3; C8 ?c2; C8 ?c1; C8 ?c0; C8 ?cra] =>
change (rw_cells sg mm A (mc_frame top a1 a2 a3 f8 f7 f6 f5 f4 f3 f2 f1 f0 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra)) in H
end.

Section MCCPS.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis APO : alloca_poison_contract RT.
Hypothesis AUN : allocas_unpoison_contract RT.
Hypothesis SM2 : stack_malloc_contract RT 2.

Theorem multicomb_ok : multicomb_cps RT.
Proof using AF APO AUN SM2.
intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m EB eoff ne pitch lo fp P0 N0 kp eb ns
FDO MST -> -> -> -> -> -> XEB LEB INL PL PH E4 EOFF HP XNE LNS INF FPN NFP ACN N4 FRMX CR0 POA ART0 MI0 FRM ST0 LOW LOR SPT U32.
intros T c Hc Hk.
set (usp := bv_unsigned sp) in *.
assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned).
unfold entry_st in Hc. rewrite ESP in Hc. unfold MULTICOMB_STACK in LOR.
assert (FRN : rt_frames RT Σ <> []) by (intros E; rewrite E in INF; exact INF).
destruct (live_below_lo RT AF Σ m P0 N0 lo ART0 INL LOW) as (BL0 & BL1 & LOSH).
destruct (frame_below_lo RT AF Σ m fp kp lo ART0 INF LOW) as (BF0 & _ & _).
pose proof (frame_facts RT AF Σ m fp kp ART0 INF) as (FF0 & FF1 & FF2 & _ & FF4 & _).
destruct (frame_live_apart RT AF Σ m fp kp P0 N0 ART0 INF INL) as (FL0 & _).
pose proof (pres_fp_refl (rt_live RT Σ) (rt_frames RT Σ) usp [(ne, ne + 320)] m) as PF.
pose proof (fun a => aclient_split RT AF Σ m usp a ART0) as SPL.
pose proof (af_client_consts RT AF Σ m ART0) as CC0.
assert (FSZ : 0 <= fs_size kp) by (unfold fs_size; apply Z.shiftl_nonneg; lia).
assert (EOR : 0 <= eoff /\ eoff + 80 <= 500) by (clear - EOFF; lia).
cps_norm.
assert (FP8 : fp mod 8 = 0) by (clear - FF1; Z.div_mod_to_equations; lia).
pose proof (fs_size_mod8 kp) as FS8.
assert (NSHD : forall i, 0 <= i < 320 -> SH_LO <= shad (ne + i) < SH_HI).
{ intros i Hi. unfold shad, SHB, SH_LO, SH_HI. assert (0 <= (ne + i) / 8 < 17592186044416) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; [lia|]; clear - Hi NFP BF0 LOR SPT; lia]). lia. }
cps_hide.

cps_seg (mc_w1 (EB + 4 * eoff) ne pitch usp lo).
destruct POST as (j1 & j2 & j3 & jh & m1 & -> & MU1 & WM1 & MI1 & ST1 & FR1 & HULL1).
assert (ACN1 : acc asegs m1 ne 320).
{ refine (proj2 (proj2 (aobj_munch asegs _ m m1 ne 320 _ MU1 _))); [split; [ulc|]; split; [ulc| exact ACN]|].
apply shfree_of_offsh; [cbn; unfold SH_LO, SH_HI; repeat split; ulc| ulc| ulc]. }
unfold mc_frame in FR1. cps_seg_post.

assert (EU1 : bv_unsigned (Z_to_bv 64 (usp + -896)) = usp + -896) by (apply unsigned_lit; ulc).
assert (RR1 : alloca_rr (usp + -864) 640 = usp + -192) by (rewrite mc_rr; [clear; lia | clear - U32; Z.div_mod_to_equations; lia | reflexivity | lia]).
cps_rt (APO Σ PMc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 (usp + -864) 640 lo).
{ rewrite RR1. apply (pois_above_le _ usp); [exact POA| clear; lia]. }
{ cps_callok. }
intros c2 (Σ1 & Hc2 & PO1 & LV1 & FRS1 & SP1 & CR1).
cps_unpack Hc2 as (m2 & v1 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2 & ACX1 & ACT2).
cps_sigma LV1 FRS1 SP1.
assert (INX1 : In (usp + -864, 640) (rt_pois RT Σ1)) by (rewrite PO1; left; reflexivity).
assert (ACN2 : acc asegs m2 ne 320) by (apply (ACT2 ne 320 ACN1); [ulc| left; ulc]).

fold_mc_frame FR1.
cps_seg (mc_w2 (EB + 4 * eoff) ne pitch usp lo).
destruct POST as (m3 & -> & MU3 & WM3 & MI3 & FR3).
assert (ACN3 : acc asegs m3 ne 320).
{ refine (proj2 (proj2 (aobj_munch asegs _ m2 m3 ne 320 _ MU3 _))); [split; [ulc|]; split; [ulc| exact ACN2]|].
apply shfree_of_offsh; [cbn; unfold SH_LO, SH_HI; repeat split; ulc| ulc| ulc]. }
clear FR1. unfold mc_frame in FR3. cps_seg_post.

apply (rw_cells_split_CB asegs _ _ [] 704 _ [] [32; 320; 320; 32]%nat) in HULL1; [| reflexivity]. cbn [mk_CB_cells app] in HULL1.
chunk_uncons HULL1 as RZ1. chunk_uncons HULL1 as XI1. chunk_uncons HULL1 as XI2. rename HULL1 into PAD1.
replace (usp + -896 + 32) with (usp + -864) in * by (clear; lia). replace (usp + -864 + 320) with (usp + -544) in * by (clear; lia).
replace (usp + -544 + 320) with (usp + -224) in * by (clear; lia).
destruct (rw_cells_CB_f32 asegs _ _ 80%nat _ XI1) as (i1l & LI1 & XI1f). destruct (rw_cells_CB_f32 asegs _ _ 80%nat _ XI2) as (i2l & LI2 & XI2f).
clear XI1 XI2.

cps_rt (interp_pitch_ok RT AF SM2 Σ1 PMc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m3 EB eoff pitch (usp + -864) P0 N0 (usp + -864) 640 lo eb i1l).
{ rewrite FRS1. exact FRMX. }
{ rewrite EU1. eassumption. }
intros c4 (Σ2 & Hc4 & LV2 & FRS2 & SP2 & CR2 & PO2).
cps_unpack_lib Hc4 as (v4 & m4 & ip1' & RS4 & (ART4 & MI4 & WM4 & ST4) & PRES4 & XI1' & LI1').
replace (usp + -864 + 320) with (usp + -544) in PRES4 by (clear; lia).
clear XI1f.
cps_tr_lib PRES4.
cps_pf_lib PRES4 SPL.
assert (ACN4 : acc asegs m4 ne 320).
{ apply (acc_pres_fp_frame _ _ _ _ m3 m4 fp kp ne 320 PRES4); [exact INF | exact FP8 | exact FS8 | ulc | exact FPN | ulc | | exact ACN3].
intros i Hi. cbn [outside]. split; [| exact I]. pose proof (NSHD i Hi) as [_ HS]. intros [Ha Hb]. clear - HS Ha LOSH LOR. unfold SH_HI in *. lia. }
cps_sigma LV2 FRS2 SP2.
assert (INX2 : In (usp + -864, 640) (rt_pois RT Σ2)) by (rewrite PO2; exact INX1).

cps_seg (mc_w3 (EB + 4 * eoff) ne pitch usp).
subst ms.
assert (P2R : 0 <= eoff - mc_p2 pitch - 6 /\ eoff - mc_p2 pitch <= 414).
{ unfold mc_p2. pose proof (EOFF : eoff = 294 \/ eoff = 374) as EOFF2. clear - EOFF2 HP. destruct (40 <? pitch) eqn:B; [apply Z.ltb_lt in B | apply Z.ltb_ge in B]; lia. }
destruct P2R as (P2a & P2b).

cps_rt (interp_pitch_ok RT AF SM2 Σ2 PMc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m4 EB eoff (mc_p2 pitch) (usp + -544) P0 N0 (usp + -864) 640 lo eb i2l).
{ rewrite FRS2, FRS1. exact FRMX. }
{ rewrite CR2, CR1. clear - CR0. lia. }
{ rewrite EU1. eassumption. }
intros c6 (Σ3 & Hc6 & LV3 & FRS3 & SP3 & CR3 & PO3).
cps_unpack_lib Hc6 as (v6 & m6 & ip2' & RS6 & (ART6 & MI6 & WM6 & ST6) & PRES6 & XI2' & LI2').
replace (usp + -544 + 320) with (usp + -224) in PRES6 by (clear; lia).
clear XI2f.
cps_tr_lib PRES6.
cps_pf_lib PRES6 SPL.
assert (ACN6 : acc asegs m6 ne 320).
{ apply (acc_pres_fp_frame _ _ _ _ m4 m6 fp kp ne 320 PRES6); [exact INF | exact FP8 | exact FS8 | ulc | exact FPN | ulc | | exact ACN4].
intros i Hi. cbn [outside]. split; [| exact I]. pose proof (NSHD i Hi) as [_ HS]. intros [Ha Hb]. clear - HS Ha LOSH LOR. unfold SH_HI in *. lia. }
cps_sigma LV3 FRS3 SP3.
assert (INX3 : In (usp + -864, 640) (rt_pois RT Σ3)) by (rewrite PO3; exact INX2).

destruct (eb_window m6 EB eb eoff XEB LEB ltac:(clear - EOR; lia) ltac:(clear - EOR; lia)) as [XW LXW].
set (xw := firstn 80 (skipn (Z.to_nat eoff) eb)) in *.
assert (LI1z : Z.of_nat (length ip1') = 4 * 20) by (rewrite LI1'; reflexivity). assert (LI2z : Z.of_nat (length ip2') = 4 * 20) by (rewrite LI2'; reflexivity).
assert (HI2 : usp + -544 = usp + -864 + 320) by (clear; lia).
assert (XBR : EB <= EB + 4 * eoff /\ EB + 4 * eoff + 320 <= EB + 2000) by (clear - EOR; lia).
assert (X4 : (EB + 4 * eoff) mod 4 = 0) by (clear - E4; Z.div_mod_to_equations; lia).
assert (I4 : (usp + -864) mod 4 = 0) by (clear - U32; Z.div_mod_to_equations; lia).
destruct (af_acc_live RT AF Σ3 m6 P0 N0 ART6 INL) as (_ & ACL).
assert (OBE : aobj asegs m6 EB 2000) by (split; [ulc|]; split; [ulc|]; exact (acc_sub asegs m6 P0 N0 EB 2000 ACL PL PH)).
assert (OBI : aobj asegs m6 (usp + -864) 640) by (split; [ulc|]; split; [ulc|]; exact (af_acc_pois RT AF Σ3 m6 _ _ ART6 INX3)).
pose proof (af_client_consts RT AF Σ3 m6 ART6) as CC6.
cps_seg (mc_mid EB (EB + 4 * eoff) (usp + -864) (usp + -544) ne pitch usp lo xw ip1' ip2' _ _ _ _ LXW LI1z LI2z HP HI2 XBR X4 I4).
destruct POST as (ra7 & t07 & t17 & t27 & a77 & t37 & t47 & t57 & t67 & F7 & fc7 & m7 & -> & MU7 & WM7 & MI7 & FRM7 & ST7).
assert (ACN7 : acc asegs m7 ne 320).
{ refine (proj2 (proj2 (aobj_munch asegs _ m6 m7 ne 320 _ MU7 _))); [split; [ulc|]; split; [ulc| exact ACN6]|].
apply shfree_of_offsh; [cbn; unfold SH_LO, SH_HI; repeat split; ulc| ulc| ulc]. }
cps_seg_post.

assert (SEPE : ne + 320 <= EB \/ EB + 2000 <= ne) by ulc.
assert (SEPI : ne + 320 <= usp + -864 \/ usp + -864 + 640 <= ne) by (left; ulc).
assert (NI : IMG_TOP <= ne) by ulc.
assert (NSH : ne + 320 <= SH_LO \/ SH_HI <= ne) by ulc.
destruct (af_acc_live RT AF Σ3 m7 P0 N0 ART INL) as (_ & ACL7).
assert (OBE7 : aobj asegs m7 EB 2000) by (split; [ulc|]; split; [ulc|]; exact (acc_sub asegs m7 P0 N0 EB 2000 ACL7 PL PH)).
assert (OBI7 : aobj asegs m7 (usp + -864) 640) by (split; [ulc|]; split; [ulc|]; exact (af_acc_pois RT AF Σ3 m7 _ _ ART INX3)).
assert (OBN7 : aobj asegs m7 ne 320) by (split; [ulc|]; split; [ulc|]; exact ACN7).
assert (LXWn : length xw = 80%nat) by (clear - LXW; lia).
cps_seg (mc_tail EB (EB + 4 * eoff) (usp + -864) (usp + -544) ne pitch usp _ _ _ _ HI2 XBR E4 X4 I4 N4 SEPE SEPI NI NSH xw ip1' ip2' ns).
destruct POST as (ra8 & t08 & t18 & t28 & a08 & a18 & a28 & a38 & a48 & a58 & a68 & a78 & s28 & s38 & s48 & s58 & s68 & t38 & t48 & t58 & t68 & F8 & fc8 & m8 & ns' & -> & MU8 & WM8 & MI8 & FRM8 & LNS' & XNE8).
assert (ACN8 : acc asegs m8 ne 320).
{ refine (proj2 (proj2 (aobj_munch asegs _ m7 m8 ne 320 _ MU8 _))); [split; [ulc|]; split; [ulc| exact ACN7]|].
apply shfree_of_offsh; [cbn; unfold SH_LO, SH_HI; repeat split; ulc| ulc| ulc]. }
clear XNE OBE7 OBI7 OBN7 ACL7. cps_seg_post.

fold_mc_frame FR3.
cps_seg (mc_w5 usp lo _ _ (usp + -896)).
subst ms.
cps_rt (AUN Σ3 PMc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m8 (usp + -896) (usp + -192) lo).
{ rewrite PO3, PO2, PO1. intros e [<-|He].
- left. unfold pz_lo, pz_hi. cbn [fst snd]. rewrite RR1. clear. lia.
- right. pose proof (POA e He). lia. }
{ cps_callok. }
intros c10 (Σ4 & Hc10 & PO4 & LV4 & FRS4 & SP4 & CR4).
cps_unpack Hc10 as (m10 & v10 & RS10 & (ART10 & MI10 & WM10 & ST10) & PRES10 & ACT10).
assert (ACN10 : acc asegs m10 ne 320) by (apply (ACT10 ne 320 ACN8); [ulc| left; ulc]).

assert (L1n : length ip1' = 80%nat) by exact LI1'. assert (L2n : length ip2' = 80%nat) by exact LI2'.
apply rw_cells_f32_CB in XI1'. rewrite L1n in XI1'. change (4 * 80)%nat with 320%nat in XI1'.
apply rw_cells_f32_CB in XI2'. rewrite L2n in XI2'. change (4 * 80)%nat with 320%nat in XI2'.
chunk_cat RZ1 XI1'. chunk_cat RZ1 XI2'. chunk_cat RZ1 PAD1. apply rw_cells_to_CB in RZ1. cbn [cells_size csize Nat.add] in RZ1.
cps_seg (mc_w6 usp lo _ _).
destruct POST as (F10 & -> & ST11).
apply Hk. exists Σ4. split.
2:{ split; [congruence|]. split; [congruence|]. split; [congruence|]. split; [rewrite CR4, CR3, CR2, CR1; clear; lia|].
rewrite PO4, PO3, PO2, PO1. rewrite !pois_drop_cons_below by (unfold pz_lo; cbn [fst]; clear; lia).
apply pois_drop_above. apply (pois_above_le _ usp); [exact POA| clear; lia]. }
eapply ASTA_conseq; [eassumption|]. intros ms <-. exists v10, m10, ns'.
split; [rewrite ESP; unfold ret_stL; do 16 eexists; split; [reflexivity| exact FRM8]|].
split. { split; [exact ART10|]. split; [exact MI10|]. split; [cps_wmono| exact ST11]. }
split; [exact PF|]. split; [exact XNE8|]. split; [exact LNS'| exact ACN10].
Qed.
End MCCPS.
