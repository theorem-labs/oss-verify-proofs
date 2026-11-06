(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS Require Import X0mx X0k2.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1da X1dg X1df X1ck.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0bp X0j9 X0ec X001 X00b X04b X07z X05o X05p X05s
X05l X07r X07y X07t X07u X07v.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X12c X14x X0r0 X0ra X0v9 X0yr X0wl X0yj X0yq X0yl X0ym X0yn.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14x OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0r0 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ra OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0v9 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0yr OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0wl OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0yj OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0yq OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0yl OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ym OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0yn.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section IpCPS.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis SM2 : stack_malloc_contract RT 2.

Local Ltac ul := unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK, SH_HI, SH_LO, APP_TOP, IMG_TOP_B in *; lia.

Definition interp_pitch_cps : Prop :=
forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
F fc (m : mem) (EB eoff p IP P0 N0 IA IN lo : Z) (eb ip : list word),
fdfs_only PMc -> mat_stable PMc ->
a0 = Z_to_bv 64 (EB + 4 * eoff) -> a1 = Z_to_bv 64 IP -> a2 = Z_to_bv 64 p -> tp = Z_to_bv 64 0x638c98 ->

rw_cells bsegs m EB (f32 eb) -> length eb = 500%nat -> In (P0, N0) (rt_live RT Σ) -> P0 <= EB -> EB + 2000 <= P0 + N0 -> EB mod 4 = 0 ->
0 <= eoff - p - 6 -> eoff - p <= 414 -> eoff + 80 <= 500 -> 0 <= eoff ->

rw_cells bsegs m IP (f32 ip) -> length ip = 80%nat -> bv_unsigned sp <= IP -> IP + 320 <= USTACK_TOP - 16 -> IP mod 4 = 0 ->
(length (rt_frames RT Σ) < FRAMES_MAX)%nat -> 1 <= rt_credit RT Σ -> In (IA, IN) (rt_pois RT Σ) -> IA <= IP -> IP + 320 <= IA + IN ->
ART RT Σ m -> mem_inv bsegs m -> frm0 fc ->
stk bsegs m lo (bv_unsigned sp) -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + RT_STACK + 240 <= bv_unsigned sp ->
bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 32 = 0 ->
cps bsegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
t3 t4 t5 t6 F fc A_interp_pitch m)))
(fun c => exists (Σ' : rts RT),
ASTA RT Σ' PMc (fun ms => exists v m' ip',
ret_stL (fun _ fc' => frm0 fc') ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v m' ms
/\ rt_after RT Σ' (bv_unsigned sp) lo m m'
/\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) [(IP, IP + 320)] m m'
/\ rw_cells bsegs m' IP (f32 ip') /\ length ip' = 80%nat) c
/\ rt_live RT Σ' = rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
/\ rt_credit RT Σ' = rt_credit RT Σ - 1 /\ rt_pois RT Σ' = rt_pois RT Σ).

Theorem interp_pitch_ok : interp_pitch_cps.
Proof using AF SM2.
intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
EB eoff p IP P0 N0 IA IN lo eb ip FDO MST -> -> -> -> XEB LEB INL PL PH E4 R1 R2 R3 R4 XIP LIP IPLO IPHI IP4 FRM CR0 INP IAL IAH ART0 MI0 FRM0 ST0 LOW LOR SPT SPA.
intros T c Hc Hk.
set (usp := bv_unsigned sp) in *.
assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned).
unfold entry_st in Hc. rewrite ESP in Hc.
destruct (live_below_lo RT AF Σ m P0 N0 lo ART0 INL LOW) as (BL0 & BL1 & BL2).
pose proof (af_client_consts RT AF Σ m ART0) as CC0.
pose proof (pres_fp_refl (rt_live RT Σ) (rt_frames RT Σ) usp [(IP, IP + 320)] m) as PF.
pose proof (fun a => aclient_split RT AF Σ m usp a ART0) as SPL.
pose proof (fun E : rt_frames RT Σ = [] => af_pois_nil RT AF Σ m ART0 E) as PNIL.
cps_norm.

cps_seg (ip_w1 usp lo (EB + 4 * eoff) IP p).
destruct POST as (m1 & j8 & j16 & j24 & j32 & j40 & j48 & j64 & j72 & j80 & -> & MU1 & WM1 & MI1 & ST1 & FR1). cps_seg_post.

cps_rt_sized SM2 0. { cbn; tauto. } { cps_callok. }
intros c2 (Σ1 & f & Hc2 & FRS1 & LV1 & SP1 & CR1 & FPOS & F64 & FTOP & PO1).
cps_unpack Hc2 as (m2 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2 & WRF & WRS).
cps_new_frame ART2 FRS1 LV1 SP1 WRF WRS sf.

cps_seg (ip_w2 usp lo (EB + 4 * eoff) IP p f sf).
{ ulc. } { ulc. }
destruct POST as (m3 & a0' & a1' & a2' & rb & rs & -> & MU3 & WM3 & MI3 & ST3 & FR3 & FRB3 & FRS3).
clear FR1 FRB FRS. cps_seg_post.

destruct (af_acc_live RT AF Σ1 m3 P0 N0 ART INL) as (_ & ACL).
assert (OBE : aobj bsegs m3 EB 2000) by (split; [ulc|]; split; [ulc|]; exact (acc_sub bsegs m3 P0 N0 EB 2000 ACL PL PH)).
assert (INP1 : In (IA, IN) (rt_pois RT Σ1)) by (rewrite PO1; exact INP).
assert (OBI : aobj bsegs m3 IP 320) by (split; [ulc|]; split; [ulc|]; exact (acc_sub bsegs m3 IA IN IP 320 (af_acc_pois RT AF Σ1 m3 IA IN ART INP1) IAL IAH)).
assert (OBF : aobj bsegs m3 SHIFT_FILT 84) by (apply (aobj_lit RT AF Σ1 m3 SHIFT_FILT 84 ART); [unfold ACC_LITS, SHIFT_FILT; cbn [In]; repeat (first [left; reflexivity | right]) | unfold SHIFT_FILT; lia | unfold SHIFT_FILT, APP_TOP; lia]).
assert (OBC : aobj bsegs m3 (f + 32) 112) by (split; [ulc|]; split; [ulc|]; exact (ip_corr_acc m3 f sf rs FRS3 Esf F64 ltac:(lia))).
unfold ip_fhdr in FRB3. chunk_uncons FRB3 as HD3. chunk_uncons FRB3 as HD3b. chunk_uncons FRB3 as HD3c.
apply (rw_cells_split_CB bsegs _ _ [] 224 _ [] [8; 112; 104]%nat) in FRB3; [| reflexivity]. cbn [mk_CB_cells app] in FRB3.
chunk_uncons FRB3 as PAD3. chunk_uncons FRB3 as CORR3. replace (f + 8 + 8 + 8 + 8) with (f + 32) in CORR3 by lia.
pose proof (af_client_consts RT AF Σ1 m3 ART) as CC3.

unfold ip_frame in FR3. chunk_uncons FR3 as FC0. chunk_uncons FR3 as FC8. chunk_uncons FR3 as FC16. chunk_uncons FR3 as FC24.
chunk_uncons FR3 as FC32. chunk_uncons FR3 as FC40. chunk_uncons FR3 as FC48. chunk_uncons FR3 as FC56.
chunk_cat FC32 FC40. chunk_cat FC32 FC48. chunk_cat FC32 FC56.
replace (usp + -192 + 8 + 8 + 8 + 8) with (usp + -192 + 32) in FC32 by lia.
cps_seg (ip_body (usp + -192) lo EB eoff p IP f (f + 32) eb ip).
{ clear - FIMG. unfold IMG_TOP_B. lia. }
destruct POST as (ra5 & x0 & x1 & x2 & y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & z2 & z3 & z4 & z5 & z6 & z7 & z8 & z9 & z10 & z11 & x3 & x4 & x5 & x6
& F5 & fc5 & m5 & ip5 & cb5 & -> & MU5 & WM5 & MI5 & FRM5 & ST5 & XIP5 & LIP5 & CORR5 & FC5).
clear XIP CORR3 ST3 ST2 OBE OBI OBF OBC ACL CC3 HD3b HD3c PAD3 FRB3 FC32.
unfold ip_shadow_live, bF1, bF3 in FRS3. cbn [map repeat app] in FRS3. cps_seg_post.
chunk_cat FC0 FC8. chunk_cat FC0 FC16. chunk_cat FC0 FC24. chunk_cat FC0 FC5. chunk_cat FC0 FR3.

cps_seg (ip_epi_a usp f sf).
{ exact FRS3. }
destruct POST as (m6 & -> & MU6 & WM6 & MI6 & FR6 & FRS6).
clear FC0 FRS3 HD3 CORR5. cps_seg_post.

cps_release_intro ART FRS1 LV1 (fun E : rt_frames RT Σ = [] => eq_trans PO1 (PNIL E)) Σ2 fl.
cps_seg (ip_epi_b usp lo f fl).
destruct POST as (m7 & -> & MU7 & WM7 & MI7 & ST7 & FLG7).
clear FRS6 XEB. cps_release_done REL MU7 WM7 FLG7.
apply Hk. exists Σ2. split; [| repeat split; congruence].
eapply ASTA_conseq; [eassumption|]. intros ms <-. exists (Z_to_bv 64 fl), m7, ip5.
split; [rewrite ESP; unfold ret_stL; do 16 eexists; split; [reflexivity| exact FRM5]|].
split. { split; [assumption|]. split; [exact MI7|]. split; [cps_wmono| exact ST7]. }
split; [exact PF| split; [exact XIP5| exact LIP5]].
Qed.
End IpCPS.
End B_TWIN.

Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section IpCPS.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis SM2 : stack_malloc_contract RT 2.

Local Ltac ul := unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK, SH_HI, SH_LO, APP_TOP, IMG_TOP in *; lia.

Definition interp_pitch_cps : Prop :=
forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
F fc (m : mem) (EB eoff p IP P0 N0 IA IN lo : Z) (eb ip : list word),
fdfs_only PMc -> mat_stable PMc ->
a0 = Z_to_bv 64 (EB + 4 * eoff) -> a1 = Z_to_bv 64 IP -> a2 = Z_to_bv 64 p -> tp = Z_to_bv 64 0x630458 ->

rw_cells asegs m EB (f32 eb) -> length eb = 500%nat -> In (P0, N0) (rt_live RT Σ) -> P0 <= EB -> EB + 2000 <= P0 + N0 -> EB mod 4 = 0 ->
0 <= eoff - p - 6 -> eoff - p <= 414 -> eoff + 80 <= 500 -> 0 <= eoff ->

rw_cells asegs m IP (f32 ip) -> length ip = 80%nat -> bv_unsigned sp <= IP -> IP + 320 <= USTACK_TOP - 16 -> IP mod 4 = 0 ->
(length (rt_frames RT Σ) < FRAMES_MAX)%nat -> 1 <= rt_credit RT Σ -> In (IA, IN) (rt_pois RT Σ) -> IA <= IP -> IP + 320 <= IA + IN ->
ART RT Σ m -> mem_inv asegs m -> frm0 fc ->
stk asegs m lo (bv_unsigned sp) -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + RT_STACK + 176 <= bv_unsigned sp ->
bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 32 = 0 ->
cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
t3 t4 t5 t6 F fc A_interp_pitch m)))
(fun c => exists (Σ' : rts RT),
ASTA RT Σ' PMc (fun ms => exists v m' ip',
ret_stL (fun _ fc' => frm0 fc') ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v m' ms
/\ rt_after RT Σ' (bv_unsigned sp) lo m m'
/\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) [(IP, IP + 320)] m m'
/\ rw_cells asegs m' IP (f32 ip') /\ length ip' = 80%nat) c
/\ rt_live RT Σ' = rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
/\ rt_credit RT Σ' = rt_credit RT Σ - 1 /\ rt_pois RT Σ' = rt_pois RT Σ).

Theorem interp_pitch_ok : interp_pitch_cps.
Proof using AF SM2.
intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
EB eoff p IP P0 N0 IA IN lo eb ip FDO MST -> -> -> -> XEB LEB INL PL PH E4 R1 R2 R3 R4 XIP LIP IPLO IPHI IP4 FRM CR0 INP IAL IAH ART0 MI0 FRM0 ST0 LOW LOR SPT SPA.
intros T c Hc Hk.
set (usp := bv_unsigned sp) in *.
assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned).
unfold entry_st in Hc. rewrite ESP in Hc.
destruct (live_below_lo RT AF Σ m P0 N0 lo ART0 INL LOW) as (BL0 & BL1 & BL2).
pose proof (af_client_consts RT AF Σ m ART0) as CC0.
pose proof (pres_fp_refl (rt_live RT Σ) (rt_frames RT Σ) usp [(IP, IP + 320)] m) as PF.
pose proof (fun a => aclient_split RT AF Σ m usp a ART0) as SPL.
pose proof (fun E : rt_frames RT Σ = [] => af_pois_nil RT AF Σ m ART0 E) as PNIL.
cps_norm.

cps_seg (ip_w1 usp lo (EB + 4 * eoff) IP p).
destruct POST as (m1 & j8 & j16 & j24 & j32 & j40 & j48 & -> & MU1 & WM1 & MI1 & ST1 & FR1). cps_seg_post.

cps_rt_sized SM2 0. { cbn; tauto. } { cps_callok. }
intros c2 (Σ1 & f & Hc2 & FRS1 & LV1 & SP1 & CR1 & FPOS & F64 & FTOP & PO1).
cps_unpack Hc2 as (m2 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2 & WRF & WRS).
cps_new_frame ART2 FRS1 LV1 SP1 WRF WRS sf.

cps_seg (ip_w2 usp lo (EB + 4 * eoff) IP p f sf).
destruct POST as (m3 & a0' & a1' & a2' & rb & rs & -> & MU3 & WM3 & MI3 & ST3 & FR3 & FRB3 & FRS3).
clear FR1 FRB FRS. cps_seg_post.

destruct (af_acc_live RT AF Σ1 m3 P0 N0 ART INL) as (_ & ACL).
assert (OBE : aobj asegs m3 EB 2000) by (split; [ulc|]; split; [ulc|]; exact (acc_sub asegs m3 P0 N0 EB 2000 ACL PL PH)).
assert (INP1 : In (IA, IN) (rt_pois RT Σ1)) by (rewrite PO1; exact INP).
assert (OBI : aobj asegs m3 IP 320) by (split; [ulc|]; split; [ulc|]; exact (acc_sub asegs m3 IA IN IP 320 (af_acc_pois RT AF Σ1 m3 IA IN ART INP1) IAL IAH)).
assert (OBF : aobj asegs m3 SHIFT_FILT 84) by (apply (aobj_lit RT AF Σ1 m3 SHIFT_FILT 84 ART); [unfold ACC_LITS, SHIFT_FILT; cbn [In]; repeat (first [left; reflexivity | right]) | unfold SHIFT_FILT; lia | unfold SHIFT_FILT, APP_TOP; lia]).
assert (OBC : aobj asegs m3 (f + 32) 112) by (split; [ulc|]; split; [ulc|]; exact (ip_corr_acc m3 f sf rs FRS3 Esf F64 ltac:(lia))).
unfold ip_fhdr in FRB3. chunk_uncons FRB3 as HD3. chunk_uncons FRB3 as HD3b. chunk_uncons FRB3 as HD3c.
apply (rw_cells_split_CB asegs _ _ [] 224 _ [] [8; 112; 104]%nat) in FRB3; [| reflexivity]. cbn [mk_CB_cells app] in FRB3.
chunk_uncons FRB3 as PAD3. chunk_uncons FRB3 as CORR3. replace (f + 8 + 8 + 8 + 8) with (f + 32) in CORR3 by lia.
pose proof (af_client_consts RT AF Σ1 m3 ART) as CC3.
cps_seg (ip_body (usp + -160) lo EB eoff p IP f (f + 32) eb ip).
destruct POST as (ra5 & x0 & x1 & x2 & y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & z2 & z3 & z4 & z5 & z6 & z9 & z10 & z11 & x3 & x4 & x5 & x6
& F5 & fc5 & m5 & ip5 & cb5 & -> & MU5 & WM5 & MI5 & FRM5 & ST5 & XIP5 & LIP5 & CORR5).
clear XIP CORR3 ST3 ST2 OBE OBI OBF OBC ACL CC3 HD3b HD3c PAD3 FRB3.
unfold ip_frame in FR3. unfold ip_shadow_live, bF1, bF3 in FRS3. cbn [map repeat app] in FRS3. cps_seg_post.

cps_seg (ip_epi_a usp f sf). { exact FRS3. }
destruct POST as (m6 & -> & MU6 & WM6 & MI6 & FR6 & FRS6).
clear FR3 FRS3 HD3 CORR5. cps_seg_post.

cps_release_intro ART FRS1 LV1 (fun E : rt_frames RT Σ = [] => eq_trans PO1 (PNIL E)) Σ2 fl.
cps_seg (ip_epi_b usp lo f fl).
destruct POST as (m7 & a0'' & -> & MU7 & WM7 & MI7 & ST7 & FLG7).
clear FRS6 XEB. cps_release_done REL MU7 WM7 FLG7.
apply Hk. exists Σ2. split; [| repeat split; congruence].
eapply ASTA_conseq; [eassumption|]. intros ms <-. exists a0'', m7, ip5.
split; [rewrite ESP; unfold ret_stL; do 16 eexists; split; [reflexivity| exact FRM5]|].
split. { split; [assumption|]. split; [exact MI7|]. split; [cps_wmono| exact ST7]. }
split; [exact PF| split; [exact XIP5| exact LIP5]].
Qed.
End IpCPS.
