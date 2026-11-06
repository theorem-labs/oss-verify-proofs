(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS Require Import X0mx X0k2.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1cr X1da X1dg X1df X1ck.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0j9 X05o X05p.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require Import X12c X14x X0r0 X0ra X0v9 X0yr X0wl X0wm X0yc.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition HIGHPASS_STACK : Z := 256.

Definition hp_rom (a : Z) : list byte := match image_bytes bsegs a 60 with Some bs => bs | None => [] end.
Lemma hp_rom_len : forall a, a = HP_PCOEF \/ a = HP_ZCOEF -> length (hp_rom a) = 60%nat.
Proof. intros a [-> | ->]; vm_compute; reflexivity. Qed.
Lemma hp_rom_at : forall (m : mem) a, mem_inv bsegs m -> a = HP_PCOEF \/ a = HP_ZCOEF -> bytes_at bsegs m a (hp_rom a).
Proof.
intros m a MI HA. apply ro_bytes_at; [exact MI| destruct HA as [-> | ->]; unfold HP_PCOEF, HP_ZCOEF; lia |
rewrite (hp_rom_len a HA); destruct HA as [-> | ->]; unfold HP_PCOEF, HP_ZCOEF; lia |].
apply ro_bytes_b_sound. destruct HA as [-> | ->]; vm_compute; reflexivity.
Qed.

Lemma hp_den_acc : forall (m : mem) (f sf : Z) (rs : list byte),
rw_cells bsegs m sf (hp_shadow_w2 rs) -> sf = Z.shiftr f 3 + SHB -> f mod 64 = 0 -> 0 <= f -> acc bsegs m (f + 32) 60.
Proof.
intros m f sf rs [[_ B] _] Esf F64 F0. unfold hp_shadow_w2 in B.
rewrite cells_bytes_app in B. apply bytes_at_app in B. destruct B as [B _].
assert (E : cells_bytes (map C1 (repeat hF1 4 ++ repeat z8 7 ++ [hb4] ++ repeat hF2 4 ++ repeat hF8 8 ++ repeat hF3 4))
= repeat hF1 4 ++ (repeat z8 7 ++ [hb4]) ++ repeat hF2 4 ++ repeat hF8 8 ++ repeat hF3 4) by reflexivity.
rewrite E in B. apply bytes_at_app in B. destruct B as [_ B]. apply bytes_at_app in B. destruct B as [BD _].
cbn [length repeat app] in BD.
assert (SH1 : shad (f + 32) = sf + 4) by (rewrite Esf, shad_shiftr; unfold shad; clear - F64; Z.div_mod_to_equations; lia).
apply acc_ushadow; [clear - F64; Z.div_mod_to_equations; lia | lia | lia |]. rewrite SH1. exact BD.
Qed.

Section HpCPS.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis SM2 : stack_malloc_contract RT 2.
Hypothesis MCP : memcpy_icontract RT e_asan_memcpy.

Definition highpass_cps : Prop :=
forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
F fc (m : mem) (PX PM filt lo fp P0 N0 : Z) (kp : nat) (xs ms0 : list word),
fdfs_only PMc -> mat_stable PMc ->
a0 = Z_to_bv 64 PX -> a1 = Z_to_bv 64 PX -> a2 = Z_to_bv 64 160 -> a3 = Z_to_bv 64 filt -> a4 = Z_to_bv 64 PM -> tp = Z_to_bv 64 0x638c98 ->
filt = 1 \/ filt = 3 ->

rw_cells bsegs m PX (f32 xs) -> length xs = 160%nat -> In (fp, kp) (rt_frames RT Σ) -> fp <= PX -> PX + 640 <= fp + fs_size kp - 8 ->
acc bsegs m PX 640 -> PX mod 4 = 0 ->

rw_cells bsegs m PM (f32 ms0) -> length ms0 = 2%nat -> In (P0, N0) (rt_live RT Σ) -> P0 <= PM -> PM + 8 <= P0 + N0 -> PM mod 8 = 0 ->
(length (rt_frames RT Σ) < FRAMES_MAX)%nat -> 1 <= rt_credit RT Σ ->
ART RT Σ m -> mem_inv bsegs m -> X1cn.frm0 fc ->
stk bsegs m lo (bv_unsigned sp) -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + RT_STACK + HIGHPASS_STACK <= bv_unsigned sp ->
bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 32 = 0 ->
cps bsegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
t3 t4 t5 t6 F fc B_highpass m)))
(fun c => exists (Σ' : rts RT),
ASTA RT Σ' PMc (fun ms => exists v m' (ys hs : list word),
ret_stL (fun F' fc' => X1cn.frm0 fc') ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v m' ms
/\ rt_after RT Σ' (bv_unsigned sp) lo m m'
/\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) [(PX, PX + 640); (PM, PM + 8)] m m'
/\ rw_cells bsegs m' PX (f32 ys) /\ length ys = 160%nat /\ acc bsegs m' PX 640
/\ rw_cells bsegs m' PM (f32 hs) /\ length hs = 2%nat) c
/\ rt_live RT Σ' = rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
/\ rt_credit RT Σ' = rt_credit RT Σ - 1 /\ rt_pois RT Σ' = rt_pois RT Σ).

Theorem highpass_ok : highpass_cps.
Proof using AF SM2 MCP.
intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
PX PM filt lo fp P0 N0 kp xs ms0 FDO MST -> -> -> -> -> -> HF XS LXS INF FPL FPH ACX X4 MS0 LMS INL PL PH M8 FRMS CR0 ART0 MI0 FRM0 ST0 LOW LOR SPT SPA.
intros T c Hc Hk.
set (usp := bv_unsigned sp) in *.
assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned).
unfold entry_st in Hc. rewrite ESP in Hc.
destruct (live_below_lo RT AF Σ m P0 N0 lo ART0 INL LOW) as (BL0 & BL1 & BL2).
destruct (frame_below_lo RT AF Σ m fp kp lo ART0 INF LOW) as (BF0 & BF1 & BF2).
pose proof (af_live_offshadow RT AF Σ m P0 N0 ART0 INL) as LSH.
pose proof (af_frames_hi RT AF Σ m fp kp ART0 INF) as FSHp.
pose proof (frame_facts RT AF Σ m fp kp ART0 INF) as (FP0 & FP64 & FPIMG & _).
destruct (frame_live_apart RT AF Σ m fp kp P0 N0 ART0 INF INL) as (FLA0 & _).
pose proof (af_client_consts RT AF Σ m ART0) as CC0.
pose proof (pres_fp_refl (rt_live RT Σ) (rt_frames RT Σ) usp [(PX, PX + 640); (PM, PM + 8)] m) as PF.
pose proof (fun E : rt_frames RT Σ = [] => af_pois_nil RT AF Σ m ART0 E) as PNIL.
pose proof (fun a => aclient_split RT AF Σ m usp a ART0) as SPL.
unfold HIGHPASS_STACK in *. cps_norm. cps_hide.

cps_seg (hp_w1 usp lo PX PX 160 filt PM).
destruct POST as (m1 & j8 & j16 & j24 & j32 & j40 & j48 & j56 & j64 & j72 & j80 & j88 & j96 & j104 & j128 & j136 & j144 & -> & MU1 & WM1 & MI1 & ST1 & FR1).
cps_seg_post.

cps_rt_sized SM2 0. { cbn; tauto. } { cps_callok. }
intros c2 (Σ1 & f & Hc2 & FRS1 & LV1 & SP1 & CR1 & FPOS & F64 & FTOP & PO1).
cps_unpack Hc2 as (m2 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2 & WRF & WRS).

pose proof (af_frames_disj RT AF Σ1 m2 f 2%nat fp kp [] (rt_frames RT Σ) ART2 FRS1 INF) as FFA.
cps_new_frame ART2 FRS1 LV1 SP1 WRF WRS sf. cps_hide.

cps_seg (hp_w2 usp lo PX PX 160 filt PM f sf).
destruct POST as (m3 & rb & rs & -> & MU3 & WM3 & MI3 & ST3 & FR3 & FRB3 & FRS3).
clear FR1 FRB FRS. cps_seg_post.

unfold hp_fhdr in FRB3. chunk_uncons FRB3 as HD3. chunk_uncons FRB3 as HD3b. chunk_uncons FRB3 as HD3c.
apply (rw_cells_split_CB bsegs _ _ [] 224 _ [] [8; 60; 36; 60; 60]%nat) in FRB3; [| reflexivity]. cbn [mk_CB_cells app] in FRB3.
chunk_uncons FRB3 as PAD3. chunk_uncons FRB3 as DENB. chunk_uncons FRB3 as GAP3. chunk_uncons FRB3 as NUMB. rename FRB3 into TAIL3.
replace (f + 8 + 8 + 8 + 8) with (f + 32) in DENB by lia.
replace (f + 8 + 8 + 8 + 8 + 60) with (f + 92) in GAP3 by lia.
replace (f + 8 + 8 + 8 + 8 + 60 + 36) with (f + 128) in NUMB by lia.
replace (f + 8 + 8 + 8 + 8 + 60 + 36 + 60) with (f + 188) in TAIL3 by lia.
replace (f + 8 + 8 + 8) with (f + 24) in PAD3 by lia.
replace (f + 8 + 8) with (f + 16) in HD3c by lia.
clear HD3b HD3c PAD3 GAP3 TAIL3. try clear Hc0.
pose proof (proj2 DENB) as WRD. cbn [cells_size csize Nat.add] in WRD. change (Z.of_nat 60) with 60 in WRD.
assert (ACD3 : acc bsegs m3 (f + 32) 60) by exact (hp_den_acc m3 f sf rs FRS3 Esf F64 ltac:(lia)).
assert (ACP3 : acc bsegs m3 HP_PCOEF 60).
{ destruct (aobj_lit RT AF Σ1 m3 HP_PCOEF 60 ART) as (_ & _ & H);
[ unfold ACC_LITS, HP_PCOEF; cbn [In]; repeat (first [left; reflexivity | right]) | unfold HP_PCOEF; lia | unfold HP_PCOEF, APP_TOP; lia | exact H ]. }
pose proof (hp_rom_at m3 HP_PCOEF MI3 (or_introl eq_refl)) as BYP.
pose proof (hp_rom_len HP_PCOEF (or_introl eq_refl)) as LBP.
set (bsp := hp_rom HP_PCOEF) in *. clearbody bsp.
cps_rt (MCP Σ1 PMc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m3 (f + 32) HP_PCOEF bsp lo).
{ rewrite LBP. reflexivity. }
{ unfold HP_PCOEF. lia. }
{ rewrite LBP. change (Z.of_nat 60) with 60. split; [intros _; split | left; unfold HP_PCOEF; lia].
- exact ACP3.
- right; right; right. unfold SEGTOP_A, HP_PCOEF. lia. }
{ rewrite LBP. change (Z.of_nat 60) with 60. split; [intros _; split | split].
- exact ACD3.
- right; left. exists f, 2%nat. split; [exact INF0| change (fs_size 2) with 256; lia].
- intros i Hi. right; right; right; left. exists f, 2%nat. split; [exact INF0| change (fs_size 2) with 256; lia].
- exact WRD. }
{ right. rewrite LBP. unfold HP_PCOEF. lia. }
{ cps_callok. }
intros c4 Hc4.
cps_unpack Hc4 as (m4 & RS4 & (ART4 & MI4 & WM4 & ST4) & PRES4 & BY4).
assert (DEN4 : rw_cells bsegs m4 (f + 32) [CB 60 bsp]).
{ split; [split|].
- cbn [cells_wf cell_wf]. split; [exact LBP| exact I].
- cbn [cells_bytes cbytes]. rewrite app_nil_r. exact BY4.
- cbn [cells_size csize Nat.add]. change (Z.of_nat 60) with 60. exact (wr_at_transport bsegs m3 m4 _ _ WRD WM4). }
destruct (rw_cells_CB_f32 bsegs m4 (f + 32) 15 bsp DEN4) as (den & LDEN & DEN).
clear DEN4 BY4 WRD LBP. try clear BYP. try clear ACD3. try clear ACP3. try clear PRES4. try clear bsp.

try clear PRES2. try clear Hc0. try clear Hc1.

cps_seg (hp_w3 usp 160 filt PM f sf).
destruct POST as (m5 & -> & MU5 & WM5 & MI5 & FRS5). clear FRS3. cps_seg_post.
pose proof (proj2 NUMB) as WRN. cbn [cells_size csize Nat.add] in WRN. change (Z.of_nat 60) with 60 in WRN.
destruct (hp_tabs_acc m5 f sf rs FRS5 Esf F64 ltac:(lia)) as (_ & ACN5).
assert (ACZ5 : acc bsegs m5 HP_ZCOEF 60).
{ destruct (aobj_lit RT AF Σ1 m5 HP_ZCOEF 60 ART) as (_ & _ & H);
[ unfold ACC_LITS, HP_ZCOEF; cbn [In]; repeat (first [left; reflexivity | right]) | unfold HP_ZCOEF; lia | unfold HP_ZCOEF, APP_TOP; lia | exact H ]. }
pose proof (hp_rom_at m5 HP_ZCOEF MI5 (or_intror eq_refl)) as BYZ.
pose proof (hp_rom_len HP_ZCOEF (or_intror eq_refl)) as LBZ.
set (bsz := hp_rom HP_ZCOEF) in *. clearbody bsz.
cps_rt (MCP Σ1 PMc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m5 (f + 128) HP_ZCOEF bsz lo).
{ rewrite LBZ. reflexivity. }
{ unfold HP_ZCOEF. lia. }
{ rewrite LBZ. change (Z.of_nat 60) with 60. split; [intros _; split | left; unfold HP_ZCOEF; lia].
- exact ACZ5.
- right; right; right. unfold SEGTOP_A, HP_ZCOEF. lia. }
{ rewrite LBZ. change (Z.of_nat 60) with 60. split; [intros _; split | split].
- exact ACN5.
- right; left. exists f, 2%nat. split; [exact INF0| change (fs_size 2) with 256; lia].
- intros i Hi. right; right; right; left. exists f, 2%nat. split; [exact INF0| change (fs_size 2) with 256; lia].
- exact WRN. }
{ right. rewrite LBZ. unfold HP_ZCOEF. lia. }
{ cps_callok. }
intros c6 Hc6. clear NUMB BYZ ACN5 ACZ5.
cps_unpack Hc6 as (m6 & RS6 & (ART6 & MI6 & WM6 & ST6) & PRES6 & BY6).

assert (NUM6 : rw_cells bsegs m6 (f + 128) [CB 60 bsz]).
{ split; [split|].
- cbn [cells_wf cell_wf]. split; [exact LBZ| exact I].
- cbn [cells_bytes cbytes]. rewrite app_nil_r. exact BY6.
- cbn [cells_size csize Nat.add]. change (Z.of_nat 60) with 60. exact (wr_at_transport bsegs m5 m6 _ _ WRN WM6). }
destruct (rw_cells_CB_f32 bsegs m6 (f + 128) 15 bsz NUM6) as (num & LNUM & NUM).
clear NUM6 BY6 WRN LBZ. try clear PRES6. try clear bsz.

assert (INFe : In (fp, kp) (rt_frames RT Σ)).
{ pose proof INF as I2. rewrite FRS1 in I2. destruct I2 as [E | H]; [| exact H]. exfalso.
injection E as <- <-. pose proof (FFA : _ \/ _) as U. change (fs_size 2) with 256 in U. lia. }
assert (FSK8 : fs_size kp mod 8 = 0).
{ unfold fs_size. rewrite Z.shiftl_mul_pow2 by lia. change 64 with (8 * 8). rewrite <- Z.mul_assoc, Z.mul_comm. apply Z.mod_mul. lia. }
assert (ACX6 : acc bsegs m6 PX 640).
{ apply (acc_pres_fp_frame (rt_live RT Σ) (rt_frames RT Σ) usp [(PX, PX + 640); (PM, PM + 8)] m m6 fp kp PX 640 PF INFe);
[ clear - FP64; Z.div_mod_to_equations; lia | exact FSK8 | lia | exact FPL | lia | | exact ACX ].
intros i Hi. pose proof (shad_window (PX + i) ltac:(unfold APP_TOP; ulc)) as SW. cbn [outside].
pose proof (FSHp : _ \/ _) as U1. pose proof (LSH : _ \/ _) as U2. unfold SH_LO, SH_HI in SW. clear - SW U1 U2 FPL FPH PL PH Hi. Lia.lia. }
destruct (af_acc_live RT AF Σ1 m6 P0 N0 ART6 INL) as (_ & ACL6).
assert (OBX6 : aobj bsegs m6 PX 640) by (split; [lia|]; split; [unfold APP_TOP; ulc| exact ACX6]).
assert (OBM6 : aobj bsegs m6 PM 8) by (split; [lia|]; split; [unfold APP_TOP; ulc| exact (acc_sub bsegs m6 P0 N0 PM 8 ACL6 PL PH)]).
clear ACL6.

cps_seg (hp_body usp lo PX PM f sf filt).
{ clear - FPH BF0 LOR SPT. Lia.lia. }
{ clear - PH BL1 LOR SPT. Lia.lia. }
unfold hp_body_post in POST.
destruct POST as (m7 & F7 & fc7 & xra7 & zt0 & zt1 & zt2 & za0 & za1 & za2 & za3 & za4 & za5 & za6 & za7 & zs2 & zs3 & zs4 & zs5 & zs6 & zs7 & zs8 & zs9 & zs11
& zt3 & zt4 & zt5 & zt6 & w16 & w24 & w32 & w40 & w48 & w56 & w80 & w88 & w96 & w104 & xs7 & u0 & u1
& -> & MU7 & WM7 & MI7 & FRM7 & ST7 & FR7 & XS7 & LXS7 & PMC7).
clear FR3 XS MS0 DEN NUM OBX6 OBM6 ACX6.
unfold hp_shadow_live, hF1, hF2, hF3, hb4, z8 in FRS5. cbn [map repeat app] in FRS5. cps_seg_post.

cps_seg (hp_epi_a usp f sf).
{ unfold hp_shadow_live, hF1, hF2, hF3, hb4, z8; cbn [map repeat app]; exact FRS5. }
destruct POST as (m8 & -> & MU8 & WM8 & MI8 & FR8 & FRS8).
clear FR7 FRS5 HD3. cps_seg_post.

lazymatch goal with A : ART RT Σ1 m8 |- _ => cps_release_intro A FRS1 LV1 (fun E : rt_frames RT Σ = [] => eq_trans PO1 (PNIL E)) Σ2 fl end.

assert (FLX : fl + 1 <= PX \/ PX + 640 <= fl).
{ destruct (Z_lt_le_dec fl PX) as [H|H]; [left; lia|]. destruct (Z_lt_le_dec fl (PX + 640)) as [H'|H']; [|right; lia].
exfalso. apply NAC. right; right; right; left. exists fp, kp. split; [exact INF| lia]. }
assert (FLM : fl + 1 <= PM \/ PM + 8 <= fl).
{ destruct (Z_lt_le_dec fl PM) as [H|H]; [left; lia|]. destruct (Z_lt_le_dec fl (PM + 8)) as [H'|H']; [|right; lia].
exfalso. apply NAC. right; right; left. exists P0, N0. split; [exact INL| lia]. }
cps_hide.
cps_seg (hp_epi_b usp lo f fl).
destruct POST as (m9 & a0'' & -> & MU9 & WM9 & MI9 & ST9 & FLG9).
clear FRS8. cps_release_done REL MU9 WM9 FLG9.

assert (ACX9 : acc bsegs m9 PX 640).
{ apply (acc_pres_fp_frame (rt_live RT Σ) (rt_frames RT Σ) usp [(PX, PX + 640); (PM, PM + 8)] m m9 fp kp PX 640 PF INFe);
[ clear - FP64; Z.div_mod_to_equations; lia | exact FSK8 | lia | exact FPL | lia | | exact ACX ].
intros i Hi. pose proof (shad_window (PX + i) ltac:(unfold APP_TOP; ulc)) as SW. cbn [outside].
pose proof (FSHp : _ \/ _) as U1. pose proof (LSH : _ \/ _) as U2. unfold SH_LO, SH_HI in SW. clear - SW U1 U2 FPL FPH PL PH Hi. Lia.lia. }
apply Hk. exists Σ2. split; [| repeat split; congruence].
eapply ASTA_conseq; [eassumption|]. intros ms <-. exists a0'', m9, xs7, [u0; u1].
split; [rewrite ESP; unfold ret_stL; do 16 eexists; split; [reflexivity| exact FRM7]|].
split. { split; [assumption|]. split; [exact MI9|]. split; [cps_wmono| exact ST9]. }
split; [exact PF|]. split; [exact XS7|]. split; [exact LXS7|]. split; [exact ACX9|]. split; [exact PMC7| reflexivity].
Qed.
End HpCPS.

