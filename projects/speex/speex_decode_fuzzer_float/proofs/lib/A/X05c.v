(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS Require Import X0mx X0k2.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1da X1dg X1cg.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1nt X1r8.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0bp X0j9 X0ec X001 X00b X04b X07z X05o X05p X05s
X05l X05e X05d.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X12c X14x X0r0 X0ra X0v9 X0wl X0wb X0wa.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14x OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0r0 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ra OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0v9 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0wl OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0wb OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0wa.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition bits_shadow : list cell := map C1 (repeat z8 6).

Lemma bits_shadow_acc : forall (m : mem) A, ro_cells bsegs m (shad A) bits_shadow -> A mod 8 = 0 -> 0 <= A -> acc bsegs m A 48.
Proof.
intros m A [_ B] A8 A0. change 48 with (8 * Z.of_nat 6). apply acc_zero_run; [exact A8| exact A0|]. exact B.
Qed.

Lemma bits_init_prun : forall q r q', prun (speex_bits_init (St := pst) p_calloc) q = Some (r, q') -> r = Some bits_fresh /\ q' = q.
Proof.
intros q r q' H. unfold speex_bits_init in H.
rewrite prun_bind in H. rewrite (prun_calloc_ok MAX_CHARS_PER_FRAME 1 q) in H by (unfold MAX_CHARS_PER_FRAME; lia).
rewrite prun_ret in H. injection H as <- <-. split; reflexivity.
Qed.

Section BitsCPS.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis CAL : calloc_contract RT.

Definition speex_bits_init_cps : Prop :=
forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
F fc (m : mem) (A f lo : Z) (k : nat) (junk : list byte),
fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 A -> tp = Z_to_bv 64 0x638c98 ->
rw_cells bsegs m A [CB 48 junk] -> ro_cells bsegs m (shad A) bits_shadow -> A mod 8 = 0 ->
In (f, k) (rt_frames RT Σ) -> f <= A -> A + 48 <= f + fs_size k - 8 ->
Z.of_nat (length (rt_live RT Σ)) < LIVE_MAX -> 0 <= rt_credit RT Σ ->
ART RT Σ m -> mem_inv bsegs m ->
stk bsegs m lo (bv_unsigned sp) -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + RT_STACK + 32 <= bv_unsigned sp ->
bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 ->
cps bsegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
t3 t4 t5 t6 F fc A_speex_bits_init m)))
(fun c => exists (Σ' : rts RT) (D : Z),
ASTA RT Σ' PMc (fun ms => exists v m',
ret_stL (fun F' fc' => F' = F /\ fc' = fc) ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v m' ms
/\ rt_after RT Σ' (bv_unsigned sp) lo m m'
/\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) [(A, A + 48)] m m'
/\ bits_rep bsegs m' A D bits_fresh /\ ro_cells bsegs m' (shad A) bits_shadow) c
/\ rt_live RT Σ' = (D, 2000) :: rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
/\ rt_credit RT Σ' = rt_credit RT Σ /\ rt_pois RT Σ' = rt_pois RT Σ).

Theorem speex_bits_init_ok : speex_bits_init_cps.
Proof using AF CAL.
intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m A f lo k junk
FDO MST -> -> OBJ SHC A8 INF FA1 FA2 LVM CR0 ART0 MI0 ST0 LOW LOR SPT SPA.
intros T c Hc Hk.
set (usp := bv_unsigned sp) in *.
assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned).
unfold entry_st in Hc. rewrite ESP in Hc.
unfold bits_shadow in SHC. cbn [map repeat] in SHC.
destruct (frame_below_lo RT AF Σ m f k lo ART0 INF LOW) as (BF1 & BF2 & BF3).
pose proof (frame_facts RT AF Σ m f k ART0 INF) as (F0 & F64 & FIMG & _ & FHI & _ & SHF1 & _ & _ & FSELF).
assert (FSZ : 0 <= fs_size k) by (unfold fs_size; apply Z.shiftl_nonneg; lia).
assert (FS8 : fs_size k mod 8 = 0) by (unfold fs_size; rewrite Z.shiftl_mul_pow2 by lia; change 64 with (8 * 8); rewrite <- Z.mul_assoc, Z.mul_comm, Z.mod_mul by lia; reflexivity).
destruct (shad_inside f (fs_size k) A 48 ltac:(clear - F64; Z.div_mod_to_equations; lia) A8 FS8 eq_refl ltac:(lia) FA1 ltac:(lia) ltac:(lia)) as (SHA1 & SHA2). change (48 / 8) with 6 in SHA2.
assert (BSA : shad A + 6 <= lo) by lia.
pose proof (af_client_consts RT AF Σ m ART0) as CC0.
pose proof (pres_fp_refl (rt_live RT Σ) (rt_frames RT Σ) usp [(A, A + 48)] m) as PF.
pose proof (fun a => aclient_split RT AF Σ m usp a ART0) as SPL.
cps_norm.

cps_seg (bits_init_w1 A usp lo).
destruct POST as (m1 & j0 & -> & MU1 & WM1 & MI1 & ST1 & FR1). cps_seg_post.

assert (EU32 : bv_unsigned (Z_to_bv 64 (usp + -32)) = usp + -32) by (apply unsigned_lit; ulc).
cps_rt CAL.
{ cps_callok. }
{ apply unwind_ok_ch. unfold unwind_ok, RA_bits_init_calloc. rewrite EU32, !unsigned_lit by ulc.
split; [unfold ALLOC_RAS; cbn [In]; repeat (first [left; reflexivity | right])| left; ulc]. }
intros c2 (Σ1 & D & Hc2 & LV1 & FRS1 & SP1 & CR1 & DPOS & D16 & DTOP & PO1).
change (2000 * 1) with 2000 in *. change (mcost 2000) with 0 in CR1. rewrite Z.sub_0_r in CR1. change (Z.to_nat 2000) with 2000%nat in *.
cps_unpack Hc2 as (m2 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2 & WRD & ACD & BYD).
pose proof (fun a Ha => newchunk_apart RT AF Σ Σ1 m2 D 2000 usp a ART2 LV1 FRS1 SP1 ltac:(ulc) ltac:(lia) Ha) as NAD.
cps_sigma LV1 FRS1 SP1.
destruct (live_below_lo RT AF Σ1 m2 D 2000 lo ART2 INL LOW) as (_ & BD1 & _).
destruct (frame_live_apart RT AF Σ1 m2 f k D 2000 ART2 INF INL) as (FLA1 & FLA2). rewrite SHF1 in FLA2.
pose proof (live_facts RT AF Σ1 m2 D 2000 ART2 INL) as (_ & _ & _ & DHI).
assert (BLK : rw_cells bsegs m2 D [CB 2000 (repeat z8 2000)]).
{ split; [split; [split; [vm_compute; reflexivity| exact I]| cbn [cells_bytes cbytes app]; rewrite app_nil_r; exact BYD]| exact WRD]. }
assert (OBA : aobj bsegs m2 A BITS_SIZEOF) by (split; [ulc|]; split; [unfold BITS_SIZEOF; ulc|]; apply bits_shadow_acc; [exact SHC| exact A8| ulc]).
assert (OBD : aobj bsegs m2 D 2000) by (split; [lia|]; split; [ulc| exact ACD]).
cps_norm.

cps_seg (bits_init_w2 A D usp lo).
{ unfold BITS_SIZEOF; ulc. } { unfold BITS_SIZEOF; ulc. } { unfold BITS_SIZEOF; ulc. }
destruct POST as (m3 & a0' & a1' & a2' & -> & MU3 & WM3 & MI3 & ST3 & REP3 & OK3).
clear OBJ BLK FR1 OBA OBD. cps_seg_post.
apply Hk. exists Σ1, D. split; [| repeat split; congruence].
eapply ASTA_conseq; [eassumption|]. intros ms <-. exists a0', m3.
split; [rewrite ESP; unfold ret_stL; do 16 eexists; split; [reflexivity| split; reflexivity]|].
split. { split; [assumption|]. split; [exact MI3|]. split; [cps_wmono| exact ST3]. }
split; [exact PF|]. split; [exact REP3|]. unfold bits_shadow. cbn [map repeat]. exact SHC.
Qed.

Hypothesis FRE : free_contract RT.

Definition speex_bits_destroy_cps : Prop :=
forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
F fc (m : mem) (A D f lo : Z) (k : nat) (b : bits_st unit),
fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 A -> tp = Z_to_bv 64 0x638c98 ->
bits_rep bsegs m A D b -> bits_ok b -> sb_owner b = 1 -> ro_cells bsegs m (shad A) bits_shadow ->
In (f, k) (rt_frames RT Σ) -> f <= A -> A + 48 <= f + fs_size k - 8 ->
In (D, sb_buf_size b) (rt_live RT Σ) ->
ART RT Σ m -> mem_inv bsegs m ->
stk bsegs m lo (bv_unsigned sp) -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + RT_STACK + 16 <= bv_unsigned sp ->
bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 ->
unwind_ch m ra s0 sp ->
cps bsegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
t3 t4 t5 t6 F fc A_speex_bits_destroy m)))
(fun c => exists (Σ' : rts RT),
ASTA RT Σ' PMc (fun ms => exists v m',
ret_stL (fun F' fc' => F' = F /\ fc' = fc) ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v m' ms
/\ rt_after_f RT Σ' (bv_unsigned sp) lo m m'
/\ rt_pres_fp (rt_live RT Σ') (rt_frames RT Σ) (bv_unsigned sp) [] m m') c
/\ rt_live RT Σ' = live_remove D (rt_live RT Σ) /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
/\ rt_credit RT Σ' = rt_credit RT Σ /\ rt_pois RT Σ' = rt_pois RT Σ).

Theorem speex_bits_destroy_ok : speex_bits_destroy_cps.
Proof using AF FRE.
intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m A D f lo k b
FDO MST -> -> REP OK OWN SHC INF FA1 FA2 INL ART0 MI0 ST0 LOW LOR SPT SPA UNW.
intros T c Hc Hk.
set (usp := bv_unsigned sp) in *.
assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned).
unfold entry_st in Hc. rewrite ESP in Hc.
unfold bits_shadow in SHC. cbn [map repeat] in SHC.
destruct (frame_below_lo RT AF Σ m f k lo ART0 INF LOW) as (BF1 & BF2 & BF3).
destruct (live_below_lo RT AF Σ m D (sb_buf_size b) lo ART0 INL LOW) as (BD0 & BD1 & _).
pose proof (frame_facts RT AF Σ m f k ART0 INF) as (F0 & F64 & FIMG & _ & _ & _ & _ & _ & _ & _).
assert (FSZ : 0 <= fs_size k) by (unfold fs_size; apply Z.shiftl_nonneg; lia).
pose proof REP as (_ & _ & (A8 & _)).
pose proof (af_client_consts RT AF Σ m ART0) as CC0.
pose proof (fun a => aclient_split RT AF Σ m usp a ART0) as SPL.
assert (OBA : aobj bsegs m A BITS_SIZEOF) by (split; [ulc|]; split; [unfold BITS_SIZEOF; ulc|]; apply bits_shadow_acc; [exact SHC| exact A8| ulc]).
cps_norm.

cps_seg (bits_destroy_w1 A D usp lo b).
{ unfold BITS_SIZEOF; ulc. }
destruct POST as (m1 & a1' & a2' & a3' & -> & MU1 & WM1 & MI1 & ST1 & REP1).
assert (UNW1 : unwind_ch m1 ra s0 (Z_to_bv 64 usp)).
{ rewrite <- ESP. apply (unwind_ch_transport [(usp + -16, usp)] m m1 ra s0 sp); [| exact MU1| exact WM1| exact UNW].
intros a Ha. cbn [disjoint_from]. fold usp in Ha. split; [lia| exact I]. }
cps_seg_post.

cps_rt FRE. { cps_callok. }
intros c2 (Σ1 & v & Hc2 & LV1 & FRS1 & SP1 & CR1 & PO1).
cps_unpack Hc2 as (m2 & RS2 & (ART2 & MI2 & ST2) & PRES2).
apply Hk. exists Σ1. split; [| repeat split; assumption].
eapply ASTA_conseq; [eassumption|]. intros ms <-. exists v, m2.
split; [rewrite ESP; unfold ret_stL; do 16 eexists; split; [reflexivity| split; reflexivity]|].
split; [exact (conj ART2 (conj MI2 ST2))|].
intros a Ha Ho. rewrite (PRES2 a); [| exact Ha].
apply MU1. cbn [outside]. split; [| exact I].
assert (Ha' : aclient (rt_live RT Σ) (rt_frames RT Σ) usp (bv_unsigned a)).
{ apply (aclient_mono _ _ _ _ _ _ _ Ha); [| auto| lia]. intros e He. rewrite LV1 in He. exact (live_remove_sub _ _ _ He). }
clear - SPL Ha' LOW LOR. specialize (SPL _ Ha'). lia.
Qed.
End BitsCPS.
End B_TWIN.

Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition bits_shadow : list cell := map C1 (repeat z8 6).

Lemma bits_shadow_acc : forall (m : mem) A, ro_cells asegs m (shad A) bits_shadow -> A mod 8 = 0 -> 0 <= A -> acc asegs m A 48.
Proof.
intros m A [_ B] A8 A0. change 48 with (8 * Z.of_nat 6). apply acc_zero_run; [exact A8| exact A0|]. exact B.
Qed.

Lemma bits_init_prun : forall q r q', prun (speex_bits_init (St := pst) p_calloc) q = Some (r, q') -> r = Some bits_fresh /\ q' = q.
Proof.
intros q r q' H. unfold speex_bits_init in H.
rewrite prun_bind in H. rewrite (prun_calloc_ok MAX_CHARS_PER_FRAME 1 q) in H by (unfold MAX_CHARS_PER_FRAME; lia).
rewrite prun_ret in H. injection H as <- <-. split; reflexivity.
Qed.

Section BitsCPS.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis CAL : calloc_contract RT.

Definition speex_bits_init_cps : Prop :=
forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
F fc (m : mem) (A f lo : Z) (k : nat) (junk : list byte),
fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 A -> tp = Z_to_bv 64 0x630458 ->
rw_cells asegs m A [CB 48 junk] -> ro_cells asegs m (shad A) bits_shadow -> A mod 8 = 0 ->
In (f, k) (rt_frames RT Σ) -> f <= A -> A + 48 <= f + fs_size k - 8 ->
Z.of_nat (length (rt_live RT Σ)) < LIVE_MAX -> 0 <= rt_credit RT Σ ->
ART RT Σ m -> mem_inv asegs m ->
stk asegs m lo (bv_unsigned sp) -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + RT_STACK + 32 <= bv_unsigned sp ->
bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 ->
cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
t3 t4 t5 t6 F fc A_speex_bits_init m)))
(fun c => exists (Σ' : rts RT) (D : Z),
ASTA RT Σ' PMc (fun ms => exists v m',
ret_stL (fun F' fc' => F' = F /\ fc' = fc) ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v m' ms
/\ rt_after RT Σ' (bv_unsigned sp) lo m m'
/\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) [(A, A + 48)] m m'
/\ bits_rep asegs m' A D bits_fresh /\ ro_cells asegs m' (shad A) bits_shadow) c
/\ rt_live RT Σ' = (D, 2000) :: rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
/\ rt_credit RT Σ' = rt_credit RT Σ /\ rt_pois RT Σ' = rt_pois RT Σ).

Theorem speex_bits_init_ok : speex_bits_init_cps.
Proof using AF CAL.
intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m A f lo k junk
FDO MST -> -> OBJ SHC A8 INF FA1 FA2 LVM CR0 ART0 MI0 ST0 LOW LOR SPT SPA.
intros T c Hc Hk.
set (usp := bv_unsigned sp) in *.
assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned).
unfold entry_st in Hc. rewrite ESP in Hc.
unfold bits_shadow in SHC. cbn [map repeat] in SHC.
destruct (frame_below_lo RT AF Σ m f k lo ART0 INF LOW) as (BF1 & BF2 & BF3).
pose proof (frame_facts RT AF Σ m f k ART0 INF) as (F0 & F64 & FIMG & _ & FHI & _ & SHF1 & _ & _ & FSELF).
assert (FSZ : 0 <= fs_size k) by (unfold fs_size; apply Z.shiftl_nonneg; lia).
assert (FS8 : fs_size k mod 8 = 0) by (unfold fs_size; rewrite Z.shiftl_mul_pow2 by lia; change 64 with (8 * 8); rewrite <- Z.mul_assoc, Z.mul_comm, Z.mod_mul by lia; reflexivity).
destruct (shad_inside f (fs_size k) A 48 ltac:(clear - F64; Z.div_mod_to_equations; lia) A8 FS8 eq_refl ltac:(lia) FA1 ltac:(lia) ltac:(lia)) as (SHA1 & SHA2). change (48 / 8) with 6 in SHA2.
assert (BSA : shad A + 6 <= lo) by lia.
pose proof (af_client_consts RT AF Σ m ART0) as CC0.
pose proof (pres_fp_refl (rt_live RT Σ) (rt_frames RT Σ) usp [(A, A + 48)] m) as PF.
pose proof (fun a => aclient_split RT AF Σ m usp a ART0) as SPL.
cps_norm.

cps_seg (bits_init_w1 A usp lo).
destruct POST as (m1 & j0 & -> & MU1 & WM1 & MI1 & ST1 & FR1). cps_seg_post.

assert (EU32 : bv_unsigned (Z_to_bv 64 (usp + -32)) = usp + -32) by (apply unsigned_lit; ulc).
cps_rt CAL.
{ cps_callok. }
{ apply unwind_ok_ch. unfold unwind_ok, RA_bits_init_calloc. rewrite EU32, !unsigned_lit by ulc.
split; [unfold ALLOC_RAS; cbn [In]; repeat (first [left; reflexivity | right])| left; ulc]. }
intros c2 (Σ1 & D & Hc2 & LV1 & FRS1 & SP1 & CR1 & DPOS & D16 & DTOP & PO1).
change (2000 * 1) with 2000 in *. change (mcost 2000) with 0 in CR1. rewrite Z.sub_0_r in CR1. change (Z.to_nat 2000) with 2000%nat in *.
cps_unpack Hc2 as (m2 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2 & WRD & ACD & BYD).
pose proof (fun a Ha => newchunk_apart RT AF Σ Σ1 m2 D 2000 usp a ART2 LV1 FRS1 SP1 ltac:(ulc) ltac:(lia) Ha) as NAD.
cps_sigma LV1 FRS1 SP1.
destruct (live_below_lo RT AF Σ1 m2 D 2000 lo ART2 INL LOW) as (_ & BD1 & _).
destruct (frame_live_apart RT AF Σ1 m2 f k D 2000 ART2 INF INL) as (FLA1 & FLA2). rewrite SHF1 in FLA2.
pose proof (live_facts RT AF Σ1 m2 D 2000 ART2 INL) as (_ & _ & _ & DHI).
assert (BLK : rw_cells asegs m2 D [CB 2000 (repeat z8 2000)]).
{ split; [split; [split; [vm_compute; reflexivity| exact I]| cbn [cells_bytes cbytes app]; rewrite app_nil_r; exact BYD]| exact WRD]. }
assert (OBA : aobj asegs m2 A BITS_SIZEOF) by (split; [ulc|]; split; [unfold BITS_SIZEOF; ulc|]; apply bits_shadow_acc; [exact SHC| exact A8| ulc]).
assert (OBD : aobj asegs m2 D 2000) by (split; [lia|]; split; [ulc| exact ACD]).
cps_norm.

cps_seg (bits_init_w2 A D usp lo).
{ unfold BITS_SIZEOF; ulc. } { unfold BITS_SIZEOF; ulc. } { unfold BITS_SIZEOF; ulc. }
destruct POST as (m3 & a0' & a1' & a2' & -> & MU3 & WM3 & MI3 & ST3 & REP3 & OK3).
clear OBJ BLK FR1 OBA OBD. cps_seg_post.
apply Hk. exists Σ1, D. split; [| repeat split; congruence].
eapply ASTA_conseq; [eassumption|]. intros ms <-. exists a0', m3.
split; [rewrite ESP; unfold ret_stL; do 16 eexists; split; [reflexivity| split; reflexivity]|].
split. { split; [assumption|]. split; [exact MI3|]. split; [cps_wmono| exact ST3]. }
split; [exact PF|]. split; [exact REP3|]. unfold bits_shadow. cbn [map repeat]. exact SHC.
Qed.

Hypothesis FRE : free_contract RT.

Definition speex_bits_destroy_cps : Prop :=
forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
F fc (m : mem) (A D f lo : Z) (k : nat) (b : bits_st unit),
fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 A -> tp = Z_to_bv 64 0x630458 ->
bits_rep asegs m A D b -> bits_ok b -> sb_owner b = 1 -> ro_cells asegs m (shad A) bits_shadow ->
In (f, k) (rt_frames RT Σ) -> f <= A -> A + 48 <= f + fs_size k - 8 ->
In (D, sb_buf_size b) (rt_live RT Σ) ->
ART RT Σ m -> mem_inv asegs m ->
stk asegs m lo (bv_unsigned sp) -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + RT_STACK + 16 <= bv_unsigned sp ->
bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 ->
unwind_ch m ra s0 sp ->
cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
t3 t4 t5 t6 F fc A_speex_bits_destroy m)))
(fun c => exists (Σ' : rts RT),
ASTA RT Σ' PMc (fun ms => exists v m',
ret_stL (fun F' fc' => F' = F /\ fc' = fc) ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v m' ms
/\ rt_after_f RT Σ' (bv_unsigned sp) lo m m'
/\ rt_pres_fp (rt_live RT Σ') (rt_frames RT Σ) (bv_unsigned sp) [] m m') c
/\ rt_live RT Σ' = live_remove D (rt_live RT Σ) /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
/\ rt_credit RT Σ' = rt_credit RT Σ /\ rt_pois RT Σ' = rt_pois RT Σ).

Theorem speex_bits_destroy_ok : speex_bits_destroy_cps.
Proof using AF FRE.
intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m A D f lo k b
FDO MST -> -> REP OK OWN SHC INF FA1 FA2 INL ART0 MI0 ST0 LOW LOR SPT SPA UNW.
intros T c Hc Hk.
set (usp := bv_unsigned sp) in *.
assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned).
unfold entry_st in Hc. rewrite ESP in Hc.
unfold bits_shadow in SHC. cbn [map repeat] in SHC.
destruct (frame_below_lo RT AF Σ m f k lo ART0 INF LOW) as (BF1 & BF2 & BF3).
destruct (live_below_lo RT AF Σ m D (sb_buf_size b) lo ART0 INL LOW) as (BD0 & BD1 & _).
pose proof (frame_facts RT AF Σ m f k ART0 INF) as (F0 & F64 & FIMG & _ & _ & _ & _ & _ & _ & _).
assert (FSZ : 0 <= fs_size k) by (unfold fs_size; apply Z.shiftl_nonneg; lia).
pose proof REP as (_ & _ & (A8 & _)).
pose proof (af_client_consts RT AF Σ m ART0) as CC0.
pose proof (fun a => aclient_split RT AF Σ m usp a ART0) as SPL.
assert (OBA : aobj asegs m A BITS_SIZEOF) by (split; [ulc|]; split; [unfold BITS_SIZEOF; ulc|]; apply bits_shadow_acc; [exact SHC| exact A8| ulc]).
cps_norm.

cps_seg (bits_destroy_w1 A D usp lo b).
{ unfold BITS_SIZEOF; ulc. }
destruct POST as (m1 & a1' & a2' & a3' & -> & MU1 & WM1 & MI1 & ST1 & REP1).
assert (UNW1 : unwind_ch m1 ra s0 (Z_to_bv 64 usp)).
{ rewrite <- ESP. apply (unwind_ch_transport [(usp + -16, usp)] m m1 ra s0 sp); [| exact MU1| exact WM1| exact UNW].
intros a Ha. cbn [disjoint_from]. fold usp in Ha. split; [lia| exact I]. }
cps_seg_post.

cps_rt FRE. { cps_callok. }
intros c2 (Σ1 & v & Hc2 & LV1 & FRS1 & SP1 & CR1 & PO1).
cps_unpack Hc2 as (m2 & RS2 & (ART2 & MI2 & ST2) & PRES2).
apply Hk. exists Σ1. split; [| repeat split; assumption].
eapply ASTA_conseq; [eassumption|]. intros ms <-. exists v, m2.
split; [rewrite ESP; unfold ret_stL; do 16 eexists; split; [reflexivity| split; reflexivity]|].
split; [exact (conj ART2 (conj MI2 ST2))|].
intros a Ha Ho. rewrite (PRES2 a); [| exact Ha].
apply MU1. cbn [outside]. split; [| exact I].
assert (Ha' : aclient (rt_live RT Σ) (rt_frames RT Σ) usp (bv_unsigned a)).
{ apply (aclient_mono _ _ _ _ _ _ _ Ha); [| auto| lia]. intros e He. rewrite LV1 in He. exact (live_remove_sub _ _ _ He). }
clear - SPL Ha' LOW LOR. specialize (SPL _ Ha'). lia.
Qed.
End BitsCPS.
