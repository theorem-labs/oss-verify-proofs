(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS Require Import X0mx X0k2.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1da X1dg X1cg.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1qz X1r8.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0bp X0j9 X0ec X001 X00b X04b X07z X05o X05p X05s
X0ae X09p X09n.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X12c X14x X0r0 X0ra X0v9 X0wl X110 X10c X10a.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14x OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0r0 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ra OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0v9 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0wl OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X110 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X10c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X10a.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma sync_clear_prun : forall (sy : sync_st unit) q r q', prun (ogg_sync_clear (St := pst) p_free sy) q = Some (r, q') -> r = ogg_sync_init /\ q' = q.
Proof.
intros sy q r q' H. unfold ogg_sync_clear in H. destruct (sy_data sy) as [p|].
- rewrite prun_bind, prun_free in H. cbn beta iota in H. rewrite prun_ret in H. injection H as <- <-. split; reflexivity.
- rewrite prun_ret in H. injection H as <- <-. split; reflexivity.
Qed.

Section OggClearCPS.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis FRE : free_contract RT.

Definition sync_clear_live (sy : sync_st bptr) (D : Z) (live : list (Z * Z)) : list (Z * Z) :=
match sy_data sy with Some _ => live_remove D live | None => live end.

Definition ogg_sync_clear_cps : Prop :=
forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
F fc (m : mem) (A D f lo : Z) (k : nat) (sy : sync_st bptr) (bytes : list byte),
fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 A -> tp = Z_to_bv 64 0x638c98 ->
sync_rep m A D sy bytes -> 0 < A ->
(sy_data sy <> None -> In (D, sy_storage sy) (rt_live RT Σ)) ->
In (f, k) (rt_frames RT Σ) -> f <= A -> A + 32 <= f + fs_size k - 8 ->
ART RT Σ m -> mem_inv bsegs m ->
stk bsegs m lo (bv_unsigned sp) -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + RT_STACK + 16 <= bv_unsigned sp ->
bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 ->
cps bsegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
t3 t4 t5 t6 F fc A_ogg_sync_clear m)))
(fun c => exists (Σ' : rts RT),
ASTA RT Σ' PMc (fun ms => exists m',
ret_stL (fun F' fc' => F' = F /\ fc' = fc) ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 0) m' ms
/\ rt_after_f RT Σ' (bv_unsigned sp) lo m m'
/\ rt_pres_fp (sync_clear_live sy D (rt_live RT Σ)) (rt_frames RT Σ) (bv_unsigned sp) [(A, A + 32)] m m'
/\ sync_rep m' A 0 ogg_sync_init []) c
/\ rt_live RT Σ' = sync_clear_live sy D (rt_live RT Σ) /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
/\ rt_credit RT Σ' = rt_credit RT Σ /\ rt_pois RT Σ' = rt_pois RT Σ).

Lemma sync_rep_cleared : forall (m : mem) A, 0 < A -> rw_cells bsegs m A (sync_cells 0 ogg_sync_init) -> sync_rep m A 0 ogg_sync_init [].
Proof.
intros m A A0 H. split; [exact H|]. split; [unfold sync_fields_ok, int31; cbn; lia|].
split; [cbn; repeat split; reflexivity| cbn; lia].
Qed.

Theorem ogg_sync_clear_ok : ogg_sync_clear_cps.
Proof using AF FRE.
intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m A D f lo k sy bytes
FDO MST -> -> REP A0 INL INF FA1 FA2 ART0 MI0 ST0 LOW LOR SPT SPA.
intros T c Hc Hk.
set (usp := bv_unsigned sp) in *.
assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned).
unfold entry_st in Hc. rewrite ESP in Hc.
destruct (frame_below_lo RT AF Σ m f k lo ART0 INF LOW) as (BF1 & BF2 & BF3).
pose proof (frame_facts RT AF Σ m f k ART0 INF) as (F0 & F64 & FIMG & _ & _ & _ & _ & _ & _ & _).
assert (FSZ : 0 <= fs_size k) by (unfold fs_size; apply Z.shiftl_nonneg; lia).
assert (LOU : rt_sp0 RT Σ - STACK_WIN <= usp) by (clear - LOW LOR; unfold RT_STACK in *; lia).
destruct REP as (SY & FOK & DAT & SEP). unfold sync_cells in SY.
unfold sync_data in DAT. unfold sync_clear_live in *.
destruct (sy_data sy) as [p|] eqn:ED.
-
destruct DAT as (D0 & ARR & LEN & _ & _).
specialize (INL ltac:(intros X; discriminate X)).
destruct (live_below_lo RT AF Σ m D (sy_storage sy) lo ART0 INL LOW) as (BD0 & BD1 & _).
assert (DR : 0 < D < 2^64) by (pose proof FOK as ((S0 & _) & _); clear - BD0 BD1 S0 LOR SPT; unfold RT_STACK, USTACK_TOP in *; lia).
pose proof (pres_fp_refl (live_remove D (rt_live RT Σ)) (rt_frames RT Σ) usp [(A, A + 32)] m) as PF.
assert (SPL : forall a, aclient (live_remove D (rt_live RT Σ)) (rt_frames RT Σ) usp a -> usp <= a \/ a < rt_sp0 RT Σ - STACK_WIN).
{ intros a Ha. apply (aclient_split RT AF Σ m usp a ART0). apply (aclient_mono _ _ _ _ _ _ _ Ha); [apply live_remove_sub| auto| apply Z.le_refl]. }
cps_norm.
cps_seg (sync_clear_w1 A D usp lo sy).
destruct POST as (m1 & -> & MU1 & WM1 & MI1 & ST1 & FR1).
clear ARR. cps_seg_post.
assert (EU : bv_unsigned (Z_to_bv 64 (usp + -16)) = usp + -16) by (apply unsigned_lit; ulc).
cps_rt FRE. { cps_callok. }
{ apply unwind_ok_ch. unfold unwind_ok, RA_sync_clear_free. rewrite EU, !unsigned_lit by ulc.
split; [unfold ALLOC_RAS; cbn [In]; repeat (first [left; reflexivity | right])| left; ulc]. }
intros c2 (Σ1 & v & Hc2 & LV1 & FRS1 & SP1 & CR1 & PO1).
cps_unpack Hc2 as (m2 & RS2 & (ART2 & MI2 & ST2) & PRES2).
ogg_sigma_free FRS1 SP1.
cps_seg (sync_clear_w2 A D usp lo sy).
destruct POST as (m3 & -> & MU3 & WM3 & MI3 & ST3 & SY3).
clear FR1. cps_seg_post.
apply Hk. exists Σ1. split; [| repeat split; assumption].
eapply ASTA_conseq; [eassumption|]. intros ms <-. exists m3.
split; [rewrite ESP; unfold ret_stL; do 16 eexists; split; [reflexivity| split; reflexivity]|].
split; [exact (conj ART (conj MI3 ST3))|].
split; [exact PF| apply sync_rep_cleared; assumption].
-
destruct DAT as (-> & _).
pose proof (pres_fp_refl (rt_live RT Σ) (rt_frames RT Σ) usp [(A, A + 32)] m) as PF.
pose proof (fun a => aclient_split RT AF Σ m usp a ART0) as SPL.
cps_norm.
cps_seg (sync_clear_nodata A usp lo sy).
destruct POST as (m1 & -> & MU1 & WM1 & MI1 & ST1 & SY1).
clear SY. cps_seg_post.
apply Hk. exists Σ. split; [| repeat split; reflexivity].
eapply ASTA_conseq; [eassumption|]. intros ms <-. exists m1.
split; [rewrite ESP; unfold ret_stL; do 16 eexists; split; [reflexivity| split; reflexivity]|].
split; [exact (conj ART (conj MI1 ST1))|].
split; [exact PF| apply sync_rep_cleared; assumption].
Qed.

Hypothesis MSET : memset_icontract RT e_memset.

Definition ogg_stream_clear_cps : Prop :=
forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
F fc (m : mem) (A Bd L G f lo : Z) (k : nat) (os : stream_st bptr) (hdr : list byte),
fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 A -> tp = Z_to_bv 64 0x638c98 ->
rw_cells bsegs m A (stream_cells Bd L G hdr os) -> length hdr = 284%nat -> 0 < A -> acc bsegs m A 408 ->
stream_live RT Σ os Bd L G -> 0 <= os_body_storage os -> 0 <= os_lacing_storage os ->
In (f, k) (rt_frames RT Σ) -> f <= A -> A + 408 <= f + fs_size k - 8 ->
ART RT Σ m -> mem_inv bsegs m ->
stk bsegs m lo (bv_unsigned sp) -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + RT_STACK + 16 <= bv_unsigned sp ->
bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 ->
cps bsegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
t3 t4 t5 t6 F fc A_ogg_stream_clear m)))
(fun c => exists (Σ' : rts RT),
ASTA RT Σ' PMc (fun ms => exists m',
ret_stL (fun F' fc' => F' = F /\ fc' = fc) ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 0) m' ms
/\ rt_after_f RT Σ' (bv_unsigned sp) lo m m'
/\ rt_pres_fp (live_remove G (live_remove L (live_remove Bd (rt_live RT Σ)))) (rt_frames RT Σ) (bv_unsigned sp) [(A, A + 408)] m m'
/\ rw_cells bsegs m' A (stream_cells 0 0 0 zero_hdr stream_zero)) c
/\ rt_live RT Σ' = live_remove G (live_remove L (live_remove Bd (rt_live RT Σ))) /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
/\ rt_credit RT Σ' = rt_credit RT Σ /\ rt_pois RT Σ' = rt_pois RT Σ).

Theorem ogg_stream_clear_ok : ogg_stream_clear_cps.
Proof using AF FRE MSET.
intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m A Bd L G f lo k os hdr
FDO MST -> -> OS LH A0 ACC (INB & INLc & ING & NBL & NBG & NLG) SB0 SL0 INF FA1 FA2 ART0 MI0 ST0 LOW LOR SPT SPA.
intros T c Hc Hk.
set (usp := bv_unsigned sp) in *.
assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned).
unfold entry_st in Hc. rewrite ESP in Hc.
destruct (frame_below_lo RT AF Σ m f k lo ART0 INF LOW) as (BF1 & BF2 & BF3).
pose proof (frame_facts RT AF Σ m f k ART0 INF) as (F0 & F64 & FIMG & _ & _ & _ & SHF2 & _ & _ & FSELF).
assert (INF0 : id (In (f, k) (rt_frames RT Σ))) by exact INF.
assert (FSZ : 0 <= fs_size k) by (unfold fs_size; apply Z.shiftl_nonneg; lia).
assert (LOU : rt_sp0 RT Σ - STACK_WIN <= usp) by (clear - LOW LOR; unfold RT_STACK in *; lia).
destruct (live_below_lo RT AF Σ m Bd _ lo ART0 INB LOW) as (BB0 & BB1 & _).
destruct (live_below_lo RT AF Σ m L _ lo ART0 INLc LOW) as (BL0 & BL1 & _).
destruct (live_below_lo RT AF Σ m G _ lo ART0 ING LOW) as (BG0 & BG1 & _).
assert (BR : 0 < Bd < 2^64) by (clear - BB0 BB1 SB0 LOR SPT; unfold RT_STACK, USTACK_TOP in *; lia).
assert (LR : 0 < L < 2^64) by (clear - BL0 BL1 SL0 LOR SPT; unfold RT_STACK, USTACK_TOP in *; lia).
assert (GR : 0 < G < 2^64) by (clear - BG0 BG1 SL0 LOR SPT; unfold RT_STACK, USTACK_TOP in *; lia).
set (LV3 := live_remove G (live_remove L (live_remove Bd (rt_live RT Σ)))) in *.
assert (SUB3 : forall e, In e LV3 -> In e (rt_live RT Σ)) by (intros e He; unfold LV3 in He; do 3 apply live_remove_sub in He; exact He).
pose proof (pres_fp_refl LV3 (rt_frames RT Σ) usp [(A, A + 408)] m) as PF.
assert (SPL : forall a, aclient LV3 (rt_frames RT Σ) usp a -> usp <= a \/ a < rt_sp0 RT Σ - STACK_WIN).
{ intros a Ha. apply (aclient_split RT AF Σ m usp a ART0). apply (aclient_mono _ _ _ _ _ _ _ Ha); [exact SUB3| auto| apply Z.le_refl]. }
unfold stream_cells in OS.
cps_norm.

cps_seg (stream_clear_w1 A Bd L G usp lo hdr os).
destruct POST as (m1 & -> & MU1 & WM1 & MI1 & ST1 & FR1).
cps_seg_post.
assert (EU : bv_unsigned (Z_to_bv 64 (usp + -16)) = usp + -16) by (apply unsigned_lit; ulc).
cps_rt FRE. { cps_callok. }
{ apply unwind_ok_ch. unfold unwind_ok, RA_stream_clear_free1. rewrite EU, !unsigned_lit by ulc.
split; [unfold ALLOC_RAS; cbn [In]; repeat (first [left; reflexivity | right])| left; ulc]. }
intros kc2 (Σ1 & v1 & Hc2 & LV1 & FRS1 & SP1 & CR1 & PO1).
assert (SUB1 : forall e, In e LV3 -> In e (rt_live RT Σ1)) by (intros e He; rewrite LV1; unfold LV3 in He; do 2 apply live_remove_sub in He; exact He).
assert (INL1 : In (L, 4 * os_lacing_storage os) (rt_live RT Σ1)) by (rewrite LV1; apply live_remove_keep; [exact INLc| cbn [fst]; congruence]).
assert (ING1 : In (G, 8 * os_lacing_storage os) (rt_live RT Σ1)) by (rewrite LV1; apply live_remove_keep; [exact ING| cbn [fst]; congruence]).
cps_unpack Hc2 as (m2 & RS2 & (ART2 & MI2 & ST2) & PRES2).
ogg_sigma_free FRS1 SP1.

cps_seg (stream_clear_w2 A Bd L G hdr os).
subst ms.
cps_rt FRE. { cps_callok. }
{ apply unwind_ok_ch. unfold unwind_ok, RA_stream_clear_free2. rewrite EU, !unsigned_lit by ulc.
split; [unfold ALLOC_RAS; cbn [In]; repeat (first [left; reflexivity | right])| left; ulc]. }
intros kc3 (Σ2 & v2 & Hc3 & LV2 & FRS2 & SP2 & CR2 & PO2).
assert (SUB2 : forall e, In e LV3 -> In e (rt_live RT Σ2)) by (intros e He; rewrite LV2, LV1; unfold LV3 in He; apply live_remove_sub in He; exact He).
assert (ING2 : In (G, 8 * os_lacing_storage os) (rt_live RT Σ2)) by (rewrite LV2; apply live_remove_keep; [exact ING1| cbn [fst]; congruence]).
cps_unpack Hc3 as (m3 & RS3 & (ART3 & MI3 & ST3) & PRES3).
ogg_sigma_free FRS2 SP2.

cps_seg (stream_clear_w3 A Bd L G hdr os).
subst ms.
cps_rt FRE. { cps_callok. }
{ apply unwind_ok_ch. unfold unwind_ok, RA_stream_clear_free3. rewrite EU, !unsigned_lit by ulc.
split; [unfold ALLOC_RAS; cbn [In]; repeat (first [left; reflexivity | right])| left; ulc]. }
intros kc4 (Σ3 & v3 & Hc4 & LV3' & FRS3 & SP3 & CR3 & PO3).
assert (SUB3' : forall e, In e LV3 -> In e (rt_live RT Σ3)) by (intros e He; rewrite LV3', LV2, LV1; exact He).
cps_unpack Hc4 as (m4 & RS4 & (ART4 & MI4 & ST4) & PRES4).
ogg_sigma_free FRS3 SP3.

cps_seg (stream_clear_w4 A).
subst ms.
pose proof (proj2 OS) as WR4. cbn [cells_size csize Nat.add] in WR4. change (Z.of_nat 408) with 408 in WR4.
assert (ACC4 : acc bsegs m4 A 408).
{ apply (acc_frame_pres_fp LV3 (rt_frames RT Σ) usp [(A, A + 408)] m m4 f k A 408 PF INF0);
[clear - F64; Z.div_mod_to_equations; lia| apply fs_size_mod8| lia| exact FA1| lia| | exact ACC].
intros x Hx. cbn [outside]. split; [| exact I]. rewrite SHF2 in Hx. clear - Hx FSELF FA1 FA2. lia. }
cps_rt (MSET Σ3 PMc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m4 A 408 (Z_to_bv 8 0) lo).
{ clear - A0 FA2 BF1 LOR SPT; lia. }
{ apply (frame_checked_dst RT Σ3 m4 _ f k A 408); [exact INF| exact FA1| exact FA2| exact ACC4| exact WR4]. }
{ cps_callok. }
intros kc5 Hc5. unfold icpt_postF in Hc5.
cps_unpack Hc5 as (m5 & RS5 & (ART5 & MI5 & WM5 & ST5) & PRES5 & BY5).
change (Z.to_nat 408) with 408%nat in BY5.
pose proof (ogg_ms_piece m4 m5 A 408 _ WR4 WM5 BY5) as OSZ. clear BY5.

cps_seg (stream_clear_w5 A usp lo).
destruct POST as (m6 & -> & MU6 & WM6 & MI6 & ST6).
clear FR1. cps_seg_post.
apply Hk. exists Σ3. split; [| split; [rewrite LV3', LV2, LV1; reflexivity| repeat split; congruence]].
eapply ASTA_conseq; [eassumption|]. intros ms <-. exists m6.
split; [rewrite ESP; unfold ret_stL; do 16 eexists; split; [reflexivity| split; reflexivity]|].
split; [exact (conj ART (conj MI6 ST6))|].
split; [exact PF| apply stream_cells_zero; exact OSZ].
Qed.

Definition ogg_stream_clear_null_cps : Prop :=
forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
F fc (m : mem) (A f lo : Z) (k : nat) (os : stream_st bptr) (hdr : list byte),
fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 A -> tp = Z_to_bv 64 0x638c98 ->
rw_cells bsegs m A (stream_cells 0 0 0 hdr os) -> length hdr = 284%nat -> 0 < A -> acc bsegs m A 408 ->
In (f, k) (rt_frames RT Σ) -> f <= A -> A + 408 <= f + fs_size k - 8 ->
ART RT Σ m -> mem_inv bsegs m ->
stk bsegs m lo (bv_unsigned sp) -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + RT_STACK + 16 <= bv_unsigned sp ->
bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 ->
cps bsegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
t3 t4 t5 t6 F fc A_ogg_stream_clear m)))
(fun c => ASTA RT Σ PMc (fun ms => exists m',
ret_stL (fun F' fc' => F' = F /\ fc' = fc) ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 0) m' ms
/\ rt_after RT Σ (bv_unsigned sp) lo m m'
/\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) [(A, A + 408)] m m'
/\ rw_cells bsegs m' A (stream_cells 0 0 0 zero_hdr stream_zero)) c).

Theorem ogg_stream_clear_null_ok : ogg_stream_clear_null_cps.
Proof using AF MSET.
intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m A f lo k os hdr
FDO MST -> -> OS LH A0 ACC INF FA1 FA2 ART0 MI0 ST0 LOW LOR SPT SPA.
intros T c Hc Hk.
set (usp := bv_unsigned sp) in *.
assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned).
unfold entry_st in Hc. rewrite ESP in Hc.
destruct (frame_below_lo RT AF Σ m f k lo ART0 INF LOW) as (BF1 & BF2 & BF3).
pose proof (frame_facts RT AF Σ m f k ART0 INF) as (F0 & F64 & FIMG & _ & _ & _ & SHF2 & _ & _ & FSELF).
assert (FSZ : 0 <= fs_size k) by (unfold fs_size; apply Z.shiftl_nonneg; lia).
pose proof (pres_fp_refl (rt_live RT Σ) (rt_frames RT Σ) usp [(A, A + 408)] m) as PF.
pose proof (fun a => aclient_split RT AF Σ m usp a ART0) as SPL.
unfold stream_cells in OS.
cps_norm.
cps_seg (stream_clear_w1_null A usp lo hdr os).
destruct POST as (m1 & -> & MU1 & WM1 & MI1 & ST1 & FR1).
cps_seg_post.
pose proof (proj2 OS) as WR1. cbn [cells_size csize Nat.add] in WR1. change (Z.of_nat 408) with 408 in WR1.
assert (ACC1 : acc bsegs m1 A 408).
{ apply (acc_frame_pres_fp (rt_live RT Σ) (rt_frames RT Σ) usp [(A, A + 408)] m m1 f k A 408 PF INF);
[clear - F64; Z.div_mod_to_equations; lia| apply fs_size_mod8| lia| exact FA1| lia| | exact ACC].
intros x Hx. cbn [outside]. split; [| exact I]. rewrite SHF2 in Hx. clear - Hx FSELF FA1 FA2. lia. }
cps_rt (MSET Σ PMc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 A 408 (Z_to_bv 8 0) lo).
{ clear - A0 FA2 BF1 LOR SPT; lia. }
{ apply (frame_checked_dst RT Σ m1 _ f k A 408); [exact INF| exact FA1| exact FA2| exact ACC1| exact WR1]. }
{ cps_callok. }
intros kc2 Hc2. unfold icpt_postF in Hc2.
cps_unpack Hc2 as (m2 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2 & BY2).
change (Z.to_nat 408) with 408%nat in BY2.
pose proof (ogg_ms_piece m1 m2 A 408 _ WR1 WM2 BY2) as OSZ. clear BY2.
cps_seg (stream_clear_w5 A usp lo).
destruct POST as (m3 & -> & MU3 & WM3 & MI3 & ST3).
clear FR1. cps_seg_post.
apply Hk.
eapply ASTA_conseq; [eassumption|]. intros ms <-. exists m3.
split; [rewrite ESP; unfold ret_stL; do 16 eexists; split; [reflexivity| split; reflexivity]|].
split. { split; [assumption|]. split; [exact MI3|]. split; [cps_wmono| exact ST3]. }
split; [exact PF| apply stream_cells_zero; exact OSZ].
Qed.
End OggClearCPS.
End B_TWIN.

Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma sync_clear_prun : forall (sy : sync_st unit) q r q', prun (ogg_sync_clear (St := pst) p_free sy) q = Some (r, q') -> r = ogg_sync_init /\ q' = q.
Proof.
intros sy q r q' H. unfold ogg_sync_clear in H. destruct (sy_data sy) as [p|].
- rewrite prun_bind, prun_free in H. cbn beta iota in H. rewrite prun_ret in H. injection H as <- <-. split; reflexivity.
- rewrite prun_ret in H. injection H as <- <-. split; reflexivity.
Qed.

Section OggClearCPS.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis FRE : free_contract RT.

Definition sync_clear_live (sy : sync_st bptr) (D : Z) (live : list (Z * Z)) : list (Z * Z) :=
match sy_data sy with Some _ => live_remove D live | None => live end.

Definition ogg_sync_clear_cps : Prop :=
forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
F fc (m : mem) (A D f lo : Z) (k : nat) (sy : sync_st bptr) (bytes : list byte),
fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 A -> tp = Z_to_bv 64 0x630458 ->
sync_rep m A D sy bytes -> 0 < A ->
(sy_data sy <> None -> In (D, sy_storage sy) (rt_live RT Σ)) ->
In (f, k) (rt_frames RT Σ) -> f <= A -> A + 32 <= f + fs_size k - 8 ->
ART RT Σ m -> mem_inv asegs m ->
stk asegs m lo (bv_unsigned sp) -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + RT_STACK + 16 <= bv_unsigned sp ->
bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 ->
cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
t3 t4 t5 t6 F fc A_ogg_sync_clear m)))
(fun c => exists (Σ' : rts RT),
ASTA RT Σ' PMc (fun ms => exists m',
ret_stL (fun F' fc' => F' = F /\ fc' = fc) ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 0) m' ms
/\ rt_after_f RT Σ' (bv_unsigned sp) lo m m'
/\ rt_pres_fp (sync_clear_live sy D (rt_live RT Σ)) (rt_frames RT Σ) (bv_unsigned sp) [(A, A + 32)] m m'
/\ sync_rep m' A 0 ogg_sync_init []) c
/\ rt_live RT Σ' = sync_clear_live sy D (rt_live RT Σ) /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
/\ rt_credit RT Σ' = rt_credit RT Σ /\ rt_pois RT Σ' = rt_pois RT Σ).

Lemma sync_rep_cleared : forall (m : mem) A, 0 < A -> rw_cells asegs m A (sync_cells 0 ogg_sync_init) -> sync_rep m A 0 ogg_sync_init [].
Proof.
intros m A A0 H. split; [exact H|]. split; [unfold sync_fields_ok, int31; cbn; lia|].
split; [cbn; repeat split; reflexivity| cbn; lia].
Qed.

Theorem ogg_sync_clear_ok : ogg_sync_clear_cps.
Proof using AF FRE.
intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m A D f lo k sy bytes
FDO MST -> -> REP A0 INL INF FA1 FA2 ART0 MI0 ST0 LOW LOR SPT SPA.
intros T c Hc Hk.
set (usp := bv_unsigned sp) in *.
assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned).
unfold entry_st in Hc. rewrite ESP in Hc.
destruct (frame_below_lo RT AF Σ m f k lo ART0 INF LOW) as (BF1 & BF2 & BF3).
pose proof (frame_facts RT AF Σ m f k ART0 INF) as (F0 & F64 & FIMG & _ & _ & _ & _ & _ & _ & _).
assert (FSZ : 0 <= fs_size k) by (unfold fs_size; apply Z.shiftl_nonneg; lia).
assert (LOU : rt_sp0 RT Σ - STACK_WIN <= usp) by (clear - LOW LOR; unfold RT_STACK in *; lia).
destruct REP as (SY & FOK & DAT & SEP). unfold sync_cells in SY.
unfold sync_data in DAT. unfold sync_clear_live in *.
destruct (sy_data sy) as [p|] eqn:ED.
-
destruct DAT as (D0 & ARR & LEN & _ & _).
specialize (INL ltac:(intros X; discriminate X)).
destruct (live_below_lo RT AF Σ m D (sy_storage sy) lo ART0 INL LOW) as (BD0 & BD1 & _).
assert (DR : 0 < D < 2^64) by (pose proof FOK as ((S0 & _) & _); clear - BD0 BD1 S0 LOR SPT; unfold RT_STACK, USTACK_TOP in *; lia).
pose proof (pres_fp_refl (live_remove D (rt_live RT Σ)) (rt_frames RT Σ) usp [(A, A + 32)] m) as PF.
assert (SPL : forall a, aclient (live_remove D (rt_live RT Σ)) (rt_frames RT Σ) usp a -> usp <= a \/ a < rt_sp0 RT Σ - STACK_WIN).
{ intros a Ha. apply (aclient_split RT AF Σ m usp a ART0). apply (aclient_mono _ _ _ _ _ _ _ Ha); [apply live_remove_sub| auto| apply Z.le_refl]. }
cps_norm.
cps_seg (sync_clear_w1 A D usp lo sy).
destruct POST as (m1 & -> & MU1 & WM1 & MI1 & ST1 & FR1).
clear ARR. cps_seg_post.
assert (EU : bv_unsigned (Z_to_bv 64 (usp + -16)) = usp + -16) by (apply unsigned_lit; ulc).
cps_rt FRE. { cps_callok. }
{ apply unwind_ok_ch. unfold unwind_ok, RA_sync_clear_free. rewrite EU, !unsigned_lit by ulc.
split; [unfold ALLOC_RAS; cbn [In]; repeat (first [left; reflexivity | right])| left; ulc]. }
intros c2 (Σ1 & v & Hc2 & LV1 & FRS1 & SP1 & CR1 & PO1).
cps_unpack Hc2 as (m2 & RS2 & (ART2 & MI2 & ST2) & PRES2).
ogg_sigma_free FRS1 SP1.
cps_seg (sync_clear_w2 A D usp lo sy).
destruct POST as (m3 & -> & MU3 & WM3 & MI3 & ST3 & SY3).
clear FR1. cps_seg_post.
apply Hk. exists Σ1. split; [| repeat split; assumption].
eapply ASTA_conseq; [eassumption|]. intros ms <-. exists m3.
split; [rewrite ESP; unfold ret_stL; do 16 eexists; split; [reflexivity| split; reflexivity]|].
split; [exact (conj ART (conj MI3 ST3))|].
split; [exact PF| apply sync_rep_cleared; assumption].
-
destruct DAT as (-> & _).
pose proof (pres_fp_refl (rt_live RT Σ) (rt_frames RT Σ) usp [(A, A + 32)] m) as PF.
pose proof (fun a => aclient_split RT AF Σ m usp a ART0) as SPL.
cps_norm.
cps_seg (sync_clear_nodata A usp lo sy).
destruct POST as (m1 & -> & MU1 & WM1 & MI1 & ST1 & SY1).
clear SY. cps_seg_post.
apply Hk. exists Σ. split; [| repeat split; reflexivity].
eapply ASTA_conseq; [eassumption|]. intros ms <-. exists m1.
split; [rewrite ESP; unfold ret_stL; do 16 eexists; split; [reflexivity| split; reflexivity]|].
split; [exact (conj ART (conj MI1 ST1))|].
split; [exact PF| apply sync_rep_cleared; assumption].
Qed.

Hypothesis MSET : memset_icontract RT e_memset.

Definition ogg_stream_clear_cps : Prop :=
forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
F fc (m : mem) (A Bd L G f lo : Z) (k : nat) (os : stream_st bptr) (hdr : list byte),
fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 A -> tp = Z_to_bv 64 0x630458 ->
rw_cells asegs m A (stream_cells Bd L G hdr os) -> length hdr = 284%nat -> 0 < A -> acc asegs m A 408 ->
stream_live RT Σ os Bd L G -> 0 <= os_body_storage os -> 0 <= os_lacing_storage os ->
In (f, k) (rt_frames RT Σ) -> f <= A -> A + 408 <= f + fs_size k - 8 ->
ART RT Σ m -> mem_inv asegs m ->
stk asegs m lo (bv_unsigned sp) -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + RT_STACK + 16 <= bv_unsigned sp ->
bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 ->
cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
t3 t4 t5 t6 F fc A_ogg_stream_clear m)))
(fun c => exists (Σ' : rts RT),
ASTA RT Σ' PMc (fun ms => exists m',
ret_stL (fun F' fc' => F' = F /\ fc' = fc) ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 0) m' ms
/\ rt_after_f RT Σ' (bv_unsigned sp) lo m m'
/\ rt_pres_fp (live_remove G (live_remove L (live_remove Bd (rt_live RT Σ)))) (rt_frames RT Σ) (bv_unsigned sp) [(A, A + 408)] m m'
/\ rw_cells asegs m' A (stream_cells 0 0 0 zero_hdr stream_zero)) c
/\ rt_live RT Σ' = live_remove G (live_remove L (live_remove Bd (rt_live RT Σ))) /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
/\ rt_credit RT Σ' = rt_credit RT Σ /\ rt_pois RT Σ' = rt_pois RT Σ).

Theorem ogg_stream_clear_ok : ogg_stream_clear_cps.
Proof using AF FRE MSET.
intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m A Bd L G f lo k os hdr
FDO MST -> -> OS LH A0 ACC (INB & INLc & ING & NBL & NBG & NLG) SB0 SL0 INF FA1 FA2 ART0 MI0 ST0 LOW LOR SPT SPA.
intros T c Hc Hk.
set (usp := bv_unsigned sp) in *.
assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned).
unfold entry_st in Hc. rewrite ESP in Hc.
destruct (frame_below_lo RT AF Σ m f k lo ART0 INF LOW) as (BF1 & BF2 & BF3).
pose proof (frame_facts RT AF Σ m f k ART0 INF) as (F0 & F64 & FIMG & _ & _ & _ & SHF2 & _ & _ & FSELF).
assert (INF0 : id (In (f, k) (rt_frames RT Σ))) by exact INF.
assert (FSZ : 0 <= fs_size k) by (unfold fs_size; apply Z.shiftl_nonneg; lia).
assert (LOU : rt_sp0 RT Σ - STACK_WIN <= usp) by (clear - LOW LOR; unfold RT_STACK in *; lia).
destruct (live_below_lo RT AF Σ m Bd _ lo ART0 INB LOW) as (BB0 & BB1 & _).
destruct (live_below_lo RT AF Σ m L _ lo ART0 INLc LOW) as (BL0 & BL1 & _).
destruct (live_below_lo RT AF Σ m G _ lo ART0 ING LOW) as (BG0 & BG1 & _).
assert (BR : 0 < Bd < 2^64) by (clear - BB0 BB1 SB0 LOR SPT; unfold RT_STACK, USTACK_TOP in *; lia).
assert (LR : 0 < L < 2^64) by (clear - BL0 BL1 SL0 LOR SPT; unfold RT_STACK, USTACK_TOP in *; lia).
assert (GR : 0 < G < 2^64) by (clear - BG0 BG1 SL0 LOR SPT; unfold RT_STACK, USTACK_TOP in *; lia).
set (LV3 := live_remove G (live_remove L (live_remove Bd (rt_live RT Σ)))) in *.
assert (SUB3 : forall e, In e LV3 -> In e (rt_live RT Σ)) by (intros e He; unfold LV3 in He; do 3 apply live_remove_sub in He; exact He).
pose proof (pres_fp_refl LV3 (rt_frames RT Σ) usp [(A, A + 408)] m) as PF.
assert (SPL : forall a, aclient LV3 (rt_frames RT Σ) usp a -> usp <= a \/ a < rt_sp0 RT Σ - STACK_WIN).
{ intros a Ha. apply (aclient_split RT AF Σ m usp a ART0). apply (aclient_mono _ _ _ _ _ _ _ Ha); [exact SUB3| auto| apply Z.le_refl]. }
unfold stream_cells in OS.
cps_norm.

cps_seg (stream_clear_w1 A Bd L G usp lo hdr os).
destruct POST as (m1 & -> & MU1 & WM1 & MI1 & ST1 & FR1).
cps_seg_post.
assert (EU : bv_unsigned (Z_to_bv 64 (usp + -16)) = usp + -16) by (apply unsigned_lit; ulc).
cps_rt FRE. { cps_callok. }
{ apply unwind_ok_ch. unfold unwind_ok, RA_stream_clear_free1. rewrite EU, !unsigned_lit by ulc.
split; [unfold ALLOC_RAS; cbn [In]; repeat (first [left; reflexivity | right])| left; ulc]. }
intros kc2 (Σ1 & v1 & Hc2 & LV1 & FRS1 & SP1 & CR1 & PO1).
assert (SUB1 : forall e, In e LV3 -> In e (rt_live RT Σ1)) by (intros e He; rewrite LV1; unfold LV3 in He; do 2 apply live_remove_sub in He; exact He).
assert (INL1 : In (L, 4 * os_lacing_storage os) (rt_live RT Σ1)) by (rewrite LV1; apply live_remove_keep; [exact INLc| cbn [fst]; congruence]).
assert (ING1 : In (G, 8 * os_lacing_storage os) (rt_live RT Σ1)) by (rewrite LV1; apply live_remove_keep; [exact ING| cbn [fst]; congruence]).
cps_unpack Hc2 as (m2 & RS2 & (ART2 & MI2 & ST2) & PRES2).
ogg_sigma_free FRS1 SP1.

cps_seg (stream_clear_w2 A Bd L G hdr os).
subst ms.
cps_rt FRE. { cps_callok. }
{ apply unwind_ok_ch. unfold unwind_ok, RA_stream_clear_free2. rewrite EU, !unsigned_lit by ulc.
split; [unfold ALLOC_RAS; cbn [In]; repeat (first [left; reflexivity | right])| left; ulc]. }
intros kc3 (Σ2 & v2 & Hc3 & LV2 & FRS2 & SP2 & CR2 & PO2).
assert (SUB2 : forall e, In e LV3 -> In e (rt_live RT Σ2)) by (intros e He; rewrite LV2, LV1; unfold LV3 in He; apply live_remove_sub in He; exact He).
assert (ING2 : In (G, 8 * os_lacing_storage os) (rt_live RT Σ2)) by (rewrite LV2; apply live_remove_keep; [exact ING1| cbn [fst]; congruence]).
cps_unpack Hc3 as (m3 & RS3 & (ART3 & MI3 & ST3) & PRES3).
ogg_sigma_free FRS2 SP2.

cps_seg (stream_clear_w3 A Bd L G hdr os).
subst ms.
cps_rt FRE. { cps_callok. }
{ apply unwind_ok_ch. unfold unwind_ok, RA_stream_clear_free3. rewrite EU, !unsigned_lit by ulc.
split; [unfold ALLOC_RAS; cbn [In]; repeat (first [left; reflexivity | right])| left; ulc]. }
intros kc4 (Σ3 & v3 & Hc4 & LV3' & FRS3 & SP3 & CR3 & PO3).
assert (SUB3' : forall e, In e LV3 -> In e (rt_live RT Σ3)) by (intros e He; rewrite LV3', LV2, LV1; exact He).
cps_unpack Hc4 as (m4 & RS4 & (ART4 & MI4 & ST4) & PRES4).
ogg_sigma_free FRS3 SP3.

cps_seg (stream_clear_w4 A).
subst ms.
pose proof (proj2 OS) as WR4. cbn [cells_size csize Nat.add] in WR4. change (Z.of_nat 408) with 408 in WR4.
assert (ACC4 : acc asegs m4 A 408).
{ apply (acc_frame_pres_fp LV3 (rt_frames RT Σ) usp [(A, A + 408)] m m4 f k A 408 PF INF0);
[clear - F64; Z.div_mod_to_equations; lia| apply fs_size_mod8| lia| exact FA1| lia| | exact ACC].
intros x Hx. cbn [outside]. split; [| exact I]. rewrite SHF2 in Hx. clear - Hx FSELF FA1 FA2. lia. }
cps_rt (MSET Σ3 PMc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m4 A 408 (Z_to_bv 8 0) lo).
{ clear - A0 FA2 BF1 LOR SPT; lia. }
{ apply (frame_checked_dst RT Σ3 m4 _ f k A 408); [exact INF| exact FA1| exact FA2| exact ACC4| exact WR4]. }
{ cps_callok. }
intros kc5 Hc5. unfold icpt_postF in Hc5.
cps_unpack Hc5 as (m5 & RS5 & (ART5 & MI5 & WM5 & ST5) & PRES5 & BY5).
change (Z.to_nat 408) with 408%nat in BY5.
pose proof (ogg_ms_piece m4 m5 A 408 _ WR4 WM5 BY5) as OSZ. clear BY5.

cps_seg (stream_clear_w5 A usp lo).
destruct POST as (m6 & -> & MU6 & WM6 & MI6 & ST6).
clear FR1. cps_seg_post.
apply Hk. exists Σ3. split; [| split; [rewrite LV3', LV2, LV1; reflexivity| repeat split; congruence]].
eapply ASTA_conseq; [eassumption|]. intros ms <-. exists m6.
split; [rewrite ESP; unfold ret_stL; do 16 eexists; split; [reflexivity| split; reflexivity]|].
split; [exact (conj ART (conj MI6 ST6))|].
split; [exact PF| apply stream_cells_zero; exact OSZ].
Qed.

Definition ogg_stream_clear_null_cps : Prop :=
forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
F fc (m : mem) (A f lo : Z) (k : nat) (os : stream_st bptr) (hdr : list byte),
fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 A -> tp = Z_to_bv 64 0x630458 ->
rw_cells asegs m A (stream_cells 0 0 0 hdr os) -> length hdr = 284%nat -> 0 < A -> acc asegs m A 408 ->
In (f, k) (rt_frames RT Σ) -> f <= A -> A + 408 <= f + fs_size k - 8 ->
ART RT Σ m -> mem_inv asegs m ->
stk asegs m lo (bv_unsigned sp) -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + RT_STACK + 16 <= bv_unsigned sp ->
bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 ->
cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
t3 t4 t5 t6 F fc A_ogg_stream_clear m)))
(fun c => ASTA RT Σ PMc (fun ms => exists m',
ret_stL (fun F' fc' => F' = F /\ fc' = fc) ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 0) m' ms
/\ rt_after RT Σ (bv_unsigned sp) lo m m'
/\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) [(A, A + 408)] m m'
/\ rw_cells asegs m' A (stream_cells 0 0 0 zero_hdr stream_zero)) c).

Theorem ogg_stream_clear_null_ok : ogg_stream_clear_null_cps.
Proof using AF MSET.
intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m A f lo k os hdr
FDO MST -> -> OS LH A0 ACC INF FA1 FA2 ART0 MI0 ST0 LOW LOR SPT SPA.
intros T c Hc Hk.
set (usp := bv_unsigned sp) in *.
assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned).
unfold entry_st in Hc. rewrite ESP in Hc.
destruct (frame_below_lo RT AF Σ m f k lo ART0 INF LOW) as (BF1 & BF2 & BF3).
pose proof (frame_facts RT AF Σ m f k ART0 INF) as (F0 & F64 & FIMG & _ & _ & _ & SHF2 & _ & _ & FSELF).
assert (FSZ : 0 <= fs_size k) by (unfold fs_size; apply Z.shiftl_nonneg; lia).
pose proof (pres_fp_refl (rt_live RT Σ) (rt_frames RT Σ) usp [(A, A + 408)] m) as PF.
pose proof (fun a => aclient_split RT AF Σ m usp a ART0) as SPL.
unfold stream_cells in OS.
cps_norm.
cps_seg (stream_clear_w1_null A usp lo hdr os).
destruct POST as (m1 & -> & MU1 & WM1 & MI1 & ST1 & FR1).
cps_seg_post.
pose proof (proj2 OS) as WR1. cbn [cells_size csize Nat.add] in WR1. change (Z.of_nat 408) with 408 in WR1.
assert (ACC1 : acc asegs m1 A 408).
{ apply (acc_frame_pres_fp (rt_live RT Σ) (rt_frames RT Σ) usp [(A, A + 408)] m m1 f k A 408 PF INF);
[clear - F64; Z.div_mod_to_equations; lia| apply fs_size_mod8| lia| exact FA1| lia| | exact ACC].
intros x Hx. cbn [outside]. split; [| exact I]. rewrite SHF2 in Hx. clear - Hx FSELF FA1 FA2. lia. }
cps_rt (MSET Σ PMc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 A 408 (Z_to_bv 8 0) lo).
{ clear - A0 FA2 BF1 LOR SPT; lia. }
{ apply (frame_checked_dst RT Σ m1 _ f k A 408); [exact INF| exact FA1| exact FA2| exact ACC1| exact WR1]. }
{ cps_callok. }
intros kc2 Hc2. unfold icpt_postF in Hc2.
cps_unpack Hc2 as (m2 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2 & BY2).
change (Z.to_nat 408) with 408%nat in BY2.
pose proof (ogg_ms_piece m1 m2 A 408 _ WR1 WM2 BY2) as OSZ. clear BY2.
cps_seg (stream_clear_w5 A usp lo).
destruct POST as (m3 & -> & MU3 & WM3 & MI3 & ST3).
clear FR1. cps_seg_post.
apply Hk.
eapply ASTA_conseq; [eassumption|]. intros ms <-. exists m3.
split; [rewrite ESP; unfold ret_stL; do 16 eexists; split; [reflexivity| split; reflexivity]|].
split. { split; [assumption|]. split; [exact MI3|]. split; [cps_wmono| exact ST3]. }
split; [exact PF| apply stream_cells_zero; exact OSZ].
Qed.
End OggClearCPS.
