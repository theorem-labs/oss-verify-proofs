(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS Require Import X0mx X0k2.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1cr X1da X1dg X1df X1ck X1cu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1nt X1rh X1re X1r8.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0bp X0j9 X0ec X001 X00b X04b X07z X05o X05p X05s
X081 X05l X05m X09f X06d X069.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X12c X14x X0r0 X0ra X0v9 X0yr X0wl X0ys X0x2.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14x OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0r0 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ra OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0v9 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0yr OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0wl OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ys OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0x2.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Definition e_free_L : Z := 0x67f80.

Lemma nbdestroy_w1 : forall (S usp lo : Z) (hrest : list cell)
(ra gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
rw_cells bsegs m S (C8 (Z_to_bv 64 A_speex_nb_mode) :: hrest) -> Z.of_nat (cells_size hrest) = 24 ->
aobj bsegs m S 2968 -> S mod 8 = 0 -> aobj bsegs m A_speex_nb_mode 96 ->
stk bsegs m lo usp -> lo <= usp - 16 -> SH_HI <= lo -> usp < 2^63 ->
(S + 2968 <= lo \/ usp <= S) -> 0 < S -> S + 2968 < 2^63 ->
client_constsB m -> lib_consts m -> mem_inv bsegs m ->
evt bsegs (fun ms => exists (m1 : mem) (xt1 xa1 xa2 xa3 : word),
ms = MS (mkR ra (Z_to_bv 64 usp) gp tp t0 xt1 t2 s0 s1 (Z_to_bv 64 S) xa1 xa2 xa3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 e_free_L) fc None m1 (seg_rom bsegs)
/\ munch [(usp + -16, usp)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1 /\ stk bsegs m1 lo usp)
(MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 S) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_speex_decoder_destroy) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros P0 HR OBS S8 OBM ST LO LOS SPH AP GS SB (G1 & G2 & _) LC MI.
unfold A_speex_decoder_destroy, e_free_L, gB_GOT_shadow_offset_cell, gB_shadow_memory_dynamic_address in *.
pose proof (lib_const m A_speex_nb_mode LC_speex_nb_mode LC ltac:(lc_in)) as ND. unfold LC_speex_nb_mode in ND.
assert (AL8 : A_speex_nb_mode mod 8 = 0) by reflexivity.
assert (MPR : 0x10000 <= A_speex_nb_mode /\ A_speex_nb_mode + 96 <= 0x65b000) by (unfold A_speex_nb_mode; lia).
set (MP := A_speex_nb_mode) in *. clearbody MP.
pose proof LOS as LOS'. unfold SH_LO, SH_HI in LOS'.
pose proof (munch_refl [(usp + -16, usp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
assert (OF : offsh [(usp + -16, usp)]) by (cbn; unfold SH_LO, SH_HI; lia).
carve_frame 16%nat ST.
apply (rw_cells_split_CB bsegs _ _ [] 16 _ [] [8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
ato 0x98a38. astep. sh_if.
ato 0x98a40. astep. sh_if.
ato 0x98a64. astep. sh_if.
ato 0x98a6c. astep. sh_if.
ato 0x98a88. do 2 astep. release_frame FR ST usp.
ato 0x67f80.
apply evt_done. do 5 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
Qed.

Section NbDestroyCPS.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis FRE : free_contract RT.
Hypothesis AF_LIB : forall Σ m, ART RT Σ m -> lib_consts m.

Definition nb_decoder_destroy_cps : Prop :=
forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
F fc (m : mem) (S OUT STEREO lo : Z) (st : nb_state bptr),
fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 S -> tp = Z_to_bv 64 0x638c98 ->
NBREP m S OUT STEREO st -> In (S, NBSTATE_SIZEOF) (rt_live RT Σ) ->
ART RT Σ m -> mem_inv bsegs m ->
stk bsegs m lo (bv_unsigned sp) -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + RT_STACK + 16 <= bv_unsigned sp ->
bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 ->
unwind_ch m ra s0 sp ->
cps bsegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
t3 t4 t5 t6 F fc A_speex_decoder_destroy m)))
(fun c => exists (Σ' : rts RT),
ASTA RT Σ' PMc (fun ms => exists v m',
ret_stL (fun F' fc' => F' = F /\ fc' = fc) ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v m' ms
/\ rt_after_f RT Σ' (bv_unsigned sp) lo m m'
/\ rt_pres_fp (rt_live RT Σ') (rt_frames RT Σ) (bv_unsigned sp) [] m m') c
/\ rt_live RT Σ' = live_remove S (rt_live RT Σ) /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
/\ rt_credit RT Σ' = rt_credit RT Σ /\ rt_pois RT Σ' = rt_pois RT Σ).

Theorem nb_decoder_destroy_ok : nb_decoder_destroy_cps.
Proof using AF FRE AF_LIB.
intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m S OUT STEREO lo st
FDO MST -> -> REP INL ART0 MI0 ST0 LOW LOR SPT SPA UNW.
intros T c Hc Hk.
set (usp := bv_unsigned sp) in *.
assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned).
unfold entry_st in Hc. rewrite ESP in Hc.
unfold NBSTATE_SIZEOF in *.
destruct (live_below_lo RT AF Σ m S 2968 lo ART0 INL LOW) as (BD0 & BD1 & LOS).
destruct (af_acc_live RT AF Σ m S 2968 ART0 INL) as (_ & ACS).
destruct REP as (S8 & SPOS & INV & j & JOK & CBS & X).
apply (nb_pieces_of_cells bsegs _ _ _ m S OUT STEREO st j JOK) in X. destruct X as (P0 & _). unfold nb_hdr_cells in P0.
pose proof (af_client_consts RT AF Σ m ART0) as CC0.
pose proof (AF_LIB Σ m ART0) as LC0.
assert (OBM : aobj bsegs m A_speex_nb_mode 96)
by (apply (aobj_lit RT AF Σ m A_speex_nb_mode 96 ART0); [unfold ACC_LITS, A_speex_nb_mode; cbn [In]; repeat (first [left; reflexivity | right]) | unfold A_speex_nb_mode; lia | unfold A_speex_nb_mode, APP_TOP; lia]).
assert (OBS : aobj bsegs m S 2968) by (split; [lia|]; split; [unfold APP_TOP, STACK_WIN, USTACK_TOP, RT_STACK in *; lia| exact ACS]).
pose proof (fun a => aclient_split RT AF Σ m usp a ART0) as SPL.
cps_norm.

cps_seg (nbdestroy_w1 S usp lo). { reflexivity. } { ulc. }
destruct POST as (m1 & xt1 & xa1 & xa2 & xa3 & -> & MU1 & WM1 & MI1 & ST1).
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
End NbDestroyCPS.
End B_TWIN.

Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Definition e_free_L : Z := 0x67e94.

Lemma nbdestroy_w1 : forall (S usp lo : Z) (hrest : list cell)
(ra gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
rw_cells asegs m S (C8 (Z_to_bv 64 A_speex_nb_mode) :: hrest) -> Z.of_nat (cells_size hrest) = 24 ->
aobj asegs m S 2968 -> S mod 8 = 0 -> aobj asegs m A_speex_nb_mode 96 ->
stk asegs m lo usp -> lo <= usp - 16 -> SH_HI <= lo -> usp < 2^63 ->
(S + 2968 <= lo \/ usp <= S) -> 0 < S -> S + 2968 < 2^63 ->
client_consts m -> lib_consts m -> mem_inv asegs m ->
evt asegs (fun ms => exists (m1 : mem) (xt1 xa1 xa2 xa3 : word),
ms = MS (mkR ra (Z_to_bv 64 usp) gp tp t0 xt1 t2 s0 s1 (Z_to_bv 64 S) xa1 xa2 xa3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 e_free_L) fc None m1 (seg_rom asegs)
/\ munch [(usp + -16, usp)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo usp)
(MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 S) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_speex_decoder_destroy) fc None m (seg_rom asegs)).
Proof.
intros until m. intros P0 HR OBS S8 OBM ST LO LOS SPH AP GS SB (G1 & G2 & _) LC MI.
unfold A_speex_decoder_destroy, e_free_L, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address in *.
pose proof (lib_const m A_speex_nb_mode LC_speex_nb_mode LC ltac:(lc_in)) as ND. unfold LC_speex_nb_mode in ND.
assert (AL8 : A_speex_nb_mode mod 8 = 0) by reflexivity.
assert (MPR : 0x10000 <= A_speex_nb_mode /\ A_speex_nb_mode + 96 <= 0x652000) by (unfold A_speex_nb_mode; lia).
set (MP := A_speex_nb_mode) in *. clearbody MP.
pose proof LOS as LOS'. unfold SH_LO, SH_HI in LOS'.
pose proof (munch_refl [(usp + -16, usp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
assert (OF : offsh [(usp + -16, usp)]) by (cbn; unfold SH_LO, SH_HI; lia).
carve_frame 16%nat ST.
apply (rw_cells_split_CB asegs _ _ [] 16 _ [] [8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
ato 0x984c0. do 2 astep. release_frame FR ST usp.
ato 0x67e94.
apply evt_done. do 5 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
Qed.

Section NbDestroyCPS.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis FRE : free_contract RT.
Hypothesis AF_LIB : forall Σ m, ART RT Σ m -> lib_consts m.

Definition nb_decoder_destroy_cps : Prop :=
forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
F fc (m : mem) (S OUT STEREO lo : Z) (st : nb_state bptr),
fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 S -> tp = Z_to_bv 64 0x630458 ->
NBREP m S OUT STEREO st -> In (S, NBSTATE_SIZEOF) (rt_live RT Σ) ->
ART RT Σ m -> mem_inv asegs m ->
stk asegs m lo (bv_unsigned sp) -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + RT_STACK + 16 <= bv_unsigned sp ->
bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 ->
unwind_ch m ra s0 sp ->
cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
t3 t4 t5 t6 F fc A_speex_decoder_destroy m)))
(fun c => exists (Σ' : rts RT),
ASTA RT Σ' PMc (fun ms => exists v m',
ret_stL (fun F' fc' => F' = F /\ fc' = fc) ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v m' ms
/\ rt_after_f RT Σ' (bv_unsigned sp) lo m m'
/\ rt_pres_fp (rt_live RT Σ') (rt_frames RT Σ) (bv_unsigned sp) [] m m') c
/\ rt_live RT Σ' = live_remove S (rt_live RT Σ) /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
/\ rt_credit RT Σ' = rt_credit RT Σ /\ rt_pois RT Σ' = rt_pois RT Σ).

Theorem nb_decoder_destroy_ok : nb_decoder_destroy_cps.
Proof using AF FRE AF_LIB.
intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m S OUT STEREO lo st
FDO MST -> -> REP INL ART0 MI0 ST0 LOW LOR SPT SPA UNW.
intros T c Hc Hk.
set (usp := bv_unsigned sp) in *.
assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned).
unfold entry_st in Hc. rewrite ESP in Hc.
unfold NBSTATE_SIZEOF in *.
destruct (live_below_lo RT AF Σ m S 2968 lo ART0 INL LOW) as (BD0 & BD1 & LOS).
destruct (af_acc_live RT AF Σ m S 2968 ART0 INL) as (_ & ACS).
destruct REP as (S8 & SPOS & INV & j & JOK & CBS & X).
apply (nb_pieces_of_cells asegs _ _ _ m S OUT STEREO st j JOK) in X. destruct X as (P0 & _). unfold nb_hdr_cells in P0.
pose proof (af_client_consts RT AF Σ m ART0) as CC0.
pose proof (AF_LIB Σ m ART0) as LC0.
assert (OBM : aobj asegs m A_speex_nb_mode 96)
by (apply (aobj_lit RT AF Σ m A_speex_nb_mode 96 ART0); [unfold ACC_LITS, A_speex_nb_mode; cbn [In]; repeat (first [left; reflexivity | right]) | unfold A_speex_nb_mode; lia | unfold A_speex_nb_mode, APP_TOP; lia]).
assert (OBS : aobj asegs m S 2968) by (split; [lia|]; split; [unfold APP_TOP, STACK_WIN, USTACK_TOP, RT_STACK in *; lia| exact ACS]).
pose proof (fun a => aclient_split RT AF Σ m usp a ART0) as SPL.
cps_norm.

cps_seg (nbdestroy_w1 S usp lo). { reflexivity. } { ulc. }
destruct POST as (m1 & xt1 & xa1 & xa2 & xa3 & -> & MU1 & WM1 & MI1 & ST1).
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
End NbDestroyCPS.
