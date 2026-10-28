(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bj X1cf X1bp.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1nj X1nk. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1ho X1fe X1eb X1fz X1fw X1ed X1es X1eu X1er.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Open Scope Z_scope.
Local Notation rsegs := Ubsan.M.loaded_segments.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Lemma farr_post_feqv_closed : forall W P n ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m,
feqv_closed (farr_post W P n ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m).
Proof.
intros. intros s t E sfH_; first [ sf_destruct 8%nat sfH_ as rv kk F' fc' m' ws' -> REST | sf_fb; destruct sfH_ as (rv & kk & F' & fc' & m' & ws' & -> & REST) ].
destruct (ms_feqv_inv _ _ _ _ _ _ _ _ E) as (F'' & _ & ->).
first [ unshelve sf_eexists 6%nat; [ exact (rv) | exact (kk) | exact (F'') | exact (fc') | exact (m') | exact (ws') | ] | sf_fb; exists rv, kk, F'', fc', m', ws' ]. split; [reflexivity| exact REST].
Qed.

Lemma farr2_post_feqv_closed : forall W P n Q k ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m,
feqv_closed (farr2_post W P n Q k ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m).
Proof.
intros. intros s t E sfH_; first [ sf_destruct 9%nat sfH_ as rv kk F' fc' m' ws' vs' -> REST | sf_fb; destruct sfH_ as (rv & kk & F' & fc' & m' & ws' & vs' & -> & REST) ].
destruct (ms_feqv_inv _ _ _ _ _ _ _ _ E) as (F'' & _ & ->).
first [ unshelve sf_eexists 7%nat; [ exact (rv) | exact (kk) | exact (F'') | exact (fc') | exact (m') | exact (ws') | exact (vs') | ] | sf_fb; exists rv, kk, F'', fc', m', ws', vs' ]. split; [reflexivity| exact REST].
Qed.

Lemma farr2s_post_feqv_closed : forall W P n Q k lo ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m,
feqv_closed (farr2s_post W P n Q k lo ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m).
Proof.
intros. intros s t E sfH_; first [ sf_destruct 9%nat sfH_ as rv kk F' fc' m' ws' vs' -> REST | sf_fb; destruct sfH_ as (rv & kk & F' & fc' & m' & ws' & vs' & -> & REST) ].
destruct (ms_feqv_inv _ _ _ _ _ _ _ _ E) as (F'' & _ & ->).
first [ unshelve sf_eexists 7%nat; [ exact (rv) | exact (kk) | exact (F'') | exact (fc') | exact (m') | exact (ws') | exact (vs') | ] | sf_fb; exists rv, kk, F'', fc', m', ws', vs' ]. split; [reflexivity| exact REST].
Qed.

Lemma Z_of_nat_to_nat : forall n, 0 <= n -> Z.of_nat (Z.to_nat n) = n.
Proof. intros. apply Z2Nat.id. assumption. Qed.

Lemma bw_lpc_w_proof : bw_lpc_w_stmt.
Proof.
unfold bw_lpc_w_stmt. intros until m. intros XI LI XO LO AP PI0 PI4 PO0 PO4 -> -> -> MI FRM.
eapply evt_mono.
- eapply (bw_lpc_spec xs ys PI PO); try eassumption.
+ rewrite LI, LO. reflexivity.
+ unfold apart in AP. rewrite LI. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. lia.
+ rewrite LI. reflexivity.
+ rewrite LI. cbn. lia.
- intros ms' sfH_; destruct sfH_ as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & f14 & f15 & fc' & m' & -> & MU & WM & MI' & FRM' & OUTP & _).
exists a0', (ICL t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6'), (bvmap_set 14 f14 (bvmap_set 15 f15 F)), fc', m', (bw_outs (reg_get F 10) 0 xs).
split; [reflexivity|]. rewrite LI in MU. cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in MU.
split; [exact MU|]. split; [exact WM|]. split; [exact MI'|]. split; [exact FRM'|]. split; [exact OUTP|]. rewrite length_bw_outs. exact LI.
Qed.

Lemma compute_rms16_w_proof : compute_rms16_w_stmt.
Proof.
unfold compute_rms16_w_stmt. intros until m. intros XI LI HN PX0 PX4 -> -> MI FRM.
assert (EN : Z.of_nat (length xs) = n) by (rewrite LI; apply Z2Nat.id; lia).
eapply evt_mono.
- rewrite <- EN. eapply (compute_rms16_spec xs PX); try eassumption. rewrite EN. exact HN.
- intros ms' sfH_; destruct sfH_ as (t0' & t1' & t2' & a0' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & g13 & g14 & g15 & fc' & m' & -> & MU & WM & MI' & FRM').
eexists a0', (ICL t0' t1' t2' _ a2' a3' a4' a5' a6' a7' t3' t4' t5' t6'), _, fc', m', xs.
split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI'|]. split; [exact FRM'|]. split; [| exact LI].
eapply rw_cells_transport; [exact XI | exact MU | exact WM | exact I].
Qed.

Lemma signal_mul_w_proof : signal_mul_w_stmt.
Proof.
unfold signal_mul_w_stmt. intros until m. intros XI LI PX0 PX4 -> -> -> MI FRM.
eapply evt_mono.
- eapply (signal_mul_spec xs PX); try eassumption.
+ rewrite LI. reflexivity.
+ rewrite LI. cbn. lia.
- intros ms' sfH_; destruct sfH_ as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & f15 & fc' & m' & -> & MU & WM & MI' & FRM' & OUTP).
exists a0', (ICL t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6'), (bvmap_set 15 f15 F), fc', m', (map (smul (reg_get F 10)) xs).
split; [reflexivity|]. rewrite LI in MU. cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in MU.
split; [exact MU|]. split; [exact WM|]. split; [exact MI'|]. split; [exact FRM'|]. split; [exact OUTP|]. rewrite length_map. exact LI.
Qed.

Lemma sanitize_values32_w_proof : sanitize_values32_w_stmt.
Proof.
unfold sanitize_values32_w_stmt. intros until m. intros XI LI PX0 PX4 -> -> MI FRM.
apply evt_canonF; [apply farr_post_feqv_closed|]. unfold fcanon.
eapply evt_mono.
- eapply (sanitize_values32_spec xs PX); try eassumption.
+ rewrite LI. reflexivity.
+ rewrite LI. cbn. lia.
- intros ms' sfH_; destruct sfH_ as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & g13 & g14 & fc' & m' & -> & MU & WM & MI' & FRM' & OUTP).
eexists a0', (ICL t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6'), _, fc', m', _.
split; [reflexivity|]. rewrite LI in MU. cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in MU.
split; [exact MU|]. split; [exact WM|]. split; [exact MI'|]. split; [exact FRM'|]. split; [exact OUTP|]. rewrite length_map. exact LI.
Qed.

Lemma highpass_w_proof : highpass_w_stmt.
Proof.
unfold highpass_w_stmt. intros until m. intros XI LI MM LM FID AP PX0 PX4 PM0 PM4 ST LO GLO SP63 AX AM -> -> -> -> -> MI FRM.
destruct mem0 as [|m0' [|m1' [|? ?]]]; try (cbn in LM; lia).
unfold apart, HIGHPASS_DEPTH, NB_GLOBALS_TOP in *.
apply evt_canonF; [apply farr2s_post_feqv_closed|]. unfold fcanon.
eapply evt_mono.
- eapply (highpass_spec xs m0' m1' PX PM); try eassumption.
all: try (rewrite LI; reflexivity).
all: try reflexivity.
all: rewrite ?LI; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia.
- intros ms' sfH_; destruct sfH_ as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & g0 & g1 & g10 & g11 & g12 & g13 & g14 & g15 & fc' & m' & -> & MU & WM & MI' & FRM' & OUTP & OUTM & ST').
eexists a0', (ICL t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6'), _, fc', m', _, _.
split; [reflexivity|]. rewrite LI in MU. cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in MU.
split; [exact MU|]. split; [exact WM|]. split; [exact MI'|]. split; [exact FRM'|]. split; [exact ST'|]. split; [exact OUTP|]. split; [rewrite length_hp_ys; exact LI|].
split; [exact OUTM|]. reflexivity.
Qed.

Lemma iir_mem16_w_proof : iir_mem16_w_stmt.
Proof.
unfold iir_mem16_w_stmt. intros until m. intros XI LI DD LD MM LM YY HN A1 A2 A3 A4 PX0 PX4 PD0 PD4 PY0 PY4 PM0 PM4 ST LO GLO SP63 BX BY BD BM -> -> -> -> -> -> -> MI FRM.
assert (EN : Z.of_nat (length xs) = N) by (rewrite LI; apply Z2Nat.id; lia).
assert (ED : Z.of_nat (length den) = 10) by (rewrite LD; reflexivity).
unfold apart, IIR_DEPTH, NB_GLOBALS_TOP in *.
apply evt_canonF; [apply farr2s_post_feqv_closed|]. unfold fcanon.
destruct YY as [(-> & ->) | (AXY & YI & LY)].
-
eapply evt_mono.
+ rewrite <- EN, <- ED.
eapply (iir_mem16_spec_inplace xs den mem0 PX PD PM); try eassumption; rewrite ?EN, ?ED; try lia.
+ intros ms' sfH_; destruct sfH_ as (t0' & t1' & t2' & a6' & a7' & t3' & t4' & t5' & t6' & g12 & g13 & g14 & g15 & fc' & m' & -> & MU & WM & MI' & FRM' & OY & OM & ODEN & _ & ST').
eexists _, (ICL t0' t1' t2' _ _ _ _ _ a6' a7' t3' t4' t5' t6'), _, fc', m', _, _.
split; [rewrite EN, ED; reflexivity|]. rewrite EN, ED in MU. change (4 * 10) with 40 in MU.
split; [exact MU|]. split; [exact WM|]. split; [exact MI'|]. split; [exact FRM'|]. split; [exact ST'|]. split; [exact OY|]. split; [rewrite length_iir_ys; exact LI|].
split; [exact OM|]. rewrite length_iir_st; [exact LD | rewrite LM, LD; reflexivity | rewrite LD; lia].
-
eapply evt_mono.
+ rewrite <- EN, <- ED.
eapply (iir_mem16_spec xs den mem0 PX PD PY PM); try eassumption; rewrite ?EN, ?ED, ?LY, ?LI; try lia; try reflexivity.
+ intros ms' sfH_; destruct sfH_ as (t0' & t1' & t2' & a6' & a7' & t3' & t4' & t5' & t6' & g12 & g13 & g14 & g15 & fc' & m' & -> & MU & WM & MI' & FRM' & OY & OM & ODEN & _ & ST').
eexists _, (ICL t0' t1' t2' _ _ _ _ _ a6' a7' t3' t4' t5' t6'), _, fc', m', _, _.
split; [rewrite EN, ED; reflexivity|]. rewrite EN, ED in MU. change (4 * 10) with 40 in MU.
split; [exact MU|]. split; [exact WM|]. split; [exact MI'|]. split; [exact FRM'|]. split; [exact ST'|]. split; [exact OY|]. split; [rewrite length_iir_ys; exact LI|].
split; [exact OM|]. rewrite length_iir_st; [exact LD | rewrite LM, LD; reflexivity | rewrite LD; lia].
Qed.

Lemma skipn_skipn_nat : forall {A} (a b : nat) (l : list A), skipn a (skipn b l) = skipn (b + a) l.
Proof. intros. rewrite skipn_skipn. f_equal. lia. Qed.

Lemma memmove_proof : memmove_stmt.
Proof.
unfold memmove_stmt. intros until m. intros XB BD DN BS SN N0 DS TOP -> -> -> MI.
pose proof (u8arr_of_rw_cells rsegs _ _ _ _ XB) as U.
rewrite <- (firstn_skipn (Z.to_nat (d - B)) bs) in U.
apply (proj1 (u8arr_app _ _ _ _)) in U. destruct U as [UPRE USUF].
rewrite firstn_length_le in USUF by lia. rewrite Z2Nat.id in USUF by lia. replace (B + (d - B)) with d in USUF by lia.
assert (LSUF : length (skipn (Z.to_nat (d - B)) bs) = (length bs - Z.to_nat (d - B))%nat) by (rewrite length_skipn; lia).
eapply evt_mono.
- eapply (memmove_fwd_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m d (s - d) n (skipn (Z.to_nat (d - B)) bs));
try reflexivity; try eassumption; rewrite ?LSUF; try lia. all: try (f_equal; lia).
- intros ms' sfH_; first [ sf_destruct 20%nat sfH_ as t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' -> MU WM MI' UD | sf_fb; destruct sfH_ as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MU & WM & MI' & UD) ].
exists (ICL t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6'), m'. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [exact MI'|].

assert (UPRE' : u8arr rsegs m' B (firstn (Z.to_nat (d - B)) bs)).
{ eapply u8arr_transport; [exact UPRE | exact MU | exact WM |].
cbn [disjoint_from]. rewrite firstn_length_le by lia. split; [|exact I]. lia. }
pose proof (proj2 (u8arr_app m' B (firstn (Z.to_nat (d - B)) bs) (firstn (Z.to_nat n) (skipn (Z.to_nat (s - d)) (skipn (Z.to_nat (d - B)) bs)) ++ skipn (Z.to_nat n) (skipn (Z.to_nat (d - B)) bs)))) as J.
rewrite firstn_length_le in J by lia. rewrite Z2Nat.id in J by lia. replace (B + (d - B)) with d in J by lia.
specialize (J (conj UPRE' UD)).
apply rw_cells_of_u8arr in J.
unfold mm_bytes. rewrite !skipn_skipn_nat in J.
replace (Z.to_nat (d - B) + Z.to_nat (s - d))%nat with (Z.to_nat (s - B)) in J by lia.
match type of J with rw_cells _ _ _ [CB ?k _] => replace k with (length bs) in J end.
+ exact J.
+ rewrite !length_app, !length_firstn, !length_skipn. lia.
Qed.
