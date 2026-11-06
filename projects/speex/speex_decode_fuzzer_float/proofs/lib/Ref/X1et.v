(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bj X1cf X1bp.
From OSSVerify.speex.speex_decode_fuzzer_float.images Require Import Plain.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1nj X1nk X1ho X1es X1eu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Open Scope Z_scope.
Local Notation rsegs := Plain.M.loaded_segments.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition iir_mem16_8_stmt_copy : Prop :=
forall (PX PD PY PM N : Z) (xs den ys mem0 : list word) (stk8 : word)
(ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem),
rw_cells rsegs m PX (f32 xs) -> length xs = Z.to_nat N ->
rw_cells rsegs m PD (f32 den) -> length den = 8%nat ->
rw_cells rsegs m PM (f32 mem0) -> length mem0 = 8%nat ->
(PY = PX /\ ys = xs \/ apart PY (4 * N) PX (4 * N) /\ rw_cells rsegs m PY (f32 ys) /\ length ys = Z.to_nat N) ->
1 <= N <= 320 ->
apart PY (4 * N) PD 32 -> apart PY (4 * N) PM 32 -> apart PM 32 PD 32 -> apart PM 32 PX (4 * N) ->
a0 = Z_to_bv 64 PX -> a1 = Z_to_bv 64 PD -> a2 = Z_to_bv 64 PY -> a3 = Z_to_bv 64 N -> a4 = Z_to_bv 64 8 ->
a5 = Z_to_bv 64 PM -> a6 = stk8 ->
mem_inv rsegs m -> frm0 fc ->
evt rsegs (farr2_post [(PY, PY + 4 * N); (PM, PM + 32)] PY (Z.to_nat N) PM 8%nat ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_iir_mem16) fc None m (seg_rom rsegs)).

Lemma farr2_post_feqv_closed8 : forall W P n Q k ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m,
feqv_closed (farr2_post W P n Q k ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m).
Proof.
intros. intros s t E sfH_; first [ sf_destruct 9%nat sfH_ as rv kk F' fc' m' ws' vs' -> REST | sf_fb; destruct sfH_ as (rv & kk & F' & fc' & m' & ws' & vs' & -> & REST) ].
destruct (ms_feqv_inv _ _ _ _ _ _ _ _ E) as (F'' & _ & ->).
first [ unshelve sf_eexists 7%nat; [ exact (rv) | exact (kk) | exact (F'') | exact (fc') | exact (m') | exact (ws') | exact (vs') | ] | sf_fb; exists rv, kk, F'', fc', m', ws', vs' ]. split; [reflexivity| exact REST].
Qed.

Lemma iir_mem16_8_spec : iir_mem16_8_stmt_copy.
Proof.
unfold iir_mem16_8_stmt_copy. intros until m. intros XI LI DD LD MM LM YY HN A1 A2 A3 A4 -> -> -> -> -> -> -> MI FRM.
assert (EN : Z.of_nat (length xs) = N) by (rewrite LI; apply Z2Nat.id; lia).
assert (ED : Z.of_nat (length den) = 8) by (rewrite LD; reflexivity).
unfold apart in *.
apply evt_canonF; [apply farr2_post_feqv_closed8|]. unfold fcanon.
destruct YY as [(-> & ->) | (AXY & YI & LY)].
-
eapply evt_mono.
+ rewrite <- EN, <- ED.
eapply (iir_mem16_spec_inplace xs den mem0 PX PD PM); try eassumption; rewrite ?EN, ?ED; try lia.
+ intros ms' sfH_; first [ sf_destruct 24%nat sfH_ as t0' t1' t2' a6' a7' t3' t4' t5' t6' g12 g13 g14 g15 fc' m' -> MU WM MI' FRM' OY OM ODEN _ | sf_fb; destruct sfH_ as (t0' & t1' & t2' & a6' & a7' & t3' & t4' & t5' & t6' & g12 & g13 & g14 & g15 & fc' & m' & -> & MU & WM & MI' & FRM' & OY & OM & ODEN & _) ].
eexists _, (ICL t0' t1' t2' _ _ _ _ _ a6' a7' t3' t4' t5' t6'), _, fc', m', _, _.
split; [rewrite EN, ED; reflexivity|]. rewrite EN, ED in MU. change (4 * 8) with 32 in MU.
split; [exact MU|]. split; [exact WM|]. split; [exact MI'|]. split; [exact FRM'|]. split; [exact OY|]. split; [rewrite length_iir_ys; exact LI|].
split; [exact OM|]. rewrite length_iir_st; [exact LD | rewrite LM, LD; reflexivity | rewrite LD; lia].
-
eapply evt_mono.
+ rewrite <- EN, <- ED.
eapply (iir_mem16_spec xs den mem0 PX PD PY PM); try eassumption; rewrite ?EN, ?ED, ?LY, ?LI; try lia; try reflexivity.
+ intros ms' sfH_; first [ sf_destruct 24%nat sfH_ as t0' t1' t2' a6' a7' t3' t4' t5' t6' g12 g13 g14 g15 fc' m' -> MU WM MI' FRM' OY OM ODEN _ | sf_fb; destruct sfH_ as (t0' & t1' & t2' & a6' & a7' & t3' & t4' & t5' & t6' & g12 & g13 & g14 & g15 & fc' & m' & -> & MU & WM & MI' & FRM' & OY & OM & ODEN & _) ].
eexists _, (ICL t0' t1' t2' _ _ _ _ _ a6' a7' t3' t4' t5' t6'), _, fc', m', _, _.
split; [rewrite EN, ED; reflexivity|]. rewrite EN, ED in MU. change (4 * 8) with 32 in MU.
split; [exact MU|]. split; [exact WM|]. split; [exact MI'|]. split; [exact FRM'|]. split; [exact OY|]. split; [rewrite length_iir_ys; exact LI|].
split; [exact OM|]. rewrite length_iir_st; [exact LD | rewrite LM, LD; reflexivity | rewrite LD; lia].
Qed.
