(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS Require Import X0mx X0k2.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1da X1dg X1df X1ck.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0bp X0j9 X0ec X001 X00b X04b X07z X05o X05p X05s.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X12c X14x X0r0 X0ra X0v9 X0yr X0wl.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14x OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0r0 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ra OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0v9 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0yr OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0wl.
Import ListNotations.
Open Scope Z_scope.

Section QMF16.
Variable RT : rt_sig.

Definition qmf_synth_cps16 (N : Z) : Prop :=
forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
F fc (m : mem) (Y G0 G1 lo fp P0 N0 P1 N1 : Z) (kp : nat) (ys g0l g1l : list word),
fdfs_only PMc -> mat_stable PMc ->
a0 = Z_to_bv 64 Y -> a1 = Z_to_bv 64 (Y + 2 * N) -> a2 = Z_to_bv 64 0x27000 -> a3 = Z_to_bv 64 Y -> a4 = Z_to_bv 64 N -> a5 = Z_to_bv 64 64 ->
a6 = Z_to_bv 64 G0 -> a7 = Z_to_bv 64 G1 -> tp = Z_to_bv 64 0x638c98 ->

rw_cells bsegs m Y (f32 ys) -> Z.of_nat (length ys) = N -> In (fp, kp) (rt_frames RT Σ) -> fp <= Y -> Y + 4 * N <= fp + fs_size kp - 8 ->
acc bsegs m Y (4 * N) -> Y mod 4 = 0 ->

rw_cells bsegs m G0 (f32 g0l) -> length g0l = 64%nat -> In (P0, N0) (rt_live RT Σ) -> P0 <= G0 -> G0 + 256 <= P0 + N0 -> G0 mod 4 = 0 ->
rw_cells bsegs m G1 (f32 g1l) -> length g1l = 64%nat -> In (P1, N1) (rt_live RT Σ) -> P1 <= G1 -> G1 + 256 <= P1 + N1 -> G1 mod 4 = 0 ->
(G0 + 256 <= G1 \/ G1 + 256 <= G0) ->
pois_above (rt_pois RT Σ) (bv_unsigned sp) -> X1cn.frm0 fc ->
ART RT Σ m -> mem_inv bsegs m ->
stk bsegs m lo (bv_unsigned sp) -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + RT_STACK + 5776 <= bv_unsigned sp ->
bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 32 = 16 ->
cps bsegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
t3 t4 t5 t6 F fc 0xa8508 m)))
(fun c => exists (Σ' : rts RT),
ASTA RT Σ' PMc (fun ms => exists v m' (ys' g0' g1' : list word),
ret_stL (fun F' fc' => X1cn.frm0 fc') ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v m' ms
/\ rt_after RT Σ' (bv_unsigned sp) lo m m'
/\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) [(Y, Y + 4 * N); (G0, G0 + 256); (G1, G1 + 256)] m m'
/\ rw_cells bsegs m' Y (f32 ys') /\ Z.of_nat (length ys') = N
/\ rw_cells bsegs m' G0 (f32 g0') /\ length g0' = 64%nat /\ rw_cells bsegs m' G1 (f32 g1') /\ length g1' = 64%nat
/\ acc bsegs m' Y (4 * N)) c
/\ rt_live RT Σ' = rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
/\ rt_credit RT Σ' = rt_credit RT Σ /\ rt_pois RT Σ' = rt_pois RT Σ).
End QMF16.
End B_TWIN.

Import ListNotations.
Open Scope Z_scope.

Section QMF16.
Variable RT : rt_sig.

Definition qmf_synth_cps16 (N : Z) : Prop :=
forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
F fc (m : mem) (Y G0 G1 lo fp P0 N0 P1 N1 : Z) (kp : nat) (ys g0l g1l : list word),
fdfs_only PMc -> mat_stable PMc ->
a0 = Z_to_bv 64 Y -> a1 = Z_to_bv 64 (Y + 2 * N) -> a2 = Z_to_bv 64 0x27000 -> a3 = Z_to_bv 64 Y -> a4 = Z_to_bv 64 N -> a5 = Z_to_bv 64 64 ->
a6 = Z_to_bv 64 G0 -> a7 = Z_to_bv 64 G1 -> tp = Z_to_bv 64 0x630458 ->

rw_cells asegs m Y (f32 ys) -> Z.of_nat (length ys) = N -> In (fp, kp) (rt_frames RT Σ) -> fp <= Y -> Y + 4 * N <= fp + fs_size kp - 8 ->
acc asegs m Y (4 * N) -> Y mod 4 = 0 ->

rw_cells asegs m G0 (f32 g0l) -> length g0l = 64%nat -> In (P0, N0) (rt_live RT Σ) -> P0 <= G0 -> G0 + 256 <= P0 + N0 -> G0 mod 4 = 0 ->
rw_cells asegs m G1 (f32 g1l) -> length g1l = 64%nat -> In (P1, N1) (rt_live RT Σ) -> P1 <= G1 -> G1 + 256 <= P1 + N1 -> G1 mod 4 = 0 ->
(G0 + 256 <= G1 \/ G1 + 256 <= G0) ->
pois_above (rt_pois RT Σ) (bv_unsigned sp) -> X1cn.frm0 fc ->
ART RT Σ m -> mem_inv asegs m ->
stk asegs m lo (bv_unsigned sp) -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + RT_STACK + 5744 <= bv_unsigned sp ->
bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 32 = 16 ->
cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
t3 t4 t5 t6 F fc 0xa4b58 m)))
(fun c => exists (Σ' : rts RT),
ASTA RT Σ' PMc (fun ms => exists v m' (ys' g0' g1' : list word),
ret_stL (fun F' fc' => X1cn.frm0 fc') ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v m' ms
/\ rt_after RT Σ' (bv_unsigned sp) lo m m'
/\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) [(Y, Y + 4 * N); (G0, G0 + 256); (G1, G1 + 256)] m m'
/\ rw_cells asegs m' Y (f32 ys') /\ Z.of_nat (length ys') = N
/\ rw_cells asegs m' G0 (f32 g0') /\ length g0' = 64%nat /\ rw_cells asegs m' G1 (f32 g1') /\ length g1' = 64%nat
/\ acc asegs m' Y (4 * N)) c
/\ rt_live RT Σ' = rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
/\ rt_credit RT Σ' = rt_credit RT Σ /\ rt_pois RT Σ' = rt_pois RT Σ).
End QMF16.
