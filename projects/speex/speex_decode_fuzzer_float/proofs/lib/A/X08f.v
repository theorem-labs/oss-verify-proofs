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

Definition A_multicomb : Z := 0xa8f7c.
Definition MULTICOMB_STACK : Z := 4320.

Section MC.
Variable RT : rt_sig.

Definition multicomb_cps : Prop :=
forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
F fc (m : mem) (EB eoff ne pitch lo fp P0 N0 : Z) (kp : nat) (eb ns : list word),
fdfs_only PMc -> mat_stable PMc ->
a0 = Z_to_bv 64 (EB + 4 * eoff) -> a1 = Z_to_bv 64 ne -> a4 = Z_to_bv 64 80 -> a5 = Z_to_bv 64 pitch -> a6 = Z_to_bv 64 40 -> tp = Z_to_bv 64 0x638c98 ->

rw_cells bsegs m EB (f32 eb) -> length eb = 500%nat -> In (P0, N0) (rt_live RT Σ) -> P0 <= EB -> EB + 2000 <= P0 + N0 -> EB mod 4 = 0 ->
(eoff = 294 \/ eoff = 374) -> 17 <= pitch <= 144 ->

rw_cells bsegs m ne (f32 ns) -> length ns = 80%nat -> In (fp, kp) (rt_frames RT Σ) -> fp <= ne -> ne + 320 <= fp + fs_size kp - 8 ->
acc bsegs m ne 320 -> ne mod 4 = 0 ->
(length (rt_frames RT Σ) < FRAMES_MAX)%nat -> 2 <= rt_credit RT Σ -> pois_above (rt_pois RT Σ) (bv_unsigned sp) ->
ART RT Σ m -> mem_inv bsegs m -> X1cn.frm0 fc ->
stk bsegs m lo (bv_unsigned sp) -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + RT_STACK + MULTICOMB_STACK <= bv_unsigned sp ->
bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 32 = 0 ->
cps bsegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
t3 t4 t5 t6 F fc A_multicomb m)))
(fun c => exists (Σ' : rts RT),
ASTA RT Σ' PMc (fun ms => exists v m' (ns' : list word),
ret_stL (fun F' fc' => X1cn.frm0 fc') ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v m' ms
/\ rt_after RT Σ' (bv_unsigned sp) lo m m'
/\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) [(ne, ne + 320)] m m'
/\ rw_cells bsegs m' ne (f32 ns') /\ length ns' = 80%nat
/\ acc bsegs m' ne 320) c
/\ rt_live RT Σ' = rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
/\ rt_credit RT Σ' = rt_credit RT Σ - 2 /\ rt_pois RT Σ' = rt_pois RT Σ).
End MC.
End B_TWIN.

Import ListNotations.
Open Scope Z_scope.

Definition A_multicomb : Z := 0xa5388.
Definition MULTICOMB_STACK : Z := 4288.

Section MC.
Variable RT : rt_sig.

Definition multicomb_cps : Prop :=
forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
F fc (m : mem) (EB eoff ne pitch lo fp P0 N0 : Z) (kp : nat) (eb ns : list word),
fdfs_only PMc -> mat_stable PMc ->
a0 = Z_to_bv 64 (EB + 4 * eoff) -> a1 = Z_to_bv 64 ne -> a4 = Z_to_bv 64 80 -> a5 = Z_to_bv 64 pitch -> a6 = Z_to_bv 64 40 -> tp = Z_to_bv 64 0x630458 ->

rw_cells asegs m EB (f32 eb) -> length eb = 500%nat -> In (P0, N0) (rt_live RT Σ) -> P0 <= EB -> EB + 2000 <= P0 + N0 -> EB mod 4 = 0 ->
(eoff = 294 \/ eoff = 374) -> 17 <= pitch <= 144 ->

rw_cells asegs m ne (f32 ns) -> length ns = 80%nat -> In (fp, kp) (rt_frames RT Σ) -> fp <= ne -> ne + 320 <= fp + fs_size kp - 8 ->
acc asegs m ne 320 -> ne mod 4 = 0 ->
(length (rt_frames RT Σ) < FRAMES_MAX)%nat -> 2 <= rt_credit RT Σ -> pois_above (rt_pois RT Σ) (bv_unsigned sp) ->
ART RT Σ m -> mem_inv asegs m -> X1cn.frm0 fc ->
stk asegs m lo (bv_unsigned sp) -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + RT_STACK + MULTICOMB_STACK <= bv_unsigned sp ->
bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 32 = 0 ->
cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
t3 t4 t5 t6 F fc A_multicomb m)))
(fun c => exists (Σ' : rts RT),
ASTA RT Σ' PMc (fun ms => exists v m' (ns' : list word),
ret_stL (fun F' fc' => X1cn.frm0 fc') ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v m' ms
/\ rt_after RT Σ' (bv_unsigned sp) lo m m'
/\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) [(ne, ne + 320)] m m'
/\ rw_cells asegs m' ne (f32 ns') /\ length ns' = 80%nat
/\ acc asegs m' ne 320) c
/\ rt_live RT Σ' = rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
/\ rt_credit RT Σ' = rt_credit RT Σ - 2 /\ rt_pois RT Σ' = rt_pois RT Σ).
End MC.
