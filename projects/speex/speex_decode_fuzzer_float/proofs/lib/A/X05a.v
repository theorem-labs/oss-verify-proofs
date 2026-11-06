(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS Require Import X0mx X0k2.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1da.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0bp X0j9 X0ec.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X12c X14x.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14x.
Import ListNotations.
Open Scope Z_scope.

Definition allocas_unpoison_lo_contract (RT : rt_sig) : Prop :=
forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
F fc (m : mem) (top bottom lo : Z),
fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 top -> a1 = Z_to_bv 64 bottom ->
0 < top <= bottom -> top mod 8 = 0 -> bottom mod 8 = 0 -> lo <= top -> bottom <= USTACK_TOP - 16 ->
(forall e, In e (rt_pois RT Σ) -> (top <= pz_lo e /\ pz_hi e <= bottom) \/ bottom <= pz_lo e) ->
ART RT Σ m -> mem_inv bsegs m -> call_ok RT Σ m sp lo ->
cps bsegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
t3 t4 t5 t6 F fc e_allocas_unpoison m)))
(fun c => exists (Σ' : rts RT),
ASTA RT Σ' PMc (fun ms => exists m' v0, ret_stF F fc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v0 m' ms
/\ rt_after RT Σ' (bv_unsigned sp) lo m m' /\ rt_pres (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) m m'
/\ (forall o n, acc bsegs m o n -> o + n <= USTACK_TOP -> o + n <= top \/ bottom <= o -> acc bsegs m' o n)) c
/\ rt_pois RT Σ' = pois_drop bottom (rt_pois RT Σ)
/\ rt_live RT Σ' = rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ' = rt_credit RT Σ).

Lemma allocas_unpoison_of_lo : forall RT, allocas_unpoison_lo_contract RT -> allocas_unpoison_contract RT.
Proof.
intros RT H Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m top bottom lo
FDO MST E0 E1 HTB HT8 HB8 HSP HBT HST ART0 MI0 CALL.
apply (H Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m top bottom lo); try assumption.
destruct CALL as (_ & _ & LOR & _). unfold RT_STACK in LOR. lia.
Qed.
End B_TWIN.

Import ListNotations.
Open Scope Z_scope.

Definition allocas_unpoison_lo_contract (RT : rt_sig) : Prop :=
forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
F fc (m : mem) (top bottom lo : Z),
fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 top -> a1 = Z_to_bv 64 bottom ->
0 < top <= bottom -> top mod 8 = 0 -> bottom mod 8 = 0 -> lo <= top -> bottom <= USTACK_TOP - 16 ->
(forall e, In e (rt_pois RT Σ) -> (top <= pz_lo e /\ pz_hi e <= bottom) \/ bottom <= pz_lo e) ->
ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo ->
cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
t3 t4 t5 t6 F fc e_allocas_unpoison m)))
(fun c => exists (Σ' : rts RT),
ASTA RT Σ' PMc (fun ms => exists m' v0, ret_stF F fc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v0 m' ms
/\ rt_after RT Σ' (bv_unsigned sp) lo m m' /\ rt_pres (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) m m'
/\ (forall o n, acc asegs m o n -> o + n <= USTACK_TOP -> o + n <= top \/ bottom <= o -> acc asegs m' o n)) c
/\ rt_pois RT Σ' = pois_drop bottom (rt_pois RT Σ)
/\ rt_live RT Σ' = rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ' = rt_credit RT Σ).

Lemma allocas_unpoison_of_lo : forall RT, allocas_unpoison_lo_contract RT -> allocas_unpoison_contract RT.
Proof.
intros RT H Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m top bottom lo
FDO MST E0 E1 HTB HT8 HB8 HSP HBT HST ART0 MI0 CALL.
apply (H Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m top bottom lo); try assumption.
destruct CALL as (_ & _ & LOR & _). unfold RT_STACK in LOR. lia.
Qed.
