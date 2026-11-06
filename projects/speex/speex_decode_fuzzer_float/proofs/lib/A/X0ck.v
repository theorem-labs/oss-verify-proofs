(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cy X1cp X1cj X1dd X1cg X1cs X1cm X1da.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS Require Import X0k2.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0bp X0j9 X0ec X0j1 X0gi X0hr X0hb X0hi
X0j3 X0hn X0hs X0fy X0fg X0g4 X0e4 X0e8 X0d9 X0e5 X0ci X0cn.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X12c X14x X173 X18c X17w X183 X19m X188 X18d X16j X161 X16p X14p X14t X13u X14q X133 X138.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14x OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X173 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X18c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X17w OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X183 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X19m OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X188 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X18d OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X16j OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X161 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X16p OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14p OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14t OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X13u OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14q OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X133 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X138.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.

Section DG.
Variable Σ : rtsA.
Hypothesis HG : geo_ok Σ.
#[local] Notation L := (lay Σ).
#[local] Notation T := (l_T (lay Σ)).
#[local] Notation TCX := (l_TCX (lay Σ)).
#[local] Notation SB := (l_SB (lay Σ)).

Lemma dg_ok : T_ok (l_ACEIL L) T /\ SB_ok (l_ACEIL L) SB /\ tsep (l_ACEIL L) SB T TCX.
Proof using HG.
clear - HG.
pose proof (dk_geo Σ HG) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8).
pose proof (g_grant Σ HG T 4096 ltac:(unfold startup_grants; right; right; left; reflexivity)) as (T1 & T2 & T3 & T4 & T5).
pose proof (g_grant Σ HG TCX 0x10000 ltac:(unfold startup_grants; right; right; right; left; reflexivity)) as (X1 & X2 & X3 & X4 & X5).
pose proof (g_apart Σ HG 0 2 _ _ ltac:(lia) eq_refl eq_refl) as A02. pose proof (g_apart Σ HG 0 3 _ _ ltac:(lia) eq_refl eq_refl) as A03.
pose proof (g_apart Σ HG 2 3 _ _ ltac:(lia) eq_refl eq_refl) as A23. cbn [fst snd] in A02, A03, A23. unfold apart in *.
pose proof (g_prb Σ HG) as (P1 & P2 & P3).
unfold tsep, T_ok, SB_ok, img_hull_lo, img_hull_hi, kHighShadowEnd.
unfold SEGTOP_A, K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi, SHB in *. repeat split; lia.
Qed.

End DG.

Lemma dg_consts : forall L (m : mem), consts_rep L m ->
inst_cells (l_SB L) m /\ mm_gcells m /\ thread_cells (l_TCX L) (l_T L) m /\ ps_cells m /\ stk bsegs m (l_T L + 2768) (l_T L + 3168)
/\ rw_cells bsegs m (l_T L + 0xc60) [C1 (Z_to_bv 8 0)].
Proof.
intros L m (I1 & I2 & I3 & _ & I5 & _ & _ & IC). split; [exact I1|]. split; [exact I2|]. split; [exact I3|]. split; [exact I5|].
unfold icells_rep in IC. destruct IC as (C1 & IC).
repeat match type of IC with _ /\ ?R => let X := fresh "X" in destruct IC as [X IC] end.
split; [|exact C1].
match goal with H : stk bsegs m (l_T L + 2768) (l_T L + 3168) |- _ => exact H end.
Qed.
End B_TWIN.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.

Section DG.
Variable Σ : rtsA.
Hypothesis HG : geo_ok Σ.
#[local] Notation L := (lay Σ).
#[local] Notation T := (l_T (lay Σ)).
#[local] Notation TCX := (l_TCX (lay Σ)).
#[local] Notation SB := (l_SB (lay Σ)).

Lemma dg_ok : T_ok (l_ACEIL L) T /\ SB_ok (l_ACEIL L) SB /\ tsep (l_ACEIL L) SB T TCX.
Proof using HG.
clear - HG.
pose proof (dk_geo Σ HG) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8).
pose proof (g_grant Σ HG T 4096 ltac:(unfold startup_grants; right; right; left; reflexivity)) as (T1 & T2 & T3 & T4 & T5).
pose proof (g_grant Σ HG TCX 0x10000 ltac:(unfold startup_grants; right; right; right; left; reflexivity)) as (X1 & X2 & X3 & X4 & X5).
pose proof (g_apart Σ HG 0 2 _ _ ltac:(lia) eq_refl eq_refl) as A02. pose proof (g_apart Σ HG 0 3 _ _ ltac:(lia) eq_refl eq_refl) as A03.
pose proof (g_apart Σ HG 2 3 _ _ ltac:(lia) eq_refl eq_refl) as A23. cbn [fst snd] in A02, A03, A23. unfold apart in *.
pose proof (g_prb Σ HG) as (P1 & P2 & P3).
unfold tsep, T_ok, SB_ok, img_hull_lo, img_hull_hi, kHighShadowEnd.
unfold SEGTOP_A, K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi, SHB in *. repeat split; lia.
Qed.

End DG.

Lemma dg_consts : forall L (m : mem), consts_rep L m ->
inst_cells (l_SB L) m /\ mm_gcells m /\ thread_cells (l_TCX L) (l_T L) m /\ ps_cells m /\ stk asegs m (l_T L + 2768) (l_T L + 3168)
/\ rw_cells asegs m (l_T L + 0xc60) [C1 (Z_to_bv 8 0)].
Proof.
intros L m (I1 & I2 & I3 & _ & I5 & _ & _ & IC). split; [exact I1|]. split; [exact I2|]. split; [exact I3|]. split; [exact I5|].
unfold icells_rep in IC. destruct IC as (C1 & IC).
repeat match type of IC with _ /\ ?R => let X := fresh "X" in destruct IC as [X IC] end.
split; [|exact C1].
match goal with H : stk asegs m (l_T L + 2768) (l_T L + 3168) |- _ => exact H end.
Qed.
