(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac Mem Frame Cells Step Arr ImageA Exec RzCPS.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Common Require Import AsanAcct.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow R_sizeclass.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface R_cache_defs R_prim_defs R_glue_defs R_m2s R_thread R_poison R_prim_kit RT_state RT_rep RT_trans RT_freelift RT_geo0 RT_fkit RT_freestate RT_drain_defs RT_drain_kit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
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

(* [comment removed for export] *)
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
