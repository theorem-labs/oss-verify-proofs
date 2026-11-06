(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Lib Require Import Mem Frame Cells Step Arr ImageA RzCPS.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.A Require Import Layout Shadow RT_iface RT_state RT_rep RT_facts TopA_iodefs RT_io.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Theorem rta_cli_ro : forall Σ m, ART_A Σ m -> cli_ro m.
Proof. intros Σ m HA. exact (cli_ro_of_io m (rta_io Σ m HA)). Qed.

Lemma ro_cells_app_c : forall (m : mem) A cs1 cs2,
  ro_cells asegs m A (cs1 ++ cs2) <-> ro_cells asegs m A cs1 /\ ro_cells asegs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros m A cs1 cs2. unfold ro_cells, cells_at.
  rewrite cells_wf_app, cells_bytes_app, bytes_at_app.
  split.
  - intros ((W1 & W2) & (B1 & B2)). rewrite (cells_bytes_length cs1 W1) in B2. tauto.
  - intros ((W1 & B1) & (W2 & B2)). rewrite (cells_bytes_length cs1 W1). tauto.
Qed.

Lemma ro_cells_mid : forall (m : mem) A (pre : list cell) (c : cell) (post : list cell),
  ro_cells asegs m A (pre ++ c :: post) -> ro_cells asegs m (A + Z.of_nat (cells_size pre)) [c].
Proof.
  intros m A pre c post H. apply ro_cells_app_c in H as [_ H]. change (c :: post) with ([c] ++ post) in H.
  apply ro_cells_app_c in H as [H _]. exact H.
Qed.

Section AtRTA.
Variables (Σ : rtsA) (m : mem).
Hypothesis HA : ART_A Σ m.

Lemma rta_vt_impl : ro_cells asegs m 0x109780
  [C8 (Z_to_bv 64 0x0); C8 (Z_to_bv 64 0x1097e0); C8 (Z_to_bv 64 0xc59ac); C8 (Z_to_bv 64 0xc5b38); C8 (Z_to_bv 64 0xc5cc4); C8 (Z_to_bv 64 0x9cd44); C8 (Z_to_bv 64 0x9f334); C8 (Z_to_bv 64 0x9f4c4)].
Proof using HA. apply (cli_ro_at m); [exact (rta_cli_ro Σ m HA)| cli_in]. Qed.

Lemma rta_vt_dpi : ro_cells asegs m 0x109840
  [C8 (Z_to_bv 64 0x0); C8 (Z_to_bv 64 0x1098c0); C8 (Z_to_bv 64 0xc5958); C8 (Z_to_bv 64 0x9cfa0); C8 (Z_to_bv 64 0x9f8d8); C8 (Z_to_bv 64 0xb2330); C8 (Z_to_bv 64 0xc4a1c); C8 (Z_to_bv 64 0xc51d0); C8 (Z_to_bv 64 0xc5d0c); C8 (Z_to_bv 64 0xc5e6c); C8 (Z_to_bv 64 0xc5fd4); C8 (Z_to_bv 64 0xc60c0)].
Proof using HA. apply (cli_ro_at m); [exact (rta_cli_ro Σ m HA)| cli_in]. Qed.

Lemma rta_got_nothrow : ro_cells asegs m 0x10d890
  [C8 (Z_to_bv 64 0x2d070)].
Proof using HA. apply (cli_ro_at m); [exact (rta_cli_ro Σ m HA)| cli_in]. Qed.

Lemma rta_cmp_real : ro_cells asegs m 0x10e9f8
  [C8 (Z_to_bv 64 0x1029d8); C8 (Z_to_bv 64 0x102908)].
Proof using HA. apply (cli_ro_at m); [exact (rta_cli_ro Σ m HA)| cli_in]. Qed.

Lemma rta_cmp_flags : ro_cells asegs m 0x1a71a6
  [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1)].
Proof using HA. apply (cli_ro_at m); [exact (rta_cli_ro Σ m HA)| cli_in]. Qed.

Lemma rta_num_lits : acc asegs m 0x288a0 10416 /\ acc asegs m 0x2b220 640.
Proof using HA.
  pose proof (rta_acc_lits Σ m HA) as F. rewrite Forall_forall in F. split.
  - exact (F (0x288a0, 10416) ltac:(unfold ACC_LITS; repeat (first [left; reflexivity | right]))).
  - exact (F (0x2b220, 640) ltac:(unfold ACC_LITS; repeat (first [left; reflexivity | right]))).
Qed.
End AtRTA.
