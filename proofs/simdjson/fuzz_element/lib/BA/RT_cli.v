(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Mem Frame Cells Step Arr ImageA RzCPS.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout RT_iface. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import RT_state RT_rep RT_facts TopA_iodefs RT_io.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section GWIN. Context {GWc : OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A.Shadow.GW}.
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

Lemma rta_vt_impl : ro_cells asegs m 0x164a00
  [C8 (Z_to_bv 64 0x0); C8 (Z_to_bv 64 0x164a60); C8 (Z_to_bv 64 0xe2d30); C8 (Z_to_bv 64 0xe2ebc); C8 (Z_to_bv 64 0xe3048); C8 (Z_to_bv 64 0xba0c8); C8 (Z_to_bv 64 0xbc6b8); C8 (Z_to_bv 64 0xbc848)].
Proof using HA. apply (cli_ro_at m); [exact (rta_cli_ro Σ m HA)| cli_in]. Qed.

Lemma rta_vt_dpi : ro_cells asegs m 0x164ac0
  [C8 (Z_to_bv 64 0x0); C8 (Z_to_bv 64 0x164b40); C8 (Z_to_bv 64 0xe2cdc); C8 (Z_to_bv 64 0xba324); C8 (Z_to_bv 64 0xbcc5c); C8 (Z_to_bv 64 0xcf6b4); C8 (Z_to_bv 64 0xe1da0); C8 (Z_to_bv 64 0xe2554); C8 (Z_to_bv 64 0xe3090); C8 (Z_to_bv 64 0xe31f0); C8 (Z_to_bv 64 0xe3358); C8 (Z_to_bv 64 0xe3444)].
Proof using HA. apply (cli_ro_at m); [exact (rta_cli_ro Σ m HA)| cli_in]. Qed.

Lemma rta_got_nothrow : ro_cells asegs m 0x16aec0
  [C8 (Z_to_bv 64 0x2eae8)].
Proof using HA. apply (cli_ro_at m); [exact (rta_cli_ro Σ m HA)| cli_in]. Qed.

Lemma rta_cmp_real : ro_cells asegs m 0x16c078
  [C8 (Z_to_bv 64 0x15c4f4); C8 (Z_to_bv 64 0x15c424)].
Proof using HA. apply (cli_ro_at m); [exact (rta_cli_ro Σ m HA)| cli_in]. Qed.

Lemma rta_cmp_flags : ro_cells asegs m 0x205866
  [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1)].
Proof using HA. apply (cli_ro_at m); [exact (rta_cli_ro Σ m HA)| cli_in]. Qed.

Lemma rta_num_lits : acc asegs m 0x2a2e0 10416 /\ acc asegs m 0x2cc60 640.
Proof using HA.
  pose proof (rta_acc_lits Σ m HA) as F. rewrite Forall_forall in F. split.
  - exact (F (0x2a2e0, 10416) ltac:(unfold ACC_LITS; repeat (first [left; reflexivity | right]))).
  - exact (F (0x2cc60, 640) ltac:(unfold ACC_LITS; repeat (first [left; reflexivity | right]))).
Qed.
End AtRTA.

End GWIN.
