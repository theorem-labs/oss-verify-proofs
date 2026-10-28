(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Lib Require Import Mem Frame Cells Step Arr ImageA RzCPS.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.B Require Import Layout RT_iface RT_state RT_rep RT_facts TopA_iodefs RT_io.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section GWIN. Context {GWc : OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.A.Shadow.GW}.
Theorem rta_cli_ro : forall Σ m, ART_A Σ m -> cli_ro m.
Proof. intros Σ m HA. exact (cli_ro_of_io m (rta_io Σ m HA)). Qed.

Lemma ro_cells_app_c : forall (m : mem) A cs1 cs2,
  ro_cells bsegs m A (cs1 ++ cs2) <-> ro_cells bsegs m A cs1 /\ ro_cells bsegs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros m A cs1 cs2. unfold ro_cells, cells_at.
  rewrite cells_wf_app, cells_bytes_app, bytes_at_app.
  split.
  - intros ((W1 & W2) & (B1 & B2)). rewrite (cells_bytes_length cs1 W1) in B2. tauto.
  - intros ((W1 & B1) & (W2 & B2)). rewrite (cells_bytes_length cs1 W1). tauto.
Qed.

Lemma ro_cells_mid : forall (m : mem) A (pre : list cell) (c : cell) (post : list cell),
  ro_cells bsegs m A (pre ++ c :: post) -> ro_cells bsegs m (A + Z.of_nat (cells_size pre)) [c].
Proof.
  intros m A pre c post H. apply ro_cells_app_c in H as [_ H]. change (c :: post) with ([c] ++ post) in H.
  apply ro_cells_app_c in H as [H _]. exact H.
Qed.

Section AtRTA.
Variables (Σ : rtsA) (m : mem).
Hypothesis HA : ART_A Σ m.

Lemma rta_vt_impl : ro_cells bsegs m 0x1689a0
  [C8 (Z_to_bv 64 0x0); C8 (Z_to_bv 64 0x168a00); C8 (Z_to_bv 64 0xe6c2c); C8 (Z_to_bv 64 0xe6dcc); C8 (Z_to_bv 64 0xe6f6c); C8 (Z_to_bv 64 0xb30ec); C8 (Z_to_bv 64 0xb622c); C8 (Z_to_bv 64 0xb6414)].
Proof using HA. apply (cli_ro_at m); [exact (rta_cli_ro Σ m HA)| cli_in]. Qed.

Lemma rta_vt_dpi : ro_cells bsegs m 0x168a60
  [C8 (Z_to_bv 64 0x0); C8 (Z_to_bv 64 0x168ae0); C8 (Z_to_bv 64 0xe6bd8); C8 (Z_to_bv 64 0xb338c); C8 (Z_to_bv 64 0xb6868); C8 (Z_to_bv 64 0xce250); C8 (Z_to_bv 64 0xe5ae8); C8 (Z_to_bv 64 0xe638c); C8 (Z_to_bv 64 0xe6fb4); C8 (Z_to_bv 64 0xe7128); C8 (Z_to_bv 64 0xe729c); C8 (Z_to_bv 64 0xe7388)].
Proof using HA. apply (cli_ro_at m); [exact (rta_cli_ro Σ m HA)| cli_in]. Qed.

Lemma rta_got_nothrow : ro_cells bsegs m 0x16ee88
  [C8 (Z_to_bv 64 0x2cf28)].
Proof using HA. apply (cli_ro_at m); [exact (rta_cli_ro Σ m HA)| cli_in]. Qed.

Lemma rta_cmp_real : ro_cells bsegs m 0x170008
  [C8 (Z_to_bv 64 0x160854); C8 (Z_to_bv 64 0x160784)].
Proof using HA. apply (cli_ro_at m); [exact (rta_cli_ro Σ m HA)| cli_in]. Qed.

Lemma rta_cmp_flags : ro_cells bsegs m 0x208d66
  [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1)].
Proof using HA. apply (cli_ro_at m); [exact (rta_cli_ro Σ m HA)| cli_in]. Qed.

Lemma rta_num_lits : acc bsegs m 0x28700 10416 /\ acc bsegs m 0x2b080 640.
Proof using HA.
  pose proof (rta_acc_lits Σ m HA) as F. rewrite Forall_forall in F. split.
  - exact (F (0x28700, 10416) ltac:(unfold ACC_LITS; repeat (first [left; reflexivity | right]))).
  - exact (F (0x2b080, 640) ltac:(unfold ACC_LITS; repeat (first [left; reflexivity | right]))).
Qed.
End AtRTA.

End GWIN.
