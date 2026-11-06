(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatSim StoreOk StreamSim ArtMem ArtRuns ArtRunsMem.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Local Ltac vmc_refl := first [ lazymatch goal with |- _ = ?b => vm_cast_no_check (@eq_refl _ b) end | vm_compute; reflexivity ].
#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

Definition art_iatab_n : nat := Z.to_nat 0x81030.
Lemma art_wseg_iatab : wseg_ok ASEGS (Z_to_bv 64 0x15ef00) art_iatab_n = true.
Proof. vmc_refl. Qed.
Lemma art_iatab_n_Z : Z.of_nat art_iatab_n = 0x81030. Proof. unfold art_iatab_n. apply Z2Nat.id. lia. Qed.
Global Opaque art_iatab_n.
Lemma art_wseg_iaflag : wseg_ok ASEGS (Z_to_bv 64 0x1ed788) 4 = true.
Proof. vmc_refl. Qed.

Lemma art_img_wr_iatab : forall (M : word -> option byte) a n, 0x15ef00 <= a -> 0 <= n -> a + n <= 0x15ef00 + 0x81030 -> wrA M a n.
Proof.
  intros M a n Ha Hn0 Hn d k Hd Hk.
  apply (store_ok_window ASEGS M (Z_to_bv 64 0x15ef00) (Z_to_bv 64 (a + d)) art_iatab_n k 0x15ef00 (0x15ef00 + 0x81030));
    first [exact art_wseg_iatab | (rewrite art_iatab_n_Z; reflexivity) | reflexivity | lia | (rewrite art_u_lit by lia; lia)].
Qed.
Lemma art_img_wr_iaflag : forall (M : word -> option byte) a n, 0x1ed788 <= a -> 0 <= n -> a + n <= 0x1ed788 + 4 -> wrA M a n.
Proof.
  intros M a n Ha Hn0 Hn d k Hd Hk.
  apply (store_ok_window ASEGS M (Z_to_bv 64 0x1ed788) (Z_to_bv 64 (a + d)) 4%nat k 0x1ed788 (0x1ed788 + 4));
    first [exact art_wseg_iaflag | reflexivity | lia | (rewrite art_u_lit by lia; lia)].
Qed.
