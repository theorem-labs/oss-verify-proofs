(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0035. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StreamSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0035.ArtMem OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0035.ArtRuns OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0035.ArtRunsMem.
Import ListNotations. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation wrA := (wr Asan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

Definition art_iatab_n : nat := Z.to_nat 0x81030.
Lemma art_wseg_iatab : wseg_ok ASEGS (Z_to_bv 64 0x160c80) art_iatab_n = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma art_iatab_n_Z : Z.of_nat art_iatab_n = 0x81030. Proof. unfold art_iatab_n. apply Z2Nat.id. lia. Qed.
Global Opaque art_iatab_n.
Lemma art_wseg_iaflag : wseg_ok ASEGS (Z_to_bv 64 0x1ef508) 4 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

Lemma art_img_wr_iatab : forall (M : word -> option byte) a n, 0x160c80 <= a -> 0 <= n -> a + n <= 0x160c80 + 0x81030 -> wrA M a n.
Proof.
  intros M a n Ha Hn0 Hn d k Hd Hk.
  apply (store_ok_window ASEGS M (Z_to_bv 64 0x160c80) (Z_to_bv 64 (a + d)) art_iatab_n k 0x160c80 (0x160c80 + 0x81030));
    first [exact art_wseg_iatab | (rewrite art_iatab_n_Z; reflexivity) | reflexivity | lia | (rewrite art_u_lit by lia; lia)].
Qed.
Lemma art_img_wr_iaflag : forall (M : word -> option byte) a n, 0x1ef508 <= a -> 0 <= n -> a + n <= 0x1ef508 + 4 -> wrA M a n.
Proof.
  intros M a n Ha Hn0 Hn d k Hd Hk.
  apply (store_ok_window ASEGS M (Z_to_bv 64 0x1ef508) (Z_to_bv 64 (a + d)) 4%nat k 0x1ef508 (0x1ef508 + 4));
    first [exact art_wseg_iaflag | reflexivity | lia | (rewrite art_u_lit by lia; lia)].
Qed.
