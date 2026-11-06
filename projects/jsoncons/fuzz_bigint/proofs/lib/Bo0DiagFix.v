(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim SeqExec StoreOk L5Defs L5Kn L5KnA Bo0DiagKit Bo0DiagGlue.
Import ListNotations. Open Scope Z_scope. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import DK. Import DG.
Module DFX.
Lemma u32_of_u8s (M : word -> option byte) a a1 a2 a3 w b0 b1 b2 b3 : 0 <= a -> a + 4 <= 2 ^ 64 -> a1 = a + 1 -> a2 = a + 2 -> a3 = a + 3 ->
  L5.u8_at RSEGS M a b0 -> L5.u8_at RSEGS M a1 b1 -> L5.u8_at RSEGS M a2 b2 -> L5.u8_at RSEGS M a3 b3 ->
  map bv_unsigned (word_to_le_bytes 4 (Z_to_bv 64 w)) = [b0; b1; b2; b3] -> 0 <= b0 < 256 -> 0 <= b1 < 256 -> 0 <= b2 < 256 -> 0 <= b3 < 256 -> L5.u32_at RSEGS M a w.
Proof.
  intros Ha Hb -> -> -> B0 B1 B2 B3 E R0 R1 R2 R3. unfold L5.u32_at.
  assert (EL : word_to_le_bytes 4 (Z_to_bv 64 w) = [Z_to_bv 8 b0; Z_to_bv 8 b1; Z_to_bv 8 b2; Z_to_bv 8 b3]).
  { apply list_bv_eq. rewrite E. cbn [map]. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. rewrite !Z.mod_small by lia. reflexivity. }
  rewrite EL. unfold L5.u8_at in *.
  apply rdn_cons; [lia | cbn; lia | exact B0 |].
  apply rdn_cons; [lia | cbn; lia | exact B1 |].
  replace (a + 1 + 1) with (a + 2) by lia. apply rdn_cons; [lia | cbn; lia | exact B2 |].
  replace (a + 2 + 1) with (a + 3) by lia. apply rdn_cons; [lia | cbn; lia | exact B3 |]. reflexivity.
Qed.
End DFX.
