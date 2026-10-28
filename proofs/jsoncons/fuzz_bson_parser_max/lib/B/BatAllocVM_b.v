(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatSim StoreOk ArtMem ArtRegs ArtAtomics ArtTac. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatAllocV_b.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.

#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).

Lemma art_e_magic : forall M sp ab rz n b1, 32 <= sp -> sp < 2 ^ 64 -> 0 <= ab -> ab + rz < 2 ^ 64 -> 16 <= rz -> rz <> 16 -> rz mod 16 = 0 -> apart (sp - 32) 32 ab 16 ->
  cellA (art_e_mem M sp ab rz n b1) ab 8 0xcc6e96b9cc6e96b9 /\ cellA (art_e_mem M sp ab rz n b1) (ab + 8) 8 (ab + rz - 16).
Proof.
  intros M sp ab rz n b1 Hsp Hsp' Hab Hab' Hrz Nrz Mrz A. unfold art_e_mem.
  destruct (Z.eqb_spec rz 16) as [E|_]; [contradiction|].
  assert (H32 : 32 <= rz). { pose proof (Z.div_mod rz 16 ltac:(lia)) as D. rewrite Mrz in D. lia. }
  split; zcell.
Qed.
