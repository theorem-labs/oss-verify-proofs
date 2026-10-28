(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac
     As0StepLib As0Tables ArtMem ArtAtomics ArtTac. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatClassId_b BatCachePop_b BatCombAlloc_b.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wokA := (wok AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

(* [comment removed for export] *)
Definition art_ca_hit_mem (M : word -> option byte) (sp ra s0 s1 s2 s3 s4 ca c cnt st csz : Z) : word -> option byte :=
  Wn 8 (Wn 4 (art_ca_frame M sp ra s0 s1 s2 s3 s4) (ca + 80 * c) (cnt - 1)) (ca + 2576) (st + csz).

(* [comment removed for export] *)
Definition art_ca_kept (r : reg) : Prop :=
  r <> 5%bv /\ r <> 6%bv /\ r <> 10%bv /\ r <> 11%bv /\ r <> 12%bv /\ r <> 13%bv /\ r <> 14%bv /\ r <> 15%bv /\ r <> 16%bv /\ r <> 17%bv.

Lemma class_id_small : forall s, 1 <= s <= 512 -> AsanTab.class_id s = (s + 31) / 32.
Proof. intros s Hs. unfold AsanTab.class_id. replace (s <=? 512) with true by (symmetry; apply Z.leb_le; lia). reflexivity. Qed.

Section FPX. Context {fx : PropExec.FPState}.

(* [comment removed for export] *)
End FPX.
