(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim SeqExec StoreOk HeapIfaceA L5Defs L5AChk As0_code_8e368_8f368 As0_code_91368_92368.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.   (* [comment removed for export] *)

Module L5ACHK0.
Abbreviation RSEGS := Asan.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Asan.M.loaded_segments)) (only parsing).
Local Ltac dlit D := rewrite D; repeat f_equal; apply bv_eq; reflexivity.

(* [comment removed for export] *)
Lemma chk_8e924 (fx : FPState) R M a :
  getr R (reg 10) = Z_to_bv 64 (S a) -> getr R (reg 24) = Z_to_bv 64 a -> 0 <= a < 2 ^ 47 -> aacc M a 1 ->
  exists R', msteps RSEGS (st fx R 0x8ec78 M) (st fx R' 0x8ec80 M) /\ (forall k, (k < 32)%nat -> k <> 10%nat -> k <> 11%nat -> getr R' (reg k) = getr R (reg k)).
Proof.
  intros G10 G24 Ha ACC.
  refine (L5ACHK.asan_chk1 RSEGS fx R M 0x8ec78 0x8ecb8 10 24 11 W_8ec78 W_8ec7c W_8ecb8 W_8ecbc 60%bv 8132%bv a
            F_8ec78 eq_refl ltac:(dlit D_8ec78) F_8ec7c eq_refl ltac:(dlit D_8ec7c) eq_refl F_8ecb8 eq_refl ltac:(dlit D_8ecb8) F_8ecbc eq_refl ltac:(dlit D_8ecbc) eq_refl
            ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) G10 G24 Ha ACC).
Qed.

(* [comment removed for export] *)
Lemma chk_8e810 (fx : FPState) R M a :
  getr R (reg 13) = Z_to_bv 64 (S a) -> getr R (reg 10) = Z_to_bv 64 a -> 0 <= a < 2 ^ 47 -> aacc M a 1 ->
  exists R', msteps RSEGS (st fx R 0x8eb64 M) (st fx R' 0x8eb6c M) /\ (forall k, (k < 32)%nat -> k <> 13%nat -> k <> 14%nat -> getr R' (reg k) = getr R (reg k)).
Proof.
  intros G13 G10 Ha ACC.
  refine (L5ACHK.asan_chk1 RSEGS fx R M 0x8eb64 0x8eb84 13 10 14 W_8eb64 W_8eb68 W_8eb84 W_8eb88 28%bv 8164%bv a
            F_8eb64 eq_refl ltac:(dlit D_8eb64) F_8eb68 eq_refl ltac:(dlit D_8eb68) eq_refl F_8eb84 eq_refl ltac:(dlit D_8eb84) F_8eb88 eq_refl ltac:(dlit D_8eb88) eq_refl
            ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) G13 G10 Ha ACC).
Qed.
(* [comment removed for export] *)
Lemma chk_8e26c (fx : FPState) R M a :
  getr R (reg 11) = Z_to_bv 64 (S a) -> getr R (reg 10) = Z_to_bv 64 a -> 0 <= a < 2 ^ 47 -> aacc M a 1 ->
  exists R', msteps RSEGS (st fx R 0x8e5c0 M) (st fx R' 0x8e5c8 M) /\ (forall k, (k < 32)%nat -> k <> 11%nat -> k <> 12%nat -> getr R' (reg k) = getr R (reg k)).
Proof.
  intros G11 G10 Ha ACC.
  refine (L5ACHK.asan_chk1 RSEGS fx R M 0x8e5c0 0x8e5f8 11 10 12 W_8e5c0 W_8e5c4 W_8e5f8 W_8e5fc 52%bv 8140%bv a
            F_8e5c0 eq_refl ltac:(dlit D_8e5c0) F_8e5c4 eq_refl ltac:(dlit D_8e5c4) eq_refl F_8e5f8 eq_refl ltac:(dlit D_8e5f8) F_8e5fc eq_refl ltac:(dlit D_8e5fc) eq_refl
            ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) G11 G10 Ha ACC).
Qed.
(* [comment removed for export] *)
Lemma chk_8e654 (fx : FPState) R M a :
  getr R (reg 12) = Z_to_bv 64 (S a) -> getr R (reg 10) = Z_to_bv 64 a -> 0 <= a < 2 ^ 47 -> aacc M a 1 ->
  exists R', msteps RSEGS (st fx R 0x8e9a8 M) (st fx R' 0x8e9b0 M) /\ (forall k, (k < 32)%nat -> k <> 12%nat -> k <> 15%nat -> getr R' (reg k) = getr R (reg k)).
Proof.
  intros G12 G10 Ha ACC.
  refine (L5ACHK.asan_chk1 RSEGS fx R M 0x8e9a8 0x8e9f0 12 10 15 W_8e9a8 W_8e9ac W_8e9f0 W_8e9f4 68%bv 8124%bv a
            F_8e9a8 eq_refl ltac:(dlit D_8e9a8) F_8e9ac eq_refl ltac:(dlit D_8e9ac) eq_refl F_8e9f0 eq_refl ltac:(dlit D_8e9f0) F_8e9f4 eq_refl ltac:(dlit D_8e9f4) eq_refl
            ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) G12 G10 Ha ACC).
Qed.
(* [comment removed for export] *)
Lemma chk_9144c (fx : FPState) R M a :
  getr R (reg 12) = Z_to_bv 64 (S a) -> getr R (reg 10) = Z_to_bv 64 a -> 0 <= a < 2 ^ 47 -> aacc M a 1 ->
  exists R', msteps RSEGS (st fx R 0x917a0 M) (st fx R' 0x917a8 M) /\ (forall k, (k < 32)%nat -> k <> 12%nat -> k <> 14%nat -> getr R' (reg k) = getr R (reg k)).
Proof.
  intros G12 G10 Ha ACC.
  refine (L5ACHK.asan_chk1 RSEGS fx R M 0x917a0 0x917f0 12 10 14 W_917a0 W_917a4 W_917f0 W_917f4 76%bv 8116%bv a
            F_917a0 eq_refl ltac:(dlit D_917a0) F_917a4 eq_refl ltac:(dlit D_917a4) eq_refl F_917f0 eq_refl ltac:(dlit D_917f0) F_917f4 eq_refl ltac:(dlit D_917f4) eq_refl
            ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) G12 G10 Ha ACC).
Qed.
End L5ACHK0.
