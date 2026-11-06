(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim SeqExec StoreOk HeapIfaceA L5Defs L5AChk Bo0_code_8e368_8f368 Bo0_code_91368_92368.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.   (* [comment removed for export] *)

Module L5ACHK0.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom AsanUbsan.M.loaded_segments)) (only parsing).
Local Ltac dlit D := rewrite D; repeat f_equal; apply bv_eq; reflexivity.

(* [comment removed for export] *)
Lemma chk_8ecd0 (fx : FPState) R M a :
  getr R (reg 10) = Z_to_bv 64 (S a) -> getr R (reg 23) = Z_to_bv 64 a -> 0 <= a < 2 ^ 47 -> aacc M a 1 ->
  exists R', msteps RSEGS (st fx R 0x8f024 M) (st fx R' 0x8f02c M) /\ (forall k, (k < 32)%nat -> k <> 10%nat -> k <> 11%nat -> getr R' (reg k) = getr R (reg k)).
Proof.
  intros G10 G23 Ha ACC.
  refine (L5ACHK.asan_chk1 RSEGS fx R M 0x8f024 0x8f068 10 23 11 W_8f024 W_8f028 W_8f068 W_8f06c 64%bv 8128%bv a
            F_8f024 eq_refl ltac:(dlit D_8f024) F_8f028 eq_refl ltac:(dlit D_8f028) eq_refl F_8f068 eq_refl ltac:(dlit D_8f068) F_8f06c eq_refl ltac:(dlit D_8f06c) eq_refl
            ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) G10 G23 Ha ACC).
Qed.

(* [comment removed for export] *)
Lemma chk_8eb60 (fx : FPState) R M a :
  getr R (reg 14) = Z_to_bv 64 (S a) -> getr R (reg 10) = Z_to_bv 64 a -> 0 <= a < 2 ^ 47 -> aacc M a 1 ->
  exists R', msteps RSEGS (st fx R 0x8eeb4 M) (st fx R' 0x8eebc M) /\ (forall k, (k < 32)%nat -> k <> 14%nat -> k <> 15%nat -> getr R' (reg k) = getr R (reg k)).
Proof.
  intros G14 G10 Ha ACC.
  refine (L5ACHK.asan_chk1 RSEGS fx R M 0x8eeb4 0x8eedc 14 10 15 W_8eeb4 W_8eeb8 W_8eedc W_8eee0 36%bv 8156%bv a
            F_8eeb4 eq_refl ltac:(dlit D_8eeb4) F_8eeb8 eq_refl ltac:(dlit D_8eeb8) eq_refl F_8eedc eq_refl ltac:(dlit D_8eedc) F_8eee0 eq_refl ltac:(dlit D_8eee0) eq_refl
            ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) G14 G10 Ha ACC).
Qed.
(* [comment removed for export] *)
Lemma chk_8e4e8 (fx : FPState) R M a :
  getr R (reg 11) = Z_to_bv 64 (S a) -> getr R (reg 10) = Z_to_bv 64 a -> 0 <= a < 2 ^ 47 -> aacc M a 1 ->
  exists R', msteps RSEGS (st fx R 0x8e83c M) (st fx R' 0x8e844 M) /\ (forall k, (k < 32)%nat -> k <> 11%nat -> k <> 12%nat -> getr R' (reg k) = getr R (reg k)).
Proof.
  intros G11 G10 Ha ACC.
  refine (L5ACHK.asan_chk1 RSEGS fx R M 0x8e83c 0x8e878 11 10 12 W_8e83c W_8e840 W_8e878 W_8e87c 56%bv 8136%bv a
            F_8e83c eq_refl ltac:(dlit D_8e83c) F_8e840 eq_refl ltac:(dlit D_8e840) eq_refl F_8e878 eq_refl ltac:(dlit D_8e878) F_8e87c eq_refl ltac:(dlit D_8e87c) eq_refl
            ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) G11 G10 Ha ACC).
Qed.
(* [comment removed for export] *)
Lemma chk_8e974 (fx : FPState) R M a :
  getr R (reg 12) = Z_to_bv 64 (S a) -> getr R (reg 10) = Z_to_bv 64 a -> 0 <= a < 2 ^ 47 -> aacc M a 1 ->
  exists R', msteps RSEGS (st fx R 0x8ecc8 M) (st fx R' 0x8ecd0 M) /\ (forall k, (k < 32)%nat -> k <> 12%nat -> k <> 15%nat -> getr R' (reg k) = getr R (reg k)).
Proof.
  intros G12 G10 Ha ACC.
  refine (L5ACHK.asan_chk1 RSEGS fx R M 0x8ecc8 0x8ed1c 12 10 15 W_8ecc8 W_8eccc W_8ed1c W_8ed20 80%bv 8112%bv a
            F_8ecc8 eq_refl ltac:(dlit D_8ecc8) F_8eccc eq_refl ltac:(dlit D_8eccc) eq_refl F_8ed1c eq_refl ltac:(dlit D_8ed1c) F_8ed20 eq_refl ltac:(dlit D_8ed20) eq_refl
            ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) G12 G10 Ha ACC).
Qed.
(* [comment removed for export] *)
Lemma chk_91d08 (fx : FPState) R M a :
  getr R (reg 12) = Z_to_bv 64 (S a) -> getr R (reg 10) = Z_to_bv 64 a -> 0 <= a < 2 ^ 47 -> aacc M a 1 ->
  exists R', msteps RSEGS (st fx R 0x9205c M) (st fx R' 0x92064 M) /\ (forall k, (k < 32)%nat -> k <> 12%nat -> k <> 14%nat -> getr R' (reg k) = getr R (reg k)).
Proof.
  intros G12 G10 Ha ACC.
  refine (L5ACHK.asan_chk1 RSEGS fx R M 0x9205c 0x920b8 12 10 14 W_9205c W_92060 W_920b8 W_920bc 88%bv 8104%bv a
            F_9205c eq_refl ltac:(dlit D_9205c) F_92060 eq_refl ltac:(dlit D_92060) eq_refl F_920b8 eq_refl ltac:(dlit D_920b8) F_920bc eq_refl ltac:(dlit D_920bc) eq_refl
            ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) G12 G10 Ha ACC).
Qed.
End L5ACHK0.
