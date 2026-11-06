(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface
     AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 SegRun SegPlan Eb0PlanKit AsanPlanCore
     BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA
     PeBSlowTP2 PeBSlowTP3 PeBSlowTP4 PeBSlowTP5.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module PMBSLTU.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom AsanUbsan.M.loaded_segments)) (only parsing).

Lemma bstS_uni fx R M (V : nat -> Z) (k SZ NC NO : Z) : 0 <= k <= 10 -> SZ = 32 * 2 ^ k -> NC = 2 ^ (k + 1) -> NO = 2 ^ k ->
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 52%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 11) = Z_to_bv 64 (V 34%nat) -> getr R (reg 12) = Z_to_bv 64 (V 35%nat) -> getr R (reg 13) = Z_to_bv 64 (V 52%nat) ->
  140735332491264 <= (V 2%nat) <= 140737488355328 -> PMBSLTP2.aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 4096) 4096 -> L5KA.zeros_at M (((V 2%nat) / 8) + 2147450368) 512 ->
  L5.img_clear M 1273856 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 6930432 <= (V 33%nat) <= 140737488355295 ->
  PMBSLTP2.aligned (V 33%nat) 8 -> (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 24 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 3 -> (((V 2%nat) - 4096) + 4096 <= (V 33%nat) \/ (V 33%nat) + 24 <= ((V 2%nat) - 4096)) ->
  (65536 + 6864896 <= (V 33%nat) \/ (V 33%nat) + 24 <= 65536) -> L5.u64_at RSEGS M (V 33%nat) (V 36%nat) -> L5.u64_at RSEGS M ((V 33%nat) + 8) ((V 36%nat) + SZ) -> L5.u64_at RSEGS M ((V 33%nat) + 16) ((V 36%nat) + SZ) ->
  4096 <= (V 36%nat) <= 140737488355296 -> PMBSLTP2.aligned (V 36%nat) 16 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 192) <= bv_unsigned a < ((V 2%nat) - 192) + 192) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 192) <= i < ((V 2%nat) - 192) + 192) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xbc26c M) (st fx' R' 0x136668 M')
        /\ (forall x, In x PMBSLTP2.KS_bstS0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 743076
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 176)
        /\ getr R' (reg 8) = Z_to_bv 64 ((V 2%nat) - 80)
        /\ getr R' (reg 9) = Z_to_bv 64 NC
        /\ getr R' (reg 10) = Z_to_bv 64 (2 * SZ)
        /\ getr R' (reg 11) = Z_to_bv 64 NC
        /\ getr R' (reg 12) = Z_to_bv 64 1335544
        /\ getr R' (reg 13) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 14) = Z_to_bv 64 0
        /\ getr R' (reg 18) = Z_to_bv 64 ((V 2%nat) - 104)
        /\ getr R' (reg 19) = Z_to_bv 64 NO
        /\ getr R' (reg 20) = Z_to_bv 64 ((((V 2%nat) - 80) / 8) + 2147450880)
        /\ getr R' (reg 21) = Z_to_bv 64 2147450880
        /\ getr R' (reg 22) = Z_to_bv 64 2147450880
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) (V 33%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 168) ((((V 33%nat) + 8) / 8) + 2147450880)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 160) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 152) (V 35%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 144) (V 52%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 136) (V 33%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 128) ((V 33%nat) + 8)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 120) 770868
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (bv_unsigned (getr R (reg 22)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (bv_unsigned (getr R (reg 21)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (bv_unsigned (getr R (reg 20)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))).
Proof.
  intros Hk ESZ ENC ENO. subst SZ NC NO.
  assert (KC : k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10) by Lia.lia.
  destruct KC as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]].
  - exact (PMBSLTP2.bstS0_conc fx R M V).
  - exact (PMBSLTP2.bstS1_conc fx R M V).
  - exact (PMBSLTP2.bstS2_conc fx R M V).
  - exact (PMBSLTP2.bstS3_conc fx R M V).
  - exact (PMBSLTP2.bstS4_conc fx R M V).
  - exact (PMBSLTP2.bstS5_conc fx R M V).
  - exact (PMBSLTP2.bstS6_conc fx R M V).
  - exact (PMBSLTP2.bstS7_conc fx R M V).
  - exact (PMBSLTP2.bstS8_conc fx R M V).
  - exact (PMBSLTP2.bstS9_conc fx R M V).
  - exact (PMBSLTP2.bstS10_conc fx R M V).
Qed.

Lemma bstG_uni fx R M (V : nat -> Z) (k SZ NC NO : Z) : 0 <= k <= 10 -> SZ = 32 * 2 ^ k -> NC = 2 ^ (k + 1) -> NO = 2 ^ k ->
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 52%nat) < 2 ^ 64 -> 0 <= (V 53%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 176) -> getr R (reg 8) = Z_to_bv 64 ((V 2%nat) - 80) -> getr R (reg 9) = Z_to_bv 64 NC -> getr R (reg 10) = Z_to_bv 64 (V 40%nat) -> getr R (reg 18) = Z_to_bv 64 ((V 2%nat) - 104) -> getr R (reg 19) = Z_to_bv 64 NO -> getr R (reg 20) = Z_to_bv 64 ((((V 2%nat) - 80) / 8) + 2147450880) -> getr R (reg 21) = Z_to_bv 64 2147450880 -> getr R (reg 22) = Z_to_bv 64 2147450880 ->
  140735332491264 <= (V 2%nat) <= 140737488355328 -> PMBSLTP3.aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 4096) 4096 -> L5KA.zeros_at M (((V 2%nat) / 8) + 2147450368) 512 ->
  L5.img_clear M 1273856 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 6930432 <= (V 33%nat) <= 140737488355295 ->
  PMBSLTP3.aligned (V 33%nat) 8 -> (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 24 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 3 -> (((V 2%nat) - 4096) + 4096 <= (V 33%nat) \/ (V 33%nat) + 24 <= ((V 2%nat) - 4096)) ->
  (65536 + 6864896 <= (V 33%nat) \/ (V 33%nat) + 24 <= 65536) -> L5.u64_at RSEGS M (V 33%nat) (V 36%nat) -> L5.u64_at RSEGS M ((V 33%nat) + 8) ((V 36%nat) + SZ) -> L5.u64_at RSEGS M ((V 33%nat) + 16) ((V 36%nat) + SZ) ->
  4096 <= (V 36%nat) <= 140737488355296 -> PMBSLTP3.aligned (V 36%nat) 16 -> 6930432 <= (V 34%nat) <= 140737488355324 -> PMBSLTP3.aligned (V 34%nat) 4 ->
  (2147446784 + 17592186048512 <= (V 34%nat) \/ (V 34%nat) + 4 <= 2147446784) -> L5KA.zeros_at M (((V 34%nat) / 8) + 2147450880) 1 -> L5.u32_at RSEGS M (V 34%nat) (V 38%nat) -> (((V 2%nat) - 4096) + 4096 <= (V 34%nat) \/ (V 34%nat) + 4 <= ((V 2%nat) - 4096)) ->
  6930432 <= (V 35%nat) <= 140737488355320 -> PMBSLTP3.aligned (V 35%nat) 8 -> (2147446784 + 17592186048512 <= (V 35%nat) \/ (V 35%nat) + 8 <= 2147446784) -> L5KA.zeros_at M (((V 35%nat) / 8) + 2147450880) 1 ->
  L5.u64_at RSEGS M (V 35%nat) (V 39%nat) -> (((V 2%nat) - 4096) + 4096 <= (V 35%nat) \/ (V 35%nat) + 8 <= ((V 2%nat) - 4096)) -> ((V 33%nat) + 24 <= (V 34%nat) \/ (V 34%nat) + 4 <= (V 33%nat)) -> ((V 33%nat) + 24 <= (V 35%nat) \/ (V 35%nat) + 8 <= (V 33%nat)) ->
  0 <= (V 38%nat) <= 2147483647 -> 0 <= (V 39%nat) <= 18446744073709551615 -> 6930432 <= (V 52%nat) <= 140737488355327 -> (2147446784 + 17592186048512 <= (V 52%nat) \/ (V 52%nat) + 1 <= 2147446784) ->
  L5.u8_at RSEGS M (V 52%nat) (V 53%nat) -> (((V 2%nat) - 4096) + 4096 <= (V 52%nat) \/ (V 52%nat) + 1 <= ((V 2%nat) - 4096)) -> PMBSLTP3.aligned (V 52%nat) 8 -> L5.u8_at RSEGS M (((V 52%nat) / 8) + 2147450880) 1 ->
  ((V 33%nat) + 24 <= (V 52%nat) \/ (V 52%nat) + 1 <= (V 33%nat)) -> 0 <= (V 53%nat) <= 255 -> 4096 <= (V 40%nat) <= (140737488355328 - 2 * SZ) -> PMBSLTP3.aligned (V 40%nat) 16 ->
  L5.writable RSEGS M ((V 40%nat) + SZ) 32 -> L5KA.zeros_at M ((((V 40%nat) + SZ) / 8) + 2147450880) 4 -> (2147446784 + 17592186048512 <= ((V 40%nat) + SZ) \/ ((V 40%nat) + SZ) + 32 <= 2147446784) -> 4096 <= ((V 40%nat) + SZ) <= 140737488355296 ->
  (((V 2%nat) - 4096) + 4096 <= ((V 40%nat) + SZ) \/ ((V 40%nat) + SZ) + 32 <= ((V 2%nat) - 4096)) -> ((V 33%nat) + 24 <= ((V 40%nat) + SZ) \/ ((V 40%nat) + SZ) + 32 <= (V 33%nat)) -> ((V 34%nat) + 4 <= ((V 40%nat) + SZ) \/ ((V 40%nat) + SZ) + 32 <= (V 34%nat)) -> ((V 35%nat) + 8 <= ((V 40%nat) + SZ) \/ ((V 40%nat) + SZ) + 32 <= (V 35%nat)) ->
  (65536 + 6864896 <= ((V 40%nat) + SZ) \/ ((V 40%nat) + SZ) + 32 <= 65536) -> ((V 52%nat) + 1 <= ((V 40%nat) + SZ) \/ ((V 40%nat) + SZ) + 32 <= (V 52%nat)) -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 43%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 44%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 24) (V 45%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 46%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 47%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 48%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 56) (V 49%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 120) 770868 -> L5.u64_at RSEGS M ((V 2%nat) - 128) ((V 33%nat) + 8) ->
  L5.u64_at RSEGS M ((V 2%nat) - 136) (V 33%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 144) (V 52%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 152) (V 35%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 160) (V 34%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 168) ((((V 33%nat) + 8) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 80) 0 -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 33%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 240) <= bv_unsigned a < ((V 2%nat) - 240) + 240) -> ~ ((((V 40%nat) + SZ) + 0) <= bv_unsigned a < (((V 40%nat) + SZ) + 0) + 32) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 240) <= i < ((V 2%nat) - 240) + 240) -> ~ ((((V 40%nat) + SZ) + 0) <= i < (((V 40%nat) + SZ) + 0) + 32) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb56a4 M) (st fx' R' 0x7cc28 M')
        /\ (forall x, In x PMBSLTP3.KS_bstG0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 698784
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 208)
        /\ getr R' (reg 8) = Z_to_bv 64 ((V 2%nat) - 104)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 36%nat) + SZ)
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 36%nat) + SZ)
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 36%nat) + SZ)
        /\ getr R' (reg 14) = Z_to_bv 64 1
        /\ getr R' (reg 15) = Z_to_bv 64 0
        /\ getr R' (reg 16) = Z_to_bv 64 (((V 33%nat) + 16) / 8)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 52%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 35%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 208) ((V 2%nat) - 104)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 200) 743392
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 192) (bv_unsigned (getr R (reg 24)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 184) (bv_unsigned (getr R (reg 23)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 176) 2147450880
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 168) ((((V 33%nat) + 8) / 8) + 2147450880)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 160) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 152) (V 35%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 144) (V 52%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 136) (V 33%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 128) ((V 33%nat) + 8)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 120) 771064
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 88) ((V 40%nat) + (SZ + 32))
        /\ L5.u64_at RSEGS M' ((V 40%nat) + (SZ + 24)) 0
        /\ L5.u8_at RSEGS M' ((V 40%nat) + (SZ + 16)) (V 53%nat)
        /\ L5.u64_at RSEGS M' ((V 40%nat) + (SZ + 8)) (V 39%nat)
        /\ L5.u32_at RSEGS M' ((V 40%nat) + SZ) (V 38%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) ((V 40%nat) + (2 * SZ))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 96) ((V 40%nat) + SZ)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 104) (V 40%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 43%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (V 44%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (V 45%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (V 46%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (V 47%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (V 48%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (V 49%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (V 50%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) (V 33%nat)).
Proof.
  intros Hk ESZ ENC ENO. subst SZ NC NO.
  assert (KC : k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10) by Lia.lia.
  destruct KC as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]].
  - exact (PMBSLTP3.bstG0_conc fx R M V).
  - exact (PMBSLTP3.bstG1_conc fx R M V).
  - exact (PMBSLTP3.bstG2_conc fx R M V).
  - exact (PMBSLTP3.bstG3_conc fx R M V).
  - exact (PMBSLTP3.bstG4_conc fx R M V).
  - exact (PMBSLTP3.bstG5_conc fx R M V).
  - exact (PMBSLTP3.bstG6_conc fx R M V).
  - exact (PMBSLTP3.bstG7_conc fx R M V).
  - exact (PMBSLTP3.bstG8_conc fx R M V).
  - exact (PMBSLTP3.bstG9_conc fx R M V).
  - exact (PMBSLTP3.bstG10_conc fx R M V).
Qed.

Lemma bstH_uni fx R M (V : nat -> Z) (k SZ NC NO : Z) : 0 <= k <= 10 -> SZ = 32 * 2 ^ k -> NC = 2 ^ (k + 1) -> NO = 2 ^ k ->
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 -> 0 <= (V 52%nat) < 2 ^ 64 -> 0 <= (V 54%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 208) -> getr R (reg 8) = Z_to_bv 64 ((V 2%nat) - 104) -> getr R (reg 9) = Z_to_bv 64 (V 33%nat) -> getr R (reg 18) = Z_to_bv 64 (V 52%nat) -> getr R (reg 19) = Z_to_bv 64 (V 35%nat) -> getr R (reg 20) = Z_to_bv 64 (V 34%nat) -> getr R (reg 21) = Z_to_bv 64 2147450880 -> getr R (reg 22) = Z_to_bv 64 2147450880 -> getr R (reg 23) = Z_to_bv 64 (V 51%nat) -> getr R (reg 24) = Z_to_bv 64 (V 54%nat) ->
  140735332491264 <= (V 2%nat) <= 140737488355328 -> PMBSLTP4.aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 4096) 4096 -> L5KA.zeros_at M (((V 2%nat) / 8) + 2147450368) 512 ->
  L5.img_clear M 1273856 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 6930432 <= (V 33%nat) <= 140737488355295 ->
  PMBSLTP4.aligned (V 33%nat) 8 -> (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 24 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 3 -> (((V 2%nat) - 4096) + 4096 <= (V 33%nat) \/ (V 33%nat) + 24 <= ((V 2%nat) - 4096)) ->
  (65536 + 6864896 <= (V 33%nat) \/ (V 33%nat) + 24 <= 65536) -> L5.u64_at RSEGS M (V 33%nat) (V 36%nat) -> L5.u64_at RSEGS M ((V 33%nat) + 8) ((V 36%nat) + SZ) -> L5.u64_at RSEGS M ((V 33%nat) + 16) ((V 36%nat) + SZ) ->
  4096 <= (V 36%nat) <= 140737488355296 -> PMBSLTP4.aligned (V 36%nat) 16 -> 4096 <= (V 40%nat) <= (140737488355328 - 2 * SZ) -> PMBSLTP4.aligned (V 40%nat) 16 ->
  L5.u64_at RSEGS M ((V 2%nat) - 8) (V 43%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 44%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 45%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 46%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 40) (V 47%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 48%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 49%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 50%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 120) 771064 -> L5.u64_at RSEGS M ((V 2%nat) - 128) ((V 33%nat) + 8) -> L5.u64_at RSEGS M ((V 2%nat) - 136) (V 33%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 144) (V 52%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 152) (V 35%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 160) (V 34%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 168) ((((V 33%nat) + 8) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 176) 2147450880 ->
  L5.u64_at RSEGS M ((V 2%nat) - 184) (V 51%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 192) (V 54%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 104) (V 40%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 96) ((V 40%nat) + SZ) ->
  L5.u64_at RSEGS M ((V 2%nat) - 88) ((V 40%nat) + (SZ + 32)) -> L5.u64_at RSEGS M ((V 2%nat) - 80) ((V 40%nat) + (2 * SZ)) -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 33%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 200) 743392 ->
  L5.u64_at RSEGS M ((V 2%nat) - 208) ((V 2%nat) - 104) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xaa9a0 M) (st fx' R' 0x78e40 M')
        /\ (forall x, In x PMBSLTP4.KS_bstH0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 743552
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 192)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 40%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 SZ
        /\ getr R' (reg 13) = Z_to_bv 64 (18446744073709551616 - SZ)
        /\ getr R' (reg 14) = Z_to_bv 64 1
        /\ getr R' (reg 18) = Z_to_bv 64 ((V 33%nat) + 8)
        /\ getr R' (reg 19) = Z_to_bv 64 ((V 2%nat) - 96)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 40%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 ((((V 33%nat) + 8) / 8) + 2147450880)
        /\ getr R' (reg 23) = Z_to_bv 64 ((((V 2%nat) - 96) / 8) + 2147450880)
        /\ getr R' (reg 24) = Z_to_bv 64 (((V 33%nat) / 8) + 2147450880)).
Proof.
  intros Hk ESZ ENC ENO. subst SZ NC NO.
  assert (KC : k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10) by Lia.lia.
  destruct KC as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]].
  - exact (PMBSLTP4.bstH0_conc fx R M V).
  - exact (PMBSLTP4.bstH1_conc fx R M V).
  - exact (PMBSLTP4.bstH2_conc fx R M V).
  - exact (PMBSLTP4.bstH3_conc fx R M V).
  - exact (PMBSLTP4.bstH4_conc fx R M V).
  - exact (PMBSLTP4.bstH5_conc fx R M V).
  - exact (PMBSLTP4.bstH6_conc fx R M V).
  - exact (PMBSLTP4.bstH7_conc fx R M V).
  - exact (PMBSLTP4.bstH8_conc fx R M V).
  - exact (PMBSLTP4.bstH9_conc fx R M V).
  - exact (PMBSLTP4.bstH10_conc fx R M V).
Qed.

Lemma bstI_uni fx R M (V : nat -> Z) (k SZ NC NO : Z) : 0 <= k <= 10 -> SZ = 32 * 2 ^ k -> NC = 2 ^ (k + 1) -> NO = 2 ^ k ->
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 -> 0 <= (V 52%nat) < 2 ^ 64 -> 0 <= (V 54%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 192) -> getr R (reg 8) = Z_to_bv 64 ((V 2%nat) - 104) -> getr R (reg 9) = Z_to_bv 64 (V 33%nat) -> getr R (reg 18) = Z_to_bv 64 ((V 33%nat) + 8) -> getr R (reg 19) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 20) = Z_to_bv 64 (V 40%nat) -> getr R (reg 21) = Z_to_bv 64 2147450880 -> getr R (reg 22) = Z_to_bv 64 ((((V 33%nat) + 8) / 8) + 2147450880) -> getr R (reg 23) = Z_to_bv 64 ((((V 2%nat) - 96) / 8) + 2147450880) -> getr R (reg 24) = Z_to_bv 64 (((V 33%nat) / 8) + 2147450880) ->
  140735332491264 <= (V 2%nat) <= 140737488355328 -> PMBSLTP5.aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 4096) 4096 -> L5KA.zeros_at M (((V 2%nat) / 8) + 2147450368) 512 ->
  L5.img_clear M 1273856 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 6930432 <= (V 33%nat) <= 140737488355295 ->
  PMBSLTP5.aligned (V 33%nat) 8 -> (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 24 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 3 -> (((V 2%nat) - 4096) + 4096 <= (V 33%nat) \/ (V 33%nat) + 24 <= ((V 2%nat) - 4096)) ->
  (65536 + 6864896 <= (V 33%nat) \/ (V 33%nat) + 24 <= 65536) -> L5.writable RSEGS M (V 33%nat) 24 -> L5.u64_at RSEGS M (V 33%nat) (V 36%nat) -> L5.u64_at RSEGS M ((V 33%nat) + 8) ((V 36%nat) + SZ) ->
  L5.u64_at RSEGS M ((V 33%nat) + 16) ((V 36%nat) + SZ) -> 4096 <= (V 36%nat) <= 140737488355296 -> PMBSLTP5.aligned (V 36%nat) 16 -> 4096 <= (V 40%nat) <= (140737488355328 - 2 * SZ) ->
  PMBSLTP5.aligned (V 40%nat) 16 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 43%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 44%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 45%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 32) (V 46%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 47%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 48%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 49%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 64) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 120) 771064 -> L5.u64_at RSEGS M ((V 2%nat) - 128) ((V 33%nat) + 8) -> L5.u64_at RSEGS M ((V 2%nat) - 136) (V 33%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 144) (V 52%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 152) (V 35%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 160) (V 34%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 168) ((((V 33%nat) + 8) / 8) + 2147450880) ->
  L5.u64_at RSEGS M ((V 2%nat) - 176) 2147450880 -> L5.u64_at RSEGS M ((V 2%nat) - 184) (V 51%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 192) (V 54%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 104) (V 40%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 96) ((V 40%nat) + SZ) -> L5.u64_at RSEGS M ((V 2%nat) - 88) ((V 40%nat) + (SZ + 32)) -> L5.u64_at RSEGS M ((V 2%nat) - 80) ((V 40%nat) + (2 * SZ)) -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 33%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 192) <= bv_unsigned a < ((V 2%nat) - 192) + 192) -> ~ (((V 33%nat) + 0) <= bv_unsigned a < ((V 33%nat) + 0) + 24) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 192) <= i < ((V 2%nat) - 192) + 192) -> ~ (((V 33%nat) + 0) <= i < ((V 33%nat) + 0) + 24) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb5880 M) (st fx' R' 0x7cc28 M')
        /\ (forall x, In x PMBSLTP5.KS_bstI0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 744352
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 128)
        /\ getr R' (reg 8) = Z_to_bv 64 ((V 33%nat) + 8)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 40%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 40%nat) + (2 * SZ))
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 40%nat) + (2 * SZ))
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 40%nat) + (SZ + 32))
        /\ getr R' (reg 14) = Z_to_bv 64 1
        /\ getr R' (reg 15) = Z_to_bv 64 0
        /\ getr R' (reg 16) = Z_to_bv 64 0
        /\ getr R' (reg 18) = Z_to_bv 64 (V 52%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 35%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 ((((V 33%nat) + 8) / 8) + 2147450880)
        /\ getr R' (reg 22) = Z_to_bv 64 2147450880
        /\ getr R' (reg 23) = Z_to_bv 64 (V 51%nat)
        /\ getr R' (reg 24) = Z_to_bv 64 (V 54%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 128) ((V 33%nat) + 8)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 120) 771064
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 104) (V 36%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) ((V 36%nat) + SZ)
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 16) ((V 40%nat) + (2 * SZ))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 88) (V 36%nat)
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 8) ((V 40%nat) + (SZ + 32))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 96) (V 36%nat)
        /\ L5.u64_at RSEGS M' (V 33%nat) (V 40%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 43%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (V 44%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (V 45%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (V 46%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (V 47%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (V 48%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (V 49%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (V 50%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) (V 33%nat)).
Proof.
  intros Hk ESZ ENC ENO. subst SZ NC NO.
  assert (KC : k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10) by Lia.lia.
  destruct KC as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]].
  - exact (PMBSLTP5.bstI0_conc fx R M V).
  - exact (PMBSLTP5.bstI1_conc fx R M V).
  - exact (PMBSLTP5.bstI2_conc fx R M V).
  - exact (PMBSLTP5.bstI3_conc fx R M V).
  - exact (PMBSLTP5.bstI4_conc fx R M V).
  - exact (PMBSLTP5.bstI5_conc fx R M V).
  - exact (PMBSLTP5.bstI6_conc fx R M V).
  - exact (PMBSLTP5.bstI7_conc fx R M V).
  - exact (PMBSLTP5.bstI8_conc fx R M V).
  - exact (PMBSLTP5.bstI9_conc fx R M V).
  - exact (PMBSLTP5.bstI10_conc fx R M V).
Qed.

End PMBSLTU.
