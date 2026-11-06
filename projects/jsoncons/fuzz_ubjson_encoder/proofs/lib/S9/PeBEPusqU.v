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
     BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA PeCModel
     PeBEPusqP2 PeBEPusqP3 PeBEPusqP4 PeBEPusqP5.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module PEBEQU.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom AsanUbsan.M.loaded_segments)) (only parsing).

Lemma bpqS_uni fx R M (V : nat -> Z) (k SZ NC NO : Z) : 0 < k <= 11 -> NO = PEC.ecap k -> SZ = 24 * NO -> NC = 2 * NO ->
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 ((V 33%nat) + 24) -> getr R (reg 11) = Z_to_bv 64 (V 34%nat) -> getr R (reg 12) = Z_to_bv 64 (V 35%nat) ->
  140735332491264 <= (V 2%nat) <= 140737488355328 -> PEBEQP2.aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 4096) 4096 -> L5KA.zeros_at M (((V 2%nat) / 8) + 2147450368) 512 ->
  L5.img_clear M 65536 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 6930432 <= (V 33%nat) <= 140737488355263 ->
  PEBEQP2.aligned (V 33%nat) 8 -> (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 56 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 7 -> (((V 2%nat) - 4096) + 4096 <= (V 33%nat) \/ (V 33%nat) + 56 <= ((V 2%nat) - 4096)) ->
  (65536 + 6864896 <= (V 33%nat) \/ (V 33%nat) + 56 <= 65536) -> L5.u64_at RSEGS M ((V 33%nat) + 24) (V 36%nat) -> L5.u64_at RSEGS M ((V 33%nat) + 32) ((V 36%nat) + SZ) -> L5.u64_at RSEGS M ((V 33%nat) + 40) ((V 36%nat) + SZ) ->
  4096 <= (V 36%nat) <= 140737488355304 -> PEBEQP2.aligned (V 36%nat) 8 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 176) <= bv_unsigned a < ((V 2%nat) - 176) + 176) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 176) <= i < ((V 2%nat) - 176) + 176) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb0648 M) (st fx' R' 0x136668 M')
        /\ (forall x, In x PEBEQP2.KS_bpqS1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 723940
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 160)
        /\ getr R' (reg 8) = Z_to_bv 64 ((V 2%nat) - 72)
        /\ getr R' (reg 9) = Z_to_bv 64 NC
        /\ getr R' (reg 10) = Z_to_bv 64 (2 * SZ)
        /\ getr R' (reg 11) = Z_to_bv 64 (32 * NC)
        /\ getr R' (reg 12) = Z_to_bv 64 1335544
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 33%nat) + 24)
        /\ getr R' (reg 14) = Z_to_bv 64 12297829382473034411
        /\ getr R' (reg 15) = Z_to_bv 64 0
        /\ getr R' (reg 18) = Z_to_bv 64 ((V 2%nat) - 96)
        /\ getr R' (reg 19) = Z_to_bv 64 NO
        /\ getr R' (reg 20) = Z_to_bv 64 ((((V 2%nat) - 72) / 8) + 2147450880)
        /\ getr R' (reg 21) = Z_to_bv 64 2147450880
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) ((V 33%nat) + 24)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 152) 2147450880
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 144) ((((V 33%nat) + 32) / 8) + 2147450880)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 136) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 128) (V 35%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 120) ((V 33%nat) + 24)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 112) ((V 33%nat) + 32)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 104) 722720
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (bv_unsigned (getr R (reg 21)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (bv_unsigned (getr R (reg 20)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))).
Proof.
  intros Hk ENO ESZ ENC. subst SZ NC. subst NO.
  assert (KC : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11) by Lia.lia.
  clear Hk. destruct KC as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]].
  - exact (PEBEQP2.bpqS1_conc fx R M V).
  - exact (PEBEQP2.bpqS2_conc fx R M V).
  - exact (PEBEQP2.bpqS3_conc fx R M V).
  - exact (PEBEQP2.bpqS4_conc fx R M V).
  - exact (PEBEQP2.bpqS5_conc fx R M V).
  - exact (PEBEQP2.bpqS6_conc fx R M V).
  - exact (PEBEQP2.bpqS7_conc fx R M V).
  - exact (PEBEQP2.bpqS8_conc fx R M V).
  - exact (PEBEQP2.bpqS9_conc fx R M V).
  - exact (PEBEQP2.bpqS10_conc fx R M V).
  - exact (PEBEQP2.bpqS11_conc fx R M V).
Qed.

Lemma bpqG_uni fx R M (V : nat -> Z) (k SZ NC NO : Z) : 0 < k <= 11 -> NO = PEC.ecap k -> SZ = 24 * NO -> NC = 2 * NO ->
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 8) = Z_to_bv 64 ((V 2%nat) - 72) -> getr R (reg 9) = Z_to_bv 64 NC -> getr R (reg 10) = Z_to_bv 64 (V 40%nat) -> getr R (reg 18) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 19) = Z_to_bv 64 NO -> getr R (reg 20) = Z_to_bv 64 ((((V 2%nat) - 72) / 8) + 2147450880) -> getr R (reg 21) = Z_to_bv 64 2147450880 ->
  140735332491264 <= (V 2%nat) <= 140737488355328 -> PEBEQP3.aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 4096) 4096 -> L5KA.zeros_at M (((V 2%nat) / 8) + 2147450368) 512 ->
  L5.img_clear M 65536 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 6930432 <= (V 33%nat) <= 140737488355263 ->
  PEBEQP3.aligned (V 33%nat) 8 -> (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 56 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 7 -> (((V 2%nat) - 4096) + 4096 <= (V 33%nat) \/ (V 33%nat) + 56 <= ((V 2%nat) - 4096)) ->
  (65536 + 6864896 <= (V 33%nat) \/ (V 33%nat) + 56 <= 65536) -> L5.u64_at RSEGS M ((V 33%nat) + 24) (V 36%nat) -> L5.u64_at RSEGS M ((V 33%nat) + 32) ((V 36%nat) + SZ) -> L5.u64_at RSEGS M ((V 33%nat) + 40) ((V 36%nat) + SZ) ->
  4096 <= (V 36%nat) <= 140737488355304 -> PEBEQP3.aligned (V 36%nat) 8 -> 6930432 <= (V 34%nat) <= 140737488355324 -> PEBEQP3.aligned (V 34%nat) 4 ->
  (2147446784 + 17592186048512 <= (V 34%nat) \/ (V 34%nat) + 4 <= 2147446784) -> L5KA.zeros_at M (((V 34%nat) / 8) + 2147450880) 1 -> L5.u32_at RSEGS M (V 34%nat) (V 38%nat) -> (((V 2%nat) - 4096) + 4096 <= (V 34%nat) \/ (V 34%nat) + 4 <= ((V 2%nat) - 4096)) ->
  ((V 33%nat) + 56 <= (V 34%nat) \/ (V 34%nat) + 4 <= (V 33%nat)) -> 0 <= (V 38%nat) <= 3 -> 6930432 <= (V 35%nat) <= 140737488355320 -> PEBEQP3.aligned (V 35%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 35%nat) \/ (V 35%nat) + 8 <= 2147446784) -> L5KA.zeros_at M (((V 35%nat) / 8) + 2147450880) 1 -> L5.u64_at RSEGS M (V 35%nat) (V 39%nat) -> (((V 2%nat) - 4096) + 4096 <= (V 35%nat) \/ (V 35%nat) + 8 <= ((V 2%nat) - 4096)) ->
  ((V 33%nat) + 56 <= (V 35%nat) \/ (V 35%nat) + 8 <= (V 33%nat)) -> 0 <= (V 39%nat) <= 16777216 -> 4096 <= (V 40%nat) <= (140737488355328 - 2 * SZ) -> PEBEQP3.aligned (V 40%nat) 16 ->
  L5.writable RSEGS M ((V 40%nat) + SZ) 24 -> L5KA.zeros_at M ((((V 40%nat) + SZ) / 8) + 2147450880) 3 -> (2147446784 + 17592186048512 <= ((V 40%nat) + SZ) \/ ((V 40%nat) + SZ) + 24 <= 2147446784) -> 4096 <= ((V 40%nat) + SZ) <= 140737488355304 ->
  (((V 2%nat) - 4096) + 4096 <= ((V 40%nat) + SZ) \/ ((V 40%nat) + SZ) + 24 <= ((V 2%nat) - 4096)) -> ((V 33%nat) + 56 <= ((V 40%nat) + SZ) \/ ((V 40%nat) + SZ) + 24 <= (V 33%nat)) -> ((V 34%nat) + 4 <= ((V 40%nat) + SZ) \/ ((V 40%nat) + SZ) + 24 <= (V 34%nat)) -> ((V 35%nat) + 8 <= ((V 40%nat) + SZ) \/ ((V 40%nat) + SZ) + 24 <= (V 35%nat)) ->
  (65536 + 6864896 <= ((V 40%nat) + SZ) \/ ((V 40%nat) + SZ) + 24 <= 65536) -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 43%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 44%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 45%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 32) (V 46%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 47%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 48%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 49%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 104) 722720 -> L5.u64_at RSEGS M ((V 2%nat) - 112) ((V 33%nat) + 32) -> L5.u64_at RSEGS M ((V 2%nat) - 120) ((V 33%nat) + 24) -> L5.u64_at RSEGS M ((V 2%nat) - 128) (V 35%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 136) (V 34%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 144) ((((V 33%nat) + 32) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 152) 2147450880 -> L5.u64_at RSEGS M ((V 2%nat) - 72) 0 ->
  L5.u64_at RSEGS M ((V 2%nat) - 64) ((V 33%nat) + 24) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 208) <= bv_unsigned a < ((V 2%nat) - 208) + 208) -> ~ ((((V 40%nat) + SZ) + 0) <= bv_unsigned a < (((V 40%nat) + SZ) + 0) + 24) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 208) <= i < ((V 2%nat) - 208) + 208) -> ~ ((((V 40%nat) + SZ) + 0) <= i < (((V 40%nat) + SZ) + 0) + 24) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb0be4 M) (st fx' R' 0x7cc28 M')
        /\ (forall x, In x PEBEQP3.KS_bpqG1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 725264
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 192)
        /\ getr R' (reg 8) = Z_to_bv 64 ((V 2%nat) - 96)
        /\ getr R' (reg 9) = Z_to_bv 64 ((V 33%nat) + 24)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 36%nat) + SZ)
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 36%nat) + SZ)
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 36%nat) + SZ)
        /\ getr R' (reg 14) = Z_to_bv 64 1
        /\ getr R' (reg 15) = Z_to_bv 64 0
        /\ getr R' (reg 16) = Z_to_bv 64 (((V 33%nat) + 40) / 8)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 35%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 ((((V 33%nat) + 32) / 8) + 2147450880)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 192) ((V 2%nat) - 96)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 184) 724288
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 176) (bv_unsigned (getr R (reg 24)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 168) (bv_unsigned (getr R (reg 23)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 160) (bv_unsigned (getr R (reg 22)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 152) 2147450880
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 144) ((((V 33%nat) + 32) / 8) + 2147450880)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 136) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 128) (V 35%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 120) ((V 33%nat) + 24)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 112) ((V 33%nat) + 32)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 104) 722872
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) ((V 40%nat) + (SZ + 24))
        /\ L5.u64_at RSEGS M' ((V 40%nat) + (SZ + 16)) 0
        /\ L5.u64_at RSEGS M' ((V 40%nat) + (SZ + 8)) (V 39%nat)
        /\ L5.u32_at RSEGS M' ((V 40%nat) + SZ) (V 38%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) ((V 40%nat) + (2 * SZ))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 88) ((V 40%nat) + SZ)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 96) (V 40%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 43%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (V 44%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (V 45%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (V 46%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (V 47%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (V 48%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (V 49%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) ((V 33%nat) + 24)).
Proof.
  intros Hk ENO ESZ ENC. subst SZ NC. subst NO.
  assert (KC : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11) by Lia.lia.
  clear Hk. destruct KC as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]].
  - exact (PEBEQP3.bpqG1_conc fx R M V).
  - exact (PEBEQP3.bpqG2_conc fx R M V).
  - exact (PEBEQP3.bpqG3_conc fx R M V).
  - exact (PEBEQP3.bpqG4_conc fx R M V).
  - exact (PEBEQP3.bpqG5_conc fx R M V).
  - exact (PEBEQP3.bpqG6_conc fx R M V).
  - exact (PEBEQP3.bpqG7_conc fx R M V).
  - exact (PEBEQP3.bpqG8_conc fx R M V).
  - exact (PEBEQP3.bpqG9_conc fx R M V).
  - exact (PEBEQP3.bpqG10_conc fx R M V).
  - exact (PEBEQP3.bpqG11_conc fx R M V).
Qed.

Lemma bpqH_uni fx R M (V : nat -> Z) (k SZ NC NO : Z) : 0 < k <= 11 -> NO = PEC.ecap k -> SZ = 24 * NO -> NC = 2 * NO ->
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 192) -> getr R (reg 8) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 9) = Z_to_bv 64 ((V 33%nat) + 24) -> getr R (reg 18) = Z_to_bv 64 (V 35%nat) -> getr R (reg 19) = Z_to_bv 64 (V 34%nat) -> getr R (reg 20) = Z_to_bv 64 ((((V 33%nat) + 32) / 8) + 2147450880) -> getr R (reg 21) = Z_to_bv 64 2147450880 ->
  140735332491264 <= (V 2%nat) <= 140737488355328 -> PEBEQP4.aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 4096) 4096 -> L5KA.zeros_at M (((V 2%nat) / 8) + 2147450368) 512 ->
  L5.img_clear M 65536 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 6930432 <= (V 33%nat) <= 140737488355263 ->
  PEBEQP4.aligned (V 33%nat) 8 -> (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 56 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 7 -> (((V 2%nat) - 4096) + 4096 <= (V 33%nat) \/ (V 33%nat) + 56 <= ((V 2%nat) - 4096)) ->
  (65536 + 6864896 <= (V 33%nat) \/ (V 33%nat) + 56 <= 65536) -> L5.u64_at RSEGS M ((V 33%nat) + 24) (V 36%nat) -> L5.u64_at RSEGS M ((V 33%nat) + 32) ((V 36%nat) + SZ) -> L5.u64_at RSEGS M ((V 33%nat) + 40) ((V 36%nat) + SZ) ->
  4096 <= (V 36%nat) <= 140737488355304 -> PEBEQP4.aligned (V 36%nat) 8 -> 4096 <= (V 40%nat) <= (140737488355328 - 2 * SZ) -> PEBEQP4.aligned (V 40%nat) 16 ->
  4096 <= ((V 40%nat) + SZ) <= 140737488355304 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 43%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 44%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 45%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 32) (V 46%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 47%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 48%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 49%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 104) 722872 -> L5.u64_at RSEGS M ((V 2%nat) - 112) ((V 33%nat) + 32) -> L5.u64_at RSEGS M ((V 2%nat) - 120) ((V 33%nat) + 24) -> L5.u64_at RSEGS M ((V 2%nat) - 128) (V 35%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 136) (V 34%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 144) ((((V 33%nat) + 32) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 152) 2147450880 -> L5.u64_at RSEGS M ((V 2%nat) - 160) (bv_unsigned (getr R (reg 22))) ->
  L5.u64_at RSEGS M ((V 2%nat) - 168) (bv_unsigned (getr R (reg 23))) -> L5.u64_at RSEGS M ((V 2%nat) - 176) (bv_unsigned (getr R (reg 24))) -> L5.u64_at RSEGS M ((V 2%nat) - 184) 724288 -> L5.u64_at RSEGS M ((V 2%nat) - 192) ((V 2%nat) - 96) ->
  L5.u64_at RSEGS M ((V 2%nat) - 96) (V 40%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 88) ((V 40%nat) + SZ) -> L5.u64_at RSEGS M ((V 2%nat) - 80) ((V 40%nat) + (SZ + 24)) -> L5.u64_at RSEGS M ((V 2%nat) - 72) ((V 40%nat) + (2 * SZ)) ->
  L5.u64_at RSEGS M ((V 2%nat) - 64) ((V 33%nat) + 24) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 208) <= bv_unsigned a < ((V 2%nat) - 208) + 208) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 208) <= i < ((V 2%nat) - 208) + 208) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb1110 M) (st fx' R' 0x78e40 M')
        /\ (forall x, In x PEBEQP4.KS_bpqH1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 724444
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 176)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 40%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 SZ
        /\ getr R' (reg 13) = Z_to_bv 64 (18446744073709551616 - 4 * NC)
        /\ getr R' (reg 14) = Z_to_bv 64 0
        /\ getr R' (reg 18) = Z_to_bv 64 ((V 33%nat) + 32)
        /\ getr R' (reg 19) = Z_to_bv 64 ((V 2%nat) - 88)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 40%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 ((((V 33%nat) + 32) / 8) + 2147450880)
        /\ getr R' (reg 23) = Z_to_bv 64 ((((V 2%nat) - 88) / 8) + 2147450880)
        /\ getr R' (reg 24) = Z_to_bv 64 ((((V 33%nat) + 24) / 8) + 2147450880)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 43%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (V 44%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (V 45%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (V 46%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (V 47%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (V 48%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (V 49%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 104) 722872
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 112) ((V 33%nat) + 32)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 120) ((V 33%nat) + 24)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 128) (V 35%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 136) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 144) ((((V 33%nat) + 32) / 8) + 2147450880)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 152) 2147450880
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 160) (bv_unsigned (getr R (reg 22)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 168) (bv_unsigned (getr R (reg 23)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 176) (bv_unsigned (getr R (reg 24)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 96) (V 40%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 88) ((V 40%nat) + SZ)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) ((V 40%nat) + (SZ + 24))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) ((V 40%nat) + (2 * SZ))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) ((V 33%nat) + 24)).
Proof.
  intros Hk ENO ESZ ENC. subst SZ NC. subst NO.
  assert (KC : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11) by Lia.lia.
  clear Hk. destruct KC as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]].
  - exact (PEBEQP4.bpqH1_conc fx R M V).
  - exact (PEBEQP4.bpqH2_conc fx R M V).
  - exact (PEBEQP4.bpqH3_conc fx R M V).
  - exact (PEBEQP4.bpqH4_conc fx R M V).
  - exact (PEBEQP4.bpqH5_conc fx R M V).
  - exact (PEBEQP4.bpqH6_conc fx R M V).
  - exact (PEBEQP4.bpqH7_conc fx R M V).
  - exact (PEBEQP4.bpqH8_conc fx R M V).
  - exact (PEBEQP4.bpqH9_conc fx R M V).
  - exact (PEBEQP4.bpqH10_conc fx R M V).
  - exact (PEBEQP4.bpqH11_conc fx R M V).
Qed.

Lemma bpqI_uni fx R M (V : nat -> Z) (k SZ NC NO : Z) : 0 < k <= 11 -> NO = PEC.ecap k -> SZ = 24 * NO -> NC = 2 * NO ->
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 22%nat) < 2 ^ 64 -> 0 <= (V 23%nat) < 2 ^ 64 -> 0 <= (V 24%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 176) -> getr R (reg 8) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 9) = Z_to_bv 64 ((V 33%nat) + 24) -> getr R (reg 18) = Z_to_bv 64 ((V 33%nat) + 32) -> getr R (reg 19) = Z_to_bv 64 ((V 2%nat) - 88) -> getr R (reg 20) = Z_to_bv 64 (V 40%nat) -> getr R (reg 21) = Z_to_bv 64 2147450880 -> getr R (reg 22) = Z_to_bv 64 ((((V 33%nat) + 32) / 8) + 2147450880) -> getr R (reg 23) = Z_to_bv 64 ((((V 2%nat) - 88) / 8) + 2147450880) -> getr R (reg 24) = Z_to_bv 64 ((((V 33%nat) + 24) / 8) + 2147450880) ->
  140735332491264 <= (V 2%nat) <= 140737488355328 -> PEBEQP5.aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 4096) 4096 -> L5KA.zeros_at M (((V 2%nat) / 8) + 2147450368) 512 ->
  L5.img_clear M 65536 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 6930432 <= (V 33%nat) <= 140737488355263 ->
  PEBEQP5.aligned (V 33%nat) 8 -> (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 56 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 7 -> (((V 2%nat) - 4096) + 4096 <= (V 33%nat) \/ (V 33%nat) + 56 <= ((V 2%nat) - 4096)) ->
  (65536 + 6864896 <= (V 33%nat) \/ (V 33%nat) + 56 <= 65536) -> L5.writable RSEGS M ((V 33%nat) + 24) 24 -> L5.u64_at RSEGS M ((V 33%nat) + 24) (V 36%nat) -> L5.u64_at RSEGS M ((V 33%nat) + 32) ((V 36%nat) + SZ) ->
  L5.u64_at RSEGS M ((V 33%nat) + 40) ((V 36%nat) + SZ) -> 4096 <= (V 36%nat) <= 140737488355304 -> PEBEQP5.aligned (V 36%nat) 8 -> 4096 <= (V 40%nat) <= (140737488355328 - 2 * SZ) ->
  PEBEQP5.aligned (V 40%nat) 16 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 43%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 44%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 45%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 32) (V 46%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 47%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 48%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 49%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 104) 722872 -> L5.u64_at RSEGS M ((V 2%nat) - 112) ((V 33%nat) + 32) -> L5.u64_at RSEGS M ((V 2%nat) - 120) ((V 33%nat) + 24) -> L5.u64_at RSEGS M ((V 2%nat) - 128) (V 35%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 136) (V 34%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 144) ((((V 33%nat) + 32) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 152) 2147450880 -> L5.u64_at RSEGS M ((V 2%nat) - 160) (V 22%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 168) (V 23%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 176) (V 24%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 96) (V 40%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 88) ((V 40%nat) + SZ) ->
  L5.u64_at RSEGS M ((V 2%nat) - 80) ((V 40%nat) + (SZ + 24)) -> L5.u64_at RSEGS M ((V 2%nat) - 72) ((V 40%nat) + (2 * SZ)) -> L5.u64_at RSEGS M ((V 2%nat) - 64) ((V 33%nat) + 24) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 208) <= bv_unsigned a < ((V 2%nat) - 208) + 208) -> ~ (((V 33%nat) + 24) <= bv_unsigned a < ((V 33%nat) + 24) + 24) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 208) <= i < ((V 2%nat) - 208) + 208) -> ~ (((V 33%nat) + 24) <= i < ((V 33%nat) + 24) + 24) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb0ddc M) (st fx' R' 0x7cc28 M')
        /\ (forall x, In x PEBEQP5.KS_bpqI1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 725468
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 112)
        /\ getr R' (reg 8) = Z_to_bv 64 ((V 33%nat) + 32)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 40%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 40%nat) + (2 * SZ))
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 40%nat) + (2 * SZ))
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 40%nat) + (SZ + 24))
        /\ getr R' (reg 14) = Z_to_bv 64 1
        /\ getr R' (reg 15) = Z_to_bv 64 0
        /\ getr R' (reg 16) = Z_to_bv 64 1
        /\ getr R' (reg 17) = Z_to_bv 64 0
        /\ getr R' (reg 18) = Z_to_bv 64 (V 35%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 ((((V 33%nat) + 32) / 8) + 2147450880)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 22%nat)
        /\ getr R' (reg 23) = Z_to_bv 64 (V 23%nat)
        /\ getr R' (reg 24) = Z_to_bv 64 (V 24%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 112) ((V 33%nat) + 32)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 104) 722872
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 96) (V 36%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) ((V 36%nat) + SZ)
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 40) ((V 40%nat) + (2 * SZ))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) (V 36%nat)
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 32) ((V 40%nat) + (SZ + 24))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 88) (V 36%nat)
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 24) (V 40%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 43%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (V 44%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (V 45%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (V 46%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (V 47%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (V 48%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (V 49%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) ((V 33%nat) + 24)).
Proof.
  intros Hk ENO ESZ ENC. subst SZ NC. subst NO.
  assert (KC : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11) by Lia.lia.
  clear Hk. destruct KC as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]].
  - exact (PEBEQP5.bpqI1_conc fx R M V).
  - exact (PEBEQP5.bpqI2_conc fx R M V).
  - exact (PEBEQP5.bpqI3_conc fx R M V).
  - exact (PEBEQP5.bpqI4_conc fx R M V).
  - exact (PEBEQP5.bpqI5_conc fx R M V).
  - exact (PEBEQP5.bpqI6_conc fx R M V).
  - exact (PEBEQP5.bpqI7_conc fx R M V).
  - exact (PEBEQP5.bpqI8_conc fx R M V).
  - exact (PEBEQP5.bpqI9_conc fx R M V).
  - exact (PEBEQP5.bpqI10_conc fx R M V).
  - exact (PEBEQP5.bpqI11_conc fx R M V).
Qed.

End PEBEQU.
