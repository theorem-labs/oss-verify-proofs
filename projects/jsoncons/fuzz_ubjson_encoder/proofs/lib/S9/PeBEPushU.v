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
     PeBEPushP2 PeBEPushP3 PeBEPushP4 PeBEPushP5.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module PEBEPU.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom AsanUbsan.M.loaded_segments)) (only parsing).

Lemma bpkS_uni fx R M (V : nat -> Z) (k SZ NC NO : Z) : 0 < k <= 11 -> NO = PEC.ecap k -> SZ = 24 * NO -> NC = 2 * NO ->
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 ((V 33%nat) + 24) -> getr R (reg 11) = Z_to_bv 64 (V 34%nat) ->
  140735332491264 <= (V 2%nat) <= 140737488355328 -> PEBEPP2.aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 4096) 4096 -> L5KA.zeros_at M (((V 2%nat) / 8) + 2147450368) 512 ->
  L5.img_clear M 65536 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 6930432 <= (V 33%nat) <= 140737488355263 ->
  PEBEPP2.aligned (V 33%nat) 8 -> (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 56 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 7 -> (((V 2%nat) - 4096) + 4096 <= (V 33%nat) \/ (V 33%nat) + 56 <= ((V 2%nat) - 4096)) ->
  (65536 + 6864896 <= (V 33%nat) \/ (V 33%nat) + 56 <= 65536) -> L5.u64_at RSEGS M ((V 33%nat) + 24) (V 36%nat) -> L5.u64_at RSEGS M ((V 33%nat) + 32) ((V 36%nat) + SZ) -> L5.u64_at RSEGS M ((V 33%nat) + 40) ((V 36%nat) + SZ) ->
  4096 <= (V 36%nat) <= 140737488355304 -> PEBEPP2.aligned (V 36%nat) 8 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 176) <= bv_unsigned a < ((V 2%nat) - 176) + 176) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 176) <= i < ((V 2%nat) - 176) + 176) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb417c M) (st fx' R' 0x136668 M')
        /\ (forall x, In x PEBEPP2.KS_bpkS1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 723940
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 160)
        /\ getr R' (reg 8) = Z_to_bv 64 ((V 2%nat) - 64)
        /\ getr R' (reg 9) = Z_to_bv 64 NC
        /\ getr R' (reg 10) = Z_to_bv 64 (2 * SZ)
        /\ getr R' (reg 11) = Z_to_bv 64 (32 * NC)
        /\ getr R' (reg 12) = Z_to_bv 64 1335544
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 33%nat) + 24)
        /\ getr R' (reg 14) = Z_to_bv 64 12297829382473034411
        /\ getr R' (reg 15) = Z_to_bv 64 0
        /\ getr R' (reg 18) = Z_to_bv 64 ((V 2%nat) - 88)
        /\ getr R' (reg 19) = Z_to_bv 64 NO
        /\ getr R' (reg 20) = Z_to_bv 64 ((((V 2%nat) - 64) / 8) + 2147450880)
        /\ getr R' (reg 21) = Z_to_bv 64 2147450880
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) ((V 33%nat) + 24)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 152) (bv_unsigned (getr R (reg 21)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 144) 2147450880
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 136) ((((V 33%nat) + 32) / 8) + 2147450880)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 128) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 120) ((V 33%nat) + 24)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 112) ((V 33%nat) + 32)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 104) 737868
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
  - exact (PEBEPP2.bpkS1_conc fx R M V).
  - exact (PEBEPP2.bpkS2_conc fx R M V).
  - exact (PEBEPP2.bpkS3_conc fx R M V).
  - exact (PEBEPP2.bpkS4_conc fx R M V).
  - exact (PEBEPP2.bpkS5_conc fx R M V).
  - exact (PEBEPP2.bpkS6_conc fx R M V).
  - exact (PEBEPP2.bpkS7_conc fx R M V).
  - exact (PEBEPP2.bpkS8_conc fx R M V).
  - exact (PEBEPP2.bpkS9_conc fx R M V).
  - exact (PEBEPP2.bpkS10_conc fx R M V).
  - exact (PEBEPP2.bpkS11_conc fx R M V).
Qed.

Lemma bpkG_uni fx R M (V : nat -> Z) (k SZ NC NO : Z) : 0 < k <= 11 -> NO = PEC.ecap k -> SZ = 24 * NO -> NC = 2 * NO ->
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 21%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 8) = Z_to_bv 64 ((V 2%nat) - 64) -> getr R (reg 9) = Z_to_bv 64 NC -> getr R (reg 10) = Z_to_bv 64 (V 40%nat) -> getr R (reg 18) = Z_to_bv 64 ((V 2%nat) - 88) -> getr R (reg 19) = Z_to_bv 64 NO -> getr R (reg 20) = Z_to_bv 64 ((((V 2%nat) - 64) / 8) + 2147450880) -> getr R (reg 21) = Z_to_bv 64 2147450880 ->
  140735332491264 <= (V 2%nat) <= 140737488355328 -> PEBEPP3.aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 4096) 4096 -> L5KA.zeros_at M (((V 2%nat) / 8) + 2147450368) 512 ->
  L5.img_clear M 65536 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 6930432 <= (V 33%nat) <= 140737488355263 ->
  PEBEPP3.aligned (V 33%nat) 8 -> (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 56 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 7 -> (((V 2%nat) - 4096) + 4096 <= (V 33%nat) \/ (V 33%nat) + 56 <= ((V 2%nat) - 4096)) ->
  (65536 + 6864896 <= (V 33%nat) \/ (V 33%nat) + 56 <= 65536) -> L5.u64_at RSEGS M ((V 33%nat) + 24) (V 36%nat) -> L5.u64_at RSEGS M ((V 33%nat) + 32) ((V 36%nat) + SZ) -> L5.u64_at RSEGS M ((V 33%nat) + 40) ((V 36%nat) + SZ) ->
  4096 <= (V 36%nat) <= 140737488355304 -> PEBEPP3.aligned (V 36%nat) 8 -> 6930432 <= (V 34%nat) <= 140737488355324 -> PEBEPP3.aligned (V 34%nat) 4 ->
  (2147446784 + 17592186048512 <= (V 34%nat) \/ (V 34%nat) + 4 <= 2147446784) -> L5KA.zeros_at M (((V 34%nat) / 8) + 2147450880) 1 -> L5.u32_at RSEGS M (V 34%nat) (V 38%nat) -> (((V 2%nat) - 4096) + 4096 <= (V 34%nat) \/ (V 34%nat) + 4 <= ((V 2%nat) - 4096)) ->
  ((V 33%nat) + 56 <= (V 34%nat) \/ (V 34%nat) + 4 <= (V 33%nat)) -> 0 <= (V 38%nat) <= 3 -> 4096 <= (V 40%nat) <= (140737488355328 - 2 * SZ) -> PEBEPP3.aligned (V 40%nat) 16 ->
  L5.writable RSEGS M ((V 40%nat) + SZ) 24 -> L5KA.zeros_at M ((((V 40%nat) + SZ) / 8) + 2147450880) 3 -> (2147446784 + 17592186048512 <= ((V 40%nat) + SZ) \/ ((V 40%nat) + SZ) + 24 <= 2147446784) -> 4096 <= ((V 40%nat) + SZ) <= 140737488355304 ->
  (((V 2%nat) - 4096) + 4096 <= ((V 40%nat) + SZ) \/ ((V 40%nat) + SZ) + 24 <= ((V 2%nat) - 4096)) -> ((V 33%nat) + 56 <= ((V 40%nat) + SZ) \/ ((V 40%nat) + SZ) + 24 <= (V 33%nat)) -> ((V 34%nat) + 4 <= ((V 40%nat) + SZ) \/ ((V 40%nat) + SZ) + 24 <= (V 34%nat)) -> (65536 + 6864896 <= ((V 40%nat) + SZ) \/ ((V 40%nat) + SZ) + 24 <= 65536) ->
  L5.u64_at RSEGS M ((V 2%nat) - 8) (V 43%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 44%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 45%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 46%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 40) (V 47%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 48%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 104) 737868 -> L5.u64_at RSEGS M ((V 2%nat) - 112) ((V 33%nat) + 32) ->
  L5.u64_at RSEGS M ((V 2%nat) - 120) ((V 33%nat) + 24) -> L5.u64_at RSEGS M ((V 2%nat) - 128) (V 34%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 136) ((((V 33%nat) + 32) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 144) 2147450880 ->
  L5.u64_at RSEGS M ((V 2%nat) - 152) (V 21%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) 0 -> L5.u64_at RSEGS M ((V 2%nat) - 56) ((V 33%nat) + 24) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 208) <= bv_unsigned a < ((V 2%nat) - 208) + 208) -> ~ ((((V 40%nat) + SZ) + 0) <= bv_unsigned a < (((V 40%nat) + SZ) + 0) + 24) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 208) <= i < ((V 2%nat) - 208) + 208) -> ~ ((((V 40%nat) + SZ) + 0) <= i < (((V 40%nat) + SZ) + 0) + 24) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb0be4 M) (st fx' R' 0x792dc M')
        /\ (forall x, In x PEBEPP3.KS_bpkG1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 737940
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 96)
        /\ getr R' (reg 8) = Z_to_bv 64 ((V 33%nat) + 32)
        /\ getr R' (reg 9) = Z_to_bv 64 ((V 33%nat) + 24)
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 40%nat) + (SZ + 8))
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 12) = Z_to_bv 64 16
        /\ getr R' (reg 13) = Z_to_bv 64 0
        /\ getr R' (reg 14) = Z_to_bv 64 0
        /\ getr R' (reg 15) = Z_to_bv 64 0
        /\ getr R' (reg 18) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 ((((V 33%nat) + 32) / 8) + 2147450880)
        /\ getr R' (reg 20) = Z_to_bv 64 2147450880
        /\ getr R' (reg 21) = Z_to_bv 64 (V 21%nat)
        /\ L5.u32_at RSEGS M' ((V 40%nat) + SZ) (V 38%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) ((V 40%nat) + (2 * SZ))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) ((V 40%nat) + SZ)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) ((V 40%nat) + SZ)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 88) (V 40%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 43%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (V 44%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (V 45%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (V 46%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (V 47%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (V 48%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) ((V 33%nat) + 24)).
Proof.
  intros Hk ENO ESZ ENC. subst SZ NC. subst NO.
  assert (KC : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11) by Lia.lia.
  clear Hk. destruct KC as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]].
  - exact (PEBEPP3.bpkG1_conc fx R M V).
  - exact (PEBEPP3.bpkG2_conc fx R M V).
  - exact (PEBEPP3.bpkG3_conc fx R M V).
  - exact (PEBEPP3.bpkG4_conc fx R M V).
  - exact (PEBEPP3.bpkG5_conc fx R M V).
  - exact (PEBEPP3.bpkG6_conc fx R M V).
  - exact (PEBEPP3.bpkG7_conc fx R M V).
  - exact (PEBEPP3.bpkG8_conc fx R M V).
  - exact (PEBEPP3.bpkG9_conc fx R M V).
  - exact (PEBEPP3.bpkG10_conc fx R M V).
  - exact (PEBEPP3.bpkG11_conc fx R M V).
Qed.

Lemma bpkH_uni fx R M (V : nat -> Z) (k SZ NC NO : Z) : 0 < k <= 11 -> NO = PEC.ecap k -> SZ = 24 * NO -> NC = 2 * NO ->
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 21%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 192) -> getr R (reg 8) = Z_to_bv 64 ((V 2%nat) - 88) -> getr R (reg 9) = Z_to_bv 64 ((V 33%nat) + 24) -> getr R (reg 18) = Z_to_bv 64 (V 34%nat) -> getr R (reg 19) = Z_to_bv 64 ((((V 33%nat) + 32) / 8) + 2147450880) -> getr R (reg 20) = Z_to_bv 64 2147450880 -> getr R (reg 21) = Z_to_bv 64 2147450880 ->
  140735332491264 <= (V 2%nat) <= 140737488355328 -> PEBEPP4.aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 4096) 4096 -> L5KA.zeros_at M (((V 2%nat) / 8) + 2147450368) 512 ->
  L5.img_clear M 65536 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 6930432 <= (V 33%nat) <= 140737488355263 ->
  PEBEPP4.aligned (V 33%nat) 8 -> (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 56 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 7 -> (((V 2%nat) - 4096) + 4096 <= (V 33%nat) \/ (V 33%nat) + 56 <= ((V 2%nat) - 4096)) ->
  (65536 + 6864896 <= (V 33%nat) \/ (V 33%nat) + 56 <= 65536) -> L5.u64_at RSEGS M ((V 33%nat) + 24) (V 36%nat) -> L5.u64_at RSEGS M ((V 33%nat) + 32) ((V 36%nat) + SZ) -> L5.u64_at RSEGS M ((V 33%nat) + 40) ((V 36%nat) + SZ) ->
  4096 <= (V 36%nat) <= 140737488355304 -> PEBEPP4.aligned (V 36%nat) 8 -> 4096 <= (V 40%nat) <= (140737488355328 - 2 * SZ) -> PEBEPP4.aligned (V 40%nat) 16 ->
  4096 <= ((V 40%nat) + SZ) <= 140737488355304 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 43%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 44%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 45%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 32) (V 46%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 47%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 48%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 104) 737976 ->
  L5.u64_at RSEGS M ((V 2%nat) - 112) ((V 33%nat) + 32) -> L5.u64_at RSEGS M ((V 2%nat) - 120) ((V 33%nat) + 24) -> L5.u64_at RSEGS M ((V 2%nat) - 128) (V 34%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 136) ((((V 33%nat) + 32) / 8) + 2147450880) ->
  L5.u64_at RSEGS M ((V 2%nat) - 144) 2147450880 -> L5.u64_at RSEGS M ((V 2%nat) - 152) (V 21%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 160) (bv_unsigned (getr R (reg 22))) -> L5.u64_at RSEGS M ((V 2%nat) - 168) (bv_unsigned (getr R (reg 23))) ->
  L5.u64_at RSEGS M ((V 2%nat) - 176) (bv_unsigned (getr R (reg 24))) -> L5.u64_at RSEGS M ((V 2%nat) - 184) 724288 -> L5.u64_at RSEGS M ((V 2%nat) - 192) ((V 2%nat) - 88) -> L5.u64_at RSEGS M ((V 2%nat) - 88) (V 40%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 80) ((V 40%nat) + SZ) -> L5.u64_at RSEGS M ((V 2%nat) - 72) ((V 40%nat) + (SZ + 24)) -> L5.u64_at RSEGS M ((V 2%nat) - 64) ((V 40%nat) + (2 * SZ)) -> L5.u64_at RSEGS M ((V 2%nat) - 56) ((V 33%nat) + 24) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 208) <= bv_unsigned a < ((V 2%nat) - 208) + 208) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 208) <= i < ((V 2%nat) - 208) + 208) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb1110 M) (st fx' R' 0x78e40 M')
        /\ (forall x, In x PEBEPP4.KS_bpkH1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 724444
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 176)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 40%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 SZ
        /\ getr R' (reg 13) = Z_to_bv 64 (18446744073709551616 - 4 * NC)
        /\ getr R' (reg 14) = Z_to_bv 64 0
        /\ getr R' (reg 18) = Z_to_bv 64 ((V 33%nat) + 32)
        /\ getr R' (reg 19) = Z_to_bv 64 ((V 2%nat) - 80)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 40%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 ((((V 33%nat) + 32) / 8) + 2147450880)
        /\ getr R' (reg 23) = Z_to_bv 64 ((((V 2%nat) - 80) / 8) + 2147450880)
        /\ getr R' (reg 24) = Z_to_bv 64 ((((V 33%nat) + 24) / 8) + 2147450880)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 43%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (V 44%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (V 45%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (V 46%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (V 47%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (V 48%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 104) 737976
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 112) ((V 33%nat) + 32)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 120) ((V 33%nat) + 24)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 128) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 136) ((((V 33%nat) + 32) / 8) + 2147450880)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 144) 2147450880
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 152) (V 21%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 160) (bv_unsigned (getr R (reg 22)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 168) (bv_unsigned (getr R (reg 23)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 176) (bv_unsigned (getr R (reg 24)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 88) (V 40%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) ((V 40%nat) + SZ)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) ((V 40%nat) + (SZ + 24))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) ((V 40%nat) + (2 * SZ))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) ((V 33%nat) + 24)).
Proof.
  intros Hk ENO ESZ ENC. subst SZ NC. subst NO.
  assert (KC : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11) by Lia.lia.
  clear Hk. destruct KC as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]].
  - exact (PEBEPP4.bpkH1_conc fx R M V).
  - exact (PEBEPP4.bpkH2_conc fx R M V).
  - exact (PEBEPP4.bpkH3_conc fx R M V).
  - exact (PEBEPP4.bpkH4_conc fx R M V).
  - exact (PEBEPP4.bpkH5_conc fx R M V).
  - exact (PEBEPP4.bpkH6_conc fx R M V).
  - exact (PEBEPP4.bpkH7_conc fx R M V).
  - exact (PEBEPP4.bpkH8_conc fx R M V).
  - exact (PEBEPP4.bpkH9_conc fx R M V).
  - exact (PEBEPP4.bpkH10_conc fx R M V).
  - exact (PEBEPP4.bpkH11_conc fx R M V).
Qed.

Lemma bpkI_uni fx R M (V : nat -> Z) (k SZ NC NO : Z) : 0 < k <= 11 -> NO = PEC.ecap k -> SZ = 24 * NO -> NC = 2 * NO ->
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 21%nat) < 2 ^ 64 -> 0 <= (V 22%nat) < 2 ^ 64 -> 0 <= (V 23%nat) < 2 ^ 64 -> 0 <= (V 24%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 176) -> getr R (reg 8) = Z_to_bv 64 ((V 2%nat) - 88) -> getr R (reg 9) = Z_to_bv 64 ((V 33%nat) + 24) -> getr R (reg 18) = Z_to_bv 64 ((V 33%nat) + 32) -> getr R (reg 19) = Z_to_bv 64 ((V 2%nat) - 80) -> getr R (reg 20) = Z_to_bv 64 (V 40%nat) -> getr R (reg 21) = Z_to_bv 64 2147450880 -> getr R (reg 22) = Z_to_bv 64 ((((V 33%nat) + 32) / 8) + 2147450880) -> getr R (reg 23) = Z_to_bv 64 ((((V 2%nat) - 80) / 8) + 2147450880) -> getr R (reg 24) = Z_to_bv 64 ((((V 33%nat) + 24) / 8) + 2147450880) ->
  140735332491264 <= (V 2%nat) <= 140737488355328 -> PEBEPP5.aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 4096) 4096 -> L5KA.zeros_at M (((V 2%nat) / 8) + 2147450368) 512 ->
  L5.img_clear M 65536 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 6930432 <= (V 33%nat) <= 140737488355263 ->
  PEBEPP5.aligned (V 33%nat) 8 -> (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 56 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 7 -> (((V 2%nat) - 4096) + 4096 <= (V 33%nat) \/ (V 33%nat) + 56 <= ((V 2%nat) - 4096)) ->
  (65536 + 6864896 <= (V 33%nat) \/ (V 33%nat) + 56 <= 65536) -> L5.writable RSEGS M ((V 33%nat) + 24) 24 -> L5.u64_at RSEGS M ((V 33%nat) + 24) (V 36%nat) -> L5.u64_at RSEGS M ((V 33%nat) + 32) ((V 36%nat) + SZ) ->
  L5.u64_at RSEGS M ((V 33%nat) + 40) ((V 36%nat) + SZ) -> 4096 <= (V 36%nat) <= 140737488355304 -> PEBEPP5.aligned (V 36%nat) 8 -> 4096 <= (V 40%nat) <= (140737488355328 - 2 * SZ) ->
  PEBEPP5.aligned (V 40%nat) 16 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 43%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 44%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 45%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 32) (V 46%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 47%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 48%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 104) 737976 ->
  L5.u64_at RSEGS M ((V 2%nat) - 112) ((V 33%nat) + 32) -> L5.u64_at RSEGS M ((V 2%nat) - 120) ((V 33%nat) + 24) -> L5.u64_at RSEGS M ((V 2%nat) - 128) (V 34%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 136) ((((V 33%nat) + 32) / 8) + 2147450880) ->
  L5.u64_at RSEGS M ((V 2%nat) - 144) 2147450880 -> L5.u64_at RSEGS M ((V 2%nat) - 152) (V 21%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 160) (V 22%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 168) (V 23%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 176) (V 24%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 88) (V 40%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 80) ((V 40%nat) + SZ) -> L5.u64_at RSEGS M ((V 2%nat) - 72) ((V 40%nat) + (SZ + 24)) ->
  L5.u64_at RSEGS M ((V 2%nat) - 64) ((V 40%nat) + (2 * SZ)) -> L5.u64_at RSEGS M ((V 2%nat) - 56) ((V 33%nat) + 24) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 208) <= bv_unsigned a < ((V 2%nat) - 208) + 208) -> ~ (((V 33%nat) + 24) <= bv_unsigned a < ((V 33%nat) + 24) + 24) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 208) <= i < ((V 2%nat) - 208) + 208) -> ~ (((V 33%nat) + 24) <= i < ((V 33%nat) + 24) + 24) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb0ddc M) (st fx' R' 0x7cc28 M')
        /\ (forall x, In x PEBEPP5.KS_bpkI1 -> getr R' (reg x) = getr R (reg x))
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
        /\ getr R' (reg 18) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 ((((V 33%nat) + 32) / 8) + 2147450880)
        /\ getr R' (reg 20) = Z_to_bv 64 2147450880
        /\ getr R' (reg 21) = Z_to_bv 64 (V 21%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 22%nat)
        /\ getr R' (reg 23) = Z_to_bv 64 (V 23%nat)
        /\ getr R' (reg 24) = Z_to_bv 64 (V 24%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 112) ((V 33%nat) + 32)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 104) 737976
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 88) (V 36%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) ((V 36%nat) + SZ)
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 40) ((V 40%nat) + (2 * SZ))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) (V 36%nat)
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 32) ((V 40%nat) + (SZ + 24))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) (V 36%nat)
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 24) (V 40%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 43%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (V 44%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (V 45%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (V 46%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (V 47%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (V 48%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) ((V 33%nat) + 24)).
Proof.
  intros Hk ENO ESZ ENC. subst SZ NC. subst NO.
  assert (KC : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11) by Lia.lia.
  clear Hk. destruct KC as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]].
  - exact (PEBEPP5.bpkI1_conc fx R M V).
  - exact (PEBEPP5.bpkI2_conc fx R M V).
  - exact (PEBEPP5.bpkI3_conc fx R M V).
  - exact (PEBEPP5.bpkI4_conc fx R M V).
  - exact (PEBEPP5.bpkI5_conc fx R M V).
  - exact (PEBEPP5.bpkI6_conc fx R M V).
  - exact (PEBEPP5.bpkI7_conc fx R M V).
  - exact (PEBEPP5.bpkI8_conc fx R M V).
  - exact (PEBEPP5.bpkI9_conc fx R M V).
  - exact (PEBEPP5.bpkI10_conc fx R M V).
  - exact (PEBEPP5.bpkI11_conc fx R M V).
Qed.

End PEBEPU.
