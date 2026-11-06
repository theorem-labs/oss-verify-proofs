(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA IcptIfaceAB0 L5Defs L5Core L5CoreKit L5KnA L5LazyA L5DefsAB0 L5CoreAB0S9 L5StepARB0S9.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PmLayout PmLayoutA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PmModel PmStatics PmStaticsA HeapIfaceAEx PmSpecsA PmSpecsAX PeSpecsAb PeSpecsBXJ PnStatics.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PeCLayoutB.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PeCModelA PeCSpecsA PeCSpecsAb.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PeCLayout.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PeCSink PeCModel.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.Spec Require Import UbjRef.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module PEBEQGS.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Abbreviation AD := PeCLayoutB.CADDR_B.

Section Mid.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (HI : asan_iface).
Variables (R : bvmap 5 word) (M : word -> option byte) (model : Model) (LBX : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit)
          (ov b k : Z) (stk : list eitem) (sp pk pl kd ln : Z).

Definition SZ : Z := 24 * PEC.ecap k.

Definition gmid (B : Z) (R6 : bvmap 5 word) (M6 : word -> option byte) (model6 : Model) (Aw6 : list (Z * Z)) : Prop :=

  getr R6 (reg 2) = Z_to_bv 64 (sp - 176) /\ getr R6 (reg 8) = Z_to_bv 64 (sp - 96) /\ getr R6 (reg 9) = Z_to_bv 64 (ov + 24)
  /\ getr R6 (reg 18) = Z_to_bv 64 (ov + 32) /\ getr R6 (reg 19) = Z_to_bv 64 (sp - 88) /\ getr R6 (reg 20) = Z_to_bv 64 B /\ getr R6 (reg 21) = Z_to_bv 64 2147450880
  /\ getr R6 (reg 22) = Z_to_bv 64 ((ov + 32) / 8 + 2147450880) /\ getr R6 (reg 23) = Z_to_bv 64 ((sp - 88) / 8 + 2147450880)
  /\ getr R6 (reg 24) = Z_to_bv 64 ((ov + 24) / 8 + 2147450880)
  /\ (forall x, In x [3; 4; 25; 26; 27]%nat -> getr R6 (reg x) = getr R (reg x))

  /\ L5.u64_at RSEGS M6 (sp - 8) (bv_unsigned (getr R (reg 1))) /\ L5.u64_at RSEGS M6 (sp - 16) (bv_unsigned (getr R (reg 8)))
  /\ L5.u64_at RSEGS M6 (sp - 24) (bv_unsigned (getr R (reg 9))) /\ L5.u64_at RSEGS M6 (sp - 32) (bv_unsigned (getr R (reg 18)))
  /\ L5.u64_at RSEGS M6 (sp - 40) (bv_unsigned (getr R (reg 19))) /\ L5.u64_at RSEGS M6 (sp - 48) (bv_unsigned (getr R (reg 20)))
  /\ L5.u64_at RSEGS M6 (sp - 56) (bv_unsigned (getr R (reg 21)))
  /\ L5.u64_at RSEGS M6 (sp - 104) 722872 /\ L5.u64_at RSEGS M6 (sp - 112) (ov + 32) /\ L5.u64_at RSEGS M6 (sp - 120) (ov + 24)
  /\ L5.u64_at RSEGS M6 (sp - 128) pl /\ L5.u64_at RSEGS M6 (sp - 136) pk /\ L5.u64_at RSEGS M6 (sp - 144) ((ov + 32) / 8 + 2147450880)
  /\ L5.u64_at RSEGS M6 (sp - 152) 2147450880 /\ L5.u64_at RSEGS M6 (sp - 160) (bv_unsigned (getr R (reg 22)))
  /\ L5.u64_at RSEGS M6 (sp - 168) (bv_unsigned (getr R (reg 23))) /\ L5.u64_at RSEGS M6 (sp - 176) (bv_unsigned (getr R (reg 24)))
  /\ L5.u64_at RSEGS M6 (sp - 96) B /\ L5.u64_at RSEGS M6 (sp - 88) (B + SZ) /\ L5.u64_at RSEGS M6 (sp - 80) (B + SZ + 24)
  /\ L5.u64_at RSEGS M6 (sp - 72) (B + 2 * SZ) /\ L5.u64_at RSEGS M6 (sp - 64) (ov + 24)

  /\ L5.u64_at RSEGS M6 (ov + 24) b /\ L5.u64_at RSEGS M6 (ov + 32) (b + SZ) /\ L5.u64_at RSEGS M6 (ov + 40) (b + SZ) /\ PMSPA.accA M6 ov 56

  /\ 4096 <= B /\ B + 2 * SZ <= ahl_ceil ar /\ B mod 16 = 0 /\ app_mem B (2 * SZ) /\ (B + 2 * SZ <= 65536 \/ 0x69c000 <= B)
  /\ (B + 2 * SZ <= b \/ b + SZ <= B) /\ (ov + 56 <= B \/ B + 2 * SZ <= ov) /\ ablock_range L ar B (2 * SZ)
  /\ L5.defined M6 B (2 * SZ) /\ shadow_zero M6 B (2 * SZ / 8)
  /\ (forall i, (i < length stk)%nat -> PEC.eitem_at RSEGS M6 (B + 24 * Z.of_nat i) (nth i stk (EI 0 0 0)))
  /\ PEC.eitem_at RSEGS M6 (B + SZ) (EI kd ln 0)

  /\ ri_inv HI ((B, 2 * SZ) :: (b, SZ) :: LBX) FF LK (adebit L cr (2 * SZ)) Aw6 M6 (vml_of model6) /\ L5CA.amodel_ok Aw6 model6
  /\ model_rt model model6 /\ incl Aw Aw6 /\ L5CA.astk ar M6 sp 12288 /\ shadow_zero M6 (sp - 12288) 1536 /\ PMSTA.base_okA RSEGS AD M6
  /\ (forall a, 0 <= a < 2 ^ 64 -> aclient L ar LBX FF 0 0 a -> ~ (sp - 12288 <= a < sp) -> ~ (ov + 24 <= a < ov + 48) -> M6 (Z_to_bv 64 a) = M (Z_to_bv 64 a))
  /\ (forall a, 0 <= a < 2 ^ 64 -> aclient L ar LBX FF 0 0 a -> M (Z_to_bv 64 a) <> None -> M6 (Z_to_bv 64 a) <> None).
End Mid.
End PEBEQGS.
