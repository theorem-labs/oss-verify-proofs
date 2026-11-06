(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA IcptIfaceA L5Defs L5Core L5CoreKit L5KnA L5LazyA L5DefsA L5CoreAS8 L5StepARS8.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PmLayout PmLayoutA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PmModel PmStatics PmStaticsA HeapIfaceAEx PmSpecsA PmSpecsAX PeSpecsAa PnStatics.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PeCLayoutA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PeCModelA PeCSpecsA PeCSpecsAa.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module PMAESGS.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := Asan.M.loaded_segments.

Section Mid.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (HI : asan_iface).
Variables (R : bvmap 5 word) (M : word -> option byte) (model : Model) (LBX : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit)
          (v b k : Z) (stk : list PM.pstate) (sp r p1 p2 p3 m n t : Z).

Definition SZ : Z := 32 * 2 ^ k.

Definition gmid (B : Z) (R6 : bvmap 5 word) (M6 : word -> option byte) (model6 : Model) (Aw6 : list (Z * Z)) : Prop :=

  getr R6 (reg 2) = Z_to_bv 64 (sp - 160) /\ getr R6 (reg 8) = Z_to_bv 64 (sp - 112) /\ getr R6 (reg 9) = Z_to_bv 64 v
  /\ getr R6 (reg 18) = Z_to_bv 64 B /\ getr R6 (reg 19) = Z_to_bv 64 2147450880 /\ getr R6 (reg 20) = Z_to_bv 64 p1 /\ getr R6 (reg 21) = Z_to_bv 64 SZ
  /\ getr R6 (reg 22) = Z_to_bv 64 ((v + 8) / 8 + 2147450880) /\ getr R6 (reg 23) = Z_to_bv 64 2147450880
  /\ (forall x, In x [3; 4; 24; 25; 26; 27]%nat -> getr R6 (reg x) = getr R (reg x))

  /\ L5.u64_at RSEGS M6 (sp - 8) (bv_unsigned (getr R (reg 1))) /\ L5.u64_at RSEGS M6 (sp - 16) (bv_unsigned (getr R (reg 8)))
  /\ L5.u64_at RSEGS M6 (sp - 24) (bv_unsigned (getr R (reg 9))) /\ L5.u64_at RSEGS M6 (sp - 32) (bv_unsigned (getr R (reg 18)))
  /\ L5.u64_at RSEGS M6 (sp - 40) (bv_unsigned (getr R (reg 19))) /\ L5.u64_at RSEGS M6 (sp - 48) (bv_unsigned (getr R (reg 20)))
  /\ L5.u64_at RSEGS M6 (sp - 56) (bv_unsigned (getr R (reg 21))) /\ L5.u64_at RSEGS M6 (sp - 64) (bv_unsigned (getr R (reg 22)))
  /\ L5.u64_at RSEGS M6 (sp - 72) (bv_unsigned (getr R (reg 23)))
  /\ L5.u64_at RSEGS M6 (sp - 120) 752724 /\ L5.u64_at RSEGS M6 (sp - 128) (v + 8) /\ L5.u64_at RSEGS M6 (sp - 136) p3
  /\ L5.u64_at RSEGS M6 (sp - 144) v /\ L5.u64_at RSEGS M6 (sp - 152) p2
  /\ L5.u64_at RSEGS M6 (sp - 112) B /\ L5.u64_at RSEGS M6 (sp - 104) (B + SZ) /\ L5.u64_at RSEGS M6 (sp - 96) (B + (SZ + 32))
  /\ L5.u64_at RSEGS M6 (sp - 88) (B + 2 * SZ) /\ L5.u64_at RSEGS M6 (sp - 80) v

  /\ L5.u64_at RSEGS M6 v b /\ L5.u64_at RSEGS M6 (v + 8) (b + SZ) /\ L5.u64_at RSEGS M6 (v + 16) (b + SZ) /\ PMSPA.accA M6 v 24

  /\ 4096 <= B /\ B + 2 * SZ <= ahl_ceil ar /\ B mod 16 = 0 /\ app_mem B (2 * SZ) /\ (B + 2 * SZ <= 65536 \/ 0x698000 <= B)
  /\ (B + 2 * SZ <= b \/ b + SZ <= B) /\ (v + 24 <= B \/ B + 2 * SZ <= v)
  /\ L5.defined M6 B (2 * SZ) /\ shadow_zero M6 B (2 * SZ / 8)
  /\ (forall i, (i < length stk)%nat -> PM.pstate_at RSEGS M6 (B + 32 * Z.of_nat i) (nth i stk PM.ps_root))
  /\ PM.pstate_at RSEGS M6 (B + SZ) (PM.PS m n t 0)

  /\ ri_inv HI ((B, 2 * SZ) :: PM.vec_own b k ++ LBX) FF LK (adebit L cr (2 * SZ)) Aw6 M6 (vml_of model6) /\ L5CA.amodel_ok Aw6 model6
  /\ model_rt model model6 /\ incl Aw Aw6 /\ L5CA.astk ar M6 sp 12288 /\ shadow_zero M6 (sp - 12288) 1536
  /\ (forall a, 0 <= a < 2 ^ 64 -> aclient L ar LBX FF 0 0 a -> ~ (sp - 12288 <= a < sp) -> ~ (v <= a < v + 24) -> M6 (Z_to_bv 64 a) = M (Z_to_bv 64 a))
  /\ (forall a, 0 <= a < 2 ^ 64 -> aclient L ar LBX FF 0 0 a -> M (Z_to_bv 64 a) <> None -> M6 (Z_to_bv 64 a) <> None).
End Mid.
End PMAESGS.
