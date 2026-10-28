(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnASrcKit_b PgSrcKitA_b PnASrcRead1_b PnASrcReadK_b PnASrcReadP_b Ba0PgSrcReadK16_b Ba0PgSrcReadC16_b Ba0PgSrcReadMB16_b Ba0PgSrcReadMQ16_b Ba0PgSrcReadMBB16_b.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.LeanFeed.
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA HeapIfaceABx. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import IcptIfaceA_b.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import L5Defs L5Core L5CoreKit L5Kn L5KnA L5LazyA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import L5DefsA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.asan Require Import L5CoreA_b L5StepAR_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnLayoutA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmModel PmModelFacts PmStatics PmStaticsA PmSpecs PmParSpecs. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PmSpecsA_b PmSpecsAX_b PnSpecsAa_b
     PmModelFactsA_b PnStepA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmStep PmParStep. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnASrcKit_b PnASrcReadK_b PnASrcRead1_b PnASrcReadP_b Ba0_code_raf314_af318_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PgSrc. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PgSrcA_b PgSrcKitA_b PnRunA_b PmAUarK_b PmAUar_b PnAReadCsK_b.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := first [ L5FastLia.plia | Lia.lia ].

Module PGSRDMS16.
Abbreviation RSEGS := PGSRDK16.RSEGS.
Abbreviation mem := (word -> option byte).
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).

Section WithHeap.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).

Definition srd_mc_post_T (al : Z) : Prop :=
  forall (O : PGS.owner) (R0 : bvmap 5 word) (M0 : mem) (model0 : Model) (K : TSet) (OB LBX : list (Z * Z))
         (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (sp r : Z) (str : PM.vstr) (Wextra : list L5.range)
         (qc de rem g eg sst p k : Z),
    PGSRDK16.srd_ctx L ar HI al O R0 M0 model0 K OB LBX FF LK Aw cr sp r (PM.SRC qc de rem) str (PM.STRM g eg sst) Wextra ->
    getr R0 (reg 11) = Z_to_bv 64 p -> getr R0 (reg 12) = Z_to_bv 64 k ->
    forall (F fl : Z) (LK2 : list fframe) (M2 : mem) (model2 : Model),
    PGSRDK16.srd_frame L ar HI al R0 OB LBX FF LK Aw cr sp (PM.SRC qc de rem) F fl LK2 M2 model2 ->
    forall (fx : FPState) (R : bvmap 5 word) (M : mem) (model : Model) (LKc : list fframe) (Ac : list (Z * Z))
           (V : nat -> Z),
    PGSRDK16.srd_body L ar HI al O R0 M0 model0 OB LBX FF LK Aw sp (PM.SRC qc de rem) Wextra F M model LKc cr Ac ->
    V 2%nat = sp - al -> V 36%nat = PGS.ow_os O -> V 37%nat = p -> V 38%nat = k -> 32 * V 50%nat = F -> V 51%nat = fl ->
    (forall i, In i [1; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> V i = bv_unsigned (getr R0 (reg i))) ->
    getr R (reg 3) = getr R0 (reg 3) -> getr R (reg 4) = getr R0 (reg 4) ->
    V 34%nat = qc -> V 35%nat = de -> V 45%nat = PGS.ow_ois O ->
    PM.iss_at RSEGS PMA.AD PMSPA.accA M (PGS.ow_ois O) str (PM.STRM g eg sst) ->
    PGSRDK16.srd_stA V R (mrestrict (ahid Ac model) M) -> PGSRDK16.srd_pathG V R (mrestrict (ahid Ac model) M) rem sst ->
    forall (len1 : Z) (fx3 : FPState) (R3 : bvmap 5 word) (M3 : mem) (model3 : Model),
    len1 = Z.min k rem ->
    PGSRDK16.srd_body L ar HI al O R0 M0 model0 OB LBX FF LK Aw sp (PM.SRC qc de rem) Wextra F M3 model3 LKc cr Ac ->
    L5.defined M3 p len1 ->
    PGS.ow_at O M3 (PM.SRC qc de rem) OB -> PM.iss_at RSEGS PMA.AD PMSPA.accA M3 (PGS.ow_ois O) str (PM.STRM g eg sst) ->
    PMSTA.base_okA RSEGS PMA.AD M3 ->
    (forall i, 0 <= i < 2 ^ 64 ->
      (sp - 160 - al <= i < sp) \/ (F <= i < F + 120 /\ ~ (F + 24 <= i < F + 32)) \/ (F / 8 + SB <= i < F / 8 + SB + 16)
      \/ (PGS.ow_os O <= i < PGS.ow_os O + 296) \/ ((PGS.ow_os O + 8) / 8 + SB <= i < (PGS.ow_os O + 8) / 8 + SB + 36) ->
      ~ ((((V 2%nat) - 152) <= i < ((V 2%nat) - 152) + 16) \/ (((V 2%nat) - 112) <= i < ((V 2%nat) - 112) + 8) \/ (((32 * (V 50%nat)) + 0) <= i < ((32 * (V 50%nat)) + 0) + 24) \/ (((32 * (V 50%nat)) + 32) <= i < ((32 * (V 50%nat)) + 32) + 8) \/ (((4 * (V 50%nat)) + 2147450880) <= i < ((4 * (V 50%nat)) + 2147450880) + 12)) -> ~ (p <= i < p + len1) ->
      mrestrict (ahid Ac model3) M3 (Z_to_bv 64 i) = mrestrict (ahid Ac model) M (Z_to_bv 64 i)) ->
    getr R3 (reg 2) = Z_to_bv 64 ((V 2%nat) - 160) ->
    getr R3 (reg 8) = Z_to_bv 64 ((V 2%nat) + 16) ->
    getr R3 (reg 9) = Z_to_bv 64 ((V 2%nat) - 160) ->
    getr R3 (reg 18) = Z_to_bv 64 ((((V 36%nat) + 288) / 8) + 2147450880) ->
    getr R3 (reg 19) = Z_to_bv 64 (V 36%nat) ->
    getr R3 (reg 20) = Z_to_bv 64 len1 ->
    getr R3 (reg 21) = Z_to_bv 64 ((((V 36%nat) + 280) / 8) + 2147450880) ->
    getr R3 (reg 22) = Z_to_bv 64 (V 38%nat) ->
    getr R3 (reg 23) = Z_to_bv 64 ((V 36%nat) + 288) ->
    getr R3 (reg 24) = Z_to_bv 64 ((V 36%nat) + 280) ->
    getr R3 (reg 25) = Z_to_bv 64 ((4 * (V 50%nat)) + 2147450880) ->
    getr R3 (reg 26) = Z_to_bv 64 (32 * (V 50%nat)) ->
    (forall x, In x [3; 4; 27]%nat -> getr R3 (reg x) = getr R (reg x)) ->
    L5.u64_at RSEGS (mrestrict (ahid Ac model3) M3) ((V 2%nat) - 152) ((32 * (V 50%nat)) + 32) ->
    L5.u64_at RSEGS (mrestrict (ahid Ac model3) M3) ((V 2%nat) - 144) (32 * (V 50%nat)) ->
    L5.u64_at RSEGS (mrestrict (ahid Ac model3) M3) ((V 2%nat) - 112) (32 * (V 50%nat)) ->
    L5.u64_at RSEGS (mrestrict (ahid Ac model3) M3) ((32 * (V 50%nat)) + 32) (V 38%nat) ->
    L5.u8_at RSEGS (mrestrict (ahid Ac model3) M3) ((4 * (V 50%nat)) + 2147450891) 243 ->
    L5.u8_at RSEGS (mrestrict (ahid Ac model3) M3) ((4 * (V 50%nat)) + 2147450890) 243 ->
    L5.u8_at RSEGS (mrestrict (ahid Ac model3) M3) ((4 * (V 50%nat)) + 2147450889) 243 ->
    L5.u8_at RSEGS (mrestrict (ahid Ac model3) M3) ((4 * (V 50%nat)) + 2147450888) 248 ->
    L5.u8_at RSEGS (mrestrict (ahid Ac model3) M3) ((4 * (V 50%nat)) + 2147450883) 241 ->
    L5.u8_at RSEGS (mrestrict (ahid Ac model3) M3) ((4 * (V 50%nat)) + 2147450882) 241 ->
    L5.u8_at RSEGS (mrestrict (ahid Ac model3) M3) ((4 * (V 50%nat)) + 2147450881) 241 ->
    L5.u8_at RSEGS (mrestrict (ahid Ac model3) M3) ((4 * (V 50%nat)) + 2147450880) 241 ->
    L5.u8_at RSEGS (mrestrict (ahid Ac model3) M3) ((4 * (V 50%nat)) + 2147450887) 242 ->
    L5.u8_at RSEGS (mrestrict (ahid Ac model3) M3) ((4 * (V 50%nat)) + 2147450886) 242 ->
    L5.u8_at RSEGS (mrestrict (ahid Ac model3) M3) ((4 * (V 50%nat)) + 2147450885) 242 ->
    L5.u8_at RSEGS (mrestrict (ahid Ac model3) M3) ((4 * (V 50%nat)) + 2147450884) 0 ->
    L5.u64_at RSEGS (mrestrict (ahid Ac model3) M3) ((32 * (V 50%nat)) + 16) 716108 ->
    L5.u64_at RSEGS (mrestrict (ahid Ac model3) M3) ((32 * (V 50%nat)) + 8) 127274 ->
    L5.u64_at RSEGS (mrestrict (ahid Ac model3) M3) (32 * (V 50%nat)) 1102416563 ->
    L5.defined (mrestrict (ahid Ac model3) M3) ((32 * (V 50%nat)) + 24) 8 ->
    L5.defined (mrestrict (ahid Ac model3) M3) ((32 * (V 50%nat)) + 40) 88 ->
    srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx3 R3 0xaeed4 M3 model3) K.

Definition vxMS (V : nat -> Z) (R : bvmap 5 word) (len1 : Z) : nat -> Z := fun i =>
  match i with 39%nat => len1 | _ => PGSRDMB16.vxC V R i end.

Definition srd_stM_R (V : nat -> Z) (R : bvmap 5 word) : Prop :=
  (0 <= (V 1%nat) < 2 ^ 64)
  /\ (0 <= (V 2%nat) < 2 ^ 64)
  /\ (0 <= (V 8%nat) < 2 ^ 64)
  /\ (0 <= (V 9%nat) < 2 ^ 64)
  /\ (0 <= (V 18%nat) < 2 ^ 64)
  /\ (0 <= (V 19%nat) < 2 ^ 64)
  /\ (0 <= (V 20%nat) < 2 ^ 64)
  /\ (0 <= (V 21%nat) < 2 ^ 64)
  /\ (0 <= (V 22%nat) < 2 ^ 64)
  /\ (0 <= (V 23%nat) < 2 ^ 64)
  /\ (0 <= (V 24%nat) < 2 ^ 64)
  /\ (0 <= (V 25%nat) < 2 ^ 64)
  /\ (0 <= (V 26%nat) < 2 ^ 64)
  /\ (0 <= (V 27%nat) < 2 ^ 64)
  /\ (0 <= (V 34%nat) < 2 ^ 64)
  /\ (0 <= (V 35%nat) < 2 ^ 64)
  /\ (0 <= (V 36%nat) < 2 ^ 64)
  /\ (0 <= (V 37%nat) < 2 ^ 64)
  /\ (0 <= (V 38%nat) < 2 ^ 64)
  /\ (0 <= (V 39%nat) < 2 ^ 64)
  /\ (0 <= (V 50%nat) < 2 ^ 64)
  /\ (0 <= (V 51%nat) < 2 ^ 64)
  /\ (0 <= (V 61%nat) < 2 ^ 64)
  /\ (0 <= (V 62%nat) < 2 ^ 64)
  /\ (0 <= (V 63%nat) < 2 ^ 64)
  /\ (0 <= (V 64%nat) < 2 ^ 64)
  /\ (0 <= (V 65%nat) < 2 ^ 64)
  /\ (0 <= (V 66%nat) < 2 ^ 64)
  /\ (0 <= (V 67%nat) < 2 ^ 64)
  /\ (0 <= (V 68%nat) < 2 ^ 64)
  /\ (0 <= (V 69%nat) < 2 ^ 64)
  /\ (0 <= (V 70%nat) < 2 ^ 64)
  /\ (0 <= (V 71%nat) < 2 ^ 64)
  /\ (0 <= (V 72%nat) < 2 ^ 64)
  /\ (0 <= (V 73%nat) < 2 ^ 64)
  /\ (0 <= (V 74%nat) < 2 ^ 64)
  /\ (getr R (reg 1) = Z_to_bv 64 (V 61%nat))
  /\ (getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 160))
  /\ (getr R (reg 5) = Z_to_bv 64 (V 62%nat))
  /\ (getr R (reg 6) = Z_to_bv 64 (V 63%nat))
  /\ (getr R (reg 7) = Z_to_bv 64 (V 64%nat))
  /\ (getr R (reg 8) = Z_to_bv 64 ((V 2%nat) + 16))
  /\ (getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 160))
  /\ (getr R (reg 12) = Z_to_bv 64 (V 65%nat))
  /\ (getr R (reg 13) = Z_to_bv 64 (V 66%nat))
  /\ (getr R (reg 14) = Z_to_bv 64 (V 67%nat))
  /\ (getr R (reg 15) = Z_to_bv 64 (V 68%nat))
  /\ (getr R (reg 16) = Z_to_bv 64 (V 69%nat))
  /\ (getr R (reg 17) = Z_to_bv 64 (V 70%nat))
  /\ (getr R (reg 18) = Z_to_bv 64 ((((V 36%nat) + 288) / 8) + 2147450880))
  /\ (getr R (reg 19) = Z_to_bv 64 (V 36%nat))
  /\ (getr R (reg 20) = Z_to_bv 64 (V 39%nat))
  /\ (getr R (reg 21) = Z_to_bv 64 ((((V 36%nat) + 280) / 8) + 2147450880))
  /\ (getr R (reg 23) = Z_to_bv 64 ((V 36%nat) + 288))
  /\ (getr R (reg 24) = Z_to_bv 64 ((V 36%nat) + 280))
  /\ (getr R (reg 25) = Z_to_bv 64 ((4 * (V 50%nat)) + 2147450880))
  /\ (getr R (reg 26) = Z_to_bv 64 (32 * (V 50%nat)))
  /\ (getr R (reg 27) = Z_to_bv 64 2147450880)
  /\ (getr R (reg 28) = Z_to_bv 64 (V 71%nat))
  /\ (getr R (reg 29) = Z_to_bv 64 (V 72%nat))
  /\ (getr R (reg 30) = Z_to_bv 64 (V 73%nat))
  /\ (getr R (reg 31) = Z_to_bv 64 (V 74%nat))
  /\ (140735332487232 <= (V 2%nat) <= 140737488355312)
  /\ ((V 2%nat) mod 32 = 0)
  /\ (6905856 <= (V 36%nat) <= 140737488355032)
  /\ ((V 36%nat) mod 8 = 0)
  /\ (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 296 <= 2147446784)
  /\ (((V 2%nat) - 160) + 176 <= (V 36%nat) \/ (V 36%nat) + 296 <= ((V 2%nat) - 160))
  /\ (140735332487248 <= (V 2%nat) <= 140737488355328)
  /\ (((V 2%nat) - 160) + 160 <= (V 36%nat) \/ (V 36%nat) + 296 <= ((V 2%nat) - 160))
  /\ (4096 <= (V 35%nat) <= 140737488338944)
  /\ (215808 <= (V 50%nat) <= 4398046511102)
  /\ ((V 50%nat) mod 4 = 0)
  /\ (2147446784 + 17592186048512 <= (32 * (V 50%nat)) \/ (32 * (V 50%nat)) + 128 <= 2147446784)
  /\ (4096 <= (V 51%nat) <= 140737488355327)
  /\ (2147446784 + 17592186048512 <= (V 51%nat) \/ (V 51%nat) + 1 <= 2147446784)
  /\ ((32 * (V 50%nat)) + 128 <= (V 51%nat) \/ (V 51%nat) + 1 <= (32 * (V 50%nat)))
  /\ (((V 2%nat) - 160) + 176 <= (32 * (V 50%nat)) \/ (32 * (V 50%nat)) + 128 <= ((V 2%nat) - 160))
  /\ (((V 2%nat) - 160) + 176 <= (V 51%nat) \/ (V 51%nat) + 1 <= ((V 2%nat) - 160))
  /\ ((32 * (V 50%nat)) + 128 <= ((4 * (V 50%nat)) + 2147450880) \/ ((4 * (V 50%nat)) + 2147450880) + 16 <= (32 * (V 50%nat)))
  /\ ((V 51%nat) + 1 <= ((4 * (V 50%nat)) + 2147450880) \/ ((4 * (V 50%nat)) + 2147450880) + 16 <= (V 51%nat))
  /\ (((V 2%nat) - 160) + 176 <= ((4 * (V 50%nat)) + 2147450880) \/ ((4 * (V 50%nat)) + 2147450880) + 16 <= ((V 2%nat) - 160))
  /\ ((32 * (V 50%nat)) + 128 <= (V 36%nat) \/ (V 36%nat) + 296 <= (32 * (V 50%nat)))
  /\ ((V 51%nat) + 1 <= (V 36%nat) \/ (V 36%nat) + 296 <= (V 51%nat))
  /\ (((4 * (V 50%nat)) + 2147450880) + 16 <= (V 36%nat) \/ (V 36%nat) + 296 <= ((4 * (V 50%nat)) + 2147450880))
  /\ (((4 * (V 50%nat)) + 2147450880) + 16 <= ((((V 36%nat) + 8) / 8) + 2147450880) \/ ((((V 36%nat) + 8) / 8) + 2147450880) + 36 <= ((4 * (V 50%nat)) + 2147450880))
  /\ ((32 * (V 50%nat)) + 128 <= ((((V 36%nat) + 8) / 8) + 2147450880) \/ ((((V 36%nat) + 8) / 8) + 2147450880) + 36 <= (32 * (V 50%nat)))
  /\ ((V 51%nat) + 1 <= ((((V 36%nat) + 8) / 8) + 2147450880) \/ ((((V 36%nat) + 8) / 8) + 2147450880) + 36 <= (V 51%nat)).

Definition srd_stM_C (V : nat -> Z) (R : bvmap 5 word) (M : mem) : Prop :=
  (L5.img_clear M 65536 1282048)
  /\ (L5.u64_at RSEGS M 1309752 2147450880)
  /\ (L5.u32_at RSEGS M 1309760 1)
  /\ (L5.writable RSEGS M ((V 2%nat) - 160) 176)
  /\ (L5KA.zeros_at M ((((V 36%nat) + 8) / 8) + 2147450880) 36)
  /\ (L5.writable RSEGS M (V 36%nat) 296)
  /\ (L5.u64_at RSEGS M ((V 36%nat) + 264) (V 34%nat))
  /\ (L5.u64_at RSEGS M ((V 36%nat) + 272) 16384)
  /\ (L5.u64_at RSEGS M ((V 36%nat) + 280) (V 35%nat))
  /\ (L5.defined M ((V 36%nat) + 256) 8)
  /\ (L5.writable RSEGS M ((V 2%nat) - 160) 160)
  /\ (L5.u64_at RSEGS M (V 2%nat) (V 8%nat))
  /\ (L5.u64_at RSEGS M ((V 2%nat) + 8) (V 1%nat))
  /\ (L5.defined M (32 * (V 50%nat)) 128)
  /\ (L5.writable RSEGS M (32 * (V 50%nat)) 128)
  /\ (L5.writable RSEGS M ((4 * (V 50%nat)) + 2147450880) 16)
  /\ (L5.writable RSEGS M (V 51%nat) 1)
  /\ (L5.u64_at RSEGS M ((V 2%nat) - 152) ((32 * (V 50%nat)) + 32))
  /\ (L5.u64_at RSEGS M ((V 2%nat) - 144) (32 * (V 50%nat)))
  /\ (L5.u64_at RSEGS M ((V 2%nat) - 112) (32 * (V 50%nat)))
  /\ (L5.u64_at RSEGS M ((32 * (V 50%nat)) + 32) (V 38%nat))
  /\ (L5.u8_at RSEGS M ((4 * (V 50%nat)) + 2147450891) 243)
  /\ (L5.u8_at RSEGS M ((4 * (V 50%nat)) + 2147450890) 243)
  /\ (L5.u8_at RSEGS M ((4 * (V 50%nat)) + 2147450889) 243)
  /\ (L5.u8_at RSEGS M ((4 * (V 50%nat)) + 2147450888) 248)
  /\ (L5.u8_at RSEGS M ((4 * (V 50%nat)) + 2147450883) 241)
  /\ (L5.u8_at RSEGS M ((4 * (V 50%nat)) + 2147450882) 241)
  /\ (L5.u8_at RSEGS M ((4 * (V 50%nat)) + 2147450881) 241)
  /\ (L5.u8_at RSEGS M ((4 * (V 50%nat)) + 2147450880) 241)
  /\ (L5.u8_at RSEGS M ((4 * (V 50%nat)) + 2147450887) 242)
  /\ (L5.u8_at RSEGS M ((4 * (V 50%nat)) + 2147450886) 242)
  /\ (L5.u8_at RSEGS M ((4 * (V 50%nat)) + 2147450885) 242)
  /\ (L5.u8_at RSEGS M ((4 * (V 50%nat)) + 2147450884) 0)
  /\ (L5.u64_at RSEGS M ((32 * (V 50%nat)) + 16) 716108)
  /\ (L5.u64_at RSEGS M ((32 * (V 50%nat)) + 8) 127274)
  /\ (L5.u64_at RSEGS M (32 * (V 50%nat)) 1102416563)
  /\ (L5.u64_at RSEGS M ((V 2%nat) - 136) (V 37%nat))
  /\ (L5.u64_at RSEGS M ((V 2%nat) - 88) (V 27%nat))
  /\ (L5.u64_at RSEGS M ((V 2%nat) - 80) (V 26%nat))
  /\ (L5.u64_at RSEGS M ((V 2%nat) - 72) (V 25%nat))
  /\ (L5.u64_at RSEGS M ((V 2%nat) - 64) (V 24%nat))
  /\ (L5.u64_at RSEGS M ((V 2%nat) - 56) (V 23%nat))
  /\ (L5.u64_at RSEGS M ((V 2%nat) - 48) (V 22%nat))
  /\ (L5.u64_at RSEGS M ((V 2%nat) - 40) (V 21%nat))
  /\ (L5.u64_at RSEGS M ((V 2%nat) - 32) (V 20%nat))
  /\ (L5.u64_at RSEGS M ((V 2%nat) - 24) (V 19%nat))
  /\ (L5.u64_at RSEGS M ((V 2%nat) - 16) (V 18%nat))
  /\ (L5.u64_at RSEGS M ((V 2%nat) - 8) (V 9%nat))
  /\ (L5.defined M ((32 * (V 50%nat)) + 24) 8)
  /\ (L5.defined M ((32 * (V 50%nat)) + 40) 88)
  /\ (L5.u64_at RSEGS M ((32 * (V 50%nat)) + 120) (V 51%nat)).

Lemma stM_of_RC V R M : srd_stM_R V R -> srd_stM_C V R M -> PGSRDMB16.srd_stM V R M.
Proof.
  intros HR HC. unfold srd_stM_R, srd_stM_C, PGSRDMB16.srd_stM in *.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  repeat split; assumption.
Qed.

Definition ms_g1_T (al : Z) : Prop :=
  forall (O : PGS.owner) (R0 : bvmap 5 word) (M0 : mem) (model0 : Model) (K : TSet) (OB LBX : list (Z * Z))
         (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (sp r : Z) (str : PM.vstr) (Wextra : list L5.range)
         (qc de rem g eg sst p k : Z),
    PGSRDK16.srd_ctx L ar HI al O R0 M0 model0 K OB LBX FF LK Aw cr sp r (PM.SRC qc de rem) str (PM.STRM g eg sst) Wextra ->
    getr R0 (reg 11) = Z_to_bv 64 p -> getr R0 (reg 12) = Z_to_bv 64 k ->
    forall (F fl : Z) (LK2 : list fframe) (M2 : mem) (model2 : Model),
    PGSRDK16.srd_frame L ar HI al R0 OB LBX FF LK Aw cr sp (PM.SRC qc de rem) F fl LK2 M2 model2 ->
    forall (fx : FPState) (R : bvmap 5 word) (M : mem) (model : Model) (LKc : list fframe) (Ac : list (Z * Z))
           (V : nat -> Z),
    PGSRDK16.srd_body L ar HI al O R0 M0 model0 OB LBX FF LK Aw sp (PM.SRC qc de rem) Wextra F M model LKc cr Ac ->
    V 2%nat = sp - al -> V 36%nat = PGS.ow_os O -> V 37%nat = p -> V 38%nat = k -> 32 * V 50%nat = F -> V 51%nat = fl ->
    (forall i, In i [1; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> V i = bv_unsigned (getr R0 (reg i))) ->
    getr R (reg 3) = getr R0 (reg 3) -> getr R (reg 4) = getr R0 (reg 4) ->
    V 34%nat = qc -> V 35%nat = de -> V 45%nat = PGS.ow_ois O ->
    PM.iss_at RSEGS PMA.AD PMSPA.accA M (PGS.ow_ois O) str (PM.STRM g eg sst) ->
    PGSRDK16.srd_stA V R (mrestrict (ahid Ac model) M) -> PGSRDK16.srd_pathG V R (mrestrict (ahid Ac model) M) rem sst ->
    forall (len1 : Z) (fx3 : FPState) (R3 : bvmap 5 word) (M3 : mem) (model3 : Model),
    len1 = Z.min k rem ->
    PGSRDK16.srd_body L ar HI al O R0 M0 model0 OB LBX FF LK Aw sp (PM.SRC qc de rem) Wextra F M3 model3 LKc cr Ac ->
    L5.defined M3 p len1 ->
    PGS.ow_at O M3 (PM.SRC qc de rem) OB -> PM.iss_at RSEGS PMA.AD PMSPA.accA M3 (PGS.ow_ois O) str (PM.STRM g eg sst) ->
    PMSTA.base_okA RSEGS PMA.AD M3 ->
    (forall i, 0 <= i < 2 ^ 64 ->
      (sp - 160 - al <= i < sp) \/ (F <= i < F + 120 /\ ~ (F + 24 <= i < F + 32)) \/ (F / 8 + SB <= i < F / 8 + SB + 16)
      \/ (PGS.ow_os O <= i < PGS.ow_os O + 296) \/ ((PGS.ow_os O + 8) / 8 + SB <= i < (PGS.ow_os O + 8) / 8 + SB + 36) ->
      ~ ((((V 2%nat) - 152) <= i < ((V 2%nat) - 152) + 16) \/ (((V 2%nat) - 112) <= i < ((V 2%nat) - 112) + 8) \/ (((32 * (V 50%nat)) + 0) <= i < ((32 * (V 50%nat)) + 0) + 24) \/ (((32 * (V 50%nat)) + 32) <= i < ((32 * (V 50%nat)) + 32) + 8) \/ (((4 * (V 50%nat)) + 2147450880) <= i < ((4 * (V 50%nat)) + 2147450880) + 12)) -> ~ (p <= i < p + len1) ->
      mrestrict (ahid Ac model3) M3 (Z_to_bv 64 i) = mrestrict (ahid Ac model) M (Z_to_bv 64 i)) ->
    getr R3 (reg 2) = Z_to_bv 64 ((V 2%nat) - 160) ->
    getr R3 (reg 8) = Z_to_bv 64 ((V 2%nat) + 16) ->
    getr R3 (reg 9) = Z_to_bv 64 ((V 2%nat) - 160) ->
    getr R3 (reg 18) = Z_to_bv 64 ((((V 36%nat) + 288) / 8) + 2147450880) ->
    getr R3 (reg 19) = Z_to_bv 64 (V 36%nat) ->
    getr R3 (reg 20) = Z_to_bv 64 len1 ->
    getr R3 (reg 21) = Z_to_bv 64 ((((V 36%nat) + 280) / 8) + 2147450880) ->
    getr R3 (reg 22) = Z_to_bv 64 (V 38%nat) ->
    getr R3 (reg 23) = Z_to_bv 64 ((V 36%nat) + 288) ->
    getr R3 (reg 24) = Z_to_bv 64 ((V 36%nat) + 280) ->
    getr R3 (reg 25) = Z_to_bv 64 ((4 * (V 50%nat)) + 2147450880) ->
    getr R3 (reg 26) = Z_to_bv 64 (32 * (V 50%nat)) ->
    (forall x, In x [3; 4; 27]%nat -> getr R3 (reg x) = getr R (reg x)) ->
    L5.u64_at RSEGS (mrestrict (ahid Ac model3) M3) ((V 2%nat) - 152) ((32 * (V 50%nat)) + 32) ->
    L5.u64_at RSEGS (mrestrict (ahid Ac model3) M3) ((V 2%nat) - 144) (32 * (V 50%nat)) ->
    L5.u64_at RSEGS (mrestrict (ahid Ac model3) M3) ((V 2%nat) - 112) (32 * (V 50%nat)) ->
    L5.u64_at RSEGS (mrestrict (ahid Ac model3) M3) ((32 * (V 50%nat)) + 32) (V 38%nat) ->
    L5.u8_at RSEGS (mrestrict (ahid Ac model3) M3) ((4 * (V 50%nat)) + 2147450891) 243 ->
    L5.u8_at RSEGS (mrestrict (ahid Ac model3) M3) ((4 * (V 50%nat)) + 2147450890) 243 ->
    L5.u8_at RSEGS (mrestrict (ahid Ac model3) M3) ((4 * (V 50%nat)) + 2147450889) 243 ->
    L5.u8_at RSEGS (mrestrict (ahid Ac model3) M3) ((4 * (V 50%nat)) + 2147450888) 248 ->
    L5.u8_at RSEGS (mrestrict (ahid Ac model3) M3) ((4 * (V 50%nat)) + 2147450883) 241 ->
    L5.u8_at RSEGS (mrestrict (ahid Ac model3) M3) ((4 * (V 50%nat)) + 2147450882) 241 ->
    L5.u8_at RSEGS (mrestrict (ahid Ac model3) M3) ((4 * (V 50%nat)) + 2147450881) 241 ->
    L5.u8_at RSEGS (mrestrict (ahid Ac model3) M3) ((4 * (V 50%nat)) + 2147450880) 241 ->
    L5.u8_at RSEGS (mrestrict (ahid Ac model3) M3) ((4 * (V 50%nat)) + 2147450887) 242 ->
    L5.u8_at RSEGS (mrestrict (ahid Ac model3) M3) ((4 * (V 50%nat)) + 2147450886) 242 ->
    L5.u8_at RSEGS (mrestrict (ahid Ac model3) M3) ((4 * (V 50%nat)) + 2147450885) 242 ->
    L5.u8_at RSEGS (mrestrict (ahid Ac model3) M3) ((4 * (V 50%nat)) + 2147450884) 0 ->
    L5.u64_at RSEGS (mrestrict (ahid Ac model3) M3) ((32 * (V 50%nat)) + 16) 716108 ->
    L5.u64_at RSEGS (mrestrict (ahid Ac model3) M3) ((32 * (V 50%nat)) + 8) 127274 ->
    L5.u64_at RSEGS (mrestrict (ahid Ac model3) M3) (32 * (V 50%nat)) 1102416563 ->
    L5.defined (mrestrict (ahid Ac model3) M3) ((32 * (V 50%nat)) + 24) 8 ->
    L5.defined (mrestrict (ahid Ac model3) M3) ((32 * (V 50%nat)) + 40) 88 ->
    srd_stM_R (vxMS V R3 len1) R3.

Definition ms_g2_T (al : Z) : Prop :=
  forall (O : PGS.owner) (R0 : bvmap 5 word) (M0 : mem) (model0 : Model) (K : TSet) (OB LBX : list (Z * Z))
         (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (sp r : Z) (str : PM.vstr) (Wextra : list L5.range)
         (qc de rem g eg sst p k : Z),
    PGSRDK16.srd_ctx L ar HI al O R0 M0 model0 K OB LBX FF LK Aw cr sp r (PM.SRC qc de rem) str (PM.STRM g eg sst) Wextra ->
    getr R0 (reg 11) = Z_to_bv 64 p -> getr R0 (reg 12) = Z_to_bv 64 k ->
    forall (F fl : Z) (LK2 : list fframe) (M2 : mem) (model2 : Model),
    PGSRDK16.srd_frame L ar HI al R0 OB LBX FF LK Aw cr sp (PM.SRC qc de rem) F fl LK2 M2 model2 ->
    forall (fx : FPState) (R : bvmap 5 word) (M : mem) (model : Model) (LKc : list fframe) (Ac : list (Z * Z))
           (V : nat -> Z),
    PGSRDK16.srd_body L ar HI al O R0 M0 model0 OB LBX FF LK Aw sp (PM.SRC qc de rem) Wextra F M model LKc cr Ac ->
    V 2%nat = sp - al -> V 36%nat = PGS.ow_os O -> V 37%nat = p -> V 38%nat = k -> 32 * V 50%nat = F -> V 51%nat = fl ->
    (forall i, In i [1; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> V i = bv_unsigned (getr R0 (reg i))) ->
    getr R (reg 3) = getr R0 (reg 3) -> getr R (reg 4) = getr R0 (reg 4) ->
    V 34%nat = qc -> V 35%nat = de -> V 45%nat = PGS.ow_ois O ->
    PM.iss_at RSEGS PMA.AD PMSPA.accA M (PGS.ow_ois O) str (PM.STRM g eg sst) ->
    PGSRDK16.srd_stA V R (mrestrict (ahid Ac model) M) -> PGSRDK16.srd_pathG V R (mrestrict (ahid Ac model) M) rem sst ->
    forall (len1 : Z) (fx3 : FPState) (R3 : bvmap 5 word) (M3 : mem) (model3 : Model),
    len1 = Z.min k rem ->
    PGSRDK16.srd_body L ar HI al O R0 M0 model0 OB LBX FF LK Aw sp (PM.SRC qc de rem) Wextra F M3 model3 LKc cr Ac ->
    L5.defined M3 p len1 ->
    PGS.ow_at O M3 (PM.SRC qc de rem) OB -> PM.iss_at RSEGS PMA.AD PMSPA.accA M3 (PGS.ow_ois O) str (PM.STRM g eg sst) ->
    PMSTA.base_okA RSEGS PMA.AD M3 ->
    (forall i, 0 <= i < 2 ^ 64 ->
      (sp - 160 - al <= i < sp) \/ (F <= i < F + 120 /\ ~ (F + 24 <= i < F + 32)) \/ (F / 8 + SB <= i < F / 8 + SB + 16)
      \/ (PGS.ow_os O <= i < PGS.ow_os O + 296) \/ ((PGS.ow_os O + 8) / 8 + SB <= i < (PGS.ow_os O + 8) / 8 + SB + 36) ->
      ~ ((((V 2%nat) - 152) <= i < ((V 2%nat) - 152) + 16) \/ (((V 2%nat) - 112) <= i < ((V 2%nat) - 112) + 8) \/ (((32 * (V 50%nat)) + 0) <= i < ((32 * (V 50%nat)) + 0) + 24) \/ (((32 * (V 50%nat)) + 32) <= i < ((32 * (V 50%nat)) + 32) + 8) \/ (((4 * (V 50%nat)) + 2147450880) <= i < ((4 * (V 50%nat)) + 2147450880) + 12)) -> ~ (p <= i < p + len1) ->
      mrestrict (ahid Ac model3) M3 (Z_to_bv 64 i) = mrestrict (ahid Ac model) M (Z_to_bv 64 i)) ->
    getr R3 (reg 2) = Z_to_bv 64 ((V 2%nat) - 160) ->
    getr R3 (reg 8) = Z_to_bv 64 ((V 2%nat) + 16) ->
    getr R3 (reg 9) = Z_to_bv 64 ((V 2%nat) - 160) ->
    getr R3 (reg 18) = Z_to_bv 64 ((((V 36%nat) + 288) / 8) + 2147450880) ->
    getr R3 (reg 19) = Z_to_bv 64 (V 36%nat) ->
    getr R3 (reg 20) = Z_to_bv 64 len1 ->
    getr R3 (reg 21) = Z_to_bv 64 ((((V 36%nat) + 280) / 8) + 2147450880) ->
    getr R3 (reg 22) = Z_to_bv 64 (V 38%nat) ->
    getr R3 (reg 23) = Z_to_bv 64 ((V 36%nat) + 288) ->
    getr R3 (reg 24) = Z_to_bv 64 ((V 36%nat) + 280) ->
    getr R3 (reg 25) = Z_to_bv 64 ((4 * (V 50%nat)) + 2147450880) ->
    getr R3 (reg 26) = Z_to_bv 64 (32 * (V 50%nat)) ->
    (forall x, In x [3; 4; 27]%nat -> getr R3 (reg x) = getr R (reg x)) ->
    L5.u64_at RSEGS (mrestrict (ahid Ac model3) M3) ((V 2%nat) - 152) ((32 * (V 50%nat)) + 32) ->
    L5.u64_at RSEGS (mrestrict (ahid Ac model3) M3) ((V 2%nat) - 144) (32 * (V 50%nat)) ->
    L5.u64_at RSEGS (mrestrict (ahid Ac model3) M3) ((V 2%nat) - 112) (32 * (V 50%nat)) ->
    L5.u64_at RSEGS (mrestrict (ahid Ac model3) M3) ((32 * (V 50%nat)) + 32) (V 38%nat) ->
    L5.u8_at RSEGS (mrestrict (ahid Ac model3) M3) ((4 * (V 50%nat)) + 2147450891) 243 ->
    L5.u8_at RSEGS (mrestrict (ahid Ac model3) M3) ((4 * (V 50%nat)) + 2147450890) 243 ->
    L5.u8_at RSEGS (mrestrict (ahid Ac model3) M3) ((4 * (V 50%nat)) + 2147450889) 243 ->
    L5.u8_at RSEGS (mrestrict (ahid Ac model3) M3) ((4 * (V 50%nat)) + 2147450888) 248 ->
    L5.u8_at RSEGS (mrestrict (ahid Ac model3) M3) ((4 * (V 50%nat)) + 2147450883) 241 ->
    L5.u8_at RSEGS (mrestrict (ahid Ac model3) M3) ((4 * (V 50%nat)) + 2147450882) 241 ->
    L5.u8_at RSEGS (mrestrict (ahid Ac model3) M3) ((4 * (V 50%nat)) + 2147450881) 241 ->
    L5.u8_at RSEGS (mrestrict (ahid Ac model3) M3) ((4 * (V 50%nat)) + 2147450880) 241 ->
    L5.u8_at RSEGS (mrestrict (ahid Ac model3) M3) ((4 * (V 50%nat)) + 2147450887) 242 ->
    L5.u8_at RSEGS (mrestrict (ahid Ac model3) M3) ((4 * (V 50%nat)) + 2147450886) 242 ->
    L5.u8_at RSEGS (mrestrict (ahid Ac model3) M3) ((4 * (V 50%nat)) + 2147450885) 242 ->
    L5.u8_at RSEGS (mrestrict (ahid Ac model3) M3) ((4 * (V 50%nat)) + 2147450884) 0 ->
    L5.u64_at RSEGS (mrestrict (ahid Ac model3) M3) ((32 * (V 50%nat)) + 16) 716108 ->
    L5.u64_at RSEGS (mrestrict (ahid Ac model3) M3) ((32 * (V 50%nat)) + 8) 127274 ->
    L5.u64_at RSEGS (mrestrict (ahid Ac model3) M3) (32 * (V 50%nat)) 1102416563 ->
    L5.defined (mrestrict (ahid Ac model3) M3) ((32 * (V 50%nat)) + 24) 8 ->
    L5.defined (mrestrict (ahid Ac model3) M3) ((32 * (V 50%nat)) + 40) 88 ->
    srd_stM_C (vxMS V R3 len1) R3 (mrestrict (ahid Ac model3) M3).

End WithHeap.

Lemma vxMS_low V R len1 i : i <> 39%nat -> (i < 61)%nat -> vxMS V R len1 i = V i.
Proof.
  intros N1 N2. unfold vxMS, PGSRDMB16.vxC.
  do 61 (destruct i as [|i]; [first [reflexivity | exfalso; apply N1; reflexivity]|]). exfalso. clear - N2. lia.
Qed.

Section Post.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Variable IL : icpt_layout.
Hypothesis ICok : aicpt_ok L ar IL SCFG HI.
Hypothesis ILY : as0_icpt_layout IL.

Lemma srd_mc_post_ok : PGSRDK16.srd_exit_T L ar HI 16 -> PGSRDK16.srd_fill_ret_T L ar HI 16 -> PGSA.fill_buffer_specG RSEGS PMA.AD L ar HI PNRA.FCB ->
  ms_g1_T L ar HI 16 -> ms_g2_T L ar HI 16 -> srd_mc_post_T L ar HI 16.
Proof.
  intros EXIT FR FB G1 G2. unfold srd_mc_post_T.
  intros O R0 M0 model0 K OB LBX FF LK Aw cr sp r str Wextra qc de rem g eg sst p k CTX R11 R12 F fl LK2 M2 model2 G
         fx R M model LKc Ac V BD XV2 XV36 XV37 XV38 XV50 XV51 XVS XR3 XR4 XV34 XV35 XV45 XIS STA PTH
         len1 fx3 R3 M3 model3 HL BD3 DEF3 OW3 IS3 BASE3 AG3 Q2 Q8 Q9 Q18 Q19 Q20 Q21 Q22 Q23 Q24 Q25 Q26 Q3427
         C152 C144 C112 CF32 S0 S1 S2 S3 S4 S5 S6 S7 S8 S9 S10 S11 CF16 CF8 CF0 DF24 DF40.
  pose proof (G1 O R0 M0 model0 K OB LBX FF LK Aw cr sp r str Wextra qc de rem g eg sst p k CTX R11 R12 F fl LK2 M2 model2 G
         fx R M model LKc Ac V BD XV2 XV36 XV37 XV38 XV50 XV51 XVS XR3 XR4 XV34 XV35 XV45 XIS STA PTH
         len1 fx3 R3 M3 model3 HL BD3 DEF3 OW3 IS3 BASE3 AG3 Q2 Q8 Q9 Q18 Q19 Q20 Q21 Q22 Q23 Q24 Q25 Q26 Q3427
         C152 C144 C112 CF32 S0 S1 S2 S3 S4 S5 S6 S7 S8 S9 S10 S11 CF16 CF8 CF0 DF24 DF40) as SR.
  pose proof (G2 O R0 M0 model0 K OB LBX FF LK Aw cr sp r str Wextra qc de rem g eg sst p k CTX R11 R12 F fl LK2 M2 model2 G
         fx R M model LKc Ac V BD XV2 XV36 XV37 XV38 XV50 XV51 XVS XR3 XR4 XV34 XV35 XV45 XIS STA PTH
         len1 fx3 R3 M3 model3 HL BD3 DEF3 OW3 IS3 BASE3 AG3 Q2 Q8 Q9 Q18 Q19 Q20 Q21 Q22 Q23 Q24 Q25 Q26 Q3427
         C152 C144 C112 CF32 S0 S1 S2 S3 S4 S5 S6 S7 S8 S9 S10 S11 CF16 CF8 CF0 DF24 DF40) as SC.
  pose proof (stM_of_RC _ _ _ SR SC) as STM. clear SR SC G1 G2.
  pose proof PTH as (V33 & REM1 & _).
  assert (R38 : 0 <= V 38%nat < 2 ^ 64).
  { pose proof STA as X. unfold PGSRDK16.srd_stA in X.
    repeat match type of X with _ /\ _ => let H := fresh "SA" in destruct X as (H & X) end. first [assumption | split; assumption]. }
  pose proof CTX as (OK & HH & AM & K0 & ENT & FRM & FRS & OFR & A10 & SP32 & ARGS & WX & PA0 & IA0 & BASE0 & INCS & KONT).
  destruct ENT as (Rra & RAok & Rsp & Rgp & Rtp & ASTK & STKSH).
  destruct ARGS as (p' & k' & A11 & A12 & Hk & _). rewrite L5SAR.r12 in A12. unfold PM.CHUNK in Hk.
  pose proof R12 as R12k. rewrite A12 in R12k. apply (f_equal bv_unsigned) in R12k.
  rewrite !L5.unsigned_lit in R12k by (first [clear - Hk; lia | rewrite <- XV38; exact R38]). subst k'.
  pose proof (PGSA.oo_lay _ _ _ _ _ _ OK) as (LY1 & LY2 & LY3 & LY4 & LY5 & O8 & I8 & LY6 & LYD).
  pose proof (PGSA.oo_src _ _ _ _ _ _ OK M0 _ OB PA0) as (PSRC & PNI & SDEF0).
  pose proof PSRC as (_ & _ & _ & _ & _ & _ & _ & QD1 & QD2 & QD3 & _). cbn [PM.sr_qc PM.sr_de PM.sr_rem] in QD1, QD2, QD3.
  try unfold PM.CHUNK in QD1, QD2, QD3.
  assert (AO : PMSPA.aobjA FF (PGS.ow_os O) 296) by (apply (PGSKA.aobjA_sub FF (PGS.ow_lo O) (PGS.ow_hi O)); [exact OFR| exact LY1| exact LY2]).
  pose proof (PGSKA.src_visG L ar C HI LY HIok _ FF LK cr Aw M0 model0 (PGS.ow_os O) _ _ _ sp (PMSPA.pm_scr 4) HH AO O8 PSRC PNI ASTK) as ((O1 & _ & OBIG) & _).
  pose proof (PGSA.oo_src _ _ _ _ _ _ OK M3 _ OB OW3) as (PSRC3 & _ & _).
  pose proof PSRC3 as (_ & _ & _ & _ & _ & _ & S288 & _). cbn [PM.sr_rem] in S288.
  assert (RB : rem <= 16384) by (clear - QD1 QD2 QD3; lia).
  assert (Hl1 : 1 <= len1 <= k) by (rewrite HL; clear - REM1 Hk; lia).
  set (V' := vxMS V R3 len1) in *.
  assert (XV2' : V' 2%nat = sp - 16) by (unfold V'; rewrite vxMS_low by (clear; lia); exact XV2).
  assert (XV36' : V' 36%nat = PGS.ow_os O) by (unfold V'; rewrite vxMS_low by (clear; lia); exact XV36).
  assert (XV37' : V' 37%nat = p) by (unfold V'; rewrite vxMS_low by (clear; lia); exact XV37).
  assert (XV38' : V' 38%nat = k) by (unfold V'; rewrite vxMS_low by (clear; lia); exact XV38).
  assert (XV50' : 32 * V' 50%nat = F) by (unfold V'; rewrite vxMS_low by (clear; lia); exact XV50).
  assert (XV51' : V' 51%nat = fl) by (unfold V'; rewrite vxMS_low by (clear; lia); exact XV51).
  assert (XVS' : forall i, In i [1; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> V' i = bv_unsigned (getr R0 (reg i))).
  { intros i Hi. unfold V'. rewrite vxMS_low; [exact (XVS i Hi)| |]; cbn in Hi; repeat destruct Hi as [<-|Hi]; first [destruct Hi | clear; lia]. }
  assert (XR3' : getr R3 (reg 3) = getr R0 (reg 3)) by (rewrite (Q3427 3%nat) by (cbn; tauto); exact XR3).
  assert (XR4' : getr R3 (reg 4) = getr R0 (reg 4)) by (rewrite (Q3427 4%nat) by (cbn; tauto); exact XR4).
  assert (XV39' : V' 39%nat = len1) by reflexivity.
  assert (XV34' : V' 34%nat = qc) by (unfold V'; rewrite vxMS_low by (clear; lia); exact XV34).
  assert (XV35' : V' 35%nat = de) by (unfold V'; rewrite vxMS_low by (clear; lia); exact XV35).
  assert (XV45' : V' 45%nat = PGS.ow_ois O) by (unfold V'; rewrite vxMS_low by (clear; lia); exact XV45).
  assert (XV33' : V' 33%nat = rem) by (unfold V'; rewrite vxMS_low by (clear; lia); exact V33).
  assert (AV : L5A.avis (ahid Ac model3) (PGS.ow_os O + 288) 8).
  { intros i Hi. apply (PGSRDC16.srd_vis L ar C HI LY HIok O R0 M0 model0 K OB LBX FF LK Aw cr sp r (PM.SRC qc de rem) str (PM.STRM g eg sst) Wextra F fl LK2 M2 model2 M3 model3 LKc Ac _ CTX G BD3).
    right; right; right; left. clear - Hi. lia. }
  assert (U288 : L5.u64_at RSEGS (mrestrict (ahid Ac model3) M3) (V' 36%nat + 288) (V' 33%nat)).
  { rewrite XV36', XV33'. apply (proj2 (L5A.u64_at_vis (ahid Ac model3) M3 (PGS.ow_os O + 288) rem AV ltac:(clear - O1; lia) ltac:(clear - O1; lia))). exact S288. }
  clearbody V'.
  destruct (Z.eq_dec len1 k) as [Ek|Nk].
  - (* Beq *)
    apply (PGSRDMQ16.srd_beq_ok L ar C HI LY HIok IL ICok ILY EXIT O R0 M0 model0 K OB LBX FF LK Aw cr sp r str Wextra qc de rem g eg sst p k CTX R11 R12
             F fl LK2 M2 model2 G fx3 R3 M3 model3 LKc Ac V' BD3 XV2' XV36' XV37' XV38' XV50' XV51' XVS' XR3' XR4' len1 STM).
    + unfold PGSRDMQ16.srd_beqX. rewrite XV33', XV39'.
      split; [clear - REM1 RB; lia|]. split; [rewrite Ek, <- XV38; exact Q22|].
      split; [rewrite <- XV33'; exact U288|]. split; [clear - REM1 RB; lia|]. split; [clear - Hl1 Hk; lia|]. clear - HL Ek REM1 RB Hk. lia.
    + exact XV39'. + exact XV33'. + exact XV34'. + exact XV35'. + exact XV45'.
    + exact OW3. + exact IS3. + exact BASE3. + exact Ek. + clear - HL. lia. + exact DEF3.
  - (* Bne *)
    assert (Er : len1 = rem) by (clear - HL Nk; lia).
    apply (PGSRDMBB16.srd_bne_ok L ar C HI LY HIok IL ICok ILY FB FR O R0 M0 model0 K OB LBX FF LK Aw cr sp r str Wextra qc de rem g eg sst p k CTX R11 R12
             F fl LK2 M2 model2 G fx3 R3 M3 model3 LKc Ac V' BD3 XV2' XV36' XV37' XV38' XV50' XV51' XVS' XR3' XR4' len1 STM).
    + unfold PGSRDMB16.srd_bneX. rewrite XV38', XV39'. split; [rewrite <- XV38; exact Q22|].
      split; [rewrite Er, <- XV33'; exact U288|]. split; [clear - HL Nk Hk REM1; lia|]. split; [clear - HL Nk Hk REM1; lia|]. clear - HL Nk Hk REM1. lia.
    + exact XV39'. + exact XV34'. + exact XV35'. + exact XV45'.
    + exact OW3. + exact IS3. + exact BASE3. + exact Er. + clear - HL Nk Hk REM1. lia. + unfold PM.CHUNK. clear - HL Nk Hk REM1. lia. + exact DEF3.
Qed.
End Post.
End PGSRDMS16.
