(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnASrcKit_b PgSrcKitA_b PnASrcRead1_b PnASrcReadK_b PnASrcReadP_b Ba0PgSrcReadK16_b Ba0PgSrcReadC16_b.
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

Module PGSRDMB16.
Abbreviation RSEGS := PGSRDK16.RSEGS.
Abbreviation mem := (word -> option byte).
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).

Section WithHeap.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).

Definition srd_stM (V : nat -> Z) (R : bvmap 5 word) (M : mem) : Prop :=
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
  /\ (L5.img_clear M 65536 1282048)
  /\ (L5.u64_at RSEGS M 1309752 2147450880)
  /\ (L5.u32_at RSEGS M 1309760 1)
  /\ (140735332487232 <= (V 2%nat) <= 140737488355312)
  /\ ((V 2%nat) mod 32 = 0)
  /\ (L5.writable RSEGS M ((V 2%nat) - 160) 176)
  /\ (6905856 <= (V 36%nat) <= 140737488355032)
  /\ ((V 36%nat) mod 8 = 0)
  /\ (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 296 <= 2147446784)
  /\ (L5KA.zeros_at M ((((V 36%nat) + 8) / 8) + 2147450880) 36)
  /\ (L5.writable RSEGS M (V 36%nat) 296)
  /\ (((V 2%nat) - 160) + 176 <= (V 36%nat) \/ (V 36%nat) + 296 <= ((V 2%nat) - 160))
  /\ (L5.u64_at RSEGS M ((V 36%nat) + 264) (V 34%nat))
  /\ (L5.u64_at RSEGS M ((V 36%nat) + 272) 16384)
  /\ (L5.u64_at RSEGS M ((V 36%nat) + 280) (V 35%nat))
  /\ (L5.defined M ((V 36%nat) + 256) 8)
  /\ (140735332487248 <= (V 2%nat) <= 140737488355328)
  /\ (L5.writable RSEGS M ((V 2%nat) - 160) 160)
  /\ (((V 2%nat) - 160) + 160 <= (V 36%nat) \/ (V 36%nat) + 296 <= ((V 2%nat) - 160))
  /\ (4096 <= (V 35%nat) <= 140737488338944)
  /\ (L5.u64_at RSEGS M (V 2%nat) (V 8%nat))
  /\ (L5.u64_at RSEGS M ((V 2%nat) + 8) (V 1%nat))
  /\ (215808 <= (V 50%nat) <= 4398046511102)
  /\ ((V 50%nat) mod 4 = 0)
  /\ (L5.defined M (32 * (V 50%nat)) 128)
  /\ (L5.writable RSEGS M (32 * (V 50%nat)) 128)
  /\ (2147446784 + 17592186048512 <= (32 * (V 50%nat)) \/ (32 * (V 50%nat)) + 128 <= 2147446784)
  /\ (L5.writable RSEGS M ((4 * (V 50%nat)) + 2147450880) 16)
  /\ (4096 <= (V 51%nat) <= 140737488355327)
  /\ (L5.writable RSEGS M (V 51%nat) 1)
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
  /\ ((V 51%nat) + 1 <= ((((V 36%nat) + 8) / 8) + 2147450880) \/ ((((V 36%nat) + 8) / 8) + 2147450880) + 36 <= (V 51%nat))
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

Definition srd_bneX (V : nat -> Z) (R : bvmap 5 word) (M : mem) : Prop :=
  (getr R (reg 22) = Z_to_bv 64 (V 38%nat))
  /\ (L5.u64_at RSEGS M ((V 36%nat) + 288) (V 39%nat))
  /\ (1 <= (V 39%nat) <= 16383)
  /\ (2 <= (V 38%nat) <= 16384)
  /\ (1 <= ((V 38%nat) - (V 39%nat)) <= 16383).

Definition srd_bne_T (al : Z) : Prop :=
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
    forall (len1 : Z),
    srd_stM V R (mrestrict (ahid Ac model) M) -> srd_bneX V R (mrestrict (ahid Ac model) M) ->
    V 39%nat = len1 -> V 34%nat = qc -> V 35%nat = de -> V 45%nat = PGS.ow_ois O ->
    PGS.ow_at O M (PM.SRC qc de rem) OB -> PM.iss_at RSEGS PMA.AD PMSPA.accA M (PGS.ow_ois O) str (PM.STRM g eg sst) ->
    PMSTA.base_okA RSEGS PMA.AD M -> len1 = rem -> len1 < k -> k - len1 <= PM.CHUNK -> L5.defined M p len1 ->
    srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx R 0xaeed4 M model) K.

Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Variable IL : icpt_layout.
Hypothesis ICok : aicpt_ok L ar IL SCFG HI.
Hypothesis ILY : as0_icpt_layout IL.
Let LYa := PMA.ly_as0 L C LY.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Ltac pdestr PP := repeat match type of PP with _ /\ _ => let H := fresh "S" in destruct PP as (H & PP) end.

Definition vxC (V : nat -> Z) (R : bvmap 5 word) : nat -> Z := fun i =>
  match i with
  | 61%nat => bv_unsigned (getr R (reg 1)) | 62%nat => bv_unsigned (getr R (reg 5)) | 63%nat => bv_unsigned (getr R (reg 6))
  | 64%nat => bv_unsigned (getr R (reg 7)) | 65%nat => bv_unsigned (getr R (reg 12)) | 66%nat => bv_unsigned (getr R (reg 13))
  | 67%nat => bv_unsigned (getr R (reg 14)) | 68%nat => bv_unsigned (getr R (reg 15)) | 69%nat => bv_unsigned (getr R (reg 16))
  | 70%nat => bv_unsigned (getr R (reg 17)) | 71%nat => bv_unsigned (getr R (reg 28)) | 72%nat => bv_unsigned (getr R (reg 29))
  | 73%nat => bv_unsigned (getr R (reg 30)) | 74%nat => bv_unsigned (getr R (reg 31))
  | _ => V i
  end.

Lemma srd_fill_ag O R0 M0 model0 K OB LBX FF LK Aw cr sp r src str sm Wextra F fl LK2 M2 model2 M3 model3 LK3 Ac3 M4 model4 LK4 Ac4 srcf i :
  PGSRDK16.srd_ctx L ar HI 16 O R0 M0 model0 K OB LBX FF LK Aw cr sp r src str sm Wextra ->
  PGSRDK16.srd_frame L ar HI 16 R0 OB LBX FF LK Aw cr sp src F fl LK2 M2 model2 ->
  PGSRDK16.srd_body L ar HI 16 O R0 M0 model0 OB LBX FF LK Aw sp src Wextra F M3 model3 LK3 cr Ac3 ->
  PGSRDK16.srd_body L ar HI 16 O R0 M0 model0 OB LBX FF LK Aw sp src Wextra F M4 model4 LK4 cr Ac4 ->
  L5CA.ahpres L ar (PM.src_own srcf ++ OB ++ LBX) ((F, 1, sp - 160 - 16 + 32) :: FF) (sp - 160 - 16) (PMSPA.pm_scr 3) (PGS.W_srcG (PGS.ow_os O) (PGS.ow_ois O) srcf ++ []) M3 M4 ->
  0 <= i < 2 ^ 64 ->
  (sp - 160 - 16 <= i < sp) \/ (F <= i < F + 120 /\ ~ (F + 24 <= i < F + 32)) \/ (F / 8 + SB <= i < F / 8 + SB + 16)
    \/ (PGS.ow_os O <= i < PGS.ow_os O + 296) \/ ((PGS.ow_os O + 8) / 8 + SB <= i < (PGS.ow_os O + 8) / 8 + SB + 36) ->
  L5.outside (PGS.W_srcG (PGS.ow_os O) (PGS.ow_ois O) srcf ++ []) i ->
  mrestrict (ahid Ac4 model4) M4 (Z_to_bv 64 i) = mrestrict (ahid Ac3 model3) M3 (Z_to_bv 64 i).
Proof.
  intros CTX G BI3 BI4 AH Hi RG OUT.
  assert (RG' : (sp - 160 - 16 <= i < sp) \/ (F <= i < F + 128) \/ (F / 8 + SB <= i < F / 8 + SB + 16)
    \/ (PGS.ow_os O <= i < PGS.ow_os O + 296) \/ ((PGS.ow_os O + 8) / 8 + SB <= i < (PGS.ow_os O + 8) / 8 + SB + 36)) by (clear - RG; lia).
  apply PGSRDC16.mr_eq; [exact (PGSRDC16.srd_vis L ar C HI LY HIok O R0 M0 model0 K OB LBX FF LK Aw cr sp r src str sm Wextra F fl LK2 M2 model2 M3 model3 LK3 Ac3 i CTX G BI3 RG')|
                exact (PGSRDC16.srd_vis L ar C HI LY HIok O R0 M0 model0 K OB LBX FF LK Aw cr sp r src str sm Wextra F fl LK2 M2 model2 M4 model4 LK4 Ac4 i CTX G BI4 RG')|].
  pose proof CTX as (OK & HH0 & _ & _ & _ & _ & _ & OFR & _).
  pose proof (PGSA.oo_lay _ _ _ _ _ _ OK) as (LY1 & LY2 & _ & _ & _ & O8 & _).
  assert (AO : PMSPA.aobjA FF (PGS.ow_os O) 296).
  { apply (PGSKA.aobjA_sub FF (PGS.ow_lo O) (PGS.ow_hi O)); [exact OFR| exact LY1| exact LY2]. }
  unfold PGSRDK16.srd_frame in G.
  pose proof G as G'. destruct G' as [_ GSPT GSLO GSHI GSPC GOCR GOWN GFS1 GFS2 GFCEIL GLKI2 GFLP GFLNC GHH2 GFLC GFR GF8 GFBIG GF32 GFLA GFLR GFLBIG GNCF GNCS].
  change (ff_bytes 1) with 128 in *. change (128 / 8) with 16 in *.
  destruct AH as (AK & _). apply AK. split; [exact Hi|]. split.
  2:{ exact OUT. }
  unfold aclient. set (os := PGS.ow_os O) in *.
  destruct RG as [Y|[Y|[Y|[Y|Y]]]].
  - apply (L5SAR.stack_client L ar). clear - Y GSLO GSPC. lia. clear - Y. lia.
  - apply (L5SAR.fframe_client L ar _ _ _ _ F 1 (sp - 160 - 16 + 32)); [left; reflexivity|]. change (ff_bytes 1) with 128. clear - Y. lia.
  - apply (L5SAR.fframe_shadow_client L ar _ _ _ _ F 1 (sp - 160 - 16 + 32)); [left; reflexivity|].
    change (ff_bytes 1) with 128. unfold in_shadow_of, S. destruct GF8 as (_ & GF8b & _). rewrite GF8b. clear - Y. lia.
  - apply L5SAR.aclient_cons. apply PMASR1.cl_of_bf. right. apply (PMASR1.in_fframe_of_aobjA FF _ 296 i AO). clear - Y. lia.
  - apply L5SAR.aclient_cons. destruct AO as ([[fa fk] frs] & Hf & X1 & X2). cbn [ff_addr ff_class fst snd] in X1, X2.
    apply (L5SAR.fframe_shadow_client L ar _ _ _ _ fa fk frs); [exact Hf|]. unfold in_shadow_of, S. clear - Y X1 X2 O8. lia.
Qed.

Lemma srd_fill_call : PGSA.fill_buffer_specG RSEGS PMA.AD L ar HI PNRA.FCB -> PGSRDK16.srd_fill_ret_T L ar HI 16 ->
  forall (O : PGS.owner) (R0 : bvmap 5 word) (M0 : mem) (model0 : Model) (K : TSet) (OB LBX : list (Z * Z))
         (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (sp r : Z) (str : PM.vstr) (Wextra : list L5.range)
         (qc de rem g eg sst p k : Z),
    PGSRDK16.srd_ctx L ar HI 16 O R0 M0 model0 K OB LBX FF LK Aw cr sp r (PM.SRC qc de rem) str (PM.STRM g eg sst) Wextra ->
    getr R0 (reg 11) = Z_to_bv 64 p -> getr R0 (reg 12) = Z_to_bv 64 k ->
    forall (F fl : Z) (LK2 : list fframe) (M2 : mem) (model2 : Model),
    PGSRDK16.srd_frame L ar HI 16 R0 OB LBX FF LK Aw cr sp (PM.SRC qc de rem) F fl LK2 M2 model2 ->
    forall (fx : FPState) (R : bvmap 5 word) (M : mem) (model : Model) (LKc : list fframe) (Ac : list (Z * Z))
           (V : nat -> Z),
    PGSRDK16.srd_body L ar HI 16 O R0 M0 model0 OB LBX FF LK Aw sp (PM.SRC qc de rem) Wextra F M model LKc cr Ac ->
    V 2%nat = sp - 16 -> V 36%nat = PGS.ow_os O -> V 37%nat = p -> V 38%nat = k -> 32 * V 50%nat = F -> V 51%nat = fl ->
    (forall i, In i [1; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> V i = bv_unsigned (getr R0 (reg i))) ->
    getr R (reg 3) = getr R0 (reg 3) -> getr R (reg 4) = getr R0 (reg 4) ->
    forall (len1 : Z),
    PGSRDK16.srd_stC V R (mrestrict (ahid Ac model) M) -> V 39%nat = len1 -> V 34%nat = qc -> V 61%nat = 716700 -> V 65%nat = PM.CHUNK ->
    getr R (reg 10) = Z_to_bv 64 (PGS.ow_os O) -> getr R (reg 11) = Z_to_bv 64 qc ->
    PGS.ow_at O M (PM.SRC qc qc 0) OB -> PM.iss_at RSEGS PMA.AD PMSPA.accA M (PGS.ow_ois O) str (PM.STRM g eg sst) -> PMSTA.base_okA RSEGS PMA.AD M ->
    len1 = rem -> len1 < k -> k - len1 <= 16383 -> L5.defined M p len1 ->
    srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx R 731640 M model) K.
Proof.
  intros FB FRT.
  intros O R M model K OB LBX FF LK Aw cr sp r str Wextra qc de rem g eg sst pb kb CTX R11 R12
         F fl LK2 M2 model2 G fxc Rc Mc modelc LKc Ac V BD XV2 XV36 XV37 XV38 XV50 XV51 XVS XR3 XR4
         len1 ST XV39 XV34 XV61 XV65 XC10 XC11 XPA XIA XBASE XL1 XL2 XL3 XDP.
  pose proof CTX as CTX0.
  destruct CTX as (OK & HH & AM & K0 & ENT & FRM & FRS & OFR & A10 & S32 & ARGS & WX & PA & IA & BASE & INCS & KONT).
  set (src := PM.SRC qc de rem) in *. set (sm := PM.STRM g eg sst) in *.
  destruct ENT as (Rra & RAok & Rsp & Rgp & Rtp & ASTK & STKSH).
  destruct ARGS as (p & k & A11 & A12 & Hk & DST). destruct WX as (p' & k' & A11' & A12' & Hp' & Hk' & ->).
  rewrite L5K.rl1 in Rra. rewrite L5K.rl2 in Rsp. rewrite L5K.rl3 in Rgp. rewrite L5K.rl4 in Rtp. rewrite L5K.rl10 in A10.
  rewrite L5SAR.r11 in A11, A11'. rewrite L5SAR.r12 in A12, A12'. unfold PM.CHUNK in Hk.
  change (PMSPA.pm_scr 4) with 20480 in *. pose proof RAok as (Hr1 & Hr2).
  pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP).
  pose proof (PGSA.oo_lay _ _ _ _ _ _ OK) as (LY1 & LY2 & LY3 & LY4 & LY5 & O8 & I8 & LY6 & LYD).
  pose proof (PGSA.oo_src _ _ _ _ _ _ OK M src OB PA) as (PSRC & PNI & SDEF0).
  set (os := PGS.ow_os O) in *. set (ois := PGS.ow_ois O) in *. set (lo := PGS.ow_lo O) in *. set (hi := PGS.ow_hi O) in *.
  set (LB := PM.src_own src ++ OB ++ LBX) in *.
  assert (AO : PMSPA.aobjA FF os 296) by (apply (PGSKA.aobjA_sub FF lo hi); [exact OFR| exact LY1| exact LY2]).
  assert (AOI : PMSPA.aobjA FF ois 272) by (apply (PGSKA.aobjA_sub FF lo hi); [exact OFR| exact LY3| exact LY4]).
  pose proof (PGSKA.src_visG L ar C HI LY HIok LB FF LK cr Aw M model os _ _ src sp 20480 HH AO O8 PSRC PNI ASTK)
    as ((O1 & _ & OBIG) & OZ & OW & OCE & OAV & _ & OFS1 & OFS2).
  pose proof (PGSKA.iss_visG L ar C HI LY HIok LB FF LK cr Aw M model ois str sm sp 20480 HH AOI I8 IA ASTK)
    as ((I1 & _ & IBIG) & IZ & IW & ICE & IAV & _).
  pose proof (PMASK.mach_vis L ar C HI LY HIok LB FF LK cr Aw M model HH BASE) as (V0 & V1 & V2).
  pose proof (PMASK.stk_vis L ar C HI LY HIok LB FF LK cr Aw M model sp 20480 80 HH ASTK ltac:(lia)) as (SL80 & SH80 & V3).
  pose proof (PMASK.img_shz_vis L ar C HI LY IL ICok ILY LB FF LK cr Aw M model 0x132c30 1 HH ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(lia) ltac:(lia)) as VT1.
  pose proof (PMASK.img_shz_vis L ar C HI LY IL ICok ILY LB FF LK cr Aw M model 0x132b98 1 HH ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(lia) ltac:(lia)) as VT2.
  cbn in VT1, VT2.
  pose proof (PMASK.frb_of L ar C HI HIok _ _ _ _ _ _ _ HH) as FRB. pose proof (PMASK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HH) as BRB.
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & _ & _ & _ & _ & _ & TOP & _).
  pose proof (PMASK.fs_above_img L ar C HI LY HIok _ _ _ _ _ _ _ HH) as FSI.
  pose proof OFR as (ff & Hff & FLO & FHI). destruct (WF _ Hff) as (FB1 & FB2 & _).
  unfold src, sm in *. clear src sm.
  cbn [PM.sr_qc PM.sr_de PM.sr_rem PM.sm_g PM.sm_eg PM.sm_st] in *.
  pose proof PSRC as PSRC0.
  destruct PSRC as (S240 & S248 & SD256 & S264 & S272 & S280 & S288 & G1 & G2 & G3 & G16 & DCH & ACH & ACC240).
  cbn [PM.sr_qc PM.sr_de PM.sr_rem] in *. unfold PM.CHUNK in *.
  pose proof IA as (H0i & _ & _ & H16i & _ & _ & _ & _ & _ & _ & _ & _ & IOSB & _ & _).
  destruct IOSB as (I0 & I32 & I36 & I40 & _ & _ & _ & _ & IST).
  cbn [PM.sm_g PM.sm_eg PM.sm_st pa_vp_iss pa_vp_strbuf pa_vp_iss_ios PMA.AD ADDR_A] in *.
  replace (ois + 120 + 32) with (ois + 152) in I32 by lia. replace (ois + 120 + 36) with (ois + 156) in I36 by lia.
  replace (ois + 120 + 40) with (ois + 160) in I40 by lia.
  assert (SOWN : incl (PM.vs_own str) LB) by (unfold LB; intros x Hx; apply in_or_app; right; apply in_or_app; right; exact (INCS x Hx)).
  assert (QIN : In (qc, 16384) LB) by (unfold LB, PM.src_own; cbn; left; reflexivity).
  assert (OBIN : forall B m, In (B, m) OB -> In (B, m) LB) by (intros B m Hin; unfold LB, PM.src_own; cbn; right; apply in_or_app; left; exact Hin).
  assert (ND : NoDup (map fst LB)) by exact (PMASK.lb_nodup L ar C HI HIok _ _ _ _ _ _ _ HH).
  destruct (WB _ QIN) as ((Q0 & QI & Q16 & _ & Q4 & QAPP) & _). cbn [fst snd] in Q0, QI, Q16, Q4, QAPP.
  rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa) in QI.
  unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI in QAPP, FSAPP.
  set (MV := mrestrict (ahid Aw model) M) in *.
  assert (STb : forall c1 n1 q1, str = PM.VLong c1 n1 q1 -> In (q1, c1) LB).
  { intros c1 n1 q1 E. apply SOWN. rewrite E. cbn. left. reflexivity. }
  assert (STbX : forall c1 n1 q1, str = PM.VLong c1 n1 q1 -> In (q1, c1) LBX).
  { intros c1 n1 q1 E. apply INCS. rewrite E. cbn. left. reflexivity. }
  assert (DF : 0 <= p /\ p + k <= 2 ^ 47 /\ L5.defined M p k /\ aacc M p k /\ app_rng ar p k
     /\ (forall a, p <= a < p + k -> in_block LB a \/ in_fframe FF a)
     /\ (forall a, p <= a < p + k -> ~ (sp - 20480 <= a < sp) /\ ~ (ois <= a < ois + 272) /\ ~ (os <= a < os + 296)
           /\ ~ (qc <= a < qc + 16384) /\ (forall c1 n1 q1, str = PM.VLong c1 n1 q1 -> ~ (q1 <= a < q1 + c1))
           /\ ~ (65536 <= a < 6897664))
     /\ (p + k <= BIGSHADOW_LO \/ BIGSHADOW_HI <= p)
     /\ (k = 16384 -> PGS.in_blk OB p k)
     /\ (PMSPA.aobjA FF p k \/ exists q m, In (q, m) LB /\ q <= p /\ p + k <= q + m)
     /\ (p + k <= qc \/ qc + 16384 <= p)
     /\ (((p + k <= lo \/ hi <= p) /\ (forall B m, In (B, m) OB -> p + k <= B \/ B + m <= p)) \/ PGS.ow_win O M (PM.SRC qc de rem) OB p k)).
  { destruct FSAPP as (FSA0 & FSAs & FSA47). destruct QAPP as (QA0 & QAs & QA47).
    assert (OBJ : forall (APo : p + k <= os \/ os + 296 <= p) (APi : p + k <= ois \/ ois + 272 <= p),
      PMSPA.aobjA FF p k -> L5.defined M p k -> aacc M p k -> k < 16384 ->
      (((p + k <= lo \/ hi <= p) /\ (forall B m, In (B, m) OB -> p + k <= B \/ B + m <= p)) \/ PGS.ow_win O M (PM.SRC qc de rem) OB p k) ->
      0 <= p /\ p + k <= 2 ^ 47 /\ L5.defined M p k /\ aacc M p k /\ app_rng ar p k
     /\ (forall a, p <= a < p + k -> in_block LB a \/ in_fframe FF a)
     /\ (forall a, p <= a < p + k -> ~ (sp - 20480 <= a < sp) /\ ~ (ois <= a < ois + 272) /\ ~ (os <= a < os + 296)
           /\ ~ (qc <= a < qc + 16384) /\ (forall c1 n1 q1, str = PM.VLong c1 n1 q1 -> ~ (q1 <= a < q1 + c1))
           /\ ~ (65536 <= a < 6897664))
     /\ (p + k <= BIGSHADOW_LO \/ BIGSHADOW_HI <= p)
     /\ (k = 16384 -> PGS.in_blk OB p k)
     /\ (PMSPA.aobjA FF p k \/ exists q m, In (q, m) LB /\ q <= p /\ p + k <= q + m)
     /\ (p + k <= qc \/ qc + 16384 <= p)
     /\ (((p + k <= lo \/ hi <= p) /\ (forall B m, In (B, m) OB -> p + k <= B \/ B + m <= p)) \/ PGS.ow_win O M (PM.SRC qc de rem) OB p k)).
    { intros APo APi AOD DD AD Hk16 DWX.
      pose proof AOD as (f & Hf & X1 & X2). destruct (WF f Hf) as (Y1 & Y2 & _).
      pose proof (PMASK.blk_obj_apart L ar C HI HIok LB FF LK cr Aw M _ qc 16384 p k HH QIN AOD) as APQ.
      split; [clear - X1 Y1 FSI; lia|]. split; [clear - X2 Y2 FSCEIL SLO SHI SPT; lia|]. split; [exact DD|]. split; [exact AD|].
      split; [apply (L5SAR.app_rng_fs L ar C HI HIok LB FF LK cr Aw M _ p k HH); clear - X1 X2 Y1 Y2; lia|].
      split; [intros a Ha; right; apply (PMASR1.in_fframe_of_aobjA FF p k a AOD Ha)|].
      split; [|split; [unfold BIGSHADOW_LO, BIGSHADOW_HI; destruct FSAs as [Z|Z]; [left|right]; clear - Z X1 X2 Y1 Y2; lia|
               split; [intros E; exfalso; clear - E Hk16; lia| split; [left; exact AOD| split; [clear - APQ; Lia.lia| exact DWX]]]]].
      intros a Ha. split; [clear - Ha X2 Y2 FSCEIL SLO; lia|]. split; [clear - Ha APi; lia|]. split; [clear - Ha APo; lia|].
      split; [clear - Ha APQ; lia|]. split; [|clear - Ha X1 Y1 FSI; lia].
      intros c1 n1 q1 E; destruct (PMASK.blk_obj_apart L ar C HI HIok LB FF LK cr Aw M _ q1 c1 p k HH (STb c1 n1 q1 E) AOD) as [Z|Z]; clear - Ha Z; lia. }
    destruct DST as [(AOD & Hk8 & DD & AD & APF)|DW].
    -
      apply OBJ; [clear - APF LY1 LY2; lia| clear - APF LY3 LY4; lia| exact AOD| exact DD| exact AD| clear - Hk8; lia|].
      left. split; [exact APF|]. intros B m Hin.
      destruct (PMASK.blk_obj_apart L ar C HI HIok LB FF LK cr Aw M _ B m p k HH (OBIN B m Hin) AOD) as [Z|Z]; clear - Z; lia.
    - destruct (PGSA.oo_win _ _ _ _ _ _ OK M (PM.SRC qc de rem) OB p k PA DW) as (W0 & WD & [(B & m & BIN & WB1 & WB2)|(W1 & W2 & WL1 & WL2 & WL3 & WL4 & WL5)] & WACC).
      +
        pose proof (OBIN B m BIN) as TIN.
        destruct (WB _ TIN) as ((T0 & TI & _ & _ & T4 & TAPP) & _). cbn [fst snd] in T0, TI, T4, TAPP.
        rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa) in TI. unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI in TAPP. destruct TAPP as (TA0 & TAs & TA47).
        assert (NQ : B <> qc).
        { intros E. apply (PMASK.fst_neq_appA [(qc, 16384)] (OB ++ LBX) qc 16384 B m); [exact ND| left; reflexivity| apply in_or_app; left; exact BIN| symmetry; exact E]. }
        pose proof (PMASK.blk_apart L ar C HI HIok LB FF LK cr Aw M _ B m qc 16384 HH TIN QIN NQ) as APQ.
        pose proof (PMASK.blk_obj_apart L ar C HI HIok LB FF LK cr Aw M _ B m os 296 HH TIN AO) as APP.
        pose proof (PMASK.blk_obj_apart L ar C HI HIok LB FF LK cr Aw M _ B m ois 272 HH TIN AOI) as API.
        split; [clear - WB1 T0; lia|]. split; [clear - WB2 T4 SLO SHI SPT; lia|]. split; [exact WD|]. split; [exact WACC|].
        split; [apply (L5SAR.app_rng_block L ar C HI HIok LB FF LK cr Aw M _ B m p k HH TIN); clear - WB1 WB2; lia|].
        split; [intros a Ha; left; apply (PMASR1.in_block_of LB B m a TIN); clear - Ha WB1 WB2; lia|].
        split; [|split; [unfold BIGSHADOW_LO, BIGSHADOW_HI; destruct TAs as [Z|Z]; [left|right]; clear - Z WB1 WB2; lia
                        | split; [intros _; exists B, m; split; [exact BIN|]; split; [exact WB1| exact WB2]|
                          split; [right; exists B, m; split; [exact TIN|]; split; [exact WB1| exact WB2]| split; [clear - APQ WB1 WB2; Lia.lia| right; exact DW]]]]].
        intros a Ha. split; [clear - Ha WB1 WB2 T4 SLO; lia|]. split; [clear - Ha WB1 WB2 API; lia|]. split; [clear - Ha WB1 WB2 APP; lia|].
        split; [clear - Ha WB1 WB2 APQ; lia|]. split; [|clear - Ha WB1 WB2 TI T0; lia].
        intros c1 n1 q1 E.
        assert (NS : B <> q1) by (apply (PMASK.fst_neq_appA ((qc, 16384) :: OB) LBX B m q1 c1); [exact ND| right; exact BIN| exact (STbX c1 n1 q1 E)]).
        destruct (PMASK.blk_apart L ar C HI HIok LB FF LK cr Aw M _ B m q1 c1 HH TIN (STb c1 n1 q1 E) NS) as [Z|Z]; clear - Ha WB1 WB2 Z; lia.
      +
        unfold PM.CHUNK in WL3.
        apply OBJ; [exact WL4| exact WL5| apply (PGSKA.aobjA_sub FF lo hi p k OFR WL1 WL2)| exact WD| exact WACC| exact WL3| right; exact DW]. }
  destruct DF as (DP0 & DP1 & DDP & DAP & DAPP & DCL & DX & DSH & D16K & DLOC & DQA & DWX).
  assert (pk : p' = p /\ k' = k).
  { rewrite A11 in A11'. rewrite A12 in A12'. apply (f_equal bv_unsigned) in A11', A12'.
    rewrite !L5.unsigned_lit in A11', A12' by (clear - Hp' Hk' DP0 DP1 Hk; lia). split; congruence. }
  destruct pk as (-> & ->). clear A11' A12'.
  destruct FSAPP as (FSA0 & FSAs & FSA47). destruct QAPP as (QA0 & QAs & QA47).
  assert (APQO : forall o n, PMSPA.aobjA FF o n -> qc + 16384 <= o \/ o + n <= qc).
  { intros o n AOo. exact (PMASK.blk_obj_apart L ar C HI HIok LB FF LK cr Aw M _ qc 16384 o n HH QIN AOo). }
  set (WA := PGS.W_srcG os ois (PM.SRC qc de rem) ++ [(p, k)]).
  assert (OUTWA : forall i, ~ (os + 256 <= i < os + 296) -> ~ (ois + 40 <= i < ois + 48) -> ~ (ois + 152 <= i < ois + 156) ->
                  ~ (qc <= i < qc + 16384) -> ~ (p <= i < p + k) -> L5.outside WA i).
  { intros i N1 N2 N3 N4 N5 r0 Hr. unfold WA, PGS.W_srcG, PGS.W_srcfG in Hr. cbn [PM.sr_qc app] in Hr. unfold L5.in_rng.
    destruct Hr as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn [fst snd]; unfold PM.CHUNK; clear - N1 N2 N3 N4 N5; lia. }
  assert (WAPP : PMKA.wapp WA).
  { unfold WA, PGS.W_srcG, PGS.W_srcfG. cbn [PM.sr_qc app]. unfold BIGSHADOW_LO, BIGSHADOW_HI in OBIG, IBIG, DSH.
    apply PMKA.wapp_cons; [cbn [fst snd]; unfold BIGSHADOW_LO, BIGSHADOW_HI; clear - OBIG; Lia.lia|].
    apply PMKA.wapp_cons; [cbn [fst snd]; unfold BIGSHADOW_LO, BIGSHADOW_HI; clear - IBIG; Lia.lia|].
    apply PMKA.wapp_cons; [cbn [fst snd]; unfold BIGSHADOW_LO, BIGSHADOW_HI; clear - IBIG; Lia.lia|].
    apply PMKA.wapp_cons; [cbn [fst snd]; unfold BIGSHADOW_LO, BIGSHADOW_HI, PM.CHUNK; clear - QAs; Lia.lia|].
    apply PMKA.wapp_cons; [cbn [fst snd]; unfold BIGSHADOW_LO, BIGSHADOW_HI; clear - DSH; Lia.lia| apply PMKA.wapp_nil]. }
  assert (OUTIMG : forall a, 65536 <= a < 6897664 -> L5.outside WA a).
  { intros a Ha. apply OUTWA; [clear - Ha O1; lia| clear - Ha I1; lia| clear - Ha I1; lia| clear - Ha QI; lia|].
    intros Y. destruct (DX a Y) as (_ & _ & _ & _ & _ & X6). apply X6. exact Ha. }
  assert (OWA : Forall (fun b => fst b + snd b <= lo \/ hi <= fst b) (PM.src_own (PM.SRC qc de rem) ++ OB)).
  { apply Forall_forall. intros [B m] Hin. cbn [fst snd].
    assert (HB : In (B, m) LB) by (unfold LB; rewrite app_assoc; apply in_or_app; left; exact Hin).
    destruct (PMASK.blk_obj_apart L ar C HI HIok LB FF LK cr Aw M _ B m lo (hi - lo) HH HB OFR) as [X|X]; [left; exact X| right; clear - X; lia]. }
  assert (OWB : forall b, In b OB -> fst b + snd b <= PM.sr_qc (PM.SRC qc de rem) \/ PM.sr_qc (PM.SRC qc de rem) + PM.CHUNK <= fst b).
  { intros [B m] Hin. cbn [fst snd PM.sr_qc]. unfold PM.CHUNK.
    assert (NE : B <> qc).
    { intros E. apply (PMASK.fst_neq_appA [(qc, 16384)] (OB ++ LBX) qc 16384 B m); [exact ND| left; reflexivity| apply in_or_app; left; exact Hin| symmetry; exact E]. }
    destruct (PMASK.blk_apart L ar C HI HIok LB FF LK cr Aw M _ B m qc 16384 HH (OBIN B m Hin) QIN NE) as [X|X]; clear - X; lia. }
  assert (OWC : Forall (fun r => ((fst r + snd r <= lo \/ hi <= fst r) /\ (forall B m, In (B, m) OB -> fst r + snd r <= B \/ B + m <= fst r) /\ app_mem (fst r) (snd r))
                              \/ PGS.ow_win O M (PM.SRC qc de rem) OB (fst r) (snd r)) [(p, k)]).
  { constructor; [| constructor]. cbn [fst snd]. destruct DWX as [(DW1 & DW2)|DW]; [left| right; exact DW].
    split; [exact DW1|]. split; [exact DW2|]. unfold app_mem. split; [exact DP0|]. split; [exact DSH| exact DP1]. }
  assert (OWU : forall (M3 : word -> option byte) (de' rem' : Z),
      L5CA.ahpres L ar LB FF sp 20480 WA M M3 ->
      L5.u64_at RSEGS M3 (os + 264) qc -> L5.u64_at RSEGS M3 (os + 272) 16384 ->
      L5.u64_at RSEGS M3 (os + 280) de' -> L5.u64_at RSEGS M3 (os + 288) rem' ->
      qc <= de' -> 0 <= rem' -> de' + rem' <= qc + 16384 ->
      PGS.ow_at O M3 (PM.SRC qc de' rem') OB).
  { intros M3 de' rem' AH C264 C272 C280 C288 Q1' Q2' Q3'. pose proof (proj1 AH) as EK. pose proof (proj2 (proj2 AH)) as DK.
    assert (OUTO : forall i, os <= i < os + 256 -> L5.outside WA i).
    { intros i Hi. apply OUTWA; [clear - Hi; lia| clear - Hi LYD; lia| clear - Hi LYD; lia| destruct (APQO os 296 AO) as [Z|Z]; clear - Hi Z; lia|].
      intros Y. destruct (DX i Y) as (_ & _ & X3 & _). apply X3. clear - Hi; lia. }
    apply (PGSA.oo_upd _ _ _ _ _ _ OK LBX sp 20480 [(p, k)] M M3 (PM.SRC qc de rem) (PM.SRC qc de' rem') OB FF LK Aw cr (vml_of model) OFR PA HH OWA OWB OWC).
    - exact AH.
    - apply (PGSKA.src_fields_updG M M3 os ois (ois + 16) qc de rem de' rem' PSRC0); unfold PM.CHUNK.
      + clear - O1; lia.
      + clear - O1; lia.
      + apply (PMKA.agA_obj L ar LB FF sp 20480 WA M M3 EK WAPP FRB os 256); [apply (PGSKA.aobjA_sub FF lo hi); [exact OFR| clear - LY1; lia| clear - LY2; lia]| exact OUTO].
      + apply (PMKA.agsh_obj L ar LB FF sp 20480 WA M M3 EK WAPP FRB (os + 256) 40). apply (PGSKA.aobjA_sub FF lo hi); [exact OFR| clear - LY1; lia| clear - LY2; lia].
      + apply (PMASK.defined_dk L ar LB FF sp 20480 M M3 (os + 256) 8 DK); [| clear - O1; lia| clear - O1; lia| exact SD256].
        intros i Hi. apply PMASR1.cl_of_bf. right. apply (PMASR1.in_fframe_of_aobjA FF os 296 i AO). clear - Hi; lia.
      + apply (PMASK.agsh_blk L ar LB FF sp 20480 WA M M3 qc 16384 EK WAPP QIN); [clear - Q0; lia| clear - Q4 SLO SHI SPT; lia].
      + apply (PMASK.defined_dk L ar LB FF sp 20480 M M3 qc 16384 DK); [| clear - Q0; lia| clear - Q4 SLO SHI SPT; lia| exact DCH].
        intros i Hi. apply PMASR1.cl_of_bf. left. apply (PMASR1.in_block_of LB qc 16384 i QIN Hi).
      + exact C264. + exact C272. + exact C280. + exact C288. + exact Q1'. + exact Q2'. + exact Q3'.
    - reflexivity. }
  assert (pbk : pb = p /\ kb = k).
  { pose proof ST as ST'. unfold PGSRDK16.srd_stC in ST'. pdestr ST'.
    rewrite A11 in R11. rewrite A12 in R12. apply (f_equal bv_unsigned) in R11, R12.
    rewrite !L5.unsigned_lit in R11, R12 by (first [clear - DP0 DP1 Hk; lia | rewrite <- XV37; assumption | rewrite <- XV38; assumption]).
    split; congruence. }
  destruct pbk as (pbp & kbk). rewrite pbp in *. rewrite kbk in *. clear pbp kbk.
  pose proof G as G'. unfold PGSRDK16.srd_frame in G'.
  destruct G' as [_ GSPT GSLO GSHI GSPC GOCR GOWN GFS1 GFS2 GFCEIL GLKI2 GFLP GFLNC GHH2 GFLC GFR GF8 GFBIG GF32 GFLA GFLR GFLBIG GNCF GNCS].
  pose proof BD as BD'. unfold PGSRDK16.srd_body, PMAUK.binv in BD'.
  destruct BD' as (HHc & AMc & MRTc & INCAc & INCLc & ASTKc & EKc & DKc & OWNc & DSHc).
  assert (C1 : getr Rc (reg 1) = Z_to_bv 64 0xaef9c).
  { pose proof ST as S'. unfold PGSRDK16.srd_stC in S'. pdestr S'. rewrite <- XV61. assumption. }
  assert (C2 : getr Rc (reg 2) = Z_to_bv 64 (sp - 160 - 16)).
  { pose proof ST as S'. unfold PGSRDK16.srd_stC in S'. pdestr S'.
    match goal with H : getr Rc (reg 2) = _ |- _ => rewrite H end. rewrite XV2. f_equal. clear; lia. }
  assert (C12 : getr Rc (reg 12) = Z_to_bv 64 16384).
  { pose proof ST as S'. unfold PGSRDK16.srd_stC in S'. pdestr S'. rewrite <- XV65. assumption. }
  assert (WCL : forall rr a, In rr (PGS.W_srcG os ois (PM.SRC qc qc 0) ++ []) -> L5.in_rng rr a -> aclient L ar LB FF sp 20480 a).
  { intros rr a Hin Ha. rewrite app_nil_r in Hin. unfold PGS.W_srcG, PGS.W_srcfG in Hin. cbn [PM.sr_qc app] in Hin. unfold L5.in_rng in Ha.
    apply PMASR1.cl_of_bf.
    destruct Hin as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd] in Ha.
    - right. apply (PMASR1.in_fframe_of_aobjA FF os 296 a AO). clear - Ha; lia.
    - right. apply (PMASR1.in_fframe_of_aobjA FF ois 272 a AOI). clear - Ha; lia.
    - right. apply (PMASR1.in_fframe_of_aobjA FF ois 272 a AOI). clear - Ha; lia.
    - left. apply (PMASR1.in_block_of LB qc 16384 a QIN). unfold PM.CHUNK in Ha. clear - Ha; lia. }
  unfold PGSA.fill_buffer_specG, PGSA.src_specG in FB.
  apply (FB O OK fxc Rc Mc modelc K OB LBX ((F, 1, sp - 160 - 16 + 32) :: FF) LKc Ac cr (sp - 160 - 16) 0xaef9c (PM.SRC qc qc 0) str (PM.STRM g eg sst) []).
  - exact HHc.
  - exact AMc.
  - exact K0.
  - unfold PMSPA.entryA. rewrite L5K.rl1, L5K.rl2, L5K.rl3, L5K.rl4.
    split; [exact C1|]. split; [split; [clear; lia| reflexivity]|]. split; [exact C2|].
    split; [rewrite XR3; exact Rgp|]. split; [rewrite XR4; exact Rtp|].
    change (PMSPA.pm_scr 3) with 18432.
    split.
    + replace (sp - 160 - 16) with (sp - 160 - 16) by (clear; lia).
      try (replace (sp - 160 - 16) with (sp - 176) by lia); apply (L5SAR.astk_sub ar Mc Mc sp 20480 176 18432 ASTKc (fun _ X => X)); [clear; lia| clear; lia| clear; lia|].
      clear - S32. lia.
    + assert (M8a : (sp - 20480) mod 8 = 0) by (clear - S32; lia).
      assert (M8b : (sp - 160 - 16 - 18432) mod 8 = 0) by (clear - S32; lia).
      apply (PMKA.shadow_zero_sub Mc (sp - 20480) (20480 / 8)); [exact M8a| exact M8b| clear; lia| clear; lia| clear; lia|].
      apply (PMKA.stksh_keepA L ar LB FF sp 20480 WA M Mc EKc WAPP (sp - 20480) (20480 / 8));
        [clear - SLO SPT; lia| clear - SLO; lia| clear - SHI SPT; lia| exact M8a| clear; lia| exact STKSH].
  - apply (PMAUAR.ffroomB_push PNRA.FCB 4 3 FF LK LKc _ FRM INCLc); [| clear; lia].
    pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HHc) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & NDF1 & _).
    exact NDF1.
  - apply (PMAUAR.ffrsA_push FF sp (sp - 160 - 16) F 1 (sp - 160 - 16 + 32) FRS); clear; lia.
  - unfold PGSA.ofr. apply PMAUAR.aobjA_push. exact OFR.
  - rewrite L5K.rl10. exact XC10.
  - unfold PGSA.fill_args. rewrite L5SAR.r11, L5SAR.r12. split; [exact XC11| exact C12].
  - reflexivity.
  - exact XPA.
  - exact XIA.
  - exact XBASE.
  - exact INCS.
  - intros fx2 R2 M4 model4 LK4 Aw4 src4 sm4 RP4 PA4 IA4 STEP4 RES4 HP4 MRT4 INC4 INCA4 AM4 HH4.
    destruct RES4 as (E4 & c & A10c & Hc & Hg4 & RS0 & RS2). subst src4.
    destruct sm4 as [g2 eg2 st2]. cbn [PM.sm_g PM.sm_eg PM.sm_st] in Hg4, RS0, RS2, STEP4.
    pose proof STEP4 as (_ & EG4 & _ & _ & _). cbn [PM.sm_eg] in EG4. subst eg2.
    unfold PM.CHUNK in Hc, RS0.
    assert (BD4 : PGSRDK16.srd_body L ar HI 16 O R M model OB LBX FF LK Aw sp (PM.SRC qc de rem) [(p, k)] F M4 model4 LK4 cr Aw4).
    { assert (HP4' : L5CA.ahpres L ar ([] ++ (PM.src_own (PM.SRC qc de rem) ++ OB ++ LBX)) ((F, 1, sp - 160 - 16 + 32) :: FF) (sp - 160 - 16) (PMSPA.pm_scr 3)
                        (PGS.W_srcG os ois (PM.SRC qc qc 0) ++ []) Mc M4).
      { exact HP4. }
      assert (HH4' : ri_inv HI ([] ++ (PM.src_own (PM.SRC qc de rem) ++ OB ++ LBX)) ((F, 1, sp - 160 - 16 + 32) :: FF) LK4 cr Aw4 M4 (vml_of model4)) by exact HH4.
      unfold PGSRDK16.srd_body.
      eapply (PMAUK.binv_callee L ar C HI HIok); [exact G| exact BD| exact HP4'| exact HH4'| exact AM4| exact MRT4| exact INCA4| exact INC4| unfold PMSPA.pm_scr; clear; lia| unfold PMSPA.pm_scr; clear; lia| | |].
      + intros rr a Hin Ha. pose proof (WCL rr a Hin Ha) as CLa. change (ff_bytes 1) with 128 in *. change (128 / 8) with 16 in *.
        unfold PNACSK.ocell. split.
        * intros Y. apply (GNCS a); [clear - Y; lia| exact CLa].
        * intros Y. apply (GNCF a); [right; unfold S; destruct GF8 as (_ & GF8b & _); rewrite GF8b; clear - Y; lia| exact CLa].
      + intros a _ Oq rr Hin X. apply (Oq rr); [| exact X]. rewrite app_nil_r in Hin. apply in_or_app. left. exact Hin.
      + intros a X. exact X. }
    pose proof BD4 as BD4'. unfold PGSRDK16.srd_body, PMAUK.binv in BD4'.
    destruct BD4' as (HH4b & AM4b & MRT4b & INCA4b & INCL4b & ASTK4 & EK4 & DK4 & OWN4 & DSH4).
    set (MVc := mrestrict (ahid Ac modelc) Mc) in *.
    set (MV4 := mrestrict (ahid Aw4 model4) M4) in *.
    assert (F4 : 4 * V 50%nat = F / 8) by (clear - XV50; lia).
    assert (AG2 : forall i, (V 2%nat - 160 <= i < V 2%nat + 16) \/ (32 * V 50%nat <= i < 32 * V 50%nat + 120 /\ ~ (32 * V 50%nat + 24 <= i < 32 * V 50%nat + 32))
                          \/ (4 * V 50%nat + 2147450880 <= i < 4 * V 50%nat + 2147450880 + 16) -> MV4 (Z_to_bv 64 i) = MVc (Z_to_bv 64 i)).
    { intros i Hi. rewrite XV2, XV50, F4 in Hi. unfold MV4, MVc.
      change (ff_bytes 1) with 128 in GNCF, GF8, GFR.
      pose proof GFR as (GFR1 & GFR2 & _).
      apply (srd_fill_ag O R M model K OB LBX FF LK Aw cr sp r (PM.SRC qc de rem) str (PM.STRM g eg sst) [(p, k)] F fl LK2 M2 model2
               Mc modelc LKc Ac M4 model4 LK4 Aw4 (PM.SRC qc qc 0) i CTX0 G BD BD4 HP4).
      - destruct Hi as [Y|[Y|Y]]; clear - Y SLO SHI SPT GFR1 GFR2; unfold SB in *; lia.
      - destruct Hi as [Y|[Y|Y]]; [left| right; left| right; right; left]; unfold SB in *; clear - Y; lia.
      - intros rr Hin Hr. pose proof (WCL rr i Hin Hr) as CLi. destruct Hi as [Y|[Y|Y]].
        + apply (GNCS i); [clear - Y; lia| exact CLi].
        + apply (GNCF i); [left; clear - Y; lia| exact CLi].
        + apply (GNCF i); [right; unfold S; destruct GF8 as (_ & GF8b & _); rewrite GF8b; unfold SB in *; clear - Y; lia| exact CLi]. }
    assert (EKcm : L5SAR.ek L ar LB FF sp 20480 (PGS.W_srcG os ois (PM.SRC qc qc 0) ++ []) Mc M4).
    { apply (L5SAR.ek_callee L ar LB [] FF [(F, 1, sp - 160 - 16 + 32)] sp 20480 (sp - 160 - 16) (PMSPA.pm_scr 3) (PGS.W_srcG os ois (PM.SRC qc qc 0) ++ []) (PGS.W_srcG os ois (PM.SRC qc qc 0) ++ []) Mc M4 HP4);
        [unfold PMSPA.pm_scr; clear; lia| clear; lia|].
      intros a _ X. exact X. }
    assert (OUTIMGc : forall a, 65536 <= a < 6905856 -> L5.outside (PGS.W_srcG os ois (PM.SRC qc qc 0) ++ []) a).
    { intros a Ha rr Hin Hr. rewrite app_nil_r in Hin. unfold PGS.W_srcG, PGS.W_srcfG in Hin. cbn [PM.sr_qc app] in Hin. unfold L5.in_rng in Hr.
      destruct Hin as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd] in Hr; unfold PM.CHUNK in Hr;
        [clear - Ha Hr O1 OFS1 FSI| clear - Ha Hr I1| clear - Ha Hr I1| clear - Ha Hr QI]; lia. }
    assert (BASE4 : PMSTA.base_okA RSEGS PMA.AD M4) by exact (PMASK.base_keep L ar C LY LB FF sp 20480 _ Mc M4 EKcm OUTIMGc XBASE).
    pose proof (PMASK.mach_vis L ar C HI LY HIok _ _ _ _ _ M4 model4 HH4 BASE4) as (GV0 & GV1 & GV2).
    pose proof (PGSA.oo_src _ _ _ _ _ _ OK M4 _ OB PA4) as (PSRC4 & PNI4 & SDEF4).
    pose proof (PGSKA.src_visG L ar C HI LY HIok _ ((F, 1, sp - 160 - 16 + 32) :: FF) LK4 cr Aw4 M4 model4 os _ _ (PM.SRC qc qc 0) sp 20480 HH4
                  (PMAUAR.aobjA_push _ _ _ _ AO) O8 PSRC4 PNI4 ASTK4) as (_ & OZ4 & OW4 & _ & OAV4 & _).
    pose proof PSRC4 as PSRC4'.
    destruct PSRC4' as (S240' & S248' & SD256' & S264' & S272' & S280' & S288' & _).
    cbn [PM.sr_qc PM.sr_de PM.sr_rem] in S264', S272', S280', S288'.
    assert (O1' : 0 <= os /\ os + 296 <= 2 ^ 64) by (clear - O1; lia).
    assert (C264 : L5.u64_at RSEGS MV4 (V 36%nat + 264) (V 34%nat)).
    { rewrite XV36, XV34. apply (proj2 (L5A.u64_at_vis (ahid Aw4 model4) M4 (os + 264) qc (OAV4 (os + 264) 8 ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear - O1'; lia) ltac:(clear - O1'; lia))). exact S264'. }
    assert (C280 : L5.u64_at RSEGS MV4 (V 36%nat + 280) (V 34%nat)).
    { rewrite XV36, XV34. apply (proj2 (L5A.u64_at_vis (ahid Aw4 model4) M4 (os + 280) qc (OAV4 (os + 280) 8 ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear - O1'; lia) ltac:(clear - O1'; lia))). exact S280'. }
    assert (C288 : L5.u64_at RSEGS MV4 (V 36%nat + 288) 0).
    { rewrite XV36. apply (proj2 (L5A.u64_at_vis (ahid Aw4 model4) M4 (os + 288) 0 (OAV4 (os + 288) 8 ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear - O1'; lia) ltac:(clear - O1'; lia))). exact S288'. }
    assert (C272v : forall v, L5.u64_at RSEGS M4 (os + 272) v -> L5.u64_at RSEGS MV4 (V 36%nat + 272) v).
    { intros v X. rewrite XV36. apply (proj2 (L5A.u64_at_vis (ahid Aw4 model4) M4 (os + 272) v (OAV4 (os + 272) 8 ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear - O1'; lia) ltac:(clear - O1'; lia))). exact X. }
    assert (C272 := C272v _ S272').
    assert (D256 : L5.defined MV4 (V 36%nat + 256) 8).
    { rewrite XV36. apply (proj2 (L5A.defined_vis (ahid Aw4 model4) M4 (os + 256) 8 (OAV4 (os + 256) 8 ltac:(clear; lia) ltac:(clear; lia)))). exact SD256'. }
    assert (W296 : L5.writable RSEGS MV4 (V 36%nat) 296) by (rewrite XV36; exact OW4).
    assert (Z36 : L5KA.zeros_at MV4 (((V 36%nat + 8) / 8) + 2147450880) 36) by (rewrite XV36; exact OZ4).
    pose proof (L5SAR.fl_writable L ar C HI LYa HIok _ _ LK4 cr Aw4 M4 (vml_of model4) fl HH4 GFLP) as (_ & FLW4).
    assert (WFL : L5.writable RSEGS MV4 (V 51%nat) 1).
    { rewrite XV51. pose proof GFLR as (FL1 & FL2 & _).
      apply (proj2 (L5A.writable_vis (ahid Aw4 model4) M4 fl 1 (L5SAR.fl_vis L ar C HI LYa HIok _ _ LK4 cr Aw4 M4 model4 fl HH4 GFLP) ltac:(clear - FL1; lia) ltac:(clear - FL2; lia))).
      exact FLW4. }
    pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH4) as FSD4. repeat lazymatch type of FSD4 with _ /\ _ => apply proj2 in FSD4 end.
    pose proof (L5SAR.vis_pack L ar C HI LYa HIok _ _ LK4 cr Aw4 M4 model4 HH4) as VP4; cbv zeta in VP4; destruct VP4 as (_ & _ & _ & VFS4 & _).
    pose proof GFR as (GFR1' & GFR2' & _). change (ff_bytes 1) with 128 in GFS2, GFR2'.
    assert (DFM4 : forall a n, F <= a -> a + n <= F + 128 -> 0 <= n -> L5.defined MV4 a n).
    { intros a n Ha Hn Hn0. apply (proj2 (L5A.defined_vis (ahid Aw4 model4) M4 a n (VFS4 a n ltac:(clear - Ha GFS1; lia) ltac:(clear - Hn GFS2; lia)))).
      intros i Hi. replace (a + i) with (ar_fs ar + (a + i - ar_fs ar)) by (clear; lia). apply FSD4. unfold FS_BYTES in *. clear - Hi Ha Hn GFS1 GFS2; lia. }
    assert (DF128 : L5.defined MV4 (32 * V 50%nat) 128) by (rewrite XV50; apply DFM4; clear; lia).
    assert (DF24 : L5.defined MV4 (32 * V 50%nat + 24) 8) by (rewrite XV50; apply DFM4; clear; lia).
    assert (DF40 : L5.defined MV4 (32 * V 50%nat + 40) 88) by (rewrite XV50; apply DFM4; clear; lia).
    assert (WF128 : L5.writable RSEGS MV4 (32 * V 50%nat) 128).
    { apply (L5C.writable_of_defined RSEGS); [exact DF128| rewrite XV50; clear - GFR1'; lia| rewrite XV50; clear - GFR2'; lia]. }
    assert (C120 : L5.u64_at RSEGS MV4 (32 * V 50%nat + 120) (V 51%nat)).
    { rewrite XV50, XV51.
      destruct (L5SAR.flagptr_now L ar C HI LYa HIok _ _ _ _ _ M2 _ _ _ LK4 cr Aw4 M4 model4 F 1 (sp - 160 - 16 + 32) (sp - 160 - 16 + 32) fl
                  GHH2 HH4 (or_introl eq_refl) (or_introl eq_refl) ltac:(right; left; reflexivity) GFLC) as (_ & X).
      replace (F + 120) with (F + ff_bytes 1 - 8) by (change (ff_bytes 1) with 128; clear; lia). exact X. }
    assert (STC4 : PGSRDK16.srd_stC (vxC V R2) R2 MV4).
    { pose proof ST as STc. unfold PGSRDK16.srd_stC in STc. pdestr STc.
      match goal with
      | H2 : _ <= V 2%nat <= _, H36 : _ <= V 36%nat <= _, H50 : _ <= V 50%nat <= _, H51 : 4096 <= V 51%nat <= _ |- _ =>
          pose proof (conj H2 (conj H36 (conj H50 H51))) as KB
      end.
      unfold PGSRDK16.srd_stC, vxC. cbn beta iota.
      PGSRDC16.sweep ltac:(first [assumption | exact (bv_unsigned_in_range _ _) | (symmetry; apply Z_to_bv_bv_unsigned)
                        | (rewrite (L5SAR.cs_of_preserved Rc R2 _ RP4) by inl; assumption)
                        | PGSRDC16.carry MVc AG2 KB]). }
    assert (VSV2 : forall i, In i [1; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> vxC V R2 i = bv_unsigned (getr R (reg i))).
    { intros i Hi. rewrite <- (XVS i Hi). cbn in Hi. repeat destruct Hi as [<-|Hi]; first [reflexivity | destruct Hi]. }
    assert (X3' : getr R2 (reg 3) = getr R (reg 3)) by (rewrite (L5SAR.cs_of_preserved Rc R2 3 RP4) by inl; exact XR3).
    assert (X4' : getr R2 (reg 4) = getr R (reg 4)) by (rewrite (L5SAR.cs_of_preserved Rc R2 4 RP4) by inl; exact XR4).
    assert (DP4 : L5.defined M4 p len1).
    { apply (PMASK.defined_dk L ar LB FF sp 20480 Mc M4 p len1 (L5SAR.dk_callee L ar LB [] FF [(F, 1, sp - 160 - 16 + 32)] sp 20480 (sp - 160 - 16) (PMSPA.pm_scr 3) _ Mc M4 HP4 ltac:(unfold PMSPA.pm_scr; clear; lia) ltac:(clear; lia)));
        [| clear - DP0 DP1 XL1 XL2; lia| clear - DP0 DP1 XL1 XL2; lia| exact XDP].
      intros i Hi. apply PMASR1.cl_of_bf. destruct (DCL i ltac:(clear - Hi XL2; lia)) as [Z|Z]; [left; exact Z| right; exact Z]. }
    pose proof IA as IAs. pose proof (PMASK.iss_size_ltA M ois str _ IAs) as SZ. cbn [PM.sm_g PM.sm_eg] in SZ.
    unfold PGSRDK16.srd_fill_ret_T in FRT.
    apply (FRT O R M model K OB LBX FF LK Aw cr sp r str [(p, k)] qc de rem g eg sst p k CTX0 R11 R12 F fl LK2 M2 model2 G
             fx2 R2 M4 model4 LK4 Aw4 (vxC V R2) BD4 XV2 XV36 XV37 XV38 XV50 XV51 VSV2 X3' X4' len1 c g2 st2 STC4 XV39 XV34).
    + rewrite L5K.rl10 in A10c. exact A10c.
    + exact PA4.
    + exact IA4.
    + exact BASE4.
    + exact XL1.
    + exact XL2.
    + exact XL3.
    + exact Hc.
    + exact Hg4.
    + destruct (Z.eq_dec sst 2) as [E2|E2]; [destruct (RS2 E2) as (E0 & _); subst c; clear - Hg4 SZ; lia|].
      assert (E0 : sst = 0) by (clear - IST E2; lia). destruct (RS0 E0) as (Ec & _). clear - Ec Hg4 SZ; lia.
    + exact (fun E => proj2 (RS2 E)).
    + intros Ec0. destruct (Z.eq_dec sst 2) as [E2|E2]; [exact (proj2 (RS2 E2))|].
      assert (E0 : sst = 0) by (clear - IST E2; lia). destruct (RS0 E0) as (Ec & Est). rewrite Est. subst c. reflexivity.
    + exact DP4.
Qed.

End WithHeap.
End PGSRDMB16.
