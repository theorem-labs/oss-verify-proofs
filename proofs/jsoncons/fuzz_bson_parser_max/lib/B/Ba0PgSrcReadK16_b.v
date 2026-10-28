(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
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

Module PGSRDK16.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Abbreviation mem := (word -> option byte).
Section WithHeap.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).

Definition srd_kont (O : PGS.owner) (R : bvmap 5 word) (M : mem) (model : Model) (K : TSet) (OB LBX : list (Z * Z))
    (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (sp r : Z) (src : PM.srcst) (str : PM.vstr) (sm : PM.strm)
    (Wextra : list L5.range) : Prop :=
  forall (fx' : FPState) (R' : bvmap 5 word) (M' : mem) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z)) (src' : PM.srcst) (sm' : PM.strm),
    regs_preserved R R' ->
    PGS.ow_at O M' src' OB ->
    PM.iss_at RSEGS PMA.AD PMSPA.accA M' (PGS.ow_ois O) str sm' -> PMSP.src_step src src' sm sm' ->
    PMPS.read_res R R' M' src src' sm sm' ->
    L5CA.ahpres L ar (PM.src_own src ++ OB ++ LBX) FF sp (PMSPA.pm_scr 4) (PGS.W_srcG (PGS.ow_os O) (PGS.ow_ois O) src ++ Wextra) M M' ->
    model_rt model model' -> incl LK' LK -> incl Aw Aw' -> L5CA.amodel_ok Aw' model' ->
    ri_inv HI (PM.src_own src ++ OB ++ LBX) FF LK' cr Aw' M' (vml_of model') ->
    srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx' R' r M' model') K.

Definition srd_ctx (al : Z) (O : PGS.owner) (R : bvmap 5 word) (M : mem) (model : Model) (K : TSet) (OB LBX : list (Z * Z))
    (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (sp r : Z) (src : PM.srcst) (str : PM.vstr) (sm : PM.strm)
    (Wextra : list L5.range) : Prop :=
  PGSA.owner_ok RSEGS PMA.AD L ar HI O /\
  ri_inv HI (PM.src_own src ++ OB ++ LBX) FF LK cr Aw M (vml_of model) /\ L5CA.amodel_ok Aw model /\ K [] /\
  PMSPA.entryA PMA.AD L ar R M sp r 4 /\ PGSA.ffroomB PNRA.FCB 4 FF LK /\ PMSPA.ffrsA FF sp /\ PGSA.ofr FF (PGS.ow_lo O) (PGS.ow_hi O) /\
  getr R 10%bv = Z_to_bv 64 (PGS.ow_os O) /\ sp mod 32 = al /\ PGSA.read_args O FF R M sp src OB /\ PMPS.read_W R Wextra /\
  PGS.ow_at O M src OB /\ PM.iss_at RSEGS PMA.AD PMSPA.accA M (PGS.ow_ois O) str sm /\ PMSTA.base_okA RSEGS PMA.AD M /\
  incl (PM.vs_own str) LBX /\
  srd_kont O R M model K OB LBX FF LK Aw cr sp r src str sm Wextra.

Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).

Definition srd_frame (al : Z) (R0 : bvmap 5 word) (OB LBX : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z))
    (cr : credit) (sp : Z) (src : PM.srcst) (F fl : Z) (LK2 : list fframe) (M2 : mem) (model2 : Model) : Prop :=
  PMAUK.gctx L ar HI (PM.src_own src ++ OB ++ LBX) FF LK Aw sp (PMSPA.pm_scr 4) (sp - 160 - al) (sp - 104) sp
    (PNACSK.ocell sp) (PNACSK.own sp R0) F fl 1 LK2 M2 model2 cr [].

Definition srd_body (al : Z) (O : PGS.owner) (R0 : bvmap 5 word) (M0 : mem) (model0 : Model) (OB LBX : list (Z * Z))
    (FF LK : list fframe) (Aw : list (Z * Z)) (sp : Z) (src : PM.srcst) (Wextra : list L5.range) (F : Z)
    (M : mem) (model : Model) (LKc : list fframe) (crc : credit) (Ac : list (Z * Z)) : Prop :=
  PMAUK.binv L ar HI M0 model0 (PM.src_own src ++ OB ++ LBX) FF LK Aw sp (PMSPA.pm_scr 4) (sp - 160 - al) (PNACSK.own sp R0) F 1
    (PGS.W_srcG (PGS.ow_os O) (PGS.ow_ois O) src ++ Wextra) [] M model LKc crc Ac.

Definition srd_stC (V : nat -> Z) (R : bvmap 5 word) (M : mem) : Prop :=
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
  /\ (0 <= (V 36%nat) < 2 ^ 64)
  /\ (0 <= (V 37%nat) < 2 ^ 64)
  /\ (0 <= (V 38%nat) < 2 ^ 64)
  /\ (0 <= (V 39%nat) < 2 ^ 64)
  /\ (0 <= (V 50%nat) < 2 ^ 64)
  /\ (0 <= (V 51%nat) < 2 ^ 64)
  /\ (0 <= (V 60%nat) < 2 ^ 64)
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
  /\ (getr R (reg 22) = Z_to_bv 64 ((V 36%nat) + 280))
  /\ (getr R (reg 23) = Z_to_bv 64 ((V 36%nat) + 288))
  /\ (getr R (reg 24) = Z_to_bv 64 (V 60%nat))
  /\ (getr R (reg 25) = Z_to_bv 64 ((4 * (V 50%nat)) + 2147450880))
  /\ (getr R (reg 26) = Z_to_bv 64 (32 * (V 50%nat)))
  /\ (getr R (reg 27) = Z_to_bv 64 2147450880)
  /\ (getr R (reg 28) = Z_to_bv 64 (V 71%nat))
  /\ (getr R (reg 29) = Z_to_bv 64 (V 72%nat))
  /\ (getr R (reg 30) = Z_to_bv 64 (V 73%nat))
  /\ (getr R (reg 31) = Z_to_bv 64 (V 74%nat))
  /\ (1 <= (V 38%nat) <= 16384)
  /\ (L5.img_clear M 65536 1282048)
  /\ (L5.u64_at RSEGS M 1309752 2147450880)
  /\ (L5.u32_at RSEGS M 1309760 1)
  /\ (140735332487232 <= (V 2%nat) <= 140737488355312)
  /\ ((V 2%nat) mod 32 = 0)
  /\ (L5.writable RSEGS M ((V 2%nat) - 160) 176)
  /\ (6905856 <= (V 36%nat) <= 140737488355032)
  /\ ((V 36%nat) mod 8 = 0)
  /\ ((2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 296 <= 2147446784))
  /\ (L5.writable RSEGS M (V 36%nat) 296)
  /\ ((((V 2%nat) - 160) + 176 <= (V 36%nat) \/ (V 36%nat) + 296 <= ((V 2%nat) - 160)))
  /\ (140735332487248 <= (V 2%nat) <= 140737488355328)
  /\ (L5.writable RSEGS M ((V 2%nat) - 160) 160)
  /\ ((((V 2%nat) - 160) + 160 <= (V 36%nat) \/ (V 36%nat) + 296 <= ((V 2%nat) - 160)))
  /\ (L5.u64_at RSEGS M (V 2%nat) (V 8%nat))
  /\ (L5.u64_at RSEGS M ((V 2%nat) + 8) (V 1%nat))
  /\ (215808 <= (V 50%nat) <= 4398046511102)
  /\ ((V 50%nat) mod 4 = 0)
  /\ (L5.defined M (32 * (V 50%nat)) 128)
  /\ (L5.writable RSEGS M (32 * (V 50%nat)) 128)
  /\ ((2147446784 + 17592186048512 <= (32 * (V 50%nat)) \/ (32 * (V 50%nat)) + 128 <= 2147446784))
  /\ (L5.writable RSEGS M ((4 * (V 50%nat)) + 2147450880) 16)
  /\ (4096 <= (V 51%nat) <= 140737488355327)
  /\ (L5.writable RSEGS M (V 51%nat) 1)
  /\ ((2147446784 + 17592186048512 <= (V 51%nat) \/ (V 51%nat) + 1 <= 2147446784))
  /\ (((32 * (V 50%nat)) + 128 <= (V 51%nat) \/ (V 51%nat) + 1 <= (32 * (V 50%nat))))
  /\ ((((V 2%nat) - 160) + 176 <= (32 * (V 50%nat)) \/ (32 * (V 50%nat)) + 128 <= ((V 2%nat) - 160)))
  /\ ((((V 2%nat) - 160) + 176 <= (V 51%nat) \/ (V 51%nat) + 1 <= ((V 2%nat) - 160)))
  /\ (((32 * (V 50%nat)) + 128 <= ((4 * (V 50%nat)) + 2147450880) \/ ((4 * (V 50%nat)) + 2147450880) + 16 <= (32 * (V 50%nat))))
  /\ (((V 51%nat) + 1 <= ((4 * (V 50%nat)) + 2147450880) \/ ((4 * (V 50%nat)) + 2147450880) + 16 <= (V 51%nat)))
  /\ ((((V 2%nat) - 160) + 176 <= ((4 * (V 50%nat)) + 2147450880) \/ ((4 * (V 50%nat)) + 2147450880) + 16 <= ((V 2%nat) - 160)))
  /\ (((32 * (V 50%nat)) + 128 <= (V 36%nat) \/ (V 36%nat) + 296 <= (32 * (V 50%nat))))
  /\ (((V 51%nat) + 1 <= (V 36%nat) \/ (V 36%nat) + 296 <= (V 51%nat)))
  /\ ((((4 * (V 50%nat)) + 2147450880) + 16 <= (V 36%nat) \/ (V 36%nat) + 296 <= ((4 * (V 50%nat)) + 2147450880)))
  /\ ((((4 * (V 50%nat)) + 2147450880) + 16 <= ((((V 36%nat) + 8) / 8) + 2147450880) \/ ((((V 36%nat) + 8) / 8) + 2147450880) + 36 <= ((4 * (V 50%nat)) + 2147450880)))
  /\ (((32 * (V 50%nat)) + 128 <= ((((V 36%nat) + 8) / 8) + 2147450880) \/ ((((V 36%nat) + 8) / 8) + 2147450880) + 36 <= (32 * (V 50%nat))))
  /\ (((V 51%nat) + 1 <= ((((V 36%nat) + 8) / 8) + 2147450880) \/ ((((V 36%nat) + 8) / 8) + 2147450880) + 36 <= (V 51%nat)))
  /\ (0 <= (V 39%nat) <= 16383)
  /\ (L5KA.zeros_at M ((((V 36%nat) + 8) / 8) + 2147450880) 36)
  /\ (L5.u64_at RSEGS M ((V 36%nat) + 264) (V 34%nat))
  /\ (L5.u64_at RSEGS M ((V 36%nat) + 272) 16384)
  /\ (L5.u64_at RSEGS M ((V 36%nat) + 280) (V 34%nat))
  /\ (L5.u64_at RSEGS M ((V 36%nat) + 288) 0)
  /\ (L5.defined M ((V 36%nat) + 256) 8)
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

Definition srd_stR (V : nat -> Z) (R : bvmap 5 word) (M : mem) : Prop :=
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
  /\ (0 <= (V 36%nat) < 2 ^ 64)
  /\ (0 <= (V 37%nat) < 2 ^ 64)
  /\ (0 <= (V 38%nat) < 2 ^ 64)
  /\ (0 <= (V 50%nat) < 2 ^ 64)
  /\ (0 <= (V 51%nat) < 2 ^ 64)
  /\ (0 <= (V 52%nat) < 2 ^ 64)
  /\ (0 <= (V 53%nat) < 2 ^ 64)
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
  /\ (0 <= (V 75%nat) < 2 ^ 64)
  /\ (0 <= (V 76%nat) < 2 ^ 64)
  /\ (0 <= (V 77%nat) < 2 ^ 64)
  /\ (0 <= (V 78%nat) < 2 ^ 64)
  /\ (0 <= (V 79%nat) < 2 ^ 64)
  /\ (getr R (reg 1) = Z_to_bv 64 (V 61%nat))
  /\ (getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 160))
  /\ (getr R (reg 5) = Z_to_bv 64 (V 62%nat))
  /\ (getr R (reg 6) = Z_to_bv 64 (V 63%nat))
  /\ (getr R (reg 7) = Z_to_bv 64 (V 64%nat))
  /\ (getr R (reg 8) = Z_to_bv 64 ((V 2%nat) + 16))
  /\ (getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 160))
  /\ (getr R (reg 10) = Z_to_bv 64 (V 65%nat))
  /\ (getr R (reg 11) = Z_to_bv 64 (V 66%nat))
  /\ (getr R (reg 12) = Z_to_bv 64 (V 67%nat))
  /\ (getr R (reg 13) = Z_to_bv 64 (V 68%nat))
  /\ (getr R (reg 14) = Z_to_bv 64 (V 69%nat))
  /\ (getr R (reg 15) = Z_to_bv 64 (V 70%nat))
  /\ (getr R (reg 16) = Z_to_bv 64 (V 71%nat))
  /\ (getr R (reg 17) = Z_to_bv 64 (V 72%nat))
  /\ (getr R (reg 18) = Z_to_bv 64 (V 73%nat))
  /\ (getr R (reg 19) = Z_to_bv 64 (V 36%nat))
  /\ (getr R (reg 20) = Z_to_bv 64 (V 74%nat))
  /\ (getr R (reg 21) = Z_to_bv 64 (V 75%nat))
  /\ (getr R (reg 22) = Z_to_bv 64 (V 76%nat))
  /\ (getr R (reg 23) = Z_to_bv 64 ((V 36%nat) + 288))
  /\ (getr R (reg 24) = Z_to_bv 64 (V 77%nat))
  /\ (getr R (reg 25) = Z_to_bv 64 ((4 * (V 50%nat)) + 2147450880))
  /\ (getr R (reg 26) = Z_to_bv 64 (32 * (V 50%nat)))
  /\ (getr R (reg 27) = Z_to_bv 64 2147450880)
  /\ (getr R (reg 28) = Z_to_bv 64 (V 78%nat))
  /\ (getr R (reg 29) = Z_to_bv 64 (V 79%nat))
  /\ (getr R (reg 30) = Z_to_bv 64 (V 52%nat))
  /\ (getr R (reg 31) = Z_to_bv 64 (V 53%nat))
  /\ (L5.img_clear M 65536 1282048)
  /\ (L5.u64_at RSEGS M 1309752 2147450880)
  /\ (L5.u32_at RSEGS M 1309760 1)
  /\ (140735332487232 <= (V 2%nat) <= 140737488355312)
  /\ ((V 2%nat) mod 32 = 0)
  /\ (L5.writable RSEGS M ((V 2%nat) - 160) 176)
  /\ (6905856 <= (V 36%nat) <= 140737488355032)
  /\ ((V 36%nat) mod 8 = 0)
  /\ ((2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 296 <= 2147446784))
  /\ (L5KA.zeros_at M ((((V 36%nat) + 8) / 8) + 2147450880) 36)
  /\ (L5.writable RSEGS M (V 36%nat) 296)
  /\ ((((V 2%nat) - 160) + 176 <= (V 36%nat) \/ (V 36%nat) + 296 <= ((V 2%nat) - 160)))
  /\ (L5.defined M ((V 36%nat) + 256) 8)
  /\ (140735332487248 <= (V 2%nat) <= 140737488355328)
  /\ (L5.writable RSEGS M ((V 2%nat) - 160) 160)
  /\ ((((V 2%nat) - 160) + 160 <= (V 36%nat) \/ (V 36%nat) + 296 <= ((V 2%nat) - 160)))
  /\ (L5.u64_at RSEGS M (V 2%nat) (V 8%nat))
  /\ (L5.u64_at RSEGS M ((V 2%nat) + 8) (V 1%nat))
  /\ (215808 <= (V 50%nat) <= 4398046511102)
  /\ ((V 50%nat) mod 4 = 0)
  /\ (L5.defined M (32 * (V 50%nat)) 128)
  /\ (L5.writable RSEGS M (32 * (V 50%nat)) 128)
  /\ ((2147446784 + 17592186048512 <= (32 * (V 50%nat)) \/ (32 * (V 50%nat)) + 128 <= 2147446784))
  /\ (L5.writable RSEGS M ((4 * (V 50%nat)) + 2147450880) 16)
  /\ (4096 <= (V 51%nat) <= 140737488355327)
  /\ (L5.writable RSEGS M (V 51%nat) 1)
  /\ ((2147446784 + 17592186048512 <= (V 51%nat) \/ (V 51%nat) + 1 <= 2147446784))
  /\ (((32 * (V 50%nat)) + 128 <= (V 51%nat) \/ (V 51%nat) + 1 <= (32 * (V 50%nat))))
  /\ ((((V 2%nat) - 160) + 176 <= (32 * (V 50%nat)) \/ (32 * (V 50%nat)) + 128 <= ((V 2%nat) - 160)))
  /\ ((((V 2%nat) - 160) + 176 <= (V 51%nat) \/ (V 51%nat) + 1 <= ((V 2%nat) - 160)))
  /\ (((32 * (V 50%nat)) + 128 <= ((4 * (V 50%nat)) + 2147450880) \/ ((4 * (V 50%nat)) + 2147450880) + 16 <= (32 * (V 50%nat))))
  /\ (((V 51%nat) + 1 <= ((4 * (V 50%nat)) + 2147450880) \/ ((4 * (V 50%nat)) + 2147450880) + 16 <= (V 51%nat)))
  /\ ((((V 2%nat) - 160) + 176 <= ((4 * (V 50%nat)) + 2147450880) \/ ((4 * (V 50%nat)) + 2147450880) + 16 <= ((V 2%nat) - 160)))
  /\ (((32 * (V 50%nat)) + 128 <= (V 36%nat) \/ (V 36%nat) + 296 <= (32 * (V 50%nat))))
  /\ (((V 51%nat) + 1 <= (V 36%nat) \/ (V 36%nat) + 296 <= (V 51%nat)))
  /\ ((((4 * (V 50%nat)) + 2147450880) + 16 <= (V 36%nat) \/ (V 36%nat) + 296 <= ((4 * (V 50%nat)) + 2147450880)))
  /\ ((((4 * (V 50%nat)) + 2147450880) + 16 <= ((((V 36%nat) + 8) / 8) + 2147450880) \/ ((((V 36%nat) + 8) / 8) + 2147450880) + 36 <= ((4 * (V 50%nat)) + 2147450880)))
  /\ (((32 * (V 50%nat)) + 128 <= ((((V 36%nat) + 8) / 8) + 2147450880) \/ ((((V 36%nat) + 8) / 8) + 2147450880) + 36 <= (32 * (V 50%nat))))
  /\ (((V 51%nat) + 1 <= ((((V 36%nat) + 8) / 8) + 2147450880) \/ ((((V 36%nat) + 8) / 8) + 2147450880) + 36 <= (V 51%nat)))
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
  /\ (L5.u64_at RSEGS M ((V 36%nat) + 264) (V 34%nat))
  /\ (L5.u64_at RSEGS M ((V 36%nat) + 272) 16384)
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

Definition srd_fill_ret_T (al : Z) : Prop :=
  forall (O : PGS.owner) (R0 : bvmap 5 word) (M0 : mem) (model0 : Model) (K : TSet) (OB LBX : list (Z * Z))
         (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (sp r : Z) (str : PM.vstr) (Wextra : list L5.range)
         (qc de rem g eg sst p k : Z),
    srd_ctx al O R0 M0 model0 K OB LBX FF LK Aw cr sp r (PM.SRC qc de rem) str (PM.STRM g eg sst) Wextra ->
    getr R0 (reg 11) = Z_to_bv 64 p -> getr R0 (reg 12) = Z_to_bv 64 k ->
    forall (F fl : Z) (LK2 : list fframe) (M2 : mem) (model2 : Model),
    srd_frame al R0 OB LBX FF LK Aw cr sp (PM.SRC qc de rem) F fl LK2 M2 model2 ->
    forall (fx : FPState) (R : bvmap 5 word) (M : mem) (model : Model) (LKc : list fframe) (Ac : list (Z * Z))
           (V : nat -> Z),
    srd_body al O R0 M0 model0 OB LBX FF LK Aw sp (PM.SRC qc de rem) Wextra F M model LKc cr Ac ->
    V 2%nat = sp - al -> V 36%nat = PGS.ow_os O -> V 37%nat = p -> V 38%nat = k -> 32 * V 50%nat = F -> V 51%nat = fl ->
    (forall i, In i [1; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> V i = bv_unsigned (getr R0 (reg i))) ->
    getr R (reg 3) = getr R0 (reg 3) -> getr R (reg 4) = getr R0 (reg 4) ->
    forall (len1 c g2 st2 : Z),
    srd_stC V R (mrestrict (ahid Ac model) M) -> V 39%nat = len1 -> V 34%nat = qc -> getr R (reg 10) = Z_to_bv 64 c ->
    PGS.ow_at O M (PM.SRC qc qc 0) OB -> PM.iss_at RSEGS PMA.AD PMSPA.accA M (PGS.ow_ois O) str (PM.STRM g2 eg st2) -> PMSTA.base_okA RSEGS PMA.AD M -> len1 = rem -> len1 < k -> k - len1 <= 16383 -> 0 <= c <= 16384 -> g2 = g + c -> g2 <= eg -> (sst = 2 -> st2 = 2) -> (c = 0 -> st2 = 2) -> L5.defined M p len1 ->
    srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx R 716700 M model) K.

Definition srd_exit_T (al : Z) : Prop :=
  forall (O : PGS.owner) (R0 : bvmap 5 word) (M0 : mem) (model0 : Model) (K : TSet) (OB LBX : list (Z * Z))
         (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (sp r : Z) (str : PM.vstr) (Wextra : list L5.range)
         (qc de rem g eg sst p k : Z),
    srd_ctx al O R0 M0 model0 K OB LBX FF LK Aw cr sp r (PM.SRC qc de rem) str (PM.STRM g eg sst) Wextra ->
    getr R0 (reg 11) = Z_to_bv 64 p -> getr R0 (reg 12) = Z_to_bv 64 k ->
    forall (F fl : Z) (LK2 : list fframe) (M2 : mem) (model2 : Model),
    srd_frame al R0 OB LBX FF LK Aw cr sp (PM.SRC qc de rem) F fl LK2 M2 model2 ->
    forall (fx : FPState) (R : bvmap 5 word) (M : mem) (model : Model) (LKc : list fframe) (Ac : list (Z * Z))
           (V : nat -> Z),
    srd_body al O R0 M0 model0 OB LBX FF LK Aw sp (PM.SRC qc de rem) Wextra F M model LKc cr Ac ->
    V 2%nat = sp - al -> V 36%nat = PGS.ow_os O -> V 37%nat = p -> V 38%nat = k -> 32 * V 50%nat = F -> V 51%nat = fl ->
    (forall i, In i [1; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> V i = bv_unsigned (getr R0 (reg i))) ->
    getr R (reg 3) = getr R0 (reg 3) -> getr R (reg 4) = getr R0 (reg 4) ->
    forall (de' rem' g' st' d : Z),
    srd_stR V R (mrestrict (ahid Ac model) M) -> V 76%nat = d ->
    L5.u64_at RSEGS M ((PGS.ow_os O) + 264) qc -> L5.u64_at RSEGS M ((PGS.ow_os O) + 272) 16384 -> L5.u64_at RSEGS M ((PGS.ow_os O) + 280) de' -> L5.u64_at RSEGS M ((PGS.ow_os O) + 288) rem' -> qc <= de' -> 0 <= rem' -> de' + rem' <= qc + 16384 -> PM.iss_at RSEGS PMA.AD PMSPA.accA M (PGS.ow_ois O) str (PM.STRM g' eg st') -> g <= g' <= eg -> (sst = 2 -> st' = 2) -> 0 <= d <= k -> (rem + (eg - g)) - (rem' + (eg - g')) = d -> (1 <= rem -> 1 <= d) -> (d = 0 -> rem' = 0 /\ st' = 2) -> L5.defined M p d ->
    srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx R 717356 M model) K.

Definition srd_stA (V : nat -> Z) (R : bvmap 5 word) (M : mem) : Prop :=
  (0 <= (V 1%nat) < 2 ^ 64)
  /\ (0 <= (V 2%nat) < 2 ^ 64)
  /\ (0 <= (V 8%nat) < 2 ^ 64)
  /\ (0 <= (V 9%nat) < 2 ^ 64)
  /\ (0 <= (V 19%nat) < 2 ^ 64)
  /\ (0 <= (V 22%nat) < 2 ^ 64)
  /\ (0 <= (V 27%nat) < 2 ^ 64)
  /\ (0 <= (V 34%nat) < 2 ^ 64)
  /\ (0 <= (V 35%nat) < 2 ^ 64)
  /\ (0 <= (V 36%nat) < 2 ^ 64)
  /\ (0 <= (V 37%nat) < 2 ^ 64)
  /\ (0 <= (V 38%nat) < 2 ^ 64)
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
  /\ (0 <= (V 75%nat) < 2 ^ 64)
  /\ (getr R (reg 1) = Z_to_bv 64 (V 61%nat))
  /\ (getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 160))
  /\ (getr R (reg 5) = Z_to_bv 64 (V 62%nat))
  /\ (getr R (reg 6) = Z_to_bv 64 (V 63%nat))
  /\ (getr R (reg 7) = Z_to_bv 64 (V 64%nat))
  /\ (getr R (reg 8) = Z_to_bv 64 ((V 2%nat) + 16))
  /\ (getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 160))
  /\ (getr R (reg 10) = Z_to_bv 64 (32 * (V 50%nat)))
  /\ (getr R (reg 11) = Z_to_bv 64 (V 65%nat))
  /\ (getr R (reg 12) = Z_to_bv 64 (V 66%nat))
  /\ (getr R (reg 13) = Z_to_bv 64 (V 67%nat))
  /\ (getr R (reg 14) = Z_to_bv 64 (V 68%nat))
  /\ (getr R (reg 15) = Z_to_bv 64 (V 69%nat))
  /\ (getr R (reg 16) = Z_to_bv 64 (V 70%nat))
  /\ (getr R (reg 17) = Z_to_bv 64 (V 71%nat))
  /\ (getr R (reg 19) = Z_to_bv 64 (V 36%nat))
  /\ (getr R (reg 22) = Z_to_bv 64 (V 38%nat))
  /\ (getr R (reg 27) = Z_to_bv 64 2147450880)
  /\ (getr R (reg 28) = Z_to_bv 64 (V 72%nat))
  /\ (getr R (reg 29) = Z_to_bv 64 (V 73%nat))
  /\ (getr R (reg 30) = Z_to_bv 64 (V 74%nat))
  /\ (getr R (reg 31) = Z_to_bv 64 (V 75%nat))
  /\ (L5.img_clear M 65536 1282048)
  /\ (L5.u64_at RSEGS M 1309752 2147450880)
  /\ (L5.u32_at RSEGS M 1309760 1)
  /\ (140735332487232 <= (V 2%nat) <= 140737488355312)
  /\ ((V 2%nat) mod 32 = 0)
  /\ (L5.writable RSEGS M ((V 2%nat) - 160) 176)
  /\ (6905856 <= (V 36%nat) <= 140737488355032)
  /\ ((V 36%nat) mod 8 = 0)
  /\ ((2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 296 <= 2147446784))
  /\ (L5KA.zeros_at M ((((V 36%nat) + 8) / 8) + 2147450880) 36)
  /\ (L5.writable RSEGS M (V 36%nat) 296)
  /\ ((((V 2%nat) - 160) + 176 <= (V 36%nat) \/ (V 36%nat) + 296 <= ((V 2%nat) - 160)))
  /\ (L5.u64_at RSEGS M ((V 36%nat) + 264) (V 34%nat))
  /\ (L5.u64_at RSEGS M ((V 36%nat) + 272) 16384)
  /\ (L5.u64_at RSEGS M ((V 36%nat) + 280) (V 35%nat))
  /\ (L5.defined M ((V 36%nat) + 256) 8)
  /\ (140735332487248 <= (V 2%nat) <= 140737488355328)
  /\ (L5.writable RSEGS M ((V 2%nat) - 160) 160)
  /\ ((((V 2%nat) - 160) + 160 <= (V 36%nat) \/ (V 36%nat) + 296 <= ((V 2%nat) - 160)))
  /\ (L5.u64_at RSEGS M ((V 2%nat) - 136) (V 37%nat))
  /\ (L5.u64_at RSEGS M ((V 2%nat) - 88) (V 27%nat))
  /\ (L5.u64_at RSEGS M ((V 2%nat) - 80) (bv_unsigned (getr R (reg 26))))
  /\ (L5.u64_at RSEGS M ((V 2%nat) - 72) (bv_unsigned (getr R (reg 25))))
  /\ (L5.u64_at RSEGS M ((V 2%nat) - 64) (bv_unsigned (getr R (reg 24))))
  /\ (L5.u64_at RSEGS M ((V 2%nat) - 56) (bv_unsigned (getr R (reg 23))))
  /\ (L5.u64_at RSEGS M ((V 2%nat) - 48) (V 22%nat))
  /\ (L5.u64_at RSEGS M ((V 2%nat) - 40) (bv_unsigned (getr R (reg 21))))
  /\ (L5.u64_at RSEGS M ((V 2%nat) - 32) (bv_unsigned (getr R (reg 20))))
  /\ (L5.u64_at RSEGS M ((V 2%nat) - 24) (V 19%nat))
  /\ (L5.u64_at RSEGS M ((V 2%nat) - 16) (bv_unsigned (getr R (reg 18))))
  /\ (L5.u64_at RSEGS M ((V 2%nat) - 8) (V 9%nat))
  /\ (L5.u64_at RSEGS M (V 2%nat) (V 8%nat))
  /\ (L5.u64_at RSEGS M ((V 2%nat) + 8) (V 1%nat))
  /\ (L5.u64_at RSEGS M ((V 2%nat) - 144) 0)
  /\ (215808 <= (V 50%nat) <= 4398046511102)
  /\ ((V 50%nat) mod 4 = 0)
  /\ (L5.defined M (32 * (V 50%nat)) 128)
  /\ (L5.writable RSEGS M (32 * (V 50%nat)) 128)
  /\ ((2147446784 + 17592186048512 <= (32 * (V 50%nat)) \/ (32 * (V 50%nat)) + 128 <= 2147446784))
  /\ (L5.writable RSEGS M ((4 * (V 50%nat)) + 2147450880) 16)
  /\ (L5.u64_at RSEGS M ((32 * (V 50%nat)) + 120) (V 51%nat))
  /\ (4096 <= (V 51%nat) <= 140737488355327)
  /\ (L5.writable RSEGS M (V 51%nat) 1)
  /\ ((2147446784 + 17592186048512 <= (V 51%nat) \/ (V 51%nat) + 1 <= 2147446784))
  /\ (((32 * (V 50%nat)) + 128 <= (V 51%nat) \/ (V 51%nat) + 1 <= (32 * (V 50%nat))))
  /\ ((((V 2%nat) - 160) + 176 <= (32 * (V 50%nat)) \/ (32 * (V 50%nat)) + 128 <= ((V 2%nat) - 160)))
  /\ ((((V 2%nat) - 160) + 176 <= (V 51%nat) \/ (V 51%nat) + 1 <= ((V 2%nat) - 160)))
  /\ (((32 * (V 50%nat)) + 128 <= ((4 * (V 50%nat)) + 2147450880) \/ ((4 * (V 50%nat)) + 2147450880) + 16 <= (32 * (V 50%nat))))
  /\ (((V 51%nat) + 1 <= ((4 * (V 50%nat)) + 2147450880) \/ ((4 * (V 50%nat)) + 2147450880) + 16 <= (V 51%nat)))
  /\ ((((V 2%nat) - 160) + 176 <= ((4 * (V 50%nat)) + 2147450880) \/ ((4 * (V 50%nat)) + 2147450880) + 16 <= ((V 2%nat) - 160)))
  /\ (((32 * (V 50%nat)) + 128 <= (V 36%nat) \/ (V 36%nat) + 296 <= (32 * (V 50%nat))))
  /\ (((V 51%nat) + 1 <= (V 36%nat) \/ (V 36%nat) + 296 <= (V 51%nat)))
  /\ ((((4 * (V 50%nat)) + 2147450880) + 16 <= (V 36%nat) \/ (V 36%nat) + 296 <= ((4 * (V 50%nat)) + 2147450880)))
  /\ ((((4 * (V 50%nat)) + 2147450880) + 16 <= ((((V 36%nat) + 8) / 8) + 2147450880) \/ ((((V 36%nat) + 8) / 8) + 2147450880) + 36 <= ((4 * (V 50%nat)) + 2147450880)))
  /\ (((32 * (V 50%nat)) + 128 <= ((((V 36%nat) + 8) / 8) + 2147450880) \/ ((((V 36%nat) + 8) / 8) + 2147450880) + 36 <= (32 * (V 50%nat))))
  /\ (((V 51%nat) + 1 <= ((((V 36%nat) + 8) / 8) + 2147450880) \/ ((((V 36%nat) + 8) / 8) + 2147450880) + 36 <= (V 51%nat))).

Definition srd_pG (V : nat -> Z) (R : bvmap 5 word) (M : mem) : Prop :=
  (0 <= (V 33%nat) < 2 ^ 64)
  /\ (L5.u64_at RSEGS M ((V 36%nat) + 288) (V 33%nat))
  /\ (4096 <= (V 35%nat) <= 140737488338944).

Definition srd_pathG (V : nat -> Z) (R : bvmap 5 word) (M : mem) (rem sst : Z) : Prop :=
  V 33%nat = rem /\ 1 <= rem /\ srd_pG V R M.

Definition srd_a0_T (al : Z) (pth : (nat -> Z) -> bvmap 5 word -> mem -> Z -> Z -> Prop) : Prop :=
  forall (O : PGS.owner) (R0 : bvmap 5 word) (M0 : mem) (model0 : Model) (K : TSet) (OB LBX : list (Z * Z))
         (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (sp r : Z) (str : PM.vstr) (Wextra : list L5.range)
         (qc de rem g eg sst p k : Z),
    srd_ctx al O R0 M0 model0 K OB LBX FF LK Aw cr sp r (PM.SRC qc de rem) str (PM.STRM g eg sst) Wextra ->
    getr R0 (reg 11) = Z_to_bv 64 p -> getr R0 (reg 12) = Z_to_bv 64 k ->
    forall (F fl : Z) (LK2 : list fframe) (M2 : mem) (model2 : Model),
    srd_frame al R0 OB LBX FF LK Aw cr sp (PM.SRC qc de rem) F fl LK2 M2 model2 ->
    forall (fx : FPState) (R : bvmap 5 word) (M : mem) (model : Model) (LKc : list fframe) (Ac : list (Z * Z))
           (V : nat -> Z),
    srd_body al O R0 M0 model0 OB LBX FF LK Aw sp (PM.SRC qc de rem) Wextra F M model LKc cr Ac ->
    V 2%nat = sp - al -> V 36%nat = PGS.ow_os O -> V 37%nat = p -> V 38%nat = k -> 32 * V 50%nat = F -> V 51%nat = fl ->
    (forall i, In i [1; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> V i = bv_unsigned (getr R0 (reg i))) ->
    getr R (reg 3) = getr R0 (reg 3) -> getr R (reg 4) = getr R0 (reg 4) ->
    V 34%nat = qc -> V 35%nat = de -> V 45%nat = PGS.ow_ois O ->
    PM.iss_at RSEGS PMA.AD PMSPA.accA M (PGS.ow_ois O) str (PM.STRM g eg sst) ->
    srd_stA V R (mrestrict (ahid Ac model) M) -> pth V R (mrestrict (ahid Ac model) M) rem sst ->
    srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx R 716228 M model) K.

Definition srd_pA0f (V : nat -> Z) (R : bvmap 5 word) (M : mem) : Prop :=
  (L5.u64_at RSEGS M ((V 36%nat) + 288) 0)
  /\ (1 <= (V 38%nat) <= 16383).

Definition srd_pthF (V : nat -> Z) (R : bvmap 5 word) (M : mem) (rem sst : Z) : Prop :=
  rem = 0 /\ srd_pA0f V R M.

Definition srd_post_sm (al : Z) (O : PGS.owner) (R0 : bvmap 5 word) (M0 : mem) (model0 : Model) (K : TSet) (OB LBX : list (Z * Z))
    (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (sp r : Z) (str : PM.vstr) (Wextra : list L5.range)
    (qc de rem g eg sst p k : Z) (F fl : Z) (LK2 : list fframe) (M2 : mem) (model2 : Model)
    (R : bvmap 5 word) (M : mem) (model : Model) (LKc : list fframe) (Ac : list (Z * Z)) (V : nat -> Z) : Prop :=
  srd_ctx al O R0 M0 model0 K OB LBX FF LK Aw cr sp r (PM.SRC qc de rem) str (PM.STRM g eg sst) Wextra /\
  getr R0 (reg 11) = Z_to_bv 64 p /\ getr R0 (reg 12) = Z_to_bv 64 k /\
  srd_frame al R0 OB LBX FF LK Aw cr sp (PM.SRC qc de rem) F fl LK2 M2 model2 /\
  srd_body al O R0 M0 model0 OB LBX FF LK Aw sp (PM.SRC qc de rem) Wextra F M model LKc cr Ac /\
  V 2%nat = sp - al /\ V 36%nat = PGS.ow_os O /\ V 37%nat = p /\ V 38%nat = k /\ 32 * V 50%nat = F /\ V 51%nat = fl /\
  (forall i, In i [1; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> V i = bv_unsigned (getr R0 (reg i))) /\
  getr R (reg 3) = getr R0 (reg 3) /\ getr R (reg 4) = getr R0 (reg 4) /\
  V 34%nat = qc /\ V 35%nat = de /\ V 45%nat = PGS.ow_ois O /\
  PM.iss_at RSEGS PMA.AD PMSPA.accA M (PGS.ow_ois O) str (PM.STRM g eg sst) /\
  srd_stA V R (mrestrict (ahid Ac model) M) /\
  L5.u64_at RSEGS (mrestrict (ahid Ac model) M) (PGS.ow_os O + 288) rem.

Definition srd_entry_body_T (al : Z) : Prop :=
  forall (O : PGS.owner) (R0 : bvmap 5 word) (M0 : mem) (model0 : Model) (K : TSet) (OB LBX : list (Z * Z))
         (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (sp r : Z) (str : PM.vstr) (Wextra : list L5.range)
         (qc de rem g eg sst p k : Z) (F fl : Z) (LK2 : list fframe) (M2 : mem) (model2 : Model)
         (fx : FPState) (R : bvmap 5 word) (M : mem) (model : Model) (LKc : list fframe) (Ac : list (Z * Z)) (V : nat -> Z),
    srd_post_sm al O R0 M0 model0 K OB LBX FF LK Aw cr sp r str Wextra qc de rem g eg sst p k F fl LK2 M2 model2 R M model LKc Ac V ->
    srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx R 716228 M model) K.

End WithHeap.

Section Exit.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Variable IL : icpt_layout.
Hypothesis ICok : aicpt_ok L ar IL SCFG HI.
Hypothesis ILY : as0_icpt_layout IL.
Let LYa := PMA.ly_as0 L C LY.
Ltac pdestr PP := repeat match type of PP with _ /\ _ => let H := fresh "S" in destruct PP as (H & PP) end.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).

Lemma srd_exit_ok : srd_exit_T L ar HI 16.
Proof.
  unfold srd_exit_T.
  intros O R M model K OB LBX FF LK Aw cr sp r str Wextra qc de rem g eg sst pb kb CTX R11 R12
         F fl LK2 M2 model2 G fxc Rc Mc modelc LKc Ac V BD XV2 XV36 XV37 XV38 XV50 XV51 XVS XR3 XR4
         deX remX gX stX d ST VD XC264 XC272 XC280 XC288 XQ1 XQ2 XQ3 XIA3 XHg XHst2 XHd XHcons XHR1 XHR0 XDD3.
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
  { unfold srd_stR in ST. pdestr ST.
    rewrite A11 in R11. rewrite A12 in R12. apply (f_equal bv_unsigned) in R11, R12.
    rewrite !L5.unsigned_lit in R11, R12 by (first [clear - DP0 DP1 Hk; lia | rewrite <- XV37; assumption | rewrite <- XV38; assumption]).
    split; congruence. }
  destruct pbk as (pbp & kbk). rewrite pbp in *. rewrite kbk in *. clear pbp kbk.
  unfold srd_frame in G. unfold srd_body in BD.
  set (MVc := mrestrict (ahid Ac modelc) Mc) in *.
  unfold srd_stR in ST. pdestr ST.
  assert (DJ1 : 32 * V 50%nat + 128 <= V 36%nat \/ V 36%nat + 296 <= 32 * V 50%nat) by assumption.
  assert (DJ2 : V 51%nat + 1 <= V 36%nat \/ V 36%nat + 296 <= V 51%nat) by assumption.
  assert (DJ3 : 4 * V 50%nat + SB + 16 <= V 36%nat \/ V 36%nat + 296 <= 4 * V 50%nat + SB) by (unfold SB; assumption).
  LeanFeed.pfeed P (PMASRP.asrR16_conc fxc Rc MVc V) ltac:(assumption).
  destruct P as (fx1 & R1 & M1v & MG1 & FRZa & FRZ1 & MS1 & KS1 & T1 & T2 & T8 & T9 & T10 & T18 & T19 & T20 & T21 & T22 & T23 & T24 & T25 & T26 & T27 & FL0).
  assert (RV : forall i, In i [1; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> Z_to_bv 64 (V i) = getr R (reg i)).
  { intros i Hi. rewrite (XVS i Hi). apply Z_to_bv_bv_unsigned. }
  assert (R1ra : getr R1 (reg 1) = Z_to_bv 64 r) by (rewrite T1, (RV 1%nat) by inl; exact Rra).
  pose proof (PMK.ret_to RSEGS fx1 R1 M1v 717568 W_addcc r F_addcc eq_refl D_addcc R1ra Hr1 Hr2) as MSr.
  pose proof BD as BD'. unfold PMAUK.binv in BD'. destruct BD' as (HHc & AMc & MRTc & INCAc & INCLc & ASTKc & EKc & DKc & OWNc & DSHc).
  apply (PMAUK.retire_coreW L ar C HI LYa HIok M model LB FF LK Aw sp _ _ _ _ _ _ F fl 1 LK2 M2 model2 cr [] G
           _ [] Mc modelc LKc cr Ac (fun _ => False) fxc fx1 Rc 717356 R1 r M1v K BD).
  { intros a []. }
  { intros a. right. intros []. }
  { exact (msteps_trans _ _ _ _ MS1 MSr). }
  { exact MG1. }
  { intros a Ha NW. apply FRZ1; [exact Ha| | |]; intros X; apply NW; unfold PMAUK.WretX, PMAUK.Wret; change (ff_bytes 1) with 128.
    - left; left; left. clear - X XV50; lia.
    - left; left; right. unfold SB. clear - X XV50; lia.
    - left; right. clear - X XV51; lia. }
  { rewrite <- XV51. exact FL0. }
  intros Mf modelf FZf MGf VISf AHf MRTf AMf HHf.
  assert (FZc : forall a, 0 <= a < 2 ^ 64 -> ~ (F <= a < F + 8) -> ~ (F / 8 + SB <= a < F / 8 + SB + 16) -> a <> fl ->
                Mf (Z_to_bv 64 a) = Mc (Z_to_bv 64 a)).
  { intros a Ha N1 N2 N3. apply FZf; [exact Ha|]. unfold PMAUK.WretX, PMAUK.Wret. change (ff_bytes 1) with 128.
    intros [[[X|X]|X]|[]]; [exact (N1 X)| apply N2; clear - X; lia| exact (N3 X)]. }
  assert (CO : forall a v, os <= a -> a + 8 <= os + 296 -> L5.u64_at RSEGS Mc a v -> L5.u64_at RSEGS Mf a v).
  { intros a v Ha Hb X. apply (L5C.u64_at_agree RSEGS Mc Mf); [| clear - Ha O1; lia| clear - Hb O1; lia| exact X].
    intros i Hi. apply FZc.
    - clear - Hi Ha Hb O1; lia.
    - intros Y. clear - Y Hi Ha Hb DJ1 XV50 XV36. lia.
    - intros Y. clear - Y Hi Ha Hb DJ3 XV50 XV36. lia.
    - intros Y. clear - Y Hi Ha Hb DJ2 XV51 XV36. lia. }
  assert (EKf : L5SAR.ek L ar LB FF 0 0 [] Mc Mf).
  { apply (PMAUAR.wret_ek L ar C HI LY HIok LB FF LK Aw sp _ _ _ _ _ _ F fl 1 LK2 M2 model2 cr [] ([] ++ LB) LKc cr Ac Mc Mf _
             [] (fun _ => False) G HHc).
    - intros a [].
    - exact FZf. }
  assert (IAf : PM.iss_at RSEGS PMA.AD PMSPA.accA Mf ois str (PM.STRM gX eg stX)).
  { apply (PMKA.iss_keepA RSEGS PMA.AD L ar LB FF 0 0 [] Mc Mf EKf PMKA.wapp_nil FRB BRB ois str (PM.STRM gX eg stX) AOI SOWN).
    - intros i _ rr [].
    - intros c0 n0 p0 _ i _ rr [].
    - exact XIA3. }
  assert (PAf : PGS.ow_at O Mf (PM.SRC qc deX remX) OB).
  { apply (OWU Mf deX remX AHf).
    - apply CO; [clear; lia| clear; lia| exact XC264].
    - apply CO; [clear; lia| clear; lia| exact XC272].
    - apply CO; [clear; lia| clear; lia| exact XC280].
    - apply CO; [clear; lia| clear; lia| exact XC288].
    - exact XQ1.
    - exact XQ2.
    - exact XQ3. }
  assert (E10 : getr R1 (reg 10) = Z_to_bv 64 d) by (rewrite T10, VD; reflexivity).
  assert (DDf : L5.defined Mf p d) by exact (L5.defined_grows Mc Mf p d MGf XDD3).
  apply (KONT fx1 R1 Mf modelf LKc Ac (PM.SRC qc deX remX) (PM.STRM gX eg stX)).
  - apply L5SAR.preserved_by_index. intros j Hj. unfold L5SAR.cs_all in Hj.
    destruct Hj as [<-|[<-|[<-|Hj]]].
    + rewrite T2, Rsp, XV2. f_equal. clear; lia.
    + rewrite (KS1 3%nat) by inl. exact XR3.
    + rewrite (KS1 4%nat) by inl. exact XR4.
    + repeat (destruct Hj as [<-|Hj]; [first [rewrite T8 | rewrite T9 | rewrite T18 | rewrite T19 | rewrite T20 | rewrite T21 | rewrite T22
                                             | rewrite T23 | rewrite T24 | rewrite T25 | rewrite T26 | rewrite T27]; apply RV; inl|]).
      destruct Hj.
  - exact PAf.
  - exact IAf.
  - unfold PMSP.src_step, PM.unread. cbn [PM.sr_qc PM.sr_rem PM.sm_eg PM.sm_g PM.sm_st]. split; [reflexivity|]. split; [reflexivity|].
    split; [clear - XHg; lia|]. split; [exact XHst2| clear - XHcons XHd; lia].
  - unfold PMPS.read_res, PMSP.consumed, PM.unread. cbn [PM.sr_rem PM.sm_eg PM.sm_g PM.sm_st]. exists p, k, d.
    rewrite L5SAR.r11, L5SAR.r12, L5K.rl10. split; [exact A11|]. split; [exact A12|]. split; [clear - DP0 DP1 Hk; lia|].
    split; [unfold PM.CHUNK; clear - Hk; lia|].
    split; [exact E10|]. split; [exact XHd|]. split; [exact XHcons|]. split; [exact DDf|]. split; [exact XHR1| exact XHR0].
  - exact AHf.
  - exact MRTf.
  - exact INCLc.
  - exact INCAc.
  - exact AMf.
  - exact HHf.
Qed.

End Exit.

End PGSRDK16.
