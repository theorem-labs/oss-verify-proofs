(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnASrcKit_b PgSrcKitA_b PnASrcRead1_b PnASrcReadK_b PnASrcReadP_b Ba0PgSrcReadK_b Ba0PgSrcReadC_b.
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

Module PGSRDMT.
Abbreviation RSEGS := PGSRDK.RSEGS.
Abbreviation mem := (word -> option byte).
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).

Section WithHeap.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).

Definition srd_mc_args_T (al : Z) : Prop :=
  forall (O : PGS.owner) (R0 : bvmap 5 word) (M0 : mem) (model0 : Model) (K : TSet) (OB LBX : list (Z * Z))
         (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (sp r : Z) (str : PM.vstr) (Wextra : list L5.range)
         (qc de rem g eg sst p k : Z),
    PGSRDK.srd_ctx L ar HI al O R0 M0 model0 K OB LBX FF LK Aw cr sp r (PM.SRC qc de rem) str (PM.STRM g eg sst) Wextra ->
    getr R0 (reg 11) = Z_to_bv 64 p -> getr R0 (reg 12) = Z_to_bv 64 k ->
    0 <= p < 2 ^ 64 -> 0 <= k < 2 ^ 64 ->
    forall (F fl : Z) (LK2 : list fframe) (M2 : mem) (model2 : Model),
    PGSRDK.srd_frame L ar HI al R0 OB LBX FF LK Aw cr sp (PM.SRC qc de rem) F fl LK2 M2 model2 ->

    forall (M1 : mem) (model1 : Model) (LKc : list fframe) (Ac : list (Z * Z)) (len1 : Z),
    PGSRDK.srd_body L ar HI al O R0 M0 model0 OB LBX FF LK Aw sp (PM.SRC qc de rem) Wextra F M1 model1 LKc cr Ac ->
    len1 = Z.min k rem ->
    aacc M1 p len1
     /\ L5.defined M1 p len1
     /\ 0 <= p
     /\ p + len1 <= 2 ^ 47
     /\ app_rng ar p len1
     /\ (forall i, 0 <= i < len1 -> in_block (PM.src_own (PM.SRC qc de rem) ++ OB ++ LBX) (p + i) \/ in_fframe FF (p + i))
     /\ (forall i, 0 <= i < len1 -> ~ (sp - PMSPA.pm_scr 4 <= p + i < sp) /\
           ~ L5.outside (PGS.W_srcG (PGS.ow_os O) (PGS.ow_ois O) (PM.SRC qc de rem) ++ Wextra) (p + i))
     /\ aacc M1 de len1
     /\ L5.defined M1 de len1
     /\ 0 <= de
     /\ de + len1 <= 2 ^ 47
     /\ app_rng ar de len1
     /\ (forall i, 0 <= i < len1 -> in_block (PM.src_own (PM.SRC qc de rem) ++ OB ++ LBX) (de + i))
     /\ (p + len1 <= de \/ de + len1 <= p)
     /\ 0 <= len1 <= PM.CHUNK
     /\ (forall i, p <= i < p + len1 ->
         ~ ((sp - 160 - al <= i < sp) \/ (F <= i < F + 128) \/ (F / 8 + SB <= i < F / 8 + SB + 16)
            \/ (PGS.ow_os O <= i < PGS.ow_os O + 296) \/ ((PGS.ow_os O + 8) / 8 + SB <= i < (PGS.ow_os O + 8) / 8 + SB + 36))).

Definition srd_mc_keep_T (al : Z) : Prop :=
  forall (O : PGS.owner) (R0 : bvmap 5 word) (M0 : mem) (model0 : Model) (K : TSet) (OB LBX : list (Z * Z))
         (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (sp r : Z) (str : PM.vstr) (Wextra : list L5.range)
         (qc de rem g eg sst p k : Z),
    PGSRDK.srd_ctx L ar HI al O R0 M0 model0 K OB LBX FF LK Aw cr sp r (PM.SRC qc de rem) str (PM.STRM g eg sst) Wextra ->
    getr R0 (reg 11) = Z_to_bv 64 p -> getr R0 (reg 12) = Z_to_bv 64 k ->
    0 <= p < 2 ^ 64 -> 0 <= k < 2 ^ 64 ->
    forall (F fl : Z) (LK2 : list fframe) (M2 : mem) (model2 : Model),
    PGSRDK.srd_frame L ar HI al R0 OB LBX FF LK Aw cr sp (PM.SRC qc de rem) F fl LK2 M2 model2 ->

    forall (M : mem) (model : Model) (LKc : list fframe) (Ac : list (Z * Z)),
    PGSRDK.srd_body L ar HI al O R0 M0 model0 OB LBX FF LK Aw sp (PM.SRC qc de rem) Wextra F M model LKc cr Ac ->
    PM.iss_at RSEGS PMA.AD PMSPA.accA M (PGS.ow_ois O) str (PM.STRM g eg sst) ->
    forall (len1 : Z) (M1 : mem) (model1 : Model) (M3 : mem) (model3 : Model),
    len1 = Z.min k rem ->
    PGSRDK.srd_body L ar HI al O R0 M0 model0 OB LBX FF LK Aw sp (PM.SRC qc de rem) Wextra F M1 model1 LKc cr Ac ->
    L5SAR.ek L ar (PM.src_own (PM.SRC qc de rem) ++ OB ++ LBX) FF sp (PMSPA.pm_scr 4) [(PGS.ow_os O + 256, 40)] M M1 ->
    L5.u64_at RSEGS (mrestrict (ahid Ac model) M) (PGS.ow_os O + 264) qc ->
    L5.u64_at RSEGS (mrestrict (ahid Ac model) M) (PGS.ow_os O + 272) 16384 ->
    L5.u64_at RSEGS (mrestrict (ahid Ac model) M) (PGS.ow_os O + 280) de ->
    L5.u64_at RSEGS (mrestrict (ahid Ac model) M) (PGS.ow_os O + 288) rem ->
    (forall i, 0 <= i < 2 ^ 64 ->
      ~ ((sp - 160 - al <= i < sp - 104 - al) \/ (F <= i < F + 128) \/ (F / 8 + SB <= i < F / 8 + SB + 16)) ->
      M1 (Z_to_bv 64 i) = M (Z_to_bv 64 i)) ->
    PGSRDK.srd_body L ar HI al O R0 M0 model0 OB LBX FF LK Aw sp (PM.SRC qc de rem) Wextra F M3 model3 LKc cr Ac ->
    L5CA.ahpres L ar ([] ++ (PM.src_own (PM.SRC qc de rem) ++ OB ++ LBX)) ((F, 1, sp - 160 - al + 32) :: FF) (sp - 160 - al) 2560 [(p, len1)] M1 M3 ->
    PGS.ow_at O M3 (PM.SRC qc de rem) OB /\ PM.iss_at RSEGS PMA.AD PMSPA.accA M3 (PGS.ow_ois O) str (PM.STRM g eg sst) /\ PMSTA.base_okA RSEGS PMA.AD M3.

Definition srd_mc_keep_ow_T (al : Z) : Prop :=
  forall (O : PGS.owner) (R0 : bvmap 5 word) (M0 : mem) (model0 : Model) (K : TSet) (OB LBX : list (Z * Z))
         (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (sp r : Z) (str : PM.vstr) (Wextra : list L5.range)
         (qc de rem g eg sst p k : Z),
    PGSRDK.srd_ctx L ar HI al O R0 M0 model0 K OB LBX FF LK Aw cr sp r (PM.SRC qc de rem) str (PM.STRM g eg sst) Wextra ->
    getr R0 (reg 11) = Z_to_bv 64 p -> getr R0 (reg 12) = Z_to_bv 64 k ->
    0 <= p < 2 ^ 64 -> 0 <= k < 2 ^ 64 ->
    forall (F fl : Z) (LK2 : list fframe) (M2 : mem) (model2 : Model),
    PGSRDK.srd_frame L ar HI al R0 OB LBX FF LK Aw cr sp (PM.SRC qc de rem) F fl LK2 M2 model2 ->

    forall (M : mem) (model : Model) (LKc : list fframe) (Ac : list (Z * Z)),
    PGSRDK.srd_body L ar HI al O R0 M0 model0 OB LBX FF LK Aw sp (PM.SRC qc de rem) Wextra F M model LKc cr Ac ->
    PM.iss_at RSEGS PMA.AD PMSPA.accA M (PGS.ow_ois O) str (PM.STRM g eg sst) ->
    forall (len1 : Z) (M1 : mem) (model1 : Model) (M3 : mem) (model3 : Model),
    len1 = Z.min k rem ->
    PGSRDK.srd_body L ar HI al O R0 M0 model0 OB LBX FF LK Aw sp (PM.SRC qc de rem) Wextra F M1 model1 LKc cr Ac ->
    L5SAR.ek L ar (PM.src_own (PM.SRC qc de rem) ++ OB ++ LBX) FF sp (PMSPA.pm_scr 4) [(PGS.ow_os O + 256, 40)] M M1 ->
    L5.u64_at RSEGS (mrestrict (ahid Ac model) M) (PGS.ow_os O + 264) qc ->
    L5.u64_at RSEGS (mrestrict (ahid Ac model) M) (PGS.ow_os O + 272) 16384 ->
    L5.u64_at RSEGS (mrestrict (ahid Ac model) M) (PGS.ow_os O + 280) de ->
    L5.u64_at RSEGS (mrestrict (ahid Ac model) M) (PGS.ow_os O + 288) rem ->
    (forall i, 0 <= i < 2 ^ 64 ->
      ~ ((sp - 160 - al <= i < sp - 104 - al) \/ (F <= i < F + 128) \/ (F / 8 + SB <= i < F / 8 + SB + 16)) ->
      M1 (Z_to_bv 64 i) = M (Z_to_bv 64 i)) ->
    PGSRDK.srd_body L ar HI al O R0 M0 model0 OB LBX FF LK Aw sp (PM.SRC qc de rem) Wextra F M3 model3 LKc cr Ac ->
    L5CA.ahpres L ar ([] ++ (PM.src_own (PM.SRC qc de rem) ++ OB ++ LBX)) ((F, 1, sp - 160 - al + 32) :: FF) (sp - 160 - al) 2560 [(p, len1)] M1 M3 ->
    PGS.ow_at O M3 (PM.SRC qc de rem) OB.

Definition srd_mc_keep_iss_T (al : Z) : Prop :=
  forall (O : PGS.owner) (R0 : bvmap 5 word) (M0 : mem) (model0 : Model) (K : TSet) (OB LBX : list (Z * Z))
         (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (sp r : Z) (str : PM.vstr) (Wextra : list L5.range)
         (qc de rem g eg sst p k : Z),
    PGSRDK.srd_ctx L ar HI al O R0 M0 model0 K OB LBX FF LK Aw cr sp r (PM.SRC qc de rem) str (PM.STRM g eg sst) Wextra ->
    getr R0 (reg 11) = Z_to_bv 64 p -> getr R0 (reg 12) = Z_to_bv 64 k ->
    0 <= p < 2 ^ 64 -> 0 <= k < 2 ^ 64 ->
    forall (F fl : Z) (LK2 : list fframe) (M2 : mem) (model2 : Model),
    PGSRDK.srd_frame L ar HI al R0 OB LBX FF LK Aw cr sp (PM.SRC qc de rem) F fl LK2 M2 model2 ->

    forall (M : mem) (model : Model) (LKc : list fframe) (Ac : list (Z * Z)),
    PGSRDK.srd_body L ar HI al O R0 M0 model0 OB LBX FF LK Aw sp (PM.SRC qc de rem) Wextra F M model LKc cr Ac ->
    PM.iss_at RSEGS PMA.AD PMSPA.accA M (PGS.ow_ois O) str (PM.STRM g eg sst) ->
    forall (len1 : Z) (M1 : mem) (model1 : Model) (M3 : mem) (model3 : Model),
    len1 = Z.min k rem ->
    PGSRDK.srd_body L ar HI al O R0 M0 model0 OB LBX FF LK Aw sp (PM.SRC qc de rem) Wextra F M1 model1 LKc cr Ac ->
    L5SAR.ek L ar (PM.src_own (PM.SRC qc de rem) ++ OB ++ LBX) FF sp (PMSPA.pm_scr 4) [(PGS.ow_os O + 256, 40)] M M1 ->
    L5.u64_at RSEGS (mrestrict (ahid Ac model) M) (PGS.ow_os O + 264) qc ->
    L5.u64_at RSEGS (mrestrict (ahid Ac model) M) (PGS.ow_os O + 272) 16384 ->
    L5.u64_at RSEGS (mrestrict (ahid Ac model) M) (PGS.ow_os O + 280) de ->
    L5.u64_at RSEGS (mrestrict (ahid Ac model) M) (PGS.ow_os O + 288) rem ->
    (forall i, 0 <= i < 2 ^ 64 ->
      ~ ((sp - 160 - al <= i < sp - 104 - al) \/ (F <= i < F + 128) \/ (F / 8 + SB <= i < F / 8 + SB + 16)) ->
      M1 (Z_to_bv 64 i) = M (Z_to_bv 64 i)) ->
    PGSRDK.srd_body L ar HI al O R0 M0 model0 OB LBX FF LK Aw sp (PM.SRC qc de rem) Wextra F M3 model3 LKc cr Ac ->
    L5CA.ahpres L ar ([] ++ (PM.src_own (PM.SRC qc de rem) ++ OB ++ LBX)) ((F, 1, sp - 160 - al + 32) :: FF) (sp - 160 - al) 2560 [(p, len1)] M1 M3 ->
    PM.iss_at RSEGS PMA.AD PMSPA.accA M3 (PGS.ow_ois O) str (PM.STRM g eg sst).

Definition srd_mc_keep_base_T (al : Z) : Prop :=
  forall (O : PGS.owner) (R0 : bvmap 5 word) (M0 : mem) (model0 : Model) (K : TSet) (OB LBX : list (Z * Z))
         (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (sp r : Z) (str : PM.vstr) (Wextra : list L5.range)
         (qc de rem g eg sst p k : Z),
    PGSRDK.srd_ctx L ar HI al O R0 M0 model0 K OB LBX FF LK Aw cr sp r (PM.SRC qc de rem) str (PM.STRM g eg sst) Wextra ->
    getr R0 (reg 11) = Z_to_bv 64 p -> getr R0 (reg 12) = Z_to_bv 64 k ->
    0 <= p < 2 ^ 64 -> 0 <= k < 2 ^ 64 ->
    forall (F fl : Z) (LK2 : list fframe) (M2 : mem) (model2 : Model),
    PGSRDK.srd_frame L ar HI al R0 OB LBX FF LK Aw cr sp (PM.SRC qc de rem) F fl LK2 M2 model2 ->

    forall (M : mem) (model : Model) (LKc : list fframe) (Ac : list (Z * Z)),
    PGSRDK.srd_body L ar HI al O R0 M0 model0 OB LBX FF LK Aw sp (PM.SRC qc de rem) Wextra F M model LKc cr Ac ->
    PM.iss_at RSEGS PMA.AD PMSPA.accA M (PGS.ow_ois O) str (PM.STRM g eg sst) ->
    forall (len1 : Z) (M1 : mem) (model1 : Model) (M3 : mem) (model3 : Model),
    len1 = Z.min k rem ->
    PGSRDK.srd_body L ar HI al O R0 M0 model0 OB LBX FF LK Aw sp (PM.SRC qc de rem) Wextra F M1 model1 LKc cr Ac ->
    L5SAR.ek L ar (PM.src_own (PM.SRC qc de rem) ++ OB ++ LBX) FF sp (PMSPA.pm_scr 4) [(PGS.ow_os O + 256, 40)] M M1 ->
    L5.u64_at RSEGS (mrestrict (ahid Ac model) M) (PGS.ow_os O + 264) qc ->
    L5.u64_at RSEGS (mrestrict (ahid Ac model) M) (PGS.ow_os O + 272) 16384 ->
    L5.u64_at RSEGS (mrestrict (ahid Ac model) M) (PGS.ow_os O + 280) de ->
    L5.u64_at RSEGS (mrestrict (ahid Ac model) M) (PGS.ow_os O + 288) rem ->
    (forall i, 0 <= i < 2 ^ 64 ->
      ~ ((sp - 160 - al <= i < sp - 104 - al) \/ (F <= i < F + 128) \/ (F / 8 + SB <= i < F / 8 + SB + 16)) ->
      M1 (Z_to_bv 64 i) = M (Z_to_bv 64 i)) ->
    PGSRDK.srd_body L ar HI al O R0 M0 model0 OB LBX FF LK Aw sp (PM.SRC qc de rem) Wextra F M3 model3 LKc cr Ac ->
    L5CA.ahpres L ar ([] ++ (PM.src_own (PM.SRC qc de rem) ++ OB ++ LBX)) ((F, 1, sp - 160 - al + 32) :: FF) (sp - 160 - al) 2560 [(p, len1)] M1 M3 ->
    PMSTA.base_okA RSEGS PMA.AD M3.

Lemma srd_mc_keep_of_split al : srd_mc_keep_ow_T al -> srd_mc_keep_iss_T al -> srd_mc_keep_base_T al -> srd_mc_keep_T al.
Proof.
  intros OW IS BA O R0 M0 model0 K OB LBX FF LK Aw cr sp r str Wextra qc de rem g eg sst p k H1 H2 H3 H4 H5 F fl LK2 M2 model2 H6 M model LKc Ac H7 H8 len1 M1 model1 M3 model3 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18.
  split; [exact (OW O R0 M0 model0 K OB LBX FF LK Aw cr sp r str Wextra qc de rem g eg sst p k H1 H2 H3 H4 H5 F fl LK2 M2 model2 H6 M model LKc Ac H7 H8 len1 M1 model1 M3 model3 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18)| split; [exact (IS O R0 M0 model0 K OB LBX FF LK Aw cr sp r str Wextra qc de rem g eg sst p k H1 H2 H3 H4 H5 F fl LK2 M2 model2 H6 M model LKc Ac H7 H8 len1 M1 model1 M3 model3 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18)| exact (BA O R0 M0 model0 K OB LBX FF LK Aw cr sp r str Wextra qc de rem g eg sst p k H1 H2 H3 H4 H5 F fl LK2 M2 model2 H6 M model LKc Ac H7 H8 len1 M1 model1 M3 model3 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18)]].
Qed.

Definition srd_mc_ow_cells_T (al : Z) : Prop :=
  forall (O : PGS.owner) (R0 : bvmap 5 word) (M0 : mem) (model0 : Model) (K : TSet) (OB LBX : list (Z * Z))
         (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (sp r : Z) (str : PM.vstr) (Wextra : list L5.range)
         (qc de rem g eg sst p k : Z),
    PGSRDK.srd_ctx L ar HI al O R0 M0 model0 K OB LBX FF LK Aw cr sp r (PM.SRC qc de rem) str (PM.STRM g eg sst) Wextra ->
    getr R0 (reg 11) = Z_to_bv 64 p -> getr R0 (reg 12) = Z_to_bv 64 k ->
    0 <= p < 2 ^ 64 -> 0 <= k < 2 ^ 64 ->
    forall (F fl : Z) (LK2 : list fframe) (M2 : mem) (model2 : Model),
    PGSRDK.srd_frame L ar HI al R0 OB LBX FF LK Aw cr sp (PM.SRC qc de rem) F fl LK2 M2 model2 ->

    forall (M : mem) (model : Model) (LKc : list fframe) (Ac : list (Z * Z)),
    PGSRDK.srd_body L ar HI al O R0 M0 model0 OB LBX FF LK Aw sp (PM.SRC qc de rem) Wextra F M model LKc cr Ac ->
    PM.iss_at RSEGS PMA.AD PMSPA.accA M (PGS.ow_ois O) str (PM.STRM g eg sst) ->
    forall (len1 : Z) (M1 : mem) (model1 : Model) (M3 : mem) (model3 : Model),
    len1 = Z.min k rem ->
    PGSRDK.srd_body L ar HI al O R0 M0 model0 OB LBX FF LK Aw sp (PM.SRC qc de rem) Wextra F M1 model1 LKc cr Ac ->
    L5SAR.ek L ar (PM.src_own (PM.SRC qc de rem) ++ OB ++ LBX) FF sp (PMSPA.pm_scr 4) [(PGS.ow_os O + 256, 40)] M M1 ->
    L5.u64_at RSEGS (mrestrict (ahid Ac model) M) (PGS.ow_os O + 264) qc ->
    L5.u64_at RSEGS (mrestrict (ahid Ac model) M) (PGS.ow_os O + 272) 16384 ->
    L5.u64_at RSEGS (mrestrict (ahid Ac model) M) (PGS.ow_os O + 280) de ->
    L5.u64_at RSEGS (mrestrict (ahid Ac model) M) (PGS.ow_os O + 288) rem ->
    (forall i, 0 <= i < 2 ^ 64 ->
      ~ ((sp - 160 - al <= i < sp - 104 - al) \/ (F <= i < F + 128) \/ (F / 8 + SB <= i < F / 8 + SB + 16)) ->
      M1 (Z_to_bv 64 i) = M (Z_to_bv 64 i)) ->
    PGSRDK.srd_body L ar HI al O R0 M0 model0 OB LBX FF LK Aw sp (PM.SRC qc de rem) Wextra F M3 model3 LKc cr Ac ->
    L5CA.ahpres L ar ([] ++ (PM.src_own (PM.SRC qc de rem) ++ OB ++ LBX)) ((F, 1, sp - 160 - al + 32) :: FF) (sp - 160 - al) 2560 [(p, len1)] M1 M3 ->
    L5.u64_at RSEGS M3 (PGS.ow_os O + 264) qc /\ L5.u64_at RSEGS M3 (PGS.ow_os O + 272) 16384
    /\ L5.u64_at RSEGS M3 (PGS.ow_os O + 280) de /\ L5.u64_at RSEGS M3 (PGS.ow_os O + 288) rem.

End WithHeap.
Section MT.
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

Lemma srd_mc_args_ok : srd_mc_args_T L ar HI 0.
Proof using All.
  unfold srd_mc_args_T.
  intros O R M model K OB LBX FF LK Aw cr sp r str Wextra qc de rem g eg sst pb kb CTX R11 R12 HPB HKB
         F fl LK2 M2 model2 G M1 model1 LKc Ac len1 BD Hl.
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
  assert (Epb : pb = p).
  { rewrite A11 in R11. apply (f_equal bv_unsigned) in R11. rewrite !L5.unsigned_lit in R11 by (clear - HPB DP0 DP1 Hk; lia). symmetry; exact R11. }
  assert (Ekb : kb = k).
  { rewrite A12 in R12. apply (f_equal bv_unsigned) in R12. rewrite !L5.unsigned_lit in R12 by (clear - HKB Hk; lia). symmetry; exact R12. }
  subst pb kb.
  unfold PGSRDK.srd_body in BD. destruct BD as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10).
  pose proof G as G'. unfold PGSRDK.srd_frame in G'.
  destruct G' as [Hg SPTg SLOg SHIg SPCg OCRg OWNg FS1g FS2g FCEILg LKI2g FLPg FLNCg HH2g FLCg FRg F8g FBIGg F32g FLAg FLRg FLBIGg NCFg NCSg].
  change (ff_bytes 1) with 128 in *.
  assert (L1R : 0 <= len1 <= k /\ len1 <= rem) by (rewrite Hl; clear - Hk G2; lia).
  assert (AGP : PMFA.agsh M M1 p k).
  { destruct DLOC as [AOD|(q & m & Hq & X1 & X2)].
    - exact (PMKA.agsh_obj L ar LB FF sp 20480 WA M M1 B7 WAPP FRB p k AOD).
    - destruct (WB _ Hq) as ((T0 & _ & _ & _ & T4 & _) & _). cbn [fst snd] in T0, T4.
      apply (PMFA.agsh_sub M M1 q m p k); [apply (PMASK.agsh_blk L ar LB FF sp 20480 WA M M1 q m B7 WAPP Hq); clear - T0 T4 SLO SHI SPT; lia| clear - X1; lia| clear - X2; lia]. }
  assert (AGQ : PMFA.agsh M M1 qc 16384).
  { apply (PMASK.agsh_blk L ar LB FF sp 20480 WA M M1 qc 16384 B7 WAPP QIN); clear - Q0 Q4 SLO SHI SPT; lia. }
  assert (CLP : forall i, 0 <= i < len1 -> aclient L ar LB FF sp 20480 (p + i)).
  { intros i Hi. apply PMASR1.cl_of_bf. apply DCL. clear - Hi L1R; lia. }
  split.
  { intros a Ha. apply (PMFA.accA_agree M M1 p k AGP DAP a). clear - Ha L1R; lia. }
  split.
  { apply (PMASK.defined_dk L ar LB FF sp 20480 M M1 p len1 B8); [| clear - DP0; lia| clear - DP1 L1R; lia|].
    - intros i Hi. apply PMASR1.cl_of_bf. apply DCL. clear - Hi L1R; lia.
    - intros i Hi. apply DDP. clear - Hi L1R; lia. }
  split; [clear - DP0; lia|]. split; [clear - DP1 L1R; lia|].
  split; [unfold app_rng in DAPP |- *; clear - DAPP L1R; lia|].
  split; [intros i Hi; apply DCL; clear - Hi L1R; lia|].
  split.
  { intros i Hi. split.
    - destruct (DX (p + i) ltac:(clear - Hi L1R; lia)) as (X1 & _). exact X1.
    - intros OUT. apply (OUT (p, k)); [apply in_or_app; right; left; reflexivity| unfold L5.in_rng; cbn [fst snd]; clear - Hi L1R; lia]. }
  split.
  { intros a Ha. apply (PMFA.accA_agree M M1 qc 16384 AGQ ACH a). clear - Ha G1 G3 L1R; lia. }
  split.
  { apply (PMASK.defined_dk L ar LB FF sp 20480 M M1 de len1 B8); [| clear - Q0 G1; lia| clear - Q4 G1 G3 L1R SLO SHI SPT; lia|].
    - intros i Hi. apply PMASR1.cl_of_bf. left. apply (PMASR1.in_block_of LB qc 16384 i QIN). clear - Hi G1 G3 L1R; lia.
    - intros i Hi. replace (de + i) with (qc + (de - qc + i)) by (clear; lia). apply DCH. clear - Hi G1 G3 L1R; lia. }
  split; [clear - Q0 G1; lia|]. split; [clear - Q4 G1 G3 L1R SLO SHI SPT; lia|].
  split; [apply (L5SAR.app_rng_block L ar C HI HIok LB FF LK cr Aw M _ qc 16384 de len1 HH QIN); clear - G1 G3 L1R; lia|].
  split; [intros i Hi; apply (PMASR1.in_block_of LB qc 16384 (de + i) QIN); clear - Hi G1 G3 L1R; lia|].
  split; [clear - DQA G1 G3 L1R; lia|].
  split; [unfold PM.CHUNK; clear - L1R Hk; lia|].
  intros i Hi Hr.
  assert (CLi : aclient L ar LB FF sp 20480 i) by (apply PMASR1.cl_of_bf; apply DCL; clear - Hi L1R; lia).
  destruct (DX i ltac:(clear - Hi L1R; lia)) as (X1 & _ & X3 & _).
  destruct Hr as [Y|[Y|[Y|[Y|Y]]]].
  - apply X1. clear - Y; lia.
  - exact (NCFg i (or_introl Y) CLi).
  - apply (NCFg i); [right; unfold HeapIfaceA.S, HeapIfaceA.SB in *; clear - Y F32g; lia| exact CLi].
  - apply X3. exact Y.
  - unfold BIGSHADOW_LO, BIGSHADOW_HI in DSH. unfold SB in Y. clear - Y DSH O1 Hi L1R. lia.
Qed.

Lemma srd_mc_ow_cells : srd_mc_ow_cells_T L ar HI 0.
Proof using All.
  unfold srd_mc_ow_cells_T.
  intros O R M model K OB LBX FF LK Aw cr sp r str Wextra qc de rem g eg sst pb kb CTX R11 R12 HPB HKB
         F fl LK2 M2 model2 G Mb modelb LKc Ac BD IAc len1 M1 model1 M3 model3 Hl BD1 EKp C264 C272 C280 C288 FZ BD3 AHP.
  pose proof BD as BD0. pose proof G as G0. pose proof CTX as CTX0.
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
  assert (Epb : pb = p).
  { rewrite A11 in R11. apply (f_equal bv_unsigned) in R11. rewrite !L5.unsigned_lit in R11 by (clear - HPB DP0 DP1 Hk; lia). symmetry; exact R11. }
  assert (Ekb : kb = k).
  { rewrite A12 in R12. apply (f_equal bv_unsigned) in R12. rewrite !L5.unsigned_lit in R12 by (clear - HKB Hk; lia). symmetry; exact R12. }
  subst pb kb.
  assert (L1R : 0 <= len1 <= k) by (rewrite Hl; clear - Hk G2; lia).
  pose proof G as G'. unfold PGSRDK.srd_frame in G'.
  destruct G' as [Hg SPTg SLOg SHIg SPCg OCRg OWNg FS1g FS2g FCEILg LKI2g FLPg FLNCg HH2g FLCg FRg F8g FBIGg F32g FLAg FLRg FLBIGg NCFg NCSg].
  change (ff_bytes 1) with 128 in *.
  assert (CLo : forall a, os <= a < os + 296 -> aclient L ar LB FF sp 20480 a).
  { intros a Ha. apply PMASR1.cl_of_bf. right. exact (PMASR1.in_fframe_of_aobjA FF os 296 a AO Ha). }
  assert (AO' : PMSPA.aobjA ((F, 1, sp - 160 - 0 + 32) :: FF) os 296).
  { destruct AO as (f & Hf & X1 & X2). exists f. split; [right; exact Hf| split; assumption]. }
  assert (VIo : forall a n, os <= a -> a + n <= os + 296 -> L5A.avis (ahid Ac modelb) a n).
  { intros a n Ha Hn j Hj. apply (PGSRDC.srd_vis L ar C HI LY HIok O R M model K OB LBX FF LK Aw cr sp r _ str _ _ F fl LK2 M2 model2 Mb modelb LKc Ac (a + j) CTX0 G0 BD0).
    right; right; right; left. clear - Ha Hn Hj; lia. }
  assert (KEEP : forall a, os + 264 <= a < os + 296 -> M3 (Z_to_bv 64 a) = Mb (Z_to_bv 64 a)).
  { intros a Ha. destruct AHP as (EK3 & _).
    rewrite (EK3 a).
    - apply FZ; [clear - Ha O1; lia|]. intros [Y|[Y|Y]].
      + apply (NCSg a); [clear - Y; lia| apply CLo; clear - Ha; lia].
      + apply (NCFg a); [left; exact Y| apply CLo; clear - Ha; lia].
      + apply (NCFg a); [right; unfold HeapIfaceA.S, HeapIfaceA.SB in *; clear - Y F32g; lia| apply CLo; clear - Ha; lia].
    - split; [clear - Ha O1; lia|]. split.
      + apply PMASR1.cl_of_bf. right. exact (PMASR1.in_fframe_of_aobjA _ os 296 a AO' ltac:(clear - Ha; lia)).
      + intros r0 [<-|[]]. unfold L5.in_rng. cbn [fst snd]. intros Y.
        destruct (DX a ltac:(clear - Y L1R; lia)) as (_ & _ & X3 & _). apply X3. clear - Ha; lia. }
  assert (TR : forall off v, 264 <= off <= 288 -> L5.u64_at RSEGS (mrestrict (ahid Ac modelb) Mb) (os + off) v -> L5.u64_at RSEGS M3 (os + off) v).
  { intros off v Hoff X.
    apply (proj1 (L5A.u64_at_vis _ Mb (os + off) v (VIo (os + off) 8 ltac:(clear - Hoff; lia) ltac:(clear - Hoff; lia)) ltac:(clear - O1 Hoff; lia) ltac:(clear - O1 Hoff; lia))) in X.
    apply (L5C.u64_at_agree RSEGS Mb M3); [intros i Hi; apply KEEP; clear - Hi Hoff; lia| clear - O1 Hoff; lia| clear - O1 Hoff; lia| exact X]. }
  split; [exact (TR 264 _ ltac:(clear; lia) C264)|]. split; [exact (TR 272 _ ltac:(clear; lia) C272)|].
  split; [exact (TR 280 _ ltac:(clear; lia) C280)| exact (TR 288 _ ltac:(clear; lia) C288)].
Qed.

Lemma srd_mc_keep_iss : srd_mc_keep_iss_T L ar HI 0.
Proof using All.
  unfold srd_mc_keep_iss_T.
  intros O R0 M0 model0 K OB LBX FF LK Aw cr sp r str Wextra qc de rem g eg sst p k CTX R11 R12 Hp0 Hk0 F fl LK2 M2 model2 FR
         M model LKc Ac BI ISM len1 M1 model1 M3 model3 Elen BI1 EK1 U264 U272 U280 U288 AGM BI3 HP3.
  pose proof CTX as (OK & HH & AM & K0 & ENT & FRM & FRS & OFR & A10 & SP32 & ARGS & WX & PA0 & IA0 & BASE0 & INCS & KONT).
  destruct ENT as (Rra & RAok & Rsp & Rgp & Rtp & ASTK & STKSH).
  destruct ARGS as (p' & k' & A11 & A12 & Hk & DST). destruct WX as (p'' & k'' & A11' & A12' & Hp'' & Hk'' & WE).
  rewrite L5SAR.r11 in A11, A11'. rewrite L5SAR.r12 in A12, A12'.
  pose proof (PGSA.oo_lay _ _ _ _ _ _ OK) as (LY1 & LY2 & LY3 & LY4 & LY5 & O8 & I8 & LY6 & LYD).
  pose proof (PGSA.oo_src _ _ _ _ _ _ OK M0 _ OB PA0) as (PSRC & PNI & SDEF0).
  pose proof (PMASK.fs_above_img L ar C HI LY HIok _ _ _ _ _ _ _ HH) as FSI.
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & _).
  pose proof (PMASK.frb_of L ar C HI HIok _ _ _ _ _ _ _ HH) as FRB. pose proof (PMASK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HH) as BRB.
  pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP).
  set (os := PGS.ow_os O) in *. set (ois := PGS.ow_ois O) in *. set (lo := PGS.ow_lo O) in *. set (hi := PGS.ow_hi O) in *.
  set (LB := PM.src_own (PM.SRC qc de rem) ++ OB ++ LBX) in *.
  assert (AO : PMSPA.aobjA FF os 296) by (apply (PGSKA.aobjA_sub FF lo hi); [exact OFR| exact LY1| exact LY2]).
  assert (AOI : PMSPA.aobjA FF ois 272) by (apply (PGSKA.aobjA_sub FF lo hi); [exact OFR| exact LY3| exact LY4]).
  pose proof (PGSKA.src_visG L ar C HI LY HIok LB FF LK cr Aw M0 model0 os _ _ _ sp (PMSPA.pm_scr 4) HH AO O8 PSRC PNI ASTK)
    as ((O1 & _ & OBIG) & _ & _ & OCE & _ & _ & OFS1 & OFS2).
  pose proof (PGSKA.iss_visG L ar C HI LY HIok LB FF LK cr Aw M0 model0 ois str _ sp (PMSPA.pm_scr 4) HH AOI I8 IA0 ASTK)
    as ((I1 & _ & IBIG) & _ & _ & ICE & _ & _).
  cbn [PM.sr_qc PM.sr_de PM.sr_rem PM.sm_g PM.sm_eg PM.sm_st] in *.
  pose proof PSRC as (S240 & S248 & SD256 & S264 & S272 & S280 & S288 & G1 & G2 & G3 & G16 & DCH & ACH & ACC240).
  assert (QIN : In (qc, PM.CHUNK) LB) by (unfold LB, PM.src_own; cbn; left; reflexivity).
  assert (OBIN : forall B m, In (B, m) OB -> In (B, m) LB) by (intros B m Hin; unfold LB, PM.src_own; cbn; right; apply in_or_app; left; exact Hin).
  assert (SOWN : incl (PM.vs_own str) LB) by (unfold LB; intros x Hx; apply in_or_app; right; apply in_or_app; right; exact (INCS x Hx)).
  assert (STb : forall c1 n1 q1, str = PM.VLong c1 n1 q1 -> In (q1, c1) LB).
  { intros c1 n1 q1 E. apply SOWN. rewrite E. cbn. left. reflexivity. }
  assert (STbX : forall c1 n1 q1, str = PM.VLong c1 n1 q1 -> In (q1, c1) LBX).
  { intros c1 n1 q1 E. apply INCS. rewrite E. cbn. left. reflexivity. }
  assert (ND : NoDup (map fst LB)) by exact (PMASK.lb_nodup L ar C HI HIok _ _ _ _ _ _ _ HH).
  destruct (WB _ QIN) as ((Q0 & QI & Q16 & _ & Q4 & QAPP) & _). cbn [fst snd] in Q0, QI, Q16, Q4, QAPP.
  unfold app_mem in QAPP, FSAPP. destruct FSAPP as (FSA0 & FSAs & FSA47). destruct QAPP as (QA0 & QAs & QA47).
  assert (DF : 0 <= p' /\ p' + k' <= 2 ^ 47 /\ L5.defined M0 p' k' /\ aacc M0 p' k' /\ app_rng ar p' k'
     /\ (forall a, p' <= a < p' + k' -> in_block LB a \/ in_fframe FF a)
     /\ (forall a, p' <= a < p' + k' -> ~ (sp - PMSPA.pm_scr 4 <= a < sp) /\ ~ (ois <= a < ois + 272) /\ ~ (os <= a < os + 296)
           /\ ~ (qc <= a < qc + PM.CHUNK) /\ (forall c1 n1 q1, str = PM.VLong c1 n1 q1 -> ~ (q1 <= a < q1 + c1)))
     /\ (p' + k' <= BIGSHADOW_LO \/ BIGSHADOW_HI <= p')
     /\ (PMSPA.aobjA FF p' k' \/ exists q m, In (q, m) LB /\ q <= p' /\ p' + k' <= q + m)
     /\ (p' + k' <= qc \/ qc + PM.CHUNK <= p')).
  { assert (OBJ : forall (APo : p' + k' <= os \/ os + 296 <= p') (APi : p' + k' <= ois \/ ois + 272 <= p'),
      PMSPA.aobjA FF p' k' -> L5.defined M0 p' k' -> aacc M0 p' k' ->
      0 <= p' /\ p' + k' <= 2 ^ 47 /\ L5.defined M0 p' k' /\ aacc M0 p' k' /\ app_rng ar p' k'
      /\ (forall a, p' <= a < p' + k' -> in_block LB a \/ in_fframe FF a)
      /\ (forall a, p' <= a < p' + k' -> ~ (sp - PMSPA.pm_scr 4 <= a < sp) /\ ~ (ois <= a < ois + 272) /\ ~ (os <= a < os + 296)
            /\ ~ (qc <= a < qc + PM.CHUNK) /\ (forall c1 n1 q1, str = PM.VLong c1 n1 q1 -> ~ (q1 <= a < q1 + c1)))
      /\ (p' + k' <= BIGSHADOW_LO \/ BIGSHADOW_HI <= p')
      /\ (PMSPA.aobjA FF p' k' \/ exists q m, In (q, m) LB /\ q <= p' /\ p' + k' <= q + m)
      /\ (p' + k' <= qc \/ qc + PM.CHUNK <= p')).
    { intros APo APi AOD DD AD.
      pose proof AOD as (f & Hf & X1 & X2). destruct (WF f Hf) as (Y1 & Y2 & _).
      pose proof (PMASK.blk_obj_apart L ar C HI HIok LB FF LK cr Aw M0 _ qc PM.CHUNK p' k' HH QIN AOD) as APQ.
      split; [clear - X1 Y1 FSI; lia|]. split; [clear - X2 Y2 FSCEIL SLO SHI SPT; lia|]. split; [exact DD|]. split; [exact AD|].
      split; [apply (L5SAR.app_rng_fs L ar C HI HIok LB FF LK cr Aw M0 _ p' k' HH); clear - X1 X2 Y1 Y2; lia|].
      split; [intros a Ha; right; apply (PMASR1.in_fframe_of_aobjA FF p' k' a AOD Ha)|].
      split; [|split; [destruct FSAs as [Z|Z]; [left|right]; clear - Z X1 X2 Y1 Y2; lia| split; [left; exact AOD| clear - APQ; lia]]].
      intros a Ha. split; [clear - Ha X2 Y2 FSCEIL SLO; lia|]. split; [clear - Ha APi; lia|]. split; [clear - Ha APo; lia|].
      split; [clear - Ha APQ; lia|].
      intros c1 n1 q1 E. destruct (PMASK.blk_obj_apart L ar C HI HIok LB FF LK cr Aw M0 _ q1 c1 p' k' HH (STb c1 n1 q1 E) AOD) as [Z|Z]; clear - Ha Z; lia. }
    destruct DST as [(AOD & Hk8 & DD & AD & APF)|DW].
    - apply OBJ; [clear - APF LY1 LY2; lia| clear - APF LY3 LY4; lia| exact AOD| exact DD| exact AD].
    - destruct (PGSA.oo_win _ _ _ _ _ _ OK M0 (PM.SRC qc de rem) OB p' k' PA0 DW) as (W0 & WD & [(B & m & BIN & WB1 & WB2)|(W1 & W2 & WL1 & WL2 & WL3 & WL4 & WL5)] & WACC).
      + pose proof (OBIN B m BIN) as TIN.
        destruct (WB _ TIN) as ((T0 & _ & _ & _ & T4 & TAPP) & _). cbn [fst snd] in T0, T4, TAPP.
        unfold app_mem in TAPP. destruct TAPP as (TA0 & TAs & TA47).
        assert (NQ : B <> qc).
        { intros E. apply (PMASK.fst_neq_appA [(qc, PM.CHUNK)] (OB ++ LBX) qc PM.CHUNK B m); [exact ND| left; reflexivity| apply in_or_app; left; exact BIN| symmetry; exact E]. }
        pose proof (PMASK.blk_apart L ar C HI HIok LB FF LK cr Aw M0 _ B m qc PM.CHUNK HH TIN QIN NQ) as APQ.
        pose proof (PMASK.blk_obj_apart L ar C HI HIok LB FF LK cr Aw M0 _ B m os 296 HH TIN AO) as APP.
        pose proof (PMASK.blk_obj_apart L ar C HI HIok LB FF LK cr Aw M0 _ B m ois 272 HH TIN AOI) as API.
        split; [clear - WB1 T0; lia|]. split; [clear - WB2 T4 SLO SHI SPT; lia|]. split; [exact WD|]. split; [exact WACC|].
        split; [apply (L5SAR.app_rng_block L ar C HI HIok LB FF LK cr Aw M0 _ B m p' k' HH TIN); clear - WB1 WB2; lia|].
        split; [intros a Ha; left; apply (PMASR1.in_block_of LB B m a TIN); clear - Ha WB1 WB2; lia|].
        split; [|split; [destruct TAs as [Z|Z]; [left|right]; clear - Z WB1 WB2; lia|
                 split; [right; exists B, m; split; [exact TIN|]; split; [exact WB1| exact WB2]| clear - APQ WB1 WB2; lia]]].
        intros a Ha. split; [clear - Ha WB1 WB2 T4 SLO; lia|]. split; [clear - Ha WB1 WB2 API; lia|]. split; [clear - Ha WB1 WB2 APP; lia|].
        split; [clear - Ha WB1 WB2 APQ; lia|].
        intros c1 n1 q1 E.
        assert (NS : B <> q1) by (apply (PMASK.fst_neq_appA ((qc, PM.CHUNK) :: OB) LBX B m q1 c1); [exact ND| right; exact BIN| exact (STbX c1 n1 q1 E)]).
        destruct (PMASK.blk_apart L ar C HI HIok LB FF LK cr Aw M0 _ B m q1 c1 HH TIN (STb c1 n1 q1 E) NS) as [Z|Z]; clear - Ha WB1 WB2 Z; lia.
      + apply OBJ; [exact WL4| exact WL5| apply (PGSKA.aobjA_sub FF lo hi p' k' OFR WL1 WL2)| exact WD| exact WACC]. }
  destruct DF as (DP0 & DP1 & DDP & DAP & DAPP & DCL & DX & DSH & DLOC & DQA).
  assert (P37 : 0 <= p < 2 ^ 64) by exact Hp0.
  assert (P38 : 0 <= k < 2 ^ 64) by exact Hk0.
  assert (EP : p' = p).
  { rewrite R11 in A11. apply (f_equal bv_unsigned) in A11. rewrite !L5.unsigned_lit in A11 by (clear - P37 DP0 DP1 Hk; unfold PM.CHUNK in Hk; lia). lia. }
  assert (EK : k' = k).
  { rewrite R12 in A12. apply (f_equal bv_unsigned) in A12. rewrite !L5.unsigned_lit in A12 by (clear - P38 Hk; unfold PM.CHUNK in Hk; lia). lia. }
  assert (EP2 : p'' = p).
  { rewrite R11 in A11'. apply (f_equal bv_unsigned) in A11'. rewrite !L5.unsigned_lit in A11' by (clear - P37 Hp''; lia). lia. }
  assert (EK2 : k'' = k).
  { rewrite R12 in A12'. apply (f_equal bv_unsigned) in A12'. rewrite !L5.unsigned_lit in A12' by (clear - P38 Hk''; lia). lia. }
  subst p' k' p'' k''.
  assert (ISSG : forall (Ma Mb : mem) (W : list L5.range), L5SAR.ek L ar LB FF sp (PMSPA.pm_scr 4) W Ma Mb -> PMKA.wapp W ->
      (forall a, ois <= a < ois + 272 -> L5.outside W a) ->
      (forall c1 n1 q1, str = PM.VLong c1 n1 q1 -> forall a, q1 <= a < q1 + c1 -> L5.outside W a) ->
      forall sm0, PM.iss_at RSEGS PMA.AD PMSPA.accA Ma ois str sm0 -> PM.iss_at RSEGS PMA.AD PMSPA.accA Mb ois str sm0).
  { intros Ma Mb W E WP OI OS sm0 IS.
    apply (PMFA.iss_at_agreeA RSEGS PMA.AD Ma Mb ois str sm0); [clear - I1; lia| clear - I1; lia| split| | exact IS].
    - intros i Hi. apply E. split; [clear - Hi I1; lia|].
      split; [apply PMASR1.cl_of_bf; right; exact (PMASR1.in_fframe_of_aobjA FF ois 272 i AOI Hi)| exact (OI i Hi)].
    - exact (PMKA.agsh_obj L ar LB FF sp (PMSPA.pm_scr 4) W Ma Mb E WP FRB ois 272 AOI).
    - intros c1 n1 q1 Es. pose proof (STb c1 n1 q1 Es) as TIN. destruct (WB _ TIN) as ((T0 & _ & _ & _ & T4 & _) & _).
      cbn [fst snd] in T0, T4. split.
      + intros i Hi. apply E. split; [clear - Hi T0 T4 SLO SHI SPT; lia|].
        split; [apply PMASR1.cl_of_bf; left; exact (PMASR1.in_block_of LB q1 c1 i TIN Hi)| exact (OS c1 n1 q1 Es i Hi)].
      + apply (PMASK.agsh_blk L ar LB FF sp (PMSPA.pm_scr 4) W Ma Mb q1 c1 E WP TIN); clear - T0 T4 SLO SHI SPT; lia. }
  assert (WOS : PMKA.wapp [(PGS.ow_os O + 256, 40)]).
  { apply PMKA.wapp_cons; [cbn [fst snd]; clear - OBIG; unfold BIGSHADOW_LO, BIGSHADOW_HI in *; lia| apply PMKA.wapp_nil]. }
  assert (OI_os : forall a, ois <= a < ois + 272 -> L5.outside [(PGS.ow_os O + 256, 40)] a).
  { intros a Ha r0 [<-|[]]. unfold L5.in_rng. cbn [fst snd]. clear - Ha LYD. lia. }
  assert (OS_os : forall c1 n1 q1, str = PM.VLong c1 n1 q1 -> forall a, q1 <= a < q1 + c1 -> L5.outside [(PGS.ow_os O + 256, 40)] a).
  { intros c1 n1 q1 Es a Ha r0 [<-|[]]. unfold L5.in_rng. cbn [fst snd].
    destruct (PMASK.blk_obj_apart L ar C HI HIok LB FF LK cr Aw M0 _ q1 c1 os 296 HH (STb c1 n1 q1 Es) AO) as [Z|Z]; clear - Ha Z; lia. }
  assert (ISS1 : PM.iss_at RSEGS PMA.AD PMSPA.accA M1 ois str (PM.STRM g eg sst)) by exact (ISSG M M1 _ EK1 WOS OI_os OS_os _ ISM).
  assert (LEN : len1 <= k) by (rewrite Elen; apply Z.le_min_l).
  assert (NDP : forall a, p <= a < p + len1 -> p <= a < p + k) by (intros a Ha; clear - Ha LEN; lia).
  assert (WSP : PMKA.wapp [(p, len1)]).
  { apply PMKA.wapp_cons; [cbn [fst snd]; unfold BIGSHADOW_LO, BIGSHADOW_HI in *; clear - DSH LEN DP0; lia| apply PMKA.wapp_nil]. }
  assert (EK13 : L5SAR.ek L ar LB FF sp (PMSPA.pm_scr 4) [(p, len1)] M1 M3).
  { apply (L5SAR.ek_callee L ar LB [] FF [(F, 1, sp - 160 - 0 + 32)] sp (PMSPA.pm_scr 4) (sp - 160 - 0) 2560 _ [(p, len1)] M1 M3 HP3);
      [unfold PMSPA.pm_scr; clear; lia| clear; lia| intros a _ Oq; exact Oq]. }
  apply (ISSG M1 M3 _ EK13 WSP); [| | exact ISS1].
  - intros a Ha r0 [<-|[]]. unfold L5.in_rng. cbn [fst snd]. intros Y. destruct (DX a (NDP a Y)) as (_ & X2 & _). apply X2. exact Ha.
  - intros c1 n1 q1 Es a Ha r0 [<-|[]]. unfold L5.in_rng. cbn [fst snd]. intros Y.
    destruct (DX a (NDP a Y)) as (_ & _ & _ & _ & X5). apply (X5 c1 n1 q1 Es). exact Ha.
Qed.

Lemma srd_mc_keep_base : srd_mc_keep_base_T L ar HI 0.
Proof using All.
  unfold srd_mc_keep_base_T.
  intros O R0 M0 model0 K OB LBX FF LK Aw cr sp r str Wextra qc de rem g eg sst p k CTX R11 R12 HP HK F fl LK2 M2 model2 FR
         M model LKc Ac BI ISS len1 M1 model1 M3 model3 HL BI1 EK1 U264 U272 U280 U288 FR1 BI3 AH.
  pose proof CTX as (OK & HH & _ & _ & ENT & _ & _ & OFR & _ & _ & ARGS & WX & PA0 & IA0 & BASE0 & _ & _).
  destruct ENT as (_ & _ & _ & _ & _ & ASTK & _).
  destruct ARGS as (p' & k' & A11 & A12 & Hk & DST). destruct WX as (p'' & k'' & A11' & A12' & Hp'' & Hk'' & WE).
  rewrite L5SAR.r11 in A11, A11'. rewrite L5SAR.r12 in A12, A12'.
  pose proof (PGSA.oo_lay _ _ _ _ _ _ OK) as (LY1 & LY2 & LY3 & LY4 & _ & O8 & I8 & _).
  pose proof (PGSA.oo_src _ _ _ _ _ _ OK M0 _ OB PA0) as (PSRC & PNI & _).
  pose proof (PMASK.fs_above_img L ar C HI LY HIok _ _ _ _ _ _ _ HH) as FSI.
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & _ & FSCEIL & _).
  pose proof ASTK as (_ & SLO & SHI & SPT & _).
  set (LB := PM.src_own (PM.SRC qc de rem) ++ OB ++ LBX) in *.
  assert (AO : PMSPA.aobjA FF (PGS.ow_os O) 296) by (apply (PGSKA.aobjA_sub FF (PGS.ow_lo O) (PGS.ow_hi O)); [exact OFR| exact LY1| exact LY2]).
  assert (AOI : PMSPA.aobjA FF (PGS.ow_ois O) 272) by (apply (PGSKA.aobjA_sub FF (PGS.ow_lo O) (PGS.ow_hi O)); [exact OFR| exact LY3| exact LY4]).
  pose proof (PGSKA.src_visG L ar C HI LY HIok LB FF LK cr Aw M0 model0 (PGS.ow_os O) _ _ _ sp (PMSPA.pm_scr 4) HH AO O8 PSRC PNI ASTK)
    as ((O1 & _) & _).
  pose proof (PGSKA.iss_visG L ar C HI LY HIok LB FF LK cr Aw M0 model0 (PGS.ow_ois O) str _ sp (PMSPA.pm_scr 4) HH AOI I8 IA0 ASTK)
    as ((I1 & _) & _).
  assert (QIN : In (qc, PM.CHUNK) LB) by (unfold LB, PM.src_own; cbn; left; reflexivity).
  assert (OBIN : forall B m, In (B, m) OB -> In (B, m) LB) by (intros B m Hin; unfold LB, PM.src_own; cbn; right; apply in_or_app; left; exact Hin).
  destruct (WB _ QIN) as ((Q0 & QI & _) & _). cbn [fst snd] in Q0, QI.
  rewrite (L5A.aly_img_lo L C (PMA.ly_as0 L C LY)), (L5A.aly_img_hi L C (PMA.ly_as0 L C LY)) in QI.
  assert (DLOC : 0 <= p' /\ p' + k' <= 2 ^ 47 /\ (PMSPA.aobjA FF p' k' \/ exists q m, In (q, m) LB /\ q <= p' /\ p' + k' <= q + m)).
  { assert (OBJ : PMSPA.aobjA FF p' k' ->
                  0 <= p' /\ p' + k' <= 2 ^ 47 /\ (PMSPA.aobjA FF p' k' \/ exists q m, In (q, m) LB /\ q <= p' /\ p' + k' <= q + m)).
    { intros AOD. pose proof AOD as (f & Hf & X1 & X2). destruct (WF f Hf) as (Y1 & Y2 & _).
      split; [clear - X1 Y1 FSI; lia|]. split; [clear - X2 Y2 FSCEIL SLO SHI SPT; lia| left; exact AOD]. }
    destruct DST as [(AOD & _)|DW]; [exact (OBJ AOD)|].
    destruct (PGSA.oo_win _ _ _ _ _ _ OK M0 (PM.SRC qc de rem) OB p' k' PA0 DW)
      as (_ & _ & [(B & m & BIN & WB1 & WB2)|(_ & _ & WL1 & WL2 & _)] & _).
    - pose proof (OBIN B m BIN) as TIN. destruct (WB _ TIN) as ((T0 & _ & _ & _ & T4 & _) & _). cbn [fst snd] in T0, T4.
      split; [clear - WB1 T0; lia|]. split; [clear - WB2 T4 SLO SHI SPT; lia|].
      right. exists B, m. split; [exact TIN| split; [exact WB1| exact WB2]].
    - exact (OBJ (PGSKA.aobjA_sub FF _ _ p' k' OFR WL1 WL2)). }
  destruct DLOC as (DP0 & DP1 & DLOC).
  assert (EP : p' = p).
  { rewrite R11 in A11. apply (f_equal bv_unsigned) in A11.
    rewrite !L5.unsigned_lit in A11 by (clear - HP DP0 DP1 Hk; unfold PM.CHUNK in Hk; lia). lia. }
  assert (EK : k' = k).
  { rewrite R12 in A12. apply (f_equal bv_unsigned) in A12.
    rewrite !L5.unsigned_lit in A12 by (clear - HK Hk; unfold PM.CHUNK in Hk; lia). lia. }
  assert (EP2 : p'' = p).
  { rewrite R11 in A11'. apply (f_equal bv_unsigned) in A11'. rewrite !L5.unsigned_lit in A11' by (clear - HP Hp''; lia). lia. }
  assert (EK2 : k'' = k).
  { rewrite R12 in A12'. apply (f_equal bv_unsigned) in A12'. rewrite !L5.unsigned_lit in A12' by (clear - HK Hk''; lia). lia. }
  subst p' k' p'' k''.
  pose proof BI3 as BI3'. unfold PGSRDK.srd_body, PMAUK.binv in BI3'. destruct BI3' as (_ & _ & _ & _ & _ & _ & EK3 & _).
  apply (PMASK.base_keep L ar C LY _ _ _ _ _ M0 M3 EK3); [| exact BASE0].
  intros a Ha r0 Hr. rewrite WE in Hr. unfold PGS.W_srcG, PGS.W_srcfG in Hr. cbn [PM.sr_qc app] in Hr. unfold L5.in_rng.
  destruct Hr as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn [fst snd].
  - clear - Ha O1. lia.
  - clear - Ha I1. lia.
  - clear - Ha I1. lia.
  - clear - Ha QI Q0. unfold PM.CHUNK in *. lia.
  - destruct DLOC as [(f & Hf & X1 & _)|(q & m & Hq & X1 & X2)].
    + destruct (WF f Hf) as (Y1 & _). clear - Ha X1 Y1 FSI. lia.
    + destruct (WB _ Hq) as ((T0 & TI & _) & _). cbn [fst snd] in T0, TI.
      rewrite (L5A.aly_img_lo L C (PMA.ly_as0 L C LY)), (L5A.aly_img_hi L C (PMA.ly_as0 L C LY)) in TI.
      clear - Ha X1 X2 TI T0. lia.
Qed.

Lemma srd_mc_keep_ow : srd_mc_keep_ow_T L ar HI 0.
Proof using All.
  unfold srd_mc_keep_ow_T.
  intros O R M model K OB LBX FF LK Aw cr sp r str Wextra qc de rem g eg sst pb kb CTX R11 R12 HPB HKB
         F fl LK2 M2 model2 G Mb modelb LKc Ac BD IAc len1 M1 model1 M3 model3 Hl BD1 EKp C264 C272 C280 C288 FZ BD3 AHP.
  destruct (srd_mc_ow_cells O R M model K OB LBX FF LK Aw cr sp r str Wextra qc de rem g eg sst pb kb CTX R11 R12 HPB HKB F fl LK2 M2 model2 G Mb modelb LKc Ac BD IAc len1 M1 model1 M3 model3 Hl BD1 EKp C264 C272 C280 C288 FZ BD3 AHP) as (U264 & U272 & U280 & U288).
  pose proof BD as BD0. pose proof G as G0. pose proof CTX as CTX0.
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
  assert (Epb : pb = p).
  { rewrite A11 in R11. apply (f_equal bv_unsigned) in R11. rewrite !L5.unsigned_lit in R11 by (clear - HPB DP0 DP1 Hk; lia). symmetry; exact R11. }
  assert (Ekb : kb = k).
  { rewrite A12 in R12. apply (f_equal bv_unsigned) in R12. rewrite !L5.unsigned_lit in R12 by (clear - HKB Hk; lia). symmetry; exact R12. }
  subst pb kb.
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
  unfold PGSRDK.srd_body in BD3. destruct BD3 as (B31 & B32 & B33 & B34 & B35 & B36 & B37 & B38 & B39 & B310).
  assert (AH3 : L5CA.ahpres L ar LB FF sp (PMSPA.pm_scr 4) WA M M3).
  { apply (L5SAR.ahpres_of L ar LB FF sp _ WA M M3 B37).
    - pose proof B36 as (_ & _ & _ & _ & SD3 & _). exact SD3.
    - exact B38. }
  pose proof (proj1 AH3) as EK. pose proof (proj2 (proj2 AH3)) as DK.
  assert (OUTO : forall i, os <= i < os + 256 -> L5.outside WA i).
  { intros i Hi. apply OUTWA; [clear - Hi; lia| clear - Hi LYD; lia| clear - Hi LYD; lia| destruct (APQO os 296 AO) as [Z|Z]; clear - Hi Z; lia|].
    intros Y. destruct (DX i Y) as (_ & _ & X3 & _). apply X3. clear - Hi; lia. }
  apply (PGSA.oo_upd _ _ _ _ _ _ OK LBX sp 20480 [(p, k)] M M3 (PM.SRC qc de rem) (PM.SRC qc de rem) OB FF LK Aw cr (vml_of model) OFR PA HH OWA OWB OWC).
  - exact AH3.
  - apply (PGSKA.src_fields_updG M M3 os ois (ois + 16) qc de rem de rem PSRC0); unfold PM.CHUNK.
    + clear - O1; lia.
    + clear - O1; lia.
    + apply (PMKA.agA_obj L ar LB FF sp 20480 WA M M3 EK WAPP FRB os 256); [apply (PGSKA.aobjA_sub FF lo hi); [exact OFR| clear - LY1; lia| clear - LY2; lia]| exact OUTO].
    + apply (PMKA.agsh_obj L ar LB FF sp 20480 WA M M3 EK WAPP FRB (os + 256) 40). apply (PGSKA.aobjA_sub FF lo hi); [exact OFR| clear - LY1; lia| clear - LY2; lia].
    + apply (PMASK.defined_dk L ar LB FF sp 20480 M M3 (os + 256) 8 DK); [| clear - O1; lia| clear - O1; lia| exact SD256].
      intros i Hi. apply PMASR1.cl_of_bf. right. apply (PMASR1.in_fframe_of_aobjA FF os 296 i AO). clear - Hi; lia.
    + apply (PMASK.agsh_blk L ar LB FF sp 20480 WA M M3 qc 16384 EK WAPP QIN); [clear - Q0; lia| clear - Q4 SLO SHI SPT; lia].
    + apply (PMASK.defined_dk L ar LB FF sp 20480 M M3 qc 16384 DK); [| clear - Q0; lia| clear - Q4 SLO SHI SPT; lia| exact DCH].
      intros i Hi. apply PMASR1.cl_of_bf. left. apply (PMASR1.in_block_of LB qc 16384 i QIN Hi).
    + exact U264. + exact U272. + exact U280. + exact U288. + clear - G1 G2 G3; lia. + clear - G1 G2 G3; lia. + clear - G1 G2 G3; lia.
  - reflexivity.
Qed.

Lemma srd_mc_keep_ok : srd_mc_keep_T L ar HI 0.
Proof using All.
  apply srd_mc_keep_of_split; [exact srd_mc_keep_ow| exact srd_mc_keep_iss| exact srd_mc_keep_base].
Qed.

End MT.
End PGSRDMT.
