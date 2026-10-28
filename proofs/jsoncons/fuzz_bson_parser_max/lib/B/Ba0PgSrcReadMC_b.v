(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnASrcKit_b PgSrcKitA_b PnASrcRead1_b PnASrcReadK_b PnASrcReadP_b Ba0PgSrcReadK_b Ba0PgSrcReadC_b Ba0PgSrcReadMS_b.
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

Module PGSRDMC.
Abbreviation RSEGS := PGSRDK.RSEGS.
Abbreviation mem := (word -> option byte).
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.

Section WithHeap.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Variable IL : icpt_layout.
Hypothesis ICok : aicpt_ok L ar IL SCFG HI.
Hypothesis ILY : as0_icpt_layout IL.

Definition srd_mc_pre_T (al : Z) : Prop :=
  forall (O : PGS.owner) (R0 : bvmap 5 word) (M0 : mem) (model0 : Model) (K : TSet) (OB LBX : list (Z * Z))
         (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (sp r : Z) (str : PM.vstr) (Wextra : list L5.range)
         (qc de rem g eg sst p k : Z),
    PGSRDK.srd_ctx L ar HI al O R0 M0 model0 K OB LBX FF LK Aw cr sp r (PM.SRC qc de rem) str (PM.STRM g eg sst) Wextra ->
    getr R0 (reg 11) = Z_to_bv 64 p -> getr R0 (reg 12) = Z_to_bv 64 k ->
    forall (F fl : Z) (LK2 : list fframe) (M2 : mem) (model2 : Model),
    PGSRDK.srd_frame L ar HI al R0 OB LBX FF LK Aw cr sp (PM.SRC qc de rem) F fl LK2 M2 model2 ->
    forall (fx : FPState) (R : bvmap 5 word) (M : mem) (model : Model) (LKc : list fframe) (Ac : list (Z * Z))
           (V : nat -> Z),
    PGSRDK.srd_body L ar HI al O R0 M0 model0 OB LBX FF LK Aw sp (PM.SRC qc de rem) Wextra F M model LKc cr Ac ->
    V 2%nat = sp - al -> V 36%nat = PGS.ow_os O -> V 37%nat = p -> V 38%nat = k -> 32 * V 50%nat = F -> V 51%nat = fl ->
    (forall i, In i [1; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> V i = bv_unsigned (getr R0 (reg i))) ->
    getr R (reg 3) = getr R0 (reg 3) -> getr R (reg 4) = getr R0 (reg 4) ->
    V 34%nat = qc -> V 35%nat = de -> V 45%nat = PGS.ow_ois O ->
    PM.iss_at RSEGS PMA.AD PMSPA.accA M (PGS.ow_ois O) str (PM.STRM g eg sst) ->
    PGSRDK.srd_stA V R (mrestrict (ahid Ac model) M) -> PGSRDK.srd_pathG V R (mrestrict (ahid Ac model) M) rem sst ->
    forall (len1 : Z) (fx1 : FPState) (R1 : bvmap 5 word) (M1 : mem) (model1 : Model),
    len1 = Z.min k rem ->
    PGSRDK.srd_body L ar HI al O R0 M0 model0 OB LBX FF LK Aw sp (PM.SRC qc de rem) Wextra F M1 model1 LKc cr Ac ->
    ahid Ac model1 = ahid Ac model ->
    getr R1 (reg 1) = Z_to_bv 64 716500 ->
    getr R1 (reg 4) = Z_to_bv 64 (hl_tp L) ->
    getr R1 (reg 10) = Z_to_bv 64 (V 37%nat) ->
    getr R1 (reg 11) = Z_to_bv 64 (V 35%nat) ->
    getr R1 (reg 12) = Z_to_bv 64 len1 ->
    getr R1 (reg 2) = Z_to_bv 64 ((V 2%nat) - 160) ->
    getr R1 (reg 8) = Z_to_bv 64 (V 2%nat) ->
    getr R1 (reg 9) = Z_to_bv 64 ((V 2%nat) - 160) ->
    getr R1 (reg 18) = Z_to_bv 64 ((((V 36%nat) + 288) / 8) + 2147450880) ->
    getr R1 (reg 19) = Z_to_bv 64 (V 36%nat) ->
    getr R1 (reg 20) = Z_to_bv 64 len1 ->
    getr R1 (reg 21) = Z_to_bv 64 ((((V 36%nat) + 280) / 8) + 2147450880) ->
    getr R1 (reg 22) = Z_to_bv 64 (V 38%nat) ->
    getr R1 (reg 23) = Z_to_bv 64 ((V 36%nat) + 288) ->
    getr R1 (reg 24) = Z_to_bv 64 ((V 36%nat) + 280) ->
    getr R1 (reg 25) = Z_to_bv 64 ((4 * (V 50%nat)) + 2147450880) ->
    getr R1 (reg 26) = Z_to_bv 64 (32 * (V 50%nat)) ->
    (forall x, In x [3; 4; 27]%nat -> getr R1 (reg x) = getr R (reg x)) ->
    (aacc M1 p len1
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
            \/ (PGS.ow_os O <= i < PGS.ow_os O + 296) \/ ((PGS.ow_os O + 8) / 8 + SB <= i < (PGS.ow_os O + 8) / 8 + SB + 36)))) ->
    (forall (M3 : mem) (model3 : Model), PGSRDK.srd_body L ar HI al O R0 M0 model0 OB LBX FF LK Aw sp (PM.SRC qc de rem) Wextra F M3 model3 LKc cr Ac ->
      L5CA.ahpres L ar ([] ++ (PM.src_own (PM.SRC qc de rem) ++ OB ++ LBX)) ((F, 1, sp - 160 - al + 32) :: FF) (sp - 160 - al) 2560 [(p, len1)] M1 M3 ->
      PGS.ow_at O M3 (PM.SRC qc de rem) OB /\ PM.iss_at RSEGS PMA.AD PMSPA.accA M3 (PGS.ow_ois O) str (PM.STRM g eg sst) /\ PMSTA.base_okA RSEGS PMA.AD M3) ->
    (forall i, 0 <= i < 2 ^ 64 ->
      (sp - 160 - al <= i < sp) \/ (F <= i < F + 120 /\ ~ (F + 24 <= i < F + 32)) \/ (F / 8 + SB <= i < F / 8 + SB + 16)
      \/ (PGS.ow_os O <= i < PGS.ow_os O + 296) \/ ((PGS.ow_os O + 8) / 8 + SB <= i < (PGS.ow_os O + 8) / 8 + SB + 36) ->
      ~ ((((V 2%nat) - 152) <= i < ((V 2%nat) - 152) + 16) \/ (((V 2%nat) - 112) <= i < ((V 2%nat) - 112) + 8) \/ (((32 * (V 50%nat)) + 0) <= i < ((32 * (V 50%nat)) + 0) + 24) \/ (((32 * (V 50%nat)) + 32) <= i < ((32 * (V 50%nat)) + 32) + 8) \/ (((4 * (V 50%nat)) + 2147450880) <= i < ((4 * (V 50%nat)) + 2147450880) + 12)) ->
      (mrestrict (ahid Ac model1) M1) (Z_to_bv 64 i) = mrestrict (ahid Ac model) M (Z_to_bv 64 i)) ->
    L5.u64_at RSEGS (mrestrict (ahid Ac model1) M1) ((V 2%nat) - 152) ((32 * (V 50%nat)) + 32) ->
    L5.u64_at RSEGS (mrestrict (ahid Ac model1) M1) ((V 2%nat) - 144) (32 * (V 50%nat)) ->
    L5.u64_at RSEGS (mrestrict (ahid Ac model1) M1) ((V 2%nat) - 112) (32 * (V 50%nat)) ->
    L5.u64_at RSEGS (mrestrict (ahid Ac model1) M1) ((32 * (V 50%nat)) + 32) (V 38%nat) ->
    L5.u8_at RSEGS (mrestrict (ahid Ac model1) M1) ((4 * (V 50%nat)) + 2147450891) 243 ->
    L5.u8_at RSEGS (mrestrict (ahid Ac model1) M1) ((4 * (V 50%nat)) + 2147450890) 243 ->
    L5.u8_at RSEGS (mrestrict (ahid Ac model1) M1) ((4 * (V 50%nat)) + 2147450889) 243 ->
    L5.u8_at RSEGS (mrestrict (ahid Ac model1) M1) ((4 * (V 50%nat)) + 2147450888) 248 ->
    L5.u8_at RSEGS (mrestrict (ahid Ac model1) M1) ((4 * (V 50%nat)) + 2147450883) 241 ->
    L5.u8_at RSEGS (mrestrict (ahid Ac model1) M1) ((4 * (V 50%nat)) + 2147450882) 241 ->
    L5.u8_at RSEGS (mrestrict (ahid Ac model1) M1) ((4 * (V 50%nat)) + 2147450881) 241 ->
    L5.u8_at RSEGS (mrestrict (ahid Ac model1) M1) ((4 * (V 50%nat)) + 2147450880) 241 ->
    L5.u8_at RSEGS (mrestrict (ahid Ac model1) M1) ((4 * (V 50%nat)) + 2147450887) 242 ->
    L5.u8_at RSEGS (mrestrict (ahid Ac model1) M1) ((4 * (V 50%nat)) + 2147450886) 242 ->
    L5.u8_at RSEGS (mrestrict (ahid Ac model1) M1) ((4 * (V 50%nat)) + 2147450885) 242 ->
    L5.u8_at RSEGS (mrestrict (ahid Ac model1) M1) ((4 * (V 50%nat)) + 2147450884) 0 ->
    L5.u64_at RSEGS (mrestrict (ahid Ac model1) M1) ((32 * (V 50%nat)) + 16) 716108 ->
    L5.u64_at RSEGS (mrestrict (ahid Ac model1) M1) ((32 * (V 50%nat)) + 8) 127274 ->
    L5.u64_at RSEGS (mrestrict (ahid Ac model1) M1) (32 * (V 50%nat)) 1102416563 ->
    L5.defined (mrestrict (ahid Ac model1) M1) ((32 * (V 50%nat)) + 24) 8 ->
    L5.defined (mrestrict (ahid Ac model1) M1) ((32 * (V 50%nat)) + 40) 88 ->
    srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx1 R1 0x77c94 M1 model1) K.

Lemma srd_mc_cont : PGSRDMS.srd_mc_post_T L ar HI 0 ->
  forall (O : PGS.owner) (R0 : bvmap 5 word) (M0 : mem) (model0 : Model) (K : TSet) (OB LBX : list (Z * Z))
         (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (sp r : Z) (str : PM.vstr) (Wextra : list L5.range)
         (qc de rem g eg sst p k : Z),
    PGSRDK.srd_ctx L ar HI 0 O R0 M0 model0 K OB LBX FF LK Aw cr sp r (PM.SRC qc de rem) str (PM.STRM g eg sst) Wextra ->
    getr R0 (reg 11) = Z_to_bv 64 p -> getr R0 (reg 12) = Z_to_bv 64 k ->
    forall (F fl : Z) (LK2 : list fframe) (M2 : mem) (model2 : Model),
    PGSRDK.srd_frame L ar HI 0 R0 OB LBX FF LK Aw cr sp (PM.SRC qc de rem) F fl LK2 M2 model2 ->
    forall (fx : FPState) (R : bvmap 5 word) (M : mem) (model : Model) (LKc : list fframe) (Ac : list (Z * Z))
           (V : nat -> Z),
    PGSRDK.srd_body L ar HI 0 O R0 M0 model0 OB LBX FF LK Aw sp (PM.SRC qc de rem) Wextra F M model LKc cr Ac ->
    V 2%nat = sp - 0 -> V 36%nat = PGS.ow_os O -> V 37%nat = p -> V 38%nat = k -> 32 * V 50%nat = F -> V 51%nat = fl ->
    (forall i, In i [1; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> V i = bv_unsigned (getr R0 (reg i))) ->
    getr R (reg 3) = getr R0 (reg 3) -> getr R (reg 4) = getr R0 (reg 4) ->
    V 34%nat = qc -> V 35%nat = de -> V 45%nat = PGS.ow_ois O ->
    PM.iss_at RSEGS PMA.AD PMSPA.accA M (PGS.ow_ois O) str (PM.STRM g eg sst) ->
    PGSRDK.srd_stA V R (mrestrict (ahid Ac model) M) -> PGSRDK.srd_pathG V R (mrestrict (ahid Ac model) M) rem sst ->
    forall (len1 : Z) (fx1 : FPState) (R1 : bvmap 5 word) (M1 : mem) (model1 : Model),
    len1 = Z.min k rem ->
    PGSRDK.srd_body L ar HI 0 O R0 M0 model0 OB LBX FF LK Aw sp (PM.SRC qc de rem) Wextra F M1 model1 LKc cr Ac ->
    ahid Ac model1 = ahid Ac model ->
    getr R1 (reg 1) = Z_to_bv 64 716500 ->
    getr R1 (reg 4) = Z_to_bv 64 (hl_tp L) ->
    getr R1 (reg 10) = Z_to_bv 64 (V 37%nat) ->
    getr R1 (reg 11) = Z_to_bv 64 (V 35%nat) ->
    getr R1 (reg 12) = Z_to_bv 64 len1 ->
    getr R1 (reg 2) = Z_to_bv 64 ((V 2%nat) - 160) ->
    getr R1 (reg 8) = Z_to_bv 64 (V 2%nat) ->
    getr R1 (reg 9) = Z_to_bv 64 ((V 2%nat) - 160) ->
    getr R1 (reg 18) = Z_to_bv 64 ((((V 36%nat) + 288) / 8) + 2147450880) ->
    getr R1 (reg 19) = Z_to_bv 64 (V 36%nat) ->
    getr R1 (reg 20) = Z_to_bv 64 len1 ->
    getr R1 (reg 21) = Z_to_bv 64 ((((V 36%nat) + 280) / 8) + 2147450880) ->
    getr R1 (reg 22) = Z_to_bv 64 (V 38%nat) ->
    getr R1 (reg 23) = Z_to_bv 64 ((V 36%nat) + 288) ->
    getr R1 (reg 24) = Z_to_bv 64 ((V 36%nat) + 280) ->
    getr R1 (reg 25) = Z_to_bv 64 ((4 * (V 50%nat)) + 2147450880) ->
    getr R1 (reg 26) = Z_to_bv 64 (32 * (V 50%nat)) ->
    (forall x, In x [3; 4; 27]%nat -> getr R1 (reg x) = getr R (reg x)) ->
    (aacc M1 p len1
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
         ~ ((sp - 160 - 0 <= i < sp) \/ (F <= i < F + 128) \/ (F / 8 + SB <= i < F / 8 + SB + 16)
            \/ (PGS.ow_os O <= i < PGS.ow_os O + 296) \/ ((PGS.ow_os O + 8) / 8 + SB <= i < (PGS.ow_os O + 8) / 8 + SB + 36)))) ->
    (forall (M3 : mem) (model3 : Model), PGSRDK.srd_body L ar HI 0 O R0 M0 model0 OB LBX FF LK Aw sp (PM.SRC qc de rem) Wextra F M3 model3 LKc cr Ac ->
      L5CA.ahpres L ar ([] ++ (PM.src_own (PM.SRC qc de rem) ++ OB ++ LBX)) ((F, 1, sp - 160 - 0 + 32) :: FF) (sp - 160 - 0) 2560 [(p, len1)] M1 M3 ->
      PGS.ow_at O M3 (PM.SRC qc de rem) OB /\ PM.iss_at RSEGS PMA.AD PMSPA.accA M3 (PGS.ow_ois O) str (PM.STRM g eg sst) /\ PMSTA.base_okA RSEGS PMA.AD M3) ->
    (forall i, 0 <= i < 2 ^ 64 ->
      (sp - 160 - 0 <= i < sp) \/ (F <= i < F + 120 /\ ~ (F + 24 <= i < F + 32)) \/ (F / 8 + SB <= i < F / 8 + SB + 16)
      \/ (PGS.ow_os O <= i < PGS.ow_os O + 296) \/ ((PGS.ow_os O + 8) / 8 + SB <= i < (PGS.ow_os O + 8) / 8 + SB + 36) ->
      ~ ((((V 2%nat) - 152) <= i < ((V 2%nat) - 152) + 16) \/ (((V 2%nat) - 112) <= i < ((V 2%nat) - 112) + 8) \/ (((32 * (V 50%nat)) + 0) <= i < ((32 * (V 50%nat)) + 0) + 24) \/ (((32 * (V 50%nat)) + 32) <= i < ((32 * (V 50%nat)) + 32) + 8) \/ (((4 * (V 50%nat)) + 2147450880) <= i < ((4 * (V 50%nat)) + 2147450880) + 12)) ->
      (mrestrict (ahid Ac model1) M1) (Z_to_bv 64 i) = mrestrict (ahid Ac model) M (Z_to_bv 64 i)) ->
    L5.u64_at RSEGS (mrestrict (ahid Ac model1) M1) ((V 2%nat) - 152) ((32 * (V 50%nat)) + 32) ->
    L5.u64_at RSEGS (mrestrict (ahid Ac model1) M1) ((V 2%nat) - 144) (32 * (V 50%nat)) ->
    L5.u64_at RSEGS (mrestrict (ahid Ac model1) M1) ((V 2%nat) - 112) (32 * (V 50%nat)) ->
    L5.u64_at RSEGS (mrestrict (ahid Ac model1) M1) ((32 * (V 50%nat)) + 32) (V 38%nat) ->
    L5.u8_at RSEGS (mrestrict (ahid Ac model1) M1) ((4 * (V 50%nat)) + 2147450891) 243 ->
    L5.u8_at RSEGS (mrestrict (ahid Ac model1) M1) ((4 * (V 50%nat)) + 2147450890) 243 ->
    L5.u8_at RSEGS (mrestrict (ahid Ac model1) M1) ((4 * (V 50%nat)) + 2147450889) 243 ->
    L5.u8_at RSEGS (mrestrict (ahid Ac model1) M1) ((4 * (V 50%nat)) + 2147450888) 248 ->
    L5.u8_at RSEGS (mrestrict (ahid Ac model1) M1) ((4 * (V 50%nat)) + 2147450883) 241 ->
    L5.u8_at RSEGS (mrestrict (ahid Ac model1) M1) ((4 * (V 50%nat)) + 2147450882) 241 ->
    L5.u8_at RSEGS (mrestrict (ahid Ac model1) M1) ((4 * (V 50%nat)) + 2147450881) 241 ->
    L5.u8_at RSEGS (mrestrict (ahid Ac model1) M1) ((4 * (V 50%nat)) + 2147450880) 241 ->
    L5.u8_at RSEGS (mrestrict (ahid Ac model1) M1) ((4 * (V 50%nat)) + 2147450887) 242 ->
    L5.u8_at RSEGS (mrestrict (ahid Ac model1) M1) ((4 * (V 50%nat)) + 2147450886) 242 ->
    L5.u8_at RSEGS (mrestrict (ahid Ac model1) M1) ((4 * (V 50%nat)) + 2147450885) 242 ->
    L5.u8_at RSEGS (mrestrict (ahid Ac model1) M1) ((4 * (V 50%nat)) + 2147450884) 0 ->
    L5.u64_at RSEGS (mrestrict (ahid Ac model1) M1) ((32 * (V 50%nat)) + 16) 716108 ->
    L5.u64_at RSEGS (mrestrict (ahid Ac model1) M1) ((32 * (V 50%nat)) + 8) 127274 ->
    L5.u64_at RSEGS (mrestrict (ahid Ac model1) M1) (32 * (V 50%nat)) 1102416563 ->
    L5.defined (mrestrict (ahid Ac model1) M1) ((32 * (V 50%nat)) + 24) 8 ->
    L5.defined (mrestrict (ahid Ac model1) M1) ((32 * (V 50%nat)) + 40) 88 ->
    forall (fx2 : FPState) (R2 : bvmap 5 word) (M3 : mem) (model3 : Model),
    regs_preserved R1 R2 -> L5.defined M3 p len1 ->
    PGSRDK.srd_body L ar HI 0 O R0 M0 model0 OB LBX FF LK Aw sp (PM.SRC qc de rem) Wextra F M3 model3 LKc cr Ac ->
    L5CA.ahpres L ar ([] ++ (PM.src_own (PM.SRC qc de rem) ++ OB ++ LBX)) ((F, 1, sp - 160 - 0 + 32) :: FF) (sp - 160 - 0) 2560 [(p, len1)] M1 M3 ->
    srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx2 R2 716500 M3 model3) K.
Proof.
  intros POST O R0 M0 model0 K OB LBX FF LK Aw cr sp r str Wextra qc de rem g eg sst p k CTX R11 R12
         F fl LK2 M2 model2 FR fx R M model LKc Ac V BI XV2 XV36 XV37 XV38 XV50 XV51 XVS XR3 XR4 XV34 XV35 XV45 XIA ST PTH
         len1 fx1 R1 M1 model1 HL1 BI1 HID1 Y1 Y4 Y10 Y11 Y12 Y2 Y8 Y9 Y18 Y19 Y20 Y21 Y22 Y23 Y24 Y25 Y26 YK MEM KEEP AG1
         C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16 C17 C18 C19 C20 C21
         fx2 R2 M3 model3 RP DEF3 BI3 AH3.
  pose proof MEM as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & NDST).
  destruct (KEEP M3 model3 BI3 AH3) as (OW3 & IA3 & BASE3).
  assert (RP' : forall x, In x [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R2 (reg x) = getr R1 (reg x)).
  { intros x Hx. apply RP. cbn in Hx. repeat destruct Hx as [<-|Hx]; try destruct Hx; vm_compute; repeat (first [left; reflexivity| right]). }
  assert (AG3 : forall i, 0 <= i < 2 ^ 64 ->
      (sp - 160 - 0 <= i < sp) \/ (F <= i < F + 120 /\ ~ (F + 24 <= i < F + 32)) \/ (F / 8 + SB <= i < F / 8 + SB + 16)
      \/ (PGS.ow_os O <= i < PGS.ow_os O + 296) \/ ((PGS.ow_os O + 8) / 8 + SB <= i < (PGS.ow_os O + 8) / 8 + SB + 36) ->
      mrestrict (ahid Ac model3) M3 (Z_to_bv 64 i) = mrestrict (ahid Ac model1) M1 (Z_to_bv 64 i)).
  { intros i Hi RGi.
    apply (PGSRDC.srd_call_ag L ar C HI LY HIok O R0 M0 model0 K OB LBX FF LK Aw cr sp r (PM.SRC qc de rem) str (PM.STRM g eg sst) Wextra F fl LK2 M2 model2
             M1 model1 LKc Ac M3 model3 LKc Ac p len1 i CTX FR BI1 BI3 AH3 Hi ltac:(clear - RGi; lia)).
    intros Y. apply (NDST i Y). clear - RGi. lia. }
  pose proof (PMAUK.vis_facts L ar C HI (PMA.ly_as0 L C LY) HIok _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FR _ _ _ _ _ _ _ BI3)
    as (_ & _ & (VF128 & _) & _).
  change (ff_bytes 1) with 128 in VF128.
  pose proof ST as STA. unfold PGSRDK.srd_stA in STA.
  repeat match type of STA with _ /\ _ => let X := fresh "SA" in destruct STA as (X & STA) end.
  match goal with
  | H2 : _ <= V 2%nat <= _, H50 : _ <= V 50%nat <= _ |- _ => pose proof (conj H2 H50) as KB
  end.
  apply (POST O R0 M0 model0 K OB LBX FF LK Aw cr sp r str Wextra qc de rem g eg sst p k CTX R11 R12
          F fl LK2 M2 model2 FR fx R M model LKc Ac V BI XV2 XV36 XV37 XV38 XV50 XV51 XVS XR3 XR4 XV34 XV35 XV45 XIA ST PTH
          len1 fx2 R2 M3 model3 HL1 BI3 DEF3 OW3 IA3 BASE3).
  all: first
    [ solve [intros i Hi RGi NA ND; rewrite (AG3 i Hi RGi); exact (AG1 i Hi RGi NA)]
    | solve [intros x Hx; rewrite (RP' x) by (cbn in Hx; repeat (destruct Hx as [<-|Hx]; [inl|]); destruct Hx); exact (YK x Hx)]
    | solve [rewrite RP' by inl; assumption]
    | solve [apply (L5.defined_sub _ F 128 _ _ VF128); clear - XV50; lia]
    | solve [apply (L5C.u64_at_agree RSEGS (mrestrict (ahid Ac model1) M1));
             [intros ii Hii; apply AG3; clear - Hii KB XV2 XV50; unfold SB in *; lia
             | clear - KB XV2 XV50; unfold SB in *; lia| clear - KB XV2 XV50; unfold SB in *; lia| assumption]]
    | solve [apply (L5C.u8_at_agree RSEGS (mrestrict (ahid Ac model1) M1));
             [intros ii Hii; apply AG3; clear - Hii KB XV2 XV50; unfold SB in *; lia
             | clear - KB XV2 XV50; unfold SB in *; lia| clear - KB XV2 XV50; unfold SB in *; lia| assumption]]
    | match goal with |- ?G => fail 100 "mc_cont" G end ].
Qed.

Lemma srd_mc_call_ok : PGSRDMS.srd_mc_post_T L ar HI 0 -> srd_mc_pre_T 0.
Proof.
  intros POST. unfold srd_mc_pre_T.
  intros O R0 M0 model0 K OB LBX FF LK Aw cr sp r str Wextra qc de rem g eg sst p k CTX R11 R12
         F fl LK2 M2 model2 FR fx R M model LKc Ac V BI XV2 XV36 XV37 XV38 XV50 XV51 XVS XR3 XR4 XV34 XV35 XV45 XIA ST PTH
         len1 fx1 R1 M1 model1 HL1 BI1 HID1 Y1 Y4 Y10 Y11 Y12 Y2 Y8 Y9 Y18 Y19 Y20 Y21 Y22 Y23 Y24 Y25 Y26 YK MEM KEEP AG1
         C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16 C17 C18 C19 C20 C21.
  pose proof MEM as (ACD & DDF & D0 & D1 & APD & CLD & NSD & ACS & DSF & S0 & S1 & APS & CLS & NOV & HN & NDST).
  apply (PGSRDC.srd_call L ar C HI LY HIok O R0 M0 model0 K OB LBX FF LK Aw cr sp r (PM.SRC qc de rem) str (PM.STRM g eg sst) Wextra F fl LK2 M2 model2
           M1 model1 LKc Ac fx1 R1 _ p de len1 CTX FR BI1 Y1).
  - split; [clear; lia| reflexivity].
  - rewrite Y2, XV2. f_equal. clear; lia.
  - exact Y4.
  - rewrite Y10, XV37. reflexivity.
  - rewrite Y11, XV35. reflexivity.
  - exact Y12.
  - exact HN.
  - exact ACD.
  - exact DDF.
  - exact D0.
  - exact D1.
  - exact APD.
  - exact CLD.
  - exact NSD.
  - exact ACS.
  - exact DSF.
  - exact S0.
  - exact S1.
  - exact APS.
  - exact CLS.
  - exact NOV.
  - intros fx2 R2 M3 model3 RP DEF3 BI3 AH3.
    exact (srd_mc_cont POST O R0 M0 model0 K OB LBX FF LK Aw cr sp r str Wextra qc de rem g eg sst p k CTX R11 R12
      F fl LK2 M2 model2 FR fx R M model LKc Ac V BI XV2 XV36 XV37 XV38 XV50 XV51 XVS XR3 XR4 XV34 XV35 XV45 XIA ST PTH
      len1 fx1 R1 M1 model1 HL1 BI1 HID1 Y1 Y4 Y10 Y11 Y12 Y2 Y8 Y9 Y18 Y19 Y20 Y21 Y22 Y23 Y24 Y25 Y26 YK MEM KEEP AG1
      C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16 C17 C18 C19 C20 C21
      fx2 R2 M3 model3 RP DEF3 BI3 AH3).
Qed.

End WithHeap.
End PGSRDMC.
