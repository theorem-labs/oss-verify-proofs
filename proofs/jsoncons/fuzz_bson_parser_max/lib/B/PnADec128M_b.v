(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import HeapIfaceABx PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface HeapIfaceA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import IcptIfaceA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import LibIface
     AsanAcct AxSymExec3 AxSymExec3Sound SegRun BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA L5Core L5CoreKit L5LazyA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import L5DefsA_b.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.asan Require Import L5CoreA_b L5CoreSpecsA_b L5StepAR_b L5CoreBR_b L5ADetailHR_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmParSpecs PmLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnLayoutA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmModel PmModelFacts PmStatics PmStaticsA PmSpecs. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PmSpecsA_b PnSpecsAa_b
     PmModelFactsA_b PnStepA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmStep PgSrc PgV8. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PgSrcA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnLayout PnModel PnModelFacts PnStatics PnStaticsA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnRunA_b PnRunAa_b PnASrcKit_b PmAUarK_b PmAUar_b.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnDecFacts. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnSpecsAXD_b PnADec128Defs_b PnADec128K_b PnADec128S_b PnADec128F_b.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PNADM.
Import L5A. Import L5CA. Import L5SAR. Import PNADK.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Abbreviation mem := (word -> option byte).

Section SCFG_1.
Context {SCFG_P : ScfgP}.
Section WithHeap.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Let LYa := PMA.ly_as0 L C LY.

(* [comment removed for export] *)
Definition mid_run : Prop :=
  forall (E : dve), dkc L ar HI E ->
  forall (fx : FPState) (Rc : bvmap 5 word) (Mc : mem) (modelc : Model) (LKc : list fframe) (Ac : list (Z * Z)) (sigma : Z),
    dst L ar HI E Mc modelc LKc Ac -> L5KA.zeros_at (mrestrict (ahid Ac modelc) Mc) (vF E + 32) 144 -> 0 <= sigma <= 1 ->
    PNADD.stJ (vR E) (vsp E) (vF E) (vfirst E) sigma (vvp E) Rc ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : mem) (model' : Model) (LK' : list fframe) (A' : list (Z * Z)) (e z sd : Z),
        dst L ar HI E M' model' LK' A' ->
        PNADD.stP (vR E) (vsp E) (vF E) (vfirst E) sigma e z sd R' -> PNADD.sdigs (vF E) (mrestrict (ahid A' model') M') z sd ->
        0 <= e <= 16383 -> 0 <= z -> 1 <= sd -> z + sd <= 36 ->
        srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx' R' 0xb4294 M' model') (vK E)) ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : mem) (model' : Model) (LK' : list fframe) (A' : list (Z * Z)) (hi lo : Z),
        dst L ar HI E M' model' LK' A' ->
        PNADD.stX (vR E) (vsp E) (vF E) (vfirst E) sigma hi lo R' -> 0 <= hi < 2 ^ 64 -> 0 <= lo < 2 ^ 64 ->
        PNADD.vp_at (mrestrict (ahid A' model') M') (vvp E) lo hi ->
        srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx' R' 0xb4994 M' model') (vK E)) ->
    srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx Rc 0xb406c Mc modelc) (vK E).

(* [comment removed for export] *)
Definition special_stmt : Prop :=
  forall (E : dve), dkc L ar HI E ->
  forall (fx : FPState) (Rc : bvmap 5 word) (Mc : mem) (modelc : Model) (LKc : list fframe) (Ac : list (Z * Z)) (sigma hi lo : Z),
    dst L ar HI E Mc modelc LKc Ac -> 0 <= sigma <= 1 -> 0 <= hi < 2 ^ 64 -> 0 <= lo < 2 ^ 64 ->
    PNADD.vp_at (mrestrict (ahid Ac modelc) Mc) (vvp E) lo hi ->
    PNADD.stX (vR E) (vsp E) (vF E) (vfirst E) sigma hi lo Rc ->
    srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx Rc 0xb4994 Mc modelc) (vK E).

(* [comment removed for export] *)
Lemma out_to_end (E : dve) (X : dkc L ar HI E) (fx' : FPState) (R' : bvmap 5 word) (M' : mem) (model' : Model) (LK' : list fframe) (A' : list (Z * Z)) (ptr ec : Z) :
  dst L ar HI E M' model' LK' A' ->
  PNADD.out_post (vR E) (vsp E) (vF E) (vfl E) (vfirst E) (vr E) ptr ec R' (mrestrict (ahid A' model') M') ->
  srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx' R' 0xb46b0 M' model') (vK E).
Proof.
  intros ST (SE & _ & Hp & Hec). apply (PNADF.epilogue L ar C HI LY HIok E X fx' R' M' model' LK' A' ptr ec ST SE Hp).
  destruct Hec as [-> | ->]; clear; lia.
Qed.

Theorem signj_of : mid_run -> out_stmt L ar HI -> special_stmt -> PNADS.at_signj L ar HI.
Proof.
  intros MID OUT SPC E X fx Rc Mc modelc LKc Ac sigma ST ZS Hs RJ.
  apply (MID E X fx Rc Mc modelc LKc Ac sigma ST ZS Hs RJ).
  - intros fx' R' M3 model3 LK3 A3 e z sd ST3 SP SD He Hz Hsd Hzs.
    pose proof (dmem_of L ar C HI LY HIok E X M3 model3 LK3 A3 ST3) as (MIA3 & _).
    apply (OUT E X fx' R' M3 model3 LK3 A3 sigma e z sd ST3).
    + unfold PNADD.out_pre. split; [exact SP|]. split; [exact MIA3|]. split; [exact SD|]. split; [exact Hs|]. split; [exact He|]. split; [exact Hz|]. split; [exact Hsd| exact Hzs].
    + intros fx9 R9 M9 model9 LK9 A9 ptr ec ST9 OP9. exact (out_to_end E X fx9 R9 M9 model9 LK9 A9 ptr ec ST9 OP9).
  - intros fx' R' M3 model3 LK3 A3 hi lo ST3 SX Hhi Hlo VP.
    exact (SPC E X fx' R' M3 model3 LK3 A3 sigma hi lo ST3 Hs Hhi Hlo VP SX).
Qed.

End WithHeap.
End SCFG_1.
End PNADM.
