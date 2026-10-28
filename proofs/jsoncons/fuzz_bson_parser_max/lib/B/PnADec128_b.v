(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import HeapIfaceABx PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface HeapIfaceA
     L5Defs L5Core. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import L5DefsA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.asan Require Import L5CoreA_b L5StepAR_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnLayoutA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmStatics PmStaticsA PmSpecs. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PmSpecsA_b PnSpecsAa_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnLayout PnStatics PnStaticsA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnRunA_b PnRunAa_b
     PnSpecsAXD_b PnADec128Defs_b PnADec128K_b PnADec128E_b PnADec128G_b PnADec128S_b PnADec128F_b PnADec128M_b PnADec128MidR_b IcptIfaceA_b PnADec128X_b PnADec128C3_b.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PNADEC.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Section SCFG_1.
Context {SCFG_P : ScfgP}.
Section WithHeap.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.

Theorem dec128_ok_modulo : PNADS.at_signj L ar HI -> PNADG.cold_stmt L ar HI -> @PNSAXD.dec128_spec SCFG_P RSEGS PMA.AD PMA.AN PMA.AAD L ar HI.
Proof.
  intros SIGNJ COLD. apply (PNADE.entry L ar C HI LY HIok). apply (PNADG.guards L ar C HI LY HIok); [| exact COLD].
  apply (PNADS.frame_tail L ar C HI LY HIok). exact SIGNJ.
Qed.

(* [comment removed for export] *)
Theorem dec128_ok_open : PNADM.mid_run L ar HI -> PNADK.out_stmt L ar HI -> PNADM.special_stmt L ar HI -> PNADG.cold_stmt L ar HI ->
  @PNSAXD.dec128_spec SCFG_P RSEGS PMA.AD PMA.AN PMA.AAD L ar HI.
Proof.
  intros MID OUT SPC COLD. apply dec128_ok_modulo; [| exact COLD]. exact (PNADM.signj_of L ar C HI LY HIok MID OUT SPC).
Qed.
(* [comment removed for export] *)
Theorem dec128_ok_open3 : PNADK.out_stmt L ar HI -> PNADM.special_stmt L ar HI -> PNADG.cold_stmt L ar HI ->
  @PNSAXD.dec128_spec SCFG_P RSEGS PMA.AD PMA.AN PMA.AAD L ar HI.
Proof. intros OUT SPC COLD. exact (dec128_ok_open (PNADMR.mid_run_ok L ar C HI LY HIok) OUT SPC COLD). Qed.
(* [comment removed for export] *)
Theorem dec128_ok_open2 (IL : icpt_layout) (ICok : aicpt_ok L ar IL SCFG HI) (ILY : as0_icpt_layout IL) :
  PNADK.out_stmt L ar HI -> PNADG.cold_stmt L ar HI -> @PNSAXD.dec128_spec SCFG_P RSEGS PMA.AD PMA.AN PMA.AAD L ar HI.
Proof. intros OUT COLD. exact (dec128_ok_open3 OUT (PNADX.special_ok L ar C IL HI LY HIok ICok ILY OUT) COLD). Qed.
(* [comment removed for export] *)
Theorem dec128_ok_open1 (IL : icpt_layout) (ICok : aicpt_ok L ar IL SCFG HI) (ILY : as0_icpt_layout IL) (EXT : HAJ.asan_ext_ok L ar SCFG HI PMA.EXT) :
  PNADK.out_stmt L ar HI -> @PNSAXD.dec128_spec SCFG_P RSEGS PMA.AD PMA.AN PMA.AAD L ar HI.
Proof.
  intros OUT. apply (dec128_ok_open2 IL ICok ILY OUT). apply (PNADC3.cold_ok L ar C IL HI LY HIok ICok ILY EXT).
  apply (PNADS.frame_tail L ar C HI LY HIok).
  exact (PNADM.signj_of L ar C HI LY HIok (PNADMR.mid_run_ok L ar C HI LY HIok) OUT (PNADX.special_ok L ar C IL HI LY HIok ICok ILY OUT)).
Qed.
End WithHeap.
End SCFG_1.
End PNADEC.
