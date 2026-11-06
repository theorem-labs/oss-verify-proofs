(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_bson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import HeapIfaceABx PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface HeapIfaceA
     L5Defs L5Core L5DefsA L5CoreA L5StepAR PmLayout PnLayoutA PmStatics PmStaticsA PmSpecs PmSpecsA PnSpecsAa PnLayout PnStatics PnStaticsA PnRunA PnRunAa
     PnSpecsAXD PnADec128Defs PnADec128K PnADec128E PnADec128G PnADec128S PnADec128F PnADec128M PnADec128MidR IcptIfaceA PnADec128X PnADec128C3.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PNADEC.
Abbreviation RSEGS := Asan.M.loaded_segments.
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
Proof. intros OUT SPC COLD. exact (dec128_ok_open (PNADMR.mid_run_ok L ar HI) OUT SPC COLD). Qed.
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
  exact (PNADM.signj_of L ar C HI LY HIok (PNADMR.mid_run_ok L ar HI) OUT (PNADX.special_ok L ar C IL HI LY HIok ICok ILY OUT)).
Qed.
End WithHeap.
End SCFG_1.
End PNADEC.
