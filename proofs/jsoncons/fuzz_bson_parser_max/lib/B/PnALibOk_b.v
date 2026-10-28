(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec StoreOk HeapIface HeapIfaceA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import IcptIfaceA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import LibIface LibIfaceAB L5Defs L5Core. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import L5DefsA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import HeapIfaceABx. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import HeapIfaceABxI_b.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmLayout PmLayoutA PnLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnLayoutA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmStatics PmStaticsA PnStatics PnStaticsA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PmSpecsA_b PnSpecsAa_b PnTopAL_b PnAHarnessStmts_b PnAHarness_b PnAStaticsTop_b PnAImgGap_b Ba0ExitCells_b Ba0MainPhaseA_b.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PNALO.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Section SCFG_1.
Context {SCFG_P : ScfgP}.

Section LibOk.
Variables (L : asan_layout) (C : asan_statics_cells) (IL : icpt_layout).
Hypothesis LY : PMA.layout L C.
Hypothesis ILY : as0_icpt_layout IL.
(* [comment removed for export] *)
Hypothesis PKG : forall ar HIR, HAJ.asan_iface_okR L ar C SCFG HIR -> aicpt_ok L ar IL SCFG HIR -> HAJ.asan_ext_ok L ar SCFG HIR PMA.EXT ->
  PMAGAP.rt_img_gap HIR -> PNHA.harness_depsA L ar HIR.

Theorem lib_ok : lib_ok_stmt SCFG L C IL PMA.EXT (PNHA.LayA L) (fun _ => PNSTA.TopLSA RSEGS PMA.AD PMA.AAD PMA.AN).
Proof.
  unfold lib_ok_stmt, lib_ext_okG. intros ar HI _ _ (HIR & EHI & HIRok & ICok & EXT & GAP). subst HI.
  split; [reflexivity|].
  pose proof (PKG ar HIR HIRok ICok EXT GAP) as DEPS.
  constructor.
  - exact (PNHA.harness_call_okA L ar C HIR IL LY HIRok ICok ILY DEPS).
  - exact (PNSTT.statics_initA L ar C LY).
  - exact (PNSTT.statics_frameA L ar).
Qed.

(* [comment removed for export] *)
Theorem lsxfa : forall (ar : asan_run) (g : PNST.st) (M : word -> option byte),
  LibIface.ls_ok ((fun _ : asan_run => PNSTA.TopLSA RSEGS PMA.AD PMA.AAD PMA.AN) ar) g M -> exists ax : axv, atexit_cellsA M ax.
Proof. intros ar g M H. exact (PNSTT.lsx_atexit ar g M H). Qed.
End LibOk.
End SCFG_1.
End PNALO.
