(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_bson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec StoreOk HeapIface HeapIfaceA IcptIfaceA LibIface LibIfaceAB L5Defs L5Core L5DefsA HeapIfaceABx HeapIfaceABxI
     PmLayout PmLayoutA PnLayout PnLayoutA PmStatics PmStaticsA PnStatics PnStaticsA PmSpecsA PnSpecsAa PnSpecsAmc PnSpecsAX PnRunA PnRunAa PnAImgGap
     PnTopAL PnAHarnessStmts PnAHarness PnAStaticsTop Ba0ExitCells Ba0MainPhaseA PnALibOk
     PnAStr PnAIss PnASys PnAOpnew PnAOpdel PnASrcDtor PnALoc PnAIosDtor PnAAnn PnAAnnV8 PnAVecDtor PnAVu8Dtor PnAResetBStmts.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PNACP.
Abbreviation RSEGS := Asan.M.loaded_segments.
Section SCFG_1.
Context {SCFG_P : ScfgP}.
Section Close.
Variables (L : asan_layout) (C : asan_statics_cells) (IL : icpt_layout).
Hypothesis LY : PMA.layout L C.
Hypothesis ILY : as0_icpt_layout IL.
Hypothesis MCC : PMAMC.mcmp_cells C.

(* [comment removed for export] *)
Definition inst_ok (ar : asan_run) (HIR : asan_iface) : Prop :=
  HAJ.asan_iface_okR L ar C SCFG HIR /\ aicpt_ok L ar IL SCFG HIR /\ HAJ.asan_ext_ok L ar SCFG HIR PMA.EXT /\ PMAGAP.rt_img_gap HIR.

(* [comment removed for export] *)
Hypothesis RDCTOR : forall ar HIR, inst_ok ar HIR -> PNRAa.reader_ctor_spec L ar HIR.
Hypothesis RESET : forall ar HIR, inst_ok ar HIR -> PNARBS.reset_spec L ar HIR.
Hypothesis PARSE : forall ar HIR, inst_ok ar HIR -> PNRAa.parse_spec L ar HIR.

Theorem deps_closed : forall ar HIR, inst_ok ar HIR -> PNHA.harness_depsA L ar HIR.
Proof.
  intros ar HIR IOK. pose proof IOK as (HIok & ICok & EXT & GAP).
  assert (OPN : PMA.opnew_spec L ar HIR) by (eapply PMAOPN.opnew_ok; eassumption).
  assert (OPD : PMA.opdel_spec L ar HIR) by (eapply PMAOPD.opdel_ok; eassumption).
  assert (LCC : PMA.locale_ctor_spec L ar HIR) by (eapply PMALOC.locale_ctor_ok; eassumption).
  assert (LCD : PMA.locale_dtor_spec L ar HIR) by (eapply PMALOC.locale_dtor_ok; eassumption).
  assert (IOD : PMA.ios_dtor_spec L ar HIR) by (eapply PMAID.ios_dtor_ok; eassumption).
  assert (ASH : PNSAX.ann_shrink_spec RSEGS PMA.AD L ar HIR 0xaaecc) by (eapply PNAANN.ann_shrink_ok; eassumption).
  assert (ADL : PNSAX.ann_delete_spec RSEGS PMA.AD L ar HIR 0xaae2c) by (eapply PNAANN.ann_delete_ok; eassumption).
  assert (ASH8 : PNSAX.ann_shrink_v8_spec RSEGS PMA.AD L ar HIR 0xab138) by (eapply PNAAV8.ann_shrink_v8_ok; eassumption).
  assert (ADL8 : PNSAX.ann_delete_v8_spec RSEGS PMA.AD L ar HIR 0xab098) by (eapply PNAAV8.ann_delete_v8_ok; eassumption).
  unfold PNHA.harness_depsA.
  split; [eapply PMASTR.str_ctor_ok; eassumption|].
  split; [eapply PMAISS.iss_ctor_ok; eassumption|].
  split; [exact (RDCTOR ar HIR IOK)|].
  split; [eapply PMASY.syscat_ok; eassumption|].
  split; [exact (RESET ar HIR IOK)|].
  split; [exact (PARSE ar HIR IOK)|].
  split; [eapply PNAVD.vec_dtor_ok; eassumption|].
  split; [eapply PNAV8D.vu8_dtor_ok; eassumption|].
  split; [exact OPD|].
  split; [eapply PMASD.src_dtor_ok; eassumption|].
  split; [exact LCD|].
  split; [exact IOD|].
  exact (HAJ.aex_stack_free _ _ _ _ _ EXT).
Qed.

(* [comment removed for export] *)
Theorem pkg : forall ar HIR, HAJ.asan_iface_okR L ar C SCFG HIR -> aicpt_ok L ar IL SCFG HIR -> HAJ.asan_ext_ok L ar SCFG HIR PMA.EXT ->
  PMAGAP.rt_img_gap HIR -> PNHA.harness_depsA L ar HIR.
Proof. intros ar HIR H1 H2 H3 H4. exact (deps_closed ar HIR (conj H1 (conj H2 (conj H3 H4)))). Qed.

(* [comment removed for export] *)
Theorem lib_ok3 : lib_ok_stmt SCFG L C IL PMA.EXT (PNHA.LayA L) (fun _ => PNSTA.TopLSA RSEGS PMA.AD PMA.AAD PMA.AN).
Proof. exact (PNALO.lib_ok L C IL LY ILY pkg). Qed.
End Close.
End SCFG_1.
End PNACP.
