(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith Bool List Lia.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit FinInput Classifier.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import ShapeAlg.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 Val IMap Mem State Plan PlanSound.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Img Require Import ImgSrc ImgUbs.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Top Require Import TopUbs.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue Require Import DrvShape DrvTop DrvLib LibLib RunSrc RunUbs TopHypsSrc TopHypsUbs.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache.

Module TopLib.
Import TopUbs.
Module HS := TopHypsSrc.TopHypsSrc.
Module HU := TopHypsUbs.TopHypsUbs.

Lemma G0_S : forall inp sp rnd (Hva : valid_argv (in_argv inp)), @HS.G0_stmt inp sp rnd Hva.
Proof. intros inp sp rnd Hva. exact (@HS.G0_ok inp sp rnd Hva). Qed.
Lemma G0_U : forall inp sp rnd (Hva : valid_argv (in_argv inp)), @HU.G0_stmt inp sp rnd Hva.
Proof. intros inp sp rnd Hva. exact (@HU.G0_ok inp sp rnd Hva). Qed.

Lemma RZ_SRC : forall sp brk0 mb rnd inp,
  valid_core inp -> valid_entry SRC (mkEntry sp brk0 mb rnd) inp ->
  realizes SRC_SEGS (init_config SRC_SEGS SRC_PC SRC_PH sp brk0 mb rnd source_alloc_limit inp) (DrvShape.DrvShape.K inp).
Proof.
  intros sp brk0 mb rnd inp Hc Hen. pose proof Hc as (Hva & Hve & _ & _ & _ & _ & Hhw & Hsz).
  exact (@HS.rz inp sp brk0 mb rnd source_alloc_limit Hva Hve Hhw Hsz Hen ltac:(unfold source_alloc_limit; lia) (G0_S inp sp rnd Hva)).
Qed.
Lemma RZ_UBS : forall sp brk0 mb rnd inp,
  valid_core inp -> valid_entry UBS (mkEntry sp brk0 mb rnd) inp ->
  realizes UBS_SEGS (init_config UBS_SEGS UBS_PC UBS_PH sp brk0 mb rnd target_alloc_limit inp) (DrvShape.DrvShape.K inp).
Proof.
  intros sp brk0 mb rnd inp Hc Hen. pose proof Hc as (Hva & Hve & _ & _ & _ & _ & Hhw & Hsz).
  exact (@HU.rz inp sp brk0 mb rnd target_alloc_limit Hva Hve Hhw Hsz Hen ltac:(unfold target_alloc_limit; lia) (G0_U inp sp rnd Hva)).
Qed.

Lemma RZ_UBS_SRCLIM : forall sp brk0 mb rnd inp,
  valid_core inp -> valid_entry UBS (mkEntry sp brk0 mb rnd) inp ->
  realizes UBS_SEGS (init_config UBS_SEGS UBS_PC UBS_PH sp brk0 mb rnd source_alloc_limit inp) (DrvShape.DrvShape.K inp).
Proof.
  intros sp brk0 mb rnd inp Hc Hen. pose proof Hc as (Hva & Hve & _ & _ & _ & _ & Hhw & Hsz).
  exact (@HU.rz inp sp brk0 mb rnd source_alloc_limit Hva Hve Hhw Hsz Hen ltac:(unfold source_alloc_limit; lia) (G0_U inp sp rnd Hva)).
Qed.

Theorem base_ubsan : strong_universal_error_free_T_scfg_budgets_abort (mkSpuriousCfg false true true true true true)
  ShippedBudgets.lim_source ShippedBudgets.lim_target SRC UBS.
Proof. exact (TopUbs.base_ubsan DrvShape.DrvShape.K (fun inp _ => DrvShape.DrvShape.K_kill_free inp) RZ_SRC RZ_UBS). Qed.
End TopLib.
