(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the launch's caps and far-end reader passed on; the library hypothesis of both CONFIG_RSEQ copies of the certificates, at the launch's mmap base too, which the start environment reads; the walks over the binaries' own segments lifted to the run's segment list by RzBridge.run_init_our). *)
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
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require RzBridge.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache.

Module TopLib.
Import TopUbs.
Module HS := TopHypsSrc.TopHypsSrc.
Module HU := TopHypsUbs.TopHypsUbs.

Lemma G0_S : forall inp sp mb rnd (Hva : valid_argv (in_argv inp)), @HS.G0_stmt inp sp mb rnd Hva.
Proof. intros inp sp mb rnd Hva. exact (@HS.G0_ok inp sp mb rnd Hva). Qed.
Lemma G0_U : forall inp sp mb rnd (Hva : valid_argv (in_argv inp)), @HU.G0_stmt inp sp mb rnd Hva.
Proof. intros inp sp mb rnd Hva. exact (@HU.G0_ok inp sp mb rnd Hva). Qed.
Lemma G0_SR : forall inp sp mb rnd (Hva : valid_argv (in_argv inp)), @HS.G0_stmtR inp sp mb rnd Hva.
Proof. intros inp sp mb rnd Hva. exact (@HS.G0_okR inp sp mb rnd Hva). Qed.
Lemma G0_UR : forall inp sp mb rnd (Hva : valid_argv (in_argv inp)), @HU.G0_stmtR inp sp mb rnd Hva.
Proof. intros inp sp mb rnd Hva. exact (@HU.G0_okR inp sp mb rnd Hva). Qed.

Lemma RZ_SRC : forall sp brk0 mb rnd inp,
  valid_core inp -> valid_entry SRC (mkEntry sp brk0 mb rnd) inp ->
  realizes (run_segments SRC_SEGS inp sp mb)
    (init_config (run_segments SRC_SEGS inp sp mb) SRC_PC SRC_PH sp brk0 mb rnd source_alloc_limit inp) (DrvShape.DrvShape.K inp).
Proof.
  intros sp brk0 mb rnd inp Hc Hen. pose proof Hc as (Hva & Hve & _ & _ & _ & _ & Hhw & Hsz & Hvl & Hrdr).
  apply RzBridge.RzBridge.run_init_our; [reflexivity|].
  exact (@HS.rz inp sp brk0 mb rnd source_alloc_limit Hva Hve Hhw Hsz Hvl Hrdr Hen ltac:(unfold source_alloc_limit; lia) (G0_S inp sp mb rnd Hva) (G0_SR inp sp mb rnd Hva)).
Qed.
Lemma RZ_UBS : forall sp brk0 mb rnd inp,
  valid_core inp -> valid_entry UBS (mkEntry sp brk0 mb rnd) inp ->
  realizes (run_segments UBS_SEGS inp sp mb)
    (init_config (run_segments UBS_SEGS inp sp mb) UBS_PC UBS_PH sp brk0 mb rnd target_alloc_limit inp) (DrvShape.DrvShape.K inp).
Proof.
  intros sp brk0 mb rnd inp Hc Hen. pose proof Hc as (Hva & Hve & _ & _ & _ & _ & Hhw & Hsz & Hvl & Hrdr).
  apply RzBridge.RzBridge.run_init_our; [reflexivity|].
  exact (@HU.rz inp sp brk0 mb rnd target_alloc_limit Hva Hve Hhw Hsz Hvl Hrdr Hen ltac:(unfold target_alloc_limit; lia) (G0_U inp sp mb rnd Hva) (G0_UR inp sp mb rnd Hva)).
Qed.

Lemma RZ_UBS_SRCLIM : forall sp brk0 mb rnd inp,
  valid_core inp -> valid_entry UBS (mkEntry sp brk0 mb rnd) inp ->
  realizes (run_segments UBS_SEGS inp sp mb)
    (init_config (run_segments UBS_SEGS inp sp mb) UBS_PC UBS_PH sp brk0 mb rnd source_alloc_limit inp) (DrvShape.DrvShape.K inp).
Proof.
  intros sp brk0 mb rnd inp Hc Hen. pose proof Hc as (Hva & Hve & _ & _ & _ & _ & Hhw & Hsz & Hvl & Hrdr).
  apply RzBridge.RzBridge.run_init_our; [reflexivity|].
  exact (@HU.rz inp sp brk0 mb rnd source_alloc_limit Hva Hve Hhw Hsz Hvl Hrdr Hen ltac:(unfold source_alloc_limit; lia) (G0_U inp sp mb rnd Hva) (G0_UR inp sp mb rnd Hva)).
Qed.

Theorem base_ubsan : strong_universal_error_free_T_scfg_budgets_abort (mkSpuriousCfg false true true true true true)
  ShippedBudgets.lim_source ShippedBudgets.lim_target SRC UBS.
Proof. exact (TopUbs.base_ubsan DrvShape.DrvShape.K (fun inp _ => DrvShape.DrvShape.K_kill_free inp) RZ_SRC RZ_UBS). Qed.
End TopLib.
