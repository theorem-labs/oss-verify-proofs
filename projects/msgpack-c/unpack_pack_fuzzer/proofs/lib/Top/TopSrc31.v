(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith Bool List Lia.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import ShapeAlg.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Img Require Import ImgSrc.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Top Require Import TopUbs TopLib.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue Require Import DrvShape TopHypsSrc.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AS Require MainEntry MainEntryBoth.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require AImg.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW Require BImg.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require TopAsanSkel2 TopBothSkel2.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Scfg Require Import Fcfg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Module TopSrc31.
Import TopUbs.
Module HS := TopHypsSrc.TopHypsSrc.

Lemma lim31 : 2 ^ 31 <= SanitizerBudgets.lim_source.
Proof. unfold SanitizerBudgets.lim_source, sanitizer_source_limit. lia. Qed.

Lemma valid_core_of_either : forall inp, valid_input_either inp -> valid_core inp.
Proof. intros inp H. unfold valid_input_either in H. unfold valid_core. tauto. Qed.

Lemma RZ_SRC31 : forall sp brk0 mb rnd inp,
  valid_core inp -> valid_entry SRC (mkEntry sp brk0 mb rnd) inp ->
  realizes SRC_SEGS (init_config SRC_SEGS SRC_PC SRC_PH sp brk0 mb rnd SanitizerBudgets.lim_source inp) (DrvShape.DrvShape.K inp).
Proof.
  intros sp brk0 mb rnd inp Hc Hen. pose proof Hc as (Hva & Hve & _ & _ & _ & _ & Hhw & Hsz).
  exact (@HS.rz inp sp brk0 mb rnd SanitizerBudgets.lim_source Hva Hve Hhw Hsz Hen lim31 (TopLib.G0_S inp sp rnd Hva)).
Qed.

Lemma SRC_either31 : forall en inp, valid_entry (mkImage SRC_SEGS SRC_PC SRC_PH) en inp -> valid_input_either inp ->
  ~ run_scfg_budget_refused fcfg (mkImage SRC_SEGS SRC_PC SRC_PH) SanitizerBudgets.lim_source en inp ->
  realizes SRC_SEGS (init_config SRC_SEGS SRC_PC SRC_PH (en_sp en) (en_brk en) (en_mmap_base en) (en_draw en) SanitizerBudgets.lim_source inp)
           (DrvShape.DrvShape.K inp).
Proof.
  intros [sp brk0 mb rnd] inp Hen Hi _. cbn [en_sp en_brk en_mmap_base en_draw].
  exact (RZ_SRC31 sp brk0 mb rnd inp (valid_core_of_either inp Hi) Hen).
Qed.

Module AI := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AImg.
Module BI := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW.BImg.
Module ME := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AS.MainEntry.
Module MB := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AS.MainEntryBoth.

Theorem asan_base_of_main :
  (forall en inp, valid_entry (mkImage AI.asegs AI.a_init_pc AI.a_phdrs) en inp -> valid_input_either inp ->
     forall ms mo, ME.amain_at en inp ms mo -> realizes AI.asegs (mkCfg ms mo) (DrvShape.DrvShape.K inp)) ->
  strong_universal_error_free_T_scfg_budgets_abort fcfg SanitizerBudgets.lim_source SanitizerBudgets.lim_target
    (mkImage SRC_SEGS SRC_PC SRC_PH) (mkImage AI.asegs AI.a_init_pc AI.a_phdrs).
Proof. intros MAIN. exact (TopAsanSkel2.TopAsanSkel2.asan_base SRC_SEGS SRC_PC SRC_PH SRC_either31 MAIN). Qed.
Theorem both_base_of_main :
  (forall en inp, valid_entry (mkImage BI.bsegs BI.b_init_pc BI.b_phdrs) en inp -> valid_input_either inp ->
     forall ms mo, MB.bmain_at en inp ms mo -> realizes BI.bsegs (mkCfg ms mo) (DrvShape.DrvShape.K inp)) ->
  strong_universal_error_free_T_scfg_budgets_abort fcfg SanitizerBudgets.lim_source SanitizerBudgets.lim_target
    (mkImage SRC_SEGS SRC_PC SRC_PH) (mkImage BI.bsegs BI.b_init_pc BI.b_phdrs).
Proof. intros MAIN. exact (TopBothSkel2.TopBothSkel2.both_base SRC_SEGS SRC_PC SRC_PH SRC_either31 MAIN). Qed.
End TopSrc31.
