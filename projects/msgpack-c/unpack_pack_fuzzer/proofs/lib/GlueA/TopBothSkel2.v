(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith Bool List Lia.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics StackLayout Fs State Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib Require TopLevel.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require TopLevelGen.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AS Require MainEntryBoth ShapeAlg SpinAlg.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW Require BImg.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require ShapeAlg.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 Val IMap Mem Instr State.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue Require Import StackInit InitLib DrvShape.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require Import LinZ InitAsanLib RootBoth2 RootBothN InitBoth2 InitBothN RzBridge.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Scfg Require Import Fcfg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import Val St.
Open Scope Z_scope.

Module TopBothSkel2.
Module OUR := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.ShapeAlg.
Module TG := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.TopLevelGen.
Module ME := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AS.MainEntryBoth.
Module AI := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW.BImg.

Section Skel.

Variables (ssegs : list Segment) (spc : N) (sph : PhdrInfo).

Hypothesis SRC : forall en inp, valid_entry (mkImage ssegs spc sph) en inp -> valid_input_either inp ->
  ~ run_scfg_budget_refused fcfg (mkImage ssegs spc sph) SanitizerBudgets.lim_source en inp ->
  OUR.realizes ssegs (init_config ssegs spc sph (en_sp en) (en_brk en) (en_mmap_base en) (en_draw en) SanitizerBudgets.lim_source inp) (DrvShape.K inp).

Hypothesis MAIN : forall en inp, valid_entry (mkImage AI.bsegs AI.b_init_pc AI.b_phdrs) en inp -> valid_input_either inp ->
  forall ms mo, ME.bmain_at en inp ms mo -> OUR.realizes AI.bsegs (mkCfg ms mo) (DrvShape.K inp).

Definition TK : TG.tfam := fun inp _ => DrvShape.K inp.

Theorem both_base : strong_universal_error_free_T_scfg_budgets_abort fcfg SanitizerBudgets.lim_source SanitizerBudgets.lim_target
  (mkImage ssegs spc sph) (mkImage AI.bsegs AI.b_init_pc AI.b_phdrs).
Proof.
  apply (TG.side_ok_equiv_budgets_abort_gen SanitizerBudgets.lim_source SanitizerBudgets.lim_target ssegs spc sph AI.bsegs AI.b_init_pc AI.b_phdrs TK TK).
  - apply TG.side_ok_p_of_srealizes. intros en inp Hv Hi HB. apply RzBridge.srealizes_bridge. exact (SRC en inp Hv Hi HB).
  - apply ME.both_side_ok. intros en inp Hv Hi. split; [exact (DrvShape.K_nil inp)|].
    intros ms mo HM. apply RzBridge.srealizes_bridge. exact (MAIN en inp Hv Hi ms mo HM).
  - intros inp en tr Htr sig fs Hin. exact (DrvShape.K_kill_free inp tr sig fs Htr Hin).
  - intros enS enT inp _ _ _ tr. reflexivity.
Qed.

End Skel.
End TopBothSkel2.
