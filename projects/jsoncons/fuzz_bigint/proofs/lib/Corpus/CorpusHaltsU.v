(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from the shape of projects/jsoncons/fuzz_ubjson_parser_max/proofs/lib/UbjsonPmHaltsU.v at c395a1e0dfa (its ub_top, top_ubsan_closed and ubjson_pm_halts_ubsan), with that file's closing instance of ub0_realizes_spec_heap replaced by the one of projects/jsoncons/fuzz_bigint/proofs/lib/BigintFinal.v:86-89 at the same commit, its LIB1 hypothesis discharged by LIB1_of_divide OPMOD1_ub0_ok OPMOD2_ub0_ok as projects/jsoncons/fuzz_bigint/proofs/lib/BigintBase.v:83 and :89 do (BigintBaseHA.v:26 does the same with abstract arguments), and the theorem renamed bigint_pm_halts_ubsan. *)
From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit HaltsAllowed.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import ShapeAlg SpinAlg Spec BigintSpec HeapIface LibIface.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.CJ.Bridge Require Import HeapInst1 HeapClosed.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import Ub0DrvLibL Ub0DrvG Ub0DrvMain Ub0HeapBridge L5TopU BigintFinal BigintBaseH BigintBase.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.Corpus Require Import CorpusShape CorpusSpec CorpusHalts CorpusHaltsTop.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require PropExec.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section FPX_1.
#[local] Existing Instance PropExec.fx0.

Lemma ub_top : Ub0DrvMain.tgt_realizes_stmt2 cfg0.
Proof.
  exact (ub0_realizes_spec_heap cfg0 eq_refl eq_refl
           (fun sp => L5TopU.L5TOPU.TopLay (HeapInst1.L1 (bv_unsigned sp)))
           (fun sp => L5TopU.L5TOPU.TopLS (HeapInst1.L1 (bv_unsigned sp)))
           drv_lib_layout_top1 (LIB1_of_divide OPMOD1_ub0_ok OPMOD2_ub0_ok) budget1).
Qed.

Lemma top_ubsan_closed : top_ubsan cfg0 target_alloc_limit.
Proof.
  intros sp brk mbase rdraw inp Hsp Hbrk Hmb Hfit Hargv Henvp Hfs Hcreds _ _.
  exact (ub_top sp brk mbase rdraw inp Hsp Hbrk Hmb Hfit Hargv Henvp Hfs Hcreds).
Qed.

Theorem bigint_pm_halts_ubsan :
  halts_allowed_T_scfg_budgets forced_only_cfg ShippedBudgets.lim_source halts_codes
    (mkImage Ubsan.M.loaded_segments Ubsan.M.init_pc Ubsan.M.phdrs).
Proof. exact (bigint_pm_halts_ubsan_of_top cfg0 target_alloc_limit lim_source_le_target top_ubsan_closed). Qed.

End FPX_1.
