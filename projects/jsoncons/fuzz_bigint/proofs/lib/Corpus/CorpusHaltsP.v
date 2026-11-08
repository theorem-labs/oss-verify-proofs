(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from the shape of projects/jsoncons/fuzz_ubjson_parser_max/proofs/lib/UbjsonPmHaltsS.v at c395a1e0dfa (its src_top, top_plain_closed and ubjson_pm_halts_plain), with that file's closing instance of src0_realizes_spec_heap replaced by the one of projects/jsoncons/fuzz_bigint/proofs/lib/BigintTopA.v:58-61 at the same commit, and the theorem renamed bigint_pm_halts_plain. *)
From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit HaltsAllowed.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import ShapeAlg SpinAlg Spec BigintSpec HeapIface LibIface.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.CJ.Bridge Require Import HeapInst0 HeapClosed.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import Src0DrvLibL Src0DrvG Src0DrvMain Src0HeapBridge L5Top BigintFinal BigintBaseH BigintBaseS0.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.Corpus Require Import CorpusShape CorpusSpec CorpusHalts CorpusHaltsTop.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require PropExec.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section FPX_1.
#[local] Existing Instance PropExec.fx0.

Lemma src_top : Src0DrvMain.src_realizes_stmt2 cfg0.
Proof.
  exact (src0_realizes_spec_heap cfg0 eq_refl eq_refl
           (fun sp => L5Top.L5TOP.TopLay (HeapInst0.L0 (bv_unsigned sp)))
           (fun sp => L5Top.L5TOP.TopLS (HeapInst0.L0 (bv_unsigned sp)))
           drv_lib_layout_top0 (LIB0_of_divide OPMOD1_src0_ok OPMOD2_src0_ok) budget0).
Qed.

Lemma top_plain_closed : top_plain cfg0 source_alloc_limit.
Proof.
  intros sp brk mbase rdraw inp Hsp Hbrk Hmb Hfit Hargv Henvp Hfs Hcreds _ _.
  exact (src_top sp brk mbase rdraw inp Hsp Hbrk Hmb Hfit Hargv Henvp Hfs Hcreds).
Qed.

Theorem bigint_pm_halts_plain :
  halts_allowed_T_scfg_budgets forced_only_cfg ShippedBudgets.lim_source halts_codes
    (mkImage Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs).
Proof. exact (bigint_pm_halts_plain_of_top cfg0 source_alloc_limit lim_source_le_source top_plain_closed). Qed.

End FPX_1.
