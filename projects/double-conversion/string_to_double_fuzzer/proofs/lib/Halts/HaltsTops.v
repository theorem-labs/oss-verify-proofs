(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from projects/fast_float/from_chars/proofs/lib/TopHaltsA.v and its sibling
   TopHaltsB.v at commit c395a1e0dfa, lines 4-6 (the Stdlib/LPS import block), lines 14-15 (lim_source_le_target,
   verbatim) and lines 17-19 of each (the halts_allowed_T_scfg_budgets theorem statement), with from_chars's Asan and
   AsanUbsan images replaced by this harness's Plain and Ubsan, SpecHalts.HALT_CODES by this tree's HALT_CODES, and the
   theorem names by halts_skcms_iccprofile_info_plain and _ubsan.  The proof bodies are not copied: from_chars's single
   halts_allowed_lowered_of_realizes call is replaced here by HaltsBridge.halts_of_realizes_spec for the plain build and
   by must_exit_of_realizes_spec composed with Halts.Lim.LimTransfer.lim_transfer_scfg for the UBSan build. *)
(* Modified by gabelogan195, 2026-11: made from projects/skcms/iccprofile_info/proofs/lib/Halts/HaltsTops.v at commit f92feaf8b7 (its import block, lim_source_le_target verbatim, and the UBSan theorem's composition of the bridge with Halts.Lim.LimTransfer.lim_transfer_scfg), restated as Statements.plain_halts, Statements.plain_halts_may_fail and Statements.ubsan_halts of double-conversion/string_to_double_fuzzer, over this folder's closed realizations RefMainClosed.ref_realizes_spec_closed (at RefLim.SrcLim) and UbMainClosed.ref_realizes_spec_closed; the may-fail theorem and halt_codes_any are new. *)
(** The halting theorems of this harness, in the form [Statements.v] states them.

    The plain build's realization is proved for every budget of 2 GiB or
    more, so it is taken at 16 GiB, where both of its halting statements
    are judged, and its halting theorems are the walk of [HaltsBridge] and
    nothing else.  The UBSan build's realization is proved at 512 GiB (it is
    the TARGET of the ubsan pair), and [Statements.ubsan_halts] asks for
    16 GiB, so the walk is followed by the budget transfer of
    [Halts.Lim.LimTransfer]: a run that must exit at the larger budget must
    exit at the smaller one on every input the smaller budget never refuses,
    which is exactly the statement's own premise. *)

From Stdlib Require Import ZArith NArith List Lia.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit HaltsAllowed.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
Require OSSVerify.double_conversion.string_to_double_fuzzer.Statements.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import ImgP ImgU LibIface LxLib RefLim ShapeAlg Spec.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require RefMainClosed UbMainClosed.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.Halts Require Import SpecHalts HaltsBridge.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.Halts.Lim Require Import LimTransfer.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma lim_source_le_target : (ShippedBudgets.lim_source <= target_alloc_limit)%Z.
Proof. vm_compute. discriminate. Qed.

Lemma plain_realizes :
  realizes_spec_at ImgP.M.loaded_segments ImgP.M.init_pc ImgP.M.phdrs source_alloc_limit.
Proof. exact (RefMainClosed.ref_realizes_spec_closed (AL:=SrcLim) lib_P). Qed.

Lemma ubsan_realizes :
  realizes_spec_at ImgU.M.loaded_segments ImgU.M.init_pc ImgU.M.phdrs target_alloc_limit.
Proof. exact (UbMainClosed.ref_realizes_spec_closed lib_U). Qed.

Lemma halt_codes_any : forall code, In code HALT_CODES -> In code AnyExit.codes.
Proof.
  intros code Hc. unfold HALT_CODES in Hc. cbn [In] in Hc.
  unfold AnyExit.codes.
  destruct Hc as [<- | [<- | []]].
  - apply (in_byte_codes 0). lia.
  - apply (in_byte_codes 2). lia.
Qed.

Theorem plain_halts_thm : OSSVerify.double_conversion.string_to_double_fuzzer.Statements.plain_halts.
Proof.
  intros en inp Hen Hinp _.
  exact (must_exit_in_scfg_of_realizes_spec forced_only_cfg _ _ _ _ plain_realizes en inp Hen Hinp).
Qed.

Theorem plain_halts_may_fail_thm :
  OSSVerify.double_conversion.string_to_double_fuzzer.Statements.plain_halts_may_fail.
Proof.
  intros en inp Hen Hinp.
  apply (must_exit_in_scfg_mono_set may_fail_cfg HALT_CODES).
  - exact halt_codes_any.
  - exact (must_exit_in_scfg_of_realizes_spec may_fail_cfg _ _ _ _ plain_realizes en inp Hen Hinp).
Qed.

Theorem ubsan_halts_thm : OSSVerify.double_conversion.string_to_double_fuzzer.Statements.ubsan_halts.
Proof.
  intros en inp Hen Hinp Hbud.
  exact (lim_transfer_scfg forced_only_cfg HALT_CODES
           (mkImage ImgU.M.loaded_segments ImgU.M.init_pc ImgU.M.phdrs) en inp
           ShippedBudgets.lim_source target_alloc_limit lim_source_le_target
           (must_exit_in_scfg_of_realizes_spec forced_only_cfg _ _ _ _ ubsan_realizes en inp Hen Hinp)
           Hbud).
Qed.
