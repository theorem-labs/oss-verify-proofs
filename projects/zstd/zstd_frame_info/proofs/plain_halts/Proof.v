(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by gabelogan195, 2026-11: made in part from this harness's proofs/lib/HaltsAsanB.v at commit f92feaf8b7: three of its import lines (lines 5, 6 and 8) and its final step, haltsB_of_must_exit_acfg with forced_only_cfg_least (line 24, as in proofs/lib/HaltsAsanBClosed.v, line 13), restated for the plain build; the rest of the file is new. *)
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit HaltsAllowed.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.zstd.zstd_frame_info Require Statements.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib Require Import TopLevel PlainTree.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib Require Import ITree Nodes HaltsTreeB Cfg.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Spec Require Import Prog ProgExits.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Plain Require Import PImg.

(** The plain build's program tree, which the agreement proof realizes at 16 GiB, ends only
    in exits with status 0 or 2 ([prog_texits]).  So every execution of the plain build, with
    memory refused only when forced, exits with one of them. *)
Lemma plain_must_exit : forall en inp,
  valid_entry (mkImage psegs p_init_pc p_phdrs) en inp -> valid_input inp ->
  must_exit_in_scfg ACFG EXITS02 (mkImage psegs p_init_pc p_phdrs) source_alloc_limit en inp.
Proof.
  intros en inp Hen Hinp.
  pose proof (valid_input_either_of_valid_input _ Hinp) as Heither.
  destruct (plain_tree_ok en inp Hen Heither) as (Himpl & Hleaves & Hsafe).
  exact (halts_of_impl_tree_S psegs p_init_pc p_phdrs source_alloc_limit EXITS02
           (Prog.prog psegs PREAD_STAGE inp en) _ en inp Hen
           (valid_input_either_va_size _ Heither) (prog_texits _ _ _ _) Himpl Hleaves Hsafe).
Qed.

Theorem plain_halts_holds : Statements.plain_halts.
Proof.
  exact (haltsB_of_must_exit_acfg forced_only_cfg EXITS02 (mkImage psegs p_init_pc p_phdrs)
           source_alloc_limit (forced_only_cfg_least _) plain_must_exit).
Qed.
