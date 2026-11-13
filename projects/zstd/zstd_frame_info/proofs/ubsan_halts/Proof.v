(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by gabelogan195, 2026-11: made in part from this harness's proofs/lib/HaltsAsanB.v at commit f92feaf8b7: three of its import lines (lines 5, 6 and 8) and its final step, haltsB_of_must_exit_acfg with forced_only_cfg_least (line 24, as in proofs/lib/HaltsAsanBClosed.v, line 13), restated for the UBSan build; one step is proofs/lib/UbsanMain.v, line 24, with a hypothesis renamed, and the facts it passes are those of proofs/lib/Spec/ModelOK.v, line 55; the rest of the file is new. *)
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit HaltsAllowed.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.zstd.zstd_frame_info Require Statements.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib Require Import TopLevel.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib Require Import ITree Nodes HaltsTreeB Cfg.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Spec Require Import Prog ProgExits ModelOK ImgFacts.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Ubsan Require Import UImg.
Require OSSVerify.Proofs.zstd.zstd_frame_info.lib.Ubsan.PlainClosed.

(** The UBSan build realizes the same program tree as the plain build.  The agreement proof
    shows it at 512 GiB; [prog_model_ok] holds at any budget of at least 2 GiB, so it holds at
    16 GiB as well, and the tree ends only in exits with status 0 or 2 ([prog_texits]). *)
Lemma ubsan_must_exit : forall en inp,
  valid_entry (mkImage usegs u_init_pc u_phdrs) en inp -> valid_input inp ->
  must_exit_in_scfg ACFG EXITS02 (mkImage usegs u_init_pc u_phdrs) source_alloc_limit en inp.
Proof.
  intros en inp Hen Hinp.
  pose proof (valid_input_either_of_valid_input _ Hinp) as Heither.
  destruct (prog_model_ok usegs UREAD_STAGE u_init_pc u_phdrs source_alloc_limit en inp
              top_pos_ubsan ceil_ubsan floor_ubsan resv_ubsan lim_p Hen Heither)
    as [Hleaves Hsafe].
  exact (halts_of_impl_tree_S usegs u_init_pc u_phdrs source_alloc_limit EXITS02
           (Prog.prog usegs UREAD_STAGE inp en) _ en inp Hen
           (valid_input_either_va_size _ Heither) (prog_texits _ _ _ _)
           (OSSVerify.Proofs.zstd.zstd_frame_info.lib.Ubsan.PlainClosed.plain_impl_closed
              en inp Hen Heither)
           Hleaves Hsafe).
Qed.

Theorem ubsan_halts_holds : Statements.ubsan_halts.
Proof.
  exact (haltsB_of_must_exit_acfg forced_only_cfg EXITS02 (mkImage usegs u_init_pc u_phdrs)
           source_alloc_limit (forced_only_cfg_least _) ubsan_must_exit).
Qed.
