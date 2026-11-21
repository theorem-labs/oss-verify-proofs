(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
(** * plain_halts.Thm_checksum_halts_okr: the plain build halts with status 0 or 2 (may-fail configuration)

    The proof of [plain_halts_any_exit.Thm_checksum_halts.halts_plain] with the exit set [Exits.ok_or_refused]
    in place of [AnyExit.codes]: the same walk ([S0MainHs.s0_realizes_spec_h]) realizes the same specification,
    and [OkrEnds.okr_spec_ends_in] shows that every end of it exits with status 0 or 2. *)
From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit HaltsAllowed.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From OSSVerify.Core Require Shapes.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.World Require Import Src_zlib_checksum_fuzzer_repro.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.World Require Import Tgt_checksum_fuzzer_ubsan.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit Require Import ShapeAlg Spec ShapeHalts SpecHalts S0FuzzStmt U0FuzzStmt.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.MrP0 Require S0MainHs.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.MrP0 Require U0LMainHs.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts Require Import OkrEnds.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Theorem halts_plain_okr :
  halts_allowed_T_scfg may_fail_cfg OSSVerify.Core.Shapes.Exits.ok_or_refused
    (mkImage Src_zlib_checksum_fuzzer_repro.M.loaded_segments Src_zlib_checksum_fuzzer_repro.M.init_pc Src_zlib_checksum_fuzzer_repro.M.phdrs).
Proof.
  intros [sp brk mb draw] inp Hen Hvalid.
  apply (proj2 (must_exit_in_scfg_may_fail _ _ _ _ _)). cbn [must_exit_in].
  pose proof (valid_input_va_size _ Hvalid) as Hsv48.
  rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hen.
  destruct Hen as [Hsp [Hbrk [Hmb Hfits]]]. destruct Hvalid as [Hargv [Henvp [Hfs Hrest]]].
  apply (realizes_must_exit_init _ OSSVerify.Core.Shapes.Exits.ok_or_refused _ (spec (in_argv inp) (in_fs inp))).
  - (* the launch premises, as in [plain_halts_any_exit.Thm_checksum_halts.halts_plain] *)
    assert (Hvl : valid_launch inp) by (decompose [and] Hrest; assumption).
    assert (Hcr : in_channel_reader inp = true) by (decompose [and] Hrest; assumption).
    exact (S0MainHs.s0_realizes_spec_h sp brk mb draw inp Hsp Hbrk Hargv Henvp Hfs Hvl (proj2 Hfits) Hcr).
  - apply okr_spec_ends_in.
  - reflexivity.
Qed.
