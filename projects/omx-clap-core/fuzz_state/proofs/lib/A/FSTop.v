(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: made from proofs/cgif/cgif_file_fuzzer/lib/A/AZ03.v and lib/Halts_tfib.v for fuzz_state, in the form proofs/libreac/fuzz_grant/lib/A/AsanTop.v:91-129 (a working branch c2edc13c0fa) gives them: the plain side is fuzz_state's proved realization (lib/FSPlain.v), the shape is ag_shape checksum_shape, the halting corollary takes srealizes, module paths changed. *)
(* Qed modulo TFIB_T (lead 20:39Z: discharged by porting cgif_file's closed AD1q / AD2p walk).
   OPEN: TFIB_T (the ASan side of fs.asan: from every valid start, fs.asan's init_config at target_alloc_limit
   srealizes SPECX (LS:=ag_shape checksum_shape), lib/A/FSTfib.v). It is the ONE premise of both theorems below
   (Section a's hypothesis TFIB; invisible to Print Assumptions, so it is named here). What will discharge it:
   - the relocated cgif_file ASan core: lib/A and the lib/Reusable files of the raw copy d579ce160e2 (runtime,
     allocator model, start-up, driver), moved from cgif_file.asan to fs.asan by lane RELOC, with fs's start-up
     certificate;
   - fs's per-function walks, lanes ALLOC / READER / WRITER / CNO / CRT / CHECKS / ENTRY / RUNTIME, composed by
     ENTRY (a Theorem Labs lane) into fs_lib_contract_x and then into TFIB_T;
   - open inputs INSIDE TFIB_T, each a named hypothesis with an owner (table 'Named hypotheses' in
     (internal path)); none is a hypothesis of these theorems:
     * FS_AREALLOC_A: fs's ASan realloc contract (call target __wrap_realloc 0x53078, which jumps to
       __interceptor_realloc 0x53474; trace ipc 0x53594). The donor model has no realloc (YG0f.v:134-178 asyms,
       YG00.v ops, YG0d.v contracts, ACej.v:337 universe). Owner a Theorem Labs lane; model
       lib/A/FSH_ReallocModel.v (a working branch a882c264dfa); discharge: a Theorem Labs lane
       arealloc_realizes_all (a working branch). fs needs 1 <= n < MALLOC_MAX; cgif_rgb's
       arealloc_realizes needs 64513 <= n (YG0f.v:221-230).
     * FS_DOC_STRS: two clauses about the document round_trip_document builds (fs.c:229-247: its keys and string
       values; they keep parse_value off its number arm, so strtod is unreachable). Owner a Theorem Labs lane, lane READER,
       proof in lib/A/Prog/FSDocStrs.v; discharge: a model-level lemma over the document value plus the byte-level
       no-backslash clause via WRITER's exact-bytes post.
   NOT open: the plain realloc arm. The plain side is fs's own released plain realization (lib/FSPlain.v from
   AgreeTop.v:16 plain_rz_of_contracts_R), whose proof covers realloc (fs's lib/Reusable/YH02.v ms_realloc =
   Some src0_A_realloc); the donor's YH02.v:20-23 (ms_realloc = None) and YO0d.v:434-444 are not in its closure.
   fuzz_state's two ASan statements from TFIB_T, in the form of cgif_file lib/A/AZ03.v (agreement) and
   lib/Halts_tfib.v (halting):
   - asan_agrees: shape_strong_equiv_efs_relim (Reusable/YM09.v) over the plain build's proved realization of SPECX
     at 2^34 (FSPlain.fs_plain_rz), the statement's plain budget premise (which also discharges the plain
     realization's cuts, lib/A/RelimCut.v), TFIB_T and t_eq_refl (both sides at ag_shape checksum_shape);
   - asan_halts: halts_budgets_of_srealizes (Reusable/HaltsKitB.v) over TFIB_T and SPECX_shape_ok (FSHaltsSpec.v). *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit HaltsAllowed.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Core Require Import Shapes.
From OSSVerify.omx_clap_core.fuzz_state Require Statements Images.
From OSSVerify.omx_clap_core.fuzz_state.images Require Plain Asan.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
  YK11 YK15 YK18 YM05 YM09 YO09 YO06 HaltsKitB.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib Require Import Agree AgreeTop AgreeShape ZTraceSpec
  FSPlain FSHaltsSpec.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import FSTfib.
Import ListNotations.
Open Scope Z_scope.
#[local] Existing Instance YK11.fx0.

Lemma asan_lim_source_le : SanitizerBudgets.lim_source <= ShippedBudgets.lim_source.
Proof. unfold SanitizerBudgets.lim_source, sanitizer_source_limit, ShippedBudgets.lim_source, source_alloc_limit. cbn. lia. Qed.

Lemma lim_source_le_target : ShippedBudgets.lim_source <= target_alloc_limit.
Proof. unfold ShippedBudgets.lim_source, source_alloc_limit, target_alloc_limit. cbn. lia. Qed.

Section a.
Hypothesis TFIB : TFIB_T.

Theorem fs_asan_agrees_of_tfib : Statements.asan_agrees.
Proof.
  unfold Statements.asan_agrees, agrees_in.
  intros en_s [sp' brk' mb' rnd'] inp Hens Hent Hinp SWB.
  pose proof (fs_plain_rz en_s inp Hens Hinp) as HP.
  destruct en_s as [sp brk mb rnd].
  pose proof (valid_input_va_size _ Hinp) as Hsv48.
  unfold Images.asan in Hent.
  rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hent. destruct Hent as [Hsp' [Hbrk' [Hmb' Hfit']]].
  exact (shape_strong_equiv_efs_relim SanitizerBudgets.lim_source ShippedBudgets.lim_source SanitizerBudgets.lim_target
    Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs sp brk mb rnd
    fssegs0 Asan.M.init_pc Asan.M.phdrs sp' brk' mb' rnd'
    (SPECX (LS:=ag_shape checksum_shape) inp) (SPECX (LS:=ag_shape checksum_shape) inp) inp
    asan_lim_source_le SWB HP (TFIB sp' brk' mb' rnd' inp Hsp' Hbrk' Hmb' Hfit' Hinp) (t_eq_refl _)).
Qed.

Theorem fs_asan_halts_of_tfib : Statements.asan_halts.
Proof.
  unfold Statements.asan_halts, Images.asan.
  change (halts_allowed_T_scfg_budgets forced_only_cfg ShippedBudgets.lim_source Exits.ok_or_refused
    (mkImage fssegs0 Asan.M.init_pc Asan.M.phdrs)).
  apply (halts_budgets_of_srealizes forced_only_cfg Exits.ok_or_refused fssegs0 Asan.M.init_pc Asan.M.phdrs
    target_alloc_limit ShippedBudgets.lim_source lim_source_le_target (forced_only_cfg_least _)).
  intros sp brk mb rnd inp Hen Hinp. exists (SPECX (LS:=ag_shape checksum_shape) inp). split.
  - pose proof (valid_input_va_size _ Hinp) as Hsv48.
    rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hen. destruct Hen as [Hsp [Hbrk [Hmb Hfit]]].
    exact (TFIB sp brk mb rnd inp Hsp Hbrk Hmb Hfit Hinp).
  - exact (SPECX_shape_ok inp).
Qed.
End a.

Check fs_asan_agrees_of_tfib.
Check fs_asan_halts_of_tfib.
Print Assumptions fs_asan_agrees_of_tfib.
Print Assumptions fs_asan_halts_of_tfib.
