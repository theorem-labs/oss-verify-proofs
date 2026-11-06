(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: made from proofs/cgif/cgif_file_fuzzer/lib/A/AZ03.v and lib/Halts_tfib.v for fuzz_decode, by way of fuzz_grant's lib/A/AsanTop.v: the plain side is fuzz_decode's proved realization (built as its lib/AgreeFrame.v builds it for the ubsan agreement, with the plain slot contract of lib/Prog/LLVMFuzzerTestOneInput_gfr.v, at decode_shape), the halting corollary takes srealizes, module paths changed. *)
(* Modified by Theorem Labs, 2026-10: copied from libreac/fuzz_decode's lib/A/AsanTop.v (section a, the ASan image) for fuzz_frame: the plain side is the named hypothesis frame_plain_rz_stmt (A/FrameShape.v) until the plain build's realization at frame_shape is proved; module paths changed. *)
(* fuzz_frame's two image-A statements from the ASan side TFIB_T (FrameTFIB.v) and the plain side frame_plain_rz_stmt,
   in the form of proofs/cgif/cgif_file_fuzzer/lib/A/AZ03.v (agreement) and lib/Halts_tfib.v (halting):
   - asan_agrees: shape_strong_equiv_efs_relim (Reusable/YM09.v) over the plain build's realization of SPECX at 2^34
     (frame_plain_rz_stmt), the statement's plain budget premise, TFIB_T and t_eq_refl;
   - asan_halts: halts_budgets_of_srealizes (Reusable/HaltsKitB.v) over TFIB_T and SPECX_shape_ok (HaltsSpecF.v). *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit HaltsAllowed.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Core Require Import Shapes.
From OSSVerify.libdiginet.fuzz_transport Require Statements Images.
From OSSVerify.libdiginet.fuzz_transport.images Require Plain Asan.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
  YK11 YK15 YK18 YM05 YM09 YO09 YO06 HaltsKitB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib Require Import Agree.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import TransportShape TransportTFIB HaltsSpecT.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require AB1v.
Import ListNotations.
Open Scope Z_scope.
#[local] Existing Instance YK11.fx0.

Module TSt := OSSVerify.libdiginet.fuzz_transport.Statements.
Module TIm := OSSVerify.libdiginet.fuzz_transport.Images.
Module TPl := OSSVerify.libdiginet.fuzz_transport.images.Plain.
Module TAs := OSSVerify.libdiginet.fuzz_transport.images.Asan.

Lemma asan_lim_source_le : SanitizerBudgets.lim_source <= ShippedBudgets.lim_source.
Proof. unfold SanitizerBudgets.lim_source, sanitizer_source_limit, ShippedBudgets.lim_source, source_alloc_limit. cbn. lia. Qed.

Lemma lim_source_le_target : ShippedBudgets.lim_source <= target_alloc_limit.
Proof. unfold ShippedBudgets.lim_source, source_alloc_limit, target_alloc_limit. cbn. lia. Qed.

Section a.
Hypothesis PLAIN : transport_plain_rz_stmt.
Hypothesis TFIB : TFIB_T.

Theorem transport_asan_agrees_of_tfib : TSt.asan_agrees.
Proof.
  unfold TSt.asan_agrees, agrees_in.
  intros en_s [sp' brk' mb' rnd'] inp Hens Hent Hinp SWB.
  pose proof (PLAIN en_s inp Hens Hinp) as HP.
  destruct en_s as [sp brk mb rnd].
  pose proof (valid_input_va_size _ Hinp) as Hsv48.
  unfold TIm.asan in Hent.
  rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hent. destruct Hent as [Hsp' [Hbrk' [Hmb' Hfit']]].
  exact (shape_strong_equiv_efs_relim SanitizerBudgets.lim_source ShippedBudgets.lim_source SanitizerBudgets.lim_target
    TPl.M.loaded_segments TPl.M.init_pc TPl.M.phdrs sp brk mb rnd
    AB1v.tfibsegs TAs.M.init_pc TAs.M.phdrs sp' brk' mb' rnd'
    (SPECX (LS:=transport_shape) inp) (SPECX (LS:=transport_shape) inp) inp
    asan_lim_source_le SWB HP (TFIB sp' brk' mb' rnd' inp Hsp' Hbrk' Hmb' Hfit' Hinp) (t_eq_refl _)).
Qed.

Theorem transport_asan_halts_of_tfib : TSt.asan_halts.
Proof.
  unfold TSt.asan_halts, TIm.asan.
  change (halts_allowed_T_scfg_budgets forced_only_cfg ShippedBudgets.lim_source Exits.ok_or_refused
    (mkImage AB1v.tfibsegs TAs.M.init_pc TAs.M.phdrs)).
  apply (halts_budgets_of_srealizes forced_only_cfg Exits.ok_or_refused AB1v.tfibsegs TAs.M.init_pc TAs.M.phdrs
    target_alloc_limit ShippedBudgets.lim_source lim_source_le_target (forced_only_cfg_least _)).
  intros sp brk mb rnd inp Hen Hinp. exists (SPECX (LS:=transport_shape) inp). split.
  - pose proof (valid_input_va_size _ Hinp) as Hsv48.
    rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hen. destruct Hen as [Hsp [Hbrk [Hmb Hfit]]].
    exact (TFIB sp brk mb rnd inp Hsp Hbrk Hmb Hfit Hinp).
  - exact (SPECX_shape_ok inp).
Qed.
End a.
