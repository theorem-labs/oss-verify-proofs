(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: made from proofs/cgif/cgif_file_fuzzer/lib/A/AZ03.v and lib/Halts_tfib.v for fuzz_decode, by way of fuzz_grant's lib/A/AsanTop.v: the plain side is fuzz_decode's proved realization (built as its lib/AgreeFrame.v builds it for the ubsan agreement, with the plain slot contract of lib/Prog/LLVMFuzzerTestOneInput_gfr.v, at decode_shape), the halting corollary takes srealizes, module paths changed. *)
(* Modified by Theorem Labs, 2026-10: made from Section b of proofs/libreac/fuzz_decode/lib/A/AsanTop.v at recipes commit
   88154566652a (itself from proofs/cgif/cgif_file_fuzzer/lib/A/AZ03.v and lib/Halts_tfib.v, by way of fuzz_grant's
   lib/A/AsanTop.v), in the form of reac-repacer/fuzz_uci's image-B Section b, for libdiginet/fuzz_frame's ASan+UBSan
   image: TFIB_TB is lib/B/FrameTFIB.v's; the plain build's realization is the Section hypothesis PRZ of the shared
   statement lib/A/FrameShape.v frame_plain_rz_stmt (fuzz_decode proves it in place as decode_plain_rz);
   SPECX_shape_ok is the shared lib/A/HaltsSpecF.v's; no file this one Requires states a fact of the ASan image; names
   and module paths changed. *)
(* Modified by Theorem Labs, 2026-10: made from libdiginet/fuzz_frame lib/B/AsanUbsanTop.v (file sha256 57af27c925c3;
   donor not released) for libdiginet/fuzz_transport's ASan+UBSan image: TFIB_TB is lib/B/TransportTFIBB.v's; the plain
   build's realization is the Section hypothesis PRZ of the shared statement lib/A/TransportShape.v
   transport_plain_rz_stmt; SPECX_shape_ok is the shared lib/A/HaltsSpecT.v's; names and module paths changed. *)
(* fuzz_transport's two ASan+UBSan statements from the ASan+UBSan side TFIB_TB (lib/B/TransportTFIBB.v), in the form of
   proofs/cgif/cgif_file_fuzzer/lib/A/AZ03.v (agreement) and lib/Halts_tfib.v (halting):
   - asan_ubsan_agrees: shape_strong_equiv_efs_relim (Reusable/YM09.v) over the plain build's realization of SPECX at
     2^34 (PRZ), the statement's plain budget premise, TFIB_TB and t_eq_refl;
   - asan_ubsan_halts: halts_budgets_of_srealizes (Reusable/HaltsKitB.v) over TFIB_TB and SPECX_shape_ok
     (lib/A/HaltsSpecT.v). *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit HaltsAllowed.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Core Require Import Shapes.
From OSSVerify.libdiginet.fuzz_transport Require Statements Images.
From OSSVerify.libdiginet.fuzz_transport.images Require Plain AsanUbsan.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
  YK11 YK15 YK18 YM05 YM09 YO09 YO06 HaltsKitB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import TransportShape HaltsSpecT.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import TransportTFIBB.
Import ListNotations.
Open Scope Z_scope.
#[local] Existing Instance YK11.fx0.

Module TSt := OSSVerify.libdiginet.fuzz_transport.Statements.
Module TIm := OSSVerify.libdiginet.fuzz_transport.Images.
Module TPl := OSSVerify.libdiginet.fuzz_transport.images.Plain.
Module TBU := OSSVerify.libdiginet.fuzz_transport.images.AsanUbsan.

Lemma b_asan_lim_source_le : SanitizerBudgets.lim_source <= ShippedBudgets.lim_source.
Proof. unfold SanitizerBudgets.lim_source, sanitizer_source_limit, ShippedBudgets.lim_source, source_alloc_limit. cbn. lia. Qed.

Lemma b_lim_source_le_target : ShippedBudgets.lim_source <= target_alloc_limit.
Proof. unfold ShippedBudgets.lim_source, source_alloc_limit, target_alloc_limit. cbn. lia. Qed.

Section b.
Hypothesis PRZ : transport_plain_rz_stmt.
Hypothesis TFIBB : TFIB_TB.

Theorem transport_asan_ubsan_agrees_of_tfib : TSt.asan_ubsan_agrees.
Proof.
  unfold TSt.asan_ubsan_agrees, agrees_in.
  intros en_s [sp' brk' mb' rnd'] inp Hens Hent Hinp SWB.
  pose proof (PRZ en_s inp Hens Hinp) as HP.
  destruct en_s as [sp brk mb rnd].
  pose proof (valid_input_va_size _ Hinp) as Hsv48.
  unfold TIm.asan_ubsan in Hent.
  rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hent. destruct Hent as [Hsp' [Hbrk' [Hmb' Hfit']]].
  exact (shape_strong_equiv_efs_relim SanitizerBudgets.lim_source ShippedBudgets.lim_source SanitizerBudgets.lim_target
    TPl.M.loaded_segments TPl.M.init_pc TPl.M.phdrs sp brk mb rnd
    transportsegsB0 TBU.M.init_pc TBU.M.phdrs sp' brk' mb' rnd'
    (SPECX (LS:=transport_shape) inp) (SPECX (LS:=transport_shape) inp) inp
    b_asan_lim_source_le SWB HP (TFIBB sp' brk' mb' rnd' inp Hsp' Hbrk' Hmb' Hfit' Hinp) (t_eq_refl _)).
Qed.

Theorem transport_asan_ubsan_halts_of_tfib : TSt.asan_ubsan_halts.
Proof.
  unfold TSt.asan_ubsan_halts, TIm.asan_ubsan.
  change (halts_allowed_T_scfg_budgets forced_only_cfg ShippedBudgets.lim_source Exits.ok_or_refused
    (mkImage transportsegsB0 TBU.M.init_pc TBU.M.phdrs)).
  apply (halts_budgets_of_srealizes forced_only_cfg Exits.ok_or_refused transportsegsB0 TBU.M.init_pc
    TBU.M.phdrs target_alloc_limit ShippedBudgets.lim_source b_lim_source_le_target (forced_only_cfg_least _)).
  intros sp brk mb rnd inp Hen Hinp. exists (SPECX (LS:=transport_shape) inp). split.
  - pose proof (valid_input_va_size _ Hinp) as Hsv48.
    rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hen. destruct Hen as [Hsp [Hbrk [Hmb Hfit]]].
    exact (TFIBB sp brk mb rnd inp Hsp Hbrk Hmb Hfit Hinp).
  - exact (SPECX_shape_ok inp).
Qed.
End b.
