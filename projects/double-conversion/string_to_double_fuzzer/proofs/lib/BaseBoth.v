(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by gabelogan195, 2026-11: made from this folder's BothTop.v (the proof of both_top_abort) and BaseUbsan.v (the proof of ubsan_base) at commit f92feaf8b7: the plain/ASan+UBSan agreement stated as LPS's strong_universal_error_free_T, at LPS's own budgets and with neither a budget premise nor the abort reading, with the plain build's realization taken at RefLim.SrcLim (16 GiB) where BothClosed takes SanLim, and shape_strong_equiv_efs in place of shape_strong_equiv_efs_abort; the bound and decidability theorems apply ConstAccept's lemmas to it, as ConstAccept does for the UBSan build. *)
(** As [BaseAsan], for the ASan+UBSan build: the plain and ASan+UBSan builds
    agree on every input at 16 GiB / 512 GiB with no budget premise, so no
    input disagrees ([both_bound_0]) and the constant classifier of
    [ConstAccept] decides the agreeing inputs ([both_decidable]). *)

From Stdlib Require Import QArith.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Core Require Import Shapes.
Require OSSVerify.double_conversion.string_to_double_fuzzer.Images.
Require OSSVerify.double_conversion.string_to_double_fuzzer.Statements.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import
  ImgP ImgB ImgSame LibIface LxLib RefLim ShapeAlg SpinAlg Spec ShapeEFS
  LbLibBClosed BothTop BothObls BothCertsAll.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require RefMainClosed ConstAccept.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Theorem both_base : strong_universal_error_free_T image_P image_B.
Proof.
  intros [rsp rbrk rmb rrnd] [asp abrk amb arnd] inp Hens Hent Hvalid.
  pose proof (valid_input_va_size _ Hvalid) as Hsv48.
  rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hens. rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hent.
  destruct Hens as [Hrsp [Hrbrk [Hrmb Hrfit]]]. destruct Hent as [Hasp [Habrk [Hamb Hafit]]].
  destruct Hvalid as (Hargv & Henvp & Hfs & Hrel & [Huid Hgid] & Hnofile & Hsigmask & Hhw & Habort & _).
  apply (shape_strong_equiv_efs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (spec (in_argv inp) (in_fs inp))).
  - exact (RefMainClosed.ref_realizes_spec_closed (AL:=SrcLim) lib_P rsp rbrk rmb rrnd inp Hrsp Hrbrk Hrfit Hargv Henvp Hfs).
  - exact (both_side (both_obls_of lib_B) both_certs_all asp abrk amb arnd inp Hasp Habrk Hafit Hargv Henvp Huid Hhw Hsv48).
Qed.

Lemma both_base_scfg :
  strong_universal_error_free_T_scfg Env.may_fail
    OSSVerify.double_conversion.string_to_double_fuzzer.Images.plain
    OSSVerify.double_conversion.string_to_double_fuzzer.Images.asan_ubsan.
Proof. exact (proj2 (strong_universal_error_free_T_scfg_may_fail _ _) both_base). Qed.

Theorem both_bound_0 :
  OSSVerify.double_conversion.string_to_double_fuzzer.Statements.asan_ubsan_disagrees_at_most 0.
Proof. exact (ConstAccept.disagrees_at_most_0 _ _ _ _ _ both_base_scfg). Qed.

Theorem both_decidable :
  OSSVerify.double_conversion.string_to_double_fuzzer.Statements.asan_ubsan_agreement_decidable.
Proof. exact (ConstAccept.agreement_decidable_of_base _ _ _ both_base_scfg). Qed.
