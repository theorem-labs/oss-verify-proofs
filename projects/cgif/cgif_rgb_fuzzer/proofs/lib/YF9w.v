(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YK18 YK0l YK0s YK0o YQ0k YK1d.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ0a YQ04 YQ05 YQ0e YQ02.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10 YP0g.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YA0n YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YG00 YG0a YG01 YG0h YG0u YG0d YG0e YG0y YG0z.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YB1u YE3h YF9i YF9j YFa1 YB1v YE3q YE3c.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require YF00 YF3h.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Definition SF_ENTRY : Z := 0x3d618.
Section a.
Section b.
Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Variable B : asyms.
Hypothesis LAWS : AR_laws trbsegs B.
Hypothesis TB : TrbSyms B.
Theorem trb_stack_free_7 : astack_free_realizes trbsegs B SF_ENTRY 7.
Proof. first [ exact (YF3h.tfx_stack_free_7 (imgk := YF00.K_trb)) | exact ((YF3h.tfx_stack_free_7 (imgk := YF00.K_trb)) B LAWS TB) | exact ((YF3h.tfx_stack_free_7 (imgk := YF00.K_trb)) B LAWS) | exact ((YF3h.tfx_stack_free_7 (imgk := YF00.K_trb)) B TB) | exact ((YF3h.tfx_stack_free_7 (imgk := YF00.K_trb)) LAWS TB) | exact ((YF3h.tfx_stack_free_7 (imgk := YF00.K_trb)) B) | exact ((YF3h.tfx_stack_free_7 (imgk := YF00.K_trb)) LAWS) | exact ((YF3h.tfx_stack_free_7 (imgk := YF00.K_trb)) TB) | solve [ eapply (YF3h.tfx_stack_free_7 (imgk := YF00.K_trb)); eassumption ] | solve [ intros; eapply (YF3h.tfx_stack_free_7 (imgk := YF00.K_trb)); eassumption ] ]. Qed.
End b.
End a.
