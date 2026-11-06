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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YA0n YA0o YA0k.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YG00 YG0a YG01 YG0h YG0u YG0d.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YB0z YE2g YF8z YF90 YE22 YE2t YE2s YE2x YE21 YF9g YE1y YE2b.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require YF00 YE1m.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Section a.
Section S.
Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Variable B : asyms.
Hypothesis LAWS : AR_laws trasegs B.
Hypothesis TB : TraSyms B.
Hypothesis MU0 : forall ly, cell_lookup (Tra_const ly) (ANum 0xa7a70) = Some (ACell (ANum 0xa7a70) 8 (AV (ANum 0))).
Theorem x2_realizes : xret_realizes_noar trasegs B X2_PC XW2 XTRUE.
Proof. first [ exact (YE1m.x2_realizes (imgk := YF00.K_tra)) | exact ((YE1m.x2_realizes (imgk := YF00.K_tra)) B LAWS TB MU0) | exact ((YE1m.x2_realizes (imgk := YF00.K_tra)) B LAWS TB) | exact ((YE1m.x2_realizes (imgk := YF00.K_tra)) B LAWS MU0) | exact ((YE1m.x2_realizes (imgk := YF00.K_tra)) B TB MU0) | exact ((YE1m.x2_realizes (imgk := YF00.K_tra)) LAWS TB MU0) | exact ((YE1m.x2_realizes (imgk := YF00.K_tra)) B LAWS) | exact ((YE1m.x2_realizes (imgk := YF00.K_tra)) B TB) | exact ((YE1m.x2_realizes (imgk := YF00.K_tra)) LAWS TB) | exact ((YE1m.x2_realizes (imgk := YF00.K_tra)) B MU0) | exact ((YE1m.x2_realizes (imgk := YF00.K_tra)) LAWS MU0) | exact ((YE1m.x2_realizes (imgk := YF00.K_tra)) TB MU0) | solve [ eapply (YE1m.x2_realizes (imgk := YF00.K_tra)); eassumption ] | solve [ intros; eapply (YE1m.x2_realizes (imgk := YF00.K_tra)); eassumption ] ]. Qed.
End S.
End a.
