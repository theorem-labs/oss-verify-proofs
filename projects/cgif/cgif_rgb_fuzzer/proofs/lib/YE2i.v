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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require YF00 YE1l.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Section b.
Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Lemma rdword_img_some : forall (H : word -> bool) (m : word -> option byte) a,
zallb (img_byte_ok trasegs) a 8%nat = true -> exists v, rdword (aview trasegs H m) a = Some v /\ 0 <= v < 2 ^ 64.
Proof. first [ exact (YE1l.rdword_img_some (imgk := YF00.K_tra)) | solve [ eapply (YE1l.rdword_img_some (imgk := YF00.K_tra)); eassumption ] | solve [ intros; eapply (YE1l.rdword_img_some (imgk := YF00.K_tra)); eassumption ] ]. Qed.
Section S.
Variable B : asyms.
Hypothesis LAWS : AR_laws trasegs B.
Hypothesis COV0 : forall ly S (W : world trasegs) mem md, AR trasegs B ly S W mem md -> aview trasegs (w_H W) mem 0x13c060 = Some 0.
Hypothesis COMPLETED_free : forall ly S (W : world trasegs) mem md, AR trasegs B ly S W mem md -> ~ aowned B ly S 0xa6b50.
Theorem x1_realizes : xret_realizes trasegs B X1_PC XW1 XTRUE.
Proof. first [ exact (YE1l.x1_realizes (imgk := YF00.K_tra)) | exact ((YE1l.x1_realizes (imgk := YF00.K_tra)) B LAWS COV0 COMPLETED_free) | exact ((YE1l.x1_realizes (imgk := YF00.K_tra)) B LAWS COV0) | exact ((YE1l.x1_realizes (imgk := YF00.K_tra)) B LAWS COMPLETED_free) | exact ((YE1l.x1_realizes (imgk := YF00.K_tra)) B COV0 COMPLETED_free) | exact ((YE1l.x1_realizes (imgk := YF00.K_tra)) LAWS COV0 COMPLETED_free) | exact ((YE1l.x1_realizes (imgk := YF00.K_tra)) B LAWS) | exact ((YE1l.x1_realizes (imgk := YF00.K_tra)) B COV0) | exact ((YE1l.x1_realizes (imgk := YF00.K_tra)) LAWS COV0) | exact ((YE1l.x1_realizes (imgk := YF00.K_tra)) B COMPLETED_free) | exact ((YE1l.x1_realizes (imgk := YF00.K_tra)) LAWS COMPLETED_free) | exact ((YE1l.x1_realizes (imgk := YF00.K_tra)) COV0 COMPLETED_free) | solve [ eapply (YE1l.x1_realizes (imgk := YF00.K_tra)); eassumption ] | solve [ intros; eapply (YE1l.x1_realizes (imgk := YF00.K_tra)); eassumption ] ]. Qed.
Theorem x3_realizes : xret_realizes trasegs B X3_PC XW3 X3PRE.
Proof. first [ exact (YE1l.x3_realizes (imgk := YF00.K_tra)) | exact ((YE1l.x3_realizes (imgk := YF00.K_tra)) B LAWS COV0 COMPLETED_free) | exact ((YE1l.x3_realizes (imgk := YF00.K_tra)) B LAWS COV0) | exact ((YE1l.x3_realizes (imgk := YF00.K_tra)) B LAWS COMPLETED_free) | exact ((YE1l.x3_realizes (imgk := YF00.K_tra)) B COV0 COMPLETED_free) | exact ((YE1l.x3_realizes (imgk := YF00.K_tra)) LAWS COV0 COMPLETED_free) | exact ((YE1l.x3_realizes (imgk := YF00.K_tra)) B LAWS) | exact ((YE1l.x3_realizes (imgk := YF00.K_tra)) B COV0) | exact ((YE1l.x3_realizes (imgk := YF00.K_tra)) LAWS COV0) | exact ((YE1l.x3_realizes (imgk := YF00.K_tra)) B COMPLETED_free) | exact ((YE1l.x3_realizes (imgk := YF00.K_tra)) LAWS COMPLETED_free) | exact ((YE1l.x3_realizes (imgk := YF00.K_tra)) COV0 COMPLETED_free) | solve [ eapply (YE1l.x3_realizes (imgk := YF00.K_tra)); eassumption ] | solve [ intros; eapply (YE1l.x3_realizes (imgk := YF00.K_tra)); eassumption ] ]. Qed.
End S.
End b.
