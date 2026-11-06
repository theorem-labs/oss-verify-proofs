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
YB1u YE3h YF9i YF9j YE33 YE3u YE3t YE3y YE32 YFa1 YE2z YE3c.
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
zallb (img_byte_ok trbsegs) a 8%nat = true -> exists v, rdword (aview trbsegs H m) a = Some v /\ 0 <= v < 2 ^ 64.
Proof. first [ exact (YE1l.rdword_img_some (imgk := YF00.K_trb)) | solve [ eapply (YE1l.rdword_img_some (imgk := YF00.K_trb)); eassumption ] | solve [ intros; eapply (YE1l.rdword_img_some (imgk := YF00.K_trb)); eassumption ] ]. Qed.
Section S.
Variable B : asyms.
Hypothesis LAWS : AR_laws trbsegs B.
Hypothesis COV0 : forall ly S (W : world trbsegs) mem md, AR trbsegs B ly S W mem md -> aview trbsegs (w_H W) mem 0x13d120 = Some 0.
Hypothesis COMPLETED_free : forall ly S (W : world trbsegs) mem md, AR trbsegs B ly S W mem md -> ~ aowned B ly S 0xa7c10.
Theorem x1_realizes : xret_realizes trbsegs B X1_PC XW1 XTRUE.
Proof. first [ exact (YE1l.x1_realizes (imgk := YF00.K_trb)) | exact ((YE1l.x1_realizes (imgk := YF00.K_trb)) B LAWS COV0 COMPLETED_free) | exact ((YE1l.x1_realizes (imgk := YF00.K_trb)) B LAWS COV0) | exact ((YE1l.x1_realizes (imgk := YF00.K_trb)) B LAWS COMPLETED_free) | exact ((YE1l.x1_realizes (imgk := YF00.K_trb)) B COV0 COMPLETED_free) | exact ((YE1l.x1_realizes (imgk := YF00.K_trb)) LAWS COV0 COMPLETED_free) | exact ((YE1l.x1_realizes (imgk := YF00.K_trb)) B LAWS) | exact ((YE1l.x1_realizes (imgk := YF00.K_trb)) B COV0) | exact ((YE1l.x1_realizes (imgk := YF00.K_trb)) LAWS COV0) | exact ((YE1l.x1_realizes (imgk := YF00.K_trb)) B COMPLETED_free) | exact ((YE1l.x1_realizes (imgk := YF00.K_trb)) LAWS COMPLETED_free) | exact ((YE1l.x1_realizes (imgk := YF00.K_trb)) COV0 COMPLETED_free) | solve [ eapply (YE1l.x1_realizes (imgk := YF00.K_trb)); eassumption ] | solve [ intros; eapply (YE1l.x1_realizes (imgk := YF00.K_trb)); eassumption ] ]. Qed.
Theorem x3_realizes : xret_realizes trbsegs B X3_PC XW3 X3PRE.
Proof. first [ exact (YE1l.x3_realizes (imgk := YF00.K_trb)) | exact ((YE1l.x3_realizes (imgk := YF00.K_trb)) B LAWS COV0 COMPLETED_free) | exact ((YE1l.x3_realizes (imgk := YF00.K_trb)) B LAWS COV0) | exact ((YE1l.x3_realizes (imgk := YF00.K_trb)) B LAWS COMPLETED_free) | exact ((YE1l.x3_realizes (imgk := YF00.K_trb)) B COV0 COMPLETED_free) | exact ((YE1l.x3_realizes (imgk := YF00.K_trb)) LAWS COV0 COMPLETED_free) | exact ((YE1l.x3_realizes (imgk := YF00.K_trb)) B LAWS) | exact ((YE1l.x3_realizes (imgk := YF00.K_trb)) B COV0) | exact ((YE1l.x3_realizes (imgk := YF00.K_trb)) LAWS COV0) | exact ((YE1l.x3_realizes (imgk := YF00.K_trb)) B COMPLETED_free) | exact ((YE1l.x3_realizes (imgk := YF00.K_trb)) LAWS COMPLETED_free) | exact ((YE1l.x3_realizes (imgk := YF00.K_trb)) COV0 COMPLETED_free) | solve [ eapply (YE1l.x3_realizes (imgk := YF00.K_trb)); eassumption ] | solve [ intros; eapply (YE1l.x3_realizes (imgk := YF00.K_trb)); eassumption ] ]. Qed.
End S.
End b.
