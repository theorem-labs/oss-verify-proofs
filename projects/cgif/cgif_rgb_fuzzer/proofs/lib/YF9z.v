(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YK18 YK0s YP0c.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YA0n YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG00 YG0a YG01 YG0h YG10 YG0u YG0d.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB1u YF9i YF9j YFa1.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF9m.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require YF00 YF43.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05 YA00.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Open Scope Z_scope.
Section a.
Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Theorem trb_amalloc_realizes : forall B, TrbSyms B -> (forall t, as_dhash B t = trb_dhash t) -> amalloc_realizes trbsegs B.
Proof. first [ exact (YF43.tfx_amalloc_realizes (imgk := YF00.K_trb)) | solve [ eapply (YF43.tfx_amalloc_realizes (imgk := YF00.K_trb)); eassumption ] | solve [ intros; eapply (YF43.tfx_amalloc_realizes (imgk := YF00.K_trb)); eassumption ] ]. Qed.
End a.
