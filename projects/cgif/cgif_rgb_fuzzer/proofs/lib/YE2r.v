(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YK18 YK0o YQ0k.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0k YA0l YA0m YF9g.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YB0z YE2q.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require YF00 YE1o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Section a.
Section b.
Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Variable W : world trasegs.
Lemma fdchan_sbm : forall fd ch m m', fdchan fd ch m -> same_but_materialized m m' -> fdchan fd ch m'.
Proof. first [ exact YE1o.fdchan_sbm | exact (YE1o.fdchan_sbm W) | exact YE1o.fdchan_sbm | solve [ eapply YE1o.fdchan_sbm; eassumption ] | solve [ intros; eapply YE1o.fdchan_sbm; eassumption ] ]. Qed.
End b.
End a.
