(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the walk of the strlen wrapper of libreac/fuzz_identity.asan-ubsan (trampoline 0x421f4 -> ___interceptor_strlen 0x42284 -> musl strlen 0x94f50 -> the inline range check -> the epilogue), over cgif_file_fuzzer's lib/A/AE6x.v (the memchr wrapper: the entry phase, the lift of a musl msteps walk, the check, the epilogue) and lib/A/AE7d.v (the strnlen wrapper: the 2144-byte frame and its eight saved registers) as the B core holds them. The walked function is released as proofs/coturn/FuzzStunClient/lib/VBothIcStrlenWalk.v:819 isl_run at coturn's asan-ubsan addresses; this is that walk at fuzz_identity.asan-ubsan's addresses in this release's engine, and its statement is lib/B/Rt/StrlenDef.v astrlen_realizes (cgif lib/YG0d.v:401-419 astrnlen_realizes without the n bound). The text is lib/A/Rt/Strlen.v's; only the addresses, the module prefix and this line differ. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Rt/Strlen.v, with its module paths and module names changed; 15 of its 25 lines of code are new or changed and 495 lines of the source are left out. *)
(* libreac/fuzz_identity, build asan-ubsan: the strlen wrapper's contract, lib/B/Rt/StrlenDef.v astrlen_realizes at
   STRLEN_ENTRY = 0x421f4, from the shared strlen walk lib/B/FMstrlen.v strlen_icpt_srr: the walk
   (cgif_file_fuzzer asan coordinates, SL_ENTRY 0x418f0) relocated to
   fuzz_identity.asan-ubsan (SL_ENTRY 0x421f4). The text is lib/A/Rt/Strlen.v's over the B core. *)
(* Modified by Theorem Labs, 2026-10-29: for a Theorem Labs lane's acceptance (a working branch), the record class is TfibSyms, not IdentTfibSyms, and the core modules are Required by full path at the applied B core's names: lib/B/A<x>.v -> lib/ReusableB/Y<x>.v (AB1v AB1w AE20 AE2y AE34 AE39 AE3a AE6y AF0l AF0m AF0x -> YB1v YB1w YE20 YE2y YE34 YE39 YE3a YE6y YF0l YF0m YF0x, qualified names included), lib/Reusable/YA0m, YE08, YE21. *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YM05.
Require Import
  OSSVerify.Proofs.libreac.fuzz_identity.lib.ReusableB.YB1v
  OSSVerify.Proofs.libreac.fuzz_identity.lib.ReusableB.YF0m
  OSSVerify.Proofs.libreac.fuzz_identity.lib.ReusableB.YE39.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B Require FMstrlen.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Rt Require Import StrlenDef WrapRo WrapRoM.
Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma SL_ENTRY_eq : FMstrlen.SL_ENTRY = STRLEN_ENTRY. Proof. reflexivity. Qed.
Theorem strlen_icpt_contract : forall B, AR_laws tfibsegs B -> TfibSyms B -> astrlen_realizes tfibsegs B STRLEN_ENTRY.
Proof.
intros B LAWS TB. unfold astrlen_realizes. intros ly S W regs mem md x k. intros.
rewrite <- SL_ENTRY_eq.
apply (FMstrlen.strlen_icpt_srr B LAWS TB ly S W regs mem md x k).
all: first [ assumption | apply (mconsts_of_aro B W mem TB); assumption ].
Qed.
End d.
