(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AE32.v, with its module paths changed and its addresses moved to libreac/fuzz_disco's ASan build. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/AE32.v, with its module paths changed; 10 of its 25 lines of code are new or changed and 569 lines of the source are left out. *)
(* fuzz_state image A: the bcmp interceptor contract with its nested memcmp discharged (POISON-U lane, a Theorem Labs lane).
   ARU (any-user-poison) form, published as the shared one; two Theorem Labs lanes hold the U = [] form at their own
   addresses. Rule 24: no function proved here; this file only composes two proved theorems:
   - lib/A/FSupoisonBcmp.v tfib_abcmp_realizesU (port of cgif_file's released A/AE2s.v over ARU), which takes the
     nested memcmp interceptor (fs's musl bcmp 0x98920 is `j __wrap_memcmp`) as its Section hypothesis AMEMCMPU;
   - lib/A/FSupoisonMemcmp.v tfib_amemcmp_realizesU (port of cgif_file's released A/AE2z.v over ARU), which is that
     hypothesis.
   The closed theorem below therefore has only the donor's Section hypotheses, AR_laws and TfibSyms. Its U = [] form
   follows through FSupoisonU.abcmp_realizes_of_U. This is the term for S0's FSH_Rt field fr_bcmp
   (FSupoisonU.abcmp_realizesU segs B PC_bcmp, PC_bcmp = pc_wrap_bcmp (as_code B) = 0x42668 on fs.asan). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0k YK0s YK0n YP0n YK1d.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import AB1v AE34 AF0l AF0m AF0x AB1w AE20 AE2y.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require FSupoisonU FSupoisonBcmp FSupoisonMemcmp.
Open Scope Z_scope.

Module FSU := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.FSupoisonU.
Module FSB := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.FSupoisonBcmp.
Module FSM := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.FSupoisonMemcmp.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis TB : TfibSyms B.

(* abcmp_realizesU at fs's bcmp trampoline, AMEMCMPU discharged. *)
Theorem tfib_abcmp_realizesU_closed : FSU.abcmp_realizesU tfibsegs B (pc_wrap_bcmp (as_code B)).
Proof. exact (FSB.tfib_abcmp_realizesU B LAWS TB (FSM.tfib_amemcmp_realizesU B LAWS TB)). Qed.

(* Its U = [] form, the donor's statement (YG0d.v abcmp_realizes). *)
Corollary tfib_abcmp_realizes_closed : abcmp_realizes tfibsegs B (pc_wrap_bcmp (as_code B)).
Proof. exact (FSU.abcmp_realizes_of_U tfibsegs B (pc_wrap_bcmp (as_code B)) tfib_abcmp_realizesU_closed). Qed.
End c.
