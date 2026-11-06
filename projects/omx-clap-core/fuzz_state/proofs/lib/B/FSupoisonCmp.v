(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AE32.v, with its module paths changed and its addresses moved to libreac/fuzz_disco's ASan build. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/AE32.v, with its module paths changed; 10 of its 25 lines of code are new or changed and 569 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/FSupoisonCmp.v, with its module paths and module names changed; 8 of its 33 lines of code are new or changed. *)
(* fuzz_state image B (fs.asan-ubsan, sha256 5ac5ce0954f8): the bcmp interceptor contract with its nested memcmp
   discharged, ARU (any-user-poison) form. Rule 24: no function proved here; this file only composes two proved
   theorems:
   - lib/B/FSupoisonBcmp.v tfib_abcmp_realizesU (the ARU bcmp walk, image B), which takes the nested memcmp
     interceptor (B's musl bcmp 0x98e3c is `j 0x426d4`, __wrap_memcmp) as its Section hypothesis AMEMCMPU;
   - lib/B/FSupoisonMemcmp.v tfib_amemcmp_realizesU (the ARU memcmp walk, image B), which is that hypothesis.
   The closed theorem below therefore has only the donor's Section hypotheses, AR_laws and TfibSyms. Its U = [] form
   follows through FSupoisonU.abcmp_realizes_of_U. tfib_abcmp_realizesU_PC is the term for S0's FsRt field fr_bcmp
   (lib/B/FSH_Rt.v: FSupoisonU.abcmp_realizesU segs B PC_bcmp at segs := tfibsegs): pc_wrap_bcmp (as_code B) is
   lib/B/FSH_Base.v's PC_bcmp 0x426d8 (sym __wrap_bcmp) by computation, through TfibSyms' ts_code and YF0l.v's
   pc_wrap_bcmp := 0x426d8.
   PORTED FROM: lib/A/FSupoisonCmp.v of a working branch cd7610bc4ed (a Theorem Labs lane), text kept; imports
   switched to the image-B files (lib/B twins of the image-A modules, the B ports of FSupoisonBcmp / FSupoisonMemcmp);
   the PC_bcmp bridge and its corollary are new here. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0k YK0s YK0n YP0n YK1d.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import YB1v YE34 YF0l YF0m YF0x YB1w YE20 YE2y.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require FSupoisonU.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require FSupoisonBcmp FSupoisonMemcmp FSH_Base.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YI14 YI16.
(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here (the build errors naming this line) means a WRONG sink instance resolved. *)
Fail Definition probe_SK : Reusable.YI16.sink_head := _.
Fail Definition probe_SH : Reusable.YI14.sink_syms := _.
Open Scope Z_scope.

Module FSU := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.FSupoisonU.
Module FSB := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B.FSupoisonBcmp.
Module FSM := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B.FSupoisonMemcmp.

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

(* The bcmp trampoline of as_code B is lib/B/FSH_Base.v's PC_bcmp (0x426d8, sym __wrap_bcmp), by computation. *)
Lemma tfib_pc_wrap_bcmp : pc_wrap_bcmp (as_code B) = FSH_Base.PC_bcmp.
Proof. rewrite (ts_code B TB). reflexivity. Qed.

(* The type of FsRt.fr_bcmp (lib/B/FSH_Rt.v) at segs := tfibsegs. *)
Corollary tfib_abcmp_realizesU_PC : FSU.abcmp_realizesU tfibsegs B FSH_Base.PC_bcmp.
Proof. rewrite <- tfib_pc_wrap_bcmp. exact tfib_abcmp_realizesU_closed. Qed.
End c.
