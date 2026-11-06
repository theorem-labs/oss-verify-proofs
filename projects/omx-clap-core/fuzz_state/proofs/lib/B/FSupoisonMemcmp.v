(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/B/FSupoisonBcmp.v, with its module paths and module names changed; 6 of its 35 lines of code are new or changed and 616 lines of the source are left out. *)
(* fuzz_state image B (fs.asan-ubsan): FSupoisonU.amemcmp_realizesU at fs's memcmp entry, i.e. the donor's memcmp interceptor contract
   over ARU for ANY set U of user-poisoned ranges (POISON-U lane, a Theorem Labs lane). ARU (any-user-poison) form,
   published as the shared one; two Theorem Labs lanes hold the U = [] form at their own addresses.
   PORT (image B): text of lib/A/FSupoisonMemcmp.v at a working branch cd7610bc4ed (a Theorem Labs lane); imports switched to the lib/B
   twins (YB1v YE34 YF0l YF0m YF0x YB1w YE20 YE2y; YE2s YE2z YE3b YE6z YE70 = this branch's relocations of
   lib/A/AE2s / AE2z / AE3b / AE6z / AE70 to fs.asan-ubsan), FSupoisonIntrinR -> lib/B/FSupoisonAsanR (the same region
   lemmas over image B, McpyB f32c92531db), the image-generic lib/A modules (FSupoison, FSupoisonU) kept.
   The text below is the image-A file's, with its addresses replaced by image B's.
   Rule 24: no function proved from scratch; the walk is cgif_file_fuzzer's released A/AE2z.v, ported over ARU in
   lib/B/FSupoisonMemcmpW.v (over lib/B/YE2z.v / YE3b.v for the AR-free half and the musl memcmp leaf, and
   lib/B/FSupoisonMcmpChkX.v / FSupoisonMcmpChkY.v for the two range checks).
   Port-from of this file's proofs: cgif A/AE2z.v:710 memcmp_icpt_contract and A/ACed.v:156 tfibX_AMEMCMP, with U
   threaded; pc_wrap_memcmp (as_code B) = YF0l's 0x426d4 (`j 0x43d28`, __wrap_memcmp -> ___interceptor_memcmp, checked
   against fs.asan-ubsan's listing, sha256 5ac5ce0954f8...).

   CONSUMERS (owner decision 22:28Z): fs's program part never calls memcmp directly (image B's call graph, asan-ubsan
   fuzz_state.edges.tsv: no program function calls memcmp; musl bcmp 0x98e3c is `j __wrap_memcmp`, and the other
   caller is musl's do_tzset), so lib/B/FSH_Rt.v has no fr_memcmp field and S0 does
   not change. The two consumers are:
   (1) the sibling bcmp walk (lib/B/FSupoisonBcmp.v), through its Section hypothesis AMEMCMPU, discharged
       by tfib_amemcmp_realizesU B LAWS TB;
   (2) the kit's own obligation lib/Reusable/YG0d.v:541 aa_memcmp (a field of the AsanAPI record, U = [] form),
       discharged by tfib_aa_memcmp below. No AsanAPI instance exists in fuzz_state/lib today (no Build_AsanAPI or
       AsanAPI value there, checked by search); whichever instance TFIB_T's runtime record builds takes
       aa_memcmp := tfib_aa_memcmp. Its cgif analogue is A/ACed.v:156 tfibX_AMEMCMP.
   The U = [] corollary tfib_aa_memcmp goes through FSupoisonU.amemcmp_realizes_of_U; lib/B/YE2z.v states the
   same contract on plain AR (memcmp_icpt_contract). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0k YK0s YK0n YP0n YK1d.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP04 YP0g YP01.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0v YO0f.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q YA0m.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import YB1v YE34 YF0l YF0m YF0x YB1w YE20 YE2y.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import FSupoisonMemcmpW.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require FSupoison FSupoisonU.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YI14 YI16.
(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here (the build errors naming this line) means a WRONG sink instance resolved. *)
Fail Definition probe_SK : Reusable.YI16.sink_head := _.
Fail Definition probe_SH : Reusable.YI14.sink_syms := _.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module FSU := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.FSupoisonU.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis TB : TfibSyms B.
(* memcmp: FSupoisonU.v:266 amemcmp_realizesU at the harness's memcmp entry. *)
Theorem tfib_amemcmp_realizesU : FSU.amemcmp_realizesU tfibsegs B (pc_wrap_memcmp (as_code B)).
Proof. rewrite (ts_code B TB). exact (mc_icpt_realizesU B LAWS TB). Qed.
(* Its U = [] corollary: the AsanAPI field YG0d.v:541 aa_memcmp, through FSupoisonU.v:390 amemcmp_realizes_of_U. *)
Theorem tfib_aa_memcmp : amemcmp_realizes tfibsegs B (pc_wrap_memcmp (as_code B)).
Proof. exact (FSU.amemcmp_realizes_of_U tfibsegs B _ tfib_amemcmp_realizesU). Qed.
End b.
