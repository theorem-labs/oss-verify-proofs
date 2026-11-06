(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: made from TFIB_T_closed of proofs/cgif/cgif_file_fuzzer/lib/YD2p.v:11-17
   (the donor's asan-ubsan image; its lib/A/AD2p.v:11-17 twin is the asan one) for fuzz_preset's asan-ubsan image. This file and
   lib/A/PresetD2pA.v are the same text except for the image.
   It states the CLOSED ASan-side walk: the asan-ubsan build realizes SPECX from every valid start whose plain run is never
   refused at the agreement's budget, i.e. exactly lib/AU/PresetTFIBAU.v TFIB_T_AU, the premise of the agreement top
   (lib/AU/AsanUbsanTop.v preset_asan_ubsan_agrees_of_tfib).
   Nothing in this file is a proof of a function (rule 24: no function proved; this is the composition / driver layer
   of a port).
   Changes from the donor (the internal file closedwalk-plan.md section 1b): the conclusion is preset's TFIB_T_AU, with the plain no-refusal
   premise; cgif's `wfn` literal is dropped (preset's target code has no function pointer); cgif's three library walks
   are replaced by the program's function walks of preset (the 14 callee contracts and the harness walk, taken by
   TFIB_T_of_partsXF_B, PresetD2oB.v). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import PresetTFIBAU.
Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(* 1. The statement. Donor: YD2p.v:11 (TFIB_T_closed : TFIB_T). *)
Definition TFIB_T_closed_B : Prop := TFIB_T_AU.
