(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: made from TFIB_T_closed of proofs/cgif/cgif_file_fuzzer/lib/A/AD2p.v:11-17
   (the donor's asan image; its lib/YD2p.v:11-17 twin is the asan-ubsan one) for fuzz_preset's asan image. This file and
   lib/AU/PresetD2pB.v are the same text except for the image.
   It states the CLOSED ASan-side walk: the asan build realizes SPECX from every valid start whose plain run is never
   refused at the agreement's budget, i.e. exactly lib/A/PresetTFIB.v TFIB_T, the premise of the agreement top
   (lib/A/AsanTop.v preset_asan_agrees_of_tfib).
   Nothing in this file is a proof of a function (rule 24: no function proved; this is the composition / driver layer
   of a port).
   Changes from the donor (closedwalk-plan.md section 1b): the conclusion is preset's TFIB_T, with the plain no-refusal
   premise; cgif's `wfn` literal is dropped (preset's target code has no function pointer); cgif's three library walks
   are replaced by the program's function walks of preset (the 14 callee contracts and the harness walk, taken by
   TFIB_T_of_partsXF_A, PresetD2oA.v). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/PresetD2pA.v, with its module paths and module names changed; 1 of its 16 lines of code is new or changed and 1 line of the source is left out. *)
(* Modified by Theorem Labs, 2026-10: made from TFIB_T_closed of proofs/cgif/cgif_file_fuzzer/lib/A/AD2p.v:11-17
   (the donor's asan image; its lib/YD2p.v:11-17 twin is the asan-ubsan one) for fuzz_preset's asan image. This file and
   lib/AU/PresetD2pB.v are the same text except for the image.
   It states the CLOSED ASan-side walk: the asan build realizes SPECX from every valid start whose plain run is never
   refused at the agreement's budget, i.e. exactly lib/A/PresetTFIB.v TFIB_T, the premise of the agreement top
   (lib/A/AsanAgreesTop.v preset_asan_agrees_of_tfib).
   Nothing in this file is a proof of a function (rule 24: no function proved; this is the composition / driver layer
   of a port).
   Changes from the donor (the internal file closedwalk-plan.md section 1b): the conclusion is preset's TFIB_T, with the plain no-refusal
   premise; cgif's `wfn` literal is dropped (preset's target code has no function pointer); cgif's three library walks
   are replaced by the program's function walks of preset (the 14 callee contracts and the harness walk, taken by
   TFIB_T_of_partsXF_A, PresetD2oA.v). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PresetTFIB.
Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(* 1. The statement. Donor: A/AD2p.v:11 (TFIB_T_closed : TFIB_T). *)
Definition TFIB_T_closed_A : Prop := TFIB_T.
