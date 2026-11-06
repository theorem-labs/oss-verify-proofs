(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: cgif_file_fuzzer lib/A/AE39.v:88 astrnlen_of_M, for strlen and over lib/Rt/ConstsViewDef.v's consts_view with cgif's fixed MC_LO/MC_HI as arguments; module paths. *)
(* Modified by Theorem Labs, 2026-10: copied from lib/A/Rt/StrlenOfM.v for the asan-ubsan image of libreac/fuzz_disco; the lemma names no image, so only the module path changes. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt Require Import ConstsViewDef StrlenDef.
Import ListNotations.
Open Scope Z_scope.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section c.
Variable segs : list Segment.
Variable B : asyms.
Lemma astrlen_of_M : forall lo hi pc,
(forall a, lo <= a < hi -> in_rom segs a) ->
astrlen_realizesM segs B lo hi pc -> astrlen_realizes segs B pc.
Proof.
intros lo hi pc Hin HM ly S W regs mem md x k
HPRE G10 Hx Hk0 Hk32 Hxk Hfb Hsrc Ham Hra Hhull Htail Hrom.
exact (HM ly S W regs mem md x k HPRE G10 Hx Hk0 Hk32 Hxk Hfb Hsrc Ham Hra Hhull Htail
(consts_view_of_rom_view segs lo hi W mem Hin Hrom)).
Qed.
End c.
End b.
