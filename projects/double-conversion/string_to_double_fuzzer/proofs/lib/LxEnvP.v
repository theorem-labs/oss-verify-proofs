(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import ImgP LibIface.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import LxLin LxState LxMem LxStep LxCheck.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations LXL LXS LXM LXI LXC.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition TABLES_P : list table :=
  [TB 0x13408 8 23 [TF 0 8 false TFresh];
   TB 0x13518 16 87 [TF 0 8 true (THull (-9204148869281624187) (-38366372719436721)); TF 0 8 false (THull 9242595204427927429 18408377700990114895); TF 8 2 true (THull (-1220) 1066); TF 10 2 true (TAffine (-348) 8)];
   TB 0x134c0 4 7 [TF 0 4 true (THull 4 24)];
   TB 0x134e0 8 7 [TF 0 8 true (THull 2560000000 4194304000); TF 0 8 false (THull 2560000000 4194304000)]].

Definition UP : uenv :=
  UEnv ImgP.M.loaded_segments 4096 RO_P [LIBR_HULL_P] (2 ^ 26) TABLES_P 0x35320 1888 [(CANARY_P, SYM_SC0)].
