(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import NArith ZArith List Bool.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import AxSymExec3 AsanPlanCore AsanPlan AsanMainDefs AsanMain BothTop BothCertsRoots BTreesRoot4 BK0TailAll BK0TailAllCerts BK0TreeR5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition both_certs_all : both_certs := both_certs_roots TT_r5 TT_r5_ok BTreesRoot4.T_h0_r4_ok T_r5 T_r5_ok.
