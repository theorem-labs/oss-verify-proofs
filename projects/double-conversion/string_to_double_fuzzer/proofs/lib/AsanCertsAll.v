(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import NArith ZArith List Bool.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import AxSymExec3 AsanPlanCore AsanPlan AsanMainDefs AsanMain AsanTop AsanCertsRoots TreesRoot4 K0TailAll K0TailAllCerts K0TreeR5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition asan_certs_all : asan_certs := asan_certs_roots TT_r5 TT_r5_ok TreesRoot4.T_h0_r4_ok T_r5 T_r5_ok.
