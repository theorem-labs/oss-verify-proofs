(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAW Require Import Contracts IcptA0 AllocA0.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.AW Require Import H_pparse_stmt H_pparse_kit.

Definition pparse_spec_A := @H_pparse_kit.pparse_spec_A.
