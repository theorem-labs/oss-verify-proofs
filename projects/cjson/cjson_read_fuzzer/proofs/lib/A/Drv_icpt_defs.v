(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import AImg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.


(* [comment removed for export] *)
Definition AFWRITE_STACK : Z := 2368.         (* [comment removed for export] *)
Definition AREAL_FWRITE_SLOT : Z := 0xa3cc8.
Definition AMUSL_FWRITE : Z := 0x943dc.
Definition fwrite_icpt_cells (m : word -> option byte) : Prop :=
  ro_cells asegs m AREAL_FWRITE_SLOT [C8 (Z_to_bv 64 AMUSL_FWRITE)].

(* [comment removed for export] *)


End CeilWrap.
