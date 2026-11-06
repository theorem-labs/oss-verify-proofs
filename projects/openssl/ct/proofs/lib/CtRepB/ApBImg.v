(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.openssl.ct.lib.CtRepB Require Import ApATac.
Import ListNotations.
Open Scope Z_scope.

Definition A_GOT_SHB : Z := 0x5e1b38.
Definition A_SHB_CELL : Z := 0x6a4e78.
Definition A_REPORTS : list Z :=
  [0x1c5960; 0x1c5a00; 0x1c5aa0; 0x1c5b40; 0x1c5be0; 0x1c5c80; 0x1c5d20; 0x1c5dc0; 0x1c5e60; 0x1c5f00; 0x1c5fa0; 0x1c6040].
  (* [comment removed for export] *)

#[global] Instance apb_asan_img : AsanImg ctbsegs := {| as_got_shb := A_GOT_SHB ; as_reports := A_REPORTS |}.
