(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require Import ApATac.
Import ListNotations.
Open Scope Z_scope.

Definition A_GOT_SHB : Z := 0x5a9238.
Definition A_SHB_CELL : Z := 0x672038.
Definition A_REPORTS : list Z :=
  [0x1ca9d0; 0x1caa70; 0x1cab10; 0x1cabb0; 0x1cac50; 0x1cacf0; 0x1cad90; 0x1cae30; 0x1caed0; 0x1caf70; 0x1cb010; 0x1cb0b0].
  (* [comment removed for export] *)

#[global] Instance apb_asan_img : AsanImg ctasegs := {| as_got_shb := A_GOT_SHB ; as_reports := A_REPORTS |}.
