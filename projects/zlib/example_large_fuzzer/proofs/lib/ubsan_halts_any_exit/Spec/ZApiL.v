(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Spec Require Import Prelim ZApi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition Z_BEST_COMPRESSION : Z := 9.
Definition Z_NO_COMPRESSION : Z := 0.
Definition Z_DEFAULT_STRATEGY : Z := 0.
Definition Z_FILTERED : Z := 1.

Definition ZL_MAX : Z := 524288.
Definition NofL (size : Z) : Z := 100 + 3 * size.

Record zapiL : Type := mkZapiL {
  DSL : Type;
  ISL : Type;
  zl_dstate : Z; zl_dwin : Z; zl_dprev : Z; zl_dhead : Z; zl_dpend : Z; zl_isize : Z; zl_wsize : Z;
  dl_init9 : DSL;
  dl_total_out : DSL -> Z;
  dl_deflate : list Z -> DSL -> Z -> Z -> DSL * Z * list Z * Z;
  dl_params : list Z -> DSL -> Z -> Z -> Z -> DSL * Z * list Z * Z;
  dl_end : DSL -> Z;
  il_init : ISL;
  il_total_in : ISL -> Z;
  il_total_out : ISL -> Z;
  il_wants_window : list Z -> ISL -> Z -> bool;
  il_inflate : list Z -> ISL -> Z -> bool -> ISL * Z * list Z * Z;
  il_end : ISL -> Z
}.
