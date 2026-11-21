(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec Require Import Prelim ZApi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition Z_NEED_DICT : Z := 2.
Definition Z_DATA_ERROR : Z := -3.
Definition Z_BUF_ERROR : Z := -5.

Definition ZC_MIN : Z := 10.
Definition ZC_MAX : Z := 1048576.

Definition ZC_UMAX : Z := 4294967295.

Record zapiC : Type := mkZapiC {
  DSC : Type;
  ISC : Type;
  zc_bound : Z -> Z;

  zc_dstate : Z; zc_dwin : Z; zc_dprev : Z; zc_dhead : Z; zc_dpend : Z; zc_isize : Z; zc_wsize : Z;

  dc_init : Z -> DSC;
  dc_total_out : DSC -> Z;
  dc_deflate : list Z -> DSC -> Z -> Z -> DSC * Z * list Z * Z;

  dc_end : DSC -> Z;

  ic_init : ISC;
  ic_total_in : ISC -> Z;
  ic_total_out : ISC -> Z;
  ic_wants_window : list Z -> ISC -> Z -> bool;
  ic_inflate : list Z -> ISC -> Z -> bool -> ISC * Z * list Z * Z;

  ic_end : ISC -> Z
}.
