(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Spec Require Import Prelim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition Z_OK : Z := 0.
Definition Z_STREAM_END : Z := 1.
Definition Z_MEM_ERROR : Z := -4.
Definition Z_NO_FLUSH : Z := 0.
Definition Z_FINISH : Z := 4.

Definition ZH_MAX : Z := 1048576.

Record zapi : Type := mkZapi {
  DS : Type;
  IS : Type;
  z_bound : Z -> Z;
  z_dstate : Z;
  z_dwin : Z;
  z_dprev : Z;
  z_dhead : Z;
  z_dpend : Z;
  z_isize : Z;
  z_wsize : Z;
  d_init : DS;
  d_total_in : DS -> Z;
  d_total_out : DS -> Z;
  d_deflate : list Z -> DS -> Z -> Z -> Z -> DS * Z * Z * list Z * Z;
  d_end : DS -> Z;
  i_init : IS;
  i_total_in : IS -> Z;
  i_total_out : IS -> Z;
  i_wants_window : list Z -> IS -> bool;
  i_inflate : list Z -> IS -> Z -> Z -> bool -> IS * Z * Z * list Z * Z;
  i_end : IS -> Z
}.
