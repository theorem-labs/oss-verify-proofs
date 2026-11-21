(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Spec Require Import Prelim STree Malloc Stdio.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Record PState := mkPS {
  ps_m   : mstate;
  ps_brk : Z;
  ps_fa  : unit;
  ps_so  : stdout_st
}.
Definition set_m (v : mstate) (s : PState) := mkPS v (ps_brk s) (ps_fa s) (ps_so s).
Definition set_brk_ps (v : Z) (s : PState) := mkPS (ps_m s) v (ps_fa s) (ps_so s).
Definition set_fa_ps (v : unit) (s : PState) := mkPS (ps_m s) (ps_brk s) v (ps_so s).
Definition set_so_ps (v : stdout_st) (s : PState) := mkPS (ps_m s) (ps_brk s) (ps_fa s) v.

Definition ps_init (reserved : list (Z * Z)) (atop : Z) : PState :=
  mkPS (strip (minit 0 reserved atop)) 0 tt stdout_init.
