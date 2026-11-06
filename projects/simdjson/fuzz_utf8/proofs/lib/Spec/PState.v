(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Spec Require Import Prelim STree Malloc Stdio.
Import ListNotations.
Open Scope Z_scope.

Record PState := mkPS {
  ps_m   : mstate;        (* [comment removed for export] *)
  ps_brk : Z;             (* [comment removed for export] *)
  ps_fa  : unit;          (* [comment removed for export] *)
  ps_so  : stdout_st      (* [comment removed for export] *)
}.
Definition set_m (v : mstate) (s : PState) := mkPS v (ps_brk s) (ps_fa s) (ps_so s).
Definition set_brk_ps (v : Z) (s : PState) := mkPS (ps_m s) v (ps_fa s) (ps_so s).
Definition set_fa_ps (v : unit) (s : PState) := mkPS (ps_m s) (ps_brk s) v (ps_so s).
Definition set_so_ps (v : stdout_st) (s : PState) := mkPS (ps_m s) (ps_brk s) (ps_fa s) v.

(* [comment removed for export] *)
Definition ps_init (reserved : list (Z * Z)) (atop : Z) : PState :=
  mkPS (strip (minit 0 reserved atop)) 0 tt stdout_init.
