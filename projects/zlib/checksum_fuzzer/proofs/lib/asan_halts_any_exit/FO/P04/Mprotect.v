(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
(** * FO.P04.Mprotect — lps patch 04's mprotect refusal condition, as agent-side definitions

    See [FO.P04.Mmap]: the one fallible [mprotect] arm was forced to fail under the patch exactly when
    the commit charge did not fit ([mprotect_budget_ok]); copied verbatim so the patch-04 trees keep
    reading [Mprotect.mprotect_refusable]. *)

From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mprotect.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Definition mprotect_errnos_when (forced : bool) : list Z :=
  if forced then mprotect_errnos else [].

Definition mprotect_refusable (m : Model) (addr n : word) : bool :=
  negb (mprotect_budget_ok m addr n).
