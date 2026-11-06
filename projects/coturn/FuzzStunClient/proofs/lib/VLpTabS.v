(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import List.
From Corelib Require Import PrimInt63 PrimString.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import VLpTabS0 VLpTabSboth.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Definition LPT_BITS : int := 18%uint63.
Definition LPT_PIECES : list (PrimString.string * int) := LPT_BASE ++ LPT_BOTH.
