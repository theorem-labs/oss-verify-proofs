(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import SymDriveLet RefItabW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac run_block_with_let_img HR HK fuel stops scr NX keep :=
  first [ run_block_with_letI RefItabW.ITABW RefItabW.ITABW_ok HR HK fuel stops scr NX keep
        | run_block_with_let HR HK fuel stops scr NX keep ].
