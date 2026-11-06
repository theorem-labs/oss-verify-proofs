(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Uint63.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import AxSymExec3.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Common.Br Require Import BrEnv.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
Record LeafAux : Type := LA {
  la_vt  : vtab;                 (* [comment removed for export] *)
  la_tl  : ttab;                 (* [comment removed for export] *)
  la_xtn : list (int * nat);     (* [comment removed for export] *)
  la_shp : list (int * int)      (* [comment removed for export] *)
}.

Definition page_lin (v : nat) : AX2.lin := AX2.lin_of (AX2.EMd M_MUL (AX2.ELit 4096) (AX2.EVar v)).

