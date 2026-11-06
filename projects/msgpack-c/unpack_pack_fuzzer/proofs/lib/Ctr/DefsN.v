(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 Val IMap Mem Instr State Step Plan.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr Require Import Lib DefsA.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val Mem FI St Step Plan CtrLib.
Open Scope Z_scope.
Unset Lia Cache.

Module CtrN.
Section WithImg.
Variable segs : list Segment.
Variables (ERRNO LIBC GOT GUARD TP : int) (CANARY : sv).

Definition malloc1_apply (st : sstate) : option (list sstate) :=
  match CtrA.malloc_apply segs ERRNO LIBC GOT GUARD TP CANARY st with
  | Some [_; stB] => Some [stB]
  | _ => None
  end.
Definition malloc1_c (pc : int) : contract := Contract pc malloc1_apply.

End WithImg.
End CtrN.
