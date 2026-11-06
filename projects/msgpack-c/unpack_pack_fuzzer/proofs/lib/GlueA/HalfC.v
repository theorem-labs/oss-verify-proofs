(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 Val IMap Mem Instr State Step Plan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.Mem FI St Step Plan.
Open Scope Z_scope.

Module HalfC.
Section WithSegs.
Variable segs : list Segment.

Fixpoint push_cells (st : sstate) (base : sv) (cells : list (int * sv)) : option sstate :=
  match cells with
  | [] => Some st
  | (off, v) :: tl =>
      match do_store segs st (sv_alu ALU_ADD base (VL (wlit off))) 8%uint63 v with
      | inl st' => push_cells st' base tl
      | inr _ => None
      end
  end.

Fixpoint set_regs (st : sstate) (l : list (r5 * sv)) : sstate :=
  match l with
  | [] => st
  | (x, v) :: tl => set_regs (setr st x v) tl
  end.
End WithSegs.
End HalfC.

Module TwinB.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64 OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.IMap OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Instr OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.State OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Plan.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.Mem FI St Step Plan.
Open Scope Z_scope.

Module HalfC.
Section WithSegs.
Variable segs : list Segment.

Fixpoint push_cells (st : sstate) (base : sv) (cells : list (int * sv)) : option sstate :=
  match cells with
  | [] => Some st
  | (off, v) :: tl =>
      match do_store segs st (sv_alu ALU_ADD base (VL (wlit off))) 8%uint63 v with
      | inl st' => push_cells st' base tl
      | inr _ => None
      end
  end.

Fixpoint set_regs (st : sstate) (l : list (r5 * sv)) : sstate :=
  match l with
  | [] => st
  | (x, v) :: tl => set_regs (setr st x v) tl
  end.
End WithSegs.
End HalfC.
End TwinB.
