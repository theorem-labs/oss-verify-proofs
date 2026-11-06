(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 Val IMap Mem Instr State Step Plan.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr Require Import Lib.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.Mem FI St Step Plan CtrLib.
Open Scope Z_scope.

Module OpDropC.
Definition drop_ops (id : int) (os : list opinst) : list opinst := List.filter (fun o => negb (PrimInt63.eqb (op_id o) id)) os.
Definition op_drop_apply (id : int) (st : sstate) : option (list sstate) :=
  match find_op id (s_ops st) with
  | Some _ =>
      if PrimInt63.eqb id HEAP_ID then None
      else Some [SS (s_pc st) (s_rf st) (s_ff st) (s_resv st) (s_regs st) (s_facts st) (drop_ops id (s_ops st)) (s_priv st) (s_next st)]
  | None => None
  end.
Definition op_drop_c (id : int) (pc : int) : contract := Contract pc (op_drop_apply id).
End OpDropC.

Module TwinB.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64 OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.IMap OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Instr OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.State OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Plan.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.Lib.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.Mem FI St Step Plan CtrLib.
Open Scope Z_scope.

Module OpDropC.
Definition drop_ops (id : int) (os : list opinst) : list opinst := List.filter (fun o => negb (PrimInt63.eqb (op_id o) id)) os.
Definition op_drop_apply (id : int) (st : sstate) : option (list sstate) :=
  match find_op id (s_ops st) with
  | Some _ =>
      if PrimInt63.eqb id HEAP_ID then None
      else Some [SS (s_pc st) (s_rf st) (s_ff st) (s_resv st) (s_regs st) (s_facts st) (drop_ops id (s_ops st)) (s_priv st) (s_next st)]
  | None => None
  end.
Definition op_drop_c (id : int) (pc : int) : contract := Contract pc (op_drop_apply id).
End OpDropC.
End TwinB.
