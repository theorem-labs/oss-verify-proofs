(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 Val IMap Mem Instr State Step Plan.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr Require Import Lib Defs DefsA.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require Import Actr.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require Import HalfC VprintfC FprintfC StrRegC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.Mem FI St Step Plan CtrLib.
Open Scope Z_scope.

Module FprintfSC.
Definition FMT_USAGE : w64 := wlit 90128%uint63.
Definition FMT_CANTOPEN : w64 := wlit 126556%uint63.
Definition FMT_READERR : w64 := wlit 126577%uint63.

Section WithSegs.
Variable segs : list Segment.

Definition str_ok_at (x : r5) (st : sstate) (wl : list (int * sv * w64)) (j js : int) : bool :=
  match getr st x with
  | VP k o => match IMap.find k (s_regs st) with
              | Some r => weqb o wzero && StrRegC.str_reg_ok st wl k r j js
              | None => false
              end
  | _ => false
  end.
Definition str_ok (st : sstate) (wl : list (int * sv * w64)) (j js : int) : bool := str_ok_at X12 st wl j js.

Definition afprintf_s_pre_apply (FMT : w64) (j js : int) (st : sstate) : option (list sstate) :=
  match ActrA.acall_pre ActrA.ASTACK None st with
  | Some (r, hargs, wl, st1) => if str_ok st wl j js then FprintfC.afprintf_pre_apply segs FMT st else None
  | None => None
  end.

Definition afprintf_s_pre_c (FMT : w64) (j js : int) (pc : int) : contract := Contract pc (afprintf_s_pre_apply FMT j js).
End WithSegs.
End FprintfSC.

Module TwinB.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64 OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.IMap OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Instr OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.State OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Plan.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.Lib OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.Defs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.DefsA.
Import Actr.TwinB.
Import HalfC.TwinB VprintfC.TwinB FprintfC.TwinB StrRegC.TwinB.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.Mem FI St Step Plan CtrLib.
Open Scope Z_scope.

Module FprintfSC.
Definition FMT_USAGE : w64 := wlit 90434%uint63.
Definition FMT_CANTOPEN : w64 := wlit 126819%uint63.
Definition FMT_READERR : w64 := wlit 126840%uint63.

Section WithSegs.
Variable segs : list Segment.

Definition str_ok_at (x : r5) (st : sstate) (wl : list (int * sv * w64)) (j js : int) : bool :=
  match getr st x with
  | VP k o => match IMap.find k (s_regs st) with
              | Some r => weqb o wzero && StrRegC.TwinB.StrRegC.str_reg_ok st wl k r j js
              | None => false
              end
  | _ => false
  end.
Definition str_ok (st : sstate) (wl : list (int * sv * w64)) (j js : int) : bool := str_ok_at X12 st wl j js.

Definition afprintf_s_pre_apply (FMT : w64) (j js : int) (st : sstate) : option (list sstate) :=
  match ActrA.acall_pre ActrA.ASTACK None st with
  | Some (r, hargs, wl, st1) => if str_ok st wl j js then FprintfC.TwinB.FprintfC.afprintf_pre_apply segs FMT st else None
  | None => None
  end.

Definition afprintf_s_pre_c (FMT : w64) (j js : int) (pc : int) : contract := Contract pc (afprintf_s_pre_apply FMT j js).
End WithSegs.
End FprintfSC.
End TwinB.
