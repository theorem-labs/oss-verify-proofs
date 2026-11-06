(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 Val IMap Mem Instr State Step Plan.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr Require Import Lib DefsA.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require Import Actr.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require Import UnreggC.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require Import GshC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.Mem FI St Step Plan CtrLib.
Open Scope Z_scope.

Module StrlenC.
Section WithSegs.
Variable segs : list Segment.
Definition slot_ok (C : GshC.gcfg) (st : sstate) : bool :=
  match IMap.find 0%uint63 (s_regs st) with
  | Some r0 => UnreggC.is_bgimage (rg_bg r0) && UnreggC.range_untouched r0 (GshC.g_slot C) 8
               && negb (in_priv_b (s_priv st) (of_Z (GshC.g_slot C)) 8%uint63)
  | None => false
  end.
Definition astrlen_apply (C : GshC.gcfg) (st : sstate) : option (list sstate) :=
  match ActrA.acall_pre ActrA.ASTACK None st with
  | Some (r, hargs, wl, st1) =>
      match getr st X10 with
      | VL a =>
          match GshC.gstr segs C st a with
          | Some len => if slot_ok C st then Some [setpc (setr (clobber st1) X10 (VL (wlit len))) r] else None
          | None => None
          end
      | _ => None
      end
  | None => None
  end.
Definition astrlen_c (C : GshC.gcfg) (pc : int) : contract := Contract pc (astrlen_apply C).
End WithSegs.
End StrlenC.

Module TwinB.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64 OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.IMap OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Instr OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.State OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Plan.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.Lib OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.DefsA.
Import Actr.TwinB.
Import UnreggC.TwinB.
Import GshC.TwinB.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.Mem FI St Step Plan CtrLib.
Open Scope Z_scope.

Module StrlenC.
Section WithSegs.
Variable segs : list Segment.
Definition slot_ok (C : GshC.TwinB.GshC.gcfg) (st : sstate) : bool :=
  match IMap.find 0%uint63 (s_regs st) with
  | Some r0 => UnreggC.TwinB.UnreggC.is_bgimage (rg_bg r0) && UnreggC.TwinB.UnreggC.range_untouched r0 (GshC.TwinB.GshC.g_slot C) 8
               && negb (in_priv_b (s_priv st) (of_Z (GshC.TwinB.GshC.g_slot C)) 8%uint63)
  | None => false
  end.
Definition astrlen_apply (C : GshC.TwinB.GshC.gcfg) (st : sstate) : option (list sstate) :=
  match ActrA.acall_pre ActrA.ASTACK None st with
  | Some (r, hargs, wl, st1) =>
      match getr st X10 with
      | VL a =>
          match GshC.TwinB.GshC.gstr segs C st a with
          | Some len => if slot_ok C st then Some [setpc (setr (clobber st1) X10 (VL (wlit len))) r] else None
          | None => None
          end
      | _ => None
      end
  | None => None
  end.
Definition astrlen_c (C : GshC.TwinB.GshC.gcfg) (pc : int) : contract := Contract pc (astrlen_apply C).
End WithSegs.
End StrlenC.
End TwinB.
