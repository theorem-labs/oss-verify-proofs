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
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require Import HalfC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.Mem FI St Step Plan CtrLib.
Open Scope Z_scope.

Module VprintfC.
Definition ZRO_ID : int := 13%uint63.
Definition FMT_D : w64 := wlit 85252%uint63.
Definition STDOUT : w64 := wlit 875656%uint63.
Definition RET_VF : w64 := wlit 330132%uint63.
Definition RET_VP : w64 := wlit 327204%uint63.
Definition REAL_VF : int := 802012%uint63.
Definition NEG96 : w64 := wsub wzero (wlit 96%uint63).

Section WithSegs.
Variable segs : list Segment.

Definition avprintf_pre_apply (st : sstate) : option (list sstate) :=
  match ActrA.acall_pre ActrA.ASTACK None st with
  | Some (r, hargs, wl, st1) =>
      let a0 := getr st X10 in let a1 := getr st X11 in
      if CtrS.is_lit a0 FMT_D && match find_op ZRO_ID (s_ops st) with Some [] => true | _ => false end then
        let sp' := sv_alu ALU_ADD (getr st X2) (VL NEG96) in
        let st2 := setpc (setr (clobber st1) X10 (VL STDOUT)) r in
        match HalfC.push_cells segs st2 sp'
                [(16%uint63, getr st X18); (24%uint63, a1); (32%uint63, a0); (40%uint63, VL RET_VP);
                 (72%uint63, getr st X9); (80%uint63, getr st X8); (88%uint63, VL (wlit r))] with
        | Some st3 =>
            Some [setpc (HalfC.set_regs st3 [(X1, VL RET_VF); (X2, sp'); (X8, a0); (X9, VL STDOUT); (X11, a0); (X12, a1); (X18, a1)]) REAL_VF]
        | None => None
        end
      else None
  | None => None
  end.

Definition avprintf_pre_c (pc : int) : contract := Contract pc avprintf_pre_apply.
End WithSegs.
End VprintfC.

Module TwinB.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64 OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.IMap OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Instr OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.State OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Plan.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.Lib OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.Defs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.DefsA.
Import Actr.TwinB.
Import HalfC.TwinB.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.Mem FI St Step Plan CtrLib.
Open Scope Z_scope.

Module VprintfC.
Definition ZRO_ID : int := 13%uint63.
Definition FMT_D : w64 := wlit 85506%uint63.
Definition STDOUT : w64 := wlit 884128%uint63.
Definition RET_VF : w64 := wlit 332580%uint63.
Definition RET_VP : w64 := wlit 329652%uint63.
Definition REAL_VF : int := 810488%uint63.
Definition NEG96 : w64 := wsub wzero (wlit 96%uint63).

Section WithSegs.
Variable segs : list Segment.

Definition avprintf_pre_apply (st : sstate) : option (list sstate) :=
  match ActrA.acall_pre ActrA.ASTACK None st with
  | Some (r, hargs, wl, st1) =>
      let a0 := getr st X10 in let a1 := getr st X11 in
      if CtrS.is_lit a0 FMT_D && match find_op ZRO_ID (s_ops st) with Some [] => true | _ => false end then
        let sp' := sv_alu ALU_ADD (getr st X2) (VL NEG96) in
        let st2 := setpc (setr (clobber st1) X10 (VL STDOUT)) r in
        match HalfC.TwinB.HalfC.push_cells segs st2 sp'
                [(16%uint63, getr st X18); (24%uint63, a1); (32%uint63, a0); (40%uint63, VL RET_VP);
                 (72%uint63, getr st X9); (80%uint63, getr st X8); (88%uint63, VL (wlit r))] with
        | Some st3 =>
            Some [setpc (HalfC.TwinB.HalfC.set_regs st3 [(X1, VL RET_VF); (X2, sp'); (X8, a0); (X9, VL STDOUT); (X11, a0); (X12, a1); (X18, a1)]) REAL_VF]
        | None => None
        end
      else None
  | None => None
  end.

Definition avprintf_pre_c (pc : int) : contract := Contract pc avprintf_pre_apply.
End WithSegs.
End VprintfC.
End TwinB.
