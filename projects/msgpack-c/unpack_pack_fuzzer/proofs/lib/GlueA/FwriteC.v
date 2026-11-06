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

Module FwriteC.
Definition RET_FW : w64 := wlit 324804%uint63.
Definition REAL_FW : int := 801448%uint63.
Definition NEG2128 : w64 := wsub wzero (wlit 2128%uint63).
Definition NEG56 : w64 := wsub wzero (wlit 56%uint63).

Section WithSegs.
Variable segs : list Segment.

Definition fw_sp (st : sstate) : sv := sv_alu ALU_ADD (getr st X2) (VL NEG2128).
Definition fw_fr (st : sstate) : sv := sv_alu ALU_ADD (getr st X2) (VL NEG56).
Definition fw_cells (st : sstate) (r : int) : list (int * sv) :=
  [(0%uint63, getr st X21); (8%uint63, getr st X20); (16%uint63, getr st X19); (24%uint63, getr st X18);
   (32%uint63, getr st X9); (40%uint63, getr st X8); (48%uint63, VL (wlit r))].
Definition fw_regs (st : sstate) : list (r5 * sv) :=
  [(X1, VL RET_FW); (X2, fw_sp st); (X8, getr st X2); (X9, getr st X11); (X11, getr st X11); (X12, getr st X12); (X13, getr st X13);
   (X18, getr st X10); (X19, getr st X13); (X20, getr st X12); (X21, VL (wlit 1%uint63))].

Definition afwrite_pre_apply (st : sstate) : option (list sstate) :=
  match ActrA.acall_pre ActrA.ASTACK None st with
  | Some (r, hargs, wl, st1) =>
      let st2 := setpc (setr (clobber st1) X10 (getr st X10)) r in
      match HalfC.push_cells segs st2 (fw_fr st) (fw_cells st r) with
      | Some st3 => Some [setpc (HalfC.set_regs st3 (fw_regs st)) REAL_FW]
      | None => None
      end
  | None => None
  end.

Definition afwrite_pre_c (pc : int) : contract := Contract pc afwrite_pre_apply.
End WithSegs.
End FwriteC.

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

Module FwriteC.
Definition RET_FW : w64 := wlit 327252%uint63.
Definition REAL_FW : int := 809924%uint63.
Definition NEG2128 : w64 := wsub wzero (wlit 2128%uint63).
Definition NEG56 : w64 := wsub wzero (wlit 56%uint63).

Section WithSegs.
Variable segs : list Segment.

Definition fw_sp (st : sstate) : sv := sv_alu ALU_ADD (getr st X2) (VL NEG2128).
Definition fw_fr (st : sstate) : sv := sv_alu ALU_ADD (getr st X2) (VL NEG56).
Definition fw_cells (st : sstate) (r : int) : list (int * sv) :=
  [(0%uint63, getr st X21); (8%uint63, getr st X20); (16%uint63, getr st X19); (24%uint63, getr st X18);
   (32%uint63, getr st X9); (40%uint63, getr st X8); (48%uint63, VL (wlit r))].
Definition fw_regs (st : sstate) : list (r5 * sv) :=
  [(X1, VL RET_FW); (X2, fw_sp st); (X8, getr st X2); (X9, getr st X11); (X11, getr st X11); (X12, getr st X12); (X13, getr st X13);
   (X18, getr st X10); (X19, getr st X13); (X20, getr st X12); (X21, VL (wlit 1%uint63))].

Definition afwrite_pre_apply (st : sstate) : option (list sstate) :=
  match ActrA.acall_pre ActrA.ASTACK None st with
  | Some (r, hargs, wl, st1) =>
      let st2 := setpc (setr (clobber st1) X10 (getr st X10)) r in
      match HalfC.TwinB.HalfC.push_cells segs st2 (fw_fr st) (fw_cells st r) with
      | Some st3 => Some [setpc (HalfC.TwinB.HalfC.set_regs st3 (fw_regs st)) REAL_FW]
      | None => None
      end
  | None => None
  end.

Definition afwrite_pre_c (pc : int) : contract := Contract pc afwrite_pre_apply.
End WithSegs.
End FwriteC.
End TwinB.
