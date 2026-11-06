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
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require Import HalfC VprintfC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.Mem FI St Step Plan CtrLib.
Open Scope Z_scope.

Module FprintfC.
Definition FMT_TOOBIG : w64 := wlit 108802%uint63.
Definition RET_FP : w64 := wlit 331184%uint63.
Definition NEG112 : w64 := wsub wzero (wlit 112%uint63).
Definition NEG48 : w64 := wsub wzero (wlit 48%uint63).

Section WithSegs.
Variable segs : list Segment.

Definition fp_sp (st : sstate) : sv := sv_alu ALU_ADD (getr st X2) (VL NEG112).
Definition fp_ap (st : sstate) : sv := sv_alu ALU_ADD (getr st X2) (VL NEG48).
Definition fp_cells (st : sstate) (r : int) : list (int * sv) :=
  [(32%uint63, getr st X18); (40%uint63, getr st X9); (48%uint63, getr st X8); (56%uint63, VL (wlit r));
   (64%uint63, getr st X12); (72%uint63, getr st X13); (80%uint63, getr st X14); (88%uint63, getr st X15);
   (96%uint63, getr st X16); (104%uint63, getr st X17)].
Definition fp_regs (st : sstate) : list (r5 * sv) :=
  [(X1, VL RET_FP); (X2, fp_sp st); (X8, getr st X11); (X9, getr st X10); (X11, getr st X11); (X12, fp_ap st); (X18, fp_ap st)].

Definition afprintf_pre_apply (FMT : w64) (st : sstate) : option (list sstate) :=
  match ActrA.acall_pre ActrA.ASTACK None st with
  | Some (r, hargs, wl, st1) =>
      if CtrS.is_lit (getr st X11) FMT && match find_op VprintfC.ZRO_ID (s_ops st) with Some [] => true | _ => false end then
        let st2 := setpc (setr (clobber st1) X10 (getr st X10)) r in
        match HalfC.push_cells segs st2 (fp_sp st) (fp_cells st r) with
        | Some st3 => Some [setpc (HalfC.set_regs st3 (fp_regs st)) VprintfC.REAL_VF]
        | None => None
        end
      else None
  | None => None
  end.

Definition afprintf_pre_c (FMT : w64) (pc : int) : contract := Contract pc (afprintf_pre_apply FMT).
End WithSegs.
End FprintfC.

Module TwinB.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64 OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.IMap OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Instr OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.State OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Plan.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.Lib OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.Defs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.DefsA.
Import Actr.TwinB.
Import HalfC.TwinB VprintfC.TwinB.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.Mem FI St Step Plan CtrLib.
Open Scope Z_scope.

Module FprintfC.
Definition FMT_TOOBIG : w64 := wlit 108736%uint63.
Definition RET_FP : w64 := wlit 333632%uint63.
Definition NEG112 : w64 := wsub wzero (wlit 112%uint63).
Definition NEG48 : w64 := wsub wzero (wlit 48%uint63).

Section WithSegs.
Variable segs : list Segment.

Definition fp_sp (st : sstate) : sv := sv_alu ALU_ADD (getr st X2) (VL NEG112).
Definition fp_ap (st : sstate) : sv := sv_alu ALU_ADD (getr st X2) (VL NEG48).
Definition fp_cells (st : sstate) (r : int) : list (int * sv) :=
  [(32%uint63, getr st X18); (40%uint63, getr st X9); (48%uint63, getr st X8); (56%uint63, VL (wlit r));
   (64%uint63, getr st X12); (72%uint63, getr st X13); (80%uint63, getr st X14); (88%uint63, getr st X15);
   (96%uint63, getr st X16); (104%uint63, getr st X17)].
Definition fp_regs (st : sstate) : list (r5 * sv) :=
  [(X1, VL RET_FP); (X2, fp_sp st); (X8, getr st X11); (X9, getr st X10); (X11, getr st X11); (X12, fp_ap st); (X18, fp_ap st)].

Definition afprintf_pre_apply (FMT : w64) (st : sstate) : option (list sstate) :=
  match ActrA.acall_pre ActrA.ASTACK None st with
  | Some (r, hargs, wl, st1) =>
      if CtrS.is_lit (getr st X11) FMT && match find_op VprintfC.TwinB.VprintfC.ZRO_ID (s_ops st) with Some [] => true | _ => false end then
        let st2 := setpc (setr (clobber st1) X10 (getr st X10)) r in
        match HalfC.TwinB.HalfC.push_cells segs st2 (fp_sp st) (fp_cells st r) with
        | Some st3 => Some [setpc (HalfC.TwinB.HalfC.set_regs st3 (fp_regs st)) VprintfC.TwinB.VprintfC.REAL_VF]
        | None => None
        end
      else None
  | None => None
  end.

Definition afprintf_pre_c (FMT : w64) (pc : int) : contract := Contract pc (afprintf_pre_apply FMT).
End WithSegs.
End FprintfC.
End TwinB.
