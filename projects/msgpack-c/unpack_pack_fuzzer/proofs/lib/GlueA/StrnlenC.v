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
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require Import FprintfSC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.Mem FI St Step Plan CtrLib.
Open Scope Z_scope.

Module StrnlenC.
Definition astrnlen_apply (st : sstate) : option (list sstate) :=
  match ActrA.acall_pre ActrA.ASTACK None st with
  | Some (r, hargs, wl, st1) =>
      match getr st X10, getr st X11 with
      | VP ks os, VL m =>
          match IMap.find ks (s_regs st), IMap.find CtrA.STRS_ID (s_regs st) with
          | Some rs, Some r12 =>
              match rg_bg rs, rg_cells r12, rg_bg r12 with
              | BGBlob j _, IMap.Leaf, BGBlob j12 sh12 =>
                  let js := if PrimInt63.eqb j 1%uint63 then 9%uint63 else 10%uint63 in
                  let H := rg_hi rs in
                  let fs := s_facts st in
                  if (PrimInt63.eqb j 1%uint63 || PrimInt63.eqb j 3%uint63)
                     && FprintfSC.str_ok_at X10 st wl j js
                     && sv_eqb (rg_hi r12) (CtrA.SZ 15%uint63) && PrimInt63.eqb j12 CtrA.STRS_ID && PrimInt63.eqb sh12 0%uint63
                     && PrimInt63.eqb (rg_lo r12) 0%uint63
                     && known_leu fs H (VL m)
                     && known_leu fs (VP CtrA.STRS_ID wzero) (VP ks wzero)
                     && known_leu fs (sv_alu ALU_ADD (VP ks wzero) H) (sv_alu ALU_ADD (VP CtrA.STRS_ID wzero) (CtrA.SZ 15%uint63))
                     && aligned fs (VP CtrA.STRS_ID wzero) 3%uint63
                  then
                    let L := sv_alu ALU_SUB H (VL wone) in
                    let st2 := addfact (addfact (addfact (setr (clobber st1) X10 L) (FULt L H)) (FULt L (VL m)))
                                       (FEq (sv_ext false 0%uint63 1%uint63 (VBlob false j L 1%uint63)) (VL wzero)) in
                    Some [setpc st2 r]
                  else None
              | _, _, _ => None
              end
          | _, _ => None
          end
      | _, _ => None
      end
  | None => None
  end.

Definition astrnlen_c (pc : int) : contract := Contract pc astrnlen_apply.
End StrnlenC.

Module TwinB.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64 OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.IMap OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Instr OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.State OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Plan.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.Lib OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.DefsA.
Import Actr.TwinB.
Import FprintfSC.TwinB.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.Mem FI St Step Plan CtrLib.
Open Scope Z_scope.

Module StrnlenC.
Definition astrnlen_apply (st : sstate) : option (list sstate) :=
  match ActrA.acall_pre ActrA.ASTACK None st with
  | Some (r, hargs, wl, st1) =>
      match getr st X10, getr st X11 with
      | VP ks os, VL m =>
          match IMap.find ks (s_regs st), IMap.find CtrA.STRS_ID (s_regs st) with
          | Some rs, Some r12 =>
              match rg_bg rs, rg_cells r12, rg_bg r12 with
              | BGBlob j _, IMap.Leaf, BGBlob j12 sh12 =>
                  let js := if PrimInt63.eqb j 1%uint63 then 9%uint63 else 10%uint63 in
                  let H := rg_hi rs in
                  let fs := s_facts st in
                  if (PrimInt63.eqb j 1%uint63 || PrimInt63.eqb j 3%uint63)
                     && FprintfSC.TwinB.FprintfSC.str_ok_at X10 st wl j js
                     && sv_eqb (rg_hi r12) (CtrA.SZ 15%uint63) && PrimInt63.eqb j12 CtrA.STRS_ID && PrimInt63.eqb sh12 0%uint63
                     && PrimInt63.eqb (rg_lo r12) 0%uint63
                     && known_leu fs H (VL m)
                     && known_leu fs (VP CtrA.STRS_ID wzero) (VP ks wzero)
                     && known_leu fs (sv_alu ALU_ADD (VP ks wzero) H) (sv_alu ALU_ADD (VP CtrA.STRS_ID wzero) (CtrA.SZ 15%uint63))
                     && aligned fs (VP CtrA.STRS_ID wzero) 3%uint63
                  then
                    let L := sv_alu ALU_SUB H (VL wone) in
                    let st2 := addfact (addfact (addfact (setr (clobber st1) X10 L) (FULt L H)) (FULt L (VL m)))
                                       (FEq (sv_ext false 0%uint63 1%uint63 (VBlob false j L 1%uint63)) (VL wzero)) in
                    Some [setpc st2 r]
                  else None
              | _, _, _ => None
              end
          | _, _ => None
          end
      | _, _ => None
      end
  | None => None
  end.

Definition astrnlen_c (pc : int) : contract := Contract pc astrnlen_apply.
End StrnlenC.
End TwinB.
