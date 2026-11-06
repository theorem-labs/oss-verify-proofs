(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 Val IMap Mem Instr State Step Plan.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr Require Import Lib DefsA DefsM.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require Import Actr.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require Import RangeC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.Mem FI St Step Plan CtrLib.
Open Scope Z_scope.

Module PayloadC.

Definition others_ok (wl : list (int * sv * w64)) (kp kb : int) : bool :=
  forallb (fun t : int * sv * w64 => let '(k, _, kdw) := t in
     PrimInt63.eqb k kp || PrimInt63.eqb k kb || weqb kdw ActrA.K_TWIN || weqb kdw RangeC.K_FRAME || weqb kdw RangeC.K_FTWIN) wl.

Definition apayload_apply (st : sstate) : option (list sstate) :=
  match ActrA.acall_pre ActrA.ASTACK None st with
  | Some (r, hargs, wl, st1) =>
      match getr st X10 with
      | VP kp op =>
          match CtrM.dst_offset (s_regs st) (getr st X11), IMap.find kp (s_regs st) with
          | Some (kb, OFF), Some rp =>
              match IMap.find kb (s_regs st), CtrA.win_lookup wl kp, CtrA.win_lookup wl kb with
              | Some rb, Some (wlenp, kdp), Some (wlenb, kdb) =>
                  match rg_cells rp, rg_cells rb, rg_bg rb with
                  | IMap.Leaf, IMap.Leaf, BGBlob j sh =>
                      if negb (RangeC.pat_ok st wl kp kdp && RangeC.pat_ok st wl kb kdb) then None else
                      let n := getr st X12 in
                      let fs := s_facts st in
                      if weqb op wzero && negb (PrimInt63.eqb kb kp)
                         && weqb kdp CtrLib.K_BLOCK && weqb kdb CtrLib.K_BLOCK && others_ok wl kp kb
                         && PrimInt63.eqb j 4%uint63 && PrimInt63.eqb sh 0%uint63 && PrimInt63.eqb (rg_lo rb) 0%uint63
                         && PrimInt63.eqb (rg_lo rp) 0%uint63 && rg_w rp
                         && fact_lookup fs (is_FEq OFF CtrM.B14) && fact_lookup fs (is_FEq n CtrM.B13)
                         && known_ltu fs (VL wzero) n && known_leu fs n (rg_hi rp)
                         && known_leu fs OFF (rg_hi rb) && known_leu fs n (sv_alu ALU_SUB (rg_hi rb) OFF)
                         && known_leu fs n wlenp && known_leu fs (rg_hi rb) wlenb
                      then
                        let st2 := setr (clobber st1) X10 (getr st X10) in
                        Some [setpc (setregs st2 (IMap.add kp (Region 0%uint63 n true (BGBlob 5%uint63 0%uint63) IMap.empty) (s_regs st2))) r]
                      else None
                  | _, _, _ => None
                  end
              | _, _, _ => None
              end
          | _, _ => None
          end
      | _ => None
      end
  | None => None
  end.

Definition apayload_c (pc : int) : contract := Contract pc apayload_apply.
End PayloadC.

Module TwinB.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64 OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.IMap OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Instr OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.State OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Plan.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.Lib OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.DefsA OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.DefsM.
Import Actr.TwinB.
Import RangeC.TwinB.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.Mem FI St Step Plan CtrLib.
Open Scope Z_scope.

Module PayloadC.

Definition others_ok (wl : list (int * sv * w64)) (kp kb : int) : bool :=
  forallb (fun t : int * sv * w64 => let '(k, _, kdw) := t in
     PrimInt63.eqb k kp || PrimInt63.eqb k kb || weqb kdw ActrA.K_TWIN || weqb kdw RangeC.TwinB.RangeC.K_FRAME || weqb kdw RangeC.TwinB.RangeC.K_FTWIN) wl.

Definition apayload_apply (st : sstate) : option (list sstate) :=
  match ActrA.acall_pre ActrA.ASTACK None st with
  | Some (r, hargs, wl, st1) =>
      match getr st X10 with
      | VP kp op =>
          match CtrM.dst_offset (s_regs st) (getr st X11), IMap.find kp (s_regs st) with
          | Some (kb, OFF), Some rp =>
              match IMap.find kb (s_regs st), CtrA.win_lookup wl kp, CtrA.win_lookup wl kb with
              | Some rb, Some (wlenp, kdp), Some (wlenb, kdb) =>
                  match rg_cells rp, rg_cells rb, rg_bg rb with
                  | IMap.Leaf, IMap.Leaf, BGBlob j sh =>
                      if negb (RangeC.TwinB.RangeC.pat_ok st wl kp kdp && RangeC.TwinB.RangeC.pat_ok st wl kb kdb) then None else
                      let n := getr st X12 in
                      let fs := s_facts st in
                      if weqb op wzero && negb (PrimInt63.eqb kb kp)
                         && weqb kdp CtrLib.K_BLOCK && weqb kdb CtrLib.K_BLOCK && others_ok wl kp kb
                         && PrimInt63.eqb j 4%uint63 && PrimInt63.eqb sh 0%uint63 && PrimInt63.eqb (rg_lo rb) 0%uint63
                         && PrimInt63.eqb (rg_lo rp) 0%uint63 && rg_w rp
                         && fact_lookup fs (is_FEq OFF CtrM.B14) && fact_lookup fs (is_FEq n CtrM.B13)
                         && known_ltu fs (VL wzero) n && known_leu fs n (rg_hi rp)
                         && known_leu fs OFF (rg_hi rb) && known_leu fs n (sv_alu ALU_SUB (rg_hi rb) OFF)
                         && known_leu fs n wlenp && known_leu fs (rg_hi rb) wlenb
                      then
                        let st2 := setr (clobber st1) X10 (getr st X10) in
                        Some [setpc (setregs st2 (IMap.add kp (Region 0%uint63 n true (BGBlob 5%uint63 0%uint63) IMap.empty) (s_regs st2))) r]
                      else None
                  | _, _, _ => None
                  end
              | _, _, _ => None
              end
          | _, _ => None
          end
      | _ => None
      end
  | None => None
  end.

Definition apayload_c (pc : int) : contract := Contract pc apayload_apply.
End PayloadC.
End TwinB.
