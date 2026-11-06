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
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require Import RangeC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.Mem FI St Step Plan CtrLib.
Open Scope Z_scope.

Module BlobC.

Definition others_twins2 (wl : list (int * sv * w64)) (kd ks : int) : bool :=
  forallb (fun t : int * sv * w64 => let '(k, _, kdw) := t in PrimInt63.eqb k kd || PrimInt63.eqb k ks || weqb kdw ActrA.K_TWIN) wl.

Definition ablob_apply (st : sstate) : option (list sstate) :=
  match ActrA.acall_pre ActrA.ASTACK None st with
  | Some (r, hargs, wl, st1) =>
      match getr st X10, getr st X11 with
      | VP kd od, VP ks os =>
          match IMap.find kd (s_regs st), IMap.find ks (s_regs st), CtrA.win_lookup wl kd, CtrA.win_lookup wl ks with
          | Some rd, Some rs, Some (wlend, kdd), Some (wlens, kds) =>
              match rg_cells rd, rg_cells rs, rg_bg rs with
              | IMap.Leaf, IMap.Leaf, BGBlob j sh =>
                  if negb (RangeC.pat_ok st wl kd kdd && RangeC.pat_ok st wl ks kds) then None else
                  let n := getr st X12 in
                  let fs := s_facts st in
                  if weqb od wzero && weqb os wzero && negb (PrimInt63.eqb kd ks)
                     && weqb kdd CtrLib.K_BLOCK && weqb kds CtrLib.K_BLOCK && others_twins2 wl kd ks
                     && PrimInt63.eqb sh 0%uint63 && PrimInt63.eqb (rg_lo rs) 0%uint63 && PrimInt63.eqb (rg_lo rd) 0%uint63 && rg_w rd
                     && known_ltu fs (VL wzero) n && known_leu fs n (rg_hi rs) && known_leu fs n (rg_hi rd)
                     && known_leu fs n wlend && known_leu fs n wlens
                  then
                    let st2 := setr (clobber st1) X10 (getr st X10) in
                    Some [setpc (setregs st2 (IMap.add kd (Region 0%uint63 n true (BGBlob j 0%uint63) IMap.empty) (s_regs st2))) r]
                  else None
              | _, _, _ => None
              end
          | _, _, _, _ => None
          end
      | _, _ => None
      end
  | None => None
  end.

Definition ablob_c (pc : int) : contract := Contract pc ablob_apply.
End BlobC.

Module TwinB.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64 OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.IMap OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Instr OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.State OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Plan.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.Lib OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.DefsA.
Import Actr.TwinB.
Import RangeC.TwinB.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.Mem FI St Step Plan CtrLib.
Open Scope Z_scope.

Module BlobC.

Definition others_twins2 (wl : list (int * sv * w64)) (kd ks : int) : bool :=
  forallb (fun t : int * sv * w64 => let '(k, _, kdw) := t in PrimInt63.eqb k kd || PrimInt63.eqb k ks || weqb kdw ActrA.K_TWIN) wl.

Definition ablob_apply (st : sstate) : option (list sstate) :=
  match ActrA.acall_pre ActrA.ASTACK None st with
  | Some (r, hargs, wl, st1) =>
      match getr st X10, getr st X11 with
      | VP kd od, VP ks os =>
          match IMap.find kd (s_regs st), IMap.find ks (s_regs st), CtrA.win_lookup wl kd, CtrA.win_lookup wl ks with
          | Some rd, Some rs, Some (wlend, kdd), Some (wlens, kds) =>
              match rg_cells rd, rg_cells rs, rg_bg rs with
              | IMap.Leaf, IMap.Leaf, BGBlob j sh =>
                  if negb (RangeC.TwinB.RangeC.pat_ok st wl kd kdd && RangeC.TwinB.RangeC.pat_ok st wl ks kds) then None else
                  let n := getr st X12 in
                  let fs := s_facts st in
                  if weqb od wzero && weqb os wzero && negb (PrimInt63.eqb kd ks)
                     && weqb kdd CtrLib.K_BLOCK && weqb kds CtrLib.K_BLOCK && others_twins2 wl kd ks
                     && PrimInt63.eqb sh 0%uint63 && PrimInt63.eqb (rg_lo rs) 0%uint63 && PrimInt63.eqb (rg_lo rd) 0%uint63 && rg_w rd
                     && known_ltu fs (VL wzero) n && known_leu fs n (rg_hi rs) && known_leu fs n (rg_hi rd)
                     && known_leu fs n wlend && known_leu fs n wlens
                  then
                    let st2 := setr (clobber st1) X10 (getr st X10) in
                    Some [setpc (setregs st2 (IMap.add kd (Region 0%uint63 n true (BGBlob j 0%uint63) IMap.empty) (s_regs st2))) r]
                  else None
              | _, _, _ => None
              end
          | _, _, _, _ => None
          end
      | _, _ => None
      end
  | None => None
  end.

Definition ablob_c (pc : int) : contract := Contract pc ablob_apply.
End BlobC.
End TwinB.
