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
Import ListNotations.
Import W64 Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.Mem FI St Step Plan CtrLib.
Open Scope Z_scope.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require KnownT.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module SinkC.

Definition client_kind (kd : w64) : bool :=
  negb (weqb kd wzero) && negb (weqb kd ActrA.K_TWIN) && negb (weqb kd RangeC.K_FRAME) && negb (weqb kd RangeC.K_FTWIN)
  && (weqb kd (wlit 1%uint63) || weqb kd (wlit 2%uint63) || weqb kd (wlit 3%uint63) || weqb kd (wlit 4%uint63) || weqb kd (wlit 5%uint63) || weqb kd (wlit 6%uint63)).

Definition asink_apply (st : sstate) : option (list sstate) :=
  match ActrA.acall_pre ActrA.ASTACK None st with
  | Some (r, hargs, wl, st1) =>
      match getr st X10 with
      | VP ka oa =>
          match CtrA.sym_offset (s_regs st) (getr st X11), IMap.find ka (s_regs st) with
          | Some (kd, OFF), Some ra =>
              match IMap.find kd (s_regs st), rg_cells ra, CtrA.win_lookup wl ka, CtrA.win_lookup wl kd with
              | Some rd, IMap.Leaf, Some (wlena, kda), Some (wlend, kdd) =>
                  if negb (RangeC.pat_ok st wl ka kda && RangeC.pat_ok st wl kd kdd) then None else
                  let n := getr st X12 in
                  let fs := s_facts st in
                  if weqb oa wzero && is_bgnone (rg_bg ra) && PrimInt63.eqb (rg_lo ra) 0%uint63 && rg_w ra && PrimInt63.eqb (rg_lo rd) 0%uint63
                     && negb (PrimInt63.eqb kd ka)
                     && client_kind kda && client_kind kdd
                     && KnownT.KnownT.known_leu_t fs n (rg_hi ra) && KnownT.KnownT.known_leu_t fs OFF (rg_hi rd) && KnownT.KnownT.known_leu_t fs n (sv_alu ALU_SUB (rg_hi rd) OFF)
                     && KnownT.KnownT.known_leu_t fs (rg_hi ra) wlena && KnownT.KnownT.known_leu_t fs (rg_hi rd) wlend
                  then Some [setpc (setr (clobber st1) X10 (getr st X10)) r]
                  else None
              | _, _, _, _ => None
              end
          | _, _ => None
          end
      | _ => None
      end
  | None => None
  end.

Definition asink_c (pc : int) : contract := Contract pc asink_apply.
End SinkC.

Module TwinB.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64 OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.IMap OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Instr OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.State OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Plan.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.Lib OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.DefsA.
Import Actr.TwinB.
Import RangeC.TwinB.

Import ListNotations.
Import W64 Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.Mem FI St Step Plan CtrLib.
Open Scope Z_scope.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module SinkC.

Definition client_kind (kd : w64) : bool :=
  negb (weqb kd wzero) && negb (weqb kd ActrA.K_TWIN) && negb (weqb kd RangeC.TwinB.RangeC.K_FRAME) && negb (weqb kd RangeC.TwinB.RangeC.K_FTWIN)
  && (weqb kd (wlit 1%uint63) || weqb kd (wlit 2%uint63) || weqb kd (wlit 3%uint63) || weqb kd (wlit 4%uint63) || weqb kd (wlit 5%uint63) || weqb kd (wlit 6%uint63)).

Definition asink_apply (st : sstate) : option (list sstate) :=
  match ActrA.acall_pre ActrA.ASTACK None st with
  | Some (r, hargs, wl, st1) =>
      match getr st X10 with
      | VP ka oa =>
          match CtrA.sym_offset (s_regs st) (getr st X11), IMap.find ka (s_regs st) with
          | Some (kd, OFF), Some ra =>
              match IMap.find kd (s_regs st), rg_cells ra, CtrA.win_lookup wl ka, CtrA.win_lookup wl kd with
              | Some rd, IMap.Leaf, Some (wlena, kda), Some (wlend, kdd) =>
                  if negb (RangeC.TwinB.RangeC.pat_ok st wl ka kda && RangeC.TwinB.RangeC.pat_ok st wl kd kdd) then None else
                  let n := getr st X12 in
                  let fs := s_facts st in
                  if weqb oa wzero && is_bgnone (rg_bg ra) && PrimInt63.eqb (rg_lo ra) 0%uint63 && rg_w ra && PrimInt63.eqb (rg_lo rd) 0%uint63
                     && negb (PrimInt63.eqb kd ka)
                     && client_kind kda && client_kind kdd
                     && KnownT.KnownT.known_leu_t fs n (rg_hi ra) && KnownT.KnownT.known_leu_t fs OFF (rg_hi rd) && KnownT.KnownT.known_leu_t fs n (sv_alu ALU_SUB (rg_hi rd) OFF)
                     && KnownT.KnownT.known_leu_t fs (rg_hi ra) wlena && KnownT.KnownT.known_leu_t fs (rg_hi rd) wlend
                  then Some [setpc (setr (clobber st1) X10 (getr st X10)) r]
                  else None
              | _, _, _, _ => None
              end
          | _, _ => None
          end
      | _ => None
      end
  | None => None
  end.

Definition asink_c (pc : int) : contract := Contract pc asink_apply.
End SinkC.
End TwinB.
