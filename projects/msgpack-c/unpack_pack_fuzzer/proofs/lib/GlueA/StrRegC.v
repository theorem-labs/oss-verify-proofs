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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.Mem FI St Step Plan CtrLib.
Open Scope Z_scope.

Module StrRegC.
Definition ZARG_ID : int := 14%uint63.
Definition TOP16 : w64 := wlit 140737488355312%uint63.

Definition str_region (r : region) (j js : int) : bool :=
  PrimInt63.eqb (rg_lo r) 0%uint63 && negb (rg_w r)
  && match rg_hi r with VBlob false js' (VL z) w8 => PrimInt63.eqb js' js && weqb z wzero && PrimInt63.eqb w8 8%uint63 | _ => false end
  && match rg_bg r with BGBlob j' sh => PrimInt63.eqb j' j && PrimInt63.eqb sh 0%uint63 | _ => false end
  && match rg_cells r with IMap.Leaf => true | _ => false end.

Definition str_reg_ok (st : sstate) (wl : list (int * sv * w64)) (k : int) (r : region) (j js : int) : bool :=
  match find_op ZARG_ID (s_ops st) with
  | Some [az] =>
      negb (PrimInt63.eqb k 0%uint63) && str_region r j js
      && match CtrA.win_lookup wl k with None => true | Some _ => false end
      && match ActrA.sp_region st with Some (ks, _, _) => negb (PrimInt63.eqb k ks) | None => false end
      && known_leu (s_facts st) (sv_alu ALU_ADD az (VL (wlit 72%uint63))) (VP k wzero)
      && known_leu (s_facts st) (sv_alu ALU_ADD (VP k wzero) (rg_hi r)) (VL TOP16)
  | _ => false
  end.

Definition arg_range (st : sstate) (wl : list (int * sv * w64)) (k : int) (o : w64) (len : int) : bool :=
  match IMap.find k (s_regs st) with
  | Some r => (str_reg_ok st wl k r 1%uint63 9%uint63 || str_reg_ok st wl k r 3%uint63 10%uint63)
              && negb (wt o) && negb (wt (wadd o (wlit len))) && wleu o (wadd o (wlit len))
              && known_leu (s_facts st) (VL (wadd o (wlit len))) (rg_hi r)
  | None => false
  end.
End StrRegC.

Module TwinB.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64 OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.IMap OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Instr OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.State OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Plan.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.Lib OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.Defs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.DefsA.
Import Actr.TwinB.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.Mem FI St Step Plan CtrLib.
Open Scope Z_scope.

Module StrRegC.
Definition ZARG_ID : int := 14%uint63.
Definition TOP16 : w64 := wlit 140737488355312%uint63.

Definition str_region (r : region) (j js : int) : bool :=
  PrimInt63.eqb (rg_lo r) 0%uint63 && negb (rg_w r)
  && match rg_hi r with VBlob false js' (VL z) w8 => PrimInt63.eqb js' js && weqb z wzero && PrimInt63.eqb w8 8%uint63 | _ => false end
  && match rg_bg r with BGBlob j' sh => PrimInt63.eqb j' j && PrimInt63.eqb sh 0%uint63 | _ => false end
  && match rg_cells r with IMap.Leaf => true | _ => false end.

Definition str_reg_ok (st : sstate) (wl : list (int * sv * w64)) (k : int) (r : region) (j js : int) : bool :=
  match find_op ZARG_ID (s_ops st) with
  | Some [az] =>
      negb (PrimInt63.eqb k 0%uint63) && str_region r j js
      && match CtrA.win_lookup wl k with None => true | Some _ => false end
      && match ActrA.sp_region st with Some (ks, _, _) => negb (PrimInt63.eqb k ks) | None => false end
      && known_leu (s_facts st) (sv_alu ALU_ADD az (VL (wlit 72%uint63))) (VP k wzero)
      && known_leu (s_facts st) (sv_alu ALU_ADD (VP k wzero) (rg_hi r)) (VL TOP16)
  | _ => false
  end.

Definition arg_range (st : sstate) (wl : list (int * sv * w64)) (k : int) (o : w64) (len : int) : bool :=
  match IMap.find k (s_regs st) with
  | Some r => (str_reg_ok st wl k r 1%uint63 9%uint63 || str_reg_ok st wl k r 3%uint63 10%uint63)
              && negb (wt o) && negb (wt (wadd o (wlit len))) && wleu o (wadd o (wlit len))
              && known_leu (s_facts st) (VL (wadd o (wlit len))) (rg_hi r)
  | None => false
  end.
End StrRegC.
End TwinB.
