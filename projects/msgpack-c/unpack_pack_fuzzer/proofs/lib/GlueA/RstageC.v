(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 Val IMap Mem Instr State Step Plan.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr Require Import Lib DefsA DefsB Defs.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require Import Actr.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require Import ReadC RangeC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.Mem FI St Step Plan CtrLib.
Open Scope Z_scope.

Module RstageC.
Section WithCfg.
Variable C : ReadC.rcfg.

Definition others_twins (wl : list (int * sv * w64)) (kb : int) : bool :=
  forallb (fun t : int * sv * w64 => let '(k, _, kd) := t in PrimInt63.eqb k kb || weqb kd ActrA.K_TWIN) wl.

Definition prefix_ok (fs : list fact) (rb : region) (X : sv) : bool :=
  (match rg_bg rb with BGBlob j sh => PrimInt63.eqb j 4%uint63 && PrimInt63.eqb sh 0%uint63 | _ => false end && known_eq fs (rg_hi rb) X)
  || known_eq fs X (VL wzero).

Definition arstage_apply (st : sstate) : option (list sstate) :=
  match ActrA.acall_pre ActrA.ASTACK None st with
  | Some (r, hargs, wl, st1) =>
      match getr st X11, CtrA.sym_offset (s_regs st) (getr st X10), find_op ReadC.RSTV_ID (s_ops st), find_op (ReadC.r_zsh C) (s_ops st) with
      | VL rs, Some (kb, X), Some [off; n'], Some [] =>
          match CtrA.win_lookup wl kb, IMap.find kb (s_regs st) with
          | Some (wlen, kd), Some rb =>
              if negb (RangeC.pat_ok st wl kb kd) then None else
              let n := getr st X12 in
              let fs := s_facts st in
              if weqb rs (wlit (ReadC.r_stage C)) && Nat.eqb (CtrA.count_op ReadC.RSTV_ID (s_ops st)) 1%nat
                 && weqb kd CtrLib.K_BLOCK && others_twins wl kb
                 && match rg_cells rb with IMap.Leaf => true | _ => false end
                 && prefix_ok fs rb X && PrimInt63.eqb (rg_lo rb) 0%uint63 && rg_w rb
                 && known_eq fs off X && known_eq fs n' n
                 && known_leu fs X wlen && known_leu fs n (sv_alu ALU_SUB wlen X) && known_ltu fs (VL wzero) n
              then
                let st2 := setr (clobber st1) X10 (getr st X10) in
                let rb' := Region 0%uint63 (CtrB.new_hi fs X n) true (BGBlob 4%uint63 0%uint63) IMap.empty in
                let st3 := set_ops (setregs st2 (IMap.add kb rb' (s_regs st2)))
                                   (set_op ReadC.RSTV_ID [sv_alu ALU_ADD off n; VL wzero] (s_ops st2)) in
                Some [setpc st3 r]
              else None
          | _, _ => None
          end
      | _, _, _, _ => None
      end
  | None => None
  end.

Definition arstage_c (pc : int) : contract := Contract pc arstage_apply.
End WithCfg.
End RstageC.

Module TwinB.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64 OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.IMap OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Instr OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.State OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Plan.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.Lib OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.DefsA OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.DefsB OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.Defs.
Import Actr.TwinB.
Import ReadC.TwinB RangeC.TwinB.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.Mem FI St Step Plan CtrLib.
Open Scope Z_scope.

Module RstageC.
Section WithCfg.
Variable C : ReadC.TwinB.ReadC.rcfg.

Definition others_twins (wl : list (int * sv * w64)) (kb : int) : bool :=
  forallb (fun t : int * sv * w64 => let '(k, _, kd) := t in PrimInt63.eqb k kb || weqb kd ActrA.K_TWIN) wl.

Definition prefix_ok (fs : list fact) (rb : region) (X : sv) : bool :=
  (match rg_bg rb with BGBlob j sh => PrimInt63.eqb j 4%uint63 && PrimInt63.eqb sh 0%uint63 | _ => false end && known_eq fs (rg_hi rb) X)
  || known_eq fs X (VL wzero).

Definition arstage_apply (st : sstate) : option (list sstate) :=
  match ActrA.acall_pre ActrA.ASTACK None st with
  | Some (r, hargs, wl, st1) =>
      match getr st X11, CtrA.sym_offset (s_regs st) (getr st X10), find_op ReadC.TwinB.ReadC.RSTV_ID (s_ops st), find_op (ReadC.TwinB.ReadC.r_zsh C) (s_ops st) with
      | VL rs, Some (kb, X), Some [off; n'], Some [] =>
          match CtrA.win_lookup wl kb, IMap.find kb (s_regs st) with
          | Some (wlen, kd), Some rb =>
              if negb (RangeC.TwinB.RangeC.pat_ok st wl kb kd) then None else
              let n := getr st X12 in
              let fs := s_facts st in
              if weqb rs (wlit (ReadC.TwinB.ReadC.r_stage C)) && Nat.eqb (CtrA.count_op ReadC.TwinB.ReadC.RSTV_ID (s_ops st)) 1%nat
                 && weqb kd CtrLib.K_BLOCK && others_twins wl kb
                 && match rg_cells rb with IMap.Leaf => true | _ => false end
                 && prefix_ok fs rb X && PrimInt63.eqb (rg_lo rb) 0%uint63 && rg_w rb
                 && known_eq fs off X && known_eq fs n' n
                 && known_leu fs X wlen && known_leu fs n (sv_alu ALU_SUB wlen X) && known_ltu fs (VL wzero) n
              then
                let st2 := setr (clobber st1) X10 (getr st X10) in
                let rb' := Region 0%uint63 (CtrB.new_hi fs X n) true (BGBlob 4%uint63 0%uint63) IMap.empty in
                let st3 := set_ops (setregs st2 (IMap.add kb rb' (s_regs st2)))
                                   (set_op ReadC.TwinB.ReadC.RSTV_ID [sv_alu ALU_ADD off n; VL wzero] (s_ops st2)) in
                Some [setpc st3 r]
              else None
          | _, _ => None
          end
      | _, _, _, _ => None
      end
  | None => None
  end.

Definition arstage_c (pc : int) : contract := Contract pc arstage_apply.
End WithCfg.
End RstageC.
End TwinB.
