(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 Val IMap Mem Instr State Step Plan.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val Mem FI St Step Plan.
Open Scope Z_scope.
Unset Lia Cache.

Module LdPart.
Section WithSegs.
Variable segs : list Segment.

Definition load_at (pc : int) : option (msize * bool * r5 * r5 * w64) :=
  match fetch_word segs (Z_to_bv 64 (to_Z pc)) with
  | Some w =>
      if is_ecall w then None else
      match decode_any w with
      | Some (i, z) =>
          if Z.eqb z 4 then
            match of_instr i with Some (ILoad sz sx rd rs1 off) => Some (sz, sx, rd, rs1, off) | _ => None end
          else None
      | None => None
      end
  | None => None
  end.

Definition cell_apart (i w : int) (c : cell) : bool :=
  PrimInt63.leb (PrimInt63.add (c_idx c) (c_w c)) i || PrimInt63.leb (PrimInt63.add i w) (c_idx c).
Definition cell_inside (i w : int) (c : cell) : bool :=
  PrimInt63.leb i (c_idx c) && PrimInt63.leb (PrimInt63.add (c_idx c) (c_w c)) (PrimInt63.add i w).
Definition cells_fit (i w : int) (s : slot) : bool := forallb (fun c => cell_apart i w c || cell_inside i w c) s.

Definition cell_fact (n i : int) (c : cell) : fact :=
  FEq (sv_ext false (PrimInt63.sub (c_idx c) i) (c_w c) (VP n wzero)) (sv_ext false 0%uint63 (c_w c) (c_v c)).

Definition wmax (w : int) : w64 := wlit (PrimInt63.sub (PrimInt63.lsl 1%uint63 (PrimInt63.mul 8%uint63 w)) 1%uint63).

Definition ldpart_apply (st : sstate) : option (list sstate) :=
  match load_at (s_pc st) with
  | Some (sz, sx, rd, rs, off) =>
      let w := msize_bytes sz in
      match addr_of (sv_alu ALU_ADD (getr st rs) (VL off)) with
      | Some (k, o) =>
          if PrimInt63.eqb k 0%uint63 then None else
          match IMap.find k (s_regs st), okey o with
          | Some r, Some key =>
              let n := s_next st in
              let g := granule key in let i := gidx key in
              let old := match IMap.find g (rg_cells r) with Some gr => g_cells gr | None => [] end in
              if is_bgnone (rg_bg r) && in_granule key w
                 && can_read segs (s_facts st) (s_priv st) k r key w
                 && cells_fit i w old
                 && negb (r5_eqb rd X0) && st_vars_below n st
                 && PrimInt63.ltb 0%uint63 n && PrimInt63.ltb n (PrimInt63.sub bit62i 8%uint63) && PrimInt63.ltb (s_pc st) bit62i
              then
                let v := VP n wzero in
                let dropped := List.filter (fun c => negb (cell_apart i w c)) old in
                let nf := (if negb sx && PrimInt63.ltb w 8%uint63 then [FRange n wzero (wmax w)] else [])
                          ++ map (cell_fact n i) dropped in
                let st1 := SS (s_pc st) (s_rf st) (s_ff st) (s_resv st) (IMap.add k (region_store1 r key w v) (s_regs st))
                              (nf ++ s_facts st) (s_ops st) (s_priv st) (PrimInt63.add n 1%uint63) in
                Some [setpc (setr st1 rd v) (PrimInt63.add (s_pc st) 4%uint63)]
              else None
          | _, _ => None
          end
      | None => None
      end
  | None => None
  end.

Definition ldpart_c (pc : int) : contract := Contract pc ldpart_apply.

End WithSegs.
End LdPart.
