(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 Val IMap Mem Instr State Step Plan.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr Require Import Lib DefsA LdPart.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import GLib.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val Mem FI St Step Plan CtrLib UG.
Open Scope Z_scope.
Unset Lia Cache.

Module PkBody.
Section WithSegs.
Variable segs : list Segment.
Variable ERRNO : int.

Definition T_STRw : w64 := wlit 5%uint63.
Definition T_BINw : w64 := wlit 6%uint63.
Definition T_EXTw : w64 := wlit 9%uint63.

Definition body_src (fs : list fact) (eb rootT n1 P1 cf fT fN fP : sv) : option (sv * sv * sv) :=
  if sv_eqb eb (VL wzero) then Some (rootT, n1, P1)
  else if dec_false (decide_eq0 fs cf) then Some (fT, fN, fP) else None.

Definition unsextw (fs : list fact) (v : sv) : sv :=
  match v with
  | VAluw ALU_ADD x (VL z) => if weqb z wzero && wltu (snd (sv_bounds fs x)) (wlit 2147483648%uint63) then x else v
  | _ => v
  end.

Definition body_src_ok (st : sstate) (n : sv) : bool :=
  match the_op st with
  | Some (md, aw, ws, ca) =>
      PrimInt63.eqb md 3%uint63 &&
      match ca with
      | [root; rootT; n1; P1; zh; c0; eb; ee; ecap; tptr; trest; tmap; tkey; cf; fT; fN; fP] =>
          match body_src (s_facts st) eb rootT n1 P1 cf fT fN fP with
          | Some (VL t, fN, fP) =>
              let fs := s_facts st in
              let fN' := unsextw fs (narrow_f fs fN) in

              let src := if weqb t T_EXTw then sv_alu ALU_ADD fP (VL wone) else fP in
              (weqb t T_STRw || weqb t T_BINw || weqb t T_EXTw)
              && dec_true (decide_eq fs (getr st X11) src) && dec_true (decide_eq fs n fN')
          | _ => false
          end
      | _ => false
      end
  | None => false
  end.

Definition based_src_ok (st : sstate) (kS : int) (n : sv) : bool :=
  match CtrA.sym_offset (s_regs st) (getr st X11) with
  | Some (kd, OFF) =>
      match IMap.find kd (s_regs st) with
      | Some rd =>
          let fs := s_facts st in
          negb (PrimInt63.eqb kd 0%uint63) && negb (PrimInt63.eqb kd kS) && PrimInt63.eqb (rg_lo rd) 0%uint63
          && known_leu fs OFF (rg_hi rd) && known_leu fs n (sv_alu ALU_SUB (rg_hi rd) OFF)
      | None => false
      end
  | None => false
  end.

Definition STK_MAX : int := 4096%uint63.
Definition stack_src_ok (st : sstate) (n : sv) : bool :=
  match getr st X11, n, getr st X2, IMap.find CtrA.STACK_ID (s_regs st) with
  | VP k1 o, VL nw, VP k2 osp, Some r1 =>
      PrimInt63.eqb k1 CtrA.STACK_ID && PrimInt63.eqb k2 CtrA.STACK_ID && negb (wt nw) && PrimInt63.leb (wl nw) STK_MAX &&
      match okey o, okey (wadd o nw), okey osp, rg_hi r1 with
      | Some i, Some ie, Some ksp, VL h =>
          match okey h with
          | Some kh => kleb (rg_lo r1) i && kleb ksp i && kleb i ie && kleb ie kh
          | None => false
          end
      | _, _, _, _ => false
      end
  | _, _, _, _ => false
  end.

Definition is_block_bg (b : bg) : bool := match b with BGNone | BGUnk => true | _ => false end.

Definition G_MAX : int := 576460752303423488%uint63.
Definition cell_apart (fs : list fact) (OFF n : sv) (g : int) (c : cell) : bool :=
  PrimInt63.ltb g G_MAX &&
  (let o := PrimInt63.add (PrimInt63.lsl g 3%uint63) (c_idx c) in
   let e := PrimInt63.add o (c_w c) in
   known_leu fs (VL (wlit e)) OFF || known_leu fs (sv_alu ALU_ADD OFF n) (VL (wlit o))).
Definition cells_apart (fs : list fact) (OFF n : sv) (cs : IMap.t gran) : bool :=
  IMap.forallb (fun g gr => List.forallb (cell_apart fs OFF n g) (g_cells gr)) cs.
Definition dst_region (fs : list fact) (OFF n : sv) (rS : region) : region :=
  Region (rg_lo rS) (rg_hi rS) (rg_w rS) BGNone (if cells_apart fs OFF n (rg_cells rS) then rg_cells rS else IMap.empty).

Definition pkmemcpy_apply (st : sstate) : option (list sstate) :=
  match call_pre st, CtrA.sym_offset (s_regs st) (getr st X10) with
  | Some r, Some (kS, OFF) =>
      if PrimInt63.eqb kS 0%uint63 || PrimInt63.eqb kS CtrA.STACK_ID then None else
      match IMap.find kS (s_regs st) with
      | Some rS =>
          let fs := s_facts st in
          let n := getr st X12 in
          if is_block_bg (rg_bg rS) && PrimInt63.eqb (rg_lo rS) 0%uint63 && rg_w rS
             && known_leu fs OFF (rg_hi rS) && known_leu fs n (sv_alu ALU_SUB (rg_hi rS) OFF)
             && (stack_src_ok st n || based_src_ok st kS n || body_src_ok st n)
          then
            let st1 := setregs st (IMap.add kS (dst_region fs OFF n rS) (s_regs st)) in
            match havoc_errno segs ERRNO (clobber st1) with
            | Some st2 => Some [setpc st2 r]
            | None => None
            end
          else None
      | None => None
      end
  | _, _ => None
  end.
Definition pkmemcpy_c (pc : int) : contract := Contract pc pkmemcpy_apply.

Definition pkextb_apply (st : sstate) : option (list sstate) :=
  match LdPart.load_at segs (s_pc st), the_op st with
  | Some (SZ1, true, rd, rs, off), Some (md, aw, ws, ca) =>
      if negb (PrimInt63.eqb md 3%uint63) then None else
      match ca with
      | [root; rootT; n1; P1; zh; c0; eb; ee; ecap; tptr; trest; tmap; tkey; cf; fT; fN; fP] =>
          match body_src (s_facts st) eb rootT n1 P1 cf fT fN fP with
          | Some (VL t, fN, fP) =>
              let fs := s_facts st in
              let n := s_next st in
              if weqb t T_EXTw && dec_true (decide_eq fs (sv_alu ALU_ADD (getr st rs) (VL off)) fP)
                 && negb (r5_eqb rd X0) && st_vars_below n st
                 && PrimInt63.ltb 0%uint63 n && PrimInt63.ltb n (PrimInt63.sub bit62i 8%uint63) && PrimInt63.ltb (s_pc st) bit62i
              then
                let st1 := SS (s_pc st) (s_rf st) (s_ff st) (s_resv st) (s_regs st) (FRange n wzero (wlit 255%uint63) :: fs)
                              (s_ops st) (s_priv st) (PrimInt63.add n 1%uint63) in
                Some [setpc (setr st1 rd (VExt true 0%uint63 1%uint63 (VP n wzero))) (PrimInt63.add (s_pc st) 4%uint63)]
              else None
          | _ => None
          end
      | _ => None
      end
  | _, _ => None
  end.
Definition pkextb_c (pc : int) : contract := Contract pc pkextb_apply.

End WithSegs.
End PkBody.
