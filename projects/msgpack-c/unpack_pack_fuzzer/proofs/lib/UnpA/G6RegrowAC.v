(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List Lia.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 Val IMap Mem Instr State Step Plan.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr Require Import Lib DefsA.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import GLib GWin G4 G6A.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require Import Actr.
Import ListNotations.
Import W64 Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.Mem FI St OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step.Step Plan UG GW CtrLib G6A.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module G6RegrowAC.

Definition cells_from (r : region) (L : Z) : bool := IMap.forallb (fun g _ => Z.leb (L / 8) (keyZ g)) (rg_cells r).

Definition sink (st st1 : sstate) (r : int) : sstate := setpc (setr (clobber st1) X10 (getr st X10)) r.

Section WithSrc.
Variable SRCPAT : sstate -> list (int * sv * w64) -> int -> sv -> bool.
Variable isV : bool.

Definition KD : int := if isV then 3%uint63 else 2%uint63.

Definition regrow (st stS : sstate) (wnl : list (int * sv * w64)) (aw : sv) (ws : list (sv * sv * sv)) (ca : list sv) : option (list sstate) :=
  match ca with
  | [root; cb; ce; ccap; vb; ve; vcap; zptr; zfree; c0; slot; tD; restD; rootT; n1; P1; zh] =>
      let fs := s_facts stS in let n0 := s_next stS in let R := s_regs stS in
      let b := if isV then vb else cb in let e := if isV then ve else ce in let cap := if isV then vcap else ccap in
      match b, e, cap with
      | VP kB ob, VP kT oe, VP kB' oc =>
          let L := w2Z oc in let dx := getr st X10 in let n12 := getr st X12 in
          match dst_anchor dx n12 L with
          | Some kN =>
              let l2 := VL (wlit (Uint63.of_Z (2 * L))) in
              let wN := (VP kN wzero, l2, VL (wlit 1%uint63)) in
              let wT := top_win kT 8%uint63 KD in
              if PrimInt63.eqb kB kB' && weqb ob wzero && weqb oe (wlit 8%uint63) && negb (wt oc)
                 && (16 <=? L) && (L mod 8 =? 0) && (L <? two40Z)
                 && negb (PrimInt63.eqb kB 0%uint63) && negb (PrimInt63.eqb kT 0%uint63) && negb (PrimInt63.eqb kN 0%uint63)
                 && negb (PrimInt63.eqb kT kB) && negb (PrimInt63.eqb kN kB) && negb (PrimInt63.eqb kN kT)
                 && Z.ltb (Z.of_nat (length ws)) 4000
                 && sv_eqb (getr st X11) b && len_ok n12 e b L
                 && implied fs (FULe e cap) && implied fs (FULe cap e)
                 && existsb (win3_eqb wN) ws && G4.no_other_at kN wN ws
                 && existsb (win3_eqb wT) ws && only_kind (to_Z KD) (Some wT) ws
                 && PrimInt63.leb 3%uint63 (find_align fs kN) && G4.range_nz fs kN
                 && match IMap.find kB R with None => true | Some _ => false end
                 && G4.kinds_lit ws && other_blocks_ok fs R kN ws && sub_windows_ok R kN wT ws

                 && match IMap.find kN (s_regs st), CtrA.win_lookup wnl kN with
                    | Some ra, Some (wlena, kda) =>
                        is_bgnone (rg_bg ra) && PrimInt63.eqb (rg_lo ra) 0%uint63 && rg_w ra && sv_eqb (rg_hi ra) l2 && cells_from ra L
                        && sv_eqb wlena l2 && weqb kda (wlit 1%uint63) && ActrA.twin_pat_ok st wnl kN
                    | _, _ => false
                    end
                 && SRCPAT st wnl kB (VL oc)
              then
              match IMap.find kN R, IMap.find kT R with
              | Some rN, Some rT =>
                  if PrimInt63.eqb (rg_lo rN) 0%uint63 && sv_eqb (rg_hi rN) l2 && rg_w rN
                     && match rg_bg rN with BGNone | BGUnk => true | _ => false end
                     && PrimInt63.eqb (rg_lo rT) 0%uint63 && sv_eqb (rg_hi rT) (VL (wlit 8%uint63)) && rg_w rT
                  then
                  match elem_cells isV rT 0%uint63, elem_cells isV rN (Uint63.of_Z (L / 8)) with
                  | Some topc, Some newc =>
                      let nT := n0 in
                      let st2 := repl_regs kept_r5 dx (VP kN wzero) (setr stS X10 (VP kN wzero)) in
                      let rT' := region16 topc newc in
                      let rB' := empty_region L in
                      let ws' := List.filter (fun w => negb (win3_eqb w wN || win3_eqb w wT)) ws
                                 ++ [(VP kB wzero, VL oc, VL (wlit 1%uint63)); top_win nT 16%uint63 KD] in
                      let b' := VP kN wzero in let e' := VP nT (wlit 8%uint63) in let cap' := VP kN (wlit (Uint63.of_Z (2 * L))) in
                      let ca' := if isV then [root; cb; ce; ccap; b'; e'; cap'; zptr; zfree; c0; slot; tD; restD; rootT; n1; P1; zh]
                                 else [root; b'; e'; cap'; vb; ve; vcap; zptr; zfree; c0; slot; tD; restD; rootT; n1; P1; zh] in
                      let nf := [FEq (VP nT wzero) (VP kN (wlit (Uint63.of_Z (L - 8)))); FULt b' e'; FULe e' cap';
                                 FEq (VAlu ALU_SUB e' b') (VAlu ALU_SUB e b)]
                                ++ G4.anchor_facts fs kN (L - 8) (L - 8) nT
                                ++ (if PrimInt63.leb 3%uint63 (find_align fs kN) then [FAlign nT 3%uint63] else []) in
                      Some [surg st2 [kN; kT] [(nT, rT'); (kB, rB')] (mk_args 1%uint63 aw ws' ca') nf (PrimInt63.add n0 1%uint63)]
                  | _, _ => None
                  end
                  else None
              | _, _ => None
              end
              else None
          | None => None
          end
      | _, _, _ => None
      end
  | _ => None
  end.

Definition g6r_apply (st : sstate) : option (list sstate) :=
  match the_op st, ActrA.acall_pre ActrA.ASTACK None st with
  | Some (md, aw, ws, ca), Some (r, hargs, wnl, st1) =>
      let stS := sink st st1 r in
      if PrimInt63.eqb md 1%uint63 && fresh_ok stS then regrow st stS wnl aw ws ca else None
  | _, _ => None
  end.

Definition g6r_contract (pc : int) : contract := Contract pc g6r_apply.
End WithSrc.
End G6RegrowAC.

Module TwinB.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Sem.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64 OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.IMap OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Instr OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.State OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Plan.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.Lib OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.DefsA.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.GLib OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.GWin OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.G4 OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.G6A.
Import Actr.TwinB.

Import ListNotations.
Import W64 Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.Mem FI St OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step.Step Plan UG GW CtrLib G6A.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module G6RegrowAC.

Definition cells_from (r : region) (L : Z) : bool := IMap.forallb (fun g _ => Z.leb (L / 8) (keyZ g)) (rg_cells r).

Definition sink (st st1 : sstate) (r : int) : sstate := setpc (setr (clobber st1) X10 (getr st X10)) r.

Section WithSrc.
Variable SRCPAT : sstate -> list (int * sv * w64) -> int -> sv -> bool.
Variable isV : bool.

Definition KD : int := if isV then 3%uint63 else 2%uint63.

Definition regrow (st stS : sstate) (wnl : list (int * sv * w64)) (aw : sv) (ws : list (sv * sv * sv)) (ca : list sv) : option (list sstate) :=
  match ca with
  | [root; cb; ce; ccap; vb; ve; vcap; zptr; zfree; c0; slot; tD; restD; rootT; n1; P1; zh] =>
      let fs := s_facts stS in let n0 := s_next stS in let R := s_regs stS in
      let b := if isV then vb else cb in let e := if isV then ve else ce in let cap := if isV then vcap else ccap in
      match b, e, cap with
      | VP kB ob, VP kT oe, VP kB' oc =>
          let L := w2Z oc in let dx := getr st X10 in let n12 := getr st X12 in
          match dst_anchor dx n12 L with
          | Some kN =>
              let l2 := VL (wlit (Uint63.of_Z (2 * L))) in
              let wN := (VP kN wzero, l2, VL (wlit 1%uint63)) in
              let wT := top_win kT 8%uint63 KD in
              if PrimInt63.eqb kB kB' && weqb ob wzero && weqb oe (wlit 8%uint63) && negb (wt oc)
                 && (16 <=? L) && (L mod 8 =? 0) && (L <? two40Z)
                 && negb (PrimInt63.eqb kB 0%uint63) && negb (PrimInt63.eqb kT 0%uint63) && negb (PrimInt63.eqb kN 0%uint63)
                 && negb (PrimInt63.eqb kT kB) && negb (PrimInt63.eqb kN kB) && negb (PrimInt63.eqb kN kT)
                 && Z.ltb (Z.of_nat (length ws)) 4000
                 && sv_eqb (getr st X11) b && len_ok n12 e b L
                 && implied fs (FULe e cap) && implied fs (FULe cap e)
                 && existsb (win3_eqb wN) ws && G4.no_other_at kN wN ws
                 && existsb (win3_eqb wT) ws && only_kind (to_Z KD) (Some wT) ws
                 && PrimInt63.leb 3%uint63 (find_align fs kN) && G4.range_nz fs kN
                 && match IMap.find kB R with None => true | Some _ => false end
                 && G4.kinds_lit ws && other_blocks_ok fs R kN ws && sub_windows_ok R kN wT ws

                 && match IMap.find kN (s_regs st), CtrA.win_lookup wnl kN with
                    | Some ra, Some (wlena, kda) =>
                        is_bgnone (rg_bg ra) && PrimInt63.eqb (rg_lo ra) 0%uint63 && rg_w ra && sv_eqb (rg_hi ra) l2 && cells_from ra L
                        && sv_eqb wlena l2 && weqb kda (wlit 1%uint63) && ActrA.twin_pat_ok st wnl kN
                    | _, _ => false
                    end
                 && SRCPAT st wnl kB (VL oc)
              then
              match IMap.find kN R, IMap.find kT R with
              | Some rN, Some rT =>
                  if PrimInt63.eqb (rg_lo rN) 0%uint63 && sv_eqb (rg_hi rN) l2 && rg_w rN
                     && match rg_bg rN with BGNone | BGUnk => true | _ => false end
                     && PrimInt63.eqb (rg_lo rT) 0%uint63 && sv_eqb (rg_hi rT) (VL (wlit 8%uint63)) && rg_w rT
                  then
                  match elem_cells isV rT 0%uint63, elem_cells isV rN (Uint63.of_Z (L / 8)) with
                  | Some topc, Some newc =>
                      let nT := n0 in
                      let st2 := repl_regs kept_r5 dx (VP kN wzero) (setr stS X10 (VP kN wzero)) in
                      let rT' := region16 topc newc in
                      let rB' := empty_region L in
                      let ws' := List.filter (fun w => negb (win3_eqb w wN || win3_eqb w wT)) ws
                                 ++ [(VP kB wzero, VL oc, VL (wlit 1%uint63)); top_win nT 16%uint63 KD] in
                      let b' := VP kN wzero in let e' := VP nT (wlit 8%uint63) in let cap' := VP kN (wlit (Uint63.of_Z (2 * L))) in
                      let ca' := if isV then [root; cb; ce; ccap; b'; e'; cap'; zptr; zfree; c0; slot; tD; restD; rootT; n1; P1; zh]
                                 else [root; b'; e'; cap'; vb; ve; vcap; zptr; zfree; c0; slot; tD; restD; rootT; n1; P1; zh] in
                      let nf := [FEq (VP nT wzero) (VP kN (wlit (Uint63.of_Z (L - 8)))); FULt b' e'; FULe e' cap';
                                 FEq (VAlu ALU_SUB e' b') (VAlu ALU_SUB e b)]
                                ++ G4.anchor_facts fs kN (L - 8) (L - 8) nT
                                ++ (if PrimInt63.leb 3%uint63 (find_align fs kN) then [FAlign nT 3%uint63] else []) in
                      Some [surg st2 [kN; kT] [(nT, rT'); (kB, rB')] (mk_args 1%uint63 aw ws' ca') nf (PrimInt63.add n0 1%uint63)]
                  | _, _ => None
                  end
                  else None
              | _, _ => None
              end
              else None
          | None => None
          end
      | _, _, _ => None
      end
  | _ => None
  end.

Definition g6r_apply (st : sstate) : option (list sstate) :=
  match the_op st, ActrA.acall_pre ActrA.ASTACK None st with
  | Some (md, aw, ws, ca), Some (r, hargs, wnl, st1) =>
      let stS := sink st st1 r in
      if PrimInt63.eqb md 1%uint63 && fresh_ok stS then regrow st stS wnl aw ws ca else None
  | _, _ => None
  end.

Definition g6r_contract (pc : int) : contract := Contract pc g6r_apply.
End WithSrc.
End G6RegrowAC.
End TwinB.
