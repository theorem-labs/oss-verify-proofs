(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List Lia.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 Val IMap Mem Instr State Step Plan.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr Require Import Lib DefsA.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import GLib GWin PkStack PkRegrow.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require Import Actr.
Import ListNotations.
Import W64 Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.Mem FI St OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step.Step Plan UG GW CtrLib PkRegrow.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PkRegrowAC.

Definition cells_from (r : region) (L : Z) : bool := IMap.forallb (fun g _ => Z.leb (L / 8) (keyZ g)) (rg_cells r).

Definition sink (st st1 : sstate) (r : int) : sstate := setpc (setr (clobber st1) X10 (getr st X10)) r.

Section WithSrc.
Variable SRCPAT : sstate -> list (int * sv * w64) -> int -> sv -> bool.

Definition regrow0 (st stS : sstate) (aw : sv) (ws : list (sv * sv * sv)) (c : PkStack.pkca) : option (list sstate) :=
  let fs := s_facts stS in let n0 := s_next stS in let R := s_regs stS in
  let dx := getr st X10 in let n12 := getr st X12 in
  match dst_anchor dx n12 0 with
  | Some kN =>
      let wN := (VP kN wzero, VL (wlit 24%uint63), VL (wlit 1%uint63)) in
      if sv_eqb (PkStack.c_ee c) (VL wzero) && sv_eqb (PkStack.c_ecap c) (VL wzero)
         && negb (PrimInt63.eqb kN 0%uint63) && negb (PrimInt63.eqb kN 1%uint63)
         && Z.ltb (Z.of_nat (length ws)) 4000
         && sv_eqb (getr st X11) (VL wzero) && len_ok n12 (VL wzero) (VL wzero) 0
         && existsb (win3_eqb wN) ws && no_other_at kN wN ws
         && PkStack.only_kind 6 None ws
         && PrimInt63.leb 3%uint63 (find_align fs kN) && range_nz fs kN
         && kinds_lit ws && other_blocks_ok fs R kN ws && sub_windows_ok R kN wN ws
      then
        match IMap.find kN R with
        | Some rN =>
            if PrimInt63.eqb (rg_lo rN) 0%uint63 && sv_eqb (rg_hi rN) (VL (wlit 24%uint63)) && rg_w rN
               && match rg_bg rN with BGNone | BGUnk => true | _ => false end
            then
              let st2 := repl_regs kept_r5 dx (VP kN wzero) (setr stS X10 (VP kN wzero)) in
              let ws' := List.map (fun w => if win3_eqb w wN then top_win kN 24%uint63 ETOPk else w) ws in
              let c' := PkStack.PC (PkStack.c_root c) (PkStack.c_rootT c) (PkStack.c_n1 c) (PkStack.c_P1 c) (PkStack.c_zh c) (PkStack.c_c0 c)
                          (VP kN wzero) (VP kN wzero) (VP kN (wlit 24%uint63))
                          (PkStack.c_tptr c) (PkStack.c_trest c) (PkStack.c_tmap c) (PkStack.c_tkey c)
                          (PkStack.c_cf c) (PkStack.c_fT c) (PkStack.c_fN c) (PkStack.c_fP c) in
              Some [surg st2 [] [] (mk_args 3%uint63 aw ws' (PkStack.unparse_ca c')) [] n0]
            else None
        | None => None
        end
      else None
  | None => None
  end.

Definition regrow1 (st stS : sstate) (wnl : list (int * sv * w64)) (aw : sv) (ws : list (sv * sv * sv)) (c : PkStack.pkca) (kB kT : int) (oc : w64)
    : option (list sstate) :=
  let fs := s_facts stS in let n0 := s_next stS in let R := s_regs stS in
  let L := w2Z oc in let dx := getr st X10 in let n12 := getr st X12 in
  match dst_anchor dx n12 L with
  | Some kN =>
      let l2 := VL (wlit (Uint63.of_Z (2 * L))) in
      let wN := (VP kN wzero, l2, VL (wlit 1%uint63)) in
      let wT := top_win kT 24%uint63 ETOPk in
      if negb (wt oc) && (24 <=? L) && (L mod 8 =? 0) && (L <? two40Z)
         && negb (PrimInt63.eqb kB 0%uint63) && negb (PrimInt63.eqb kT 0%uint63) && negb (PrimInt63.eqb kN 0%uint63) && negb (PrimInt63.eqb kN 1%uint63)
         && negb (PrimInt63.eqb kN kB) && negb (PrimInt63.eqb kN kT)
         && (PrimInt63.eqb kT kB || match IMap.find kB R with None => true | Some _ => false end)
         && Z.ltb (Z.of_nat (length ws)) 4000
         && sv_eqb (getr st X11) (VP kB wzero) && len_ok n12 (VP kT (wlit 24%uint63)) (VP kB wzero) L
         && implied fs (FULe (VP kT (wlit 24%uint63)) (VP kB oc)) && implied fs (FULe (VP kB oc) (VP kT (wlit 24%uint63)))
         && existsb (win3_eqb wN) ws && no_other_at kN wN ws
         && existsb (win3_eqb wT) ws && PkStack.only_kind 6 (Some wT) ws
         && PrimInt63.leb 3%uint63 (find_align fs kN) && range_nz fs kN
         && kinds_lit ws && other_blocks_ok fs R kN ws && sub_windows_ok R kN wT ws

         && match IMap.find kN (s_regs st), CtrA.win_lookup wnl kN with
            | Some ra, Some (wlena, kda) =>
                is_bgnone (rg_bg ra) && PrimInt63.eqb (rg_lo ra) 0%uint63 && rg_w ra && sv_eqb (rg_hi ra) l2 && cells_from ra L
                && sv_eqb wlena l2 && weqb kda (wlit 1%uint63)
                && ActrA.twin_pat_ok st wnl kN
            | _, _ => false
            end
         && SRCPAT st wnl kB (VL oc)
      then
        match IMap.find kN R, IMap.find kT R with
        | Some rN, Some rT =>
            if PrimInt63.eqb (rg_lo rN) 0%uint63 && sv_eqb (rg_hi rN) l2 && rg_w rN
               && match rg_bg rN with BGNone | BGUnk => true | _ => false end
               && PrimInt63.eqb (rg_lo rT) 0%uint63 && sv_eqb (rg_hi rT) (VL (wlit 24%uint63)) && rg_w rT
            then
              let g := Uint63.of_Z (L / 8) in
              match gcells rT 0%uint63, gcells rT 1%uint63, gcells rT 2%uint63,
                    gcells rN g, gcells rN (PrimInt63.add g 1%uint63), gcells rN (PrimInt63.add g 2%uint63) with
              | Some t0, Some t1, Some t2, Some e0, Some e1, Some e2 =>
                  let nT := n0 in
                  let st2 := repl_regs kept_r5 dx (VP kN wzero) (setr stS X10 (VP kN wzero)) in
                  let rT' := region48 t0 t1 t2 e0 e1 e2 in
                  let rB' := empty_region L in
                  let wB' := (VP kB wzero, VL oc, VL (wlit 1%uint63)) in
                  let wNT := top_win nT 48%uint63 ETOPk in
                  let ws' := List.filter (fun w => negb (win3_eqb w wN || win3_eqb w wT)) ws ++ [wB'; wNT] in
                  let b' := VP kN wzero in let e' := VP nT (wlit 24%uint63) in let cap' := VP kN (wlit (Uint63.of_Z (2 * L))) in
                  let c' := PkStack.PC (PkStack.c_root c) (PkStack.c_rootT c) (PkStack.c_n1 c) (PkStack.c_P1 c) (PkStack.c_zh c) (PkStack.c_c0 c)
                              b' e' cap'
                              (PkStack.c_tptr c) (PkStack.c_trest c) (PkStack.c_tmap c) (PkStack.c_tkey c)
                              (PkStack.c_cf c) (PkStack.c_fT c) (PkStack.c_fN c) (PkStack.c_fP c) in
                  let nf := [FEq (VP nT wzero) (VP kN (wlit (Uint63.of_Z (L - 24)))); FULe b' (VP nT wzero); FULe e' cap']
                            ++ top_facts fs b' nT
                            ++ anchor_facts fs kN (L - 24) (L - 24) nT in
                  Some [surg st2 [kN; kT] [(nT, rT'); (kB, rB')] (mk_args 3%uint63 aw ws' (PkStack.unparse_ca c')) nf (PrimInt63.add n0 1%uint63)]
              | _, _, _, _, _, _ => None
              end
            else None
        | _, _ => None
        end
      else None
  | None => None
  end.

Definition pkregrow_apply (st : sstate) : option (list sstate) :=
  match the_op st, ActrA.acall_pre ActrA.ASTACK None st with
  | Some (md, aw, ws, ca), Some (r, hargs, wnl, st1) =>
      let stS := sink st st1 r in
      if PrimInt63.eqb md 3%uint63 && fresh_ok stS then
      match PkStack.parse_ca ca with
      | Some c =>
          match PkStack.c_eb c, PkStack.c_ee c, PkStack.c_ecap c with
          | VL b0, _, _ => if weqb b0 wzero then regrow0 st stS aw ws c else None
          | VP kB ob, VP kT oe, VP kB' oc =>
              if PrimInt63.eqb kB kB' && weqb ob wzero && weqb oe (wlit 24%uint63) then regrow1 st stS wnl aw ws c kB kT oc else None
          | _, _, _ => None
          end
      | None => None
      end
      else None
  | _, _ => None
  end.

Definition pkregrow_contract (pc : int) : contract := Contract pc pkregrow_apply.
End WithSrc.
End PkRegrowAC.

Module TwinB.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Sem.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64 OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.IMap OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Instr OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.State OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Plan.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.Lib OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.DefsA.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.GLib OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.GWin OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.PkStack OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.PkRegrow.
Import Actr.TwinB.

Import ListNotations.
Import W64 Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.Mem FI St OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step.Step Plan UG GW CtrLib PkRegrow.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PkRegrowAC.

Definition cells_from (r : region) (L : Z) : bool := IMap.forallb (fun g _ => Z.leb (L / 8) (keyZ g)) (rg_cells r).

Definition sink (st st1 : sstate) (r : int) : sstate := setpc (setr (clobber st1) X10 (getr st X10)) r.

Section WithSrc.
Variable SRCPAT : sstate -> list (int * sv * w64) -> int -> sv -> bool.

Definition regrow0 (st stS : sstate) (aw : sv) (ws : list (sv * sv * sv)) (c : PkStack.pkca) : option (list sstate) :=
  let fs := s_facts stS in let n0 := s_next stS in let R := s_regs stS in
  let dx := getr st X10 in let n12 := getr st X12 in
  match dst_anchor dx n12 0 with
  | Some kN =>
      let wN := (VP kN wzero, VL (wlit 24%uint63), VL (wlit 1%uint63)) in
      if sv_eqb (PkStack.c_ee c) (VL wzero) && sv_eqb (PkStack.c_ecap c) (VL wzero)
         && negb (PrimInt63.eqb kN 0%uint63) && negb (PrimInt63.eqb kN 1%uint63)
         && Z.ltb (Z.of_nat (length ws)) 4000
         && sv_eqb (getr st X11) (VL wzero) && len_ok n12 (VL wzero) (VL wzero) 0
         && existsb (win3_eqb wN) ws && no_other_at kN wN ws
         && PkStack.only_kind 6 None ws
         && PrimInt63.leb 3%uint63 (find_align fs kN) && range_nz fs kN
         && kinds_lit ws && other_blocks_ok fs R kN ws && sub_windows_ok R kN wN ws
      then
        match IMap.find kN R with
        | Some rN =>
            if PrimInt63.eqb (rg_lo rN) 0%uint63 && sv_eqb (rg_hi rN) (VL (wlit 24%uint63)) && rg_w rN
               && match rg_bg rN with BGNone | BGUnk => true | _ => false end
            then
              let st2 := repl_regs kept_r5 dx (VP kN wzero) (setr stS X10 (VP kN wzero)) in
              let ws' := List.map (fun w => if win3_eqb w wN then top_win kN 24%uint63 ETOPk else w) ws in
              let c' := PkStack.PC (PkStack.c_root c) (PkStack.c_rootT c) (PkStack.c_n1 c) (PkStack.c_P1 c) (PkStack.c_zh c) (PkStack.c_c0 c)
                          (VP kN wzero) (VP kN wzero) (VP kN (wlit 24%uint63))
                          (PkStack.c_tptr c) (PkStack.c_trest c) (PkStack.c_tmap c) (PkStack.c_tkey c)
                          (PkStack.c_cf c) (PkStack.c_fT c) (PkStack.c_fN c) (PkStack.c_fP c) in
              Some [surg st2 [] [] (mk_args 3%uint63 aw ws' (PkStack.unparse_ca c')) [] n0]
            else None
        | None => None
        end
      else None
  | None => None
  end.

Definition regrow1 (st stS : sstate) (wnl : list (int * sv * w64)) (aw : sv) (ws : list (sv * sv * sv)) (c : PkStack.pkca) (kB kT : int) (oc : w64)
    : option (list sstate) :=
  let fs := s_facts stS in let n0 := s_next stS in let R := s_regs stS in
  let L := w2Z oc in let dx := getr st X10 in let n12 := getr st X12 in
  match dst_anchor dx n12 L with
  | Some kN =>
      let l2 := VL (wlit (Uint63.of_Z (2 * L))) in
      let wN := (VP kN wzero, l2, VL (wlit 1%uint63)) in
      let wT := top_win kT 24%uint63 ETOPk in
      if negb (wt oc) && (24 <=? L) && (L mod 8 =? 0) && (L <? two40Z)
         && negb (PrimInt63.eqb kB 0%uint63) && negb (PrimInt63.eqb kT 0%uint63) && negb (PrimInt63.eqb kN 0%uint63) && negb (PrimInt63.eqb kN 1%uint63)
         && negb (PrimInt63.eqb kN kB) && negb (PrimInt63.eqb kN kT)
         && (PrimInt63.eqb kT kB || match IMap.find kB R with None => true | Some _ => false end)
         && Z.ltb (Z.of_nat (length ws)) 4000
         && sv_eqb (getr st X11) (VP kB wzero) && len_ok n12 (VP kT (wlit 24%uint63)) (VP kB wzero) L
         && implied fs (FULe (VP kT (wlit 24%uint63)) (VP kB oc)) && implied fs (FULe (VP kB oc) (VP kT (wlit 24%uint63)))
         && existsb (win3_eqb wN) ws && no_other_at kN wN ws
         && existsb (win3_eqb wT) ws && PkStack.only_kind 6 (Some wT) ws
         && PrimInt63.leb 3%uint63 (find_align fs kN) && range_nz fs kN
         && kinds_lit ws && other_blocks_ok fs R kN ws && sub_windows_ok R kN wT ws

         && match IMap.find kN (s_regs st), CtrA.win_lookup wnl kN with
            | Some ra, Some (wlena, kda) =>
                is_bgnone (rg_bg ra) && PrimInt63.eqb (rg_lo ra) 0%uint63 && rg_w ra && sv_eqb (rg_hi ra) l2 && cells_from ra L
                && sv_eqb wlena l2 && weqb kda (wlit 1%uint63)
                && ActrA.twin_pat_ok st wnl kN
            | _, _ => false
            end
         && SRCPAT st wnl kB (VL oc)
      then
        match IMap.find kN R, IMap.find kT R with
        | Some rN, Some rT =>
            if PrimInt63.eqb (rg_lo rN) 0%uint63 && sv_eqb (rg_hi rN) l2 && rg_w rN
               && match rg_bg rN with BGNone | BGUnk => true | _ => false end
               && PrimInt63.eqb (rg_lo rT) 0%uint63 && sv_eqb (rg_hi rT) (VL (wlit 24%uint63)) && rg_w rT
            then
              let g := Uint63.of_Z (L / 8) in
              match gcells rT 0%uint63, gcells rT 1%uint63, gcells rT 2%uint63,
                    gcells rN g, gcells rN (PrimInt63.add g 1%uint63), gcells rN (PrimInt63.add g 2%uint63) with
              | Some t0, Some t1, Some t2, Some e0, Some e1, Some e2 =>
                  let nT := n0 in
                  let st2 := repl_regs kept_r5 dx (VP kN wzero) (setr stS X10 (VP kN wzero)) in
                  let rT' := region48 t0 t1 t2 e0 e1 e2 in
                  let rB' := empty_region L in
                  let wB' := (VP kB wzero, VL oc, VL (wlit 1%uint63)) in
                  let wNT := top_win nT 48%uint63 ETOPk in
                  let ws' := List.filter (fun w => negb (win3_eqb w wN || win3_eqb w wT)) ws ++ [wB'; wNT] in
                  let b' := VP kN wzero in let e' := VP nT (wlit 24%uint63) in let cap' := VP kN (wlit (Uint63.of_Z (2 * L))) in
                  let c' := PkStack.PC (PkStack.c_root c) (PkStack.c_rootT c) (PkStack.c_n1 c) (PkStack.c_P1 c) (PkStack.c_zh c) (PkStack.c_c0 c)
                              b' e' cap'
                              (PkStack.c_tptr c) (PkStack.c_trest c) (PkStack.c_tmap c) (PkStack.c_tkey c)
                              (PkStack.c_cf c) (PkStack.c_fT c) (PkStack.c_fN c) (PkStack.c_fP c) in
                  let nf := [FEq (VP nT wzero) (VP kN (wlit (Uint63.of_Z (L - 24)))); FULe b' (VP nT wzero); FULe e' cap']
                            ++ top_facts fs b' nT
                            ++ anchor_facts fs kN (L - 24) (L - 24) nT in
                  Some [surg st2 [kN; kT] [(nT, rT'); (kB, rB')] (mk_args 3%uint63 aw ws' (PkStack.unparse_ca c')) nf (PrimInt63.add n0 1%uint63)]
              | _, _, _, _, _, _ => None
              end
            else None
        | _, _ => None
        end
      else None
  | None => None
  end.

Definition pkregrow_apply (st : sstate) : option (list sstate) :=
  match the_op st, ActrA.acall_pre ActrA.ASTACK None st with
  | Some (md, aw, ws, ca), Some (r, hargs, wnl, st1) =>
      let stS := sink st st1 r in
      if PrimInt63.eqb md 3%uint63 && fresh_ok stS then
      match PkStack.parse_ca ca with
      | Some c =>
          match PkStack.c_eb c, PkStack.c_ee c, PkStack.c_ecap c with
          | VL b0, _, _ => if weqb b0 wzero then regrow0 st stS aw ws c else None
          | VP kB ob, VP kT oe, VP kB' oc =>
              if PrimInt63.eqb kB kB' && weqb ob wzero && weqb oe (wlit 24%uint63) then regrow1 st stS wnl aw ws c kB kT oc else None
          | _, _, _ => None
          end
      | None => None
      end
      else None
  | _, _ => None
  end.

Definition pkregrow_contract (pc : int) : contract := Contract pc pkregrow_apply.
End WithSrc.
End PkRegrowAC.
End TwinB.
