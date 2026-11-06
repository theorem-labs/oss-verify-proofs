(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List Lia.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import ShapeAlg.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 W64Proofs Val IMap Mem Instr State Step Plan Notation ValProofs MemProofs PlanSound.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap Require Import Op.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import Model Layout Inv Steps OpsBridge Tree KidsFacts PkOps PkLib GLib GWin PkU.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val Mem FI St Step Plan ValP MemP PlanS HeapOp UB UG GW TR PK PKL.
Open Scope Z_scope.
Unset Lia Cache.
Arguments Uint63.to_Z : simpl never.
Arguments Z_to_bv : simpl never.

Module PkStack.

Definition dec_true (o : option bool) : bool := match o with Some true => true | _ => false end.
Definition dec_false (o : option bool) : bool := match o with Some false => true | _ => false end.

Definition ETOP : w64 := wlit 6%uint63.
Definition etop_win (k : int) (len : int) : sv * sv * sv := (VP k wzero, VL (wlit len), VL ETOP).

Definition only_kind (kd : Z) (w0 : option (sv * sv * sv)) (ws : list (sv * sv * sv)) : bool :=
  forallb (fun w => match kind_of w with
                    | Some k' => if k' =? kd then match w0 with Some x => win3_eqb w x | None => false end else true
                    | None => false
                    end) ws.

Record pkca := PC { c_root : sv; c_rootT : sv; c_n1 : sv; c_P1 : sv; c_zh : sv; c_c0 : sv; c_eb : sv; c_ee : sv; c_ecap : sv;
                    c_tptr : sv; c_trest : sv; c_tmap : sv; c_tkey : sv; c_cf : sv; c_fT : sv; c_fN : sv; c_fP : sv }.
Definition parse_ca (ca : list sv) : option pkca :=
  match ca with
  | [a; b; c; d; e; f; g; h; i; j; k; l; m; n; o; p; q] => Some (PC a b c d e f g h i j k l m n o p q)
  | _ => None
  end.
Definition unparse_ca (c : pkca) : list sv :=
  [c_root c; c_rootT c; c_n1 c; c_P1 c; c_zh c; c_c0 c; c_eb c; c_ee c; c_ecap c; c_tptr c; c_trest c; c_tmap c; c_tkey c;
   c_cf c; c_fT c; c_fN c; c_fP c].

Definition lit01 (v : sv) : option bool :=
  match v with VL w => if weqb w wzero then Some false else if weqb w (wlit 1%uint63) then Some true else None | _ => None end.
Definition b2v (b : bool) : sv := VL (if b then wlit 1%uint63 else wzero).

Definition top_cells (r : region) (base : Z) : option (sv * sv * sv * sv) :=
  match cell_at r base 8%uint63, cell_at r (base + 8) 8%uint63, cell_at r (base + 16) 1%uint63, cell_at r (base + 17) 1%uint63 with
  | Some p, Some n, Some m, Some k => Some (p, n, m, k)
  | _, _, _, _ => None
  end.

Definition top_region (p n : sv) (m k : bool) : region :=
  Region 0%uint63 (VL (wlit 24%uint63)) true BGNone
    (IMap.add 2%uint63 (Gran true [Cell 0%uint63 1%uint63 (b2v m); Cell 1%uint63 1%uint63 (b2v k)])
      (IMap.add 1%uint63 (Gran true [Cell 0%uint63 8%uint63 n])
        (IMap.add 0%uint63 (Gran true [Cell 0%uint63 8%uint63 p]) IMap.empty))).

Definition repoint_g (all : bool) (old new : sv) (st : sstate) : sstate :=
  let f := fun v => if sv_eqb v old then new else v in
  let R := if all then IMap.map (subst_cells f) (s_regs st) else
           match IMap.find 1%uint63 (s_regs st) with
           | Some r1 => IMap.add 1%uint63 (subst_cells f r1) (s_regs st)
           | None => s_regs st
           end in
  SS (s_pc st) (rf_map f (s_rf st)) (s_ff st) (s_resv st) R (s_facts st) (s_ops st) (s_priv st) (s_next st).
Definition repoint : sv -> sv -> sstate -> sstate := repoint_g false.

Definition flags_at (r : region) (off : Z) : option (sv * option sv) :=
  match cell_at r off 8%uint63 with
  | Some f => Some (f, None)
  | None => match cell_at r off 1%uint63, cell_at r (off + 1) 1%uint63 with
            | Some b0, Some b1 => Some (b0, Some b1)
            | _, _ => None
            end
  end.
Definition flags_ok (fs : list fact) (f : sv * option sv) (ismap : bool) : bool :=
  match f with
  | (w, None) => dec_true (decide_eq fs (sv_ext false 0%uint63 2%uint63 w) (VL (wlit (if ismap then 257%uint63 else 0%uint63))))
  | (b0, Some b1) => dec_true (decide_eq fs (sv_ext false 0%uint63 1%uint63 b0) (b2v ismap))
                     && dec_true (decide_eq fs (sv_ext false 0%uint63 1%uint63 b1) (b2v ismap))
  end.

Definition common_ok (st : sstate) (ws : list (sv * sv * sv)) : bool :=
  let n := s_next st in
  st_vars_below n st && PrimInt63.ltb 0%uint63 n && PrimInt63.ltb n (PrimInt63.sub bit62i 8%uint63)
  && Z.ltb (Z.of_nat (length ws)) 4000.

Section Pcs.
Variable THE_PC : int.

Definition roome_apply_g (af : bool) (st : sstate) : option (list sstate) :=
  match the_op st with
  | Some (md, aw, ws, ca) =>
      if PrimInt63.eqb md 3%uint63 then
      match parse_ca ca with
      | Some c =>
          match c_ee c with
          | VP kT oT =>
              match IMap.find kT (s_regs st) with
              | Some rT =>
                  if common_ok st ws && weqb oT (wlit 24%uint63) && negb (PrimInt63.eqb kT 0%uint63) && negb (PrimInt63.eqb kT 1%uint63)
                     && existsb (win3_eqb (etop_win kT 24%uint63)) ws && only_kind 6 (Some (etop_win kT 24%uint63)) ws
                     && PrimInt63.eqb (rg_lo rT) 0%uint63 && sv_eqb (rg_hi rT) (VL (wlit 24%uint63)) && rg_w rT
                     && match rg_bg rT with BGNone => true | _ => false end
                     && dec_true (decide_ltu (s_facts st) (c_ee c) (c_ecap c))
                     && implied (s_facts st) (FULe (c_eb c) (VP kT wzero))
                  then
                    let rT' := Region 0%uint63 (VL (wlit 48%uint63)) true BGNone (rg_cells rT) in
                    let ws' := List.map (fun w => if win3_eqb w (etop_win kT 24%uint63) then etop_win kT 48%uint63 else w) ws in
                    Some [surg st [kT] [(kT, rT')] (mk_args 3%uint63 aw ws' ca)
                               (if af then [FULe (VP kT (wlit 48%uint63)) (c_ecap c)] else []) (s_next st)]
                  else None
              | None => None
              end
          | _ => None
          end
      | None => None
      end
      else None
  | None => None
  end.
Definition roome_apply : sstate -> option (list sstate) := roome_apply_g false.
Definition roome_contract : contract := Contract THE_PC roome_apply.
Definition roome_contract_a : contract := Contract THE_PC (roome_apply_g true).

Definition push_apply_g (all : bool) (st : sstate) : option (list sstate) :=
  match the_op st with
  | Some (md, aw, ws, ca) =>
      if PrimInt63.eqb md 3%uint63 then
      match parse_ca ca with
      | Some c =>
          match c_ee c, c_fT c with
          | VP kT oT, VL t =>
              match IMap.find kT (s_regs st) with
              | Some rT =>
                  let fs := s_facts st in let n := s_next st in
                  let ismap := weqb t (wlit 8%uint63) in
                  let flags2 : int := if ismap then 257%uint63 else 0%uint63 in
                  match top_cells rT 0, cell_at rT 24 8%uint63, cell_at rT 32 8%uint63, flags_at rT 40 with
                  | Some (op, on, om, ok), Some np, Some nn, Some f =>
                      if common_ok st ws && weqb oT (wlit 24%uint63) && negb (PrimInt63.eqb kT 0%uint63) && negb (PrimInt63.eqb kT 1%uint63)
                         && (weqb t (wlit 7%uint63) || ismap)
                         && existsb (win3_eqb (etop_win kT 48%uint63)) ws && only_kind 6 (Some (etop_win kT 48%uint63)) ws
                         && PrimInt63.eqb (rg_lo rT) 0%uint63 && sv_eqb (rg_hi rT) (VL (wlit 48%uint63)) && rg_w rT
                         && dec_false (decide_eq0 fs (c_cf c))

                         && sv_eqb op (c_tptr c) && sv_eqb on (c_trest c) && dec_true (decide_eq fs om (c_tmap c)) && dec_true (decide_eq fs ok (c_tkey c))

                         && dec_true (decide_eq fs np (c_fP c)) && dec_true (decide_eq fs nn (c_fN c))
                         && flags_ok fs f ismap
                      then
                        let kT' := n in
                        let ws' := List.map (fun w => if win3_eqb w (etop_win kT 48%uint63) then etop_win kT' 24%uint63 else w) ws in
                        let c' := PC (c_root c) (c_rootT c) (c_n1 c) (c_P1 c) (c_zh c) (c_c0 c) (c_eb c) (VP kT' (wlit 24%uint63)) (c_ecap c)
                                     (c_fP c) (c_fN c) (b2v ismap) (b2v ismap) (VL wzero) (VL wzero) (VL wzero) (VL wzero) in
                        let st1 (wsF : list (sv * sv * sv)) := surg st [kT] [(kT', top_region (c_fP c) (c_fN c) ismap ismap)] (mk_args 3%uint63 aw wsF (unparse_ca c'))
                                        ([FEq (VP kT' wzero) (VP kT (wlit 24%uint63)); FULe (c_eb c) (VP kT' wzero); FULe (VP kT' (wlit 24%uint63)) (c_ecap c)] ++ top_facts fs (c_eb c) kT') (PrimInt63.add n 1%uint63) in
                        match PkU.pku_flip fs negb true ws' with
                        | Some wsF => Some [repoint_g all (VP kT (wlit 48%uint63)) (VP kT' (wlit 24%uint63)) (st1 wsF)]
                        | None => None
                        end
                      else None
                  | _, _, _, _ => None
                  end
              | None => None
              end
          | _, _ => None
          end
      | None => None
      end
      else None
  | None => None
  end.
Definition push_apply : sstate -> option (list sstate) := push_apply_g false.
Definition push_contract : contract := Contract THE_PC push_apply.
Definition push_contract_a : contract := Contract THE_PC (push_apply_g true).

Definition root_type_lit (fs : list fact) (v : sv) : option w64 :=
  match v with
  | VL t => Some t
  | _ => if dec_true (decide_eq fs v (VL (wlit 7%uint63))) then Some (wlit 7%uint63)
         else if dec_true (decide_eq fs v (VL (wlit 8%uint63))) then Some (wlit 8%uint63) else None
  end.

Definition p1_align (p : sv) : list fact :=
  match p with
  | VP k o => if weqb o wzero && negb (PrimInt63.eqb k 0%uint63) then [FAlign k 3%uint63] else []
  | _ => []
  end.

Definition push0_apply (st : sstate) : option (list sstate) :=
  match the_op st with
  | Some (md, aw, ws, ca) =>
      if PrimInt63.eqb md 3%uint63 then
      match parse_ca ca with
      | Some c =>
          match c_ee c, c_eb c, c_ecap c, root_type_lit (s_facts st) (c_rootT c) with
          | VP kT oT, VP kB oB, VP kE offC, Some t =>
              match IMap.find kT (s_regs st) with
              | Some rT =>
                  let fs := s_facts st in
                  let ismap := weqb t (wlit 8%uint63) in
                  let flags2 : int := if ismap then 257%uint63 else 0%uint63 in
                  match cell_at rT 0 8%uint63, cell_at rT 8 8%uint63, flags_at rT 16 with
                  | Some np, Some nn, Some f =>
                      if common_ok st ws && weqb oT wzero && weqb oB wzero && PrimInt63.eqb kT kB && PrimInt63.eqb kT kE
                         && negb (PrimInt63.eqb kT 0%uint63) && negb (PrimInt63.eqb kT 1%uint63)
                         && negb (wt offC) && PrimInt63.leb 24%uint63 (wl offC)
                         && (weqb t (wlit 7%uint63) || ismap)
                         && existsb (win3_eqb (etop_win kT 24%uint63)) ws && only_kind 6 (Some (etop_win kT 24%uint63)) ws
                         && PrimInt63.eqb (rg_lo rT) 0%uint63 && sv_eqb (rg_hi rT) (VL (wlit 24%uint63)) && rg_w rT
                         && dec_true (decide_eq fs np (c_P1 c)) && dec_true (decide_eq fs nn (c_n1 c))
                         && flags_ok fs f ismap
                      then
                        let c' := PC (c_root c) (VL t) (c_n1 c) (c_P1 c) (c_zh c) (c_c0 c) (c_eb c) (VP kT (wlit 24%uint63)) (c_ecap c)
                                     (c_P1 c) (c_n1 c) (b2v ismap) (b2v ismap) (VL wzero) (VL wzero) (VL wzero) (VL wzero) in
                        match PkU.pku_flip fs (fun _ => true) true ws with
                        | Some wsF => Some [surg st [kT] [(kT, top_region (c_P1 c) (c_n1 c) ismap ismap)] (mk_args 3%uint63 aw wsF (unparse_ca c')) (p1_align (c_P1 c)) (s_next st)]
                        | None => None
                        end
                      else None
                  | _, _, _ => None
                  end
              | None => None
              end
          | _, _, _, _ => None
          end
      | None => None
      end
      else None
  | None => None
  end.
Definition push0_contract : contract := Contract THE_PC push0_apply.

Definition next_apply (st : sstate) : option (list sstate) :=
  match the_op st with
  | Some (md, aw, ws, ca) =>
      if PrimInt63.eqb md 3%uint63 then
      match parse_ca ca with
      | Some c =>
          match c_ee c, lit01 (c_tmap c), lit01 (c_tkey c) with
          | VP kT oT, Some m, Some k =>
              match IMap.find kT (s_regs st) with
              | Some rT =>
                  let fs := s_facts st in
                  match top_cells rT 0 with
                  | Some (np, nn, nm, nk) =>
                      let exp_p := if m then (if k then c_tptr c else sv_alu ALU_ADD (c_tptr c) (VL (wlit 48%uint63)))
                                   else sv_alu ALU_ADD (c_tptr c) (VL (wlit 24%uint63)) in
                      let exp_n := if m && k then c_trest c else sv_alu ALU_ADD (c_trest c) (VL wones) in
                      let k' := if m then negb k else false in
                      if common_ok st ws && weqb oT (wlit 24%uint63) && negb (PrimInt63.eqb kT 0%uint63)
                         && existsb (win3_eqb (etop_win kT 24%uint63)) ws
                         && dec_false (decide_eq0 fs (c_trest c))
                         && dec_true (decide_eq fs np exp_p) && dec_true (decide_eq fs nn exp_n)
                         && dec_true (decide_eq fs nm (b2v m)) && dec_true (decide_eq fs nk (b2v k'))
                         && dec_false (decide_eq0 fs nn)
                      then
                        let c' := PC (c_root c) (c_rootT c) (c_n1 c) (c_P1 c) (c_zh c) (c_c0 c) (c_eb c) (c_ee c) (c_ecap c)
                                     np nn (b2v m) (b2v k') (VL wzero) (VL wzero) (VL wzero) (VL wzero) in
                        match PkU.pku_flip fs (fun _ => true) true ws with
                        | Some ws1 => Some [surg st [] [] (mk_args 3%uint63 aw ws1 (unparse_ca c')) [] (s_next st)]
                        | None => None
                        end
                      else None
                  | None => None
                  end
              | None => None
              end
          | _, _, _ => None
          end
      | None => None
      end
      else None
  | None => None
  end.
Definition next_contract : contract := Contract THE_PC next_apply.

Definition pop_apply_g (all : bool) (st : sstate) : option (list sstate) :=
  match the_op st with
  | Some (md, aw, ws, ca) =>
      if PrimInt63.eqb md 3%uint63 then
      match parse_ca ca with
      | Some c =>
          match c_ee c with
          | VP kT oT =>
              match IMap.find kT (s_regs st) with
              | Some rT =>
              let fs := s_facts st in let n := s_next st in
              if common_ok st ws && weqb oT (wlit 24%uint63) && negb (PrimInt63.eqb kT 0%uint63) && negb (PrimInt63.eqb kT 1%uint63)
                 && existsb (win3_eqb (etop_win kT 24%uint63)) ws
                 && PrimInt63.eqb (rg_lo rT) 0%uint63 && sv_eqb (rg_hi rT) (VL (wlit 24%uint63)) && rg_w rT
                 && dec_true (decide_eq fs (getr st X11) (VP kT wzero))
                 && implied fs (FULe (c_eb c) (VP kT wzero))
                 && dec_false (decide_eq fs (c_eb c) (VP kT wzero))
              then
                let ws0 := List.filter (fun w => negb (win3_eqb w (etop_win kT 24%uint63))) ws in

                let mkB (wsF : list (sv * sv * sv)) (m k : bool) :=
                  let kT' := n in let kp := PrimInt63.add n 1%uint63 in let kr := PrimInt63.add n 2%uint63 in
                  let cB := PC (c_root c) (c_rootT c) (c_n1 c) (c_P1 c) (c_zh c) (c_c0 c) (c_eb c) (VP kT' (wlit 24%uint63)) (c_ecap c)
                               (VP kp wzero) (VP kr wzero) (b2v m) (b2v k) (VL wzero) (VL wzero) (VL wzero) (VL wzero) in
                  repoint_g all (VP kT wzero) (VP kT' (wlit 24%uint63))
                    (surg st [kT] [(kT', top_region (VP kp wzero) (VP kr wzero) m k)] (mk_args 3%uint63 aw wsF (unparse_ca cB))
                          ([FEq (VP kT' (wlit 24%uint63)) (VP kT wzero); FRange kr (wlit 1%uint63) (wlit 1000%uint63); FAlign kp 3%uint63;
                            FULe (c_eb c) (VP kT' wzero); FULe (VP kT' (wlit 24%uint63)) (c_ecap c)] ++ top_facts fs (c_eb c) kT'
                           ++ KF.kids_facts (VP kr wzero) (VP kp wzero))
                          (PrimInt63.add n 3%uint63)) in
                match PkU.pku_flip fs (fun _ => true) false (ws0 ++ [etop_win n 24%uint63]) with
                | Some wsF => Some [mkB wsF false false; mkB wsF true true; mkB wsF true false]
                | None => None
                end
              else None
              | None => None
              end
          | _ => None
          end
      | None => None
      end
      else None
  | None => None
  end.
Definition pop_apply : sstate -> option (list sstate) := pop_apply_g false.
Definition pop_contract : contract := Contract THE_PC pop_apply.
Definition pop_contract_a : contract := Contract THE_PC (pop_apply_g true).

End Pcs.
End PkStack.
