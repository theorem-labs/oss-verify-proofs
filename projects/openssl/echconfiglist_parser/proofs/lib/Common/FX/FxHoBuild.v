(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Uint63 PrimString.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Common.FX Require Import
  W64 ITrie FxInstr FxState FxMem FxExec FxHandoff.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope uint63_scope.

Section Build.
Variable IM : fimage.
Variable facts : list hfact.

(* [comment removed for export] *)
Fixpoint cells_from (fuel : nat) (c last : int) : list int :=
  match fuel with
  | O => []
  | S f => if c <=? last then c :: cells_from f (c + 8) last else []
  end.
Definition span_cells (o n : int) : list int :=
  if n =? 0 then [] else
  let c0 := (o >> 3) << 3 in
  let c1 := ((o + n - 1) >> 3) << 3 in
  cells_from (S (Z.to_nat (to_Z ((c1 - c0) >> 3)))) c0 c1.

(* [comment removed for export] *)
Definition zero_page (t pn : int) : bool := zero_cov facts t (pn << 12) 4096.

(* [comment removed for export] *)
Definition cells_of_fact (t : int) (f : hfact) : list int :=
  match f with
  | HCell t' o n _ => if t' =? t then span_cells o n else []
  | HVal t' o _ => if t' =? t then span_cells o 8 else []
  | HBytes t' o n _ => if t' =? t then span_cells o n else []
  | HZero t' o l =>
      if (t' =? t) && (l <=? 1048576)
      then filter (fun c => negb (zero_page t (c >> 12))) (span_cells o l) else []
  | _ => []
  end.

(* [comment removed for export] *)
Definition sym_slot (t a : int) : slot :=
  let fix go (fs : list hfact) : slot :=
    match fs with
    | [] => SU
    | f :: r =>
        match f with
        | HBytes t' o n v =>
            if (t' =? t) && negb (vtag v =? 0) && (o <=? a) && (a <? o + n) && (n <=? 8) then SV v (a - o) else go r
        | HVal t' o v =>
            if (t' =? t) && negb (vtag v =? 0) && (o <=? a) && (a <? o + 8) then SV v (a - o) else go r
        | _ => go r
        end
    end in
  go facts.
Definition slot_of (t a : int) : slot :=
  match byte_known IM facts t a with
  | Some b => SK b
  | None => sym_slot t a
  end.

Definition slot_is_v (s : slot) (v : fval) (j : int) : bool :=
  match s with SV v' j' => fval_eqb v' v && (j' =? j) | _ => false end.

Definition cell_of (t c : int) : cell :=
  let s0 := slot_of t c in let s1 := slot_of t (c + 1) in let s2 := slot_of t (c + 2) in
  let s3 := slot_of t (c + 3) in let s4 := slot_of t (c + 4) in let s5 := slot_of t (c + 5) in
  let s6 := slot_of t (c + 6) in let s7 := slot_of t (c + 7) in
  match s0, s1, s2, s3, s4, s5, s6, s7 with
  | SK b0, SK b1, SK b2, SK b3, SK b4, SK b5, SK b6, SK b7 =>
      CV (FV 0 (w_of_bytes8 b0 b1 b2 b3 b4 b5 b6 b7))
  | SV v _, _, _, _, _, _, _, _ =>
      if slot_is_v s0 v 0 && slot_is_v s1 v 1 && slot_is_v s2 v 2 && slot_is_v s3 v 3
         && slot_is_v s4 v 4 && slot_is_v s5 v 5 && slot_is_v s6 v 6 && slot_is_v s7 v 7
      then CV v else CB (SL s0 s1 s2 s3 s4 s5 s6 s7)
  | _, _, _, _, _, _, _, _ => CB (SL s0 s1 s2 s3 s4 s5 s6 s7)
  end.

(* [comment removed for export] *)
Definition add_cell (t : int) (acc : itrie (list (int * cell))) (c : int) : itrie (list (int * cell)) :=
  let pn := c >> 12 in
  let ci := (c land 4095) >> 3 in
  let old := match iget pn acc with Some l => l | None => [] end in
  if existsb (fun p => fst p =? ci) old then acc
  else iset pn ((ci, cell_of t c) :: old) acc.

(* [comment removed for export] *)
Fixpoint pages_list (fuel : nat) (pn last : int) : list int :=
  match fuel with
  | O => []
  | S f => if pn <=? last then pn :: pages_list f (pn + 1) last else []
  end.
Definition zero_pages_of_fact (t : int) (f : hfact) : list int :=
  match f with
  | HZero t' o l =>
      if (t' =? t) && (4096 <=? l) && (l <=? 1048576) then
        let p0 := (o + 4095) >> 12 in
        let p1 := ((o + l) >> 12) in
        if p0 <? p1 then pages_list (S (Z.to_nat (to_Z (p1 - p0)))) p0 (p1 - 1) else []
      else []
  | _ => []
  end.

Definition page_desc (t pn : int) (cells : list (int * cell)) : pdesc :=
  if t =? 0 then PD pn (seg_wr_page IM pn) PKImage cells
  else PD pn (wr_cov facts t (pn << 12) 4096) (if zero_page t pn then PKZero else PKUnk) cells.

Definition all_su (c : cell) : bool :=
  match c with
  | CB (SL SU SU SU SU SU SU SU SU) => true
  | _ => false
  end.

(* [comment removed for export] *)
Definition image_page_cells (pn : int) : list (int * cell) :=
  flat_map (fun ci =>
     let c := (pn << 12) + (ci << 3) in
     if clear_cov facts c 8 then []
     else let x := cell_of 0 c in [(ci, if all_su x then CU else x)]) (iseq 512).

(* [comment removed for export] *)
Definition image_pages : list int :=
  flat_map (fun sg =>
     filter (fun pn => negb (clear_cov facts (pn << 12) 4096))
            (pages_list (Z.to_nat (to_Z (sg_size sg >> 12))) (sg_base sg >> 12)
                        ((sg_base sg >> 12) + (sg_size sg >> 12) - 1))) IM.

Definition region_desc (shape : int * int * int * int * option pkind) : rdesc :=
  let '(t, lo, len, al, dflt) := shape in
  if t =? 0 then
    RD t lo len al dflt (map (fun pn => page_desc 0 pn (image_page_cells pn)) image_pages)
  else
  let cells := flat_map (cells_of_fact t) facts in
  let grouped := fold_left (add_cell t) cells iempty in
  let zp := flat_map (zero_pages_of_fact t) facts in
  let grouped := fold_left (fun acc pn => match iget pn acc with Some _ => acc | None => iset pn [] acc end) zp grouped in
  RD t lo len al dflt (map (fun kv => page_desc t (fst kv) (snd kv)) (ielements grouped)).

Definition regs_desc : list (int * fval) :=
  flat_map (fun f => match f with HReg r v => [(r, v)] | _ => [] end) facts.

Definition ho_build (pc : int) (shapes : list (int * int * int * int * option pkind)) : sdesc :=
  SD pc regs_desc (map region_desc shapes).
End Build.
