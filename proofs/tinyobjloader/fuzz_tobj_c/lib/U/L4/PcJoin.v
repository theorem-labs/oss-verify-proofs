From Stdlib Require Import ZArith List Bool PArith.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymFrame.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import ObjXform.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

(* Where a fresh variable of a joined state takes its value in each joined leaf. *)
Inductive loc := LReg (i : nat) | LFReg (i : nat) | LCell (j : nat) (off : Z) | LCur (j : nat) (off : Z).

Definition reg (S : sstate) (i : nat) : sv := nth i (ss_regs S) (SLit 0).
Definition freg (S : sstate) (i : nat) : sv := nth i (ss_fregs S) (SLit 0).

Definition off_lit (c : cell) : Z := match c_off c with SLit z => z | _ => 0 end.

Definition cell_at (o : sobj) (off w : Z) : option sv :=
  match find (fun c => sv_eqb (c_off c) (SLit off) && Z.eqb (c_width c) w) (ob_cells o) with
  | Some c => Some (c_val c)
  | None => None
  end.

(* Offset of a text pointer [vB + x] or [(vB + x) + k] from the text base. *)
Definition cur_off (v : sv) : sv :=
  match v with
  | SAlu ALU_ADD (SAlu ALU_ADD _ x) k => SAlu ALU_ADD x k
  | SAlu ALU_ADD _ x => x
  | _ => v
  end.

Section Join.
Variable vB : sv.
Variable vE : sv.
Variable keep_diff : bool.

Fixpoint join_regs (get : sstate -> nat -> sv) (mk : nat -> loc) (Ls : list sstate) (L0 : sstate) (i n : nat)
  (nx : positive) : list sv * list (positive * loc) * positive :=
  match n with
  | O => ([], [], nx)
  | S n' =>
      let v0 := get L0 i in
      let '(r1, l1, nx1) :=
        if forallb (fun L => sv_eqb (get L i) v0) Ls then ([v0], [], nx)
        else ([SVar nx], [(nx, mk i)], Pos.succ nx) in
      let '(r2, l2, nx2) := join_regs get mk Ls L0 (Datatypes.S i) n' nx1 in
      (r1 ++ r2, l1 ++ l2, nx2)
  end.

Fixpoint join_cells (Ls : list sstate) (j : nat) (cur : bool) (cs : list cell) (nx : positive)
  : list cell * list (positive * loc) * list sprop * positive :=
  match cs with
  | [] => ([], [], [], nx)
  | c :: t =>
      let vs := map (fun L => cell_at (nth j (ss_objs L) dummy_obj) (off_lit c) (c_width c)) Ls in
      let '(c1, l1, f1, nx1) :=
        if forallb (fun o => match o with Some _ => true | None => false end) vs then
          if cur then
            ([mkCell (c_off c) (c_width c) (SAlu ALU_ADD vB (SVar nx))], [(nx, LCur j (off_lit c))],
             [SPUle (SVar nx) vE], Pos.succ nx)
          else if forallb (fun o => match o with Some v => sv_eqb v (c_val c) | None => false end) vs
          then ([c], [], [], nx)
          else if keep_diff then
            ([mkCell (c_off c) (c_width c) (SVar nx)], [(nx, LCell j (off_lit c))], [], Pos.succ nx)
          else ([], [], [], nx)
        else ([], [], [], nx) in
      let '(c2, l2, f2, nx2) := join_cells Ls j cur t nx1 in
      (c1 ++ c2, l1 ++ l2, f1 ++ f2, nx2)
  end.

Fixpoint join_objs (Ls : list sstate) (curp : sv) (j : nat) (os : list sobj) (nx : positive)
  : list sobj * list (positive * loc) * list sprop * positive :=
  match os with
  | [] => ([], [], [], nx)
  | o :: t =>
      let cur := sv_eqb (SAlu ALU_ADD (ob_base o) (ob_lo o)) curp || sv_eqb (ob_base o) curp in
      let '(cs, l1, f1, nx1) := join_cells Ls j cur (ob_cells o) nx in
      let '(os2, l2, f2, nx2) := join_objs Ls curp (Datatypes.S j) t nx1 in
      (mkObj (ob_base o) (ob_lo o) (ob_hi o) cs (ob_dflt o) :: os2, l1 ++ l2, f1 ++ f2, nx2)
  end.

Definition max_next (Ls : list sstate) : positive :=
  fold_left (fun a L => Pos.max a (ss_next L)) Ls 1%positive.

(* Most specific common generalisation of [Ls] (same pc, same object layout), with the
   cursor cell (the cell [curp] points to) rewritten as [vB + fresh]. *)
Definition join (dflt : sstate) (curp : sv) (Ls : list sstate) : sstate * list (positive * loc) :=
  let L0 := nth 0 Ls dflt in
  let '(rs, lr, nx1) := join_regs reg LReg Ls L0 0 32 (max_next Ls) in
  let '(fs, lf, nx1') := join_regs freg LFReg Ls L0 0 32 nx1 in
  let '(os, lo, fo, nx2) := join_objs Ls curp 0 (ss_objs L0) nx1' in
  let facts := List.filter (fun f => forallb (fun L => existsb (sprop_equiv f) (ss_facts L)) Ls) (ss_facts L0) in
  (mkSS (ss_pc L0) rs fs (ss_fcsr L0) (ss_resv L0) os (fo ++ facts) nx2 false, lr ++ lf ++ lo).
End Join.

Definition loc_val (L : sstate) (l : loc) : sv :=
  match l with
  | LReg i => reg L i
  | LFReg i => freg L i
  | LCell j off =>
      match find (fun c => sv_eqb (c_off c) (SLit off)) (ob_cells (nth j (ss_objs L) dummy_obj)) with
      | Some c => c_val c | None => SLit 0 end
  | LCur j off =>
      match find (fun c => sv_eqb (c_off c) (SLit off)) (ob_cells (nth j (ss_objs L) dummy_obj)) with
      | Some c => cur_off (c_val c) | None => SLit 0 end
  end.

Definition sub_of (locs : list (positive * loc)) (L : sstate) : wsub :=
  map (fun p => (fst p, loc_val L (snd p))) locs.

(* Object merge plan for a frame split into pieces: rebase every [sp + k]-based piece with literal
   bounds onto sp, order the sp-based pieces by their low bound, and merge them. *)
Definition sp_off (o : sobj) : option Z :=
  match ob_base o, ob_lo o with
  | SAlu ALU_ADD (SVar 10) (SLit k), SLit _ => Some k
  | _, _ => None
  end.

Definition rebase_plan (S : sstate) : list xform :=
  map (fun p => XRebase (snd p))
    (List.filter (fun p => match sp_off (fst p) with Some _ => true | None => false end)
       (combine (ss_objs S) (seq 0 (length (ss_objs S))))).

Definition is_frame (o : sobj) : bool :=
  sv_eqb (ob_base o) (SVar 10) && match ob_lo o with SLit _ => true | _ => false end.
Definition lo_lit (o : sobj) : Z :=
  match ob_lo o with SLit z => z | SAlu ALU_SLL (SLit a) (SLit b) => Z.shiftl a b | _ => 0 end.

Fixpoint insert_by (k : Z) (x : nat) (l : list (Z * nat)) : list (Z * nat) :=
  match l with
  | [] => [(k, x)]
  | (k', y) :: t => if Z.leb k k' then (k, x) :: l else (k', y) :: insert_by k x t
  end.

Definition merge_plan_by (isp : sobj -> bool) (S : sstate) : list xform :=
  let ix := combine (ss_objs S) (seq 0 (length (ss_objs S))) in
  let fr := fold_right (fun p acc => if isp (fst p) then insert_by (lo_lit (fst p)) (snd p) acc else acc) [] ix in
  let others := map snd (List.filter (fun p => negb (isp (fst p))) ix) in
  XSelect (map snd fr ++ others) :: repeat (XMerge 0) (pred (length fr)).

Definition merge_plan : sstate -> list xform := merge_plan_by is_frame.
