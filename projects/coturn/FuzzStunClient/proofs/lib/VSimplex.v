(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Bool.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import VMap VLin VItv VStore VFarkas VSimplexI.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import VLpKey VLpTab.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Unset Lia Cache.
Unset Lia Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition srow := list term.

(* [comment removed for export] *)
Fixpoint sget (r : srow) (c : positive) : Z :=
  match r with
  | [] => 0
  | (c', v) :: t =>
      match Pos.compare c' c with
      | Lt => sget t c
      | Eq => v
      | Gt => 0
      end
  end.

Fixpoint srow_gcd (r : srow) (acc : Z) : Z :=
  match r with
  | [] => acc
  | (_, x) :: t => if Z.eqb acc 1 then 1 else srow_gcd t (Z.gcd x acc)
  end.

Fixpoint srow_div (r : srow) (g : Z) : srow :=
  match r with
  | [] => []
  | (c, x) :: t => (c, x / g) :: srow_div t g
  end.

Fixpoint srow_remove (r : srow) (c : positive) : srow :=
  match r with
  | [] => []
  | (c', v) :: t =>
      match Pos.compare c' c with
      | Lt => (c', v) :: srow_remove t c
      | Eq => t
      | Gt => r
      end
  end.

Fixpoint lcm_list (l : list Z) : Z :=
  match l with [] => 1 | d :: t => Z.lcm d (lcm_list t) end.

Fixpoint iotaN (from : N) (n : nat) : list N :=
  match n with O => [] | S n' => from :: iotaN (N.succ from) n' end.

(* [comment removed for export] *)
(* [comment removed for export] *)

Record trow := mkRow { bcol : positive ; ents : srow ; rhs : Z }.
Record zrow := mkZ { zc : Z ; zents : srow ; zrhs : Z }.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition elim_row (p' : Z) (pr : srow) (prhs : Z) (c : positive) (row : trow) : trow :=
  let t := sget (ents row) c in
  if Z.eqb t 0 then row
  else
    if Z.eqb p' 1 then mkRow (bcol row) (terms_axpy (- t) (ents row) pr) (rhs row - t * prhs)
    else
    let e := terms_axpy (- t) (terms_scale p' (ents row)) pr in
    let h := p' * rhs row - t * prhs in
    let g := srow_gcd e (Z.abs h) in
    if Z.leb g 1 then mkRow (bcol row) e h
    else mkRow (bcol row) (srow_div e g) (h / g).

Definition elim_z (p' : Z) (pr : srow) (prhs : Z) (c : positive) (z : zrow) : zrow :=
  let t := sget (zents z) c in
  if Z.eqb t 0 then z
  else
    if Z.eqb p' 1 then mkZ (zc z) (terms_axpy (- t) (zents z) pr) (zrhs z - t * prhs)
    else
    let e := terms_axpy (- t) (terms_scale p' (zents z)) pr in
    let h := p' * zrhs z - t * prhs in
    let zc' := p' * zc z in
    let g := srow_gcd e (Z.gcd (Z.abs h) zc') in
    if Z.leb g 1 then mkZ zc' e h
    else mkZ (zc' / g) (srow_div e g) (h / g).

Fixpoint pivot_rows (T : list trow) (r : nat) (c : positive) (p' : Z) (pr : srow) (prhs : Z) : list trow :=
  match T with
  | [] => []
  | row :: t =>
      match r with
      | O => mkRow c pr prhs :: map (elim_row p' pr prhs c) t
      | S r' => elim_row p' pr prhs c row :: pivot_rows t r' c p' pr prhs
      end
  end.

Definition pivot (T : list trow) (z : zrow) (r : nat) (c : positive) : list trow * zrow :=
  let row := nth r T (mkRow xH [] 0) in
  let p := sget (ents row) c in
  let pr := if Z.ltb p 0 then terms_scale (-1) (ents row) else ents row in
  let prhs := if Z.ltb p 0 then - rhs row else rhs row in
  let p' := Z.abs p in
  (pivot_rows T r c p' pr prhs, elim_z p' pr prhs c z).

(* [comment removed for export] *)
Fixpoint find_entering (e : srow) : option positive :=
  match e with
  | [] => None
  | (c, x) :: t => if Z.ltb x 0 then Some c else find_entering t
  end.

(* [comment removed for export] *)
Fixpoint find_leaving (T : list trow) (i : nat) (c : positive) (best : option (nat * positive * Z * Z)) : option nat :=
  match T with
  | [] => match best with Some (k, _, _, _) => Some k | None => None end
  | row :: T' =>
      let t := sget (ents row) c in
      let best' :=
        if Z.leb t 0 then best
        else match best with
             | None => Some (i, bcol row, rhs row, t)
             | Some (k, bk, rk, tk) =>
                 let l := rhs row * tk in let r := rk * t in
                 if Z.ltb l r then Some (i, bcol row, rhs row, t)
                 else if Z.eqb l r then (if Pos.ltb (bcol row) bk then Some (i, bcol row, rhs row, t) else best)
                 else best
             end in
      find_leaving T' (S i) c best'
  end.

Inductive sresult : Type :=
| SOpt (T : list trow) (z : zrow)
| SUnbounded
| SFuel.

Fixpoint simplex (fuel : nat) (T : list trow) (z : zrow) : sresult :=
  match fuel with
  | O => SFuel
  | S fuel' =>
      match find_entering (zents z) with
      | None => SOpt T z
      | Some c =>
          match find_leaving T O c None with
          | None => SUnbounded
          | Some r => let '(T', z') := pivot T z r c in simplex fuel' T' z'
          end
      end
  end.

(* [comment removed for export] *)
Definition zrow_init (d : srow) : zrow := mkZ 1 (terms_scale (-1) d) 0.

Definition zrow_elim (T : list trow) (z : zrow) : zrow :=
  fold_left (fun (z : zrow) (row : trow) =>
               let b := sget (ents row) (bcol row) in
               if Z.leb b 0 then z
               else elim_z b (ents row) (rhs row) (bcol row) z) T z.

(* [comment removed for export] *)
Definition duals_to_hint (zcoef : Z) (ds : list (N * Z)) : option hint :=
  if Z.leb zcoef 0 then None
  else if existsb (fun d : N * Z => Z.ltb (snd d) 0) ds then None
  else
    let ds := filter (fun d : N * Z => Z.ltb 0 (snd d)) ds in
    let fr := map (fun d : N * Z => let g := Z.gcd (snd d) zcoef in (fst d, (snd d / g, zcoef / g))) ds in
    let k := lcm_list (map (fun f : N * (Z * Z) => snd (snd f)) fr) in
    if Z.leb k 0 then None else
    Some (HIdx (Z.to_pos k)
               (map (fun f : N * (Z * Z) => (fst f, Z.to_pos (fst (snd f) * (k / snd (snd f))))) fr)).

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Record symcol := mkSymcol { sc_col : positive ; sc_sign : Z ; sc_col2 : option positive ; sc_base : Z }.

Record lpsetup := mkSetup {
  su_map : pmap symcol ;
  su_next : positive ;                  (* [comment removed for export] *)
  su_boxrows : list (positive * Z)      (* [comment removed for export] *)
}.

Fixpoint setup_cols (B : box) (syms : list positive) (acc : lpsetup) : lpsetup :=
  match syms with
  | [] => acc
  | s :: t =>
      let c := su_next acc in
      let acc' :=
        match box_get B s with
        | (Some lo, Some hi) =>
            mkSetup (pm_set s (mkSymcol c 1 None lo) (su_map acc)) (Pos.succ c) ((c, hi - lo) :: su_boxrows acc)
        | (Some lo, None) =>
            mkSetup (pm_set s (mkSymcol c 1 None lo) (su_map acc)) (Pos.succ c) (su_boxrows acc)
        | (None, Some hi) =>
            mkSetup (pm_set s (mkSymcol c (-1) None hi) (su_map acc)) (Pos.succ c) (su_boxrows acc)
        | (None, None) =>
            mkSetup (pm_set s (mkSymcol c 1 (Some (Pos.succ c)) 0) (su_map acc)) (Pos.succ (Pos.succ c)) (su_boxrows acc)
        end in
      setup_cols B t acc'
  end.

(* [comment removed for export] *)
Fixpoint terms_cols (mp : pmap symcol) (l : list term) (acc : srow) (k0 : Z) : srow * Z :=
  match l with
  | [] => (acc, k0)
  | (s, k) :: t =>
      match pm_get s mp with
      | None => terms_cols mp t acc k0   (* [comment removed for export] *)
      | Some sc =>
          let acc1 := terms_axpy (k * sc_sign sc) acc [(sc_col sc, 1)] in
          let acc2 := match sc_col2 sc with
                      | None => acc1
                      | Some c2 => terms_axpy (- k) acc1 [(c2, 1)]
                      end in
          terms_cols mp t acc2 (k0 + k * sc_base sc)
      end
  end.

(* [comment removed for export] *)
Fixpoint mark_syms (l : list term) (m : pmap unit) : pmap unit :=
  match l with [] => m | (s, _) :: t => mark_syms t (pm_set s tt m) end.

Fixpoint touches (l : list term) (m : pmap unit) : bool :=
  match l with [] => false | (s, _) :: t => pm_mem s m || touches t m end.

Fixpoint comp_pass (cs : list (N * lin)) (symset : pmap unit) (sel rest : list (N * lin)) (changed : bool)
  : pmap unit * list (N * lin) * list (N * lin) * bool :=
  match cs with
  | [] => (symset, sel, rest, changed)
  | (i, g) :: t =>
      if touches (lt g) symset
      then comp_pass t (mark_syms (lt g) symset) ((i, g) :: sel) rest true
      else comp_pass t symset sel ((i, g) :: rest) changed
  end.

Fixpoint comp_iter (fuel : nat) (cs : list (N * lin)) (symset : pmap unit) (sel : list (N * lin))
  : pmap unit * list (N * lin) :=
  match fuel with
  | O => (symset, sel)
  | S fuel' =>
      let '(symset', sel', rest, changed) := comp_pass cs symset sel [] false in
      if changed then comp_iter fuel' rest symset' sel' else (symset', sel')
  end.

Fixpoint index_cons (cs : list lin) (i : N) : list (N * lin) :=
  match cs with [] => [] | c :: t => (i, c) :: index_cons t (N.succ i) end.

Definition component (St : store) (a : lin) : pmap unit * list (N * lin) :=
  let cs := index_cons (scons St) 0%N in
  comp_iter (Datatypes.S (length cs)) cs (mark_syms (lt a) pm_empty) [].

(* [comment removed for export] *)
(* [comment removed for export] *)

Inductive lpresult : Type :=
| LOpt (h : hint)          (* [comment removed for export] *)
| LInfeasible (h : hint)   (* [comment removed for export] *)
| LUnbounded
| LFail.

Fixpoint find_row_with_bcol (T : list trow) (i : nat) (c : positive) : option (nat * trow) :=
  match T with
  | [] => None
  | row :: t => if Pos.eqb (bcol row) c then Some (i, row) else find_row_with_bcol t (S i) c
  end.

Definition art_pivot_out (T : list trow) (z : zrow) (art : positive) : list trow * zrow :=
  match find_row_with_bcol T O art with
  | None => (T, z)
  | Some (r, row) =>
      match find (fun cv : positive * Z => negb (Pos.eqb (fst cv) art)) (ents row) with
      | None => (T, z)
      | Some (j, _) => pivot T z r j
      end
  end.

Definition remove_col (T : list trow) (c : positive) : list trow :=
  map (fun row => mkRow (bcol row) (srow_remove (ents row) c) (rhs row)) T.

Definition FUEL : nat := 1000%nat.

Fixpoint most_negative (T : list trow) (i : nat) (best : option (nat * Z)) : option (nat * Z) :=
  match T with
  | [] => best
  | row :: t =>
      let best' := if Z.ltb (rhs row) (match best with Some (_, b) => b | None => 0 end)
                   then Some (i, rhs row) else best in
      most_negative t (S i) best'
  end.

Record lpprob := mkProb {
  pr_T0 : list trow ; pr_obj : srow ; pr_art : positive ;
  pr_gslack : list (N * positive)        (* [comment removed for export] *)
}.

Fixpoint build_grows (mp : pmap symcol) (gs : list (N * lin)) (slack : positive) (art : positive)
  (accT : list trow) (accg : list (N * positive)) : list trow * list (N * positive) * positive :=
  match gs with
  | [] => (accT, accg, slack)
  | (i, g) :: t =>
      let '(coefs, k0) := terms_cols mp (lt g) [] (lc g) in
      let r := - k0 in
      let e := coefs ++ (if Z.ltb r 0 then [(slack, 1); (art, -1)] else [(slack, 1)]) in
      build_grows mp t (Pos.succ slack) art (mkRow slack e r :: accT) ((i, slack) :: accg)
  end.

Fixpoint build_brows (brs : list (positive * Z)) (slack : positive) (art : positive) (accT : list trow)
  : list trow :=
  match brs with
  | [] => accT
  | (c, r) :: t =>
      let e := (c, 1) :: (if Z.ltb r 0 then [(slack, 1); (art, -1)] else [(slack, 1)]) in
      build_brows t (Pos.succ slack) art (mkRow slack e r :: accT)
  end.

Definition lp_setup (St : store) (symset : pmap unit) (gs : list (N * lin)) (a : lin) : lpprob :=
  let syms := map fst (pm_elements symset) in
  let su := setup_cols (sbox St) syms (mkSetup pm_empty xH []) in
  let n := su_next su in                                   (* [comment removed for export] *)
  let m := (length gs + length (su_boxrows su))%nat in
  let art := Pos.of_nat (Pos.to_nat n + m) in
  let '(Tg, gsl, slack1) := build_grows (su_map su) gs n art [] [] in
  let Tb := build_brows (su_boxrows su) slack1 art [] in
  let '(obj, _) := terms_cols (su_map su) (lt a) [] 0 in
  mkProb (rev_append Tg (rev Tb)) obj art gsl.

Definition lp_run (pb : lpprob) : lpresult :=
  let T0 := pr_T0 pb in let art := pr_art pb in
  let mk_hint := fun (z : zrow) =>
                   duals_to_hint (zc z) (map (fun isl : N * positive => (fst isl, sget (zents z) (snd isl)))
                                             (pr_gslack pb)) in
  (* [comment removed for export] *)
  let phase1 : option (list trow * option zrow) :=
    match most_negative T0 O None with
    | None => Some (T0, None)
    | Some (r0, _) =>
        let z1 := zrow_init [(art, -1)] in                      (* [comment removed for export] *)
        let '(T1, z1') := pivot T0 z1 r0 art in
        match simplex FUEL T1 z1' with
        | SOpt T2 z2 =>
            if Z.ltb (zrhs z2) 0 then Some ([], Some z2)       (* [comment removed for export] *)
            else let '(T3, z3) := art_pivot_out T2 z2 art in Some (remove_col T3 art, None)
        | _ => None
        end
    end in
  match phase1 with
  | None => LFail
  | Some (_, Some zinf) => match mk_hint zinf with Some h => LInfeasible h | None => LFail end
  | Some (T, None) =>
      let z := zrow_elim T (zrow_init (pr_obj pb)) in
      match simplex FUEL T z with
      | SOpt T' z' => match mk_hint z' with Some h => LOpt h | None => LFail end
      | SUnbounded => LUnbounded
      | SFuel => LFail
      end
  end.

(* [comment removed for export] *)
Definition lp_solve_raw (St : store) (symset : pmap unit) (gs : list (N * lin)) (a : lin) : lpresult :=
  (* [comment removed for export] *)
  match ilp_solve St symset gs a with
  | IOpt h => LOpt h
  | IInfeasible h => LInfeasible h
  | IUnbounded => LUnbounded
  | IFail => lp_run (lp_setup St symset gs a)
  end.

Definition box_implied (B : box) (g : lin) : bool :=
  match snd (lin_range B g) with Some u => Z.leb u 0 | None => false end.

Definition box_nonempty (B : box) (s : positive) : bool :=
  match box_get B s with (Some lo, Some hi) => Z.leb lo hi | _ => true end.

Fixpoint terms_gcdz (l : list term) (acc : Z) : Z :=
  match l with [] => acc | (_, k) :: t => terms_gcdz t (Z.gcd k acc) end.

Definition scale_hint (g : Z) (h : hint) : hint :=
  match h with
  | HIdx k lams => HIdx k (map (fun il : N * positive => (fst il, Z.to_pos (Zpos (snd il) * g))) lams)
  | _ => h
  end.

(* [comment removed for export] *)
Fixpoint terms_ub_ne (B : box) (l : list term) (acc : Z) : option Z :=
  match l with
  | [] => Some acc
  | (s, k) :: t =>
      match box_get B s with
      | (Some lo, Some hi) => if Z.ltb hi lo then None else terms_ub_ne B t (acc + (if Z.ltb k 0 then k * lo else k * hi))
      | (Some lo, None) => if Z.ltb k 0 then terms_ub_ne B t (acc + k * lo) else None
      | (None, Some hi) => if Z.ltb 0 k then terms_ub_ne B t (acc + k * hi) else None
      | (None, None) => None
      end
  end.

Definition box_implied_c (B : box) (g : lin) : bool :=
  match terms_ub_ne B (lt g) (lc g) with Some u => Z.leb u 0 | None => false end.

Definition lp_solve0 (St : store) (symset : pmap unit) (gs : list (N * lin)) (a : lin) : lpresult :=
  let gs' := List.filter (fun ig : N * lin => negb (box_implied_c (sbox St) (snd ig))) gs in
  match gs' with
  | [] => LOpt HBox
  | _ =>
      let g := terms_gcdz (lt a) 0 in
      if Z.leb g 1 then lp_solve_raw St symset gs' a else
      match lp_solve_raw St symset gs' (mkLin 0 (map (fun t : term => (fst t, snd t / g)) (lt a))) with
      | LOpt h => LOpt (scale_hint g h)
      | r => r
      end
  end.

(* [comment removed for export] *)
Definition lp_solve (St : store) (symset : pmap unit) (gs : list (N * lin)) (a : lin) : lpresult :=
  match lpt_find (lp_key St symset gs a) with
  | Some (t, h) =>
      if tag_opt t then LOpt h else if tag_inf t then LInfeasible h else if tag_unb t then LUnbounded else LFail
  | None => lp_solve0 St symset gs a
  end.
