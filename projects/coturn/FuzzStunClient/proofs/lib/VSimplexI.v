(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Bool.
From Stdlib Require Import Uint63.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import VMap VLin VItv VStore VFarkas.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Unset Lia Cache.
Unset Lia Cache.
Import ListNotations.


Definition LIM : int := 2305843009213693952%uint63.          (* [comment removed for export] *)
Definition ineg (x : int) : int := PrimInt63.sub 0%uint63 x.
Definition iltz (x : int) : bool := PrimInt63.ltsb x 0%uint63.
Definition iabs (x : int) : int := if iltz x then ineg x else x.
Definition ifits (x : int) : bool := PrimInt63.ltb (iabs x) LIM.

(* [comment removed for export] *)
Definition z2i (z : Z) : option int :=
  match z with
  | Z0 => Some 0%uint63
  | Zpos p => if Pos.ltb p 2305843009213693952%positive then Some (Uint63.of_pos p) else None
  | Zneg p => if Pos.ltb p 2305843009213693952%positive then Some (ineg (Uint63.of_pos p)) else None
  end.

(* [comment removed for export] *)
Definition i2pos (x : int) : positive := Z.to_pos (Uint63.to_Z x).

(* [comment removed for export] *)
Definition imul (a b : int) : option int :=
  if PrimInt63.eqb a 1%uint63 then (if ifits b then Some b else None) else
  if PrimInt63.eqb a 9223372036854775807%uint63 then (if ifits b then Some (ineg b) else None) else
  let (h, l) := PrimInt63.mulc (iabs a) (iabs b) in
  if PrimInt63.eqb h 0%uint63 && PrimInt63.ltb l LIM
  then Some (if xorb (iltz a) (iltz b) then ineg l else l) else None.

Definition iadd (a b : int) : option int :=
  let s := PrimInt63.add a b in if ifits s then Some s else None.

(* [comment removed for export] *)
Definition iel (p a t b : int) : option int :=
  match imul p a, imul t b with
  | Some x, Some y => let s := PrimInt63.sub x y in if ifits s then Some s else None
  | _, _ => None
  end.

(* [comment removed for export] *)
Fixpoint igcd_rec (n : nat) (a b : int) : int :=
  match n with
  | O => 1%uint63
  | S n' => if PrimInt63.eqb b 0%uint63 then a else igcd_rec n' b (PrimInt63.mod a b)
  end.
Definition igcd (a b : int) : int := igcd_rec 128 (iabs a) (iabs b).

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition irow := list (int * int).

Fixpoint iget (r : irow) (c : int) : int :=
  match r with
  | [] => 0%uint63
  | (c', v) :: t =>
      if PrimInt63.ltb c' c then iget t c
      else if PrimInt63.eqb c' c then v else 0%uint63
  end.

Fixpoint iscale (k : int) (l : irow) : option irow :=
  match l with
  | [] => Some []
  | (c, v) :: t =>
      match imul k v, iscale k t with
      | Some x, Some t' => Some ((c, x) :: t')
      | _, _ => None
      end
  end.

(* [comment removed for export] *)
Fixpoint imerge (p t : int) (l1 : irow) {struct l1} : irow -> option irow :=
  match l1 with
  | [] => fun l2 => iscale (ineg t) l2
  | (c1, v1) :: t1 =>
      fix aux (l2 : irow) : option irow :=
        match l2 with
        | [] => iscale p l1
        | (c2, v2) :: t2 =>
            if PrimInt63.ltb c1 c2 then
              match imul p v1, imerge p t t1 l2 with
              | Some x, Some r => Some ((c1, x) :: r) | _, _ => None end
            else if PrimInt63.ltb c2 c1 then
              match imul (ineg t) v2, aux t2 with
              | Some x, Some r => Some ((c2, x) :: r) | _, _ => None end
            else
              match iel p v1 t v2, imerge p t t1 t2 with
              | Some x, Some r => if PrimInt63.eqb x 0%uint63 then Some r else Some ((c1, x) :: r)
              | _, _ => None
              end
        end
  end.

Fixpoint irow_gcd (r : irow) (acc : int) : int :=
  match r with
  | [] => acc
  | (_, x) :: t => if PrimInt63.eqb acc 1%uint63 then 1%uint63 else irow_gcd t (igcd x acc)
  end.

Fixpoint irow_div (r : irow) (g : int) : irow :=
  match r with
  | [] => []
  | (c, x) :: t => (c, PrimInt63.divs x g) :: irow_div t g
  end.

Fixpoint irow_remove (r : irow) (c : int) : irow :=
  match r with
  | [] => []
  | (c', v) :: t =>
      if PrimInt63.ltb c' c then (c', v) :: irow_remove t c
      else if PrimInt63.eqb c' c then t else r
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)

Record itrow := mkIRow { ibcol : int ; ients : irow ; irhs : int }.
Record izrow := mkIZ { izc : int ; izents : irow ; izrhs : int }.

Definition ielim_row (p' : int) (pr : irow) (prhs : int) (c : int) (row : itrow) : option itrow :=
  let t := iget (ients row) c in
  if PrimInt63.eqb t 0%uint63 then Some row
  else
    match imerge p' t (ients row) pr, iel p' (irhs row) t prhs with
    | Some e, Some h =>
        if PrimInt63.eqb p' 1%uint63 then Some (mkIRow (ibcol row) e h)
        else
          let g := irow_gcd e (iabs h) in
          if PrimInt63.leb g 1%uint63 then Some (mkIRow (ibcol row) e h)
          else Some (mkIRow (ibcol row) (irow_div e g) (PrimInt63.divs h g))
    | _, _ => None
    end.

Definition ielim_z (p' : int) (pr : irow) (prhs : int) (c : int) (z : izrow) : option izrow :=
  let t := iget (izents z) c in
  if PrimInt63.eqb t 0%uint63 then Some z
  else
    match imerge p' t (izents z) pr, iel p' (izrhs z) t prhs, imul p' (izc z) with
    | Some e, Some h, Some zc' =>
        if PrimInt63.eqb p' 1%uint63 then Some (mkIZ zc' e h)
        else
          let g := irow_gcd e (igcd (iabs h) zc') in
          if PrimInt63.leb g 1%uint63 then Some (mkIZ zc' e h)
          else Some (mkIZ (PrimInt63.divs zc' g) (irow_div e g) (PrimInt63.divs h g))
    | _, _, _ => None
    end.

Fixpoint ielim_all (p' : int) (pr : irow) (prhs : int) (c : int) (l : list itrow) : option (list itrow) :=
  match l with
  | [] => Some []
  | x :: l' => match ielim_row p' pr prhs c x, ielim_all p' pr prhs c l' with
               | Some y, Some l'' => Some (y :: l'') | _, _ => None end
  end.

Fixpoint ipivot_rows (T : list itrow) (r : nat) (c : int) (p' : int) (pr : irow) (prhs : int) : option (list itrow) :=
  match T with
  | [] => Some []
  | row :: t =>
      match r with
      | O => match ielim_all p' pr prhs c t with Some t' => Some (mkIRow c pr prhs :: t') | None => None end
      | S r' =>
          match ielim_row p' pr prhs c row, ipivot_rows t r' c p' pr prhs with
          | Some y, Some t' => Some (y :: t') | _, _ => None
          end
      end
  end.

Definition ipivot (T : list itrow) (z : izrow) (r : nat) (c : int) : option (list itrow * izrow) :=
  let row := nth r T (mkIRow 0%uint63 [] 0%uint63) in
  let p := iget (ients row) c in
  let neg := iltz p in
  let pr := if neg then map (fun cv : int * int => (fst cv, ineg (snd cv))) (ients row) else ients row in
  let prhs := if neg then ineg (irhs row) else irhs row in
  let p' := iabs p in
  match ipivot_rows T r c p' pr prhs, ielim_z p' pr prhs c z with
  | Some T', Some z' => Some (T', z')
  | _, _ => None
  end.

(* [comment removed for export] *)
Fixpoint ifind_entering (e : irow) : option int :=
  match e with
  | [] => None
  | (c, x) :: t => if iltz x then Some c else ifind_entering t
  end.

(* [comment removed for export] *)
Fixpoint ifind_leaving (T : list itrow) (i : nat) (c : int) (best : option (nat * int * int * int)) : option (option nat) :=
  match T with
  | [] => Some (match best with Some (k, _, _, _) => Some k | None => None end)
  | row :: T' =>
      let t := iget (ients row) c in
      if PrimInt63.lesb t 0%uint63 then ifind_leaving T' (S i) c best
      else match best with
           | None => ifind_leaving T' (S i) c (Some (i, ibcol row, irhs row, t))
           | Some (k, bk, rk, tk) =>
               match imul (irhs row) tk, imul rk t with
               | Some l, Some r =>
                   if PrimInt63.ltsb l r then ifind_leaving T' (S i) c (Some (i, ibcol row, irhs row, t))
                   else if PrimInt63.eqb l r then
                     (if PrimInt63.ltb (ibcol row) bk then ifind_leaving T' (S i) c (Some (i, ibcol row, irhs row, t))
                      else ifind_leaving T' (S i) c best)
                   else ifind_leaving T' (S i) c best
               | _, _ => None
               end
           end
  end.

Inductive isresult : Type :=
| ISOpt (T : list itrow) (z : izrow)
| ISUnbounded
| ISFail.

Fixpoint isimplex (fuel : nat) (T : list itrow) (z : izrow) : isresult :=
  match fuel with
  | O => ISFail
  | S fuel' =>
      match ifind_entering (izents z) with
      | None => ISOpt T z
      | Some c =>
          match ifind_leaving T O c None with
          | None => ISFail
          | Some None => ISUnbounded
          | Some (Some r) =>
              match ipivot T z r c with
              | Some (T', z') => isimplex fuel' T' z'
              | None => ISFail
              end
          end
      end
  end.

Definition izrow_init (d : irow) : izrow := mkIZ 1%uint63 (map (fun cv : int * int => (fst cv, ineg (snd cv))) d) 0%uint63.

Fixpoint izrow_elim (T : list itrow) (z : izrow) : option izrow :=
  match T with
  | [] => Some z
  | row :: T' =>
      let b := iget (ients row) (ibcol row) in
      if PrimInt63.lesb b 0%uint63 then izrow_elim T' z
      else match ielim_z b (ients row) (irhs row) (ibcol row) z with
           | Some z' => izrow_elim T' z'
           | None => None
           end
  end.

(* [comment removed for export] *)
Fixpoint ilcm_dens (l : list (N * (int * int))) (acc : int) : option int :=
  match l with
  | [] => Some acc
  | (_, (_, d)) :: t =>
      let g := igcd acc d in
      match imul (PrimInt63.divs acc g) d with
      | Some m => ilcm_dens t m
      | None => None
      end
  end.

Fixpoint iscale_duals (k : int) (l : list (N * (int * int))) : option (list (N * positive)) :=
  match l with
  | [] => Some []
  | (i, (n, d)) :: t =>
      match imul n (PrimInt63.divs k d), iscale_duals k t with
      | Some x, Some t' => Some ((i, i2pos x) :: t')
      | _, _ => None
      end
  end.

Definition iduals_to_hint (zcoef : int) (ds : list (N * int)) : option hint :=
  if PrimInt63.lesb zcoef 0%uint63 then None
  else if existsb (fun d : N * int => iltz (snd d)) ds then None
  else
    let ds := filter (fun d : N * int => PrimInt63.ltsb 0%uint63 (snd d)) ds in
    let fr := map (fun d : N * int => let g := igcd (snd d) zcoef in
                                        (fst d, (PrimInt63.divs (snd d) g, PrimInt63.divs zcoef g))) ds in
    match ilcm_dens fr 1%uint63 with
    | None => None
    | Some k =>
        if PrimInt63.lesb k 0%uint63 then None else
        match iscale_duals k fr with
        | Some lams => Some (HIdx (i2pos k) lams)
        | None => None
        end
    end.

(* [comment removed for export] *)
(* [comment removed for export] *)

Record isymcol := mkISc { isc_col : int ; isc_neg : bool ; isc_col2 : option int ; isc_base : int }.

Record isetup := mkISu { isu_map : pmap isymcol ; isu_next : int ; isu_boxrows : list (int * int) ; isu_relaxed : bool }.

(* [comment removed for export] *)
Definition zsmall (z : Z) : bool := Z.ltb (Z.abs z) 4611686018427387904%Z.          (* [comment removed for export] *)
Definition obz_small (o : option Z) : option Z := match o with Some z => if zsmall z then Some z else None | None => None end.
Definition obz_dropped (o : option Z) : bool := match o with Some z => negb (zsmall z) | None => false end.

Fixpoint isetup_cols (B : box) (syms : list positive) (acc : isetup) : option isetup :=
  match syms with
  | [] => Some acc
  | s :: t =>
      let c := isu_next acc in
      let c1 := PrimInt63.add c 1%uint63 in
      let blo := fst (box_get B s) in let bhi := snd (box_get B s) in
      let rel := orb (isu_relaxed acc) (orb (obz_dropped blo) (obz_dropped bhi)) in
      let r :=
        match (obz_small blo, obz_small bhi) with
        | (Some lo, Some hi) =>
            match z2i lo, z2i (hi - lo)%Z with
            | Some l, Some w => Some (mkISu (pm_set s (mkISc c false None l) (isu_map acc)) c1 ((c, w) :: isu_boxrows acc) rel)
            | _, _ => None
            end
        | (Some lo, None) =>
            match z2i lo with
            | Some l => Some (mkISu (pm_set s (mkISc c false None l) (isu_map acc)) c1 (isu_boxrows acc) rel)
            | None => None
            end
        | (None, Some hi) =>
            match z2i hi with
            | Some h => Some (mkISu (pm_set s (mkISc c true None h) (isu_map acc)) c1 (isu_boxrows acc) rel)
            | None => None
            end
        | (None, None) =>
            Some (mkISu (pm_set s (mkISc c false (Some c1) 0%uint63) (isu_map acc)) (PrimInt63.add c1 1%uint63) (isu_boxrows acc) rel)
        end in
      match r with Some acc' => isetup_cols B t acc' | None => None end
  end.

(* [comment removed for export] *)
Fixpoint iins (c : int) (k : int) (r : irow) : option irow :=
  match r with
  | [] => Some [(c, k)]
  | (c', v) :: t =>
      if PrimInt63.ltb c c' then Some ((c, k) :: r)
      else if PrimInt63.eqb c c' then
        match iadd v k with
        | Some x => if PrimInt63.eqb x 0%uint63 then Some t else Some ((c', x) :: t)
        | None => None
        end
      else match iins c k t with Some t' => Some ((c', v) :: t') | None => None end
  end.

(* [comment removed for export] *)
Fixpoint iterms_cols (wk0 : bool) (mp : pmap isymcol) (l : list term) (acc : irow) (k0 : int) : option (irow * int) :=
  match l with
  | [] => Some (acc, k0)
  | (s, kz) :: t =>
      match pm_get s mp, z2i kz with
      | Some sc, Some k =>
          match iins (isc_col sc) (if isc_neg sc then ineg k else k) acc,
                (if wk0 then imul k (isc_base sc) else Some 0%uint63) with
          | Some acc1, Some kb =>
              match (match isc_col2 sc with None => Some acc1 | Some c2 => iins c2 (ineg k) acc1 end),
                    (if wk0 then iadd k0 kb else Some k0) with
              | Some acc2, Some k0' => iterms_cols wk0 mp t acc2 k0'
              | _, _ => None
              end
          | _, _ => None
          end
      | None, _ => iterms_cols wk0 mp t acc k0
      | _, None => None
      end
  end.

(* [comment removed for export] *)
Fixpoint sumabs (l : list term) : Z := match l with [] => 0%Z | (_, k) :: t => (Z.abs k + sumabs t)%Z end.
Definition droppable (g : lin) : bool := Z.leb (lc g) (- (sumabs (lt g)) * 4611686018427387904)%Z.

Record iprob := mkIProb {
  ipr_T0 : list itrow ; ipr_obj : irow ; ipr_art : int ;
  ipr_gslack : list (N * int) ; ipr_relaxed : bool
}.

Fixpoint ibuild_grows (mp : pmap isymcol) (gs : list (N * lin)) (slack : int) (art : int)
  (accT : list itrow) (accg : list (N * int)) (rel : bool) : option (list itrow * list (N * int) * int * bool) :=
  match gs with
  | [] => Some (accT, accg, slack, rel)
  | (i, g) :: t =>
      match z2i (lc g) with
      | None => if droppable g then ibuild_grows mp t slack art accT accg true else None
      | Some c0 =>
          match iterms_cols true mp (lt g) [] c0 with
          | None => None
          | Some (coefs, k0) =>
              let r := ineg k0 in
              let e := coefs ++ (if iltz r then [(slack, 1%uint63); (art, ineg 1%uint63)] else [(slack, 1%uint63)]) in
              ibuild_grows mp t (PrimInt63.add slack 1%uint63) art (mkIRow slack e r :: accT) ((i, slack) :: accg) rel
          end
      end
  end.

Fixpoint ibuild_brows (brs : list (int * int)) (slack : int) (art : int) (accT : list itrow) : list itrow :=
  match brs with
  | [] => accT
  | (c, r) :: t =>
      let e := (c, 1%uint63) :: (if iltz r then [(slack, 1%uint63); (art, ineg 1%uint63)] else [(slack, 1%uint63)]) in
      ibuild_brows t (PrimInt63.add slack 1%uint63) art (mkIRow slack e r :: accT)
  end.

Definition ilp_setup (St : store) (symset : pmap unit) (gs : list (N * lin)) (a : lin) : option iprob :=
  let syms := map fst (pm_elements symset) in
  match isetup_cols (sbox St) syms (mkISu pm_empty 1%uint63 [] false) with
  | None => None
  | Some su =>
      let n := isu_next su in
      let m := Uint63.of_Z (Z.of_nat (length gs + length (isu_boxrows su))) in
      let art := PrimInt63.add n m in
      match ibuild_grows (isu_map su) gs n art [] [] (isu_relaxed su) with
      | None => None
      | Some (Tg, gsl, slack1, rel) =>
          let Tb := ibuild_brows (isu_boxrows su) slack1 art [] in
          match iterms_cols false (isu_map su) (lt a) [] 0%uint63 with
          | None => None
          | Some (obj, _) => Some (mkIProb (rev_append Tg (rev Tb)) obj art gsl rel)
          end
      end
  end.

Inductive iresult : Type :=
| IOpt (h : hint)
| IInfeasible (h : hint)
| IUnbounded
| IFail.

Fixpoint ifind_row_with_bcol (T : list itrow) (i : nat) (c : int) : option (nat * itrow) :=
  match T with
  | [] => None
  | row :: t => if PrimInt63.eqb (ibcol row) c then Some (i, row) else ifind_row_with_bcol t (S i) c
  end.

Definition iart_pivot_out (T : list itrow) (z : izrow) (art : int) : option (list itrow * izrow) :=
  match ifind_row_with_bcol T O art with
  | None => Some (T, z)
  | Some (r, row) =>
      match find (fun cv : int * int => negb (PrimInt63.eqb (fst cv) art)) (ients row) with
      | None => Some (T, z)
      | Some (j, _) => ipivot T z r j
      end
  end.

Definition iremove_col (T : list itrow) (c : int) : list itrow :=
  map (fun row => mkIRow (ibcol row) (irow_remove (ients row) c) (irhs row)) T.

Fixpoint imost_negative (T : list itrow) (i : nat) (best : option (nat * int)) : option (nat * int) :=
  match T with
  | [] => best
  | row :: t =>
      let best' := if PrimInt63.ltsb (irhs row) (match best with Some (_, b) => b | None => 0%uint63 end)
                   then Some (i, irhs row) else best in
      imost_negative t (S i) best'
  end.

Definition IFUEL : nat := 1000%nat.

Definition ilp_run (pb : iprob) : iresult :=
  let T0 := ipr_T0 pb in let art := ipr_art pb in
  let mk_hint := fun (z : izrow) =>
                   iduals_to_hint (izc z) (map (fun isl : N * int => (fst isl, iget (izents z) (snd isl)))
                                               (ipr_gslack pb)) in
  (* [comment removed for export] *)
  let phase1 : option (list itrow * option izrow) :=
    match imost_negative T0 O None with
    | None => Some (T0, None)
    | Some (r0, _) =>
        let z1 := izrow_init [(art, ineg 1%uint63)] in
        match ipivot T0 z1 r0 art with
        | None => None
        | Some (T1, z1') =>
            match isimplex IFUEL T1 z1' with
            | ISOpt T2 z2 =>
                if iltz (izrhs z2) then Some ([], Some z2)
                else match iart_pivot_out T2 z2 art with
                     | Some (T3, _) => Some (iremove_col T3 art, None)
                     | None => None
                     end
            | _ => None
            end
        end
    end in
  match phase1 with
  | None => IFail
  | Some (_, Some zinf) => match mk_hint zinf with Some h => IInfeasible h | None => IFail end
  | Some (T, None) =>
      match izrow_elim T (izrow_init (ipr_obj pb)) with
      | None => IFail
      | Some z =>
          match isimplex IFUEL T z with
          | ISOpt _ z' => match mk_hint z' with Some h => IOpt h | None => IFail end
          | ISUnbounded => if ipr_relaxed pb then IFail else IUnbounded
          | ISFail => IFail
          end
      end
  end.

Definition ilp_solve (St : store) (symset : pmap unit) (gs : list (N * lin)) (a : lin) : iresult :=
  match ilp_setup St symset gs a with
  | None => IFail
  | Some pb => ilp_run pb
  end.
