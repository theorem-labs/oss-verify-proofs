(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool PrimString Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import FxLin FxCore FxPlan FxLoop FxWorkX.
From OSSVerify.Proofs.fast_float.from_chars.lib.M4X Require Import FxConstGen.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition tok := list Z.
Definition ser (A : Type) := A -> tok -> tok.
Definition des (A : Type) := tok -> option (A * tok).

Definition ser_Z : ser Z := fun z acc => z :: acc.
Definition des_Z : des Z := fun s => match s with z :: r => Some (z, r) | [] => None end.
Definition ser_pos : ser positive := fun p acc => Z.pos p :: acc.
Definition des_pos : des positive := fun s => match s with Z.pos p :: r => Some (p, r) | _ => None end.
Definition ser_nat : ser nat := fun n acc => Z.of_nat n :: acc.
Definition des_nat : des nat := fun s => match s with z :: r => Some (Z.to_nat z, r) | [] => None end.
Definition ser_bool : ser bool := fun b acc => (if b then 1 else 0) :: acc.
Definition des_bool : des bool := fun s => match s with 0 :: r => Some (false, r) | 1 :: r => Some (true, r) | _ => None end.

Definition ser_pair {A B} (f : ser A) (g : ser B) : ser (A * B) := fun '(a, b) acc => f a (g b acc).
Definition des_pair {A B} (f : des A) (g : des B) : des (A * B) :=
  fun s => match f s with Some (a, r) => match g r with Some (b, r') => Some ((a, b), r') | None => None end | None => None end.
Definition ser_opt {A} (f : ser A) : ser (option A) := fun o acc => match o with Some a => 1 :: f a acc | None => 0 :: acc end.
Definition des_opt {A} (f : des A) : des (option A) :=
  fun s => match s with 0 :: r => Some (None, r) | 1 :: r => match f r with Some (a, r') => Some (Some a, r') | None => None end | _ => None end.
Fixpoint ser_els {A} (f : ser A) (l : list A) (acc : tok) : tok := match l with [] => acc | x :: l' => f x (ser_els f l' acc) end.
Definition ser_list {A} (f : ser A) : ser (list A) := fun l acc => Z.of_nat (List.length l) :: ser_els f l acc.
(* [comment removed for export] *)
Fixpoint des_els {A} (f : des A) (n : nat) (s : tok) (racc : list A) : option (list A * tok) :=
  match n with
  | O => Some (List.rev' racc, s)
  | S n' => match f s with Some (a, r) => des_els f n' r (a :: racc) | None => None end
  end.
Definition des_list {A} (f : des A) : des (list A) :=
  fun s => match s with z :: r => des_els f (Z.to_nat z) r [] | [] => None end.
Definition des_map {A B} (f : des A) (g : A -> B) : des B := fun s => match f s with Some (a, r) => Some (g a, r) | None => None end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition sgw (z : Z) : Z := if (Z.leb 9223372036854775808 z && Z.ltb z 18446744073709551616)%bool then z - 18446744073709551616 else z.
Definition usw (z : Z) : Z := if Z.ltb z 0 then z + 18446744073709551616 else z.
Definition ser_lin : ser lin :=
  fun l acc => match l with
               | LIN 0 [(x, 1)] => (- Z.pos x) :: acc
               | LIN c t => Z.of_nat (List.length t) :: sgw c :: ser_els (fun p a => Z.pos (fst p) :: sgw (snd p) :: a) t acc
               end.
Definition des_lin : des lin :=
  fun s => match s with
           | Z.neg x :: r => Some (LIN 0 [(x, 1)], r)
           | n :: c :: r => des_map (fun s' => des_els (des_map (des_pair des_pos des_Z) (fun '(x, k) => (x, usw k))) (Z.to_nat n) s' []) (fun t => LIN (usw c) t) r
           | _ => None
           end.
Definition ser_rkind : ser rkind := fun k acc => (match k with RW => 0 | RO => 1 | RZ => 2 | RI => 3 | RT => 4 end) :: acc.
Definition des_rkind : des rkind :=
  fun s => match s with 0 :: r => Some (RW, r) | 1 :: r => Some (RO, r) | 2 :: r => Some (RZ, r) | 3 :: r => Some (RI, r) | 4 :: r => Some (RT, r) | _ => None end.
Definition ser_bc : ser branch_cond :=
  fun c acc => (match c with BC_EQ => 0 | BC_NE => 1 | BC_LT => 2 | BC_GE => 3 | BC_LTU => 4 | BC_GEU => 5 end) :: acc.
Definition des_bc : des branch_cond :=
  fun s => match s with 0 :: r => Some (BC_EQ, r) | 1 :: r => Some (BC_NE, r) | 2 :: r => Some (BC_LT, r) | 3 :: r => Some (BC_GE, r)
                   | 4 :: r => Some (BC_LTU, r) | 5 :: r => Some (BC_GEU, r) | _ => None end.
Definition ser_fact : ser fact :=
  fun f acc =>
    match f with
    | FCond c a b tk => 0 :: ser_bc c (ser_lin a (ser_lin b (ser_bool tk acc)))
    | FRange l lo hi => 1 :: ser_lin l (lo :: hi :: acc)
    | FMod l k r => 2 :: ser_lin l (k :: r :: acc)
    | FBits l m v => 3 :: ser_lin l (m :: v :: acc)
    | FByte x v j => 4 :: ser_lin x (ser_lin v (j :: acc))
    | FBytes x bs => 5 :: ser_lin x (ser_list (ser_pair ser_lin ser_Z) bs acc)
    end.
Definition des_fact : des fact :=
  fun s =>
    match s with
    | 0 :: r => des_map (des_pair des_bc (des_pair des_lin (des_pair des_lin des_bool))) (fun '(c, (a, (b, tk))) => FCond c a b tk) r
    | 1 :: r => des_map (des_pair des_lin (des_pair des_Z des_Z)) (fun '(l, (lo, hi)) => FRange l lo hi) r
    | 2 :: r => des_map (des_pair des_lin (des_pair des_Z des_Z)) (fun '(l, (k, m)) => FMod l k m) r
    | 3 :: r => des_map (des_pair des_lin (des_pair des_Z des_Z)) (fun '(l, (m, v)) => FBits l m v) r
    | 4 :: r => des_map (des_pair des_lin (des_pair des_lin des_Z)) (fun '(x, (v, j)) => FByte x v j) r
    | 5 :: r => des_map (des_pair des_lin (des_list (des_pair des_lin des_Z))) (fun '(x, bs) => FBytes x bs) r
    | _ => None
    end.
Definition ser_rsv : ser rsv := fun v acc => match v with RNone => 0 :: acc | RAt l => 1 :: ser_lin l acc | RUnk => 2 :: acc end.
Definition des_rsv : des rsv :=
  fun s => match s with 0 :: r => Some (RNone, r) | 1 :: r => des_map des_lin RAt r | 2 :: r => Some (RUnk, r) | _ => None end.
Definition ser_bval : ser bval := fun v acc => match v with BK b => 0 :: b :: acc | BV l j => 1 :: ser_lin l (j :: acc) end.
Definition des_bval : des bval :=
  fun s => match s with 0 :: b :: r => Some (BK b, r) | 1 :: r => des_map (des_pair des_lin des_Z) (fun '(l, j) => BV l j) r | _ => None end.
(* [comment removed for export] *)
Fixpoint ser_tree {A} (f : ser A) (t : tree A) (acc : tok) : tok :=
  match t with
  | TEmpty => 0 :: acc
  | TNode l v r => match v with
                   | None => 1 :: ser_tree f l (ser_tree f r acc)
                   | Some x => 2 :: f x (ser_tree f l (ser_tree f r acc))
                   end
  end.
Fixpoint des_tree {A} (f : des A) (fuel : nat) (s : tok) : option (tree A * tok) :=
  match fuel with
  | O => None
  | S fu =>
      match s with
      | 0 :: r => Some (TEmpty, r)
      | 1 :: r => match des_tree f fu r with
                  | Some (l, r1) => match des_tree f fu r1 with Some (rr, r2) => Some (TNode l None rr, r2) | None => None end
                  | None => None
                  end
      | 2 :: r => match f r with
                  | Some (x, r0) => match des_tree f fu r0 with
                                    | Some (l, r1) => match des_tree f fu r1 with Some (rr, r2) => Some (TNode l (Some x) rr, r2) | None => None end
                                    | None => None
                                    end
                  | None => None
                  end
      | _ => None
      end
  end.
Definition ser_region : ser region :=
  fun R acc => ser_lin (rg_base R) (ser_lin (rg_size R) (ser_rkind (rg_kind R) (ser_tree ser_bval (rg_cont R) acc))).
Definition des_region : des region :=
  des_map (des_pair des_lin (des_pair des_lin (des_pair des_rkind (des_tree des_bval 200)))) (fun '(b, (z, (k, c))) => RG b z k c).

(* [comment removed for export] *)
Definition int_of_digit (d : Z) : int :=
  match d with 0 => 48 | 1 => 49 | 2 => 50 | 3 => 51 | 4 => 52 | 5 => 53 | 6 => 54 | 7 => 55 | 8 => 56 | _ => 57 end%uint63.
(* [comment removed for export] *)
Fixpoint digits (fuel : nat) (z : Z) (acc : list string) : list string :=
  match fuel with
  | O => acc
  | S fu => let acc' := PrimString.make 1 (int_of_digit (z mod 10)) :: acc in
            if z <? 10 then acc' else digits fu (z / 10) acc'
  end.
Definition tok_strs (z : Z) (acc : list string) : list string :=
  if z <? 0 then PrimString.make 1 45%uint63 :: digits 80 (- z) acc else digits 80 z acc.
(* [comment removed for export] *)
Fixpoint cat_pairs (l : list string) : list string :=
  match l with a :: b :: r => PrimString.cat a b :: cat_pairs r | _ => l end.
Fixpoint cat_all (fuel : nat) (l : list string) : string :=
  match fuel with
  | O => ""%pstring
  | S fu => match l with [] => ""%pstring | [a] => a | _ => cat_all fu (cat_pairs l) end
  end.
Definition str_of_toks (ts : tok) : string :=
  cat_all 64 (List.fold_right (fun z acc => tok_strs z (PrimString.make 1 32%uint63 :: acc)) [] ts).

(* [comment removed for export] *)
Definition P18 : Z := 1000000000000000000.
Fixpoint pow10 (n : nat) : Z := match n with O => 1 | S n' => 10 * pow10 n' end.
(* [comment removed for export] *)
Fixpoint toks_loop (fuel : nat) (s : string) (i : int) (hi : option Z) (cur : int) (nd : nat) (neg any : bool) (racc : tok) : tok :=
  let fin (racc : tok) : tok :=
    if any then
      let v := match hi with Some h => h * pow10 nd + Uint63.to_Z cur | None => Uint63.to_Z cur end in
      (if neg then - v else v) :: racc
    else racc in
  match fuel with
  | O => List.rev' (fin racc)
  | S fu =>
      let c := PrimString.get s i in
      if (c =? 32)%uint63 then toks_loop fu s (i + 1)%uint63 None 0%uint63 O false false (fin racc)
      else if (c =? 45)%uint63 then toks_loop fu s (i + 1)%uint63 hi cur nd true any racc
      else
        let d := (c - 48)%uint63 in
        match nd with
        | 18%nat => let h := match hi with Some h => h * P18 + Uint63.to_Z cur | None => Uint63.to_Z cur end in
                    toks_loop fu s (i + 1)%uint63 (Some h) d 1%nat neg true racc
        | _ => toks_loop fu s (i + 1)%uint63 hi (cur * 10 + d)%uint63 (S nd) neg true racc
        end
  end.
Definition toks_of_str (s : string) : tok :=
  toks_loop (Z.to_nat (Uint63.to_Z (PrimString.length s))) s 0%uint63 None 0%uint63 O false false [].

(* [comment removed for export] *)
Fixpoint telems_gd {A} (t : tree A) (k : positive -> positive) (acc : list (positive * A)) : list (positive * A) :=
  match t with
  | TEmpty => acc
  | TNode l v r => telems_gd l (fun p => k (xO p)) (match v with Some x => (k xH, x) :: telems_gd r (fun p => k (xI p)) acc | None => telems_gd r (fun p => k (xI p)) acc end)
  end.
Fixpoint merge_gd {A} (a : list (positive * A)) : list (positive * A) -> list (positive * A) :=
  match a with
  | [] => fun b => b
  | (ka, va) :: a' => fix go (b : list (positive * A)) : list (positive * A) :=
                        match b with
                        | [] => a
                        | (kb, vb) :: b' => if Pos.leb ka kb then (ka, va) :: merge_gd a' b else (kb, vb) :: go b'
                        end
  end.
Fixpoint mpairs_gd {A} (ls : list (list (positive * A))) : list (list (positive * A)) :=
  match ls with a :: b :: r => merge_gd a b :: mpairs_gd r | _ => ls end.
Fixpoint msort_gd {A} (fuel : nat) (ls : list (list (positive * A))) : list (positive * A) :=
  match fuel with O => List.concat ls | S fu => match ls with [] => [] | [a] => a | _ => msort_gd fu (mpairs_gd ls) end end.
Definition sorted_cells (t : tree bval) : list (positive * bval) := msort_gd 64 (List.map (fun x => [x]) (telems_gd t (fun p => p) [])).
Definition ser_cell : ser bval := fun v acc => match v with BK b => (if (Z.leb 0 b && Z.ltb b 256)%bool then b :: acc else 300 :: b :: acc) | BV l j => (256 + j) :: ser_lin l acc end.
Definition des_cell : des bval :=
  fun s => match s with
           | 300 :: b :: r => Some (BK b, r)
           | t :: r => if Z.ltb t 256 then Some (BK t, r) else des_map des_lin (fun l => BV l (t - 256)) r
           | [] => None
           end.
(* [comment removed for export] *)
Fixpoint runs_gd (cs : list (positive * bval)) (start : positive) (last : positive) (racc : list bval) (out : list (positive * list bval)) : list (positive * list bval) :=
  match cs with
  | [] => List.rev' ((start, List.rev' racc) :: out)
  | (k, v) :: r => if Pos.eqb k (Pos.succ last) then runs_gd r start k (v :: racc) out else runs_gd r k k [v] ((start, List.rev' racc) :: out)
  end.
Definition cont_runs (t : tree bval) : list (positive * list bval) :=
  match sorted_cells t with [] => [] | (k, v) :: r => runs_gd r k k [v] [] end.
(* [comment removed for export] *)
Definition is_bv (l : lin) (j : Z) (v : bval) : bool := match v with BV l' j' => (Z.eqb j j' && lin_eqb l l')%bool | BK _ => false end.
Definition word_at (vs : list bval) : option (lin * list bval) :=
  match vs with
  | BV l 0 :: v1 :: v2 :: v3 :: v4 :: v5 :: v6 :: v7 :: r =>
      if (is_bv l 1 v1 && is_bv l 2 v2 && is_bv l 3 v3 && is_bv l 4 v4 && is_bv l 5 v5 && is_bv l 6 v6 && is_bv l 7 v7)%bool then Some (l, r) else None
  | _ => None
  end.
Fixpoint ser_vals (fuel : nat) (vs : list bval) (acc : tok) : tok :=
  match fuel with
  | O => acc
  | S fu => match vs with
            | [] => acc
            | v :: r => match word_at vs with
                        | Some (l, r8) => 264 :: ser_lin l (ser_vals fu r8 acc)
                        | None => ser_cell v (ser_vals fu r acc)
                        end
            end
  end.
Fixpoint des_vals (fuel : nat) (n : nat) (s : tok) (racc : list bval) : option (list bval * tok) :=
  match fuel with
  | O => None
  | S fu => match n with
            | O => Some (List.rev' racc, s)
            | S _ => match s with
                     | 264 :: r => match des_lin r with
                                   | Some (l, r') => des_vals fu (n - 8) r' (BV l 7 :: BV l 6 :: BV l 5 :: BV l 4 :: BV l 3 :: BV l 2 :: BV l 1 :: BV l 0 :: racc)
                                   | None => None
                                   end
                     | _ => match des_cell s with Some (v, r') => des_vals fu (n - 1) r' (v :: racc) | None => None end
                     end
            end
  end.
Definition ser_run : ser (positive * list bval) := fun kr acc => Z.pos (fst kr) :: Z.of_nat (List.length (snd kr)) :: ser_vals (S (List.length (snd kr))) (snd kr) acc.
Definition des_run : des (positive * list bval) :=
  fun s => match s with
           | Z.pos k :: n :: r => des_map (fun s' => des_vals (S (Z.to_nat n)) (Z.to_nat n) s' []) (fun vs => (k, vs)) r
           | _ => None
           end.
Definition ser_cont : ser (tree bval) := fun t acc => ser_list ser_run (cont_runs t) acc.
Fixpoint put_run (t : tree bval) (k : positive) (vs : list bval) : tree bval := match vs with [] => t | v :: r => put_run (tset k v t) (Pos.succ k) r end.
Definition des_cont : des (tree bval) :=
  des_map (des_list des_run) (fun rs => List.fold_left (fun t kr => put_run t (fst kr) (snd kr)) rs TEmpty).
Definition ser_region2 : ser region := fun R acc => ser_lin (rg_base R) (ser_lin (rg_size R) (ser_rkind (rg_kind R) (ser_cont (rg_cont R) acc))).
Definition des_region2 : des region := des_map (des_pair des_lin (des_pair des_lin (des_pair des_rkind des_cont))) (fun '(b, (z, (k, c))) => RG b z k c).

(* [comment removed for export] *)
Definition ser_sst : ser sst :=
  fun St acc => s_pc St :: ser_tree ser_lin (s_regs St) (ser_list ser_region2 (s_rgs St) (ser_list ser_fact (s_facts St) (ser_pos (s_next St) (ser_rsv (s_resv St) acc)))).
Definition des_sst : des sst :=
  des_map (des_pair des_Z (des_pair (des_tree des_lin 200) (des_pair (des_list des_region2) (des_pair (des_list des_fact) (des_pair des_pos des_rsv)))))
          (fun '(pc, (regs, (rgs, (fs, (nx, rv))))) => SST pc regs rgs fs nx rv).
Definition ser_xfact : ser xfact := fun f acc => ser_nat (xf_tag f) (ser_list ser_lin (xf_args f) acc).
Definition des_xfact : des xfact := des_map (des_pair des_nat (des_list des_lin)) (fun '(t, a) => XF t a).
Definition ser_ls : ser loopspec :=
  fun l acc => ser_sst (ls_inv l) (ser_lin (ls_meas l) (ser_list ser_pos (ls_params l) (ser_nat (ls_fuel l) (ser_list ser_Z (ls_stops l) acc)))).
Definition des_ls : des loopspec :=
  des_map (des_pair des_sst (des_pair des_lin (des_pair (des_list des_pos) (des_pair des_nat (des_list des_Z)))))
          (fun '(i, (m, (ps, (fu, st)))) => LS i m ps fu st).
Fixpoint ser_plan (p : plan) (acc : tok) {struct p} : tok :=
  let ser_ks := (fix go (ks : list (Z * plan)) (acc : tok) {struct ks} : tok :=
                   match ks with [] => acc | (z, q) :: r => z :: ser_plan q (go r acc) end) in
  match p with
  | PFin => 0 :: acc
  | PRun fuel stops ks => 1 :: ser_nat fuel (ser_list ser_Z stops (Z.of_nat (List.length ks) :: ser_ks ks acc))
  | PLoop ls ks => 2 :: ser_ls ls (Z.of_nat (List.length ks) :: ser_ks ks acc)
  | PJoin fuel stops jpc pj ks => 3 :: ser_nat fuel (ser_list ser_Z stops (jpc :: ser_plan pj (Z.of_nat (List.length ks) :: ser_ks ks acc)))
  | PLoopW fuel wstops ks => 4 :: ser_nat fuel (ser_list ser_Z wstops (Z.of_nat (List.length ks) :: ser_ks ks acc))
  | PCases x lo hi q => 5 :: ser_lin x (lo :: hi :: ser_plan q acc)
  end.
Fixpoint des_plan (fuel : nat) (s : tok) : option (plan * tok) :=
  match fuel with
  | O => None
  | S fu =>
      let des_ks := des_list (des_pair des_Z (des_plan fu)) in
      match s with
      | 0 :: r => Some (PFin, r)
      | 1 :: r => des_map (des_pair des_nat (des_pair (des_list des_Z) des_ks)) (fun '(f, (st, ks)) => PRun f st ks) r
      | 2 :: r => des_map (des_pair des_ls des_ks) (fun '(l, ks) => PLoop l ks) r
      | 3 :: r => des_map (des_pair des_nat (des_pair (des_list des_Z) (des_pair des_Z (des_pair (des_plan fu) des_ks)))) (fun '(f, (st, (j, (pj, ks)))) => PJoin f st j pj ks) r
      | 4 :: r => des_map (des_pair des_nat (des_pair (des_list des_Z) des_ks)) (fun '(f, (st, ks)) => PLoopW f st ks) r
      | 5 :: r => des_map (des_pair des_lin (des_pair des_Z (des_pair des_Z (des_plan fu)))) (fun '(x, (lo, (hi, q))) => PCases x lo hi q) r
      | _ => None
      end
  end.
Definition ser_gdata : ser gdata :=
  fun '(Ps, ix, pls) acc => ser_list (ser_pair ser_sst (ser_list ser_xfact)) Ps (ser_list ser_nat ix (ser_list ser_plan pls acc)).
Definition des_gdata : des gdata :=
  des_map (des_pair (des_list (des_pair des_sst (des_list des_xfact))) (des_pair (des_list des_nat) (des_list (des_plan 400))))
          (fun '(Ps, (ix, pls)) => (Ps, ix, pls)).
Definition ser_gd : ser (list (option gdata)) := ser_list (ser_opt ser_gdata).
Definition des_gd : des (list (option gdata)) := des_list (des_opt des_gdata).

(* [comment removed for export] *)
Fixpoint chunk_toks (fuel n : nat) (ts : tok) : list tok :=
  match fuel with
  | O => [ts]
  | S fu => match ts with [] => [] | _ => List.firstn n ts :: chunk_toks fu n (List.skipn n ts) end
  end.
Definition GD_CHUNK : nat := 400000.
Definition gd_enc (x : list (option gdata)) : list string := List.map str_of_toks (chunk_toks 100000 GD_CHUNK (ser_gd x [])).
Definition gd_toks (ss : list string) : tok := List.concat (List.map toks_of_str ss).
(* [comment removed for export] *)
Definition gd_dec (ss : list string) : list (option gdata) := match des_gd (gd_toks ss) with Some (x, []) => x | _ => [] end.
Definition gd_ok (ss : list string) : bool := match des_gd (gd_toks ss) with Some (_, []) => true | _ => false end.
