(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import FxLin FxCore FxSound FxMem FxRgs FxFacts FxStep FxSubst FxEnt FxDrv FxCall FxGenA FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require Import FxChain FxChDen FxChMain.
From OSSVerify.Proofs.fast_float.from_chars.lib.HXH Require Import HxBaseH.
From OSSVerify.Proofs.fast_float.from_chars.lib.HXHB Require Import HxPay.
From OSSVerify.Proofs.fast_float.from_chars.lib.M4HB Require Import HarnKind HarnLoop.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition dreg : Type := (lin * list lin)%type.    (* [comment removed for export] *)
Fixpoint lall2b (f : lin -> lin -> bool) (a b : list lin) : bool :=
  match a, b with [], [] => true | x :: a', y :: b' => (f x y && lall2b f a' b')%bool | _, _ => false end.
Fixpoint link1 (l0 : lin) (ls : list lin) (ds : list (lin * lin * list lin)) : option lin :=
  match ds with
  | [] => None
  | (V, r0, rs) :: ds' =>
      let try := fun a : Z =>
        let b := lsub l0 (lscale a r0) in
        if lall2b (fun l r => lin_eqb l (ladd (lscale a r) b)) ls rs then Some (ladd (lscale a V) b) else None in
      match try 1 with Some t => Some t | None =>
      match try (-1) with Some t => Some t | None =>
      match try 2 with Some t => Some t | None =>
      match try (-2) with Some t => Some t | None => link1 l0 ls ds' end end end end
  end.
(* [comment removed for export] *)
Definition is_bare (l : lin) : option positive :=
  match l_t l with [(x, 1)] => if Z.eqb (l_c l) 0 then Some x else None | _ => None end.
(* [comment removed for export] *)
Definition is_one (l : lin) : option (positive * Z * Z) :=
  match l_t l with [(x, k)] => Some (x, k, l_c l) | _ => None end.
Definition tform (l0 : lin) (y : positive) : lin := match l_t l0 with [(_, k)] => LIN (l_c l0) [(y, k)] | _ => l0 end.
(* [comment removed for export] *)
Definition btup : Type := (positive * list (positive * Z))%type.
Definition btup_eqb (a b : btup) : bool :=
  (Pos.eqb (fst a) (fst b) && (fix eqs (u v : list (positive * Z)) : bool :=
      match u, v with [], [] => true | (x, s) :: u', (y, t) :: v' => (Pos.eqb x y && Z.eqb s t && eqs u' v')%bool | _, _ => false end) (snd a) (snd b))%bool.
Definition sdiff (c c0 : Z) : Z := let d := (c - c0) mod 18446744073709551616 in if Z.ltb d 9223372036854775808 then d else d - 18446744073709551616.
Definition one_tup (l0 : lin) (ls : list lin) : option btup :=
  match is_one l0 with
  | Some (x0, k0, c0) =>
      match List.fold_right (fun l acc => match is_one l, acc with
                                          | Some (x, k, c), Some xs =>
                                              if Z.eqb k k0 then
                                                if Z.eqb c c0 then Some ((x, 0) :: xs)
                                                else if (Z.ltb 0 k0 && Z.ltb k0 4294967296 && Z.eqb (sdiff c c0 mod k0) 0)%bool then Some ((x, sdiff c c0 / k0) :: xs)
                                                else None
                                              else None
                                          | _, _ => None end) (Some []) ls with
      | Some xs => if forallb (fun '(x, s) => (Pos.eqb x0 x && Z.eqb s 0)%bool) xs then None else Some (x0, xs)
      | None => None
      end
  | None => None
  end.
(* [comment removed for export] *)
Definition bare_tup (key : positive) (v0 : bval) (cs : list (tree bval)) : option btup :=
  match v0 with
  | BV l0 j0 =>
      match List.fold_right (fun t acc => match tget key t, acc with
                                         | Some (BV l j), Some ls => if Z.eqb j j0 then Some (l :: ls) else None
                                         | _, _ => None end) (Some []) cs with
      | Some ls => one_tup l0 ls
      | None => None
      end
  | BK _ => None
  end.
Fixpoint tup_idx (T : list btup) (a : btup) (i : nat) : option nat :=
  match T with [] => None | b :: T' => if btup_eqb a b then Some i else tup_idx T' a (S i) end.
Definition tups_of_cont (c0 : tree bval) (cs : list (tree bval)) (T : list btup) : list btup :=
  List.fold_left (fun acc '(key, v0) => match bare_tup key v0 cs with
                                        | Some a => match tup_idx acc a 0 with Some _ => acc | None => acc ++ [a] end
                                        | None => acc end) (FxCall.telems c0) T.
Definition add_tup (T : list btup) (o : option btup) : list btup :=
  match o with Some a => match tup_idx T a 0 with Some _ => T | None => T ++ [a] end | None => T end.
Definition hd_lin (f : region -> lin) (rs : list region) : lin := match rs with X :: _ => f X | [] => lconst 0 end.
(* [comment removed for export] *)
Fixpoint treq {X} (f : X -> X -> bool) (t u : tree X) : bool :=
  match t, u with
  | TEmpty, TEmpty => true
  | TNode l v r, TNode l' v' r' =>
      if match v, v' with Some x, Some y => f x y | None, None => true | _, _ => false end then (if treq f l l' then treq f r r' else false) else false
  | _, _ => false
  end.
Definition rg_same (R X : region) : bool :=
  if lin_eqb (rg_base R) (rg_base X) then (if lin_eqb (rg_size R) (rg_size X) then treq bval_eqb (rg_cont R) (rg_cont X) else false) else false.
Fixpoint allb_hd (R : region) (rr : list (list region)) : bool :=
  match rr with [] => true | rs :: rr' => match rs with X :: _ => if rg_same R X then allb_hd R rr' else false | [] => false end end.
(* [comment removed for export] *)
Fixpoint rgs_eqs (r0 : list region) (rr : list (list region)) : list bool :=
  match r0 with [] => [] | R :: r0' => allb_hd R rr :: rgs_eqs r0' (List.map (@List.tl region) rr) end.
Fixpoint tups_of_rgsE (eqs : list bool) (r0 : list region) (rr : list (list region)) (T : list btup) : list btup :=
  match r0 with
  | [] => T
  | R :: r0' => tups_of_rgsE (List.tl eqs) r0' (List.map (@List.tl region) rr)
                  (if match eqs with b :: _ => b | [] => false end then T else
                   tups_of_cont (rg_cont R) (List.map (fun rs => match rs with X :: _ => rg_cont X | [] => TEmpty end) rr)
                     (add_tup (add_tup T (one_tup (rg_base R) (List.map (hd_lin rg_base) rr))) (one_tup (rg_size R) (List.map (hd_lin rg_size) rr))))
  end.
Definition tups_of_rgs (r0 : list region) (rr : list (list region)) (T : list btup) : list btup := tups_of_rgsE (rgs_eqs r0 rr) r0 rr T.
(* [comment removed for export] *)
Definition gform (T : list btup) (yb : positive) (l0 : lin) (ls : list lin) : lin :=
  match one_tup l0 ls with
  | Some a => match tup_idx T a 0 with Some i => tform l0 (yb + Pos.of_succ_nat i) | None => l0 end
  | None => l0
  end.

Definition jcont (T : list btup) (yb : positive) (ds : list (lin * lin * list lin)) (c0 : tree bval) (cs : list (tree bval)) : tree bval :=
  List.fold_left (fun acc '(key, v0) =>
      let vs := List.map (fun t => tget key t) cs in
      if forallb (fun o => match o with Some v => bval_eqb v v0 | None => false end) vs then tset key v0 acc
      else match v0 with
           | BV l0 j0 =>
               match List.fold_right (fun o accl => match o, accl with Some (BV l j), Some ls => if Z.eqb j j0 then Some (l :: ls) else None | _, _ => None end) (Some []) vs with
               | Some ls => match link1 l0 ls ds with
                            | Some t => tset key (BV t j0) acc
                            | None => match bare_tup key v0 cs with
                                      | Some a => match tup_idx T a 0 with Some i => tset key (BV (tform l0 (yb + Pos.of_succ_nat i)) j0) acc | None => acc end
                                      | None => acc
                                      end
                            end
               | None => acc
               end
           | BK _ => acc
           end) (FxCall.telems c0) (@TEmpty bval).
Fixpoint jrgs (T : list btup) (yb : positive) (ds : list (lin * lin * list lin)) (r0 : list region) (rr : list (list region)) : list region :=
  match r0 with
  | [] => []
  | R :: r0' => RG (gform T yb (rg_base R) (List.map (hd_lin rg_base) rr)) (gform T yb (rg_size R) (List.map (hd_lin rg_size) rr)) (rg_kind R)
                   (jcont T yb ds (rg_cont R) (List.map (fun rs => match rs with X :: _ => rg_cont X | [] => TEmpty end) rr))
                :: jrgs T yb ds r0' (List.map (@List.tl region) rr)
  end.
(* [comment removed for export] *)
Definition ttab : Type := list (btup * lin).
Definition ren_tmpl (TT : ttab) : tree lin := List.fold_left (fun σ '(a, y) => tset (fst a) y σ) TT (@TEmpty lin).
Definition ren_state (TT : ttab) (k : nat) : tree lin :=
  List.fold_left (fun σ '(a, _) => match nth_error (snd a) k with Some (x, sft) => tset (fst a) (laddc (lvar x) sft) σ | None => σ end) TT (@TEmpty lin).
Definition mentions (TT : ttab) (f : fact) : bool := existsb (fun x => existsb (fun '(a, _) => Pos.eqb x (fst a)) TT) (fact_vars f).
Definition cell_ttab (T : list btup) (yb : positive) : ttab :=
  snd (List.fold_left (fun '(i, acc) a => (S i, acc ++ [(a, lvar (yb + Pos.of_succ_nat i))])) T (O, [])).
Definition reg_ttab (ds : list (lin * lin * list lin)) : ttab :=
  List.flat_map (fun '(V, r0, rs) =>
     match is_bare r0, List.fold_right (fun r acc => match is_bare r, acc with Some x, Some xs => Some (x :: xs) | _, _ => None end) (Some []) rs with
     | Some x0, Some xs => [((x0, List.map (fun x => (x, 0)) xs), V)]
     | _, _ => []
     end) ds.
Fixpoint jregs (T : list btup) (yb : positive) (R0 : tree lin) (Rs : list (tree lin)) (n0 : positive) (k : nat) (acc : tree lin) : tree lin :=
  match k with
  | O => acc
  | S k' => let key := Pos.of_succ_nat k in
            let l0 := rget R0 key in
            jregs T yb R0 Rs n0 k' (rset acc key (if forallb (fun R => lin_eqb (rget R key) l0) Rs then l0
                                                  else match one_tup l0 (List.map (fun R => rget R key) Rs) with
                                                       | Some a => match tup_idx T a 0 with Some i => tform l0 (yb + Pos.of_succ_nat i) | None => lvar (n0 + 1 + key) end
                                                       | None => lvar (n0 + 1 + key)
                                                       end))
  end.
Fixpoint tups_of_regs (R0 : tree lin) (Rs : list (tree lin)) (k : nat) (T : list btup) : list btup :=
  match k with
  | O => T
  | S k' => let key := Pos.of_succ_nat k in
            tups_of_regs R0 Rs k' (add_tup T (one_tup (rget R0 key) (List.map (fun R => rget R key) Rs)))
  end.
(* [comment removed for export] *)
Fixpoint allb {A} (f : A -> bool) (l : list A) : bool := match l with [] => true | x :: r => if f x then allb f r else false end.
Fixpoint anyb {A} (f : A -> bool) (l : list A) : bool := match l with [] => false | x :: r => if f x then true else anyb f r end.
Definition has_fact (fs : list fact) (f : fact) : bool := if anyb (fact_eqb f) fs then true else fact_implied fs f.
Definition genJ (prov : sst -> lin) (g : pgeo) (L : list (sst * smodel)) (als : list (list lin)) : option (sst * smodel * list lin) :=
  match L with
  | [] => None
  | (F0, M0) :: Lr =>
      let Fr := List.map fst Lr in
      let n0 := List.fold_left (fun n F => Pos.max n (s_next F)) Fr (s_next F0) in
      let X := lvar n0 in
      let pv := prov F0 in
      match find_cell (s_rgs F0) pv, find_cell (s_rgs F0) (laddc pv 8), find_idx (s_rgs F0) pv 0, find_idx (s_rgs F0) (laddc pv 8) 0 with
      | Some (_, _, p0), Some (_, _, r0), Some (ip, op), Some (ir, or) =>
          let END := ladd p0 r0 in
          let keys := List.map (fun k => Pos.of_succ_nat k) (seq 1 31) in
          let dks := List.filter (fun key => negb (forallb (fun F => lin_eqb (rget (s_regs F) key) (rget (s_regs F0) key)) Fr)) keys in
          let ds := List.map (fun key => (lvar (n0 + 1 + key), rget (s_regs F0) key, List.map (fun F => rget (s_regs F) key) Fr)) dks in
          let hulls := List.flat_map (fun key =>
                         let rs := List.map (fun F => irange (s_facts F) (rget (s_regs F) key)) (F0 :: Fr) in
                         let lo := List.fold_left Z.min (List.map fst rs) M64 in let hi := List.fold_left Z.max (List.map snd rs) 0 in
                         if (Z.leb lo hi && negb (Z.eqb lo 0 && Z.eqb hi M64))%bool then [FRange (lvar (n0 + 1 + key)) lo hi] else []) dks in
          let T := tups_of_regs (s_regs F0) (List.map s_regs Fr) 31 (tups_of_rgs (s_rgs F0) (List.map s_rgs Fr) []) in
          let yb := (n0 + 40)%positive in
          let rgs1 := jrgs T yb ds (s_rgs F0) (List.map s_rgs Fr) in
          let rgs2 := upd_cont rgs1 ip (fun c => put_bytes c op (bv8v X)) in
          let rgs3 := upd_cont rgs2 ir (fun c => put_bytes c or (bv8v (lsub END X))) in
          let R := jregs T yb (s_regs F0) (List.map s_regs Fr) n0 31 TEmpty in
          let thulls := List.flat_map (fun '(i, a) =>
                         let rs := List.map (fun '(F, (x, sft)) => irange (s_facts F) (laddc (lvar x) sft)) (combine (F0 :: Fr) ((fst a, 0) :: snd a)) in
                         let lo := List.fold_left Z.min (List.map fst rs) M64 in let hi := List.fold_left Z.max (List.map snd rs) 0 in
                         if (Z.leb lo hi && negb (Z.eqb lo 0 && Z.eqb hi M64))%bool then [FRange (lvar (yb + Pos.of_succ_nat i)) lo hi] else [])
                         (combine (seq 0 (List.length T)) T) in
          let fs0 := List.filter (fun f => allb (fun F => has_fact (s_facts F) f) Fr) (s_facts F0) in
          let TT := cell_ttab T yb ++ reg_ttab ds in
          let σT := ren_tmpl TT in
          let fsT := List.map (fsubst σT)
                       (List.filter (fun f => if mentions TT f
                            then allb (fun '(k, F) => has_fact (s_facts F) (fsubst (ren_state TT k) f)) (combine (seq 0 (List.length Fr)) Fr)
                            else false) (s_facts F0)) in
          let fs := [FRange (lsub END X) 0 (PAY_HI - 1); FRange (lsub X (pg_P g)) 0 PAY_HI] ++ hulls ++ thulls ++ fsT ++ fs0 in
          Some (SST (s_pc F0) R rgs3 fs (yb + Pos.of_succ_nat (List.length T) + 1) (s_resv F0), M0, match als with a :: _ => a | [] => [] end)
      | _, _, _, _ => None
      end
  end.

(* [comment removed for export] *)
Definition join_chk (P : sst) (n0 : positive) (L : list (sst * smodel)) : list (bool * bool * bool) :=
  List.map (fun '(F, _) => let σ := match_st F P in (entails F P σ, params_fixed σ (pos_below n0), Pos.leb (s_next F) n0)) L.
(* [comment removed for export] *)
