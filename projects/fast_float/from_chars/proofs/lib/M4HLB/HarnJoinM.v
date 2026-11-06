(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import FxLin FxCore FxSound FxMem FxRgs FxFacts FxStep FxSubst FxEnt FxDrv FxCall FxGenA FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require Import FxChain FxChDen FxChEntM FxChSubst FxChMain.
From OSSVerify.Proofs.fast_float.from_chars.lib.M4HLB Require Import HarnLoop HarnJoin HarnJoinN.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Fixpoint coefs_eqb (u v : list (positive * Z)) : bool :=
  match u, v with
  | [], [] => true
  | (_, a) :: u', (_, b) :: v' => (Z.eqb a b && coefs_eqb u' v')%bool
  | _, _ => false
  end.
Definition multi_tups (l0 : lin) (ls : list lin) : list btup :=
  let n := List.length (l_t l0) in
  if (Nat.leb 2 n && forallb (fun l => (Z.eqb (l_c l) (l_c l0) && coefs_eqb (l_t l) (l_t l0))%bool) ls)%bool
  then List.flat_map (fun t => match nth_error (l_t l0) t with
                               | Some (x0, _) =>
                                   let xs := List.map (fun l => match nth_error (l_t l) t with Some (x, _) => (x, 0) | None => (x0, 0) end) ls in
                                   if forallb (fun '(x, _) => Pos.eqb x x0) xs then [] else [(x0, xs)]
                               | None => []
                               end) (List.seq 0 n)
  else [].
Definition cell_mtups (key : positive) (v0 : bval) (cs : list (tree bval)) : list btup :=
  match v0 with
  | BV l0 j0 =>
      match List.fold_right (fun t acc => match tget key t, acc with
                                         | Some (BV l j), Some ls => if Z.eqb j j0 then Some (l :: ls) else None
                                         | _, _ => None end) (Some []) cs with
      | Some ls => multi_tups l0 ls
      | None => []
      end
  | BK _ => []
  end.
Definition mtups_of_cont (c0 : tree bval) (cs : list (tree bval)) (T : list btup) : list btup :=
  List.fold_left (fun acc '(key, v0) => List.fold_left (fun acc' a => add_tup acc' (Some a)) (cell_mtups key v0 cs) acc) (FxCall.telems c0) T.
Fixpoint mtups_of_rgsE (eqs : list bool) (r0 : list region) (rr : list (list region)) (T : list btup) : list btup :=
  match r0 with
  | [] => T
  | R :: r0' => mtups_of_rgsE (List.tl eqs) r0' (List.map (@List.tl region) rr)
                  (if match eqs with b :: _ => b | [] => false end then T else      (* [comment removed for export] *)
                   mtups_of_cont (rg_cont R) (List.map (fun rs => match rs with X :: _ => rg_cont X | [] => TEmpty end) rr) T)
  end.
Definition mtups_of_rgs (r0 : list region) (rr : list (list region)) (T : list btup) : list btup := mtups_of_rgsE (rgs_eqs r0 rr) r0 rr T.

Definition genM (xf : sst -> list lin -> list fact) (L : list (sst * smodel)) (As : list (list lin)) : option (sst * smodel * list lin) :=
  match L with
  | [] => None
  | (F0, M0) :: Lr =>
      let Fr := List.map fst Lr in
      let n0 := List.fold_left (fun n F => Pos.max n (s_next F)) Fr (s_next F0) in
      let T := dedup_tups (F0 :: Fr) (lvar (n0 + 1))
                 (let eqs := rgs_eqs (s_rgs F0) (List.map s_rgs Fr) in
                  mtups_of_rgsE eqs (s_rgs F0) (List.map s_rgs Fr)
                    (tups_of_regs (s_regs F0) (List.map s_regs Fr) 39 (tups_of_rgsE eqs (s_rgs F0) (List.map s_rgs Fr) []))) [] in
      let yb := n0 in
      let nx := (yb + Pos.of_succ_nat (List.length T) + 1)%positive in
      let N := List.map (fun '(k, ((F, M), al)) => let σ := norm_sig T yb k in (ssubstF σ nx F, msubstF σ M, lsubstsF σ al))      (* [comment removed for export] *)
                        (List.combine (List.seq 0 (List.length L)) (List.combine L As)) in
      match genLAF (List.map (fun x => fst x) N) (List.map (fun x => snd x) N) with      (* [comment removed for export] *)
      | Some (P, MP, als) =>
          let Fσ := List.map (fun '((F, M), al) => (F, matchLA F M al P MP als)) (List.combine L As) in
          let oth := List.map (fun x => (s_facts (fst x), snd x)) Fσ in
          let base := match N with x :: _ => s_facts (fst (fst x)) | [] => [] end in
          let cf := List.flat_map (fun f => if all_implyN oth f then [f] else match f with FRange l _ _ => hull_factN oth l | _ => [] end) base in
          let fs := dedupF (List.filter (all_implyN oth) (xf P als ++ s_facts P) ++ cf) in
          Some (SST (s_pc P) (s_regs P) (fix_cellsN P Fσ) fs (s_next P) (s_resv P), MP, als)
      | None => None
      end
  end.
(* [comment removed for export] *)
