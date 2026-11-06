(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import FxLin FxCore FxSound FxMem FxRgs FxFacts FxStep FxSubst FxEnt FxDrv FxCall FxGenA FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require Import FxChain FxChDen FxChEntM FxChSubst FxChMain.
From OSSVerify.Proofs.fast_float.from_chars.lib.HXH Require Import HxBaseH.
From OSSVerify.Proofs.fast_float.from_chars.lib.M4HB Require Import HarnHintTbl HarnHint HxPChk.
From OSSVerify.Proofs.fast_float.from_chars.lib.M4HLB Require Import HarnLoop HarnSite HarnBudget HarnJoin HarnJoinN HarnJoinM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition has_tvar (nb : positive) (l : lin) : bool := existsb (fun '(x, _) => Pos.leb nb x) (l_t l).
(* [comment removed for export] *)
Definition t_cells (nb : positive) (T : sst) : list (lin * lin) :=
  List.flat_map (fun R => List.flat_map (fun '(key, v) => match v with
                                                          | BV l 0 => if has_tvar nb l then [(laddc (rg_base R) (Zpos key - 1), l)] else []
                                                          | _ => [] end) (FxCall.telems (rg_cont R))) (s_rgs T).
(* [comment removed for export] *)
Definition slot_pairs (nb : positive) (T : sst) (alsT : list lin) (nfix : nat) (P : sst) (alsP : list lin) : list (lin * lin) :=
  List.filter (fun '(lT, lP) => negb (lin_eqb lT lP))
    (List.flat_map (fun '(a, lT) => match cell P a with Some lP => [(lT, lP)] | None => [] end) (t_cells nb T) ++
     List.filter (fun '(lT, _) => has_tvar nb lT) (List.combine (firstn nfix alsT) (firstn nfix alsP))).
Definition delta_lins (prs : list (lin * lin)) : list lin := List.flat_map (fun '(lT, lP) => [lsub lP lT; lsub lT lP]) prs.
(* [comment removed for export] *)
Definition rho_of (nb : positive) (prs : list (lin * lin)) : tree lin :=
  List.fold_left (fun t '(lT, lP) => match l_t lT with
                                     | [(v, 1)] => if Pos.leb nb v then tset v (laddc lP (- l_c lT)) t else t
                                     | _ => t end) prs TEmpty.
Definition transported (T : sst) (ρ : tree lin) : list fact :=
  List.flat_map (fun f => if existsb (fun x => match tget x ρ with Some _ => true | None => false end) (fact_vars f) then [fsubst ρ f] else []) (s_facts T).

(* [comment removed for export] *)
Definition coef_of (x : positive) (l : lin) : Z := match List.filter (fun '(y, _) => Pos.eqb x y) (l_t l) with (_, k) :: _ => k | [] => 0 end.
Definition transported_b (T : sst) (ρ : tree lin) (rv : positive) : list fact :=
  List.flat_map (fun f => match f with
                          | FRange g lo hi =>
                              let D := coef_of rv g in
                              if (Z.ltb 0 D && Z.ltb D 4294967296 && existsb (fun x => match tget x ρ with Some _ => true | None => false end) (fact_vars f))%bool
                              then [FRange (laddc (lsubst ρ g) (- D)) 0 hi] else []
                          | _ => [] end) (s_facts T).
(* [comment removed for export] *)
Definition sgn64z (k : Z) : Z := if Z.ltb k 9223372036854775808 then k else k - 18446744073709551616.
Definition transported_u (T : sst) (ρ : tree lin) (uv : positive) : list fact :=
  List.flat_map (fun f => match f with
                          | FRange g lo hi =>
                              let c := sgn64z (coef_of uv g) in
                              if (negb (Z.eqb c 0) && existsb (fun x => match tget x ρ with Some _ => true | None => false end) (fact_vars f))%bool
                              then [FRange (laddc (lsubst ρ g) c) 0 hi] else []
                          | _ => [] end) (s_facts T).
(* [comment removed for export] *)
Definition hull_small (oth : list (list fact * tree lin)) (l : lin) : list fact :=
  match hull_factN oth l with
  | [FRange g lo hi] => if Z.ltb hi 4611686018427387904 then [FRange g 0 hi] else []      (* [comment removed for export] *)
  | _ => []
  end.
(* [comment removed for export] *)
Fixpoint dedup_tups2 (Fs : list sst) (Y : lin) (T : list btup) (seen : list positive) (seenr : list (list positive)) : list btup :=
  match T with
  | [] => []
  | a :: r =>
      let clash := existsb (fun '(i, (x, _)) => existsb (Pos.eqb x) (nth i seenr [])) (List.combine (List.seq 0 (List.length (snd a))) (snd a)) in
      if existsb (Pos.eqb (fst a)) seen then dedup_tups2 Fs Y r seen seenr
      else if clash then dedup_tups2 Fs Y r seen seenr
      else if tup_ok Fs Y a
           then a :: dedup_tups2 Fs Y r (fst a :: seen)
                       (List.map (fun '(i, (x, _)) => x :: nth i seenr []) (List.combine (List.seq 0 (List.length (snd a))) (snd a)))
           else dedup_tups2 Fs Y r seen seenr
  end.
(* [comment removed for export] *)
Definition selfrel (As : list (list lin)) (als : list lin) : list lin :=
  List.flat_map (fun '(p, lP) =>
      let col := List.map (fun al => nth p al (lconst 0)) As in
      match col with
      | [] => []
      | l0 :: cr => if forallb (lin_eqb l0) cr then []
                    else List.flat_map (fun l => List.flat_map (fun '(g, k) => if Z.eqb k 1 then [lsub lP (lvar g)] else []) (l_t l)) col
      end) (List.combine (List.seq 0 (List.length als)) als).
(* [comment removed for export] *)
Definition factrel (L : list (sst * smodel)) (As : list (list lin)) (als : list lin) : list lin :=
  List.flat_map (fun '(p, lP) =>
      let col := List.map (fun al => nth p al (lconst 0)) As in
      match col with
      | [] => []
      | l0 :: cr => if forallb (lin_eqb l0) cr then []
                    else List.flat_map (fun '((F, _), l) =>
                           match l_t l with
                           | [(z, 1)] => if Z.eqb (l_c l) 0
                                         then List.flat_map (fun f => match f with
                                                                      | FRange g _ _ => match l_t g with
                                                                                        | [(a, ka); (b, kb)] => if ((Pos.eqb a z && Z.eqb ka 1) || (Pos.eqb b z && Z.eqb kb 1))%bool
                                                                                                                then [ladd (lsub g (lvar z)) lP] else []
                                                                                        | _ => [] end
                                                                      | _ => [] end) (s_facts F)
                                         else []
                           | _ => [] end) (List.combine L col)
      end) (List.combine (List.seq 0 (List.length als)) als).
Definition dedupL (l : list lin) : list lin := List.rev (List.fold_left (fun acc x => if existsb (lin_eqb x) acc then acc else x :: acc) l []).
Definition hull_tiny (oth : list (list fact * tree lin)) (l : lin) : list fact :=
  match hull_factN oth l with
  | [FRange g lo hi] => if Z.ltb hi 131072 then [FRange g lo hi] else []
  | _ => []
  end.
(* [comment removed for export] *)
Definition psr_copy (Ns : list sst) (P : sst) : sst :=
  match Ns with
  | [] => P
  | St0 :: Str =>
      let regs := List.fold_left (fun R k => match tget k (s_regs St0) with
                                             | Some l => if forallb (fun St => match tget k (s_regs St) with Some l' => lin_eqb l l' | None => false end) Str then tset k l R else R
                                             | None => R end) PSR_KEYS (s_regs P) in
      SST (s_pc P) regs (s_rgs P) (s_facts P) (s_next P) (s_resv P)
  end.
(* [comment removed for export] *)
Definition genMH_core (m : hmode) (st0 : hst) (xf : sst -> list lin -> list fact) (hl : sst -> list lin -> list lin) (L : list (sst * smodel)) (As : list (list lin))
  : option (sst * smodel * list lin * hst) :=
  match L with
  | [] => None
  | (F0, M0) :: Lr =>
      let Fr := List.map fst Lr in
      let n0 := List.fold_left (fun n F => Pos.max n (s_next F)) Fr (s_next F0) in
      let T := dedup_tups2 (F0 :: Fr) (lvar (n0 + 1))
                 (let eqs := rgs_eqs (s_rgs F0) (List.map s_rgs Fr) in      (* [comment removed for export] *)
                  mtups_of_rgsE eqs (s_rgs F0) (List.map s_rgs Fr)
                    (tups_of_regs (s_regs F0) (List.map s_regs Fr) 39 (tups_of_rgsE eqs (s_rgs F0) (List.map s_rgs Fr) []))) [] [] in
      let yb := n0 in
      let nx := (yb + Pos.of_succ_nat (List.length T) + 1)%positive in
      let N := List.map (fun '(k, ((F, M), al)) => let σ := norm_sig T yb k in (ssubstF σ nx F, msubstF σ M, lsubstsF σ al))      (* [comment removed for export] *)
                        (List.combine (List.seq 0 (List.length L)) (List.combine L As)) in
      match genLAF (List.map (fun x => fst x) N) (List.map (fun x => snd x) N) with      (* [comment removed for export] *)
      | Some (P0, MP, als) =>
          let P := psr_copy (List.map (fun x => fst (fst x)) N) P0 in
          let Fσ := List.map (fun '((F, M), al) => (F, psr_ext F P (matchLA F M al P MP als))) (List.combine L As) in
          let oth := List.map (fun x => (s_facts (fst x), snd x)) Fσ in
          let base := match N with x :: _ => s_facts (fst (fst x)) | [] => [] end in
          let '(cf, st1) := flat_map_h (fun st f => let '(b, st') := ask_b m st (fun _ => all_implyN oth f) in
                                                   if b then ([f], st') else match f with FRange l _ _ => ask_h m st' l (fun _ => hull_factN oth l) | _ => ([], st') end) base st0 in
          (* [comment removed for export] *)
          (* [comment removed for export] *)
          let Pm := SST (s_pc P) (s_regs P) (s_rgs P) (s_facts P ++ cf ++ s_facts F0) (s_next P) (s_resv P) in
          (* [comment removed for export] *)
          let skip (l : lin) : bool :=
            if existsb (fun f => match f with FRange g _ _ => terms_eqb (l_t g) (l_t l) | _ => false end) base
            then match oth with
                 | o0 :: orr => let l0 := lsubst (snd o0) l in forallb (fun o => lin_eqb (lsubst (snd o) l) l0) orr
                 | [] => true end
            else false in
          let '(f1, st2) := filter_h (fun st f => ask_b m st (fun _ => all_implyN oth f)) (xf Pm als ++ s_facts P) st1 in
          let '(f3, st3) := flat_map_h (fun st l => ask_h m st l (fun _ => hull_small oth l)) (List.filter (fun l => negb (skip l)) (dedupL (hl Pm als))) st2 in
          let fs := dedupF (f1 ++ cf ++ f3) in      (* [comment removed for export] *)
          Some (SST (s_pc P) (s_regs P) (fix_cellsN P Fσ) fs (s_next P) (s_resv P), MP, als, st3)
      | None => None
      end
  end.

(* [comment removed for export] *)
Definition hkey_join (L : list (sst * smodel)) : list Z :=
  match L with
  | (F0, _) :: Lr => [1; s_pc F0; Zpos (List.fold_left (fun n F => Pos.max n (s_next (fst F))) Lr (s_next F0)); Z.of_nat (List.length L);
                      Z.of_nat (List.length (s_facts F0)); Z.of_nat (List.length (s_rgs F0))]
  | [] => [1]
  end.
Definition genMH (xf : sst -> list lin -> list fact) (hl : sst -> list lin -> list lin) (L : list (sst * smodel)) (As : list (list lin))
  : option (sst * smodel * list lin) :=
  let real := fun _ : unit => match genMH_core HReal hst0 xf hl L As with Some (P, MP, als, _) => Some (P, MP, als) | None => None end in
  if HINT_REC then
    match genMH_core HRec hst0 xf hl L As with
    | Some (P, MP, als, st) => Some (SST (s_pc P) (s_regs P) (s_rgs P) (s_facts P ++ [hmarker (hkey_join L) st]) (s_next P) (s_resv P), MP, als)
    | None => None
    end
  else if HINT_STRICT then
    match hint_lookup (hkey_join L) with
    | Some (bits, hull) => match genMH_core HReplay (hst_replay bits hull) xf hl L As with
                           | Some (P, MP, als, st) => if hst_done st then Some (P, MP, als) else None      (* [comment removed for export] *)
                           | None => None
                           end
    | None => None      (* [comment removed for export] *)
    end
  else real tt.
(* [comment removed for export] *)
Definition genM2 (xf : sst -> list lin -> list fact) := genMH xf (fun _ _ => []).
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition genREB (nb : positive) (T : sst) (alsT : list lin) (nfix : nat) (rv : positive) (xf : sst -> list lin -> list fact) (hl : sst -> list lin -> list lin) :=
  genMH (fun P als => let prs := slot_pairs nb T alsT nfix P als in let ρ := rho_of nb prs in xf P als ++ transported T ρ ++ transported_b T ρ rv)
        (fun P als => hl P als ++ delta_lins (slot_pairs nb T alsT nfix P als)).
Definition genREU (nb : positive) (T : sst) (alsT : list lin) (nfix : nat) (uv : positive) (xf : sst -> list lin -> list fact) (hl : sst -> list lin -> list lin) :=
  genMH (fun P als => let prs := slot_pairs nb T alsT nfix P als in let ρ := rho_of nb prs in xf P als ++ transported T ρ ++ transported_u T ρ uv)
        (fun P als => hl P als ++ delta_lins (slot_pairs nb T alsT nfix P als)).
Definition genRE (nb : positive) (T : sst) (alsT : list lin) (nfix : nat) (xf : sst -> list lin -> list fact) :=
  genMH (fun P als => let prs := slot_pairs nb T alsT nfix P als in xf P als ++ transported T (rho_of nb prs))
        (fun P als => delta_lins (slot_pairs nb T alsT nfix P als)).

(* [comment removed for export] *)
Definition clean_st (nb : positive) (P : sst) (MP : smodel) (als : list lin) : sst :=
  let keepv := List.map fst (l_t (rU P)) ++ List.map fst (l_t (rC P)) in
  let LS := live_set (SST (s_pc P) (s_regs P) (s_rgs P) [] (s_next P) (s_resv P)) MP FSDone (ShEmit [] 0)
              (List.concat (List.map (fun l => List.map fst (l_t l)) als) ++ keepv) in
  SST (s_pc P) (s_regs P) (s_rgs P)
      (List.filter (fun f => forallb (fun x => if Pos.ltb x nb then true else match tget x LS with Some _ => true | None => false end) (FxChMain.fact_vars f)) (s_facts P))
      (s_next P) (s_resv P).
Definition gclean (nb : positive) (gen : list (sst * smodel) -> list (list lin) -> option (sst * smodel * list lin)) :=
  fun (L : list (sst * smodel)) (As : list (list lin)) => match gen L As with Some (P, MP, als) => Some (clean_st nb P MP als, MP, als) | None => None end.
(* [comment removed for export] *)
