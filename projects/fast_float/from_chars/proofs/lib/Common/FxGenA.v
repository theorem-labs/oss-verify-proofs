(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLin FxCore FxSound FxMem FxFold FxRgs FxFacts FxImg FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSubst FxEnt FxLoop FxPlan FxFrame.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxDrv.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxDrv FxCall FxWork.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxMem OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFold OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxRgs OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxImg OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEnt OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxDrv.FxGrow OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxDrv OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCall OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxWork.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition T48 : Z := 281474976710656.
Definition good48 (r : Z * Z) : bool := (Z.leb 0 (fst r) && Z.ltb (snd r) T48)%bool.
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition irange_pre (fs : list fact) (l : lin) : Z * Z := ne_int_fixl fs fs l (lround fs l (rel_iv fs fs l (l_iv fs l))).
Definition near48 (r : Z * Z) : bool := (Z.leb (- 1048576) (fst r) && Z.ltb (snd r) T48)%bool.
(* [comment removed for export] *)
Definition irange_pv (fs : list fact) (l : lin) : (Z * Z) * (Z * Z) :=
  match is_const l with
  | Some c => ((c, c), (c, c))
  | None => let v := ne_int_fixl fs fs l (lround fs l (rel_iv fs fs l (l_iv fs l))) in
            let r := ne_refine' fs l (wrap_iv v) in
            let a := lalign fs l in ((if Z.ltb 0 a then align_iv a r else r), v)
  end.
(* [comment removed for export] *)
Definition hull_dir (Ls : list sst) (f : sst -> lin) : Z * Z :=
  let rs := List.map (fun L => let '(r, v) := irange_pv (s_facts L) (f L) in (L, r, v)) Ls in
  if forallb (fun '(_, r, v) => (good48 r || near48 v)%bool) rs then
    List.fold_left (fun acc '(L, r, v) => let r' := if good48 r then r else irange_x (s_facts L) (f L) in
                                         (Z.min (fst acc) (fst r'), Z.max (snd acc) (snd r'))) rs (T48, -1)
  else (-1, -1).
(* [comment removed for export] *)
Definition hull_anchor (Ls : list sst) (key : positive) (X a : lin) : list fact :=
  let r1 := hull_dir Ls (fun L => lsub (rget (s_regs L) key) a) in
  if good48 r1 then [FRange (lsub X a) (fst r1) (snd r1)]
  else let r2 := hull_dir Ls (fun L => lsub a (rget (s_regs L) key)) in
       if good48 r2 then [FRange (lsub a X) (fst r2) (snd r2)] else [].
(* [comment removed for export] *)
Definition hull_abs (Ls : list sst) (key : positive) (X : lin) : list fact :=
  match Ls with
  | [] => []
  | L0 :: Lrs =>
      let r := List.fold_left (fun r L => let r' := irange (s_facts L) (rget (s_regs L) key) in
                                           (Z.min (fst r) (fst r'), Z.max (snd r) (snd r'))) Lrs (irange (s_facts L0) (rget (s_regs L0) key)) in
      if (Z.eqb (fst r) 0 && Z.eqb (snd r) M64)%bool then
        let w := List.fold_left (fun r L => let r' := irange_pre (s_facts L) (rget (s_regs L) key) in
                                             (Z.min (fst r) (fst r'), Z.max (snd r) (snd r'))) Lrs (irange_pre (s_facts L0) (rget (s_regs L0) key)) in
        if (Z.ltb (fst w) 0 && Z.leb (- T48) (fst w) && Z.ltb (snd w) T48)%bool then [FRange (laddc X (- fst w)) 0 (snd w - fst w)] else []
      else [FRange X (fst r) (snd r)]
  end.
Definition keys31 : list positive := List.map Pos.of_succ_nat (seq 1 31).
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition lvars (l : lin) : list positive := List.map fst (l_t l).
Definition bval_vars (v : bval) : list positive := match v with BK _ => [] | BV l _ => lvars l end.
Definition fact_vars (f : fact) : list positive :=
  match f with
  | FCond _ a b _ => lvars a ++ lvars b
  | FRange l _ _ | FMod l _ _ | FBits l _ _ => lvars l
  | FByte x v _ => lvars x ++ lvars v
  | FBytes x bs => lvars x ++ List.flat_map (fun '(l, _) => lvars l) bs
  end.
Definition live_vars (R : tree lin) (rgs : list region) : list positive :=
  List.flat_map (fun key => lvars (rget R key)) keys31 ++
  List.flat_map (fun R => lvars (rg_base R) ++ lvars (rg_size R) ++ List.flat_map (fun '(_, v) => bval_vars v) (telems (rg_cont R))) rgs.
Definition gc_facts (nin : positive) (live : list positive) (fs : list fact) : list fact :=
  List.filter (fun f => forallb (fun y => (Pos.ltb y nin || existsb (Pos.eqb y) live)%bool) (fact_vars f)) fs.
(* [comment removed for export] *)
Definition ptr_like (avs : list positive) (fs : list fact) (v : lin) : bool :=
  match l_t v with
  | [] => false
  | _ => existsb (fun f => let vs := fact_vars f in
                           (existsb (fun y => existsb (Pos.eqb y) avs) vs && existsb (fun y => existsb (Pos.eqb y) (lvars v)) vs)%bool) fs
  end.
Definition reg_anchors (anchors : list lin) (L0 : sst) (Lrs : list sst) : list lin :=
  let avs := List.flat_map lvars anchors in
  List.fold_left (fun acc key =>
     let v := rget (s_regs L0) key in
     if (forallb (fun L => lin_eqb (rget (s_regs L) key) v) Lrs && ptr_like avs (s_facts L0) v
         && negb (existsb (lin_eqb v) anchors) && negb (existsb (lin_eqb v) acc))%bool
     then acc ++ [v] else acc) keys31 [].
(* [comment removed for export] *)
Definition nodup_facts (fs : list fact) : list fact :=
  List.rev (List.fold_left (fun acc f => if existsb (fact_eqb f) acc then acc else f :: acc) fs []).
(* [comment removed for export] *)
Definition key_hull (Ls : list sst) (key : positive) : Z * Z :=
  match Ls with
  | [] => (0, M64)
  | L0 :: Lrs => List.fold_left (fun r L => let r' := irange (s_facts L) (rget (s_regs L) key) in (Z.min (fst r) (fst r'), Z.max (snd r) (snd r')))
                                Lrs (irange (s_facts L0) (rget (s_regs L0) key))
  end.
Definition key_whull (Ls : list sst) (key : positive) : Z * Z :=
  match Ls with
  | [] => (0, M64)
  | L0 :: Lrs => List.fold_left (fun r L => let r' := irange_pre (s_facts L) (rget (s_regs L) key) in (Z.min (fst r) (fst r'), Z.max (snd r) (snd r')))
                                Lrs (irange_pre (s_facts L0) (rget (s_regs L0) key))
  end.
(* [comment removed for export] *)
Definition key_hulls (Ls : list sst) (key : positive) : (Z * Z) * (Z * Z) :=
  match Ls with
  | [] => ((0, M64), (0, M64))
  | L0 :: Lrs => List.fold_left (fun '(r, w) L => let '(r', w') := irange_pv (s_facts L) (rget (s_regs L) key) in
                                   ((Z.min (fst r) (fst r'), Z.max (snd r) (snd r')), (Z.min (fst w) (fst w'), Z.max (snd w) (snd w'))))
                                Lrs (irange_pv (s_facts L0) (rget (s_regs L0) key))
  end.
(* [comment removed for export] *)
Definition rjoin_gck (nin : positive) (anchors : list lin) (fkeys : list positive) (Ls : list sst) : sst :=
  match Ls with
  | [] => SST 0 TEmpty [] [] 1 RNone
  | L0 :: Lrs =>
      let n0 := max_next Lrs (s_next L0) in
      let info := List.map (fun key =>
                    let v0 := rget (s_regs L0) key in
                    let d := negb (forallb (fun L => lin_eqb (rget (s_regs L) key) v0) Lrs) in
                    match l_t v0, d with
                    | [], false => (key, 0%nat, (0, 0))
                    | _ :: _ :: _, false => (key, 0%nat, (0, 0))   (* [comment removed for export] *)
                    | _, _ =>
                        let '(r, w) := key_hulls Ls key in
                        if (Z.ltb (fst w) 0 && Z.leb (- T48) (fst w) && Z.ltb (snd w) T48)%bool then (key, 2%nat, w)
                        else
                          if (Z.eqb (fst r) 0 && Z.eqb (snd r) M64)%bool then (key, if d then 1%nat else 0%nat, r)
                          else (key, if (d || existsb (Pos.eqb key) fkeys)%bool then 1%nat else 3%nat, r)
                    end) keys31 in
      let X := fun key => lvar (n0 + key) in
      let ranc := reg_anchors anchors L0 Lrs in
      let avs := List.flat_map lvars anchors in
      let R := List.fold_left (fun acc '(key, mode, w) =>
                 rset acc key (match mode with
                               | 2%nat => laddc (X key) (fst w)
                               | 1%nat => X key
                               | _ => rget (s_regs L0) key
                               end)) info TEmpty in
      let gf := List.flat_map (fun '(key, mode, w) =>
                  match mode with
                  | 2%nat => [FRange (X key) 0 (snd w - fst w)]
                  | 1%nat => (if (Z.eqb (fst w) 0 && Z.eqb (snd w) M64)%bool then [] else [FRange (X key) (fst w) (snd w)])
                             ++ (if ptr_like avs (s_facts L0) (rget (s_regs L0) key)
                                 then List.flat_map (hull_anchor Ls key (X key)) (anchors ++ ranc) else [])
                  | 3%nat => [FRange (rget (s_regs L0) key) (fst w) (snd w)]
                  | _ => []
                  end) info in
      let common := List.fold_left (fun fs L => List.filter (fun f => existsb (fact_eqb f) (s_facts L)) fs) Lrs (s_facts L0) in
      let rgs := gen_rgs (s_rgs L0) (List.map s_rgs Lrs) in
      SST (s_pc L0) R rgs (nodup_facts (gf ++ gc_facts nin (live_vars R rgs) common)) (n0 + 33)
          (if forallb (fun L => rsv_eqb (s_resv L) (s_resv L0)) Lrs then s_resv L0 else RUnk)
  end.
(* [comment removed for export] *)
Definition rjoin_gc (nin : positive) (anchors : list lin) (Ls : list sst) : sst := rjoin_gck nin anchors [] Ls.
Definition rjoin (anchors : list lin) (Ls : list sst) : sst :=
  match Ls with
  | [] => SST 0 TEmpty [] [] 1 RNone
  | L0 :: Lrs =>
      let n0 := max_next Lrs (s_next L0) in
      let diff := List.filter (fun key => negb (forallb (fun L => lin_eqb (rget (s_regs L) key) (rget (s_regs L0) key)) Lrs)) keys31 in
      let gf := List.flat_map (fun key => let X := lvar (n0 + key) in hull_abs Ls key X ++ List.flat_map (hull_anchor Ls key X) anchors) diff in
      let common := List.fold_left (fun fs L => List.filter (fun f => existsb (fact_eqb f) (s_facts L)) fs) Lrs (s_facts L0) in
      SST (s_pc L0) (gen_regs_n Lrs (s_regs L0) n0 31 TEmpty) (gen_rgs (s_rgs L0) (List.map s_rgs Lrs)) (gf ++ common) (n0 + 33)
          (if forallb (fun L => rsv_eqb (s_resv L) (s_resv L0)) Lrs then s_resv L0 else RUnk)
  end.

(* [comment removed for export] *)
Definition aloop (t : tree xi) (img : tree Z) (anchors : list lin) (fuel : nat) (stops : list Z) (P : sst) : plan :=
  let backs := List.filter (fun L => Z.eqb (s_pc L) (s_pc P)) (fx_explore t img fuel (s_pc P :: stops) P []) in
  let n0 := max_next backs (s_next P) in
  let deltas := List.map (fun key => (key, common_delta P backs key)) rkeys in
  let same := List.filter (fun key => forallb (fun B => lin_eqb (rget (s_regs B) key) (rget (s_regs P) key)) backs) rkeys in
  (* [comment removed for export] *)
  let cmpe := fun (z : positive) (dz : Z) (e : positive) => forallb (fun B => let zv := rget (s_regs B) z in let ev := rget (s_regs B) e in
               let zp := laddc zv (- dz) in   (* [comment removed for export] *)
               existsb (fun f => match f with
                                 | FCond _ a b _ => ((lin_eqb a zv && lin_eqb b ev) || (lin_eqb a ev && lin_eqb b zv)
                                                     || (lin_eqb a zp && lin_eqb b ev) || (lin_eqb a ev && lin_eqb b zp))%bool
                                 | _ => false end) (s_facts B)) backs in
  (* [comment removed for export] *)
  let cand := List.flat_map (fun '(z, od) => match od with
                 | Some dz => if Z.ltb 0 dz then
                                List.flat_map (fun e => let r := irange (s_facts P) (lsub (rget (s_regs P) e) (rget (s_regs P) z)) in
                                                        if (Z.leb 0 (fst r) && Z.leb (snd r) (2 ^ 48) && negb (Pos.eqb e z))%bool
                                                        then [(z, dz, rget (s_regs P) e, fst r, snd r, cmpe z dz e)] else []) same
                                ++ List.flat_map (fun '(k, odk) => match odk with
                                                  | Some dk => if (Z.eqb dk (- dz) && negb (Pos.eqb k z))%bool then
                                                                 let r := irange (s_facts P) (rget (s_regs P) k) in
                                                                 if (Z.leb 0 (fst r) && Z.leb (snd r) (2 ^ 48))%bool
                                                                 then [(z, dz, ladd (rget (s_regs P) z) (rget (s_regs P) k), fst r, snd r, true)] else []
                                                               else []
                                                  | None => [] end) deltas
                              else []
                 | None => [] end) deltas in
  let cand1 := List.filter (fun '(_, dz, _, _, hi, _) => Z.leb dz hi) cand in
  let cand2 := match List.filter (fun '(_, _, _, _, _, c) => c) cand1 with [] => cand1 | l => l end in
  let cand' := List.fold_left (fun acc c => match acc with
                                            | [] => [c]
                                            | (_, _, _, _, h0, _) :: _ => let '(_, _, _, _, h, _) := c in if Z.ltb h0 h then [c] else acc
                                            end) cand2 [] in
  match backs, cand' with
  | [], _ => PRun fuel stops []
  | _, [] => PLoopW fuel stops []
  | _, (z, dz, Ev, lo, hi, _) :: _ =>
      let X := lvar (n0 + z) in let z0 := rget (s_regs P) z in
      (* [comment removed for export] *)
      let regsb := fun (bad : list positive) => List.fold_left (fun acc '(key, od) =>
                    let v := rget (s_regs P) key in
                    rset acc key (if existsb (Pos.eqb key) same then v
                                  else if Pos.eqb key z then X
                                  else if existsb (Pos.eqb key) bad then lvar (n0 + key)
                                  else match od with
                                       | Some d => if Z.eqb (Z.rem d dz) 0 then ladd v (lscale (Z.quot d dz) (lsub X z0)) else lvar (n0 + key)
                                       | None => lvar (n0 + key)
                                       end)) deltas TEmpty in
      let af := List.flat_map (fun a => let r := irange (s_facts P) (lsub z0 a) in
                                        if (Z.leb 0 (fst r) && Z.ltb (snd r) T48)%bool then [FRange (lsub X a) (fst r) T48] else [])
                              (anchors ++ reg_anchors anchors P backs) in
      let rw := irange (s_facts P) (lsub Ev z0) in
      let lo := Z.max lo (fst rw) in
      (* [comment removed for export] *)
      let uf := List.flat_map (fun a => if lin_eqb a Ev then [] else
                                        let r := irange (s_facts P) (lsub a Ev) in let r0 := irange (s_facts P) (lsub a z0) in
                                        if (Z.leb 0 (fst r) && Z.ltb (snd r) T48 && Z.ltb (snd r0) T48)%bool then [FRange (lsub a X) 0 (snd r0)] else [])
                              (anchors ++ reg_anchors anchors P backs) in
      let invb := fun bad => SST (s_pc P) (regsb bad) (gen_rgs (s_rgs P) (List.map s_rgs backs)) (FRange (lsub Ev X) lo hi :: af ++ uf ++ s_facts P) (n0 + 33)
                     (if forallb (fun B => rsv_eqb (s_resv B) (s_resv P)) backs then s_resv P else RUnk) in
      let inv1 := invb [] in
      let backs1 := List.filter (fun L => Z.eqb (s_pc L) (s_pc P)) (fx_explore t img fuel (s_pc P :: stops) inv1 []) in
      let bad := List.filter (fun key => negb (forallb (fun B => let σ := match_st B inv1 in
                                                                 lin_eqb (rget (s_regs B) key) (lsubst σ (rget (s_regs inv1) key))) backs1)) rkeys in
      let inv := match bad with [] => inv1 | _ => invb bad end in
      PLoop (LS inv (lsub Ev X) (vars_below (s_next P)) fuel stops) []
  end.

(* [comment removed for export] *)
Definition gloop (t : tree xi) (img : tree Z) (ks kp : positive) (e : lin) (ganchors panchors : list lin) (fuel : nat) (stops : list Z) (P : sst) : plan :=
  let backs := List.filter (fun L => Z.eqb (s_pc L) (s_pc P)) (fx_explore t img fuel (s_pc P :: stops) P []) in
  let n0 := max_next backs (s_next P) in
  let deltas := List.map (fun key => (key, common_delta P backs key)) rkeys in
  let same := List.filter (fun key => forallb (fun B => lin_eqb (rget (s_regs B) key) (rget (s_regs P) key)) backs) rkeys in
  let G := lvar (n0 + ks) in let z0 := rget (s_regs P) ks in
  let regs := List.fold_left (fun acc '(key, od) =>
                let v := rget (s_regs P) key in
                rset acc key (if existsb (Pos.eqb key) same then v
                              else if Pos.eqb key ks then G
                              else match od with
                                   | Some d => ladd v (lscale d (lsub G z0))
                                   | None => lvar (n0 + key)
                                   end)) deltas TEmpty in
  let p := rget regs kp in
  let rw := irange (s_facts P) (lsub e (rget (s_regs P) kp)) in
  let gf := List.flat_map (fun a => let r1 := irange (s_facts P) (lsub z0 a) in let r2 := irange (s_facts P) (lsub a z0) in
                             (if (Z.leb 0 (fst r1) && Z.ltb (snd r1) T48)%bool then [FRange (lsub G a) (fst r1) T48] else []) ++
                             (if (Z.leb 0 (fst r2) && Z.ltb (snd r2) T48)%bool then [FRange (lsub a G) (fst r2) (snd r2)] else [])) ganchors in
  (* [comment removed for export] *)
  let p0 := rget (s_regs P) kp in
  let pf := List.flat_map (fun a => let r1 := irange (s_facts P) (lsub p0 a) in
                             if (Z.leb 0 (fst r1) && Z.ltb (snd r1) T48)%bool then [FRange (lsub p a) (fst r1) T48] else [])
                 (panchors ++ reg_anchors panchors P backs) in
  let inv := SST (s_pc P) regs (gen_rgs (s_rgs P) (List.map s_rgs backs)) (FRange (lsub e p) (fst rw) (snd rw) :: gf ++ pf ++ s_facts P) (n0 + 33)
                 (if forallb (fun B => rsv_eqb (s_resv B) (s_resv P)) backs then s_resv P else RUnk) in
  match backs with
  | [] => PRun fuel stops []
  | _ => PLoop (LS inv (lsub e p) (vars_below (s_next P)) fuel stops) []
  end.

(* [comment removed for export] *)
Definition gloopc (t : tree xi) (img : tree Z) (ks kp kc : positive) (e : lin) (ganchors panchors : list lin) (fuel : nat) (stops : list Z) (P : sst) : plan :=
  match gloop t img ks kp e ganchors panchors fuel stops P with
  | PLoop (LS inv meas ins fl st) rest =>
      let rk0 := irange (s_facts P) (rget (s_regs P) kc) in
      let G := rget (s_regs inv) ks in
      (* [comment removed for export] *)
      let rev := fun f => match f with FRange l _ _ => existsb (fun a => lin_eqb l (lsub a G)) ganchors | _ => false end in
      let facts' := match s_facts inv with
                    | f0 :: fs => f0 :: FRange (rget (s_regs inv) kc) 1 (snd rk0) :: List.filter (fun f => negb (rev f)) fs
                    | fs => fs
                    end in
      PLoop (LS (SST (s_pc inv) (s_regs inv) (s_rgs inv) facts' (s_next inv) (s_resv inv)) (rget (s_regs inv) kc) ins fl st) rest
  | pl => pl
  end.

(* [comment removed for export] *)
Definition cloop (t : tree xi) (img : tree Z) (kc : positive) (up : bool) (panchors : list lin) (fuel : nat) (stops : list Z) (P : sst) : plan :=
  let backs := List.filter (fun L => Z.eqb (s_pc L) (s_pc P)) (fx_explore t img fuel (s_pc P :: stops) P []) in
  let n0 := max_next backs (s_next P) in
  let deltas := List.map (fun key => (key, common_delta P backs key)) rkeys in
  let same := List.filter (fun key => forallb (fun B => lin_eqb (rget (s_regs B) key) (rget (s_regs P) key)) backs) rkeys in
  let K := lvar (n0 + 40) in
  let regs := List.fold_left (fun acc '(key, od) =>
                let v := rget (s_regs P) key in
                rset acc key (if existsb (Pos.eqb key) same then v
                              else match od with Some d => ladd v (lscale d K) | None => lvar (n0 + key) end)) deltas TEmpty in
  let msr := fun (R : tree lin) => if up then lscale (-1) (rget R kc) else rget R kc in
  let hk := snd (irange (s_facts P) (msr (s_regs P))) in
  let pf := List.flat_map (fun key =>
              if existsb (Pos.eqb key) same then [] else
              let v := rget (s_regs P) key in
              List.flat_map (fun a => let r := irange (s_facts P) (lsub v a) in
                                      (* [comment removed for export] *)
                                      if (Z.leb 0 (fst r) && Z.leb (snd r) 4096)%bool then [FRange (lsub (rget regs key) a) (fst r) T48] else [])
                            panchors) rkeys in
  let inv := SST (s_pc P) regs (gen_rgs (s_rgs P) (List.map s_rgs backs)) (FRange (msr regs) 1 hk :: FRange K 0 T48 :: pf ++ s_facts P)
                 (n0 + 41) (if forallb (fun B => rsv_eqb (s_resv B) (s_resv P)) backs then s_resv P else RUnk) in
  match backs with
  | [] => PRun fuel stops []
  | _ => PLoop (LS inv (msr regs) (vars_below (s_next P)) fuel stops) []
  end.

(* [comment removed for export] *)
Definition cloopf (t : tree xi) (img : tree Z) (mform : list (Z * Z)) (mc : Z) (panchors : list lin) (fuel : nat) (stops : list Z) (P : sst) : plan :=
  let backs := List.filter (fun L => Z.eqb (s_pc L) (s_pc P)) (fx_explore t img fuel (s_pc P :: stops) P []) in
  let n0 := max_next backs (s_next P) in
  let deltas := List.map (fun key => (key, common_delta P backs key)) rkeys in
  let same := List.filter (fun key => forallb (fun B => lin_eqb (rget (s_regs B) key) (rget (s_regs P) key)) backs) rkeys in
  let K := lvar (n0 + 40) in
  let regs := List.fold_left (fun acc '(key, od) =>
                let v := rget (s_regs P) key in
                rset acc key (if existsb (Pos.eqb key) same then v
                              else match od with Some d => ladd v (lscale d K) | None => lvar (n0 + key) end)) deltas TEmpty in
  let msr := fun (R : tree lin) => List.fold_left (fun acc '(r, c) => ladd acc (lscale c (rget R (bv_key (Z_to_bv 5 r))))) mform (lconst mc) in
  let hk := snd (irange (s_facts P) (msr (s_regs P))) in
  let pf := List.flat_map (fun '(key, od) =>
              if existsb (Pos.eqb key) same then [] else
              match od with None => [] | Some _ =>     (* [comment removed for export] *)
              let v := rget (s_regs P) key in
              List.flat_map (fun a => let r := irange (s_facts P) (lsub v a) in
                                      if (Z.leb 0 (fst r) && Z.leb (snd r) 4096)%bool then [FRange (lsub (rget regs key) a) (fst r) T48] else [])
                            panchors end) deltas in
  let inv := SST (s_pc P) regs (gen_rgs (s_rgs P) (List.map s_rgs backs)) (FRange (msr regs) 1 hk :: FRange K 0 T48 :: pf ++ s_facts P)
                 (n0 + 41) (if forallb (fun B => rsv_eqb (s_resv B) (s_resv P)) backs then s_resv P else RUnk) in
  match backs with
  | [] => PRun fuel stops []
  | _ => PLoop (LS inv (msr regs) (vars_below (s_next P)) fuel stops) []
  end.

(* [comment removed for export] *)
Definition cloopg (t : tree xi) (img : tree Z) (msrf : sst -> tree lin -> lin) (panchors : list lin) (fuel : nat) (stops : list Z) (P : sst) : plan :=
  let backs := List.filter (fun L => Z.eqb (s_pc L) (s_pc P)) (fx_explore t img fuel (s_pc P :: stops) P []) in
  let n0 := max_next backs (s_next P) in
  let deltas := List.map (fun key => (key, common_delta P backs key)) rkeys in
  let same := List.filter (fun key => forallb (fun B => lin_eqb (rget (s_regs B) key) (rget (s_regs P) key)) backs) rkeys in
  let K := lvar (n0 + 40) in
  (* [comment removed for export] *)
  let regsb := fun (bad : list positive) => List.fold_left (fun acc '(key, od) =>
                let v := rget (s_regs P) key in
                rset acc key (if existsb (Pos.eqb key) bad then lvar (n0 + key)
                              else if existsb (Pos.eqb key) same then v
                              else match od with Some d => ladd v (lscale d K) | None => lvar (n0 + key) end)) deltas TEmpty in
  let msr := msrf P in
  let hk := snd (irange (s_facts P) (msr (s_regs P))) in
  let pf := fun (bad : list positive) => List.flat_map (fun '(key, od) =>
              if (existsb (Pos.eqb key) same || existsb (Pos.eqb key) bad)%bool then [] else
              match od with None => [] | Some _ =>
              let v := rget (s_regs P) key in
              List.flat_map (fun a => let r := irange (s_facts P) (lsub v a) in
                                      if (Z.leb 0 (fst r) && Z.leb (snd r) 4096)%bool then [FRange (lsub (rget (regsb bad) key) a) (fst r) T48] else [])
                            panchors end) deltas in
  let invb := fun (bad : list positive) =>
                SST (s_pc P) (regsb bad) (gen_rgs (s_rgs P) (List.map s_rgs backs)) (FRange (msr (regsb bad)) 1 hk :: FRange K 0 T48 :: pf bad ++ s_facts P)
                    (n0 + 41) (if forallb (fun B => rsv_eqb (s_resv B) (s_resv P)) backs then s_resv P else RUnk) in
  let inv1 := invb [] in
  let backs1 := List.filter (fun L => Z.eqb (s_pc L) (s_pc P)) (fx_explore t img fuel (s_pc P :: stops) inv1 []) in
  let bad := List.filter (fun key => negb (forallb (fun B => let σ := match_st B inv1 in
                                                             lin_eqb (rget (s_regs B) key) (lsubst σ (rget (s_regs inv1) key))) backs1)) rkeys in
  let inv := match bad with [] => inv1 | _ => invb bad end in
  match backs with
  | [] => PRun fuel stops []
  | _ => PLoop (LS inv (msr (s_regs inv)) (vars_below (s_next P)) fuel stops) []
  end.

(* [comment removed for export] *)
Definition cloopt (t : tree xi) (img : tree Z) (kc : positive) (panchors : list lin) (fuel : nat) (stops : list Z) (P : sst) : plan :=
  let backs := List.filter (fun L => Z.eqb (s_pc L) (s_pc P)) (fx_explore t img fuel (s_pc P :: stops) P []) in
  let n0 := max_next backs (s_next P) in
  let deltas := List.map (fun key => (key, common_delta P backs key)) rkeys in
  let same := List.filter (fun key => forallb (fun B => lin_eqb (rget (s_regs B) key) (rget (s_regs P) key)) backs) rkeys in
  let K := lvar (n0 + 40) in
  let regsb := fun (bad : list positive) => List.fold_left (fun acc '(key, od) =>
                let v := rget (s_regs P) key in
                rset acc key (if existsb (Pos.eqb key) bad then lvar (n0 + key)
                              else if existsb (Pos.eqb key) same then v
                              else match od with Some d => ladd v (lscale d K) | None => lvar (n0 + key) end)) deltas TEmpty in
  let hk := snd (irange (s_facts P) (rget (s_regs P) kc)) in
  let pf := fun (bad : list positive) => List.flat_map (fun '(key, od) =>
              if (existsb (Pos.eqb key) same || existsb (Pos.eqb key) bad)%bool then [] else
              match od with None => [] | Some _ =>
              let v := rget (s_regs P) key in
              List.flat_map (fun a => let r := irange (s_facts P) (lsub v a) in
                                      if (Z.leb 0 (fst r) && Z.leb (snd r) 4096)%bool then [FRange (lsub (rget (regsb bad) key) a) (fst r) T48] else [])
                            panchors end) deltas in
  let invb := fun (bad : list positive) =>
                SST (s_pc P) (regsb bad) (gen_rgs (s_rgs P) (List.map s_rgs backs)) (FRange (rget (regsb bad) kc) 0 hk :: FRange K 0 T48 :: pf bad ++ s_facts P)
                    (n0 + 41) (if forallb (fun B => rsv_eqb (s_resv B) (s_resv P)) backs then s_resv P else RUnk) in
  let inv1 := invb [] in
  let backs1 := List.filter (fun L => Z.eqb (s_pc L) (s_pc P)) (fx_explore t img fuel (s_pc P :: stops) inv1 []) in
  let bad := List.filter (fun key => negb (forallb (fun B => let σ := match_st B inv1 in
                                                             lin_eqb (rget (s_regs B) key) (lsubst σ (rget (s_regs inv1) key))) backs1)) rkeys in
  let inv := match bad with [] => inv1 | _ => invb bad end in
  match backs with
  | [] => PRun fuel stops []
  | _ => PLoop (LS inv (laddc (rget (s_regs inv) kc) 1) (vars_below (s_next P)) fuel stops) []
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition csub_win (c : tree bval) (o n : Z) : tree bval :=
  put_list TEmpty (List.flat_map (fun '(p, v) => let j := Zpos p - 1 in if (Z.leb o j && Z.ltb j (o + n))%bool then [(okey (j - o), v)] else [])
                                 (telems c)).
Definition view_rg (L : sst) (v : vop) (n : Z) (k : rkind) : region :=
  match v with
  | VCopy i => nth i (s_rgs L) (RGz (lconst 0) 0 RW TEmpty)
  | VSub i o => let R := nth i (s_rgs L) (RGz (lconst 0) 0 RW TEmpty) in RG (laddc (rg_base R) o) (lconst n) k (csub_win (rg_cont R) o n)
  end.
Definition views_of (specs : list (vop * Z * rkind)) (L : sst) : list region := List.map (fun '(v, n, k) => view_rg L v n k) specs.
Definition mk_csite (P0 Q : sst) (keep qk : list positive) (specs : list (vop * Z * rkind)) : csite :=
  CSite P0 Q keep qk (List.map (fun '(v, _, _) => v) specs) (views_of specs).
