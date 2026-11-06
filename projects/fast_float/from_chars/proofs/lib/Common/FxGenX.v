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
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxDrv FxCall FxWork FxWorkX FxGenA.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxMem OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFold OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxRgs OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxImg OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEnt OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxDrv.FxGrow OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxDrv OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCall OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxWork OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxWorkX OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxGenA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition find_reg (L0 : sst) (a : lin) : option positive := List.find (fun k => lin_eqb (rget (s_regs L0) k) a) keys31.
Definition reloc_xf (P L0 : sst) (f : xfact) : xfact :=
  XF (xf_tag f) (List.map (fun a => match find_reg L0 a with Some k => rget (s_regs P) k | None => a end) (xf_args f)).
Definition nodup_x (fs : list xfact) : list xfact :=
  List.rev (List.fold_left (fun acc f => if existsb (xf_eqb f) acc then acc else f :: acc) fs []).
(* [comment removed for export] *)
Definition xjoin_facts (P : sst) (Xs : list xst) : list xfact :=
  match Xs with
  | [] => []
  | X0 :: _ =>
      List.filter (fun f => forallb (fun X => let σ := match_st (xs_st X) P in existsb (xf_eqb (xsubst σ f)) (xs_x X)) Xs)
                  (nodup_x (List.map (reloc_xf P (xs_st X0)) (xs_x X0) ++ xs_x X0))
  end.
(* [comment removed for export] *)
Definition rkx (k : Z) : positive := bv_key (Z_to_bv 5 k).
Definition rcombo (R : tree lin) (c : list (Z * Z)) : lin :=
  List.fold_left (fun acc '(k, a) => ladd acc (lscale a (rget R (rkx k)))) c (lconst 0).
Definition rel_facts (Ls : list sst) (P : sst) (rels : list (list (Z * Z))) : list fact :=
  List.flat_map (fun c => let r := hull_dir Ls (fun L => rcombo (s_regs L) c) in
                          if good48 r then [FRange (rcombo (s_regs P) c) (fst r) (snd r)] else []) rels.
(* [comment removed for export] *)
Definition reloc_cont (L0 : sst) (Lrs : list sst) (R : tree lin) (i : nat) (c : tree bval) : tree bval :=
  match nth_error (s_rgs L0) i with
  | None => c
  | Some RL0 =>
      put_list c (List.flat_map (fun '(p, v) =>
         match tget p c, v with
         | Some _, _ => []
         | None, BV l j =>
             (* [comment removed for export] *)
             let ok := fun k => forallb (fun L => match nth_error (s_rgs L) i with
                                                  | Some RL => match tget p (rg_cont RL) with
                                                               | Some (BV l' j') => (lin_eqb l' (rget (s_regs L) k) && Z.eqb j' j)%bool
                                                               | _ => false end
                                                  | None => false end) Lrs in
             match List.find (fun k => (lin_eqb (rget (s_regs L0) k) l && ok k)%bool) keys31 with
             | Some k => [(p, BV (rget R k) j)]
             | None => []
             end
         | None, BK _ => []
         end) (telems (rg_cont RL0)))
  end.
Definition reloc_rgs (L0 : sst) (Lrs : list sst) (R : tree lin) (rgs : list region) : list region :=
  map_i (fun i Rg => RG (rg_base Rg) (rg_size Rg) (rg_kind Rg) (reloc_cont L0 Lrs R i (rg_cont Rg))) 0 rgs.
Definition rjoin_r0 (nin : positive) (anchors : list lin) (fkeys : list positive) (rels : list (list (Z * Z))) (Ls : list sst) : sst :=
  let P := rjoin_gck nin anchors fkeys Ls in
  let rgs := match Ls with L0 :: Lrs => reloc_rgs L0 Lrs (s_regs P) (s_rgs P) | [] => s_rgs P end in
  SST (s_pc P) (s_regs P) rgs (nodup_facts (rel_facts Ls P rels ++ s_facts P)) (s_next P) (s_resv P).
(* [comment removed for export] *)
Definition bv_at (L : sst) (i : nat) (p : positive) : option (lin * Z) :=
  match nth_error (s_rgs L) i with
  | Some R => match tget p (rg_cont R) with Some (BV l j) => Some (l, j) | _ => None end
  | None => None
  end.
Fixpoint tup_eqb (a b : list lin) : bool :=
  match a, b with [], [] => true | x :: a', y :: b' => (lin_eqb x y && tup_eqb a' b')%bool | _, _ => false end.
Fixpoint tup_find (acc : list (list lin * positive)) (t : list lin) : option positive :=
  match acc with [] => None | (t', x) :: acc' => if tup_eqb t t' then Some x else tup_find acc' t end.
Definition cell_hull_facts (Ls : list sst) (t : list lin) (anchors : list lin) (X : lin) : list fact :=
  let r0 := List.fold_left (fun r '(L, l) => let r' := irange (s_facts L) l in (Z.min (fst r) (fst r'), Z.max (snd r) (snd r')))
                           (combine Ls t) (T48, -1) in
  (if Z.ltb (snd r0 - fst r0) T48 then [FRange X (fst r0) (snd r0)] else []) ++
  List.flat_map (fun a => let r := List.fold_left (fun r '(L, l) => let r' := irange (s_facts L) (lsub l a) in
                                                                   (Z.min (fst r) (fst r'), Z.max (snd r) (snd r')))
                                                  (combine Ls t) (T48, -1) in
                          if (Z.leb 0 (fst r) && Z.ltb (snd r - fst r) 4096)%bool then [FRange (lsub X a) (fst r) (snd r)] else []) anchors.
Definition rjoin_r (nin : positive) (anchors : list lin) (fkeys : list positive) (rels : list (list (Z * Z))) (Ls : list sst) : sst :=
  let P := rjoin_r0 nin anchors fkeys rels Ls in
  match Ls with
  | [] => P
  | L0 :: _ =>
      (* [comment removed for export] *)
      let cands := List.flat_map (fun '(i, RL0) =>
                     match nth_error (s_rgs P) i with
                     | Some RP => List.flat_map (fun '(p, v) =>
                                    match tget p (rg_cont RP), v with
                                    | None, BV _ j =>
                                        let ts := List.map (fun L => bv_at L i p) Ls in
                                        if forallb (fun o => match o with Some (_, j') => Z.eqb j' j | None => false end) ts
                                        then [(i, p, j, List.map (fun o => match o with Some (l, _) => l | None => lconst 0 end) ts)] else []
                                    | _, _ => []
                                    end) (telems (rg_cont RL0))
                     | None => []
                     end) (combine (seq 0 (List.length (s_rgs L0))) (s_rgs L0)) in
      let '(asg, n1) := List.fold_left (fun '(acc, n) '(_, _, _, t) =>
                          match tup_find acc t with Some _ => (acc, n) | None => ((t, n) :: acc, Pos.succ n) end) cands ([], s_next P) in
      let rgs := map_i (fun i R => RG (rg_base R) (rg_size R) (rg_kind R)
                   (put_list (rg_cont R) (List.flat_map (fun '(i', p, j, t) => if Nat.eqb i' i then
                                            match tup_find asg t with Some x => [(p, BV (lvar x) j)] | None => [] end else []) cands))) 0 (s_rgs P) in
      let fs := List.flat_map (fun '(t, x) => cell_hull_facts Ls t anchors (lvar x)) asg in
      SST (s_pc P) (s_regs P) rgs (fs ++ s_facts P) n1 (s_resv P)
  end.
(* [comment removed for export] *)
Definition eq_merge (Ls : list sst) (P : sst) : sst :=
  let eqk := fun key => List.find (fun k1 => (Pos.ltb k1 key && forallb (fun L => lin_eqb (rget (s_regs L) k1) (rget (s_regs L) key)) Ls)%bool) keys31 in
  let R := List.fold_left (fun acc key => match eqk key with Some k1 => rset acc key (rget acc k1) | None => acc end) keys31 (s_regs P) in
  let live := live_vars R (s_rgs P) in
  let dead := List.filter (fun y => negb (existsb (Pos.eqb y) live)) (List.flat_map (fun key => lvars (rget (s_regs P) key)) keys31) in
  SST (s_pc P) R (s_rgs P) (List.filter (fun f => forallb (fun y => negb (existsb (Pos.eqb y) dead)) (fact_vars f)) (s_facts P)) (s_next P) (s_resv P).
Definition rjoin_re (nin : positive) (anchors : list lin) (fkeys : list positive) (rels : list (list (Z * Z))) (Ls : list sst) : sst :=
  eq_merge Ls (rjoin_r nin anchors fkeys rels Ls).
(* [comment removed for export] *)
Definition xjoin (mk : list sst -> sst) (g : sst -> plan) : xaction :=
  XGenTs (fun here => let P := mk (List.map xs_st here) in ([(P, xjoin_facts P here)], List.repeat 0%nat (List.length here))) g.
(* [comment removed for export] *)
Fixpoint keys_of (key : sst -> Z) (Ls : list sst) (acc : list Z) : list Z :=
  match Ls with
  | [] => List.rev acc
  | L :: Ls' => keys_of key Ls' (if existsb (Z.eqb (key L)) acc then acc else key L :: acc)
  end.
Fixpoint idx_of (ks : list Z) (k : Z) : nat := match ks with [] => 0%nat | k0 :: ks' => if Z.eqb k0 k then 0%nat else S (idx_of ks' k) end.
Definition xjoin_part (key : sst -> Z) (mk : list sst -> sst) (g : sst -> plan) : xaction :=
  XGenTs (fun here =>
            let ks := keys_of key (List.map xs_st here) [] in
            let Ps := List.map (fun k => let grp := List.filter (fun X => Z.eqb (key (xs_st X)) k) here in
                                         let P := mk (List.map xs_st grp) in (P, xjoin_facts P grp)) ks in
            (Ps, List.map (fun X => idx_of ks (key (xs_st X))) here)) g.
(* [comment removed for export] *)
Definition xjoin_each (mk : list sst -> sst) (g : sst -> plan) : xaction :=
  XGenTs (fun here => (List.map (fun X => let P := mk [xs_st X] in (P, xjoin_facts P [X])) here, seq 0 (List.length here))) g.

(* [comment removed for export] *)
Inductive xres : Type :=
| XOk (pc : Z) (nhere : nat) (nnew : nat) (npend : nat)
| XFail (pc : Z) (nhere : nat) (why : nat)       (* [comment removed for export] *)
| XSkip (pc : Z).
Fixpoint wtracex (t : tree xi) (img : tree Z) (ins : list positive) (depth : nat) (s0 : sst) (nodes : list (Z * xaction)) (pend : list xst)
  : list xres * list xst :=
  match nodes with
  | [] => ([], pend)
  | (pc, a) :: rest =>
      let here := List.filter (fun X => Z.eqb (s_pc (xs_st X)) pc) pend in
      let others := List.filter (fun X => negb (Z.eqb (s_pc (xs_st X)) pc)) pend in
      match here with
      | [] => let '(r, p) := wtracex t img ins depth s0 rest others in (XSkip pc :: r, p)
      | _ :: _ =>
          let go := fun f => let '(r, p) := wtracex t img ins depth s0 rest (others ++ f) in
                             (XOk pc (List.length here) (List.length f) (List.length (others ++ f)) :: r, p) in
          match a with
          | XGenTs mk g =>
              let '(Ps, ix) := mk here in
              if ent_ix ins Ps here ix then
                match xchecks t img depth s0 g Ps with Some f => go f | None => ([XFail pc (List.length here) 2], here) end
              else ([XFail pc (List.length here) 1], here)
          | XCall c => match xcalls c here with Some ks => go ks | None => ([XFail pc (List.length here) 3], here) end
          | XCallK c => match xcalls c here with Some ks => go ks | None => ([XFail pc (List.length here) 3], here) end
          | XCallKs cs => match xcallsm cs here with Some ks => go ks | None => ([XFail pc (List.length here) 3], here) end
          | XFragK c pcQ => match xfrags c pcQ here with Some ks => go ks | None => ([XFail pc (List.length here) 3], here) end
          | XFragKs cs pcQ => match xfragsm cs pcQ here with Some ks => go ks | None => ([XFail pc (List.length here) 3], here) end
          | XHand f => match xhands f here with Some ks => go ks | None => ([XFail pc (List.length here) 4], here) end
          end
      end
  end.
Definition wtstartx (t : tree xi) (img : tree Z) (ins : list positive) (depth : nat) (s0 : sst) (p0 : plan) (nodes : list (Z * xaction))
  : list xres * list xst :=
  match check t img ins depth p0 s0 with Some f => wtracex t img ins depth s0 nodes (List.map (fun K => XST K []) f) | None => ([XFail 0 0 2], []) end.
Fixpoint count_pcsx (l : list xst) (acc : list (Z * nat)) : list (Z * nat) :=
  match l with
  | [] => acc
  | X :: l' => count_pcsx l' (let fix ins (a : list (Z * nat)) := match a with
                                                                | [] => [(s_pc (xs_st X), 1%nat)]
                                                                | (p, n) :: a' => if Z.eqb p (s_pc (xs_st X)) then (p, S n) :: a' else (p, n) :: ins a'
                                                                end in ins acc)
  end.
