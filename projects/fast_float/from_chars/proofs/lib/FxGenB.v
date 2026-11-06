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
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxDrv FxCall FxWork FxWorkX FxGenA FxGenX.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxMem OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFold OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxRgs OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxImg OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEnt OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxDrv.FxGrow OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxDrv OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCall OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxWork OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxWorkX OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxGenA OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxGenX.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition rjoin_gckb (nin : positive) (anchors : list lin) (fkeys : list positive) (Ls : list sst) : sst :=
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
                        if ((d || existsb (Pos.eqb key) fkeys) && Z.ltb (fst w) 0 && Z.leb (- T48) (fst w) && Z.ltb (snd w) T48)%bool then (key, 2%nat, w)
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
Definition rjoin_r0b (nin : positive) (anchors : list lin) (fkeys : list positive) (rels : list (list (Z * Z))) (Ls : list sst) : sst :=
  let P := rjoin_gckb nin anchors fkeys Ls in
  let rgs := match Ls with L0 :: Lrs => reloc_rgs L0 Lrs (s_regs P) (s_rgs P) | [] => s_rgs P end in
  SST (s_pc P) (s_regs P) rgs (nodup_facts (rel_facts Ls P rels ++ s_facts P)) (s_next P) (s_resv P).
Definition rjoin_rb (nin : positive) (anchors : list lin) (fkeys : list positive) (rels : list (list (Z * Z))) (Ls : list sst) : sst :=
  let P := rjoin_r0b nin anchors fkeys rels Ls in
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
Definition rjoin_reb (nin : positive) (anchors : list lin) (fkeys : list positive) (rels : list (list (Z * Z))) (Ls : list sst) : sst :=
  eq_merge Ls (rjoin_rb nin anchors fkeys rels Ls).
