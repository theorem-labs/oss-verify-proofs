(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import FxLin FxCore FxSound FxMem FxRgs FxFacts FxStep FxSubst FxEnt FxDrv FxGenA FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require Import FxChain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require Import FxChDen FxChMain.
From OSSVerify.Proofs.fast_float.from_chars.lib.HXH Require Import HxBaseH.
From OSSVerify.Proofs.fast_float.from_chars.lib.HXHB Require Import HxPay.
From OSSVerify.Proofs.fast_float.from_chars.lib.M4HB Require Import HarnKind.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition rk (r : Z) : positive := bv_key (Z_to_bv 5 r).
(* [comment removed for export] *)
Definition psr_keep (RS acc : tree lin) : tree lin :=
  List.fold_left (fun t k => match Prelude.tget k RS with Some l => Prelude.tset k l t | None => t end) [48%positive; 49%positive] acc.
(* [comment removed for export] *)
Fixpoint find_idx (rgs : list region) (a : lin) (i : nat) : option (nat * Z) :=
  match rgs with
  | [] => None
  | R :: rs => match is_const (lsub a (rg_base R)) with
               | Some o => if (Z.leb 0 o && match is_const (rg_size R) with Some n => Z.ltb o n | None => true end)%bool then Some (i, o)
                           else find_idx rs a (S i)
               | None => find_idx rs a (S i)
               end
  end.
(* [comment removed for export] *)
Fixpoint cinter (t u : tree bval) : tree bval :=
  match t with
  | TEmpty => TEmpty
  | TNode l v r =>
      match u with
      | TEmpty => TEmpty
      | TNode ul uv ur => TNode (cinter l ul) (match v, uv with Some x, Some y => if bval_eqb x y then Some x else None | _, _ => None end) (cinter r ur)
      end
  end.
Fixpoint rgs_inter (a b : list region) : list region :=
  match a, b with
  | R :: a', R' :: b' => RG (rg_base R) (rg_size R) (rg_kind R) (cinter (rg_cont R) (rg_cont R')) :: rgs_inter a' b'
  | _, _ => a
  end.
Definition bv8v (l : lin) : list bval := List.map (fun j => BV l (Z.of_nat j)) (seq 0 8).
Definition upd_cont (rgs : list region) (i : nat) (f : tree bval -> tree bval) : list region :=
  map_i (fun j R => if Nat.eqb j i then RG (rg_base R) (rg_size R) (rg_kind R) (f (rg_cont R)) else R) 0 rgs.
(* [comment removed for export] *)
Definition upd_cont_rw (rgs : list region) (i : nat) (f : tree bval -> tree bval) : list region :=
  map_i (fun j R => if Nat.eqb j i then RG (rg_base R) (rg_size R) (match rg_kind R with RZ => RW | k => k end) (f (rg_cont R)) else R) 0 rgs.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition C0B : Z := 128.      (* [comment removed for export] *)
Definition KEPT : list Z := [2; 3; 4; 8; 9; 18; 19; 20; 21; 23; 24; 25; 26; 27].
Fixpoint tregs (RS : tree lin) (n0 : positive) (Zc X RM : lin) (k : nat) (acc : tree lin) : tree lin :=
  match k with
  | O => acc
  | S k' => let key := Pos.of_succ_nat k in
            tregs RS n0 Zc X RM k' (rset acc key (if Nat.eqb k 22 then Zc
                                                  else if Nat.eqb k 10 then X else if Nat.eqb k 13 then RM
                                                  else if existsb (Z.eqb (Z.of_nat k)) KEPT then rget RS key else lvar (n0 + 2 + key)))
  end.

(* [comment removed for export] *)
Definition genCRLSg (g : pgeo) (S F1 : sst) (FS FS1 : fstate) (sh sh1 : shp) : option (sst * positive * fstate * shp * lin) :=
  let n0 := Pos.max (s_next S) (s_next F1) in
  let Zc := lvar n0 in let RM := lvar (n0 + 1) in
  let prov := rget (s_regs S) (rk 20) in let str := rget (s_regs S) (rk 24) in
  match find_cell (s_rgs S) prov, find_cell (s_rgs S) (laddc prov 8), find_idx (s_rgs S) prov 0, find_idx (s_rgs S) (laddc prov 8) 0,
        find_idx (s_rgs S) str 0, (match is_const (rget (s_regs S) (rk 22)) with Some _ => Some C0B | None => None end), find_idx (s_rgs S) (rget (s_regs S) (rk 2)) 0 with
  | Some (_, _, p0), Some (_, _, r0), Some (ip, op), Some (ir, or), Some (is, os), Some c0, Some (isp, osp) =>
      let X := lsub (ladd p0 r0) RM in let K := lsub (lconst c0) Zc in
      let rgs1 := rgs_inter (s_rgs S) (s_rgs F1) in
      let rgs2 := upd_cont rgs1 ip (fun c => put_bytes c op (bv8v X)) in
      let rgs3 := upd_cont rgs2 ir (fun c => put_bytes c or (bv8v RM)) in
      let rgs4 := upd_cont (upd_cont_rw rgs3 is (fun c => put_bytes (havoc_range c (os + 1) (os + 24)) os [BV (lscale 2 K) 0]))
                           isp (fun c => havoc_range c 0 osp) in
      let R := psr_keep (s_regs S) (tregs (s_regs S) n0 (lsub (lconst c0) Zc) X RM 31 TEmpty) in
      let fs := [FRange Zc 1 c0; FRange RM 1 (PAY_HI - 1); FRange (lsub r0 (ladd K RM)) 0 (PAY_HI - 1)] ++ acc_facts g X ++ s_facts S in
      Some (SST (s_pc S) R rgs4 fs (n0 + 40) (s_resv S), n0, FS, sh, Zc)
  | _, _, _, _, _, _, _ => None
  end.
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint tregs0 (RS : tree lin) (n0 : positive) (Zc : lin) (k : nat) (acc : tree lin) : tree lin :=
  match k with
  | O => acc
  | S k' => let key := Pos.of_succ_nat k in
            tregs0 RS n0 Zc k' (rset acc key (if Nat.eqb k 22 then Zc
                                              else if existsb (Z.eqb (Z.of_nat k)) KEPT then rget RS key else lvar (n0 + 2 + key)))
  end.
Definition genCRLS0g (g : pgeo) (S F1 : sst) (FS FS1 : fstate) (sh sh1 : shp) : option (sst * positive * fstate * shp * lin) :=
  let n0 := Pos.max (s_next S) (s_next F1) in
  let Zc := lvar n0 in let RM := lvar (n0 + 1) in
  let prov := rget (s_regs S) (rk 20) in let str := rget (s_regs S) (rk 24) in
  match find_cell (s_rgs S) prov, find_cell (s_rgs S) (laddc prov 8), find_idx (s_rgs S) prov 0, find_idx (s_rgs S) (laddc prov 8) 0,
        find_idx (s_rgs S) str 0, (match is_const (rget (s_regs S) (rk 22)) with Some _ => Some C0B | None => None end), find_idx (s_rgs S) (rget (s_regs S) (rk 2)) 0 with
  | Some (_, _, p0), Some (_, _, r0), Some (ip, op), Some (ir, or), Some (is, os), Some c0, Some (isp, osp) =>
      let X := lsub (ladd p0 r0) RM in let K := lsub (lconst c0) Zc in
      let rgs1 := rgs_inter (s_rgs S) (s_rgs F1) in
      let rgs2 := upd_cont rgs1 ip (fun c => put_bytes c op (bv8v X)) in
      let rgs3 := upd_cont rgs2 ir (fun c => put_bytes c or (bv8v RM)) in
      let rgs4 := upd_cont (upd_cont_rw rgs3 is (fun c => put_bytes (havoc_range c (os + 1) (os + 24)) os [BV (lscale 2 K) 0]))
                           isp (fun c => havoc_range c 0 osp) in
      let R := psr_keep (s_regs S) (tregs0 (s_regs S) n0 (lsub (lconst c0) Zc) 31 TEmpty) in
      let fs := [FRange Zc 1 c0; FRange RM 0 (PAY_HI - 1); FRange (lsub r0 (ladd K RM)) 0 (PAY_HI - 1); FRange (lsub X (pg_P g)) 0 PAY_HI] ++ s_facts S in
      Some (SST (s_pc S) R rgs4 fs (n0 + 40) (s_resv S), n0, FS, sh, Zc)
  | _, _, _, _, _, _, _ => None
  end.

(* [comment removed for export] *)
Definition genCRLSLg (g : pgeo) (S F1 : sst) (FS FS1 : fstate) (sh sh1 : shp) : option (sst * positive * fstate * shp * lin) :=
  let n0 := Pos.max (s_next S) (s_next F1) in
  let Zc := lvar n0 in let RM := lvar (n0 + 1) in
  let prov := rget (s_regs S) (rk 20) in let str := rget (s_regs S) (rk 24) in
  match find_cell (s_rgs S) prov, find_cell (s_rgs S) (laddc prov 8), find_idx (s_rgs S) prov 0, find_idx (s_rgs S) (laddc prov 8) 0,
        find_idx (s_rgs S) str 0, (match is_const (rget (s_regs S) (rk 22)) with Some _ => Some C0B | None => None end), find_idx (s_rgs S) (rget (s_regs S) (rk 2)) 0,
        find_cell (s_rgs S) str, find_cell (s_rgs S) (laddc str 16) with
  | Some (_, _, p0), Some (_, _, r0), Some (ip, op), Some (ir, or), Some (is, os), Some c0, Some (isp, osp), Some (_, _, w0), Some (_, _, pb) =>
      match find_idx (s_rgs S) pb 0 with
      | Some (iu, _) =>
          let X := lsub (ladd p0 r0) RM in let K := lsub (lconst c0) Zc in
          let rgs1 := rgs_inter (s_rgs S) (s_rgs F1) in
          let rgs2 := upd_cont rgs1 ip (fun c => put_bytes c op (bv8v X)) in
          let rgs3 := upd_cont rgs2 ir (fun c => put_bytes c or (bv8v RM)) in
          let rgs4 := upd_cont (upd_cont_rw (upd_cont rgs3 is (fun c => put_bytes c (os + 8) (bv8v K))) iu (fun _ => TEmpty))
                               isp (fun c => havoc_range c 0 osp) in
          let R := psr_keep (s_regs S) (tregs0 (s_regs S) n0 (lsub (lconst c0) Zc) 31 TEmpty) in
          (* [comment removed for export] *)
          let capr := irange (s_facts S) (lsub (laddc w0 (-2)) r0) in
          let capf := if (Z.leb 0 (fst capr) && Z.leb (snd capr) (PAY_HI + 464))%bool then [FRange (lsub (laddc w0 (-2)) (ladd K RM)) 0 (PAY_HI + 464)] else [] in
          let fs := [FRange Zc 1 c0; FRange RM 0 (PAY_HI - 1); FRange (lsub r0 (ladd K RM)) 0 (PAY_HI - 1); FRange (lsub X (pg_P g)) 0 PAY_HI] ++ capf ++ s_facts S in
          Some (SST (s_pc S) R rgs4 fs (n0 + 40) (s_resv S), n0, FS, sh, Zc)
      | None => None
      end
  | _, _, _, _, _, _, _, _, _ => None
  end.
(* [comment removed for export] *)
Definition crls_capsum (S : sst) : option (lin * lin) :=
  let prov := rget (s_regs S) (rk 20) in let str := rget (s_regs S) (rk 24) in
  match find_cell (s_rgs S) str, find_cell (s_rgs S) (laddc str 8), find_cell (s_rgs S) (laddc prov 8) with
  | Some (_, _, w0), Some (_, _, k), Some (_, _, rc) =>
      match l_t rc with
      | [(x, 1)] => Some (lsub (laddc w0 (-2)) (ladd k (lvar x)), lvar x)
      | _ => None
      end
  | _, _, _ => None
  end.


(* [comment removed for export] *)
Definition ent_diag (n0 : positive) (F P : sst) :=
  let σ := match_st F P in
  (List.filter (fun k => negb (lin_eqb (rget (s_regs F) (rk k)) (lsubst σ (rget (s_regs P) (rk k))))) (List.map Z.of_nat (seq 1 31)),
   List.map fst (List.filter (fun '(i, b) => negb b) (combine (seq 0 (List.length (s_rgs P))) (List.map (fun '(R1, R2) => rg_ent R1 R2 σ) (combine (s_rgs F) (s_rgs P))))),
   List.length (s_rgs F), List.length (s_rgs P),
   List.filter (fun f => negb (fact_implied (s_facts F) (fsubst σ f))) (firstn 3 (s_facts P)),
   List.length (List.filter (fun f => negb (fact_implied (s_facts F) (fsubst σ f))) (s_facts P)),
   state_wf P, params_fixed σ (pos_below n0), Pos.leb n0 (s_next P)).
(* [comment removed for export] *)
Fixpoint tlist_acc {A} (t : tree A) (k : positive -> positive) : list (positive * A) :=
  match t with
  | TEmpty => []
  | TNode l None r => tlist_acc l (fun p => k (xO p)) ++ tlist_acc r (fun p => k (xI p))
  | TNode l (Some x) r => (k xH, x) :: tlist_acc l (fun p => k (xO p)) ++ tlist_acc r (fun p => k (xI p))
  end.
Definition tlist {A} (t : tree A) (p : positive) : list (positive * A) := tlist_acc t (fun q => q).
Definition rg_diag (F P : sst) (i : nat) :=
  let σ := match_st F P in
  match nth_error (s_rgs F) i, nth_error (s_rgs P) i with
  | Some RF, Some RP =>
      (rg_base RF, rg_size RF, rg_kind RF, rg_kind RP, lin_eqb (rg_base RF) (lsubst σ (rg_base RP)), lin_eqb (rg_size RF) (lsubst σ (rg_size RP)),
       firstn 12 (List.filter (fun '(p, v, w) => match w with Some w' => negb (bval_eqb (bsubst σ v) w') | None => true end)
         (List.map (fun '(p, v) => (p, v, tget p (rg_cont RF))) (tlist (rg_cont RP) xH))))
  | _, _ => (lconst 0, lconst 0, RO, RO, false, false, [])
  end.
(* [comment removed for export] *)
