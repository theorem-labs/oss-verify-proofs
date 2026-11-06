(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import FxLin FxCore FxSound FxMem FxRgs FxFacts FxStep FxSubst FxEnt FxDrv FxCall FxGenA FxLoop FxPlan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require Import FxChain FxChDen FxChEntM FxChSubst FxChMain.
From OSSVerify.Proofs.fast_float.from_chars.lib.M4HLB Require Import HarnLoop HarnJoin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition tup_sig (a : btup) (Y : lin) (k : nat) : tree lin :=
  match k with
  | O => tset (fst a) Y TEmpty
  | Datatypes.S k' => match nth_error (snd a) k' with Some (x, sft) => tset x (laddc Y (- sft)) TEmpty | None => TEmpty end
  end.
(* [comment removed for export] *)
Definition pos_lins (F : sst) : list lin :=
  List.map (fun k => rget (s_regs F) (Pos.of_succ_nat k)) (seq 1 31) ++ List.map rg_base (s_rgs F) ++ List.map rg_size (s_rgs F).
Definition hd0 (l : list lin) : lin := match l with x :: _ => x | [] => lconst 0 end.
(* [comment removed for export] *)
Fixpoint cols_ok (P0 : list lin) (Pr : list (list lin)) (Q0 : list lin) (Qr : list (list lin)) : bool :=
  match P0, Q0 with
  | x :: P0t, y :: Q0t =>
      if (if forallb (fun l => lin_eqb x (hd0 l)) Pr then forallb (fun l => lin_eqb y (hd0 l)) Qr else true)
      then cols_ok P0t (List.map (@List.tl lin) Pr) Q0t (List.map (@List.tl lin) Qr) else false
  | _, _ => true
  end.
Definition tup_ok (Fs : list sst) (Y : lin) (a : btup) : bool :=
  match List.map pos_lins Fs with
  | [] => false
  | P0 :: Pr =>
      let Q := List.map (fun '(k, P) => List.map (lsubst (tup_sig a Y k)) P) (List.combine (seq 0 (List.length Fs)) (P0 :: Pr)) in
      match Q with Q0 :: Qr => cols_ok P0 Pr Q0 Qr | [] => false end
  end.
(* [comment removed for export] *)
Fixpoint dedup_tups (Fs : list sst) (Y : lin) (T : list btup) (seen : list positive) : list btup :=
  match T with
  | [] => []
  | a :: r => if existsb (Pos.eqb (fst a)) seen then dedup_tups Fs Y r seen
              else if tup_ok Fs Y a then a :: dedup_tups Fs Y r (fst a :: seen) else dedup_tups Fs Y r seen
  end.
(* [comment removed for export] *)
Definition lin_bound (σ : tree lin) (l : lin) : bool := existsb (fun p => match tget (fst p) σ with Some _ => true | None => false end) (l_t l).
Definition lsubstF (σ : tree lin) (l : lin) : lin := if lin_bound σ l then lsubst σ l else l.
Definition bsubstF (σ : tree lin) (v : bval) : bval := match v with BK _ => v | BV l j => if lin_bound σ l then BV (lsubst σ l) j else v end.
Definition fsubstF (σ : tree lin) (f : fact) : fact :=
  match f with FCond c a b tk => FCond c (lsubstF σ a) (lsubstF σ b) tk | FRange l lo hi => FRange (lsubstF σ l) lo hi
  | FMod l k r => FMod (lsubstF σ l) k r | FBits l m v => FBits (lsubstF σ l) m v
  | FByte x v j => FByte (lsubstF σ x) (lsubstF σ v) j
  | FBytes x bs => FBytes (lsubstF σ x) (List.map (fun p => (lsubstF σ (fst p), snd p)) bs) end.
Definition rsubstF (σ : tree lin) (R : region) : region := RG (lsubstF σ (rg_base R)) (lsubstF σ (rg_size R)) (rg_kind R) (tmap (bsubstF σ) (rg_cont R)).
Definition ssubstF (σ : tree lin) (n : positive) (F : sst) : sst :=
  match σ with
  | TEmpty => SST (s_pc F) (s_regs F) (s_rgs F) (s_facts F) n (s_resv F)
  | _ => SST (s_pc F) (tmap (lsubstF σ) (s_regs F)) (List.map (rsubstF σ) (s_rgs F)) (List.map (fsubstF σ) (s_facts F)) n (rvsubst σ (s_resv F))
  end.
Definition msubstF (σ : tree lin) (M : smodel) : smodel := match σ with TEmpty => M | _ => msubst σ M end.
Definition lsubstsF (σ : tree lin) (al : list lin) : list lin := match σ with TEmpty => al | _ => List.map (lsubstF σ) al end.
(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint nodead {X} (t : tree X) : bool :=
  match t with
  | TEmpty => true
  | TNode l v r => if nodead l then (if nodead r then match v, l, r with None, TEmpty, TEmpty => false | _, _, _ => true end else false) else false
  end.
Fixpoint gen_rgsLF (rss : list (list region)) (fss : list (list fact)) (n : nat) (g : gst) : option (list region * gst) :=
  match n with
  | O => Some ([], g)
  | Datatypes.S n' =>
      match List.fold_right (fun o acc => match o, acc with Some R, Some l => Some (R :: l) | _, _ => None end) (Some []) (List.map (fun rs => List.hd_error rs) rss) with
      | Some (R0 :: Rr) =>
          let '(b, g1) := gq_gen g (List.map rg_base (R0 :: Rr)) fss in
          let '(z, g2) := gq_gen g1 (List.map rg_size (R0 :: Rr)) fss in
          let same := if forallb (fun R => treq bval_eqb (rg_cont R0) (rg_cont R)) Rr then nodead (rg_cont R0) else false in
          let '(c, g2') := if same then (rg_cont R0, g2) else gen_contL (rg_cont R0) (List.map rg_cont Rr) fss g2 in
          match gen_rgsLF (List.map (@List.tl region) rss) fss n' g2' with
          | Some (rs', g3) =>
              let k := if same then (if forallb (fun R => rkind_eqb (rg_kind R) (rg_kind R0)) Rr then rg_kind R0 else RW) else gen_kindL R0 Rr c in
              Some (RG b z k c :: rs', g3)
          | None => None
          end
      | _ => None
      end
  end.
Definition genLAF (L : list (sst * smodel)) (As : list (list lin)) : option (sst * smodel * list lin) :=
  match L with
  | [] => None
  | (F0, M0) :: Lrst =>
      let Lsts := List.map fst L in let Msts := List.map snd L in let fss := List.map s_facts Lsts in
      let n0 := max_next (List.map fst Lrst) (s_next F0) in
      let nR := List.length (s_rgs F0) in
      if (forallb (fun F => Nat.eqb (List.length (s_rgs F)) nR) Lsts &&
          forallb (fun M => Nat.eqb (List.length (sm_maps M)) (List.length (sm_maps M0)) && Nat.eqb (List.length (sm_allow M)) (List.length (sm_allow M0)) &&
                            Nat.eqb (List.length (sm_frz M)) (List.length (sm_frz M0)) && Nat.eqb (List.length (sm_own M)) (List.length (sm_own M0)) &&
                            zr_eqb (sm_zr M) (sm_zr M0)) Msts)%bool then
      let '(regs', g1) := gen_regsL Lsts fss 31 (GST n0 [] []) TEmpty in
      match gen_rgsLF (List.map s_rgs Lsts) fss nR g1 with
      | Some (rgs', g2) =>
          match gen_mapsL (List.map sm_maps Msts) fss (List.length (sm_maps M0)) g2 with
          | Some (maps', g3) =>
              match gen_allowL (List.map sm_allow Msts) fss (List.length (sm_allow M0)) g3 with
              | Some (allow', g4) =>
                  match gen_pairsL (List.map sm_frz Msts) fss (List.length (sm_frz M0)) g4 with
                  | Some (frz', g5) =>
                      match gen_pairsL (List.map sm_own Msts) fss (List.length (sm_own M0)) g5 with
                      | Some (own', g6) =>
                          let '(brk', g7) := gq_gen g6 (List.map sm_brk Msts) fss in
                          let '(sbrk', g8) := gq_gen g7 (List.map sm_sbrk Msts) fss in
                          let '(sp', g9a) := gq_gen g8 (List.map sm_sp Msts) fss in
                          let nA := List.length (List.hd [] As) in
                          match (if forallb (fun ls => Nat.eqb (List.length ls) nA) As then gen_linsL As fss nA g9a else None) with
                          | Some (als', g9) =>
                          let tid' := sm_tid M0 in
                          if forallb (fun M => match sm_tid M, tid' with Some a, Some b => lin_eqb a b | None, None => true | _, _ => false end) Msts then
                          let fs := g_fs g9 ++ List.fold_left (fun fs L => common_suffix fs (s_facts L)) (List.map fst Lrst) (s_facts F0) in
                          Some (SST (s_pc F0) regs' rgs' fs (g_v g9)
                                    (if forallb (fun F => rsv_eqb (s_resv F) (s_resv F0)) Lsts then s_resv F0 else RUnk),
                                SM maps' allow' (sm_zr M0) tid' brk' sbrk' sp' frz' own', als')
                          else None
                          | None => None
                          end
                      | None => None
                      end
                  | None => None
                  end
              | None => None
              end
          | None => None
          end
      | None => None
      end
      else None
  end.
Definition norm_sig (T : list btup) (yb : positive) (k : nat) : tree lin :=
  snd (List.fold_left (fun '(t, σ) a =>
         let Y := lvar (yb + Pos.of_succ_nat t) in
         (S t, match k with
               | O => tset (fst a) Y σ
               | Datatypes.S k' => match nth_error (snd a) k' with Some (x, sft) => tset x (laddc Y (- sft)) σ | None => σ end
               end)) T (O, @TEmpty lin)).
Definition fvarsN (f : fact) : list positive := fact_vars f.
Definition hull_factN (oth : list (list fact * tree lin)) (l : lin) : list fact :=
  let rs := List.map (fun o => irange (fst o) (lsubst (snd o) l)) oth in
  match rs with
  | [] => []
  | r0 :: rr => let lo := fold_left Z.min (List.map fst rr) (fst r0) in let hi := fold_left Z.max (List.map snd rr) (snd r0) in
                if (Z.leb 0 lo && Z.ltb hi (two64 - 1) && negb (Z.eqb lo 0 && Z.eqb hi M64))%bool then [FRange l lo hi] else []
  end.
Definition all_implyN (oth : list (list fact * tree lin)) (f : fact) : bool := allb (fun o => has_fact (fst o) (fsubst (snd o) f)) oth.
(* [comment removed for export] *)
Definition fix_cellsN (P : sst) (cst : list (sst * tree lin)) : list region :=
  let fix go (rp : list region) (rss : list (list region * tree lin)) {struct rp} : list region :=
    match rp with
    | [] => []
    | R :: rp' =>
        let heads := List.map (fun x => (List.hd_error (fst x), snd x)) rss in
        let tails := List.map (fun x => (List.tl (fst x), snd x)) rss in
        let R' :=
          match rg_kind R with
          | RW | RZ =>
              if forallb (fun h => match fst h with
                                   | Some Ri => tforall2 (fun v ov => match ov with Some v' => bval_ent v' (bsubstF (snd h) v) | None => false end) (rg_cont R) (rg_cont Ri)
                                   | None => match rg_cont R with TEmpty => true | _ => match FxCall.telems (rg_cont R) with [] => true | _ => false end end
                                   end) heads
              then R
              else let cell_ok (kv : positive * bval) : bool :=
                     forallb (fun h => match fst h with
                                       | Some Ri => match tget (fst kv) (rg_cont Ri) with Some v => bval_ent v (bsubstF (snd h) (snd kv)) | None => false end
                                       | None => false
                                       end) heads in
                   RG (rg_base R) (rg_size R) RW (fold_left (fun t kv => tset (fst kv) (snd kv) t) (List.filter cell_ok (FxCall.telems (rg_cont R))) TEmpty)
          | _ => R
          end in
        R' :: go rp' tails
    end in
  go (s_rgs P) (List.map (fun Fσ => (s_rgs (fst Fσ), snd Fσ)) cst).
Definition dedupF (l : list fact) : list fact := List.rev (fold_left (fun acc f => if existsb (fact_eqb f) acc then acc else f :: acc) l []).

Definition genN (xf : sst -> list fact) (L : list (sst * smodel)) (As : list (list lin)) : option (sst * smodel * list lin) :=
  match L with
  | [] => None
  | (F0, M0) :: Lr =>
      let Fr := List.map fst Lr in
      let n0 := List.fold_left (fun n F => Pos.max n (s_next F)) Fr (s_next F0) in
      let T := dedup_tups (F0 :: Fr) (lvar (n0 + 1)) (tups_of_regs (s_regs F0) (List.map s_regs Fr) 31 (tups_of_rgs (s_rgs F0) (List.map s_rgs Fr) [])) [] in
      let yb := n0 in
      let nx := (yb + Pos.of_succ_nat (List.length T) + 1)%positive in
      let N := List.map (fun '(k, ((F, M), al)) => let σ := norm_sig T yb k in (ssubst σ nx F, msubst σ M, List.map (lsubst σ) al))
                        (List.combine (List.seq 0 (List.length L)) (List.combine L As)) in
      match genLAF (List.map (fun x => fst x) N) (List.map (fun x => snd x) N) with      (* [comment removed for export] *)
      | Some (P, MP, als) =>
          let Fσ := List.map (fun '((F, M), al) => (F, matchLA F M al P MP als)) (List.combine L As) in
          let oth := List.map (fun x => (s_facts (fst x), snd x)) Fσ in
          let base := match N with x :: _ => s_facts (fst (fst x)) | [] => [] end in
          let cf := List.flat_map (fun f => if all_implyN oth f then [f] else match f with FRange l _ _ => hull_factN oth l | _ => [] end) base in
          let fs := dedupF (List.filter (all_implyN oth) (xf P ++ s_facts P) ++ cf) in
          Some (SST (s_pc P) (s_regs P) (fix_cellsN P Fσ) fs (s_next P) (s_resv P), MP, als)
      | None => None
      end
  end.
(* [comment removed for export] *)
