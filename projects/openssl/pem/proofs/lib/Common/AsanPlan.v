(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.openssl.pem.lib.Common Require Import PropExec.
From OSSVerify.Proofs.openssl.pem.lib.Common Require Import AxSymExec3.
From OSSVerify.Proofs.openssl.pem.lib.Common Require Export AsanPlanCore.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Module AP.
Include APC.
Import AX2.

Section WithSegs.
Variable segs : list Segment.
Variable IT : itab.
Variable A : atable.
Variable nx0 : nat.     (* [comment removed for export] *)
Variable LIMIT : Z.     (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Inductive snode : Type :=
| YMunmap      (* [comment removed for export] *)
| YBrk         (* [comment removed for export] *)
| YSetTid      (* [comment removed for export] *)
| YMadvise.    (* [comment removed for export] *)

(* [comment removed for export] *)
Inductive xnode : Type :=
| XIMemset     (* [comment removed for export] *)
| XIMemcpy     (* [comment removed for export] *)
| XMemset      (* [comment removed for export] *)
| XMemcpy      (* [comment removed for export] *)
| XMemIsZero   (* [comment removed for export] *)
| XEnvScan     (* [comment removed for export] *)
| XPnScan      (* [comment removed for export] *)
| XLayout      (* [comment removed for export] *)
| XIStrncpy    (* [comment removed for export] *)
| XPopFree     (* [comment removed for export] *)
| XSniff.      (* [comment removed for export] *)

Inductive plan : Type :=
| PRun (stops : list Z) (k : plan)           (* [comment removed for export] *)
| PSplit (e : expr) (mid : Z) (k1 k2 : plan) (* [comment removed for export] *)
| PCase2 (e : expr) (mid : Z) (k1 k2 : plan) (* [comment removed for export] *)
| PCaseDisj (b1 b2 : expr) (k1 k2 : plan)  (* [comment removed for export] *)
| PShDisj (b1 n1 b2 n2 : expr) (k : plan)  (* [comment removed for export] *)
| PContra                                    (* [comment removed for export] *)
| PFact (K : kentry) (k : plan)              (* [comment removed for export] *)
| PJoin (b : expr) (off : Z) (n : nat) (k : plan)  (* [comment removed for export] *)
| PForget (ixs : list nat) (k : plan)        (* [comment removed for export] *)
| PDropRange (b : expr) (n : expr) (k : plan) (* [comment removed for export] *)
| PGcKeep (ws : list (expr * expr)) (k : plan) (* [comment removed for export] *)
| PBump (m : nat) (k : plan)                 (* [comment removed for export] *)
| PHavoc (rs : list nat) (k : plan)          (* [comment removed for export] *)
| PHavocBig (K : nat) (k : plan)             (* [comment removed for export] *)
| PFresh (r : nat) (logc : Z) (base : option expr) (k : plan)  (* [comment removed for export] *)
| PSys (y : snode) (k : plan)                (* [comment removed for export] *)
(* [comment removed for export] *)
| PMmap (krefused kgranted : plan)           (* [comment removed for export] *)
| PMmapIn (kkept kok kdestroyed : plan)      (* [comment removed for export] *)
| PMprotect (krefused kgranted : plan)       (* [comment removed for export] *)
| PBrk2 (kblocked kgranted : plan)           (* [comment removed for export] *)
| PX (x : xnode) (args : list expr) (k : plan)   (* [comment removed for export] *)
| PExt (id : nat) (args : list expr) (k : plan)  (* [comment removed for export] *)
| PEmit (id : nat) (args : list expr) (k : plan) (* [comment removed for export] *)
| PExt2 (id : nat) (args : list expr) (k1 k2 : plan) (* [comment removed for export] *)
| PLoop (J : nat) (N : expr) (inv : acs) (body k : plan)  (* [comment removed for export] *)
| PNext                                      (* [comment removed for export] *)
| PHandoff (h : nat)                         (* [comment removed for export] *)
| PExit                                      (* [comment removed for export] *)
| PSpin                                      (* [comment removed for export] *)
| PFog (i : nat) (sz : Z) (k : plan)          (* [comment removed for export] *)
| PFogNew (i : nat) (sz : Z) (k : plan)       (* [comment removed for export] *)
| PGhost (b n : expr) (k : plan)              (* [comment removed for export] *)
| PUnvis (b n : expr) (k : plan)              (* [comment removed for export] *)
| PHavocBrk (lo hi : Z) (k : plan)            (* [comment removed for export] *)
| PIntro (lo hi : Z) (k : plan)               (* [comment removed for export] *)
| PDiamond (joinpc : Z) (rs : list nat) (k : plan)  (* [comment removed for export] *)
| PRename (m : list (nat * nat)) (k : plan)   (* [comment removed for export] *)
| PCompact (k : plan)                         (* [comment removed for export] *)
| PVia (j : nat) (js : acs) (lo : nat) (karms k : plan)  (* [comment removed for export] *)
| PMerge (j : nat)                            (* [comment removed for export] *)
| PAbstractCell (b : expr) (n : Z) (k : plan) (* [comment removed for export] *)
| PHavocWords (bs : list expr) (k : plan)    (* [comment removed for export] *)
| PRespell (r : nat) (e : expr) (k : plan)    (* [comment removed for export] *)
| PMmapInH (kkept kok kdestroyed : plan)      (* [comment removed for export] *)
| PJoinX (b : expr) (off : Z) (n : nat) (k : plan)  (* [comment removed for export] *)
| PDiamondT (joinpc : Z) (depth : nat) (rs : list nat) (k : plan)  (* [comment removed for export] *)
| PBand (v : nat) (klow khigh : plan)           (* [comment removed for export] *)
| PIntroG (lo hi n : Z) (k : plan)             (* [comment removed for export] *)
| PDiamondDisj (b1 b2 : expr) (joinpc : Z) (rs : list nat) (k : plan)
                                                (* [comment removed for export] *)
| PDiamondTX (joinpc : Z) (depth : nat) (rs : list nat) (R : nat) (k : plan)
| PGcDisj (live : list expr) (k : plan)     (* [comment removed for export] *)
| PGcRangeAuto (k : plan)                   (* [comment removed for export] *)
| PLoopAuto (J : nat) (N : expr) (r : lrecipe) (body k : plan)
                                            (* [comment removed for export] *)
| PDiamondBand (v : nat) (joinpc : Z) (depth : nat) (rs : list nat) (k : plan).
                                            (* [comment removed for export] *)
                                                (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition node_sys (y : snode) (cs : acs) : option acs :=
  match y with
  | YMunmap => node_munmap A cs
  | YBrk => node_brk1 A cs
  | YSetTid => node_settid nx0 cs
  | YMadvise => node_madvise A cs
  end.

(* [comment removed for export] *)
Definition x_off (x : xnode) : bool :=
  match x with
  | XIMemset => Z.eqb (x_imemset A) 0
  | XIMemcpy => Z.eqb (x_imemcpy A) 0
  | XMemset => Z.eqb (x_memset A) 0
  | XMemcpy => Z.eqb (x_memcpy A) 0
  | XMemIsZero => Z.eqb (x_memiszero A) 0
  | XIStrncpy => Z.eqb (x_istrncpy A) 0
  | XPopFree => Z.eqb (x_popfree A) 0
  | XSniff => Z.eqb (x_sniff A) 0
  | XEnvScan | XPnScan | XLayout => false
  end.

Definition node_x_on (x : xnode) (args : list expr) (cs : acs) : option acs :=
  match x with
  | XIMemset => summary_fill A nx0 cs (x_imemset A) 256       (* [comment removed for export] *)
  | XMemset => summary_fill A nx0 cs (x_memset A) two64
  | XIMemcpy => summary_copy segs A nx0 cs (x_imemcpy A)
  | XMemcpy => summary_copy segs A nx0 cs (x_memcpy A)
  | XMemIsZero => summary_miz A nx0 cs
  | XEnvScan => node_envscan A cs
  | XPnScan => node_pnscan A nx0 cs
  | XLayout => node_layout cs args
  | XIStrncpy => summary_istrncpy A nx0 cs
  | XPopFree => summary_popfree A nx0 cs args
  | XSniff => summary_sniff segs A nx0 cs
  end.

Definition node_x (x : xnode) (args : list expr) (cs : acs) : option acs :=
  if x_off x then None else node_x_on x args cs.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Inductive cres : Type := COk (s : shape) | CErr (code : Z) (where_ : plan) (cs : acs).

Section Check.
Variable XN : nat -> list expr -> acs -> option acs.                      (* [comment removed for export] *)
Variable XE : nat -> list expr -> acs -> option (Z * list spiece * acs).  (* [comment removed for export] *)
Variable XB : nat -> list expr -> acs -> option (acs * acs).              (* [comment removed for export] *)
Variable HS : nat -> option acs.   (* [comment removed for export] *)
Variable KC : nat.                 (* [comment removed for export] *)
Variable bfuel : nat.              (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint hxm_evars (e : expr) (acc : list nat) : list nat :=
  match e with
  | ELit _ => acc
  | EVar n => if existsb (Nat.eqb n) acc then acc else n :: acc
  | EAlu _ a b | EAluw _ a b | EMd _ a b | EMdw _ a b => hxm_evars a (hxm_evars b acc)
  | EExt _ _ _ a => hxm_evars a acc
  | EBlob _ _ _ _ => acc
  end.
Definition hxm_kvars (K : kentry) (acc : list nat) : list nat :=
  match K with
  | KWord a _ v => hxm_evars (a_base a) (hxm_evars v acc)
  | KZero a n | KBlob a n _ | KWr a n | KUnk a n => hxm_evars (a_base a) (hxm_evars n acc)
  | KFill a n _ => hxm_evars (a_base a) (hxm_evars n acc)
  | KImg _ _ => acc
  | KAlign x _ => hxm_evars x acc
  | KRange x _ _ => hxm_evars x acc
  | KDisj a1 n1 a2 n2 => hxm_evars (a_base a1) (hxm_evars n1 (hxm_evars (a_base a2) (hxm_evars n2 acc)))
  end.
Definition hxm_avars (cs : acs) (acc : list nat) : list nat :=
  let acc := List.fold_right hxm_evars acc (s_regs (a_ss cs)) in
  let acc := List.fold_right hxm_kvars acc (kn cs) in
  let acc := List.fold_right (fun m acc => hxm_evars (am_base m) (hxm_evars (am_len m) acc)) acc (a_maps cs) in
  let acc := List.fold_right (fun p acc => hxm_evars (fst p) (hxm_evars (snd p) acc)) acc (a_vis cs ++ a_ghost cs) in
  let acc := hxm_evars (a_brk cs) acc in
  match a_fd cs with FdFile _ l o => hxm_evars l (hxm_evars o acc) | _ => acc end.
(* [comment removed for export] *)
Definition hxm_pool_b (vb : nat) (used : list nat) (top : nat) : list nat :=
  List.filter (fun v => negb (existsb (Nat.eqb v) used)) (List.rev (List.seq vb (top - vb))).
Definition hxm_pool (used : list nat) (top : nat) : list nat := hxm_pool_b nx0 used top.

(* [comment removed for export] *)
Fixpoint hxm_cells_of (k : list kentry) (acc : list (saddr * nat)) : list (saddr * nat) :=
  match k with
  | [] => acc
  | KWord a w _ :: r => hxm_cells_of r (if existsb (fun p => saddr_eqb (fst p) a && Nat.eqb (snd p) w)%bool acc then acc else acc ++ [(a, w)])
  | _ :: r => hxm_cells_of r acc
  end.
Definition hxm_all_some {X : Type} (l : list (option X)) : option (list X) :=
  List.fold_right (fun o acc => match o, acc with Some x, Some r => Some (x :: r) | _, _ => None end) (Some []) l.
Definition hxm_hull (rs : list (Z * Z)) : option (Z * Z) :=
  match rs with
  | [] => None
  | r :: rest => Some (List.fold_right (fun x acc => (Z.min (fst x) (fst acc), Z.max (snd x) (snd acc))) r rest)
  end.
Definition hxm_all_eq (es : list expr) : bool :=
  match es with [] => true | e :: r => forallb (expr_eqb e) r end.

(* [comment removed for export] *)
Definition hxm_cell (ls : list acs) (M : list kentry) (c : saddr * nat) (pool : list nat)
  : list kentry * list nat :=
  let '(a, w) := c in
  if existsb (fun K => match K with KWord a' w' _ => saddr_eqb a' a && Nat.eqb w' w | _ => false end)%bool M
  then ([], pool) else
  match hxm_all_some (List.map (fun lf => hx_cell (kn lf) a w) ls) with
  | Some vals =>
      if hxm_all_eq vals then (match vals with e :: _ => ([KWord a w e], pool) | [] => ([], pool) end) else
      match pool with
      | [] => ([], pool)
      | v :: pool' =>
          let rng := match hxm_all_some (List.map (fun p => erange (kn (fst p)) (snd p)) (List.combine ls vals)) with
                     | Some rs => match hxm_hull rs with Some (lo, hi) => [KRange (EVar v) lo hi] | None => [] end
                     | None => []
                     end in
          (KWord a w (EVar v) :: rng, pool')
      end
  | None =>
      let K := KUnk a (ELit (Z.of_nat w)) in
      if forallb (fun lf => kunk_covered A (kn lf) K) ls then ([K], pool) else ([], pool)
  end.
Fixpoint hxm_cells (ls : list acs) (M : list kentry) (cs : list (saddr * nat)) (pool : list nat) (acc : list kentry)
  : list kentry :=
  match cs with
  | [] => acc
  | c :: r => let '(add, pool') := hxm_cell ls M c pool in hxm_cells ls M r pool' (acc ++ add)
  end.

(* [comment removed for export] *)
Definition hxm_zpieces (k : list kentry) (b : expr) : list (Z * Z) :=
  List.flat_map (fun K => match K with
                          | KZero (SA b' o) (ELit n) => if expr_eqb b b' && Z.ltb 0 n && Z.ltb n two64 then [(o, o + n)] else []
                          | _ => [] end)%bool k.
Definition hxm_isect (ps qs : list (Z * Z)) : list (Z * Z) :=
  List.flat_map (fun p => List.flat_map (fun q => let lo := Z.max (fst p) (fst q) in let hi := Z.min (snd p) (snd q) in
                                                  if Z.ltb lo hi then [(lo, hi)] else []) qs) ps.
Definition hxm_zeros1 (ls : list acs) (M : list kentry) (b : expr) (o n : Z) : list kentry :=
  let ps := List.fold_right (fun lf ps => hxm_isect ps (hxm_zpieces (kn lf) b)) [(o, o + n)] ls in
  List.flat_map (fun p => let K := KZero (SA b (fst p)) (ELit (snd p - fst p)) in
                          if existsb (kentry_eqb K) M then [] else [K]) ps.
Definition hxm_zeros (ls : list acs) (M : list kentry) (k1 : list kentry) : list kentry :=
  List.flat_map (fun K => match K with
                          | KZero (SA b o) (ELit n) =>
                              if existsb (kentry_eqb K) M then []
                              else if (Z.ltb 0 n && Z.ltb n two64)%bool then hxm_zeros1 ls M b o n else []
                          | _ => [] end) k1.

(* [comment removed for export] *)
Definition hxm_rng_of (k : list kentry) (e : expr) : option (Z * Z) :=
  List.fold_right (fun K acc => match acc with Some _ => acc | None =>
                     match K with KRange e' lo hi => if expr_eqb e e' then Some (lo, hi) else None | _ => None end end) None k.
Definition hxm_ranges (ls : list acs) (M : list kentry) (k1 : list kentry) : list kentry :=
  List.flat_map (fun K => match K with
                          | KRange e _ _ =>
                              if existsb (kentry_eqb K) M then [] else
                              match hxm_all_some (List.map (fun lf => hxm_rng_of (kn lf) e) ls) with
                              | Some rs => match hxm_hull rs with
                                           | Some (lo, hi) => let K' := KRange e lo hi in if existsb (kentry_eqb K') M then [] else [K']
                                           | None => [] end
                              | None => []
                              end
                          | _ => [] end) k1.

Fixpoint hxm_dedup (k : list kentry) (acc : list kentry) : list kentry :=
  match k with
  | [] => acc
  | K :: r => hxm_dedup r (if existsb (kentry_eqb K) acc then acc else acc ++ [K])
  end.

(* [comment removed for export] *)
Definition hxm_additions_b (vb top : nat) (ls : list acs) (m : acs) : list kentry :=
  let M := kn m in
  let used := List.fold_right hxm_avars (List.fold_right hxm_kvars [] M) ls in
  let pool := hxm_pool_b vb used top in
  let cells := List.fold_right (fun lf acc => hxm_cells_of (kn lf) acc) [] ls in
  let g13 := hxm_cells ls M cells pool [] in
  let k1 := match ls with lf :: _ => kn lf | [] => [] end in
  hxm_dedup (g13 ++ hxm_zeros ls M k1 ++ hxm_ranges ls M k1) [].
Definition hxm_additions (ls : list acs) (m : acs) : list kentry := hxm_additions_b nx0 (nxt m) ls m.

(* [comment removed for export] *)
Fixpoint regs_diff_all (base : list expr) (ls : list acs) (acc : list nat) : list nat :=
  match ls with
  | [] => acc
  | x :: r => regs_diff_all base r (acc ++ diff_regs 0 base (s_regs (a_ss x)))
  end.
Definition diamond_joinx_all (nx : nat) (joinpc : Z) (rs : list nat) (R : nat) (l : acs) (ls : list acs) : option acs :=
  let regs0 := s_regs (a_ss l) in
  let hv := nodup Nat.eq_dec (regs_diff_all regs0 ls [] ++ rs) in
  let v0 := List.fold_right (fun x m => Nat.max (nxt x) m) nx (l :: ls) in
  let hi := (v0 + length hv)%nat in
  let regsJ := sr_fresh regs0 hv v0 in
  let knJ := List.fold_right (fun x k => kn_isect k (kn x)) (kn l) ls in
  let m := with_ss l (mk_ss joinpc regsJ knJ hi) in
  let top := (hi + R)%nat in
  let csJ := with_ss l (mk_ss joinpc regsJ (knJ ++ hxm_additions_b hi top (l :: ls) m) top) in
  if (forallb (fun x => Z.eqb (pc x) joinpc) (l :: ls)
      && forallb (fun r => Nat.ltb 0 r && Nat.ltb r 32) hv
      && Nat.eqb (length regsJ) 32
      && Nat.leb nx0 nx && Nat.leb nx v0
      && forallb (fun x => entails_xb segs A nx0 v0 x csJ) (l :: ls))%bool
  then Some csJ else None.

(* [comment removed for export] *)
Definition check_all (chk : acs -> plan -> cres) (k : plan) (css : list acs) : cres :=
  match css with
  | [] => CErr 3 k (init_acs_of A)
  | cs0 :: rest =>
      match chk cs0 k with
      | COk s0 =>
          fold_left (fun acc cs => match acc with
                                   | COk s => match chk cs k with
                                              | COk s' => if shape_eqb s s' then COk s else CErr 6 k cs
                                              | err => err
                                              end
                                   | err => err
                                   end) rest (COk s0)
      | err => err
      end
  end.

(* [comment removed for export] *)
Fixpoint diamond_tree (gb nx : nat) (fuel : nat) (joinpc : Z) (cs : acs) {struct fuel} : option (list acs) :=
  match fuel with
  | O => None
  | S f =>
      match run_block_gc segs IT gb KC bfuel (joinpc :: STOPS A) cs with
      | None => None
      | Some cs' =>
          if Z.eqb (pc cs') joinpc then Some [cs']
          else if negb (Nat.leb nx (nxt cs')) then None
          else match branch_probe IT cs' with
               | Some e =>
                   match erange (kn cs') e with
                   | Some (lo, hi) =>
                       if (Z.leb lo 0 && Z.ltb 0 hi)%bool then
                         match diamond_tree gb nx f joinpc (set_kn cs' (KRange e lo 0 :: kn cs')),
                               diamond_tree gb nx f joinpc (set_kn cs' (KRange e 1 hi :: kn cs')) with
                         | Some la, Some lb => Some (la ++ lb)
                         | _, _ => None
                         end
                       else None      (* [comment removed for export] *)
                   | None => None
                   end
               | None => None
               end
      end
  end.

Fixpoint check (fuel : nat) (lc : option loopctx) (cs : acs) (p : plan) {struct fuel} : cres :=
  match fuel with
  | O => CErr 0 p cs
  | S f =>
  let check_in := check in
  let check (f : nat) := check_in f lc in
  (* [comment removed for export] *)
  let gcb := match lc with Some c => lc_bnd c | None => nx0 end in
  if negb match lc with Some c => Nat.leb (lc_bnd c) (nxt cs) | None => true end then CErr 9 p cs else
  match p with
  | PRun stops k =>
      match run_block_gc segs IT gcb KC bfuel (stops ++ STOPS A) cs with
      | Some cs' => check f cs' k
      | None => CErr 1 p cs
      end
  | PSplit e mid k1 k2 =>
      if expr_vars_lt nx0 e then
      match erange (kn cs) e with
      | Some (lo, hi) =>
          if (Z.leb lo mid && Z.ltb mid hi)%bool then
            match check f (set_kn cs (KRange e lo mid :: kn cs)) k1 with
            | COk s1 =>
                match check f (set_kn cs (KRange e (mid + 1) hi :: kn cs)) k2 with
                | COk s2 => COk (SCase e mid s1 s2)
                | err => err
                end
            | err => err
            end
          else (* [comment removed for export] *)
            if Z.leb hi mid then check f cs k1 else check f cs k2
      | None => CErr 3 p cs
      end
      else CErr 3 p cs
  | PCase2 e mid k1 k2 =>
      match erange (kn cs) e with
      | Some (lo, hi) =>
          if negb (Z.leb lo mid && Z.ltb mid hi)%bool then (if Z.leb hi mid then check f cs k1 else check f cs k2) else
          if (Z.leb lo mid && Z.ltb mid hi)%bool then
            let cs1 := set_kn cs (KRange e lo mid :: kn cs) in
            let cs2 := set_kn cs (KRange e (mid + 1) hi :: kn cs) in
            (* [comment removed for export] *)
            if kn_contra (kn cs1) then check f cs2 k2
            else if kn_contra (kn cs2) then check f cs1 k1
            else
            match check f cs1 k1 with
            | COk s1 =>
                match check f cs2 k2 with
                | COk s2 => if shape_eqb s1 s2 then COk s1 else CErr 6 p cs
                | err => err
                end
            | err => err
            end
          else CErr 3 p cs
      | None => CErr 3 p cs
      end
  | PCaseDisj b1 b2 k1 k2 =>
      match node_casedisj cs b1 b2 with
      | Some (csa, csb) =>
          match check f csa k1 with
          | COk s1 => match check f csb k2 with
                      | COk s2 => if shape_eqb s1 s2 then COk s1 else CErr 6 p cs
                      | err => err
                      end
          | err => err
          end
      | None => CErr 3 p cs
      end
  | PShDisj b1 n1 b2 n2 k => match node_shdisj A cs b1 n1 b2 n2 with Some cs' => check f cs' k | None => CErr 3 p cs end
  | PContra => if kn_contra (kn cs) then COk SNil else CErr 3 p cs
  | PFact K k => if fact_ok (kn cs) K then check f (add_kn cs [K]) k else CErr 3 p cs
  | PJoin b off n k => match node_join segs cs b off n with Some cs' => check f cs' k | None => CErr 3 p cs end
  | PJoinX b off n k => match node_joinx segs nx0 cs b off n with Some cs' => check f cs' k | None => CErr 3 p cs end
  | PDiamondT joinpc depth rs k =>
      match diamond_tree gcb (nxt cs) (S depth) joinpc cs with
      | Some (l :: ls) =>
          match diamond_join_all A nx0 (nxt cs) joinpc rs l ls with
          | Some csj => check f csj k
          | None => CErr 3 p l            (* [comment removed for export] *)
          end
      | _ => CErr 1 p cs
      end
  | PBand v k1 k2 =>
      match node_band A cs v with
      | Some (csa, csb) =>
          match check f csa k1 with
          | COk s1 => match check f csb k2 with
                      | COk s2 => if shape_eqb s1 s2 then COk s1 else CErr 6 p cs
                      | err => err
                      end
          | err => err
          end
      | None => CErr 3 p cs
      end
  | PForget ixs k => check f (set_kn cs (drop_ixs ixs 0 (kn cs))) k
  | PDropRange b n k => check f (node_droprange cs b n) k
  | PGcKeep ws k => check f (set_kn cs (kn_keep (kn cs) ws)) k
  | PGcDisj live k => check f (set_kn cs (kn_gcdisj cs live)) k
  | PGcRangeAuto k => check f (set_kn cs (kn_gcrange nx0 cs)) k
  | PLoopAuto J N r body k => check f cs (PLoop J N (mk_inv cs J r) body k)
  | PDiamondBand v joinpc depth rs k =>
      match node_band A cs v with
      | Some (csa, csb) =>
          match diamond_tree gcb (nxt cs) (S depth) joinpc csa, diamond_tree gcb (nxt cs) (S depth) joinpc csb with
          | Some la, Some lb =>
              match la ++ lb with
              | l :: ls =>
                  match diamond_join_all A nx0 (nxt cs) joinpc rs l ls with
                  | Some csj => check f csj k
                  | None => CErr 3 p l            (* [comment removed for export] *)
                  end
              | [] => CErr 1 p cs
              end
          | _, _ => CErr 1 p cs
          end
      | None => CErr 3 p cs
      end
  | PBump m k => match node_bump cs m with Some cs' => check f cs' k | None => CErr 3 p cs end
  | PHavoc rs k => match node_havoc nx0 cs rs with Some cs' => check f cs' k | None => CErr 3 p cs end
  | PHavocBig K k => match node_havocbig nx0 cs K with Some cs' => check f cs' k | None => CErr 3 p cs end
  | PFresh r logc base k => match node_fresh nx0 cs r logc base with Some cs' => check f cs' k | None => CErr 3 p cs end
  | PSys y k =>
      if is_ecall_at segs cs then
        match node_sys y cs with Some cs' => check f cs' k | None => CErr 3 p cs end
      else CErr 2 p cs
  | PBrk2 ka kb =>
      if is_ecall_at segs cs then
        match node_brk2F A nx0 LIMIT cs with   (* [comment removed for export] *)
        | Some (poss, csa, csb) =>
            (* [comment removed for export] *)
            if poss then check f csb kb
            else
            match check f csa ka with
            | COk sa => match check f csb kb with
                        | COk sb => if shape_seteq sa sb then COk sa   (* [comment removed for export] *)
                                   else CErr 3 p cs
                        | err => err
                        end
            | err => err
            end
        | None => CErr 3 p cs
        end
      else CErr 2 p cs
  | PMmap ka kb =>
      if is_ecall_at segs cs then
        match node_mmap2F A nx0 LIMIT cs with   (* [comment removed for export] *)
        | Some (csa, csb) =>
            (* [comment removed for export] *)
            check f csb kb
        | None => CErr 3 p cs
        end
      else CErr 2 p cs
  | PMmapIn ka kb kc =>
      if is_ecall_at segs cs then
        match node_mmapin A LIMIT false cs with
        | Some (csa, csb, cscs) => check f csb kb   (* [comment removed for export] *)
        | None => CErr 3 p cs
        end
      else CErr 2 p cs
  | PMmapInH ka kb kc =>      (* [comment removed for export] *)
      if is_ecall_at segs cs then
        match node_mmapin A LIMIT true cs with
        | Some (csa, csb, cscs) => check f csb kb   (* [comment removed for export] *)
        | None => CErr 3 p cs
        end
      else CErr 2 p cs
  | PMprotect ka kb =>
      if is_ecall_at segs cs then
        match node_mprotect2 A LIMIT cs with
        | Some (csa, csb) => check f csb kb   (* [comment removed for export] *)
        | None => CErr 3 p cs
        end
      else CErr 2 p cs
  | PX x args k => match node_x x args cs with Some cs' => check f cs' k | None => CErr 3 p cs end
  | PExt id args k => match XN id args cs with Some cs' => check f cs' k | None => CErr 3 p cs end
  | PEmit id args k =>
      match XE id args cs with
      | Some (fd, ps, cs') => match check f cs' k with COk s => COk (SEmitP fd ps s) | err => err end
      | None => CErr 3 p cs
      end
  | PExt2 id args k1 k2 =>
      match XB id args cs with
      | Some (csa, csb) =>
          match check f csa k1 with
          | COk sa => match check f csb k2 with COk sb => COk (SAlt2 sa sb) | err => err end
          | err => err
          end
      | None => CErr 3 p cs
      end
  | PLoop J N inv body k =>
      match loop_ok nx0 cs J N inv with
      | Some nhi =>
          let lo := S J in let hi := nxt inv in
          if (Z.eqb (pc inv) (pc cs) && entails_h A lo hi cs (inst inv J (ELit 0)))%bool then
            match check_in f (Some (LC (pc cs) (inst inv J (eaddz (EVar J) 1)) lo hi)) (loop_body_state J N nhi inv) body with
            | COk SNext => check f (inst inv J N) k
            | COk _ => CErr 7 p cs
            | err => err
            end
          else CErr 3 p cs
      | None => CErr 3 p cs
      end
  | PNext =>
      match lc with
      | Some (LC h nx lo hi) =>
          if (Z.eqb (pc cs) h && entails_h A lo hi cs nx)%bool then COk SNext else CErr 3 p cs
      | _ => CErr 8 p cs
      end
  | PHandoff h =>
      match HS h with
      | Some ch => if entails_x segs A nx0 cs ch then COk (SHole h) else CErr 3 p cs   (* [comment removed for export] *)
      | None => CErr 4 p cs
      end
  | PExit =>
      if is_ecall_at segs cs then
        match node_exit cs with Some code => COk (SExit code) | None => CErr 3 p cs end
      else CErr 2 p cs
  | PSpin => CErr 2 p cs   (* [comment removed for export] *)
  | PFog i sz k => match node_fog cs i sz with Some cs' => check f cs' k | None => CErr 3 p cs end
  | PFogNew i sz k => match node_fognew cs i sz with Some cs' => check f cs' k | None => CErr 3 p cs end
  | PGhost b n k => match node_ghost LIMIT cs b n with Some cs' => check f cs' k | None => CErr 3 p cs end
  | PUnvis b n k => match node_unvis A cs b n with Some cs' => check f cs' k | None => CErr 3 p cs end
  | PHavocBrk lo hi k => match node_havocbrk nx0 cs lo hi with Some cs' => check f cs' k | None => CErr 3 p cs end
  | PIntro lo hi k => match node_intro nx0 cs lo hi with Some cs' => check f cs' k | None => CErr 3 p cs end
  | PIntroG lo hi n k => match node_introg A nx0 cs lo hi n with Some cs' => check f cs' k | None => CErr 3 p cs end
  | PDiamondDisj b1 b2 joinpc rs k =>
      match node_casedisj cs b1 b2 with
      | Some (csa, csb) =>
          match run_block_gc segs IT gcb KC bfuel (joinpc :: STOPS A) csa with
          | Some ca =>
              match run_block_gc segs IT gcb KC bfuel (joinpc :: STOPS A) csb with
              | Some cb =>
                  match node_diamond_join A nx0 (nxt cs) joinpc rs ca cb with
                  | Some csj => check f csj k
                  | None => CErr 3 p ca            (* [comment removed for export] *)
                  end
              | None => CErr 1 p csb
              end
          | None => CErr 1 p csa
          end
      | None => CErr 3 p cs
      end
  | PDiamondTX joinpc depth rs R k =>
      match diamond_tree gcb (nxt cs) (S depth) joinpc cs with
      | Some (l :: ls) =>
          match diamond_joinx_all (nxt cs) joinpc rs R l ls with
          | Some csj => check f csj k
          | None => CErr 3 p l            (* [comment removed for export] *)
          end
      | _ => CErr 1 p cs
      end
  | PRename m k => match node_rename gcb cs m with Some cs' => check f cs' k | None => CErr 3 p cs end
  | PCompact k => match node_compact gcb cs with Some cs' => check f cs' k | None => CErr 3 p cs end
  | PVia j js lo karms k =>
      if via_ok nx0 cs js lo then
        match check f js k with
        | COk sk => check_in f (Some (JC j js sk (nxt cs) lo)) cs karms
        | err => err
        end
      else CErr 3 p cs
  | PMerge j =>
      match lc with
      | Some (JC j' js sk b lo) =>
          (* [comment removed for export] *)
          if (Nat.eqb j j' && Z.eqb (pc cs) (pc js) && shape_vars_lt nx0 sk
              && (entails_h A lo (nxt js) cs js || entails_xb segs A nx0 b cs js))%bool
          then COk sk else CErr 3 p cs
      | _ => CErr 8 p cs
      end
  | PAbstractCell b n k => match node_abstractcell A cs b n with Some cs' => check f cs' k | None => CErr 3 p cs end
  | PHavocWords bs k => match node_havocwords nx0 cs bs with Some cs' => check f cs' k | None => CErr 3 p cs end
  | PRespell r e k => match node_respell cs r e with Some cs' => check f cs' k | None => CErr 3 p cs end
  | PDiamond joinpc rs k =>
      match branch_probe IT cs with
      | Some e =>
          match erange (kn cs) e with
          | Some (lo, hi) =>
              (* [comment removed for export] *)
              if (Z.ltb hi 1 || Z.ltb 0 lo)%bool then
                match run_block_gc segs IT gcb KC bfuel (joinpc :: STOPS A) cs with
                | Some cs' => if Z.eqb (pc cs') joinpc then check f cs' k else CErr 3 p cs'
                | None => CErr 1 p cs
                end
              else
                let cs1 := set_kn cs (KRange e lo 0 :: kn cs) in
                let cs2 := set_kn cs (KRange e 1 hi :: kn cs) in
                match run_block_gc segs IT gcb KC bfuel (joinpc :: STOPS A) cs1 with
                | Some ca =>
                    match run_block_gc segs IT gcb KC bfuel (joinpc :: STOPS A) cs2 with
                    | Some cb =>
                        match node_diamond_join A nx0 (nxt cs) joinpc rs ca cb with
                        | Some csj => check f csj k
                        | None => CErr 3 p ca    (* [comment removed for export] *)
                        end
                    | None => CErr 1 p cs2
                    end
                | None => CErr 1 p cs1
                end
          | None => CErr 3 p cs
          end
      | None => CErr 2 p cs                  (* [comment removed for export] *)
      end
  end
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Record colres := CR { cr_leaves : list (nat * acs); cr_err : option (Z * plan * acs) }.
Definition cr_ok (l : list (nat * acs)) := CR l None.
Definition cr_fail (l : list (nat * acs)) (code : Z) (p : plan) (cs : acs) := CR l (Some (code, p, cs)).

(* [comment removed for export] *)
Definition collect_all (col : acs -> plan -> list (nat * acs) -> colres) (k : plan) (css : list acs) (acc : list (nat * acs)) : colres :=
  match css with
  | [] => cr_fail acc 3 k (init_acs_of A)
  | _ => fold_left (fun r cs => match r with CR acc1 None => col cs k acc1 | err => err end) css (cr_ok acc)
  end.

Fixpoint collect (fuel : nat) (lc : option loopctx) (cs : acs) (p : plan) (acc : list (nat * acs)) {struct fuel} : colres :=
  match fuel with
  | O => cr_fail acc 0 p cs
  | S f =>
  let collect_in := collect in
  let collect (f : nat) := collect_in f lc in
  (* [comment removed for export] *)
  let gcb := match lc with Some c => lc_bnd c | None => nx0 end in
  if negb match lc with Some c => Nat.leb (lc_bnd c) (nxt cs) | None => true end then cr_fail acc 9 p cs else
  match p with
  | PRun stops k =>
      match run_block_gc segs IT gcb KC bfuel (stops ++ STOPS A) cs with
      | Some cs' => collect f cs' k acc
      | None => cr_fail acc 1 p cs
      end
  | PSplit e mid k1 k2 =>
      if expr_vars_lt nx0 e then
      match erange (kn cs) e with
      | Some (lo, hi) =>
          if (Z.leb lo mid && Z.ltb mid hi)%bool then
            match collect f (set_kn cs (KRange e lo mid :: kn cs)) k1 acc with
            | CR acc1 None => collect f (set_kn cs (KRange e (mid + 1) hi :: kn cs)) k2 acc1
            | err => err
            end
          else (* [comment removed for export] *)
            if Z.leb hi mid then collect f cs k1 acc else collect f cs k2 acc
      | None => cr_fail acc 3 p cs
      end
      else cr_fail acc 3 p cs
  | PCase2 e mid k1 k2 =>
      match erange (kn cs) e with
      | Some (lo, hi) =>
          if negb (Z.leb lo mid && Z.ltb mid hi)%bool then (if Z.leb hi mid then collect f cs k1 acc else collect f cs k2 acc) else
          if (Z.leb lo mid && Z.ltb mid hi)%bool then
            let cs1 := set_kn cs (KRange e lo mid :: kn cs) in
            let cs2 := set_kn cs (KRange e (mid + 1) hi :: kn cs) in
            (* [comment removed for export] *)
            if kn_contra (kn cs1) then collect f cs2 k2 acc
            else if kn_contra (kn cs2) then collect f cs1 k1 acc
            else
            match collect f cs1 k1 acc with
            | CR acc1 None => collect f cs2 k2 acc1
            | err => err
            end
          else cr_fail acc 3 p cs
      | None => cr_fail acc 3 p cs
      end
  | PCaseDisj b1 b2 k1 k2 =>
      match node_casedisj cs b1 b2 with
      | Some (csa, csb) =>
          match collect f csa k1 acc with
          | CR acc1 None => collect f csb k2 acc1
          | err => err
          end
      | None => cr_fail acc 3 p cs
      end
  | PShDisj b1 n1 b2 n2 k => match node_shdisj A cs b1 n1 b2 n2 with Some cs' => collect f cs' k acc | None => cr_fail acc 3 p cs end
  | PContra => if kn_contra (kn cs) then cr_ok acc else cr_fail acc 3 p cs
  | PFact K k => if fact_ok (kn cs) K then collect f (add_kn cs [K]) k acc else cr_fail acc 3 p cs
  | PJoin b off n k => match node_join segs cs b off n with Some cs' => collect f cs' k acc | None => cr_fail acc 3 p cs end
  | PJoinX b off n k => match node_joinx segs nx0 cs b off n with Some cs' => collect f cs' k acc | None => cr_fail acc 3 p cs end
  | PDiamondT joinpc depth rs k =>
      match diamond_tree gcb (nxt cs) (S depth) joinpc cs with
      | Some (l :: ls) =>
          match diamond_join_all A nx0 (nxt cs) joinpc rs l ls with
          | Some csj => collect f csj k acc
          | None => cr_fail acc 3 p l
          end
      | _ => cr_fail acc 1 p cs
      end
  | PBand v k1 k2 =>
      match node_band A cs v with
      | Some (csa, csb) =>
          match collect f csa k1 acc with
          | CR acc1 None => collect f csb k2 acc1
          | err => err
          end
      | None => cr_fail acc 3 p cs
      end
  | PForget ixs k => collect f (set_kn cs (drop_ixs ixs 0 (kn cs))) k acc
  | PDropRange b n k => collect f (node_droprange cs b n) k acc
  | PGcKeep ws k => collect f (set_kn cs (kn_keep (kn cs) ws)) k acc
  | PGcDisj live k => collect f (set_kn cs (kn_gcdisj cs live)) k acc
  | PGcRangeAuto k => collect f (set_kn cs (kn_gcrange nx0 cs)) k acc
  | PLoopAuto J N r body k => collect f cs (PLoop J N (mk_inv cs J r) body k) acc
  | PDiamondBand v joinpc depth rs k =>
      match node_band A cs v with
      | Some (csa, csb) =>
          match diamond_tree gcb (nxt cs) (S depth) joinpc csa, diamond_tree gcb (nxt cs) (S depth) joinpc csb with
          | Some la, Some lb =>
              match la ++ lb with
              | l :: ls =>
                  match diamond_join_all A nx0 (nxt cs) joinpc rs l ls with
                  | Some csj => collect f csj k acc
                  | None => cr_fail acc 3 p l
                  end
              | [] => cr_fail acc 1 p cs
              end
          | _, _ => cr_fail acc 1 p cs
          end
      | None => cr_fail acc 3 p cs
      end
  | PBump m k => match node_bump cs m with Some cs' => collect f cs' k acc | None => cr_fail acc 3 p cs end
  | PHavoc rs k => match node_havoc nx0 cs rs with Some cs' => collect f cs' k acc | None => cr_fail acc 3 p cs end
  | PHavocBig K k => match node_havocbig nx0 cs K with Some cs' => collect f cs' k acc | None => cr_fail acc 3 p cs end
  | PFresh r logc base k => match node_fresh nx0 cs r logc base with Some cs' => collect f cs' k acc | None => cr_fail acc 3 p cs end
  | PSys y k =>
      if is_ecall_at segs cs then
        match node_sys y cs with Some cs' => collect f cs' k acc | None => cr_fail acc 3 p cs end
      else cr_fail acc 2 p cs
  | PBrk2 ka kb =>
      if is_ecall_at segs cs then
        match node_brk2F A nx0 LIMIT cs with   (* [comment removed for export] *)
        | Some (poss, csa, csb) =>      (* [comment removed for export] *)
            if poss then collect f csb kb acc      (* [comment removed for export] *)
            else
            match collect f csa ka acc with
            | CR acc1 None => collect f csb kb acc1
            | err => err
            end
        | None => cr_fail acc 3 p cs
        end
      else cr_fail acc 2 p cs
  | PMmap ka kb =>
      if is_ecall_at segs cs then
        match node_mmap2F A nx0 LIMIT cs with   (* [comment removed for export] *)
        | Some (csa, csb) => collect f csb kb acc      (* [comment removed for export] *)
        | None => cr_fail acc 3 p cs
        end
      else cr_fail acc 2 p cs
  | PMmapIn ka kb kc =>
      if is_ecall_at segs cs then
        match node_mmapin A LIMIT false cs with
        | Some (csa, csb, cscs) => collect f csb kb acc      (* [comment removed for export] *)
        | None => cr_fail acc 3 p cs
        end
      else cr_fail acc 2 p cs
  | PMmapInH ka kb kc =>      (* [comment removed for export] *)
      if is_ecall_at segs cs then
        match node_mmapin A LIMIT true cs with
        | Some (csa, csb, cscs) => collect f csb kb acc      (* [comment removed for export] *)
        | None => cr_fail acc 3 p cs
        end
      else cr_fail acc 2 p cs
  | PMprotect ka kb =>
      if is_ecall_at segs cs then
        match node_mprotect2 A LIMIT cs with
        | Some (csa, csb) => collect f csb kb acc      (* [comment removed for export] *)
        | None => cr_fail acc 3 p cs
        end
      else cr_fail acc 2 p cs
  | PX x args k => match node_x x args cs with Some cs' => collect f cs' k acc | None => cr_fail acc 3 p cs end
  | PExt id args k => match XN id args cs with Some cs' => collect f cs' k acc | None => cr_fail acc 3 p cs end
  | PEmit id args k =>
      match XE id args cs with
      | Some (fd, ps, cs') => collect f cs' k acc
      | None => cr_fail acc 3 p cs
      end
  | PExt2 id args k1 k2 =>
      match XB id args cs with
      | Some (csa, csb) =>
          match collect f csa k1 acc with
          | CR acc1 None => collect f csb k2 acc1
          | err => err
          end
      | None => cr_fail acc 3 p cs
      end
  | PLoop J N inv body k =>
      match loop_ok nx0 cs J N inv with
      | Some nhi =>
          let lo := S J in let hi := nxt inv in
          if (Z.eqb (pc inv) (pc cs) && entails_h A lo hi cs (inst inv J (ELit 0)))%bool then
            match collect_in f (Some (LC (pc cs) (inst inv J (eaddz (EVar J) 1)) lo hi)) (loop_body_state J N nhi inv) body acc with
            | CR acc1 None => collect f (inst inv J N) k acc1
            | err => err
            end
          else cr_fail acc 3 p cs
      | None => cr_fail acc 3 p cs
      end
  | PNext =>
      match lc with
      | Some (LC h nx lo hi) =>
          if (Z.eqb (pc cs) h && entails_h A lo hi cs nx)%bool then cr_ok acc else cr_fail acc 3 p cs
      | _ => cr_fail acc 8 p cs
      end
  | PHandoff h => cr_ok ((h, cs) :: acc)   (* [comment removed for export] *)
  | PExit =>
      if is_ecall_at segs cs then
        match node_exit cs with Some _ => cr_ok acc | None => cr_fail acc 3 p cs end
      else cr_fail acc 2 p cs
  | PSpin => if node_spin segs cs then cr_ok acc else cr_fail acc 2 p cs
  | PFog i sz k => match node_fog cs i sz with Some cs' => collect f cs' k acc | None => cr_fail acc 3 p cs end
  | PFogNew i sz k => match node_fognew cs i sz with Some cs' => collect f cs' k acc | None => cr_fail acc 3 p cs end
  | PGhost b n k => match node_ghost LIMIT cs b n with Some cs' => collect f cs' k acc | None => cr_fail acc 3 p cs end
  | PUnvis b n k => match node_unvis A cs b n with Some cs' => collect f cs' k acc | None => cr_fail acc 3 p cs end
  | PHavocBrk lo hi k => match node_havocbrk nx0 cs lo hi with Some cs' => collect f cs' k acc | None => cr_fail acc 3 p cs end
  | PIntro lo hi k => match node_intro nx0 cs lo hi with Some cs' => collect f cs' k acc | None => cr_fail acc 3 p cs end
  | PIntroG lo hi n k => match node_introg A nx0 cs lo hi n with Some cs' => collect f cs' k acc | None => cr_fail acc 3 p cs end
  | PDiamondDisj b1 b2 joinpc rs k =>
      match node_casedisj cs b1 b2 with
      | Some (csa, csb) =>
          match run_block_gc segs IT gcb KC bfuel (joinpc :: STOPS A) csa with
          | Some ca =>
              match run_block_gc segs IT gcb KC bfuel (joinpc :: STOPS A) csb with
              | Some cb =>
                  match node_diamond_join A nx0 (nxt cs) joinpc rs ca cb with
                  | Some csj => collect f csj k acc
                  | None => cr_fail acc 3 p ca
                  end
              | None => cr_fail acc 1 p csb
              end
          | None => cr_fail acc 1 p csa
          end
      | None => cr_fail acc 3 p cs
      end
  | PDiamondTX joinpc depth rs R k =>
      match diamond_tree gcb (nxt cs) (S depth) joinpc cs with
      | Some (l :: ls) =>
          match diamond_joinx_all (nxt cs) joinpc rs R l ls with
          | Some csj => collect f csj k acc
          | None => cr_fail acc 3 p l
          end
      | _ => cr_fail acc 1 p cs
      end
  | PRename m k => match node_rename gcb cs m with Some cs' => collect f cs' k acc | None => cr_fail acc 3 p cs end
  | PCompact k => match node_compact gcb cs with Some cs' => collect f cs' k acc | None => cr_fail acc 3 p cs end
  | PVia j js lo karms k =>
      if via_ok nx0 cs js lo then
        match collect f js k acc with
        | CR acc1 None => collect_in f (Some (JC j js SNil (nxt cs) lo)) cs karms acc1
        | err => err
        end
      else cr_fail acc 3 p cs
  | PMerge j =>
      match lc with
      | Some (JC j' js sk b lo) =>
          if (Nat.eqb j j' && Z.eqb (pc cs) (pc js) && shape_vars_lt nx0 sk
              && (entails_h A lo (nxt js) cs js || entails_xb segs A nx0 b cs js))%bool
          then cr_ok acc else cr_fail acc 3 p cs
      | _ => cr_fail acc 8 p cs
      end
  | PAbstractCell b n k => match node_abstractcell A cs b n with Some cs' => collect f cs' k acc | None => cr_fail acc 3 p cs end
  | PHavocWords bs k => match node_havocwords nx0 cs bs with Some cs' => collect f cs' k acc | None => cr_fail acc 3 p cs end
  | PRespell r e k => match node_respell cs r e with Some cs' => collect f cs' k acc | None => cr_fail acc 3 p cs end
  | PDiamond joinpc rs k =>
      match branch_probe IT cs with
      | Some e =>
          match erange (kn cs) e with
          | Some (lo, hi) =>
              (* [comment removed for export] *)
              if (Z.ltb hi 1 || Z.ltb 0 lo)%bool then
                match run_block_gc segs IT gcb KC bfuel (joinpc :: STOPS A) cs with
                | Some cs' => if Z.eqb (pc cs') joinpc then collect f cs' k acc else cr_fail acc 3 p cs'
                | None => cr_fail acc 1 p cs
                end
              else
                let cs1 := set_kn cs (KRange e lo 0 :: kn cs) in
                let cs2 := set_kn cs (KRange e 1 hi :: kn cs) in
                match run_block_gc segs IT gcb KC bfuel (joinpc :: STOPS A) cs1 with
                | Some ca =>
                    match run_block_gc segs IT gcb KC bfuel (joinpc :: STOPS A) cs2 with
                    | Some cb =>
                        match node_diamond_join A nx0 (nxt cs) joinpc rs ca cb with
                        | Some csj => collect f csj k acc
                        | None => cr_fail acc 3 p ca    (* [comment removed for export] *)
                        end
                    | None => cr_fail acc 1 p cs2
                    end
                | None => cr_fail acc 1 p cs1
                end
          | None => cr_fail acc 3 p cs
          end
      | None => cr_fail acc 2 p cs                  (* [comment removed for export] *)
      end
  end
  end.


(* [comment removed for export] *)
Definition kn_meet (k1 k2 : list kentry) : list kentry :=
  let s2 := kset_of k2 in   (* [comment removed for export] *)
  let imgs2 := List.filter (fun K' => match K' with KImg _ _ => true | _ => false end) k2 in
  List.flat_map (fun K =>
    match K with
    | KImg lo hi =>
        List.flat_map (fun K' => match K' with
                                 | KImg lo' hi' => let a := Z.max lo lo' in let b := Z.min hi hi' in
                                                   if Z.ltb a b then [KImg a b] else []
                                 | _ => [] end) imgs2
    | _ => if kset_mem s2 K then [K] else []
    end) k1.

Definition acs_meet (a b : acs) : option acs :=
  if (Z.eqb (pc a) (pc b)
      && list_eqb expr_eqb (s_regs (a_ss a)) (s_regs (a_ss b))
      && list_eqb amap_eqb (a_maps a) (a_maps b)
      && list_eqb pair_eqb (a_vis a) (a_vis b)
      && list_eqb pair_eqb (a_ghost a) (a_ghost b)
      && expr_eqb (a_brk a) (a_brk b)
      && afd_eqb (a_fd a) (a_fd b)
      && Bool.eqb (a_tidset a) (a_tidset b))%bool
  then Some (ACS (mk_ss (pc a) (s_regs (a_ss a)) (kn_meet (kn a) (kn b)) (Nat.max (nxt a) (nxt b)))
                (a_maps a) (Z.max (a_totsz a) (a_totsz b)) (Z.min (a_ylo a) (a_ylo b)) (Z.max (a_eager a) (a_eager b))
                (a_vis a) (a_ghost a) (Z.max (a_abytes a) (a_abytes b)) (a_brk a) (a_fd a) (a_tidset a))
  else None.

Fixpoint meet_all (l : list acs) : option acs :=
  match l with
  | [] => None
  | [a] => Some a
  | a :: r => match meet_all r with Some m => acs_meet a m | None => None end
  end.

Definition leaves_of (h : nat) (l : list (nat * acs)) : list acs :=
  List.map snd (List.filter (fun p => Nat.eqb (fst p) h) l).

(* [comment removed for export] *)
Definition HS_of (l : list (nat * acs)) (h : nat) : option acs := meet_all (leaves_of h l).

(* [comment removed for export] *)
Fixpoint regs_diff (i : nat) (x y : list expr) : list nat :=
  match x, y with
  | a :: x', b :: y' => if expr_eqb a b then regs_diff (S i) x' y' else i :: regs_diff (S i) x' y'
  | [], [] => []
  | _, _ => [99%nat]
  end.
Definition acs_diff (a b : acs) :=
  (regs_diff 0 (s_regs (a_ss a)) (s_regs (a_ss b)),
   list_eqb amap_eqb (a_maps a) (a_maps b), list_eqb pair_eqb (a_vis a) (a_vis b),
   expr_eqb (a_brk a) (a_brk b), afd_eqb (a_fd a) (a_fd b), Bool.eqb (a_tidset a) (a_tidset b),
   length (kn a), length (kn b), length (kn_meet (kn a) (kn b))).


Definition HS_ofX (l : list (nat * acs)) (h : nat) : option acs :=
  let ls := leaves_of h l in
  match meet_all ls with
  | Some m => Some (set_kn m (kn m ++ hxm_additions ls m))
  | None => None
  end.
(* [comment removed for export] *)
Definition HS_ofXv (vb top : nat) (l : list (nat * acs)) (h : nat) : option acs :=
  let ls := leaves_of h l in
  match meet_all ls with
  | Some m => let m' := set_kn m (kn m ++ hxm_additions_b vb top ls m) in
              Some (if Nat.leb (nxt m') top then bump m' (top - nxt m') else m')
  | None => None
  end.
Definition HS_reportXv (vb top : nat) (l : list (nat * acs)) (h : nat) : option (list kentry * nat * list nat) :=
  let ls := leaves_of h l in
  match meet_all ls with
  | Some m => Some (hxm_additions_b vb top ls m, length (kn m), List.map (fun lf => length (kn lf)) ls)
  | None => None
  end.
Definition HS_checkXv (vb top : nat) (l : list (nat * acs)) (h : nat) : list bool :=
  match HS_ofXv vb top l h with
  | Some hs => List.map (fun lf => entails_xb segs A nx0 vb lf hs) (leaves_of h l)
  | None => []
  end.
(* [comment removed for export] *)
Definition HS_reportX (l : list (nat * acs)) (h : nat) : option (list kentry * nat * list nat) :=
  let ls := leaves_of h l in
  match meet_all ls with
  | Some m => Some (hxm_additions ls m, length (kn m), List.map (fun lf => length (kn lf)) ls)
  | None => None
  end.
(* [comment removed for export] *)
Definition HS_checkX (l : list (nat * acs)) (h : nat) : list bool :=
  match HS_ofX l h with
  | Some hs => List.map (fun lf => entails_x segs A nx0 lf hs) (leaves_of h l)
  | None => []
  end.
End Check.

End WithSegs.
End AP.
