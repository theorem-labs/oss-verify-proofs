(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import PropExec.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import AxSymExec3.
From OSSVerify.Proofs.openssl.hashtable.lib Require Export AsanPlanCore.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import CxPlan CxfL1 CxfL2 CxfL3 CxfLeaf CxfNat.
Import ListNotations.
Open Scope Z_scope.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module CAPL.
Import CAP. Import AX2BL. Import APCL.
Notation "x && y" := (if x then y else false) (at level 40, left associativity) : bool_scope.
Notation "x || y" := (if x then true else y) (at level 50, left associativity) : bool_scope.
Import AX2.
Import AX2L.
Section WithSegs.
Variable segs : list Segment.
Variable IT : itab.
Variable A : atable.
Variable nx0 : nat.
Variable LIMIT : Z.
Definition vis_add0 (cs : acs) (b n : expr) (k : list kentry) : option acs :=
  match xhi (kn cs) n with
  | Some nhi =>
      if (expr_vars_lt (nxt cs) b && expr_vars_lt (nxt cs) n && Z.leb (a_eager cs + a_abytes cs + vis_cost nhi) LIMIT)%bool
      then Some (ACS (mk_ss (pc cs) (s_regs (a_ss cs)) k (nxt cs))
                     (a_maps cs) (a_totsz cs) (a_ylo cs) (a_eager cs)
                     ((b, n) :: a_vis cs) (a_ghost cs) (a_abytes cs + vis_cost nhi) (a_brk cs) (a_fd cs) (a_tidset cs))
      else None
  | None => None
  end.
Definition mmap_null_p (cs : acs) : option acs :=
  match mmap_len cs with
  | Some (ne, nlo, nhi) =>
      if (fresh_ok nx0 cs && expr_vars_lt (nxt cs) ne
          && gap_ok A cs nhi && budget_ok LIMIT cs nhi
          && Z.leb nhi TOPMAX
          && no_holes (a_maps cs))%bool then
        let v := nxt cs in
        let base := escale 4096 (EVar v) in
        let kfacts := KRange (EVar v) (null_lo A (a_maps cs) nlo) ((TOPMAX - nlo) / 4096) :: null_kend base ne nlo ++ kdisj_new A (a_maps cs) base ne in
        let kmem := [KWr (SA base 0) ne; KZero (SA base 0) ne] in
        let k' := kfacts ++ kn_grant_filter A (kn cs) (a_maps cs) in
        let cs1 := add_entry cs (sr_upd (s_regs (a_ss cs)) 10 base) k' (S v) (AM base ne KRW) nhi true (a_ylo cs) in
        vis_add0 cs1 base ne (kmem ++ kn cs1)
      else None
  | None => None
  end.
Definition node_mmap_p (cs : acs) : option acs :=
  if (is_ecall_at segs cs
      && match reg_lit cs 17 with Some 222 => true | _ => false end
      && match reg_lit cs 10 with Some 0 => true | _ => false end
      && match reg_lit cs 12 with Some 3 => true | _ => false end
      && match reg_lit cs 13 with Some 34 => true | _ => false end
      && match reg_lit cs 14 with Some m => Z.eqb m (two64 - 1) | _ => false end
      && match reg_lit cs 15 with Some 0 => true | _ => false end)%bool
  then mmap_null_p cs else None.
Definition mmap_len_q (cs : acs) : option (expr * Z * Z) :=
  match mmap_len cs with
  | Some x => Some x
  | None =>
      let le := reg cs 11 in let k := kn cs in
      match xlo k le, xhi k le with
      | Some lo, Some hi =>
          let ne := mkAluK k ALU_AND (mkAluK k ALU_ADD le (ELit 4095)) (ELit (-4096)) in
          match xlo k ne, xhi k ne with
          | Some nlo, Some nhi =>
              if (Z.ltb 0 lo && Z.ltb (hi + 4095) two64 && Z.ltb 0 nlo && Z.leb nhi (CXLF.p46))%bool then Some (ne, nlo, nhi) else None
          | _, _ => None
          end
      | _, _ => None
      end
  end.
Definition mmap_null_q (cs : acs) : option acs :=
  match mmap_len_q cs with
  | Some (ne, nlo, nhi) =>
      if (fresh_ok nx0 cs && expr_vars_lt (nxt cs) ne
          && gap_ok A cs nhi && budget_ok LIMIT cs nhi
          && Z.leb nhi TOPMAX
          && no_holes (a_maps cs))%bool then
        let v := nxt cs in
        let base := escale 4096 (EVar v) in
        let kfacts := KRange (EVar v) (null_lo A (a_maps cs) nlo) ((TOPMAX - nlo) / 4096) :: null_kend base ne nlo ++ kdisj_new A (a_maps cs) base ne in
        let kmem := [KWr (SA base 0) ne; KZero (SA base 0) ne] in
        let k' := kfacts ++ kn_grant_filter A (kn cs) (a_maps cs) in
        let cs1 := add_entry cs (sr_upd (s_regs (a_ss cs)) 10 base) k' (S v) (AM base ne KRW) nhi true (a_ylo cs) in
        vis_add0 cs1 base ne (kmem ++ kn cs1)
      else None
  | None => None
  end.
Definition node_mmap_q (cs : acs) : option acs :=
  if (is_ecall_at segs cs
      && match reg_lit cs 17 with Some 222 => true | _ => false end
      && match reg_lit cs 10 with Some 0 => true | _ => false end
      && match reg_lit cs 12 with Some 3 => true | _ => false end
      && match reg_lit cs 13 with Some 34 => true | _ => false end
      && match reg_lit cs 14 with Some m => Z.eqb m (two64 - 1) | _ => false end
      && match reg_lit cs 15 with Some 0 => true | _ => false end)%bool
  then mmap_null_q cs else None.
Definition node_munmap_p (cs : acs) : option acs :=
  if negb (is_ecall_at segs cs) then None else
  match reg_lit cs 17, mmap_len cs with
  | Some 215, Some (ne, nlo, nhi) =>
      let b := reg cs 10 in let k := kn cs in
      let '(bb, bk) := split_lit b in
      if (existsb (amap_match k b ne) (a_maps cs) && page_aligned k b && flat_x k bb bk ne
          && match xhi k b with Some hi => Z.ltb (hi + nhi) two64 | None => false end)%bool then
        let k1 := kn_unfill k bb bk ne in
        let ss := a_ss cs in
        Some (ACS (mk_ss (pc cs + 4) (sr_upd (s_regs ss) 10 (ELit 0)) k1 (s_next ss))
                 (List.filter (fun m => negb (amap_match k b ne m)) (a_maps cs))
                 (a_totsz cs) (a_ylo cs) (a_eager cs) (a_vis cs) (a_ghost cs) (a_abytes cs) (a_brk cs) (a_fd cs) (a_tidset cs))
      else None
  | _, _ => None
  end.
Definition node_sys (y : snode) (cs : acs) : option acs :=
  match y with
  | YMunmap => node_munmap A cs
  | YBrk => node_brk1 A cs
  | YSetTid => node_settid nx0 cs
  end.
Definition x_on (x : xnode) : bool :=
  negb (Z.eqb (match x with
               | XIMemset => x_imemset A | XIMemcpy => x_imemcpy A | XMemset => x_memset A | XMemcpy => x_memcpy A
               | XMemIsZero => x_memiszero A | XEnvScan => x_envscan A | XPnScan => x_pnscan A | XLayout => x_envscan A
               | XIStrncpy => x_istrncpy A | XPopFree => x_popfree A | XSniff => x_sniff A end) 0).
Definition node_x (x : xnode) (args : list expr) (cs : acs) : option acs :=
  match x with
  | XIMemset => summary_fill A nx0 cs (x_imemset A) 256       
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
Definition hole_cls (h : nat) : nat := Nat.modulo h 1000.
Fixpoint shape_eqh (x y : shape) : bool :=
  match x, y with
  | SNil, SNil => true
  | SExit c, SExit c' => Z.eqb c c'
  | SEmitP fd ps s, SEmitP fd' ps' s' => Z.eqb fd fd' && spieces_eqb ps ps' && shape_eqh s s'
  | SAlt2 a b, SAlt2 a' b' => shape_eqh a a' && shape_eqh b b'
  | SCase e m a b, SCase e' m' a' b' => expr_eqb e e' && Z.eqb m m' && shape_eqh a a' && shape_eqh b b'
  | SHole h, SHole h' => CXNAT.eqbF (hole_cls h) (hole_cls h')
  | SNext, SNext => true
  | _, _ => false
  end.
Section Check.
Variable XN : nat -> list expr -> acs -> option acs.
Variable XE : nat -> list expr -> acs -> option (Z * list spiece * acs).
Variable XB : nat -> list expr -> acs -> option (acs * acs).
Variable HS : nat -> option acs.
Variable KC : nat.
Variable FO : bool.
Variable SPIN : bool.
Variable GC : bool.
Variable bfuel : nat.
Fixpoint hxm_evars (e : expr) (acc : list nat) : list nat :=
  match e with
  | ELit _ => acc
  | EVar n => if existsb (CXNAT.eqbF n) acc then acc else n :: acc
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
Definition hxm_pool_b (vb : nat) (used : list nat) (top : nat) : list nat :=
  List.filter (fun v => negb (existsb (CXNAT.eqbF v) used)) (List.rev (List.seq vb (top - vb))).
Definition hxm_pool (used : list nat) (top : nat) : list nat := hxm_pool_b nx0 used top.
Fixpoint hxm_cells_of (k : list kentry) (acc : list (saddr * nat)) : list (saddr * nat) :=
  match k with
  | [] => acc
  | KWord a w _ :: r => hxm_cells_of r (if existsb (fun p => saddr_eqb (fst p) a && CXNAT.eqbF (snd p) w)%bool acc then acc else acc ++ [(a, w)])
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
Definition hxm_cell (ls : list acs) (M : list kentry) (c : saddr * nat) (pool : list nat)
  : list kentry * list nat :=
  let '(a, w) := c in
  if existsb (fun K => match K with KWord a' w' _ => saddr_eqb a' a && CXNAT.eqbF w' w | _ => false end)%bool M
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
Definition hxm_additions_b (vb top : nat) (ls : list acs) (m : acs) : list kentry :=
  let M := kn m in
  let used := List.fold_right hxm_avars (List.fold_right hxm_kvars [] M) ls in
  let pool := hxm_pool_b vb used top in
  let cells := List.fold_right (fun lf acc => hxm_cells_of (kn lf) acc) [] ls in
  let g13 := hxm_cells ls M cells pool [] in
  let k1 := match ls with lf :: _ => kn lf | [] => [] end in
  hxm_dedup (g13 ++ hxm_zeros ls M k1 ++ hxm_ranges ls M k1) [].
Definition hxm_additions (ls : list acs) (m : acs) : list kentry := hxm_additions_b nx0 (nxt m) ls m.
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
      && forallb (fun r => CXNAT.ltbF 0 r && CXNAT.ltbF r 32) hv
      && CXNAT.eqbF (length regsJ) 32
      && CXNAT.lebF nx0 nx && CXNAT.lebF nx v0
      && forallb (fun x => entails_xb segs A nx0 v0 x csJ) (l :: ls))%bool
  then Some csJ else None.
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
Definition run_block_gcx (gb : nat) (K : nat) (fuel : nat) (stops : list Z) (cs : acs) : option acs :=
  if GC then run_block_gc segs IT gb K fuel stops cs else run_block segs IT gb K fuel stops cs.
Fixpoint diamond_tree (gb nx : nat) (fuel : nat) (joinpc : Z) (cs : acs) {struct fuel} : option (list acs) :=
  match fuel with
  | O => None
  | S f =>
      match run_block_gcx gb KC bfuel (joinpc :: STOPS A) cs with
      | None => None
      | Some cs' =>
          if Z.eqb (pc cs') joinpc then Some [cs']
          else if negb (CXNAT.lebF nx (nxt cs')) then None
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
                       else None      
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
  
  let gcb := match lc with Some c => lc_bnd c | None => nx0 end in
  if negb match lc with Some c => CXNAT.lebF (lc_bnd c) (nxt cs) | None => true end then CErr 9 p cs else
  match p with
  | PRun stops k =>
      match run_block_gcx gcb KC bfuel (stops ++ STOPS A) cs with
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
          else 
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
            
            if kn_contra (kn cs1) then check f cs2 k2
            else if kn_contra (kn cs2) then check f cs1 k1
            else
            match check f cs1 k1 with
            | COk s1 =>
                match check f cs2 k2 with
                | COk s2 => if shape_eqh s1 s2 then COk s1 else CErr 6 p cs
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
          | None => CErr 3 p l            
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
        match node_brk2F A nx0 LIMIT cs with   
        | Some (poss, csa, csb) =>
            match (if (FO && poss)%bool then COk SNil else check f csa ka) with
            | COk sa => match check f csb kb with
                        | COk sb => if poss then COk (salt2 sa sb)
                                   else if shape_seteq sa sb then COk sa   
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
        match node_mmap2F A nx0 LIMIT cs with   
        | Some (csa, csb) =>
            match (if FO then COk SNil else check f csa ka) with
            | COk sa => match check f csb kb with
                        | COk sb => COk (salt2 sa sb)
                        | err => err
                        end
            | err => err
            end
        | None => CErr 3 p cs
        end
      else CErr 2 p cs
  | PMmapIn ka kb kc =>
      if is_ecall_at segs cs then
        match node_mmapin A LIMIT false cs with
        | Some (csa, csb, cscs) =>
            match (if FO then COk SNil else check f csa ka) with
            | COk sa => match check f csb kb with
                        | COk sb => match (if FO then COk SNil else check_all (check f) kc cscs) with
                                    | COk sc => COk (salt2 sa (salt2 sb sc))
                                    | err => err
                                    end
                        | err => err
                        end
            | err => err
            end
        | None => CErr 3 p cs
        end
      else CErr 2 p cs
  | PMmapInH ka kb kc =>      
      if is_ecall_at segs cs then
        match node_mmapin A LIMIT true cs with
        | Some (csa, csb, cscs) =>
            match (if FO then COk SNil else check f csa ka) with
            | COk sa => match check f csb kb with
                        | COk sb => match (if FO then COk SNil else check_all (check f) kc cscs) with
                                    | COk sc => COk (salt2 sa (salt2 sb sc))
                                    | err => err
                                    end
                        | err => err
                        end
            | err => err
            end
        | None => CErr 3 p cs
        end
      else CErr 2 p cs
  | PMprotect ka kb =>
      if is_ecall_at segs cs then
        match node_mprotect2 A LIMIT cs with
        | Some (csa, csb) =>
            match (if FO then COk SNil else check f csa ka) with
            | COk sa => match check f csb kb with
                        | COk sb => COk (salt2 sa sb)
                        | err => err
                        end
            | err => err
            end
        | None => CErr 3 p cs
        end
      else CErr 2 p cs
  | PX x args k => if negb (x_on x) then CErr 3 p cs else match node_x x args cs with Some cs' => check f cs' k | None => CErr 3 p cs end
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
      | Some ch => if entails_x segs A nx0 cs ch then COk (SHole h) else CErr 3 p cs   
      | None => CErr 4 p cs
      end
  | PExit =>
      if is_ecall_at segs cs then
        match node_exit cs with Some code => COk (SExit code) | None => CErr 3 p cs end
      else CErr 2 p cs
  | PSpin => if (SPIN && node_spin segs cs)%bool then COk SNil else CErr 2 p cs
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
          match run_block_gcx gcb KC bfuel (joinpc :: STOPS A) csa with
          | Some ca =>
              match run_block_gcx gcb KC bfuel (joinpc :: STOPS A) csb with
              | Some cb =>
                  match node_diamond_join A nx0 (nxt cs) joinpc rs ca cb with
                  | Some csj => check f csj k
                  | None => CErr 3 p ca            
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
          | None => CErr 3 p l            
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
          
          if (CXNAT.eqbF j j' && Z.eqb (pc cs) (pc js) && shape_vars_lt nx0 sk
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
              
              if (Z.ltb hi 1 || Z.ltb 0 lo)%bool then
                match run_block_gcx gcb KC bfuel (joinpc :: STOPS A) cs with
                | Some cs' => if Z.eqb (pc cs') joinpc then check f cs' k else CErr 3 p cs'
                | None => CErr 1 p cs
                end
              else
                let cs1 := set_kn cs (KRange e lo 0 :: kn cs) in
                let cs2 := set_kn cs (KRange e 1 hi :: kn cs) in
                match run_block_gcx gcb KC bfuel (joinpc :: STOPS A) cs1 with
                | Some ca =>
                    match run_block_gcx gcb KC bfuel (joinpc :: STOPS A) cs2 with
                    | Some cb =>
                        match node_diamond_join A nx0 (nxt cs) joinpc rs ca cb with
                        | Some csj => check f csj k
                        | None => CErr 3 p ca    
                        end
                    | None => CErr 1 p cs2
                    end
                | None => CErr 1 p cs1
                end
          | None => CErr 3 p cs
          end
      | None => CErr 2 p cs                  
      end
  end
  end.
Definition cr_ok (l : list (nat * acs)) := CR l None.
Definition cr_fail (l : list (nat * acs)) (code : Z) (p : plan) (cs : acs) := CR l (Some (code, p, cs)).
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
  
  let gcb := match lc with Some c => lc_bnd c | None => nx0 end in
  if negb match lc with Some c => CXNAT.lebF (lc_bnd c) (nxt cs) | None => true end then cr_fail acc 9 p cs else
  match p with
  | PRun stops k =>
      match run_block_gcx gcb KC bfuel (stops ++ STOPS A) cs with
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
          else 
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
        match node_brk2F A nx0 LIMIT cs with   
        | Some (poss, csa, csb) =>      
            match (if (FO && poss)%bool then cr_ok acc else collect f csa ka acc) with
            | CR acc1 None => collect f csb kb acc1
            | err => err
            end
        | None => cr_fail acc 3 p cs
        end
      else cr_fail acc 2 p cs
  | PMmap ka kb =>
      if is_ecall_at segs cs then
        match node_mmap2F A nx0 LIMIT cs with   
        | Some (csa, csb) =>
            match (if FO then cr_ok acc else collect f csa ka acc) with
            | CR acc1 None => collect f csb kb acc1
            | err => err
            end
        | None => cr_fail acc 3 p cs
        end
      else cr_fail acc 2 p cs
  | PMmapIn ka kb kc =>
      if is_ecall_at segs cs then
        match node_mmapin A LIMIT false cs with
        | Some (csa, csb, cscs) =>
            match (if FO then cr_ok acc else collect f csa ka acc) with
            | CR acc1 None => match collect f csb kb acc1 with
                              | CR acc2 None => if FO then cr_ok acc2 else collect_all (collect f) kc cscs acc2
                              | err => err
                              end
            | err => err
            end
        | None => cr_fail acc 3 p cs
        end
      else cr_fail acc 2 p cs
  | PMmapInH ka kb kc =>      
      if is_ecall_at segs cs then
        match node_mmapin A LIMIT true cs with
        | Some (csa, csb, cscs) =>
            match (if FO then cr_ok acc else collect f csa ka acc) with
            | CR acc1 None => match collect f csb kb acc1 with
                              | CR acc2 None => if FO then cr_ok acc2 else collect_all (collect f) kc cscs acc2
                              | err => err
                              end
            | err => err
            end
        | None => cr_fail acc 3 p cs
        end
      else cr_fail acc 2 p cs
  | PMprotect ka kb =>
      if is_ecall_at segs cs then
        match node_mprotect2 A LIMIT cs with
        | Some (csa, csb) =>
            match (if FO then cr_ok acc else collect f csa ka acc) with
            | CR acc1 None => collect f csb kb acc1
            | err => err
            end
        | None => cr_fail acc 3 p cs
        end
      else cr_fail acc 2 p cs
  | PX x args k => if negb (x_on x) then cr_fail acc 3 p cs else match node_x x args cs with Some cs' => collect f cs' k acc | None => cr_fail acc 3 p cs end
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
  | PHandoff h => cr_ok ((h, cs) :: acc)   
  | PExit =>
      if is_ecall_at segs cs then
        match node_exit cs with Some _ => cr_ok acc | None => cr_fail acc 3 p cs end
      else cr_fail acc 2 p cs
  | PSpin => if (SPIN && node_spin segs cs)%bool then cr_ok acc else cr_fail acc 2 p cs
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
          match run_block_gcx gcb KC bfuel (joinpc :: STOPS A) csa with
          | Some ca =>
              match run_block_gcx gcb KC bfuel (joinpc :: STOPS A) csb with
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
          if (CXNAT.eqbF j j' && Z.eqb (pc cs) (pc js) && shape_vars_lt nx0 sk
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
              
              if (Z.ltb hi 1 || Z.ltb 0 lo)%bool then
                match run_block_gcx gcb KC bfuel (joinpc :: STOPS A) cs with
                | Some cs' => if Z.eqb (pc cs') joinpc then collect f cs' k acc else cr_fail acc 3 p cs'
                | None => cr_fail acc 1 p cs
                end
              else
                let cs1 := set_kn cs (KRange e lo 0 :: kn cs) in
                let cs2 := set_kn cs (KRange e 1 hi :: kn cs) in
                match run_block_gcx gcb KC bfuel (joinpc :: STOPS A) cs1 with
                | Some ca =>
                    match run_block_gcx gcb KC bfuel (joinpc :: STOPS A) cs2 with
                    | Some cb =>
                        match node_diamond_join A nx0 (nxt cs) joinpc rs ca cb with
                        | Some csj => collect f csj k acc
                        | None => cr_fail acc 3 p ca    
                        end
                    | None => cr_fail acc 1 p cs2
                    end
                | None => cr_fail acc 1 p cs1
                end
          | None => cr_fail acc 3 p cs
          end
      | None => cr_fail acc 2 p cs                  
      end
  end
  end.
Definition kn_meet (k1 k2 : list kentry) : list kentry :=
  let s2 := kset_of k2 in   
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
  List.map snd (List.filter (fun p => CXNAT.eqbF (fst p) h) l).
Definition HS_of (l : list (nat * acs)) (h : nat) : option acs := meet_all (leaves_of h l).
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
Definition HS_ofXv (vb top : nat) (l : list (nat * acs)) (h : nat) : option acs :=
  let ls := leaves_of h l in
  match meet_all ls with
  | Some m => let m' := set_kn m (kn m ++ hxm_additions_b vb top ls m) in
              Some (if CXNAT.lebF (nxt m') top then bump m' (top - nxt m') else m')
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
Definition HS_reportX (l : list (nat * acs)) (h : nat) : option (list kentry * nat * list nat) :=
  let ls := leaves_of h l in
  match meet_all ls with
  | Some m => Some (hxm_additions ls m, length (kn m), List.map (fun lf => length (kn lf)) ls)
  | None => None
  end.
Definition HS_checkX (l : list (nat * acs)) (h : nat) : list bool :=
  match HS_ofX l h with
  | Some hs => List.map (fun lf => entails_x segs A nx0 lf hs) (leaves_of h l)
  | None => []
  end.
End Check.
End WithSegs.
Lemma L_CAPL_vis_add0 : @vis_add0 = @CAP.vis_add0.
Proof. unfold vis_add0. rewrite ?APCL.L_APCL_expr_vars_lt, ?APCL.L_APCL_kn, ?APCL.L_APCL_mk_ss, ?APCL.L_APCL_nxt, ?APCL.L_APCL_pc, ?APCL.L_APCL_vis_cost, ?AX2L.L_AX2L_xhi. reflexivity. Qed.

Lemma L_CAPL_mmap_null_p : @mmap_null_p = @CAP.mmap_null_p.
Proof. unfold mmap_null_p. rewrite ?L_CAPL_vis_add0, ?APCL.L_APCL_TOPMAX, ?APCL.L_APCL_add_entry, ?APCL.L_APCL_budget_ok, ?APCL.L_APCL_escale, ?APCL.L_APCL_expr_vars_lt, ?APCL.L_APCL_fresh_ok, ?APCL.L_APCL_gap_ok, ?APCL.L_APCL_kdisj_new, ?APCL.L_APCL_kn, ?APCL.L_APCL_kn_grant_filter, ?APCL.L_APCL_mmap_len, ?APCL.L_APCL_no_holes, ?APCL.L_APCL_null_kend, ?APCL.L_APCL_null_lo, ?APCL.L_APCL_nxt, ?AX2L.L_AX2L_sr_upd. reflexivity. Qed.

Lemma L_CAPL_node_mmap_p : @node_mmap_p = @CAP.node_mmap_p.
Proof. unfold node_mmap_p. rewrite ?L_CAPL_mmap_null_p, ?APCL.L_APCL_is_ecall_at, ?APCL.L_APCL_reg_lit, ?AX2L.L_AX2L_two64. reflexivity. Qed.

Lemma L_CAPL_mmap_len_q : @mmap_len_q = @CAP.mmap_len_q.
Proof. unfold mmap_len_q. rewrite ?APCL.L_APCL_kn, ?AX2L.L_AX2L_mkAluK, ?APCL.L_APCL_mmap_len, ?APCL.L_APCL_reg, ?AX2L.L_AX2L_two64, ?AX2L.L_AX2L_xhi, ?AX2L.L_AX2L_xlo, ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

Lemma L_CAPL_mmap_null_q : @mmap_null_q = @CAP.mmap_null_q.
Proof. unfold mmap_null_q. rewrite ?L_CAPL_vis_add0, ?L_CAPL_mmap_len_q, ?APCL.L_APCL_TOPMAX, ?APCL.L_APCL_add_entry, ?APCL.L_APCL_budget_ok, ?APCL.L_APCL_escale, ?APCL.L_APCL_expr_vars_lt, ?APCL.L_APCL_fresh_ok, ?APCL.L_APCL_gap_ok, ?APCL.L_APCL_kdisj_new, ?APCL.L_APCL_kn, ?APCL.L_APCL_kn_grant_filter, ?APCL.L_APCL_no_holes, ?APCL.L_APCL_null_kend, ?APCL.L_APCL_null_lo, ?APCL.L_APCL_nxt, ?AX2L.L_AX2L_sr_upd. reflexivity. Qed.

Lemma L_CAPL_node_mmap_q : @node_mmap_q = @CAP.node_mmap_q.
Proof. unfold node_mmap_q. rewrite ?L_CAPL_mmap_null_q, ?APCL.L_APCL_is_ecall_at, ?APCL.L_APCL_reg_lit, ?AX2L.L_AX2L_two64. reflexivity. Qed.

Lemma L_CAPL_node_munmap_p : @node_munmap_p = @CAP.node_munmap_p.
Proof. unfold node_munmap_p. rewrite ?APCL.L_APCL_amap_match, ?APCL.L_APCL_flat_x, ?APCL.L_APCL_is_ecall_at, ?APCL.L_APCL_kn, ?APCL.L_APCL_kn_unfill, ?APCL.L_APCL_mk_ss, ?APCL.L_APCL_mmap_len, ?APCL.L_APCL_page_aligned, ?APCL.L_APCL_pc, ?APCL.L_APCL_reg, ?APCL.L_APCL_reg_lit, ?AX2L.L_AX2L_split_lit, ?AX2L.L_AX2L_sr_upd, ?AX2L.L_AX2L_two64, ?AX2L.L_AX2L_xhi. reflexivity. Qed.

Lemma L_CAPL_node_sys : @node_sys = @CAP.node_sys.
Proof. unfold node_sys. rewrite ?APCL.L_APCL_node_brk1, ?APCL.L_APCL_node_munmap, ?APCL.L_APCL_node_settid. reflexivity. Qed.

Lemma L_CAPL_x_on : @x_on = @CAP.x_on.
Proof. unfold x_on. reflexivity. Qed.

Lemma L_CAPL_node_x : @node_x = @CAP.node_x.
Proof. unfold node_x. rewrite ?APCL.L_APCL_node_envscan, ?APCL.L_APCL_node_layout, ?APCL.L_APCL_node_pnscan, ?APCL.L_APCL_summary_copy, ?APCL.L_APCL_summary_fill, ?APCL.L_APCL_summary_istrncpy, ?APCL.L_APCL_summary_miz, ?APCL.L_APCL_summary_popfree, ?APCL.L_APCL_summary_sniff, ?AX2L.L_AX2L_two64. reflexivity. Qed.

Lemma L_CAPL_hole_cls : @hole_cls = @CAP.hole_cls.
Proof. unfold hole_cls. reflexivity. Qed.

Lemma L_CAPL_shape_eqh : @shape_eqh = @CAP.shape_eqh.
Proof. unfold shape_eqh. rewrite ?L_CAPL_hole_cls, ?AX2L.L_AX2L_expr_eqb, ?APCL.L_APCL_spieces_eqb, ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

Lemma L_CAPL_hxm_evars : @hxm_evars = @CAP.hxm_evars.
Proof. unfold hxm_evars. rewrite ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

Lemma L_CAPL_hxm_kvars : @hxm_kvars = @CAP.hxm_kvars.
Proof. unfold hxm_kvars. rewrite ?L_CAPL_hxm_evars. reflexivity. Qed.

Lemma L_CAPL_hxm_avars : @hxm_avars = @CAP.hxm_avars.
Proof. unfold hxm_avars. rewrite ?L_CAPL_hxm_evars, ?L_CAPL_hxm_kvars, ?APCL.L_APCL_kn. reflexivity. Qed.

Lemma L_CAPL_hxm_pool_b : @hxm_pool_b = @CAP.hxm_pool_b.
Proof. unfold hxm_pool_b. rewrite ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

Lemma L_CAPL_hxm_pool : @hxm_pool = @CAP.hxm_pool.
Proof. unfold hxm_pool. rewrite ?L_CAPL_hxm_pool_b. reflexivity. Qed.

Lemma L_CAPL_hxm_cells_of : @hxm_cells_of = @CAP.hxm_cells_of.
Proof. unfold hxm_cells_of. rewrite ?AX2L.L_AX2L_saddr_eqb, ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

Lemma L_CAPL_hxm_all_some : @hxm_all_some = @CAP.hxm_all_some.
Proof. unfold hxm_all_some. reflexivity. Qed.

Lemma L_CAPL_hxm_hull : @hxm_hull = @CAP.hxm_hull.
Proof. unfold hxm_hull. reflexivity. Qed.

Lemma L_CAPL_hxm_all_eq : @hxm_all_eq = @CAP.hxm_all_eq.
Proof. unfold hxm_all_eq. rewrite ?AX2L.L_AX2L_expr_eqb. reflexivity. Qed.

Lemma L_CAPL_hxm_cell : @hxm_cell = @CAP.hxm_cell.
Proof. unfold hxm_cell. rewrite ?L_CAPL_hxm_all_some, ?L_CAPL_hxm_hull, ?L_CAPL_hxm_all_eq, ?AX2L.L_AX2L_erange, ?APCL.L_APCL_hx_cell, ?APCL.L_APCL_kn, ?APCL.L_APCL_kunk_covered, ?AX2L.L_AX2L_saddr_eqb, ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

Lemma L_CAPL_hxm_cells : @hxm_cells = @CAP.hxm_cells.
Proof. unfold hxm_cells. rewrite ?L_CAPL_hxm_cell. reflexivity. Qed.

Lemma L_CAPL_hxm_zpieces : @hxm_zpieces = @CAP.hxm_zpieces.
Proof. unfold hxm_zpieces. rewrite ?AX2L.L_AX2L_expr_eqb, ?AX2L.L_AX2L_two64. reflexivity. Qed.

Lemma L_CAPL_hxm_isect : @hxm_isect = @CAP.hxm_isect.
Proof. unfold hxm_isect. reflexivity. Qed.

Lemma L_CAPL_hxm_zeros1 : @hxm_zeros1 = @CAP.hxm_zeros1.
Proof. unfold hxm_zeros1. rewrite ?L_CAPL_hxm_zpieces, ?L_CAPL_hxm_isect, ?APCL.L_APCL_kentry_eqb, ?APCL.L_APCL_kn. reflexivity. Qed.

Lemma L_CAPL_hxm_zeros : @hxm_zeros = @CAP.hxm_zeros.
Proof. unfold hxm_zeros. rewrite ?L_CAPL_hxm_zeros1, ?APCL.L_APCL_kentry_eqb, ?AX2L.L_AX2L_two64. reflexivity. Qed.

Lemma L_CAPL_hxm_rng_of : @hxm_rng_of = @CAP.hxm_rng_of.
Proof. unfold hxm_rng_of. rewrite ?AX2L.L_AX2L_expr_eqb. reflexivity. Qed.

Lemma L_CAPL_hxm_ranges : @hxm_ranges = @CAP.hxm_ranges.
Proof. unfold hxm_ranges. rewrite ?L_CAPL_hxm_all_some, ?L_CAPL_hxm_hull, ?L_CAPL_hxm_rng_of, ?APCL.L_APCL_kentry_eqb, ?APCL.L_APCL_kn. reflexivity. Qed.

Lemma L_CAPL_hxm_dedup : @hxm_dedup = @CAP.hxm_dedup.
Proof. unfold hxm_dedup. rewrite ?APCL.L_APCL_kentry_eqb. reflexivity. Qed.

Lemma L_CAPL_hxm_additions_b : @hxm_additions_b = @CAP.hxm_additions_b.
Proof. unfold hxm_additions_b. rewrite ?L_CAPL_hxm_kvars, ?L_CAPL_hxm_avars, ?L_CAPL_hxm_pool_b, ?L_CAPL_hxm_cells_of, ?L_CAPL_hxm_cells, ?L_CAPL_hxm_zeros, ?L_CAPL_hxm_ranges, ?L_CAPL_hxm_dedup, ?APCL.L_APCL_kn. reflexivity. Qed.

Lemma L_CAPL_hxm_additions : @hxm_additions = @CAP.hxm_additions.
Proof. unfold hxm_additions. rewrite ?L_CAPL_hxm_additions_b, ?APCL.L_APCL_nxt. reflexivity. Qed.

Lemma L_CAPL_regs_diff_all : @regs_diff_all = @CAP.regs_diff_all.
Proof. unfold regs_diff_all. rewrite ?APCL.L_APCL_diff_regs. reflexivity. Qed.

Lemma L_CAPL_diamond_joinx_all : @diamond_joinx_all = @CAP.diamond_joinx_all.
Proof. unfold diamond_joinx_all. rewrite ?L_CAPL_hxm_additions_b, ?L_CAPL_regs_diff_all, ?APCL.L_APCL_entails_xb, ?APCL.L_APCL_kn, ?APCL.L_APCL_kn_isect, ?APCL.L_APCL_mk_ss, ?APCL.L_APCL_nxt, ?APCL.L_APCL_pc, ?APCL.L_APCL_sr_fresh, ?APCL.L_APCL_with_ss, ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

Lemma L_CAPL_check_all : @check_all = @CAP.check_all.
Proof. unfold check_all. rewrite ?APCL.L_APCL_init_acs_of, ?APCL.L_APCL_shape_eqb. reflexivity. Qed.

Lemma L_CAPL_run_block_gcx : @run_block_gcx = @CAP.run_block_gcx.
Proof. unfold run_block_gcx. rewrite ?APCL.L_APCL_run_block, ?APCL.L_APCL_run_block_gc. reflexivity. Qed.

Lemma L_CAPL_diamond_tree : @diamond_tree = @CAP.diamond_tree.
Proof. unfold diamond_tree. rewrite ?L_CAPL_run_block_gcx, ?APCL.L_APCL_STOPS, ?APCL.L_APCL_branch_probe, ?AX2L.L_AX2L_erange, ?APCL.L_APCL_kn, ?APCL.L_APCL_nxt, ?APCL.L_APCL_pc, ?APCL.L_APCL_set_kn, ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

Lemma L_CAPL_check : @check = @CAP.check.
Proof. unfold check. rewrite ?L_CAPL_node_sys, ?L_CAPL_x_on, ?L_CAPL_node_x, ?L_CAPL_shape_eqh, ?L_CAPL_diamond_joinx_all, ?L_CAPL_check_all, ?L_CAPL_run_block_gcx, ?L_CAPL_diamond_tree, ?APCL.L_APCL_STOPS, ?APCL.L_APCL_add_kn, ?APCL.L_APCL_branch_probe, ?APCL.L_APCL_diamond_join_all, ?APCL.L_APCL_drop_ixs, ?APCL.L_APCL_eaddz, ?APCL.L_APCL_entails_h, ?APCL.L_APCL_entails_x, ?APCL.L_APCL_entails_xb, ?AX2L.L_AX2L_erange, ?APCL.L_APCL_expr_vars_lt, ?APCL.L_APCL_fact_ok, ?APCL.L_APCL_inst, ?APCL.L_APCL_is_ecall_at, ?APCL.L_APCL_kn, ?APCL.L_APCL_kn_contra, ?APCL.L_APCL_kn_gcdisj, ?APCL.L_APCL_kn_gcrange, ?APCL.L_APCL_kn_keep, ?APCL.L_APCL_lc_bnd, ?APCL.L_APCL_loop_body_state, ?APCL.L_APCL_loop_ok, ?APCL.L_APCL_node_abstractcell, ?APCL.L_APCL_node_band, ?APCL.L_APCL_node_brk2F, ?APCL.L_APCL_node_bump, ?APCL.L_APCL_node_casedisj, ?APCL.L_APCL_node_compact, ?APCL.L_APCL_node_diamond_join, ?APCL.L_APCL_node_droprange, ?APCL.L_APCL_node_exit, ?APCL.L_APCL_node_fog, ?APCL.L_APCL_node_fognew, ?APCL.L_APCL_node_fresh, ?APCL.L_APCL_node_ghost, ?APCL.L_APCL_node_havoc, ?APCL.L_APCL_node_havocbig, ?APCL.L_APCL_node_havocbrk, ?APCL.L_APCL_node_havocwords, ?APCL.L_APCL_node_intro, ?APCL.L_APCL_node_introg, ?APCL.L_APCL_node_join, ?APCL.L_APCL_node_joinx, ?APCL.L_APCL_node_mmap2F, ?APCL.L_APCL_node_mmapin, ?APCL.L_APCL_node_mprotect2, ?APCL.L_APCL_node_rename, ?APCL.L_APCL_node_respell, ?APCL.L_APCL_node_shdisj, ?APCL.L_APCL_node_spin, ?APCL.L_APCL_node_unvis, ?APCL.L_APCL_nxt, ?APCL.L_APCL_pc, ?APCL.L_APCL_salt2, ?APCL.L_APCL_set_kn, ?APCL.L_APCL_shape_eqb, ?APCL.L_APCL_shape_seteq, ?APCL.L_APCL_shape_vars_lt, ?APCL.L_APCL_via_ok, ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

Lemma L_CAPL_cr_ok : @cr_ok = @CAP.cr_ok.
Proof. unfold cr_ok. reflexivity. Qed.

Lemma L_CAPL_cr_fail : @cr_fail = @CAP.cr_fail.
Proof. unfold cr_fail. reflexivity. Qed.

Lemma L_CAPL_collect_all : @collect_all = @CAP.collect_all.
Proof. unfold collect_all. rewrite ?L_CAPL_cr_ok, ?L_CAPL_cr_fail, ?APCL.L_APCL_init_acs_of. reflexivity. Qed.

Lemma L_CAPL_collect : @collect = @CAP.collect.
Proof. unfold collect. rewrite ?L_CAPL_node_sys, ?L_CAPL_x_on, ?L_CAPL_node_x, ?L_CAPL_diamond_joinx_all, ?L_CAPL_run_block_gcx, ?L_CAPL_diamond_tree, ?L_CAPL_cr_ok, ?L_CAPL_cr_fail, ?L_CAPL_collect_all, ?APCL.L_APCL_STOPS, ?APCL.L_APCL_add_kn, ?APCL.L_APCL_branch_probe, ?APCL.L_APCL_diamond_join_all, ?APCL.L_APCL_drop_ixs, ?APCL.L_APCL_eaddz, ?APCL.L_APCL_entails_h, ?APCL.L_APCL_entails_xb, ?AX2L.L_AX2L_erange, ?APCL.L_APCL_expr_vars_lt, ?APCL.L_APCL_fact_ok, ?APCL.L_APCL_inst, ?APCL.L_APCL_is_ecall_at, ?APCL.L_APCL_kn, ?APCL.L_APCL_kn_contra, ?APCL.L_APCL_kn_gcdisj, ?APCL.L_APCL_kn_gcrange, ?APCL.L_APCL_kn_keep, ?APCL.L_APCL_lc_bnd, ?APCL.L_APCL_loop_body_state, ?APCL.L_APCL_loop_ok, ?APCL.L_APCL_node_abstractcell, ?APCL.L_APCL_node_band, ?APCL.L_APCL_node_brk2F, ?APCL.L_APCL_node_bump, ?APCL.L_APCL_node_casedisj, ?APCL.L_APCL_node_compact, ?APCL.L_APCL_node_diamond_join, ?APCL.L_APCL_node_droprange, ?APCL.L_APCL_node_exit, ?APCL.L_APCL_node_fog, ?APCL.L_APCL_node_fognew, ?APCL.L_APCL_node_fresh, ?APCL.L_APCL_node_ghost, ?APCL.L_APCL_node_havoc, ?APCL.L_APCL_node_havocbig, ?APCL.L_APCL_node_havocbrk, ?APCL.L_APCL_node_havocwords, ?APCL.L_APCL_node_intro, ?APCL.L_APCL_node_introg, ?APCL.L_APCL_node_join, ?APCL.L_APCL_node_joinx, ?APCL.L_APCL_node_mmap2F, ?APCL.L_APCL_node_mmapin, ?APCL.L_APCL_node_mprotect2, ?APCL.L_APCL_node_rename, ?APCL.L_APCL_node_respell, ?APCL.L_APCL_node_shdisj, ?APCL.L_APCL_node_spin, ?APCL.L_APCL_node_unvis, ?APCL.L_APCL_nxt, ?APCL.L_APCL_pc, ?APCL.L_APCL_set_kn, ?APCL.L_APCL_shape_vars_lt, ?APCL.L_APCL_via_ok, ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

Lemma L_CAPL_kn_meet : @kn_meet = @CAP.kn_meet.
Proof. unfold kn_meet. rewrite ?APCL.L_APCL_kset_mem, ?APCL.L_APCL_kset_of. reflexivity. Qed.

Lemma L_CAPL_acs_meet : @acs_meet = @CAP.acs_meet.
Proof. unfold acs_meet. rewrite ?L_CAPL_kn_meet, ?APCL.L_APCL_afd_eqb, ?APCL.L_APCL_amap_eqb, ?AX2L.L_AX2L_expr_eqb, ?APCL.L_APCL_kn, ?APCL.L_APCL_list_eqb, ?APCL.L_APCL_mk_ss, ?APCL.L_APCL_nxt, ?APCL.L_APCL_pair_eqb, ?APCL.L_APCL_pc. reflexivity. Qed.

Lemma L_CAPL_meet_all : @meet_all = @CAP.meet_all.
Proof. unfold meet_all. rewrite ?L_CAPL_acs_meet. reflexivity. Qed.

Lemma L_CAPL_leaves_of : @leaves_of = @CAP.leaves_of.
Proof. unfold leaves_of. rewrite ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

Lemma L_CAPL_HS_of : @HS_of = @CAP.HS_of.
Proof. unfold HS_of. rewrite ?L_CAPL_meet_all, ?L_CAPL_leaves_of. reflexivity. Qed.

Lemma L_CAPL_regs_diff : @regs_diff = @CAP.regs_diff.
Proof. unfold regs_diff. rewrite ?AX2L.L_AX2L_expr_eqb. reflexivity. Qed.

Lemma L_CAPL_acs_diff : @acs_diff = @CAP.acs_diff.
Proof. unfold acs_diff. rewrite ?L_CAPL_kn_meet, ?L_CAPL_regs_diff, ?APCL.L_APCL_afd_eqb, ?APCL.L_APCL_amap_eqb, ?AX2L.L_AX2L_expr_eqb, ?APCL.L_APCL_kn, ?APCL.L_APCL_list_eqb, ?APCL.L_APCL_pair_eqb. reflexivity. Qed.

Lemma L_CAPL_HS_ofX : @HS_ofX = @CAP.HS_ofX.
Proof. unfold HS_ofX. rewrite ?L_CAPL_hxm_additions, ?L_CAPL_meet_all, ?L_CAPL_leaves_of, ?APCL.L_APCL_kn, ?APCL.L_APCL_set_kn. reflexivity. Qed.

Lemma L_CAPL_HS_ofXv : @HS_ofXv = @CAP.HS_ofXv.
Proof. unfold HS_ofXv. rewrite ?L_CAPL_hxm_additions_b, ?L_CAPL_meet_all, ?L_CAPL_leaves_of, ?APCL.L_APCL_bump, ?APCL.L_APCL_kn, ?APCL.L_APCL_nxt, ?APCL.L_APCL_set_kn, ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

Lemma L_CAPL_HS_reportXv : @HS_reportXv = @CAP.HS_reportXv.
Proof. unfold HS_reportXv. rewrite ?L_CAPL_hxm_additions_b, ?L_CAPL_meet_all, ?L_CAPL_leaves_of, ?APCL.L_APCL_kn. reflexivity. Qed.

Lemma L_CAPL_HS_checkXv : @HS_checkXv = @CAP.HS_checkXv.
Proof. unfold HS_checkXv. rewrite ?L_CAPL_leaves_of, ?L_CAPL_HS_ofXv, ?APCL.L_APCL_entails_xb. reflexivity. Qed.

Lemma L_CAPL_HS_reportX : @HS_reportX = @CAP.HS_reportX.
Proof. unfold HS_reportX. rewrite ?L_CAPL_hxm_additions, ?L_CAPL_meet_all, ?L_CAPL_leaves_of, ?APCL.L_APCL_kn. reflexivity. Qed.

Lemma L_CAPL_HS_checkX : @HS_checkX = @CAP.HS_checkX.
Proof. unfold HS_checkX. rewrite ?L_CAPL_leaves_of, ?L_CAPL_HS_ofX, ?APCL.L_APCL_entails_x. reflexivity. Qed.

End CAPL.
