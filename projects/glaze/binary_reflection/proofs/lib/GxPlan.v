(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import PropExec.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import GxSymExec3.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Export GxPlanCore.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

Module AP.
(* [comment removed for export] *)
#[local] Notation "a || b" := (if a then true else b) (at level 50, left associativity, only parsing) : bool_scope.
Include APC.
Import AX2.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

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
| YSetTid.     (* [comment removed for export] *)

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
| PMmap (krefused kgranted : plan)           (* [comment removed for export] *)
| PMmapIn (kkept kok kdestroyed : plan)      (* [comment removed for export] *)
| PMprotect (krefused kgranted : plan)       (* [comment removed for export] *)
| PBrk2 (kblocked kgranted : plan)           (* [comment removed for export] *)
| PX (x : xnode) (args : list expr) (k : plan)   (* [comment removed for export] *)
| PExt (id : nat) (args : list expr) (k : plan)  (* [comment removed for export] *)
| PEmit (id : nat) (args : list expr) (k : plan) (* [comment removed for export] *)
| PExt2 (id : nat) (args : list expr) (k1 k2 : plan) (* [comment removed for export] *)
| PLoop (J : nat) (N : expr) (inv : acs) (w : list (nat * expr)) (body k : plan)  (* [comment removed for export] *)
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
(* [comment removed for export] *)
| PNextW (w : list (nat * expr))              (* [comment removed for export] *)
| PMergeW (j : nat) (w : list (nat * expr))   (* [comment removed for export] *)
| PBranch (kfall ktaken : plan)               (* [comment removed for export] *)
| PCaseReg (r : nat) (mid : Z) (k1 k2 : plan)  (* [comment removed for export] *)
| PFactVia (e via : expr) (lo hi : Z) (k : plan)  (* [comment removed for export] *)
| PHandoffW (h : nat) (w : list (nat * expr))   (* [comment removed for export] *)
| PFactLe (e big : expr) (hi : Z) (k : plan)    (* [comment removed for export] *)
| PFactScale (e : expr) (c hi : Z) (k : plan)  (* [comment removed for export] *)
| PFactLeR (r : nat) (off : Z) (big : expr) (hi : Z) (k : plan)  (* [comment removed for export] *)
| PFactR (r : nat) (off : Z) (lo hi : Z) (k : plan)             (* [comment removed for export] *)
| PFactLeX (r ph : nat) (e big : expr) (hi : Z) (k : plan)      (* [comment removed for export] *)
| PFactX (r ph : nat) (e : expr) (lo hi : Z) (k : plan)         (* [comment removed for export] *)
| PContraH (h : nat)                                             (* [comment removed for export] *)
(* [comment removed for export] *)
| PLoopM (J : nat) (N : expr) (alts : list (acs * plan * plan)) (w : list (nat * expr))
                                                (* [comment removed for export] *)
| PViaM (j : nat) (alts : list (acs * plan)) (lo : nat) (karms : plan)
| PBranchP (k0 k1 : plan)                       (* [comment removed for export] *)
| PAlt2X (id : nat) (args : list expr) (k1 k2 : plan).  (* [comment removed for export] *)
                                                (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition node_sys (y : snode) (cs : acs) : option acs :=
  match y with
  | YMunmap => node_munmap A cs
  | YBrk => node_brk1 A cs
  | YSetTid => node_settid nx0 cs
  end.

Definition node_x (x : xnode) (args : list expr) (cs : acs) : option acs :=
  (* [comment removed for export] *)
  let _ := segs in let _ := A in let _ := nx0 in None.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Inductive cres : Type := COk (s : shape) | CErr (code : Z) (where_ : plan) (cs : acs).

(* [comment removed for export] *)
Definition xhookN : Type := nat -> list expr -> acs -> option acs.
Definition xhookE : Type := nat -> list expr -> acs -> option (Z * list spiece * acs).
Definition xhookB : Type := nat -> list expr -> acs -> option (acs * acs).

Section Check.
Variable XN : nat -> list expr -> acs -> option acs.                      (* [comment removed for export] *)
Variable XE : nat -> list expr -> acs -> option (Z * list spiece * acs).  (* [comment removed for export] *)
Variable XB : nat -> list expr -> acs -> option (acs * acs).              (* [comment removed for export] *)
Variable XC : xhookB.                                                     (* [comment removed for export] *)
Variable HS : nat -> option acs.   (* [comment removed for export] *)
Variable KC : nat.                 (* [comment removed for export] *)
Variable bfuel : nat.              (* [comment removed for export] *)

(* [comment removed for export] *)
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
Fixpoint next_or_holes (s : shape) : bool :=
  match s with
  | SNext | SHole _ => true
  | SCase _ _ a b => next_or_holes a && next_or_holes b
  | _ => false
  end%bool.
Fixpoint holes_only (s : shape) : bool :=
  match s with
  | SHole _ => true
  | SCase _ _ a b => holes_only a && holes_only b
  | _ => false
  end%bool.

(* [comment removed for export] *)
Definition check_next (lc : option loopctx) (cs : acs) (p : plan) (w : list (nat * expr)) : cres :=
  match lc with
  | Some (LC h nxs lo hi _) =>
      if (Z.eqb (pc cs) h && existsbL (fun nx => entails_tw A lo hi w cs nx) nxs)%bool then COk SNext else CErr 3 p cs
  | _ => CErr 8 p cs
  end.
Definition check_merge (lc : option loopctx) (cs : acs) (p : plan) (j : nat) (w : list (nat * expr)) : cres :=
  match lc with
  | Some (JC j' jss sk b lo _) =>
      if (Nat.eqb j j' && shape_vars_lt nx0 sk
          && existsbL (fun js => Z.eqb (pc cs) (pc js) && entails_tw A lo (nxt js) w cs js) jss)%bool
      then COk sk else CErr 3 p cs
  | _ => CErr 8 p cs
  end.
Definition check_handoff (lc : option loopctx) (cs : acs) (p : plan) (h : nat) (w : list (nat * expr)) : cres :=
  match HS h with
  | Some ch =>
      if (entails cs ch || entails_tw A nx0 (nxt ch) w cs ch)%bool
      then COk (if lc_xmode lc then SNext else SHole h) else CErr 3 p cs
  | None => CErr 4 p cs
  end.
(* [comment removed for export] *)
Definition shape_eqv (s1 s2 : shape) : bool := (shape_eqb s1 s2 || (holes_only s1 && holes_only s2))%bool.

(* [comment removed for export] *)
Definition lc_raise (lc : option loopctx) (b : nat) : option loopctx :=
  match lc with
  | None => Some (LC 0 [] b b false)
  | Some (LC h nxs lo hi x) => Some (LC h nxs lo (Nat.max hi b) x)
  | Some (JC _ _ _ _ _ _) => lc
  end.
(* [comment removed for export] *)
Fixpoint check_each (chk : acs -> plan -> cres) (p : plan) (cs0 : acs) (css : list (acs * plan)) : cres :=
  match css with
  | [] => CErr 3 p cs0
  | [(cs, k)] => chk cs k
  | (cs, k) :: rest =>
      match chk cs k with
      | COk s => match check_each chk p cs0 rest with
                 | COk s' => if shape_eqv s s' then COk s else CErr 6 p cs
                 | err => err
                 end
      | err => err
      end
  end.
(* [comment removed for export] *)
Fixpoint check_bodies (chk : acs -> plan -> cres) (p : plan) (cs0 : acs) (css : list (acs * plan)) : cres :=
  match css with
  | [] => COk SNext
  | (cs, b) :: rest => match chk cs b with
                       | COk SNext => check_bodies chk p cs0 rest
                       | COk _ => CErr 7 p cs0
                       | err => err
                       end
  end.
Definition lalt := (acs * plan * plan)%type.   (* [comment removed for export] *)
Definition la_inv (a : lalt) : acs := fst (fst a).
Definition la_body (a : lalt) : plan := snd (fst a).
Definition la_k (a : lalt) : plan := snd a.
Definition loop_okM (cs : acs) (J : nat) (N : expr) (alts : list lalt) : option Z :=
  match alts with
  | [] => None
  | a0 :: _ =>
      if forallb (fun a => Z.eqb (pc (la_inv a)) (pc cs) && Nat.eqb (nxt (la_inv a)) (nxt (la_inv a0))
                           && match loop_ok nx0 cs J N (la_inv a) with Some _ => true | None => false end) alts
      then loop_ok nx0 cs J N (la_inv a0) else None
  end.
(* [comment removed for export] *)
Definition loop_start (w : list (nat * expr)) (J : nat) : expr :=
  match tb_get w J with Some e => e | None => ELit 0 end.
Definition start_ok (cs : acs) (N e0 : expr) : bool :=
  match e0 with
  | ELit Z0 => true
  | _ => (expr_vars_lt (nxt cs) e0 && lin_ge0 (kn cs) [(N, 0%Z)] [(e0, 0%Z)])%bool
  end.
Definition check_loop (chk : option loopctx -> acs -> plan -> cres) (lc : option loopctx) (cs : acs) (p : plan)
           (J : nat) (N : expr) (alts : list lalt) (w : list (nat * expr)) : cres :=
  match loop_okM cs J N alts, alts with
  | Some nhi, a0 :: _ =>
      let lo := S J in let hi := nxt (la_inv a0) in
      let e0 := loop_start w J in
      if (start_ok cs N e0 && existsbL (fun a => entails_tw A lo hi w cs (inst (la_inv a) J e0)) alts)%bool then
        (* [comment removed for export] *)
        match check_each (fun js k => chk (lc_raise lc (nxt js)) js k) p cs (map (fun a => (inst (la_inv a) J N, la_k a)) alts) with
        | COk sk =>
            (* [comment removed for export] *)
            let xm := (holes_only sk || (lc_xmode lc && next_or_holes sk))%bool in
            let lc' := Some (LC (pc cs) (map (fun a => inst (la_inv a) J (eaddz (EVar J) 1)) alts) lo hi xm) in
            match check_bodies (chk lc') p cs (map (fun a => (loop_body_state J N nhi (la_inv a), la_body a)) alts) with
            | COk SNext => COk (if (lc_xmode lc && next_or_holes sk)%bool then SNext else sk)
            | COk _ => CErr 7 p cs
            | err => err
            end
        | err => err
        end
      else CErr 3 p cs
  | _, _ => CErr 3 p cs
  end.
Definition check_via (chk : option loopctx -> acs -> plan -> cres) (lc : option loopctx) (cs : acs) (p : plan)
           (j : nat) (alts : list (acs * plan)) (lo : nat) (karms : plan) : cres :=
  if (forallb (fun a => via_ok nx0 cs (fst a) lo) alts && match alts with [] => false | _ => true end)%bool then
    match check_each (fun js k => chk (lc_raise lc (nxt js)) js k) p cs alts with
    | COk sk => chk (Some (JC j (map fst alts) sk (nxt cs) lo (lc_xmode lc))) cs karms
    | err => err
    end
  else CErr 3 p cs.

(* [comment removed for export] *)
Definition check_branch (chk : acs -> plan -> cres) (cs : acs) (p : plan) (e : expr) (k1 k2 : plan) : cres :=
  match brange (kn cs) e with
          | Some (lo, hi) =>
              if negb (Z.leb lo 0 && Z.ltb 0 hi)%bool then (if Z.leb hi 0 then chk cs k1 else chk cs k2) else
              if (Z.leb lo 0 && Z.ltb 0 hi)%bool then
                let cs1 := set_kn cs (KRange e lo 0 :: probe_lin_facts (kn cs) e false ++ kn cs) in
                let cs2 := set_kn cs (KRange e (0 + 1) hi :: probe_lin_facts (kn cs) e true ++ kn cs) in
                if kn_contra (kn cs1) then chk cs2 k2
                else if kn_contra (kn cs2) then chk cs1 k1
                else
                match chk cs1 k1 with
                | COk s1 =>
                    match chk cs2 k2 with
                    | COk s2 => if shape_eqv s1 s2 then COk s1 else CErr 6 p cs
                    | err => err
                    end
                | err => err
                end
              else CErr 3 p cs
          | None => CErr 3 p cs
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
      match brange (kn cs) e with
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
      match brange (kn cs) e with
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
                | COk s2 => if shape_eqv s1 s2 then COk s1 else CErr 6 p cs
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
                      | COk s2 => if shape_eqv s1 s2 then COk s1 else CErr 6 p cs
                      | err => err
                      end
          | err => err
          end
      | None => CErr 3 p cs
      end
  | PShDisj b1 n1 b2 n2 k => match node_shdisj A cs b1 n1 b2 n2 with Some cs' => check f cs' k | None => CErr 3 p cs end
  | PContra => if kn_contra (kn cs) then COk SNil else CErr 3 p cs
  | PFact K k => if fact_okM (kn cs) K then check f (add_kn cs [K]) k else CErr 3 p cs
  | PJoin b off n k => match node_join segs cs b off n with Some cs' => check f cs' k | None => CErr 3 p cs end
  | PForget ixs k => check f (set_kn cs (drop_ixs ixs 0 (kn cs))) k
  | PDropRange b n k => check f (node_droprange cs b n) k
  | PGcKeep ws k => check f (set_kn cs (kn_keep (kn cs) ws)) k
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
        match node_brk2 A LIMIT cs with
        | Some (csa, csb) =>
            match check f csa ka with
            | COk sa => match check f csb kb with
                        | COk sb => COk (salt2 sa sb)
                        | err => err
                        end
            | err => err
            end
        | None => CErr 3 p cs
        end
      else CErr 2 p cs
  | PMmap ka kb =>
      if is_ecall_at segs cs then
        match node_mmap2 A nx0 LIMIT cs with
        | Some (csa, csb) =>
            match check f csa ka with
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
            match check f csa ka with
            | COk sa => match check f csb kb with
                        | COk sb => match check_all (check f) kc cscs with
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
  | PMmapInH ka kb kc =>      (* [comment removed for export] *)
      if is_ecall_at segs cs then
        match node_mmapin A LIMIT true cs with
        | Some (csa, csb, cscs) =>
            match check f csa ka with
            | COk sa => match check f csb kb with
                        | COk sb => match check_all (check f) kc cscs with
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
            match check f csa ka with
            | COk sa => match check f csb kb with
                        | COk sb => COk (salt2 sa sb)
                        | err => err
                        end
            | err => err
            end
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
      (* [comment removed for export] *)
      match XB id args cs with
      | Some (csa, csb) =>
          (* [comment removed for export] *)
          if kn_contra (kn csa) then check f csb k2
          else if kn_contra (kn csb) then check f csa k1
          else
          match check f csa k1 with
          | COk sa => match check f csb k2 with
                     | COk sb => if shape_eqv sa sb then COk sa else CErr 6 p cs
                     | err => err
                     end
          | err => err
          end
      | None => CErr 3 p cs
      end
  | PAlt2X id args k1 k2 =>
      (* [comment removed for export] *)
      match XC id args cs with
      | Some (csa, csb) =>
          match check f csa k1 with
          | COk sa => match check f csb k2 with
                     | COk sb => COk (if shape_eqb sa sb then sa else salt2 sa sb)
                     | err => err
                     end
          | err => err
          end
      | None => CErr 3 p cs
      end
  | PLoop J N inv w body k => check_loop (check_in f) lc cs p J N [(inv, body, k)] w
  | PLoopM J N alts w => check_loop (check_in f) lc cs p J N alts w
  | PNext => check_next lc cs p []
  | PHandoff h => check_handoff lc cs p h []
  | PExit =>
      if is_ecall_at segs cs then
        match node_exit cs with Some code => COk (SExit code) | None => CErr 3 p cs end
      else CErr 2 p cs
  | PSpin => if node_spin segs cs then COk SNil else CErr 2 p cs
  | PFog i sz k => match node_fog cs i sz with Some cs' => check f cs' k | None => CErr 3 p cs end
  | PFogNew i sz k => match node_fognew cs i sz with Some cs' => check f cs' k | None => CErr 3 p cs end
  | PGhost b n k => match node_ghost LIMIT cs b n with Some cs' => check f cs' k | None => CErr 3 p cs end
  | PUnvis b n k => match node_unvis A cs b n with Some cs' => check f cs' k | None => CErr 3 p cs end
  | PHavocBrk lo hi k => match node_havocbrk nx0 cs lo hi with Some cs' => check f cs' k | None => CErr 3 p cs end
  | PIntro lo hi k => match node_intro nx0 cs lo hi with Some cs' => check f cs' k | None => CErr 3 p cs end
  | PRename m k => match node_rename gcb cs m with Some cs' => check f cs' k | None => CErr 3 p cs end
  | PCompact k => match node_compact gcb cs with Some cs' => check f cs' k | None => CErr 3 p cs end
  | PVia j js lo karms k => check_via (check_in f) lc cs p j [(js, k)] lo karms
  | PViaM j alts lo karms => check_via (check_in f) lc cs p j alts lo karms
  | PMerge j => check_merge lc cs p j []
  | PAbstractCell b n k => match node_abstractcell A cs b n with Some cs' => check f cs' k | None => CErr 3 p cs end
  | PHavocWords bs k => match node_havocwords nx0 cs bs with Some cs' => check f cs' k | None => CErr 3 p cs end
  | PRespell r e k => match node_respell cs r e with Some cs' => check f cs' k | None => CErr 3 p cs end
  | PDiamond joinpc rs k =>
      match branch_probe IT cs with
      | Some e =>
          match brange (kn cs) e with
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
  | PNextW w => check_next lc cs p w
  | PMergeW j w => check_merge lc cs p j w
  | PBranch kfall ktaken =>
      match branch_probe2 IT cs with
      | Some (e, pos) =>
          let k1 := if pos then kfall else ktaken in   (* [comment removed for export] *)
          let k2 := if pos then ktaken else kfall in   (* [comment removed for export] *)
          check_branch (check f) cs p e k1 k2
      | None => CErr 2 p cs
      end
  | PBranchP kz knz =>
      match branch_probe2 IT cs with
      | Some (e, _) => check_branch (check f) cs p e kz knz
      | None => CErr 2 p cs
      end
  | PFactVia e via lo hi k => if factvia_ok (kn cs) e via lo hi then check f (add_kn cs [KRange e lo hi]) k else CErr 3 p cs
  | PHandoffW h w => check_handoff lc cs p h w
  | PFactLe e big hi k => if factle_okM (kn cs) e big hi then check f (add_kn cs [KRange e 0 hi]) k else CErr 3 p cs
  | PFactScale e c hi k => if factscale_ok (kn cs) e c hi then check f (add_kn cs [KRange e 0 hi]) k else CErr 3 p cs
  | PFactLeR r off big hi k => let e := eaddz (reg cs r) off in
      if factle_okM (kn cs) e big hi then check f (add_kn cs [KRange e 0 hi]) k else CErr 3 p cs
  | PFactR r off lo hi k => let e := eaddz (reg cs r) off in
      if fact_okM (kn cs) (KRange e lo hi) then check f (add_kn cs [KRange e lo hi]) k else CErr 3 p cs
  | PFactLeX r ph e big hi k => let x := reg cs r in let e' := APC.esubst ph x e in let big' := APC.esubst ph x big in
      if factle_okM (kn cs) e' big' hi then check f (add_kn cs [KRange e' 0 hi]) k else CErr 3 p cs
  | PFactX r ph e lo hi k => let e' := APC.esubst ph (reg cs r) e in
      if fact_okM (kn cs) (KRange e' lo hi) then check f (add_kn cs [KRange e' lo hi]) k else CErr 3 p cs
  | PContraH h => if kn_contra (kn cs) then COk (if lc_xmode lc then SNext else SHole h) else CErr 3 p cs   (* [comment removed for export] *)
  | PCaseReg r mid k1 k2 =>
      let e := reg cs r in
      match brange (kn cs) e with
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
                | COk s2 => if shape_eqv s1 s2 then COk s1 else CErr 6 p cs
                | err => err
                end
            | err => err
            end
          else CErr 3 p cs
      | None => CErr 3 p cs
      end
  end
  end.
End Check.

End WithSegs.
End AP.
