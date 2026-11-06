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
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import PropExec.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import AxSymExec3.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Export AsanPlanCore.
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
| XUnwind.     (* [comment removed for export] *)
(* [comment removed for export] *)

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
| PLib (k : plan)                             (* [comment removed for export] *)
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
| PBytes (b : expr) (off : Z) (n : nat) (k : plan)  (* [comment removed for export] *)
| PJoinV (b : expr) (off : Z) (n : nat) (k : plan)  (* [comment removed for export] *)
| PZones (e : expr) (k : plan)                     (* [comment removed for export] *)
| PZoneHull (e : expr) (k : plan)                  (* [comment removed for export] *)
| PVisCut (b : expr) (N n1 : Z) (k : plan)         (* [comment removed for export] *)
| PFactC (K : kentry) (s : Z) (cert : list (Z * expr)) (k : plan)    (* [comment removed for export] *)
| PZonesD (e : expr) (joinpc : Z) (rs : list nat) (m : nat) (k : plan)   (* [comment removed for export] *)
| PIntroEq (wit : expr) (lo hi : Z) (k : plan)                      (* [comment removed for export] *)
| PGhostCover (L : list (expr * expr)) (al : list (nat * expr)) (k : plan)  (* [comment removed for export] *)
| PCaseDisjD (b1 b2 : expr) (joinpc : Z) (rs : list nat) (m : nat) (k : plan)  (* [comment removed for export] *)
| PKeepOnly (bs : list expr) (rs : list (Z * Z)) (k : plan)   (* [comment removed for export] *)
| PTail (t : nat)                                 (* [comment removed for export] *)
| PNameWord (b : expr) (lo hi : Z) (k : plan)     (* [comment removed for export] *)
| PCompactFrom (b : nat) (k : plan)              (* [comment removed for export] *)
| PDiamondX (joinpc : Z) (rs : list nat) (opsa opsb : list (nat * list expr)) (k : plan)
                                                (* [comment removed for export] *)
| PRunF (n : nat) (stops : list Z) (k : plan)    (* [comment removed for export] *)
| PTailF (t : nat)                               (* [comment removed for export] *)
| PFullTail (k : plan).                          (* [comment removed for export] *)

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
  match x with
  | XIMemset => summary_fill A nx0 cs (x_imemset A) 256       (* [comment removed for export] *)
  | XMemset => match args with
               | [] => summary_fill A nx0 cs (x_memset A) two64
               | [p; q] => summary_fill0 A nx0 cs (x_memset A) two64 p q   (* [comment removed for export] *)
               | _ => None
               end
  | XIMemcpy => summary_copy segs A nx0 cs (x_imemcpy A)
  | XMemcpy => summary_copy segs A nx0 cs (x_memcpy A)
  | XMemIsZero => summary_miz A nx0 cs
  | XEnvScan => node_envscan A cs
  | XPnScan => node_pnscan A nx0 cs
  | XLayout => node_layout cs args
  | XIStrncpy => summary_istrncpy A nx0 cs
  | XPopFree => summary_popfree A nx0 cs args
  | XUnwind => None   (* [comment removed for export] *)
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Inductive cres : Type := COk (s : shape) | CErr (code : Z) (where_ : plan) (cs : acs).

(* [comment removed for export] *)
Definition is_full (p : plan) : bool := match p with PFullTail _ => true | _ => false end.

(* [comment removed for export] *)
Fixpoint run_arms (run1 : acs -> option acs) (css : list acs) : sum (list acs) acs :=
  match css with
  | [] => inl []
  | c :: r => match run1 c with
              | Some ca => match run_arms run1 r with inl l => inl (ca :: l) | inr bad => inr bad end
              | None => inr c
              end
  end.

Section Check.
Variable XN : nat -> list expr -> acs -> option acs.                      (* [comment removed for export] *)
Variable XE : nat -> list expr -> acs -> option (Z * list spiece * acs).  (* [comment removed for export] *)
Variable XB : nat -> list expr -> acs -> option (acs * acs).              (* [comment removed for export] *)
Variable XL : acs -> option acs.                                           (* [comment removed for export] *)
Variable HS : nat -> option acs.   (* [comment removed for export] *)
Variable HL : nat -> option nat.   (* [comment removed for export] *)
Variable TT : nat -> option (acs * plan * shape).   (* [comment removed for export] *)
Variable KC : nat.                 (* [comment removed for export] *)
Variable bfuel : nat.              (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition hole_eqv (h1 h2 : nat) : bool :=
  Nat.eqb h1 h2 || match HL h1, HL h2 with Some a, Some b => Nat.eqb a b | _, _ => false end.
Fixpoint shape_eqb_h (x y : shape) : bool :=
  match x, y with
  | SNil, SNil => true
  | SExit c, SExit c' => Z.eqb c c'
  | SEmitP fd ps s, SEmitP fd' ps' s' => Z.eqb fd fd' && spieces_eqb ps ps' && shape_eqb_h s s'
  | SAlt2 a b, SAlt2 a' b' => shape_eqb_h a a' && shape_eqb_h b b'
  | SCase e m a b, SCase e' m' a' b' => expr_eqb e e' && Z.eqb m m' && shape_eqb_h a a' && shape_eqb_h b b'
  | SHole h, SHole h' => hole_eqv h h'
  | SNext, SNext => true
  | _, _ => false
  end.
(* [comment removed for export] *)
Fixpoint shape_norm (x : shape) : shape :=
  match x with
  | SEmitP fd ps s => SEmitP fd ps (shape_norm s)
  | SAlt2 a b => let a' := shape_norm a in let b' := shape_norm b in if shape_eqb_h a' b' then a' else SAlt2 a' b'
  | SCase e m a b => SCase e m (shape_norm a) (shape_norm b)
  | _ => x
  end.
Definition shape_eqv (x y : shape) : bool := shape_eqb_h (shape_norm x) (shape_norm y).

(* [comment removed for export] *)
Definition entails_t (gcb : nat) (cs : acs) (T : acs) : bool := entails_t0 A nx0 cs T.

(* [comment removed for export] *)
Definition check_all (chk : acs -> plan -> cres) (k : plan) (css : list acs) : cres :=
  match css with
  | [] => CErr 3 k (init_acs_of A)
  | cs0 :: rest =>
      match chk cs0 k with
      | COk s0 =>
          fold_left (fun acc cs => match acc with
                                   | COk s => match chk cs k with
                                              | COk s' => if shape_eqv s s' then COk s else CErr 6 k cs
                                              | err => err
                                              end
                                   | err => err
                                   end) rest (COk s0)
      | err => err
      end
  end.

(* [comment removed for export] *)
Fixpoint apply_ops (ops : list (nat * list expr)) (cs : acs) : option acs :=
  match ops with
  | [] => Some cs
  | (id, args) :: r =>
      match XN id args cs with
      | Some cs' => if Nat.leb (nxt cs) (nxt cs') then apply_ops r cs' else None
      | None => None
      end
  end.
(* [comment removed for export] *)
Definition apply_ops_from (nx : nat) (ops : list (nat * list expr)) (cs : acs) : option acs :=
  if Nat.leb nx (nxt cs) then apply_ops ops cs else None.

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
      match run_block_gc segs IT A gcb KC bfuel (stops ++ STOPS A) cs with
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
            if kn_contraM (kn cs1) then check f cs2 k2          (* [comment removed for export] *)
            else if kn_contraM (kn cs2) then check f cs1 k1
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
      | Some (Some csa, Some csb) =>
          match check f csa k1 with
          | COk s1 => match check f csb k2 with
                      | COk s2 => if shape_eqv s1 s2 then COk s1 else CErr 6 p cs
                      | err => err
                      end
          | err => err
          end
      | Some (Some csa, None) => check f csa k1     (* [comment removed for export] *)
      | Some (None, Some csb) => check f csb k2
      | _ => CErr 3 p cs
      end
  | PShDisj b1 n1 b2 n2 k => match node_shdisj A cs b1 n1 b2 n2 with Some cs' => check f cs' k | None => CErr 3 p cs end
  | PContra => if kn_contraM (kn cs) then COk SNil else CErr 3 p cs
  | PFact K k => if (if fact_okM (kn cs) K then true else fact_okKM (kn cs) K) then check f (add_kn cs [K]) k else CErr 3 p cs   (* [comment removed for export] *)
  | PJoin b off n k => match node_join segs cs b off n with Some cs' => check f cs' k | None => CErr 3 p cs end
  | PForget ixs k => check f (set_kn cs (drop_ixsF ixs 0 (kn cs))) k   (* [comment removed for export] *)
  | PDropRange b n k => check f (node_droprange cs b n) k
  | PGcKeep ws k => check f (set_kn cs (kn_keep (kn cs) ws)) k
  | PBump m k => match node_bump cs m with Some cs' => check f cs' k | None => CErr 3 p cs end
  | PHavoc rs k => match node_havoc nx0 cs rs with Some cs' => check f cs' k | None => CErr 3 p cs end
  | PHavocBig K k => match node_havocbig nx0 cs K with Some cs' => check f cs' k | None => CErr 3 p cs end
  | PFresh r logc base k => match node_freshM nx0 cs r logc base with Some cs' => check f cs' k | None => CErr 3 p cs end   (* [comment removed for export] *)
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
                        | COk sb => if shape_eqv sa sb then COk sa else CErr 6 p cs   (* [comment removed for export] *)
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
  | PLib k => match XL cs with Some cs' => check f cs' k | None => CErr 3 p cs end
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
      | Some ch => if entails cs ch then COk (SHole h) else CErr 3 p cs
      | None => CErr 4 p cs
      end
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
          if (Nat.eqb j j' && Z.eqb (pc cs) (pc js) && shape_vars_lt nx0 sk && entails_h A lo (nxt js) cs js)%bool
          then COk sk else CErr 3 p cs
      | _ => CErr 8 p cs
      end
  | PAbstractCell b n k => match node_abstractcell A cs b n with Some cs' => check f cs' k | None => CErr 3 p cs end
  | PBytes b off n k => match node_bytes cs b off n with Some cs' => check f cs' k | None => CErr 3 p cs end
  | PJoinV b off n k => match node_joinv nx0 cs b off n with Some cs' => check f cs' k | None => CErr 3 p cs end
  | PZones e k => match node_zones A cs e with Some css => check_all (check f) k css | None => CErr 3 p cs end
  | PZoneHull e k => match node_zonehull A cs e with Some cs' => check f cs' k | None => CErr 3 p cs end
  | PVisCut b N n1 k => match node_viscut LIMIT cs b N n1 with Some cs' => check f cs' k | None => CErr 3 p cs end
  | PFactC K s cert k => if fact_okC (kn cs) K s cert then check f (add_kn cs [K]) k else CErr 3 p cs
  | PZonesD e joinpc rs m k =>
      match node_zones A cs e with
      | Some css =>
          match run_arms (fun c => match run_block_gc segs IT A gcb KC bfuel (joinpc :: STOPS A) c with
                                   | Some ca => if Z.eqb (pc ca) joinpc then Some ca else None
                                   | None => None
                                   end) css with
          | inl arms => match node_zjoin A nx0 (nxt cs) m joinpc rs arms with
                        | Some csj => check f csj k
                        | None => CErr 3 p (hd cs arms)   (* [comment removed for export] *)
                        end
          | inr c => CErr 1 p c                     (* [comment removed for export] *)
          end
      | None => CErr 3 p cs
      end
  | PIntroEq wit lo hi k => match node_introeq nx0 cs wit lo hi with Some cs' => check f cs' k | None => CErr 3 p cs end
  | PGhostCover L al k => match node_ghostcover LIMIT cs L al with Some cs' => check f cs' k | None => CErr 3 p cs end
  | PCaseDisjD b1 b2 joinpc rs m k =>
      match node_casedisj cs b1 b2 with
      | Some (xa, xb) =>
          let css := match xa with Some c => [c] | None => [] end ++ match xb with Some c => [c] | None => [] end in
          match run_arms (fun c => match run_block_gc segs IT A gcb KC bfuel (joinpc :: STOPS A) c with
                                   | Some ca => if Z.eqb (pc ca) joinpc then Some ca else None
                                   | None => None
                                   end) css with
          | inl arms => match node_zjoin A nx0 (nxt cs) m joinpc rs arms with
                        | Some csj => check f csj k
                        | None => CErr 3 p (hd cs arms)
                        end
          | inr c => CErr 1 p c
          end
      | None => CErr 3 p cs
      end
  | PHavocWords bs k => match node_havocwords nx0 cs bs with Some cs' => check f cs' k | None => CErr 3 p cs end
  | PRespell r e k => match node_respellM cs r e with Some cs' => check f cs' k | None => CErr 3 p cs end   (* [comment removed for export] *)
  | PDiamond joinpc rs k =>
      match branch_probe IT cs with
      | Some e =>
          match erange (kn cs) e with
          | Some (lo, hi) =>
              (* [comment removed for export] *)
              if (Z.ltb hi 1 || Z.ltb 0 lo)%bool then
                match run_block_gc segs IT A gcb KC bfuel (joinpc :: STOPS A) cs with
                | Some cs' => if Z.eqb (pc cs') joinpc then check f cs' k else CErr 3 p cs'
                | None => CErr 1 p cs
                end
              else
                let cs1 := set_kn cs (KRange e lo 0 :: kn cs) in
                let cs2 := set_kn cs (KRange e 1 hi :: kn cs) in
                match run_block_gc segs IT A gcb KC bfuel (joinpc :: STOPS A) cs1 with
                | Some ca =>
                    match run_block_gc segs IT A gcb KC bfuel (joinpc :: STOPS A) cs2 with
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
  | PKeepOnly bs rs k => check f (set_kn cs (kn_keeponly (kn cs) bs rs)) k     (* [comment removed for export] *)
  | PTail t =>                                                            (* [comment removed for export] *)
      match TT t with
      | Some (T, pt, s) => if (if is_full pt then false else entails_t gcb cs T) then COk s else CErr 3 p cs   (* [comment removed for export] *)
      | None => CErr 4 p cs
      end
  | PNameWord b lo hi k => match node_nameword nx0 cs b lo hi with Some cs' => check f cs' k | None => CErr 3 p cs end   (* [comment removed for export] *)
  | PCompactFrom b k => match node_compact (Nat.max gcb b) cs with Some cs' => check f cs' k | None => CErr 3 p cs end   (* [comment removed for export] *)
  | PRunF n stops k =>                                                                                                 (* [comment removed for export] *)
      match run_block_gc segs IT A gcb KC (Nat.min n bfuel) (stops ++ STOPS A) cs with
      | Some cs' => check f cs' k
      | None => CErr 1 p cs
      end
  | PTailF t =>                                                                                                        (* [comment removed for export] *)
      match TT t with
      | Some (T, pt, s) => if (if is_full pt then (if shape_vars_lt nx0 s then entails cs T else false) else false) then COk s else CErr 3 p cs
      | None => CErr 4 p cs
      end
  | PFullTail k => check f cs k                                                                                        (* [comment removed for export] *)
  | PDiamondX joinpc rs opsa opsb k =>                                                                                 (* [comment removed for export] *)
      match branch_probe IT cs with
      | Some e =>
          match erange (kn cs) e with
          | Some (lo, hi) =>
              if (Z.ltb hi 1 || Z.ltb 0 lo)%bool then
                match run_block_gc segs IT A gcb KC bfuel (joinpc :: STOPS A) cs with
                | Some cs' =>
                    if Z.eqb (pc cs') joinpc then
                      match apply_ops_from (nxt cs) (if Z.ltb hi 1 then opsa else opsb) cs' with
                      | Some cs'' => check f cs'' k
                      | None => CErr 3 p cs'
                      end
                    else CErr 3 p cs'
                | None => CErr 1 p cs
                end
              else
                let cs1 := set_kn cs (KRange e lo 0 :: kn cs) in
                let cs2 := set_kn cs (KRange e 1 hi :: kn cs) in
                match run_block_gc segs IT A gcb KC bfuel (joinpc :: STOPS A) cs1 with
                | Some ca0 =>
                    match run_block_gc segs IT A gcb KC bfuel (joinpc :: STOPS A) cs2 with
                    | Some cb0 =>
                        match apply_ops_from (nxt cs) opsa ca0, apply_ops_from (nxt cs) opsb cb0 with
                        | Some ca, Some cb =>
                            match node_diamond_join A nx0 (nxt cs) joinpc rs ca cb with
                            | Some csj => check f csj k
                            | None => CErr 3 p ca
                            end
                        | None, _ => CErr 3 p ca0
                        | _, None => CErr 3 p cb0
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

(* [comment removed for export] *)
Definition TBFUEL : nat := 100000.
Definition tail_x (x : xnode) : bool := match x with XIMemset | XMemset | XIMemcpy | XMemcpy => true | _ => false end.
Definition tstep (rec : acs -> plan -> option shape) (cs c : acs) (k : plan) : option shape :=
  if Nat.leb (nxt cs) (nxt c) then rec (tw (a_ss c)) k else None.
Fixpoint checkT_go (cs : acs) (p : plan) {struct p} : option shape :=
  let step := tstep checkT_go cs in
  match p with
  | PRun stops k =>
      match run_block segs IT A nx0 KC TBFUEL (stops ++ STOPS A) cs with
      | Some c => step (ss_gc nx0 (tw (a_ss c))) k
      | None => None
      end
  | PCase2 e mid k1 k2 =>
      match erange (kn cs) e with
      | Some (lo, hi) =>
          if negb (Z.leb lo mid && Z.ltb mid hi)%bool then (if Z.leb hi mid then checkT_go cs k1 else checkT_go cs k2) else
          let cs1 := set_kn cs (KRange e lo mid :: kn cs) in
          let cs2 := set_kn cs (KRange e (mid + 1) hi :: kn cs) in
          if kn_contra (kn cs1) then step cs2 k2
          else if kn_contra (kn cs2) then step cs1 k1
          else match step cs1 k1, step cs2 k2 with
               | Some s1, Some s2 => if shape_eqb s1 s2 then Some s1 else None
               | _, _ => None
               end
      | None => None
      end
  | PFact K k => if (fact_ok (kn cs) K || fact_okK (kn cs) K)%bool then step (add_kn cs [K]) k else None
  | PKeepOnly bs rs k => step (set_kn cs (kn_keeponly (kn cs) bs rs)) k
  | PBump m k => match node_bump cs m with Some c => step c k | None => None end
  | PHavoc rs k => match node_havoc nx0 cs rs with Some c => step c k | None => None end
  | PFresh r logc base k => match node_fresh nx0 cs r logc base with Some c => step c k | None => None end
  | PDiamond joinpc rs k =>
      match branch_probe IT cs with
      | Some e =>
          match erange (kn cs) e with
          | Some (lo, hi) =>
              if (Z.ltb hi 1 || Z.ltb 0 lo)%bool then
                match run_block segs IT A nx0 KC TBFUEL (joinpc :: STOPS A) cs with
                | Some c => if Z.eqb (pc c) joinpc then step (ss_gc nx0 (tw (a_ss c))) k else None
                | None => None
                end
              else
                let cs1 := set_kn cs (KRange e lo 0 :: kn cs) in
                let cs2 := set_kn cs (KRange e 1 hi :: kn cs) in
                match run_block segs IT A nx0 KC TBFUEL (joinpc :: STOPS A) cs1, run_block segs IT A nx0 KC TBFUEL (joinpc :: STOPS A) cs2 with
                | Some ca, Some cb =>
                    let ga := ss_gc nx0 (tw (a_ss ca)) in let gb := ss_gc nx0 (tw (a_ss cb)) in
                    match node_diamond_join A nx0 (nxt cs) joinpc rs (tw (a_ss ga)) (tw (a_ss gb)) with
                    | Some csj => step csj k
                    | None => None
                    end
                | _, _ => None
                end
          | None => None
          end
      | None => None
      end
  | PX x args k =>      (* [comment removed for export] *)
      match args with
      | [] => if tail_x x then match node_x x [] cs with Some c => step c k | None => None end else None
      | _ => None
      end
  | PContra => if kn_contra (kn cs) then Some SNil else None
  | PSpin => if node_spin segs cs then Some SNil else None
  | PExit => if is_ecall_at segs cs then match node_exit cs with Some code => Some (SExit code) | None => None end else None
  | _ => None
  end.
(* [comment removed for export] *)
Definition checkT (T : acs) (p : plan) : option shape :=
  let _ := LIMIT in   (* [comment removed for export] *)
  let ss := a_ss T in
  if (match s_log ss with [] => true | _ => false end && match s_resv ss with None => true | _ => false end
      && Nat.eqb (length (s_regs ss)) 32 && fresh_ok nx0 (tw ss))%bool
  then match checkT_go (tw ss) p with
       | Some s => if shape_vars_lt nx0 s then Some s else None
       | None => None
       end
  else None.
Definition tails_ok : Prop := forall t T p s, TT t = Some (T, p, s) -> is_full p = false -> checkT T p = Some s.   (* [comment removed for export] *)
End Check.

(* [comment removed for export] *)
Definition TT_none : nat -> option (acs * plan * shape) := fun _ => None.
(* [comment removed for export] *)
Definition tails_nofull (TT : nat -> option (acs * plan * shape)) : Prop := forall t T p s, TT t = Some (T, p, s) -> is_full p = false.
Definition tails_ok0 (TT : nat -> option (acs * plan * shape)) (KC : nat) : Prop := tails_ok TT KC /\ tails_nofull TT.
Lemma tails_ok_none : forall KC, tails_ok0 TT_none KC.
Proof. intros KC. split; intros t T p s H; discriminate H. Qed.
(* [comment removed for export] *)
Definition tt_of_list (TL : list (acs * plan * shape)) : nat -> option (acs * plan * shape) := fun t => nth_error TL t.
Definition tails_okb (KC : nat) (TL : list (acs * plan * shape)) : bool :=
  forallb (fun e : acs * plan * shape => let '(T, p, s) := e in
                                         if is_full p then true else   (* [comment removed for export] *)
                                         match checkT KC T p with Some s' => shape_eqb s s' | None => false end) TL.
(* [comment removed for export] *)

End WithSegs.
End AP.
