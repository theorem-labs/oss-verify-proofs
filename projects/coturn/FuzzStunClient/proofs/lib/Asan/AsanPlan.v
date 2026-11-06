(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import PropExec.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import AxSymExec3.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Export AsanPlanCore.
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
Variable nx0 : N.       (* [comment removed for export] *)
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
| XSniff.       

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
| PMmapIn (kkept kok kdestroyed : plan)       
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
| PVia (j : nat) (js : acs) (lo : nat) (karms k : plan)   
| PMerge (j : nat)                            (* [comment removed for export] *)
| PAbstractCell (b : expr) (n : Z) (k : plan)  
| PHavocWords (bs : list expr) (k : plan)     
| PRespell (r : nat) (e : expr) (k : plan)     
| PMmapInH (kkept kok kdestroyed : plan)       
| PCaseDisjJ (b1 b2 : expr) (joinpc : Z) (rs : list nat) (k : plan)
| PCaseP (k1 k2 : plan)                      (* [comment removed for export] *)
| PCaseNJ (e : expr) (cuts : list Z) (joinpc : Z) (rs : list nat) (ws : list (expr * Z * nat)) (k : plan)
| PVisAbsorb (b n : expr) (k : plan)         (* [comment removed for export] *)
| PFreshCell (b : expr) (n : nat) (k : plan)  (* [comment removed for export] *)
| PVisSplit (b : expr) (n d : Z) (k : plan)  (* [comment removed for export] *)
| PVisHead (b : expr) (m : Z) (L : expr) (k : plan)  (* [comment removed for export] *)
| PUnvisHead (b : expr) (m : Z) (k : plan)  (* [comment removed for export] *)
| PGhostDedup (k : plan)                    (* [comment removed for export] *)
| PHavocBrkP (lo hi : Z) (k : plan)         (* [comment removed for export] *)
| PKeep (ws : list (expr * expr)) (vs : list nat) (k : plan)   (* [comment removed for export] *)
| PFactMem (K : kentry) (k : plan)           (* [comment removed for export] *)
| PVisRespell (b n b' n' : expr) (k : plan)  (* [comment removed for export] *)
| PMapRespell (b n b' n' : expr) (k : plan)  (* [comment removed for export] *)
| PMemRespell (b : expr) (lo hi : Z) (b' : expr) (d : Z) (k : plan)  (* [comment removed for export] *)
| PSrlSplit (r : nat) (s : Z) (k : plan)  (* [comment removed for export] *)
| PAndRange (r : nat) (logc : Z) (ub : expr) (k : plan)  (* [comment removed for export] *)
| PAndRangeR (r : nat) (logc : Z) (rs : nat) (k : plan)  (* [comment removed for export] *)
| PSrlSplitAll (r : nat) (s : Z) (k : plan)  (* [comment removed for export] *)
| PFdHavoc (lo hi : Z) (k : plan)  (* [comment removed for export] *)
| PFreshCellK (b : expr) (n : nat) (k : plan)  (* [comment removed for export] *)
| PVisPerm (perm : list nat) (k : plan)  (* [comment removed for export] *)
| PHandoffM (m : list (nat * nat))  (* [comment removed for export] *)
| PFdRespell (len off : expr) (k : plan)  (* [comment removed for export] *)
| PDisjNth (b1 n1 : expr) (i : nat) (k : plan)  (* [comment removed for export] *)
| PMmapInS (kkept kok kdestroyed : plan).  (* [comment removed for export] *)
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
  end.

Definition node_x (x : xnode) (args : list expr) (cs : acs) : option acs :=
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
  | XSniff => None    
  end.

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

Fixpoint check (fuel : nat) (lc : option loopctx) (cs : acs) (p : plan) {struct fuel} : cres :=
  match fuel with
  | O => CErr 0 p cs
  | S f =>
  let check_in := check in
  let check (f : nat) := check_in f lc in
  (* [comment removed for export] *)
  let gcb := match lc with Some c => lc_bnd c | None => nx0 end in
  if negb match lc with Some c => N.leb (lc_bnd c) (nxt cs) | None => true end then CErr 9 p cs else
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
  | PFact K k => if fact_okc cs K then check f (add_kn cs [K]) k else CErr 3 p cs   (* [comment removed for export] *)
  | PJoin b off n k => match node_join segs cs b off n with Some cs' => check f cs' k | None => CErr 3 p cs end
  | PForget ixs k => check f (set_kn cs (drop_ixsM ixs (kn cs))) k   (* [comment removed for export] *)
  | PDropRange b n k => check f (node_droprange cs b n) k
  | PGcKeep ws k => check f (set_kn cs (kn_keep (kn cs) ws)) k
  | PBump m k => match node_bump cs (vN m) with Some cs' => check f cs' k | None => CErr 3 p cs end
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
        | None =>
            match node_brk2s A LIMIT cs with
            | Some (csa, csb) =>
                match check f csa ka with
                | COk sa => match check f csb kb with
                            | COk sb => if shape_eqb sa sb then COk sa else CErr 5 p cs
                            | err => err
                            end
                | err => err
                end
            | None => CErr 3 p cs
            end
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
  | PMmapInH ka kb kc =>       
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
      match XB id args cs with
      | Some (csa, csb) =>
          match check f csa k1 with
          | COk sa => match check f csb k2 with COk sb => COk (SAlt2 sa sb) | err => err end
          | err => err
          end
      | None => CErr 3 p cs
      end
  | PLoop J0 N inv body k =>
      let J := vN J0 in   (* [comment removed for export] *)
      match loop_ok nx0 cs J N inv with
      | Some nhi =>
          let lo := N.succ J in let hi := nxt inv in
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
  | PRename m k => match node_rename gcb cs (vNm m) with Some cs' => check f cs' k | None => CErr 3 p cs end
  | PCompact k => match node_compact gcb cs with Some cs' => check f cs' k | None => CErr 3 p cs end
  | PVia j js lo0 karms k =>
      let lo := vN lo0 in
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
  | PCaseDisjJ b1 b2 joinpc rs k =>
      match node_casedisj cs b1 b2 with
      | Some (cs1, cs2) =>
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
  | PCaseP ck1 ck2 =>      (* [comment removed for export] *)
      match branch_probe IT cs with
      | Some ce =>
      (* [comment removed for export] *)
      match concretize (kn cs) ce with
      | Some v => if Z.eqb (v mod two64) 0 then check f cs ck1 else check f cs ck2
      | None =>
      match erange (kn cs) ce with
      | Some (lo, hi) =>
          if negb (Z.leb lo 0 && Z.ltb 0 hi)%bool then (if Z.leb hi 0 then check f cs ck1 else check f cs ck2) else
          if (Z.leb lo 0 && Z.ltb 0 hi)%bool then
            let cs1 := set_kn cs (KRange ce lo 0 :: kn cs) in
            let cs2 := set_kn cs (KRange ce (0 + 1) hi :: kn cs) in
            if kn_contra (kn cs1) then check f cs2 ck2
            else if kn_contra (kn cs2) then check f cs1 ck1
            else
            match check f cs1 ck1 with
            | COk s1 =>
                match check f cs2 ck2 with
                | COk s2 => if shape_eqb s1 s2 then COk s1 else CErr 6 p cs
                | err => err
                end
            | err => err
            end
          else CErr 3 p cs
      | None => CErr 3 p cs
      end
      end
      | None => CErr 3 p cs
      end
  | PCaseNJ e cuts joinpc rs ws k =>      (* [comment removed for export] *)
      match erange (kn cs) e with
      | Some (lo, hi) =>
          match nj_ends (run_block_gc segs IT gcb KC bfuel (joinpc :: STOPS A)) joinpc (nj_starts cs e (nj_arms lo hi cuts)) with
          | Some ends =>
              match node_joinN segs A nx0 (nxt cs) joinpc rs ws ends with
              | Some csj => check f csj k
              | None => CErr 3 p cs          (* [comment removed for export] *)
              end
          | None => CErr 1 p cs              (* [comment removed for export] *)
          end
      | None => CErr 3 p cs
      end
  | PVisAbsorb b n k => match node_visabsorb A cs b n with Some cs' => check f cs' k | None => CErr 3 p cs end   (* [comment removed for export] *)
  | PFreshCell b n k => match node_freshcell segs nx0 cs b n with Some cs' => check f cs' k | None => CErr 3 p cs end   (* [comment removed for export] *)
  | PVisSplit b n d k => match node_vissplit LIMIT cs b n d with Some cs' => check f cs' k | None => CErr 3 p cs end   (* [comment removed for export] *)
  | PVisHead b m L k => match node_vishead A LIMIT cs b m L with Some cs' => check f cs' k | None => CErr 3 p cs end   (* [comment removed for export] *)
  | PUnvisHead b m k => match node_unvishead A cs b m with Some cs' => check f cs' k | None => CErr 3 p cs end   (* [comment removed for export] *)
  | PGhostDedup k => check f (node_ghostdedup cs) k   (* [comment removed for export] *)
  | PHavocBrkP lo hi k => match node_havocbrkp nx0 cs lo hi with Some cs' => check f cs' k | None => CErr 3 p cs end   (* [comment removed for export] *)
  | PKeep ws vs k => check f (set_kn cs (kn_keepm nx0 (kn cs) ws (map vN vs))) k   (* [comment removed for export] *)
  | PFactMem K k => if (if memfact_ok segs A (kn cs) K then true else memfact_fd (kn cs) (a_fd cs) K) then check f (add_kn cs [K]) k else CErr 3 p cs   (* [comment removed for export] *)
  | PVisRespell b n b' n' k => match node_visrespell cs b n b' n' with Some cs' => check f cs' k | None => CErr 3 p cs end   (* [comment removed for export] *)
  | PMapRespell b n b' n' k => match node_maprespell cs b n b' n' with Some cs' => check f cs' k | None => CErr 3 p cs end   (* [comment removed for export] *)
  | PMemRespell b lo hi b' d k => match node_memrespell cs b lo hi b' d with Some cs' => check f cs' k | None => CErr 3 p cs end   (* [comment removed for export] *)
  | PSrlSplit r s k => match node_srlsplit cs r s with Some cs' => check f cs' k | None => CErr 3 p cs end   (* [comment removed for export] *)
  | PAndRange r logc ub k => match node_andrange cs r logc ub with Some cs' => check f cs' k | None => CErr 3 p cs end   (* [comment removed for export] *)
  | PAndRangeR r logc rs k => match node_andrange cs r logc (reg cs rs) with Some cs' => check f cs' k | None => CErr 3 p cs end   (* [comment removed for export] *)
  | PSrlSplitAll r s k => match node_srlsplitall cs r s with Some cs' => check f cs' k | None => CErr 3 p cs end   (* [comment removed for export] *)
  | PFdHavoc lo hi k => match node_fdhavoc nx0 cs lo hi with Some cs' => check f cs' k | None => CErr 3 p cs end   (* [comment removed for export] *)
  | PFreshCellK b n k => match node_freshcellk segs nx0 cs b n with Some cs' => check f cs' k | None => CErr 3 p cs end   (* [comment removed for export] *)
  | PVisPerm perm k => match node_visperm cs perm with Some cs' => check f cs' k | None => CErr 3 p cs end   (* [comment removed for export] *)
  | PHandoffM m0 =>   (* [comment removed for export] *)
      let m := vNm m0 in
      match lc with
      | Some (MC b v h st) =>
          match find_src m v with
          | Some w =>
              if lin_ge0 (kn cs) [(EVar w, -1)] [(EVar v, 0)] then
                match node_rename nx0 cs m with
                | Some cs' => if entails cs' st then COk (SHole h) else CErr 3 p cs
                | None => CErr 3 p cs
                end
              else CErr 3 p cs
          | None => CErr 3 p cs
          end
      | _ => CErr 8 p cs
      end
  | PFdRespell len off k => match node_fdrespell cs len off with Some cs' => check f cs' k | None => CErr 3 p cs end   (* [comment removed for export] *)
  | PDisjNth b1 n1 i k => match disj_nth cs b1 n1 i with
                          | Some K => if fact_okc cs K then check f (add_kn cs [K]) k else CErr 3 p cs
                          | None => CErr 3 p cs
                          end   (* [comment removed for export] *)
  | PMmapInS ka kb kc =>   (* [comment removed for export] *)
      if is_ecall_at segs cs then
        match node_mmapinS A LIMIT cs with
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
  end
  end.
End Check.

End WithSegs.
End AP.
