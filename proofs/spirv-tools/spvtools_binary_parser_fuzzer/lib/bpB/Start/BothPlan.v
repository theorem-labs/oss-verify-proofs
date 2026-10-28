(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BPropExec.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BxSymExec3.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Export BothPlanCore.
Import ListNotations.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Open Scope Z_scope.

Module AP.
Include APC.
Import AX2.

Section WithSegs.
Variable segs : list Segment.
Variable IT : itab.
Variable A : atable.
Variable nx0 : nat.
Variable LIMIT : Z.

Inductive snode : Type :=
| YMunmap
| YBrk
| YSetTid.

Inductive xnode : Type :=
| XIMemset
| XIMemcpy
| XMemset
| XMemcpy
| XMemIsZero
| XEnvScan
| XPnScan
| XLayout
| XIStrncpy
| XPopFree
| XSniff
| XSmear.

Inductive plan : Type :=
| PRun (stops : list Z) (k : plan)
| PSplit (e : expr) (mid : Z) (k1 k2 : plan)
| PCase2 (e : expr) (mid : Z) (k1 k2 : plan)
| PCaseDisj (b1 b2 : expr) (k1 k2 : plan)
| PShDisj (b1 n1 b2 n2 : expr) (k : plan)
| PContra
| PFact (K : kentry) (k : plan)
| PJoin (b : expr) (off : Z) (n : nat) (k : plan)
| PForget (ixs : list nat) (k : plan)
| PDropRange (b : expr) (n : expr) (k : plan)
| PGcKeep (ws : list (expr * expr)) (k : plan)
| PBump (m : nat) (k : plan)
| PHavoc (rs : list nat) (k : plan)
| PHavocBig (K : nat) (k : plan)
| PFresh (r : nat) (logc : Z) (base : option expr) (k : plan)
| PSys (y : snode) (k : plan)
| PMmap1 (kgranted : plan)
| PMmapIn1 (kok : plan)
| PMprotect1 (kgranted : plan)
| PBrk2 (kblocked kgranted : plan)
| PX (x : xnode) (args : list expr) (k : plan)
| PExt (id : nat) (args : list expr) (k : plan)
| PEmit (id : nat) (args : list expr) (k : plan)
| PExt2 (id : nat) (args : list expr) (k1 k2 : plan)
| PLoop (J : nat) (N : expr) (inv : acs) (body k : plan)
| PNext
| PHandoff (h : nat)
| PExit
| PSpin
| PFog (i : nat) (sz : Z) (k : plan)
| PFogNew (i : nat) (sz : Z) (k : plan)
| PGhost (b n : expr) (k : plan)
| PUnvis (b n : expr) (k : plan)
| PHavocBrk (lo hi : Z) (k : plan)
| PIntro (lo hi : Z) (k : plan)
| PDiamond (joinpc : Z) (rs : list nat) (k : plan)
| PRename (m : list (nat * nat)) (k : plan)
| PCompact (k : plan)
| PVia (j : nat) (js : acs) (lo : nat) (karms k : plan)
| PMerge (j : nat)
| PAbstractCell (b : expr) (n : Z) (k : plan)
| PHavocWords (bs : list expr) (k : plan)
| PRespell (r : nat) (e : expr) (k : plan)
| PNameCell (b : expr) (n : nat) (k : plan)
| PCaseGaps (v : nat) (sc : Z) (ks : list plan)
| PRangeGaps (v : nat) (sc : Z) (k : plan)
| PMmapGaps (ks : list plan)
| PFrozen (id : nat) (hs ws : list hull) (cold : list expr) (items : list fitem) (k : plan).

Definition node_sys (y : snode) (cs : acs) : option acs :=
  match y with
  | YMunmap => node_munmap A cs
  | YBrk => node_brk1 A cs
  | YSetTid => node_settid nx0 cs
  end.

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
  | XSniff => None
  | XSmear => node_smear A cs
  end.

Definition node_frozen (KC bfuel : nat) (hs ws : list hull) (cold : list expr) (items : list fitem) (cs : acs) : option acs :=
  let (fz, act) := partition (fz_sel hs cold) (kn cs) in
  if frozen_entry_ok nx0 hs ws cs then
    match run_fitems segs IT A nx0 hs ws (fold_right kentry_vars_t PTLeaf fz) (nxt cs) KC bfuel (STOPS A) items (set_kn cs act) with
    | Some cs' => Some (set_kn cs' (kn cs' ++ fz))
    | None => None
    end
  else None.

Inductive cres : Type := COk (s : shape) | CErr (code : Z) (where_ : plan) (cs : acs).

Section Check.
Variable XN : nat -> list expr -> acs -> option acs.
Variable XE : nat -> list expr -> acs -> option (Z * list spiece * acs).
Variable XB : nat -> list expr -> acs -> option (acs * acs).
Variable HS : nat -> option acs.
Variable KC : nat.
Variable bfuel : nat.

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

Fixpoint casegaps_fold (chk : acs -> plan -> cres) (p : plan) (cs0 : acs) (css : list acs) (ks : list plan) (acc : option shape) : cres :=
  match css, ks with
  | [], [] => match acc with Some s1 => COk s1 | None => CErr 3 p cs0 end
  | csi :: css', ki :: ks' =>
      match chk csi ki with
      | COk si =>
          match acc with
          | None => casegaps_fold chk p cs0 css' ks' (Some si)
          | Some s1 => if shape_eqb_h s1 si then casegaps_fold chk p cs0 css' ks' acc else CErr 6 p csi
          end
      | err => err
      end
  | _, _ => CErr 3 p cs0
  end.

Fixpoint check (fuel : nat) (lc : option loopctx) (cs : acs) (p : plan) {struct fuel} : cres :=
  match fuel with
  | O => CErr 0 p cs
  | S f =>
  let check_in := check in
  let check (f : nat) := check_in f lc in

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
                | COk s2 => if shape_eqb_h s1 s2 then COk s1 else CErr 6 p cs
                | err => err
                end
            | err => err
            end
          else CErr 3 p cs
      | None => CErr 3 p cs
      end
  | PCaseGaps v sc ks =>
      match node_casegaps cs v sc with
      | Some css => casegaps_fold (check f) p cs css ks None
      | None => CErr 3 p cs
      end
  | PRangeGaps v sc k => match node_rangegaps cs v sc with Some cs' => check f cs' k | None => CErr 3 p cs end
  | PMmapGaps ks =>
      if is_ecall_at segs cs then
        match node_mmapgaps A nx0 LIMIT cs with
        | Some css => casegaps_fold (check f) p cs css ks None
        | None => CErr 3 p cs
        end
      else CErr 2 p cs
  | PFrozen _ hs ws cold items k =>
      match lc with
      | Some _ => CErr 8 p cs
      | None => match node_frozen KC bfuel hs ws cold items cs with Some cs' => check f cs' k | None => CErr 1 p cs end
      end
  | PCaseDisj b1 b2 k1 k2 =>
      match node_casedisj cs b1 b2 with
      | Some (csa, csb) =>
          match check f csa k1 with
          | COk s1 => match check f csb k2 with
                      | COk s2 => if shape_eqb_h s1 s2 then COk s1 else CErr 6 p cs
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
                        | COk sb => if shape_eqb_h sa sb then COk sa else CErr 6 p cs
                        | err => err
                        end
            | err => err
            end
        | None => CErr 3 p cs
        end
      else CErr 2 p cs
  | PMmap1 kb =>
      if is_ecall_at segs cs then
        match node_mmap2 A nx0 LIMIT cs with
        | Some (_, csb) => check f csb kb
        | None => CErr 3 p cs
        end
      else CErr 2 p cs
  | PMmapIn1 kb =>
      if is_ecall_at segs cs then
        match node_mmapin1 A LIMIT cs with
        | Some csb => check f csb kb
        | None => CErr 3 p cs
        end
      else CErr 2 p cs
  | PNameCell b n k => match node_namecell segs nx0 cs b n with Some cs' => check f cs' k | None => CErr 3 p cs end
  | PMprotect1 kb =>
      if is_ecall_at segs cs then
        match node_mprotect A LIMIT cs with
        | Some csb => check f csb kb
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
  | PHavocWords bs k => match node_havocwords nx0 cs bs with Some cs' => check f cs' k | None => CErr 3 p cs end
  | PRespell r e k => match node_respell cs r e with Some cs' => check f cs' k | None => CErr 3 p cs end
  | PDiamond joinpc rs k =>
      match branch_probe IT cs with
      | Some e =>
          match erange (kn cs) e with
          | Some (lo, hi) =>

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
End Check.

End WithSegs.
End AP.
