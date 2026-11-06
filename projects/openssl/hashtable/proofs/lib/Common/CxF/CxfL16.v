(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import PropExec AxSymExec3 AsanPlanCore CxPlan CxfPlan CxfRt.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import CxfPlanC CxfL1 CxfL2 CxfL3 CxfL4 CxfL8 CxfL15 CxfLeaf CxfNat.
Import ListNotations.
Open Scope Z_scope.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module CXFPCL.
Import CXFPC.
Notation "x && y" := (if x then y else false) (at level 40, left associativity) : bool_scope.
Notation "x || y" := (if x then true else y) (at level 50, left associativity) : bool_scope.
Import AX2.
Import AX2L.
Import APC.
Import APCL.
Import CAP.
Import CAPL.
Section G.
Variable segs : list Segment.
Variable IT : itab.
Variable A : atable.
Variable nx0 : nat.
Variable LIMIT : Z.
Variable XN : nat -> list expr -> acs -> option acs.
Variable XE : nat -> list expr -> acs -> option (Z * list spiece * acs).
Variable XB : nat -> list expr -> acs -> option (acs * acs).
Variable HS : nat -> option acs.
Variable FO : bool.
Variable SPIN : bool.
Variable RBC : CXFRT.rtc -> nat -> list Z -> acs -> option acs * CXFRT.rtc.
Variable NXC : CXFRT.rtc -> xnode -> list expr -> acs -> option acs * CXFRT.rtc.
Variable RESPC : CXFRT.rtc -> acs -> nat -> expr -> option acs.
Variable ENTX : acs -> acs -> bool.
Fixpoint check_c (fuel : nat) (lc : option loopctx) (c : CXFRTL.rtc) (cs : acs) (p : plan) {struct fuel} : cres :=
  match fuel with
  | O => CErr 0 p cs
  | S f =>
  let check_in := check_c in
  let check (f : nat) := check_in f lc c in
  let check_in_lc (f : nat) (lc' : option loopctx) := check_in f lc' c in
  let RBc := fun gb st cs0 => fst (RBC c gb st cs0) in
  
  let gcb := match lc with Some c => lc_bnd c | None => nx0 end in
  if negb match lc with Some c => CXNAT.lebF (lc_bnd c) (nxt cs) | None => true end then CErr 9 p cs else
  match p with
  | PRun stops k =>
      match RBC c gcb (stops ++ STOPS A) cs with
      | (Some cs', c') => check_in f lc c' cs' k
      | (None, _) => CErr 1 p cs
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
      match CXFPL.diamond_tree_g IT A RBc gcb (nxt cs) (S depth) joinpc cs with
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
        match node_sys A nx0 y cs with Some cs' => check f cs' k | None => CErr 3 p cs end
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
                        | COk sb => match (if FO then COk SNil else check_all A (check f) kc cscs) with
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
                        | COk sb => match (if FO then COk SNil else check_all A (check f) kc cscs) with
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
  | PX x args k => if negb (x_on A x) then CErr 3 p cs else match NXC c x args cs with (Some cs', c') => check_in f lc c' cs' k | (None, _) => CErr 3 p cs end
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
            match check_in_lc f (Some (LC (pc cs) (inst inv J (eaddz (EVar J) 1)) lo hi)) (loop_body_state J N nhi inv) body with
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
      | Some ch => if ENTX cs ch then COk (SHole h) else CErr 3 p cs   
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
          match RBc gcb (joinpc :: STOPS A) csa with
          | Some ca =>
              match RBc gcb (joinpc :: STOPS A) csb with
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
      match CXFPL.diamond_tree_g IT A RBc gcb (nxt cs) (S depth) joinpc cs with
      | Some (l :: ls) =>
          match diamond_joinx_all segs A nx0 (nxt cs) joinpc rs R l ls with
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
        | COk sk => check_in_lc f (Some (JC j js sk (nxt cs) lo)) cs karms
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
  | PRespell r e k => match RESPC c cs r e with Some cs' => check f cs' k | None => CErr 3 p cs end
  | PDiamond joinpc rs k =>
      match branch_probe IT cs with
      | Some e =>
          match erange (kn cs) e with
          | Some (lo, hi) =>
              
              if (Z.ltb hi 1 || Z.ltb 0 lo)%bool then
                match RBc gcb (joinpc :: STOPS A) cs with
                | Some cs' => if Z.eqb (pc cs') joinpc then check f cs' k else CErr 3 p cs'
                | None => CErr 1 p cs
                end
              else
                let cs1 := set_kn cs (KRange e lo 0 :: kn cs) in
                let cs2 := set_kn cs (KRange e 1 hi :: kn cs) in
                match RBc gcb (joinpc :: STOPS A) cs1 with
                | Some ca =>
                    match RBc gcb (joinpc :: STOPS A) cs2 with
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
Variable RB : nat -> list Z -> acs -> option acs.
Variable NX : xnode -> list expr -> acs -> option acs.
Variable RESP : acs -> nat -> expr -> option acs.
End G.
Lemma L_CXFPCL_check_c : @check_c = @CXFPC.check_c.
Proof. unfold check_c. rewrite ?APCL.L_APCL_STOPS, ?APCL.L_APCL_add_kn, ?APCL.L_APCL_branch_probe, ?CAPL.L_CAPL_check, ?CAPL.L_CAPL_check_all, ?APCL.L_APCL_diamond_join_all, ?CAPL.L_CAPL_diamond_joinx_all, ?CXFPL.L_CXFPL_diamond_tree_g, ?APCL.L_APCL_drop_ixs, ?APCL.L_APCL_eaddz, ?APCL.L_APCL_entails_h, ?APCL.L_APCL_entails_xb, ?AX2L.L_AX2L_erange, ?APCL.L_APCL_expr_vars_lt, ?APCL.L_APCL_fact_ok, ?APCL.L_APCL_inst, ?APCL.L_APCL_is_ecall_at, ?APCL.L_APCL_kn, ?APCL.L_APCL_kn_contra, ?APCL.L_APCL_kn_gcdisj, ?APCL.L_APCL_kn_gcrange, ?APCL.L_APCL_kn_keep, ?APCL.L_APCL_lc_bnd, ?APCL.L_APCL_loop_body_state, ?APCL.L_APCL_loop_ok, ?APCL.L_APCL_node_abstractcell, ?APCL.L_APCL_node_band, ?APCL.L_APCL_node_brk2F, ?APCL.L_APCL_node_bump, ?APCL.L_APCL_node_casedisj, ?APCL.L_APCL_node_compact, ?APCL.L_APCL_node_diamond_join, ?APCL.L_APCL_node_droprange, ?APCL.L_APCL_node_exit, ?APCL.L_APCL_node_fog, ?APCL.L_APCL_node_fognew, ?APCL.L_APCL_node_fresh, ?APCL.L_APCL_node_ghost, ?APCL.L_APCL_node_havoc, ?APCL.L_APCL_node_havocbig, ?APCL.L_APCL_node_havocbrk, ?APCL.L_APCL_node_havocwords, ?APCL.L_APCL_node_intro, ?APCL.L_APCL_node_introg, ?APCL.L_APCL_node_join, ?APCL.L_APCL_node_joinx, ?APCL.L_APCL_node_mmap2F, ?APCL.L_APCL_node_mmapin, ?APCL.L_APCL_node_mprotect2, ?APCL.L_APCL_node_rename, ?APCL.L_APCL_node_shdisj, ?APCL.L_APCL_node_spin, ?CAPL.L_CAPL_node_sys, ?APCL.L_APCL_node_unvis, ?APCL.L_APCL_nxt, ?APCL.L_APCL_pc, ?CXFRTL.L_CXFRTL_rtc, ?APCL.L_APCL_salt2, ?APCL.L_APCL_set_kn, ?APCL.L_APCL_shape_eqb, ?CAPL.L_CAPL_shape_eqh, ?APCL.L_APCL_shape_seteq, ?APCL.L_APCL_shape_vars_lt, ?APCL.L_APCL_via_ok, ?CAPL.L_CAPL_x_on, ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

End CXFPCL.
