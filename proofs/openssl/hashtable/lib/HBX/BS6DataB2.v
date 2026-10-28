(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Uint63 PrimString.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType Run.
From OssFuzzTheorems.openssl.hashtable.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.FX Require Import W64 ITrie FxInstr FxState FxMem FxExec FxImage FxHandoff FxHoBuild
  FxSys FxDrive FxDrive3 FxDrive3N FxDrive3S FxDrive3C FxDrive3D FxDrive3H FxDrive3T FxDrive3O FxDrive3W.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore AsanInit CxPlan HBPlanImage HBAtable BC2B2Lit.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.Br Require Import BrEnv BrMem BrRev BrClass BrRevS BrDress BrTrans BrGen.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib.HBX Require Import BS6Pcs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Open Scope Z_scope.
Definition IM : fimage := odflt [] (mk_fimage HASEGS).
Definition code : itrie finstr := odflt iempty (build_code HASEGS s6_pcs).
Definition START : CAP.acs := c2b2_hs10.
Definition TT0 : ttab_e := [(2%uint63, CAP.eaddz CAP.e_spw (-8388608)); (4%uint63, AX2.ELit 0)].
Definition shapes0 : list rshape :=
  [(0%uint63, 0x10000%uint63, 0xbfb000%uint63, 0%uint63, None);
   (2%uint63, 0%uint63, 8388608%uint63, 4%uint63, Some PKUnk);
   (4%uint63, 2147459072%uint63, 2149021184%uint63, 12%uint63, Some PKZero)].   (* [comment removed for export] *)
Definition classes0 : list (int * rclass) := [(0%uint63, RCHull); (2%uint63, RCTop); (4%uint63, RCSpan)].
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition wr_whole (b : AX2.expr) (l : Z) : bool :=
  existsb (fun K => match K with
                    | AX2.KWr a (AX2.ELit l') => AX2.expr_eqb (AX2.a_base a) b && (AX2.a_off a =? 0) && (l <=? l')
                    | _ => false end) (CAP.kn START).
Definition dflt_of (b : AX2.expr) (l : Z) : option pkind := if wr_whole b l then Some PKUnk else None.
Definition root_step (acc : ttab_e * list rshape * list (int * rclass) * list fent * int * nat) (m : CAP.amap) :=
  let '(tab, shs, cl, all, t, i) := acc in
  match CAP.am_base m, CAP.am_len m with
  | AX2.ELit b, AX2.ELit l => (tab, shs, cl, all ++ [(0%uint63, of_Z b, of_Z l)], t, S i)
  | b, AX2.ELit l => (tab ++ [(t, b)], shs ++ [(t, 0%uint63, of_Z l, 12%uint63, dflt_of b l)], cl ++ [(t, RCEnt i)],
                      all ++ [(t, 0%uint63, of_Z l)], (t + 2)%uint63, S i)
  | _, _ => (tab, shs, cl, all, t, S i)
  end.
Definition rootgen := fold_left root_step (CAP.a_maps START) (TT0, shapes0, classes0, [], 10%uint63, O).
(* [comment removed for export] *)
Definition TG : int := 26%uint63.
Definition TSB : int := 27%uint63.
Definition SBe : AX2.expr :=
  AX2.EAlu Instr.ALU_ADD (AX2.EAlu Instr.ALU_ADD (AX2.EMd Instr.M_MUL (AX2.ELit 4096) (AX2.EVar 235))
                                                  (AX2.EMd Instr.M_MUL (AX2.ELit (-4096)) (AX2.EVar 236))) (AX2.ELit 65536).
(* [comment removed for export] *)
Definition TTOP : int := 29%uint63.
Definition Te : AX2.expr :=
  AX2.EAlu Instr.ALU_ADD (AX2.EMd Instr.M_MUL (AX2.ELit 32768) (AX2.EVar 0))
    (AX2.EAlu Instr.ALU_ADD (AX2.EMd Instr.M_MUL (AX2.ELit 4096) (AX2.EVar 10)) (AX2.EMd Instr.M_MUL (AX2.ELit 4096) (AX2.EVar 433))).
Definition TT1 : ttab_e := (let '(tab, _, _, _, _, _) := rootgen in tab ++ [(TSB, SBe); (TTOP, Te)]).
Definition shapes : list rshape := (let '(_, shs, _, _, _, _) := rootgen in
   filter (fun s : rshape => negb (sh_tag s =? TG)%uint63) shs ++ [(TSB, 0%uint63, 137438957568%uint63, 12%uint63, None)]).
Definition classes : list (int * rclass) := (let '(_, _, cl, _, _, _) := rootgen in filter (fun c => negb (fst c =? TG)%uint63) cl ++ [(TSB, RCEnt 8)]).
Definition ALL0 : list fent := (let '(_, _, _, all, _, _) := rootgen in all).
Definition regtags : ttab_e := gen_tt TT1 100%uint63 (map (fun e => AX2.KWord (AX2.SA (AX2.ELit 0) 0) 8 e) (AX2.s_regs (CAP.a_ss START))).
Definition TT : ttab_e := gen_tt regtags 200%uint63 (CAP.kn START).
(* [comment removed for export] *)
Definition ORD_CAND : list (int * int * Z) :=
  [(2%uint63, TTOP, 8388448); (TTOP, 2%uint63, -8388608); (2%uint63, TTOP, 8388624); (TTOP, 2%uint63, -8392528);
   (2%uint63, TTOP, 8388513); (TTOP, 2%uint63, -8388512)].
Definition ORD_T : list (int * int * Z) := filter (fun o : int * int * Z => let '(ta, tb, dd) := o in
            CAP.xinsideJ (CAP.kn START) (tte TT tb) 0 (AX2.ELit 1) (tte TT ta) dd (AX2.ELit (2 ^ 62))) ORD_CAND.
Definition NTAG : int := 1000%uint63.
Definition d0 : sdesc := ho_build_fast IM (rb_facts HAT TT shapes [] classes START) (of_Z (AX2.s_pc (CAP.a_ss START))) shapes.   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition whole_syms : list (int * Z * fval) := flat_map (fun K => match K with
     | AX2.KWord a 8%nat v =>
         match aview [] (rb_M shapes) [] (xt_of TT) a, vview_ok TT v with
         | Some (t, o), Some fv => if (vtag fv =? 0)%uint63 then [] else if (o mod 8 =? 0) && (0 <=? o) then [(t, o, fv)] else []
         | _, _ => []
         end
     | _ => [] end) (CAP.kn START).
Definition set_cell (dd : sdesc) (x : int * Z * fval) : sdesc :=
  let '(t, off, fv) := x in
  SD (sd_pc dd) (sd_regs dd)
     (map (fun r => if (rd_tag r =? t)%uint63 then
                      RD (rd_tag r) (rd_lo r) (rd_len r) (rd_align r) (rd_dflt r)
                         (map (fun p => if (pd_pn p =? of_Z (off / 4096))%uint63 then
                                          PD (pd_pn p) (pd_wr p) (pd_kind p)
                                             (map (fun ic : int * cell =>
                                                     if (fst ic =? of_Z ((off mod 4096) / 8))%uint63
                                                     then (fst ic, match snd ic with CB _ => CV fv | c => c end) else ic) (pd_cells p))
                                        else p) (rd_pages r))
                    else r) (sd_mem dd)).
Definition d : sdesc := fold_left set_cell whole_syms d0.
Definition STK_RANGE : Z * Z := odflt (0, 0) (AX2.base_range (CAP.kn START) (tte TT 2%uint63)).
Definition bs : list ditem := [(4%uint63, 0%uint63, 0%uint63, RK_plain); (2%uint63, of_Z (fst STK_RANGE), of_Z (snd STK_RANGE), RK_plain)].
Definition is_lazy_am (m : CAP.amap) : bool := match CAP.am_kind m with CAP.KRWLAZY => true | _ => false end.
Definition LZ0 : list fent := map snd (filter (fun p => is_lazy_am (fst p)) (combine (CAP.a_maps START) ALL0)).
Definition V2 : list fent := filter (fun e => negb (fent_tag e =? 0)%uint63 && negb (fent_tag e =? TG)%uint63) ALL0.
Definition RBYTES : Z := State.live_bytes (segments_reserved HASEGS).
(* [comment removed for export] *)
Definition EX0 : list fent := filter (fun e => negb (fent_tag e =? 0)%uint63) ALL0.
Definition L3 : fledger3 :=
  FL3 (FL V2 [] 0%uint63 (Z.of_nat (List.length ALL0)) (CAP.a_totsz START - RBYTES)) ALL0 [] LZ0 [] (CAP.a_abytes START) (CAP.a_eager START) EX0 ([(TG, TSB, 4096); (TSB, TG, -65536)] ++ ORD_T) [].
Definition W : Z := 12562432.

Definition BP : int := 2025044%uint63.   (* [comment removed for export] *)
Definition shp (l : int) : bool := ((l land 32767) =? 0)%uint63.
Definition oelse {T} (a b : option T) : option T := match a with Some x => Some x | None => b end.
Definition xask (F : fstate) : option (int * int) := oelse (xask_b5 IM code F) (xask_band code F).
Definition RC : Z := Z.of_nat (List.length (segments_reserved HASEGS)).
(* [comment removed for export] *)
