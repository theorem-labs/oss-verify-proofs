(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Uint63 PrimString.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType Run.
From OssFuzzTheorems.openssl.hashtable.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.FX Require Import W64 ITrie FxInstr FxState FxMem FxExec FxImage FxHandoff FxHoBuild
  FxSys FxDrive FxDrive3 FxDrive3N FxDrive3S FxDrive3C FxDrive3D FxDrive3H FxDrive3T FxDrive3O FxDrive3W.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore AsanInit CxPlan HBPlanImage HBAtable BKC5A2Lit BFIEndK5A2.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.Br Require Import BrEnv BrMem BrRev BrClass BrRevS BrDress BrTrans BrGen Br3HoL Br3RespDefs.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib.HBX Require Import BFIPcs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Open Scope Z_scope.
Definition IM : fimage := odflt [] (mk_fimage HASEGS).
Definition code : itrie finstr := odflt iempty (build_code HASEGS fi_pcs).
(* [comment removed for export] *)
Definition START0 : CAP.acs := kc5a2_hs305.
Definition END0 : CAP.acs := fiendk5a2.
Definition TT0 : ttab_e := [(2%uint63, CAP.eaddz CAP.e_spw (-8388608)); (4%uint63, AX2.ELit 0)].
(* [comment removed for export] *)
Definition shapes0 : list rshape := [(0%uint63, of_Z (CAP.img_lo HAT), of_Z (CAP.img_hi HAT), 0%uint63, None);
   (2%uint63, 0%uint63, 8388608%uint63, 4%uint63, Some PKUnk);
   (4%uint63, of_Z (CAP.shadow_off HAT + CAP.img_lo HAT / 8), of_Z (CAP.shadow_off HAT + CAP.img_hi HAT / 8), 12%uint63,
    (* [comment removed for export] *)
    if existsb (fun K => match K with
                         | AX2.KZero (AX2.SA (AX2.ELit 0) o) (AX2.ELit l) => (o =? CAP.shadow_off HAT + CAP.img_lo HAT / 8) && ((CAP.img_hi HAT - CAP.img_lo HAT) / 8 <=? l)
                         | _ => false end) (CAP.kn START0) then Some PKZero else Some PKUnk)].
Definition classes0 : list (int * rclass) := [(0%uint63, RCHull); (2%uint63, RCTop); (4%uint63, RCSpan)].
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition wr_whole (b : AX2.expr) (l : Z) : bool :=
  existsb (fun K => match K with
                    | AX2.KWr a (AX2.ELit l') => AX2.expr_eqb (AX2.a_base a) b && (AX2.a_off a =? 0) && (l <=? l')
                    | _ => false end) (CAP.kn START0).
Definition dflt_of (b : AX2.expr) (l : Z) : option pkind := if wr_whole b l then Some PKUnk else None.
(* [comment removed for export] *)
Definition shK : Z := 2147450880.
Definition sh_expr (e : AX2.expr) : AX2.expr :=
  let l := AX2.lin_of e in AX2.unlin (fst l / 8 + shK, map (fun p : Z * AX2.expr => (fst p / 8, snd p)) (snd l)).
(* [comment removed for export] *)
Definition sh_base0 (e : AX2.expr) : AX2.expr := let l := AX2.lin_of e in AX2.unlin (0, map (fun p : Z * AX2.expr => (fst p / 8, snd p)) (snd l)).
Definition sh_fact (zero : bool) (b : AX2.expr) (l : Z) : bool :=
  existsb (fun K => match K, zero with
                    | AX2.KWr a (AX2.ELit l'), false | AX2.KZero a (AX2.ELit l'), true =>
                        lin_match (AX2.lin_of (AX2.a_base a)) (AX2.lin_of (sh_base0 b)) 0 && (AX2.a_off a =? shK) && (l / 8 <=? l')
                    | _, _ => false end) (CAP.kn START0).
Definition dflt_sh (b : AX2.expr) (l : Z) : option pkind :=
  if sh_fact false b l then (if sh_fact true b l then Some PKZero else Some PKUnk) else None.
(* [comment removed for export] *)
Definition SHCLAIM : list nat := map fst (filter (fun p : nat * CAP.amap => match CAP.am_len (snd p) with AX2.ELit l => (l =? 11571200) | _ => false end) (combine (seq 0 (List.length (CAP.a_maps START0))) (CAP.a_maps START0))).   (* [comment removed for export] *)
Definition kbases (kn : list AX2.kentry) : list AX2.expr :=
  fold_left (fun acc K =>
     let ob := match K with
               | AX2.KWord a _ _ | AX2.KZero a _ | AX2.KBlob a _ _ | AX2.KWr a _ | AX2.KFill a _ _ | AX2.KUnk a _ => Some (AX2.a_base a)
               | _ => None end in
     match ob with
     | Some b => if existsb (AX2.expr_eqb b) acc then acc else acc ++ [b]
     | None => acc end) kn [].
(* [comment removed for export] *)
Definition KB0 : list AX2.expr := kbases (CAP.kn START0).
Definition has_sh_facts (b : AX2.expr) : bool :=
  existsb (fun b0 => lin_match (AX2.lin_of b0) (AX2.lin_of (sh_base0 b)) 0) KB0.
Definition root_step (acc : ttab_e * list rshape * list (int * rclass) * list fent * int * nat) (m : CAP.amap) :=
  let '(tab, shs, cl, all, t, i) := acc in
  match CAP.am_base m, CAP.am_len m with
  | AX2.ELit b, AX2.ELit l => (tab, shs, cl, all ++ [(0%uint63, of_Z b, of_Z l)], t, S i)
  | b, AX2.ELit l =>
      let sh := has_sh_facts b in
      (tab ++ [(t, b)] ++ (if sh then [((t + 1)%uint63, sh_expr b)] else []),
       shs ++ [(t, 0%uint63, of_Z l, 12%uint63, dflt_of b l)]
           ++ (if sh then [((t + 1)%uint63, 0%uint63, of_Z (l / 8), 9%uint63, if existsb (Nat.eqb i) SHCLAIM then dflt_sh b l else None)] else []),
       cl ++ [(t, RCEnt i)] ++ (if sh then [((t + 1)%uint63, RCSpan)] else []),
       all ++ [(t, 0%uint63, of_Z l)], (t + 4)%uint63, S i)
  | _, _ => (tab, shs, cl, all, t, S i)
  end.
Definition rootgen := fold_left root_step (CAP.a_maps START0) (TT0, shapes0, classes0, [], 12%uint63, O).
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition is_res (m : CAP.amap) : bool := match CAP.am_len m with AX2.ELit l => (2 ^ 36 <=? l) | _ => false end.
Definition IRES : nat := (fix go (l : list CAP.amap) (i : nat) := match l with [] => O | m :: r => if is_res m then i else go r (S i) end) (CAP.a_maps START0) O.
Definition RESB : AX2.expr := CAP.am_base (nth IRES (CAP.a_maps START0) (CAP.AM (AX2.ELit 0) (AX2.ELit 0) CAP.KRW)).
Definition TG : int := (let '(tab, _, _, _, _, _) := rootgen in
   match List.find (fun p : int * AX2.expr => AX2.expr_eqb (snd p) RESB) tab with Some p => fst p | None => 0%uint63 end).
Definition TSB : int := (TG + 2)%uint63.
Definition TSBS : int := (TG + 3)%uint63.
(* [comment removed for export] *)
Definition SBe : AX2.expr := match List.find (fun e => match e with
                            | AX2.EAlu Instr.ALU_ADD b (AX2.EMd Instr.M_MUL (AX2.ELit (-4096)) (AX2.EVar _)) => AX2.expr_eqb b RESB
                            | _ => false end) KB0 with
  | Some e => e
  | None => AX2.ELit 0
  end.
(* [comment removed for export] *)
Definition TTOP : int := 7%uint63.
(* [comment removed for export] *)
Definition Te : AX2.expr := match flat_map (fun K => match K with
       | AX2.KWord _ 8%nat ((AX2.EAlu Instr.ALU_ADD (AX2.EMd Instr.M_MUL (AX2.ELit 32768) (AX2.EVar O))
                              (AX2.EAlu Instr.ALU_ADD (AX2.EMd Instr.M_MUL (AX2.ELit 4096) (AX2.EVar 10%nat)) (AX2.EMd Instr.M_MUL (AX2.ELit 4096) (AX2.EVar x)))) as e) =>
           if Nat.leb 12 x then [e] else []
       | _ => [] end) (CAP.kn START0) with
  | e :: _ => e
  | [] => AX2.ELit 0
  end.
Definition TT1 : ttab_e := (let '(tab, _, _, _, _, _) := rootgen in tab ++ [(TSB, SBe); (TSBS, sh_expr SBe); (3%uint63, sh_expr (CAP.eaddz CAP.e_spw (-8388608))); (TTOP, Te)]).
(* [comment removed for export] *)
Definition SHTAGS : list (int * int) := (let '(tab, _, _, _, _, _) := rootgen in
   flat_map (fun p : int * AX2.expr => if (fst p land 1 =? 1)%uint63 then [(fst p, (fst p - 1)%uint63)] else []) tab) ++ [(TSBS, TSB); (3%uint63, 2%uint63)].
Definition row_of (b : AX2.expr) : list rrow :=
  let lb := AX2.lin_of b in
  flat_map (fun q : int * int =>
     let lt := AX2.lin_of (tte TT1 (fst q)) in
     let kk := AX2.snorm (fst lt - fst lb) in
     if terms_eqb (snd lb) (snd lt) && (0 <? kk) then [RR b (tte TT1 (fst q)) kk (Some (tte TT1 (snd q)))] else []) SHTAGS.
Definition RTs : list rrow := flat_map row_of (kbases (CAP.kn START0)).
Definition START : CAP.acs := resp_cs RTs START0.
Definition shapes : list rshape := (let '(_, shs, _, _, _, _) := rootgen in
   filter (fun s : rshape => negb (sh_tag s =? TG)%uint63) shs ++ [(TSB, 65536%uint63, 137439023104%uint63, 12%uint63, None);
      (TSBS, 8192%uint63, 17179877376%uint63, 9%uint63, None); (3%uint63, 0%uint63, 1048576%uint63, 1%uint63, None)]).
Definition classes : list (int * rclass) := (let '(_, _, cl, _, _, _) := rootgen in filter (fun c => negb (fst c =? TG)%uint63) cl ++ [(TSB, RCEnt IRES); (TSBS, RCSpan); (3%uint63, RCSpan)]).
Definition ALL0 : list fent := (let '(_, _, _, all, _, _) := rootgen in all).
Definition regtags : ttab_e := gen_tt TT1 300%uint63 (map (fun e => AX2.KWord (AX2.SA (AX2.ELit 0) 0) 8 e) (AX2.s_regs (CAP.a_ss START))).
Definition TT : ttab_e := gen_tt regtags 400%uint63 (CAP.kn START).
(* [comment removed for export] *)
Definition ORD_CAND : list (int * int * Z) :=
  [(2%uint63, TTOP, 8388448); (TTOP, 2%uint63, -8388608); (2%uint63, TTOP, 8388624); (TTOP, 2%uint63, -8392528);
   (2%uint63, TTOP, 8388513); (TTOP, 2%uint63, -8388512)].
Definition ORD_T : list (int * int * Z) := filter (fun o : int * int * Z => let '(ta, tb, dd) := o in
            CAP.xinsideJ (CAP.kn START) (tte TT tb) 0 (AX2.ELit 1) (tte TT ta) dd (AX2.ELit (2 ^ 62))) ORD_CAND.
(* [comment removed for export] *)
Definition ORD_N : list (int * int * Z) := flat_map (fun p : int * AX2.expr =>
     if (300 <=? fst p)%uint63 then
       match AX2.base_range (CAP.kn START) (snd p) with
       | Some (lo, hi) => if hi <? 2 ^ 32 then [(0%uint63, fst p, lo); (fst p, 2%uint63, 0)] else []
       | None => [] end
     else []) TT.
Definition NTAG : int := 1000%uint63.
(* [comment removed for export] *)
Definition FACTS0 : list hfact := rb_facts HAT TT shapes [] classes START.
(* [comment removed for export] *)
Definition FILL_LIM : Z := 0.
Definition FILLX : list hfact := fill_pieces FILL_LIM (rb_fillcov TT shapes START).
(* [comment removed for export] *)
Definition d0 : sdesc := (let F := FACTS0 ++ FILLX in
   SD (of_Z (AX2.s_pc (CAP.a_ss START))) (regs_desc F)
      (map (fun sh : int * int * int * int * option pkind => let '(t, _, _, _, _) := sh in
              if (t =? 0)%uint63 then region_fast IM F sh
              else let Ft := hfacts_of_tag F t in
                   if Nat.ltb 2000 (List.length Ft) then region_desc2L IM Ft sh else FxHandoff2.region_desc2 IM Ft sh) shapes)).
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
Definition d1 : sdesc := fold_left set_cell whole_syms d0.
(* [comment removed for export] *)
Definition FACTS : list hfact := FACTS0.
Definition zpages_of (t : int) : list int :=
  flat_map (fun f => match f with
     | HZero t' o l => if ((t' =? t) && (4096 <=? l) && (l <=? 67108864))%uint63 then
                         let p0 := ((o + 4095) >> 12)%uint63 in let p1 := ((o + l) >> 12)%uint63 in
                         if (p0 <? p1)%uint63 then pages_list (S (Z.to_nat (to_Z (p1 - p0)))) p0 (p1 - 1)%uint63 else []
                       else []
     | _ => [] end) FACTS.
Definition upgrade_page (t : int) (p : pdesc) : pdesc :=
  match pd_kind p with
  | PKUnk => if forallb (fun ci => match List.find (fun ic : int * cell => (fst ic =? ci)%uint63) (pd_cells p) with
                                   | Some _ => true
                                   | None => zero_cov FACTS t ((pd_pn p << 12) + (ci << 3))%uint63 8%uint63 end) (iseq 512)
             then PD (pd_pn p) (pd_wr p) PKZero (pd_cells p) else p
  | _ => p
  end.
(* [comment removed for export] *)
Definition edge_pages_of (t : int) : list int :=
  flat_map (fun f => match f with
     | HZero t' o l => if ((t' =? t) && (1048576 <? l) && (l <=? 67108864))%uint63 then
                         (if ((o land 4095) =? 0)%uint63 then [] else [(o >> 12)%uint63])
                         ++ (if (((o + l) land 4095) =? 0)%uint63 then [] else [((o + l) >> 12)%uint63])
                       else []
     | _ => [] end) FACTS.
Definition zero_cells_of (t pn : int) (have : list (int * cell)) : list (int * cell) :=
  flat_map (fun ci => if existsb (fun ic : int * cell => (fst ic =? ci)%uint63) have then []
                      else if zero_cov FACTS t ((pn << 12) + (ci << 3))%uint63 8%uint63
                           then [(ci, CV (FV 0%uint63 (W64 0%uint63 0%uint63)))] else []) (iseq 512).
Definition edge_page (t : int) (edges : list int) (p : pdesc) : pdesc :=
  match pd_kind p with
  | PKUnk => if existsb (fun q => (q =? pd_pn p)%uint63) edges
             then PD (pd_pn p) (pd_wr p) PKUnk (pd_cells p ++ zero_cells_of t (pd_pn p) (pd_cells p)) else p
  | _ => p
  end.
Definition upgrade_region (r : rdesc) : rdesc :=
  if (rd_tag r =? 0)%uint63 then r else
  let edges := edge_pages_of (rd_tag r) in
  let pages1 := map (fun p => edge_page (rd_tag r) edges (upgrade_page (rd_tag r) p)) (rd_pages r) in
  let have := map pd_pn pages1 in
  let extra := filter (fun pn => negb (existsb (fun q => (q =? pn)%uint63) have)) (zpages_of (rd_tag r)) in
  let have2 := have ++ extra in
  let eextra := filter (fun pn => negb (existsb (fun q => (q =? pn)%uint63) have2)
                                  && ((pn << 12) + 4096 <=? rd_len r)%uint63) edges in
  RD (rd_tag r) (rd_lo r) (rd_len r) (rd_align r) (rd_dflt r)
     (pages1 ++ map (fun pn => PD pn (wr_cov FACTS (rd_tag r) (pn << 12)%uint63 4096%uint63) PKZero []) extra
             ++ map (fun pn => PD pn (wr_cov FACTS (rd_tag r) (pn << 12)%uint63 4096%uint63) PKUnk (zero_cells_of (rd_tag r) pn [])) eextra).
Definition d2 : sdesc := SD (sd_pc d1) (sd_regs d1) (map upgrade_region (sd_mem d1)).
(* [comment removed for export] *)
Definition XA : list fent := flat_map (fun q : AX2.expr * AX2.expr =>
     match snd q with
     | AX2.ELit l =>
         let lb := AX2.lin_of (fst q) in let lt := AX2.lin_of SBe in
         let c := AX2.snorm (fst lb - fst lt) in
         if terms_eqb (snd lb) (snd lt) && (65536 <=? c) && (c + l <=? 65536 + 2 ^ 37) && negb (existsb (fun p => CAP.pair_eqb p q) (CAP.a_vis START0))
         then [(TSBS, of_Z (c / 8), of_Z (l / 8))] else []
     | _ => [] end) (CAP.a_vis END0).
Definition xa_pages (ts : int) : list int :=
  flat_map (fun e : fent => let '(t, o, l) := e in
              if (t =? ts)%uint63 then pages_list (S (Z.to_nat (to_Z (l >> 12)))) (o >> 12)%uint63 (((o + l) >> 12) - 1)%uint63 else []) XA.
Definition add_pages (ts : int) (wr : bool) (pns : list int) (r : rdesc) : rdesc :=
  if (rd_tag r =? ts)%uint63 then
    let have := map pd_pn (rd_pages r) in
    RD (rd_tag r) (rd_lo r) (rd_len r) (rd_align r) (rd_dflt r)
       (rd_pages r ++ map (fun pn => PD pn wr PKZero []) (filter (fun pn => negb (existsb (fun q => (q =? pn)%uint63) have)) pns))
  else r.
(* [comment removed for export] *)
Definition NOCLAIM : list int := (let '(_, shs, _, _, _, _) := rootgen in
   flat_map (fun s : rshape => let '(t, _, _, _, k) := s in
               if (t land 1 =? 1)%uint63 then (match k with None => [t] | Some _ => [] end) else []) shs).
Definition drop_partial (r : rdesc) : rdesc :=
  if (rd_tag r =? 0)%uint63 then r else
  if existsb (fun t => (t =? rd_tag r)%uint63) NOCLAIM then RD (rd_tag r) (rd_lo r) (rd_len r) (rd_align r) None [] else
  (* [comment removed for export] *)
  RD (rd_tag r) (rd_lo r) (rd_len r) (rd_align r) (rd_dflt r)
     (filter (fun p => ((pd_pn p << 12) + 4096 <=? rd_len r)%uint63 || ((rd_len r land 7 =? 0)%uint63 && ((pd_pn p << 12) <? rd_len r)%uint63)) (rd_pages r)).
(* [comment removed for export] *)
Definition RO_MIN : Z := 4096.
Definition ro_ranges : list (Z * Z) := flat_map (fun K => match K with
     | AX2.KZero (AX2.SA (AX2.ELit b) o) (AX2.ELit l) =>
         if (0 <? RO_MIN) && (RO_MIN <=? l) && (CAP.img_lo HAT <=? b + o) && (b + o + l <=? CAP.img_hi HAT) && existsb (CAP.kentry_eqb K) (CAP.kn END0)
         then [(b + o, b + o + l)] else []
     | _ => [] end) (CAP.kn START0).
Definition ro_page (pn : int) : bool :=
  existsb (fun r : Z * Z => (fst r <? (to_Z pn + 1) * 4096) && (to_Z pn * 4096 <? snd r)) ro_ranges.
Definition set_ro (r : rdesc) : rdesc :=
  if (rd_tag r =? 0)%uint63 then
    RD (rd_tag r) (rd_lo r) (rd_len r) (rd_align r) (rd_dflt r)
       (map (fun p => if ro_page (pd_pn p) then PD (pd_pn p) false (pd_kind p) (pd_cells p) else p) (rd_pages r))
  else r.
(* [comment removed for export] *)
Definition slice_pages : list int := flat_map (fun f => match f with
     | HWr t o l => if (t =? TSB)%uint63 && (4096 <=? l)%uint63 && (l <=? 16777216)%uint63
                    then pages_list (S (Z.to_nat (to_Z (l >> 12)))) ((o + 4095) >> 12)%uint63 (((o + l) >> 12) - 1)%uint63 else []
     | _ => [] end) FACTS0.
Definition add_pages_unk (ts : int) (pns : list int) (r : rdesc) : rdesc :=
  if (rd_tag r =? ts)%uint63 then
    let have := map pd_pn (rd_pages r) in
    RD (rd_tag r) (rd_lo r) (rd_len r) (rd_align r) (rd_dflt r)
       (rd_pages r ++ map (fun pn => PD pn true PKUnk []) (filter (fun pn => negb (existsb (fun q => (q =? pn)%uint63) have)) pns))
  else r.
Definition d : sdesc := SD (sd_pc d2) (sd_regs d2) (map (fun r => set_ro (drop_partial (add_pages_unk TSB slice_pages (add_pages 3%uint63 false (pages_list 256 0%uint63 255%uint63) (add_pages TSBS true (xa_pages TSBS) r))))) (sd_mem d2)).
Definition STK_RANGE : Z * Z := odflt (0, 0) (AX2.base_range (CAP.kn START) (tte TT 2%uint63)).
Definition MAXI : int := 9223372036854775807%uint63.
Definition bs : list ditem := [(4%uint63, 0%uint63, 0%uint63, RK_plain)]
  ++ flat_map (fun s : rshape =>
       if (sh_tag s =? 0)%uint63 || (sh_tag s =? 4)%uint63 then [] else
       if (sh_tag s land 1 =? 1)%uint63 then [(sh_tag s, 0%uint63, MAXI, RK_shadow (sh_tag s - 1))] else
       match AX2.base_range (CAP.kn START) (tte TT (sh_tag s)) with
       | Some (blo, bhi) => [(sh_tag s, of_Z (if (sh_tag s =? TSB)%uint63 then 17594333429760 else blo), of_Z bhi, RK_plain)]
       | None => [] end) shapes.
Definition is_lazy_am (m : CAP.amap) : bool := match CAP.am_kind m with CAP.KRWLAZY => true | _ => false end.
Definition LZ0 : list fent := map snd (filter (fun p => is_lazy_am (fst p)) (combine (CAP.a_maps START) ALL0)).
Definition V2 : list fent := filter (fun e => negb (fent_tag e =? 0)%uint63 && negb (fent_tag e =? TG)%uint63) ALL0.
Definition RBYTES : Z := State.live_bytes (segments_reserved HASEGS).
(* [comment removed for export] *)
Definition EX0 : list fent := filter (fun e => negb (fent_tag e =? 0)%uint63) ALL0.
(* [comment removed for export] *)
Definition XAB : Z := fold_right (fun (e : fent) acc => to_Z (snd e) + 8192 + acc) 0 XA.
Definition L3 : fledger3 :=
  FL3 (FL V2 [] 0%uint63 (Z.of_nat (List.length ALL0)) (CAP.a_totsz START - RBYTES)) ALL0 [] LZ0 [] (CAP.a_abytes START + XAB) (CAP.a_eager START) EX0 ([(TSB, TG, 0); (TG, TSB, -65536)] ++ ORD_T ++ ORD_N) ([]).
Definition W : Z := CAP.img_hi HAT.   (* [comment removed for export] *)

Definition BP : int := 2024868%uint63.
Definition shp (l : int) : bool := true.
Definition oelse {T} (a b : option T) : option T := match a with Some x => Some x | None => b end.
Definition xask (F : fstate) : option (int * int) := oelse (xask_b5 IM code F) (xask_band code F).
Definition RC : Z := Z.of_nat (List.length (segments_reserved HASEGS)).
(* [comment removed for export] *)
Definition SHREGS : list rshape := filter (fun s : rshape => (sh_tag s land 1 =? 1)%uint63) shapes.
Definition XF : list hfact := [HZero 3%uint63 0%uint63 1048576%uint63]
  ++ flat_map (fun e : fent => let '(t, o, l) := e in [HZero t o l; HWr t o l]) XA
  ++ flat_map (fun s1 : rshape => flat_map (fun s2 : rshape =>
        if (sh_tag s1 <? sh_tag s2)%uint63 then
          let '(t1, lo1, len1, _, _) := s1 in let '(t2, lo2, len2, _, _) := s2 in [HDisj t1 lo1 len1 t2 lo2 len2] else []) SHREGS) SHREGS
  ++ FILLX.
