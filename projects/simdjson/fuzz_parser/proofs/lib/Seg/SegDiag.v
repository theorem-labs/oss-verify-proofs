(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AS Require Import AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AS Require AxSymRun3.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Seg Require Import SegLearn SegDisch SegFP SegExplore SegLin SegTmpl SegGhost SegCall SegProg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.

Module SD.
Import SDI. Import SX. Import ST. Import SP.

Inductive dres :=
| DOk (x : sexit)
| DFail (why : nat) (pc : Z) (ss : sym_state) (scs : list sidecond).
(* [comment removed for export] *)

Section D.
Variable segs : list Segment.
Variable IT : itab.
Variable stops : list Z.
Variable rr : bool.

Variable sps : list split.
Variable aw : option (list awin).

Fixpoint dexplore (fuel : nat) (first nosp : bool) (bc : bctx) (kx : kix) (ss : sym_state) (path : list sidecond) : list dres :=
  match fuel with
  | O => [DFail 1 (s_pc ss) ss []]
  | S f =>
    if (negb first && existsb (Z.eqb (s_pc ss)) stops)%bool then
      (if s_clean ss then [DOk (SXT ss path)] else [DFail 2 (s_pc ss) ss []])
    else
    match (if nosp then None else find_split (s_pc ss) sps) with
    | Some (SpCmpG v _ c e1 e2) =>
        let a := sp_sub v ss e1 in let b := sp_sub v ss e2 in
        if (AxSymRun3.expr_vars_lt (s_next ss) a && AxSymRun3.expr_vars_lt (s_next ss) b)%bool then
          let kn := s_know ss in
          (match SL.learn (facts_of kn) c true a b with
           | None => []
           | Some l => let kn1 := l ++ kn in dexplore f first true (mkbc (facts_of kn1)) (mk_kix kn1) (set_know ss kn1) (SCBr true c a b :: path)
           end) ++
          (match SL.learn (facts_of kn) c false a b with
           | None => []
           | Some l => let kn0 := l ++ kn in dexplore f first true (mkbc (facts_of kn0)) (mk_kix kn0) (set_know ss kn0) (SCBr false c a b :: path)
           end)
        else [DFail 10 (s_pc ss) ss []]
    | Some (SpEnumG v _ e lo hi) =>
        let a := sp_sub v ss e in
        if (AxSymRun3.expr_vars_lt (s_next ss) a && Z.leb 0 lo && Z.ltb hi (2^64) &&
            match erange (facts_of (s_know ss)) a with Some (l, h) => (Z.leb lo l && Z.leb h hi)%bool | None => false end)%bool then
          flat_map (fun v => let kn1 := KRange a v v :: s_know ss in
                             dexplore f first true (mkbc (facts_of kn1)) (mk_kix kn1) (set_know ss kn1) (SCBr true BC_EQ a (ELit v) :: path))
                   (map (fun k => lo + Z.of_nat k) (seq 0 (S (Z.to_nat (hi - lo)))))
        else [DFail 11 (s_pc ss) ss []]
    | Some (SpEnumS _ n lo hi) =>
        let a := EVar n in
        if (AxSymRun3.expr_vars_lt (s_next ss) a && Z.leb 0 lo && Z.ltb hi (2^64) &&
            match erange (facts_of (s_know ss)) a with Some (l, h) => (Z.leb lo l && Z.leb h hi)%bool | None => false end)%bool then
          flat_map (fun v => match SL.sub_facts (facts_of (s_know ss)) n v with
                             | None => []
                             | Some D => let kn1 := D ++ KRange a v v :: s_know ss in
                                 dexplore f first true (mkbc (facts_of kn1)) (mk_kix kn1) (set_know ss kn1) (SCBr true BC_EQ a (ELit v) :: path)
                             end)
                   (map (fun k => lo + Z.of_nat k) (seq 0 (S (Z.to_nat (hi - lo)))))
        else [DFail 11 (s_pc ss) ss []]
    | Some (SpRdK _) =>
        let kn1 := rd_know (facts_of (s_know ss)) path ++ s_know ss in
        dexplore f first true (mkbc (facts_of kn1)) (mk_kix kn1) (set_know ss kn1) path
    | Some (SpHav _ r) => if (Nat.ltb 0 r && Nat.ltb r 32)%bool then dexplore f first true bc kx (shav ss r) path else [DFail 12 (s_pc ss) ss []]
    | Some (SpSlt _) => dexplore f first true bc kx (sslt ss) path
    | Some (SpW _) => dexplore f first true bc kx (sw ss) path
    | Some (SpAl _) =>
        let kn := s_know ss in
        match SL.al_tight (facts_of kn) (facts_of kn) with
        | None => []
        | Some l => let kn1 := l ++ kn in dexplore f first true (mkbc (facts_of kn1)) (mk_kix kn1) (set_know ss kn1) path
        end
    | None =>
    match itab_lookup IT (s_pc ss) with
    | None => [DFail 3 (s_pc ss) ss []]
    | Some i =>
      match i with
      | Branch c rs1 rs2 _ =>
        match sym_stepBI bc kx segs i ss (SCR [true] [] []) with
        | SOk ss1 [] _ => dexplore f false false bc kx ss1 path
        | SOk ss1 (_ :: _) _ =>
          match sym_stepBI bc kx segs i ss (SCR [false] [] []) with
          | SOk ss0 (_ :: _) _ =>
            let a := sr_get (s_regs ss) rs1 in
            let b := sr_get (s_regs ss) rs2 in
            let kn := s_know ss in
            let r1 := match SL.learn (facts_of kn) c true a b with
                      | None => []
                      | Some l => let kn1 := l ++ kn in
                                  dexplore f false false (mkbc (facts_of kn1)) (mk_kix kn1) (set_know ss1 kn1) (SCBr true c a b :: path)
                      end in
            let r0 := match SL.learn (facts_of kn) c false a b with
                      | None => []
                      | Some l => let kn0 := l ++ kn in
                                  dexplore f false false (mkbc (facts_of kn0)) (mk_kix kn0) (set_know ss0 kn0) (SCBr false c a b :: path)
                      end in
            r1 ++ r0
          | _ => [DFail 5 (s_pc ss) ss []]
          end
        | SStop => [DFail 4 (s_pc ss) ss []]
        end
      | _ =>
        if negb (acc_check aw i ss) then [DFail 8 (s_pc ss) ss []] else
        match (if SFP.is_fp_instr i then SFP.fp_step segs i ss else sym_stepBI bc kx segs i ss scr_nil) with
        | SOk ss' scs _ =>
            let rest := x_filterB segs bc ss ss' scs in
            if (Nat.leb (s_next ss) (s_next ss') && rest_ok segs bc ss ss' scs)%bool then
              dexplore f false false bc kx (respell ss' (s_next ss) scs i) (if rr then List.filter is_readbase scs ++ path else path)
            else [DFail 7 (s_pc ss) ss rest]
        | SStop => [DFail 6 (s_pc ss) ss path]
        end
      end
    end
    end
  end.

Definition dstart (fuel : nat) (ss : sym_state) : list dres :=
  dexplore fuel true false (mkbc (facts_of (s_know ss))) (mk_kix (s_know ss)) ss [].
End D.

(* [comment removed for export] *)
Definition dsumm (l : list dres) : list (nat * Z * nat) :=
  map (fun d => match d with DOk x => (0%nat, s_pc (x_ss x), length (x_path x)) | DFail w pc _ _ => (w, pc, 0%nat) end) l.

Definition dfails (l : list dres) : list dres :=
  List.filter (fun d => match d with DOk _ => false | _ => true end) l.

(* [comment removed for export] *)
Definition dedge (segs : list Segment) (gfp : nat -> list expr -> list SG.gwin) (gvc : SG.vc -> bool)
    (P : prog) (T : tmpl) (x : sexit) (xh : xhint) : nat * Z * list expr * option SG.vc :=
  let ss := x_ss x in
  match exit_kn ss with
  | None => (1%nat, s_pc ss, [], None)
  | Some kn' =>
    if negb (wins_ok (p_W P) (s_know ss) (s_log ss)) then (2%nat, s_pc ss, [], None) else
    let tgt := match find_tm (s_pc ss) (p_tm P ++ p_xt P) with Some T' => Some (T', true) | None =>
               match find_csr (s_pc ss) (nth 1 (s_regs ss) (ELit 0)) (p_cs P) with Some _ => None | None =>
               match find_tm (s_pc ss) (p_ex P) with Some X => Some (X, false) | None => None end end end in
    match tgt with
    | None => (match find_csr (s_pc ss) (nth 1 (s_regs ss) (ELit 0)) (p_cs P) with Some _ => 10%nat | None => 8%nat end, s_pc ss, [], None)
    | Some (T', loop) =>
        let sg := mk_sg (p_G P) T' (s_regs ss) kn' (xh_sg xh) in
        if negb (regs_match kn' (s_regs ss) (map (esub sg) (t_regs T'))) then (4%nat, s_pc ss, sg, None) else
        let ovc := edge_vc segs gfp T T' x kn' sg (xh_fk xh) in
        if negb (match ovc with None => true | Some c => gvc c end) then (9%nat, s_pc ss, sg, ovc) else
        if (loop && negb (decreases (map (ksub sg) (t_know T') ++ kn') T T' sg (xh_dec xh)))%bool then (6%nat, s_pc ss, sg, ovc) else
        if negb (globals_id (p_G P) sg && Nat.eqb (length sg) (t_ns T'))%bool then (7%nat, s_pc ss, sg, ovc) else (0%nat, s_pc ss, [], ovc)
    end
  end.

(* [comment removed for export] *)
Definition dcall (segs : list Segment) (gfp : nat -> list expr -> list SG.gwin) (gvc : SG.vc -> bool)
    (P : prog) (IT : itab) (T : tmpl) (x : sexit) (xh : xhint) (Sm : summ) : list (nat * Z * list expr * option SG.vc) :=
  let ss := x_ss x in
  match exit_kn ss with
  | None => [(1%nat, s_pc ss, [], None)]
  | Some kn' =>
    if negb (wins_ok (p_W P) (s_know ss) (s_log ss)) then [(2%nat, s_pc ss, [], None)] else
    let sg := mk_sg 0 (sm_pre Sm) (s_regs ss) kn' (xh_sg xh) in
    let Wc := map (SC.sub_win sg) (sm_W Sm) in
    if negb (Nat.eqb (length sg) (t_ns (sm_pre Sm))) then [(11%nat, s_pc ss, sg, None)] else
    if negb (forallb (AxSymRun3.expr_vars_lt (s_next ss)) sg) then [(12%nat, s_pc ss, sg, None)] else
    if negb (Nat.leb (t_ns T) (s_next ss)) then [(13%nat, s_pc ss, sg, None)] else
    if negb (regs_match kn' (s_regs ss) (map (esub sg) (t_regs (sm_pre Sm)))) then [(14%nat, s_pc ss, sg, None)] else
    let ovc := edge_vc segs gfp T (sm_pre Sm) x kn' sg (xh_fk xh) in
    if negb (match ovc with None => true | Some c => gvc c end) then [(15%nat, s_pc ss, sg, ovc)] else
    if negb (forallb (fun wc => let '(b, off, n) := wc in
                     existsb (fun w' => let '(b', off', n') := w' in SLin.xinside2 kn' b off n b' off' n') (p_W P)) Wc)
    then [(16%nat, s_pc ss, sg, None)] else
    if negb (acc_cont (p_A P) (sm_A Sm) sg kn') then [(20%nat, s_pc ss, sg, None)] else
    if negb (ps_ok P Sm sg kn') then [(21%nat, s_pc ss, sg, None)] else
    if negb (stk_ok P Sm sg kn') then [(23%nat, s_pc ss, sg, None)] else
    if negb (crs_ok P Sm sg kn') then [(24%nat, s_pc ss, sg, None)] else
    flat_map (fun X =>
      if negb (ret_ok' Sm IT X) then [(17%nat, t_pc X, [], None)] else
      if negb (Nat.leb (sm_G Sm) (t_ns X)) then [(18%nat, t_pc X, [], None)] else
      match ret_pc Sm sg X with
      | None => [(19%nat, t_pc X, sg, None)]
      | Some rpc => if negb (pr_pc_ok Sm X rpc) then [(22%nat, t_pc X, sg, None)] else
                    let '(xC, src) := call_exit gfp P T x kn' Sm sg X rpc in
                    let T0 := TMG (t_pc T) (t_regs T) (t_know T) (t_ns T) (t_meas T) (t_rank T) src in
                    [dedge segs gfp gvc P T0 xC xh0]
      end) (sm_post Sm)
  end.

(* [comment removed for export] *)
Fixpoint hist_add (k : nat * Z) (h : list (nat * Z * nat)) : list (nat * Z * nat) :=
  match h with
  | [] => [(fst k, snd k, 1%nat)]
  | (c, p, n) :: r => if (Nat.eqb c (fst k) && Z.eqb p (snd k))%bool then (c, p, S n) :: r else (c, p, n) :: hist_add k r
  end.
Definition hist (l : list (nat * Z)) : list (nat * Z * nat) := fold_left (fun h k => hist_add k h) l [].

(* [comment removed for export] *)
Definition harvest (segs : list Segment) (gfp : nat -> list expr -> list SG.gwin) (P : prog) (IT : itab) (fuel : nat) (rr : bool)
    : list (Z * Z * SG.vc) :=
  let stops := p_stops P in
  flat_map (fun T =>
    flat_map (fun d => match d with
      | DOk x => match dedge segs gfp (fun _ => true) P T x xh0 with
                 | (_, pc, _, Some c) => [(t_pc T, pc, c)]
                 | _ => []
                 end
      | _ => []
      end) (dstart segs IT stops rr (p_sp P) (p_A P) fuel (tstate T))) (p_tm P).

(* [comment removed for export] *)
Definition is_pure (K : kentry) : bool := match K with KRange _ _ _ | KAlign _ _ | KDisj _ _ _ _ => true | _ => false end.
Definition vc_trim (c : SG.vc) : SG.vc :=
  SG.VC (List.filter is_pure (SG.vc_kn c)) (SG.vc_path c) (SG.vc_log c) (SG.vc_src c) (SG.vc_tgt c) (SG.vc_facts c).
Definition vc_dflt : SG.vc := SG.VC [] [] [] [] [] [].

(* [comment removed for export] *)
Definition lp_facts (kn : list kentry) : list (expr * Z * Z * lin) :=
  flat_map (fun K => match K with KRange e l h => if fact_nowrap kn e h then [(e, l, h, lin_of e)] else [] | _ => [] end) kn.

Fixpoint lin_atoms (l : list (Z * expr)) : list expr := match l with [] => [] | (_, a) :: r => a :: lin_atoms r end.

Definition lp_ranges (kn : list kentry) (atoms : list expr) : list (expr * option (Z * Z)) := map (fun a => (a, SLin.arng kn a)) atoms.

End SD.
