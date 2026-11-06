(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec AxSymExec3 AxSymExec3B AsanPlanCore LibSym SegRun SegPlan SegPlanAuto.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutOpsF CutCert CutOps CutHeap.
Import ListNotations. Import AX2. Import AX2B.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module CA.
Inductive xtree : Type :=
| XStep (st : SR.sstep) (k : xtree)
| XCopyX (k : xtree)
| XFillX (k : xtree)
| XBranch (kt kf : xtree)
| XCase (e : expr) (mid : Z) (klo khi : xtree)
| XFact (K : kentry) (k : xtree)
| XAbstract (b : expr) (o n : Z) (k : xtree)
| XCoalesce (b : expr) (o : Z) (n : expr) (k : xtree)
| XRespell (r : nat) (e : expr) (k : xtree)
| XPin (v : nat) (c : Z) (k : xtree)
| XRefine (v : nat) (lo hi : Z) (k : xtree)
| XLoadByte (k : xtree)                          (* [comment removed for export] *)
| XOp (op : CX.xop) (k : xtree)                  (* [comment removed for export] *)
| XOp2 (op : CX.xop2) (ka kb : xtree)            (* [comment removed for export] *)
| XLeaf (ps : SR.post_spec) (t : CC.tag)
| XDead
| XStuck (code : Z) (ss : sym_state).

(* [comment removed for export] *)
Record pout : Type := PO { po_plan : SGP.splan; po_leaves : list (SR.post_spec * CC.tag); po_ops : list CX.xop; po_ops2 : list CX.xop2 }.
Fixpoint plan_of (t : xtree) (n a b : nat) : pout :=
  let un (f : SGP.splan -> SGP.splan) (k : xtree) := let r := plan_of k n a b in PO (f (po_plan r)) (po_leaves r) (po_ops r) (po_ops2 r) in
  let bin (f : SGP.splan -> SGP.splan -> SGP.splan) (k1 k2 : xtree) (extra2 : list CX.xop2) (b0 : nat) :=
      let r1 := plan_of k1 n a b0 in
      let r2 := plan_of k2 (n + length (po_leaves r1))%nat (a + length (po_ops r1))%nat (b0 + length (po_ops2 r1))%nat in
      PO (f (po_plan r1) (po_plan r2)) (po_leaves r1 ++ po_leaves r2) (po_ops r1 ++ po_ops r2) (extra2 ++ po_ops2 r1 ++ po_ops2 r2) in
  match t with
  | XStep st k => un (SGP.PStep st) k
  | XCopyX k => un SGP.PCopyX k
  | XFillX k => un SGP.PFillX k
  | XBranch kt kf => bin SGP.PBranch kt kf [] b
  | XCase e mid klo khi => bin (SGP.PCase e mid) klo khi [] b
  | XFact K k => un (SGP.PFact K) k
  | XAbstract bb o m k => un (SGP.PAbstract bb o m) k
  | XCoalesce bb o m k => un (SGP.PCoalesce bb o m) k
  | XRespell r e k => un (SGP.PRespell r e) k
  | XPin v c k => un (SGP.PPin v c) k
  | XRefine v lo hi k => un (SGP.PRefine v lo hi) k
  | XLoadByte k => un SGP.PLoadByte k
  | XOp op k => let r := plan_of k n (S a) b in PO (SGP.PX a (po_plan r)) (po_leaves r) (op :: po_ops r) (po_ops2 r)
  | XOp2 op ka kb => bin (SGP.PX2 b) ka kb [op] (S b)
  | XLeaf ps tg => PO (SGP.PEnd n) [(ps, tg)] [] []
  | XDead => PO (SGP.PEnd 0) [] [] []
  | XStuck _ _ => PO (SGP.PEnd 0) [] [] []
  end.
Fixpoint stucks (t : xtree) : list (Z * sym_state) :=
  match t with
  | XStep _ k | XCopyX k | XFillX k | XFact _ k | XAbstract _ _ _ k | XCoalesce _ _ _ k | XRespell _ _ k | XPin _ _ k | XRefine _ _ _ k | XOp _ k | XLoadByte k => stucks k
  | XBranch a b | XCase _ _ a b | XOp2 _ a b => stucks a ++ stucks b
  | XLeaf _ _ | XDead => []
  | XStuck c ss => [(c, ss)]
  end.
Fixpoint size (t : xtree) : nat :=
  match t with
  | XStep _ k | XCopyX k | XFillX k | XFact _ k | XAbstract _ _ _ k | XCoalesce _ _ _ k | XRespell _ _ k | XPin _ _ k | XRefine _ _ _ k | XOp _ k | XLoadByte k => S (size k)
  | XBranch a b | XCase _ _ a b | XOp2 _ a b => S (size a + size b)
  | _ => 1%nat
  end.

(* [comment removed for export] *)
Record callsum : Type := CSUM {
  cs_pc : Z;                                           (* [comment removed for export] *)
  cs_clob : list expr -> list (expr * Z * expr);       (* [comment removed for export] *)
  cs_a0 : list expr -> option expr;                    (* [comment removed for export] *)
  cs_res : list expr -> expr -> list kentry;           (* [comment removed for export] *)
  cs_newblk : list expr -> option expr;                (* [comment removed for export] *)
  cs_free : bool;                                      (* [comment removed for export] *)
  cs_inl : option (Z * list nat);                      (* [comment removed for export] *)
  cs_scratch : Z;                                      (* [comment removed for export] *)
  cs_alloc : bool;                                     (* [comment removed for export] *)
  cs_blob : bool                                       (* [comment removed for export] *)
}.

Section WithImage.
Variable segs : list Segment.
Variable IT : itab.
Variable x_cpy x_set x_len ro_lo ro_hi : Z.
Variable BFUEL : nat.
Variable A : APC.atable.
Variable NF : nat.
Variable CPS : list CC.cutpoint.       (* [comment removed for export] *)
Variable ENDS : list Z.                (* [comment removed for export] *)
Variable CSUMS : list callsum.         (* [comment removed for export] *)
Definition CALLS : list Z := map cs_pc CSUMS.
Variable FORGET_N : nat.               (* [comment removed for export] *)
Variable FORGET_KEEP : list nat.
Variable NAME_PCS : list Z.            (* [comment removed for export] *)
Variable XSTOPS : list Z.              (* [comment removed for export] *)

Definition cut_pcs : list Z := map CC.cp_pc CPS.
Definition STOPS : list Z := cut_pcs ++ ENDS ++ CALLS ++ XSTOPS ++ NAME_PCS ++ [x_cpy; x_set].   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition bound (s : CC.subst) (v : nat) : bool := existsb (fun p : nat * expr => Nat.eqb (fst p) v) s.
Fixpoint all_bound (s : CC.subst) (e : expr) : bool :=
  match e with
  | ELit _ | EBlob _ _ _ _ => true
  | EVar n => Nat.ltb n NF || bound s n
  | EAlu _ a b | EAluw _ a b | EMd _ a b | EMdw _ a b => all_bound s a && all_bound s b
  | EExt _ _ _ a => all_bound s a
  end.
Fixpoint bind_regs (ts rs : list expr) (s : CC.subst) : CC.subst :=
  match ts, rs with
  | t :: tr, e :: er =>
      bind_regs tr er (match t with
                       | EVar v => if (Nat.leb NF v && negb (bound s v))%bool then (v, e) :: s else s
                       | _ => s
                       end)
  | _, _ => s
  end.
(* [comment removed for export] *)
Fixpoint unify (t e : expr) (s : CC.subst) : CC.subst :=
  match t, e with
  | EVar v, _ => if (Nat.leb NF v && negb (bound s v))%bool then (v, e) :: s else s
  | EAlu op a b, EAlu op' a' b' => if expr_eqb (EAlu op (ELit 0) (ELit 0)) (EAlu op' (ELit 0) (ELit 0)) then unify b b' (unify a a' s) else s
  | EMd op a b, EMd op' a' b' => if expr_eqb (EMd op (ELit 0) (ELit 0)) (EMd op' (ELit 0) (ELit 0)) then unify b b' (unify a a' s) else s
  | _, _ => s
  end.
(* [comment removed for export] *)
Fixpoint unbound_vars (s : CC.subst) (e : expr) : list nat :=
  match e with
  | EVar n => if (Nat.ltb n NF || bound s n)%bool then [] else [n]
  | EAlu _ a b | EAluw _ a b | EMd _ a b | EMdw _ a b => unbound_vars s a ++ unbound_vars s b
  | EExt _ _ _ a => unbound_vars s a
  | _ => []
  end.
Definition solve1 (kn : list kentry) (t e : expr) (s : CC.subst) : CC.subst :=
  match unbound_vars s t with
  | v :: r =>
      if forallb (Nat.eqb v) r then
        let t0 := CC.esubstL NF ((v, ELit 0) :: s) t in
        let ok (c : expr) := match erange kn (APC.esub e (CC.esubstL NF ((v, c) :: s) t)) with Some (0, 0) => true | _ => false end in
        let c1 := APC.esub e t0 in let c2 := APC.esub t0 e in
        if ok c1 then (v, c1) :: s else if ok c2 then (v, c2) :: s else s
      else s
  | [] => s
  end.
Fixpoint bind_cells (kn tk : list kentry) (s : CC.subst) : CC.subst :=
  match tk with
  | [] => s
  | KWord a w (EVar c) :: r =>
      bind_cells kn r
        (if (Nat.leb NF c && negb (bound s c) && all_bound s (a_base a))%bool
         then match SGP.cell_value kn (CC.asubstL NF s a) w with Some e => (c, e) :: s | None => s end
         else s)
  | KWord a w tv :: r =>
      bind_cells kn r
        (if (negb (all_bound s tv) && all_bound s (a_base a))%bool
         then match SGP.cell_value kn (CC.asubstL NF s a) w with
              | Some e => let s1 := solve1 kn tv e s in if all_bound s1 tv then s1 else unify tv e s      (* [comment removed for export] *)
              | None => s end
         else s)
  | _ :: r => bind_cells kn r s
  end.
Fixpoint bind_rounds (n : nat) (kn tk : list kentry) (s : CC.subst) : CC.subst :=
  match n with O => s | S m => bind_rounds m kn tk (bind_cells kn tk s) end.
Fixpoint solve_regs (kn : list kentry) (ts rs : list expr) (s : CC.subst) : CC.subst :=
  match ts, rs with t :: tr, e :: er => solve_regs kn tr er (solve1 kn t e s) | _, _ => s end.

(* [comment removed for export] *)
Definition has (kn : list kentry) (X : kentry) : bool := existsb (APC.kentry_eqb X) kn.
Definition set_kn := SGP.set_kn.

(* [comment removed for export] *)
Inductive fixup := FFact (K : kentry) | FOp (op : CX.xop) | FAbs (b : expr) (o n : Z) | FCoal (b : expr) (o : Z) (n : expr) | FResp (r : nat) (e : expr).
Definition apply_fix (f : fixup) (ss : sym_state) : option sym_state :=
  match f with
  | FFact K => if (APC.fact_ok (s_know ss) K && APC.kentry_vars_lt (s_next ss) K)%bool then Some (set_kn ss (K :: s_know ss)) else None
  | FOp op => CX.xop_applyA A op ss
  | FAbs b o n => SGP.abstract A ss b o n
  | FCoal b o n => SGP.coalesce A ss b o n
  | FResp r e => SGP.respell ss r e
  end.
Definition FOFact (K : kentry) : fixup := FOp (CX.OFact K).
Definition wrap_fix (f : fixup) (k : xtree) : xtree :=
  match f with FFact K => XFact K k | FOp op => XOp op k | FAbs b o n => XAbstract b o n k | FCoal b o n => XCoalesce b o n k | FResp r e => XRespell r e k end.

(* [comment removed for export] *)
Definition unk_fix (kn : list kentry) (X : kentry) : option (option fixup) :=
  if has kn X then Some None else
  match X with
  | KUnk (SA b o) (ELit n) => Some (Some (FOp (CX.OAbsW b o n)))      (* [comment removed for export] *)
  | KUnk (SA b o) n => Some (Some (FOp (CX.OCoalW b o n)))
  | _ => Some None   (* [comment removed for export] *)
  end.
Definition is_fact (X : kentry) : bool := match X with KRange _ _ _ | KAlign _ _ | KDisj _ _ _ _ => true | _ => false end.

Inductive cres := COk (t : xtree) | CFail (code : Z) (X : option kentry) (ss : sym_state).

Fixpoint run_fixes (fs : list fixup) (ss : sym_state) : option sym_state :=
  match fs with [] => Some ss | f :: r => match apply_fix f ss with Some s' => run_fixes r s' | None => None end end.
Fixpoint wrap_fixes (fs : list fixup) (k : xtree) : xtree :=
  match fs with [] => k | f :: r => wrap_fix f (wrap_fixes r k) end.

(* [comment removed for export] *)
Fixpoint run_fixes_dbg (fs : list fixup) (ss : sym_state) : sym_state * option fixup :=
  match fs with
  | [] => (ss, None)
  | f :: r => match apply_fix f ss with Some s' => run_fixes_dbg r s' | None => (ss, Some f) end
  end.

Definition meas_facts (mi : expr) (cj : CC.cutpoint) (s : CC.subst) : list kentry :=
  let mj := CC.esubstL NF s (CC.cp_meas cj) in
  [KRange (APC.esub mi mj) 1 CC.MB; KRange mi 0 CC.MB; KRange mj 0 CC.MB].

Definition close1 (mi : expr) (hints : CC.subst) (j : nat) (cj : CC.cutpoint) (ss : sym_state) : cres :=
  let s0 := bind_regs (CC.cp_regs cj) (s_regs ss) hints in
  let s1 := bind_rounds 4 (s_know ss) (CC.cp_know cj) s0 in
  let s := solve_regs (s_know ss) (CC.cp_regs cj) (s_regs ss) (solve_regs (s_know ss) (CC.cp_regs cj) (s_regs ss) s1) in
  let want_regs := map (CC.esubstL NF s) (CC.cp_regs cj) in
  let want_kn := map (CC.ksubstL NF s) (CC.cp_know cj) ++ meas_facts mi cj s in
  (* [comment removed for export] *)
  let rfix := flat_map (fun r => let w := nth r want_regs (ELit 0) in
                                 if expr_eqb w (nth r (s_regs ss) (ELit 0)) then [] else [FResp r w]) (seq 1 31) in
  let '(ss1, bad1) := run_fixes_dbg rfix ss in
  match bad1 with
  | Some (FResp r e) => CFail (960 + Z.of_nat r) (Some (KRange e 0 0)) ss
  | Some _ => CFail 969 None ss
  | None =>
      (* [comment removed for export] *)
      let ufix := flat_map (fun X => match unk_fix (s_know ss1) X with Some (Some f) => [f] | _ => [] end) want_kn in
      let '(ss2, bad2) := run_fixes_dbg ufix ss1 in
      match bad2 with
      | Some (FAbs b o n) | Some (FOp (CX.OAbsW b o n)) => CFail 970 (Some (KUnk (SA b o) (ELit n))) ss1
      | Some (FCoal b o n) | Some (FOp (CX.OCoalW b o n)) => CFail 971 (Some (KUnk (SA b o) n)) ss1
      | Some _ => CFail 979 None ss1
      | None =>
          (* [comment removed for export] *)
          let ffix := flat_map (fun X => if has (s_know ss2) X then [] else
                                         if is_fact X then (if APC.fact_ok (s_know ss2) X then [FFact X] else [FOFact X]) else []) want_kn in
          let '(ss3, bad3) := run_fixes_dbg ffix ss2 in
          match bad3 with
          | Some (FFact X) => CFail 980 (Some X) ss2
          | Some (FOp (CX.OFact X)) => CFail 981 (Some X) ss2
          | Some _ => CFail 989 None ss2
          | None =>
              (* [comment removed for export] *)
              match List.filter (fun X => negb (has (s_know ss3) X)) want_kn with
              | X :: _ => CFail 990 (Some X) ss3
              | [] =>
                  (* [comment removed for export] *)
                  let extra := match NAME_PCS with
                               | [] => []
                               | _ => List.filter (fun X => (match X with KRange _ _ _ => true | KWord _ 1 _ => true | _ => false end && negb (has want_kn X))%bool) (s_know ss3)
                               end in
                  let ps := SR.PS (CC.cp_pc cj) (map (fun r => (r, nth r want_regs (ELit 0))) (seq 1 31)) [] (want_kn ++ extra) in
                  COk (wrap_fixes (rfix ++ ufix ++ ffix) (XLeaf ps (CC.TGoto j s)))
              end
          end
      end
  end.

(* [comment removed for export] *)
Fixpoint close_go (mi : expr) (hints : list (nat * CC.subst)) (j : nat) (cps : list CC.cutpoint) (ss : sym_state) : option xtree :=
  match cps with
  | [] => None
  | cj :: r =>
      if Z.eqb (CC.cp_pc cj) (s_pc ss) then
        match close1 mi (match find (fun h : nat * CC.subst => Nat.eqb (fst h) j) hints with Some h => snd h | None => [] end) j cj ss with
        | COk t => Some t
        | CFail _ _ _ => close_go mi hints (S j) r ss
        end
      else close_go mi hints (S j) r ss
  end.
(* [comment removed for export] *)
Fixpoint close_dbg_go (mi : expr) (hints : list (nat * CC.subst)) (j : nat) (cps : list CC.cutpoint) (ss : sym_state)
  : list (nat * Z * option kentry) :=
  match cps with
  | [] => []
  | cj :: r =>
      (if Z.eqb (CC.cp_pc cj) (s_pc ss) then
         match close1 mi (match find (fun h : nat * CC.subst => Nat.eqb (fst h) j) hints with Some h => snd h | None => [] end) j cj ss with
         | COk _ => [(j, 0, None)]
         | CFail c X _ => [(j, c, X)]
         end
       else []) ++ close_dbg_go mi hints (S j) r ss
  end.
Definition close_dbg (mi : expr) (hints : list (nat * CC.subst)) (ss : sym_state) := close_dbg_go mi hints 0 CPS ss.

(* [comment removed for export] *)
Variable F : list SGP.region.          (* [comment removed for export] *)
Variable mi : expr.                    (* [comment removed for export] *)
Variable HINTS : list (nat * CC.subst).  (* [comment removed for export] *)

Definition STEP (st : SR.sstep) := SGP.step1 segs IT x_cpy x_set x_len ro_lo ro_hi BFUEL F st.
(* [comment removed for export] *)
Fixpoint fp_count (st : bool) (n : nat) (p : Z) : nat :=
  match n with
  | O => O
  | S n' => match itab_lookup IT p with
            | Some (Instr.FStore Instr.FMT_D _ _ _) => if st then S (fp_count st n' (p + 4)) else O
            | Some (Instr.FLoad Instr.FMT_D _ _ _) => if st then O else S (fp_count st n' (p + 4))
            | _ => O
            end
  end.
Definition fp_run (ss : sym_state) : option (SGA.aitem * sym_state) :=
  match itab_lookup IT (s_pc ss) with
  | Some (Instr.FStore Instr.FMT_D _ _ _) =>
      let k := fp_count true 32 (s_pc ss) in match STEP (SR.SFsdSeq k) ss with Some s' => Some (SGA.AStep (SR.SFsdSeq k), s') | None => None end
  | Some (Instr.FLoad Instr.FMT_D _ _ _) =>
      let k := fp_count false 32 (s_pc ss) in match STEP (SR.SFldSeq k) ss with Some s' => Some (SGA.AStep (SR.SFldSeq k), s') | None => None end
  | _ => None
  end.
Definition full_ps (ss : sym_state) : SR.post_spec :=
  SR.PS (s_pc ss) (map (fun r => (r, nth r (s_regs ss) (ELit 0))) (seq 1 31)) [] (s_know ss).
Fixpoint regs_eqb (a b : list expr) : bool :=
  match a, b with
  | [], [] => true
  | x :: a', y :: b' => expr_eqb x y && regs_eqb a' b'
  | _, _ => false
  end.
Definition wrap_item (it : SGA.aitem) (k : xtree) : xtree :=
  match it with SGA.AStep st => XStep st k | SGA.ACopyX => XCopyX k | SGA.AFillX => XFillX k end.

(* [comment removed for export] *)
Fixpoint expr_vars (e : expr) : list nat :=
  match e with
  | ELit _ | EBlob _ _ _ _ => []
  | EVar n => [n]
  | EAlu _ a b | EAluw _ a b | EMd _ a b | EMdw _ a b => expr_vars a ++ expr_vars b
  | EExt _ _ _ a => expr_vars a
  end.
Fixpoint expr_lits (e : expr) : list Z :=
  match e with
  | ELit z => [z]
  | EVar _ | EBlob _ _ _ _ => []
  | EAlu _ a b | EAluw _ a b | EMd _ a b | EMdw _ a b => expr_lits a ++ expr_lits b
  | EExt _ _ _ a => expr_lits a
  end.
Definition cur_range (ss : sym_state) (v : nat) : Z * Z :=
  match erange (s_know ss) (EVar v) with Some (l, h) => (Z.max l 0, Z.min h (two64 - 1)) | None => (0, two64 - 1) end.
Definition refine_cands (l h : Z) (lits : list Z) : list (Z * Z) :=
  List.filter (fun c : Z * Z => (Z.leb l (fst c) && Z.leb (fst c) (snd c) && Z.leb (snd c) h && negb (Z.eqb l (fst c) && Z.eqb h (snd c)))%bool)
    (flat_map (fun c => [(l, c - 1); (c, h); (l, c); (c + 1, h)]) lits ++ [(l + 1, h); (l, h - 1)]).
Fixpoint first_refine (ss : sym_state) (v : nat) (cands : list (Z * Z)) : option (Z * Z * sym_state) :=
  match cands with
  | [] => None
  | (lo, hi) :: r => match SGP.refine ss v lo hi with Some s' => Some (lo, hi, s') | None => first_refine ss v r end
  end.
(* [comment removed for export] *)
Fixpoint refine_var (n : nat) (lits : list Z) (v : nat) (ss : sym_state) : list (nat * Z * Z) * sym_state :=
  match n with
  | O => ([], ss)
  | S m => let '(l, h) := cur_range ss v in
           match first_refine ss v (refine_cands l h lits) with
           | Some (lo, hi, s') => let '(items, sf) := refine_var m lits v s' in ((v, lo, hi) :: items, sf)
           | None => ([], ss)
           end
  end.
Fixpoint refine_vars (lits : list Z) (vs : list nat) (ss : sym_state) : list (nat * Z * Z) * sym_state :=
  match vs with
  | [] => ([], ss)
  | v :: r => let '(i1, s1) := refine_var 2 lits v ss in let '(i2, s2) := refine_vars lits r s1 in (i1 ++ i2, s2)
  end.
Fixpoint wrap_refines (items : list (nat * Z * Z)) (k : xtree) : xtree :=
  match items with [] => k | (v, lo, hi) :: r => XRefine v lo hi (wrap_refines r k) end.
Definition after_branch (e : expr) (ss : sym_state) : list (nat * Z * Z) * sym_state :=
  refine_vars (expr_lits e) (nodup Nat.eq_dec (expr_vars e)) ss.
(* [comment removed for export] *)
Definition ltu_fix (e : expr) (taken : bool) (ss : sym_state) : list fixup * sym_state :=
  match e with
  | EAlu ALU_SLTU a b =>
      let f := if taken then FOp (CX.OLtu a b true) else FOp (CX.OLtu b a false) in
      match apply_fix f ss with Some s' => ([f], s') | None => ([], ss) end
  | EAlu ALU_SLT a b =>          (* [comment removed for export] *)
      let f := if taken then FOp (CX.OLts a b true) else FOp (CX.OLts b a false) in
      match apply_fix f ss with Some s' => ([f], s') | None => ([], ss) end
  | _ => ([], ss)
  end.

(* [comment removed for export] *)
Definition ENUM_MAX : Z := 300.
Fixpoint enum_go (n : nat) (v : nat) (lo hi : Z) (cont : sym_state -> xtree) (ss : sym_state) : xtree :=
  match n with
  | O => XStuck 97 ss
  | S n' =>
      if Z.eqb lo hi then
        match SGP.pin ss v lo with Some s' => XPin v lo (cont s') | None => XStuck 98 ss end
      else
        let mid := (lo + hi) / 2 in
        match SGP.case_arms ss (EVar v) mid with
        | Some (alo, ahi) =>
            XCase (EVar v) mid (match alo with Some s1 => enum_go n' v lo mid cont s1 | None => XDead end)
                               (match ahi with Some s2 => enum_go n' v (mid + 1) hi cont s2 | None => XDead end)
        | None => XStuck 99 ss
        end
  end.
Definition enum_candidate (ss : sym_state) : option (nat * Z * Z) :=
  let of_reg (rs1 : reg) :=
    let e := sr_get (s_regs ss) rs1 in
    find (fun c : nat * Z * Z => let '(_, l, h) := c in (Z.leb l h && Z.leb (h - l) ENUM_MAX)%bool)
         (map (fun v => let '(l, h) := cur_range ss v in (v, l, h)) (nodup Nat.eq_dec (expr_vars e))) in
  match itab_lookup IT (s_pc ss) with
  | Some (Instr.Load _ _ _ rs1 _) => of_reg rs1
  | Some (Instr.Jalr _ rs1 _) => of_reg rs1
  | _ => None
  end.

(* [comment removed for export] *)
Fixpoint subexprs (e : expr) : list expr :=
  e :: match e with
       | EAlu _ a b | EAluw _ a b | EMd _ a b | EMdw _ a b => subexprs a ++ subexprs b
       | EExt _ _ _ a => subexprs a
       | _ => []
       end.
Definition tighter (kn : list kentry) (e : expr) : list fixup :=
  match e with
  | ELit _ => []
  | _ =>
    match CX.range3 kn e with
    | Some (l, h) =>
        match erange kn e with
        | Some (l0, h0) => if (Z.ltb l0 l || Z.ltb h h0)%bool then [FOFact (KRange e (Z.max l l0) (Z.min h h0))] else []
        | None => [FOFact (KRange e l h)]
        end
    | None => []
    end
  end.
Definition branch_ops (ss : sym_state) : list expr :=
  match itab_lookup IT (s_pc ss) with
  | Some (Instr.Branch _ rs1 rs2 _) => subexprs (sr_get (s_regs ss) rs1) ++ subexprs (sr_get (s_regs ss) rs2)
  | _ => []
  end.
Definition tighten_fixes (ss : sym_state) : list fixup := flat_map (tighter (s_know ss)) (branch_ops ss).

(* [comment removed for export] *)
Definition clob_fact_k (kn : list kentry) (r : expr * Z * expr) : list kentry :=
  let '(b, o, n) := r in
  flat_map (fun X => match X with
                     | KWr (SA b' o') m => if (expr_eqb b b' && Z.leb o' o)%bool
                                           then [KRange (APC.esub m (APC.eaddz n (o - o'))) 0 CC.MB] else []
                     | _ => []
                     end) kn.
Definition clob_fact (kn : list kentry) (r : expr * Z * expr) : list fixup := map FOFact (clob_fact_k kn r).
Fixpoint best_effort (fs : list fixup) (ss : sym_state) : list fixup * sym_state :=
  match fs with
  | [] => ([], ss)
  | f :: r => match apply_fix f ss with
              | Some s' => let '(l, sf) := best_effort r s' in (f :: l, sf)
              | None => best_effort r ss
              end
  end.


(* [comment removed for export] *)
Fixpoint zgcd_nat (n : nat) (a b : Z) : Z := match n with O => Z.max 1 (Z.abs a) | S m => if Z.eqb b 0 then Z.max 1 (Z.abs a) else zgcd_nat m b (a mod b) end.
Definition pair_certs (F : list sfact) : list (list (nat * Z)) :=
  let idx := combine (seq 0 (length F)) F in
  map (fun p : nat * sfact => [(fst p, 1)]) idx
  ++ flat_map (fun p : nat * sfact =>
       flat_map (fun q : nat * sfact =>
         if Nat.ltb (fst p) (fst q) then
           flat_map (fun t : Z * expr =>
                       let ci := fst t in let cj := coef_of (snd t) (fst (snd q)) in
                       if Z.eqb cj 0 then [] else
                       let g := zgcd_nat 70 ci cj in [[(fst p, cj / g); (fst q, - (ci / g))]]) (fst (snd p))
         else []) idx) idx.
Definition find_contra (kn : list kentry) : option (list (nat * Z)) :=
  match sum_facts kn kn with
  | [] => None
  | F => find (CX.contra_chk kn) (pair_certs F)
  end.

(* [comment removed for export] *)
Definition scale_cert (l : Z) (c : list (nat * Z)) : list (nat * Z) := map (fun iq : nat * Z => (fst iq, l * snd iq)) c.
Definition cert_cands (F : list sfact) (ts : list (Z * expr)) : list (list (nat * Z)) :=
  flat_map (fun c : list (nat * Z) =>
              let tsS := fst (CX.comb F c [] 0 0) in
              flat_map (fun t : Z * expr => let cs := coef_of (snd t) tsS in
                                            if Z.eqb cs 0 then [] else if Z.eqb (fst t mod cs) 0 then [scale_cert (fst t / cs) c] else []) ts)
           (pair_certs F).
Definition best_cert (kn : list kentry) (e : expr) : option (list (nat * Z) * (Z * Z)) :=
  match sum_facts kn kn with
  | [] => None
  | F => fold_left (fun (best : option (list (nat * Z) * (Z * Z))) (c : list (nat * Z)) =>
                      match CX.cert_range kn e c with
                      | Some (A, B) => match best with
                                       | Some (_, (A0, B0)) => if Z.ltb (B - A) (B0 - A0) then Some (c, (A, B)) else best
                                       | None => Some (c, (A, B))
                                       end
                      | None => best
                      end) (cert_cands F (snd (lin_of e))) None
  end.
Definition cert_tighter (kn : list kentry) (e : expr) : list fixup :=
  match e with
  | ELit _ => []
  | _ => match best_cert kn e with
         | Some (c, (A, B)) =>
             match CX.range3 kn e with
             | Some (l0, h0) => if (Z.ltb l0 A || Z.ltb B h0)%bool then [FOp (CX.OFactC (KRange e (Z.max A l0) (Z.min B h0)) c)] else []
             | None => [FOp (CX.OFactC (KRange e A B) c)]
             end
         | None => []
         end
  end.
(* [comment removed for export] *)
Definition dead_or (cont : sym_state -> xtree) (ss : sym_state) : xtree :=
  match find_contra (s_know ss) with
  | Some cert => XOp (CX.OContra cert) (XCase (EVar (s_next ss)) 0 XDead XDead)
  | None => cont ss
  end.

Definition nm_load_addr (ss : sym_state) : option saddr :=
  match itab_lookup IT (s_pc ss) with
  | Some (Instr.Load _ _ _ rs1 imm) => Some (to_saddr (sr_get (s_regs ss) rs1) (bv_signed imm))
  | _ => None
  end.
Definition nm_fix (ss : sym_state) : option (fixup * sym_state) :=
  if existsb (Z.eqb (s_pc ss)) NAME_PCS then
    match nm_load_addr ss with
    | Some a => match SGP.cell_value (s_know ss) a 1 with
                | Some _ => None                                   (* [comment removed for export] *)
                | None => match apply_fix (FOp (CX.ONameB a)) ss with Some s1 => Some (FOp (CX.ONameB a), s1) | None => None end
                end
    | None => None
    end
  else None.

(* [comment removed for export] *)
Definition tab_val (kn : list kentry) (J : nat) (a : saddr) (w : nat) (v : Z) : option Z :=
  match SGP.eval_at J (a_base a) v with
  | Some ax => match know_bytes_lit segs kn (ELit 0) (ax + a_off a) w with Some zs => Some (zbytes_le_to_Z zs) | None => None end
  | None => None
  end.
Definition oz_eqb (a b : option Z) : bool := match a, b with Some x, Some y => Z.eqb x y | None, None => true | _, _ => false end.
(* [comment removed for export] *)
Fixpoint tab_runs (fuel : nat) (kn : list kentry) (J : nat) (a : saddr) (w : nat) (v : Z) (acc : list (Z * option Z)) : list (Z * option Z) :=
  match fuel with
  | O => acc
  | S f => let c := tab_val kn J a w v in
           tab_runs f kn J a w (v - 1) (match acc with
                                        | (_, c0) :: _ => if oz_eqb c c0 then acc else (v, c) :: acc
                                        | [] => [(v, c)]
                                        end)
  end.
Definition tab_leaf (J : nat) (a : saddr) (w : nat) (cont : sym_state -> xtree) (oc : option Z) (s : sym_state) : xtree :=
  match oc with
  | Some c => match CX.xop_applyS segs A (CX.OImgW a w J c) s with Some s1 => XOp (CX.OImgW a w J c) (cont s1) | None => XStuck 88 s end      (* [comment removed for export] *)
  | None => XStuck 87 s
  end.
Fixpoint tab_go (runs : list (Z * option Z)) (J : nat) (a : saddr) (w : nat) (cont : sym_state -> xtree) (ss : sym_state) : xtree :=
  match runs with
  | [] => XStuck 86 ss
  | (h, oc) :: rest =>
      match rest with
      | [] => tab_leaf J a w cont oc ss
      | _ :: _ =>
          match SGP.case_arms ss (EVar J) h with
          | Some (alo, ahi) => XCase (EVar J) h (match alo with Some s1 => tab_leaf J a w cont oc s1 | None => XDead end)
                                                (match ahi with Some s2 => tab_go rest J a w cont s2 | None => XDead end)
          | None => XStuck 99 ss
          end
      end
  end.
Definition tab_fix (cont : sym_state -> xtree) (ss : sym_state) : option xtree :=
  if existsb (Z.eqb (s_pc ss)) NAME_PCS then
    match itab_lookup IT (s_pc ss) with
    | Some (Instr.Load sz _ _ rs1 imm) =>
        let a := to_saddr (sr_get (s_regs ss) rs1) (bv_signed imm) in
        let w := msize_bytes sz in
        match nodup Nat.eq_dec (expr_vars (a_base a)) with
        | [J] => let '(l0, h0) := cur_range ss J in
                 (* [comment removed for export] *)
                 let '(l, h) := match CX.range3 (s_know ss) (EVar J) with Some (l1, h1) => (Z.max l0 l1, Z.min h0 h1) | None => (l0, h0) end in
                 let tight := negb (Z.eqb l l0 && Z.eqb h h0) in
                 let pre := if tight then apply_fix (FOFact (KRange (EVar J) l h)) ss else Some ss in
                 match pre with
                 | Some ss1 =>
                     if (Z.leb l h && Z.leb (h - l) CX.IMG_MAX)%bool then
                       let runs := tab_runs (Z.to_nat (h - l + 1)) (s_know ss1) J a w h [] in
                       if existsb (fun r : Z * option Z => match snd r with Some _ => true | None => false end) runs
                       then Some (if tight then wrap_fix (FOFact (KRange (EVar J) l h)) (tab_go runs J a w cont ss1) else tab_go runs J a w cont ss1) else None
                     else None
                 | None => None
                 end
        | _ => None
        end
    | _ => None
    end
  else None.

Fixpoint explore (fuel : nat) (first : bool) (ss : sym_state) : xtree :=
  match fuel with
  | O => XStuck 90 ss
  | S m =>
      if (negb first && existsb (Z.eqb (s_pc ss)) cut_pcs)%bool then
        match close_go mi HINTS 0 CPS ss with
        | Some t => t
        | None => (* [comment removed for export] *)
            if existsb (Z.eqb (s_pc ss)) ENDS then XLeaf (full_ps ss) (CC.TOther (s_pc ss)) else XStuck 96 ss
        end
      else if (negb first && existsb (Z.eqb (s_pc ss)) ENDS)%bool then XLeaf (full_ps ss) (CC.TOther (s_pc ss))
      else if (negb first && existsb (Z.eqb (s_pc ss)) CALLS)%bool then
        (* [comment removed for export] *)
        let ct := flat_map (fun r => flat_map (cert_tighter (s_know ss)) (rev (subexprs (nth r (s_regs ss) (ELit 0))))) [10; 12]%nat in
        let '(ct', ssc) := best_effort ct ss in
        let hf := flat_map (fun cs : callsum => if Z.eqb (cs_pc cs) (s_pc ss) then flat_map (clob_fact (s_know ssc)) (cs_clob cs (s_regs ssc)) else []) CSUMS in
        let '(hf0, ss0) := best_effort hf ssc in
        let hf' := ct' ++ hf0 in
        let K := KRange mi 1 CC.MB in
        if has (s_know ss0) K then wrap_fixes hf' (XLeaf (full_ps ss0) (CC.TOther (s_pc ss)))
        else let f := if APC.fact_ok (s_know ss0) K then FFact K else FOFact K in
             match apply_fix f ss0 with
             | Some s' => wrap_fixes hf' (wrap_fix f (XLeaf (full_ps s') (CC.TOther (s_pc ss))))
             | None => XStuck 93 ss0
             end
      else
        match (if Nat.eqb FORGET_N 0 then [] else CXF.big_regs FORGET_N FORGET_KEEP ss) with
        | r :: _ => match apply_fix (FOp (CX.OForget r)) ss with
                    | Some s' => wrap_fix (FOp (CX.OForget r)) (explore m first s')
                    | None => XStuck 89 ss
                    end
        | [] =>
        match (match SGA.special segs IT x_cpy x_set x_len ro_lo ro_hi BFUEL A F ss with
               | Some r => Some r
               | None => fp_run ss      (* [comment removed for export] *)
               end) with
        | Some (it, s') => wrap_item it (explore m false s')
        | None =>
            if ((Z.eqb (s_pc ss) x_cpy || Z.eqb (s_pc ss) x_set) && negb (match SR.reg ss 12 with ELit 0 => true | _ => false end))%bool then XStuck 94 ss else   (* [comment removed for export] *)
            match nm_fix ss with                    (* [comment removed for export] *)
            | Some (f, s1) => wrap_fix f (explore m true s1)
            | None =>
            match STEP (SR.SBlock STOPS) ss with
            | Some ss' =>
                if negb (Z.eqb (s_pc ss') (s_pc ss) && regs_eqb (s_regs ss') (s_regs ss))%bool
                then XStep (SR.SBlock STOPS) (explore m false ss')
                else
                  let fs := tighten_fixes ss in
                  match (match fs with [] => None | _ => run_fixes fs ss end) with
                  | Some ss1 => wrap_fixes fs (explore m true ss1)      (* [comment removed for export] *)
                  | None =>
                  match SGP.branch_probe IT ss with
                  | Some e =>
                      match SGP.case_arms ss e 0 with
                      | Some (af, at_) =>
                          XBranch (match at_ with
                                   | Some s2 => let '(items, s2') := after_branch e s2 in
                                                let '(fx, s2'') := ltu_fix e true s2' in
                                                wrap_refines items (wrap_fixes fx (dead_or (explore m true) s2''))
                                   | None => XDead end)
                                  (match af with
                                   | Some s1 => let '(items, s1') := after_branch e s1 in
                                                let '(fx, s1'') := ltu_fix e false s1' in
                                                wrap_refines items (wrap_fixes fx (dead_or (explore m true) s1''))
                                   | None => XDead end)
                      | None => XStuck 95 ss
                      end
                  | None =>
                      match nm_fix ss with                    (* [comment removed for export] *)
                      | Some (f, s1) => wrap_fix f (explore m true s1)
                      | None =>
                      match tab_fix (explore m true) ss with   (* [comment removed for export] *)
                      | Some t => t
                      | None =>
                      match SGP.loadbyte IT [] ss with          (* [comment removed for export] *)
                      | Some s' => XLoadByte (explore m false s')
                      | None =>
                      match enum_candidate ss with
                      | Some (v, l, h) => enum_go 12 v l h (explore m true) ss
                      | None => XStuck 91 ss
                      end
                      end
                      end
                      end
                  end
                  end
            | None => XStuck 92 ss
            end
            end
        end
        end
  end.

End WithImage.

(* [comment removed for export] *)
Definition ps_reg (ps : SR.post_spec) (r : nat) : expr :=
  match find (fun ie : nat * expr => Nat.eqb (fst ie) r) (SR.ps_regs ps) with Some ie => snd ie | None => EVar r end.
Definition ps_reglist (ps : SR.post_spec) : list expr := EVar 0 :: map (ps_reg ps) (seq 1 31).
Fixpoint expr_bound (e : expr) : nat :=
  match e with
  | ELit _ | EBlob _ _ _ _ => 0%nat
  | EVar n => S n
  | EAlu _ a b | EAluw _ a b | EMd _ a b | EMdw _ a b => Nat.max (expr_bound a) (expr_bound b)
  | EExt _ _ _ a => expr_bound a
  end.
Definition kentry_bound (K : kentry) : nat :=
  match K with
  | KWord a _ v => Nat.max (expr_bound (a_base a)) (expr_bound v)
  | KZero a n | KBlob a n _ | KWr a n | KFill a n _ | KUnk a n => Nat.max (expr_bound (a_base a)) (expr_bound n)
  | KImg _ _ => 0%nat
  | KAlign e _ | KRange e _ _ => expr_bound e
  | KDisj a1 n1 a2 n2 => Nat.max (Nat.max (expr_bound (a_base a1)) (expr_bound n1)) (Nat.max (expr_bound (a_base a2)) (expr_bound n2))
  end.
Definition ps_bound (ps : SR.post_spec) : nat :=
  fold_right Nat.max 0%nat (map (fun ie : nat * expr => expr_bound (snd ie)) (SR.ps_regs ps) ++ map kentry_bound (SR.ps_cells ps)).

(* [comment removed for export] *)
Definition blocks : Type := CH.blocks.
Definition same_base (p : expr) (r : expr * Z * expr) : bool := let '(b, _, _) := r in expr_eqb b p.
Definition ret_tmpl (hd : CH.hdecl) (cs : callsum) (hull_lo hull_hi : Z) (apart : list (expr * Z * expr))   (* [comment removed for export] *)
           (src : CC.cutpoint) (BL : blocks) (nxsrc : nat) (ps : SR.post_spec) : option (CC.cutpoint * blocks) :=
  let regs := ps_reglist ps in
  let nx := Nat.max nxsrc (ps_bound ps) in
  match (match cs_inl cs with
         | Some (len, hv) => Some (SR.ps_pc ps + len, APC.sr_fresh regs hv nx, length hv)
         | None => match nth 1 regs (ELit 1) with ELit ra => Some (ra, APC.sr_fresh regs APC.caller_saved nx, APC.NCS) | _ => None end
         end) with
  | Some (ra, regs1, nfresh) =>
      let regs2 := match cs_a0 cs regs with Some e => sr_upd regs1 10 e | None => regs1 end in
      let a0' := nth 10 regs2 (ELit 0) in
      let p := nth 10 regs (ELit 0) in
      (* [comment removed for export] *)
      let helpers := flat_map (clob_fact_k (SR.ps_cells ps)) (cs_clob cs regs) in
      let kn1 := List.filter (fun X => negb (existsb (APC.kentry_eqb X) helpers))
                   (fold_left (fun k (r : expr * Z * expr) => let '(b, o, n) := r in KUnk (SA b o) n :: APC.kn_havoc k b o n) (cs_clob cs regs) (SR.ps_cells ps)) in
      let kn1 := if Z.ltb 0 (cs_scratch cs) then
                   let '(spb, spo) := split_lit (nth 2 regs (ELit 0)) in
                   KUnk (SA spb (spo - cs_scratch cs)) (ELit (cs_scratch cs)) :: APC.kn_havoc kn1 spb (spo - cs_scratch cs) (ELit (cs_scratch cs))
                 else kn1 in
      let kn2 := if cs_free cs then
                   match find (fun b : expr * expr => expr_eqb (fst b) p) BL with
                   | Some (_, sz) => let kc := APC.kn_cutout kn1 p 0 sz in
                                     (* [comment removed for export] *)
                                     kc ++ List.filter (fun X => negb (existsb (APC.kentry_eqb X) kc)) kn1
                   | None => kn1
                   end
                 else kn1 in
      let knew := match cs_newblk cs regs with
                  | Some n => [KRange a0' 4096 140737488355328; KAlign a0' 16; KUnk (SA a0' 0) n; KWr (SA a0' 0) n;
                               KDisj (SA a0' 0) n (SA (ELit 0) hull_lo) (ELit (hull_hi - hull_lo))]
                              ++ map (fun r : expr * Z * expr => let '(b, o, m) := r in KDisj (SA a0' 0) n (SA b o) m) apart
                              ++ map (fun b : expr * expr => KDisj (SA a0' 0) n (SA (fst b) 0) (snd b)) BL
                  | None => []
                  end in
      let F' := (if cs_free cs then List.filter (fun r => negb (same_base p r)) (CC.cp_F src) else CC.cp_F src)
                ++ match cs_newblk cs regs with Some n => [(a0', 0, n)] | None => [] end
                (* [comment removed for export] *)
                ++ flat_map (fun X => match X with KWr (SA b o) n => [(b, o, n)] | _ => [] end) (cs_res cs regs a0') in
      let BLk := if cs_free cs then CH.remove_first p BL else BL in
      let BL' := match cs_newblk cs regs with Some n => [(a0', n)] | None => [] end ++ BLk in
      (* [comment removed for export] *)
      let cand := if cs_alloc cs then kn2 ++ List.filter (fun X => negb (existsb (APC.kentry_eqb X) kn2)) (SR.ps_cells ps) else kn2 in
      let kn3 := if cs_alloc cs then List.filter (CH.survive_chk hd (SR.ps_cells ps) (snd (split_lit (nth 2 regs (ELit 0)))) BLk) cand else kn2 in
      let kblob := if cs_blob cs then
                     let '(db, dk) := split_lit p in let '(sb, sk) := split_lit (nth 11 regs (ELit 0)) in let n := nth 12 regs (ELit 0) in
                     flat_map (fun X => match X with
                                        | KBlob (SA b k) m id => if (expr_eqb b sb && Z.eqb k sk && expr_eqb m n)%bool then [KBlob (SA db dk) n id] else []
                                        | _ => []
                                        end) (SR.ps_cells ps)
                   else [] in
      (* [comment removed for export] *)
      let hback := List.filter (fun X => existsb (APC.kentry_eqb X) (SR.ps_cells ps)) helpers in
      Some (CC.CP ra regs2 (cs_res cs regs a0' ++ knew ++ kblob ++ kn3 ++ hback) (nx + nfresh) F' [] (APC.esub (CC.cp_meas src) (ELit 1)), BL')
  | None => None
  end.
(* [comment removed for export] *)
Definition HL_STACK : Z := 8224.   (* [comment removed for export] *)
Definition cs_malloc (pc : Z) : callsum := CSUM pc (fun _ => []) (fun _ => None) (fun _ _ => []) (fun regs => Some (nth 10 regs (ELit 0))) false None HL_STACK true false.
Definition cs_free_ (pc : Z) : callsum := CSUM pc (fun _ => []) (fun _ => None) (fun _ _ => []) (fun _ => None) true None HL_STACK true false.
(* [comment removed for export] *)
Definition cs_copy (pc : Z) : callsum :=
  CSUM pc (fun regs => [(fst (split_lit (nth 10 regs (ELit 0))), snd (split_lit (nth 10 regs (ELit 0))), nth 12 regs (ELit 0))])
       (fun regs => Some (nth 10 regs (ELit 0))) (fun _ _ => []) (fun _ => None) false None 0 false true.
(* [comment removed for export] *)
Definition cs_inline (pc len : Z) (hv : list nat) : callsum :=
  CSUM pc (fun _ => []) (fun _ => None) (fun _ _ => []) (fun _ => None) false (Some (len, hv)) 0 false false.
Definition dummy_cp : CC.cutpoint := CC.CP 0 [] [] 0 [] [] (ELit 0).
End CA.
