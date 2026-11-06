(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec AxSymExec3 AxSymExec3B AsanPlanCore LibSym SegRun SegPlan Pm4PlanKit.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PmLibDefs PmEncSpecs PmLibSpecsW PmRef.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutHeap2 CutAutoX.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import Pm4CutKit CutCertA CutHeapA CutAutoXA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Import PsoInstXA ParseSomeChkXA.
Import ListNotations. Import AX2.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Printing Width 250. Set Printing Depth 100000.

Module OBSXA.
Import PML. Import PMR.
(* [comment removed for export] *)
Definition PC_VEC_PUSH := PSOC.VPUSH. Definition PC_PUSH_BACK := PSOC.PUSHB. Definition PC_POP := PSOC.POPST. Definition PC_PARENT := PSOC.PARENT. Definition PC_SETEC := PSOC.SETEC.
Definition PC_SKIP := PSOC.SKIPSP. Definition PC_BOBJ := PSOC.BOBJ. Definition PC_BARR := PSOC.BARR. Definition PC_PSTRING := PSOC.PSTRING. Definition PC_PNUMBER := PSOC.PNUMBER.
Definition PC_PNULL := PSOC.PNULL. Definition PC_PTRUE := PSOC.PTRUE. Definition PC_PFALSE := PSOC.PFALSE. Definition PC_EOBJ := PSOC.EOBJ. Definition PC_EARR := PSOC.EARR.
Definition PC_BMEM := PSOC.BMEMBER. Definition PC_EINT := PSOC.ENDINT. Definition PC_EFRAC := PSOC.ENDFRAC. Definition PC_VNULL := PSOC.VNULL. Definition PC_VBOOL := PSOC.VBOOL.
Definition PC_RET := PSOC.RETXPC. Definition PC_DEAD := PSOC.DEAD. Definition PC_TAILSETEC := PSOC.SETECJ. Definition PC_ERRH := PSOC.ERRH.
Definition CSLPCS : list Z := Eval vm_compute in List.map (fun i => CC.cp_pc (PSO.cutn i)) (seq 11 28).
Definition inb (z : Z) (l : list Z) : bool := existsb (Z.eqb z) l.
Definition PC_HEAD := PSOC.HEAD. Definition PC_LATCH := PSOC.LATCH. Definition PC_CONSUME := PSOC.CONSUME. Definition CPS := PSO.G.CPS. Definition TAGS := PSO.G.TAGS.

(* [comment removed for export] *)
Definition POBJ : nat := 10%nat.
(* [comment removed for export] *)
Fixpoint pcell (off : Z) (w : nat) (cells : list kentry) : option expr :=
  match cells with
  | KWord (SA (EVar 10) o) w' e :: r => if (o =? off) && Nat.eqb w w' then Some e else pcell off w r
  | _ :: r => pcell off w r | [] => None end.
(* [comment removed for export] *)
Fixpoint pbyte (off : Z) (cells : list kentry) : option Z :=
  match cells with
  | KWord (SA (EVar 10) o) w' (ELit v) :: r =>
      if (o <=? off) && (off <? o + Z.of_nat w') then Some (Z.land (Z.shiftr (v mod 2 ^ 64) (8 * (off - o))) 255) else pbyte off r
  | KWord (SA (EVar 10) o) w' _ :: r => if (o <=? off) && (off <? o + Z.of_nat w') then None else pbyte off r
  | _ :: r => pbyte off r | [] => None end.
(* [comment removed for export] *)
Fixpoint rng (e : expr) (cells : list kentry) (lo hi : Z) : Z * Z :=
  match cells with
  | KRange e' l h :: r => if expr_eqb e e' then rng e r (Z.max lo l) (Z.min hi h) else rng e r lo hi
  | _ :: r => rng e r lo hi | [] => (lo, hi) end.
(* [comment removed for export] *)
Definition lit_of (oe : option expr) : option Z := match oe with Some (ELit c) => Some c | _ => None end.
Fixpoint reg (i : nat) (rs : list (nat * expr)) : option expr :=
  match rs with (j, e) :: r => if Nat.eqb i j then Some e else reg i r | [] => None end.
(* [comment removed for export] *)
Fixpoint named_bytes (nx : nat) (cells : list kentry) : list (saddr * nat) :=
  match cells with
  | KWord (SA base o) 1 (EVar v) :: r =>
      (if match base with EVar 10 => false | _ => Nat.leb nx v end then [(SA base o, v)] else []) ++ named_bytes nx r
  | _ :: r => named_bytes nx r | [] => [] end.
Fixpoint min_var (l : list (saddr * nat)) (best : option (saddr * nat)) : option (saddr * nat) :=
  match l with
  | [] => best
  | (a, v) :: r => min_var r (match best with Some (_, v0) => if Nat.ltb v v0 then Some (a, v) else best | None => Some (a, v) end)
  end.

(* [comment removed for export] *)
Definition leaf_state (tmpl leafc : list kentry) : option (Z * Z) :=      (* [comment removed for export] *)
  match pcell 208 1 tmpl with
  | Some e => match PSO.st_lit (leafc ++ tmpl) e with
              | Some c => Some (c, c)
              | None => match e with EVar s => Some (rng (EVar s) leafc (fst (rng (EVar s) tmpl 0 255)) (snd (rng (EVar s) tmpl 0 255))) | _ => None end
              end
  | None => None
  end.

(* [comment removed for export] *)
Record obs := OB { ob_pc : Z; ob_goto : option nat; ob_a1 : option expr; ob_st : option Z; ob_more : option Z; ob_done : option Z; ob_bytev : option nat }.
Definition observe (nx : nat) (ps : SR.post_spec) (t : CC.tag) : obs :=
  OB (SR.ps_pc ps) (match t with CC.TGoto j _ => Some j | _ => None end) (reg 11 (SR.ps_regs ps))
     (pbyte 208 (SR.ps_cells ps)) (pbyte 211 (SR.ps_cells ps)) (pbyte 212 (SR.ps_cells ps))
     (match min_var (named_bytes nx (SR.ps_cells ps)) None with Some (_, v) => Some v | None => None end).
Definition st_is (o : obs) (s : Z) : bool := match ob_st o with Some s' => s =? s' | None => false end.
Definition a1_is (o : obs) (c : Z) : bool := match ob_a1 o with Some (ELit c') => c =? c' | _ => false end.
(* [comment removed for export] *)
Definition agree (a : act) (b : Z) (o : obs) : bool :=
  let pc := ob_pc o in
  match a with
  | AErr c _ => (pc =? PC_ERRH) || (((pc =? PC_SETEC) || (pc =? PC_TAILSETEC)) && a1_is o c)      (* [comment removed for export] *)
  | AAccept => st_is o ST_DONE
  | ASkip => pc =? PC_SKIP
  | ASlash => (pc =? PC_VEC_PUSH) || st_is o ST_SLASH || (pc =? PC_ERRH)      (* [comment removed for export] *)
  | ABegin false => pc =? PC_BOBJ
  | ABegin true => pc =? PC_BARR
  | AEnd false => pc =? PC_EOBJ
  | AEnd true => pc =? PC_EARR
  | AString false => (pc =? PC_PSTRING) && st_is o ST_STRING
  | AString true => (pc =? PC_VEC_PUSH) || ((pc =? PC_PSTRING) && st_is o ST_STRING)
  | ANumber => (pc =? PC_PUSH_BACK) && match ob_a1 o, ob_bytev o with Some (ELit c), _ => c =? b | Some (EVar v), Some bv => Nat.eqb v bv | _, _ => false end
  | ALit w => pc =? (if w =? 0 then PC_PNULL else if w =? 1 then PC_PTRUE else PC_PFALSE)
  | AComma => pc =? PC_BMEM
  | AGoto st' _ => st_is o st' || (pc =? PC_ERRH) || match ob_goto o, ob_st o with Some _, None => true | _, _ => false end   (* [comment removed for export] *)
  | APop _ => pc =? PC_POP
  | APushCr => (pc =? PC_VEC_PUSH) || st_is o ST_CR
  | ALitDone => (pc =? PC_VNULL) || (pc =? PC_VBOOL)
  | AParseString => pc =? PC_PSTRING
  | AParseNumber => pc =? PC_PNUMBER
  | AStuck => pc =? PC_DEAD
  end.
(* [comment removed for export] *)
Definition act_eqb (a1 a2 : act) : bool :=
  match a1, a2 with
  | AErr c1 k1, AErr c2 k2 => (c1 =? c2) && Bool.eqb k1 k2 | AAccept, AAccept => true | ASkip, ASkip => true | ASlash, ASlash => true
  | ABegin x, ABegin y => Bool.eqb x y | AEnd x, AEnd y => Bool.eqb x y | AString x, AString y => Bool.eqb x y | ANumber, ANumber => true
  | ALit x, ALit y => x =? y | AComma, AComma => true | AGoto s1 k1, AGoto s2 k2 => (s1 =? s2) && Bool.eqb k1 k2 | APop k1, APop k2 => Bool.eqb k1 k2
  | APushCr, APushCr => true | ALitDone, ALitDone => true | AParseString, AParseString => true | AParseNumber, AParseNumber => true | AStuck, AStuck => true
  | _, _ => false
  end.
Definition PARENTS : list Z := [ST_ROOT; ST_OBJECT; ST_ARRAY; ST_MEMBER_NAME; ST_START].
Definition pindep (st b : Z) : bool := forallb (fun p => act_eqb (dispatch st p b) (dispatch st ST_ROOT b)) PARENTS.
Fixpoint forall_b (lo : Z) (n : nat) (f : Z -> bool) : bool :=
  match n with O => true | S n' => f lo && forall_b (lo + 1) n' f end.
Definition all_bytes (lo hi : Z) (f : Z -> bool) : bool := forall_b lo (Z.to_nat (hi - lo + 1)) f.
(* [comment removed for export] *)
Definition E_nil : env := Env (fun _ => Z_to_bv 64 0) (fun _ => []).
Definition only_var (bv : nat) (e : expr) : bool := forallb (Nat.eqb bv) (APC.expr_vars e []) && negb (match APC.expr_vars e [] with [] => true | _ => false end).
Definition fact_okb (bv : nat) (b : Z) (k : kentry) : bool :=
  match k with
  | KRange e lo hi => if only_var bv e then let v := bv_unsigned (edenot E_nil (APC.esubst bv (ELit b) e)) in (lo <=? v) && (v <=? hi) else true
  | _ => true
  end.
Definition byte_adm (bv : nat) (cells : list kentry) (b : Z) : bool := forallb (fact_okb bv b) cells.

(* [comment removed for export] *)
Definition leaf_sim (tmpl : list kentry) (nx : nat) (ps : SR.post_spec) (t : CC.tag) : option (bool + Z) :=
  match leaf_state tmpl (SR.ps_cells ps) with
  | None => None
  | Some (slo, shi) =>
    if negb (slo =? shi) then None else
    let o := observe nx ps t in
    match ob_bytev o with
    | None => Some (inr 0)
    | Some bv =>
        if inb (ob_pc o + 4) CSLPCS then Some (inr 2) else      (* [comment removed for export] *)
        let adm := byte_adm bv (SR.ps_cells ps) in
        if negb (all_bytes 0 255 (fun b => negb (adm b) || pindep slo b)) then
          (if ob_pc o =? PC_PARENT then Some (inl true) else Some (inr 1))
        else Some (inl (all_bytes 0 255 (fun b => negb (adm b) || agree (dispatch slo ST_ROOT b) b o)))
    end
  end.
Fixpoint idx {A} (k : nat) (l : list A) : list (nat * A) := match l with [] => [] | x :: r => (k, x) :: idx (S k) r end.
Definition run_cut (i : nat) : list (nat * option (bool + Z)) :=
  match nth_error CPS i, nth_error TAGS i with
  | Some c, Some tg => List.map (fun p => (fst p, leaf_sim (CC.cp_know c) (CC.cp_nx c) (fst (snd p)) (snd (snd p)))) (idx 0 (List.combine (CC.cp_PSS c) tg))
  | _, _ => []
  end.
Definition count (f : option (bool + Z) -> bool) (l : list (nat * option (bool + Z))) : Z := Z.of_nat (length (List.filter (fun p => f (snd p)) l)).
(* [comment removed for export] *)
Definition summary (i : nat) := let l := run_cut i in
  (Z.of_nat i, Z.of_nat (length l),
   count (fun o => match o with Some (inl true) => true | _ => false end) l,
   count (fun o => match o with Some (inl false) => true | _ => false end) l,
   count (fun o => match o with None => true | _ => false end) l,
   count (fun o => match o with Some (inr 0) => true | _ => false end) l,
   count (fun o => match o with Some (inr 1) => true | Some (inr 2) => true | _ => false end) l,
   List.map fst (List.filter (fun p => match snd p with Some (inl false) => true | _ => false end) l)).
Definition nonempty (s : Z * Z * Z * Z * Z * Z * Z * list nat) := let '(_, n, _, _, _, _, _, _) := s in negb (n =? 0).
Definition census := List.filter nonempty (List.map summary (seq 0 (length CPS))).
Definition totals := List.fold_right (fun s acc => let '(_, n, a, d, u, nb, pd, _) := s in let '(N, A, D, U, NB, PD) := acc in (N + n, A + a, D + d, U + u, NB + nb, PD + pd))
                                     (0, 0, 0, 0, 0, 0) census.
End OBSXA.
Eval vm_compute in OBSXA.totals.
Eval vm_compute in OBSXA.census.
