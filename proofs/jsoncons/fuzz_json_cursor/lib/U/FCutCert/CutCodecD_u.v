(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith List Bool.
From Corelib Require Import PrimInt63 PrimString.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec AxSymExec3 AxSymExec3B AsanPlanCore LibSym SegRun SegPlan SegPlanAuto.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.FCutCert Require Import CutOpsF CutCert CutOps CutHeap CutOpsD CutAutoD.
Import ListNotations. Import AX2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module CCDD.

Unset Elimination Schemes.
Inductive sx : Type := SxA (z : Z) | SxL (l : list sx) | SxR (k : positive).
Set Elimination Schemes.

Record pst : Type := PST { p_pos : int; p_stack : list (list sx); p_num : option (bool * Z); p_ref : bool }.

Definition digit_of (c : int) : option Z :=
  if PrimInt63.ltb c 48%int63 then None
  else if PrimInt63.ltb 57%int63 c then None
  else Some (if PrimInt63.eqb c 48%int63 then 0 else if PrimInt63.eqb c 49%int63 then 1 else if PrimInt63.eqb c 50%int63 then 2
            else if PrimInt63.eqb c 51%int63 then 3 else if PrimInt63.eqb c 52%int63 then 4 else if PrimInt63.eqb c 53%int63 then 5
            else if PrimInt63.eqb c 54%int63 then 6 else if PrimInt63.eqb c 55%int63 then 7 else if PrimInt63.eqb c 56%int63 then 8 else 9).

Definition push_item (x : sx) (stk : list (list sx)) : list (list sx) :=
  match stk with l :: r => (x :: l) :: r | [] => [[x]] end.
Definition flush (num : option (bool * Z)) (isref : bool) (stk : list (list sx)) : list (list sx) :=
  match num with
  | Some (neg, v) => push_item (if isref then SxR (Z.to_pos v) else SxA (if neg then Z.opp v else v)) stk
  | None => stk
  end.

Definition step (s : string) (st : pst) : pst :=
  let c := PrimString.get s (p_pos st) in
  let pos' := PrimInt63.add (p_pos st) 1%int63 in
  match digit_of c with
  | Some d => PST pos' (p_stack st) (Some match p_num st with Some (neg, v) => (neg, v * 10 + d) | None => (false, d) end) (p_ref st)
  | None =>
      if PrimInt63.eqb c 45%int63   then PST pos' (p_stack st) (Some (true, 0)) false
      else if PrimInt63.eqb c 35%int63   then PST pos' (flush (p_num st) (p_ref st) (p_stack st)) (Some (false, 0)) true
      else if PrimInt63.eqb c 40%int63   then PST pos' ([] :: flush (p_num st) (p_ref st) (p_stack st)) None false
      else if PrimInt63.eqb c 41%int63   then
        match flush (p_num st) (p_ref st) (p_stack st) with
        | l :: r => PST pos' (push_item (SxL (rev l)) r) None false
        | [] => PST pos' [] None false
        end
      else   PST pos' (flush (p_num st) (p_ref st) (p_stack st)) None false
  end.

Fixpoint iterp {A : Type} (n : positive) (f : A -> A) (x : A) : A :=
  match n with
  | xH => f x
  | xO p => iterp p f (iterp p f x)
  | xI p => f (iterp p f (iterp p f x))
  end.

Definition parse (len : positive) (s : string) : sx :=
  let st := iterp len (step s) (PST 0%int63 [[]] None false) in
  match flush (p_num st) (p_ref st) (p_stack st) with
  | [x] :: _ => x
  | (x :: _) :: _ => x
  | _ => SxL []
  end.

Definition dchar (d : Z) : int :=
  match d with 0 => 48 | 1 => 49 | 2 => 50 | 3 => 51 | 4 => 52 | 5 => 53 | 6 => 54 | 7 => 55 | 8 => 56 | _ => 57 end%int63.
Fixpoint pos_digits (fuel : nat) (p : Z) (acc : list int) : list int :=
  match fuel with
  | O => acc
  | S f => if Z.ltb p 10 then dchar p :: acc else pos_digits f (Z.div p 10) (dchar (Z.modulo p 10) :: acc)
  end.
Definition str_of_chars (l : list int) : string :=
  fold_right (fun c acc => PrimString.cat (PrimString.make 1%int63 c) acc) ""%pstring l.
Definition ztok (z : Z) : string :=
  if Z.ltb z 0 then str_of_chars (45%int63 :: pos_digits 30 (Z.opp z) []) else str_of_chars (pos_digits 30 z []).
Definition SP : string := " "%pstring.
Definition LP : string := "("%pstring.
Definition RP : string := ")"%pstring.

Definition is_atom (x : sx) : bool := match x with SxL _ => false | _ => true end.
Fixpoint toks (x : sx) (acc : list string) : list string :=
  match x with
  | SxA z => ztok z :: acc
  | SxR k => str_of_chars (35%int63 :: pos_digits 30 (Zpos k) []) :: acc
  | SxL l => LP :: (fix go (prev_atom : bool) (l : list sx) (acc : list string) : list string :=
                     match l with
                     | [] => acc
                     | y :: r => let here := toks y (go (is_atom y) r acc) in
                                 if (prev_atom && match y with SxA _ => true | _ => false end)%bool then SP :: here else here
                     end) false l (RP :: acc)
  end.
Fixpoint pair_cat (l : list string) : list string :=
  match l with
  | a :: b :: r => PrimString.cat a b :: pair_cat r
  | _ => l
  end.
Fixpoint cat_rounds (fuel : nat) (l : list string) : string :=
  match fuel with
  | O => match l with a :: _ => a | [] => ""%pstring end
  | S f => match l with [] => ""%pstring | [a] => a | _ => cat_rounds f (pair_cat l) end
  end.
Definition print (x : sx) : string := cat_rounds 64 (toks x []).

Inductive pt : Type := PTe | PTn (l : pt) (v : option sx) (r : pt).
Fixpoint pt_get (t : pt) (k : positive) : option sx :=
  match t with
  | PTe => None
  | PTn l v r => match k with xH => v | xO k' => pt_get l k' | xI k' => pt_get r k' end
  end.
Fixpoint pt_set (t : pt) (k : positive) (x : sx) : pt :=
  match t, k with
  | PTe, xH => PTn PTe (Some x) PTe
  | PTe, xO k' => PTn (pt_set PTe k' x) None PTe
  | PTe, xI k' => PTn PTe None (pt_set PTe k' x)
  | PTn l v r, xH => PTn l (Some x) r
  | PTn l v r, xO k' => PTn (pt_set l k' x) v r
  | PTn l v r, xI k' => PTn l v (pt_set r k' x)
  end.
Fixpoint resolve (t : pt) (x : sx) : sx :=
  match x with
  | SxA _ => x
  | SxR k => match pt_get t k with Some y => y | None => SxL [] end
  | SxL l => SxL ((fix go (l : list sx) : list sx := match l with [] => [] | y :: r => resolve t y :: go r end) l)
  end.
Fixpoint build (t : pt) (k : positive) (es : list sx) : pt :=
  match es with
  | [] => t
  | e :: r => build (pt_set t k (resolve t e)) (Pos.succ k) r
  end.
Definition expand (x : sx) : sx :=
  match x with
  | SxL [SxA (-1); SxL es; body] => resolve (build PTe 1%positive es) body
  | _ => x
  end.

Definition e_nat (n : nat) : sx := SxA (Z.of_nat n).
Definition d_nat (x : sx) : nat := match x with SxA z => Z.to_nat z | _ => O end.
Definition e_Z (z : Z) : sx := SxA z.
Definition d_Z (x : sx) : Z := match x with SxA z => z | _ => 0 end.
Definition e_bool (b : bool) : sx := SxA (if b then 1 else 0).
Definition d_bool (x : sx) : bool := match x with SxA 1 => true | _ => false end.
Definition e_list {A} (f : A -> sx) (l : list A) : sx := SxL (map f l).
Definition d_list {A} (f : sx -> A) (x : sx) : list A := match x with SxL l => map f l | _ => [] end.
Definition e_opt {A} (f : A -> sx) (o : option A) : sx := match o with Some a => SxL [f a] | None => SxL [] end.
Definition d_opt {A} (f : sx -> A) (x : sx) : option A := match x with SxL [a] => Some (f a) | _ => None end.
Definition e_p2 {A B} (f : A -> sx) (g : B -> sx) (p : A * B) : sx := SxL [f (fst p); g (snd p)].
Definition d_p2 {A B} (f : sx -> A) (g : sx -> B) (dA : A) (dB : B) (x : sx) : A * B := match x with SxL [a; b] => (f a, g b) | _ => (dA, dB) end.

Definition e_aluop (o : aluop) : sx := SxA match o with ALU_ADD => 0 | ALU_SUB => 1 | ALU_SLL => 2 | ALU_SLT => 3 | ALU_SLTU => 4 | ALU_XOR => 5 | ALU_SRL => 6 | ALU_SRA => 7 | ALU_OR => 8 | ALU_AND => 9 end.
Definition d_aluop (x : sx) : aluop := match x with SxA 0 => ALU_ADD | SxA 1 => ALU_SUB | SxA 2 => ALU_SLL | SxA 3 => ALU_SLT | SxA 4 => ALU_SLTU | SxA 5 => ALU_XOR | SxA 6 => ALU_SRL | SxA 7 => ALU_SRA | SxA 8 => ALU_OR | _ => ALU_AND end.
Definition e_mulop (o : mulop) : sx := SxA match o with M_MUL => 0 | M_MULH => 1 | M_MULHSU => 2 | M_MULHU => 3 | M_DIV => 4 | M_DIVU => 5 | M_REM => 6 | M_REMU => 7 end.
Definition d_mulop (x : sx) : mulop := match x with SxA 0 => M_MUL | SxA 1 => M_MULH | SxA 2 => M_MULHSU | SxA 3 => M_MULHU | SxA 4 => M_DIV | SxA 5 => M_DIVU | SxA 6 => M_REM | _ => M_REMU end.

Fixpoint e_expr (e : expr) : sx :=
  match e with
  | ELit z => SxL [SxA 0; SxA z]
  | EVar n => SxL [SxA 1; e_nat n]
  | EAlu op a b => SxL [SxA 2; e_aluop op; e_expr a; e_expr b]
  | EAluw op a b => SxL [SxA 3; e_aluop op; e_expr a; e_expr b]
  | EMd op a b => SxL [SxA 4; e_mulop op; e_expr a; e_expr b]
  | EMdw op a b => SxL [SxA 5; e_mulop op; e_expr a; e_expr b]
  | EExt sg lo n e => SxL [SxA 6; e_bool sg; e_nat lo; e_nat n; e_expr e]
  | EBlob sg k i n => SxL [SxA 7; e_bool sg; e_nat k; SxA i; e_nat n]
  end.
Fixpoint d_expr (x : sx) : expr :=
  match x with
  | SxL [SxA 0; SxA z] => ELit z
  | SxL [SxA 1; n] => EVar (d_nat n)
  | SxL [SxA 2; op; a; b] => EAlu (d_aluop op) (d_expr a) (d_expr b)
  | SxL [SxA 3; op; a; b] => EAluw (d_aluop op) (d_expr a) (d_expr b)
  | SxL [SxA 4; op; a; b] => EMd (d_mulop op) (d_expr a) (d_expr b)
  | SxL [SxA 5; op; a; b] => EMdw (d_mulop op) (d_expr a) (d_expr b)
  | SxL [SxA 6; sg; lo; n; e] => EExt (d_bool sg) (d_nat lo) (d_nat n) (d_expr e)
  | SxL [SxA 7; sg; k; SxA i; n] => EBlob (d_bool sg) (d_nat k) i (d_nat n)
  | _ => ELit 0
  end.
Definition e_saddr (a : saddr) : sx := SxL [e_expr (a_base a); SxA (a_off a)].
Definition d_saddr (x : sx) : saddr := match x with SxL [b; SxA o] => SA (d_expr b) o | _ => SA (ELit 0) 0 end.
Definition e_kentry (K : kentry) : sx :=
  match K with
  | KWord a w v => SxL [SxA 0; e_saddr a; e_nat w; e_expr v]
  | KZero a n => SxL [SxA 1; e_saddr a; e_expr n]
  | KBlob a n k => SxL [SxA 2; e_saddr a; e_expr n; e_nat k]
  | KImg lo hi => SxL [SxA 3; SxA lo; SxA hi]
  | KAlign e m => SxL [SxA 4; e_expr e; SxA m]
  | KRange e lo hi => SxL [SxA 5; e_expr e; SxA lo; SxA hi]
  | KWr a n => SxL [SxA 6; e_saddr a; e_expr n]
  | KDisj a1 n1 a2 n2 => SxL [SxA 7; e_saddr a1; e_expr n1; e_saddr a2; e_expr n2]
  | KFill a n c => SxL [SxA 8; e_saddr a; e_expr n; SxA c]
  | KUnk a n => SxL [SxA 9; e_saddr a; e_expr n]
  end.
Definition d_kentry (x : sx) : kentry :=
  match x with
  | SxL [SxA 0; a; w; v] => KWord (d_saddr a) (d_nat w) (d_expr v)
  | SxL [SxA 1; a; n] => KZero (d_saddr a) (d_expr n)
  | SxL [SxA 2; a; n; k] => KBlob (d_saddr a) (d_expr n) (d_nat k)
  | SxL [SxA 3; SxA lo; SxA hi] => KImg lo hi
  | SxL [SxA 4; e; SxA m] => KAlign (d_expr e) m
  | SxL [SxA 5; e; SxA lo; SxA hi] => KRange (d_expr e) lo hi
  | SxL [SxA 6; a; n] => KWr (d_saddr a) (d_expr n)
  | SxL [SxA 7; a1; n1; a2; n2] => KDisj (d_saddr a1) (d_expr n1) (d_saddr a2) (d_expr n2)
  | SxL [SxA 8; a; n; SxA c] => KFill (d_saddr a) (d_expr n) c
  | SxL [SxA 9; a; n] => KUnk (d_saddr a) (d_expr n)
  | _ => KImg 0 0
  end.
Definition e_sentry (e : sentry) : sx := SxL [e_saddr (e_addr e); e_nat (e_width e); e_expr (e_val e)].
Definition d_sentry (x : sx) : sentry := match x with SxL [a; w; v] => SE (d_saddr a) (d_nat w) (d_expr v) | _ => SE (SA (ELit 0) 0) O (ELit 0) end.
Definition e_state (ss : sym_state) : sx :=
  SxL [SxA (s_pc ss); e_list e_expr (s_regs ss); e_list e_sentry (s_log ss); e_list e_kentry (s_know ss); e_nat (s_next ss); e_opt e_saddr (s_resv ss)].
Definition d_state (x : sx) : sym_state :=
  match x with
  | SxL [SxA pc; regs; lg; kn; nx; rv] => SSR pc (d_list d_expr regs) (d_list d_sentry lg) (d_list d_kentry kn) (d_nat nx) (d_opt d_saddr rv)
  | _ => SSR 0 [] [] [] O None
  end.
Definition e_sstep (st : SR.sstep) : sx :=
  match st with
  | SR.SBlock stops => SxL [SxA 0; e_list e_Z stops]
  | SR.SCopy => SxL [SxA 1]
  | SR.SFill => SxL [SxA 2]
  | SR.SFsdSeq n => SxL [SxA 3; e_nat n]
  | SR.SFldSeq n => SxL [SxA 4; e_nat n]
  | SR.SStrlen k => SxL [SxA 5; SxA k]
  | SR.SExpect pc => SxL [SxA 6; SxA pc]
  | SR.SDiamond j => SxL [SxA 7; SxA j]
  | SR.SEvalReg r => SxL [SxA 8; e_nat r]
  end.
Definition d_sstep (x : sx) : SR.sstep :=
  match x with
  | SxL [SxA 0; stops] => SR.SBlock (d_list d_Z stops)
  | SxL [SxA 1] => SR.SCopy
  | SxL [SxA 2] => SR.SFill
  | SxL [SxA 3; n] => SR.SFsdSeq (d_nat n)
  | SxL [SxA 4; n] => SR.SFldSeq (d_nat n)
  | SxL [SxA 5; SxA k] => SR.SStrlen k
  | SxL [SxA 6; SxA pc] => SR.SExpect pc
  | SxL [SxA 7; SxA j] => SR.SDiamond j
  | SxL [SxA 8; r] => SR.SEvalReg (d_nat r)
  | _ => SR.SBlock []
  end.
Fixpoint e_plan (p : SGP.splan) : sx :=
  match p with
  | SGP.PStep st k => SxL [SxA 0; e_sstep st; e_plan k]
  | SGP.PEnd i => SxL [SxA 1; e_nat i]
  | SGP.PCase e mid klo khi => SxL [SxA 2; e_expr e; SxA mid; e_plan klo; e_plan khi]
  | SGP.PBranch kt kf => SxL [SxA 3; e_plan kt; e_plan kf]
  | SGP.PFact K k => SxL [SxA 4; e_kentry K; e_plan k]
  | SGP.PAbstract b o n k => SxL [SxA 5; e_expr b; SxA o; SxA n; e_plan k]
  | SGP.PCoalesce b o n k => SxL [SxA 6; e_expr b; SxA o; e_expr n; e_plan k]
  | SGP.PFillX k => SxL [SxA 7; e_plan k]
  | SGP.PCopyX k => SxL [SxA 8; e_plan k]
  | SGP.PEvalReg r J k => SxL [SxA 9; e_nat r; e_nat J; e_plan k]
  | SGP.PFactRange e J lo hi k => SxL [SxA 10; e_expr e; e_nat J; SxA lo; SxA hi; e_plan k]
  | SGP.PRefine v lo hi k => SxL [SxA 11; e_nat v; SxA lo; SxA hi; e_plan k]
  | SGP.PRespell r e k => SxL [SxA 12; e_nat r; e_expr e; e_plan k]
  | SGP.PPin v c k => SxL [SxA 13; e_nat v; SxA c; e_plan k]
  | SGP.PLoadByte k => SxL [SxA 14; e_plan k]
  | SGP.PLoadByteNe v klo khi => SxL [SxA 15; SxA v; e_plan klo; e_plan khi]
  | SGP.PX id k => SxL [SxA 16; e_nat id; e_plan k]
  | SGP.PX2 id ka kb => SxL [SxA 17; e_nat id; e_plan ka; e_plan kb]
  | SGP.PLoop J N inv body k => SxL [SxA 18; e_nat J; e_expr N; e_state inv; e_plan body; e_plan k]
  | SGP.PNext => SxL [SxA 19]
  | SGP.PJoin j js lo karms k => SxL [SxA 20; e_nat j; e_state js; e_nat lo; e_plan karms; e_plan k]
  | SGP.PMerge j => SxL [SxA 21; e_nat j]
  end.
Fixpoint d_plan (x : sx) : SGP.splan :=
  match x with
  | SxL [SxA 0; st; k] => SGP.PStep (d_sstep st) (d_plan k)
  | SxL [SxA 1; i] => SGP.PEnd (d_nat i)
  | SxL [SxA 2; e; SxA mid; klo; khi] => SGP.PCase (d_expr e) mid (d_plan klo) (d_plan khi)
  | SxL [SxA 3; kt; kf] => SGP.PBranch (d_plan kt) (d_plan kf)
  | SxL [SxA 4; K; k] => SGP.PFact (d_kentry K) (d_plan k)
  | SxL [SxA 5; b; SxA o; SxA n; k] => SGP.PAbstract (d_expr b) o n (d_plan k)
  | SxL [SxA 6; b; SxA o; n; k] => SGP.PCoalesce (d_expr b) o (d_expr n) (d_plan k)
  | SxL [SxA 7; k] => SGP.PFillX (d_plan k)
  | SxL [SxA 8; k] => SGP.PCopyX (d_plan k)
  | SxL [SxA 9; r; J; k] => SGP.PEvalReg (d_nat r) (d_nat J) (d_plan k)
  | SxL [SxA 10; e; J; SxA lo; SxA hi; k] => SGP.PFactRange (d_expr e) (d_nat J) lo hi (d_plan k)
  | SxL [SxA 11; v; SxA lo; SxA hi; k] => SGP.PRefine (d_nat v) lo hi (d_plan k)
  | SxL [SxA 12; r; e; k] => SGP.PRespell (d_nat r) (d_expr e) (d_plan k)
  | SxL [SxA 13; v; SxA c; k] => SGP.PPin (d_nat v) c (d_plan k)
  | SxL [SxA 14; k] => SGP.PLoadByte (d_plan k)
  | SxL [SxA 15; SxA v; klo; khi] => SGP.PLoadByteNe v (d_plan klo) (d_plan khi)
  | SxL [SxA 16; id; k] => SGP.PX (d_nat id) (d_plan k)
  | SxL [SxA 17; id; ka; kb] => SGP.PX2 (d_nat id) (d_plan ka) (d_plan kb)
  | SxL [SxA 18; J; N; inv; body; k] => SGP.PLoop (d_nat J) (d_expr N) (d_state inv) (d_plan body) (d_plan k)
  | SxL [SxA 19] => SGP.PNext
  | SxL [SxA 20; j; js; lo; karms; k] => SGP.PJoin (d_nat j) (d_state js) (d_nat lo) (d_plan karms) (d_plan k)
  | SxL [SxA 21; j] => SGP.PMerge (d_nat j)
  | _ => SGP.PEnd O
  end.
Definition e_region (r : SR.region) : sx := let '(b, lo, len) := r in SxL [e_expr b; SxA lo; SxA len].
Definition d_region (x : sx) : SR.region := match x with SxL [b; SxA lo; SxA len] => (d_expr b, lo, len) | _ => (ELit 0, 0, 0) end.
Definition e_ps (ps : SR.post_spec) : sx :=
  SxL [SxA (SR.ps_pc ps); e_list (e_p2 e_nat e_expr) (SR.ps_regs ps); e_list e_region (SR.ps_regions ps); e_list e_kentry (SR.ps_cells ps)].
Definition d_ps (x : sx) : SR.post_spec :=
  match x with
  | SxL [SxA pc; regs; rg; cells] => SR.PS pc (d_list (d_p2 d_nat d_expr O (ELit 0)) regs) (d_list d_region rg) (d_list d_kentry cells)
  | _ => SR.PS 0 [] [] []
  end.
Definition e_tag (t : CC.tag) : sx :=
  match t with CC.TGoto j s => SxL [SxA 0; e_nat j; e_list (e_p2 e_nat e_expr) s] | CC.TOther id => SxL [SxA 1; SxA id] end.
Definition d_tag (x : sx) : CC.tag :=
  match x with SxL [SxA 0; j; s] => CC.TGoto (d_nat j) (d_list (d_p2 d_nat d_expr O (ELit 0)) s) | SxL [SxA 1; SxA id] => CC.TOther id | _ => CC.TOther 0 end.
Definition e_cert (c : list (nat * Z)) : sx := e_list (e_p2 e_nat e_Z) c.
Definition d_cert (x : sx) : list (nat * Z) := d_list (d_p2 d_nat d_Z O 0) x.
Definition e_xopb (o : CX.xop) : sx :=
  match o with
  | CX.OFact K => SxL [SxA 0; e_kentry K]
  | CX.OLtu a b s => SxL [SxA 1; e_expr a; e_expr b; e_bool s]
  | CX.OForget r => SxL [SxA 2; e_nat r]
  | CX.OContra c => SxL [SxA 3; e_cert c]
  | CX.OFactC K c => SxL [SxA 4; e_kentry K; e_cert c]
  end.
Definition d_xopb (x : sx) : CX.xop :=
  match x with
  | SxL [SxA 0; K] => CX.OFact (d_kentry K)
  | SxL [SxA 1; a; b; s] => CX.OLtu (d_expr a) (d_expr b) (d_bool s)
  | SxL [SxA 2; r] => CX.OForget (d_nat r)
  | SxL [SxA 3; c] => CX.OContra (d_cert c)
  | SxL [SxA 4; K; c] => CX.OFactC (d_kentry K) (d_cert c)
  | _ => CX.OForget O
  end.
Definition e_xop (o : CXD.xop) : sx :=
  match o with
  | CXD.OBase op => SxL [SxA 0; e_xopb op]
  | CXD.OLem Ps K => SxL [SxA 1; e_list e_kentry Ps; e_kentry K]
  | CXD.ONameB a => SxL [SxA 2; e_saddr a]
  | CXD.ONameW a w => SxL [SxA 3; e_saddr a; e_nat w]
  | CXD.OAbsW b o n => SxL [SxA 4; e_expr b; SxA o; SxA n]
  | CXD.OCoalW b o n => SxL [SxA 5; e_expr b; SxA o; e_expr n]
  | CXD.OCellR a a2 w => SxL [SxA 6; e_saddr a; e_saddr a2; e_nat w]
  end.
Definition d_xop (x : sx) : CXD.xop :=
  match x with
  | SxL [SxA 0; op] => CXD.OBase (d_xopb op)
  | SxL [SxA 1; Ps; K] => CXD.OLem (d_list d_kentry Ps) (d_kentry K)
  | SxL [SxA 2; a] => CXD.ONameB (d_saddr a)
  | SxL [SxA 3; a; w] => CXD.ONameW (d_saddr a) (d_nat w)
  | SxL [SxA 4; b; SxA o; SxA n] => CXD.OAbsW (d_expr b) o n
  | SxL [SxA 5; b; SxA o; n] => CXD.OCoalW (d_expr b) o (d_expr n)
  | SxL [SxA 6; a; a2; w] => CXD.OCellR (d_saddr a) (d_saddr a2) (d_nat w)
  | _ => CXD.OBase (CX.OForget O)
  end.
Definition e_xop2 (o : CX.xop2) : sx := match o with CX.OCase e mid => SxL [e_expr e; SxA mid] end.
Definition d_xop2 (x : sx) : CX.xop2 := match x with SxL [e; SxA mid] => CX.OCase (d_expr e) mid | _ => CX.OCase (ELit 0) 0 end.
Definition e_pout (o : CAD.pout) : sx :=
  SxL [e_plan (CAD.po_plan o); e_list (e_p2 e_ps e_tag) (CAD.po_leaves o); e_list e_xop (CAD.po_ops o); e_list e_xop2 (CAD.po_ops2 o)].
Definition d_pout (x : sx) : CAD.pout :=
  match x with
  | SxL [p; lv; ops; ops2] => CAD.PO (d_plan p) (d_list (d_p2 d_ps d_tag (SR.PS 0 [] [] []) (CC.TOther 0)) lv) (d_list d_xop ops) (d_list d_xop2 ops2)
  | _ => CAD.PO (SGP.PEnd O) [] [] []
  end.

Definition e_fregion (r : SGP.region) : sx := let '(b, lo, len) := r in SxL [e_expr b; SxA lo; e_expr len].
Definition d_fregion (x : sx) : SGP.region := match x with SxL [b; SxA lo; len] => (d_expr b, lo, d_expr len) | _ => (ELit 0, 0, ELit 0) end.
Definition e_cp (c : CC.cutpoint) : sx :=
  SxL [SxA (CC.cp_pc c); e_list e_expr (CC.cp_regs c); e_list e_kentry (CC.cp_know c); e_nat (CC.cp_nx c); e_list e_fregion (CC.cp_F c); e_list e_ps (CC.cp_PSS c); e_expr (CC.cp_meas c)].
Definition d_cp (x : sx) : CC.cutpoint :=
  match x with
  | SxL [SxA pc; regs; kn; nx; F; pss; meas] => CC.CP pc (d_list d_expr regs) (d_list d_kentry kn) (d_nat nx) (d_list d_fregion F) (d_list d_ps pss) (d_expr meas)
  | _ => CAD.dummy_cp
  end.
Definition e_bl (b : CAD.blocks) : sx := e_list (e_p2 e_expr e_expr) b.
Definition d_bl (x : sx) : CAD.blocks := d_list (d_p2 d_expr d_expr (ELit 0) (ELit 0)) x.

Definition mk_table (len : positive) (s : string) : pt := match parse len s with SxL es => build PTe 1%positive es | _ => PTe end.
Definition dec_pout_t (t : pt) (len : positive) (s : string) : CAD.pout := d_pout (resolve t (parse len s)).
Definition dec_cp_t (t : pt) (len : positive) (s : string) : CC.cutpoint := d_cp (resolve t (parse len s)).
Definition dec_bl_t (t : pt) (len : positive) (s : string) : CAD.blocks := d_bl (resolve t (parse len s)).

Definition enc_pout (o : CAD.pout) : string := print (e_pout o).
Definition dec_pout (len : positive) (s : string) : CAD.pout := d_pout (expand (parse len s)).

Definition rt_ok (len : positive) (s : string) : bool := PrimString.eqb (enc_pout (dec_pout len s)) s.
Definition enc_cp (c : CC.cutpoint) : string := print (e_cp c).
Definition dec_cp (len : positive) (s : string) : CC.cutpoint := d_cp (expand (parse len s)).
Definition rt_cp_ok (len : positive) (s : string) : bool := PrimString.eqb (enc_cp (dec_cp len s)) s.
Definition enc_bl (b : CAD.blocks) : string := print (e_bl b).
Definition dec_bl (len : positive) (s : string) : CAD.blocks := d_bl (expand (parse len s)).
Definition rt_bl_ok (len : positive) (s : string) : bool := PrimString.eqb (enc_bl (dec_bl len s)) s.

Definition slen63 (s : string) : int := PrimString.length s.
End CCDD.

Goal True.
  let o := constr:(CAD.PO (SGP.PCase (EAlu ALU_ADD (EVar 3) (ELit (-5))) 17 (SGP.PEnd 0) (SGP.PStep (SR.SBlock [4096; 4100]) (SGP.PEnd 1)))
                         [(SR.PS 65536 [(1%nat, EVar 1); (10%nat, ELit 0)] [(EVar 2, -16, 16)] [KRange (EVar 33) 0 255; KUnk (SA (EVar 2) (-32)) (ELit 32)], CC.TGoto 1 [(33%nat, EExt false 0 1 (EVar 40))]);
                          (SR.PS 4 [] [] [], CC.TOther 251380)]
                         [CXD.OBase (CX.OLtu (EVar 1) (EVar 2) true); CXD.ONameW (SA (ELit 0) 732620) 8] [CX.OCase (EVar 5) 9]) in
  let s := eval vm_compute in (CCDD.enc_pout o) in
  let n := eval vm_compute in (Pos.of_nat (Z.to_nat (Z.of_N (N.of_nat 400)))) in
  let b := eval vm_compute in (CCDD.rt_ok 400%positive s) in
  idtac s; idtac b;
  lazymatch b with true => idtac | _ => fail "CutCodec smoke test: round trip failed" end.
  exact I.
Qed.
