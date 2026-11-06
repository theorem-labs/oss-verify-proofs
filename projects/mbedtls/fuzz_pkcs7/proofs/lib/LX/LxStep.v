(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith PArith NArith List Bool Lia.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LX Require Import LxExpr LxDec LxMem.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Section LXH.
Context {lxHT : lx_hints}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Inductive ckind : Set := KEq | KLtu | KLts.
Inductive cond : Set := CN (negate : bool) (k : ckind) (a b : expr).

(* [comment removed for export] *)
Definition zbranch (bc : branch_cond) (x y : Z) : bool :=
  branch_taken bc (Z_to_bv 64 x) (Z_to_bv 64 y).

Definition ckind_of (bc : branch_cond) : bool * ckind :=
  match bc with
  | BC_EQ => (false, KEq) | BC_NE => (true, KEq)
  | BC_LTU => (false, KLtu) | BC_GEU => (true, KLtu)
  | BC_LT => (false, KLts) | BC_GE => (true, KLts)
  end.

Definition e_s64 (O : oracle) (e : expr) : bool := e_in O e (- two63) (two63 - 1).

(* [comment removed for export] *)
Definition e_win (O : oracle) (a b : expr) : bool :=
  if (if e_s64 O a then e_s64 O b else false) then true else (if e_in O a 1 two64 then e_in O b 1 two64 else false).

(* [comment removed for export] *)
Fixpoint shb_lookup (pf : list pfact) (v : positive) : option (expr * expr * expr) :=
  match pf with
  | [] => None
  | FShb v' c oa on :: pf' => if Pos.eqb v v' then Some (c, oa, on) else shb_lookup pf' v
  | _ :: pf' => shb_lookup pf' v
  end.

Definition shadow_slow (pf : list pfact) (a b : expr) : bool :=
  match lin_of b with
  | ([(1, EZv v)], 0) =>
      match shb_lookup pf v with
      | Some (c, oa, on) =>
          match lin_of a with
          | ([(1, EOp OAnd c' (ELit 7))], d) =>
              if (if (if Z.leb 0 d then expr_eqb c' c else false) then dec_le pf (ELit 1) b else false) then dec_inside pf c (ELit (d + 1)) oa on else false
          (* [comment removed for export] *)
          | ([], d) =>
              if (if Z.leb 0 d then dec_le pf (ELit 1) b else false) then dec_inside pf c (ELit (d + 1)) oa on else false
          | _ => false
          end
      | None => false
      end
  | _ => false
  end.

(* [comment removed for export] *)
Definition nlit (k : ckind) (e : expr) : expr :=
  match e with
  | ELit x => ELit (match k with KLts => zswrap 64 x | _ => zlow 64 x end)
  | _ => e
  end.

(* [comment removed for export] *)
Definition decide_kind0 (O : oracle) (pf : list pfact) (k : ckind) (a b : expr) : option bool :=
  match is_lit a, is_lit b with
  | Some x, Some y =>
      Some (match k with
            | KEq => Z.eqb (zlow 64 x) (zlow 64 y)
            | KLtu => Z.ltb (zlow 64 x) (zlow 64 y)
            | KLts => Z.ltb (zswrap 64 x) (zswrap 64 y)
            end)
  | _, _ =>
      match k with
      | KEq =>
          if dec_eq pf a b then Some true
          else if (if (if (if e_u64 O a then e_u64 O b else false) then true else e_win O a b)
                   then (if dec_lt pf a b then true else dec_lt pf b a) else false) then Some false
          else None
      | KLtu =>
          if (if e_u64 O a then e_u64 O b else false) then
            (if dec_lt pf a b then Some true else if dec_le pf b a then Some false else None)
          else None
      | KLts =>
          if shadow_slow pf a b then Some true else
          if (if e_s64 O a then e_s64 O b else false) then
            (if dec_lt pf a b then Some true else if dec_le pf b a then Some false else None)
          else None
      end
  end.

Definition decide_kind (O : oracle) (pf : list pfact) (k : ckind) (a b : expr) : option bool :=
  decide_kind0 O pf k (nlit k a) (nlit k b).

Definition decide_cond (O : oracle) (pf : list pfact) (c : cond) : option bool :=
  match c with CN n k a b => option_map (xorb n) (decide_kind O pf k a b) end.

(* [comment removed for export] *)
Definition kind_facts (O : oracle) (k : ckind) (a b : expr) (outcome : bool) : list pfact :=
  (* [comment removed for export] *)
  match k with
  | KEq =>
      (* [comment removed for export] *)
      let sgn := if e_win O a b then negb (if e_u64 O a then e_u64 O b else false) else false in
      let a' := if sgn then a else elow O a 64 in let b' := if sgn then b else elow O b 64 in
      if outcome then [FGe (esub a' b'); FGe (esub b' a')] else [FSep a' (ELit 1) b' (ELit 1)]
  | KLtu =>
      let a' := elow O a 64 in let b' := elow O b 64 in
      if outcome then [FGe (esub (esub b' a') (ELit 1))] else [FGe (esub a' b')]
  | KLts =>
      let a' := esx O a 64 in let b' := esx O b 64 in
      if outcome then [FGe (esub (esub b' a') (ELit 1))] else [FGe (esub a' b')]
  end.

Definition cond_facts (O : oracle) (c : cond) (taken : bool) : list pfact :=
  match c with CN n k a b => kind_facts O k a b (xorb n taken) end.

(* [comment removed for export] *)
Definition kind_expr (O : oracle) (k : ckind) (a b : expr) : expr :=
  match k with
  | KLtu => eatom (EOp OLtu (elow O a 64) (elow O b 64))
  | KLts => eatom (EOp OLts (esx O a 64) (esx O b 64))
  | KEq => ELit 0 (* [comment removed for export] *)
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Inductive dir : Set :=
| DSplit                      (* [comment removed for export] *)
| DJoin                       (* [comment removed for export] *)
| DMerge (r : Z).             (* [comment removed for export] *)

Inductive sres : Set :=
| SNext (ss' : sstate)
| SBind (ss' : sstate)                          (* [comment removed for export] *)
| SBranch (c : cond) (st sf : sstate)           (* [comment removed for export] *)
| SStop (ss' : sstate)                          (* [comment removed for export] *)
| SFail (code : Z).

(* [comment removed for export] *)
Definition zalu (op : aluop) (x y : Z) : Z :=
  bv_unsigned (alu64 op (Z_to_bv 64 x) (Z_to_bv 64 y)).
Definition zalu32 (op : aluop) (x y : Z) : Z :=
  bv_unsigned (sext 64 (alu32 op (low32 (Z_to_bv 64 x)) (low32 (Z_to_bv 64 y))) : word).
Definition zmuldiv (op : mulop) (x y : Z) : Z :=
  bv_unsigned (mul_div op (Z_to_bv 64 x) (Z_to_bv 64 y) : word).
Definition zmuldiv32 (op : mulop) (x y : Z) : Z :=
  bv_unsigned (sext 64 (mul_div op (low32 (Z_to_bv 64 x)) (low32 (Z_to_bv 64 y))) : word).
Definition zlui (imm : bv 20) : Z :=
  bv_unsigned (sext 64 (bv_concat 32 imm (Z_to_bv 12 0)) : word).

(* [comment removed for export] *)
Definition sym_alu (O : oracle) (pf : list pfact) (op : aluop) (a b : expr) : option expr :=
  match is_lit a, is_lit b, op with
  | Some x, Some y, (ALU_SLL | ALU_SRL | ALU_SRA | ALU_SLT | ALU_SLTU) => Some (ELit (zalu op x y))
  | _, _, _ =>
      (* [comment removed for export] *)
      match op with
      | ALU_ADD => Some (eadd a b)
      | ALU_SUB => Some (esub a b)
      | ALU_AND => Some (eand O a b)
      | ALU_OR => Some (eor O a b)
      | ALU_XOR => Some (exor O a b)
      | ALU_SLL => match is_lit b with
                   | Some k => if Z.leb 0 k then Some (eshl a (Z.land k 63)) else None
                   (* [comment removed for export] *)
                   | None => Some (eatom (EOp OShl (elow O a 64) (elow O b 6))) end
      | ALU_SRL => match is_lit b with
                   | Some k => if Z.leb 0 k then Some (eshr O a (Z.land k 63)) else None
                   (* [comment removed for export] *)
                   | None => Some (eatom (EOp OShr (elow O a 64) (elow O b 6))) end
      | ALU_SRA => match is_lit b with
                   | Some k => if Z.leb 0 k then Some (eatom (EOp OShr (esx O a 64) (ELit (Z.land k 63)))) else None
                   | None => None end
      | ALU_SLTU => match decide_kind O pf KLtu a b with
                    | Some true => Some (ELit 1) | Some false => Some (ELit 0)
                    | None => Some (kind_expr O KLtu a b) end
      | ALU_SLT => match decide_kind O pf KLts a b with
                   | Some true => Some (ELit 1) | Some false => Some (ELit 0)
                   | None => Some (kind_expr O KLts a b) end
      end
  end.

(* [comment removed for export] *)
Definition sym_alu32 (O : oracle) (op : aluop) (a b : expr) : option expr :=
  match is_lit a, is_lit b, op with
  | Some x, Some y, (ALU_SRL | ALU_SRA | ALU_SLT | ALU_SLTU | ALU_AND | ALU_OR | ALU_XOR) => Some (ELit (zalu32 op x y))
  | _, _, _ =>
      match op with
      | ALU_ADD => Some (ew32 O (eadd a b))
      | ALU_SUB => Some (ew32 O (esub a b))
      (* [comment removed for export] *)
      | ALU_SLL => match is_lit b with
                   | Some k => if Z.leb 0 k then Some (ew32 O (eshl a (Z.land k 31))) else None
                   | None => Some (esx O (elow O (eatom (EOp OShl (elow O a 32) (elow O b 5))) 32) 32) end
      | ALU_SRL => match is_lit b with
                   | Some k => if Z.leb 0 k then (let s := Z.land k 31 in
                                 Some (if Z.eqb s 0 then ew32 O a else eatom (EOp OShr (elow O a 32) (ELit s)))) else None
                   | None => Some (esx O (eatom (EOp OShr (elow O a 32) (elow O b 5))) 32) end
      | ALU_SRA => match is_lit b with
                   | Some k => if Z.leb 0 k then (let s := Z.land k 31 in
                                 Some (if Z.eqb s 0 then ew32 O a else eatom (EOp OShr (esx O a 32) (ELit s)))) else None
                   | None => None end
      | _ => None
      end
  end.

Definition sym_mul (O : oracle) (op : mulop) (a b : expr) : option expr :=
  match is_lit a, is_lit b with
  | Some x, Some y => Some (ELit (zmuldiv op x y))
  | _, _ =>
      match op with
      | M_MUL => Some (emulO O a b)
      | M_DIVU => match is_lit b with
                  | Some y => let y' := zlow 64 y in
                              Some (if Z.eqb y' 0 then ELit (two64 - 1) else eatom (EOp ODivU (elow O a 64) (ELit y')))
                  | None => None end
      | M_REMU => match is_lit b with
                  | Some y => let y' := zlow 64 y in
                              Some (if Z.eqb y' 0 then a else eatom (EOp ORemU (elow O a 64) (ELit y')))
                  | None => None end
      | _ => None
      end
  end.

Definition ridx (r : reg) : Z := bv_unsigned r.

Definition msize_N (sz : msize) : N :=
  match sz with SZ1 => 1 | SZ2 => 2 | SZ4 => 4 | SZ8 => 8 end%N.

(* [comment removed for export] *)
Definition contradictory (pf : list pfact) : bool := lin_ge pf (ELit (-1)).

Section Step.
  Variable C : lxcfg.

  Definition next_pc (ss : sstate) (pc sz : Z) : sstate := set_pc ss (PCz (pc + sz)).

  (* [comment removed for export] *)
  Definition settle (ss : sstate) : sstate := set_pf ss (settle_seps (s_pf ss)).

  (* [comment removed for export] *)
  Definition havoc_rd_with (ss : sstate) (rd : Z) (extra : list pfact) (pc sz : Z) : sres :=
    let v := s_nx ss in
    let ev := eatom (EZv v) in
    let ss1 := add_pfs (bump ss) ([FGe ev; FGe (eadd (ELit (two64 - 1)) (emulc (-1) ev))] ++ extra) in
    SBind (next_pc (wr_reg ss1 rd (RZ ev)) pc sz).
  Definition havoc_rd (ss : sstate) (rd : Z) (pc sz : Z) : sres := havoc_rd_with ss rd [] pc sz.

  (* [comment removed for export] *)
  Fixpoint eops (e : expr) : nat :=
    match e with
    | EOp _ a b => S (eops a + eops b)
    | EAdd a b => (eops a + eops b)%nat
    | EMulC _ a => eops a
    | _ => O
    end.
  Definition ebig_ops : nat := 24%nat.
  Definition ebig (e : expr) : bool := Nat.leb ebig_ops (eops e).

  (* [comment removed for export] *)
  Definition def_fact (O : oracle) (v : positive) (e : expr) : list pfact :=
    if evars_lt v e then [FEq (eatom (EZv v)) (elow O e 64)] else [].

  (* [comment removed for export] *)
  Definition finish_rd (ss : sstate) (rd : Z) (e : expr) (pc sz : Z) : sres :=
    if ebig e then havoc_rd_with ss rd (def_fact (oracle_of ss) (s_nx ss) e) pc sz
    else SNext (next_pc (wr_reg ss rd (mkreg e)) pc sz).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition align_down (O : oracle) (op : aluop) (a b : expr) (v : positive) : option Z :=
    match op, is_lit a, is_lit b with
    | ALU_AND, None, Some m =>
        match high_mask_j m with
        | Some j => if e_u64 O a && Z.leb 1 j && Z.leb j 63 && negb (N.leb (Z.to_N j) (eal O a)) && evars_lt v a then Some j else None
        | None => None
        end
    | _, _, _ => None
    end.

  Definition align_facts (a : expr) (j : Z) (v : positive) : list pfact :=
    let ev := emulc (2 ^ j) (eatom (EZv v)) in
    [FGe (esub a ev); FGe (eadd (esub ev a) (ELit (2 ^ j - 1)))].

  (* [comment removed for export] *)
  Definition havoc_rd_scaled (ss : sstate) (rd : Z) (k : Z) (extra : list pfact) (pc sz : Z) : sres :=
    let v := s_nx ss in
    let ev := emulc k (eatom (EZv v)) in
    let ss1 := add_pfs (bump ss) ([FGe ev; FGe (eadd (ELit (two64 - 1)) (emulc (-1) ev))] ++ extra) in
    SBind (next_pc (wr_reg ss1 rd (RZ ev)) pc sz).

  Definition alu_extra (O : oracle) (op : aluop) (a b : expr) (v : positive) : list pfact :=
    match op, is_lit a, is_lit b with
    | ALU_AND, None, Some m =>
        match high_mask_j m with
        | Some j => if e_u64 O a && Z.leb 1 j && Z.leb j 63 && negb (N.leb (Z.to_N j) (eal O a)) && evars_lt v a then
                      let ev := eatom (EZv v) in
                      [FGe (esub a ev); FGe (eadd (esub ev a) (ELit (2 ^ j - 1))); FAl (EZv v) (Z.to_N j)]
                    else []
        | None => []
        end
    | _, _, _ => []
    end.

  Definition do_load (ss : sstate) (msz : msize) (sx : bool) (rd rs1 : Z) (imm : Z) (pc sz : Z) : sres :=
    let a := eadd (rd_expr ss rs1) (ELit imm) in
    let w := msize_N msz in
    match acc_class C ss a (Z.of_N w) with
    | None => SFail 30 (* [comment removed for export] *)
    | Some _ =>
        match sym_load C ss a w sx with
        | LReg r => SNext (next_pc (wr_reg ss rd r) pc sz)
        | LFresh lo hi =>
            let v := s_nx ss in
            let ev := eatom (EZv v) in
            let ss1 := add_pfs (bump ss) [FGe (eadd ev (ELit (- lo))); FGe (eadd (emulc (-1) ev) (ELit hi))] in
            SBind (next_pc (wr_reg ss1 rd (RZ ev)) pc sz)
        | LShb c oa on =>
            let v := s_nx ss in
            if evars_lt v c && evars_lt v oa && evars_lt v on then
              let ev := eatom (EZv v) in
              let ss1 := add_pfs (bump ss) [FGe ev; FGe (eadd (emulc (-1) ev) (ELit 7)); FShb v c oa on] in
              SBind (next_pc (wr_reg ss1 rd (RZ ev)) pc sz)
            else SFail 33
        | LNone => SFail 31 (* [comment removed for export] *)
        end
    end.

  Definition do_store (ss : sstate) (msz : msize) (rs1 rs2 : Z) (imm : Z) (pc sz : Z) : sres :=
    let a := eadd (rd_expr ss rs1) (ELit imm) in
    let w := msize_N msz in
    match acc_class C ss a (Z.of_N w) with
    | None => SFail 32
    | Some cl =>
        match sym_store C cl ss a w (rd_reg ss rs2) with
        | StOk mf' W' => SNext (next_pc (set_W (set_mf ss mf') W') pc sz)
        | StFail code => SFail code
        end
    end.

  (* [comment removed for export] *)
  Definition amo_w (wd : awidth) : N := match wd with AW => 4%N | AD => 8%N end.

  Definition amo_expr (O : oracle) (op : amoop) (old src : expr) : option expr :=
    match op with
    | AMO_SWAP => Some src
    | AMO_ADD => Some (eadd old src)
    | AMO_AND => Some (eand O old src)
    | AMO_OR => Some (eor O old src)
    | AMO_XOR => Some (exor O old src)
    | _ => None
    end.

  Definition do_amo (ss : sstate) (op : amoop) (wd : awidth) (rd rs1 rs2 : Z) (pc sz : Z) : sres :=
    let a := rd_expr ss rs1 in
    let w := amo_w wd in
    let O := oracle_of ss in
    if negb (N.leb (match wd with AW => 2%N | AD => 3%N end) (eal O a)) then SFail 11 else
    match acc_class C ss a (Z.of_N w) with
    | None => SFail 30
    | Some cl =>
        match sym_load C ss a w true with
        | LReg r =>
            match amo_expr O op (expr_of_reg r) (rd_expr ss rs2) with
            | None => SFail 13
            | Some v =>
                match sym_store C cl ss a w (mkreg v) with
                | StOk mf' W' => SNext (next_pc (wr_reg (set_W (set_mf ss mf') W') rd r) pc sz)
                | StFail code => SFail code
                end
            end
        | _ => SFail 12
        end
    end.

  Definition do_branch (D : Z -> option dir) (ss : sstate) (bc : branch_cond) (rs1 rs2 : Z) (off : Z) (pc sz : Z) : sres :=
    let a := rd_expr ss rs1 in let b := rd_expr ss rs2 in
    let '(n, k) := ckind_of bc in
    let c := CN n k a b in
    let O := oracle_of ss in
    match decide_cond O (s_pf ss) c with
    | Some true => SNext (set_pc ss (PCz (pc + off)))
    | Some false => SNext (set_pc ss (PCz (pc + sz)))
    | None =>
        let st := set_pc (settle (add_pfs ss (cond_facts O c true))) (PCz (pc + off)) in
        let sf := set_pc (settle (add_pfs ss (cond_facts O c false))) (PCz (pc + sz)) in
        SBranch c st sf
    end.

  (* [comment removed for export] *)
  Definition do_slt (D : Z -> option dir) (ss : sstate) (k : ckind) (rd : Z) (a b : expr) (pc sz : Z) : sres :=
    let O := oracle_of ss in
    match decide_kind O (s_pf ss) k a b with
    | Some true => finish_rd ss rd (ELit 1) pc sz
    | Some false => finish_rd ss rd (ELit 0) pc sz
    | None =>
        match D pc with
        | Some DSplit =>
            let c := CN false k a b in
            let st := next_pc (wr_reg (add_pfs ss (cond_facts O c true)) rd (RZ (ELit 1))) pc sz in
            let sf := next_pc (wr_reg (add_pfs ss (cond_facts O c false)) rd (RZ (ELit 0))) pc sz in
            SBranch c st sf
        | _ => finish_rd ss rd (kind_expr O k a b) pc sz
        end
    end.

  Definition sym_step (D : Z -> option dir) (i : instr) (sz : Z) (ss : sstate) : sres :=
    match s_pc ss with
    | PCret _ => SFail 1
    | PCz pc =>
    let O := oracle_of ss in
    match i with
    | Lui rd imm => finish_rd ss (ridx rd) (ELit (zlui imm)) pc sz
    | Auipc rd imm => finish_rd ss (ridx rd) (ELit (zlow 64 (pc + zlui imm))) pc sz
    | Jal rd imm =>
        let ss1 := wr_reg ss (ridx rd) (RZ (ELit (zlow 64 (pc + sz)))) in
        SNext (set_pc ss1 (PCz (zlow 64 (pc + bv_signed imm))))
    | Jalr rd rs1 imm =>
        match rd_reg ss (ridx rs1), ridx rd, bv_signed imm with
        | RW j, 0, 0 => SStop (set_pc ss (PCret (RW j)))
        | r, _, immz =>
            match is_lit (expr_of_reg r) with
            | Some t =>
                let tgt := Z.land (zlow 64 (t + immz)) (Z.lnot 1) in
                let ss1 := wr_reg ss (ridx rd) (RZ (ELit (zlow 64 (pc + sz)))) in
                SNext (set_pc ss1 (PCz tgt))
            | None => SFail 2 (* [comment removed for export] *)
            end
        end
    | Branch bc rs1 rs2 imm => do_branch D ss bc (ridx rs1) (ridx rs2) (bv_signed imm) pc sz
    | Load msz sx rd rs1 imm => do_load ss msz sx (ridx rd) (ridx rs1) (bv_signed imm) pc sz
    | Store msz rs1 rs2 imm => do_store ss msz (ridx rs1) (ridx rs2) (bv_signed imm) pc sz
    | OpImm op rd rs1 imm =>
        match op with
        | ALU_SLT | ALU_SLTU =>
            do_slt D ss (match op with ALU_SLT => KLts | _ => KLtu end) (ridx rd) (rd_expr ss (ridx rs1)) (ELit (bv_signed imm)) pc sz
        | _ =>
            match alu_extra O op (rd_expr ss (ridx rs1)) (ELit (bv_signed imm)) (s_nx ss) with
            | [] =>
                match sym_alu O (s_pf ss) op (rd_expr ss (ridx rs1)) (ELit (bv_signed imm)) with
                | Some e => finish_rd ss (ridx rd) e pc sz
                | None => havoc_rd ss (ridx rd) pc sz
                end
            | extra => havoc_rd_with ss (ridx rd) extra pc sz
            end
        end
    | ShiftImm op rd rs1 shamt =>
        match sym_alu O (s_pf ss) op (rd_expr ss (ridx rs1)) (ELit (bv_unsigned shamt)) with
        | Some e => finish_rd ss (ridx rd) e pc sz
        | None => havoc_rd ss (ridx rd) pc sz
        end
    | Op op rd rs1 rs2 =>
        match op with
        | ALU_SLT | ALU_SLTU =>
            do_slt D ss (match op with ALU_SLT => KLts | _ => KLtu end) (ridx rd) (rd_expr ss (ridx rs1)) (rd_expr ss (ridx rs2)) pc sz
        | _ =>
            match sym_alu O (s_pf ss) op (rd_expr ss (ridx rs1)) (rd_expr ss (ridx rs2)) with
            | Some e => finish_rd ss (ridx rd) e pc sz
            | None => havoc_rd ss (ridx rd) pc sz
            end
        end
    | OpImm32 rd rs1 imm =>
        match sym_alu32 O ALU_ADD (rd_expr ss (ridx rs1)) (ELit (bv_signed imm)) with
        | Some e => finish_rd ss (ridx rd) e pc sz
        | None => havoc_rd ss (ridx rd) pc sz
        end
    | ShiftImm32 op rd rs1 shamt =>
        match sym_alu32 O op (rd_expr ss (ridx rs1)) (ELit (bv_unsigned shamt)) with
        | Some e => finish_rd ss (ridx rd) e pc sz
        | None => havoc_rd ss (ridx rd) pc sz
        end
    | Op32 op rd rs1 rs2 =>
        match sym_alu32 O op (rd_expr ss (ridx rs1)) (rd_expr ss (ridx rs2)) with
        | Some e => finish_rd ss (ridx rd) e pc sz
        | None => havoc_rd ss (ridx rd) pc sz
        end
    | Mul op rd rs1 rs2 =>
        match sym_mul O op (rd_expr ss (ridx rs1)) (rd_expr ss (ridx rs2)) with
        | Some e => finish_rd ss (ridx rd) e pc sz
        | None => havoc_rd ss (ridx rd) pc sz
        end
    (* [comment removed for export] *)
    | Mul32 _ rd _ _ => havoc_rd ss (ridx rd) pc sz
    | Fence _ _ _ _ _ => SNext (set_pc ss (PCz (pc + sz)))
    | Amo op wd _ _ rd rs1 rs2 => do_amo ss op wd (ridx rd) (ridx rs1) (ridx rs2) pc sz
    | _ => SFail 10
    end
    end.
End Step.

End LXH.
