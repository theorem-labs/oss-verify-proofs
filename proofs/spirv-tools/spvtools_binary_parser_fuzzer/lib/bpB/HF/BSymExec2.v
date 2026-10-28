(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BPropExec BCatExec BCatSim BSeqExec BStoreOk BSymExec.
Import ListNotations.
Open Scope bv_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Module SX2.

Inductive expr : Type :=
| ELit  (z : Z)
| EVar  (n : nat)
| EAlu  (op : aluop) (a b : expr)
| EAluw (op : aluop) (a b : expr)
| EMd   (op : mulop) (a b : expr)
| EMdw  (op : mulop) (a b : expr)
| EExt  (sx : bool) (lo n : nat) (e : expr)
| EBlob (sx : bool) (k : nat) (i : Z) (n : nat).

Record env : Type := Env { ev : nat -> word; eb : nat -> list byte }.

Definition ext_Z (sx : bool) (lo n : nat) (z : Z) : Z :=
  let u := ((z / 2 ^ (8 * Z.of_nat lo)) mod 2 ^ (8 * Z.of_nat n))%Z in
  if sx then bv_swrap (8 * N.of_nat n) u else u.

Definition ext_val (sx : bool) (lo n : nat) (v : word) : word :=
  Z_to_bv 64 (ext_Z sx lo n (bv_unsigned v)).

Definition blob_bytes (bs : list byte) (i : Z) (n : nat) : list byte :=
  firstn n (skipn (Z.to_nat i) bs).

Definition blob_val (sx : bool) (bs : list byte) (i : Z) (n : nat) : word :=
  Z_to_bv 64 (let u := bytes_le_to_Z (blob_bytes bs i n) in
              if sx then bv_swrap (8 * N.of_nat n) u else u).

Fixpoint edenot (E : env) (e : expr) : word :=
  match e with
  | ELit z => Z_to_bv 64 z
  | EVar n => ev E n
  | EAlu op a b => alu64 op (edenot E a) (edenot E b)
  | EAluw op a b => sext 64 (alu32 op (low32 (edenot E a)) (low32 (edenot E b)))
  | EMd op a b => mul_div op (edenot E a) (edenot E b)
  | EMdw op a b => sext 64 (mul_div op (low32 (edenot E a)) (low32 (edenot E b)))
  | EExt sx lo n a => ext_val sx lo n (edenot E a)
  | EBlob sx k i n => blob_val sx (eb E k) i n
  end.

Definition aluop_eqb (a b : aluop) : bool :=
  match a, b with
  | ALU_ADD, ALU_ADD | ALU_SUB, ALU_SUB | ALU_SLL, ALU_SLL | ALU_SLT, ALU_SLT
  | ALU_SLTU, ALU_SLTU | ALU_XOR, ALU_XOR | ALU_SRL, ALU_SRL | ALU_SRA, ALU_SRA
  | ALU_OR, ALU_OR | ALU_AND, ALU_AND => true
  | _, _ => false
  end.

Definition mulop_eqb (a b : mulop) : bool :=
  match a, b with
  | M_MUL, M_MUL | M_MULH, M_MULH | M_MULHSU, M_MULHSU | M_MULHU, M_MULHU
  | M_DIV, M_DIV | M_DIVU, M_DIVU | M_REM, M_REM | M_REMU, M_REMU => true
  | _, _ => false
  end.

Fixpoint expr_eqb (x y : expr) : bool :=
  match x, y with
  | ELit a, ELit b => Z.eqb a b
  | EVar a, EVar b => Nat.eqb a b
  | EAlu o a b, EAlu o' a' b' => aluop_eqb o o' && expr_eqb a a' && expr_eqb b b'
  | EAluw o a b, EAluw o' a' b' => aluop_eqb o o' && expr_eqb a a' && expr_eqb b b'
  | EMd o a b, EMd o' a' b' => mulop_eqb o o' && expr_eqb a a' && expr_eqb b b'
  | EMdw o a b, EMdw o' a' b' => mulop_eqb o o' && expr_eqb a a' && expr_eqb b b'
  | EExt s l n a, EExt s' l' n' a' =>
      Bool.eqb s s' && Nat.eqb l l' && Nat.eqb n n' && expr_eqb a a'
  | EBlob s k i n, EBlob s' k' i' n' =>
      Bool.eqb s s' && Nat.eqb k k' && Z.eqb i i' && Nat.eqb n n'
  | _, _ => false
  end.

Definition zalu (op : aluop) (x y : Z) : Z :=
  bv_unsigned (alu64 op (Z_to_bv 64 x) (Z_to_bv 64 y)).
Definition zaluw (op : aluop) (x y : Z) : Z :=
  bv_unsigned (sext 64 (alu32 op (low32 (Z_to_bv 64 x)) (low32 (Z_to_bv 64 y))) : word).
Definition zmd (op : mulop) (x y : Z) : Z :=
  bv_unsigned (mul_div op (Z_to_bv 64 x) (Z_to_bv 64 y)).
Definition zmdw (op : mulop) (x y : Z) : Z :=
  bv_unsigned (sext 64 (mul_div op (low32 (Z_to_bv 64 x)) (low32 (Z_to_bv 64 y))) : word).
Definition zext_lit (sx : bool) (lo n : nat) (x : Z) : Z :=
  bv_unsigned (ext_val sx lo n (Z_to_bv 64 x)).

Definition is_lit (e : expr) : option Z :=
  match e with ELit z => Some z | _ => None end.

Definition two64z : Z := 2 ^ 64.
Definition snorm (k : Z) : Z :=
  let m := (k mod two64z)%Z in if Z.leb (2 ^ 63) m then (m - two64z)%Z else m.

Definition lin : Type := (Z * list (Z * expr))%type.

Definition ctor_ix (e : expr) : nat :=
  match e with
  | ELit _ => 0 | EVar _ => 1 | EAlu _ _ _ => 2 | EAluw _ _ _ => 3
  | EMd _ _ _ => 4 | EMdw _ _ _ => 5 | EExt _ _ _ _ => 6 | EBlob _ _ _ _ => 7
  end.
Definition aluop_ix (op : aluop) : nat :=
  match op with
  | ALU_ADD => 0 | ALU_SUB => 1 | ALU_SLL => 2 | ALU_SLT => 3 | ALU_SLTU => 4
  | ALU_XOR => 5 | ALU_SRL => 6 | ALU_SRA => 7 | ALU_OR => 8 | ALU_AND => 9
  end.
Definition mulop_ix (op : mulop) : nat :=
  match op with
  | M_MUL => 0 | M_MULH => 1 | M_MULHSU => 2 | M_MULHU => 3
  | M_DIV => 4 | M_DIVU => 5 | M_REM => 6 | M_REMU => 7
  end.
Definition bool_ix (b : bool) : nat := if b then 1 else 0.
Definition lexc (c k : comparison) : comparison := match c with Eq => k | _ => c end.

Fixpoint expr_cmp (x y : expr) {struct x} : comparison :=
  match x, y with
  | ELit a, ELit b => Z.compare a b
  | EVar a, EVar b => Nat.compare a b
  | EAlu o a b, EAlu o' a' b' =>
      lexc (Nat.compare (aluop_ix o) (aluop_ix o')) (lexc (expr_cmp a a') (expr_cmp b b'))
  | EAluw o a b, EAluw o' a' b' =>
      lexc (Nat.compare (aluop_ix o) (aluop_ix o')) (lexc (expr_cmp a a') (expr_cmp b b'))
  | EMd o a b, EMd o' a' b' =>
      lexc (Nat.compare (mulop_ix o) (mulop_ix o')) (lexc (expr_cmp a a') (expr_cmp b b'))
  | EMdw o a b, EMdw o' a' b' =>
      lexc (Nat.compare (mulop_ix o) (mulop_ix o')) (lexc (expr_cmp a a') (expr_cmp b b'))
  | EExt s l n e, EExt s' l' n' e' =>
      lexc (Nat.compare (bool_ix s) (bool_ix s'))
           (lexc (Nat.compare l l') (lexc (Nat.compare n n') (expr_cmp e e')))
  | EBlob s k i n, EBlob s' k' i' n' =>
      lexc (Nat.compare (bool_ix s) (bool_ix s'))
           (lexc (Nat.compare k k') (lexc (Z.compare i i') (Nat.compare n n')))
  | _, _ => Nat.compare (ctor_ix x) (ctor_ix y)
  end.

Fixpoint lins (k : Z) (a : expr) (ts : list (Z * expr)) : list (Z * expr) :=
  match ts with
  | [] => if Z.eqb (snorm k) 0 then [] else [(snorm k, a)]
  | (k', a') :: rest =>
      if expr_eqb a a' then
        (let s := snorm (k + k') in if Z.eqb s 0 then rest else (s, a') :: rest)
      else match expr_cmp a a' with
           | Lt => if Z.eqb (snorm k) 0 then ts else (snorm k, a) :: ts
           | _ => (k', a') :: lins k a rest
           end
  end.

Definition ladd (x y : lin) : lin :=
  (snorm (fst x + fst y), fold_right (fun t acc => lins (fst t) (snd t) acc) (snd y) (snd x)).

Fixpoint lscale_terms (m : Z) (ts : list (Z * expr)) : list (Z * expr) :=
  match ts with
  | [] => []
  | (k, a) :: rest =>
      let k' := snorm (m * k) in
      if Z.eqb k' 0 then lscale_terms m rest else (k', a) :: lscale_terms m rest
  end.

Definition lscale (m : Z) (x : lin) : lin := (snorm (m * fst x), lscale_terms m (snd x)).

Fixpoint lin_of (e : expr) : lin :=
  match e with
  | ELit z => (snorm z, [])
  | EAlu ALU_ADD a b => ladd (lin_of a) (lin_of b)
  | EAlu ALU_SUB a b => ladd (lin_of a) (lscale (-1) (lin_of b))
  | EAlu ALU_SLL a (ELit s) => lscale (2 ^ (s mod 64)) (lin_of a)
  | EMd M_MUL (ELit k) a => lscale k (lin_of a)
  | EMd M_MUL a (ELit k) => lscale k (lin_of a)
  | _ => (0%Z, [(1%Z, e)])
  end.

Definition lterm (t : Z * expr) : expr :=
  if Z.eqb (fst t) 1 then snd t else EMd M_MUL (ELit (fst t)) (snd t).

Fixpoint lterms (ts : list (Z * expr)) : expr :=
  match ts with
  | [] => ELit 0
  | [t] => lterm t
  | t :: rest => EAlu ALU_ADD (lterm t) (lterms rest)
  end.

Definition unlin (x : lin) : expr :=
  match snd x with
  | [] => ELit (fst x)
  | _ => if Z.eqb (fst x) 0 then lterms (snd x) else EAlu ALU_ADD (lterms (snd x)) (ELit (fst x))
  end.

Fixpoint coeffs_div (m : Z) (ts : list (Z * expr)) : bool :=
  match ts with
  | [] => true
  | (k, _) :: rest => (Z.eqb (k mod m) 0 && coeffs_div m rest)%bool
  end.

Definition lin_lowbits (e : expr) (k : Z) : option Z :=
  let l := lin_of e in
  if coeffs_div (2 ^ k) (snd l) then Some ((fst l) mod 2 ^ k)%Z else None.

Definition shamt_of (e : expr) (bits : Z) : option Z :=
  match e with
  | ELit s => Some (s mod 2 ^ bits)%Z
  | _ => lin_lowbits e bits
  end.

Definition mkAlu (op : aluop) (a b : expr) : expr :=
  match is_lit a, is_lit b with
  | Some x, Some y => ELit (zalu op x y)
  | _, _ =>
    match op with
    | ALU_ADD => unlin (ladd (lin_of a) (lin_of b))
    | ALU_SUB => unlin (ladd (lin_of a) (lscale (-1) (lin_of b)))
    | ALU_SLL => match shamt_of b 6 with
                 | Some s => unlin (lscale (2 ^ s) (lin_of a))
                 | None => EAlu op a b
                 end
    | ALU_SRL | ALU_SRA => match is_lit b with
                           | Some _ => EAlu op a b
                           | None => match shamt_of b 6 with
                                     | Some s => EAlu op a (ELit s)
                                     | None => EAlu op a b
                                     end
                           end
    | _ => EAlu op a b
    end
  end.

Definition mkAluw (op : aluop) (a b : expr) : expr :=
  match is_lit a, is_lit b with
  | Some x, Some y => ELit (zaluw op x y)
  | _, _ =>
      match op with
      | ALU_SLL | ALU_SRL | ALU_SRA =>
          match is_lit b with
          | Some _ => EAluw op a b
          | None => match shamt_of b 5 with
                    | Some s => match is_lit a with
                                | Some x => ELit (zaluw op x s)
                                | None => EAluw op a (ELit s)
                                end
                    | None => EAluw op a b
                    end
          end
      | _ => EAluw op a b
      end
  end.

Definition mkMd (op : mulop) (a b : expr) : expr :=
  match is_lit a, is_lit b with
  | Some x, Some y => ELit (zmd op x y)
  | Some x, None => match op with M_MUL => unlin (lscale x (lin_of b)) | _ => EMd op a b end
  | None, Some y => match op with M_MUL => unlin (lscale y (lin_of a)) | _ => EMd op a b end
  | _, _ => EMd op a b
  end.

Definition mkMdw (op : mulop) (a b : expr) : expr :=
  match is_lit a, is_lit b with
  | Some x, Some y => ELit (zmdw op x y)
  | _, _ => EMdw op a b
  end.

Definition mkExt (sx : bool) (lo n : nat) (e : expr) : expr :=
  match e with
  | ELit x => ELit (zext_lit sx lo n x)
  | _ =>
    if (Nat.eqb lo 0 && Nat.eqb n 8)%bool then e
    else match e with
         | EExt false lo' n' e' =>
             if (Nat.leb (lo + n) n' && Nat.leb n' 8)%bool then EExt sx (lo' + lo) n e'
             else EExt sx lo n e
         | _ => EExt sx lo n e
         end
  end.

Definition ridx (r : reg) : nat := Z.to_nat (bv_unsigned r).

Definition sr_get (sr : list expr) (r : reg) : expr :=
  if bv_eqb r 0 then ELit 0 else nth (ridx r) sr (ELit 0).

Fixpoint sr_upd (sr : list expr) (n : nat) (e : expr) : list expr :=
  match n with
  | O => match sr with [] => [e] | _ :: t => e :: t end
  | S n' => match sr with
            | [] => ELit 0 :: sr_upd [] n' e
            | h :: t => h :: sr_upd t n' e
            end
  end.

Definition sr_id : list expr :=
  [EVar 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7;
   EVar 8; EVar 9; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15;
   EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23;
   EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].

Record saddr : Type := SA { a_base : expr; a_off : Z }.

Definition split_lit (e : expr) : expr * Z :=
  match e with
  | ELit z => (ELit 0, z)
  | EAlu ALU_ADD b (ELit z) => (b, z)
  | _ => (e, 0%Z)
  end.

Definition to_saddr (e : expr) (imm : Z) : saddr :=
  let (b, k) := split_lit e in SA b (k + imm).

Definition adenot (E : env) (a : saddr) : word :=
  v_addi (edenot E (a_base a)) (a_off a).

Definition saddr_eqb (a b : saddr) : bool :=
  expr_eqb (a_base a) (a_base b) && Z.eqb (a_off a) (a_off b).

Record sentry : Type := SE { e_addr : saddr; e_width : nat; e_val : expr }.

Inductive kentry : Type :=
| KWord (a : saddr) (w : nat) (v : expr)
| KZero (a : saddr) (n : expr)
| KBlob (a : saddr) (n : expr) (k : nat)
| KImg  (lo hi : Z)
| KAlign (e : expr) (m : Z)
| KRange (e : expr) (lo hi : Z)
| KWr (a : saddr) (n : Z)
| KDisj (a1 : saddr) (n1 : Z) (a2 : saddr) (n2 : Z).

Inductive sidecond : Type :=
| SCBr       (taken : bool) (c : branch_cond) (a b : expr)
| SCFlat     (a : saddr) (n : expr)
| SCDisj     (a1 : saddr) (n1 : expr) (a2 : saddr) (n2 : expr)
| SCInside   (a1 : saddr) (n1 : expr) (a2 : saddr) (n2 : expr)
| SCStoreOk  (a : saddr) (n : nat)
| SCReadBase (a : saddr) (n : nat) (sx : bool) (e : expr)
| SCEq       (a b : expr).

Record sym_state : Type := SS {
  s_pc   : Z;
  s_regs : list expr;
  s_log  : list sentry;
  s_know : list kentry;
  s_next : nat
}.

Definition sset (ss : sym_state) (rd : reg) (e : expr) (npc : Z) : sym_state :=
  SS npc (if bv_eqb rd 0 then s_regs ss else sr_upd (s_regs ss) (ridx rd) e)
     (s_log ss) (s_know ss) (s_next ss).

Definition sjump (ss : sym_state) (npc : Z) : sym_state :=
  SS npc (s_regs ss) (s_log ss) (s_know ss) (s_next ss).

Inductive rangerel := RInside (delta : Z) | RDisjoint | RPartial | RUnknown.

Definition rel_lit (rb : expr) (rk : Z) (rn : Z) (kb : expr) (kk : Z) (kn : Z) : rangerel :=
  if expr_eqb rb kb then
    if (Z.leb kk rk && Z.leb (rk + rn) (kk + kn))%bool then RInside (rk - kk)
    else if (Z.leb (rk + rn) kk || Z.leb (kk + kn) rk)%bool then RDisjoint
    else RPartial
  else RUnknown.

Definition elen (n : nat) : expr := ELit (Z.of_nat n).

Fixpoint find_range (kn : list kentry) (e : expr) : option (Z * Z) :=
  match kn with
  | [] => None
  | KRange e' lo hi :: rest => if expr_eqb e e' then Some (lo, hi) else find_range rest e
  | _ :: rest => find_range rest e
  end.

Fixpoint find_align (kn : list kentry) (e : expr) : option Z :=
  match kn with
  | [] => None
  | KAlign e' m :: rest => if expr_eqb e e' then Some m else find_align rest e
  | _ :: rest => find_align rest e
  end.

Definition two64 : Z := 2 ^ 64.

Definition clampi (r : Z * Z) : Z * Z :=
  let (lo, hi) := r in (Z.max lo 0, Z.min hi (two64 - 1)).

Definition mask_cover (h : Z) : Z :=
  if Z.ltb h 0 then 0 else (2 ^ (Z.log2_up (h + 1)) - 1)%Z.

Definition lit_shamt (e : expr) : option Z :=
  match e with ELit s => Some (s mod 64)%Z | _ => None end.

Definition zsigned64 (v : Z) : Z := if Z.leb (2 ^ 63) v then (v - two64)%Z else v.

Fixpoint lin_range (rng : expr -> option (Z * Z)) (c : Z) (ts : list (Z * expr)) : option (Z * Z) :=
  match ts with
  | [] => Some (c, c)
  | (k, a) :: rest =>
      match rng a, lin_range rng c rest with
      | Some (al, ah), Some (lo, hi) =>
          if Z.leb 0 k then Some ((lo + k * al)%Z, (hi + k * ah)%Z)
          else Some ((lo + k * ah)%Z, (hi + k * al)%Z)
      | _, _ => None
      end
  end.

Definition lin_trivial (l : lin) : bool :=
  match l with
  | (c, [(k, _)]) => (Z.eqb c 0 && Z.eqb k 1)%bool
  | _ => false
  end.

Fixpoint erange_f (fuel : nat) (kn : list kentry) (e : expr) {struct fuel} : option (Z * Z) :=
  match fuel with
  | O => None
  | S fuel' =>
  let erange := erange_f fuel' in
  match find_range kn e with
  | Some r => Some (clampi r)
  | None =>
  match (let l := lin_of e in
         if lin_trivial l then None
         else match lin_range (erange kn) (fst l) (snd l) with
              | Some (lo, hi) => if (Z.leb 0 lo && Z.ltb hi two64)%bool then Some (lo, hi) else None
              | None => None
              end) with
  | Some r => Some r
  | None =>
  match e with
  | ELit z => let v := (z mod two64)%Z in Some (v, v)
  | EVar _ => None
  | EAlu op a b =>
      match op with
      | ALU_ADD =>
          match erange kn a, erange kn b with
          | Some (al, ah), Some (bl, bh) =>
              if Z.ltb (ah + bh) two64 then Some ((al + bl)%Z, (ah + bh)%Z)
              else if Z.leb two64 (al + bl) then Some ((al + bl - two64)%Z, (ah + bh - two64)%Z)
              else None
          | _, _ => None
          end
      | ALU_SUB =>
          match erange kn a, erange kn b with
          | Some (al, ah), Some (bl, bh) =>
              if Z.leb bh al then Some ((al - bh)%Z, (ah - bl)%Z)
              else if Z.ltb ah bl then Some ((al - bh + two64)%Z, (ah - bl + two64)%Z)
              else None
          | _, _ => None
          end
      | ALU_AND =>
          match erange kn a, erange kn b with
          | Some (_, ah), Some (_, bh) => Some (0%Z, Z.min ah bh)
          | Some (_, ah), None => Some (0%Z, ah)
          | None, Some (_, bh) => Some (0%Z, bh)
          | None, None => None
          end
      | ALU_OR =>
          match erange kn a, erange kn b with
          | Some (al, ah), Some (bl, bh) => Some (Z.max al bl, mask_cover (Z.max ah bh))
          | _, _ => None
          end
      | ALU_XOR =>
          match erange kn a, erange kn b with
          | Some (_, ah), Some (_, bh) => Some (0%Z, mask_cover (Z.max ah bh))
          | _, _ => None
          end
      | ALU_SRL =>
          match erange kn a, lit_shamt b with
          | Some (al, ah), Some s => Some ((al / 2 ^ s)%Z, (ah / 2 ^ s)%Z)
          | _, _ => None
          end
      | ALU_SRA =>
          match erange kn a, lit_shamt b with
          | Some (al, ah), Some s =>
              if Z.ltb ah (2 ^ 63) then Some ((al / 2 ^ s)%Z, (ah / 2 ^ s)%Z) else None
          | _, _ => None
          end
      | ALU_SLL =>
          match erange kn a, lit_shamt b with
          | Some (al, ah), Some s =>
              if Z.ltb (ah * 2 ^ s) two64 then Some ((al * 2 ^ s)%Z, (ah * 2 ^ s)%Z) else None
          | _, _ => None
          end
      | ALU_SLTU =>
          match erange kn a, erange kn b with
          | Some (al, ah), Some (bl, bh) =>
              if Z.ltb ah bl then Some (1%Z, 1%Z)
              else if Z.leb bh al then Some (0%Z, 0%Z) else Some (0%Z, 1%Z)
          | _, _ => Some (0%Z, 1%Z)
          end
      | ALU_SLT =>
          match erange kn a, erange kn b with
          | Some (al, ah), Some (bl, bh) =>
              if (Z.ltb ah (2 ^ 63) && Z.ltb bh (2 ^ 63))%bool then
                (if Z.ltb ah bl then Some (1%Z, 1%Z)
                 else if Z.leb bh al then Some (0%Z, 0%Z) else Some (0%Z, 1%Z))
              else Some (0%Z, 1%Z)
          | _, _ => Some (0%Z, 1%Z)
          end
      end
  | EAluw op a b =>
      match op with
      | ALU_ADD =>
          match erange kn a, erange kn b with
          | Some (al, ah), Some (bl, bh) =>
              let bl' := if Z.eqb bl bh then zsigned64 bl else bl in
              let bh' := if Z.eqb bl bh then zsigned64 bh else bh in
              if (Z.leb 0 (al + bl') && Z.ltb (ah + bh') (2 ^ 31))%bool
              then Some ((al + bl')%Z, (ah + bh')%Z) else None
          | _, _ => None
          end
      | ALU_SUB =>
          match erange kn a, erange kn b with
          | Some (al, ah), Some (bl, bh) =>
              if (Z.leb bh al && Z.ltb (ah - bl) (2 ^ 31))%bool
              then Some ((al - bh)%Z, (ah - bl)%Z) else None
          | _, _ => None
          end
      | ALU_SLL =>
          match erange kn a, lit_shamt b with
          | Some (al, ah), Some s =>
              let s' := (s mod 32)%Z in
              if Z.ltb (ah * 2 ^ s') (2 ^ 31) then Some ((al * 2 ^ s')%Z, (ah * 2 ^ s')%Z) else None
          | _, _ => None
          end
      | ALU_SRL =>
          match erange kn a, lit_shamt b with
          | Some (al, ah), Some s =>
              let s' := (s mod 32)%Z in
              if (Z.ltb ah (2 ^ 32) && (Z.ltb 0 s' || Z.ltb ah (2 ^ 31)))%bool
              then Some ((al / 2 ^ s')%Z, (ah / 2 ^ s')%Z) else None
          | _, _ => None
          end
      | ALU_SRA =>
          match erange kn a, lit_shamt b with
          | Some (al, ah), Some s =>
              let s' := (s mod 32)%Z in
              if Z.ltb ah (2 ^ 31) then Some ((al / 2 ^ s')%Z, (ah / 2 ^ s')%Z) else None
          | _, _ => None
          end
      | _ => None
      end
  | EMd op a b =>
      match op with
      | M_MUL =>
          match erange kn a, erange kn b with
          | Some (al, ah), Some (bl, bh) =>
              if (Z.leb 0 al && Z.leb 0 bl && Z.ltb (ah * bh) two64)%bool
              then Some ((al * bl)%Z, (ah * bh)%Z) else None
          | _, _ => None
          end
      | M_MULHU =>
          match erange kn a, erange kn b with
          | Some (al, ah), Some (bl, bh) =>
              if (Z.leb 0 al && Z.leb 0 bl)%bool
              then Some ((al * bl / two64)%Z, (ah * bh / two64)%Z) else None
          | _, _ => None
          end
      | M_DIVU =>
          match erange kn a, b with
          | Some (al, ah), ELit d =>
              let d' := (d mod two64)%Z in
              if Z.ltb 0 d' then Some ((al / d')%Z, (ah / d')%Z) else None
          | _, _ => None
          end
      | M_REMU =>
          match erange kn a, b with
          | Some (al, ah), ELit d =>
              let d' := (d mod two64)%Z in
              if Z.ltb 0 d' then Some (0%Z, Z.min ah (d' - 1)) else None
          | _, _ => None
          end
      | _ => None
      end
  | EMdw _ _ _ => None
  | EExt sx lo n a =>
      let w := (2 ^ (8 * Z.of_nat n))%Z in
      if sx then
        match lo, erange kn a with
        | O, Some (al, ah) =>
            if (Z.leb 0 al && Z.ltb ah (w / 2))%bool then Some (al, ah) else None
        | _, _ => None
        end
      else
        match lo, erange kn a with
        | O, Some (al, ah) =>
            if (Z.leb 0 al && Z.ltb ah w)%bool then Some (al, ah) else Some (0%Z, Z.min (w - 1) (two64 - 1))
        | _, _ => Some (0%Z, Z.min (w - 1) (two64 - 1))
        end
  | EBlob sx k i n =>
      if sx then None else Some (0%Z, Z.min (2 ^ (8 * Z.of_nat n) - 1) (two64 - 1))%Z
  end
  end
  end
  end.

Definition erange_fuel : nat := 64%nat.
Global Opaque erange_fuel.
Definition erange (kn : list kentry) (e : expr) : option (Z * Z) := erange_f erange_fuel kn e.

Definition base_range (kn : list kentry) (e : expr) : option (Z * Z) := erange kn e.

Fixpoint ctz_fuel (fuel : nat) (z : Z) : Z :=
  match fuel with
  | O => 0
  | S f => if (Z.eqb (z mod 2) 0)%Z then (1 + ctz_fuel f (z / 2))%Z else 0%Z
  end.
Definition ctz64 (z : Z) : Z := ctz_fuel 64 z.

Fixpoint ealign (kn : list kentry) (e : expr) {struct e} : Z :=
  match find_align kn e with
  | Some m => if Z.ltb 0 m then ctz64 m else 0%Z
  | None =>
  match e with
  | ELit z => ctz64 (z mod two64)
  | EAlu ALU_ADD a b => Z.min (ealign kn a) (ealign kn b)
  | EAlu ALU_SUB a b => Z.min (ealign kn a) (ealign kn b)
  | EAlu ALU_AND a b => Z.max (ealign kn a) (ealign kn b)
  | EAlu ALU_OR a b => Z.min (ealign kn a) (ealign kn b)
  | EAlu ALU_SLL a b =>
      match lit_shamt b with
      | Some s => Z.min (ealign kn a + s)%Z 64
      | None => 0%Z
      end
  | EMd M_MUL a b => Z.min (ealign kn a + ealign kn b)%Z 64
  | _ => 0%Z
  end
  end.

Definition sub_itv (b : expr) (k n : Z) (c : saddr) (m : Z) : bool :=
  (expr_eqb b (a_base c) && Z.leb (a_off c) k && Z.leb (k + n) (a_off c + m))%bool.

Fixpoint kdisj_apart (kn : list kentry) (b1 : expr) (k1 n1 : Z) (b2 : expr) (k2 n2 : Z) : bool :=
  match kn with
  | [] => false
  | KDisj c1 m1 c2 m2 :: rest =>
      ((sub_itv b1 k1 n1 c1 m1 && sub_itv b2 k2 n2 c2 m2)
       || (sub_itv b1 k1 n1 c2 m2 && sub_itv b2 k2 n2 c1 m1)
       || kdisj_apart rest b1 k1 n1 b2 k2 n2)%bool
  | _ :: rest => kdisj_apart rest b1 k1 n1 b2 k2 n2
  end.

Definition ranges_apart (kn : list kentry) (b1 : expr) (k1 n1 : Z) (b2 : expr) (k2 n2 : Z) : bool :=
  (match base_range kn b1, base_range kn b2 with
   | Some (lo1, hi1), Some (lo2, hi2) =>
       (Z.leb (hi1 + k1 + n1) (lo2 + k2) || Z.leb (hi2 + k2 + n2) (lo1 + k1))%bool
   | _, _ => false
   end) || kdisj_apart kn b1 k1 n1 b2 k2 n2.

Inductive lres :=
| LHit (v : expr) (scs : list sidecond) (hints : list bool)
| LMiss (scs : list sidecond) (hints : list bool)
| LStuck.

Fixpoint log_lookup (kn : list kentry) (log : list sentry) (rb : expr) (rk : Z) (n : nat) (sx : bool)
         (hints : list bool) (acc : list sidecond) : lres :=
  match log with
  | [] => LMiss acc hints
  | SE (SA kb kk) w v :: rest =>
      match rel_lit rb rk (Z.of_nat n) kb kk (Z.of_nat w) with
      | RInside d => LHit (mkExt sx (Z.to_nat d) n v) acc hints
      | RDisjoint => log_lookup kn rest rb rk n sx hints acc
      | RPartial => LStuck
      | RUnknown =>
          if ranges_apart kn rb rk (Z.of_nat n) kb kk (Z.of_nat w)
          then log_lookup kn rest rb rk n sx hints acc
          else
          match hints with
          | false :: _ => LStuck
          | _ => log_lookup kn rest rb rk n sx (tl hints)
                   (SCDisj (SA rb rk) (elen n) (SA kb kk) (elen w) :: acc)
          end
      end
  end.

Fixpoint img_bytes (segs : list Segment) (a : Z) (n : nat) : option (list Z) :=
  match n with
  | O => Some []
  | S n' =>
      match seg_rom segs (Z_to_bv 64 a) with
      | Some b => match img_bytes segs (a + 1) n' with
                  | Some r => Some (bv_unsigned b :: r)
                  | None => None
                  end
      | None => None
      end
  end.

Fixpoint zbytes_le_to_Z (bs : list Z) : Z :=
  match bs with
  | [] => 0
  | b :: rest => Z.lor b (Z.shiftl (zbytes_le_to_Z rest) 8)
  end.

Definition lit_of_bytes (sx : bool) (n : nat) (bs : list Z) : expr :=
  ELit (let u := zbytes_le_to_Z bs in if sx then bv_swrap (8 * N.of_nat n) u else u).

Fixpoint know_lookup (segs : list Segment) (kn : list kentry) (rb : expr) (rk : Z)
         (n : nat) (sx : bool) (hints : list bool) (acc : list sidecond) : lres :=
  match kn with
  | [] => LMiss acc hints
  | K :: rest =>
      match K with
      | KWord (SA kb kk) w v =>
          match rel_lit rb rk (Z.of_nat n) kb kk (Z.of_nat w) with
          | RInside d => LHit (mkExt sx (Z.to_nat d) n v) acc hints
          | _ => know_lookup segs rest rb rk n sx hints acc
          end
      | KZero (SA kb kk) len =>
          match len with
          | ELit l0 =>
              match rel_lit rb rk (Z.of_nat n) kb kk (l0 mod 2^64)%Z with
              | RInside _ => LHit (ELit 0) acc hints
              | RDisjoint | RPartial => know_lookup segs rest rb rk n sx hints acc
              | RUnknown =>
                  match hints with
                  | true :: hs => LHit (ELit 0) (SCInside (SA rb rk) (elen n) (SA kb kk) len :: acc) hs
                  | false :: hs => know_lookup segs rest rb rk n sx hs acc
                  | [] => know_lookup segs rest rb rk n sx [] acc
                  end
              end
          | _ =>
              match hints with
              | true :: hs => LHit (ELit 0) (SCInside (SA rb rk) (elen n) (SA kb kk) len :: acc) hs
              | false :: hs => know_lookup segs rest rb rk n sx hs acc
              | [] => know_lookup segs rest rb rk n sx [] acc
              end
          end
      | KBlob (SA kb kk) len k =>
          if expr_eqb rb kb then

            if Z.leb kk rk then
              match len with
              | ELit l0 =>
                  if Z.leb (rk + Z.of_nat n) (kk + (l0 mod 2^64)%Z)
                  then LHit (EBlob sx k (rk - kk) n) acc hints
                  else if Z.leb (kk + (l0 mod 2^64)%Z) rk then know_lookup segs rest rb rk n sx hints acc
                  else LStuck
              | _ =>
                  match hints with
                  | true :: hs => LHit (EBlob sx k (rk - kk) n)
                                    (SCInside (SA rb rk) (elen n) (SA kb kk) len :: acc) hs
                  | false :: hs => know_lookup segs rest rb rk n sx hs acc
                  | [] => know_lookup segs rest rb rk n sx [] acc
                  end
              end
            else know_lookup segs rest rb rk n sx hints acc
          else know_lookup segs rest rb rk n sx hints acc
      | KImg lo hi =>
          match rb with
          | ELit 0 =>
              if (Z.leb lo rk && Z.leb (rk + Z.of_nat n) hi)%bool then
                match img_bytes segs rk n with
                | Some bs => LHit (lit_of_bytes sx n bs) acc hints
                | None => LStuck
                end
              else know_lookup segs rest rb rk n sx hints acc
          | _ => know_lookup segs rest rb rk n sx hints acc
          end
      | KAlign _ _ => know_lookup segs rest rb rk n sx hints acc
      | KRange _ _ _ => know_lookup segs rest rb rk n sx hints acc
      | KWr _ _ => know_lookup segs rest rb rk n sx hints acc
      | KDisj _ _ _ _ => know_lookup segs rest rb rk n sx hints acc
      end
  end.

Definition mkAnd (kn : list kentry) (a b : expr) : expr :=
  match b with
  | ELit k =>
      let k' := (k mod two64)%Z in
      let j := Z.log2 (two64 - k') in
      if (Z.eqb (two64 - k') (2 ^ j) && Z.ltb j 64)%bool then

        (if Z.leb j (ealign kn a) then a
         else let l := lin_of a in
              if coeffs_div (2 ^ j) (snd l) then unlin ((fst l - (fst l) mod 2 ^ j)%Z, snd l)
              else mkAlu ALU_AND a b)
      else
        let j2 := Z.log2 (k' + 1) in
        if (Z.eqb (k' + 1) (2 ^ j2) && Z.ltb j2 64)%bool then

          (if Z.leb j2 (ealign kn a) then ELit 0
           else match lin_lowbits a j2 with
                | Some v => ELit v
                | None => mkAlu ALU_AND a b
                end)
        else mkAlu ALU_AND a b
  | _ => mkAlu ALU_AND a b
  end.

Definition or_disjoint (kn : list kentry) (a b : expr) : bool :=
  match erange kn b with
  | Some (lo, hi) => (Z.leb 0 lo && Z.ltb hi (2 ^ (ealign kn a)))%bool
  | None => false
  end.

Definition mkOr (kn : list kentry) (a b : expr) : expr :=
  match is_lit a, is_lit b with
  | Some x, Some y => ELit (zalu ALU_OR x y)
  | _, _ =>
      if or_disjoint kn a b then mkAlu ALU_ADD a b
      else if or_disjoint kn b a then mkAlu ALU_ADD a b
      else EAlu ALU_OR a b
  end.

Fixpoint ldiv_terms (m : Z) (ts : list (Z * expr)) : list (Z * expr) :=
  match ts with
  | [] => []
  | (k, a) :: rest => ((k / m)%Z, a) :: ldiv_terms m rest
  end.

Definition lin_nowrap (kn : list kentry) (e : expr) : bool :=
  let l := lin_of e in
  match lin_range (erange kn) (fst l) (snd l) with
  | Some (lo, hi) => (Z.leb 0 lo && Z.ltb hi two64)%bool
  | None => false
  end.

Definition mkSrl (kn : list kentry) (a : expr) (s : Z) : expr :=
  let l := lin_of a in
  let m := (2 ^ s)%Z in
  if (negb (lin_trivial l) && coeffs_div m (snd l) && Z.leb 0 (fst l) && Z.ltb (fst l) m && lin_nowrap kn a)%bool
  then unlin (0%Z, ldiv_terms m (snd l))
  else mkAlu ALU_SRL a (ELit s).

Definition mkAluK (kn : list kentry) (op : aluop) (a b : expr) : expr :=
  match op with
  | ALU_AND => match a, b with
               | ELit _, ELit _ => mkAnd kn a b
               | ELit _, _ => mkAnd kn b a
               | _, _ => mkAnd kn a b
               end
  | ALU_OR => mkOr kn a b
  | ALU_SRL => match is_lit a, shamt_of b 6 with
               | None, Some s => mkSrl kn a s
               | _, _ => mkAlu op a b
               end
  | _ => mkAlu op a b
  end.

Definition msize_bytes (sz : msize) : nat :=
  match sz with SZ1 => 1 | SZ2 => 2 | SZ4 => 4 | SZ8 => 8 end.

Definition flat_sc (kn : list kentry) (a : saddr) (n : nat) : list sidecond :=
  match base_range kn (a_base a) with
  | Some (lo, hi) =>
      if (Z.leb 0 (lo + a_off a) && Z.leb (hi + a_off a + Z.of_nat n) (2 ^ 64))%bool
      then [] else [SCFlat a (elen n)]
  | None => [SCFlat a (elen n)]
  end.

Fixpoint wr_covered (kn : list kentry) (a : saddr) (n : nat) : bool :=
  match kn with
  | [] => false
  | KWr (SA kb kk) len :: rest =>
      if (expr_eqb (a_base a) kb && Z.leb kk (a_off a) && Z.leb (a_off a + Z.of_nat n) (kk + len))%bool
      then true else wr_covered rest a n
  | _ :: rest => wr_covered rest a n
  end.

Definition storeok_sc (kn : list kentry) (a : saddr) (n : nat) : list sidecond :=
  if wr_covered kn a n then [] else [SCStoreOk a n].

Record scripts : Type := SCR {
  sc_dirs  : list bool;
  sc_reads : list expr;
  sc_hints : list bool
}.

Inductive stepres :=
| SOk (ss : sym_state) (scs : list sidecond) (scr : scripts)
| SStop.

Definition lit_branch (c : branch_cond) (x y : Z) : bool :=
  branch_taken c (Z_to_bv 64 x) (Z_to_bv 64 y).

Definition cond_on_eq (c : branch_cond) : bool :=
  match c with
  | BC_EQ => true | BC_NE => false | BC_LT => false | BC_GE => true
  | BC_LTU => false | BC_GEU => true
  end.

Definition itv_ltu (al ah bl bh : Z) : option bool :=
  if Z.ltb ah bl then Some true else if Z.leb bh al then Some false else None.

Definition itv_lts (al ah bl bh : Z) : option bool :=
  let h := (2 ^ 63)%Z in
  if ((Z.ltb ah h && Z.ltb bh h) || (Z.leb h al && Z.leb h bl))%bool then itv_ltu al ah bl bh
  else if (Z.leb h al && Z.ltb bh h)%bool then Some true
  else if (Z.ltb ah h && Z.leb h bl)%bool then Some false
  else None.

Definition range_branch (c : branch_cond) (al ah bl bh : Z) : option bool :=
  match c with
  | BC_EQ =>
      if (Z.ltb ah bl || Z.ltb bh al)%bool then Some false
      else if (Z.eqb al ah && Z.eqb bl bh && Z.eqb al bl)%bool then Some true else None
  | BC_NE =>
      if (Z.ltb ah bl || Z.ltb bh al)%bool then Some true
      else if (Z.eqb al ah && Z.eqb bl bh && Z.eqb al bl)%bool then Some false else None
  | BC_LTU => itv_ltu al ah bl bh
  | BC_GEU => option_map negb (itv_ltu al ah bl bh)
  | BC_LT => itv_lts al ah bl bh
  | BC_GE => option_map negb (itv_lts al ah bl bh)
  end.

Definition decide_branch (kn : list kentry) (c : branch_cond) (a b : expr) : option bool :=
  match a, b with
  | ELit x, ELit y => Some (lit_branch c x y)
  | _, _ =>
      if expr_eqb a b then Some (cond_on_eq c)
      else match erange kn a, erange kn b with
           | Some (al, ah), Some (bl, bh) => range_branch c al ah bl bh
           | _, _ => None
           end
  end.

Fixpoint closedb (e : expr) : bool :=
  match e with
  | ELit _ => true
  | EVar _ => false
  | EAlu _ a b | EAluw _ a b | EMd _ a b | EMdw _ a b => closedb a && closedb b
  | EExt _ _ _ a => closedb a
  | EBlob _ _ _ _ => false
  end.

Fixpoint esubst (s r e : expr) : expr :=
  if expr_eqb e s then r else
  match e with
  | EAlu op a b => EAlu op (esubst s r a) (esubst s r b)
  | EAluw op a b => EAluw op (esubst s r a) (esubst s r b)
  | EMd op a b => EMd op (esubst s r a) (esubst s r b)
  | EMdw op a b => EMdw op (esubst s r a) (esubst s r b)
  | EExt sx lo n a => EExt sx lo n (esubst s r a)
  | _ => e
  end.

Fixpoint eval_closed (e : expr) : option Z :=
  match e with
  | ELit z => Some (z mod two64)%Z
  | EVar _ => None
  | EAlu op a b => match eval_closed a, eval_closed b with
                   | Some x, Some y => Some (zalu op x y) | _, _ => None end
  | EAluw op a b => match eval_closed a, eval_closed b with
                    | Some x, Some y => Some (zaluw op x y) | _, _ => None end
  | EMd op a b => match eval_closed a, eval_closed b with
                  | Some x, Some y => Some (zmd op x y) | _, _ => None end
  | EMdw op a b => match eval_closed a, eval_closed b with
                   | Some x, Some y => Some (zmdw op x y) | _, _ => None end
  | EExt sx lo n a => match eval_closed a with
                      | Some x => Some (zext_lit sx lo n x) | None => None end
  | EBlob _ _ _ _ => None
  end.

Fixpoint subexprs (e : expr) : list expr :=
  match e with
  | EAlu _ a b | EAluw _ a b | EMd _ a b | EMdw _ a b => subexprs a ++ subexprs b ++ [e]
  | EExt _ _ _ a => subexprs a ++ [e]
  | _ => [e]
  end.

Fixpoint all_eval_to (s e : expr) (v lo : Z) (cnt : nat) : bool :=
  match cnt with
  | O => true
  | S c => match eval_closed (esubst s (ELit lo) e) with
           | Some w => Z.eqb w v && all_eval_to s e v (lo + 1) c
           | None => false
           end
  end.

Definition conc_limit : Z := 4096.

Fixpoint conc_try (kn : list kentry) (e : expr) (cands : list expr) : option Z :=
  match cands with
  | [] => None
  | s :: rest =>
      if closedb s then conc_try kn e rest else
      match erange kn s with
      | Some (lo, hi) =>
          if Z.leb (hi - lo) conc_limit then
            match eval_closed (esubst s (ELit lo) e) with
            | Some v => if all_eval_to s e v lo (Z.to_nat (hi - lo + 1)) then Some v
                        else conc_try kn e rest
            | None => conc_try kn e rest
            end
          else conc_try kn e rest
      | None => conc_try kn e rest
      end
  end.

Definition concretize (kn : list kentry) (e : expr) : option Z :=
  if closedb e then eval_closed e else conc_try kn e (subexprs e).

Definition conc_expr (kn : list kentry) (e : expr) : expr :=
  match e with
  | ELit _ => e
  | _ => match concretize kn e with Some v => ELit v | None => e end
  end.

Definition to_saddrK (kn : list kentry) (e : expr) (imm : Z) : saddr :=
  match split_lit e with
  | (ELit _, _) => to_saddr e imm
  | _ => match concretize kn (mkAlu ALU_ADD e (ELit imm)) with
         | Some v => SA (ELit 0) v
         | None => to_saddr e imm
         end
  end.

Definition sym_step (segs : list Segment) (i : instr) (ss : sym_state) (scr : scripts) : stepres :=
  let g r := sr_get (s_regs ss) r in
  let p := s_pc ss in
  match i with
  | OpImm op rd rs imm => SOk (sset ss rd (mkAluK (s_know ss) op (g rs) (ELit (bv_signed imm))) (p + 4)) [] scr
  | ShiftImm op rd rs sh => SOk (sset ss rd (mkAluK (s_know ss) op (g rs) (ELit (bv_unsigned sh))) (p + 4)) [] scr
  | Op op rd rs1 rs2 => SOk (sset ss rd (mkAluK (s_know ss) op (g rs1) (g rs2)) (p + 4)) [] scr
  | OpImm32 rd rs imm => SOk (sset ss rd (mkAluw ALU_ADD (g rs) (ELit (bv_signed imm))) (p + 4)) [] scr
  | ShiftImm32 op rd rs sh => SOk (sset ss rd (mkAluw op (g rs) (ELit (bv_unsigned sh))) (p + 4)) [] scr
  | Op32 op rd rs1 rs2 => SOk (sset ss rd (mkAluw op (g rs1) (g rs2)) (p + 4)) [] scr
  | Mul op rd rs1 rs2 => SOk (sset ss rd (mkMd op (g rs1) (g rs2)) (p + 4)) [] scr
  | Mul32 op rd rs1 rs2 => SOk (sset ss rd (mkMdw op (g rs1) (g rs2)) (p + 4)) [] scr
  | Lui rd imm => SOk (sset ss rd (ELit (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_signed imm) 12)))) (p + 4)) [] scr
  | Auipc rd imm => SOk (sset ss rd (ELit (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_signed imm) 12 + p)))) (p + 4)) [] scr
  | Jal rd imm => SOk (sset ss rd (ELit (p + 4)) (bv_unsigned (Z_to_bv 64 (p + bv_signed imm)))) [] scr
  | Jalr rd rs1 imm =>
      match conc_expr (s_know ss) (g rs1) with
      | ELit z => SOk (sset ss rd (ELit (p + 4)) (Z.land (bv_wrap 64 z + bv_signed imm) (-2) mod 2^64)) [] scr
      | _ => SStop
      end
  | Branch c rs1 rs2 imm =>
      let tk := bv_unsigned (Z_to_bv 64 (p + bv_signed imm)) in
      let a := g rs1 in let b := g rs2 in
      match match decide_branch (s_know ss) c a b with
            | Some t => Some t
            | None => decide_branch (s_know ss) c (conc_expr (s_know ss) a) (conc_expr (s_know ss) b)
            end with
      | Some t => SOk (sjump ss (if t then tk else p + 4)) [] scr
      | None =>
          match sc_dirs scr with
          | [] => SStop
          | t :: dirs' =>
              SOk (sjump ss (if t then tk else p + 4)) [SCBr t c a b]
                  (SCR dirs' (sc_reads scr) (sc_hints scr))
          end
      end
  | Fence _ _ _ _ _ => SOk (sjump ss (p + 4)) [] scr
  | FenceI _ _ _ => SOk (sjump ss (p + 4)) [] scr
  | Load sz sx rd rs imm =>
      let n := msize_bytes sz in

      let sx' := match sz with SZ8 => false | _ => sx end in
      let a := to_saddrK (s_know ss) (g rs) (bv_signed imm) in
      let fin v scs hints :=
        SOk (sset ss rd v (p + 4)) (flat_sc (s_know ss) a n ++ scs)
            (SCR (sc_dirs scr) (sc_reads scr) hints) in
      match log_lookup (s_know ss) (s_log ss) (a_base a) (a_off a) n sx' (sc_hints scr) [] with
      | LStuck => SStop
      | LHit v scs hints => fin v scs hints
      | LMiss scs hints =>
          match know_lookup segs (s_know ss) (a_base a) (a_off a) n sx' hints scs with
          | LStuck => SStop
          | LHit v scs' hints' => fin v scs' hints'
          | LMiss scs' hints' =>

              let i := s_next ss in
              let rv := match sc_reads scr with [] => EVar i | e :: _ => e end in
              let reads' := match sc_reads scr with [] => [] | _ :: t => t end in
              SOk (SS (p + 4)
                      (if bv_eqb rd 0 then s_regs ss else sr_upd (s_regs ss) (ridx rd) rv)
                      (s_log ss) (s_know ss) (S i))
                  (flat_sc (s_know ss) a n ++ SCReadBase a n sx' rv :: scs')
                  (SCR (sc_dirs scr) reads' hints')
          end
      end
  | Store sz rs1 rs2 imm =>
      let n := msize_bytes sz in
      let a := to_saddrK (s_know ss) (g rs1) (bv_signed imm) in
      SOk (SS (p + 4) (s_regs ss) (SE a n (g rs2) :: s_log ss) (s_know ss) (s_next ss))
          (flat_sc (s_know ss) a n ++ storeok_sc (s_know ss) a n) scr
  | _ => SStop
  end.

Definition sidecond_eqb (x y : sidecond) : bool :=
  match x, y with
  | SCFlat a n, SCFlat a' n' => saddr_eqb a a' && expr_eqb n n'
  | SCStoreOk a n, SCStoreOk a' n' => saddr_eqb a a' && Nat.eqb n n'
  | SCDisj a n b m, SCDisj a' n' b' m' =>
      saddr_eqb a a' && expr_eqb n n' && saddr_eqb b b' && expr_eqb m m'
  | SCInside a n b m, SCInside a' n' b' m' =>
      saddr_eqb a a' && expr_eqb n n' && saddr_eqb b b' && expr_eqb m m'
  | _, _ => false
  end.

Fixpoint sc_mem (x : sidecond) (l : list sidecond) : bool :=
  match l with [] => false | y :: t => sidecond_eqb x y || sc_mem x t end.

Fixpoint sc_add (news acc : list sidecond) : list sidecond :=
  match news with
  | [] => acc
  | x :: t => sc_add t (if sc_mem x acc then acc else x :: acc)
  end.

Section WithSegs.
Variable segs : list Segment.

Fixpoint sym_exec (fuel : nat) (first : bool) (stops : list Z) (scr : scripts)
                  (ss : sym_state) (acc : list sidecond)
  : sym_state * list sidecond * scripts :=
  match fuel with
  | O => (ss, acc, scr)
  | S f =>
      if (negb first && existsb (Z.eqb (s_pc ss)) stops)%bool then (ss, acc, scr) else
      match fetch_word segs (Z_to_bv 64 (s_pc ss)) with
      | None => (ss, acc, scr)
      | Some w =>
          if is_ecall w then (ss, acc, scr) else
          match decode_any w with
          | None => (ss, acc, scr)
          | Some (i, sz) =>
              if negb (Z.eqb sz 4) then (ss, acc, scr) else
              match sym_step segs i ss scr with
              | SOk ss' scs scr' => sym_exec f false stops scr' ss' (sc_add scs acc)
              | SStop => (ss, acc, scr)
              end
          end
      end
  end.

End WithSegs.

Definition prune1 (allkn : list kentry) (wa : saddr) (w : nat) (K : kentry) (hints : list bool)
  : list kentry * list sidecond * list bool :=
  let k := a_off wa in
  let diffbase (ka : saddr) (kl : expr) :=
    let apart := match kl with
                 | ELit l => ranges_apart allkn (a_base wa) k (Z.of_nat w) (a_base ka) (a_off ka) (l mod 2 ^ 64)%Z
                 | _ => false
                 end in
    if apart then ([K], [], hints) else
    match hints with
    | true :: hs => ([K], [SCDisj wa (elen w) ka kl], hs)
    | false :: hs => ([], [], hs)
    | [] => ([], [], [])
    end in
  match K with
  | KAlign _ _ => ([K], [], hints)
  | KRange _ _ _ => ([K], [], hints)
  | KWr _ _ => ([K], [], hints)
  | KDisj _ _ _ _ => ([K], [], hints)
  | KImg lo hi =>
      match a_base wa with
      | ELit 0 =>
          let r1 := if Z.ltb lo (Z.min k hi) then [KImg lo (Z.min k hi)] else [] in
          let lo2 := Z.max lo (k + Z.of_nat w) in
          let r2 := if Z.ltb lo2 hi then [KImg lo2 hi] else [] in
          (r1 ++ r2, [], hints)
      | _ => if Z.ltb (hi - lo) (2 ^ 64) then diffbase (SA (ELit 0) lo) (ELit (hi - lo))
             else ([], [], hints)
      end
  | KZero (SA kb kk) len =>
      if expr_eqb kb (a_base wa) then
        match len with
        | ELit l0 =>
            let l := (l0 mod 2 ^ 64)%Z in
            let hi1 := Z.min k (kk + l) in
            let r1 := if Z.ltb kk hi1 then [KZero (SA kb kk) (ELit (hi1 - kk))] else [] in
            let lo2 := Z.max kk (k + Z.of_nat w) in
            let r2 := if Z.ltb lo2 (kk + l) then [KZero (SA kb lo2) (ELit (kk + l - lo2))] else [] in
            (r1 ++ r2, [], hints)
        | _ => if Z.leb (k + Z.of_nat w) kk then ([K], [], hints) else ([], [], hints)
        end
      else diffbase (SA kb kk) len
  | KWord (SA kb kk) w' v =>
      if expr_eqb kb (a_base wa) then
        (if (Z.leb (kk + Z.of_nat w') k || Z.leb (k + Z.of_nat w) kk)%bool
         then ([K], [], hints) else ([], [], hints))
      else diffbase (SA kb kk) (elen w')
  | KBlob (SA kb kk) len bk =>
      if expr_eqb kb (a_base wa) then
        match len with
        | ELit l0 =>
            let l := (l0 mod 2 ^ 64)%Z in
            (if (Z.leb (kk + l) k || Z.leb (k + Z.of_nat w) kk)%bool
             then ([K], [], hints) else ([], [], hints))
        | _ => if Z.leb (k + Z.of_nat w) kk then ([K], [], hints) else ([], [], hints)
        end
      else diffbase (SA kb kk) len
  end.

Fixpoint prune (allkn : list kentry) (wa : saddr) (w : nat) (kn : list kentry) (hints : list bool)
  : list kentry * list sidecond * list bool :=
  match kn with
  | [] => ([], [], hints)
  | K :: rest =>
      let '(kept, scs1, hs1) := prune1 allkn wa w K hints in
      let '(r, scs2, hs2) := prune allkn wa w rest hs1 in
      (kept ++ r, scs1 ++ scs2, hs2)
  end.

Fixpoint carry (log : list sentry) (kn : list kentry) (hints : list bool)
  : list kentry * list sidecond * list bool :=
  match log with
  | [] => (kn, [], hints)
  | SE a w v :: older =>
      let '(kn1, scs1, hs1) := carry older kn hints in
      let '(kn2, scs2, hs2) := prune kn1 a w kn1 hs1 in
      (KWord a w v :: kn2, scs1 ++ scs2, hs2)
  end.

End SX2.
