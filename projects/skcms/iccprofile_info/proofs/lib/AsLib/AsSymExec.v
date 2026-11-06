(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.Riscv Require Import Fpu.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import PropExec CatExec CatSim SeqExec StoreOk SymExec PropExecFP.
Unset Lia Cache. Unset Nia Cache.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.

Module ASX.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Inductive fop1 : Type :=
| FO_BoxS                                          (* [comment removed for export] *)
| FO_Sqrt (fmt : ffmt) (md : rmode)
| FO_Class (fmt : ffmt)                            (* [comment removed for export] *)
| FO_CvtFF (sf df : ffmt) (md : rmode)
| FO_CvtFI (sf : ffmt) (sgn : bool) (bits : Z) (md : rmode)   (* [comment removed for export] *)
| FO_CvtIF (df : ffmt) (sgn : bool) (bits : Z) (md : rmode).
Inductive fop2 : Type :=
| FO_Sgnj (op : fsgnop) (fmt : ffmt)
| FO_Ari (op : fariop) (fmt : ffmt) (md : rmode)
| FO_Minmax (op : fminmaxop) (fmt : ffmt)
| FO_Cmp (op : fcmpop) (fmt : ffmt).              (* [comment removed for export] *)
Inductive fop3 : Type :=
| FO_Ma (op : fmaop) (fmt : ffmt) (md : rmode).

Definition fop1_denot (o : fop1) (x : word) : word :=
  match o with
  | FO_BoxS => fmv_fx_res FMT_S x
  | FO_Sqrt fmt md => fsqrt_res fmt md x
  | FO_Class fmt => fclass_res fmt x
  | FO_CvtFF sf df md => fcvt_ff_res sf df md x
  | FO_CvtFI sf sgn bits md => fcvt_fi_res sf sgn bits md x
  | FO_CvtIF df sgn bits md => fcvt_if_res df sgn bits md x
  end.
Definition fop2_denot (o : fop2) (x y : word) : word :=
  match o with
  | FO_Sgnj op fmt => fsgnj_res op fmt x y
  | FO_Ari op fmt md => fari_res op fmt md x y
  | FO_Minmax op fmt => fminmax_res op fmt x y
  | FO_Cmp op fmt => fcmp_res op fmt x y
  end.
Definition fop3_denot (o : fop3) (x y z : word) : word :=
  match o with
  | FO_Ma op fmt md => fma_res op fmt md x y z
  end.

Inductive expr : Type :=
| ELit  (z : Z)                              (* [comment removed for export] *)
| EVar  (n : nat)                            (* [comment removed for export] *)
| EAlu  (op : aluop) (a b : expr)            (* [comment removed for export] *)
| EAluw (op : aluop) (a b : expr)            (* [comment removed for export] *)
| EMd   (op : mulop) (a b : expr)            (* [comment removed for export] *)
| EMdw  (op : mulop) (a b : expr)            (* [comment removed for export] *)
| EExt  (sx : bool) (lo n : nat) (e : expr)  (* [comment removed for export] *)
| EBlob (sx : bool) (k : nat) (i : Z) (n : nat)
                                             (* [comment removed for export] *)
| EFop1 (o : fop1) (a : expr)                (* [comment removed for export] *)
| EFop2 (o : fop2) (a b : expr)
| EFop3 (o : fop3) (a b c : expr)
| EBlobX (sx : bool) (k : nat) (rb : expr) (d : Z) (kb : expr) (n : nat)
                                             (* [comment removed for export] *)
(* [comment removed for export] *)
| EShad (x d n : expr)                       (* [comment removed for export] *)
| ESel (c a b : expr).                       (* [comment removed for export] *)

(* [comment removed for export] *)
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

(* [comment removed for export] *)
Definition shad_byte (x d n : Z) : Z :=
  if Z.leb ((x / 8 + 1) * 8) (d + n) then 0 else ((d + n) mod 8).

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
  | EFop1 o a => fop1_denot o (edenot E a)
  | EFop2 o a b => fop2_denot o (edenot E a) (edenot E b)
  | EFop3 o a b c => fop3_denot o (edenot E a) (edenot E b) (edenot E c)
  | EBlobX sx k rb d kb n =>
      blob_val sx (eb E k) (bv_unsigned (edenot E rb) + d - bv_unsigned (edenot E kb)) n
  | EShad x d n => Z_to_bv 64 (shad_byte (bv_unsigned (edenot E x)) (bv_unsigned (edenot E d)) (bv_unsigned (edenot E n)))
  | ESel c a b => if Z.eqb (bv_unsigned (edenot E c)) 0 then edenot E a else edenot E b
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

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

Definition ffmt_eqb (a b : ffmt) : bool :=
  match a, b with FMT_S, FMT_S | FMT_D, FMT_D => true | _, _ => false end.
Definition rmode_eqb (a b : rmode) : bool :=
  match a, b with
  | RNE, RNE | RTZ, RTZ | RDN, RDN | RUP, RUP | RMM, RMM => true
  | _, _ => false
  end.
Definition fariop_eqb (a b : fariop) : bool :=
  match a, b with
  | F_ADD, F_ADD | F_SUB, F_SUB | F_MUL, F_MUL | F_DIV, F_DIV => true
  | _, _ => false
  end.
Definition fmaop_eqb (a b : fmaop) : bool :=
  match a, b with
  | F_MADD, F_MADD | F_MSUB, F_MSUB | F_NMSUB, F_NMSUB | F_NMADD, F_NMADD => true
  | _, _ => false
  end.
Definition fsgnop_eqb (a b : fsgnop) : bool :=
  match a, b with
  | F_SGNJ, F_SGNJ | F_SGNJN, F_SGNJN | F_SGNJX, F_SGNJX => true
  | _, _ => false
  end.
Definition fminmaxop_eqb (a b : fminmaxop) : bool :=
  match a, b with F_MIN, F_MIN | F_MAX, F_MAX => true | _, _ => false end.
Definition fcmpop_eqb (a b : fcmpop) : bool :=
  match a, b with F_EQ, F_EQ | F_LT, F_LT | F_LE, F_LE => true | _, _ => false end.

Definition fop1_eqb (a b : fop1) : bool :=
  match a, b with
  | FO_BoxS, FO_BoxS => true
  | FO_Sqrt f m, FO_Sqrt f' m' => ffmt_eqb f f' && rmode_eqb m m'
  | FO_Class f, FO_Class f' => ffmt_eqb f f'
  | FO_CvtFF s d m, FO_CvtFF s' d' m' => ffmt_eqb s s' && ffmt_eqb d d' && rmode_eqb m m'
  | FO_CvtFI s g b m, FO_CvtFI s' g' b' m' => ffmt_eqb s s' && Bool.eqb g g' && Z.eqb b b' && rmode_eqb m m'
  | FO_CvtIF d g b m, FO_CvtIF d' g' b' m' => ffmt_eqb d d' && Bool.eqb g g' && Z.eqb b b' && rmode_eqb m m'
  | _, _ => false
  end.
Definition fop2_eqb (a b : fop2) : bool :=
  match a, b with
  | FO_Sgnj o f, FO_Sgnj o' f' => fsgnop_eqb o o' && ffmt_eqb f f'
  | FO_Ari o f m, FO_Ari o' f' m' => fariop_eqb o o' && ffmt_eqb f f' && rmode_eqb m m'
  | FO_Minmax o f, FO_Minmax o' f' => fminmaxop_eqb o o' && ffmt_eqb f f'
  | FO_Cmp o f, FO_Cmp o' f' => fcmpop_eqb o o' && ffmt_eqb f f'
  | _, _ => false
  end.
Definition fop3_eqb (a b : fop3) : bool :=
  match a, b with
  | FO_Ma o f m, FO_Ma o' f' m' => fmaop_eqb o o' && ffmt_eqb f f' && rmode_eqb m m'
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
  | EFop1 o a, EFop1 o' a' => fop1_eqb o o' && expr_eqb a a'
  | EFop2 o a b, EFop2 o' a' b' => fop2_eqb o o' && expr_eqb a a' && expr_eqb b b'
  | EFop3 o a b c, EFop3 o' a' b' c' => fop3_eqb o o' && expr_eqb a a' && expr_eqb b b' && expr_eqb c c'
  | EBlobX s k r d b n, EBlobX s' k' r' d' b' n' =>
      Bool.eqb s s' && Nat.eqb k k' && expr_eqb r r' && Z.eqb d d' && expr_eqb b b' && Nat.eqb n n'
  | EShad x d n, EShad x' d' n' => expr_eqb x x' && expr_eqb d d' && expr_eqb n n'
  | ESel c a b, ESel c' a' b' => expr_eqb c c' && expr_eqb a a' && expr_eqb b b'
  | _, _ => false
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
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

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

Definition two64z : Z := 2 ^ 64.
Definition snorm (k : Z) : Z :=
  let m := (k mod two64z)%Z in if Z.leb (2 ^ 63) m then (m - two64z)%Z else m.

Definition lin : Type := (Z * list (Z * expr))%type.

Definition bool_ix (b : bool) : nat := if b then 1 else 0.
Definition ctor_ix (e : expr) : nat :=
  match e with
  | ELit _ => 0 | EVar _ => 1 | EAlu _ _ _ => 2 | EAluw _ _ _ => 3
  | EMd _ _ _ => 4 | EMdw _ _ _ => 5 | EExt _ _ _ _ => 6 | EBlob _ _ _ _ => 7
  | EFop1 _ _ => 8 | EFop2 _ _ _ => 9 | EFop3 _ _ _ _ => 10 | EBlobX _ _ _ _ _ _ => 11
  | EShad _ _ _ => 12 | ESel _ _ _ => 13
  end.

(* [comment removed for export] *)
Definition ffmt_ix (f : ffmt) : nat := match f with FMT_S => 0 | FMT_D => 1 end.
Definition rmode_ix (m : rmode) : nat :=
  match m with RNE => 0 | RTZ => 1 | RDN => 2 | RUP => 3 | RMM => 4 end.
Definition fop1_ix (o : fop1) : nat :=
  match o with
  | FO_BoxS => 0
  | FO_Sqrt f m => 2 + 5 * ffmt_ix f + rmode_ix m
  | FO_Class f => 12 + ffmt_ix f
  | FO_CvtFF s d m => 14 + 10 * ffmt_ix s + 5 * ffmt_ix d + rmode_ix m
  | FO_CvtFI s g b m => 40 + 40 * ffmt_ix s + 20 * bool_ix g + 5 * (if Z.eqb b 32 then 0 else 1) + rmode_ix m
  | FO_CvtIF d g b m => 120 + 40 * ffmt_ix d + 20 * bool_ix g + 5 * (if Z.eqb b 32 then 0 else 1) + rmode_ix m
  end.
Definition fop2_ix (o : fop2) : nat :=
  match o with
  | FO_Sgnj op f => 2 * (match op with F_SGNJ => 0 | F_SGNJN => 1 | F_SGNJX => 2 end) + ffmt_ix f
  | FO_Ari op f m => 6 + 10 * (match op with F_ADD => 0 | F_SUB => 1 | F_MUL => 2 | F_DIV => 3 end) + 5 * ffmt_ix f + rmode_ix m
  | FO_Minmax op f => 46 + 2 * (match op with F_MIN => 0 | F_MAX => 1 end) + ffmt_ix f
  | FO_Cmp op f => 50 + 2 * (match op with F_EQ => 0 | F_LT => 1 | F_LE => 2 end) + ffmt_ix f
  end.
Definition fop3_ix (o : fop3) : nat :=
  match o with
  | FO_Ma op f m => 10 * (match op with F_MADD => 0 | F_MSUB => 1 | F_NMSUB => 2 | F_NMADD => 3 end) + 5 * ffmt_ix f + rmode_ix m
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
  | EFop1 o a, EFop1 o' a' => lexc (Nat.compare (fop1_ix o) (fop1_ix o')) (expr_cmp a a')
  | EFop2 o a b, EFop2 o' a' b' =>
      lexc (Nat.compare (fop2_ix o) (fop2_ix o')) (lexc (expr_cmp a a') (expr_cmp b b'))
  | EFop3 o a b c, EFop3 o' a' b' c' =>
      lexc (Nat.compare (fop3_ix o) (fop3_ix o'))
           (lexc (expr_cmp a a') (lexc (expr_cmp b b') (expr_cmp c c')))
  | EBlobX s k r d b n, EBlobX s' k' r' d' b' n' =>
      lexc (Nat.compare (bool_ix s) (bool_ix s'))
       (lexc (Nat.compare k k')
        (lexc (expr_cmp r r') (lexc (Z.compare d d') (lexc (expr_cmp b b') (Nat.compare n n')))))
  | EShad a b c, EShad a' b' c' => lexc (expr_cmp a a') (lexc (expr_cmp b b') (expr_cmp c c'))
  | ESel a b c, ESel a' b' c' => lexc (expr_cmp a a') (lexc (expr_cmp b b') (expr_cmp c c'))
  | _, _ => Nat.compare (ctor_ix x) (ctor_ix y)
  end.

(* [comment removed for export] *)
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

(* [comment removed for export] *)
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

(* [comment removed for export] *)
Fixpoint coeffs_div (m : Z) (ts : list (Z * expr)) : bool :=
  match ts with
  | [] => true
  | (k, _) :: rest => (Z.eqb (k mod m) 0 && coeffs_div m rest)%bool
  end.

Definition lin_lowbits (e : expr) (k : Z) : option Z :=
  let l := lin_of e in
  if coeffs_div (2 ^ k) (snd l) then Some ((fst l) mod 2 ^ k)%Z else None.

(* [comment removed for export] *)
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

(* [comment removed for export] *)
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

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

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

(* [comment removed for export] *)
Definition sfr_get (sfr : list expr) (r : reg) : expr := nth (ridx r) sfr (ELit 0).

(* [comment removed for export] *)
Definition sfr_vars (b : nat) : list expr := map (fun i => EVar (b + i)) (seq 0 32).

Definition sr_id : list expr :=
  [EVar 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7;
   EVar 8; EVar 9; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15;
   EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23;
   EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
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

(* [comment removed for export] *)
Record sentry : Type := SE { e_addr : saddr; e_width : nat; e_val : expr }.

(* [comment removed for export] *)
Inductive kentry : Type :=
| KWord (a : saddr) (w : nat) (v : expr)      (* [comment removed for export] *)
| KZero (a : saddr) (n : expr)                (* [comment removed for export] *)
| KBlob (a : saddr) (n : expr) (k : nat)      (* [comment removed for export] *)
| KBlobD (a : saddr) (n : expr) (k : nat)     (* [comment removed for export] *)
| KImg  (lo hi : Z)                           (* [comment removed for export] *)
| KAlign (e : expr) (m : Z)                   (* [comment removed for export] *)
| KRange (e : expr) (lo hi : Z)               (* [comment removed for export] *)
| KWr (a : saddr) (n : Z)                     (* [comment removed for export] *)
| KDisj (a1 : saddr) (n1 : Z) (a2 : saddr) (n2 : Z)
                                              (* [comment removed for export] *)
| KShad (d n : expr) (sb : Z).                (* [comment removed for export] *)

(* [comment removed for export] *)
Inductive sidecond : Type :=
| SCBr       (taken : bool) (c : branch_cond) (a b : expr)
| SCFlat     (a : saddr) (n : expr)                     (* [comment removed for export] *)
| SCDisj     (a1 : saddr) (n1 : expr) (a2 : saddr) (n2 : expr)  (* [comment removed for export] *)
| SCInside   (a1 : saddr) (n1 : expr) (a2 : saddr) (n2 : expr)  (* [comment removed for export] *)
| SCStoreOk  (a : saddr) (n : nat)                      (* [comment removed for export] *)
| SCReadBase (a : saddr) (n : nat) (sx : bool) (e : expr)  (* [comment removed for export] *)
| SCEq       (a b : expr).                              (* [comment removed for export] *)

Record sym_state : Type := SS {
  s_pc    : Z;
  s_regs  : list expr;
  s_fregs : list expr;        (* [comment removed for export] *)
  s_log   : list sentry;      (* [comment removed for export] *)
  s_know  : list kentry;
  s_next  : nat               (* [comment removed for export] *)
}.

Definition sset (ss : sym_state) (rd : reg) (e : expr) (npc : Z) : sym_state :=
  SS npc (if bv_eqb rd 0 then s_regs ss else sr_upd (s_regs ss) (ridx rd) e)
     (s_fregs ss) (s_log ss) (s_know ss) (s_next ss).

(* [comment removed for export] *)
Definition sfset (ss : sym_state) (rd : reg) (e : expr) (npc : Z) : sym_state :=
  SS npc (s_regs ss) (sr_upd (s_fregs ss) (ridx rd) e) (s_log ss) (s_know ss) (s_next ss).

Definition sjump (ss : sym_state) (npc : Z) : sym_state :=
  SS npc (s_regs ss) (s_fregs ss) (s_log ss) (s_know ss) (s_next ss).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Inductive rangerel := RInside (delta : Z) | RDisjoint | RPartial | RUnknown.

(* [comment removed for export] *)
Definition rel_lit (rb : expr) (rk : Z) (rn : Z) (kb : expr) (kk : Z) (kn : Z) : rangerel :=
  if expr_eqb rb kb then
    if (Z.leb kk rk && Z.leb (rk + rn) (kk + kn))%bool then RInside (rk - kk)
    else if (Z.leb (rk + rn) kk || Z.leb (kk + kn) rk)%bool then RDisjoint
    else RPartial
  else RUnknown.

Definition elen (n : nat) : expr := ELit (Z.of_nat n).

(* [comment removed for export] *)
Fixpoint find_range (kn : list kentry) (e : expr) : option (Z * Z) :=
  match kn with
  | [] => None
  | KRange e' lo hi :: rest => if expr_eqb e e' then Some (lo, hi) else find_range rest e
  | _ :: rest => find_range rest e
  end.

(* [comment removed for export] *)
Fixpoint find_align (kn : list kentry) (e : expr) : option Z :=
  match kn with
  | [] => None
  | KAlign e' m :: rest => if expr_eqb e e' then Some m else find_align rest e
  | _ :: rest => find_align rest e
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition two64 : Z := 2 ^ 64.

Definition clampi (r : Z * Z) : Z * Z :=
  let (lo, hi) := r in (Z.max lo 0, Z.min hi (two64 - 1)).

(* [comment removed for export] *)
Definition mask_cover (h : Z) : Z :=
  if Z.ltb h 0 then 0 else (2 ^ (Z.log2_up (h + 1)) - 1)%Z.

Definition lit_shamt (e : expr) : option Z :=
  match e with ELit s => Some (s mod 64)%Z | _ => None end.

(* [comment removed for export] *)
Definition zsigned64 (v : Z) : Z := if Z.leb (2 ^ 63) v then (v - two64)%Z else v.

(* [comment removed for export] *)
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
              | Some (lo, hi) => if (Z.leb 0 lo && Z.ltb hi two64)%bool then Some (lo, hi)
                                 (* [comment removed for export] *)
                                 else if (Z.leb (- two64) lo && Z.ltb hi 0)%bool then Some ((lo + two64)%Z, (hi + two64)%Z)
                                 else None
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
  | EFop2 (FO_Cmp _ _) _ _ => Some (0%Z, 1%Z)          (* [comment removed for export] *)
  | EFop1 (FO_Class _) _ => Some (0%Z, 512%Z)          (* [comment removed for export] *)
  | EFop1 _ _ | EFop2 _ _ _ | EFop3 _ _ _ _ => None
  | EBlobX sx k _ _ _ n =>
      if sx then None else Some (0%Z, Z.min (2 ^ (8 * Z.of_nat n) - 1) (two64 - 1))%Z
  | EShad _ _ _ => Some (0%Z, 7%Z)                      (* [comment removed for export] *)
  | ESel _ a b =>
      match erange kn a, erange kn b with
      | Some (al, ah), Some (bl, bh) => Some (Z.min al bl, Z.max ah bh)
      | _, _ => None
      end
  end
  end
  end
  end.

(* [comment removed for export] *)
Definition erange_fuel : nat := 64%nat.
Global Opaque erange_fuel.
Definition erange (kn : list kentry) (e : expr) : option (Z * Z) := erange_f erange_fuel kn e.


Definition base_range (kn : list kentry) (e : expr) : option (Z * Z) := erange kn e.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint ctz_fuel (fuel : nat) (z : Z) : Z :=
  match fuel with
  | O => 0
  | S f => if (Z.eqb (z mod 2) 0)%Z then (1 + ctz_fuel f (z / 2))%Z else 0%Z
  end.
Definition ctz64 (z : Z) : Z := ctz_fuel 64 z.

(* [comment removed for export] *)
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
  (* [comment removed for export] *)
  | EAlu ALU_SRL a b =>
      match lit_shamt b with
      | Some s => Z.max (ealign kn a - s)%Z 0
      | None => 0%Z
      end
  (* [comment removed for export] *)
  | EAluw ALU_ADD a b => Z.min (Z.min (ealign kn a) (ealign kn b)) 32
  | EAluw ALU_SUB a b => Z.min (Z.min (ealign kn a) (ealign kn b)) 32
  | _ => 0%Z
  end
  end.

(* [comment removed for export] *)
Definition is_lit0 (e : expr) : bool := match e with ELit 0 => true | _ => false end.
Definition sub_itv (allkn : list kentry) (b : expr) (k n : Z) (c : saddr) (m : Z) : bool :=
  ((expr_eqb b (a_base c) && Z.leb (a_off c) k && Z.leb (k + n) (a_off c + m))
   || (is_lit0 (a_base c)
       && match base_range allkn b with
          | Some (lo, hi) => Z.leb (a_off c) (lo + k) && Z.leb (hi + k + n) (a_off c + m)
          | None => false
          end))%bool.

(* [comment removed for export] *)
Fixpoint kdisj_apart_f (allkn kn : list kentry) (b1 : expr) (k1 n1 : Z) (b2 : expr) (k2 n2 : Z) : bool :=
  match kn with
  | [] => false
  | KDisj c1 m1 c2 m2 :: rest =>
      ((sub_itv allkn b1 k1 n1 c1 m1 && sub_itv allkn b2 k2 n2 c2 m2)
       || (sub_itv allkn b1 k1 n1 c2 m2 && sub_itv allkn b2 k2 n2 c1 m1)
       || kdisj_apart_f allkn rest b1 k1 n1 b2 k2 n2)%bool
  | _ :: rest => kdisj_apart_f allkn rest b1 k1 n1 b2 k2 n2
  end.
Definition kdisj_apart (kn : list kentry) (b1 : expr) (k1 n1 : Z) (b2 : expr) (k2 n2 : Z) : bool :=
  kdisj_apart_f kn kn b1 k1 n1 b2 k2 n2.

Definition ranges_apart (kn : list kentry) (b1 : expr) (k1 n1 : Z) (b2 : expr) (k2 n2 : Z) : bool :=
  (match base_range kn b1, base_range kn b2 with
   | Some (lo1, hi1), Some (lo2, hi2) =>
       (Z.leb (hi1 + k1 + n1) (lo2 + k2) || Z.leb (hi2 + k2 + n2) (lo1 + k1))%bool
   | _, _ => false
   end) || kdisj_apart kn b1 k1 n1 b2 k2 n2.

(* [comment removed for export] *)
Fixpoint zone_apart_f (allkn kn : list kentry) (b : expr) (k n zlo zhi : Z) : bool :=
  match kn with
  | [] => false
  | KDisj c1 m1 c2 m2 :: rest =>
      ((sub_itv allkn b k n c1 m1 && is_lit0 (a_base c2) && Z.leb (a_off c2) zlo && Z.leb zhi (a_off c2 + m2))
       || (sub_itv allkn b k n c2 m2 && is_lit0 (a_base c1) && Z.leb (a_off c1) zlo && Z.leb zhi (a_off c1 + m1))
       || zone_apart_f allkn rest b k n zlo zhi)%bool
  | _ :: rest => zone_apart_f allkn rest b k n zlo zhi
  end.

(* [comment removed for export] *)
Definition shad_zone_apart (allkn : list kentry) (b : expr) (k n : Z) (d len : expr) (sb : Z) : bool :=
  match erange allkn (EAlu ALU_ADD d len), erange allkn d, erange allkn len with
  | Some (_, H), Some (_, hd), Some (_, hl) =>
      (Z.ltb (hd + hl) two64 && zone_apart_f allkn allkn b k n sb (sb + H / 8 + 1))%bool
  | _, _, _ => false
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Inductive lres :=
| LHit (v : expr) (scs : list sidecond) (hints : list bool)
| LMiss (scs : list sidecond) (hints : list bool)     (* [comment removed for export] *)
| LStuck.

(* [comment removed for export] *)
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

(* [comment removed for export] *)
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

(* [comment removed for export] *)
Definition srl3_of (e : expr) : option expr :=
  match e with
  | EAlu ALU_SRL X (ELit z) => if Z.eqb z 3 then Some X else None
  | _ => None
  end.
Definition shad_of (e : expr) : option (expr * expr * expr) :=
  match e with
  | EShad x d n => Some (x, d, n)
  | _ => None
  end.
(* [comment removed for export] *)
Definition and7k_of (e : expr) : option (expr * Z) :=
  match e with
  | EAlu ALU_AND X2 (ELit z) => if Z.eqb z 7 then Some (X2, 0%Z) else None
  | EAlu ALU_ADD (EAlu ALU_AND X2 (ELit z)) (ELit k) => if Z.eqb z 7 then Some (X2, k) else None
  | _ => None
  end.

(* [comment removed for export] *)
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
            (* [comment removed for export] *)
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
      | KBlobD (SA kb kk) len k =>
          let claim hs := LHit (EBlobX sx k rb (rk - kk) kb n)
                               (SCInside (SA rb rk) (elen n) (SA kb kk) len :: acc) hs in
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
                  | false :: hs => know_lookup segs rest rb rk n sx hs acc
                  | true :: hs => LHit (EBlob sx k (rk - kk) n) (SCInside (SA rb rk) (elen n) (SA kb kk) len :: acc) hs
                  | [] => LHit (EBlob sx k (rk - kk) n) (SCInside (SA rb rk) (elen n) (SA kb kk) len :: acc) []
                  end
              end
            else know_lookup segs rest rb rk n sx hints acc
          else
            match hints with
            | false :: hs => know_lookup segs rest rb rk n sx hs acc
            | true :: hs => claim hs
            | [] => claim []
            end
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
      | KShad d len sb =>
          match (if Nat.eqb n 1 then srl3_of rb else None) with
          | Some X =>
              match hints with
              | false :: hs => know_lookup segs rest rb rk n sx hs acc
              | _ =>
                  let k := (rk - sb)%Z in
                  LHit (EShad (mkAlu ALU_ADD X (ELit (8 * k))) d len)
                       (SCInside (SA X (8 * k)) (ELit 1) (SA d 0) len :: acc)
                       (match hints with [] => [] | _ :: hs => hs end)
              end
          | None => know_lookup segs rest rb rk n sx hints acc
          end
      end
  end.

(* [comment removed for export] *)
Definition shad_lmax (kn : list kentry) (len : expr) : Z :=
  match erange kn len with
  | Some (_, hi) => Z.min (hi / 8 + 2)%Z (2 ^ 61 + 2)%Z
  | None => (2 ^ 61 + 2)%Z
  end.
Definition shad_saddr (d : expr) (sb : Z) : saddr := SA (EAlu ALU_SRL d (ELit 3)) sb.

(* [comment removed for export] *)
Fixpoint coeffs_divK (kn : list kentry) (m : Z) (ts : list (Z * expr)) : bool :=
  match ts with
  | [] => true
  | (k, a) :: rest => (Z.eqb ((k * 2 ^ ealign kn a) mod m) 0 && coeffs_divK kn m rest)%bool
  end.

Definition lin_lowbitsK (kn : list kentry) (e : expr) (k : Z) : option Z :=
  let l := lin_of e in
  if coeffs_divK kn (2 ^ k) (snd l) then Some ((fst l) mod 2 ^ k)%Z else None.

(* [comment removed for export] *)
Definition mkAnd (kn : list kentry) (a b : expr) : expr :=
  match b with
  | ELit k =>
      let k' := (k mod two64)%Z in
      let j := Z.log2 (two64 - k') in
      if (Z.eqb (two64 - k') (2 ^ j) && Z.ltb j 64)%bool then
        (* [comment removed for export] *)
        (if Z.leb j (ealign kn a) then a
         else let l := lin_of a in
              if coeffs_divK kn (2 ^ j) (snd l) then unlin ((fst l - (fst l) mod 2 ^ j)%Z, snd l)
              else mkAlu ALU_AND a b)
      else
        let j2 := Z.log2 (k' + 1) in
        if (Z.eqb (k' + 1) (2 ^ j2) && Z.ltb j2 64)%bool then
          (* [comment removed for export] *)
          (if Z.leb j2 (ealign kn a) then ELit 0
           else match lin_lowbitsK kn a j2 with
                | Some v => ELit v
                | None => mkAlu ALU_AND a b
                end)
        else
          (* [comment removed for export] *)
          if (Z.ltb 0 (ealign kn a) && Z.ltb k' (2 ^ (ealign kn a)))%bool then ELit 0
          else mkAlu ALU_AND a b
  | _ => mkAlu ALU_AND a b
  end.

(* [comment removed for export] *)
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

(* [comment removed for export] *)
Fixpoint ldiv_terms (m : Z) (ts : list (Z * expr)) : list (Z * expr) :=
  match ts with
  | [] => []
  | (k, a) :: rest => ((k / m)%Z, a) :: ldiv_terms m rest
  end.

(* [comment removed for export] *)
Definition lin_nowrap (kn : list kentry) (e : expr) : bool :=
  let l := lin_of e in
  match lin_range (erange kn) (fst l) (snd l) with
  | Some (lo, hi) => (Z.leb 0 lo && Z.ltb hi two64)%bool
  | None => false
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint ldiv_termsK (kn : list kentry) (m s : Z) (ts : list (Z * expr)) : option (list (Z * expr)) :=
  match ts with
  | [] => Some []
  | (k, a) :: rest =>
      match ldiv_termsK kn m s rest with
      | None => None
      | Some rest' =>
          if Z.eqb (k mod m) 0 then Some (((k / m)%Z, a) :: rest')
          else if Z.leb s (ealign kn a) then Some ((k, EAlu ALU_SRL a (ELit s)) :: rest')
          else None
      end
  end.

Definition mkSrl (kn : list kentry) (a : expr) (s : Z) : expr :=
  let l := lin_of a in
  let m := (2 ^ s)%Z in
  if (negb (lin_trivial l) && lin_nowrap kn a)%bool then
    match ldiv_termsK kn m s (snd l) with
    | Some ts' => unlin (ladd ((fst l) / m, []) (0, ts'))%Z
    | None => mkAlu ALU_SRL a (ELit s)
    end
  else mkAlu ALU_SRL a (ELit s).

(* [comment removed for export] *)
Definition mkXor (a b : expr) : expr :=
  match is_lit a, b with
  | None, ELit k =>
      if Z.eqb (k mod two64) (two64 - 1) then unlin (ladd (lin_of (ELit (-1))) (lscale (-1) (lin_of a)))
      else mkAlu ALU_XOR a b
  | _, _ => mkAlu ALU_XOR a b
  end.

Definition mkAluK (kn : list kentry) (op : aluop) (a b : expr) : expr :=
  match op with
  | ALU_AND => match a, b with
               | ELit _, ELit _ => mkAnd kn a b
               | ELit _, _ => mkAnd kn b a      (* [comment removed for export] *)
               | _, _ => mkAnd kn a b
               end
  | ALU_OR => mkOr kn a b
  | ALU_XOR => mkXor a b
  | ALU_SRL => match is_lit a, shamt_of b 6 with
               | None, Some s => mkSrl kn a s
               | _, _ => mkAlu op a b
               end
  | _ => mkAlu op a b
  end.

Definition msize_bytes (sz : msize) : nat :=
  match sz with SZ1 => 1 | SZ2 => 2 | SZ4 => 4 | SZ8 => 8 end.

(* [comment removed for export] *)
Fixpoint flat_covered (kn : list kentry) (a : saddr) (n : nat) : bool :=
  match kn with
  | [] => false
  | K :: rest =>
      let inside (kb : expr) (kk : Z) (klen : Z) :=
        (expr_eqb (a_base a) kb && Z.leb kk (a_off a) && Z.leb (a_off a + Z.of_nat n) (kk + klen))%bool in
      (match K with
       | KWord (SA kb kk) w _ => inside kb kk (Z.of_nat w)
       | KWr (SA kb kk) len => inside kb kk len
       | KZero (SA kb kk) (ELit l) => inside kb kk (l mod 2 ^ 64)%Z
       | KBlob (SA kb kk) (ELit l) _ => inside kb kk (l mod 2 ^ 64)%Z
       | KBlobD (SA kb kk) (ELit l) _ => inside kb kk (l mod 2 ^ 64)%Z
       | _ => false
       end || flat_covered rest a n)%bool
  end.

(* [comment removed for export] *)
Definition flat_sc (kn : list kentry) (a : saddr) (n : nat) : list sidecond :=
  if flat_covered kn a n then [] else
  match base_range kn (a_base a) with
  | Some (lo, hi) =>
      if (Z.leb 0 (lo + a_off a) && Z.leb (hi + a_off a + Z.of_nat n) (2 ^ 64))%bool
      then [] else [SCFlat a (elen n)]
  | None => [SCFlat a (elen n)]
  end.

(* [comment removed for export] *)
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

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Record scripts : Type := SCR {
  sc_dirs  : list bool;     (* [comment removed for export] *)
  sc_reads : list expr;     (* [comment removed for export] *)
  sc_hints : list bool      (* [comment removed for export] *)
}.

Inductive stepres :=
| SOk (ss : sym_state) (scs : list sidecond) (scr : scripts)
| SStop.

Definition lit_branch (c : branch_cond) (x y : Z) : bool :=
  branch_taken c (Z_to_bv 64 x) (Z_to_bv 64 y).

(* [comment removed for export] *)
Definition cond_on_eq (c : branch_cond) : bool :=
  match c with
  | BC_EQ => true | BC_NE => false | BC_LT => false | BC_GE => true
  | BC_LTU => false | BC_GEU => true
  end.

(* [comment removed for export] *)
Definition itv_ltu (al ah bl bh : Z) : option bool :=
  if Z.ltb ah bl then Some true else if Z.leb bh al then Some false else None.

(* [comment removed for export] *)
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

(* [comment removed for export] *)
Definition lin_eq_dec (c : branch_cond) (a b : expr) : option bool :=
  match c with
  | BC_EQ | BC_NE =>
      let d := ladd (lin_of a) (lscale (-1) (lin_of b)) in
      match snd d with
      | [] => let ne := negb (Z.eqb ((fst d) mod two64) 0) in
              Some (match c with BC_EQ => negb ne | _ => ne end)
      | _ => None
      end
  | _ => None
  end.

(* [comment removed for export] *)
Fixpoint terms_eqb (x y : list (Z * expr)) : bool :=
  match x, y with
  | [], [] => true
  | (k, e) :: x', (k', e') :: y' => (Z.eqb k k' && expr_eqb e e' && terms_eqb x' y')%bool
  | _, _ => false
  end.

Definition lin_cmp_dec (kn : list kentry) (c : branch_cond) (a b : expr) : option bool :=
  match c with
  | BC_LTU | BC_GEU =>
      if (lin_nowrap kn a && lin_nowrap kn b && terms_eqb (snd (lin_of a)) (snd (lin_of b)))%bool then
        let d := (fst (lin_of a) - fst (lin_of b))%Z in
        Some (match c with BC_LTU => Z.ltb d 0 | _ => negb (Z.ltb d 0) end)
      else None
  | _ => None
  end.

Definition lin_dec2 (kn : list kentry) (c : branch_cond) (a b : expr) : option bool :=
  match lin_eq_dec c a b with
  | Some t => Some t
  | None => lin_cmp_dec kn c a b
  end.

(* [comment removed for export] *)
Definition decide_branch (kn : list kentry) (c : branch_cond) (a b : expr) : option bool :=
  match a, b with
  | ELit x, ELit y => Some (lit_branch c x y)
  | _, _ =>
      if expr_eqb a b then Some (cond_on_eq c)
      else match match erange kn a, erange kn b with
                 | Some (al, ah), Some (bl, bh) => range_branch c al ah bl bh
                 | _, _ => None
                 end with
           | Some t => Some t
           | None => lin_dec2 kn c a b
           end
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

Fixpoint closedb (e : expr) : bool :=
  match e with
  | ELit _ => true
  | EVar _ => false
  | EAlu _ a b | EAluw _ a b | EMd _ a b | EMdw _ a b => closedb a && closedb b
  | EExt _ _ _ a => closedb a
  | EBlob _ _ _ _ => false
  | EFop1 _ _ | EFop2 _ _ _ | EFop3 _ _ _ _ => false   (* [comment removed for export] *)
  | EBlobX _ _ _ _ _ _ => false
  | EShad _ _ _ | ESel _ _ _ => false
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

(* [comment removed for export] *)
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
  | EFop1 _ _ | EFop2 _ _ _ | EFop3 _ _ _ _ => None
  | EBlobX _ _ _ _ _ _ => None
  | EShad _ _ _ | ESel _ _ _ => None
  end.

(* [comment removed for export] *)
Fixpoint subexprs (e : expr) : list expr :=
  match e with
  | EAlu _ a b | EAluw _ a b | EMd _ a b | EMdw _ a b => subexprs a ++ subexprs b ++ [e]
  | EExt _ _ _ a => subexprs a ++ [e]
  | _ => [e]
  end.

(* [comment removed for export] *)
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

(* [comment removed for export] *)
Definition conc_expr (kn : list kentry) (e : expr) : expr :=
  match e with
  | ELit _ => e
  | _ => match concretize kn e with Some v => ELit v | None => e end
  end.

(* [comment removed for export] *)
Definition to_saddrK (kn : list kentry) (e : expr) (imm : Z) : saddr :=
  match split_lit e with
  | (ELit _, _) => to_saddr e imm
  | _ => match concretize kn (mkAlu ALU_ADD e (ELit imm)) with
         | Some v => SA (ELit 0) v
         | None => to_saddr e imm
         end
  end.

(* [comment removed for export] *)
Definition ext_small (kn : list kentry) (sx : bool) (n : nat) (e : expr) : bool :=
  match erange kn e with
  | Some (lo, hi) =>
      (Z.leb 0 lo && (if sx then Z.ltb hi (2 ^ (8 * Z.of_nat n) / 2) else Z.ltb hi (2 ^ (8 * Z.of_nat n))))%bool
  | None => false
  end.

Definition mkExtK (kn : list kentry) (e : expr) : expr :=
  match e with
  | EExt sx O n a => if ext_small kn sx n a then a else e
  | _ => e
  end.

(* [comment removed for export] *)
Definition load_resolve (segs : list Segment) (ss : sym_state) (scr : scripts)
           (a : saddr) (n : nat) (sx : bool) : option (expr * list sidecond * scripts * nat) :=
  let kn := s_know ss in
  match log_lookup kn (s_log ss) (a_base a) (a_off a) n sx (sc_hints scr) [] with
  | LStuck => None
  | LHit v scs hints => Some (mkExtK kn v, flat_sc kn a n ++ scs, SCR (sc_dirs scr) (sc_reads scr) hints, s_next ss)
  | LMiss scs hints =>
      match know_lookup segs kn (a_base a) (a_off a) n sx hints scs with
      | LStuck => None
      | LHit v scs' hints' => Some (mkExtK kn v, flat_sc kn a n ++ scs', SCR (sc_dirs scr) (sc_reads scr) hints', s_next ss)
      | LMiss scs' hints' =>
          (* [comment removed for export] *)
          let i := s_next ss in
          let rv := match sc_reads scr with [] => EVar i | e :: _ => e end in
          let reads' := match sc_reads scr with [] => [] | _ :: t => t end in
          Some (rv, flat_sc kn a n ++ SCReadBase a n sx rv :: scs', SCR (sc_dirs scr) reads' hints', S i)
      end
  end.

Definition sym_step (segs : list Segment) (i : instr) (ss : sym_state) (scr : scripts) : stepres :=
  let g r := sr_get (s_regs ss) r in
  let f r := sfr_get (s_fregs ss) r in
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
      (* [comment removed for export] *)
      let sx' := match sz with SZ8 => false | _ => sx end in
      let a := to_saddrK (s_know ss) (g rs) (bv_signed imm) in
      match load_resolve segs ss scr a n sx' with
      | None => SStop
      | Some (v, scs, scr', nx) =>
          SOk (SS (p + 4) (if bv_eqb rd 0 then s_regs ss else sr_upd (s_regs ss) (ridx rd) v)
                  (s_fregs ss) (s_log ss) (s_know ss) nx) scs scr'
      end
  | Store sz rs1 rs2 imm =>
      let n := msize_bytes sz in
      let a := to_saddrK (s_know ss) (g rs1) (bv_signed imm) in
      SOk (SS (p + 4) (s_regs ss) (s_fregs ss) (SE a n (g rs2) :: s_log ss) (s_know ss) (s_next ss))
          (flat_sc (s_know ss) a n ++ storeok_sc (s_know ss) a n) scr
  (* [comment removed for export] *)
  | FLoad fmt rd rs imm =>
      let n := fmt_bytes fmt in
      let a := to_saddrK (s_know ss) (g rs) (bv_signed imm) in
      match load_resolve segs ss scr a n false with
      | None => SStop
      | Some (v, scs, scr', nx) =>
          let fv := match fmt with FMT_S => EFop1 FO_BoxS v | FMT_D => v end in
          SOk (SS (p + 4) (s_regs ss) (sr_upd (s_fregs ss) (ridx rd) fv) (s_log ss) (s_know ss) nx) scs scr'
      end
  | FStore fmt rs1 rs2 imm =>
      let n := fmt_bytes fmt in
      let a := to_saddrK (s_know ss) (g rs1) (bv_signed imm) in
      SOk (SS (p + 4) (s_regs ss) (s_fregs ss) (SE a n (f rs2) :: s_log ss) (s_know ss) (s_next ss))
          (flat_sc (s_know ss) a n ++ storeok_sc (s_know ss) a n) scr
  | Fmv FMV_X_F FMT_S rd rs1 => SOk (sset ss rd (mkExtK (s_know ss) (mkExt true 0 4 (f rs1))) (p + 4)) [] scr
  | Fmv FMV_X_F FMT_D rd rs1 => SOk (sset ss rd (f rs1) (p + 4)) [] scr
  | Fmv FMV_F_X FMT_S rd rs1 => SOk (sfset ss rd (EFop1 FO_BoxS (g rs1)) (p + 4)) [] scr
  | Fmv FMV_F_X FMT_D rd rs1 => SOk (sfset ss rd (g rs1) (p + 4)) [] scr
  | Fsgnj op fmt rd rs1 rs2 => SOk (sfset ss rd (EFop2 (FO_Sgnj op fmt) (f rs1) (f rs2)) (p + 4)) [] scr
  | Fari op fmt rd rs1 rs2 rm =>
      match rm_static rm with
      | Some md => SOk (sfset ss rd (EFop2 (FO_Ari op fmt md) (f rs1) (f rs2)) (p + 4)) [] scr
      | None => SStop
      end
  | Fsqrt fmt rd rs1 rm =>
      match rm_static rm with
      | Some md => SOk (sfset ss rd (EFop1 (FO_Sqrt fmt md) (f rs1)) (p + 4)) [] scr
      | None => SStop
      end
  | Fma op fmt rd rs1 rs2 rs3 rm =>
      match rm_static rm with
      | Some md => SOk (sfset ss rd (EFop3 (FO_Ma op fmt md) (f rs1) (f rs2) (f rs3)) (p + 4)) [] scr
      | None => SStop
      end
  | Fminmax op fmt rd rs1 rs2 => SOk (sfset ss rd (EFop2 (FO_Minmax op fmt) (f rs1) (f rs2)) (p + 4)) [] scr
  | Fcmp op fmt rd rs1 rs2 => SOk (sset ss rd (EFop2 (FO_Cmp op fmt) (f rs1) (f rs2)) (p + 4)) [] scr
  | Fclass fmt rd rs1 => SOk (sset ss rd (EFop1 (FO_Class fmt) (f rs1)) (p + 4)) [] scr
  | Fcvt dst src rd rs1 rm =>
      match rm_static rm with
      | None => SStop
      | Some md =>
          match fcvt_fty dst, fcvt_fty src with
          | Some df, Some sf => SOk (sfset ss rd (EFop1 (FO_CvtFF sf df md) (f rs1)) (p + 4)) [] scr
          | None, Some sf =>
              match fcvt_ity dst with
              | Some (sgn, bits) => SOk (sset ss rd (EFop1 (FO_CvtFI sf sgn bits md) (f rs1)) (p + 4)) [] scr
              | None => SStop
              end
          | Some df, None =>
              match fcvt_ity src with
              | Some (sgn, bits) => SOk (sfset ss rd (EFop1 (FO_CvtIF df sgn bits md) (g rs1)) (p + 4)) [] scr
              | None => SStop
              end
          | None, None => SStop
          end
      end
  | _ => SStop
  end.

(* [comment removed for export] *)
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

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

Definition site_fuel : nat := 8%nat.

(* [comment removed for export] *)
Definition site_size (kn : list kentry) (X ey : expr) : option Z :=
  match is_lit ey with
  | Some c =>
      match lin_lowbitsK kn X 3 with
      | Some c0 => if (Z.leb c0 c && Z.ltb c 64)%bool then Some (c - c0 + 1)%Z else None
      | None => None
      end
  | None =>
      match and7k_of ey with
      | Some (X2, k) => if (expr_eqb X2 X && Z.leb 0 k && Z.ltb k 64)%bool then Some (k + 1)%Z else None
      | None => None
      end
  end.

(* [comment removed for export] *)
Definition site_plain (i : instr) : bool :=
  match i with
  | OpImm _ _ _ _ | ShiftImm _ _ _ _ | Op _ _ _ _ | OpImm32 _ _ _ | ShiftImm32 _ _ _ _
  | Op32 _ _ _ _ | Lui _ _ | Auipc _ _ | Load _ _ _ _ _ => true
  | _ => false
  end.

Definition fetch_instr (segs : list Segment) (pc : Z) : option instr :=
  match fetch_word segs (Z_to_bv 64 pc) with
  | None => None
  | Some w => if is_ecall w then None else
              match decode_any w with
              | Some (i, 4%Z) => Some i
              | _ => None
              end
  end.

(* [comment removed for export] *)
Fixpoint site_run (segs : list Segment) (fuel : nat) (vexp : expr) (fast : Z)
         (ss : sym_state) (scr : scripts) (acc : list sidecond)
  : option (sym_state * expr * list sidecond * scripts) :=
  match fuel with
  | O => None
  | S f =>
      let p := s_pc ss in
      let g r := sr_get (s_regs ss) r in
      match fetch_instr segs p with
      | None => None
      | Some i =>
          match i with
          | Branch BC_LT rsY rsV imm =>
              let tk := bv_unsigned (Z_to_bv 64 (p + bv_signed imm)) in
              if (expr_eqb (g rsV) vexp && Z.eqb tk fast)%bool then Some (ss, g rsY, acc, scr) else None
          | Branch BC_GE rsY rsV imm =>
              if expr_eqb (g rsV) vexp then
                (if Z.eqb (p + 4) fast then Some (ss, g rsY, acc, scr)
                 else match fetch_instr segs (p + 4) with
                      | Some (Jal rd imm2) =>
                          if (bv_eqb rd 0 && Z.eqb (bv_unsigned (Z_to_bv 64 (p + 4 + bv_signed imm2))) fast)%bool
                          then Some (ss, g rsY, acc, scr) else None
                      | _ => None
                      end)
              else None
          | Jal rd imm =>
              if bv_eqb rd 0 then site_run segs f vexp fast (sjump ss (bv_unsigned (Z_to_bv 64 (p + bv_signed imm)))) scr acc
              else None
          | _ =>
              if site_plain i then
                match sym_step segs i ss scr with
                | SOk ss' scs scr' =>
                    if Z.eqb (s_pc ss') (p + 4) then site_run segs f vexp fast ss' scr' (sc_add scs acc) else None
                | SStop => None
                end
              else None
          end
      end
  end.

(* [comment removed for export] *)
Definition merge_regs (vexp : expr) (sr1 sr2 : list expr) : list expr :=
  map (fun i => let o := nth i sr1 (ELit 0) in
                let n := nth i sr2 (ELit 0) in
                if expr_eqb o n then o else ESel vexp o n) (seq 0 32).

(* [comment removed for export] *)
Definition asan_site (segs : list Segment) (i : instr) (ss : sym_state) (scr : scripts)
  : option (sym_state * list sidecond * scripts) :=
  let p := s_pc ss in
  match i with
  | Branch c rsV rs0 imm =>
      if bv_eqb rs0 0 then
        match shad_of (sr_get (s_regs ss) rsV) with
        | Some (X, d, n) =>
            let vexp := sr_get (s_regs ss) rsV in
            let tk := bv_unsigned (Z_to_bv 64 (p + bv_signed imm)) in
            let ways := match c with
                        | BC_NE => Some (tk, (p + 4)%Z)      (* [comment removed for export] *)
                        | BC_EQ => Some ((p + 4)%Z, tk)
                        | _ => None
                        end in
            match ways with
            | None => None
            | Some (slow, fast) =>
                match site_run segs site_fuel vexp fast (sjump ss slow) scr [] with
                | None => None
                | Some (ss2, ey, acc, scr') =>
                    match site_size (s_know ss) X ey with
                    | None => None
                    | Some L =>
                        Some (SS fast (merge_regs vexp (s_regs ss) (s_regs ss2)) (s_fregs ss)
                                 (s_log ss) (s_know ss) (s_next ss2),
                              SCInside (SA X 0) (ELit L) (SA d 0) n :: acc, scr')
                    end
                end
            end
        | None => None
        end
      else None
  | _ => None
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section WithSegs.
Variable segs : list Segment.

(* [comment removed for export] *)
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
              match asan_site segs i ss scr with
              | Some (ss', scs, scr') => sym_exec f false stops scr' ss' (sc_add scs acc)
              | None =>
              match sym_step segs i ss scr with
              | SOk ss' scs scr' => sym_exec f false stops scr' ss' (sc_add scs acc)
              | SStop => (ss, acc, scr)
              end
              end
          end
      end
  end.

End WithSegs.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
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
    | true :: hs => ([K], [SCDisj wa (elen w) ka kl], hs)   (* [comment removed for export] *)
    | false :: hs => ([], [], hs)                          (* [comment removed for export] *)
    | [] => ([], [], [])                                   (* [comment removed for export] *)
    end in
  match K with
  | KAlign _ _ => ([K], [], hints)
  | KRange _ _ _ => ([K], [], hints)
  | KWr _ _ => ([K], [], hints)
  | KDisj _ _ _ _ => ([K], [], hints)
  | KShad d len sb =>
      if shad_zone_apart allkn (a_base wa) k (Z.of_nat w) d len sb then ([K], [], hints)
      else diffbase (shad_saddr d sb) (ELit (shad_lmax allkn len))
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
  | KBlob (SA kb kk) len bk | KBlobD (SA kb kk) len bk =>
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

(* [comment removed for export] *)
Fixpoint carry (log : list sentry) (kn : list kentry) (hints : list bool)
  : list kentry * list sidecond * list bool :=
  match log with
  | [] => (kn, [], hints)
  | SE a w v :: older =>
      let '(kn1, scs1, hs1) := carry older kn hints in
      let '(kn2, scs2, hs2) := prune kn1 a w kn1 hs1 in
      (KWord a w v :: kn2, scs1 ++ scs2, hs2)
  end.


End ASX.
