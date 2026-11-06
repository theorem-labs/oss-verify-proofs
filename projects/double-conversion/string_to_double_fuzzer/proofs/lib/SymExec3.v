(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import PropExec CatExec CatSim SeqExec StoreOk SymExec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Module SX2.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section FPW_1. Context {fx : PropExec.FPState}.


Inductive expr : Type :=
| ELit  (z : Z)                              (* [comment removed for export] *)
| EVar  (n : nat)                            (* [comment removed for export] *)
| EAlu  (op : aluop) (a b : expr)            (* [comment removed for export] *)
| EAluw (op : aluop) (a b : expr)            (* [comment removed for export] *)
| EMd   (op : mulop) (a b : expr)            (* [comment removed for export] *)
| EMdw  (op : mulop) (a b : expr)            (* [comment removed for export] *)
| EExt  (sx : bool) (lo n : nat) (e : expr)  (* [comment removed for export] *)
| EBlob (sx : bool) (k : nat) (i : Z) (n : nat).
                                             (* [comment removed for export] *)

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

(* [comment removed for export] *)
Lemma aluop_eqb_true : forall a b, aluop_eqb a b = true -> a = b.
Proof. intros [] []; cbn; intros; try reflexivity; discriminate. Qed.
Lemma mulop_eqb_true : forall a b, mulop_eqb a b = true -> a = b.
Proof. intros [] []; cbn; intros; try reflexivity; discriminate. Qed.
Lemma expr_eqb_true : forall x y, expr_eqb x y = true -> x = y.
Proof.
  induction x; destruct y; cbn; intros H; try discriminate;
    repeat match goal with
      | H : (_ && _)%bool = true |- _ => apply andb_prop in H; destruct H
      end;
    repeat match goal with
      | H : Z.eqb _ _ = true |- _ => apply Z.eqb_eq in H
      | H : Nat.eqb _ _ = true |- _ => apply Nat.eqb_eq in H
      | H : Bool.eqb _ _ = true |- _ => apply Bool.eqb_prop in H
      | H : aluop_eqb _ _ = true |- _ => apply aluop_eqb_true in H
      | H : mulop_eqb _ _ = true |- _ => apply mulop_eqb_true in H
      | H : expr_eqb ?a _ = true, IH : forall y, expr_eqb ?a y = true -> _ |- _ => apply IH in H
      end; subst; reflexivity.
Qed.

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
Definition two64 : Z := 2 ^ 64.    (* [comment removed for export] *)
(* [comment removed for export] *)
Definition two63z : Z := 2 ^ 63.
Definition mtwo63z : Z := - 2 ^ 63.
Definition two32z : Z := 2 ^ 32.
Definition two31z : Z := 2 ^ 31.
Definition ones64z : Z := Z.ones 64.          (* [comment removed for export] *)
Definition ones32z : Z := Z.ones 32.
(* [comment removed for export] *)
Definition snorm_ref (k : Z) : Z :=
  let m := (k mod two64z)%Z in if Z.leb (2 ^ 63) m then (m - two64z)%Z else m.
(* [comment removed for export] *)
Definition snorm (k : Z) : Z :=
  if (if Z.leb mtwo63z k then Z.ltb k two63z else false) then k
  else let m := Z.land k ones64z in if Z.leb two63z m then (m - two64z)%Z else m.
Lemma land_ones64z' : forall a, Z.land a ones64z = (a mod 2 ^ 64)%Z.
Proof. intros a. exact (Z.land_ones a 64 ltac:(lia)). Qed.
Lemma snorm_eq : forall k, snorm k = snorm_ref k.
Proof.
  intros k. cbv beta zeta delta [snorm snorm_ref mtwo63z two63z two64z]. rewrite land_ones64z'.
  pose proof (Z.mod_pos_bound k (2 ^ 64) ltac:(lia)) as B.
  destruct (Z.leb_spec (- 2 ^ 63) k) as [H1|H1]; [|reflexivity].
  destruct (Z.ltb_spec k (2 ^ 63)) as [H2|H2]; [|reflexivity].
  destruct (Z.leb_spec 0 k) as [H3|H3].
  - rewrite (Z.mod_small k (2 ^ 64)) by lia.
    destruct (Z.leb_spec (2 ^ 63) k); lia.
  - replace (k mod 2 ^ 64)%Z with (k + 2 ^ 64)%Z.
    + destruct (Z.leb_spec (2 ^ 63) (k + 2 ^ 64)); lia.
    + symmetry. rewrite <- (Z.mod_add k 1 (2 ^ 64)) by lia. apply Z.mod_small. lia.
Qed.

(* [comment removed for export] *)
Definition zmod64 (z : Z) : Z :=
  if (if Z.leb 0 z then Z.ltb z two64z else false) then z else Z.land z ones64z.
Lemma zmod64_eq : forall z, zmod64 z = (z mod 2 ^ 64)%Z.
Proof.
  intros z. cbv beta iota delta [zmod64 two64z]. rewrite land_ones64z'.
  destruct (Z.leb_spec 0 z); [|reflexivity]. destruct (Z.ltb_spec z (2 ^ 64)); [|reflexivity].
  symmetry. apply Z.mod_small. lia.
Qed.
Definition zdiv64 (z : Z) : Z :=
  if (if Z.leb 0 z then Z.ltb z two64z else false) then 0 else Z.shiftr z 64.
Lemma zdiv64_eq : forall z, zdiv64 z = (z / 2 ^ 64)%Z.
Proof.
  intros z. cbv beta iota delta [zdiv64 two64z].
  destruct (Z.leb_spec 0 z); [|apply Z.shiftr_div_pow2; lia].
  destruct (Z.ltb_spec z (2 ^ 64)); [|apply Z.shiftr_div_pow2; lia].
  symmetry. apply Z.div_small. lia.
Qed.
Definition zpow2 (s : Z) : Z := if Z.ltb s 0 then 0 else Z.shiftl 1 s.
Lemma zpow2_eq : forall s, zpow2 s = (2 ^ s)%Z.
Proof.
  intros s. unfold zpow2. destruct (Z.ltb_spec s 0).
  - symmetry. apply Z.pow_neg_r. lia.
  - rewrite Z.shiftl_mul_pow2 by lia. lia.
Qed.
Definition zdivp (x s : Z) : Z := if Z.ltb s 0 then (x / 2 ^ s)%Z else Z.shiftr x s.
Lemma zdivp_eq : forall x s, zdivp x s = (x / 2 ^ s)%Z.
Proof. intros x s. unfold zdivp. destruct (Z.ltb_spec s 0); [reflexivity|]. apply Z.shiftr_div_pow2. lia. Qed.
Definition zmulp (x s : Z) : Z := if Z.ltb s 0 then (x * 2 ^ s)%Z else Z.shiftl x s.
Lemma zmulp_eq : forall x s, zmulp x s = (x * 2 ^ s)%Z.
Proof. intros x s. unfold zmulp. destruct (Z.ltb_spec s 0); [reflexivity|]. apply Z.shiftl_mul_pow2. lia. Qed.
Definition zmodp (x s : Z) : Z := if Z.ltb s 0 then (x mod 2 ^ s)%Z else Z.land x (Z.ones s).
Lemma zmodp_eq : forall x s, zmodp x s = (x mod 2 ^ s)%Z.
Proof. intros x s. unfold zmodp. destruct (Z.ltb_spec s 0); [reflexivity|]. apply Z.land_ones. lia. Qed.

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
  | EAlu ALU_SLL a (ELit s) => lscale (zpow2 (zmodp s 6)) (lin_of a)
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
  if coeffs_div (zpow2 k) (snd l) then Some (zmodp (fst l) k) else None.

(* [comment removed for export] *)
Definition shamt_of (e : expr) (bits : Z) : option Z :=
  match e with
  | ELit s => Some (zmodp s bits)
  | _ => lin_lowbits e bits
  end.

(* [comment removed for export] *)
Definition wrap64 (z : Z) : Z :=
  if (Z.leb 0 z && Z.ltb z two64)%bool then z else Z.land z ones64z.

Definition sx32 (r : Z) : Z :=
  if Z.ltb r 2147483648 then r else (r + 18446744069414584320)%Z.

(* [comment removed for export] *)
Definition zfast_ref (op : aluop) (x y : Z) : Z :=
  match op with
  | ALU_ADD => let t := (x + y)%Z in if Z.ltb t two64 then t else (t - two64)%Z
  | ALU_SUB => let t := (x - y)%Z in if Z.leb 0 t then t else (t + two64)%Z
  | ALU_AND => Z.land x y
  | ALU_OR => Z.lor x y
  | ALU_XOR => Z.lxor x y
  | ALU_SRL => Z.shiftr x (y mod 64)
  | ALU_SLL => ((Z.shiftl x (y mod 64)) mod two64)%Z
  | ALU_SLTU => if Z.ltb x y then 1%Z else 0%Z
  | _ => zalu op x y
  end.

Definition zfastw_ref (op : aluop) (x y : Z) : Z :=
  match op with
  | ALU_ADD => sx32 ((x + y) mod 4294967296)%Z
  | ALU_SUB => sx32 ((x - y) mod 4294967296)%Z
  | ALU_SRL => sx32 (Z.shiftr (x mod 4294967296) (y mod 32))
  | ALU_SLL => sx32 ((Z.shiftl (x mod 4294967296) (y mod 32)) mod 4294967296)%Z
  | _ => zaluw op x y
  end.

Definition zfastm_ref (op : mulop) (x y : Z) : Z :=
  match op with
  | M_MUL => ((x * y) mod two64)%Z
  | _ => zmd op x y
  end.

(* [comment removed for export] *)
Definition zfast (op : aluop) (x y : Z) : Z :=
  match op with
  | ALU_ADD => let t := (x + y)%Z in if Z.ltb t two64 then t else (t - two64)%Z
  | ALU_SUB => let t := (x - y)%Z in if Z.leb 0 t then t else (t + two64)%Z
  | ALU_AND => Z.land x y
  | ALU_OR => Z.lor x y
  | ALU_XOR => Z.lxor x y
  | ALU_SRL => Z.shiftr x (Z.land y 63)
  | ALU_SLL => Z.land (Z.shiftl x (Z.land y 63)) ones64z
  | ALU_SLTU => if Z.ltb x y then 1%Z else 0%Z
  | _ => zalu op x y
  end.

Definition zfastw (op : aluop) (x y : Z) : Z :=
  match op with
  | ALU_ADD => sx32 (Z.land (x + y) ones32z)
  | ALU_SUB => sx32 (Z.land (x - y) ones32z)
  | ALU_SRL => sx32 (Z.shiftr (Z.land x ones32z) (Z.land y 31))
  | ALU_SLL => sx32 (Z.land (Z.shiftl (Z.land x ones32z) (Z.land y 31)) ones32z)
  | _ => zaluw op x y
  end.

(* [comment removed for export] *)
Definition smag64 (x : Z) : Z := if Z.ltb x two63z then x else (x - two64)%Z.
Definition zmul64 (x y : Z) : Z :=
  let a := smag64 x in let b := smag64 y in
  Z.land (if Z.leb (Z.abs a) (Z.abs b) then a * b else b * a)%Z ones64z.
Definition zfastm (op : mulop) (x y : Z) : Z :=
  match op with
  | M_MUL => zmul64 x y
  | _ => zmd op x y
  end.
Lemma zmul64_eq : forall x y, zmul64 x y = Z.land (x * y) ones64z.
Proof.
  intros x y. unfold zmul64. rewrite !land_ones64z'.
  assert (Hs : forall u, exists q, smag64 u = (u + q * 2 ^ 64)%Z).
  { intros u. unfold smag64, two64. destruct (Z.ltb u two63z); [exists 0%Z | exists (-1)%Z]; lia. }
  destruct (Hs x) as [qx Hx]. destruct (Hs y) as [qy Hy]. rewrite Hx, Hy.
  replace (if (Z.abs (x + qx * 2 ^ 64) <=? Z.abs (y + qy * 2 ^ 64))%Z
           then ((x + qx * 2 ^ 64) * (y + qy * 2 ^ 64))%Z else ((y + qy * 2 ^ 64) * (x + qx * 2 ^ 64))%Z)
    with ((x + qx * 2 ^ 64) * (y + qy * 2 ^ 64))%Z by (destruct (Z.leb _ _); lia).
  replace ((x + qx * 2 ^ 64) * (y + qy * 2 ^ 64))%Z with (x * y + (x * qy + qx * y + qx * qy * 2 ^ 64) * 2 ^ 64)%Z by lia.
  apply Z.mod_add. lia.
Qed.

Lemma land63_eq : forall a, Z.land a 63 = (a mod 64)%Z.
Proof. intros a. exact (Z.land_ones a 6 ltac:(lia)). Qed.
Lemma land31_eq : forall a, Z.land a 31 = (a mod 32)%Z.
Proof. intros a. exact (Z.land_ones a 5 ltac:(lia)). Qed.
Lemma land_ones64z : forall a, Z.land a ones64z = (a mod two64)%Z.
Proof. intros a. exact (Z.land_ones a 64 ltac:(lia)). Qed.
Lemma land_ones32z : forall a, Z.land a ones32z = (a mod 4294967296)%Z.
Proof. intros a. exact (Z.land_ones a 32 ltac:(lia)). Qed.
Lemma zfast_ref_eq : forall op x y, zfast op x y = zfast_ref op x y.
Proof.
  intros op x y. destruct op; cbv beta iota zeta delta [zfast zfast_ref]; rewrite ?land63_eq, ?land_ones64z; reflexivity.
Qed.
Lemma zfastw_ref_eq : forall op x y, zfastw op x y = zfastw_ref op x y.
Proof.
  intros op x y. destruct op; cbv beta iota zeta delta [zfastw zfastw_ref]; rewrite ?land31_eq, ?land_ones32z; reflexivity.
Qed.
Lemma zfastm_ref_eq : forall op x y, zfastm op x y = zfastm_ref op x y.
Proof.
  intros op x y. destruct op; cbv beta iota zeta delta [zfastm zfastm_ref]; rewrite ?zmul64_eq, ?land_ones64z; reflexivity.
Qed.

(* [comment removed for export] *)
Definition zalu_lit (op : aluop) (x y : Z) : Z := zfast op (wrap64 x) (wrap64 y).
Definition zaluw_lit (op : aluop) (x y : Z) : Z := zfastw op (wrap64 x) (wrap64 y).
Definition zmd_lit (op : mulop) (x y : Z) : Z := zfastm op (wrap64 x) (wrap64 y).

Definition mkAlu (op : aluop) (a b : expr) : expr :=
  match is_lit a, is_lit b with
  | Some x, Some y => ELit (zalu_lit op x y)
  | _, _ =>
    match op with
    | ALU_ADD => unlin (ladd (lin_of a) (lin_of b))
    | ALU_SUB => unlin (ladd (lin_of a) (lscale (-1) (lin_of b)))
    | ALU_SLL => match shamt_of b 6 with
                 | Some s => unlin (lscale (zpow2 s) (lin_of a))
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
  | Some x, Some y => ELit (zaluw_lit op x y)
  | _, _ =>
      match op with
      | ALU_SLL | ALU_SRL | ALU_SRA =>
          match is_lit b with
          | Some _ => EAluw op a b
          | None => match shamt_of b 5 with
                    | Some s => match is_lit a with
                                | Some x => ELit (zaluw_lit op x s)
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
  | Some x, Some y => ELit (zmd_lit op x y)
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
| KImg  (lo hi : Z)                           (* [comment removed for export] *)
| KAlign (e : expr) (m : Z)                   (* [comment removed for export] *)
| KRange (e : expr) (lo hi : Z)               (* [comment removed for export] *)
| KWr (a : saddr) (n : expr)                  (* [comment removed for export] *)
| KDisj (a1 : saddr) (n1 : expr) (a2 : saddr) (n2 : expr).
                                              (* [comment removed for export] *)

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
  s_pc   : Z;
  s_regs : list expr;
  s_log  : list sentry;       (* [comment removed for export] *)
  s_know : list kentry;
  s_next : nat                (* [comment removed for export] *)
}.

Definition sset (ss : sym_state) (rd : reg) (e : expr) (npc : Z) : sym_state :=
  SS npc (if bv_eqb rd 0 then s_regs ss else sr_upd (s_regs ss) (ridx rd) e)
     (s_log ss) (s_know ss) (s_next ss).

Definition sjump (ss : sym_state) (npc : Z) : sym_state :=
  SS npc (s_regs ss) (s_log ss) (s_know ss) (s_next ss).

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
Definition two64m1 : Z := two64 - 1.   (* [comment removed for export] *)
Lemma zmod64_eq2 : forall z, zmod64 z = (z mod two64)%Z. Proof. exact zmod64_eq. Qed.
Lemma zdiv64_eq2 : forall z, zdiv64 z = (z / two64)%Z. Proof. exact zdiv64_eq. Qed.
Lemma zmodp_6 : forall s, zmodp s 6 = (s mod 64)%Z. Proof. intros s. exact (zmodp_eq s 6). Qed.
Lemma zmodp_5 : forall s, zmodp s 5 = (s mod 32)%Z. Proof. intros s. exact (zmodp_eq s 5). Qed.
(* [comment removed for export] *)
End FPW_1.

Ltac zhyg_in H := rewrite ?zmodp_6, ?zmodp_5, ?zmod64_eq2, ?zdiv64_eq2, ?zpow2_eq, ?zdivp_eq, ?zmulp_eq, ?zmodp_eq in H.
Ltac zhyg := rewrite ?zmodp_6, ?zmodp_5, ?zmod64_eq2, ?zdiv64_eq2, ?zpow2_eq, ?zdivp_eq, ?zmulp_eq, ?zmodp_eq.
Section FPW_2. Context {fx : PropExec.FPState}.


Definition clampi (r : Z * Z) : Z * Z :=
  let (lo, hi) := r in (Z.max lo 0, Z.min hi two64m1).

(* [comment removed for export] *)
Definition mask_cover (h : Z) : Z :=
  if Z.ltb h 0 then 0 else (zpow2 (Z.log2_up (h + 1)) - 1)%Z.

Definition lit_shamt (e : expr) : option Z :=
  match e with ELit s => Some (zmodp s 6) | _ => None end.

(* [comment removed for export] *)
Definition zsigned64 (v : Z) : Z := if Z.leb two63z v then (v - two64)%Z else v.

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
              | Some (lo, hi) =>
                  (* [comment removed for export] *)
                  let q := zdiv64 lo in
                  if Z.eqb q (zdiv64 hi) then Some ((lo - q * two64)%Z, (hi - q * two64)%Z) else None
              | None => None
              end) with
  | Some r => Some r
  | None =>
  match e with
  | ELit z => let v := zmod64 z in Some (v, v)
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
          (* [comment removed for export] *)
          match (match b, erange kn a with
                 | ELit m, Some (al, ah) =>
                     let m' := zmod64 m in
                     let j := Z.log2 (m' + 1) in
                     if (Z.eqb (m' + 1) (zpow2 j) && Z.leb (zdivp al j) (zdivp ah j) && Z.eqb (zdivp al j) (zdivp ah j))%bool
                     then Some (zmodp al j, zmodp ah j) else None
                 | _, _ => None
                 end) with
          | Some r => Some r
          | None =>
          match erange kn a, erange kn b with
          | Some (_, ah), Some (_, bh) => Some (0%Z, Z.min ah bh)
          | Some (_, ah), None => Some (0%Z, ah)
          | None, Some (_, bh) => Some (0%Z, bh)
          | None, None => None
          end
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
          | Some (al, ah), Some s => Some (zdivp al s, zdivp ah s)
          | _, _ => None
          end
      | ALU_SRA =>
          match erange kn a, lit_shamt b with
          | Some (al, ah), Some s =>
              if Z.ltb ah two63z then Some (zdivp al s, zdivp ah s) else None
          | _, _ => None
          end
      | ALU_SLL =>
          match erange kn a, lit_shamt b with
          | Some (al, ah), Some s =>
              let ahs := zmulp ah s in
              if Z.ltb ahs two64 then Some (zmulp al s, ahs) else None
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
              if (Z.ltb ah two63z && Z.ltb bh two63z)%bool then
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
              if (Z.leb 0 (al + bl') && Z.ltb (ah + bh') two31z)%bool
              then Some ((al + bl')%Z, (ah + bh')%Z) else None
          | _, _ => None
          end
      | ALU_SUB =>
          match erange kn a, erange kn b with
          | Some (al, ah), Some (bl, bh) =>
              if (Z.leb bh al && Z.ltb (ah - bl) two31z)%bool
              then Some ((al - bh)%Z, (ah - bl)%Z) else None
          | _, _ => None
          end
      | ALU_SLL =>
          match erange kn a, lit_shamt b with
          | Some (al, ah), Some s =>
              let s' := zmodp s 5 in
              let ahs := zmulp ah s' in
              if Z.ltb ahs two31z then Some (zmulp al s', ahs) else None
          | _, _ => None
          end
      | ALU_SRL =>
          match erange kn a, lit_shamt b with
          | Some (al, ah), Some s =>
              let s' := zmodp s 5 in
              if (Z.ltb ah two32z && (Z.ltb 0 s' || Z.ltb ah two31z))%bool
              then Some (zdivp al s', zdivp ah s') else None
          | _, _ => None
          end
      | ALU_SRA =>
          match erange kn a, lit_shamt b with
          | Some (al, ah), Some s =>
              let s' := zmodp s 5 in
              if Z.ltb ah two31z then Some (zdivp al s', zdivp ah s') else None
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
              then Some (zdiv64 (al * bl), zdiv64 (ah * bh)) else None
          | _, _ => None
          end
      | M_DIVU =>
          match erange kn a, b with
          | Some (al, ah), ELit d =>
              let d' := zmod64 d in
              if Z.ltb 0 d' then Some ((al / d')%Z, (ah / d')%Z) else None
          | _, _ => None
          end
      | M_REMU =>
          match erange kn a, b with
          | Some (al, ah), ELit d =>
              let d' := zmod64 d in
              if Z.ltb 0 d' then Some (0%Z, Z.min ah (d' - 1)) else None
          | _, _ => None
          end
      | _ => None
      end
  | EMdw _ _ _ => None
  | EExt sx lo n a =>
      let w := zpow2 (8 * Z.of_nat n) in
      if sx then
        match lo, erange kn a with
        | O, Some (al, ah) =>
            let w2 := zdivp w 1 in
            if (Z.leb 0 al && Z.ltb ah w2)%bool then Some (al, ah)
            else if (Nat.leb 1 n && Nat.leb n 8 && Z.leb w2 al && Z.ltb ah w)%bool
                 then Some ((two64 - w + al)%Z, (two64 - w + ah)%Z) else None
        | _, _ => None
        end
      else
        match lo, erange kn a with
        | O, Some (al, ah) =>
            if (Z.leb 0 al && Z.ltb ah w)%bool then Some (al, ah) else Some (0%Z, Z.min (w - 1) two64m1)
        | _, _ => Some (0%Z, Z.min (w - 1) two64m1)
        end
  | EBlob sx k i n =>
      if sx then None else Some (0%Z, Z.min (zpow2 (8 * Z.of_nat n) - 1) two64m1)%Z
  end
  end
  end
  end.

(* [comment removed for export] *)
Definition erange_fuel : nat := 64%nat.
End FPW_2.

Global Opaque erange_fuel.
(* [comment removed for export] *)
Section FPW_3. Context {fx : PropExec.FPState}.

Definition is_factb (K : kentry) : bool :=
  match K with KRange _ _ _ | KAlign _ _ | KDisj _ _ _ _ | KWr _ _ => true | _ => false end.
(* [comment removed for export] *)
Fixpoint all_factsb (kn : list kentry) : bool :=
  match kn with [] => true | K :: rest => if is_factb K then all_factsb rest else false end.
Definition facts_of (kn : list kentry) : list kentry :=
  if all_factsb kn then kn else List.filter is_factb kn.
Lemma all_factsb_filter : forall kn, all_factsb kn = true -> List.filter is_factb kn = kn.
Proof.
  induction kn as [|K rest IH]; cbn; [reflexivity|].
  destruct (is_factb K); [|discriminate]. intros H. rewrite (IH H). reflexivity.
Qed.
Lemma facts_of_filter : forall kn, facts_of kn = List.filter is_factb kn.
Proof.
  intros kn. unfold facts_of. destruct (all_factsb kn) eqn:E; [|reflexivity].
  symmetry. apply all_factsb_filter. exact E.
Qed.
Definition erange (kn : list kentry) (e : expr) : option (Z * Z) := erange_f erange_fuel (facts_of kn) e.


(* [comment removed for export] *)
Definition base_range (kn : list kentry) (e : expr) : option (Z * Z) :=
  match e with ELit z => let v := zmod64 z in Some (v, v) | _ => erange kn e end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint ctz_fuel (fuel : nat) (z : Z) : Z :=
  match fuel with
  | O => 0
  | S f => if Z.even z then (1 + ctz_fuel f (Z.div2 z))%Z else 0%Z
  end.
Definition ctz64 (z : Z) : Z := ctz_fuel 64 z.

(* [comment removed for export] *)
Fixpoint ealign0 (kn : list kentry) (e : expr) {struct e} : Z :=
  match find_align kn e with
  | Some m => if Z.ltb 0 m then ctz64 m else 0%Z
  | None =>
  match e with
  | ELit z => ctz64 (zmod64 z)
  | EAlu ALU_ADD a b => Z.min (ealign0 kn a) (ealign0 kn b)
  | EAlu ALU_SUB a b => Z.min (ealign0 kn a) (ealign0 kn b)
  | EAlu ALU_AND a b => Z.max (ealign0 kn a) (ealign0 kn b)
  | EAlu ALU_OR a b => Z.min (ealign0 kn a) (ealign0 kn b)
  | EAlu ALU_SLL a b =>
      match lit_shamt b with
      | Some s => Z.min (ealign0 kn a + s)%Z 64
      | None => 0%Z
      end
  | EMd M_MUL a b => Z.min (ealign0 kn a + ealign0 kn b)%Z 64
  (* [comment removed for export] *)
  | EAluw ALU_ADD a b => Z.min 32 (Z.min (ealign0 kn a) (ealign0 kn b))
  | EAluw ALU_SUB a b => Z.min 32 (Z.min (ealign0 kn a) (ealign0 kn b))
  | _ => 0%Z
  end
  end.


(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint lins_e (k : Z) (a : expr) (ts : list (Z * expr)) : list (Z * expr) :=
  match ts with
  | [] => if Z.eqb k 0 then [] else [(k, a)]
  | (k', a') :: rest =>
      if expr_eqb a a' then (let s := (k + k')%Z in if Z.eqb s 0 then rest else (s, a') :: rest)
      else (k', a') :: lins_e k a rest
  end.

Definition lsub_e (ts2 ts1 : list (Z * expr)) : list (Z * expr) :=
  fold_right (fun t acc => lins_e (- fst t)%Z (snd t) acc) ts2 ts1.

(* [comment removed for export] *)
Fixpoint find_and_atom (ts : list (Z * expr)) : option (expr * Z) :=
  match ts with
  | [] => None
  | (k, EAlu ALU_AND y (ELit mm)) :: r =>
      if (Z.eqb k 1 && Z.ltb 0 mm && Z.eqb (Z.land (mm + 1) mm) 0)%bool then Some (y, mm) else find_and_atom r
  | _ :: r => find_and_atom r
  end.

Definition pageup_low (e : expr) (m : Z) : option Z :=
  let l := lin_of e in
  match find_and_atom (snd l) with
  | Some (y, mm) =>
      if (Z.ltb 0 m && Z.eqb ((mm + 1) mod m) 0 && Z.leb (mm + 1) two64)%bool then
        let ly := lin_of y in
        let rest := lins_e (-1)%Z (EAlu ALU_AND y (ELit mm)) (snd l) in
        match fold_right (fun t acc => lins_e (1 * fst t)%Z (snd t) acc) (snd ly) rest with
        | [] => Some ((fst l + fst ly) mod m)%Z
        | _ => None
        end
      else None
  | None => None
  end.

Definition pageup_align (e : expr) : Z :=
  let l := lin_of e in
  match find_and_atom (snd l) with
  | Some (y, mm) =>
      let m := (mm + 1)%Z in let k := ctz64 m in
      if (Z.eqb m (zpow2 k) && Z.leb k 64)%bool then
        match pageup_low e m with Some 0%Z => k | _ => 0%Z end
      else 0%Z
  | None => 0%Z
  end.

Definition ealign (kn : list kentry) (e : expr) : Z := Z.max (ealign0 (facts_of kn) e) (pageup_align e).

(* [comment removed for export] *)
Definition lin_nowrap (kn : list kentry) (e : expr) : bool :=
  let l := lin_of e in
  match lin_range (erange kn) (fst l) (snd l) with
  | Some (lo, hi) => (Z.leb 0 lo && Z.ltb hi two64)%bool
  | None => false
  end.

(* [comment removed for export] *)
Definition srl_rem (e : expr) (m : Z) : expr := EAlu ALU_AND e (ELit (m - 1)%Z).

Fixpoint srl_expand (kn : list kentry) (ts : list (Z * expr)) : Z * list (Z * expr) :=
  match ts with
  | [] => (0%Z, [])
  | (k, a) :: rest =>
      let '(c, ts') := srl_expand kn rest in
      let keep := (c, lins_e k a ts') in
      match a with
      | EAlu ALU_SRL e (ELit s) =>
          let j := zmodp (zmod64 s) 6 in
          let m := zpow2 j in
          if (Z.eqb (zmodp k j) 0%Z && lin_nowrap kn e)%bool then
            let q := zdivp k j in
            let le := lin_of e in
            if Z.leb j (ealign kn e) then   (* [comment removed for export] *)
              ((c + q * fst le)%Z, fold_right (fun t acc => lins_e (q * fst t)%Z (snd t) acc) ts' (snd le))
            else
            ((c + q * fst le)%Z,
             lins_e (- q)%Z (srl_rem e m) (fold_right (fun t acc => lins_e (q * fst t)%Z (snd t) acc) ts' (snd le)))
          else keep
      | _ => keep
      end
  end.

(* [comment removed for export] *)
Definition sfact : Type := (list (Z * expr) * (Z * Z))%type.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition sum_fact_x (allkn : list kentry) (ts : list (Z * expr)) (lo hi : Z) : list sfact :=
  let '(c2, ts2) := srl_expand allkn ts in
  match ts2 with
  | _ :: _ => if Z.eqb c2 0 then [] else [(ts2, ((lo - c2)%Z, (hi - c2)%Z))]
  | [] => []
  end.

(* [comment removed for export] *)
Definition fact_nowrap (allkn : list kentry) (e : expr) (hi : Z) : bool :=
  let l := lin_of e in
  match lin_range (erange allkn) (fst l) (snd l) with
  | Some (a, b) => (Z.ltb b two64 && Z.ltb hi (a + two64))%bool
  | None => false
  end.

Fixpoint sum_facts (allkn kn : list kentry) : list sfact :=
  match kn with
  | [] => []
  | KRange e lo hi :: rest =>
      match e with
      | EVar _ => sum_facts allkn rest
      | _ =>
        match lin_of e with
        | (c, (_ :: _ :: _) as ts) =>
            if fact_nowrap allkn e hi then (ts, ((lo - c)%Z, (hi - c)%Z)) :: sum_fact_x allkn ts (lo - c)%Z (hi - c)%Z ++ sum_facts allkn rest
            else sum_facts allkn rest
        | _ => sum_facts allkn rest
        end
      end
  | _ :: rest => sum_facts allkn rest
  end.

(* [comment removed for export] *)
Fixpoint coef_of (a : expr) (ts : list (Z * expr)) : Z :=
  match ts with
  | [] => 0
  | (k, a') :: r => if expr_eqb a a' then k else coef_of a r
  end.

(* [comment removed for export] *)
Fixpoint fact_quot (fts ts : list (Z * expr)) (acc : option Z) : option Z :=
  match fts with
  | [] => acc
  | (k, a) :: r =>
      if Z.eqb k 0 then None else
      let K := coef_of a ts in
      if Z.eqb K 0 then None else
      if negb (Z.eqb (K mod k) 0) then None else
      let q := (K / k)%Z in
      match acc with
      | None => fact_quot r ts (Some q)
      | Some q0 => if Z.eqb q0 q then fact_quot r ts acc else None
      end
  end.

Definition sub_fact (q : Z) (fts ts : list (Z * expr)) : list (Z * expr) :=
  fold_right (fun t acc => lins_e (- (q * fst t))%Z (snd t) acc) ts fts.

(* [comment removed for export] *)
Fixpoint sum_subst (fs : list sfact) (ts : list (Z * expr)) (lo hi : Z) (hit : bool)
  : list (Z * expr) * (Z * Z) * bool :=
  match fs with
  | [] => (ts, (lo, hi), hit)
  | (fts, (flo, fhi)) :: r =>
      match fact_quot fts ts None with
      | Some q =>
          let ts' := sub_fact q fts ts in
          if Z.leb 0 q then sum_subst r ts' (lo + q * flo)%Z (hi + q * fhi)%Z true
          else sum_subst r ts' (lo + q * fhi)%Z (hi + q * flo)%Z true
      | None => sum_subst r ts lo hi hit
      end
  end.

Definition lin_test_rel (kn : list kentry) (c : Z) (ts : list (Z * expr)) (test : Z -> Z -> bool) : bool :=
  match sum_facts kn kn with
  | [] => false
  | fs =>
      match sum_subst fs ts 0 0 false with
      | (ts', (lo0, hi0), true) =>
          match lin_range (erange kn) c ts' with
          | Some (lo, hi) => test (lo + lo0)%Z (hi + hi0)%Z
          | None => false
          end
      | _ => false
      end
  end.

Definition lin_test (kn : list kentry) (c : Z) (ts : list (Z * expr)) (test : Z -> Z -> bool) : bool :=
  match lin_range (erange kn) c ts with
  | Some (lo, hi) => if test lo hi then true else lin_test_rel kn c ts test
  | None => lin_test_rel kn c ts test
  end.

(* [comment removed for export] *)
Definition lin_nowrapR (kn : list kentry) (e : expr) : bool :=
  let l := lin_of e in
  let '(c2, t2) := srl_expand kn (snd l) in            (* [comment removed for export] *)
  lin_test kn (fst l + c2)%Z t2 (fun lo hi => (Z.leb 0 lo && Z.ltb hi two64)%bool).

(* [comment removed for export] *)
Fixpoint mentions_var (v : nat) (e : expr) : bool :=
  match e with
  | ELit _ => false
  | EVar w => Nat.eqb v w
  | EAlu _ a b | EAluw _ a b | EMd _ a b | EMdw _ a b => if mentions_var v a then true else mentions_var v b
  | EExt _ _ _ a => mentions_var v a
  | EBlob _ _ _ _ => false
  end.
Fixpoint shares_var (e1 e2 : expr) : bool :=
  match e2 with
  | ELit _ => false
  | EVar w => mentions_var w e1
  | EAlu _ a b | EAluw _ a b | EMd _ a b | EMdw _ a b => if shares_var e1 a then true else shares_var e1 b
  | EExt _ _ _ a => shares_var e1 a
  | EBlob _ _ _ _ => false
  end.
Fixpoint novars (e : expr) : bool :=
  match e with
  | ELit _ => true
  | EVar _ => false
  | EAlu _ a b | EAluw _ a b | EMd _ a b | EMdw _ a b => if novars a then novars b else false
  | EExt _ _ _ a => novars a
  | EBlob _ _ _ _ => true
  end.
(* [comment removed for export] *)
Definition related (b1 b2 : expr) : bool :=
  if shares_var b1 b2 then true else novars b2.

(* [comment removed for export] *)
Definition lin_apart0 (kn : list kentry) (b1 : expr) (k1 n1 : Z) (b2 : expr) (k2 n2 : Z) : bool :=
  (lin_nowrapR kn b1 && lin_nowrapR kn b2 &&
   let l1 := lin_of b1 in let l2 := lin_of b2 in
   lin_test kn (fst l2 + k2 - fst l1 - k1)%Z (lsub_e (snd l2) (snd l1))
            (fun lo hi => (Z.leb n1 lo || Z.leb hi (- n2))%bool))%bool.
Definition lin_apart (kn : list kentry) (b1 : expr) (k1 n1 : Z) (b2 : expr) (k2 n2 : Z) : bool :=
  if shares_var b1 b2 then lin_apart0 kn b1 k1 n1 b2 k2 n2 else false.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition zlit64 (z : Z) : Z := if (Z.leb 0 z && Z.ltb z two64)%bool then z else Z.land z ones64z.

(* [comment removed for export] *)
Definition lin_brange (kn : list kentry) (e : expr) : option (Z * Z) :=
  let l := lin_of e in
  match sum_facts kn kn with
  | [] => None
  | fs =>
      match sum_subst fs (snd l) 0 0 false with
      | (ts', (lo0, hi0), true) =>
          match lin_range (erange kn) (fst l) ts' with
          | Some (lo, hi) =>
              let lo' := (lo + lo0)%Z in let hi' := (hi + hi0)%Z in
              if (Z.leb 0 lo' && Z.ltb hi' two64)%bool then Some (lo', hi') else None
          | None => None
          end
      | _ => None
      end
  end.

Definition xlo (kn : list kentry) (e : expr) : option Z :=
  match e with
  | ELit z => Some (zlit64 z)
  | _ => match erange kn e with
         | Some (lo, _) => Some lo
         | None => match lin_brange kn e with Some (lo, _) => Some lo | None => None end
         end
  end.
Definition xhi (kn : list kentry) (e : expr) : option Z :=
  match e with
  | ELit z => Some (zlit64 z)
  | _ => match erange kn e with
         | Some (_, hi) => Some hi
         | None => match lin_brange kn e with Some (_, hi) => Some hi | None => None end
         end
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition xterms := list (expr * Z).

Fixpoint xt_nowrap (kn : list kentry) (ts : xterms) : bool :=
  match ts with [] => true | (e, _) :: r => lin_nowrapR kn e && xt_nowrap kn r end.
Fixpoint xt_const (ts : xterms) : Z :=
  match ts with [] => 0 | (e, k) :: r => (fst (lin_of e) + k + xt_const r)%Z end.
Fixpoint xt_lin (ts : xterms) : list (Z * expr) :=
  match ts with [] => [] | (e, _) :: r => fold_right (fun t acc => lins_e (fst t) (snd t) acc) (xt_lin r) (snd (lin_of e)) end.

(* [comment removed for export] *)
Definition lin_ge0 (kn : list kentry) (pos neg : xterms) : bool :=
  (xt_nowrap kn pos && xt_nowrap kn neg &&
   (* [comment removed for export] *)
   (if lin_test kn (xt_const pos - xt_const neg)%Z (lsub_e (xt_lin pos) (xt_lin neg)) (fun lo _ => Z.leb 0 lo) then true
    else let '(c2, t2) := srl_expand kn (lsub_e (xt_lin pos) (xt_lin neg)) in
         lin_test kn (xt_const pos - xt_const neg + c2)%Z t2 (fun lo _ => Z.leb 0 lo)))%bool.

(* [comment removed for export] *)
Definition xinside0 (kn : list kentry) (b1 : expr) (k1 : Z) (n1 : expr) (b2 : expr) (k2 : Z) (n2 : expr) : bool :=
  if lin_ge0 kn [(b1, k1)] [(b2, k2)] then lin_ge0 kn [(b2, k2); (n2, 0%Z)] [(b1, k1); (n1, 0%Z)] else false.
(* [comment removed for export] *)
Definition xinside_num (kn : list kentry) (b1 : expr) (k1 : Z) (n1 : expr) (b2 : expr) (k2 : Z) (n2 : expr) : bool :=
  match xlo kn b2, xhi kn b2 with
  | Some lo2, Some hi2 =>
      if Z.eqb lo2 hi2 then
        match base_range kn b1, xhi kn n1, xlo kn n2 with
        | Some (lo1, hi1), Some h1, Some l2 => Z.leb (lo2 + k2) (lo1 + k1) && Z.leb (hi1 + k1 + h1) (lo2 + k2 + l2)
        | _, _, _ => false
        end
      else false
  | _, _ => false
  end.
Definition xinside (kn : list kentry) (b1 : expr) (k1 : Z) (n1 : expr) (b2 : expr) (k2 : Z) (n2 : expr) : bool :=
  if shares_var b1 b2 then xinside0 kn b1 k1 n1 b2 k2 n2
  else if novars b2 then xinside_num kn b1 k1 n1 b2 k2 n2 else false.


(* [comment removed for export] *)
Definition sub_itv (allkn : list kentry) (b : expr) (k n : Z) (c : saddr) (m : expr) : bool :=
  if (if (expr_eqb b (a_base c) && Z.leb (a_off c) k)%bool then
        match xlo allkn m with Some ml => Z.leb (k + n) (a_off c + ml) | None => false end
      else false)
  then true
  else (* [comment removed for export] *)
    if (Z.leb 0 n && Z.ltb n two64)%bool then xinside allkn b k (ELit n) (a_base c) (a_off c) m else false.

(* [comment removed for export] *)
Fixpoint kdisj_apart (allkn kn : list kentry) (b1 : expr) (k1 n1 : Z) (b2 : expr) (k2 n2 : Z) : bool :=
  match kn with
  | [] => false
  | KDisj c1 m1 c2 m2 :: rest =>
      if (if sub_itv allkn b1 k1 n1 c1 m1 then sub_itv allkn b2 k2 n2 c2 m2 else false) then true
      else if (if sub_itv allkn b1 k1 n1 c2 m2 then sub_itv allkn b2 k2 n2 c1 m1 else false) then true
      else kdisj_apart allkn rest b1 k1 n1 b2 k2 n2
  | _ :: rest => kdisj_apart allkn rest b1 k1 n1 b2 k2 n2
  end.

Definition ranges_apart (kn : list kentry) (b1 : expr) (k1 n1 : Z) (b2 : expr) (k2 n2 : Z) : bool :=
  if (match base_range kn b1, base_range kn b2 with
      | Some (lo1, hi1), Some (lo2, hi2) =>
          (Z.leb (hi1 + k1 + n1) (lo2 + k2) || Z.leb (hi2 + k2 + n2) (lo1 + k1))%bool
      | _, _ => false
      end) then true
  else if kdisj_apart kn kn b1 k1 n1 b2 k2 n2 then true
  else lin_apart kn b1 k1 n1 b2 k2 n2.

Definition sub_itv_x (kn : list kentry) (b : expr) (k : Z) (n : expr) (c : saddr) (m : expr) : bool :=
  xinside kn b k n (a_base c) (a_off c) m.

Fixpoint kdisj_apart_x (allkn kn : list kentry) (b1 : expr) (k1 : Z) (n1 : expr) (b2 : expr) (k2 : Z) (n2 : expr) : bool :=
  match kn with
  | [] => false
  | KDisj c1 m1 c2 m2 :: rest =>
      if (if sub_itv_x allkn b1 k1 n1 c1 m1 then sub_itv_x allkn b2 k2 n2 c2 m2 else false) then true
      else if (if sub_itv_x allkn b1 k1 n1 c2 m2 then sub_itv_x allkn b2 k2 n2 c1 m1 else false) then true
      else kdisj_apart_x allkn rest b1 k1 n1 b2 k2 n2
  | _ :: rest => kdisj_apart_x allkn rest b1 k1 n1 b2 k2 n2
  end.

(* [comment removed for export] *)
Definition ranges_apart_x (kn : list kentry) (b1 : expr) (k1 : Z) (n1 : expr) (b2 : expr) (k2 : Z) (n2 : expr) : bool :=
  match n1, n2 with
  | ELit z1, ELit z2 => ranges_apart kn b1 k1 (zlit64 z1) b2 k2 (zlit64 z2)
  | _, _ =>
    if (match base_range kn b1, base_range kn b2, xhi kn n1, xhi kn n2 with
        | Some (lo1, hi1), Some (lo2, hi2), Some h1, Some h2 =>
            (Z.leb (hi1 + k1 + h1) (lo2 + k2) || Z.leb (hi2 + k2 + h2) (lo1 + k1))%bool
        | _, _, _, _ => false
        end) then true
    else if kdisj_apart_x kn kn b1 k1 n1 b2 k2 n2 then true
    else if negb (shares_var b1 b2) then false
    else if lin_ge0 kn [(b2, k2)] [(b1, k1); (n1, 0%Z)] then true
    else lin_ge0 kn [(b1, k1)] [(b2, k2); (n2, 0%Z)]
  end.

(* [comment removed for export] *)
Definition lin_test_relF (fs : list sfact) (kn : list kentry) (c : Z) (ts : list (Z * expr))
           (test : Z -> Z -> bool) : bool :=
  match fs with
  | [] => false
  | _ =>
      match sum_subst fs ts 0 0 false with
      | (ts', (lo0, hi0), true) =>
          match lin_range (erange kn) c ts' with
          | Some (lo, hi) => test (lo + lo0)%Z (hi + hi0)%Z
          | None => false
          end
      | _ => false
      end
  end.

Definition lin_testF (fs : list sfact) (kn : list kentry) (c : Z) (ts : list (Z * expr)) (test : Z -> Z -> bool) : bool :=
  match lin_range (erange kn) c ts with
  | Some (lo, hi) => if test lo hi then true else lin_test_relF fs kn c ts test
  | None => lin_test_relF fs kn c ts test
  end.

Definition lin_nowrapRF (fs : list sfact) (kn : list kentry) (e : expr) : bool :=
  let l := lin_of e in
  let '(c2, t2) := srl_expand kn (snd l) in
  lin_testF fs kn (fst l + c2)%Z t2 (fun lo hi => (Z.leb 0 lo && Z.ltb hi two64)%bool).

Fixpoint xt_nowrapF (fs : list sfact) (kn : list kentry) (ts : xterms) : bool :=
  match ts with
  | [] => true
  | (e, _) :: r => if lin_nowrapRF fs kn e then xt_nowrapF fs kn r else false
  end.

Definition lin_ge0F (fs : list sfact) (kn : list kentry) (pos neg : xterms) : bool :=
  if xt_nowrapF fs kn pos then
    if xt_nowrapF fs kn neg then
      let d := lsub_e (xt_lin pos) (xt_lin neg) in
      let c := (xt_const pos - xt_const neg)%Z in
      if lin_testF fs kn c d (fun lo _ => Z.leb 0 lo) then true
      else let '(c2, t2) := srl_expand kn d in
           lin_testF fs kn (c + c2)%Z t2 (fun lo _ => Z.leb 0 lo)
    else false
  else false.

Definition lin_apart0F (fs : list sfact) (kn : list kentry) (b1 : expr) (k1 n1 : Z) (b2 : expr) (k2 n2 : Z) : bool :=
  if lin_nowrapRF fs kn b1 then
    if lin_nowrapRF fs kn b2 then
      let l1 := lin_of b1 in let l2 := lin_of b2 in
      lin_testF fs kn (fst l2 + k2 - fst l1 - k1)%Z (lsub_e (snd l2) (snd l1))
                (fun lo hi => (Z.leb n1 lo || Z.leb hi (- n2))%bool)
    else false
  else false.
Definition lin_apartF (fs : list sfact) (kn : list kentry) (b1 : expr) (k1 n1 : Z) (b2 : expr) (k2 n2 : Z) : bool :=
  if shares_var b1 b2 then lin_apart0F fs kn b1 k1 n1 b2 k2 n2 else false.

Definition lin_brangeF (fs : list sfact) (kn : list kentry) (e : expr) : option (Z * Z) :=
  let l := lin_of e in
  match fs with
  | [] => None
  | _ =>
      match sum_subst fs (snd l) 0 0 false with
      | (ts', (lo0, hi0), true) =>
          match lin_range (erange kn) (fst l) ts' with
          | Some (lo, hi) =>
              let lo' := (lo + lo0)%Z in let hi' := (hi + hi0)%Z in
              if (Z.leb 0 lo' && Z.ltb hi' two64)%bool then Some (lo', hi') else None
          | None => None
          end
      | _ => None
      end
  end.

Definition xloF (fs : list sfact) (kn : list kentry) (e : expr) : option Z :=
  match e with
  | ELit z => Some (zlit64 z)
  | _ => match erange kn e with
         | Some (lo, _) => Some lo
         | None => match lin_brangeF fs kn e with Some (lo, _) => Some lo | None => None end
         end
  end.
Definition xhiF (fs : list sfact) (kn : list kentry) (e : expr) : option Z :=
  match e with
  | ELit z => Some (zlit64 z)
  | _ => match erange kn e with
         | Some (_, hi) => Some hi
         | None => match lin_brangeF fs kn e with Some (_, hi) => Some hi | None => None end
         end
  end.

Definition xinside0F (fs : list sfact) (kn : list kentry) (b1 : expr) (k1 : Z) (n1 : expr) (b2 : expr) (k2 : Z) (n2 : expr) : bool :=
  if lin_ge0F fs kn [(b1, k1)] [(b2, k2)] then lin_ge0F fs kn [(b2, k2); (n2, 0%Z)] [(b1, k1); (n1, 0%Z)] else false.
Definition xinside_numF (fs : list sfact) (kn : list kentry) (b1 : expr) (k1 : Z) (n1 : expr) (b2 : expr) (k2 : Z) (n2 : expr) : bool :=
  match xloF fs kn b2, xhiF fs kn b2 with
  | Some lo2, Some hi2 =>
      if Z.eqb lo2 hi2 then
        match base_range kn b1, xhiF fs kn n1, xloF fs kn n2 with
        | Some (lo1, hi1), Some h1, Some l2 => Z.leb (lo2 + k2) (lo1 + k1) && Z.leb (hi1 + k1 + h1) (lo2 + k2 + l2)
        | _, _, _ => false
        end
      else false
  | _, _ => false
  end.
Definition xinsideF (fs : list sfact) (kn : list kentry) (b1 : expr) (k1 : Z) (n1 : expr) (b2 : expr) (k2 : Z) (n2 : expr) : bool :=
  if shares_var b1 b2 then xinside0F fs kn b1 k1 n1 b2 k2 n2
  else if novars b2 then xinside_numF fs kn b1 k1 n1 b2 k2 n2 else false.

Definition sub_itvF (fs : list sfact) (allkn : list kentry) (b : expr) (k n : Z) (c : saddr) (m : expr) : bool :=
  if (if (expr_eqb b (a_base c) && Z.leb (a_off c) k)%bool then
        match xloF fs allkn m with Some ml => Z.leb (k + n) (a_off c + ml) | None => false end
      else false)
  then true
  else if (Z.leb 0 n && Z.ltb n two64)%bool then xinsideF fs allkn b k (ELit n) (a_base c) (a_off c) m else false.

Fixpoint kdisj_apartF (fs : list sfact) (allkn kn : list kentry) (b1 : expr) (k1 n1 : Z) (b2 : expr) (k2 n2 : Z) : bool :=
  match kn with
  | [] => false
  | KDisj c1 m1 c2 m2 :: rest =>
      if (if sub_itvF fs allkn b1 k1 n1 c1 m1 then sub_itvF fs allkn b2 k2 n2 c2 m2 else false) then true
      else if (if sub_itvF fs allkn b1 k1 n1 c2 m2 then sub_itvF fs allkn b2 k2 n2 c1 m1 else false) then true
      else kdisj_apartF fs allkn rest b1 k1 n1 b2 k2 n2
  | _ :: rest => kdisj_apartF fs allkn rest b1 k1 n1 b2 k2 n2
  end.

Definition ranges_apartF (fs : list sfact) (kn : list kentry) (b1 : expr) (k1 n1 : Z) (b2 : expr) (k2 n2 : Z) : bool :=
  if (match base_range kn b1, base_range kn b2 with
      | Some (lo1, hi1), Some (lo2, hi2) =>
          (Z.leb (hi1 + k1 + n1) (lo2 + k2) || Z.leb (hi2 + k2 + n2) (lo1 + k1))%bool
      | _, _ => false
      end) then true
  else if kdisj_apartF fs kn kn b1 k1 n1 b2 k2 n2 then true
  else lin_apartF fs kn b1 k1 n1 b2 k2 n2.

Definition sub_itv_xF (fs : list sfact) (kn : list kentry) (b : expr) (k : Z) (n : expr) (c : saddr) (m : expr) : bool :=
  xinsideF fs kn b k n (a_base c) (a_off c) m.

Fixpoint kdisj_apart_xF (fs : list sfact) (allkn kn : list kentry) (b1 : expr) (k1 : Z) (n1 : expr) (b2 : expr) (k2 : Z) (n2 : expr) : bool :=
  match kn with
  | [] => false
  | KDisj c1 m1 c2 m2 :: rest =>
      if (if sub_itv_xF fs allkn b1 k1 n1 c1 m1 then sub_itv_xF fs allkn b2 k2 n2 c2 m2 else false) then true
      else if (if sub_itv_xF fs allkn b1 k1 n1 c2 m2 then sub_itv_xF fs allkn b2 k2 n2 c1 m1 else false) then true
      else kdisj_apart_xF fs allkn rest b1 k1 n1 b2 k2 n2
  | _ :: rest => kdisj_apart_xF fs allkn rest b1 k1 n1 b2 k2 n2
  end.

Definition ranges_apart_xF (fs : list sfact) (kn : list kentry) (b1 : expr) (k1 : Z) (n1 : expr) (b2 : expr) (k2 : Z) (n2 : expr) : bool :=
  match n1, n2 with
  | ELit z1, ELit z2 => ranges_apartF fs kn b1 k1 (zlit64 z1) b2 k2 (zlit64 z2)
  | _, _ =>
    if (match base_range kn b1, base_range kn b2, xhiF fs kn n1, xhiF fs kn n2 with
        | Some (lo1, hi1), Some (lo2, hi2), Some h1, Some h2 =>
            (Z.leb (hi1 + k1 + h1) (lo2 + k2) || Z.leb (hi2 + k2 + h2) (lo1 + k1))%bool
        | _, _, _, _ => false
        end) then true
    else if kdisj_apart_xF fs kn kn b1 k1 n1 b2 k2 n2 then true
    else if negb (shares_var b1 b2) then false
    else if lin_ge0F fs kn [(b2, k2)] [(b1, k1); (n1, 0%Z)] then true
    else lin_ge0F fs kn [(b1, k1)] [(b2, k2); (n2, 0%Z)]
  end.

(* [comment removed for export] *)
Fixpoint disj_sidesF (fs : list sfact) (allkn kn : list kentry) (b1 : expr) (k1 n1 : Z) : list (saddr * expr) :=
  match kn with
  | [] => []
  | KDisj c1 m1 c2 m2 :: rest =>
      let r := disj_sidesF fs allkn rest b1 k1 n1 in
      let r1 := if sub_itvF fs allkn b1 k1 n1 c2 m2 then (c1, m1) :: r else r in
      if sub_itvF fs allkn b1 k1 n1 c1 m1 then (c2, m2) :: r1 else r1
  | _ :: rest => disj_sidesF fs allkn rest b1 k1 n1
  end.
Fixpoint in_sidesF (fs : list sfact) (allkn : list kentry) (D : list (saddr * expr)) (b2 : expr) (k2 n2 : Z) : bool :=
  match D with
  | [] => false
  | (c, m) :: r => if sub_itvF fs allkn b2 k2 n2 c m then true else in_sidesF fs allkn r b2 k2 n2
  end.
Lemma in_sidesF_disj : forall fs allkn kn b1 k1 n1 b2 k2 n2,
  in_sidesF fs allkn (disj_sidesF fs allkn kn b1 k1 n1) b2 k2 n2 = kdisj_apartF fs allkn kn b1 k1 n1 b2 k2 n2.
Proof.
  intros fs allkn kn b1 k1 n1 b2 k2 n2. induction kn as [|K rest IH]; [reflexivity|].
  destruct K as [| | | | | | |c1 m1 c2 m2]; cbn [disj_sidesF kdisj_apartF]; try exact IH.
  destruct (sub_itvF fs allkn b1 k1 n1 c1 m1), (sub_itvF fs allkn b1 k1 n1 c2 m2); cbn [in_sidesF];
    destruct (sub_itvF fs allkn b2 k2 n2 c2 m2) eqn:E2, (sub_itvF fs allkn b2 k2 n2 c1 m1) eqn:E1;
    rewrite ?E1, ?E2, ?IH; reflexivity.
Qed.
(* [comment removed for export] *)
Definition lthr : Type := option (Z * Z).
Definition mk_lthr (kn : list kentry) (b1 : expr) (k1 n1 : Z) : lthr :=
  match base_range kn b1 with Some (lo1, hi1) => Some ((hi1 + k1 + n1)%Z, (lo1 + k1)%Z) | None => None end.
Definition lthr_test (t : lthr) (br2 : option (Z * Z)) (k2 n2 : Z) : bool :=
  match t, br2 with
  | Some (A, B), Some (lo2, hi2) => (Z.leb A (lo2 + k2) || Z.leb (hi2 + k2 + n2) B)%bool
  | _, _ => false
  end.
Lemma lthr_test_eq : forall kn b1 k1 n1 b2 k2 n2,
  lthr_test (mk_lthr kn b1 k1 n1) (base_range kn b2) k2 n2 =
  match base_range kn b1, base_range kn b2 with
  | Some (lo1, hi1), Some (lo2, hi2) => (Z.leb (hi1 + k1 + n1) (lo2 + k2) || Z.leb (hi2 + k2 + n2) (lo1 + k1))%bool
  | _, _ => false
  end.
Proof. intros. unfold lthr_test, mk_lthr. destruct (base_range kn b1) as [[lo1 hi1]|]; [reflexivity|]. destruct (base_range kn b2) as [[? ?]|]; reflexivity. Qed.
(* [comment removed for export] *)
Definition mk_ethr (t : lthr) (br2 : option (Z * Z)) : option (Z * Z) :=
  match t, br2 with
  | Some (A, B), Some (lo2, hi2) => Some ((A - lo2)%Z, (B - hi2)%Z)
  | _, _ => None
  end.
Definition ethr_test (et : option (Z * Z)) (k2 n2 : Z) : bool :=
  match et with Some (tA, tB) => (Z.leb tA k2 || Z.leb (k2 + n2) tB)%bool | None => false end.
Lemma Zleb_eqb_iff : forall a b c d, ((a <= b)%Z <-> (c <= d)%Z) -> Z.leb a b = Z.leb c d.
Proof.
  intros a b c d H. destruct (Z.leb_spec a b), (Z.leb_spec c d); try reflexivity; exfalso; lia.
Qed.
Lemma ethr_test_eq : forall t br2 k2 n2, ethr_test (mk_ethr t br2) k2 n2 = lthr_test t br2 k2 n2.
Proof.
  intros [[A B]|] [[lo2 hi2]|] k2 n2; try reflexivity. cbn [mk_ethr ethr_test lthr_test].
  rewrite (Zleb_eqb_iff (A - lo2) k2 A (lo2 + k2)) by lia.
  rewrite (Zleb_eqb_iff (k2 + n2) (B - hi2) (hi2 + k2 + n2) B) by lia. reflexivity.
Qed.
(* [comment removed for export] *)
Definition ranges_apart_restF (fs : list sfact) (kn : list kentry) (D : list (saddr * expr)) (b1 : expr) (k1 n1 : Z)
           (b2 : expr) (k2 n2 : Z) : bool :=
  if in_sidesF fs kn D b2 k2 n2 then true else lin_apartF fs kn b1 k1 n1 b2 k2 n2.
Lemma ranges_apart_stagedF_eq : forall fs kn b1 k1 n1 b2 k2 n2,
  (if lthr_test (mk_lthr kn b1 k1 n1) (base_range kn b2) k2 n2 then true
   else ranges_apart_restF fs kn (disj_sidesF fs kn kn b1 k1 n1) b1 k1 n1 b2 k2 n2) = ranges_apartF fs kn b1 k1 n1 b2 k2 n2.
Proof. intros. rewrite lthr_test_eq. unfold ranges_apart_restF, ranges_apartF. rewrite in_sidesF_disj. reflexivity. Qed.
(* [comment removed for export] *)
Fixpoint lbr_lookup (c : list (expr * option (Z * Z))) (b : expr) : option (option (Z * Z)) :=
  match c with
  | [] => None
  | (b', r) :: rest => if expr_eqb b b' then Some r else lbr_lookup rest b
  end.

(* [comment removed for export] *)
Definition SFS (kn : list kentry) : list sfact := sum_facts kn kn.

Lemma lin_test_relF_eq : forall kn c ts test, lin_test_relF (SFS kn) kn c ts test = lin_test_rel kn c ts test.
Proof. intros. unfold lin_test_relF, lin_test_rel, SFS. destruct (sum_facts kn kn); reflexivity. Qed.
Lemma lin_testF_eq : forall kn c ts test, lin_testF (SFS kn) kn c ts test = lin_test kn c ts test.
Proof. intros. unfold lin_testF, lin_test. rewrite !lin_test_relF_eq. reflexivity. Qed.
Lemma lin_nowrapRF_eq : forall kn e, lin_nowrapRF (SFS kn) kn e = lin_nowrapR kn e.
Proof. intros. unfold lin_nowrapRF, lin_nowrapR. destruct (srl_expand kn (snd (lin_of e))). apply lin_testF_eq. Qed.
Lemma xt_nowrapF_eq : forall kn ts, xt_nowrapF (SFS kn) kn ts = xt_nowrap kn ts.
Proof.
  intros kn ts. induction ts as [|[e k] r IH]; [reflexivity|]. cbn [xt_nowrapF xt_nowrap].
  rewrite lin_nowrapRF_eq, IH. destruct (lin_nowrapR kn e); reflexivity.
Qed.
Lemma lin_ge0F_eq : forall kn pos neg, lin_ge0F (SFS kn) kn pos neg = lin_ge0 kn pos neg.
Proof.
  intros. unfold lin_ge0F, lin_ge0. rewrite !xt_nowrapF_eq, !lin_testF_eq.
  destruct (xt_nowrap kn pos), (xt_nowrap kn neg); cbn [andb]; try reflexivity.
  destruct (srl_expand kn (lsub_e (xt_lin pos) (xt_lin neg))). rewrite lin_testF_eq. reflexivity.
Qed.
Lemma lin_apart0F_eq : forall kn b1 k1 n1 b2 k2 n2, lin_apart0F (SFS kn) kn b1 k1 n1 b2 k2 n2 = lin_apart0 kn b1 k1 n1 b2 k2 n2.
Proof.
  intros. unfold lin_apart0F, lin_apart0. rewrite !lin_nowrapRF_eq, !lin_testF_eq.
  destruct (lin_nowrapR kn b1), (lin_nowrapR kn b2); reflexivity.
Qed.
Lemma lin_apartF_eq : forall kn b1 k1 n1 b2 k2 n2, lin_apartF (SFS kn) kn b1 k1 n1 b2 k2 n2 = lin_apart kn b1 k1 n1 b2 k2 n2.
Proof. intros. unfold lin_apartF, lin_apart. rewrite lin_apart0F_eq. reflexivity. Qed.
Lemma lin_brangeF_eq : forall kn e, lin_brangeF (SFS kn) kn e = lin_brange kn e.
Proof. intros. unfold lin_brangeF, lin_brange, SFS. destruct (sum_facts kn kn); reflexivity. Qed.
Lemma xloF_eq : forall kn e, xloF (SFS kn) kn e = xlo kn e.
Proof. intros. unfold xloF, xlo. rewrite lin_brangeF_eq. reflexivity. Qed.
Lemma xhiF_eq : forall kn e, xhiF (SFS kn) kn e = xhi kn e.
Proof. intros. unfold xhiF, xhi. rewrite lin_brangeF_eq. reflexivity. Qed.
Lemma xinside0F_eq : forall kn b1 k1 n1 b2 k2 n2, xinside0F (SFS kn) kn b1 k1 n1 b2 k2 n2 = xinside0 kn b1 k1 n1 b2 k2 n2.
Proof. intros. unfold xinside0F, xinside0. rewrite !lin_ge0F_eq. reflexivity. Qed.
Lemma xinside_numF_eq : forall kn b1 k1 n1 b2 k2 n2, xinside_numF (SFS kn) kn b1 k1 n1 b2 k2 n2 = xinside_num kn b1 k1 n1 b2 k2 n2.
Proof. intros. unfold xinside_numF, xinside_num. rewrite !xloF_eq, !xhiF_eq. reflexivity. Qed.
Lemma xinsideF_eq : forall kn b1 k1 n1 b2 k2 n2, xinsideF (SFS kn) kn b1 k1 n1 b2 k2 n2 = xinside kn b1 k1 n1 b2 k2 n2.
Proof. intros. unfold xinsideF, xinside. rewrite xinside0F_eq, xinside_numF_eq. reflexivity. Qed.
Lemma sub_itvF_eq : forall kn b k n c m, sub_itvF (SFS kn) kn b k n c m = sub_itv kn b k n c m.
Proof. intros. unfold sub_itvF, sub_itv. rewrite xloF_eq, xinsideF_eq. reflexivity. Qed.
Lemma kdisj_apartF_eq : forall allkn kn b1 k1 n1 b2 k2 n2,
  kdisj_apartF (SFS allkn) allkn kn b1 k1 n1 b2 k2 n2 = kdisj_apart allkn kn b1 k1 n1 b2 k2 n2.
Proof.
  intros allkn kn b1 k1 n1 b2 k2 n2. induction kn as [|K rest IH]; [reflexivity|].
  cbn [kdisj_apartF kdisj_apart]. rewrite IH. destruct K; try reflexivity. rewrite !sub_itvF_eq. reflexivity.
Qed.
Lemma ranges_apartF_eq : forall kn b1 k1 n1 b2 k2 n2, ranges_apartF (SFS kn) kn b1 k1 n1 b2 k2 n2 = ranges_apart kn b1 k1 n1 b2 k2 n2.
Proof. intros. unfold ranges_apartF, ranges_apart. rewrite kdisj_apartF_eq, lin_apartF_eq. reflexivity. Qed.
Lemma sub_itv_xF_eq : forall kn b k n c m, sub_itv_xF (SFS kn) kn b k n c m = sub_itv_x kn b k n c m.
Proof. intros. unfold sub_itv_xF, sub_itv_x. apply xinsideF_eq. Qed.
Lemma kdisj_apart_xF_eq : forall allkn kn b1 k1 n1 b2 k2 n2,
  kdisj_apart_xF (SFS allkn) allkn kn b1 k1 n1 b2 k2 n2 = kdisj_apart_x allkn kn b1 k1 n1 b2 k2 n2.
Proof.
  intros allkn kn b1 k1 n1 b2 k2 n2. induction kn as [|K rest IH]; [reflexivity|].
  cbn [kdisj_apart_xF kdisj_apart_x]. rewrite IH. destruct K; try reflexivity. rewrite !sub_itv_xF_eq. reflexivity.
Qed.
Lemma ranges_apart_xF_eq : forall kn b1 k1 n1 b2 k2 n2,
  ranges_apart_xF (SFS kn) kn b1 k1 n1 b2 k2 n2 = ranges_apart_x kn b1 k1 n1 b2 k2 n2.
Proof.
  intros. unfold ranges_apart_xF, ranges_apart_x.
  destruct n1, n2; rewrite ?ranges_apartF_eq, ?xhiF_eq, ?kdisj_apart_xF_eq, ?lin_ge0F_eq; reflexivity.
Qed.

(* [comment removed for export] *)
Record sprep := SPrep {
  sp_rng : option (Z * Z);          (* [comment removed for export] *)
  sp_h1 : option Z;                 (* [comment removed for export] *)
  sp_D : list (saddr * expr);       (* [comment removed for export] *)
  sp_Dx : list (saddr * expr) }.    (* [comment removed for export] *)

Fixpoint disj_sides (allkn kn : list kentry) (b1 : expr) (k1 n1 : Z) : list (saddr * expr) :=
  match kn with
  | [] => []
  | KDisj c1 m1 c2 m2 :: rest =>
      let r := disj_sides allkn rest b1 k1 n1 in
      let r1 := if sub_itv allkn b1 k1 n1 c2 m2 then (c1, m1) :: r else r in
      if sub_itv allkn b1 k1 n1 c1 m1 then (c2, m2) :: r1 else r1
  | _ :: rest => disj_sides allkn rest b1 k1 n1
  end.

Fixpoint disj_sides_x (allkn kn : list kentry) (b1 : expr) (k1 : Z) (n1 : expr) : list (saddr * expr) :=
  match kn with
  | [] => []
  | KDisj c1 m1 c2 m2 :: rest =>
      let r := disj_sides_x allkn rest b1 k1 n1 in
      let r1 := if sub_itv_x allkn b1 k1 n1 c2 m2 then (c1, m1) :: r else r in
      if sub_itv_x allkn b1 k1 n1 c1 m1 then (c2, m2) :: r1 else r1
  | _ :: rest => disj_sides_x allkn rest b1 k1 n1
  end.

Fixpoint in_sides (allkn : list kentry) (D : list (saddr * expr)) (b2 : expr) (k2 n2 : Z) : bool :=
  match D with
  | [] => false
  | (c, m) :: r => if sub_itv allkn b2 k2 n2 c m then true else in_sides allkn r b2 k2 n2
  end.

Fixpoint in_sides_x (allkn : list kentry) (D : list (saddr * expr)) (b2 : expr) (k2 : Z) (n2 : expr) : bool :=
  match D with
  | [] => false
  | (c, m) :: r => if sub_itv_x allkn b2 k2 n2 c m then true else in_sides_x allkn r b2 k2 n2
  end.

Definition mk_sprep (kn : list kentry) (b1 : expr) (k1 : Z) (n1 : expr) : sprep :=
  SPrep (base_range kn b1) (xhi kn n1)
        (match n1 with ELit z1 => disj_sides kn kn b1 k1 (zlit64 z1) | _ => [] end)
        (disj_sides_x kn kn b1 k1 n1).

(* [comment removed for export] *)
Definition ranges_apart_p (kn : list kentry) (sp : sprep) (b1 : expr) (k1 : Z) (n1 : expr)
           (b2 : expr) (k2 : Z) (n2 : expr) : bool :=
  match n1, n2 with
  | ELit z1, ELit z2 =>
      let m1 := zlit64 z1 in let m2 := zlit64 z2 in
      if (match sp_rng sp, base_range kn b2 with
          | Some (lo1, hi1), Some (lo2, hi2) =>
              (Z.leb (hi1 + k1 + m1) (lo2 + k2) || Z.leb (hi2 + k2 + m2) (lo1 + k1))%bool
          | _, _ => false
          end) then true
      else if in_sides kn (sp_D sp) b2 k2 m2 then true
      else lin_apart kn b1 k1 m1 b2 k2 m2
  | _, _ =>
    if (match sp_rng sp, base_range kn b2, sp_h1 sp, xhi kn n2 with
        | Some (lo1, hi1), Some (lo2, hi2), Some h1, Some h2 =>
            (Z.leb (hi1 + k1 + h1) (lo2 + k2) || Z.leb (hi2 + k2 + h2) (lo1 + k1))%bool
        | _, _, _, _ => false
        end) then true
    else if in_sides_x kn (sp_Dx sp) b2 k2 n2 then true
    else if negb (shares_var b1 b2) then false
    else if lin_ge0 kn [(b2, k2)] [(b1, k1); (n1, 0%Z)] then true
    else lin_ge0 kn [(b1, k1)] [(b2, k2); (n2, 0%Z)]
  end.

(* [comment removed for export] *)
Lemma filter_is_factb_idem : forall kn, List.filter is_factb (List.filter is_factb kn) = List.filter is_factb kn.
Proof.
  induction kn as [|K rest IH]; [reflexivity|]. cbn [List.filter].
  destruct (is_factb K) eqn:E; cbn [List.filter]; rewrite ?E, IH; reflexivity.
Qed.
Lemma facts_of_idem : forall kn, facts_of (facts_of kn) = facts_of kn.
Proof. intros kn. rewrite !facts_of_filter. apply filter_is_factb_idem. Qed.
Lemma erange_fk : forall kn e, erange (facts_of kn) e = erange kn e.
Proof. intros. unfold erange. rewrite facts_of_idem. reflexivity. Qed.
Lemma base_range_fk : forall kn e, base_range (facts_of kn) e = base_range kn e.
Proof. intros. unfold base_range. rewrite erange_fk. reflexivity. Qed.
Lemma ealign_fk : forall kn e, ealign (facts_of kn) e = ealign kn e.
Proof. intros. unfold ealign. rewrite facts_of_idem. reflexivity. Qed.
Lemma lin_range_ext : forall f g, (forall a, f a = g a) -> forall c ts, lin_range f c ts = lin_range g c ts.
Proof.
  intros f g H c ts. induction ts as [|[k a] rest IH]; [reflexivity|]. cbn [lin_range]. rewrite H, IH. reflexivity.
Qed.
Lemma lin_nowrap_fk : forall kn e, lin_nowrap (facts_of kn) e = lin_nowrap kn e.
Proof. intros. unfold lin_nowrap. rewrite (lin_range_ext _ _ (erange_fk kn)). reflexivity. Qed.
Lemma srl_expand_fk : forall kn ts, srl_expand (facts_of kn) ts = srl_expand kn ts.
Proof.
  intros kn ts. induction ts as [|[k a] rest IH]; [reflexivity|]. cbn [srl_expand]. rewrite IH.
  destruct (srl_expand kn rest) as [c ts']. destruct a; try reflexivity. destruct op; try reflexivity.
  destruct a2; try reflexivity. rewrite lin_nowrap_fk, ealign_fk. reflexivity.
Qed.
Lemma fact_nowrap_fk : forall kn e hi, fact_nowrap (facts_of kn) e hi = fact_nowrap kn e hi.
Proof. intros. unfold fact_nowrap. rewrite (lin_range_ext _ _ (erange_fk kn)). reflexivity. Qed.
Lemma sum_fact_x_fk : forall kn ts lo hi, sum_fact_x (facts_of kn) ts lo hi = sum_fact_x kn ts lo hi.
Proof. intros. unfold sum_fact_x. rewrite srl_expand_fk. reflexivity. Qed.
Lemma sum_facts_fk1 : forall allkn kn, sum_facts (facts_of allkn) kn = sum_facts allkn kn.
Proof.
  intros allkn kn. induction kn as [|K rest IH]; [reflexivity|]. cbn [sum_facts]. rewrite IH.
  destruct K; try reflexivity. rewrite fact_nowrap_fk.
  destruct e; try reflexivity; destruct (lin_of _) as [c [|t1 [|t2 ts]]]; rewrite ?sum_fact_x_fk; reflexivity.
Qed.
Lemma sum_facts_fk2 : forall allkn kn, sum_facts allkn (facts_of kn) = sum_facts allkn kn.
Proof.
  intros allkn kn. rewrite facts_of_filter. induction kn as [|K rest IH]; [reflexivity|].
  cbn [List.filter]. destruct (is_factb K) eqn:E.
  - cbn [sum_facts]. rewrite IH. destruct K; reflexivity.
  - rewrite IH. destruct K; try reflexivity; discriminate.
Qed.
Lemma SFS_fk : forall kn, SFS (facts_of kn) = SFS kn.
Proof. intros. unfold SFS. rewrite sum_facts_fk1, sum_facts_fk2. reflexivity. Qed.
Lemma lin_test_rel_fk : forall kn c ts test, lin_test_rel (facts_of kn) c ts test = lin_test_rel kn c ts test.
Proof.
  intros. unfold lin_test_rel. rewrite sum_facts_fk1, sum_facts_fk2.
  destruct (sum_facts kn kn) as [|f fs]; [reflexivity|].
  destruct (sum_subst (f :: fs) ts 0 0 false) as [[ts' [lo0 hi0]] [|]]; [|reflexivity].
  rewrite (lin_range_ext _ _ (erange_fk kn)). reflexivity.
Qed.
Lemma lin_test_fk : forall kn c ts test, lin_test (facts_of kn) c ts test = lin_test kn c ts test.
Proof. intros. unfold lin_test. rewrite (lin_range_ext _ _ (erange_fk kn)), !lin_test_rel_fk. reflexivity. Qed.
Lemma lin_nowrapR_fk : forall kn e, lin_nowrapR (facts_of kn) e = lin_nowrapR kn e.
Proof. intros. unfold lin_nowrapR. rewrite srl_expand_fk. destruct (srl_expand kn _). apply lin_test_fk. Qed.
Lemma xt_nowrap_fk : forall kn ts, xt_nowrap (facts_of kn) ts = xt_nowrap kn ts.
Proof. intros kn ts. induction ts as [|[e k] r IH]; [reflexivity|]. cbn [xt_nowrap]. rewrite lin_nowrapR_fk, IH. reflexivity. Qed.
Lemma lin_ge0_fk : forall kn pos neg, lin_ge0 (facts_of kn) pos neg = lin_ge0 kn pos neg.
Proof.
  intros. unfold lin_ge0. rewrite !xt_nowrap_fk, !lin_test_fk, srl_expand_fk.
  destruct (srl_expand kn _). rewrite lin_test_fk. reflexivity.
Qed.
Lemma lin_apart0_fk : forall kn b1 k1 n1 b2 k2 n2, lin_apart0 (facts_of kn) b1 k1 n1 b2 k2 n2 = lin_apart0 kn b1 k1 n1 b2 k2 n2.
Proof. intros. unfold lin_apart0. rewrite !lin_nowrapR_fk, lin_test_fk. reflexivity. Qed.
Lemma lin_apart_fk : forall kn b1 k1 n1 b2 k2 n2, lin_apart (facts_of kn) b1 k1 n1 b2 k2 n2 = lin_apart kn b1 k1 n1 b2 k2 n2.
Proof. intros. unfold lin_apart. rewrite lin_apart0_fk. reflexivity. Qed.
Lemma lin_brange_fk : forall kn e, lin_brange (facts_of kn) e = lin_brange kn e.
Proof.
  intros. unfold lin_brange. rewrite sum_facts_fk1, sum_facts_fk2.
  destruct (sum_facts kn kn) as [|f fs]; [reflexivity|].
  destruct (sum_subst (f :: fs) _ 0 0 false) as [[ts' [lo0 hi0]] [|]]; [|reflexivity].
  rewrite (lin_range_ext _ _ (erange_fk kn)). reflexivity.
Qed.
Lemma xlo_fk : forall kn e, xlo (facts_of kn) e = xlo kn e.
Proof. intros. unfold xlo. rewrite erange_fk, lin_brange_fk. reflexivity. Qed.
Lemma xhi_fk : forall kn e, xhi (facts_of kn) e = xhi kn e.
Proof. intros. unfold xhi. rewrite erange_fk, lin_brange_fk. reflexivity. Qed.
Lemma xinside0_fk : forall kn b1 k1 n1 b2 k2 n2, xinside0 (facts_of kn) b1 k1 n1 b2 k2 n2 = xinside0 kn b1 k1 n1 b2 k2 n2.
Proof. intros. unfold xinside0. rewrite !lin_ge0_fk. reflexivity. Qed.
Lemma xinside_num_fk : forall kn b1 k1 n1 b2 k2 n2, xinside_num (facts_of kn) b1 k1 n1 b2 k2 n2 = xinside_num kn b1 k1 n1 b2 k2 n2.
Proof. intros. unfold xinside_num. rewrite !xlo_fk, !xhi_fk, base_range_fk. reflexivity. Qed.
Lemma xinside_fk : forall kn b1 k1 n1 b2 k2 n2, xinside (facts_of kn) b1 k1 n1 b2 k2 n2 = xinside kn b1 k1 n1 b2 k2 n2.
Proof. intros. unfold xinside. rewrite xinside0_fk, xinside_num_fk. reflexivity. Qed.
Lemma sub_itv_fk : forall kn b k n c m, sub_itv (facts_of kn) b k n c m = sub_itv kn b k n c m.
Proof. intros. unfold sub_itv. rewrite xlo_fk, xinside_fk. reflexivity. Qed.
Lemma kdisj_apart_fk1 : forall allkn kn b1 k1 n1 b2 k2 n2,
  kdisj_apart (facts_of allkn) kn b1 k1 n1 b2 k2 n2 = kdisj_apart allkn kn b1 k1 n1 b2 k2 n2.
Proof.
  intros allkn kn b1 k1 n1 b2 k2 n2. induction kn as [|K rest IH]; [reflexivity|].
  cbn [kdisj_apart]. rewrite IH. destruct K; try reflexivity. rewrite !sub_itv_fk. reflexivity.
Qed.
Lemma kdisj_apart_fk2 : forall allkn kn b1 k1 n1 b2 k2 n2,
  kdisj_apart allkn (facts_of kn) b1 k1 n1 b2 k2 n2 = kdisj_apart allkn kn b1 k1 n1 b2 k2 n2.
Proof.
  intros allkn kn b1 k1 n1 b2 k2 n2. rewrite facts_of_filter. induction kn as [|K rest IH]; [reflexivity|].
  cbn [List.filter]. destruct (is_factb K) eqn:E.
  - cbn [kdisj_apart]. rewrite IH. reflexivity.
  - rewrite IH. destruct K; try reflexivity; discriminate.
Qed.
Lemma ranges_apart_fk : forall kn b1 k1 n1 b2 k2 n2, ranges_apart (facts_of kn) b1 k1 n1 b2 k2 n2 = ranges_apart kn b1 k1 n1 b2 k2 n2.
Proof. intros. unfold ranges_apart. rewrite !base_range_fk, kdisj_apart_fk1, kdisj_apart_fk2, lin_apart_fk. reflexivity. Qed.
Lemma sub_itv_x_fk : forall kn b k n c m, sub_itv_x (facts_of kn) b k n c m = sub_itv_x kn b k n c m.
Proof. intros. unfold sub_itv_x. apply xinside_fk. Qed.
Lemma kdisj_apart_x_fk1 : forall allkn kn b1 k1 n1 b2 k2 n2,
  kdisj_apart_x (facts_of allkn) kn b1 k1 n1 b2 k2 n2 = kdisj_apart_x allkn kn b1 k1 n1 b2 k2 n2.
Proof.
  intros allkn kn b1 k1 n1 b2 k2 n2. induction kn as [|K rest IH]; [reflexivity|].
  cbn [kdisj_apart_x]. rewrite IH. destruct K; try reflexivity. rewrite !sub_itv_x_fk. reflexivity.
Qed.
Lemma kdisj_apart_x_fk2 : forall allkn kn b1 k1 n1 b2 k2 n2,
  kdisj_apart_x allkn (facts_of kn) b1 k1 n1 b2 k2 n2 = kdisj_apart_x allkn kn b1 k1 n1 b2 k2 n2.
Proof.
  intros allkn kn b1 k1 n1 b2 k2 n2. rewrite facts_of_filter. induction kn as [|K rest IH]; [reflexivity|].
  cbn [List.filter]. destruct (is_factb K) eqn:E.
  - cbn [kdisj_apart_x]. rewrite IH. reflexivity.
  - rewrite IH. destruct K; try reflexivity; discriminate.
Qed.
Lemma ranges_apart_x_fk : forall kn b1 k1 n1 b2 k2 n2, ranges_apart_x (facts_of kn) b1 k1 n1 b2 k2 n2 = ranges_apart_x kn b1 k1 n1 b2 k2 n2.
Proof.
  intros. unfold ranges_apart_x.
  destruct n1, n2; rewrite ?ranges_apart_fk, ?base_range_fk, ?xhi_fk, ?kdisj_apart_x_fk1, ?kdisj_apart_x_fk2, ?lin_ge0_fk; reflexivity.
Qed.
Lemma disj_sides_fk1 : forall allkn kn b1 k1 n1, disj_sides (facts_of allkn) kn b1 k1 n1 = disj_sides allkn kn b1 k1 n1.
Proof.
  intros allkn kn b1 k1 n1. induction kn as [|K rest IH]; [reflexivity|].
  cbn [disj_sides]. rewrite IH. destruct K; try reflexivity. rewrite !sub_itv_fk. reflexivity.
Qed.
Lemma disj_sides_fk2 : forall allkn kn b1 k1 n1, disj_sides allkn (facts_of kn) b1 k1 n1 = disj_sides allkn kn b1 k1 n1.
Proof.
  intros allkn kn b1 k1 n1. rewrite facts_of_filter. induction kn as [|K rest IH]; [reflexivity|].
  cbn [List.filter]. destruct (is_factb K) eqn:E.
  - cbn [disj_sides]. rewrite IH. reflexivity.
  - rewrite IH. destruct K; try reflexivity; discriminate.
Qed.
Lemma disj_sides_x_fk1 : forall allkn kn b1 k1 n1, disj_sides_x (facts_of allkn) kn b1 k1 n1 = disj_sides_x allkn kn b1 k1 n1.
Proof.
  intros allkn kn b1 k1 n1. induction kn as [|K rest IH]; [reflexivity|].
  cbn [disj_sides_x]. rewrite IH. destruct K; try reflexivity. rewrite !sub_itv_x_fk. reflexivity.
Qed.
Lemma disj_sides_x_fk2 : forall allkn kn b1 k1 n1, disj_sides_x allkn (facts_of kn) b1 k1 n1 = disj_sides_x allkn kn b1 k1 n1.
Proof.
  intros allkn kn b1 k1 n1. rewrite facts_of_filter. induction kn as [|K rest IH]; [reflexivity|].
  cbn [List.filter]. destruct (is_factb K) eqn:E.
  - cbn [disj_sides_x]. rewrite IH. reflexivity.
  - rewrite IH. destruct K; try reflexivity; discriminate.
Qed.
Lemma in_sides_fk : forall kn D b2 k2 n2, in_sides (facts_of kn) D b2 k2 n2 = in_sides kn D b2 k2 n2.
Proof. intros kn D b2 k2 n2. induction D as [|[c m] r IH]; [reflexivity|]. cbn [in_sides]. rewrite sub_itv_fk, IH. reflexivity. Qed.
Lemma in_sides_x_fk : forall kn D b2 k2 n2, in_sides_x (facts_of kn) D b2 k2 n2 = in_sides_x kn D b2 k2 n2.
Proof. intros kn D b2 k2 n2. induction D as [|[c m] r IH]; [reflexivity|]. cbn [in_sides_x]. rewrite sub_itv_x_fk, IH. reflexivity. Qed.
Lemma mk_sprep_fk : forall kn b1 k1 n1, mk_sprep (facts_of kn) b1 k1 n1 = mk_sprep kn b1 k1 n1.
Proof.
  intros. unfold mk_sprep. rewrite base_range_fk, xhi_fk, disj_sides_x_fk1, disj_sides_x_fk2.
  destruct n1; rewrite ?disj_sides_fk1, ?disj_sides_fk2; reflexivity.
Qed.
Lemma ranges_apart_p_fk : forall kn sp b1 k1 n1 b2 k2 n2,
  ranges_apart_p (facts_of kn) sp b1 k1 n1 b2 k2 n2 = ranges_apart_p kn sp b1 k1 n1 b2 k2 n2.
Proof.
  intros. unfold ranges_apart_p.
  destruct n1, n2; rewrite ?base_range_fk, ?xhi_fk, ?in_sides_fk, ?in_sides_x_fk, ?lin_apart_fk, ?lin_ge0_fk; reflexivity.
Qed.

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
Fixpoint know_lookupA (allkn : list kentry) (segs : list Segment) (kn : list kentry) (rb : expr) (rk : Z)
         (n : nat) (sx : bool) (hints : list bool) (acc : list sidecond) : lres :=
  let know_lookup := know_lookupA allkn in
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
              match rel_lit rb rk (Z.of_nat n) kb kk (zmod64 l0) with
              | RInside _ => LHit (ELit 0) acc hints
              | RDisjoint | RPartial => know_lookup segs rest rb rk n sx hints acc
              | RUnknown =>
                  (* [comment removed for export] *)
                  if xinside allkn rb rk (elen n) kb kk len then LHit (ELit 0) acc hints else
                  match hints with
                  | true :: hs => LHit (ELit 0) (SCInside (SA rb rk) (elen n) (SA kb kk) len :: acc) hs
                  | false :: hs => know_lookup segs rest rb rk n sx hs acc
                  | [] => know_lookup segs rest rb rk n sx [] acc
                  end
              end
          | _ =>
              if xinside allkn rb rk (elen n) kb kk len then LHit (ELit 0) acc hints else
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
                  let l0' := zmod64 l0 in
                  if Z.leb (rk + Z.of_nat n) (kk + l0')
                  then LHit (EBlob sx k (rk - kk) n) acc hints
                  else if Z.leb (kk + l0') rk then know_lookup segs rest rb rk n sx hints acc
                  else LStuck
              | _ =>
                  (* [comment removed for export] *)
                  if match erange rest len with
                     | Some (lo, _) => Z.leb (rk + Z.of_nat n) (kk + lo)
                     | None => false
                     end
                  then LHit (EBlob sx k (rk - kk) n) acc hints
                  else
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

Definition know_lookup (segs : list Segment) (kn : list kentry) (rb : expr) (rk : Z)
         (n : nat) (sx : bool) (hints : list bool) (acc : list sidecond) : lres :=
  know_lookupA kn segs kn rb rk n sx hints acc.

(* [comment removed for export] *)
Fixpoint coeffs_divk (kn : list kentry) (m : Z) (ts : list (Z * expr)) : bool :=
  match ts with
  | [] => true
  | (k, a) :: rest => ((Z.eqb (k mod m) 0 || Z.eqb ((zmulp k (ealign kn a)) mod m) 0) && coeffs_divk kn m rest)%bool
  end.

Definition lin_lowbits_kn (kn : list kentry) (e : expr) (k : Z) : option Z :=
  let l := lin_of e in
  let m := zpow2 k in
  if coeffs_divk kn m (snd l) then Some (zmodp (fst l) k)
  else pageup_low e m.   (* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint ldiv_terms (m : Z) (ts : list (Z * expr)) : list (Z * expr) :=
  match ts with
  | [] => []
  | (k, a) :: rest => ((k / m)%Z, a) :: ldiv_terms m rest
  end.

Definition mkSrl (kn : list kentry) (a : expr) (s : Z) : expr :=
  let l := lin_of a in
  let m := (2 ^ s)%Z in
  if (negb (lin_trivial l) && coeffs_div m (snd l) && lin_nowrap kn a)%bool
  then unlin ((fst l / m)%Z, ldiv_terms m (snd l))     (* [comment removed for export] *)
  else mkAlu ALU_SRL a (ELit s).

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
              if (negb (lin_trivial l) && coeffs_divk kn (2 ^ j) (snd l))%bool
              then unlin ((fst l - (fst l) mod 2 ^ j)%Z, snd l)
              else (* [comment removed for export] *)
                   mkMd M_MUL (ELit (2 ^ j)%Z) (mkSrl kn a j))
      else
        let j2 := Z.log2 (k' + 1) in
        if (Z.eqb (k' + 1) (2 ^ j2) && Z.ltb j2 64)%bool then
          (* [comment removed for export] *)
          (if Z.leb j2 (ealign kn a) then ELit 0
           else if lin_trivial (lin_of a) then mkAlu ALU_AND a b
           else match lin_lowbits_kn kn a j2 with
                | Some v => ELit v
                | None => mkAlu ALU_AND a b
                end)
        else (* [comment removed for export] *)
          let j3 := (Z.log2 k' + 1)%Z in
          if (Z.ltb 0 k' && Z.leb j3 64 && negb (lin_trivial (lin_of a)))%bool then
            match lin_lowbits_kn kn a j3 with
            | Some v => ELit (Z.land v k')
            | None => mkAlu ALU_AND a b
            end
          else mkAlu ALU_AND a b
  | _ => mkAlu ALU_AND a b
  end.

(* [comment removed for export] *)
Definition mkAndK (kn : list kentry) (a b : expr) : expr :=
  match a, b with
  | EAlu ALU_AND x (ELit m1), ELit k => mkAnd kn x (ELit (Z.land (m1 mod two64) (k mod two64))%Z)
  | EMd M_MUL (ELit m) (EAlu ALU_SRL x (ELit i)), ELit k =>
      (* [comment removed for export] *)
      let i' := ((i mod two64) mod 64)%Z in
      if Z.eqb (m mod two64) (2 ^ i') then mkAnd kn x (ELit (Z.land (two64 - 2 ^ i') (k mod two64))%Z)
      else mkAnd kn a b
  | _, _ => mkAnd kn a b
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
      else (* [comment removed for export] *)
           match b with
           | ELit c => mkAlu ALU_ADD (mkAndK kn a (ELit (Z.lnot (c mod two64)))) (ELit c)
           | _ => match a with
                  | ELit c => mkAlu ALU_ADD (mkAndK kn b (ELit (Z.lnot (c mod two64)))) (ELit c)
                  | _ => EAlu ALU_OR a b
                  end
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
           | Some w => if Z.eqb w v then all_eval_to s e v (lo + 1) c else false   (* [comment removed for export] *)
           | None => false
           end
  end.

(* [comment removed for export] *)

Fixpoint evalS (s : expr) (z : Z) (e : expr) : option Z :=
  if expr_eqb e s then Some z else
  match e with
  | ELit w => Some (wrap64 w)
  | EVar _ => None
  | EAlu op a b => match evalS s z a with
                   | Some x => match evalS s z b with Some y => Some (zfast op x y) | None => None end
                   | None => None
                   end
  | EAluw op a b => match evalS s z a with
                    | Some x => match evalS s z b with Some y => Some (zfastw op x y) | None => None end
                    | None => None
                    end
  | EMd op a b => match evalS s z a with
                  | Some x => match evalS s z b with Some y => Some (zfastm op x y) | None => None end
                  | None => None
                  end
  | EMdw op a b => match evalS s z a with
                   | Some x => match evalS s z b with Some y => Some (zmdw op x y) | None => None end
                   | None => None
                   end
  | EExt sx lo n a => match evalS s z a with
                      | Some x => Some (zext_lit sx lo n x) | None => None end
  | EBlob _ _ _ _ => None
  end.

(* [comment removed for export] *)
Fixpoint all_eval_toS (s e : expr) (v lo : Z) (cnt : nat) : bool :=
  match cnt with
  | O => true
  | S c => match evalS s (wrap64 lo) e with
           | Some w => if Z.eqb w v then all_eval_toS s e v (lo + 1) c else false
           | None => false
           end
  end.

(* [comment removed for export] *)
Inductive pnode : Type :=
| PIn                                   (* [comment removed for export] *)
| PLit (v : Z)                          (* [comment removed for export] *)
| PAlu (op : aluop) (i j : nat)         (* [comment removed for export] *)
| PAluw (op : aluop) (i j : nat)
| PMd (op : mulop) (i j : nat)
| PMdw (op : mulop) (i j : nat)
| PExt (sx : bool) (lo n : nat) (i : nat).

Definition pnode_eval (z : Z) (vs : list Z) (p : pnode) : Z :=
  match p with
  | PIn => z
  | PLit v => v
  | PAlu op i j => zfast op (nth i vs 0%Z) (nth j vs 0%Z)
  | PAluw op i j => zfastw op (nth i vs 0%Z) (nth j vs 0%Z)
  | PMd op i j => zfastm op (nth i vs 0%Z) (nth j vs 0%Z)
  | PMdw op i j => zmdw op (nth i vs 0%Z) (nth j vs 0%Z)
  | PExt sx lo n i => zext_lit sx lo n (nth i vs 0%Z)
  end.

(* [comment removed for export] *)
Fixpoint prun (z : Z) (prog : list pnode) (vs : list Z) : list Z :=
  match prog with
  | [] => vs
  | p :: rest => prun z rest (pnode_eval z vs p :: vs)
  end.

(* [comment removed for export] *)
Record pstate : Type := PS { ps_prog : list pnode; ps_n : nat; ps_memo : list (expr * nat) }.

Fixpoint pmemo_get (m : list (expr * nat)) (e : expr) : option nat :=
  match m with
  | [] => None
  | (e', i) :: r => if expr_eqb e e' then Some i else pmemo_get r e
  end.

Definition pemit (st : pstate) (e : expr) (p : pnode) : pstate * nat :=
  (PS (p :: ps_prog st) (S (ps_n st)) ((e, ps_n st) :: ps_memo st), ps_n st).

(* [comment removed for export] *)
Definition pref (n i : nat) : nat := n - S i.

Fixpoint pcomp (s : expr) (e : expr) (st : pstate) {struct e} : option (pstate * nat) :=
  if expr_eqb e s then
    match pmemo_get (ps_memo st) e with Some i => Some (st, i) | None => Some (pemit st e PIn) end
  else
  match pmemo_get (ps_memo st) e with
  | Some i => Some (st, i)
  | None =>
    match e with
    | ELit w => Some (pemit st e (PLit (wrap64 w)))
    | EVar _ => None
    | EBlob _ _ _ _ => None
    | EAlu op a b =>
        match pcomp s a st with
        | Some (st1, i) =>
            match pcomp s b st1 with
            | Some (st2, j) => Some (pemit st2 e (PAlu op (pref (ps_n st2) i) (pref (ps_n st2) j)))
            | None => None
            end
        | None => None
        end
    | EAluw op a b =>
        match pcomp s a st with
        | Some (st1, i) =>
            match pcomp s b st1 with
            | Some (st2, j) => Some (pemit st2 e (PAluw op (pref (ps_n st2) i) (pref (ps_n st2) j)))
            | None => None
            end
        | None => None
        end
    | EMd op a b =>
        match pcomp s a st with
        | Some (st1, i) =>
            match pcomp s b st1 with
            | Some (st2, j) => Some (pemit st2 e (PMd op (pref (ps_n st2) i) (pref (ps_n st2) j)))
            | None => None
            end
        | None => None
        end
    | EMdw op a b =>
        match pcomp s a st with
        | Some (st1, i) =>
            match pcomp s b st1 with
            | Some (st2, j) => Some (pemit st2 e (PMdw op (pref (ps_n st2) i) (pref (ps_n st2) j)))
            | None => None
            end
        | None => None
        end
    | EExt sx lo n a =>
        match pcomp s a st with
        | Some (st1, i) => Some (pemit st1 e (PExt sx lo n (pref (ps_n st1) i)))
        | None => None
        end
    end
  end.

Fixpoint sweepP (prog : list pnode) (d : nat) (v lo : Z) (cnt : nat) : bool :=
  match cnt with
  | O => true
  | S c => if Z.eqb (nth d (prun (wrap64 lo) prog []) 0%Z) v then sweepP prog d v (lo + 1) c else false
  end.

Definition all_eval_toP (s e : expr) (v lo : Z) (cnt : nat) : bool :=
  match pcomp s e (PS [] 0 []) with
  | Some (st, i) => sweepP (List.rev_append (ps_prog st) []) (pref (ps_n st) i) v lo cnt
  | None => all_eval_toS s e v lo cnt
  end.

(* [comment removed for export] *)
Definition probeS (s e : expr) (v z : Z) : bool :=
  match evalS s (wrap64 z) e with Some w => Z.eqb w v | None => false end.

Fixpoint memE (e : expr) (l : list expr) : bool :=
  match l with [] => false | x :: r => if expr_eqb e x then true else memE e r end.

Fixpoint nubE_acc (l acc : list expr) : list expr :=
  match l with
  | [] => []
  | x :: r => if memE x acc then nubE_acc r acc else x :: nubE_acc r (x :: acc)
  end.
Definition nubE (l : list expr) : list expr := nubE_acc l [].

Definition conc_limit : Z := 4096.

Fixpoint conc_try (kn : list kentry) (e : expr) (cands : list expr) : option Z :=
  match cands with
  | [] => None
  | s :: rest =>
      if closedb s then conc_try kn e rest else
      match erange kn s with
      | Some (lo, hi) =>
          if Z.leb (hi - lo) conc_limit then
            match evalS s (wrap64 lo) e with
            | Some v =>
                if (if Z.ltb hi lo then true
                     else if probeS s e v hi then probeS s e v (lo + (hi - lo) / 2)%Z else false) then
                  if all_eval_toP s e v lo (Z.to_nat (hi - lo + 1)) then Some v   (* [comment removed for export] *)
                  else conc_try kn e rest
                else conc_try kn e rest
            | None => conc_try kn e rest
            end
          else conc_try kn e rest
      | None => conc_try kn e rest
      end
  end.

Definition concretize (kn : list kentry) (e : expr) : option Z :=
  if closedb e then eval_closed e else conc_try kn e (nubE (subexprs e)).

(* [comment removed for export] *)
Definition foldK (kn : list kentry) (e : expr) : expr :=
  match e with
  | ELit _ => e
  | _ => match erange kn e with
         | Some (lo, hi) => if Z.eqb lo hi then ELit lo
                            else match concretize kn e with Some v => ELit v | None => e end
         | None => match concretize kn e with Some v => ELit v | None => e end   (* [comment removed for export] *)
         end
  end.

Definition mkAluK0 (kn : list kentry) (op : aluop) (a b : expr) : expr :=
  match op with
  | ALU_AND => match a, b with
               | ELit _, ELit _ => mkAnd kn a b
               | ELit _, _ => mkAndK kn b a      (* [comment removed for export] *)
               | _, _ => mkAndK kn a b
               end
  | ALU_OR => if expr_eqb a b then a else mkOr kn a b
  | ALU_XOR => if expr_eqb a b then ELit 0 else match is_lit a, b with
               | None, ELit k => if Z.eqb (k mod two64) (two64 - 1) then mkAlu ALU_SUB (ELit (two64 - 1)) a
                                else mkAlu op a b
               | _, _ => mkAlu op a b
               end
  | ALU_SRL => match is_lit a, shamt_of b 6 with
               | None, Some s => mkSrl kn a s
               | _, _ => mkAlu op a b
               end
  | _ => mkAlu op a b
  end.

(* [comment removed for export] *)
Definition zsx32 (v : Z) : Z := ((bv_swrap 32 v) mod two64)%Z.

Definition mkAluK (kn : list kentry) (op : aluop) (a b : expr) : expr :=
  foldK kn (mkAluK0 kn op a b).

(* [comment removed for export] *)
Definition two64m31 : Z := two64 - 2 ^ 31.
Definition mtwo31z : Z := - 2 ^ 31.
Definition sx32_stable (lo hi : Z) : bool :=
  (Z.ltb hi two31z || Z.leb two64m31 lo)%bool.

(* [comment removed for export] *)
Definition zband32 (kn : list kentry) (d : expr) : bool :=
  let l := lin_of d in
  match lin_range (erange kn) (fst l) (snd l) with
  | Some (lo, hi) => (Z.ltb mtwo31z lo && Z.ltb hi two31z)%bool
  | None => false
  end.

Definition mkAluwK0 (kn : list kentry) (op : aluop) (a b : expr) : expr :=
  match op with
  | ALU_ADD | ALU_SUB =>
      let d := mkAlu op a b in
      match is_lit d with
      | Some v => ELit (zsx32 v)
      | None => match erange kn d with
                | Some (lo, hi) => if sx32_stable lo hi then d else if zband32 kn d then d else mkAluw op a b
                | None => if zband32 kn d then d else mkAluw op a b
                end
      end
  | _ => mkAluw op a b
  end.

Definition mkAluwK (kn : list kentry) (op : aluop) (a b : expr) : expr :=
  foldK kn (mkAluwK0 kn op a b).

(* [comment removed for export] *)
Definition extK0 (kn : list kentry) (v : expr) : expr :=
  match v with
  | EExt sx O n e =>
      if Nat.leb n 7 then
        match erange kn e with
        | Some (lo, hi) => if Z.ltb hi (if sx then 2 ^ (8 * Z.of_nat n) / 2 else 2 ^ (8 * Z.of_nat n)) then e else v
        | None => v
        end
      else v
  | _ => v
  end.

Definition extK (kn : list kentry) (v : expr) : expr := foldK kn (extK0 kn v).

Definition msize_bytes (sz : msize) : nat :=
  match sz with SZ1 => 1 | SZ2 => 2 | SZ4 => 4 | SZ8 => 8 end.

(* [comment removed for export] *)
Definition flat_sc (kn : list kentry) (a : saddr) (n : nat) : list sidecond :=
  match base_range kn (a_base a) with
  | Some (lo, hi) =>
      if (Z.leb 0 (lo + a_off a) && Z.leb (hi + a_off a + Z.of_nat n) two64)%bool
      then [] else [SCFlat a (elen n)]
  | None => [SCFlat a (elen n)]
  end.

(* [comment removed for export] *)
Fixpoint wr_covered (allkn kn : list kentry) (a : saddr) (n : nat) : bool :=
  match kn with
  | [] => false
  | KWr (SA kb kk) len :: rest =>
      if (if (expr_eqb (a_base a) kb && Z.leb kk (a_off a))%bool
          then match xlo allkn len with Some l => Z.leb (a_off a + Z.of_nat n) (kk + l) | None => false end
          else false)
      then true
      else if xinside allkn (a_base a) (a_off a) (ELit (Z.of_nat n)) kb kk len then true
      else wr_covered allkn rest a n
  | _ :: rest => wr_covered allkn rest a n
  end.

Definition storeok_sc (kn : list kentry) (a : saddr) (n : nat) : list sidecond :=
  if wr_covered kn kn a n then [] else [SCStoreOk a n].

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
  let h := two63z in
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
(* [comment removed for export] *)
Definition diff_branch (c : branch_cond) (a b : expr) : option bool :=
  match c with
  | BC_EQ | BC_NE =>
      match is_lit (mkAlu ALU_SUB a b) with
      | Some z => let e := Z.eqb (z mod two64) 0 in Some (match c with BC_EQ => e | _ => negb e end)
      | None => None
      end
  | _ => None
  end.

Definition decide_branch (kn : list kentry) (c : branch_cond) (a b : expr) : option bool :=
  match a, b with
  | ELit x, ELit y => Some (lit_branch c x y)
  | _, _ =>
      if expr_eqb a b then Some (cond_on_eq c)
      else match diff_branch c a b with
           | Some t => Some t
           | None =>
             match erange kn a, erange kn b with
             | Some (al, ah), Some (bl, bh) => range_branch c al ah bl bh
             | _, _ => None
             end
           end
  end.

(* [comment removed for export] *)
Definition conc_expr (kn : list kentry) (e : expr) : expr :=
  match e with
  | ELit _ => e
  | _ => match concretize kn e with Some v => ELit v | None => e end
  end.

(* [comment removed for export] *)
Definition cond_probe (c : branch_cond) (a b : expr) : expr * bool :=
  match c with
  | BC_EQ => (EAlu ALU_SLTU (EAlu ALU_SUB a b) (ELit 1%Z), true)    (* [comment removed for export] *)
  | BC_NE => (EAlu ALU_SLTU (EAlu ALU_SUB a b) (ELit 1%Z), false)
  | BC_LT => (EAlu ALU_SLT a b, true)
  | BC_GE => (EAlu ALU_SLT a b, false)
  | BC_LTU => (EAlu ALU_SLTU a b, true)
  | BC_GEU => (EAlu ALU_SLTU a b, false)
  end.

Definition enum_branch (kn : list kentry) (c : branch_cond) (a b : expr) : option bool :=
  let '(e, pos) := cond_probe c a b in
  match concretize kn e with
  | Some v => let z := Z.eqb (v mod two64) 0 in Some (if pos then negb z else z)
  | None => None
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

Definition sym_step (segs : list Segment) (i : instr) (ss : sym_state) (scr : scripts) : stepres :=
  let g r := sr_get (s_regs ss) r in
  let p := s_pc ss in
  let fk := facts_of (s_know ss) in   (* [comment removed for export] *)
  match i with
  | OpImm op rd rs imm => SOk (sset ss rd (mkAluK fk op (g rs) (ELit (bv_signed imm))) (p + 4)) [] scr
  | ShiftImm op rd rs sh => SOk (sset ss rd (mkAluK fk op (g rs) (ELit (bv_unsigned sh))) (p + 4)) [] scr
  | Op op rd rs1 rs2 => SOk (sset ss rd (mkAluK fk op (g rs1) (g rs2)) (p + 4)) [] scr
  | OpImm32 rd rs imm => SOk (sset ss rd (mkAluwK fk ALU_ADD (g rs) (ELit (bv_signed imm))) (p + 4)) [] scr
  | ShiftImm32 op rd rs sh => SOk (sset ss rd (mkAluw op (g rs) (ELit (bv_unsigned sh))) (p + 4)) [] scr
  | Op32 op rd rs1 rs2 => SOk (sset ss rd (mkAluwK fk op (g rs1) (g rs2)) (p + 4)) [] scr
  | Mul op rd rs1 rs2 => SOk (sset ss rd (mkMd op (g rs1) (g rs2)) (p + 4)) [] scr
  | Mul32 op rd rs1 rs2 => SOk (sset ss rd (mkMdw op (g rs1) (g rs2)) (p + 4)) [] scr
  | Lui rd imm => SOk (sset ss rd (ELit (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_signed imm) 12)))) (p + 4)) [] scr
  | Auipc rd imm => SOk (sset ss rd (ELit (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_signed imm) 12 + p)))) (p + 4)) [] scr
  | Jal rd imm => SOk (sset ss rd (ELit (p + 4)) (bv_unsigned (Z_to_bv 64 (p + bv_signed imm)))) [] scr
  | Jalr rd rs1 imm =>
      match conc_expr fk (g rs1) with
      | ELit z => SOk (sset ss rd (ELit (p + 4)) (Z.land (bv_wrap 64 z + bv_signed imm) (-2) mod 2^64)) [] scr
      | _ => SStop
      end
  | Branch c rs1 rs2 imm =>
      let tk := bv_unsigned (Z_to_bv 64 (p + bv_signed imm)) in
      let a := g rs1 in let b := g rs2 in
      match match decide_branch fk c a b with
            | Some t => Some t
            | None => match decide_branch fk c (conc_expr fk a) (conc_expr fk b) with
                      | Some t => Some t
                      | None => enum_branch fk c a b
                      end
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
      let a := to_saddrK fk (g rs) (bv_signed imm) in
      let fin v scs hints :=
        SOk (sset ss rd (extK fk v) (p + 4)) (flat_sc fk a n ++ scs)
            (SCR (sc_dirs scr) (sc_reads scr) hints) in
      match log_lookup fk (s_log ss) (a_base a) (a_off a) n sx' (sc_hints scr) [] with
      | LStuck => SStop
      | LHit v scs hints => fin v scs hints
      | LMiss scs hints =>
          match know_lookupA fk segs (s_know ss) (a_base a) (a_off a) n sx' hints scs with
          | LStuck => SStop
          | LHit v scs' hints' => fin v scs' hints'
          | LMiss scs' hints' =>
              (* [comment removed for export] *)
              let i := s_next ss in
              let rv := match sc_reads scr with [] => EVar i | e :: _ => e end in
              let reads' := match sc_reads scr with [] => [] | _ :: t => t end in
              SOk (SS (p + 4)
                      (if bv_eqb rd 0 then s_regs ss else sr_upd (s_regs ss) (ridx rd) rv)
                      (s_log ss) (s_know ss) (S i))
                  (flat_sc fk a n ++ SCReadBase a n sx' rv :: scs')
                  (SCR (sc_dirs scr) reads' hints')
          end
      end
  | Store sz rs1 rs2 imm =>
      let n := msize_bytes sz in
      let a := to_saddrK fk (g rs1) (bv_signed imm) in
      SOk (SS (p + 4) (s_regs ss) (SE a n (g rs2) :: s_log ss) (s_know ss) (s_next ss))
          (flat_sc fk a n ++ storeok_sc fk a n) scr
  | _ => SStop
  end.

(* [comment removed for export] *)
Fixpoint log_lookupF (fs : list sfact) (kn : list kentry) (log : list sentry) (rb : expr) (rk : Z) (n : nat) (sx : bool)
         (hints : list bool) (acc : list sidecond) : lres :=
  match log with
  | [] => LMiss acc hints
  | SE (SA kb kk) w v :: rest =>
      match rel_lit rb rk (Z.of_nat n) kb kk (Z.of_nat w) with
      | RInside d => LHit (mkExt sx (Z.to_nat d) n v) acc hints
      | RDisjoint => log_lookupF fs kn rest rb rk n sx hints acc
      | RPartial => LStuck
      | RUnknown =>
          if ranges_apartF fs kn rb rk (Z.of_nat n) kb kk (Z.of_nat w)
          then log_lookupF fs kn rest rb rk n sx hints acc
          else
          match hints with
          | false :: _ => LStuck
          | _ => log_lookupF fs kn rest rb rk n sx (tl hints)
                   (SCDisj (SA rb rk) (elen n) (SA kb kk) (elen w) :: acc)
          end
      end
  end.
Fixpoint know_lookupAF (fs : list sfact) (allkn : list kentry) (segs : list Segment) (kn : list kentry) (rb : expr) (rk : Z)
         (n : nat) (sx : bool) (hints : list bool) (acc : list sidecond) : lres :=
  let know_lookup := know_lookupAF fs allkn in
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
              match rel_lit rb rk (Z.of_nat n) kb kk (zmod64 l0) with
              | RInside _ => LHit (ELit 0) acc hints
              | RDisjoint | RPartial => know_lookup segs rest rb rk n sx hints acc
              | RUnknown =>
                  (* [comment removed for export] *)
                  if xinsideF fs allkn rb rk (elen n) kb kk len then LHit (ELit 0) acc hints else
                  match hints with
                  | true :: hs => LHit (ELit 0) (SCInside (SA rb rk) (elen n) (SA kb kk) len :: acc) hs
                  | false :: hs => know_lookup segs rest rb rk n sx hs acc
                  | [] => know_lookup segs rest rb rk n sx [] acc
                  end
              end
          | _ =>
              if xinsideF fs allkn rb rk (elen n) kb kk len then LHit (ELit 0) acc hints else
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
                  let l0' := zmod64 l0 in
                  if Z.leb (rk + Z.of_nat n) (kk + l0')
                  then LHit (EBlob sx k (rk - kk) n) acc hints
                  else if Z.leb (kk + l0') rk then know_lookup segs rest rb rk n sx hints acc
                  else LStuck
              | _ =>
                  (* [comment removed for export] *)
                  if match erange rest len with
                     | Some (lo, _) => Z.leb (rk + Z.of_nat n) (kk + lo)
                     | None => false
                     end
                  then LHit (EBlob sx k (rk - kk) n) acc hints
                  else
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
Fixpoint wr_coveredF (fs : list sfact) (allkn kn : list kentry) (a : saddr) (n : nat) : bool :=
  match kn with
  | [] => false
  | KWr (SA kb kk) len :: rest =>
      if (if (expr_eqb (a_base a) kb && Z.leb kk (a_off a))%bool
          then match xloF fs allkn len with Some l => Z.leb (a_off a + Z.of_nat n) (kk + l) | None => false end
          else false)
      then true
      else if xinsideF fs allkn (a_base a) (a_off a) (ELit (Z.of_nat n)) kb kk len then true
      else wr_coveredF fs allkn rest a n
  | _ :: rest => wr_coveredF fs allkn rest a n
  end.
Definition storeok_scF (fs : list sfact) (kn : list kentry) (a : saddr) (n : nat) : list sidecond :=
  if wr_coveredF fs kn kn a n then [] else [SCStoreOk a n].

(* [comment removed for export] *)
Fixpoint log_lookupL (fs : list sfact) (kn : list kentry) (log : list sentry) (rb : expr) (rk : Z) (n : nat) (sx : bool)
         (hints : list bool) (acc : list sidecond)
         (othr : option lthr) (oD : option (list (saddr * expr))) (cache : list (expr * option (Z * Z))) : lres :=
  match log with
  | [] => LMiss acc hints
  | SE (SA kb kk) w v :: rest =>
      match rel_lit rb rk (Z.of_nat n) kb kk (Z.of_nat w) with
      | RInside d => LHit (mkExt sx (Z.to_nat d) n v) acc hints
      | RDisjoint => log_lookupL fs kn rest rb rk n sx hints acc othr oD cache
      | RPartial => LStuck
      | RUnknown =>
          let thr := match othr with Some t => t | None => mk_lthr kn rb rk (Z.of_nat n) end in
          let brc := match lbr_lookup cache kb with
                     | Some et => (et, cache)
                     | None => let et := mk_ethr thr (base_range kn kb) in (et, (kb, et) :: cache)
                     end in
          if ethr_test (fst brc) kk (Z.of_nat w)
          then log_lookupL fs kn rest rb rk n sx hints acc (Some thr) oD (snd brc)
          else
          let D := match oD with Some D => D | None => disj_sidesF fs kn kn rb rk (Z.of_nat n) end in
          if ranges_apart_restF fs kn D rb rk (Z.of_nat n) kb kk (Z.of_nat w)
          then log_lookupL fs kn rest rb rk n sx hints acc (Some thr) (Some D) (snd brc)
          else
          match hints with
          | false :: _ => LStuck
          | _ => log_lookupL fs kn rest rb rk n sx (tl hints)
                   (SCDisj (SA rb rk) (elen n) (SA kb kk) (elen w) :: acc) (Some thr) (Some D) (snd brc)
          end
      end
  end.

Definition sym_stepF (fk : list kentry) (fs : list sfact) (segs : list Segment) (i : instr) (ss : sym_state) (scr : scripts) : stepres :=
  let g r := sr_get (s_regs ss) r in
  let p := s_pc ss in
  match i with
  | OpImm op rd rs imm => SOk (sset ss rd (mkAluK fk op (g rs) (ELit (bv_signed imm))) (p + 4)) [] scr
  | ShiftImm op rd rs sh => SOk (sset ss rd (mkAluK fk op (g rs) (ELit (bv_unsigned sh))) (p + 4)) [] scr
  | Op op rd rs1 rs2 => SOk (sset ss rd (mkAluK fk op (g rs1) (g rs2)) (p + 4)) [] scr
  | OpImm32 rd rs imm => SOk (sset ss rd (mkAluwK fk ALU_ADD (g rs) (ELit (bv_signed imm))) (p + 4)) [] scr
  | ShiftImm32 op rd rs sh => SOk (sset ss rd (mkAluw op (g rs) (ELit (bv_unsigned sh))) (p + 4)) [] scr
  | Op32 op rd rs1 rs2 => SOk (sset ss rd (mkAluwK fk op (g rs1) (g rs2)) (p + 4)) [] scr
  | Mul op rd rs1 rs2 => SOk (sset ss rd (mkMd op (g rs1) (g rs2)) (p + 4)) [] scr
  | Mul32 op rd rs1 rs2 => SOk (sset ss rd (mkMdw op (g rs1) (g rs2)) (p + 4)) [] scr
  | Lui rd imm => SOk (sset ss rd (ELit (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_signed imm) 12)))) (p + 4)) [] scr
  | Auipc rd imm => SOk (sset ss rd (ELit (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_signed imm) 12 + p)))) (p + 4)) [] scr
  | Jal rd imm => SOk (sset ss rd (ELit (p + 4)) (bv_unsigned (Z_to_bv 64 (p + bv_signed imm)))) [] scr
  | Jalr rd rs1 imm =>
      match conc_expr fk (g rs1) with
      | ELit z => SOk (sset ss rd (ELit (p + 4)) (Z.land (bv_wrap 64 z + bv_signed imm) (-2) mod 2^64)) [] scr
      | _ => SStop
      end
  | Branch c rs1 rs2 imm =>
      let tk := bv_unsigned (Z_to_bv 64 (p + bv_signed imm)) in
      let a := g rs1 in let b := g rs2 in
      match match decide_branch fk c a b with
            | Some t => Some t
            | None => match decide_branch fk c (conc_expr fk a) (conc_expr fk b) with
                      | Some t => Some t
                      | None => enum_branch fk c a b
                      end
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
      let a := to_saddrK fk (g rs) (bv_signed imm) in
      let fin v scs hints :=
        SOk (sset ss rd (extK fk v) (p + 4)) (flat_sc fk a n ++ scs)
            (SCR (sc_dirs scr) (sc_reads scr) hints) in
      match log_lookupL fs fk (s_log ss) (a_base a) (a_off a) n sx' (sc_hints scr) [] None None [] with
      | LStuck => SStop
      | LHit v scs hints => fin v scs hints
      | LMiss scs hints =>
          match know_lookupAF fs fk segs (s_know ss) (a_base a) (a_off a) n sx' hints scs with
          | LStuck => SStop
          | LHit v scs' hints' => fin v scs' hints'
          | LMiss scs' hints' =>
              (* [comment removed for export] *)
              let i := s_next ss in
              let rv := match sc_reads scr with [] => EVar i | e :: _ => e end in
              let reads' := match sc_reads scr with [] => [] | _ :: t => t end in
              SOk (SS (p + 4)
                      (if bv_eqb rd 0 then s_regs ss else sr_upd (s_regs ss) (ridx rd) rv)
                      (s_log ss) (s_know ss) (S i))
                  (flat_sc fk a n ++ SCReadBase a n sx' rv :: scs')
                  (SCR (sc_dirs scr) reads' hints')
          end
      end
  | Store sz rs1 rs2 imm =>
      let n := msize_bytes sz in
      let a := to_saddrK fk (g rs1) (bv_signed imm) in
      SOk (SS (p + 4) (s_regs ss) (SE a n (g rs2) :: s_log ss) (s_know ss) (s_next ss))
          (flat_sc fk a n ++ storeok_scF fs fk a n) scr
  | _ => SStop
  end.

Lemma log_lookupF_eq : forall kn log rb rk n sx hints acc,
  log_lookupF (SFS kn) kn log rb rk n sx hints acc = log_lookup kn log rb rk n sx hints acc.
Proof.
  intros kn log. induction log as [|[[kb kk] w v] rest IH]; intros; [reflexivity|].
  cbn [log_lookupF log_lookup]. rewrite ranges_apartF_eq.
  destruct (rel_lit rb rk (Z.of_nat n) kb kk (Z.of_nat w)); rewrite ?IH; try reflexivity;
  destruct (ranges_apart kn rb rk (Z.of_nat n) kb kk (Z.of_nat w)); rewrite ?IH; try reflexivity;
  destruct hints as [|[|] hs]; rewrite ?IH; reflexivity.
Qed.
Lemma log_lookupL_eq : forall fs kn log rb rk n sx hints acc othr oD cache,
  (othr = None \/ othr = Some (mk_lthr kn rb rk (Z.of_nat n))) ->
  (oD = None \/ oD = Some (disj_sidesF fs kn kn rb rk (Z.of_nat n))) ->
  (forall b r, lbr_lookup cache b = Some r -> r = mk_ethr (mk_lthr kn rb rk (Z.of_nat n)) (base_range kn b)) ->
  log_lookupL fs kn log rb rk n sx hints acc othr oD cache = log_lookupF fs kn log rb rk n sx hints acc.
Proof.
  intros fs kn log. induction log as [|[[kb kk] w v] rest IH]; intros rb rk n sx hints acc othr oD cache Ht HD Hc; [reflexivity|].
  cbn [log_lookupL log_lookupF].
  destruct (rel_lit rb rk (Z.of_nat n) kb kk (Z.of_nat w)); try reflexivity; [apply IH; assumption|].
  set (thr := match othr with Some t => t | None => mk_lthr kn rb rk (Z.of_nat n) end).
  assert (Hthr : thr = mk_lthr kn rb rk (Z.of_nat n)) by (destruct Ht as [-> | ->]; reflexivity).
  set (D := match oD with Some D => D | None => disj_sidesF fs kn kn rb rk (Z.of_nat n) end).
  assert (HDD : D = disj_sidesF fs kn kn rb rk (Z.of_nat n)) by (destruct HD as [-> | ->]; reflexivity).
  rewrite Hthr.
  set (T := mk_lthr kn rb rk (Z.of_nat n)) in *.
  set (brc := match lbr_lookup cache kb with Some et => (et, cache) | None => (mk_ethr T (base_range kn kb), (kb, mk_ethr T (base_range kn kb)) :: cache) end).
  assert (Hbr : fst brc = mk_ethr T (base_range kn kb) /\ forall b r, lbr_lookup (snd brc) b = Some r -> r = mk_ethr T (base_range kn b)).
  { subst brc. destruct (lbr_lookup cache kb) as [r|] eqn:Hl; cbn [fst snd].
    - split; [exact (Hc _ _ Hl) | exact Hc].
    - split; [reflexivity|]. intros b r. cbn [lbr_lookup]. destruct (expr_eqb b kb) eqn:E.
      + intros H; injection H as <-. apply expr_eqb_true in E. subst b. reflexivity.
      + apply Hc. }
  destruct Hbr as [Hfst Hsnd]. rewrite Hfst, ethr_test_eq, HDD, <- ranges_apart_stagedF_eq.
  destruct (lthr_test _ _ _ _); [apply IH; auto|].
  destruct (ranges_apart_restF _ _ _ _ _ _ _ _ _); [apply IH; auto|].
  destruct hints as [|[|] hs]; [| |reflexivity]; apply IH; auto.
Qed.


(* [comment removed for export] *)
End FPW_3.

Ltac feq_step IH :=
  first [ reflexivity
        | rewrite IH; reflexivity
        | progress (rewrite ?xinsideF_eq, ?xloF_eq, ?xhiF_eq, ?ranges_apartF_eq)
        | lazymatch goal with
          | |- (if ?x then _ else _) = _ => destruct x; cbn beta iota zeta
          | |- match ?x with _ => _ end = _ => destruct x; cbn beta iota zeta
          end ].
Section FPW_4. Context {fx : PropExec.FPState}.

Lemma know_lookupAF_eq : forall allkn segs kn rb rk n sx hints acc,
  know_lookupAF (SFS allkn) allkn segs kn rb rk n sx hints acc = know_lookupA allkn segs kn rb rk n sx hints acc.
Proof.
  intros allkn segs kn. induction kn as [|K rest IH]; intros; [reflexivity|].
  cbn [know_lookupAF know_lookupA]. repeat (feq_step IH).
Qed.
Lemma wr_coveredF_eq : forall allkn kn a n, wr_coveredF (SFS allkn) allkn kn a n = wr_covered allkn kn a n.
Proof.
  intros allkn kn a n. induction kn as [|K rest IH]; [reflexivity|].
  cbn [wr_coveredF wr_covered]. repeat (feq_step IH).
Qed.
Lemma storeok_scF_eq : forall kn a n, storeok_scF (SFS kn) kn a n = storeok_sc kn a n.
Proof. intros. unfold storeok_scF, storeok_sc. rewrite wr_coveredF_eq. reflexivity. Qed.
Lemma sym_stepF_eq : forall segs i ss scr,
  sym_stepF (facts_of (s_know ss)) (SFS (facts_of (s_know ss))) segs i ss scr = sym_step segs i ss scr.
Proof.
  intros segs i ss scr. unfold sym_stepF, sym_step.
  destruct i; rewrite ?log_lookupL_eq, ?log_lookupF_eq, ?know_lookupAF_eq, ?storeok_scF_eq by (first [left; reflexivity | intros ? ? [=]]); try reflexivity.
  destruct (log_lookup _ _ _ _ _ _ _ _); rewrite ?know_lookupAF_eq; reflexivity.
Qed.
(* [comment removed for export] *)
Lemma sym_step_know : forall segs i ss scr ss' scs scr',
  sym_step segs i ss scr = SOk ss' scs scr' -> s_know ss' = s_know ss.
Proof.
  intros segs i ss scr ss' scs scr' H. unfold sym_step in H.
  destruct i; try discriminate;
  repeat (lazymatch type of H with
          | SOk _ _ _ = SOk _ _ _ => injection H as <- _ _
          | (match ?x with _ => _ end) = _ => destruct x
          | (let (_, _) := ?x in _) = _ => destruct x
          | (if ?x then _ else _) = _ => destruct x
          end); try discriminate; try reflexivity.
Qed.

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
Inductive ptree (A : Type) : Type := PTLeaf | PTNode (l : ptree A) (o : option A) (r : ptree A).
End FPW_4.

Arguments PTLeaf {A}. Arguments PTNode {A} _ _ _.
Section FPW_5. Context {fx : PropExec.FPState}.

Fixpoint pt_get {A} (t : ptree A) (k : positive) {struct k} : option A :=
  match t with
  | PTLeaf => None
  | PTNode l o r => match k with xH => o | xO k' => pt_get l k' | xI k' => pt_get r k' end
  end.
Fixpoint pt_set {A} (k : positive) (v : A) (t : ptree A) {struct k} : ptree A :=
  match t with
  | PTLeaf => match k with
              | xH => PTNode PTLeaf (Some v) PTLeaf
              | xO k' => PTNode (pt_set k' v PTLeaf) None PTLeaf
              | xI k' => PTNode PTLeaf None (pt_set k' v PTLeaf)
              end
  | PTNode l o r => match k with
                    | xH => PTNode l (Some v) r
                    | xO k' => PTNode (pt_set k' v l) o r
                    | xI k' => PTNode l o (pt_set k' v r)
                    end
  end.
Lemma pt_gss : forall A (k : positive) (v : A) t, pt_get (pt_set k v t) k = Some v.
Proof. induction k; destruct t; cbn; auto. Qed.
Lemma pt_gso : forall A (k k' : positive) (v : A) t, k <> k' -> pt_get (pt_set k' v t) k = pt_get t k.
Proof.
  induction k; destruct k', t; cbn; intros; auto;
    try (rewrite IHk by congruence); try (destruct k; reflexivity); try reflexivity; congruence.
Qed.
Lemma pt_get_leaf : forall A (k : positive), pt_get (@PTLeaf A) k = None.
Proof. destruct k; reflexivity. Qed.

Definition itab : Type := ptree instr.
Definition itab_lookup (t : itab) (pc : Z) : option instr :=
  match pc with Zpos p => pt_get t p | _ => None end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section WithSegs.
Variable segs : list Segment.

(* [comment removed for export] *)
Definition itab_entry (pc : Z) : option instr :=
  match fetch_word segs (Z_to_bv 64 pc) with
  | None => None
  | Some w => if is_ecall w then None else
              match decode_any w with
              | Some (i, sz) => if Z.eqb sz 4 then Some i else None
              | None => None
              end
  end.
Fixpoint mk_itab_fuel (n : nat) (pc : Z) (t : itab) : itab :=
  match n with
  | O => t
  | S n' => mk_itab_fuel n' (pc + 4)%Z
            (match pc, itab_entry pc with
             | Zpos p, Some i => pt_set p i t
             | _, _ => t
             end)
  end.
(* [comment removed for export] *)
Definition mk_itab (lo : Z) (n : nat) : itab := mk_itab_fuel n lo PTLeaf.
Definition itab_sound (t : itab) : Prop :=
  forall pc i, itab_lookup t pc = Some i -> itab_entry pc = Some i.
Lemma mk_itab_fuel_sound : forall n pc t, itab_sound t -> itab_sound (mk_itab_fuel n pc t).
Proof.
  induction n as [|n IH]; intros pc t Ht; cbn; [exact Ht|].
  apply IH. destruct pc as [|p|p]; try exact Ht.
  destruct (itab_entry (Zpos p)) as [i|] eqn:E; [|exact Ht].
  intros pc' i'. unfold itab_lookup. destruct pc' as [|p'|p']; try discriminate.
  destruct (Pos.eq_dec p' p) as [->|Hne].
  - rewrite pt_gss. intros H; injection H as <-. exact E.
  - rewrite pt_gso by exact Hne. exact (Ht (Zpos p') i').
Qed.
Lemma mk_itab_sound : forall lo n, itab_sound (mk_itab lo n).
Proof.
  intros lo n. apply mk_itab_fuel_sound. intros pc i. unfold itab_lookup.
  destruct pc; try discriminate. rewrite pt_get_leaf. discriminate.
Qed.

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
              match sym_step segs i ss scr with
              | SOk ss' scs scr' => sym_exec f false stops scr' ss' (sc_add scs acc)
              | SStop => (ss, acc, scr)
              end
          end
      end
  end.

(* [comment removed for export] *)
Definition scr_nil : scripts := SCR [] [] [].

Fixpoint sym_execS (fuel : nat) (first : bool) (stops : list Z) (ss : sym_state) : sym_state :=
  match fuel with
  | O => ss
  | S f =>
      if (negb first && existsb (Z.eqb (s_pc ss)) stops)%bool then ss else
      match fetch_word segs (Z_to_bv 64 (s_pc ss)) with
      | None => ss
      | Some w =>
          if is_ecall w then ss else
          match decode_any w with
          | None => ss
          | Some (i, sz) =>
              if negb (Z.eqb sz 4) then ss else
              match sym_step segs i ss scr_nil with
              | SOk ss' [] _ => sym_execS f false stops ss'
              | _ => ss
              end
          end
      end
  end.

(* [comment removed for export] *)
Fixpoint sym_execT (t : itab) (fuel : nat) (first : bool) (stops : list Z) (ss : sym_state) : sym_state :=
  match fuel with
  | O => ss
  | S f =>
      if (negb first && existsb (Z.eqb (s_pc ss)) stops)%bool then ss else
      match itab_lookup t (s_pc ss) with
      | None => ss
      | Some i =>
          match sym_step segs i ss scr_nil with
          | SOk ss' [] _ => sym_execT t f false stops ss'
          | _ => ss
          end
      end
  end.

(* [comment removed for export] *)
Fixpoint sym_execTF (fk : list kentry) (fs : list sfact) (t : itab) (fuel : nat) (first : bool) (stops : list Z)
         (ss : sym_state) : sym_state :=
  match fuel with
  | O => ss
  | S f =>
      if (negb first && existsb (Z.eqb (s_pc ss)) stops)%bool then ss else
      match itab_lookup t (s_pc ss) with
      | None => ss
      | Some i =>
          match sym_stepF fk fs segs i ss scr_nil with
          | SOk ss' [] _ => sym_execTF fk fs t f false stops ss'
          | _ => ss
          end
      end
  end.
Definition sym_execT' (t : itab) (fuel : nat) (first : bool) (stops : list Z) (ss : sym_state) : sym_state :=
  let fk := facts_of (s_know ss) in
  sym_execTF fk (SFS fk) t fuel first stops ss.
Lemma sym_execTF_eq : forall t fuel first stops ss,
  sym_execTF (facts_of (s_know ss)) (SFS (facts_of (s_know ss))) t fuel first stops ss = sym_execT t fuel first stops ss.
Proof.
  intros t fuel. induction fuel as [|f IH]; intros first stops ss; [reflexivity|].
  cbn [sym_execTF sym_execT]. destruct (negb first && existsb (Z.eqb (s_pc ss)) stops)%bool; [reflexivity|].
  destruct (itab_lookup t (s_pc ss)) as [i|]; [|reflexivity].
  rewrite sym_stepF_eq. destruct (sym_step segs i ss scr_nil) as [ss' scs scr'|] eqn:Hs; [|reflexivity].
  destruct scs; [|reflexivity]. rewrite <- (sym_step_know _ _ _ _ _ _ _ Hs). apply IH.
Qed.
Lemma sym_execT'_eq : forall t fuel first stops ss,
  sym_execT' t fuel first stops ss = sym_execT t fuel first stops ss.
Proof. intros. unfold sym_execT'. apply sym_execTF_eq. Qed.

End WithSegs.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition kzero_cut (kn : list kentry) (wb : expr) (wk : Z) (wn : expr)
           (kb : expr) (kk : Z) (len : expr) : list kentry :=
  let ws := mkAlu ALU_ADD wb (ELit wk) in
  let ks := mkAlu ALU_ADD kb (ELit kk) in
  (* [comment removed for export] *)
  let low :=
    if (if lin_ge0 kn [(kb, kk)] [(wb, wk)] then false   (* [comment removed for export] *)
        else if lin_ge0 kn [(wb, wk)] [(kb, kk)] then lin_ge0 kn [(kb, kk); (len, 0%Z)] [(wb, wk)] else false)
    then [KZero (SA kb kk) (mkAlu ALU_SUB ws ks)] else [] in
  let high :=
    if (if lin_ge0 kn [(kb, kk); (len, 0%Z)] [(wb, wk); (wn, 0%Z)]            (* [comment removed for export] *)
        then if lin_ge0 kn [(wb, wk); (wn, 0%Z)] [(kb, kk)]                    (* [comment removed for export] *)
             then lin_ge0 kn [(ELit 0, (two64 - 1)%Z)] [(kb, kk); (len, 0%Z)]  (* [comment removed for export] *)
             else false
        else false)
    then let we := mkAlu ALU_ADD ws wn in
         let '(hb, ho) := split_lit we in
         let ha := if (lin_ge0 kn [(hb, ho)] [(wb, wk); (wn, 0%Z)] && lin_ge0 kn [(wb, wk); (wn, 0%Z)] [(hb, ho)])%bool
                   then SA hb ho else SA we 0%Z in
         [KZero ha (mkAlu ALU_SUB (mkAlu ALU_ADD ks len) we)]
    else [] in
  low ++ high.

Definition prune1 (allkn : list kentry) (wa : saddr) (w : nat) (wv : expr) (K : kentry) (hints : list bool)
  : list kentry * list sidecond * list bool :=
  let k := a_off wa in
  let diffbase (ka : saddr) (kl : expr) :=
    let apart := ranges_apart_x allkn (a_base wa) k (elen w) (a_base ka) (a_off ka) kl in
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
        | _ => if Z.leb (k + Z.of_nat w) kk then ([K], [], hints)
               else (kzero_cut allkn (a_base wa) k (elen w) kb kk len, [], hints)
        end
      else if ranges_apart_x allkn (a_base wa) k (elen w) kb kk len then ([K], [], hints)
      else match kzero_cut allkn (a_base wa) k (elen w) kb kk len with
           | [] => diffbase (SA kb kk) len
           | cut => (cut, [], hints)
           end
  | KWord (SA kb kk) w' v =>
      if expr_eqb kb (a_base wa) then
        (if (Z.leb (kk + Z.of_nat w') k || Z.leb (k + Z.of_nat w) kk)%bool
         then ([K], [], hints) else ([], [], hints))
      else if ranges_apart_x allkn (a_base wa) k (elen w) kb kk (elen w') then ([K], [], hints)
      else if (Nat.eqb w 1 && Nat.eqb w' 1 && expr_eqb wv v)%bool
      then ([K], [], hints)   (* [comment removed for export] *)
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

Fixpoint prune (allkn : list kentry) (wa : saddr) (w : nat) (wv : expr) (kn : list kentry) (hints : list bool)
  : list kentry * list sidecond * list bool :=
  match kn with
  | [] => ([], [], hints)
  | K :: rest =>
      let '(kept, scs1, hs1) := prune1 allkn wa w wv K hints in
      let '(r, scs2, hs2) := prune allkn wa w wv rest hs1 in
      (kept ++ r, scs1 ++ scs2, hs2)
  end.

(* [comment removed for export] *)
Definition prune1p (allkn : list kentry) (sp : sprep) (wa : saddr) (w : nat) (wv : expr) (K : kentry) (hints : list bool)
  : list kentry * list sidecond * list bool :=
  let k := a_off wa in
  let diffbase (ka : saddr) (kl : expr) :=
    let apart := ranges_apart_p allkn sp (a_base wa) k (elen w) (a_base ka) (a_off ka) kl in
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
        | _ => if Z.leb (k + Z.of_nat w) kk then ([K], [], hints)
               else (kzero_cut allkn (a_base wa) k (elen w) kb kk len, [], hints)
        end
      else if ranges_apart_p allkn sp (a_base wa) k (elen w) kb kk len then ([K], [], hints)
      else match kzero_cut allkn (a_base wa) k (elen w) kb kk len with
           | [] => diffbase (SA kb kk) len
           | cut => (cut, [], hints)
           end
  | KWord (SA kb kk) w' v =>
      if expr_eqb kb (a_base wa) then
        (if (Z.leb (kk + Z.of_nat w') k || Z.leb (k + Z.of_nat w) kk)%bool
         then ([K], [], hints) else ([], [], hints))
      else if ranges_apart_p allkn sp (a_base wa) k (elen w) kb kk (elen w') then ([K], [], hints)
      else if (Nat.eqb w 1 && Nat.eqb w' 1 && expr_eqb wv v)%bool
      then ([K], [], hints)   (* [comment removed for export] *)
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

Fixpoint prunep (allkn : list kentry) (sp : sprep) (wa : saddr) (w : nat) (wv : expr) (kn : list kentry) (hints : list bool)
  : list kentry * list sidecond * list bool :=
  match kn with
  | [] => ([], [], hints)
  | K :: rest =>
      let '(kept, scs1, hs1) := prune1p allkn sp wa w wv K hints in
      let '(r, scs2, hs2) := prunep allkn sp wa w wv rest hs1 in
      (kept ++ r, scs1 ++ scs2, hs2)
  end.

(* [comment removed for export] *)
Definition ranges_apart_pc (kn : list kentry) (sp : sprep) (b1 : expr) (k1 : Z) (n1 : expr)
           (br2 : option (Z * Z)) (b2 : expr) (k2 : Z) (n2 : expr) : bool :=
  match n1, n2 with
  | ELit z1, ELit z2 =>
      let m1 := zlit64 z1 in let m2 := zlit64 z2 in
      if (match sp_rng sp, br2 with
          | Some (lo1, hi1), Some (lo2, hi2) =>
              (Z.leb (hi1 + k1 + m1) (lo2 + k2) || Z.leb (hi2 + k2 + m2) (lo1 + k1))%bool
          | _, _ => false
          end) then true
      else if in_sides kn (sp_D sp) b2 k2 m2 then true
      else lin_apart kn b1 k1 m1 b2 k2 m2
  | _, _ =>
    if (match sp_rng sp, br2, sp_h1 sp, xhi kn n2 with
        | Some (lo1, hi1), Some (lo2, hi2), Some h1, Some h2 =>
            (Z.leb (hi1 + k1 + h1) (lo2 + k2) || Z.leb (hi2 + k2 + h2) (lo1 + k1))%bool
        | _, _, _, _ => false
        end) then true
    else if in_sides_x kn (sp_Dx sp) b2 k2 n2 then true
    else if negb (shares_var b1 b2) then false
    else if lin_ge0 kn [(b2, k2)] [(b1, k1); (n1, 0%Z)] then true
    else lin_ge0 kn [(b1, k1)] [(b2, k2); (n2, 0%Z)]
  end.

(* [comment removed for export] *)
Definition kbase (K : kentry) : option expr :=
  match K with
  | KZero (SA kb _) _ | KWord (SA kb _) _ _ | KBlob (SA kb _) _ _ => Some kb
  | _ => None
  end.

(* [comment removed for export] *)
Definition prune1pc (allkn : list kentry) (sp : sprep) (wa : saddr) (w : nat) (wv : expr) (K : kentry) (hints : list bool)
  (br2 : option (Z * Z)) : list kentry * list sidecond * list bool :=
  let k := a_off wa in
  let diffbase (ka : saddr) (kl : expr) :=
    let apart := ranges_apart_pc allkn sp (a_base wa) k (elen w) br2 (a_base ka) (a_off ka) kl in
    if apart then ([K], [], hints) else
    match hints with
    | true :: hs => ([K], [SCDisj wa (elen w) ka kl], hs)
    | false :: hs => ([], [], hs)
    | [] => ([], [], [])
    end in
  match K with
  | KAlign _ _ | KRange _ _ _ | KWr _ _ | KDisj _ _ _ _ | KImg _ _ => prune1p allkn sp wa w wv K hints
  | KZero (SA kb kk) len =>
      if expr_eqb kb (a_base wa) then prune1p allkn sp wa w wv K hints
      else if ranges_apart_pc allkn sp (a_base wa) k (elen w) br2 kb kk len then ([K], [], hints)
      else match kzero_cut allkn (a_base wa) k (elen w) kb kk len with
           | [] => diffbase (SA kb kk) len
           | cut => (cut, [], hints)
           end
  | KWord (SA kb kk) w' v =>
      if expr_eqb kb (a_base wa) then prune1p allkn sp wa w wv K hints
      else if ranges_apart_pc allkn sp (a_base wa) k (elen w) br2 kb kk (elen w') then ([K], [], hints)
      else if (Nat.eqb w 1 && Nat.eqb w' 1 && expr_eqb wv v)%bool
      then ([K], [], hints)
      else diffbase (SA kb kk) (elen w')
  | KBlob (SA kb kk) len bk =>
      if expr_eqb kb (a_base wa) then prune1p allkn sp wa w wv K hints
      else diffbase (SA kb kk) len
  end.

Fixpoint br_lookup (c : list (expr * option (Z * Z))) (b : expr) : option (option (Z * Z)) :=
  match c with
  | [] => None
  | (b', r) :: rest => if expr_eqb b b' then Some r else br_lookup rest b
  end.

Fixpoint prunepc (allkn : list kentry) (sp : sprep) (wa : saddr) (w : nat) (wv : expr) (kn : list kentry) (hints : list bool)
  (cache : list (expr * option (Z * Z))) : list kentry * list sidecond * list bool :=
  match kn with
  | [] => ([], [], hints)
  | K :: rest =>
      let '(br2, cache') :=
        match kbase K with
        | Some kb => match br_lookup cache kb with
                     | Some r => (r, cache)
                     | None => let r := base_range allkn kb in (r, (kb, r) :: cache)
                     end
        | None => (None, cache)
        end in
      let '(kept, scs1, hs1) := prune1pc allkn sp wa w wv K hints br2 in
      let '(r, scs2, hs2) := prunepc allkn sp wa w wv rest hs1 cache' in
      (kept ++ r, scs1 ++ scs2, hs2)
  end.

(* [comment removed for export] *)
Fixpoint carry_ref (log : list sentry) (kn : list kentry) (hints : list bool)
  : list kentry * list sidecond * list bool :=
  match log with
  | [] => (kn, [], hints)
  | SE a w v :: older =>
      let '(kn1, scs1, hs1) := carry_ref older kn hints in
      let fk := facts_of kn1 in
      let '(kn2, scs2, hs2) := prunepc fk (mk_sprep fk (a_base a) (a_off a) (elen w)) a w v kn1 hs1 [] in   (* [comment removed for export] *)
      (KWord a w v :: kn2, scs1 ++ scs2, hs2)
  end.


(* [comment removed for export] *)
Lemma kzero_cut_fk : forall kn wb wk wn kb kk len,
  kzero_cut (facts_of kn) wb wk wn kb kk len = kzero_cut kn wb wk wn kb kk len.
Proof.
  intros. unfold kzero_cut. rewrite !lin_ge0_fk.
  destruct (split_lit _) as [hb ho]. rewrite !lin_ge0_fk. reflexivity.
Qed.
End FPW_5.


Local Open Scope Z_scope.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Section FPW_6. Context {fx : PropExec.FPState}.

Inductive xkind : Type := XKNever | XKNum (u v : Z) | XKShare.

Record sdesc : Type := SD {
  sd_c : saddr; sd_m : expr;   (* [comment removed for export] *)
  sd_same : bool;              (* [comment removed for export] *)
  sd_lim : option Z;           (* [comment removed for export] *)
  sd_kind : xkind }.

Definition mk_sd (fs : list sfact) (fk : list kentry) (b : expr) (br : option (Z * Z)) (c : saddr) (m : expr) : sdesc :=
  let cb := a_base c in let ck := a_off c in
  let same := expr_eqb b cb in
  SD c m same
     (if same then match xloF fs fk m with Some ml => Some (ck + ml) | None => None end else None)
     (if shares_var b cb then XKShare
      else if novars cb then
        match xloF fs fk cb, xhiF fs fk cb with
        | Some lo2, Some hi2 =>
            if Z.eqb lo2 hi2 then
              match br, xloF fs fk m with
              | Some (lo1, hi1), Some l2 => XKNum (lo2 + ck - lo1) (lo2 + ck + l2 - hi1)
              | _, _ => XKNever
              end
            else XKNever
        | _, _ => XKNever
        end
      else XKNever).

(* [comment removed for export] *)
Record sideinfo : Type := SDI {
  sdi_c : saddr; sdi_m : expr;
  sdi_xlom : option Z;         (* [comment removed for export] *)
  sdi_nov : bool;              (* [comment removed for export] *)
  sdi_pt : option Z }.         (* [comment removed for export] *)

Definition mk_sdi (fs : list sfact) (fk : list kentry) (c : saddr) (m : expr) : sideinfo :=
  let cb := a_base c in
  SDI c m (xloF fs fk m) (novars cb)
      (if novars cb then
         match xloF fs fk cb, xhiF fs fk cb with
         | Some lo2, Some hi2 => if Z.eqb lo2 hi2 then Some lo2 else None
         | _, _ => None
         end
       else None).

(* [comment removed for export] *)
Definition mk_sd' (fs : list sfact) (fk : list kentry) (b : expr) (br : option (Z * Z)) (d : sideinfo) : sdesc :=
  let c := sdi_c d in let m := sdi_m d in
  let cb := a_base c in let ck := a_off c in
  let same := expr_eqb b cb in
  SD c m same
     (if same then match sdi_xlom d with Some ml => Some (ck + ml) | None => None end else None)
     (if shares_var b cb then XKShare
      else if sdi_nov d then
        match sdi_pt d with
        | Some lo2 =>
            match br, sdi_xlom d with
            | Some (lo1, hi1), Some l2 => XKNum (lo2 + ck - lo1) (lo2 + ck + l2 - hi1)
            | _, _ => XKNever
            end
        | None => XKNever
        end
      else XKNever).

Fixpoint kdisj_sdis (fs : list sfact) (fk : list kentry) (kn : list kentry) : list (sideinfo * sideinfo) :=
  match kn with
  | [] => []
  | KDisj c1 m1 c2 m2 :: r => (mk_sdi fs fk c1 m1, mk_sdi fs fk c2 m2) :: kdisj_sdis fs fk r
  | _ :: r => kdisj_sdis fs fk r
  end.

(* [comment removed for export] *)
Definition xk_eval (fs : list sfact) (fk : list kentry) (b : expr) (d : sdesc) (k : Z) (n : expr) (h : option Z) : bool :=
  match sd_kind d with
  | XKNever => false
  | XKNum u v => match h with Some hv => (Z.leb u k && Z.leb (k + hv) v)%bool | None => false end
  | XKShare => xinside0F fs fk b k n (a_base (sd_c d)) (a_off (sd_c d)) (sd_m d)
  end.

(* [comment removed for export] *)
Definition sd_eval (fs : list sfact) (fk : list kentry) (b : expr) (d : sdesc) (k n : Z) : bool :=
  if (if sd_same d then
        if Z.leb (a_off (sd_c d)) k then match sd_lim d with Some L => Z.leb (k + n) L | None => false end
        else false
      else false) then true
  else if (if Z.leb 0 n then Z.ltb n two64 else false) then xk_eval fs fk b d k (ELit n) (Some n) else false.

(* [comment removed for export] *)
Definition sd_useless (d : sdesc) : bool :=
  if sd_same d then false else match sd_kind d with XKNever => true | _ => false end.

(* [comment removed for export] *)
Fixpoint kdisj_sides (kn : list kentry) : list (saddr * expr * saddr * expr) :=
  match kn with
  | [] => []
  | KDisj c1 m1 c2 m2 :: r => (c1, m1, c2, m2) :: kdisj_sides r
  | _ :: r => kdisj_sides r
  end.

(* [comment removed for export] *)
Record cinfo : Type := CI { ci_br : option (Z * Z); ci_sds : list (sdesc * sdesc) }.

Definition mk_ci (fs : list sfact) (fk : list kentry) (tbl : list (saddr * expr * saddr * expr)) (b : expr) : cinfo :=
  let br := base_range fk b in
  CI br (map (fun t => let '(c1, m1, c2, m2) := t in (mk_sd fs fk b br c1 m1, mk_sd fs fk b br c2 m2)) tbl).

Definition mk_ci' (fs : list sfact) (fk : list kentry) (tbl : list (sideinfo * sideinfo)) (b : expr) : cinfo :=
  let br := base_range fk b in
  CI br (map (fun t => (mk_sd' fs fk b br (fst t), mk_sd' fs fk b br (snd t))) tbl).

(* [comment removed for export] *)
Definition dmask_of (fs : list sfact) (fk : list kentry) (b1 : expr) (k1 m1 : Z) (sds : list (sdesc * sdesc)) : list (bool * bool) :=
  map (fun p => (sd_eval fs fk b1 (fst p) k1 m1, sd_eval fs fk b1 (snd p) k1 m1)) sds.
Definition dxmask_of (fs : list sfact) (fk : list kentry) (b1 : expr) (k1 : Z) (n1 : expr) (h1 : option Z) (sds : list (sdesc * sdesc)) : list (bool * bool) :=
  map (fun p => (xk_eval fs fk b1 (fst p) k1 n1 h1, xk_eval fs fk b1 (snd p) k1 n1 h1)) sds.

(* [comment removed for export] *)
Fixpoint dselect (drop : bool) (mask : list (bool * bool)) (sds : list (sdesc * sdesc)) : list sdesc :=
  match mask, sds with
  | (in1, in2) :: mr, (d1, d2) :: sr =>
      let r := dselect drop mr sr in
      let r1 := if in2 then (if (drop && sd_useless d1)%bool then r else d1 :: r) else r in
      if in1 then (if (drop && sd_useless d2)%bool then r1 else d2 :: r1) else r1
  | _, _ => []
  end.

Fixpoint exists_sd (fs : list sfact) (fk : list kentry) (b : expr) (k n : Z) (ds : list sdesc) : bool :=
  match ds with
  | [] => false
  | d :: r => if sd_eval fs fk b d k n then true else exists_sd fs fk b k n r
  end.
Fixpoint exists_xk (fs : list sfact) (fk : list kentry) (b : expr) (k : Z) (n : expr) (h : option Z) (ds : list sdesc) : bool :=
  match ds with
  | [] => false
  | d :: r => if xk_eval fs fk b d k n h then true else exists_xk fs fk b k n h r
  end.

(* [comment removed for export] *)
Record sinfo : Type := SI {
  si_b1 : expr; si_k1 : Z; si_n1 : expr;
  si_m1 : option Z;                 (* [comment removed for export] *)
  si_h1 : option Z;                 (* [comment removed for export] *)
  si_br1 : option (Z * Z);          (* [comment removed for export] *)
  si_sds1 : list (sdesc * sdesc);   (* [comment removed for export] *)
  si_dmask : list (bool * bool) }.  (* [comment removed for export] *)

(* [comment removed for export] *)
Record ccache : Type := CC {
  cc_tbl : list (sideinfo * sideinfo);           (* [comment removed for export] *)
  cc_fs : list sfact;                            (* [comment removed for export] *)
  cc_bases : list (expr * cinfo);
  cc_xh : list (expr * option Z) }.

(* [comment removed for export] *)
Record sentryinfo : Type := SEI { se_thr : option (Z * Z); se_dsel : list sdesc; se_sh : bool; se_sds : list (sdesc * sdesc) }.
Record scache : Type := ST { st_bs : list (expr * sentryinfo); st_dx : option (list (bool * bool)) }.

Fixpoint alookup {A : Type} (l : list (expr * A)) (e : expr) : option A :=
  match l with
  | [] => None
  | (e', a) :: r => if expr_eqb e e' then Some a else alookup r e
  end.

Definition cc_get (fk : list kentry) (cc : ccache) (b : expr) : cinfo * ccache :=
  match alookup (cc_bases cc) b with
  | Some ci => (ci, cc)
  | None => let ci := mk_ci' (cc_fs cc) fk (cc_tbl cc) b in (ci, CC (cc_tbl cc) (cc_fs cc) ((b, ci) :: cc_bases cc) (cc_xh cc))
  end.

Definition xh_get (fk : list kentry) (cc : ccache) (n : expr) : option Z * ccache :=
  match alookup (cc_xh cc) n with
  | Some h => (h, cc)
  | None => let h := xhiF (cc_fs cc) fk n in (h, CC (cc_tbl cc) (cc_fs cc) (cc_bases cc) ((n, h) :: cc_xh cc))
  end.

Definition lit_of_len (n1 : expr) : option Z := match n1 with ELit z1 => Some (zlit64 z1) | _ => None end.

Definition mk_si (fs : list sfact) (fk : list kentry) (b1 : expr) (k1 : Z) (n1 : expr) (ci1 : cinfo) : sinfo :=
  let m1 := lit_of_len n1 in
  SI b1 k1 n1 m1 (xhiF fs fk n1) (ci_br ci1) (ci_sds ci1)
     (match m1 with Some m => dmask_of fs fk b1 k1 m (ci_sds ci1) | None => [] end).

Definition mk_thr (si : sinfo) (br2 : option (Z * Z)) : option (Z * Z) :=
  match si_br1 si, br2, si_h1 si with
  | Some (lo1, hi1), Some (lo2, hi2), Some h1 => Some (hi1 + si_k1 si + h1 - lo2, lo1 + si_k1 si - hi2)
  | _, _, _ => None
  end.

Definition mk_sei (si : sinfo) (b2 : expr) (ci2 : cinfo) : sentryinfo :=
  SEI (mk_thr si (ci_br ci2)) (dselect true (si_dmask si) (ci_sds ci2)) (shares_var (si_b1 si) b2) (ci_sds ci2).

Definition st_get (fk : list kentry) (si : sinfo) (cc : ccache) (st : scache) (b2 : expr)
  : sentryinfo * ccache * scache :=
  match alookup (st_bs st) b2 with
  | Some e => (e, cc, (* [comment removed for export] *)
               match st_bs st with
               | (b', _) :: _ => if expr_eqb b2 b' then st else ST ((b2, e) :: st_bs st) (st_dx st)
               | [] => st
               end)
  | None =>
      let '(ci2, cc') := cc_get fk cc b2 in
      let e := mk_sei si b2 ci2 in
      (e, cc', ST ((b2, e) :: st_bs st) (st_dx st))
  end.

Definition dx_get (fs : list sfact) (fk : list kentry) (si : sinfo) (st : scache) : list (bool * bool) * scache :=
  match st_dx st with
  | Some m => (m, st)
  | None =>
      let m := dxmask_of fs fk (si_b1 si) (si_k1 si) (si_n1 si) (si_h1 si) (si_sds1 si) in
      (m, ST (st_bs st) (Some m))
  end.

(* [comment removed for export] *)
Definition thr_test (thr : option (Z * Z)) (k2 : Z) (h2 : option Z) : bool :=
  match thr, h2 with
  | Some (tA, tB), Some h => if Z.leb tA k2 then true else Z.leb (k2 + h) tB
  | _, _ => false
  end.

(* [comment removed for export] *)
Definition apartf (fk : list kentry) (si : sinfo) (b2 : expr) (k2 : Z) (n2 : expr) (cc : ccache) (st : scache)
  : bool * ccache * scache :=
  let '(e, cc, st) := st_get fk si cc st b2 in
  match si_m1 si, n2 with
  | Some m1, ELit z2 =>
      let m2 := zlit64 z2 in
      if thr_test (se_thr e) k2 (Some m2) then (true, cc, st)
      else if exists_sd (cc_fs cc) fk b2 k2 m2 (se_dsel e) then (true, cc, st)
      else ((if se_sh e then lin_apart0F (cc_fs cc) fk (si_b1 si) (si_k1 si) m1 b2 k2 m2 else false), cc, st)
  | _, _ =>
      let '(h2, cc) := xh_get fk cc n2 in
      if thr_test (se_thr e) k2 h2 then (true, cc, st)
      else
        let '(dxm, st) := dx_get (cc_fs cc) fk si st in
        if exists_xk (cc_fs cc) fk b2 k2 n2 h2 (dselect false dxm (se_sds e)) then (true, cc, st)
        else ((if se_sh e then
                 if lin_ge0F (cc_fs cc) fk [(b2, k2)] [(si_b1 si, si_k1 si); (si_n1 si, 0%Z)] then true
                 else lin_ge0F (cc_fs cc) fk [(si_b1 si, si_k1 si)] [(b2, k2); (n2, 0%Z)]
               else false), cc, st)
  end.

Definition prune1f (fk : list kentry) (si : sinfo) (wa : saddr) (w : nat) (wv : expr) (K : kentry) (hints : list bool)
  (cc : ccache) (st : scache) : (list kentry * list sidecond * list bool) * ccache * scache :=
  let k := a_off wa in
  let hint_case (ka : saddr) (kl : expr) :=
    match hints with
    | true :: hs => ([K], [SCDisj wa (elen w) ka kl], hs)
    | false :: hs => ([], [], hs)
    | [] => ([], [], [])
    end in
  match K with
  | KAlign _ _ | KRange _ _ _ | KWr _ _ | KDisj _ _ _ _ => (([K], [], hints), cc, st)
  | KImg lo hi =>
      match a_base wa with
      | ELit 0 =>
          let r1 := if Z.ltb lo (Z.min k hi) then [KImg lo (Z.min k hi)] else [] in
          let lo2 := Z.max lo (k + Z.of_nat w) in
          let r2 := if Z.ltb lo2 hi then [KImg lo2 hi] else [] in
          ((r1 ++ r2, [], hints), cc, st)
      | _ => if Z.ltb (hi - lo) two64 then
               let '(ap, cc, st) := apartf fk si (ELit 0) lo (ELit (hi - lo)) cc st in
               ((if ap then ([K], [], hints) else hint_case (SA (ELit 0) lo) (ELit (hi - lo))), cc, st)
             else (([], [], hints), cc, st)
      end
  | KZero (SA kb kk) len =>
      if expr_eqb kb (a_base wa) then
        ((match len with
          | ELit l0 =>
              let l := (l0 mod two64)%Z in
              let hi1 := Z.min k (kk + l) in
              let r1 := if Z.ltb kk hi1 then [KZero (SA kb kk) (ELit (hi1 - kk))] else [] in
              let lo2 := Z.max kk (k + Z.of_nat w) in
              let r2 := if Z.ltb lo2 (kk + l) then [KZero (SA kb lo2) (ELit (kk + l - lo2))] else [] in
              (r1 ++ r2, [], hints)
          | _ => if Z.leb (k + Z.of_nat w) kk then ([K], [], hints)
                 else (kzero_cut fk (a_base wa) k (elen w) kb kk len, [], hints)
          end), cc, st)
      else
        let '(ap, cc, st) := apartf fk si kb kk len cc st in
        ((if ap then ([K], [], hints)
          else match kzero_cut fk (a_base wa) k (elen w) kb kk len with
               | [] => hint_case (SA kb kk) len
               | cut => (cut, [], hints)
               end), cc, st)
  | KWord (SA kb kk) w' v =>
      if expr_eqb kb (a_base wa) then
        ((if (Z.leb (kk + Z.of_nat w') k || Z.leb (k + Z.of_nat w) kk)%bool
          then ([K], [], hints) else ([], [], hints)), cc, st)
      else
        let '(ap, cc, st) := apartf fk si kb kk (elen w') cc st in
        ((if ap then ([K], [], hints)
          else if (Nat.eqb w 1 && Nat.eqb w' 1 && expr_eqb wv v)%bool then ([K], [], hints)
          else hint_case (SA kb kk) (elen w')), cc, st)
  | KBlob (SA kb kk) len bk =>
      if expr_eqb kb (a_base wa) then
        ((match len with
          | ELit l0 =>
              let l := (l0 mod two64)%Z in
              (if (Z.leb (kk + l) k || Z.leb (k + Z.of_nat w) kk)%bool
               then ([K], [], hints) else ([], [], hints))
          | _ => if Z.leb (k + Z.of_nat w) kk then ([K], [], hints) else ([], [], hints)
          end), cc, st)
      else
        let '(ap, cc, st) := apartf fk si kb kk len cc st in
        ((if ap then ([K], [], hints) else hint_case (SA kb kk) len), cc, st)
  end.

Fixpoint prunef (fk : list kentry) (si : sinfo) (wa : saddr) (w : nat) (wv : expr) (kn : list kentry) (hints : list bool)
  (cc : ccache) (st : scache) : (list kentry * list sidecond * list bool) * ccache * scache :=
  match kn with
  | [] => (([], [], hints), cc, st)
  | K :: rest =>
      let '(r1, cc, st) := prune1f fk si wa w wv K hints cc st in
      let '(kept, scs1, hs1) := r1 in
      let '(r2, cc, st) := prunef fk si wa w wv rest hs1 cc st in
      let '(r, scs2, hs2) := r2 in
      ((kept ++ r, scs1 ++ scs2, hs2), cc, st)
  end.

Definition prune_store (fk : list kentry) (cc : ccache) (wa : saddr) (w : nat) (wv : expr) (kn : list kentry) (hints : list bool)
  : (list kentry * list sidecond * list bool) * ccache :=
  let '(ci1, cc) := cc_get fk cc (a_base wa) in
  let si := mk_si (cc_fs cc) fk (a_base wa) (a_off wa) (elen w) ci1 in
  let '(r, cc, _) := prunef fk si wa w wv kn hints cc (ST [] None) in
  (r, cc).

Fixpoint carryF (fk : list kentry) (cc : ccache) (log : list sentry) (kn : list kentry) (hints : list bool)
  : (list kentry * list sidecond * list bool) * ccache :=
  match log with
  | [] => ((kn, [], hints), cc)
  | SE a w v :: older =>
      let '(r1, cc) := carryF fk cc older kn hints in
      let '(kn1, scs1, hs1) := r1 in
      let '(r2, cc) := prune_store fk cc a w v kn1 hs1 in
      let '(kn2, scs2, hs2) := r2 in
      ((KWord a w v :: kn2, scs1 ++ scs2, hs2), cc)
  end.

Definition carry_p5 (log : list sentry) (kn : list kentry) (hints : list bool)
  : list kentry * list sidecond * list bool :=
  match log with
  | [] => (kn, [], hints)
  | _ => let fk := facts_of kn in let fs := SFS fk in fst (carryF fk (CC (kdisj_sdis fs fk fk) fs [] []) log kn hints)
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Record stctx : Type := SX { sx_wa : saddr; sx_w : nat; sx_wv : expr; sx_si : sinfo }.

Definition mk_stctx (fk : list kentry) (cc : ccache) (e : sentry) : stctx * ccache :=
  match e with SE wa w wv =>
    let '(ci1, cc) := cc_get fk cc (a_base wa) in
    (SX wa w wv (mk_si (cc_fs cc) fk (a_base wa) (a_off wa) (elen w) ci1), cc)
  end.

(* [comment removed for export] *)
Fixpoint stctxs_of (fk : list kentry) (cc : ccache) (log : list sentry) : list stctx * ccache :=
  match log with
  | [] => ([], cc)
  | e :: older =>
      let '(r, cc) := stctxs_of fk cc older in      (* [comment removed for export] *)
      let '(sx, cc) := mk_stctx fk cc e in
      (r ++ [sx], cc)
  end.

(* [comment removed for export] *)
Definition klit (K : kentry) : option (expr * Z * Z) :=
  match K with
  | KWord (SA kb kk) w' _ => Some (kb, kk, kk + zlit64 (Z.of_nat w'))
  | KZero (SA kb kk) (ELit z) | KBlob (SA kb kk) (ELit z) _ => Some (kb, kk, kk + zlit64 z)
  | KImg lo hi => if Z.ltb (hi - lo) two64 then Some (ELit 0, lo, lo + zlit64 (hi - lo)) else None
  | _ => None
  end.
Definition klit_ok (K : kentry) : bool :=
  match K with
  | KWord _ _ _ | KZero _ (ELit _) | KBlob _ (ELit _) _ => true
  | KImg lo hi => Z.ltb (hi - lo) two64
  | _ => false
  end.

(* [comment removed for export] *)
Fixpoint bounds_acc (kn : list kentry) (cur : option (expr * Z * Z)) (acc : list (expr * Z * Z))
  : list (expr * Z * Z) :=
  match kn with
  | [] => match cur with Some c => c :: acc | None => acc end
  | K :: rest =>
      match klit K with
      | None => bounds_acc rest cur acc
      | Some (b2, lo, hi) =>
          match cur with
          | Some (b, l, h) =>
              if expr_eqb b2 b then bounds_acc rest (Some (b, Z.min l lo, Z.max h hi)) acc
              else bounds_acc rest (Some (b2, lo, hi)) ((b, l, h) :: acc)
          | None => bounds_acc rest (Some (b2, lo, hi)) acc
          end
      end
  end.

Fixpoint group_bounds (tbl : list (expr * Z * Z)) (b2 : expr) : option (Z * Z) :=
  match tbl with
  | [] => None
  | (b, l, h) :: rest =>
      match group_bounds rest b2 with
      | Some (l', h') => if expr_eqb b2 b then Some (Z.min l l', Z.max h h') else Some (l', h')
      | None => if expr_eqb b2 b then Some (l, h) else None
      end
  end.

(* [comment removed for export] *)
Fixpoint fast_all (ds : list sdesc) (gl gh : Z) : bool :=
  match ds with
  | [] => false
  | d :: r =>
      if (if sd_same d then
            if Z.leb (a_off (sd_c d)) gl then match sd_lim d with Some L => Z.leb gh L | None => false end
            else false
          else false)
      then true else fast_all r gl gh
  end.

Definition group_all (sx : stctx) (b2 : expr) (e : sentryinfo) (gb : option (Z * Z)) : bool :=
  match gb, si_m1 (sx_si sx) with
  | Some (gl, gh), Some _ =>
      if expr_eqb b2 (a_base (sx_wa sx)) then false
      else if (match se_thr e with Some (tA, tB) => if Z.leb tA gl then true else Z.leb gh tB | None => false end)
           then true
      else fast_all (se_dsel e) gl gh
  | _, _ => false
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Record colent : Type := CE { ce_sei : sentryinfo; ce_all : bool; ce_same : option (Z * Z) }.
(* [comment removed for export] *)
Fixpoint mask_eqb (a b : list (bool * bool)) : bool :=
  match a, b with
  | [], [] => true
  | (x1, x2) :: r, (y1, y2) :: s => if Bool.eqb x1 y1 then if Bool.eqb x2 y2 then mask_eqb r s else false else false
  | _, _ => false
  end.
Inductive fcls : Type := FCnone | FCbad | FC (thr : option (Z * Z)) (md : option (list (bool * bool) * list sdesc)).
Definition thr_hull (t1 t2 : option (Z * Z)) : option (Z * Z) :=
  match t1, t2 with Some (a0, b0), Some (a, b) => Some (Z.max a0 a, Z.min b0 b) | _, _ => None end.
Definition fc_add (f : fcls) (sx : stctx) (c : colent) : fcls :=
  let si := sx_si sx in let e := ce_sei c in
  match si_m1 si with
  | None => FCbad
  | Some _ =>
      match f with
      | FCnone => FC (se_thr e) (Some (si_dmask si, se_dsel e))
      | FCbad => FCbad
      | FC thr md => FC (thr_hull thr (se_thr e))
                        (match md with Some (m, ds) => if mask_eqb m (si_dmask si) then md else None | None => None end)
      end
  end.
Definition fc_test (fs : list sfact) (fk : list kentry) (f : fcls) (b2 : expr) (k2 h : Z) : bool :=
  match f with
  | FCnone => true
  | FCbad => false
  | FC thr md => if thr_test thr k2 (Some h) then true
                 else match md with Some (_, ds) => exists_sd fs fk b2 k2 h ds | None => false end
  end.
(* [comment removed for export] *)
Record csum : Type := CSUM { cs_N : fcls; cs_A : fcls }.
Definition cs_empty : csum := CSUM FCnone FCnone.
Definition cs_add (sx : stctx) (c : colent) (s : csum) : csum :=
  CSUM (if ce_all c then cs_N s else fc_add (cs_N s) sx c) (fc_add (cs_A s) sx c).
Fixpoint cupd (cid : positive) (sx : stctx) (c : colent) (l : list (positive * csum)) : list (positive * csum) :=
  match l with
  | [] => [(cid, cs_add sx c cs_empty)]
  | (p, s) :: r => if Pos.eqb p cid then (p, cs_add sx c s) :: r else (p, s) :: cupd cid sx c r
  end.
(* [comment removed for export] *)
Fixpoint sums_of (sxs : list stctx) (ents : list colent) (cids : list positive) : list (list (positive * csum)) :=
  match sxs, ents, cids with
  | sx :: sr, c :: cr, cid :: ir =>
      let l := sums_of sr cr ir in
      (match ce_same c with Some _ => hd [] l | None => cupd cid sx c (hd [] l) end) :: l
  | _, _, _ => [[]]
  end.
(* [comment removed for export] *)
Fixpoint cid_of (tbl : list (expr * positive)) (b : expr) (nxt : positive) : positive * list (expr * positive) * positive :=
  match tbl with
  | [] => (nxt, [(b, nxt)], Pos.succ nxt)
  | (e, p) :: r => if expr_eqb e b then (p, tbl, nxt) else let '(q, r', n') := cid_of r b nxt in (q, (e, p) :: r', n')
  end.
Fixpoint cids_of (sxs : list stctx) (tbl : list (expr * positive)) (nxt : positive) : list positive :=
  match sxs with
  | [] => []
  | sx :: r => let '(p, tbl', n') := cid_of tbl (a_base (sx_wa sx)) nxt in p :: cids_of r tbl' n'
  end.

Record column : Type := COL { co_ents : list colent; co_all : bool; co_gb : option (Z * Z);
                              co_sds : list (sdesc * sdesc);                  (* [comment removed for export] *)
                              co_cids : list positive;                        (* [comment removed for export] *)
                              co_sums : list (list (positive * csum)) }.      (* [comment removed for export] *)

Fixpoint all_true (l : list colent) : bool :=
  match l with [] => true | c :: r => if ce_all c then all_true r else false end.

Definition column_of (sxs : list stctx) (b2 : expr) (ci2 : cinfo) (gb : option (Z * Z)) : column :=
  let ents := map (fun sx => let e := mk_sei (sx_si sx) b2 ci2 in
                          CE e (group_all sx b2 e gb)
                             (if expr_eqb b2 (a_base (sx_wa sx))
                              then Some (a_off (sx_wa sx), a_off (sx_wa sx) + Z.of_nat (sx_w sx)) else None)) sxs in
  let cids := cids_of sxs [] xH in
  COL ents (all_true ents) gb (ci_sds ci2) cids (sums_of sxs ents cids).

(* [comment removed for export] *)
Definition zin64 (z : Z) : bool := if Z.leb 0 z then Z.ltb z two64 else false.

Definition dxm_of (fs : list sfact) (fk : list kentry) (sx : stctx) : list (bool * bool) :=
  let si := sx_si sx in dxmask_of fs fk (si_b1 si) (si_k1 si) (si_n1 si) (si_h1 si) (si_sds1 si).

Definition quick_apartL (fs : list sfact) (fk : list kentry) (sx : stctx) (e : sentryinfo)
           (b2 : expr) (k2 : Z) (z2 : Z) : bool :=
  let si := sx_si sx in
  match si_m1 si with
  | Some m1 =>
      let m2 := zlit64 z2 in
      if thr_test (se_thr e) k2 (Some m2) then true
      else if exists_sd fs fk b2 k2 m2 (se_dsel e) then true
      else if se_sh e then lin_apart0F fs fk (si_b1 si) (si_k1 si) m1 b2 k2 m2 else false
  | None => false    (* [comment removed for export] *)
  end.

Definition quick_apartX (fs : list sfact) (fk : list kentry) (sx : stctx) (e : sentryinfo)
           (b2 : expr) (k2 : Z) (n2 : expr) (h2 : option Z) : bool :=
  let si := sx_si sx in
  if thr_test (se_thr e) k2 h2 then true
  else
    let dxm := dxm_of fs fk sx in     (* [comment removed for export] *)
    if exists_xk fs fk b2 k2 n2 h2 (dselect false dxm (se_sds e)) then true
    else if se_sh e then
           if lin_ge0F fs fk [(b2, k2)] [(si_b1 si, si_k1 si); (si_n1 si, 0%Z)] then true
           else lin_ge0F fs fk [(si_b1 si, si_k1 si)] [(b2, k2); (n2, 0%Z)]
         else false.

Definition quick_keepL (fs : list sfact) (fk : list kentry) (sx : stctx) (e : sentryinfo) (K : kentry) : bool :=
  let wa := sx_wa sx in let k := a_off wa in let w := sx_w sx in
  match K with
  | KAlign _ _ | KRange _ _ _ | KWr _ _ | KDisj _ _ _ _ => true
  | KImg lo hi =>
      match a_base wa with
      | ELit 0 => if Z.ltb lo hi then (if Z.leb hi k then true else Z.leb (k + Z.of_nat w) lo) else false
      | _ => if Z.ltb (hi - lo) two64 then quick_apartL fs fk sx e (ELit 0) lo (hi - lo) else false
      end
  | KZero (SA kb kk) (ELit l0) =>
      if expr_eqb kb (a_base wa) then
        if zin64 l0 then if Z.ltb 0 l0 then (if Z.leb (kk + l0) k then true else Z.leb (k + Z.of_nat w) kk) else false else false
      else quick_apartL fs fk sx e kb kk l0
  | KWord (SA kb kk) w' v =>
      if expr_eqb kb (a_base wa) then (if Z.leb (kk + Z.of_nat w') k then true else Z.leb (k + Z.of_nat w) kk)
      else quick_apartL fs fk sx e kb kk (Z.of_nat w')
  | KBlob (SA kb kk) (ELit l0) bk =>
      if expr_eqb kb (a_base wa) then
        (let l := (l0 mod two64)%Z in if Z.leb (kk + l) k then true else Z.leb (k + Z.of_nat w) kk)
      else quick_apartL fs fk sx e kb kk l0
  | _ => false   (* [comment removed for export] *)
  end.

Definition quick_keepX (fs : list sfact) (fk : list kentry) (sx : stctx) (e : sentryinfo)
           (h2 : option Z) (K : kentry) : bool :=
  let wa := sx_wa sx in let k := a_off wa in let w := sx_w sx in
  match K with
  | KZero (SA kb kk) (ELit _) | KBlob (SA kb kk) (ELit _) _ => false   (* [comment removed for export] *)
  | KZero (SA kb kk) len =>
      if expr_eqb kb (a_base wa) then Z.leb (k + Z.of_nat w) kk
      else quick_apartX fs fk sx e kb kk len h2
  | KBlob (SA kb kk) len bk =>
      if expr_eqb kb (a_base wa) then Z.leb (k + Z.of_nat w) kk
      else quick_apartX fs fk sx e kb kk len h2
  | _ => false
  end.

(* [comment removed for export] *)
Definition klen_sym (K : kentry) : option expr :=
  match K with
  | KZero _ (ELit _) | KBlob _ (ELit _) _ => None
  | KZero _ n | KBlob _ n _ => Some n
  | _ => None
  end.

(* [comment removed for export] *)
Definition esum (K : kentry) : option (Z * Z) :=
  match K with
  | KWord (SA _ kk) w' _ => Some (kk, kk + Z.of_nat w')
  | KZero (SA _ kk) (ELit l0) => if zin64 l0 then if Z.ltb 0 l0 then Some (kk, kk + l0) else None else None
  | KBlob (SA _ kk) (ELit l0) _ => if zin64 l0 then Some (kk, kk + l0) else None
  | KImg lo hi => if Z.ltb lo hi then Some (lo, hi) else None
  | _ => None
  end.

(* [comment removed for export] *)
Fixpoint first_failL (fs : list sfact) (fk : list kentry) (useall : bool) (es : option (Z * Z))
         (sxs : list stctx) (ents : list colent) (K : kentry) : option (list stctx) :=
  match sxs, ents with
  | sx :: sr, c :: cr =>
      if (if useall then ce_all c else false) then first_failL fs fk useall es sr cr K
      else if (match ce_same c, es with
               | Some (k, kw), Some (lo, hi) => if Z.leb hi k then true else Z.leb kw lo
               | _, _ => quick_keepL fs fk sx (ce_sei c) K
               end)
           then first_failL fs fk useall es sr cr K
      else Some sxs
  | [], _ => None
  | _, [] => Some sxs
  end.

(* [comment removed for export] *)
Fixpoint first_failX (fs : list sfact) (fk : list kentry) (sxs : list stctx) (ents : list colent) (h2 : option Z) (K : kentry)
  : option (list stctx) :=
  match sxs, ents with
  | sx :: sr, c :: cr => if quick_keepX fs fk sx (ce_sei c) h2 K then first_failX fs fk sr cr h2 K else Some sxs
  | [], _ => None
  | _, [] => Some sxs
  end.

(* [comment removed for export] *)
Definition klitq (K : kentry) : option (Z * Z) :=
  match K with
  | KImg lo hi => if Z.ltb (hi - lo) two64 then Some (lo, hi - lo) else None
  | KZero (SA _ kk) (ELit l0) => Some (kk, l0)
  | KWord (SA _ kk) w' _ => Some (kk, Z.of_nat w')
  | KBlob (SA _ kk) (ELit l0) _ => Some (kk, l0)
  | _ => None
  end.
Fixpoint vlook (p : positive) (V : list (positive * bool)) : bool :=
  match V with [] => false | (q, b) :: r => if Pos.eqb q p then b else vlook p r end.
(* [comment removed for export] *)
Definition verdicts (fs : list sfact) (fk : list kentry) (l : list (positive * csum)) (useall : bool) (b2 : expr) (K : kentry) : list (positive * bool) :=
  match klitq K with
  | Some (k2, z2) => let h := zlit64 z2 in map (fun ps => (fst ps, fc_test fs fk (if useall then cs_N (snd ps) else cs_A (snd ps)) b2 k2 h)) l
  | None => []
  end.
(* [comment removed for export] *)
Fixpoint first_failH (fs : list sfact) (fk : list kentry) (V : list (positive * bool)) (useall : bool) (es : option (Z * Z))
         (sxs : list stctx) (ents : list colent) (cids : list positive) (K : kentry) : option (list stctx) :=
  match sxs, ents with
  | sx :: sr, c :: cr =>
      let ir := match cids with _ :: r => r | [] => [] end in
      if (if useall then ce_all c else false) then first_failH fs fk V useall es sr cr ir K
      else if (match ce_same c, es with
               | Some (k, kw), Some (lo, hi) => if Z.leb hi k then true else Z.leb kw lo
               | None, _ => if (match cids with cid :: _ => vlook cid V | [] => false end) then true
                            else quick_keepL fs fk sx (ce_sei c) K
               | _, _ => quick_keepL fs fk sx (ce_sei c) K
               end)
           then first_failH fs fk V useall es sr cr ir K
      else Some sxs
  | [], _ => None
  | _, [] => Some sxs
  end.
Definition kdead (sx : stctx) (K : kentry) : bool :=
  match K with
  | KWord (SA kb kk) w' _ =>
      if expr_eqb kb (a_base (sx_wa sx))
      then negb (Z.leb (kk + Z.of_nat w') (a_off (sx_wa sx)) || Z.leb (a_off (sx_wa sx) + Z.of_nat (sx_w sx)) kk)%bool
      else false
  | _ => false
  end.

(* [comment removed for export] *)
Definition emask_of (fs : list sfact) (fk : list kentry) (b2 : expr) (k2 : Z) (n2 : expr) (h2 : option Z) (sds : list (sdesc * sdesc)) : list (bool * bool) :=
  map (fun p => (xk_eval fs fk b2 (fst p) k2 n2 h2, xk_eval fs fk b2 (snd p) k2 n2 h2)) sds.
Fixpoint exists_xk2 (fs : list sfact) (fk : list kentry) (b1 : expr) (k1 : Z) (n1 : expr) (h1 : option Z)
         (em : list (bool * bool)) (sds1 : list (sdesc * sdesc)) : bool :=
  match em, sds1 with
  | (e1, e2) :: er, (d1, d2) :: dr =>
      if (if e2 then xk_eval fs fk b1 d1 k1 n1 h1 else false) then true
      else if (if e1 then xk_eval fs fk b1 d2 k1 n1 h1 else false) then true
      else exists_xk2 fs fk b1 k1 n1 h1 er dr
  | _, _ => false
  end.
Definition quick_apartX2 (fs : list sfact) (fk : list kentry) (sx : stctx) (e : sentryinfo) (em : list (bool * bool))
           (b2 : expr) (k2 : Z) (n2 : expr) (h2 : option Z) : bool :=
  let si := sx_si sx in
  if thr_test (se_thr e) k2 h2 then true
  else if exists_xk2 fs fk (si_b1 si) (si_k1 si) (si_n1 si) (si_h1 si) em (si_sds1 si) then true
  else if se_sh e then
         if lin_ge0F fs fk [(b2, k2)] [(si_b1 si, si_k1 si); (si_n1 si, 0%Z)] then true
         else lin_ge0F fs fk [(si_b1 si, si_k1 si)] [(b2, k2); (n2, 0%Z)]
       else false.
Definition quick_keepX2 (fs : list sfact) (fk : list kentry) (sx : stctx) (e : sentryinfo) (em : list (bool * bool))
           (h2 : option Z) (K : kentry) : bool :=
  let wa := sx_wa sx in let k := a_off wa in let w := sx_w sx in
  match K with
  | KZero (SA kb kk) (ELit _) | KBlob (SA kb kk) (ELit _) _ => false
  | KZero (SA kb kk) len =>
      if expr_eqb kb (a_base wa) then Z.leb (k + Z.of_nat w) kk
      else quick_apartX2 fs fk sx e em kb kk len h2
  | KBlob (SA kb kk) len bk =>
      if expr_eqb kb (a_base wa) then Z.leb (k + Z.of_nat w) kk
      else quick_apartX2 fs fk sx e em kb kk len h2
  | _ => false
  end.
Fixpoint first_failX2 (fs : list sfact) (fk : list kentry) (sxs : list stctx) (ents : list colent) (em : list (bool * bool))
         (h2 : option Z) (K : kentry) : option (list stctx) :=
  match sxs, ents with
  | sx :: sr, c :: cr => if quick_keepX2 fs fk sx (ce_sei c) em h2 K then first_failX2 fs fk sr cr em h2 K else Some sxs
  | [], _ => None
  | _, [] => Some sxs
  end.
Definition kx_off (K : kentry) : Z := match K with KZero (SA _ kk) _ | KBlob (SA _ kk) _ _ => kk | _ => 0%Z end.

(* [comment removed for export] *)
Fixpoint pieces_through (fk : list kentry) (cc : ccache) (sxs : list stctx) (ps : list kentry) : list kentry :=
  match sxs with
  | [] => ps
  | sx :: sr =>
      let '(r, _, _) := prunef fk (sx_si sx) (sx_wa sx) (sx_w sx) (sx_wv sx) ps [] cc (ST [] None) in
      let '(ps', _, _) := r in
      pieces_through fk cc sr ps'
  end.

(* [comment removed for export] *)
Record vtables : Type := VT {
  vt_fk : list kentry; vt_cc : ccache;
  vt_sxs : list stctx;                          (* [comment removed for export] *)
  vt_gb : list (expr * Z * Z);                  (* [comment removed for export] *)
  vt_cols : list (expr * column) }.             (* [comment removed for export] *)

Definition vt_col (vt : vtables) (b2 : expr) : column * vtables :=
  match alookup (vt_cols vt) b2 with
  | Some col => (col, vt)
  | None =>
      let '(ci2, cc) := cc_get (vt_fk vt) (vt_cc vt) b2 in
      let col := column_of (vt_sxs vt) b2 ci2 (group_bounds (vt_gb vt) b2) in
      (col, VT (vt_fk vt) cc (vt_sxs vt) (vt_gb vt) ((b2, col) :: vt_cols vt))
  end.

Definition kkey (K : kentry) : option expr :=
  match K with
  | KZero (SA kb _) _ | KWord (SA kb _) _ _ | KBlob (SA kb _) _ _ => Some kb
  | KImg _ _ => Some (ELit 0)
  | _ => None
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition in_group (col : column) (K : kentry) : bool :=
  match co_gb col, klit K with
  | Some (gl, gh), Some (_, lo, hi) => if Z.leb gl lo then Z.leb hi gh else false
  | _, _ => false
  end.

Definition entryV (vt : vtables) (orig : bool) (i : nat) (b2 : expr) (K : kentry) : list kentry * vtables :=
  let '(col, vt) := vt_col vt b2 in
  let sxs := skipn i (vt_sxs vt) in
  let ents := skipn i (co_ents col) in
  match klen_sym K with
  | None =>
      let useall := if orig then in_group col K else false in
      if (if useall then match i with O => co_all col | S _ => false end else false) then ([K], vt)
      else let V := verdicts (cc_fs (vt_cc vt)) (vt_fk vt) (hd [] (skipn i (co_sums col))) useall b2 K in   (* [comment removed for export] *)
           match first_failH (cc_fs (vt_cc vt)) (vt_fk vt) V useall (esum K) sxs ents (skipn i (co_cids col)) K with
           | None => ([K], vt)
           | Some sfx => ((match sfx with
                           | sx :: _ => if kdead sx K then [] else pieces_through (vt_fk vt) (vt_cc vt) sfx [K]
                           | [] => [K]
                           end), vt)
           end
  | Some n =>
      let '(h2, cc) := xh_get (vt_fk vt) (vt_cc vt) n in
      let vt := VT (vt_fk vt) cc (vt_sxs vt) (vt_gb vt) (vt_cols vt) in
      let em := emask_of (cc_fs cc) (vt_fk vt) b2 (kx_off K) n h2 (co_sds col) in                          (* [comment removed for export] *)
      match first_failX2 (cc_fs cc) (vt_fk vt) sxs ents em h2 K with
      | None => ([K], vt)
      | Some sfx => (pieces_through (vt_fk vt) cc sfx [K], vt)
      end
  end.

Definition chainV (vt : vtables) (K : kentry) : list kentry * vtables :=
  match kkey K with
  | None => ([K], vt)      (* [comment removed for export] *)
  | Some b2 => entryV vt true O b2 K
  end.

Fixpoint chainsV (vt : vtables) (kn : list kentry) : list kentry :=
  match kn with
  | [] => []
  | K :: rest => let '(ps, vt) := chainV vt K in ps ++ chainsV vt rest
  end.

(* [comment removed for export] *)
Fixpoint stores_partV (vt : vtables) (i : nat) (sfx : list stctx) : list kentry * vtables :=
  match sfx with
  | [] => ([], vt)
  | sx :: newer =>
      let '(r_newer, vt) := stores_partV vt (S i) newer in
      let K := KWord (sx_wa sx) (sx_w sx) (sx_wv sx) in
      let '(r_i, vt) := entryV vt false i (a_base (sx_wa sx)) K in
      (r_newer ++ r_i, vt)
  end.

Definition carryV (log : list sentry) (kn : list kentry) : list kentry :=
  let fk := facts_of kn in
  let fs := SFS fk in
  let cc0 := CC (kdisj_sdis fs fk fk) fs [] [] in
  let '(sxs, cc) := stctxs_of fk cc0 log in
  let vt := VT fk cc sxs (bounds_acc kn None []) [] in
  let '(sp, vt) := stores_partV vt 1%nat sxs in
  sp ++ chainsV vt kn.

Definition carry (log : list sentry) (kn : list kentry) (hints : list bool)
  : list kentry * list sidecond * list bool :=
  match log, hints with
  | [], _ => (kn, [], hints)
  | _, [] => (carryV log kn, [], [])
  | _, _ => carry_p5 log kn hints
  end.

(* [comment removed for export] *)
Lemma p5_aluop_eqb_eq : forall a b, aluop_eqb a b = true -> a = b.
Proof. intros [] []; cbn; intros; try reflexivity; discriminate. Qed.
Lemma p5_mulop_eqb_eq : forall a b, mulop_eqb a b = true -> a = b.
Proof. intros [] []; cbn; intros; try reflexivity; discriminate. Qed.
Lemma p5_expr_eqb_eq : forall x y, expr_eqb x y = true -> x = y.
Proof.
  induction x; destruct y; cbn; intros H; try discriminate;
    repeat match goal with
      | H : (_ && _)%bool = true |- _ => apply andb_prop in H; destruct H
      end;
    repeat match goal with
      | H : Z.eqb _ _ = true |- _ => apply Z.eqb_eq in H
      | H : Nat.eqb _ _ = true |- _ => apply Nat.eqb_eq in H
      | H : Bool.eqb _ _ = true |- _ => apply Bool.eqb_prop in H
      | H : aluop_eqb _ _ = true |- _ => apply p5_aluop_eqb_eq in H
      | H : mulop_eqb _ _ = true |- _ => apply p5_mulop_eqb_eq in H
      | H : expr_eqb ?a _ = true, IH : forall y, expr_eqb ?a y = true -> _ |- _ => apply IH in H
      end; subst; reflexivity.
Qed.
Lemma p5_in_sides_eq : forall allkn kn b1 k1 n1 b2 k2 n2,
  in_sides allkn (disj_sides allkn kn b1 k1 n1) b2 k2 n2 = kdisj_apart allkn kn b1 k1 n1 b2 k2 n2.
Proof.
  intros allkn kn b1 k1 n1 b2 k2 n2. induction kn as [|K rest IH]; [reflexivity|].
  destruct K as [| | | | | | |c1 m1 c2 m2]; cbn [disj_sides kdisj_apart]; try exact IH.
  destruct (sub_itv allkn b1 k1 n1 c1 m1), (sub_itv allkn b1 k1 n1 c2 m2); cbn [in_sides];
    destruct (sub_itv allkn b2 k2 n2 c2 m2) eqn:E2, (sub_itv allkn b2 k2 n2 c1 m1) eqn:E1;
    rewrite ?E1, ?E2, ?IH; reflexivity.
Qed.
Lemma p5_in_sides_x_eq : forall allkn kn b1 k1 n1 b2 k2 n2,
  in_sides_x allkn (disj_sides_x allkn kn b1 k1 n1) b2 k2 n2 = kdisj_apart_x allkn kn b1 k1 n1 b2 k2 n2.
Proof.
  intros allkn kn b1 k1 n1 b2 k2 n2. induction kn as [|K rest IH]; [reflexivity|].
  destruct K as [| | | | | | |c1 m1 c2 m2]; cbn [disj_sides_x kdisj_apart_x]; try exact IH.
  destruct (sub_itv_x allkn b1 k1 n1 c1 m1), (sub_itv_x allkn b1 k1 n1 c2 m2); cbn [in_sides_x];
    destruct (sub_itv_x allkn b2 k2 n2 c2 m2) eqn:E2, (sub_itv_x allkn b2 k2 n2 c1 m1) eqn:E1;
    rewrite ?E1, ?E2, ?IH; reflexivity.
Qed.
Lemma p5_ranges_apart_p_eq : forall kn b1 k1 n1 b2 k2 n2,
  ranges_apart_p kn (mk_sprep kn b1 k1 n1) b1 k1 n1 b2 k2 n2 = ranges_apart_x kn b1 k1 n1 b2 k2 n2.
Proof.
  intros kn b1 k1 n1 b2 k2 n2. unfold ranges_apart_p, ranges_apart_x, mk_sprep. cbn [sp_rng sp_h1 sp_D sp_Dx].
  destruct n1; try (rewrite p5_in_sides_x_eq; reflexivity).
  destruct n2; try (rewrite p5_in_sides_x_eq; reflexivity).
  unfold ranges_apart. rewrite p5_in_sides_eq. reflexivity.
Qed.
Lemma p5_prune1p_eq : forall allkn wa w wv K hints,
  prune1p allkn (mk_sprep allkn (a_base wa) (a_off wa) (elen w)) wa w wv K hints = prune1 allkn wa w wv K hints.
Proof.
  intros allkn wa w wv K hints. unfold prune1p, prune1.
  destruct K as [[kb kk] w' v|[kb kk] len|[kb kk] len bk|lo hi|e' m'|e' lo' hi'|[eb ek] en|c1 m1 c2 m2];
    rewrite ?p5_ranges_apart_p_eq; reflexivity.
Qed.
Lemma p5_prunep_eq : forall allkn wa w wv kn hints,
  prunep allkn (mk_sprep allkn (a_base wa) (a_off wa) (elen w)) wa w wv kn hints = prune allkn wa w wv kn hints.
Proof.
  intros allkn wa w wv kn. induction kn as [|K rest IH]; intros hints; [reflexivity|].
  cbn [prunep prune]. rewrite p5_prune1p_eq. destruct (prune1 allkn wa w wv K hints) as [[kept scs1] hs1].
  rewrite IH. reflexivity.
Qed.
Lemma p5_ranges_apart_pc_eq : forall kn sp b1 k1 n1 b2 k2 n2,
  ranges_apart_pc kn sp b1 k1 n1 (base_range kn b2) b2 k2 n2 = ranges_apart_p kn sp b1 k1 n1 b2 k2 n2.
Proof. intros. reflexivity. Qed.
Lemma p5_prune1pc_eq : forall allkn sp wa w wv K hints br2,
  match kbase K with Some kb => br2 = base_range allkn kb | None => True end ->
  prune1pc allkn sp wa w wv K hints br2 = prune1p allkn sp wa w wv K hints.
Proof.
  intros allkn sp wa w wv K hints br2 Hb.
  destruct K as [[kb kk] w' v|[kb kk] len|[kb kk] len bk|lo hi|e' m'|e' lo' hi'|[eb ek] en|c1 m1 c2 m2];
    cbn [kbase] in Hb; try reflexivity; subst br2; unfold prune1pc, prune1p; rewrite ?p5_ranges_apart_pc_eq;
    destruct (expr_eqb kb (a_base wa)); reflexivity.
Qed.
Definition p5_br_cache_ok (allkn : list kentry) (c : list (expr * option (Z * Z))) : Prop :=
  Forall (fun p => snd p = base_range allkn (fst p)) c.
Lemma p5_br_lookup_ok : forall allkn c b r, p5_br_cache_ok allkn c -> br_lookup c b = Some r -> r = base_range allkn b.
Proof.
  intros allkn c b r Hc. induction c as [|[b' r'] rest IH]; cbn; [discriminate|].
  apply Forall_cons_iff in Hc as [H1 Hc]. cbn in H1.
  destruct (expr_eqb b b') eqn:E.
  - intros H. injection H as <-. apply p5_expr_eqb_eq in E. subst b'. exact H1.
  - apply IH. exact Hc.
Qed.
Lemma p5_prunepc_eq : forall allkn sp wa w wv kn hints cache,
  p5_br_cache_ok allkn cache ->
  prunepc allkn sp wa w wv kn hints cache = prunep allkn sp wa w wv kn hints.
Proof.
  intros allkn sp wa w wv kn. induction kn as [|K rest IH]; intros hints cache Hc; [reflexivity|].
  cbn [prunepc prunep].
  destruct (kbase K) as [kb|] eqn:HK.
  - destruct (br_lookup cache kb) as [r|] eqn:HL.
    + rewrite (p5_prune1pc_eq allkn sp wa w wv K hints r) by (rewrite HK; exact (p5_br_lookup_ok _ _ _ _ Hc HL)).
      destruct (prune1p allkn sp wa w wv K hints) as [[kept scs1] hs1]. rewrite (IH hs1 cache Hc). reflexivity.
    + rewrite (p5_prune1pc_eq allkn sp wa w wv K hints (base_range allkn kb)) by (rewrite HK; reflexivity).
      destruct (prune1p allkn sp wa w wv K hints) as [[kept scs1] hs1].
      rewrite (IH hs1 ((kb, base_range allkn kb) :: cache)) by (constructor; [reflexivity | exact Hc]). reflexivity.
  - rewrite (p5_prune1pc_eq allkn sp wa w wv K hints None) by (rewrite HK; exact I).
    destruct (prune1p allkn sp wa w wv K hints) as [[kept scs1] hs1]. rewrite (IH hs1 cache Hc). reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma leb_iff_eq : forall a b c d, (a <= b <-> c <= d) -> Z.leb a b = Z.leb c d.
Proof.
  intros a b c d H. destruct (Z.leb_spec0 a b), (Z.leb_spec0 c d); try reflexivity; exfalso; tauto.
Qed.

Lemma zlit64_small : forall n, Z.leb 0 n = true -> Z.ltb n two64 = true -> zlit64 n = n.
Proof.
  intros n H1 H2. unfold zlit64. rewrite H1, H2. reflexivity.
Qed.

Lemma xhi_lit : forall fk z, xhi fk (ELit z) = Some (zlit64 z).
Proof. reflexivity. Qed.

Lemma xk_eval_eq : forall fk b br c m k n h,
  br = base_range fk b -> h = xhi fk n ->
  xk_eval (SFS fk) fk b (mk_sd (SFS fk) fk b br c m) k n h = xinside fk b k n (a_base c) (a_off c) m.
Proof.
  intros fk b br [cb ck] m k n h -> ->. unfold xk_eval, mk_sd, xinside. cbn [a_base a_off sd_kind sd_c sd_m].
  rewrite !xloF_eq, !xhiF_eq.
  destruct (shares_var b cb); [rewrite xinside0F_eq; reflexivity|].
  destruct (novars cb); [|reflexivity].
  unfold xinside_num.
  destruct (xlo fk cb) as [lo2|]; [|reflexivity].
  destruct (xhi fk cb) as [hi2|]; [|reflexivity].
  destruct (Z.eqb lo2 hi2); [|reflexivity].
  destruct (base_range fk b) as [[lo1 hi1]|]; [|reflexivity].
  destruct (xhi fk n) as [hv|]; destruct (xlo fk m) as [l2|]; try reflexivity.
  f_equal; apply leb_iff_eq; lia.
Qed.

Lemma sd_eval_eq : forall fk b br c m k n,
  br = base_range fk b ->
  sd_eval (SFS fk) fk b (mk_sd (SFS fk) fk b br c m) k n = sub_itv fk b k n c m.
Proof.
  intros fk b br c m k n Hbr. unfold sd_eval, sub_itv.
  replace (sd_same (mk_sd (SFS fk) fk b br c m)) with (expr_eqb b (a_base c)) by reflexivity.
  replace (sd_c (mk_sd (SFS fk) fk b br c m)) with c by reflexivity.
  replace (sd_lim (mk_sd (SFS fk) fk b br c m))
    with (if expr_eqb b (a_base c) then match xlo fk m with Some ml => Some (a_off c + ml) | None => None end else None)
    by (cbn [sd_lim mk_sd]; rewrite xloF_eq; reflexivity).
  assert (SLOW : (if (if Z.leb 0 n then Z.ltb n two64 else false) then xk_eval (SFS fk) fk b (mk_sd (SFS fk) fk b br c m) k (ELit n) (Some n) else false)
                 = (if (Z.leb 0 n && Z.ltb n two64)%bool then xinside fk b k (ELit n) (a_base c) (a_off c) m else false)).
  { destruct (Z.leb 0 n) eqn:G1; destruct (Z.ltb n two64) eqn:G2; cbn [andb]; try reflexivity.
    apply xk_eval_eq; [exact Hbr|]. rewrite xhi_lit, (zlit64_small n G1 G2). reflexivity. }
  rewrite SLOW.
  destruct (expr_eqb b (a_base c)); cbn [andb]; [|reflexivity].
  destruct (Z.leb (a_off c) k); [|reflexivity].
  destruct (xlo fk m) as [ml|]; reflexivity.
Qed.

Lemma sd_useless_false : forall fs fk b d k n, sd_useless d = true -> sd_eval fs fk b d k n = false.
Proof.
  intros fs fk b d k n H. unfold sd_useless in H. unfold sd_eval, xk_eval.
  destruct (sd_same d); [discriminate|].
  destruct (sd_kind d); try discriminate.
  destruct (if Z.leb 0 n then Z.ltb n two64 else false); reflexivity.
Qed.

(* [comment removed for export] *)
Definition sds_of (fk : list kentry) (kn : list kentry) (b : expr) : list (sdesc * sdesc) :=
  ci_sds (mk_ci (SFS fk) fk (kdisj_sides kn) b).

Lemma sds_of_cons_disj : forall fk c1 m1 c2 m2 rest b,
  sds_of fk (KDisj c1 m1 c2 m2 :: rest) b =
  (mk_sd (SFS fk) fk b (base_range fk b) c1 m1, mk_sd (SFS fk) fk b (base_range fk b) c2 m2) :: sds_of fk rest b.
Proof. reflexivity. Qed.

Lemma exists_sd_cons_opt : forall fk b2 k2 n2 drop c m L,
  exists_sd (SFS fk) fk b2 k2 n2 (if (drop && sd_useless (mk_sd (SFS fk) fk b2 (base_range fk b2) c m))%bool then L
                         else mk_sd (SFS fk) fk b2 (base_range fk b2) c m :: L)
  = (if sub_itv fk b2 k2 n2 c m then true else exists_sd (SFS fk) fk b2 k2 n2 L).
Proof.
  intros fk b2 k2 n2 drop c m L.
  destruct drop; cbn [andb].
  - destruct (sd_useless (mk_sd (SFS fk) fk b2 (base_range fk b2) c m)) eqn:U.
    + pose proof (sd_useless_false (SFS fk) fk b2 _ k2 n2 U) as F. rewrite sd_eval_eq in F by reflexivity.
      rewrite F. reflexivity.
    + cbn [exists_sd]. rewrite sd_eval_eq by reflexivity. reflexivity.
  - cbn [exists_sd]. rewrite sd_eval_eq by reflexivity. reflexivity.
Qed.

Lemma exists_sd_dselect_eq : forall fk kn b1 k1 m1 b2 k2 n2 drop,
  exists_sd (SFS fk) fk b2 k2 n2 (dselect drop (dmask_of (SFS fk) fk b1 k1 m1 (sds_of fk kn b1)) (sds_of fk kn b2))
  = in_sides fk (disj_sides fk kn b1 k1 m1) b2 k2 n2.
Proof.
  intros fk kn b1 k1 m1 b2 k2 n2 drop. induction kn as [|K rest IH]; [reflexivity|].
  destruct K as [| | | | | | |c1 m1' c2 m2]; try exact IH.
  rewrite !sds_of_cons_disj. cbn [dmask_of map fst snd dselect disj_sides].
  fold (dmask_of (SFS fk) fk b1 k1 m1 (sds_of fk rest b1)).
  rewrite !sd_eval_eq by reflexivity.
  destruct (sub_itv fk b1 k1 m1 c1 m1'), (sub_itv fk b1 k1 m1 c2 m2); cbn [in_sides];
    rewrite ?exists_sd_cons_opt, IH; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma exists_xk_cons : forall fk b2 k2 n2 h2 c m L,
  h2 = xhi fk n2 ->
  exists_xk (SFS fk) fk b2 k2 n2 h2 (mk_sd (SFS fk) fk b2 (base_range fk b2) c m :: L)
  = (if sub_itv_x fk b2 k2 n2 c m then true else exists_xk (SFS fk) fk b2 k2 n2 h2 L).
Proof.
  intros fk b2 k2 n2 h2 c m L Hh. cbn [exists_xk]. unfold sub_itv_x. rewrite xk_eval_eq by (reflexivity || exact Hh). reflexivity.
Qed.

Lemma exists_xk_dselect_eq : forall fk kn b1 k1 n1 h1 b2 k2 n2 h2,
  h1 = xhi fk n1 -> h2 = xhi fk n2 ->
  exists_xk (SFS fk) fk b2 k2 n2 h2 (dselect false (dxmask_of (SFS fk) fk b1 k1 n1 h1 (sds_of fk kn b1)) (sds_of fk kn b2))
  = in_sides_x fk (disj_sides_x fk kn b1 k1 n1) b2 k2 n2.
Proof.
  intros fk kn b1 k1 n1 h1 b2 k2 n2 h2 H1 H2. induction kn as [|K rest IH]; [reflexivity|].
  destruct K as [| | | | | | |c1 m1' c2 m2]; try exact IH.
  rewrite !sds_of_cons_disj. cbn [dxmask_of map fst snd dselect disj_sides_x andb].
  fold (dxmask_of (SFS fk) fk b1 k1 n1 h1 (sds_of fk rest b1)).
  rewrite !xk_eval_eq by (reflexivity || assumption).
  change (sub_itv_x fk b1 k1 n1 c1 m1') with (xinside fk b1 k1 n1 (a_base c1) (a_off c1) m1').
  change (sub_itv_x fk b1 k1 n1 c2 m2) with (xinside fk b1 k1 n1 (a_base c2) (a_off c2) m2).
  destruct (xinside fk b1 k1 n1 (a_base c1) (a_off c1) m1'), (xinside fk b1 k1 n1 (a_base c2) (a_off c2) m2); cbn [in_sides_x];
    rewrite ?exists_xk_cons, IH by (reflexivity || assumption); reflexivity.
Qed.

(* [comment removed for export] *)
Lemma thr_test_eq : forall br1 br2 k1 m1 h1 k2 h2 b1 n1 sds1 dm,
  thr_test (mk_thr (SI b1 k1 n1 m1 h1 br1 sds1 dm) br2) k2 h2
  = match br1, br2, h1, h2 with
    | Some (lo1, hi1), Some (lo2, hi2), Some m, Some h => (Z.leb (hi1 + k1 + m) (lo2 + k2) || Z.leb (hi2 + k2 + h) (lo1 + k1))%bool
    | _, _, _, _ => false
    end.
Proof.
  intros. unfold thr_test, mk_thr. cbn [si_br1 si_k1 si_h1].
  destruct br1 as [[lo1 hi1]|], br2 as [[lo2 hi2]|], h1 as [m|], h2 as [h|]; try reflexivity.
  rewrite (leb_iff_eq (hi1 + k1 + m - lo2) k2 (hi1 + k1 + m) (lo2 + k2)) by lia.
  rewrite (leb_iff_eq (k2 + h) (lo1 + k1 - hi2) (hi2 + k2 + h) (lo1 + k1)) by lia.
  destruct (Z.leb (hi1 + k1 + m) (lo2 + k2)); reflexivity.
Qed.

(* [comment removed for export] *)

Lemma mk_sd'_eq : forall fs fk b br c m, mk_sd' fs fk b br (mk_sdi fs fk c m) = mk_sd fs fk b br c m.
Proof.
  intros. unfold mk_sd', mk_sdi, mk_sd. cbn [sdi_c sdi_m sdi_xlom sdi_nov sdi_pt].
  destruct (novars (a_base c)); [|reflexivity].
  destruct (xloF fs fk (a_base c)), (xhiF fs fk (a_base c)); try reflexivity.
  destruct (Z.eqb _ _); reflexivity.
Qed.

Lemma mk_ci'_eq : forall fs fk kn b, mk_ci' fs fk (kdisj_sdis fs fk kn) b = mk_ci fs fk (kdisj_sides kn) b.
Proof.
  intros. unfold mk_ci', mk_ci. f_equal. induction kn as [|K r IH]; [reflexivity|].
  destruct K; cbn [kdisj_sdis kdisj_sides map]; try exact IH. cbn [fst snd]. rewrite !mk_sd'_eq, IH. reflexivity.
Qed.

Definition pcc_ok (fk : list kentry) (cc : ccache) : Prop :=
  (cc_tbl cc = kdisj_sdis (SFS fk) fk fk /\ cc_fs cc = SFS fk)
  /\ (forall b ci, alookup (cc_bases cc) b = Some ci -> ci = mk_ci (SFS fk) fk (kdisj_sides fk) b)
  /\ (forall n h, alookup (cc_xh cc) n = Some h -> h = xhi fk n).

Definition si_of (fk : list kentry) (b1 : expr) (k1 : Z) (n1 : expr) : sinfo :=
  mk_si (SFS fk) fk b1 k1 n1 (mk_ci (SFS fk) fk (kdisj_sides fk) b1).

Definition pst_ok (fk : list kentry) (si : sinfo) (st : scache) : Prop :=
  (forall b e, alookup (st_bs st) b = Some e -> e = mk_sei si b (mk_ci (SFS fk) fk (kdisj_sides fk) b))
  /\ (forall m, st_dx st = Some m -> m = dxmask_of (SFS fk) fk (si_b1 si) (si_k1 si) (si_n1 si) (si_h1 si) (si_sds1 si)).

Lemma alookup_cons : forall (A : Type) (l : list (expr * A)) k v b,
  alookup ((k, v) :: l) b = if expr_eqb b k then Some v else alookup l b.
Proof. reflexivity. Qed.

Lemma cc_get_ok : forall fk cc b,
  pcc_ok fk cc ->
  fst (cc_get fk cc b) = mk_ci (SFS fk) fk (kdisj_sides fk) b /\ pcc_ok fk (snd (cc_get fk cc b)).
Proof.
  intros fk cc b ([Ht Hf] & Hb & Hx). unfold cc_get.
  destruct (alookup (cc_bases cc) b) as [ci|] eqn:L.
  - split; [exact (Hb _ _ L) | exact (conj (conj Ht Hf) (conj Hb Hx))].
  - cbn [fst snd]. rewrite Ht, Hf. split; [apply mk_ci'_eq|]. split; [split; reflexivity|]. split; [|exact Hx].
    cbn [cc_bases]. intros b' ci'. rewrite alookup_cons.
    destruct (expr_eqb b' b) eqn:E.
    + intros H. injection H as <-. apply p5_expr_eqb_eq in E. subst b'. apply mk_ci'_eq.
    + apply Hb.
Qed.

Lemma xh_get_ok : forall fk cc n,
  pcc_ok fk cc ->
  fst (xh_get fk cc n) = xhi fk n /\ pcc_ok fk (snd (xh_get fk cc n)).
Proof.
  intros fk cc n ([Ht Hf] & Hb & Hx). unfold xh_get.
  destruct (alookup (cc_xh cc) n) as [h|] eqn:L.
  - split; [exact (Hx _ _ L) | exact (conj (conj Ht Hf) (conj Hb Hx))].
  - cbn [fst snd]. split; [rewrite Hf; apply xhiF_eq|]. split; [split; [exact Ht|exact Hf]|]. split; [exact Hb|].
    cbn [cc_xh]. intros n' h'. rewrite alookup_cons.
    destruct (expr_eqb n' n) eqn:E.
    + intros H. injection H as <-. apply p5_expr_eqb_eq in E. subst n'. rewrite Hf. apply xhiF_eq.
    + apply Hx.
Qed.

Lemma st_get_ok : forall fk si cc st b2,
  pcc_ok fk cc -> pst_ok fk si st ->
  let '(e, cc', st') := st_get fk si cc st b2 in
  e = mk_sei si b2 (mk_ci (SFS fk) fk (kdisj_sides fk) b2) /\ pcc_ok fk cc' /\ pst_ok fk si st'.
Proof.
  intros fk si cc st b2 Hcc (Hs & Hd). unfold st_get.
  destruct (alookup (st_bs st) b2) as [e|] eqn:L.
  - split; [exact (Hs _ _ L)|]. split; [exact Hcc |].
    assert (Hs2 : forall l, (forall b0 e0, alookup l b0 = Some e0 -> e0 = mk_sei si b0 (mk_ci (SFS fk) fk (kdisj_sides fk) b0)) ->
                  pst_ok fk si (ST ((b2, e) :: l) (st_dx st))).
    { intros l Hl. split; [|exact Hd]. cbn [st_bs]. intros b0 e0. rewrite alookup_cons.
      destruct (expr_eqb b0 b2) eqn:E.
      + intros H. injection H as <-. apply p5_expr_eqb_eq in E. subst b0. exact (Hs _ _ L).
      + apply Hl. }
    destruct (st_bs st) as [|[b' e'] rest] eqn:EB.
    + split; [intros b0 e0; rewrite EB; apply Hs | exact Hd].
    + destruct (expr_eqb b2 b').
      * split; [intros b0 e0; rewrite EB; apply Hs | exact Hd].
      * apply Hs2. intros b0 e0. apply Hs.
  - destruct (cc_get fk cc b2) as [ci2 cc'] eqn:G.
    pose proof (cc_get_ok fk cc b2 Hcc) as [H1 H2]. rewrite G in H1, H2. cbn [fst snd] in H1, H2. subst ci2.
    split; [reflexivity|]. split; [exact H2|]. split; [|exact Hd].
    cbn [st_bs]. intros b' e'. rewrite alookup_cons.
    destruct (expr_eqb b' b2) eqn:E.
    + intros H. injection H as <-. apply p5_expr_eqb_eq in E. subst b'. reflexivity.
    + apply Hs.
Qed.

Lemma dx_get_ok : forall fk si st,
  pst_ok fk si st ->
  fst (dx_get (SFS fk) fk si st) = dxmask_of (SFS fk) fk (si_b1 si) (si_k1 si) (si_n1 si) (si_h1 si) (si_sds1 si)
  /\ pst_ok fk si (snd (dx_get (SFS fk) fk si st)).
Proof.
  intros fk si st [Hs Hd]. unfold dx_get.
  destruct (st_dx st) as [m|] eqn:L; cbn [fst snd].
  - split; [apply Hd; reflexivity|]. split; [exact Hs|]. intros m' H'. rewrite L in H'. injection H' as <-. apply Hd. reflexivity.
  - split; [reflexivity|]. split; [exact Hs|]. cbn [st_dx]. intros m' H. injection H as <-. reflexivity.
Qed.

Lemma lin_apart_unfold : forall kn b1 k1 n1 b2 k2 n2,
  lin_apart kn b1 k1 n1 b2 k2 n2 = if shares_var b1 b2 then lin_apart0 kn b1 k1 n1 b2 k2 n2 else false.
Proof. reflexivity. Qed.

Lemma sei_thr_eq : forall fk b1 k1 n1 b2 k2 h,
  thr_test (se_thr (mk_sei (si_of fk b1 k1 n1) b2 (mk_ci (SFS fk) fk (kdisj_sides fk) b2))) k2 h
  = match base_range fk b1, base_range fk b2, xhi fk n1, h with
    | Some (lo1, hi1), Some (lo2, hi2), Some h1, Some hv =>
        (Z.leb (hi1 + k1 + h1) (lo2 + k2) || Z.leb (hi2 + k2 + hv) (lo1 + k1))%bool
    | _, _, _, _ => false
    end.
Proof.
  intros. unfold si_of, mk_si, mk_sei. cbn [se_thr ci_br mk_ci]. rewrite thr_test_eq, xhiF_eq. reflexivity.
Qed.

Lemma sei_dsel_eq : forall fk b1 k1 z1 b2 k2 m2,
  exists_sd (SFS fk) fk b2 k2 m2 (se_dsel (mk_sei (si_of fk b1 k1 (ELit z1)) b2 (mk_ci (SFS fk) fk (kdisj_sides fk) b2)))
  = kdisj_apart fk fk b1 k1 (zlit64 z1) b2 k2 m2.
Proof.
  intros. unfold si_of, mk_si, mk_sei. cbn [se_dsel si_dmask lit_of_len].
  change (ci_sds (mk_ci (SFS fk) fk (kdisj_sides fk) ?b)) with (sds_of fk fk b).
  rewrite exists_sd_dselect_eq. apply p5_in_sides_eq.
Qed.

Lemma sei_sh_eq : forall fk b1 k1 n1 b2,
  se_sh (mk_sei (si_of fk b1 k1 n1) b2 (mk_ci (SFS fk) fk (kdisj_sides fk) b2)) = shares_var b1 b2.
Proof. reflexivity. Qed.

Lemma sei_sds_eq : forall fk b1 k1 n1 b2,
  se_sds (mk_sei (si_of fk b1 k1 n1) b2 (mk_ci (SFS fk) fk (kdisj_sides fk) b2)) = sds_of fk fk b2.
Proof. reflexivity. Qed.

Lemma si_dx_eq : forall fk b1 k1 n1 b2 k2 n2 h2,
  h2 = xhi fk n2 ->
  let si := si_of fk b1 k1 n1 in
  exists_xk (SFS fk) fk b2 k2 n2 h2 (dselect false (dxmask_of (SFS fk) fk (si_b1 si) (si_k1 si) (si_n1 si) (si_h1 si) (si_sds1 si)) (sds_of fk fk b2))
  = kdisj_apart_x fk fk b1 k1 n1 b2 k2 n2.
Proof.
  intros fk b1 k1 n1 b2 k2 n2 h2 Hh si. unfold si, si_of, mk_si. cbn [si_b1 si_k1 si_n1 si_h1 si_sds1].
  change (ci_sds (mk_ci (SFS fk) fk (kdisj_sides fk) ?b)) with (sds_of fk fk b).
  rewrite exists_xk_dselect_eq; [apply p5_in_sides_x_eq | apply xhiF_eq | exact Hh].
Qed.

Lemma apartf_eq : forall fk b1 k1 n1 b2 k2 n2 cc st,
  let si := si_of fk b1 k1 n1 in
  pcc_ok fk cc -> pst_ok fk si st ->
  let '(r, cc', st') := apartf fk si b2 k2 n2 cc st in
  r = ranges_apart_x fk b1 k1 n1 b2 k2 n2 /\ pcc_ok fk cc' /\ pst_ok fk si st'.
Proof.
  intros fk b1 k1 n1 b2 k2 n2 cc st si Hcc Hst. unfold apartf.
  pose proof (st_get_ok fk si cc st b2 Hcc Hst) as G.
  destruct (st_get fk si cc st b2) as [[e cc1] st1]. destruct G as (He & Hcc1 & Hst1).
  assert (Hf1 : cc_fs cc1 = SFS fk) by exact (proj2 (proj1 Hcc1)). rewrite !Hf1.
  subst e. subst si.
  unfold ranges_apart_x.
  change (si_m1 (si_of fk b1 k1 n1)) with (lit_of_len n1).
  (* [comment removed for export] *)
  assert (XP : forall n2x,
    let (p, st') := (let (h2, cc) := xh_get fk cc1 n2x in
        if thr_test (se_thr (mk_sei (si_of fk b1 k1 n1) b2 (mk_ci (SFS fk) fk (kdisj_sides fk) b2))) k2 h2 then (true, cc, st1)
        else let (dxm, st) := dx_get (cc_fs cc) fk (si_of fk b1 k1 n1) st1 in
          if exists_xk (cc_fs cc) fk b2 k2 n2x h2 (dselect false dxm (se_sds (mk_sei (si_of fk b1 k1 n1) b2 (mk_ci (SFS fk) fk (kdisj_sides fk) b2)))) then (true, cc, st)
          else ((if se_sh (mk_sei (si_of fk b1 k1 n1) b2 (mk_ci (SFS fk) fk (kdisj_sides fk) b2)) then
                   if lin_ge0F (cc_fs cc) fk [(b2, k2)] [(si_b1 (si_of fk b1 k1 n1), si_k1 (si_of fk b1 k1 n1)); (si_n1 (si_of fk b1 k1 n1), 0)] then true
                   else lin_ge0F (cc_fs cc) fk [(si_b1 (si_of fk b1 k1 n1), si_k1 (si_of fk b1 k1 n1))] [(b2, k2); (n2x, 0)]
                 else false), cc, st)) in let (r, cc') := p in
    r = (if match base_range fk b1, base_range fk b2, xhi fk n1, xhi fk n2x with
            | Some (lo1, hi1), Some (lo2, hi2), Some h1, Some h2 => (hi1 + k1 + h1 <=? lo2 + k2) || (hi2 + k2 + h2 <=? lo1 + k1)
            | _, _, _, _ => false end then true
         else if kdisj_apart_x fk fk b1 k1 n1 b2 k2 n2x then true
         else if negb (shares_var b1 b2) then false
         else if lin_ge0 fk [(b2, k2)] [(b1, k1); (n1, 0)] then true else lin_ge0 fk [(b1, k1)] [(b2, k2); (n2x, 0)])
    /\ pcc_ok fk cc' /\ pst_ok fk (si_of fk b1 k1 n1) st').
  { intros n2x.
    pose proof (xh_get_ok fk cc1 n2x Hcc1) as X; destruct (xh_get fk cc1 n2x) as [h2 cc2]; cbn [fst snd] in X; destruct X as [Hh2 Hcc2].
    assert (Hf2 : cc_fs cc2 = SFS fk) by exact (proj2 (proj1 Hcc2)). rewrite !Hf2, !lin_ge0F_eq.
    rewrite sei_thr_eq, sei_sh_eq, sei_sds_eq.
    pose proof (dx_get_ok fk _ st1 Hst1) as D; destruct (dx_get (SFS fk) fk (si_of fk b1 k1 n1) st1) as [dxm st2]; cbn [fst snd] in D; destruct D as [Hdxm Hst2].
    rewrite Hdxm. rewrite (si_dx_eq fk b1 k1 n1 b2 k2 _ h2 Hh2). cbn [si_b1 si_k1 si_n1 si_of mk_si].
    rewrite <- Hh2.
    destruct (base_range fk b1) as [[lo1 hi1]|], (base_range fk b2) as [[lo2 hi2]|]; destruct (xhi fk n1); destruct h2;
    destruct (shares_var b1 b2); cbn [negb];
    repeat match goal with |- context [if ?c then _ else _] => destruct c end;
    first [exact (conj eq_refl (conj Hcc2 Hst1)) | exact (conj eq_refl (conj Hcc2 Hst2))]. }
  destruct n1 as [z1|v1 | | | | | |]; cbn [lit_of_len]; [|apply XP..].
  destruct n2 as [z2|v | | | | | |]; [|apply XP..].
  rewrite sei_thr_eq, sei_dsel_eq, sei_sh_eq; unfold ranges_apart, lin_apart; cbn [si_b1 si_k1 si_of mk_si].
  rewrite lin_apart0F_eq, xhi_lit.
  destruct (base_range fk b1) as [[lo1 hi1]|], (base_range fk b2) as [[lo2 hi2]|];
    repeat match goal with |- context [if ?c then _ else _] => destruct c end; exact (conj eq_refl (conj Hcc1 Hst1)).
Qed.

(* [comment removed for export] *)
Lemma prune1f_eq : forall fk wa w wv K hints cc st,
  let si := si_of fk (a_base wa) (a_off wa) (elen w) in
  pcc_ok fk cc -> pst_ok fk si st ->
  let '(r, cc', st') := prune1f fk si wa w wv K hints cc st in
  r = prune1 fk wa w wv K hints /\ pcc_ok fk cc' /\ pst_ok fk si st'.
Proof.
  intros fk [b1 k1] w wv K hints cc st si Hcc Hst. cbn [a_base a_off] in si.
  assert (AP : forall b2 k2 n2 cc0 st0, pcc_ok fk cc0 -> pst_ok fk si st0 ->
            let (p, st1) := apartf fk si b2 k2 n2 cc0 st0 in let (r, cc1) := p in
            r = ranges_apart_x fk b1 k1 (elen w) b2 k2 n2 /\ pcc_ok fk cc1 /\ pst_ok fk si st1)
    by (intros; apply apartf_eq; assumption).
  unfold prune1f, prune1. cbn [a_base a_off]. change (2 ^ 64) with two64.
  destruct K as [[kb kk] w2 v|[kb kk] len|[kb kk] len bk|lo hi|e m|e lo hi|[eb ek] en|c1 m1 c2 m2];
    try exact (conj eq_refl (conj Hcc Hst)).
  - destruct (expr_eqb kb b1); [exact (conj eq_refl (conj Hcc Hst))|].
    specialize (AP kb kk (elen w2) cc st Hcc Hst). destruct (apartf fk si kb kk (elen w2) cc st) as [[ap cc1] st1].
    destruct AP as (-> & Hcc1 & Hst1).
    destruct (ranges_apart_x fk b1 k1 (elen w) kb kk (elen w2)); [exact (conj eq_refl (conj Hcc1 Hst1))|].
    match goal with |- context [if ?c then _ else _] => destruct c end; [exact (conj eq_refl (conj Hcc1 Hst1))|].
    destruct hints as [|[|] hs]; exact (conj eq_refl (conj Hcc1 Hst1)).
  - destruct (expr_eqb kb b1); [exact (conj eq_refl (conj Hcc Hst))|].
    specialize (AP kb kk len cc st Hcc Hst). destruct (apartf fk si kb kk len cc st) as [[ap cc1] st1].
    destruct AP as (-> & Hcc1 & Hst1).
    destruct (ranges_apart_x fk b1 k1 (elen w) kb kk len); [exact (conj eq_refl (conj Hcc1 Hst1))|].
    destruct (kzero_cut fk b1 k1 (elen w) kb kk len); [|exact (conj eq_refl (conj Hcc1 Hst1))].
    destruct hints as [|[|] hs]; exact (conj eq_refl (conj Hcc1 Hst1)).
  - destruct (expr_eqb kb b1); [exact (conj eq_refl (conj Hcc Hst))|].
    specialize (AP kb kk len cc st Hcc Hst). destruct (apartf fk si kb kk len cc st) as [[ap cc1] st1].
    destruct AP as (-> & Hcc1 & Hst1).
    destruct (ranges_apart_x fk b1 k1 (elen w) kb kk len); [exact (conj eq_refl (conj Hcc1 Hst1))|].
    destruct hints as [|[|] hs]; exact (conj eq_refl (conj Hcc1 Hst1)).
  - clearbody si.
    assert (GEN : let (p, st2) := (if hi - lo <? two64 then
        let (p, st0) := apartf fk si (ELit 0) lo (ELit (hi - lo)) cc st in
        let (ap, cc0) := p in
        (if ap then ([KImg lo hi], [], hints)
         else match hints with
              | [] => ([], [], [])
              | true :: hs => ([KImg lo hi], [SCDisj {| a_base := b1; a_off := k1 |} (elen w) {| a_base := ELit 0; a_off := lo |} (ELit (hi - lo))], hs)
              | false :: hs => ([], [], hs)
              end, cc0, st0)
       else ([], [], hints, cc, st)) in let (r, cc2) := p in
       r = (if hi - lo <? two64
       then
        if ranges_apart_x fk b1 k1 (elen w) (ELit 0) lo (ELit (hi - lo))
        then ([KImg lo hi], [], hints)
        else
         match hints with
         | [] => ([], [], [])
         | true :: hs => ([KImg lo hi], [SCDisj {| a_base := b1; a_off := k1 |} (elen w) {| a_base := ELit 0; a_off := lo |} (ELit (hi - lo))], hs)
         | false :: hs => ([], [], hs)
         end
       else ([], [], hints)) /\ pcc_ok fk cc2 /\ pst_ok fk si st2).
    { destruct (hi - lo <? two64); [|exact (conj eq_refl (conj Hcc Hst))].
      specialize (AP (ELit 0) lo (ELit (hi - lo)) cc st Hcc Hst). destruct (apartf fk si (ELit 0) lo (ELit (hi - lo)) cc st) as [[ap cc1] st1].
      destruct AP as (-> & Hcc1 & Hst1).
      destruct (ranges_apart_x fk b1 k1 (elen w) (ELit 0) lo (ELit (hi - lo))); [exact (conj eq_refl (conj Hcc1 Hst1))|].
      destruct hints as [|[|] hs]; exact (conj eq_refl (conj Hcc1 Hst1)). }
    destruct b1 as [z| | | | | | |]; try exact GEN. destruct z; try exact GEN. exact (conj eq_refl (conj Hcc Hst)).
Qed.

(* [comment removed for export] *)
Lemma prunef_eq : forall fk wa w wv kn hints cc st,
  let si := si_of fk (a_base wa) (a_off wa) (elen w) in
  pcc_ok fk cc -> pst_ok fk si st ->
  let '(r, cc', st') := prunef fk si wa w wv kn hints cc st in
  r = prune fk wa w wv kn hints /\ pcc_ok fk cc' /\ pst_ok fk si st'.
Proof.
  intros fk wa w wv kn. induction kn as [|K rest IH]; intros hints cc st si Hcc Hst.
  - exact (conj eq_refl (conj Hcc Hst)).
  - cbn [prunef prune].
    pose proof (prune1f_eq fk wa w wv K hints cc st Hcc Hst) as P1. subst si.
    destruct (prune1f fk (si_of fk (a_base wa) (a_off wa) (elen w)) wa w wv K hints cc st) as [[r1 cc1] st1].
    destruct r1 as [[kept scs1] hs1].
    destruct P1 as (E1 & Hcc1 & Hst1). rewrite <- E1.
    pose proof (IH hs1 cc1 st1 Hcc1 Hst1) as P2. cbn zeta in P2.
    destruct (prunef fk (si_of fk (a_base wa) (a_off wa) (elen w)) wa w wv rest hs1 cc1 st1) as [[r2 cc2] st2].
    destruct r2 as [[r scs2] hs2].
    destruct P2 as (E2 & Hcc2 & Hst2). rewrite <- E2.
    exact (conj eq_refl (conj Hcc2 Hst2)).
Qed.

Lemma prune_store_eq : forall fk cc wa w wv kn hints,
  pcc_ok fk cc ->
  fst (prune_store fk cc wa w wv kn hints) = prune fk wa w wv kn hints /\ pcc_ok fk (snd (prune_store fk cc wa w wv kn hints)).
Proof.
  intros fk cc wa w wv kn hints Hcc. unfold prune_store.
  pose proof (cc_get_ok fk cc (a_base wa) Hcc) as [G1 G2].
  destruct (cc_get fk cc (a_base wa)) as [ci1 cc1]. cbn [fst snd] in G1, G2. subst ci1.
  assert (Hst : pst_ok fk (si_of fk (a_base wa) (a_off wa) (elen w)) (ST [] None)).
  { split; [intros b e H; discriminate | intros m H; discriminate]. }
  pose proof (prunef_eq fk wa w wv kn hints cc1 (ST [] None) G2 Hst) as P. cbn zeta in P.
  unfold si_of in P. assert (Hf1 : cc_fs cc1 = SFS fk) by exact (proj2 (proj1 G2)). rewrite Hf1.
  destruct (prunef fk (mk_si (SFS fk) fk (a_base wa) (a_off wa) (elen w) (mk_ci (SFS fk) fk (kdisj_sides fk) (a_base wa))) wa w wv kn hints cc1 (ST [] None))
    as [[r cc2] st2].
  cbn [fst snd]. destruct P as (E & Hcc2 & _). exact (conj E Hcc2).
Qed.
(* [comment removed for export] *)
Lemma filter_factb_app : forall a b, List.filter is_factb (a ++ b) = List.filter is_factb a ++ List.filter is_factb b.
Proof. intros. apply filter_app. Qed.

Lemma kzero_cut_nofacts : forall kn wb wk wn kb kk len, List.filter is_factb (kzero_cut kn wb wk wn kb kk len) = [].
Proof.
  intros. unfold kzero_cut.
  repeat match goal with |- context [if ?c then _ else _] => destruct c | |- context [let '(_, _) := ?p in _] => destruct p end;
    reflexivity.
Qed.
Lemma prune1_facts : forall fk wa w wv K hints,
  List.filter is_factb (fst (fst (prune1 fk wa w wv K hints))) = List.filter is_factb [K].
Proof.
  intros fk [b1 k1] w wv K hints. unfold prune1. cbn [a_base a_off].
  destruct K as [[kb kk] w2 v|[kb kk] len|[kb kk] len bk|lo hi|e m|e lo hi|[eb ek] en|c1 m1 c2 m2]; cbn [List.filter is_factb];
    try reflexivity.
  - destruct (expr_eqb kb b1).
    + match goal with |- context [if ?c then _ else _] => destruct c end; reflexivity.
    + destruct (ranges_apart_x fk b1 k1 (elen w) kb kk (elen w2)); [reflexivity|].
      match goal with |- context [if ?c then _ else _] => destruct c end; [reflexivity|].
      destruct hints as [|[|] hs]; reflexivity.
  - change (2 ^ 64) with two64. destruct (expr_eqb kb b1).
    + destruct len; repeat match goal with |- context [if ?c then _ else _] => destruct c end; cbn -[two64 Z.sub Z.add Z.min Z.max Z.modulo];
        try reflexivity; apply kzero_cut_nofacts.
    + destruct (ranges_apart_x fk b1 k1 (elen w) kb kk len); [reflexivity|].
      destruct (kzero_cut fk b1 k1 (elen w) kb kk len) eqn:KC.
      * destruct hints as [|[|] hs]; reflexivity.
      * cbn [fst]. rewrite <- KC. apply kzero_cut_nofacts.
  - destruct (expr_eqb kb b1).
    + destruct len; repeat match goal with |- context [if ?c then _ else _] => destruct c end; reflexivity.
    + destruct (ranges_apart_x fk b1 k1 (elen w) kb kk len); [reflexivity|]. destruct hints as [|[|] hs]; reflexivity.
  - destruct b1 as [z| | | | | | |]; [destruct z|..];
      repeat match goal with |- context [if ?c then _ else _] => destruct c end; cbn -[Z.sub Z.add Z.min Z.max Z.pow]; try reflexivity;
      destruct hints as [|[|] hs]; reflexivity.
Qed.

Lemma prune_facts : forall fk wa w wv kn hints,
  List.filter is_factb (fst (fst (prune fk wa w wv kn hints))) = List.filter is_factb kn.
Proof.
  intros fk wa w wv kn. induction kn as [|K rest IH]; intros hints; [reflexivity|].
  cbn [prune]. pose proof (prune1_facts fk wa w wv K hints) as H1.
  destruct (prune1 fk wa w wv K hints) as [[kept scs1] hs1]. cbn [fst] in H1.
  specialize (IH hs1). destruct (prune fk wa w wv rest hs1) as [[r scs2] hs2]. cbn [fst] in IH |- *.
  rewrite filter_factb_app, H1, IH. change (K :: rest) with ([K] ++ rest). rewrite filter_factb_app. reflexivity.
Qed.
Lemma carry_ref_facts : forall log kn hints,
  facts_of (fst (fst (carry_ref log kn hints))) = facts_of kn.
Proof.
  intros log kn hints. rewrite !facts_of_filter. induction log as [|[a w v] older IH]; [reflexivity|].
  cbn [carry_ref]. destruct (carry_ref older kn hints) as [[kn1 scs1] hs1]. cbn [fst] in IH.
  rewrite (p5_prunepc_eq _ _ _ _ _ _ _ [] ltac:(constructor)), p5_prunep_eq.
  pose proof (prune_facts (facts_of kn1) a w v kn1 hs1) as PF.
  destruct (prune (facts_of kn1) a w v kn1 hs1) as [[kn2 scs2] hs2]. cbn [fst] in PF |- *.
  cbn [List.filter is_factb]. rewrite PF. exact IH.
Qed.

Lemma carryF_eq : forall fk log kn hints cc,
  fk = facts_of kn -> pcc_ok fk cc ->
  fst (carryF fk cc log kn hints) = carry_ref log kn hints /\ pcc_ok fk (snd (carryF fk cc log kn hints)).
Proof.
  intros fk log kn hints cc Hfk. revert cc. induction log as [|[a w v] older IH]; intros cc Hcc.
  - exact (conj eq_refl Hcc).
  - cbn [carryF carry_ref].
    pose proof (carry_ref_facts older kn hints) as HF.
    destruct (IH cc Hcc) as [E1 Hcc1].
    destruct (carryF fk cc older kn hints) as [[[kn1 scs1] hs1] cc1]. cbn [fst snd] in E1, Hcc1. rewrite <- E1 in HF |- *.
    cbn [fst] in HF.
    rewrite (p5_prunepc_eq _ _ _ _ _ _ _ [] ltac:(constructor)), p5_prunep_eq.
    pose proof (prune_store_eq fk cc1 a w v kn1 hs1 Hcc1) as [E2 Hcc2].
    destruct (prune_store fk cc1 a w v kn1 hs1) as [[[kn2 scs2] hs2] cc2]. cbn [fst snd] in E2, Hcc2 |- *.
    rewrite HF, <- Hfk, <- E2. exact (conj eq_refl Hcc2).
Qed.

Theorem carry_p5_eq : forall log kn hints, carry_p5 log kn hints = carry_ref log kn hints.
Proof.
  intros log kn hints. unfold carry_p5. destruct log as [|s older]; [reflexivity|].
  apply carryF_eq; [reflexivity|].
  split; [split; reflexivity|]. split; intros ? ? H; discriminate.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

Definition P1 (fk : list kentry) (sx : stctx) (K : kentry) : list kentry :=
  fst (fst (prune1 fk (sx_wa sx) (sx_w sx) (sx_wv sx) K [])).

Lemma prune1_nil : forall fk wa w wv K,
  prune1 fk wa w wv K [] = (fst (fst (prune1 fk wa w wv K [])), [], []).
Proof.
  intros fk [b1 k1] w wv K.
  destruct (prune1 fk (SA b1 k1) w wv K []) as [[l scs] hs] eqn:E. cbn [fst].
  revert E. unfold prune1. cbn [a_base a_off].
  destruct K as [[kb kk] w2 v|[kb kk] len|[kb kk] len bk|lo hi|e m|e lo hi|[eb ek] en|c1 m1 c2 m2];
    try (intros E; injection E as <- <- <-; reflexivity).
  - repeat match goal with |- context [if ?c then _ else _] => destruct c end; intros E; injection E as <- <- <-; reflexivity.
  - destruct (expr_eqb kb b1).
    + destruct len; repeat match goal with |- context [if ?c then _ else _] => destruct c end;
        intros E; injection E as <- <- <-; reflexivity.
    + destruct (ranges_apart_x fk b1 k1 (elen w) kb kk len); [intros E; injection E as <- <- <-; reflexivity|].
      destruct (kzero_cut fk b1 k1 (elen w) kb kk len);
        [destruct (ranges_apart_x fk b1 k1 (elen w) kb kk len)|]; intros E; injection E as <- <- <-; reflexivity.
  - destruct (expr_eqb kb b1).
    + destruct len; repeat match goal with |- context [if ?c then _ else _] => destruct c end;
        intros E; injection E as <- <- <-; reflexivity.
    + destruct (ranges_apart_x fk b1 k1 (elen w) kb kk len); intros E; injection E as <- <- <-; reflexivity.
  - destruct b1 as [z| | | | | | |]; [destruct z|..];
      repeat match goal with |- context [if ?c then _ else _] => destruct c end;
      intros E; injection E as <- <- <-; reflexivity.
Qed.

Lemma prune_nil : forall fk wa w wv l,
  prune fk wa w wv l [] = (flat_map (fun K => fst (fst (prune1 fk wa w wv K []))) l, [], []).
Proof.
  intros fk wa w wv l. induction l as [|K rest IH]; [reflexivity|].
  cbn [prune flat_map]. rewrite (prune1_nil fk wa w wv K).
  destruct (prune1 fk wa w wv K []) as [[kept scs] hs]. cbn [fst]. rewrite IH. reflexivity.
Qed.

(* [comment removed for export] *)
Fixpoint PT (fk : list kentry) (sxs : list stctx) (ps : list kentry) : list kentry :=
  match sxs with
  | [] => ps
  | sx :: sr => PT fk sr (flat_map (P1 fk sx) ps)
  end.

Lemma PT_app : forall fk a b ps, PT fk (a ++ b) ps = PT fk b (PT fk a ps).
Proof. intros fk a. induction a as [|sx r IH]; intros b ps; [reflexivity|]. cbn [PT app]. apply IH. Qed.

Lemma flat_map_app' : forall (A B : Type) (f : A -> list B) l1 l2, flat_map f (l1 ++ l2) = flat_map f l1 ++ flat_map f l2.
Proof. intros A B f l1 l2. induction l1 as [|x r IH]; [reflexivity|]. cbn [flat_map app]. rewrite IH, app_assoc. reflexivity. Qed.

Lemma PT_app_ps : forall fk sxs p1 p2, PT fk sxs (p1 ++ p2) = PT fk sxs p1 ++ PT fk sxs p2.
Proof.
  intros fk sxs. induction sxs as [|sx r IH]; intros p1 p2; [reflexivity|]. cbn [PT].
  rewrite flat_map_app'. apply IH.
Qed.

Lemma PT_nil_ps : forall fk sxs, PT fk sxs [] = [].
Proof. intros fk sxs. induction sxs as [|sx r IH]; [reflexivity|]. cbn [PT flat_map]. exact IH. Qed.

Lemma PT_flat_map : forall fk sxs l, PT fk sxs l = flat_map (fun K => PT fk sxs [K]) l.
Proof.
  intros fk sxs l. induction l as [|K rest IH]; [apply PT_nil_ps|].
  change (K :: rest) with ([K] ++ rest). rewrite PT_app_ps, IH. reflexivity.
Qed.

(* [comment removed for export] *)
Fixpoint SPspec (fk : list kentry) (sxs : list stctx) : list kentry :=
  match sxs with
  | [] => []
  | sx :: newer => SPspec fk newer ++ PT fk newer [KWord (sx_wa sx) (sx_w sx) (sx_wv sx)]
  end.

Lemma SPspec_snoc : forall fk l sx,
  SPspec fk (l ++ [sx]) = KWord (sx_wa sx) (sx_w sx) (sx_wv sx) :: flat_map (P1 fk sx) (SPspec fk l).
Proof.
  intros fk l sx. induction l as [|sx0 l' IH]; [reflexivity|].
  cbn [SPspec app]. rewrite IH, PT_app. cbn [PT app].
  rewrite flat_map_app'. reflexivity.
Qed.

Definition sx_of (fk : list kentry) (e : sentry) : stctx :=
  match e with SE wa w wv => SX wa w wv (si_of fk (a_base wa) (a_off wa) (elen w)) end.

(* [comment removed for export] *)
Lemma carry_ref_nil : forall log kn,
  let fk := facts_of kn in
  let sxs := map (sx_of fk) (rev log) in
  carry_ref log kn [] = (SPspec fk sxs ++ PT fk sxs kn, [], []).
Proof.
  intros log kn fk sxs. subst sxs. induction log as [|[wa w wv] older IH]; [reflexivity|].
  cbn [carry_ref]. pose proof (carry_ref_facts older kn []) as HF. rewrite IH in HF |- *. cbn [fst] in HF.
  rewrite (p5_prunepc_eq _ _ _ _ _ _ _ [] ltac:(constructor)), p5_prunep_eq, HF.
  fold fk. rewrite prune_nil. cbn [rev]. rewrite map_app. cbn [map]. rewrite SPspec_snoc, PT_app. cbn [PT].
  rewrite flat_map_app'. reflexivity.
Qed.

(* [comment removed for export] *)

Definition sx_wf (fk : list kentry) (sx : stctx) : Prop :=
  sx_si sx = si_of fk (a_base (sx_wa sx)) (a_off (sx_wa sx)) (elen (sx_w sx)).

Lemma sx_of_wf : forall fk e, sx_wf fk (sx_of fk e).
Proof. intros fk [wa w wv]. reflexivity. Qed.

Lemma stctxs_of_eq : forall fk log cc,
  pcc_ok fk cc ->
  fst (stctxs_of fk cc log) = map (sx_of fk) (rev log) /\ pcc_ok fk (snd (stctxs_of fk cc log)).
Proof.
  intros fk log. induction log as [|[wa w wv] older IH]; intros cc Hcc; [exact (conj eq_refl Hcc)|].
  cbn [stctxs_of]. destruct (IH cc Hcc) as [E1 H1]. destruct (stctxs_of fk cc older) as [r cc1]. cbn [fst snd] in E1, H1.
  unfold mk_stctx. pose proof (cc_get_ok fk cc1 (a_base wa) H1) as [G1 G2].
  destruct (cc_get fk cc1 (a_base wa)) as [ci1 cc2]. cbn [fst snd] in G1, G2 |- *.
  split; [|exact G2]. rewrite E1. cbn [rev]. rewrite map_app. cbn [map]. f_equal. f_equal.
  unfold sx_of. f_equal. subst ci1. rewrite (proj2 (proj1 G2)). reflexivity.
Qed.

Lemma pieces_through_eq : forall fk cc sxs ps,
  pcc_ok fk cc -> Forall (sx_wf fk) sxs ->
  pieces_through fk cc sxs ps = PT fk sxs ps.
Proof.
  intros fk cc sxs. induction sxs as [|sx sr IH]; intros ps Hcc Hwf; [reflexivity|].
  apply Forall_cons_iff in Hwf as [Hsx Hwf]. cbn [pieces_through PT].
  unfold sx_wf in Hsx.
  assert (Hst : pst_ok fk (si_of fk (a_base (sx_wa sx)) (a_off (sx_wa sx)) (elen (sx_w sx))) (ST [] None)).
  { split; [intros b e H; discriminate | intros m H; discriminate]. }
  pose proof (prunef_eq fk (sx_wa sx) (sx_w sx) (sx_wv sx) ps [] cc (ST [] None) Hcc Hst) as P. cbv zeta in P.
  rewrite <- Hsx in P.
  destruct (prunef fk (sx_si sx) (sx_wa sx) (sx_w sx) (sx_wv sx) ps [] cc (ST [] None)) as [[r cc'] st'].
  destruct P as (E & _ & _). subst r. rewrite prune_nil. cbn [fst]. apply IH; assumption.
Qed.

(* [comment removed for export] *)
Lemma P1_fact : forall fk sx K, kkey K = None -> P1 fk sx K = [K].
Proof.
  intros fk sx K H. unfold P1, prune1.
  destruct K as [[kb kk] w2 v|[kb kk] len|[kb kk] len bk|lo hi|e m|e lo hi|[eb ek] en|c1 m1 c2 m2]; try discriminate; reflexivity.
Qed.

Lemma PT_keep : forall fk sxs K, Forall (fun sx => P1 fk sx K = [K]) sxs -> PT fk sxs [K] = [K].
Proof.
  intros fk sxs K H. induction sxs as [|sx sr IH]; [reflexivity|].
  apply Forall_cons_iff in H as [H1 H]. cbn [PT flat_map]. rewrite H1. cbn [app]. apply IH. exact H.
Qed.

(* [comment removed for export] *)
Definition ent_ok (fk : list kentry) (b2 : expr) (gb : option (Z * Z)) (sx : stctx) (c : colent) : Prop :=
  ce_sei c = mk_sei (sx_si sx) b2 (mk_ci (SFS fk) fk (kdisj_sides fk) b2)
  /\ (ce_all c = true -> group_all sx b2 (ce_sei c) gb = true)
  /\ (forall k kw, ce_same c = Some (k, kw) ->
        expr_eqb b2 (a_base (sx_wa sx)) = true /\ k = a_off (sx_wa sx) /\ kw = a_off (sx_wa sx) + Z.of_nat (sx_w sx)).

(* [comment removed for export] *)
Lemma quick_apartL_eq : forall fk sx e b2 k2 z2,
  sx_wf fk sx -> e = mk_sei (sx_si sx) b2 (mk_ci (SFS fk) fk (kdisj_sides fk) b2) ->
  quick_apartL (SFS fk) fk sx e b2 k2 z2
  = ranges_apart_x fk (a_base (sx_wa sx)) (a_off (sx_wa sx)) (elen (sx_w sx)) b2 k2 (ELit z2).
Proof.
  intros fk sx e b2 k2 z2 Hwf He. unfold sx_wf in Hwf. subst e. unfold quick_apartL. rewrite !Hwf. unfold elen.
  change (si_m1 (si_of fk ?b ?k ?n)) with (lit_of_len n). cbn [lit_of_len].
  rewrite sei_thr_eq, sei_dsel_eq, sei_sh_eq. cbn [si_b1 si_k1 si_of mk_si]. rewrite lin_apart0F_eq.
  unfold ranges_apart_x, ranges_apart, lin_apart. rewrite xhi_lit.
  destruct (base_range fk (a_base (sx_wa sx))) as [[lo1 hi1]|], (base_range fk b2) as [[lo2 hi2]|]; reflexivity.
Qed.

Lemma quick_apartX_eq : forall fk sx e b2 k2 n2 h2,
  sx_wf fk sx -> e = mk_sei (sx_si sx) b2 (mk_ci (SFS fk) fk (kdisj_sides fk) b2) -> h2 = xhi fk n2 ->
  match n2 with ELit _ => False | _ => True end ->
  quick_apartX (SFS fk) fk sx e b2 k2 n2 h2
  = ranges_apart_x fk (a_base (sx_wa sx)) (a_off (sx_wa sx)) (elen (sx_w sx)) b2 k2 n2.
Proof.
  intros fk sx e b2 k2 n2 h2 Hwf He Hh Hn. unfold sx_wf in Hwf. subst e. unfold quick_apartX, dxm_of. rewrite !Hwf.
  rewrite sei_thr_eq, sei_sh_eq, sei_sds_eq.
  rewrite (si_dx_eq fk _ _ _ b2 k2 n2 h2 Hh).
  cbn [si_b1 si_k1 si_n1 si_of mk_si]. rewrite !lin_ge0F_eq.
  unfold ranges_apart_x. unfold elen. rewrite xhi_lit, <- Hh.
  destruct n2; [destruct Hn|..];
    destruct (base_range fk (a_base (sx_wa sx))) as [[lo1 hi1]|]; destruct (base_range fk b2) as [[lo2 hi2]|]; destruct h2;
    destruct (shares_var (a_base (sx_wa sx)) b2); cbn [negb]; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma P1_foreign_keep : forall fk sx b2 K,
  let wa := sx_wa sx in
  kkey K = Some b2 -> expr_eqb b2 (a_base wa) = false ->
  match K with KImg lo hi => Z.ltb (hi - lo) two64 = true | _ => True end ->
  (forall k2 n2, match K with
                 | KWord (SA _ kk) w' _ => k2 = kk /\ n2 = elen w'
                 | KZero (SA _ kk) l | KBlob (SA _ kk) l _ => k2 = kk /\ n2 = l
                 | KImg lo hi => k2 = lo /\ n2 = ELit (hi - lo)
                 | _ => False
                 end -> ranges_apart_x fk (a_base wa) (a_off wa) (elen (sx_w sx)) b2 k2 n2 = true) ->
  P1 fk sx K = [K].
Proof.
  intros fk sx b2 K wa HK Hneq Himg HRA. unfold P1, prune1. fold wa.
  destruct wa as [b1 k1] eqn:Ewa. cbn [a_base a_off] in *.
  destruct K as [[kb kk] w2 v|[kb kk] len|[kb kk] len bk|lo hi|e m|e lo hi|[eb ek] en|c1 m1 c2 m2];
    cbn [kkey] in HK; try discriminate; injection HK as <-.
  - rewrite Hneq. rewrite (HRA kk (elen w2) (conj eq_refl eq_refl)). reflexivity.
  - rewrite Hneq. rewrite (HRA kk len (conj eq_refl eq_refl)). reflexivity.
  - rewrite Hneq. rewrite (HRA kk len (conj eq_refl eq_refl)). reflexivity.
  - change (2 ^ 64) with two64. rewrite Himg.
    specialize (HRA lo (ELit (hi - lo)) (conj eq_refl eq_refl)).
    destruct b1 as [z| | | | | | |]; try (rewrite HRA; reflexivity).
    destruct z as [|p|p]; try (rewrite HRA; reflexivity).
    cbn in Hneq. discriminate.
Qed.

Lemma orb_if : forall a b : bool, (if a then true else b) = (a || b)%bool.
Proof. intros [|] b; reflexivity. Qed.

(* [comment removed for export] *)
Lemma quick_keepL_sound : forall fk sx c b2 gb K,
  sx_wf fk sx -> ent_ok fk b2 gb sx c -> kkey K = Some b2 -> klen_sym K = None ->
  quick_keepL (SFS fk) fk sx (ce_sei c) K = true -> P1 fk sx K = [K].
Proof.
  intros fk sx c b2 gb K Hwf (He & _ & _) HK HL HQ.
  pose proof (fun k2 z2 => quick_apartL_eq fk sx (ce_sei c) b2 k2 z2 Hwf He) as QA.
  destruct K as [[kb kk] w2 v|[kb kk] len|[kb kk] len bk|lo hi|e m|e lo hi|[eb ek] en|c1 m1 c2 m2];
    cbn [kkey klen_sym] in HK, HL; try discriminate.
  - (* [comment removed for export] *) injection HK as <-. unfold quick_keepL in HQ.
    destruct (expr_eqb kb (a_base (sx_wa sx))) eqn:Eb.
    + unfold P1, prune1. destruct (sx_wa sx) as [b1 k1]. cbn [a_base a_off] in *. rewrite Eb.
      rewrite orb_if in HQ. rewrite HQ. reflexivity.
    + apply (P1_foreign_keep fk sx kb); [reflexivity | exact Eb | exact I |].
      intros k2 n2 [-> ->]. change (elen w2) with (ELit (Z.of_nat w2)). rewrite <- (QA kk (Z.of_nat w2)). exact HQ.
  - (* [comment removed for export] *) injection HK as <-. destruct len as [l0| | | | | | |]; try discriminate. unfold quick_keepL in HQ.
    destruct (expr_eqb kb (a_base (sx_wa sx))) eqn:Eb.
    + unfold P1, prune1. destruct (sx_wa sx) as [b1 k1]. cbn [a_base a_off] in *. rewrite Eb.
      unfold zin64 in HQ.
      destruct (Z.leb 0 l0) eqn:G1; [|discriminate]. destruct (Z.ltb l0 two64) eqn:G2; [|discriminate].
      destruct (Z.ltb 0 l0) eqn:G3; [|discriminate].
      apply Z.leb_le in G1. apply Z.ltb_lt in G2. apply Z.ltb_lt in G3.
      change (2 ^ 64) with two64. rewrite (Z.mod_small l0 two64) by lia.
      destruct (Z.leb (kk + l0) k1) eqn:C1.
      * apply Z.leb_le in C1. rewrite (Z.min_r k1 (kk + l0)) by lia.
        destruct (Z.ltb_spec kk (kk + l0)); [|lia].
        destruct (Z.ltb_spec (Z.max kk (k1 + Z.of_nat (sx_w sx))) (kk + l0)); [lia|].
        cbn [app fst]. f_equal. f_equal. f_equal. lia.
      * apply Z.leb_le in HQ. rewrite (Z.min_l k1 (kk + l0)) by lia.
        destruct (Z.ltb_spec kk k1); [lia|].
        rewrite (Z.max_l kk (k1 + Z.of_nat (sx_w sx))) by lia.
        destruct (Z.ltb_spec kk (kk + l0)); [|lia].
        cbn [app fst]. f_equal. f_equal. f_equal. lia.
    + apply (P1_foreign_keep fk sx kb); [reflexivity | exact Eb | exact I |].
      intros k2 n2 [-> ->]. rewrite <- (QA kk l0). exact HQ.
  - (* [comment removed for export] *) injection HK as <-. destruct len as [l0| | | | | | |]; try discriminate. unfold quick_keepL in HQ.
    destruct (expr_eqb kb (a_base (sx_wa sx))) eqn:Eb.
    + unfold P1, prune1. destruct (sx_wa sx) as [b1 k1]. cbn [a_base a_off] in *. rewrite Eb.
      change (2 ^ 64) with two64. cbv zeta in HQ. rewrite orb_if in HQ. cbv zeta. rewrite HQ. reflexivity.
    + apply (P1_foreign_keep fk sx kb); [reflexivity | exact Eb | exact I |].
      intros k2 n2 [-> ->]. rewrite <- (QA kk l0). exact HQ.
  - (* [comment removed for export] *) injection HK as <-. unfold quick_keepL in HQ.
    assert (FOREIGN : expr_eqb (ELit 0) (a_base (sx_wa sx)) = false ->
              (if Z.ltb (hi - lo) two64 then quick_apartL (SFS fk) fk sx (ce_sei c) (ELit 0) lo (hi - lo) else false) = true ->
              P1 fk sx (KImg lo hi) = [KImg lo hi]).
    { intros Eb H. destruct (Z.ltb (hi - lo) two64) eqn:Hi; [|discriminate].
      apply (P1_foreign_keep fk sx (ELit 0)); [reflexivity | exact Eb | exact Hi |].
      intros k2 n2 [-> ->]. rewrite <- (QA lo (hi - lo)). exact H. }
    destruct (a_base (sx_wa sx)) as [z| | | | | | |] eqn:Eb0; try (apply FOREIGN; [reflexivity | exact HQ]).
    destruct z as [|p|p]; try (apply FOREIGN; [reflexivity | exact HQ]).
    clear FOREIGN. unfold P1, prune1. destruct (sx_wa sx) as [b1 k1]. cbn [a_base a_off] in *. subst b1.
    destruct (Z.ltb_spec lo hi); [|discriminate].
    destruct (Z.leb_spec hi k1).
    + rewrite (Z.min_r k1 hi) by lia. destruct (Z.ltb_spec lo hi); [|lia].
      destruct (Z.ltb_spec (Z.max lo (k1 + Z.of_nat (sx_w sx))) hi); [lia|]. reflexivity.
    + apply Z.leb_le in HQ. rewrite (Z.min_l k1 hi) by lia. destruct (Z.ltb_spec lo k1); [lia|].
      rewrite (Z.max_l lo (k1 + Z.of_nat (sx_w sx))) by lia.
      destruct (Z.ltb_spec lo hi); [|lia]. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma quick_keepX_sound : forall fk sx c b2 gb K n h2,
  sx_wf fk sx -> ent_ok fk b2 gb sx c -> kkey K = Some b2 -> klen_sym K = Some n -> h2 = xhi fk n ->
  quick_keepX (SFS fk) fk sx (ce_sei c) h2 K = true -> P1 fk sx K = [K].
Proof.
  intros fk sx c b2 gb K n h2 Hwf (He & _ & _) HK HL Hh HQ.
  destruct K as [[kb kk] w2 v|[kb kk] len|[kb kk] len bk|lo hi|e m|e lo hi|[eb ek] en|c1 m1 c2 m2];
    cbn [kkey klen_sym] in HK, HL; try discriminate; injection HK as <-;
    (destruct len as [l0| | | | | | |]; [discriminate|..]); injection HL as <-; unfold quick_keepX in HQ;
    destruct (expr_eqb kb (a_base (sx_wa sx))) eqn:Eb;
    try (unfold P1, prune1; destruct (sx_wa sx) as [b1 k1]; cbn [a_base a_off] in *; rewrite Eb, HQ; reflexivity);
    (apply (P1_foreign_keep fk sx kb); [reflexivity | exact Eb | exact I |]);
    intros k2 n2 [-> ->]; rewrite <- (quick_apartX_eq fk sx (ce_sei c) kb kk _ h2 Hwf He Hh I); exact HQ.
Qed.

(* [comment removed for export] *)
Lemma fast_all_exists : forall fs fk b2 ds gl gh k2 m2,
  gl <= k2 -> k2 + m2 <= gh ->
  fast_all ds gl gh = true -> exists_sd fs fk b2 k2 m2 ds = true.
Proof.
  intros fs fk b2 ds gl gh k2 m2 H1 H2. induction ds as [|d r IH]; [discriminate|].
  cbn [fast_all exists_sd]. intros H.
  destruct (sd_eval fs fk b2 d k2 m2) eqn:E; [reflexivity|].
  apply IH. revert H E. unfold sd_eval.
  destruct (sd_same d); [|intros H' _; exact H'].
  destruct (Z.leb_spec (a_off (sd_c d)) gl); [|intros H' _; exact H'].
  destruct (sd_lim d) as [L|]; [|intros H' _; exact H'].
  destruct (Z.leb_spec gh L); [|intros H' _; exact H'].
  destruct (Z.leb_spec (a_off (sd_c d)) k2); [|lia].
  destruct (Z.leb_spec (k2 + m2) L); [|lia].
  intros _ E. discriminate.
Qed.

(* [comment removed for export] *)
Lemma group_all_sound : forall fk sx c b2 gb K gl gh lo hi,
  sx_wf fk sx -> ent_ok fk b2 gb sx c ->
  group_all sx b2 (ce_sei c) (Some (gl, gh)) = true ->
  klit K = Some (b2, lo, hi) -> gl <= lo -> hi <= gh ->
  P1 fk sx K = [K].
Proof.
  intros fk sx c b2 gb K gl gh lo hi Hwf (He & _ & _) HG HK Hgl Hgh.
  unfold group_all in HG.
  rewrite Hwf in HG at 1. unfold si_of, mk_si in HG. cbn [si_m1 lit_of_len elen] in HG.
  destruct (expr_eqb b2 (a_base (sx_wa sx))) eqn:Eb; [discriminate|].
  assert (QA : forall k2 z2, lo = k2 -> hi = k2 + zlit64 z2 -> quick_apartL (SFS fk) fk sx (ce_sei c) b2 k2 z2 = true).
  { intros k2 z2 -> ->. unfold quick_apartL. rewrite Hwf at 1. unfold si_of, mk_si. cbn [si_m1 lit_of_len elen].
    destruct (se_thr (ce_sei c)) as [[tA tB]|].
    - unfold thr_test.
      destruct (Z.leb_spec tA gl).
      + destruct (Z.leb_spec tA k2); [reflexivity | lia].
      + destruct (Z.leb_spec gh tB).
        * destruct (Z.leb tA k2); [reflexivity|]. destruct (Z.leb_spec (k2 + zlit64 z2) tB); [reflexivity | lia].
        * destruct (Z.leb tA k2); [reflexivity|]. destruct (Z.leb (k2 + zlit64 z2) tB); [reflexivity|].
          rewrite (fast_all_exists _ _ _ _ _ _ _ _ Hgl Hgh HG). reflexivity.
    - cbn [thr_test]. rewrite (fast_all_exists _ _ _ _ _ _ _ _ Hgl Hgh HG). reflexivity. }
  pose proof (fun k2 z2 H1 H2 => eq_trans (eq_sym (quick_apartL_eq fk sx (ce_sei c) b2 k2 z2 Hwf He)) (QA k2 z2 H1 H2)) as RA.
  destruct K as [[kb kk] w2 v|[kb kk] len|[kb kk] len bk|ilo ihi|e m|e rlo rhi|[eb ek] en|c1 m1 c2 m2];
    cbn [klit] in HK; try discriminate.
  - injection HK as <- <- <-. apply (P1_foreign_keep fk sx kb); [reflexivity | exact Eb | exact I |].
    intros k2 n2 [-> ->]. apply (RA kk (Z.of_nat w2)); reflexivity.
  - destruct len as [l0| | | | | | |]; try discriminate. injection HK as <- <- <-.
    apply (P1_foreign_keep fk sx kb); [reflexivity | exact Eb | exact I |].
    intros k2 n2 [-> ->]. apply (RA kk l0); reflexivity.
  - destruct len as [l0| | | | | | |]; try discriminate. injection HK as <- <- <-.
    apply (P1_foreign_keep fk sx kb); [reflexivity | exact Eb | exact I |].
    intros k2 n2 [-> ->]. apply (RA kk l0); reflexivity.
  - destruct (Z.ltb (ihi - ilo) two64) eqn:Hi; [|discriminate]. injection HK as <- <- <-.
    apply (P1_foreign_keep fk sx (ELit 0)); [reflexivity | exact Eb | exact Hi |].
    intros k2 n2 [-> ->]. apply (RA ilo (ihi - ilo)); reflexivity.
Qed.

(* [comment removed for export] *)
Definition ents_ok (fk : list kentry) (b2 : expr) (gb : option (Z * Z)) (sxs : list stctx) (ents : list colent) : Prop :=
  Forall2 (ent_ok fk b2 gb) sxs ents.

Lemma column_of_ok : forall fk sxs b2 gb,
  let col := column_of sxs b2 (mk_ci (SFS fk) fk (kdisj_sides fk) b2) gb in
  ents_ok fk b2 gb sxs (co_ents col)
  /\ (co_all col = true -> Forall (fun c => ce_all c = true) (co_ents col))
  /\ co_gb col = gb.
Proof.
  intros fk sxs b2 gb col. subst col. unfold column_of. cbn [co_ents co_all co_gb].
  split; [|split; [|reflexivity]].
  - induction sxs as [|sx sr IH]; [constructor|]. cbn [map]. constructor; [|exact IH].
    split; [reflexivity|]. split; [cbn [ce_all ce_sei]; intros H; exact H|].
    cbn [ce_same]. intros k kw. destruct (expr_eqb b2 (a_base (sx_wa sx))); [|discriminate].
    intros H. injection H as <- <-. split; [reflexivity|]. split; reflexivity.
  - induction sxs as [|sx sr IH]; cbn [map all_true]; intros H; [constructor|].
    match type of H with (if ?c then _ else _) = true => destruct c eqn:G; [|discriminate] end.
    constructor; [exact G | exact (IH H)].
Qed.

Lemma klit_kkey : forall K b lo hi, klit K = Some (b, lo, hi) -> kkey K = Some b.
Proof.
  intros K b lo hi H.
  destruct K as [[kb kk] w2 v|[kb kk] len|[kb kk] len bk|ilo ihi|e m|e rlo rhi|[eb ek] en|c1 m1 c2 m2];
    cbn [klit kkey] in H |- *; try discriminate.
  - injection H as <- _ _. reflexivity.
  - destruct len; try discriminate. injection H as <- _ _. reflexivity.
  - destruct len; try discriminate. injection H as <- _ _. reflexivity.
  - destruct (Z.ltb (ihi - ilo) two64); [|discriminate]. injection H as <- _ _. reflexivity.
Qed.

Lemma PT_cons_keep : forall fk sx sr K, P1 fk sx K = [K] -> PT fk (sx :: sr) [K] = PT fk sr [K].
Proof. intros fk sx sr K H. cbn [PT flat_map]. rewrite H. reflexivity. Qed.

(* [comment removed for export] *)
Lemma same_quick : forall fk sx c b2 gb K k kw lo hi,
  ent_ok fk b2 gb sx c -> kkey K = Some b2 -> ce_same c = Some (k, kw) -> esum K = Some (lo, hi) ->
  (if Z.leb hi k then true else Z.leb kw lo) = true ->
  quick_keepL (SFS fk) fk sx (ce_sei c) K = true.
Proof.
  intros fk sx c b2 gb K k kw lo hi (_ & _ & Hs) HK Hc HE HT.
  destruct (Hs k kw Hc) as (Eb & -> & ->).
  unfold quick_keepL.
  destruct K as [[kb kk] w2 v|[kb kk] len|[kb kk] len bk|ilo ihi|e m|e rlo rhi|[eb ek] en|c1 m1 c2 m2];
    cbn [kkey esum] in HK, HE; try discriminate.
  - injection HK as <-. rewrite Eb. injection HE as <- <-. exact HT.
  - injection HK as <-. destruct len as [l0| | | | | | |]; try discriminate. rewrite Eb.
    destruct (zin64 l0); [|discriminate]. destruct (Z.ltb 0 l0); [|discriminate]. injection HE as <- <-. exact HT.
  - injection HK as <-. destruct len as [l0| | | | | | |]; try discriminate. rewrite Eb.
    destruct (zin64 l0) eqn:Z64; [|discriminate]. injection HE as <- <-.
    unfold zin64 in Z64. destruct (Z.leb_spec 0 l0); [|discriminate]. destruct (Z.ltb_spec l0 two64); [|discriminate].
    cbv zeta. rewrite (Z.mod_small l0 two64) by lia. exact HT.
  - injection HK as E. apply p5_expr_eqb_eq in Eb. rewrite <- Eb, <- E.
    destruct (Z.ltb ilo ihi); [|discriminate]. injection HE as <- <-. exact HT.
Qed.

(* [comment removed for export] *)
Lemma first_failL_sound : forall fk b2 gb K useall sxs ents,
  Forall (sx_wf fk) sxs -> ents_ok fk b2 gb sxs ents -> kkey K = Some b2 -> klen_sym K = None ->
  (useall = true -> exists gl gh lo hi, gb = Some (gl, gh) /\ klit K = Some (b2, lo, hi) /\ gl <= lo /\ hi <= gh) ->
  match first_failL (SFS fk) fk useall (esum K) sxs ents K with
  | None => PT fk sxs [K] = [K]
  | Some sfx => exists pre, sxs = pre ++ sfx /\ PT fk pre [K] = [K]
  end.
Proof.
  intros fk b2 gb K useall sxs ents Hwf Hents HK HL HU.
  induction Hents as [|sx c sr cr Hc Hents IH]; [reflexivity|].
  apply Forall_cons_iff in Hwf as [Hsx Hwf]. specialize (IH Hwf). cbn [first_failL].
  assert (STEP : P1 fk sx K = [K] ->
            match first_failL (SFS fk) fk useall (esum K) sr cr K with
            | None => PT fk (sx :: sr) [K] = [K]
            | Some sfx => exists pre, sx :: sr = pre ++ sfx /\ PT fk pre [K] = [K]
            end).
  { intros HP. rewrite PT_cons_keep by exact HP.
    destruct (first_failL (SFS fk) fk useall (esum K) sr cr K) as [sfx|]; [|exact IH].
    destruct IH as [pre [E1 E2]]. exists (sx :: pre). split; [rewrite E1; reflexivity|].
    rewrite PT_cons_keep by exact HP. exact E2. }
  assert (QK : quick_keepL (SFS fk) fk sx (ce_sei c) K = true -> P1 fk sx K = [K])
    by (intros Q; exact (quick_keepL_sound fk sx c b2 gb K Hsx Hc HK HL Q)).
  assert (SM : (match ce_same c, esum K with
                | Some (k, kw), Some (lo, hi) => if Z.leb hi k then true else Z.leb kw lo
                | _, _ => quick_keepL (SFS fk) fk sx (ce_sei c) K
                end) = true -> P1 fk sx K = [K]).
  { destruct (ce_same c) as [[k kw]|] eqn:Hcs; [|exact QK]. destruct (esum K) as [[lo hi]|] eqn:HE; [|exact QK].
    intros HT. apply QK. exact (same_quick fk sx c b2 gb K k kw lo hi Hc HK Hcs HE HT). }
  destruct (if useall then ce_all c else false) eqn:UA.
  - apply STEP. destruct useall; [|discriminate]. destruct (HU eq_refl) as (gl & gh & lo & hi & Hgb & HKl & H1 & H2).
    apply (group_all_sound fk sx c b2 gb K gl gh lo hi Hsx Hc); [|exact HKl|exact H1|exact H2].
    rewrite <- Hgb. exact (proj1 (proj2 Hc) UA).
  - match goal with |- context [if ?cnd then first_failL _ _ _ _ _ _ _ else Some _] => destruct cnd eqn:CM end.
    + apply STEP. apply SM. reflexivity.
    + exists []. split; reflexivity.
Qed.

Lemma first_failX_sound : forall fk b2 gb K n h2 sxs ents,
  Forall (sx_wf fk) sxs -> ents_ok fk b2 gb sxs ents -> kkey K = Some b2 -> klen_sym K = Some n -> h2 = xhi fk n ->
  match first_failX (SFS fk) fk sxs ents h2 K with
  | None => PT fk sxs [K] = [K]
  | Some sfx => exists pre, sxs = pre ++ sfx /\ PT fk pre [K] = [K]
  end.
Proof.
  intros fk b2 gb K n h2 sxs ents Hwf Hents HK HL Hh.
  induction Hents as [|sx c sr cr Hc Hents IH]; [reflexivity|].
  apply Forall_cons_iff in Hwf as [Hsx Hwf]. specialize (IH Hwf). cbn [first_failX].
  destruct (quick_keepX (SFS fk) fk sx (ce_sei c) h2 K) eqn:Q.
  - pose proof (quick_keepX_sound fk sx c b2 gb K n h2 Hsx Hc HK HL Hh Q) as HP.
    rewrite PT_cons_keep by exact HP.
    destruct (first_failX (SFS fk) fk sr cr h2 K) as [sfx|]; [|exact IH].
    destruct IH as [pre [E1 E2]]. exists (sx :: pre). split; [rewrite E1; reflexivity|].
    rewrite PT_cons_keep by exact HP. exact E2.
  - exists []. split; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma PT_nil : forall fk sxs, PT fk sxs [] = [].
Proof. intros fk sxs. induction sxs as [|sx r IH]; [reflexivity|]. cbn [PT flat_map]. exact IH. Qed.

Lemma kdead_P1 : forall fk sx K, kdead sx K = true -> P1 fk sx K = [].
Proof.
  intros fk sx K H. unfold kdead in H.
  destruct K as [[kb kk] w2 v|[kb kk] len|[kb kk] len bk|lo hi|e m|e lo hi|[eb ek] en|c1 m1 c2 m2]; try discriminate.
  unfold P1, prune1. destruct (sx_wa sx) as [b1 k1]. cbn [a_base a_off] in *.
  destruct (expr_eqb kb b1); [|discriminate].
  destruct (Z.leb (kk + Z.of_nat w2) k1 || Z.leb (k1 + Z.of_nat (sx_w sx)) kk)%bool; [discriminate|]. reflexivity.
Qed.

Lemma mask_eqb_eq : forall a b, mask_eqb a b = true -> a = b.
Proof.
  induction a as [|[x1 x2] r IH]; intros [|[y1 y2] s] H; cbn [mask_eqb] in H; try discriminate; [reflexivity|].
  destruct (Bool.eqb x1 y1) eqn:E1; [|discriminate]. destruct (Bool.eqb x2 y2) eqn:E2; [|discriminate].
  apply Bool.eqb_prop in E1. apply Bool.eqb_prop in E2. subst. f_equal. exact (IH s H).
Qed.
Lemma thr_hull_test : forall t1 t2 k h,
  thr_test (thr_hull t1 t2) k (Some h) = true -> thr_test t1 k (Some h) = true /\ thr_test t2 k (Some h) = true.
Proof.
  intros [[a0 b0]|] [[a b]|] k h; cbn [thr_hull thr_test]; try discriminate.
  destruct (Z.leb_spec (Z.max a0 a) k).
  - intros _. destruct (Z.leb_spec a0 k); [|lia]. destruct (Z.leb_spec a k); [|lia]. split; reflexivity.
  - destruct (Z.leb_spec (k + h) (Z.min b0 b)); [|discriminate]. intros _.
    destruct (Z.leb a0 k); destruct (Z.leb a k); destruct (Z.leb_spec (k + h) b0); destruct (Z.leb_spec (k + h) b); try lia; split; reflexivity.
Qed.

(* [comment removed for export] *)
Definition fc_wf (sds2 : list (sdesc * sdesc)) (f : fcls) : Prop :=
  match f with FC _ (Some (m, ds)) => ds = dselect true m sds2 | _ => True end.

Lemma fc_add_wf : forall sds2 f sx c,
  se_dsel (ce_sei c) = dselect true (si_dmask (sx_si sx)) sds2 -> fc_wf sds2 f -> fc_wf sds2 (fc_add f sx c).
Proof.
  intros sds2 f sx c He Hf. unfold fc_add. destruct (si_m1 (sx_si sx)); [|exact I].
  destruct f as [| |thr [[m ds]|]]; cbn [fc_wf] in *; try exact I; [exact He|].
  destruct (mask_eqb m (si_dmask (sx_si sx))); [exact Hf | exact I].
Qed.

(* [comment removed for export] *)
Lemma fc_add_sound : forall fs fk sds2 f sx c b2 k2 z2,
  se_dsel (ce_sei c) = dselect true (si_dmask (sx_si sx)) sds2 -> fc_wf sds2 f ->
  fc_test fs fk (fc_add f sx c) b2 k2 (zlit64 z2) = true ->
  fc_test fs fk f b2 k2 (zlit64 z2) = true /\ quick_apartL fs fk sx (ce_sei c) b2 k2 z2 = true.
Proof.
  intros fs fk sds2 f sx c b2 k2 z2 He Hf. unfold fc_add, quick_apartL.
  destruct (si_m1 (sx_si sx)) as [m1|]; [|discriminate].
  destruct f as [| |thr md]; cbn [fc_test]; [| discriminate |].
  - intros H. split; [reflexivity|].
    destruct (thr_test (se_thr (ce_sei c)) k2 (Some (zlit64 z2))); [reflexivity|]. rewrite H. reflexivity.
  - destruct (thr_test (thr_hull thr (se_thr (ce_sei c))) k2 (Some (zlit64 z2))) eqn:T.
    + intros _. apply thr_hull_test in T as [T1 T2]. rewrite T1, T2. split; reflexivity.
    + destruct md as [[m ds]|]; [|discriminate].
      destruct (mask_eqb m (si_dmask (sx_si sx))) eqn:M; [|discriminate].
      intros H. apply mask_eqb_eq in M. cbn [fc_wf] in Hf. split.
      * destruct (thr_test thr k2 (Some (zlit64 z2))); [reflexivity | exact H].
      * destruct (thr_test (se_thr (ce_sei c)) k2 (Some (zlit64 z2))); [reflexivity|].
        rewrite He, <- M, <- Hf, H. reflexivity.
Qed.
Lemma klitq_keep : forall fs fk sx e b2 K k2 z2,
  kkey K = Some b2 -> expr_eqb b2 (a_base (sx_wa sx)) = false -> klitq K = Some (k2, z2) ->
  quick_apartL fs fk sx e b2 k2 z2 = true -> quick_keepL fs fk sx e K = true.
Proof.
  intros fs fk sx e b2 K k2 z2 HK Hb Hq HA. unfold quick_keepL.
  destruct K as [[kb kk] w2 v|[kb kk] len|[kb kk] len bk|lo hi|ee m|ee lo hi|[eb ek] en|c1 m1 c2 m2];
    cbn [kkey klitq] in HK, Hq; try discriminate.
  - injection HK as <-. injection Hq as <- <-. rewrite Hb. exact HA.
  - injection HK as <-. destruct len as [l0| | | | | | |]; try discriminate. injection Hq as <- <-. rewrite Hb. exact HA.
  - injection HK as <-. destruct len as [l0| | | | | | |]; try discriminate. injection Hq as <- <-. rewrite Hb. exact HA.
  - injection HK as <-. destruct (Z.ltb (hi - lo) two64) eqn:Hi; [|discriminate]. injection Hq as <- <-.
    destruct (a_base (sx_wa sx)) as [z| | | | | | |]; try exact HA.
    destruct z as [|p|p]; try exact HA. cbn in Hb. discriminate.
Qed.

(* [comment removed for export] *)
Definition ent_ok2 (fk : list kentry) (b2 : expr) (gb : option (Z * Z)) (sx : stctx) (c : colent) : Prop :=
  ent_ok fk b2 gb sx c /\ (ce_same c = None -> expr_eqb b2 (a_base (sx_wa sx)) = false).

Lemma column_of_ok2 : forall fk sxs b2 gb,
  Forall2 (ent_ok2 fk b2 gb) sxs (co_ents (column_of sxs b2 (mk_ci (SFS fk) fk (kdisj_sides fk) b2) gb)).
Proof.
  intros fk sxs b2 gb. pose proof (column_of_ok fk sxs b2 gb) as [H _]. cbv zeta in H. unfold ents_ok in H.
  unfold column_of in *. cbn [co_ents] in *.
  induction sxs as [|sx sr IH]; [constructor|]. cbn [map] in *.
  apply Forall2_cons_iff in H as [H1 H2]. constructor; [|exact (IH H2)].
  split; [exact H1|]. cbn [ce_same]. destruct (expr_eqb b2 (a_base (sx_wa sx))); [discriminate | reflexivity].
Qed.

Definition cs_wf (sds2 : list (sdesc * sdesc)) (ps : positive * csum) : Prop :=
  fc_wf sds2 (cs_N (snd ps)) /\ fc_wf sds2 (cs_A (snd ps)).

Lemma cs_add_wf : forall sds2 sx c s,
  se_dsel (ce_sei c) = dselect true (si_dmask (sx_si sx)) sds2 ->
  fc_wf sds2 (cs_N s) -> fc_wf sds2 (cs_A s) ->
  fc_wf sds2 (cs_N (cs_add sx c s)) /\ fc_wf sds2 (cs_A (cs_add sx c s)).
Proof.
  intros sds2 sx c s He HN HA. unfold cs_add. cbn [cs_N cs_A]. split; [|exact (fc_add_wf sds2 _ sx c He HA)].
  destruct (ce_all c); [exact HN | exact (fc_add_wf sds2 _ sx c He HN)].
Qed.

Lemma cupd_wf : forall sds2 cid sx c l,
  se_dsel (ce_sei c) = dselect true (si_dmask (sx_si sx)) sds2 ->
  Forall (cs_wf sds2) l -> Forall (cs_wf sds2) (cupd cid sx c l).
Proof.
  intros sds2 cid sx c l He. induction l as [|[p s] r IH]; intros H; cbn [cupd].
  - constructor; [|constructor]. exact (cs_add_wf sds2 sx c cs_empty He I I).
  - apply Forall_cons_iff in H as [[H1 H1'] H2]. cbn [snd] in H1, H1'. destruct (Pos.eqb p cid).
    + constructor; [|exact H2]. exact (cs_add_wf sds2 sx c s He H1 H1').
    + constructor; [split; assumption | exact (IH H2)].
Qed.

Definition dsel_ok (sds2 : list (sdesc * sdesc)) (sx : stctx) (c : colent) : Prop :=
  se_dsel (ce_sei c) = dselect true (si_dmask (sx_si sx)) sds2.

Lemma sums_wf : forall sds2 sxs ents cids,
  Forall2 (dsel_ok sds2) sxs ents -> Forall (cs_wf sds2) (hd [] (sums_of sxs ents cids)).
Proof.
  intros sds2 sxs ents cids H. revert cids. induction H as [|sx c sr cr Hc H IH]; intros cids; [destruct cids; constructor|].
  destruct cids as [|cid ir]; [constructor|]. cbn [sums_of hd].
  destruct (ce_same c); [exact (IH ir)|]. apply cupd_wf; [exact Hc | exact (IH ir)].
Qed.

Definition clook (p : positive) (l : list (positive * csum)) : csum :=
  match find (fun ps => Pos.eqb (fst ps) p) l with Some ps => snd ps | None => cs_empty end.

Lemma clook_cupd : forall p cid sx c l,
  clook p (cupd cid sx c l) = if Pos.eqb cid p then cs_add sx c (clook cid l) else clook p l.
Proof.
  intros p cid sx c l. unfold clook. induction l as [|[q s] r IH].
  - cbn [cupd find fst snd]. destruct (Pos.eqb cid p); reflexivity.
  - cbn [cupd]. destruct (Pos.eqb q cid) eqn:Eq.
    + cbn [find fst snd]. rewrite Eq. apply Pos.eqb_eq in Eq. subst q.
      destruct (Pos.eqb cid p); reflexivity.
    + cbn [find fst snd]. rewrite Eq. destruct (Pos.eqb q p) eqn:Ep.
      * apply Pos.eqb_eq in Ep. subst q. rewrite Pos.eqb_sym, Eq. reflexivity.
      * exact IH.
Qed.

Lemma vlook_map : forall (f : csum -> bool) p l,
  vlook p (map (fun ps => (fst ps, f (snd ps))) l) = true -> f (clook p l) = true.
Proof.
  intros f p l. unfold clook. induction l as [|[q s] r IH]; cbn [map vlook find fst snd]; [discriminate|].
  destruct (Pos.eqb q p); [intros H; exact H | exact IH].
Qed.

Lemma cs_add_sound : forall fs fk sds2 (useall : bool) b2 k2 z2 sx c s,
  dsel_ok sds2 sx c -> fc_wf sds2 (cs_N s) -> fc_wf sds2 (cs_A s) ->
  fc_test fs fk (if useall then cs_N (cs_add sx c s) else cs_A (cs_add sx c s)) b2 k2 (zlit64 z2) = true ->
  fc_test fs fk (if useall then cs_N s else cs_A s) b2 k2 (zlit64 z2) = true
  /\ ((useall = true /\ ce_all c = true) \/ quick_apartL fs fk sx (ce_sei c) b2 k2 z2 = true).
Proof.
  intros fs fk sds2 useall b2 k2 z2 sx c s He HN HA. unfold cs_add. cbn [cs_N cs_A]. destruct useall.
  - destruct (ce_all c) eqn:CA.
    + intros H. split; [exact H | left; split; reflexivity].
    + intros H. destruct (fc_add_sound fs fk sds2 _ sx c b2 k2 z2 He HN H) as [H1 H2]. split; [exact H1 | right; exact H2].
  - intros H. destruct (fc_add_sound fs fk sds2 _ sx c b2 k2 z2 He HA H) as [H1 H2]. split; [exact H1 | right; exact H2].
Qed.

Lemma clook_wf : forall sds2 p l, Forall (cs_wf sds2) l -> fc_wf sds2 (cs_N (clook p l)) /\ fc_wf sds2 (cs_A (clook p l)).
Proof.
  intros sds2 p l H. unfold clook. induction H as [|[q s] r Hq H IH]; cbn [find fst snd]; [split; exact I|].
  destruct (Pos.eqb q p); [exact Hq | exact IH].
Qed.

Lemma sums_of_nil_cids : forall sxs ents, sums_of sxs ents [] = [[]].
Proof. intros [|sx sr] [|c cr]; reflexivity. Qed.

Lemma first_failH_sound : forall fk b2 gb K useall V sxs ents cids,
  Forall (sx_wf fk) sxs -> Forall2 (ent_ok2 fk b2 gb) sxs ents ->
  kkey K = Some b2 -> klen_sym K = None ->
  (useall = true -> exists gl gh lo hi, gb = Some (gl, gh) /\ klit K = Some (b2, lo, hi) /\ gl <= lo /\ hi <= gh) ->
  (forall p, vlook p V = true -> exists k2 z2, klitq K = Some (k2, z2)
       /\ fc_test (SFS fk) fk (if useall then cs_N (clook p (hd [] (sums_of sxs ents cids))) else cs_A (clook p (hd [] (sums_of sxs ents cids)))) b2 k2 (zlit64 z2) = true) ->
  match first_failH (SFS fk) fk V useall (esum K) sxs ents cids K with
  | None => PT fk sxs [K] = [K]
  | Some sfx => exists pre, sxs = pre ++ sfx /\ PT fk pre [K] = [K]
  end.
Proof.
  intros fk b2 gb K useall V sxs ents cids Hwf Hents HK HL HU. revert cids.
  set (sds2 := ci_sds (mk_ci (SFS fk) fk (kdisj_sides fk) b2)).
  assert (DS : Forall2 (dsel_ok sds2) sxs ents).
  { clear Hwf. induction Hents as [|sx c sr cr [(He & _) _] _ IH]; constructor; [|exact IH].
    unfold dsel_ok. rewrite He. reflexivity. }
  remember (esum K) as es eqn:Hes.
  induction Hents as [|sx c sr cr Hc Hents IH]; intros cids HV; [reflexivity|].
  apply Forall_cons_iff in Hwf as [Hsx Hwf]. apply Forall2_cons_iff in DS as [Dc DS].
  destruct Hc as [Hc Hnone]. cbn [first_failH].
  set (ir := match cids with _ :: r => r | [] => [] end).
  (* [comment removed for export] *)
  assert (HV' : forall p, vlook p V = true -> exists k2 z2, klitq K = Some (k2, z2)
       /\ fc_test (SFS fk) fk (if useall then cs_N (clook p (hd [] (sums_of sr cr ir))) else cs_A (clook p (hd [] (sums_of sr cr ir)))) b2 k2 (zlit64 z2) = true).
  { intros p Hp. destruct (HV p Hp) as (k2 & z2 & Hq & T). exists k2, z2. split; [exact Hq|].
    destruct cids as [|cid ir0]; [subst ir; rewrite sums_of_nil_cids in T |- *; exact T|]. subst ir. cbn [sums_of hd] in T.
    destruct (ce_same c); [exact T|]. rewrite clook_cupd in T. destruct (Pos.eqb cid p) eqn:Ep; [|exact T].
    apply Pos.eqb_eq in Ep. subst p.
    destruct (clook_wf sds2 cid _ (sums_wf sds2 sr cr ir0 DS)) as [W1 W2].
    exact (proj1 (cs_add_sound (SFS fk) fk sds2 useall b2 k2 z2 sx c _ Dc W1 W2 T)). }
  assert (STEP : P1 fk sx K = [K] ->
            match first_failH (SFS fk) fk V useall es sr cr ir K with
            | None => PT fk (sx :: sr) [K] = [K]
            | Some sfx => exists pre, sx :: sr = pre ++ sfx /\ PT fk pre [K] = [K]
            end).
  { intros HP. rewrite PT_cons_keep by exact HP. specialize (IH Hwf DS ir HV').
    destruct (first_failH (SFS fk) fk V useall es sr cr ir K) as [sfx|]; [|exact IH].
    destruct IH as [pre [E1 E2]]. exists (sx :: pre). split; [rewrite E1; reflexivity|].
    rewrite PT_cons_keep by exact HP. exact E2. }
  assert (QK : quick_keepL (SFS fk) fk sx (ce_sei c) K = true -> P1 fk sx K = [K])
    by (intros Q; exact (quick_keepL_sound fk sx c b2 gb K Hsx Hc HK HL Q)).
  assert (GA : useall = true -> ce_all c = true -> P1 fk sx K = [K]).
  { intros U CA. destruct (HU U) as (gl & gh & lo & hi & Hgb & HKl & H1 & H2).
    apply (group_all_sound fk sx c b2 gb K gl gh lo hi Hsx Hc); [|exact HKl|exact H1|exact H2].
    rewrite <- Hgb. exact (proj1 (proj2 Hc) CA). }
  destruct (if useall then ce_all c else false) eqn:UA.
  - apply STEP. destruct useall; [|discriminate]. exact (GA eq_refl UA).
  - match goal with |- context [if ?cnd then first_failH _ _ _ _ _ _ _ _ _ else Some _] => destruct cnd eqn:CM end;
      [|exists []; split; reflexivity].
    apply STEP. destruct (ce_same c) as [[k kw]|] eqn:Hcs.
    + destruct es as [[lo hi]|]; [|exact (QK CM)].
      apply QK. exact (same_quick fk sx c b2 gb K k kw lo hi Hc HK Hcs (eq_sym Hes) CM).
    + destruct cids as [|cid ir0]; [exact (QK CM)|].
      destruct (vlook cid V) eqn:VL; [|exact (QK CM)].
      destruct (HV cid VL) as (k2 & z2 & Hq & T). cbn [sums_of hd] in T. rewrite Hcs, clook_cupd, Pos.eqb_refl in T.
      destruct (clook_wf sds2 cid _ (sums_wf sds2 sr cr ir0 DS)) as [W1 W2].
      destruct (cs_add_sound (SFS fk) fk sds2 useall b2 k2 z2 sx c _ Dc W1 W2 T) as [_ [[U CA]|QA]]; [exact (GA U CA)|].
      apply QK. exact (klitq_keep (SFS fk) fk sx (ce_sei c) b2 K k2 z2 HK (Hnone eq_refl) Hq QA).
Qed.

Lemma verdicts_ok : forall fs fk l useall b2 K p,
  vlook p (verdicts fs fk l useall b2 K) = true ->
  exists k2 z2, klitq K = Some (k2, z2)
    /\ fc_test fs fk (if useall then cs_N (clook p l) else cs_A (clook p l)) b2 k2 (zlit64 z2) = true.
Proof.
  intros fs fk l useall b2 K p. unfold verdicts. destruct (klitq K) as [[k2 z2]|]; [|discriminate].
  intros H. exists k2, z2. split; [reflexivity|].
  exact (vlook_map (fun s => fc_test fs fk (if useall then cs_N s else cs_A s) b2 k2 (zlit64 z2)) p l H).
Qed.

(* [comment removed for export] *)
Lemma exists_xk2_imp : forall fs fk b1 k1 n1 h1 b2 k2 n2 h2 sds2 sds1,
  exists_xk2 fs fk b1 k1 n1 h1 (emask_of fs fk b2 k2 n2 h2 sds2) sds1 = true ->
  exists_xk fs fk b2 k2 n2 h2 (dselect false (dxmask_of fs fk b1 k1 n1 h1 sds1) sds2) = true.
Proof.
  intros fs fk b1 k1 n1 h1 b2 k2 n2 h2 sds2. induction sds2 as [|[a1 a2] r2 IH]; intros [|[d1 d2] r1] H;
    cbn [emask_of map exists_xk2] in H; try discriminate.
  cbn [dxmask_of map dselect fst snd andb] in *. fold (emask_of fs fk b2 k2 n2 h2 r2) in H.
  fold (dxmask_of fs fk b1 k1 n1 h1 r1).
  destruct (xk_eval fs fk b1 d1 k1 n1 h1) eqn:I1; destruct (xk_eval fs fk b1 d2 k1 n1 h1) eqn:I2;
    destruct (xk_eval fs fk b2 a1 k2 n2 h2) eqn:E1; destruct (xk_eval fs fk b2 a2 k2 n2 h2) eqn:E2;
    cbn [exists_xk]; rewrite ?E1, ?E2; try reflexivity; cbn in H; try (exact (IH r1 H)); try discriminate.
Qed.

Lemma quick_keepX2_imp : forall fs fk sx e K h2 n,
  klen_sym K = Some n ->
  quick_keepX2 fs fk sx e (emask_of fs fk (match kkey K with Some b => b | None => ELit 0 end) (kx_off K) n h2 (se_sds e)) h2 K = true ->
  quick_keepX fs fk sx e h2 K = true.
Proof.
  intros fs fk sx e K h2 n HL. unfold quick_keepX2, quick_keepX.
  assert (QA : forall kb kk len, quick_apartX2 fs fk sx e (emask_of fs fk kb kk len h2 (se_sds e)) kb kk len h2 = true ->
                                 quick_apartX fs fk sx e kb kk len h2 = true).
  { intros kb kk len. unfold quick_apartX2, quick_apartX, dxm_of.
    destruct (thr_test (se_thr e) kk h2); [reflexivity|].
    match goal with |- (if ?a then _ else _) = true -> _ => destruct a eqn:X end.
    - intros _. rewrite (exists_xk2_imp _ _ _ _ _ _ _ _ _ _ _ _ X). reflexivity.
    - intros H. match goal with |- (if ?a then _ else _) = true => destruct a end; [reflexivity | exact H]. }
  destruct K as [[kb kk] w2 v|[kb kk] len|[kb kk] len bk|lo hi|ee m|ee lo hi|[eb ek] en|c1 m1 c2 m2]; try (intros; assumption);
    cbn [klen_sym kkey kx_off] in *.
  - destruct len as [l0| | | | | | |]; try (intros; assumption); injection HL as <-;
      (destruct (expr_eqb kb (a_base (sx_wa sx))); [intros H; exact H | apply QA]).
  - destruct len as [l0| | | | | | |]; try (intros; assumption); injection HL as <-;
      (destruct (expr_eqb kb (a_base (sx_wa sx))); [intros H; exact H | apply QA]).
Qed.

Lemma first_failX2_sound : forall fk b2 gb K n h2 sxs ents,
  Forall (sx_wf fk) sxs -> ents_ok fk b2 gb sxs ents -> kkey K = Some b2 -> klen_sym K = Some n -> h2 = xhi fk n ->
  match first_failX2 (SFS fk) fk sxs ents
          (emask_of (SFS fk) fk b2 (kx_off K) n h2 (ci_sds (mk_ci (SFS fk) fk (kdisj_sides fk) b2))) h2 K with
  | None => PT fk sxs [K] = [K]
  | Some sfx => exists pre, sxs = pre ++ sfx /\ PT fk pre [K] = [K]
  end.
Proof.
  intros fk b2 gb K n h2 sxs ents Hwf Hents HK HL Hh.
  induction Hents as [|sx c sr cr Hc Hents IH]; [reflexivity|].
  apply Forall_cons_iff in Hwf as [Hsx Hwf]. specialize (IH Hwf). cbn [first_failX2].
  match goal with |- context [if ?q then _ else _] => destruct q eqn:Q end.
  - assert (Q' : quick_keepX (SFS fk) fk sx (ce_sei c) h2 K = true).
    { apply (quick_keepX2_imp (SFS fk) fk sx (ce_sei c) K h2 n HL). rewrite HK.
      destruct Hc as (He & _). rewrite He at 2. cbn [mk_sei se_sds]. exact Q. }
    pose proof (quick_keepX_sound fk sx c b2 gb K n h2 Hsx Hc HK HL Hh Q') as HP.
    rewrite PT_cons_keep by exact HP.
    match goal with |- match ?ff with _ => _ end => destruct ff as [sfx|] end; [|exact IH].
    destruct IH as [pre [E1 E2]]. exists (sx :: pre). split; [rewrite E1; reflexivity|].
    rewrite PT_cons_keep by exact HP. exact E2.
  - exists []. split; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma skipn_sums_of : forall i sxs ents cids,
  length ents = length sxs -> length cids = length sxs -> (i <= length sxs)%nat ->
  skipn i (sums_of sxs ents cids) = sums_of (skipn i sxs) (skipn i ents) (skipn i cids).
Proof.
  induction i as [|i IH]; intros sxs ents cids H1 H2 Hi; [reflexivity|].
  destruct sxs as [|sx sr]; [cbn [length] in Hi; lia|].
  destruct ents as [|c cr]; [discriminate|]. destruct cids as [|cid ir]; [discriminate|].
  cbn [length] in *. cbn [sums_of skipn]. apply IH; lia.
Qed.

Lemma cids_of_length : forall sxs tbl nxt, length (cids_of sxs tbl nxt) = length sxs.
Proof.
  induction sxs as [|sx r IH]; intros tbl nxt; [reflexivity|]. cbn [cids_of].
  destruct (cid_of tbl (a_base (sx_wa sx)) nxt) as [[p tbl'] n']. cbn [length]. rewrite IH. reflexivity.
Qed.

(* [comment removed for export] *)
Definition vt_ok (fk : list kentry) (sxs : list stctx) (gbt : list (expr * Z * Z)) (vt : vtables) : Prop :=
  vt_fk vt = fk /\ pcc_ok fk (vt_cc vt) /\ vt_sxs vt = sxs /\ vt_gb vt = gbt
  /\ (forall b col, alookup (vt_cols vt) b = Some col ->
        col = column_of sxs b (mk_ci (SFS fk) fk (kdisj_sides fk) b) (group_bounds gbt b)).

Lemma vt_col_ok : forall fk sxs gbt vt b2,
  vt_ok fk sxs gbt vt ->
  fst (vt_col vt b2) = column_of sxs b2 (mk_ci (SFS fk) fk (kdisj_sides fk) b2) (group_bounds gbt b2)
  /\ vt_ok fk sxs gbt (snd (vt_col vt b2)).
Proof.
  intros fk sxs gbt vt b2 (Hfk & Hcc & Hsxs & Hgb & Hcols). unfold vt_col.
  destruct (alookup (vt_cols vt) b2) as [col|] eqn:L.
  - split; [exact (Hcols _ _ L)|]. exact (conj Hfk (conj Hcc (conj Hsxs (conj Hgb Hcols)))).
  - rewrite Hfk. pose proof (cc_get_ok fk (vt_cc vt) b2 Hcc) as [G1 G2].
    destruct (cc_get fk (vt_cc vt) b2) as [ci2 cc']. cbn [fst snd] in G1, G2 |- *. subst ci2. rewrite Hsxs, Hgb.
    split; [reflexivity|]. split; [reflexivity|]. split; [exact G2|]. split; [reflexivity|]. split; [reflexivity|].
    cbn [vt_cols]. intros b col. rewrite alookup_cons. destruct (expr_eqb b b2) eqn:E.
    + intros H. injection H as <-. apply p5_expr_eqb_eq in E. subst b. reflexivity.
    + apply Hcols.
Qed.

Lemma Forall2_skipn : forall (A B : Type) (R : A -> B -> Prop) i l1 l2,
  Forall2 R l1 l2 -> Forall2 R (skipn i l1) (skipn i l2).
Proof.
  intros A B R i. induction i as [|i IH]; intros l1 l2 H; [exact H|].
  destruct H; cbn [skipn]; [constructor | apply IH; assumption].
Qed.

Lemma Forall_skipn' : forall (A : Type) (P : A -> Prop) i l, Forall P l -> Forall P (skipn i l).
Proof.
  intros A P i. induction i as [|i IH]; intros l H; [exact H|]. destruct H; cbn [skipn]; [constructor | apply IH; assumption].
Qed.

Lemma Forall_app_inv_r : forall (A : Type) (P : A -> Prop) l1 l2, Forall P (l1 ++ l2) -> Forall P l2.
Proof. intros A P l1 l2 H. apply Forall_app in H as [_ H]. exact H. Qed.

Lemma entryV_eq : forall fk sxs gbt vt orig i b2 K,
  vt_ok fk sxs gbt vt -> Forall (sx_wf fk) sxs -> kkey K = Some b2 ->
  fst (entryV vt orig i b2 K) = PT fk (skipn i sxs) [K] /\ vt_ok fk sxs gbt (snd (entryV vt orig i b2 K)).
Proof.
  intros fk sxs gbt vt orig i b2 K Hvt Hwf HK. unfold entryV.
  pose proof (vt_col_ok fk sxs gbt vt b2 Hvt) as [Hcol Hvt1].
  destruct (vt_col vt b2) as [col vt1]. cbn [fst snd] in Hcol, Hvt1.
  pose proof (column_of_ok fk sxs b2 (group_bounds gbt b2)) as CO. cbv zeta in CO. rewrite <- Hcol in CO.
  destruct CO as (Hents & Hall & Hgb).
  destruct Hvt1 as (Hfk & Hcc & Hsxs & Hgbt & Hcols). rewrite Hfk, Hsxs.
  assert (Hfs : cc_fs (vt_cc vt1) = SFS fk) by exact (proj2 (proj1 Hcc)).
  assert (SFX : forall pre sfx, skipn i sxs = pre ++ sfx -> PT fk pre [K] = [K] ->
            pieces_through fk (vt_cc vt1) sfx [K] = PT fk (skipn i sxs) [K]).
  { intros pre sfx E1 E2. rewrite E1, PT_app, E2. apply pieces_through_eq; [exact Hcc|].
    apply (Forall_app_inv_r _ _ pre). rewrite <- E1. apply Forall_skipn'. exact Hwf. }
  destruct (klen_sym K) as [n|] eqn:HL.
  - pose proof (xh_get_ok fk (vt_cc vt1) n Hcc) as [Xh Xcc].
    destruct (xh_get fk (vt_cc vt1) n) as [h2 cc2]. cbn [fst snd] in Xh, Xcc |- *.
    assert (Hfs2 : cc_fs cc2 = SFS fk) by exact (proj2 (proj1 Xcc)). rewrite Hfs2.
    cbn [vt_fk vt_cc vt_sxs vt_gb vt_cols].
    assert (Hsds : co_sds col = ci_sds (mk_ci (SFS fk) fk (kdisj_sides fk) b2)) by (rewrite Hcol; reflexivity).
    rewrite Hsds.
    pose proof (first_failX2_sound fk b2 (group_bounds gbt b2) K n h2 (skipn i sxs) (skipn i (co_ents col))
                  (Forall_skipn' _ _ i _ Hwf) (Forall2_skipn _ _ _ i _ _ Hents) HK HL Xh) as FF.
    match goal with |- context [first_failX2 ?a ?b ?c ?d ?e ?f ?g] => destruct (first_failX2 a b c d e f g) as [sfx|] end.
    + destruct FF as [pre [E1 E2]]. cbn [fst snd]. split.
      * rewrite E1, PT_app, E2. apply pieces_through_eq; [exact Xcc|].
        apply (Forall_app_inv_r _ _ pre). rewrite <- E1. apply Forall_skipn'. exact Hwf.
      * split; [reflexivity|]. split; [exact Xcc|]. split; [reflexivity|]. split; [exact Hgbt|]. exact Hcols.
    + cbn [fst snd]. split; [symmetry; exact FF|].
      split; [reflexivity|]. split; [exact Xcc|]. split; [reflexivity|]. split; [exact Hgbt|]. exact Hcols.
  - rewrite Hfs.
    set (useall := if orig then in_group col K else false).
    assert (HU : useall = true -> exists gl gh lo hi, group_bounds gbt b2 = Some (gl, gh) /\ klit K = Some (b2, lo, hi) /\ gl <= lo /\ hi <= gh).
    { subst useall. destruct orig; [|discriminate]. unfold in_group. rewrite Hgb.
      destruct (group_bounds gbt b2) as [[gl gh]|]; [|discriminate].
      destruct (klit K) as [[[b lo] hi]|] eqn:HKl; [|discriminate].
      pose proof (klit_kkey K b lo hi HKl) as Kb. rewrite HK in Kb. injection Kb as ->.
      destruct (Z.leb_spec gl lo); [|discriminate]. destruct (Z.leb_spec hi gh); [|discriminate].
      intros _. exists gl, gh, lo, hi. repeat split; assumption || reflexivity. }
    assert (VT1 : vt_ok fk sxs gbt vt1) by exact (conj Hfk (conj Hcc (conj Hsxs (conj Hgbt Hcols)))).
    destruct (if useall then match i with O => co_all col | S _ => false end else false) eqn:C.
    + cbn [fst snd]. split; [|exact VT1].
      destruct useall; [|discriminate]. destruct i; [|discriminate]. cbn [skipn]. symmetry. apply PT_keep.
      destruct (HU eq_refl) as (gl & gh & lo & hi & Hgb2 & HKl & H1 & H2).
      pose proof (Hall C) as HA. clear -Hents HA Hwf HKl H1 H2 Hgb2.
      induction Hents as [|sx c sr cr Hc Hents IH]; [constructor|].
      apply Forall_cons_iff in Hwf as [Hsx Hwf]. apply Forall_cons_iff in HA as [Ha HA].
      constructor; [|exact (IH Hwf HA)].
      apply (group_all_sound fk sx c b2 (group_bounds gbt b2) K gl gh lo hi Hsx Hc); [|exact HKl|exact H1|exact H2].
      rewrite <- Hgb2. exact (proj1 (proj2 Hc) Ha).
    + assert (E2 : Forall2 (ent_ok2 fk b2 (group_bounds gbt b2)) sxs (co_ents col)) by (rewrite Hcol; apply column_of_ok2).
      assert (Hsums : co_sums col = sums_of sxs (co_ents col) (co_cids col)) by (rewrite Hcol; reflexivity).
      assert (Hcids : length (co_cids col) = length sxs) by (rewrite Hcol; cbn [column_of co_cids]; apply cids_of_length).
      assert (Hlen : length (co_ents col) = length sxs) by (symmetry; exact (Forall2_length E2)).
      destruct (Nat.le_gt_cases i (length sxs)) as [Hi|Hi].
      * pose proof (first_failH_sound fk b2 (group_bounds gbt b2) K useall
                      (verdicts (SFS fk) fk (hd [] (skipn i (co_sums col))) useall b2 K)
                      (skipn i sxs) (skipn i (co_ents col)) (skipn i (co_cids col))
                      (Forall_skipn' _ _ i _ Hwf) (Forall2_skipn _ _ _ i _ _ E2) HK HL HU) as FF.
        rewrite Hsums, (skipn_sums_of i sxs (co_ents col) _ Hlen Hcids Hi) in FF |- *.
        specialize (FF (verdicts_ok _ _ _ _ _ _)).
        match goal with |- context [first_failH ?a ?b ?c ?d ?e ?f ?g ?h ?k] => destruct (first_failH a b c d e f g h k) as [sfx|] end.
        -- destruct FF as [pre [E1 E2']]. cbn [fst snd]. split; [|exact VT1].
           destruct sfx as [|sx sr]; [rewrite E1, app_nil_r; symmetry; exact E2'|].
           destruct (kdead sx K) eqn:KD; [|exact (SFX pre (sx :: sr) E1 E2')].
           rewrite E1, PT_app, E2'. cbn [PT flat_map]. rewrite (kdead_P1 fk sx K KD). cbn [app]. symmetry. apply PT_nil.
        -- cbn [fst snd]. split; [symmetry; exact FF | exact VT1].
      * assert (Es : skipn i sxs = []) by (apply skipn_all2; lia). rewrite Es. cbn [first_failH fst snd PT]. split; [reflexivity | exact VT1].
Qed.

Lemma chainsV_eq : forall fk sxs gbt vt l,
  vt_ok fk sxs gbt vt -> Forall (sx_wf fk) sxs ->
  chainsV vt l = PT fk sxs l.
Proof.
  intros fk sxs gbt vt l Hvt Hwf. rewrite PT_flat_map. revert vt Hvt.
  induction l as [|K rest IH]; intros vt Hvt; [reflexivity|]. cbn [chainsV flat_map]. unfold chainV.
  destruct (kkey K) as [b2|] eqn:HK.
  - pose proof (entryV_eq fk sxs gbt vt true 0 b2 K Hvt Hwf HK) as [E V].
    destruct (entryV vt true 0 b2 K) as [ps vt']. cbn [fst snd skipn] in E, V. rewrite E, (IH vt' V). reflexivity.
  - rewrite (IH vt Hvt). rewrite PT_keep; [reflexivity|]. apply Forall_forall. intros sx _. apply P1_fact. exact HK.
Qed.

Lemma skipn_S_of : forall (A : Type) j (l : list A) x r, skipn j l = x :: r -> skipn (S j) l = r.
Proof.
  intros A j. induction j as [|j IH]; intros l x r H.
  - change (skipn 0 l) with l in H. subst l. reflexivity.
  - destruct l as [|y l']; [discriminate|]. change (skipn (S j) (y :: l')) with (skipn j l') in H.
    change (skipn (S (S j)) (y :: l')) with (skipn (S j) l'). exact (IH l' x r H).
Qed.

Lemma stores_partV_eq : forall fk sxs gbt vt j sfx,
  vt_ok fk sxs gbt vt -> Forall (sx_wf fk) sxs -> skipn j sxs = sfx ->
  fst (stores_partV vt (S j) sfx) = SPspec fk sfx /\ vt_ok fk sxs gbt (snd (stores_partV vt (S j) sfx)).
Proof.
  intros fk sxs gbt vt j sfx Hvt Hwf. revert vt j Hvt.
  induction sfx as [|sx newer IH]; intros vt j Hvt Hj; [exact (conj eq_refl Hvt)|].
  cbn [stores_partV SPspec].
  pose proof (skipn_S_of _ j sxs sx newer Hj) as Hj'.
  destruct (IH vt (S j) Hvt Hj') as [E1 V1].
  destruct (stores_partV vt (S (S j)) newer) as [r_newer vt1]. cbn [fst snd] in E1, V1.
  pose proof (entryV_eq fk sxs gbt vt1 false (S j) (a_base (sx_wa sx)) (KWord (sx_wa sx) (sx_w sx) (sx_wv sx)) V1 Hwf
                ltac:(destruct (sx_wa sx); reflexivity)) as [E2 V2].
  destruct (entryV vt1 false (S j) (a_base (sx_wa sx)) (KWord (sx_wa sx) (sx_w sx) (sx_wv sx))) as [r_i vt2].
  cbn [fst snd] in E2, V2 |- *. rewrite E1, E2, Hj'. exact (conj eq_refl V2).
Qed.

Theorem carryV_eq : forall log kn,
  let fk := facts_of kn in
  carryV log kn = SPspec fk (map (sx_of fk) (rev log)) ++ PT fk (map (sx_of fk) (rev log)) kn.
Proof.
  intros log kn fk. unfold carryV. fold fk.
  assert (H0 : pcc_ok fk (CC (kdisj_sdis (SFS fk) fk fk) (SFS fk) [] [])).
  { split; [split; reflexivity|]. split; intros ? ? H; discriminate. }
  pose proof (stctxs_of_eq fk log _ H0) as [E1 Hcc].
  destruct (stctxs_of fk (CC (kdisj_sdis (SFS fk) fk fk) (SFS fk) [] []) log) as [sxs cc]. cbn [fst snd] in E1, Hcc.
  assert (Hwf : Forall (sx_wf fk) sxs).
  { rewrite E1. apply Forall_forall. intros sx Hin. apply in_map_iff in Hin as [e [<- _]]. apply sx_of_wf. }
  assert (VT0 : vt_ok fk sxs (bounds_acc kn None []) (VT fk cc sxs (bounds_acc kn None []) [])).
  { split; [reflexivity|]. split; [exact Hcc|]. split; [reflexivity|]. split; [reflexivity|]. intros b col H. discriminate. }
  pose proof (stores_partV_eq fk sxs _ _ 0 sxs VT0 Hwf eq_refl) as [E2 V2].
  destruct (stores_partV (VT fk cc sxs (bounds_acc kn None []) []) 1 sxs) as [sp vt]. cbn [fst snd] in E2, V2.
  rewrite E2, (chainsV_eq fk sxs _ vt kn V2 Hwf), E1. reflexivity.
Qed.

Theorem carry_eq : forall log kn hints, carry log kn hints = carry_ref log kn hints.
Proof.
  intros log kn hints. unfold carry.
  destruct log as [|e older]; [reflexivity|].
  destruct hints as [|h hs]; [|apply carry_p5_eq].
  pose proof (carry_ref_nil (e :: older) kn) as R. cbv zeta in R. rewrite R.
  rewrite carryV_eq. reflexivity.
Qed.
End FPW_6.


End SX2.
