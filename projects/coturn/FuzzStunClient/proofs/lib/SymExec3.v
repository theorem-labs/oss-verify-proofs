(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import PropExec CatExec CatSim SeqExec StoreOk SymExec.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import RomFast.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Unset Lia Cache.
#[local] Existing Instance PropExec.fx0.  (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.

Module SX2.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Inductive expr : Type :=
| ELit  (z : Z)                              (* [comment removed for export] *)
| EVar  (n : N)                              (* [comment removed for export] *)
| EAlu  (op : aluop) (a b : expr)            (* [comment removed for export] *)
| EAluw (op : aluop) (a b : expr)            (* [comment removed for export] *)
| EMd   (op : mulop) (a b : expr)            (* [comment removed for export] *)
| EMdw  (op : mulop) (a b : expr)            (* [comment removed for export] *)
| EExt  (sx : bool) (lo n : nat) (e : expr)  (* [comment removed for export] *)
| EBlob (sx : bool) (k : nat) (i : Z) (n : nat).
                                             (* [comment removed for export] *)
Arguments EVar _%_N_scope.
(* [comment removed for export] *)

(* [comment removed for export] *)
Record env : Type := Env { ev : N -> word; eb : nat -> list byte }.

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
  | EVar a, EVar b => N.eqb a b
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
      | H : N.eqb _ _ = true |- _ => apply N.eqb_eq in H
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
  | EVar a, EVar b => N.compare a b
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
(* [comment removed for export] *)
Lemma swrap_small : forall n u h m, m = (2 ^ Z.of_N n)%Z -> h = (m / 2)%Z -> (0 <= u < m)%Z -> (0 < n)%N ->
  bv_swrap n u = (if Z.ltb u h then u else (u - m)%Z).
Proof.
  intros n u h m Hm Hh Hu Hn. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. rewrite <- Hm, <- Hh.
  assert (Hm2 : m = (2 * h)%Z).
  { subst h. rewrite Hm. replace (Z.of_N n) with (Z.succ (Z.of_N n - 1)) by lia. rewrite Z.pow_succ_r by lia.
    rewrite Z.mul_comm, Z.div_mul by lia. lia. }
  destruct (Z.ltb_spec u h).
  - rewrite Z.mod_small by lia. lia.
  - rewrite <- (Z.mod_add _ (-1)) by lia. rewrite Z.mod_small by lia. lia.
Qed.
Lemma zmod64_bv : forall z, zmod64 z = bv_unsigned (Z_to_bv 64 z).
Proof. intros z. rewrite zmod64_eq, Z_to_bv_unsigned. reflexivity. Qed.

(* [comment removed for export] *)
Definition zext_litF (sx : bool) (lo n : nat) (x : Z) : Z :=
  if (Nat.leb 1 n && Nat.leb n 8)%bool then
    let nb := (8 * Z.of_nat n)%Z in
    let u := zmodp (zdivp (zmod64 x) (8 * Z.of_nat lo)) nb in
    if sx then (if Z.ltb u (zpow2 (nb - 1)) then u else (u - zpow2 nb + two64)%Z) else u
  else zext_lit sx lo n x.
Lemma zext_litF_eq : forall sx lo n x, zext_litF sx lo n x = zext_lit sx lo n x.
Proof.
  intros sx lo n x. unfold zext_litF.
  destruct (Nat.leb 1 n && Nat.leb n 8)%bool eqn:Hn; [|reflexivity].
  apply andb_prop in Hn as [H1 H8]. apply Nat.leb_le in H1. apply Nat.leb_le in H8.
  unfold zext_lit, ext_val, ext_Z.
  rewrite Z_to_bv_unsigned, <- !zmod64_bv. rewrite zmodp_eq, zdivp_eq, !zpow2_eq.
  set (u := ((zmod64 x / 2 ^ (8 * Z.of_nat lo)) mod 2 ^ (8 * Z.of_nat n))%Z).
  assert (Hu : (0 <= u < 2 ^ (8 * Z.of_nat n))%Z) by (subst u; apply Z.mod_pos_bound; lia).
  assert (Hpow : (2 ^ (8 * Z.of_nat n) <= 2 ^ 64)%Z) by (apply Z.pow_le_mono_r; lia).
  clearbody u. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64)%Z with (2 ^ 64)%Z.
  destruct sx.
  - assert (Hh : (2 ^ (8 * Z.of_nat n) = 2 * 2 ^ (8 * Z.of_nat n - 1))%Z).
    { replace (8 * Z.of_nat n)%Z with (Z.succ (8 * Z.of_nat n - 1)) at 1 by lia. rewrite Z.pow_succ_r by lia. reflexivity. }
    rewrite (swrap_small (8 * N.of_nat n) u (2 ^ (8 * Z.of_nat n - 1)) (2 ^ (8 * Z.of_nat n))); try lia.
    unfold two64.
    destruct (Z.ltb_spec u (2 ^ (8 * Z.of_nat n - 1))).
    + rewrite Z.mod_small by lia. reflexivity.
    + rewrite <- (Z.mod_add _ 1) by lia. rewrite Z.mod_small by lia. lia.
  - rewrite Z.mod_small by lia. reflexivity.
Qed.

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
Definition mkExtF (sx : bool) (lo n : nat) (e : expr) : expr :=
  match e with
  | ELit x => ELit (zext_litF sx lo n x)
  | _ =>
    if (Nat.eqb lo 0 && Nat.eqb n 8)%bool then e
    else match e with
         | EExt false lo' n' e' =>
             if (Nat.leb (lo + n) n' && Nat.leb n' 8)%bool then EExt sx (lo' + lo) n e'
             else EExt sx lo n e
         | _ => EExt sx lo n e
         end
  end.
Lemma mkExtF_eq : forall sx lo n e, mkExtF sx lo n e = mkExt sx lo n e.
Proof. intros. unfold mkExtF, mkExt. destruct e; rewrite ?zext_litF_eq; reflexivity. Qed.


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
  s_next : N                  (* [comment removed for export] *)
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
Definition rel_lit2 (rb : expr) (rk re : Z) (kb : expr) (kk ke : Z) : rangerel :=
  if expr_eqb rb kb then
    if Z.leb kk rk then
      (if Z.leb re ke then RInside (rk - kk)
       else if Z.leb re kk then RDisjoint else if Z.leb ke rk then RDisjoint else RPartial)
    else (if Z.leb re kk then RDisjoint else if Z.leb ke rk then RDisjoint else RPartial)
  else RUnknown.
Lemma rel_lit2_eq : forall rb rk rn kb kk kn, rel_lit2 rb rk (rk + rn) kb kk (kk + kn) = rel_lit rb rk rn kb kk kn.
Proof.
  intros. unfold rel_lit2, rel_lit. destruct (expr_eqb rb kb); [|reflexivity].
  destruct (Z.leb kk rk), (Z.leb (rk + rn) (kk + kn)), (Z.leb (rk + rn) kk), (Z.leb (kk + kn) rk); reflexivity.
Qed.

(* [comment removed for export] *)
Lemma rel_lit2_guard rb rk re kb kk ke : (if expr_eqb rb kb then rel_lit2 rb rk re kb kk ke else RUnknown) = rel_lit2 rb rk re kb kk ke.
Proof. unfold rel_lit2. destruct (expr_eqb rb kb); reflexivity. Qed.

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
Ltac zhyg_in H := rewrite ?zmodp_6, ?zmodp_5, ?zmod64_eq2, ?zdiv64_eq2, ?zpow2_eq, ?zdivp_eq, ?zmulp_eq, ?zmodp_eq in H.
Ltac zhyg := rewrite ?zmodp_6, ?zmodp_5, ?zmod64_eq2, ?zdiv64_eq2, ?zpow2_eq, ?zdivp_eq, ?zmulp_eq, ?zmodp_eq.

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
Global Opaque erange_fuel.
(* [comment removed for export] *)
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
Fixpoint mentions_var (v : N) (e : expr) : bool :=
  match e with
  | ELit _ => false
  | EVar w => N.eqb v w
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
Inductive ptree (A : Type) : Type := PTLeaf | PTNode (l : ptree A) (o : option A) (r : ptree A).
Arguments PTLeaf {A}. Arguments PTNode {A} _ _ _.
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


(* [comment removed for export] *)
Definition nm_get {A : Type} (t : ptree A) (n : N) : option A := pt_get t (N.succ_pos n).
Definition nm_set {A : Type} (t : ptree A) (n : N) (v : A) : ptree A := pt_set (N.succ_pos n) v t.
Lemma succ_pos_inj : forall n n', N.succ_pos n = N.succ_pos n' -> n = n'.
Proof.
  intros n n' H. apply N.succ_inj. rewrite <- !N.succ_pos_spec. rewrite H. reflexivity.
Qed.
Lemma nm_get_set_same : forall (A : Type) (t : ptree A) n v, nm_get (nm_set t n v) n = Some v.
Proof. intros. unfold nm_get, nm_set. apply pt_gss. Qed.
Lemma nm_get_leaf : forall (A : Type) n, nm_get (@PTLeaf A) n = None.
Proof. intros. unfold nm_get. apply pt_get_leaf. Qed.
Lemma nm_get_set_other : forall (A : Type) (t : ptree A) n n' v, n <> n' -> nm_get (nm_set t n' v) n = nm_get t n.
Proof.
  intros A t n n' v Hne. unfold nm_get, nm_set. apply pt_gso. intros H. apply Hne. apply succ_pos_inj. exact H.
Qed.

Record fdig : Type := FD {
  fd_sf : list sfact;                 (* [comment removed for export] *)
  fd_rv : ptree (Z * Z);              (* [comment removed for export] *)
  fd_rc : list (expr * (Z * Z));      (* [comment removed for export] *)
  fd_av : ptree Z;                    (* [comment removed for export] *)
  fd_ac : list (expr * Z) }.

Fixpoint mk_rv (kn : list kentry) : ptree (Z * Z) :=
  match kn with
  | [] => PTLeaf
  | KRange (EVar n) lo hi :: rest => nm_set (mk_rv rest) n (clampi (lo, hi))
  | _ :: rest => mk_rv rest
  end.
Fixpoint mk_rc (kn : list kentry) : list (expr * (Z * Z)) :=
  match kn with
  | [] => []
  | KRange (EVar _) _ _ :: rest => mk_rc rest
  | KRange e lo hi :: rest => (e, clampi (lo, hi)) :: mk_rc rest
  | _ :: rest => mk_rc rest
  end.
Fixpoint mk_av (kn : list kentry) : ptree Z :=
  match kn with
  | [] => PTLeaf
  | KAlign (EVar n) m :: rest => nm_set (mk_av rest) n m
  | _ :: rest => mk_av rest
  end.
Fixpoint mk_ac (kn : list kentry) : list (expr * Z) :=
  match kn with
  | [] => []
  | KAlign (EVar _) _ :: rest => mk_ac rest
  | KAlign e m :: rest => (e, m) :: mk_ac rest
  | _ :: rest => mk_ac rest
  end.
Fixpoint ea_lookup {A : Type} (l : list (expr * A)) (e : expr) : option A :=
  match l with
  | [] => None
  | (k, v) :: r => if expr_eqb e k then Some v else ea_lookup r e
  end.
Definition rt_find (fs : fdig) (e : expr) : option (Z * Z) :=
  match e with
  | EVar n => nm_get (fd_rv fs) n
  | _ => ea_lookup (fd_rc fs) e
  end.
Definition at_find (fs : fdig) (e : expr) : option Z :=
  match e with
  | EVar n => nm_get (fd_av fs) n
  | _ => ea_lookup (fd_ac fs) e
  end.

Lemma rt_find_mk : forall sf av ac kn e, rt_find (FD sf (mk_rv kn) (mk_rc kn) av ac) e = match find_range kn e with Some r => Some (clampi r) | None => None end.
Proof.
  intros sf av ac kn e. induction kn as [|K rest IH]; cbn [mk_rv mk_rc find_range].
  - unfold rt_find; cbn - [nm_get]. destruct e; try reflexivity. apply nm_get_leaf.
  - destruct K as [| | | | |e' lo hi| |]; try exact IH.
    cbn [rt_find fd_rv fd_rc] in IH.
    destruct e' as [z'|n'|o a b|o a b|o a b|o a b|s l w a|s k i w];
      (destruct e as [z|n|p a' b'|p a' b'|p a' b'|p a' b'|s' l' w' a'|s' k' i' w']; cbn [rt_find fd_rv fd_rc ea_lookup expr_eqb];
       try exact IH);
      first [ destruct (N.eq_dec n n') as [->|Hne];
                [ rewrite N.eqb_refl, nm_get_set_same; reflexivity | rewrite (proj2 (N.eqb_neq _ _) Hne), nm_get_set_other by exact Hne; exact IH ]
            | lazymatch goal with |- (if ?c then _ else _) = _ => destruct c; [reflexivity | exact IH] end ].
Qed.
Lemma at_find_mk : forall sf rv rc kn e, at_find (FD sf rv rc (mk_av kn) (mk_ac kn)) e = find_align kn e.
Proof.
  intros sf rv rc kn e. induction kn as [|K rest IH]; cbn [mk_av mk_ac find_align].
  - unfold at_find; cbn - [nm_get]. destruct e; try reflexivity. apply nm_get_leaf.
  - destruct K as [| | | |e' m| | |]; try exact IH.
    destruct e' as [z'|n'|o a b|o a b|o a b|o a b|s l w a|s k i w];
      (destruct e as [z|n|p a' b'|p a' b'|p a' b'|p a' b'|s' l' w' a'|s' k' i' w']; cbn [at_find fd_av fd_ac ea_lookup expr_eqb];
       try exact IH);
      try (cbn [at_find fd_av fd_ac] in IH; rewrite <- IH; reflexivity).
    cbn [at_find fd_av] in IH. destruct (N.eq_dec n n') as [->|Hne].
    + rewrite N.eqb_refl. apply nm_get_set_same.
    + rewrite (proj2 (N.eqb_neq _ _) Hne), nm_get_set_other by exact Hne. exact IH.
Qed.

Fixpoint erange_fT (fuel : nat) (fs : fdig) (e : expr) {struct fuel} : option (Z * Z) :=
  match fuel with
  | O => None
  | S fuel' =>
  let erange := erange_fT fuel' in
  match rt_find fs e with
  | Some r => Some r
  | None =>
  match (let l := lin_of e in
         if lin_trivial l then None
         else match lin_range (erange fs) (fst l) (snd l) with
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
          match erange fs a, erange fs b with
          | Some (al, ah), Some (bl, bh) =>
              if Z.ltb (ah + bh) two64 then Some ((al + bl)%Z, (ah + bh)%Z)
              else if Z.leb two64 (al + bl) then Some ((al + bl - two64)%Z, (ah + bh - two64)%Z)
              else None
          | _, _ => None
          end
      | ALU_SUB =>
          match erange fs a, erange fs b with
          | Some (al, ah), Some (bl, bh) =>
              if Z.leb bh al then Some ((al - bh)%Z, (ah - bl)%Z)
              else if Z.ltb ah bl then Some ((al - bh + two64)%Z, (ah - bl + two64)%Z)
              else None
          | _, _ => None
          end
      | ALU_AND =>
          (* [comment removed for export] *)
          match (match b, erange fs a with
                 | ELit m, Some (al, ah) =>
                     let m' := zmod64 m in
                     let j := Z.log2 (m' + 1) in
                     if (Z.eqb (m' + 1) (zpow2 j) && Z.leb (zdivp al j) (zdivp ah j) && Z.eqb (zdivp al j) (zdivp ah j))%bool
                     then Some (zmodp al j, zmodp ah j) else None
                 | _, _ => None
                 end) with
          | Some r => Some r
          | None =>
          match erange fs a, erange fs b with
          | Some (_, ah), Some (_, bh) => Some (0%Z, Z.min ah bh)
          | Some (_, ah), None => Some (0%Z, ah)
          | None, Some (_, bh) => Some (0%Z, bh)
          | None, None => None
          end
          end
      | ALU_OR =>
          match erange fs a, erange fs b with
          | Some (al, ah), Some (bl, bh) => Some (Z.max al bl, mask_cover (Z.max ah bh))
          | _, _ => None
          end
      | ALU_XOR =>
          match erange fs a, erange fs b with
          | Some (_, ah), Some (_, bh) => Some (0%Z, mask_cover (Z.max ah bh))
          | _, _ => None
          end
      | ALU_SRL =>
          match erange fs a, lit_shamt b with
          | Some (al, ah), Some s => Some (zdivp al s, zdivp ah s)
          | _, _ => None
          end
      | ALU_SRA =>
          match erange fs a, lit_shamt b with
          | Some (al, ah), Some s =>
              if Z.ltb ah two63z then Some (zdivp al s, zdivp ah s) else None
          | _, _ => None
          end
      | ALU_SLL =>
          match erange fs a, lit_shamt b with
          | Some (al, ah), Some s =>
              let ahs := zmulp ah s in
              if Z.ltb ahs two64 then Some (zmulp al s, ahs) else None
          | _, _ => None
          end
      | ALU_SLTU =>
          match erange fs a, erange fs b with
          | Some (al, ah), Some (bl, bh) =>
              if Z.ltb ah bl then Some (1%Z, 1%Z)
              else if Z.leb bh al then Some (0%Z, 0%Z) else Some (0%Z, 1%Z)
          | _, _ => Some (0%Z, 1%Z)
          end
      | ALU_SLT =>
          match erange fs a, erange fs b with
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
          match erange fs a, erange fs b with
          | Some (al, ah), Some (bl, bh) =>
              let bl' := if Z.eqb bl bh then zsigned64 bl else bl in
              let bh' := if Z.eqb bl bh then zsigned64 bh else bh in
              if (Z.leb 0 (al + bl') && Z.ltb (ah + bh') two31z)%bool
              then Some ((al + bl')%Z, (ah + bh')%Z) else None
          | _, _ => None
          end
      | ALU_SUB =>
          match erange fs a, erange fs b with
          | Some (al, ah), Some (bl, bh) =>
              if (Z.leb bh al && Z.ltb (ah - bl) two31z)%bool
              then Some ((al - bh)%Z, (ah - bl)%Z) else None
          | _, _ => None
          end
      | ALU_SLL =>
          match erange fs a, lit_shamt b with
          | Some (al, ah), Some s =>
              let s' := zmodp s 5 in
              let ahs := zmulp ah s' in
              if Z.ltb ahs two31z then Some (zmulp al s', ahs) else None
          | _, _ => None
          end
      | ALU_SRL =>
          match erange fs a, lit_shamt b with
          | Some (al, ah), Some s =>
              let s' := zmodp s 5 in
              if (Z.ltb ah two32z && (Z.ltb 0 s' || Z.ltb ah two31z))%bool
              then Some (zdivp al s', zdivp ah s') else None
          | _, _ => None
          end
      | ALU_SRA =>
          match erange fs a, lit_shamt b with
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
          match erange fs a, erange fs b with
          | Some (al, ah), Some (bl, bh) =>
              if (Z.leb 0 al && Z.leb 0 bl && Z.ltb (ah * bh) two64)%bool
              then Some ((al * bl)%Z, (ah * bh)%Z) else None
          | _, _ => None
          end
      | M_MULHU =>
          match erange fs a, erange fs b with
          | Some (al, ah), Some (bl, bh) =>
              if (Z.leb 0 al && Z.leb 0 bl)%bool
              then Some (zdiv64 (al * bl), zdiv64 (ah * bh)) else None
          | _, _ => None
          end
      | M_DIVU =>
          match erange fs a, b with
          | Some (al, ah), ELit d =>
              let d' := zmod64 d in
              if Z.ltb 0 d' then Some ((al / d')%Z, (ah / d')%Z) else None
          | _, _ => None
          end
      | M_REMU =>
          match erange fs a, b with
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
        match lo, erange fs a with
        | O, Some (al, ah) =>
            let w2 := zdivp w 1 in
            if (Z.leb 0 al && Z.ltb ah w2)%bool then Some (al, ah)
            else if (Nat.leb 1 n && Nat.leb n 8 && Z.leb w2 al && Z.ltb ah w)%bool
                 then Some ((two64 - w + al)%Z, (two64 - w + ah)%Z) else None
        | _, _ => None
        end
      else
        match lo, erange fs a with
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

Definition erangeT (fs : fdig) (e : expr) : option (Z * Z) := erange_fT erange_fuel fs e.
Definition base_rangeT (fs : fdig) (e : expr) : option (Z * Z) :=
  match e with ELit z => let v := zmod64 z in Some (v, v) | _ => erangeT fs e end.

Fixpoint ealign0T (fs : fdig) (e : expr) {struct e} : Z :=
  match at_find fs e with
  | Some m => if Z.ltb 0 m then ctz64 m else 0%Z
  | None =>
  match e with
  | ELit z => ctz64 (zmod64 z)
  | EAlu ALU_ADD a b => Z.min (ealign0T fs a) (ealign0T fs b)
  | EAlu ALU_SUB a b => Z.min (ealign0T fs a) (ealign0T fs b)
  | EAlu ALU_AND a b => Z.max (ealign0T fs a) (ealign0T fs b)
  | EAlu ALU_OR a b => Z.min (ealign0T fs a) (ealign0T fs b)
  | EAlu ALU_SLL a b =>
      match lit_shamt b with
      | Some s => Z.min (ealign0T fs a + s)%Z 64
      | None => 0%Z
      end
  | EMd M_MUL a b => Z.min (ealign0T fs a + ealign0T fs b)%Z 64
  | _ => 0%Z
  end
  end.
Definition ealignT (fs : fdig) (kn : list kentry) (e : expr) : Z := Z.max (ealign0T fs e) (pageup_align e).

Definition lin_nowrapT (fs : fdig) (e : expr) : bool :=
  let l := lin_of e in
  match lin_range (erangeT fs) (fst l) (snd l) with
  | Some (lo, hi) => (Z.leb 0 lo && Z.ltb hi two64)%bool
  | None => false
  end.

Fixpoint srl_expandT (fs : fdig) (kn : list kentry) (ts : list (Z * expr)) : Z * list (Z * expr) :=
  match ts with
  | [] => (0%Z, [])
  | (k, a) :: rest =>
      let '(c, ts') := srl_expandT fs kn rest in
      let keep := (c, lins_e k a ts') in
      match a with
      | EAlu ALU_SRL e (ELit s) =>
          let j := zmodp (zmod64 s) 6 in
          let m := zpow2 j in
          if (Z.eqb (zmodp k j) 0%Z && lin_nowrapT fs e)%bool then
            let q := zdivp k j in
            let le := lin_of e in
            if Z.leb j (ealignT fs kn e) then   (* [comment removed for export] *)
              ((c + q * fst le)%Z, fold_right (fun t acc => lins_e (q * fst t)%Z (snd t) acc) ts' (snd le))
            else
            ((c + q * fst le)%Z,
             lins_e (- q)%Z (srl_rem e m) (fold_right (fun t acc => lins_e (q * fst t)%Z (snd t) acc) ts' (snd le)))
          else keep
      | _ => keep
      end
  end.

(* [comment removed for export] *)
Definition lin_test_relF (fs : fdig) (kn : list kentry) (c : Z) (ts : list (Z * expr))
           (test : Z -> Z -> bool) : bool :=
  match fd_sf fs with
  | [] => false
  | sf =>
      match sum_subst sf ts 0 0 false with
      | (ts', (lo0, hi0), true) =>
          match lin_range (erangeT fs) c ts' with
          | Some (lo, hi) => test (lo + lo0)%Z (hi + hi0)%Z
          | None => false
          end
      | _ => false
      end
  end.

Definition lin_testF (fs : fdig) (kn : list kentry) (c : Z) (ts : list (Z * expr)) (test : Z -> Z -> bool) : bool :=
  match lin_range (erangeT fs) c ts with
  | Some (lo, hi) => if test lo hi then true else lin_test_relF fs kn c ts test
  | None => lin_test_relF fs kn c ts test
  end.

Definition lin_nowrapRF (fs : fdig) (kn : list kentry) (e : expr) : bool :=
  let l := lin_of e in
  let '(c2, t2) := srl_expandT fs kn (snd l) in
  lin_testF fs kn (fst l + c2)%Z t2 (fun lo hi => (Z.leb 0 lo && Z.ltb hi two64)%bool).

Fixpoint xt_nowrapF (fs : fdig) (kn : list kentry) (ts : xterms) : bool :=
  match ts with
  | [] => true
  | (e, _) :: r => if lin_nowrapRF fs kn e then xt_nowrapF fs kn r else false
  end.

Definition lin_ge0F (fs : fdig) (kn : list kentry) (pos neg : xterms) : bool :=
  if xt_nowrapF fs kn pos then
    if xt_nowrapF fs kn neg then
      let d := lsub_e (xt_lin pos) (xt_lin neg) in
      let c := (xt_const pos - xt_const neg)%Z in
      if lin_testF fs kn c d (fun lo _ => Z.leb 0 lo) then true
      else let '(c2, t2) := srl_expandT fs kn d in
           lin_testF fs kn (c + c2)%Z t2 (fun lo _ => Z.leb 0 lo)
    else false
  else false.

Definition lin_apart0F (fs : fdig) (kn : list kentry) (b1 : expr) (k1 n1 : Z) (b2 : expr) (k2 n2 : Z) : bool :=
  if lin_nowrapRF fs kn b1 then
    if lin_nowrapRF fs kn b2 then
      let l1 := lin_of b1 in let l2 := lin_of b2 in
      lin_testF fs kn (fst l2 + k2 - fst l1 - k1)%Z (lsub_e (snd l2) (snd l1))
                (fun lo hi => (Z.leb n1 lo || Z.leb hi (- n2))%bool)
    else false
  else false.
Definition lin_apartF (fs : fdig) (kn : list kentry) (b1 : expr) (k1 n1 : Z) (b2 : expr) (k2 n2 : Z) : bool :=
  if shares_var b1 b2 then lin_apart0F fs kn b1 k1 n1 b2 k2 n2 else false.

Definition lin_brangeF (fs : fdig) (kn : list kentry) (e : expr) : option (Z * Z) :=
  let l := lin_of e in
  match fd_sf fs with
  | [] => None
  | sf =>
      match sum_subst sf (snd l) 0 0 false with
      | (ts', (lo0, hi0), true) =>
          match lin_range (erangeT fs) (fst l) ts' with
          | Some (lo, hi) =>
              let lo' := (lo + lo0)%Z in let hi' := (hi + hi0)%Z in
              if (Z.leb 0 lo' && Z.ltb hi' two64)%bool then Some (lo', hi') else None
          | None => None
          end
      | _ => None
      end
  end.

Definition xloF (fs : fdig) (kn : list kentry) (e : expr) : option Z :=
  match e with
  | ELit z => Some (zlit64 z)
  | _ => match erangeT fs e with
         | Some (lo, _) => Some lo
         | None => match lin_brangeF fs kn e with Some (lo, _) => Some lo | None => None end
         end
  end.
Definition xhiF (fs : fdig) (kn : list kentry) (e : expr) : option Z :=
  match e with
  | ELit z => Some (zlit64 z)
  | _ => match erangeT fs e with
         | Some (_, hi) => Some hi
         | None => match lin_brangeF fs kn e with Some (_, hi) => Some hi | None => None end
         end
  end.

Definition xinside0F (fs : fdig) (kn : list kentry) (b1 : expr) (k1 : Z) (n1 : expr) (b2 : expr) (k2 : Z) (n2 : expr) : bool :=
  if lin_ge0F fs kn [(b1, k1)] [(b2, k2)] then lin_ge0F fs kn [(b2, k2); (n2, 0%Z)] [(b1, k1); (n1, 0%Z)] else false.
Definition xinside_numF (fs : fdig) (kn : list kentry) (b1 : expr) (k1 : Z) (n1 : expr) (b2 : expr) (k2 : Z) (n2 : expr) : bool :=
  match xloF fs kn b2, xhiF fs kn b2 with
  | Some lo2, Some hi2 =>
      if Z.eqb lo2 hi2 then
        match base_rangeT fs b1, xhiF fs kn n1, xloF fs kn n2 with
        | Some (lo1, hi1), Some h1, Some l2 => Z.leb (lo2 + k2) (lo1 + k1) && Z.leb (hi1 + k1 + h1) (lo2 + k2 + l2)
        | _, _, _ => false
        end
      else false
  | _, _ => false
  end.
Definition xinsideF (fs : fdig) (kn : list kentry) (b1 : expr) (k1 : Z) (n1 : expr) (b2 : expr) (k2 : Z) (n2 : expr) : bool :=
  if shares_var b1 b2 then xinside0F fs kn b1 k1 n1 b2 k2 n2
  else if novars b2 then xinside_numF fs kn b1 k1 n1 b2 k2 n2 else false.

Definition sub_itvF (fs : fdig) (allkn : list kentry) (b : expr) (k n : Z) (c : saddr) (m : expr) : bool :=
  if (if (expr_eqb b (a_base c) && Z.leb (a_off c) k)%bool then
        match xloF fs allkn m with Some ml => Z.leb (k + n) (a_off c + ml) | None => false end
      else false)
  then true
  else if (Z.leb 0 n && Z.ltb n two64)%bool then xinsideF fs allkn b k (ELit n) (a_base c) (a_off c) m else false.

Fixpoint kdisj_apartF (fs : fdig) (allkn kn : list kentry) (b1 : expr) (k1 n1 : Z) (b2 : expr) (k2 n2 : Z) : bool :=
  match kn with
  | [] => false
  | KDisj c1 m1 c2 m2 :: rest =>
      if (if sub_itvF fs allkn b1 k1 n1 c1 m1 then sub_itvF fs allkn b2 k2 n2 c2 m2 else false) then true
      else if (if sub_itvF fs allkn b1 k1 n1 c2 m2 then sub_itvF fs allkn b2 k2 n2 c1 m1 else false) then true
      else kdisj_apartF fs allkn rest b1 k1 n1 b2 k2 n2
  | _ :: rest => kdisj_apartF fs allkn rest b1 k1 n1 b2 k2 n2
  end.

Definition ranges_apartF (fs : fdig) (kn : list kentry) (b1 : expr) (k1 n1 : Z) (b2 : expr) (k2 n2 : Z) : bool :=
  if (match base_rangeT fs b1, base_rangeT fs b2 with
      | Some (lo1, hi1), Some (lo2, hi2) =>
          (Z.leb (hi1 + k1 + n1) (lo2 + k2) || Z.leb (hi2 + k2 + n2) (lo1 + k1))%bool
      | _, _ => false
      end) then true
  else if kdisj_apartF fs kn kn b1 k1 n1 b2 k2 n2 then true
  else lin_apartF fs kn b1 k1 n1 b2 k2 n2.

Definition sub_itv_xF (fs : fdig) (kn : list kentry) (b : expr) (k : Z) (n : expr) (c : saddr) (m : expr) : bool :=
  xinsideF fs kn b k n (a_base c) (a_off c) m.

Fixpoint kdisj_apart_xF (fs : fdig) (allkn kn : list kentry) (b1 : expr) (k1 : Z) (n1 : expr) (b2 : expr) (k2 : Z) (n2 : expr) : bool :=
  match kn with
  | [] => false
  | KDisj c1 m1 c2 m2 :: rest =>
      if (if sub_itv_xF fs allkn b1 k1 n1 c1 m1 then sub_itv_xF fs allkn b2 k2 n2 c2 m2 else false) then true
      else if (if sub_itv_xF fs allkn b1 k1 n1 c2 m2 then sub_itv_xF fs allkn b2 k2 n2 c1 m1 else false) then true
      else kdisj_apart_xF fs allkn rest b1 k1 n1 b2 k2 n2
  | _ :: rest => kdisj_apart_xF fs allkn rest b1 k1 n1 b2 k2 n2
  end.

Definition ranges_apart_xF (fs : fdig) (kn : list kentry) (b1 : expr) (k1 : Z) (n1 : expr) (b2 : expr) (k2 : Z) (n2 : expr) : bool :=
  match n1, n2 with
  | ELit z1, ELit z2 => ranges_apartF fs kn b1 k1 (zlit64 z1) b2 k2 (zlit64 z2)
  | _, _ =>
    if (match base_rangeT fs b1, base_rangeT fs b2, xhiF fs kn n1, xhiF fs kn n2 with
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
Fixpoint disj_sidesF (fs : fdig) (allkn kn : list kentry) (b1 : expr) (k1 n1 : Z) : list (saddr * expr) :=
  match kn with
  | [] => []
  | KDisj c1 m1 c2 m2 :: rest =>
      let r := disj_sidesF fs allkn rest b1 k1 n1 in
      let r1 := if sub_itvF fs allkn b1 k1 n1 c2 m2 then (c1, m1) :: r else r in
      if sub_itvF fs allkn b1 k1 n1 c1 m1 then (c2, m2) :: r1 else r1
  | _ :: rest => disj_sidesF fs allkn rest b1 k1 n1
  end.
Fixpoint in_sidesF (fs : fdig) (allkn : list kentry) (D : list (saddr * expr)) (b2 : expr) (k2 n2 : Z) : bool :=
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
Definition mk_lthr (fs : fdig) (b1 : expr) (k1 n1 : Z) : lthr :=
  match base_rangeT fs b1 with Some (lo1, hi1) => Some ((hi1 + k1 + n1)%Z, (lo1 + k1)%Z) | None => None end.
Definition lthr_test (t : lthr) (br2 : option (Z * Z)) (k2 n2 : Z) : bool :=
  match t, br2 with
  | Some (A, B), Some (lo2, hi2) => (Z.leb A (lo2 + k2) || Z.leb (hi2 + k2 + n2) B)%bool
  | _, _ => false
  end.
Lemma lthr_test_eq : forall fs b1 k1 n1 b2 k2 n2,
  lthr_test (mk_lthr fs b1 k1 n1) (base_rangeT fs b2) k2 n2 =
  match base_rangeT fs b1, base_rangeT fs b2 with
  | Some (lo1, hi1), Some (lo2, hi2) => (Z.leb (hi1 + k1 + n1) (lo2 + k2) || Z.leb (hi2 + k2 + n2) (lo1 + k1))%bool
  | _, _ => false
  end.
Proof. intros. unfold lthr_test, mk_lthr. destruct (base_rangeT fs b1) as [[lo1 hi1]|]; [reflexivity|]. destruct (base_rangeT fs b2) as [[? ?]|]; reflexivity. Qed.
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
Definition ranges_apart_restF (fs : fdig) (kn : list kentry) (D : list (saddr * expr)) (b1 : expr) (k1 n1 : Z)
           (b2 : expr) (k2 n2 : Z) : bool :=
  if in_sidesF fs kn D b2 k2 n2 then true else lin_apartF fs kn b1 k1 n1 b2 k2 n2.
Lemma ranges_apart_stagedF_eq : forall fs kn b1 k1 n1 b2 k2 n2,
  (if lthr_test (mk_lthr fs b1 k1 n1) (base_rangeT fs b2) k2 n2 then true
   else ranges_apart_restF fs kn (disj_sidesF fs kn kn b1 k1 n1) b1 k1 n1 b2 k2 n2) = ranges_apartF fs kn b1 k1 n1 b2 k2 n2.
Proof. intros. rewrite lthr_test_eq. unfold ranges_apart_restF, ranges_apartF. rewrite in_sidesF_disj. reflexivity. Qed.
(* [comment removed for export] *)
Fixpoint lbr_lookup (c : list (expr * option (Z * Z))) (b : expr) : option (option (Z * Z)) :=
  match c with
  | [] => None
  | (b', r) :: rest => if expr_eqb b b' then Some r else lbr_lookup rest b
  end.

(* [comment removed for export] *)
Fixpoint kdisj_pre2F (fs : fdig) (allkn kn : list kentry) (b2 : expr) (k2 n2 : Z) : list (bool * bool) :=
  match kn with
  | [] => []
  | KDisj c1 m1 c2 m2 :: rest => (sub_itvF fs allkn b2 k2 n2 c2 m2, sub_itvF fs allkn b2 k2 n2 c1 m1) :: kdisj_pre2F fs allkn rest b2 k2 n2
  | _ :: rest => kdisj_pre2F fs allkn rest b2 k2 n2
  end.
Fixpoint kdisj_apart_withF (fs : fdig) (allkn kn : list kentry) (pre : list (bool * bool)) (b1 : expr) (k1 n1 : Z) : bool :=
  match kn with
  | [] => false
  | KDisj c1 m1 c2 m2 :: rest =>
      match pre with
      | (fB, fD) :: pre' =>
          if (if fB then sub_itvF fs allkn b1 k1 n1 c1 m1 else false) then true
          else if (if fD then sub_itvF fs allkn b1 k1 n1 c2 m2 else false) then true
          else kdisj_apart_withF fs allkn rest pre' b1 k1 n1
      | [] => false
      end
  | _ :: rest => kdisj_apart_withF fs allkn rest pre b1 k1 n1
  end.
Lemma kdisj_apart_withF_eq : forall fs allkn kn b1 k1 n1 b2 k2 n2,
  kdisj_apart_withF fs allkn kn (kdisj_pre2F fs allkn kn b2 k2 n2) b1 k1 n1 = kdisj_apartF fs allkn kn b1 k1 n1 b2 k2 n2.
Proof.
  intros. induction kn as [|K rest IH]; [reflexivity|].
  destruct K as [| | | | | | |c1 m1 c2 m2]; cbn [kdisj_pre2F kdisj_apart_withF kdisj_apartF]; try exact IH.
  rewrite IH. destruct (sub_itvF fs allkn b2 k2 n2 c2 m2), (sub_itvF fs allkn b2 k2 n2 c1 m1),
    (sub_itvF fs allkn b1 k1 n1 c1 m1), (sub_itvF fs allkn b1 k1 n1 c2 m2); reflexivity.
Qed.
(* [comment removed for export] *)
Fixpoint kdisj_pre2_xF (fs : fdig) (allkn kn : list kentry) (b2 : expr) (k2 : Z) (n2 : expr) : list (bool * bool) :=
  match kn with
  | [] => []
  | KDisj c1 m1 c2 m2 :: rest => (sub_itv_xF fs allkn b2 k2 n2 c2 m2, sub_itv_xF fs allkn b2 k2 n2 c1 m1) :: kdisj_pre2_xF fs allkn rest b2 k2 n2
  | _ :: rest => kdisj_pre2_xF fs allkn rest b2 k2 n2
  end.
Fixpoint kdisj_apart_with_xF (fs : fdig) (allkn kn : list kentry) (pre : list (bool * bool)) (b1 : expr) (k1 : Z) (n1 : expr) : bool :=
  match kn with
  | [] => false
  | KDisj c1 m1 c2 m2 :: rest =>
      match pre with
      | (fB, fD) :: pre' =>
          if (if fB then sub_itv_xF fs allkn b1 k1 n1 c1 m1 else false) then true
          else if (if fD then sub_itv_xF fs allkn b1 k1 n1 c2 m2 else false) then true
          else kdisj_apart_with_xF fs allkn rest pre' b1 k1 n1
      | [] => false
      end
  | _ :: rest => kdisj_apart_with_xF fs allkn rest pre b1 k1 n1
  end.
Lemma kdisj_apart_with_xF_eq : forall fs allkn kn b1 k1 n1 b2 k2 n2,
  kdisj_apart_with_xF fs allkn kn (kdisj_pre2_xF fs allkn kn b2 k2 n2) b1 k1 n1 = kdisj_apart_xF fs allkn kn b1 k1 n1 b2 k2 n2.
Proof.
  intros. induction kn as [|K rest IH]; [reflexivity|].
  destruct K as [| | | | | | |c1 m1 c2 m2]; cbn [kdisj_pre2_xF kdisj_apart_with_xF kdisj_apart_xF]; try exact IH.
  rewrite IH. destruct (sub_itv_xF fs allkn b2 k2 n2 c2 m2), (sub_itv_xF fs allkn b2 k2 n2 c1 m1),
    (sub_itv_xF fs allkn b1 k1 n1 c1 m1), (sub_itv_xF fs allkn b1 k1 n1 c2 m2); reflexivity.
Qed.
Lemma xhiF_lit : forall fs kn z, xhiF fs kn (ELit z) = Some (zlit64 z).
Proof. reflexivity. Qed.
(* [comment removed for export] *)
Record slotpre : Type := SLP { sp_br2 : option (Z * Z); sp_lit : option Z; sp_h2 : option Z; sp_pre : list (bool * bool) }.
Definition mk_slotpre (fs : fdig) (kn : list kentry) (b2 : expr) (k2 : Z) (n2 : expr) : slotpre :=
  match n2 with
  | ELit z2 => SLP (base_rangeT fs b2) (Some (zlit64 z2)) None (kdisj_pre2F fs kn kn b2 k2 (zlit64 z2))
  | _ => SLP (base_rangeT fs b2) None (xhiF fs kn n2) (kdisj_pre2_xF fs kn kn b2 k2 n2)
  end.
(* [comment removed for export] *)
Definition ranges_apart_slotF (fs : fdig) (kn : list kentry) (br1 : option (Z * Z)) (b1 : expr) (k1 z1 : Z)
           (sp : slotpre) (b2 : expr) (k2 : Z) (n2 : expr) : bool :=
  match sp_lit sp with
  | Some m2 =>
      let n1 := zlit64 z1 in
      if (match br1, sp_br2 sp with
          | Some (lo1, hi1), Some (lo2, hi2) => if Z.leb (hi1 + k1 + n1) (lo2 + k2) then true else Z.leb (hi2 + k2 + m2) (lo1 + k1)
          | _, _ => false
          end) then true
      else if kdisj_apart_withF fs kn kn (sp_pre sp) b1 k1 n1 then true
      else lin_apartF fs kn b1 k1 n1 b2 k2 m2
  | None =>
      if (match br1, sp_br2 sp, sp_h2 sp with
          | Some (lo1, hi1), Some (lo2, hi2), Some h2 =>
              if Z.leb (hi1 + k1 + zlit64 z1) (lo2 + k2) then true else Z.leb (hi2 + k2 + h2) (lo1 + k1)
          | _, _, _ => false
          end) then true
      else if kdisj_apart_with_xF fs kn kn (sp_pre sp) b1 k1 (ELit z1) then true
      else if negb (shares_var b1 b2) then false
      else if lin_ge0F fs kn [(b2, k2)] [(b1, k1); (ELit z1, 0%Z)] then true
      else lin_ge0F fs kn [(b1, k1)] [(b2, k2); (n2, 0%Z)]
  end.
Lemma ranges_apart_slotF_eq : forall fs kn b1 k1 z1 b2 k2 n2,
  ranges_apart_slotF fs kn (base_rangeT fs b1) b1 k1 z1 (mk_slotpre fs kn b2 k2 n2) b2 k2 n2 = ranges_apart_xF fs kn b1 k1 (ELit z1) b2 k2 n2.
Proof.
  intros. unfold ranges_apart_slotF, mk_slotpre, ranges_apart_xF.
  destruct n2 as [z2|v| | | | | |]; cbn [sp_lit sp_br2 sp_h2 sp_pre];
    rewrite ?kdisj_apart_withF_eq, ?kdisj_apart_with_xF_eq, ?xhiF_lit.
  1: unfold ranges_apartF.
  all: destruct (base_rangeT fs b1) as [[lo1 hi1]|], (base_rangeT fs b2) as [[lo2 hi2]|]; try reflexivity.
  all: try (destruct (xhiF fs kn _) as [h2|]; try reflexivity).
  all: destruct (Z.leb (hi1 + k1 + zlit64 z1) (lo2 + k2)); reflexivity.
Qed.

(* [comment removed for export] *)
Definition SFS (kn : list kentry) : fdig := FD (sum_facts kn kn) (mk_rv kn) (mk_rc kn) (mk_av kn) (mk_ac kn).

Lemma lin_range_extT : forall f g, (forall a, f a = g a) -> forall c ts, lin_range f c ts = lin_range g c ts.
Proof.
  intros f g H c ts. induction ts as [|[k a] rest IH]; [reflexivity|]. cbn [lin_range]. rewrite H, IH. reflexivity.
Qed.
Lemma rt_find_eq : forall kn e, rt_find (SFS kn) e = match find_range kn e with Some r => Some (clampi r) | None => None end.
Proof. intros. apply rt_find_mk. Qed.
Lemma at_find_eq : forall kn e, at_find (SFS kn) e = find_align kn e.
Proof. intros. apply at_find_mk. Qed.
Lemma find_range_filter : forall kn e, find_range (List.filter is_factb kn) e = find_range kn e.
Proof. intros kn e. induction kn as [|K rest IH]; [reflexivity|]. destruct K; cbn; rewrite ?IH; reflexivity. Qed.
Lemma find_align_filter : forall kn e, find_align (List.filter is_factb kn) e = find_align kn e.
Proof. intros kn e. induction kn as [|K rest IH]; [reflexivity|]. destruct K; cbn; rewrite ?IH; reflexivity. Qed.
Lemma mk_rv_filter : forall kn, mk_rv (List.filter is_factb kn) = mk_rv kn.
Proof. induction kn as [|K rest IH]; [reflexivity|]. destruct K; cbn; rewrite ?IH; reflexivity. Qed.
Lemma mk_rc_filter : forall kn, mk_rc (List.filter is_factb kn) = mk_rc kn.
Proof. induction kn as [|K rest IH]; [reflexivity|]. destruct K; cbn; rewrite ?IH; reflexivity. Qed.
Lemma mk_av_filter : forall kn, mk_av (List.filter is_factb kn) = mk_av kn.
Proof. induction kn as [|K rest IH]; [reflexivity|]. destruct K; cbn; rewrite ?IH; reflexivity. Qed.
Lemma mk_ac_filter : forall kn, mk_ac (List.filter is_factb kn) = mk_ac kn.
Proof. induction kn as [|K rest IH]; [reflexivity|]. destruct K; cbn; rewrite ?IH; reflexivity. Qed.
Lemma erange_fT_eq : forall fuel kn e, erange_fT fuel (SFS kn) e = erange_f fuel kn e.
Proof.
  induction fuel as [|f IH]; intros kn e; [reflexivity|].
  cbn [erange_fT erange_f]. rewrite rt_find_eq, (lin_range_extT _ _ (IH kn)).
  destruct (find_range kn e) as [r|]; [reflexivity|].
  destruct e; rewrite ?IH; reflexivity.
Qed.
Lemma erange_f_filter : forall fuel kn e, erange_f fuel (List.filter is_factb kn) e = erange_f fuel kn e.
Proof.
  induction fuel as [|f IH]; intros kn e; [reflexivity|].
  cbn [erange_f]. rewrite find_range_filter, (lin_range_extT _ _ (IH kn)).
  destruct e; rewrite ?IH; reflexivity.
Qed.
Lemma erangeT_eq : forall kn e, erangeT (SFS kn) e = erange kn e.
Proof. intros. unfold erangeT, erange. rewrite erange_fT_eq, facts_of_filter, erange_f_filter. reflexivity. Qed.
Lemma erangeT_eq' : forall kn, forall e, erangeT (SFS kn) e = erange kn e.
Proof. exact erangeT_eq. Qed.
Lemma base_rangeT_eq : forall kn e, base_rangeT (SFS kn) e = base_range kn e.
Proof. intros kn e. unfold base_rangeT, base_range. rewrite erangeT_eq. reflexivity. Qed.
Lemma ealign0T_eq : forall kn e, ealign0T (SFS kn) e = ealign0 kn e.
Proof. intros kn e. induction e; cbn [ealign0T ealign0]; rewrite at_find_eq, ?IHe, ?IHe1, ?IHe2; reflexivity. Qed.
Lemma ealign0_filter : forall kn e, ealign0 (List.filter is_factb kn) e = ealign0 kn e.
Proof. intros kn e. induction e; cbn [ealign0]; rewrite find_align_filter, ?IHe, ?IHe1, ?IHe2; reflexivity. Qed.
Lemma ealignT_eq : forall kn e, ealignT (SFS kn) kn e = ealign kn e.
Proof. intros. unfold ealignT, ealign. rewrite ealign0T_eq, facts_of_filter, ealign0_filter. reflexivity. Qed.
Lemma lin_nowrapT_eq : forall kn e, lin_nowrapT (SFS kn) e = lin_nowrap kn e.
Proof. intros. unfold lin_nowrapT, lin_nowrap. rewrite (lin_range_extT _ _ (erangeT_eq' kn)). reflexivity. Qed.
Lemma srl_expandT_eq : forall kn ts, srl_expandT (SFS kn) kn ts = srl_expand kn ts.
Proof.
  intros kn ts. induction ts as [|[k a] rest IH]; [reflexivity|].
  cbn [srl_expandT srl_expand]. rewrite IH. destruct (srl_expand kn rest) as [c ts'].
  destruct a as [| |o e0 b0| | | | |]; try reflexivity. destruct o; try reflexivity. destruct b0; try reflexivity.
  rewrite lin_nowrapT_eq, ealignT_eq. reflexivity.
Qed.

Lemma lin_test_relF_eq : forall kn c ts test, lin_test_relF (SFS kn) kn c ts test = lin_test_rel kn c ts test.
Proof.
  intros. unfold lin_test_relF, lin_test_rel. replace (fd_sf (SFS kn)) with (sum_facts kn kn) by reflexivity.
  destruct (sum_facts kn kn) as [|f r]; [reflexivity|]. cbn beta iota.
  destruct (sum_subst (f :: r) ts 0 0 false) as [[ts' [lo0 hi0]] [|]]; [|reflexivity]. cbn beta iota.
  rewrite (lin_range_extT _ _ (erangeT_eq' kn)). reflexivity.
Qed.
Lemma lin_testF_eq : forall kn c ts test, lin_testF (SFS kn) kn c ts test = lin_test kn c ts test.
Proof. intros. unfold lin_testF, lin_test. rewrite !lin_test_relF_eq, (lin_range_extT _ _ (erangeT_eq' kn)). reflexivity. Qed.
Lemma lin_nowrapRF_eq : forall kn e, lin_nowrapRF (SFS kn) kn e = lin_nowrapR kn e.
Proof. intros. unfold lin_nowrapRF, lin_nowrapR. rewrite srl_expandT_eq. destruct (srl_expand kn (snd (lin_of e))). apply lin_testF_eq. Qed.
Lemma xt_nowrapF_eq : forall kn ts, xt_nowrapF (SFS kn) kn ts = xt_nowrap kn ts.
Proof.
  intros kn ts. induction ts as [|[e k] r IH]; [reflexivity|]. cbn [xt_nowrapF xt_nowrap].
  rewrite lin_nowrapRF_eq, IH. destruct (lin_nowrapR kn e); reflexivity.
Qed.
Lemma lin_ge0F_eq : forall kn pos neg, lin_ge0F (SFS kn) kn pos neg = lin_ge0 kn pos neg.
Proof.
  intros. unfold lin_ge0F, lin_ge0. rewrite !xt_nowrapF_eq, !lin_testF_eq, srl_expandT_eq.
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
Proof.
  intros. unfold lin_brangeF, lin_brange. replace (fd_sf (SFS kn)) with (sum_facts kn kn) by reflexivity.
  destruct (sum_facts kn kn) as [|f r]; [reflexivity|]. cbn beta iota.
  destruct (sum_subst (f :: r) (snd (lin_of e)) 0 0 false) as [[ts' [lo0 hi0]] [|]]; [|reflexivity]. cbn beta iota.
  rewrite (lin_range_extT _ _ (erangeT_eq' kn)). reflexivity.
Qed.
Lemma xloF_eq : forall kn e, xloF (SFS kn) kn e = xlo kn e.
Proof. intros. unfold xloF, xlo. rewrite erangeT_eq, lin_brangeF_eq. reflexivity. Qed.
Lemma xhiF_eq : forall kn e, xhiF (SFS kn) kn e = xhi kn e.
Proof. intros. unfold xhiF, xhi. rewrite erangeT_eq, lin_brangeF_eq. reflexivity. Qed.
Lemma xinside0F_eq : forall kn b1 k1 n1 b2 k2 n2, xinside0F (SFS kn) kn b1 k1 n1 b2 k2 n2 = xinside0 kn b1 k1 n1 b2 k2 n2.
Proof. intros. unfold xinside0F, xinside0. rewrite !lin_ge0F_eq. reflexivity. Qed.
Lemma xinside_numF_eq : forall kn b1 k1 n1 b2 k2 n2, xinside_numF (SFS kn) kn b1 k1 n1 b2 k2 n2 = xinside_num kn b1 k1 n1 b2 k2 n2.
Proof. intros. unfold xinside_numF, xinside_num. rewrite !xloF_eq, !xhiF_eq, base_rangeT_eq. reflexivity. Qed.
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
Proof. intros. unfold ranges_apartF, ranges_apart. rewrite !base_rangeT_eq, kdisj_apartF_eq, lin_apartF_eq. reflexivity. Qed.
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
  destruct n1, n2; rewrite ?ranges_apartF_eq, ?base_rangeT_eq, ?xhiF_eq, ?kdisj_apart_xF_eq, ?lin_ge0F_eq; reflexivity.
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
Proof. intros. unfold SFS. rewrite sum_facts_fk1, sum_facts_fk2, !facts_of_filter, mk_rv_filter, mk_rc_filter, mk_av_filter, mk_ac_filter. reflexivity. Qed.
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

(* [comment removed for export] *)
Lemma two64_bvwf : forall z, (if Z.leb 0 z then Z.ltb z two64 else false) = true -> BvWf 64 z.
Proof.
  intros z H. apply bv_wf_in_range. change (bv_modulus 64) with two64.
  destruct (Z.leb_spec 0 z); [|discriminate]. destruct (Z.ltb_spec z two64); [|discriminate]. unfold two64 in *. lia.
Qed.
Definition Z_to_bv64f (z : Z) : bv 64 :=
  match Sumbool.sumbool_of_bool (if Z.leb 0 z then Z.ltb z two64 else false) with
  | left H => @BV 64 z (two64_bvwf z H)
  | right _ => Z_to_bv 64 z
  end.
Lemma Z_to_bv64f_eq : forall z, Z_to_bv64f z = Z_to_bv 64 z.
Proof.
  intros z. unfold Z_to_bv64f. destruct (Sumbool.sumbool_of_bool _) as [H|H]; [|reflexivity].
  apply bv_eq. cbn [bv_unsigned]. rewrite Z_to_bv_unsigned. symmetry. apply bv_wrap_small.
  change (bv_modulus 64) with two64.
  assert (H1 : (0 <= z)%Z) by (destruct (Z.leb_spec 0 z); [assumption|discriminate]).
  assert (H2 : (z < two64)%Z) by (destruct (Z.leb 0 z); [destruct (Z.ltb_spec z two64); [assumption|discriminate]|discriminate]).
  split; [exact H1 | exact H2].
Qed.
Fixpoint img_bytesF (segs : list Segment) (a : Z) (n : nat) : option (list Z) :=
  match n with
  | O => Some []
  | S n' =>
      match seg_rom_f segs (Z_to_bv64f a) with     (* [comment removed for export] *)
      | Some b => match img_bytesF segs (a + 1) n' with
                  | Some r => Some (bv_unsigned b :: r)
                  | None => None
                  end
      | None => None
      end
  end.
Lemma img_bytesF_eq : forall segs a n, img_bytesF segs a n = img_bytes segs a n.
Proof.
  intros segs a n. revert a. induction n as [|n IH]; intros a; [reflexivity|].
  cbn [img_bytesF img_bytes]. rewrite seg_rom_f_eq, Z_to_bv64f_eq, IH. reflexivity.
Qed.

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
(* [comment removed for export] *)
Definition zsx32F (v : Z) : Z :=
  let u := Z.land v ones32z in
  if Z.ltb u two31z then u else (u - two32z + two64)%Z.
Lemma swrap_mod : forall n v, bv_swrap n v = bv_swrap n (v mod 2 ^ Z.of_N n)%Z.
Proof.
  intros n v. unfold bv_swrap, bv_wrap, bv_modulus. rewrite Z.add_mod_idemp_l by lia. reflexivity.
Qed.
Lemma zsx32F_eq : forall v, zsx32F v = zsx32 v.
Proof.
  intros v. unfold zsx32F, zsx32, ones32z, two31z, two32z, two64.
  rewrite (Z.land_ones v 32) by lia.
  pose proof (Z.mod_pos_bound v (2 ^ 32) ltac:(lia)) as Hb.
  rewrite (swrap_mod 32 v). change (Z.of_N 32) with 32%Z.
  rewrite (swrap_small 32 (v mod 2 ^ 32) (2 ^ 31) (2 ^ 32)); try reflexivity; try lia.
  set (u := (v mod 2 ^ 32)%Z) in *. clearbody u.
  destruct (Z.ltb_spec u (2 ^ 31)).
  - rewrite Z.mod_small by lia. reflexivity.
  - rewrite <- (Z.mod_add _ 1) by lia. rewrite Z.mod_small by lia. lia.
Qed.

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
Definition s64 (z : Z) : Z := if Z.ltb z two63z then z else (z - two64)%Z.
Lemma s64_eq : forall z, (0 <= z < two64)%Z -> s64 z = bv_swrap 64 z.
Proof.
  intros z Hz. unfold s64, two63z, two64 in *. symmetry. apply swrap_small; try reflexivity; try lia.
Qed.
Lemma zmod64_range : forall z, (0 <= zmod64 z < two64)%Z.
Proof. intros z. rewrite zmod64_eq. unfold two64. apply Z.mod_pos_bound. lia. Qed.
Definition lit_branchF (c : branch_cond) (x y : Z) : bool :=
  let x' := zmod64 x in let y' := zmod64 y in
  match c with
  | BC_EQ => Z.eqb x' y'
  | BC_NE => negb (Z.eqb x' y')
  | BC_LT => Z.ltb (s64 x') (s64 y')
  | BC_GE => negb (Z.ltb (s64 x') (s64 y'))
  | BC_LTU => Z.ltb x' y'
  | BC_GEU => negb (Z.ltb x' y')
  end.
Lemma lit_branchF_eq : forall c x y, lit_branchF c x y = lit_branch c x y.
Proof.
  intros c x y. unfold lit_branchF, lit_branch, branch_taken, bv_eqb, bv_ltu, bv_lts, bv_signed.
  rewrite !s64_eq by apply zmod64_range. rewrite !zmod64_bv. destruct c; reflexivity.
Qed.

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

(* [comment removed for export] *)
Lemma conc_try_fk : forall kn e cands, conc_try (facts_of kn) e cands = conc_try kn e cands.
Proof. intros kn e cands. induction cands as [|s rest IH]; [reflexivity|]. cbn [conc_try]. rewrite IH, erange_fk. reflexivity. Qed.
Lemma concretize_fk : forall kn e, concretize (facts_of kn) e = concretize kn e.
Proof. intros. unfold concretize. rewrite conc_try_fk. reflexivity. Qed.
Lemma foldK_fk : forall kn e, foldK (facts_of kn) e = foldK kn e.
Proof. intros. unfold foldK. rewrite ?erange_fk, ?concretize_fk. reflexivity. Qed.
Lemma know_lookupA_fk1 : forall k segs kn rb rk n sx hints acc,
  know_lookupA (facts_of k) segs kn rb rk n sx hints acc = know_lookupA k segs kn rb rk n sx hints acc.
Proof.
  intros k segs kn. induction kn as [|K rest IH]; intros; [reflexivity|].
  cbn [know_lookupA].
  repeat first [ reflexivity
               | rewrite IH; reflexivity
               | progress (rewrite ?xinside_fk)
               | lazymatch goal with
                 | |- (if ?x then _ else _) = _ => destruct x; cbn beta iota zeta
                 | |- match ?x with _ => _ end = _ => destruct x; cbn beta iota zeta
                 end ].
Qed.

(* [comment removed for export] *)
Fixpoint conc_tryT (fs : fdig) (kn : list kentry) (e : expr) (cands : list expr) : option Z :=
  match cands with
  | [] => None
  | s :: rest =>
      if closedb s then conc_tryT fs kn e rest else
      match erangeT fs s with
      | Some (lo, hi) =>
          if Z.leb (hi - lo) conc_limit then
            match evalS s (wrap64 lo) e with
            | Some v =>
                if (if Z.ltb hi lo then true
                     else if probeS s e v hi then probeS s e v (lo + (hi - lo) / 2)%Z else false) then
                  if all_eval_toP s e v lo (Z.to_nat (hi - lo + 1)) then Some v   (* [comment removed for export] *)
                  else conc_tryT fs kn e rest
                else conc_tryT fs kn e rest
            | None => conc_tryT fs kn e rest
            end
          else conc_tryT fs kn e rest
      | None => conc_tryT fs kn e rest
      end
  end.

Definition concretizeT (fs : fdig) (kn : list kentry) (e : expr) : option Z :=
  if closedb e then eval_closed e else conc_tryT fs kn e (nubE (subexprs e)).

Definition foldKT (fs : fdig) (kn : list kentry) (e : expr) : expr :=
  match e with
  | ELit _ => e
  | _ => match erangeT fs e with
         | Some (lo, hi) => if Z.eqb lo hi then ELit lo
                            else match concretizeT fs kn e with Some v => ELit v | None => e end
         | None => match concretizeT fs kn e with Some v => ELit v | None => e end   (* [comment removed for export] *)
         end
  end.

Definition mkAluKT (fs : fdig) (kn : list kentry) (op : aluop) (a b : expr) : expr :=
  foldKT fs kn (mkAluK0 kn op a b).

Definition zband32T (fs : fdig) (kn : list kentry) (d : expr) : bool :=
  let l := lin_of d in
  match lin_range (erangeT fs) (fst l) (snd l) with
  | Some (lo, hi) => (Z.ltb mtwo31z lo && Z.ltb hi two31z)%bool
  | None => false
  end.

Definition mkAluwK0T (fs : fdig) (kn : list kentry) (op : aluop) (a b : expr) : expr :=
  match op with
  | ALU_ADD | ALU_SUB =>
      let d := mkAlu op a b in
      match is_lit d with
      | Some v => ELit (zsx32F v)
      | None => match erangeT fs d with
                | Some (lo, hi) => if sx32_stable lo hi then d else if zband32T fs kn d then d else mkAluw op a b
                | None => if zband32T fs kn d then d else mkAluw op a b
                end
      end
  | _ => mkAluw op a b
  end.

Definition mkAluwKT (fs : fdig) (kn : list kentry) (op : aluop) (a b : expr) : expr :=
  foldKT fs kn (mkAluwK0T fs kn op a b).

Definition extK0T (fs : fdig) (kn : list kentry) (v : expr) : expr :=
  match v with
  | EExt sx O n e =>
      if Nat.leb n 7 then
        match erangeT fs e with
        | Some (lo, hi) => if Z.ltb hi (if sx then 2 ^ (8 * Z.of_nat n) / 2 else 2 ^ (8 * Z.of_nat n)) then e else v
        | None => v
        end
      else v
  | _ => v
  end.

Definition extKT (fs : fdig) (kn : list kentry) (v : expr) : expr := foldKT fs kn (extK0T fs kn v).

Definition flat_scT (fs : fdig) (kn : list kentry) (a : saddr) (n : nat) : list sidecond :=
  match base_rangeT fs (a_base a) with
  | Some (lo, hi) =>
      if (Z.leb 0 (lo + a_off a) && Z.leb (hi + a_off a + Z.of_nat n) two64)%bool
      then [] else [SCFlat a (elen n)]
  | None => [SCFlat a (elen n)]
  end.

Definition decide_branchT (fs : fdig) (kn : list kentry) (c : branch_cond) (a b : expr) : option bool :=
  match a, b with
  | ELit x, ELit y => Some (lit_branchF c x y)
  | _, _ =>
      if expr_eqb a b then Some (cond_on_eq c)
      else match diff_branch c a b with
           | Some t => Some t
           | None =>
             match erangeT fs a, erangeT fs b with
             | Some (al, ah), Some (bl, bh) => range_branch c al ah bl bh
             | _, _ => None
             end
           end
  end.

Definition conc_exprT (fs : fdig) (kn : list kentry) (e : expr) : expr :=
  match e with
  | ELit _ => e
  | _ => match concretizeT fs kn e with Some v => ELit v | None => e end
  end.

Definition enum_branchT (fs : fdig) (kn : list kentry) (c : branch_cond) (a b : expr) : option bool :=
  let '(e, pos) := cond_probe c a b in
  match concretizeT fs kn e with
  | Some v => let z := Z.eqb (v mod two64) 0 in Some (if pos then negb z else z)
  | None => None
  end.

Definition to_saddrKT (fs : fdig) (kn : list kentry) (e : expr) (imm : Z) : saddr :=
  match split_lit e with
  | (ELit _, _) => to_saddr e imm
  | _ => match concretizeT fs kn (mkAlu ALU_ADD e (ELit imm)) with
         | Some v => SA (ELit 0) v
         | None => to_saddr e imm
         end
  end.

Lemma conc_tryT_eq : forall kn e cands, conc_tryT (SFS kn) kn e cands = conc_try kn e cands.
Proof. intros kn e cands. induction cands as [|s rest IH]; [reflexivity|]. cbn [conc_tryT conc_try]. rewrite IH, erangeT_eq. reflexivity. Qed.
Lemma concretizeT_eq : forall kn e, concretizeT (SFS kn) kn e = concretize kn e.
Proof. intros. unfold concretizeT, concretize. rewrite conc_tryT_eq. reflexivity. Qed.
Lemma foldKT_eq : forall kn e, foldKT (SFS kn) kn e = foldK kn e.
Proof. intros. unfold foldKT, foldK. rewrite ?erangeT_eq, ?concretizeT_eq. reflexivity. Qed.
Lemma mkAluKT_eq : forall kn op a b, mkAluKT (SFS kn) kn op a b = mkAluK kn op a b.
Proof. intros. unfold mkAluKT, mkAluK. apply foldKT_eq. Qed.
Lemma zband32T_eq : forall kn d, zband32T (SFS kn) kn d = zband32 kn d.
Proof. intros. unfold zband32T, zband32. rewrite (lin_range_extT _ _ (erangeT_eq' kn)). reflexivity. Qed.
Lemma mkAluwK0T_eq : forall kn op a b, mkAluwK0T (SFS kn) kn op a b = mkAluwK0 kn op a b.
Proof.
  intros. unfold mkAluwK0T, mkAluwK0. destruct op; try reflexivity;
    destruct (is_lit (mkAlu _ a b)); rewrite ?zsx32F_eq, ?erangeT_eq, ?zband32T_eq; reflexivity.
Qed.
Lemma mkAluwKT_eq : forall kn op a b, mkAluwKT (SFS kn) kn op a b = mkAluwK kn op a b.
Proof. intros. unfold mkAluwKT, mkAluwK. rewrite mkAluwK0T_eq. apply foldKT_eq. Qed.
Lemma extK0T_eq : forall kn v, extK0T (SFS kn) kn v = extK0 kn v.
Proof. intros. unfold extK0T, extK0. destruct v; try reflexivity. destruct lo; rewrite ?erangeT_eq; reflexivity. Qed.
Lemma extKT_eq : forall kn v, extKT (SFS kn) kn v = extK kn v.
Proof. intros. unfold extKT, extK. rewrite extK0T_eq. apply foldKT_eq. Qed.
Lemma flat_scT_eq : forall kn a n, flat_scT (SFS kn) kn a n = flat_sc kn a n.
Proof. intros. unfold flat_scT, flat_sc. rewrite base_rangeT_eq. reflexivity. Qed.
Lemma decide_branchT_eq : forall kn c a b, decide_branchT (SFS kn) kn c a b = decide_branch kn c a b.
Proof. intros. unfold decide_branchT, decide_branch. destruct a, b; rewrite ?lit_branchF_eq, ?erangeT_eq; reflexivity. Qed.
Lemma conc_exprT_eq : forall kn e, conc_exprT (SFS kn) kn e = conc_expr kn e.
Proof. intros. unfold conc_exprT, conc_expr. rewrite ?concretizeT_eq. reflexivity. Qed.
Lemma enum_branchT_eq : forall kn c a b, enum_branchT (SFS kn) kn c a b = enum_branch kn c a b.
Proof. intros. unfold enum_branchT, enum_branch. destruct (cond_probe c a b). rewrite concretizeT_eq. reflexivity. Qed.
Lemma to_saddrKT_eq : forall kn e imm, to_saddrKT (SFS kn) kn e imm = to_saddrK kn e imm.
Proof. intros. unfold to_saddrKT, to_saddrK. rewrite ?concretizeT_eq. reflexivity. Qed.

(* [comment removed for export] *)
Definition smemo : Type := list (expr * expr * Z * Z * nat * bool).
Fixpoint sm_lookup (m : smemo) (s e : expr) (v lo : Z) (cnt : nat) : option bool :=
  match m with
  | [] => None
  | (s', e', v', lo', cnt', r) :: rest =>
      if (if expr_eqb s s' then if expr_eqb e e' then if Z.eqb v v' then if Z.eqb lo lo' then Nat.eqb cnt cnt' else false else false else false else false)
      then Some r else sm_lookup rest s e v lo cnt
  end.
Definition smemo_ok (m : smemo) : Prop :=
  Forall (fun x : expr * expr * Z * Z * nat * bool => let '(s, e, v, lo, cnt, r) := x in all_eval_toP s e v lo cnt = r) m.
Lemma sm_lookup_ok : forall m s e v lo cnt r, smemo_ok m -> sm_lookup m s e v lo cnt = Some r -> all_eval_toP s e v lo cnt = r.
Proof.
  intros m s e v lo cnt r Hm. induction Hm as [|[[[[[s' e'] v'] lo'] cnt'] r'] rest Hx Hrest IH]; [discriminate|].
  cbn [sm_lookup]. destruct (expr_eqb s s') eqn:E1; [|exact IH]. destruct (expr_eqb e e') eqn:E2; [|exact IH].
  destruct (Z.eqb_spec v v'); [|exact IH]. destruct (Z.eqb_spec lo lo'); [|exact IH]. destruct (Nat.eqb_spec cnt cnt'); [|exact IH].
  intros H; injection H as <-. apply expr_eqb_true in E1. apply expr_eqb_true in E2. cbn in Hx. subst s' e' v' lo' cnt'. exact Hx.
Qed.
Definition all_eval_toPM (s e : expr) (v lo : Z) (cnt : nat) (m : smemo) : bool * smemo :=
  match sm_lookup m s e v lo cnt with
  | Some r => (r, m)
  | None => let r := all_eval_toP s e v lo cnt in (r, (s, e, v, lo, cnt, r) :: m)
  end.
Lemma all_eval_toPM_eq : forall s e v lo cnt m, smemo_ok m ->
  fst (all_eval_toPM s e v lo cnt m) = all_eval_toP s e v lo cnt /\ smemo_ok (snd (all_eval_toPM s e v lo cnt m)).
Proof.
  intros s e v lo cnt m Hm. unfold all_eval_toPM. destruct (sm_lookup m s e v lo cnt) as [r|] eqn:L; cbn [fst snd].
  - split; [symmetry; exact (sm_lookup_ok _ _ _ _ _ _ _ Hm L) | exact Hm].
  - split; [reflexivity|]. constructor; [reflexivity | exact Hm].
Qed.

Fixpoint conc_tryM (fs : fdig) (kn : list kentry) (e : expr) (cands : list expr) (m : smemo) : option Z * smemo :=
  match cands with
  | [] => (None, m)
  | s :: rest =>
      if closedb s then conc_tryM fs kn e rest m else
      match erangeT fs s with
      | Some (lo, hi) =>
          if Z.leb (hi - lo) conc_limit then
            match evalS s (wrap64 lo) e with
            | Some v =>
                if (if Z.ltb hi lo then true
                     else if probeS s e v hi then probeS s e v (lo + (hi - lo) / 2)%Z else false) then
                  let '(r, m') := all_eval_toPM s e v lo (Z.to_nat (hi - lo + 1)) m in
                  if r then (Some v, m') else conc_tryM fs kn e rest m'
                else conc_tryM fs kn e rest m
            | None => conc_tryM fs kn e rest m
            end
          else conc_tryM fs kn e rest m
      | None => conc_tryM fs kn e rest m
      end
  end.
Lemma conc_tryM_eq : forall fs kn e cands m, smemo_ok m ->
  fst (conc_tryM fs kn e cands m) = conc_tryT fs kn e cands /\ smemo_ok (snd (conc_tryM fs kn e cands m)).
Proof.
  intros fs kn e cands. induction cands as [|s rest IH]; intros m Hm; [split; [reflexivity|exact Hm]|].
  cbn [conc_tryM conc_tryT].
  destruct (closedb s); [exact (IH m Hm)|].
  destruct (erangeT fs s) as [[lo hi]|]; [|exact (IH m Hm)].
  destruct (Z.leb (hi - lo) conc_limit); [|exact (IH m Hm)].
  destruct (evalS s (wrap64 lo) e) as [v|]; [|exact (IH m Hm)].
  destruct (if Z.ltb hi lo then true else if probeS s e v hi then probeS s e v (lo + (hi - lo) / 2)%Z else false); [|exact (IH m Hm)].
  pose proof (all_eval_toPM_eq s e v lo (Z.to_nat (hi - lo + 1)) m Hm) as [Hr Hm'].
  destruct (all_eval_toPM s e v lo (Z.to_nat (hi - lo + 1)) m) as [r m']. cbn [fst snd] in Hr, Hm'. subst r.
  destruct (all_eval_toP s e v lo (Z.to_nat (hi - lo + 1))); [split; [reflexivity|exact Hm'] | exact (IH m' Hm')].
Qed.
Definition concretizeM (fs : fdig) (kn : list kentry) (e : expr) (m : smemo) : option Z * smemo :=
  if closedb e then (eval_closed e, m) else conc_tryM fs kn e (nubE (subexprs e)) m.
Lemma concretizeM_eq : forall fs kn e m, smemo_ok m ->
  fst (concretizeM fs kn e m) = concretizeT fs kn e /\ smemo_ok (snd (concretizeM fs kn e m)).
Proof. intros. unfold concretizeM, concretizeT. destruct (closedb e); [split; [reflexivity|assumption] | apply conc_tryM_eq; assumption]. Qed.
Definition foldKM (fs : fdig) (kn : list kentry) (e : expr) (m : smemo) : expr * smemo :=
  match e with
  | ELit _ => (e, m)
  | _ => match erangeT fs e with
         | Some (lo, hi) => if Z.eqb lo hi then (ELit lo, m)
                            else let '(c, m') := concretizeM fs kn e m in (match c with Some v => ELit v | None => e end, m')
         | None => let '(c, m') := concretizeM fs kn e m in (match c with Some v => ELit v | None => e end, m')
         end
  end.
Ltac smemo_use L m Hm :=
  let H := fresh in pose proof (L m Hm) as H;
  let p := fresh "p" in
  match type of H with fst ?t = _ /\ _ => destruct t as [? ?] eqn:?; cbn [fst snd] in H; destruct H as [<- ?] end.
Lemma foldKM_eq : forall fs kn e m, smemo_ok m -> fst (foldKM fs kn e m) = foldKT fs kn e /\ smemo_ok (snd (foldKM fs kn e m)).
Proof.
  intros fs kn e m Hm. unfold foldKM, foldKT.
  destruct e; try (split; [reflexivity|exact Hm]);
    (destruct (erangeT fs _) as [[rlo rhi]|]; [destruct (Z.eqb rlo rhi); [split; [reflexivity|exact Hm]|]|]);
    (match goal with |- context [concretizeM ?a ?b ?c ?d] =>
       pose proof (concretizeM_eq a b c d Hm) as [H1 H2]; destruct (concretizeM a b c d) as [c0 m'] end;
     cbn [fst snd] in H1, H2 |- *; subst c0; split; [reflexivity|exact H2]).
Qed.
Definition mkAluKM (fs : fdig) (kn : list kentry) (op : aluop) (a b : expr) (m : smemo) : expr * smemo :=
  foldKM fs kn (mkAluK0 kn op a b) m.
Lemma mkAluKM_eq : forall fs kn op a b m, smemo_ok m -> fst (mkAluKM fs kn op a b m) = mkAluKT fs kn op a b /\ smemo_ok (snd (mkAluKM fs kn op a b m)).
Proof. intros. unfold mkAluKM, mkAluKT. apply foldKM_eq. assumption. Qed.
Definition mkAluwKM (fs : fdig) (kn : list kentry) (op : aluop) (a b : expr) (m : smemo) : expr * smemo :=
  foldKM fs kn (mkAluwK0T fs kn op a b) m.
Lemma mkAluwKM_eq : forall fs kn op a b m, smemo_ok m -> fst (mkAluwKM fs kn op a b m) = mkAluwKT fs kn op a b /\ smemo_ok (snd (mkAluwKM fs kn op a b m)).
Proof. intros. unfold mkAluwKM, mkAluwKT. apply foldKM_eq. assumption. Qed.
Definition extKM (fs : fdig) (kn : list kentry) (v : expr) (m : smemo) : expr * smemo := foldKM fs kn (extK0T fs kn v) m.
Lemma extKM_eq : forall fs kn v m, smemo_ok m -> fst (extKM fs kn v m) = extKT fs kn v /\ smemo_ok (snd (extKM fs kn v m)).
Proof. intros. unfold extKM, extKT. apply foldKM_eq. assumption. Qed.
Definition conc_exprM (fs : fdig) (kn : list kentry) (e : expr) (m : smemo) : expr * smemo :=
  match e with
  | ELit _ => (e, m)
  | _ => let '(c, m') := concretizeM fs kn e m in (match c with Some v => ELit v | None => e end, m')
  end.
Lemma conc_exprM_eq : forall fs kn e m, smemo_ok m -> fst (conc_exprM fs kn e m) = conc_exprT fs kn e /\ smemo_ok (snd (conc_exprM fs kn e m)).
Proof.
  intros fs kn e m Hm. unfold conc_exprM, conc_exprT.
  destruct e; try (split; [reflexivity|exact Hm]);
    (match goal with |- context [concretizeM ?a ?b ?c ?d] =>
       pose proof (concretizeM_eq a b c d Hm) as [H1 H2]; destruct (concretizeM a b c d) as [c0 m'] end;
     cbn [fst snd] in H1, H2 |- *; subst c0; split; [reflexivity|exact H2]).
Qed.
Definition enum_branchM (fs : fdig) (kn : list kentry) (c : branch_cond) (a b : expr) (m : smemo) : option bool * smemo :=
  let '(e, pos) := cond_probe c a b in
  let '(r, m') := concretizeM fs kn e m in
  (match r with
   | Some v => let z := Z.eqb (v mod two64) 0 in Some (if pos then negb z else z)
   | None => None
   end, m').
Lemma enum_branchM_eq : forall fs kn c a b m, smemo_ok m -> fst (enum_branchM fs kn c a b m) = enum_branchT fs kn c a b /\ smemo_ok (snd (enum_branchM fs kn c a b m)).
Proof.
  intros fs kn c a b m Hm. unfold enum_branchM, enum_branchT. destruct (cond_probe c a b) as [e pos].
  pose proof (concretizeM_eq fs kn e m Hm) as [H1 H2]. destruct (concretizeM fs kn e m) as [r m']. cbn [fst snd] in H1, H2 |- *.
  subst r. split; [reflexivity|exact H2].
Qed.
Definition to_saddrKM (fs : fdig) (kn : list kentry) (e : expr) (imm : Z) (m : smemo) : saddr * smemo :=
  match split_lit e with
  | (ELit _, _) => (to_saddr e imm, m)
  | _ => let '(c, m') := concretizeM fs kn (mkAlu ALU_ADD e (ELit imm)) m in
         (match c with Some v => SA (ELit 0) v | None => to_saddr e imm end, m')
  end.
Lemma to_saddrKM_eq : forall fs kn e imm m, smemo_ok m -> fst (to_saddrKM fs kn e imm m) = to_saddrKT fs kn e imm /\ smemo_ok (snd (to_saddrKM fs kn e imm m)).
Proof.
  intros fs kn e imm m Hm. unfold to_saddrKM, to_saddrKT. destruct (split_lit e) as [b k].
  destruct b; try (split; [reflexivity|exact Hm]);
    (pose proof (concretizeM_eq fs kn (mkAlu ALU_ADD e (ELit imm)) m Hm) as [H1 H2];
     destruct (concretizeM fs kn (mkAlu ALU_ADD e (ELit imm)) m) as [c0 m']; cbn [fst snd] in H1, H2 |- *; subst c0; split; [reflexivity|exact H2]).
Qed.


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
                      (s_log ss) (s_know ss) (N.succ i))
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
(* [comment removed for export] *)
Definition sbv12 (b : bv 12) : Z := let u := bv_unsigned b in if Z.ltb u 2048 then u else (u - 4096)%Z.
Definition sbv13 (b : bv 13) : Z := let u := bv_unsigned b in if Z.ltb u 4096 then u else (u - 8192)%Z.
Definition sbv20 (b : bv 20) : Z := let u := bv_unsigned b in if Z.ltb u 524288 then u else (u - 1048576)%Z.
Definition sbv21 (b : bv 21) : Z := let u := bv_unsigned b in if Z.ltb u 1048576 then u else (u - 2097152)%Z.
Lemma sbv12_eq : forall b, sbv12 b = bv_signed b.
Proof. intros b. unfold sbv12, bv_signed. symmetry. apply swrap_small; [reflexivity|reflexivity| |lia]. exact (bv_unsigned_in_range 12 b). Qed.
Lemma sbv13_eq : forall b, sbv13 b = bv_signed b.
Proof. intros b. unfold sbv13, bv_signed. symmetry. apply swrap_small; [reflexivity|reflexivity| |lia]. exact (bv_unsigned_in_range 13 b). Qed.
Lemma sbv20_eq : forall b, sbv20 b = bv_signed b.
Proof. intros b. unfold sbv20, bv_signed. symmetry. apply swrap_small; [reflexivity|reflexivity| |lia]. exact (bv_unsigned_in_range 20 b). Qed.
Lemma sbv21_eq : forall b, sbv21 b = bv_signed b.
Proof. intros b. unfold sbv21, bv_signed. symmetry. apply swrap_small; [reflexivity|reflexivity| |lia]. exact (bv_unsigned_in_range 21 b). Qed.

Fixpoint log_lookupF (fs : fdig) (kn : list kentry) (log : list sentry) (rb : expr) (rk : Z) (n : nat) (sx : bool)
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
Fixpoint know_lookupAF (fs : fdig) (allkn : list kentry) (segs : list Segment) (kn : list kentry) (rb : expr) (rk : Z)
         (n : nat) (zn re : Z) (sx : bool) (hints : list bool) (acc : list sidecond) : lres :=
  let know_lookup (sg : list Segment) rest rb rk n := know_lookupAF fs allkn sg rest rb rk n zn re in
  match kn with
  | [] => LMiss acc hints
  | K :: rest =>
      match K with
      | KWord (SA kb kk) w v =>
          match (if expr_eqb rb kb then rel_lit2 rb rk re kb kk (kk + Z.of_nat w) else RUnknown) with
          | RInside d => LHit (mkExtF sx (Z.to_nat d) n v) acc hints
          | _ => know_lookup segs rest rb rk n sx hints acc
          end
      | KZero (SA kb kk) len =>
          match len with
          | ELit l0 =>
              match (if expr_eqb rb kb then rel_lit2 rb rk re kb kk (kk + zmod64 l0) else RUnknown) with
              | RInside _ => LHit (ELit 0) acc hints
              | RDisjoint | RPartial => know_lookup segs rest rb rk n sx hints acc
              | RUnknown =>
                  (* [comment removed for export] *)
                  if xinsideF fs allkn rb rk (ELit zn) kb kk len then LHit (ELit 0) acc hints else
                  match hints with
                  | true :: hs => LHit (ELit 0) (SCInside (SA rb rk) (ELit zn) (SA kb kk) len :: acc) hs
                  | false :: hs => know_lookup segs rest rb rk n sx hs acc
                  | [] => know_lookup segs rest rb rk n sx [] acc
                  end
              end
          | _ =>
              if xinsideF fs allkn rb rk (ELit zn) kb kk len then LHit (ELit 0) acc hints else
              match hints with
              | true :: hs => LHit (ELit 0) (SCInside (SA rb rk) (ELit zn) (SA kb kk) len :: acc) hs
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
                                    (SCInside (SA rb rk) (ELit zn) (SA kb kk) len :: acc) hs
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
                match img_bytesF segs rk n with
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
Fixpoint wr_coveredF (fs : fdig) (allkn kn : list kentry) (a : saddr) (n : nat) : bool :=
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
Definition storeok_scF (fs : fdig) (kn : list kentry) (a : saddr) (n : nat) : list sidecond :=
  if wr_coveredF fs kn kn a n then [] else [SCStoreOk a n].

(* [comment removed for export] *)
Fixpoint log_lookupL (fs : fdig) (kn : list kentry) (log : list sentry) (rb : expr) (rk : Z) (n : nat) (zn re : Z) (sx : bool)
         (hints : list bool) (acc : list sidecond)
         (othr : option lthr) (oD : option (list (saddr * expr))) (cache : list (expr * option (Z * Z))) : lres :=
  match log with
  | [] => LMiss acc hints
  | SE (SA kb kk) w v :: rest =>
      match (if expr_eqb rb kb then rel_lit2 rb rk re kb kk (kk + Z.of_nat w) else RUnknown) with
      | RInside d => LHit (mkExtF sx (Z.to_nat d) n v) acc hints
      | RDisjoint => log_lookupL fs kn rest rb rk n zn re sx hints acc othr oD cache
      | RPartial => LStuck
      | RUnknown =>
          let thr := match othr with Some t => t | None => mk_lthr fs rb rk zn end in
          let brc := match lbr_lookup cache kb with
                     | Some et => (et, cache)
                     | None => let et := mk_ethr thr (base_rangeT fs kb) in (et, (kb, et) :: cache)
                     end in
          if ethr_test (fst brc) kk (Z.of_nat w)
          then log_lookupL fs kn rest rb rk n zn re sx hints acc (Some thr) oD (snd brc)
          else
          let D := match oD with Some D => D | None => disj_sidesF fs kn kn rb rk zn end in
          if ranges_apart_restF fs kn D rb rk zn kb kk (Z.of_nat w)
          then log_lookupL fs kn rest rb rk n zn re sx hints acc (Some thr) (Some D) (snd brc)
          else
          match hints with
          | false :: _ => LStuck
          | _ => log_lookupL fs kn rest rb rk n zn re sx (tl hints)
                   (SCDisj (SA rb rk) (ELit zn) (SA kb kk) (elen w) :: acc) (Some thr) (Some D) (snd brc)
          end
      end
  end.

Definition sym_stepF (fk : list kentry) (fs : fdig) (segs : list Segment) (i : instr) (ss : sym_state) (scr : scripts) : stepres :=
  let g r := sr_get (s_regs ss) r in
  let p := s_pc ss in
  match i with
  | OpImm op rd rs imm => SOk (sset ss rd (mkAluKT fs fk op (g rs) (ELit (sbv12 imm))) (p + 4)) [] scr
  | ShiftImm op rd rs sh => SOk (sset ss rd (mkAluKT fs fk op (g rs) (ELit (bv_unsigned sh))) (p + 4)) [] scr
  | Op op rd rs1 rs2 => SOk (sset ss rd (mkAluKT fs fk op (g rs1) (g rs2)) (p + 4)) [] scr
  | OpImm32 rd rs imm => SOk (sset ss rd (mkAluwKT fs fk ALU_ADD (g rs) (ELit (sbv12 imm))) (p + 4)) [] scr
  | ShiftImm32 op rd rs sh => SOk (sset ss rd (mkAluw op (g rs) (ELit (bv_unsigned sh))) (p + 4)) [] scr
  | Op32 op rd rs1 rs2 => SOk (sset ss rd (mkAluwKT fs fk op (g rs1) (g rs2)) (p + 4)) [] scr
  | Mul op rd rs1 rs2 => SOk (sset ss rd (mkMd op (g rs1) (g rs2)) (p + 4)) [] scr
  | Mul32 op rd rs1 rs2 => SOk (sset ss rd (mkMdw op (g rs1) (g rs2)) (p + 4)) [] scr
  | Lui rd imm => SOk (sset ss rd (ELit (zmod64 (Z.shiftl (sbv20 imm) 12))) (p + 4)) [] scr
  | Auipc rd imm => SOk (sset ss rd (ELit (zmod64 (Z.shiftl (sbv20 imm) 12 + p))) (p + 4)) [] scr
  | Jal rd imm => SOk (sset ss rd (ELit (p + 4)) (zmod64 (p + sbv21 imm))) [] scr
  | Jalr rd rs1 imm =>
      match conc_exprT fs fk (g rs1) with
      | ELit z => SOk (sset ss rd (ELit (p + 4)) (zmod64 (Z.land (zmod64 z + sbv12 imm) (-2)))) [] scr
      | _ => SStop
      end
  | Branch c rs1 rs2 imm =>
      let tk := zmod64 (p + sbv13 imm) in
      let a := g rs1 in let b := g rs2 in
      match match decide_branchT fs fk c a b with
            | Some t => Some t
            | None => match decide_branchT fs fk c (conc_exprT fs fk a) (conc_exprT fs fk b) with
                      | Some t => Some t
                      | None => enum_branchT fs fk c a b
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
      let n := msize_bytes sz in let zn := Z.of_nat n in
      (* [comment removed for export] *)
      let sx' := match sz with SZ8 => false | _ => sx end in
      let a := to_saddrKT fs fk (g rs) (sbv12 imm) in
      let fin v scs hints :=
        SOk (sset ss rd (extKT fs fk v) (p + 4)) (flat_scT fs fk a n ++ scs)
            (SCR (sc_dirs scr) (sc_reads scr) hints) in
      match log_lookupL fs fk (s_log ss) (a_base a) (a_off a) n zn (a_off a + zn) sx' (sc_hints scr) [] None None [] with
      | LStuck => SStop
      | LHit v scs hints => fin v scs hints
      | LMiss scs hints =>
          match know_lookupAF fs fk segs (s_know ss) (a_base a) (a_off a) n zn (a_off a + zn) sx' hints scs with
          | LStuck => SStop
          | LHit v scs' hints' => fin v scs' hints'
          | LMiss scs' hints' =>
              (* [comment removed for export] *)
              let i := s_next ss in
              let rv := match sc_reads scr with [] => EVar i | e :: _ => e end in
              let reads' := match sc_reads scr with [] => [] | _ :: t => t end in
              SOk (SS (p + 4)
                      (if bv_eqb rd 0 then s_regs ss else sr_upd (s_regs ss) (ridx rd) rv)
                      (s_log ss) (s_know ss) (N.succ i))
                  (flat_scT fs fk a n ++ SCReadBase a n sx' rv :: scs')
                  (SCR (sc_dirs scr) reads' hints')
          end
      end
  | Store sz rs1 rs2 imm =>
      let n := msize_bytes sz in
      let a := to_saddrKT fs fk (g rs1) (sbv12 imm) in
      SOk (SS (p + 4) (s_regs ss) (SE a n (g rs2) :: s_log ss) (s_know ss) (s_next ss))
          (flat_scT fs fk a n ++ storeok_scF fs fk a n) scr
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
  (othr = None \/ othr = Some (mk_lthr fs rb rk (Z.of_nat n))) ->
  (oD = None \/ oD = Some (disj_sidesF fs kn kn rb rk (Z.of_nat n))) ->
  (forall b r, lbr_lookup cache b = Some r -> r = mk_ethr (mk_lthr fs rb rk (Z.of_nat n)) (base_rangeT fs b)) ->
  log_lookupL fs kn log rb rk n (Z.of_nat n) (rk + Z.of_nat n) sx hints acc othr oD cache = log_lookupF fs kn log rb rk n sx hints acc.
Proof.
  intros fs kn log. induction log as [|[[kb kk] w v] rest IH]; intros rb rk n sx hints acc othr oD cache Ht HD Hc; [reflexivity|].
  cbn [log_lookupL log_lookupF]. unfold elen. rewrite rel_lit2_guard, rel_lit2_eq.
  destruct (rel_lit rb rk (Z.of_nat n) kb kk (Z.of_nat w)); rewrite ?mkExtF_eq; try reflexivity; [apply IH; assumption|].
  set (thr := match othr with Some t => t | None => mk_lthr fs rb rk (Z.of_nat n) end).
  assert (Hthr : thr = mk_lthr fs rb rk (Z.of_nat n)) by (destruct Ht as [-> | ->]; reflexivity).
  set (D := match oD with Some D => D | None => disj_sidesF fs kn kn rb rk (Z.of_nat n) end).
  assert (HDD : D = disj_sidesF fs kn kn rb rk (Z.of_nat n)) by (destruct HD as [-> | ->]; reflexivity).
  rewrite Hthr.
  set (T := mk_lthr fs rb rk (Z.of_nat n)) in *.
  set (brc := match lbr_lookup cache kb with Some et => (et, cache) | None => (mk_ethr T (base_rangeT fs kb), (kb, mk_ethr T (base_rangeT fs kb)) :: cache) end).
  assert (Hbr : fst brc = mk_ethr T (base_rangeT fs kb) /\ forall b r, lbr_lookup (snd brc) b = Some r -> r = mk_ethr T (base_rangeT fs b)).
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
Ltac feq_step IH :=
  first [ reflexivity
        | rewrite IH; reflexivity
        | progress (rewrite ?rel_lit2_guard, ?xinsideF_eq, ?xloF_eq, ?xhiF_eq, ?ranges_apartF_eq, ?mkExtF_eq, ?rel_lit2_eq)
        | lazymatch goal with
          | |- (if ?x then _ else _) = _ => destruct x; cbn beta iota zeta
          | |- match ?x with _ => _ end = _ => destruct x; cbn beta iota zeta
          end ].
Lemma know_lookupAF_eq : forall allkn segs kn rb rk n sx hints acc,
  know_lookupAF (SFS allkn) allkn segs kn rb rk n (Z.of_nat n) (rk + Z.of_nat n) sx hints acc = know_lookupA allkn segs kn rb rk n sx hints acc.
Proof.
  intros allkn segs kn. induction kn as [|K rest IH]; intros; [reflexivity|].
  cbn [know_lookupAF know_lookupA]. unfold elen. rewrite ?img_bytesF_eq. repeat (feq_step IH).
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
  destruct i; rewrite ?sbv12_eq, ?sbv13_eq, ?sbv20_eq, ?sbv21_eq, ?zmod64_bv;
    rewrite ?mkAluKT_eq, ?mkAluwKT_eq, ?conc_exprT_eq, ?decide_branchT_eq, ?enum_branchT_eq, ?to_saddrKT_eq, ?flat_scT_eq;
    rewrite ?log_lookupL_eq, ?log_lookupF_eq, ?know_lookupAF_eq, ?storeok_scF_eq by (first [left; reflexivity | intros ? ? [=]]); try reflexivity.
  all: try (destruct (conc_expr _ _); rewrite ?zmod64_bv; reflexivity).
  destruct (log_lookup _ _ _ _ _ _ _ _); rewrite ?extKT_eq, ?know_lookupAF_eq; try reflexivity.
  destruct (know_lookupA _ _ _ _ _ _ _ _ _); rewrite ?extKT_eq; reflexivity.
Qed.
(* [comment removed for export] *)
Definition lk_relevant (rb : expr) (K : kentry) : bool :=
  match K with
  | KWord (SA kb _) _ _ => expr_eqb rb kb
  | KBlob (SA kb _) _ _ => expr_eqb rb kb
  | KImg _ _ => match rb with ELit _ => true | _ => false end
  | _ => true
  end.
Lemma filter_factb_relevant : forall rb kn,
  List.filter is_factb (List.filter (lk_relevant rb) kn) = List.filter is_factb kn.
Proof.
  intros rb kn. induction kn as [|K rest IH]; [reflexivity|]. cbn [List.filter].
  destruct (lk_relevant rb K) eqn:R; cbn [List.filter]; rewrite IH; destruct (is_factb K) eqn:F; try reflexivity.
  exfalso. destruct K as [[? ?] ? ?|[? ?] ?|[? ?] ? ?| | | |[? ?] ?|]; cbn in R, F; try discriminate.
Qed.
Lemma erange_relevant : forall rb kn e, erange (List.filter (lk_relevant rb) kn) e = erange kn e.
Proof. intros. unfold erange. rewrite !facts_of_filter, filter_factb_relevant. reflexivity. Qed.
Lemma know_lookupAF_bucket : forall fs allkn segs kn rb rk n zn re sx hints acc,
  know_lookupAF fs allkn segs (List.filter (lk_relevant rb) kn) rb rk n zn re sx hints acc
  = know_lookupAF fs allkn segs kn rb rk n zn re sx hints acc.
Proof.
  intros fs allkn segs kn rb. induction kn as [|K rest IH]; intros; [reflexivity|].
  cbn [List.filter]. destruct (lk_relevant rb K) eqn:R.
  - cbn [know_lookupAF].
    repeat first [ reflexivity
                 | rewrite IH; reflexivity
                 | progress (rewrite ?erange_relevant)
                 | lazymatch goal with
                   | |- (if ?x then _ else _) = _ => destruct x; cbn beta iota zeta
                   | |- match ?x with _ => _ end = _ => destruct x; cbn beta iota zeta
                   end ].
  - (* [comment removed for export] *)
    rewrite IH. cbn [know_lookupAF].
    destruct K as [[kb kk] w v|[kb kk] len|[kb kk] len bk|lo hi|e al|e lo hi|[kb kk] len|a1 n1 a2 n2]; cbn in R; try discriminate; try reflexivity.
    + unfold rel_lit2. rewrite R. reflexivity.
    + rewrite R. reflexivity.
    + destruct rb; try discriminate; reflexivity.
Qed.

Definition lkcache : Type := list (expr * list kentry).
Definition lkc_ok (kn : list kentry) (lc : lkcache) : Prop :=
  forall rb b, ea_lookup lc rb = Some b -> b = List.filter (lk_relevant rb) kn.
Definition lk_get (lc : lkcache) (kn : list kentry) (rb : expr) : list kentry * lkcache :=
  match ea_lookup lc rb with
  | Some b => (b, lc)
  | None => let b := List.filter (lk_relevant rb) kn in (b, (rb, b) :: lc)
  end.
Lemma lk_get_ok : forall kn lc rb, lkc_ok kn lc ->
  fst (lk_get lc kn rb) = List.filter (lk_relevant rb) kn /\ lkc_ok kn (snd (lk_get lc kn rb)).
Proof.
  intros kn lc rb H. unfold lk_get. destruct (ea_lookup lc rb) as [b|] eqn:E; cbn [fst snd].
  - split; [exact (H _ _ E) | exact H].
  - split; [reflexivity|]. intros rb' b'. cbn [ea_lookup]. destruct (expr_eqb rb' rb) eqn:E'.
    + intros X; injection X as <-. apply expr_eqb_true in E'. subst. reflexivity.
    + apply H.
Qed.
Lemma lkc_ok_nil : forall kn, lkc_ok kn [].
Proof. intros kn rb b H. discriminate. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma expr_eqb_refl0 : forall e, expr_eqb e e = true.
Proof.
  induction e; cbn; rewrite ?IHe, ?IHe1, ?IHe2, ?Z.eqb_refl, ?Nat.eqb_refl, ?N.eqb_refl; try reflexivity.
  - destruct op; reflexivity.
  - destruct op; reflexivity.
  - destruct op; reflexivity.
  - destruct op; reflexivity.
  - destruct sx; reflexivity.
  - destruct sx; cbn; rewrite ?Nat.eqb_refl, ?Z.eqb_refl; reflexivity.
Qed.
Lemma expr_eqb_sym_false0 : forall a b, expr_eqb a b = false -> expr_eqb b a = false.
Proof.
  intros a b H. destruct (expr_eqb b a) eqn:E; [|reflexivity]. apply expr_eqb_true in E. subst. rewrite expr_eqb_refl0 in H. discriminate.
Qed.
Record lgroup : Type := LG { g_base : expr; g_br : option (Z * Z); g_lo : Z; g_hi : Z; g_ents : list sentry }.
Definition lidx : Type := list lgroup.

Definition se_base (e : sentry) : expr := a_base (e_addr e).
Definition se_off (e : sentry) : Z := a_off (e_addr e).
Definition se_end (e : sentry) : Z := a_off (e_addr e) + Z.of_nat (e_width e).

Fixpoint lidx_add (fs : fdig) (e : sentry) (li : lidx) : lidx :=
  match li with
  | [] => [LG (se_base e) (base_rangeT fs (se_base e)) (se_off e) (se_end e) [e]]
  | g :: r => if expr_eqb (se_base e) (g_base g)
              then LG (g_base g) (g_br g) (Z.min (g_lo g) (se_off e)) (Z.max (g_hi g) (se_end e)) (e :: g_ents g) :: r
              else g :: lidx_add fs e r
  end.
(* [comment removed for export] *)
Fixpoint lidx_of (fs : fdig) (log : list sentry) : lidx :=
  match log with [] => [] | e :: older => lidx_add fs e (lidx_of fs older) end.

Fixpoint lfind (li : lidx) (rb : expr) : option lgroup :=
  match li with
  | [] => None
  | g :: r => if expr_eqb rb (g_base g) then Some g else lfind r rb
  end.

Definition lidx_ok (fs : fdig) (log : list sentry) (li : lidx) : Prop :=
  (forall rb, List.filter (fun e => expr_eqb rb (se_base e)) log = match lfind li rb with Some g => g_ents g | None => [] end)
  /\ Forall (fun g => g_br g = base_rangeT fs (g_base g)
                      /\ Forall (fun e => se_base e = g_base g /\ (g_lo g <= se_off e)%Z /\ (se_end e <= g_hi g)%Z) (g_ents g)) li.

Lemma lidx_ok_nil : forall fs, lidx_ok fs [] [].
Proof. intros fs. split; [intros rb; reflexivity | constructor]. Qed.

Lemma filter_cons_b : forall (A : Type) (f : A -> bool) x l, List.filter f (x :: l) = if f x then x :: List.filter f l else List.filter f l.
Proof. reflexivity. Qed.

Lemma lidx_add_ok : forall fs log li e, lidx_ok fs log li -> lidx_ok fs (e :: log) (lidx_add fs e li).
Proof.
  intros fs log li e [H1 H2]. split.
  - intros rb. rewrite filter_cons_b. rewrite H1. clear H1.
    induction H2 as [|g r [Hbr Hg] H2 IH]; cbn [lidx_add lfind g_base g_ents].
    + destruct (expr_eqb rb (se_base e)); reflexivity.
    + destruct (expr_eqb (se_base e) (g_base g)) eqn:E.
      * apply expr_eqb_true in E. cbn [lfind g_base g_ents]. rewrite <- E.
        destruct (expr_eqb rb (se_base e)); reflexivity.
      * cbn [lfind]. destruct (expr_eqb rb (g_base g)) eqn:E2.
        -- apply expr_eqb_true in E2. subst rb. rewrite expr_eqb_sym_false0 by exact E. reflexivity.
        -- exact IH.
  - clear H1. induction H2 as [|g r [Hbr Hg] H2 IH]; cbn [lidx_add].
    + constructor; [|constructor]. split; [reflexivity|]. constructor; [|constructor]. cbn. split; [reflexivity|lia].
    + destruct (expr_eqb (se_base e) (g_base g)) eqn:E.
      * apply expr_eqb_true in E. constructor; [|exact H2]. cbn. split; [exact Hbr|]. constructor.
        -- split; [exact E|lia].
        -- apply Forall_impl with (2 := Hg). intros e' (A1 & A2 & A3). split; [exact A1|lia].
      * constructor; [exact (conj Hbr Hg)|exact IH].
Qed.

Lemma lidx_of_ok : forall fs log, lidx_ok fs log (lidx_of fs log).
Proof. intros fs log. induction log as [|e older IH]; [apply lidx_ok_nil | apply lidx_add_ok; exact IH]. Qed.

(* [comment removed for export] *)
Definition lgrp_apart (thr : lthr) (g : lgroup) : bool :=
  ethr_test (mk_ethr thr (g_br g)) (g_lo g) (g_hi g - g_lo g).

(* [comment removed for export] *)
Fixpoint lgrps_ok (thr : lthr) (rb : expr) (li : lidx) : option (list sentry) :=
  match li with
  | [] => Some []
  | g :: r => if expr_eqb rb (g_base g) then match lgrps_ok thr rb r with Some _ => Some (g_ents g) | None => None end
              else if lgrp_apart thr g then lgrps_ok thr rb r else None
  end.

(* [comment removed for export] *)
Fixpoint in_sides_grp (fs : fdig) (kn : list kentry) (D : list (saddr * expr)) (g : lgroup) : bool :=
  match D with
  | [] => false
  | (c, m) :: r =>
      if (if expr_eqb (g_base g) (a_base c) then
            if Z.leb (a_off c) (g_lo g) then
              match xloF fs kn m with Some ml => Z.leb (g_hi g) (a_off c + ml) | None => false end
            else false
          else false)
      then true else in_sides_grp fs kn r g
  end.
Fixpoint lgrps_okD (fs : fdig) (kn : list kentry) (thr : lthr) (D : list (saddr * expr)) (rb : expr) (li : lidx) : option (list sentry) :=
  match li with
  | [] => Some []
  | g :: r => if expr_eqb rb (g_base g) then match lgrps_okD fs kn thr D rb r with Some _ => Some (g_ents g) | None => None end
              else if (if lgrp_apart thr g then true else in_sides_grp fs kn D g) then lgrps_okD fs kn thr D rb r else None
  end.

(* [comment removed for export] *)
Definition rel_off (rk re kk ke : Z) : rangerel :=
  if Z.leb kk rk then
    (if Z.leb re ke then RInside (rk - kk)
     else if Z.leb re kk then RDisjoint else if Z.leb ke rk then RDisjoint else RPartial)
  else (if Z.leb re kk then RDisjoint else if Z.leb ke rk then RDisjoint else RPartial).
Lemma rel_off_eq : forall rb rk re kk ke, rel_off rk re kk ke = rel_lit2 rb rk re rb kk ke.
Proof. intros. unfold rel_off, rel_lit2. rewrite expr_eqb_refl0. reflexivity. Qed.

Fixpoint scan_same (rk re : Z) (n : nat) (sx : bool) (acc : list sidecond) (ents : list sentry) : lres :=
  match ents with
  | [] => LMiss acc []
  | SE (SA _ kk) w v :: rest =>
      match rel_off rk re kk (kk + Z.of_nat w) with
      | RInside d => LHit (mkExtF sx (Z.to_nat d) n v) acc []
      | RDisjoint => scan_same rk re n sx acc rest
      | _ => LStuck
      end
  end.

Definition log_lookupG (fs : fdig) (kn : list kentry) (li : lidx) (log : list sentry) (rb : expr) (rk : Z) (n : nat) (zn re : Z)
           (sx : bool) (acc : list sidecond) : lres :=
  match log with
  | [] => LMiss acc []
  | _ =>
      let thr := mk_lthr fs rb rk zn in
      match lgrps_ok thr rb li with
      | Some ents => scan_same rk re n sx acc ents
      | None =>
          let D := disj_sidesF fs kn kn rb rk zn in
          match lgrps_okD fs kn thr D rb li with
          | Some ents => scan_same rk re n sx acc ents
          | None => log_lookupL fs kn log rb rk n zn re sx [] acc (Some thr) (Some D) []
          end
      end
  end.

(* [comment removed for export] *)
Lemma log_lookupF_same : forall fs kn log rb rk n sx acc,
  (forall e, In e log -> expr_eqb rb (se_base e) = false ->
             ranges_apartF fs kn rb rk (Z.of_nat n) (se_base e) (se_off e) (Z.of_nat (e_width e)) = true) ->
  log_lookupF fs kn log rb rk n sx [] acc
  = scan_same rk (rk + Z.of_nat n) n sx acc (List.filter (fun e => expr_eqb rb (se_base e)) log).
Proof.
  intros fs kn log rb rk n sx acc. induction log as [|[[kb kk] w v] rest IH]; intros HA; [reflexivity|].
  cbn [log_lookupF List.filter se_base e_addr a_base].
  assert (HA' : forall e, In e rest -> expr_eqb rb (se_base e) = false ->
            ranges_apartF fs kn rb rk (Z.of_nat n) (se_base e) (se_off e) (Z.of_nat (e_width e)) = true)
    by (intros e He; apply HA; right; exact He).
  destruct (expr_eqb rb kb) eqn:E.
  - apply expr_eqb_true in E. subst kb. cbn [scan_same].
    rewrite (rel_off_eq rb), rel_lit2_eq.
    destruct (rel_lit rb rk (Z.of_nat n) rb kk (Z.of_nat w)) eqn:R; rewrite ?mkExtF_eq; try reflexivity.
    + apply IH. exact HA'.
    + exfalso. unfold rel_lit in R. rewrite expr_eqb_refl0 in R.
      destruct (Z.leb kk rk && Z.leb (rk + Z.of_nat n) (kk + Z.of_nat w))%bool; [discriminate|].
      destruct (Z.leb (rk + Z.of_nat n) kk || Z.leb (kk + Z.of_nat w) rk)%bool; discriminate.
  - assert (R : rel_lit rb rk (Z.of_nat n) kb kk (Z.of_nat w) = RUnknown) by (unfold rel_lit; rewrite E; reflexivity).
    rewrite R. pose proof (HA (SE (SA kb kk) w v) (or_introl eq_refl) E) as HAe. cbn [se_base se_off e_addr a_base a_off e_width] in HAe.
    rewrite HAe. apply IH. exact HA'.
Qed.

Lemma lgrps_ok_sound : forall fs li thr rb ents,
  Forall (fun g => g_br g = base_rangeT fs (g_base g)
                   /\ Forall (fun e => se_base e = g_base g /\ (g_lo g <= se_off e)%Z /\ (se_end e <= g_hi g)%Z) (g_ents g)) li ->
  lgrps_ok thr rb li = Some ents ->
  ents = match lfind li rb with Some g => g_ents g | None => [] end
  /\ forall g, In g li -> expr_eqb rb (g_base g) = false ->
       forall e, In e (g_ents g) -> lthr_test thr (base_rangeT fs (se_base e)) (se_off e) (Z.of_nat (e_width e)) = true.
Proof.
  intros fs li thr rb. induction li as [|g r IH]; intros ents Hli H.
  - cbn in H. injection H as <-. split; [reflexivity|]. intros g [].
  - apply Forall_cons_iff in Hli as [[Hbr Hg] Hr]. cbn [lgrps_ok lfind] in H |- *.
    destruct (expr_eqb rb (g_base g)) eqn:E.
    + destruct (lgrps_ok thr rb r) as [ents'|] eqn:H'; [|discriminate]. injection H as <-.
      destruct (IH ents' Hr eq_refl) as [_ IH2]. split; [reflexivity|].
      intros g0 [<-|Hin]; [rewrite E; discriminate|]. exact (IH2 g0 Hin).
    + destruct (lgrp_apart thr g) eqn:GA; [|discriminate].
      destruct (IH ents Hr H) as [IH1 IH2]. split; [exact IH1|].
      intros g0 [<-|Hin]; [|exact (IH2 g0 Hin)]. intros _ e He.
      pose proof (proj1 (Forall_forall _ _) Hg e He) as (B1 & B2 & B3). unfold se_end, se_off in B2, B3 |- *.
      rewrite B1, <- Hbr, <- ethr_test_eq.
      unfold lgrp_apart in GA. unfold ethr_test in GA |- *.
      destruct (mk_ethr thr (g_br g)) as [[tA tB]|]; [|discriminate].
      apply Bool.orb_true_iff in GA. apply Bool.orb_true_iff.
      destruct GA as [GA|GA].
      * left. apply Z.leb_le in GA. apply Z.leb_le. lia.
      * right. apply Z.leb_le in GA. apply Z.leb_le. lia.
Qed.

Lemma in_sides_grp_sound : forall fs kn D g e,
  in_sides_grp fs kn D g = true ->
  se_base e = g_base g -> (g_lo g <= se_off e)%Z -> (se_end e <= g_hi g)%Z ->
  in_sidesF fs kn D (se_base e) (se_off e) (Z.of_nat (e_width e)) = true.
Proof.
  intros fs kn D g e. induction D as [|[c m] r IH]; intros H B1 B2 B3; [discriminate|].
  cbn [in_sides_grp in_sidesF] in H |- *.
  match type of H with (if ?cnd then true else _) = true => destruct cnd eqn:C end.
  - assert (S1 : sub_itvF fs kn (se_base e) (se_off e) (Z.of_nat (e_width e)) c m = true).
    { unfold sub_itvF. rewrite B1. unfold se_end, se_off in B2, B3 |- *.
      destruct (expr_eqb (g_base g) (a_base c)); [|discriminate].
      destruct (Z.leb_spec (a_off c) (g_lo g)); [|discriminate].
      destruct (xloF fs kn m) as [ml|]; [|discriminate].
      destruct (Z.leb_spec (g_hi g) (a_off c + ml)); [|discriminate].
      cbn [andb]. destruct (Z.leb_spec (a_off c) (a_off (e_addr e))); [|lia]. cbn [andb].
      destruct (Z.leb_spec (a_off (e_addr e) + Z.of_nat (e_width e)) (a_off c + ml)); [reflexivity|lia]. }
    rewrite S1. reflexivity.
  - rewrite (IH H B1 B2 B3). destruct (sub_itvF _ _ _ _ _ _ _); reflexivity.
Qed.

Lemma lgrps_okD_sound : forall fs kn li thr D rb ents,
  Forall (fun g => g_br g = base_rangeT fs (g_base g)
                   /\ Forall (fun e => se_base e = g_base g /\ (g_lo g <= se_off e)%Z /\ (se_end e <= g_hi g)%Z) (g_ents g)) li ->
  lgrps_okD fs kn thr D rb li = Some ents ->
  ents = match lfind li rb with Some g => g_ents g | None => [] end
  /\ forall g, In g li -> expr_eqb rb (g_base g) = false ->
       forall e, In e (g_ents g) ->
         lthr_test thr (base_rangeT fs (se_base e)) (se_off e) (Z.of_nat (e_width e)) = true
         \/ in_sidesF fs kn D (se_base e) (se_off e) (Z.of_nat (e_width e)) = true.
Proof.
  intros fs kn li thr D rb. induction li as [|g r IH]; intros ents Hli H.
  - cbn in H. injection H as <-. split; [reflexivity|]. intros g [].
  - apply Forall_cons_iff in Hli as [[Hbr Hg] Hr]. cbn [lgrps_okD lfind] in H |- *.
    destruct (expr_eqb rb (g_base g)) eqn:E.
    + destruct (lgrps_okD fs kn thr D rb r) as [ents'|] eqn:H'; [|discriminate]. injection H as <-.
      destruct (IH ents' Hr eq_refl) as [_ IH2]. split; [reflexivity|].
      intros g0 [<-|Hin]; [rewrite E; discriminate|]. exact (IH2 g0 Hin).
    + match type of H with (if ?cnd then _ else _) = _ => destruct cnd eqn:GA end; [|discriminate].
      destruct (IH ents Hr H) as [IH1 IH2]. split; [exact IH1|].
      intros g0 [<-|Hin]; [|exact (IH2 g0 Hin)]. intros _ e He.
      pose proof (proj1 (Forall_forall _ _) Hg e He) as (B1 & B2 & B3).
      destruct (lgrp_apart thr g) eqn:GT.
      * left. unfold se_end, se_off in B2, B3 |- *.
        rewrite B1, <- Hbr, <- ethr_test_eq.
        unfold lgrp_apart in GT. unfold ethr_test in GT |- *.
        destruct (mk_ethr thr (g_br g)) as [[tA tB]|]; [|discriminate].
        apply Bool.orb_true_iff in GT. apply Bool.orb_true_iff.
        destruct GT as [GT|GT].
        -- left. apply Z.leb_le in GT. apply Z.leb_le. lia.
        -- right. apply Z.leb_le in GT. apply Z.leb_le. lia.
      * right. exact (in_sides_grp_sound fs kn D g e GA B1 B2 B3).
Qed.

Lemma log_lookupG_eq : forall fs kn li log rb rk n sx acc,
  lidx_ok fs log li ->
  log_lookupG fs kn li log rb rk n (Z.of_nat n) (rk + Z.of_nat n) sx acc
  = log_lookupL fs kn log rb rk n (Z.of_nat n) (rk + Z.of_nat n) sx [] acc None None [].
Proof.
  intros fs kn li log rb rk n sx acc [H1 H2]. unfold log_lookupG.
  destruct log as [|e0 log'] eqn:EL; [reflexivity|]. rewrite <- EL in *. clear EL e0 log'.
  (* [comment removed for export] *)
  assert (GRP : forall e, In e log -> expr_eqb rb (se_base e) = false ->
            exists g, In g li /\ expr_eqb rb (g_base g) = false /\ In e (g_ents g)).
  { intros e He E.
    assert (Hf : In e (List.filter (fun e' => expr_eqb (se_base e) (se_base e')) log))
      by (apply filter_In; split; [exact He | apply expr_eqb_refl0]).
    rewrite H1 in Hf.
    destruct (lfind li (se_base e)) as [g|] eqn:L; [|destruct Hf].
    assert (Hg : In g li /\ expr_eqb (se_base e) (g_base g) = true).
    { clear -L. induction li as [|g0 r IH]; cbn [lfind] in L; [discriminate|].
      destruct (expr_eqb (se_base e) (g_base g0)) eqn:E0.
      - injection L as <-. split; [left; reflexivity | exact E0].
      - destruct (IH L) as [A B]. split; [right; exact A | exact B]. }
    destruct Hg as [Hin Eg]. apply expr_eqb_true in Eg.
    exists g. split; [exact Hin|]. split; [rewrite <- Eg; exact E | exact Hf]. }
  cbv zeta.
  destruct (lgrps_ok (mk_lthr fs rb rk (Z.of_nat n)) rb li) as [ents|] eqn:G.
  - rewrite log_lookupL_eq; [|left; reflexivity|left; reflexivity|intros b r Hb; discriminate].
    destruct (lgrps_ok_sound fs li _ rb ents H2 G) as [Hents Hap].
    rewrite log_lookupF_same; [rewrite H1, <- Hents; reflexivity|].
    intros e He E. destruct (GRP e He E) as (g & Hin & Efg & Heg).
    rewrite <- ranges_apart_stagedF_eq. rewrite (Hap g Hin Efg e Heg). reflexivity.
  - destruct (lgrps_okD fs kn (mk_lthr fs rb rk (Z.of_nat n)) (disj_sidesF fs kn kn rb rk (Z.of_nat n)) rb li) as [ents|] eqn:GD.
    + rewrite log_lookupL_eq; [|left; reflexivity|left; reflexivity|intros b r Hb; discriminate].
      destruct (lgrps_okD_sound fs kn li _ _ rb ents H2 GD) as [Hents Hap].
      rewrite log_lookupF_same; [rewrite H1, <- Hents; reflexivity|].
      intros e He E. destruct (GRP e He E) as (g & Hin & Efg & Heg).
      rewrite <- ranges_apart_stagedF_eq.
      destruct (Hap g Hin Efg e Heg) as [T|S]; [rewrite T; reflexivity|].
      unfold ranges_apart_restF. rewrite S. destruct (lthr_test _ _ _ _); reflexivity.
    + rewrite (log_lookupL_eq fs kn log rb rk n sx [] acc (Some _) (Some _) []); [|right; reflexivity | right; reflexivity | intros b r Hb; discriminate].
      symmetry. apply log_lookupL_eq; [left; reflexivity | left; reflexivity | intros b r Hb; discriminate].
Qed.

(* [comment removed for export] *)
Definition lidx_next (fs : fdig) (i : instr) (ss' : sym_state) (li : lidx) : lidx :=
  match i with
  | Store _ _ _ _ => match s_log ss' with e :: _ => lidx_add fs e li | [] => li end
  | _ => li
  end.

Definition sym_stepFM (fk : list kentry) (fs : fdig) (segs : list Segment) (i : instr) (ss : sym_state) (scr : scripts) (m : smemo) (lc : lkcache) (li : lidx)
  : stepres * smemo * lkcache :=
  let g r := sr_get (s_regs ss) r in
  let p := s_pc ss in
  match i with
  | OpImm op rd rs imm => let '(e, m) := mkAluKM fs fk op (g rs) (ELit (sbv12 imm)) m in (SOk (sset ss rd e (p + 4)) [] scr, m, lc)
  | ShiftImm op rd rs sh => let '(e, m) := mkAluKM fs fk op (g rs) (ELit (bv_unsigned sh)) m in (SOk (sset ss rd e (p + 4)) [] scr, m, lc)
  | Op op rd rs1 rs2 => let '(e, m) := mkAluKM fs fk op (g rs1) (g rs2) m in (SOk (sset ss rd e (p + 4)) [] scr, m, lc)
  | OpImm32 rd rs imm => let '(e, m) := mkAluwKM fs fk ALU_ADD (g rs) (ELit (sbv12 imm)) m in (SOk (sset ss rd e (p + 4)) [] scr, m, lc)
  | ShiftImm32 op rd rs sh => (SOk (sset ss rd (mkAluw op (g rs) (ELit (bv_unsigned sh))) (p + 4)) [] scr, m, lc)
  | Op32 op rd rs1 rs2 => let '(e, m) := mkAluwKM fs fk op (g rs1) (g rs2) m in (SOk (sset ss rd e (p + 4)) [] scr, m, lc)
  | Mul op rd rs1 rs2 => (SOk (sset ss rd (mkMd op (g rs1) (g rs2)) (p + 4)) [] scr, m, lc)
  | Mul32 op rd rs1 rs2 => (SOk (sset ss rd (mkMdw op (g rs1) (g rs2)) (p + 4)) [] scr, m, lc)
  | Lui rd imm => (SOk (sset ss rd (ELit (zmod64 (Z.shiftl (sbv20 imm) 12))) (p + 4)) [] scr, m, lc)
  | Auipc rd imm => (SOk (sset ss rd (ELit (zmod64 (Z.shiftl (sbv20 imm) 12 + p))) (p + 4)) [] scr, m, lc)
  | Jal rd imm => (SOk (sset ss rd (ELit (p + 4)) (zmod64 (p + sbv21 imm))) [] scr, m, lc)
  | Jalr rd rs1 imm =>
      let '(ce, m) := conc_exprM fs fk (g rs1) m in
      (match ce with
       | ELit z => SOk (sset ss rd (ELit (p + 4)) (zmod64 (Z.land (zmod64 z + sbv12 imm) (-2)))) [] scr
       | _ => SStop
       end, m, lc)
  | Branch c rs1 rs2 imm =>
      let tk := zmod64 (p + sbv13 imm) in
      let a := g rs1 in let b := g rs2 in
      let '(d, m) := match decide_branchT fs fk c a b with
                     | Some t => (Some t, m)
                     | None => let '(ca, m) := conc_exprM fs fk a m in
                               let '(cb, m) := conc_exprM fs fk b m in
                               match decide_branchT fs fk c ca cb with
                               | Some t => (Some t, m)
                               | None => enum_branchM fs fk c a b m
                               end
                     end in
      (match d with
       | Some t => SOk (sjump ss (if t then tk else p + 4)) [] scr
       | None =>
           match sc_dirs scr with
           | [] => SStop
           | t :: dirs' =>
               SOk (sjump ss (if t then tk else p + 4)) [SCBr t c a b]
                   (SCR dirs' (sc_reads scr) (sc_hints scr))
           end
       end, m, lc)
  | Fence _ _ _ _ _ => (SOk (sjump ss (p + 4)) [] scr, m, lc)
  | FenceI _ _ _ => (SOk (sjump ss (p + 4)) [] scr, m, lc)
  | Load sz sx rd rs imm =>
      let n := msize_bytes sz in let zn := Z.of_nat n in
      let sx' := match sz with SZ8 => false | _ => sx end in
      let '(a, m) := to_saddrKM fs fk (g rs) (sbv12 imm) m in
      match (match sc_hints scr with
             | [] => log_lookupG fs fk li (s_log ss) (a_base a) (a_off a) n zn (a_off a + zn) sx' []
             | _ => log_lookupL fs fk (s_log ss) (a_base a) (a_off a) n zn (a_off a + zn) sx' (sc_hints scr) [] None None []
             end) with
      | LStuck => (SStop, m, lc)
      | LHit v scs hints =>
          let '(ev, m) := extKM fs fk v m in
          (SOk (sset ss rd ev (p + 4)) (flat_scT fs fk a n ++ scs) (SCR (sc_dirs scr) (sc_reads scr) hints), m, lc)
      | LMiss scs hints =>
          let '(bkt, lc) := lk_get lc (s_know ss) (a_base a) in
          match know_lookupAF fs fk segs bkt (a_base a) (a_off a) n zn (a_off a + zn) sx' hints scs with
          | LStuck => (SStop, m, lc)
          | LHit v scs' hints' =>
              let '(ev, m) := extKM fs fk v m in
              (SOk (sset ss rd ev (p + 4)) (flat_scT fs fk a n ++ scs') (SCR (sc_dirs scr) (sc_reads scr) hints'), m, lc)
          | LMiss scs' hints' =>
              let i := s_next ss in
              let rv := match sc_reads scr with [] => EVar i | e :: _ => e end in
              let reads' := match sc_reads scr with [] => [] | _ :: t => t end in
              (SOk (SS (p + 4)
                      (if bv_eqb rd 0 then s_regs ss else sr_upd (s_regs ss) (ridx rd) rv)
                      (s_log ss) (s_know ss) (N.succ i))
                  (flat_scT fs fk a n ++ SCReadBase a n sx' rv :: scs')
                  (SCR (sc_dirs scr) reads' hints'), m, lc)
          end
      end
  | Store sz rs1 rs2 imm =>
      let n := msize_bytes sz in
      let '(a, m) := to_saddrKM fs fk (g rs1) (sbv12 imm) m in
      (SOk (SS (p + 4) (s_regs ss) (SE a n (g rs2) :: s_log ss) (s_know ss) (s_next ss))
          (flat_scT fs fk a n ++ storeok_scF fs fk a n) scr, m, lc)
  | _ => (SStop, m, lc)
  end.

Ltac smemo_step L :=
  lazymatch goal with
  | Hm : smemo_ok ?m |- context [L] => idtac
  end.
(* [comment removed for export] *)
Ltac mstep t L Hm :=
  let H1 := fresh "HM" in let H2 := fresh "HM" in
  pose proof (L Hm) as [H1 H2]; destruct t as [? ?]; cbn [fst snd] in H1, H2; subst.

Lemma sym_stepFM_eq : forall fk fs segs i ss scr m lc li, smemo_ok m -> lkc_ok (s_know ss) lc -> lidx_ok fs (s_log ss) li ->
  fst (fst (sym_stepFM fk fs segs i ss scr m lc li)) = sym_stepF fk fs segs i ss scr
  /\ smemo_ok (snd (fst (sym_stepFM fk fs segs i ss scr m lc li))) /\ lkc_ok (s_know ss) (snd (sym_stepFM fk fs segs i ss scr m lc li)).
Proof.
  intros fk fs segs i ss scr m lc li Hm Hl Hli. unfold sym_stepFM, sym_stepF.
  destruct i; try (split; [reflexivity | split; [exact Hm | exact Hl]]).
  all: repeat first
    [ split; [reflexivity | split; assumption]
    | match goal with
      | H : smemo_ok ?m1 |- context [mkAluKM ?X ?Y ?op ?a ?b ?m1] => mstep (mkAluKM X Y op a b m1) (mkAluKM_eq X Y op a b m1) H
      | H : smemo_ok ?m1 |- context [mkAluwKM ?X ?Y ?op ?a ?b ?m1] => mstep (mkAluwKM X Y op a b m1) (mkAluwKM_eq X Y op a b m1) H
      | H : smemo_ok ?m1 |- context [conc_exprM ?X ?Y ?b ?m1] => mstep (conc_exprM X Y b m1) (conc_exprM_eq X Y b m1) H
      | H : smemo_ok ?m1 |- context [enum_branchM ?X ?Y ?c ?a ?b ?m1] => mstep (enum_branchM X Y c a b m1) (enum_branchM_eq X Y c a b m1) H
      | H : smemo_ok ?m1 |- context [to_saddrKM ?X ?Y ?e ?k ?m1] => mstep (to_saddrKM X Y e k m1) (to_saddrKM_eq X Y e k m1) H
      | H : smemo_ok ?m1 |- context [extKM ?X ?Y ?v ?m1] => mstep (extKM X Y v m1) (extKM_eq X Y v m1) H
      | H : lkc_ok ?kn ?lc1 |- context [lk_get ?lc1 ?kn ?rb] =>
          let H1 := fresh "HL" in let H2 := fresh "HL" in
          pose proof (lk_get_ok kn lc1 rb H) as [H1 H2]; destruct (lk_get lc1 kn rb) as [? ?]; cbn [fst snd] in H1, H2; subst;
          rewrite know_lookupAF_bucket
      | H : lidx_ok ?f ?lg ?li1 |- context [log_lookupG ?f ?a2 ?li1 ?lg ?a5 ?a6 ?a7 ?a8 ?a9 ?a10 ?a11] =>
          rewrite (log_lookupG_eq f a2 li1 lg a5 a6 a7 a10 a11 H)
      | |- context [match sc_hints ?sc with _ => _ end] => destruct (sc_hints sc)
      | |- context [log_lookupL ?a1 ?a2 ?a3 ?a4 ?a5 ?a6 ?a7 ?a8 ?a9 ?a10 ?a11 ?a12 ?a13 ?a14] =>
          destruct (log_lookupL a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14) as [? ? ?|? ?|]
      | |- context [know_lookupAF ?a1 ?a2 ?a3 ?a4 ?a5 ?a6 ?a7 ?a8 ?a9 ?a10 ?a11 ?a12] =>
          destruct (know_lookupAF a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12) as [? ? ?|? ?|]
      | |- context [match decide_branchT ?X ?Y ?c ?a ?b with _ => _ end] => destruct (decide_branchT X Y c a b)
      end ].
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
Fixpoint sym_execTF (fk : list kentry) (fs : fdig) (t : itab) (fuel : nat) (first : bool) (stops : list Z)
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
Fixpoint sym_execTFM (fk : list kentry) (fs : fdig) (t : itab) (fuel : nat) (first : bool) (stops : list Z)
         (ss : sym_state) (m : smemo) (lc : lkcache) (li : lidx) : sym_state * smemo * lkcache :=
  match fuel with
  | O => (ss, m, lc)
  | S f =>
      if (negb first && existsb (Z.eqb (s_pc ss)) stops)%bool then (ss, m, lc) else
      match itab_lookup t (s_pc ss) with
      | None => (ss, m, lc)
      | Some i =>
          let '(r, m, lc) := sym_stepFM fk fs segs i ss scr_nil m lc li in
          match r with
          | SOk ss' [] _ => sym_execTFM fk fs t f false stops ss' m lc (lidx_next fs i ss' li)
          | _ => (ss, m, lc)
          end
      end
  end.
(* [comment removed for export] *)
Lemma sym_stepF_know : forall fk fs i ss scr ss' scs scr',
  sym_stepF fk fs segs i ss scr = SOk ss' scs scr' -> s_know ss' = s_know ss.
Proof.
  intros fk fs i ss scr ss' scs scr' H. unfold sym_stepF in H.
  destruct i; try discriminate;
  repeat (lazymatch type of H with
          | SOk _ _ _ = SOk _ _ _ => injection H as <- _ _
          | (match ?x with _ => _ end) = _ => destruct x
          | (let (_, _) := ?x in _) = _ => destruct x
          | (if ?x then _ else _) = _ => destruct x
          end); try discriminate; try reflexivity.
Qed.
(* [comment removed for export] *)
Lemma sym_stepF_lidx : forall fk fs i ss scr ss' scs scr' li,
  sym_stepF fk fs segs i ss scr = SOk ss' scs scr' -> lidx_ok fs (s_log ss) li ->
  lidx_ok fs (s_log ss') (lidx_next fs i ss' li).
Proof.
  intros fk fs i ss scr ss' scs scr' li H Hli. unfold sym_stepF in H.
  destruct i; try discriminate;
  repeat (lazymatch type of H with
          | SOk _ _ _ = SOk _ _ _ => injection H as <- _ _
          | (match ?x with _ => _ end) = _ => destruct x
          | (let (_, _) := ?x in _) = _ => destruct x
          | (if ?x then _ else _) = _ => destruct x
          end); try discriminate; cbn [lidx_next s_log sset sjump]; try exact Hli.
  all: apply lidx_add_ok; exact Hli.
Qed.
Lemma sym_execTFM_eq : forall fk fs t fuel first stops ss m lc li, smemo_ok m -> lkc_ok (s_know ss) lc -> lidx_ok fs (s_log ss) li ->
  fst (fst (sym_execTFM fk fs t fuel first stops ss m lc li)) = sym_execTF fk fs t fuel first stops ss
  /\ smemo_ok (snd (fst (sym_execTFM fk fs t fuel first stops ss m lc li))).
Proof.
  intros fk fs t fuel. induction fuel as [|f IH]; intros first stops ss m lc li Hm Hl Hli; [split; [reflexivity|exact Hm]|].
  cbn [sym_execTFM sym_execTF].
  destruct (negb first && existsb (Z.eqb (s_pc ss)) stops)%bool; [split; [reflexivity|exact Hm]|].
  destruct (itab_lookup t (s_pc ss)) as [i|]; [|split; [reflexivity|exact Hm]].
  pose proof (sym_stepFM_eq fk fs segs i ss scr_nil m lc li Hm Hl Hli) as [H1 [H2 H3]].
  destruct (sym_stepFM fk fs segs i ss scr_nil m lc li) as [[r m1] lc1]. cbn [fst snd] in H1, H2, H3. subst r.
  destruct (sym_stepF fk fs segs i ss scr_nil) as [ss' [|? ?] scr'|] eqn:Hs; try (split; [reflexivity|exact H2]).
  apply IH; [exact H2| |].
  - rewrite (sym_stepF_know _ _ _ _ _ _ _ _ Hs). exact H3.
  - exact (sym_stepF_lidx _ _ _ _ _ _ _ _ li Hs Hli).
Qed.
Definition sym_execT'M (t : itab) (fuel : nat) (first : bool) (stops : list Z) (ss : sym_state) (m : smemo) : sym_state * smemo :=
  let fk := facts_of (s_know ss) in let fs := SFS fk in fst (sym_execTFM fk fs t fuel first stops ss m [] (lidx_of fs (s_log ss))).
Lemma sym_execT'M_eq : forall t fuel first stops ss m, smemo_ok m ->
  fst (sym_execT'M t fuel first stops ss m) = sym_execT' t fuel first stops ss /\ smemo_ok (snd (sym_execT'M t fuel first stops ss m)).
Proof. intros. unfold sym_execT'M, sym_execT'. apply sym_execTFM_eq; [assumption | apply lkc_ok_nil | apply lidx_of_ok]. Qed.
Lemma smemo_ok_nil : smemo_ok [].
Proof. constructor. Qed.

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

Local Open Scope Z_scope.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Inductive xkind : Type := XKNever | XKNum (u v : Z) | XKShare.

Record sdesc : Type := SD {
  sd_c : saddr; sd_m : expr;   (* [comment removed for export] *)
  sd_same : bool;              (* [comment removed for export] *)
  sd_lim : option Z;           (* [comment removed for export] *)
  sd_kind : xkind }.

Definition mk_sd (fs : fdig) (fk : list kentry) (b : expr) (br : option (Z * Z)) (c : saddr) (m : expr) : sdesc :=
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

Definition mk_sdi (fs : fdig) (fk : list kentry) (c : saddr) (m : expr) : sideinfo :=
  let cb := a_base c in
  SDI c m (xloF fs fk m) (novars cb)
      (if novars cb then
         match xloF fs fk cb, xhiF fs fk cb with
         | Some lo2, Some hi2 => if Z.eqb lo2 hi2 then Some lo2 else None
         | _, _ => None
         end
       else None).

(* [comment removed for export] *)
Definition mk_sd' (fs : fdig) (fk : list kentry) (b : expr) (br : option (Z * Z)) (d : sideinfo) : sdesc :=
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

Fixpoint kdisj_sdis (fs : fdig) (fk : list kentry) (kn : list kentry) : list (sideinfo * sideinfo) :=
  match kn with
  | [] => []
  | KDisj c1 m1 c2 m2 :: r => (mk_sdi fs fk c1 m1, mk_sdi fs fk c2 m2) :: kdisj_sdis fs fk r
  | _ :: r => kdisj_sdis fs fk r
  end.

(* [comment removed for export] *)
Lemma expr_eqb_refl : forall e, expr_eqb e e = true.
Proof.
  induction e; cbn; rewrite ?IHe, ?IHe1, ?IHe2, ?Z.eqb_refl, ?Nat.eqb_refl, ?N.eqb_refl; try reflexivity.
  - destruct op; reflexivity.
  - destruct op; reflexivity.
  - destruct op; reflexivity.
  - destruct op; reflexivity.
  - destruct sx; reflexivity.
  - destruct sx; cbn; rewrite ?Nat.eqb_refl, ?Z.eqb_refl; reflexivity.
Qed.
(* [comment removed for export] *)
Fixpoint distinctE (ts : list (Z * expr)) : Prop :=
  match ts with
  | [] => True
  | (_, a) :: r => (forall k' a', In (k', a') r -> expr_eqb a' a = false) /\ distinctE r
  end.
Lemma lins_e_In : forall k a ts k' a', In (k', a') (lins_e k a ts) -> (exists k'', In (k'', a') ts) \/ a' = a.
Proof.
  intros k a ts. induction ts as [|[k0 a0] r IH]; intros k' a' H; cbn [lins_e] in H.
  - destruct (Z.eqb k 0); [destruct H|]. destruct H as [H|[]]. injection H as _ <-. right; reflexivity.
  - destruct (expr_eqb a a0) eqn:E.
    + destruct (Z.eqb (k + k0) 0).
      * left. exists k'. right. exact H.
      * destruct H as [H|H]; [injection H as _ <-; left; exists k0; left; reflexivity|]. left. exists k'. right. exact H.
    + destruct H as [H|H]; [injection H as _ <-; left; exists k0; left; reflexivity|].
      destruct (IH _ _ H) as [[k'' Hin]| ->]; [left; exists k''; right; exact Hin | right; reflexivity].
Qed.
Lemma lins_e_distinct : forall k a ts, distinctE ts -> distinctE (lins_e k a ts).
Proof.
  intros k a ts. induction ts as [|[k0 a0] r IH]; intros Hd; cbn [lins_e].
  - destruct (Z.eqb k 0); cbn; [exact I|]. split; [intros ? ? []|exact I].
  - destruct Hd as [Hhd Hr]. destruct (expr_eqb a a0) eqn:E.
    + destruct (Z.eqb (k + k0) 0); [exact Hr|]. split; [exact Hhd|exact Hr].
    + split; [|exact (IH Hr)]. intros k' a' Hin. destruct (lins_e_In _ _ _ _ _ Hin) as [[k'' Hin']| ->].
      * exact (Hhd _ _ Hin').
      * exact E.
Qed.
Lemma xt_lin1_distinct : forall e k, distinctE (xt_lin [(e, k)]).
Proof.
  intros e k. cbn [xt_lin]. induction (snd (lin_of e)) as [|t r IH]; cbn [fold_right]; [exact I|].
  apply lins_e_distinct. exact IH.
Qed.
Lemma lins_e_cancel : forall P k a, (forall k' a', In (k', a') P -> expr_eqb a a' = false) -> lins_e (- k) a (P ++ [(k, a)]) = P.
Proof.
  induction P as [|[k0 a0] r IH]; intros k a H; cbn [lins_e app].
  - rewrite expr_eqb_refl. replace (- k + k) with 0 by lia. reflexivity.
  - rewrite (H k0 a0 (or_introl eq_refl)). rewrite IH; [reflexivity|]. intros k' a' Hin. apply (H k'). right. exact Hin.
Qed.
Lemma expr_eqb_sym_false : forall a b, expr_eqb a b = false -> expr_eqb b a = false.
Proof.
  intros a b H. destruct (expr_eqb b a) eqn:E; [|reflexivity]. apply expr_eqb_true in E. subst. rewrite expr_eqb_refl in H. discriminate.
Qed.
Lemma distinct_split : forall P k a S', distinctE (P ++ (k, a) :: S') -> forall k' a', In (k', a') P -> expr_eqb a a' = false.
Proof.
  induction P as [|[k0 a0] P' IH]; intros k a S' HT k' a' Hin; [destruct Hin|].
  cbn [app distinctE] in HT. destruct HT as [Hhd Hr]. destruct Hin as [Hp|Hin].
  - injection Hp as <- <-. apply (Hhd k a). apply in_app_iff. right. left. reflexivity.
  - exact (IH k a S' Hr k' a' Hin).
Qed.
Lemma lsub_e_self : forall T, distinctE T -> lsub_e T T = [].
Proof.
  intros T HT. unfold lsub_e.
  assert (G : forall S P, T = P ++ S -> fold_right (fun t acc => lins_e (- fst t) (snd t) acc) T S = P).
  { induction S as [|[k a] S' IH]; intros P E.
    - cbn. rewrite app_nil_r in E. exact E.
    - cbn [fold_right fst snd]. rewrite (IH (P ++ [(k, a)])) by (rewrite <- app_assoc; exact E).
      apply lins_e_cancel. intros k' a' Hin. apply (distinct_split P k a S' ltac:(rewrite <- E; exact HT) k' a' Hin). }
  exact (G T [] eq_refl).
Qed.

Definition ss_fast (fs : fdig) (fk : list kentry) (b : expr) (ck k zn zm : Z) : bool :=
  if Z.leb ck k then
    if Z.leb (k + snorm zn) (ck + snorm zm) then
      if lin_nowrapRF fs fk b then if lin_nowrapRF fs fk (ELit zm) then lin_nowrapRF fs fk (ELit zn) else false else false
    else false
  else false.
Lemma lin_testF_nil_ge0 : forall fs kn c, 0 <= c -> lin_testF fs kn c [] (fun lo _ => Z.leb 0 lo) = true.
Proof.
  intros fs kn c Hc. unfold lin_testF. cbn [lin_range]. destruct (Z.leb_spec 0 c); [reflexivity|lia].
Qed.
Lemma ss_fast_sound : forall fs fk b ck k zn zm,
  ss_fast fs fk b ck k zn zm = true -> xinside0F fs fk b k (ELit zn) b ck (ELit zm) = true.
Proof.
  intros fs fk b ck k zn zm H. unfold ss_fast in H.
  destruct (Z.leb_spec ck k) as [H1|]; [|discriminate].
  destruct (Z.leb_spec (k + snorm zn) (ck + snorm zm)) as [H2|]; [|discriminate].
  destruct (lin_nowrapRF fs fk b) eqn:NB; [|discriminate].
  destruct (lin_nowrapRF fs fk (ELit zm)) eqn:NM; [|discriminate].
  rename H into NN.
  unfold xinside0F, lin_ge0F. cbn [xt_nowrapF]. rewrite NB, NM, NN.
  change (xt_lin [(b, ck)]) with (xt_lin [(b, k)]).
  change (xt_lin [(b, ck); (ELit zm, 0)]) with (xt_lin [(b, k)]).
  change (xt_lin [(b, k); (ELit zn, 0)]) with (xt_lin [(b, k)]).
  rewrite (lsub_e_self _ (xt_lin1_distinct b k)).
  rewrite !lin_testF_nil_ge0; [reflexivity| |]; cbn [xt_const lin_of fst snd]; lia.
Qed.

(* [comment removed for export] *)
Definition xk_eval (fs : fdig) (fk : list kentry) (b : expr) (d : sdesc) (k : Z) (n : expr) (h : option Z) : bool :=
  match sd_kind d with
  | XKNever => false
  | XKNum u v => match h with Some hv => (Z.leb u k && Z.leb (k + hv) v)%bool | None => false end
  | XKShare =>
      if (if sd_same d then match n, sd_m d with ELit zn, ELit zm => ss_fast fs fk b (a_off (sd_c d)) k zn zm | _, _ => false end else false)
      then true else xinside0F fs fk b k n (a_base (sd_c d)) (a_off (sd_c d)) (sd_m d)
  end.

(* [comment removed for export] *)
Definition sd_eval (fs : fdig) (fk : list kentry) (b : expr) (d : sdesc) (k n : Z) : bool :=
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

Definition mk_ci (fs : fdig) (fk : list kentry) (tbl : list (saddr * expr * saddr * expr)) (b : expr) : cinfo :=
  let br := base_range fk b in
  CI br (map (fun t => let '(c1, m1, c2, m2) := t in (mk_sd fs fk b br c1 m1, mk_sd fs fk b br c2 m2)) tbl).

Definition mk_ci' (fs : fdig) (fk : list kentry) (tbl : list (sideinfo * sideinfo)) (b : expr) : cinfo :=
  let br := base_range fk b in
  CI br (map (fun t => (mk_sd' fs fk b br (fst t), mk_sd' fs fk b br (snd t))) tbl).

(* [comment removed for export] *)
Definition dmask_of (fs : fdig) (fk : list kentry) (b1 : expr) (k1 m1 : Z) (sds : list (sdesc * sdesc)) : list (bool * bool) :=
  map (fun p => (sd_eval fs fk b1 (fst p) k1 m1, sd_eval fs fk b1 (snd p) k1 m1)) sds.
Definition dxmask_of (fs : fdig) (fk : list kentry) (b1 : expr) (k1 : Z) (n1 : expr) (h1 : option Z) (sds : list (sdesc * sdesc)) : list (bool * bool) :=
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

Fixpoint exists_sd (fs : fdig) (fk : list kentry) (b : expr) (k n : Z) (ds : list sdesc) : bool :=
  match ds with
  | [] => false
  | d :: r => if sd_eval fs fk b d k n then true else exists_sd fs fk b k n r
  end.
Fixpoint exists_xk (fs : fdig) (fk : list kentry) (b : expr) (k : Z) (n : expr) (h : option Z) (ds : list sdesc) : bool :=
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
  cc_fs : fdig;                            (* [comment removed for export] *)
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

Definition mk_AB (br1 : option (Z * Z)) (k1 : Z) (h1 : option Z) : option (Z * Z) :=
  match br1, h1 with
  | Some (lo1, hi1), Some h => Some (hi1 + k1 + h, lo1 + k1)
  | _, _ => None
  end.
Definition mk_si (fs : fdig) (fk : list kentry) (b1 : expr) (k1 : Z) (n1 : expr) (ci1 : cinfo) : sinfo :=
  let m1 := lit_of_len n1 in
  let h1 := xhiF fs fk n1 in
  SI b1 k1 n1 m1 h1 (mk_AB (ci_br ci1) k1 h1) (ci_sds ci1)
     (match m1 with Some m => dmask_of fs fk b1 k1 m (ci_sds ci1) | None => [] end).

Definition mk_thr (si : sinfo) (br2 : option (Z * Z)) : option (Z * Z) :=
  match si_br1 si, br2 with
  | Some (A, B), Some (lo2, hi2) => Some (A - lo2, B - hi2)
  | _, _ => None
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

Definition dx_get (fs : fdig) (fk : list kentry) (si : sinfo) (st : scache) : list (bool * bool) * scache :=
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
Record grun : Type := GR { gr_b : expr; gr_lo : Z; gr_hi : Z; gr_n : Z }.
Definition gnear (l h lo hi : Z) : bool :=
  if Z.leb lo (h + 4096) then Z.leb (l - 4096) hi else false.
Fixpoint bounds_acc (kn : list kentry) (cur : option grun) (acc : list grun) : list grun :=
  match kn with
  | [] => match cur with Some c => c :: acc | None => acc end
  | K :: rest =>
      match klit K with
      | None => bounds_acc rest cur acc
      | Some (b2, lo, hi) =>
          match cur with
          | Some (GR b l h c) =>
              if (if expr_eqb b2 b then gnear l h lo hi else false)
              then bounds_acc rest (Some (GR b (Z.min l lo) (Z.max h hi) (c + 1))) acc
              else bounds_acc rest (Some (GR b2 lo hi 1)) (GR b l h c :: acc)
          | None => bounds_acc rest (Some (GR b2 lo hi 1)) acc
          end
      end
  end.
(* [comment removed for export] *)
Fixpoint gclust_ins (l h c : Z) (cl : list (Z * Z * Z)) : list (Z * Z * Z) :=
  match cl with
  | [] => [(l, h, c)]
  | (l', h', c') :: r => if gnear l' h' l h then (Z.min l l', Z.max h h', c + c') :: r
                         else (l', h', c') :: gclust_ins l h c r
  end.
Fixpoint gclusters (tbl : list grun) (b2 : expr) (cl : list (Z * Z * Z)) : list (Z * Z * Z) :=
  match tbl with
  | [] => cl
  | GR b l h c :: rest => gclusters rest b2 (if expr_eqb b2 b then gclust_ins l h c cl else cl)
  end.
Fixpoint gbest (cl : list (Z * Z * Z)) (best : option (Z * Z * Z)) : option (Z * Z) :=
  match cl with
  | [] => match best with Some (l, h, _) => Some (l, h) | None => None end
  | (l, h, c) :: r => match best with
                      | Some (_, _, c') => if Z.ltb c' c then gbest r (Some (l, h, c)) else gbest r best
                      | None => gbest r (Some (l, h, c))
                      end
  end.
Definition group_bounds (tbl : list grun) (b2 : expr) : option (Z * Z) :=
  gbest (gclusters tbl b2 []) None.

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
Record column : Type := COL { co_ents : list colent; co_all : bool; co_gb : option (Z * Z);
                               co_allf : bool; co_runs : list (Z * Z) }.

(* [comment removed for export] *)
Fixpoint run_ins (k kw : Z) (runs : list (Z * Z)) : list (Z * Z) :=
  match runs with
  | [] => [(k, kw)]
  | (a, b) :: r => if (if Z.ltb kw a then true else Z.ltb b k) then (a, b) :: run_ins k kw r
                   else run_ins (Z.min k a) (Z.max kw b) r
  end.
Fixpoint runs_of (ents : list colent) : list (Z * Z) :=
  match ents with
  | [] => []
  | c :: r => match ce_same c with Some (k, kw) => run_ins k kw (runs_of r) | None => runs_of r end
  end.
Fixpoint all_truef (ents : list colent) : bool :=
  match ents with
  | [] => true
  | c :: r => if (if ce_all c then true else match ce_same c with Some _ => true | None => false end) then all_truef r else false
  end.
Fixpoint runs_disj (runs : list (Z * Z)) (lo hi : Z) : bool :=
  match runs with
  | [] => true
  | (a, b) :: r => if (if Z.leb hi a then true else Z.leb b lo) then runs_disj r lo hi else false
  end.
Definition covered (runs : list (Z * Z)) (k kw : Z) : Prop := exists a b, In (a, b) runs /\ a <= k /\ kw <= b.
Lemma run_ins_cover : forall runs k kw,
  (forall k' kw', covered runs k' kw' -> covered (run_ins k kw runs) k' kw') /\ covered (run_ins k kw runs) k kw.
Proof.
  induction runs as [|[a b] r IH]; intros k kw.
  - split; [intros k' kw' (a & b & H & _); destruct H|]. exists k, kw. cbn. split; [left; reflexivity|lia].
  - cbn [run_ins]. destruct (if Z.ltb kw a then true else Z.ltb b k) eqn:D.
    + split.
      * intros k' kw' (a' & b' & Hin & H1 & H2). destruct Hin as [E|Hin].
        -- exists a', b'. split; [left; exact E|lia].
        -- destruct (proj1 (IH k kw) k' kw') as (a2 & b2 & Hin2 & H3 & H4); [exists a', b'; split; [exact Hin|lia]|].
           exists a2, b2. split; [right; exact Hin2|lia].
      * destruct (proj2 (IH k kw)) as (a2 & b2 & Hin2 & H3 & H4). exists a2, b2. split; [right; exact Hin2|lia].
    + split.
      * intros k' kw' (a' & b' & Hin & H1 & H2). destruct Hin as [E|Hin].
        -- assert (a' = a /\ b' = b) as [-> ->] by (injection E; intros; subst; split; reflexivity).
           destruct (proj2 (IH (Z.min k a) (Z.max kw b))) as (a2 & b2 & Hin2 & H3 & H4).
           exists a2, b2. split; [exact Hin2|lia].
        -- exact (proj1 (IH _ _) k' kw' (ex_intro _ a' (ex_intro _ b' (conj Hin (conj H1 H2))))).
      * destruct (proj2 (IH (Z.min k a) (Z.max kw b))) as (a2 & b2 & Hin2 & H3 & H4).
        exists a2, b2. split; [exact Hin2|lia].
Qed.
Lemma runs_disj_sound : forall runs lo hi a b, runs_disj runs lo hi = true -> In (a, b) runs -> hi <= a \/ b <= lo.
Proof.
  intros runs lo hi a b. induction runs as [|[a' b'] r IH]; cbn [runs_disj]; intros H Hin; [destruct Hin|].
  destruct Hin as [E|Hin].
  - injection E as -> ->. destruct (Z.leb_spec hi a); [lia|]. destruct (Z.leb_spec b lo); [lia|discriminate].
  - apply IH; [|exact Hin]. destruct (if Z.leb hi a' then true else Z.leb b' lo); [exact H|discriminate].
Qed.
Lemma runs_of_cover : forall ents c k kw, In c ents -> ce_same c = Some (k, kw) -> covered (runs_of ents) k kw.
Proof.
  induction ents as [|c0 r IH]; intros c k kw Hin Hc; [destruct Hin|].
  cbn [runs_of]. destruct Hin as [->|Hin].
  - rewrite Hc. apply (proj2 (run_ins_cover _ _ _)).
  - specialize (IH c k kw Hin Hc). destruct (ce_same c0) as [[k0 kw0]|]; [|exact IH].
    apply (proj1 (run_ins_cover _ _ _)). exact IH.
Qed.
Lemma all_truef_In : forall ents c, all_truef ents = true -> In c ents -> ce_all c = true \/ exists k kw, ce_same c = Some (k, kw).
Proof.
  induction ents as [|c0 r IH]; intros c H Hin; [destruct Hin|]. cbn [all_truef] in H.
  destruct (if ce_all c0 then true else match ce_same c0 with Some _ => true | None => false end) eqn:D; [|discriminate].
  destruct Hin as [->|Hin]; [|exact (IH c H Hin)].
  destruct (ce_all c); [left; reflexivity|]. destruct (ce_same c) as [[k kw]|]; [right; exists k, kw; reflexivity|discriminate].
Qed.

Fixpoint all_true (l : list colent) : bool :=
  match l with [] => true | c :: r => if ce_all c then all_true r else false end.

Definition column_of (sxs : list stctx) (b2 : expr) (ci2 : cinfo) (gb : option (Z * Z)) : column :=
  let ents := map (fun sx => let e := mk_sei (sx_si sx) b2 ci2 in
                          CE e (group_all sx b2 e gb)
                             (if expr_eqb b2 (a_base (sx_wa sx))
                              then Some (a_off (sx_wa sx), a_off (sx_wa sx) + Z.of_nat (sx_w sx)) else None)) sxs in
  COL ents (all_true ents) gb (all_truef ents) (runs_of ents).

(* [comment removed for export] *)
Definition zin64 (z : Z) : bool := if Z.leb 0 z then Z.ltb z two64 else false.

Definition dxm_of (fs : fdig) (fk : list kentry) (sx : stctx) : list (bool * bool) :=
  let si := sx_si sx in dxmask_of fs fk (si_b1 si) (si_k1 si) (si_n1 si) (si_h1 si) (si_sds1 si).

Definition quick_apartL (fs : fdig) (fk : list kentry) (sx : stctx) (e : sentryinfo)
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

Definition quick_apartX (fs : fdig) (fk : list kentry) (sx : stctx) (e : sentryinfo)
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

Definition quick_keepL (fs : fdig) (fk : list kentry) (sx : stctx) (e : sentryinfo) (K : kentry) : bool :=
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

Definition quick_keepX (fs : fdig) (fk : list kentry) (sx : stctx) (e : sentryinfo)
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
Fixpoint first_failL (fs : fdig) (fk : list kentry) (useall : bool) (es : option (Z * Z))
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
Fixpoint first_failX (fs : fdig) (fk : list kentry) (sxs : list stctx) (ents : list colent) (h2 : option Z) (K : kentry)
  : option (list stctx) :=
  match sxs, ents with
  | sx :: sr, c :: cr => if quick_keepX fs fk sx (ce_sei c) h2 K then first_failX fs fk sr cr h2 K else Some sxs
  | [], _ => None
  | _, [] => Some sxs
  end.

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
  vt_gb : list grun;                            (* [comment removed for export] *)
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
      if (if useall then match i with
                          | O => if co_all col then true
                                 else if co_allf col then match esum K with Some (elo, ehi) => runs_disj (co_runs col) elo ehi | None => false end
                                 else false
                          | S _ => false end else false) then ([K], vt)
      else match first_failL (cc_fs (vt_cc vt)) (vt_fk vt) useall (esum K) sxs ents K with
           | None => ([K], vt)
           | Some sfx => (pieces_through (vt_fk vt) (vt_cc vt) sfx [K], vt)
           end
  | Some n =>
      let '(h2, cc) := xh_get (vt_fk vt) (vt_cc vt) n in
      let vt := VT (vt_fk vt) cc (vt_sxs vt) (vt_gb vt) (vt_cols vt) in
      match first_failX (cc_fs cc) (vt_fk vt) sxs ents h2 K with
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
      | H : N.eqb _ _ = true |- _ => apply N.eqb_eq in H
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
  cbn [sd_same].
  destruct (shares_var b cb).
  { match goal with |- (if ?c then true else _) = _ => destruct c eqn:FAST end; [|rewrite xinside0F_eq; reflexivity].
    destruct (expr_eqb b cb) eqn:EB; [|discriminate]. apply expr_eqb_true in EB. subst cb.
    destruct n as [zn| | | | | | |]; try discriminate. destruct m as [zm| | | | | | |]; try discriminate.
    rewrite <- xinside0F_eq. symmetry. apply ss_fast_sound. exact FAST. }
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
  thr_test (mk_thr (SI b1 k1 n1 m1 h1 (mk_AB br1 k1 h1) sds1 dm) br2) k2 h2
  = match br1, br2, h1, h2 with
    | Some (lo1, hi1), Some (lo2, hi2), Some m, Some h => (Z.leb (hi1 + k1 + m) (lo2 + k2) || Z.leb (hi2 + k2 + h) (lo1 + k1))%bool
    | _, _, _, _ => false
    end.
Proof.
  intros. unfold thr_test, mk_thr, mk_AB. cbn [si_br1 si_k1 si_h1].
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
Definition vt_ok (fk : list kentry) (sxs : list stctx) (gbt : list grun) (vt : vtables) : Prop :=
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

Lemma runs_keep_sound : forall fk b2 gl gh sxs ents K lo hi elo ehi,
  Forall (sx_wf fk) sxs -> ents_ok fk b2 (Some (gl, gh)) sxs ents -> kkey K = Some b2 -> klen_sym K = None ->
  klit K = Some (b2, lo, hi) -> gl <= lo -> hi <= gh -> esum K = Some (elo, ehi) ->
  all_truef ents = true -> runs_disj (runs_of ents) elo ehi = true ->
  Forall (fun sx => P1 fk sx K = [K]) sxs.
Proof.
  intros fk b2 gl gh sxs ents K lo hi elo ehi Hwf Hents HK HL HKl H1 H2 HE HA HR.
  assert (HS : forall c k kw, In c ents -> ce_same c = Some (k, kw) -> (if Z.leb ehi k then true else Z.leb kw elo) = true).
  { intros c k kw Hin Hc. destruct (runs_of_cover ents c k kw Hin Hc) as (a & b & Hab & Ha & Hb).
    pose proof (runs_disj_sound _ _ _ _ _ HR Hab) as D.
    destruct (Z.leb_spec ehi k); [reflexivity|]. destruct (Z.leb_spec kw elo); [reflexivity|]. exfalso. lia. }
  assert (HA' : forall c, In c ents -> ce_all c = true \/ exists k kw, ce_same c = Some (k, kw)) by (intros c; apply all_truef_In; exact HA).
  clear HA HR. induction Hents as [|sx c sr cr Hc Hents IH]; [constructor|].
  apply Forall_cons_iff in Hwf as [Hsx Hwf]. constructor.
  - destruct (HA' c (or_introl eq_refl)) as [Hall|(k & kw & Hsame)].
    + apply (group_all_sound fk sx c b2 (Some (gl, gh)) K gl gh lo hi Hsx Hc); [|exact HKl|exact H1|exact H2].
      exact (proj1 (proj2 Hc) Hall).
    + apply (quick_keepL_sound fk sx c b2 (Some (gl, gh)) K Hsx Hc HK HL).
      exact (same_quick fk sx c b2 (Some (gl, gh)) K k kw elo ehi Hc HK Hsame HE (HS c k kw (or_introl eq_refl) Hsame)).
  - apply IH; [exact Hwf| |].
    + intros c0 k kw Hin. apply HS. right. exact Hin.
    + intros c0 Hin. apply HA'. right. exact Hin.
Qed.

Lemma column_of_extra : forall sxs b2 ci gb,
  co_allf (column_of sxs b2 ci gb) = all_truef (co_ents (column_of sxs b2 ci gb)) /\ co_runs (column_of sxs b2 ci gb) = runs_of (co_ents (column_of sxs b2 ci gb)).
Proof. intros. split; reflexivity. Qed.

Lemma entryV_eq : forall fk sxs gbt vt orig i b2 K,
  vt_ok fk sxs gbt vt -> Forall (sx_wf fk) sxs -> kkey K = Some b2 ->
  fst (entryV vt orig i b2 K) = PT fk (skipn i sxs) [K] /\ vt_ok fk sxs gbt (snd (entryV vt orig i b2 K)).
Proof.
  intros fk sxs gbt vt orig i b2 K Hvt Hwf HK. unfold entryV.
  pose proof (vt_col_ok fk sxs gbt vt b2 Hvt) as [Hcol Hvt1].
  destruct (vt_col vt b2) as [col vt1]. cbn [fst snd] in Hcol, Hvt1.
  pose proof (column_of_ok fk sxs b2 (group_bounds gbt b2)) as CO. cbv zeta in CO. rewrite <- Hcol in CO.
  pose proof (column_of_extra sxs b2 (mk_ci (SFS fk) fk (kdisj_sides fk) b2) (group_bounds gbt b2)) as [Hallf Hruns]. rewrite <- Hcol in Hallf, Hruns.
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
    pose proof (first_failX_sound fk b2 (group_bounds gbt b2) K n h2 (skipn i sxs) (skipn i (co_ents col))
                  (Forall_skipn' _ _ i _ Hwf) (Forall2_skipn _ _ _ i _ _ Hents) HK HL Xh) as FF.
    destruct (first_failX (SFS fk) fk (skipn i sxs) (skipn i (co_ents col)) h2 K) as [sfx|].
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
    match goal with |- context [if ?cnd then ([K], vt1) else _] => destruct cnd eqn:C end.
    + cbn [fst snd]. split; [|exact VT1].
      destruct useall; [|discriminate]. destruct i; [|discriminate]. cbn [skipn]. symmetry. apply PT_keep.
      destruct (HU eq_refl) as (gl & gh & lo & hi & Hgb2 & HKl & H1 & H2).
      destruct (co_all col) eqn:CA.
      2: { destruct (co_allf col) eqn:CF; [|discriminate]. destruct (esum K) as [[elo ehi]|] eqn:HE; [|discriminate].
           rewrite Hruns in C. rewrite Hgb2 in Hents.
           exact (runs_keep_sound fk b2 gl gh sxs (co_ents col) K lo hi elo ehi Hwf Hents HK HL HKl H1 H2 HE (eq_sym Hallf) C). }
      pose proof (Hall eq_refl) as HA. clear -Hents HA Hwf HKl H1 H2 Hgb2.
      induction Hents as [|sx c sr cr Hc Hents IH]; [constructor|].
      apply Forall_cons_iff in Hwf as [Hsx Hwf]. apply Forall_cons_iff in HA as [Ha HA].
      constructor; [|exact (IH Hwf HA)].
      apply (group_all_sound fk sx c b2 (group_bounds gbt b2) K gl gh lo hi Hsx Hc); [|exact HKl|exact H1|exact H2].
      rewrite <- Hgb2. exact (proj1 (proj2 Hc) Ha).
    + pose proof (first_failL_sound fk b2 (group_bounds gbt b2) K useall (skipn i sxs) (skipn i (co_ents col))
                    (Forall_skipn' _ _ i _ Hwf) (Forall2_skipn _ _ _ i _ _ Hents) HK HL HU) as FF.
      destruct (first_failL (SFS fk) fk useall (esum K) (skipn i sxs) (skipn i (co_ents col)) K) as [sfx|].
      * destruct FF as [pre [E1 E2]]. cbn [fst snd]. split; [exact (SFX pre sfx E1 E2) | exact VT1].
      * cbn [fst snd]. split; [symmetry; exact FF | exact VT1].
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

(* [comment removed for export] *)
Fixpoint dm_apart (dm pre : list (bool * bool)) : bool :=
  match dm, pre with
  | (d1, d2) :: dr, (fB, fD) :: pr =>
      if (if fB then d1 else false) then true
      else if (if fD then d2 else false) then true
      else dm_apart dr pr
  | _, _ => false
  end.

Lemma dm_apart_eq : forall fk kn b1 k1 m1 b2 k2 n2,
  dm_apart (dmask_of (SFS fk) fk b1 k1 m1 (sds_of fk kn b1)) (kdisj_pre2F (SFS fk) fk kn b2 k2 n2)
  = kdisj_apartF (SFS fk) fk kn b1 k1 m1 b2 k2 n2.
Proof.
  intros fk kn b1 k1 m1 b2 k2 n2. induction kn as [|K rest IH]; [reflexivity|].
  destruct K as [| | | | | | |c1 m1' c2 m2]; try exact IH.
  rewrite sds_of_cons_disj. cbn [dmask_of map fst snd kdisj_pre2F kdisj_apartF dm_apart].
  fold (dmask_of (SFS fk) fk b1 k1 m1 (sds_of fk rest b1)). rewrite IH.
  rewrite !sd_eval_eq by reflexivity. rewrite <- !sub_itvF_eq.
  destruct (sub_itvF (SFS fk) fk b2 k2 n2 c2 m2), (sub_itvF (SFS fk) fk b2 k2 n2 c1 m1'),
           (sub_itvF (SFS fk) fk b1 k1 m1 c1 m1'), (sub_itvF (SFS fk) fk b1 k1 m1 c2 m2); reflexivity.
Qed.

(* [comment removed for export] *)
Lemma sx_si_dmask : forall fk sx,
  sx_wf fk sx ->
  si_dmask (sx_si sx) = dmask_of (SFS fk) fk (a_base (sx_wa sx)) (a_off (sx_wa sx)) (zlit64 (Z.of_nat (sx_w sx))) (sds_of fk fk (a_base (sx_wa sx))).
Proof. intros fk sx H. rewrite H. reflexivity. Qed.

(* [comment removed for export] *)
Definition carryVS (log : list sentry) (kn : list kentry) : list kentry * fdig * list stctx :=
  let fk := facts_of kn in
  let fs := SFS fk in
  let cc0 := CC (kdisj_sdis fs fk fk) fs [] [] in
  let '(sxs, cc) := stctxs_of fk cc0 log in
  let vt := VT fk cc sxs (bounds_acc kn None []) [] in
  let '(sp, vt) := stores_partV vt 1%nat sxs in
  (sp ++ chainsV vt kn, fs, sxs).
Lemma carryVS_eq : forall log kn,
  let fk := facts_of kn in
  fst (fst (carryVS log kn)) = carryV log kn /\ snd (fst (carryVS log kn)) = SFS fk
  /\ snd (carryVS log kn) = map (sx_of fk) (rev log).
Proof.
  intros log kn fk. unfold carryVS, carryV. fold fk.
  assert (H0 : pcc_ok fk (CC (kdisj_sdis (SFS fk) fk fk) (SFS fk) [] [])).
  { split; [split; reflexivity|]. split; intros ? ? H; discriminate. }
  pose proof (stctxs_of_eq fk log _ H0) as [E1 _].
  destruct (stctxs_of fk (CC (kdisj_sdis (SFS fk) fk fk) (SFS fk) [] []) log) as [sxs cc]. cbn [fst snd] in E1.
  destruct (stores_partV (VT fk cc sxs (bounds_acc kn None []) []) 1 sxs) as [sp vt]. cbn [fst snd].
  split; [reflexivity|]. split; [reflexivity | exact E1].
Qed.
Lemma carryVS_wf : forall log kn, Forall (sx_wf (facts_of kn)) (snd (carryVS log kn)).
Proof.
  intros log kn. destruct (carryVS_eq log kn) as (_ & _ & E). rewrite E.
  apply Forall_forall. intros sx Hin. apply in_map_iff in Hin as [e [<- _]]. apply sx_of_wf.
Qed.

End SX2.
