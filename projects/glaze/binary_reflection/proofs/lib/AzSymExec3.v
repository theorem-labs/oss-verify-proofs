(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
#[local] Ltac Zify.zify ::= WdZS.wd_zs_stock.   (* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SymExec. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SymExec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.

Module AX2.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

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
Definition two64 : Z := 2 ^ 64.         (* [comment removed for export] *)
Definition two64m1 : Z := two64 - 1.   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition two63z : Z := 2 ^ 63.
Definition mtwo63z : Z := - 2 ^ 63.
Definition two32z : Z := 2 ^ 32.

Definition ones64z : Z := Z.ones 64.          (* [comment removed for export] *)
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
(* [comment removed for export] *)
Definition pdiv (a j : Z) : Z := if Z.leb 0 j then Z.shiftr a j else (a / 2 ^ j)%Z.
Definition pmod (a j : Z) : Z := if Z.leb 0 j then Z.land a (Z.ones j) else (a mod 2 ^ j)%Z.
Definition pmul (a j : Z) : Z := if Z.leb 0 j then Z.shiftl a j else (a * 2 ^ j)%Z.
Definition phalf (w : Z) : Z := Z.div2 w.
Fixpoint pos_ones (p : positive) : bool := match p with xH => true | xI q => pos_ones q | xO _ => false end.
(* [comment removed for export] *)
Fixpoint pshl_sz (q p : positive) : positive := match p with xH => xO q | xI p' | xO p' => xO (pshl_sz q p') end.
Definition zshl_sz (k : Z) (p : positive) : Z :=
  match k with Z0 => Z0 | Zpos q => Zpos (pshl_sz q p) | Zneg q => Zneg (pshl_sz q p) end.
Definition zmulf (k y : Z) : Z :=
  match k with
  | Z0 => Z0
  | Zpos xH => y
  | Zneg xH => Z.opp y
  | _ => match y with
         | Zpos p => if pos_ones p then (zshl_sz k p - k)%Z else (k * y)%Z
         | _ => (k * y)%Z
         end
  end.
Lemma pdiv_eq : forall a j, pdiv a j = (a / 2 ^ j)%Z.
Proof. intros a j. unfold pdiv. destruct (Z.leb_spec 0 j); [apply Z.shiftr_div_pow2; assumption | reflexivity]. Qed.
Lemma pmod_eq : forall a j, pmod a j = (a mod 2 ^ j)%Z.
Proof. intros a j. unfold pmod. destruct (Z.leb_spec 0 j); [apply Z.land_ones; assumption | reflexivity]. Qed.
Lemma pmul_eq : forall a j, pmul a j = (a * 2 ^ j)%Z.
Proof. intros a j. unfold pmul. destruct (Z.leb_spec 0 j); [apply Z.shiftl_mul_pow2; assumption | reflexivity]. Qed.
Lemma phalf_eq : forall w, phalf w = (w / 2)%Z.
Proof. intros w. unfold phalf. apply Z.div2_div. Qed.
Lemma pos_ones_spec : forall p, pos_ones p = true -> Zpos p = (2 ^ Zpos (Pos.size p) - 1)%Z.
Proof.
  induction p as [q IH|q IH|]; cbn [pos_ones Pos.size]; intros H; [|discriminate|reflexivity].
  rewrite Pos2Z.inj_succ, Z.pow_succ_r by apply Pos2Z.is_nonneg. rewrite Pos2Z.inj_xI, (IH H). ring.
Qed.
Lemma zmulf_eq : forall k y, zmulf k y = (k * y)%Z.
Proof.
  assert (SH : forall q p, Zpos (pshl_sz q p) = (Zpos q * 2 ^ Zpos (Pos.size p))%Z).
  { intros q p. induction p as [p' IH|p' IH|]; cbn [pshl_sz Pos.size].
    - rewrite Pos2Z.inj_succ, Z.pow_succ_r by apply Pos2Z.is_nonneg. rewrite Pos2Z.inj_xO, IH. ring.
    - rewrite Pos2Z.inj_succ, Z.pow_succ_r by apply Pos2Z.is_nonneg. rewrite Pos2Z.inj_xO, IH. ring.
    - rewrite Pos2Z.inj_xO. change (2 ^ 1)%Z with 2%Z. ring. }
  assert (ZS : forall k p, zshl_sz k p = (k * 2 ^ Zpos (Pos.size p))%Z).
  { intros k p. destruct k as [|q|q]; cbn [zshl_sz]; [reflexivity | apply SH |].
    change (Zneg (pshl_sz q p)) with (- Zpos (pshl_sz q p))%Z. rewrite SH. change (Zneg q) with (- Zpos q)%Z. ring. }
  intros k y. unfold zmulf.
  assert (G : match y with
              | Zpos p => if pos_ones p then (zshl_sz k p - k)%Z else (k * y)%Z
              | _ => (k * y)%Z
              end = (k * y)%Z).
  { destruct y as [|p|p]; try reflexivity. destruct (pos_ones p) eqn:Ho; [|reflexivity].
    rewrite ZS. rewrite (pos_ones_spec p Ho). ring. }
  destruct k as [|q|q]; [reflexivity | | ].
  - destruct q; try exact G. destruct y; reflexivity.
  - destruct q; try exact G. destruct y; reflexivity.
Qed.

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

(* [comment removed for export] *)
Definition wrap64 (z : Z) : Z :=
  if (Z.leb 0 z && Z.ltb z two64)%bool then z else (z mod two64)%Z.

Definition sx32 (r : Z) : Z :=
  if Z.ltb r 2147483648 then r else (r + 18446744069414584320)%Z.

(* [comment removed for export] *)
Definition ones32z : Z := Z.ones 32.
Definition land64 (z : Z) : Z :=
  if (Z.leb 0 z && Z.ltb z two64)%bool then z else Z.land z ones64z.
Definition land32 (z : Z) : Z :=
  if (Z.leb 0 z && Z.ltb z two32z)%bool then z else Z.land z ones32z.

Definition zfast (op : aluop) (x y : Z) : Z :=
  match op with
  | ALU_ADD => let t := (x + y)%Z in if Z.ltb t two64 then t else (t - two64)%Z
  | ALU_SUB => let t := (x - y)%Z in if Z.leb 0 t then t else (t + two64)%Z
  | ALU_AND => Z.land x y
  | ALU_OR => Z.lor x y
  | ALU_XOR => Z.lxor x y
  | ALU_SRL => Z.shiftr x (Z.land y 63)
  | ALU_SLL => land64 (Z.shiftl x (Z.land y 63))
  | ALU_SLTU => if Z.ltb x y then 1%Z else 0%Z
  | _ => zalu op x y
  end.

Definition zfastw (op : aluop) (x y : Z) : Z :=
  match op with
  | ALU_ADD => sx32 (land32 (x + y))
  | ALU_SUB => sx32 (land32 (x - y))
  | ALU_SRL => sx32 (Z.shiftr (land32 x) (Z.land y 31))
  | ALU_SLL => sx32 (land32 (Z.shiftl (land32 x) (Z.land y 31)))
  | _ => zaluw op x y
  end.

Definition zfastm (op : mulop) (x y : Z) : Z :=
  match op with
  | M_MUL => land64 (x * y)
  | _ => zmd op x y
  end.

(* [comment removed for export] *)
Definition zext_fast (sx : bool) (lo n : nat) (x : Z) : Z :=
  let k := (8 * Z.of_nat n)%Z in
  let u := Z.land (Z.shiftr x (8 * Z.of_nat lo)) (Z.ones k) in
  if sx then match n with
             | O => wrap64 u
             | _ => if Z.ltb u (Z.shiftl 1 (k - 1)) then wrap64 u else wrap64 (u - Z.shiftl 1 k + two64)
             end
  else wrap64 u.

(* [comment removed for export] *)
Definition zalu_l (op : aluop) (x y : Z) : Z := zfast op (wrap64 x) (wrap64 y).
Definition zaluw_l (op : aluop) (x y : Z) : Z := zfastw op (wrap64 x) (wrap64 y).
Definition zmd_l (op : mulop) (x y : Z) : Z := zfastm op (wrap64 x) (wrap64 y).

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
  | Some x, Some y => ELit (zalu_l op x y)
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
  | Some x, Some y => ELit (zaluw_l op x y)
  | _, _ =>
      match op with
      | ALU_SLL | ALU_SRL | ALU_SRA =>
          match is_lit b with
          | Some _ => EAluw op a b
          | None => match shamt_of b 5 with
                    | Some s => match is_lit a with
                                | Some x => ELit (zaluw_l op x s)
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
  | Some x, Some y => ELit (zmd_l op x y)
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
  | ELit x => ELit (zext_fast sx lo n (wrap64 x))   (* [comment removed for export] *)
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
| KDisj (a1 : saddr) (n1 : expr) (a2 : saddr) (n2 : expr)
                                              (* [comment removed for export] *)
| KFill (a : saddr) (n : expr) (c : Z)        (* [comment removed for export] *)
| KUnk (a : saddr) (n : expr)                  (* [comment removed for export] *)
| KShOk (a : saddr) (n : expr)                 (* [comment removed for export] *)
| KFpc (v lo : expr) (d : nat).                (* [comment removed for export] *)

(* [comment removed for export] *)
Definition SB : Z := 0x7fff8000.

(* [comment removed for export] *)
Inductive sidecond : Type :=
| SCBr       (taken : bool) (c : branch_cond) (a b : expr)
| SCFlat     (a : saddr) (n : expr)                     (* [comment removed for export] *)
| SCDisj     (a1 : saddr) (n1 : expr) (a2 : saddr) (n2 : expr)  (* [comment removed for export] *)
| SCInside   (a1 : saddr) (n1 : expr) (a2 : saddr) (n2 : expr)  (* [comment removed for export] *)
| SCStoreOk  (a : saddr) (n : nat)                      (* [comment removed for export] *)
| SCReadBase (a : saddr) (n : nat) (sx : bool) (e : expr)  (* [comment removed for export] *)
| SCEq       (a b : expr).                              (* [comment removed for export] *)

Record sym_state : Type := SSR {
  s_pc   : Z;
  s_regs : list expr;
  s_log  : list sentry;       (* [comment removed for export] *)
  s_know : list kentry;
  s_next : nat;               (* [comment removed for export] *)
  s_resv : option saddr       (* [comment removed for export] *)
}.

(* [comment removed for export] *)
Abbreviation SS p r l k n := (SSR p r l k n None).

Definition sset (ss : sym_state) (rd : reg) (e : expr) (npc : Z) : sym_state :=
  SSR npc (if bv_eqb rd 0 then s_regs ss else sr_upd (s_regs ss) (ridx rd) e)
     (s_log ss) (s_know ss) (s_next ss) (s_resv ss).

Definition sjump (ss : sym_state) (npc : Z) : sym_state :=
  SSR npc (s_regs ss) (s_log ss) (s_know ss) (s_next ss) (s_resv ss).

(* [comment removed for export] *)
Definition clr (ss : sym_state) : sym_state :=
  SSR (s_pc ss) (s_regs ss) (s_log ss) (s_know ss) (s_next ss) None.
Definition s_clean (ss : sym_state) : bool :=
  match s_resv ss with None => true | Some _ => false end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Inductive rangerel := RInside (delta : Z) | RDisjoint | RPartial | RUnknown.

(* [comment removed for export] *)
Definition rel_lit_ref (rb : expr) (rk : Z) (rn : Z) (kb : expr) (kk : Z) (kn : Z) : rangerel :=
  if expr_eqb rb kb then
    if (Z.leb kk rk && Z.leb (rk + rn) (kk + kn))%bool then RInside (rk - kk)
    else if (Z.leb (rk + rn) kk || Z.leb (kk + kn) rk)%bool then RDisjoint
    else RPartial
  else RUnknown.
(* [comment removed for export] *)
Definition rel_lit_diff (rk : Z) (rn : Z) (kk : Z) (kn : Z) : rangerel :=
  let d := (rk - kk)%Z in
  if (if Z.leb 0 d then Z.leb (d + rn) kn else false) then RInside d
  else if (if Z.leb (d + rn) 0 then true else Z.leb kn d) then RDisjoint
  else RPartial.
(* [comment removed for export] *)
Definition rel_lit (rb : expr) (rk : Z) (rn : Z) (kb : expr) (kk : Z) (kn : Z) : rangerel :=
  if expr_eqb rb kb then
    match Z.compare rk kk with
    | Lt => if Z.leb (rk + rn) kk then RDisjoint else rel_lit_diff rk rn kk kn
    | _ => if Z.leb (kk + kn) rk then (if Z.ltb 0 rn then RDisjoint else rel_lit_diff rk rn kk kn) else rel_lit_diff rk rn kk kn
    end
  else RUnknown.
Lemma rel_lit_diff_eq : forall rk rn kk kn, rel_lit_diff rk rn kk kn =
  if (Z.leb kk rk && Z.leb (rk + rn) (kk + kn))%bool then RInside (rk - kk)
  else if (Z.leb (rk + rn) kk || Z.leb (kk + kn) rk)%bool then RDisjoint else RPartial.
Proof.
  intros. unfold rel_lit_diff. cbv zeta.
  destruct (Z.leb_spec 0 (rk - kk)); destruct (Z.leb_spec kk rk); try lia; cbn [andb];
    destruct (Z.leb_spec (rk - kk + rn) kn); destruct (Z.leb_spec (rk + rn) (kk + kn)); try lia; try reflexivity;
    destruct (Z.leb_spec (rk - kk + rn) 0); destruct (Z.leb_spec (rk + rn) kk); try lia; cbn [orb]; try reflexivity;
    destruct (Z.leb_spec kn (rk - kk)); destruct (Z.leb_spec (kk + kn) rk); try lia; reflexivity.
Qed.
Lemma rel_lit_eq : forall rb rk rn kb kk kn, rel_lit rb rk rn kb kk kn = rel_lit_ref rb rk rn kb kk kn.
Proof.
  intros. unfold rel_lit, rel_lit_ref. destruct (expr_eqb rb kb); [|reflexivity]. rewrite !rel_lit_diff_eq.
  destruct (Z.compare_spec rk kk) as [E|L|G].
  - destruct (Z.leb_spec (kk + kn) rk); [|reflexivity]. destruct (Z.ltb_spec 0 rn); [|reflexivity].
    destruct (Z.leb_spec kk rk); try lia; cbn [andb]. destruct (Z.leb_spec (rk + rn) (kk + kn)); try lia.
    destruct (Z.leb_spec (rk + rn) kk); cbn [orb]; [reflexivity|]. destruct (Z.leb_spec (kk + kn) rk); try lia. reflexivity.
  - destruct (Z.leb_spec (rk + rn) kk); [|reflexivity].
    destruct (Z.leb_spec kk rk); try lia; cbn [andb]. reflexivity.
  - destruct (Z.leb_spec (kk + kn) rk); [|reflexivity]. destruct (Z.ltb_spec 0 rn); [|reflexivity].
    destruct (Z.leb_spec kk rk); try lia; cbn [andb]. destruct (Z.leb_spec (rk + rn) (kk + kn)); try lia.
    destruct (Z.leb_spec (rk + rn) kk); cbn [orb]; [reflexivity|]. destruct (Z.leb_spec (kk + kn) rk); try lia. reflexivity.
Qed.

Definition elen (n : nat) : expr := ELit (Z.of_nat n).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition lit_strip (e : expr) : expr * Z :=
  match e with
  | EAlu ALU_ADD v (ELit c) => (v, c)
  | _ => (e, 0%Z)
  end.
Fixpoint find_range (kn : list kentry) (e : expr) : option (Z * Z) :=
  match kn with
  | [] => None
  | KRange e' lo hi :: rest =>
      if expr_eqb e e' then Some (lo, hi) else
      match e with
      | ELit _ => find_range rest e
      | _ =>
        let '(v, c) := lit_strip e in
        let '(v', c') := lit_strip e' in
        if expr_eqb v v' then
          let d := (c - c')%Z in
          if (Z.leb 0 lo && Z.leb lo hi && Z.ltb hi two64 && Z.leb 0 (lo + d) && Z.ltb (hi + d) two64)%bool   (* [comment removed for export] *)
          then (* [comment removed for export] *)
               match find_range rest e with
               | Some (lo2, hi2) => Some (Z.max (lo + d) lo2, Z.min (hi + d) hi2)%Z
               | None => Some ((lo + d)%Z, (hi + d)%Z)
               end
          else find_range rest e
        else find_range rest e
      end
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
Lemma zmod64_eq2 : forall z, zmod64 z = (z mod two64)%Z. Proof. exact zmod64_eq. Qed.
Lemma zdiv64_eq2 : forall z, zdiv64 z = (z / two64)%Z. Proof. exact zdiv64_eq. Qed.

(* [comment removed for export] *)
Definition pmod64 (z : Z) : Z := zmod64 z.
Definition pdiv64 (z : Z) : Z := zdiv64 z.
Lemma pmod64_eq : forall z, pmod64 z = (z mod two64)%Z. Proof. exact zmod64_eq. Qed.
Lemma pdiv64_eq : forall z, pdiv64 z = (z / two64)%Z. Proof. exact zdiv64_eq. Qed.

(* [comment removed for export] *)
Definition mul_rng (al ah bl bh : Z) : option (Z * Z) :=
  let hh := zmulf ah bh in
  if Z.leb 0 al then (if Z.leb 0 bl then (if Z.ltb hh two64 then Some (zmulf al bl, hh) else None) else None) else None.
Lemma mul_rng_eq : forall al ah bl bh, mul_rng al ah bl bh =
  if (Z.leb 0 al && Z.leb 0 bl && Z.ltb (ah * bh) two64)%bool then Some ((al * bl)%Z, (ah * bh)%Z) else None.
Proof. intros. unfold mul_rng. rewrite !zmulf_eq. destruct (Z.leb 0 al), (Z.leb 0 bl), (Z.ltb (ah * bh) two64); reflexivity. Qed.
Definition ext_w (n : nat) : Z :=
  match n with
  | 1%nat => 256 | 2%nat => 65536 | 3%nat => 16777216 | 4%nat => 4294967296
  | 8%nat => 18446744073709551616
  | _ => 2 ^ (8 * Z.of_nat n)
  end%Z.
Definition ext_top (n : nat) : Z :=
  match n with
  | 1%nat => 255 | 2%nat => 65535 | 3%nat => 16777215 | 4%nat => 4294967295
  | 8%nat => 18446744073709551615
  | _ => Z.min (2 ^ (8 * Z.of_nat n) - 1) (two64 - 1)
  end%Z.
Definition ext_half (n : nat) : Z :=
  match n with
  | 1%nat => 128 | 2%nat => 32768 | 3%nat => 8388608 | 4%nat => 2147483648
  | 8%nat => 9223372036854775808
  | _ => 2 ^ (8 * Z.of_nat n) / 2
  end%Z.
Lemma ext_w_eq : forall n, ext_w n = (2 ^ (8 * Z.of_nat n))%Z.
Proof. intros n. do 9 (destruct n as [|n]; [reflexivity|]). reflexivity. Qed.
Lemma ext_top_eq : forall n, ext_top n = Z.min (2 ^ (8 * Z.of_nat n) - 1) (two64 - 1).
Proof. intros n. do 9 (destruct n as [|n]; [reflexivity|]). reflexivity. Qed.
Lemma ext_half_eq : forall n, ext_half n = (2 ^ (8 * Z.of_nat n) / 2)%Z.
Proof. intros n. do 9 (destruct n as [|n]; [reflexivity|]). reflexivity. Qed.

Definition clampi (r : Z * Z) : Z * Z :=
  let (lo, hi) := r in (Z.max lo 0, Z.min hi two64m1).

(* [comment removed for export] *)
Definition mask_cover (h : Z) : Z :=
  if Z.ltb h 0 then 0 else (2 ^ (Z.log2_up (h + 1)) - 1)%Z.

Definition lit_shamt (e : expr) : option Z :=
  match e with ELit s => Some (s mod 64)%Z | _ => None end.

(* [comment removed for export] *)
Definition zsigned64 (v : Z) : Z := if Z.leb two63z v then (v - two64)%Z else v.

(* [comment removed for export] *)
Fixpoint lin_range (rng : expr -> option (Z * Z)) (c : Z) (ts : list (Z * expr)) : option (Z * Z) :=
  match ts with
  | [] => Some (c, c)
  | (k, a) :: rest =>
      match rng a, lin_range rng c rest with
      | Some (al, ah), Some (lo, hi) =>
          if Z.leb 0 k then Some ((lo + zmulf k al)%Z, (hi + zmulf k ah)%Z)
          else Some ((lo + zmulf k ah)%Z, (hi + zmulf k al)%Z)
      | _, _ => None
      end
  end.

Definition lin_trivial (l : lin) : bool :=
  match l with
  | (c, [(k, _)]) => (Z.eqb c 0 && Z.eqb k 1)%bool
  | _ => false
  end.

(* [comment removed for export] *)
Definition rng_or_full (o : option (Z * Z)) : Z * Z := match o with Some r => r | None => (0%Z, (two64 - 1)%Z) end.

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
                  let q := zdiv64 lo in   (* [comment removed for export] *)
                  if Z.eqb q (zdiv64 hi) then Some ((lo - q * two64)%Z, (hi - q * two64)%Z) else None
              | None => None
              end) with
  | Some r => Some r
  | None =>
  match e with
  | ELit z => let v := zmod64 z in Some (v, v)   (* [comment removed for export] *)
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
                     let m' := (pmod64 m) in
                     let j := Z.log2 (m' + 1) in
                     if (Z.eqb (m' + 1) (2 ^ j) && Z.leb (pdiv al j) (pdiv ah j) && Z.eqb (pdiv al j) (pdiv ah j))%bool
                     then Some ((pmod al j)%Z, (pmod ah j)%Z)
                     else let jh := Z.log2 (two64 - m') in
                          if (Z.eqb (two64 - m') (2 ^ jh) && Z.ltb jh 64)%bool
                          then Some ((al - pmod al jh)%Z, (ah - pmod ah jh)%Z)
                          else None
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
          | Some (al, ah), Some s => Some ((pdiv al s)%Z, (pdiv ah s)%Z)
          | None, Some s => Some (0%Z, (2 ^ (64 - s) - 1)%Z)   (* [comment removed for export] *)
          | _, _ => None
          end
      | ALU_SRA =>
          match erange kn a, lit_shamt b with
          | Some (al, ah), Some s =>
              if Z.ltb ah (2 ^ 63) then Some ((pdiv al s)%Z, (pdiv ah s)%Z)
              else (* [comment removed for export] *)
                if Z.leb (2 ^ 63) al then Some ((two64 + pdiv (al - two64) s)%Z, (two64 + pdiv (ah - two64) s)%Z)
                else None
          | _, _ => None
          end
      | ALU_SLL =>
          match erange kn a, lit_shamt b with
          | Some (al, ah), Some s =>
              if Z.ltb (pmul ah s) two64 then Some ((pmul al s)%Z, (pmul ah s)%Z) else None
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
              if Z.ltb (pmul ah s') (2 ^ 31) then Some ((pmul al s')%Z, (pmul ah s')%Z) else None
          | _, _ => None
          end
      | ALU_SRL =>
          match erange kn a, lit_shamt b with
          | Some (al0, ah0), Some s =>
              let s' := (s mod 32)%Z in
              (* [comment removed for export] *)
              match (if Z.ltb ah0 (2 ^ 32) then Some (al0, ah0)
                     else if Z.eqb (pdiv al0 32) (pdiv ah0 32) then Some ((pmod al0 32)%Z, (pmod ah0 32)%Z)
                     else None) with
              | Some (al, ah) =>
                  if (Z.ltb ah (2 ^ 32) && (Z.ltb 0 s' || Z.ltb ah (2 ^ 31)))%bool
                  then Some ((pdiv al s')%Z, (pdiv ah s')%Z)
                  else if Z.ltb 0 s' then Some (0%Z, (2 ^ (32 - s') - 1)%Z) else None
              | None => if Z.ltb 0 s' then Some (0%Z, (2 ^ (32 - s') - 1)%Z) else None
              end
          | None, Some s =>   (* [comment removed for export] *)
              let s' := (s mod 32)%Z in if Z.ltb 0 s' then Some (0%Z, (2 ^ (32 - s') - 1)%Z) else None
          | _, _ => None
          end
      | ALU_SRA =>
          match erange kn a, lit_shamt b with
          | Some (al, ah), Some s =>
              let s' := (s mod 32)%Z in
              if Z.ltb ah (2 ^ 31) then Some ((pdiv al s')%Z, (pdiv ah s')%Z)
              else (* [comment removed for export] *)
                if (Z.eqb (pdiv al 32) (pdiv ah 32) && Z.leb (2 ^ 31) (pmod al 32))%bool
                then Some ((two64 + pdiv (pmod al 32 - 2 ^ 32) s')%Z, (two64 + pdiv (pmod ah 32 - 2 ^ 32) s')%Z)
                else None
          | _, _ => None
          end
      | _ => None
      end
  | EMd op a b =>
      match op with
      | M_MUL =>
          match erange kn a, erange kn b with
          | Some (al, ah), Some (bl, bh) =>
              mul_rng al ah bl bh
          | _, _ => None
          end
      | M_MULH =>   (* [comment removed for export] *)
          match erange kn a, erange kn b with
          | Some (al, ah), Some (bl, bh) =>
              if (Z.leb 0 al && Z.leb 0 bl && Z.ltb ah (2 ^ 63) && Z.ltb bh (2 ^ 63))%bool
              then Some ((pdiv64 (zmulf al bl))%Z, (pdiv64 (zmulf ah bh))%Z) else None
          | _, _ => None
          end
      | M_MULHU =>   (* [comment removed for export] *)
          match rng_or_full (erange kn a), rng_or_full (erange kn b) with
          | (al, ah), (bl, bh) =>
              if (Z.leb 0 al && Z.leb 0 bl)%bool
              then Some ((pdiv64 (zmulf al bl))%Z, (pdiv64 (zmulf ah bh))%Z) else None
          end
      | M_DIVU =>
          match erange kn a, b with
          | Some (al, ah), ELit d =>
              let d' := (pmod64 d) in
              if Z.ltb 0 d' then Some ((al / d')%Z, (ah / d')%Z) else None
          | _, _ => None
          end
      | M_REMU =>
          match erange kn a, b with
          | Some (al, ah), ELit d =>
              let d' := (pmod64 d) in
              if Z.ltb 0 d' then Some (0%Z, Z.min ah (d' - 1)) else None
          | _, _ => None
          end
      | _ => None
      end
  | EMdw _ _ _ => None
  | EExt sx lo n a =>
      let w := ext_w n in
      if sx then
        match lo with
        | O =>
            let dec (r : option (Z * Z)) : option (Z * Z) :=
              match r with
              | Some (al, ah) =>
                  if (Z.leb 0 al && Z.ltb ah (ext_half n))%bool then Some (al, ah)
                  else if (Nat.leb 1 n && Nat.leb n 8 && Z.leb (ext_half n) al && Z.ltb ah w)%bool
                       then Some ((two64 - w + al)%Z, (two64 - w + ah)%Z) else None
              | None => None
              end in
            match dec (erange kn a) with
            | Some r => Some r
            | None =>
                (* [comment removed for export] *)
                if Nat.leb n 7 then dec (erange kn (EExt false 0 n a)) else None
            end
        | _ => None
        end
      else
        match lo, erange kn a with
        | O, Some (al, ah) =>
            if (Z.leb 0 al && Z.ltb ah w)%bool then Some (al, ah) else Some (0%Z, ext_top n)
        | _, _ => Some (0%Z, ext_top n)
        end
  | EBlob sx k i n =>
      (* [comment removed for export] *)
      if sx then Some (0%Z, two64m1) else Some (0%Z, ext_top n)%Z
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
Definition erange0 (kn : list kentry) (e : expr) : option (Z * Z) := erange_f erange_fuel (facts_of kn) e.

(* [comment removed for export] *)
Fixpoint deand (e : expr) : expr * Z :=
  match e with
  | EAlu ALU_AND x (ELit m) =>
      let m' := (m mod two64)%Z in
      let j := Z.log2 (two64 - m') in
      if (Z.eqb (two64 - m') (2 ^ j) && Z.leb j 48)%bool
      then let '(x', s) := deand x in (x', (s + (2 ^ j - 1))%Z)
      else (e, 0%Z)
  | EAlu ALU_ADD a b => let '(a', s1) := deand a in let '(b', s2) := deand b in (EAlu ALU_ADD a' b', (s1 + s2)%Z)
  | _ => (e, 0%Z)
  end.

Definition erange (kn : list kentry) (e : expr) : option (Z * Z) :=
  let r := erange0 kn e in
  let '(e', s) := deand e in
  if Z.eqb s 0 then r else
  match erange0 kn (unlin (lin_of e')) with     (* [comment removed for export] *)
  | Some (lo', hi') =>
      if Z.leb s lo' then
        match r with
        | Some (lo, hi) => Some (Z.max lo (lo' - s), Z.min hi hi')
        | None => Some ((lo' - s)%Z, hi')
        end
      else r
  | None => r
  end.


(* [comment removed for export] *)
Definition base_range (kn : list kentry) (e : expr) : option (Z * Z) :=
  match e with ELit z => let v := (z mod two64)%Z in Some (v, v) | _ => erange kn e end.

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
Fixpoint ealign0 (kn : list kentry) (e : expr) {struct e} : Z :=
  match find_align kn e with
  | Some m => if Z.ltb 0 m then ctz64 m else 0%Z
  | None =>
  match e with
  | ELit z => ctz64 (z mod two64)
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
(* [comment removed for export] *)
Fixpoint find_and_atom_k (sg : Z) (ts : list (Z * expr)) : option (expr * Z) :=
  match ts with
  | [] => None
  | (k, EAlu ALU_AND y (ELit mm)) :: r =>
      if (Z.eqb k sg && Z.ltb 0 mm && Z.eqb (Z.land (mm + 1) mm) 0)%bool then Some (y, mm) else find_and_atom_k sg r
  | _ :: r => find_and_atom_k sg r
  end.


Definition pageup_low_k (sg : Z) (e : expr) (m : Z) : option Z :=
  let l := lin_of e in
  match find_and_atom_k sg (snd l) with
  | Some (y, mm) =>
      if (Z.ltb 0 m && Z.eqb ((mm + 1) mod m) 0 && Z.leb (mm + 1) two64)%bool then
        let ly := lin_of y in
        let rest := lins_e (- sg)%Z (EAlu ALU_AND y (ELit mm)) (snd l) in
        match fold_right (fun t acc => lins_e (sg * fst t)%Z (snd t) acc) (snd ly) rest with
        | [] => Some ((fst l + sg * fst ly) mod m)%Z
        | _ => None
        end
      else None
  | None => None
  end.

(* [comment removed for export] *)
Definition pageup_low (e : expr) (m : Z) : option Z :=
  match pageup_low_k 1 e m with
  | Some r => Some r
  | None => pageup_low_k (-1) e m
  end.

Definition pageup_align (e : expr) : Z :=
  let l := lin_of e in
  match (match find_and_atom_k 1 (snd l) with
         | Some p => Some p
         | None => find_and_atom_k (-1) (snd l)
         end) with
  | Some (y, mm) =>
      let m := (mm + 1)%Z in let k := ctz64 m in
      if (Z.eqb m (2 ^ k) && Z.leb k 64)%bool then
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

(* [comment removed for export] *)
Definition highmask_s (mk : Z) : option Z :=
  let m' := (mk mod two64)%Z in
  let s := Z.log2 (two64 - m') in
  if (Z.eqb (two64 - m') (2 ^ s) && Z.ltb 0 s && Z.ltb s 64)%bool then Some s else None.

Fixpoint srl_expand (kn : list kentry) (ts : list (Z * expr)) : Z * list (Z * expr) :=
  match ts with
  | [] => (0%Z, [])
  | (k, a) :: rest =>
      let '(c, ts') := srl_expand kn rest in
      let keep := (c, lins_e k a ts') in
      match a with
      | EAlu ALU_SRL e (ELit s) =>
          let m := (2 ^ ((s mod two64) mod 64))%Z in
          if (Z.eqb (k mod m)%Z 0%Z && lin_nowrap kn e)%bool then
            let q := (k / m)%Z in
            let le := lin_of e in
            if Z.leb ((s mod two64) mod 64) (ealign kn e) then   (* [comment removed for export] *)
              ((c + q * fst le)%Z, fold_right (fun t acc => lins_e (q * fst t)%Z (snd t) acc) ts' (snd le))
            else
            ((c + q * fst le)%Z,
             lins_e (- q)%Z (srl_rem e m) (fold_right (fun t acc => lins_e (q * fst t)%Z (snd t) acc) ts' (snd le)))
          else keep
      | EAlu ALU_AND e (ELit mk) =>
          (* [comment removed for export] *)
          match highmask_s mk with
          | Some s =>
              if lin_nowrap kn e then
                let le := lin_of e in
                ((c + k * fst le)%Z,
                 lins_e (- k)%Z (srl_rem e (2 ^ s)) (fold_right (fun t acc => lins_e (k * fst t)%Z (snd t) acc) ts' (snd le)))
              else keep
          | None => keep
          end
      | _ => keep
      end
  end.

(* [comment removed for export] *)
Fixpoint has_srl (ts : list (Z * expr)) : bool :=
  match ts with
  | [] => false
  | (_, EAlu ALU_SRL _ (ELit _)) :: _ => true
  | _ :: rest => has_srl rest
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
(* [comment removed for export] *)
Definition fact_period (allkn : list kentry) (e : expr) (hi : Z) : option Z :=
  let l := lin_of e in
  match lin_range (erange allkn) (fst l) (snd l) with
  | Some (a, b) => let q := zdiv64 b in if Z.ltb (hi + q * two64) (a + two64) then Some q else None
  | None => None
  end.

(* [comment removed for export] *)
Definition unit_single (ts : list (Z * expr)) : bool :=
  match ts with [(k, _)] => Z.eqb (Z.abs k) 1 | _ => false end.
(* [comment removed for export] *)
Definition sum_fact_kr (allkn : list kentry) (e : expr) (lo hi : Z) : list sfact :=
  match e with
  | EVar _ => []
  | _ =>
    match lin_of e with
    | (c, (_ :: _) as ts) =>          (* [comment removed for export] *)
        if unit_single ts then [] else
        match fact_period allkn e hi with
        | Some q => let sh := (q * two64 - c)%Z in
            (ts, ((lo + sh)%Z, (hi + sh)%Z)) :: sum_fact_x allkn ts (lo + sh)%Z (hi + sh)%Z
        | None => []
        end
    | _ => []
    end
  end.
(* [comment removed for export] *)
Definition probe_mark_kr (allkn : list kentry) (j : nat) (n : expr) : list sfact :=
  match erange allkn (EVar j) with
  | Some (lo, hi) =>
      if Z.leb 1 lo then
        match n with
        | ELit z => [([(1%Z, EVar j)], (Z.max lo (zmod64 z), hi))]      (* [comment removed for export] *)
        | _ => sum_fact_kr allkn (EAlu ALU_SUB (EVar j) n) 0 hi
        end
      else []
  | None => []
  end.
Fixpoint sum_facts_raw (allkn kn : list kentry) : list sfact :=
  match kn with
  | [] => []
  | KRange e lo hi :: rest => sum_fact_kr allkn e lo hi ++ sum_facts_raw allkn rest
  | KDisj (SA (EVar j) 0%Z) (ELit 0%Z) (SA (ELit 0%Z) 0%Z) n :: rest => probe_mark_kr allkn j n ++ sum_facts_raw allkn rest
  | _ :: rest => sum_facts_raw allkn rest
  end.
(* [comment removed for export] *)
Fixpoint sf_ins (f : sfact) (l : list sfact) : list sfact :=
  match l with
  | [] => [f]
  | g :: r => if Nat.leb (length (fst g)) (length (fst f)) then f :: l else g :: sf_ins f r   (* [comment removed for export] *)
  end.
Fixpoint sf_sort (l : list sfact) : list sfact :=
  match l with [] => [] | f :: r => sf_ins f (sf_sort r) end.
Definition sum_facts (allkn kn : list kentry) : list sfact := sf_sort (sum_facts_raw allkn kn).

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

(* [comment removed for export] *)
Definition lin_rel_core (rng : expr -> option (Z * Z)) (fs : list sfact) (c : Z) (ts : list (Z * expr)) : option (Z * Z) :=
  match sum_subst fs ts 0 0 false with
  | (ts', (lo0, hi0), true) =>
      match lin_range rng c ts' with
      | Some (lo, hi) => Some ((lo + lo0)%Z, (hi + hi0)%Z)
      | None => None
      end
  | _ => None
  end.
Fixpoint sf_orders (fs all : list sfact) (ts : list (Z * expr)) : list (list sfact) :=
  match fs with
  | [] => []
  | f :: r => match fact_quot (fst f) ts None with
              | Some _ => (f :: all) :: sf_orders r all ts
              | None => sf_orders r all ts
              end
  end.
Fixpoint lin_rel_fold (rng : expr -> option (Z * Z)) (ords : list (list sfact)) (c : Z) (ts : list (Z * expr))
         (acc : option (Z * Z)) : option (Z * Z) :=
  match ords with
  | [] => acc
  | o :: r =>
      let acc' := match lin_rel_core rng o c ts, acc with
                  | Some (l, h), Some (l0, h0) => Some (Z.max l l0, Z.min h h0)
                  | Some p, None => Some p
                  | None, _ => acc
                  end in
      lin_rel_fold rng r c ts acc'
  end.
Definition lin_rel_multi (rng : expr -> option (Z * Z)) (fs : list sfact) (c : Z) (ts : list (Z * expr)) : option (Z * Z) :=
  lin_rel_fold rng (fs :: sf_orders fs fs ts) c ts None.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition zcdiv (a b : Z) : Z := (- ((- a) / b))%Z.
Fixpoint part_quot (fts ts : list (Z * expr)) : option (Z * Z) :=
  match fts with
  | [] => None
  | (k, a) :: r =>
      if Z.eqb k 0 then part_quot r ts else
      let K := coef_of a ts in
      if Z.eqb K 0 then part_quot r ts else
      let m := (Z.abs k / Z.gcd K k)%Z in
      if (Z.leb 1 m && Z.eqb ((m * K) mod k) 0)%bool then Some (m, (m * K) / k)%Z else part_quot r ts
  end.
Definition scale_ts (m : Z) (ts : list (Z * expr)) : list (Z * expr) := map (fun t => ((m * fst t)%Z, snd t)) ts.
Definition lin_eval (rng : expr -> option (Z * Z)) (fs : list sfact) (c : Z) (ts : list (Z * expr)) (test : Z -> Z -> bool) : bool :=
  match lin_rel_multi rng fs c ts with
  | Some (lo, hi) => test lo hi
  | None => false
  end
  || match lin_range rng c ts with
     | Some (lo, hi) => test lo hi
     | None => false
     end.
Fixpoint lin_chain (fuel : nat) (rng : expr -> option (Z * Z)) (fs : list sfact) (c : Z) (ts : list (Z * expr))
         (test : Z -> Z -> bool) {struct fuel} : bool :=
  lin_eval rng fs c ts test
  || match fuel with
     | O => false
     | S f =>
         existsb (fun sf : sfact =>
                    match part_quot (fst sf) ts with
                    | Some (m, q) =>
                        let d := if Z.leb 0 q then ((q * fst (snd sf))%Z, (q * snd (snd sf))%Z)
                                 else ((q * snd (snd sf))%Z, (q * fst (snd sf))%Z) in
                        lin_chain f rng fs (m * c)%Z (sub_fact q (fst sf) (scale_ts m ts))
                                  (fun lo hi => test (zcdiv (lo + fst d) m) ((hi + snd d) / m))%Z
                    | None => false
                    end) fs
     end.
(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint part_quots (fts ts : list (Z * expr)) : list (Z * Z) :=
  match fts with
  | [] => []
  | (k, a) :: r =>
      if Z.eqb k 0 then part_quots r ts else
      let K := coef_of a ts in
      if Z.eqb K 0 then part_quots r ts else
      let m := (Z.abs k / Z.gcd K k)%Z in
      if (Z.leb 1 m && Z.eqb ((m * K) mod k) 0)%bool then (m, (m * K) / k)%Z :: part_quots r ts else part_quots r ts
  end.
Fixpoint lin_chainA (fuel : nat) (rng : expr -> option (Z * Z)) (fs : list sfact) (c : Z) (ts : list (Z * expr))
         (test : Z -> Z -> bool) {struct fuel} : bool :=
  lin_eval rng fs c ts test
  || match fuel with
     | O => false
     | S f =>
         existsb (fun sf : sfact =>
                    existsb (fun mq : Z * Z =>
                        let m := fst mq in let q := snd mq in
                        let d := if Z.leb 0 q then ((q * fst (snd sf))%Z, (q * snd (snd sf))%Z)
                                 else ((q * snd (snd sf))%Z, (q * fst (snd sf))%Z) in
                        lin_chainA f rng fs (m * c)%Z (sub_fact q (fst sf) (scale_ts m ts))
                                   (fun lo hi => test (zcdiv (lo + fst d) m) ((hi + snd d) / m))%Z)
                      (part_quots (fst sf) ts)) fs
     end.
Definition lin_test_reldA (d : nat) (kn : list kentry) (c : Z) (ts : list (Z * expr)) (test : Z -> Z -> bool) : bool :=
  match sum_facts kn kn with
  | [] => false
  | fs => lin_chainA d (erange kn) fs c ts test
  end.
Definition LCHAIN : nat := 1%nat.
Definition lin_test_reld (d : nat) (kn : list kentry) (c : Z) (ts : list (Z * expr)) (test : Z -> Z -> bool) : bool :=
  match sum_facts kn kn with
  | [] => false
  | fs => lin_chain d (erange kn) fs c ts test
  end.
Definition lin_test_rel (kn : list kentry) (c : Z) (ts : list (Z * expr)) (test : Z -> Z -> bool) : bool :=
  lin_test_reld LCHAIN kn c ts test.
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition lin_testd (d : nat) (kn : list kentry) (c : Z) (ts : list (Z * expr)) (test : Z -> Z -> bool) : bool :=
  match lin_range (erange kn) c ts with
  | Some (lo, hi) => if test lo hi then true else lin_test_reldA d kn c ts test
  | None => lin_test_reldA d kn c ts test
  end.

Definition lin_test (kn : list kentry) (c : Z) (ts : list (Z * expr)) (test : Z -> Z -> bool) : bool :=
  match lin_range (erange kn) c ts with
  | Some (lo, hi) => if test lo hi then true else lin_test_rel kn c ts test
  | None => lin_test_rel kn c ts test
  end.

(* [comment removed for export] *)
Fixpoint srl_scale_need (ts : list (Z * expr)) : Z :=
  match ts with
  | [] => 0
  | (k, EAlu ALU_SRL _ (ELit s)) :: rest => Z.max (((s mod two64) mod 64) - ctz64 k)%Z (srl_scale_need rest)
  | _ :: rest => srl_scale_need rest
  end.
Definition lin_srange (kn : list kentry) (e : expr) : option (Z * Z) :=
  let l := lin_of e in
  let j := srl_scale_need (snd l) in
  if (if Z.leb 0 j then Z.leb j 24 else false) then   (* [comment removed for export] *)
    let sc := (2 ^ j)%Z in
    let ts := List.map (fun t => ((sc * fst t)%Z, snd t)) (snd l) in
    let '(c2, t2) := srl_expand kn ts in
    let '(c3, t3) := (if has_srl t2 then srl_expand kn t2 else (0%Z, t2)) in
    match lin_range (erange kn) (sc * fst l + c2 + c3)%Z t3 with
    | Some (lo', hi') =>
        let lo := zcdiv lo' sc in let hi := (hi' / sc)%Z in
        if (if Z.leb 0 lo then (if Z.leb lo hi then Z.ltb hi two64 else false) else false) then Some (lo, hi) else None
    | None => None
    end
  else None.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition lin_unit (l : lin) : bool :=
  match l with (c, [(k, _)]) => (Z.eqb c 0 && Z.eqb k 1)%bool | _ => false end.
Definition lin_nowrapR (kn : list kentry) (e : expr) : bool :=
  let l := lin_of e in
  if lin_unit l then true else                           (* [comment removed for export] *)
  (* [comment removed for export] *)
  if lin_test kn (fst l) (snd l) (fun lo hi => (Z.leb 0 lo && Z.ltb hi two64)%bool) then true else
  let '(c2, t2) := srl_expand kn (snd l) in            (* [comment removed for export] *)
  if lin_test kn (fst l + c2)%Z t2 (fun lo hi => (Z.leb 0 lo && Z.ltb hi two64)%bool) then true
  else (* [comment removed for export] *)
    match lin_srange kn e with Some _ => true | None => false end.

(* [comment removed for export] *)
Definition lin_negwrapR (kn : list kentry) (e : expr) : bool :=
  let l := lin_of e in
  lin_test kn (fst l) (snd l) (fun lo hi => (Z.leb (- two64) lo && Z.ltb hi 0)%bool).

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
Definition lin_apart0 (kn : list kentry) (b1 : expr) (k1 n1 : Z) (b2 : expr) (k2 n2 : Z) : bool :=
  (lin_nowrapR kn b1 && lin_nowrapR kn b2 &&
   let l1 := lin_of b1 in let l2 := lin_of b2 in
   lin_test kn (fst l2 + k2 - fst l1 - k1)%Z (lsub_e (snd l2) (snd l1))
            (fun lo hi => (Z.leb n1 lo || Z.leb hi (- n2))%bool))%bool.
Definition lin_apart (kn : list kentry) (b1 : expr) (k1 n1 : Z) (b2 : expr) (k2 n2 : Z) : bool :=
  if shares_var b1 b2 then lin_apart0 kn b1 k1 n1 b2 k2 n2 else false.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition zlit64 (z : Z) : Z := if (Z.leb 0 z && Z.ltb z two64)%bool then z else (z mod two64)%Z.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition iv_isect (a b : option (Z * Z)) : option (Z * Z) :=
  match a, b with
  | Some (l1, h1), Some (l2, h2) => Some (Z.max l1 l2, Z.min h1 h2)
  | Some r, None => Some r
  | None, r => r
  end.
Definition lin_iv1 (rng : expr -> option (Z * Z)) (all : list sfact) (c : Z) (ts : list (Z * expr)) : option (Z * Z) :=
  iv_isect (lin_rel_multi rng all c ts) (lin_range rng c ts).
Fixpoint lin_ivs_chain (rng : expr -> option (Z * Z)) (fs all : list sfact) (c : Z) (ts : list (Z * expr)) (acc : option (Z * Z))
  : option (Z * Z) :=
  match fs with
  | [] => acc
  | sf :: r =>
      let acc' :=
        match part_quot (fst sf) ts with
        | Some (m, q) =>
            let d := if Z.leb 0 q then ((q * fst (snd sf))%Z, (q * snd (snd sf))%Z) else ((q * snd (snd sf))%Z, (q * fst (snd sf))%Z) in
            match lin_iv1 rng all (m * c)%Z (sub_fact q (fst sf) (scale_ts m ts)) with
            | Some (lo, hi) => iv_isect acc (Some (zcdiv (lo + fst d) m, (hi + snd d) / m))%Z
            | None => acc
            end
        | None => acc
        end in
      lin_ivs_chain rng r all c ts acc'
  end.
Definition lin_brange (kn : list kentry) (e : expr) : option (Z * Z) :=
  let l := lin_of e in
  match sum_facts kn kn with
  | [] => None
  | fs =>
      match iv_isect (lin_rel_multi (erange kn) fs (fst l) (snd l))
                     (iv_isect (lin_ivs_chain (erange kn) fs fs (fst l) (snd l) None) (lin_range (erange kn) (fst l) (snd l))) with   (* [comment removed for export] *)
      | Some (lo', hi') =>
          if (Z.leb 0 lo' && Z.ltb hi' two64)%bool then Some (lo', hi')
          else (* [comment removed for export] *)
            let q := zdiv64 lo' in
            if Z.eqb q (zdiv64 hi') then Some ((lo' - q * two64)%Z, (hi' - q * two64)%Z) else None
      | None => None
      end
  end.
Definition xlo (kn : list kentry) (e : expr) : option Z :=
  match e with
  | ELit z => Some (zlit64 z)
  | _ => match erange kn e with
         | Some (lo, _) => Some lo
         | None => match lin_brange kn e with
                   | Some (lo, _) => Some lo
                   | None => match lin_srange kn e with Some (lo, _) => Some lo | None => None end   (* [comment removed for export] *)
                   end
         end
  end.
Definition xhi (kn : list kentry) (e : expr) : option Z :=
  match e with
  | ELit z => Some (zlit64 z)
  | _ => match erange kn e with
         | Some (_, hi) => Some hi
         | None => match lin_brange kn e with
                   | Some (_, hi) => Some hi
                   | None => match lin_srange kn e with Some (_, hi) => Some hi | None => None end   (* [comment removed for export] *)
                   end
         end
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition xrange2 (kn : list kentry) (e : expr) : option (Z * Z) :=
  match e with
  | ELit z => let v := zlit64 z in Some (v, v)
  | _ =>
    match erange kn e, lin_brange kn e with
    | Some (l1, h1), Some (l2, h2) => Some (Z.max l1 l2, Z.min h1 h2)
    | Some r, None => Some r
    | None, Some r => Some r
    | None, None => None
    end
  end.
Definition base_rangeX (kn : list kentry) (e : expr) : option (Z * Z) :=
  let plain := base_range kn e in
  match e with
  | EAlu ALU_SRL a (ELit s) =>
      let m := (2 ^ ((s mod two64) mod 64))%Z in
      match xrange2 kn a with
      | Some (lo, hi) =>
          match plain with
          | Some (plo, phi) => Some (Z.max plo (lo / m)%Z, Z.min phi (hi / m)%Z)
          | None => Some ((lo / m)%Z, (hi / m)%Z)
          end
      | None => plain
      end
  | _ => match plain, lin_brange kn e with
         | Some (l1, h1), Some (l2, h2) => Some (Z.max l1 l2, Z.min h1 h2)
         | Some r, None => Some r
         | None, _ => xrange2 kn e
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
Definition lin_ge0_scaled (kn : list kentry) (c : Z) (ts : list (Z * expr)) : bool :=
  let j := srl_scale_need ts in
  if (if Z.ltb 0 j then Z.leb j 24 else false) then
    let sc := (2 ^ j)%Z in
    let ts' := List.map (fun t => ((sc * fst t)%Z, snd t)) ts in
    let '(c2, t2) := srl_expand kn ts' in
    let '(c3, t3) := (if has_srl t2 then srl_expand kn t2 else (0%Z, t2)) in
    lin_test kn (sc * c + c2 + c3)%Z t3 (fun lo _ => Z.leb 0 lo)
  else false.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition lin_try_ge0 (kn : list kentry) (c : Z) (ts : list (Z * expr)) : option bool :=
  match lin_range (erange kn) c ts with
  | Some (lo, hi) => if Z.leb 0 lo then Some true
                     else if Z.ltb hi 0 then None
                     else Some (lin_test_rel kn c ts (fun lo _ => Z.leb 0 lo))
  | None => Some (lin_test_rel kn c ts (fun lo _ => Z.leb 0 lo))
  end.

Definition lin_ge0 (kn : list kentry) (pos neg : xterms) : bool :=
  (xt_nowrap kn pos && xt_nowrap kn neg &&
   (* [comment removed for export] *)
   (match lin_try_ge0 kn (xt_const pos - xt_const neg)%Z (lsub_e (xt_lin pos) (xt_lin neg)) with
   | Some true => true
   | None => false                     (* [comment removed for export] *)
   | Some false =>
         let '(c2, t2) := srl_expand kn (lsub_e (xt_lin pos) (xt_lin neg)) in
         if lin_test kn (xt_const pos - xt_const neg + c2)%Z t2 (fun lo _ => Z.leb 0 lo) then true
         else (* [comment removed for export] *)
         if (if has_srl t2 then
               let '(c3, t3) := srl_expand kn t2 in
               lin_test kn (xt_const pos - xt_const neg + c2 + c3)%Z t3 (fun lo _ => Z.leb 0 lo)
             else false) then true
         else (* [comment removed for export] *)
           lin_ge0_scaled kn (xt_const pos - xt_const neg)%Z (lsub_e (xt_lin pos) (xt_lin neg))
   end))%bool.

(* [comment removed for export] *)
Definition lin_ge0d (d : nat) (kn : list kentry) (pos neg : xterms) : bool :=
  (xt_nowrap kn pos && xt_nowrap kn neg &&
   (lin_testd d kn (xt_const pos - xt_const neg)%Z (lsub_e (xt_lin pos) (xt_lin neg)) (fun lo _ => Z.leb 0 lo)
    || lin_ge0 kn pos neg))%bool.

(* [comment removed for export] *)
Definition xinside0 (kn : list kentry) (b1 : expr) (k1 : Z) (n1 : expr) (b2 : expr) (k2 : Z) (n2 : expr) : bool :=
  if lin_ge0 kn [(b1, k1)] [(b2, k2)] then lin_ge0 kn [(b2, k2); (n2, 0%Z)] [(b1, k1); (n1, 0%Z)] else false.
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition xend_hi (kn : list kentry) (b1 : expr) (k1 : Z) (n1 : expr) (hi1 h1 : Z) : Z :=
  match xhi kn (unlin (ladd (lin_of b1) (lin_of n1))) with
  | Some j => if Z.ltb (hi1 + h1) two64 then Z.min (hi1 + k1 + h1) (j + k1) else hi1 + k1 + h1
  | None => hi1 + k1 + h1
  end.
Definition xinside_num (kn : list kentry) (b1 : expr) (k1 : Z) (n1 : expr) (b2 : expr) (k2 : Z) (n2 : expr) : bool :=
  match xlo kn b2, xhi kn b2 with
  | Some lo2, Some hi2 =>
      if Z.eqb lo2 hi2 then
        match xlo kn n2 with
        | Some l2 =>
            (* [comment removed for export] *)
            if match base_range kn b1 with
               | Some (lo1p, hi1p) => (Z.ltb (hi1p + k1) (lo2 + k2) || Z.ltb (lo2 + k2 + l2) (lo1p + k1))%bool
               | None => false
               end then false
            else
            match base_rangeX kn b1, xhi kn n1 with       (* [comment removed for export] *)
            | Some (lo1, hi1), Some h1 => Z.leb (lo2 + k2) (lo1 + k1) && Z.leb (xend_hi kn b1 k1 n1 hi1 h1) (lo2 + k2 + l2)
            | _, _ => false
            end
        | None => false
        end
      else false
  | _, _ => false
  end.
Definition xinside (kn : list kentry) (b1 : expr) (k1 : Z) (n1 : expr) (b2 : expr) (k2 : Z) (n2 : expr) : bool :=
  if shares_var b1 b2 then xinside0 kn b1 k1 n1 b2 k2 n2
  else if novars b2 then xinside_num kn b1 k1 n1 b2 k2 n2 else false.

(* [comment removed for export] *)
Definition kshok_entailed (fk kn : list kentry) (b : expr) (o : Z) (n : expr) : bool :=
  existsb (fun K => match K with
                    | KShOk (SA b' o') n' => xinside fk b o n b' o' n'
                    | _ => false
                    end) kn.


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

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition shpre_apart (kn : list kentry) (b1 : expr) (k1 n1 : Z) (b2 : expr) (k2 n2 : Z) : bool :=
  match b1 with
  | EAlu ALU_SRL x1 (ELit c1) =>
      Z.eqb c1 3 && Z.leb 3 (ealign kn x1) && Z.leb SB k1 && Z.leb SB k2 && Z.leb 0 n1 && Z.leb 0 n2
      && match b2 with
         | ELit z2 => Z.eqb z2 0 && kdisj_apart kn kn x1 (8 * (k1 - SB)) (8 * n1) (ELit 0) (8 * (k2 - SB)) (8 * n2)
         | EAlu ALU_SRL x2 (ELit c2) => Z.eqb c2 3 && Z.leb 3 (ealign kn x2) && kdisj_apart kn kn x1 (8 * (k1 - SB)) (8 * n1) x2 (8 * (k2 - SB)) (8 * n2)
         | _ => false
         end
  | _ => false
  end%bool.
Definition itv_apartX (kn : list kentry) (b1 : expr) (k1 n1 : Z) (b2 : expr) (k2 n2 : Z) : bool :=
  match base_rangeX kn b1, base_rangeX kn b2 with
  | Some (lo1, hi1), Some (lo2, hi2) => (Z.leb (hi1 + k1 + n1) (lo2 + k2) || Z.leb (hi2 + k2 + n2) (lo1 + k1))%bool
  | _, _ => false
  end
  || shpre_apart kn b1 k1 n1 b2 k2 n2 || shpre_apart kn b2 k2 n2 b1 k1 n1.   (* [comment removed for export] *)
Definition ranges_apart (kn : list kentry) (b1 : expr) (k1 n1 : Z) (b2 : expr) (k2 n2 : Z) : bool :=
  if (match base_range kn b1, base_range kn b2 with
      | Some (lo1, hi1), Some (lo2, hi2) =>
          (Z.leb (hi1 + k1 + n1) (lo2 + k2) || Z.leb (hi2 + k2 + n2) (lo1 + k1))%bool
      | _, _ => false
      end) then true
  else if kdisj_apart kn kn b1 k1 n1 b2 k2 n2 then true
  else if lin_apart kn b1 k1 n1 b2 k2 n2 then true
  else if itv_apartX kn b1 k1 n1 b2 k2 n2 then true          (* [comment removed for export] *)
  (* [comment removed for export] *)
  else if (Z.leb 0 n1 && Z.ltb n1 two64 && lin_ge0 kn [(b2, k2)] [(b1, k1); (ELit n1, 0%Z)])%bool then true
  else (Z.leb 0 n2 && Z.ltb n2 two64 && lin_ge0 kn [(b1, k1)] [(b2, k2); (ELit n2, 0%Z)])%bool.

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
(* [comment removed for export] *)
Definition end_hi (kn : list kentry) (b : expr) (k : Z) (n : expr) (lo1 hi1 h1 : Z) : option Z :=
  match n with
  | ELit _ => None
  | _ => if (if Z.leb 0 (lo1 + k) then Z.ltb (hi1 + k + h1) two64 else false)
         then match find_range (facts_of kn) (mkAlu ALU_ADD (mkAlu ALU_ADD b (ELit k)) n) with
              | Some (_, ehi) => Some ehi
              | None => None
              end
         else None
  end.

Definition ranges_apart_x (kn : list kentry) (b1 : expr) (k1 : Z) (n1 : expr) (b2 : expr) (k2 : Z) (n2 : expr) : bool :=
  match n1, n2 with
  | ELit z1, ELit z2 => ranges_apart kn b1 k1 (zlit64 z1) b2 k2 (zlit64 z2)
  | _, _ =>
    if (match base_range kn b1, base_range kn b2, xhi kn n1, xhi kn n2 with
        | Some (lo1, hi1), Some (lo2, hi2), Some h1, Some h2 =>
            if (Z.leb (hi1 + k1 + h1) (lo2 + k2) || Z.leb (hi2 + k2 + h2) (lo1 + k1))%bool then true
            else (* [comment removed for export] *)
            if match end_hi kn b1 k1 n1 lo1 hi1 h1 with Some e1 => Z.leb e1 (lo2 + k2) | None => false end then true
            else match end_hi kn b2 k2 n2 lo2 hi2 h2 with Some e2 => Z.leb e2 (lo1 + k1) | None => false end
        | _, _, _, _ => false
        end) then true
    else if kdisj_apart_x kn kn b1 k1 n1 b2 k2 n2 then true
    else if negb (shares_var b1 b2) then false
    else if lin_ge0 kn [(b2, k2)] [(b1, k1); (n1, 0%Z)] then true
    else lin_ge0 kn [(b1, k1)] [(b2, k2); (n2, 0%Z)]
  end.

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
      else if lin_apart kn b1 k1 m1 b2 k2 m2 then true
      else if itv_apartX kn b1 k1 m1 b2 k2 m2 then true
      else if (Z.leb 0 m1 && Z.ltb m1 two64 && lin_ge0 kn [(b2, k2)] [(b1, k1); (ELit m1, 0%Z)])%bool then true   (* [comment removed for export] *)
      else (Z.leb 0 m2 && Z.ltb m2 two64 && lin_ge0 kn [(b1, k1)] [(b2, k2); (ELit m2, 0%Z)])%bool
  | _, _ =>
    if (match sp_rng sp, base_range kn b2, sp_h1 sp, xhi kn n2 with
        | Some (lo1, hi1), Some (lo2, hi2), Some h1, Some h2 =>
            if (Z.leb (hi1 + k1 + h1) (lo2 + k2) || Z.leb (hi2 + k2 + h2) (lo1 + k1))%bool then true
            else (* [comment removed for export] *)
            if match end_hi kn b1 k1 n1 lo1 hi1 h1 with Some e1 => Z.leb e1 (lo2 + k2) | None => false end then true
            else match end_hi kn b2 k2 n2 lo2 hi2 h2 with Some e2 => Z.leb e2 (lo1 + k1) | None => false end
        | _, _, _, _ => false
        end) then true
    else if in_sides_x kn (sp_Dx sp) b2 k2 n2 then true
    else if negb (shares_var b1 b2) then false
    else if lin_ge0 kn [(b2, k2)] [(b1, k1); (n1, 0%Z)] then true
    else lin_ge0 kn [(b1, k1)] [(b2, k2); (n2, 0%Z)]
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
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
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Inductive lres :=
| LHit (v : expr) (scs : list sidecond) (hints : list bool)
| LMiss (scs : list sidecond) (hints : list bool)     (* [comment removed for export] *)
| LStuck.

Fixpoint zbytes_le_to_Z (bs : list Z) : Z :=
  match bs with
  | [] => 0
  | b :: rest => Z.lor b (Z.shiftl (zbytes_le_to_Z rest) 8)
  end.

Definition lit_of_bytes (sx : bool) (n : nat) (bs : list Z) : expr :=
  ELit (let u := zbytes_le_to_Z bs in if sx then bv_swrap (8 * N.of_nat n) u else u).

(* [comment removed for export] *)
Fixpoint log_byte_lit (log : list sentry) (rb : expr) (rk : Z) : option Z :=
  match log with
  | [] => None
  | SE (SA kb kk) w v :: rest =>
      match rel_lit rb rk 1 kb kk (Z.of_nat w) with
      | RInside d => match v with
                     | ELit z => Some (((z mod two64) / 2 ^ (8 * d)) mod 256)%Z
                     | _ => None
                     end
      | RDisjoint => log_byte_lit rest rb rk
      | _ => None
      end
  end.

(* [comment removed for export] *)
Fixpoint log_bytes_lit (log : list sentry) (rb : expr) (rk : Z) (n : nat) : option (list Z) :=
  match n with
  | O => Some []
  | S n' => match log_byte_lit log rb rk, log_bytes_lit log rb (rk + 1) n' with
            | Some b, Some r => Some (b :: r)
            | _, _ => None
            end
  end.

(* [comment removed for export] *)
Fixpoint log_lookup (kn : list kentry) (log : list sentry) (rb : expr) (rk : Z) (n : nat) (sx : bool)
         (hints : list bool) (acc : list sidecond) : lres :=
  match log with
  | [] => LMiss acc hints
  | SE (SA kb kk) w v :: rest =>
      match rel_lit rb rk (Z.of_nat n) kb kk (Z.of_nat w) with
      | RInside d => LHit (mkExt sx (Z.to_nat d) n v) acc hints
      | RDisjoint => log_lookup kn rest rb rk n sx hints acc
      | RPartial => match log_bytes_lit log rb rk n with
                    | Some bs => LHit (lit_of_bytes sx n bs) acc hints
                    | None => LStuck
                    end
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
Definition fill_lit (sx : bool) (n : nat) (c : Z) : expr :=
  lit_of_bytes sx n (repeat (c mod 256)%Z n).

(* [comment removed for export] *)
Fixpoint know_byte_lit (segs : list Segment) (kn : list kentry) (rb : expr) (rk : Z) : option Z :=
  match kn with
  | [] => None
  | K :: rest =>
      match K with
      | KWord (SA kb kk) w (ELit z) =>
          match rel_lit rb rk 1 kb kk (Z.of_nat w) with
          | RInside d => Some (((z mod two64) / 2 ^ (8 * d)) mod 256)%Z
          | _ => know_byte_lit segs rest rb rk
          end
      | KZero (SA kb kk) (ELit l0) =>
          match rel_lit rb rk 1 kb kk (l0 mod 2 ^ 64)%Z with
          | RInside _ => Some 0%Z
          | _ => know_byte_lit segs rest rb rk
          end
      | KFill (SA kb kk) (ELit l0) c =>
          match rel_lit rb rk 1 kb kk (l0 mod 2 ^ 64)%Z with
          | RInside _ => Some (c mod 256)%Z
          | _ => know_byte_lit segs rest rb rk
          end
      | KImg lo hi =>
          match rb with
          | ELit 0 =>
              if (Z.leb lo rk && Z.ltb rk hi)%bool then
                match seg_rom segs (Z_to_bv 64 rk) with
                | Some b => Some (bv_unsigned b)
                | None => None            (* [comment removed for export] *)
                end
              else know_byte_lit segs rest rb rk
          | _ => know_byte_lit segs rest rb rk
          end
      | _ => know_byte_lit segs rest rb rk
      end
  end.

(* [comment removed for export] *)
Fixpoint know_bytes_lit (segs : list Segment) (kn : list kentry) (rb : expr) (rk : Z) (n : nat)
  : option (list Z) :=
  match n with
  | O => Some []
  | S n' => match know_byte_lit segs kn rb rk, know_bytes_lit segs kn rb (rk + 1) n' with
            | Some b, Some r => Some (b :: r)
            | _, _ => None
            end
  end.

(* [comment removed for export] *)
Fixpoint know_lookupA0 (allkn : list kentry) (segs : list Segment) (kn : list kentry) (rb : expr) (rk : Z)
         (n : nat) (sx : bool) (hints : list bool) (acc : list sidecond) : lres :=
  let know_lookup := know_lookupA0 allkn in
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
      | KFill (SA kb kk) len c =>
          (* [comment removed for export] *)
          let hit := fill_lit sx n c in
          match len with
          | ELit l0 =>
              match rel_lit rb rk (Z.of_nat n) kb kk (l0 mod 2^64)%Z with
              | RInside _ => LHit hit acc hints
              | RDisjoint | RPartial => know_lookup segs rest rb rk n sx hints acc
              | RUnknown =>
                  if xinside allkn rb rk (elen n) kb kk len then LHit hit acc hints else
                  match hints with
                  | true :: hs => LHit hit (SCInside (SA rb rk) (elen n) (SA kb kk) len :: acc) hs
                  | false :: hs => know_lookup segs rest rb rk n sx hs acc
                  | [] => know_lookup segs rest rb rk n sx [] acc
                  end
              end
          | _ =>
              if xinside allkn rb rk (elen n) kb kk len then LHit hit acc hints else
              match hints with
              | true :: hs => LHit hit (SCInside (SA rb rk) (elen n) (SA kb kk) len :: acc) hs
              | false :: hs => know_lookup segs rest rb rk n sx hs acc
              | [] => know_lookup segs rest rb rk n sx [] acc
              end
          end
      | KUnk _ _ => know_lookup segs rest rb rk n sx hints acc   (* [comment removed for export] *)
      | KShOk _ _ => know_lookup segs rest rb rk n sx hints acc  (* [comment removed for export] *)
      | KFpc _ _ _ => know_lookup segs rest rb rk n sx hints acc (* [comment removed for export] *)
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
                  (* [comment removed for export] *)
                  if match erange allkn len with   (* [comment removed for export] *)
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

(* [comment removed for export] *)
Definition know_lookupA (allkn : list kentry) (segs : list Segment) (kn : list kentry) (rb : expr) (rk : Z)
         (n : nat) (sx : bool) (hints : list bool) (acc : list sidecond) : lres :=
  match know_lookupA0 allkn segs kn rb rk n sx hints acc with
  | LMiss acc' hints' =>
      match know_bytes_lit segs kn rb rk n with
      | Some bs => LHit (lit_of_bytes sx n bs) acc' hints'
      | None => LMiss acc' hints'
      end
  | r => r
  end.

Definition know_lookup (segs : list Segment) (kn : list kentry) (rb : expr) (rk : Z)
         (n : nat) (sx : bool) (hints : list bool) (acc : list sidecond) : lres :=
  know_lookupA kn segs kn rb rk n sx hints acc.

(* [comment removed for export] *)
Fixpoint coeffs_divk (kn : list kentry) (m : Z) (ts : list (Z * expr)) : bool :=
  match ts with
  | [] => true
  | (k, a) :: rest => ((Z.eqb (k mod m) 0 || Z.eqb ((k * 2 ^ ealign kn a) mod m) 0) && coeffs_divk kn m rest)%bool
  end.

(* [comment removed for export] *)
Fixpoint find_res (fk : list kentry) (t : expr) (s : Z) : option Z :=
  match fk with
  | [] => None
  | KAlign e m :: rest =>
      match (match snd (lin_of e) with
             | [(k, t')] =>
                 if (Z.eqb k 1 && expr_eqb t t' && Z.ltb 0 m && Z.eqb m (2 ^ ctz64 m) && Z.leb s (ctz64 m))%bool
                 then Some ((- fst (lin_of e)) mod 2 ^ s)%Z else None
             | _ => None
             end) with
      | Some r => Some r
      | None => find_res rest t s
      end
  | _ :: rest => find_res rest t s
  end.

(* [comment removed for export] *)
Definition term_res (kn : list kentry) (t : expr) (s : Z) : option Z :=
  if Z.leb s (ealign kn t) then Some 0%Z else find_res (facts_of kn) t s.

(* [comment removed for export] *)
Fixpoint terms_res (kn : list kentry) (s : Z) (ts : list (Z * expr)) : option Z :=
  match ts with
  | [] => Some 0%Z
  | (k, t) :: rest =>
      match terms_res kn s rest with
      | None => None
      | Some acc => if Z.eqb (k mod 2 ^ s) 0 then Some acc
                    else match term_res kn t s with Some r => Some (k * r + acc)%Z | None => None end
      end
  end.

Definition lin_lowbits_kn (kn : list kentry) (e : expr) (k : Z) : option Z :=
  let l := lin_of e in
  if coeffs_divk kn (2 ^ k) (snd l) then Some ((fst l) mod 2 ^ k)%Z
  else match pageup_low e (2 ^ k) with   (* [comment removed for export] *)
       | Some r => Some r
       | None => (* [comment removed for export] *)
           match terms_res kn k (snd l) with
           | Some r => Some ((fst l + r) mod 2 ^ k)%Z
           | None => None
           end
       end.

(* [comment removed for export] *)
Fixpoint ldiv_terms (m : Z) (ts : list (Z * expr)) : list (Z * expr) :=
  match ts with
  | [] => []
  | (k, a) :: rest => ((k / m)%Z, a) :: ldiv_terms m rest
  end.

(* [comment removed for export] *)
Fixpoint lsplit_divc (m : Z) (ts : list (Z * expr)) : list (Z * expr) * list (Z * expr) :=
  match ts with
  | [] => ([], [])
  | (k, a) :: rest =>
      let (d, r) := lsplit_divc m rest in
      if Z.eqb (k mod m) 0 then ((k, a) :: d, r) else (d, (k, a) :: r)
  end.

(* [comment removed for export] *)
Definition lin_nowrap_l (kn : list kentry) (c : Z) (ts : list (Z * expr)) : bool :=
  match lin_range (erange kn) c ts with
  | Some (lo, hi) => (Z.leb 0 lo && Z.ltb hi two64)%bool
  | None => false
  end.

(* [comment removed for export] *)
Definition lin_period (kn : list kentry) (a : expr) : option Z :=
  let l := lin_of a in
  match lin_range (erange kn) (fst l) (snd l) with
  | Some (lo, hi) => let q := zdiv64 lo in if Z.eqb q (zdiv64 hi) then Some q else None
  | None => None
  end.

(* [comment removed for export] *)
Fixpoint srl_terms (s : Z) (ts : list (Z * expr)) : list (Z * expr) :=
  match ts with
  | [] => []
  | (k, t) :: rest =>
      if Z.eqb (k mod 2 ^ s) 0 then lins (k / 2 ^ s) t (srl_terms s rest)
      else lins k (EAlu ALU_SRL t (ELit s)) (srl_terms s rest)
  end.

Definition mkSrl_res (kn : list kentry) (a : expr) (s : Z) : expr :=
  let l := lin_of a in
  match (if (negb (lin_trivial l) && lin_nowrap kn a)%bool then terms_res kn s (snd l) else None) with
  | Some r => unlin (((fst l + r) / 2 ^ s)%Z, srl_terms s (snd l))
  | None => mkAlu ALU_SRL a (ELit s)
  end.

Definition mkSrl (kn : list kentry) (a : expr) (s : Z) : expr :=
  let l := lin_of a in
  let m := (2 ^ s)%Z in
  match (if (negb (lin_trivial l) && coeffs_div m (snd l))%bool then lin_period kn a else None) with
  | Some q => unlin (((fst l - q * two64) / m)%Z, ldiv_terms m (snd l))   (* [comment removed for export] *)
  | None =>
  if (negb (lin_trivial l) && coeffs_div m (snd l) && lin_nowrap kn a)%bool
  then unlin ((fst l / m)%Z, ldiv_terms m (snd l))     (* [comment removed for export] *)
  else
    (* [comment removed for export] *)
    match (if (negb (lin_trivial l) && lin_nowrap kn a)%bool then lsplit_divc m (snd l) else ([], [])) with
    | ((_ :: _) as dts, (_ :: _) as rts) =>
        match (if lin_nowrap_l kn (fst l) rts then erange kn (unlin (fst l, rts)) else None) with
        | Some (lo, hi) =>
            if Z.eqb (lo / m) (hi / m) then unlin ((lo / m)%Z, ldiv_terms m dts)
            else mkSrl_res kn a s
        | None => mkSrl_res kn a s
        end
    | _ => mkSrl_res kn a s
    end
  end.

(* [comment removed for export] *)
Fixpoint lowbits (kn : list kentry) (e : expr) (j : Z) {struct e} : option Z :=
  let m := (2 ^ j)%Z in
  let dflt := if Z.leb j (ealign kn e) then Some 0%Z else lin_lowbits_kn kn e j in
  match e with
  | ELit z => Some ((z mod two64) mod m)%Z
  | EAlu ALU_AND a (ELit c) =>
      if Z.eqb ((c mod two64) mod m) 0 then Some 0%Z else
      match lowbits kn a j with Some v => Some (Z.land v ((c mod two64) mod m)) | None => dflt end
  | EAlu ALU_OR a (ELit c) =>
      match lowbits kn a j with Some v => Some (Z.lor v ((c mod two64) mod m)) | None => dflt end
  | EAlu ALU_XOR a (ELit c) =>
      match lowbits kn a j with Some v => Some (Z.lxor v ((c mod two64) mod m)) | None => dflt end
  | EAlu ALU_ADD a b =>
      match lowbits kn a j, lowbits kn b j with Some x, Some y => Some ((x + y) mod m)%Z | _, _ => dflt end
  | EAlu ALU_SUB a b =>
      match lowbits kn a j, lowbits kn b j with Some x, Some y => Some ((x - y) mod m)%Z | _, _ => dflt end
  | EMd M_MUL (ELit c) a =>
      if Z.eqb ((c mod two64) mod m) 0 then Some 0%Z else
      match lowbits kn a j with Some v => Some ((c * v) mod m)%Z | None => dflt end
  | EExt false O n a =>
      (* [comment removed for export] *)
      if Z.leb j (8 * Z.of_nat n) then match lowbits kn a j with Some v => Some v | None => dflt end else dflt
  | _ => dflt
  end.

(* [comment removed for export] *)
Fixpoint lsplit_div (kn : list kentry) (m : Z) (ts : list (Z * expr)) : list (Z * expr) * list (Z * expr) :=
  match ts with
  | [] => ([], [])
  | (k, a) :: rest =>
      let (d, r) := lsplit_div kn m rest in
      if (Z.eqb (k mod m) 0 || Z.eqb ((k * 2 ^ ealign kn a) mod m) 0)%bool then ((k, a) :: d, r) else (d, (k, a) :: r)
  end.

(* [comment removed for export] *)
Definition and_high_split (kn : list kentry) (bk : expr) (j c : Z) (dts rts : list (Z * expr)) : expr :=
  let m := (2 ^ j)%Z in
  let cA := (c - c mod m)%Z in
  let r := unlin ((c mod m)%Z, rts) in
  match erange kn r with
  | Some (lo, hi) =>
      if Z.eqb (lo / m) (hi / m) then unlin ((cA + (lo / m) * m)%Z, dts)
      else mkAlu ALU_ADD (unlin (cA, dts)) (mkAlu ALU_AND r bk)
  | None => mkAlu ALU_ADD (unlin (cA, dts)) (mkAlu ALU_AND r bk)
  end.

Definition and_low_split (kn : list kentry) (bk : expr) (j c : Z) (rts : list (Z * expr)) : expr :=
  let m := (2 ^ j)%Z in
  let r := unlin ((c mod m)%Z, rts) in
  match erange kn r with
  | Some (lo, hi) =>
      if Z.eqb (lo / m) (hi / m) then unlin ((c mod m - (lo / m) * m)%Z, rts)
      else mkAlu ALU_AND r bk
  | None => mkAlu ALU_AND r bk
  end.

(* [comment removed for export] *)
Definition mkAnd0 (kn : list kentry) (a b : expr) : expr :=
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
                match (if lin_trivial l then None else terms_res kn j (snd l)) with
                | Some r => unlin ((fst l - (fst l + r) mod 2 ^ j)%Z, snd l)
                | None =>
                (* [comment removed for export] *)
                match (if lin_trivial l then ([], snd l) else lsplit_div kn (2 ^ j) (snd l)) with
                | ((_ :: _) as dts, (_ :: _) as rts) => and_high_split kn b j (fst l) dts rts
                | _ => (* [comment removed for export] *)
                       mkMd M_MUL (ELit (2 ^ j)%Z) (mkSrl kn a j)
                end
                end)
      else
        let j2 := Z.log2 (k' + 1) in
        if (Z.eqb (k' + 1) (2 ^ j2) && Z.ltb j2 64)%bool then
          (* [comment removed for export] *)
          (if Z.leb j2 (ealign kn a) then ELit 0
           else match lowbits kn a j2 with        (* [comment removed for export] *)
           | Some v => ELit v
           | None =>
           if lin_trivial (lin_of a) then mkAlu ALU_AND a b
           else match lin_lowbits_kn kn a j2 with
                | Some v => ELit v
                | None => (* [comment removed for export] *)
                    match lsplit_div kn (2 ^ j2) (snd (lin_of a)) with
                    | (_ :: _, (_ :: _) as rts) => and_low_split kn b j2 (fst (lin_of a)) rts
                    | _ => mkAlu ALU_AND a b
                    end
                end
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
(* [comment removed for export] *)
Definition narrow_mask (kn : list kentry) (a : expr) (k' : Z) : option Z :=
  let i := ctz64 k' in
  let m := (k' + 2 ^ i)%Z in
  let j := Z.log2 m in
  if (Z.ltb 0 k' && Z.eqb m (2 ^ j) && Z.ltb j 64)%bool then
    match xhi kn a with
    | Some h => if Z.ltb h (2 ^ j) then Some (two64 - 2 ^ i)%Z else None
    | None => None
    end
  else None.

Definition mkAnd (kn : list kentry) (a b : expr) : expr :=
  match b with
  | ELit k =>
      match narrow_mask kn a (k mod two64)%Z with
      | Some m => mkAnd0 kn a (ELit m)
      | None => mkAnd0 kn a b
      end
  | _ => mkAnd0 kn a b
  end.

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
                      | Some x => Some (zext_fast sx lo n x) | None => None end   (* [comment removed for export] *)
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

(* [comment removed for export] *)
Fixpoint evalS_def (s e : expr) : bool :=
  if expr_eqb e s then true else
  match e with
  | ELit _ => true
  | EVar _ => false
  | EAlu _ a b | EAluw _ a b | EMd _ a b | EMdw _ a b => if evalS_def s a then evalS_def s b else false
  | EExt _ _ _ a => evalS_def s a
  | EBlob _ _ _ _ => false
  end.

Fixpoint conc_try (kn : list kentry) (e : expr) (cands : list expr) : option Z :=
  match cands with
  | [] => None
  | s :: rest =>
      if closedb s then conc_try kn e rest else
      if negb (evalS_def s e) then conc_try kn e rest else
      match erange kn s with
      | Some (lo, hi) =>
          if Z.leb (hi - lo) conc_limit then
            match evalS s (wrap64 lo) e with
            | Some v =>
                if (if Z.ltb hi lo then true
                     else if probeS s e v hi then probeS s e v (lo + (hi - lo) / 2)%Z else false) then
                  if all_eval_toS s e v lo (Z.to_nat (hi - lo + 1)) then Some v
                  else conc_try kn e rest
                else conc_try kn e rest
            | None => conc_try kn e rest
            end
          else conc_try kn e rest
      | None => conc_try kn e rest
      end
  end.




(* [comment removed for export] *)
Fixpoint csize_budget (e : expr) (b : nat) {struct e} : option nat :=
  match b with
  | O => None
  | S b' =>
      match e with
      | ELit _ | EVar _ | EBlob _ _ _ _ => Some b'
      | EAlu _ x y | EAluw _ x y | EMd _ x y | EMdw _ x y =>
          match csize_budget x b' with Some b'' => csize_budget y b'' | None => None end
      | EExt _ _ _ x => csize_budget x b'
      end
  end.
Definition CONC_SIZE : nat := 96.
Definition conc_small (e : expr) : bool := match csize_budget e CONC_SIZE with Some _ => true | None => false end.
Definition concretize (kn : list kentry) (e : expr) : option Z :=
  if closedb e then eval_closed e else
  match (match erange kn e with Some (lo, hi) => if Z.eqb lo hi then Some lo else None | None => None end) with
  | Some v => Some v                      (* [comment removed for export] *)
  | None => if conc_small e then conc_try kn e (nubE (subexprs e)) else None
  end.

(* [comment removed for export] *)
Definition foldK_ref (kn : list kentry) (e : expr) : expr :=
  match e with
  | ELit _ => e
  | _ => match erange kn e with
         | Some (lo, hi) => if Z.eqb lo hi then ELit lo
                            else match concretize kn e with Some v => ELit v | None => e end
         | None => match concretize kn e with Some v => ELit v | None => e end   (* [comment removed for export] *)
         end
  end.

(* [comment removed for export] *)
Definition concretize_nr (kn : list kentry) (e : expr) : option Z :=
  if closedb e then eval_closed e else if conc_small e then conc_try kn e (nubE (subexprs e)) else None.
Definition foldK (kn : list kentry) (e : expr) : expr :=
  match e with
  | ELit _ => e
  | _ => match erange kn e with
         | Some (lo, hi) => if Z.eqb lo hi then ELit lo
                            else match concretize_nr kn e with Some v => ELit v | None => e end
         | None => match concretize_nr kn e with Some v => ELit v | None => e end
         end
  end.
Lemma foldK_eq : forall kn e, foldK kn e = foldK_ref kn e.
Proof.
  intros kn e. unfold foldK, foldK_ref.
  destruct e; try reflexivity;
    (match goal with |- context [erange kn ?x] => destruct (erange kn x) as [[rlo rhi]|] eqn:Er end;
     [destruct (Z.eqb rlo rhi) eqn:Eq; [reflexivity|]|]; unfold concretize, concretize_nr; rewrite Er, ?Eq; reflexivity).
Qed.

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

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ltu_negwrap (kn : list kentry) (a b : expr) : option bool :=
  if (lin_negwrapR kn a && lin_negwrapR kn b)%bool then
    let la := lin_of a in let lb := lin_of b in
    if lin_test kn (fst lb - 1 - fst la)%Z (lsub_e (snd lb) (snd la)) (fun lo _ => Z.leb 0 lo) then Some true
    else if lin_test kn (fst la - fst lb)%Z (lsub_e (snd la) (snd lb)) (fun lo _ => Z.leb 0 lo) then Some false
    else None
  else None.

Definition lin_branch (kn : list kentry) (c : branch_cond) (a b : expr) : option bool :=
  let ltu := if lin_ge0 kn [(b, (-1)%Z)] [(a, 0%Z)] then Some true
             else if lin_ge0 kn [(a, 0%Z)] [(b, 0%Z)] then Some false
             else ltu_negwrap kn a b in        (* [comment removed for export] *)
  match c with
  | BC_LTU => ltu
  | BC_GEU => option_map negb ltu
  | BC_LT | BC_GE =>
      match erange kn a, erange kn b with
      | Some (_, ah), Some (_, bh) =>
          if (Z.ltb ah (2 ^ 63) && Z.ltb bh (2 ^ 63))%bool
          then match c with BC_LT => ltu | _ => option_map negb ltu end
          else None
      | _, _ => None
      end
  | BC_EQ | BC_NE =>
      (* [comment removed for export] *)
      if (lin_ge0 kn [(b, (-1)%Z)] [(a, 0%Z)] || lin_ge0 kn [(a, (-1)%Z)] [(b, 0%Z)])%bool
      then Some (match c with BC_EQ => false | _ => true end)
      else
      (* [comment removed for export] *)
      if (if lin_ge0 kn [(a, 0%Z)] [(b, 0%Z)] then lin_ge0 kn [(b, 0%Z)] [(a, 0%Z)] else false)
      then Some (match c with BC_EQ => true | _ => false end)
      else None
  end.

Definition decide_branch (kn : list kentry) (c : branch_cond) (a b : expr) : option bool :=
  match a, b with
  | ELit x, ELit y => Some (lit_branch c x y)
  | _, _ =>
      if expr_eqb a b then Some (cond_on_eq c)
      else match diff_branch c a b with
           | Some t => Some t
           | None =>
             match (match erange kn a, erange kn b with
                    | Some (al, ah), Some (bl, bh) => range_branch c al ah bl bh
                    | _, _ => None
                    end) with
             | Some t => Some t
             | None => lin_branch kn c a b      (* [comment removed for export] *)
             end
           end
  end.


(* [comment removed for export] *)
Definition mkSlt (kn : list kentry) (c : branch_cond) (op : aluop) (a b : expr) : expr :=
  match a, b with
  | ELit _, ELit _ => mkAlu op a b
  | _, _ => match decide_branch kn c a b with
            | Some true => ELit 1
            | Some false => ELit 0
            | None => mkAlu op a b
            end
  end.

Definition mkAluK0 (kn : list kentry) (op : aluop) (a b : expr) : expr :=
  match op with
  | ALU_SLTU => mkSlt kn BC_LTU ALU_SLTU a b
  | ALU_SLT => mkSlt kn BC_LT ALU_SLT a b
  | ALU_AND => match a, b with
               | ELit _, ELit _ => mkAnd kn a b
               | ELit _, _ => mkAndK kn b a      (* [comment removed for export] *)
               | _, _ => mkAndK kn a b
               end
  | ALU_OR => if expr_eqb a b then a else mkOr kn a b
  | ALU_XOR => if expr_eqb a b then ELit 0 else match is_lit a, b with
               | None, ELit k => if Z.eqb (k mod two64) (two64 - 1) then mkAlu ALU_SUB (ELit (two64 - 1)) a
                                else if Z.eqb (k mod two64) 0 then a    (* [comment removed for export] *)
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
Definition pow2_log (m : Z) : option Z :=
  let m' := (m mod two64)%Z in
  let k := Z.log2 m' in
  if (Z.ltb 0 m' && Z.eqb m' (2 ^ k) && Z.ltb k 64)%bool then Some k else None.

Definition mkMdK (kn : list kentry) (op : mulop) (a b : expr) : expr :=
  match is_lit a, op, b with
  | None, M_REMU, ELit m =>
      match pow2_log m with
      | Some k => mkAluK kn ALU_AND a (ELit (2 ^ k - 1))
      | None => mkMd op a b
      end
  | None, M_DIVU, ELit m =>
      match pow2_log m with
      | Some k => mkAluK kn ALU_SRL a (ELit k)
      | None => mkMd op a b
      end
  | _, _, _ => mkMd op a b
  end.

(* [comment removed for export] *)
Definition sx32_stable (lo hi : Z) : bool :=
  (Z.ltb hi (2 ^ 31) || Z.leb (two64 - 2 ^ 31) lo)%bool.

(* [comment removed for export] *)
Definition zband32 (kn : list kentry) (d : expr) : bool :=
  let l := lin_of d in
  match lin_range (erange kn) (fst l) (snd l) with
  | Some (lo, hi) => (Z.ltb (- 2 ^ 31) lo && Z.ltb hi (2 ^ 31))%bool
  | None => false
  end.

(* [comment removed for export] *)
Definition zband32k (kn : list kentry) (d : expr) : option Z :=
  let l := lin_of d in
  match lin_range (erange kn) (fst l) (snd l) with
  | Some (lo, hi) =>
      let k := ((lo + 2 ^ 31) / 2 ^ 32)%Z in
      if (Z.leb (k * 2 ^ 32 - 2 ^ 31) lo && Z.ltb hi (k * 2 ^ 32 + 2 ^ 31))%bool then Some k else None
  | None => None
  end.
Definition zband_fix (d : expr) (k : Z) : expr :=
  if Z.eqb k 0 then d else mkAlu ALU_ADD d (ELit (- (k * 2 ^ 32))%Z).

(* [comment removed for export] *)
Definition snorm32 (k : Z) : Z := let m := (k mod 2 ^ 32)%Z in if Z.leb (2 ^ 31) m then (m - 2 ^ 32)%Z else m.
Fixpoint lred32 (ts : list (Z * expr)) : list (Z * expr) :=
  match ts with
  | [] => []
  | (k, a) :: r => let k' := snorm32 k in if Z.eqb k' 0 then lred32 r else (k', a) :: lred32 r
  end.
Fixpoint terms_same (a b : list (Z * expr)) : bool :=
  match a, b with
  | [], [] => true
  | (k, _) :: a', (k', _) :: b' => (Z.eqb k k' && terms_same a' b')%bool
  | _, _ => false
  end.
Definition band_of (c : Z) (ts : list (Z * expr)) (r : option (Z * Z)) : option (expr * Z) :=
  match r with
  | Some (lo, hi) =>
      let k := ((lo + 2 ^ 31) / 2 ^ 32)%Z in
      if (Z.leb (k * 2 ^ 32 - 2 ^ 31) lo && Z.ltb hi (k * 2 ^ 32 + 2 ^ 31))%bool then Some (unlin (c, ts), k) else None
  | None => None
  end.
Definition wband32 (kn : list kentry) (d : expr) : option (expr * Z) :=
  let l := lin_of d in
  let ts := lred32 (snd l) in
  if terms_same ts (snd l) then None else            (* [comment removed for export] *)
  match band_of (fst l) ts (lin_range (erange kn) (fst l) ts) with
  | Some x => Some x
  | None => band_of (fst l) ts (match sum_facts kn kn with
                              | [] => None
                              | fs => lin_rel_multi (erange kn) fs (fst l) ts
                              end)
  end.

Definition mkAluwK0_lin (kn : list kentry) (op : aluop) (a b : expr) : expr :=
  let d := mkAlu op a b in
  match is_lit d with
  | Some v => ELit (zsx32 v)
  | None => match erange kn d with
            | Some (lo, hi) => if sx32_stable lo hi then d else
                               match zband32k kn d with Some k => zband_fix d k | None =>
                               match wband32 kn d with Some (r, k) => zband_fix r k | None => mkAluw op a b end end
            | None => match zband32k kn d with Some k => zband_fix d k | None =>
                      match wband32 kn d with Some (r, k) => zband_fix r k | None => mkAluw op a b end end
            end
  end.
Definition mkAluwK0 (kn : list kentry) (op : aluop) (a b : expr) : expr :=
  match op with
  | ALU_ADD | ALU_SUB => mkAluwK0_lin kn op a b
  | ALU_SLL =>   (* [comment removed for export] *)
      match b with
      | ELit s => if (Z.leb 0 s && Z.ltb s 32)%bool then mkAluwK0_lin kn op a b else mkAluw op a b
      | _ => mkAluw op a b
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
        let w := (2 ^ (8 * Z.of_nat n))%Z in
        (* [comment removed for export] *)
        let viaz :=
          if sx then
            match erange kn (EExt false 0 n e) with
            | Some (lo, hi) =>
                if (Z.leb 0 lo && Z.ltb hi (w / 2))%bool then EExt false 0 n e
                else if (Nat.leb 1 n && Z.leb (w / 2) lo && Z.ltb hi w)%bool
                     then mkAlu ALU_ADD (EExt false 0 n e) (ELit (two64 - w)%Z) else v
            | None => v
            end
          else v in
        match erange kn e with
        | Some (lo, hi) =>
            if Z.ltb hi (if sx then w / 2 else w) then e
            else (* [comment removed for export] *)
              if (sx && Nat.leb 1 n && Z.leb (w / 2) lo && Z.ltb hi w)%bool
              then mkAlu ALU_ADD e (ELit (two64 - w)%Z) else viaz
        | None => viaz
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
      if (Z.leb 0 (lo + a_off a) && Z.leb (hi + a_off a + Z.of_nat n) (2 ^ 64))%bool
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
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition amo_sz (wd : awidth) : msize := match wd with AW => SZ4 | AD => SZ8 end.
(* [comment removed for export] *)
Definition amo_sx (wd : awidth) : bool := match wd with AW => true | AD => false end.

(* [comment removed for export] *)
Definition amo_alignedb (kn : list kentry) (e : expr) (wd : awidth) : bool :=
  match lin_lowbits_kn kn e (match wd with AW => 2 | AD => 3 end) with
  | Some r => Z.eqb r 0
  | None => false
  end.

(* [comment removed for export] *)
Definition resv_inval (r : option saddr) (a : saddr) : option (option saddr) :=
  match r with
  | None => Some None
  | Some ra =>
      if saddr_eqb ra a then Some None
      else if (expr_eqb (a_base ra) (a_base a) && negb (Z.eqb ((a_off ra - a_off a) mod two64) 0))%bool
           then Some r
           else None
  end.

(* [comment removed for export] *)
Definition amo_aluop (op : amoop) : option (option aluop) :=
  match op with
  | AMO_SWAP => Some None
  | AMO_ADD => Some (Some ALU_ADD)
  | AMO_XOR => Some (Some ALU_XOR)
  | AMO_AND => Some (Some ALU_AND)
  | AMO_OR => Some (Some ALU_OR)
  | _ => None
  end.

(* [comment removed for export] *)
Definition amo_newval (kn : list kentry) (wd : awidth) (aop : option aluop) (old src : expr) : expr :=
  match aop with
  | None => src
  | Some o => match wd with AW => mkAluwK kn o old src | AD => mkAluK kn o old src end
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition ffmt_bytes (fmt : ffmt) : nat := match fmt with FMT_S => 4%nat | FMT_D => 8%nat end.

(* [comment removed for export] *)
Definition rm_okb (rm : bv 3) : bool := (Z.leb (bv_unsigned rm) 4 || Z.eqb (bv_unsigned rm) 7)%bool.

(* [comment removed for export] *)
Definition fcvt_is_f (t : fcvt_ty) : bool := match t with FC_S | FC_D => true | _ => false end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition xwrap (n : nat) (sx : bool) (e : expr) : expr :=
  if Nat.ltb n 8 then (if sx then EExt true 0 n (EExt false 0 n e) else EExt false 0 n e) else e.
Definition xunwrap (e : expr) : option nat :=
  match e with
  | EVar j => Some j
  | EExt _ _ _ (EVar j) => Some j
  | EExt _ _ _ (EExt _ _ _ (EVar j)) => Some j
  | _ => None
  end.

(* [comment removed for export] *)
Fixpoint split_read_lo (allkn : list kentry) (segs : list Segment) (kn : list kentry) (rb : expr) (rk : Z)
         (w1 : nat) : option (nat * expr) :=
  match w1 with
  | O => None
  | S w1' =>
      match know_lookupA0 allkn segs kn rb rk w1 false [] [] with
      | LHit v [] _ => Some (w1, v)
      | _ => split_read_lo allkn segs kn rb rk w1'
      end
  end.
Definition split_value (lo : expr) (w1 : nat) (hi : expr) : expr :=
  EAlu ALU_ADD lo (EMd M_MUL (ELit (2 ^ (8 * Z.of_nat w1))) hi).

Definition sym_read (segs : list Segment) (ss : sym_state) (fk : list kentry) (scr : scripts)
           (a : saddr) (n : nat) (sx' : bool)
  : option (expr * list sidecond * scripts * nat) :=
  match log_lookup fk (s_log ss) (a_base a) (a_off a) n sx' (sc_hints scr) [] with
  | LStuck => None
  | LHit v scs hints =>
      Some (extK fk v, flat_sc fk a n ++ scs, SCR (sc_dirs scr) (sc_reads scr) hints, s_next ss)
  | LMiss scs hints =>
      match know_lookupA fk segs (s_know ss) (a_base a) (a_off a) n sx' hints scs with
      | LStuck => None
      | LHit v scs' hints' =>
          Some (extK fk v, flat_sc fk a n ++ scs', SCR (sc_dirs scr) (sc_reads scr) hints', s_next ss)
      | LMiss scs' hints' =>
          (* [comment removed for export] *)
          let i := s_next ss in
          match sc_reads scr with
          | e :: reads' => Some (e, flat_sc fk a n ++ SCReadBase a n sx' e :: scs', SCR (sc_dirs scr) reads' hints', S i)
          | [] =>
              match (if sx' then None else split_read_lo fk segs (s_know ss) (a_base a) (a_off a) (Nat.pred n)) with
              | Some (w1, v1) =>
                  let a2 := SA (a_base a) (a_off a + Z.of_nat w1)%Z in
                  let n2 := (n - w1)%nat in
                  let rv2 := xwrap n2 false (EVar i) in
                  Some (split_value (extK fk v1) w1 rv2, flat_sc fk a n ++ SCReadBase a2 n2 false rv2 :: scs',
                        SCR (sc_dirs scr) [] hints', S i)
              | None =>
                  let rv := xwrap n sx' (EVar i) in
                  Some (rv, flat_sc fk a n ++ SCReadBase a n sx' rv :: scs', SCR (sc_dirs scr) [] hints', S i)
              end
          end
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
  | ShiftImm32 op rd rs sh => SOk (sset ss rd (mkAluwK fk op (g rs) (ELit (bv_unsigned sh))) (p + 4)) [] scr
  | Op32 op rd rs1 rs2 => SOk (sset ss rd (mkAluwK fk op (g rs1) (g rs2)) (p + 4)) [] scr
  | Mul op rd rs1 rs2 => SOk (sset ss rd (mkMdK fk op (g rs1) (g rs2)) (p + 4)) [] scr
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
      match sym_read segs ss fk scr a n sx' with
      | None => SStop
      | Some (v, scs, scr', nx') =>
          SOk (SSR (p + 4) (if bv_eqb rd 0 then s_regs ss else sr_upd (s_regs ss) (ridx rd) v)
                   (s_log ss) (s_know ss) nx' (s_resv ss)) scs scr'
      end
  | Store sz rs1 rs2 imm =>
      let n := msize_bytes sz in
      let a := to_saddrK fk (g rs1) (bv_signed imm) in
      match resv_inval (s_resv ss) a with
      | None => SStop
      | Some r' =>
          SOk (SSR (p + 4) (s_regs ss) (SE a n (g rs2) :: s_log ss) (s_know ss) (s_next ss) r')
              (flat_sc fk a n ++ storeok_sc fk a n) scr
      end
  (* [comment removed for export] *)
  | Lr wd _ _ rd rs =>
      let n := msize_bytes (amo_sz wd) in
      let e := g rs in
      if amo_alignedb fk e wd then
        let a := to_saddrK fk e 0 in
        match sym_read segs ss fk scr a n (amo_sx wd) with
        | None => SStop
        | Some (v, scs, scr', nx') =>
            SOk (SSR (p + 4) (if bv_eqb rd 0 then s_regs ss else sr_upd (s_regs ss) (ridx rd) v)
                     (s_log ss) (s_know ss) nx' (Some a)) scs scr'
        end
      else SStop
  | Sc wd _ _ rd rs1 rs2 =>
      let n := msize_bytes (amo_sz wd) in
      let e := g rs1 in
      if amo_alignedb fk e wd then
        let a := to_saddrK fk e 0 in
        match s_resv ss with
        | Some r =>
            if saddr_eqb r a then
              SOk (SSR (p + 4) (if bv_eqb rd 0 then s_regs ss else sr_upd (s_regs ss) (ridx rd) (ELit 0))
                       (SE a n (g rs2) :: s_log ss) (s_know ss) (s_next ss) None)
                  (flat_sc fk a n ++ storeok_sc fk a n) scr
            else SStop   (* [comment removed for export] *)
        | None => SStop
        end
      else SStop
  | Amo op wd _ _ rd rs1 rs2 =>
      match amo_aluop op with
      | None => SStop
      | Some aop =>
          let n := msize_bytes (amo_sz wd) in
          let e := g rs1 in
          if amo_alignedb fk e wd then
            let a := to_saddrK fk e 0 in
            match resv_inval (s_resv ss) a with
            | None => SStop
            | Some r' =>
                match sym_read segs ss fk scr a n (amo_sx wd) with
                | None => SStop
                | Some (vold, scs, scr', nx') =>
                    SOk (SSR (p + 4) (if bv_eqb rd 0 then s_regs ss else sr_upd (s_regs ss) (ridx rd) vold)
                             (SE a n (amo_newval fk wd aop vold (g rs2)) :: s_log ss) (s_know ss) nx' r')
                        (scs ++ storeok_sc fk a n) scr'
                end
            end
          else SStop
      end
  (* [comment removed for export] *)
  | FLoad fmt rd rs imm =>
      let n := ffmt_bytes fmt in
      let a := to_saddrK fk (g rs) (bv_signed imm) in
      match sym_read segs ss fk scr a n false with
      | None => SStop
      | Some (_, scs, scr', nx') =>
          SOk (SSR (p + 4) (s_regs ss) (s_log ss) (s_know ss) nx' (s_resv ss)) scs scr'
      end
  | Fmv FMV_F_X _ _ _ => SOk (sjump ss (p + 4)) [] scr
  | Fsgnj _ _ _ _ _ => SOk (sjump ss (p + 4)) [] scr
  | Fminmax _ _ _ _ _ => SOk (sjump ss (p + 4)) [] scr
  | Fari _ _ _ _ _ rm => if rm_okb rm then SOk (sjump ss (p + 4)) [] scr else SStop
  | Fsqrt _ _ _ rm => if rm_okb rm then SOk (sjump ss (p + 4)) [] scr else SStop
  | Fma _ _ _ _ _ _ rm => if rm_okb rm then SOk (sjump ss (p + 4)) [] scr else SStop
  | Fcvt dst src rd rs1 rm =>
      if (fcvt_is_f dst && rm_okb rm)%bool then SOk (sjump ss (p + 4)) [] scr else SStop
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


(* [comment removed for export] *)
Fixpoint sym_exec_go (fuel : nat) (first : bool) (stops : list Z) (scr : scripts)
                  (ss : sym_state) (acc : list sidecond)
                  (ck : sym_state * list sidecond * scripts)
  : sym_state * list sidecond * scripts :=
  match fuel with
  | O => if s_clean ss then (ss, acc, scr) else ck
  | S f =>
      if (negb first && existsb (Z.eqb (s_pc ss)) stops)%bool then (if s_clean ss then (ss, acc, scr) else ck) else
      match fetch_word segs (Z_to_bv 64 (s_pc ss)) with
      | None => if s_clean ss then (ss, acc, scr) else ck
      | Some w =>
          if is_ecall w then (if s_clean ss then (ss, acc, scr) else ck) else
          match decode_any w with
          | None => if s_clean ss then (ss, acc, scr) else ck
          | Some (i, sz) =>
              if negb (Z.eqb sz 4) then (if s_clean ss then (ss, acc, scr) else ck) else
              match sym_step segs i ss scr with
              | SOk ss' scs scr' =>
                  let acc' := sc_add scs acc in
                  sym_exec_go f false stops scr' ss' acc'
                    (if s_clean ss' then (ss', acc', scr') else ck)
              | SStop => if s_clean ss then (ss, acc, scr) else ck
              end
          end
      end
  end.

Definition sym_exec (fuel : nat) (first : bool) (stops : list Z) (scr : scripts)
           (ss : sym_state) (acc : list sidecond) : sym_state * list sidecond * scripts :=
  sym_exec_go fuel first stops scr (clr ss) acc (clr ss, acc, scr).

(* [comment removed for export] *)
Definition scr_nil : scripts := SCR [] [] [].





(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition zf_covers (allkn : list kentry) (rb : expr) (rk : Z) (n : nat) (kb : expr) (kk : Z) (len : expr) : bool :=
  (match len with
   | ELit l0 => match rel_lit rb rk (Z.of_nat n) kb kk (l0 mod 2 ^ 64)%Z with RInside _ => true | _ => false end
   | _ => false
   end) || xinside allkn rb rk (elen n) kb kk len.

(* [comment removed for export] *)
Definition kentry_overlay (allkn : list kentry) (rb : expr) (rk : Z) (n : nat) (K : kentry) : bool :=
  match K with
  | KUnk (SA kb kk) len | KZero (SA kb kk) len | KFill (SA kb kk) len _ | KBlob (SA kb kk) len _ =>
      zf_covers allkn rb rk n kb kk len
  | _ => false
  end.

(* [comment removed for export] *)
Definition kentry_readable (allkn : list kentry) (rb : expr) (rk : Z) (n : nat) (K : kentry) : bool :=
  match K with
  | KWord (SA kb kk) w _ =>
      match rel_lit rb rk (Z.of_nat n) kb kk (Z.of_nat w) with RInside _ => true | _ => false end
  | _ => kentry_overlay allkn rb rk n K
  end.

(* [comment removed for export] *)
Fixpoint know_byte_cov (img : bool) (kn : list kentry) (rb : expr) (rk : Z) : bool :=
  match kn with
  | [] => false
  | K :: rest =>
      let lit kb kk (l : Z) := match rel_lit rb rk 1 kb kk l with RInside _ => true | _ => false end in
      (match K with
       | KWord (SA kb kk) w _ => img && lit kb kk (Z.of_nat w)
       | KZero (SA kb kk) (ELit l0) | KFill (SA kb kk) (ELit l0) _ | KBlob (SA kb kk) (ELit l0) _
       | KUnk (SA kb kk) (ELit l0) => lit kb kk (l0 mod 2 ^ 64)%Z
       | KImg lo hi =>
           img && match rb with
                  | ELit 0 => Z.leb lo rk && Z.ltb rk hi &&
                              match seg_rom segs (Z_to_bv 64 rk) with Some _ => true | None => false end
                  | _ => false
                  end
       | _ => false
       end) || know_byte_cov img rest rb rk
  end%bool.

Fixpoint know_bytes_cov (img : bool) (kn : list kentry) (rb : expr) (rk : Z) (n : nat) : bool :=
  match n with
  | O => true
  | S n' => know_byte_cov img kn rb rk && know_bytes_cov img kn rb (rk + 1) n'
  end.

Definition kn_readable (allkn kn : list kentry) (rb : expr) (rk : Z) (n : nat) : bool :=
  existsb (kentry_readable allkn rb rk n) kn || know_bytes_cov true kn rb rk n.
Definition kn_overlay (allkn kn : list kentry) (rb : expr) (rk : Z) (n : nat) : bool :=
  existsb (kentry_overlay allkn rb rk n) kn || know_bytes_cov false kn rb rk n.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition probe_app_lin (fk : list kentry) (rb : expr) (rk : Z) : option expr :=
  match xlo fk rb, xhi fk rb with
  | Some lo, Some hi =>
      if (Z.leb SB (lo + rk) && Z.ltb (hi + rk - SB) (2 ^ 61))%bool
      then Some (mkMd M_MUL (ELit 8) (mkAlu ALU_ADD rb (ELit (rk - SB)%Z))) else None
  | _, _ => None
  end.
Definition probe_app (fk : list kentry) (rb : expr) (rk : Z) : option expr :=
  match rb with
  | EAlu ALU_SRL e (ELit 3%Z) =>
      let c := (rk - SB)%Z in
      if Z.eqb c 0 then Some e
      else if (Z.leb 0 c && match xhi fk e with Some h => Z.ltb (h + 8 * c) two64 | None => false end)%bool
           then Some (mkAlu ALU_ADD e (ELit (8 * c))) else probe_app_lin fk rb rk   (* [comment removed for export] *)
  | _ => probe_app_lin fk rb rk
  end.

Inductive pres : Type := PZero | PPart (q : expr) (d : option Z).

(* [comment removed for export] *)
Definition ge_x (kn : list kentry) (a : expr) (ka : Z) (b : expr) (kb : Z) : bool :=
  lin_ge0 kn [(a, ka)] [(b, kb)]
  || match xrange2 kn a, xrange2 kn b with Some (l, _), Some (_, h) => Z.leb (h + kb) (l + ka) | _, _ => false end.

(* [comment removed for export] *)
Definition kshok_probe1 (fk : list kentry) (y : expr) (K : kentry) : option pres :=
  match K with
  | KShOk (SA ob oo) len =>
      let obase := mkAlu ALU_ADD ob (ELit oo) in
      let oend := mkAlu ALU_ADD obase len in
      let ry := lowbits fk y 3 in
      (* [comment removed for export] *)
      if negb (ge_x fk y 0%Z obase 0%Z) then None else
      (* [comment removed for export] *)
      let startok := match lowbits fk obase 3, ry with
                     | Some 0%Z, _ => true
                     | _, Some r => ge_x fk y (- r)%Z obase 0%Z
                     | _, None => false
                     end in
      (* [comment removed for export] *)
      if (ge_x fk oend 0%Z y 8%Z        (* [comment removed for export] *)
          || (startok &&
              (match ry with Some r => ge_x fk oend 0%Z y (8 - r)%Z | None => false end
               || match lowbits fk oend 3 with Some 0%Z => ge_x fk oend 0%Z y 1%Z | _ => false end)))%bool
      then Some PZero
      else if ge_x fk oend 0%Z y 1%Z then      (* [comment removed for export] *)
        let d := mkAluK fk ALU_SUB oend y in
        if startok then Some (PPart (mkAluK fk ALU_ADD d (mkAluK fk ALU_AND y (ELit 7))) (xlo fk d))
        else (* [comment removed for export] *)
          match xlo fk d with
          | Some lo => if Z.leb 1 lo then Some (PPart (mkAluK fk ALU_ADD (mkAluK fk ALU_AND y (ELit 7)) (ELit (Z.min lo 8))) None) else None
          | None => None
          end
      else None
  | _ => None
  end.

Fixpoint kshok_probe (fk kn : list kentry) (y : expr) : option pres :=
  match kn with
  | [] => None
  | K :: rest => match kshok_probe1 fk y K with Some r => Some r | None => kshok_probe fk rest y end
  end.

(* [comment removed for export] *)
Definition probe_mark (i : nat) (n : expr) : kentry :=
  KDisj (SA (EVar i) 0%Z) (ELit 0%Z) (SA (ELit 0%Z) 0%Z) n.

(* [comment removed for export] *)
Definition probe_facts (fk : list kentry) (i : nat) (y q : expr) (d : option Z) : list kentry :=
  KRange (EVar i) 0 7
  :: probe_mark i q
  :: match d with
     | Some lo => if Z.leb 1 lo then [probe_mark i (mkAluK fk ALU_ADD (mkAluK fk ALU_AND y (ELit 7)) (ELit (Z.min lo 8)))] else []
     | None => []
     end.

(* [comment removed for export] *)
Fixpoint has_probe_mark (kn : list kentry) (i : nat) : bool :=
  match kn with
  | [] => false
  | KDisj (SA (EVar j) 0%Z) (ELit 0%Z) (SA (ELit 0%Z) 0%Z) _ :: rest => if Nat.eqb i j then true else has_probe_mark rest i
  | _ :: rest => has_probe_mark rest i
  end.

(* [comment removed for export] *)
Fixpoint evars_lt (b : nat) (e : expr) : bool :=
  match e with
  | ELit _ | EBlob _ _ _ _ => true
  | EVar v => Nat.ltb v b
  | EAlu _ x y | EAluw _ x y | EMd _ x y | EMdw _ x y => evars_lt b x && evars_lt b y
  | EExt _ _ _ x => evars_lt b x
  end.

(* [comment removed for export] *)
Fixpoint find_readbase (i : nat) (scs : list sidecond) : option (saddr * nat * bool) :=
  match scs with
  | [] => None
  | SCReadBase a n sx rv :: rest =>
      match xunwrap rv with
      | Some j => if Nat.eqb j i then Some (a, n, sx) else find_readbase i rest
      | None => find_readbase i rest
      end
  | _ :: rest => find_readbase i rest
  end.

(* [comment removed for export] *)
Definition x_dischargeable (ss ss' : sym_state) (rb : option (saddr * nat * bool)) (sc : sidecond) : bool :=
  let kn := s_know ss in
  let fk := facts_of kn in
  match sc with
  | SCReadBase a n sx rv =>
      match xunwrap rv with
      | Some j =>
      (match rb with
       | Some (a', n', sx') => saddr_eqb a' a && Nat.eqb n' n && Bool.eqb sx' sx
       | None => false
       end)
      && Nat.eqb j (s_next ss) && Nat.ltb j (s_next ss') && evars_lt (s_next ss) (a_base a)
      && Nat.leb 1 n && Nat.leb n 8 && kn_readable fk kn (a_base a) (a_off a) n && expr_eqb rv (xwrap n sx (EVar j))
      | None => false
      end
  | SCFlat a (ELit z) =>
      Z.leb 1 z && Z.leb z 8 && kn_readable fk kn (a_base a) (a_off a) (Z.to_nat z)
  | SCStoreOk a n => Nat.leb 1 n && Nat.leb n 8 && kn_overlay fk kn (a_base a) (a_off a) n
  | _ => false
  end%bool.

Definition x_filter (ss ss' : sym_state) (scs : list sidecond) : list sidecond :=
  match scs with
  | [] => []          (* [comment removed for export] *)
  | _ => let rb := find_readbase (s_next ss) scs in
         List.filter (fun sc => negb (x_dischargeable ss ss' rb sc)) scs
  end.

(* [comment removed for export] *)
Fixpoint esize_budget (e : expr) (b : nat) {struct e} : option nat :=
  match b with
  | O => None
  | S b' =>
      match e with
      | ELit _ | EVar _ | EBlob _ _ _ _ => Some b'
      | EAlu _ x y | EAluw _ x y | EMd _ x y | EMdw _ x y =>
          match esize_budget x b' with Some b'' => esize_budget y b'' | None => None end
      | EExt _ _ _ x => esize_budget x b'
      end
  end.
Definition esize_le (e : expr) (k : nat) : bool :=
  match esize_budget e k with Some _ => true | None => false end.

(* [comment removed for export] *)
Definition rd_of (i : instr) : option reg :=
  match i with
  | Lui rd _ | Auipc rd _ | Jal rd _ | Jalr rd _ _ | Load _ _ rd _ _
  | OpImm _ rd _ _ | ShiftImm _ rd _ _ | Op _ rd _ _ | OpImm32 rd _ _ | ShiftImm32 _ rd _ _ | Op32 _ rd _ _
  | Mul _ rd _ _ | Mul32 _ rd _ _ | Lr _ _ _ rd _ | Sc _ _ _ rd _ _ | Amo _ _ _ _ rd _ _ => Some rd
  | _ => None
  end.

(* [comment removed for export] *)
Definition cap_rd (K : nat) (i : instr) (ss : sym_state) : sym_state :=
  match K with
  | O => ss
  | _ =>
      match rd_of i with
      | None => ss
      | Some rd =>
          if bv_eqb rd 0 then ss
          else if esize_le (sr_get (s_regs ss) rd) K then ss
          else SSR (s_pc ss) (sr_upd (s_regs ss) (ridx rd) (EVar (s_next ss)))
                   (s_log ss) (s_know ss) (S (s_next ss)) (s_resv ss)
      end
  end.

(* [comment removed for export] *)
Definition xfp_step (kn : list kentry) (i : instr) (ss : sym_state) (scr : scripts) : option stepres :=
  let p := s_pc ss in
  let i0 := s_next ss in
  let xdef (rd : reg) :=
    SOk (SSR (p + 4) (if bv_eqb rd 0 then s_regs ss else sr_upd (s_regs ss) (ridx rd) (EVar i0))
             (s_log ss) (s_know ss) (S i0) (s_resv ss)) [] scr in
  match i with
  | FStore fmt rs1 rs2 imm =>
      let fk := facts_of kn in
      let n := ffmt_bytes fmt in
      let a := to_saddrK fk (sr_get (s_regs ss) rs1) (bv_signed imm) in
      Some match resv_inval (s_resv ss) a with
           | None => SStop
           | Some r' =>
               let ss' := SSR (p + 4) (s_regs ss) (SE a n (EVar i0) :: s_log ss) (s_know ss) (S i0) r' in
               SOk ss' (x_filter ss ss' (flat_sc fk a n ++ storeok_sc fk a n)) scr
           end
  | Fmv FMV_X_F FMT_D rd _ =>   (* [comment removed for export] *)
      Some (SOk (SSR (p + 4) (if bv_eqb rd 0 then s_regs ss
                                else sr_upd (s_regs ss) (ridx rd) (EExt false 0 8 (EVar i0)))
                    (s_log ss) (s_know ss) (S i0) (s_resv ss)) [] scr)
  | Fmv FMV_X_F FMT_S rd _ =>   (* [comment removed for export] *)
      Some (SOk (SSR (p + 4) (if bv_eqb rd 0 then s_regs ss
                                else sr_upd (s_regs ss) (ridx rd) (EExt true 0 4 (EExt false 0 4 (EVar i0))))
                    (s_log ss) (s_know ss) (S i0) (s_resv ss)) [] scr)
  | Fcmp _ _ rd _ _ => Some (xdef rd)
  | Fclass _ rd _ => Some (xdef rd)
  | Fcvt dst src rd rs1 rm =>
      if fcvt_is_f dst then None
      else Some (if (fcvt_is_f src && rm_okb rm)%bool then xdef rd else SStop)
  | _ => None
  end.

(* [comment removed for export] *)
Definition probe_step (i : instr) (ss : sym_state) : option (sym_state * bool) :=
  match i with
  | Load SZ1 sx rd rs imm =>
      let kn := s_know ss in let fk := facts_of kn in
      let a := to_saddrK fk (sr_get (s_regs ss) rs) (bv_signed imm) in
      match probe_app fk (a_base a) (a_off a) with
      | None => None
      | Some y =>
          match log_lookup fk (s_log ss) (a_base a) (a_off a) 1 sx [] [] with
          | LMiss [] _ =>
              match kshok_probe fk kn y with
              | Some PZero => Some (sset ss rd (ELit 0) (s_pc ss + 4), false)
              | Some (PPart q d) =>
                  let i0 := s_next ss in
                  Some (SSR (s_pc ss + 4)
                            (if bv_eqb rd 0 then s_regs ss else sr_upd (s_regs ss) (ridx rd) (EVar i0))
                            (s_log ss) (probe_facts fk i0 y q d ++ kn) (S i0) (s_resv ss), true)
              | None => None
              end
          | _ => None
          end
      end
  | _ => None
  end.

(* [comment removed for export] *)
Definition sym_stepX0 (K : nat) (i : instr) (ss : sym_state) (scr : scripts) : stepres :=
  match xfp_step (s_know ss) i ss scr with
  | Some r => r
  | None =>
  match sym_step segs i ss scr with
  | SOk ss' scs scr' =>
      if Nat.leb (s_next ss) (s_next ss')            (* [comment removed for export] *)
      then SOk (cap_rd K i ss') (x_filter ss ss' scs) scr'
      else SStop
  | SStop => SStop
  end
  end.

Definition sym_stepX (K : nat) (i : instr) (ss : sym_state) (scr : scripts) : stepres :=
  match probe_step i ss with
  | Some (ss', _) => SOk ss' [] scr
  | None => sym_stepX0 K i ss scr
  end.



(* [comment removed for export] *)
Definition PROBE_FUEL : nat := 12.

Fixpoint regs_join (n : nat) (rm rs : list expr) (nx : nat) : list expr * nat :=
  match n with
  | O => ([], nx)
  | S n' =>
      let x := hd (ELit 0%Z) rm in
      if expr_eqb x (hd (ELit 0%Z) rs)
      then let '(r, nx') := regs_join n' (tl rm) (tl rs) nx in (x :: r, nx')
      else let '(r, nx') := regs_join n' (tl rm) (tl rs) (S nx) in (EVar nx :: r, nx')
  end.

Definition side_instr_ok (i : instr) : bool :=
  match i with
  | Store _ _ _ _ | FStore _ _ _ _ | Sc _ _ _ _ _ _ | Amo _ _ _ _ _ _ _ | Lr _ _ _ _ _
  | Ecall | Ebreak | Csr _ _ _ _ | CsrI _ _ _ _ => false
  | _ => true
  end.

Fixpoint side_run (t : itab) (K : nat) (fuel : nat) (z0 : Z) (ss : sym_state) : option sym_state :=
  if Z.eqb (s_pc ss) z0 then Some ss else
  match fuel with
  | O => None
  | S f =>
      match itab_lookup t (s_pc ss) with
      | None => None
      | Some i =>
          if negb (side_instr_ok i) then None else
          match probe_step i ss with
          | Some _ => None
          | None =>
            match sym_stepX0 K i ss scr_nil with
            | SOk ss' [] _ =>
                if (Nat.eqb (length (s_log ss')) (length (s_log ss)) && s_clean ss')%bool
                then side_run t K f z0 ss' else None
            | _ => None
            end
          end
      end
  end.

(* [comment removed for export] *)
Definition probe_branch (fk kn : list kentry) (i : instr) (ss : sym_state) : option (nat * Z * Z) :=
  match i with
  | Branch c rs1 rs2 imm =>
      let p := s_pc ss in
      let tk := bv_unsigned (Z_to_bv 64 (p + bv_signed imm)) in
      let pick (a b : expr) := match a, b with
                               | EVar j, ELit 0%Z => if has_probe_mark kn j then Some j else None
                               | _, _ => None
                               end in
      let a := conc_expr fk (sr_get (s_regs ss) rs1) in
      let b := conc_expr fk (sr_get (s_regs ss) rs2) in
      match (match pick a b with Some j => Some j | None => pick b a end) with
      | None => None
      | Some j =>
          match c with
          | BC_EQ => Some (j, tk, (p + 4)%Z)          (* [comment removed for export] *)
          | BC_NE => Some (j, (p + 4)%Z, tk)          (* [comment removed for export] *)
          | _ => None
          end
      end
  | _ => None
  end.

Definition probe_diamond (t : itab) (K : nat) (i : instr) (ss : sym_state) : option sym_state :=
  if negb (s_clean ss) then None else
  let kn := s_know ss in let fk := facts_of kn in
  match probe_branch fk kn i ss with
  | None => None
  | Some (j, z0, n0) =>
      let hj := match xhi fk (EVar j) with Some h => h | None => two64m1 end in
      let ss_nz := SSR n0 (s_regs ss) (s_log ss) (KRange (EVar j) 1 hj :: kn) (s_next ss) (s_resv ss) in
      match side_run t K PROBE_FUEL z0 ss_nz with
      | None => None
      | Some sd =>
          let '(rj, nx') := regs_join 32 (s_regs ss) (s_regs sd) (Nat.max (s_next ss) (s_next sd)) in
          Some (SSR z0 rj (s_log ss) kn nx' (s_resv ss))
      end
  end.

Fixpoint sym_execTX_go (t : itab) (K : nat) (fuel : nat) (first : bool) (stops : list Z) (ss : sym_state) (ck : sym_state)
  : sym_state :=
  match fuel with
  | O => if s_clean ss then ss else ck
  | S f =>
      if (negb first && existsb (Z.eqb (s_pc ss)) stops)%bool then (if s_clean ss then ss else ck) else
      match itab_lookup t (s_pc ss) with
      | None => if s_clean ss then ss else ck
      | Some i =>
          match sym_stepX K i ss scr_nil with
          | SOk ss' [] _ => sym_execTX_go t K f false stops ss' (if s_clean ss' then ss' else ck)
          | _ => (* [comment removed for export] *)
              match probe_diamond t K i ss with
              | Some ssj => sym_execTX_go t K f false stops ssj (if s_clean ssj then ssj else ck)
              | None => if s_clean ss then ss else ck
              end
          end
      end
  end.

Definition sym_execTX (t : itab) (K : nat) (fuel : nat) (first : bool) (stops : list Z) (ss : sym_state) : sym_state :=
  sym_execTX_go t K fuel first stops (clr ss) (clr ss).



End WithSegs.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition kcut (mk : saddr -> expr -> kentry) (kn : list kentry) (wb : expr) (wk : Z) (wn : expr)
           (kb : expr) (kk : Z) (len : expr) : list kentry :=
  let ws := mkAlu ALU_ADD wb (ELit wk) in
  let ks := mkAlu ALU_ADD kb (ELit kk) in
  (* [comment removed for export] *)
  let low :=
    if (if lin_ge0 kn [(kb, kk)] [(wb, wk)] then false   (* [comment removed for export] *)
        else if lin_ge0 kn [(wb, wk)] [(kb, kk)] then lin_ge0 kn [(kb, kk); (len, 0%Z)] [(wb, wk)] else false)
    then [mk (SA kb kk) (mkAlu ALU_SUB ws ks)] else [] in
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
         [mk ha (mkAlu ALU_SUB (mkAlu ALU_ADD ks len) we)]
    else [] in
  low ++ high.

Definition kzero_cut (kn : list kentry) (wb : expr) (wk : Z) (wn : expr)
           (kb : expr) (kk : Z) (len : expr) : list kentry := kcut KZero kn wb wk wn kb kk len.
Definition kfill_cut (c : Z) (kn : list kentry) (wb : expr) (wk : Z) (wn : expr)
           (kb : expr) (kk : Z) (len : expr) : list kentry := kcut (fun a n => KFill a n c) kn wb wk wn kb kk len.
Definition kunk_cut (kn : list kentry) (wb : expr) (wk : Z) (wn : expr)
           (kb : expr) (kk : Z) (len : expr) : list kentry := kcut KUnk kn wb wk wn kb kk len.

(* [comment removed for export] *)
Definition ktrim (mk : saddr -> expr -> kentry) (kb : expr) (kk : Z) (l0 : Z) (k : Z) (w : nat) : list kentry :=
  let l := (l0 mod 2 ^ 64)%Z in
  let hi1 := Z.min k (kk + l) in
  let r1 := if Z.ltb kk hi1 then [mk (SA kb kk) (ELit (hi1 - kk))] else [] in
  let lo2 := Z.max kk (k + Z.of_nat w) in
  let r2 := if Z.ltb lo2 (kk + l) then [mk (SA kb lo2) (ELit (kk + l - lo2))] else [] in
  r1 ++ r2.

(* [comment removed for export] *)
Definition kword_cut (kb : expr) (kk : Z) (w' : nat) (v : expr) (k : Z) (w : nat) : list kentry :=
  match v with
  | ELit _ =>
      let n1 := (k - kk)%Z in                                (* [comment removed for export] *)
      let r1 := if Z.ltb 0 n1 then [KWord (SA kb kk) (Z.to_nat n1) (mkExt false 0 (Z.to_nat n1) v)] else [] in
      let d := (k + Z.of_nat w - kk)%Z in                    (* [comment removed for export] *)
      let r2 := if Z.ltb d (Z.of_nat w')
                then [KWord (SA kb (kk + d)) (w' - Z.to_nat d) (mkExt false (Z.to_nat d) (w' - Z.to_nat d) v)]
                else [] in
      r1 ++ r2
  | _ => []
  end.

(* [comment removed for export] *)
Definition prune_zf (mk : saddr -> expr -> kentry) (allkn : list kentry) (wb : expr) (k : Z) (w : nat)
           (K : kentry) (kb : expr) (kk : Z) (len : expr) (apart : unit -> bool) (hints : list bool)
           (diffbase : unit -> list kentry * list sidecond * list bool)
  : list kentry * list sidecond * list bool :=
  (* [comment removed for export] *)
  if expr_eqb kb wb then
    match len with
    | ELit l0 => (ktrim mk kb kk l0 k w, [], hints)
    | _ => if Z.leb (k + Z.of_nat w) kk then ([K], [], hints)
           else (kcut mk allkn wb k (elen w) kb kk len, [], hints)
    end
  else if apart tt then ([K], [], hints)
  else match kcut mk allkn wb k (elen w) kb kk len with
       | [] => diffbase tt
       | cut => (cut, [], hints)
       end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition shb44 : Z := 2 ^ 44.
Definition app47 : Z := 2 ^ 47.
(* [comment removed for export] *)
Definition shok_apart (allkn : list kentry) (wb : expr) (wk : Z) (wn : expr) (kb : expr) (kk : Z) (len : expr) : bool :=
  match base_range allkn wb, xhi allkn wn, base_range allkn kb, xhi allkn len with
  | Some (wlo, whi), Some nh, Some (olo, ohi), Some lh =>
      (* [comment removed for export] *)
      if (Z.leb 0 (olo + kk)
          && (Z.leb (ohi + kk + lh) app47
              || match end_hi allkn kb kk len olo ohi lh with Some e => Z.leb e app47 | None => false end)   (* [comment removed for export] *)
          && ranges_apart_x allkn wb wk wn (ELit 0) SB (ELit shb44))%bool then true
      else if (Z.ltb (whi + wk + nh - 1) (SB + (olo + kk) / 8) || Z.ltb (SB + (ohi + kk + lh - 1) / 8) (wlo + wk))%bool then true
      else if match end_hi allkn kb kk len olo ohi lh with
              | Some e => Z.ltb (SB + (e - 1) / 8) (wlo + wk)
              | None => false
              end then true
      else (* [comment removed for export] *)
           match wb with
           | EAlu ALU_SRL xb (ELit c3) =>
               (Z.eqb c3 3 && Z.leb 3 (ealign allkn xb) && Z.leb SB wk && Z.leb 0 nh && Z.leb nh 8
                && ranges_apart_x allkn xb (8 * (wk - SB)) (ELit (8 * nh)) kb kk len)%bool
           | _ => false
           end
  | _, _, _, _ => false
  end.

(* [comment removed for export] *)
Definition kfpc_apart (allkn : list kentry) (wb : expr) (wk : Z) (wn : expr) (v lo : expr) : bool :=   (* [comment removed for export] *)
  lin_ge0 allkn [(v, (-16)%Z)] [(wb, wk); (wn, 0%Z)] || lin_ge0 allkn [(lo, 0%Z)] [(wb, wk); (wn, 0%Z)] || lin_ge0 allkn [(lo, 0%Z)] [(v, 0%Z)].

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
      prune_zf KZero allkn (a_base wa) k w K kb kk len
               (fun _ => ranges_apart_x allkn (a_base wa) k (elen w) kb kk len) hints (fun _ => diffbase (SA kb kk) len)
  | KFill (SA kb kk) len c =>
      prune_zf (fun a n => KFill a n c) allkn (a_base wa) k w K kb kk len
               (fun _ => ranges_apart_x allkn (a_base wa) k (elen w) kb kk len) hints (fun _ => diffbase (SA kb kk) len)
  | KUnk (SA kb kk) len => ([K], [], hints)     (* [comment removed for export] *)
  | KShOk (SA kb kk) len =>                    (* [comment removed for export] *)
      if shok_apart allkn (a_base wa) k (elen w) kb kk len then ([K], [], hints) else ([], [], hints)
  | KFpc v lo _ =>                             (* [comment removed for export] *)
      if kfpc_apart allkn (a_base wa) k (elen w) v lo then ([K], [], hints) else ([], [], hints)
  | KWord (SA kb kk) w' v =>
      if expr_eqb kb (a_base wa) then
        (if (Z.leb (kk + Z.of_nat w') k || Z.leb (k + Z.of_nat w) kk)%bool
         then ([K], [], hints) else (kword_cut kb kk w' v k w, [], hints))   (* [comment removed for export] *)
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
      prune_zf KZero allkn (a_base wa) k w K kb kk len
               (fun _ => ranges_apart_p allkn sp (a_base wa) k (elen w) kb kk len) hints (fun _ => diffbase (SA kb kk) len)
  | KFill (SA kb kk) len c =>
      prune_zf (fun a n => KFill a n c) allkn (a_base wa) k w K kb kk len
               (fun _ => ranges_apart_p allkn sp (a_base wa) k (elen w) kb kk len) hints (fun _ => diffbase (SA kb kk) len)
  | KUnk (SA kb kk) len => ([K], [], hints)     (* [comment removed for export] *)
  | KShOk (SA kb kk) len =>                    (* [comment removed for export] *)
      if shok_apart allkn (a_base wa) k (elen w) kb kk len then ([K], [], hints) else ([], [], hints)
  | KFpc v lo _ =>                             (* [comment removed for export] *)
      if kfpc_apart allkn (a_base wa) k (elen w) v lo then ([K], [], hints) else ([], [], hints)
  | KWord (SA kb kk) w' v =>
      if expr_eqb kb (a_base wa) then
        (if (Z.leb (kk + Z.of_nat w') k || Z.leb (k + Z.of_nat w) kk)%bool
         then ([K], [], hints) else (kword_cut kb kk w' v k w, [], hints))   (* [comment removed for export] *)
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
      else if lin_apart kn b1 k1 m1 b2 k2 m2 then true
      else if itv_apartX kn b1 k1 m1 b2 k2 m2 then true
      else if (Z.leb 0 m1 && Z.ltb m1 two64 && lin_ge0 kn [(b2, k2)] [(b1, k1); (ELit m1, 0%Z)])%bool then true   (* [comment removed for export] *)
      else (Z.leb 0 m2 && Z.ltb m2 two64 && lin_ge0 kn [(b1, k1)] [(b2, k2); (ELit m2, 0%Z)])%bool
  | _, _ =>
    if (match sp_rng sp, br2, sp_h1 sp, xhi kn n2 with
        | Some (lo1, hi1), Some (lo2, hi2), Some h1, Some h2 =>
            if (Z.leb (hi1 + k1 + h1) (lo2 + k2) || Z.leb (hi2 + k2 + h2) (lo1 + k1))%bool then true
            else (* [comment removed for export] *)
            if match end_hi kn b1 k1 n1 lo1 hi1 h1 with Some e1 => Z.leb e1 (lo2 + k2) | None => false end then true
            else match end_hi kn b2 k2 n2 lo2 hi2 h2 with Some e2 => Z.leb e2 (lo1 + k1) | None => false end
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
  | KZero (SA kb _) _ | KWord (SA kb _) _ _ | KBlob (SA kb _) _ _ | KFill (SA kb _) _ _ | KUnk (SA kb _) _ => Some kb
  | _ => None   (* [comment removed for export] *)
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
  | KFill (SA kb kk) len c =>
      if expr_eqb kb (a_base wa) then prune1p allkn sp wa w wv K hints
      else if ranges_apart_pc allkn sp (a_base wa) k (elen w) br2 kb kk len then ([K], [], hints)
      else match kfill_cut c allkn (a_base wa) k (elen w) kb kk len with
           | [] => diffbase (SA kb kk) len
           | cut => (cut, [], hints)
           end
  | KUnk (SA kb kk) len => ([K], [], hints)     (* [comment removed for export] *)
  | KShOk (SA kb kk) len =>                    (* [comment removed for export] *)
      if shok_apart allkn (a_base wa) k (elen w) kb kk len then ([K], [], hints) else ([], [], hints)
  | KFpc v lo _ =>                             (* [comment removed for export] *)
      if kfpc_apart allkn (a_base wa) k (elen w) v lo then ([K], [], hints) else ([], [], hints)
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
Fixpoint carry (log : list sentry) (kn : list kentry) (hints : list bool)
  : list kentry * list sidecond * list bool :=
  match log with
  | [] => (kn, [], hints)
  | SE a w v :: older =>
      let '(kn1, scs1, hs1) := carry older kn hints in
      let fk := facts_of kn1 in
      let '(kn2, scs2, hs2) := prunepc fk (mk_sprep fk (a_base a) (a_off a) (elen w)) a w v kn1 hs1 [] in   (* [comment removed for export] *)
      (KWord a w v :: kn2, scs1 ++ scs2, hs2)
  end.




End AX2.
