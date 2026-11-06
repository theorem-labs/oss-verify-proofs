(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import PropExec CatExec CatSim SeqExec StoreOk SymExec.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import AxSymExec3 CxfLeaf CxfNat.
Import ListNotations.
Open Scope bv_scope.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module AX2L.
Import AX2.
Notation "x && y" := (if x then y else false) (at level 40, left associativity) : bool_scope.
Notation "x || y" := (if x then true else y) (at level 50, left associativity) : bool_scope.
Definition ext_Z (sx : bool) (lo n : nat) (z : Z) : Z :=
  let u := ((z / 2 ^ (8 * Z.of_nat lo)) mod 2 ^ (8 * Z.of_nat n))%Z in
  if sx then bv_swrap (8 * N.of_nat n) u else u.
Lemma L_AX2L_ext_Z : @ext_Z = @AX2.ext_Z.
Proof. unfold ext_Z. reflexivity. Qed.

Definition ext_val (sx : bool) (lo n : nat) (v : word) : word :=
  Z_to_bv 64 (ext_Z sx lo n (bv_unsigned v)).
Lemma L_AX2L_ext_val : @ext_val = @AX2.ext_val.
Proof. unfold ext_val. rewrite ?L_AX2L_ext_Z. reflexivity. Qed.

Definition blob_bytes (bs : list byte) (i : Z) (n : nat) : list byte :=
  firstn n (skipn (Z.to_nat i) bs).
Lemma L_AX2L_blob_bytes : @blob_bytes = @AX2.blob_bytes.
Proof. unfold blob_bytes. reflexivity. Qed.

Definition blob_val (sx : bool) (bs : list byte) (i : Z) (n : nat) : word :=
  Z_to_bv 64 (let u := bytes_le_to_Z (blob_bytes bs i n) in
              if sx then bv_swrap (8 * N.of_nat n) u else u).
Lemma L_AX2L_blob_val : @blob_val = @AX2.blob_val.
Proof. unfold blob_val. rewrite ?L_AX2L_blob_bytes. reflexivity. Qed.

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
Lemma L_AX2L_edenot : @edenot = @AX2.edenot.
Proof. unfold edenot. rewrite ?L_AX2L_ext_val, ?L_AX2L_blob_val. reflexivity. Qed.

Definition aluop_eqb (a b : aluop) : bool :=
  match a, b with
  | ALU_ADD, ALU_ADD | ALU_SUB, ALU_SUB | ALU_SLL, ALU_SLL | ALU_SLT, ALU_SLT
  | ALU_SLTU, ALU_SLTU | ALU_XOR, ALU_XOR | ALU_SRL, ALU_SRL | ALU_SRA, ALU_SRA
  | ALU_OR, ALU_OR | ALU_AND, ALU_AND => true
  | _, _ => false
  end.
Lemma L_AX2L_aluop_eqb : @aluop_eqb = @AX2.aluop_eqb.
Proof. unfold aluop_eqb. reflexivity. Qed.

Definition mulop_eqb (a b : mulop) : bool :=
  match a, b with
  | M_MUL, M_MUL | M_MULH, M_MULH | M_MULHSU, M_MULHSU | M_MULHU, M_MULHU
  | M_DIV, M_DIV | M_DIVU, M_DIVU | M_REM, M_REM | M_REMU, M_REMU => true
  | _, _ => false
  end.
Lemma L_AX2L_mulop_eqb : @mulop_eqb = @AX2.mulop_eqb.
Proof. unfold mulop_eqb. reflexivity. Qed.

Fixpoint expr_eqb (x y : expr) : bool :=
  match x, y with
  | ELit a, ELit b => Z.eqb a b
  | EVar a, EVar b => CXNAT.eqbF a b
  | EAlu o a b, EAlu o' a' b' => aluop_eqb o o' && expr_eqb a a' && expr_eqb b b'
  | EAluw o a b, EAluw o' a' b' => aluop_eqb o o' && expr_eqb a a' && expr_eqb b b'
  | EMd o a b, EMd o' a' b' => mulop_eqb o o' && expr_eqb a a' && expr_eqb b b'
  | EMdw o a b, EMdw o' a' b' => mulop_eqb o o' && expr_eqb a a' && expr_eqb b b'
  | EExt s l n a, EExt s' l' n' a' =>
      Bool.eqb s s' && CXNAT.eqbF l l' && CXNAT.eqbF n n' && expr_eqb a a'
  | EBlob s k i n, EBlob s' k' i' n' =>
      Bool.eqb s s' && CXNAT.eqbF k k' && Z.eqb i i' && CXNAT.eqbF n n'
  | _, _ => false
  end.
Lemma L_AX2L_expr_eqb : @expr_eqb = @AX2.expr_eqb.
Proof. unfold expr_eqb. rewrite ?L_AX2L_aluop_eqb, ?L_AX2L_mulop_eqb, ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

Definition zalu (op : aluop) (x y : Z) : Z :=
  bv_unsigned (alu64 op (Z_to_bv 64 x) (Z_to_bv 64 y)).
Lemma L_AX2L_zalu : @zalu = @AX2.zalu.
Proof. unfold zalu. reflexivity. Qed.

Definition zaluw (op : aluop) (x y : Z) : Z :=
  bv_unsigned (sext 64 (alu32 op (low32 (Z_to_bv 64 x)) (low32 (Z_to_bv 64 y))) : word).
Lemma L_AX2L_zaluw : @zaluw = @AX2.zaluw.
Proof. unfold zaluw. reflexivity. Qed.

Definition zmd (op : mulop) (x y : Z) : Z :=
  bv_unsigned (mul_div op (Z_to_bv 64 x) (Z_to_bv 64 y)).
Lemma L_AX2L_zmd : @zmd = @AX2.zmd.
Proof. unfold zmd. reflexivity. Qed.

Definition zmdw (op : mulop) (x y : Z) : Z :=
  bv_unsigned (sext 64 (mul_div op (low32 (Z_to_bv 64 x)) (low32 (Z_to_bv 64 y))) : word).
Lemma L_AX2L_zmdw : @zmdw = @AX2.zmdw.
Proof. unfold zmdw. reflexivity. Qed.

Definition zext_lit (sx : bool) (lo n : nat) (x : Z) : Z :=
  bv_unsigned (ext_val sx lo n (Z_to_bv 64 x)).
Lemma L_AX2L_zext_lit : @zext_lit = @AX2.zext_lit.
Proof. unfold zext_lit. rewrite ?L_AX2L_ext_val. reflexivity. Qed.

Definition is_lit (e : expr) : option Z :=
  match e with ELit z => Some z | _ => None end.
Lemma L_AX2L_is_lit : @is_lit = @AX2.is_lit.
Proof. unfold is_lit. reflexivity. Qed.

Definition two64z : Z := CXLF.p64.
Lemma L_AX2L_two64z : @two64z = @AX2.two64z.
Proof. unfold two64z. rewrite ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

Definition two64 : Z := CXLF.p64.
Lemma L_AX2L_two64 : @two64 = @AX2.two64.
Proof. unfold two64. rewrite ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

Definition two64m1 : Z := two64 - 1.
Lemma L_AX2L_two64m1 : @two64m1 = @AX2.two64m1.
Proof. unfold two64m1. rewrite ?L_AX2L_two64. reflexivity. Qed.

Definition two63z : Z := CXLF.p63.
Lemma L_AX2L_two63z : @two63z = @AX2.two63z.
Proof. unfold two63z. rewrite ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

Definition mtwo63z : Z := - CXLF.p63.
Lemma L_AX2L_mtwo63z : @mtwo63z = @AX2.mtwo63z.
Proof. unfold mtwo63z. rewrite ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

Definition two32z : Z := CXLF.p32.
Lemma L_AX2L_two32z : @two32z = @AX2.two32z.
Proof. unfold two32z. rewrite ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

Definition two31z : Z := CXLF.p31.
Lemma L_AX2L_two31z : @two31z = @AX2.two31z.
Proof. unfold two31z. rewrite ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

Definition ones64z : Z := Z.ones 64.
Lemma L_AX2L_ones64z : @ones64z = @AX2.ones64z.
Proof. unfold ones64z. reflexivity. Qed.

Definition snorm_ref (k : Z) : Z :=
  let m := (k mod two64z)%Z in if Z.leb (CXLF.p63) m then (m - two64z)%Z else m.
Lemma L_AX2L_snorm_ref : @snorm_ref = @AX2.snorm_ref.
Proof. unfold snorm_ref. rewrite ?L_AX2L_two64z, ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

Definition snorm (k : Z) : Z :=
  if (if Z.leb mtwo63z k then Z.ltb k two63z else false) then k
  else let m := Z.land k ones64z in if Z.leb two63z m then (m - two64z)%Z else m.
Lemma L_AX2L_snorm : @snorm = @AX2.snorm.
Proof. unfold snorm. rewrite ?L_AX2L_two64z, ?L_AX2L_two63z, ?L_AX2L_mtwo63z, ?L_AX2L_ones64z. reflexivity. Qed.

Definition zmod64 (z : Z) : Z :=
  if (if Z.leb 0 z then Z.ltb z two64z else false) then z else Z.land z ones64z.
Lemma L_AX2L_zmod64 : @zmod64 = @AX2.zmod64.
Proof. unfold zmod64. rewrite ?L_AX2L_two64z, ?L_AX2L_ones64z. reflexivity. Qed.

Definition zdiv64 (z : Z) : Z :=
  if (if Z.leb 0 z then Z.ltb z two64z else false) then 0 else Z.shiftr z 64.
Lemma L_AX2L_zdiv64 : @zdiv64 = @AX2.zdiv64.
Proof. unfold zdiv64. rewrite ?L_AX2L_two64z. reflexivity. Qed.

Definition wrap64 (z : Z) : Z :=
  if (Z.leb 0 z && Z.ltb z two64)%bool then z else (CXLF.zm64 z)%Z.
Lemma L_AX2L_wrap64 : @wrap64 = @AX2.wrap64.
Proof. unfold wrap64. rewrite ?L_AX2L_two64, ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

Definition sx32 (r : Z) : Z :=
  if Z.ltb r 2147483648 then r else (r + 18446744069414584320)%Z.
Lemma L_AX2L_sx32 : @sx32 = @AX2.sx32.
Proof. unfold sx32. reflexivity. Qed.

Definition ones32z : Z := Z.ones 32.
Lemma L_AX2L_ones32z : @ones32z = @AX2.ones32z.
Proof. unfold ones32z. reflexivity. Qed.

Definition land64 (z : Z) : Z :=
  if (Z.leb 0 z && Z.ltb z two64)%bool then z else Z.land z ones64z.
Lemma L_AX2L_land64 : @land64 = @AX2.land64.
Proof. unfold land64. rewrite ?L_AX2L_two64, ?L_AX2L_ones64z. reflexivity. Qed.

Definition land32 (z : Z) : Z :=
  if (Z.leb 0 z && Z.ltb z two32z)%bool then z else Z.land z ones32z.
Lemma L_AX2L_land32 : @land32 = @AX2.land32.
Proof. unfold land32. rewrite ?L_AX2L_two32z, ?L_AX2L_ones32z. reflexivity. Qed.

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
Lemma L_AX2L_zfast : @zfast = @AX2.zfast.
Proof. unfold zfast. rewrite ?L_AX2L_zalu, ?L_AX2L_two64, ?L_AX2L_land64. reflexivity. Qed.

Definition zfastw (op : aluop) (x y : Z) : Z :=
  match op with
  | ALU_ADD => sx32 (land32 (x + y))
  | ALU_SUB => sx32 (land32 (x - y))
  | ALU_SRL => sx32 (Z.shiftr (land32 x) (Z.land y 31))
  | ALU_SLL => sx32 (land32 (Z.shiftl (land32 x) (Z.land y 31)))
  | _ => zaluw op x y
  end.
Lemma L_AX2L_zfastw : @zfastw = @AX2.zfastw.
Proof. unfold zfastw. rewrite ?L_AX2L_zaluw, ?L_AX2L_sx32, ?L_AX2L_land32. reflexivity. Qed.

Definition zfastm (op : mulop) (x y : Z) : Z :=
  match op with
  | M_MUL => land64 (x * y)
  | _ => zmd op x y
  end.
Lemma L_AX2L_zfastm : @zfastm = @AX2.zfastm.
Proof. unfold zfastm. rewrite ?L_AX2L_zmd, ?L_AX2L_land64. reflexivity. Qed.

Definition zext_fast (sx : bool) (lo n : nat) (x : Z) : Z :=
  let k := (8 * Z.of_nat n)%Z in
  let u := Z.land (Z.shiftr x (8 * Z.of_nat lo)) (Z.ones k) in
  if sx then match n with
             | O => wrap64 u
             | _ => if Z.ltb u (Z.shiftl 1 (k - 1)) then wrap64 u else wrap64 (u - Z.shiftl 1 k + two64)
             end
  else wrap64 u.
Lemma L_AX2L_zext_fast : @zext_fast = @AX2.zext_fast.
Proof. unfold zext_fast. rewrite ?L_AX2L_two64, ?L_AX2L_wrap64. reflexivity. Qed.

Definition zalu_l (op : aluop) (x y : Z) : Z := zfast op (wrap64 x) (wrap64 y).
Lemma L_AX2L_zalu_l : @zalu_l = @AX2.zalu_l.
Proof. unfold zalu_l. rewrite ?L_AX2L_wrap64, ?L_AX2L_zfast. reflexivity. Qed.

Definition zaluw_l (op : aluop) (x y : Z) : Z := zfastw op (wrap64 x) (wrap64 y).
Lemma L_AX2L_zaluw_l : @zaluw_l = @AX2.zaluw_l.
Proof. unfold zaluw_l. rewrite ?L_AX2L_wrap64, ?L_AX2L_zfastw. reflexivity. Qed.

Definition zmd_l (op : mulop) (x y : Z) : Z := zfastm op (wrap64 x) (wrap64 y).
Lemma L_AX2L_zmd_l : @zmd_l = @AX2.zmd_l.
Proof. unfold zmd_l. rewrite ?L_AX2L_wrap64, ?L_AX2L_zfastm. reflexivity. Qed.

Definition lin : Type := (Z * list (Z * expr))%type.
Lemma L_AX2L_lin : @lin = @AX2.lin.
Proof. unfold lin. reflexivity. Qed.

Definition ctor_ix (e : expr) : nat :=
  match e with
  | ELit _ => 0 | EVar _ => 1 | EAlu _ _ _ => 2 | EAluw _ _ _ => 3
  | EMd _ _ _ => 4 | EMdw _ _ _ => 5 | EExt _ _ _ _ => 6 | EBlob _ _ _ _ => 7
  end.
Lemma L_AX2L_ctor_ix : @ctor_ix = @AX2.ctor_ix.
Proof. unfold ctor_ix. reflexivity. Qed.

Definition aluop_ix (op : aluop) : nat :=
  match op with
  | ALU_ADD => 0 | ALU_SUB => 1 | ALU_SLL => 2 | ALU_SLT => 3 | ALU_SLTU => 4
  | ALU_XOR => 5 | ALU_SRL => 6 | ALU_SRA => 7 | ALU_OR => 8 | ALU_AND => 9
  end.
Lemma L_AX2L_aluop_ix : @aluop_ix = @AX2.aluop_ix.
Proof. unfold aluop_ix. reflexivity. Qed.

Definition mulop_ix (op : mulop) : nat :=
  match op with
  | M_MUL => 0 | M_MULH => 1 | M_MULHSU => 2 | M_MULHU => 3
  | M_DIV => 4 | M_DIVU => 5 | M_REM => 6 | M_REMU => 7
  end.
Lemma L_AX2L_mulop_ix : @mulop_ix = @AX2.mulop_ix.
Proof. unfold mulop_ix. reflexivity. Qed.

Definition bool_ix (b : bool) : nat := if b then 1 else 0.
Lemma L_AX2L_bool_ix : @bool_ix = @AX2.bool_ix.
Proof. unfold bool_ix. reflexivity. Qed.

Definition lexc (c k : comparison) : comparison := match c with Eq => k | _ => c end.
Lemma L_AX2L_lexc : @lexc = @AX2.lexc.
Proof. unfold lexc. reflexivity. Qed.

Fixpoint expr_cmp (x y : expr) {struct x} : comparison :=
  match x, y with
  | ELit a, ELit b => Z.compare a b
  | EVar a, EVar b => CXNAT.compareF a b
  | EAlu o a b, EAlu o' a' b' =>
      lexc (CXNAT.compareF (aluop_ix o) (aluop_ix o')) (lexc (expr_cmp a a') (expr_cmp b b'))
  | EAluw o a b, EAluw o' a' b' =>
      lexc (CXNAT.compareF (aluop_ix o) (aluop_ix o')) (lexc (expr_cmp a a') (expr_cmp b b'))
  | EMd o a b, EMd o' a' b' =>
      lexc (CXNAT.compareF (mulop_ix o) (mulop_ix o')) (lexc (expr_cmp a a') (expr_cmp b b'))
  | EMdw o a b, EMdw o' a' b' =>
      lexc (CXNAT.compareF (mulop_ix o) (mulop_ix o')) (lexc (expr_cmp a a') (expr_cmp b b'))
  | EExt s l n e, EExt s' l' n' e' =>
      lexc (CXNAT.compareF (bool_ix s) (bool_ix s'))
           (lexc (CXNAT.compareF l l') (lexc (CXNAT.compareF n n') (expr_cmp e e')))
  | EBlob s k i n, EBlob s' k' i' n' =>
      lexc (CXNAT.compareF (bool_ix s) (bool_ix s'))
           (lexc (CXNAT.compareF k k') (lexc (Z.compare i i') (CXNAT.compareF n n')))
  | _, _ => CXNAT.compareF (ctor_ix x) (ctor_ix y)
  end.
Lemma L_AX2L_expr_cmp : @expr_cmp = @AX2.expr_cmp.
Proof. unfold expr_cmp. rewrite ?L_AX2L_ctor_ix, ?L_AX2L_aluop_ix, ?L_AX2L_mulop_ix, ?L_AX2L_bool_ix, ?L_AX2L_lexc, ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

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
Lemma L_AX2L_lins : @lins = @AX2.lins.
Proof. unfold lins. rewrite ?L_AX2L_expr_eqb, ?L_AX2L_snorm, ?L_AX2L_expr_cmp. reflexivity. Qed.

Definition ladd (x y : lin) : lin :=
  (snorm (fst x + fst y), fold_right (fun t acc => lins (fst t) (snd t) acc) (snd y) (snd x)).
Lemma L_AX2L_ladd : @ladd = @AX2.ladd.
Proof. unfold ladd. rewrite ?L_AX2L_snorm, ?L_AX2L_lin, ?L_AX2L_lins. reflexivity. Qed.

Fixpoint lscale_terms (m : Z) (ts : list (Z * expr)) : list (Z * expr) :=
  match ts with
  | [] => []
  | (k, a) :: rest =>
      let k' := snorm (m * k) in
      if Z.eqb k' 0 then lscale_terms m rest else (k', a) :: lscale_terms m rest
  end.
Lemma L_AX2L_lscale_terms : @lscale_terms = @AX2.lscale_terms.
Proof. unfold lscale_terms. rewrite ?L_AX2L_snorm. reflexivity. Qed.

Definition lscale (m : Z) (x : lin) : lin := (snorm (m * fst x), lscale_terms m (snd x)).
Lemma L_AX2L_lscale : @lscale = @AX2.lscale.
Proof. unfold lscale. rewrite ?L_AX2L_snorm, ?L_AX2L_lin, ?L_AX2L_lscale_terms. reflexivity. Qed.

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
Lemma L_AX2L_lin_of : @lin_of = @AX2.lin_of.
Proof. unfold lin_of. rewrite ?L_AX2L_snorm, ?L_AX2L_lin, ?L_AX2L_ladd, ?L_AX2L_lscale. reflexivity. Qed.

Definition lterm (t : Z * expr) : expr :=
  if Z.eqb (fst t) 1 then snd t else EMd M_MUL (ELit (fst t)) (snd t).
Lemma L_AX2L_lterm : @lterm = @AX2.lterm.
Proof. unfold lterm. reflexivity. Qed.

Fixpoint lterms (ts : list (Z * expr)) : expr :=
  match ts with
  | [] => ELit 0
  | [t] => lterm t
  | t :: rest => EAlu ALU_ADD (lterm t) (lterms rest)
  end.
Lemma L_AX2L_lterms : @lterms = @AX2.lterms.
Proof. unfold lterms. rewrite ?L_AX2L_lterm. reflexivity. Qed.

Definition unlin (x : lin) : expr :=
  match snd x with
  | [] => ELit (fst x)
  | _ => if Z.eqb (fst x) 0 then lterms (snd x) else EAlu ALU_ADD (lterms (snd x)) (ELit (fst x))
  end.
Lemma L_AX2L_unlin : @unlin = @AX2.unlin.
Proof. unfold unlin. rewrite ?L_AX2L_lin, ?L_AX2L_lterms. reflexivity. Qed.

Fixpoint coeffs_div (m : Z) (ts : list (Z * expr)) : bool :=
  match ts with
  | [] => true
  | (k, _) :: rest => (Z.eqb (k mod m) 0 && coeffs_div m rest)%bool
  end.
Lemma L_AX2L_coeffs_div : @coeffs_div = @AX2.coeffs_div.
Proof. unfold coeffs_div. reflexivity. Qed.

Definition lin_lowbits (e : expr) (k : Z) : option Z :=
  let l := lin_of e in
  if coeffs_div (CXLF.zpow2 k) (snd l) then Some ((fst l) mod 2 ^ k)%Z else None.
Lemma L_AX2L_lin_lowbits : @lin_lowbits = @AX2.lin_lowbits.
Proof. unfold lin_lowbits. rewrite ?L_AX2L_lin_of, ?L_AX2L_coeffs_div, ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

Definition shamt_of (e : expr) (bits : Z) : option Z :=
  match e with
  | ELit s => Some (CXLF.zmodp s bits)
  | _ => lin_lowbits e bits
  end.
Lemma L_AX2L_shamt_of : @shamt_of = @AX2.shamt_of.
Proof. unfold shamt_of. rewrite ?L_AX2L_lin_lowbits, ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

Definition mkAlu (op : aluop) (a b : expr) : expr :=
  match is_lit a, is_lit b with
  | Some x, Some y => ELit (zalu_l op x y)
  | _, _ =>
    match op with
    | ALU_ADD => unlin (ladd (lin_of a) (lin_of b))
    | ALU_SUB => unlin (ladd (lin_of a) (lscale (-1) (lin_of b)))
    | ALU_SLL => match shamt_of b 6 with
                 | Some s => unlin (lscale (CXLF.zpow2 s) (lin_of a))
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
Lemma L_AX2L_mkAlu : @mkAlu = @AX2.mkAlu.
Proof. unfold mkAlu. rewrite ?L_AX2L_is_lit, ?L_AX2L_zalu_l, ?L_AX2L_ladd, ?L_AX2L_lscale, ?L_AX2L_lin_of, ?L_AX2L_unlin, ?L_AX2L_shamt_of, ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

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
Lemma L_AX2L_mkAluw : @mkAluw = @AX2.mkAluw.
Proof. unfold mkAluw. rewrite ?L_AX2L_is_lit, ?L_AX2L_zaluw_l, ?L_AX2L_shamt_of. reflexivity. Qed.

Definition mkMd (op : mulop) (a b : expr) : expr :=
  match is_lit a, is_lit b with
  | Some x, Some y => ELit (zmd_l op x y)
  | Some x, None => match op with M_MUL => unlin (lscale x (lin_of b)) | _ => EMd op a b end
  | None, Some y => match op with M_MUL => unlin (lscale y (lin_of a)) | _ => EMd op a b end
  | _, _ => EMd op a b
  end.
Lemma L_AX2L_mkMd : @mkMd = @AX2.mkMd.
Proof. unfold mkMd. rewrite ?L_AX2L_is_lit, ?L_AX2L_zmd_l, ?L_AX2L_lscale, ?L_AX2L_lin_of, ?L_AX2L_unlin. reflexivity. Qed.

Definition mkMdw (op : mulop) (a b : expr) : expr :=
  match is_lit a, is_lit b with
  | Some x, Some y => ELit (zmdw op x y)
  | _, _ => EMdw op a b
  end.
Lemma L_AX2L_mkMdw : @mkMdw = @AX2.mkMdw.
Proof. unfold mkMdw. rewrite ?L_AX2L_zmdw, ?L_AX2L_is_lit. reflexivity. Qed.

Definition mkExt (sx : bool) (lo n : nat) (e : expr) : expr :=
  match e with
  | ELit x => ELit (zext_fast sx lo n (wrap64 x))   
  | _ =>
    if (CXNAT.eqbF lo 0 && CXNAT.eqbF n 8)%bool then e
    else match e with
         | EExt false lo' n' e' =>
             if (CXNAT.lebF (lo + n) n' && CXNAT.lebF n' 8)%bool then EExt sx (lo' + lo) n e'
             else EExt sx lo n e
         | _ => EExt sx lo n e
         end
  end.
Lemma L_AX2L_mkExt : @mkExt = @AX2.mkExt.
Proof. unfold mkExt. rewrite ?L_AX2L_wrap64, ?L_AX2L_zext_fast, ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

Definition ridx (r : reg) : nat := Z.to_nat (bv_unsigned r).
Lemma L_AX2L_ridx : @ridx = @AX2.ridx.
Proof. unfold ridx. reflexivity. Qed.

Definition sr_get (sr : list expr) (r : reg) : expr :=
  if bv_eqb r 0 then ELit 0 else CXNAT.nthF (ridx r) sr (ELit 0).
Lemma L_AX2L_sr_get : @sr_get = @AX2.sr_get.
Proof. unfold sr_get. rewrite ?L_AX2L_ridx, ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

Fixpoint sr_upd (sr : list expr) (n : nat) (e : expr) : list expr :=
  match n with
  | O => match sr with [] => [e] | _ :: t => e :: t end
  | S n' => match sr with
            | [] => ELit 0 :: sr_upd [] n' e
            | h :: t => h :: sr_upd t n' e
            end
  end.
Lemma L_AX2L_sr_upd : @sr_upd = @AX2.sr_upd.
Proof. unfold sr_upd. reflexivity. Qed.

Definition sr_id : list expr :=
  [EVar 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7;
   EVar 8; EVar 9; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15;
   EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23;
   EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Lemma L_AX2L_sr_id : @sr_id = @AX2.sr_id.
Proof. unfold sr_id. reflexivity. Qed.

Definition split_lit (e : expr) : expr * Z :=
  match e with
  | ELit z => (ELit 0, z)
  | EAlu ALU_ADD b (ELit z) => (b, z)
  | _ => (e, 0%Z)
  end.
Lemma L_AX2L_split_lit : @split_lit = @AX2.split_lit.
Proof. unfold split_lit. reflexivity. Qed.

Definition to_saddr (e : expr) (imm : Z) : saddr :=
  let (b, k) := split_lit e in SA b (k + imm).
Lemma L_AX2L_to_saddr : @to_saddr = @AX2.to_saddr.
Proof. unfold to_saddr. rewrite ?L_AX2L_split_lit. reflexivity. Qed.

Definition adenot (E : env) (a : saddr) : word :=
  v_addi (edenot E (a_base a)) (a_off a).
Lemma L_AX2L_adenot : @adenot = @AX2.adenot.
Proof. unfold adenot. rewrite ?L_AX2L_edenot. reflexivity. Qed.

Definition saddr_eqb (a b : saddr) : bool :=
  expr_eqb (a_base a) (a_base b) && Z.eqb (a_off a) (a_off b).
Lemma L_AX2L_saddr_eqb : @saddr_eqb = @AX2.saddr_eqb.
Proof. unfold saddr_eqb. rewrite ?L_AX2L_expr_eqb. reflexivity. Qed.

Definition sset (ss : sym_state) (rd : reg) (e : expr) (npc : Z) : sym_state :=
  SSR npc (if bv_eqb rd 0 then s_regs ss else sr_upd (s_regs ss) (ridx rd) e)
     (s_log ss) (s_know ss) (s_next ss) (s_resv ss).
Lemma L_AX2L_sset : @sset = @AX2.sset.
Proof. unfold sset. rewrite ?L_AX2L_ridx, ?L_AX2L_sr_upd. reflexivity. Qed.

Definition sjump (ss : sym_state) (npc : Z) : sym_state :=
  SSR npc (s_regs ss) (s_log ss) (s_know ss) (s_next ss) (s_resv ss).
Lemma L_AX2L_sjump : @sjump = @AX2.sjump.
Proof. unfold sjump. reflexivity. Qed.

Definition clr (ss : sym_state) : sym_state :=
  SSR (s_pc ss) (s_regs ss) (s_log ss) (s_know ss) (s_next ss) None.
Lemma L_AX2L_clr : @clr = @AX2.clr.
Proof. unfold clr. reflexivity. Qed.

Definition s_clean (ss : sym_state) : bool :=
  match s_resv ss with None => true | Some _ => false end.
Lemma L_AX2L_s_clean : @s_clean = @AX2.s_clean.
Proof. unfold s_clean. reflexivity. Qed.

Definition rel_lit (rb : expr) (rk : Z) (rn : Z) (kb : expr) (kk : Z) (kn : Z) : rangerel :=
  if expr_eqb rb kb then
    if (Z.leb kk rk && Z.leb (rk + rn) (kk + kn))%bool then RInside (rk - kk)
    else if (Z.leb (rk + rn) kk || Z.leb (kk + kn) rk)%bool then RDisjoint
    else RPartial
  else RUnknown.
Lemma L_AX2L_rel_lit : @rel_lit = @AX2.rel_lit.
Proof. unfold rel_lit. rewrite ?L_AX2L_expr_eqb. reflexivity. Qed.

Definition elen (n : nat) : expr := ELit (Z.of_nat n).
Lemma L_AX2L_elen : @elen = @AX2.elen.
Proof. unfold elen. reflexivity. Qed.

Definition lit_strip (e : expr) : expr * Z :=
  match e with
  | EAlu ALU_ADD v (ELit c) => (v, c)
  | _ => (e, 0%Z)
  end.
Lemma L_AX2L_lit_strip : @lit_strip = @AX2.lit_strip.
Proof. unfold lit_strip. reflexivity. Qed.

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
          if (Z.leb 0 lo && Z.leb lo hi && Z.ltb hi (CXLF.p64) && Z.leb 0 (lo + d) && Z.ltb (hi + d) (CXLF.p64))%bool
          then Some ((lo + d)%Z, (hi + d)%Z) else find_range rest e
        else find_range rest e
      end
  | _ :: rest => find_range rest e
  end.
Lemma L_AX2L_find_range : @find_range = @AX2.find_range.
Proof. unfold find_range. rewrite ?L_AX2L_expr_eqb, ?L_AX2L_lit_strip, ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

Fixpoint find_align (kn : list kentry) (e : expr) : option Z :=
  match kn with
  | [] => None
  | KAlign e' m :: rest => if expr_eqb e e' then Some m else find_align rest e
  | _ :: rest => find_align rest e
  end.
Lemma L_AX2L_find_align : @find_align = @AX2.find_align.
Proof. unfold find_align. rewrite ?L_AX2L_expr_eqb. reflexivity. Qed.

Definition clampi (r : Z * Z) : Z * Z :=
  let (lo, hi) := r in (Z.max lo 0, Z.min hi two64m1).
Lemma L_AX2L_clampi : @clampi = @AX2.clampi.
Proof. unfold clampi. rewrite ?L_AX2L_two64m1. reflexivity. Qed.

Definition mask_cover (h : Z) : Z :=
  if Z.ltb h 0 then 0 else (2 ^ (Z.log2_up (h + 1)) - 1)%Z.
Lemma L_AX2L_mask_cover : @mask_cover = @AX2.mask_cover.
Proof. unfold mask_cover. reflexivity. Qed.

Definition lit_shamt (e : expr) : option Z :=
  match e with ELit s => Some (s mod 64)%Z | _ => None end.
Lemma L_AX2L_lit_shamt : @lit_shamt = @AX2.lit_shamt.
Proof. unfold lit_shamt. reflexivity. Qed.

Definition zsigned64 (v : Z) : Z := if Z.leb two63z v then (v - two64)%Z else v.
Lemma L_AX2L_zsigned64 : @zsigned64 = @AX2.zsigned64.
Proof. unfold zsigned64. rewrite ?L_AX2L_two64, ?L_AX2L_two63z. reflexivity. Qed.

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
Lemma L_AX2L_lin_range : @lin_range = @AX2.lin_range.
Proof. unfold lin_range. reflexivity. Qed.

Definition lin_trivial (l : lin) : bool :=
  match l with
  | (c, [(k, _)]) => (Z.eqb c 0 && Z.eqb k 1)%bool
  | _ => false
  end.
Lemma L_AX2L_lin_trivial : @lin_trivial = @AX2.lin_trivial.
Proof. unfold lin_trivial. rewrite ?L_AX2L_lin. reflexivity. Qed.

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
          
          match (match b, erange kn a with
                 | ELit m, Some (al, ah) =>
                     let m' := (CXLF.zm64 m)%Z in
                     let j := Z.log2 (m' + 1) in
                     if (Z.eqb (m' + 1) (CXLF.zpow2 j) && Z.leb (CXLF.zshr al j) (CXLF.zshr ah j) && Z.eqb (CXLF.zshr al j) (CXLF.zshr ah j))%bool
                     then Some ((CXLF.zmodp al j), (CXLF.zmodp ah j))
                     else let jh := Z.log2 (two64 - m') in
                          if (Z.eqb (two64 - m') (CXLF.zpow2 jh) && Z.ltb jh 64)%bool
                          then Some ((al - al mod 2 ^ jh)%Z, (ah - ah mod 2 ^ jh)%Z)
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
          | Some (al, ah), Some s => Some ((CXLF.zshr al s), (CXLF.zshr ah s))
          | _, _ => None
          end
      | ALU_SRA =>
          match erange kn a, lit_shamt b with
          | Some (al, ah), Some s =>
              if Z.ltb ah (CXLF.p63) then Some ((CXLF.zshr al s), (CXLF.zshr ah s)) else None
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
              if (Z.ltb ah (CXLF.p63) && Z.ltb bh (CXLF.p63))%bool then
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
              if (Z.leb 0 (al + bl') && Z.ltb (ah + bh') (CXLF.p31))%bool
              then Some ((al + bl')%Z, (ah + bh')%Z) else None
          | _, _ => None
          end
      | ALU_SUB =>
          match erange kn a, erange kn b with
          | Some (al, ah), Some (bl, bh) =>
              if (Z.leb bh al && Z.ltb (ah - bl) (CXLF.p31))%bool
              then Some ((al - bh)%Z, (ah - bl)%Z) else None
          | _, _ => None
          end
      | ALU_SLL =>
          match erange kn a, lit_shamt b with
          | Some (al, ah), Some s =>
              let s' := (s mod 32)%Z in
              if Z.ltb (ah * 2 ^ s') (CXLF.p31) then Some ((al * 2 ^ s')%Z, (ah * 2 ^ s')%Z) else None
          | _, _ => None
          end
      | ALU_SRL =>
          match erange kn a, lit_shamt b with
          | Some (al, ah), Some s =>
              let s' := (s mod 32)%Z in
              if (Z.ltb ah (CXLF.p32) && (Z.ltb 0 s' || Z.ltb ah (CXLF.p31)))%bool
              then Some ((CXLF.zshr al s'), (CXLF.zshr ah s')) else None
          | _, _ => None
          end
      | ALU_SRA =>
          match erange kn a, lit_shamt b with
          | Some (al, ah), Some s =>
              let s' := (s mod 32)%Z in
              if Z.ltb ah (CXLF.p31) then Some ((CXLF.zshr al s'), (CXLF.zshr ah s')) else None
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
              let d' := (CXLF.zm64 d)%Z in
              if Z.ltb 0 d' then Some ((al / d')%Z, (ah / d')%Z) else None
          | _, _ => None
          end
      | M_REMU =>
          match erange kn a, b with
          | Some (al, ah), ELit d =>
              let d' := (CXLF.zm64 d)%Z in
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
            if (Z.leb 0 al && Z.ltb ah (CXLF.zhalf w))%bool then Some (al, ah)
            else if (CXNAT.lebF 1 n && CXNAT.lebF n 8 && Z.leb (CXLF.zhalf w) al && Z.ltb ah w)%bool
                 then Some ((two64 - w + al)%Z, (two64 - w + ah)%Z) else None
        | _, _ => None
        end
      else
        match lo, erange kn a with
        | O, Some (al, ah) =>
            if (Z.leb 0 al && Z.ltb ah w)%bool then Some (al, ah) else Some (0%Z, Z.min (w - 1) (two64 - 1))
        | _, _ => Some (0%Z, Z.min (w - 1) (two64 - 1))
        end
  | EBlob sx k i n =>
      
      if sx then Some (0%Z, two64m1) else Some (0%Z, Z.min (2 ^ (8 * Z.of_nat n) - 1) (two64 - 1))%Z
  end
  end
  end
  end.
Lemma L_AX2L_erange_f : @erange_f = @AX2.erange_f.
Proof. unfold erange_f. rewrite ?L_AX2L_two64, ?L_AX2L_two64m1, ?L_AX2L_zmod64, ?L_AX2L_zdiv64, ?L_AX2L_lin_of, ?L_AX2L_find_range, ?L_AX2L_clampi, ?L_AX2L_mask_cover, ?L_AX2L_lit_shamt, ?L_AX2L_zsigned64, ?L_AX2L_lin_range, ?L_AX2L_lin_trivial, ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

Definition erange_fuel : nat := 64%nat.
Lemma L_AX2L_erange_fuel : @erange_fuel = @AX2.erange_fuel.
Proof. unfold erange_fuel. reflexivity. Qed.

Definition is_factb (K : kentry) : bool :=
  match K with KRange _ _ _ | KAlign _ _ | KDisj _ _ _ _ | KWr _ _ => true | _ => false end.
Lemma L_AX2L_is_factb : @is_factb = @AX2.is_factb.
Proof. unfold is_factb. reflexivity. Qed.

Fixpoint all_factsb (kn : list kentry) : bool :=
  match kn with [] => true | K :: rest => if is_factb K then all_factsb rest else false end.
Lemma L_AX2L_all_factsb : @all_factsb = @AX2.all_factsb.
Proof. unfold all_factsb. rewrite ?L_AX2L_is_factb. reflexivity. Qed.

Definition facts_of (kn : list kentry) : list kentry :=
  if all_factsb kn then kn else List.filter is_factb kn.
Lemma L_AX2L_facts_of : @facts_of = @AX2.facts_of.
Proof. unfold facts_of. rewrite ?L_AX2L_is_factb, ?L_AX2L_all_factsb. reflexivity. Qed.

Definition erange0 (kn : list kentry) (e : expr) : option (Z * Z) := erange_f erange_fuel (facts_of kn) e.
Lemma L_AX2L_erange0 : @erange0 = @AX2.erange0.
Proof. unfold erange0. rewrite ?L_AX2L_erange_f, ?L_AX2L_erange_fuel, ?L_AX2L_facts_of. reflexivity. Qed.

Fixpoint deand (e : expr) : expr * Z :=
  match e with
  | EAlu ALU_AND x (ELit m) =>
      let m' := (CXLF.zm64 m)%Z in
      let j := Z.log2 (two64 - m') in
      if (Z.eqb (two64 - m') (CXLF.zpow2 j) && Z.leb j 48)%bool
      then let '(x', s) := deand x in (x', (s + (2 ^ j - 1))%Z)
      else (e, 0%Z)
  | EAlu ALU_ADD a b => let '(a', s1) := deand a in let '(b', s2) := deand b in (EAlu ALU_ADD a' b', (s1 + s2)%Z)
  | _ => (e, 0%Z)
  end.
Lemma L_AX2L_deand : @deand = @AX2.deand.
Proof. unfold deand. rewrite ?L_AX2L_two64, ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

Definition erange (kn : list kentry) (e : expr) : option (Z * Z) :=
  let r := erange0 kn e in
  let '(e', s) := deand e in
  if Z.eqb s 0 then r else
  match erange0 kn (unlin (lin_of e')) with     
  | Some (lo', hi') =>
      if Z.leb s lo' then
        match r with
        | Some (lo, hi) => Some (Z.max lo (lo' - s), Z.min hi hi')
        | None => Some ((lo' - s)%Z, hi')
        end
      else r
  | None => r
  end.
Lemma L_AX2L_erange : @erange = @AX2.erange.
Proof. unfold erange. rewrite ?L_AX2L_lin_of, ?L_AX2L_unlin, ?L_AX2L_erange0, ?L_AX2L_deand. reflexivity. Qed.

Definition base_range (kn : list kentry) (e : expr) : option (Z * Z) :=
  match e with ELit z => let v := (CXLF.zm64 z)%Z in Some (v, v) | _ => erange kn e end.
Lemma L_AX2L_base_range : @base_range = @AX2.base_range.
Proof. unfold base_range. rewrite ?L_AX2L_erange, ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

Definition ctz_fuel : nat -> Z -> Z := CXLF.ctz_fuelF.
Lemma L_AX2L_ctz_fuel : @ctz_fuel = @AX2.ctz_fuel.
Proof. exact CXLF.ctz_fuelF_eqf. Qed.

Definition ctz64 (z : Z) : Z := ctz_fuel 64 z.
Lemma L_AX2L_ctz64 : @ctz64 = @AX2.ctz64.
Proof. unfold ctz64. rewrite ?L_AX2L_ctz_fuel. reflexivity. Qed.

Fixpoint ealign0 (kn : list kentry) (e : expr) {struct e} : Z :=
  match find_align kn e with
  | Some m => if Z.ltb 0 m then ctz64 m else 0%Z
  | None =>
  match e with
  | ELit z => ctz64 (CXLF.zm64 z)
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
Lemma L_AX2L_ealign0 : @ealign0 = @AX2.ealign0.
Proof. unfold ealign0. rewrite ?L_AX2L_find_align, ?L_AX2L_lit_shamt, ?L_AX2L_ctz64, ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

Fixpoint lins_e (k : Z) (a : expr) (ts : list (Z * expr)) : list (Z * expr) :=
  match ts with
  | [] => if Z.eqb k 0 then [] else [(k, a)]
  | (k', a') :: rest =>
      if expr_eqb a a' then (let s := (k + k')%Z in if Z.eqb s 0 then rest else (s, a') :: rest)
      else (k', a') :: lins_e k a rest
  end.
Lemma L_AX2L_lins_e : @lins_e = @AX2.lins_e.
Proof. unfold lins_e. rewrite ?L_AX2L_expr_eqb. reflexivity. Qed.

Definition lsub_e (ts2 ts1 : list (Z * expr)) : list (Z * expr) :=
  fold_right (fun t acc => lins_e (- fst t)%Z (snd t) acc) ts2 ts1.
Lemma L_AX2L_lsub_e : @lsub_e = @AX2.lsub_e.
Proof. unfold lsub_e. rewrite ?L_AX2L_lins_e. reflexivity. Qed.

Fixpoint find_and_atom_k (sg : Z) (ts : list (Z * expr)) : option (expr * Z) :=
  match ts with
  | [] => None
  | (k, EAlu ALU_AND y (ELit mm)) :: r =>
      if (Z.eqb k sg && Z.ltb 0 mm && Z.eqb (Z.land (mm + 1) mm) 0)%bool then Some (y, mm) else find_and_atom_k sg r
  | _ :: r => find_and_atom_k sg r
  end.
Lemma L_AX2L_find_and_atom_k : @find_and_atom_k = @AX2.find_and_atom_k.
Proof. unfold find_and_atom_k. reflexivity. Qed.

Definition find_and_atom (ts : list (Z * expr)) : option (expr * Z) := find_and_atom_k 1 ts.
Lemma L_AX2L_find_and_atom : @find_and_atom = @AX2.find_and_atom.
Proof. unfold find_and_atom. rewrite ?L_AX2L_find_and_atom_k. reflexivity. Qed.

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
Lemma L_AX2L_pageup_low_k : @pageup_low_k = @AX2.pageup_low_k.
Proof. unfold pageup_low_k. rewrite ?L_AX2L_two64, ?L_AX2L_lin_of, ?L_AX2L_lins_e, ?L_AX2L_find_and_atom_k. reflexivity. Qed.

Definition pageup_low (e : expr) (m : Z) : option Z :=
  match pageup_low_k 1 e m with
  | Some r => Some r
  | None => pageup_low_k (-1) e m
  end.
Lemma L_AX2L_pageup_low : @pageup_low = @AX2.pageup_low.
Proof. unfold pageup_low. rewrite ?L_AX2L_pageup_low_k. reflexivity. Qed.

Definition pageup_align (e : expr) : Z :=
  let l := lin_of e in
  match (match find_and_atom_k 1 (snd l) with
         | Some p => Some p
         | None => find_and_atom_k (-1) (snd l)
         end) with
  | Some (y, mm) =>
      let m := (mm + 1)%Z in let k := ctz64 m in
      if (Z.eqb m (CXLF.zpow2 k) && Z.leb k 64)%bool then
        match pageup_low e m with Some 0%Z => k | _ => 0%Z end
      else 0%Z
  | None => 0%Z
  end.
Lemma L_AX2L_pageup_align : @pageup_align = @AX2.pageup_align.
Proof. unfold pageup_align. rewrite ?L_AX2L_lin_of, ?L_AX2L_ctz64, ?L_AX2L_find_and_atom_k, ?L_AX2L_pageup_low, ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

Definition ealign (kn : list kentry) (e : expr) : Z := Z.max (ealign0 (facts_of kn) e) (pageup_align e).
Lemma L_AX2L_ealign : @ealign = @AX2.ealign.
Proof. unfold ealign. rewrite ?L_AX2L_facts_of, ?L_AX2L_ealign0, ?L_AX2L_pageup_align. reflexivity. Qed.

Definition lin_nowrap (kn : list kentry) (e : expr) : bool :=
  let l := lin_of e in
  match lin_range (erange kn) (fst l) (snd l) with
  | Some (lo, hi) => (Z.leb 0 lo && Z.ltb hi two64)%bool
  | None => false
  end.
Lemma L_AX2L_lin_nowrap : @lin_nowrap = @AX2.lin_nowrap.
Proof. unfold lin_nowrap. rewrite ?L_AX2L_two64, ?L_AX2L_lin_of, ?L_AX2L_lin_range, ?L_AX2L_erange. reflexivity. Qed.

Definition srl_rem (e : expr) (m : Z) : expr := EAlu ALU_AND e (ELit (m - 1)%Z).
Lemma L_AX2L_srl_rem : @srl_rem = @AX2.srl_rem.
Proof. unfold srl_rem. reflexivity. Qed.

Definition highmask_s (mk : Z) : option Z :=
  let m' := (CXLF.zm64 mk)%Z in
  let s := Z.log2 (two64 - m') in
  if (Z.eqb (two64 - m') (CXLF.zpow2 s) && Z.ltb 0 s && Z.ltb s 64)%bool then Some s else None.
Lemma L_AX2L_highmask_s : @highmask_s = @AX2.highmask_s.
Proof. unfold highmask_s. rewrite ?L_AX2L_two64, ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

Fixpoint srl_expand (kn : list kentry) (ts : list (Z * expr)) : Z * list (Z * expr) :=
  match ts with
  | [] => (0%Z, [])
  | (k, a) :: rest =>
      let '(c, ts') := srl_expand kn rest in
      let keep := (c, lins_e k a ts') in
      match a with
      | EAlu ALU_SRL e (ELit s) =>
          let m := (2 ^ ((CXLF.zm64 s) mod 64))%Z in
          if (Z.eqb (k mod m)%Z 0%Z && lin_nowrap kn e)%bool then
            let q := (k / m)%Z in
            let le := lin_of e in
            if Z.leb ((CXLF.zm64 s) mod 64) (ealign kn e) then   
              ((c + q * fst le)%Z, fold_right (fun t acc => lins_e (q * fst t)%Z (snd t) acc) ts' (snd le))
            else
            ((c + q * fst le)%Z,
             lins_e (- q)%Z (srl_rem e m) (fold_right (fun t acc => lins_e (q * fst t)%Z (snd t) acc) ts' (snd le)))
          else keep
      | EAlu ALU_AND e (ELit mk) =>
          
          match highmask_s mk with
          | Some s =>
              if lin_nowrap kn e then
                let le := lin_of e in
                ((c + k * fst le)%Z,
                 lins_e (- k)%Z (srl_rem e (CXLF.zpow2 s)) (fold_right (fun t acc => lins_e (k * fst t)%Z (snd t) acc) ts' (snd le)))
              else keep
          | None => keep
          end
      | _ => keep
      end
  end.
Lemma L_AX2L_srl_expand : @srl_expand = @AX2.srl_expand.
Proof. unfold srl_expand. rewrite ?L_AX2L_lin_of, ?L_AX2L_lins_e, ?L_AX2L_ealign, ?L_AX2L_lin_nowrap, ?L_AX2L_srl_rem, ?L_AX2L_highmask_s, ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

Fixpoint has_srl (ts : list (Z * expr)) : bool :=
  match ts with
  | [] => false
  | (_, EAlu ALU_SRL _ (ELit _)) :: _ => true
  | _ :: rest => has_srl rest
  end.
Lemma L_AX2L_has_srl : @has_srl = @AX2.has_srl.
Proof. unfold has_srl. reflexivity. Qed.

Definition sfact : Type := (list (Z * expr) * (Z * Z))%type.
Lemma L_AX2L_sfact : @sfact = @AX2.sfact.
Proof. unfold sfact. reflexivity. Qed.

Definition sum_fact_x (allkn : list kentry) (ts : list (Z * expr)) (lo hi : Z) : list sfact :=
  let '(c2, ts2) := srl_expand allkn ts in
  match ts2 with
  | _ :: _ => if Z.eqb c2 0 then [] else [(ts2, ((lo - c2)%Z, (hi - c2)%Z))]
  | [] => []
  end.
Lemma L_AX2L_sum_fact_x : @sum_fact_x = @AX2.sum_fact_x.
Proof. unfold sum_fact_x. rewrite ?L_AX2L_srl_expand, ?L_AX2L_sfact. reflexivity. Qed.

Fixpoint pin_terms (allkn : list kentry) (ts : list (Z * expr)) (lo hi : Z) : list (Z * expr) * (Z * Z) * bool :=
  match ts with
  | [] => ([], (lo, hi), false)
  | (k, a) :: r =>
      let '(r', lh, hit) := pin_terms allkn r lo hi in
      let '(lo', hi') := lh in
      match erange allkn a with
      | Some (c, c') => if Z.eqb c c' then (r', ((lo' - k * c)%Z, (hi' - k * c)%Z), true) else ((k, a) :: r', (lo', hi'), hit)
      | None => ((k, a) :: r', (lo', hi'), hit)
      end
  end.
Lemma L_AX2L_pin_terms : @pin_terms = @AX2.pin_terms.
Proof. unfold pin_terms. rewrite ?L_AX2L_erange. reflexivity. Qed.

Definition sum_fact_pin (allkn : list kentry) (ts : list (Z * expr)) (lo hi : Z) : list sfact :=
  match pin_terms allkn ts lo hi with
  | ((_ :: _) as ts', lh, true) => [(ts', lh)]
  | _ => []
  end.
Lemma L_AX2L_sum_fact_pin : @sum_fact_pin = @AX2.sum_fact_pin.
Proof. unfold sum_fact_pin. rewrite ?L_AX2L_sfact, ?L_AX2L_pin_terms. reflexivity. Qed.

Fixpoint terms_gcd (ts : list (Z * expr)) : Z :=
  match ts with [] => 0 | (k, _) :: r => Z.gcd k (terms_gcd r) end.
Lemma L_AX2L_terms_gcd : @terms_gcd = @AX2.terms_gcd.
Proof. unfold terms_gcd. reflexivity. Qed.

Definition sfact_reduce (f : sfact) : list sfact :=
  let '(ts, lh) := f in let '(lo, hi) := lh in
  let g := terms_gcd ts in
  if Z.ltb 1 g then [(List.map (fun t => ((fst t / g)%Z, snd t)) ts, (((lo + g - 1) / g)%Z, (hi / g)%Z))] else [].
Lemma L_AX2L_sfact_reduce : @sfact_reduce = @AX2.sfact_reduce.
Proof. unfold sfact_reduce. rewrite ?L_AX2L_sfact, ?L_AX2L_terms_gcd. reflexivity. Qed.

Definition fact_nowrap (allkn : list kentry) (e : expr) (hi : Z) : bool :=
  let l := lin_of e in
  match lin_range (erange allkn) (fst l) (snd l) with
  | Some (a, b) => (Z.ltb b two64 && Z.ltb hi (a + two64))%bool
  | None => false
  end.
Lemma L_AX2L_fact_nowrap : @fact_nowrap = @AX2.fact_nowrap.
Proof. unfold fact_nowrap. rewrite ?L_AX2L_two64, ?L_AX2L_lin_of, ?L_AX2L_lin_range, ?L_AX2L_erange. reflexivity. Qed.

Fixpoint sum_facts (allkn kn : list kentry) : list sfact :=
  match kn with
  | [] => []
  | KRange e lo hi :: rest =>
      match e with
      | EVar _ => sum_facts allkn rest
      | _ =>
        match lin_of e with
        | (c, (_ :: _ :: _) as ts) =>
            if fact_nowrap allkn e hi then
              let pins := sum_fact_pin allkn ts (lo - c)%Z (hi - c)%Z in
              (ts, ((lo - c)%Z, (hi - c)%Z)) :: sfact_reduce (ts, ((lo - c)%Z, (hi - c)%Z)) ++ sum_fact_x allkn ts (lo - c)%Z (hi - c)%Z
                                             ++ pins ++ List.flat_map sfact_reduce pins ++ sum_facts allkn rest
            else sum_facts allkn rest
        | _ => sum_facts allkn rest
        end
      end
  | _ :: rest => sum_facts allkn rest
  end.
Lemma L_AX2L_sum_facts : @sum_facts = @AX2.sum_facts.
Proof. unfold sum_facts. rewrite ?L_AX2L_lin_of, ?L_AX2L_sfact, ?L_AX2L_sum_fact_x, ?L_AX2L_sum_fact_pin, ?L_AX2L_sfact_reduce, ?L_AX2L_fact_nowrap. reflexivity. Qed.

Fixpoint coef_of (a : expr) (ts : list (Z * expr)) : Z :=
  match ts with
  | [] => 0
  | (k, a') :: r => if expr_eqb a a' then k else coef_of a r
  end.
Lemma L_AX2L_coef_of : @coef_of = @AX2.coef_of.
Proof. unfold coef_of. rewrite ?L_AX2L_expr_eqb. reflexivity. Qed.

Definition fact_quot : list (Z * expr) -> list (Z * expr) -> option Z -> option Z := CXLF.fact_quotF.
Lemma L_AX2L_fact_quot : @fact_quot = @AX2.fact_quot.
Proof. exact CXLF.fact_quotF_eqf. Qed.

Definition sub_fact (q : Z) (fts ts : list (Z * expr)) : list (Z * expr) :=
  fold_right (fun t acc => lins_e (- (q * fst t))%Z (snd t) acc) ts fts.
Lemma L_AX2L_sub_fact : @sub_fact = @AX2.sub_fact.
Proof. unfold sub_fact. rewrite ?L_AX2L_lins_e. reflexivity. Qed.

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
Lemma L_AX2L_sum_subst : @sum_subst = @AX2.sum_subst.
Proof. unfold sum_subst. rewrite ?L_AX2L_sfact, ?L_AX2L_fact_quot, ?L_AX2L_sub_fact. reflexivity. Qed.

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
Lemma L_AX2L_lin_test_rel : @lin_test_rel = @AX2.lin_test_rel.
Proof. unfold lin_test_rel. rewrite ?L_AX2L_lin_range, ?L_AX2L_erange, ?L_AX2L_sum_facts, ?L_AX2L_sum_subst. reflexivity. Qed.

Definition lin_test (kn : list kentry) (c : Z) (ts : list (Z * expr)) (test : Z -> Z -> bool) : bool :=
  match lin_range (erange kn) c ts with
  | Some (lo, hi) => if test lo hi then true else lin_test_rel kn c ts test
  | None => lin_test_rel kn c ts test
  end.
Lemma L_AX2L_lin_test : @lin_test = @AX2.lin_test.
Proof. unfold lin_test. rewrite ?L_AX2L_lin_range, ?L_AX2L_erange, ?L_AX2L_lin_test_rel. reflexivity. Qed.

Fixpoint has_round (ts : list (Z * expr)) : bool :=
  match ts with
  | [] => false
  | (_, EAlu ALU_SRL _ (ELit _)) :: _ => true
  | (_, EAlu ALU_AND _ (ELit _)) :: _ => true
  | (_, EAlu ALU_AND (ELit _) _) :: _ => true
  | _ :: rest => has_round rest
  end.
Lemma L_AX2L_has_round : @has_round = @AX2.has_round.
Proof. unfold has_round. reflexivity. Qed.

Fixpoint srl_scale_need (ts : list (Z * expr)) : Z :=
  match ts with
  | [] => 0
  | (k, EAlu ALU_SRL _ (ELit s)) :: rest => Z.max (((CXLF.zm64 s) mod 64) - ctz64 k)%Z (srl_scale_need rest)
  | _ :: rest => srl_scale_need rest
  end.
Lemma L_AX2L_srl_scale_need : @srl_scale_need = @AX2.srl_scale_need.
Proof. unfold srl_scale_need. rewrite ?L_AX2L_ctz64, ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

Definition zcdiv (a b : Z) : Z := (- ((- a) / b))%Z.
Lemma L_AX2L_zcdiv : @zcdiv = @AX2.zcdiv.
Proof. unfold zcdiv. reflexivity. Qed.

Definition lin_srange (kn : list kentry) (e : expr) : option (Z * Z) :=
  let l := lin_of e in
  let j := srl_scale_need (snd l) in
  if (if Z.leb 0 j then Z.leb j 24 else false) then   
    let sc := (CXLF.zpow2 j) in
    let ts := List.map (fun t => ((sc * fst t)%Z, snd t)) (snd l) in
    let '(c2, t2) := srl_expand kn ts in
    let '(c3, t3) := (if has_round t2 then srl_expand kn t2 else (0%Z, t2)) in
    match lin_range (erange kn) (sc * fst l + c2 + c3)%Z t3 with
    | Some (lo', hi') =>
        let lo := zcdiv lo' sc in let hi := (hi' / sc)%Z in
        if (if Z.leb 0 lo then (if Z.leb lo hi then Z.ltb hi two64 else false) else false) then Some (lo, hi) else None
    | None => None
    end
  else None.
Lemma L_AX2L_lin_srange : @lin_srange = @AX2.lin_srange.
Proof. unfold lin_srange. rewrite ?L_AX2L_two64, ?L_AX2L_lin_of, ?L_AX2L_lin_range, ?L_AX2L_erange, ?L_AX2L_srl_expand, ?L_AX2L_has_round, ?L_AX2L_srl_scale_need, ?L_AX2L_zcdiv, ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

Definition lin_nowrapR (kn : list kentry) (e : expr) : bool :=
  let l := lin_of e in
  let '(c2, t2) := srl_expand kn (snd l) in            
  if lin_test kn (fst l + c2)%Z t2 (fun lo hi => (Z.leb 0 lo && Z.ltb hi two64)%bool) then true
  else 
    match lin_srange kn e with Some _ => true | None => false end.
Lemma L_AX2L_lin_nowrapR : @lin_nowrapR = @AX2.lin_nowrapR.
Proof. unfold lin_nowrapR. rewrite ?L_AX2L_two64, ?L_AX2L_lin_of, ?L_AX2L_srl_expand, ?L_AX2L_lin_test, ?L_AX2L_lin_srange. reflexivity. Qed.

Fixpoint mentions_var (v : nat) (e : expr) : bool :=
  match e with
  | ELit _ => false
  | EVar w => CXNAT.eqbF v w
  | EAlu _ a b | EAluw _ a b | EMd _ a b | EMdw _ a b => if mentions_var v a then true else mentions_var v b
  | EExt _ _ _ a => mentions_var v a
  | EBlob _ _ _ _ => false
  end.
Lemma L_AX2L_mentions_var : @mentions_var = @AX2.mentions_var.
Proof. unfold mentions_var. rewrite ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

Fixpoint shares_var (e1 e2 : expr) : bool :=
  match e2 with
  | ELit _ => false
  | EVar w => mentions_var w e1
  | EAlu _ a b | EAluw _ a b | EMd _ a b | EMdw _ a b => if shares_var e1 a then true else shares_var e1 b
  | EExt _ _ _ a => shares_var e1 a
  | EBlob _ _ _ _ => false
  end.
Lemma L_AX2L_shares_var : @shares_var = @AX2.shares_var.
Proof. unfold shares_var. rewrite ?L_AX2L_mentions_var. reflexivity. Qed.

Fixpoint novars (e : expr) : bool :=
  match e with
  | ELit _ => true
  | EVar _ => false
  | EAlu _ a b | EAluw _ a b | EMd _ a b | EMdw _ a b => if novars a then novars b else false
  | EExt _ _ _ a => novars a
  | EBlob _ _ _ _ => true
  end.
Lemma L_AX2L_novars : @novars = @AX2.novars.
Proof. unfold novars. reflexivity. Qed.

Definition related (b1 b2 : expr) : bool :=
  if shares_var b1 b2 then true else novars b2.
Lemma L_AX2L_related : @related = @AX2.related.
Proof. unfold related. rewrite ?L_AX2L_shares_var, ?L_AX2L_novars. reflexivity. Qed.

Definition lin_apart0 (kn : list kentry) (b1 : expr) (k1 n1 : Z) (b2 : expr) (k2 n2 : Z) : bool :=
  (lin_nowrapR kn b1 && lin_nowrapR kn b2 &&
   let l1 := lin_of b1 in let l2 := lin_of b2 in
   lin_test kn (fst l2 + k2 - fst l1 - k1)%Z (lsub_e (snd l2) (snd l1))
            (fun lo hi => (Z.leb n1 lo || Z.leb hi (- n2))%bool))%bool.
Lemma L_AX2L_lin_apart0 : @lin_apart0 = @AX2.lin_apart0.
Proof. unfold lin_apart0. rewrite ?L_AX2L_lin_of, ?L_AX2L_lsub_e, ?L_AX2L_lin_test, ?L_AX2L_lin_nowrapR. reflexivity. Qed.

Definition lin_apart (kn : list kentry) (b1 : expr) (k1 n1 : Z) (b2 : expr) (k2 n2 : Z) : bool :=
  if shares_var b1 b2 then lin_apart0 kn b1 k1 n1 b2 k2 n2 else false.
Lemma L_AX2L_lin_apart : @lin_apart = @AX2.lin_apart.
Proof. unfold lin_apart. rewrite ?L_AX2L_shares_var, ?L_AX2L_lin_apart0. reflexivity. Qed.

Definition zlit64 (z : Z) : Z := if (Z.leb 0 z && Z.ltb z two64)%bool then z else (CXLF.zm64 z)%Z.
Lemma L_AX2L_zlit64 : @zlit64 = @AX2.zlit64.
Proof. unfold zlit64. rewrite ?L_AX2L_two64, ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

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
Lemma L_AX2L_lin_brange : @lin_brange = @AX2.lin_brange.
Proof. unfold lin_brange. rewrite ?L_AX2L_two64, ?L_AX2L_lin_of, ?L_AX2L_lin_range, ?L_AX2L_erange, ?L_AX2L_sum_facts, ?L_AX2L_sum_subst. reflexivity. Qed.

Definition xlo (kn : list kentry) (e : expr) : option Z :=
  match e with
  | ELit z => Some (zlit64 z)
  | _ => match erange kn e with
         | Some (lo, _) => Some lo
         | None => match lin_brange kn e with
                   | Some (lo, _) => Some lo
                   | None => match lin_srange kn e with Some (lo, _) => Some lo | None => None end   
                   end
         end
  end.
Lemma L_AX2L_xlo : @xlo = @AX2.xlo.
Proof. unfold xlo. rewrite ?L_AX2L_erange, ?L_AX2L_lin_srange, ?L_AX2L_zlit64, ?L_AX2L_lin_brange. reflexivity. Qed.

Definition xhi (kn : list kentry) (e : expr) : option Z :=
  match e with
  | ELit z => Some (zlit64 z)
  | _ => match erange kn e with
         | Some (_, hi) => Some hi
         | None => match lin_brange kn e with
                   | Some (_, hi) => Some hi
                   | None => match lin_srange kn e with Some (_, hi) => Some hi | None => None end   
                   end
         end
  end.
Lemma L_AX2L_xhi : @xhi = @AX2.xhi.
Proof. unfold xhi. rewrite ?L_AX2L_erange, ?L_AX2L_lin_srange, ?L_AX2L_zlit64, ?L_AX2L_lin_brange. reflexivity. Qed.

Definition xterms := list (expr * Z).
Lemma L_AX2L_xterms : @xterms = @AX2.xterms.
Proof. unfold xterms. reflexivity. Qed.

Fixpoint xt_nowrap (kn : list kentry) (ts : xterms) : bool :=
  match ts with [] => true | (e, _) :: r => lin_nowrapR kn e && xt_nowrap kn r end.
Lemma L_AX2L_xt_nowrap : @xt_nowrap = @AX2.xt_nowrap.
Proof. unfold xt_nowrap. rewrite ?L_AX2L_lin_nowrapR, ?L_AX2L_xterms. reflexivity. Qed.

Fixpoint xt_const (ts : xterms) : Z :=
  match ts with [] => 0 | (e, k) :: r => (fst (lin_of e) + k + xt_const r)%Z end.
Lemma L_AX2L_xt_const : @xt_const = @AX2.xt_const.
Proof. unfold xt_const. rewrite ?L_AX2L_lin_of, ?L_AX2L_xterms. reflexivity. Qed.

Fixpoint xt_lin (ts : xterms) : list (Z * expr) :=
  match ts with [] => [] | (e, _) :: r => fold_right (fun t acc => lins_e (fst t) (snd t) acc) (xt_lin r) (snd (lin_of e)) end.
Lemma L_AX2L_xt_lin : @xt_lin = @AX2.xt_lin.
Proof. unfold xt_lin. rewrite ?L_AX2L_lin_of, ?L_AX2L_lins_e, ?L_AX2L_xterms. reflexivity. Qed.

Definition lin_ge0_scaled (kn : list kentry) (c : Z) (ts : list (Z * expr)) : bool :=
  let j := srl_scale_need ts in
  if (if Z.ltb 0 j then Z.leb j 24 else false) then
    let sc := (CXLF.zpow2 j) in
    let ts' := List.map (fun t => ((sc * fst t)%Z, snd t)) ts in
    let '(c2, t2) := srl_expand kn ts' in
    let '(c3, t3) := (if has_round t2 then srl_expand kn t2 else (0%Z, t2)) in
    lin_test kn (sc * c + c2 + c3)%Z t3 (fun lo _ => Z.leb 0 lo)
  else false.
Lemma L_AX2L_lin_ge0_scaled : @lin_ge0_scaled = @AX2.lin_ge0_scaled.
Proof. unfold lin_ge0_scaled. rewrite ?L_AX2L_srl_expand, ?L_AX2L_lin_test, ?L_AX2L_has_round, ?L_AX2L_srl_scale_need, ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

Definition lin_test_r (kn : list kentry) (r : option (Z * Z)) (c : Z) (ts : list (Z * expr)) (test : Z -> Z -> bool) : bool :=
  match r with
  | Some (lo, hi) => if test lo hi then true else lin_test_rel kn c ts test
  | None => lin_test_rel kn c ts test
  end.
Lemma L_AX2L_lin_test_r : @lin_test_r = @AX2.lin_test_r.
Proof. unfold lin_test_r. rewrite ?L_AX2L_lin_test_rel. reflexivity. Qed.

Definition lin_hopeless (r : option (Z * Z)) : bool :=
  match r with Some (_, hi) => Z.ltb hi 0 | None => false end.
Lemma L_AX2L_lin_hopeless : @lin_hopeless = @AX2.lin_hopeless.
Proof. unfold lin_hopeless. reflexivity. Qed.

Definition lin_ge0_core (kn : list kentry) (pos neg : xterms) : bool :=
  
  if negb (xt_nowrap kn pos) then false else if negb (xt_nowrap kn neg) then false else
  let r0 := lin_range (erange kn) (xt_const pos - xt_const neg)%Z (lsub_e (xt_lin pos) (xt_lin neg)) in
  if lin_hopeless r0 then false else
   
   (if lin_test_r kn r0 (xt_const pos - xt_const neg)%Z (lsub_e (xt_lin pos) (xt_lin neg)) (fun lo _ => Z.leb 0 lo) then true
    else let '(c2, t2) := srl_expand kn (lsub_e (xt_lin pos) (xt_lin neg)) in
         if lin_test kn (xt_const pos - xt_const neg + c2)%Z t2 (fun lo _ => Z.leb 0 lo) then true
         else 
         if (if has_round t2 then
               let '(c3, t3) := srl_expand kn t2 in
               lin_test kn (xt_const pos - xt_const neg + c2 + c3)%Z t3 (fun lo _ => Z.leb 0 lo)
             else false) then true
         else 
         if lin_ge0_scaled kn (xt_const pos - xt_const neg)%Z (lsub_e (xt_lin pos) (xt_lin neg)) then true
         else 
           (has_round t2 && lin_ge0_scaled kn (xt_const pos - xt_const neg + c2)%Z t2))%bool.
Lemma L_AX2L_lin_ge0_core : @lin_ge0_core = @AX2.lin_ge0_core.
Proof. unfold lin_ge0_core. rewrite ?L_AX2L_lin_range, ?L_AX2L_erange, ?L_AX2L_lsub_e, ?L_AX2L_srl_expand, ?L_AX2L_lin_test, ?L_AX2L_has_round, ?L_AX2L_xterms, ?L_AX2L_xt_nowrap, ?L_AX2L_xt_const, ?L_AX2L_xt_lin, ?L_AX2L_lin_ge0_scaled, ?L_AX2L_lin_test_r, ?L_AX2L_lin_hopeless. reflexivity. Qed.

Fixpoint terms_align (kn : list kentry) (ts : list (Z * expr)) : Z :=
  match ts with
  | [] => 64%Z
  | (k, a) :: rest => Z.min (Z.min (ctz64 (Z.abs k) + ealign kn a) 64)%Z (terms_align kn rest)
  end.
Lemma L_AX2L_terms_align : @terms_align = @AX2.terms_align.
Proof. unfold terms_align. rewrite ?L_AX2L_ctz64, ?L_AX2L_ealign. reflexivity. Qed.

Definition form_align (kn : list kentry) (c : Z) (ts : list (Z * expr)) : Z :=
  Z.max 0 (Z.min (if Z.eqb c 0 then 64%Z else ctz64 (Z.abs c)) (terms_align kn ts)).
Lemma L_AX2L_form_align : @form_align = @AX2.form_align.
Proof. unfold form_align. rewrite ?L_AX2L_ctz64, ?L_AX2L_terms_align. reflexivity. Qed.

Definition lin_ge0 (kn : list kentry) (pos neg : xterms) : bool :=
  if lin_ge0_core kn pos neg then true
  else
    let ts := lsub_e (xt_lin pos) (xt_lin neg) in
    if (has_round ts && xt_nowrap kn pos && xt_nowrap kn neg)%bool then
      let j := Z.min (form_align kn (xt_const pos - xt_const neg)%Z ts) 16 in
      if Z.ltb 0 j then lin_ge0_core kn ((ELit 0, (2 ^ j - 1)%Z) :: pos) neg else false
    else false.
Lemma L_AX2L_lin_ge0 : @lin_ge0 = @AX2.lin_ge0.
Proof. unfold lin_ge0. rewrite ?L_AX2L_lsub_e, ?L_AX2L_has_round, ?L_AX2L_xterms, ?L_AX2L_xt_nowrap, ?L_AX2L_xt_const, ?L_AX2L_xt_lin, ?L_AX2L_lin_ge0_core, ?L_AX2L_form_align. reflexivity. Qed.

Definition xinside0 (kn : list kentry) (b1 : expr) (k1 : Z) (n1 : expr) (b2 : expr) (k2 : Z) (n2 : expr) : bool :=
  if lin_ge0 kn [(b1, k1)] [(b2, k2)] then lin_ge0 kn [(b2, k2); (n2, 0%Z)] [(b1, k1); (n1, 0%Z)] else false.
Lemma L_AX2L_xinside0 : @xinside0 = @AX2.xinside0.
Proof. unfold xinside0. rewrite ?L_AX2L_lin_ge0. reflexivity. Qed.

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
Lemma L_AX2L_xinside_num : @xinside_num = @AX2.xinside_num.
Proof. unfold xinside_num. rewrite ?L_AX2L_base_range, ?L_AX2L_xlo, ?L_AX2L_xhi. reflexivity. Qed.

Definition lsum3 (b : expr) (k : Z) (n : expr) : expr := unlin (ladd (ladd (lin_of b) (lin_of (ELit k))) (lin_of n)).
Lemma L_AX2L_lsum3 : @lsum3 = @AX2.lsum3.
Proof. unfold lsum3. rewrite ?L_AX2L_ladd, ?L_AX2L_lin_of, ?L_AX2L_unlin. reflexivity. Qed.

Definition end_hi (kn : list kentry) (b : expr) (k : Z) (n : expr) (lo1 hi1 h1 : Z) : option Z :=
  match n with
  | ELit _ => None
  | _ => if (if Z.leb 0 (lo1 + k) then Z.ltb (hi1 + k + h1) two64 else false)
         then match lsum3 b k n with
              | ELit z => Some (CXLF.zm64 z)%Z     
              | e => match find_range (facts_of kn) e with
                     | Some (_, ehi) => Some ehi
                     | None => None
                     end
              end
         else None
  end.
Lemma L_AX2L_end_hi : @end_hi = @AX2.end_hi.
Proof. unfold end_hi. rewrite ?L_AX2L_two64, ?L_AX2L_find_range, ?L_AX2L_facts_of, ?L_AX2L_lsum3, ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

Definition xinside_jt (kn : list kentry) (b1 : expr) (k1 : Z) (n1 : expr) (b2 : expr) (k2 : Z) (n2 : expr) : bool :=
  match xlo kn b2, xhi kn b2 with
  | Some lo2, Some hi2 =>
      if Z.eqb lo2 hi2 then
        match base_range kn b1, xhi kn n1, xlo kn n2 with
        | Some (lo1, hi1), Some h1, Some l2 =>
            if Z.leb (lo2 + k2) (lo1 + k1)
            then match end_hi kn b1 k1 n1 lo1 hi1 h1 with Some eh => Z.leb eh (lo2 + k2 + l2) | None => false end
            else false
        | _, _, _ => false
        end
      else false
  | _, _ => false
  end.
Lemma L_AX2L_xinside_jt : @xinside_jt = @AX2.xinside_jt.
Proof. unfold xinside_jt. rewrite ?L_AX2L_base_range, ?L_AX2L_xlo, ?L_AX2L_xhi, ?L_AX2L_end_hi. reflexivity. Qed.

Definition xinside (kn : list kentry) (b1 : expr) (k1 : Z) (n1 : expr) (b2 : expr) (k2 : Z) (n2 : expr) : bool :=
  if shares_var b1 b2 then xinside0 kn b1 k1 n1 b2 k2 n2
  else if novars b2 then (if xinside_num kn b1 k1 n1 b2 k2 n2 then true else xinside_jt kn b1 k1 n1 b2 k2 n2) else false.
Lemma L_AX2L_xinside : @xinside = @AX2.xinside.
Proof. unfold xinside. rewrite ?L_AX2L_shares_var, ?L_AX2L_novars, ?L_AX2L_xinside0, ?L_AX2L_xinside_num, ?L_AX2L_xinside_jt. reflexivity. Qed.

Definition sub_itv (allkn : list kentry) (b : expr) (k n : Z) (c : saddr) (m : expr) : bool :=
  if (if (expr_eqb b (a_base c) && Z.leb (a_off c) k)%bool then
        match xlo allkn m with Some ml => Z.leb (k + n) (a_off c + ml) | None => false end
      else false)
  then true
  else 
    if (Z.leb 0 n && Z.ltb n two64)%bool then xinside allkn b k (ELit n) (a_base c) (a_off c) m else false.
Lemma L_AX2L_sub_itv : @sub_itv = @AX2.sub_itv.
Proof. unfold sub_itv. rewrite ?L_AX2L_expr_eqb, ?L_AX2L_two64, ?L_AX2L_xlo, ?L_AX2L_xinside. reflexivity. Qed.

Fixpoint kdisj_apart (allkn kn : list kentry) (b1 : expr) (k1 n1 : Z) (b2 : expr) (k2 n2 : Z) : bool :=
  match kn with
  | [] => false
  | KDisj c1 m1 c2 m2 :: rest =>
      if (if sub_itv allkn b1 k1 n1 c1 m1 then sub_itv allkn b2 k2 n2 c2 m2 else false) then true
      else if (if sub_itv allkn b1 k1 n1 c2 m2 then sub_itv allkn b2 k2 n2 c1 m1 else false) then true
      else kdisj_apart allkn rest b1 k1 n1 b2 k2 n2
  | _ :: rest => kdisj_apart allkn rest b1 k1 n1 b2 k2 n2
  end.
Lemma L_AX2L_kdisj_apart : @kdisj_apart = @AX2.kdisj_apart.
Proof. unfold kdisj_apart. rewrite ?L_AX2L_sub_itv. reflexivity. Qed.

Definition ranges_apart (kn : list kentry) (b1 : expr) (k1 n1 : Z) (b2 : expr) (k2 n2 : Z) : bool :=
  if (match base_range kn b1, base_range kn b2 with
      | Some (lo1, hi1), Some (lo2, hi2) =>
          (Z.leb (hi1 + k1 + n1) (lo2 + k2) || Z.leb (hi2 + k2 + n2) (lo1 + k1))%bool
      | _, _ => false
      end) then true
  else if kdisj_apart kn kn b1 k1 n1 b2 k2 n2 then true
  else lin_apart kn b1 k1 n1 b2 k2 n2.
Lemma L_AX2L_ranges_apart : @ranges_apart = @AX2.ranges_apart.
Proof. unfold ranges_apart. rewrite ?L_AX2L_base_range, ?L_AX2L_lin_apart, ?L_AX2L_kdisj_apart. reflexivity. Qed.

Definition sub_itv_x (kn : list kentry) (b : expr) (k : Z) (n : expr) (c : saddr) (m : expr) : bool :=
  match n with
  | ELit z => sub_itv kn b k (zlit64 z) c m
  | _ => xinside kn b k n (a_base c) (a_off c) m
  end.
Lemma L_AX2L_sub_itv_x : @sub_itv_x = @AX2.sub_itv_x.
Proof. unfold sub_itv_x. rewrite ?L_AX2L_zlit64, ?L_AX2L_xinside, ?L_AX2L_sub_itv. reflexivity. Qed.

Fixpoint kdisj_apart_x (allkn kn : list kentry) (b1 : expr) (k1 : Z) (n1 : expr) (b2 : expr) (k2 : Z) (n2 : expr) : bool :=
  match kn with
  | [] => false
  | KDisj c1 m1 c2 m2 :: rest =>
      if (if sub_itv_x allkn b1 k1 n1 c1 m1 then sub_itv_x allkn b2 k2 n2 c2 m2 else false) then true
      else if (if sub_itv_x allkn b1 k1 n1 c2 m2 then sub_itv_x allkn b2 k2 n2 c1 m1 else false) then true
      else kdisj_apart_x allkn rest b1 k1 n1 b2 k2 n2
  | _ :: rest => kdisj_apart_x allkn rest b1 k1 n1 b2 k2 n2
  end.
Lemma L_AX2L_kdisj_apart_x : @kdisj_apart_x = @AX2.kdisj_apart_x.
Proof. unfold kdisj_apart_x. rewrite ?L_AX2L_sub_itv_x. reflexivity. Qed.

Definition ranges_apart_x (kn : list kentry) (b1 : expr) (k1 : Z) (n1 : expr) (b2 : expr) (k2 : Z) (n2 : expr) : bool :=
  match n1, n2 with
  | ELit z1, ELit z2 => ranges_apart kn b1 k1 (zlit64 z1) b2 k2 (zlit64 z2)
  | _, _ =>
    if (match base_range kn b1, base_range kn b2, xhi kn n1, xhi kn n2 with
        | Some (lo1, hi1), Some (lo2, hi2), Some h1, Some h2 =>
            if (Z.leb (hi1 + k1 + h1) (lo2 + k2) || Z.leb (hi2 + k2 + h2) (lo1 + k1))%bool then true
            else 
            if match end_hi kn b1 k1 n1 lo1 hi1 h1 with Some e1 => Z.leb e1 (lo2 + k2) | None => false end then true
            else match end_hi kn b2 k2 n2 lo2 hi2 h2 with Some e2 => Z.leb e2 (lo1 + k1) | None => false end
        | _, _, _, _ => false
        end) then true
    else if kdisj_apart_x kn kn b1 k1 n1 b2 k2 n2 then true
    else if negb (shares_var b1 b2) then false
    else if lin_ge0 kn [(b2, k2)] [(b1, k1); (n1, 0%Z)] then true
    else lin_ge0 kn [(b1, k1)] [(b2, k2); (n2, 0%Z)]
  end.
Lemma L_AX2L_ranges_apart_x : @ranges_apart_x = @AX2.ranges_apart_x.
Proof. unfold ranges_apart_x. rewrite ?L_AX2L_base_range, ?L_AX2L_shares_var, ?L_AX2L_zlit64, ?L_AX2L_xhi, ?L_AX2L_lin_ge0, ?L_AX2L_end_hi, ?L_AX2L_ranges_apart, ?L_AX2L_kdisj_apart_x. reflexivity. Qed.

Fixpoint disj_sides (allkn kn : list kentry) (b1 : expr) (k1 n1 : Z) : list (saddr * expr) :=
  match kn with
  | [] => []
  | KDisj c1 m1 c2 m2 :: rest =>
      let r := disj_sides allkn rest b1 k1 n1 in
      let r1 := if sub_itv allkn b1 k1 n1 c2 m2 then (c1, m1) :: r else r in
      if sub_itv allkn b1 k1 n1 c1 m1 then (c2, m2) :: r1 else r1
  | _ :: rest => disj_sides allkn rest b1 k1 n1
  end.
Lemma L_AX2L_disj_sides : @disj_sides = @AX2.disj_sides.
Proof. unfold disj_sides. rewrite ?L_AX2L_sub_itv. reflexivity. Qed.

Fixpoint disj_sides_x (allkn kn : list kentry) (b1 : expr) (k1 : Z) (n1 : expr) : list (saddr * expr) :=
  match kn with
  | [] => []
  | KDisj c1 m1 c2 m2 :: rest =>
      let r := disj_sides_x allkn rest b1 k1 n1 in
      let r1 := if sub_itv_x allkn b1 k1 n1 c2 m2 then (c1, m1) :: r else r in
      if sub_itv_x allkn b1 k1 n1 c1 m1 then (c2, m2) :: r1 else r1
  | _ :: rest => disj_sides_x allkn rest b1 k1 n1
  end.
Lemma L_AX2L_disj_sides_x : @disj_sides_x = @AX2.disj_sides_x.
Proof. unfold disj_sides_x. rewrite ?L_AX2L_sub_itv_x. reflexivity. Qed.

Fixpoint in_sides (allkn : list kentry) (D : list (saddr * expr)) (b2 : expr) (k2 n2 : Z) : bool :=
  match D with
  | [] => false
  | (c, m) :: r => if sub_itv allkn b2 k2 n2 c m then true else in_sides allkn r b2 k2 n2
  end.
Lemma L_AX2L_in_sides : @in_sides = @AX2.in_sides.
Proof. unfold in_sides. rewrite ?L_AX2L_sub_itv. reflexivity. Qed.

Fixpoint in_sides_x (allkn : list kentry) (D : list (saddr * expr)) (b2 : expr) (k2 : Z) (n2 : expr) : bool :=
  match D with
  | [] => false
  | (c, m) :: r => if sub_itv_x allkn b2 k2 n2 c m then true else in_sides_x allkn r b2 k2 n2
  end.
Lemma L_AX2L_in_sides_x : @in_sides_x = @AX2.in_sides_x.
Proof. unfold in_sides_x. rewrite ?L_AX2L_sub_itv_x. reflexivity. Qed.

Definition mk_sprep (kn : list kentry) (b1 : expr) (k1 : Z) (n1 : expr) : sprep :=
  SPrep (base_range kn b1) (xhi kn n1)
        (match n1 with ELit z1 => disj_sides kn kn b1 k1 (zlit64 z1) | _ => [] end)
        (disj_sides_x kn kn b1 k1 n1).
Lemma L_AX2L_mk_sprep : @mk_sprep = @AX2.mk_sprep.
Proof. unfold mk_sprep. rewrite ?L_AX2L_base_range, ?L_AX2L_zlit64, ?L_AX2L_xhi, ?L_AX2L_disj_sides, ?L_AX2L_disj_sides_x. reflexivity. Qed.

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
            if (Z.leb (hi1 + k1 + h1) (lo2 + k2) || Z.leb (hi2 + k2 + h2) (lo1 + k1))%bool then true
            else 
            if match end_hi kn b1 k1 n1 lo1 hi1 h1 with Some e1 => Z.leb e1 (lo2 + k2) | None => false end then true
            else match end_hi kn b2 k2 n2 lo2 hi2 h2 with Some e2 => Z.leb e2 (lo1 + k1) | None => false end
        | _, _, _, _ => false
        end) then true
    else if in_sides_x kn (sp_Dx sp) b2 k2 n2 then true
    else if negb (shares_var b1 b2) then false
    else if lin_ge0 kn [(b2, k2)] [(b1, k1); (n1, 0%Z)] then true
    else lin_ge0 kn [(b1, k1)] [(b2, k2); (n2, 0%Z)]
  end.
Lemma L_AX2L_ranges_apart_p : @ranges_apart_p = @AX2.ranges_apart_p.
Proof. unfold ranges_apart_p. rewrite ?L_AX2L_base_range, ?L_AX2L_shares_var, ?L_AX2L_lin_apart, ?L_AX2L_zlit64, ?L_AX2L_xhi, ?L_AX2L_lin_ge0, ?L_AX2L_end_hi, ?L_AX2L_in_sides, ?L_AX2L_in_sides_x. reflexivity. Qed.

Arguments PTLeaf {A}.
Arguments PTNode {A} _ _ _.
Fixpoint pt_get {A} (t : ptree A) (k : positive) {struct k} : option A :=
  match t with
  | PTLeaf => None
  | PTNode l o r => match k with xH => o | xO k' => pt_get l k' | xI k' => pt_get r k' end
  end.
Lemma L_AX2L_pt_get : @pt_get = @AX2.pt_get.
Proof. unfold pt_get. reflexivity. Qed.

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
Lemma L_AX2L_pt_set : @pt_set = @AX2.pt_set.
Proof. unfold pt_set. reflexivity. Qed.

Fixpoint zbytes_le_to_Z (bs : list Z) : Z :=
  match bs with
  | [] => 0
  | b :: rest => Z.lor b (Z.shiftl (zbytes_le_to_Z rest) 8)
  end.
Lemma L_AX2L_zbytes_le_to_Z : @zbytes_le_to_Z = @AX2.zbytes_le_to_Z.
Proof. unfold zbytes_le_to_Z. reflexivity. Qed.

Definition lit_of_bytes (sx : bool) (n : nat) (bs : list Z) : expr :=
  ELit (let u := zbytes_le_to_Z bs in if sx then bv_swrap (8 * N.of_nat n) u else u).
Lemma L_AX2L_lit_of_bytes : @lit_of_bytes = @AX2.lit_of_bytes.
Proof. unfold lit_of_bytes. rewrite ?L_AX2L_zbytes_le_to_Z. reflexivity. Qed.

Fixpoint log_byte_lit (log : list sentry) (rb : expr) (rk : Z) : option Z :=
  match log with
  | [] => None
  | SE (SA kb kk) w v :: rest =>
      match rel_lit rb rk 1 kb kk (Z.of_nat w) with
      | RInside d => match v with
                     | ELit z => Some (((CXLF.zm64 z) / 2 ^ (8 * d)) mod 256)%Z
                     | _ => None
                     end
      | RDisjoint => log_byte_lit rest rb rk
      | _ => None
      end
  end.
Lemma L_AX2L_log_byte_lit : @log_byte_lit = @AX2.log_byte_lit.
Proof. unfold log_byte_lit. rewrite ?L_AX2L_rel_lit, ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

Fixpoint log_bytes_lit (log : list sentry) (rb : expr) (rk : Z) (n : nat) : option (list Z) :=
  match n with
  | O => Some []
  | S n' => match log_byte_lit log rb rk, log_bytes_lit log rb (rk + 1) n' with
            | Some b, Some r => Some (b :: r)
            | _, _ => None
            end
  end.
Lemma L_AX2L_log_bytes_lit : @log_bytes_lit = @AX2.log_bytes_lit.
Proof. unfold log_bytes_lit. rewrite ?L_AX2L_log_byte_lit. reflexivity. Qed.

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
Lemma L_AX2L_log_lookup : @log_lookup = @AX2.log_lookup.
Proof. unfold log_lookup. rewrite ?L_AX2L_mkExt, ?L_AX2L_rel_lit, ?L_AX2L_elen, ?L_AX2L_ranges_apart, ?L_AX2L_lit_of_bytes, ?L_AX2L_log_bytes_lit. reflexivity. Qed.

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
Lemma L_AX2L_img_bytes : @img_bytes = @AX2.img_bytes.
Proof. unfold img_bytes. reflexivity. Qed.

Definition fill_lit (sx : bool) (n : nat) (c : Z) : expr :=
  lit_of_bytes sx n (repeat (c mod 256)%Z n).
Lemma L_AX2L_fill_lit : @fill_lit = @AX2.fill_lit.
Proof. unfold fill_lit. rewrite ?L_AX2L_lit_of_bytes. reflexivity. Qed.

Fixpoint know_byte_lit (segs : list Segment) (kn : list kentry) (rb : expr) (rk : Z) : option Z :=
  match kn with
  | [] => None
  | K :: rest =>
      match K with
      | KWord (SA kb kk) w (ELit z) =>
          match rel_lit rb rk 1 kb kk (Z.of_nat w) with
          | RInside d => Some (((CXLF.zm64 z) / 2 ^ (8 * d)) mod 256)%Z
          | _ => know_byte_lit segs rest rb rk
          end
      | KZero (SA kb kk) (ELit l0) =>
          match rel_lit rb rk 1 kb kk (CXLF.zm64 l0)%Z with
          | RInside _ => Some 0%Z
          | _ => know_byte_lit segs rest rb rk
          end
      | KFill (SA kb kk) (ELit l0) c =>
          match rel_lit rb rk 1 kb kk (CXLF.zm64 l0)%Z with
          | RInside _ => Some (c mod 256)%Z
          | _ => know_byte_lit segs rest rb rk
          end
      | KImg lo hi =>
          match rb with
          | ELit 0 =>
              if (Z.leb lo rk && Z.ltb rk hi)%bool then
                match seg_rom segs (Z_to_bv 64 rk) with
                | Some b => Some (bv_unsigned b)
                | None => None            
                end
              else know_byte_lit segs rest rb rk
          | _ => know_byte_lit segs rest rb rk
          end
      | _ => know_byte_lit segs rest rb rk
      end
  end.
Lemma L_AX2L_know_byte_lit : @know_byte_lit = @AX2.know_byte_lit.
Proof. unfold know_byte_lit. rewrite ?L_AX2L_rel_lit, ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

Fixpoint know_bytes_lit (segs : list Segment) (kn : list kentry) (rb : expr) (rk : Z) (n : nat)
  : option (list Z) :=
  match n with
  | O => Some []
  | S n' => match know_byte_lit segs kn rb rk, know_bytes_lit segs kn rb (rk + 1) n' with
            | Some b, Some r => Some (b :: r)
            | _, _ => None
            end
  end.
Lemma L_AX2L_know_bytes_lit : @know_bytes_lit = @AX2.know_bytes_lit.
Proof. unfold know_bytes_lit. rewrite ?L_AX2L_know_byte_lit. reflexivity. Qed.

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
              match rel_lit rb rk (Z.of_nat n) kb kk (CXLF.zm64 l0)%Z with
              | RInside _ => LHit (ELit 0) acc hints
              | RDisjoint | RPartial => know_lookup segs rest rb rk n sx hints acc
              | RUnknown =>
                  
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
          
          let hit := fill_lit sx n c in
          match len with
          | ELit l0 =>
              match rel_lit rb rk (Z.of_nat n) kb kk (CXLF.zm64 l0)%Z with
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
      | KUnk _ _ => know_lookup segs rest rb rk n sx hints acc   
      | KBlob (SA kb kk) len k =>
          if expr_eqb rb kb then
            
            if Z.leb kk rk then
              match len with
              | ELit l0 =>
                  if Z.leb (rk + Z.of_nat n) (kk + (CXLF.zm64 l0)%Z)
                  then LHit (EBlob sx k (rk - kk) n) acc hints
                  else if Z.leb (kk + (CXLF.zm64 l0)%Z) rk then know_lookup segs rest rb rk n sx hints acc
                  else LStuck
              | _ =>
                  
                  if match erange allkn len with   
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
Lemma L_AX2L_know_lookupA0 : @know_lookupA0 = @AX2.know_lookupA0.
Proof. unfold know_lookupA0. rewrite ?L_AX2L_expr_eqb, ?L_AX2L_mkExt, ?L_AX2L_rel_lit, ?L_AX2L_elen, ?L_AX2L_erange, ?L_AX2L_xinside, ?L_AX2L_lit_of_bytes, ?L_AX2L_img_bytes, ?L_AX2L_fill_lit, ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

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
Lemma L_AX2L_know_lookupA : @know_lookupA = @AX2.know_lookupA.
Proof. unfold know_lookupA. rewrite ?L_AX2L_lit_of_bytes, ?L_AX2L_know_bytes_lit, ?L_AX2L_know_lookupA0. reflexivity. Qed.

Definition know_lookup (segs : list Segment) (kn : list kentry) (rb : expr) (rk : Z)
         (n : nat) (sx : bool) (hints : list bool) (acc : list sidecond) : lres :=
  know_lookupA kn segs kn rb rk n sx hints acc.
Lemma L_AX2L_know_lookup : @know_lookup = @AX2.know_lookup.
Proof. unfold know_lookup. rewrite ?L_AX2L_know_lookupA. reflexivity. Qed.

Fixpoint coeffs_divk (kn : list kentry) (m : Z) (ts : list (Z * expr)) : bool :=
  match ts with
  | [] => true
  | (k, a) :: rest => ((Z.eqb (k mod m) 0 || Z.eqb ((k * 2 ^ ealign kn a) mod m) 0) && coeffs_divk kn m rest)%bool
  end.
Lemma L_AX2L_coeffs_divk : @coeffs_divk = @AX2.coeffs_divk.
Proof. unfold coeffs_divk. rewrite ?L_AX2L_ealign. reflexivity. Qed.

Definition lin_lowbits_kn (kn : list kentry) (e : expr) (k : Z) : option Z :=
  let l := lin_of e in
  if coeffs_divk kn (CXLF.zpow2 k) (snd l) then Some ((fst l) mod 2 ^ k)%Z
  else pageup_low e (CXLF.zpow2 k).
Lemma L_AX2L_lin_lowbits_kn : @lin_lowbits_kn = @AX2.lin_lowbits_kn.
Proof. unfold lin_lowbits_kn. rewrite ?L_AX2L_lin_of, ?L_AX2L_pageup_low, ?L_AX2L_coeffs_divk, ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

Fixpoint ldiv_terms (m : Z) (ts : list (Z * expr)) : list (Z * expr) :=
  match ts with
  | [] => []
  | (k, a) :: rest => ((k / m)%Z, a) :: ldiv_terms m rest
  end.
Lemma L_AX2L_ldiv_terms : @ldiv_terms = @AX2.ldiv_terms.
Proof. unfold ldiv_terms. reflexivity. Qed.

Fixpoint lsplit_divc (m : Z) (ts : list (Z * expr)) : list (Z * expr) * list (Z * expr) :=
  match ts with
  | [] => ([], [])
  | (k, a) :: rest =>
      let (d, r) := lsplit_divc m rest in
      if Z.eqb (k mod m) 0 then ((k, a) :: d, r) else (d, (k, a) :: r)
  end.
Lemma L_AX2L_lsplit_divc : @lsplit_divc = @AX2.lsplit_divc.
Proof. unfold lsplit_divc. reflexivity. Qed.

Definition lin_nowrap_l (kn : list kentry) (c : Z) (ts : list (Z * expr)) : bool :=
  match lin_range (erange kn) c ts with
  | Some (lo, hi) => (Z.leb 0 lo && Z.ltb hi two64)%bool
  | None => false
  end.
Lemma L_AX2L_lin_nowrap_l : @lin_nowrap_l = @AX2.lin_nowrap_l.
Proof. unfold lin_nowrap_l. rewrite ?L_AX2L_two64, ?L_AX2L_lin_range, ?L_AX2L_erange. reflexivity. Qed.

Definition srl_split_span : Z := 64.
Lemma L_AX2L_srl_split_span : @srl_split_span = @AX2.srl_split_span.
Proof. unfold srl_split_span. reflexivity. Qed.

Definition mkSrl (kn : list kentry) (a : expr) (s : Z) : expr :=
  let l := lin_of a in
  let m := (CXLF.zpow2 s) in
  if (negb (lin_trivial l) && coeffs_div m (snd l) && lin_nowrap kn a)%bool
  then unlin ((fst l / m)%Z, ldiv_terms m (snd l))     
  else
    
    match (if (negb (lin_trivial l) && lin_nowrap kn a)%bool then lsplit_divc m (snd l) else ([], [])) with
    | ((_ :: _) as dts, (_ :: _) as rts) =>
        match (if lin_nowrap_l kn (fst l) rts then erange kn (unlin (fst l, rts)) else None) with
        | Some (lo, hi) =>
            if Z.eqb (lo / m) (hi / m) then unlin ((lo / m)%Z, ldiv_terms m dts)
            else if Z.leb (hi / m - lo / m) srl_split_span
            then unlin (ladd (0%Z, ldiv_terms m dts) (0%Z, [(1%Z, EAlu ALU_SRL (unlin (fst l, rts)) (ELit s))]))
            else mkAlu ALU_SRL a (ELit s)
        | None => mkAlu ALU_SRL a (ELit s)
        end
    | _ => mkAlu ALU_SRL a (ELit s)
    end.
Lemma L_AX2L_mkSrl : @mkSrl = @AX2.mkSrl.
Proof. unfold mkSrl. rewrite ?L_AX2L_ladd, ?L_AX2L_lin_of, ?L_AX2L_unlin, ?L_AX2L_coeffs_div, ?L_AX2L_mkAlu, ?L_AX2L_lin_trivial, ?L_AX2L_erange, ?L_AX2L_lin_nowrap, ?L_AX2L_ldiv_terms, ?L_AX2L_lsplit_divc, ?L_AX2L_lin_nowrap_l, ?L_AX2L_srl_split_span, ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

Fixpoint lowbits (kn : list kentry) (e : expr) (j : Z) {struct e} : option Z :=
  let m := (CXLF.zpow2 j) in
  let dflt := if Z.leb j (ealign kn e) then Some 0%Z else lin_lowbits_kn kn e j in
  match e with
  | ELit z => Some ((CXLF.zm64 z) mod m)%Z
  | EAlu ALU_AND a (ELit c) =>
      if Z.eqb ((CXLF.zm64 c) mod m) 0 then Some 0%Z else
      match lowbits kn a j with Some v => Some (Z.land v ((CXLF.zm64 c) mod m)) | None => dflt end
  | EAlu ALU_OR a (ELit c) =>
      match lowbits kn a j with Some v => Some (Z.lor v ((CXLF.zm64 c) mod m)) | None => dflt end
  | EAlu ALU_XOR a (ELit c) =>
      match lowbits kn a j with Some v => Some (Z.lxor v ((CXLF.zm64 c) mod m)) | None => dflt end
  | EAlu ALU_ADD a b =>
      match lowbits kn a j, lowbits kn b j with Some x, Some y => Some ((x + y) mod m)%Z | _, _ => dflt end
  | EAlu ALU_SUB a b =>
      match lowbits kn a j, lowbits kn b j with Some x, Some y => Some ((x - y) mod m)%Z | _, _ => dflt end
  | EMd M_MUL (ELit c) a =>
      if Z.eqb ((CXLF.zm64 c) mod m) 0 then Some 0%Z else
      match lowbits kn a j with Some v => Some ((c * v) mod m)%Z | None => dflt end
  | _ => dflt
  end.
Lemma L_AX2L_lowbits : @lowbits = @AX2.lowbits.
Proof. unfold lowbits. rewrite ?L_AX2L_ealign, ?L_AX2L_lin_lowbits_kn, ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

Fixpoint lsplit_div (kn : list kentry) (m : Z) (ts : list (Z * expr)) : list (Z * expr) * list (Z * expr) :=
  match ts with
  | [] => ([], [])
  | (k, a) :: rest =>
      let (d, r) := lsplit_div kn m rest in
      if (Z.eqb (k mod m) 0 || Z.eqb ((k * 2 ^ ealign kn a) mod m) 0)%bool then ((k, a) :: d, r) else (d, (k, a) :: r)
  end.
Lemma L_AX2L_lsplit_div : @lsplit_div = @AX2.lsplit_div.
Proof. unfold lsplit_div. rewrite ?L_AX2L_ealign. reflexivity. Qed.

Definition and_high_split (kn : list kentry) (bk : expr) (j c : Z) (dts rts : list (Z * expr)) : expr :=
  let m := (CXLF.zpow2 j) in
  let cA := (c - c mod m)%Z in
  let r := unlin ((c mod m)%Z, rts) in
  match erange kn r with
  | Some (lo, hi) =>
      if Z.eqb (lo / m) (hi / m) then unlin ((cA + (lo / m) * m)%Z, dts)
      else mkAlu ALU_ADD (unlin (cA, dts)) (mkAlu ALU_AND r bk)
  | None => mkAlu ALU_ADD (unlin (cA, dts)) (mkAlu ALU_AND r bk)
  end.
Lemma L_AX2L_and_high_split : @and_high_split = @AX2.and_high_split.
Proof. unfold and_high_split. rewrite ?L_AX2L_unlin, ?L_AX2L_mkAlu, ?L_AX2L_erange, ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

Definition and_low_split (kn : list kentry) (bk : expr) (j c : Z) (rts : list (Z * expr)) : expr :=
  let m := (CXLF.zpow2 j) in
  let r := unlin ((c mod m)%Z, rts) in
  match erange kn r with
  | Some (lo, hi) =>
      if Z.eqb (lo / m) (hi / m) then unlin ((c mod m - (lo / m) * m)%Z, rts)
      else mkAlu ALU_AND r bk
  | None => mkAlu ALU_AND r bk
  end.
Lemma L_AX2L_and_low_split : @and_low_split = @AX2.and_low_split.
Proof. unfold and_low_split. rewrite ?L_AX2L_unlin, ?L_AX2L_mkAlu, ?L_AX2L_erange, ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

Definition mkAnd0 (kn : list kentry) (a b : expr) : expr :=
  match b with
  | ELit k =>
      let k' := (CXLF.zm64 k)%Z in
      let j := Z.log2 (two64 - k') in
      if (Z.eqb (two64 - k') (CXLF.zpow2 j) && Z.ltb j 64)%bool then
        
        (if Z.leb j (ealign kn a) then a
         else let l := lin_of a in
              if (negb (lin_trivial l) && coeffs_divk kn (CXLF.zpow2 j) (snd l))%bool
              then unlin ((fst l - (fst l) mod 2 ^ j)%Z, snd l)
              else 
                match (if lin_trivial l then ([], snd l) else lsplit_div kn (CXLF.zpow2 j) (snd l)) with
                | ((_ :: _) as dts, (_ :: _) as rts) => and_high_split kn b j (fst l) dts rts
                | _ => 
                       mkMd M_MUL (ELit (CXLF.zpow2 j)) (mkSrl kn a j)
                end)
      else
        let j2 := Z.log2 (k' + 1) in
        if (Z.eqb (k' + 1) (CXLF.zpow2 j2) && Z.ltb j2 64)%bool then
          
          (if Z.leb j2 (ealign kn a) then ELit 0
           else match lowbits kn a j2 with        
           | Some v => ELit v
           | None =>
           if lin_trivial (lin_of a) then mkAlu ALU_AND a b
           else match lin_lowbits_kn kn a j2 with
                | Some v => ELit v
                | None => 
                    match lsplit_div kn (CXLF.zpow2 j2) (snd (lin_of a)) with
                    | (_ :: _, (_ :: _) as rts) => and_low_split kn b j2 (fst (lin_of a)) rts
                    | _ => mkAlu ALU_AND a b
                    end
                end
           end)
        else 
          let j3 := (Z.log2 k' + 1)%Z in
          if (Z.ltb 0 k' && Z.leb j3 64 && negb (lin_trivial (lin_of a)))%bool then
            match lin_lowbits_kn kn a j3 with
            | Some v => ELit (Z.land v k')
            | None => mkAlu ALU_AND a b
            end
          else mkAlu ALU_AND a b
  | _ => mkAlu ALU_AND a b
  end.
Lemma L_AX2L_mkAnd0 : @mkAnd0 = @AX2.mkAnd0.
Proof. unfold mkAnd0. rewrite ?L_AX2L_two64, ?L_AX2L_lin_of, ?L_AX2L_unlin, ?L_AX2L_mkAlu, ?L_AX2L_mkMd, ?L_AX2L_lin_trivial, ?L_AX2L_ealign, ?L_AX2L_coeffs_divk, ?L_AX2L_lin_lowbits_kn, ?L_AX2L_mkSrl, ?L_AX2L_lowbits, ?L_AX2L_lsplit_div, ?L_AX2L_and_high_split, ?L_AX2L_and_low_split, ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

Definition narrow_mask (kn : list kentry) (a : expr) (k' : Z) : option Z :=
  let i := ctz64 k' in
  let m := (k' + 2 ^ i)%Z in
  let j := Z.log2 m in
  if (Z.ltb 0 k' && Z.eqb m (CXLF.zpow2 j) && Z.ltb j 64)%bool then
    match xhi kn a with
    | Some h => if Z.ltb h (CXLF.zpow2 j) then Some (two64 - 2 ^ i)%Z else None
    | None => None
    end
  else None.
Lemma L_AX2L_narrow_mask : @narrow_mask = @AX2.narrow_mask.
Proof. unfold narrow_mask. rewrite ?L_AX2L_two64, ?L_AX2L_ctz64, ?L_AX2L_xhi, ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

Definition mkAnd (kn : list kentry) (a b : expr) : expr :=
  match b with
  | ELit k =>
      match narrow_mask kn a (CXLF.zm64 k)%Z with
      | Some m => mkAnd0 kn a (ELit m)
      | None => mkAnd0 kn a b
      end
  | _ => mkAnd0 kn a b
  end.
Lemma L_AX2L_mkAnd : @mkAnd = @AX2.mkAnd.
Proof. unfold mkAnd. rewrite ?L_AX2L_mkAnd0, ?L_AX2L_narrow_mask, ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

Definition mkAndK (kn : list kentry) (a b : expr) : expr :=
  match a, b with
  | EAlu ALU_AND x (ELit m1), ELit k => mkAnd kn x (ELit (Z.land (CXLF.zm64 m1) (CXLF.zm64 k))%Z)
  | EMd M_MUL (ELit m) (EAlu ALU_SRL x (ELit i)), ELit k =>
      
      let i' := ((CXLF.zm64 i) mod 64)%Z in
      if Z.eqb (CXLF.zm64 m) (CXLF.zpow2 i') then mkAnd kn x (ELit (Z.land (two64 - 2 ^ i') (CXLF.zm64 k))%Z)
      else mkAnd kn a b
  | _, _ => mkAnd kn a b
  end.
Lemma L_AX2L_mkAndK : @mkAndK = @AX2.mkAndK.
Proof. unfold mkAndK. rewrite ?L_AX2L_two64, ?L_AX2L_mkAnd, ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

Definition or_disjoint (kn : list kentry) (a b : expr) : bool :=
  match erange kn b with
  | Some (lo, hi) => (Z.leb 0 lo && Z.ltb hi (2 ^ (ealign kn a)))%bool
  | None => false
  end.
Lemma L_AX2L_or_disjoint : @or_disjoint = @AX2.or_disjoint.
Proof. unfold or_disjoint. rewrite ?L_AX2L_erange, ?L_AX2L_ealign. reflexivity. Qed.

Definition mkOr (kn : list kentry) (a b : expr) : expr :=
  match is_lit a, is_lit b with
  | Some x, Some y => ELit (zalu ALU_OR x y)
  | _, _ =>
      if or_disjoint kn a b then mkAlu ALU_ADD a b
      else if or_disjoint kn b a then mkAlu ALU_ADD a b
      else 
           match b with
           | ELit c => mkAlu ALU_ADD (mkAndK kn a (ELit (Z.lnot (CXLF.zm64 c)))) (ELit c)
           | _ => match a with
                  | ELit c => mkAlu ALU_ADD (mkAndK kn b (ELit (Z.lnot (CXLF.zm64 c)))) (ELit c)
                  | _ => EAlu ALU_OR a b
                  end
           end
  end.
Lemma L_AX2L_mkOr : @mkOr = @AX2.mkOr.
Proof. unfold mkOr. rewrite ?L_AX2L_zalu, ?L_AX2L_is_lit, ?L_AX2L_mkAlu, ?L_AX2L_mkAndK, ?L_AX2L_or_disjoint, ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

Fixpoint closedb (e : expr) : bool :=
  match e with
  | ELit _ => true
  | EVar _ => false
  | EAlu _ a b | EAluw _ a b | EMd _ a b | EMdw _ a b => closedb a && closedb b
  | EExt _ _ _ a => closedb a
  | EBlob _ _ _ _ => false
  end.
Lemma L_AX2L_closedb : @closedb = @AX2.closedb.
Proof. unfold closedb. reflexivity. Qed.

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
Lemma L_AX2L_esubst : @esubst = @AX2.esubst.
Proof. unfold esubst. rewrite ?L_AX2L_expr_eqb. reflexivity. Qed.

Fixpoint eval_closed (e : expr) : option Z :=
  match e with
  | ELit z => Some (CXLF.zm64 z)%Z
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
Lemma L_AX2L_eval_closed : @eval_closed = @AX2.eval_closed.
Proof. unfold eval_closed. rewrite ?L_AX2L_zalu, ?L_AX2L_zaluw, ?L_AX2L_zmd, ?L_AX2L_zmdw, ?L_AX2L_zext_lit, ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

Fixpoint subexprs (e : expr) : list expr :=
  match e with
  | EAlu _ a b | EAluw _ a b | EMd _ a b | EMdw _ a b => subexprs a ++ subexprs b ++ [e]
  | EExt _ _ _ a => subexprs a ++ [e]
  | _ => [e]
  end.
Lemma L_AX2L_subexprs : @subexprs = @AX2.subexprs.
Proof. unfold subexprs. reflexivity. Qed.

Fixpoint all_eval_to (s e : expr) (v lo : Z) (cnt : nat) : bool :=
  match cnt with
  | O => true
  | S c => match eval_closed (esubst s (ELit lo) e) with
           | Some w => if Z.eqb w v then all_eval_to s e v (lo + 1) c else false   
           | None => false
           end
  end.
Lemma L_AX2L_all_eval_to : @all_eval_to = @AX2.all_eval_to.
Proof. unfold all_eval_to. rewrite ?L_AX2L_esubst, ?L_AX2L_eval_closed. reflexivity. Qed.

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
                      | Some x => Some (zext_fast sx lo n x) | None => None end   
  | EBlob _ _ _ _ => None
  end.
Lemma L_AX2L_evalS : @evalS = @AX2.evalS.
Proof. unfold evalS. rewrite ?L_AX2L_expr_eqb, ?L_AX2L_zmdw, ?L_AX2L_wrap64, ?L_AX2L_zfast, ?L_AX2L_zfastw, ?L_AX2L_zfastm, ?L_AX2L_zext_fast. reflexivity. Qed.

Fixpoint all_eval_toS (s e : expr) (v lo : Z) (cnt : nat) : bool :=
  match cnt with
  | O => true
  | S c => match evalS s (wrap64 lo) e with
           | Some w => if Z.eqb w v then all_eval_toS s e v (lo + 1) c else false
           | None => false
           end
  end.
Lemma L_AX2L_all_eval_toS : @all_eval_toS = @AX2.all_eval_toS.
Proof. unfold all_eval_toS. rewrite ?L_AX2L_wrap64, ?L_AX2L_evalS. reflexivity. Qed.

Definition probeS (s e : expr) (v z : Z) : bool :=
  match evalS s (wrap64 z) e with Some w => Z.eqb w v | None => false end.
Lemma L_AX2L_probeS : @probeS = @AX2.probeS.
Proof. unfold probeS. rewrite ?L_AX2L_wrap64, ?L_AX2L_evalS. reflexivity. Qed.

Fixpoint memE (e : expr) (l : list expr) : bool :=
  match l with [] => false | x :: r => if expr_eqb e x then true else memE e r end.
Lemma L_AX2L_memE : @memE = @AX2.memE.
Proof. unfold memE. rewrite ?L_AX2L_expr_eqb. reflexivity. Qed.

Fixpoint nubE_acc (l acc : list expr) : list expr :=
  match l with
  | [] => []
  | x :: r => if memE x acc then nubE_acc r acc else x :: nubE_acc r (x :: acc)
  end.
Lemma L_AX2L_nubE_acc : @nubE_acc = @AX2.nubE_acc.
Proof. unfold nubE_acc. rewrite ?L_AX2L_memE. reflexivity. Qed.

Definition nubE (l : list expr) : list expr := nubE_acc l [].
Lemma L_AX2L_nubE : @nubE = @AX2.nubE.
Proof. unfold nubE. rewrite ?L_AX2L_nubE_acc. reflexivity. Qed.

Definition conc_limit : Z := 4096.
Lemma L_AX2L_conc_limit : @conc_limit = @AX2.conc_limit.
Proof. unfold conc_limit. reflexivity. Qed.

Fixpoint evalS_def (s e : expr) : bool :=
  if expr_eqb e s then true else
  match e with
  | ELit _ => true
  | EVar _ => false
  | EAlu _ a b | EAluw _ a b | EMd _ a b | EMdw _ a b => if evalS_def s a then evalS_def s b else false
  | EExt _ _ _ a => evalS_def s a
  | EBlob _ _ _ _ => false
  end.
Lemma L_AX2L_evalS_def : @evalS_def = @AX2.evalS_def.
Proof. unfold evalS_def. rewrite ?L_AX2L_expr_eqb. reflexivity. Qed.

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
Lemma L_AX2L_conc_try : @conc_try = @AX2.conc_try.
Proof. unfold conc_try. rewrite ?L_AX2L_wrap64, ?L_AX2L_erange, ?L_AX2L_closedb, ?L_AX2L_evalS, ?L_AX2L_all_eval_toS, ?L_AX2L_probeS, ?L_AX2L_conc_limit, ?L_AX2L_evalS_def. reflexivity. Qed.

Fixpoint conc_try_ref (kn : list kentry) (e : expr) (cands : list expr) : option Z :=
  match cands with
  | [] => None
  | s :: rest =>
      if closedb s then conc_try_ref kn e rest else
      match erange kn s with
      | Some (lo, hi) =>
          if Z.leb (hi - lo) conc_limit then
            match evalS s (wrap64 lo) e with
            | Some v =>
                if (if Z.ltb hi lo then true
                     else if probeS s e v hi then probeS s e v (lo + (hi - lo) / 2)%Z else false) then
                  if all_eval_toS s e v lo (Z.to_nat (hi - lo + 1)) then Some v
                  else conc_try_ref kn e rest
                else conc_try_ref kn e rest
            | None => conc_try_ref kn e rest
            end
          else conc_try_ref kn e rest
      | None => conc_try_ref kn e rest
      end
  end.
Lemma L_AX2L_conc_try_ref : @conc_try_ref = @AX2.conc_try_ref.
Proof. unfold conc_try_ref. rewrite ?L_AX2L_wrap64, ?L_AX2L_erange, ?L_AX2L_closedb, ?L_AX2L_evalS, ?L_AX2L_all_eval_toS, ?L_AX2L_probeS, ?L_AX2L_conc_limit. reflexivity. Qed.

Definition concretize (kn : list kentry) (e : expr) : option Z :=
  if closedb e then eval_closed e else conc_try kn e (nubE (subexprs e)).
Lemma L_AX2L_concretize : @concretize = @AX2.concretize.
Proof. unfold concretize. rewrite ?L_AX2L_closedb, ?L_AX2L_eval_closed, ?L_AX2L_subexprs, ?L_AX2L_nubE, ?L_AX2L_conc_try. reflexivity. Qed.

Definition foldK (kn : list kentry) (e : expr) : expr :=
  match e with
  | ELit _ => e
  | _ => match erange kn e with
         | Some (lo, hi) => if Z.eqb lo hi then ELit lo
                            else match concretize kn e with Some v => ELit v | None => e end
         | None => match concretize kn e with Some v => ELit v | None => e end   
         end
  end.
Lemma L_AX2L_foldK : @foldK = @AX2.foldK.
Proof. unfold foldK. rewrite ?L_AX2L_erange, ?L_AX2L_concretize. reflexivity. Qed.

Definition lit_branch (c : branch_cond) (x y : Z) : bool :=
  branch_taken c (Z_to_bv 64 x) (Z_to_bv 64 y).
Lemma L_AX2L_lit_branch : @lit_branch = @AX2.lit_branch.
Proof. unfold lit_branch. reflexivity. Qed.

Definition cond_on_eq (c : branch_cond) : bool :=
  match c with
  | BC_EQ => true | BC_NE => false | BC_LT => false | BC_GE => true
  | BC_LTU => false | BC_GEU => true
  end.
Lemma L_AX2L_cond_on_eq : @cond_on_eq = @AX2.cond_on_eq.
Proof. unfold cond_on_eq. reflexivity. Qed.

Definition itv_ltu (al ah bl bh : Z) : option bool :=
  if Z.ltb ah bl then Some true else if Z.leb bh al then Some false else None.
Lemma L_AX2L_itv_ltu : @itv_ltu = @AX2.itv_ltu.
Proof. unfold itv_ltu. reflexivity. Qed.

Definition itv_lts (al ah bl bh : Z) : option bool :=
  let h := (CXLF.p63)%Z in
  if ((Z.ltb ah h && Z.ltb bh h) || (Z.leb h al && Z.leb h bl))%bool then itv_ltu al ah bl bh
  else if (Z.leb h al && Z.ltb bh h)%bool then Some true
  else if (Z.ltb ah h && Z.leb h bl)%bool then Some false
  else None.
Lemma L_AX2L_itv_lts : @itv_lts = @AX2.itv_lts.
Proof. unfold itv_lts. rewrite ?L_AX2L_itv_ltu, ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

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
Lemma L_AX2L_range_branch : @range_branch = @AX2.range_branch.
Proof. unfold range_branch. rewrite ?L_AX2L_itv_ltu, ?L_AX2L_itv_lts. reflexivity. Qed.

Fixpoint lin_ctz (ts : list (Z * expr)) : Z :=
  match ts with
  | [] => 64
  | (k, _) :: rest => Z.min (ctz64 k) (lin_ctz rest)
  end.
Lemma L_AX2L_lin_ctz : @lin_ctz = @AX2.lin_ctz.
Proof. unfold lin_ctz. rewrite ?L_AX2L_ctz64. reflexivity. Qed.

Definition lowbits_width (kn : list kentry) (e : expr) : Z :=
  Z.max (lin_ctz (snd (lin_of e))) (ealign kn e).
Lemma L_AX2L_lowbits_width : @lowbits_width = @AX2.lowbits_width.
Proof. unfold lowbits_width. rewrite ?L_AX2L_lin_of, ?L_AX2L_ealign, ?L_AX2L_lin_ctz. reflexivity. Qed.

Definition lowbits_neq (kn : list kentry) (a b : expr) : bool :=
  let j := Z.min (Z.min (lowbits_width kn a) (lowbits_width kn b)) 64 in
  if Z.ltb 0 j then
    match lowbits kn a j, lowbits kn b j with
    | Some x, Some y => negb (Z.eqb x y)
    | _, _ => false
    end
  else false.
Lemma L_AX2L_lowbits_neq : @lowbits_neq = @AX2.lowbits_neq.
Proof. unfold lowbits_neq. rewrite ?L_AX2L_lowbits, ?L_AX2L_lowbits_width. reflexivity. Qed.

Definition lowbits_branch (kn : list kentry) (c : branch_cond) (a b : expr) : option bool :=
  match c with
  | BC_EQ => if lowbits_neq kn a b then Some false else None
  | BC_NE => if lowbits_neq kn a b then Some true else None
  | _ => None
  end.
Lemma L_AX2L_lowbits_branch : @lowbits_branch = @AX2.lowbits_branch.
Proof. unfold lowbits_branch. rewrite ?L_AX2L_lowbits_neq. reflexivity. Qed.

Definition diff_branch (c : branch_cond) (a b : expr) : option bool :=
  match c with
  | BC_EQ | BC_NE =>
      match is_lit (mkAlu ALU_SUB a b) with
      | Some z => let e := Z.eqb (CXLF.zm64 z) 0 in Some (match c with BC_EQ => e | _ => negb e end)
      | None => None
      end
  | _ => None
  end.
Lemma L_AX2L_diff_branch : @diff_branch = @AX2.diff_branch.
Proof. unfold diff_branch. rewrite ?L_AX2L_is_lit, ?L_AX2L_mkAlu, ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

Definition lin_branch (kn : list kentry) (c : branch_cond) (a b : expr) : option bool :=
  let ltu := if lin_ge0 kn [(b, (-1)%Z)] [(a, 0%Z)] then Some true
             else if lin_ge0 kn [(a, 0%Z)] [(b, 0%Z)] then Some false else None in
  match c with
  | BC_LTU => ltu
  | BC_GEU => option_map negb ltu
  | BC_LT | BC_GE =>
      match erange kn a, erange kn b with
      | Some (_, ah), Some (_, bh) =>
          if (Z.ltb ah (CXLF.p63) && Z.ltb bh (CXLF.p63))%bool
          then match c with BC_LT => ltu | _ => option_map negb ltu end
          else None
      | _, _ => None
      end
  | BC_EQ | BC_NE =>
      
      if (lin_ge0 kn [(b, (-1)%Z)] [(a, 0%Z)] || lin_ge0 kn [(a, (-1)%Z)] [(b, 0%Z)])%bool
      then Some (match c with BC_EQ => false | _ => true end)
      else
      
      if (if lin_ge0 kn [(a, 0%Z)] [(b, 0%Z)] then lin_ge0 kn [(b, 0%Z)] [(a, 0%Z)] else false)
      then Some (match c with BC_EQ => true | _ => false end)
      else None
  end.
Lemma L_AX2L_lin_branch : @lin_branch = @AX2.lin_branch.
Proof. unfold lin_branch. rewrite ?L_AX2L_erange, ?L_AX2L_lin_ge0, ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

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
             | None => match lowbits_branch kn c a b with   
                       | Some t => Some t
                       | None => lin_branch kn c a b      
                       end
             end
           end
  end.
Lemma L_AX2L_decide_branch : @decide_branch = @AX2.decide_branch.
Proof. unfold decide_branch. rewrite ?L_AX2L_expr_eqb, ?L_AX2L_erange, ?L_AX2L_lit_branch, ?L_AX2L_cond_on_eq, ?L_AX2L_range_branch, ?L_AX2L_lowbits_branch, ?L_AX2L_diff_branch, ?L_AX2L_lin_branch. reflexivity. Qed.

Definition mkSlt (kn : list kentry) (c : branch_cond) (op : aluop) (a b : expr) : expr :=
  match a, b with
  | ELit _, ELit _ => mkAlu op a b
  | _, _ => match decide_branch kn c a b with
            | Some true => ELit 1
            | Some false => ELit 0
            | None => mkAlu op a b
            end
  end.
Lemma L_AX2L_mkSlt : @mkSlt = @AX2.mkSlt.
Proof. unfold mkSlt. rewrite ?L_AX2L_mkAlu, ?L_AX2L_decide_branch. reflexivity. Qed.

Definition mkAluK0 (kn : list kentry) (op : aluop) (a b : expr) : expr :=
  match op with
  | ALU_SLTU => mkSlt kn BC_LTU ALU_SLTU a b
  | ALU_SLT => mkSlt kn BC_LT ALU_SLT a b
  | ALU_AND => match a, b with
               | ELit _, ELit _ => mkAnd kn a b
               | ELit _, _ => mkAndK kn b a      
               | _, _ => mkAndK kn a b
               end
  | ALU_OR => if expr_eqb a b then a else mkOr kn a b
  | ALU_XOR => if expr_eqb a b then ELit 0 else match is_lit a, b with
               | None, ELit k => if Z.eqb (CXLF.zm64 k) (two64 - 1) then mkAlu ALU_SUB (ELit (two64 - 1)) a
                                else mkAlu op a b
               | _, _ => mkAlu op a b
               end
  | ALU_SRL => match is_lit a, shamt_of b 6 with
               | None, Some s => mkSrl kn a s
               | _, _ => mkAlu op a b
               end
  | _ => mkAlu op a b
  end.
Lemma L_AX2L_mkAluK0 : @mkAluK0 = @AX2.mkAluK0.
Proof. unfold mkAluK0. rewrite ?L_AX2L_expr_eqb, ?L_AX2L_is_lit, ?L_AX2L_two64, ?L_AX2L_shamt_of, ?L_AX2L_mkAlu, ?L_AX2L_mkSrl, ?L_AX2L_mkAnd, ?L_AX2L_mkAndK, ?L_AX2L_mkOr, ?L_AX2L_mkSlt, ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

Definition zsx32 (v : Z) : Z := ((bv_swrap 32 v) mod two64)%Z.
Lemma L_AX2L_zsx32 : @zsx32 = @AX2.zsx32.
Proof. unfold zsx32. rewrite ?L_AX2L_two64. reflexivity. Qed.

Definition mkAluK (kn : list kentry) (op : aluop) (a b : expr) : expr :=
  foldK kn (mkAluK0 kn op a b).
Lemma L_AX2L_mkAluK : @mkAluK = @AX2.mkAluK.
Proof. unfold mkAluK. rewrite ?L_AX2L_foldK, ?L_AX2L_mkAluK0. reflexivity. Qed.

Definition pow2_log (m : Z) : option Z :=
  let m' := (CXLF.zm64 m)%Z in
  let k := Z.log2 m' in
  if (Z.ltb 0 m' && Z.eqb m' (CXLF.zpow2 k) && Z.ltb k 64)%bool then Some k else None.
Lemma L_AX2L_pow2_log : @pow2_log = @AX2.pow2_log.
Proof. unfold pow2_log. rewrite ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

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
Lemma L_AX2L_mkMdK : @mkMdK = @AX2.mkMdK.
Proof. unfold mkMdK. rewrite ?L_AX2L_is_lit, ?L_AX2L_mkMd, ?L_AX2L_mkAluK, ?L_AX2L_pow2_log. reflexivity. Qed.

Definition sx32_stable (lo hi : Z) : bool :=
  (Z.ltb hi (CXLF.p31) || Z.leb (two64 - CXLF.p31) lo)%bool.
Lemma L_AX2L_sx32_stable : @sx32_stable = @AX2.sx32_stable.
Proof. unfold sx32_stable. rewrite ?L_AX2L_two64, ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

Definition zband32 (kn : list kentry) (d : expr) : bool :=
  let l := lin_of d in
  match lin_range (erange kn) (fst l) (snd l) with
  | Some (lo, hi) => (Z.ltb (- CXLF.p31) lo && Z.ltb hi (CXLF.p31))%bool
  | None => false
  end.
Lemma L_AX2L_zband32 : @zband32 = @AX2.zband32.
Proof. unfold zband32. rewrite ?L_AX2L_lin_of, ?L_AX2L_lin_range, ?L_AX2L_erange, ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

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
Lemma L_AX2L_mkAluwK0 : @mkAluwK0 = @AX2.mkAluwK0.
Proof. unfold mkAluwK0. rewrite ?L_AX2L_is_lit, ?L_AX2L_mkAlu, ?L_AX2L_mkAluw, ?L_AX2L_erange, ?L_AX2L_zsx32, ?L_AX2L_sx32_stable, ?L_AX2L_zband32. reflexivity. Qed.

Definition mkAluwK (kn : list kentry) (op : aluop) (a b : expr) : expr :=
  foldK kn (mkAluwK0 kn op a b).
Lemma L_AX2L_mkAluwK : @mkAluwK = @AX2.mkAluwK.
Proof. unfold mkAluwK. rewrite ?L_AX2L_foldK, ?L_AX2L_mkAluwK0. reflexivity. Qed.

Definition extK0 (kn : list kentry) (v : expr) : expr :=
  match v with
  | EExt sx O n e =>
      if CXNAT.lebF n 7 then
        match erange kn e with
        | Some (lo, hi) => if Z.ltb hi (if sx then 2 ^ (8 * Z.of_nat n) / 2 else 2 ^ (8 * Z.of_nat n)) then e else v
        | None => v
        end
      else v
  | _ => v
  end.
Lemma L_AX2L_extK0 : @extK0 = @AX2.extK0.
Proof. unfold extK0. rewrite ?L_AX2L_erange, ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

Definition extK (kn : list kentry) (v : expr) : expr := foldK kn (extK0 kn v).
Lemma L_AX2L_extK : @extK = @AX2.extK.
Proof. unfold extK. rewrite ?L_AX2L_foldK, ?L_AX2L_extK0. reflexivity. Qed.

Definition msize_bytes (sz : msize) : nat :=
  match sz with SZ1 => 1 | SZ2 => 2 | SZ4 => 4 | SZ8 => 8 end.
Lemma L_AX2L_msize_bytes : @msize_bytes = @AX2.msize_bytes.
Proof. unfold msize_bytes. reflexivity. Qed.

Definition flat_sc (kn : list kentry) (a : saddr) (n : nat) : list sidecond :=
  match base_range kn (a_base a) with
  | Some (lo, hi) =>
      if (Z.leb 0 (lo + a_off a) && Z.leb (hi + a_off a + Z.of_nat n) (CXLF.p64))%bool
      then [] else [SCFlat a (elen n)]
  | None => [SCFlat a (elen n)]
  end.
Lemma L_AX2L_flat_sc : @flat_sc = @AX2.flat_sc.
Proof. unfold flat_sc. rewrite ?L_AX2L_elen, ?L_AX2L_base_range, ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

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
Lemma L_AX2L_wr_covered : @wr_covered = @AX2.wr_covered.
Proof. unfold wr_covered. rewrite ?L_AX2L_expr_eqb, ?L_AX2L_xlo, ?L_AX2L_xinside. reflexivity. Qed.

Definition storeok_sc (kn : list kentry) (a : saddr) (n : nat) : list sidecond :=
  if wr_covered kn kn a n then [] else [SCStoreOk a n].
Lemma L_AX2L_storeok_sc : @storeok_sc = @AX2.storeok_sc.
Proof. unfold storeok_sc. rewrite ?L_AX2L_wr_covered. reflexivity. Qed.

Definition conc_expr (kn : list kentry) (e : expr) : expr :=
  match e with
  | ELit _ => e
  | _ => match concretize kn e with Some v => ELit v | None => e end
  end.
Lemma L_AX2L_conc_expr : @conc_expr = @AX2.conc_expr.
Proof. unfold conc_expr. rewrite ?L_AX2L_concretize. reflexivity. Qed.

Definition cond_probe (c : branch_cond) (a b : expr) : expr * bool :=
  match c with
  | BC_EQ => (EAlu ALU_SLTU (EAlu ALU_SUB a b) (ELit 1%Z), true)    
  | BC_NE => (EAlu ALU_SLTU (EAlu ALU_SUB a b) (ELit 1%Z), false)
  | BC_LT => (EAlu ALU_SLT a b, true)
  | BC_GE => (EAlu ALU_SLT a b, false)
  | BC_LTU => (EAlu ALU_SLTU a b, true)
  | BC_GEU => (EAlu ALU_SLTU a b, false)
  end.
Lemma L_AX2L_cond_probe : @cond_probe = @AX2.cond_probe.
Proof. unfold cond_probe. reflexivity. Qed.

Definition enum_branch (kn : list kentry) (c : branch_cond) (a b : expr) : option bool :=
  let '(e, pos) := cond_probe c a b in
  match concretize kn e with
  | Some v => let z := Z.eqb (CXLF.zm64 v) 0 in Some (if pos then negb z else z)
  | None => None
  end.
Lemma L_AX2L_enum_branch : @enum_branch = @AX2.enum_branch.
Proof. unfold enum_branch. rewrite ?L_AX2L_concretize, ?L_AX2L_cond_probe, ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

Definition to_saddrK (kn : list kentry) (e : expr) (imm : Z) : saddr :=
  match split_lit e with
  | (ELit _, _) => to_saddr e imm
  | _ => match concretize kn (mkAlu ALU_ADD e (ELit imm)) with
         | Some v => SA (ELit 0) v
         | None => to_saddr e imm
         end
  end.
Lemma L_AX2L_to_saddrK : @to_saddrK = @AX2.to_saddrK.
Proof. unfold to_saddrK. rewrite ?L_AX2L_mkAlu, ?L_AX2L_split_lit, ?L_AX2L_to_saddr, ?L_AX2L_concretize. reflexivity. Qed.

Definition amo_sz (wd : awidth) : msize := match wd with AW => SZ4 | AD => SZ8 end.
Lemma L_AX2L_amo_sz : @amo_sz = @AX2.amo_sz.
Proof. unfold amo_sz. reflexivity. Qed.

Definition amo_sx (wd : awidth) : bool := match wd with AW => true | AD => false end.
Lemma L_AX2L_amo_sx : @amo_sx = @AX2.amo_sx.
Proof. unfold amo_sx. reflexivity. Qed.

Definition amo_alignedb (kn : list kentry) (e : expr) (wd : awidth) : bool :=
  match lin_lowbits_kn kn e (match wd with AW => 2 | AD => 3 end) with
  | Some r => Z.eqb r 0
  | None => false
  end.
Lemma L_AX2L_amo_alignedb : @amo_alignedb = @AX2.amo_alignedb.
Proof. unfold amo_alignedb. rewrite ?L_AX2L_lin_lowbits_kn. reflexivity. Qed.

Definition resv_inval (r : option saddr) (a : saddr) : option (option saddr) :=
  match r with
  | None => Some None
  | Some ra =>
      if saddr_eqb ra a then Some None
      else if (expr_eqb (a_base ra) (a_base a) && negb (Z.eqb ((a_off ra - a_off a) mod two64) 0))%bool
           then Some r
           else None
  end.
Lemma L_AX2L_resv_inval : @resv_inval = @AX2.resv_inval.
Proof. unfold resv_inval. rewrite ?L_AX2L_expr_eqb, ?L_AX2L_two64, ?L_AX2L_saddr_eqb. reflexivity. Qed.

Definition amo_aluop (op : amoop) : option (option aluop) :=
  match op with
  | AMO_SWAP => Some None
  | AMO_ADD => Some (Some ALU_ADD)
  | AMO_XOR => Some (Some ALU_XOR)
  | AMO_AND => Some (Some ALU_AND)
  | AMO_OR => Some (Some ALU_OR)
  | _ => None
  end.
Lemma L_AX2L_amo_aluop : @amo_aluop = @AX2.amo_aluop.
Proof. unfold amo_aluop. reflexivity. Qed.

Definition amo_newval (kn : list kentry) (wd : awidth) (aop : option aluop) (old src : expr) : expr :=
  match aop with
  | None => src
  | Some o => match wd with AW => mkAluwK kn o old src | AD => mkAluK kn o old src end
  end.
Lemma L_AX2L_amo_newval : @amo_newval = @AX2.amo_newval.
Proof. unfold amo_newval. rewrite ?L_AX2L_mkAluK, ?L_AX2L_mkAluwK. reflexivity. Qed.

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
          
          let i := s_next ss in
          let rv := match sc_reads scr with [] => EVar i | e :: _ => e end in
          let reads' := match sc_reads scr with [] => [] | _ :: t => t end in
          Some (rv, flat_sc fk a n ++ SCReadBase a n sx' rv :: scs', SCR (sc_dirs scr) reads' hints', S i)
      end
  end.
Lemma L_AX2L_sym_read : @sym_read = @AX2.sym_read.
Proof. unfold sym_read. rewrite ?L_AX2L_log_lookup, ?L_AX2L_know_lookupA, ?L_AX2L_extK, ?L_AX2L_flat_sc. reflexivity. Qed.

Definition sym_step (segs : list Segment) (i : instr) (ss : sym_state) (scr : scripts) : stepres :=
  let g r := sr_get (s_regs ss) r in
  let p := s_pc ss in
  let fk := facts_of (s_know ss) in   
  match i with
  | OpImm op rd rs imm => SOk (sset ss rd (mkAluK fk op (g rs) (ELit (bv_signed imm))) (p + 4)) [] scr
  | ShiftImm op rd rs sh => SOk (sset ss rd (mkAluK fk op (g rs) (ELit (bv_unsigned sh))) (p + 4)) [] scr
  | Op op rd rs1 rs2 => SOk (sset ss rd (mkAluK fk op (g rs1) (g rs2)) (p + 4)) [] scr
  | OpImm32 rd rs imm => SOk (sset ss rd (mkAluwK fk ALU_ADD (g rs) (ELit (bv_signed imm))) (p + 4)) [] scr
  | ShiftImm32 op rd rs sh => SOk (sset ss rd (mkAluw op (g rs) (ELit (bv_unsigned sh))) (p + 4)) [] scr
  | Op32 op rd rs1 rs2 => SOk (sset ss rd (mkAluwK fk op (g rs1) (g rs2)) (p + 4)) [] scr
  | Mul op rd rs1 rs2 => SOk (sset ss rd (mkMdK fk op (g rs1) (g rs2)) (p + 4)) [] scr
  | Mul32 op rd rs1 rs2 => SOk (sset ss rd (mkMdw op (g rs1) (g rs2)) (p + 4)) [] scr
  | Lui rd imm => SOk (sset ss rd (ELit (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_signed imm) 12)))) (p + 4)) [] scr
  | Auipc rd imm => SOk (sset ss rd (ELit (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_signed imm) 12 + p)))) (p + 4)) [] scr
  | Jal rd imm => SOk (sset ss rd (ELit (p + 4)) (bv_unsigned (Z_to_bv 64 (p + bv_signed imm)))) [] scr
  | Jalr rd rs1 imm =>
      match conc_expr fk (g rs1) with
      | ELit z => SOk (sset ss rd (ELit (p + 4)) (Z.land (bv_wrap 64 z + bv_signed imm) (-2) mod CXLF.p64)) [] scr
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
            else SStop   
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
  | _ => SStop
  end.
Lemma L_AX2L_sym_step : @sym_step = @AX2.sym_step.
Proof. unfold sym_step. rewrite ?L_AX2L_mkAluw, ?L_AX2L_mkMdw, ?L_AX2L_ridx, ?L_AX2L_sr_get, ?L_AX2L_sr_upd, ?L_AX2L_saddr_eqb, ?L_AX2L_sset, ?L_AX2L_sjump, ?L_AX2L_facts_of, ?L_AX2L_decide_branch, ?L_AX2L_mkAluK, ?L_AX2L_mkMdK, ?L_AX2L_mkAluwK, ?L_AX2L_msize_bytes, ?L_AX2L_flat_sc, ?L_AX2L_storeok_sc, ?L_AX2L_conc_expr, ?L_AX2L_enum_branch, ?L_AX2L_to_saddrK, ?L_AX2L_amo_sz, ?L_AX2L_amo_sx, ?L_AX2L_amo_alignedb, ?L_AX2L_resv_inval, ?L_AX2L_amo_aluop, ?L_AX2L_amo_newval, ?L_AX2L_sym_read, ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

Definition sidecond_eqb (x y : sidecond) : bool :=
  match x, y with
  | SCFlat a n, SCFlat a' n' => saddr_eqb a a' && expr_eqb n n'
  | SCStoreOk a n, SCStoreOk a' n' => saddr_eqb a a' && CXNAT.eqbF n n'
  | SCDisj a n b m, SCDisj a' n' b' m' =>
      saddr_eqb a a' && expr_eqb n n' && saddr_eqb b b' && expr_eqb m m'
  | SCInside a n b m, SCInside a' n' b' m' =>
      saddr_eqb a a' && expr_eqb n n' && saddr_eqb b b' && expr_eqb m m'
  | _, _ => false
  end.
Lemma L_AX2L_sidecond_eqb : @sidecond_eqb = @AX2.sidecond_eqb.
Proof. unfold sidecond_eqb. rewrite ?L_AX2L_expr_eqb, ?L_AX2L_saddr_eqb, ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

Fixpoint sc_mem (x : sidecond) (l : list sidecond) : bool :=
  match l with [] => false | y :: t => sidecond_eqb x y || sc_mem x t end.
Lemma L_AX2L_sc_mem : @sc_mem = @AX2.sc_mem.
Proof. unfold sc_mem. rewrite ?L_AX2L_sidecond_eqb. reflexivity. Qed.

Fixpoint sc_add (news acc : list sidecond) : list sidecond :=
  match news with
  | [] => acc
  | x :: t => sc_add t (if sc_mem x acc then acc else x :: acc)
  end.
Lemma L_AX2L_sc_add : @sc_add = @AX2.sc_add.
Proof. unfold sc_add. rewrite ?L_AX2L_sc_mem. reflexivity. Qed.

Definition itab : Type := ptree instr.
Lemma L_AX2L_itab : @itab = @AX2.itab.
Proof. unfold itab. reflexivity. Qed.

Definition itab_lookup (t : itab) (pc : Z) : option instr :=
  match pc with Zpos p => pt_get t p | _ => None end.
Lemma L_AX2L_itab_lookup : @itab_lookup = @AX2.itab_lookup.
Proof. unfold itab_lookup. rewrite ?L_AX2L_pt_get, ?L_AX2L_itab. reflexivity. Qed.

Section WithSegs.
Variable segs : list Segment.
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
Definition mk_itab (lo : Z) (n : nat) : itab := mk_itab_fuel n lo PTLeaf.
Definition itab_sound (t : itab) : Prop :=
  forall pc i, itab_lookup t pc = Some i -> itab_entry pc = Some i.
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
Definition scr_nil : scripts := SCR [] [] [].
Fixpoint sym_execS_go (fuel : nat) (first : bool) (stops : list Z) (ss : sym_state) (ck : sym_state)
  : sym_state :=
  match fuel with
  | O => if s_clean ss then ss else ck
  | S f =>
      if (negb first && existsb (Z.eqb (s_pc ss)) stops)%bool then (if s_clean ss then ss else ck) else
      match fetch_word segs (Z_to_bv 64 (s_pc ss)) with
      | None => if s_clean ss then ss else ck
      | Some w =>
          if is_ecall w then (if s_clean ss then ss else ck) else
          match decode_any w with
          | None => if s_clean ss then ss else ck
          | Some (i, sz) =>
              if negb (Z.eqb sz 4) then (if s_clean ss then ss else ck) else
              match sym_step segs i ss scr_nil with
              | SOk ss' [] _ => sym_execS_go f false stops ss' (if s_clean ss' then ss' else ck)
              | _ => if s_clean ss then ss else ck
              end
          end
      end
  end.
Definition sym_execS (fuel : nat) (first : bool) (stops : list Z) (ss : sym_state) : sym_state :=
  sym_execS_go fuel first stops (clr ss) (clr ss).
Fixpoint sym_execT_go (t : itab) (fuel : nat) (first : bool) (stops : list Z) (ss : sym_state) (ck : sym_state)
  : sym_state :=
  match fuel with
  | O => if s_clean ss then ss else ck
  | S f =>
      if (negb first && existsb (Z.eqb (s_pc ss)) stops)%bool then (if s_clean ss then ss else ck) else
      match itab_lookup t (s_pc ss) with
      | None => if s_clean ss then ss else ck
      | Some i =>
          match sym_step segs i ss scr_nil with
          | SOk ss' [] _ => sym_execT_go t f false stops ss' (if s_clean ss' then ss' else ck)
          | _ => if s_clean ss then ss else ck
          end
      end
  end.
Definition sym_execT (t : itab) (fuel : nat) (first : bool) (stops : list Z) (ss : sym_state) : sym_state :=
  sym_execT_go t fuel first stops (clr ss) (clr ss).
Definition zf_covers (allkn : list kentry) (rb : expr) (rk : Z) (n : nat) (kb : expr) (kk : Z) (len : expr) : bool :=
  (match len with
   | ELit l0 => match rel_lit rb rk (Z.of_nat n) kb kk (CXLF.zm64 l0)%Z with RInside _ => true | _ => false end
   | _ => false
   end) || xinside allkn rb rk (elen n) kb kk len.
Definition kentry_overlay (allkn : list kentry) (rb : expr) (rk : Z) (n : nat) (K : kentry) : bool :=
  match K with
  | KUnk (SA kb kk) len | KZero (SA kb kk) len | KFill (SA kb kk) len _ | KBlob (SA kb kk) len _ =>
      zf_covers allkn rb rk n kb kk len
  | _ => false
  end.
Definition kentry_readable (allkn : list kentry) (rb : expr) (rk : Z) (n : nat) (K : kentry) : bool :=
  match K with
  | KWord (SA kb kk) w _ =>
      match rel_lit rb rk (Z.of_nat n) kb kk (Z.of_nat w) with RInside _ => true | _ => false end
  | _ => kentry_overlay allkn rb rk n K
  end.
Fixpoint know_byte_cov (img : bool) (kn : list kentry) (rb : expr) (rk : Z) : bool :=
  match kn with
  | [] => false
  | K :: rest =>
      let lit kb kk (l : Z) := match rel_lit rb rk 1 kb kk l with RInside _ => true | _ => false end in
      (match K with
       | KWord (SA kb kk) w _ => img && lit kb kk (Z.of_nat w)
       | KZero (SA kb kk) (ELit l0) | KFill (SA kb kk) (ELit l0) _ | KBlob (SA kb kk) (ELit l0) _
       | KUnk (SA kb kk) (ELit l0) => lit kb kk (CXLF.zm64 l0)%Z
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
Fixpoint evars_lt (b : nat) (e : expr) : bool :=
  match e with
  | ELit _ | EBlob _ _ _ _ => true
  | EVar v => CXNAT.ltbF v b
  | EAlu _ x y | EAluw _ x y | EMd _ x y | EMdw _ x y => evars_lt b x && evars_lt b y
  | EExt _ _ _ x => evars_lt b x
  end.
Fixpoint find_readbase (i : nat) (scs : list sidecond) : option (saddr * nat * bool) :=
  match scs with
  | [] => None
  | SCReadBase a n sx (EVar j) :: rest => if CXNAT.eqbF j i then Some (a, n, sx) else find_readbase i rest
  | _ :: rest => find_readbase i rest
  end.
Definition x_dischargeable (ss ss' : sym_state) (rb : option (saddr * nat * bool)) (sc : sidecond) : bool :=
  let kn := s_know ss in
  let fk := facts_of kn in
  match sc with
  | SCReadBase a n sx (EVar j) =>
      (match rb with
       | Some (a', n', sx') => saddr_eqb a' a && CXNAT.eqbF n' n && Bool.eqb sx' sx
       | None => false
       end)
      && CXNAT.eqbF j (s_next ss) && CXNAT.ltbF j (s_next ss') && evars_lt (s_next ss) (a_base a)
      && CXNAT.lebF 1 n && CXNAT.lebF n 8 && kn_readable fk kn (a_base a) (a_off a) n
  | SCFlat a (ELit z) =>
      Z.leb 1 z && Z.leb z 8 && kn_readable fk kn (a_base a) (a_off a) (Z.to_nat z)
  | SCStoreOk a n => CXNAT.lebF 1 n && CXNAT.lebF n 8 && kn_overlay fk kn (a_base a) (a_off a) n
  | _ => false
  end%bool.
Definition x_filter (ss ss' : sym_state) (scs : list sidecond) : list sidecond :=
  match scs with
  | [] => []          
  | _ => let rb := find_readbase (s_next ss) scs in
         List.filter (fun sc => negb (x_dischargeable ss ss' rb sc)) scs
  end.
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
Definition rd_of (i : instr) : option reg :=
  match i with
  | Lui rd _ | Auipc rd _ | Jal rd _ | Jalr rd _ _ | Load _ _ rd _ _
  | OpImm _ rd _ _ | ShiftImm _ rd _ _ | Op _ rd _ _ | OpImm32 rd _ _ | ShiftImm32 _ rd _ _ | Op32 _ rd _ _
  | Mul _ rd _ _ | Mul32 _ rd _ _ | Lr _ _ _ rd _ | Sc _ _ _ rd _ _ | Amo _ _ _ _ rd _ _ => Some rd
  | _ => None
  end.
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
Definition sym_stepX (K : nat) (i : instr) (ss : sym_state) (scr : scripts) : stepres :=
  match sym_step segs i ss scr with
  | SOk ss' scs scr' =>
      if CXNAT.lebF (s_next ss) (s_next ss')            
      then SOk (cap_rd K i ss') (x_filter ss ss' scs) scr'
      else SStop
  | SStop => SStop
  end.
Fixpoint sym_execSX_go (K : nat) (fuel : nat) (first : bool) (stops : list Z) (ss : sym_state) (ck : sym_state)
  : sym_state :=
  match fuel with
  | O => if s_clean ss then ss else ck
  | S f =>
      if (negb first && existsb (Z.eqb (s_pc ss)) stops)%bool then (if s_clean ss then ss else ck) else
      match fetch_word segs (Z_to_bv 64 (s_pc ss)) with
      | None => if s_clean ss then ss else ck
      | Some w =>
          if is_ecall w then (if s_clean ss then ss else ck) else
          match decode_any w with
          | None => if s_clean ss then ss else ck
          | Some (i, sz) =>
              if negb (Z.eqb sz 4) then (if s_clean ss then ss else ck) else
              match sym_stepX K i ss scr_nil with
              | SOk ss' [] _ => sym_execSX_go K f false stops ss' (if s_clean ss' then ss' else ck)
              | _ => if s_clean ss then ss else ck
              end
          end
      end
  end.
Definition sym_execSX (K : nat) (fuel : nat) (first : bool) (stops : list Z) (ss : sym_state) : sym_state :=
  sym_execSX_go K fuel first stops (clr ss) (clr ss).
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
          | _ => if s_clean ss then ss else ck
          end
      end
  end.
Definition sym_execTX (t : itab) (K : nat) (fuel : nat) (first : bool) (stops : list Z) (ss : sym_state) : sym_state :=
  sym_execTX_go t K fuel first stops (clr ss) (clr ss).
End WithSegs.
Lemma L_AX2L_itab_entry : @itab_entry = @AX2.itab_entry.
Proof. unfold itab_entry. reflexivity. Qed.

Lemma L_AX2L_mk_itab_fuel : @mk_itab_fuel = @AX2.mk_itab_fuel.
Proof. unfold mk_itab_fuel. rewrite ?L_AX2L_pt_set, ?L_AX2L_itab, ?L_AX2L_itab_entry. reflexivity. Qed.

Lemma L_AX2L_mk_itab : @mk_itab = @AX2.mk_itab.
Proof. unfold mk_itab. rewrite ?L_AX2L_itab, ?L_AX2L_mk_itab_fuel. reflexivity. Qed.

Lemma L_AX2L_itab_sound : @itab_sound = @AX2.itab_sound.
Proof. unfold itab_sound. rewrite ?L_AX2L_itab, ?L_AX2L_itab_lookup, ?L_AX2L_itab_entry. reflexivity. Qed.

Lemma L_AX2L_sym_exec_go : @sym_exec_go = @AX2.sym_exec_go.
Proof. unfold sym_exec_go. rewrite ?L_AX2L_s_clean, ?L_AX2L_sym_step, ?L_AX2L_sc_add. reflexivity. Qed.

Lemma L_AX2L_sym_exec : @sym_exec = @AX2.sym_exec.
Proof. unfold sym_exec. rewrite ?L_AX2L_clr, ?L_AX2L_sym_exec_go. reflexivity. Qed.

Lemma L_AX2L_scr_nil : @scr_nil = @AX2.scr_nil.
Proof. unfold scr_nil. reflexivity. Qed.

Lemma L_AX2L_sym_execS_go : @sym_execS_go = @AX2.sym_execS_go.
Proof. unfold sym_execS_go. rewrite ?L_AX2L_s_clean, ?L_AX2L_sym_step, ?L_AX2L_scr_nil. reflexivity. Qed.

Lemma L_AX2L_sym_execS : @sym_execS = @AX2.sym_execS.
Proof. unfold sym_execS. rewrite ?L_AX2L_clr, ?L_AX2L_sym_execS_go. reflexivity. Qed.

Lemma L_AX2L_sym_execT_go : @sym_execT_go = @AX2.sym_execT_go.
Proof. unfold sym_execT_go. rewrite ?L_AX2L_s_clean, ?L_AX2L_sym_step, ?L_AX2L_itab, ?L_AX2L_itab_lookup, ?L_AX2L_scr_nil. reflexivity. Qed.

Lemma L_AX2L_sym_execT : @sym_execT = @AX2.sym_execT.
Proof. unfold sym_execT. rewrite ?L_AX2L_clr, ?L_AX2L_itab, ?L_AX2L_sym_execT_go. reflexivity. Qed.

Lemma L_AX2L_zf_covers : @zf_covers = @AX2.zf_covers.
Proof. unfold zf_covers. rewrite ?L_AX2L_rel_lit, ?L_AX2L_elen, ?L_AX2L_xinside, ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

Lemma L_AX2L_kentry_overlay : @kentry_overlay = @AX2.kentry_overlay.
Proof. unfold kentry_overlay. rewrite ?L_AX2L_zf_covers. reflexivity. Qed.

Lemma L_AX2L_kentry_readable : @kentry_readable = @AX2.kentry_readable.
Proof. unfold kentry_readable. rewrite ?L_AX2L_rel_lit, ?L_AX2L_kentry_overlay. reflexivity. Qed.

Lemma L_AX2L_know_byte_cov : @know_byte_cov = @AX2.know_byte_cov.
Proof. unfold know_byte_cov. rewrite ?L_AX2L_rel_lit, ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

Lemma L_AX2L_know_bytes_cov : @know_bytes_cov = @AX2.know_bytes_cov.
Proof. unfold know_bytes_cov. rewrite ?L_AX2L_know_byte_cov. reflexivity. Qed.

Lemma L_AX2L_kn_readable : @kn_readable = @AX2.kn_readable.
Proof. unfold kn_readable. rewrite ?L_AX2L_kentry_readable, ?L_AX2L_know_bytes_cov. reflexivity. Qed.

Lemma L_AX2L_kn_overlay : @kn_overlay = @AX2.kn_overlay.
Proof. unfold kn_overlay. rewrite ?L_AX2L_kentry_overlay, ?L_AX2L_know_bytes_cov. reflexivity. Qed.

Lemma L_AX2L_evars_lt : @evars_lt = @AX2.evars_lt.
Proof. unfold evars_lt. rewrite ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

Lemma L_AX2L_find_readbase : @find_readbase = @AX2.find_readbase.
Proof. unfold find_readbase. rewrite ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

Lemma L_AX2L_x_dischargeable : @x_dischargeable = @AX2.x_dischargeable.
Proof. unfold x_dischargeable. rewrite ?L_AX2L_saddr_eqb, ?L_AX2L_facts_of, ?L_AX2L_kn_readable, ?L_AX2L_kn_overlay, ?L_AX2L_evars_lt, ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

Lemma L_AX2L_x_filter : @x_filter = @AX2.x_filter.
Proof. unfold x_filter. rewrite ?L_AX2L_find_readbase, ?L_AX2L_x_dischargeable. reflexivity. Qed.

Lemma L_AX2L_esize_budget : @esize_budget = @AX2.esize_budget.
Proof. unfold esize_budget. reflexivity. Qed.

Lemma L_AX2L_esize_le : @esize_le = @AX2.esize_le.
Proof. unfold esize_le. rewrite ?L_AX2L_esize_budget. reflexivity. Qed.

Lemma L_AX2L_rd_of : @rd_of = @AX2.rd_of.
Proof. unfold rd_of. reflexivity. Qed.

Lemma L_AX2L_cap_rd : @cap_rd = @AX2.cap_rd.
Proof. unfold cap_rd. rewrite ?L_AX2L_ridx, ?L_AX2L_sr_get, ?L_AX2L_sr_upd, ?L_AX2L_esize_le, ?L_AX2L_rd_of. reflexivity. Qed.

Lemma L_AX2L_sym_stepX : @sym_stepX = @AX2.sym_stepX.
Proof. unfold sym_stepX. rewrite ?L_AX2L_sym_step, ?L_AX2L_x_filter, ?L_AX2L_cap_rd, ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

Lemma L_AX2L_sym_execSX_go : @sym_execSX_go = @AX2.sym_execSX_go.
Proof. unfold sym_execSX_go. rewrite ?L_AX2L_s_clean, ?L_AX2L_scr_nil, ?L_AX2L_sym_stepX. reflexivity. Qed.

Lemma L_AX2L_sym_execSX : @sym_execSX = @AX2.sym_execSX.
Proof. unfold sym_execSX. rewrite ?L_AX2L_clr, ?L_AX2L_sym_execSX_go. reflexivity. Qed.

Lemma L_AX2L_sym_execTX_go : @sym_execTX_go = @AX2.sym_execTX_go.
Proof. unfold sym_execTX_go. rewrite ?L_AX2L_s_clean, ?L_AX2L_itab, ?L_AX2L_itab_lookup, ?L_AX2L_scr_nil, ?L_AX2L_sym_stepX. reflexivity. Qed.

Lemma L_AX2L_sym_execTX : @sym_execTX = @AX2.sym_execTX.
Proof. unfold sym_execTX. rewrite ?L_AX2L_clr, ?L_AX2L_itab, ?L_AX2L_sym_execTX_go. reflexivity. Qed.

Definition kcut (mk : saddr -> expr -> kentry) (kn : list kentry) (wb : expr) (wk : Z) (wn : expr)
           (kb : expr) (kk : Z) (len : expr) : list kentry :=
  let ws := mkAlu ALU_ADD wb (ELit wk) in
  let ks := mkAlu ALU_ADD kb (ELit kk) in
  
  let low :=
    if (if lin_ge0 kn [(kb, kk)] [(wb, wk)] then false   
        else if lin_ge0 kn [(wb, wk)] [(kb, kk)] then lin_ge0 kn [(kb, kk); (len, 0%Z)] [(wb, wk)] else false)
    then [mk (SA kb kk) (mkAlu ALU_SUB ws ks)] else [] in
  let high :=
    if (if lin_ge0 kn [(kb, kk); (len, 0%Z)] [(wb, wk); (wn, 0%Z)]            
        then if lin_ge0 kn [(wb, wk); (wn, 0%Z)] [(kb, kk)]                    
             then lin_ge0 kn [(ELit 0, (two64 - 1)%Z)] [(kb, kk); (len, 0%Z)]  
             else false
        else false)
    then let we := mkAlu ALU_ADD ws wn in
         let '(hb, ho) := split_lit we in
         let ha := if (lin_ge0 kn [(hb, ho)] [(wb, wk); (wn, 0%Z)] && lin_ge0 kn [(wb, wk); (wn, 0%Z)] [(hb, ho)])%bool
                   then SA hb ho else SA we 0%Z in
         [mk ha (mkAlu ALU_SUB (mkAlu ALU_ADD ks len) we)]
    else [] in
  low ++ high.
Lemma L_AX2L_kcut : @kcut = @AX2.kcut.
Proof. unfold kcut. rewrite ?L_AX2L_two64, ?L_AX2L_mkAlu, ?L_AX2L_split_lit, ?L_AX2L_lin_ge0. reflexivity. Qed.

Definition kzero_cut (kn : list kentry) (wb : expr) (wk : Z) (wn : expr)
           (kb : expr) (kk : Z) (len : expr) : list kentry := kcut KZero kn wb wk wn kb kk len.
Lemma L_AX2L_kzero_cut : @kzero_cut = @AX2.kzero_cut.
Proof. unfold kzero_cut. rewrite ?L_AX2L_kcut. reflexivity. Qed.

Definition kfill_cut (c : Z) (kn : list kentry) (wb : expr) (wk : Z) (wn : expr)
           (kb : expr) (kk : Z) (len : expr) : list kentry := kcut (fun a n => KFill a n c) kn wb wk wn kb kk len.
Lemma L_AX2L_kfill_cut : @kfill_cut = @AX2.kfill_cut.
Proof. unfold kfill_cut. rewrite ?L_AX2L_kcut. reflexivity. Qed.

Definition kunk_cut (kn : list kentry) (wb : expr) (wk : Z) (wn : expr)
           (kb : expr) (kk : Z) (len : expr) : list kentry := kcut KUnk kn wb wk wn kb kk len.
Lemma L_AX2L_kunk_cut : @kunk_cut = @AX2.kunk_cut.
Proof. unfold kunk_cut. rewrite ?L_AX2L_kcut. reflexivity. Qed.

Definition ktrim (mk : saddr -> expr -> kentry) (kb : expr) (kk : Z) (l0 : Z) (k : Z) (w : nat) : list kentry :=
  let l := (CXLF.zm64 l0)%Z in
  let hi1 := Z.min k (kk + l) in
  let r1 := if Z.ltb kk hi1 then [mk (SA kb kk) (ELit (hi1 - kk))] else [] in
  let lo2 := Z.max kk (k + Z.of_nat w) in
  let r2 := if Z.ltb lo2 (kk + l) then [mk (SA kb lo2) (ELit (kk + l - lo2))] else [] in
  r1 ++ r2.
Lemma L_AX2L_ktrim : @ktrim = @AX2.ktrim.
Proof. unfold ktrim. rewrite ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

Definition kword_cut (kb : expr) (kk : Z) (w' : nat) (v : expr) (k : Z) (w : nat) : list kentry :=
  let n1 := (k - kk)%Z in                                
  let r1 := if Z.ltb 0 n1 then [KWord (SA kb kk) (Z.to_nat n1) (mkExt false 0 (Z.to_nat n1) v)] else [] in
  let d := (k + Z.of_nat w - kk)%Z in                    
  let r2 := if Z.ltb d (Z.of_nat w')
            then [KWord (SA kb (kk + d)) (w' - Z.to_nat d) (mkExt false (Z.to_nat d) (w' - Z.to_nat d) v)]
            else [] in
  r1 ++ r2.
Lemma L_AX2L_kword_cut : @kword_cut = @AX2.kword_cut.
Proof. unfold kword_cut. rewrite ?L_AX2L_mkExt. reflexivity. Qed.

Definition prune_zf (mk : saddr -> expr -> kentry) (allkn : list kentry) (wb : expr) (k : Z) (w : nat)
           (K : kentry) (kb : expr) (kk : Z) (len : expr) (apart : unit -> bool) (hints : list bool)
           (diffbase : unit -> list kentry * list sidecond * list bool)
  : list kentry * list sidecond * list bool :=
  
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
Lemma L_AX2L_prune_zf : @prune_zf = @AX2.prune_zf.
Proof. unfold prune_zf. rewrite ?L_AX2L_expr_eqb, ?L_AX2L_elen, ?L_AX2L_kcut, ?L_AX2L_ktrim. reflexivity. Qed.

Definition prune1 (allkn : list kentry) (wa : saddr) (w : nat) (wv : expr) (K : kentry) (hints : list bool)
  : list kentry * list sidecond * list bool :=
  let k := a_off wa in
  let diffbase (ka : saddr) (kl : expr) :=
    let apart := ranges_apart_x allkn (a_base wa) k (elen w) (a_base ka) (a_off ka) kl in
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
      | _ => if Z.ltb (hi - lo) (CXLF.p64) then diffbase (SA (ELit 0) lo) (ELit (hi - lo))
             else ([], [], hints)
      end
  | KZero (SA kb kk) len =>
      prune_zf KZero allkn (a_base wa) k w K kb kk len
               (fun _ => ranges_apart_x allkn (a_base wa) k (elen w) kb kk len) hints (fun _ => diffbase (SA kb kk) len)
  | KFill (SA kb kk) len c =>
      prune_zf (fun a n => KFill a n c) allkn (a_base wa) k w K kb kk len
               (fun _ => ranges_apart_x allkn (a_base wa) k (elen w) kb kk len) hints (fun _ => diffbase (SA kb kk) len)
  | KUnk (SA kb kk) len =>
      prune_zf KUnk allkn (a_base wa) k w K kb kk len
               (fun _ => ranges_apart_x allkn (a_base wa) k (elen w) kb kk len) hints (fun _ => diffbase (SA kb kk) len)
  | KWord (SA kb kk) w' v =>
      if expr_eqb kb (a_base wa) then
        (if (Z.leb (kk + Z.of_nat w') k || Z.leb (k + Z.of_nat w) kk)%bool
         then ([K], [], hints) else (kword_cut kb kk w' v k w, [], hints))   
      else if ranges_apart_x allkn (a_base wa) k (elen w) kb kk (elen w') then ([K], [], hints)
      else if (CXNAT.eqbF w 1 && CXNAT.eqbF w' 1 && expr_eqb wv v)%bool
      then ([K], [], hints)   
      else diffbase (SA kb kk) (elen w')
  | KBlob (SA kb kk) len bk =>
      if expr_eqb kb (a_base wa) then
        match len with
        | ELit l0 =>
            let l := (CXLF.zm64 l0)%Z in
            (if (Z.leb (kk + l) k || Z.leb (k + Z.of_nat w) kk)%bool
             then ([K], [], hints) else ([], [], hints))
        | _ => if Z.leb (k + Z.of_nat w) kk then ([K], [], hints) else ([], [], hints)
        end
      else diffbase (SA kb kk) len
  end.
Lemma L_AX2L_prune1 : @prune1 = @AX2.prune1.
Proof. unfold prune1. rewrite ?L_AX2L_expr_eqb, ?L_AX2L_elen, ?L_AX2L_ranges_apart_x, ?L_AX2L_kword_cut, ?L_AX2L_prune_zf, ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

Fixpoint prune (allkn : list kentry) (wa : saddr) (w : nat) (wv : expr) (kn : list kentry) (hints : list bool)
  : list kentry * list sidecond * list bool :=
  match kn with
  | [] => ([], [], hints)
  | K :: rest =>
      let '(kept, scs1, hs1) := prune1 allkn wa w wv K hints in
      let '(r, scs2, hs2) := prune allkn wa w wv rest hs1 in
      (kept ++ r, scs1 ++ scs2, hs2)
  end.
Lemma L_AX2L_prune : @prune = @AX2.prune.
Proof. unfold prune. rewrite ?L_AX2L_prune1. reflexivity. Qed.

Definition prune1p (allkn : list kentry) (sp : sprep) (wa : saddr) (w : nat) (wv : expr) (K : kentry) (hints : list bool)
  : list kentry * list sidecond * list bool :=
  let k := a_off wa in
  let diffbase (ka : saddr) (kl : expr) :=
    let apart := ranges_apart_p allkn sp (a_base wa) k (elen w) (a_base ka) (a_off ka) kl in
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
      | _ => if Z.ltb (hi - lo) (CXLF.p64) then diffbase (SA (ELit 0) lo) (ELit (hi - lo))
             else ([], [], hints)
      end
  | KZero (SA kb kk) len =>
      prune_zf KZero allkn (a_base wa) k w K kb kk len
               (fun _ => ranges_apart_p allkn sp (a_base wa) k (elen w) kb kk len) hints (fun _ => diffbase (SA kb kk) len)
  | KFill (SA kb kk) len c =>
      prune_zf (fun a n => KFill a n c) allkn (a_base wa) k w K kb kk len
               (fun _ => ranges_apart_p allkn sp (a_base wa) k (elen w) kb kk len) hints (fun _ => diffbase (SA kb kk) len)
  | KUnk (SA kb kk) len =>
      prune_zf KUnk allkn (a_base wa) k w K kb kk len
               (fun _ => ranges_apart_p allkn sp (a_base wa) k (elen w) kb kk len) hints (fun _ => diffbase (SA kb kk) len)
  | KWord (SA kb kk) w' v =>
      if expr_eqb kb (a_base wa) then
        (if (Z.leb (kk + Z.of_nat w') k || Z.leb (k + Z.of_nat w) kk)%bool
         then ([K], [], hints) else (kword_cut kb kk w' v k w, [], hints))   
      else if ranges_apart_p allkn sp (a_base wa) k (elen w) kb kk (elen w') then ([K], [], hints)
      else if (CXNAT.eqbF w 1 && CXNAT.eqbF w' 1 && expr_eqb wv v)%bool
      then ([K], [], hints)   
      else diffbase (SA kb kk) (elen w')
  | KBlob (SA kb kk) len bk =>
      if expr_eqb kb (a_base wa) then
        match len with
        | ELit l0 =>
            let l := (CXLF.zm64 l0)%Z in
            (if (Z.leb (kk + l) k || Z.leb (k + Z.of_nat w) kk)%bool
             then ([K], [], hints) else ([], [], hints))
        | _ => if Z.leb (k + Z.of_nat w) kk then ([K], [], hints) else ([], [], hints)
        end
      else diffbase (SA kb kk) len
  end.
Lemma L_AX2L_prune1p : @prune1p = @AX2.prune1p.
Proof. unfold prune1p. rewrite ?L_AX2L_expr_eqb, ?L_AX2L_elen, ?L_AX2L_ranges_apart_p, ?L_AX2L_kword_cut, ?L_AX2L_prune_zf, ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

Fixpoint prunep (allkn : list kentry) (sp : sprep) (wa : saddr) (w : nat) (wv : expr) (kn : list kentry) (hints : list bool)
  : list kentry * list sidecond * list bool :=
  match kn with
  | [] => ([], [], hints)
  | K :: rest =>
      let '(kept, scs1, hs1) := prune1p allkn sp wa w wv K hints in
      let '(r, scs2, hs2) := prunep allkn sp wa w wv rest hs1 in
      (kept ++ r, scs1 ++ scs2, hs2)
  end.
Lemma L_AX2L_prunep : @prunep = @AX2.prunep.
Proof. unfold prunep. rewrite ?L_AX2L_prune1p. reflexivity. Qed.

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
            if (Z.leb (hi1 + k1 + h1) (lo2 + k2) || Z.leb (hi2 + k2 + h2) (lo1 + k1))%bool then true
            else 
            if match end_hi kn b1 k1 n1 lo1 hi1 h1 with Some e1 => Z.leb e1 (lo2 + k2) | None => false end then true
            else match end_hi kn b2 k2 n2 lo2 hi2 h2 with Some e2 => Z.leb e2 (lo1 + k1) | None => false end
        | _, _, _, _ => false
        end) then true
    else if in_sides_x kn (sp_Dx sp) b2 k2 n2 then true
    else if negb (shares_var b1 b2) then false
    else if lin_ge0 kn [(b2, k2)] [(b1, k1); (n1, 0%Z)] then true
    else lin_ge0 kn [(b1, k1)] [(b2, k2); (n2, 0%Z)]
  end.
Lemma L_AX2L_ranges_apart_pc : @ranges_apart_pc = @AX2.ranges_apart_pc.
Proof. unfold ranges_apart_pc. rewrite ?L_AX2L_shares_var, ?L_AX2L_lin_apart, ?L_AX2L_zlit64, ?L_AX2L_xhi, ?L_AX2L_lin_ge0, ?L_AX2L_end_hi, ?L_AX2L_in_sides, ?L_AX2L_in_sides_x. reflexivity. Qed.

Definition kbase (K : kentry) : option expr :=
  match K with
  | KZero (SA kb _) _ | KWord (SA kb _) _ _ | KBlob (SA kb _) _ _ | KFill (SA kb _) _ _ | KUnk (SA kb _) _ => Some kb
  | _ => None
  end.
Lemma L_AX2L_kbase : @kbase = @AX2.kbase.
Proof. unfold kbase. reflexivity. Qed.

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
  | KUnk (SA kb kk) len =>
      if expr_eqb kb (a_base wa) then prune1p allkn sp wa w wv K hints
      else if ranges_apart_pc allkn sp (a_base wa) k (elen w) br2 kb kk len then ([K], [], hints)
      else match kunk_cut allkn (a_base wa) k (elen w) kb kk len with
           | [] => diffbase (SA kb kk) len
           | cut => (cut, [], hints)
           end
  | KWord (SA kb kk) w' v =>
      if expr_eqb kb (a_base wa) then prune1p allkn sp wa w wv K hints
      else if ranges_apart_pc allkn sp (a_base wa) k (elen w) br2 kb kk (elen w') then ([K], [], hints)
      else if (CXNAT.eqbF w 1 && CXNAT.eqbF w' 1 && expr_eqb wv v)%bool
      then ([K], [], hints)
      else diffbase (SA kb kk) (elen w')
  | KBlob (SA kb kk) len bk =>
      if expr_eqb kb (a_base wa) then prune1p allkn sp wa w wv K hints
      else diffbase (SA kb kk) len
  end.
Lemma L_AX2L_prune1pc : @prune1pc = @AX2.prune1pc.
Proof. unfold prune1pc. rewrite ?L_AX2L_expr_eqb, ?L_AX2L_elen, ?L_AX2L_kzero_cut, ?L_AX2L_kfill_cut, ?L_AX2L_kunk_cut, ?L_AX2L_prune1p, ?L_AX2L_ranges_apart_pc, ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

Fixpoint br_lookup (c : list (expr * option (Z * Z))) (b : expr) : option (option (Z * Z)) :=
  match c with
  | [] => None
  | (b', r) :: rest => if expr_eqb b b' then Some r else br_lookup rest b
  end.
Lemma L_AX2L_br_lookup : @br_lookup = @AX2.br_lookup.
Proof. unfold br_lookup. rewrite ?L_AX2L_expr_eqb. reflexivity. Qed.

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
Lemma L_AX2L_prunepc : @prunepc = @AX2.prunepc.
Proof. unfold prunepc. rewrite ?L_AX2L_base_range, ?L_AX2L_kbase, ?L_AX2L_prune1pc, ?L_AX2L_br_lookup. reflexivity. Qed.

Fixpoint carry (log : list sentry) (kn : list kentry) (hints : list bool)
  : list kentry * list sidecond * list bool :=
  match log with
  | [] => (kn, [], hints)
  | SE a w v :: older =>
      let '(kn1, scs1, hs1) := carry older kn hints in
      let fk := facts_of kn1 in
      let '(kn2, scs2, hs2) := prunepc fk (mk_sprep fk (a_base a) (a_off a) (elen w)) a w v kn1 hs1 [] in   
      (KWord a w v :: kn2, scs1 ++ scs2, hs2)
  end.
Lemma L_AX2L_carry : @carry = @AX2.carry.
Proof. unfold carry. rewrite ?L_AX2L_elen, ?L_AX2L_facts_of, ?L_AX2L_mk_sprep, ?L_AX2L_prunepc. reflexivity. Qed.

End AX2L.
