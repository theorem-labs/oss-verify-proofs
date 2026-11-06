(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import AxSymExec3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
Import AX2.

Module AxScChk.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma land_le_l : forall a b, 0 <= a -> Z.land a b <= a.
Proof.
  intros a b Ha.
  assert (H0 : Z.land (Z.ldiff a b) (Z.land a b) = 0).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.ldiff_spec, Z.land_spec, Z.bits_0.
    destruct (Z.testbit a i), (Z.testbit b i); reflexivity. }
  pose proof (Z.add_nocarry_lor _ _ H0) as H1. rewrite Z.lor_ldiff_and in H1.
  assert (0 <= Z.ldiff a b) by (apply Z.ldiff_nonneg; left; exact Ha). lia.
Qed.
Lemma land_le_r : forall a b, 0 <= b -> Z.land a b <= b.
Proof. intros a b Hb. rewrite Z.land_comm. apply land_le_l. exact Hb. Qed.

Lemma lor_lt64 : forall a b, 0 <= a < 2^64 -> 0 <= b < 2^64 -> 0 <= Z.lor a b < 2^64.
Proof.
  intros a b Ha Hb. split; [apply Z.lor_nonneg; lia|].
  destruct (Z.eq_dec (Z.lor a b) 0) as [->|Hn]; [lia|].
  assert (Hp : 0 < Z.lor a b) by (pose proof (proj2 (Z.lor_nonneg a b) (conj (proj1 Ha) (proj1 Hb))); lia).
  apply Z.log2_lt_pow2; [exact Hp|]. rewrite Z.log2_lor by lia.
  apply Z.max_lub_lt.
  - destruct (Z.eq_dec a 0) as [->|]; [cbn; lia | apply Z.log2_lt_pow2; lia].
  - destruct (Z.eq_dec b 0) as [->|]; [cbn; lia | apply Z.log2_lt_pow2; lia].
Qed.

Lemma shiftr_mono : forall x y k, 0 <= k -> x <= y -> Z.shiftr x k <= Z.shiftr y k.
Proof. intros x y k Hk H. rewrite !Z.shiftr_div_pow2 by lia. apply Z.div_le_mono; [apply Z.pow_pos_nonneg; lia | exact H]. Qed.

Lemma swrap_small : forall n z, 0 < n -> - 2^(n-1) <= z < 2^(n-1) -> bv_swrap (Z.to_N n) z = z.
Proof.
  intros n z Hn Hz. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. rewrite Z2N.id by lia.
  assert (H2 : 2^n = 2 * 2^(n-1)) by (replace n with ((n-1)+1) at 1 by lia; rewrite Z.pow_add_r by lia; lia).
  rewrite H2. replace (Z.div (2 * 2^(n-1)) 2) with (2^(n-1)) by (symmetry; rewrite (Z.mul_comm 2 (2^(n-1))); apply Z.div_mul; lia).
  rewrite Z.mod_small by lia. lia.
Qed.
Lemma swrap_range : forall n z, 0 < n -> - 2^(n-1) <= bv_swrap (Z.to_N n) z < 2^(n-1).
Proof.
  intros n z Hn. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. rewrite Z2N.id by lia.
  assert (H2 : 2^n = 2 * 2^(n-1)) by (replace n with ((n-1)+1) at 1 by lia; rewrite Z.pow_add_r by lia; lia).
  rewrite H2. replace (Z.div (2 * 2^(n-1)) 2) with (2^(n-1)) by (symmetry; rewrite (Z.mul_comm 2 (2^(n-1))); apply Z.div_mul; lia).
  assert (0 < 2^(n-1)) by (apply Z.pow_pos_nonneg; lia).
  pose proof (Z.mod_pos_bound (z + 2^(n-1)) (2 * 2^(n-1)) ltac:(lia)). lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition lf := (Z * list (expr * Z))%type.
Definition iv := (Z * Z)%type.
Definition rfact := (expr * iv)%type.
Definition dfact := (expr * expr * Z)%type.

Fixpoint addm (a : expr) (k : Z) (l : list (expr * Z)) : list (expr * Z) :=
  match l with
  | [] => [(a, k)]
  | (b, j) :: t => if expr_eqb a b then (b, j + k) :: t else (b, j) :: addm a k t
  end.
Definition lf_add (L1 L2 : lf) : lf :=
  (fst L1 + fst L2, fold_right (fun p acc => addm (fst p) (snd p) acc) (snd L2) (snd L1)).
Definition lf_scale (c : Z) (L : lf) : lf := (c * fst L, map (fun p => (fst p, c * snd p)) (snd L)).
Definition lf_sub (L1 L2 : lf) : lf := lf_add L1 (lf_scale (-1) L2).
Definition lf_const (c : Z) : lf := (c, []).
Definition lf_atom (e : expr) : lf := (0, [(e, 1)]).
Definition lf_addc (L : lf) (c : Z) : lf := (fst L + c, snd L).
Definition lf_divides (d : Z) (L : lf) : bool :=
  (fst L mod d =? 0) && forallb (fun p => snd p mod d =? 0) (snd L).
Definition lf_div (d : Z) (L : lf) : lf := (fst L / d, map (fun p => (fst p, snd p / d)) (snd L)).
Fixpoint coef (a : expr) (l : list (expr * Z)) : Z :=
  match l with [] => 0 | (b, j) :: t => if expr_eqb a b then j else coef a t end.

Definition lit_of (e : expr) : option Z := match e with ELit z => Some z | _ => None end.
Definition in64 (i : iv) : bool := (0 <=? fst i) && (snd i <? 2^64).
Definition U64 : iv := (0, 2^64 - 1).
Definition iv_meet (a b : iv) : iv := (Z.max (fst a) (fst b), Z.min (snd a) (snd b)).
Definition iv_scale (k : Z) (i : iv) : iv := if 0 <=? k then (k * fst i, k * snd i) else (k * snd i, k * fst i).
Definition iv_mul (a b : iv) : iv :=
  if fst a =? snd a then iv_scale (fst a) b
  else if fst b =? snd b then iv_scale (fst b) a
  else if (0 <=? fst a) && (0 <=? fst b) then (fst a * fst b, snd a * snd b)
  else let m := Z.max (Z.abs (fst a)) (Z.abs (snd a)) * Z.max (Z.abs (fst b)) (Z.abs (snd b)) in (- m, m).

Fixpoint rf_find (rf : list rfact) (e : expr) : option iv :=
  match rf with [] => None | (x, i) :: t => if expr_eqb e x then Some i else rf_find t e end.

Definition iv_alu (op : aluop) (ia ib : iv) (lb : option Z) : iv :=
  match op with
  | ALU_ADD => (fst ia + fst ib, snd ia + snd ib)
  | ALU_SUB => (fst ia - snd ib, snd ia - fst ib)
  | ALU_AND => (0, Z.min (if in64 ia then snd ia else 2^64 - 1) (if in64 ib then snd ib else 2^64 - 1))
  | ALU_SRL => match lb with
               | Some k => if in64 ia then (Z.shiftr (fst ia) (k mod 64), Z.shiftr (snd ia) (k mod 64)) else U64
               | None => U64
               end
  | ALU_SLL => match lb with
               | Some k => if in64 ia then (fst ia * 2^(k mod 64), snd ia * 2^(k mod 64)) else (0, (2^64 - 1) * 2^63)
               | None => (0, (2^64 - 1) * 2^63)
               end
  | _ => U64
  end.
Definition iv_aluw (op : aluop) (ia ib : iv) : iv :=
  match op with
  | ALU_ADD => if (- 2^31 <=? fst ia + fst ib) && (snd ia + snd ib <? 2^31) then (fst ia + fst ib, snd ia + snd ib)
               else (- 2^31, 2^31 - 1)
  | ALU_SLL => (- 2^31, 2^31 - 1)
  | _ => U64
  end.
Definition iv_md (op : mulop) (ia ib : iv) : iv :=
  match op with M_MUL => iv_mul ia ib | _ => U64 end.
Definition ext_id (sx : bool) (lo n : nat) (ia : iv) : bool :=
  Nat.eqb lo 0 && Nat.leb 1 n && Nat.leb n 8 && (0 <=? fst ia) &&
  (snd ia <? 2^(8 * Z.of_nat n - (if sx then 1 else 0))).
Definition iv_ext (sx : bool) (lo n : nat) (ia : iv) : iv :=
  if ext_id sx lo n ia then ia
  else match n with
       | O => (0, 0)
       | _ => if sx then (- 2^(8 * Z.of_nat n - 1), 2^(8 * Z.of_nat n - 1) - 1) else (0, 2^(8 * Z.of_nat n) - 1)
       end.

Section Chk.
Variable rf : list rfact.
Variable df : list dfact.

Fixpoint iv_of (e : expr) : iv :=
  let s := match e with
           | ELit z => (z, z)
           | EAlu op a b => iv_alu op (iv_of a) (iv_of b) (lit_of b)
           | EAluw op a b => iv_aluw op (iv_of a) (iv_of b)
           | EMd op a b => iv_md op (iv_of a) (iv_of b)
           | EExt sx lo n a => iv_ext sx lo n (iv_of a)
           | _ => U64
           end in
  match rf_find rf e with Some i => iv_meet i s | None => s end.

Definition lf_alu (e : expr) (op : aluop) (la lb : lf) (ia : iv) (kb : option Z) : lf :=
  match op with
  | ALU_ADD => lf_add la lb
  | ALU_SUB => lf_sub la lb
  | ALU_SLL => match kb with
               | Some k => if in64 ia then lf_scale (2^(k mod 64)) la else lf_atom e
               | None => lf_atom e
               end
  | ALU_SRL => match kb with
               | Some k => if in64 ia && lf_divides (2^(k mod 64)) la then lf_div (2^(k mod 64)) la else lf_atom e
               | None => lf_atom e
               end
  | _ => lf_atom e
  end.
Definition lf_md (e : expr) (op : mulop) (la lb : lf) (ka kb : option Z) : lf :=
  match op with
  | M_MUL => match ka, kb with
             | Some k, _ => lf_scale k lb
             | None, Some k => lf_scale k la
             | None, None => lf_atom e
             end
  | _ => lf_atom e
  end.

Fixpoint lf_of (e : expr) : lf :=
  match e with
  | ELit z => lf_const z
  | EAlu op a b => lf_alu e op (lf_of a) (lf_of b) (iv_of a) (lit_of b)
  | EMd op a b => lf_md e op (lf_of a) (lf_of b) (lit_of a) (lit_of b)
  | EAluw ALU_ADD a b =>
      if (- 2^31 <=? fst (iv_of a) + fst (iv_of b)) && (snd (iv_of a) + snd (iv_of b) <? 2^31)
      then lf_add (lf_of a) (lf_of b) else lf_atom e
  | EExt sx lo n a => if ext_id sx lo n (iv_of a) then lf_of a else lf_atom e
  | _ => lf_atom e
  end.

Fixpoint lsum_lo (l : list (expr * Z)) : Z :=
  match l with [] => 0 | (a, k) :: t => fst (iv_scale k (iv_of a)) + lsum_lo t end.
Definition lf_lo (L : lf) : Z := fst L + lsum_lo (snd L).

Fixpoint dif_go (d : list dfact) (L : lf) (acc : Z) : lf * Z :=
  match d with
  | [] => (L, acc)
  | (x, y, g) :: t =>
      let kx := coef x (snd L) in let ky := coef y (snd L) in
      if (0 <? kx) && (ky <? 0) then
        let k := Z.min kx (- ky) in
        dif_go t (fst L, addm x (- k) (addm y k (snd L))) (acc + k * g)
      else dif_go t L acc
  end.
Definition lo_dif (L : lf) : Z := let r := dif_go df L 0 in snd r + lf_lo (fst r).

Definition le0 (L : lf) : bool := 0 <=? lo_dif L.
Definition chk_le (A B : lf) : bool := le0 (lf_sub B A).
Definition chk_lt (A B : lf) : bool := le0 (lf_addc (lf_sub B A) (-1)).
Definition in64L (L : lf) : bool := le0 L && le0 (lf_sub (lf_const (2^64 - 1)) L).
Definition lt63L (L : lf) : bool := le0 (lf_sub (lf_const (2^63 - 1)) L).
Definition uval_of (e : expr) : lf :=
  let L := lf_of e in match snd L with [] => (fst L mod 2^64, []) | _ => L end.

Definition flat_chk (a : saddr) (n : expr) : bool :=
  let B := uval_of (a_base a) in let N := uval_of n in let S := lf_addc B (a_off a) in
  in64L B && in64L N && le0 S && le0 (lf_sub (lf_const (2^64 - 1)) S) && le0 (lf_sub (lf_const (2^64)) (lf_add S N)).
Definition st_of (a : saddr) : lf := lf_addc (uval_of (a_base a)) (a_off a).

Definition raw_eq (a b : expr) : bool := chk_le (lf_of a) (lf_of b) && chk_le (lf_of b) (lf_of a).
Definition br_eqc (t : bool) (c : branch_cond) : bool :=
  match c, t with BC_EQ, true | BC_NE, false => true | _, _ => false end.
Definition br_chk (t : bool) (c : branch_cond) (a b : expr) : bool :=
  (br_eqc t c && raw_eq a b) ||
  let A := uval_of a in let B := uval_of b in
  in64L A && in64L B &&
  match c with
  | BC_EQ => if t then chk_le A B && chk_le B A else chk_lt A B || chk_lt B A
  | BC_NE => if t then chk_lt A B || chk_lt B A else chk_le A B && chk_le B A
  | BC_LTU => if t then chk_lt A B else chk_le B A
  | BC_GEU => if t then chk_le B A else chk_lt A B
  | BC_LT => lt63L A && lt63L B && (if t then chk_lt A B else chk_le B A)
  | BC_GE => lt63L A && lt63L B && (if t then chk_le B A else chk_lt A B)
  end.

Definition sc_chk (s : sidecond) : bool :=
  match s with
  | SCBr t c a b => br_chk t c a b
  | SCFlat a n => flat_chk a n
  | SCDisj a1 n1 a2 n2 =>
      flat_chk a1 n1 && flat_chk a2 n2 &&
      (chk_le (lf_add (st_of a1) (uval_of n1)) (st_of a2) || chk_le (lf_add (st_of a2) (uval_of n2)) (st_of a1))
  | SCInside a1 n1 a2 n2 =>
      flat_chk a2 n2 && in64L (uval_of (a_base a1)) && in64L (uval_of n1) &&
      chk_le (st_of a2) (st_of a1) && chk_le (lf_add (st_of a1) (uval_of n1)) (lf_add (st_of a2) (uval_of n2))
  | SCEq a b => raw_eq a b
  | _ => false
  end.

Fixpoint scs_res (l : list sidecond) : list sidecond :=
  match l with [] => [] | s :: t => if sc_chk s then scs_res t else s :: scs_res t end.
Definition scs_chk (l : list sidecond) : bool := forallb sc_chk l.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Variable E : env.
Definition rf_ok (f : rfact) : Prop := fst (snd f) <= zeval E (fst f) <= snd (snd f).
Definition df_ok (f : dfact) : Prop := snd f <= zeval E (fst (fst f)) - zeval E (snd (fst f)).
Hypothesis Hrf : Forall rf_ok rf.
Hypothesis Hdf : Forall df_ok df.

Fixpoint lsum (l : list (expr * Z)) : Z := match l with [] => 0 | (a, k) :: t => k * zeval E a + lsum t end.
Definition lf_eval (L : lf) : Z := fst L + lsum (snd L).
Definition bnd (i : iv) (z : Z) : Prop := fst i <= z <= snd i.

#[using="Type"] Lemma addm_ok : forall a k l, lsum (addm a k l) = k * zeval E a + lsum l.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros a k l. induction l as [|[b j] t IH]; cbn [addm lsum]; [ring|].
  destruct (expr_eqb a b) eqn:Hab; cbn [lsum].
  - apply expr_eqb_eq in Hab. subst b. ring.
  - rewrite IH. ring.
Qed.
#[using="Type"] Lemma lf_add_ok : forall L1 L2, lf_eval (lf_add L1 L2) = lf_eval L1 + lf_eval L2.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros [c1 l1] [c2 l2]. unfold lf_add, lf_eval. cbn [fst snd].
  induction l1 as [|[a k] t IH]; cbn [fold_right lsum fst snd]; [ring|].
  rewrite addm_ok. lia.
Qed.
#[using="Type"] Lemma lf_scale_ok : forall c L, lf_eval (lf_scale c L) = c * lf_eval L.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros c [c1 l1]. unfold lf_scale, lf_eval. cbn [fst snd].
  induction l1 as [|[a k] t IH]; cbn [map lsum fst snd]; [ring|]. lia.
Qed.
#[using="Type"] Lemma lf_sub_ok : forall L1 L2, lf_eval (lf_sub L1 L2) = lf_eval L1 - lf_eval L2.
Proof. LiaFast.lf_pins LiaFast.u0. intros. unfold lf_sub. rewrite lf_add_ok, lf_scale_ok. ring. Qed.
#[using="Type"] Lemma lf_addc_ok : forall L c, lf_eval (lf_addc L c) = lf_eval L + c.
Proof. LiaFast.lf_pins LiaFast.u0. intros [c1 l1] c. unfold lf_addc, lf_eval. cbn [fst snd]. ring. Qed.
#[using="Type"] Lemma lf_const_ok : forall c, lf_eval (lf_const c) = c.
Proof. LiaFast.lf_pins LiaFast.u0. intros. unfold lf_const, lf_eval. cbn [fst snd lsum]. ring. Qed.
#[using="Type"] Lemma lf_atom_ok : forall e, lf_eval (lf_atom e) = zeval E e.
Proof. LiaFast.lf_pins LiaFast.u0. intros. unfold lf_atom, lf_eval. cbn [fst snd lsum]. ring. Qed.
#[using="Type"] Lemma lf_div_ok : forall d L, 0 < d -> lf_divides d L = true -> lf_eval L = d * lf_eval (lf_div d L).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros d [c l] Hd H. unfold lf_divides in H. cbn [fst snd] in H. apply andb_prop in H as [H1 H2].
  apply Z.eqb_eq in H1. unfold lf_div, lf_eval. cbn [fst snd].
  assert (Hl : lsum l = d * lsum (map (fun p => (fst p, snd p / d)) l)).
  { induction l as [|[a k] t IH]; cbn [map lsum fst snd]; [ring|].
    cbn [forallb snd] in H2. apply andb_prop in H2 as [Hk Ht]. apply Z.eqb_eq in Hk.
    rewrite (IH Ht). rewrite (Z.div_mod k d) at 1 by lia. rewrite Hk. ring. }
  rewrite Hl. rewrite (Z.div_mod c d) at 1 by lia. rewrite H1. ring.
Qed.

#[using="Type"] Lemma iv_scale_ok : forall k i z, bnd i z -> bnd (iv_scale k i) (k * z).
Proof. LiaFast.lf_pins LiaFast.u0. intros k [lo hi] z [H1 H2]. unfold iv_scale, bnd in *. cbn [fst snd] in *. destruct (0 <=? k) eqn:Hk; cbn [fst snd]; [apply Z.leb_le in Hk | apply Z.leb_gt in Hk]; nia. Qed.
#[using="Type"] Lemma iv_mul_ok : forall a b x y, bnd a x -> bnd b y -> bnd (iv_mul a b) (x * y).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros [la ha] [lb hb] x y [Ha1 Ha2] [Hb1 Hb2]. unfold iv_mul. cbn [fst snd] in *.
  destruct (la =? ha) eqn:E1.
  { apply Z.eqb_eq in E1. assert (x = la) by lia. subst x. apply iv_scale_ok. split; assumption. }
  destruct (lb =? hb) eqn:E2.
  { apply Z.eqb_eq in E2. assert (y = lb) by lia. subst y. rewrite Z.mul_comm. apply iv_scale_ok. split; assumption. }
  destruct ((0 <=? la) && (0 <=? lb)) eqn:E3.
  { apply andb_prop in E3 as [P1 P2]. apply Z.leb_le in P1. apply Z.leb_le in P2. unfold bnd. cbn [fst snd]. nia. }
  unfold bnd. cbn [fst snd].
  assert (Hx : Z.abs x <= Z.max (Z.abs la) (Z.abs ha)) by lia.
  assert (Hy : Z.abs y <= Z.max (Z.abs lb) (Z.abs hb)) by lia.
  assert (Hxy : Z.abs (x * y) <= Z.max (Z.abs la) (Z.abs ha) * Z.max (Z.abs lb) (Z.abs hb)).
  { rewrite Z.abs_mul. apply Z.mul_le_mono_nonneg; [apply Z.abs_nonneg | exact Hx | apply Z.abs_nonneg | exact Hy]. }
  apply Z.abs_le. exact Hxy.
Qed.

#[using="Type"] Lemma rf_find_ok_gen : forall l, Forall rf_ok l -> forall e i, rf_find l e = Some i -> bnd i (zeval E e).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros l Hl e i. induction Hl as [|[x j] t Hx Ht IH]; cbn [rf_find]; [discriminate|].
  destruct (expr_eqb e x) eqn:Hex.
  - intros [= <-]. apply expr_eqb_eq in Hex. subst x. exact Hx.
  - exact IH.
Qed.
#[using="Hrf"] Lemma rf_find_ok : forall e i, rf_find rf e = Some i -> bnd i (zeval E e).
Proof. LiaFast.lf_pins (fun (Hrf : LiaFast.U) => LiaFast.u0). exact (rf_find_ok_gen rf Hrf). Qed.

#[using="Type"] Lemma in64_ok : forall i z, in64 i = true -> bnd i z -> 0 <= z < 2^64.
Proof. LiaFast.lf_pins LiaFast.u0. intros [lo hi] z H [H1 H2]. unfold in64 in H. cbn [fst snd] in *. apply andb_prop in H as [A B]. apply Z.leb_le in A. apply Z.ltb_lt in B. lia. Qed.

#[using="Type"] Lemma u_rng : forall w : word, 0 <= bv_unsigned w < 2^64.
Proof. LiaFast.lf_pins LiaFast.u0. intros w. pose proof (bv_unsigned_in_range _ w) as H. change (bv_modulus 64) with (2^64) in H. exact H. Qed.
#[using="Type"] Lemma bnd_U64_u : forall w : word, bnd U64 (bv_unsigned w).
Proof. LiaFast.lf_pins LiaFast.u0. intros w. pose proof (u_rng w). unfold bnd, U64. cbn [fst snd]. lia. Qed.
#[using="Type"] Lemma bnd_U64 : forall z, 0 <= z < 2^64 -> bnd U64 z.
Proof. LiaFast.lf_pins LiaFast.u0. intros z H. unfold bnd, U64. cbn [fst snd]. lia. Qed.

#[using="Type"] Lemma lit_of_eq : forall e k, lit_of e = Some k -> e = ELit k.
Proof. LiaFast.lf_pins LiaFast.u0. intros e k H. destruct e; cbn in H; try discriminate. injection H as ->. reflexivity. Qed.

#[using="Type"] Lemma mod64_pos : forall k, 0 <= k mod 64 < 64.
Proof. LiaFast.lf_pins LiaFast.u0. intros. apply Z.mod_pos_bound. lia. Qed.

#[using="Type"] Lemma iv_alu_ok : forall op a b ia ib, bnd ia (zeval E a) -> bnd ib (zeval E b) ->
  bnd (iv_alu op ia ib (lit_of b)) (zeval E (EAlu op a b)).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros op a b ia ib Ha Hb.
  destruct op; cbn [iv_alu]; try (cbn [zeval]; apply bnd_U64_u).
  - (* [comment removed for export] *) cbn [zeval]. destruct Ha, Hb. unfold bnd. cbn [fst snd]. lia.
  - (* [comment removed for export] *) cbn [zeval]. destruct Ha, Hb. unfold bnd. cbn [fst snd]. lia.
  - (* [comment removed for export] *) cbn [zeval].
    pose proof (Z.mod_pos_bound (zeval E a) (2^64) ltac:(lia)) as Hm.
    pose proof (mod64_pos (zeval E b)) as Hs.
    rewrite Z.shiftl_mul_pow2 by lia.
    assert (Hp : 0 < 2 ^ (zeval E b mod 64) <= 2^63).
    { split; [apply Z.pow_pos_nonneg; lia | apply Z.pow_le_mono_r; lia]. }
    destruct (lit_of b) as [k|] eqn:Hl.
    + apply lit_of_eq in Hl. subst b. cbn [zeval] in *.
      destruct (in64 ia) eqn:Hi.
      * pose proof (in64_ok _ _ Hi Ha) as H64. rewrite (Z.mod_small (zeval E a)) by lia. destruct Ha as [Ha1 Ha2]. unfold bnd. cbn [fst snd].
        generalize dependent (2 ^ (k mod 64)). intros P HP. split; apply Z.mul_le_mono_nonneg_r; lia.
      * unfold bnd. cbn [fst snd]. generalize dependent (2 ^ (k mod 64)). generalize dependent (zeval E a mod 2^64). intros X HX P HP.
        split; [apply Z.mul_nonneg_nonneg; lia | apply Z.mul_le_mono_nonneg; lia].
    + unfold bnd. cbn [fst snd]. generalize dependent (2 ^ (zeval E b mod 64)). generalize dependent (zeval E a mod 2^64). intros X HX P HP.
      split; [apply Z.mul_nonneg_nonneg; lia | apply Z.mul_le_mono_nonneg; lia].
  - (* [comment removed for export] *) cbn [zeval].
    pose proof (Z.mod_pos_bound (zeval E a) (2^64) ltac:(lia)) as Hm.
    pose proof (mod64_pos (zeval E b)) as Hs.
    assert (HU : bnd U64 (Z.shiftr (zeval E a mod 2 ^ 64) (zeval E b mod 64))).
    { apply bnd_U64. split; [apply Z.shiftr_nonneg; lia|].
      rewrite Z.shiftr_div_pow2 by lia.
      assert (0 < 2 ^ (zeval E b mod 64)) by (apply Z.pow_pos_nonneg; lia).
      apply Z.le_lt_trans with (zeval E a mod 2^64); [|lia]. apply Z.div_le_upper_bound; nia. }
    destruct (lit_of b) as [k|] eqn:Hl; [|exact HU].
    apply lit_of_eq in Hl. subst b. cbn [zeval] in *.
    destruct (in64 ia) eqn:Hi; [|exact HU].
    pose proof (in64_ok _ _ Hi Ha) as H64. rewrite (Z.mod_small (zeval E a)) by lia. destruct Ha. unfold bnd. cbn [fst snd].
    split; apply shiftr_mono; lia.
  - (* [comment removed for export] *) cbn [zeval]. apply bnd_U64. apply lor_lt64; apply Z.mod_pos_bound; lia.
  - (* [comment removed for export] *) cbn [zeval].
    pose proof (Z.mod_pos_bound (zeval E a) (2^64) ltac:(lia)) as Hma.
    pose proof (Z.mod_pos_bound (zeval E b) (2^64) ltac:(lia)) as Hmb.
    unfold bnd. cbn [fst snd]. split; [apply Z.land_nonneg; lia|].
    apply Z.min_glb.
    + apply Z.le_trans with (zeval E a mod 2^64); [apply land_le_l; lia|].
      destruct (in64 ia) eqn:Hi; [|lia]. pose proof (in64_ok _ _ Hi Ha). rewrite Z.mod_small by lia. destruct Ha; lia.
    + apply Z.le_trans with (zeval E b mod 2^64); [apply land_le_r; lia|].
      destruct (in64 ib) eqn:Hi; [|lia]. pose proof (in64_ok _ _ Hi Hb). rewrite Z.mod_small by lia. destruct Hb; lia.
Qed.

#[using="Type"] Lemma iv_aluw_ok : forall op a b ia ib, bnd ia (zeval E a) -> bnd ib (zeval E b) ->
  bnd (iv_aluw op ia ib) (zeval E (EAluw op a b)).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros op a b ia ib Ha Hb.
  destruct op; cbn [iv_aluw]; try (cbn [zeval]; apply bnd_U64_u).
  - (* [comment removed for export] *) cbn [zeval].
    destruct ((- 2 ^ 31 <=? fst ia + fst ib) && (snd ia + snd ib <? 2 ^ 31)) eqn:Hc.
    + apply andb_prop in Hc as [C1 C2]. apply Z.leb_le in C1. apply Z.ltb_lt in C2. destruct Ha, Hb.
      change 32%N with (Z.to_N 32). rewrite swrap_small by (change (2^(32-1)) with (2^31); lia).
      unfold bnd. cbn [fst snd]. lia.
    + pose proof (swrap_range 32 (zeval E a + zeval E b) ltac:(lia)) as H. change (Z.to_N 32) with 32%N in H.
      change (2^(32-1)) with (2^31) in H. unfold bnd. cbn [fst snd]. lia.
  - (* [comment removed for export] *) cbn [zeval].
    pose proof (swrap_range 32 (Z.shiftl (zeval E a mod 2 ^ 64) (zeval E b mod 32)) ltac:(lia)) as H.
    change (Z.to_N 32) with 32%N in H. change (2^(32-1)) with (2^31) in H. unfold bnd. cbn [fst snd]. lia.
Qed.

#[using="Type"] Lemma iv_md_ok : forall op a b ia ib, bnd ia (zeval E a) -> bnd ib (zeval E b) ->
  bnd (iv_md op ia ib) (zeval E (EMd op a b)).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros op a b ia ib Ha Hb. destruct op; cbn [iv_md]; try (cbn [zeval]; apply bnd_U64_u).
  cbn [zeval]. apply iv_mul_ok; assumption.
Qed.

#[using="Type"] Lemma ext_id_ok : forall sx lo n ia z, ext_id sx lo n ia = true -> bnd ia z -> ext_Z sx lo n (z mod 2^64) = z.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros sx lo n [l h] z H [B1 B2]. unfold ext_id in H. cbn [fst snd] in *.
  repeat (apply andb_prop in H as [H ?]).
  apply Nat.eqb_eq in H. subst lo.
  match goal with H : Nat.leb 1 n = true |- _ => apply Nat.leb_le in H end.
  match goal with H : Nat.leb n 8 = true |- _ => apply Nat.leb_le in H end.
  match goal with H : (0 <=? l) = true |- _ => apply Z.leb_le in H end.
  match goal with H : (h <? _) = true |- _ => apply Z.ltb_lt in H end.
  assert (Hn : 8 <= 8 * Z.of_nat n <= 64) by lia.
  assert (Hp : 2^(8 * Z.of_nat n - (if sx then 1 else 0)) <= 2^(8 * Z.of_nat n)) by (apply Z.pow_le_mono_r; destruct sx; lia).
  assert (Hq : 2^(8 * Z.of_nat n) <= 2^64) by (apply Z.pow_le_mono_r; lia).
  unfold ext_Z. cbn [Nat.mul Z.of_nat]. change (8 * 0) with 0. rewrite Z.pow_0_r, Z.div_1_r.
  rewrite (Z.mod_small z (2^64)) by lia. rewrite (Z.mod_small z) by lia.
  destruct sx; [|reflexivity].
  replace (8 * N.of_nat n)%N with (Z.to_N (8 * Z.of_nat n)) by lia.
  apply swrap_small; lia.
Qed.

#[using="Type"] Lemma ext_Z_n0 : forall sx lo z, ext_Z sx lo 0 z = 0.
Proof. LiaFast.lf_pins LiaFast.u0. intros. unfold ext_Z. cbn [Z.of_nat]. change (8 * 0) with 0. rewrite Z.pow_0_r, Z.mod_1_r. destruct sx; reflexivity. Qed.

#[using="Type"] Lemma iv_ext_ok : forall sx lo n a ia, bnd ia (zeval E a) -> bnd (iv_ext sx lo n ia) (zeval E (EExt sx lo n a)).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros sx lo n a ia Ha. cbn [zeval]. unfold iv_ext.
  destruct (ext_id sx lo n ia) eqn:Hid.
  { rewrite (ext_id_ok _ _ _ _ _ Hid Ha). exact Ha. }
  destruct n as [|n'].
  { rewrite ext_Z_n0. unfold bnd. cbn [fst snd]. lia. }
  assert (Hn : 0 < 8 * Z.of_nat (S n')) by lia.
  unfold ext_Z.
  set (u := (zeval E a mod 2 ^ 64 / 2 ^ (8 * Z.of_nat lo)) mod 2 ^ (8 * Z.of_nat (S n'))).
  destruct sx.
  - replace (8 * N.of_nat (S n'))%N with (Z.to_N (8 * Z.of_nat (S n'))) by lia.
    pose proof (swrap_range (8 * Z.of_nat (S n')) u Hn). unfold bnd. cbn [fst snd]. lia.
  - pose proof (Z.mod_pos_bound (zeval E a mod 2 ^ 64 / 2 ^ (8 * Z.of_nat lo)) (2 ^ (8 * Z.of_nat (S n'))) ltac:(apply Z.pow_pos_nonneg; lia)) as H.
    fold u in H. unfold bnd. cbn [fst snd]. lia.
Qed.

#[using="Type"] Lemma iv_meet_ok : forall i j z, bnd i z -> bnd j z -> bnd (iv_meet i j) z.
Proof. LiaFast.lf_pins LiaFast.u0. intros [a b] [c d] z [H1 H2] [H3 H4]. unfold iv_meet, bnd. cbn [fst snd] in *. lia. Qed.

#[using="Hrf"] Lemma iv_of_ok : forall e, bnd (iv_of e) (zeval E e).
Proof. LiaFast.lf_pins (fun (Hrf : LiaFast.U) => LiaFast.u0).
  assert (W : forall e s, bnd s (zeval E e) ->
                bnd (match rf_find rf e with Some i => iv_meet i s | None => s end) (zeval E e)).
  { intros e s Hs. destruct (rf_find rf e) as [i|] eqn:Hf; [|exact Hs]. apply iv_meet_ok; [apply rf_find_ok; exact Hf | exact Hs]. }
  induction e; cbn [iv_of]; apply W.
  - unfold bnd. cbn [zeval fst snd]. lia.
  - cbn [zeval]. apply bnd_U64_u.
  - apply iv_alu_ok; assumption.
  - apply iv_aluw_ok; assumption.
  - apply iv_md_ok; assumption.
  - cbn [zeval]. apply bnd_U64_u.
  - apply iv_ext_ok; assumption.
  - cbn [zeval]. apply bnd_U64_u.
Qed.

#[using="Hrf"] Lemma lf_alu_ok : forall op a b, lf_eval (lf_of a) = zeval E a -> lf_eval (lf_of b) = zeval E b ->
  lf_eval (lf_alu (EAlu op a b) op (lf_of a) (lf_of b) (iv_of a) (lit_of b)) = zeval E (EAlu op a b).
Proof. LiaFast.lf_pins (fun (Hrf : LiaFast.U) => LiaFast.u0).
  intros op a b Ha Hb. destruct op; cbn [lf_alu]; try apply lf_atom_ok.
  - rewrite lf_add_ok, Ha, Hb. reflexivity.
  - rewrite lf_sub_ok, Ha, Hb. reflexivity.
  - (* [comment removed for export] *) destruct (lit_of b) as [k|] eqn:Hl; [|apply lf_atom_ok].
    destruct (in64 (iv_of a)) eqn:Hi; [|apply lf_atom_ok].
    apply lit_of_eq in Hl. subst b. cbn [zeval].
    pose proof (in64_ok _ _ Hi (iv_of_ok a)) as H64. pose proof (mod64_pos k).
    rewrite lf_scale_ok, Ha. rewrite (Z.mod_small (zeval E a)) by lia. rewrite Z.shiftl_mul_pow2 by lia. ring.
  - (* [comment removed for export] *) destruct (lit_of b) as [k|] eqn:Hl; [|apply lf_atom_ok].
    destruct (in64 (iv_of a) && lf_divides (2 ^ (k mod 64)) (lf_of a)) eqn:Hc; [|apply lf_atom_ok].
    apply andb_prop in Hc as [Hi Hd]. apply lit_of_eq in Hl. subst b. cbn [zeval].
    pose proof (in64_ok _ _ Hi (iv_of_ok a)) as H64. pose proof (mod64_pos k).
    assert (Hp : 0 < 2 ^ (k mod 64)) by (apply Z.pow_pos_nonneg; lia).
    rewrite (Z.mod_small (zeval E a)) by lia. rewrite Z.shiftr_div_pow2 by lia.
    rewrite <- Ha. rewrite (lf_div_ok _ _ Hp Hd). rewrite Z.mul_comm, Z.div_mul by lia. reflexivity.
Qed.

#[using="Type"] Lemma lf_md_ok : forall op a b, lf_eval (lf_of a) = zeval E a -> lf_eval (lf_of b) = zeval E b ->
  lf_eval (lf_md (EMd op a b) op (lf_of a) (lf_of b) (lit_of a) (lit_of b)) = zeval E (EMd op a b).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros op a b Ha Hb. destruct op; cbn [lf_md]; try apply lf_atom_ok.
  destruct (lit_of a) as [k|] eqn:Hla.
  { apply lit_of_eq in Hla. subst a. cbn [zeval]. rewrite lf_scale_ok, Hb. reflexivity. }
  destruct (lit_of b) as [k|] eqn:Hlb; [|apply lf_atom_ok].
  apply lit_of_eq in Hlb. subst b. cbn [zeval]. rewrite lf_scale_ok, Ha. ring.
Qed.

#[using="Hrf"] Lemma lf_of_ok : forall e, lf_eval (lf_of e) = zeval E e.
Proof. LiaFast.lf_pins (fun (Hrf : LiaFast.U) => LiaFast.u0).
  induction e; cbn [lf_of]; try apply lf_atom_ok.
  - apply lf_const_ok.
  - apply lf_alu_ok; assumption.
  - destruct op; try apply lf_atom_ok.
    destruct ((- 2 ^ 31 <=? fst (iv_of e1) + fst (iv_of e2)) && (snd (iv_of e1) + snd (iv_of e2) <? 2 ^ 31)) eqn:Hc; [|apply lf_atom_ok].
    apply andb_prop in Hc as [C1 C2]. apply Z.leb_le in C1. apply Z.ltb_lt in C2.
    pose proof (iv_of_ok e1) as [A1 A2]. pose proof (iv_of_ok e2) as [B1 B2].
    rewrite lf_add_ok, IHe1, IHe2. cbn [zeval]. change 32%N with (Z.to_N 32).
    rewrite swrap_small by (change (2^(32-1)) with (2^31); lia). reflexivity.
  - apply lf_md_ok; assumption.
  - destruct (ext_id sx lo n (iv_of e)) eqn:Hid; [|apply lf_atom_ok].
    rewrite IHe. cbn [zeval]. symmetry. apply (ext_id_ok _ _ _ _ _ Hid (iv_of_ok e)).
Qed.

#[using="Hrf"] Lemma lsum_lo_ok : forall l, lsum_lo l <= lsum l.
Proof. LiaFast.lf_pins (fun (Hrf : LiaFast.U) => LiaFast.u0).
  induction l as [|[a k] t IH]; cbn [lsum_lo lsum]; [lia|].
  pose proof (iv_scale_ok k _ _ (iv_of_ok a)) as [H _]. lia.
Qed.
#[using="Hrf"] Lemma lf_lo_ok : forall L, lf_lo L <= lf_eval L.
Proof. LiaFast.lf_pins (fun (Hrf : LiaFast.U) => LiaFast.u0). intros [c l]. unfold lf_lo, lf_eval. cbn [fst snd]. pose proof (lsum_lo_ok l). lia. Qed.

#[using="Type"] Lemma dif_go_ok : forall d, Forall df_ok d -> forall L acc,
  snd (dif_go d L acc) + lf_eval (fst (dif_go d L acc)) <= acc + lf_eval L.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros d Hd. induction Hd as [|[[x y] g] t Hx Ht IH]; intros L acc; cbn [dif_go]; [cbn [fst snd]; lia|].
  destruct ((0 <? coef x (snd L)) && (coef y (snd L) <? 0)) eqn:Hc; [|apply IH].
  apply andb_prop in Hc as [C1 C2]. apply Z.ltb_lt in C1. apply Z.ltb_lt in C2.
  set (k := Z.min (coef x (snd L)) (- coef y (snd L))).
  assert (Hk : 0 <= k) by (unfold k; lia).
  eapply Z.le_trans; [apply IH|].
  unfold lf_eval at 1. cbn [fst snd]. rewrite !addm_ok. unfold lf_eval.
  unfold df_ok in Hx. cbn [fst snd] in Hx. nia.
Qed.
#[using="Hrf Hdf"] Lemma lo_dif_ok : forall L, lo_dif L <= lf_eval L.
Proof. LiaFast.lf_pins (fun (Hrf Hdf : LiaFast.U) => LiaFast.u0).
  intros L. unfold lo_dif. pose proof (dif_go_ok df Hdf L 0) as H.
  pose proof (lf_lo_ok (fst (dif_go df L 0))). lia.
Qed.
#[using="Hrf Hdf"] Lemma le0_ok : forall L, le0 L = true -> 0 <= lf_eval L.
Proof. LiaFast.lf_pins (fun (Hrf Hdf : LiaFast.U) => LiaFast.u0). intros L H. unfold le0 in H. apply Z.leb_le in H. pose proof (lo_dif_ok L). lia. Qed.
#[using="Hrf Hdf"] Lemma chk_le_ok : forall A B, chk_le A B = true -> lf_eval A <= lf_eval B.
Proof. LiaFast.lf_pins (fun (Hrf Hdf : LiaFast.U) => LiaFast.u0). intros A B H. apply le0_ok in H. rewrite lf_sub_ok in H. lia. Qed.
#[using="Hrf Hdf"] Lemma chk_lt_ok : forall A B, chk_lt A B = true -> lf_eval A < lf_eval B.
Proof. LiaFast.lf_pins (fun (Hrf Hdf : LiaFast.U) => LiaFast.u0). intros A B H. apply le0_ok in H. rewrite lf_addc_ok, lf_sub_ok in H. lia. Qed.
#[using="Hrf Hdf"] Lemma in64L_ok : forall L, in64L L = true -> 0 <= lf_eval L < 2^64.
Proof. LiaFast.lf_pins (fun (Hrf Hdf : LiaFast.U) => LiaFast.u0).
  intros L H. unfold in64L in H. apply andb_prop in H as [H1 H2]. apply le0_ok in H1. apply le0_ok in H2.
  rewrite lf_sub_ok, lf_const_ok in H2. lia.
Qed.
#[using="Hrf Hdf"] Lemma lt63L_ok : forall L, lt63L L = true -> lf_eval L < 2^63.
Proof. LiaFast.lf_pins (fun (Hrf Hdf : LiaFast.U) => LiaFast.u0). intros L H. unfold lt63L in H. apply le0_ok in H. rewrite lf_sub_ok, lf_const_ok in H. lia. Qed.

#[using="Hrf"] Lemma uval_of_eqm : forall e, lf_eval (uval_of e) mod 2^64 = zeval E e mod 2^64.
Proof. LiaFast.lf_pins (fun (Hrf : LiaFast.U) => LiaFast.u0).
  intros e. unfold uval_of. pose proof (lf_of_ok e) as H. destruct (lf_of e) as [c l]. cbn [fst snd].
  destruct l as [|p t]; [|rewrite H; reflexivity].
  unfold lf_eval in *. cbn [fst snd lsum] in *. rewrite Z.add_0_r in *. subst c. apply Z.mod_mod. lia.
Qed.
#[using="Hrf Hdf"] Lemma uval_of_u : forall e, in64L (uval_of e) = true -> bv_unsigned (edenot E e) = lf_eval (uval_of e).
Proof. LiaFast.lf_pins (fun (Hrf Hdf : LiaFast.U) => LiaFast.u0).
  intros e H. apply in64L_ok in H. rewrite zeval_sound, u_wa, <- uval_of_eqm. apply Z.mod_small. exact H.
Qed.

#[using="Hrf Hdf"] Lemma flat_chk_ok : forall a n, flat_chk a n = true ->
  flat E a (elenZ E n) /\ estart E a = lf_eval (st_of a) /\ elenZ E n = lf_eval (uval_of n).
Proof. LiaFast.lf_pins (fun (Hrf Hdf : LiaFast.U) => LiaFast.u0).
  intros a n H. unfold flat_chk in H. cbv zeta in H.
  apply andb_prop in H as [H H5]. apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply le0_ok in H5. rewrite lf_sub_ok, lf_const_ok, lf_add_ok, lf_addc_ok in H5.
  apply le0_ok in H4. rewrite lf_sub_ok, lf_const_ok, lf_addc_ok in H4.
  apply le0_ok in H3. rewrite lf_addc_ok in H3.
  pose proof (uval_of_u _ H2) as HN. apply in64L_ok in H2.
  pose proof (uval_of_u _ H1) as HB. apply in64L_ok in H1.
  assert (Hs : estart E a = lf_eval (st_of a)) by (unfold estart, st_of; rewrite lf_addc_ok, HB; reflexivity).
  assert (Hn : elenZ E n = lf_eval (uval_of n)) by (unfold elenZ; exact HN).
  split; [|split; assumption]. unfold flat. rewrite Hs, Hn. unfold st_of. rewrite lf_addc_ok. lia.
Qed.

#[using="Type"] Lemma signed_small : forall z, 0 <= z < 2^63 -> bv_signed (wa z) = z.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros z H. unfold bv_signed. rewrite u_wa, Z.mod_small by lia. change 64%N with (Z.to_N 64).
  apply swrap_small; [lia|]. change (2^(64-1)) with (2^63). lia.
Qed.

#[using="Hrf Hdf"] Lemma br_chk_ok : forall t c a b, br_chk t c a b = true -> branch_taken c (edenot E a) (edenot E b) = t.
Proof. LiaFast.lf_pins (fun (Hrf Hdf : LiaFast.U) => LiaFast.u0).
  intros t c a b H. unfold br_chk in H. apply orb_prop in H as [H|H].
  { apply andb_prop in H as [Hc Hr]. unfold raw_eq in Hr. apply andb_prop in Hr as [C1 C2].
    apply chk_le_ok in C1. apply chk_le_ok in C2. rewrite !lf_of_ok in *.
    assert (He : edenot E a = edenot E b) by (rewrite !zeval_sound; f_equal; lia).
    destruct c, t; try discriminate Hc; cbn [branch_taken]; unfold bv_eqb; rewrite He, Z.eqb_refl; reflexivity. }
  cbv zeta in H. apply andb_prop in H as [H Hc]. apply andb_prop in H as [HA HB].
  pose proof (uval_of_u _ HA) as UA. pose proof (uval_of_u _ HB) as UB.
  apply in64L_ok in HA. apply in64L_ok in HB.
  set (A := lf_eval (uval_of a)) in *. set (B := lf_eval (uval_of b)) in *.
  assert (SA : lt63L (uval_of a) = true -> bv_signed (edenot E a) = A).
  { intros H63. apply lt63L_ok in H63. fold A in H63. rewrite <- (wa_u (edenot E a)), UA. apply signed_small. lia. }
  assert (SB : lt63L (uval_of b) = true -> bv_signed (edenot E b) = B).
  { intros H63. apply lt63L_ok in H63. fold B in H63. rewrite <- (wa_u (edenot E b)), UB. apply signed_small. lia. }
  destruct c; cbn [branch_taken]; unfold bv_eqb, bv_ltu, bv_lts; rewrite ?UA, ?UB.
  - (* [comment removed for export] *) destruct t.
    + apply andb_prop in Hc as [C1 C2]. apply chk_le_ok in C1. apply chk_le_ok in C2. fold A B in C1, C2. apply Z.eqb_eq. lia.
    + apply Z.eqb_neq. apply orb_prop in Hc as [C|C]; apply chk_lt_ok in C; fold A B in C; lia.
  - (* [comment removed for export] *) destruct t.
    + apply negb_true_iff, Z.eqb_neq. apply orb_prop in Hc as [C|C]; apply chk_lt_ok in C; fold A B in C; lia.
    + apply andb_prop in Hc as [C1 C2]. apply chk_le_ok in C1. apply chk_le_ok in C2. fold A B in C1, C2. apply negb_false_iff, Z.eqb_eq. lia.
  - (* [comment removed for export] *) apply andb_prop in Hc as [Hc C]. apply andb_prop in Hc as [H1 H2]. rewrite (SA H1), (SB H2). destruct t.
    + apply chk_lt_ok in C. fold A B in C. apply Z.ltb_lt. lia.
    + apply chk_le_ok in C. fold A B in C. apply Z.ltb_ge. lia.
  - (* [comment removed for export] *) apply andb_prop in Hc as [Hc C]. apply andb_prop in Hc as [H1 H2]. rewrite (SA H1), (SB H2). destruct t.
    + apply chk_le_ok in C. fold A B in C. apply negb_true_iff, Z.ltb_ge. lia.
    + apply chk_lt_ok in C. fold A B in C. apply negb_false_iff, Z.ltb_lt. lia.
  - (* [comment removed for export] *) destruct t.
    + apply chk_lt_ok in Hc. fold A B in Hc. apply Z.ltb_lt. lia.
    + apply chk_le_ok in Hc. fold A B in Hc. apply Z.ltb_ge. lia.
  - (* [comment removed for export] *) destruct t.
    + apply chk_le_ok in Hc. fold A B in Hc. apply negb_true_iff, Z.ltb_ge. lia.
    + apply chk_lt_ok in Hc. fold A B in Hc. apply negb_false_iff, Z.ltb_lt. lia.
Qed.

#[using="Hrf Hdf"] Lemma sc_chk_ok : forall segs base s, sc_chk s = true -> sc_denot segs base E s.
Proof. LiaFast.lf_pins (fun (Hrf Hdf : LiaFast.U) => LiaFast.u0).
  intros segs base s H. destruct s; cbn [sc_chk] in H; try discriminate; cbn [sc_denot].
  - apply br_chk_ok. exact H.
  - apply flat_chk_ok in H. tauto.
  - apply andb_prop in H as [H Hd]. apply andb_prop in H as [F1 F2].
    apply flat_chk_ok in F1 as (F1 & S1 & N1). apply flat_chk_ok in F2 as (F2 & S2 & N2).
    split; [exact F1|]. split; [exact F2|]. rewrite S1, S2, N1, N2.
    apply orb_prop in Hd as [C|C]; apply chk_le_ok in C; rewrite lf_add_ok in C; [left|right]; exact C.
  - apply andb_prop in H as [H C2]. apply andb_prop in H as [H C1]. apply andb_prop in H as [H HN1r]. apply andb_prop in H as [H HB1r].
    apply flat_chk_ok in H as (F2 & S2 & N2).
    pose proof (uval_of_u _ HB1r) as HB1. pose proof (uval_of_u _ HN1r) as HN1. apply in64L_ok in HN1r.
    assert (S1 : estart E a1 = lf_eval (st_of a1)) by (unfold estart, st_of; rewrite lf_addc_ok, HB1; reflexivity).
    assert (N1 : elenZ E n1 = lf_eval (uval_of n1)) by (unfold elenZ; exact HN1).
    apply chk_le_ok in C1. apply chk_le_ok in C2. rewrite !lf_add_ok in C2.
    split; [exact F2|]. rewrite S1, S2, N1, N2. lia.
  - unfold raw_eq in H. apply andb_prop in H as [C1 C2]. apply chk_le_ok in C1. apply chk_le_ok in C2. rewrite !lf_of_ok in *.
    rewrite !zeval_sound. f_equal. lia.
Qed.

#[using="Hrf Hdf"] Theorem scs_res_sound : forall segs base l, scs_denot segs base E (scs_res l) -> scs_denot segs base E l.
Proof. LiaFast.lf_pins (fun (Hrf Hdf : LiaFast.U) => LiaFast.u0).
  intros segs base l. unfold scs_denot. induction l as [|s t IH]; cbn [scs_res]; [auto|].
  destruct (sc_chk s) eqn:Hs; intros H.
  - constructor; [apply sc_chk_ok; exact Hs | apply IH; exact H].
  - inversion H; subst. constructor; [assumption | apply IH; assumption].
Qed.
#[using="Hrf Hdf"] Theorem scs_chk_sound : forall segs base l, scs_chk l = true -> scs_denot segs base E l.
Proof. LiaFast.lf_pins (fun (Hrf Hdf : LiaFast.U) => LiaFast.u0).
  intros segs base l H. unfold scs_denot. unfold scs_chk in H. rewrite forallb_forall in H.
  apply Forall_forall. intros s Hs. apply sc_chk_ok. apply H. exact Hs.
Qed.
End Chk.
(* [comment removed for export] *)
End AxScChk.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Lemma testbit_pow2 : forall n k, 0 <= n -> 0 <= k -> Z.testbit (2^n) k = (n =? k).
Proof.
  intros n k Hn Hk. rewrite <- (Z.shiftl_1_l n), Z.shiftl_spec by lia.
  destruct (Z.eqb_spec n k) as [->|Hne].
  - rewrite Z.sub_diag. reflexivity.
  - destruct (Z.lt_ge_cases (k - n) 0) as [Hl|Hg].
    + apply Z.testbit_neg_r. lia.
    + rewrite Z.bits_above_log2; [reflexivity | lia |]. apply Z.log2_lt_pow2; [lia|].
      apply Z.lt_le_trans with (2^1)%Z; [simpl; lia|]. apply Z.pow_le_mono_r; lia.
Qed.

Lemma testbit_high : forall n a k, 0 <= n -> 0 <= a < 2^n -> n <= k -> Z.testbit a k = false.
Proof.
  intros n a k Hn Ha Hk. destruct (Z.eq_dec a 0) as [->|Hnz]; [apply Z.bits_0|].
  apply Z.bits_above_log2; [lia|]. apply Z.log2_lt_pow2; [lia|].
  apply Z.lt_le_trans with (2^n); [lia | apply Z.pow_le_mono_r; lia].
Qed.

Lemma testbit_add_shifted : forall a m k n, 0 <= n -> 0 <= a < 2^n -> 0 <= m -> 0 <= k ->
  Z.testbit (a + 2^n * m) k = if k <? n then Z.testbit a k else Z.testbit m (k - n).
Proof.
  intros a m k n Hn Ha Hm Hk.
  assert (Hd : Z.land a (2^n * m) = 0).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
    destruct (Z.lt_ge_cases i n) as [Hl|Hg].
    - replace (2^n * m) with (Z.shiftl m n) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
      rewrite Z.shiftl_spec_low by lia. apply andb_false_r.
    - rewrite (testbit_high n a i) by lia. reflexivity. }
  rewrite (Z.add_nocarry_lxor a (2^n * m) Hd). rewrite Z.lxor_spec.
  replace (2^n * m) with (Z.shiftl m n) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
  destruct (Z.ltb_spec k n) as [Hl|Hg].
  - rewrite Z.shiftl_spec_low by lia. apply xorb_false_r.
  - rewrite Z.shiftl_spec by lia. rewrite (testbit_high n a k) by lia. reflexivity.
Qed.

Lemma testbit31_iff : forall u, 0 <= u < 2^32 -> Z.testbit u 31 = (2^31 <=? u).
Proof.
  intros u Hu. destruct (Z.leb_spec (2^31) u) as [Hg|Hl].
  - apply Z.testbit_true; [lia|].
    assert (E : u / 2^31 = 1) by (symmetry; apply Z.div_unique with (r := u - 2^31); lia). rewrite E. reflexivity.
  - apply (testbit_high 31); lia.
Qed.

Lemma swrap32_eq_mod : forall x, bv_swrap 32 x = bv_swrap 32 (x mod 2^32).
Proof. intros. apply swrap32_eqm. rewrite Z.mod_mod by lia. reflexivity. Qed.

Lemma swrap32_mod : forall x, bv_swrap 32 x mod 2^32 = x mod 2^32.
Proof.
  intros x. unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2^31). change (bv_modulus 32) with (2^32).
  rewrite Zminus_mod. rewrite Z.mod_mod by lia. rewrite <- Zminus_mod. f_equal. lia.
Qed.

(* [comment removed for export] *)
Lemma sx32_val : forall x, bv_swrap 32 x mod 2^64 =
  if Z.testbit x 31 then x mod 2^32 + 2^32 * (2^32 - 1) else x mod 2^32.
Proof.
  intros x. rewrite swrap32_eq_mod.
  assert (Hu : 0 <= x mod 2^32 < 2^32) by (apply Z.mod_pos_bound; lia).
  replace (Z.testbit x 31) with (Z.testbit (x mod 2^32) 31) by (apply Z.mod_pow2_bits_low; lia).
  rewrite testbit31_iff by exact Hu. set (u := x mod 2^32) in *.
  unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2^31). change (bv_modulus 32) with (2^32).
  destruct (Z.leb_spec (2^31) u) as [Hg|Hl].
  - rewrite <- (Z.mod_unique (u + 2^31) (2^32) 1 (u + 2^31 - 2^32)) by lia.
    rewrite <- (Z.mod_unique (u + 2^31 - 2^32 - 2^31) (2^64) (-1) (u + 2^32 * (2^32 - 1))) by lia. reflexivity.
  - rewrite (Z.mod_small (u + 2^31)) by lia. rewrite Z.mod_small by lia. lia.
Qed.

Lemma testbit_sx32 : forall x k, 0 <= k ->
  Z.testbit (bv_swrap 32 x mod 2^64) k = (k <? 64) && Z.testbit x (Z.min k 31).
Proof.
  intros x k Hk. rewrite sx32_val.
  assert (Hu : 0 <= x mod 2^32 < 2^32) by (apply Z.mod_pos_bound; lia).
  destruct (Z.ltb_spec k 32) as [Hl|Hg].
  - replace (Z.min k 31) with k by lia. replace (k <? 64) with true by (symmetry; apply Z.ltb_lt; lia).
    cbn [andb]. destruct (Z.testbit x 31).
    + rewrite testbit_add_shifted by lia. replace (k <? 32) with true by (symmetry; apply Z.ltb_lt; lia).
      apply Z.mod_pow2_bits_low; lia.
    + apply Z.mod_pow2_bits_low; lia.
  - replace (Z.min k 31) with 31 by lia. destruct (Z.testbit x 31) eqn:Hb.
    + rewrite testbit_add_shifted by lia. replace (k <? 32) with false by (symmetry; apply Z.ltb_ge; lia).
      replace (2^32 - 1) with (Z.ones 32) by reflexivity. rewrite Z.testbit_ones by lia. rewrite andb_true_r.
      destruct (Z.leb_spec 0 (k - 32)); [|lia]. cbn [andb].
      destruct (Z.ltb_spec (k - 32) 32), (Z.ltb_spec k 64); try reflexivity; lia.
    + rewrite (testbit_high 32 (x mod 2^32) k) by lia. rewrite andb_false_r. reflexivity.
Qed.

Lemma sx32_lor : forall a b, Z.lor (bv_swrap 32 a mod 2^64) (bv_swrap 32 b mod 2^64) = bv_swrap 32 (Z.lor a b) mod 2^64.
Proof.
  intros a b. apply Z.bits_inj'. intros k Hk. rewrite Z.lor_spec, !testbit_sx32 by lia.
  rewrite Z.lor_spec. destruct (k <? 64); reflexivity.
Qed.

Lemma sx32_land : forall a b, Z.land (bv_swrap 32 a mod 2^64) (bv_swrap 32 b mod 2^64) = bv_swrap 32 (Z.land a b) mod 2^64.
Proof.
  intros a b. apply Z.bits_inj'. intros k Hk. rewrite Z.land_spec, !testbit_sx32 by lia.
  rewrite Z.land_spec. destruct (k <? 64); reflexivity.
Qed.

Lemma sx32_eqb : forall a b, (bv_swrap 32 a mod 2^64 =? bv_swrap 32 b mod 2^64) = (a mod 2^32 =? b mod 2^32).
Proof.
  intros a b. rewrite !sx32_val.
  assert (Ha : 0 <= a mod 2^32 < 2^32) by (apply Z.mod_pos_bound; lia).
  assert (Hb : 0 <= b mod 2^32 < 2^32) by (apply Z.mod_pos_bound; lia).
  replace (Z.testbit a 31) with (Z.testbit (a mod 2^32) 31) by (apply Z.mod_pow2_bits_low; lia).
  replace (Z.testbit b 31) with (Z.testbit (b mod 2^32) 31) by (apply Z.mod_pow2_bits_low; lia).
  rewrite !testbit31_iff by assumption.
  set (u := a mod 2^32) in *. set (v := b mod 2^32) in *.
  destruct (Z.leb_spec (2^31) u), (Z.leb_spec (2^31) v);
    destruct (Z.eqb_spec u v); first [reflexivity | apply Z.eqb_eq; lia | apply Z.eqb_neq; lia].
Qed.

Lemma ext4_swrap : forall x, ext_Z true 0 4 x = bv_swrap 32 x.
Proof.
  intros x. unfold ext_Z. cbn [Z.of_nat N.of_nat]. change (2 ^ (8 * 0)) with 1. rewrite Z.div_1_r.
  change (8 * N.pos 4)%N with 32%N. change (2 ^ (8 * 4)) with (2^32). symmetry. apply swrap32_eq_mod.
Qed.

(* [comment removed for export] *)

Lemma sllw1_val : forall idx, 0 <= idx <= 31 -> bv_swrap 32 (Z.shiftl 1 idx) mod 2^64 = bv_swrap 32 (2^idx) mod 2^64.
Proof. intros idx H. rewrite Z.shiftl_1_l. reflexivity. Qed.

Lemma mask_bit_clear : forall f idx, 0 <= f < 2^32 -> 0 <= idx <= 31 -> Z.testbit f idx = false ->
  Z.land (bv_swrap 32 f mod 2^64) (bv_swrap 32 (Z.shiftl 1 idx) mod 2^64) = 0.
Proof.
  intros f idx Hf Hi Hb. rewrite sllw1_val by lia. rewrite sx32_land.
  replace (Z.land f (2^idx)) with 0.
  - reflexivity.
  - apply Z.bits_inj'. intros k Hk. rewrite Z.land_spec, Z.bits_0, testbit_pow2 by lia.
    destruct (Z.eqb_spec idx k) as [<-|]; [rewrite Hb; reflexivity | rewrite andb_false_r; reflexivity].
Qed.

Lemma mask2_bit_clear : forall a f idx, 0 <= a < 2^32 -> 0 <= f < 2^32 -> 0 <= idx <= 31 ->
  Z.testbit a idx = false -> Z.testbit f idx = false ->
  Z.land (Z.lor (bv_swrap 32 a mod 2^64) (bv_swrap 32 f mod 2^64) mod 2^64) (bv_swrap 32 (Z.shiftl 1 idx) mod 2^64) = 0.
Proof.
  intros a f idx Ha Hf Hi Hba Hbf. rewrite sx32_lor. rewrite Z.mod_mod by lia.
  apply mask_bit_clear; [split; [apply Z.lor_nonneg; lia | ] | lia | ].
  - apply (Z.le_lt_trans _ (Z.lor a f)); [lia|]. 
    destruct (Z.eq_dec (Z.lor a f) 0) as [->|Hnz]; [lia|].
    apply Z.log2_lt_cancel. rewrite Z.log2_pow2 by lia. rewrite Z.log2_lor by lia.
    apply Z.max_lub_lt; [destruct (Z.eq_dec a 0) as [->|]; [simpl; lia | apply Z.log2_lt_pow2; lia]
                         | destruct (Z.eq_dec f 0) as [->|]; [simpl; lia | apply Z.log2_lt_pow2; lia]].
  - rewrite Z.lor_spec, Hba, Hbf. reflexivity.
Qed.

Lemma land31_bound : forall x, 0 <= x -> 0 <= Z.land x 31 < 32.
Proof.
  intros x Hx. change 31 with (Z.ones 5). rewrite Z.land_ones by lia.
  pose proof (Z.mod_pos_bound x (2^5) ltac:(lia)). change (2^5) with 32 in *. lia.
Qed.

Lemma shiftr5_bound : forall h, 0 <= h <= 159 -> 0 <= Z.shiftr h 5 <= 4.
Proof.
  intros h H. rewrite Z.shiftr_div_pow2 by lia. change (2^5) with 32.
  split; [apply Z.div_pos; lia | apply Z.lt_succ_r; apply Z.div_lt_upper_bound; lia].
Qed.

Lemma lor_lt32 : forall a f, 0 <= a < 2^32 -> 0 <= f < 2^32 -> 0 <= Z.lor a f < 2^32.
Proof.
  intros a f Ha Hf. split; [apply Z.lor_nonneg; lia|].
  destruct (Z.eq_dec (Z.lor a f) 0) as [->|Hnz]; [lia|].
  apply Z.log2_lt_cancel. rewrite Z.log2_pow2 by lia. rewrite Z.log2_lor by lia.
  apply Z.max_lub_lt; [destruct (Z.eq_dec a 0) as [->|]; [simpl; lia | apply Z.log2_lt_pow2; lia]
                       | destruct (Z.eq_dec f 0) as [->|]; [simpl; lia | apply Z.log2_lt_pow2; lia]].
Qed.

Lemma add_bit_clear_lt : forall a k, 0 <= a < 2^32 -> 0 <= k <= 31 -> Z.testbit a k = false -> a + 2^k < 2^32.
Proof.
  intros a k Ha Hk Hb.
  assert (Hd : Z.land a (2^k) = 0).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0, testbit_pow2 by lia.
    destruct (Z.eqb_spec k i) as [<-|]; [rewrite Hb; reflexivity | apply andb_false_r]. }
  rewrite (Z.add_nocarry_lxor a (2^k) Hd), (Z.lxor_lor a (2^k) Hd).
  apply lor_lt32; [lia|]. split; [apply Z.pow_nonneg; lia | apply Z.pow_lt_mono_r; lia].
Qed.

(* [comment removed for export] *)
Lemma all_cond_z : forall a f idx W, 0 <= a < 2^32 -> 0 <= f < 2^32 -> 0 <= idx <= 31 -> 0 <= W ->
  Z.testbit a idx = false -> Z.testbit f idx = false ->
  (bv_swrap 32 (Z.lor (ext_Z true 0 4 a mod 2^64) (ext_Z true 0 4 f mod 2^64) + bv_swrap 32 (Z.shiftl 1 idx)) mod 2^64
     =? bv_swrap 32 (bv_swrap 32 (Z.shiftl 2 (W mod 32)) + -1) mod 2^64)
  = (Z.lor a f + 2^idx =? 2^(Z.land W 31 + 1) - 1).
Proof.
  intros a f idx W Ha Hf Hi HW Hba Hbf.
  rewrite !ext4_swrap, sx32_lor, sx32_eqb.
  assert (HL : 0 <= Z.lor a f < 2^32) by (apply lor_lt32; lia).
  assert (HLb : Z.testbit (Z.lor a f) idx = false) by (rewrite Z.lor_spec, Hba, Hbf; reflexivity).
  assert (HLt : Z.lor a f + 2^idx < 2^32) by (apply add_bit_clear_lt; [exact HL | lia | exact HLb]).
  assert (Hp : 0 < 2^idx) by (apply Z.pow_pos_nonneg; lia).
  rewrite Z.shiftl_1_l.
  assert (E1 : (bv_swrap 32 (Z.lor a f) mod 2^64 + bv_swrap 32 (2^idx)) mod 2^32 = Z.lor a f + 2^idx).
  { rewrite Zplus_mod, mod64_32, !swrap32_mod, <- Zplus_mod. apply Z.mod_small. lia. }
  assert (Hl : 0 <= Z.land W 31 < 32) by (apply land31_bound; lia).
  assert (Hw : W mod 32 = Z.land W 31) by (change 31 with (Z.ones 5); rewrite Z.land_ones by lia; reflexivity).
  assert (E2 : (bv_swrap 32 (Z.shiftl 2 (W mod 32)) + -1) mod 2^32 = 2^(Z.land W 31 + 1) - 1).
  { rewrite Zplus_mod, swrap32_mod, <- Zplus_mod. rewrite Hw. rewrite Z.shiftl_mul_pow2 by lia.
    rewrite Z.pow_add_r by lia. change (2^1) with 2.
    assert (0 < 2^(Z.land W 31) <= 2^31) by (split; [apply Z.pow_pos_nonneg; lia | apply Z.pow_le_mono_r; lia]).
    rewrite Z.mod_small; lia. }
  rewrite E1, E2. reflexivity.
Qed.

Lemma sx32_zero : forall f, (bv_swrap 32 f mod 2^64 =? 0) = (f mod 2^32 =? 0).
Proof. intros f. change 0 with (bv_swrap 32 0 mod 2^64) at 1. rewrite sx32_eqb. reflexivity. Qed.
