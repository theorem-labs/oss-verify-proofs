(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith Lia Bool List.
From Stdlib Require Import Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.openssl.bignum.lib.Common Require Import FastWord FastWordSem.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Local Open Scope Z_scope.
#[local] Arguments Uint63Axioms.to_Z : simpl never.
#[local] Arguments Uint63Axioms.of_Z : simpl never.

Inductive hval : Type :=
| VC (w : w64)
| VP (t : int) (o : w64)
| VU
| VN (t : int) (o : w64).

Definition valuation := int -> Z.

Definition pword (rho : valuation) (t : int) (o : w64) : bv 64 := Z_to_bv 64 (rho t + wZ o).

Definition den (rho : valuation) (v : hval) (x : bv 64) : Prop :=
  match v with
  | VC w => x = wbv w
  | VP t o => x = pword rho t o
  | VU => True
  | VN t o => bv_unsigned x = two64 - 1 - bv_unsigned (pword rho t o)
  end.

Definition vzero : hval := VC w_zero.

Lemma den_vzero (rho : valuation) : den rho vzero (Z_to_bv 64 0).
Proof. reflexivity. Qed.

Definition agree_below (n : int) (rho rho' : valuation) : Prop :=
  forall t, to_Z t < to_Z n -> rho' t = rho t.

Lemma agree_below_refl (n : int) (rho : valuation) : agree_below n rho rho.
Proof. intros t _. reflexivity. Qed.

Lemma agree_below_trans (n n' : int) (r1 r2 r3 : valuation) :
  to_Z n <= to_Z n' -> agree_below n r1 r2 -> agree_below n' r2 r3 -> agree_below n r1 r3.
Proof. intros Hn H1 H2 t Ht. rewrite (H2 t) by lia. apply H1. exact Ht. Qed.

Definition val_below (n : int) (v : hval) : Prop :=
  match v with VP t _ | VN t _ => to_Z t < to_Z n | _ => True end.

Lemma Z_to_bv64_congr (a b : Z) : a mod two64 = b mod two64 -> Z_to_bv 64 a = Z_to_bv 64 b.
Proof.
  intros H. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. rewrite bv_modulus_64. exact H.
Qed.

Lemma wbv_Z (w : w64) : wbv w = Z_to_bv 64 (wZ w).
Proof. reflexivity. Qed.

Lemma Z_to_bv64_add (a b : Z) : bv_add (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a + b).
Proof.
  apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap. rewrite bv_modulus_64.
  rewrite <- Z.add_mod by (unfold two64; lia). reflexivity.
Qed.

Lemma Z_to_bv64_sub (a b : Z) : bv_sub (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a - b).
Proof.
  apply bv_eq. rewrite bv_sub_unsigned, !Z_to_bv_unsigned. unfold bv_wrap. rewrite bv_modulus_64.
  rewrite <- Zminus_mod. reflexivity.
Qed.

Lemma pword_add (rho : valuation) (t : int) (o c : w64) :
  bv_add (pword rho t o) (wbv c) = pword rho t (w_add o c).
Proof.
  unfold pword. rewrite wbv_Z, Z_to_bv64_add. apply Z_to_bv64_congr. rewrite wZ_add.
  rewrite Z.add_mod_idemp_r by (unfold two64; lia). f_equal. ring.
Qed.

Lemma pword_add_l (rho : valuation) (t : int) (o c : w64) :
  bv_add (wbv c) (pword rho t o) = pword rho t (w_add o c).
Proof. rewrite <- pword_add. apply bv_eq. rewrite !bv_add_unsigned. f_equal. ring. Qed.

Lemma pword_sub (rho : valuation) (t : int) (o c : w64) :
  bv_sub (pword rho t o) (wbv c) = pword rho t (w_sub o c).
Proof.
  unfold pword. rewrite wbv_Z, Z_to_bv64_sub. apply Z_to_bv64_congr. rewrite wZ_sub.
  rewrite Z.add_mod_idemp_r by (unfold two64; lia). f_equal. ring.
Qed.

Lemma pword_diff (rho : valuation) (t : int) (o1 o2 : w64) :
  bv_sub (pword rho t o1) (pword rho t o2) = wbv (w_sub o1 o2).
Proof.
  unfold pword. rewrite Z_to_bv64_sub, wbv_Z. apply Z_to_bv64_congr. rewrite wZ_sub.
  rewrite Z.mod_mod by (unfold two64; lia). f_equal. ring.
Qed.

Lemma pword_eq_iff (rho : valuation) (t : int) (o1 o2 : w64) :
  pword rho t o1 = pword rho t o2 <-> o1 = o2.
Proof.
  split; [|intros ->; reflexivity]. intros H. apply wZ_inj.
  assert (E : bv_sub (pword rho t o1) (pword rho t o2) = Z_to_bv 64 0).
  { rewrite H. apply bv_eq. rewrite bv_sub_unsigned, Z_to_bv_unsigned. rewrite Z.sub_diag. reflexivity. }
  rewrite pword_diff in E. apply (f_equal bv_unsigned) in E. rewrite wbv_unsigned, Z_to_bv_unsigned in E.
  change (bv_wrap 64 0) with 0 in E. rewrite wZ_sub in E.
  pose proof (wZ_range o1) as H1. pose proof (wZ_range o2) as H2.
  destruct (Z_lt_le_dec (wZ o1) (wZ o2)) as [Hlt|Hge].
  - replace (wZ o1 - wZ o2) with ((wZ o1 - wZ o2 + two64) + (-1) * two64) in E by ring.
    rewrite Z.mod_add in E by (unfold two64; lia). rewrite Z.mod_small in E by lia. lia.
  - rewrite Z.mod_small in E by lia. lia.
Qed.

Definition vctx := int -> option (int * int).

Definition ctx_ok (rho : valuation) (ctx : vctx) : Prop :=
  forall t al sz, ctx t = Some (al, sz) ->
    to_Z al < 63 /\ rho t mod 2 ^ to_Z al = 0 /\ 0 < rho t /\ rho t + to_Z sz < two63.

Definition inb (ctx : vctx) (t : int) (o : w64) : bool :=
  match ctx t with
  | Some (_, sz) => negb (wh o) && (wl o <=? sz)%uint63
  | None => false
  end.

Lemma inb_spec (rho : valuation) (ctx : vctx) (t : int) (o : w64) :
  ctx_ok rho ctx -> inb ctx t o = true ->
  0 < rho t + wZ o < two63 /\ bv_unsigned (pword rho t o) = rho t + wZ o.
Proof.
  intros Hc H. unfold inb in H. destruct (ctx t) as [[al sz]|] eqn:E; [|discriminate].
  destruct (Hc t al sz E) as (_ & _ & Hpos & Hhi). apply andb_prop in H as [Hh Hl].
  destruct o as [h l]. cbn [wh wl] in *. destruct h; [discriminate|].
  apply leb_spec in Hl. pose proof (phi_range l) as Hr.
  assert (Ew : wZ (W false l) = to_Z l) by (unfold wZ; cbn [wh wl]; lia).
  rewrite Ew. split; [lia|]. unfold pword. rewrite Ew, Z_to_bv_unsigned. unfold bv_wrap. rewrite bv_modulus_64.
  apply Z.mod_small. unfold two63, two64 in *. lia.
Qed.

Definition alu_rule := vctx -> aluop -> hval -> hval -> option hval.

Definition alu_rule_ok (r : alu_rule) : Prop :=
  forall rho ctx op a b v x y, ctx_ok rho ctx -> r ctx op a b = Some v ->
    den rho a x -> den rho b y -> den rho v (alu64 op x y).

Definition ar_conc : alu_rule := fun _ op a b =>
  match a, b with VC x, VC y => Some (VC (w_alu64 op x y)) | _, _ => None end.

Lemma ar_conc_ok : alu_rule_ok ar_conc.
Proof.
  intros rho ctx op a b v x y _ H Ha Hb. unfold ar_conc in H.
  destruct a as [wa| | |]; try discriminate. destruct b as [wb| | |]; try discriminate.
  injection H as <-. cbn [den] in *. subst x y. symmetry. apply w_alu64_ok.
Qed.

Definition ar_ptr : alu_rule := fun _ op a b =>
  match op, a, b with
  | ALU_ADD, VP t o, VC c => Some (VP t (w_add o c))
  | ALU_ADD, VC c, VP t o => Some (VP t (w_add o c))
  | ALU_SUB, VP t o, VC c => Some (VP t (w_sub o c))
  | ALU_SUB, VP t1 o1, VP t2 o2 => if (t1 =? t2)%uint63 then Some (VC (w_sub o1 o2)) else None
  | _, _, _ => None
  end.

Lemma ar_ptr_ok : alu_rule_ok ar_ptr.
Proof.
  intros rho ctx op a b v x y _ H Ha Hb. unfold ar_ptr in H.
  destruct op; try discriminate; destruct a as [wa|ta oa| |]; try discriminate; destruct b as [wb|tb ob| |]; try discriminate;
    cbn [den] in *; subst x y; unfold alu64, alu.
  - injection H as <-. cbn [den]. apply pword_add_l.
  - injection H as <-. cbn [den]. apply pword_add.
  - injection H as <-. cbn [den]. apply pword_sub.
  - destruct (eqbP ta tb) as [E|E]; [|discriminate]. injection H as <-. apply to_Z_inj in E. subst tb.
    cbn [den]. apply pword_diff.
Qed.

Definition is_zero (w : w64) : bool := negb (wh w) && (wl w =? 0)%uint63.

Lemma is_zero_spec (w : w64) : is_zero w = true -> w = w_zero.
Proof.
  destruct w as [h l]. unfold is_zero; cbn [wh wl]. intros H. apply andb_prop in H as [Hh Hl].
  destruct h; [discriminate|]. destruct (eqbP l 0) as [E|E]; [|discriminate]. apply to_Z_inj in E. subst l. reflexivity.
Qed.

Definition ar_zero : alu_rule := fun _ op a b =>
  match op, a, b with
  | (ALU_OR | ALU_XOR | ALU_ADD | ALU_SUB | ALU_SLL | ALU_SRL | ALU_SRA), v, VC c => if is_zero c then Some v else None
  | _, _, _ => None
  end.

Lemma alu64_zero_r (op : aluop) (x : bv 64) :
  match op with ALU_OR | ALU_XOR | ALU_ADD | ALU_SUB | ALU_SLL | ALU_SRL | ALU_SRA => True | _ => False end ->
  alu64 op x (Z_to_bv 64 0) = x.
Proof.
  intros H. unfold alu64, alu. destruct op; try (destruct H); apply bv_eq.
  - rewrite bv_add_unsigned. change (bv_unsigned (Z_to_bv 64 0)) with 0. rewrite Z.add_0_r. apply bv_wrap_small, bv_unsigned_in_range.
  - rewrite bv_sub_unsigned. change (bv_unsigned (Z_to_bv 64 0)) with 0. rewrite Z.sub_0_r. apply bv_wrap_small, bv_unsigned_in_range.
  - rewrite bv_shiftl_unsigned. change (bv_unsigned (bv_and (Z_to_bv 64 0) (Z_to_bv 64 63))) with 0.
    rewrite Z.shiftl_0_r. apply bv_wrap_small, bv_unsigned_in_range.
  - rewrite bv_xor_unsigned. change (bv_unsigned (Z_to_bv 64 0)) with 0. apply Z.lxor_0_r.
  - rewrite bv_shiftr_unsigned. change (bv_unsigned (bv_and (Z_to_bv 64 0) (Z_to_bv 64 63))) with 0. apply Z.shiftr_0_r.
  - rewrite bv_ashiftr_unsigned. change (bv_unsigned (bv_and (Z_to_bv 64 0) (Z_to_bv 64 63))) with 0.
    rewrite Z.shiftr_0_r. unfold bv_wrap. rewrite bv_modulus_64.
    pose proof (bv_unsigned_in_range 64 x) as Hx. rewrite bv_modulus_64 in Hx.
    unfold bv_signed, bv_swrap, bv_wrap. rewrite bv_modulus_64. change (bv_half_modulus 64) with two63.
    destruct (Z_lt_le_dec (bv_unsigned x) two63).
    + rewrite (Z.mod_small (bv_unsigned x + two63)) by (unfold two63, two64 in *; lia).
      replace (bv_unsigned x + two63 - two63) with (bv_unsigned x) by ring. apply Z.mod_small. exact Hx.
    + replace (bv_unsigned x + two63) with ((bv_unsigned x - two63) + 1 * two64) by (rewrite two64_eq; ring).
      rewrite Z.mod_add by (unfold two64; lia). rewrite (Z.mod_small (bv_unsigned x - two63)) by (unfold two63, two64 in *; lia).
      replace (bv_unsigned x - two63 - two63) with (bv_unsigned x + (-1) * two64) by (rewrite two64_eq; ring).
      rewrite Z.mod_add by (unfold two64; lia). apply Z.mod_small. exact Hx.
  - rewrite bv_or_unsigned. change (bv_unsigned (Z_to_bv 64 0)) with 0. apply Z.lor_0_r.
Qed.

Lemma ar_zero_ok : alu_rule_ok ar_zero.
Proof.
  intros rho ctx op a b v x y _ H Ha Hb. unfold ar_zero in H.
  destruct b as [c| | |]; try (destruct op; discriminate).
  assert (Hz : is_zero c = true /\ v = a /\ match op with ALU_OR | ALU_XOR | ALU_ADD | ALU_SUB | ALU_SLL | ALU_SRL | ALU_SRA => True | _ => False end).
  { destruct op; try discriminate; destruct (is_zero c); try discriminate; injection H as <-; auto. }
  destruct Hz as (Hz & -> & Hop). apply is_zero_spec in Hz. subst c. cbn [den] in Hb. subst y.
  change (wbv w_zero) with (Z_to_bv 64 0). rewrite (alu64_zero_r op x Hop). exact Ha.
Qed.

Fixpoint first_alu (rs : list alu_rule) (ctx : vctx) (op : aluop) (a b : hval) : hval :=
  match rs with
  | [] => VU
  | r :: rs' => match r ctx op a b with Some v => v | None => first_alu rs' ctx op a b end
  end.

Lemma first_alu_ok (rs : list alu_rule) : Forall alu_rule_ok rs ->
  forall rho ctx op a b x y, ctx_ok rho ctx -> den rho a x -> den rho b y -> den rho (first_alu rs ctx op a b) (alu64 op x y).
Proof.
  induction 1 as [|r rs Hr _ IH]; intros rho ctx op a b x y Hc Ha Hb; cbn [first_alu]; [exact I|].
  destruct (r ctx op a b) as [v|] eqn:E; [exact (Hr rho ctx op a b v x y Hc E Ha Hb) | apply IH; assumption].
Qed.

Definition ar_align : alu_rule := fun ctx op a b =>
  match op, a, b with
  | ALU_AND, VP t o, VC c =>
      match ctx t with
      | Some (al, _) => if inb ctx t o && negb (wh c) && (wl c <? (1 << al))%uint63 then Some (VC (w_and o c)) else None
      | None => None
      end
  | _, _, _ => None
  end.

Lemma land_low_mod (X C al : Z) : 0 <= al -> 0 <= C < 2 ^ al -> Z.land X C = Z.land (X mod 2 ^ al) C.
Proof.
  intros Hal HC. rewrite <- (Z.land_ones X al) by exact Hal. rewrite <- Z.land_assoc. f_equal.
  rewrite Z.land_comm. rewrite Z.land_ones by exact Hal. symmetry. apply Z.mod_small. exact HC.
Qed.

Lemma ar_align_ok : alu_rule_ok ar_align.
Proof.
  intros rho ctx op a b v x y Hc H Ha Hb. unfold ar_align in H.
  destruct op; try discriminate. destruct a as [|t o| |]; try discriminate. destruct b as [c| | |]; try discriminate.
  destruct (ctx t) as [[al sz]|] eqn:Ec; [|discriminate].
  destruct (inb ctx t o && negb (wh c) && (wl c <? 1 << al)%uint63) eqn:E; [|discriminate]. injection H as <-.
  apply andb_prop in E as [E E3]. apply andb_prop in E as [E1 E2]. apply ltb_spec in E3. apply negb_true_iff in E2.
  destruct (Hc t al sz Ec) as (Hal & Hmod & _ & _). destruct (inb_spec rho ctx t o Hc E1) as [_ Ep].
  cbn [den] in *. subst x y. unfold alu64, alu. rewrite wbv_and. apply bv_eq. rewrite !bv_and_unsigned, Ep, !wbv_unsigned.
  pose proof (to_Z_bounded al) as Bal. pose proof (to_Z_bounded (wl c)) as Bc.
  assert (E1s : to_Z (1 << al)%uint63 = 2 ^ to_Z al).
  { rewrite lsl_spec. change (to_Z 1%uint63) with 1. rewrite Z.mul_1_l. apply Z.mod_small. rewrite wB_eq. unfold two63.
    split; [apply Z.pow_nonneg; lia | change 9223372036854775808 with (2 ^ 63); apply Z.pow_lt_mono_r; lia]. }
  assert (EC : wZ c = to_Z (wl c)) by (unfold wZ; rewrite E2; lia).
  rewrite EC. rewrite E1s in E3.
  rewrite (land_low_mod (rho t + wZ o) (to_Z (wl c)) (to_Z al)) by lia.
  rewrite (land_low_mod (wZ o) (to_Z (wl c)) (to_Z al)) by lia. f_equal.
  rewrite Z.add_mod by (apply Z.pow_nonzero; lia). rewrite Hmod, Z.add_0_l. apply Z.mod_mod. apply Z.pow_nonzero; lia.
Qed.

Definition ar_pnz : alu_rule := fun ctx op a b =>
  match op, a, b with
  | ALU_SLTU, VC c, VP t o => if inb ctx t o && is_zero c then Some (VC (W false 1)) else None
  | ALU_SLTU, VP t o, VC c => if inb ctx t o && negb (wh c) && (wl c =? 1)%uint63 then Some (VC w_zero) else None
  | _, _, _ => None
  end.

Lemma ar_pnz_ok : alu_rule_ok ar_pnz.
Proof.
  intros rho ctx op a b v x y Hc H Ha Hb. unfold ar_pnz in H.
  destruct op; try discriminate; destruct a as [ca|ta oa| |]; try discriminate; destruct b as [cb|tb ob| |]; try discriminate.
  - destruct (inb ctx tb ob && is_zero ca) eqn:E; [|discriminate]. injection H as <-. apply andb_prop in E as [E1 E2].
    apply is_zero_spec in E2. subst ca. destruct (inb_spec rho ctx tb ob Hc E1) as [Hr Ep]. cbn [den] in *. subst x y.
    unfold alu64, alu, bv_ltu. rewrite Ep. change (bv_unsigned (wbv w_zero)) with 0.
    replace (0 <? rho tb + wZ ob) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
  - destruct (inb ctx ta oa && negb (wh cb) && (wl cb =? 1)%uint63) eqn:E; [|discriminate]. injection H as <-.
    apply andb_prop in E as [E E3]. apply andb_prop in E as [E1 E2]. apply negb_true_iff in E2.
    destruct (eqbP (wl cb) 1) as [E4|E4]; [|discriminate]. change (to_Z 1%uint63) with 1 in E4.
    destruct (inb_spec rho ctx ta oa Hc E1) as [Hr Ep]. cbn [den] in *. subst x y.
    unfold alu64, alu, bv_ltu. rewrite Ep, wbv_unsigned. assert (EC : wZ cb = 1) by (unfold wZ; rewrite E2; lia). rewrite EC.
    replace (rho ta + wZ oa <? 1) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.

Definition ar_pcmp : alu_rule := fun ctx op a b =>
  match op, a, b with
  | ALU_SLTU, VP t1 o1, VP t2 o2 =>
      if (t1 =? t2)%uint63 && inb ctx t1 o1 && inb ctx t1 o2 then Some (VC (w_alu64 ALU_SLTU o1 o2)) else None
  | _, _, _ => None
  end.

Lemma ar_pcmp_ok : alu_rule_ok ar_pcmp.
Proof.
  intros rho ctx op a b v x y Hc H Ha Hb. unfold ar_pcmp in H.
  destruct op; try discriminate; destruct a as [|t1 o1| |]; try discriminate; destruct b as [|t2 o2| |]; try discriminate.
  destruct ((t1 =? t2)%uint63 && inb ctx t1 o1 && inb ctx t1 o2) eqn:E; [|discriminate]. injection H as <-.
  apply andb_prop in E as [E E3]. apply andb_prop in E as [E1 E2]. destruct (eqbP t1 t2) as [Et|Et]; [|discriminate].
  apply to_Z_inj in Et. subst t2. destruct (inb_spec rho ctx t1 o1 Hc E2) as [_ Ep1]. destruct (inb_spec rho ctx t1 o2 Hc E3) as [_ Ep2].
  cbn [den] in *. subst x y. unfold alu64, alu, bv_ltu. rewrite Ep1, Ep2, w_ltu_spec.
  destruct (Z.ltb_spec (rho t1 + wZ o1) (rho t1 + wZ o2)); destruct (Z.ltb_spec (wZ o1) (wZ o2)); try reflexivity; lia.
Qed.

Definition is_ones (w : w64) : bool := wh w && (wl w =? 9223372036854775807)%uint63.

Lemma is_ones_spec (w : w64) : is_ones w = true -> wZ w = two64 - 1.
Proof.
  destruct w as [h l]. unfold is_ones; cbn [wh wl]. intros H. apply andb_prop in H as [Hh Hl]. subst h.
  destruct (eqbP l 9223372036854775807) as [E|E]; [|discriminate]. unfold wZ; cbn [wh wl]. rewrite E. reflexivity.
Qed.

Lemma lxor_ones64 (a : Z) : 0 <= a < two64 -> Z.lxor a (two64 - 1) = two64 - 1 - a.
Proof.
  intros Ha. change (two64 - 1) with (Z.ones 64).
  assert (E : Z.lxor a (Z.ones 64) = Z.land (Z.lnot a) (Z.ones 64)).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.lxor_spec, Z.land_spec, Z.lnot_spec by exact Hi.
    destruct (Z_lt_le_dec i 64) as [Hlt|Hge].
    - rewrite Z.ones_spec_low by lia. rewrite xorb_true_r, andb_true_r. reflexivity.
    - rewrite Z.ones_spec_high by lia. rewrite xorb_false_r, andb_false_r.
      destruct (Z.eq_dec a 0) as [->|Hnz]; [apply Z.bits_0|].
      apply Z.bits_above_log2; [lia|]. apply Z.lt_le_trans with 64; [|exact Hge].
      apply Z.log2_lt_pow2; [lia|]. change (2 ^ 64) with two64. lia. }
  rewrite E, Z.land_ones by lia. unfold Z.lnot. change (Z.pred (- a)) with (- a - 1). change (2 ^ 64) with two64.
  replace (- a - 1) with ((two64 - 1 - a) + (-1) * two64) by ring.
  rewrite Z.mod_add by (unfold two64; lia). change (Z.ones 64) with (two64 - 1). apply Z.mod_small. lia.
Qed.

Definition ar_not : alu_rule := fun _ op a b =>
  match op, a, b with
  | ALU_XOR, VP t o, VC c => if is_ones c then Some (VN t o) else None
  | _, _, _ => None
  end.

Lemma ar_not_ok : alu_rule_ok ar_not.
Proof.
  intros rho ctx op a b v x y _ H Ha Hb. unfold ar_not in H.
  destruct op; try discriminate; destruct a as [|t o| |]; try discriminate; destruct b as [c| | |]; try discriminate.
  destruct (is_ones c) eqn:E; [|discriminate]. injection H as <-. apply is_ones_spec in E.
  cbn [den] in *. subst x y. unfold alu64, alu. rewrite bv_xor_unsigned, wbv_unsigned, E.
  apply lxor_ones64. pose proof (bv_unsigned_in_range 64 (pword rho t o)) as Hr. rewrite bv_modulus_64 in Hr. exact Hr.
Qed.

Definition alu_rules : list alu_rule := [ar_conc; ar_ptr; ar_zero; ar_align; ar_pnz; ar_pcmp; ar_not].

Lemma alu_rules_ok : Forall alu_rule_ok alu_rules.
Proof. repeat constructor; [apply ar_conc_ok | apply ar_ptr_ok | apply ar_zero_ok | apply ar_align_ok | apply ar_pnz_ok | apply ar_pcmp_ok | apply ar_not_ok]. Qed.

Definition v_alu64 (ctx : vctx) (op : aluop) (a b : hval) : hval := first_alu alu_rules ctx op a b.

Lemma v_alu64_ok (rho : valuation) (ctx : vctx) (op : aluop) (a b : hval) (x y : bv 64) :
  ctx_ok rho ctx -> den rho a x -> den rho b y -> den rho (v_alu64 ctx op a b) (alu64 op x y).
Proof. apply first_alu_ok. apply alu_rules_ok. Qed.

Definition br_rule := vctx -> branch_cond -> hval -> hval -> option bool.

Definition br_rule_ok (r : br_rule) : Prop :=
  forall rho ctx bc a b d x y, ctx_ok rho ctx -> r ctx bc a b = Some d ->
    den rho a x -> den rho b y -> branch_taken bc x y = d.

Definition br_conc : br_rule := fun _ bc a b =>
  match a, b with VC x, VC y => Some (w_branch bc x y) | _, _ => None end.

Lemma br_conc_ok : br_rule_ok br_conc.
Proof.
  intros rho ctx bc a b d x y _ H Ha Hb. unfold br_conc in H.
  destruct a as [wa| | |]; try discriminate. destruct b as [wb| | |]; try discriminate.
  injection H as <-. cbn [den] in *. subst x y. symmetry. apply w_branch_ok.
Qed.

Definition br_same : br_rule := fun ctx bc a b =>
  match a, b with
  | VP t1 o1, VP t2 o2 =>
      if (t1 =? t2)%uint63 then
        match bc with
        | BC_EQ => Some (w_eqb o1 o2)
        | BC_NE => Some (negb (w_eqb o1 o2))
        | _ => if inb ctx t1 o1 && inb ctx t1 o2 then Some (w_branch bc o1 o2) else None
        end
      else None
  | _, _ => None
  end.

Lemma w_eqb_true_iff (a b : w64) : w_eqb a b = true <-> a = b.
Proof.
  rewrite w_eqb_spec. split; [intros H; apply wZ_inj; apply Z.eqb_eq; exact H | intros ->; apply Z.eqb_refl].
Qed.

Lemma bv_eqb_pword (rho : valuation) (t : int) (o1 o2 : w64) :
  bv_eqb (pword rho t o1) (pword rho t o2) = w_eqb o1 o2.
Proof.
  unfold bv_eqb. destruct (w_eqb o1 o2) eqn:E.
  - apply w_eqb_true_iff in E. subst. apply Z.eqb_refl.
  - apply Z.eqb_neq. intros H. apply bv_eq in H. apply pword_eq_iff in H. subst o2.
    assert (w_eqb o1 o1 = true) by (apply w_eqb_true_iff; reflexivity). congruence.
Qed.

Lemma br_same_ok : br_rule_ok br_same.
Proof.
  intros rho ctx bc a b d x y Hc H Ha Hb. unfold br_same in H.
  destruct a as [|t1 o1| |]; try discriminate. destruct b as [|t2 o2| |]; try discriminate.
  destruct (eqbP t1 t2) as [E|E]; [|discriminate]. apply to_Z_inj in E. subst t2. cbn [den] in *. subst x y.
  assert (Hord : inb ctx t1 o1 && inb ctx t1 o2 = true -> branch_taken bc (pword rho t1 o1) (pword rho t1 o2) = w_branch bc o1 o2).
  { intros Hi. apply andb_prop in Hi as [Hi1 Hi2].
    destruct (inb_spec rho ctx t1 o1 Hc Hi1) as [R1 U1]. destruct (inb_spec rho ctx t1 o2 Hc Hi2) as [R2 U2].
    assert (S1 : bv_signed (pword rho t1 o1) = rho t1 + wZ o1).
    { unfold bv_signed, bv_swrap, bv_wrap. rewrite U1, bv_modulus_64. change (bv_half_modulus 64) with two63.
      rewrite Z.mod_small by (unfold two63, two64 in *; lia). ring. }
    assert (S2 : bv_signed (pword rho t1 o2) = rho t1 + wZ o2).
    { unfold bv_signed, bv_swrap, bv_wrap. rewrite U2, bv_modulus_64. change (bv_half_modulus 64) with two63.
      rewrite Z.mod_small by (unfold two63, two64 in *; lia). ring. }
    assert (B1 : wh o1 = false) by (unfold inb in Hi1; destruct (ctx t1) as [[? ?]|]; [|discriminate]; apply andb_prop in Hi1 as [Hh _]; destruct (wh o1); [discriminate | reflexivity]).
    assert (B2 : wh o2 = false) by (unfold inb in Hi2; destruct (ctx t1) as [[? ?]|]; [|discriminate]; apply andb_prop in Hi2 as [Hh _]; destruct (wh o2); [discriminate | reflexivity]).
    assert (WS1 : wS o1 = wZ o1) by (unfold wS; rewrite B1; reflexivity).
    assert (WS2 : wS o2 = wZ o2) by (unfold wS; rewrite B2; reflexivity).
    unfold branch_taken, w_branch. rewrite bv_eqb_pword.
    unfold bv_lts, bv_ltu. rewrite S1, S2, U1, U2. rewrite w_lts_spec, w_ltu_spec, WS1, WS2.
    assert (L : (rho t1 + wZ o1 <? rho t1 + wZ o2) = (wZ o1 <? wZ o2)).
    { destruct (Z.ltb_spec (wZ o1) (wZ o2)); [apply Z.ltb_lt | apply Z.ltb_ge]; lia. }
    rewrite L. destruct bc; reflexivity. }
  destruct bc; try (destruct (inb ctx t1 o1 && inb ctx t1 o2) eqn:Ei; [|discriminate]; injection H as <-; apply Hord; reflexivity).
  - injection H as <-. unfold branch_taken. apply bv_eqb_pword.
  - injection H as <-. unfold branch_taken. rewrite bv_eqb_pword. reflexivity.
Qed.

Definition br_null : br_rule := fun ctx bc a b =>
  match bc, a, b with
  | BC_EQ, VP t o, VC c => if inb ctx t o && is_zero c then Some false else None
  | BC_NE, VP t o, VC c => if inb ctx t o && is_zero c then Some true else None
  | BC_EQ, VC c, VP t o => if inb ctx t o && is_zero c then Some false else None
  | BC_NE, VC c, VP t o => if inb ctx t o && is_zero c then Some true else None
  | _, _, _ => None
  end.

Lemma pword_nonzero (rho : valuation) (ctx : vctx) (t : int) (o : w64) :
  ctx_ok rho ctx -> inb ctx t o = true -> bv_eqb (pword rho t o) (Z_to_bv 64 0) = false /\ bv_eqb (Z_to_bv 64 0) (pword rho t o) = false.
Proof.
  intros Hc Hi. destruct (inb_spec rho ctx t o Hc Hi) as [R U]. unfold bv_eqb. rewrite U.
  change (bv_unsigned (Z_to_bv 64 0)) with 0. split; apply Z.eqb_neq; lia.
Qed.

Lemma br_null_ok : br_rule_ok br_null.
Proof.
  intros rho ctx bc a b d x y Hc H Ha Hb. unfold br_null in H.
  destruct bc; try discriminate; destruct a as [ca|ta oa| |]; try discriminate; destruct b as [cb|tb ob| |]; try discriminate;
    match type of H with (if ?i && ?z then _ else _) = _ => destruct i eqn:Hi; [|discriminate]; destruct z eqn:Hz; [|discriminate] end;
    cbn [andb] in H; injection H as <-; apply is_zero_spec in Hz; subst; cbn [den] in *; subst x y;
    change (wbv w_zero) with (Z_to_bv 64 0); unfold branch_taken;
    destruct (pword_nonzero rho ctx _ _ Hc Hi) as [E1 E2]; rewrite ?E1, ?E2; reflexivity.
Qed.

Fixpoint first_br (rs : list br_rule) (ctx : vctx) (bc : branch_cond) (a b : hval) : option bool :=
  match rs with
  | [] => None
  | r :: rs' => match r ctx bc a b with Some d => Some d | None => first_br rs' ctx bc a b end
  end.

Lemma first_br_ok (rs : list br_rule) : Forall br_rule_ok rs ->
  forall rho ctx bc a b d x y, ctx_ok rho ctx -> first_br rs ctx bc a b = Some d -> den rho a x -> den rho b y -> branch_taken bc x y = d.
Proof.
  induction 1 as [|r rs Hr _ IH]; intros rho ctx bc a b d x y Hc H Ha Hb; cbn [first_br] in H; [discriminate|].
  destruct (r ctx bc a b) as [d'|] eqn:E.
  - injection H as <-. exact (Hr rho ctx bc a b d' x y Hc E Ha Hb).
  - exact (IH rho ctx bc a b d x y Hc H Ha Hb).
Qed.

Definition br_wrap : br_rule := fun ctx bc a b =>
  match bc, a, b with
  | BC_LTU, VP t o, VC c => if inb ctx t o && negb (wh c) && (wl c <=? wl o)%uint63 then Some false else None
  | BC_GEU, VP t o, VC c => if inb ctx t o && negb (wh c) && (wl c <=? wl o)%uint63 then Some true else None
  | _, _, _ => None
  end.

Lemma br_wrap_ok : br_rule_ok br_wrap.
Proof.
  intros rho ctx bc a b d x y Hc H Ha Hb. unfold br_wrap in H.
  destruct bc; try discriminate; destruct a as [|t o| |]; try discriminate; destruct b as [c| | |]; try discriminate;
    (destruct (inb ctx t o && negb (wh c) && (wl c <=? wl o)%uint63) eqn:E; [|discriminate]); injection H as <-;
    apply andb_prop in E as [E E3]; apply andb_prop in E as [E1 E2]; apply leb_spec in E3; apply negb_true_iff in E2;
    destruct (inb_spec rho ctx t o Hc E1) as [_ Ep]; cbn [den] in *; subst x y; unfold branch_taken, bv_ltu; rewrite Ep, wbv_unsigned;
    (assert (Hpos : 0 < rho t) by (unfold inb in E1; destruct (ctx t) as [[al sz]|] eqn:Ec; [exact (proj1 (proj2 (proj2 (Hc t al sz Ec)))) | discriminate]));
    (assert (EC : wZ c = to_Z (wl c)) by (unfold wZ; rewrite E2; lia));
    (assert (EO : to_Z (wl o) <= wZ o) by (unfold wZ, two63; destruct (wh o); lia));
    [|apply negb_true_iff]; apply Z.ltb_ge; lia.
Qed.

Definition br_not : br_rule := fun ctx bc a b =>
  match bc, a, b with
  | BC_LTU, VN t o, VC c => if inb ctx t o && negb (wh c) then Some false else None
  | BC_GEU, VN t o, VC c => if inb ctx t o && negb (wh c) then Some true else None
  | _, _, _ => None
  end.

Lemma br_not_ok : br_rule_ok br_not.
Proof.
  intros rho ctx bc a b d x y Hc H Ha Hb. unfold br_not in H.
  destruct bc; try discriminate; destruct a as [| | |t o]; try discriminate; destruct b as [c| | |]; try discriminate;
    (destruct (inb ctx t o && negb (wh c)) eqn:E; [|discriminate]); injection H as <-;
    apply andb_prop in E as [E1 E2]; apply negb_true_iff in E2;
    destruct (inb_spec rho ctx t o Hc E1) as [Hr Ep]; cbn [den] in *; subst y; unfold branch_taken, bv_ltu; rewrite Ha, Ep, wbv_unsigned;
    (assert (EC : wZ c < two63) by (unfold wZ; rewrite E2; pose proof (to_Z_bounded (wl c)) as Bc; rewrite wB_eq in Bc; unfold two63 in *; lia));
    [|apply negb_true_iff]; apply Z.ltb_ge; unfold two63, two64 in *; lia.
Qed.

Definition br_phigh : br_rule := fun ctx bc a b =>
  match bc, a, b with
  | BC_EQ, VP t o, VC c => if inb ctx t o && wh c then Some false else None
  | BC_NE, VP t o, VC c => if inb ctx t o && wh c then Some true else None
  | BC_LTU, VP t o, VC c => if inb ctx t o && wh c then Some true else None
  | BC_GEU, VP t o, VC c => if inb ctx t o && wh c then Some false else None
  | BC_EQ, VC c, VP t o => if inb ctx t o && wh c then Some false else None
  | BC_NE, VC c, VP t o => if inb ctx t o && wh c then Some true else None
  | BC_LTU, VC c, VP t o => if inb ctx t o && wh c then Some false else None
  | BC_GEU, VC c, VP t o => if inb ctx t o && wh c then Some true else None
  | _, _, _ => None
  end.

Lemma br_phigh_ok : br_rule_ok br_phigh.
Proof.
  intros rho ctx bc a b d x y Hc H Ha Hb. unfold br_phigh in H.
  destruct bc; try discriminate; destruct a as [ca|ta oa| |]; try discriminate; destruct b as [cb|tb ob| |]; try discriminate;
    match type of H with (if ?i && ?z then _ else _) = _ => destruct i eqn:Hi; [|discriminate]; destruct z eqn:Hz; [|discriminate] end;
    cbn [andb] in H; injection H as <-; cbn [den] in *; subst x y; unfold branch_taken, bv_eqb, bv_ltu;
    match goal with Hi' : inb ctx ?t ?o = true |- _ => destruct (inb_spec rho ctx t o Hc Hi') as [Hr Ep] end;
    rewrite Ep, wbv_unsigned;
    match goal with Hz' : wh ?c = true |- _ =>
      assert (EC : two63 <= wZ c) by (unfold wZ; rewrite Hz'; pose proof (to_Z_bounded (wl c)); lia) end;
    first [ apply Z.eqb_neq; lia | apply negb_true_iff; apply Z.eqb_neq; lia | apply Z.ltb_lt; lia | apply Z.ltb_ge; lia
          | apply negb_true_iff; apply Z.ltb_ge; lia | apply negb_false_iff; apply Z.ltb_lt; lia ].
Qed.

Definition br_rules : list br_rule := [br_conc; br_same; br_null; br_wrap; br_not; br_phigh].

Lemma br_rules_ok : Forall br_rule_ok br_rules.
Proof. repeat constructor; [apply br_conc_ok | apply br_same_ok | apply br_null_ok | apply br_wrap_ok | apply br_not_ok | apply br_phigh_ok]. Qed.

Definition v_branch (ctx : vctx) (bc : branch_cond) (a b : hval) : option bool := first_br br_rules ctx bc a b.

Lemma v_branch_ok (rho : valuation) (ctx : vctx) (bc : branch_cond) (a b : hval) (d : bool) (x y : bv 64) :
  ctx_ok rho ctx -> v_branch ctx bc a b = Some d -> den rho a x -> den rho b y -> branch_taken bc x y = d.
Proof. apply first_br_ok. apply br_rules_ok. Qed.

Definition v_op32 (op : aluop) (a b : hval) : hval :=
  match a, b with
  | VC x, VC y => VC (w_sext32 (w_alu32 op (w_low32 x) (w_low32 y)))
  | _, _ => VU
  end.

Lemma v_op32_ok (rho : valuation) (op : aluop) (a b : hval) (x y : bv 64) :
  den rho a x -> den rho b y -> den rho (v_op32 op a b) (sext 64 (alu32 op (low32 x) (low32 y))).
Proof.
  intros Ha Hb. destruct a as [wa| | |]; try exact I. destruct b as [wb| | |]; try exact I.
  cbn [den v_op32] in *. subst x y. symmetry. apply w_op32_ok; symmetry; apply low32_wbv.
Qed.

Definition v_muldiv (op : mulop) (a b : hval) : hval :=
  match a, b with VC x, VC y => VC (w_muldiv op x y) | _, _ => VU end.

Lemma v_muldiv_ok (rho : valuation) (op : mulop) (a b : hval) (x y : bv 64) :
  den rho a x -> den rho b y -> den rho (v_muldiv op a b) (mul_div op x y).
Proof.
  intros Ha Hb. destruct a as [wa| | |]; try exact I. destruct b as [wb| | |]; try exact I.
  cbn [den v_muldiv] in *. subst x y. symmetry. apply w_muldiv_ok.
Qed.

Definition v_muldiv32 (op : mulop) (a b : hval) : hval :=
  match a, b with
  | VC x, VC y => VC (w_sext32 (w_muldiv32 op (w_low32 x) (w_low32 y)))
  | _, _ => VU
  end.

Lemma v_muldiv32_ok (rho : valuation) (op : mulop) (a b : hval) (x y : bv 64) :
  den rho a x -> den rho b y -> den rho (v_muldiv32 op a b) (sext 64 (mul_div op (low32 x) (low32 y))).
Proof.
  intros Ha Hb. destruct a as [wa| | |]; try exact I. destruct b as [wb| | |]; try exact I.
  cbn [den v_muldiv32] in *. subst x y. symmetry. apply w_sext32_ok.
  apply w_muldiv32_ok; symmetry; apply low32_wbv.
Qed.
