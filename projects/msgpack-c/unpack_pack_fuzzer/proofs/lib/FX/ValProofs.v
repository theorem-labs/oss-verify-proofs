(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List Lia.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem Fpu.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 W64Proofs Val Instr State Step Plan.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val FI St Step Plan.
Open Scope Z_scope.
Unset Lia Cache.

Module ValP.

Lemma aluop_eqb_eq a b : aluop_eqb a b = true -> a = b.
Proof. destruct a, b; cbn; congruence. Qed.
Lemma mulop_eqb_eq a b : mulop_eqb a b = true -> a = b.
Proof. destruct a, b; cbn; congruence. Qed.
Lemma ffmt_eqb_eq a b : ffmt_eqb a b = true -> a = b.
Proof. destruct a, b; cbn; congruence. Qed.
Lemma rmode_eqb_eq a b : rmode_eqb a b = true -> a = b.
Proof. destruct a, b; cbn; congruence. Qed.
Lemma fop1_eqb_eq a b : fop1_eqb a b = true -> a = b.
Proof.
  destruct a, b; cbn; try congruence.
  intros H. apply andb_prop in H as [H1 H3]. apply andb_prop in H1 as [H1 H2].
  apply ffmt_eqb_eq in H1. apply ffmt_eqb_eq in H2. apply rmode_eqb_eq in H3. congruence.
Qed.
Lemma int_eqb_eq (a b : int) : PrimInt63.eqb a b = true -> a = b.
Proof. apply eqb_correct. Qed.
Lemma weqb_eq a b : weqb a b = true -> a = b.
Proof. apply weqb_ok. Qed.
Lemma bool_eqb_eq (a b : bool) : Bool.eqb a b = true -> a = b.
Proof. apply eqb_prop. Qed.

Ltac vp_eqb_split H :=
  repeat match goal with
  | G : weqb _ _ = true |- _ => apply weqb_eq in G
  | G : _ && _ = true |- _ => apply andb_prop in G as [G ?]
  | G : PrimInt63.eqb _ _ = true |- _ => apply int_eqb_eq in G
  | G : weqb _ _ = true |- _ => apply weqb_eq in G
  | G : Bool.eqb _ _ = true |- _ => apply bool_eqb_eq in G
  | G : aluop_eqb _ _ = true |- _ => apply aluop_eqb_eq in G
  | G : mulop_eqb _ _ = true |- _ => apply mulop_eqb_eq in G
  | G : fop1_eqb _ _ = true |- _ => apply fop1_eqb_eq in G
  end.

Lemma sv_eqb_eq : forall a b, sv_eqb a b = true -> a = b.
Proof.
  induction a; destruct b; cbn [sv_eqb]; intros H; try discriminate; vp_eqb_split H;
  repeat match goal with
  | IH : forall b, sv_eqb ?a b = true -> ?a = b, G : sv_eqb ?a _ = true |- _ => apply IH in G
  end; subst; reflexivity.
Qed.

Lemma aluop_eqb_refl a : aluop_eqb a a = true. Proof. destruct a; reflexivity. Qed.
Lemma mulop_eqb_refl a : mulop_eqb a a = true. Proof. destruct a; reflexivity. Qed.
Lemma fop1_eqb_refl a : fop1_eqb a a = true. Proof. destruct a as [| |[] [] []]; reflexivity. Qed.

Lemma sv_eqb_refl : forall a, sv_eqb a a = true.
Proof.
  induction a; cbn [sv_eqb]; rewrite ?Uint63.eqb_refl, ?weqb_refl, ?Bool.eqb_reflx, ?aluop_eqb_refl, ?mulop_eqb_refl, ?fop1_eqb_refl, ?IHa, ?IHa1, ?IHa2; reflexivity.
Qed.

Lemma den_vlit : forall E i, den E (vlit i) = Z_to_bv 64 (to_Z i).
Proof. intros E i. cbn [den vlit]. unfold wbv. rewrite wlit_ok. reflexivity. Qed.

Lemma wbv_wadd a b : wbv (wadd a b) = (wbv a + wbv b)%bv.
Proof. exact (walu_ok ALU_ADD a b). Qed.
Lemma wbv_wsub a b : wbv (wsub a b) = (wbv a - wbv b)%bv.
Proof. exact (walu_ok ALU_SUB a b). Qed.
Lemma weqb_wzero_unsigned c : weqb c wzero = true -> bv_unsigned (wbv c) = 0.
Proof. intros H. apply weqb_eq in H. subst. reflexivity. Qed.
Lemma weqb_wones_unsigned c : weqb c wones = true -> bv_unsigned (wbv c) = two64 - 1.
Proof. intros H. apply weqb_eq in H. subst. reflexivity. Qed.
Lemma shamt6_zero c : PrimInt63.eqb (shamt6 c) 0%uint63 = true ->
  bv_unsigned (bv_and (wbv c) (Z_to_bv 64 63)) = 0.
Proof. intros H. apply int_eqb_eq in H. rewrite shamt6_bv, H. reflexivity. Qed.

Section alu_cases.
  Variable E : env.
  Implicit Types x y : word.
  Lemma alu_lit op a b : den E (VL (walu op a b)) = alu64 op (den E (VL a)) (den E (VL b)).
  Proof. cbn [den]. apply walu_ok. Qed.
  Lemma alu_add_pl k o c : den E (VP k (wadd o c)) = alu64 ALU_ADD (den E (VP k o)) (den E (VL c)).
  Proof. cbn [den alu64 alu]. rewrite wbv_wadd. bv_solve. Qed.
  Lemma alu_add_lp k o c : den E (VP k (wadd o c)) = alu64 ALU_ADD (den E (VL c)) (den E (VP k o)).
  Proof. cbn [den alu64 alu]. rewrite wbv_wadd. bv_solve. Qed.
  Lemma alu_sub_pl k o c : den E (VP k (wsub o c)) = alu64 ALU_SUB (den E (VP k o)) (den E (VL c)).
  Proof. cbn [den alu64 alu]. rewrite wbv_wsub. bv_solve. Qed.
  Lemma alu_sub_pp k o1 o2 : den E (VL (wsub o1 o2)) = alu64 ALU_SUB (den E (VP k o1)) (den E (VP k o2)).
  Proof. cbn [den alu64 alu]. rewrite wbv_wsub. bv_solve. Qed.
  Lemma alu_add_x0 x y : bv_unsigned y = 0 -> x = alu64 ALU_ADD x y.
  Proof. intros H. cbn [alu64 alu]. bv_solve. Qed.
  Lemma alu_add_0x x y : bv_unsigned y = 0 -> x = alu64 ALU_ADD y x.
  Proof. intros H. cbn [alu64 alu]. bv_solve. Qed.
  Lemma alu_sub_x0 x y : bv_unsigned y = 0 -> x = alu64 ALU_SUB x y.
  Proof. intros H. cbn [alu64 alu]. bv_solve. Qed.
  Lemma alu_or_x0 x y : bv_unsigned y = 0 -> x = alu64 ALU_OR x y.
  Proof. intros H. cbn [alu64 alu]. symmetry. apply bv_or_0_r. exact H. Qed.
  Lemma alu_or_0x x y : bv_unsigned y = 0 -> x = alu64 ALU_OR y x.
  Proof. intros H. cbn [alu64 alu]. symmetry. apply bv_or_0_l. exact H. Qed.
  Lemma alu_xor_x0 x y : bv_unsigned y = 0 -> x = alu64 ALU_XOR x y.
  Proof. intros H. cbn [alu64 alu]. apply bv_eq. rewrite bv_xor_unsigned, H, Z.lxor_0_r. reflexivity. Qed.
  Lemma alu_xor_0x x y : bv_unsigned y = 0 -> x = alu64 ALU_XOR y x.
  Proof. intros H. cbn [alu64 alu]. apply bv_eq. rewrite bv_xor_unsigned, H, Z.lxor_0_l. reflexivity. Qed.
  Lemma alu_and_x1 x y : bv_unsigned y = two64 - 1 -> x = alu64 ALU_AND x y.
  Proof.
    intros H. cbn [alu64 alu]. apply bv_eq. rewrite bv_and_unsigned, H.
    change (two64 - 1) with (Z.ones 64). rewrite Z.land_ones by (pose proof (bv_unsigned_in_range _ x); lia).
    symmetry. apply Z.mod_small. pose proof (bv_unsigned_in_range _ x). unfold bv_modulus in *. exact H0.
  Qed.
  Lemma alu_and_x0 x y : bv_unsigned y = 0 -> wbv wzero = alu64 ALU_AND x y.
  Proof. intros H. cbn [alu64 alu]. apply bv_eq. rewrite bv_and_unsigned, H, Z.land_0_r, wbv_unsigned, wzero_ok. reflexivity. Qed.
  Lemma alu_and_0x x y : bv_unsigned y = 0 -> wbv wzero = alu64 ALU_AND y x.
  Proof. intros H. cbn [alu64 alu]. apply bv_eq. rewrite bv_and_unsigned, H, Z.land_0_l, wbv_unsigned, wzero_ok. reflexivity. Qed.
  Lemma alu_and_1x x y : bv_unsigned y = two64 - 1 -> x = alu64 ALU_AND y x.
  Proof.
    intros H. cbn [alu64 alu]. apply bv_eq. rewrite bv_and_unsigned, H, Z.land_comm.
    change (two64 - 1) with (Z.ones 64). rewrite Z.land_ones by (pose proof (bv_unsigned_in_range _ x); lia).
    symmetry. apply Z.mod_small. pose proof (bv_unsigned_in_range _ x). unfold bv_modulus in *. exact H0.
  Qed.
  Lemma alu_sll_x0 x c : bv_unsigned (bv_and (wbv c) (Z_to_bv 64 63)) = 0 -> x = alu64 ALU_SLL x (den E (VL c)).
  Proof. intros H. cbn [alu64 alu den]. apply bv_eq. rewrite bv_shiftl_unsigned, H, Z.shiftl_0_r, bv_wrap_bv_unsigned. reflexivity. Qed.
  Lemma alu_srl_x0 x c : bv_unsigned (bv_and (wbv c) (Z_to_bv 64 63)) = 0 -> x = alu64 ALU_SRL x (den E (VL c)).
  Proof. intros H. cbn [alu64 alu den]. apply bv_eq. rewrite bv_shiftr_unsigned, H, Z.shiftr_0_r. reflexivity. Qed.
  Lemma alu_sra_x0 x c : bv_unsigned (bv_and (wbv c) (Z_to_bv 64 63)) = 0 -> x = alu64 ALU_SRA x (den E (VL c)).
  Proof. intros H. cbn [alu64 alu den]. apply bv_eq_signed. rewrite bv_ashiftr_signed, H, Z.shiftr_0_r, bv_swrap_bv_signed. reflexivity. Qed.
End alu_cases.

Lemma den_add_lit_fold : forall E a c, den E (add_lit_fold a c) = alu64 ALU_ADD (den E a) (den E (VL c)).
Proof.
  intros E a c.
  assert (G : forall u k o, (u + (ev E k + wbv (wadd o c)))%bv = ((u + (ev E k + wbv o)) + wbv c)%bv).
  { intros. rewrite wbv_wadd. bv_solve. }
  assert (G2 : forall u k o, ((ev E k + wbv (wadd o c)) + u)%bv = (((ev E k + wbv o) + u) + wbv c)%bv).
  { intros. rewrite wbv_wadd. bv_solve. }
  unfold add_lit_fold.
  destruct a as [| |op x y| | | | | | | |]; try reflexivity.
  destruct op; try reflexivity.
  - destruct y as [|k o| | | | | | | | |]; destruct x as [|k' o'| | | | | | | | |]; cbn [den alu64 alu];
      first [apply G | apply G2 | reflexivity].
  - destruct y as [c'| | | | | | | | | |]; try reflexivity.
    destruct (weqb c c') eqn:Hc; [|reflexivity]. apply weqb_eq in Hc. subst c'. cbn [den alu64 alu]. bv_solve.
Qed.

Lemma wbv_wzero : wbv wzero = Z_to_bv 64 0.
Proof. apply bv_eq. rewrite wbv_unsigned, wzero_ok. reflexivity. Qed.

Lemma den_sv_alu0 : forall E op a b, den E (sv_alu0 op a b) = alu64 op (den E a) (den E b).
Proof.
  intros E op a b. unfold sv_alu0.
  destruct a; destruct b; destruct op; lazy beta iota zeta; try reflexivity; try apply alu_lit;
  repeat match goal with
  | |- context [if weqb ?w wzero then _ else _] =>
      destruct (weqb w wzero) eqn:?Hw; [apply weqb_wzero_unsigned in Hw|first [reflexivity | apply den_add_lit_fold | rewrite den_add_lit_fold | idtac]]
  | |- context [if weqb ?w wones then _ else _] =>
      destruct (weqb w wones) eqn:?Hw1; [apply weqb_wones_unsigned in Hw1|try reflexivity]
  | |- context [if PrimInt63.eqb (shamt6 ?w) 0 then _ else _] =>
      destruct (PrimInt63.eqb (shamt6 w) 0) eqn:?Hs; [apply shamt6_zero in Hs|reflexivity]
  | |- context [if PrimInt63.eqb ?k ?k' then _ else _] =>
      destruct (PrimInt63.eqb k k') eqn:?Hk; [apply int_eqb_eq in Hk; subst|reflexivity]
  | |- context [if sv_eqb ?x ?y then _ else _] =>
      destruct (sv_eqb x y) eqn:?Hq; [apply sv_eqb_eq in Hq|reflexivity]
  | |- den _ (match ?o with ALU_ADD => _ | _ => _ end) = _ => destruct o; try reflexivity; try apply den_add_lit_fold
  end;
  try match goal with H : @eq sv _ _ |- _ => first [rewrite <- H | rewrite H]; clear H end;
  first [ apply alu_add_pl | apply alu_add_lp | apply alu_sub_pl | apply alu_sub_pp
        | apply alu_add_x0; assumption | apply alu_add_0x; assumption | apply alu_sub_x0; assumption
        | apply alu_or_x0; assumption | apply alu_or_0x; assumption
        | apply alu_xor_x0; assumption | apply alu_xor_0x; assumption
        | apply alu_sll_x0; assumption | apply alu_srl_x0; assumption | apply alu_sra_x0; assumption
        | apply alu_and_x1; assumption | apply alu_and_1x; assumption
        | apply alu_and_x0; assumption | apply alu_and_0x; assumption
        | idtac ].
  all: cbn [den alu64 alu]; rewrite ?wbv_wzero.
  all: try (apply bv_eq; rewrite ?bv_sub_unsigned, ?bv_xor_unsigned, ?Z.lxor_nilpotent, ?Z.sub_diag; reflexivity).
  all: try bv_solve.

  all: repeat match goal with |- den _ (match ?x with VP _ _ => _ | _ => _ end) = _ => destruct x end.
  all: cbn [den alu64 alu].
  all: try bv_solve.
  all: repeat match goal with
  | |- context [if weqb ?w wzero then _ else _] =>
      destruct (weqb w wzero) eqn:?Hw; [apply weqb_wzero_unsigned in Hw|first [reflexivity | apply den_add_lit_fold | rewrite den_add_lit_fold | idtac]]
  | |- context [if sv_eqb ?x ?y then _ else _] =>
      destruct (sv_eqb x y) eqn:?Hq; [apply sv_eqb_eq in Hq; subst|]
  | |- den _ (match ?o with ALU_ADD => _ | _ => _ end) = _ => destruct o
  | |- den _ (match ?x with VP _ _ => _ | _ => _ end) = _ => destruct x
  end.
  all: cbn [den alu64 alu].
  all: try reflexivity.
  all: try bv_solve.
  all: rewrite den_add_lit_fold; cbn [den alu64 alu]; try reflexivity; try bv_solve.
Qed.

Lemma den_sv_aluw : forall E op a b,
  den E (sv_aluw op a b) = sext 64 (alu32 op (low32 (den E a)) (low32 (den E b))).
Proof. intros E op a b. unfold sv_aluw. destruct a; destruct b; lazy beta iota zeta; try reflexivity. cbn [den]. apply walu32_ok. Qed.
Lemma den_sv_md : forall E op a b, den E (sv_md op a b) = mul_div op (den E a) (den E b).
Proof. intros E op a b. unfold sv_md. destruct a; destruct b; lazy beta iota zeta; try reflexivity. cbn [den]. apply wmd_ok. Qed.
Lemma den_sv_mdw : forall E op a b,
  den E (sv_mdw op a b) = sext 64 (mul_div op (low32 (den E a)) (low32 (den E b))).
Proof. intros E op a b. unfold sv_mdw. destruct a; destruct b; lazy beta iota zeta; try reflexivity. cbn [den]. apply wmd32_ok. Qed.

Lemma pow2_le_64 n : 0 <= n <= 8 -> 1 <= 2 ^ (8 * n) <= 2 ^ 64.
Proof. intros. split. - change 1 with (2 ^ 0). apply Z.pow_le_mono_r; lia. - apply Z.pow_le_mono_r; lia. Qed.

Lemma ext_Z_range : forall sx lo n z, 0 <= lo -> 0 < n -> n <= 8 -> 0 <= ext_Z sx lo n z < two64.
Proof.
  intros sx lo n z Hlo Hn Hn8. unfold ext_Z.
  pose proof (pow2_le_64 n ltac:(lia)) as HP.
  assert (HU : 0 <= (z / 2 ^ (8 * lo)) mod 2 ^ (8 * n) < 2 ^ (8 * n)) by (apply Z.mod_pos_bound; lia).
  set (u := (z / 2 ^ (8 * lo)) mod 2 ^ (8 * n)) in *. clearbody u.
  rewrite two64_eq. destruct sx.
  - apply Z.mod_pos_bound. reflexivity.
  - lia.
Qed.

Lemma Z256 : 256 = 2 ^ 8. Proof. reflexivity. Qed.

Ltac vp_tb := repeat (W64Proofs.w64_tb_step || rewrite pow2_m1_ones).

Lemma ext_Z_byte : forall lo n z i, 0 <= lo -> 0 <= i < n -> 0 <= z ->
  (ext_Z false lo n z / 2 ^ (8 * i)) mod 256 = (z / 2 ^ (8 * (lo + i))) mod 256.
Proof.
  intros lo n z i Hlo Hi Hz. unfold ext_Z. rewrite Z256.
  apply Z.bits_inj'; intros m Hm. vp_tb.
  destruct (Z.ltb_spec m 8); [|reflexivity].
  destruct (Z.ltb_spec (m + 8 * i) (8 * n)); [|exfalso; lia].
  cbn [andb]. f_equal. lia.
Qed.

Ltac vp_tbfin :=
  w64_bcase; rewrite ?andb_true_r, ?andb_false_r, ?andb_false_l, ?orb_false_r, ?orb_false_l;
  cbn [andb orb negb]; try reflexivity; try (f_equal; lia).

Lemma ins_Z_byte_in : forall lo n a v i, 0 <= lo -> 0 < n -> lo + n <= 8 -> 0 <= a -> 0 <= v ->
  lo <= i < lo + n -> (ins_Z lo n a v / 2 ^ (8 * i)) mod 256 = (v / 2 ^ (8 * (i - lo))) mod 256.
Proof.
  intros lo n a v i Hlo Hn Hle Ha Hv Hi. unfold ins_Z. rewrite Z256, pow2_m1_ones.
  apply Z.bits_inj'; intros m Hm. vp_tb.
  destruct (Z.ltb_spec m 8); cbn [andb]; [|reflexivity]. vp_tb. vp_tbfin.
Qed.

Lemma ins_Z_byte_out : forall lo n a v i, 0 <= lo -> 0 < n -> lo + n <= 8 -> 0 <= a < two64 -> 0 <= v ->
  0 <= i < 8 -> ~ (lo <= i < lo + n) -> (ins_Z lo n a v / 2 ^ (8 * i)) mod 256 = (a / 2 ^ (8 * i)) mod 256.
Proof.
  intros lo n a v i Hlo Hn Hle Ha Hv Hi Hni. unfold ins_Z. rewrite Z256, pow2_m1_ones.
  apply Z.bits_inj'; intros m Hm. vp_tb.
  destruct (Z.ltb_spec m 8); cbn [andb]; [|reflexivity].
  w64_bcase. all: try rewrite (Z.testbit_neg_r (Z.ones _)) by lia. all: vp_tb; vp_tbfin.
Qed.

Lemma ins_Z_range : forall lo n a v, 0 <= lo -> 0 < n -> lo + n <= 8 -> 0 <= a < two64 -> 0 <= ins_Z lo n a v < two64.
Proof.
  intros lo n a v Hlo Hn Hle Ha. unfold ins_Z. rewrite two64_eq in *.
  assert (HP : 1 <= 2 ^ (8 * n) <= 2 ^ 64) by (apply pow2_le_64; lia).
  assert (HPl : 1 <= 2 ^ (8 * lo) <= 2 ^ 64) by (apply pow2_le_64; lia).
  assert (HPs : 2 ^ (8 * n) * 2 ^ (8 * lo) <= 2 ^ 64).
  { rewrite <- Z.pow_add_r by lia. apply Z.pow_le_mono_r; lia. }
  apply lor_range.
  - apply land_range_l. exact Ha.
  - assert (HL : 0 <= Z.land v (2 ^ (8 * n) - 1) < 2 ^ (8 * n)) by (apply land_range_r; lia).
    rewrite Z.shiftl_mul_pow2 by lia. nia.
Qed.

Lemma sx_presentation : forall k u, 0 < k ->
  (if 2 ^ (k - 1) <=? u mod 2 ^ k then u mod 2 ^ k - 2 ^ k else u mod 2 ^ k)
  = (u + 2 ^ (k - 1)) mod 2 ^ k - 2 ^ (k - 1).
Proof.
  intros k u Hk.
  assert (H2 : 2 ^ k = 2 * 2 ^ (k - 1)) by (rewrite <- Z.pow_succ_r by lia; f_equal; lia).
  assert (Hp : 0 < 2 ^ (k - 1)) by (apply Z.pow_pos_nonneg; lia).
  assert (Hr : 0 <= u mod 2 ^ k < 2 ^ k) by (apply Z.mod_pos_bound; lia).
  rewrite <- (Z.add_mod_idemp_l u) by lia.
  rewrite (mod_cases2 (u mod 2 ^ k + 2 ^ (k - 1))) by lia.
  destruct (Z.leb_spec (2 ^ (k - 1)) (u mod 2 ^ k)); destruct (Z.ltb_spec (u mod 2 ^ k + 2 ^ (k - 1)) (2 ^ k)); lia.
Qed.

Lemma ext_word_sext_k : forall (m : N) (n : Z) (w : word), 0 < n -> Z.of_N m = 8 * n ->
  ext_word true 0 n w = sext 64 (bv_extract 0 m w).
Proof.
  intros m n w Hn Hm. unfold ext_word, ext_Z, sext. apply bv_eq.
  rewrite Z_to_bv_unsigned, bv_sign_extend_unsigned, bv_extract_signed.
  change (8 * 0) with 0. rewrite Z.pow_0_r, Z.div_1_r, Z.shiftr_0_r.
  change two64 with (bv_modulus 64).
  match goal with |- bv_wrap 64 (?x mod bv_modulus 64) = _ => change (x mod bv_modulus 64) with (bv_wrap 64 x) end.
  rewrite bv_wrap_idemp. f_equal.
  unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. rewrite Hm.
  replace (2 ^ (8 * n) `div` 2) with (2 ^ (8 * n - 1)) by (change 2 with (2 ^ 1) at 3; rewrite <- Z.pow_sub_r by lia; reflexivity).
  apply sx_presentation. lia.
Qed.

Lemma ext_word_sext8 : forall w : word, ext_word true 0 1 w = sext 64 (bv_extract 0 8 w).
Proof. intros w. apply ext_word_sext_k; reflexivity. Qed.
Lemma ext_word_sext16 : forall w : word, ext_word true 0 2 w = sext 64 (bv_extract 0 16 w).
Proof. intros w. apply ext_word_sext_k; reflexivity. Qed.
Lemma ext_word_sext32 : forall w : word, ext_word true 0 4 w = sext 64 (bv_extract 0 32 w).
Proof. intros w. apply ext_word_sext_k; reflexivity. Qed.

Lemma ext_word_zext_k : forall (m : N) (n : Z) (w : word), 0 < n -> Z.of_N m = 8 * n ->
  ext_word false 0 n w = zext 64 (bv_extract 0 m w).
Proof.
  intros m n w Hn Hm. unfold ext_word, ext_Z, zext. apply bv_eq.
  rewrite Z_to_bv_unsigned, bv_zero_extend_unsigned', bv_extract_0_unsigned.
  f_equal. change (8 * 0) with 0. rewrite Z.pow_0_r, Z.div_1_r.
  unfold bv_wrap, bv_modulus. rewrite Hm. reflexivity.
Qed.
Lemma ext_word_zext8 : forall w : word, ext_word false 0 1 w = zext 64 (bv_extract 0 8 w).
Proof. intros w. apply ext_word_zext_k; reflexivity. Qed.
Lemma ext_word_zext16 : forall w : word, ext_word false 0 2 w = zext 64 (bv_extract 0 16 w).
Proof. intros w. apply ext_word_zext_k; reflexivity. Qed.
Lemma ext_word_zext32 : forall w : word, ext_word false 0 4 w = zext 64 (bv_extract 0 32 w).
Proof. intros w. apply ext_word_zext_k; reflexivity. Qed.

Lemma ext_Z_id64 : forall sx u, 0 <= u < two64 -> ext_Z sx 0 8 u = u.
Proof.
  intros sx u Hu. unfold ext_Z. change (8 * 8 - 1) with 63. change (8 * 8) with 64. change (8 * 0) with 0.
  rewrite Z.pow_0_r, Z.div_1_r, <- two64_eq.
  rewrite (Z.mod_small u two64) by lia.
  destruct sx; [|reflexivity].
  destruct (Z.leb_spec (2 ^ 63) u).
  - unfold two64 in *. symmetry. apply Z.mod_unique_pos with (q := -1); lia.
  - apply Z.mod_small; lia.
Qed.

Lemma ext_word_id64 : forall sx (w : word), ext_word sx 0 8 w = w.
Proof.
  intros sx w. unfold ext_word. rewrite ext_Z_id64. apply Z_to_bv_bv_unsigned.
  rewrite <- bv_modulus_64. apply bv_unsigned_in_range.
Qed.

Lemma low32_ext : forall w : word, bv_unsigned (low32 w) = bv_unsigned w mod 2 ^ 32.
Proof. intros w. unfold low32. rewrite bv_extract_0_unsigned. reflexivity. Qed.

Definition width_ok (lo n : Z) : Prop := 0 <= lo /\ 1 <= n /\ lo + n <= 8.

Lemma bytes_le_to_Z_nonneg : forall bs, 0 <= bytes_le_to_Z bs.
Proof.
  induction bs as [|b bs IH]; cbn [bytes_le_to_Z]; [lia|].
  apply Z.lor_nonneg. split; [apply bv_unsigned_in_range|]. rewrite Z.shiftl_nonneg. exact IH.
Qed.

Lemma bytes_le_to_Z_cons_tb : forall b bs m, 0 <= m ->
  Z.testbit (bytes_le_to_Z (b :: bs)) m = if m <? 8 then Z.testbit (bv_unsigned b) m else Z.testbit (bytes_le_to_Z bs) (m - 8).
Proof.
  intros b bs m Hm. cbn [bytes_le_to_Z]. rewrite Z.lor_spec, Z.shiftl_spec by lia.
  pose proof (bv_unsigned_in_range 8 b) as Hb. change (bv_modulus 8) with (2 ^ 8) in Hb.
  destruct (Z.ltb_spec m 8).
  - rewrite (Z.testbit_neg_r _ (m - 8)) by lia. apply orb_false_r.
  - rewrite (testbit_high _ 8) by lia. reflexivity.
Qed.

Lemma bytes_le_to_Z_firstn_tb : forall k bs m, 0 <= m ->
  Z.testbit (bytes_le_to_Z (firstn k bs)) m = (m <? 8 * Z.of_nat k) && Z.testbit (bytes_le_to_Z bs) m.
Proof.
  induction k as [|k IH]; intros bs m Hm.
  - cbn [firstn bytes_le_to_Z Z.of_nat]. rewrite Z.mul_0_r, Z.bits_0. destruct (Z.ltb_spec m 0); [lia|reflexivity].
  - destruct bs as [|b bs]; cbn [firstn].
    + cbn [bytes_le_to_Z]. rewrite Z.bits_0, andb_false_r. reflexivity.
    + rewrite !bytes_le_to_Z_cons_tb by lia. destruct (Z.ltb_spec m 8).
      * destruct (Z.ltb_spec m (8 * Z.of_nat (S k))); [reflexivity|lia].
      * rewrite IH by lia. destruct (Z.ltb_spec (m - 8) (8 * Z.of_nat k)), (Z.ltb_spec m (8 * Z.of_nat (S k))); try reflexivity; lia.
Qed.

Lemma bytes_le_to_Z_skipn_tb : forall k bs m, 0 <= m ->
  Z.testbit (bytes_le_to_Z (skipn k bs)) m = Z.testbit (bytes_le_to_Z bs) (m + 8 * Z.of_nat k).
Proof.
  induction k as [|k IH]; intros bs m Hm.
  - cbn [skipn]. f_equal. lia.
  - destruct bs as [|b bs]; cbn [skipn].
    + cbn [bytes_le_to_Z]. rewrite !Z.bits_0. reflexivity.
    + rewrite bytes_le_to_Z_cons_tb by lia. destruct (Z.ltb_spec (m + 8 * Z.of_nat (S k)) 8); [lia|].
      rewrite IH by lia. f_equal. lia.
Qed.

Lemma firstn_skipn_firstn {A} : forall (n lo n' : nat) (l : list A), (lo + n <= n')%nat ->
  firstn n (skipn lo (firstn n' l)) = firstn n (skipn lo l).
Proof.
  intros n lo n' l H. rewrite skipn_firstn_comm, firstn_firstn. f_equal. lia.
Qed.

Lemma bg_bytes_firstn : forall g n s N', (n <= N')%nat -> firstn n (bg_bytes g s N') = bg_bytes g s n.
Proof.
  intros g n. induction n as [|n IHn]; intros s N' H; [reflexivity|].
  destruct N' as [|N']; [lia|]. cbn [bg_bytes]. rewrite firstn_cons. f_equal. apply IHn. lia.
Qed.

Lemma bg_bytes_shift : forall g n lo s N', (lo + n <= N')%nat ->
  firstn n (skipn lo (bg_bytes g s N')) = bg_bytes g (s + Z.of_nat lo) n.
Proof.
  intros g n lo. induction lo as [|lo IH]; intros s N' H.
  - rewrite skipn_O, Z.add_0_r. apply bg_bytes_firstn. lia.
  - destruct N' as [|N']; [lia|]. cbn [bg_bytes]. rewrite skipn_cons, IH by lia. f_equal. lia.
Qed.

Lemma ext_core_tb : forall sx' n' z j, 0 <= z -> 0 <= j < 8 * n' -> j < 64 ->
  Z.testbit (bv_wrap 64 (ext_Z sx' 0 n' z)) j = Z.testbit z j.
Proof.
  intros sx' n' z j Hz Hj Hj64. unfold bv_wrap. rewrite bv_modulus_64, two64_eq.
  rewrite Z.mod_pow2_bits_low by lia. unfold ext_Z. change (8 * 0) with 0. rewrite Z.pow_0_r, Z.div_1_r.
  assert (Hu : 0 <= z mod 2 ^ (8 * n') < 2 ^ (8 * n')) by (apply Z.mod_pos_bound; apply Z.pow_pos_nonneg; lia).
  destruct sx'.
  - rewrite two64_eq, Z.mod_pow2_bits_low by lia.
    destruct (Z.leb_spec (2 ^ (8 * n' - 1)) (z mod 2 ^ (8 * n'))).
    + rewrite testbit_sub_pow2 by lia. destruct (Z.ltb_spec j (8 * n')); [|lia]. apply Z.mod_pow2_bits_low. lia.
    + apply Z.mod_pow2_bits_low. lia.
  - apply Z.mod_pow2_bits_low. lia.
Qed.

Lemma ext_narrow : forall sx sx' lo n n' z z', 0 <= lo -> 0 < n -> lo + n <= n' -> lo + n <= 8 -> 0 <= z -> 0 <= z' ->
  (forall m, 0 <= m < 8 * n -> Z.testbit z' m = Z.testbit z (m + 8 * lo)) ->
  ext_Z sx lo n (bv_wrap 64 (ext_Z sx' 0 n' z)) = ext_Z sx 0 n z'.
Proof.
  intros sx sx' lo n n' z z' Hlo Hn Hle H8 Hz Hz' Htb. unfold ext_Z at 1 3.
  change (8 * 0) with 0. rewrite Z.pow_0_r, Z.div_1_r.
  replace ((bv_wrap 64 (ext_Z sx' 0 n' z) / 2 ^ (8 * lo)) mod 2 ^ (8 * n)) with (z' mod 2 ^ (8 * n)); [reflexivity|].
  apply Z.bits_inj'; intros m Hm. rewrite !Z.testbit_mod_pow2, Z.div_pow2_bits by lia.
  destruct (Z.ltb_spec m (8 * n)); [|reflexivity]. cbn [andb].
  rewrite ext_core_tb by lia. rewrite Htb by lia. reflexivity.
Qed.

Lemma w2Zs_wadd_small : forall off lo, 0 <= to_Z lo < 8 ->
  wt off || negb (wt (wadd off (wlit lo))) = true ->
  w2Zs (wadd off (wlit lo)) = w2Zs off + to_Z lo.
Proof.
  intros off lo Hlo Hg.
  pose proof (w2Z_range off) as Ro. pose proof (w2Z_range (wadd off (wlit lo))) as Rs.
  pose proof (w2Z_wt off) as Wo. pose proof (w2Z_wt (wadd off (wlit lo))) as Ws.
  unfold w2Zs. rewrite Wo, Ws in *. rewrite wadd_ok, wlit_ok in *.
  unfold two63, two64 in *.
  destruct (Z.leb_spec 9223372036854775808 (w2Z off)); cbn [orb negb] in Hg.
  - destruct (Z.ltb_spec (w2Z off + to_Z lo) 18446744073709551616).
    + rewrite Z.mod_small in * by lia. destruct (Z.leb_spec 9223372036854775808 (w2Z off + to_Z lo)); lia.
    + rewrite (mod_cases2 (w2Z off + to_Z lo)) in * by lia.
      destruct (Z.ltb_spec (w2Z off + to_Z lo) 18446744073709551616); [lia|].
      destruct (Z.leb_spec 9223372036854775808 (w2Z off + to_Z lo - 18446744073709551616)); lia.
  - rewrite Z.mod_small in * by lia.
    destruct (Z.leb_spec 9223372036854775808 (w2Z off + to_Z lo)); [discriminate|lia].
Qed.

Module BDP.
Import BD.

Definition tb (E : env) (x : sv) (m : Z) : bool := Z.testbit (bv_unsigned (den E x)) m.

Lemma tb_high E x m : 64 <= m -> tb E x m = false.
Proof. intros Hm. unfold tb. apply bv_unsigned_spec_high. cbn. lia. Qed.

Lemma tb_wrap z m : 0 <= m < 64 -> Z.testbit (bv_wrap 64 z) m = Z.testbit z m.
Proof. intros Hm. unfold bv_wrap. rewrite bv_modulus_64, two64_eq. apply Z.mod_pow2_bits_low. lia. Qed.

Lemma ext_Z_lo sx lo n z : ext_Z sx lo n z = ext_Z sx 0 n (z / 2 ^ (8 * lo)).
Proof. unfold ext_Z. rewrite Z.mul_0_r, Z.pow_0_r, Z.div_1_r. reflexivity. Qed.

Lemma ext_Z_false_lt' lo n z : 0 < n -> 0 <= ext_Z false lo n z < 2 ^ (8 * n).
Proof. intros Hn. unfold ext_Z. apply Z.mod_pos_bound. apply Z.pow_pos_nonneg; lia. Qed.

Lemma tb_VExt E sx lo n y m :
  0 <= to_Z lo -> 1 <= to_Z n -> to_Z lo + to_Z n <= 8 -> 0 <= m < 8 * to_Z n ->
  tb E (VExt sx lo n y) m = tb E y (m + 8 * to_Z lo).
Proof.
  intros Hlo Hn Hle Hm. unfold tb. cbn [den]. unfold ext_word. rewrite Z_to_bv_unsigned.
  rewrite ext_Z_lo. rewrite ext_core_tb; try lia.
  - apply Z.div_pow2_bits; lia.
  - apply Z.div_pos; [| apply Z.pow_pos_nonneg; lia]. pose proof (bv_unsigned_in_range _ (den E y)). lia.
Qed.

Lemma tb_VExt_hi E lo n y m :
  1 <= to_Z n -> 8 * to_Z n <= m -> tb E (VExt false lo n y) m = false.
Proof.
  intros Hn Hm. unfold tb. cbn [den]. unfold ext_word. rewrite Z_to_bv_unsigned.
  pose proof (ext_Z_false_lt' (to_Z lo) (to_Z n) (bv_unsigned (den E y)) ltac:(lia)) as R.
  destruct (Z_lt_le_dec m 64).
  - rewrite tb_wrap by lia. apply (testbit_high _ (8 * to_Z n)); lia.
  - unfold bv_wrap. rewrite bv_modulus_64, two64_eq. apply (testbit_high _ 64); [|lia].
    apply Z.mod_pos_bound. lia.
Qed.

Lemma byte_shift_ok c k : byte_shift c = Some k -> to_Z (shamt6 c) = 8 * Z.of_nat k /\ (k <= 7)%nat.
Proof.
  unfold byte_shift. intros H.
  destruct (PrimInt63.eqb (PrimInt63.land (shamt6 c) 7) 0) eqn:Hb; [|discriminate].
  injection H as <-. apply eqb_correct in Hb.
  assert (H7 : to_Z (PrimInt63.land (shamt6 c) 7) = 0) by (rewrite Hb; reflexivity).
  rewrite land_spec' in H7. change (to_Z 7) with (Z.ones 3) in H7. rewrite Z.land_ones in H7 by lia.
  rewrite lsr_spec. change (2 ^ to_Z 3) with 8.
  pose proof (shamt6_range c) as R.
  split; [|apply Nat2Z.inj_le; rewrite Z2Nat.id by lia; change (Z.of_nat 7) with 7; lia].
  rewrite Z2Nat.id by (apply Z.div_pos; lia). lia.
Qed.

Lemma tb_sll E a c k m : byte_shift c = Some k -> 0 <= m < 64 ->
  tb E (VAlu ALU_SLL a (VL c)) m = if m <? 8 * Z.of_nat k then false else tb E a (m - 8 * Z.of_nat k).
Proof.
  intros Hk Hm. apply byte_shift_ok in Hk as [Hs Hk7]. unfold tb. cbn [den alu64 alu].
  rewrite bv_shiftl_unsigned, shamt6_bv, Hs, tb_wrap by lia.
  destruct (Z.ltb_spec m (8 * Z.of_nat k)).
  - apply Z.shiftl_spec_low. lia.
  - apply Z.shiftl_spec_high; lia.
Qed.

Lemma tb_srl E a c k m : byte_shift c = Some k -> 0 <= m ->
  tb E (VAlu ALU_SRL a (VL c)) m = tb E a (m + 8 * Z.of_nat k).
Proof.
  intros Hk Hm. apply byte_shift_ok in Hk as [Hs Hk7]. unfold tb. cbn [den alu64 alu].
  rewrite bv_shiftr_unsigned, shamt6_bv, Hs. apply Z.shiftr_spec. lia.
Qed.

Lemma tb_or E a b m : tb E (VAlu ALU_OR a b) m = tb E a m || tb E b m.
Proof. unfold tb. cbn [den alu64 alu]. rewrite bv_or_unsigned. apply Z.lor_spec. Qed.

Lemma tb_VL0 E w m : weqb w wzero = true -> tb E (VL w) m = false.
Proof. intros H. apply weqb_eq in H. subst. unfold tb. cbn [den]. rewrite wbv_unsigned, wzero_ok. apply Z.bits_0. Qed.

Lemma tb_VIns E lo n a v m :
  0 <= to_Z lo -> 1 <= to_Z n -> to_Z lo + to_Z n <= 8 -> 0 <= m < 64 ->
  tb E (VIns lo n a v) m =
    if (8 * to_Z lo <=? m) && (m <? 8 * (to_Z lo + to_Z n)) then tb E v (m - 8 * to_Z lo) else tb E a m.
Proof.
  intros Hlo Hn Hle Hm. unfold tb. cbn [den]. rewrite Z_to_bv_unsigned, tb_wrap by lia.
  unfold ins_Z. rewrite pow2_m1_ones.
  rewrite Z.lor_spec, !Z.land_spec, Z.lnot_spec by lia.
  destruct (Z.leb_spec (8 * to_Z lo) m).
  - rewrite !Z.shiftl_spec_high by lia. rewrite Z.land_spec, !Z.testbit_ones by lia.
    destruct (Z.ltb_spec m (8 * (to_Z lo + to_Z n))).
    + replace (0 <=? m - 8 * to_Z lo) with true by (symmetry; apply Z.leb_le; lia).
      replace (m - 8 * to_Z lo <? 8 * to_Z n) with true by (symmetry; apply Z.ltb_lt; lia).
      cbn [andb negb]. rewrite andb_false_r, andb_true_r. reflexivity.
    + replace (m - 8 * to_Z lo <? 8 * to_Z n) with false by (symmetry; apply Z.ltb_ge; lia).
      rewrite !andb_false_r, andb_true_r, orb_false_r. cbn [andb]. reflexivity.
  - rewrite !Z.shiftl_spec_low by lia. cbn [negb andb]. rewrite andb_true_r, orb_false_r. reflexivity.
Qed.

Definition bs_ok (E : env) (oy : option sv) (v : sv) (i : nat) (b : bsrc) : Prop :=
  forall r, 0 <= r < 8 ->
  match b with
  | BZ => tb E v (8 * Z.of_nat i + r) = false
  | BU => True
  | BY j => match oy with
            | Some y => tb E v (8 * Z.of_nat i + r) = tb E y (8 * Z.of_nat j + r)
            | None => False
            end
  end.
Definition desc_ok (E : env) (d : bdesc_t) (v : sv) : Prop :=
  length (snd d) = 8%nat /\ forall i, (i < 8)%nat -> bs_ok E (fst d) v i (nth i (snd d) BU).

Lemma bs_ok_BU E oy v i : bs_ok E oy v i BU. Proof. intros r Hr. exact I. Qed.
Lemma bs_ok_shift E oy v y i j b :
  (forall r, 0 <= r < 8 -> tb E v (8 * Z.of_nat i + r) = tb E y (8 * Z.of_nat j + r)) ->
  bs_ok E oy y j b -> bs_ok E oy v i b.
Proof.
  intros Hs Hb r Hr. specialize (Hs r Hr). specialize (Hb r Hr). destruct b; [rewrite Hs; exact Hb|exact I|].
  destruct oy; [rewrite Hs; exact Hb|exact Hb].
Qed.
Lemma bs_ok_zero E oy v i : (forall r, 0 <= r < 8 -> tb E v (8 * Z.of_nat i + r) = false) -> bs_ok E oy v i BZ.
Proof. intros H r Hr. apply H. exact Hr. Qed.
Lemma length_brange lo n : length (brange lo n) = n. Proof. unfold brange. rewrite length_map, length_seq. reflexivity. Qed.
Lemma nth_brange lo n i d : (i < n)%nat -> nth i (brange lo n) d = BY (lo + i).
Proof. intros Hi. unfold brange. rewrite (nth_indep _ d (BY 0%nat)) by (rewrite length_map, length_seq; lia). rewrite map_nth, seq_nth by lia. reflexivity. Qed.
Lemma desc_self E y : desc_ok E (Some y, brange 0 8) y.
Proof. split; [reflexivity|]. intros i Hi. cbn [fst snd]. rewrite nth_brange by lia. intros r Hr. reflexivity. Qed.
Lemma desc_bunk E a : desc_ok E bunk a.
Proof. split; [reflexivity|]. intros i Hi. cbn [fst snd bunk]. do 8 (destruct i as [|i]; [apply bs_ok_BU|]). lia. Qed.

Lemma bmerge_l E ya yb oy v i b : bmerge_y ya yb = Some oy -> bs_ok E ya v i b -> bs_ok E oy v i b.
Proof.
  intros Hm Hb r Hr. specialize (Hb r Hr). destruct b; try exact Hb.
  destruct ya as [y|]; [|destruct Hb]. cbn in Hm. destruct yb as [y'|].
  - destruct (sv_eqb y y'); [|discriminate]. injection Hm as <-. exact Hb.
  - injection Hm as <-. exact Hb.
Qed.
Lemma bmerge_r E ya yb oy v i b : bmerge_y ya yb = Some oy -> bs_ok E yb v i b -> bs_ok E oy v i b.
Proof.
  intros Hm Hb r Hr. specialize (Hb r Hr). destruct b; try exact Hb.
  destruct yb as [y'|]; [|destruct Hb]. destruct ya as [y|]; cbn in Hm.
  - destruct (sv_eqb y y') eqn:Hq; [|discriminate]. injection Hm as <-. apply sv_eqb_eq in Hq. subst y'. exact Hb.
  - injection Hm as <-. exact Hb.
Qed.

Lemma bzip_spec xs ys zs : bzip xs ys = Some zs ->
  length xs = length zs /\ length ys = length zs /\
  forall i, (i < length zs)%nat -> bor (nth i xs BU) (nth i ys BU) = Some (nth i zs BU).
Proof.
  revert ys zs. induction xs as [|x xs IH]; intros ys zs H.
  - destruct ys; cbn in H; [|discriminate]. injection H as <-. cbn. split; [reflexivity|split; [reflexivity|intros; lia]].
  - destruct ys as [|y ys]; cbn in H; [discriminate|].
    destruct (bor x y) as [z|] eqn:Hz; [|discriminate]. destruct (bzip xs ys) as [zs'|] eqn:Hzs; [|discriminate].
    injection H as <-. destruct (IH ys zs' Hzs) as (L1 & L2 & Hn). cbn [length]. split; [lia|split; [lia|]].
    intros [|i] Hi; cbn [nth]; [exact Hz|]. apply Hn. cbn in Hi. lia.
Qed.

Lemma desc_VExt (E : env) (sx : bool) (lo n : int) (y : sv) (dy : bdesc_t) :
  let lo' := Z.to_nat (to_Z lo) in let n' := Z.to_nat (to_Z n) in
  (1 <= n')%nat -> (lo' + n' <= 8)%nat -> desc_ok E dy y ->
  desc_ok E (fst dy, firstn n' (skipn lo' (snd dy)) ++ repeat (if sx then BU else BZ) (8 - n')) (VExt sx lo n y).
Proof.
  intros lo' n' H1 H2 [L D]. unfold desc_ok. cbn [fst snd].
  pose proof (to_Z_bounded lo) as Blo. pose proof (to_Z_bounded n) as Bn.
  assert (Hlo : Z.of_nat lo' = to_Z lo) by (subst lo'; apply Z2Nat.id; lia).
  assert (Hn : Z.of_nat n' = to_Z n) by (subst n'; apply Z2Nat.id; lia).
  assert (Lf : length (firstn n' (skipn lo' (snd dy))) = n') by (rewrite length_firstn, length_skipn, L; lia).
  split; [rewrite length_app, Lf, repeat_length; lia|].
  intros i Hi. destruct (Nat.lt_ge_cases i n') as [Hin|Hin].
  - rewrite app_nth1 by lia. rewrite nth_firstn. replace (i <? n')%nat with true by (symmetry; apply Nat.ltb_lt; lia).
    rewrite nth_skipn. eapply bs_ok_shift; [|apply D; lia].
    intros r Hr. rewrite tb_VExt by lia. f_equal. lia.
  - rewrite app_nth2 by lia. rewrite Lf. destruct sx.
    + rewrite nth_repeat_lt by lia. apply bs_ok_BU.
    + rewrite nth_repeat_lt by lia. apply bs_ok_zero. intros r Hr. apply tb_VExt_hi; lia.
Qed.

Lemma desc_sll (E : env) (a : sv) (c : w64) (k : nat) (d : bdesc_t) : byte_shift c = Some k -> desc_ok E d a ->
  desc_ok E (fst d, repeat BZ k ++ firstn (8 - k) (snd d)) (VAlu ALU_SLL a (VL c)).
Proof.
  intros Hk [L D]. pose proof (byte_shift_ok _ _ Hk) as [Hs Hk7]. unfold desc_ok. cbn [fst snd].
  split; [rewrite length_app, repeat_length, length_firstn, L; lia|].
  intros i Hi. destruct (Nat.lt_ge_cases i k) as [Hik|Hik].
  - rewrite app_nth1 by (rewrite repeat_length; lia). rewrite nth_repeat_lt by lia.
    apply bs_ok_zero. intros r Hr. rewrite (tb_sll _ _ _ _ _ Hk) by lia.
    replace (8 * Z.of_nat i + r <? 8 * Z.of_nat k) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
  - rewrite app_nth2 by (rewrite repeat_length; lia). rewrite repeat_length, nth_firstn.
    replace (i - k <? 8 - k)%nat with true by (symmetry; apply Nat.ltb_lt; lia).
    eapply bs_ok_shift; [|apply D; lia]. intros r Hr. rewrite (tb_sll _ _ _ _ _ Hk) by lia.
    replace (8 * Z.of_nat i + r <? 8 * Z.of_nat k) with false by (symmetry; apply Z.ltb_ge; lia). f_equal. lia.
Qed.

Lemma desc_srl (E : env) (a : sv) (c : w64) (k : nat) (d : bdesc_t) : byte_shift c = Some k -> desc_ok E d a ->
  desc_ok E (fst d, skipn k (snd d) ++ repeat BZ k) (VAlu ALU_SRL a (VL c)).
Proof.
  intros Hk [L D]. pose proof (byte_shift_ok _ _ Hk) as [Hs Hk7]. unfold desc_ok. cbn [fst snd].
  split; [rewrite length_app, repeat_length, length_skipn, L; lia|].
  intros i Hi. destruct (Nat.lt_ge_cases i (8 - k)) as [Hik|Hik].
  - rewrite app_nth1 by (rewrite length_skipn; lia). rewrite nth_skipn.
    eapply bs_ok_shift; [|apply D; lia]. intros r Hr. rewrite (tb_srl _ _ _ _ _ Hk) by lia. f_equal. lia.
  - rewrite app_nth2 by (rewrite length_skipn; lia). rewrite length_skipn, L, nth_repeat_lt by lia.
    apply bs_ok_zero. intros r Hr. rewrite (tb_srl _ _ _ _ _ Hk) by lia. apply tb_high. lia.
Qed.

Lemma desc_or (E : env) (a b : sv) (da db : bdesc_t) (oy : option sv) (ds : list bsrc) : desc_ok E da a -> desc_ok E db b ->
  bmerge_y (fst da) (fst db) = Some oy -> bzip (snd da) (snd db) = Some ds ->
  desc_ok E (oy, ds) (VAlu ALU_OR a b).
Proof.
  intros [La Da] [Lb Db] Hm Hz. apply bzip_spec in Hz as (L1 & L2 & Hn). unfold desc_ok. cbn [fst snd].
  split; [lia|]. intros i Hi. specialize (Hn i ltac:(lia)). specialize (Da i Hi). specialize (Db i Hi).
  destruct (nth i (snd da) BU) eqn:Ea; destruct (nth i (snd db) BU) eqn:Eb; cbn [bor] in Hn; try discriminate; injection Hn as <-.
  - apply bs_ok_zero. intros r Hr. rewrite tb_or, (Da r Hr), (Db r Hr). reflexivity.
  - apply bs_ok_BU.
  - eapply bmerge_r; [exact Hm|]. eapply bs_ok_shift; [|exact Db]. intros r Hr. rewrite tb_or, (Da r Hr). reflexivity.
  - apply bs_ok_BU.
  - eapply bmerge_l; [exact Hm|]. eapply bs_ok_shift; [|exact Da]. intros r Hr. rewrite tb_or, (Db r Hr). apply orb_false_r.
Qed.

Lemma desc_ins (E : env) (lo n : int) (a v : sv) (da dv : bdesc_t) (oy : option sv) :
  let lo' := Z.to_nat (to_Z lo) in let n' := Z.to_nat (to_Z n) in
  (1 <= n')%nat -> (lo' + n' <= 8)%nat -> desc_ok E da a -> desc_ok E dv v ->
  bmerge_y (fst da) (fst dv) = Some oy ->
  desc_ok E (oy, firstn lo' (snd da) ++ firstn n' (snd dv) ++ skipn (lo' + n') (snd da)) (VIns lo n a v).
Proof.
  intros lo' n' H1 H2 [La Da] [Lv Dv] Hm. unfold desc_ok. cbn [fst snd].
  pose proof (to_Z_bounded lo) as Blo. pose proof (to_Z_bounded n) as Bn.
  assert (Hlo : Z.of_nat lo' = to_Z lo) by (subst lo'; apply Z2Nat.id; lia).
  assert (Hn : Z.of_nat n' = to_Z n) by (subst n'; apply Z2Nat.id; lia).
  assert (L1 : length (firstn lo' (snd da)) = lo') by (rewrite length_firstn, La; lia).
  assert (L2 : length (firstn n' (snd dv)) = n') by (rewrite length_firstn, Lv; lia).
  split; [rewrite !length_app, L1, L2, length_skipn, La; lia|].
  intros i Hi. destruct (Nat.lt_ge_cases i lo') as [Hil|Hil].
  - rewrite app_nth1 by lia. rewrite nth_firstn. replace (i <? lo')%nat with true by (symmetry; apply Nat.ltb_lt; lia).
    eapply bmerge_l; [exact Hm|]. eapply bs_ok_shift; [|apply Da; lia]. intros r Hr.
    rewrite tb_VIns by lia. replace (8 * to_Z lo <=? 8 * Z.of_nat i + r) with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
  - rewrite app_nth2 by lia. rewrite L1. destruct (Nat.lt_ge_cases (i - lo') n') as [Hin|Hin].
    + rewrite app_nth1 by lia. rewrite nth_firstn. replace (i - lo' <? n')%nat with true by (symmetry; apply Nat.ltb_lt; lia).
      eapply bmerge_r; [exact Hm|]. eapply bs_ok_shift; [|apply Dv; lia]. intros r Hr.
      rewrite tb_VIns by lia. replace (8 * to_Z lo <=? 8 * Z.of_nat i + r) with true by (symmetry; apply Z.leb_le; lia).
      replace (8 * Z.of_nat i + r <? 8 * (to_Z lo + to_Z n)) with true by (symmetry; apply Z.ltb_lt; lia). cbn [andb]. f_equal. lia.
    + rewrite app_nth2 by lia. rewrite L2, nth_skipn.
      eapply bmerge_l; [exact Hm|]. replace (lo' + n' + (i - lo' - n'))%nat with i by lia.
      eapply bs_ok_shift; [|apply Da; lia]. intros r Hr.
      rewrite tb_VIns by lia. replace (8 * Z.of_nat i + r <? 8 * (to_Z lo + to_Z n)) with false by (symmetry; apply Z.ltb_ge; lia).
      rewrite andb_false_r. reflexivity.
Qed.

Lemma bdesc_ok E : forall v d, bdesc v = Some d -> desc_ok E d v.
Proof.
  induction v; intros d H; cbn [bdesc] in H; try discriminate.
  - destruct (weqb w wzero) eqn:Hw; [|discriminate]. injection H as <-.
    split; [reflexivity|]. intros i Hi. cbn [fst snd].
    assert (Z0 : bs_ok E None (VL w) i BZ) by (apply bs_ok_zero; intros r Hr; apply tb_VL0; exact Hw).
    do 8 (destruct i as [|i]; [exact Z0|]). lia.
  - destruct op; try discriminate.
    + destruct v2; try discriminate. destruct (byte_shift w) as [k|] eqn:Hk; [|discriminate].
      destruct (bdesc v1) as [[oy ds]|] eqn:Hd; [|discriminate]. injection H as <-.
      apply (desc_sll E v1 w k (oy, ds) Hk). apply IHv1. reflexivity.
    + destruct v2; try discriminate. destruct (byte_shift w) as [k|] eqn:Hk; [|discriminate].
      destruct (bdesc v1) as [[oy ds]|] eqn:Hd; [|discriminate]. injection H as <-.
      apply (desc_srl E v1 w k (oy, ds) Hk). apply IHv1. reflexivity.
    + destruct (bdesc v1) as [[ya da]|] eqn:Ha; [|discriminate]. destruct (bdesc v2) as [[yb db]|] eqn:Hb; [|discriminate].
      destruct (bmerge_y ya yb) as [oy|] eqn:Hm; [|discriminate]. destruct (bzip da db) as [ds|] eqn:Hz; [|discriminate].
      injection H as <-. apply (desc_or E v1 v2 (ya, da) (yb, db)); [apply IHv1| apply IHv2| exact Hm| exact Hz]; reflexivity.
  - destruct ((1 <=? Z.to_nat (to_Z n))%nat && (Z.to_nat (to_Z lo) + Z.to_nat (to_Z n) <=? 8)%nat) eqn:Hg; [|discriminate].
    apply andb_prop in Hg as [G1 G2]. apply Nat.leb_le in G1. apply Nat.leb_le in G2.
    injection H as <-. apply desc_VExt; [exact G1| exact G2|].
    destruct (bdesc v) as [d0|] eqn:Hd; [apply IHv; reflexivity| apply desc_self].
  - destruct ((1 <=? Z.to_nat (to_Z n))%nat && (Z.to_nat (to_Z lo) + Z.to_nat (to_Z n) <=? 8)%nat) eqn:Hg; [|discriminate].
    apply andb_prop in Hg as [G1 G2]. apply Nat.leb_le in G1. apply Nat.leb_le in G2.
    destruct (bdesc v2) as [[yv dv]|] eqn:Hv; [|discriminate].
    destruct (bmerge_y _ yv) as [oy|] eqn:Hm; [|discriminate]. injection H as <-.
    apply (desc_ins E lo n v1 v2 _ (yv, dv)); [exact G1| exact G2| | apply IHv2; reflexivity| exact Hm].
    destruct (bdesc v1) as [d0|] eqn:Ha; [apply IHv1; reflexivity| apply desc_bunk].
Qed.

Lemma bsrc_eqb_eq a b : bsrc_eqb a b = true -> a = b.
Proof. destruct a, b; cbn; try discriminate; try reflexivity. intros H. apply Nat.eqb_eq in H. subst. reflexivity. Qed.
Lemma bsrcs_eqb_eq xs : forall ys, bsrcs_eqb xs ys = true -> xs = ys.
Proof.
  induction xs as [|x xs IH]; intros [|y ys] H; cbn in H; try discriminate; [reflexivity|].
  apply andb_prop in H as [H1 H2]. apply bsrc_eqb_eq in H1. apply IH in H2. subst. reflexivity.
Qed.

Lemma tb_ext E v y : (forall m, 0 <= m < 64 -> tb E v m = tb E y m) -> den E v = den E y.
Proof.
  intros H. apply bv_eq. apply Z.bits_inj'. intros m Hm.
  destruct (Z_lt_le_dec m 64).
  - apply H. lia.
  - unfold tb in H. rewrite !bv_unsigned_spec_high by (cbn; lia). reflexivity.
Qed.

Lemma byte_split m : 0 <= m -> m = 8 * Z.of_nat (Z.to_nat (m / 8)) + m mod 8 /\ 0 <= m mod 8 < 8.
Proof. intros Hm. rewrite Z2Nat.id by (apply Z.div_pos; lia). pose proof (Z.div_mod m 8 ltac:(lia)). pose proof (Z.mod_pos_bound m 8 ltac:(lia)). lia. Qed.

Lemma desc_full_eq E y v : desc_ok E (Some y, brange 0 8) v -> den E v = den E y.
Proof.
  intros [L D]. cbn [fst snd] in D. apply tb_ext. intros m Hm.
  destruct (byte_split m ltac:(lia)) as [Em Hr].
  assert (Hi : (Z.to_nat (m / 8) < 8)%nat) by (apply Nat2Z.inj_lt; rewrite Z2Nat.id by (apply Z.div_pos; lia); change (Z.of_nat 8) with 8; apply Z.div_lt_upper_bound; lia).
  specialize (D _ Hi). rewrite nth_brange in D by lia. specialize (D (m mod 8) Hr). cbn [plus] in D.
  rewrite Em at 1 2. exact D.
Qed.

Lemma nat2int_ok k : (k <= 8)%nat -> to_Z (nat2int k) = Z.of_nat k.
Proof. intros Hk. do 9 (destruct k as [|k]; [reflexivity|]). lia. Qed.

Lemma desc_slice_eq E y v lo m : (1 <= m)%nat -> (lo + m <= 8)%nat ->
  desc_ok E (Some y, brange lo m ++ repeat BZ (8 - m)) v ->
  den E (VExt false (nat2int lo) (nat2int m) y) = den E v.
Proof.
  intros H1 H2 [L D]. cbn [fst snd] in D. apply tb_ext. intros m' Hm.
  pose proof (nat2int_ok lo ltac:(lia)) as Elo. pose proof (nat2int_ok m ltac:(lia)) as Em.
  destruct (byte_split m' ltac:(lia)) as [E' Hr].
  set (i := Z.to_nat (m' / 8)) in *.
  assert (Hi : (i < 8)%nat) by (apply Nat2Z.inj_lt; subst i; rewrite Z2Nat.id by (apply Z.div_pos; lia); change (Z.of_nat 8) with 8; apply Z.div_lt_upper_bound; lia).
  specialize (D _ Hi). rewrite E'.
  destruct (Nat.lt_ge_cases i m) as [Him|Him].
  - rewrite app_nth1 in D by (rewrite length_brange; lia). rewrite nth_brange in D by lia.
    specialize (D (m' mod 8) Hr). rewrite D. rewrite tb_VExt by (rewrite ?Elo, ?Em; lia). f_equal. rewrite Elo. lia.
  - rewrite app_nth2 in D by (rewrite length_brange; lia). rewrite length_brange, nth_repeat_lt in D by lia.
    specialize (D (m' mod 8) Hr). rewrite D. apply tb_VExt_hi; rewrite Em; lia.
Qed.

Lemma bfold_fit E y0 v lo m ds :
  (1 <= m)%nat ->
  ((lo + m <=? 8)%nat && bsrcs_eqb ds (brange lo m ++ repeat BZ (8 - m))) = true ->
  desc_ok E (Some y0, ds) v ->
  den E (VExt false (nat2int lo) (nat2int m) y0) = den E v.
Proof.
  intros Hm Hc Hd. apply andb_prop in Hc as [Hle Heq]. apply Nat.leb_le in Hle. apply bsrcs_eqb_eq in Heq. subst ds.
  apply desc_slice_eq; [exact Hm| exact Hle| exact Hd].
Qed.

Lemma bfold_ok E d v y : desc_ok E d v -> bfold d = Some y -> den E y = den E v.
Proof.
  intros Hd Hf. destruct d as [[y0|] ds]; cbn [bfold] in Hf; [|discriminate].
  destruct (bsrcs_eqb ds (brange 0 8)) eqn:Hfull.
  - injection Hf as <-. apply bsrcs_eqb_eq in Hfull. subst ds. symmetry. apply desc_full_eq. exact Hd.
  - destruct ds as [|[| |lo] ds']; try discriminate. cbv zeta in Hf.
    destruct ((lo + 4 <=? 8)%nat && bsrcs_eqb (BY lo :: ds') (brange lo 4 ++ repeat BZ (8 - 4))) eqn:H4.
    { injection Hf as <-. apply (bfold_fit E y0 v lo 4 _ ltac:(lia) H4 Hd). }
    destruct ((lo + 2 <=? 8)%nat && bsrcs_eqb (BY lo :: ds') (brange lo 2 ++ repeat BZ (8 - 2))) eqn:H2.
    { injection Hf as <-. apply (bfold_fit E y0 v lo 2 _ ltac:(lia) H2 Hd). }
    destruct ((lo + 1 <=? 8)%nat && bsrcs_eqb (BY lo :: ds') (brange lo 1 ++ repeat BZ (8 - 1))) eqn:H1; [|discriminate].
    injection Hf as <-. apply (bfold_fit E y0 v lo 1 _ ltac:(lia) H1 Hd).
Qed.

Lemma den_refold E r : den E (refold r) = den E r.
Proof.
  unfold refold. destruct (bdesc r) as [d|] eqn:Hd; [|reflexivity].
  destruct (bfold d) as [y|] eqn:Hf; [|reflexivity].
  apply (bfold_ok E d r y); [apply bdesc_ok; exact Hd| exact Hf].
Qed.
End BDP.

Lemma ext_word_compose sx sx' lo n lo2 n2 (w : word) :
  0 <= lo -> 0 < n -> lo + n <= n2 -> lo + n <= 8 -> 0 <= lo2 ->
  ext_word sx lo n (ext_word sx' lo2 n2 w) = ext_word sx (lo2 + lo) n w.
Proof.
  intros Hlo Hn Hle H8 Hlo2. unfold ext_word. f_equal. rewrite Z_to_bv_unsigned.
  rewrite (BDP.ext_Z_lo sx' lo2 n2), (BDP.ext_Z_lo sx (lo2 + lo) n).
  pose proof (bv_unsigned_in_range _ w) as Rw.
  apply ext_narrow; try lia.
  all: try (apply Z.div_pos; [lia| apply Z.pow_pos_nonneg; lia]).
  intros m Hm. rewrite !Z.div_pow2_bits by lia. f_equal. lia.
Qed.

Lemma ins_Z_testbit lo n a v p : 0 <= lo -> 0 < n -> 0 <= a -> 0 <= v -> 0 <= p ->
  Z.testbit (ins_Z lo n a v) p =
  if (8 * lo <=? p) && (p <? 8 * lo + 8 * n) then Z.testbit v (p - 8 * lo) else Z.testbit a p.
Proof.
  intros Hlo Hn Ha Hv Hp. unfold ins_Z. rewrite pow2_m1_ones.
  W64Proofs.w64_tb.
  destruct (Z.leb_spec (8 * lo) p); destruct (Z.ltb_spec p (8 * lo + 8 * n)); cbn [andb].
  1: rewrite Z.ones_spec_low by lia; cbn [negb]; rewrite andb_false_r, andb_true_r; reflexivity.
  1: rewrite Z.ones_spec_high by lia; cbn [negb]; rewrite andb_false_r, andb_true_r, orb_false_r; reflexivity.
  all: cbn [negb]; rewrite andb_true_r, orb_false_r; reflexivity.
Qed.

Lemma ext_Z_bits_shift sx lo lo' n z z' : 0 <= lo -> 0 <= lo' -> 0 < n -> 0 <= z -> 0 <= z' ->
  (forall m, 0 <= m < 8 * n -> Z.testbit z (m + 8 * lo) = Z.testbit z' (m + 8 * lo')) ->
  ext_Z sx lo n z = ext_Z sx lo' n z'.
Proof.
  intros Hlo Hlo' Hn Hz Hz' Htb.
  rewrite (BDP.ext_Z_lo sx lo n z), (BDP.ext_Z_lo sx lo' n z'). unfold ext_Z.
  rewrite !Z.mul_0_r, !Z.pow_0_r, !Z.div_1_r.
  replace ((z / 2 ^ (8 * lo)) mod 2 ^ (8 * n)) with ((z' / 2 ^ (8 * lo')) mod 2 ^ (8 * n)); [reflexivity|].
  apply Z.bits_inj'; intros m Hm. W64Proofs.w64_tb.
  destruct (Z.ltb_spec m (8 * n)); [|reflexivity]. symmetry. apply Htb. lia.
Qed.

Lemma den_VIns_u E lo2 n2 a1 a2 : 0 <= to_Z lo2 -> 0 < to_Z n2 -> to_Z lo2 + to_Z n2 <= 8 ->
  bv_unsigned (den E (VIns lo2 n2 a1 a2)) = ins_Z (to_Z lo2) (to_Z n2) (bv_unsigned (den E a1)) (bv_unsigned (den E a2)).
Proof.
  intros H1 H2 H3. cbn [den]. rewrite Z_to_bv_unsigned.
  pose proof (bv_unsigned_in_range _ (den E a1)) as R1. rewrite bv_modulus_64 in R1.
  pose proof (bv_unsigned_in_range _ (den E a2)) as R2. rewrite bv_modulus_64 in R2.
  pose proof (ins_Z_range (to_Z lo2) (to_Z n2) (bv_unsigned (den E a1)) (bv_unsigned (den E a2)) H1 H2 H3 R1).
  unfold bv_wrap. rewrite bv_modulus_64. apply Z.mod_small. lia.
Qed.

Lemma ext_ins_inside E sx lo n lo2 n2 a1 a2 :
  0 <= lo -> 0 < n -> 0 <= to_Z lo2 -> 0 < to_Z n2 -> to_Z lo2 + to_Z n2 <= 8 ->
  to_Z lo2 <= lo -> lo + n <= to_Z lo2 + to_Z n2 ->
  ext_word sx lo n (den E (VIns lo2 n2 a1 a2)) = ext_word sx (lo - to_Z lo2) n (den E a2).
Proof.
  intros Hlo Hn H1 H2 H3 Hin1 Hin2. unfold ext_word. f_equal.
  rewrite den_VIns_u by lia.
  pose proof (bv_unsigned_in_range _ (den E a1)) as R1. rewrite bv_modulus_64 in R1.
  pose proof (bv_unsigned_in_range _ (den E a2)) as R2. rewrite bv_modulus_64 in R2.
  apply ext_Z_bits_shift; try lia.
  - pose proof (ins_Z_range (to_Z lo2) (to_Z n2) (bv_unsigned (den E a1)) (bv_unsigned (den E a2)) H1 H2 H3 R1). lia.
  - intros m Hm. rewrite ins_Z_testbit by lia.
    destruct (Z.leb_spec (8 * to_Z lo2) (m + 8 * lo)); [|exfalso; lia].
    destruct (Z.ltb_spec (m + 8 * lo) (8 * to_Z lo2 + 8 * to_Z n2)); [|exfalso; lia].
    cbn [andb]. f_equal. lia.
Qed.

Lemma ext_ins_outside E sx lo n lo2 n2 a1 a2 :
  0 <= lo -> 0 < n -> 0 <= to_Z lo2 -> 0 < to_Z n2 -> to_Z lo2 + to_Z n2 <= 8 ->
  (lo + n <= to_Z lo2 \/ to_Z lo2 + to_Z n2 <= lo) ->
  ext_word sx lo n (den E (VIns lo2 n2 a1 a2)) = ext_word sx lo n (den E a1).
Proof.
  intros Hlo Hn H1 H2 H3 Hout. unfold ext_word. f_equal.
  rewrite den_VIns_u by lia.
  pose proof (bv_unsigned_in_range _ (den E a1)) as R1. rewrite bv_modulus_64 in R1.
  pose proof (bv_unsigned_in_range _ (den E a2)) as R2. rewrite bv_modulus_64 in R2.
  apply ext_Z_bits_shift; try lia.
  - pose proof (ins_Z_range (to_Z lo2) (to_Z n2) (bv_unsigned (den E a1)) (bv_unsigned (den E a2)) H1 H2 H3 R1). lia.
  - intros m Hm. rewrite ins_Z_testbit by lia.
    destruct (Z.leb_spec (8 * to_Z lo2) (m + 8 * lo)); destruct (Z.ltb_spec (m + 8 * lo) (8 * to_Z lo2 + 8 * to_Z n2));
      cbn [andb]; try reflexivity. exfalso. lia.
Qed.

Lemma den_ext_default : forall E sx lo n a,
  width_ok (to_Z lo) (to_Z n) ->
  den E (if PrimInt63.eqb lo 0%uint63 && PrimInt63.eqb n 8%uint63 then a else VExt sx lo n a)
  = ext_word sx (to_Z lo) (to_Z n) (den E a).
Proof.
  intros E sx lo n a (Hlo & Hn & Hle).
  destruct (PrimInt63.eqb lo 0) eqn:H0; destruct (PrimInt63.eqb n 8) eqn:H8; cbn [andb]; try reflexivity.
  apply int_eqb_eq in H0. apply int_eqb_eq in H8. subst. symmetry. apply ext_word_id64.
Qed.

Lemma den_sv_ext : forall E sx lo n a,
  width_ok (to_Z lo) (to_Z n) ->
  den E (sv_ext sx lo n a) = ext_word sx (to_Z lo) (to_Z n) (den E a).
Proof.
  intros E sx lo n a. revert sx lo n.
  induction a as [w|k o|op a1 IHa1 a2 IHa2|op a1 IHa1 a2 IHa2|op a1 IHa1 a2 IHa2|op a1 IHa1 a2 IHa2
                 |sx' lo2 n2 y IHy|lo' n' a1 IHa1 a2 IHa2|sx' j off IHoff n0|sx' k off n0|op a1 IHa1];
    intros sx lo n W; pose proof W as (Hlo & Hn & Hle); cbn [sv_ext]; try (apply den_ext_default; exact W).
  -   cbn [den]. unfold ext_word. rewrite wbv_unsigned. unfold wbv. rewrite wext_ok by lia. reflexivity.
  -
    destruct (PrimInt63.leb lo2 8%uint63 && PrimInt63.leb (PrimInt63.add lo n) n2
              && PrimInt63.leb (PrimInt63.add lo2 (PrimInt63.add lo n)) 8%uint63) eqn:Hg;
      [| apply den_ext_default; exact W].
    apply andb_prop in Hg as [Hg H3]. apply andb_prop in Hg as [H1 H2].
    rewrite leb_spec in H1, H2, H3. change (to_Z 8%uint63) with 8 in H1, H3.
    pose proof (to_Z_bounded lo2) as B2. pose proof (to_Z_bounded n2) as Bn2.
    assert (Hln : to_Z (PrimInt63.add lo n) = to_Z lo + to_Z n).
    { rewrite add_spec. apply Z.mod_small. rewrite wB_two63. unfold two63. lia. }
    rewrite Hln in H2.
    assert (H3' : to_Z (PrimInt63.add lo2 (PrimInt63.add lo n)) = to_Z lo2 + (to_Z lo + to_Z n)).
    { rewrite add_spec, Hln. apply Z.mod_small. rewrite wB_two63. unfold two63. lia. }
    rewrite H3' in H3.
    assert (Hl2 : to_Z (PrimInt63.add lo2 lo) = to_Z lo2 + to_Z lo).
    { rewrite add_spec. apply Z.mod_small. rewrite wB_two63. unfold two63. lia. }
    rewrite IHy by (unfold width_ok; rewrite Hl2; lia).
    rewrite Hl2. cbn [den]. symmetry. apply ext_word_compose; lia.
  -
    rename lo' into lo2. rename n' into n2.
    pose proof (to_Z_bounded lo2) as B2. pose proof (to_Z_bounded n2) as Bn2.
    pose proof (to_Z_bounded lo) as Bl. pose proof (to_Z_bounded n) as Bn.
    destruct (PrimInt63.leb lo2 8%uint63 && PrimInt63.ltb 0%uint63 n2 && PrimInt63.leb n2 8%uint63
              && PrimInt63.leb (PrimInt63.add lo2 n2) 8%uint63) eqn:Hg;
      [| apply den_ext_default; exact W].
    apply andb_prop in Hg as [Hg G4]. apply andb_prop in Hg as [Hg G3]. apply andb_prop in Hg as [G1 G2].
    rewrite leb_spec in G1, G3, G4. rewrite ltb_spec in G2.
    change (to_Z 8%uint63) with 8 in G1, G3, G4. change (to_Z 0%uint63) with 0 in G2.
    assert (A2 : to_Z (PrimInt63.add lo2 n2) = to_Z lo2 + to_Z n2).
    { rewrite add_spec. apply Z.mod_small. rewrite wB_two63. unfold two63. lia. }
    rewrite A2 in G4.
    assert (Hln : to_Z (PrimInt63.add lo n) = to_Z lo + to_Z n).
    { rewrite add_spec. apply Z.mod_small. rewrite wB_two63. unfold two63. lia. }
    destruct (PrimInt63.leb lo2 lo && PrimInt63.leb (PrimInt63.add lo n) (PrimInt63.add lo2 n2)) eqn:Hin.
    + apply andb_prop in Hin as [I1 I2]. rewrite leb_spec in I1, I2. rewrite Hln, A2 in I2.
      assert (Hs : to_Z (PrimInt63.sub lo lo2) = to_Z lo - to_Z lo2).
      { rewrite sub_spec. apply Z.mod_small. rewrite wB_two63. unfold two63. lia. }
      rewrite IHa2 by (unfold width_ok; rewrite Hs; lia). rewrite Hs.
      symmetry. apply ext_ins_inside; lia.
    + destruct (PrimInt63.leb (PrimInt63.add lo n) lo2 || PrimInt63.leb (PrimInt63.add lo2 n2) lo) eqn:Hout;
        [| apply den_ext_default; exact W].
      rewrite IHa1 by exact W. symmetry. apply ext_ins_outside; try lia.
      apply orb_prop in Hout as [O|O]; rewrite leb_spec in O; [rewrite Hln in O; left; lia| rewrite A2 in O; right; lia].
  -   destruct off as [w| | | | | | | | | |]; try (apply den_ext_default; exact W).
    destruct (PrimInt63.leb (PrimInt63.add lo n) n0) eqn:Hb; cbn [andb]; [|reflexivity].
    destruct (wt w) eqn:Ht; cbn [negb]; [reflexivity|].
    rewrite leb_spec, add_spec, Z.mod_small in Hb by (rewrite wB_two63; unfold two63; lia).
    cbn [den]. unfold ext_word, bytes_val. f_equal. rewrite Z_to_bv_unsigned.
    rewrite !wbv_unsigned, wadd_ok, wlit_ok.
    assert (Hw : w2Z w < two63) by (pose proof (w2Z_wt w) as X; rewrite Ht in X; destruct (Z.leb_spec two63 (w2Z w)); [discriminate|lia]).
    pose proof (w2Z_range w). rewrite Z.mod_small by (unfold two63, two64 in *; lia).
    symmetry. apply ext_narrow; try lia; try apply bytes_le_to_Z_nonneg.
    intros m Hm. unfold blob_bytes. rewrite !bytes_le_to_Z_firstn_tb by lia.
    rewrite !Z2Nat.id by lia.
    destruct (Z.ltb_spec m (8 * to_Z n)); [|lia]. destruct (Z.ltb_spec (m + 8 * to_Z lo) (8 * to_Z n0)); [|lia]. cbn [andb].
    rewrite Z2Nat.inj_add, Nat.add_comm, <- skipn_skipn, bytes_le_to_Z_skipn_tb, Z2Nat.id by lia. reflexivity.
  -
    destruct (PrimInt63.leb (PrimInt63.add lo n) n0) eqn:Hb; cbn [andb]; [|reflexivity].
    destruct (wt off || negb (wt (wadd off (wlit lo)))) eqn:Hg; [|reflexivity].
    rewrite leb_spec, add_spec, Z.mod_small in Hb by (rewrite wB_two63; unfold two63; lia).
    cbn [den]. unfold ext_word, bytes_val. f_equal. rewrite Z_to_bv_unsigned.
    rewrite w2Zs_wadd_small by (lia || exact Hg).
    symmetry. apply ext_narrow; try lia; try apply bytes_le_to_Z_nonneg.
    intros m Hm.
    replace (bg_bytes (eg E k) (w2Zs off + to_Z lo) (Z.to_nat (to_Z n)))
      with (firstn (Z.to_nat (to_Z n)) (skipn (Z.to_nat (to_Z lo)) (bg_bytes (eg E k) (w2Zs off) (Z.to_nat (to_Z n0)))))
      by (rewrite bg_bytes_shift by lia; f_equal; lia).
    rewrite bytes_le_to_Z_firstn_tb, bytes_le_to_Z_skipn_tb, !Z2Nat.id by lia.
    destruct (Z.ltb_spec m (8 * to_Z n)); [reflexivity|lia].
Qed.

Lemma ins_Z_full : forall a v, 0 <= a < two64 -> 0 <= v < two64 -> ins_Z 0 8 a v = v.
Proof.
  intros a v Ha Hv. unfold ins_Z. change (8 * 8) with 64. change (8 * 0) with 0.
  rewrite !Z.shiftl_0_r, pow2_m1_ones, two64_eq in *.
  apply Z.bits_inj'; intros m Hm. vp_tb.
  destruct (Z.ltb_spec m 64); cbn [negb andb orb].
  - rewrite andb_false_r, andb_true_r. reflexivity.
  - rewrite (testbit_high a 64), (testbit_high v 64) by lia. reflexivity.
Qed.

Lemma den_sv_ins : forall E lo n a v,
  width_ok (to_Z lo) (to_Z n) ->
  den E (sv_ins lo n a v) = Z_to_bv 64 (ins_Z (to_Z lo) (to_Z n) (bv_unsigned (den E a)) (bv_unsigned (den E v))).
Proof.
  intros E lo n a v (Hlo & Hn & Hle). unfold sv_ins.
  destruct (PrimInt63.eqb lo 0) eqn:H0; [destruct (PrimInt63.eqb n 8) eqn:H8|]; cbn [andb].
  - apply int_eqb_eq in H0. apply int_eqb_eq in H8. subst. change (to_Z 0) with 0. change (to_Z 8) with 8.
    rewrite ins_Z_full by (rewrite <- bv_modulus_64; apply bv_unsigned_in_range). symmetry. apply Z_to_bv_bv_unsigned.
  - destruct a; destruct v; rewrite ?BDP.den_refold; try reflexivity. cbn [den]. rewrite !wbv_unsigned. unfold wbv. rewrite wins_w2Z by lia. reflexivity.
  - destruct a; destruct v; rewrite ?BDP.den_refold; try reflexivity. cbn [den]. rewrite !wbv_unsigned. unfold wbv. rewrite wins_w2Z by lia. reflexivity.
Qed.

Lemma fact_lookup_In : forall fs p, fact_lookup fs p = true -> exists f, In f fs /\ p f = true.
Proof.
  induction fs as [|f fs IH]; cbn [fact_lookup]; intros p H; [discriminate|].
  destruct (p f) eqn:Hp.
  - exists f. split; [left; reflexivity|exact Hp].
  - cbn [orb] in H. destruct (IH p H) as (g & Hg & Hpg). exists g. split; [right; exact Hg|exact Hpg].
Qed.

Lemma fact_lookup_holds : forall E fs p, facts_hold E fs -> fact_lookup fs p = true ->
  exists f, fact_holds E f /\ p f = true.
Proof.
  intros E fs p Hfs H. destruct (fact_lookup_In fs p H) as (f & Hin & Hp).
  exists f. split; [|exact Hp]. unfold facts_hold in Hfs. rewrite Forall_forall in Hfs. apply Hfs, Hin.
Qed.

Lemma ltu_iff (a b : word) r : bv_ltu a b = r <-> (if r then bv_unsigned a < bv_unsigned b else bv_unsigned b <= bv_unsigned a).
Proof. unfold bv_ltu. destruct r; [rewrite Z.ltb_lt|rewrite Z.ltb_ge]; tauto. Qed.
Lemma lts_iff (a b : word) r : bv_lts a b = r <-> (if r then bv_signed a < bv_signed b else bv_signed b <= bv_signed a).
Proof. unfold bv_lts. destruct r; [rewrite Z.ltb_lt|rewrite Z.ltb_ge]; tauto. Qed.
Lemma eqb_iff (a b : word) r : bv_eqb a b = r <-> (if r then a = b else a <> b).
Proof.
  unfold bv_eqb. destruct r; [rewrite Z.eqb_eq|rewrite Z.eqb_neq]; split; intros H.
  - apply bv_eq; exact H. - subst; reflexivity. - intros X; subst; apply H; reflexivity. - intros X; apply H, bv_eq; exact X.
Qed.

Lemma wleu_w2Z a b : wleu a b = Z.leb (w2Z a) (w2Z b).
Proof. unfold wleu. rewrite wltu_w2Z. destruct (Z.ltb_spec (w2Z b) (w2Z a)), (Z.leb_spec (w2Z a) (w2Z b)); cbn; lia || reflexivity. Qed.

Ltac vp_wcmp :=
  repeat match goal with
  | G : wltu _ _ = _ |- _ => rewrite wltu_w2Z in G
  | G : wleu _ _ = _ |- _ => rewrite wleu_w2Z in G
  | G : wlts _ _ = _ |- _ => rewrite wlts_w2Zs in G
  | G : weqb _ _ = _ |- _ => rewrite weqb_eqb in G
  | G : negb _ = true |- _ => apply negb_true_iff in G
  | G : negb _ = false |- _ => apply negb_false_iff in G
  | G : Z.ltb _ _ = true |- _ => apply Z.ltb_lt in G
  | G : Z.ltb _ _ = false |- _ => apply Z.ltb_ge in G
  | G : Z.leb _ _ = true |- _ => apply Z.leb_le in G
  | G : Z.leb _ _ = false |- _ => apply Z.leb_gt in G
  | G : Z.eqb _ _ = true |- _ => apply Z.eqb_eq in G
  | G : Z.eqb _ _ = false |- _ => apply Z.eqb_neq in G
  end.

Ltac vp_bsplit :=
  repeat match goal with
  | G : _ && _ = true |- _ => apply andb_prop in G; destruct G
  | G : _ || _ = false |- _ => apply orb_false_elim in G; destruct G
  | G : sv_eqb _ _ = true |- _ => apply sv_eqb_eq in G; subst
  | G : PrimInt63.eqb _ _ = true |- _ => apply int_eqb_eq in G; subst
  | G : false = true |- _ => discriminate G
  | G : true = false |- _ => discriminate G
  | G : Some _ = Some _ |- _ => injection G; clear G; intros G; try subst
  | G : Some _ = None |- _ => discriminate G
  | G : None = Some _ |- _ => discriminate G
  end.

Ltac vp_hpd Hp :=
  repeat match type of Hp with context [match ?v with _ => _ end] =>
    is_var v; destruct v; try discriminate Hp end.

Ltac vp_fact_cases Hfs H :=
  apply (fact_lookup_holds _ _ _ Hfs) in H;
  destruct H as ([? ? ?|? ?|? ?|? ?|? ?|? ?|? ?|? ?] & ?Hh & ?Hp); cbn [fact_holds] in Hh;
  cbn beta iota delta [is_FULt is_FULe is_FSLt is_FSLe is_FEq is_FNe] in Hp; try discriminate Hp;
  repeat match goal with
  | G : _ || _ = true |- _ => apply orb_prop in G; destruct G
  end; vp_bsplit.

Lemma find_range_sound_gen E fs : facts_hold E fs -> forall k lo hi, find_range fs k = Some (lo, hi) ->
  w2Z lo <= bv_unsigned (ev E k) <= w2Z hi.
Proof.
  induction fs as [|f fs' IH]; cbn [find_range]; intros Hfs k lo hi H; [discriminate|].
  inversion Hfs as [|f' l Hf Hfs']; subst.
  destruct f; try (apply IH; assumption).
  destruct (PrimInt63.eqb k k0) eqn:Hk; [|apply IH; assumption].
  apply int_eqb_eq in Hk. subst. injection H; intros; subst. exact Hf.
Qed.

Lemma find_align_sound_gen E fs : facts_hold E fs -> forall k, bv_unsigned (ev E k) mod 2 ^ (to_Z (find_align fs k)) = 0.
Proof.
  induction fs as [|f fs' IH]; cbn [find_align]; intros Hfs k.
  - change (to_Z 0) with 0. rewrite Z.pow_0_r. apply Z.mod_1_r.
  - inversion Hfs as [|f' l Hf Hfs']; subst. destruct f; try (apply IH; assumption).
    destruct (PrimInt63.eqb k k0) eqn:Hk; [|apply IH; assumption].
    apply int_eqb_eq in Hk. subst. exact Hf.
Qed.

Lemma rel_facts_hold : forall E vs fs, facts_hold E fs -> facts_hold E (rel_facts vs fs).
Proof.
  intros E vs fs H. unfold facts_hold, rel_facts in *. apply Forall_forall. intros f Hf.
  apply filter_In in Hf as [Hf _]. exact (proj1 (Forall_forall _ _) H f Hf).
Qed.

Section Deciders.
Variable E : env.
Variable fs : list fact.
Hypothesis Hfs : facts_hold E fs.
Hypothesis Hz : ev E 0%uint63 = Z_to_bv 64 0.

Lemma find_range_sound : forall k lo hi, find_range fs k = Some (lo, hi) ->
  w2Z lo <= bv_unsigned (ev E k) <= w2Z hi.
Proof. exact (find_range_sound_gen E fs Hfs). Qed.

Lemma find_align_sound : forall k, bv_unsigned (ev E k) mod 2 ^ (to_Z (find_align fs k)) = 0.
Proof. exact (find_align_sound_gen E fs Hfs). Qed.

Lemma add_carries_iff a b : add_carries a b = true <-> two64 <= w2Z a + w2Z b.
Proof.
  unfold add_carries. rewrite wltu_w2Z, wadd_ok, Z.ltb_lt.
  pose proof (w2Z_range a). pose proof (w2Z_range b).
  rewrite (mod_cases2 (w2Z a + w2Z b)) by (unfold two64 in *; lia).
  destruct (Z.ltb_spec (w2Z a + w2Z b) two64); lia.
Qed.

Lemma w2Zs_eq o : w2Zs o = w2Z o - (if wt o then two64 else 0).
Proof. unfold w2Zs. destruct (wt o); lia. Qed.

Lemma nowrap_sound : forall lo hi o, nowrap lo hi o = true ->
  0 <= w2Z lo + w2Zs o /\ w2Z hi + w2Zs o < two64.
Proof.
  intros lo hi o H. unfold nowrap in H. rewrite w2Zs_eq.
  pose proof (w2Z_range lo) as Rlo. pose proof (w2Z_range hi) as Rhi. pose proof (w2Z_range o) as Ro.
  destruct (wt o).
  - apply andb_prop in H as [H1 H2]. apply add_carries_iff in H1. apply add_carries_iff in H2. lia.
  - destruct (add_carries hi o) eqn:Hc; [discriminate|].
    assert (~ two64 <= w2Z hi + w2Z o) by (rewrite <- add_carries_iff, Hc; discriminate). lia.
Qed.

Lemma den_VP k o : bv_unsigned (den E (VP k o)) = (bv_unsigned (ev E k) + w2Zs o) mod two64.
Proof.
  cbn [den]. rewrite bv_add_unsigned, wbv_unsigned, w2Zs_eq. unfold bv_wrap. rewrite bv_modulus_64.
  destruct (wt o); [|f_equal; lia].
  replace (bv_unsigned (ev E k) + (w2Z o - two64)) with (bv_unsigned (ev E k) + w2Z o + (-1) * two64) by lia.
  rewrite Z.mod_add by (unfold two64; lia). reflexivity.
Qed.

Lemma den_VPu k o : bv_unsigned (den E (VP k o)) = (bv_unsigned (ev E k) + w2Z o) mod two64.
Proof. cbn [den]. rewrite bv_add_unsigned, wbv_unsigned. unfold bv_wrap. rewrite bv_modulus_64. reflexivity. Qed.

Lemma den_VL x : bv_unsigned (den E (VL x)) = w2Z x.
Proof. cbn [den]. apply wbv_unsigned. Qed.

Lemma evk_range k : 0 <= bv_unsigned (ev E k) < two64.
Proof. rewrite <- bv_modulus_64. apply bv_unsigned_in_range. Qed.

Lemma nowrap_k_sound : forall k o, nowrap_k fs k o = true ->
  0 <= bv_unsigned (ev E k) + w2Zs o < two64 /\
  bv_unsigned (den E (VP k o)) = bv_unsigned (ev E k) + w2Zs o.
Proof.
  intros k o H. unfold nowrap_k in H.
  destruct (find_range fs k) as [[lo hi]|] eqn:Hr; [|discriminate].
  apply find_range_sound in Hr. apply nowrap_sound in H.
  split; [lia|]. rewrite den_VP. apply Z.mod_small. lia.
Qed.

Lemma lookup_ltu_lit_r_sound : forall a y r, lookup_ltu_lit_r fs a y = Some r ->
  bv_ltu (den E a) (wbv y) = r.
Proof.
  intros a y r H. unfold lookup_ltu_lit_r in H. apply ltu_iff. rewrite wbv_unsigned.
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:H1 end.
  { vp_bsplit. vp_fact_cases Hfs H1.
    all: vp_hpd Hp; vp_bsplit; vp_wcmp; rewrite ?den_VL in Hh; lia. }
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:H2 end; vp_bsplit.
  vp_fact_cases Hfs H2.
  all: vp_hpd Hp; vp_bsplit; vp_wcmp;
       try match type of Hh with den _ (VL _) = _ => rewrite <- Hh | _ = den _ (VL _) => rewrite Hh end;
       rewrite ?den_VL in Hh; rewrite ?den_VL; lia.
Qed.

Lemma lookup_ltu_lit_l_sound : forall x b r, lookup_ltu_lit_l fs x b = Some r ->
  bv_ltu (wbv x) (den E b) = r.
Proof.
  intros x b r H. unfold lookup_ltu_lit_l in H. apply ltu_iff. rewrite wbv_unsigned.
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:H1 end.
  { vp_bsplit. vp_fact_cases Hfs H1.
    all: vp_hpd Hp; vp_bsplit; vp_wcmp; rewrite ?den_VL in Hh; lia. }
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:H2 end; vp_bsplit.
  vp_fact_cases Hfs H2.
  all: vp_hpd Hp; vp_bsplit; vp_wcmp;
       try match type of Hh with den _ (VL _) = _ => rewrite <- Hh | _ = den _ (VL _) => rewrite Hh end;
       rewrite ?den_VL in Hh; rewrite ?den_VL; lia.
Qed.

Lemma umax_of_width_sound n m : umax_of_width n = Some m -> 1 <= to_Z n < 8 /\ w2Z m = 2 ^ (8 * to_Z n) - 1.
Proof.
  unfold umax_of_width. intros H.
  destruct (PrimInt63.ltb n 8) eqn:H1; [|discriminate].
  destruct (PrimInt63.ltb 0 n) eqn:H2; [|discriminate]. cbn [andb] in H. injection H as <-.
  apply Uint63.ltb_spec in H1. apply Uint63.ltb_spec in H2.
  change (to_Z 8%uint63) with 8 in H1. change (to_Z 0%uint63) with 0 in H2.
  split; [lia|].
  unfold w2Z; cbn [wt wl].
  rewrite Uint63.sub_spec, Uint63.lsl_spec, Uint63.lsl_spec.
  change (to_Z 1%uint63) with 1. change (to_Z 3%uint63) with 3. change wB with (2^63).
  assert (Hn : to_Z n * 2 ^ 3 = 8 * to_Z n) by (change (2^3) with 8; lia).
  rewrite Hn.
  rewrite (Z.mod_small (8 * to_Z n)) by lia.
  assert (Hp : 0 < 2 ^ (8 * to_Z n) <= 2 ^ 56).
  { split. apply Z.pow_pos_nonneg; lia. apply Z.pow_le_mono_r; lia. }
  rewrite Z.mul_1_l. rewrite (Z.mod_small (2 ^ (8 * to_Z n))) by (change (2^63) with (2^56 * 2^7); lia).
  rewrite Z.mod_small by (change (2^63) with (2^56 * 2^7); lia). lia.
Qed.

Lemma ext_Z_false_lt lo n z : 0 < n -> 0 <= ext_Z false lo n z < 2 ^ (8 * n).
Proof. intros Hn. unfold ext_Z. apply Z.mod_pos_bound. apply Z.pow_pos_nonneg; lia. Qed.

Lemma wminu_le_l a b : w2Z (wminu a b) <= w2Z a.
Proof. unfold wminu. rewrite wltu_w2Z. destruct (Z.ltb_spec (w2Z a) (w2Z b)); lia. Qed.
Lemma wminu_le_r a b : w2Z (wminu a b) <= w2Z b.
Proof. unfold wminu. rewrite wltu_w2Z. destruct (Z.ltb_spec (w2Z a) (w2Z b)); lia. Qed.
Lemma w2Z_top_false u : wt u = false -> w2Z u < two63.
Proof. intros H. unfold w2Z. rewrite H. pose proof (Uint63.to_Z_bounded (wl u)). unfold two63. change wB with (2^63) in H0. lia. Qed.
Lemma land_le_l x y : 0 <= x -> 0 <= y -> Z.land x y <= x.
Proof.
  intros Hx Hy. rewrite <- (Z2N.id x) at 1 2 by lia. rewrite <- (Z2N.id y) by lia.
  rewrite <- N2Z.inj_land. pose proof (N.land_le_l (Z.to_N x) (Z.to_N y)). lia.
Qed.
Lemma land_le_r x y : 0 <= x -> 0 <= y -> Z.land x y <= y.
Proof. intros. rewrite Z.land_comm. apply land_le_l; assumption. Qed.
Lemma and_umax_aux x mm (ox : option w64) :
  (forall u, ox = Some u -> x <= w2Z u) -> 0 <= x ->
  Z.land x (w2Z mm) <= w2Z (match ox with Some u => wminu u mm | None => mm end).
Proof.
  intros Hox Hx. pose proof (w2Z_range mm).
  pose proof (land_le_l x (w2Z mm) Hx ltac:(lia)). pose proof (land_le_r x (w2Z mm) Hx ltac:(lia)).
  destruct ox as [u|].
  - pose proof (Hox u eq_refl). pose proof (wminu_le_l u mm). pose proof (wminu_le_r u mm).
    unfold wminu in *. destruct (wltu u mm); lia.
  - lia.
Qed.

Lemma bvu_nonneg n (b : bv n) : 0 <= bv_unsigned b.
Proof. pose proof (bv_unsigned_in_range n b). lia. Qed.
Lemma w2Z_nonneg w : 0 <= w2Z w.
Proof. pose proof (w2Z_range w). lia. Qed.

Lemma sv_umax_sound_gen E0 v : forall m, sv_umax v = Some m -> bv_unsigned (den E0 v) <= w2Z m.
Proof.
  assert (G : forall m n z lo, umax_of_width n = Some m -> 0 < to_Z n ->
             bv_unsigned (Z_to_bv 64 (ext_Z false lo (to_Z n) z)) <= w2Z m).
  { intros m n z lo Hu Hn. apply umax_of_width_sound in Hu as [Hr Hm]. rewrite Hm.
    pose proof (ext_Z_false_lt lo (to_Z n) z Hn) as Hb.
    rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
    assert (2 ^ (8 * to_Z n) <= 2 ^ 56) by (apply Z.pow_le_mono_r; lia).
    rewrite Z.mod_small by (change (2 ^ Z.of_N 64) with (2^56 * 2^8); lia). lia. }
  assert (SUM : forall x y u w, 0 <= x <= w2Z u -> 0 <= y <= w2Z w -> wt u = false -> wt w = false ->
            x + y <= w2Z (wadd u w) /\ x + y < two64).
  { intros x y u w Hx Hy Tu Tw. pose proof (w2Z_top_false u Tu). pose proof (w2Z_top_false w Tw).
    rewrite wadd_ok. unfold two63, two64 in *.
    rewrite (Z.mod_small (w2Z u + w2Z w)) by (pose proof (w2Z_range u); pose proof (w2Z_range w); unfold two64 in *; lia). lia. }
  induction v; intros m H; try discriminate H.
  - cbn [sv_umax] in H. injection H as <-. cbn [den]. rewrite wbv_unsigned. lia.
  -
    pose proof (bv_unsigned_in_range _ (den E0 v1)) as R1. pose proof (bv_unsigned_in_range _ (den E0 v2)) as R2.
    unfold bv_modulus in R1, R2. change (2 ^ Z.of_N 64) with two64 in R1, R2.
    destruct op; try discriminate H; cbn [sv_umax] in H; fold sv_umax in H.
    +   destruct (sv_umax v1) as [u|] eqn:U1; [|discriminate]. destruct (sv_umax v2) as [w|] eqn:U2; [|discriminate].
      destruct (wt u || wt w) eqn:T; [discriminate|]. injection H as <-.
      apply orb_false_elim in T as [T1 T2].
      destruct (SUM _ _ u w (conj (proj1 R1) (IHv1 u eq_refl)) (conj (proj1 R2) (IHv2 w eq_refl)) T1 T2) as [S1 S2].
      cbn [den alu64 alu]. rewrite bv_add_unsigned.
      unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with two64. rewrite Z.mod_small by lia. exact S1.
    +   destruct v2 as [s| | | | | | | | | |]; try discriminate H. injection H as <-.
      cbn [den alu64 alu]. rewrite bv_shiftr_unsigned, shamt6_bv.
      unfold wsrl. rewrite wsrl_k_ok by (pose proof (shamt6_range s); lia).
      rewrite Z.shiftr_div_pow2 by (pose proof (shamt6_range s); lia).
      assert (Hx : bv_unsigned (den E0 v1) <= w2Z match sv_umax v1 with Some u => u | None => wones end).
      { destruct (sv_umax v1) as [u|] eqn:U1. exact (IHv1 u eq_refl). change (w2Z wones) with (two64 - 1). lia. }
      apply Z.div_le_mono; [apply Z.pow_pos_nonneg; [lia|] | exact Hx].
      pose proof (shamt6_range s). lia.
    +   destruct (sv_umax v1) as [u|] eqn:U1; [|discriminate]. destruct (sv_umax v2) as [w|] eqn:U2; [|discriminate].
      destruct (wt u || wt w) eqn:T; [discriminate|]. injection H as <-.
      apply orb_false_elim in T as [T1 T2].
      destruct (SUM _ _ u w (conj (proj1 R1) (IHv1 u eq_refl)) (conj (proj1 R2) (IHv2 w eq_refl)) T1 T2) as [S1 S2].
      cbn [den alu64 alu]. rewrite bv_or_unsigned.
      pose proof (Z.add_lor_land (bv_unsigned (den E0 v1)) (bv_unsigned (den E0 v2))).
      pose proof (proj2 (Z.land_nonneg (bv_unsigned (den E0 v1)) (bv_unsigned (den E0 v2))) (or_introl (proj1 R1))). lia.
    +   cbn [den alu64 alu]. rewrite bv_and_unsigned.
      destruct v1 as [m1| | | | | | | | | |]; destruct v2 as [m2| | | | | | | | | |]; try discriminate H;
        injection H as <-; cbn [den]; rewrite ?wbv_unsigned;
        first [ apply and_umax_aux; [intros u Hu; exact (IHv1 u Hu) | apply bvu_nonneg]
              | rewrite Z.land_comm; apply and_umax_aux; [intros u Hu; exact (IHv2 u Hu) | apply bvu_nonneg]
              | pose proof (land_le_l (w2Z m1) (w2Z m2) (w2Z_nonneg m1) (w2Z_nonneg m2));
                pose proof (land_le_r (w2Z m1) (w2Z m2) (w2Z_nonneg m1) (w2Z_nonneg m2));
                unfold wminu; destruct (wltu _ _); lia
              | apply land_le_r; [apply bvu_nonneg | apply w2Z_nonneg]
              | apply land_le_l; [apply w2Z_nonneg | apply bvu_nonneg] ].
  - cbn [sv_umax] in H. destruct sx; [discriminate|]. pose proof (umax_of_width_sound _ _ H) as [Hr _].
    cbn [den]. unfold ext_word. apply G; [exact H|lia].
  - cbn [sv_umax] in H. destruct sx; [discriminate|]. pose proof (umax_of_width_sound _ _ H) as [Hr _].
    cbn [den]. unfold bytes_val. apply G; [exact H|lia].
  - cbn [sv_umax] in H. destruct sx; [discriminate|]. pose proof (umax_of_width_sound _ _ H) as [Hr _].
    cbn [den]. unfold bytes_val. apply G; [exact H|lia].
Qed.

Lemma sv_umax_sound v m : sv_umax v = Some m -> bv_unsigned (den E v) <= w2Z m.
Proof. apply sv_umax_sound_gen. Qed.

Lemma ext_Z_mask : forall lo n z, 0 <= lo -> 1 <= n -> n <= 8 ->
  Z.land (ext_Z true lo n z) (2 ^ (8 * n) - 1) = ext_Z false lo n z.
Proof.
  intros lo n z Hlo Hn Hn8. unfold ext_Z.
  assert (HP : 0 < 2 ^ (8 * n)) by (apply Z.pow_pos_nonneg; lia).
  assert (HU : 0 <= (z / 2 ^ (8 * lo)) mod 2 ^ (8 * n) < 2 ^ (8 * n)) by (apply Z.mod_pos_bound; lia).
  set (u := (z / 2 ^ (8 * lo)) mod 2 ^ (8 * n)) in *. clearbody u.
  assert (D64 : exists q, two64 = q * 2 ^ (8 * n) /\ 1 <= q).
  { exists (2 ^ (64 - 8 * n)). rewrite two64_eq, <- Z.pow_add_r by lia. split; [f_equal; lia|].
    change 1 with (2 ^ 0). apply Z.pow_le_mono_r; lia. }
  destruct D64 as (q & Q & Q1).
  replace (2 ^ (8 * n) - 1) with (Z.ones (8 * n)) by (rewrite Z.ones_equiv; lia).
  destruct (Z.leb_spec (2 ^ (8 * n - 1)) u) as [LE|LT].
  - rewrite Z.land_ones by lia.
    replace ((u - 2 ^ (8 * n)) mod two64) with (u - 2 ^ (8 * n) + two64).
    2: { symmetry. rewrite <- (Z_mod_plus_full (u - 2 ^ (8 * n)) 1 two64). rewrite Z.mod_small; [lia|]. rewrite Q. nia. }
    rewrite Q. replace (u - 2 ^ (8 * n) + q * 2 ^ (8 * n)) with (u + (q - 1) * 2 ^ (8 * n)) by lia.
    rewrite Z_mod_plus_full. apply Z.mod_small. lia.
  - rewrite Z.land_ones by lia. rewrite (Z.mod_small u two64) by (rewrite Q; nia). apply Z.mod_small. lia.
Qed.

Lemma bytes_val_mask : forall n bs, 1 <= n -> n <= 8 ->
  Z.land (bv_unsigned (bytes_val true n bs)) (2 ^ (8 * n) - 1) = bv_unsigned (bytes_val false n bs).
Proof.
  intros n bs Hn Hn8. unfold bytes_val. rewrite !Z_to_bv_unsigned.
  pose proof (ext_Z_range true 0 n (bytes_le_to_Z bs) ltac:(lia) ltac:(lia) Hn8) as R1.
  pose proof (ext_Z_range false 0 n (bytes_le_to_Z bs) ltac:(lia) ltac:(lia) Hn8) as R2.
  unfold bv_wrap. rewrite bv_modulus_64, !Z.mod_small by assumption. apply ext_Z_mask; lia.
Qed.

Lemma ext_word_mask : forall lo n w, 0 <= lo -> 1 <= n -> n <= 8 ->
  Z.land (bv_unsigned (ext_word true lo n w)) (2 ^ (8 * n) - 1) = bv_unsigned (ext_word false lo n w).
Proof.
  intros lo n w Hlo Hn Hn8. unfold ext_word. rewrite !Z_to_bv_unsigned.
  pose proof (ext_Z_range true lo n (bv_unsigned w) Hlo ltac:(lia) Hn8) as R1.
  pose proof (ext_Z_range false lo n (bv_unsigned w) Hlo ltac:(lia) Hn8) as R2.
  unfold bv_wrap. rewrite bv_modulus_64, !Z.mod_small by assumption. apply ext_Z_mask; lia.
Qed.

Lemma zext_twin_sound : forall x n x' m, zext_twin x = Some (n, x') -> umax_of_width n = Some m ->
  Z.land (bv_unsigned (den E x)) (w2Z m) = bv_unsigned (den E x').
Proof.
  intros x n x' m H Hm. destruct (umax_of_width_sound n m Hm) as [Hn ->].
  destruct x; cbn [zext_twin] in H; try discriminate H;
    match type of H with context [if ?s then _ else _] => destruct s; [| discriminate H] | _ => idtac end;
    try (destruct sx; [| discriminate H]); injection H as <- <-; cbn [den].
  - pose proof (int_range lo). apply ext_word_mask; lia.
  - apply bytes_val_mask; lia.
  - apply bytes_val_mask; lia.
Qed.

Lemma is_low_mask_sound : forall c, is_low_mask c = true -> exists j, 0 <= j /\ w2Z c = Z.ones j.
Proof.
  intros c H. unfold is_low_mask in H. apply andb_prop in H as [H _]. apply Z.eqb_eq in H.
  exists (Z.log2 (w2Z c + 1)). split; [apply Z.log2_nonneg|]. rewrite Z.ones_equiv. lia.
Qed.

Lemma den_and_refold : forall r, den E (and_refold r) = den E r.
Proof.
  intros r. unfold and_refold. destruct r as [| | op x b| | | | | | | |]; try reflexivity.
  destruct op; try reflexivity. destruct b as [c| | | | | | | | | |]; try reflexivity.
  destruct (zext_twin x) as [[n x']|] eqn:ZT.
  - destruct (umax_of_width n) as [m|] eqn:UM; [|reflexivity]. destruct (weqb m c) eqn:MC.
    + apply (proj1 (weqb_ok _ _)) in MC. subst c.
      cbn [den alu64 alu]. apply bv_eq. rewrite bv_and_unsigned, wbv_unsigned. symmetry. exact (zext_twin_sound x n x' m ZT UM).
    + destruct (wleu c m) eqn:LE; [|reflexivity].
      rewrite wleu_ok in LE. apply negb_true_iff in LE. apply (proj1 (ltu_iff _ _ false)) in LE. rewrite !wbv_unsigned in LE.
      pose proof (zext_twin_sound x n x' m ZT UM) as TW. destruct (umax_of_width_sound n m UM) as [Hn Hm].
      cbn [den alu64 alu]. apply bv_eq. rewrite !bv_and_unsigned, wbv_unsigned, <- TW.

      rewrite <- Z.land_assoc. f_equal.
      rewrite Hm in LE |- *. replace (2 ^ (8 * to_Z n) - 1) with (Z.ones (8 * to_Z n)) by (rewrite Z.ones_equiv; lia).
      rewrite Z.land_comm, Z.land_ones by lia. apply Z.mod_small. pose proof (w2Z_range c). lia.
  - destruct (is_low_mask c) eqn:LM; [|reflexivity]. destruct (sv_umax x) as [u|] eqn:UX; [|reflexivity].
    destruct (wleu u c) eqn:LE; [|reflexivity].
    destruct (is_low_mask_sound c LM) as (j & Hj & Cj).
    pose proof (sv_umax_sound x u UX) as UB. rewrite wleu_ok in LE. apply negb_true_iff in LE.
    apply (proj1 (ltu_iff _ _ false)) in LE. rewrite !wbv_unsigned in LE.
    cbn [den alu64 alu]. apply bv_eq. rewrite bv_and_unsigned, wbv_unsigned, Cj. rewrite Z.land_ones by (pose proof (bv_unsigned_in_range _ (den E x)); lia).
    symmetry. apply Z.mod_small. pose proof (bv_unsigned_in_range _ (den E x)).
    assert (w2Z c < 2 ^ j) by (rewrite Cj, Z.ones_equiv; lia). lia.
Qed.

Lemma den_subsub_fold : forall r, den E (subsub_fold r) = den E r.
Proof.
  intros r. unfold subsub_fold. destruct r as [| | op a b| | | | | | | |]; try reflexivity.
  destruct op; try reflexivity. destruct b as [| | op2 x y| | | | | | | |]; try reflexivity. destruct op2; try reflexivity.
  destruct (sv_eqb x a) eqn:Q; [|reflexivity]. apply sv_eqb_eq in Q. subst x.
  cbn [den alu64 alu]. bv_solve.
Qed.

Lemma srl_sll_mod : forall X s, 0 <= X -> 0 < s < 64 -> ((X * 2 ^ s) mod 2 ^ 64) / 2 ^ s = X mod 2 ^ (64 - s).
Proof.
  intros X s HX Hs. assert (PS : 0 < 2 ^ s) by (apply Z.pow_pos_nonneg; lia).
  assert (P64 : 2 ^ 64 = 2 ^ (64 - s) * 2 ^ s) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
  rewrite P64, Z.mul_mod_distr_r by lia. apply Z.div_mul. lia.
Qed.
Lemma den_zext_canon : forall x k k', shamt6 k = shamt6 k' ->
  den E (zext_canon x k (VAlu ALU_SRL (VAlu ALU_SLL x (VL k)) (VL k'))) = den E (VAlu ALU_SRL (VAlu ALU_SLL x (VL k)) (VL k')).
Proof.
  intros x k k' SK. unfold zext_canon, zext_bytes.
  pose proof (bv_unsigned_in_range _ (den E x)) as XR. rewrite bv_modulus_64 in XR.
  assert (KEY : forall s n : Z, to_Z (shamt6 k) = s -> 0 < s < 64 -> 8 * n = 64 - s -> 1 <= n <= 8 ->
            ext_word false 0 n (den E x) = den E (VAlu ALU_SRL (VAlu ALU_SLL x (VL k)) (VL k'))).
  { intros s n Hs Rs Hn Rn. cbn [den alu64 alu]. apply bv_eq. unfold ext_word, ext_Z.
    rewrite bv_shiftr_unsigned, bv_shiftl_unsigned, !shamt6_bv, <- SK, Hs.
    rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. unfold bv_wrap. rewrite bv_modulus_64.
    rewrite (srl_sll_mod _ s) by lia. rewrite Hn. change (8 * 0) with 0. rewrite Z.pow_0_r, Z.div_1_r.
    assert (0 < 2 ^ (64 - s) <= 2 ^ 64) by (split; [apply Z.pow_pos_nonneg; lia| apply Z.pow_le_mono_r; lia]).
    pose proof (Z.mod_pos_bound (bv_unsigned (den E x)) (2 ^ (64 - s)) ltac:(lia)).
    rewrite Z_to_bv_unsigned. unfold bv_wrap. rewrite bv_modulus_64. apply Z.mod_small. unfold two64 in *. lia. }
  Local Ltac zc_case KEY sZ nZ :=
    match goal with
    | |- den _ (match (if PrimInt63.eqb ?a ?b then _ else _) with _ => _ end) = _ =>
        let Q := fresh "Q" in
        destruct (PrimInt63.eqb a b) eqn:Q;
        [ apply Uint63.eqb_correct in Q; rewrite den_sv_ext by (unfold width_ok; cbn; lia);
          apply (KEY sZ nZ); [rewrite Q; reflexivity| lia| lia| lia] |]
    end.
  zc_case KEY 8 7. zc_case KEY 16 6. zc_case KEY 24 5. zc_case KEY 32 4. zc_case KEY 40 3. zc_case KEY 48 2. zc_case KEY 56 1.
  reflexivity.
Qed.

Lemma den_srlsll_fold : forall r, den E (srlsll_fold r) = den E r.
Proof.
  intros r. unfold srlsll_fold. destruct r as [| | op a b| | | | | | | |]; try reflexivity.
  destruct op; try reflexivity. destruct a as [| | op2 x kk| | | | | | | |]; try reflexivity. destruct op2; try reflexivity.
  destruct kk as [k| | | | | | | | | |]; try reflexivity. destruct b as [k'| | | | | | | | | |]; try reflexivity.
  destruct (PrimInt63.eqb (shamt6 k) (shamt6 k')) eqn:SK; [|reflexivity]. apply Uint63.eqb_correct in SK.
  destruct (sv_umax x) as [u|] eqn:UX; [|exact (den_zext_canon x k k' SK)].
  destruct (weqb (wsrl (wsll u k) k) u) eqn:RT; [|exact (den_zext_canon x k k' SK)].
  apply (proj1 (weqb_w2Z _ _)) in RT. unfold wsrl, wsll in RT.
  pose proof (shamt6_range k) as SR.
  rewrite wsrl_k_ok, wsll_k_ok in RT by lia.
  pose proof (sv_umax_sound x u UX) as UB.
  pose proof (w2Z_range u) as UR. pose proof (bv_unsigned_in_range _ (den E x)) as XR. rewrite bv_modulus_64 in XR.
  set (s := to_Z (shamt6 k)) in *. set (X := bv_unsigned (den E x)) in *.
  assert (PS : 0 < 2 ^ s) by (apply Z.pow_pos_nonneg; lia).
  assert (P64 : 2 ^ 64 = 2 ^ s * 2 ^ (64 - s)) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).

  assert (NW : w2Z u * 2 ^ s < 2 ^ 64).
  { destruct (Z.lt_ge_cases (w2Z u * 2 ^ s) (2 ^ 64)) as [L|G]; [exact L| exfalso].
    assert (M : (w2Z u * 2 ^ s) mod 2 ^ 64 <= w2Z u * 2 ^ s - 2 ^ 64).
    { rewrite <- (Z_mod_plus_full (w2Z u * 2 ^ s) (-1) (2 ^ 64)). replace (w2Z u * 2 ^ s + -1 * 2 ^ 64) with (w2Z u * 2 ^ s - 2 ^ 64) by lia.
      apply Z.mod_le; [lia| lia]. }
    assert (D : (w2Z u * 2 ^ s) mod 2 ^ 64 / 2 ^ s <= (w2Z u * 2 ^ s - 2 ^ 64) / 2 ^ s) by (apply Z.div_le_mono; lia).
    rewrite RT in D. replace (w2Z u * 2 ^ s - 2 ^ 64) with ((w2Z u - 2 ^ (64 - s)) * 2 ^ s) in D by (rewrite P64; lia).
    rewrite Z.div_mul in D by lia. assert (0 < 2 ^ (64 - s)) by (apply Z.pow_pos_nonneg; lia). lia. }
  cbn [den alu64 alu]. apply bv_eq. symmetry.
  rewrite bv_shiftr_unsigned, bv_shiftl_unsigned, !shamt6_bv, <- SK. fold s.
  rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. unfold bv_wrap. rewrite bv_modulus_64. fold X.
  rewrite Z.mod_small by (unfold two64; nia). rewrite Z.div_mul by lia. reflexivity.
Qed.

Lemma lxor_ones64 x : 0 <= x < two64 -> Z.lxor x (two64 - 1) = two64 - 1 - x.
Proof.
  intros Hx.
  assert (E1 : two64 - 1 - x = (Z.lnot x) mod two64).
  { apply (Z.mod_unique_pos (Z.lnot x) two64 (-1) (two64 - 1 - x)); unfold Z.lnot, two64 in *; lia. }
  rewrite E1. unfold two64 in *. change (18446744073709551616 - 1) with (Z.ones 64). change 18446744073709551616 with (2 ^ 64).
  apply Z.bits_inj'; intros m Hm. rewrite Z.lxor_spec, Z.testbit_mod_pow2, Z.lnot_spec by lia.
  destruct (Z.ltb_spec m 64).
  - rewrite Z.ones_spec_low by lia. destruct (Z.testbit x m); reflexivity.
  - rewrite Z.ones_spec_high by lia. rewrite Bool.xorb_false_r.
    apply Z.bits_above_log2; [lia|].
    destruct (Z.eq_dec x 0) as [->|NZ]; [cbn; lia|].
    apply Z.log2_lt_pow2; [lia|]. apply (Z.lt_le_trans _ (2 ^ 64)); [lia|]. apply Z.pow_le_mono_r; lia.
Qed.

Lemma den_xor_not_fold : forall r, den E (xor_not_fold r) = den E r.
Proof.
  intros r. unfold xor_not_fold.
  assert (K : forall x c, weqb c wones = true -> den E (VAlu ALU_SUB (VL wones) x) = den E (VAlu ALU_XOR x (VL c))
                                              /\ den E (VAlu ALU_SUB (VL wones) x) = den E (VAlu ALU_XOR (VL c) x)).
  { intros x c Hc. apply weqb_wones_unsigned in Hc.
    pose proof (bv_unsigned_in_range _ (den E x)) as R. rewrite bv_modulus_64 in R.
    assert (W1 : bv_unsigned (den E (VL wones)) = two64 - 1) by (cbn [den]; apply weqb_wones_unsigned; apply weqb_refl).
    assert (Wc : bv_unsigned (den E (VL c)) = two64 - 1) by (cbn [den]; exact Hc).
    cbn [den alu64 alu] in *. split; apply bv_eq; rewrite bv_sub_unsigned, bv_xor_unsigned, W1, Wc;
      [| rewrite Z.lxor_comm]; rewrite lxor_ones64 by lia; unfold bv_wrap; rewrite bv_modulus_64; apply Z.mod_small; lia. }
  destruct r as [| | op a b| | | | | | | |]; try reflexivity. destruct op; try reflexivity.
  destruct a as [za| | | | | | | | | |]; destruct b as [zb| | | | | | | | | |]; try reflexivity.
  all: match goal with
       | |- den E (if weqb ?c wones then _ else _) = _ => destruct (weqb c wones) eqn:W; [|reflexivity]
       end.
  all: first [apply (proj1 (K _ _ W)) | apply (proj2 (K _ _ W))].
Qed.

Lemma mod_pow2_le a m n : 0 <= m <= n -> (a mod 2 ^ n) mod 2 ^ m = a mod 2 ^ m.
Proof.
  intros H. symmetry. apply Znumtheory.Zmod_div_mod; try (apply Z.pow_pos_nonneg; lia).
  exists (2 ^ (n - m)). rewrite <- Z.pow_add_r by lia. f_equal. lia.
Qed.

Lemma shl_sextw_high' : forall (w zw : word) (s : Z), bv_unsigned zw = 0 -> 32 <= s < 64 ->
  (bv_unsigned (sext 64 (alu32 ALU_ADD (low32 w) (low32 zw))) * 2 ^ s) mod two64 = (bv_unsigned w * 2 ^ s) mod two64
  /\ (bv_unsigned (sext 64 (alu32 ALU_ADD (low32 zw) (low32 w))) * 2 ^ s) mod two64 = (bv_unsigned w * 2 ^ s) mod two64.
Proof.
  intros w zw s Hzw Hs.
  pose proof (bv_unsigned_in_range _ w) as R. rewrite bv_modulus_64 in R.
  assert (Z0 : bv_unsigned (low32 zw) = 0) by (rewrite low32_ext, Hzw; reflexivity).
  assert (G : forall v : word, bv_unsigned v mod 2 ^ 32 = bv_unsigned w mod 2 ^ 32 ->
             (bv_unsigned v * 2 ^ s) mod two64 = (bv_unsigned w * 2 ^ s) mod two64).
  { intros v M.
    assert (P64 : two64 = 2 ^ s * 2 ^ (64 - s)).
    { rewrite <- Z.pow_add_r by lia. replace (s + (64 - s)) with 64 by lia. reflexivity. }
    rewrite P64.
    assert (PS : 0 < 2 ^ s) by (apply Z.pow_pos_nonneg; lia).
    assert (PR : 0 < 2 ^ (64 - s)) by (apply Z.pow_pos_nonneg; lia).
    rewrite (Z.mul_comm (bv_unsigned v) (2 ^ s)), (Z.mul_comm (bv_unsigned w) (2 ^ s)).
    rewrite !Z.mul_mod_distr_l by lia.
    f_equal. rewrite <- (mod_pow2_le (bv_unsigned v) (64 - s) 32), <- (mod_pow2_le (bv_unsigned w) (64 - s) 32) by lia.
    rewrite M. reflexivity. }
  assert (SX : forall u, u mod 2 ^ 32 = bv_unsigned w mod 2 ^ 32 -> 0 <= u -> sx32Z (u mod 2 ^ 32) mod 2 ^ 32 = bv_unsigned w mod 2 ^ 32).
  { intros u Hu Hu0. unfold sx32Z. destruct (Z.leb_spec (2 ^ 31) (u mod 2 ^ 32)).
    - rewrite (mod_pow2_le _ 32 64) by lia. rewrite Zminus_mod, Z.mod_mod, Z.mod_same, Z.sub_0_r, Z.mod_mod by lia. exact Hu.
    - rewrite Z.mod_mod by lia. exact Hu. }
  split; apply G; rewrite sext32_unsigned; cbn [alu32 alu]; rewrite bv_add_unsigned, Z0, ?Z.add_0_r, ?Z.add_0_l, low32_ext;
    unfold bv_wrap; change (bv_modulus 32) with (2 ^ 32); apply SX; try (apply Z.mod_mod; lia); apply Z.mod_pos_bound; lia.
Qed.

Lemma den_sllw_fold : forall r, den E (sllw_fold r) = den E r.
Proof.
  intros r. unfold sllw_fold. destruct r as [| | op a b| | | | | | | |]; try reflexivity. destruct op; try reflexivity.
  assert (K : forall x z c, weqb z wzero && PrimInt63.leb 32%uint63 (shamt6 c) = true ->
             den E (VAlu ALU_SLL x (VL c)) = den E (VAlu ALU_SLL (VAluw ALU_ADD x (VL z)) (VL c))
             /\ den E (VAlu ALU_SLL x (VL c)) = den E (VAlu ALU_SLL (VAluw ALU_ADD (VL z) x) (VL c))).
  { intros x z c H. apply andb_prop in H as [Hz0 Hs]. apply weqb_wzero_unsigned in Hz0.
    rewrite Uint63.leb_spec in Hs. change (to_Z 32%uint63) with 32 in Hs. pose proof (shamt6_range c) as SR.
    pose proof (shl_sextw_high' (den E x) (wbv z) (to_Z (shamt6 c)) Hz0 ltac:(lia)) as [A B].
    cbn [den alu64 alu]. split; apply bv_eq; rewrite !bv_shiftl_unsigned, !shamt6_bv, !Z.shiftl_mul_pow2 by lia;
      unfold bv_wrap; rewrite bv_modulus_64; symmetry; [exact A| exact B]. }
  destruct a as [| | | opw x y| | | | | | |]; destruct b as [c| | | | | | | | | |]; try reflexivity.
  all: try (destruct opw; try reflexivity).
  all: try (destruct x as [zx| | | | | | | | | |]; destruct y as [zy| | | | | | | | | |]; try reflexivity).
  all: try match goal with
       | |- den E (if ?cnd then _ else _) = _ => destruct cnd eqn:W; [|reflexivity]
       end.
  all: try first [apply (proj1 (K _ _ _ W)) | apply (proj2 (K _ _ _ W))].
Qed.

Lemma den_sv_alu : forall op a b, den E (sv_alu op a b) = alu64 op (den E a) (den E b).
Proof.
  intros op a b. unfold sv_alu.
  destruct op; rewrite ?BDP.den_refold, ?den_and_refold, ?den_subsub_fold, ?den_srlsll_fold, ?den_sllw_fold, ?den_xor_not_fold;
    apply den_sv_alu0.
Qed.

Lemma sv_vars_below_and_refold : forall n r, sv_vars_below n r = true -> sv_vars_below n (and_refold r) = true.
Proof.
  intros n r H. unfold and_refold. destruct r as [| | op x b| | | | | | | |]; try exact H.
  destruct op; try exact H. destruct b as [c| | | | | | | | | |]; try exact H.
  cbn [sv_vars_below] in H. rewrite andb_true_r in H.
  destruct (zext_twin x) as [[m x']|] eqn:ZT.
  - assert (X' : sv_vars_below n x' = sv_vars_below n x).
    { destruct x; cbn [zext_twin] in ZT; try discriminate ZT; destruct sx; try discriminate ZT; injection ZT as <- <-; reflexivity. }
    destruct (umax_of_width m) as [mm|]; [|cbn [sv_vars_below]; rewrite H; reflexivity].
    destruct (weqb mm c); [rewrite X'; exact H|]. destruct (wleu c mm); cbn [sv_vars_below]; rewrite ?X', H; reflexivity.
  - destruct (is_low_mask c); [|cbn [sv_vars_below]; rewrite H; reflexivity].
    destruct (sv_umax x); [|cbn [sv_vars_below]; rewrite H; reflexivity].
    destruct (wleu w c); [exact H| cbn [sv_vars_below]; rewrite H; reflexivity].
Qed.
Lemma sv_vars_below_subsub_fold : forall n r, sv_vars_below n r = true -> sv_vars_below n (subsub_fold r) = true.
Proof.
  intros n r H. unfold subsub_fold. destruct r as [| | op a b| | | | | | | |]; try exact H.
  destruct op; try exact H. destruct b as [| | op2 x y| | | | | | | |]; try exact H. destruct op2; try exact H.
  destruct (sv_eqb x a); [|exact H]. cbn [sv_vars_below] in H. apply andb_prop in H as [_ H]. apply andb_prop in H as [_ H]. exact H.
Qed.

Lemma sv_vars_below_sv_ext : forall n a sx lo m, sv_vars_below n a = true -> sv_vars_below n (sv_ext sx lo m a) = true.
Proof.
  intros n a. induction a as [w|k o|op a1 IH1 a2 IH2|op a1 IH1 a2 IH2|op a1 IH1 a2 IH2|op a1 IH1 a2 IH2|sx2 lo2 n2 y IHy|lo2 n2 a1 IH1 a2 IH2|sx2 j off IHo n2|sx2 k off n2|op a1 IH1];
    intros sx lo m H; cbn [sv_ext].
  all: try (destruct (PrimInt63.eqb lo 0%uint63 && PrimInt63.eqb m 8%uint63); [exact H| cbn [sv_vars_below]; exact H]).
  - destruct (PrimInt63.leb lo2 8%uint63 && PrimInt63.leb (PrimInt63.add lo m) n2 && PrimInt63.leb (PrimInt63.add lo2 (PrimInt63.add lo m)) 8%uint63).
    + apply IHy. exact H.
    + destruct (PrimInt63.eqb lo 0%uint63 && PrimInt63.eqb m 8%uint63); [exact H| cbn [sv_vars_below]; exact H].
  - cbn [sv_vars_below] in H. apply andb_prop in H as [H1 H2].
    destruct (PrimInt63.leb lo2 8%uint63 && PrimInt63.ltb 0%uint63 n2 && PrimInt63.leb n2 8%uint63 && PrimInt63.leb (PrimInt63.add lo2 n2) 8%uint63).
    + destruct (PrimInt63.leb lo2 lo && PrimInt63.leb (PrimInt63.add lo m) (PrimInt63.add lo2 n2)); [apply IH2; exact H2|].
      destruct (PrimInt63.leb (PrimInt63.add lo m) lo2 || PrimInt63.leb (PrimInt63.add lo2 n2) lo); [apply IH1; exact H1|].
      destruct (PrimInt63.eqb lo 0%uint63 && PrimInt63.eqb m 8%uint63); cbn [sv_vars_below]; rewrite H1, H2; reflexivity.
    + destruct (PrimInt63.eqb lo 0%uint63 && PrimInt63.eqb m 8%uint63); cbn [sv_vars_below]; rewrite H1, H2; reflexivity.
  - destruct off as [x| | | | | | | | | |];
      try (destruct (PrimInt63.eqb lo 0%uint63 && PrimInt63.eqb m 8%uint63); [exact H| cbn [sv_vars_below]; exact H]).
    destruct (PrimInt63.leb (PrimInt63.add lo m) n2 && negb (wt x)); [reflexivity| cbn [sv_vars_below]; exact H].
  - destruct (PrimInt63.leb (PrimInt63.add lo m) n2 && (wt off || negb (wt (wadd off (wlit lo))))); cbn [sv_vars_below] in *; exact H.
Qed.
Lemma sv_vars_below_srlsll_fold : forall n r, sv_vars_below n r = true -> sv_vars_below n (srlsll_fold r) = true.
Proof.
  intros n r H. unfold srlsll_fold. destruct r as [| | op a b| | | | | | | |]; try exact H.
  destruct op; try exact H. destruct a as [| | op2 x kk| | | | | | | |]; try exact H. destruct op2; try exact H.
  destruct kk as [k| | | | | | | | | |]; try exact H. destruct b as [k'| | | | | | | | | |]; try exact H.
  assert (HX : sv_vars_below n x = true) by (cbn [sv_vars_below] in H; apply andb_prop in H as [H _]; rewrite andb_true_r in H; exact H).
  assert (ZC : sv_vars_below n (zext_canon x k (VAlu ALU_SRL (VAlu ALU_SLL x (VL k)) (VL k'))) = true).
  { unfold zext_canon. destruct (zext_bytes (shamt6 k)); [apply sv_vars_below_sv_ext; exact HX| exact H]. }
  destruct (PrimInt63.eqb (shamt6 k) (shamt6 k')); [|exact H]. destruct (sv_umax x); [|exact ZC]. destruct (weqb (wsrl (wsll w k) k) w); [|exact ZC].
  exact HX.
Qed.

Lemma w2Zs_range o : - two63 <= w2Zs o < two63.
Proof. unfold w2Zs. pose proof (w2Z_wt o). pose proof (w2Z_range o). destruct (wt o); destruct (Z.leb_spec two63 (w2Z o)); try discriminate; unfold two63, two64 in *; lia. Qed.
Lemma w2Z_of_w2Zs o : w2Z o = w2Zs o + (if wt o then 1 else 0) * two64.
Proof. unfold w2Zs. destruct (wt o); lia. Qed.

Lemma mod_add_cancel_l K a b : 0 <= a < two64 -> 0 <= b < two64 ->
  (K + a) mod two64 = (K + b) mod two64 -> a = b.
Proof.
  intros Ha Hb H.
  assert (Ea : a = ((K + a) mod two64 - K) mod two64).
  { rewrite Zminus_mod_idemp_l by (unfold two64; lia). replace (K + a - K) with a by lia. symmetry. apply Z.mod_small. lia. }
  assert (Eb : b = ((K + b) mod two64 - K) mod two64).
  { rewrite Zminus_mod_idemp_l by (unfold two64; lia). replace (K + b - K) with b by lia. symmetry. apply Z.mod_small. lia. }
  rewrite Ea, Eb, H. reflexivity.
Qed.

Lemma pow2_divide m n : 0 <= m <= n -> (2 ^ m | 2 ^ n).
Proof. intros H. exists (2 ^ (n - m)). rewrite <- Z.pow_add_r by lia. f_equal. lia. Qed.

Lemma mod_pow2_mod a m n : 0 <= m <= n -> (a mod 2 ^ n) mod 2 ^ m = a mod 2 ^ m.
Proof. intros H. apply Z.mod_mod_divide. apply pow2_divide. lia. Qed.

Lemma mod64_mod a m : 0 <= m <= 63 -> (a mod two64) mod 2 ^ m = a mod 2 ^ m.
Proof. intros H. rewrite two64_eq. apply mod_pow2_mod. lia. Qed.

Lemma to_Z_mk m : to_Z m <= 63 -> to_Z (PrimInt63.sub (PrimInt63.lsl 1 m) 1) = 2 ^ (to_Z m) - 1.
Proof.
  intros Hm. pose proof (int_range m). rewrite sub_spec, lsl_spec, wB_two63, two63_eq in *. change (to_Z 1) with 1. rewrite Z.mul_1_l.
  destruct (Z.eq_dec (to_Z m) 63) as [E63|E63].
  - rewrite E63, Z.mod_same by lia. reflexivity.
  - assert (0 < 2 ^ to_Z m < 2 ^ 63) by (split; [apply Z.pow_pos_nonneg|apply Z.pow_lt_mono_r]; lia).
    rewrite !Z.mod_small; lia.
Qed.

Lemma land_mk x m : to_Z m <= 63 -> to_Z (PrimInt63.land x (PrimInt63.sub (PrimInt63.lsl 1 m) 1)) = to_Z x mod 2 ^ (to_Z m).
Proof.
  intros Hm. rewrite land_spec', to_Z_mk, pow2_m1_ones by lia. apply Z.land_ones. pose proof (int_range m); lia.
Qed.

Definition inb (z : Z) (b : bnd) : Prop := w2Z (fst b) <= z <= w2Z (snd b).
Local Notation U v := (bv_unsigned (den E v)).

Lemma U_range v : 0 <= U v < two64.
Proof. rewrite <- bv_modulus_64. apply bv_unsigned_in_range. Qed.

Lemma full_ok z : 0 <= z < two64 -> inb z full_bnd.
Proof. intros Hr. unfold inb, full_bnd; cbn [fst snd]. rewrite wzero_ok. change (w2Z wones) with (two64 - 1). lia. Qed.

Lemma wmaxu_ge_l a b : w2Z a <= w2Z (wmaxu a b).
Proof. unfold wmaxu. rewrite wltu_w2Z. destruct (Z.ltb_spec (w2Z a) (w2Z b)); lia. Qed.
Lemma wmaxu_ge_r a b : w2Z b <= w2Z (wmaxu a b).
Proof. unfold wmaxu. rewrite wltu_w2Z. destruct (Z.ltb_spec (w2Z a) (w2Z b)); lia. Qed.
Lemma wmaxu_lub a b z : w2Z a <= z -> w2Z b <= z -> w2Z (wmaxu a b) <= z.
Proof. unfold wmaxu. destruct (wltu a b); lia. Qed.
Lemma wminu_glb a b z : z <= w2Z a -> z <= w2Z b -> z <= w2Z (wminu a b).
Proof. unfold wminu. destruct (wltu a b); lia. Qed.

Lemma lit_of_sound x c : lit_of x = Some c -> U x = w2Z c.
Proof. destruct x; cbn [lit_of]; intros H; try discriminate H. injection H as ->. apply den_VL. Qed.
Lemma umax_dflt_ok n z : 0 < to_Z n -> (exists lo z0, z = ext_Z false lo (to_Z n) z0) ->
  0 <= z < two64 ->
  inb z (match umax_of_width n with Some m => (wzero, m) | None => full_bnd end).
Proof.
  intros Hn [lo [z0 ->]] R. destruct (umax_of_width n) as [m|] eqn:U0; [|apply full_ok; exact R].
  apply umax_of_width_sound in U0 as [Hr Hm]. unfold inb; cbn [fst snd]. rewrite wzero_ok, Hm.
  pose proof (ext_Z_false_lt lo (to_Z n) z0 Hn). lia.
Qed.
Lemma wadd_one_lo c z : w2Z c < z -> z < two64 -> w2Z (wadd c wone) <= z.
Proof. intros. pose proof (w2Z_range c). rewrite wadd_ok, wone_ok, Z.mod_small by lia. lia. Qed.
Lemma wsub_one_hi c z : z < w2Z c -> 0 <= z -> z <= w2Z (wsub c wone).
Proof. intros. pose proof (w2Z_range c). rewrite wsub_ok, wone_ok, Z.mod_small by lia. lia. Qed.

Lemma bump_sound v b c : U v <> w2Z c -> inb (U v) b -> inb (U v) (bump b c).
Proof.
  intros NE Hb. destruct b as [lo hi]. unfold inb, bump in *; cbn [fst snd] in *.
  pose proof (U_range v). pose proof (w2Z_range c). pose proof (w2Z_range lo). pose proof (w2Z_range hi).
  split.
  - destruct (weqb lo c) eqn:W; [|lia]. apply weqb_eq in W. subst lo.
    rewrite wadd_ok, wone_ok. destruct (Z.eq_dec (w2Z c + 1) two64) as [EQ|NEQ]; [rewrite EQ, Z.mod_same by (unfold two64; lia); lia|].
    rewrite Z.mod_small by lia. lia.
  - destruct (weqb hi c) eqn:W; [|lia]. apply weqb_eq in W. subst hi.
    rewrite wsub_ok, wone_ok. destruct (Z.eq_dec (w2Z c) 0) as [EQ|NEQ]; [lia|]. rewrite Z.mod_small by lia. lia.
Qed.

Lemma fact_bnd1_sound f v b : fact_holds E f -> inb (U v) b -> inb (U v) (fact_bnd1 f v b).
Proof.
  intros Hf Hb. pose proof (U_range v) as R. destruct b as [lo hi].
  destruct f as [| |x y|x y|x y|x y| |]; try exact Hb; cbn [fact_holds] in Hf.
  all: match type of Hf with
       | _ <> _ =>
         unfold fact_bnd1;
         destruct (lit_of y) as [c|] eqn:Ly;
         [ destruct (sv_eqb x v) eqn:Q; [|exact Hb]; apply sv_eqb_eq in Q; subst x; apply bump_sound; [|exact Hb];
           intros EQ; apply Hf; apply bv_eq; rewrite EQ; symmetry; exact (lit_of_sound y c Ly)
         | destruct (lit_of x) as [c|] eqn:Lx; [|exact Hb]; destruct (sv_eqb y v) eqn:Q; [|exact Hb]; apply sv_eqb_eq in Q; subst y;
           apply bump_sound; [|exact Hb]; intros EQ; apply Hf; apply bv_eq; rewrite EQ; exact (lit_of_sound x c Lx) ]
       | _ => idtac
       end.
  all: unfold inb in Hb |- *; cbn [fst snd] in Hb; unfold fact_bnd1.
  all: destruct (lit_of y) as [c|] eqn:Ly;
       [ apply lit_of_sound in Ly; destruct (sv_eqb x v) eqn:Q; cbn [fst snd]; [apply sv_eqb_eq in Q; subst x|exact Hb]
       | destruct (lit_of x) as [c|] eqn:Lx; cbn [fst snd]; [|exact Hb];
         apply lit_of_sound in Lx; destruct (sv_eqb y v) eqn:Q; cbn [fst snd]; [apply sv_eqb_eq in Q; subst y|exact Hb] ].
  all: try rewrite Ly in *; try rewrite Lx in *.
  - split; [lia|]. apply wminu_glb; [lia|]. apply wsub_one_hi; lia.
  - split; [|lia]. apply wmaxu_lub; [lia|]. apply wadd_one_lo; lia.
  - split; [lia|]. apply wminu_glb; lia.
  - split; [|lia]. apply wmaxu_lub; lia.
  - apply (f_equal bv_unsigned) in Hf. rewrite Ly in Hf. split; [apply wmaxu_lub; lia|apply wminu_glb; lia].
  - apply (f_equal bv_unsigned) in Hf. rewrite Lx in Hf. split; [apply wmaxu_lub; lia|apply wminu_glb; lia].
Qed.

Lemma den_add_u' : forall a b, U (VAlu ALU_ADD a b) = (U a + U b) mod two64.
Proof.
  intros a b. change (den E (VAlu ALU_ADD a b)) with (alu64 ALU_ADD (den E a) (den E b)). cbn [alu64 alu].
  rewrite bv_add_unsigned. unfold bv_wrap. rewrite bv_modulus_64. reflexivity.
Qed.

Lemma anchored_sound : forall k a o r, anchored k a = Some (o, r) ->
  U a = (bv_unsigned (ev E k) + w2Z o + match r with Some y => U y | None => 0 end) mod two64.
Proof.
  intros k a o r H. unfold anchored in H.
  destruct a as [|k' o'|op x y| | | | | | | |]; try discriminate H.
  - destruct (PrimInt63.eqb k' k) eqn:K; [|discriminate H]. apply Uint63.eqb_correct in K. subst k'. injection H as <- <-.
    rewrite Z.add_0_r. apply den_VPu.
  - destruct op; try discriminate H. rewrite den_add_u'.
    destruct x as [|k1 o1| | | | | | | | |].
    all: try (destruct (PrimInt63.eqb k1 k) eqn:K;
              [apply Uint63.eqb_correct in K; subst k1; injection H as <- <-;
               rewrite den_VPu, Z.add_mod_idemp_l by (unfold two64; lia); f_equal; lia|]).
    all: destruct y as [|k2 o2| | | | | | | | |]; try discriminate H.
    all: destruct (PrimInt63.eqb k2 k) eqn:K2; [|discriminate H]; apply Uint63.eqb_correct in K2; subst k2; injection H as <- <-;
         rewrite den_VPu, Z.add_mod_idemp_r by (unfold two64; lia); f_equal; lia.
Qed.

Lemma anchor_norm_sound : forall f, fact_holds E f -> fact_holds E (anchor_norm f).
Proof.
  intros f Hf.
  assert (KEY : forall a b k o o' y,
            anchored k a = Some (o, None) -> anchored k b = Some (o', Some y) ->
            (den E a = den E b <-> den E y = den E (VL (wsub o o')))).
  { intros a b k o o' y Ha Hb.
    pose proof (anchored_sound k a o None Ha) as A. pose proof (anchored_sound k b o' (Some y) Hb) as B. cbn in A, B.
    pose proof (bv_unsigned_in_range _ (den E y)) as Ry. rewrite bv_modulus_64 in Ry.
    pose proof (bv_unsigned_in_range _ (ev E k)) as Rk. rewrite bv_modulus_64 in Rk.
    pose proof (w2Z_range o) as Ro. pose proof (w2Z_range o') as Ro'.
    assert (L : bv_unsigned (den E (VL (wsub o o'))) = (w2Z o - w2Z o') mod two64) by (cbn [den]; rewrite wbv_unsigned; apply wsub_ok).
    split; intros H.
    - apply bv_eq. rewrite L. apply (f_equal bv_unsigned) in H. rewrite A, B in H. rewrite Z.add_0_r in H.
      unfold two64 in *.
      apply (Z.mod_unique_pos _ _ ((bv_unsigned (ev E k) + w2Z o) / 18446744073709551616 - (bv_unsigned (ev E k) + w2Z o' + bv_unsigned (den E y)) / 18446744073709551616)); [lia|].
      pose proof (Z.div_mod (bv_unsigned (ev E k) + w2Z o) 18446744073709551616 ltac:(lia)).
      pose proof (Z.div_mod (bv_unsigned (ev E k) + w2Z o' + bv_unsigned (den E y)) 18446744073709551616 ltac:(lia)). lia.
    - apply bv_eq. rewrite A, B. apply (f_equal bv_unsigned) in H. rewrite L in H. rewrite Z.add_0_r.
      unfold two64 in *.
      pose proof (Z.div_mod (w2Z o - w2Z o') 18446744073709551616 ltac:(lia)).
      pose proof (Z.mod_pos_bound (w2Z o - w2Z o') 18446744073709551616 ltac:(lia)).
      replace (bv_unsigned (ev E k) + w2Z o' + bv_unsigned (den E y))
        with ((bv_unsigned (ev E k) + w2Z o) + (-((w2Z o - w2Z o') / 18446744073709551616)) * 18446744073709551616) by lia.
      rewrite Z.mod_add; [reflexivity| lia]. }
  assert (KEY2 : forall a b k o o' y y',
            anchored k a = Some (o, Some y) -> anchored k b = Some (o', Some y') -> weqb o o' = true ->
            (den E a = den E b <-> den E y = den E y')).
  { intros a b k o o' y y' Ha Hb Ho. apply (proj1 (weqb_ok _ _)) in Ho.
    pose proof (anchored_sound k a o (Some y) Ha) as A. pose proof (anchored_sound k b o' (Some y') Hb) as B. cbn in A, B.
    pose proof (bv_unsigned_in_range _ (den E y)) as Ry. rewrite bv_modulus_64 in Ry.
    pose proof (bv_unsigned_in_range _ (den E y')) as Ry'. rewrite bv_modulus_64 in Ry'.
    pose proof (bv_unsigned_in_range _ (ev E k)) as Rk. rewrite bv_modulus_64 in Rk. pose proof (w2Z_range o) as Ro.
    rewrite <- Ho in B. split; intros H.
    - apply bv_eq. apply (f_equal bv_unsigned) in H. rewrite A, B in H. unfold two64 in *.
      pose proof (Z.div_mod (bv_unsigned (ev E k) + w2Z o + bv_unsigned (den E y)) 18446744073709551616 ltac:(lia)).
      pose proof (Z.div_mod (bv_unsigned (ev E k) + w2Z o + bv_unsigned (den E y')) 18446744073709551616 ltac:(lia)).
      pose proof (Z.mod_pos_bound (bv_unsigned (ev E k) + w2Z o + bv_unsigned (den E y)) 18446744073709551616 ltac:(lia)).
      pose proof (Z.mod_pos_bound (bv_unsigned (ev E k) + w2Z o + bv_unsigned (den E y')) 18446744073709551616 ltac:(lia)). nia.
    - apply bv_eq. rewrite A, B, H. reflexivity. }
  unfold anchor_norm.
  destruct f as [| | | |a b|a b| |]; try exact Hf; cbn [fact_holds] in Hf |- *;
    (destruct (anchor_of a) as [k|]; [|exact Hf]);
    (destruct (anchored k a) as [[o [ya|]]|] eqn:Ha; [| |exact Hf]);
    (destruct (anchored k b) as [[o' [yb|]]|] eqn:Hb; try exact Hf); cbn [fact_holds].
  all: try (destruct (weqb o o') eqn:Ho; [|exact Hf]; cbn [fact_holds]).
  - apply (proj1 (KEY2 a b k o o' ya yb Ha Hb Ho)). exact Hf.
  - apply (proj1 (KEY b a k o' o ya Hb Ha)). symmetry. exact Hf.
  - apply (proj1 (KEY a b k o o' yb Ha Hb)). exact Hf.
  - intros X. apply Hf. exact (proj2 (KEY2 a b k o o' ya yb Ha Hb Ho) X).
  - intros X. apply Hf. symmetry. exact (proj2 (KEY b a k o' o ya Hb Ha) X).
  - intros X. apply Hf. exact (proj2 (KEY a b k o o' yb Ha Hb) X).
Qed.

Lemma fact_bounds_sound : forall fs' v b, facts_hold E fs' -> inb (U v) b -> inb (U v) (fact_bounds fs' v b).
Proof.
  induction fs' as [|f fs' IH]; intros v b Hf Hb; [exact Hb|].
  apply Forall_cons_iff in Hf as [Hf1 Hf']. cbn [fact_bounds]. apply IH; [exact Hf'|].
  apply fact_bnd1_sound; [apply anchor_norm_sound|]; assumption.
Qed.
Lemma bnd_add_sound x y bx by_ : 0 <= x < two64 -> 0 <= y < two64 -> inb x bx -> inb y by_ ->
  inb ((x + y) mod two64) (bnd_add bx by_)
  /\ (bnd_add bx by_ <> full_bnd -> x + y < two64).
Proof.
  intros Rx Ry Hx Hy. destruct bx as [lx hx]; destruct by_ as [ly hy]. unfold inb in Hx, Hy; cbn [fst snd] in Hx, Hy.
  unfold bnd_add. destruct (add_carries hx hy) eqn:C.
  - split; [apply full_ok; apply Z.mod_pos_bound; unfold two64; lia|intros A; exfalso; apply A; reflexivity].
  - assert (NC : ~ two64 <= w2Z hx + w2Z hy) by (rewrite <- add_carries_iff, C; discriminate).
    pose proof (w2Z_range lx). pose proof (w2Z_range ly).
    assert (S : x + y < two64) by lia.
    split; [|intros _; exact S].
    unfold inb; cbn [fst snd]. rewrite Z.mod_small by lia. rewrite !wadd_ok, !Z.mod_small by lia. lia.
Qed.

Lemma bnd_sub_sound x y bx by_ : 0 <= x < two64 -> 0 <= y < two64 -> inb x bx -> inb y by_ ->
  inb ((x - y) mod two64) (bnd_sub bx by_)
  /\ (bnd_sub bx by_ <> full_bnd -> 0 <= x - y).
Proof.
  intros Rx Ry Hx Hy. destruct bx as [lx hx]; destruct by_ as [ly hy]. unfold inb in Hx, Hy; cbn [fst snd] in Hx, Hy.
  unfold bnd_sub. rewrite wltu_w2Z. destruct (Z.ltb_spec (w2Z lx) (w2Z hy)).
  - split; [apply full_ok; apply Z.mod_pos_bound; unfold two64; lia|intros A; exfalso; apply A; reflexivity].
  - pose proof (w2Z_range hx). pose proof (w2Z_range ly).
    split; [|intros _; lia].
    unfold inb; cbn [fst snd]. rewrite Z.mod_small by lia. rewrite !wsub_ok, !Z.mod_small by lia. lia.
Qed.

Lemma bnd_addv_sound (rec : sv -> bnd) x y : inb (U x) (rec x) -> inb (U y) (rec y) ->
  inb ((U x + U y) mod two64) (bnd_addv rec x y).
Proof.
  intros Hx Hy. pose proof (U_range x) as Rx. pose proof (U_range y) as Ry. unfold bnd_addv.
  destruct y as [c| | | | | | | | | |]; try exact (proj1 (bnd_add_sound _ _ _ _ Rx Ry Hx Hy)).
  rewrite den_VL in *. pose proof (w2Z_range c) as Rc. destruct (wt c) eqn:T.
  - pose proof (w2Z_wt c) as Tc. rewrite T in Tc. symmetry in Tc. apply Z.leb_le in Tc.
    assert (N : w2Z (wneg c) = two64 - w2Z c).
    { unfold wneg. rewrite wsub_ok, wzero_ok. unfold two63, two64 in *. symmetry. apply Z.mod_unique_pos with (q := -1); lia. }
    replace (U x + w2Z c) with ((U x - (two64 - w2Z c)) + 1 * two64) by lia. rewrite Z.mod_add by (unfold two64; lia).
    apply (proj1 (bnd_sub_sound (U x) (two64 - w2Z c) (rec x) (wneg c, wneg c) Rx ltac:(unfold two63, two64 in *; lia) Hx ltac:(unfold inb; cbn [fst snd]; lia))).
  - apply (proj1 (bnd_add_sound (U x) (w2Z c) (rec x) (c, c) Rx Ry Hx ltac:(unfold inb; cbn [fst snd]; lia))).
Qed.

Lemma bnd_below_cases b lim d : (bnd_below b lim d = b /\ w2Z (snd b) < w2Z lim) \/ bnd_below b lim d = d.
Proof. unfold bnd_below. rewrite wltu_w2Z. destruct (Z.ltb_spec (w2Z (snd b)) (w2Z lim)); [left; split; [reflexivity|lia]|right; reflexivity]. Qed.

Lemma bit31w_val : w2Z bit31w = 2 ^ 31. Proof. reflexivity. Qed.
Lemma bit32w_val : w2Z bit32w = 2 ^ 32. Proof. reflexivity. Qed.

Lemma ext_lim_val sx n : 0 < to_Z n < 8 -> w2Z (ext_lim sx n) = 2 ^ (8 * to_Z n - (if sx then 1 else 0)).
Proof.
  intros Hn. unfold ext_lim, w2Z; cbn [wt wl].
  rewrite Uint63.lsl_spec, Uint63.sub_spec, Uint63.lsl_spec.
  change (to_Z 1%uint63) with 1. change (to_Z 3%uint63) with 3. change wB with (2^63).
  replace (to_Z n * 2 ^ 3) with (8 * to_Z n) by (change (2^3) with 8; lia).
  rewrite (Z.mod_small (8 * to_Z n)) by lia.
  set (e := 8 * to_Z n - to_Z (if sx then 1%uint63 else 0%uint63)).
  assert (He : 0 <= e <= 56) by (subst e; destruct sx; [change (to_Z 1%uint63) with 1|change (to_Z 0%uint63) with 0]; lia).
  rewrite (Z.mod_small e) by lia.
  assert (2 ^ e <= 2 ^ 56) by (apply Z.pow_le_mono_r; lia). assert (0 < 2 ^ e) by (apply Z.pow_pos_nonneg; lia).
  rewrite Z.mul_1_l, Z.mod_small by (change (2^63) with (2^56*2^7); lia).
  subst e. destruct sx; [change (to_Z 1%uint63) with 1|change (to_Z 0%uint63) with 0]; f_equal; lia.
Qed.

Lemma ext_Z_small_id (sx : bool) (n z : Z) : 0 < n -> z < two64 -> 0 <= z < 2 ^ (8 * n - (if sx then 1 else 0)) -> ext_Z sx 0 n z = z.
Proof.
  intros Hn Hz64 Hz0. unfold ext_Z. rewrite Z.mul_0_r, Z.pow_0_r, Z.div_1_r.
  assert (P : 2 ^ (8 * n - 1) <= 2 ^ (8 * n)) by (apply Z.pow_le_mono_r; lia).
  destruct sx.
  - rewrite (Z.mod_small z (2 ^ (8 * n))) by lia.
    destruct (Z.leb_spec (2 ^ (8 * n - 1)) z); [lia|]. apply Z.mod_small. lia.
  - rewrite Z.sub_0_r in Hz0. apply Z.mod_small. lia.
Qed.

Lemma sv_bounds_unfold v : sv_bounds fs v =
  (let b0 := bnd_struct (sv_bounds fs) fs v in
   match v with
   | VL _ => b0
   | VP k o =>
       if weqb o wzero then var_bounds fs k
       else let b1 := fact_bounds fs v (fact_bounds fs v b0) in
            match bnd_shift (var_bounds fs k) o with Some bs => bnd_meet b1 bs | None => b1 end
   | _ => fact_bounds fs v (fact_bounds fs v b0)
   end).
Proof. destruct v; reflexivity. Qed.

Lemma w2Z_mod_pow2 (h : w64) (m : Z) : 0 <= m <= 62 -> w2Z h mod 2 ^ m = to_Z (wl h) mod 2 ^ m.
Proof.
  intros Hm. unfold w2Z. destruct (wt h).
  - replace two63 with (2 ^ (63 - m) * 2 ^ m) by (rewrite <- Z.pow_add_r by lia; replace (63 - m + m) with 63 by lia; reflexivity).
    rewrite Z.add_comm, Z.mod_add by (apply Z.pow_nonzero; lia). reflexivity.
  - rewrite Z.add_0_l. reflexivity.
Qed.

Lemma align_bnd_sound : forall k b, inb (U (VP k wzero)) b -> inb (U (VP k wzero)) (align_bnd fs k b).
Proof.
  intros k [lo hi] Hb. unfold align_bnd.
  destruct (PrimInt63.ltb 0 (find_align fs k) && PrimInt63.leb (find_align fs k) 62) eqn:C; [|exact Hb].
  apply andb_prop in C as [C1 C2]. apply Uint63.ltb_spec in C1. apply Uint63.leb_spec in C2.
  change (to_Z 0%uint63) with 0 in C1. change (to_Z 62%uint63) with 62 in C2.
  set (m := find_align fs k) in *.
  pose proof (find_align_sound k) as AL. fold m in AL.
  assert (XV : U (VP k wzero) = bv_unsigned (ev E k)).
  { rewrite den_VP. change (w2Zs wzero) with 0. rewrite Z.add_0_r. apply Z.mod_small. apply evk_range. }
  rewrite <- XV in AL.
  set (x := U (VP k wzero)) in *. set (M := 2 ^ to_Z m) in *.
  assert (MP : 0 < M) by (subst M; apply Z.pow_pos_nonneg; lia).
  assert (M62 : M <= 2 ^ 62) by (subst M; apply Z.pow_le_mono_r; lia).
  unfold inb in Hb |- *; cbn [fst snd] in Hb |- *. destruct Hb as [Hlo Hhi].
  pose proof (w2Z_range lo) as Rlo. pose proof (w2Z_range hi) as Rhi.
  assert (MK : to_Z (PrimInt63.sub (PrimInt63.lsl 1 m) 1) = M - 1) by (subst M; apply to_Z_mk; lia).
  assert (RH : to_Z (PrimInt63.land (wl hi) (PrimInt63.sub (PrimInt63.lsl 1 m) 1)) = w2Z hi mod M).
  { rewrite land_mk by lia. subst M. rewrite w2Z_mod_pow2 by lia. reflexivity. }
  assert (RL : to_Z (PrimInt63.land (wl lo) (PrimInt63.sub (PrimInt63.lsl 1 m) 1)) = w2Z lo mod M).
  { rewrite land_mk by lia. subst M. rewrite w2Z_mod_pow2 by lia. reflexivity. }
  pose proof (Z.mod_pos_bound (w2Z hi) M MP) as BH. pose proof (Z.mod_pos_bound (w2Z lo) M MP) as BL.
  pose proof (Z.div_mod (w2Z hi) M ltac:(lia)) as DH. pose proof (Z.div_mod (w2Z lo) M ltac:(lia)) as DL.
  pose proof (Z.div_mod x M ltac:(lia)) as DX. rewrite AL, Z.add_0_r in DX.
  assert (WL : forall i, w2Z {| wt := false; wl := i |} = to_Z i) by (intros i; unfold w2Z; cbn [wt wl]; lia).
  split.
  2: { rewrite wsub_ok, WL, RH. rewrite Z.mod_small by lia.
       assert (x / M <= w2Z hi / M) by (apply Z.div_le_mono; lia). nia. }
  destruct (PrimInt63.eqb _ 0%uint63) eqn:R0; [exact Hlo|].
  match goal with |- w2Z (if ?c then _ else _) <= _ => destruct c eqn:OV; [exact Hlo|] end.
  rewrite wltu_w2Z in OV. apply Z.ltb_ge in OV. revert OV.
  rewrite !wadd_ok, !WL, Uint63.sub_spec, Uint63.lsl_spec, RL. change (to_Z 1%uint63) with 1. rewrite Z.mul_1_l.
  assert (P63 : 2 ^ to_Z m < wB) by (change wB with (2^63); apply Z.pow_lt_mono_r; lia).
  rewrite (Z.mod_small (2 ^ to_Z m) wB) by lia. fold M.
  rewrite (Z.mod_small (M - w2Z lo mod M) wB) by (change wB with (2^63) in *; lia).
  assert (NZ : w2Z lo mod M <> 0).
  { intros Z0. apply Uint63.eqb_false_spec in R0. apply R0. apply Uint63.to_Z_inj. rewrite RL, Z0. reflexivity. }
  intros OV.
  destruct (Z_lt_le_dec (w2Z lo + (M - w2Z lo mod M)) two64) as [LT|GE].
  - rewrite Z.mod_small in OV |- * by lia.
    assert (w2Z lo / M < x / M) by nia. nia.
  - exfalso. revert OV. unfold two64 in *.
    replace (w2Z lo + (M - w2Z lo mod M)) with ((w2Z lo + (M - w2Z lo mod M) - 2^64) + 1 * 2^64) by lia.
    rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. lia.
Qed.

Lemma Z_to_bv64_small z : 0 <= z < two64 -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros. rewrite Z_to_bv_unsigned. apply bv_wrap_small. rewrite bv_modulus_64. exact H. Qed.

Lemma wadd_signed_nowrap a off : 0 <= w2Z a + w2Zs off < two64 -> w2Z (wadd a off) = w2Z a + w2Zs off.
Proof.
  intros H. pose proof (w2Z_range a). pose proof (w2Z_range off).
  rewrite wadd_ok, (w2Z_of_w2Zs off). destruct (wt off).
  - replace (w2Z a + (w2Zs off + 1 * two64)) with ((w2Z a + w2Zs off) + 1 * two64) by lia.
    rewrite Z.mod_add by (unfold two64; lia). apply Z.mod_small. lia.
  - rewrite Z.mul_0_l, Z.add_0_r. apply Z.mod_small. lia.
Qed.

Lemma bnd_meet_sound z x y : inb z x -> inb z y -> inb z (bnd_meet x y).
Proof. intros [A B] [C D]. unfold bnd_meet, inb; cbn [fst snd]. split; [apply wmaxu_lub; assumption| apply wminu_glb; assumption]. Qed.

Lemma bnd_shift_sound k o b b' : inb (U (VP k wzero)) b -> bnd_shift b o = Some b' -> inb (U (VP k o)) b'.
Proof.
  intros Hb H. unfold bnd_shift in H. destruct b as [lo hi]. cbn [fst snd] in H.
  destruct (nowrap lo hi o && wleu lo hi) eqn:C; [|discriminate H]. injection H as <-.
  apply andb_prop in C as [NW LEQ]. apply nowrap_sound in NW. rewrite wleu_w2Z in LEQ. apply Z.leb_le in LEQ.
  unfold inb in Hb |- *; cbn [fst snd] in *.
  assert (XV : U (VP k wzero) = bv_unsigned (ev E k)).
  { rewrite den_VP. change (w2Zs wzero) with 0. rewrite Z.add_0_r. apply Z.mod_small. apply evk_range. }
  rewrite XV in Hb. rewrite den_VP.
  pose proof (w2Z_range lo). pose proof (w2Z_range hi). pose proof (w2Z_range o). pose proof (evk_range k).
  rewrite Z.mod_small by lia. rewrite !wadd_signed_nowrap by lia. lia.
Qed.

Lemma VP_struct_sound k off : inb (U (VP k off)) (bnd_struct (sv_bounds fs) fs (VP k off)).
Proof.
  cbn [bnd_struct].
  destruct (find_range fs k) as [[lo hi]|] eqn:R; [|apply full_ok; apply U_range].
  destruct (nowrap lo hi off) eqn:NW; [|apply full_ok; apply U_range].
  pose proof (find_range_sound k lo hi R) as FR. apply nowrap_sound in NW.
  unfold inb; cbn [fst snd]. rewrite den_VP.
  pose proof (w2Z_range lo). pose proof (w2Z_range hi). pose proof (w2Z_range off).
  rewrite Z.mod_small by lia.
  rewrite !wadd_signed_nowrap by lia. lia.
Qed.

Lemma var_bounds_sound k : inb (U (VP k wzero)) (var_bounds fs k).
Proof.
  unfold var_bounds. apply align_bnd_sound. apply fact_bounds_sound; [exact Hfs|]. apply fact_bounds_sound; [exact Hfs|].
  pose proof (VP_struct_sound k wzero) as P. cbn [bnd_struct] in P |- *. exact P.
Qed.

Lemma nowrap_kb_sound : forall k o, nowrap_kb fs k o = true ->
  0 <= bv_unsigned (ev E k) + w2Zs o < two64
  /\ bv_unsigned (den E (VP k o)) = bv_unsigned (ev E k) + w2Zs o.
Proof.
  intros k o H. unfold nowrap_kb in H. apply Bool.orb_true_iff in H as [H|H]; [exact (nowrap_k_sound k o H)|].
  destruct (var_bounds fs k) as [lo hi] eqn:VB. apply nowrap_sound in H.
  pose proof (var_bounds_sound k) as IB. rewrite VB in IB. unfold inb in IB; cbn [fst snd] in IB.
  pose proof (evk_range k) as EK. rewrite den_VPu, wzero_ok, Z.add_0_r, Z.mod_small in IB by lia.
  split; [lia|]. rewrite den_VP. apply Z.mod_small. lia.
Qed.

Lemma sv_bounds_sound : forall v, inb (U v) (sv_bounds fs v).
Proof.
  induction v; rewrite sv_bounds_unfold; cbv zeta;
    lazymatch goal with
    | |- inb _ (fact_bounds _ _ (fact_bounds _ _ _)) => apply fact_bounds_sound; [exact Hfs|]; apply fact_bounds_sound; [exact Hfs|]
    | |- _ => idtac
    end; cbn [bnd_struct].
  -   unfold inb; cbn [fst snd]. rewrite den_VL. lia.
  -
    destruct (weqb off wzero) eqn:W0.
    + apply weqb_eq in W0. subst off. apply var_bounds_sound.
    + assert (FB : inb (U (VP k off)) (fact_bounds fs (VP k off) (fact_bounds fs (VP k off) (bnd_struct (sv_bounds fs) fs (VP k off))))).
      { apply fact_bounds_sound; [exact Hfs|]. apply fact_bounds_sound; [exact Hfs|]. apply VP_struct_sound. }
      cbn [bnd_struct] in FB.
      destruct (bnd_shift (var_bounds fs k) off) as [bs|] eqn:SH; [|exact FB].
      apply bnd_meet_sound; [exact FB|]. exact (bnd_shift_sound k off _ _ (var_bounds_sound k) SH).
  -
    pose proof (U_range v1) as R1. pose proof (U_range v2) as R2.
    destruct op.
    +   cbn [den alu64 alu]. rewrite bv_add_unsigned. unfold bv_wrap. rewrite bv_modulus_64.
      exact (bnd_addv_sound _ _ _ IHv1 IHv2).
    +   cbn [den alu64 alu]. rewrite bv_sub_unsigned. unfold bv_wrap. rewrite bv_modulus_64.
      exact (proj1 (bnd_sub_sound _ _ _ _ R1 R2 IHv1 IHv2)).
    +   destruct v2 as [s| | | | | | | | | |]; try (apply full_ok; apply U_range).
      destruct (sv_bounds fs v1) as [l h] eqn:B1. unfold inb in IHv1; cbn [fst snd] in IHv1.
      rewrite wleu_w2Z. destruct (Z.leb_spec (w2Z h) (w2Z (wsrl wones s))); [|apply full_ok; apply U_range].
      unfold inb; cbn [fst snd]. cbn [den alu64 alu].
      rewrite bv_shiftl_unsigned, shamt6_bv, Z.shiftl_mul_pow2 by apply int_range.
      pose proof (shamt6_range s) as SR.
      unfold wsll, wsrl in *. rewrite wsrl_k_ok in H by lia. change (w2Z wones) with (two64 - 1) in H.
      rewrite !wsll_k_ok by lia.
      assert (P : 0 < 2 ^ to_Z (shamt6 s)) by (apply Z.pow_pos_nonneg; lia).
      pose proof (Z.mul_div_le (two64 - 1) (2 ^ to_Z (shamt6 s)) ltac:(lia)) as MD.
      assert (HB : w2Z h * 2 ^ to_Z (shamt6 s) <= two64 - 1) by nia.
      pose proof (w2Z_range l). pose proof (w2Z_range h).
      unfold bv_wrap. rewrite bv_modulus_64. change (2^64) with two64.
      rewrite !Z.mod_small by nia. nia.
    +   unfold inb; cbn [fst snd den alu64 alu]. rewrite wzero_ok, wone_ok. destruct (bv_lts _ _); rewrite Z_to_bv64_small by (unfold two64; lia); lia.
    +   unfold inb; cbn [fst snd den alu64 alu]. rewrite wzero_ok, wone_ok. destruct (bv_ltu _ _); rewrite Z_to_bv64_small by (unfold two64; lia); lia.
    +   destruct (add_carries _ _) eqn:C; [apply full_ok; apply U_range|].
      assert (NC : ~ two64 <= w2Z (snd (sv_bounds fs v1)) + w2Z (snd (sv_bounds fs v2))) by (rewrite <- add_carries_iff, C; discriminate).
      unfold inb in IHv1, IHv2 |- *; cbn [fst snd]. cbn [den alu64 alu]. rewrite bv_xor_unsigned, wzero_ok.
      pose proof (Z.add_lxor_2land (U v1) (U v2)).
      pose proof (proj2 (Z.land_nonneg (U v1) (U v2)) (or_introl (proj1 R1))).
      pose proof (proj2 (Z.lxor_nonneg (U v1) (U v2)) ltac:(lia)).
      rewrite wadd_ok, Z.mod_small by (pose proof (w2Z_range (snd (sv_bounds fs v1))); pose proof (w2Z_range (snd (sv_bounds fs v2))); lia). lia.
    +   destruct v2 as [s| | | | | | | | | |]; try (apply full_ok; apply U_range).
      destruct (sv_bounds fs v1) as [l h] eqn:B1. unfold inb in IHv1; cbn [fst snd] in IHv1.
      unfold inb; cbn [fst snd]. cbn [den alu64 alu].
      rewrite bv_shiftr_unsigned, shamt6_bv, Z.shiftr_div_pow2 by apply int_range.
      pose proof (shamt6_range s) as SR. unfold wsrl. rewrite !wsrl_k_ok by lia.
      assert (P : 0 < 2 ^ to_Z (shamt6 s)) by (apply Z.pow_pos_nonneg; lia).
      split; apply Z.div_le_mono; lia.
    +   apply full_ok; apply U_range.
    +   destruct (add_carries _ _) eqn:C; [apply full_ok; apply U_range|].
      assert (NC : ~ two64 <= w2Z (snd (sv_bounds fs v1)) + w2Z (snd (sv_bounds fs v2))) by (rewrite <- add_carries_iff, C; discriminate).
      unfold inb in IHv1, IHv2 |- *; cbn [fst snd]. cbn [den alu64 alu]. rewrite bv_or_unsigned, wzero_ok.
      pose proof (Z.add_lor_land (U v1) (U v2)).
      pose proof (proj2 (Z.land_nonneg (U v1) (U v2)) (or_introl (proj1 R1))).
      pose proof (proj2 (Z.lor_nonneg (U v1) (U v2)) (conj (proj1 R1) (proj1 R2))).
      rewrite wadd_ok, Z.mod_small by (pose proof (w2Z_range (snd (sv_bounds fs v1))); pose proof (w2Z_range (snd (sv_bounds fs v2))); lia). lia.
    +   unfold inb in IHv1, IHv2 |- *; cbn [fst snd]. cbn [den alu64 alu]. rewrite bv_and_unsigned, wzero_ok.
      pose proof (proj2 (Z.land_nonneg (U v1) (U v2)) (or_introl (proj1 R1))).
      pose proof (land_le_l (U v1) (U v2) (proj1 R1) (proj1 R2)). pose proof (land_le_r (U v1) (U v2) (proj1 R1) (proj1 R2)).
      split; [lia|]. apply wminu_glb; lia.
  -
    pose proof (U_range v1) as R1. pose proof (U_range v2) as R2.
    assert (SX : forall z, 0 <= z < 2 ^ 31 -> sx32Z z = z).
    { intros z Hz0. unfold sx32Z. destruct (Z.leb_spec (2 ^ 31) z); [lia|reflexivity]. }
    destruct op; try (apply full_ok; apply U_range).
    +   destruct (bnd_below_cases (bnd_addv (sv_bounds fs) v1 v2) bit31w full_bnd) as [[EQ HB]|EQ]; rewrite EQ; [|apply full_ok; apply U_range].
      pose proof (bnd_addv_sound _ _ _ IHv1 IHv2) as IB. rewrite bit31w_val in HB.
      unfold inb in IB |- *. cbn [den alu32 alu]. rewrite sext32_unsigned, bv_add_unsigned, !low32_ext.
      unfold bv_wrap. change (bv_modulus 32) with (2^32). rewrite <- Z.add_mod by lia.
      rewrite <- (mod64_mod (U v1 + U v2) 32) by lia.
      pose proof (Z.mod_pos_bound (U v1 + U v2) two64 ltac:(unfold two64; lia)).
      rewrite (Z.mod_small _ (2^32)) by lia. rewrite SX by lia. exact IB.
    +   destruct (bnd_below_cases (bnd_sub (sv_bounds fs v1) (sv_bounds fs v2)) bit31w full_bnd) as [[EQ HB]|EQ]; rewrite EQ; [|apply full_ok; apply U_range].
      pose proof (proj1 (bnd_sub_sound _ _ _ _ R1 R2 IHv1 IHv2)) as IB. rewrite bit31w_val in HB.
      unfold inb in IB |- *. cbn [den alu32 alu]. rewrite sext32_unsigned, bv_sub_unsigned, !low32_ext.
      unfold bv_wrap. change (bv_modulus 32) with (2^32). rewrite <- Zminus_mod by lia.
      rewrite <- (mod64_mod (U v1 - U v2) 32) by lia.
      pose proof (Z.mod_pos_bound (U v1 - U v2) two64 ltac:(unfold two64; lia)).
      rewrite (Z.mod_small _ (2^32)) by lia. rewrite SX by lia. exact IB.
  -
    pose proof (U_range v1) as R1. pose proof (U_range v2) as R2.
    destruct op; try (apply full_ok; apply U_range).
    destruct (sv_bounds fs v1) as [lx hx] eqn:B1. destruct (sv_bounds fs v2) as [ly hy] eqn:B2.
    unfold inb in IHv1, IHv2; cbn [fst snd] in IHv1, IHv2.
    rewrite !wltu_w2Z, bit32w_val.
    destruct (Z.ltb_spec (w2Z hx) (2 ^ 32)); [|apply full_ok; apply U_range].
    destruct (Z.ltb_spec (w2Z hy) (2 ^ 32)); [|apply full_ok; apply U_range]. cbn [andb].
    unfold inb; cbn [fst snd]. cbn [den mul_div]. rewrite bv_mul_unsigned. unfold bv_wrap. rewrite bv_modulus_64.
    pose proof (w2Z_range lx). pose proof (w2Z_range ly).
    assert (M1 : U v1 * U v2 <= w2Z hx * w2Z hy) by nia.
    assert (M2 : w2Z hx * w2Z hy < two64) by (unfold two64; change (2^64) with (2^32 * 2^32); nia).
    assert (M3 : w2Z lx * w2Z ly <= U v1 * U v2) by nia.
    rewrite !wmul_ok, !Z.mod_small by nia. nia.
  -   apply full_ok; apply U_range.
  -
    pose proof (U_range v) as R1.
    assert (DF : forall lo', inb (U (VExt sx lo' n v)) (if sx then full_bnd else match umax_of_width n with Some m => (wzero, m) | None => full_bnd end)).
    { intros lo'. destruct sx; [apply full_ok; apply U_range|].
      destruct (umax_of_width n) as [m|] eqn:UM; [|apply full_ok; apply U_range].
      apply umax_of_width_sound in UM as [Hr Hm]. unfold inb; cbn [fst snd]. rewrite wzero_ok, Hm.
      cbn [den]. unfold ext_word. pose proof (ext_Z_false_lt (to_Z lo') (to_Z n) (U v) ltac:(lia)) as EB.
      assert (2 ^ (8 * to_Z n) <= 2 ^ 56) by (apply Z.pow_le_mono_r; lia).
      rewrite Z_to_bv64_small by (unfold two64; change (2^64) with (2^56 * 2^8); lia). lia. }
    destruct (PrimInt63.eqb lo 0) eqn:L0; cbn [andb].
    + apply int_eqb_eq in L0. subst lo.
      destruct (PrimInt63.eqb n 8) eqn:N8.
      { apply int_eqb_eq in N8. subst n. cbn [den]. change (to_Z 0%uint63) with 0. change (to_Z 8%uint63) with 8.
        rewrite ext_word_id64. exact IHv. }
      destruct (PrimInt63.ltb 0 n) eqn:N0; cbn [andb]; [|apply full_ok; apply U_range].
      destruct (PrimInt63.ltb n 8) eqn:N8'; [|apply full_ok; apply U_range].
      apply Uint63.ltb_spec in N0. apply Uint63.ltb_spec in N8'. change (to_Z 0%uint63) with 0 in N0. change (to_Z 8%uint63) with 8 in N8'.
      destruct (bnd_below_cases (sv_bounds fs v) (ext_lim sx n) (if sx then full_bnd else match umax_of_width n with Some m => (wzero, m) | None => full_bnd end)) as [[EQ HB]|EQ]; rewrite EQ; [|apply DF].
      rewrite ext_lim_val in HB by lia. unfold inb in IHv |- *.
      cbn [den]. unfold ext_word. change (to_Z 0%uint63) with 0.
      assert (P : 2 ^ (8 * to_Z n - (if sx then 1 else 0)) <= 2 ^ 56) by (apply Z.pow_le_mono_r; destruct sx; lia).
      rewrite ext_Z_small_id by (unfold two64 in *; lia).
      rewrite Z_to_bv64_small by lia. exact IHv.
    + destruct (PrimInt63.ltb 0 n && PrimInt63.ltb n 8); [apply DF|apply full_ok; apply U_range].
  -   apply full_ok; apply U_range.
  -   destruct sx; [apply full_ok; apply U_range|].
    destruct (umax_of_width n) as [m|] eqn:UM; [|apply full_ok; apply U_range].
    apply umax_of_width_sound in UM as [Hr Hm]. unfold inb; cbn [fst snd]. rewrite wzero_ok, Hm.
    cbn [den]. unfold bytes_val.
    match goal with |- context [ext_Z false 0 ?n ?z] => pose proof (ext_Z_false_lt 0 n z ltac:(lia)) as EB end.
    assert (2 ^ (8 * to_Z n) <= 2 ^ 56) by (apply Z.pow_le_mono_r; lia).
    rewrite Z_to_bv64_small by (unfold two64; change (2^64) with (2^56 * 2^8); lia). lia.
  -   destruct sx; [apply full_ok; apply U_range|].
    destruct (umax_of_width n) as [m|] eqn:UM; [|apply full_ok; apply U_range].
    apply umax_of_width_sound in UM as [Hr Hm]. unfold inb; cbn [fst snd]. rewrite wzero_ok, Hm.
    cbn [den]. unfold bytes_val.
    match goal with |- context [ext_Z false 0 ?n ?z] => pose proof (ext_Z_false_lt 0 n z ltac:(lia)) as EB end.
    assert (2 ^ (8 * to_Z n) <= 2 ^ 56) by (apply Z.pow_le_mono_r; lia).
    rewrite Z_to_bv64_small by (unfold two64; change (2^64) with (2^56 * 2^8); lia). lia.
  -   apply full_ok; apply U_range.
Qed.

Lemma bnd_ltu_sound a b r : bnd_ltu fs a b = Some r -> bv_ltu (den E a) (den E b) = r.
Proof.
  unfold bnd_ltu. pose proof (sv_bounds_sound a) as A. pose proof (sv_bounds_sound b) as B.
  destruct (sv_bounds fs a) as [la ha]. destruct (sv_bounds fs b) as [lb hb]. unfold inb in A, B; cbn [fst snd] in A, B.
  rewrite wltu_w2Z, wleu_w2Z. intros H. apply ltu_iff.
  destruct (Z.ltb_spec (w2Z ha) (w2Z lb)); [injection H as <-; lia|].
  destruct (Z.leb_spec (w2Z hb) (w2Z la)); [injection H as <-; lia|discriminate H].
Qed.

Lemma bnd_eq0_sound v r : bnd_eq0 fs v = Some r -> bv_eqb (den E v) (Z_to_bv 64 0) = r.
Proof.
  unfold bnd_eq0. pose proof (sv_bounds_sound v) as A.
  destruct (sv_bounds fs v) as [l h]. unfold inb in A; cbn [fst snd] in A.
  rewrite wltu_w2Z, wzero_ok. intros H. apply eqb_iff.
  destruct (Z.ltb_spec 0 (w2Z l)).
  - injection H as <-. intros EQ. apply (f_equal bv_unsigned) in EQ. rewrite Z_to_bv64_small in EQ by (unfold two64; lia). lia.
  - destruct (weqb h wzero) eqn:W; [|discriminate H]. injection H as <-. apply weqb_eq in W. subst h. rewrite wzero_ok in A.
    apply bv_eq. rewrite Z_to_bv64_small by (unfold two64; lia). pose proof (U_range v). lia.
Qed.

Lemma sv_bounds_hi v : bv_unsigned (den E v) <= w2Z (snd (sv_bounds fs v)).
Proof. pose proof (sv_bounds_sound v) as [_ H']. exact H'. Qed.
Lemma sv_bounds_lo v : w2Z (fst (sv_bounds fs v)) <= bv_unsigned (den E v).
Proof. pose proof (sv_bounds_sound v) as [H' _]. exact H'. Qed.

Lemma syntactic_eq_sound : forall a b,
  (fact_lookup fs (is_FNe a b) = true -> den E a <> den E b) /\
  (fact_lookup fs (is_FEq a b) = true -> den E a = den E b).
Proof.
  intros a b. split; intros H; vp_fact_cases Hfs H; (exact Hh || (symmetry; exact Hh) || (intros X; apply Hh; symmetry; exact X)).
Qed.

Lemma ptr_lit_ne : forall k o y lo hi,
  find_range fs k = Some (lo, hi) -> nowrap lo hi o = true ->
  wltu y (wadd lo o) || wltu (wadd hi o) y = true ->
  bv_unsigned (den E (VP k o)) <> w2Z y.
Proof.
  intros k o y lo hi Hr Hn Hc. apply find_range_sound in Hr. apply nowrap_sound in Hn.
  pose proof (w2Z_range lo). pose proof (w2Z_range hi). pose proof (w2Zs_range o).
  rewrite !wltu_w2Z, !wadd_ok, (w2Z_of_w2Zs o), !Z.add_assoc, !Z.mod_add, !Z.mod_small in Hc by (unfold two64 in *; lia).
  rewrite den_VP, Z.mod_small by lia.
  destruct (Z.ltb_spec (w2Z y) (w2Z lo + w2Zs o)), (Z.ltb_spec (w2Z hi + w2Zs o) (w2Z y)); cbn in Hc; lia.
Qed.

Lemma decide_eq0_s_sound : forall v r, decide_eq0_s fs v = Some r -> bv_eqb (den E v) (Z_to_bv 64 0) = r.
Proof.
  assert (Z0 : bv_unsigned (Z_to_bv 64 0) = 0) by reflexivity.
  assert (DZ : den E (VL wzero) = Z_to_bv 64 0) by reflexivity.
  assert (EQ0 : forall (w : word) (r : bool), (if r then bv_unsigned w = 0 else bv_unsigned w <> 0) -> bv_eqb w (Z_to_bv 64 0) = r).
  { intros w r Hr. apply eqb_iff. destruct r.
    - apply bv_eq. rewrite Z0. exact Hr.
    - intros X. apply Hr. rewrite X. exact Z0. }
  induction v; intros r H; cbn [decide_eq0_s] in H; fold decide_eq0_s in H.
  all: match type of H with (if fact_lookup fs ?p then _ else _) = _ =>
         destruct (fact_lookup fs p) eqn:FN;
         [ vp_bsplit; vp_fact_cases Hfs FN; rewrite ?DZ in Hh; apply EQ0; intros X;
           match goal with |- False => idtac end;
           match type of X with bv_unsigned ?w = 0 =>
             assert (XX : w = Z_to_bv 64 0) by (apply bv_eq; rewrite X; symmetry; exact Z0) end;
           congruence
         | clear FN ] end.
  all: match type of H with (if fact_lookup fs ?p then _ else _) = _ =>
         destruct (fact_lookup fs p) eqn:FE;
         [ vp_bsplit; vp_fact_cases Hfs FE; rewrite ?DZ in Hh; apply EQ0; first [rewrite Hh | rewrite <- Hh]; exact Z0 | clear FE ] end.
  all: try (destruct (sv_umax _) as [mx|] eqn:UM; [|discriminate H];
            destruct (weqb mx wzero) eqn:MZ; [|discriminate H]; vp_bsplit;
            apply weqb_eq in MZ; subst mx; pose proof (sv_umax_sound _ _ UM) as B; rewrite wzero_ok in B;
            apply EQ0; match goal with |- bv_unsigned ?w = 0 => pose proof (bvu_nonneg _ w); lia end).
  -   vp_bsplit. cbn [den]. unfold bv_eqb. rewrite wbv_unsigned, Z0, weqb_eqb, wzero_ok. reflexivity.
  -   destruct (find_range fs k) as [[lo hi]|] eqn:Hr; [|discriminate].
    destruct (nowrap lo hi off) eqn:Hn; [|discriminate].
    destruct (wltu wzero (wadd lo off)) eqn:Hc; [|discriminate]. vp_bsplit. apply EQ0.
    rewrite <- wzero_ok. apply (ptr_lit_ne k off wzero lo hi Hr Hn). rewrite Hc. reflexivity.
  -
    assert (XS : forall x y : word, (bv_unsigned (bv_xor x y) = 0 <-> x = y) /\ (bv_unsigned (bv_sub x y) = 0 <-> x = y)).
    { intros x y. split; split; intros X.
      - apply bv_eq. apply Z.lxor_eq. rewrite <- bv_xor_unsigned. exact X.
      - subst. rewrite bv_xor_unsigned, Z.lxor_nilpotent. reflexivity.
      - pose proof (bv_unsigned_in_range _ x). pose proof (bv_unsigned_in_range _ y).
        rewrite bv_sub_unsigned in X. unfold bv_wrap in X. apply bv_eq.
        apply Z.mod_divide in X; [|unfold bv_modulus; lia]. destruct X as [q Hq]. unfold bv_modulus in *.
        assert (q = 0) by nia. subst q. lia.
      - subst. rewrite bv_sub_unsigned, Z.sub_diag. reflexivity. }
    assert (CORE : forall x y (r : bool),
              (if sv_eqb x y then Some true
               else if fact_lookup fs (is_FNe x y) then Some false
               else if fact_lookup fs (is_FEq x y) then Some true
               else match x, y with
                    | VL a, VL b => Some (weqb a b)
                    | VP k1 o1, VP k2 o2 => if PrimInt63.eqb k1 k2 then Some (weqb o1 o2) else None
                    | _, VL b => if weqb b wzero then decide_eq0_s fs x else None
                    | _, _ => None
                    end) = Some r ->
              (forall r', decide_eq0_s fs x = Some r' -> bv_eqb (den E x) (Z_to_bv 64 0) = r') ->
              bv_eqb (den E x) (den E y) = r).
    { intros x y r0 HH IH.
      destruct (sv_eqb x y) eqn:SE. { apply sv_eqb_eq in SE. subst. vp_bsplit. apply eqb_iff. reflexivity. }
      pose proof (syntactic_eq_sound x y) as [S1 S2].
      destruct (fact_lookup fs (is_FNe x y)); [vp_bsplit; apply eqb_iff; apply S1; reflexivity|].
      destruct (fact_lookup fs (is_FEq x y)); [vp_bsplit; apply eqb_iff; apply S2; reflexivity|]. clear S1 S2.
      destruct x as [a|k1 o1| | | | | | | | |]; destruct y as [b|k2 o2| | | | | | | | |]; try discriminate HH.
      all: try (destruct (weqb b wzero) eqn:BZ; [|discriminate HH]; apply weqb_eq in BZ; subst b;
                rewrite DZ; exact (IH r0 HH)).
      + vp_bsplit. cbn [den]. unfold bv_eqb. rewrite !wbv_unsigned, weqb_eqb. reflexivity.
      + destruct (PrimInt63.eqb k1 k2) eqn:Hk; [|discriminate HH]. apply int_eqb_eq in Hk. subst k2. vp_bsplit.
        unfold bv_eqb. rewrite !den_VPu, weqb_eqb.
        pose proof (evk_range k1). pose proof (w2Z_range o1). pose proof (w2Z_range o2).
        destruct (Z.eqb_spec (w2Z o1) (w2Z o2)) as [X|X].
        * rewrite X. apply Z.eqb_refl.
        * apply Z.eqb_neq. intros Y. apply X. exact (mod_add_cancel_l _ _ _ H1 H2 Y). }
    destruct op; try discriminate H.
    all: try (destruct (sv_umax _) as [mx|] eqn:UM; [|discriminate H];
              destruct (weqb mx wzero) eqn:MZ; [|discriminate H]; vp_bsplit;
              apply weqb_eq in MZ; subst mx; pose proof (sv_umax_sound _ _ UM) as B; rewrite wzero_ok in B;
              apply EQ0; match goal with |- bv_unsigned ?w = 0 => pose proof (bvu_nonneg _ w); lia end).
    +   pose proof (CORE v1 v2 r H IHv1) as Q. apply EQ0. apply eqb_iff in Q. cbn [den alu64 alu].
      destruct r. * apply (proj2 (proj2 (XS _ _))). exact Q. * intros X. apply Q. apply (proj1 (proj2 (XS _ _))). exact X.
    +   pose proof (CORE v1 v2 r H IHv1) as Q. apply EQ0. apply eqb_iff in Q. cbn [den alu64 alu].
      destruct r. * apply (proj2 (proj1 (XS _ _))). exact Q. * intros X. apply Q. apply (proj1 (proj1 (XS _ _))). exact X.
Qed.

Lemma decide_eq0_b_sound : forall v r, decide_eq0_b fs v = Some r -> bv_eqb (den E v) (Z_to_bv 64 0) = r.
Proof.
  intros v r H. unfold decide_eq0_b in H.
  destruct (decide_eq0_s fs v) as [r'|] eqn:D; [injection H as <-; exact (decide_eq0_s_sound v r' D)|exact (bnd_eq0_sound v r H)].
Qed.

Definition ltu_generic (a b : sv) : option bool :=
      if sv_eqb a b then Some false
      else if fact_lookup fs (is_FULt a b) then Some true
      else if fact_lookup fs (is_FULe b a) || fact_lookup fs (is_FEq a b) then Some false
      else match a, b with
           | _, VL y =>
               if weqb y wzero then Some false else
               match (if weqb y wone then decide_eq0_b fs a else None) with
               | Some r => Some r
               | None =>
               match (match sv_umax a with Some m => wltu m y | None => false end) with
               | true => Some true
               | false =>
               match a with
               | VP k o => if weqb o wzero then
                             match find_range fs k with
                             | Some (lo, hi) => if wltu hi y then Some true
                                                else if wleu y lo then Some false
                                                else lookup_ltu_lit_r fs a y
                             | None => lookup_ltu_lit_r fs a y
                             end
                           else lookup_ltu_lit_r fs a y
               | _ => lookup_ltu_lit_r fs a y
               end
               end
               end
           | VL x, _ =>
               match (if weqb x wzero then option_map negb (decide_eq0_b fs b) else None) with
               | Some r => Some r
               | None =>
               match b with
               | VP k o => if weqb o wzero then
                             match find_range fs k with
                             | Some (lo, hi) => if wltu x lo then Some true
                                                else if wleu hi x then Some false
                                                else lookup_ltu_lit_l fs x b
                             | None => lookup_ltu_lit_l fs x b
                             end
                           else lookup_ltu_lit_l fs x b
               | _ => lookup_ltu_lit_l fs x b
               end
               end
           | _, _ => None
           end.

Lemma syntactic_ltu_sound : forall a b,
  (fact_lookup fs (is_FULt a b) = true -> bv_unsigned (den E a) < bv_unsigned (den E b)) /\
  (fact_lookup fs (is_FULe b a) || fact_lookup fs (is_FEq a b) = true -> bv_unsigned (den E b) <= bv_unsigned (den E a)).
Proof.
  intros a b. split; intros H.
  - vp_fact_cases Hfs H. exact Hh.
  - apply orb_prop in H. destruct H as [H|H]; vp_fact_cases Hfs H; rewrite ?Hh; lia.
Qed.

Lemma den_VP0 k o : weqb o wzero = true -> bv_unsigned (den E (VP k o)) = bv_unsigned (ev E k).
Proof. intros H. apply weqb_eq in H. subst. cbn [den]. rewrite bv_add_unsigned, wbv_unsigned, wzero_ok, Z.add_0_r. apply bv_wrap_bv_unsigned. Qed.

Lemma ltu_generic_sound : forall a b r, ltu_generic a b = Some r -> bv_ltu (den E a) (den E b) = r.
Proof.
  intros a b r H. unfold ltu_generic in H.
  destruct (sv_eqb a b) eqn:He.
  { vp_bsplit. apply ltu_iff. lia. }
  pose proof (syntactic_ltu_sound a b) as [S1 S2].
  destruct (fact_lookup fs (is_FULt a b)); [vp_bsplit; apply ltu_iff; apply S1; reflexivity|].
  destruct (fact_lookup fs (is_FULe b a) || fact_lookup fs (is_FEq a b)); [vp_bsplit; apply ltu_iff; apply S2; reflexivity|].
  clear S1 S2 He.
  assert (U : forall a' y, match sv_umax a' with Some m => wltu m y | None => false end = true ->
             bv_ltu (den E a') (den E (VL y)) = true).
  { intros a' y HU. destruct (sv_umax a') as [m|] eqn:Hm; [|discriminate].
    apply ltu_iff. rewrite den_VL. pose proof (sv_umax_sound _ _ Hm). rewrite wltu_w2Z in HU. apply Z.ltb_lt in HU. lia. }
  assert (U0 : forall a' y, weqb y wzero = true -> bv_ltu (den E a') (den E (VL y)) = false).
  { intros a' y Hy. apply weqb_eq in Hy. subst y. apply ltu_iff. rewrite den_VL, wzero_ok. pose proof (bv_unsigned_in_range _ (den E a')). lia. }
  assert (ONE : forall a' y r, weqb y wone = true -> decide_eq0_b fs a' = Some r -> bv_ltu (den E a') (den E (VL y)) = r).
  { intros a' y r0 Hy He. apply weqb_eq in Hy. subst y. apply decide_eq0_b_sound in He. apply eqb_iff in He. apply ltu_iff.
    rewrite den_VL, wone_ok. pose proof (bv_unsigned_in_range _ (den E a')).
    destruct r0. - rewrite He. reflexivity. - assert (bv_unsigned (den E a') <> 0) by (intros X; apply He; apply bv_eq; rewrite X; reflexivity). lia. }
  assert (ZERO : forall x b' r, weqb x wzero = true -> decide_eq0_b fs b' = Some r -> bv_ltu (den E (VL x)) (den E b') = negb r).
  { intros x b' r0 Hx He. apply weqb_eq in Hx. subst x. apply decide_eq0_b_sound in He. apply eqb_iff in He. apply ltu_iff.
    rewrite den_VL, wzero_ok. pose proof (bv_unsigned_in_range _ (den E b')).
    destruct r0; cbn [negb]. - rewrite He. reflexivity. - assert (bv_unsigned (den E b') <> 0) by (intros X; apply He; apply bv_eq; rewrite X; reflexivity). lia. }
  destruct a as [x|k o| | | | | | | | |]; destruct b as [y|k' o'| | | | | | | | |]; try discriminate H;
    try match type of H with
        | (if weqb ?y wzero then _ else _) = _ => destruct (weqb y wzero) eqn:HY0; [vp_bsplit; apply U0; exact HY0 | clear HY0]
        end;
    try match type of H with
        | context [if weqb ?y wone then decide_eq0_b fs ?a' else None] =>
            destruct (weqb y wone) eqn:HY1;
            [ destruct (decide_eq0_b fs a') as [r1|] eqn:HE1; cbn beta iota in H;
              [vp_bsplit; eapply (ONE a' y); [exact HY1 | exact HE1] | clear HY1 HE1] | clear HY1; cbn beta iota in H ]
        end;
    try match type of H with
        | context [if weqb ?x wzero then option_map negb (decide_eq0_b fs ?b') else None] =>
            destruct (weqb x wzero) eqn:HX0;
            [ destruct (decide_eq0_b fs b') as [r1|] eqn:HE1; cbn beta iota delta [option_map] in H;
              [vp_bsplit; eapply (ZERO x b'); [exact HX0 | exact HE1] | clear HX0 HE1] | clear HX0; cbn beta iota in H ]
        end;
    try match type of H with
        | (match (match sv_umax ?a' with Some m => wltu m ?y | None => false end) with | true => _ | false => _ end) = _ =>
            destruct (match sv_umax a' with Some m => wltu m y | None => false end) eqn:HU;
            [vp_bsplit; apply U; exact HU | clear HU]
        end;
    try exact (lookup_ltu_lit_r_sound _ _ _ H); try exact (lookup_ltu_lit_l_sound _ _ _ H).
  all: match goal with
  | |- bv_ltu (den E (VL ?x)) (den E (VP ?k' ?o')) = _ =>
    destruct (weqb o' wzero) eqn:Ho; [|exact (lookup_ltu_lit_l_sound _ _ _ H)];
    destruct (find_range fs k') as [[lo hi]|] eqn:Hr; [|exact (lookup_ltu_lit_l_sound _ _ _ H)];
    apply find_range_sound in Hr;
    destruct (wltu x lo) eqn:H1; [|destruct (wleu hi x) eqn:H2]; try exact (lookup_ltu_lit_l_sound _ _ _ H);
    vp_bsplit; apply ltu_iff; rewrite den_VL, (den_VP0 _ _ Ho); vp_wcmp; lia
  | |- bv_ltu (den E (VP ?k ?o)) (den E (VL ?y)) = _ =>
    destruct (weqb o wzero) eqn:Ho; [|exact (lookup_ltu_lit_r_sound _ _ _ H)];
    destruct (find_range fs k) as [[lo hi]|] eqn:Hr; [|exact (lookup_ltu_lit_r_sound _ _ _ H)];
    apply find_range_sound in Hr;
    destruct (wltu hi y) eqn:H1; [|destruct (wleu y lo) eqn:H2]; try exact (lookup_ltu_lit_r_sound _ _ _ H);
    vp_bsplit; apply ltu_iff; rewrite den_VL, (den_VP0 _ _ Ho); vp_wcmp; lia
  end.
Qed.

Fixpoint lt_eval (t : lterm) : Z := match t with [] => 0 | (a, c) :: t' => c * U a + lt_eval t' end.
Definition l_eval (l : lin) : Z := lt_eval (fst l) + snd l.

Lemma lt_add1_sound t a c : lt_eval (lt_add1 t a c) = lt_eval t + c * U a.
Proof.
  induction t as [|[a' c'] t IH]; cbn [lt_add1].
  - destruct (Z.eqb_spec c 0); cbn [lt_eval]; lia.
  - destruct (sv_eqb a a') eqn:Q.
    + apply sv_eqb_eq in Q. subst a'. destruct (Z.eqb_spec (c' + c) 0); cbn [lt_eval]; lia.
    + cbn [lt_eval]. rewrite IH. lia.
Qed.

Lemma lt_merge_sound t u s : lt_eval (lt_merge t u s) = lt_eval t + s * lt_eval u.
Proof.
  revert t. induction u as [|[a c] u IH]; intros t; cbn [lt_merge lt_eval]; [lia|].
  rewrite IH, lt_add1_sound. lia.
Qed.

Lemma l_comb_sound x s y : l_eval (l_comb x s y) = l_eval x + s * l_eval y.
Proof. unfold l_comb, l_eval; cbn [fst snd]. rewrite lt_merge_sound. lia. Qed.

Lemma l_atom_sound v : l_eval (l_atom v) = U v.
Proof. unfold l_atom, l_eval; cbn [fst snd lt_eval]. lia. Qed.
Lemma l_const_sound c : l_eval (l_const c) = c.
Proof. unfold l_const, l_eval; cbn [fst snd lt_eval]. lia. Qed.

Lemma l_isconst_sound l k : l_isconst l = Some k -> l_eval l = k.
Proof. unfold l_isconst, l_eval. destruct l as [[|? ?] c]; cbn [fst snd lt_eval]; intros H; [injection H as <-; lia|discriminate H]. Qed.

Lemma lt_scale_sound c t : lt_eval (lt_scale c t) = c * lt_eval t.
Proof.
  unfold lt_scale. destruct (Z.eqb_spec c 0) as [->|NE]; [cbn; lia|].
  induction t as [|[a k] t IH]; cbn [List.map lt_eval fst snd]; [lia|]. rewrite IH. lia.
Qed.
Lemma l_scale_sound c l : l_eval (l_scale c l) = c * l_eval l.
Proof. unfold l_scale, l_eval; cbn [fst snd]. rewrite lt_scale_sound. lia. Qed.

Lemma lt_eval_lower t : lt_allb (fun c => (0 <=? c)%Z) t = true -> 0 <= lt_eval t.
Proof.
  induction t as [|[a c] t IH]; cbn [lt_allb List.forallb lt_eval fst snd]; intros H; [lia|].
  apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. pose proof (U_range a). specialize (IH H2). nia.
Qed.
Lemma lt_eval_upper t : lt_allb (fun c => (c <=? 0)%Z) t = true -> lt_eval t <= 0.
Proof.
  induction t as [|[a c] t IH]; cbn [lt_allb List.forallb lt_eval fst snd]; intros H; [lia|].
  apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. pose proof (U_range a). specialize (IH H2). nia.
Qed.
Lemma l_nonnegb_sound l : l_nonnegb l = true -> 0 <= l_eval l.
Proof.
  unfold l_nonnegb, l_eval. intros H. apply andb_prop in H as [H1 H2]. apply Z.leb_le in H2.
  pose proof (lt_eval_lower _ H1). lia.
Qed.

Definition gap_ok (c : gapc) : Prop := let '(g, lb, e) := c in lb <= l_eval g /\ (e = true -> l_eval g = 0).

Lemma sel_rest_sound : forall sel d, l_eval (sel_rest d sel) = l_eval d - (fold_right (fun sc acc => fst sc * l_eval (fst (fst (snd sc))) + acc) 0 sel).
Proof.
  induction sel as [|[s [[g lb] e]] sel IH]; intros d; cbn [sel_rest fold_right fst snd]; [lia|].
  rewrite IH, l_comb_sound. lia.
Qed.

Lemma sel_lo_sound : forall sel L, Forall (fun sc => gap_ok (snd sc)) sel -> sel_lo sel = Some L ->
  L <= fold_right (fun sc acc => fst sc * l_eval (fst (fst (snd sc))) + acc) 0 sel.
Proof.
  induction sel as [|[s [[g lb] e]] sel IH]; intros L HF H; cbn [sel_lo fold_right fst snd] in *.
  - injection H as <-. lia.
  - apply Forall_cons_iff in HF as [H1 H2]. cbn [snd gap_ok] in H1. destruct H1 as [GL GE].
    unfold oadd in H. destruct (term_lo s (g, lb, e)) as [x|] eqn:TL; [|discriminate H].
    destruct (sel_lo sel) as [y|] eqn:SL; [|discriminate H]. injection H as <-.
    specialize (IH y H2 eq_refl).
    unfold term_lo in TL. destruct (Z.ltb_spec 0 s).
    + injection TL as <-. nia.
    + destruct e; [|discriminate TL]. injection TL as <-. rewrite (GE eq_refl). lia.
Qed.

Lemma sel_hi_sound : forall sel H0, Forall (fun sc => gap_ok (snd sc)) sel -> sel_hi sel = Some H0 ->
  fold_right (fun sc acc => fst sc * l_eval (fst (fst (snd sc))) + acc) 0 sel <= H0.
Proof.
  induction sel as [|[s [[g lb] e]] sel IH]; intros L HF H; cbn [sel_hi fold_right fst snd] in *.
  - injection H as <-. lia.
  - apply Forall_cons_iff in HF as [H1 H2]. cbn [snd gap_ok] in H1. destruct H1 as [GL GE].
    unfold oadd in H. destruct (term_hi s (g, lb, e)) as [x|] eqn:TL; [|discriminate H].
    destruct (sel_hi sel) as [y|] eqn:SL; [|discriminate H]. injection H as <-.
    specialize (IH y H2 eq_refl).
    unfold term_hi in TL. destruct (Z.ltb_spec 0 s).
    + destruct e; [|discriminate TL]. injection TL as <-. rewrite (GE eq_refl). lia.
    + injection TL as <-. unfold sel_ok. nia.
Qed.

Definition ab_ok (ab : abtab) : Prop := (forall fs', fst ab = Some fs' -> fs' = fs) /\ Forall (fun p => inb (U (fst p)) (snd p)) (snd ab).
Lemma atom_bounds_ok : forall t, ab_ok (atom_bounds fs t).
Proof.
  intros t. unfold ab_ok, atom_bounds. cbn [fst snd]. split; [destruct (asan_on fs); [intros fs' [= <-]; reflexivity| discriminate]|].
  apply Forall_forall. intros p Hp. apply in_map_iff in Hp as (ac & <- & _).
  cbn [fst snd]. apply sv_bounds_sound.
Qed.
Lemma ab_find_ok ab a : ab_ok ab -> inb (U a) (ab_find ab a).
Proof.
  intros [HF H]. unfold ab_find. destruct ab as [fb l]. cbn [fst snd] in *. induction l as [|[a' b] l IH]; cbn [ab_find_l].
  - destruct fb as [fs'|]; [rewrite (HF fs' eq_refl); apply sv_bounds_sound| apply full_ok; apply U_range].
  - apply Forall_cons_iff in H as [H1 H2]. destruct (sv_eqb a a') eqn:Q; [apply sv_eqb_eq in Q; subst a'; exact H1| exact (IH H2)].
Qed.
Lemma lt_lo_sound ab t : ab_ok ab -> lt_lo ab t <= lt_eval t.
Proof.
  intros H. induction t as [|[a c] t IH]; cbn [lt_lo lt_eval fst snd]; [lia|].
  pose proof (ab_find_ok ab a H) as B. destruct (ab_find ab a) as [lo hi]. unfold inb in B; cbn [fst snd] in B.
  destruct (Z.ltb_spec 0 c); nia.
Qed.
Lemma lt_hi_sound ab t : ab_ok ab -> lt_eval t <= lt_hi ab t.
Proof.
  intros H. induction t as [|[a c] t IH]; cbn [lt_hi lt_eval fst snd]; [lia|].
  pose proof (ab_find_ok ab a H) as B. destruct (ab_find ab a) as [lo hi]. unfold inb in B; cbn [fst snd] in B.
  destruct (Z.ltb_spec 0 c); nia.
Qed.

Lemma lin_bounds_sound ab d sel lo hi : ab_ok ab -> Forall (fun sc => gap_ok (snd sc)) sel -> lin_bounds ab d sel = (lo, hi) ->
  (forall l, lo = Some l -> l <= l_eval d) /\ (forall u, hi = Some u -> l_eval d <= u).
Proof.
  intros HA HF H. unfold lin_bounds in H. destruct (sel_ok sel); [|injection H as <- <-; split; intros; discriminate].
  pose proof (sel_rest_sound sel d) as SR. set (r := sel_rest d sel) in *.
  assert (LR : l_eval r = lt_eval (fst r) + snd r) by reflexivity.
  pose proof (lt_lo_sound ab (fst r) HA) as L0. pose proof (lt_hi_sound ab (fst r) HA) as H0.
  injection H as <- <-. split.
  - intros l Hl. destruct (sel_lo sel) as [x|] eqn:SL; cbn [oadd] in Hl; [|discriminate Hl]. injection Hl as <-.
    pose proof (sel_lo_sound sel x HF SL). lia.
  - intros u Hu. destruct (sel_hi sel) as [x|] eqn:SL; cbn [oadd] in Hu; [|discriminate Hu]. injection Hu as <-.
    pose proof (sel_hi_sound sel x HF SL). lia.
Qed.

Lemma lin_try_sound ab d sel r : ab_ok ab -> Forall (fun sc => gap_ok (snd sc)) sel -> lin_try ab d sel = Some r ->
  if r then 1 <= l_eval d else l_eval d <= 0.
Proof.
  intros HA HF H. unfold lin_try in H. destruct (lin_bounds ab d sel) as [lo hi] eqn:LB.
  destruct (lin_bounds_sound ab d sel lo hi HA HF LB) as [LO HI].
  destruct lo as [l|].
  - destruct (Z.leb_spec 1 l); [injection H as <-; pose proof (LO l eq_refl); lia|].
    destruct hi as [u|]; [|discriminate H]. destruct (Z.leb_spec u 0); [|discriminate H]. injection H as <-.
    pose proof (HI u eq_refl). lia.
  - destruct hi as [u|]; [|discriminate H]. destruct (Z.leb_spec u 0); [|discriminate H]. injection H as <-.
    pose proof (HI u eq_refl). lia.
Qed.

Lemma lin_try_eq_sound ab d sel r : ab_ok ab -> Forall (fun sc => gap_ok (snd sc)) sel -> lin_try_eq ab d sel = Some r ->
  if r then l_eval d = 0 else l_eval d <> 0.
Proof.
  intros HA HF H. unfold lin_try_eq in H. destruct (lin_bounds ab d sel) as [lo hi] eqn:LB.
  destruct (lin_bounds_sound ab d sel lo hi HA HF LB) as [LO HI].
  destruct lo as [l|]; destruct hi as [u|]; try discriminate H.
  - pose proof (LO l eq_refl). pose proof (HI u eq_refl).
    destruct (Z.eqb_spec l 0); destruct (Z.eqb_spec u 0); cbn [andb] in H; try (injection H as <-; lia).
    all: destruct (Z.leb_spec 1 l); cbn [orb] in H; [injection H as <-; lia|];
         destruct (Z.leb_spec u (-1)); [injection H as <-; lia| discriminate H].
  - pose proof (LO l eq_refl). destruct (Z.leb_spec 1 l); [injection H as <-; lia| discriminate H].
  - pose proof (HI u eq_refl). destruct (Z.leb_spec u (-1)); [injection H as <-; lia| discriminate H].
Qed.

Lemma lin_try_nonneg_sound ab d sel : ab_ok ab -> Forall (fun sc => gap_ok (snd sc)) sel -> lin_try_nonneg ab d sel = Some true -> 0 <= l_eval d.
Proof.
  intros HA HF H. unfold lin_try_nonneg in H. destruct (lin_bounds ab d sel) as [lo hi] eqn:LB.
  destruct (lin_bounds_sound ab d sel lo hi HA HF LB) as [LO HI].
  destruct lo as [l|]; [|discriminate H]. destruct (Z.leb_spec 0 l); [|discriminate H]. pose proof (LO l eq_refl). lia.
Qed.

Lemma first_some_In {A B} (f : A -> option B) l r : first_some f l = Some r -> exists x, In x l /\ f x = Some r.
Proof.
  induction l as [|x l IH]; cbn [first_some]; intros H; [discriminate H|].
  destruct (f x) as [r'|] eqn:Fx.
  - injection H as <-. exists x. split; [left; reflexivity| exact Fx].
  - destruct (IH H) as (y & Hy & Fy). exists y. split; [right; exact Hy| exact Fy].
Qed.

Lemma cands1_ok d G sel : Forall gap_ok G -> In sel (cands1 d G) -> Forall (fun sc => gap_ok (snd sc)) sel.
Proof.
  intros HG Hin. unfold cands1 in Hin. destruct Hin as [<-|Hin]; [constructor|].
  apply in_map_iff in Hin as (g & <- & Hg). constructor; [|constructor]. cbn [snd]. exact (proj1 (Forall_forall _ _) HG g Hg).
Qed.
Lemma cands2_ok d G sel : Forall gap_ok G -> In sel (cands2 d G) -> Forall (fun sc => gap_ok (snd sc)) sel.
Proof.
  intros HG Hin. unfold cands2 in Hin. apply in_flat_map in Hin as (g1 & Hg1 & Hin). cbv zeta in Hin.
  destruct (ratio d (fst (fst g1)) =? 0)%Z; [destruct Hin|].
  apply in_flat_map in Hin as (g2 & Hg2 & Hin).
  destruct (ratio (l_comb d (- ratio d (fst (fst g1))) (fst (fst g1))) (fst (fst g2)) =? 0)%Z; [destruct Hin|].
  destruct Hin as [<-|[]].
  constructor; [cbn [snd]; exact (proj1 (Forall_forall _ _) HG g1 Hg1)|].
  constructor; [cbn [snd]; exact (proj1 (Forall_forall _ _) HG g2 Hg2)| constructor].
Qed.

Lemma lin_nonneg_sound G d : Forall gap_ok G -> lin_nonneg G fs d = true -> 0 <= l_eval d.
Proof.
  intros HG H. unfold lin_nonneg in H. apply orb_prop in H as [H|H].
  - exact (l_nonnegb_sound d H).
  - destruct (first_some (lin_try_nonneg (atom_bounds fs (fst d)) d) (cands1 d G)) as [[]|] eqn:F; try discriminate H.
    destruct (first_some_In _ _ _ F) as (sel & Hsel & T).
    exact (lin_try_nonneg_sound _ d sel (atom_bounds_ok (fst d)) (cands1_ok d G sel HG Hsel) T).
Qed.

Lemma ext_transparent : forall sx lo n a,
  PrimInt63.eqb lo 0%uint63 && PrimInt63.ltb 0%uint63 n && PrimInt63.ltb n 8%uint63 && wltu (snd (sv_bounds fs a)) (ext_lim sx n) = true ->
  U (VExt sx lo n a) = U a.
Proof.
  intros sx lo n a C.
  apply andb_prop in C as [C HB0]. apply andb_prop in C as [C Hn8]. apply andb_prop in C as [Hlo Hn0].
  rewrite wltu_w2Z in HB0. apply Z.ltb_lt in HB0. rename HB0 into HB.
  apply int_eqb_eq in Hlo. subst lo.
  apply Uint63.ltb_spec in Hn0. apply Uint63.ltb_spec in Hn8.
  change (to_Z 0%uint63) with 0 in Hn0. change (to_Z 8%uint63) with 8 in Hn8.
  rewrite ext_lim_val in HB by lia. pose proof (sv_bounds_hi a) as BA. pose proof (U_range a) as RA.
  cbn [den]. unfold ext_word. change (to_Z 0%uint63) with 0.
  assert (P : 2 ^ (8 * to_Z n - (if sx then 1 else 0)) <= 2 ^ 56) by (apply Z.pow_le_mono_r; destruct sx; lia).
  rewrite ext_Z_small_id by (unfold two64 in *; lia).
  rewrite Z_to_bv64_small by lia. reflexivity.
Qed.
Lemma addw_lit_transparent : forall x z,
  negb (wt z) && negb (wt (snd (sv_bounds fs x))) && wltu (wadd (snd (sv_bounds fs x)) z) bit31w = true ->
  U (VAluw ALU_ADD x (VL z)) = U x + w2Z z.
Proof.
  intros x z H. apply andb_prop in H as [H Hb]. apply andb_prop in H as [Tz Th].
  apply negb_true_iff in Tz. apply negb_true_iff in Th.
  pose proof (w2Z_wt z) as Wz. rewrite Tz in Wz. symmetry in Wz. apply Z.leb_gt in Wz.
  pose proof (w2Z_wt (snd (sv_bounds fs x))) as Wh. rewrite Th in Wh. symmetry in Wh. apply Z.leb_gt in Wh.
  pose proof (w2Z_range z) as Rz. pose proof (w2Z_range (snd (sv_bounds fs x))) as Rh.
  rewrite wltu_w2Z, bit31w_val, wadd_ok in Hb. apply Z.ltb_lt in Hb.
  rewrite Z.mod_small in Hb by (unfold two63, two64 in *; lia).
  pose proof (sv_bounds_hi x) as BX. pose proof (U_range x) as R.
  cbn [den alu32 alu]. rewrite sext32_unsigned, bv_add_unsigned, !low32_ext, wbv_unsigned.
  rewrite (Z.mod_small (U x)) by lia. rewrite (Z.mod_small (w2Z z)) by lia.
  unfold bv_wrap. rewrite Z.mod_small by (change (bv_modulus 32) with (2^32); lia). unfold sx32Z.
  destruct (Z.leb_spec (2 ^ 31) (U x + w2Z z)); [lia|reflexivity].
Qed.

Lemma pow2_of_land : forall x, 0 < x -> Z.land (x + 1) x = 0 -> x + 1 = 2 ^ (Z.log2 (x + 1)).
Proof.
  intros x Hx HL. pose proof (Z.log2_spec (x + 1) ltac:(lia)) as [H1 H2]. pose proof (Z.log2_nonneg (x + 1)) as Hj.
  set (j := Z.log2 (x + 1)) in *. rewrite Z.pow_succ_r in H2 by lia.
  destruct (Z.eq_dec (x + 1) (2 ^ j)) as [|NE]; [assumption|]. exfalso.
  assert (T1 : Z.testbit (x + 1) j = true) by (apply Z.testbit_true; [lia|]; replace ((x + 1) / 2 ^ j) with 1; [reflexivity|apply Z.div_unique with (r := x + 1 - 2 ^ j); lia]).
  assert (T2 : Z.testbit x j = true) by (apply Z.testbit_true; [lia|]; replace (x / 2 ^ j) with 1; [reflexivity|apply Z.div_unique with (r := x - 2 ^ j); lia]).
  pose proof (Z.land_spec (x + 1) x j) as X. rewrite HL, Z.bits_0, T1, T2 in X. discriminate X.
Qed.

Lemma head0_pow2 j : 0 <= j <= 62 -> forall i, to_Z i = 2 ^ j -> to_Z (PrimInt63.head0 i) = 62 - j.
Proof.
  intros Hj i Hi. pose proof (head0_spec i) as Hs. rewrite Hi, wB_two63, two63_eq in Hs.
  assert (Hp : 0 < 2 ^ j) by (apply Z.pow_pos_nonneg; lia). specialize (Hs Hp).
  change (2 ^ 63 / 2) with (2 ^ 62) in Hs. rewrite <- Z.pow_add_r in Hs by (pose proof (int_range (PrimInt63.head0 i)); lia).
  pose proof (int_range (PrimInt63.head0 i)).
  destruct (Z.lt_total (to_Z (PrimInt63.head0 i) + j) 62) as [L|[Eq|G]]; [| lia |].
  - exfalso. assert (2 ^ (to_Z (PrimInt63.head0 i) + j) < 2 ^ 62) by (apply Z.pow_lt_mono_r; lia). lia.
  - exfalso. assert (2 ^ 63 <= 2 ^ (to_Z (PrimInt63.head0 i) + j)) by (apply Z.pow_le_mono_r; lia). lia.
Qed.

Lemma head0_zero : PrimInt63.head0 0 = 63%uint63.
Proof. reflexivity. Qed.

Lemma low_mask_k_sound : forall m k, low_mask_k m = Some k -> 1 <= to_Z k <= 62 /\ w2Z m = 2 ^ to_Z k - 1.
Proof.
  intros m k H. unfold low_mask_k in H. destruct (wt m) eqn:Ht; [discriminate|]. set (x := wl m) in H.
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hc end; [|discriminate].
  injection H as Hm. apply andb_prop in Hc as [Hc Hlt]. apply andb_prop in Hc as [Hl Hn].
  apply negb_true_iff, eqb_false_spec in Hn. apply int_eqb_eq in Hl. apply Uint63.ltb_spec in Hlt.
  change (to_Z bit62i) with (2 ^ 62) in Hlt.
  apply (f_equal to_Z) in Hl. rewrite land_spec', add_spec, wB_two63, two63_eq in Hl. change (to_Z 1) with 1 in Hl. change (to_Z 0) with 0 in Hl.
  assert (Hx0 : to_Z x <> 0) by (intros X; apply Hn; apply to_Z_inj; rewrite X; reflexivity).
  pose proof (int_range x) as Rx. rewrite two63_eq in Rx.
  rewrite Z.mod_small in Hl by lia.
  pose proof (pow2_of_land (to_Z x) ltac:(lia) Hl) as P. set (j := Z.log2 (to_Z x + 1)) in *.
  pose proof (Z.log2_nonneg (to_Z x + 1)) as Jn. fold j in Jn.
  assert (Hj : 1 <= j <= 62).
  { split.
    - destruct (Z.eq_dec j 0) as [J0|]; [|lia]. rewrite J0 in P. change (2 ^ 0) with 1 in P. lia.
    - destruct (Z.le_gt_cases j 62) as [|G]; [assumption|]. assert (2 ^ 63 <= 2 ^ j) by (apply Z.pow_le_mono_r; lia). lia. }
  assert (KJ : to_Z k = j).
  { rewrite <- Hm, sub_spec, (head0_pow2 j) by (lia || (rewrite add_spec, wB_two63, two63_eq; change (to_Z 1) with 1; rewrite Z.mod_small; lia)).
    change (to_Z 62) with 62. rewrite wB_two63, Z.mod_small by (unfold two63; lia). lia. }
  rewrite KJ. split; [exact Hj|]. unfold w2Z. rewrite Ht. fold x. lia.
Qed.

Lemma linz_sound G : Forall gap_ok G -> forall v, l_eval (linz G fs v) = U v.
Proof.
  intros HG. induction v; try (cbn [linz]; apply l_atom_sound).
  - cbn [linz]. rewrite l_const_sound, den_VL. reflexivity.
  - cbn [linz]. destruct (weqb off wzero) eqn:Ho; [apply l_atom_sound|].
    destruct (nowrap_kb fs k off) eqn:NW; [|apply l_atom_sound].
    rewrite l_comb_sound, l_atom_sound, l_const_sound.
    destruct (nowrap_kb_sound k off NW) as [_ ->]. rewrite (den_VP0 k wzero eq_refl). lia.
  - pose proof (U_range v1) as R1. pose proof (U_range v2) as R2.
    pose proof (sv_bounds_lo v1) as L1. pose proof (sv_bounds_hi v1) as H1.
    pose proof (sv_bounds_lo v2) as L2. pose proof (sv_bounds_hi v2) as H2.
    destruct op; try apply l_atom_sound; cbn [linz]; fold (linz G fs v1) (linz G fs v2).
    +
      assert (GEN : add_carries (snd (sv_bounds fs v1)) (snd (sv_bounds fs v2)) = false ->
                    l_eval (l_comb (linz G fs v1) 1 (linz G fs v2)) = U (VAlu ALU_ADD v1 v2)).
      { intros NC.
        assert (NC' : ~ two64 <= w2Z (snd (sv_bounds fs v1)) + w2Z (snd (sv_bounds fs v2))) by (rewrite <- add_carries_iff, NC; discriminate).
        rewrite l_comb_sound, IHv1, IHv2. cbn [den alu64 alu]. rewrite bv_add_unsigned. unfold bv_wrap. rewrite bv_modulus_64.
        rewrite Z.mod_small by lia. lia. }
      destruct v2 as [c| | | | | | | | | |]; try (destruct (add_carries _ _) eqn:NC; cbn [negb]; [apply l_atom_sound|exact (GEN eq_refl)]).
      rewrite den_VL in *. pose proof (w2Z_range c) as Rc.
      destruct (wt c) eqn:T.
      * cbv zeta. match goal with |- l_eval (if ?cnd then _ else _) = _ => destruct cnd eqn:CC; [|apply l_atom_sound] end.
        pose proof (w2Z_wt c) as Tc. rewrite T in Tc. symmetry in Tc. apply Z.leb_le in Tc.
        assert (N : w2Z (wneg c) = two64 - w2Z c).
        { unfold wneg. rewrite wsub_ok, wzero_ok. unfold two63, two64 in *. symmetry. apply Z.mod_unique_pos with (q := -1); lia. }
        assert (LE0 : two64 - w2Z c <= U v1).
        { apply orb_prop in CC as [CC|CC].
          - rewrite wleu_w2Z in CC. apply Z.leb_le in CC. lia.
          - pose proof (lin_nonneg_sound G _ HG CC) as NN. rewrite l_comb_sound, IHv1, l_const_sound, N in NN. lia. }
        rewrite l_comb_sound, IHv1, l_const_sound, N. cbn [den alu64 alu]. rewrite bv_add_unsigned, wbv_unsigned. unfold bv_wrap. rewrite bv_modulus_64.
        replace (U v1 + w2Z c) with ((U v1 - (two64 - w2Z c)) + 1 * two64) by lia.
        rewrite Z.mod_add by (unfold two64; lia). rewrite Z.mod_small by (unfold two63, two64 in *; lia). lia.
      * destruct (add_carries (snd (sv_bounds fs v1)) c) eqn:NC; cbn [negb]; [apply l_atom_sound|].
        assert (NC' : ~ two64 <= w2Z (snd (sv_bounds fs v1)) + w2Z c) by (rewrite <- add_carries_iff, NC; discriminate).
        rewrite l_comb_sound, IHv1, l_const_sound. cbn [den alu64 alu]. rewrite bv_add_unsigned, wbv_unsigned. unfold bv_wrap. rewrite bv_modulus_64.
        rewrite Z.mod_small by lia. lia.
    +
      cbv zeta. match goal with |- l_eval (if ?c then _ else _) = _ => destruct c eqn:C; [|apply l_atom_sound] end.
      assert (LE0 : U v2 <= U v1).
      { apply orb_prop in C as [C|C]; [apply orb_prop in C as [C|C]; [apply orb_prop in C as [C|C]|]|].
        - rewrite wleu_w2Z in C. apply Z.leb_le in C. lia.
        - pose proof (fact_lookup_holds E fs _ Hfs C) as (f & Hf & Hp).
          destruct f; try discriminate Hp. cbn [is_FULe] in Hp. apply andb_prop in Hp as [P1 P2].
          apply sv_eqb_eq in P1. apply sv_eqb_eq in P2. subst. cbn [fact_holds] in Hf. lia.
        - pose proof (fact_lookup_holds E fs _ Hfs C) as (f & Hf & Hp).
          destruct f; try discriminate Hp. cbn [is_FULt] in Hp. apply andb_prop in Hp as [P1 P2].
          apply sv_eqb_eq in P1. apply sv_eqb_eq in P2. subst. cbn [fact_holds] in Hf. lia.
        - pose proof (lin_nonneg_sound G _ HG C) as NN. rewrite l_comb_sound, IHv1, IHv2 in NN. lia. }
      rewrite l_comb_sound, IHv1, IHv2. cbn [den alu64 alu]. rewrite bv_sub_unsigned. unfold bv_wrap. rewrite bv_modulus_64.
      rewrite Z.mod_small by lia. lia.
    +   destruct v2 as [s| | | | | | | | | |]; try apply l_atom_sound.
      rewrite wleu_w2Z. destruct (Z.leb_spec (w2Z (snd (sv_bounds fs v1))) (w2Z (wsrl wones s))); [|apply l_atom_sound].
      rewrite l_scale_sound, IHv1. cbn [den alu64 alu].
      rewrite bv_shiftl_unsigned, shamt6_bv, Z.shiftl_mul_pow2 by apply int_range.
      pose proof (shamt6_range s) as SR. unfold wsrl in H. rewrite wsrl_k_ok in H by lia. change (w2Z wones) with (two64 - 1) in H.
      assert (P : 0 < 2 ^ to_Z (shamt6 s)) by (apply Z.pow_pos_nonneg; lia).
      pose proof (Z.mul_div_le (two64 - 1) (2 ^ to_Z (shamt6 s)) ltac:(lia)) as MD.
      unfold bv_wrap. rewrite bv_modulus_64. change (2 ^ 64) with two64. rewrite Z.mod_small by nia. nia.
    +
      destruct v2 as [m| | | | | | | | | |]; try apply l_atom_sound.
      destruct (low_mask_k m) as [k|] eqn:LM; [|apply l_atom_sound].
      destruct (PrimInt63.leb k 3%uint63 && asan_on fs); [|apply l_atom_sound].
      destruct (low_mask_k_sound m k LM) as (K1 & KM).
      rewrite l_comb_sound, IHv1, l_atom_sound. cbn [den alu64 alu].
      rewrite bv_and_unsigned, bv_shiftr_unsigned, shamt6_bv, shamt6_ok, !wbv_unsigned, wlit_ok, KM.
      assert (L63 : Z.land (to_Z k) 63 = to_Z k).
      { change 63 with (Z.ones 6). rewrite Z.land_ones by lia. apply Z.mod_small. change (2 ^ 6) with 64. lia. }
      rewrite L63, Z.shiftr_div_pow2 by lia.
      replace (2 ^ to_Z k - 1) with (Z.ones (to_Z k)) by (rewrite Z.ones_equiv; lia).
      rewrite Z.land_ones by lia. rewrite (Z.mod_eq (U v1) (2 ^ to_Z k)) by (apply Z.pow_nonzero; lia). ring.
  -
    destruct op; try apply l_atom_sound. cbn [linz]; fold (linz G fs v1).
    destruct v2 as [z| | | | | | | | | |]; try apply l_atom_sound.
    cbv zeta. match goal with |- l_eval (if ?c then _ else _) = _ => destruct c eqn:C; [|apply l_atom_sound] end.
    rewrite l_comb_sound, IHv1, l_const_sound, (addw_lit_transparent v1 z C). lia.
  -
    pose proof (U_range v1) as R1. pose proof (sv_bounds_hi v1) as H1.
    destruct op; try apply l_atom_sound. cbn [linz]; fold (linz G fs v1).
    destruct v2 as [c| | | | | | | | | |]; try apply l_atom_sound.
    rewrite !wltu_w2Z, bit32w_val. destruct (Z.ltb_spec (w2Z (snd (sv_bounds fs v1))) (2 ^ 32)); [|apply l_atom_sound].
    destruct (Z.ltb_spec (w2Z c) (2 ^ 32)); [|apply l_atom_sound]. cbn [andb].
    rewrite l_scale_sound, IHv1. cbn [den mul_div]. rewrite bv_mul_unsigned, wbv_unsigned. unfold bv_wrap. rewrite bv_modulus_64.
    pose proof (w2Z_range c).
    assert (M2 : U v1 * w2Z c < two64) by (unfold two64; change (2^64) with (2^32 * 2^32); nia).
    rewrite Z.mod_small by nia. nia.
  -
    cbn [linz]; fold (linz G fs v).
    match goal with |- l_eval (if ?c then _ else _) = _ => destruct c eqn:C; [|apply l_atom_sound] end.
    rewrite IHv. symmetry. exact (ext_transparent sx lo n v C).
Qed.

Lemma gaps_with_sound G : Forall gap_ok G -> forall fs', facts_hold E fs' -> Forall gap_ok (gaps_with G fs' fs).
Proof.
  intros HG. induction fs' as [|f fs' IH]; intros HF; cbn [gaps_with]; [constructor|].
  apply Forall_cons_iff in HF as [Hf HF'].
  destruct (gap_of G fs f) as [g|] eqn:GO; [|exact (IH HF')].
  constructor; [|exact (IH HF')].
  destruct f; cbn [gap_of] in GO; try discriminate GO.
  4: {
       destruct (ne0_term a b) as [t|] eqn:NT; [|discriminate GO]. injection GO as <-. cbn [gap_ok fact_holds] in *.
       rewrite (linz_sound G HG). split; [|discriminate].
       assert (TZ : U t <> 0).
       { unfold ne0_term in NT. intros X. apply Hf. apply bv_eq.
         destruct b as [z| | | | | | | | | |].
         1: { destruct (weqb z wzero) eqn:Z0; [|discriminate NT]. injection NT as <-. apply weqb_eq in Z0. subst z. rewrite den_VL, wzero_ok. exact X. }
         all: destruct a as [z| | | | | | | | | |]; try discriminate NT; destruct (weqb z wzero) eqn:Z0; try discriminate NT; injection NT as <-;
           apply weqb_eq in Z0; subst z; rewrite den_VL, wzero_ok; symmetry; exact X. }
       pose proof (U_range t). lia. }
  all: injection GO as <-; cbn [gap_ok fact_holds] in *; rewrite l_comb_sound, !(linz_sound G HG).
  - split; [lia| discriminate].
  - split; [lia| discriminate].
  - apply (f_equal bv_unsigned) in Hf. split; [lia| intros _; lia].
Qed.

Lemma linz_indep : forall fs' v, needs_gaps v = false -> forall G G', linz G fs' v = linz G' fs' v.
Proof.
  intros fs' v. induction v as [w|k o|op a1 IH1 a2 IH2|op a1 IH1 a2 IH2|op a1 IH1 a2 IH2|op a1 IH1 a2 IH2|sx lo n y IHy|lo n a1 IH1 a2 IH2|sx j off IHo n|sx k off n|op a1 IH1];
    intros N G G'; try reflexivity.
  -   destruct op; try reflexivity; cbn [needs_gaps] in N.
    +
      assert (NN : needs_gaps a1 = false /\ needs_gaps a2 = false /\ (forall c, a2 = VL c -> wt c = false)).
      { destruct a2; apply Bool.orb_false_iff in N as [Na Nb]; repeat split; try assumption; try reflexivity;
          try (intros c' X; discriminate X). intros c' X. injection X as <-. exact Na. }
      destruct NN as (N1 & N2 & NC).
      cbn [linz]. rewrite ?(IH1 N1 G G'), ?(IH2 N2 G G').
      destruct a2 as [c| | | | | | | | | |]; try reflexivity. rewrite (NC c eq_refl). reflexivity.
    +   discriminate N.
    +   destruct a2 as [c| | | | | | | | | |]; try reflexivity. cbn [linz]. rewrite (IH1 N G G'). reflexivity.
    +   destruct a2 as [c| | | | | | | | | |]; try reflexivity. cbn [linz]. rewrite (IH1 N G G'). reflexivity.
  -   destruct op; try reflexivity. destruct a2 as [c| | | | | | | | | |]; try reflexivity.
    cbn [needs_gaps] in N. cbn [linz]. rewrite (IH1 N G G'). reflexivity.
  -   destruct op; try reflexivity. destruct a2 as [c| | | | | | | | | |]; try reflexivity.
    cbn [needs_gaps] in N. cbn [linz]. rewrite (IH1 N G G'). reflexivity.
  -   cbn [needs_gaps] in N. cbn [linz]. rewrite (IHy N G G'). reflexivity.
Qed.
Lemma gap_of_indep : forall fs' f, fact_needs_gaps f = false -> forall G G', gap_of G fs' f = gap_of G' fs' f.
Proof.
  intros fs' f N G G'. destruct f; try reflexivity; cbn [fact_needs_gaps] in N; apply Bool.orb_false_iff in N as [N1 N2];
    cbn [gap_of]; rewrite ?(linz_indep fs' _ N1 G G'), ?(linz_indep fs' _ N2 G G'); try reflexivity.
    destruct (ne0_term a b) as [t|] eqn:NT; [|reflexivity].
  assert (NG : needs_gaps t = false).
  { unfold ne0_term in NT. destruct b as [z| | | | | | | | | |]; try (destruct (weqb z wzero); [injection NT as <-; exact N1| discriminate NT]);
      destruct a as [z| | | | | | | | | |]; try discriminate NT; destruct (weqb z wzero); try discriminate NT; injection NT as <-; exact N2. }
  rewrite (linz_indep fs' t NG G G'). reflexivity.
Qed.
Lemma gap_of_is_gap : forall fs' f G, is_gap_fact f = true -> exists g, gap_of G fs' f = Some g.
Proof.
  intros fs' f G H. destruct f; cbn [is_gap_fact] in H; try discriminate H; cbn [gap_of]; try (eexists; reflexivity).
  destruct (ne0_term a b); [eexists; reflexivity| discriminate H].
Qed.
Lemma gap_of_not_gap : forall fs' f G, is_gap_fact f = false -> gap_of G fs' f = None.
Proof.
  intros fs' f G H. destruct f; cbn [is_gap_fact] in H; try discriminate H; try reflexivity.
  cbn [gap_of]. destruct (ne0_term a b); [discriminate H| reflexivity].
Qed.
Lemma gaps_again_eq : forall all G G0 l, gaps_again G l all (gaps_with G0 l all) = gaps_with G l all.
Proof.
  intros all G G0 l. induction l as [|f l IH]; [reflexivity|]. cbn [gaps_again gaps_with].
  destruct (is_gap_fact f) eqn:IG.
  - destruct (gap_of_is_gap all f G0 IG) as [g0 EG0]. rewrite EG0.
    destruct (gap_of_is_gap all f G IG) as [g EG]. rewrite EG.
    destruct (fact_needs_gaps f) eqn:NF.
    + rewrite IH. reflexivity.
    + rewrite IH. f_equal. rewrite (gap_of_indep all f NF G0 G) in EG0. rewrite EG0 in EG. injection EG as <-. reflexivity.
  - rewrite (gap_of_not_gap all f G0 IG), (gap_of_not_gap all f G IG). exact IH.
Qed.
Lemma gaps_eq_ref : forall fs', gaps fs' = gaps_ref fs'.
Proof. intros fs'. unfold gaps, gaps_ref. cbv zeta. rewrite !gaps_again_eq. reflexivity. Qed.

Lemma gaps_sound : Forall gap_ok (gaps fs).
Proof. rewrite gaps_eq_ref. unfold gaps_ref. apply gaps_with_sound; [|exact Hfs]. apply gaps_with_sound; [|exact Hfs]. apply gaps_with_sound; [constructor| exact Hfs]. Qed.

Lemma lin_ltu_G_sound G a b r : Forall gap_ok G -> lin_ltu_G G fs a b = Some r -> bv_ltu (den E a) (den E b) = r.
Proof.
  unfold lin_ltu_G. intros HG H.
  assert (Hd : l_eval (l_comb (linz G fs b) (-1) (linz G fs a)) = U b - U a) by (rewrite l_comb_sound, !(linz_sound G HG); lia).
  set (d := l_comb _ _ _) in *.
  apply ltu_iff. destruct (l_isconst d) as [k|] eqn:K.
  - apply l_isconst_sound in K. injection H as <-. destruct (Z.ltb_spec 0 k); lia.
  - cbv zeta in H. set (ab := atom_bounds fs (fst d)) in *. pose proof (atom_bounds_ok (fst d)) as HA. fold ab in HA.
    destruct (first_some (lin_try ab d) (cands1 d G)) as [r1|] eqn:F1.
    + injection H as <-. destruct (first_some_In _ _ _ F1) as (sel & Hsel & T).
      pose proof (lin_try_sound ab d sel r1 HA (cands1_ok d G sel HG Hsel) T) as X. destruct r1; lia.
    + destruct (first_some_In _ _ _ H) as (sel & Hsel & T).
      pose proof (lin_try_sound ab d sel r HA (cands2_ok d G sel HG Hsel) T) as X. destruct r; lia.
Qed.

Lemma lin_ltu_sound a b r : lin_ltu fs a b = Some r -> bv_ltu (den E a) (den E b) = r.
Proof. exact (lin_ltu_G_sound (gaps fs) a b r gaps_sound). Qed.

Lemma lin_eq_G_sound G a b r : Forall gap_ok G -> lin_eq_G G fs a b = Some r -> bv_eqb (den E a) (den E b) = r.
Proof.
  unfold lin_eq_G. intros HG H.
  assert (Hd : l_eval (l_comb (linz G fs b) (-1) (linz G fs a)) = U b - U a) by (rewrite l_comb_sound, !(linz_sound G HG); lia).
  set (d := l_comb _ _ _) in *.
  assert (FIN : forall r' : bool, (if r' then l_eval d = 0 else l_eval d <> 0) -> bv_eqb (den E a) (den E b) = r').
  { intros [|] X; apply eqb_iff; [apply bv_eq; lia| intros EQ; apply X; rewrite EQ in Hd; lia]. }
  destruct (l_isconst d) as [k|] eqn:K.
  - apply l_isconst_sound in K. injection H as <-. apply FIN. destruct (Z.eqb_spec k 0); lia.
  - cbv zeta in H. set (ab := atom_bounds fs (fst d)) in *. pose proof (atom_bounds_ok (fst d)) as HA. fold ab in HA.
    destruct (first_some (lin_try_eq ab d) (cands1 d G)) as [r1|] eqn:F1.
    + injection H as <-. destruct (first_some_In _ _ _ F1) as (sel & Hsel & T).
      apply FIN. exact (lin_try_eq_sound ab d sel r1 HA (cands1_ok d G sel HG Hsel) T).
    + destruct (first_some_In _ _ _ H) as (sel & Hsel & T).
      apply FIN. exact (lin_try_eq_sound ab d sel r HA (cands2_ok d G sel HG Hsel) T).
Qed.

Lemma lin_eq_sound a b r : lin_eq fs a b = Some r -> bv_eqb (den E a) (den E b) = r.
Proof. exact (lin_eq_G_sound (gaps fs) a b r gaps_sound). Qed.

Lemma decide_ltu_s_sound : forall a b r, decide_ltu_s fs a b = Some r -> bv_ltu (den E a) (den E b) = r.
Proof.
  intros a b r H.
  destruct a as [x|k o| | | | | | | | |]; destruct b as [y|k' o'| | | | | | | | |];
    try match goal with |- bv_ltu (den E ?a) (den E ?b) = ?r => exact (ltu_generic_sound a b r H) end.
  - cbn [decide_ltu_s] in H. vp_bsplit. cbn [den]. symmetry. apply wltu_ok.
  - cbn [decide_ltu_s] in H. pose proof (syntactic_ltu_sound (VP k o) (VP k' o')) as [S1 S2].
    destruct (PrimInt63.eqb k k') eqn:Hk.
    + vp_bsplit. destruct (nowrap_kb fs k' o) eqn:N1; [|discriminate]. destruct (nowrap_kb fs k' o') eqn:N2; [|discriminate].
      cbn [andb] in H. vp_bsplit. apply nowrap_kb_sound in N1 as [_ N1]. apply nowrap_kb_sound in N2 as [_ N2].
      unfold soff_ltb. rewrite wlts_w2Zs. apply ltu_iff. rewrite N1, N2.
      destruct (Z.ltb_spec (w2Zs o) (w2Zs o')); lia.
    + destruct (fact_lookup fs (is_FULt _ _)); [vp_bsplit; apply ltu_iff; apply S1; reflexivity|].
      destruct (fact_lookup fs (is_FULe _ _) || fact_lookup fs (is_FEq _ _)); [vp_bsplit; apply ltu_iff; apply S2; reflexivity|].
      discriminate.
Qed.

Lemma decide_ltu0_G_sound : forall G, Forall gap_ok G -> forall a b r, decide_ltu0_G G fs a b = Some r -> bv_ltu (den E a) (den E b) = r.
Proof.
  intros G HG a b r H. unfold decide_ltu0_G in H.
  destruct (decide_ltu_s fs a b) as [r'|] eqn:D; [injection H as <-; exact (decide_ltu_s_sound a b r' D)|].
  destruct (bnd_ltu fs a b) as [r'|] eqn:B; [injection H as <-; exact (bnd_ltu_sound a b r' B)|exact (lin_ltu_G_sound G a b r HG H)].
Qed.
Lemma decide_ltu0_sound : forall a b r, decide_ltu0 fs a b = Some r -> bv_ltu (den E a) (den E b) = r.
Proof. exact (decide_ltu0_G_sound (gaps fs) gaps_sound). Qed.

Lemma ne_known_sound a b : ne_known fs a b = true -> den E a <> den E b.
Proof.
  unfold ne_known. intros H.
  destruct (fact_lookup_holds E fs _ Hfs H) as (f & Hf0 & Hf).
  pose proof (anchor_norm_sound f Hf0) as N.
  destruct (anchor_norm f) as [| | | | |x y| |]; try discriminate Hf. cbn [fact_holds] in N.
  apply Bool.orb_true_iff in Hf as [Hf|Hf]; apply Bool.andb_true_iff in Hf as [H1 H2];
    apply sv_eqb_eq in H1; apply sv_eqb_eq in H2; subst x y; [exact N|].
  intros X. apply N. symmetry. exact X.
Qed.

Lemma decide_ltu1_G_sound : forall G, Forall gap_ok G -> forall a b r, decide_ltu1_G G fs a b = Some r -> bv_ltu (den E a) (den E b) = r.
Proof.
  intros G HG a b r H. unfold decide_ltu1_G in H.
  destruct (ne_known fs a b) eqn:NK; [|discriminate H].
  destruct (decide_ltu0_G G fs b a) as [[]|] eqn:D2; try discriminate H. injection H as <-.
  apply (decide_ltu0_G_sound G HG) in D2. apply ne_known_sound in NK.
  apply ltu_iff. apply ltu_iff in D2.
  assert (NE : bv_unsigned (den E a) <> bv_unsigned (den E b)) by (intros X; apply NK; apply bv_eq; exact X).
  lia.
Qed.

Lemma zext_idiom_le : forall a x, zext_idiom a = Some x -> bv_unsigned (den E a) <= bv_unsigned (den E x).
Proof.
  intros a x H. unfold zext_idiom in H.
  destruct a as [| | op a1 b| | | |sx lo n e| | | |]; try discriminate H.
  2: {
       destruct sx; [discriminate H|]. destruct (PrimInt63.eqb lo 0%uint63) eqn:LO; [|discriminate H]. injection H as <-.
       apply Uint63.eqb_correct in LO. subst lo. cbn [den]. unfold ext_word, ext_Z. change (to_Z 0%uint63) with 0.
       change (8 * 0) with 0. rewrite Z.pow_0_r, Z.div_1_r.
       pose proof (bv_unsigned_in_range _ (den E e)) as ER. rewrite bv_modulus_64 in ER.
       pose proof (to_Z_bounded n) as NB.
       assert (PN : 0 < 2 ^ (8 * to_Z n)) by (apply Z.pow_pos_nonneg; lia).
       pose proof (Z.mod_le (bv_unsigned (den E e)) (2 ^ (8 * to_Z n)) ltac:(lia) PN) as ML.
       pose proof (Z.mod_pos_bound (bv_unsigned (den E e)) (2 ^ (8 * to_Z n)) PN) as MB.
       rewrite Z_to_bv64_small by (unfold two64 in *; lia). exact ML. }
  destruct op; try discriminate H.
  destruct a1 as [| | op2 y kk| | | | | | | |]; try discriminate H. destruct op2; try discriminate H.
  destruct kk as [k| | | | | | | | | |]; try discriminate H. destruct b as [k'| | | | | | | | | |]; try discriminate H.
  destruct (PrimInt63.eqb (shamt6 k) (shamt6 k')) eqn:SK; [|discriminate H]. injection H as <-. apply Uint63.eqb_correct in SK.
  pose proof (shamt6_range k) as SR. pose proof (bv_unsigned_in_range _ (den E y)) as YR. rewrite bv_modulus_64 in YR.
  cbn [den alu64 alu]. rewrite bv_shiftr_unsigned, bv_shiftl_unsigned, !shamt6_bv, <- SK.
  rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. unfold bv_wrap. rewrite bv_modulus_64.
  set (s := to_Z (shamt6 k)) in *. assert (PS : 0 < 2 ^ s) by (apply Z.pow_pos_nonneg; lia).
  apply (Z.le_trans _ ((bv_unsigned (den E y) * 2 ^ s) / 2 ^ s)).
  - apply Z.div_le_mono; [lia|]. apply Z.mod_le; [nia| unfold two64; lia].
  - rewrite Z.div_mul by lia. lia.
Qed.
Lemma decide_ltu2_G_sound : forall G, Forall gap_ok G -> forall a b r, decide_ltu2_G G fs a b = Some r -> bv_ltu (den E a) (den E b) = r.
Proof.
  intros G HG a b r H. unfold decide_ltu2_G in H.
  destruct (zext_idiom a) as [x|] eqn:ZA.
  - destruct (decide_ltu0_G G fs x b) as [[]|] eqn:D.
    + injection H as <-. apply (decide_ltu0_G_sound G HG), ltu_iff in D. pose proof (zext_idiom_le a x ZA). apply ltu_iff. lia.
    + destruct (zext_idiom b) as [x'|] eqn:ZB; [|discriminate H].
      destruct (decide_ltu0_G G fs a x') as [[]|] eqn:D'; try discriminate H. injection H as <-.
      apply (decide_ltu0_G_sound G HG), ltu_iff in D'. pose proof (zext_idiom_le b x' ZB). apply ltu_iff. lia.
    + destruct (zext_idiom b) as [x'|] eqn:ZB; [|discriminate H].
      destruct (decide_ltu0_G G fs a x') as [[]|] eqn:D'; try discriminate H. injection H as <-.
      apply (decide_ltu0_G_sound G HG), ltu_iff in D'. pose proof (zext_idiom_le b x' ZB). apply ltu_iff. lia.
  - destruct (zext_idiom b) as [x'|] eqn:ZB; [|discriminate H].
    destruct (decide_ltu0_G G fs a x') as [[]|] eqn:D'; try discriminate H. injection H as <-.
    apply (decide_ltu0_G_sound G HG), ltu_iff in D'. pose proof (zext_idiom_le b x' ZB). apply ltu_iff. lia.
Qed.

Lemma decide_ltu3_G_sound : forall G, Forall gap_ok G -> forall a b r, decide_ltu3_G G fs a b = Some r -> bv_ltu (den E a) (den E b) = r.
Proof.
  intros G HG a b r H. unfold decide_ltu3_G in H.
  destruct a as [| |op x cx| | | | | | | |]; try discriminate H. destruct op; try discriminate H.
  destruct cx as [c| | | | | | | | | |]; try discriminate H.
  destruct b as [| |op y cy| | | | | | | |]; try discriminate H. destruct op; try discriminate H.
  destruct cy as [c'| | | | | | | | | |]; try discriminate H.
  destruct (PrimInt63.eqb (shamt6 c) (shamt6 c') && asan_on fs) eqn:SK; [|discriminate H]. apply andb_prop in SK as [SK _]. apply Uint63.eqb_correct in SK.
  destruct (decide_ltu0_G G fs x y) as [[]|] eqn:D; try discriminate H. injection H as <-.
  apply (decide_ltu0_G_sound G HG), ltu_iff in D. apply ltu_iff.
  pose proof (shamt6_range c) as SR.
  cbn [den alu64 alu]. rewrite !bv_shiftr_unsigned, !shamt6_bv, <- SK. rewrite !Z.shiftr_div_pow2 by lia.
  apply Z.div_le_mono; [apply Z.pow_pos_nonneg; lia | exact D].
Qed.
Lemma decide_ltu_G_sound : forall G, Forall gap_ok G -> forall a b r, decide_ltu_G G fs a b = Some r -> bv_ltu (den E a) (den E b) = r.
Proof.
  intros G HG a b r H. unfold decide_ltu_G in H.
  destruct (decide_ltu0_G G fs a b) as [r'|] eqn:D; [injection H as <-; exact (decide_ltu0_G_sound G HG a b r' D)|].
  destruct (decide_ltu1_G G fs a b) as [r'|] eqn:D1; [injection H as <-; exact (decide_ltu1_G_sound G HG a b r' D1)|].
  destruct (decide_ltu2_G G fs a b) as [r'|] eqn:D2; [injection H as <-; exact (decide_ltu2_G_sound G HG a b r' D2)|].
  exact (decide_ltu3_G_sound G HG a b r H).
Qed.
Lemma decide_ltu_sound : forall a b r, decide_ltu fs a b = Some r -> bv_ltu (den E a) (den E b) = r.
Proof.
  intros a b r H. unfold decide_ltu in H.
  destruct (decide_ltu_s fs a b) as [r'|] eqn:D; [injection H as <-; exact (decide_ltu_s_sound a b r' D)|].
  destruct (bnd_ltu fs a b) as [r'|] eqn:B; [injection H as <-; exact (bnd_ltu_sound a b r' B)|].
  exact (decide_ltu_G_sound (gaps fs) gaps_sound a b r H).
Qed.

Lemma below63_sound : forall k o, below63 fs k o = true ->
  0 <= bv_unsigned (ev E k) + w2Zs o < two63 /\
  bv_unsigned (den E (VP k o)) = bv_unsigned (ev E k) + w2Zs o /\
  bv_signed (den E (VP k o)) = bv_unsigned (ev E k) + w2Zs o.
Proof.
  intros k o H. unfold below63 in H.
  destruct (find_range fs k) as [[lo hi]|] eqn:Hr; [|discriminate].
  apply find_range_sound in Hr. vp_bsplit. vp_wcmp.
  match goal with G : nowrap lo hi o = true |- _ => apply nowrap_sound in G end.
  pose proof (w2Z_wt (wadd hi o)) as Wh. pose proof (w2Z_range hi). pose proof (w2Z_range lo). pose proof (w2Zs_range o).
  match goal with G : wt (wadd hi o) = false |- _ => rewrite G in Wh end.
  destruct (Z.leb_spec two63 (w2Z (wadd hi o))); [discriminate|].
  rewrite wadd_ok, (w2Z_of_w2Zs o), Z.add_assoc, Z.mod_add, Z.mod_small in * by (unfold two64 in *; lia).
  assert (R : 0 <= bv_unsigned (ev E k) + w2Zs o < two63) by lia.
  assert (U : bv_unsigned (den E (VP k o)) = bv_unsigned (ev E k) + w2Zs o) by (rewrite den_VP; apply Z.mod_small; unfold two63, two64 in *; lia).
  split; [exact R|]. split; [exact U|].
  unfold bv_signed. rewrite U. unfold bv_swrap, bv_wrap. rewrite bv_modulus_64, bv_half_modulus_64.
  rewrite Z.mod_small; unfold two63, two64 in *; lia.
Qed.

Definition lts_generic (a b : sv) : option bool :=
      if sv_eqb a b then Some false
      else if fact_lookup fs (is_FSLt a b) then Some true
      else if fact_lookup fs (is_FSLe b a) || fact_lookup fs (is_FEq a b) then Some false
      else None.

Lemma syntactic_lts_sound : forall a b,
  (fact_lookup fs (is_FSLt a b) = true -> bv_signed (den E a) < bv_signed (den E b)) /\
  (fact_lookup fs (is_FSLe b a) || fact_lookup fs (is_FEq a b) = true -> bv_signed (den E b) <= bv_signed (den E a)).
Proof.
  intros a b. split; intros H.
  - vp_fact_cases Hfs H. exact Hh.
  - apply orb_prop in H. destruct H as [H|H]; vp_fact_cases Hfs H; rewrite ?Hh; lia.
Qed.

Lemma lts_generic_sound : forall a b r, lts_generic a b = Some r -> bv_lts (den E a) (den E b) = r.
Proof.
  intros a b r H. unfold lts_generic in H.
  destruct (sv_eqb a b) eqn:He.
  { vp_bsplit. apply lts_iff. lia. }
  pose proof (syntactic_lts_sound a b) as [S1 S2].
  destruct (fact_lookup fs (is_FSLt a b)); [vp_bsplit; apply lts_iff; apply S1; reflexivity|].
  destruct (fact_lookup fs (is_FSLe b a) || fact_lookup fs (is_FEq a b)); [vp_bsplit; apply lts_iff; apply S2; reflexivity|].
  discriminate.
Qed.

Lemma nonneg63_sound : forall v, nonneg63 fs v = true -> bv_unsigned (den E v) < two63.
Proof.
  intros v H. unfold nonneg63 in H. pose proof (sv_bounds_hi v) as B.
  destruct (wt (snd (sv_bounds fs v))) eqn:T; [discriminate H|]. pose proof (w2Z_top_false _ T). lia.
Qed.

Lemma bv_signed_small63 : forall (a : word), bv_unsigned a < two63 -> bv_signed a = bv_unsigned a.
Proof.
  intros a Ha. pose proof (bv_unsigned_in_range _ a). unfold bv_signed, bv_swrap, bv_wrap.
  change (bv_half_modulus 64) with two63. change (bv_modulus 64) with two64 in *. unfold two63, two64 in *.
  rewrite Z.mod_small by lia. lia.
Qed.

Lemma lts_of_ltu_nonneg : forall (a b : word) r,
  bv_unsigned a < two63 -> bv_unsigned b < two63 -> bv_ltu a b = r -> bv_lts a b = r.
Proof.
  intros a b r Ha Hb H. apply ltu_iff in H. apply lts_iff.
  rewrite !bv_signed_small63 by assumption. exact H.
Qed.

Lemma decide_lts_sound : forall a b r, decide_lts fs a b = Some r -> bv_lts (den E a) (den E b) = r.
Proof.
  intros a b r H. unfold decide_lts in H.
  assert (NN : forall a b r, (if nonneg63 fs a && nonneg63 fs b then decide_ltu fs a b else lts_generic a b) = Some r ->
               lts_generic a b = Some r \/ bv_lts (den E a) (den E b) = r).
  { intros a' b' r' H'. destruct (nonneg63 fs a' && nonneg63 fs b') eqn:NN; [|left; exact H'].
    apply andb_prop in NN as [N1 N2]. right.
    apply (lts_of_ltu_nonneg _ _ _ (nonneg63_sound _ N1) (nonneg63_sound _ N2)). apply decide_ltu_sound. exact H'. }
  destruct a as [x|k o| | | | | | | | |]; destruct b as [y|k' o'| | | | | | | | |];
    try (destruct (NN _ _ _ H) as [H'|H']; [exact (lts_generic_sound _ _ r H') | exact H']).
  - vp_bsplit. cbn [den]. symmetry. apply wlts_ok.
  - destruct (nonneg63 fs (VP k o) && nonneg63 fs (VP k' o')) eqn:NN0.
    { apply andb_prop in NN0 as [N1 N2].
      apply (lts_of_ltu_nonneg _ _ _ (nonneg63_sound _ N1) (nonneg63_sound _ N2)). apply decide_ltu_sound. exact H. }
    pose proof (syntactic_lts_sound (VP k o) (VP k' o')) as [S1 S2].
    destruct (PrimInt63.eqb k k' && below63 fs k o && below63 fs k o') eqn:Hk.
    + vp_bsplit. match goal with G : below63 fs _ o = true |- _ => apply below63_sound in G as (_ & _ & R1) end.
      match goal with G : below63 fs _ o' = true |- _ => apply below63_sound in G as (_ & _ & R2) end.
      unfold soff_ltb. rewrite wlts_w2Zs. apply lts_iff. rewrite R1, R2.
      destruct (Z.ltb_spec (w2Zs o) (w2Zs o')); lia.
    + destruct (fact_lookup fs (is_FSLt _ _)); [vp_bsplit; apply lts_iff; apply S1; reflexivity|].
      destruct (fact_lookup fs (is_FSLe _ _) || fact_lookup fs (is_FEq _ _)); [vp_bsplit; apply lts_iff; apply S2; reflexivity|].
      discriminate.
Qed.

Definition eq_generic (a b : sv) : option bool :=
      if fact_lookup fs (is_FNe a b) then Some false
      else if fact_lookup fs (is_FEq a b) then Some true
      else
        match a, b with
        | VP k o, VL y | VL y, VP k o =>
            match find_range fs k with
            | Some (lo, hi) =>
                if nowrap lo hi o then
                  (let vlo := wadd lo o in let vhi := wadd hi o in
                   if wltu y vlo || wltu vhi y then Some false else None)
                else None
            | None => None
            end
        | _, _ =>
            match decide_ltu fs a b with
            | Some true => Some false
            | _ => match decide_ltu fs b a with Some true => Some false | _ => None end
            end
        end.

Lemma eq_generic_sound : forall a b r, eq_generic a b = Some r -> bv_eqb (den E a) (den E b) = r.
Proof.
  intros a b r H. unfold eq_generic in H. apply eqb_iff.
  pose proof (syntactic_eq_sound a b) as [S1 S2].
  destruct (fact_lookup fs (is_FNe a b)); [vp_bsplit; apply S1; reflexivity|].
  destruct (fact_lookup fs (is_FEq a b)); [vp_bsplit; apply S2; reflexivity|].
  clear S1 S2.
  assert (G : match decide_ltu fs a b with
             | Some true => Some false
             | _ => match decide_ltu fs b a with Some true => Some false | _ => None end
             end = Some r -> if r then den E a = den E b else den E a <> den E b).
  { clear H. intros H. destruct (decide_ltu fs a b) as [[]|] eqn:D1.
    - vp_bsplit. apply decide_ltu_sound, ltu_iff in D1. intros X. rewrite X in D1. lia.
    - destruct (decide_ltu fs b a) as [[]|] eqn:D2; vp_bsplit. apply decide_ltu_sound, ltu_iff in D2. intros X. rewrite X in D2. lia.
    - destruct (decide_ltu fs b a) as [[]|] eqn:D2; vp_bsplit. apply decide_ltu_sound, ltu_iff in D2. intros X. rewrite X in D2. lia. }
  destruct a as [x|k o| | | | | | | | |]; destruct b as [y|k' o'| | | | | | | | |]; try exact (G H); clear G.
  - destruct (find_range fs k') as [[lo hi]|] eqn:Hr; [|discriminate]. destruct (nowrap lo hi o') eqn:Hn; [|discriminate].
    match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hc end; vp_bsplit.
    intros X. apply (ptr_lit_ne k' o' x lo hi Hr Hn Hc). rewrite <- X. apply den_VL.
  - destruct (find_range fs k) as [[lo hi]|] eqn:Hr; [|discriminate]. destruct (nowrap lo hi o) eqn:Hn; [|discriminate].
    match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hc end; vp_bsplit.
    intros X. apply (ptr_lit_ne k o y lo hi Hr Hn Hc). rewrite X. apply den_VL.
Qed.

Lemma decide_eq_s_sound : forall a b r, decide_eq_s fs a b = Some r -> bv_eqb (den E a) (den E b) = r.
Proof.
  intros a b r H. unfold decide_eq_s in H.
  destruct (sv_eqb a b) eqn:He.
  { vp_bsplit. apply eqb_iff. reflexivity. }
  clear He.

  assert (DZ : den E (VL wzero) = Z_to_bv 64 0) by reflexivity.
  match type of H with (match ?pre with Some _ => _ | None => _ end) = _ => destruct pre as [r0|] eqn:PRE end.
  { vp_bsplit.
    destruct a as [x|k o| | | | | | | | |]; destruct b as [y|k' o'| | | | | | | | |]; cbn beta iota in PRE;
    repeat match type of PRE with
    | None = Some _ => discriminate PRE
    | (if weqb ?y wzero then _ else _) = _ =>
        destruct (weqb y wzero) eqn:WY;
        [ apply weqb_eq in WY; subst y;
          first [ rewrite DZ; exact (decide_eq0_b_sound _ _ PRE)
                | apply decide_eq0_b_sound in PRE; rewrite DZ; unfold bv_eqb in *; rewrite Z.eqb_sym; exact PRE ]
        | clear WY; cbn beta iota in PRE ]
    end. }
  clear PRE.
  destruct a as [x|k o| | | | | | | | |]; destruct b as [y|k' o'| | | | | | | | |];
    try match goal with |- bv_eqb (den E ?a) (den E ?b) = ?r => exact (eq_generic_sound a b r H) end.
  - vp_bsplit. cbn [den]. unfold bv_eqb. rewrite !wbv_unsigned, weqb_eqb. reflexivity.
  - pose proof (syntactic_eq_sound (VP k o) (VP k' o')) as [S1 S2].
    destruct (PrimInt63.eqb k k') eqn:Hk.
    + vp_bsplit. unfold bv_eqb. rewrite !den_VPu, weqb_eqb.
      pose proof (evk_range k'). pose proof (w2Z_range o). pose proof (w2Z_range o').
      destruct (Z.eqb_spec (w2Z o) (w2Z o')) as [X|X].
      * rewrite X. apply Z.eqb_refl.
      * apply Z.eqb_neq. intros Y. apply X. exact (mod_add_cancel_l _ _ _ H0 H1 Y).
    + apply eqb_iff.
      destruct (fact_lookup fs (is_FNe _ _)); [vp_bsplit; apply S1; reflexivity|].
      destruct (fact_lookup fs (is_FEq _ _)); [vp_bsplit; apply S2; reflexivity|].
      discriminate.
Qed.

Lemma decide_eq_sound : forall a b r, decide_eq fs a b = Some r -> bv_eqb (den E a) (den E b) = r.
Proof.
  intros a b r H. unfold decide_eq in H.
  destruct (decide_eq_s fs a b) as [r'|] eqn:D; [injection H as <-; exact (decide_eq_s_sound a b r' D)|].
  cbv zeta in H. pose proof gaps_sound as HG. set (G := gaps fs) in *. clearbody G.
  destruct (lin_eq_G G fs a b) as [r'|] eqn:L; [injection H as <-; exact (lin_eq_G_sound G a b r' HG L)|].
  assert (NE : forall x y : word, bv_ltu x y = true -> bv_eqb x y = false /\ bv_eqb y x = false).
  { intros x y X. apply ltu_iff in X. split; apply eqb_iff; intros EQ; rewrite EQ in X; lia. }
  pose proof (decide_ltu_G_sound G HG) as DS.
  destruct (decide_ltu_G G fs a b) as [[]|] eqn:D1.
  - injection H as <-. exact (proj1 (NE _ _ (DS a b true D1))).
  - destruct (decide_ltu_G G fs b a) as [[]|] eqn:D2; try discriminate H; injection H as <-.
    + exact (proj2 (NE _ _ (DS b a true D2))).
    + pose proof (DS a b false D1) as X1. pose proof (DS b a false D2) as X2.
      apply ltu_iff in X1. apply ltu_iff in X2. apply eqb_iff. apply bv_eq. lia.
  - destruct (decide_ltu_G G fs b a) as [[]|] eqn:D2; try discriminate H. injection H as <-. exact (proj2 (NE _ _ (DS b a true D2))).
Qed.

Lemma decide_eq0_sound : forall v r, decide_eq0 fs v = Some r -> bv_eqb (den E v) (Z_to_bv 64 0) = r.
Proof.
  intros v r H. unfold decide_eq0 in H.
  destruct (decide_eq0_b fs v) as [r'|] eqn:D; [injection H as <-; exact (decide_eq0_b_sound v r' D)|].
  apply decide_eq_sound in H. cbn [den] in H. rewrite wbv_wzero in H. exact H.
Qed.

Lemma decide_branch_sound : forall c a b r, decide_branch fs c a b = Some r ->
  branch_taken c (den E a) (den E b) = r.
Proof.
  intros c a b r H. unfold decide_branch in H. unfold branch_taken.
  destruct c.
  - apply decide_eq_sound, H.
  - destruct (decide_eq fs a b) eqn:D; cbn [option_map] in H; vp_bsplit. rewrite (decide_eq_sound _ _ _ D). reflexivity.
  - apply decide_lts_sound, H.
  - destruct (decide_lts fs a b) eqn:D; cbn [option_map] in H; vp_bsplit. rewrite (decide_lts_sound _ _ _ D). reflexivity.
  - apply decide_ltu_sound, H.
  - destruct (decide_ltu fs a b) eqn:D; cbn [option_map] in H; vp_bsplit. rewrite (decide_ltu_sound _ _ _ D). reflexivity.
Qed.

Lemma cmp_z0 : forall z, weqb z wzero = true -> wbv z = Z_to_bv 64 0.
Proof. intros z Hzz. apply weqb_wzero_unsigned in Hzz. apply bv_eq. rewrite Hzz. reflexivity. Qed.
Lemma cmp_ne_ok : forall f t z, fact_holds E f -> den E t <> den E (VL z) ->
  fact_holds E (if weqb z wzero then match t with VAlu ALU_SLTU p q => FULt p q | VAlu ALU_SLT p q => FSLt p q | _ => f end else f).
Proof.
  intros f t z Hf H. destruct (weqb z wzero) eqn:Hzz; [|exact Hf].
  destruct t as [| |op p q| | | | | | | |]; try exact Hf. destruct op; try exact Hf;
    cbn [fact_holds]; cbn [den alu64 alu] in H; rewrite (cmp_z0 z Hzz) in H.
  - destruct (bv_lts (den E p) (den E q)) eqn:L; [apply lts_iff in L; exact L| exfalso; apply H; reflexivity].
  - destruct (bv_ltu (den E p) (den E q)) eqn:L; [apply ltu_iff in L; exact L| exfalso; apply H; reflexivity].
Qed.
Lemma cmp_one_ne_zero : Z_to_bv 64 1 = Z_to_bv 64 0 -> False.
Proof. intros H. apply (f_equal bv_unsigned) in H. vm_compute in H. discriminate H. Qed.
Lemma cmp_eq_ok : forall f t z, fact_holds E f -> den E t = den E (VL z) ->
  fact_holds E (if weqb z wzero then match t with VAlu ALU_SLTU p q => FULe q p | VAlu ALU_SLT p q => FSLe q p | _ => f end else f).
Proof.
  intros f t z Hf H. destruct (weqb z wzero) eqn:Hzz; [|exact Hf].
  destruct t as [| |op p q| | | | | | | |]; try exact Hf. destruct op; try exact Hf;
    cbn [fact_holds]; cbn [den alu64 alu] in H; rewrite (cmp_z0 z Hzz) in H.
  - destruct (bv_lts (den E p) (den E q)) eqn:L; [exfalso; exact (cmp_one_ne_zero H)| apply lts_iff in L; lia].
  - destruct (bv_ltu (den E p) (den E q)) eqn:L; [exfalso; exact (cmp_one_ne_zero H)| apply ltu_iff in L; lia].
Qed.
Lemma cmp_norm_sound : forall f, fact_holds E f -> fact_holds E (cmp_norm f).
Proof.
  intros f H. unfold cmp_norm. destruct f as [| | | |a b|a b| |]; try exact H.
  - destruct a, b; try exact H;
      first [ exact (cmp_eq_ok _ _ _ H H) | exact (cmp_eq_ok _ _ _ H (eq_sym H)) ].
  - destruct a, b; try exact H;
      first [ exact (cmp_ne_ok _ _ _ H H) | exact (cmp_ne_ok _ _ _ H (fun X => H (eq_sym X))) ].
Qed.

Lemma fact_of_branch_holds : forall c a b taken,
  branch_taken c (den E a) (den E b) = taken -> fact_holds E (fact_of_branch c a b taken).
Proof.
  intros c a b taken H. unfold fact_of_branch. apply cmp_norm_sound. unfold branch_taken in H.
  destruct c, taken; cbn [fact_of_branch0 fact_holds];
  first [ apply eqb_iff in H | apply negb_true_iff in H; apply eqb_iff in H | apply negb_false_iff in H; apply eqb_iff in H
        | apply lts_iff in H | apply negb_true_iff in H; apply lts_iff in H | apply negb_false_iff in H; apply lts_iff in H
        | apply ltu_iff in H | apply negb_true_iff in H; apply ltu_iff in H | apply negb_false_iff in H; apply ltu_iff in H ];
  cbn in H; solve [exact H | lia].
Qed.

Lemma align_weaken K m n : 0 <= m <= n -> K mod 2 ^ n = 0 -> K mod 2 ^ m = 0.
Proof. intros H HK. rewrite <- (mod_pow2_mod K m n), HK by lia. apply Zmod_0_l. Qed.

Definition eqm (m a b : Z) : Prop := a mod 2 ^ m = b mod 2 ^ m.
Lemma eqm_refl m a : eqm m a a. Proof. reflexivity. Qed.
Lemma eqm_sym m a b : eqm m a b -> eqm m b a. Proof. unfold eqm; intros; symmetry; assumption. Qed.
Lemma eqm_trans m a b c : eqm m a b -> eqm m b c -> eqm m a c. Proof. unfold eqm; intros; etransitivity; eassumption. Qed.
Lemma eqm_mod m n a : 0 <= m <= n -> eqm m (a mod 2 ^ n) a.
Proof. intros H. unfold eqm. apply mod_pow2_mod. lia. Qed.
Lemma eqm_mod64 m a : 0 <= m <= 63 -> eqm m (a mod two64) a.
Proof. intros H. unfold eqm. apply mod64_mod. lia. Qed.
Lemma eqm_wrap64 m a : 0 <= m <= 63 -> eqm m (bv_wrap 64 a) a.
Proof. intros H. unfold bv_wrap. rewrite bv_modulus_64. apply eqm_mod64. lia. Qed.
Lemma eqm_self m a : 0 <= m -> eqm m (a mod 2 ^ m) a.
Proof. intros H. apply eqm_mod. lia. Qed.
Lemma eqm_add m a a' b b' : eqm m a a' -> eqm m b b' -> eqm m (a + b) (a' + b').
Proof. unfold eqm. intros H1 H2. rewrite Zplus_mod, H1, H2, <- Zplus_mod. reflexivity. Qed.
Lemma eqm_sub m a a' b b' : eqm m a a' -> eqm m b b' -> eqm m (a - b) (a' - b').
Proof. unfold eqm. intros H1 H2. rewrite Zminus_mod, H1, H2, <- Zminus_mod. reflexivity. Qed.
Lemma eqm_add_mult m a k : 0 <= m -> eqm m (a + k * 2 ^ m) a.
Proof. intros H. unfold eqm. apply Z.mod_add. apply Z.pow_nonzero; lia. Qed.
Lemma eqm_small m a b : eqm m a b -> 0 <= a < 2 ^ m -> a = b mod 2 ^ m.
Proof. unfold eqm. intros H R. rewrite <- H. symmetry. apply Z.mod_small. exact R. Qed.

Lemma find_align_le k m : PrimInt63.leb m (find_align fs k) = true -> bv_unsigned (ev E k) mod 2 ^ (to_Z m) = 0.
Proof.
  intros H. rewrite leb_spec in H. pose proof (int_range m).
  apply (align_weaken _ _ (to_Z (find_align fs k))); [lia|]. apply find_align_sound.
Qed.

Lemma aligned_sound : forall a m, aligned fs a m = true -> to_Z m <= 62 ->
  bv_unsigned (den E a) mod 2 ^ (to_Z m) = 0.
Proof.
  intros a m H Hm. unfold aligned in H. pose proof (int_range m).
  destruct a as [x|k o| | | | | | | | |]; try discriminate H; vp_bsplit.
  - match goal with G : PrimInt63.land _ _ = _ |- _ => apply (f_equal to_Z) in G; rewrite land_mk, w2Z_wl, two63_eq, mod_pow2_mod in G by lia end.
    rewrite den_VL. assumption.
  - match goal with G : PrimInt63.land _ _ = _ |- _ => apply (f_equal to_Z) in G; rewrite land_mk, w2Z_wl, two63_eq, mod_pow2_mod in G by lia end.
    match goal with G : PrimInt63.leb _ _ = true |- _ => apply find_align_le in G end.
    rewrite den_VPu, mod64_mod, Zplus_mod by lia.
    match goal with G1 : ?a mod _ = 0, G2 : ?b mod _ = to_Z 0 |- _ => rewrite G1, G2 end.
    change (to_Z 0) with 0. apply Zmod_0_l.
Qed.

Lemma bv_swrap32_eqm m z : 0 <= m <= 32 -> eqm m (bv_swrap 32 z) z.
Proof.
  intros Hm. unfold bv_swrap, bv_wrap. change (bv_modulus 32) with (2 ^ 32). change (bv_half_modulus 32) with (2 ^ 31).
  replace z with ((z + 2 ^ 31) - 2 ^ 31) at 2 by lia.
  apply eqm_sub; [apply eqm_mod; lia|apply eqm_refl].
Qed.

Lemma low32_eqm m (w : word) : 0 <= m <= 32 -> eqm m (bv_unsigned (low32 w)) (bv_unsigned w).
Proof. intros Hm. rewrite low32_ext. apply eqm_mod. lia. Qed.

Lemma aluw_eqm m (a b : word) (g : bv 32 -> bv 32 -> bv 32) (f : Z -> Z -> Z) :
  0 <= m <= 32 ->
  (forall x y, bv_unsigned (g x y) = bv_wrap 32 (f (bv_unsigned x) (bv_unsigned y))) ->
  (forall x x' y y', eqm m x x' -> eqm m y y' -> eqm m (f x y) (f x' y')) ->
  eqm m (bv_unsigned (sext 64 (g (low32 a) (low32 b)))) (f (bv_unsigned a) (bv_unsigned b)).
Proof.
  intros Hm Hg Hf. unfold sext. rewrite bv_sign_extend_unsigned. unfold bv_signed. rewrite Hg.
  eapply eqm_trans; [apply eqm_wrap64; lia|]. eapply eqm_trans; [apply bv_swrap32_eqm; lia|].
  unfold bv_wrap. change (bv_modulus 32) with (2 ^ 32). eapply eqm_trans; [apply eqm_mod; lia|].
  apply Hf; apply low32_eqm; lia.
Qed.

Lemma low_bits_sound : forall v m x, to_Z m <= 63 -> low_bits fs v m = Some x ->
  to_Z x = bv_unsigned (den E v) mod 2 ^ (to_Z m).
Proof.
  induction v; intros m x Hm H; cbn [low_bits] in H; try discriminate H; pose proof (int_range m) as Rm.
  -   vp_bsplit. rewrite land_mk, w2Z_wl, two63_eq, mod_pow2_mod, den_VL by lia. reflexivity.
  -   destruct (PrimInt63.eqb k 0); [discriminate|].
    destruct (PrimInt63.leb m (find_align fs k)) eqn:Ha; [|discriminate]. vp_bsplit.
    apply find_align_le in Ha.
    rewrite land_mk, w2Z_wl, two63_eq, mod_pow2_mod, den_VPu, mod64_mod, Zplus_mod, Ha, Z.add_0_l by lia.
    symmetry. apply Z.mod_mod. apply Z.pow_nonzero; lia.
  -   destruct op; try discriminate H.
    + destruct (low_bits fs v1 m) as [x1|] eqn:L1; [|discriminate]. destruct (low_bits fs v2 m) as [x2|] eqn:L2; [|discriminate].
      vp_bsplit. specialize (IHv1 m x1 Hm L1). specialize (IHv2 m x2 Hm L2).
      rewrite land_mk, add_spec, wB_two63, two63_eq, mod_pow2_mod by lia.
      cbn [den alu64 alu]. rewrite bv_add_unsigned.
      apply eqm_small; [|apply Z.mod_pos_bound; apply Z.pow_pos_nonneg; lia].
      apply (eqm_trans _ _ (to_Z x1 + to_Z x2)); [apply eqm_self; lia|].
      apply eqm_sym. apply (eqm_trans _ _ (bv_unsigned (den E v1) + bv_unsigned (den E v2))); [apply eqm_wrap64; lia|].
      rewrite IHv1, IHv2. apply eqm_add; apply eqm_sym, eqm_self; lia.
    + destruct (low_bits fs v1 m) as [x1|] eqn:L1; [|discriminate]. destruct (low_bits fs v2 m) as [x2|] eqn:L2; [|discriminate].
      vp_bsplit. specialize (IHv1 m x1 Hm L1). specialize (IHv2 m x2 Hm L2).
      rewrite land_mk, sub_spec, add_spec, lsl_spec, wB_two63, two63_eq, mod_pow2_mod by lia. change (to_Z 1) with 1. rewrite Z.mul_1_l.
      cbn [den alu64 alu]. rewrite bv_sub_unsigned.
      apply eqm_small; [|apply Z.mod_pos_bound; apply Z.pow_pos_nonneg; lia].
      apply (eqm_trans _ _ ((to_Z x1 + (2 ^ to_Z m) mod 2 ^ 63) mod 2 ^ 63 - to_Z x2)); [apply eqm_self; lia|].
      apply (eqm_trans _ _ (to_Z x1 + 2 ^ to_Z m - to_Z x2)).
      { apply eqm_sub; [|apply eqm_refl]. apply (eqm_trans _ _ (to_Z x1 + (2 ^ to_Z m) mod 2 ^ 63)); [apply eqm_mod; lia|].
        apply eqm_add; [apply eqm_refl|apply eqm_mod; lia]. }
      replace (to_Z x1 + 2 ^ to_Z m - to_Z x2) with (to_Z x1 - to_Z x2 + 1 * 2 ^ to_Z m) by lia.
      apply (eqm_trans _ _ (to_Z x1 - to_Z x2)); [apply eqm_add_mult; lia|].
      apply eqm_sym. apply (eqm_trans _ _ (bv_unsigned (den E v1) - bv_unsigned (den E v2))); [apply eqm_wrap64; lia|].
      rewrite IHv1, IHv2. apply eqm_sub; apply eqm_sym, eqm_self; lia.
    + destruct v2; try discriminate H.
      destruct (low_bits fs v1 m) as [x1|] eqn:L1; [|discriminate]. vp_bsplit. specialize (IHv1 m x1 Hm L1).
      rewrite land_spec', IHv1, w2Z_wl, two63_eq. cbn [den alu64 alu]. rewrite bv_and_unsigned, wbv_unsigned.
      rewrite <- !Z.land_ones by lia.
      apply Z.bits_inj'; intros i Hi. rewrite !Z.land_spec, !tb_ones by lia.
      destruct (Z.ltb_spec i (to_Z m)), (Z.ltb_spec i 63); try lia; rewrite ?andb_true_r, ?andb_false_r; reflexivity.
  -   destruct op; try discriminate H; destruct (PrimInt63.leb m 32) eqn:H32; try discriminate H;
      rewrite leb_spec in H32; change (to_Z 32) with 32 in H32;
      destruct (low_bits fs v1 m) as [x1|] eqn:L1; try discriminate H; destruct (low_bits fs v2 m) as [x2|] eqn:L2; try discriminate H;
      vp_bsplit; specialize (IHv1 m x1 Hm L1); specialize (IHv2 m x2 Hm L2).
    + rewrite land_mk, add_spec, wB_two63, two63_eq, mod_pow2_mod by lia.
      cbn [den alu32 alu].
      apply eqm_small; [|apply Z.mod_pos_bound; apply Z.pow_pos_nonneg; lia].
      apply (eqm_trans _ _ (to_Z x1 + to_Z x2)); [apply eqm_self; lia|]. apply eqm_sym.
      eapply eqm_trans; [apply (aluw_eqm (to_Z m) (den E v1) (den E v2) bv_add Z.add); [lia|intros; apply bv_add_unsigned|intros; apply eqm_add; assumption]|].
      rewrite IHv1, IHv2. apply eqm_add; apply eqm_sym, eqm_self; lia.
    + rewrite land_mk, sub_spec, add_spec, lsl_spec, wB_two63, two63_eq, mod_pow2_mod by lia. change (to_Z 1) with 1. rewrite Z.mul_1_l.
      cbn [den alu32 alu].
      apply eqm_small; [|apply Z.mod_pos_bound; apply Z.pow_pos_nonneg; lia].
      apply (eqm_trans _ _ ((to_Z x1 + (2 ^ to_Z m) mod 2 ^ 63) mod 2 ^ 63 - to_Z x2)); [apply eqm_self; lia|].
      apply (eqm_trans _ _ (to_Z x1 + 2 ^ to_Z m - to_Z x2)).
      { apply eqm_sub; [|apply eqm_refl]. apply (eqm_trans _ _ (to_Z x1 + (2 ^ to_Z m) mod 2 ^ 63)); [apply eqm_mod; lia|].
        apply eqm_add; [apply eqm_refl|apply eqm_mod; lia]. }
      replace (to_Z x1 + 2 ^ to_Z m - to_Z x2) with (to_Z x1 - to_Z x2 + 1 * 2 ^ to_Z m) by lia.
      apply (eqm_trans _ _ (to_Z x1 - to_Z x2)); [apply eqm_add_mult; lia|]. apply eqm_sym.
      eapply eqm_trans; [apply (aluw_eqm (to_Z m) (den E v1) (den E v2) bv_sub Z.sub); [lia|intros; apply bv_sub_unsigned|intros; apply eqm_sub; assumption]|].
      rewrite IHv1, IHv2. apply eqm_sub; apply eqm_sym, eqm_self; lia.
Qed.

Lemma mask_log_sound : forall mask m, mask_log mask = Some m ->
  exists j, 1 <= j <= 63 /\ j <= to_Z m /\ w2Z mask = two64 - 2 ^ j.
Proof.
  intros mask m H. unfold mask_log in H.
  destruct (wt (wnot mask)) eqn:Ht; [discriminate|].
  set (x := wl (wnot mask)) in H.
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hc end; [|discriminate].
  injection H as Hm. apply andb_prop in Hc as [Hl Hn]. apply negb_true_iff, eqb_false_spec in Hn. apply int_eqb_eq in Hl.
  apply (f_equal to_Z) in Hl. rewrite land_spec', add_spec, wB_two63, two63_eq in Hl. change (to_Z 1) with 1 in Hl. change (to_Z 0) with 0 in Hl.
  assert (Hx0 : to_Z x <> 0) by (intros X; apply Hn; apply to_Z_inj; rewrite X; reflexivity).
  pose proof (int_range x) as Rx. rewrite two63_eq in Rx.
  assert (Hmask : w2Z mask = two64 - 1 - to_Z x).
  { pose proof (wnot_ok mask) as W. unfold w2Z in W at 1. rewrite Ht in W. subst x. lia. }
  destruct (Z.eq_dec (to_Z x) (2 ^ 63 - 1)) as [E63|NE].
  - exists 63. split; [lia|]. split; [|rewrite Hmask, E63; unfold two64; lia].
    rewrite <- Hm. replace (PrimInt63.add x 1) with 0%uint63 by (apply to_Z_inj; rewrite add_spec, E63; reflexivity).
    rewrite head0_zero. vm_compute. congruence.
  - rewrite Z.mod_small in Hl by lia.
    pose proof (pow2_of_land (to_Z x) ltac:(lia) Hl) as P. set (j := Z.log2 (to_Z x + 1)) in *.
    pose proof (Z.log2_nonneg (to_Z x + 1)) as Jn. fold j in Jn.
    assert (Hj : 1 <= j <= 62).
    { split.
      - destruct (Z.eq_dec j 0) as [J0|]; [|lia]. rewrite J0 in P. change (2 ^ 0) with 1 in P. lia.
      - destruct (Z.le_gt_cases j 62) as [|G]; [assumption|]. assert (2 ^ 63 <= 2 ^ j) by (apply Z.pow_le_mono_r; lia). lia. }
    exists j. split; [lia|]. split; [|rewrite Hmask; unfold two64; lia].
    rewrite <- Hm, sub_spec, (head0_pow2 j) by (lia || (rewrite add_spec, wB_two63, two63_eq; change (to_Z 1) with 1; rewrite Z.mod_small; lia)).
    change (to_Z 62) with 62. rewrite wB_two63, Z.mod_small by (unfold two63; lia). lia.
Qed.

Lemma mask_bits_sound : forall mask mb, mask_bits mask = Some mb ->
  0 <= to_Z mb <= 62 /\ wt mask = false /\ w2Z mask < 2 ^ (to_Z mb).
Proof.
  intros mask mb H. unfold mask_bits in H.
  destruct (wt mask) eqn:Ht; [discriminate|].
  destruct (PrimInt63.leb bit62i (wl mask)) eqn:Hb; [discriminate|].
  injection H as Hm.
  assert (Hb' : ~ to_Z bit62i <= to_Z (wl mask)) by (rewrite <- leb_spec, Hb; discriminate). clear Hb. rewrite to_Z_bit62i in Hb'.
  assert (Hw : w2Z mask = to_Z (wl mask)) by (unfold w2Z; rewrite Ht; lia).
  rewrite Hw. pose proof (int_range (wl mask)) as R.
  destruct (Z.eq_dec (to_Z (wl mask)) 0) as [Z0|NZ].
  - replace (wl mask) with 0%uint63 in * by (apply to_Z_inj; rewrite Z0; reflexivity).
    rewrite head0_zero in Hm. subst mb. change (to_Z (63 - 63)%uint63) with 0. change (to_Z 0) with 0. simpl. lia.
  - pose proof (head0_spec (wl mask) ltac:(lia)) as Hs. rewrite wB_two63, two63_eq in Hs. change (2 ^ 63 / 2) with (2 ^ 62) in Hs.
    pose proof (int_range (PrimInt63.head0 (wl mask))) as Rh. set (h := to_Z (PrimInt63.head0 (wl mask))) in *.
    assert (Hh1 : 1 <= h).
    { destruct (Z.le_gt_cases 1 h); [assumption|]. assert (h = 0) by lia. rewrite H0 in Hs. change (2 ^ 0) with 1 in Hs. lia. }
    assert (Hh2 : h <= 62).
    { destruct (Z.le_gt_cases h 62); [assumption|]. assert (2 ^ 63 <= 2 ^ h) by (apply Z.pow_le_mono_r; lia).
      assert (2 ^ h <= 2 ^ h * to_Z (wl mask)) by nia. lia. }
    assert (Hmb : to_Z mb = 63 - h) by (subst mb; rewrite sub_spec, wB_two63; change (to_Z 63) with 63; fold h; apply Z.mod_small; unfold two63; lia).
    rewrite Hmb. split; [lia|]. split; [reflexivity|].
    replace (2 ^ 63) with (2 ^ h * 2 ^ (63 - h)) in Hs by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
    assert (0 < 2 ^ h) by (apply Z.pow_pos_nonneg; lia). nia.
Qed.

Lemma masked_lit_sound : forall a mask mb x, mask_bits mask = Some mb -> low_bits fs a mb = Some x ->
  den E (VL (wlit (PrimInt63.land x (wl mask)))) = alu64 ALU_AND (den E a) (den E (VL mask)).
Proof.
  intros a mask mb x HB HL. apply mask_bits_sound in HB as (Rmb & Ht & Hlt).
  apply (low_bits_sound a mb x) in HL; [|lia].
  apply bv_eq. cbn [den alu64 alu]. rewrite bv_and_unsigned, !wbv_unsigned, wlit_ok, land_spec', HL.
  replace (to_Z (wl mask)) with (w2Z mask) by (unfold w2Z; rewrite Ht; lia).
  pose proof (w2Z_range mask) as Rm.
  rewrite <- Z.land_ones by lia. apply Z.bits_inj'; intros i Hi. rewrite !Z.land_spec, tb_ones by lia.
  destruct (Z.ltb_spec i (to_Z mb)); [rewrite andb_true_r; reflexivity|].
  rewrite (testbit_high (w2Z mask) (to_Z mb)) by lia. rewrite !andb_false_r. reflexivity.
Qed.

Lemma land_negpow2 v j : 0 <= v < two64 -> 0 <= j <= 64 -> Z.land v (two64 - 2 ^ j) = v - v mod 2 ^ j.
Proof.
  intros Hv Hj. rewrite two64_eq in *.
  replace (2 ^ 64 - 2 ^ j) with (Z.ones (64 - j) * 2 ^ j) by (rewrite <- pow2_m1_ones, Z.mul_sub_distr_r, <- Z.pow_add_r by lia; replace (64 - j + j) with 64 by lia; lia).
  replace (v - v mod 2 ^ j) with (v / 2 ^ j * 2 ^ j) by (pose proof (Z.div_mod v (2 ^ j) ltac:(apply Z.pow_nonzero; lia)); lia).
  apply Z.bits_inj'; intros i Hi. rewrite Z.land_spec, !tb_mul_pow2 by lia.
  destruct (Z.leb_spec j i); cbn [andb]; [|rewrite andb_false_r; reflexivity].
  rewrite tb_ones, Z.div_pow2_bits by lia. replace (i - j + j) with i by lia.
  destruct (Z.ltb_spec (i - j) (64 - j)); [rewrite andb_true_r; reflexivity|].
  rewrite (testbit_high v 64) by lia. reflexivity.
Qed.

Lemma ptr_mask_sound : forall k o mask m, mask_log mask = Some m ->
  PrimInt63.leb m (find_align fs k) = true ->
  den E (VP k (wand o mask)) = alu64 ALU_AND (den E (VP k o)) (den E (VL mask)).
Proof.
  intros k o mask m HM HA. apply mask_log_sound in HM as (j & Hj & Hjm & Hmask).
  apply find_align_le in HA. pose proof (int_range m).
  assert (HK : bv_unsigned (ev E k) mod 2 ^ j = 0) by (apply (align_weaken _ j (to_Z m)); [lia|exact HA]).
  pose proof (evk_range k) as RK. pose proof (w2Z_range o) as Ro.
  apply bv_eq. cbn [den alu64 alu]. rewrite bv_and_unsigned, !bv_add_unsigned, !wbv_unsigned, wand_ok, Hmask.
  unfold bv_wrap. rewrite bv_modulus_64.
  assert (Rv : 0 <= (bv_unsigned (ev E k) + w2Z o) mod two64 < two64) by (apply Z.mod_pos_bound; unfold two64; lia).
  rewrite !land_negpow2 by lia.
  rewrite mod64_mod, (Zplus_mod (bv_unsigned (ev E k)) (w2Z o) (2 ^ j)), HK, Z.add_0_l, Z.mod_mod by (lia || (apply Z.pow_nonzero; lia)).
  assert (Rr : 0 <= w2Z o mod 2 ^ j <= w2Z o) by (split; [apply Z.mod_pos_bound; apply Z.pow_pos_nonneg; lia| apply Z.mod_le; try lia; apply Z.pow_pos_nonneg; lia]).
  assert (Rr2 : w2Z o mod 2 ^ j <= (bv_unsigned (ev E k) + w2Z o) mod two64).
  { pose proof (mod64_mod (bv_unsigned (ev E k) + w2Z o) j ltac:(lia)) as X.
    rewrite (Zplus_mod (bv_unsigned (ev E k)) (w2Z o) (2 ^ j)), HK, Z.add_0_l, Z.mod_mod in X by (apply Z.pow_nonzero; lia).
    rewrite <- X. apply Z.mod_le; [lia|apply Z.pow_pos_nonneg; lia]. }
  replace (bv_unsigned (ev E k) + (w2Z o - w2Z o mod 2 ^ j)) with ((bv_unsigned (ev E k) + w2Z o) - w2Z o mod 2 ^ j) by lia.
  rewrite <- Zminus_mod_idemp_l. apply Z.mod_small. lia.
Qed.

Lemma den_sv_and_f : forall a b, den E (sv_and_f fs a b) = alu64 ALU_AND (den E a) (den E b).
Proof.
  intros a b. unfold sv_and_f. cbv zeta.
  destruct a as [x|k o|? ? ?|? ? ?|? ? ?|? ? ?|? ? ? ?|? ? ? ?|? ? ? ?|? ? ? ?|? ?];
  destruct b as [mask|? ?|? ? ?|? ? ?|? ? ?|? ? ?|? ? ? ?|? ? ? ?|? ? ? ?|? ? ? ?|? ?]; try apply den_sv_alu.
  all: try (destruct (mask_log mask) as [m|] eqn:HM;
            [destruct (negb (PrimInt63.eqb k 0) && PrimInt63.leb m (find_align fs k)) eqn:HC;
             [apply andb_prop in HC as [_ HC]; exact (ptr_mask_sound k o mask m HM HC)|]|]).
  all: destruct (mask_bits mask) as [mb|] eqn:HB; try apply den_sv_alu.
  all: match goal with G : mask_bits ?mask = Some ?mb |- den E (match low_bits fs ?a ?mb with _ => _ end) = _ =>
         destruct (low_bits fs a mb) as [x'|] eqn:HL; [exact (masked_lit_sound a mask mb x' G HL)|apply den_sv_alu] end.
Qed.

Lemma den_add_lit : forall x c, den E (add_lit x c) = bv_add (den E x) (wbv c).
Proof.
  intros x c. unfold add_lit.
  destruct x as [y|k o| | | | | | | | |].
  1: { cbn [den]. rewrite wbv_wadd. reflexivity. }
  1: { cbn [den]. rewrite wbv_wadd. bv_solve. }
  all: destruct (weqb c wzero) eqn:Hc;
      [ apply weqb_eq in Hc; subst c; apply bv_eq; rewrite bv_add_unsigned, wbv_unsigned, wzero_ok, Z.add_0_r;
        symmetry; apply bv_wrap_small; apply bv_unsigned_in_range
      | rewrite den_add_lit_fold; reflexivity ].
Qed.

Definition oden (rx : option sv) : word := match rx with Some x => den E x | None => Z_to_bv 64 0 end.

Lemma split_base_sound : forall v k o rx, split_base v = Some (k, o, rx) ->
  den E v = ((ev E k + wbv o) + oden rx)%bv.
Proof.
  intros v k o rx H. unfold split_base in H.
  destruct v as [|k' o'|op x y| | | | | | | |]; try discriminate H.
  - injection H as <- <- <-. cbn [den oden]. bv_solve.
  - destruct op; try discriminate H.
    destruct x as [|kx ox| | | | | | | | |];
      [ destruct y as [|ky oy| | | | | | | | |]; try discriminate H; injection H as <- <- <-; cbn [den oden alu64 alu]; bv_solve
      | injection H as <- <- <-; cbn [den oden alu64 alu]; bv_solve
      | destruct y as [|ky oy| | | | | | | | |]; try discriminate H; injection H as <- <- <-; cbn [den oden alu64 alu]; bv_solve .. ].
Qed.

Lemma sub_fold_sound : forall a b r, sub_fold a b = Some r -> den E r = alu64 ALU_SUB (den E a) (den E b).
Proof.
  intros a b r H. unfold sub_fold in H.
  destruct (split_base a) as [[[k1 o1] ra]|] eqn:SA; [|discriminate].
  destruct (split_base b) as [[[k2 o2] rb]|] eqn:SB; [|discriminate].
  destruct (PrimInt63.eqb k1 k2) eqn:HK; [|discriminate]. apply int_eqb_eq in HK. subst k2.
  cbv zeta in H. injection H as <-.
  rewrite (split_base_sound a k1 o1 ra SA), (split_base_sound b k1 o2 rb SB).
  cbn [alu64 alu].
  destruct ra as [x|]; destruct rb as [y|]; cbn [den oden]; rewrite ?den_add_lit, ?wbv_wsub; cbn [den alu64 alu]; bv_solve.
Qed.

Lemma low_lim_val : forall lo, 0 < to_Z lo < 8 -> w2Z (low_lim lo) = 2 ^ (8 * to_Z lo) - 1.
Proof.
  intros lo Hlo. unfold low_lim, w2Z. cbn [wt wl].
  assert (L3 : to_Z (PrimInt63.lsl lo 3) = 8 * to_Z lo).
  { rewrite Uint63.lsl_spec. change (2 ^ to_Z 3%uint63) with 8. rewrite Z.mod_small; [lia|]. rewrite wB_two63. unfold two63. lia. }
  assert (P56 : 1 <= 2 ^ (8 * to_Z lo) <= 2 ^ 56) by (split; [change 1 with (2 ^ 0)|]; apply Z.pow_le_mono_r; lia).
  assert (P : to_Z (PrimInt63.lsl 1 (PrimInt63.lsl lo 3)) = 2 ^ (8 * to_Z lo)).
  { rewrite Uint63.lsl_spec, L3. change (to_Z 1%uint63) with 1. rewrite Z.mul_1_l. apply Z.mod_small.
    rewrite wB_two63. unfold two63. change (2 ^ 56) with 72057594037927936 in P56. lia. }
  rewrite Uint63.sub_spec, P. change (to_Z 1%uint63) with 1. rewrite Z.mod_small; [lia|].
  rewrite wB_two63. unfold two63. change (2 ^ 56) with 72057594037927936 in P56. lia.
Qed.

Lemma or_shl_ins : forall j X Y, 0 < j < 8 -> 0 <= X < two64 -> 0 <= Y < 2 ^ (8 * j) ->
  Z.lor ((X * 2 ^ (8 * j)) mod two64) Y = ins_Z j (8 - j) Y X.
Proof.
  intros j X Y Hj HX HY. unfold ins_Z. rewrite two64_eq in *. rewrite pow2_m1_ones.
  replace (8 * (8 - j)) with (64 - 8 * j) by lia.
  rewrite <- Z.shiftl_mul_pow2 by lia. rewrite <- (Z.land_ones _ 64) by lia.
  assert (TYhi : forall m, 8 * j <= m -> Z.testbit Y m = false).
  { intros m Hm. destruct (Z.eq_dec Y 0) as [->|NZ]; [apply Z.bits_0|]. apply Z.bits_above_log2; [lia|].
    apply Z.log2_lt_pow2; [lia|]. eapply Z.lt_le_trans; [apply (proj2 HY)|]. apply Z.pow_le_mono_r; lia. }
  apply Z.bits_inj'; intros m Hm.
  rewrite Z.lor_spec, Z.land_spec, Z.shiftl_spec by lia.
  rewrite Z.lor_spec, Z.land_spec, Z.lnot_spec, Z.shiftl_spec, Z.shiftl_spec, Z.land_spec by lia.
  destruct (Z.lt_ge_cases m (8 * j)) as [LT|GE].
  - rewrite !(Z.testbit_neg_r _ (m - 8 * j)) by lia. rewrite (Z.ones_spec_low 64 m) by lia.
    cbn [negb]. destruct (Z.testbit Y m); reflexivity.
  - rewrite (TYhi m GE). destruct (Z.lt_ge_cases m 64) as [L64|G64].
    + rewrite (Z.ones_spec_low 64 m) by lia. rewrite (Z.ones_spec_low (64 - 8 * j) (m - 8 * j)) by lia.
      destruct (Z.testbit X (m - 8 * j)); reflexivity.
    + rewrite (Z.ones_spec_high 64 m) by lia. rewrite (Z.ones_spec_high (64 - 8 * j) (m - 8 * j)) by lia.
      destruct (Z.testbit X (m - 8 * j)); reflexivity.
Qed.

Lemma or_ins1_sound : forall x s y r, or_ins1 fs x s y = Some r ->
  den E r = alu64 ALU_OR (den E (VAlu ALU_SLL x s)) (den E y).
Proof.
  intros x s y r H. unfold or_ins1 in H. destruct s as [c| | | | | | | | | |]; try discriminate.
  match type of H with (if ?cnd then _ else _) = _ => destruct cnd eqn:C; [|discriminate] end. injection H as <-.
  apply andb_prop in C as [C LE]. apply andb_prop in C as [C J8]. apply andb_prop in C as [M8 J0].
  apply Uint63.eqb_correct in M8. apply Uint63.ltb_spec in J0. apply Uint63.ltb_spec in J8.
  change (to_Z 0%uint63) with 0 in J0. change (to_Z 8%uint63) with 8 in J8.
  set (j := PrimInt63.lsr (shamt6 c) 3) in *.
  pose proof (shamt6_range c) as SR.
  assert (JV : to_Z j = to_Z (shamt6 c) / 8) by (subst j; rewrite Uint63.lsr_spec; reflexivity).
  assert (SH : to_Z (shamt6 c) = 8 * to_Z j).
  { apply (f_equal to_Z) in M8. rewrite Uint63.land_spec' in M8. change (to_Z 7%uint63) with (Z.ones 3) in M8. change (to_Z 0%uint63) with 0 in M8.
    rewrite Z.land_ones in M8 by lia. change (2 ^ 3) with 8 in M8.
    pose proof (Z.div_mod (to_Z (shamt6 c)) 8 ltac:(lia)) as DM. lia. }
  rewrite wleu_w2Z in LE. apply Z.leb_le in LE. rewrite low_lim_val in LE by lia.
  pose proof (sv_bounds_hi y) as BY. pose proof (bv_unsigned_in_range _ (den E y)) as RY. pose proof (bv_unsigned_in_range _ (den E x)) as RX.
  rewrite bv_modulus_64 in RX, RY.
  rewrite den_sv_ins.
  2: { unfold width_ok. rewrite Uint63.sub_spec. change (to_Z 8%uint63) with 8. rewrite Z.mod_small by (rewrite wB_two63; unfold two63; lia). lia. }
  rewrite Uint63.sub_spec. change (to_Z 8%uint63) with 8. rewrite Z.mod_small by (rewrite wB_two63; unfold two63; lia).
  apply bv_eq. rewrite Z_to_bv_unsigned. cbn [den alu64 alu]. rewrite bv_or_unsigned, bv_shiftl_unsigned, shamt6_bv, SH.
  rewrite Z.shiftl_mul_pow2 by lia. unfold bv_wrap. rewrite bv_modulus_64.
  rewrite <- (or_shl_ins (to_Z j)) by lia.
  apply Z.mod_small. split.
  - apply Z.lor_nonneg. split; [apply Z.mod_pos_bound; unfold two64; lia| lia].
  -
    assert (P56 : 2 ^ (8 * to_Z j) <= 2 ^ 56) by (apply Z.pow_le_mono_r; lia).
    assert (L1 : 0 <= (bv_unsigned (den E x) * 2 ^ (8 * to_Z j)) mod two64 < two64) by (apply Z.mod_pos_bound; unfold two64; lia).
    assert (L2 : 0 <= bv_unsigned (den E y) < two64) by (unfold two64 in *; lia).
    rewrite two64_eq in L1, L2 |- *.
    set (A := (bv_unsigned (den E x) * 2 ^ (8 * φ%uint63 j)) mod 2 ^ 64) in *. set (B := bv_unsigned (den E y)) in *.
    destruct (Z.eq_dec (Z.lor A B) 0) as [->|NZ]; [lia|].
    apply (Z.log2_lt_pow2 (Z.lor A B) 64); [pose proof (Z.lor_nonneg A B); lia|].
    rewrite Z.log2_lor by lia. apply Z.max_lub_lt.
    + destruct (Z.eq_dec A 0) as [->|]; [cbn; lia| apply Z.log2_lt_pow2; lia].
    + destruct (Z.eq_dec B 0) as [->|]; [cbn; lia| apply Z.log2_lt_pow2; lia].
Qed.

Lemma or_ins_fold_sound : forall a b r, or_ins_fold fs a b = Some r -> den E r = alu64 ALU_OR (den E a) (den E b).
Proof.
  intros a b r H. unfold or_ins_fold in H.
  destruct (match a with VAlu ALU_SLL x s => or_ins1 fs x s b | _ => None end) as [r1|] eqn:A1.
  - injection H as <-. destruct a as [| | op x s| | | | | | | |]; try discriminate A1. destruct op; try discriminate A1.
    exact (or_ins1_sound x s b r1 A1).
  - destruct b as [| | op x s| | | | | | | |]; try discriminate H. destruct op; try discriminate H.
    rewrite (or_ins1_sound x s a r H). cbn [alu64 alu]. apply bv_eq. rewrite !bv_or_unsigned. apply Z.lor_comm.
Qed.

Lemma srlsll_core : forall x k k', shamt6 k = shamt6 k' ->
  bv_unsigned (den E x) * 2 ^ to_Z (shamt6 k) < 2 ^ 64 ->
  den E x = alu64 ALU_SRL (den E (VAlu ALU_SLL x (VL k))) (den E (VL k')).
Proof.
  intros x k k' SK B. pose proof (shamt6_range k) as SR.
  pose proof (bv_unsigned_in_range _ (den E x)) as XR. rewrite bv_modulus_64 in XR.
  set (s := to_Z (shamt6 k)) in *. set (X := bv_unsigned (den E x)) in *.
  assert (PS : 0 < 2 ^ s) by (apply Z.pow_pos_nonneg; lia).
  cbn [den alu64 alu]. apply bv_eq. symmetry.
  rewrite bv_shiftr_unsigned, bv_shiftl_unsigned, !shamt6_bv, <- SK. fold s.
  rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. unfold bv_wrap. rewrite bv_modulus_64. fold X.
  rewrite Z.mod_small by (unfold two64; nia). rewrite Z.div_mul by lia. reflexivity.
Qed.

Lemma srlsll_fold_f_sound : forall a b r, srlsll_fold_f fs a b = Some r -> den E r = alu64 ALU_SRL (den E a) (den E b).
Proof.
  intros a b r H. unfold srlsll_fold_f in H.
  destruct a as [| | op x kk| | | | | | | |]; try discriminate H. destruct op; try discriminate H.
  destruct kk as [k| | | | | | | | | |]; try discriminate H. destruct b as [k'| | | | | | | | | |]; try discriminate H.
  destruct (PrimInt63.eqb (shamt6 k) (shamt6 k')) eqn:SK; [|discriminate H]. apply Uint63.eqb_correct in SK.
  cbv zeta in H.
  pose proof (shamt6_range k) as SR.
  pose proof (bv_unsigned_in_range _ (den E x)) as XR. rewrite bv_modulus_64 in XR.
  set (s := to_Z (shamt6 k)) in *.
  assert (PS : 0 < 2 ^ s) by (apply Z.pow_pos_nonneg; lia).
  assert (P64 : 2 ^ 64 = 2 ^ s * 2 ^ (64 - s)) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
  assert (PR : 0 < 2 ^ (64 - s)) by (apply Z.pow_pos_nonneg; lia).
  destruct (weqb (wsrl (wsll (snd (sv_bounds fs x)) k) k) (snd (sv_bounds fs x))) eqn:RT.
  - injection H as <-. apply (srlsll_core x k k' SK). fold s.
    set (u := snd (sv_bounds fs x)) in *.
    apply (proj1 (weqb_w2Z _ _)) in RT. unfold wsrl, wsll in RT.
    rewrite wsrl_k_ok, wsll_k_ok in RT by lia. fold s in RT.
    pose proof (sv_bounds_hi x) as UB. fold u in UB.
    pose proof (w2Z_range u) as UR.
    assert (NW : w2Z u * 2 ^ s < 2 ^ 64).
    { destruct (Z.lt_ge_cases (w2Z u * 2 ^ s) (2 ^ 64)) as [L|G]; [exact L| exfalso].
      assert (M : (w2Z u * 2 ^ s) mod 2 ^ 64 <= w2Z u * 2 ^ s - 2 ^ 64).
      { rewrite <- (Z_mod_plus_full (w2Z u * 2 ^ s) (-1) (2 ^ 64)). replace (w2Z u * 2 ^ s + -1 * 2 ^ 64) with (w2Z u * 2 ^ s - 2 ^ 64) by lia.
        apply Z.mod_le; [lia| lia]. }
      assert (D : (w2Z u * 2 ^ s) mod 2 ^ 64 / 2 ^ s <= (w2Z u * 2 ^ s - 2 ^ 64) / 2 ^ s) by (apply Z.div_le_mono; lia).
      rewrite RT in D. replace (w2Z u * 2 ^ s - 2 ^ 64) with ((w2Z u - 2 ^ (64 - s)) * 2 ^ s) in D by (rewrite P64; lia).
      rewrite Z.div_mul in D by lia. lia. }
    nia.
  - destruct (decide_ltu fs (VL (wsrl wones k)) x) as [[]|] eqn:D; try discriminate H. injection H as <-.
    apply (srlsll_core x k k' SK). fold s.
    apply decide_ltu_sound, ltu_iff in D. rewrite den_VL in D. unfold wsrl in D. rewrite wsrl_k_ok in D by lia. fold s in D.
    change (w2Z wones) with (2 ^ 64 - 1) in D.
    assert (Q : (2 ^ 64 - 1) / 2 ^ s = 2 ^ (64 - s) - 1).
    { rewrite P64. replace (2 ^ s * 2 ^ (64 - s) - 1) with ((2 ^ (64 - s) - 1) * 2 ^ s + (2 ^ s - 1)) by lia.
      rewrite Z.div_add_l by lia. rewrite Z.div_small by lia. lia. }
    rewrite Q in D. nia.
Qed.

Lemma zero_top_ok ds k : zero_top ds = Some k -> (1 <= k <= 7)%nat /\ ds = BD.brange 0 k ++ repeat BD.BZ (8 - k).
Proof.
  unfold zero_top. intros H.
  repeat match type of H with (if ?c then _ else _) = _ =>
    let Hc := fresh in destruct c eqn:Hc; [injection H as <-; apply BDP.bsrcs_eqb_eq in Hc; split; [lia|exact Hc] |] end.
  discriminate H.
Qed.
Lemma den_refold_f : forall r, den E (refold_f fs r) = den E r.
Proof.
  intros r. unfold refold_f. destruct (BD.bdesc r) as [[[y|] ds]|] eqn:Hd; try reflexivity.
  destruct (zero_top ds) as [k|] eqn:Hzt; [|reflexivity].
  destruct (wltu (snd (sv_bounds fs y)) (ext_lim false (BD.nat2int k))) eqn:Hb; [|reflexivity].
  destruct (zero_top_ok ds k Hzt) as [Hk ->].
  pose proof (BDP.bdesc_ok E r _ Hd) as D.
  rewrite <- (BDP.desc_slice_eq E y r 0 k ltac:(lia) ltac:(lia) D).
  pose proof (BDP.nat2int_ok k ltac:(lia)) as NK.
  rewrite wltu_w2Z, ext_lim_val in Hb by (rewrite NK; lia). apply Z.ltb_lt in Hb. rewrite NK in Hb.
  pose proof (sv_bounds_hi y) as BY. pose proof (U_range y) as RY.
  cbn [den]. unfold ext_word. change (to_Z (BD.nat2int 0)) with 0. rewrite NK.
  rewrite ext_Z_small_id by lia. symmetry. apply Z_to_bv_bv_unsigned.
Qed.

Lemma find_link_holds : forall fs' k s sh, Forall (fact_holds E) fs' -> find_link fs' k s = Some sh ->
  exists c, PrimInt63.eqb (shamt6 c) 3%uint63 = true /\
    den E (VP sh wzero) = den E (VAlu ALU_ADD (VAlu ALU_SRL (VP k wzero) (VL c)) (VL s)).
Proof.
  induction fs' as [|f fs' IH]; intros k s sh HF H; cbn [find_link] in H; [discriminate|].
  inversion HF as [|f' l Hf HF']; subst.
  destruct (is_link k s f) as [sh'|] eqn:L; [|exact (IH k s sh HF' H)]. injection H as <-.
  unfold is_link in L. destruct f as [| | | |x y| | |]; try discriminate L.
  destruct x as [|sh0 z| | | | | | | | |]; try discriminate L.
  destruct y as [| |op y1 y2| | | | | | | |]; try discriminate L. destruct op; try discriminate L.
  destruct y1 as [| |op1 u1 u2| | | | | | | |]; try discriminate L. destruct op1; try discriminate L.
  destruct u1 as [|k' z'| | | | | | | | |]; try discriminate L. destruct u2 as [c| | | | | | | | | |]; try discriminate L.
  destruct y2 as [s'| | | | | | | | | |]; try discriminate L.
  destruct (weqb z wzero && PrimInt63.eqb k' k && weqb z' wzero && PrimInt63.eqb (shamt6 c) 3%uint63 && weqb s' s) eqn:C; [|discriminate L].
  injection L as <-. apply andb_prop in C as [C S']. apply andb_prop in C as [C SH]. apply andb_prop in C as [C Z']. apply andb_prop in C as [Z0 K'].
  apply weqb_eq in Z0. apply weqb_eq in Z'. apply weqb_eq in S'. apply Uint63.eqb_correct in K'. subst z z' s' k'.
  exists c. split; [exact SH| exact Hf].
Qed.

Lemma shadow_fold_x1_sound : forall k o x c s sh,
  PrimInt63.eqb (shamt6 c) 3%uint63 && PrimInt63.leb 3%uint63 (find_align fs k) && negb (wt o)
    && negb (add_carries (snd (sv_bounds fs x)) o)
    && negb (add_carries (snd (var_bounds fs k)) (snd (sv_bounds fs (sv_alu ALU_ADD x (VL o))))) = true ->
  find_link fs k s = Some sh ->
  den E (VAlu ALU_ADD (VP sh wzero) (VAlu ALU_SRL (sv_alu ALU_ADD x (VL o)) (VL (wlit 3%uint63))))
  = alu64 ALU_ADD (den E (VAlu ALU_SRL (VAlu ALU_ADD (VP k o) x) (VL c))) (den E (VL s)).
Proof.
  intros k o x c s sh C FL.
  apply andb_prop in C as [C NC2]. apply andb_prop in C as [C NC1]. apply andb_prop in C as [C WT]. apply andb_prop in C as [SH3 AL].
  destruct (find_link_holds fs k s sh Hfs FL) as (c' & SH3' & LK).
  pose proof (find_align_sound k) as ALG. apply Uint63.leb_spec in AL. change (to_Z 3%uint63) with 3 in AL.
  assert (K8 : bv_unsigned (ev E k) mod 8 = 0).
  { pose proof (int_range (find_align fs k)) as RA.
    destruct (Z_lt_ge_dec (to_Z (find_align fs k)) 64) as [LT|GE].
    - change 8 with (2 ^ 3). apply (align_weaken _ 3 (to_Z (find_align fs k))); [lia| exact ALG].
    - pose proof (bv_unsigned_in_range 64 (ev E k)) as R. rewrite bv_modulus_64 in R.
      assert (P : two64 <= 2 ^ to_Z (find_align fs k)) by (rewrite two64_eq; apply Z.pow_le_mono_r; lia).
      rewrite Z.mod_small in ALG by lia. rewrite ALG. reflexivity. }
  apply Uint63.eqb_correct in SH3. apply Uint63.eqb_correct in SH3'.
  pose proof (bv_unsigned_in_range 64 (ev E k)) as RK. rewrite bv_modulus_64 in RK.
  pose proof (bv_unsigned_in_range 64 (den E x)) as RX. rewrite bv_modulus_64 in RX.
  pose proof two64_eq as T64.
  apply negb_true_iff in WT. apply negb_true_iff in NC1. apply negb_true_iff in NC2.
  assert (N1 : ~ two64 <= w2Z (snd (sv_bounds fs x)) + w2Z o) by (rewrite <- add_carries_iff, NC1; discriminate).
  assert (N2 : ~ two64 <= w2Z (snd (var_bounds fs k)) + w2Z (snd (sv_bounds fs (sv_alu ALU_ADD x (VL o)))))
    by (rewrite <- add_carries_iff, NC2; discriminate).
  pose proof (sv_bounds_hi x) as BX.
  pose proof (sv_bounds_hi (sv_alu ALU_ADD x (VL o))) as BXO.
  pose proof (var_bounds_sound k) as BK. unfold inb in BK. destruct BK as [_ BK].
  rewrite den_VPu, wzero_ok, Z.add_0_r, Z.mod_small in BK by lia.
  assert (O0 : 0 <= w2Z o) by (unfold w2Z; destruct (wt o); pose proof (int_range (wl o)); lia).

  assert (DXO : bv_unsigned (den E (sv_alu ALU_ADD x (VL o))) = bv_unsigned (den E x) + w2Z o).
  { rewrite den_sv_alu. cbn [den alu64 alu]. rewrite bv_add_unsigned, wbv_unsigned. apply bv_wrap_small. rewrite bv_modulus_64. lia. }
  rewrite DXO in BXO.
  apply bv_eq. cbn [den alu64 alu] in LK |- *.
  apply (f_equal bv_unsigned) in LK.
  assert (X0 : forall y : bv 64, bv_unsigned (y + wbv wzero)%bv = bv_unsigned y).
  { intros y. rewrite bv_add_unsigned, wbv_unsigned, wzero_ok, Z.add_0_r. apply bv_wrap_small. apply bv_unsigned_in_range. }
  rewrite X0, bv_add_unsigned, bv_shiftr_unsigned, shamt6_bv, SH3', X0, wbv_unsigned in LK.
  rewrite !bv_add_unsigned, !bv_shiftr_unsigned, !shamt6_bv, SH3, !wbv_unsigned.
  change (to_Z (shamt6 (wlit 3%uint63))) with 3. change (to_Z 3%uint63) with 3 in *.
  rewrite wzero_ok, Z.add_0_r. rewrite (bv_wrap_small 64 (bv_unsigned (ev E sh))) by apply bv_unsigned_in_range.
  rewrite LK, DXO.
  assert (DS : bv_unsigned (ev E k + wbv o + den E x)%bv = bv_unsigned (ev E k) + (bv_unsigned (den E x) + w2Z o)).
  { rewrite !bv_add_unsigned, wbv_unsigned. unfold bv_wrap. rewrite bv_modulus_64.
    rewrite Z.add_mod_idemp_l by lia. rewrite Z.mod_small by lia. lia. }
  rewrite DS. rewrite !Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
  assert (DIV : (bv_unsigned (ev E k) + (bv_unsigned (den E x) + w2Z o)) / 8 = bv_unsigned (ev E k) / 8 + (bv_unsigned (den E x) + w2Z o) / 8).
  { rewrite (Z.div_mod (bv_unsigned (ev E k)) 8) at 1 by lia. rewrite K8, Z.add_0_r.
    rewrite (Z.mul_comm 8), Z.div_add_l by lia. reflexivity. }
  rewrite DIV. unfold bv_wrap. rewrite bv_modulus_64. rewrite Z.add_mod_idemp_l by lia. f_equal. lia.
Qed.

Lemma shadow_fold_sound : forall a b r, shadow_fold fs a b = Some r -> den E r = alu64 ALU_ADD (den E a) (den E b).
Proof.
  intros a b r H. unfold shadow_fold in H.
  destruct a as [| |op x y| | | | | | | |]; try discriminate H. destruct op; try discriminate H.
  destruct x as [|k o|op1 x1 x2| | | | | | | |]; try discriminate H.
  2: {
       destruct op1; try discriminate H. destruct x1 as [|k o| | | | | | | | |]; try discriminate H.
       destruct y as [c| | | | | | | | | |]; try discriminate H. destruct b as [s| | | | | | | | | |]; try discriminate H.
       match type of H with (if ?cnd then _ else _) = _ => destruct cnd eqn:C; [|discriminate H] end.
       destruct (find_link fs k s) as [sh|] eqn:FL; [|discriminate H]. injection H as <-.
       exact (shadow_fold_x1_sound k o x2 c s sh C FL). }
  destruct y as [c| | | | | | | | | |]; try discriminate H.
  destruct b as [s| | | | | | | | | |]; try discriminate H.
  destruct (PrimInt63.eqb (shamt6 c) 3%uint63 && PrimInt63.leb 3%uint63 (find_align fs k) && nowrap_kb fs k o) eqn:C; [|discriminate H].
  destruct (find_link fs k s) as [sh|] eqn:FL; [|discriminate H]. injection H as <-.
  apply andb_prop in C as [C NW]. apply andb_prop in C as [SH3 AL].
  destruct (find_link_holds fs k s sh Hfs FL) as (c' & SH3' & LK).
  destruct (nowrap_kb_sound k o NW) as [RNG DK].
  pose proof (find_align_sound k) as ALG. apply Uint63.leb_spec in AL. change (to_Z 3%uint63) with 3 in AL.
  assert (K8 : bv_unsigned (ev E k) mod 8 = 0).
  { pose proof (int_range (find_align fs k)) as RA.
    destruct (Z_lt_ge_dec (to_Z (find_align fs k)) 64) as [LT|GE].
    - change 8 with (2 ^ 3). apply (align_weaken _ 3 (to_Z (find_align fs k))); [lia| exact ALG].
    -
      pose proof (bv_unsigned_in_range 64 (ev E k)) as R. rewrite bv_modulus_64 in R.
      assert (P : two64 <= 2 ^ to_Z (find_align fs k)) by (rewrite two64_eq; apply Z.pow_le_mono_r; lia).
      rewrite Z.mod_small in ALG by lia. rewrite ALG. reflexivity. }
  apply Uint63.eqb_correct in SH3. apply Uint63.eqb_correct in SH3'.
  pose proof (bv_unsigned_in_range 64 (ev E k)) as RK. rewrite bv_modulus_64 in RK.
  pose proof two64_eq as T64.

  apply bv_eq. cbn [den alu64 alu] in LK |- *.
  apply (f_equal bv_unsigned) in LK.
  assert (X0 : forall x : bv 64, bv_unsigned (x + wbv wzero)%bv = bv_unsigned x).
  { intros x. rewrite bv_add_unsigned, wbv_unsigned, wzero_ok, Z.add_0_r. apply bv_wrap_small. apply bv_unsigned_in_range. }
  rewrite X0, bv_add_unsigned, bv_shiftr_unsigned, shamt6_bv, SH3', X0, wbv_unsigned in LK.
  rewrite !bv_add_unsigned, bv_shiftr_unsigned, shamt6_bv, SH3, !wbv_unsigned.
  unfold wsra. rewrite wsra_k_ok by (change (to_Z (shamt6 (wlit 3%uint63))) with 3; lia).
  change (to_Z (shamt6 (wlit 3%uint63))) with 3.
  change (den E (VP k o)) with (bv_add (ev E k) (wbv o)) in DK. rewrite DK. change (to_Z 3%uint63) with 3 in *.
  rewrite !Z.shiftr_div_pow2 in * by lia. change (2 ^ 3) with 8 in *.
  rewrite LK. unfold bv_wrap. rewrite bv_modulus_64.
  assert (DIV : (bv_unsigned (ev E k) + w2Zs o) / 8 = bv_unsigned (ev E k) / 8 + w2Zs o / 8).
  { rewrite (Z.div_mod (bv_unsigned (ev E k)) 8) at 1 by lia. rewrite K8, Z.add_0_r.
    rewrite (Z.mul_comm 8), Z.div_add_l by lia. reflexivity. }
  rewrite DIV. rewrite Z.add_mod_idemp_l, Z.add_mod_idemp_r by lia.
  f_equal. lia.
Qed.

Lemma and_base_fold_sound : forall a b r, and_base_fold fs a b = Some r -> den E r = alu64 ALU_AND (den E a) (den E b).
Proof.
  intros a b r H. unfold and_base_fold in H.
  destruct a as [| |op p x| | | | | | | |]; try discriminate H. destruct op; try discriminate H.
  destruct p as [|k o| | | | | | | | |]; try discriminate H. destruct b as [mask| | | | | | | | | |]; try discriminate H.
  destruct (low_mask_k mask) as [m|] eqn:LM; [|discriminate H].
  destruct (negb (PrimInt63.eqb k 0%uint63) && PrimInt63.leb m (find_align fs k) && asan_on fs) eqn:C; [|discriminate H]. injection H as <-.
  apply andb_prop in C as [C _]. apply andb_prop in C as [_ AL]. apply Uint63.leb_spec in AL.
  destruct (low_mask_k_sound mask m LM) as (M1 & MK).
  pose proof (find_align_sound k) as ALG.
  assert (KM : bv_unsigned (ev E k) mod 2 ^ to_Z m = 0).
  { pose proof (int_range (find_align fs k)) as RA.
    destruct (Z_lt_ge_dec (to_Z (find_align fs k)) 64) as [LT|GE].
    - apply (align_weaken _ (to_Z m) (to_Z (find_align fs k))); [lia| exact ALG].
    - pose proof (bv_unsigned_in_range 64 (ev E k)) as R. rewrite bv_modulus_64 in R.
      assert (P : two64 <= 2 ^ to_Z (find_align fs k)) by (rewrite two64_eq; apply Z.pow_le_mono_r; lia).
      rewrite Z.mod_small in ALG by lia. rewrite ALG. apply Z.mod_0_l. apply Z.pow_nonzero; lia. }
  rewrite !den_sv_alu. cbn [den alu64 alu]. apply bv_eq.
  rewrite !bv_and_unsigned, !bv_add_unsigned, !wbv_unsigned, MK.
  replace (2 ^ to_Z m - 1) with (Z.ones (to_Z m)) by (rewrite Z.ones_equiv; lia).
  rewrite !Z.land_ones by lia. unfold bv_wrap. rewrite bv_modulus_64.
  assert (D64 : two64 = 2 ^ to_Z m * 2 ^ (64 - to_Z m)) by (rewrite two64_eq, <- Z.pow_add_r by lia; f_equal; lia).
  assert (PM : 0 < 2 ^ to_Z m) by (apply Z.pow_pos_nonneg; lia).
  assert (PR : 0 < 2 ^ (64 - to_Z m)) by (apply Z.pow_pos_nonneg; lia).
  assert (MM : forall z, (z mod two64) mod 2 ^ to_Z m = z mod 2 ^ to_Z m).
  { intros z. rewrite D64. rewrite Z.rem_mul_r by lia. rewrite (Z.mul_comm (2 ^ to_Z m)). rewrite Z.mod_add by lia. apply Z.mod_mod. lia. }
  rewrite !MM.
  rewrite <- (Z.add_mod_idemp_l ((bv_unsigned (ev E k) + w2Z o) mod two64)) by lia. rewrite MM.
  rewrite Z.add_mod_idemp_l by lia.
  rewrite <- Z.add_assoc. rewrite <- (Z.add_mod_idemp_l (bv_unsigned (ev E k))) by lia. rewrite KM, Z.add_0_l. f_equal. lia.
Qed.

Lemma sv_al_sound : forall v m, sv_al fs v m = true -> to_Z m <= 62 -> bv_unsigned (den E v) mod 2 ^ (to_Z m) = 0.
Proof.
  intros v m. pose proof (int_range m) as RM.
  induction v as [x|k o|op a IHa b IHb| | | | | | | |]; intros H Hm;
    try (apply aligned_sound; [exact H| exact Hm]).
  destruct op; try (apply aligned_sound; [exact H| exact Hm]).
  -   cbn [sv_al] in H. apply andb_prop in H as [Ha Hb].
    cbn [den alu64 alu]. rewrite bv_add_unsigned. unfold bv_wrap. rewrite bv_modulus_64, mod64_mod by lia.
    rewrite Zplus_mod, (IHa Ha Hm), (IHb Hb Hm). reflexivity.
  -   cbn [sv_al] in H. apply andb_prop in H as [Ha Hb].
    cbn [den alu64 alu]. rewrite bv_sub_unsigned. unfold bv_wrap. rewrite bv_modulus_64, mod64_mod by lia.
    rewrite Zminus_mod, (IHa Ha Hm), (IHb Hb Hm). reflexivity.
Qed.

Lemma sllsr_fold_f_sound : forall a b r, sllsr_fold_f fs a b = Some r -> den E r = alu64 ALU_SLL (den E a) (den E b).
Proof.
  intros a b r H. unfold sllsr_fold_f in H.
  destruct a as [| |op t kk| | | | | | | |]; try discriminate H.
  destruct kk as [k| | | | | | | | | |]; try discriminate H. destruct b as [k'| | | | | | | | | |]; try discriminate H.
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:C; [|discriminate H] end. injection H as <-.
  apply andb_prop in C as [C AL]. apply andb_prop in C as [C _]. apply andb_prop in C as [C S62]. apply andb_prop in C as [SHR SK].
  apply Uint63.eqb_correct in SK. rewrite leb_spec in S62. change (to_Z 62%uint63) with 62 in S62.
  pose proof (shamt6_range k) as SR. set (s := to_Z (shamt6 k)) in *.
  pose proof (sv_al_sound t (shamt6 k) AL S62) as TM. fold s in TM.
  pose proof (bv_unsigned_in_range _ (den E t)) as TR. rewrite bv_modulus_64, two64_eq in TR.
  set (T := bv_unsigned (den E t)) in *.
  assert (PS : 0 < 2 ^ s) by (apply Z.pow_pos_nonneg; lia).
  assert (TD : T = T / 2 ^ s * 2 ^ s).
  { pose proof (Z.div_mod T (2 ^ s) ltac:(lia)) as DM. rewrite TM in DM. lia. }
  apply bv_eq. symmetry.
  destruct op; try discriminate SHR.
  -
    cbn [den alu64 alu]. rewrite bv_shiftl_unsigned, bv_shiftr_unsigned, !shamt6_bv, <- SK. fold s. fold T.
    rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia. unfold bv_wrap. rewrite bv_modulus_64, two64_eq.
    rewrite <- TD. apply Z.mod_small. lia.
  -
    cbn [den alu64 alu]. rewrite bv_shiftl_unsigned, bv_ashiftr_unsigned, !shamt6_bv, <- SK. fold s.
    rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia. unfold bv_wrap. rewrite bv_modulus_64, two64_eq.
    rewrite Z.mul_mod_idemp_l by lia.
    set (S := bv_signed (den E t)).
    assert (SV : S = T \/ S = T + (-1) * 2 ^ 64).
    { unfold S, bv_signed, bv_swrap, bv_wrap. fold T. change (bv_half_modulus 64) with (2 ^ 63). change (bv_modulus 64) with (2 ^ 64).
      destruct (Z_lt_ge_dec T (2 ^ 63)) as [Lt|Ge].
      - left. rewrite Z.mod_small by lia. lia.
      - right. replace (T + 2 ^ 63) with ((T - 2 ^ 63) + 1 * 2 ^ 64) by lia. rewrite Z_mod_plus_full, Z.mod_small by lia. lia. }
    assert (P64 : 2 ^ 64 = 2 ^ (64 - s) * 2 ^ s) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
    assert (SM : S mod 2 ^ s = 0).
    { destruct SV as [-> | ->]; [exact TM|]. rewrite P64, Z.mul_assoc, Z.mod_add by lia. exact TM. }
    assert (SD : S = S / 2 ^ s * 2 ^ s).
    { pose proof (Z.div_mod S (2 ^ s) ltac:(lia)) as DM. rewrite SM in DM. lia. }
    rewrite <- SD. destruct SV as [-> | ->]; [apply Z.mod_small; lia|]. rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.

Lemma den_sv_alu_f : forall op a b, den E (sv_alu_f fs op a b) = alu64 op (den E a) (den E b).
Proof.
  intros op a b. unfold sv_alu_f. destruct op; try apply den_sv_alu.
  -
    destruct (shadow_fold fs a b) as [r|] eqn:SF; [exact (shadow_fold_sound a b r SF)|].
    destruct (shadow_fold fs b a) as [r|] eqn:SF2; [|apply den_sv_alu].
    rewrite (shadow_fold_sound b a r SF2). cbn [alu64 alu]. apply bv_eq. rewrite !bv_add_unsigned. f_equal. lia.
  - destruct (sub_fold a b) as [r|] eqn:SF; [exact (sub_fold_sound a b r SF) | apply den_sv_alu].
  -   destruct (sllsr_fold_f fs a b) as [r|] eqn:SF; [exact (sllsr_fold_f_sound a b r SF) | apply den_sv_alu].
  - destruct (decide_lts fs a b) as [r|] eqn:D; [|apply den_sv_alu].
    apply decide_lts_sound in D. cbn [den alu64 alu]. rewrite D. destruct r; reflexivity.
  - destruct (decide_ltu fs a b) as [r|] eqn:D; [|apply den_sv_alu].
    apply decide_ltu_sound in D. cbn [den alu64 alu]. rewrite D. destruct r; reflexivity.
  - destruct (srlsll_fold_f fs a b) as [r|] eqn:SF; [exact (srlsll_fold_f_sound a b r SF) | apply den_sv_alu].
  - rewrite den_refold_f. destruct (or_ins_fold fs a b) as [r|] eqn:OIF; [exact (or_ins_fold_sound a b r OIF) | apply den_sv_alu].
  -
    pose proof (den_sv_and_f a b) as DA.
    destruct (sv_and_f fs a b) eqn:SA; try exact DA;
      (destruct (and_base_fold fs a b) as [r'|] eqn:BF; [exact (and_base_fold_sound a b r' BF)| exact DA]).
Qed.

Lemma den_narrow_f_lo0 : forall sx lo n a,
  PrimInt63.eqb lo 0%uint63 && PrimInt63.ltb 0%uint63 n && PrimInt63.ltb n 8%uint63 && wltu (snd (sv_bounds fs a)) (ext_lim sx n) = true ->
  den E a = den E (VExt sx lo n a).
Proof.
  intros sx lo n a C.
  apply andb_prop in C as [C HB0]. apply andb_prop in C as [C Hn8]. apply andb_prop in C as [Hlo Hn0].
  rewrite wltu_w2Z in HB0. apply Z.ltb_lt in HB0. rename HB0 into HB.
  apply int_eqb_eq in Hlo. subst lo.
  apply Uint63.ltb_spec in Hn0. apply Uint63.ltb_spec in Hn8.
  change (to_Z 0%uint63) with 0 in Hn0. change (to_Z 8%uint63) with 8 in Hn8.
  rewrite ext_lim_val in HB by lia. pose proof (sv_bounds_hi a) as BA. pose proof (U_range a) as RA.
  cbn [den]. unfold ext_word. change (to_Z 0%uint63) with 0.
  assert (P : 2 ^ (8 * to_Z n - (if sx then 1 else 0)) <= 2 ^ 56) by (apply Z.pow_le_mono_r; destruct sx; lia).
  rewrite ext_Z_small_id by (unfold two64 in *; lia).
  apply bv_eq. rewrite Z_to_bv64_small by lia. reflexivity.
Qed.

Lemma zext0_bounds_eq : forall n x, PrimInt63.ltb 0%uint63 n = true -> PrimInt63.ltb n 8%uint63 = true ->
  sv_bounds fs (VExt false 0%uint63 n x) = zext0_bounds fs n x (sv_bounds fs x).
Proof.
  intros n x N0 N8. unfold zext0_bounds. cbn [sv_bounds bnd_struct].
  assert (NE : PrimInt63.eqb n 8%uint63 = false).
  { apply Uint63.ltb_spec in N8. destruct (PrimInt63.eqb n 8%uint63) eqn:EQ; [|reflexivity].
    apply int_eqb_eq in EQ. subst n. change (to_Z 8%uint63) with 8 in N8. lia. }
  change (PrimInt63.eqb 0%uint63 0%uint63) with true. rewrite NE, N0, N8. cbn [andb]. reflexivity.
Qed.
Lemma narrow_f0_eq : forall v, narrow_f0 fs v = narrow_f0_ref fs v.
Proof.
  intros v. unfold narrow_f0, narrow_f0_ref. destruct v as [| | | | | |sx lo n a| | | |]; try reflexivity.
  destruct (PrimInt63.eqb lo 0%uint63) eqn:LO.
  - assert (L0 : PrimInt63.ltb 0%uint63 lo = false) by (apply int_eqb_eq in LO; subst lo; reflexivity).
    rewrite L0. cbn [andb].
    destruct (PrimInt63.ltb 0%uint63 n) eqn:N0; destruct (PrimInt63.ltb n 8%uint63) eqn:N8; cbn [andb]; cbv zeta;
      try (rewrite ?andb_false_r; cbn [andb]; reflexivity).
    rewrite (zext0_bounds_eq n a N0 N8). rewrite !andb_true_r.
    destruct (wltu (snd (sv_bounds fs a)) (ext_lim sx n)); [reflexivity|]. destruct sx; reflexivity.
  - cbn [andb]. rewrite !andb_false_r. cbn [andb].
    destruct (PrimInt63.ltb 0%uint63 lo && PrimInt63.ltb lo 8%uint63 && PrimInt63.ltb 0%uint63 n && PrimInt63.ltb n 8%uint63
              && PrimInt63.leb (PrimInt63.add lo n) 8%uint63) eqn:G2; cbn [andb]; reflexivity.
Qed.

Lemma den_narrow_f0 : forall v, den E (narrow_f0 fs v) = den E v.
Proof.
  intros v. rewrite narrow_f0_eq. unfold narrow_f0_ref.
  destruct v as [| | | | | |sx lo n a| | | |]; try reflexivity.
  match goal with |- den E (if ?c then _ else _) = _ => destruct c eqn:C1 end.
  { exact (den_narrow_f_lo0 sx lo n a C1). }
  match goal with |- den E (if ?c then _ else _) = _ => destruct c eqn:C2 end.
  2: {
       match goal with |- den E (if ?c then _ else _) = _ => destruct c eqn:C3; [|reflexivity] end.
       apply andb_prop in C3 as [C3 HB]. apply andb_prop in C3 as [C3 N8]. apply andb_prop in C3 as [C3 N0]. apply andb_prop in C3 as [SX LO].
       subst sx. apply int_eqb_eq in LO. subst lo.
       apply Uint63.ltb_spec in N0. apply Uint63.ltb_spec in N8. change (to_Z 0%uint63) with 0 in N0. change (to_Z 8%uint63) with 8 in N8.
       rewrite wltu_w2Z in HB. apply Z.ltb_lt in HB. rewrite ext_lim_val in HB by lia.
       pose proof (sv_bounds_hi (VExt false 0%uint63 n a)) as BA. cbn [den] in BA |- *. unfold ext_word, ext_Z in *.
       change (to_Z 0%uint63) with 0 in *. change (8 * 0) with 0 in *. rewrite Z.pow_0_r, Z.div_1_r in *.
       pose proof (bv_unsigned_in_range _ (den E a)) as RA. rewrite bv_modulus_64 in RA.
       assert (PN : 0 < 2 ^ (8 * to_Z n)) by (apply Z.pow_pos_nonneg; lia).
       pose proof (Z.mod_pos_bound (bv_unsigned (den E a)) (2 ^ (8 * to_Z n)) PN) as MB.
       assert (P56 : 2 ^ (8 * to_Z n) <= 2 ^ 56) by (apply Z.pow_le_mono_r; lia).
       rewrite Z_to_bv64_small in BA by (unfold two64; lia).
       cbn [negb] in *.
       destruct (Z.leb_spec (2 ^ (8 * to_Z n - 1)) (bv_unsigned (den E a) mod 2 ^ (8 * to_Z n))) as [G|L]; [cbn [Z.b2z] in *; lia|].
       rewrite (Z.mod_small (bv_unsigned (den E a) mod 2 ^ (8 * to_Z n)) two64) by (unfold two64; lia). reflexivity. }
  apply andb_prop in C2 as [C2 LE]. apply andb_prop in C2 as [C2 N8]. apply andb_prop in C2 as [C2 N7]. apply andb_prop in C2 as [C2 N0].
  apply andb_prop in C2 as [LO L7].
  apply Uint63.ltb_spec in LO. apply Uint63.ltb_spec in N0. apply Uint63.leb_spec in N8. apply Uint63.ltb_spec in L7. apply Uint63.ltb_spec in N7.
  change (to_Z 0%uint63) with 0 in LO, N0. change (to_Z 8%uint63) with 8 in N8, L7, N7.
  rewrite Uint63.add_spec, Z.mod_small in N8 by (rewrite wB_two63; unfold two63; lia).
  rewrite wleu_w2Z in LE. apply Z.leb_le in LE. rewrite low_lim_val in LE by lia.
  pose proof (sv_bounds_hi a) as BA. pose proof (bv_unsigned_in_range _ (den E a)) as RA.
  cbn [den]. unfold ext_word, ext_Z.
  assert (DZ : bv_unsigned (den E a) / 2 ^ (8 * to_Z lo) = 0) by (apply Z.div_small; lia).
  rewrite DZ, Z.mod_0_l by (apply Z.pow_nonzero; lia).
  apply bv_eq. rewrite Z_to_bv_unsigned.
  replace (if sx then (if 2 ^ (8 * to_Z n - 1) <=? 0 then 0 - 2 ^ (8 * to_Z n) else 0) mod two64 else 0) with 0.
  - rewrite ?Z_to_bv_unsigned, ?wbv_unsigned, ?wzero_ok. reflexivity.
  - destruct sx; [|reflexivity]. assert (0 < 2 ^ (8 * to_Z n - 1)) by (apply Z.pow_pos_nonneg; lia).
    destruct (Z.leb_spec (2 ^ (8 * to_Z n - 1)) 0); [lia|]. reflexivity.
Qed.

Lemma or_silent_bits lo n o : 0 <= to_Z lo -> 0 < to_Z n -> to_Z lo + to_Z n <= 8 ->
  or_silent fs lo n o = true -> forall m, 8 * to_Z lo <= m < 8 * to_Z lo + 8 * to_Z n -> Z.testbit (bv_unsigned (den E o)) m = false.
Proof.
  intros Hlo Hn Hle H m Hm.
  assert (BND : forall o', PrimInt63.ltb 0%uint63 lo && wleu (snd (sv_bounds fs o')) (low_lim lo) = true ->
                          Z.testbit (bv_unsigned (den E o')) m = false).
  { intros o' H'. apply andb_prop in H' as [L0 LE]. apply Uint63.ltb_spec in L0. change (to_Z 0%uint63) with 0 in L0.
    rewrite wleu_w2Z in LE. apply Z.leb_le in LE. rewrite low_lim_val in LE by lia.
    pose proof (sv_bounds_hi o') as BH. pose proof (bv_unsigned_in_range _ (den E o')) as R'.
    apply (testbit_high _ (8 * to_Z lo)); lia. }
  unfold or_silent in H. destruct o as [c| | | | | | | | | |]; try (apply BND; exact H).
  apply (proj1 (weqb_w2Z _ _)) in H. rewrite wext_ok in H by lia. rewrite wzero_ok in H. rewrite den_VL.
  unfold ext_Z in H.
  pose proof (w2Z_range c) as Rc.
  replace m with ((m - 8 * to_Z lo) + 8 * to_Z lo) by lia.
  rewrite <- Z.div_pow2_bits by lia.
  rewrite <- (Z.mod_pow2_bits_low _ (8 * to_Z n)) by lia. rewrite H. apply Z.bits_0.
Qed.
Lemma den_narrow_or : forall v, den E (narrow_or fs v) = den E v.
Proof.
  intros v. unfold narrow_or. destruct v as [| | | | | |sx lo n x| | | |]; try reflexivity.
  destruct x as [| | op a b| | | | | | | |]; try reflexivity. destruct op; try reflexivity.
  match goal with |- den E (if ?c then _ else _) = _ => destruct c eqn:G; [|reflexivity] end.
  apply andb_prop in G as [G LE]. apply andb_prop in G as [G N8]. apply andb_prop in G as [L8 N0].
  apply Uint63.ltb_spec in L8. apply Uint63.ltb_spec in N0. apply Uint63.ltb_spec in N8. apply Uint63.leb_spec in LE.
  change (to_Z 8%uint63) with 8 in L8, N8, LE. change (to_Z 0%uint63) with 0 in N0.
  pose proof (to_Z_bounded lo) as Blo.
  rewrite Uint63.add_spec, Z.mod_small in LE by (rewrite wB_two63; unfold two63; lia).
  assert (W : width_ok (to_Z lo) (to_Z n)) by (unfold width_ok; lia).
  assert (KEY : forall p q, or_silent fs lo n q = true ->
            den E (sv_ext sx lo n p) = den E (VExt sx lo n (VAlu ALU_OR p q))
            /\ den E (sv_ext sx lo n p) = den E (VExt sx lo n (VAlu ALU_OR q p))).
  { intros p q Hq. rewrite den_sv_ext by exact W.
    pose proof (or_silent_bits lo n q ltac:(lia) ltac:(lia) ltac:(lia) Hq) as QB.
    pose proof (bv_unsigned_in_range _ (den E p)) as Rp. rewrite bv_modulus_64 in Rp.
    pose proof (bv_unsigned_in_range _ (den E q)) as Rq. rewrite bv_modulus_64 in Rq.
    cbn [den alu64 alu]. unfold ext_word. split; f_equal; rewrite bv_or_unsigned; apply ext_Z_bits_shift; try lia;
      try (apply Z.lor_nonneg; lia);
      intros m Hm; rewrite Z.lor_spec, (QB (m + 8 * to_Z lo)) by lia; [rewrite Bool.orb_false_r| rewrite Bool.orb_false_l]; reflexivity. }
  destruct (or_silent fs lo n b) eqn:SB; [exact (proj1 (KEY a b SB))|].
  destruct (or_silent fs lo n a) eqn:SA; [exact (proj2 (KEY b a SA))| reflexivity].
Qed.

Lemma den_sextw_f : forall v, den E (sextw_f fs v) = den E v.
Proof.
  intros v. unfold sextw_f.
  assert (K : forall x z, weqb z wzero && wltu (snd (sv_bounds fs x)) bit31w = true ->
             den E x = den E (VAluw ALU_ADD x (VL z)) /\ den E x = den E (VAluw ALU_ADD (VL z) x)).
  { intros x z H. apply andb_prop in H as [Hz0 Hb]. apply weqb_wzero_unsigned in Hz0.
    rewrite wltu_w2Z, bit31w_val in Hb. apply Z.ltb_lt in Hb. pose proof (sv_bounds_hi x) as BX.
    pose proof (bv_unsigned_in_range _ (den E x)) as R. rewrite bv_modulus_64 in R.
    assert (Z0 : bv_unsigned (low32 (den E (VL z))) = 0) by (rewrite low32_ext; cbn [den]; rewrite Hz0; reflexivity).
    assert (LW : bv_unsigned (low32 (den E x)) = bv_unsigned (den E x)) by (rewrite low32_ext; apply Z.mod_small; lia).
    assert (G : forall s : bv 32, bv_unsigned s = bv_unsigned (den E x) -> den E x = sext 64 s).
    { intros s Hs. apply bv_eq. rewrite sext32_unsigned, Hs. unfold sx32Z.
      destruct (Z.leb_spec (2 ^ 31) (bv_unsigned (den E x))); [lia|reflexivity]. }
    cbn [den alu32 alu]. cbn [den] in Z0. split; apply G; rewrite bv_add_unsigned, ?Z0, LW, ?Z.add_0_r, ?Z.add_0_l;
      unfold bv_wrap; apply Z.mod_small; change (bv_modulus 32) with (2^32); lia. }
  destruct v as [| | |op a b| | | | | | |]; try reflexivity. destruct op; try reflexivity.
  destruct a as [za| | | | | | | | | |]; destruct b as [zb| | | | | | | | | |]; try reflexivity.
  all: try match goal with
       | |- den E (if ?cnd then _ else _) = _ => destruct cnd eqn:W; [|reflexivity]
       end.
  all: try first [apply (proj1 (K _ _ W)) | apply (proj2 (K _ _ W))].
Qed.
Lemma den_narrow_f : forall v, den E (narrow_f fs v) = den E v.
Proof. intros v. unfold narrow_f. rewrite den_sextw_f, den_narrow_f0. apply den_narrow_or. Qed.

Lemma sextw_small : forall (w : word), bv_unsigned w < 2 ^ 31 ->
  sext 64 (alu32 ALU_ADD (low32 w) (low32 (den E (VL wzero)))) = w
  /\ sext 64 (alu32 ALU_ADD (low32 (den E (VL wzero))) (low32 w)) = w.
Proof.
  intros w Hw. pose proof (bv_unsigned_in_range _ w) as R.
  assert (Z0 : bv_unsigned (low32 (den E (VL wzero))) = 0) by (rewrite low32_ext, den_VL; reflexivity).
  assert (LW : bv_unsigned (low32 w) = bv_unsigned w) by (rewrite low32_ext; apply Z.mod_small; lia).
  assert (G : forall s : bv 32, bv_unsigned s = bv_unsigned w -> sext 64 s = w).
  { intros s Hs. apply bv_eq. rewrite sext32_unsigned, Hs. unfold sx32Z.
    destruct (Z.leb_spec (2 ^ 31) (bv_unsigned w)); [lia|reflexivity]. }
  split; apply G; cbn [alu32 alu]; rewrite bv_add_unsigned, ?Z0, LW, ?Z.add_0_r, ?Z.add_0_l;
    unfold bv_wrap; apply Z.mod_small; change (bv_modulus 32) with (2^32); lia.
Qed.

Lemma den_sv_aluw_f : forall op a b, den E (sv_aluw_f fs op a b) = sext 64 (alu32 op (low32 (den E a)) (low32 (den E b))).
Proof.
  intros op a b. unfold sv_aluw_f.
  assert (SX : forall z, 0 <= z < 2 ^ 31 -> sx32Z z = z).
  { intros z Hz0. unfold sx32Z. destruct (Z.leb_spec (2 ^ 31) z); [lia|reflexivity]. }
  pose proof (U_range a) as RA. pose proof (U_range b) as RB.
  destruct op; try apply den_sv_aluw; cbv zeta; rewrite wltu_w2Z, bit31w_val.
  - destruct (Z.ltb_spec (w2Z (snd (sv_bounds fs (sv_alu_f fs ALU_ADD a b)))) (2 ^ 31)) as [C|C]; [|apply den_sv_aluw].
    pose proof (sv_bounds_hi (sv_alu_f fs ALU_ADD a b)) as B. rewrite den_sv_alu_f in B |- *.
    apply bv_eq. cbn [alu64 alu32 alu] in B |- *. rewrite sext32_unsigned.
    rewrite !bv_add_unsigned, !low32_ext in *. unfold bv_wrap in *. rewrite bv_modulus_64 in *.
    change (bv_modulus 32) with (2^32). rewrite <- Z.add_mod by lia.
    rewrite <- (mod64_mod (bv_unsigned (den E a) + bv_unsigned (den E b)) 32) by lia.
    pose proof (Z.mod_pos_bound (bv_unsigned (den E a) + bv_unsigned (den E b)) two64 ltac:(unfold two64; lia)).
    rewrite (Z.mod_small _ (2^32)) by lia. rewrite SX by lia. reflexivity.
  - destruct (Z.ltb_spec (w2Z (snd (sv_bounds fs (sv_alu_f fs ALU_SUB a b)))) (2 ^ 31)) as [C|C]; [|apply den_sv_aluw].
    pose proof (sv_bounds_hi (sv_alu_f fs ALU_SUB a b)) as B. rewrite den_sv_alu_f in B |- *.
    apply bv_eq. cbn [alu64 alu32 alu] in B |- *. rewrite sext32_unsigned.
    rewrite !bv_sub_unsigned, !low32_ext in *. unfold bv_wrap in *. rewrite bv_modulus_64 in *.
    change (bv_modulus 32) with (2^32). rewrite <- Zminus_mod by lia.
    rewrite <- (mod64_mod (bv_unsigned (den E a) - bv_unsigned (den E b)) 32) by lia.
    pose proof (Z.mod_pos_bound (bv_unsigned (den E a) - bv_unsigned (den E b)) two64 ltac:(unfold two64; lia)).
    rewrite (Z.mod_small _ (2^32)) by lia. rewrite SX by lia. reflexivity.
Qed.

End Deciders.

Lemma decide_branch_t_sound : forall E fs, facts_hold E fs -> forall c a b r, decide_branch_t fs c a b = Some r ->
  branch_taken c (den E a) (den E b) = r.
Proof.
  intros E fs Hfs c a b r H. unfold decide_branch_t in H. cbv zeta in H.
  destruct (decide_branch (rel_facts (sv_vs a (sv_vs b [])) fs) c a b) as [r1|] eqn:D1.
  { injection H as <-. exact (decide_branch_sound E _ (rel_facts_hold E _ fs Hfs) c a b r1 D1). }
  destruct (decide_branch (rel_facts (close_vs fs (sv_vs a (sv_vs b [])) (sv_vs a (sv_vs b []))) fs) c a b) as [r2|] eqn:D2.
  { injection H as <-. exact (decide_branch_sound E _ (rel_facts_hold E _ fs Hfs) c a b r2 D2). }
  exact (decide_branch_sound E fs Hfs c a b r H).
Qed.

Lemma fact_eqb_eq : forall f g, fact_eqb f g = true -> f = g.
Proof.
  intros f g H. destruct f, g; cbn [fact_eqb] in H; try discriminate H; vp_bsplit;
  repeat match goal with G : weqb _ _ = true |- _ => apply weqb_eq in G; subst end; reflexivity.
Qed.

Lemma implied_sound : forall E fs f, facts_hold E fs -> ev E 0%uint63 = Z_to_bv 64 0 ->
  Plan.implied fs f = true -> fact_holds E f.
Proof.
  intros E fs f Hfs Hz H. unfold implied in H. apply orb_prop in H. destruct H as [H|H].
  { apply existsb_exists in H as (g & Hin & Heq). apply fact_eqb_eq in Heq. subst g.
    unfold facts_hold in Hfs. rewrite Forall_forall in Hfs. apply Hfs, Hin. }
  destruct f; cbn [fact_holds].
  - destruct (find_range fs k) as [[lo' hi']|] eqn:Hr; [|discriminate]. apply (find_range_sound E fs Hfs) in Hr.
    vp_bsplit. vp_wcmp. lia.
  - apply (find_align_le E fs Hfs). exact H.
  - destruct (decide_ltu fs a b) as [[]|] eqn:D; try discriminate. apply (decide_ltu_sound E fs Hfs), ltu_iff in D. exact D.
  - destruct (decide_ltu fs b a) as [[]|] eqn:D; try discriminate. apply (decide_ltu_sound E fs Hfs), ltu_iff in D. exact D.
  - destruct (decide_eq fs a b) as [[]|] eqn:D; try discriminate. apply (decide_eq_sound E fs Hfs), eqb_iff in D. exact D.
  - destruct (decide_eq fs a b) as [[]|] eqn:D; try discriminate. apply (decide_eq_sound E fs Hfs), eqb_iff in D. exact D.
  - destruct (decide_lts fs a b) as [[]|] eqn:D; try discriminate. apply (decide_lts_sound E fs Hfs), lts_iff in D. exact D.
  - destruct (decide_lts fs b a) as [[]|] eqn:D; try discriminate. apply (decide_lts_sound E fs Hfs), lts_iff in D. exact D.
Qed.

End ValP.
