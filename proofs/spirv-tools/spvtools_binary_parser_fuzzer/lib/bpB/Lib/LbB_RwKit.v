From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatSim SymExec3 SymExec3Sound SymRun3.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HLib HWord HUbsan.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma ext_sx4_small : forall x, 0 <= x < 2 ^ 31 -> ext_val true 0 4 (Z_to_bv 64 x) = Z_to_bv 64 x.
Proof. intros x Hx. apply ext_val_sx_id; [lia|]. rewrite u64_of_Z by lia. cbn. lia. Qed.

Lemma ext_zx_small : forall (n : nat) x, 0 <= x < 2 ^ (8 * Z.of_nat n) -> 2 ^ (8 * Z.of_nat n) <= 2 ^ 64 ->
  ext_val false 0 n (Z_to_bv 64 x) = Z_to_bv 64 x.
Proof. intros n x Hx H64. apply ext_val_zx_id. rewrite u64_of_Z by lia. lia. Qed.

Lemma s64_small : forall z, 0 <= z < 2 ^ 63 -> bv_signed (Z_to_bv 64 z) = z.
Proof.
  intros z Hz. unfold bv_signed. rewrite (SymExec3.SX2.swrap_small 64 (bv_unsigned (Z_to_bv 64 z)) (2 ^ 63) (2 ^ 64));
    [| reflexivity | reflexivity | rewrite u64_of_Z by lia; lia | lia].
  rewrite u64_of_Z by lia. destruct (Z.ltb_spec z (2 ^ 63)); lia.
Qed.
Lemma br_ltB : forall x y, 0 <= x < 2 ^ 63 -> 0 <= y < 2 ^ 63 ->
  branch_taken BC_LT (Z_to_bv 64 x) (Z_to_bv 64 y) = (x <? y).
Proof. intros x y Hx Hy. cbn [branch_taken]. unfold bv_lts. rewrite !s64_small by lia. reflexivity. Qed.
Lemma br_geB : forall x y, 0 <= x < 2 ^ 63 -> 0 <= y < 2 ^ 63 ->
  branch_taken BC_GE (Z_to_bv 64 x) (Z_to_bv 64 y) = negb (x <? y).
Proof. intros x y Hx Hy. cbn [branch_taken]. unfold bv_lts. rewrite !s64_small by lia. reflexivity. Qed.

Lemma w_sra_small : forall a k, 0 <= a < 2 ^ 63 -> 0 <= k < 64 ->
  alu64 ALU_SRA (Z_to_bv 64 a) (Z_to_bv 64 k) = Z_to_bv 64 (a / 2 ^ k).
Proof.
  intros a k Ha Hk. apply bv_eq.
  change (alu64 ALU_SRA (Z_to_bv 64 a) (Z_to_bv 64 k))
    with (bv_ashiftr (Z_to_bv 64 a) (bv_and (Z_to_bv 64 k) (Z_to_bv 64 63))).
  rewrite bv_ashiftr_unsigned, bv_and_unsigned, !Z_to_bv_unsigned, !bv_wrap64_mod.
  rewrite s64_small by lia.
  rewrite (Z.mod_small k), (Z.mod_small 63) by lia.
  replace (Z.land k 63) with k.
  2:{ change 63 with (Z.ones 6). rewrite Z.land_ones by lia. symmetry. apply Z.mod_small. lia. }
  rewrite Z.shiftr_div_pow2 by lia.
  assert (0 <= a / 2 ^ k <= a) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; try lia; nia]).
  rewrite ?bv_wrap64_mod, ?Z.mod_small by lia. reflexivity.
Qed.

Lemma w_add_u : forall a b, alu64 ALU_ADD (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a + b).
Proof.
  intros a b. apply bv_eq. cbn [alu64 alu]. rewrite bv_add_unsigned, !Z_to_bv_unsigned.
  unfold bv_wrap. rewrite <- Zplus_mod. reflexivity.
Qed.
Lemma w_sub_u : forall a b, alu64 ALU_SUB (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a - b).
Proof.
  intros a b. apply bv_eq. cbn [alu64 alu]. rewrite bv_sub_unsigned, !Z_to_bv_unsigned.
  unfold bv_wrap. rewrite <- Zminus_mod. reflexivity.
Qed.
Lemma w_mul_u : forall a b, mul_div M_MUL (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a * b).
Proof.
  intros a b. apply bv_eq. cbn [mul_div]. rewrite bv_mul_unsigned, !Z_to_bv_unsigned.
  unfold bv_wrap. rewrite <- Zmult_mod. reflexivity.
Qed.

Lemma sc_trap_psub : forall (SEGS : list Segment) M E a b c p k,
  edenot E a = Z_to_bv 64 p -> edenot E b = Z_to_bv 64 (p + k) -> edenot E c = Z_to_bv 64 (- k) ->
  0 <= p -> 0 <= k < 2 ^ 63 -> p + k < 2 ^ 64 ->
  sc_denot SEGS M E (SCBr false BC_EQ (EAlu ALU_XOR (EAlu ALU_XOR (EAlu ALU_SLTU a b) (EAlu ALU_SLT c (ELit 0))) (ELit 1)) (ELit 0)).
Proof.
  intros SEGS M E a b c p k Ha Hb Hc Hp Hk Hpk. cbn [sc_denot edenot]. rewrite Ha, Hb, Hc.
  rewrite w_sltu by lia.
  assert (HS : alu64 ALU_SLT (Z_to_bv 64 (- k)) (Z_to_bv 64 0) = Z_to_bv 64 (if 0 <? k then 1 else 0)).
  { apply bv_eq. rewrite u_slt64.
    replace (bv_signed (Z_to_bv 64 (- k))) with (- k).
    2:{ unfold bv_signed. rewrite Z_to_bv_unsigned.
        destruct (Z.eq_dec k 0) as [->|Hk0]; [reflexivity|].
        assert (HW : bv_wrap 64 (- k) = 2 ^ 64 - k).
        { unfold bv_wrap, bv_modulus. cbn [Z.of_N].
          rewrite <- (Z.mod_add (- k) 1) by lia. rewrite Z.mod_small by lia. lia. }
        rewrite HW. rewrite (SymExec3.SX2.swrap_small 64 (2 ^ 64 - k) (2 ^ 63) (2 ^ 64)) by (reflexivity || lia).
        destruct (Z.ltb_spec (2 ^ 64 - k) (2 ^ 63)); lia. }
    rewrite (s64_small 0) by lia. rewrite u64_of_Z by (destruct (0 <? k); lia).
    destruct (Z.ltb_spec 0 k); destruct (Z.ltb_spec (- k) 0); try lia; reflexivity. }
  rewrite HS.
  destruct (Z.ltb_spec p (p + k)); destruct (Z.ltb_spec 0 k); try lia; vm_compute; reflexivity.
Qed.

Lemma sc_trap_psub2 : forall (SEGS : list Segment) M E a b d p k,
  edenot E a = Z_to_bv 64 p -> edenot E b = Z_to_bv 64 (p + k) -> edenot E d = Z_to_bv 64 k ->
  0 <= p -> 0 <= k < 2 ^ 63 -> p + k < 2 ^ 64 ->
  sc_denot SEGS M E (SCBr false BC_EQ (EAlu ALU_XOR (EAlu ALU_XOR (EAlu ALU_SLTU a b) (EAlu ALU_SLT (ELit 0) d)) (ELit 1)) (ELit 0)).
Proof.
  intros SEGS M E a b d p k Ha Hb Hd Hp Hk Hpk. cbn [sc_denot edenot]. rewrite Ha, Hb, Hd.
  rewrite w_sltu by lia.
  assert (HS : alu64 ALU_SLT (Z_to_bv 64 0) (Z_to_bv 64 k) = Z_to_bv 64 (if 0 <? k then 1 else 0)).
  { apply bv_eq. rewrite u_slt64. rewrite !s64_small by lia. rewrite u64_of_Z by (destruct (0 <? k); lia).
    destruct (Z.ltb_spec 0 k); reflexivity. }
  rewrite HS.
  destruct (Z.ltb_spec p (p + k)); destruct (Z.ltb_spec 0 k); try lia; vm_compute; reflexivity.
Qed.

Lemma land_3 : forall a, Z.land a 3 = a mod 4.
Proof. intros a. change 3 with (Z.ones 2). rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma sc_chk_align4 : forall (SEGS : list Segment) M E e a, edenot E e = Z_to_bv 64 a -> 0 <= a < 2 ^ 64 -> a mod 4 = 0 ->
  sc_denot SEGS M E (SCBr false BC_NE (EAlu ALU_AND e (ELit 3)) (ELit 0)).
Proof.
  intros SEGS M E e a He Ha Hal. cbn [sc_denot]. cbn [edenot]. rewrite He.
  rewrite w_and by lia. rewrite land_3, Hal. reflexivity.
Qed.

Ltac dlia := first [ lia | Z.div_mod_to_equations; lia ].

Lemma w_div5_mul : forall K c x, (5 * K) mod 2 ^ 64 = c mod 2 ^ 64 -> x mod 4 = 0 -> (x / 4) mod 5 = 0 ->
  Z_to_bv 64 (K * (x / 2 ^ 2)) = Z_to_bv 64 (c * (x / 20)).
Proof.
  intros K c x Hc H4 H5. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn [Z.of_N].
  change (2 ^ 2) with 4.
  assert (E : x / 4 = 5 * (x / 20)).
  { replace 20 with (4 * 5) by lia. rewrite <- Z.div_div by lia. Z.div_mod_to_equations. lia. }
  rewrite E. replace (K * (5 * (x / 20))) with ((5 * K) * (x / 20)) by lia.
  rewrite Z.mul_mod by lia. rewrite Hc. rewrite <- Z.mul_mod by lia. reflexivity.
Qed.
Ltac div5B :=
  match goal with |- context [Z_to_bv 64 (?K * (?x / 2 ^ 2))] =>
    let c := eval vm_compute in ((5 * K) mod 2 ^ 64) in
    let ok := eval vm_compute in (c <? 4294967296) in
    lazymatch ok with true => rewrite (w_div5_mul K c x) by (first [ vm_compute; reflexivity | dlia ]) end
  end.

Lemma w_mulh_small : forall a b, 0 <= a < 2 ^ 63 -> 0 <= b < 2 ^ 63 -> a * b < 2 ^ 63 ->
  mul_div M_MULH (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 0.
Proof.
  intros a b Ha Hb Hab. rewrite m_mulh. unfold v_mulh.
  rewrite !s64_small by lia. rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_small by nia. reflexivity.
Qed.

Ltac wnormB :=
  repeat first [ div5B | rewrite w_mul_u | rewrite w_add_u | rewrite w_sub_u | rewrite w_and by dlia
               | rewrite w_srl by dlia | rewrite w_sra_small by dlia | rewrite w_sltu by dlia | rewrite w_xor by dlia | rewrite w_or by dlia
               | rewrite ext_sx4_small by dlia | rewrite ext_zx_small by (cbn; lia)
               | rewrite w_mulh_small by dlia
               | rewrite land_7 ].

Ltac sc_valB := evs; wnormB; first [ reflexivity | f_equal; dlia ].

Ltac sc_ubB :=
  match goal with
  | |- sc_denot _ _ _ (SCBr false BC_EQ (EAlu ALU_XOR (EAlu ALU_XOR (EAlu ALU_SLTU _ _) (EAlu ALU_SLT _ (ELit 0))) (ELit 1)) (ELit 0)) =>
      eapply sc_trap_psub; [sc_valB | sc_valB | sc_valB | dlia | dlia | dlia]
  | |- sc_denot _ _ _ (SCBr false BC_EQ (EAlu ALU_XOR (EAlu ALU_XOR (EAlu ALU_SLTU _ _) (EAlu ALU_SLT (ELit 0) _)) (ELit 1)) (ELit 0)) =>
      eapply sc_trap_psub2; [sc_valB | sc_valB | sc_valB | dlia | dlia | dlia]
  | |- sc_denot _ _ _ (SCBr false BC_EQ (EAlu ALU_XOR (EAlu ALU_SLTU (ELit 0) _) (EAlu ALU_SLTU _ (ELit 1))) (ELit 0)) =>
      eapply sc_trap_nullxor; [sc_valB | sc_valB | lia | lia | lia]
  | |- sc_denot _ _ _ (SCBr false BC_LTU (EAlu ALU_ADD (EMd M_MUL (ELit (-1)) _) (ELit (-1))) _) =>
      eapply sc_trap_notlt; [sc_valB | sc_valB | lia | lia | lia]
  | |- sc_denot _ _ _ (SCBr false BC_LTU _ _) =>
      eapply sc_trap_wrap; [sc_valB | sc_valB | lia | lia | lia]
  | |- sc_denot _ _ _ (SCBr false BC_NE (EAlu ALU_SRL _ (ELit _)) (ELit 0)) =>
      eapply sc_trap_srl; [sc_valB | lia | lia]
  | |- sc_denot _ _ _ (SCBr false BC_NE (EAlu ALU_AND _ (ELit 7)) (ELit 0)) =>
      eapply sc_trap_align; [sc_valB | lia | first [ assumption | lia | Z.div_mod_to_equations; lia ]]
  | |- sc_denot _ _ _ (SCBr false BC_NE (EAlu ALU_AND _ (ELit 3)) (ELit 0)) =>
      eapply sc_chk_align4; [sc_valB | lia | first [ assumption | lia | Z.div_mod_to_equations; lia ]]
  | |- sc_denot _ _ _ (SCBr false BC_EQ _ (ELit 0)) =>
      eapply sc_trap_null; [sc_valB | lia]
  end.

Ltac bool_dlia :=
  first [ reflexivity
        | apply Z.eqb_eq; dlia | apply Z.eqb_neq; dlia
        | apply Z.ltb_lt; dlia | apply Z.ltb_ge; dlia
        | apply (proj2 (Bool.negb_true_iff _)); bool_dlia
        | apply (proj2 (Bool.negb_false_iff _)); bool_dlia ].

Ltac sc_brB :=
  cbn [sc_denot]; evs; wnormB;
  rewrite ?br_eq, ?br_ne, ?br_ltu, ?br_geu, ?br_ltB, ?br_geB by dlia; rewrite ?Z.pow_0_r, ?Z.pow_1_r; bool_dlia.

Ltac sc_caseB :=
  cbn [sc_denot]; evs; wnormB;
  repeat match goal with |- context [?x <? ?y] => destruct (Z.ltb_spec x y) end;
  repeat match goal with |- context [?x =? ?y] => destruct (Z.eqb_spec x y) end;
  first [ exfalso; dlia
        | tryif (match goal with |- context [?v] => is_var v; lazymatch type of v with Z => idtac end end)
          then fail else (vm_compute; reflexivity)
        | rewrite ?br_eq, ?br_ne, ?br_ltu, ?br_geu, ?br_ltB, ?br_geB by dlia; bool_dlia ].

Ltac sc_adB :=
  cbn [sc_denot]; unfold flat, estart, elenZ; evs; wnormB; rewrite ?u64_of_Z by dlia; cbn [a_off a_base];
  first [ dlia | (repeat split); dlia ].

Ltac sc_closeB :=
  lazymatch goal with
  | |- sc_denot _ _ _ (SCBr _ _ _ _) => first [ sc_ubB | sc_brB | sc_caseB ]
  | |- sc_denot _ _ _ (SCDisj _ _ _ _) => sc_adB
  | |- sc_denot _ _ _ (SCFlat _ _) => sc_adB
  | |- sc_denot _ _ _ (SCInside _ _ _ _) => sc_adB
  | |- _ => idtac
  end.

Ltac scs_closeB := split_scs; sc_closeB.
