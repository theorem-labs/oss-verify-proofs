(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (12 recorded proofs replaced by written proofs (lo64_mk128', lo64_mk128, hi64_mk128 and 9 more)). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Export Walk.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Export SoftFloat.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_SFModel () := "K47Corelib4Init5Logic2eq01I47Corelib4Init9Datatypes4bool00I47Corelib7Numbers7BinNums1Z00C56Stdlib6ZArith6BinInt1Z3b2zK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z6shiftlC56Stdlib6ZArith6BinInt1Z3lorC56Stdlib6ZArith6BinInt1Z6moduloI47Corelib4Init5Logic2eq00C56Stdlib6ZArith6BinInt1Z4onesC56Stdlib6ZArith6BinInt1Z4landC56Stdlib6ZArith6BinInt1Z7testbitC47Corelib4Init9Datatypes4andbC47Corelib4Init9Datatypes3orbC56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z;lt_ge_casesC56Stdlib6ZArith6BinInt1Z2leI47Corelib4Init5Logic2or00C46Stdlib4Bool4Bool;andb_true_rK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr01K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr04C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z=testbit_neg_rC56Stdlib6ZArith6BinInt1Z=ones_spec_lowC47Corelib4Init5Logic8eq_ind_rC56Stdlib6ZArith6BinInt1Z6eq_decC47Corelib4Init5Logic3notI47Corelib4Init6Specif7sumbool00C56Stdlib6ZArith6BinInt1Z6bits_0K46Stdlib9micromega5Tauto8GFormula03C56Stdlib6ZArith6BinInt1Z4log2C56Stdlib6ZArith6BinInt1Z<log2_lt_pow2C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareK46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula07K47Corelib7Numbers7BinNums1N02K46Stdlib9micromega7EnvRing5PExpr07C56Stdlib6ZArith6BinInt1Z;lt_le_transC56Stdlib6ZArith6BinInt1Z?bits_above_log2C47Corelib4Init5Logic6eq_symC46Stdlib4Bool4Bool<andb_false_rC56Stdlib6ZArith6BinInt1Z>ones_spec_highC56Stdlib6ZArith6BinInt1Z;shiftl_specC56Stdlib6ZArith6BinInt1Z8lor_specC56Stdlib6ZArith6BinInt1Z9land_specC56Stdlib6ZArith6BinInt1Z9bits_inj'K46Stdlib9micromega6VarMap1t01C56Stdlib6ZArith6BinInt1Z9land_onesC47Corelib4Init5Logic6eq_indC59OSSVerify5KrLib6Common9SoftFloat6wrap64C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common9SoftFloat:wrap64_modC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common9SoftFloat5mk128C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common9SoftFloat4lo64C1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega5Tauto8GFormula05K47Corelib7Numbers7BinNums1Z01K46Stdlib9micromega=RingMicromega3Op205C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K47Corelib4Init9Datatypes4bool02K46Stdlib9micromega=RingMicromega3Op203K47Corelib7Numbers7BinNums8positive03K47Corelib4Init9Datatypes4bool01I46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes:comparison00K46Stdlib9micromega=RingMicromega3Op201I47Corelib4Init5Logic5False00c59OSSVerify5KrLib6Common7SFModel;lo64_mk128'C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6shiftrC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z9mod_smallC56Stdlib6ZArith6BinInt1Z7lor_0_rC56Stdlib6ZArith6BinInt1Z9div_smallC56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2C56Stdlib6ZArith6BinInt1Z:shiftl_0_rC56Stdlib6ZArith6BinInt1Z8sub_diagC56Stdlib6ZArith6BinInt1Z?shiftr_shiftl_lC56Stdlib6ZArith6BinInt1Z:shiftr_lorC59OSSVerify5KrLib6Common9SoftFloat4hi64C1?~~~~~~~~~~~~~~~I45stdpp9bitvector;definitions2bv00C45stdpp9bitvector;definitions7Z_to_bvK47Corelib4Init5Logic3and01c59OSSVerify5KrLib6Common7SFModel:hi64_mk128C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common7SFModel:lo64_mk128C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4lxorC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z@add_nocarry_lxorC56Stdlib6ZArith6BinInt1Z8lxor_lorK46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr03C56Stdlib6ZArith6BinInt1Z8land_0_rC56Stdlib6ZArith6BinInt1Z:land_assocC56Stdlib6ZArith6BinInt1Z9land_diagC56Stdlib6ZArith6BinInt1Z9land_commc59OSSVerify5KrLib6Common7SFModel@lor_disjoint_addC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z@land_lor_distr_rK47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK47Corelib4Init9Datatypes3nat02K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega7EnvRing3Pol03K46Stdlib9micromega7EnvRing3Pol02K46Stdlib9micromega:ZMicromega;ZArithProof04K47Corelib4Init9Datatypes4list02K46Stdlib9micromega7EnvRing5PExpr05C56Stdlib6ZArith6BinInt1Z3mulc59OSSVerify5KrLib6Common7SFModel6land_1C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common7SFModel8land_W64C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common7SFModel>land_even_maskC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib7ZBridge;Z_to_bv_eqmC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega=RingMicromega5Psatz05K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01C56Stdlib6ZArith6BinInt1Z3oppC45stdpp9bitvector;definitions8bv_swrapK46Stdlib9micromega7EnvRing5PExpr06C45stdpp9bitvector;definitions?bv_half_modulusC45stdpp9bitvector;definitions>bv_swrap_smallC45stdpp9bitvector;definitions9bv_signedC45stdpp9bitvector;definitions>Z_to_bv_signed".
Import ListNotations.
Open Scope bv_scope.

Lemma b2z_Zb2z : b2z = Z.b2z.
Proof.
ltac2:(KReplay.run1 (kr_t_SFModel ()) [] "h01bp;2g0000j20Tg000Jg000j]0g001H'0o"). Qed.

Ltac zb_masks_in H :=
  repeat match type of H with
  | context [Z.land ?x ?m] =>
      is_Zlit_zb m;
      let k := eval vm_compute in (Z.log2 (m + 1)) in
      let m' := eval vm_compute in (2 ^ k - 1)%Z in
      constr_eq m m';
      let p := eval vm_compute in (2 ^ k)%Z in
      replace (Z.land x m) with (x mod p)%Z in H
        by (symmetry; change m with (2^k - 1)%Z; change p with (2^k)%Z; apply zb_land_mask; lia)
  end.

(* [comment removed for export] *)
Ltac zs_wrap e ::= zs_wrap_land e.
Ltac zs_wrap_in e H ::= zs_wrap_land_in e H.
Ltac zs_idioms ::= zs_idioms_land.
Ltac zs_idioms_in H ::= zs_idioms_land_in H.

Ltac unfold_sf_in H :=
  cbv beta delta [add64 sub64 mul64 shl64 not64 ltu64 eqz64 nez64 zext32 sext32 srliw mulhu
         is_neg64 sra63 lt_s64 lo64 hi64 wrap64 b2z
         ONES64 M32 SIGN64 MASK48 MASKLO ABS_HI INF_HI QUIET_HI QNAN_HI IMPLICIT_HI] in H.
Ltac unfold_sf :=
  cbv beta delta [add64 sub64 mul64 shl64 not64 ltu64 eqz64 nez64 zext32 sext32 srliw mulhu
         is_neg64 sra63 lt_s64 lo64 hi64 wrap64 b2z
         ONES64 M32 SIGN64 MASK48 MASKLO ABS_HI INF_HI QUIET_HI QNAN_HI IMPLICIT_HI].

Ltac norm_model H := unfold_sf_in H; zb_fold_lits_in H.

Ltac get_head t := lazymatch t with ?g _ => get_head g | _ => t end.

(* [comment removed for export] *)
Tactic Notation "model_hyp" ident(HR) constr(t) :=
  assert (HR : t = t) by reflexivity;
  let h := get_head t in unfold h in HR at 2;
  norm_model HR.

(* [comment removed for export] *)
Notation W64 := 18446744073709551615%Z.

(* [comment removed for export] *)
Ltac model_eval :=
  lazy -[Z.shiftr Z.shiftl Z.land Z.lor Z.lxor Z.lnot Z.mul Z.add Z.sub Z.opp Z.modulo Z.div
         Z.ltb Z.eqb Z.leb Z.pow bv_unsigned].

(* [comment removed for export] *)
Tactic Notation "model_end" constr(X) constr(t) :=
  replace (Z_to_bv 64 X) with (Z_to_bv 64 t) by (f_equal; model_eval; reflexivity).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma lo64_mk128' : forall hi lo, (0 <= lo < 2^64)%Z -> (0 <= hi)%Z -> lo64 (mk128 hi lo) = lo.
Proof.
  intros hi lo Hlo Hhi. unfold lo64, mk128. rewrite wrap64_mod.
  rewrite <- Z.land_ones by lia. apply Z.bits_inj'. intros i Hi.
  rewrite Z.land_spec, Z.lor_spec, Z.shiftl_spec by lia.
  destruct (Z.lt_ge_cases i 64).
  - rewrite Z.ones_spec_low, (Z.testbit_neg_r _ (i - 64)) by lia. cbn. apply andb_true_r.
  - rewrite Z.ones_spec_high by lia. rewrite andb_false_r.
    symmetry. destruct (Z.eq_dec lo 0) as [->|]; [apply Z.bits_0|].
    apply Z.bits_above_log2; [lia|]. apply Z.lt_le_trans with 64%Z; [apply Z.log2_lt_pow2; lia|lia].
Qed.

Lemma lo64_mk128 : forall hi lo, (0 <= lo < 2^64)%Z -> (0 <= hi < 2^64)%Z -> lo64 (mk128 hi lo) = lo.
Proof. intros. apply lo64_mk128'; lia. Qed.

Lemma hi64_mk128 : forall hi lo, (0 <= lo < 2^64)%Z -> (0 <= hi < 2^64)%Z -> hi64 (mk128 hi lo) = hi.
Proof.
  intros hi lo Hlo Hhi. unfold hi64, mk128. rewrite wrap64_mod.
  rewrite Z.shiftr_lor, Z.shiftr_shiftl_l, Z.sub_diag, Z.shiftl_0_r by lia.
  rewrite (Z.shiftr_div_pow2 lo), Z.div_small, Z.lor_0_r by lia. apply Z.mod_small. lia.
Qed.

(* [comment removed for export] *)
Lemma mk128_regs : forall hi lo, (0 <= lo < 2^64)%Z -> (0 <= hi < 2^64)%Z ->
  Z_to_bv 64 (lo64 (mk128 hi lo)) = Z_to_bv 64 lo /\ Z_to_bv 64 (hi64 (mk128 hi lo)) = Z_to_bv 64 hi.
Proof. intros. rewrite lo64_mk128, hi64_mk128 by lia. split; reflexivity. Qed.

Lemma lor_disjoint_add : forall a b, Z.land a b = 0%Z -> Z.lor a b = (a + b)%Z.
Proof. intros a b H. rewrite <- Z.lxor_lor by exact H. symmetry. apply Z.add_nocarry_lxor. exact H. Qed.

(* [comment removed for export] *)
Lemma land_even_mask : forall y, Z.land y 18446744073709551614 = (Z.land y 18446744073709551615 - Z.land y 1)%Z.
Proof.
  intros y. change 18446744073709551615%Z with (Z.lor 18446744073709551614 1).
  rewrite Z.land_lor_distr_r, lor_disjoint_add; [lia|].
  rewrite (Z.land_comm (Z.land y _) (Z.land y 1)), Z.land_assoc, (Z.land_comm (Z.land y 1) y), Z.land_assoc, Z.land_diag.
  rewrite <- Z.land_assoc. change (Z.land 1 18446744073709551614) with 0%Z. apply Z.land_0_r.
Qed.

Lemma land_1 : forall y, Z.land y 1 = (y mod 2)%Z.
Proof. intros. change 1%Z with (Z.ones 1) at 1. rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma land_W64 : forall y, Z.land y 18446744073709551615 = (y mod 2^64)%Z.
Proof. intros. change 18446744073709551615%Z with (Z.ones 64). apply Z.land_ones. lia. Qed.

(* [comment removed for export] *)
Lemma round_even_idiom : forall x, (0 <= x)%Z ->
  Z_to_bv 64 (Z.land (x + 1) 18446744073709551614) = Z_to_bv 64 (x + Z.land x 1).
Proof.
  intros x Hx. apply Z_to_bv_eqm. rewrite land_even_mask, land_W64, !land_1.
  Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Ltac bool_atom_cases :=
  repeat match goal with
  | |- context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b)
  | |- context [Z.eqb ?a ?b] => destruct (Z.eqb_spec a b)
  | |- context [Z.leb ?a ?b] => destruct (Z.leb_spec0 a b)
  end.

(* [comment removed for export] *)
Ltac weq :=
  first [ reflexivity
        | f_equal; zeq
        | rewrite round_even_idiom by zrange_nonneg; weq_arith
        | weq_arith ]
with weq_arith :=
  apply Z_to_bv_eqm; rewrite ?land_even_mask, ?land_1; zb_masks; cbv delta [Z.b2z]; cbn [negb];
  bool_atom_cases; cbn [negb]; pose_word_ranges; Z.div_mod_to_equations; lia.

(* [comment removed for export] *)
Ltac ms_eq :=
  first [ reflexivity
        | lazymatch goal with
          | |- Z_to_bv 64 _ = Z_to_bv 64 _ => weq
          | |- _ = Z_to_bv 64 (bv_unsigned _) => symmetry; apply Z_to_bv_bv_unsigned
          | |- Z_to_bv 64 (bv_unsigned _) = _ => apply Z_to_bv_bv_unsigned
          | |- context [mkR] => unfold mkR; ms_eq
          | |- MS _ _ _ _ _ _ _ = MS _ _ _ _ _ _ _ => f_equal; ms_eq
          | |- TNode _ _ _ = TNode _ _ _ => f_equal; ms_eq
          | |- Some _ = Some _ => f_equal; ms_eq
          end ].

(* [comment removed for export] *)
Ltac sf_finish :=
  apply evt_done;
  lazymatch goal with |- ?P ?ms => try unfold P end; hnf;
  rewrite ?lo64_mk128, ?hi64_mk128 by zrange;
  repeat (lazymatch goal with |- ex _ => eexists end);
  split; [ ms_eq | repeat match goal with |- _ /\ _ => split end; try assumption ].

(* [comment removed for export] *)
Lemma signed_of_Z : forall z, (-2^63 <= z < 2^63)%Z -> bv_signed (Z_to_bv 64 z) = z.
Proof.
  intros z Hz. rewrite Z_to_bv_signed. apply bv_swrap_small. unfold bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 64 / 2)%Z with (2^63)%Z. lia.
Qed.
Ltac signed_lits_in H :=
  repeat match type of H with
  | context [bv_signed (Z_to_bv 64 ?z)] => rewrite (signed_of_Z z) in H by lia
  end.

(* [comment removed for export] *)
Lemma mod64_land63 : forall y, (y mod 64 = Z.land y 63)%Z.
Proof. intros. change 63%Z with (Z.ones 6). rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma land63_idem : forall y, Z.land (Z.land y 63) 63 = Z.land y 63.
Proof. intros. rewrite <- Z.land_assoc. reflexivity. Qed.

Ltac zs_idioms_sf :=
  match goal with
  | |- context [Z.shiftr (Z.land (Z.shiftl ?x ?k) 18446744073709551615) ?k] =>
      rewrite (zb_shl_shr_land x k) by (first [lia | zrange_nonneg])
  | |- context [(?y mod 64)%Z] => rewrite (mod64_land63 y), ?land63_idem
  end.
Ltac zs_idioms_sf_in H :=
  match type of H with
  | context [Z.shiftr (Z.land (Z.shiftl ?x ?k) 18446744073709551615) ?k] =>
      rewrite (zb_shl_shr_land x k) in H by (first [lia | zrange_nonneg])
  | context [(?y mod 64)%Z] => rewrite (mod64_land63 y), ?land63_idem in H
  end.
Ltac zs_idioms ::= zs_idioms_sf.
Ltac zs_idioms_in H ::= zs_idioms_sf_in H.
