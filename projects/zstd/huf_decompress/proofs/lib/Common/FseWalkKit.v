(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (36 recorded proofs replaced by written proofs (ite_true, ite_false, ite_negb_true and 33 more)). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import STRW_tac.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_FseWalkKit () := "I47Corelib4Init5Logic2eq00K47Corelib4Init5Logic2eq01C47Corelib4Init5Logic8eq_ind_rI47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib4Init9Datatypes4bool02C47Corelib4Init9Datatypes4negbK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z3subI47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums8positive03C46Stdlib5Lists4List8nil_consC46Stdlib5Lists4List:firstn_nilK47Corelib7Numbers7BinNums1Z03C56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00K47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega=RingMicromega7Formula01C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula08C56Stdlib6ZArith6BinInt1Z9mod_smallK47Corelib7Numbers7BinNums1N02C45stdpp9bitvector;definitions8bv_swrapc59OSSVerify5KrLib6Common:FseWalkKit:swrap32_eqC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op201K47Corelib7Numbers7BinNums1Z01K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205C45stdpp9bitvector;definitions7bv_wrapc59OSSVerify5KrLib6Common:FseWalkKit9wrap32_eqC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common:FseWalkKit:swrap16_eqC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC56Stdlib6ZArith6BinInt1Z7compareK47Corelib4Init9Datatypes3nat02K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega:ZMicromega;ZArithProof03K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega5Tauto8GFormula07K47Corelib7Numbers7BinNums8positive01K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega=RingMicromega5Psatz06I47Corelib4Init9Datatypes:comparison00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01I47Corelib4Init5Logic5False00C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z3oppK46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega7EnvRing5PExpr06C56Stdlib6ZArith6BinInt1Z7mod_addC47Corelib4Init5Logic6eq_indC45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions@Z_to_bv_unsignedC45stdpp9bitvector;definitions9bv_signedC45stdpp9bitvector;definitions>Z_to_bv_signedI45stdpp9bitvector;definitions2bv00c59OSSVerify5KrLib6Common:FseWalkKit4u16sC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthC47Corelib4Init3Nat3mulC59OSSVerify5KrLib3Lib3Mem3le2C1?~~~~~~~~~~~~~~~C47Corelib4Init3Nat3addC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC46Stdlib9micromega;ZifyClasses;rew_iff_revC59OSSVerify5KrLib3Lib3Mem:length_le2C1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3appC46Stdlib5Lists4List:length_appC47Corelib4Init9Datatypes8list_indC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses5mkrelI47Corelib4Init9Datatypes3nat00C56Stdlib5Arith8PeanoNat3Nat3mulC56Stdlib6ZArith4Znat5Nat2Z7inj_mulC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC56Stdlib6ZArith4Znat5Nat2Z8inj_succC46Stdlib5Lists4List9app_assocI47Corelib4Init9Datatypes6option00C46Stdlib5Lists4List9nth_errorK47Corelib4Init9Datatypes6option01C59OSSVerify5KrLib3Lib3Arr?nth_error_splitC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00K47Corelib4Init5Logic3and01c59OSSVerify5KrLib6Common:FseWalkKit;u16s_lengthC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common:FseWalkKit8u16s_appC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01C59OSSVerify5KrLib3Lib3Mem8bytes_atC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6to_natC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesc59OSSVerify5KrLib6Common:FseWalkKit:u16s_splitC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8iff_reflC56Stdlib6ZArith6BinInt1Z8max_specI47Corelib4Init5Logic2or00K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula06C47Corelib5Lists7ListDef5skipnC47Corelib5Lists7ListDef6firstnC47Corelib4Init3Nat3subC46Stdlib5Lists4List9app_nil_rC46Stdlib5Lists4List8firstn_0C56Stdlib5Arith8PeanoNat3Nat3subC56Stdlib5Arith8PeanoNat3Nat8sub_diagI47Corelib4Init5Peano2le00C46Stdlib5Lists4List;firstn_all2C46Stdlib5Lists4List:firstn_appC46Stdlib5Lists4List9app_nil_lC46Stdlib5Lists4List7skipn_0C46Stdlib5Lists4List:skipn_all2C46Stdlib5Lists4List9skipn_appC59OSSVerify5KrLib3Lib3Mem@bytes_at_ov_readC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem2waC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3maxC46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib6ZArith4Znat5Nat2Z6inj_leC59OSSVerify5KrLib3Lib3Arr5u8arrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem5wr_atC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common:FseWalkKit:u16ro_readC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC59OSSVerify5KrLib3Lib3Mem>wr_at_store_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Arr3updC1?~~~~~~~~~~~~~~~C47Corelib4Init5Peano2ltC59OSSVerify5KrLib3Lib3Arr=upd_app_splitC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem9upd_bytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3MemEbytes_at_write_insideC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Arr=upd_bytes_midC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem<bytes_at_extC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<write_to_memC59OSSVerify5KrLib3Lib3Mem;wr_at_writeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Arr:upd_lengthC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z6inj_ltC45stdpp9bitvector;definitions5bv_eqC45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions=bv_wrap_smallI47Corelib7Numbers7BinNums1N00C47Corelib5Lists7ListDef3mapc59OSSVerify5KrLib6Common:FseWalkKit@byte_of_unsignedC1?~~~~~~~~~~~~~~~I47Corelib5Lists7ListDef6Forall00K47Corelib5Lists7ListDef6Forall01C45stdpp9bitvector;definitions:bv_modulusK47Corelib5Lists7ListDef6Forall02C56Stdlib6ZArith6BinInt1Z4of_NC56Stdlib6ZArith6BinInt1Z6shiftrC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC59OSSVerify5KrLib3Lib3Mem<Z_to_bv8_modC1?~~~~~~~~~~~~~~~C35stdpp7tactics<f_equal_helpC56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2C4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesI47Corelib4Init5Logic4True00C56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith6BinInt1Z8ltb_specI47Corelib4Init9Datatypes8BoolSpec00c59OSSVerify5KrLib6Common:FseWalkKit;le2_of_pairC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes7nat_indC56Stdlib6ZArith6BinInt1Z=pow_le_mono_rC56Stdlib6ZArith6BinInt1Z7div_posC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC59OSSVerify5KrLib3Lib9LiaTuning9zify_doneC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1ZBdiv_lt_upper_boundc59OSSVerify5KrLib6Common:FseWalkKit=swrap32_smallC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic4True01C56Stdlib6ZArith6BinInt1Z6shiftlC56Stdlib6ZArith6BinInt1Z?shiftl_mul_pow2C56Stdlib6ZArith6BinInt1Z7mul_1_lc59OSSVerify5KrLib6Common:FseWalkKit<shiftl_mod32C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z=pow_lt_mono_rC56Stdlib6ZArith6BinInt1Z3lorC56Stdlib6ZArith6BinInt1Z4lxorC59OSSVerify5KrLib3Lib7ZBridgeBzb_lxor_pow2_smallC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib7ZBridgeBzb_land_pow2_smallC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8lxor_lorC56Stdlib6ZArith6BinInt1Z8lor_commC56Stdlib6ZArith6BinInt1Z7div_mulC59OSSVerify5KrLib3Lib3Mem3le1C1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

Ltac showpc := lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "pc =" pc | _ => idtac "showpc: not an evt goal" end.
Ltac showreg r := let v := reg_val r in idtac "x" r "=" v.
Ltac showmem := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m _) => idtac "mem =" m end.

(* [comment removed for export] *)
Ltac call_pure_post :=
  let ms' := fresh "ms'" in let PO := fresh "POST" in
  intros ms' PO; hnf in PO; destruct_exs PO; subst ms';
  try (lazymatch goal with
  | |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
  end).
Tactic Notation "call_pure" uconstr(SPEC) := eapply evt_cut; [ eapply SPEC | call_pure_post ].

(* [comment removed for export] *)
Lemma ite_true : forall (A : Type) (b : bool) (x y : A), b = true -> (if b then x else y) = x.
Proof. intros A b x y ->. reflexivity. Qed.
Lemma ite_false : forall (A : Type) (b : bool) (x y : A), b = false -> (if b then x else y) = y.
Proof. intros A b x y ->. reflexivity. Qed.
Lemma ite_negb_true : forall (A : Type) (b : bool) (x y : A), b = true -> (if negb b then x else y) = y.
Proof. intros A b x y ->. reflexivity. Qed.
Lemma ite_negb_false : forall (A : Type) (b : bool) (x y : A), b = false -> (if negb b then x else y) = x.
Proof. intros A b x y ->. reflexivity. Qed.

(* [comment removed for export] *)
Lemma swrap32_eq : forall z, bv_swrap 32 z = (z + 2147483648) mod 4294967296 - 2147483648.
Proof. reflexivity. Qed.
Lemma swrap32_small : forall z, - 2147483648 <= z < 2147483648 -> bv_swrap 32 z = z.
Proof. intros z Hz. rewrite swrap32_eq. rewrite Z.mod_small by lia. lia. Qed.
Lemma wrap32_eq : forall z, bv_wrap 32 z = z mod 4294967296.
Proof. reflexivity. Qed.
Lemma wrap32_small : forall z, 0 <= z < 4294967296 -> bv_wrap 32 z = z.
Proof. intros. rewrite wrap32_eq. apply Z.mod_small. lia. Qed.
Lemma swrap16_eq : forall z, bv_swrap 16 z = (z + 32768) mod 65536 - 32768.
Proof. reflexivity. Qed.
Lemma swrap16_small : forall z, - 32768 <= z < 32768 -> bv_swrap 16 z = z.
Proof. intros z Hz. rewrite swrap16_eq. rewrite Z.mod_small by lia. lia. Qed.

(* [comment removed for export] *)
Lemma swrap32_eqm : forall x y, - 2147483648 <= y < 2147483648 -> (x - y) mod 4294967296 = 0 -> bv_swrap 32 x = y.
Proof. intros x y Hy Hm. rewrite swrap32_eq. Z.div_mod_to_equations. lia. Qed.
Ltac sw32 y :=
  match goal with |- context [bv_swrap 32 ?x] =>
    rewrite (swrap32_eqm x y) by (first [ lia | Z.div_mod_to_equations; lia ])
  end.

(* [comment removed for export] *)
Lemma unsigned_neg : forall z, - 2^63 <= z < 0 -> bv_unsigned (Z_to_bv 64 z) = z + 2^64.
Proof.
  intros z Hz. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2^64).
  rewrite <- (Z.mod_add z 1) by lia. apply Z.mod_small. lia.
Qed.
Lemma signed_lit : forall z, - 2^63 <= z < 2^63 -> bv_signed (Z_to_bv 64 z) = z.
Proof.
  intros z Hz. rewrite Z_to_bv_signed. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 64) with (2^64). change (2^64 / 2) with (2^63).
  rewrite Z.mod_small by lia. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint u16s (ws : list word) : list byte :=
  match ws with [] => [] | w :: ws' => le2 w ++ u16s ws' end.

Lemma u16s_length : forall ws, length (u16s ws) = (2 * length ws)%nat.
Proof. induction ws; cbn -[le2]; [reflexivity|]. rewrite length_app, length_le2, IHws. lia. Qed.
Lemma u16s_app : forall a b, u16s (a ++ b) = u16s a ++ u16s b.
Proof. induction a; intros; cbn -[le2]; [reflexivity|]. rewrite IHa, app_assoc. reflexivity. Qed.

Ltac simpl_arr_sizes ::= rewrite ?u32s_length, ?u64s_length, ?upd_length, ?u16s_length, ?length_map in *.

Lemma u16s_split : forall ws i w, nth_error ws i = Some w ->
  exists pre post, ws = pre ++ w :: post /\ length pre = i /\
    u16s ws = u16s pre ++ le2 w ++ u16s post /\ length (u16s pre) = (2 * i)%nat.
Proof.
  intros ws i w H. destruct (nth_error_split _ _ _ H) as (pre & post & -> & Hlen).
  exists pre, post. rewrite u16s_app. cbn -[le2]. rewrite u16s_length. repeat split; lia.
Qed.

Section U16.
Variable segs : list Segment.

(* [comment removed for export] *)
Lemma u16ro_read : forall m A ws (i : Z) w a,
  bytes_at segs m A (u16s ws) -> nth_error ws (Z.to_nat i) = Some w -> 0 <= i -> a = wa (A + 2 * i) ->
  ov_read_bytes segs m a 2 = Some (le2 w).
Proof.
  intros m A ws i w a Hb Hn Hi ->.
  destruct (u16s_split _ _ _ Hn) as (pre & post & E & Hlen & Eu & Hlu).
  replace (2 * i) with (Z.of_nat (2 * Z.to_nat i)) by lia.
  rewrite (bytes_at_ov_read segs m A (u16s ws) (2 * Z.to_nat i) 2 Hb).
  2:{ rewrite Eu, !length_app, length_le2, Hlu. lia. }
  rewrite Eu, skipn_app, skipn_all2, Hlu, Nat.sub_diag by lia. rewrite skipn_O, app_nil_l.
  rewrite firstn_app, firstn_all2 by (rewrite length_le2; lia).
  rewrite length_le2, Nat.sub_diag, firstn_O, app_nil_r. reflexivity.
Qed.

Lemma u16arr_read : forall m A ws (i : Z) w a,
  u8arr segs m A (u16s ws) -> nth_error ws (Z.to_nat i) = Some w -> 0 <= i -> a = wa (A + 2 * i) ->
  ov_read_bytes segs m a 2 = Some (le2 w).
Proof. intros m A ws i w a [Hb _]. apply u16ro_read. exact Hb. Qed.

Lemma u16arr_store_ok : forall m A ws (i : Z) a,
  u8arr segs m A (u16s ws) -> 0 <= i < Z.of_nat (length ws) -> a = wa (A + 2 * i) ->
  store_ok segs m a 2 = true.
Proof. intros m A ws i a [_ Hw] Hi ->. rewrite u16s_length in Hw. eapply wr_at_store_ok; eauto; lia. Qed.

Lemma u16arr_write : forall m A ws (i : Z) (v : word),
  u8arr segs m A (u16s ws) -> 0 <= i < Z.of_nat (length ws) ->
  u8arr segs (write_to_mem m (wa (A + 2 * i)) (le2 v)) A (u16s (upd ws (Z.to_nat i) v)).
Proof.
  intros m A ws i v [Hb Hw] Hi.
  destruct (upd_app_split ws (Z.to_nat i) v ltac:(lia)) as (pre & y & post & E & Hlen & Hupd).
  split.
  - eapply bytes_at_ext.
    { apply (bytes_at_write_inside segs m A (u16s ws) (2 * i) (le2 v) Hb); [lia|].
      rewrite length_le2, u16s_length. lia. }
    rewrite Hupd, E, !u16s_app. cbn [u16s].
    replace (Z.to_nat (2 * i)) with (length (u16s pre)) by (rewrite u16s_length; lia).
    apply upd_bytes_mid. rewrite !length_le2. reflexivity.
  - rewrite !u16s_length, upd_length in *. apply wr_at_write. exact Hw.
Qed.
End U16.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma byte_of_unsigned : forall b : byte, Z_to_bv 8 (bv_unsigned b) = b.
Proof.
  intros b. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.
Lemma bytes_of_unsigned : forall bs : list byte, map (Z_to_bv 8) (map bv_unsigned bs) = bs.
Proof. induction bs as [|b bs IH]; cbn; [reflexivity|]. rewrite byte_of_unsigned, IH. reflexivity. Qed.
Lemma bytes_unsigned_range : forall bs : list byte, Forall (fun c => 0 <= c < 256) (map bv_unsigned bs).
Proof.
  induction bs as [|b bs IH]; cbn; constructor; [|exact IH].
  pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. cbn in R. lia.
Qed.
Lemma byte_lit : forall c, 0 <= c < 256 -> bv_unsigned (Z_to_bv 8 c) = c.
Proof. intros c Hc. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. cbn. lia. Qed.

Lemma le2_of_pair : forall (b0 b1 : byte) c,
  - 32768 <= c < 32768 -> c mod 65536 = bv_unsigned b0 + 256 * bv_unsigned b1 ->
  le2 (Z_to_bv 64 c) = [b0; b1].
Proof.
  intros b0 b1 c Hc E.
  pose proof (bv_unsigned_in_range 8 b0) as R0. pose proof (bv_unsigned_in_range 8 b1) as R1.
  unfold bv_modulus in R0, R1. cbn in R0, R1.
  unfold le2. cbn [Z_to_le_bytes]. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with 18446744073709551616.
  f_equal; [|f_equal].
  - rewrite <- (byte_of_unsigned b0). apply Z_to_bv8_mod. change (2^8) with 256. Z.div_mod_to_equations. lia.
  - rewrite <- (byte_of_unsigned b1). apply Z_to_bv8_mod. rewrite Z.shiftr_div_pow2 by lia. change (2^8) with 256.
    Z.div_mod_to_equations. lia.
Qed.

Lemma u16s_of_bytes : forall (n : nat) (bs : list byte), length bs = (2 * n)%nat ->
  exists ws : list Z, length ws = n /\ Forall (fun c => - 32768 <= c < 32768) ws /\ bs = u16s (map (Z_to_bv 64) ws).
Proof.
  induction n as [|n IH]; intros bs L.
  - destruct bs; [|cbn in L; lia]. exists []. repeat split; constructor.
  - destruct bs as [|b0 [|b1 bs]]; cbn in L; try lia.
    destruct (IH bs ltac:(lia)) as (ws & Lw & Fw & E).
    pose proof (bv_unsigned_in_range 8 b0) as R0. pose proof (bv_unsigned_in_range 8 b1) as R1.
    unfold bv_modulus in R0, R1. cbn in R0, R1.
    set (w := bv_unsigned b0 + 256 * bv_unsigned b1).
    exists ((if w <? 32768 then w else w - 65536) :: ws).
    split; [cbn; lia|]. split.
    + constructor; [|exact Fw]. destruct (Z.ltb_spec w 32768); subst w; lia.
    + cbn [map u16s]. rewrite <- E.
      rewrite (le2_of_pair b0 b1); [reflexivity| |].
      * destruct (Z.ltb_spec w 32768); subst w; lia.
      * destruct (Z.ltb_spec w 32768); subst w; Z.div_mod_to_equations; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma swrap32_mod32 : forall z, (bv_swrap 32 z) mod 4294967296 = z mod 4294967296.
Proof. intros z. rewrite swrap32_eq. Z.div_mod_to_equations. lia. Qed.
Lemma swrap32_mod64_mod32 : forall z, ((bv_swrap 32 z) mod 18446744073709551616) mod 4294967296 = z mod 4294967296.
Proof. intros z. rewrite swrap32_eq. Z.div_mod_to_equations. lia. Qed.
Lemma mod64_mod32 : forall z, (z mod 18446744073709551616) mod 4294967296 = z mod 4294967296.
Proof. intros z. Z.div_mod_to_equations. lia. Qed.

(* [comment removed for export] *)
Lemma srliw_val : forall x k, 0 < k < 32 -> bv_swrap 32 (Z.shiftr (bv_wrap 32 x) k) = (x mod 4294967296) / 2^k.
Proof.
  intros x k Hk. rewrite wrap32_eq, Z.shiftr_div_pow2 by lia.
  assert (P : 2 <= 2^k) by (change 2 with (2^1) at 1; apply Z.pow_le_mono_r; lia).
  pose proof (Z.mod_pos_bound x 4294967296 ltac:(lia)) as R.
  apply swrap32_small. split.
  - pose proof (Z.div_pos (x mod 4294967296) (2^k) ltac:(lia) ltac:(lia)). lia.
  - apply Z.div_lt_upper_bound; [lia|]. nia.
Qed.

(* [comment removed for export] *)
Lemma shiftl_mod32 : forall x k, 0 <= k < 32 -> Z.shiftl x (k mod 32) = x * 2^k.
Proof. intros x k Hk. rewrite Z.mod_small by lia. apply Z.shiftl_mul_pow2. lia. Qed.
Lemma sllw_pow2 : forall k, 0 <= k < 31 -> bv_swrap 32 (Z.shiftl 1 (k mod 32)) = 2^k.
Proof.
  intros k Hk. rewrite shiftl_mod32 by lia. rewrite Z.mul_1_l. apply swrap32_small.
  assert (0 < 2^k) by (apply Z.pow_pos_nonneg; lia).
  assert (2^k <= 2^30) by (apply Z.pow_le_mono_r; lia). change (2^30) with 1073741824 in *. lia.
Qed.
Lemma lor_pow2_1 : forall k, 1 <= k -> Z.lor (2^k) 1 = 2^k + 1.
Proof.
  intros k Hk.
  assert (P : 1 < 2^k) by (change 1 with (2^0) at 1; apply Z.pow_lt_mono_r; lia).
  rewrite Z.lor_comm. rewrite <- Z.lxor_lor by (apply zb_land_pow2_small; lia).
  rewrite zb_lxor_pow2_small by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma zext32_sh31 : forall x, 0 <= x < 4294967296 -> Z.shiftr (Z.shiftl x 32 mod 18446744073709551616) 31 = 2 * x.
Proof.
  intros x Hx. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. change (2^32) with 4294967296. change (2^31) with 2147483648.
  rewrite Z.mod_small by lia. replace (x * 4294967296) with ((2 * x) * 2147483648) by lia. apply Z.div_mul. lia.
Qed.
Lemma zext32_sh32 : forall x, 0 <= x < 4294967296 -> Z.shiftr (Z.shiftl x 32 mod 18446744073709551616) 32 = x.
Proof.
  intros x Hx. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. change (2^32) with 4294967296.
  rewrite Z.mod_small by lia. apply Z.div_mul. lia.
Qed.

(* [comment removed for export] *)
Lemma le1_lit : forall x, le1 (Z_to_bv 64 x) = [Z_to_bv 8 x].
Proof.
  intros x. unfold le1. cbn [Z_to_le_bytes]. f_equal. apply Z_to_bv8_mod.
  rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with 18446744073709551616. change (2^8) with 256.
  Z.div_mod_to_equations. lia.
Qed.
