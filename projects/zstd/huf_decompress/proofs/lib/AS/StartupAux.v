(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (22 recorded proofs replaced by written proofs (getr_empty, land_align_mask, v_andi_m16_aligned and 19 more)). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zstd.huf_decompress.lib.AS Require Import
  PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk StreamSim MemSplit.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_StartupAux () := "K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00K45stdpp9bitvector;definitions2bv01C4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC45stdpp9bitvector;definitions7Z_to_bvC4ELinuxProcessSemantics5Riscv7Prelude;bvmap_emptyC4ELinuxProcessSemantics5Riscv3Sem7reg_getI47Corelib4Init5Logic2eq00K47Corelib4Init5Logic2eq01C4ELinuxProcessSemantics5Riscv7Prelude6bv_keyK4ELinuxProcessSemantics5Riscv7Prelude4tree01C4ELinuxProcessSemantics5Riscv7Prelude4tgetC45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions5bv_eqC59OSSVerify5KrLib2AS8PropExec4getrC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03K47Corelib7Numbers7BinNums1Z01K47Corelib4Init5Logic4True01I47Corelib4Init9Datatypes4bool00I47Corelib7Numbers7BinNums8positive00I47Corelib4Init9Datatypes6option00C4ELinuxProcessSemantics5Riscv3Sem2w0I47Corelib7Numbers7BinNums1N00I47Corelib4Init5Logic3and00I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z4onesC56Stdlib6ZArith6BinInt1Z4lnotC56Stdlib6ZArith6BinInt1Z4landC56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z4predC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega7EnvRing5PExpr02C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z:ones_equivK47Corelib4Init9Datatypes6option02C56Stdlib6ZArith6BinInt1Z=ones_mod_pow2C56Stdlib6ZArith6BinInt1Z9land_onesC56Stdlib6ZArith8Zbitwise1Z?sub_land_same_lC47Corelib4Init5Logic6eq_indC56Stdlib6ZArith6BinInt1Z5ldiffC56Stdlib6ZArith6BinInt1Z:ldiff_landC56Stdlib6ZArith6BinInt1Z6shiftrC56Stdlib6ZArith6BinInt1Z6shiftlK46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03C46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing5PExpr03C56Stdlib6ZArith6BinInt1Z?shiftl_mul_pow2C56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2C56Stdlib6ZArith6BinInt1Z<ldiff_ones_rC56Stdlib6ZArith6BinInt1Z9mod_smallC56Stdlib6ZArith6BinInt1Z:land_assocK46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04C47Corelib4Init5Logic8eq_ind_rK46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula07K47Corelib4Init9Datatypes4list02K46Stdlib9micromega=RingMicromega3Op201C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205I46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib4Init5Logic4True00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic5False00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01C45stdpp9bitvector;definitions7bv_wrapC59OSSVerify5KrLib2AS8PropExec9u64_rangeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4of_NC46Stdlib9micromega;ZifyClasses6eq_iffC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses9and_morphC46Stdlib9micromega;ZifyClasses;rew_iff_revC45stdpp9bitvector;definitions:bv_modulusC45stdpp9bitvector;definitions=bv_wrap_smallC56Stdlib6ZArith6BinInt1Z<eq_decidableI47Corelib4Init5Logic2or00K46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega5Tauto8GFormula06c59OSSVerify5KrLib2AS:StartupAux?land_align_maskC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions@Z_to_bv_unsignedC59OSSVerify5KrLib2AS8PropExec6v_andiC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega8ZifyInst7Inj_Z_Zc59OSSVerify5KrLib2AS:StartupAux=land_low_zeroC1?~~~~~~~~~~~~~~~C35stdpp7tactics<f_equal_helpC56Stdlib6ZArith6BinInt1Z7testbitC47Corelib4Init9Datatypes4andbC56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z8eqb_specI47Corelib4Init9Datatypes7reflect00C56Stdlib6ZArith6BinInt1Z=testbit_neg_rC56Stdlib6ZArith6BinInt1Z=mul_pow2_bitsC46Stdlib4Bool4Bool<andb_false_rC56Stdlib6ZArith6BinInt1Z=pow2_bits_eqbC56Stdlib6ZArith6BinInt1Z6bits_0C56Stdlib6ZArith6BinInt1Z9land_specC56Stdlib6ZArith6BinInt1Z9bits_inj'K47Corelib4Init9Datatypes4bool02c59OSSVerify5KrLib2AS:StartupAux?land_4_aligned8C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z9pow_add_rK47Corelib4Init5Logic2ex01C56Stdlib6ZArith4Zdiv1Z>mod_mod_divideC45stdpp9bitvector;definitions8bv_swrapC45stdpp9bitvector;definitions?bv_half_modulusC46Stdlib6ZArith4ZdivBZminus_mod_idemp_rc59OSSVerify5KrLib2AS:StartupAux=mod4_mod_pow2C1?~~~~~~~~~~~~~~~C46Stdlib6ZArith4ZdivBZminus_mod_idemp_lC59OSSVerify5KrLib2AS8PropExec=bv_wrap64_modC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8PropExec6v_subwC1?~~~~~~~~~~~~~~~I47Corelib4Init5Peano2le00C4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesC47Corelib5Lists7ListDef6firstnC56Stdlib6ZArith6BinInt1Z6of_natC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC47Corelib4Init9Datatypes7nat_indI47Corelib4Init9Datatypes3nat00C56Stdlib6ZArith4Znat5Nat2Z8inj_succC56Stdlib6ZArith4Znat5Nat2Z6inj_lec59OSSVerify5KrLib2AS:StartupAuxDfirstn_Z_to_le_bytesC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesC59OSSVerify5KrLib2AS8PropExec3rdnC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01c59OSSVerify5KrLib2AS:StartupAuxGfirstn_word_to_le_bytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS7SeqExec:rdn_firstnC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00C4ELinuxProcessSemantics?LinuxProcessSem6BvBase=bytes_le_to_ZC59OSSVerify5KrLib2AS8PropExec:bytes_le_NC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3oppK46Stdlib9micromega7EnvRing5PExpr06C45stdpp9bitvector;definitions>bv_swrap_smallC59OSSVerify5KrLib2AS8PropExec4v_lwC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS7StepTac6u_Z2bvC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8PropExec5v_addC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing3Pol03K46Stdlib9micromega=RingMicromega5Psatz03K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega5Tauto8GFormula01C59OSSVerify5KrLib2AS8PropExec6v_slliC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz05C46Stdlib5Lists4List7existsbC46Stdlib5Lists4List7forallbC46Stdlib5Lists4List2InC47Corelib4Init5Logic9False_indC46Stdlib4Bool4Bool=andb_true_iffC47Corelib4Init9Datatypes3orbC46Stdlib4Bool4Bool<orb_true_iffC56Stdlib6ZArith6BinInt1Z6eqb_eqC47Corelib4Init5Logic6eq_symK47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02C47Corelib4Init9Datatypes8list_indC45stdpp9bitvector;definitionsDbv_unsigned_in_rangec59OSSVerify5KrLib2AS:StartupAux<Z_to_bv_u_eqC1?~~~~~~~~~~~~~~~".
(* [comment removed for export] *)
Unset Lia Cache.
Unset Nia Cache.
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma getr_empty : forall r : reg, getr bvmap_empty r = Z_to_bv 64 0.
Proof.
  intro r. unfold getr. destruct (bv_eqb r 0); [reflexivity|].
  unfold reg_get, bvmap_get, bvmap_empty.
  destruct (bv_key r); cbn [tget]; apply bv_eq; reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Local Open Scope Z_scope.

Lemma land_align_mask : forall a k, 0 <= a < 2^64 -> 0 <= k <= 64 -> a mod 2^k = 0 ->
  Z.land a (2^64 - 2^k) = a.
Proof.
  intros a k Ha Hk Hmod.
  replace (2^64 - 2^k) with (Z.ldiff (Z.ones 64) (Z.ones k)).
  2:{ rewrite Z.ldiff_land, <- Z.sub_land_same_l, Z.land_ones by lia.
      rewrite Z.ones_mod_pow2 by lia. rewrite !Z.ones_equiv. lia. }
  rewrite Z.ldiff_land, Z.land_assoc, Z.land_ones by lia.
  rewrite Z.mod_small by lia.
  rewrite <- Z.ldiff_land, Z.ldiff_ones_r by lia.
  rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia.
  pose proof (Z.div_mod a (2^k) ltac:(lia)). lia.
Qed.

(* [comment removed for export] *)
Lemma v_andi_m16_aligned : forall x : word,
  bv_unsigned x mod 16 = 0 -> v_andi x (-16) = x.
Proof.
  intros x Hm. unfold v_andi. apply bv_eq. rewrite Z_to_bv_unsigned.
  change (bv_wrap 64 (-16)) with (2^64 - 2^4).
  pose proof (u64_range x).
  rewrite land_align_mask by (first [lia | exact Hm]).
  apply bv_wrap_small. unfold bv_modulus. lia.
Qed.

(* [comment removed for export] *)
Lemma v_andi_m8_aligned : forall x : word,
  bv_unsigned x mod 8 = 0 -> v_andi x (-8) = x.
Proof.
  intros x Hm. unfold v_andi. apply bv_eq. rewrite Z_to_bv_unsigned.
  change (bv_wrap 64 (-8)) with (2^64 - 2^3).
  pose proof (u64_range x).
  rewrite land_align_mask by (first [lia | exact Hm]).
  apply bv_wrap_small. unfold bv_modulus. lia.
Qed.

(* [comment removed for export] *)
Lemma land_low_zero : forall a k, 0 <= a -> 0 <= k -> a mod 2^k = 0 -> Z.land a (Z.ones k) = 0.
Proof. intros a k Ha Hk Hm. rewrite Z.land_ones by lia. exact Hm. Qed.

Lemma v_andi_3_aligned : forall x : word,
  bv_unsigned x mod 4 = 0 -> v_andi x 3 = Z_to_bv 64 0.
Proof.
  intros x Hm. unfold v_andi. f_equal.
  change (bv_wrap 64 3) with (Z.ones 2). apply land_low_zero; [apply u64_range | lia | exact Hm].
Qed.

Lemma land_4_aligned8 : forall a, 0 <= a -> a mod 8 = 0 -> Z.land a 4 = 0.
Proof.
  intros a Ha Hm.
  apply Z.bits_inj'. intros i Hi.
  rewrite Z.land_spec, Z.bits_0.
  change 4 with (2^2). rewrite Z.pow2_bits_eqb by lia.
  destruct (Z.eqb_spec 2 i); [|apply andb_false_r].
  subst i.
  replace a with ((a / 8) * 2^3) by lia.
  rewrite Z.mul_pow2_bits by lia. change (2 - 3) with (-1).
  rewrite Z.testbit_neg_r by lia. reflexivity.
Qed.

Lemma v_andi_4_aligned8 : forall x : word,
  bv_unsigned x mod 8 = 0 -> v_andi x 4 = Z_to_bv 64 0.
Proof.
  intros x Hm. unfold v_andi. f_equal.
  change (bv_wrap 64 4) with 4. apply land_4_aligned8; [apply u64_range | exact Hm].
Qed.

Lemma v_andi_1_of01 : forall z, (z = 0 \/ z = 1) ->
  v_andi (Z_to_bv 64 z) 1 = Z_to_bv 64 z.
Proof.
  intros z [-> | ->]; apply bv_eq; reflexivity.
Qed.

Lemma mod4_mod_pow2 : forall t k, 2 <= k -> (t mod 2^k) mod 4 = t mod 4.
Proof.
  intros t k Hk. apply Z.mod_mod_divide.
  exists (2^(k-2)). change 4 with (2^2). rewrite <- Z.pow_add_r by lia. f_equal. lia.
Qed.

(* [comment removed for export] *)
Lemma negw_and3_aligned : forall x : word,
  bv_unsigned x mod 4 = 0 -> v_andi (v_subw (Z_to_bv 64 0) x) 3 = Z_to_bv 64 0.
Proof.
  intros x Hm. unfold v_andi, v_subw. f_equal.
  change (bv_wrap 64 3) with (Z.ones 2). rewrite Z.land_ones by lia.
  rewrite Z_to_bv_unsigned. change (bv_unsigned (Z_to_bv 64 0)) with 0.
  unfold bv_swrap. rewrite bv_wrap64_mod.
  change (bv_half_modulus 32) with (2^31).
  unfold bv_wrap. change (bv_modulus 32) with (2^32). change (2^2) with 4.
  rewrite mod4_mod_pow2 by lia.
  rewrite <- Zminus_mod_idemp_l.
  rewrite mod4_mod_pow2 by lia.
  replace ((0 - bv_unsigned x + 2^31) mod 4) with 0.
  2:{ replace (0 - bv_unsigned x + 2^31) with (2^31 - bv_unsigned x) by lia.
      rewrite <- Zminus_mod_idemp_r, Hm. reflexivity. }
  reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma firstn_Z_to_le_bytes : forall k n z, (k <= n)%nat ->
  firstn k (Z_to_le_bytes n z) = Z_to_le_bytes k z.
Proof.
  induction k as [|k IH]; intros n z Hk; [reflexivity|].
  destruct n as [|n]; [lia|]. cbn [Z_to_le_bytes firstn]. rewrite IH by lia. reflexivity.
Qed.

Lemma firstn_word_to_le_bytes : forall k n (v : word), (k <= n)%nat ->
  firstn k (word_to_le_bytes n v) = word_to_le_bytes k v.
Proof. intros. unfold word_to_le_bytes. apply firstn_Z_to_le_bytes. assumption. Qed.

(* [comment removed for export] *)
Lemma rdn_low_bytes : forall segs m (a v : word) k, (k <= 8)%nat ->
  rdn segs m a 8 = Some (word_to_le_bytes 8 v) ->
  rdn segs m a k = Some (word_to_le_bytes k v).
Proof.
  intros segs m a v k Hk H.
  rewrite (rdn_firstn segs m 8 a _ k H Hk). f_equal. apply firstn_word_to_le_bytes. exact Hk.
Qed.

Lemma bytes_le_to_Z_4_small : forall v : word, bv_unsigned v < 2^32 ->
  bytes_le_to_Z (word_to_le_bytes 4 v) = bv_unsigned v.
Proof.
  intros v Hv. rewrite bytes_le_N. change (2 ^ (8 * Z.of_nat 4)) with (2^32).
  apply Z.mod_small. pose proof (u64_range v). lia.
Qed.

Lemma v_lw_small : forall v : word, bv_unsigned v < 2^31 -> v_lw v = v.
Proof.
  intros v Hv. unfold v_lw. apply bv_eq. rewrite Z_to_bv_unsigned.
  pose proof (u64_range v).
  rewrite bv_swrap_small by (change (bv_half_modulus 32) with (2^31); lia).
  apply bv_wrap_small. unfold bv_modulus. lia.
Qed.

(* [comment removed for export] *)
Lemma v_add_lit_r : forall (x : word) (k : Z), 0 <= k < 2^64 ->
  v_add x (Z_to_bv 64 k) = Z_to_bv 64 (bv_unsigned x + k).
Proof. intros x k Hk. unfold v_add. rewrite (u_Z2bv k) by lia. reflexivity. Qed.

Lemma v_add_lit_l : forall (x : word) (k : Z), 0 <= k < 2^64 ->
  v_add (Z_to_bv 64 k) x = Z_to_bv 64 (bv_unsigned x + k).
Proof. intros x k Hk. unfold v_add. rewrite (u_Z2bv k) by lia. f_equal. lia. Qed.

(* [comment removed for export] *)
Lemma v_slli_lit : forall z sh, 0 <= z -> 0 <= sh -> z * 2^sh < 2^64 ->
  v_slli (Z_to_bv 64 z) sh = Z_to_bv 64 (z * 2^sh).
Proof.
  intros z sh Hz Hsh Hb. unfold v_slli. f_equal.
  rewrite Z.shiftl_mul_pow2 by lia. rewrite u_Z2bv by nia. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma in_sub_bv : forall (l1 l2 : list reg) (r : reg),
  forallb (fun x => existsb (fun y => bv_eqb x y) l2) l1 = true -> In r l1 -> In r l2.
Proof.
  induction l1 as [|x l1 IH]; intros l2 r H Hin; [contradiction|].
  cbn [forallb] in H. apply andb_true_iff in H as [Hx Hl1].
  destruct Hin as [<-|Hin]; [|apply IH; assumption].
  clear IH Hl1. induction l2 as [|y l2 IH2]; [discriminate|].
  cbn [existsb] in Hx. apply orb_true_iff in Hx as [Hxy|Hx].
  - left. symmetry. apply bv_eq. unfold bv_eqb in Hxy. apply Z.eqb_eq in Hxy. exact Hxy.
  - right. apply IH2. exact Hx.
Qed.

Lemma Z_to_bv_u_eq : forall (a : word) (z : Z), z = bv_unsigned a -> Z_to_bv 64 z = a.
Proof. intros a z ->. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range. Qed.

Lemma Z_to_bv_u_eq_sym : forall (a : word) (z : Z), z = bv_unsigned a -> a = Z_to_bv 64 z.
Proof. intros a z H. symmetry. apply Z_to_bv_u_eq. exact H. Qed.
