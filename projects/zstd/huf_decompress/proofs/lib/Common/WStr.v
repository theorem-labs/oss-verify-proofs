(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (9 recorded proofs replaced by written proofs (cu_of_Z, Forall_cu_of_Z, sx32_eqb0 and 6 more)). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import MState Mem Cells Step Arr Bytes.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import StrFun.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_WStr () := "C46Stdlib5Lists4List8nil_consC47Corelib4Init5Logic8eq_ind_rC46Stdlib5Lists4List:firstn_nilC56Stdlib6ZArith6BinInt1Z2leK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z6moduloI47Corelib4Init5Logic2eq00K47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K47Corelib7Numbers7BinNums1N02K46Stdlib9micromega7EnvRing5PExpr07K47Corelib4Init9Datatypes6option02C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z9mod_smallC45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions;bv_unsignedC59OSSVerify5KrLib3Lib6MState<unsigned_litC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common4WStr2cuC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01K47Corelib7Numbers7BinNums8positive03I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib5Lists7ListDef6Forall00I45stdpp9bitvector;definitions2bv00C47Corelib4Init5Logic3notC47Corelib5Lists7ListDef3mapK47Corelib5Lists7ListDef6Forall01K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula07c59OSSVerify5KrLib6Common4WStr7cu_of_ZC1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall02K47Corelib4Init9Datatypes4list02C47Corelib5Lists7ListDef:Forall_indK46Stdlib9micromega=RingMicromega3Op201I47Corelib4Init5Logic5False00C45stdpp9bitvector;definitions8bv_swrapC45stdpp9bitvector;definitions7bv_wrapC56Stdlib6ZArith6BinInt1Z3eqbC45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC56Stdlib6ZArith6BinInt1Z8eqb_specI47Corelib4Init9Datatypes7reflect00K47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z6eqb_eqC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC56Stdlib6ZArith6BinInt1Z7compareC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega7EnvRing5PExpr04C56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z7eqb_neqC56Stdlib6ZArith6BinInt1Z4of_NC45stdpp9bitvector;definitions@Z_to_bv_unsignedC59OSSVerify5KrLib3Lib3Mem4sx32C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbK46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz06K47Corelib4Init9Datatypes4bool02I47Corelib4Init9Datatypes:comparison00I47Corelib4Init5Logic4True00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01I47Corelib4Init9Datatypes6option00C59OSSVerify5KrLib3Lib3Arr4u32sC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem8bytes_atC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6to_natC46Stdlib5Lists4List9nth_errorK47Corelib4Init9Datatypes6option01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesC59OSSVerify5KrLib3Lib3Mem3le4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Arr:u32s_splitC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3appC47Corelib4Init9Datatypes6lengthI47Corelib4Init5Logic2ex00C47Corelib4Init3Nat3mulC56Stdlib6ZArith6BinInt1Z6of_natC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses5mkrelC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z8max_specI47Corelib4Init5Logic2or00K46Stdlib9micromega5Tauto8GFormula06C46Stdlib9micromega;ZifyClasses;rew_iff_revC47Corelib5Lists7ListDef5skipnC47Corelib5Lists7ListDef6firstnC47Corelib4Init3Nat3subC46Stdlib5Lists4List9app_nil_rC46Stdlib5Lists4List8firstn_0C56Stdlib5Arith8PeanoNat3Nat3subC56Stdlib5Arith8PeanoNat3Nat8sub_diagC59OSSVerify5KrLib3Lib3Mem:length_le4C1?~~~~~~~~~~~~~~~I47Corelib4Init5Peano2le00C46Stdlib5Lists4List;firstn_all2C46Stdlib5Lists4List:firstn_appC46Stdlib5Lists4List9app_nil_lC46Stdlib5Lists4List7skipn_0C46Stdlib5Lists4List:skipn_all2C46Stdlib5Lists4List9skipn_appC47Corelib4Init3Nat3addC46Stdlib5Lists4List:length_appC59OSSVerify5KrLib3Lib3Mem@bytes_at_ov_readC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC59OSSVerify5KrLib3Lib3Mem2waC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3maxC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2I47Corelib4Init9Datatypes3nat00C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib5Arith8PeanoNat3Nat3mulC56Stdlib6ZArith4Znat5Nat2Z7inj_mulC56Stdlib6ZArith4Znat5Nat2Z6inj_leC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addI4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00C59OSSVerify5KrLib3Lib5Bytes<bytes_ok_mapC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Bytes<le_val_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Bytes6le_valC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:length_mapC4ELinuxProcessSemantics?LinuxProcessSem6BvBase=bytes_le_to_ZC59OSSVerify5KrLib3Lib5BytesDbytes_le_to_Z_le_valC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesC59OSSVerify5KrLib6Common6StrFunBZ_to_le_bytes_to_ZC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem6BvBase@le_bytes_to_wordK47Corelib4Init5Logic3and01C46Stdlib9micromega;ZifyClasses9and_morphK47Corelib4Init5Logic2ex01C46Stdlib5Lists4List<length_skipnC46Stdlib5Lists4List<firstn_skipnC47Corelib4Init3Nat3minC56Stdlib6ZArith6BinInt1Z3minC56Stdlib6ZArith6BinInt1Z8min_specC46Stdlib5Lists4List=length_firstnc59OSSVerify5KrLib6Common4WStr<le4_of_bytesC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes7nat_indC56Stdlib6ZArith4Znat5Nat2Z8inj_succC56Stdlib6ZArith4Znat5Nat2Z;inj_sub_maxC56Stdlib5Arith8PeanoNat3Nat3minC56Stdlib6ZArith4Znat5Nat2Z7inj_minC59OSSVerify5KrLib3Lib3Arr5u8arrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem5wr_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Arr6u32arrC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common4WStr=u32s_of_bytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Arr;u32s_lengthC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition cu (w : word) : Z := bv_unsigned w mod 2^32.

(* [comment removed for export] *)
Lemma cu_of_Z : forall c, 0 <= c < 2^32 -> cu (Z_to_bv 64 c) = c.
Proof. intros c Hc. unfold cu. rewrite unsigned_lit by lia. apply Z.mod_small. lia. Qed.

Lemma Forall_cu_of_Z : forall cs, Forall (fun c => 0 < c < 2^32) cs -> Forall (fun w => cu w <> 0) (map (Z_to_bv 64) cs).
Proof.
  intros cs H. induction H as [|c cs Hc H IH]; cbn; constructor; [|exact IH].
  rewrite cu_of_Z by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma sx32_eqb0 : forall w, bv_eqb (sx32 w) (Z_to_bv 64 0) = (cu w =? 0).
Proof.
  intros w. unfold sx32, cu, bv_eqb. rewrite !Z_to_bv_unsigned.
  pose proof (bv_unsigned_in_range 64 w) as R.
  unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus in *.
  cbn -[Z.modulo Z.add Z.sub Z.mul Z.pow bv_unsigned Z.eqb Z.le Z.lt] in *.
  change (2^32 `div` 2) with (2^31).
  destruct (Z.eqb_spec (bv_unsigned w mod 2^32) 0) as [E|NE].
  - apply Z.eqb_eq. Z.div_mod_to_equations. nia.
  - apply Z.eqb_neq. Z.div_mod_to_equations. nia.
Qed.

(* [comment removed for export] *)
Lemma u32ro_read : forall segs m A ws (i : Z) w a,
  bytes_at segs m A (u32s ws) -> nth_error ws (Z.to_nat i) = Some w -> 0 <= i -> a = wa (A + 4 * i) ->
  ov_read_bytes segs m a 4 = Some (le4 w).
Proof.
  intros segs m A ws i w a STR Hn Hi ->.
  destruct (u32s_split _ _ _ Hn) as (pre & post & E & Hlen & Eu & Hlu).
  replace (4 * i) with (Z.of_nat (4 * Z.to_nat i)) by lia.
  rewrite (bytes_at_ov_read segs m A (u32s ws) (4 * Z.to_nat i) 4 STR).
  2:{ rewrite Eu, !length_app, length_le4, Hlu. lia. }
  rewrite Eu, skipn_app, skipn_all2, Hlu, Nat.sub_diag by lia. rewrite skipn_O, app_nil_l.
  rewrite firstn_app, firstn_all2 by (rewrite length_le4; lia).
  rewrite length_le4, Nat.sub_diag, firstn_O, app_nil_r. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma le4_of_bytes : forall bs : list byte, length bs = 4%nat -> le4 (le_bytes_to_word bs) = bs.
Proof.
  intros bs HL. unfold le4, le_bytes_to_word.
  pose proof (le_val_range _ (bytes_ok_map bs)) as HR. rewrite length_map, HL in HR.
  change (256 ^ Z.of_nat 4) with (2^32) in HR. rewrite <- bytes_le_to_Z_le_val in HR.
  rewrite unsigned_lit by lia. rewrite <- HL. apply Z_to_le_bytes_to_Z.
Qed.

Lemma u32s_of_bytes : forall k (bs : list byte), length bs = (4 * k)%nat ->
  exists ws, length ws = k /\ u32s ws = bs.
Proof.
  induction k as [|k IH]; intros bs HL.
  - exists []. destruct bs; [split; reflexivity| cbn in HL; lia].
  - destruct (IH (skipn 4 bs) ltac:(rewrite length_skipn; lia)) as (ws & Hlen & Hu).
    exists (le_bytes_to_word (firstn 4 bs) :: ws). split; [cbn; lia|].
    cbn [u32s]. rewrite Hu, le4_of_bytes by (rewrite length_firstn; lia). apply firstn_skipn.
Qed.

Lemma u32arr_of_u8arr : forall segs m A bs k,
  u8arr segs m A bs -> length bs = (4 * k)%nat ->
  exists ws, length ws = k /\ u32s ws = bs /\ u32arr segs m A ws.
Proof.
  intros segs m A bs k [Hb Hw] HL.
  destruct (u32s_of_bytes k bs HL) as (ws & Hlen & Hu). exists ws. split; [exact Hlen|]. split; [exact Hu|]. split.
  - rewrite Hu. exact Hb.
  - rewrite Hlen. replace (4 * Z.of_nat k) with (Z.of_nat (length bs)) by lia. exact Hw.
Qed.

Lemma u8arr_of_u32arr : forall segs m A ws, u32arr segs m A ws -> u8arr segs m A (u32s ws).
Proof.
  intros segs m A ws [Hb Hw]. split; [exact Hb|]. rewrite u32s_length.
  replace (Z.of_nat (4 * length ws)) with (4 * Z.of_nat (length ws)) by lia. exact Hw.
Qed.

(* [comment removed for export] *)
Lemma cu_le_bytes_to_word : forall bs : list byte, length bs = 4%nat ->
  cu (le_bytes_to_word bs) = le_val (map bv_unsigned bs).
Proof.
  intros bs HL. unfold cu, le_bytes_to_word.
  pose proof (le_val_range _ (bytes_ok_map bs)) as HR. rewrite length_map, HL in HR.
  change (256 ^ Z.of_nat 4) with (2^32) in HR. rewrite bytes_le_to_Z_le_val.
  rewrite unsigned_lit by lia. apply Z.mod_small. lia.
Qed.
