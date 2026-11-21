(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (29 recorded proofs replaced by written proofs (lw_u, lw_wrap32, lw_mod32 and 26 more)). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import StrFun.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_STRW_merge () := "K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C45stdpp9bitvector;definitions;bv_unsignedK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z3divc59OSSVerify5KrLib6Common:STRW_merge2v4C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00K47Corelib4Init5Logic2eq01K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02C4ELinuxProcessSemantics?LinuxProcessSem6BvBase@le_bytes_to_wordC45stdpp9bitvector;definitions:bv_extractC4ELinuxProcessSemantics5Riscv7Prelude4sextC59OSSVerify5KrLib6Common6StrFun<lw_unsigned4C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rK47Corelib7Numbers7BinNums8positive03I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1N01C45stdpp9bitvector;definitions7bv_wrapC56Stdlib6ZArith6BinInt1Z6moduloC59OSSVerify5KrLib6Common6StrFun:byte_rangeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib6ZArith6BinInt1Z2leC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC56Stdlib6ZArith6BinInt1Z7compareC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega:ZMicromega;ZArithProof03I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr07K47Corelib4Init9Datatypes6option02K47Corelib7Numbers7BinNums8positive01K46Stdlib9micromega7EnvRing5PExpr04C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC59OSSVerify5KrLib6Common6StrFun<bv_wrap32_eqC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common:STRW_merge4lw_uC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega5Tauto8GFormula08K47Corelib7Numbers7BinNums1Z01K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op205K46Stdlib9micromega=RingMicromega3Op201I47Corelib4Init9Datatypes:comparison00I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic5False00c59OSSVerify5KrLib6Common:STRW_merge9lw_wrap32C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC56Stdlib6ZArith6BinInt1Z9mod_smallC45stdpp9bitvector;definitions8bv_swrapC59OSSVerify5KrLib6Common6StrFun=bv_swrap32_eqC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3lorC56Stdlib6ZArith6BinInt1Z4onesC56Stdlib6ZArith6BinInt1Z4landC56Stdlib6ZArith6BinInt1Z@land_lor_distr_lC56Stdlib6ZArith6BinInt1Z9land_onesC46Stdlib6ZArith4ZdivAZmult_mod_idemp_lC56Stdlib6ZArith6BinInt1Z6shiftlC56Stdlib6ZArith6BinInt1Z?shiftl_mul_pow2C47Corelib4Init9Datatypes6lengthC47Corelib5Lists7ListDef3mapC59OSSVerify5KrLib3Lib5Bytes6le_valC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7Z_to_bvC59OSSVerify5KrLib3Lib6MStateAunsigned_lit_wrapC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common6StrFun<le4_of_mod32C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00C59OSSVerify5KrLib6Common6StrFun;le1_of_mod8C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6shiftrc59OSSVerify5KrLib6Common:STRW_merge;mod64_smallC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common:STRW_merge=swrap32_smallC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2c59OSSVerify5KrLib6Common:STRW_merge8lw_mod32C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common:STRW_merge9shl_mod32C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common:STRW_merge=swrap32_mod32C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common:STRW_merge;mod64_mod32C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common6StrFun8lor_add'C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common:STRW_merge4hi_aC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common:STRW_merge9lor_mod32C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common:STRW_merge@le4_lit_of_mod32C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common:STRW_merge3hi8C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common:STRW_merge4lo24C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common:STRW_merge4hi16C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common:STRW_merge4lo16C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common:STRW_merge4hi24C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common:STRW_merge3lo8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common6StrFun7lor_addC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common:STRW_merge4hi_rC1?~~~~~~~~~~~~~~~C46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC59OSSVerify5KrLib3Lib9LiaTuning9zify_doneC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula03c59OSSVerify5KrLib6Common:STRW_merge?le1_lit_of_mod8C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic4True01".
Import ListNotations.
Local Open Scope Z_scope.

Local Notation LW w := (sext 64 (bv_extract 0 32 (le_bytes_to_word w))).
Local Notation M64 := 18446744073709551616%Z.

(* [comment removed for export] *)
Definition v4 (b0 b1 b2 b3 : byte) : Z :=
  bv_unsigned b0 + 256 * bv_unsigned b1 + 65536 * bv_unsigned b2 + 16777216 * bv_unsigned b3.

Local Ltac br b := pose proof (byte_range b).

Lemma lw_u b0 b1 b2 b3 :
  bv_unsigned (LW [b0;b1;b2;b3]) = v4 b0 b1 b2 b3 + (2^64 - 2^32) * (bv_unsigned b3 / 128).
Proof. rewrite lw_unsigned4. reflexivity. Qed.

Lemma lw_wrap32 b0 b1 b2 b3 : bv_wrap 32 (bv_unsigned (LW [b0;b1;b2;b3])) = v4 b0 b1 b2 b3.
Proof.
  rewrite lw_u, bv_wrap32_eq. br b0; br b1; br b2; br b3. unfold v4.
  Z.div_mod_to_equations. lia.
Qed.

Lemma lw_mod32 b0 b1 b2 b3 : (bv_unsigned (LW [b0;b1;b2;b3])) mod 2^32 = v4 b0 b1 b2 b3.
Proof. rewrite <- bv_wrap32_eq. apply lw_wrap32. Qed.

Lemma swrap32_small x : 0 <= x < 2^31 -> bv_swrap 32 x = x.
Proof. intros. rewrite bv_swrap32_eq. rewrite Z.mod_small; lia. Qed.
Lemma mod64_small x : 0 <= x < 2^64 -> x mod M64 = x.
Proof. intros. apply Z.mod_small. lia. Qed.
Lemma mod32_small x : 0 <= x < 2^32 -> x mod 2^32 = x.
Proof. intros. apply Z.mod_small. lia. Qed.

Lemma swrap32_mod32 x : (bv_swrap 32 x) mod 2^32 = x mod 2^32.
Proof. rewrite bv_swrap32_eq. Z.div_mod_to_equations. lia. Qed.

Lemma mod64_mod32 x : (x mod M64) mod 2^32 = x mod 2^32.
Proof. Z.div_mod_to_equations. lia. Qed.

Lemma lor_mod32 a b : (Z.lor a b) mod 2^32 = Z.lor (a mod 2^32) (b mod 2^32).
Proof. rewrite <- !Z.land_ones by lia. apply Z.land_lor_distr_l. Qed.

Lemma shl_mod32 x j : 0 <= j -> (Z.shiftl x j) mod 2^32 = ((x mod 2^32) * 2^j) mod 2^32.
Proof. intros. rewrite Z.shiftl_mul_pow2, <- Zmult_mod_idemp_l by lia. reflexivity. Qed.

(* [comment removed for export] *)
Lemma le4_lit_of_mod32 z (bs : list byte) : length bs = 4%nat ->
  (z mod M64) mod 2^32 = le_val (map bv_unsigned bs) -> le4 (Z_to_bv 64 z) = bs.
Proof.
  intros Hl Hz. apply le4_of_mod32; [exact Hl|]. rewrite unsigned_lit_wrap. exact Hz.
Qed.
Lemma le1_lit_of_mod8 z (b : byte) :
  (z mod M64) mod 2^8 = bv_unsigned b -> le1 (Z_to_bv 64 z) = [b].
Proof. intros Hz. apply le1_of_mod8. rewrite unsigned_lit_wrap. exact Hz. Qed.

Section merge.
  Variables b0 b1 b2 b3 c0 c1 c2 c3 : byte.

  (* [comment removed for export] *)
  Lemma lo24 : (bv_swrap 32 (Z.shiftr (bv_wrap 32 (bv_unsigned (LW [b0;b1;b2;b3]))) 24)) mod M64 mod 2^32 = bv_unsigned b3.
  Proof.
    rewrite lw_wrap32, Z.shiftr_div_pow2 by lia. br b0; br b1; br b2; br b3. unfold v4.
    replace (_ / 2^24) with (bv_unsigned b3) by (Z.div_mod_to_equations; lia).
    rewrite swrap32_small, mod64_small by lia. apply Z.mod_small. lia.
  Qed.
  Lemma lo16 : (bv_swrap 32 (Z.shiftr (bv_wrap 32 (bv_unsigned (LW [b0;b1;b2;b3]))) 16)) mod M64 mod 2^32 = bv_unsigned b2 + 256 * bv_unsigned b3.
  Proof.
    rewrite lw_wrap32, Z.shiftr_div_pow2 by lia. br b0; br b1; br b2; br b3. unfold v4.
    replace (_ / 2^16) with (bv_unsigned b2 + 256 * bv_unsigned b3) by (Z.div_mod_to_equations; lia).
    rewrite swrap32_small, mod64_small by lia. apply Z.mod_small. lia.
  Qed.
  Lemma lo8 : (bv_swrap 32 (Z.shiftr (bv_wrap 32 (bv_unsigned (LW [b0;b1;b2;b3]))) 8)) mod M64 mod 2^32 = bv_unsigned b1 + 256 * bv_unsigned b2 + 65536 * bv_unsigned b3.
  Proof.
    rewrite lw_wrap32, Z.shiftr_div_pow2 by lia. br b0; br b1; br b2; br b3. unfold v4.
    replace (_ / 2^8) with (bv_unsigned b1 + 256 * bv_unsigned b2 + 65536 * bv_unsigned b3) by (Z.div_mod_to_equations; lia).
    rewrite swrap32_small, mod64_small by lia. apply Z.mod_small. lia.
  Qed.

  Lemma hi8 : (v4 c0 c1 c2 c3 * 2^8) mod 2^32 = 256 * bv_unsigned c0 + 65536 * bv_unsigned c1 + 16777216 * bv_unsigned c2.
  Proof. br c0; br c1; br c2; br c3. unfold v4. Z.div_mod_to_equations. lia. Qed.
  Lemma hi16 : (v4 c0 c1 c2 c3 * 2^16) mod 2^32 = 65536 * bv_unsigned c0 + 16777216 * bv_unsigned c1.
  Proof. br c0; br c1; br c2; br c3. unfold v4. Z.div_mod_to_equations. lia. Qed.
  Lemma hi24 : (v4 c0 c1 c2 c3 * 2^24) mod 2^32 = 16777216 * bv_unsigned c0.
  Proof. br c0; br c1; br c2; br c3. unfold v4. Z.div_mod_to_equations. lia. Qed.

  (* [comment removed for export] *)
  Lemma hi_a j : 0 <= j -> ((bv_swrap 32 (Z.shiftl (bv_unsigned (LW [c0;c1;c2;c3])) j)) mod M64) mod 2^32 = (v4 c0 c1 c2 c3 * 2^j) mod 2^32.
  Proof. intros. rewrite mod64_mod32, swrap32_mod32, shl_mod32, lw_mod32 by lia. reflexivity. Qed.
  Lemma hi_r j : 0 <= j -> ((Z.shiftl (bv_unsigned (LW [c0;c1;c2;c3])) j) mod M64) mod 2^32 = (v4 c0 c1 c2 c3 * 2^j) mod 2^32.
  Proof. intros. rewrite mod64_mod32, shl_mod32, lw_mod32 by lia. reflexivity. Qed.

  Local Ltac merge_tac lo hi hik k :=
    apply le4_lit_of_mod32; [reflexivity|];
    rewrite mod64_mod32, lor_mod32, lo, hi, hik by lia; cbn [map le_val];
    br b0; br b1; br b2; br b3; br c0; br c1; br c2; br c3;
    first [ rewrite (lor_add' _ _ k); [ lia | lia | lia | Z.div_mod_to_equations; lia ]
          | rewrite (lor_add _ _ k); [ lia | lia | lia | Z.div_mod_to_equations; lia ] ].

  (* [comment removed for export] *)
  Lemma merge_a24 :
    le4 (Z_to_bv 64 (Z.lor ((bv_swrap 32 (Z.shiftr (bv_wrap 32 (bv_unsigned (LW [b0;b1;b2;b3]))) 24)) mod M64)
                            ((bv_swrap 32 (Z.shiftl (bv_unsigned (LW [c0;c1;c2;c3])) 8)) mod M64)))
    = [b3; c0; c1; c2].
  Proof. merge_tac lo24 hi_a hi8 8%Z. Qed.
  Lemma merge_a16 :
    le4 (Z_to_bv 64 (Z.lor ((bv_swrap 32 (Z.shiftr (bv_wrap 32 (bv_unsigned (LW [b0;b1;b2;b3]))) 16)) mod M64)
                            ((bv_swrap 32 (Z.shiftl (bv_unsigned (LW [c0;c1;c2;c3])) 16)) mod M64)))
    = [b2; b3; c0; c1].
  Proof. merge_tac lo16 hi_a hi16 16%Z. Qed.
  Lemma merge_a8 :
    le4 (Z_to_bv 64 (Z.lor ((bv_swrap 32 (Z.shiftr (bv_wrap 32 (bv_unsigned (LW [b0;b1;b2;b3]))) 8)) mod M64)
                            ((bv_swrap 32 (Z.shiftl (bv_unsigned (LW [c0;c1;c2;c3])) 24)) mod M64)))
    = [b1; b2; b3; c0].
  Proof. merge_tac lo8 hi_a hi24 24%Z. Qed.

  (* [comment removed for export] *)
  Lemma merge_r24 :
    le4 (Z_to_bv 64 (Z.lor ((Z.shiftl (bv_unsigned (LW [c0;c1;c2;c3])) 8) mod M64)
                            ((bv_swrap 32 (Z.shiftr (bv_wrap 32 (bv_unsigned (LW [b0;b1;b2;b3]))) 24)) mod M64)))
    = [b3; c0; c1; c2].
  Proof. merge_tac lo24 hi_r hi8 8%Z. Qed.
  Lemma merge_r16 :
    le4 (Z_to_bv 64 (Z.lor ((Z.shiftl (bv_unsigned (LW [c0;c1;c2;c3])) 16) mod M64)
                            ((bv_swrap 32 (Z.shiftr (bv_wrap 32 (bv_unsigned (LW [b0;b1;b2;b3]))) 16)) mod M64)))
    = [b2; b3; c0; c1].
  Proof. merge_tac lo16 hi_r hi16 16%Z. Qed.
  Lemma merge_r8 :
    le4 (Z_to_bv 64 (Z.lor ((Z.shiftl (bv_unsigned (LW [c0;c1;c2;c3])) 24) mod M64)
                            ((bv_swrap 32 (Z.shiftr (bv_wrap 32 (bv_unsigned (LW [b0;b1;b2;b3]))) 8)) mod M64)))
    = [b1; b2; b3; c0].
  Proof. merge_tac lo8 hi_r hi24 24%Z. Qed.

  (* [comment removed for export] *)
  Lemma lwb0 : le1 (LW [b0;b1;b2;b3]) = [b0].
  Proof.
    apply le1_of_mod8. rewrite lw_u. br b0; br b1; br b2; br b3. unfold v4.
    Z.div_mod_to_equations. lia.
  Qed.
  Lemma lwb1 : le1 (Z_to_bv 64 (Z.shiftr (bv_unsigned (LW [b0;b1;b2;b3])) 8)) = [b1].
  Proof.
    apply le1_lit_of_mod8. rewrite lw_u, Z.shiftr_div_pow2 by lia. br b0; br b1; br b2; br b3. unfold v4.
    replace (_ / 2^8) with (bv_unsigned b1 + 256 * bv_unsigned b2 + 65536 * bv_unsigned b3 + (2^56 - 2^24) * (bv_unsigned b3 / 128))
      by (Z.div_mod_to_equations; lia).
    rewrite mod64_small by lia. Z.div_mod_to_equations. lia.
  Qed.
  Lemma lwb2 : le1 (Z_to_bv 64 (Z.shiftr (bv_unsigned (LW [b0;b1;b2;b3])) 16)) = [b2].
  Proof.
    apply le1_lit_of_mod8. rewrite lw_u, Z.shiftr_div_pow2 by lia. br b0; br b1; br b2; br b3. unfold v4.
    replace (_ / 2^16) with (bv_unsigned b2 + 256 * bv_unsigned b3 + (2^48 - 2^16) * (bv_unsigned b3 / 128))
      by (Z.div_mod_to_equations; lia).
    rewrite mod64_small by lia. Z.div_mod_to_equations. lia.
  Qed.
End merge.
