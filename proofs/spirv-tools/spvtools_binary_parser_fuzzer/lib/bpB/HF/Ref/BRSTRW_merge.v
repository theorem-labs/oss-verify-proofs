(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BArr BBytes.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BStrFun.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Notation LW w := (sext 64 (bv_extract 0 32 (le_bytes_to_word w))).
Local Notation M64 := 18446744073709551616%Z.

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

Lemma swrap32_mod32 x : (bv_swrap 32 x) mod 2^32 = x mod 2^32.
Proof. rewrite bv_swrap32_eq. Z.div_mod_to_equations. lia. Qed.

Lemma mod64_mod32 x : (x mod M64) mod 2^32 = x mod 2^32.
Proof. Z.div_mod_to_equations. lia. Qed.

Lemma lor_mod32 a b : (Z.lor a b) mod 2^32 = Z.lor (a mod 2^32) (b mod 2^32).
Proof. rewrite <- !Z.land_ones by lia. apply Z.land_lor_distr_l. Qed.

Lemma shl_mod32 x j : 0 <= j -> (Z.shiftl x j) mod 2^32 = ((x mod 2^32) * 2^j) mod 2^32.
Proof. intros. rewrite Z.shiftl_mul_pow2, <- Zmult_mod_idemp_l by lia. reflexivity. Qed.

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
