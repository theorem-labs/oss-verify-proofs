(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc27 Q13u QwAs QvDJ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import Qc27 Q13u QwAs.
Import QvDJ.Mq3.
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
End Mq0.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import Qc27 Q13u QwAs.
Import QvDJ.Mq3.
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
End Mq1.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc27.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc27. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q13u.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q13u. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHig.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHig.
Import ListNotations.
Open Scope Z_scope.

Ltac small_offset k :=
let b := eval vm_compute in (andb (Z.leb (-4096) k) (Z.ltb k 4096))%Z in
lazymatch b with true => idtac end. Ltac mkr__small_offset_0 k := let b := eval vm_compute in (andb (Z.leb (-4096) k) (Z.ltb k 4096))%Z in
lazymatch b with true => idtac end.

Ltac solve_load_safe :=
match goal with
| |- context [ov_read_bytes ?segs ?m ?a ?n] =>
let E := addr_expr a in
match goal with
| H : rw_cells segs m ?A ?cs0 |- _ =>
let k := addr_diff E A in
small_offset k;
let kn := eval vm_compute in (Z.to_nat k) in
split_for_access H segs m A cs0 kn n;
let cs := lazymatch type of H with rw_cells _ _ _ ?cs => cs end in
let c := eval_cell_at cs kn in
lazymatch c with Some ?c0 =>
rewrite (rw_cells_read_at segs m A cs kn c0 n a H) by (first [cells_cbv; reflexivity | reflexivity | addr_eq_tac])
end
| H : ro_cells segs m ?A ?cs0 |- _ =>
let k := addr_diff E A in
small_offset k;
let kn := eval vm_compute in (Z.to_nat k) in
split_for_access H segs m A cs0 kn n;
let cs := lazymatch type of H with ro_cells _ _ _ ?cs => cs end in
let c := eval_cell_at cs kn in
lazymatch c with Some ?c0 =>
rewrite (ro_cells_read_at segs m A cs kn c0 n a H) by (first [cells_cbv; reflexivity | reflexivity | addr_eq_tac])
end
| HR : ov_read_bytes segs m ?a' n = Some ?bs |- _ =>
cbv delta [wa] in HR;
first [ rewrite HR
| replace (ov_read_bytes segs m a n) with (Some bs)
by (rewrite <- HR; f_equal; word_eq_tac) ]
end
end;
load_post.

Ltac solve_store_safe :=
match goal with
| |- context [store_ok ?segs ?m ?a ?n] =>
rewrite ?store_bytes_8', ?store_bytes_4', ?store_bytes_2', ?store_bytes_1';
let E := addr_expr a in
match goal with
| H : rw_cells segs m ?A ?cs0 |- _ =>
let k := addr_diff E A in
small_offset k;
let kn := eval vm_compute in (Z.to_nat k) in
split_for_access H segs m A cs0 kn n;
let cs := lazymatch type of H with rw_cells _ _ _ ?cs => cs end in
let c := eval_cell_at cs kn in
lazymatch c with Some ?c0 =>
rewrite (rw_cells_store_ok_at segs m A cs kn c0 n a H) by (first [cells_cbv; reflexivity | reflexivity | addr_eq_tac]);
cbv beta iota;
match goal with
| |- context [write_to_mem m a ?bs] =>
replace (write_to_mem m a bs) with (write_to_mem m (wa (A + Z.of_nat kn)) bs) by (f_equal; addr_eq_tac)
end
end
| HS : store_ok segs m ?a' n = true |- _ =>
cbv delta [wa] in HS;
first [ rewrite HS
| replace (store_ok segs m a n) with true
by (rewrite <- HS; f_equal; word_eq_tac);
try replace (write_to_mem m a) with (write_to_mem m a')
by (f_equal; word_eq_tac) ];
cbv beta iota
end
end.

Ltac solve_load ::= first [ solve_load_safe | solve_load_image ]. Ltac mkr__solve_load_1 := first [ solve_load_safe | solve_load_image ].
Ltac solve_store ::= solve_store_safe. Ltac mkr__solve_store_2 := solve_store_safe.

Lemma amo_aligned_intro4 : forall a : Z, (0 <= a < 2^64)%Z -> (a mod 4 = 0)%Z -> amo_aligned AW (Z_to_bv 64 a) = true.
Proof. intros a Ha Hm. unfold amo_aligned, amo_bytes. rewrite unsigned_lit by lia. rewrite Hm. reflexivity. Qed.
Lemma amo_aligned_intro8 : forall a : Z, (0 <= a < 2^64)%Z -> (a mod 8 = 0)%Z -> amo_aligned AD (Z_to_bv 64 a) = true.
Proof. intros a Ha Hm. unfold amo_aligned, amo_bytes. rewrite unsigned_lit by lia. rewrite Hm. reflexivity. Qed.

Ltac amo_align AMO :=
try (rewrite AMO; cbv beta iota delta [negb]);
try (rewrite Z.eqb_refl; cbv iota).

Ltac amo_step AMO :=
lazymatch goal with
| |- evt ?segs ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc ?rv ?m ?ro) =>
let fw := eval vm_compute in (fetch_word segs (Z_to_bv 64 pc)) in
lazymatch fw with Some ?w =>
let d := eval vm_compute in (decode_any w) in
lazymatch d with Some (?i, ?sz) =>
eapply evt_step;
[ split; [reflexivity|];
rewrite (step_gen segs R F (Z_to_bv 64 pc) fc rv m ro w i sz) by (vm_compute; reflexivity);
exec_cbv; simp_is_x0; simp_regs; amo_align AMO; exec_cbv; simp_is_x0; simp_regs; amo_align AMO; vnorm_for i;
try solve_load; try solve_store; reflexivity
| simp_regs; vnorm_for i; mem_after_store_opt ]
end end
end. Ltac mkr__amo_step_3 AMO := lazymatch goal with
| |- evt ?segs ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc ?rv ?m ?ro) =>
let fw := eval vm_compute in (fetch_word segs (Z_to_bv 64 pc)) in
lazymatch fw with Some ?w =>
let d := eval vm_compute in (decode_any w) in
lazymatch d with Some (?i, ?sz) =>
eapply evt_step;
[ split; [reflexivity|];
rewrite (step_gen segs R F (Z_to_bv 64 pc) fc rv m ro w i sz) by (vm_compute; reflexivity);
exec_cbv; simp_is_x0; simp_regs; amo_align AMO; exec_cbv; simp_is_x0; simp_regs; amo_align AMO; vnorm_for i;
try solve_load; try solve_store; reflexivity
| simp_regs; vnorm_for i; mem_after_store_opt ]
end end
end.

Ltac if_lit := first [ if_true | if_false ]. Ltac mkr__if_lit_4 := first [ if_true | if_false ].

Ltac fix_lit_store :=
try (lazymatch goal with
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) =>
change (Z_to_le_bytes 8 z) with (le8 (Z_to_bv 64 z)); mem_after_store
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) =>
change (Z_to_le_bytes 4 z) with (le4 (Z_to_bv 64 z)); mem_after_store
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 2 ?z)) _) =>
change (Z_to_le_bytes 2 z) with (le2 (Z_to_bv 64 z)); mem_after_store
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 1 ?z)) _) =>
change (Z_to_le_bytes 1 z) with [Z_to_bv 8 z]; mem_after_store
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 (Z_to_bv 64 ?z))) _) =>
change (le1 (Z_to_bv 64 z)) with [Z_to_bv 8 z]; mem_after_store
end).
