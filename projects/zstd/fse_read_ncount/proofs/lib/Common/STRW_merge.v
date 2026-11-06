(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Tac Arr Bytes.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import StrFun.
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
Z.div_mod_to_equations. Local Ltac2 Set LiaHints.tbl := fun () => "0010>63361140727.2200000ES1H2H02H12H22H32H82H9".
lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma lw_mod32 b0 b1 b2 b3 : (bv_unsigned (LW [b0;b1;b2;b3])) mod 2^32 = v4 b0 b1 b2 b3.
Proof. rewrite <- bv_wrap32_eq. apply lw_wrap32. Qed.
Lemma swrap32_small x : 0 <= x < 2^31 -> bv_swrap 32 x = x.
Proof. intros. rewrite bv_swrap32_eq. rewrite Z.mod_small; lia. Qed.
Lemma mod64_small x : 0 <= x < 2^64 -> x mod M64 = x.
Proof. intros. apply Z.mod_small. Local Ltac2 Set LiaHints.tbl := fun () => "0010=53493744851.2000003S1H".
lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma swrap32_mod32 x : (bv_swrap 32 x) mod 2^32 = x mod 2^32.
Proof. rewrite bv_swrap32_eq. Z.div_mod_to_equations. Local Ltac2 Set LiaHints.tbl := fun () => "0010>11447729963.2200000?S1H2H02H42H52H9".
lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma mod64_mod32 x : (x mod M64) mod 2^32 = x mod 2^32.
Proof. Z.div_mod_to_equations. Local Ltac2 Set LiaHints.tbl := fun () => "0010>11447729963.2200000?S1H2H02H42H52H9".
lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma lor_mod32 a b : (Z.lor a b) mod 2^32 = Z.lor (a mod 2^32) (b mod 2^32).
Proof. rewrite <- !Z.land_ones by lia. apply Z.land_lor_distr_l. Qed.
Lemma shl_mod32 x j : 0 <= j -> (Z.shiftl x j) mod 2^32 = ((x mod 2^32) * 2^j) mod 2^32.
Proof. intros. Local Ltac2 Set LiaHints.tbl := fun () => "0010=45266465884.3000003S1H".
rewrite Z.shiftl_mul_pow2, <- Zmult_mod_idemp_l by lia. reflexivity. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
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
#[using="Type"] Lemma lo24 : (bv_swrap 32 (Z.shiftr (bv_wrap 32 (bv_unsigned (LW [b0;b1;b2;b3]))) 24)) mod M64 mod 2^32 = bv_unsigned b3.
Proof.
Local Ltac2 Set LiaHints.tbl := fun () => "0050>18079477964.1218656728080.1941890909355.8 61309814396.1268412087420.1200000400C00D00H00LS2H2S1H2H02H12H32H4SS2H2S2H2".
rewrite lw_wrap32, Z.shiftr_div_pow2 by lia. br b0; br b1; br b2; br b3. unfold v4.
replace (_ / 2^24) with (bv_unsigned b3) by (Z.div_mod_to_equations; lia).
rewrite swrap32_small, mod64_small by lia. apply Z.mod_small. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma lo16 : (bv_swrap 32 (Z.shiftr (bv_wrap 32 (bv_unsigned (LW [b0;b1;b2;b3]))) 16)) mod M64 mod 2^32 = bv_unsigned b2 + 256 * bv_unsigned b3.
Proof.
Local Ltac2 Set LiaHints.tbl := fun () => "0050>16039846688.1223030800656.1262544251032.1965501743147.8 8929201440.12 00000700>00J00K00RS2H12H2S2H12H2S1H2H02H32H4SS2H12H2".
rewrite lw_wrap32, Z.shiftr_div_pow2 by lia. br b0; br b1; br b2; br b3. unfold v4.
replace (_ / 2^16) with (bv_unsigned b2 + 256 * bv_unsigned b3) by (Z.div_mod_to_equations; lia).
rewrite swrap32_small, mod64_small by lia. apply Z.mod_small. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma lo8 : (bv_swrap 32 (Z.shiftr (bv_wrap 32 (bv_unsigned (LW [b0;b1;b2;b3]))) 8)) mod M64 mod 2^32 = bv_unsigned b1 + 256 * bv_unsigned b2 + 65536 * bv_unsigned b3.
Proof.
Local Ltac2 Set LiaHints.tbl := fun () => "0050>16039846688.1223030800656.1228661439595.1963367611819.8 8929201440.12 00000:00D00M00N00XS2H02H12H2S2H02H12H2S1H2H32H4SS2H02H12H2".
rewrite lw_wrap32, Z.shiftr_div_pow2 by lia. br b0; br b1; br b2; br b3. unfold v4.
replace (_ / 2^8) with (bv_unsigned b1 + 256 * bv_unsigned b2 + 65536 * bv_unsigned b3) by (Z.div_mod_to_equations; lia).
rewrite swrap32_small, mod64_small by lia. apply Z.mod_small. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma hi8 : (v4 c0 c1 c2 c3 * 2^8) mod 2^32 = 256 * bv_unsigned c0 + 65536 * bv_unsigned c1 + 16777216 * bv_unsigned c2.
Proof. br c0; br c1; br c2; br c3. unfold v4. Z.div_mod_to_equations. Local Ltac2 Set LiaHints.tbl := fun () => "0010=2412704738.1900000?S1H2H02H12H32H4".
lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma hi16 : (v4 c0 c1 c2 c3 * 2^16) mod 2^32 = 65536 * bv_unsigned c0 + 16777216 * bv_unsigned c1.
Proof. br c0; br c1; br c2; br c3. unfold v4. Z.div_mod_to_equations. Local Ltac2 Set LiaHints.tbl := fun () => "0010>38281126810.1900000<S1H2H02H32H4".
lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma hi24 : (v4 c0 c1 c2 c3 * 2^24) mod 2^32 = 16777216 * bv_unsigned c0.
Proof. br c0; br c1; br c2; br c3. unfold v4. Z.div_mod_to_equations. Local Ltac2 Set LiaHints.tbl := fun () => "0010>58649097460.19000009S1H2H32H4".
lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma hi_a j : 0 <= j -> ((bv_swrap 32 (Z.shiftl (bv_unsigned (LW [c0;c1;c2;c3])) j)) mod M64) mod 2^32 = (v4 c0 c1 c2 c3 * 2^j) mod 2^32.
Proof. intros. Local Ltac2 Set LiaHints.tbl := fun () => "0010>45266465884.10000003S1H".
rewrite mod64_mod32, swrap32_mod32, shl_mod32, lw_mod32 by lia. reflexivity. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma hi_r j : 0 <= j -> ((Z.shiftl (bv_unsigned (LW [c0;c1;c2;c3])) j) mod M64) mod 2^32 = (v4 c0 c1 c2 c3 * 2^j) mod 2^32.
Proof. intros. Local Ltac2 Set LiaHints.tbl := fun () => "0010>45266465884.10000003S1H".
rewrite mod64_mod32, shl_mod32, lw_mod32 by lia. reflexivity. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Local Ltac merge_tac lo hi hik k :=
apply le4_lit_of_mod32; [reflexivity|];
rewrite mod64_mod32, lor_mod32, lo, hi, hik by lia; cbn [map le_val];
br b0; br b1; br b2; br b3; br c0; br c1; br c2; br c3;
first [ rewrite (lor_add' _ _ k); [ lia | lia | lia | Z.div_mod_to_equations; lia ]
| rewrite (lor_add _ _ k); [ lia | lia | lia | Z.div_mod_to_equations; lia ] ].
#[using="Type"] Lemma merge_a24 :
le4 (Z_to_bv 64 (Z.lor ((bv_swrap 32 (Z.shiftr (bv_wrap 32 (bv_unsigned (LW [b0;b1;b2;b3]))) 24)) mod M64)
((bv_swrap 32 (Z.shiftl (bv_unsigned (LW [c0;c1;c2;c3])) 8)) mod M64)))
= [b3; c0; c1; c2].
Proof. Local Ltac2 Set LiaHints.tbl := fun () => "0050>38032841174.1654005670136.1663367611819.8 63368315944.1666149329545.2300000100500600700>SS2H2SSS2H72H8".
merge_tac lo24 hi_a hi8 8%Z. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma merge_a16 :
le4 (Z_to_bv 64 (Z.lor ((bv_swrap 32 (Z.shiftr (bv_wrap 32 (bv_unsigned (LW [b0;b1;b2;b3]))) 16)) mod M64)
((bv_swrap 32 (Z.shiftl (bv_unsigned (LW [c0;c1;c2;c3])) 16)) mod M64)))
= [b2; b3; c0; c1].
Proof. Local Ltac2 Set LiaHints.tbl := fun () => "0050>34084794947.1637771375140.1665501743147.8 65502415272.1666149329545.2300000100800900:00ASS2H12H2SSS2H72H8".
merge_tac lo16 hi_a hi16 16%Z. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma merge_a8 :
le4 (Z_to_bv 64 (Z.lor ((bv_swrap 32 (Z.shiftr (bv_wrap 32 (bv_unsigned (LW [b0;b1;b2;b3]))) 8)) mod M64)
((bv_swrap 32 (Z.shiftl (bv_unsigned (LW [c0;c1;c2;c3])) 24)) mod M64)))
= [b1; b2; b3; c0].
Proof. Local Ltac2 Set LiaHints.tbl := fun () => "0050>26909018532.1641890909355.8 41891548456.1654250678808.1666149329545.2300000:00;00<00=00DS2H02H12H2SSSS2H72H8".
merge_tac lo8 hi_a hi24 24%Z. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma merge_r24 :
le4 (Z_to_bv 64 (Z.lor ((Z.shiftl (bv_unsigned (LW [c0;c1;c2;c3])) 8) mod M64)
((bv_swrap 32 (Z.shiftr (bv_wrap 32 (bv_unsigned (LW [b0;b1;b2;b3]))) 24)) mod M64)))
= [b3; c0; c1; c2].
Proof. Local Ltac2 Set LiaHints.tbl := fun () => "0060>48161110674.1648623770276.1654005670136.1663367611819.8 63368315944.1666149329545.2300000100200600700800?SFS2H2SSS2H72H8".
merge_tac lo24 hi_r hi8 8%Z. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma merge_r16 :
le4 (Z_to_bv 64 (Z.lor ((Z.shiftl (bv_unsigned (LW [c0;c1;c2;c3])) 16) mod M64)
((bv_swrap 32 (Z.shiftr (bv_wrap 32 (bv_unsigned (LW [b0;b1;b2;b3]))) 16)) mod M64)))
= [b2; b3; c0; c1].
Proof. Local Ltac2 Set LiaHints.tbl := fun () => "0050>34084794947.1637771375140.1665501743147.8 65502415272.1666149329545.2300000100800900:00ASS2H12H2SSS2H72H8".
merge_tac lo16 hi_r hi16 16%Z. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma merge_r8 :
le4 (Z_to_bv 64 (Z.lor ((Z.shiftl (bv_unsigned (LW [c0;c1;c2;c3])) 24) mod M64)
((bv_swrap 32 (Z.shiftr (bv_wrap 32 (bv_unsigned (LW [b0;b1;b2;b3]))) 8)) mod M64)))
= [b1; b2; b3; c0].
Proof. Local Ltac2 Set LiaHints.tbl := fun () => "0060>26909018532.1641890909355.8 41891548456.1653146180216.1664081504972.1666149329545.2300000:00;00<00=00>00ES2H02H12H2SSFSS2H72H8".
merge_tac lo8 hi_r hi24 24%Z. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma lwb0 : le1 (LW [b0;b1;b2;b3]) = [b0].
Proof.
apply le1_of_mod8. rewrite lw_u. br b0; br b1; br b2; br b3. unfold v4.
Z.div_mod_to_equations. Local Ltac2 Set LiaHints.tbl := fun () => "0010>15886324851.2600000<S1H2H32H82H9".
lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma lwb1 : le1 (Z_to_bv 64 (Z.shiftr (bv_unsigned (LW [b0;b1;b2;b3])) 8)) = [b1].
Proof.
apply le1_lit_of_mod8. Local Ltac2 Set LiaHints.tbl := fun () => "0040>1740073968.26 61800453814.2663367611819.8 8929201440.12 00000<00I00J00TS1H2H32H82H9S2H02H32H82H9SS2H02H12H2".
rewrite lw_u, Z.shiftr_div_pow2 by lia. br b0; br b1; br b2; br b3. unfold v4.
replace (_ / 2^8) with (bv_unsigned b1 + 256 * bv_unsigned b2 + 65536 * bv_unsigned b3 + (2^56 - 2^24) * (bv_unsigned b3 / 128))
by (Z.div_mod_to_equations; lia).
rewrite mod64_small by lia. Z.div_mod_to_equations. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma lwb2 : le1 (Z_to_bv 64 (Z.shiftr (bv_unsigned (LW [b0;b1;b2;b3])) 16)) = [b2].
Proof.
apply le1_lit_of_mod8. Local Ltac2 Set LiaHints.tbl := fun () => "0040>1740073968.26 61402555021.2665501743147.8 8929201440.12 00000?00L00M00TS1H2H02H32H82H9S2H12H32H82H9SS2H12H2".
rewrite lw_u, Z.shiftr_div_pow2 by lia. br b0; br b1; br b2; br b3. unfold v4.
replace (_ / 2^16) with (bv_unsigned b2 + 256 * bv_unsigned b3 + (2^48 - 2^16) * (bv_unsigned b3 / 128))
by (Z.div_mod_to_equations; lia).
rewrite mod64_small by lia. Z.div_mod_to_equations. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End merge.
