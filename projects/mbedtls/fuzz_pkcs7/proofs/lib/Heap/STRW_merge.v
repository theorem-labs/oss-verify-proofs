(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Tac Arr Bytes.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import StrFun.
Import ListNotations.
Local Open Scope Z_scope.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_STRW_merge () : Init.string Init.list := ["Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.nat"; "Corelib.Init.Datatypes.length"; "stdpp.bitvector.definitions.bv"; "Corelib.Numbers.BinNums.Z"; "Stdlib.ZArith.BinInt.Z.modulo"; "Stdlib.ZArith.BinInt.Z.pow"; "OSSVerify.KrLib.Lib.Bytes.le_val"; "Corelib.Lists.ListDef.map"; "stdpp.bitvector.definitions.bv_unsigned"; "Corelib.Init.Datatypes.list"; "OSSVerify.KrLib.Lib.Mem.le4"; "stdpp.bitvector.definitions.Z_to_bv"; "stdpp.bitvector.definitions.bv_swrap"; "Stdlib.ZArith.BinInt.Z.shiftr"; "stdpp.bitvector.definitions.bv_wrap"; "LinuxProcessSemantics.Riscv.Prelude.sext"; "stdpp.bitvector.definitions.bv_extract"; "LinuxProcessSemantics.LinuxProcessSem.BvBase.le_bytes_to_word"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.nil"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.mul"; "v4"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.shiftl"; "Stdlib.ZArith.BinInt.Z.lor"].


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


Lemma swrap32_mod32 x : (bv_swrap 32 x) mod 2^32 = x mod 2^32.
Proof. rewrite bv_swrap32_eq. Z.div_mod_to_equations. lia. Qed.

Lemma mod64_mod32 x : (x mod M64) mod 2^32 = x mod 2^32.
Proof. Z.div_mod_to_equations. lia. Qed.

Lemma lor_mod32 a b : (Z.lor a b) mod 2^32 = Z.lor (a mod 2^32) (b mod 2^32).
Proof. rewrite <- !Z.land_ones by lia. apply Z.land_lor_distr_l. Qed.

Lemma shl_mod32 x j : 0 <= j -> (Z.shiftl x j) mod 2^32 = ((x mod 2^32) * 2^j) mod 2^32.
Proof. intros. rewrite Z.shiftl_mul_pow2, <- Zmult_mod_idemp_l by lia. reflexivity. Qed.

(* [comment removed for export] *)
Lemma le4_lit_of_mod32 z (bs : list byte) : ltac2:(CDefT.buildp (gd_tbl_STRW_merge ()) "P,(0.$1.(2.(3.&8.)O1.)#4.)P,(0.$4.(5.(5.O2.+10000000000000000.)(6.+2.+20.))(7.(8.(3.&8.)$4.(9.&8.)O1.)))(0.(:.(3.&8.))(;.(<.&40.O2.))O1.)")
(* [comment removed for export] *).
Proof.
  intros Hl Hz. apply le4_of_mod32; [exact Hl|]. rewrite unsigned_lit_wrap. exact Hz.
Qed.
Lemma le1_lit_of_mod8 z (b : byte) :
  (z mod M64) mod 2^8 = bv_unsigned b -> le1 (Z_to_bv 64 z) = [b].
Proof. intros Hz. apply le1_of_mod8. rewrite unsigned_lit_wrap. exact Hz. Qed.

Section merge.
  Variables b0 b1 b2 b3 c0 c1 c2 c3 : byte.

  (* [comment removed for export] *)
  #[using="Type"] Lemma lo24 : ltac2:(CDefT.buildp (gd_tbl_STRW_merge ()) "(0.$4.(5.(5.(=.&20.(>.(?.&20.(9.&40.(10.&20.&40.(11.&40.~&20.(12.(13.(3.&8.)Vb0,(13.(3.&8.)Vb1,(13.(3.&8.)Vb2,(13.(3.&8.)Vb3,(14.(3.&8.)))))))))))+18.))+10000000000000000.)(6.+2.+20.))(9.&8.Vb3,))")
(* [comment removed for export] *).
  Proof.
    rewrite lw_wrap32, Z.shiftr_div_pow2 by lia. br b0; br b1; br b2; br b3. unfold v4.
    replace (_ / 2^24) with (bv_unsigned b3) by (Z.div_mod_to_equations; lia).
    rewrite swrap32_small, mod64_small by lia. apply Z.mod_small. lia.
  Qed.
  #[using="Type"] Lemma lo16 : ltac2:(CDefT.buildp (gd_tbl_STRW_merge ()) "(0.$4.(5.(5.(=.&20.(>.(?.&20.(9.&40.(10.&20.&40.(11.&40.~&20.(12.(13.(3.&8.)Vb0,(13.(3.&8.)Vb1,(13.(3.&8.)Vb2,(13.(3.&8.)Vb3,(14.(3.&8.)))))))))))+10.))+10000000000000000.)(6.+2.+20.))(15.(9.&8.Vb2,)(16.+100.(9.&8.Vb3,))))")
(* [comment removed for export] *).
  Proof.
    rewrite lw_wrap32, Z.shiftr_div_pow2 by lia. br b0; br b1; br b2; br b3. unfold v4.
    replace (_ / 2^16) with (bv_unsigned b2 + 256 * bv_unsigned b3) by (Z.div_mod_to_equations; lia).
    rewrite swrap32_small, mod64_small by lia. apply Z.mod_small. lia.
  Qed.
  #[using="Type"] Lemma lo8 : ltac2:(CDefT.buildp (gd_tbl_STRW_merge ()) "(0.$4.(5.(5.(=.&20.(>.(?.&20.(9.&40.(10.&20.&40.(11.&40.~&20.(12.(13.(3.&8.)Vb0,(13.(3.&8.)Vb1,(13.(3.&8.)Vb2,(13.(3.&8.)Vb3,(14.(3.&8.)))))))))))+8.))+10000000000000000.)(6.+2.+20.))(15.(15.(9.&8.Vb1,)(16.+100.(9.&8.Vb2,)))(16.+10000.(9.&8.Vb3,))))")
(* [comment removed for export] *).
  Proof.
    rewrite lw_wrap32, Z.shiftr_div_pow2 by lia. br b0; br b1; br b2; br b3. unfold v4.
    replace (_ / 2^8) with (bv_unsigned b1 + 256 * bv_unsigned b2 + 65536 * bv_unsigned b3) by (Z.div_mod_to_equations; lia).
    rewrite swrap32_small, mod64_small by lia. apply Z.mod_small. lia.
  Qed.

  #[using="Type"] Lemma hi8 : ltac2:(CDefT.buildp (gd_tbl_STRW_merge ()) "(0.$4.(5.(16.(17.Vc0,Vc1,Vc2,Vc3,)(6.+2.+8.))(6.+2.+20.))(15.(15.(16.+100.(9.&8.Vc0,))(16.+10000.(9.&8.Vc1,)))(16.+1000000.(9.&8.Vc2,))))")
(* [comment removed for export] *).
  Proof. br c0; br c1; br c2; br c3. unfold v4. Z.div_mod_to_equations. lia. Qed.
  #[using="Type"] Lemma hi16 : (v4 c0 c1 c2 c3 * 2^16) mod 2^32 = 65536 * bv_unsigned c0 + 16777216 * bv_unsigned c1.
  Proof. br c0; br c1; br c2; br c3. unfold v4. Z.div_mod_to_equations. lia. Qed.
  #[using="Type"] Lemma hi24 : (v4 c0 c1 c2 c3 * 2^24) mod 2^32 = 16777216 * bv_unsigned c0.
  Proof. br c0; br c1; br c2; br c3. unfold v4. Z.div_mod_to_equations. lia. Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma hi_a j : ltac2:(CDefT.buildp (gd_tbl_STRW_merge ()) "P,(18.=O1.)(0.$4.(5.(5.(=.&20.(19.(9.&40.(10.&20.&40.(11.&40.~&20.(12.(13.(3.&8.)Vc0,(13.(3.&8.)Vc1,(13.(3.&8.)Vc2,(13.(3.&8.)Vc3,(14.(3.&8.))))))))))O1.))+10000000000000000.)(6.+2.+20.))(5.(16.(17.Vc0,Vc1,Vc2,Vc3,)(6.+2.O1.))(6.+2.+20.)))")
(* [comment removed for export] *).
  Proof. intros. rewrite mod64_mod32, swrap32_mod32, shl_mod32, lw_mod32 by lia. reflexivity. Qed.
  #[using="Type"] Lemma hi_r j : ltac2:(CDefT.buildp (gd_tbl_STRW_merge ()) "P,(18.=O1.)(0.$4.(5.(5.(19.(9.&40.(10.&20.&40.(11.&40.~&20.(12.(13.(3.&8.)Vc0,(13.(3.&8.)Vc1,(13.(3.&8.)Vc2,(13.(3.&8.)Vc3,(14.(3.&8.))))))))))O1.)+10000000000000000.)(6.+2.+20.))(5.(16.(17.Vc0,Vc1,Vc2,Vc3,)(6.+2.O1.))(6.+2.+20.)))")
(* [comment removed for export] *).
  Proof. intros. rewrite mod64_mod32, shl_mod32, lw_mod32 by lia. reflexivity. Qed.

  Local Ltac merge_tac lo hi hik k :=
    apply le4_lit_of_mod32; [reflexivity|];
    rewrite mod64_mod32, lor_mod32, lo, hi, hik by lia; cbn [map le_val];
    br b0; br b1; br b2; br b3; br c0; br c1; br c2; br c3;
    first [ rewrite (lor_add' _ _ k); [ lia | lia | lia | Z.div_mod_to_equations; lia ]
          | rewrite (lor_add _ _ k); [ lia | lia | lia | Z.div_mod_to_equations; lia ] ].

  (* [comment removed for export] *)
  #[using="Type"] Lemma merge_a24 : ltac2:(CDefT.buildp (gd_tbl_STRW_merge ()) "(0.(:.(3.&8.))(;.(<.&40.(1:.(5.(=.&20.(>.(?.&20.(9.&40.(10.&20.&40.(11.&40.~&20.(12.(13.(3.&8.)Vb0,(13.(3.&8.)Vb1,(13.(3.&8.)Vb2,(13.(3.&8.)Vb3,(14.(3.&8.)))))))))))+18.))+10000000000000000.)(5.(=.&20.(19.(9.&40.(10.&20.&40.(11.&40.~&20.(12.(13.(3.&8.)Vc0,(13.(3.&8.)Vc1,(13.(3.&8.)Vc2,(13.(3.&8.)Vc3,(14.(3.&8.))))))))))+8.))+10000000000000000.))))(13.(3.&8.)Vb3,(13.(3.&8.)Vc0,(13.(3.&8.)Vc1,(13.(3.&8.)Vc2,(14.(3.&8.)))))))")
(* [comment removed for export] *).
  Proof. merge_tac lo24 hi_a hi8 8%Z. Qed.
  #[using="Type"] Lemma merge_a16 : ltac2:(CDefT.buildp (gd_tbl_STRW_merge ()) "(0.(:.(3.&8.))(;.(<.&40.(1:.(5.(=.&20.(>.(?.&20.(9.&40.(10.&20.&40.(11.&40.~&20.(12.(13.(3.&8.)Vb0,(13.(3.&8.)Vb1,(13.(3.&8.)Vb2,(13.(3.&8.)Vb3,(14.(3.&8.)))))))))))+10.))+10000000000000000.)(5.(=.&20.(19.(9.&40.(10.&20.&40.(11.&40.~&20.(12.(13.(3.&8.)Vc0,(13.(3.&8.)Vc1,(13.(3.&8.)Vc2,(13.(3.&8.)Vc3,(14.(3.&8.))))))))))+10.))+10000000000000000.))))(13.(3.&8.)Vb2,(13.(3.&8.)Vb3,(13.(3.&8.)Vc0,(13.(3.&8.)Vc1,(14.(3.&8.)))))))")
(* [comment removed for export] *).
  Proof. merge_tac lo16 hi_a hi16 16%Z. Qed.
  #[using="Type"] Lemma merge_a8 : ltac2:(CDefT.buildp (gd_tbl_STRW_merge ()) "(0.(:.(3.&8.))(;.(<.&40.(1:.(5.(=.&20.(>.(?.&20.(9.&40.(10.&20.&40.(11.&40.~&20.(12.(13.(3.&8.)Vb0,(13.(3.&8.)Vb1,(13.(3.&8.)Vb2,(13.(3.&8.)Vb3,(14.(3.&8.)))))))))))+8.))+10000000000000000.)(5.(=.&20.(19.(9.&40.(10.&20.&40.(11.&40.~&20.(12.(13.(3.&8.)Vc0,(13.(3.&8.)Vc1,(13.(3.&8.)Vc2,(13.(3.&8.)Vc3,(14.(3.&8.))))))))))+18.))+10000000000000000.))))(13.(3.&8.)Vb1,(13.(3.&8.)Vb2,(13.(3.&8.)Vb3,(13.(3.&8.)Vc0,(14.(3.&8.)))))))")
(* [comment removed for export] *).
  Proof. merge_tac lo8 hi_a hi24 24%Z. Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma merge_r24 : ltac2:(CDefT.buildp (gd_tbl_STRW_merge ()) "(0.(:.(3.&8.))(;.(<.&40.(1:.(5.(19.(9.&40.(10.&20.&40.(11.&40.~&20.(12.(13.(3.&8.)Vc0,(13.(3.&8.)Vc1,(13.(3.&8.)Vc2,(13.(3.&8.)Vc3,(14.(3.&8.))))))))))+8.)+10000000000000000.)(5.(=.&20.(>.(?.&20.(9.&40.(10.&20.&40.(11.&40.~&20.(12.(13.(3.&8.)Vb0,(13.(3.&8.)Vb1,(13.(3.&8.)Vb2,(13.(3.&8.)Vb3,(14.(3.&8.)))))))))))+18.))+10000000000000000.))))(13.(3.&8.)Vb3,(13.(3.&8.)Vc0,(13.(3.&8.)Vc1,(13.(3.&8.)Vc2,(14.(3.&8.)))))))")
(* [comment removed for export] *).
  Proof. merge_tac lo24 hi_r hi8 8%Z. Qed.
  #[using="Type"] Lemma merge_r16 : ltac2:(CDefT.buildp (gd_tbl_STRW_merge ()) "(0.(:.(3.&8.))(;.(<.&40.(1:.(5.(19.(9.&40.(10.&20.&40.(11.&40.~&20.(12.(13.(3.&8.)Vc0,(13.(3.&8.)Vc1,(13.(3.&8.)Vc2,(13.(3.&8.)Vc3,(14.(3.&8.))))))))))+10.)+10000000000000000.)(5.(=.&20.(>.(?.&20.(9.&40.(10.&20.&40.(11.&40.~&20.(12.(13.(3.&8.)Vb0,(13.(3.&8.)Vb1,(13.(3.&8.)Vb2,(13.(3.&8.)Vb3,(14.(3.&8.)))))))))))+10.))+10000000000000000.))))(13.(3.&8.)Vb2,(13.(3.&8.)Vb3,(13.(3.&8.)Vc0,(13.(3.&8.)Vc1,(14.(3.&8.)))))))")
(* [comment removed for export] *).
  Proof. merge_tac lo16 hi_r hi16 16%Z. Qed.
  #[using="Type"] Lemma merge_r8 : ltac2:(CDefT.buildp (gd_tbl_STRW_merge ()) "(0.(:.(3.&8.))(;.(<.&40.(1:.(5.(19.(9.&40.(10.&20.&40.(11.&40.~&20.(12.(13.(3.&8.)Vc0,(13.(3.&8.)Vc1,(13.(3.&8.)Vc2,(13.(3.&8.)Vc3,(14.(3.&8.))))))))))+18.)+10000000000000000.)(5.(=.&20.(>.(?.&20.(9.&40.(10.&20.&40.(11.&40.~&20.(12.(13.(3.&8.)Vb0,(13.(3.&8.)Vb1,(13.(3.&8.)Vb2,(13.(3.&8.)Vb3,(14.(3.&8.)))))))))))+8.))+10000000000000000.))))(13.(3.&8.)Vb1,(13.(3.&8.)Vb2,(13.(3.&8.)Vb3,(13.(3.&8.)Vc0,(14.(3.&8.)))))))")
(* [comment removed for export] *).
  Proof. merge_tac lo8 hi_r hi24 24%Z. Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma lwb0 : le1 (LW [b0;b1;b2;b3]) = [b0].
  Proof.
    apply le1_of_mod8. rewrite lw_u. br b0; br b1; br b2; br b3. unfold v4.
    Z.div_mod_to_equations. lia.
  Qed.
  #[using="Type"] Lemma lwb1 : le1 (Z_to_bv 64 (Z.shiftr (bv_unsigned (LW [b0;b1;b2;b3])) 8)) = [b1].
  Proof.
    apply le1_lit_of_mod8. rewrite lw_u, Z.shiftr_div_pow2 by lia. br b0; br b1; br b2; br b3. unfold v4.
    replace (_ / 2^8) with (bv_unsigned b1 + 256 * bv_unsigned b2 + 65536 * bv_unsigned b3 + (2^56 - 2^24) * (bv_unsigned b3 / 128))
      by (Z.div_mod_to_equations; lia).
    rewrite mod64_small by lia. Z.div_mod_to_equations. lia.
  Qed.
  #[using="Type"] Lemma lwb2 : le1 (Z_to_bv 64 (Z.shiftr (bv_unsigned (LW [b0;b1;b2;b3])) 16)) = [b2].
  Proof.
    apply le1_lit_of_mod8. rewrite lw_u, Z.shiftr_div_pow2 by lia. br b0; br b1; br b2; br b3. unfold v4.
    replace (_ / 2^16) with (bv_unsigned b2 + 256 * bv_unsigned b3 + (2^48 - 2^16) * (bv_unsigned b3 / 128))
      by (Z.div_mod_to_equations; lia).
    rewrite mod64_small by lia. Z.div_mod_to_equations. lia.
  Qed.
End merge.
