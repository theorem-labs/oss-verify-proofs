(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Arr Bytes.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import StrFun.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos35stdpp9bitvectorbdefinitionshf2bv01Zhfbbv_unsigned46Stdlib6ZArith6BinInt1Zl23addl23mul37Corelib4Init9Datatypesn64consl23pown63nil37Corelib4Init5Logicq12eq02N03h5LinuxProcessSemanticsfLinuxProcessSem6BvBasereh0le_bytes_to_word3h5LinuxProcessSemantics5Riscv7Preludehg14sext79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3RefaSTRW_merge~~~~~~hif2v4l23divl23subhfabv_extracthf7bv_wrapl26moduloq13andl22lel22lthf8bv_swrapl23lorl26shiftln64listn66lengthn63nat37Corelib5Lists7ListDefhu23map79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Bytes~~~~~~ig06le_val79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Mem~~~~~~ik63le4hf7Z_to_bvik63le1l26shiftr" s.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.   (* [comment removed for export] *)
Import ListNotations.
Local Open Scope Z_scope.

Local Notation LW w := (sext 64 (bv_extract 0 32 (le_bytes_to_word w))).
Local Notation M64 := 18446744073709551616%Z.

(* [comment removed for export] *)
Definition v4 : ltac2:(zQ "30!h9!jc!k1>2b0@1$1@1$0#8>2b1@1$1@1$0#8>2b2@1$1@1$0#8>2b3@1$1@1$0#8$2") := ltac2:(zQ "50!h9!jc!k4!ma!n0\2b0@1$1@1$0#8\2b1@1$1@1$0#8\2b2@1$1@1$0#8\2b3@1$1@1$0#8@2$3@2$3@2$3@2$2@1$0#8^4@2$4+hg0@2$2@1$0#8^3@2$4+hggg0@2$2@1$0#8^2@2$4+hggggg0@2$2@1$0#8^1").

Local Ltac br b := pose proof (byte_range b).

Lemma lw_u : ltac2:(zQ "h10!h9!jc!oe!p5!k4!pb!r5!ra!k1!ud!hi7!hn0!ma!hn6!n0!hnc!ho2>2b0@1$1@1$0#8>2b1@1$1@1$0#8>2b2@1$1@1$0#8>2b3@1$1@1$0#8@3$6$8@2$4@1$0#k0@3$a@1$0#i0@1$0#k0@4$h0@1$0#k0$7@1$0#i0@1$9@3$2@1$1@1$0#8^4@3$2@1$1@1$0#8^3@3$2@1$1@1$0#8^2@3$2@1$1@1$0#8^1@1$5@1$1@1$0#8@2$c@4$b^4^3^2^1@2$e@2$f@2$3+2+k0@2$3+2+i0@2$d@2$4@1$0#8^1+o0").
Proof. intros b0 b1 b2 b3. rewrite lw_unsigned4. reflexivity. Qed.

Lemma lw_wrap32 : ltac2:(zQ "d0!h9!jc!oe!pb!r5!ra!k1!ud!hi7!hn0!ho2!k4!hof>2b0@1$1@1$0#8>2b1@1$1@1$0#8>2b2@1$1@1$0#8>2b3@1$1@1$0#8@3$4$6@2$c@1$0#i0@2$b@1$0#k0@3$8@1$0#i0@1$0#k0@4$a@1$0#k0$5@1$0#i0@1$7@3$2@1$1@1$0#8^4@3$2@1$1@1$0#8^3@3$2@1$1@1$0#8^2@3$2@1$1@1$0#8^1@1$3@1$1@1$0#8@4$9^4^3^2^1").
Proof. intros b0 b1 b2 b3.
  rewrite lw_u, bv_wrap32_eq. br b0; br b1; br b2; br b3. unfold v4.
  Z.div_mod_to_equations. lia.
Qed.

Lemma lw_mod32 : ltac2:(zQ "e0!h9!jc!oe!pb!r5!ra!k1!ud!hi7!hn0!hp9!p5!ho2!k4>2b0@1$1@1$0#8>2b1@1$1@1$0#8>2b2@1$1@1$0#8>2b3@1$1@1$0#8@3$4$6@2$a@2$d@1$0#k0@3$8@1$0#i0@1$0#k0@4$c@1$0#k0$5@1$0#i0@1$7@3$2@1$1@1$0#8^4@3$2@1$1@1$0#8^3@3$2@1$1@1$0#8^2@3$2@1$1@1$0#8^1@1$3@1$1@1$0#8@2$b+2+i0@4$9^4^3^2^1").
Proof. intros b0 b1 b2 b3. rewrite <- bv_wrap32_eq. apply lw_wrap32. Qed.

Lemma swrap32_small : ltac2:(zQ "80!k1!hq2!r5!h9!hq8!hqd!p5!hr2>1x$0>0@2$1@2$4Z^1@2$5^1@2$6+2+hf@3$2$0@2$7@1$3#i0^2^2").
Proof. intros x. intros. rewrite bv_swrap32_eq. rewrite Z.mod_small; lia. Qed.
Lemma mod64_small : ltac2:(zQ "70!k1!hq2!r5!hq8!hqd!hp9!p5>1x$0>0@2$1@2$3Z^1@2$4^1@2$6+2+k0@3$2$0@2$5^2+hggggggggggggggg0^2").
Proof. intros x. intros. apply Z.mod_small. lia. Qed.

Lemma swrap32_mod32 : ltac2:(zQ "60!k1!hp9!p5!r5!h9!hr2>1x$0@3$3$0@2$1@2$5@1$4#i0^1@2$2+2+i0@2$1^1@2$2+2+i0").
Proof. intros x. rewrite bv_swrap32_eq. Z.div_mod_to_equations. lia. Qed.

Lemma mod64_mod32 : ltac2:(zQ "40!hp9!k1!p5!r5>1x$1@3$3$1@2$0@2$0^1+hggggggggggggggg0@2$2+2+i0@2$0^1@2$2+2+i0").
Proof. intros x. Z.div_mod_to_equations. lia. Qed.

Lemma lor_mod32 : ltac2:(zQ "50!k1!hp9!p5!hrd!r5>1a$0>1b$0@3$4$0@2$1@2$3^2^1@2$2+2+i0@2$3@2$1^2@2$2+2+i0@2$1^1@2$2+2+i0").
Proof. intros a b. rewrite <- !Z.land_ones by lia. apply Z.land_lor_distr_l. Qed.

Lemma shl_mod32 : ltac2:(zQ "70!p5!k1!hp9!r5!hq8!n0!hs3>1x$1>1j$1>0@2$4Z^1@3$3$1@2$2@2$6^3^2@2$0+2+i0@2$2@2$5@2$2^3@2$0+2+i0@2$0+2^2@2$0+2+i0").
Proof. intros x j. intros. rewrite Z.shiftl_mul_pow2, <- Zmult_mod_idemp_l by lia. reflexivity. Qed.

(* [comment removed for export] *)
Lemma le4_lit_of_mod32 : ltac2:(zQ "e0!h9!jc!r5!k1!hsc!hp9!ht3!htc!hv9!ijc!io0!p5!io7!k4>1z$3>2bs@1$4@1$1@1$0#8>0@3$2$7@2$6@1$1@1$0#8^1N4>0@3$2$3@2$5@2$5^3+hggggggggggggggg0@2$b+2+i0@1$9@4$8@1$1@1$0#8$3@1$d@1$0#8^2@3$2@1$4@1$1@1$0#8@1$a@2$c@1$0#k0^4^3").
Proof. intros z bs.
  intros Hl Hz. apply le4_of_mod32; [exact Hl|]. rewrite unsigned_lit_wrap. exact Hz.
Qed.
Lemma le1_lit_of_mod8 : ltac2:(zQ "c0!h9!jc!r5!k1!hp9!oe!hsc!pb!ip1!p5!io7!k4>1z$3>1b@1$1@1$0#8>0@3$2$3@2$4@2$4^2+hggggggggggggggg0@2$9+2+8@2$b@1$0#8^1@3$2@1$6@1$1@1$0#8@1$8@2$a@1$0#k0^3@3$5@1$1@1$0#8^2@1$7@1$1@1$0#8").
Proof. intros z b. intros Hz. apply le1_of_mod8. rewrite unsigned_lit_wrap. exact Hz. Qed.

Section merge.
  Variables b0 b1 b2 b3 c0 c1 c2 c3 : byte.

  (* [comment removed for export] *)
  Lemma lo24 : ltac2:(zQ "h00!h9!jc!oe!hp9!k4!pb!r5!ra!k1!ud!hi7!p5!ip8!ho2!hr2!hof@3$6$8@2$3@2$3@2$e@1$0#i0@2$c@2$f@1$0#i0@2$4@1$0#k0@3$a@1$0#i0@1$0#k0@4$d@1$0#k0$7@1$0#i0@1$9@3$2@1$1@1$0#8?2b0@3$2@1$1@1$0#8?2b1@3$2@1$1@1$0#8?2b2@3$2@1$1@1$0#8?2b3@1$5@1$1@1$0#8+h8+hggggggggggggggg0@2$b+2+i0@2$4@1$0#8?2b3").
  Proof.
    rewrite lw_wrap32, Z.shiftr_div_pow2 by lia. br b0; br b1; br b2; br b3. unfold v4.
    replace (_ / 2^24) with (bv_unsigned b3) by (Z.div_mod_to_equations; lia).
    rewrite swrap32_small, mod64_small by lia. apply Z.mod_small. lia.
  Qed.
  Lemma lo16 : ltac2:(zQ "h20!h9!jc!oe!k4!hp9!pb!r5!ra!k1!ud!hi7!ma!n0!p5!ip8!ho2!hr2!hof@3$6$8@2$4@2$4@2$h0@1$0#i0@2$e@2$h1@1$0#i0@2$3@1$0#k0@3$a@1$0#i0@1$0#k0@4$f@1$0#k0$7@1$0#i0@1$9@3$2@1$1@1$0#8?2b0@3$2@1$1@1$0#8?2b1@3$2@1$1@1$0#8?2b2@3$2@1$1@1$0#8?2b3@1$5@1$1@1$0#8+h0+hggggggggggggggg0@2$d+2+i0@2$b@2$3@1$0#8?2b2@2$c+hg0@2$3@1$0#8?2b3").
  Proof.
    rewrite lw_wrap32, Z.shiftr_div_pow2 by lia. br b0; br b1; br b2; br b3. unfold v4.
    replace (_ / 2^16) with (bv_unsigned b2 + 256 * bv_unsigned b3) by (Z.div_mod_to_equations; lia).
    rewrite swrap32_small, mod64_small by lia. apply Z.mod_small. lia.
  Qed.
  Lemma lo8 : ltac2:(zQ "h20!h9!jc!oe!k4!ma!hp9!n0!pb!r5!ra!k1!ud!hi7!p5!ip8!ho2!hr2!hof@3$8$a@2$5@2$5@2$h0@1$0#i0@2$e@2$h1@1$0#i0@2$3@1$0#k0@3$c@1$0#i0@1$0#k0@4$f@1$0#k0$9@1$0#i0@1$b@3$2@1$1@1$0#8?2b0@3$2@1$1@1$0#8?2b1@3$2@1$1@1$0#8?2b2@3$2@1$1@1$0#8?2b3@1$7@1$1@1$0#8+8+hggggggggggggggg0@2$d+2+i0@2$4@2$4@2$3@1$0#8?2b1@2$6+hg0@2$3@1$0#8?2b2@2$6+hggg0@2$3@1$0#8?2b3").
  Proof.
    rewrite lw_wrap32, Z.shiftr_div_pow2 by lia. br b0; br b1; br b2; br b3. unfold v4.
    replace (_ / 2^8) with (bv_unsigned b1 + 256 * bv_unsigned b2 + 65536 * bv_unsigned b3) by (Z.div_mod_to_equations; lia).
    rewrite swrap32_small, mod64_small by lia. apply Z.mod_small. lia.
  Qed.

  Lemma hi8 : ltac2:(zQ "90!n0!h9!k4!ma!p5!r5!k1!hn0!hp9@3$5$6@2$8@2$0@4$7?2c0?2c1?2c2?2c3@2$4+2+8@2$4+2+i0@2$3@2$3@2$0+hg0@2$2@1$1#8?2c0@2$0+hggg0@2$2@1$1#8?2c1@2$0+hggggg0@2$2@1$1#8?2c2").
  Proof. br c0; br c1; br c2; br c3. unfold v4. Z.div_mod_to_equations. lia. Qed.
  Lemma hi16 : ltac2:(zQ "90!n0!h9!p5!k4!r5!k1!hn0!ma!hp9@3$4$5@2$8@2$0@4$6?2c0?2c1?2c2?2c3@2$2+2+h0@2$2+2+i0@2$7@2$0+hggg0@2$3@1$1#8?2c0@2$0+hggggg0@2$3@1$1#8?2c1").
  Proof. br c0; br c1; br c2; br c3. unfold v4. Z.div_mod_to_equations. lia. Qed.
  Lemma hi24 : ltac2:(zQ "80!n0!p5!r5!h9!k1!hn0!hp9!k4@3$2$4@2$6@2$0@4$5?2c0?2c1?2c2?2c3@2$1+2+h8@2$1+2+i0@2$0+hggggg0@2$7@1$3#8?2c0").
  Proof. br c0; br c1; br c2; br c3. unfold v4. Z.div_mod_to_equations. lia. Qed.

  (* [comment removed for export] *)
  Lemma hi_a : ltac2:(zQ "h20!h9!jc!oe!hp9!p5!k1!pb!r5!ra!ud!hi7!hn0!hq8!n0!hs3!ho2!hr2!k4>1j$5>0@2$cZ^1@3$7$5@2$3@2$3@2$h0@1$0#i0@2$e@2$h1@1$0#k0@3$a@1$0#i0@1$0#k0@4$f@1$0#k0$8@1$0#i0@1$9@3$2@1$1@1$0#8?2c0@3$2@1$1@1$0#8?2c1@3$2@1$1@1$0#8?2c2@3$2@1$1@1$0#8?2c3@1$6@1$1@1$0#8^2+hggggggggggggggg0@2$4+2+i0@2$3@2$d@4$b?2c0?2c1?2c2?2c3@2$4+2^2@2$4+2+i0").
  Proof. intros j. intros. rewrite mod64_mod32, swrap32_mod32, shl_mod32, lw_mod32 by lia. reflexivity. Qed.
  Lemma hi_r : ltac2:(zQ "h10!h9!jc!oe!hp9!p5!k1!pb!r5!ra!ud!hi7!hn0!hq8!n0!hs3!ho2!k4>1j$5>0@2$cZ^1@3$7$5@2$3@2$3@2$e@2$h0@1$0#k0@3$a@1$0#i0@1$0#k0@4$f@1$0#k0$8@1$0#i0@1$9@3$2@1$1@1$0#8?2c0@3$2@1$1@1$0#8?2c1@3$2@1$1@1$0#8?2c2@3$2@1$1@1$0#8?2c3@1$6@1$1@1$0#8^2+hggggggggggggggg0@2$4+2+i0@2$3@2$d@4$b?2c0?2c1?2c2?2c3@2$4+2^2@2$4+2+i0").
  Proof. intros j. intros. rewrite mod64_mod32, shl_mod32, lw_mod32 by lia. reflexivity. Qed.

  Local Ltac merge_tac lo hi hik k :=
    apply le4_lit_of_mod32; [reflexivity|];
    rewrite mod64_mod32, lor_mod32, lo, hi, hik by lia; cbn [map le_val];
    br b0; br b1; br b2; br b3; br c0; br c1; br c2; br c3;
    first [ rewrite (lor_add' _ _ k); [ lia | lia | lia | Z.div_mod_to_equations; lia ]
          | rewrite (lor_add _ _ k); [ lia | lia | lia | Z.div_mod_to_equations; lia ] ].

  (* [comment removed for export] *)
  Lemma merge_a24 : ltac2:(zQ "h30!h9!jc!oe!pb!ra!ud!hi7!hp9!ho2!hr2!k4!hsc!r5!io0!hrd!hs3!ip8!io7!hof@3$c@1$b@1$1@1$0#8@1$d@2$h1@1$0#k0@2$e@2$7@2$9@1$0#i0@2$h0@2$h2@1$0#i0@2$a@1$0#k0@3$6@1$0#i0@1$0#k0@4$8@1$0#k0$4@1$0#i0@1$5@3$2@1$1@1$0#8?2b0@3$2@1$1@1$0#8?2b1@3$2@1$1@1$0#8?2b2@3$2@1$1@1$0#8?2b3@1$3@1$1@1$0#8+h8+hggggggggggggggg0@2$7@2$9@1$0#i0@2$f@2$a@1$0#k0@3$6@1$0#i0@1$0#k0@4$8@1$0#k0$4@1$0#i0@1$5@3$2@1$1@1$0#8?2c0@3$2@1$1@1$0#8?2c1@3$2@1$1@1$0#8?2c2@3$2@1$1@1$0#8?2c3@1$3@1$1@1$0#8+8+hggggggggggggggg0@3$2@1$1@1$0#8?2b3@3$2@1$1@1$0#8?2c0@3$2@1$1@1$0#8?2c1@3$2@1$1@1$0#8?2c2@1$3@1$1@1$0#8").
  Proof. merge_tac lo24 hi_a hi8 8%Z. Qed.
  Lemma merge_a16 : ltac2:(zQ "h30!h9!jc!oe!pb!ra!ud!hi7!hp9!ho2!hr2!k4!hsc!r5!io0!hrd!hs3!ip8!io7!hof@3$c@1$b@1$1@1$0#8@1$d@2$h1@1$0#k0@2$e@2$7@2$9@1$0#i0@2$h0@2$h2@1$0#i0@2$a@1$0#k0@3$6@1$0#i0@1$0#k0@4$8@1$0#k0$4@1$0#i0@1$5@3$2@1$1@1$0#8?2b0@3$2@1$1@1$0#8?2b1@3$2@1$1@1$0#8?2b2@3$2@1$1@1$0#8?2b3@1$3@1$1@1$0#8+h0+hggggggggggggggg0@2$7@2$9@1$0#i0@2$f@2$a@1$0#k0@3$6@1$0#i0@1$0#k0@4$8@1$0#k0$4@1$0#i0@1$5@3$2@1$1@1$0#8?2c0@3$2@1$1@1$0#8?2c1@3$2@1$1@1$0#8?2c2@3$2@1$1@1$0#8?2c3@1$3@1$1@1$0#8+h0+hggggggggggggggg0@3$2@1$1@1$0#8?2b2@3$2@1$1@1$0#8?2b3@3$2@1$1@1$0#8?2c0@3$2@1$1@1$0#8?2c1@1$3@1$1@1$0#8").
  Proof. merge_tac lo16 hi_a hi16 16%Z. Qed.
  Lemma merge_a8 : ltac2:(zQ "h30!h9!jc!oe!pb!ra!ud!hi7!hp9!ho2!hr2!k4!hsc!r5!io0!hrd!hs3!ip8!io7!hof@3$c@1$b@1$1@1$0#8@1$d@2$h1@1$0#k0@2$e@2$7@2$9@1$0#i0@2$h0@2$h2@1$0#i0@2$a@1$0#k0@3$6@1$0#i0@1$0#k0@4$8@1$0#k0$4@1$0#i0@1$5@3$2@1$1@1$0#8?2b0@3$2@1$1@1$0#8?2b1@3$2@1$1@1$0#8?2b2@3$2@1$1@1$0#8?2b3@1$3@1$1@1$0#8+8+hggggggggggggggg0@2$7@2$9@1$0#i0@2$f@2$a@1$0#k0@3$6@1$0#i0@1$0#k0@4$8@1$0#k0$4@1$0#i0@1$5@3$2@1$1@1$0#8?2c0@3$2@1$1@1$0#8?2c1@3$2@1$1@1$0#8?2c2@3$2@1$1@1$0#8?2c3@1$3@1$1@1$0#8+h8+hggggggggggggggg0@3$2@1$1@1$0#8?2b1@3$2@1$1@1$0#8?2b2@3$2@1$1@1$0#8?2b3@3$2@1$1@1$0#8?2c0@1$3@1$1@1$0#8").
  Proof. merge_tac lo8 hi_a hi24 24%Z. Qed.

  (* [comment removed for export] *)
  Lemma merge_r24 : ltac2:(zQ "h30!h9!jc!oe!pb!ra!ud!hi7!hp9!ho2!k4!hsc!r5!io0!hrd!hs3!ip8!io7!hr2!hof@3$b@1$a@1$1@1$0#8@1$c@2$h0@1$0#k0@2$d@2$7@2$e@2$9@1$0#k0@3$6@1$0#i0@1$0#k0@4$8@1$0#k0$4@1$0#i0@1$5@3$2@1$1@1$0#8?2c0@3$2@1$1@1$0#8?2c1@3$2@1$1@1$0#8?2c2@3$2@1$1@1$0#8?2c3@1$3@1$1@1$0#8+8+hggggggggggggggg0@2$7@2$h1@1$0#i0@2$f@2$h2@1$0#i0@2$9@1$0#k0@3$6@1$0#i0@1$0#k0@4$8@1$0#k0$4@1$0#i0@1$5@3$2@1$1@1$0#8?2b0@3$2@1$1@1$0#8?2b1@3$2@1$1@1$0#8?2b2@3$2@1$1@1$0#8?2b3@1$3@1$1@1$0#8+h8+hggggggggggggggg0@3$2@1$1@1$0#8?2b3@3$2@1$1@1$0#8?2c0@3$2@1$1@1$0#8?2c1@3$2@1$1@1$0#8?2c2@1$3@1$1@1$0#8").
  Proof. merge_tac lo24 hi_r hi8 8%Z. Qed.
  Lemma merge_r16 : ltac2:(zQ "h30!h9!jc!oe!pb!ra!ud!hi7!hp9!ho2!k4!hsc!r5!io0!hrd!hs3!ip8!io7!hr2!hof@3$b@1$a@1$1@1$0#8@1$c@2$h0@1$0#k0@2$d@2$7@2$e@2$9@1$0#k0@3$6@1$0#i0@1$0#k0@4$8@1$0#k0$4@1$0#i0@1$5@3$2@1$1@1$0#8?2c0@3$2@1$1@1$0#8?2c1@3$2@1$1@1$0#8?2c2@3$2@1$1@1$0#8?2c3@1$3@1$1@1$0#8+h0+hggggggggggggggg0@2$7@2$h1@1$0#i0@2$f@2$h2@1$0#i0@2$9@1$0#k0@3$6@1$0#i0@1$0#k0@4$8@1$0#k0$4@1$0#i0@1$5@3$2@1$1@1$0#8?2b0@3$2@1$1@1$0#8?2b1@3$2@1$1@1$0#8?2b2@3$2@1$1@1$0#8?2b3@1$3@1$1@1$0#8+h0+hggggggggggggggg0@3$2@1$1@1$0#8?2b2@3$2@1$1@1$0#8?2b3@3$2@1$1@1$0#8?2c0@3$2@1$1@1$0#8?2c1@1$3@1$1@1$0#8").
  Proof. merge_tac lo16 hi_r hi16 16%Z. Qed.
  Lemma merge_r8 : ltac2:(zQ "h30!h9!jc!oe!pb!ra!ud!hi7!hp9!ho2!k4!hsc!r5!io0!hrd!hs3!ip8!io7!hr2!hof@3$b@1$a@1$1@1$0#8@1$c@2$h0@1$0#k0@2$d@2$7@2$e@2$9@1$0#k0@3$6@1$0#i0@1$0#k0@4$8@1$0#k0$4@1$0#i0@1$5@3$2@1$1@1$0#8?2c0@3$2@1$1@1$0#8?2c1@3$2@1$1@1$0#8?2c2@3$2@1$1@1$0#8?2c3@1$3@1$1@1$0#8+h8+hggggggggggggggg0@2$7@2$h1@1$0#i0@2$f@2$h2@1$0#i0@2$9@1$0#k0@3$6@1$0#i0@1$0#k0@4$8@1$0#k0$4@1$0#i0@1$5@3$2@1$1@1$0#8?2b0@3$2@1$1@1$0#8?2b1@3$2@1$1@1$0#8?2b2@3$2@1$1@1$0#8?2b3@1$3@1$1@1$0#8+8+hggggggggggggggg0@3$2@1$1@1$0#8?2b1@3$2@1$1@1$0#8?2b2@3$2@1$1@1$0#8?2b3@3$2@1$1@1$0#8?2c0@1$3@1$1@1$0#8").
  Proof. merge_tac lo8 hi_r hi24 24%Z. Qed.

  (* [comment removed for export] *)
  Lemma lwb0 : ltac2:(zQ "b0!h9!jc!oe!pb!hsc!r5!ra!ud!hi7!ip1!ho2@3$5@1$4@1$1@1$0#8@1$9@3$8@1$0#i0@1$0#k0@4$a@1$0#k0$6@1$0#i0@1$7@3$2@1$1@1$0#8?2b0@3$2@1$1@1$0#8?2b1@3$2@1$1@1$0#8?2b2@3$2@1$1@1$0#8?2b3@1$3@1$1@1$0#8@3$2@1$1@1$0#8?2b0@1$3@1$1@1$0#8").
  Proof.
    apply le1_of_mod8. rewrite lw_u. br b0; br b1; br b2; br b3. unfold v4.
    Z.div_mod_to_equations. lia.
  Qed.
  Lemma lwb1 : ltac2:(zQ "e0!h9!jc!oe!pb!hsc!r5!ra!ud!hi7!ip1!ip8!io7!ho2!k4@3$5@1$4@1$1@1$0#8@1$9@2$b@1$0#k0@2$a@2$d@1$0#k0@3$8@1$0#i0@1$0#k0@4$c@1$0#k0$6@1$0#i0@1$7@3$2@1$1@1$0#8?2b0@3$2@1$1@1$0#8?2b1@3$2@1$1@1$0#8?2b2@3$2@1$1@1$0#8?2b3@1$3@1$1@1$0#8+8@3$2@1$1@1$0#8?2b1@1$3@1$1@1$0#8").
  Proof.
    apply le1_lit_of_mod8. rewrite lw_u, Z.shiftr_div_pow2 by lia. br b0; br b1; br b2; br b3. unfold v4.
    replace (_ / 2^8) with (bv_unsigned b1 + 256 * bv_unsigned b2 + 65536 * bv_unsigned b3 + (2^56 - 2^24) * (bv_unsigned b3 / 128))
      by (Z.div_mod_to_equations; lia).
    rewrite mod64_small by lia. Z.div_mod_to_equations. lia.
  Qed.
  Lemma lwb2 : ltac2:(zQ "e0!h9!jc!oe!pb!hsc!r5!ra!ud!hi7!ip1!ip8!io7!ho2!k4@3$5@1$4@1$1@1$0#8@1$9@2$b@1$0#k0@2$a@2$d@1$0#k0@3$8@1$0#i0@1$0#k0@4$c@1$0#k0$6@1$0#i0@1$7@3$2@1$1@1$0#8?2b0@3$2@1$1@1$0#8?2b1@3$2@1$1@1$0#8?2b2@3$2@1$1@1$0#8?2b3@1$3@1$1@1$0#8+h0@3$2@1$1@1$0#8?2b2@1$3@1$1@1$0#8").
  Proof.
    apply le1_lit_of_mod8. rewrite lw_u, Z.shiftr_div_pow2 by lia. br b0; br b1; br b2; br b3. unfold v4.
    replace (_ / 2^16) with (bv_unsigned b2 + 256 * bv_unsigned b3 + (2^48 - 2^16) * (bv_unsigned b3 / 128))
      by (Z.div_mod_to_equations; lia).
    rewrite mod64_small by lia. Z.div_mod_to_equations. lia.
  Qed.
End merge.
(* [comment removed for export] *)
