(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_halts_any_exit.Lib Require Import Arr Bytes ZBridge.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_halts_any_exit.cks Require Import CkTables CkModel CkMathAdler CkWalk.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_halts_any_exit.CkU Require Import CkAImg CkATables CkAShadow CkAIface CkAKit AdlAGlue AdlA_zs AdlA_zt.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_halts_any_exit.LibA Require Import Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_halts_any_exit.LibA Require Import StepF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac acc_hint ::= acc_hint_shrng.

Definition adl_FRAMEN (sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (v40 v48 : word) (m1 : amem) : Prop := exists j0,
  rw_cells asegs m1 (bv_unsigned sp + -160)
    [CB 8 j0; C8 (Z_to_bv 64 65521); C8 (Z_to_bv 64 18446744073709546064); C8 (Z_to_bv 64 5552); C8 (Z_to_bv 64 0x10338); C8 v40; C8 v48;
     C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Lemma adl_FRAMEN_T : forall sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v40 v48 m1,
  adl_FRAMEN sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v40 v48 m1 -> adl_FRAMET sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m1.
Proof.
  intros sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v40 v48 m1 (j0 & F).
  exists (cells_bytes [CB 8 j0; C8 (Z_to_bv 64 65521); C8 (Z_to_bv 64 18446744073709546064); C8 (Z_to_bv 64 5552)]).
  exists (cells_bytes [C8 v40; C8 v48]).
  pose proof (rw_cells_merge asegs m1 _ [] [CB 8 j0; C8 (Z_to_bv 64 65521); C8 (Z_to_bv 64 18446744073709546064); C8 (Z_to_bv 64 5552)] _ F) as F1.
  cbn [app] in F1.
  exact (rw_cells_merge asegs m1 _ [CB _ _; C8 (Z_to_bv 64 0x10338)] [C8 v40; C8 v48] _ F1).
Qed.

Definition adl_FRAMEN0 (sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (m1 : amem) : Prop := exists j0 j40,
  rw_cells asegs m1 (bv_unsigned sp + -160)
    [CB 8 j0; C8 (Z_to_bv 64 65521); C8 (Z_to_bv 64 18446744073709546064); C8 (Z_to_bv 64 5552); C8 (Z_to_bv 64 0x10338); CB 16 j40;
     C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Lemma adl_FRAMEN_0 : forall sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v40 v48 m1,
  adl_FRAMEN sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v40 v48 m1 -> adl_FRAMEN0 sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m1.
Proof.
  intros sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v40 v48 m1 (j0 & F).
  exists j0, (cells_bytes [C8 v40; C8 v48]).
  exact (rw_cells_merge asegs m1 _ [CB 8 j0; C8 (Z_to_bv 64 65521); C8 (Z_to_bv 64 18446744073709546064); C8 (Z_to_bv 64 5552); C8 (Z_to_bv 64 0x10338)]
                        [C8 v40; C8 v48] _ F).
Qed.

Lemma adl_INVN_T : forall sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v40 v48 m lo A bs m1,
  adl_INVG (adl_FRAMEN sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v40 v48) sp m lo A bs m1 ->
  adl_INVG (adl_FRAMET sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) sp m lo A bs m1.
Proof. intros until m1. intros (F & R). split; [eapply adl_FRAMEN_T; exact F| exact R]. Qed.

Lemma adl_INVN_0 : forall sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v40 v48 m lo A bs m1,
  adl_INVG (adl_FRAMEN sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v40 v48) sp m lo A bs m1 ->
  adl_INVG (adl_FRAMEN0 sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) sp m lo A bs m1.
Proof. intros until m1. intros (F & R). split; [eapply adl_FRAMEN_0; exact F| exact R]. Qed.

Section P.
  Variables (RNG : footprint)
            (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
            (FR : bvmap 5 word) (fc : bv 32) (m : amem) (lo : Z) (adler A n : Z) (bs : list Z).
  Hypothesis LOS : lo <= bv_unsigned sp - 160.
  Hypothesis KLO : KHIGH <= lo.
  Hypothesis AR : 0 <= adler < 2^64.
  Hypothesis A1R : 1 <= A.
  Hypothesis NL : Z.of_nat (length bs) = n.
  Hypothesis ALO : A + n <= lo.
  Hypothesis BF : Forall (fun b => 0 <= b < 256) bs.
  Hypothesis UNP : unpoisoned m A (A + n).
  Hypothesis RB : rng RNG A n.
  Hypothesis RS : shrng RNG A (A + n).
  Hypothesis RI : rng_aimg RNG.
  Hypothesis RSTK : rng RNG lo (bv_unsigned sp - lo).

  Notation SP := (bv_unsigned sp).
  Notation W := [(SP - 160, SP)].
  Notation POST res := (ck_postA 160 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc res lo m).
  Notation FRAMET := (adl_FRAMET sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11).
  Notation FRAMEN := (adl_FRAMEN sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11).
  Notation INVT := (adl_INVG FRAMET sp m lo A bs).
  Notation INVN v40 v48 := (adl_INVG (FRAMEN v40 v48) sp m lo A bs).
  Notation INVN0 := (adl_INVG (adl_FRAMEN0 sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) sp m lo A bs).
  Notation W_above := (adl_W_above sp).
  Notation CTX L := (L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m lo adler A n bs
                       LOS KLO AR A1R NL ALO BF UNP RB RS RI RSTK).

  Local Ltac ckK m1 MU BY a ib U JOIN :=
    let b := fresh "b" in let RD := fresh "RD" in let CK := fresh "CK" in let SR := fresh "SR" in let RDB := fresh "RDB" in
    destruct (unpoisoned_check_mu W (SP - 160) m m1 A (A + n) a 1 UNP MU W_above
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(Z.div_mod_to_equations; lia)) as (b & RD & CK & SR);
    pose proof (ck_buf_read m1 A bs ib _ BY ltac:(lia) eq_refl) as RDB;
    do 4 zstep; rewrite sxb_sval; zstep; cbv beta; rewrite (bz_val bs ib BF); zstep;
    ck_branch U JOIN CK; clear RD CK SR RDB.

  Lemma adl_inner : forall (c k : nat) i0 q sa sb res m1
      (x1 x5 x6 x7 x10 x13 x14 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 : word),
    Z.of_nat c = 347 - q -> 0 <= q < 347 -> 0 <= i0 -> i0 + 5552 <= n ->
    0 <= sa <= 65535 + 255 * (16 * q) -> 0 <= sb <= 65535 + 1481295 * (16 * q) ->
    res = adl_inner_res k (5552 - 16 * q) (sa, sb) (skipn (Z.to_nat (i0 + 16 * q)) bs) ->
    INVN (Z_to_bv 64 (A + i0)) (Z_to_bv 64 i0) m1 ->
    (forall sa' sb' (y1 y5 y6 y7 y8 y10 y13 y14 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 : word),
        0 <= sa' <= 65535 + 255 * 5552 -> 0 <= sb' <= 65535 + 1481295 * 5552 ->
        res = adl_blocks_res k (adl_red (sa', sb')) (skipn (Z.to_nat (i0 + 5552)) bs) ->
        evtF asegs RNG (POST res)
          (MS (mkR y1 (Z_to_bv 64 (SP + -160)) gp tp y5 y6 y7 y8 (Z_to_bv 64 0) y10 (Z_to_bv 64 A) (Z_to_bv 64 (n - i0 - 5552)) y13 y14
                   (Z_to_bv 64 sb') (Z_to_bv 64 2147450880) (Z_to_bv 64 sa') y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 (Z_to_bv 64 (A + i0)))
              FR (Z_to_bv 64 0x95378) fc None m1 (seg_rom asegs))) ->
    evtF asegs RNG (POST res)
      (MS (mkR x1 (Z_to_bv 64 (SP + -160)) gp tp x5 x6 x7 (Z_to_bv 64 (Z.shiftr (A + (i0 + 16 * q)) 3 + 2147450880)) (Z_to_bv 64 (q - 347)) x10
               (Z_to_bv 64 A) (Z_to_bv 64 (n - i0 - 5552)) x13 x14
               (Z_to_bv 64 sb) (Z_to_bv 64 2147450880) (Z_to_bv 64 sa) (Z_to_bv 64 (i0 + 16 * q)) x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 (Z_to_bv 64 (A + i0)))
          FR (Z_to_bv 64 0x953fc) fc None m1 (seg_rom asegs)).
  Proof using All.
    induction c as [|c IH]; intros k i0 q sa sb res m1 x1 x5 x6 x7 x10 x13 x14 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30
                                   HC Q0 I0 IN SA SB RES INV1 CONT; [lia|].
    pose proof INV1 as ((j0 & FRM) & ST & MU & WM & MI & BY).
    pose proof KLO as KLO'. unfold KHIGH in KLO'. pose_sp_range sp.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    destruct (unpoisoned_check_mu W (SP - 160) m m1 A (A + n) (A + (i0 + 16 * q)) 1 UNP MU W_above
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(Z.div_mod_to_equations; lia)) as (b & RD & CK & SR).
    zstep. rewrite sxb_sval. do 2 zstep.
    ck_branch 5 0x95408 CK. clear RD CK SR.
    ckK m1 MU BY (A + (i0 + 16 * q) + 1) (i0 + 16 * q) 6 0x95420.
    pose proof (bz_range bs (i0 + 16 * q) BF) as BR0.
    ckK m1 MU BY (A + (i0 + 16 * q) + 2) (i0 + 16 * q + 1) 6 0x95438.
    pose proof (bz_range bs (i0 + 16 * q + 1) BF) as BR1.
    ckK m1 MU BY (A + (i0 + 16 * q) + 3) (i0 + 16 * q + 2) 6 0x95450.
    pose proof (bz_range bs (i0 + 16 * q + 2) BF) as BR2.
    ckK m1 MU BY (A + (i0 + 16 * q) + 4) (i0 + 16 * q + 3) 6 0x95468.
    pose proof (bz_range bs (i0 + 16 * q + 3) BF) as BR3.
    ckK m1 MU BY (A + (i0 + 16 * q) + 5) (i0 + 16 * q + 4) 6 0x95480.
    pose proof (bz_range bs (i0 + 16 * q + 4) BF) as BR4.
    ckK m1 MU BY (A + (i0 + 16 * q) + 6) (i0 + 16 * q + 5) 6 0x95498.
    pose proof (bz_range bs (i0 + 16 * q + 5) BF) as BR5.
    ckK m1 MU BY (A + (i0 + 16 * q) + 7) (i0 + 16 * q + 6) 6 0x954b0.
    pose proof (bz_range bs (i0 + 16 * q + 6) BF) as BR6.
    ckK m1 MU BY (A + (i0 + 16 * q) + 8) (i0 + 16 * q + 7) 6 0x954c8.
    pose proof (bz_range bs (i0 + 16 * q + 7) BF) as BR7.
    ckK m1 MU BY (A + (i0 + 16 * q) + 9) (i0 + 16 * q + 8) 6 0x954e0.
    pose proof (bz_range bs (i0 + 16 * q + 8) BF) as BR8.
    ckK m1 MU BY (A + (i0 + 16 * q) + 10) (i0 + 16 * q + 9) 6 0x954f8.
    pose proof (bz_range bs (i0 + 16 * q + 9) BF) as BR9.
    ckK m1 MU BY (A + (i0 + 16 * q) + 11) (i0 + 16 * q + 10) 6 0x95510.
    pose proof (bz_range bs (i0 + 16 * q + 10) BF) as BR10.
    ckK m1 MU BY (A + (i0 + 16 * q) + 12) (i0 + 16 * q + 11) 6 0x95528.
    pose proof (bz_range bs (i0 + 16 * q + 11) BF) as BR11.
    ckK m1 MU BY (A + (i0 + 16 * q) + 13) (i0 + 16 * q + 12) 6 0x95540.
    pose proof (bz_range bs (i0 + 16 * q + 12) BF) as BR12.
    ckK m1 MU BY (A + (i0 + 16 * q) + 14) (i0 + 16 * q + 13) 6 0x95558.
    pose proof (bz_range bs (i0 + 16 * q + 13) BF) as BR13.
    ckK m1 MU BY (A + (i0 + 16 * q) + 15) (i0 + 16 * q + 14) 14 0x95570.
    pose proof (bz_range bs (i0 + 16 * q + 14) BF) as BR14.
    pose proof (ck_buf_read m1 A bs (i0 + 16 * q + 15) _ BY ltac:(lia) eq_refl) as RDB.
    pose proof (bz_range bs (i0 + 16 * q + 15) BF) as BR15.
    zstep. zstep. cbv beta. rewrite (bz_val bs (i0 + 16 * q + 15) BF). clear RDB.
    do 35 zstep.
    setreg 9 (Z_to_bv 64 (q + 1 - 347)) ltac:(f_equal; symmetry; apply cnt347; lia).
    replace (5552 - 16 * q) with (5552 - 16 * (q + 1) + 16) in RES by lia.
    rewrite (bz_skipn16 bs (i0 + 16 * q) ltac:(lia) ltac:(lia)) in RES. rewrite adl_inner_res_16 in RES by lia.
    replace (i0 + 16 * q + 16) with (i0 + 16 * (q + 1)) in RES by lia.
    if_cases KB; zify_cond KB.
    -
      replace (i0 + 16 * q + 16) with (i0 + 16 * (q + 1)) by lia.
      replace (Z.shiftr (A + (i0 + 16 * q)) 3 + 2147450882) with (Z.shiftr (A + (i0 + 16 * (q + 1))) 3 + 2147450880)
        by (replace (A + (i0 + 16 * (q + 1))) with (A + (i0 + 16 * q) + 16) by lia; rewrite shiftr3_add16; lia).
      eapply (IH k i0 (q + 1)); [lia|lia|lia|lia| | | eapply adl_inner_res_eq; [ | | exact RES] |exact INV1|exact CONT]; lia.
    -
      zstep.
      assert (Q346 : q = 346) by lia. 
      replace (q + 1 - 347) with 0 by lia.
      replace (i0 + 16 * (q + 1)) with (i0 + 5552) in RES by lia.
      replace (5552 - 16 * (q + 1)) with 0 in RES by lia. rewrite adl_inner_res_0 in RES.
      eapply CONT; [ | | eapply adl_blocks_res_red_eq; [ | | exact RES]]; lia.
  Qed.

  Lemma adl_outer : forall (k : nat) i0 sa sb res m1
      (x1 x5 x6 x7 x9 x10 x13 x14 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 : word),
    Z.of_nat k = (n - i0) / 5552 -> 0 <= i0 -> 5552 <= n - i0 -> 0 <= sa <= 65535 -> 0 <= sb <= 65535 ->
    res = adl_blocks_res k (sa, sb) (skipn (Z.to_nat i0) bs) ->
    INVN0 m1 ->
    evtF asegs RNG (POST res)
      (MS (mkR x1 (Z_to_bv 64 (SP + -160)) gp tp x5 x6 x7 (Z_to_bv 64 (A + i0)) x9 x10 (Z_to_bv 64 A) (Z_to_bv 64 (n - i0)) x13 x14
               (Z_to_bv 64 sb) (Z_to_bv 64 2147450880) (Z_to_bv 64 sa) (Z_to_bv 64 i0) x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 (Z_to_bv 64 (A + i0)))
          FR (Z_to_bv 64 0x953e0) fc None m1 (seg_rom asegs)).
  Proof using All.
    induction k as [|k IH]; intros i0 sa sb res m1 x1 x5 x6 x7 x9 x10 x13 x14 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30
                                   HK I0 N0 SA SB RES INV1.
    { exfalso. Z.div_mod_to_equations. lia. }
    pose proof INV1 as ((j0 & j40 & FRM) & ST & MU & WM & MI & BY).
    pose proof KLO as KLO'. unfold KHIGH in KLO'. pose_sp_range sp.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (zb_length bs) as ZBL.
    do 7 zstep.
    setreg 12 (Z_to_bv 64 (n - i0 - 5552)) ltac:(symmetry; apply sub5552_mach).
    setreg 8 (Z_to_bv 64 (Z.shiftr (A + (i0 + 16 * 0)) 3 + 2147450880)) ltac:(f_equal; replace (i0 + 16 * 0) with i0 by lia; lia).
    setreg 18 (Z_to_bv 64 (i0 + 16 * 0)) ltac:(f_equal; lia).
    rewrite adl_blocks_res_S in RES. change NMAX with (5552 - 16 * 0) in RES.
    replace (Z.to_nat i0) with (Z.to_nat (i0 + 16 * 0)) in RES by lia.
    assert (INV2 : INVN (Z_to_bv 64 (A + i0)) (Z_to_bv 64 i0) m2).
    { split; [eexists; exact FRM|]. repeat (split; [assumption|]). assumption. }
    eapply (adl_inner 347 k i0 0); [lia|lia|lia|lia|lia|lia|exact RES|exact INV2| ].
    intros sa' sb' y1 y5 y6 y7 y8 y10 y13 y14 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 SA' SB' RES'.
    do 7 zstep.
    setreg 13 (Z_to_bv 64 (amag_t sa')) ltac:(f_equal; symmetry; apply amag_t_mach; lia).
    zstep.
    setreg 10 (Z_to_bv 64 (amag_t sb')) ltac:(f_equal; symmetry; apply amag_t_mach; lia).
    pose proof (amag_t_range sa' ltac:(lia)) as TRa. pose proof (amag_v_range sa' ltac:(lia)) as VRa.
    pose proof (amag_q_range sa' ltac:(lia)) as QRa. unfold amag_q in QRa.
    pose proof (amag_t_range sb' ltac:(lia)) as TRb. pose proof (amag_v_range sb' ltac:(lia)) as VRb.
    pose proof (amag_q_range sb' ltac:(lia)) as QRb. unfold amag_q in QRb.
    do 14 zstep.
    setreg 17 (Z_to_bv 64 (sa' mod 65521)) ltac:(f_equal; change 65521 with BASE at 1; rewrite <- (amag_mod sa') by lia; unfold amag_q; reflexivity).
    setreg 15 (Z_to_bv 64 (sb' mod 65521)) ltac:(f_equal; change 65521 with BASE at 1; rewrite <- (amag_mod sb') by lia; unfold amag_q; reflexivity).
    pose proof (mod_BASE_range sa') as MRa. pose proof (mod_BASE_range sb') as MRb. unfold BASE in MRa, MRb.
    unfold adl_red in RES'. cbn [fst snd] in RES'.
    do 4 zstep.
    if_cases KE; zify_cond KE; rewrite Z.shiftr_div_pow2 in KE by lia; change (2 ^ 4) with 16 in KE.
    -
      assert (K0 : k = 0%nat) by (Z.div_mod_to_equations; lia). rewrite K0 in RES'.
      replace (A + i0 + 5552) with (A + (i0 + 5552)) by lia. replace (n - i0 - 5552) with (n - (i0 + 5552)) by lia.
      eapply (CTX adl_after_blocks); [ | | | |exact RES'| eapply adl_INVN_T; exact INV2]; first [lia | Z.div_mod_to_equations; lia].
    -
      replace (A + i0 + 5552) with (A + (i0 + 5552)) by lia. replace (n - i0 - 5552) with (n - (i0 + 5552)) by lia.
      eapply (IH (i0 + 5552)); [ | | | | |exact RES'| eapply adl_INVN_0; exact INV2]; first [lia | Z.div_mod_to_equations; lia].
  Qed.
End P.
