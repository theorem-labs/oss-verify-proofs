(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.B02 Require Import ImageA.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.Lib Require Import RzCPS NodesA SysStep Arr.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.Lib Require Import StoreFast.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.B02 Require Import Layout.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.B02 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface Lept_env LeptC_kit LeptL_kit LeptB_guard LeptB_guard2.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib Require KReplay.
Ltac2 kr_t_LeptB_guard3 () := "C56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z6ltb_ltK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3lorI47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z:lor_nonnegK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K47Corelib4Init9Datatypes6option02C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z<lor_eq_0_iffK46Stdlib9micromega6VarMap1t01C47Corelib4Init5Logic3notK46Stdlib9micromega5Tauto8GFormula07C56Stdlib6ZArith6BinInt1Z2leI47Corelib4Init5Logic2eq00K47Corelib7Numbers7BinNums8positive01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega5Tauto8GFormula03K47Corelib7Numbers7BinNums1Z01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums8positive03I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op201I47Corelib4Init5Logic5False00K46Stdlib9micromega=RingMicromega3Op205".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma div_guard_pos : forall x, 0 <= x -> (0 <? Z.lor 18446744073709551614 x) = true.
Proof.
ltac2:(KReplay.run1 (kr_t_LeptB_guard3 ()) [] "h04__x1h11ah21bh31Hh47__arithh54__ffh68__varmaph75__with81Eh94__p1h:4__p2h;1mh<1nh=2H0h>2H1h?2Hxh@1xp;2p;1p;4p;3p;6p;7p;8g0000j2;Tg000Mj2:Tg000ij2ZTg001Ij1ETg001nj1DTg002Lj25Tg002iR0j23Tg003Dj2@Tg003hj1YTg004Hj1UTg004hj2TTg005Fj1QTg005dj1NTg006Oj2<Tg0072j2LTg007Uj47Tg008@j1FTg008bj2GTg009Dj2HTg009^j2ITg00:Jj3JTg00:ij4KTg00;[j2CTg00<Aj1BTg00<_j1ATg00=8j6OTg00=\j2PTg00>8j3?Tg00>Rj10Tg00?7j7STg00?[j7XTg00@?j8WTg00@cj6VTg00AGR1f0R2'Pp=2g00AeR3g00BER47?2p=8%02#0p=R%02#0#0#0p=M%02#0#0#0#0#0#0#0p=4f1R5g00BeR6g00CDR7P7g00CdR8P2g00DDFSp=6f2R9P6P7P7P8P5P2FXp==f3R:P6P7P7P8P9P5P2GWp=9g00DdR;??21p=1P5P6P7P7P8P2EVp=>%22R<P01;52#81:95R=[1:521;95#8[R>1;:9#8\=1Z52P2n2001000000120000000X;;X<;P>^;;^<;P2P1g00EBR>#R#M#4#4#4#4#4#4#4#E#DR=/59R?P01552R@#2%29%25RA'3RB[13A<1595RC#2[RD15:9#2\B1@52P2n2001000000120000000X2;X1;PD^2;^1;P2P=P:g00EgRD#YRB%UDRD1T;5RE%Q;RF%N;RGP;1<;1RHg00FSRI1L;>R>C7,6GRJ%F7RKP;PHPI1<;=RIC7,6G==GJC91GG8RLP2P91H341I29#8dAJ;15CKR4b5b6b7X0;%2=/3A\<^0;P2f4P:O2b4O3b3%2?15=:#1R?P0%1@%19R@%15R0'3[R<%12R3,30%1CRC[%1:/3@\C1C52P5n2001000000120000000X2;X1;P<^2;^1;P2P=f5R<P5O3%1=RC%1<'3p-0R@PBPD%B;PFPGP;PIg00G:RIPHC7,6G1>G95=GPK1>G:C9PLP4b5b6b7X9@W:13C2P9[^9@^:@P2g00GaR@f7#1P5O3b4b8b3W8%A?R?eP?PBPDPEPFPGPGP6P7P7P8P;P>PIPHC7,6GEOPKPGPJPKP;PHg00H>P>C7,6GC9C9PLP4b5b6b7X0;P@\31:19\A[^0;P215=<P5P9O3b4b>b=O3b3W?X@;o"). Qed.
Ltac div_guard_fix :=
  repeat match goal with
  | |- context [0 <? Z.lor 18446744073709551614 (Z.lxor (bv_unsigned ?w) ?k)] =>
      rewrite (div_guard_pos (Z.lxor (bv_unsigned w) k))
        by (apply Z.lxor_nonneg; pose proof (bv_unsigned_in_range 64 w); split; intros _; lia)
  end; cbn [Z.b2z].
Ltac po_irrefl_fix :=
  progress (rewrite !Z.ltb_irrefl); cbn [Z.b2z]; change (Z.lxor 0 0) with 0; change (Z.lxor 0 1) with 1; change (Z.lxor 1 0) with 1.
Ltac guard_fix ::= try sx32_fix; swrap_fix; po_fix; al_fix; try mulh_fix; try mulh_fix2; po_neg_fix; po_not_fix; try al_or_fix; try po_irrefl_fix; try (progress div_guard_fix).
