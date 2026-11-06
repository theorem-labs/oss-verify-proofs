(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import LeptRoom.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_LeptRoomPC () := "K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02K47Corelib4Init5Logic2eq01I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums8positive03C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K47Corelib7Numbers7BinNums1N02K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z2ltK47Corelib7Numbers7BinNums1Z01I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01c69OSSVerify5KrLib6Common9Leptonica:LeptRoomPC<RB_paintcmapC1?~~~~~~~~~~~~~~~".
Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition RK_box : Z := 1.          Definition RB_box : Z := 2 ^ 23.
(* [comment removed for export] *)
Definition RK_cmapcopy : Z := 2.     Definition RB_cmapcopy : Z := 2 ^ 18.
(* [comment removed for export] *)
Definition RK_pixcopy : Z := RK_pix + RK_cmapcopy.
Definition RB_pixcopy : Z := RB_pix + RB_cmapcopy.
(* [comment removed for export] *)
Definition RK_paintcmap : Z := RK_deser + RK_box + 2 * RK_pixcopy.
Definition RB_paintcmap : Z := RB_deser + RB_box + 2 * RB_pixcopy.

Ltac room_consts ::=
  unfold RK_paintcmap, RB_paintcmap, RK_pixcopy, RB_pixcopy, RK_cmapcopy, RB_cmapcopy, RK_box, RB_box,
         RK_hdr, RB_hdr, RK_cmap, RB_cmap, RK_pix, RB_pix, RK_deser, RB_deser in *.

Lemma RK_paintcmap_val : RK_paintcmap = 14.
Proof.
ltac2:(KReplay.run1 (kr_t_LeptRoomPC ()) [] "p;1p;2g0000j10Tg000Uj13Tg001:j12Tg001Xj21Tg0022g002P#0#0#3#2'1o"). Qed.
Lemma RB_paintcmap_le : RB_paintcmap <= 2 ^ 30.
Proof.
ltac2:(KReplay.run1 (kr_t_LeptRoomPC ()) [] "h02Hah17__arithh24__ffh36__sat0h46__sat1h56__sat2h66__sat3h76__sat4h86__sat5h96__sat6h:6__sat7h;6__sat8h<6__sat9h=8__varmaph>5__witp;1p;2p;3p;4p;7g000Uj12Tg001:j13Tg0000j11Tg0035j25Tg003]j26Tg004:j37Tg004^j1ATg005>j1@Tg005^j1?Tg006<j1>Tg006Zj1=Tg007Ej2MTg007hj19Tg008Fj38Tg008ij3<Tg009Lj3LTg009oj4KTg00:Zj7ITg00;>j2HTg001Xj2FTg00;`j2CTg00<Lj3BTg00<fj3DTg00=Ej4ETg00>7j2:Tg00>Tj2GTg00?1j2;Tg00?Mj2JTg00?iR0f0R1'Jp=41;01p=0g002PR2#2R3#3R4%13#1#1R5#3R6'5%44R7%061646R8#4[[%04R9g00@GR:f1R;9746UW0%08\:^09%12R2#1R6#2#2R<#3R=,54%0=164=R>#4[\7A74=;V:X09%0>\:^09%22#1#1R2#3R=,54%0=164=R?#4[\7A74=;V:X09%0?\:^09%23#1#2R3#3R=,54%0=164=R@#4[\7A74=;V:X09%0@\:^09%16#2R6#3R=,54%0=164=RA#4[\7A74=;V:X09%0A\:^09g00@cR9#A%@9g0022R9#?%>9%=9R:g00AOg00AnR=P=g00BNR=P91M94R7%9<589%9598975<9%929897%9398975<99L975<9g00Bn%969897CKg00CUFI1H:=P1f2R=g00D5R:g00DUR7'F1C1==B:7dAD90;CEb2b=b>1:>81:?@,G4':/;AP1b1b3b4b5b6b7b8b9b:b;b<g00E5/;Aeo"). Qed.
