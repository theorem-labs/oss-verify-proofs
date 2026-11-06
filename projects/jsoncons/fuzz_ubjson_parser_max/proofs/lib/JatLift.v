(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatSim StoreOk AsanAcct ArtMem ArtRuns ArtRunsMem JatFp JatCellEx ArtBridge.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLiaT. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__JatLift () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ArtBridge."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ArtMem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ArtRuns."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanAcct."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatLift."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1app"; "1bool"; "1false"; "1list"; "1nat"; "1option"; "2eq"; "2iff"; "2not"; "2or"; "3Z"; "0FP"; "0H"; "0H0"; "0H1"; "0M"]; ["0M0"; "0M1"; "4in_ev_ranges"; "5cell"; "5wr"; "6aev"; "7mrestrict"; "7range_avoids"; "8art_vis"; "9loaded_segments"; ":add"; ":le"; ":lt"; ":of_nat"; ":pow"; "0a"]; ["0a'"; "0log0"; "0log1"; "0n"; "0n'"; "0sfx"; ";Z_to_bv"; ";bv"; ";bv_unsigned"; "0v"; "0x"; "0z"]]).
Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.
#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation cellA := (cell Asan.M.loaded_segments).
#[local] Abbreviation wrA := (wr Asan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).
Definition art_vis (H : word -> bool) (a n : Z) : Prop := forall x : word, a <= U x < a + n -> H x = false.
Lemma art_vis_sub : ltac2:(TCodec.tc2 tcn__JatLift "L'Q7yR0%211'1p021':&Hr5r4r3%43321&K%1253&J%1265r6%3219%6231r8%=31<;p031p091p0<1pR:B1pR2C1pR8D1pR0E1pJG1").
Proof. intros H a n a' n' V L1 L2 x Hx. apply V. lia. Qed.
Lemma art_vis_avoids : ltac2:(TCodec.tc2 tcn__JatLift "Q6'Q7yR0%211'1p021':'4&Kzr2%3221&L&Jr3&M%116%4231&N+2+R0%3221%:251&Hr5r4%;1<%43321&Gr6&Q6%12M7%43317p061p0<1p0H1pR8M1pR0O1pJQ11").
Proof.
intros H a n Ha Hn V k Hk. apply V. unfold woff. rewrite (art_u_lit a) by lia. rewrite art_u_lit by lia. lia.
Qed.
Lemma art_cell_vis : ltac2:(TCodec.tc2 tcn__JatLift "QB'Q7yR0%211'1p021'5y8%711%311p071':'4&Kzr3%3221&L&Jr4&M%116%4231&N+2+R0%3221%:251&Hr7r5%;1<%43321&7&C&I&Fr8%2219r6%65521:E%756<2;F%9221p0;1p0A1p0M1pRDQ31pR8Q31pR0Q51pQ0Q71pJQ=1").
Proof.
intros H M a n v Ha Hn V. unfold cell. rewrite (rdn_mrestrict_eq ASEGS H n M (Z_to_bv 64 a) (art_vis_avoids H a n Ha Hn V)). tauto.
Qed.
Lemma art_byte_vis : ltac2:(TCodec.tc2 tcn__JatLift "J'Q7yR0%211'1pRF21'5y8%711%311p071'6r3r1%211(2%53<21&Fr4r2%33281%912%;3=21p071pRFE1pQ0?1pJE1").
Proof. intros H M x E. unfold mrestrict. rewrite E. reflexivity. Qed.
Lemma art_wr_vis : ltac2:(TCodec.tc2 tcn__JatLift "Q='Q7yR0%211'1p021'5y8%711%311p071':&Kzr2%3221&L&Jr3%2215&N+2+R0%3221%8251&Hr6r4%3321:&7&D&I&Fr7%2218r5%645219%746;2:%9221p0;1p0@1p0J1pR8O1pR0Q01pQ0Q21pJQ81").
Proof.
intros H M a n Ha Hn V. split; intros W; apply art_wr_of_wview; try lia; intros x Hx.
- rewrite <- (wview_mrestrict_eq ASEGS H M x (V x Hx)). apply (art_wr_wview ASEGS _ a n Ha Hn W x Hx).
- rewrite (wview_mrestrict_eq ASEGS H M x (V x Hx)). apply (art_wr_wview ASEGS _ a n Ha Hn W x Hx).
Qed.
Lemma art_vis_of_wr : ltac2:(TCodec.tc2 tcn__JatLift "QC'Q7yR0%211'1p021'5y8%711%311p071':&Kzr2%3221&L&Jr3%2215&N+2+R0%3221%8251'9r4%:219+RPP0%A221+VbTP0%C215%7231&D&I&Fr7r6%3221r5%74621>&Hr8%23164p041p0=1p0F1p0Q01pR8Q51pR0Q61pQ0Q81pJQ>1").
Proof.
intros H M a n Ha Hn Off W x Hx. pose proof (art_wr_wview ASEGS _ a n Ha Hn W x Hx) as D.
rewrite art_wview_off in D by lia. unfold mrestrict in D. destruct (H x); [exfalso; apply D; reflexivity|reflexivity].
Qed.
Section Lift.
Context {fx : PropExec.FPState}.
Variables (A0 A1 : list (Z * Z)) (M0 M1 : word -> option byte) (model0 model1 : Model) (log0 log1 : list aev).
Let H0 := bhid A0 model0.
Let H1 := bhid A1 model1.
Hypothesis BH : bhist A0 M0 model0 log0 log1 A1 M1 model1.
#[using="M0 M1 log0 log1 BH"] Lemma art_lift_vis : ltac2:(TCodec.tc2 tcn__JatLift "<':&Hv=r2r1%43321v>r3%73215p041pR8:1pR0;1").
Proof.
intros a n V x Hx. destruct BH as (sfx & _ & _ & B2 & _). destruct (H1 x) eqn:E; [|reflexivity].
destruct (B2 x E) as [E0 _]. fold H0 in E0. rewrite (V x Hx) in E0. discriminate E0.
Qed.
#[using="BH"] Lemma art_lift_frame : ltac2:(TCodec.tc2 tcn__JatLift "QH':!p021'Q7yR0%211&8r2&Q8r1%2261%411%611'6'5y8%=11%311&Fv>vA%3321>v=v@%6321A%<3841p0>1pRFF1'3'E%211vQ2&0vQ1%2351I%F3541&Br3%221Mr6%11Q1p031pRHQ:1p081pR<>1r4%11Q4%Q911%L1Q9%J1Q:%Q53Q121p041pRFQ?1p091p0K1pHQE1").
Proof.
intros FP FR EVR x N. destruct BH as (sfx & El & _ & B2 & B3 & _).
destruct (H1 x) eqn:E1.
- exact (proj2 (B2 x E1)).
- destruct (H0 x) eqn:E0.
+ exfalso. apply N. apply (EVR sfx El). apply B3; assumption.
+ pose proof (FR x N) as F. unfold mrestrict in F. fold H1 H0 in F. rewrite E1, E0 in F. exact F.
Qed.
End Lift.
