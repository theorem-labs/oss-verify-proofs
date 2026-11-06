(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Run.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import CatSim ShapeAlg Spec.
Import ListNotations.
Open Scope bv_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require PropExec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__ShapeLaws () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Init.Peano."; "Corelib.Init.Specif."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.Fs."; "LinuxProcessSemantics.LinuxProcessSem.State."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ShapeAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Spec."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0A"; "0A'"; "0B"; "0B'"; "0C"; "1app"; "1length"; "1list"; "1nat"; "1nil"; "2and"; "2eq"; "3le"; "4proj1_sig"; "5firstn"; "5skipn"]; ["6Z"; "0K"; "7Fs"; "8event"; "9TSet"; "9t_alt"; "9t_alt2"; "9t_emit"; "9t_eq"; "9t_exit"; "9t_nil"; "9wr_index"; ":W"; ":exit_code"; ":t_die"; ";le"]; [";lt"; "0T"; "0a"; "0b"; "0bs"; "0c"; "0ch"; "0code"; "0e"; "0evs"; "0fs"; "0i"; "0msg"; "0n"; "<Z_to_bv"; "<bv"]; ["<bv_and"]]).
Section FPX_1. Context {fx : PropExec.FPState}.
Lemma t_alt2_comm : ltac2:(TCodec.tc2 tcn__ShapeLaws ":&D&H&Fr2r1%3221%4223%6221p681p291").
Proof. intros A B tr. unfold t_alt2. tauto. Qed.
Lemma t_alt2_assoc : ltac2:(TCodec.tc2 tcn__ShapeLaws ">&D&H&Fr3r2%3221r1%5221%6242%7261%9231p:;1p6<1p2=1").
Proof. intros A B C tr. unfold t_alt2. tauto. Qed.
Lemma t_alt2_idem_eq : ltac2:(TCodec.tc2 tcn__ShapeLaws "<&D&Hr2r1%3221&Fr3%2215%7212p051p6:1p2;1").
Proof. intros A B H tr. unfold t_alt2. pose proof (H tr). tauto. Qed.
Lemma t_alt2_idem_eq_r : ltac2:(TCodec.tc2 tcn__ShapeLaws "<&D&Hr2r1%3221&Fr3%2215%7216p051p6:1p2;1").
Proof. intros A B H tr. unfold t_alt2. pose proof (H tr). tauto. Qed.
Lemma t_alt2_absorb : ltac2:(TCodec.tc2 tcn__ShapeLaws ":&D&H&Fr2r1%3221%4231%6212p681p291").
Proof. intros A B tr. unfold t_alt2. tauto. Qed.
Lemma t_alt2_congr_l : ltac2:(TCodec.tc2 tcn__ShapeLaws ">&D&Hr3r2%3221&Fr4%2214%3265%8221p061p6;1p4<1p2=1").
Proof. intros A A' B H tr. unfold t_alt2. pose proof (H tr). tauto. Qed.
Lemma t_alt2_congr_r : ltac2:(TCodec.tc2 tcn__ShapeLaws "?&D&Hr2r1%3221&Fr4r3%3221%4237%9221p071p8<1p6=1p2>1").
Proof. intros A B B' H tr. unfold t_alt2. pose proof (H tr). tauto. Qed.
Lemma t_alt3_as_alt2 : ltac2:(TCodec.tc2 tcn__ShapeLaws ">&D&H&Fr3r2r1%4221%5241%6254%7214%9231p:;1p6<1p2=1").
Proof. intros A B C. apply t_eq_sym, t_alt2_assoc. Qed.
Lemma t_alt2_nil_l : ltac2:(TCodec.tc2 tcn__ShapeLaws ">&Dr1(9'C%211%411&H&F&Jr2%3221%5212p071pR4=1").
Proof.
intros T H0 tr. unfold t_alt2, t_nil. split.
- intros [-> | H]; [exact H0 | exact H].
- intros H. right. exact H.
Qed.
Lemma t_alt2_nil_r : ltac2:(TCodec.tc2 tcn__ShapeLaws ">&Dr1(9'C%211%411&H&Fr2&J%3221%5213p071pR4=1").
Proof.
intros T H0 tr. unfold t_alt2, t_nil. split.
- intros [H | ->]; [exact H | exact H0].
- intros H. left. exact H.
Qed.
Lemma t_emit_has_nil : ltac2:(TCodec.tc2 tcn__ShapeLaws "<'7'C%211&D&Gr2r1(9%117%53431pR471pRD91").
Proof. intros evs T. unfold t_emit. left. apply is_prefix_nil. Qed.
Lemma t_exit_has_nil : ltac2:(TCodec.tc2 tcn__ShapeLaws "='Q?yR0%211&B&Ir2r1(9'C%211%63541pRF81pR@:1").
Proof. intros. unfold t_exit. apply t_emit_has_nil. Qed.
Lemma t_alt2_has_nil_l : ltac2:(TCodec.tc2 tcn__ShapeLaws "<&Dr2(9'C%211%411&Fr3%23174p041p6:1p2;1").
Proof. intros A B H. unfold t_alt2. left. exact H. Qed.
Lemma t_alt2_emit_nil_l : ltac2:(TCodec.tc2 tcn__ShapeLaws "E'7'C%211&Dr1(9%115%311&H&F&Gr3&J%3221r2%5241%7231%9212p0;1pR4@1pRBB1").
Proof.
intros e T H0 tr. unfold t_alt2, t_emit, t_nil. split.
- intros [[Hp | (tr' & -> & ->)] | H].
+ left. exact Hp.
+ right. exists []. split; [reflexivity | exact H0].
+ exact H.
- intros H. right. exact H.
Qed.
Lemma W_app : ltac2:(TCodec.tc2 tcn__ShapeLaws "G'@'7'Q?y8%211%411';'C%711&Lr3&5r2r1%33:21%6251%7264%8274%73;21%=3;41pR8?1pR6@1pR>F1").
Proof. intros. unfold W. apply map_app. Qed.
Lemma W_nil : ltac2:(TCodec.tc2 tcn__ShapeLaws "@'@';'7'C%211&Lr1(9'Q?y8%211%411%7261%61:%=3:21pR>?1").
Proof. reflexivity. Qed.
Lemma t_emit_W_app : ltac2:(TCodec.tc2 tcn__ShapeLaws "K'@'7'Q?y8%211%411&D&H&G&Lr4r3%3221r2%5241r1%8221%9251&5%13?86%;2:1%=216%?251pR4A1pR8C1pR6D1pR>J1").
Proof.
intros ch a b T. rewrite W_app. apply t_eq_sym.
intros tr. unfold t_emit. split.
- intros [Hp | (tr' & -> & HT)].
+ apply is_prefix_app_split in Hp as [Hp | (b' & -> & Hp)].
* left. exact Hp.
* right. exists b'. split; [reflexivity | left; exact Hp].
+ right. exists (W ch b ++ tr'). split; [rewrite app_assoc; reflexivity|].
right. exists tr'. auto.
- intros [Hp | (tr' & -> & [Hp | (tr'' & -> & HT)])].
+ left. apply is_prefix_app_r. exact Hp.
+ left. apply is_prefix_app_mono. exact Hp.
+ right. exists tr''. rewrite app_assoc. auto.
Qed.
Lemma t_alt_W_wall : ltac2:(TCodec.tc2 tcn__ShapeLaws "QF'@'7'Q?y8%211%411&Dr1(9'C%211%411'<u1&6r3%22<1%5241&H&E&Kr4%211&G&Lr6&>&='8':%B2AG%A2K6%D2I1%4231qRL61%8371Lr5%;3Q121%>2=1&?%13Q454%A2@1%C21E%D251qRHF1%J2G1%F2:I%H21Q0%N231p0Q01p0Q71pQ4Q=1pR:Q?1pR>QE1").
Proof. intros ch bs K HK Hnb. unfold W. apply t_alt_wall; assumption. Qed.
Lemma t_emit_W_nil : ltac2:(TCodec.tc2 tcn__ShapeLaws "F'@&Dr1(9'C%211%411&H&G&Lr3'Q?y8%211%;11%6251r2%9221%;212p0=1pR4C1pR>E1").
Proof. intros ch T H0. rewrite W_nil. apply t_emit_nil_eq. exact H0. Qed.
Lemma t_emit_alt2_distr : ltac2:(TCodec.tc2 tcn__ShapeLaws "C'7'C%211&D&H&Gr3&Fr2r1%3221%6251%7264%8274%7221%;241p6=1p2>1pRB@1").
Proof.
intros e A B tr. unfold t_emit, t_alt2. split.
- intros [Hp | (tr' & -> & [HA | HB])].
+ left. left. exact Hp.
+ left. right. exists tr'. auto.
+ right. right. exists tr'. auto.
- intros [[Hp | (tr' & -> & HA)] | [Hp | (tr' & -> & HB)]].
+ left. exact Hp.
+ right. exists tr'. auto.
+ left. exact Hp.
+ right. exists tr'. auto.
Qed.
Lemma exit_code_and_255 : ltac2:(TCodec.tc2 tcn__ShapeLaws "J'@':&Ozr1%3221&Q0+X0%2241%8241';'Q?yR0%211&Q@&Q>r2%2251+WO%4271%63831&M%116%=3:31p0?1pR<I1").
Proof.
intros c Hc. unfold exit_code. apply bv_eq.
rewrite bv_and_unsigned, !Z_to_bv_unsigned.
rewrite !bv_wrap_small by (change (bv_modulus 64) with (2 ^ 64)%Z; lia).
change 255%Z with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_small. lia.
Qed.
Lemma t_die_unfold : ltac2:(TCodec.tc2 tcn__ShapeLaws "H'7'Q?y8%211%411&B';&D&Nr2r1%3221&G&L+2%2216&I&M%114%3219%8251%?3>:1pRFA1pRJC1").
Proof. reflexivity. Qed.
Lemma exit_leaf_eq : ltac2:(TCodec.tc2 tcn__ShapeLaws "Q7'@&B':&Ozr2%3221&Q0+X0%2241%8241&H&G&L+1(9'Q?y8%211%411%7261&I&Q@yR0&Q>r3%2231+WO%4251%73631%921I%C2;1&M%118%=21M%H241p0J1pRFQ41pR<Q61").
Proof.
intros c fs Hc. rewrite exit_code_and_255 by exact Hc. apply t_emit_W_nil. apply t_exit_has_nil.
Qed.
End FPX_1.
