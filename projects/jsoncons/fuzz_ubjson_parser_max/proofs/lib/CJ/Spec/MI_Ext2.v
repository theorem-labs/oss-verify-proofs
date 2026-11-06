(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec Require Import STree Malloc MallocCtrl KInv MI_Inv MI_Kit MI_List MI_Ext.
Import ListNotations.
Local Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import RunP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__CJ_Spec_MI_Ext2 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.MI_Inv."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.Malloc."; "stdpp.base."; "stdpp.countable."; "stdpp.decidable."; "stdpp.gmap."; "stdpp.numbers.N."; "stdpp.numbers.Z."], [["0BL"; "1Some"; "1fst"; "1option"; "1prod"; "2eq"; "3N"; "3Z"; "0LS"; "4group_ok"; "4inv_L"; "4inv_M"; "4inv_S"; "5RKGroup"; "5aptr"; "5get_head"]; ["5ghdr"; "5lhead"; "5meta"; "5optr"; "5r_kind"; "5region"; "5rkind"; "5s_groups"; "5s_metas"; "5s_regions"; "5s_slots"; "0X"; "0ai"; "0b"; "0h"; "0m"]; ["0r"; "0rid"; "0st"; "0st'"; "6lookup"; "7N_countable"; "7Z_countable"; "7prod_countable"; "8prod_eq_dec"; "9gmap"; "9gmap_lookup"; ":eq_dec"; ";eq_dec"]]).
Section CEIL_WRAP_1.
Context {RUNp : RunP}.
Section EXT2.
Variables (X : extras) (st st' : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr).
Lemma inv_M_ext : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Ext2 "Q3'5'Q9&>&Q8'6&Q;'7&Q<%544321&Q7&Q5&Q6%36872651'B%=4<621&HvQ3%211vQ2%411%D3631'@%E4D>:1&G%118%217%J3421';vKv8%332<1%433?2p021p071p0>1").
Proof.
intros HM HG I. pose proof (MR_ext st st' HM) as ME. pose proof (hosts_ext st st' HG) as HE.
destruct I as [M1 M2 M3 M4 M5]; constructor.
- intros m Hm. rewrite !ME in *. apply M1. exact Hm.
- intros m b Hm. rewrite ME in Hm. destruct (M2 m b Hm) as [H|H]; [left; apply HE; exact H| right; exact H].
- intros b h Hb. rewrite HG in Hb. destruct (M3 b h Hb) as (m & H1 & H2 & H3). exists m. rewrite !ME. auto.
- intros m Hm. rewrite HM. apply M4. exact Hm.
- intros z Hz. destruct (M5 z Hz) as (H1 & H2 & H3 & b & H4 & H5). rewrite !ME, HG. repeat split; auto. exists b. auto.
Qed.
Lemma inv_L_ext : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Ext2 "Q;'5'Q9&>&Q8'6&Q;'7&Q<%544321&Q7&Q5&Q6%36872651'B%=4<621&HvQ3%211vQ2%411%D3631'@%E4D>:1&G%118%217%J3421'A&C&?r1%22?1%32>2%Q13521pQN71':v8%22C1%32F2p021p061p0?1p0F1").
Proof.
intros HM HG HE I. pose proof (MR_ext st st' HM) as ME.
destruct I as [L1 L2 L3 L4 L5 L6 L7 L9]; constructor.
- intros h. rewrite HE. apply L1.
- intros h. apply (dll_ext_metas st st' HM). apply L2.
- exact L3.
- exact L4.
- intros m. rewrite !ME. apply L5.
- intros m Hm. rewrite !ME. apply L6. exact Hm.
- intros sc m Hm. destruct (L7 sc m Hm) as (H1 & H2 & H3). rewrite (live_group_ext st st' HG), ME. auto.
- exact L9.
Qed.
Lemma group_ok_ext : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Ext2 "R>&>'4'6'7%3221'5'Q9&Q8&Q;&Q<%348271&Q7&Q5&Q6%36<62;51'B%:4@621&HvQ3%211vQ2%411%A3631%F2GD%B4H>:1&J%118%217%G3421'E'3%112&Q4%K4OIE4&Q:%14Q1KG6r2&I%11B%76Q5:6431(1r1%22=1%Q63<41'F&D%11:(=%Q;3421&2r8%23QAQ@1r4%Q@3QC21r5%B1Q5%H6QFKGE21%A2L5%QE3K21p061p0<1p0B1pR2Q11pR4QM1'9vKv8r6%463Q@21>@r7%665QD413@p031p091p0Q=1p0QD1pQJR81pQLR81pR0R=1").
Proof. intros m b ai.
intros HM HS HR I. pose proof (MR_ext st st' HM) as ME.
destruct I as [G1 G2 G3 G4 G5 G6 G7 G8 G9 G9b G10 G11 G12 G13 G14]; constructor; rewrite ?ME, ?HM, ?HS; try assumption.
- intros Hml. destruct (G13 Hml) as (H0 & r & Hr & Hk & E1 & E2). split; [exact H0|]. exists r. split; [| auto]. apply HR; auto.
- intros H. destruct (G14 H) as (p & i & ? & ? & ? & ? & ?). exists p, i. rewrite !ME. auto 10.
Qed.
Lemma inv_S_ext : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Ext2 "Q;'5'Q9&>&Q8'6&Q;'7&Q<%544321&Q7&Q5&Q6%36872651'B%=4<621&HvQ3%211vQ2%411%D3631'@%E4D>:1&G%118%217%J3421'4%12JF%L4KEA1&J%11?%21>%Q13421'<vKv0%332C1%433F2p021p071p0?1p0F1").
Proof.
intros HM HG HS I. pose proof (MR_ext st st' HM) as ME. pose proof (hosts_ext st st' HG) as HE.
destruct I as [S1 S2 S3 S4 S5 S6]; constructor.
- intros s m i H. rewrite HS in H. destruct (S1 s m i H) as (? & ? & ?). rewrite (live_group_ext st st' HG), !ME. auto.
- intros b m i Hb Hi. rewrite HS, ME. apply (S2 b); [apply HE; exact Hb| rewrite <- ME; exact Hi].
- intros b m ai i Hb Hi. rewrite HG in Hb. rewrite !ME, HG. apply (S3 b m ai i); [exact Hb| rewrite <- ME; exact Hi].
- intros c Hc. rewrite HS. apply S4. exact Hc.
- exact S5.
- intros k Hk. destruct (S6 k Hk) as (m & i & ? & ?). exists m, i. rewrite HS, ME. auto.
Qed.
End EXT2.
End CEIL_WRAP_1.
