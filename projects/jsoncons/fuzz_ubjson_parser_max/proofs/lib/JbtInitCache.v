(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac As0StepLib As0Tables
ArtMem ArtRegs ArtAtomics ArtTac.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLiaT.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import OtfKit.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__JbtInitCache () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Init.Peano."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ArtMem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtInitCache."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.StoreOk."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1S"; "1nat"; "1option"; "2I"; "2and"; "2eq"; "2ex"; "2not"; "3le"; "4Z"; "5bvmap"; "0M"; "6Wn"; "6apart"; "6cell"; "6wok"]; ["6wr"; "7msteps"; "8art_ic_kept"; "8art_ic_mc"; "8art_ic_mem"; "8art_ic_size"; "9getr"; "9mkst"; ":mem_grows"; ";loaded_segments"; "<add"; "<le"; "<lt"; "<mul"; "<of_nat"; "<pow"]; ["0a"; "0c"; "0ca"; "0fx"; "0k"; "0n"; "0r"; "0regs"; "0regs'"; "0rom"; "=BV"; "=Z_to_bv"; "=bv"; "=bv_unsigned"; "0v"; "0x"]]).
Local Ltac oF' pc := oF constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc.
Local Ltac oD' pc := oD constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc.
Local Ltac oE' pc := oE constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc.
Local Ltac oW' pc := oW constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc. Local Ltac lia := L5FastLiaT.plia2.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Abbreviation wokA := (wok AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).
Set Printing Depth 1000000. Set Printing Width 10000.
Ltac showst := lazymatch goal with |- msteps _ (mkst ?R ?P ?MM _) _ => idtac "REGS" R; idtac "PC" P; idtac "MEM" MM | |- ?G => idtac "GOAL" G end; fail "SHOWST".
Definition art_ic_size (c : Z) : Z := if c =? 31 then 64 else AsanTab.class_size c.
Definition art_ic_mc (c : Z) : Z := 2 * Z.max 1 (Z.min 8 (1024 / art_ic_size c)).
Fixpoint art_ic_mem (M : word -> option byte) (ca : Z) (k : nat) : word -> option byte :=
match k with
| O => M
| S k' => Wn 8 (Wn 4 (art_ic_mem M ca k') (ca + 80 * Z.of_nat k + 4) (art_ic_mc (Z.of_nat k))) (ca + 80 * Z.of_nat k + 8) (art_ic_size (Z.of_nat k))
end.
Lemma art_ic_mem_S : ltac2:(TCodec.tc2 tcn__JbtInitCache "Q='Q<yR0%211'2y8%511%311p051'9'1'5&Dr3r2(0r1%211%63541&<u8u4%:3986&J&M+R@&N%11;+1%6221%6251%82A1+4%:221&C%116%A4?>31+8%?271&E%11;%F4E531%O3Q2H1pR:Q11pR6Q31pHQ51").
Proof. intros. cbn [art_ic_mem]. rewrite Nat2Z.inj_succ, <- Z.add_1_r. reflexivity. Qed.
Section SE.
Local Abbreviation SEC_T_art_ic_size_pos := (ltac2:(TCodec.tc2 tcn__JbtInitCache "C'9'4&K+1r1%3221+O%5231%7231+Q0&Er2%211%;241+RPP0%=231%?231p091pR4B1")) (only parsing).
Variable c : ltac:(sec_ty2 constr:(SEC_T_art_ic_size_pos) 0%nat 0%nat).
Lemma art_ic_size_pos : ltac:(sec_stmt2 constr:(SEC_T_art_ic_size_pos) 1%nat 0%nat).
Proof.
intros Hc.
unfold art_ic_size.
assert (H : forall x, In x (map (fun i => Z.of_nat i) (seq 1 31)) -> 32 <= (if x =? 31 then 64 else AsanTab.class_size x) <= 65536).
{ intros x Hx. cbn in Hx. repeat (destruct Hx as [<-|Hx]; [vm_compute; split; discriminate|]). destruct Hx. }
apply H. apply in_map_iff. exists (Z.to_nat c). split; [lia|]. apply in_seq. lia.
Qed.
End SE.
Lemma art_ic_mc_range : ltac2:(TCodec.tc2 tcn__JbtInitCache "C'9'4&K+1r1%3221+O%5231%7231+2&Cr2%211%;241+@%=231%?231p091pR4B1").
Proof. intros c Hc. unfold art_ic_mc. pose proof (art_ic_size_pos c Hc). split; [lia|]. assert (Z.min 8 (1024 / art_ic_size c) <= 8) by lia. lia. Qed.
Lemma art_ic_mem_grows : ltac2:(TCodec.tc2 tcn__JbtInitCache "D'Q<yR0%211'2y8%511%311p051'9'1&Hr3&Dr2r1%33421%6251pR:81pR6:1pH<1").
Proof. induction k; [apply mem_grows_refl|]. rewrite art_ic_mem_S. eapply mem_grows_trans; [exact IHk|]. eapply mem_grows_trans; apply Wn_grows. Qed.
Lemma wr_ic : ltac2:(TCodec.tc2 tcn__JbtInitCache "L'Q<yR0%211'2y8%511%311p051'9'1&@&Ir5r2r1%544321&Dr6r4%33271r3%;4:218p071pR<?1pR2@1pR:@1pR6B1pHD1").
Proof. intros. eapply wr_grows; [apply art_ic_mem_grows|assumption]. Qed.
Lemma wok_ic : ltac2:(TCodec.tc2 tcn__JbtInitCache "L'Q<yR0%211'2y8%511%311p051'9'1&?&Ir5r2r1%544321&Dr6r4%33271r3%;4:218p071pR<>1pR2@1pR:@1pR6B1pHD1").
Proof. intros. eapply wok_grows; [apply art_ic_mem_grows|assumption]. Qed.
Lemma art_ic_mem_outside : ltac2:(TCodec.tc2 tcn__JbtInitCache "QN'Q<yR0%211'2y8%511%311p051'9'1&Kzr3%3221&L&Jr4+TP0%3221&O+2+R0%3221%9251'8uO%22:1&7'4r6+RD%@221&Q=%12Q0A%H231&M+R@&Nr5%211%5241%J2<1+@%L221%N2;1%A2;1%C11'5&Dr8r7%3421F=%31>%63Q?21p081p0M1p0Q11p0Q<1pS0QH1pR:QB1pR6QD1pHQF1").
Proof.
induction k; intros x Hca Hca' Hk N; [reflexivity|]. rewrite art_ic_mem_S.
rewrite Nat2Z.inj_succ in N.
rewrite 2 Wn_outside by (cbn; lia). apply IHk; [lia|lia|lia|cbn; lia].
Qed.
Lemma cell_ic_other : ltac2:(TCodec.tc2 tcn__JbtInitCache "R>'Q<yR0%211'2y8%511%311p051'9'1&Kzr5%3221&L&Jr6+TP0%3221&O+2+R0%3221%9251'8uO%22:1%A2@;r7&N%11>%@231%B21:'4+1r1%J221r:%911%M241%7241&=r<&M+R@r2%3221%Q0251+4%Q2221+<r9%G11%<443@1p0>1pR4Q?1&>&Ir8%352A81O&Dr=r;%332E1%8571K=6p061p0;1p0Q31p0Q91p0Q;1p0Q?1p0QJ1pRNR01pR<R01pR2R21pR:R21pR6R41pHR61").
Proof.
induction k; intros a n v Hca Hca' Hk Ha Han AP C; [exact C|]. rewrite art_ic_mem_S.
pose proof (AP (Z.of_nat k + 1) ltac:(rewrite Nat2Z.inj_succ; lia)) as A1. unfold apart in A1.
apply cell_Wn_other; [lia|cbn; lia|lia|lia|unfold apart; cbn; lia|].
apply cell_Wn_other; [lia|cbn; lia|lia|lia|unfold apart; cbn; lia|].
apply IHk; [lia|lia|lia|lia|lia| |exact C]. intros c Hc. apply AP. rewrite Nat2Z.inj_succ. lia.
Qed.
Lemma cell_ic_count : ltac2:(TCodec.tc2 tcn__JbtInitCache "QL'Q<yR0%211'2y8%511%311p051'9'1&Kzr4%3221&L&Jr5+TP0%3221&O+2+R0%3221%9251'8uO%22:1'4%B2A<+O%D2>1%4231&>&Ir9r8&M+R@r6%3221%I251u4%:59821J&Dr:%231;:r7%;2:1%Q12>1%A5@418;p081p0D1p0J1p0N1p0Q91pRNQ?1pR4Q@1pR:Q@1pR6QB1pHQD1").
Proof. intros. apply cell_ic_other; [lia|lia|assumption|lia|cbn; lia| intros c' Hc'; unfold apart; cbn; lia | assumption]. Qed.
Lemma cell_ic_mc : ltac2:(TCodec.tc2 tcn__JbtInitCache "QL'Q<yR0%211'2y8%511%311p051'9'1&Kzr3%3221&L&Jr4+TP0%3221&O+2+R0%3221%9251'8uO%22:1'4+1%C21=&Nr5%211%G2A1%7251&>&I&Dr8r7r6%43321&M+R@%221=%N261+4%Q0221u4&C%11C%@5?:431p0B1p0K1p0O1p0Q:1pR4Q@1pR:Q@1pR6QB1pHQD1").
Proof.
induction k; intros c Hca Hca' Hk Hc; [lia|]. rewrite art_ic_mem_S. rewrite Nat2Z.inj_succ in Hc.
destruct (Z.eq_dec c (Z.of_nat k + 1)) as [->|NE].
- apply cell_Wn_other; [lia|cbn; lia|lia|cbn; lia|unfold apart; cbn; lia|]. apply cell_Wn_hit; [lia|cbn; lia].
- do 2 (apply cell_Wn_other; [lia|cbn; lia|lia|cbn; lia|unfold apart; cbn; lia|]). apply IHk; lia.
Qed.
Lemma cell_ic_size : ltac2:(TCodec.tc2 tcn__JbtInitCache "QL'Q<yR0%211'2y8%511%311p051'9'1&Kzr3%3221&L&Jr4+TP0%3221&O+2+R0%3221%9251'8uO%22:1'4+1%C21=&Nr5%211%G2A1%7251&>&I&Dr8r7r6%43321&M+R@%221=%N261+8%Q0221u8&E%11C%@5?:431p0B1p0K1p0O1p0Q:1pR4Q@1pR:Q@1pR6QB1pHQD1").
Proof.
induction k; intros c Hca Hca' Hk Hc; [lia|]. rewrite art_ic_mem_S. rewrite Nat2Z.inj_succ in Hc.
destruct (Z.eq_dec c (Z.of_nat k + 1)) as [->|NE].
- apply cell_Wn_hit; [lia|cbn; lia].
- do 2 (apply cell_Wn_other; [lia|cbn; lia|lia|cbn; lia|unfold apart; cbn; lia|]). apply IHk; lia.
Qed.
Definition art_ic_kept (r : reg) : Prop := r <> 11%bv /\ r <> 13%bv /\ r <> 15%bv /\ r <> 28%bv /\ r <> 29%bv /\ r <> 30%bv.
Section FPX. Context {fx : PropExec.FPState}.
Section SE.
Local Abbreviation SEC_T_art_ic_it_1 := (ltac2:(TCodec.tc2 tcn__JbtInitCache "U4&:y5'Q<yR0%211%5241'2y8%611%311p061'9'5&Fr4(Q:+;(3%33A21%6251&Q;&Jr1+RH%3221%52F1%>3F71r5+=%>3L1<%A231+Q0%<2M1%E3M31r6+?%E3Q31C%H231+_oooooooooooA%C2Q41%L3Q431r7+@%L3Q:1J%O231%I2Q::%Q23Q:21r8+A%Q23Q@1Q0%Q5231+QP0%Q02QA1%Q93QA31r9+5%Q93QG1Q7%Q<231%Q62QG@%Q?3QG21r:+6%Q?3QM1Q=%QB231%Q<2QM@%QE3QM21r;+7%QE3R31QC%QH231+`0%QC2R41%QL3R431&K+TP0%221E&L%QH2A3&O+2+R0%3221%6251&@&Ir=+Ra0%4432E1'6'4'A&GvQ3r@+Zk`0%R@3RL1R>/01RLr?r>%8576321&<u8u4&M+R@+1%3221%RF2F1+4%RH221&C%116%<4:?31+8%RM271&E%11;%A4@531%K5JS0F1D%M3Q3D1%S;2S2S6+U8%S52Q51%S72SH1%S@3SH41%S@2S7S0%S:2SKQ>%SC3SK21%SC2S:RL+_oooooooooooB%S>2SO1%SG3SO31%T21T3&B%11S@r3r2%SL221rB%SN213%T03T831p071pR>:1%QF2<1%QG2A1%QH2E1%QI2K1qRBT>1%QL2T?1p0QN1p0R41p0R<1p0R@1p0RH1p0RO1p0S61p0S>1p0SE1p0SM1p0T51pR6TE1pRDTG1pHTH1pR@TN1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_ic_it_1) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_ic_it_1) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_ic_it_1) 2%nat 0%nat).
Variable ca : ltac:(sec_ty2 constr:(SEC_T_art_ic_it_1) 3%nat 0%nat).
Lemma art_ic_it_1 : ltac:(sec_stmt2 constr:(SEC_T_art_ic_it_1) 4%nat 0%nat).
Proof using Type regs M rom ca.
intros H11 H13 H15 H16 H17 H5 H6 H7 Hca Hca' W.
eexists. split.
{ zbft (ltac:(oF' 0x56e00%Z)) (ltac:(oD' 0x56e00%Z)).
zstep (ltac:(oF' 0x56e04%Z)) (ltac:(oD' 0x56e04%Z)).
zstep (ltac:(oF' 0x56e08%Z)) (ltac:(oD' 0x56e08%Z)).
zbtk (ltac:(oF' 0x56e0c%Z)) (ltac:(oD' 0x56e0c%Z)).
zstep (ltac:(oF' 0x56e2c%Z)) (ltac:(oD' 0x56e2c%Z)).
zstep (ltac:(oF' 0x56e30%Z)) (ltac:(oD' 0x56e30%Z)).
zbft (ltac:(oF' 0x56e34%Z)) (ltac:(oD' 0x56e34%Z)).
zstep (ltac:(oF' 0x56e38%Z)) (ltac:(oD' 0x56e38%Z)).
stepn (ltac:(oF' 0x56e3c%Z)) (ltac:(oD' 0x56e3c%Z)).
zstep (ltac:(oF' 0x56ddc%Z)) (ltac:(oD' 0x56ddc%Z)).
zstep (ltac:(oF' 0x56de0%Z)) (ltac:(oD' 0x56de0%Z)).
zstep (ltac:(oF' 0x56de4%Z)) (ltac:(oD' 0x56de4%Z)).
zstep (ltac:(oF' 0x56de8%Z)) (ltac:(oD' 0x56de8%Z)).
zstep (ltac:(oF' 0x56dec%Z)) (ltac:(oD' 0x56dec%Z)).
zsw (ltac:(oF' 0x56df0%Z)) (ltac:(oD' 0x56df0%Z)) (ca + 80 * 1 + 4) (art_ic_mc 1) ltac:(rewok W).
zsd (ltac:(oF' 0x56df4%Z)) (ltac:(oD' 0x56df4%Z)) (ca + 80 * 1 + 8) (art_ic_size 1) ltac:(rewok W).
zstep (ltac:(oF' 0x56df8%Z)) (ltac:(oD' 0x56df8%Z)).
zbft (ltac:(oF' 0x56dfc%Z)) (ltac:(oD' 0x56dfc%Z)).
first [apply mst_refl | apply art_msteps_of_eq; apply art_mkst_eq; [reflexivity | zval | reflexivity]]. }
split; [kept_solve|]. split; [kept_solve|]. split; [kept_solve|].
intros r Hr. unfold art_ic_kept in Hr. decompose [and] Hr. kept_solve.
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_art_ic_it_2 := (ltac2:(TCodec.tc2 tcn__JbtInitCache "U3&:y5'Q<yR0%211%5241'2y8%611%311p061'9'5&Fr4(Q:+;(3%33A21%6251&Q;&Jr1+U8%3221%52F1%>3F71r5+=%>3L1<%A231+R0%<2M1%E3M31r6+?%E3Q31C%H231+_oooooooooooB%C2Q41%L3Q431r7+@%L3Q:1J%O231%I2Q::%Q23Q:21r8+A%Q23Q@1Q0%Q5231+QP0%Q02QA1%Q93QA31r9+5%Q93QG1Q7%Q<231%Q62QG@%Q?3QG21r:+6%Q?3QM1Q=%QB231%Q<2QM@%QE3QM21r;+7%QE3R31QC%QH231+`0%QC2R41%QL3R431&K+TP0%221E&L%QH2A3&O+2%221QA%5241&@&Ir=+Ra0%4432D1'6'4'A&GvQ3r@+Zk`0%R?3RK1R=/01RKr?r>%8576321&<u8u4&M+R@%221I%RD2E1+4%RF221&C%11N%;49>31+8%RK271&E%11Q3%@4?531%J5IRNE1C%L3Q2C1%S92S0S4+WH%S32Q41%S52SF1%S>3SF41%S>2S5RN+S0%S92SJ1%SB3SJ31%SB2S9RK+_oooooooooooC%S=2SN1%SF3SN31%T11T2&B%11S?r3r2%SK221rB%SM213%SO3T731p071pR>:1%QF2<1%QG2A1%QH2F1%QI2L1qRBT=1%QL2T>1p0QN1p0R41p0R;1p0R?1p0RG1p0RN1p0S51p0S=1p0SD1p0SL1p0T41pR6TD1pRDTF1pHTG1pR@TM1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_ic_it_2) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_ic_it_2) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_ic_it_2) 2%nat 0%nat).
Variable ca : ltac:(sec_ty2 constr:(SEC_T_art_ic_it_2) 3%nat 0%nat).
Lemma art_ic_it_2 : ltac:(sec_stmt2 constr:(SEC_T_art_ic_it_2) 4%nat 0%nat).
Proof using Type regs M rom ca.
intros H11 H13 H15 H16 H17 H5 H6 H7 Hca Hca' W.
eexists. split.
{ zbft (ltac:(oF' 0x56e00%Z)) (ltac:(oD' 0x56e00%Z)).
zstep (ltac:(oF' 0x56e04%Z)) (ltac:(oD' 0x56e04%Z)).
zstep (ltac:(oF' 0x56e08%Z)) (ltac:(oD' 0x56e08%Z)).
zbtk (ltac:(oF' 0x56e0c%Z)) (ltac:(oD' 0x56e0c%Z)).
zstep (ltac:(oF' 0x56e2c%Z)) (ltac:(oD' 0x56e2c%Z)).
zstep (ltac:(oF' 0x56e30%Z)) (ltac:(oD' 0x56e30%Z)).
zbft (ltac:(oF' 0x56e34%Z)) (ltac:(oD' 0x56e34%Z)).
zstep (ltac:(oF' 0x56e38%Z)) (ltac:(oD' 0x56e38%Z)).
stepn (ltac:(oF' 0x56e3c%Z)) (ltac:(oD' 0x56e3c%Z)).
zstep (ltac:(oF' 0x56ddc%Z)) (ltac:(oD' 0x56ddc%Z)).
zstep (ltac:(oF' 0x56de0%Z)) (ltac:(oD' 0x56de0%Z)).
zstep (ltac:(oF' 0x56de4%Z)) (ltac:(oD' 0x56de4%Z)).
zstep (ltac:(oF' 0x56de8%Z)) (ltac:(oD' 0x56de8%Z)).
zstep (ltac:(oF' 0x56dec%Z)) (ltac:(oD' 0x56dec%Z)).
zsw (ltac:(oF' 0x56df0%Z)) (ltac:(oD' 0x56df0%Z)) (ca + 80 * 2 + 4) (art_ic_mc 2) ltac:(rewok W).
zsd (ltac:(oF' 0x56df4%Z)) (ltac:(oD' 0x56df4%Z)) (ca + 80 * 2 + 8) (art_ic_size 2) ltac:(rewok W).
zstep (ltac:(oF' 0x56df8%Z)) (ltac:(oD' 0x56df8%Z)).
zbft (ltac:(oF' 0x56dfc%Z)) (ltac:(oD' 0x56dfc%Z)).
first [apply mst_refl | apply art_msteps_of_eq; apply art_mkst_eq; [reflexivity | zval | reflexivity]]. }
split; [kept_solve|]. split; [kept_solve|]. split; [kept_solve|].
intros r Hr. unfold art_ic_kept in Hr. decompose [and] Hr. kept_solve.
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_art_ic_it_3 := (ltac2:(TCodec.tc2 tcn__JbtInitCache "U5&:y5'Q<yR0%211%5241'2y8%611%311p061'9'5&Fr4(Q:+;(3%33A21%6251&Q;&Jr1+WH%3221%52F1%>3F71r5+=%>3L1<%A231+S0%<2M1%E3M31r6+?%E3Q31C%H231+_oooooooooooC%C2Q41%L3Q431r7+@%L3Q:1J%O231%I2Q::%Q23Q:21r8+A%Q23Q@1Q0%Q5231+QP0%Q02QA1%Q93QA31r9+5%Q93QG1Q7%Q<231%Q62QG@%Q?3QG21r:+6%Q?3QM1Q=%QB231%Q<2QM@%QE3QM21r;+7%QE3R31QC%QH231+`0%QC2R41%QL3R431&K+TP0%221E&L%QH2A3&O+2+R0%3221%6251&@&Ir=+Ra0%4432E1'6'4'A&GvQ3r@+Zk`0%R@3RL1R>/01RLr?r>%8576321&<u8u4&M+R@+3%3221%RF2F1+4%RH221&C%116%<4:?31+8%RM271&E%11;%A4@531%K5JS0F1D%M3Q3D1%S;2S2S6+Z8%S52Q51%S72SH1%S@3SH41%S@2S7S0+T0%S;2SL1%SD3SL31%SD2S;RM+_oooooooooooD%S?2T01%SH3T031%T31T4&B%11SAr3r2%SM221rB%SO213%T13T931p071pR>:1%QG2<1%QH2A1%QI2F1%QJ2L1qRBT?1%QM2T@1p0QO1p0R51p0R=1p0RA1p0RI1p0S01p0S71p0S?1p0SF1p0SN1p0T61pR6TF1pRDTH1pHTI1pR@TO1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_ic_it_3) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_ic_it_3) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_ic_it_3) 2%nat 0%nat).
Variable ca : ltac:(sec_ty2 constr:(SEC_T_art_ic_it_3) 3%nat 0%nat).
Lemma art_ic_it_3 : ltac:(sec_stmt2 constr:(SEC_T_art_ic_it_3) 4%nat 0%nat).
Proof using Type regs M rom ca.
intros H11 H13 H15 H16 H17 H5 H6 H7 Hca Hca' W.
eexists. split.
{ zbft (ltac:(oF' 0x56e00%Z)) (ltac:(oD' 0x56e00%Z)).
zstep (ltac:(oF' 0x56e04%Z)) (ltac:(oD' 0x56e04%Z)).
zstep (ltac:(oF' 0x56e08%Z)) (ltac:(oD' 0x56e08%Z)).
zbtk (ltac:(oF' 0x56e0c%Z)) (ltac:(oD' 0x56e0c%Z)).
zstep (ltac:(oF' 0x56e2c%Z)) (ltac:(oD' 0x56e2c%Z)).
zstep (ltac:(oF' 0x56e30%Z)) (ltac:(oD' 0x56e30%Z)).
zbft (ltac:(oF' 0x56e34%Z)) (ltac:(oD' 0x56e34%Z)).
zstep (ltac:(oF' 0x56e38%Z)) (ltac:(oD' 0x56e38%Z)).
stepn (ltac:(oF' 0x56e3c%Z)) (ltac:(oD' 0x56e3c%Z)).
zstep (ltac:(oF' 0x56ddc%Z)) (ltac:(oD' 0x56ddc%Z)).
zstep (ltac:(oF' 0x56de0%Z)) (ltac:(oD' 0x56de0%Z)).
zstep (ltac:(oF' 0x56de4%Z)) (ltac:(oD' 0x56de4%Z)).
zstep (ltac:(oF' 0x56de8%Z)) (ltac:(oD' 0x56de8%Z)).
zstep (ltac:(oF' 0x56dec%Z)) (ltac:(oD' 0x56dec%Z)).
zsw (ltac:(oF' 0x56df0%Z)) (ltac:(oD' 0x56df0%Z)) (ca + 80 * 3 + 4) (art_ic_mc 3) ltac:(rewok W).
zsd (ltac:(oF' 0x56df4%Z)) (ltac:(oD' 0x56df4%Z)) (ca + 80 * 3 + 8) (art_ic_size 3) ltac:(rewok W).
zstep (ltac:(oF' 0x56df8%Z)) (ltac:(oD' 0x56df8%Z)).
zbft (ltac:(oF' 0x56dfc%Z)) (ltac:(oD' 0x56dfc%Z)).
first [apply mst_refl | apply art_msteps_of_eq; apply art_mkst_eq; [reflexivity | zval | reflexivity]]. }
split; [kept_solve|]. split; [kept_solve|]. split; [kept_solve|].
intros r Hr. unfold art_ic_kept in Hr. decompose [and] Hr. kept_solve.
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_art_ic_it_4 := (ltac2:(TCodec.tc2 tcn__JbtInitCache "U4&:y5'Q<yR0%211%5241'2y8%611%311p061'9'5&Fr4(Q:+;(3%33A21%6251&Q;&Jr1+Z8%3221%52F1%>3F71r5+=%>3L1<%A231+T0%<2M1%E3M31r6+?%E3Q31C%H231+_oooooooooooD%C2Q41%L3Q431r7+@%L3Q:1J%O231%I2Q::%Q23Q:21r8+A%Q23Q@1Q0%Q5231+QP0%Q02QA1%Q93QA31r9+5%Q93QG1Q7%Q<231%Q62QG@%Q?3QG21r:+6%Q?3QM1Q=%QB231%Q<2QM@%QE3QM21r;+7%QE3R31QC%QH231+`0%QC2R41%QL3R431&K+TP0%221E&L%QH2A3&O+2+R0%3221%6251&@&Ir=+Ra0%4432E1'6'4'A&GvQ3r@+Zk`0%R@3RL1R>/01RLr?r>%8576321&<u8u4&M+R@+4%3221%RF2F1%RG213&C%115%;49>31+8%RL261&E%11:%@4?531%J5IROE1C%L3Q2C1%S:2S1S5+\H%S42Q41%S62SG1%S?3SG41%S?2S6RO+U0%S:2SK1%SC3SK31%SC2S:RL+_oooooooooooE%S>2SO1%SG3SO31%T21T3&B%11S@r3r2%SL221rB%SN213%T03T831p071pR>:1%QF2<1%QG2A1%QH2F1%QI2L1qRBT>1%QL2T?1p0QN1p0R41p0R<1p0R@1p0RH1p0RO1p0S61p0S>1p0SE1p0SM1p0T51pR6TE1pRDTG1pHTH1pR@TN1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_ic_it_4) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_ic_it_4) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_ic_it_4) 2%nat 0%nat).
Variable ca : ltac:(sec_ty2 constr:(SEC_T_art_ic_it_4) 3%nat 0%nat).
Lemma art_ic_it_4 : ltac:(sec_stmt2 constr:(SEC_T_art_ic_it_4) 4%nat 0%nat).
Proof using Type regs M rom ca.
intros H11 H13 H15 H16 H17 H5 H6 H7 Hca Hca' W.
eexists. split.
{ zbft (ltac:(oF' 0x56e00%Z)) (ltac:(oD' 0x56e00%Z)).
zstep (ltac:(oF' 0x56e04%Z)) (ltac:(oD' 0x56e04%Z)).
zstep (ltac:(oF' 0x56e08%Z)) (ltac:(oD' 0x56e08%Z)).
zbtk (ltac:(oF' 0x56e0c%Z)) (ltac:(oD' 0x56e0c%Z)).
zstep (ltac:(oF' 0x56e2c%Z)) (ltac:(oD' 0x56e2c%Z)).
zstep (ltac:(oF' 0x56e30%Z)) (ltac:(oD' 0x56e30%Z)).
zbft (ltac:(oF' 0x56e34%Z)) (ltac:(oD' 0x56e34%Z)).
zstep (ltac:(oF' 0x56e38%Z)) (ltac:(oD' 0x56e38%Z)).
stepn (ltac:(oF' 0x56e3c%Z)) (ltac:(oD' 0x56e3c%Z)).
zstep (ltac:(oF' 0x56ddc%Z)) (ltac:(oD' 0x56ddc%Z)).
zstep (ltac:(oF' 0x56de0%Z)) (ltac:(oD' 0x56de0%Z)).
zstep (ltac:(oF' 0x56de4%Z)) (ltac:(oD' 0x56de4%Z)).
zstep (ltac:(oF' 0x56de8%Z)) (ltac:(oD' 0x56de8%Z)).
zstep (ltac:(oF' 0x56dec%Z)) (ltac:(oD' 0x56dec%Z)).
zsw (ltac:(oF' 0x56df0%Z)) (ltac:(oD' 0x56df0%Z)) (ca + 80 * 4 + 4) (art_ic_mc 4) ltac:(rewok W).
zsd (ltac:(oF' 0x56df4%Z)) (ltac:(oD' 0x56df4%Z)) (ca + 80 * 4 + 8) (art_ic_size 4) ltac:(rewok W).
zstep (ltac:(oF' 0x56df8%Z)) (ltac:(oD' 0x56df8%Z)).
zbft (ltac:(oF' 0x56dfc%Z)) (ltac:(oD' 0x56dfc%Z)).
first [apply mst_refl | apply art_msteps_of_eq; apply art_mkst_eq; [reflexivity | zval | reflexivity]]. }
split; [kept_solve|]. split; [kept_solve|]. split; [kept_solve|].
intros r Hr. unfold art_ic_kept in Hr. decompose [and] Hr. kept_solve.
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_art_ic_it_5 := (ltac2:(TCodec.tc2 tcn__JbtInitCache "U4&:y5'Q<yR0%211%5241'2y8%611%311p061'9'5&Fr4(Q:+;(3%33A21%6251&Q;&Jr1+\H%3221%52F1%>3F71r5+=%>3L1<%A231+U0%<2M1%E3M31r6+?%E3Q31C%H231+_oooooooooooE%C2Q41%L3Q431r7+@%L3Q:1J%O231%I2Q::%Q23Q:21r8+A%Q23Q@1Q0%Q5231+QP0%Q02QA1%Q93QA31r9+5%Q93QG1Q7%Q<231%Q62QG@%Q?3QG21r:+6%Q?3QM1Q=%QB231%Q<2QM@%QE3QM21r;+7%QE3R31QC%QH231+`0%QC2R41%QL3R431&K+TP0%221E&L%QH2A3&O+2+R0%3221%6251&@&Ir=+Ra0%4432E1'6'4'A&GvQ3r@+Zk`0%R@3RL1R>/01RLr?r>%8576321&<u8u4&M+R@%221QB%RE2E1+4%RG221&C%11QG%;49>31+8%RL271&E%11QL%@4?531%J5IROE1C%L3Q2C1%S:2S1S5+_8%S42Q41%S62SG1%S?3SG41%S?2S6RO+V0%S:2SK1%SC3SK31%SC2S:RL+_oooooooooooF%S>2SO1%SG3SO31%T21T3&B%11S@r3r2%SL221rB%SN213%T03T831p071pR>:1%QF2<1%QG2A1%QH2F1%QI2L1qRBT>1%QL2T?1p0QN1p0R41p0R<1p0R@1p0RH1p0RO1p0S61p0S>1p0SE1p0SM1p0T51pR6TE1pRDTG1pHTH1pR@TN1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_ic_it_5) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_ic_it_5) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_ic_it_5) 2%nat 0%nat).
Variable ca : ltac:(sec_ty2 constr:(SEC_T_art_ic_it_5) 3%nat 0%nat).
Lemma art_ic_it_5 : ltac:(sec_stmt2 constr:(SEC_T_art_ic_it_5) 4%nat 0%nat).
Proof using Type regs M rom ca.
intros H11 H13 H15 H16 H17 H5 H6 H7 Hca Hca' W.
eexists. split.
{ zbft (ltac:(oF' 0x56e00%Z)) (ltac:(oD' 0x56e00%Z)).
zstep (ltac:(oF' 0x56e04%Z)) (ltac:(oD' 0x56e04%Z)).
zstep (ltac:(oF' 0x56e08%Z)) (ltac:(oD' 0x56e08%Z)).
zbtk (ltac:(oF' 0x56e0c%Z)) (ltac:(oD' 0x56e0c%Z)).
zstep (ltac:(oF' 0x56e2c%Z)) (ltac:(oD' 0x56e2c%Z)).
zstep (ltac:(oF' 0x56e30%Z)) (ltac:(oD' 0x56e30%Z)).
zbtk (ltac:(oF' 0x56e34%Z)) (ltac:(oD' 0x56e34%Z)).
zstep (ltac:(oF' 0x56ddc%Z)) (ltac:(oD' 0x56ddc%Z)).
zstep (ltac:(oF' 0x56de0%Z)) (ltac:(oD' 0x56de0%Z)).
zstep (ltac:(oF' 0x56de4%Z)) (ltac:(oD' 0x56de4%Z)).
zstep (ltac:(oF' 0x56de8%Z)) (ltac:(oD' 0x56de8%Z)).
zstep (ltac:(oF' 0x56dec%Z)) (ltac:(oD' 0x56dec%Z)).
zsw (ltac:(oF' 0x56df0%Z)) (ltac:(oD' 0x56df0%Z)) (ca + 80 * 5 + 4) (art_ic_mc 5) ltac:(rewok W).
zsd (ltac:(oF' 0x56df4%Z)) (ltac:(oD' 0x56df4%Z)) (ca + 80 * 5 + 8) (art_ic_size 5) ltac:(rewok W).
zstep (ltac:(oF' 0x56df8%Z)) (ltac:(oD' 0x56df8%Z)).
zbft (ltac:(oF' 0x56dfc%Z)) (ltac:(oD' 0x56dfc%Z)).
first [apply mst_refl | apply art_msteps_of_eq; apply art_mkst_eq; [reflexivity | zval | reflexivity]]. }
split; [kept_solve|]. split; [kept_solve|]. split; [kept_solve|].
intros r Hr. unfold art_ic_kept in Hr. decompose [and] Hr. kept_solve.
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_art_ic_it_6 := (ltac2:(TCodec.tc2 tcn__JbtInitCache "U4&:y5'Q<yR0%211%5241'2y8%611%311p061'9'5&Fr4(Q:+;(3%33A21%6251&Q;&Jr1+_8%3221%52F1%>3F71r5+=%>3L1<%A231+V0%<2M1%E3M31r6+?%E3Q31C%H231+_oooooooooooF%C2Q41%L3Q431r7+@%L3Q:1J%O231%I2Q::%Q23Q:21r8+A%Q23Q@1Q0%Q5231+QP0%Q02QA1%Q93QA31r9+5%Q93QG1Q7%Q<231%Q62QG@%Q?3QG21r:+6%Q?3QM1Q=%QB231%Q<2QM@%QE3QM21r;+7%QE3R31QC%QH231+`0%QC2R41%QL3R431&K+TP0%221E&L%QH2A3&O+2+R0%3221%6251&@&Ir=+Ra0%4432E1'6'4'A&GvQ3r@+Zk`0%R@3RL1R>/01RLr?r>%8576321&<u8u4&M+R@%221Q<%RE2E1+4%RG221&C%11QA%;49>31+8%RL271&E%11QF%@4?531%J5IROE1C%L3Q2C1%S:2S1S5+aH%S42Q41%S62SG1%S?3SG41%S?2S6RO+W0%S:2SK1%SC3SK31%SC2S:RL+_oooooooooooG%S>2SO1%SG3SO31%T21T3&B%11S@r3r2%SL221rB%SN213%T03T831p071pR>:1%QF2<1%QG2A1%QH2F1%QI2L1qRBT>1%QL2T?1p0QN1p0R41p0R<1p0R@1p0RH1p0RO1p0S61p0S>1p0SE1p0SM1p0T51pR6TE1pRDTG1pHTH1pR@TN1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_ic_it_6) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_ic_it_6) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_ic_it_6) 2%nat 0%nat).
Variable ca : ltac:(sec_ty2 constr:(SEC_T_art_ic_it_6) 3%nat 0%nat).
Lemma art_ic_it_6 : ltac:(sec_stmt2 constr:(SEC_T_art_ic_it_6) 4%nat 0%nat).
Proof using Type regs M rom ca.
intros H11 H13 H15 H16 H17 H5 H6 H7 Hca Hca' W.
eexists. split.
{ zbft (ltac:(oF' 0x56e00%Z)) (ltac:(oD' 0x56e00%Z)).
zstep (ltac:(oF' 0x56e04%Z)) (ltac:(oD' 0x56e04%Z)).
zstep (ltac:(oF' 0x56e08%Z)) (ltac:(oD' 0x56e08%Z)).
zbtk (ltac:(oF' 0x56e0c%Z)) (ltac:(oD' 0x56e0c%Z)).
zstep (ltac:(oF' 0x56e2c%Z)) (ltac:(oD' 0x56e2c%Z)).
zstep (ltac:(oF' 0x56e30%Z)) (ltac:(oD' 0x56e30%Z)).
zbtk (ltac:(oF' 0x56e34%Z)) (ltac:(oD' 0x56e34%Z)).
zstep (ltac:(oF' 0x56ddc%Z)) (ltac:(oD' 0x56ddc%Z)).
zstep (ltac:(oF' 0x56de0%Z)) (ltac:(oD' 0x56de0%Z)).
zstep (ltac:(oF' 0x56de4%Z)) (ltac:(oD' 0x56de4%Z)).
zstep (ltac:(oF' 0x56de8%Z)) (ltac:(oD' 0x56de8%Z)).
zstep (ltac:(oF' 0x56dec%Z)) (ltac:(oD' 0x56dec%Z)).
zsw (ltac:(oF' 0x56df0%Z)) (ltac:(oD' 0x56df0%Z)) (ca + 80 * 6 + 4) (art_ic_mc 6) ltac:(rewok W).
zsd (ltac:(oF' 0x56df4%Z)) (ltac:(oD' 0x56df4%Z)) (ca + 80 * 6 + 8) (art_ic_size 6) ltac:(rewok W).
zstep (ltac:(oF' 0x56df8%Z)) (ltac:(oD' 0x56df8%Z)).
zbft (ltac:(oF' 0x56dfc%Z)) (ltac:(oD' 0x56dfc%Z)).
first [apply mst_refl | apply art_msteps_of_eq; apply art_mkst_eq; [reflexivity | zval | reflexivity]]. }
split; [kept_solve|]. split; [kept_solve|]. split; [kept_solve|].
intros r Hr. unfold art_ic_kept in Hr. decompose [and] Hr. kept_solve.
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_art_ic_it_7 := (ltac2:(TCodec.tc2 tcn__JbtInitCache "U4&:y5'Q<yR0%211%5241'2y8%611%311p061'9'5&Fr4(Q:+;(3%33A21%6251&Q;&Jr1+aH%3221%52F1%>3F71r5+=%>3L1<%A231+W0%<2M1%E3M31r6+?%E3Q31C%H231+_oooooooooooG%C2Q41%L3Q431r7+@%L3Q:1J%O231%I2Q::%Q23Q:21r8+A%Q23Q@1Q0%Q5231+QP0%Q02QA1%Q93QA31r9+5%Q93QG1Q7%Q<231%Q62QG@%Q?3QG21r:+6%Q?3QM1Q=%QB231%Q<2QM@%QE3QM21r;+7%QE3R31QC%QH231+`0%QC2R41%QL3R431&K+TP0%221E&L%QH2A3&O+2+R0%3221%6251&@&Ir=+Ra0%4432E1'6'4'A&GvQ3r@+Zk`0%R@3RL1R>/01RLr?r>%8576321&<u8u4&M+R@%221Q6%RE2E1+4%RG221&C%11Q;%;49>31+8%RL271&E%11Q@%@4?531%J5IROE1C%L3Q2C1%S:2S1S5+d8%S42Q41%S62SG1%S?3SG41%S?2S6RO+X0%S:2SK1%SC3SK31%SC2S:RL+_oooooooooooH%S>2SO1%SG3SO31%T21T3&B%11S@r3r2%SL221rB%SN213%T03T831p071pR>:1%QF2<1%QG2A1%QH2F1%QI2L1qRBT>1%QL2T?1p0QN1p0R41p0R<1p0R@1p0RH1p0RO1p0S61p0S>1p0SE1p0SM1p0T51pR6TE1pRDTG1pHTH1pR@TN1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_ic_it_7) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_ic_it_7) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_ic_it_7) 2%nat 0%nat).
Variable ca : ltac:(sec_ty2 constr:(SEC_T_art_ic_it_7) 3%nat 0%nat).
Lemma art_ic_it_7 : ltac:(sec_stmt2 constr:(SEC_T_art_ic_it_7) 4%nat 0%nat).
Proof using Type regs M rom ca.
intros H11 H13 H15 H16 H17 H5 H6 H7 Hca Hca' W.
eexists. split.
{ zbft (ltac:(oF' 0x56e00%Z)) (ltac:(oD' 0x56e00%Z)).
zstep (ltac:(oF' 0x56e04%Z)) (ltac:(oD' 0x56e04%Z)).
zstep (ltac:(oF' 0x56e08%Z)) (ltac:(oD' 0x56e08%Z)).
zbtk (ltac:(oF' 0x56e0c%Z)) (ltac:(oD' 0x56e0c%Z)).
zstep (ltac:(oF' 0x56e2c%Z)) (ltac:(oD' 0x56e2c%Z)).
zstep (ltac:(oF' 0x56e30%Z)) (ltac:(oD' 0x56e30%Z)).
zbtk (ltac:(oF' 0x56e34%Z)) (ltac:(oD' 0x56e34%Z)).
zstep (ltac:(oF' 0x56ddc%Z)) (ltac:(oD' 0x56ddc%Z)).
zstep (ltac:(oF' 0x56de0%Z)) (ltac:(oD' 0x56de0%Z)).
zstep (ltac:(oF' 0x56de4%Z)) (ltac:(oD' 0x56de4%Z)).
zstep (ltac:(oF' 0x56de8%Z)) (ltac:(oD' 0x56de8%Z)).
zstep (ltac:(oF' 0x56dec%Z)) (ltac:(oD' 0x56dec%Z)).
zsw (ltac:(oF' 0x56df0%Z)) (ltac:(oD' 0x56df0%Z)) (ca + 80 * 7 + 4) (art_ic_mc 7) ltac:(rewok W).
zsd (ltac:(oF' 0x56df4%Z)) (ltac:(oD' 0x56df4%Z)) (ca + 80 * 7 + 8) (art_ic_size 7) ltac:(rewok W).
zstep (ltac:(oF' 0x56df8%Z)) (ltac:(oD' 0x56df8%Z)).
zbft (ltac:(oF' 0x56dfc%Z)) (ltac:(oD' 0x56dfc%Z)).
first [apply mst_refl | apply art_msteps_of_eq; apply art_mkst_eq; [reflexivity | zval | reflexivity]]. }
split; [kept_solve|]. split; [kept_solve|]. split; [kept_solve|].
intros r Hr. unfold art_ic_kept in Hr. decompose [and] Hr. kept_solve.
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_art_ic_it_8 := (ltac2:(TCodec.tc2 tcn__JbtInitCache "U4&:y5'Q<yR0%211%5241'2y8%611%311p061'9'5&Fr4(Q:+;(3%33A21%6251&Q;&Jr1+d8%3221%52F1%>3F71r5+=%>3L1<%A231+X0%<2M1%E3M31r6+?%E3Q31C%H231+_oooooooooooH%C2Q41%L3Q431r7+@%L3Q:1J%O231%I2Q::%Q23Q:21r8+A%Q23Q@1Q0%Q5231+QP0%Q02QA1%Q93QA31r9+5%Q93QG1Q7%Q<231%Q62QG@%Q?3QG21r:+6%Q?3QM1Q=%QB231%Q<2QM@%QE3QM21r;+7%QE3R31QC%QH231+`0%QC2R41%QL3R431&K+TP0%221E&L%QH2A3&O+2+R0%3221%6251&@&Ir=+Ra0%4432E1'6'4'A&GvQ3r@+Zk`0%R@3RL1R>/01RLr?r>%8576321&<u8u4&M+R@+8%3221%RF2F1+4%RH221&C%116%<4:?31%RL268&E%11:%@4?431%J5IROE1C%L3Q2C1%S:2S1S5+fH%S42Q41%S62SG1%S?3SG41%S?2S6RO+Y0%S:2SK1%SC3SK31%SC2S:RL+_oooooooooooI%S>2SO1%SG3SO31%T21T3&B%11S@r3r2%SL221rB%SN213%T03T831p071pR>:1%QF2<1%QG2A1%QH2F1%QI2L1qRBT>1%QL2T?1p0QN1p0R41p0R<1p0R@1p0RH1p0RO1p0S61p0S>1p0SE1p0SM1p0T51pR6TE1pRDTG1pHTH1pR@TN1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_ic_it_8) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_ic_it_8) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_ic_it_8) 2%nat 0%nat).
Variable ca : ltac:(sec_ty2 constr:(SEC_T_art_ic_it_8) 3%nat 0%nat).
Lemma art_ic_it_8 : ltac:(sec_stmt2 constr:(SEC_T_art_ic_it_8) 4%nat 0%nat).
Proof using Type regs M rom ca.
intros H11 H13 H15 H16 H17 H5 H6 H7 Hca Hca' W.
eexists. split.
{ zbft (ltac:(oF' 0x56e00%Z)) (ltac:(oD' 0x56e00%Z)).
zstep (ltac:(oF' 0x56e04%Z)) (ltac:(oD' 0x56e04%Z)).
zstep (ltac:(oF' 0x56e08%Z)) (ltac:(oD' 0x56e08%Z)).
zbtk (ltac:(oF' 0x56e0c%Z)) (ltac:(oD' 0x56e0c%Z)).
zstep (ltac:(oF' 0x56e2c%Z)) (ltac:(oD' 0x56e2c%Z)).
zstep (ltac:(oF' 0x56e30%Z)) (ltac:(oD' 0x56e30%Z)).
zbtk (ltac:(oF' 0x56e34%Z)) (ltac:(oD' 0x56e34%Z)).
zstep (ltac:(oF' 0x56ddc%Z)) (ltac:(oD' 0x56ddc%Z)).
zstep (ltac:(oF' 0x56de0%Z)) (ltac:(oD' 0x56de0%Z)).
zstep (ltac:(oF' 0x56de4%Z)) (ltac:(oD' 0x56de4%Z)).
zstep (ltac:(oF' 0x56de8%Z)) (ltac:(oD' 0x56de8%Z)).
zstep (ltac:(oF' 0x56dec%Z)) (ltac:(oD' 0x56dec%Z)).
zsw (ltac:(oF' 0x56df0%Z)) (ltac:(oD' 0x56df0%Z)) (ca + 80 * 8 + 4) (art_ic_mc 8) ltac:(rewok W).
zsd (ltac:(oF' 0x56df4%Z)) (ltac:(oD' 0x56df4%Z)) (ca + 80 * 8 + 8) (art_ic_size 8) ltac:(rewok W).
zstep (ltac:(oF' 0x56df8%Z)) (ltac:(oD' 0x56df8%Z)).
zbft (ltac:(oF' 0x56dfc%Z)) (ltac:(oD' 0x56dfc%Z)).
first [apply mst_refl | apply art_msteps_of_eq; apply art_mkst_eq; [reflexivity | zval | reflexivity]]. }
split; [kept_solve|]. split; [kept_solve|]. split; [kept_solve|].
intros r Hr. unfold art_ic_kept in Hr. decompose [and] Hr. kept_solve.
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_art_ic_it_9 := (ltac2:(TCodec.tc2 tcn__JbtInitCache "U5&:y5'Q<yR0%211%5241'2y8%611%311p061'9'5&Fr4(Q:+;(3%33A21%6251&Q;&Jr1+fH%3221%52F1%>3F71r5+=%>3L1<%A231+Y0%<2M1%E3M31r6+?%E3Q31C%H231+_oooooooooooI%C2Q41%L3Q431r7+@%L3Q:1J%O231%I2Q::%Q23Q:21r8+A%Q23Q@1Q0%Q5231+QP0%Q02QA1%Q93QA31r9+5%Q93QG1Q7%Q<231%Q62QG@%Q?3QG21r:+6%Q?3QM1Q=%QB231%Q<2QM@%QE3QM21r;+7%QE3R31QC%QH231+`0%QC2R41%QL3R431&K+TP0%221E&L%QH2A3&O+2+R0%3221%6251&@&Ir=+Ra0%4432E1'6'4'A&GvQ3r@+Zk`0%R@3RL1R>/01RLr?r>%8576321&<u8u4&M+R@+9%3221%RF2F1+4%RH221&C%116%<4:?31+8%RM271&E%11;%A4@531%K5JS0F1D%M3Q3D1%S;2S2S6+i8%S52Q51%S72SH1%S@3SH41%S@2S7S0+Z0%S;2SL1%SD3SL31%SD2S;RM+_oooooooooooJ%S?2T01%SH3T031%T31T4&B%11SAr3r2%SM221rB%SO213%T13T931p071pR>:1%QG2<1%QH2A1%QI2F1%QJ2L1qRBT?1%QM2T@1p0QO1p0R51p0R=1p0RA1p0RI1p0S01p0S71p0S?1p0SF1p0SN1p0T61pR6TF1pRDTH1pHTI1pR@TO1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_ic_it_9) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_ic_it_9) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_ic_it_9) 2%nat 0%nat).
Variable ca : ltac:(sec_ty2 constr:(SEC_T_art_ic_it_9) 3%nat 0%nat).
Lemma art_ic_it_9 : ltac:(sec_stmt2 constr:(SEC_T_art_ic_it_9) 4%nat 0%nat).
Proof using Type regs M rom ca.
intros H11 H13 H15 H16 H17 H5 H6 H7 Hca Hca' W.
eexists. split.
{ zbft (ltac:(oF' 0x56e00%Z)) (ltac:(oD' 0x56e00%Z)).
zstep (ltac:(oF' 0x56e04%Z)) (ltac:(oD' 0x56e04%Z)).
zstep (ltac:(oF' 0x56e08%Z)) (ltac:(oD' 0x56e08%Z)).
zbtk (ltac:(oF' 0x56e0c%Z)) (ltac:(oD' 0x56e0c%Z)).
zstep (ltac:(oF' 0x56e2c%Z)) (ltac:(oD' 0x56e2c%Z)).
zstep (ltac:(oF' 0x56e30%Z)) (ltac:(oD' 0x56e30%Z)).
zbtk (ltac:(oF' 0x56e34%Z)) (ltac:(oD' 0x56e34%Z)).
zstep (ltac:(oF' 0x56ddc%Z)) (ltac:(oD' 0x56ddc%Z)).
zstep (ltac:(oF' 0x56de0%Z)) (ltac:(oD' 0x56de0%Z)).
zstep (ltac:(oF' 0x56de4%Z)) (ltac:(oD' 0x56de4%Z)).
zstep (ltac:(oF' 0x56de8%Z)) (ltac:(oD' 0x56de8%Z)).
zstep (ltac:(oF' 0x56dec%Z)) (ltac:(oD' 0x56dec%Z)).
zsw (ltac:(oF' 0x56df0%Z)) (ltac:(oD' 0x56df0%Z)) (ca + 80 * 9 + 4) (art_ic_mc 9) ltac:(rewok W).
zsd (ltac:(oF' 0x56df4%Z)) (ltac:(oD' 0x56df4%Z)) (ca + 80 * 9 + 8) (art_ic_size 9) ltac:(rewok W).
zstep (ltac:(oF' 0x56df8%Z)) (ltac:(oD' 0x56df8%Z)).
zbft (ltac:(oF' 0x56dfc%Z)) (ltac:(oD' 0x56dfc%Z)).
first [apply mst_refl | apply art_msteps_of_eq; apply art_mkst_eq; [reflexivity | zval | reflexivity]]. }
split; [kept_solve|]. split; [kept_solve|]. split; [kept_solve|].
intros r Hr. unfold art_ic_kept in Hr. decompose [and] Hr. kept_solve.
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_art_ic_it_10 := (ltac2:(TCodec.tc2 tcn__JbtInitCache "U5&:y5'Q<yR0%211%5241'2y8%611%311p061'9'5&Fr4(Q:+;(3%33A21%6251&Q;&Jr1+i8%3221%52F1%>3F71r5+=%>3L1<%A231+Z0%<2M1%E3M31r6+?%E3Q31C%H231+_oooooooooooJ%C2Q41%L3Q431r7+@%L3Q:1J%O231%I2Q::%Q23Q:21r8+A%Q23Q@1Q0%Q5231+QP0%Q02QA1%Q93QA31r9+5%Q93QG1Q7%Q<231%Q62QG@%Q?3QG21r:+6%Q?3QM1Q=%QB231%Q<2QM@%QE3QM21r;+7%QE3R31QC%QH231+`0%QC2R41%QL3R431&K+TP0%221E&L%QH2A3&O+2+R0%3221%6251&@&Ir=+Ra0%4432E1'6'4'A&GvQ3r@+Zk`0%R@3RL1R>/01RLr?r>%8576321&<u8u4&M+R@+:%3221%RF2F1+4%RH221&C%116%<4:?31+8%RM271&E%11;%A4@531%K5JS0F1D%M3Q3D1%S;2S2S6+kH%S52Q51%S72SH1%S@3SH41%S@2S7S0+[0%S;2SL1%SD3SL31%SD2S;RM+_oooooooooooK%S?2T01%SH3T031%T31T4&B%11SAr3r2%SM221rB%SO213%T13T931p071pR>:1%QG2<1%QH2A1%QI2F1%QJ2L1qRBT?1%QM2T@1p0QO1p0R51p0R=1p0RA1p0RI1p0S01p0S71p0S?1p0SF1p0SN1p0T61pR6TF1pRDTH1pHTI1pR@TO1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_ic_it_10) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_ic_it_10) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_ic_it_10) 2%nat 0%nat).
Variable ca : ltac:(sec_ty2 constr:(SEC_T_art_ic_it_10) 3%nat 0%nat).
Lemma art_ic_it_10 : ltac:(sec_stmt2 constr:(SEC_T_art_ic_it_10) 4%nat 0%nat).
Proof using Type regs M rom ca.
intros H11 H13 H15 H16 H17 H5 H6 H7 Hca Hca' W.
eexists. split.
{ zbft (ltac:(oF' 0x56e00%Z)) (ltac:(oD' 0x56e00%Z)).
zstep (ltac:(oF' 0x56e04%Z)) (ltac:(oD' 0x56e04%Z)).
zstep (ltac:(oF' 0x56e08%Z)) (ltac:(oD' 0x56e08%Z)).
zbtk (ltac:(oF' 0x56e0c%Z)) (ltac:(oD' 0x56e0c%Z)).
zstep (ltac:(oF' 0x56e2c%Z)) (ltac:(oD' 0x56e2c%Z)).
zstep (ltac:(oF' 0x56e30%Z)) (ltac:(oD' 0x56e30%Z)).
zbtk (ltac:(oF' 0x56e34%Z)) (ltac:(oD' 0x56e34%Z)).
zstep (ltac:(oF' 0x56ddc%Z)) (ltac:(oD' 0x56ddc%Z)).
zstep (ltac:(oF' 0x56de0%Z)) (ltac:(oD' 0x56de0%Z)).
zstep (ltac:(oF' 0x56de4%Z)) (ltac:(oD' 0x56de4%Z)).
zstep (ltac:(oF' 0x56de8%Z)) (ltac:(oD' 0x56de8%Z)).
zstep (ltac:(oF' 0x56dec%Z)) (ltac:(oD' 0x56dec%Z)).
zsw (ltac:(oF' 0x56df0%Z)) (ltac:(oD' 0x56df0%Z)) (ca + 80 * 10 + 4) (art_ic_mc 10) ltac:(rewok W).
zsd (ltac:(oF' 0x56df4%Z)) (ltac:(oD' 0x56df4%Z)) (ca + 80 * 10 + 8) (art_ic_size 10) ltac:(rewok W).
zstep (ltac:(oF' 0x56df8%Z)) (ltac:(oD' 0x56df8%Z)).
zbft (ltac:(oF' 0x56dfc%Z)) (ltac:(oD' 0x56dfc%Z)).
first [apply mst_refl | apply art_msteps_of_eq; apply art_mkst_eq; [reflexivity | zval | reflexivity]]. }
split; [kept_solve|]. split; [kept_solve|]. split; [kept_solve|].
intros r Hr. unfold art_ic_kept in Hr. decompose [and] Hr. kept_solve.
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_art_ic_it_11 := (ltac2:(TCodec.tc2 tcn__JbtInitCache "U4&:y5'Q<yR0%211%5241'2y8%611%311p061'9'5&Fr4(Q:+;(3%33A21%6251&Q;&Jr1+kH%3221%52F1%>3F71r5+=%>3L1<%A231+[0%<2M1%E3M31r6+?%E3Q31C%H231+_oooooooooooK%C2Q41%L3Q431r7+@%L3Q:1J%O231%I2Q::%Q23Q:21r8+A%Q23Q@1Q0%Q5231+QP0%Q02QA1%Q93QA31r9+5%Q93QG1Q7%Q<231%Q62QG@%Q?3QG21r:+6%Q?3QM1Q=%QB231%Q<2QM@%QE3QM21r;+7%QE3R31QC%QH231+`0%QC2R41%QL3R431&K+TP0%221E&L%QH2A3&O+2+R0%3221%6251&@&Ir=+Ra0%4432E1'6'4'A&GvQ3r@+Zk`0%R@3RL1R>/01RLr?r>%8576321&<u8u4&M+R@%221RI%RE2E1+4%RG221&C%11RN%;49>31+8%RL271&E%11S3%@4?531%J5IROE1C%L3Q2C1%S:2S1S5+n8%S42Q41%S62SG1%S?3SG41%S?2S6RO+\0%S:2SK1%SC3SK31%SC2S:RL+_oooooooooooL%S>2SO1%SG3SO31%T21T3&B%11S@r3r2%SL221rB%SN213%T03T831p071pR>:1%QF2<1%QG2A1%QH2F1%QI2L1qRBT>1%QL2T?1p0QN1p0R41p0R<1p0R@1p0RH1p0RO1p0S61p0S>1p0SE1p0SM1p0T51pR6TE1pRDTG1pHTH1pR@TN1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_ic_it_11) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_ic_it_11) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_ic_it_11) 2%nat 0%nat).
Variable ca : ltac:(sec_ty2 constr:(SEC_T_art_ic_it_11) 3%nat 0%nat).
Lemma art_ic_it_11 : ltac:(sec_stmt2 constr:(SEC_T_art_ic_it_11) 4%nat 0%nat).
Proof using Type regs M rom ca.
intros H11 H13 H15 H16 H17 H5 H6 H7 Hca Hca' W.
eexists. split.
{ zbft (ltac:(oF' 0x56e00%Z)) (ltac:(oD' 0x56e00%Z)).
zstep (ltac:(oF' 0x56e04%Z)) (ltac:(oD' 0x56e04%Z)).
zstep (ltac:(oF' 0x56e08%Z)) (ltac:(oD' 0x56e08%Z)).
zbtk (ltac:(oF' 0x56e0c%Z)) (ltac:(oD' 0x56e0c%Z)).
zstep (ltac:(oF' 0x56e2c%Z)) (ltac:(oD' 0x56e2c%Z)).
zstep (ltac:(oF' 0x56e30%Z)) (ltac:(oD' 0x56e30%Z)).
zbtk (ltac:(oF' 0x56e34%Z)) (ltac:(oD' 0x56e34%Z)).
zstep (ltac:(oF' 0x56ddc%Z)) (ltac:(oD' 0x56ddc%Z)).
zstep (ltac:(oF' 0x56de0%Z)) (ltac:(oD' 0x56de0%Z)).
zstep (ltac:(oF' 0x56de4%Z)) (ltac:(oD' 0x56de4%Z)).
zstep (ltac:(oF' 0x56de8%Z)) (ltac:(oD' 0x56de8%Z)).
zstep (ltac:(oF' 0x56dec%Z)) (ltac:(oD' 0x56dec%Z)).
zsw (ltac:(oF' 0x56df0%Z)) (ltac:(oD' 0x56df0%Z)) (ca + 80 * 11 + 4) (art_ic_mc 11) ltac:(rewok W).
zsd (ltac:(oF' 0x56df4%Z)) (ltac:(oD' 0x56df4%Z)) (ca + 80 * 11 + 8) (art_ic_size 11) ltac:(rewok W).
zstep (ltac:(oF' 0x56df8%Z)) (ltac:(oD' 0x56df8%Z)).
zbft (ltac:(oF' 0x56dfc%Z)) (ltac:(oD' 0x56dfc%Z)).
first [apply mst_refl | apply art_msteps_of_eq; apply art_mkst_eq; [reflexivity | zval | reflexivity]]. }
split; [kept_solve|]. split; [kept_solve|]. split; [kept_solve|].
intros r Hr. unfold art_ic_kept in Hr. decompose [and] Hr. kept_solve.
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_art_ic_it_12 := (ltac2:(TCodec.tc2 tcn__JbtInitCache "U5&:y5'Q<yR0%211%5241'2y8%611%311p061'9'5&Fr4(Q:+;(3%33A21%6251&Q;&Jr1+n8%3221%52F1%>3F71r5+=%>3L1<%A231+\0%<2M1%E3M31r6+?%E3Q31C%H231+_oooooooooooL%C2Q41%L3Q431r7+@%L3Q:1J%O231%I2Q::%Q23Q:21r8+A%Q23Q@1Q0%Q5231+QP0%Q02QA1%Q93QA31r9+5%Q93QG1Q7%Q<231%Q62QG@%Q?3QG21r:+6%Q?3QM1Q=%QB231%Q<2QM@%QE3QM21r;+7%QE3R31QC%QH231+`0%QC2R41%QL3R431&K+TP0%221E&L%QH2A3&O+2+R0%3221%6251&@&Ir=+Ra0%4432E1'6'4'A&GvQ3r@+Zk`0%R@3RL1R>/01RLr?r>%8576321&<u8u4&M+R@+<%3221%RF2F1+4%RH221&C%116%<4:?31+8%RM271&E%11;%A4@531%K5JS0F1D%M3Q3D1%S;2S2S6+QPH%S52Q51%S72SH1%S@3SH41%S@2S7S0+]0%S;2SL1%SD3SL31%SD2S;RM+_oooooooooooM%S?2T01%SH3T031%T31T4&B%11SAr3r2%SM221rB%SO213%T13T931p071pR>:1%QG2<1%QH2A1%QI2F1%QJ2L1qRBT?1%QM2T@1p0QO1p0R51p0R=1p0RA1p0RI1p0S01p0S71p0S?1p0SF1p0SN1p0T61pR6TF1pRDTH1pHTI1pR@TO1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_ic_it_12) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_ic_it_12) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_ic_it_12) 2%nat 0%nat).
Variable ca : ltac:(sec_ty2 constr:(SEC_T_art_ic_it_12) 3%nat 0%nat).
Lemma art_ic_it_12 : ltac:(sec_stmt2 constr:(SEC_T_art_ic_it_12) 4%nat 0%nat).
Proof using Type regs M rom ca.
intros H11 H13 H15 H16 H17 H5 H6 H7 Hca Hca' W.
eexists. split.
{ zbft (ltac:(oF' 0x56e00%Z)) (ltac:(oD' 0x56e00%Z)).
zstep (ltac:(oF' 0x56e04%Z)) (ltac:(oD' 0x56e04%Z)).
zstep (ltac:(oF' 0x56e08%Z)) (ltac:(oD' 0x56e08%Z)).
zbtk (ltac:(oF' 0x56e0c%Z)) (ltac:(oD' 0x56e0c%Z)).
zstep (ltac:(oF' 0x56e2c%Z)) (ltac:(oD' 0x56e2c%Z)).
zstep (ltac:(oF' 0x56e30%Z)) (ltac:(oD' 0x56e30%Z)).
zbtk (ltac:(oF' 0x56e34%Z)) (ltac:(oD' 0x56e34%Z)).
zstep (ltac:(oF' 0x56ddc%Z)) (ltac:(oD' 0x56ddc%Z)).
zstep (ltac:(oF' 0x56de0%Z)) (ltac:(oD' 0x56de0%Z)).
zstep (ltac:(oF' 0x56de4%Z)) (ltac:(oD' 0x56de4%Z)).
zstep (ltac:(oF' 0x56de8%Z)) (ltac:(oD' 0x56de8%Z)).
zstep (ltac:(oF' 0x56dec%Z)) (ltac:(oD' 0x56dec%Z)).
zsw (ltac:(oF' 0x56df0%Z)) (ltac:(oD' 0x56df0%Z)) (ca + 80 * 12 + 4) (art_ic_mc 12) ltac:(rewok W).
zsd (ltac:(oF' 0x56df4%Z)) (ltac:(oD' 0x56df4%Z)) (ca + 80 * 12 + 8) (art_ic_size 12) ltac:(rewok W).
zstep (ltac:(oF' 0x56df8%Z)) (ltac:(oD' 0x56df8%Z)).
zbft (ltac:(oF' 0x56dfc%Z)) (ltac:(oD' 0x56dfc%Z)).
first [apply mst_refl | apply art_msteps_of_eq; apply art_mkst_eq; [reflexivity | zval | reflexivity]]. }
split; [kept_solve|]. split; [kept_solve|]. split; [kept_solve|].
intros r Hr. unfold art_ic_kept in Hr. decompose [and] Hr. kept_solve.
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_art_ic_it_13 := (ltac2:(TCodec.tc2 tcn__JbtInitCache "U4&:y5'Q<yR0%211%5241'2y8%611%311p061'9'5&Fr4(Q:+;(3%33A21%6251&Q;&Jr1+QPH%3221%52F1%>3F71r5+=%>3L1<%A231+]0%<2M1%E3M31r6+?%E3Q31C%H231+_oooooooooooM%C2Q41%L3Q431r7+@%L3Q:1J%O231%I2Q::%Q23Q:21r8+A%Q23Q@1Q0%Q5231+QP0%Q02QA1%Q93QA31r9+5%Q93QG1Q7%Q<231%Q62QG@%Q?3QG21r:+6%Q?3QM1Q=%QB231%Q<2QM@%QE3QM21r;+7%QE3R31QC%QH231+`0%QC2R41%QL3R431&K+TP0%221E&L%QH2A3&O+2+R0%3221%6251&@&Ir=+Ra0%4432E1'6'4'A&GvQ3r@+Zk`0%R@3RL1R>/01RLr?r>%8576321&<u8u4&M+R@%221R=%RE2E1+4%RG221&C%11RB%;49>31+8%RL271&E%11RG%@4?531%J5IROE1C%L3Q2C1%S:2S1S5+QS8%S42Q41%S62SG1%S?3SG41%S?2S6RO+^0%S:2SK1%SC3SK31%SC2S:RL+_oooooooooooN%S>2SO1%SG3SO31%T21T3&B%11S@r3r2%SL221rB%SN213%T03T831p071pR>:1%QF2<1%QG2A1%QH2F1%QI2L1qRBT>1%QL2T?1p0QN1p0R41p0R<1p0R@1p0RH1p0RO1p0S61p0S>1p0SE1p0SM1p0T51pR6TE1pRDTG1pHTH1pR@TN1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_ic_it_13) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_ic_it_13) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_ic_it_13) 2%nat 0%nat).
Variable ca : ltac:(sec_ty2 constr:(SEC_T_art_ic_it_13) 3%nat 0%nat).
Lemma art_ic_it_13 : ltac:(sec_stmt2 constr:(SEC_T_art_ic_it_13) 4%nat 0%nat).
Proof using Type regs M rom ca.
intros H11 H13 H15 H16 H17 H5 H6 H7 Hca Hca' W.
eexists. split.
{ zbft (ltac:(oF' 0x56e00%Z)) (ltac:(oD' 0x56e00%Z)).
zstep (ltac:(oF' 0x56e04%Z)) (ltac:(oD' 0x56e04%Z)).
zstep (ltac:(oF' 0x56e08%Z)) (ltac:(oD' 0x56e08%Z)).
zbtk (ltac:(oF' 0x56e0c%Z)) (ltac:(oD' 0x56e0c%Z)).
zstep (ltac:(oF' 0x56e2c%Z)) (ltac:(oD' 0x56e2c%Z)).
zstep (ltac:(oF' 0x56e30%Z)) (ltac:(oD' 0x56e30%Z)).
zbtk (ltac:(oF' 0x56e34%Z)) (ltac:(oD' 0x56e34%Z)).
zstep (ltac:(oF' 0x56ddc%Z)) (ltac:(oD' 0x56ddc%Z)).
zstep (ltac:(oF' 0x56de0%Z)) (ltac:(oD' 0x56de0%Z)).
zstep (ltac:(oF' 0x56de4%Z)) (ltac:(oD' 0x56de4%Z)).
zstep (ltac:(oF' 0x56de8%Z)) (ltac:(oD' 0x56de8%Z)).
zstep (ltac:(oF' 0x56dec%Z)) (ltac:(oD' 0x56dec%Z)).
zsw (ltac:(oF' 0x56df0%Z)) (ltac:(oD' 0x56df0%Z)) (ca + 80 * 13 + 4) (art_ic_mc 13) ltac:(rewok W).
zsd (ltac:(oF' 0x56df4%Z)) (ltac:(oD' 0x56df4%Z)) (ca + 80 * 13 + 8) (art_ic_size 13) ltac:(rewok W).
zstep (ltac:(oF' 0x56df8%Z)) (ltac:(oD' 0x56df8%Z)).
zbft (ltac:(oF' 0x56dfc%Z)) (ltac:(oD' 0x56dfc%Z)).
first [apply mst_refl | apply art_msteps_of_eq; apply art_mkst_eq; [reflexivity | zval | reflexivity]]. }
split; [kept_solve|]. split; [kept_solve|]. split; [kept_solve|].
intros r Hr. unfold art_ic_kept in Hr. decompose [and] Hr. kept_solve.
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_art_ic_it_14 := (ltac2:(TCodec.tc2 tcn__JbtInitCache "U5&:y5'Q<yR0%211%5241'2y8%611%311p061'9'5&Fr4(Q:+;(3%33A21%6251&Q;&Jr1+QS8%3221%52F1%>3F71r5+=%>3L1<%A231+^0%<2M1%E3M31r6+?%E3Q31C%H231+_oooooooooooN%C2Q41%L3Q431r7+@%L3Q:1J%O231%I2Q::%Q23Q:21r8+A%Q23Q@1Q0%Q5231+QP0%Q02QA1%Q93QA31r9+5%Q93QG1Q7%Q<231%Q62QG@%Q?3QG21r:+6%Q?3QM1Q=%QB231%Q<2QM@%QE3QM21r;+7%QE3R31QC%QH231+`0%QC2R41%QL3R431&K+TP0%221E&L%QH2A3&O+2+R0%3221%6251&@&Ir=+Ra0%4432E1'6'4'A&GvQ3r@+Zk`0%R@3RL1R>/01RLr?r>%8576321&<u8u4&M+R@+>%3221%RF2F1+4%RH221&C%116%<4:?31+8%RM271&E%11;%A4@531%K5JS0F1D%M3Q3D1%S;2S2S6+QUH%S52Q51%S72SH1%S@3SH41%S@2S7S0+_0%S;2SL1%SD3SL31%SD2S;RM+_oooooooooooO%S?2T01%SH3T031%T31T4&B%11SAr3r2%SM221rB%SO213%T13T931p071pR>:1%QG2<1%QH2A1%QI2F1%QJ2L1qRBT?1%QM2T@1p0QO1p0R51p0R=1p0RA1p0RI1p0S01p0S71p0S?1p0SF1p0SN1p0T61pR6TF1pRDTH1pHTI1pR@TO1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_ic_it_14) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_ic_it_14) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_ic_it_14) 2%nat 0%nat).
Variable ca : ltac:(sec_ty2 constr:(SEC_T_art_ic_it_14) 3%nat 0%nat).
Lemma art_ic_it_14 : ltac:(sec_stmt2 constr:(SEC_T_art_ic_it_14) 4%nat 0%nat).
Proof using Type regs M rom ca.
intros H11 H13 H15 H16 H17 H5 H6 H7 Hca Hca' W.
eexists. split.
{ zbft (ltac:(oF' 0x56e00%Z)) (ltac:(oD' 0x56e00%Z)).
zstep (ltac:(oF' 0x56e04%Z)) (ltac:(oD' 0x56e04%Z)).
zstep (ltac:(oF' 0x56e08%Z)) (ltac:(oD' 0x56e08%Z)).
zbtk (ltac:(oF' 0x56e0c%Z)) (ltac:(oD' 0x56e0c%Z)).
zstep (ltac:(oF' 0x56e2c%Z)) (ltac:(oD' 0x56e2c%Z)).
zstep (ltac:(oF' 0x56e30%Z)) (ltac:(oD' 0x56e30%Z)).
zbtk (ltac:(oF' 0x56e34%Z)) (ltac:(oD' 0x56e34%Z)).
zstep (ltac:(oF' 0x56ddc%Z)) (ltac:(oD' 0x56ddc%Z)).
zstep (ltac:(oF' 0x56de0%Z)) (ltac:(oD' 0x56de0%Z)).
zstep (ltac:(oF' 0x56de4%Z)) (ltac:(oD' 0x56de4%Z)).
zstep (ltac:(oF' 0x56de8%Z)) (ltac:(oD' 0x56de8%Z)).
zstep (ltac:(oF' 0x56dec%Z)) (ltac:(oD' 0x56dec%Z)).
zsw (ltac:(oF' 0x56df0%Z)) (ltac:(oD' 0x56df0%Z)) (ca + 80 * 14 + 4) (art_ic_mc 14) ltac:(rewok W).
zsd (ltac:(oF' 0x56df4%Z)) (ltac:(oD' 0x56df4%Z)) (ca + 80 * 14 + 8) (art_ic_size 14) ltac:(rewok W).
zstep (ltac:(oF' 0x56df8%Z)) (ltac:(oD' 0x56df8%Z)).
zbft (ltac:(oF' 0x56dfc%Z)) (ltac:(oD' 0x56dfc%Z)).
first [apply mst_refl | apply art_msteps_of_eq; apply art_mkst_eq; [reflexivity | zval | reflexivity]]. }
split; [kept_solve|]. split; [kept_solve|]. split; [kept_solve|].
intros r Hr. unfold art_ic_kept in Hr. decompose [and] Hr. kept_solve.
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_art_ic_it_15 := (ltac2:(TCodec.tc2 tcn__JbtInitCache "U2&:y5'Q<yR0%211%5241'2y8%611%311p061'9'5&Fr4(Q:+;(3%33A21%6251&Q;&Jr1+QUH%3221%52F1%>3F71r5+=%>3L1<%A231+_0%<2M1%E3M31r6+?%E3Q31C%H231+_oooooooooooO%C2Q41%L3Q431r7+@%L3Q:1J%O231%I2Q::%Q23Q:21r8+A%Q23Q@1Q0%Q5231+QP0%Q02QA1%Q93QA31r9+5%Q93QG1Q7%Q<231%Q62QG@%Q?3QG21r:+6%Q?3QM1Q=%QB231%Q<2QM@%QE3QM21r;+7%QE3R31QC%QH231+`0%QC2R41%QL3R431&K+TP0%221E&L%QH2A3&O+2+R0%3221%6251&@&Ir=+Ra0%4432E1'6'4'A&GvQ3r@+Zk`0%R@3RL1R>/01RLr?r>%8576321&<u8u4&M+R@%221R6%RE2E1+4%RG221&C%11R;%;49>31+8%RL271&E%11R@%@4?531%J5IROE1C%L3Q2C1%S:2S1S5+QX8%S42Q41%S62SG1%S?3SG41%S?2S6RO%SA3SI1QF%SA2S8RJz%S<2SM1%SE3SM31%T01T1&B%11S>r3r2%SJ221rB%SL213%SN3T631p071pR>:1%QD2<1%QE2A1%QF2D1%QG2J1qRBT<1%QJ2T=1p0QL1p0R21p0R:1p0R>1p0RF1p0RM1p0S41p0S<1p0SC1p0SK1p0T31pR6TC1pRDTE1pHTF1pR@TL1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_ic_it_15) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_ic_it_15) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_ic_it_15) 2%nat 0%nat).
Variable ca : ltac:(sec_ty2 constr:(SEC_T_art_ic_it_15) 3%nat 0%nat).
Lemma art_ic_it_15 : ltac:(sec_stmt2 constr:(SEC_T_art_ic_it_15) 4%nat 0%nat).
Proof using Type regs M rom ca.
intros H11 H13 H15 H16 H17 H5 H6 H7 Hca Hca' W.
eexists. split.
{ zbft (ltac:(oF' 0x56e00%Z)) (ltac:(oD' 0x56e00%Z)).
zstep (ltac:(oF' 0x56e04%Z)) (ltac:(oD' 0x56e04%Z)).
zstep (ltac:(oF' 0x56e08%Z)) (ltac:(oD' 0x56e08%Z)).
zbtk (ltac:(oF' 0x56e0c%Z)) (ltac:(oD' 0x56e0c%Z)).
zstep (ltac:(oF' 0x56e2c%Z)) (ltac:(oD' 0x56e2c%Z)).
zstep (ltac:(oF' 0x56e30%Z)) (ltac:(oD' 0x56e30%Z)).
zbtk (ltac:(oF' 0x56e34%Z)) (ltac:(oD' 0x56e34%Z)).
zstep (ltac:(oF' 0x56ddc%Z)) (ltac:(oD' 0x56ddc%Z)).
zstep (ltac:(oF' 0x56de0%Z)) (ltac:(oD' 0x56de0%Z)).
zstep (ltac:(oF' 0x56de4%Z)) (ltac:(oD' 0x56de4%Z)).
zstep (ltac:(oF' 0x56de8%Z)) (ltac:(oD' 0x56de8%Z)).
zstep (ltac:(oF' 0x56dec%Z)) (ltac:(oD' 0x56dec%Z)).
zsw (ltac:(oF' 0x56df0%Z)) (ltac:(oD' 0x56df0%Z)) (ca + 80 * 15 + 4) (art_ic_mc 15) ltac:(rewok W).
zsd (ltac:(oF' 0x56df4%Z)) (ltac:(oD' 0x56df4%Z)) (ca + 80 * 15 + 8) (art_ic_size 15) ltac:(rewok W).
zstep (ltac:(oF' 0x56df8%Z)) (ltac:(oD' 0x56df8%Z)).
zbft (ltac:(oF' 0x56dfc%Z)) (ltac:(oD' 0x56dfc%Z)).
first [apply mst_refl | apply art_msteps_of_eq; apply art_mkst_eq; [reflexivity | zval | reflexivity]]. }
split; [kept_solve|]. split; [kept_solve|]. split; [kept_solve|].
intros r Hr. unfold art_ic_kept in Hr. decompose [and] Hr. kept_solve.
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_art_ic_it_16 := (ltac2:(TCodec.tc2 tcn__JbtInitCache "U2&:y5'Q<yR0%211%5241'2y8%611%311p061'9'5&Fr4(Q:+;(3%33A21%6251&Q;&Jr1+QX8%3221%52F1%>3F71r5+=%>3L1<%A231+`0%<2M1%E3M31r6+?%E3Q31C%H231z%C2Q41%L3Q431r7+@%L3Q:1J%O231%I2Q::%Q23Q:21r8+A%Q23Q@1Q0%Q5231+QP0%Q02QA1%Q93QA31r9+5%Q93QG1Q7%Q<231%Q62QG@%Q?3QG21r:+6%Q?3QM1Q=%QB231%Q<2QM@%QE3QM21r;+7%QE3R31QC%QH231%QJ3R21Q6&K+TP0%221C&L%QF2?3&O+2+R0%3221%6251&@&Ir=+Ra0%4432C1'6'4'A&GvQ3r@+Zk`0%R>3RJ1R</01RJr?r>%8576321&<u8u4&M+R@%221QM%RC2E1+4%RE221&C%11R2%;49>31+8%RJ271&E%11R7%@4?531%J5IRME1C%L3Q2C1%S82ROS3+QZH%S22Q41%S42SE1%S=3SE41%S=2S4RM+a0%S82SI1%SA3SI31%SA2S8RJ+1%S<2SM1%SE3SM31%T01T1&B%11S>r3r2%SJ221rB%SL213%SN3T631p071pR>:1%QF2<1%QG2A1%QH2F1%QI2L1qRBT<1%QL2T=1p0QN1p0R41p0R<1p0R@1p0RF1p0RM1p0S41p0S<1p0SC1p0SK1p0T31pR6TC1pRDTE1pHTF1pR@TL1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_ic_it_16) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_ic_it_16) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_ic_it_16) 2%nat 0%nat).
Variable ca : ltac:(sec_ty2 constr:(SEC_T_art_ic_it_16) 3%nat 0%nat).
Lemma art_ic_it_16 : ltac:(sec_stmt2 constr:(SEC_T_art_ic_it_16) 4%nat 0%nat).
Proof using Type regs M rom ca.
intros H11 H13 H15 H16 H17 H5 H6 H7 Hca Hca' W.
eexists. split.
{ zbft (ltac:(oF' 0x56e00%Z)) (ltac:(oD' 0x56e00%Z)).
zstep (ltac:(oF' 0x56e04%Z)) (ltac:(oD' 0x56e04%Z)).
zstep (ltac:(oF' 0x56e08%Z)) (ltac:(oD' 0x56e08%Z)).
zbtk (ltac:(oF' 0x56e0c%Z)) (ltac:(oD' 0x56e0c%Z)).
zstep (ltac:(oF' 0x56e2c%Z)) (ltac:(oD' 0x56e2c%Z)).
zstep (ltac:(oF' 0x56e30%Z)) (ltac:(oD' 0x56e30%Z)).
zbtk (ltac:(oF' 0x56e34%Z)) (ltac:(oD' 0x56e34%Z)).
zstep (ltac:(oF' 0x56ddc%Z)) (ltac:(oD' 0x56ddc%Z)).
zstep (ltac:(oF' 0x56de0%Z)) (ltac:(oD' 0x56de0%Z)).
zstep (ltac:(oF' 0x56de4%Z)) (ltac:(oD' 0x56de4%Z)).
zstep (ltac:(oF' 0x56de8%Z)) (ltac:(oD' 0x56de8%Z)).
zstep (ltac:(oF' 0x56dec%Z)) (ltac:(oD' 0x56dec%Z)).
zsw (ltac:(oF' 0x56df0%Z)) (ltac:(oD' 0x56df0%Z)) (ca + 80 * 16 + 4) (art_ic_mc 16) ltac:(rewok W).
zsd (ltac:(oF' 0x56df4%Z)) (ltac:(oD' 0x56df4%Z)) (ca + 80 * 16 + 8) (art_ic_size 16) ltac:(rewok W).
zstep (ltac:(oF' 0x56df8%Z)) (ltac:(oD' 0x56df8%Z)).
zbft (ltac:(oF' 0x56dfc%Z)) (ltac:(oD' 0x56dfc%Z)).
first [apply mst_refl | apply art_msteps_of_eq; apply art_mkst_eq; [reflexivity | zval | reflexivity]]. }
split; [kept_solve|]. split; [kept_solve|]. split; [kept_solve|].
intros r Hr. unfold art_ic_kept in Hr. decompose [and] Hr. kept_solve.
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_art_ic_it_17 := (ltac2:(TCodec.tc2 tcn__JbtInitCache "U3&:y5'Q<yR0%211%5241'2y8%611%311p061'9'5&Fr4(Q:+;(3%33A21%6251&Q;&Jr1+QZH%3221%52F1%>3F71r5+=%>3L1<%A231+a0%<2M1%E3M31r6+?%E3Q31C%H231+1%C2Q41%L3Q431r7+@%L3Q:1J%O231%I2Q::%Q23Q:21r8+A%Q23Q@1Q0%Q5231+QP0%Q02QA1%Q93QA31r9+5%Q93QG1Q7%Q<231%Q62QG@%Q?3QG21r:+6%Q?3QM1Q=%QB231%Q<2QM@%QE3QM21r;+7%QE3R31QC%QH231+`0%QC2R41%QL3R431&K+TP0%221E&L%QH2A3&O+2+R0%3221%6251&@&Ir=+Ra0%4432E1'6'4'A&GvQ3r@+Zk`0%R@3RL1R>/01RLr?r>%8576321&<u8u4&M+R@%221QI%RE2E1+4%RG221&C%11QN%;49>31+8%RL271&E%11R3%@4?531%J5IROE1C%L3Q2C1%S:2S1S5+Q]8%S42Q41%S62SG1%S?3SG41%S?2S6RO+b0%S:2SK1%SC3SK31%SC2S:RL%S=2SNQB%SF3SN21%T11T2&B%11S?r3r2%SK221rB%SM213%SO3T731p071pR>:1%QE2<1%QF2@1%QG2E1%QH2K1qRBT=1%QK2T>1p0QM1p0R31p0R;1p0R?1p0RG1p0RN1p0S51p0S=1p0SD1p0SL1p0T41pR6TD1pRDTF1pHTG1pR@TM1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_ic_it_17) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_ic_it_17) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_ic_it_17) 2%nat 0%nat).
Variable ca : ltac:(sec_ty2 constr:(SEC_T_art_ic_it_17) 3%nat 0%nat).
Lemma art_ic_it_17 : ltac:(sec_stmt2 constr:(SEC_T_art_ic_it_17) 4%nat 0%nat).
Proof using Type regs M rom ca.
intros H11 H13 H15 H16 H17 H5 H6 H7 Hca Hca' W.
eexists. split.
{ zbft (ltac:(oF' 0x56e00%Z)) (ltac:(oD' 0x56e00%Z)).
zstep (ltac:(oF' 0x56e04%Z)) (ltac:(oD' 0x56e04%Z)).
zstep (ltac:(oF' 0x56e08%Z)) (ltac:(oD' 0x56e08%Z)).
zbft (ltac:(oF' 0x56e0c%Z)) (ltac:(oD' 0x56e0c%Z)).
zstep (ltac:(oF' 0x56e10%Z)) (ltac:(oD' 0x56e10%Z)).
zstep (ltac:(oF' 0x56e14%Z)) (ltac:(oD' 0x56e14%Z)).
zstep (ltac:(oF' 0x56e18%Z)) (ltac:(oD' 0x56e18%Z)).
zstep (ltac:(oF' 0x56e1c%Z)) (ltac:(oD' 0x56e1c%Z)).
zstep (ltac:(oF' 0x56e20%Z)) (ltac:(oD' 0x56e20%Z)).
zstep (ltac:(oF' 0x56e24%Z)) (ltac:(oD' 0x56e24%Z)).
zstep (ltac:(oF' 0x56e28%Z)) (ltac:(oD' 0x56e28%Z)).
zstep (ltac:(oF' 0x56e2c%Z)) (ltac:(oD' 0x56e2c%Z)).
zstep (ltac:(oF' 0x56e30%Z)) (ltac:(oD' 0x56e30%Z)).
zbtk (ltac:(oF' 0x56e34%Z)) (ltac:(oD' 0x56e34%Z)).
zstep (ltac:(oF' 0x56ddc%Z)) (ltac:(oD' 0x56ddc%Z)).
zstep (ltac:(oF' 0x56de0%Z)) (ltac:(oD' 0x56de0%Z)).
zstep (ltac:(oF' 0x56de4%Z)) (ltac:(oD' 0x56de4%Z)).
zstep (ltac:(oF' 0x56de8%Z)) (ltac:(oD' 0x56de8%Z)).
zstep (ltac:(oF' 0x56dec%Z)) (ltac:(oD' 0x56dec%Z)).
zsw (ltac:(oF' 0x56df0%Z)) (ltac:(oD' 0x56df0%Z)) (ca + 80 * 17 + 4) (art_ic_mc 17) ltac:(rewok W).
zsd (ltac:(oF' 0x56df4%Z)) (ltac:(oD' 0x56df4%Z)) (ca + 80 * 17 + 8) (art_ic_size 17) ltac:(rewok W).
zstep (ltac:(oF' 0x56df8%Z)) (ltac:(oD' 0x56df8%Z)).
zbft (ltac:(oF' 0x56dfc%Z)) (ltac:(oD' 0x56dfc%Z)).
first [apply mst_refl | apply art_msteps_of_eq; apply art_mkst_eq; [reflexivity | zval | reflexivity]]. }
split; [kept_solve|]. split; [kept_solve|]. split; [kept_solve|].
intros r Hr. unfold art_ic_kept in Hr. decompose [and] Hr. kept_solve.
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_art_ic_it_18 := (ltac2:(TCodec.tc2 tcn__JbtInitCache "U4&:y5'Q<yR0%211%5241'2y8%611%311p061'9'5&Fr4(Q:+;(3%33A21%6251&Q;&Jr1+Q]8%3221%52F1%>3F71r5+=%>3L1<%A231+b0%<2M1%E3M31r6+?%E3Q31C%H231+2%C2Q41%L3Q431r7+@%L3Q:1J%O231%I2Q::%Q23Q:21r8+A%Q23Q@1Q0%Q5231+QP0%Q02QA1%Q93QA31r9+5%Q93QG1Q7%Q<231%Q62QG@%Q?3QG21r:+6%Q?3QM1Q=%QB231%Q<2QM@%QE3QM21r;+7%QE3R31QC%QH231+`0%QC2R41%QL3R431&K+TP0%221E&L%QH2A3&O+R0%22Q:1%5241&@&Ir=+Ra0%4432D1'6'4'A&GvQ3r@+Zk`0%R?3RK1R=/01RKr?r>%8576321&<u8u4&M+R@+B%3221%RE2F1+4%RG221&C%116%<4:?31+8%RL271&E%11;%A4@531%K5JROF1D%M3Q3D1%S:2S1S5+Q_H%S42Q51%S62SG1%S?3SG41%S?2S6RO+c0%S:2SK1%SC3SK31%SC2S:RL+3%S>2SO1%SG3SO31%T21T3&B%11S@r3r2%SL221rB%SN213%T03T831p071pR>:1%QG2<1%QH2A1%QI2F1%QJ2L1qRBT>1%QM2T?1p0QO1p0R51p0R<1p0R@1p0RH1p0RO1p0S61p0S>1p0SE1p0SM1p0T51pR6TE1pRDTG1pHTH1pR@TN1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_ic_it_18) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_ic_it_18) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_ic_it_18) 2%nat 0%nat).
Variable ca : ltac:(sec_ty2 constr:(SEC_T_art_ic_it_18) 3%nat 0%nat).
Lemma art_ic_it_18 : ltac:(sec_stmt2 constr:(SEC_T_art_ic_it_18) 4%nat 0%nat).
Proof using Type regs M rom ca.
intros H11 H13 H15 H16 H17 H5 H6 H7 Hca Hca' W.
eexists. split.
{ zbft (ltac:(oF' 0x56e00%Z)) (ltac:(oD' 0x56e00%Z)).
zstep (ltac:(oF' 0x56e04%Z)) (ltac:(oD' 0x56e04%Z)).
zstep (ltac:(oF' 0x56e08%Z)) (ltac:(oD' 0x56e08%Z)).
zbft (ltac:(oF' 0x56e0c%Z)) (ltac:(oD' 0x56e0c%Z)).
zstep (ltac:(oF' 0x56e10%Z)) (ltac:(oD' 0x56e10%Z)).
zstep (ltac:(oF' 0x56e14%Z)) (ltac:(oD' 0x56e14%Z)).
zstep (ltac:(oF' 0x56e18%Z)) (ltac:(oD' 0x56e18%Z)).
zstep (ltac:(oF' 0x56e1c%Z)) (ltac:(oD' 0x56e1c%Z)).
zstep (ltac:(oF' 0x56e20%Z)) (ltac:(oD' 0x56e20%Z)).
zstep (ltac:(oF' 0x56e24%Z)) (ltac:(oD' 0x56e24%Z)).
zstep (ltac:(oF' 0x56e28%Z)) (ltac:(oD' 0x56e28%Z)).
zstep (ltac:(oF' 0x56e2c%Z)) (ltac:(oD' 0x56e2c%Z)).
zstep (ltac:(oF' 0x56e30%Z)) (ltac:(oD' 0x56e30%Z)).
zbtk (ltac:(oF' 0x56e34%Z)) (ltac:(oD' 0x56e34%Z)).
zstep (ltac:(oF' 0x56ddc%Z)) (ltac:(oD' 0x56ddc%Z)).
zstep (ltac:(oF' 0x56de0%Z)) (ltac:(oD' 0x56de0%Z)).
zstep (ltac:(oF' 0x56de4%Z)) (ltac:(oD' 0x56de4%Z)).
zstep (ltac:(oF' 0x56de8%Z)) (ltac:(oD' 0x56de8%Z)).
zstep (ltac:(oF' 0x56dec%Z)) (ltac:(oD' 0x56dec%Z)).
zsw (ltac:(oF' 0x56df0%Z)) (ltac:(oD' 0x56df0%Z)) (ca + 80 * 18 + 4) (art_ic_mc 18) ltac:(rewok W).
zsd (ltac:(oF' 0x56df4%Z)) (ltac:(oD' 0x56df4%Z)) (ca + 80 * 18 + 8) (art_ic_size 18) ltac:(rewok W).
zstep (ltac:(oF' 0x56df8%Z)) (ltac:(oD' 0x56df8%Z)).
zbft (ltac:(oF' 0x56dfc%Z)) (ltac:(oD' 0x56dfc%Z)).
first [apply mst_refl | apply art_msteps_of_eq; apply art_mkst_eq; [reflexivity | zval | reflexivity]]. }
split; [kept_solve|]. split; [kept_solve|]. split; [kept_solve|].
intros r Hr. unfold art_ic_kept in Hr. decompose [and] Hr. kept_solve.
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_art_ic_it_19 := (ltac2:(TCodec.tc2 tcn__JbtInitCache "U4&:y5'Q<yR0%211%5241'2y8%611%311p061'9'5&Fr4(Q:+;(3%33A21%6251&Q;&Jr1+Q_H%3221%52F1%>3F71r5+=%>3L1<%A231+c0%<2M1%E3M31r6+?%E3Q31C%H231+3%C2Q41%L3Q431r7+@%L3Q:1J%O231%I2Q::%Q23Q:21r8+A%Q23Q@1Q0%Q5231+QP0%Q02QA1%Q93QA31r9+5%Q93QG1Q7%Q<231%Q62QG@%Q?3QG21r:+6%Q?3QM1Q=%QB231%Q<2QM@%QE3QM21r;+7%QE3R31QC%QH231+`0%QC2R41%QL3R431&K+TP0%221E&L%QH2A3&O+2+R0%3221%6251&@&Ir=+Ra0%4432E1'6'4'A&GvQ3r@+Zk`0%R@3RL1R>/01RLr?r>%8576321&<u8u4&M+R@+C%3221%RF2F1+4%RH221&C%116%<4:?31+8%RM271&E%11;%A4@531%K5JS0F1D%M3Q3D1%S;2S2S6+Qb8%S52Q51%S72SH1%S@3SH41%S@2S7S0+d0%S;2SL1%SD3SL31%SD2S;RM%S>2SOF%SG3SO21%T21T3&B%11S@r3r2%SL221rB%SN213%T03T831p071pR>:1%QF2<1%QG2@1%QH2E1%QI2K1qRBT>1%QL2T?1p0QN1p0R41p0R<1p0R@1p0RH1p0RO1p0S61p0S>1p0SE1p0SM1p0T51pR6TE1pRDTG1pHTH1pR@TN1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_ic_it_19) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_ic_it_19) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_ic_it_19) 2%nat 0%nat).
Variable ca : ltac:(sec_ty2 constr:(SEC_T_art_ic_it_19) 3%nat 0%nat).
Lemma art_ic_it_19 : ltac:(sec_stmt2 constr:(SEC_T_art_ic_it_19) 4%nat 0%nat).
Proof using Type regs M rom ca.
intros H11 H13 H15 H16 H17 H5 H6 H7 Hca Hca' W.
eexists. split.
{ zbft (ltac:(oF' 0x56e00%Z)) (ltac:(oD' 0x56e00%Z)).
zstep (ltac:(oF' 0x56e04%Z)) (ltac:(oD' 0x56e04%Z)).
zstep (ltac:(oF' 0x56e08%Z)) (ltac:(oD' 0x56e08%Z)).
zbft (ltac:(oF' 0x56e0c%Z)) (ltac:(oD' 0x56e0c%Z)).
zstep (ltac:(oF' 0x56e10%Z)) (ltac:(oD' 0x56e10%Z)).
zstep (ltac:(oF' 0x56e14%Z)) (ltac:(oD' 0x56e14%Z)).
zstep (ltac:(oF' 0x56e18%Z)) (ltac:(oD' 0x56e18%Z)).
zstep (ltac:(oF' 0x56e1c%Z)) (ltac:(oD' 0x56e1c%Z)).
zstep (ltac:(oF' 0x56e20%Z)) (ltac:(oD' 0x56e20%Z)).
zstep (ltac:(oF' 0x56e24%Z)) (ltac:(oD' 0x56e24%Z)).
zstep (ltac:(oF' 0x56e28%Z)) (ltac:(oD' 0x56e28%Z)).
zstep (ltac:(oF' 0x56e2c%Z)) (ltac:(oD' 0x56e2c%Z)).
zstep (ltac:(oF' 0x56e30%Z)) (ltac:(oD' 0x56e30%Z)).
zbtk (ltac:(oF' 0x56e34%Z)) (ltac:(oD' 0x56e34%Z)).
zstep (ltac:(oF' 0x56ddc%Z)) (ltac:(oD' 0x56ddc%Z)).
zstep (ltac:(oF' 0x56de0%Z)) (ltac:(oD' 0x56de0%Z)).
zstep (ltac:(oF' 0x56de4%Z)) (ltac:(oD' 0x56de4%Z)).
zstep (ltac:(oF' 0x56de8%Z)) (ltac:(oD' 0x56de8%Z)).
zstep (ltac:(oF' 0x56dec%Z)) (ltac:(oD' 0x56dec%Z)).
zsw (ltac:(oF' 0x56df0%Z)) (ltac:(oD' 0x56df0%Z)) (ca + 80 * 19 + 4) (art_ic_mc 19) ltac:(rewok W).
zsd (ltac:(oF' 0x56df4%Z)) (ltac:(oD' 0x56df4%Z)) (ca + 80 * 19 + 8) (art_ic_size 19) ltac:(rewok W).
zstep (ltac:(oF' 0x56df8%Z)) (ltac:(oD' 0x56df8%Z)).
zbft (ltac:(oF' 0x56dfc%Z)) (ltac:(oD' 0x56dfc%Z)).
first [apply mst_refl | apply art_msteps_of_eq; apply art_mkst_eq; [reflexivity | zval | reflexivity]]. }
split; [kept_solve|]. split; [kept_solve|]. split; [kept_solve|].
intros r Hr. unfold art_ic_kept in Hr. decompose [and] Hr. kept_solve.
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_art_ic_it_20 := (ltac2:(TCodec.tc2 tcn__JbtInitCache "U3&:y5'Q<yR0%211%5241'2y8%611%311p061'9'5&Fr4(Q:+;(3%33A21%6251&Q;&Jr1+Qb8%3221%52F1%>3F71r5+=%>3L1<%A231+d0%<2M1%E3M31r6+?%E3Q31C%H231+4%C2Q41%L3Q431r7+@%L3Q:1J%O231%I2Q::%Q23Q:21r8+A%Q23Q@1Q0%Q5231+QP0%Q02QA1%Q93QA31r9+5%Q93QG1Q7%Q<231%Q62QG@%Q?3QG21r:+6%Q?3QM1Q=%QB231%Q<2QM@%QE3QM21r;+7%QE3R31QC%QH231+`0%QC2R41%QL3R431&K+TP0%221E&L%QH2A3&O+2+R0%3221%6251&@&Ir=+Ra0%4432E1'6'4'A&GvQ3r@+Zk`0%R@3RL1R>/01RLr?r>%8576321&<u8u4&M+R@+D%3221%RF2F1%RG21R6&C%115%;49>31+8%RL261&E%11:%@4?531%J5IROE1C%L3Q2C1%S:2S1S5+QdH%S42Q41%S62SG1%S?3SG41%S?2S6RO+e0%S:2SK1%SC3SK31%SC2S:RL%S=2SNR:%SF3SN21%T11T2&B%11S?r3r2%SK221rB%SM213%SO3T731p071pR>:1%QE2<1%QF2@1%QG2E1%QH2K1qRBT=1%QK2T>1p0QM1p0R31p0R;1p0R?1p0RG1p0RN1p0S51p0S=1p0SD1p0SL1p0T41pR6TD1pRDTF1pHTG1pR@TM1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_ic_it_20) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_ic_it_20) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_ic_it_20) 2%nat 0%nat).
Variable ca : ltac:(sec_ty2 constr:(SEC_T_art_ic_it_20) 3%nat 0%nat).
Lemma art_ic_it_20 : ltac:(sec_stmt2 constr:(SEC_T_art_ic_it_20) 4%nat 0%nat).
Proof using Type regs M rom ca.
intros H11 H13 H15 H16 H17 H5 H6 H7 Hca Hca' W.
eexists. split.
{ zbft (ltac:(oF' 0x56e00%Z)) (ltac:(oD' 0x56e00%Z)).
zstep (ltac:(oF' 0x56e04%Z)) (ltac:(oD' 0x56e04%Z)).
zstep (ltac:(oF' 0x56e08%Z)) (ltac:(oD' 0x56e08%Z)).
zbft (ltac:(oF' 0x56e0c%Z)) (ltac:(oD' 0x56e0c%Z)).
zstep (ltac:(oF' 0x56e10%Z)) (ltac:(oD' 0x56e10%Z)).
zstep (ltac:(oF' 0x56e14%Z)) (ltac:(oD' 0x56e14%Z)).
zstep (ltac:(oF' 0x56e18%Z)) (ltac:(oD' 0x56e18%Z)).
zstep (ltac:(oF' 0x56e1c%Z)) (ltac:(oD' 0x56e1c%Z)).
zstep (ltac:(oF' 0x56e20%Z)) (ltac:(oD' 0x56e20%Z)).
zstep (ltac:(oF' 0x56e24%Z)) (ltac:(oD' 0x56e24%Z)).
zstep (ltac:(oF' 0x56e28%Z)) (ltac:(oD' 0x56e28%Z)).
zstep (ltac:(oF' 0x56e2c%Z)) (ltac:(oD' 0x56e2c%Z)).
zstep (ltac:(oF' 0x56e30%Z)) (ltac:(oD' 0x56e30%Z)).
zbtk (ltac:(oF' 0x56e34%Z)) (ltac:(oD' 0x56e34%Z)).
zstep (ltac:(oF' 0x56ddc%Z)) (ltac:(oD' 0x56ddc%Z)).
zstep (ltac:(oF' 0x56de0%Z)) (ltac:(oD' 0x56de0%Z)).
zstep (ltac:(oF' 0x56de4%Z)) (ltac:(oD' 0x56de4%Z)).
zstep (ltac:(oF' 0x56de8%Z)) (ltac:(oD' 0x56de8%Z)).
zstep (ltac:(oF' 0x56dec%Z)) (ltac:(oD' 0x56dec%Z)).
zsw (ltac:(oF' 0x56df0%Z)) (ltac:(oD' 0x56df0%Z)) (ca + 80 * 20 + 4) (art_ic_mc 20) ltac:(rewok W).
zsd (ltac:(oF' 0x56df4%Z)) (ltac:(oD' 0x56df4%Z)) (ca + 80 * 20 + 8) (art_ic_size 20) ltac:(rewok W).
zstep (ltac:(oF' 0x56df8%Z)) (ltac:(oD' 0x56df8%Z)).
zbft (ltac:(oF' 0x56dfc%Z)) (ltac:(oD' 0x56dfc%Z)).
first [apply mst_refl | apply art_msteps_of_eq; apply art_mkst_eq; [reflexivity | zval | reflexivity]]. }
split; [kept_solve|]. split; [kept_solve|]. split; [kept_solve|].
intros r Hr. unfold art_ic_kept in Hr. decompose [and] Hr. kept_solve.
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_art_ic_it_21 := (ltac2:(TCodec.tc2 tcn__JbtInitCache "U3&:y5'Q<yR0%211%5241'2y8%611%311p061'9'5&Fr4(Q:+;(3%33A21%6251&Q;&Jr1+QdH%3221%52F1%>3F71r5+=%>3L1<%A231+e0%<2M1%E3M31r6+?%E3Q31C%H231+5%C2Q41%L3Q431r7+@%L3Q:1J%O231%I2Q::%Q23Q:21r8+A%Q23Q@1Q0%Q5231+QP0%Q02QA1%Q93QA31r9%Q83QFAQ6%Q;221%Q52QF?%Q>3QF21r:+6%Q>3QL1Q<%QA231%Q;2QL?%QD3QL21r;+7%QD3R21QB%QG231+`0%QB2R31%QK3R331&K+TP0%221D&L%QG2A3&O+2+R0%3221%6251&@&Ir=+Ra0%4432E1'6'4'A&GvQ3r@+Zk`0%R?3RK1R=/01RKr?r>%8576321&<u8u4&M+R@+E%3221%RE2F1+4%RG221&C%116%<4:?31+8%RL271&E%11;%A4@531%K5JROF1D%M3Q3D1%S:2S1S5+Qg8%S42Q51%S62SG1%S?3SG41%S?2S6RO+f0%S:2SK1%SC3SK31%SC2S:RL%S=2SNR5%SF3SN21%T11T2&B%11S?r3r2%SK221rB%SM213%SO3T731p071pR>:1%QF2<1%QG2@1%QH2E1%QI2K1qRBT=1%QL2T>1p0QN1p0R41p0R<1p0R@1p0RH1p0RO1p0S51p0S=1p0SD1p0SL1p0T41pR6TD1pRDTF1pHTG1pR@TM1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_ic_it_21) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_ic_it_21) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_ic_it_21) 2%nat 0%nat).
Variable ca : ltac:(sec_ty2 constr:(SEC_T_art_ic_it_21) 3%nat 0%nat).
Lemma art_ic_it_21 : ltac:(sec_stmt2 constr:(SEC_T_art_ic_it_21) 4%nat 0%nat).
Proof using Type regs M rom ca.
intros H11 H13 H15 H16 H17 H5 H6 H7 Hca Hca' W.
eexists. split.
{ zbft (ltac:(oF' 0x56e00%Z)) (ltac:(oD' 0x56e00%Z)).
zstep (ltac:(oF' 0x56e04%Z)) (ltac:(oD' 0x56e04%Z)).
zstep (ltac:(oF' 0x56e08%Z)) (ltac:(oD' 0x56e08%Z)).
zbft (ltac:(oF' 0x56e0c%Z)) (ltac:(oD' 0x56e0c%Z)).
zstep (ltac:(oF' 0x56e10%Z)) (ltac:(oD' 0x56e10%Z)).
zstep (ltac:(oF' 0x56e14%Z)) (ltac:(oD' 0x56e14%Z)).
zstep (ltac:(oF' 0x56e18%Z)) (ltac:(oD' 0x56e18%Z)).
zstep (ltac:(oF' 0x56e1c%Z)) (ltac:(oD' 0x56e1c%Z)).
zstep (ltac:(oF' 0x56e20%Z)) (ltac:(oD' 0x56e20%Z)).
zstep (ltac:(oF' 0x56e24%Z)) (ltac:(oD' 0x56e24%Z)).
zstep (ltac:(oF' 0x56e28%Z)) (ltac:(oD' 0x56e28%Z)).
zstep (ltac:(oF' 0x56e2c%Z)) (ltac:(oD' 0x56e2c%Z)).
zstep (ltac:(oF' 0x56e30%Z)) (ltac:(oD' 0x56e30%Z)).
zbtk (ltac:(oF' 0x56e34%Z)) (ltac:(oD' 0x56e34%Z)).
zstep (ltac:(oF' 0x56ddc%Z)) (ltac:(oD' 0x56ddc%Z)).
zstep (ltac:(oF' 0x56de0%Z)) (ltac:(oD' 0x56de0%Z)).
zstep (ltac:(oF' 0x56de4%Z)) (ltac:(oD' 0x56de4%Z)).
zstep (ltac:(oF' 0x56de8%Z)) (ltac:(oD' 0x56de8%Z)).
zstep (ltac:(oF' 0x56dec%Z)) (ltac:(oD' 0x56dec%Z)).
zsw (ltac:(oF' 0x56df0%Z)) (ltac:(oD' 0x56df0%Z)) (ca + 80 * 21 + 4) (art_ic_mc 21) ltac:(rewok W).
zsd (ltac:(oF' 0x56df4%Z)) (ltac:(oD' 0x56df4%Z)) (ca + 80 * 21 + 8) (art_ic_size 21) ltac:(rewok W).
zstep (ltac:(oF' 0x56df8%Z)) (ltac:(oD' 0x56df8%Z)).
zbft (ltac:(oF' 0x56dfc%Z)) (ltac:(oD' 0x56dfc%Z)).
first [apply mst_refl | apply art_msteps_of_eq; apply art_mkst_eq; [reflexivity | zval | reflexivity]]. }
split; [kept_solve|]. split; [kept_solve|]. split; [kept_solve|].
intros r Hr. unfold art_ic_kept in Hr. decompose [and] Hr. kept_solve.
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_art_ic_it_22 := (ltac2:(TCodec.tc2 tcn__JbtInitCache "U3&:y5'Q<yR0%211%5241'2y8%611%311p061'9'5&Fr4(Q:+;(3%33A21%6251&Q;&Jr1+Qg8%3221%52F1%>3F71r5+=%>3L1<%A231+f0%<2M1%E3M31r6+?%E3Q31C%H231+6%C2Q41%L3Q431r7+@%L3Q:1J%O231%I2Q::%Q23Q:21r8+A%Q23Q@1Q0%Q5231+QP0%Q02QA1%Q93QA31r9+5%Q93QG1Q7%Q<231%Q62QG@%Q?3QG21r:%Q>3QLGQ<%QA221%Q;2QL?%QD3QL21r;+7%QD3R21QB%QG231+`0%QB2R31%QK3R331&K+TP0%221D&L%QG2@3&O+2+R0%3221%6251&@&Ir=+Ra0%4432E1'6'4'A&GvQ3r@+Zk`0%R?3RK1R=/01RKr?r>%8576321&<u8u4&M+R@+F%3221%RE2F1+4%RG221&C%116%<4:?31+8%RL271&E%11;%A4@531%K5JROF1D%M3Q3D1%S:2S1S5+QiH%S42Q51%S62SG1%S?3SG41%S?2S6RO+g0%S:2SK1%SC3SK31%SC2S:RL%S=2SNQO%SF3SN21%T11T2&B%11S?r3r2%SK221rB%SM213%SO3T731p071pR>:1%QF2<1%QG2@1%QH2E1%QI2K1qRBT=1%QL2T>1p0QN1p0R41p0R<1p0R@1p0RH1p0RN1p0S51p0S=1p0SD1p0SL1p0T41pR6TD1pRDTF1pHTG1pR@TM1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_ic_it_22) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_ic_it_22) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_ic_it_22) 2%nat 0%nat).
Variable ca : ltac:(sec_ty2 constr:(SEC_T_art_ic_it_22) 3%nat 0%nat).
Lemma art_ic_it_22 : ltac:(sec_stmt2 constr:(SEC_T_art_ic_it_22) 4%nat 0%nat).
Proof using Type regs M rom ca.
intros H11 H13 H15 H16 H17 H5 H6 H7 Hca Hca' W.
eexists. split.
{ zbft (ltac:(oF' 0x56e00%Z)) (ltac:(oD' 0x56e00%Z)).
zstep (ltac:(oF' 0x56e04%Z)) (ltac:(oD' 0x56e04%Z)).
zstep (ltac:(oF' 0x56e08%Z)) (ltac:(oD' 0x56e08%Z)).
zbft (ltac:(oF' 0x56e0c%Z)) (ltac:(oD' 0x56e0c%Z)).
zstep (ltac:(oF' 0x56e10%Z)) (ltac:(oD' 0x56e10%Z)).
zstep (ltac:(oF' 0x56e14%Z)) (ltac:(oD' 0x56e14%Z)).
zstep (ltac:(oF' 0x56e18%Z)) (ltac:(oD' 0x56e18%Z)).
zstep (ltac:(oF' 0x56e1c%Z)) (ltac:(oD' 0x56e1c%Z)).
zstep (ltac:(oF' 0x56e20%Z)) (ltac:(oD' 0x56e20%Z)).
zstep (ltac:(oF' 0x56e24%Z)) (ltac:(oD' 0x56e24%Z)).
zstep (ltac:(oF' 0x56e28%Z)) (ltac:(oD' 0x56e28%Z)).
zstep (ltac:(oF' 0x56e2c%Z)) (ltac:(oD' 0x56e2c%Z)).
zstep (ltac:(oF' 0x56e30%Z)) (ltac:(oD' 0x56e30%Z)).
zbtk (ltac:(oF' 0x56e34%Z)) (ltac:(oD' 0x56e34%Z)).
zstep (ltac:(oF' 0x56ddc%Z)) (ltac:(oD' 0x56ddc%Z)).
zstep (ltac:(oF' 0x56de0%Z)) (ltac:(oD' 0x56de0%Z)).
zstep (ltac:(oF' 0x56de4%Z)) (ltac:(oD' 0x56de4%Z)).
zstep (ltac:(oF' 0x56de8%Z)) (ltac:(oD' 0x56de8%Z)).
zstep (ltac:(oF' 0x56dec%Z)) (ltac:(oD' 0x56dec%Z)).
zsw (ltac:(oF' 0x56df0%Z)) (ltac:(oD' 0x56df0%Z)) (ca + 80 * 22 + 4) (art_ic_mc 22) ltac:(rewok W).
zsd (ltac:(oF' 0x56df4%Z)) (ltac:(oD' 0x56df4%Z)) (ca + 80 * 22 + 8) (art_ic_size 22) ltac:(rewok W).
zstep (ltac:(oF' 0x56df8%Z)) (ltac:(oD' 0x56df8%Z)).
zbft (ltac:(oF' 0x56dfc%Z)) (ltac:(oD' 0x56dfc%Z)).
first [apply mst_refl | apply art_msteps_of_eq; apply art_mkst_eq; [reflexivity | zval | reflexivity]]. }
split; [kept_solve|]. split; [kept_solve|]. split; [kept_solve|].
intros r Hr. unfold art_ic_kept in Hr. decompose [and] Hr. kept_solve.
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_art_ic_it_23 := (ltac2:(TCodec.tc2 tcn__JbtInitCache "U3&:y5'Q<yR0%211%5241'2y8%611%311p061'9'5&Fr4(Q:+;(3%33A21%6251&Q;&Jr1+QiH%3221%52F1%>3F71r5+=%>3L1<%A231+g0%<2M1%E3M31r6+?%E3Q31C%H231+7%C2Q41%L3Q431r7+@%L3Q:1J%O231%I2Q::%Q23Q:21r8+A%Q23Q@1Q0%Q5231+QP0%Q02QA1%Q93QA31r9+5%Q93QG1Q7%Q<231%Q62QG@%Q?3QG21r:+6%Q?3QM1Q=%QB231%Q<2QM@%QE3QM21r;%QD3R2MQB%QG221+`0%QB2R31%QK3R331&K+TP0%221D&L%QG2@3&O+2+R0%3221%6251&@&Ir=+Ra0%4432D1'6'4'A&GvQ3r@+Zk`0%R?3RK1R=/01RKr?r>%8576321&<u8u4&M+R@+G%3221%RE2F1+4%RG221&C%116%<4:?31+8%RL271&E%11;%A4@531%K5JROF1D%M3Q3D1%S:2S1S5+Ql8%S42Q51%S62SG1%S?3SG41%S?2S6RO+h0%S:2SK1%SC3SK31%SC2S:RL%S=2SNA%SF3SN21%T11T2&B%11S?r3r2%SK221rB%SM213%SO3T731p071pR>:1%QF2<1%QG2@1%QH2E1%QI2K1qRBT=1%QL2T>1p0QN1p0R41p0R<1p0R@1p0RG1p0RN1p0S51p0S=1p0SD1p0SL1p0T41pR6TD1pRDTF1pHTG1pR@TM1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_ic_it_23) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_ic_it_23) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_ic_it_23) 2%nat 0%nat).
Variable ca : ltac:(sec_ty2 constr:(SEC_T_art_ic_it_23) 3%nat 0%nat).
Lemma art_ic_it_23 : ltac:(sec_stmt2 constr:(SEC_T_art_ic_it_23) 4%nat 0%nat).
Proof using Type regs M rom ca.
intros H11 H13 H15 H16 H17 H5 H6 H7 Hca Hca' W.
eexists. split.
{ zbft (ltac:(oF' 0x56e00%Z)) (ltac:(oD' 0x56e00%Z)).
zstep (ltac:(oF' 0x56e04%Z)) (ltac:(oD' 0x56e04%Z)).
zstep (ltac:(oF' 0x56e08%Z)) (ltac:(oD' 0x56e08%Z)).
zbft (ltac:(oF' 0x56e0c%Z)) (ltac:(oD' 0x56e0c%Z)).
zstep (ltac:(oF' 0x56e10%Z)) (ltac:(oD' 0x56e10%Z)).
zstep (ltac:(oF' 0x56e14%Z)) (ltac:(oD' 0x56e14%Z)).
zstep (ltac:(oF' 0x56e18%Z)) (ltac:(oD' 0x56e18%Z)).
zstep (ltac:(oF' 0x56e1c%Z)) (ltac:(oD' 0x56e1c%Z)).
zstep (ltac:(oF' 0x56e20%Z)) (ltac:(oD' 0x56e20%Z)).
zstep (ltac:(oF' 0x56e24%Z)) (ltac:(oD' 0x56e24%Z)).
zstep (ltac:(oF' 0x56e28%Z)) (ltac:(oD' 0x56e28%Z)).
zstep (ltac:(oF' 0x56e2c%Z)) (ltac:(oD' 0x56e2c%Z)).
zstep (ltac:(oF' 0x56e30%Z)) (ltac:(oD' 0x56e30%Z)).
zbtk (ltac:(oF' 0x56e34%Z)) (ltac:(oD' 0x56e34%Z)).
zstep (ltac:(oF' 0x56ddc%Z)) (ltac:(oD' 0x56ddc%Z)).
zstep (ltac:(oF' 0x56de0%Z)) (ltac:(oD' 0x56de0%Z)).
zstep (ltac:(oF' 0x56de4%Z)) (ltac:(oD' 0x56de4%Z)).
zstep (ltac:(oF' 0x56de8%Z)) (ltac:(oD' 0x56de8%Z)).
zstep (ltac:(oF' 0x56dec%Z)) (ltac:(oD' 0x56dec%Z)).
zsw (ltac:(oF' 0x56df0%Z)) (ltac:(oD' 0x56df0%Z)) (ca + 80 * 23 + 4) (art_ic_mc 23) ltac:(rewok W).
zsd (ltac:(oF' 0x56df4%Z)) (ltac:(oD' 0x56df4%Z)) (ca + 80 * 23 + 8) (art_ic_size 23) ltac:(rewok W).
zstep (ltac:(oF' 0x56df8%Z)) (ltac:(oD' 0x56df8%Z)).
zbft (ltac:(oF' 0x56dfc%Z)) (ltac:(oD' 0x56dfc%Z)).
first [apply mst_refl | apply art_msteps_of_eq; apply art_mkst_eq; [reflexivity | zval | reflexivity]]. }
split; [kept_solve|]. split; [kept_solve|]. split; [kept_solve|].
intros r Hr. unfold art_ic_kept in Hr. decompose [and] Hr. kept_solve.
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_art_ic_it_24 := (ltac2:(TCodec.tc2 tcn__JbtInitCache "U4&:y5'Q<yR0%211%5241'2y8%611%311p061'9'5&Fr4(Q:+;(3%33A21%6251&Q;&Jr1+Ql8%3221%52F1%>3F71r5+=%>3L1<%A231+h0%<2M1%E3M31r6+?%E3Q31C%H231+8%C2Q41%L3Q431r7+@%L3Q:1J%O231%I2Q::%Q23Q:21r8+A%Q23Q@1Q0%Q5231+QP0%Q02QA1%Q93QA31r9+5%Q93QG1Q7%Q<231%Q62QG@%Q?3QG21r:+6%Q?3QM1Q=%QB231%Q<2QM@%QE3QM21r;+7%QE3R31QC%QH231+`0%QC2R41%QL3R431&K+TP0%221E&L%QH2A3&O+2+R0%3221%6251&@&Ir=+Ra0%4432E1'6'4'A&GvQ3r@+Zk`0%R@3RL1R>/01RLr?r>%8576321&<u8u4&M+R@+H%3221%RF2F1+4%RH221&C%116%<4:?31%RL26R;&E%11:%@4?431%J5IROE1C%L3Q2C1%S:2S1S5+QnH%S42Q41%S62SG1%S?3SG41%S?2S6RO+i0%S:2SK1%SC3SK31%SC2S:RL+9%S>2SO1%SG3SO31%T21T3&B%11S@r3r2%SL221rB%SN213%T03T831p071pR>:1%QF2<1%QG2A1%QH2F1%QI2L1qRBT>1%QL2T?1p0QN1p0R41p0R<1p0R@1p0RH1p0RO1p0S61p0S>1p0SE1p0SM1p0T51pR6TE1pRDTG1pHTH1pR@TN1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_ic_it_24) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_ic_it_24) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_ic_it_24) 2%nat 0%nat).
Variable ca : ltac:(sec_ty2 constr:(SEC_T_art_ic_it_24) 3%nat 0%nat).
Lemma art_ic_it_24 : ltac:(sec_stmt2 constr:(SEC_T_art_ic_it_24) 4%nat 0%nat).
Proof using Type regs M rom ca.
intros H11 H13 H15 H16 H17 H5 H6 H7 Hca Hca' W.
eexists. split.
{ zbft (ltac:(oF' 0x56e00%Z)) (ltac:(oD' 0x56e00%Z)).
zstep (ltac:(oF' 0x56e04%Z)) (ltac:(oD' 0x56e04%Z)).
zstep (ltac:(oF' 0x56e08%Z)) (ltac:(oD' 0x56e08%Z)).
zbft (ltac:(oF' 0x56e0c%Z)) (ltac:(oD' 0x56e0c%Z)).
zstep (ltac:(oF' 0x56e10%Z)) (ltac:(oD' 0x56e10%Z)).
zstep (ltac:(oF' 0x56e14%Z)) (ltac:(oD' 0x56e14%Z)).
zstep (ltac:(oF' 0x56e18%Z)) (ltac:(oD' 0x56e18%Z)).
zstep (ltac:(oF' 0x56e1c%Z)) (ltac:(oD' 0x56e1c%Z)).
zstep (ltac:(oF' 0x56e20%Z)) (ltac:(oD' 0x56e20%Z)).
zstep (ltac:(oF' 0x56e24%Z)) (ltac:(oD' 0x56e24%Z)).
zstep (ltac:(oF' 0x56e28%Z)) (ltac:(oD' 0x56e28%Z)).
zstep (ltac:(oF' 0x56e2c%Z)) (ltac:(oD' 0x56e2c%Z)).
zstep (ltac:(oF' 0x56e30%Z)) (ltac:(oD' 0x56e30%Z)).
zbtk (ltac:(oF' 0x56e34%Z)) (ltac:(oD' 0x56e34%Z)).
zstep (ltac:(oF' 0x56ddc%Z)) (ltac:(oD' 0x56ddc%Z)).
zstep (ltac:(oF' 0x56de0%Z)) (ltac:(oD' 0x56de0%Z)).
zstep (ltac:(oF' 0x56de4%Z)) (ltac:(oD' 0x56de4%Z)).
zstep (ltac:(oF' 0x56de8%Z)) (ltac:(oD' 0x56de8%Z)).
zstep (ltac:(oF' 0x56dec%Z)) (ltac:(oD' 0x56dec%Z)).
zsw (ltac:(oF' 0x56df0%Z)) (ltac:(oD' 0x56df0%Z)) (ca + 80 * 24 + 4) (art_ic_mc 24) ltac:(rewok W).
zsd (ltac:(oF' 0x56df4%Z)) (ltac:(oD' 0x56df4%Z)) (ca + 80 * 24 + 8) (art_ic_size 24) ltac:(rewok W).
zstep (ltac:(oF' 0x56df8%Z)) (ltac:(oD' 0x56df8%Z)).
zbft (ltac:(oF' 0x56dfc%Z)) (ltac:(oD' 0x56dfc%Z)).
first [apply mst_refl | apply art_msteps_of_eq; apply art_mkst_eq; [reflexivity | zval | reflexivity]]. }
split; [kept_solve|]. split; [kept_solve|]. split; [kept_solve|].
intros r Hr. unfold art_ic_kept in Hr. decompose [and] Hr. kept_solve.
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_art_ic_it_25 := (ltac2:(TCodec.tc2 tcn__JbtInitCache "U5&:y5'Q<yR0%211%5241'2y8%611%311p061'9'5&Fr4(Q:+;(3%33A21%6251&Q;&Jr1+QnH%3221%52F1%>3F71r5+=%>3L1<%A231+i0%<2M1%E3M31r6+?%E3Q31C%H231+9%C2Q41%L3Q431r7+@%L3Q:1J%O231%I2Q::%Q23Q:21r8+A%Q23Q@1Q0%Q5231+QP0%Q02QA1%Q93QA31r9+5%Q93QG1Q7%Q<231%Q62QG@%Q?3QG21r:+6%Q?3QM1Q=%QB231%Q<2QM@%QE3QM21r;+7%QE3R31QC%QH231+`0%QC2R41%QL3R431&K+TP0%221E&L%QH2A3&O+2+R0%3221%6251&@&Ir=+Ra0%4432E1'6'4'A&GvQ3r@+Zk`0%R@3RL1R>/01RLr?r>%8576321&<u8u4&M+R@+I%3221%RF2F1+4%RH221&C%116%<4:?31+8%RM271&E%11;%A4@531%K5JS0F1D%M3Q3D1%S;2S2S6+RQ8%S52Q51%S72SH1%S@3SH41%S@2S7S0+j0%S;2SL1%SD3SL31%SD2S;RM+:%S?2T01%SH3T031%T31T4&B%11SAr3r2%SM221rB%SO213%T13T931p071pR>:1%QG2<1%QH2A1%QI2F1%QJ2L1qRBT?1%QM2T@1p0QO1p0R51p0R=1p0RA1p0RI1p0S01p0S71p0S?1p0SF1p0SN1p0T61pR6TF1pRDTH1pHTI1pR@TO1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_ic_it_25) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_ic_it_25) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_ic_it_25) 2%nat 0%nat).
Variable ca : ltac:(sec_ty2 constr:(SEC_T_art_ic_it_25) 3%nat 0%nat).
Lemma art_ic_it_25 : ltac:(sec_stmt2 constr:(SEC_T_art_ic_it_25) 4%nat 0%nat).
Proof using Type regs M rom ca.
intros H11 H13 H15 H16 H17 H5 H6 H7 Hca Hca' W.
eexists. split.
{ zbft (ltac:(oF' 0x56e00%Z)) (ltac:(oD' 0x56e00%Z)).
zstep (ltac:(oF' 0x56e04%Z)) (ltac:(oD' 0x56e04%Z)).
zstep (ltac:(oF' 0x56e08%Z)) (ltac:(oD' 0x56e08%Z)).
zbft (ltac:(oF' 0x56e0c%Z)) (ltac:(oD' 0x56e0c%Z)).
zstep (ltac:(oF' 0x56e10%Z)) (ltac:(oD' 0x56e10%Z)).
zstep (ltac:(oF' 0x56e14%Z)) (ltac:(oD' 0x56e14%Z)).
zstep (ltac:(oF' 0x56e18%Z)) (ltac:(oD' 0x56e18%Z)).
zstep (ltac:(oF' 0x56e1c%Z)) (ltac:(oD' 0x56e1c%Z)).
zstep (ltac:(oF' 0x56e20%Z)) (ltac:(oD' 0x56e20%Z)).
zstep (ltac:(oF' 0x56e24%Z)) (ltac:(oD' 0x56e24%Z)).
zstep (ltac:(oF' 0x56e28%Z)) (ltac:(oD' 0x56e28%Z)).
zstep (ltac:(oF' 0x56e2c%Z)) (ltac:(oD' 0x56e2c%Z)).
zstep (ltac:(oF' 0x56e30%Z)) (ltac:(oD' 0x56e30%Z)).
zbtk (ltac:(oF' 0x56e34%Z)) (ltac:(oD' 0x56e34%Z)).
zstep (ltac:(oF' 0x56ddc%Z)) (ltac:(oD' 0x56ddc%Z)).
zstep (ltac:(oF' 0x56de0%Z)) (ltac:(oD' 0x56de0%Z)).
zstep (ltac:(oF' 0x56de4%Z)) (ltac:(oD' 0x56de4%Z)).
zstep (ltac:(oF' 0x56de8%Z)) (ltac:(oD' 0x56de8%Z)).
zstep (ltac:(oF' 0x56dec%Z)) (ltac:(oD' 0x56dec%Z)).
zsw (ltac:(oF' 0x56df0%Z)) (ltac:(oD' 0x56df0%Z)) (ca + 80 * 25 + 4) (art_ic_mc 25) ltac:(rewok W).
zsd (ltac:(oF' 0x56df4%Z)) (ltac:(oD' 0x56df4%Z)) (ca + 80 * 25 + 8) (art_ic_size 25) ltac:(rewok W).
zstep (ltac:(oF' 0x56df8%Z)) (ltac:(oD' 0x56df8%Z)).
zbft (ltac:(oF' 0x56dfc%Z)) (ltac:(oD' 0x56dfc%Z)).
first [apply mst_refl | apply art_msteps_of_eq; apply art_mkst_eq; [reflexivity | zval | reflexivity]]. }
split; [kept_solve|]. split; [kept_solve|]. split; [kept_solve|].
intros r Hr. unfold art_ic_kept in Hr. decompose [and] Hr. kept_solve.
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_art_ic_it_26 := (ltac2:(TCodec.tc2 tcn__JbtInitCache "U4&:y5'Q<yR0%211%5241'2y8%611%311p061'9'5&Fr4(Q:+;(3%33A21%6251&Q;&Jr1+RQ8%3221%52F1%>3F71r5+=%>3L1<%A231+j0%<2M1%E3M31r6+?%E3Q31C%H231+:%C2Q41%L3Q431r7+@%L3Q:1J%O231%I2Q::%Q23Q:21r8+A%Q23Q@1Q0%Q5231+QP0%Q02QA1%Q93QA31r9+5%Q93QG1Q7%Q<231%Q62QG@%Q?3QG21r:+6%Q?3QM1Q=%QB231%Q<2QM@%QE3QM21r;+7%QE3R31QC%QH231+`0%QC2R41%QL3R431&K+TP0%221E&L%QH2A3&O+2+R0%3221%6251&@&Ir=+Ra0%4432E1'6'4'A&GvQ3r@+Zk`0%R@3RL1R>/01RLr?r>%8576321&<u8u4&M+R@+J%3221%RF2F1+4%RH221&C%116%<4:?31+8%RM271&E%11;%A4@531%K5JS0F1D%M3Q3D1%S;2S2S6+RSH%S52Q51%S72SH1%S@3SH41%S@2S7S0+k0%S;2SL1%SD3SL31%SD2S;RM%S>2SOSB%SG3SO21%T21T3&B%11S@r3r2%SL221rB%SN213%T03T831p071pR>:1%QF2<1%QG2@1%QH2E1%QI2K1qRBT>1%QL2T?1p0QN1p0R41p0R<1p0R@1p0RH1p0RO1p0S61p0S>1p0SE1p0SM1p0T51pR6TE1pRDTG1pHTH1pR@TN1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_ic_it_26) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_ic_it_26) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_ic_it_26) 2%nat 0%nat).
Variable ca : ltac:(sec_ty2 constr:(SEC_T_art_ic_it_26) 3%nat 0%nat).
Lemma art_ic_it_26 : ltac:(sec_stmt2 constr:(SEC_T_art_ic_it_26) 4%nat 0%nat).
Proof using Type regs M rom ca.
intros H11 H13 H15 H16 H17 H5 H6 H7 Hca Hca' W.
eexists. split.
{ zbft (ltac:(oF' 0x56e00%Z)) (ltac:(oD' 0x56e00%Z)).
zstep (ltac:(oF' 0x56e04%Z)) (ltac:(oD' 0x56e04%Z)).
zstep (ltac:(oF' 0x56e08%Z)) (ltac:(oD' 0x56e08%Z)).
zbft (ltac:(oF' 0x56e0c%Z)) (ltac:(oD' 0x56e0c%Z)).
zstep (ltac:(oF' 0x56e10%Z)) (ltac:(oD' 0x56e10%Z)).
zstep (ltac:(oF' 0x56e14%Z)) (ltac:(oD' 0x56e14%Z)).
zstep (ltac:(oF' 0x56e18%Z)) (ltac:(oD' 0x56e18%Z)).
zstep (ltac:(oF' 0x56e1c%Z)) (ltac:(oD' 0x56e1c%Z)).
zstep (ltac:(oF' 0x56e20%Z)) (ltac:(oD' 0x56e20%Z)).
zstep (ltac:(oF' 0x56e24%Z)) (ltac:(oD' 0x56e24%Z)).
zstep (ltac:(oF' 0x56e28%Z)) (ltac:(oD' 0x56e28%Z)).
zstep (ltac:(oF' 0x56e2c%Z)) (ltac:(oD' 0x56e2c%Z)).
zstep (ltac:(oF' 0x56e30%Z)) (ltac:(oD' 0x56e30%Z)).
zbtk (ltac:(oF' 0x56e34%Z)) (ltac:(oD' 0x56e34%Z)).
zstep (ltac:(oF' 0x56ddc%Z)) (ltac:(oD' 0x56ddc%Z)).
zstep (ltac:(oF' 0x56de0%Z)) (ltac:(oD' 0x56de0%Z)).
zstep (ltac:(oF' 0x56de4%Z)) (ltac:(oD' 0x56de4%Z)).
zstep (ltac:(oF' 0x56de8%Z)) (ltac:(oD' 0x56de8%Z)).
zstep (ltac:(oF' 0x56dec%Z)) (ltac:(oD' 0x56dec%Z)).
zsw (ltac:(oF' 0x56df0%Z)) (ltac:(oD' 0x56df0%Z)) (ca + 80 * 26 + 4) (art_ic_mc 26) ltac:(rewok W).
zsd (ltac:(oF' 0x56df4%Z)) (ltac:(oD' 0x56df4%Z)) (ca + 80 * 26 + 8) (art_ic_size 26) ltac:(rewok W).
zstep (ltac:(oF' 0x56df8%Z)) (ltac:(oD' 0x56df8%Z)).
zbft (ltac:(oF' 0x56dfc%Z)) (ltac:(oD' 0x56dfc%Z)).
first [apply mst_refl | apply art_msteps_of_eq; apply art_mkst_eq; [reflexivity | zval | reflexivity]]. }
split; [kept_solve|]. split; [kept_solve|]. split; [kept_solve|].
intros r Hr. unfold art_ic_kept in Hr. decompose [and] Hr. kept_solve.
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_art_ic_it_27 := (ltac2:(TCodec.tc2 tcn__JbtInitCache "U4&:y5'Q<yR0%211%5241'2y8%611%311p061'9'5&Fr4(Q:+;(3%33A21%6251&Q;&Jr1+RSH%3221%52F1%>3F71r5+=%>3L1<%A231+k0%<2M1%E3M31r6+?%E3Q31C%H231%B2Q3F%K3Q321r7+@%K3Q91I%N231%H2Q99%Q13Q921r8+A%Q13Q?1O%Q4231+QP0%O2Q@1%Q83Q@31r9+5%Q83QF1Q6%Q;231%Q52QF@%Q>3QF21r:+6%Q>3QL1Q<%QA231%Q;2QL@%QD3QL21r;+7%QD3R21QB%QG231+`0%QB2R31%QK3R331&K+TP0%221E&L%QG2A3&O+2+R0%3221%6251&@&Ir=+Ra0%4432E1'6'4'A&GvQ3r@+Zk`0%R?3RK1R=/01RKr?r>%8576321&<u8u4&M+R@+K%3221%RE2F1+4%RG221&C%116%<4:?31+8%RL271&E%11;%A4@531%K5JROF1D%M3Q3D1%S:2S1S5+RV8%S42Q51%S62SG1%S?3SG41%S?2S6RO+l0%S:2SK1%SC3SK31%SC2S:RL+<%S>2SO1%SG3SO31%T21T3&B%11S@r3r2%SL221rB%SN213%T03T831p071pR>:1%QG2<1%QH2A1%QI2F1%QJ2L1qRBT>1%QM2T?1p0QO1p0R51p0R=1p0RA1p0RI1p0S01p0S71p0S?1p0SF1p0SM1p0T51pR6TE1pRDTG1pHTH1pR@TN1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_ic_it_27) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_ic_it_27) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_ic_it_27) 2%nat 0%nat).
Variable ca : ltac:(sec_ty2 constr:(SEC_T_art_ic_it_27) 3%nat 0%nat).
Lemma art_ic_it_27 : ltac:(sec_stmt2 constr:(SEC_T_art_ic_it_27) 4%nat 0%nat).
Proof using Type regs M rom ca.
intros H11 H13 H15 H16 H17 H5 H6 H7 Hca Hca' W.
eexists. split.
{ zbft (ltac:(oF' 0x56e00%Z)) (ltac:(oD' 0x56e00%Z)).
zstep (ltac:(oF' 0x56e04%Z)) (ltac:(oD' 0x56e04%Z)).
zstep (ltac:(oF' 0x56e08%Z)) (ltac:(oD' 0x56e08%Z)).
zbft (ltac:(oF' 0x56e0c%Z)) (ltac:(oD' 0x56e0c%Z)).
zstep (ltac:(oF' 0x56e10%Z)) (ltac:(oD' 0x56e10%Z)).
zstep (ltac:(oF' 0x56e14%Z)) (ltac:(oD' 0x56e14%Z)).
zstep (ltac:(oF' 0x56e18%Z)) (ltac:(oD' 0x56e18%Z)).
zstep (ltac:(oF' 0x56e1c%Z)) (ltac:(oD' 0x56e1c%Z)).
zstep (ltac:(oF' 0x56e20%Z)) (ltac:(oD' 0x56e20%Z)).
zstep (ltac:(oF' 0x56e24%Z)) (ltac:(oD' 0x56e24%Z)).
zstep (ltac:(oF' 0x56e28%Z)) (ltac:(oD' 0x56e28%Z)).
zstep (ltac:(oF' 0x56e2c%Z)) (ltac:(oD' 0x56e2c%Z)).
zstep (ltac:(oF' 0x56e30%Z)) (ltac:(oD' 0x56e30%Z)).
zbtk (ltac:(oF' 0x56e34%Z)) (ltac:(oD' 0x56e34%Z)).
zstep (ltac:(oF' 0x56ddc%Z)) (ltac:(oD' 0x56ddc%Z)).
zstep (ltac:(oF' 0x56de0%Z)) (ltac:(oD' 0x56de0%Z)).
zstep (ltac:(oF' 0x56de4%Z)) (ltac:(oD' 0x56de4%Z)).
zstep (ltac:(oF' 0x56de8%Z)) (ltac:(oD' 0x56de8%Z)).
zstep (ltac:(oF' 0x56dec%Z)) (ltac:(oD' 0x56dec%Z)).
zsw (ltac:(oF' 0x56df0%Z)) (ltac:(oD' 0x56df0%Z)) (ca + 80 * 27 + 4) (art_ic_mc 27) ltac:(rewok W).
zsd (ltac:(oF' 0x56df4%Z)) (ltac:(oD' 0x56df4%Z)) (ca + 80 * 27 + 8) (art_ic_size 27) ltac:(rewok W).
zstep (ltac:(oF' 0x56df8%Z)) (ltac:(oD' 0x56df8%Z)).
zbft (ltac:(oF' 0x56dfc%Z)) (ltac:(oD' 0x56dfc%Z)).
first [apply mst_refl | apply art_msteps_of_eq; apply art_mkst_eq; [reflexivity | zval | reflexivity]]. }
split; [kept_solve|]. split; [kept_solve|]. split; [kept_solve|].
intros r Hr. unfold art_ic_kept in Hr. decompose [and] Hr. kept_solve.
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_art_ic_it_28 := (ltac2:(TCodec.tc2 tcn__JbtInitCache "U4&:y5'Q<yR0%211%5241'2y8%611%311p061'9'5&Fr4(Q:+;(3%33A21%6251&Q;&Jr1+RV8%3221%52F1%>3F71r5+=%>3L1<%A231+l0%<2M1%E3M31r6+?%E3Q31C%H231+<%C2Q41%L3Q431r7+@%L3Q:1J%O231%I2Q::%Q23Q:21r8+A%Q23Q@1Q0%Q5231+QP0%Q02QA1%Q93QA31r9+5%Q93QG1Q7%Q<231%Q62QG@%Q?3QG21r:+6%Q?3QM1Q=%QB231%Q<2QM@%QE3QM21r;+7%QE3R31QC%QH231+`0%QC2R41%QL3R431&K+TP0%221E&L%QH2A3&O+2+R0%3221%6251&@&Ir=+Ra0%4432E1'6'4'A&GvQ3r@+Zk`0%R@3RL1R>/01RLr?r>%8576321&<u8u4&M+R@+L%3221%RF2F1+4%RH221&C%116%<4:?31+8%RM271&E%11;%A4@531%K5JS0F1D%M3Q3D1%S;2S2S6+RXH%S52Q51%S72SH1%S@3SH41%S@2S7S0+m0%S;2SL1%SD3SL31%SD2S;RM%S>2SOS6%SG3SO21%T21T3&B%11S@r3r2%SL221rB%SN213%T03T831p071pR>:1%QF2<1%QG2@1%QH2E1%QI2K1qRBT>1%QL2T?1p0QN1p0R41p0R<1p0R@1p0RH1p0RO1p0S61p0S>1p0SE1p0SM1p0T51pR6TE1pRDTG1pHTH1pR@TN1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_ic_it_28) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_ic_it_28) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_ic_it_28) 2%nat 0%nat).
Variable ca : ltac:(sec_ty2 constr:(SEC_T_art_ic_it_28) 3%nat 0%nat).
Lemma art_ic_it_28 : ltac:(sec_stmt2 constr:(SEC_T_art_ic_it_28) 4%nat 0%nat).
Proof using Type regs M rom ca.
intros H11 H13 H15 H16 H17 H5 H6 H7 Hca Hca' W.
eexists. split.
{ zbft (ltac:(oF' 0x56e00%Z)) (ltac:(oD' 0x56e00%Z)).
zstep (ltac:(oF' 0x56e04%Z)) (ltac:(oD' 0x56e04%Z)).
zstep (ltac:(oF' 0x56e08%Z)) (ltac:(oD' 0x56e08%Z)).
zbft (ltac:(oF' 0x56e0c%Z)) (ltac:(oD' 0x56e0c%Z)).
zstep (ltac:(oF' 0x56e10%Z)) (ltac:(oD' 0x56e10%Z)).
zstep (ltac:(oF' 0x56e14%Z)) (ltac:(oD' 0x56e14%Z)).
zstep (ltac:(oF' 0x56e18%Z)) (ltac:(oD' 0x56e18%Z)).
zstep (ltac:(oF' 0x56e1c%Z)) (ltac:(oD' 0x56e1c%Z)).
zstep (ltac:(oF' 0x56e20%Z)) (ltac:(oD' 0x56e20%Z)).
zstep (ltac:(oF' 0x56e24%Z)) (ltac:(oD' 0x56e24%Z)).
zstep (ltac:(oF' 0x56e28%Z)) (ltac:(oD' 0x56e28%Z)).
zstep (ltac:(oF' 0x56e2c%Z)) (ltac:(oD' 0x56e2c%Z)).
zstep (ltac:(oF' 0x56e30%Z)) (ltac:(oD' 0x56e30%Z)).
zbtk (ltac:(oF' 0x56e34%Z)) (ltac:(oD' 0x56e34%Z)).
zstep (ltac:(oF' 0x56ddc%Z)) (ltac:(oD' 0x56ddc%Z)).
zstep (ltac:(oF' 0x56de0%Z)) (ltac:(oD' 0x56de0%Z)).
zstep (ltac:(oF' 0x56de4%Z)) (ltac:(oD' 0x56de4%Z)).
zstep (ltac:(oF' 0x56de8%Z)) (ltac:(oD' 0x56de8%Z)).
zstep (ltac:(oF' 0x56dec%Z)) (ltac:(oD' 0x56dec%Z)).
zsw (ltac:(oF' 0x56df0%Z)) (ltac:(oD' 0x56df0%Z)) (ca + 80 * 28 + 4) (art_ic_mc 28) ltac:(rewok W).
zsd (ltac:(oF' 0x56df4%Z)) (ltac:(oD' 0x56df4%Z)) (ca + 80 * 28 + 8) (art_ic_size 28) ltac:(rewok W).
zstep (ltac:(oF' 0x56df8%Z)) (ltac:(oD' 0x56df8%Z)).
zbft (ltac:(oF' 0x56dfc%Z)) (ltac:(oD' 0x56dfc%Z)).
first [apply mst_refl | apply art_msteps_of_eq; apply art_mkst_eq; [reflexivity | zval | reflexivity]]. }
split; [kept_solve|]. split; [kept_solve|]. split; [kept_solve|].
intros r Hr. unfold art_ic_kept in Hr. decompose [and] Hr. kept_solve.
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_art_ic_it_29 := (ltac2:(TCodec.tc2 tcn__JbtInitCache "U4&:y5'Q<yR0%211%5241'2y8%611%311p061'9'5&Fr4(Q:+;(3%33A21%6251&Q;&Jr1+RXH%3221%52F1%>3F71r5+=%>3L1<%A231+m0%<2M1%E3M31r6+?%E3Q31C%H231%B2Q3:%K3Q321r7+@%K3Q91I%N231%H2Q99%Q13Q921r8+A%Q13Q?1O%Q4231+QP0%O2Q@1%Q83Q@31r9+5%Q83QF1Q6%Q;231%Q52QF@%Q>3QF21r:+6%Q>3QL1Q<%QA231%Q;2QL@%QD3QL21r;+7%QD3R21QB%QG231+`0%QB2R31%QK3R331&K+TP0%221E&L%QG2A3&O+2+R0%3221%6251&@&Ir=+Ra0%4432E1'6'4'A&GvQ3r@+Zk`0%R?3RK1R=/01RKr?r>%8576321&<u8u4&M+R@+M%3221%RE2F1+4%RG221&C%116%<4:?31+8%RL271&E%11;%A4@531%K5JROF1D%M3Q3D1%S:2S1S5+R[8%S42Q51%S62SG1%S?3SG41%S?2S6RO+n0%S:2SK1%SC3SK31%SC2S:RL+>%S>2SO1%SG3SO31%T21T3&B%11S@r3r2%SL221rB%SN213%T03T831p071pR>:1%QG2<1%QH2A1%QI2F1%QJ2L1qRBT>1%QM2T?1p0QO1p0R51p0R=1p0RA1p0RI1p0S01p0S71p0S?1p0SF1p0SM1p0T51pR6TE1pRDTG1pHTH1pR@TN1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_ic_it_29) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_ic_it_29) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_ic_it_29) 2%nat 0%nat).
Variable ca : ltac:(sec_ty2 constr:(SEC_T_art_ic_it_29) 3%nat 0%nat).
Lemma art_ic_it_29 : ltac:(sec_stmt2 constr:(SEC_T_art_ic_it_29) 4%nat 0%nat).
Proof using Type regs M rom ca.
intros H11 H13 H15 H16 H17 H5 H6 H7 Hca Hca' W.
eexists. split.
{ zbft (ltac:(oF' 0x56e00%Z)) (ltac:(oD' 0x56e00%Z)).
zstep (ltac:(oF' 0x56e04%Z)) (ltac:(oD' 0x56e04%Z)).
zstep (ltac:(oF' 0x56e08%Z)) (ltac:(oD' 0x56e08%Z)).
zbft (ltac:(oF' 0x56e0c%Z)) (ltac:(oD' 0x56e0c%Z)).
zstep (ltac:(oF' 0x56e10%Z)) (ltac:(oD' 0x56e10%Z)).
zstep (ltac:(oF' 0x56e14%Z)) (ltac:(oD' 0x56e14%Z)).
zstep (ltac:(oF' 0x56e18%Z)) (ltac:(oD' 0x56e18%Z)).
zstep (ltac:(oF' 0x56e1c%Z)) (ltac:(oD' 0x56e1c%Z)).
zstep (ltac:(oF' 0x56e20%Z)) (ltac:(oD' 0x56e20%Z)).
zstep (ltac:(oF' 0x56e24%Z)) (ltac:(oD' 0x56e24%Z)).
zstep (ltac:(oF' 0x56e28%Z)) (ltac:(oD' 0x56e28%Z)).
zstep (ltac:(oF' 0x56e2c%Z)) (ltac:(oD' 0x56e2c%Z)).
zstep (ltac:(oF' 0x56e30%Z)) (ltac:(oD' 0x56e30%Z)).
zbtk (ltac:(oF' 0x56e34%Z)) (ltac:(oD' 0x56e34%Z)).
zstep (ltac:(oF' 0x56ddc%Z)) (ltac:(oD' 0x56ddc%Z)).
zstep (ltac:(oF' 0x56de0%Z)) (ltac:(oD' 0x56de0%Z)).
zstep (ltac:(oF' 0x56de4%Z)) (ltac:(oD' 0x56de4%Z)).
zstep (ltac:(oF' 0x56de8%Z)) (ltac:(oD' 0x56de8%Z)).
zstep (ltac:(oF' 0x56dec%Z)) (ltac:(oD' 0x56dec%Z)).
zsw (ltac:(oF' 0x56df0%Z)) (ltac:(oD' 0x56df0%Z)) (ca + 80 * 29 + 4) (art_ic_mc 29) ltac:(rewok W).
zsd (ltac:(oF' 0x56df4%Z)) (ltac:(oD' 0x56df4%Z)) (ca + 80 * 29 + 8) (art_ic_size 29) ltac:(rewok W).
zstep (ltac:(oF' 0x56df8%Z)) (ltac:(oD' 0x56df8%Z)).
zbft (ltac:(oF' 0x56dfc%Z)) (ltac:(oD' 0x56dfc%Z)).
first [apply mst_refl | apply art_msteps_of_eq; apply art_mkst_eq; [reflexivity | zval | reflexivity]]. }
split; [kept_solve|]. split; [kept_solve|]. split; [kept_solve|].
intros r Hr. unfold art_ic_kept in Hr. decompose [and] Hr. kept_solve.
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_art_ic_it_30 := (ltac2:(TCodec.tc2 tcn__JbtInitCache "U3&:y5'Q<yR0%211%5241'2y8%611%311p061'9'5&Fr4(Q:+;(3%33A21%6251&Q;&Jr1+R[8%3221%52F1%>3F71r5+=%>3L1<%A231+n0%<2M1%E3M31r6+?%E3Q31C%H231+>%C2Q41%L3Q431r7+@%L3Q:1J%O231%I2Q::%Q23Q:21r8+A%Q23Q@1Q0%Q5231+QP0%Q02QA1%Q93QA31r9+5%Q93QG1Q7%Q<231%Q62QG@%Q?3QG21r:+6%Q?3QM1Q=%QB231%Q<2QM@%QE3QM21r;+7%QE3R31QC%QH231+`0%QC2R41%QL3R431&K+TP0%221E&L%QH2A3&O+2+R0%3221%6251&@&Ir=+Ra0%4432E1'6'4'A&GvQ3r@+Zk`0%R@3RL1R>/01RLr?r>%8576321&<u8u4&M+R@+N%3221%RF2F1+4%RH221&C%116%<4:?31+8%RM271&E%11;%A4@531%K5JS0F1D%M3Q3D1%S;2S2S6+R]H%S52Q51%S72SH1%S@3SH41%S@2S7S0+o0%S;2SL1%SD3SL31%SD2S;RM%SF3SN1RE%T11T2&B%11S?r3r2%SK221rB%SM213%SO3T731p071pR>:1%QE2<1%QF2?1%QG2D1%QH2J1qRBT=1%QK2T>1p0QM1p0R31p0R;1p0R?1p0RG1p0RN1p0S51p0S=1p0SD1p0SL1p0T41pR6TD1pRDTF1pHTG1pR@TM1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_ic_it_30) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_ic_it_30) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_ic_it_30) 2%nat 0%nat).
Variable ca : ltac:(sec_ty2 constr:(SEC_T_art_ic_it_30) 3%nat 0%nat).
Lemma art_ic_it_30 : ltac:(sec_stmt2 constr:(SEC_T_art_ic_it_30) 4%nat 0%nat).
Proof using Type regs M rom ca.
intros H11 H13 H15 H16 H17 H5 H6 H7 Hca Hca' W.
eexists. split.
{ zbft (ltac:(oF' 0x56e00%Z)) (ltac:(oD' 0x56e00%Z)).
zstep (ltac:(oF' 0x56e04%Z)) (ltac:(oD' 0x56e04%Z)).
zstep (ltac:(oF' 0x56e08%Z)) (ltac:(oD' 0x56e08%Z)).
zbft (ltac:(oF' 0x56e0c%Z)) (ltac:(oD' 0x56e0c%Z)).
zstep (ltac:(oF' 0x56e10%Z)) (ltac:(oD' 0x56e10%Z)).
zstep (ltac:(oF' 0x56e14%Z)) (ltac:(oD' 0x56e14%Z)).
zstep (ltac:(oF' 0x56e18%Z)) (ltac:(oD' 0x56e18%Z)).
zstep (ltac:(oF' 0x56e1c%Z)) (ltac:(oD' 0x56e1c%Z)).
zstep (ltac:(oF' 0x56e20%Z)) (ltac:(oD' 0x56e20%Z)).
zstep (ltac:(oF' 0x56e24%Z)) (ltac:(oD' 0x56e24%Z)).
zstep (ltac:(oF' 0x56e28%Z)) (ltac:(oD' 0x56e28%Z)).
zstep (ltac:(oF' 0x56e2c%Z)) (ltac:(oD' 0x56e2c%Z)).
zstep (ltac:(oF' 0x56e30%Z)) (ltac:(oD' 0x56e30%Z)).
zbtk (ltac:(oF' 0x56e34%Z)) (ltac:(oD' 0x56e34%Z)).
zstep (ltac:(oF' 0x56ddc%Z)) (ltac:(oD' 0x56ddc%Z)).
zstep (ltac:(oF' 0x56de0%Z)) (ltac:(oD' 0x56de0%Z)).
zstep (ltac:(oF' 0x56de4%Z)) (ltac:(oD' 0x56de4%Z)).
zstep (ltac:(oF' 0x56de8%Z)) (ltac:(oD' 0x56de8%Z)).
zstep (ltac:(oF' 0x56dec%Z)) (ltac:(oD' 0x56dec%Z)).
zsw (ltac:(oF' 0x56df0%Z)) (ltac:(oD' 0x56df0%Z)) (ca + 80 * 30 + 4) (art_ic_mc 30) ltac:(rewok W).
zsd (ltac:(oF' 0x56df4%Z)) (ltac:(oD' 0x56df4%Z)) (ca + 80 * 30 + 8) (art_ic_size 30) ltac:(rewok W).
zstep (ltac:(oF' 0x56df8%Z)) (ltac:(oD' 0x56df8%Z)).
zbft (ltac:(oF' 0x56dfc%Z)) (ltac:(oD' 0x56dfc%Z)).
first [apply mst_refl | apply art_msteps_of_eq; apply art_mkst_eq; [reflexivity | zval | reflexivity]]. }
split; [kept_solve|]. split; [kept_solve|]. split; [kept_solve|].
intros r Hr. unfold art_ic_kept in Hr. decompose [and] Hr. kept_solve.
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_art_ic_it_31 := (ltac2:(TCodec.tc2 tcn__JbtInitCache "U2&:y5'Q<yR0%211%5241'2y8%611%311p061'9'5&Fr4(Q:+;(3%33A21%6251&Q;&Jr1+R]H%3221%52F1%>3F71r5+=%>3L1<%A231+o0%<2M1%E3M31r6+?%E3Q31C%H231%B2Q33%K3Q321r7+@%K3Q91I%N231%Q03Q816r8+A%Q03Q>1N%Q3231+QP0%N2Q?1%Q73Q?31r9+5%Q73QE1Q5%Q:231%Q42QE?%Q=3QE21r:+6%Q=3QK1Q;%Q@231%Q:2QK@%QC3QK21r;+7%QC3R11QA%QF231+`0%QA2R21%QJ3R231&K+TP0%221E&L%QF2A3&O+2+R0%3221%6251&@&Ir=+Ra0%4432E1'6'4'A&GvQ3r@+Zk`0%R>3RJ1R</01RJr?r>%8576321+ZkbD%RD3S01RB/01S0&<u8u4&M+R@+O%3221%RG2I1+4%RI221&C%116%<4:B31+8%RN271&E%11;%A4@531%N5MS1C1G%Q03Q6G1%S<2S3S7+R`8%S62Q81%S82SI1%SA3SI41%SA2S8S1%SC3SK1R=%SC2S:RL%SE3SM1R9%T01T1&B%11S>r3r2%SJ221rB%SL213%SN3T631p071pR>:1%QF2<1%QG2?1%QH2B1%QI2H1qRBT<1%QL2T=1p0QN1p0R41p0R<1p0R@1p0RH1p0RO1p0S61p0S>1p0SD1p0SK1p0T31pR6TC1pRDTE1pHTF1pR@TL1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_ic_it_31) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_ic_it_31) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_ic_it_31) 2%nat 0%nat).
Variable ca : ltac:(sec_ty2 constr:(SEC_T_art_ic_it_31) 3%nat 0%nat).
Lemma art_ic_it_31 : ltac:(sec_stmt2 constr:(SEC_T_art_ic_it_31) 4%nat 0%nat).
Proof using Type regs M rom ca.
intros H11 H13 H15 H16 H17 H5 H6 H7 Hca Hca' W.
eexists. split.
{ zbtk (ltac:(oF' 0x56e00%Z)) (ltac:(oD' 0x56e00%Z)).
zstep (ltac:(oF' 0x56e40%Z)) (ltac:(oD' 0x56e40%Z)).
zstep (ltac:(oF' 0x56e44%Z)) (ltac:(oD' 0x56e44%Z)).
zstep (ltac:(oF' 0x56e48%Z)) (ltac:(oD' 0x56e48%Z)).
zbft (ltac:(oF' 0x56e4c%Z)) (ltac:(oD' 0x56e4c%Z)).
stepn (ltac:(oF' 0x56e50%Z)) (ltac:(oD' 0x56e50%Z)).
zstep (ltac:(oF' 0x56e38%Z)) (ltac:(oD' 0x56e38%Z)).
stepn (ltac:(oF' 0x56e3c%Z)) (ltac:(oD' 0x56e3c%Z)).
zstep (ltac:(oF' 0x56ddc%Z)) (ltac:(oD' 0x56ddc%Z)).
zstep (ltac:(oF' 0x56de0%Z)) (ltac:(oD' 0x56de0%Z)).
zstep (ltac:(oF' 0x56de4%Z)) (ltac:(oD' 0x56de4%Z)).
zstep (ltac:(oF' 0x56de8%Z)) (ltac:(oD' 0x56de8%Z)).
zstep (ltac:(oF' 0x56dec%Z)) (ltac:(oD' 0x56dec%Z)).
zsw (ltac:(oF' 0x56df0%Z)) (ltac:(oD' 0x56df0%Z)) (ca + 80 * 31 + 4) (art_ic_mc 31) ltac:(rewok W).
zsd (ltac:(oF' 0x56df4%Z)) (ltac:(oD' 0x56df4%Z)) (ca + 80 * 31 + 8) (art_ic_size 31) ltac:(rewok W).
zstep (ltac:(oF' 0x56df8%Z)) (ltac:(oD' 0x56df8%Z)).
zbtk (ltac:(oF' 0x56dfc%Z)) (ltac:(oD' 0x56dfc%Z)).
first [apply mst_refl | apply art_msteps_of_eq; apply art_mkst_eq; [reflexivity | zval | reflexivity]]. }
split; [kept_solve|]. split; [kept_solve|]. split; [kept_solve|].
intros r Hr. unfold art_ic_kept in Hr. decompose [and] Hr. kept_solve.
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_art_ic_loop := (ltac2:(TCodec.tc2 tcn__JbtInitCache "T9&:y5'Q<yR0%211%5241'2y8%611%311p061'9'5&Fr4(Q:+;(3%33A21%6251&Q;&Jr1+RH%3221%52F1%>3F71r5+=%>3L1<%A231+Q0%<2M1%E3M31r6+?%E3Q31C%H231+_oooooooooooA%C2Q41%L3Q431r7+@%L3Q:1J%O231%I2Q::%Q23Q:21r8+A%Q23Q@1Q0%Q5231+QP0%Q02QA1%Q93QA31r9+5%Q93QG1Q7%Q<231%Q62QG@%Q?3QG21r:+6%Q?3QM1Q=%QB231%Q<2QM@%QE3QM21r;+7%QE3R31QC%QH231+`0%QC2R41%QL3R431&K+TP0%221E&L%QH2A3&O+2+R0%3221%6251&@&Ir=+Ra0%4432E1'6'4'A&GvQ3r@+Zk`0%R@3RL1R>/01RLr?r>%8576321+ZkbD%RF3S21RD/01S2&DuO%238D1%?5>RD418%A3G81%S:1S;&B%11RHr3r2%S4221rB%S6213%S83S@31p071pR>:1%N2<1qRBSC1%Q12SD1p0Q31p0Q91p0QA1p0QE1p0QM1p0R41p0R;1p0RC1p0RJ1p0S21p0S:1pR6SJ1pRDSL1pHSM1pR@T31")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_ic_loop) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_ic_loop) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_ic_loop) 2%nat 0%nat).
Variable ca : ltac:(sec_ty2 constr:(SEC_T_art_ic_loop) 3%nat 0%nat).
Lemma art_ic_loop : ltac:(sec_stmt2 constr:(SEC_T_art_ic_loop) 4%nat 0%nat).
Proof using Type regs M rom ca.
intros A0 B0 C0 H16_0 H17_0 H5_0 H6_0 H7_0 Hca Hca' W0.
#[local] Ltac ick := unfold art_ic_kept; repeat split; intros E; discriminate E.
destruct (art_ic_it_1 regs M rom ca A0 B0 C0 H16_0 H17_0 H5_0 H6_0 H7_0 Hca Hca' W0) as (r1 & RUN1 & A1 & B1 & C1 & K1).
match type of RUN1 with msteps _ _ (mkst _ _ ?X _) => set (M1 := X) in RUN1 end.
assert (W1 : wrA M1 ca 2592) by (unfold M1; do 2 apply wr_Wn; exact W0).
assert (H16_1 : getr r1 16 = Z_to_bv 64 15) by (rewrite (K1 16%bv) by ick; exact H16_0). assert (H17_1 : getr r1 17 = Z_to_bv 64 1024) by (rewrite (K1 17%bv) by ick; exact H17_0).
assert (H5_1 : getr r1 5 = Z_to_bv 64 16) by (rewrite (K1 5%bv) by ick; exact H5_0). assert (H6_1 : getr r1 6 = Z_to_bv 64 17) by (rewrite (K1 6%bv) by ick; exact H6_0). assert (H7_1 : getr r1 7 = Z_to_bv 64 512) by (rewrite (K1 7%bv) by ick; exact H7_0).
clear A0 B0 C0 H16_0 H17_0 H5_0 H6_0 H7_0 W0.
destruct (art_ic_it_2 r1 M1 rom ca A1 B1 C1 H16_1 H17_1 H5_1 H6_1 H7_1 Hca Hca' W1) as (r2 & RUN2 & A2 & B2 & C2 & K2).
match type of RUN2 with msteps _ _ (mkst _ _ ?X _) => set (M2 := X) in RUN2 end.
assert (W2 : wrA M2 ca 2592) by (unfold M2; do 2 apply wr_Wn; exact W1).
assert (H16_2 : getr r2 16 = Z_to_bv 64 15) by (rewrite (K2 16%bv) by ick; exact H16_1). assert (H17_2 : getr r2 17 = Z_to_bv 64 1024) by (rewrite (K2 17%bv) by ick; exact H17_1).
assert (H5_2 : getr r2 5 = Z_to_bv 64 16) by (rewrite (K2 5%bv) by ick; exact H5_1). assert (H6_2 : getr r2 6 = Z_to_bv 64 17) by (rewrite (K2 6%bv) by ick; exact H6_1). assert (H7_2 : getr r2 7 = Z_to_bv 64 512) by (rewrite (K2 7%bv) by ick; exact H7_1).
clear A1 B1 C1 H16_1 H17_1 H5_1 H6_1 H7_1 W1.
destruct (art_ic_it_3 r2 M2 rom ca A2 B2 C2 H16_2 H17_2 H5_2 H6_2 H7_2 Hca Hca' W2) as (r3 & RUN3 & A3 & B3 & C3 & K3).
match type of RUN3 with msteps _ _ (mkst _ _ ?X _) => set (M3 := X) in RUN3 end.
assert (W3 : wrA M3 ca 2592) by (unfold M3; do 2 apply wr_Wn; exact W2).
assert (H16_3 : getr r3 16 = Z_to_bv 64 15) by (rewrite (K3 16%bv) by ick; exact H16_2). assert (H17_3 : getr r3 17 = Z_to_bv 64 1024) by (rewrite (K3 17%bv) by ick; exact H17_2).
assert (H5_3 : getr r3 5 = Z_to_bv 64 16) by (rewrite (K3 5%bv) by ick; exact H5_2). assert (H6_3 : getr r3 6 = Z_to_bv 64 17) by (rewrite (K3 6%bv) by ick; exact H6_2). assert (H7_3 : getr r3 7 = Z_to_bv 64 512) by (rewrite (K3 7%bv) by ick; exact H7_2).
clear A2 B2 C2 H16_2 H17_2 H5_2 H6_2 H7_2 W2.
destruct (art_ic_it_4 r3 M3 rom ca A3 B3 C3 H16_3 H17_3 H5_3 H6_3 H7_3 Hca Hca' W3) as (r4 & RUN4 & A4 & B4 & C4 & K4).
match type of RUN4 with msteps _ _ (mkst _ _ ?X _) => set (M4 := X) in RUN4 end.
assert (W4 : wrA M4 ca 2592) by (unfold M4; do 2 apply wr_Wn; exact W3).
assert (H16_4 : getr r4 16 = Z_to_bv 64 15) by (rewrite (K4 16%bv) by ick; exact H16_3). assert (H17_4 : getr r4 17 = Z_to_bv 64 1024) by (rewrite (K4 17%bv) by ick; exact H17_3).
assert (H5_4 : getr r4 5 = Z_to_bv 64 16) by (rewrite (K4 5%bv) by ick; exact H5_3). assert (H6_4 : getr r4 6 = Z_to_bv 64 17) by (rewrite (K4 6%bv) by ick; exact H6_3). assert (H7_4 : getr r4 7 = Z_to_bv 64 512) by (rewrite (K4 7%bv) by ick; exact H7_3).
clear A3 B3 C3 H16_3 H17_3 H5_3 H6_3 H7_3 W3.
destruct (art_ic_it_5 r4 M4 rom ca A4 B4 C4 H16_4 H17_4 H5_4 H6_4 H7_4 Hca Hca' W4) as (r5 & RUN5 & A5 & B5 & C5 & K5).
match type of RUN5 with msteps _ _ (mkst _ _ ?X _) => set (M5 := X) in RUN5 end.
assert (W5 : wrA M5 ca 2592) by (unfold M5; do 2 apply wr_Wn; exact W4).
assert (H16_5 : getr r5 16 = Z_to_bv 64 15) by (rewrite (K5 16%bv) by ick; exact H16_4). assert (H17_5 : getr r5 17 = Z_to_bv 64 1024) by (rewrite (K5 17%bv) by ick; exact H17_4).
assert (H5_5 : getr r5 5 = Z_to_bv 64 16) by (rewrite (K5 5%bv) by ick; exact H5_4). assert (H6_5 : getr r5 6 = Z_to_bv 64 17) by (rewrite (K5 6%bv) by ick; exact H6_4). assert (H7_5 : getr r5 7 = Z_to_bv 64 512) by (rewrite (K5 7%bv) by ick; exact H7_4).
clear A4 B4 C4 H16_4 H17_4 H5_4 H6_4 H7_4 W4.
destruct (art_ic_it_6 r5 M5 rom ca A5 B5 C5 H16_5 H17_5 H5_5 H6_5 H7_5 Hca Hca' W5) as (r6 & RUN6 & A6 & B6 & C6 & K6).
match type of RUN6 with msteps _ _ (mkst _ _ ?X _) => set (M6 := X) in RUN6 end.
assert (W6 : wrA M6 ca 2592) by (unfold M6; do 2 apply wr_Wn; exact W5).
assert (H16_6 : getr r6 16 = Z_to_bv 64 15) by (rewrite (K6 16%bv) by ick; exact H16_5). assert (H17_6 : getr r6 17 = Z_to_bv 64 1024) by (rewrite (K6 17%bv) by ick; exact H17_5).
assert (H5_6 : getr r6 5 = Z_to_bv 64 16) by (rewrite (K6 5%bv) by ick; exact H5_5). assert (H6_6 : getr r6 6 = Z_to_bv 64 17) by (rewrite (K6 6%bv) by ick; exact H6_5). assert (H7_6 : getr r6 7 = Z_to_bv 64 512) by (rewrite (K6 7%bv) by ick; exact H7_5).
clear A5 B5 C5 H16_5 H17_5 H5_5 H6_5 H7_5 W5.
destruct (art_ic_it_7 r6 M6 rom ca A6 B6 C6 H16_6 H17_6 H5_6 H6_6 H7_6 Hca Hca' W6) as (r7 & RUN7 & A7 & B7 & C7 & K7).
match type of RUN7 with msteps _ _ (mkst _ _ ?X _) => set (M7 := X) in RUN7 end.
assert (W7 : wrA M7 ca 2592) by (unfold M7; do 2 apply wr_Wn; exact W6).
assert (H16_7 : getr r7 16 = Z_to_bv 64 15) by (rewrite (K7 16%bv) by ick; exact H16_6). assert (H17_7 : getr r7 17 = Z_to_bv 64 1024) by (rewrite (K7 17%bv) by ick; exact H17_6).
assert (H5_7 : getr r7 5 = Z_to_bv 64 16) by (rewrite (K7 5%bv) by ick; exact H5_6). assert (H6_7 : getr r7 6 = Z_to_bv 64 17) by (rewrite (K7 6%bv) by ick; exact H6_6). assert (H7_7 : getr r7 7 = Z_to_bv 64 512) by (rewrite (K7 7%bv) by ick; exact H7_6).
clear A6 B6 C6 H16_6 H17_6 H5_6 H6_6 H7_6 W6.
destruct (art_ic_it_8 r7 M7 rom ca A7 B7 C7 H16_7 H17_7 H5_7 H6_7 H7_7 Hca Hca' W7) as (r8 & RUN8 & A8 & B8 & C8 & K8).
match type of RUN8 with msteps _ _ (mkst _ _ ?X _) => set (M8 := X) in RUN8 end.
assert (W8 : wrA M8 ca 2592) by (unfold M8; do 2 apply wr_Wn; exact W7).
assert (H16_8 : getr r8 16 = Z_to_bv 64 15) by (rewrite (K8 16%bv) by ick; exact H16_7). assert (H17_8 : getr r8 17 = Z_to_bv 64 1024) by (rewrite (K8 17%bv) by ick; exact H17_7).
assert (H5_8 : getr r8 5 = Z_to_bv 64 16) by (rewrite (K8 5%bv) by ick; exact H5_7). assert (H6_8 : getr r8 6 = Z_to_bv 64 17) by (rewrite (K8 6%bv) by ick; exact H6_7). assert (H7_8 : getr r8 7 = Z_to_bv 64 512) by (rewrite (K8 7%bv) by ick; exact H7_7).
clear A7 B7 C7 H16_7 H17_7 H5_7 H6_7 H7_7 W7.
destruct (art_ic_it_9 r8 M8 rom ca A8 B8 C8 H16_8 H17_8 H5_8 H6_8 H7_8 Hca Hca' W8) as (r9 & RUN9 & A9 & B9 & C9 & K9).
match type of RUN9 with msteps _ _ (mkst _ _ ?X _) => set (M9 := X) in RUN9 end.
assert (W9 : wrA M9 ca 2592) by (unfold M9; do 2 apply wr_Wn; exact W8).
assert (H16_9 : getr r9 16 = Z_to_bv 64 15) by (rewrite (K9 16%bv) by ick; exact H16_8). assert (H17_9 : getr r9 17 = Z_to_bv 64 1024) by (rewrite (K9 17%bv) by ick; exact H17_8).
assert (H5_9 : getr r9 5 = Z_to_bv 64 16) by (rewrite (K9 5%bv) by ick; exact H5_8). assert (H6_9 : getr r9 6 = Z_to_bv 64 17) by (rewrite (K9 6%bv) by ick; exact H6_8). assert (H7_9 : getr r9 7 = Z_to_bv 64 512) by (rewrite (K9 7%bv) by ick; exact H7_8).
clear A8 B8 C8 H16_8 H17_8 H5_8 H6_8 H7_8 W8.
destruct (art_ic_it_10 r9 M9 rom ca A9 B9 C9 H16_9 H17_9 H5_9 H6_9 H7_9 Hca Hca' W9) as (r10 & RUN10 & A10 & B10 & C10 & K10).
match type of RUN10 with msteps _ _ (mkst _ _ ?X _) => set (M10 := X) in RUN10 end.
assert (W10 : wrA M10 ca 2592) by (unfold M10; do 2 apply wr_Wn; exact W9).
assert (H16_10 : getr r10 16 = Z_to_bv 64 15) by (rewrite (K10 16%bv) by ick; exact H16_9). assert (H17_10 : getr r10 17 = Z_to_bv 64 1024) by (rewrite (K10 17%bv) by ick; exact H17_9).
assert (H5_10 : getr r10 5 = Z_to_bv 64 16) by (rewrite (K10 5%bv) by ick; exact H5_9). assert (H6_10 : getr r10 6 = Z_to_bv 64 17) by (rewrite (K10 6%bv) by ick; exact H6_9). assert (H7_10 : getr r10 7 = Z_to_bv 64 512) by (rewrite (K10 7%bv) by ick; exact H7_9).
clear A9 B9 C9 H16_9 H17_9 H5_9 H6_9 H7_9 W9.
destruct (art_ic_it_11 r10 M10 rom ca A10 B10 C10 H16_10 H17_10 H5_10 H6_10 H7_10 Hca Hca' W10) as (r11 & RUN11 & A11 & B11 & C11 & K11).
match type of RUN11 with msteps _ _ (mkst _ _ ?X _) => set (M11 := X) in RUN11 end.
assert (W11 : wrA M11 ca 2592) by (unfold M11; do 2 apply wr_Wn; exact W10).
assert (H16_11 : getr r11 16 = Z_to_bv 64 15) by (rewrite (K11 16%bv) by ick; exact H16_10). assert (H17_11 : getr r11 17 = Z_to_bv 64 1024) by (rewrite (K11 17%bv) by ick; exact H17_10).
assert (H5_11 : getr r11 5 = Z_to_bv 64 16) by (rewrite (K11 5%bv) by ick; exact H5_10). assert (H6_11 : getr r11 6 = Z_to_bv 64 17) by (rewrite (K11 6%bv) by ick; exact H6_10). assert (H7_11 : getr r11 7 = Z_to_bv 64 512) by (rewrite (K11 7%bv) by ick; exact H7_10).
clear A10 B10 C10 H16_10 H17_10 H5_10 H6_10 H7_10 W10.
destruct (art_ic_it_12 r11 M11 rom ca A11 B11 C11 H16_11 H17_11 H5_11 H6_11 H7_11 Hca Hca' W11) as (r12 & RUN12 & A12 & B12 & C12 & K12).
match type of RUN12 with msteps _ _ (mkst _ _ ?X _) => set (M12 := X) in RUN12 end.
assert (W12 : wrA M12 ca 2592) by (unfold M12; do 2 apply wr_Wn; exact W11).
assert (H16_12 : getr r12 16 = Z_to_bv 64 15) by (rewrite (K12 16%bv) by ick; exact H16_11). assert (H17_12 : getr r12 17 = Z_to_bv 64 1024) by (rewrite (K12 17%bv) by ick; exact H17_11).
assert (H5_12 : getr r12 5 = Z_to_bv 64 16) by (rewrite (K12 5%bv) by ick; exact H5_11). assert (H6_12 : getr r12 6 = Z_to_bv 64 17) by (rewrite (K12 6%bv) by ick; exact H6_11). assert (H7_12 : getr r12 7 = Z_to_bv 64 512) by (rewrite (K12 7%bv) by ick; exact H7_11).
clear A11 B11 C11 H16_11 H17_11 H5_11 H6_11 H7_11 W11.
destruct (art_ic_it_13 r12 M12 rom ca A12 B12 C12 H16_12 H17_12 H5_12 H6_12 H7_12 Hca Hca' W12) as (r13 & RUN13 & A13 & B13 & C13 & K13).
match type of RUN13 with msteps _ _ (mkst _ _ ?X _) => set (M13 := X) in RUN13 end.
assert (W13 : wrA M13 ca 2592) by (unfold M13; do 2 apply wr_Wn; exact W12).
assert (H16_13 : getr r13 16 = Z_to_bv 64 15) by (rewrite (K13 16%bv) by ick; exact H16_12). assert (H17_13 : getr r13 17 = Z_to_bv 64 1024) by (rewrite (K13 17%bv) by ick; exact H17_12).
assert (H5_13 : getr r13 5 = Z_to_bv 64 16) by (rewrite (K13 5%bv) by ick; exact H5_12). assert (H6_13 : getr r13 6 = Z_to_bv 64 17) by (rewrite (K13 6%bv) by ick; exact H6_12). assert (H7_13 : getr r13 7 = Z_to_bv 64 512) by (rewrite (K13 7%bv) by ick; exact H7_12).
clear A12 B12 C12 H16_12 H17_12 H5_12 H6_12 H7_12 W12.
destruct (art_ic_it_14 r13 M13 rom ca A13 B13 C13 H16_13 H17_13 H5_13 H6_13 H7_13 Hca Hca' W13) as (r14 & RUN14 & A14 & B14 & C14 & K14).
match type of RUN14 with msteps _ _ (mkst _ _ ?X _) => set (M14 := X) in RUN14 end.
assert (W14 : wrA M14 ca 2592) by (unfold M14; do 2 apply wr_Wn; exact W13).
assert (H16_14 : getr r14 16 = Z_to_bv 64 15) by (rewrite (K14 16%bv) by ick; exact H16_13). assert (H17_14 : getr r14 17 = Z_to_bv 64 1024) by (rewrite (K14 17%bv) by ick; exact H17_13).
assert (H5_14 : getr r14 5 = Z_to_bv 64 16) by (rewrite (K14 5%bv) by ick; exact H5_13). assert (H6_14 : getr r14 6 = Z_to_bv 64 17) by (rewrite (K14 6%bv) by ick; exact H6_13). assert (H7_14 : getr r14 7 = Z_to_bv 64 512) by (rewrite (K14 7%bv) by ick; exact H7_13).
clear A13 B13 C13 H16_13 H17_13 H5_13 H6_13 H7_13 W13.
destruct (art_ic_it_15 r14 M14 rom ca A14 B14 C14 H16_14 H17_14 H5_14 H6_14 H7_14 Hca Hca' W14) as (r15 & RUN15 & A15 & B15 & C15 & K15).
match type of RUN15 with msteps _ _ (mkst _ _ ?X _) => set (M15 := X) in RUN15 end.
assert (W15 : wrA M15 ca 2592) by (unfold M15; do 2 apply wr_Wn; exact W14).
assert (H16_15 : getr r15 16 = Z_to_bv 64 15) by (rewrite (K15 16%bv) by ick; exact H16_14). assert (H17_15 : getr r15 17 = Z_to_bv 64 1024) by (rewrite (K15 17%bv) by ick; exact H17_14).
assert (H5_15 : getr r15 5 = Z_to_bv 64 16) by (rewrite (K15 5%bv) by ick; exact H5_14). assert (H6_15 : getr r15 6 = Z_to_bv 64 17) by (rewrite (K15 6%bv) by ick; exact H6_14). assert (H7_15 : getr r15 7 = Z_to_bv 64 512) by (rewrite (K15 7%bv) by ick; exact H7_14).
clear A14 B14 C14 H16_14 H17_14 H5_14 H6_14 H7_14 W14.
destruct (art_ic_it_16 r15 M15 rom ca A15 B15 C15 H16_15 H17_15 H5_15 H6_15 H7_15 Hca Hca' W15) as (r16 & RUN16 & A16 & B16 & C16 & K16).
match type of RUN16 with msteps _ _ (mkst _ _ ?X _) => set (M16 := X) in RUN16 end.
assert (W16 : wrA M16 ca 2592) by (unfold M16; do 2 apply wr_Wn; exact W15).
assert (H16_16 : getr r16 16 = Z_to_bv 64 15) by (rewrite (K16 16%bv) by ick; exact H16_15). assert (H17_16 : getr r16 17 = Z_to_bv 64 1024) by (rewrite (K16 17%bv) by ick; exact H17_15).
assert (H5_16 : getr r16 5 = Z_to_bv 64 16) by (rewrite (K16 5%bv) by ick; exact H5_15). assert (H6_16 : getr r16 6 = Z_to_bv 64 17) by (rewrite (K16 6%bv) by ick; exact H6_15). assert (H7_16 : getr r16 7 = Z_to_bv 64 512) by (rewrite (K16 7%bv) by ick; exact H7_15).
clear A15 B15 C15 H16_15 H17_15 H5_15 H6_15 H7_15 W15.
destruct (art_ic_it_17 r16 M16 rom ca A16 B16 C16 H16_16 H17_16 H5_16 H6_16 H7_16 Hca Hca' W16) as (r17 & RUN17 & A17 & B17 & C17 & K17).
match type of RUN17 with msteps _ _ (mkst _ _ ?X _) => set (M17 := X) in RUN17 end.
assert (W17 : wrA M17 ca 2592) by (unfold M17; do 2 apply wr_Wn; exact W16).
assert (H16_17 : getr r17 16 = Z_to_bv 64 15) by (rewrite (K17 16%bv) by ick; exact H16_16). assert (H17_17 : getr r17 17 = Z_to_bv 64 1024) by (rewrite (K17 17%bv) by ick; exact H17_16).
assert (H5_17 : getr r17 5 = Z_to_bv 64 16) by (rewrite (K17 5%bv) by ick; exact H5_16). assert (H6_17 : getr r17 6 = Z_to_bv 64 17) by (rewrite (K17 6%bv) by ick; exact H6_16). assert (H7_17 : getr r17 7 = Z_to_bv 64 512) by (rewrite (K17 7%bv) by ick; exact H7_16).
clear A16 B16 C16 H16_16 H17_16 H5_16 H6_16 H7_16 W16.
destruct (art_ic_it_18 r17 M17 rom ca A17 B17 C17 H16_17 H17_17 H5_17 H6_17 H7_17 Hca Hca' W17) as (r18 & RUN18 & A18 & B18 & C18 & K18).
match type of RUN18 with msteps _ _ (mkst _ _ ?X _) => set (M18 := X) in RUN18 end.
assert (W18 : wrA M18 ca 2592) by (unfold M18; do 2 apply wr_Wn; exact W17).
assert (H16_18 : getr r18 16 = Z_to_bv 64 15) by (rewrite (K18 16%bv) by ick; exact H16_17). assert (H17_18 : getr r18 17 = Z_to_bv 64 1024) by (rewrite (K18 17%bv) by ick; exact H17_17).
assert (H5_18 : getr r18 5 = Z_to_bv 64 16) by (rewrite (K18 5%bv) by ick; exact H5_17). assert (H6_18 : getr r18 6 = Z_to_bv 64 17) by (rewrite (K18 6%bv) by ick; exact H6_17). assert (H7_18 : getr r18 7 = Z_to_bv 64 512) by (rewrite (K18 7%bv) by ick; exact H7_17).
clear A17 B17 C17 H16_17 H17_17 H5_17 H6_17 H7_17 W17.
destruct (art_ic_it_19 r18 M18 rom ca A18 B18 C18 H16_18 H17_18 H5_18 H6_18 H7_18 Hca Hca' W18) as (r19 & RUN19 & A19 & B19 & C19 & K19).
match type of RUN19 with msteps _ _ (mkst _ _ ?X _) => set (M19 := X) in RUN19 end.
assert (W19 : wrA M19 ca 2592) by (unfold M19; do 2 apply wr_Wn; exact W18).
assert (H16_19 : getr r19 16 = Z_to_bv 64 15) by (rewrite (K19 16%bv) by ick; exact H16_18). assert (H17_19 : getr r19 17 = Z_to_bv 64 1024) by (rewrite (K19 17%bv) by ick; exact H17_18).
assert (H5_19 : getr r19 5 = Z_to_bv 64 16) by (rewrite (K19 5%bv) by ick; exact H5_18). assert (H6_19 : getr r19 6 = Z_to_bv 64 17) by (rewrite (K19 6%bv) by ick; exact H6_18). assert (H7_19 : getr r19 7 = Z_to_bv 64 512) by (rewrite (K19 7%bv) by ick; exact H7_18).
clear A18 B18 C18 H16_18 H17_18 H5_18 H6_18 H7_18 W18.
destruct (art_ic_it_20 r19 M19 rom ca A19 B19 C19 H16_19 H17_19 H5_19 H6_19 H7_19 Hca Hca' W19) as (r20 & RUN20 & A20 & B20 & C20 & K20).
match type of RUN20 with msteps _ _ (mkst _ _ ?X _) => set (M20 := X) in RUN20 end.
assert (W20 : wrA M20 ca 2592) by (unfold M20; do 2 apply wr_Wn; exact W19).
assert (H16_20 : getr r20 16 = Z_to_bv 64 15) by (rewrite (K20 16%bv) by ick; exact H16_19). assert (H17_20 : getr r20 17 = Z_to_bv 64 1024) by (rewrite (K20 17%bv) by ick; exact H17_19).
assert (H5_20 : getr r20 5 = Z_to_bv 64 16) by (rewrite (K20 5%bv) by ick; exact H5_19). assert (H6_20 : getr r20 6 = Z_to_bv 64 17) by (rewrite (K20 6%bv) by ick; exact H6_19). assert (H7_20 : getr r20 7 = Z_to_bv 64 512) by (rewrite (K20 7%bv) by ick; exact H7_19).
clear A19 B19 C19 H16_19 H17_19 H5_19 H6_19 H7_19 W19.
destruct (art_ic_it_21 r20 M20 rom ca A20 B20 C20 H16_20 H17_20 H5_20 H6_20 H7_20 Hca Hca' W20) as (r21 & RUN21 & A21 & B21 & C21 & K21).
match type of RUN21 with msteps _ _ (mkst _ _ ?X _) => set (M21 := X) in RUN21 end.
assert (W21 : wrA M21 ca 2592) by (unfold M21; do 2 apply wr_Wn; exact W20).
assert (H16_21 : getr r21 16 = Z_to_bv 64 15) by (rewrite (K21 16%bv) by ick; exact H16_20). assert (H17_21 : getr r21 17 = Z_to_bv 64 1024) by (rewrite (K21 17%bv) by ick; exact H17_20).
assert (H5_21 : getr r21 5 = Z_to_bv 64 16) by (rewrite (K21 5%bv) by ick; exact H5_20). assert (H6_21 : getr r21 6 = Z_to_bv 64 17) by (rewrite (K21 6%bv) by ick; exact H6_20). assert (H7_21 : getr r21 7 = Z_to_bv 64 512) by (rewrite (K21 7%bv) by ick; exact H7_20).
clear A20 B20 C20 H16_20 H17_20 H5_20 H6_20 H7_20 W20.
destruct (art_ic_it_22 r21 M21 rom ca A21 B21 C21 H16_21 H17_21 H5_21 H6_21 H7_21 Hca Hca' W21) as (r22 & RUN22 & A22 & B22 & C22 & K22).
match type of RUN22 with msteps _ _ (mkst _ _ ?X _) => set (M22 := X) in RUN22 end.
assert (W22 : wrA M22 ca 2592) by (unfold M22; do 2 apply wr_Wn; exact W21).
assert (H16_22 : getr r22 16 = Z_to_bv 64 15) by (rewrite (K22 16%bv) by ick; exact H16_21). assert (H17_22 : getr r22 17 = Z_to_bv 64 1024) by (rewrite (K22 17%bv) by ick; exact H17_21).
assert (H5_22 : getr r22 5 = Z_to_bv 64 16) by (rewrite (K22 5%bv) by ick; exact H5_21). assert (H6_22 : getr r22 6 = Z_to_bv 64 17) by (rewrite (K22 6%bv) by ick; exact H6_21). assert (H7_22 : getr r22 7 = Z_to_bv 64 512) by (rewrite (K22 7%bv) by ick; exact H7_21).
clear A21 B21 C21 H16_21 H17_21 H5_21 H6_21 H7_21 W21.
destruct (art_ic_it_23 r22 M22 rom ca A22 B22 C22 H16_22 H17_22 H5_22 H6_22 H7_22 Hca Hca' W22) as (r23 & RUN23 & A23 & B23 & C23 & K23).
match type of RUN23 with msteps _ _ (mkst _ _ ?X _) => set (M23 := X) in RUN23 end.
assert (W23 : wrA M23 ca 2592) by (unfold M23; do 2 apply wr_Wn; exact W22).
assert (H16_23 : getr r23 16 = Z_to_bv 64 15) by (rewrite (K23 16%bv) by ick; exact H16_22). assert (H17_23 : getr r23 17 = Z_to_bv 64 1024) by (rewrite (K23 17%bv) by ick; exact H17_22).
assert (H5_23 : getr r23 5 = Z_to_bv 64 16) by (rewrite (K23 5%bv) by ick; exact H5_22). assert (H6_23 : getr r23 6 = Z_to_bv 64 17) by (rewrite (K23 6%bv) by ick; exact H6_22). assert (H7_23 : getr r23 7 = Z_to_bv 64 512) by (rewrite (K23 7%bv) by ick; exact H7_22).
clear A22 B22 C22 H16_22 H17_22 H5_22 H6_22 H7_22 W22.
destruct (art_ic_it_24 r23 M23 rom ca A23 B23 C23 H16_23 H17_23 H5_23 H6_23 H7_23 Hca Hca' W23) as (r24 & RUN24 & A24 & B24 & C24 & K24).
match type of RUN24 with msteps _ _ (mkst _ _ ?X _) => set (M24 := X) in RUN24 end.
assert (W24 : wrA M24 ca 2592) by (unfold M24; do 2 apply wr_Wn; exact W23).
assert (H16_24 : getr r24 16 = Z_to_bv 64 15) by (rewrite (K24 16%bv) by ick; exact H16_23). assert (H17_24 : getr r24 17 = Z_to_bv 64 1024) by (rewrite (K24 17%bv) by ick; exact H17_23).
assert (H5_24 : getr r24 5 = Z_to_bv 64 16) by (rewrite (K24 5%bv) by ick; exact H5_23). assert (H6_24 : getr r24 6 = Z_to_bv 64 17) by (rewrite (K24 6%bv) by ick; exact H6_23). assert (H7_24 : getr r24 7 = Z_to_bv 64 512) by (rewrite (K24 7%bv) by ick; exact H7_23).
clear A23 B23 C23 H16_23 H17_23 H5_23 H6_23 H7_23 W23.
destruct (art_ic_it_25 r24 M24 rom ca A24 B24 C24 H16_24 H17_24 H5_24 H6_24 H7_24 Hca Hca' W24) as (r25 & RUN25 & A25 & B25 & C25 & K25).
match type of RUN25 with msteps _ _ (mkst _ _ ?X _) => set (M25 := X) in RUN25 end.
assert (W25 : wrA M25 ca 2592) by (unfold M25; do 2 apply wr_Wn; exact W24).
assert (H16_25 : getr r25 16 = Z_to_bv 64 15) by (rewrite (K25 16%bv) by ick; exact H16_24). assert (H17_25 : getr r25 17 = Z_to_bv 64 1024) by (rewrite (K25 17%bv) by ick; exact H17_24).
assert (H5_25 : getr r25 5 = Z_to_bv 64 16) by (rewrite (K25 5%bv) by ick; exact H5_24). assert (H6_25 : getr r25 6 = Z_to_bv 64 17) by (rewrite (K25 6%bv) by ick; exact H6_24). assert (H7_25 : getr r25 7 = Z_to_bv 64 512) by (rewrite (K25 7%bv) by ick; exact H7_24).
clear A24 B24 C24 H16_24 H17_24 H5_24 H6_24 H7_24 W24.
destruct (art_ic_it_26 r25 M25 rom ca A25 B25 C25 H16_25 H17_25 H5_25 H6_25 H7_25 Hca Hca' W25) as (r26 & RUN26 & A26 & B26 & C26 & K26).
match type of RUN26 with msteps _ _ (mkst _ _ ?X _) => set (M26 := X) in RUN26 end.
assert (W26 : wrA M26 ca 2592) by (unfold M26; do 2 apply wr_Wn; exact W25).
assert (H16_26 : getr r26 16 = Z_to_bv 64 15) by (rewrite (K26 16%bv) by ick; exact H16_25). assert (H17_26 : getr r26 17 = Z_to_bv 64 1024) by (rewrite (K26 17%bv) by ick; exact H17_25).
assert (H5_26 : getr r26 5 = Z_to_bv 64 16) by (rewrite (K26 5%bv) by ick; exact H5_25). assert (H6_26 : getr r26 6 = Z_to_bv 64 17) by (rewrite (K26 6%bv) by ick; exact H6_25). assert (H7_26 : getr r26 7 = Z_to_bv 64 512) by (rewrite (K26 7%bv) by ick; exact H7_25).
clear A25 B25 C25 H16_25 H17_25 H5_25 H6_25 H7_25 W25.
destruct (art_ic_it_27 r26 M26 rom ca A26 B26 C26 H16_26 H17_26 H5_26 H6_26 H7_26 Hca Hca' W26) as (r27 & RUN27 & A27 & B27 & C27 & K27).
match type of RUN27 with msteps _ _ (mkst _ _ ?X _) => set (M27 := X) in RUN27 end.
assert (W27 : wrA M27 ca 2592) by (unfold M27; do 2 apply wr_Wn; exact W26).
assert (H16_27 : getr r27 16 = Z_to_bv 64 15) by (rewrite (K27 16%bv) by ick; exact H16_26). assert (H17_27 : getr r27 17 = Z_to_bv 64 1024) by (rewrite (K27 17%bv) by ick; exact H17_26).
assert (H5_27 : getr r27 5 = Z_to_bv 64 16) by (rewrite (K27 5%bv) by ick; exact H5_26). assert (H6_27 : getr r27 6 = Z_to_bv 64 17) by (rewrite (K27 6%bv) by ick; exact H6_26). assert (H7_27 : getr r27 7 = Z_to_bv 64 512) by (rewrite (K27 7%bv) by ick; exact H7_26).
clear A26 B26 C26 H16_26 H17_26 H5_26 H6_26 H7_26 W26.
destruct (art_ic_it_28 r27 M27 rom ca A27 B27 C27 H16_27 H17_27 H5_27 H6_27 H7_27 Hca Hca' W27) as (r28 & RUN28 & A28 & B28 & C28 & K28).
match type of RUN28 with msteps _ _ (mkst _ _ ?X _) => set (M28 := X) in RUN28 end.
assert (W28 : wrA M28 ca 2592) by (unfold M28; do 2 apply wr_Wn; exact W27).
assert (H16_28 : getr r28 16 = Z_to_bv 64 15) by (rewrite (K28 16%bv) by ick; exact H16_27). assert (H17_28 : getr r28 17 = Z_to_bv 64 1024) by (rewrite (K28 17%bv) by ick; exact H17_27).
assert (H5_28 : getr r28 5 = Z_to_bv 64 16) by (rewrite (K28 5%bv) by ick; exact H5_27). assert (H6_28 : getr r28 6 = Z_to_bv 64 17) by (rewrite (K28 6%bv) by ick; exact H6_27). assert (H7_28 : getr r28 7 = Z_to_bv 64 512) by (rewrite (K28 7%bv) by ick; exact H7_27).
clear A27 B27 C27 H16_27 H17_27 H5_27 H6_27 H7_27 W27.
destruct (art_ic_it_29 r28 M28 rom ca A28 B28 C28 H16_28 H17_28 H5_28 H6_28 H7_28 Hca Hca' W28) as (r29 & RUN29 & A29 & B29 & C29 & K29).
match type of RUN29 with msteps _ _ (mkst _ _ ?X _) => set (M29 := X) in RUN29 end.
assert (W29 : wrA M29 ca 2592) by (unfold M29; do 2 apply wr_Wn; exact W28).
assert (H16_29 : getr r29 16 = Z_to_bv 64 15) by (rewrite (K29 16%bv) by ick; exact H16_28). assert (H17_29 : getr r29 17 = Z_to_bv 64 1024) by (rewrite (K29 17%bv) by ick; exact H17_28).
assert (H5_29 : getr r29 5 = Z_to_bv 64 16) by (rewrite (K29 5%bv) by ick; exact H5_28). assert (H6_29 : getr r29 6 = Z_to_bv 64 17) by (rewrite (K29 6%bv) by ick; exact H6_28). assert (H7_29 : getr r29 7 = Z_to_bv 64 512) by (rewrite (K29 7%bv) by ick; exact H7_28).
clear A28 B28 C28 H16_28 H17_28 H5_28 H6_28 H7_28 W28.
destruct (art_ic_it_30 r29 M29 rom ca A29 B29 C29 H16_29 H17_29 H5_29 H6_29 H7_29 Hca Hca' W29) as (r30 & RUN30 & A30 & B30 & C30 & K30).
match type of RUN30 with msteps _ _ (mkst _ _ ?X _) => set (M30 := X) in RUN30 end.
assert (W30 : wrA M30 ca 2592) by (unfold M30; do 2 apply wr_Wn; exact W29).
assert (H16_30 : getr r30 16 = Z_to_bv 64 15) by (rewrite (K30 16%bv) by ick; exact H16_29). assert (H17_30 : getr r30 17 = Z_to_bv 64 1024) by (rewrite (K30 17%bv) by ick; exact H17_29).
assert (H5_30 : getr r30 5 = Z_to_bv 64 16) by (rewrite (K30 5%bv) by ick; exact H5_29). assert (H6_30 : getr r30 6 = Z_to_bv 64 17) by (rewrite (K30 6%bv) by ick; exact H6_29). assert (H7_30 : getr r30 7 = Z_to_bv 64 512) by (rewrite (K30 7%bv) by ick; exact H7_29).
clear A29 B29 C29 H16_29 H17_29 H5_29 H6_29 H7_29 W29.
destruct (art_ic_it_31 r30 M30 rom ca A30 B30 C30 H16_30 H17_30 H5_30 H6_30 H7_30 Hca Hca' W30) as (r31 & RUN31 & A31 & B31 & C31 & K31).
match type of RUN31 with msteps _ _ (mkst _ _ ?X _) => set (M31 := X) in RUN31 end.
assert (EM : M31 = art_ic_mem M ca 31). { unfold M31, M30, M29, M28, M27, M26, M25, M24, M23, M22, M21, M20, M19, M18, M17, M16, M15, M14, M13, M12, M11, M10, M9, M8, M7, M6, M5, M4, M3, M2, M1. cbn [art_ic_mem Z.of_nat Pos.of_succ_nat Pos.succ]. reflexivity. }
rewrite EM in RUN31. exists r31. split.
{ eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|]. eapply msteps_trans; [exact RUN3|]. eapply msteps_trans; [exact RUN4|]. eapply msteps_trans; [exact RUN5|]. eapply msteps_trans; [exact RUN6|]. eapply msteps_trans; [exact RUN7|]. eapply msteps_trans; [exact RUN8|]. eapply msteps_trans; [exact RUN9|]. eapply msteps_trans; [exact RUN10|]. eapply msteps_trans; [exact RUN11|]. eapply msteps_trans; [exact RUN12|]. eapply msteps_trans; [exact RUN13|]. eapply msteps_trans; [exact RUN14|]. eapply msteps_trans; [exact RUN15|]. eapply msteps_trans; [exact RUN16|]. eapply msteps_trans; [exact RUN17|]. eapply msteps_trans; [exact RUN18|]. eapply msteps_trans; [exact RUN19|]. eapply msteps_trans; [exact RUN20|]. eapply msteps_trans; [exact RUN21|]. eapply msteps_trans; [exact RUN22|]. eapply msteps_trans; [exact RUN23|]. eapply msteps_trans; [exact RUN24|]. eapply msteps_trans; [exact RUN25|]. eapply msteps_trans; [exact RUN26|]. eapply msteps_trans; [exact RUN27|]. eapply msteps_trans; [exact RUN28|]. eapply msteps_trans; [exact RUN29|]. eapply msteps_trans; [exact RUN30|]. exact RUN31. }
intros r Hr. rewrite (K31 r Hr), (K30 r Hr), (K29 r Hr), (K28 r Hr), (K27 r Hr), (K26 r Hr), (K25 r Hr), (K24 r Hr), (K23 r Hr), (K22 r Hr), (K21 r Hr), (K20 r Hr), (K19 r Hr), (K18 r Hr), (K17 r Hr), (K16 r Hr), (K15 r Hr), (K14 r Hr), (K13 r Hr), (K12 r Hr), (K11 r Hr), (K10 r Hr), (K9 r Hr), (K8 r Hr), (K7 r Hr), (K6 r Hr), (K5 r Hr), (K4 r Hr), (K3 r Hr), (K2 r Hr), (K1 r Hr). reflexivity.
Qed.
End SE.
End FPX.
