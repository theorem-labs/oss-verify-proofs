(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib As0Tables
ArtMem ArtRegs ArtAtomics ArtTac JatLeaf JatRzLog JatAllocA JatPoison JatAllocG.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLiaT.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__JatAllocPre3 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ArtMem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.As0Tables.AsanTab."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatAllocA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatLeaf."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatRzLog."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.StoreOk."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1option"; "2I"; "2and"; "2eq"; "2ex"; "2not"; "2or"; "3Z"; "4bvmap"; "0M0"; "0M5"; "5apart"; "5cell"; "5wr"; "6rz_log"; "7msteps"]; ["8art_alloc_rodata"; "9art_tsd"; ":art_rz_rodata"; ";getr"; ";mkst"; "<mem_grows"; "=loaded_segments"; ">add"; ">div"; ">le"; ">lt"; ">max"; ">mul"; ">pow"; ">sub"; "0ctx"]; ["0fx"; "0ia"; "0key"; "0n"; "0qr"; "0qz"; "0r5"; "0raw"; "0regs"; "0rl"; "0rom"; "0rs"; "0rz"; "0sp"; "?BV"; "?Z_to_bv"]; ["?bv"; "?bv_unsigned"; "0stk"; "0t"; "0tp"; "0tsd"; "0x"]]).
Local Ltac lia := L5FastLiaT.plia2.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation cellA := (cell Asan.M.loaded_segments).
#[local] Abbreviation wokA := (wok Asan.M.loaded_segments).
#[local] Abbreviation wrA := (wr Asan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).
Ltac inl := cbn [In]; repeat first [left; reflexivity | right].
Section FPX. Context {fx : PropExec.FPState}.
Section SE.
Local Abbreviation SEC_T_art_allocate_pre3a := (ltac2:(TCodec.tc2 tcn__JatAllocPre3 "_E&8y5'Q@yR0%211%5241'0y8%611%311p061'7'3&CrB(Q>+1(1%33A21%6251r?%93A21rC+2%93G17%<231&Q?%12H7%@3H31rD+4%@3N1>%C231r<%82O1%G3O31rE+:%G3Q51E%J231r@%?2Q61%N3Q631rF+;%N3Q<1L%Q1231%Q33Q;16rG+<%Q33QA1Q1%Q6231+8%K2QB1%Q:3QB31rH+=%Q:3QH1Q8%Q=231rA%Q22QI1%QA3QI31rI+>%QA3QO1Q?%QD231%Q82QOQB%QG3QO21rJ+?%QG3R51QE%QJ231%QL3R416'2&I%12QKQ7&J&M+Q8%22QH1%42Q<1%8261&>%11Q8%R83R9R01r=&L+@%;2R1Q@%3221%R>3R?51r>%6257%RA3RB21%D2R>3+T0%F251%H231&H&G&K%12Q1QA+7%4221%621QD%C21QE%RN3RORL1%E2QGRM%S03S1RF1rL%:21QJ%Q521RB%=22:%Q72RD1%Q9231%@2R?RM+RPP0%Q;221+`PQoooPP0+TP0%E221rQ0%Q@221rQ1+RS0%J221+Q?%QB2S81%QF231rQ2rO%QI221%Q12;Q=rQ3%Q321?%QM231%QN2D3rQ4%Q721C+VbTP0%R2221rN%R42G1%Q<2=H%R421A'6%Q?2IK%R921O%R:29K%4221&;&NrQ9+Qm0%3221+Um0%64Q1Q521rQ:%7215%94JQ814%RF2FQ<%RG2FH%A221rQ5%>4KQ=1Q=+RPX0%RL21>%R42:SC%RN21M%RO2QEA+QP0%R82>1%S221Q1&=&FrQDrQA%J21H%54431I&@rQE%211&BrQF%211&ArQGrQ@rQ?rQ>rQ=rQ<%76654321&<rQH+QW^^Hu1%45G321UErQI+Qgck2z%85K3251rQJ+Sa0%S92E1u8%=5Q0421SOrQK+Sa8%S>2G1u2%B5Q5421SLrQL+Sa:%SC2D1+RP0%G5Q:4261'4'?&DvQ0rR0+ZVo4%V@3VL1V>/01VLrQOrQN%8576321r2+ZhiL%VG3W31VE/01W3r1%>5=5217%@3QL71%VN27VI+ZWd4%VN3W:1VL/01W:%W33W;41%W32<VH%RJ2MTB%VH2W?1%W73W?31%W72@VE%VK2WBQC%W:3WB21%W83WFV3W6%W;2D1%W=3WE1UG+9%W<3WJ1W:%W?2H1%W32WJQC%WB3WJ21%WB2KVI%W62WMQA%WE3WM21%WE2NVE+V@%U12RE1%W;2X21%WJ3X241%WJ2Q3VErQB%U621R>%W@2X71%WO3X741%WO2Q8VC%X13X91VH+C%X03X>1WN%X32Q<1%X53X=17+D%X43XB1X2%X72Q@1%WK2XBRJ%X:3XB21+E%X93XG1X7%X<2QE1%X>3XF1M+F%X=3XK1X;%X@2QI1%XB3XJ1N+G%XA3XO1X?%XD2QM1%X82XORL%XG3XO21+I%XF3Y41XD%XI2R21%X=2Y4V1%XL3Y421+J%XK3Y91XI%XN2R71%XB2Y9SM%Y13Y921+K%Y03Y>1XN%Y32R<1%Y53Y=1W?+3%Y43YB1Y2%Y72R@1%Y82RH2%Y:3YB21&E%12RGR@&5rQM+T@%U5221&QA%12YKRF%WE231%WD226%WH221%911r3%11S0rR1%11S2%YK3YN31p061pS>Z51+SH%W82RJ1%?2Z9B%T<5TOS52T01+S@%W<2RN1%Z32SCRI%D2Z>1%TA5U4S:3T51+S8%WA2S31%Z82SHRJ%I2ZC1%TF5U9S?3T:1+S0%WF2S81+B%Z<3ZJ1Z:%Z?2SO1%Q02ZJ1%TM5U@SF5TA1+RH%WM2S?1%ZD2T4RB%Q52ZO1%U25UESK3TF1+R@%X22SD1%ZI2T9RC%Q:2[41%U75UJT03TK1+R8%X72SI1%ZN2T>RC%Q?2[91%U<5UOT53U01+R0%X<2SN1%[32TCRD%QD2[>1%UA5V4T:3U51+QH%XA2T31%[82THRE%QI2[C1%UF5V9T?3U:1+Q@%XF2T81+H%[<3[J1[:%[?2TO1%R02[J1%UM5V@TF5UA1%XL2T>YA%[C2U3RK%R42[N1%V15VDTJ3UE1+Q0%Y12TC1%[H2U8RK%R92\31%V65VITO3UJ1%Y52TG>%[L2U<RJ%R=2\71%V:5VMU33UN1%Y92TKZH%V<5VOU51V0[M%Y;2TMYG%V>5W1U71V2YH%Z7231%Z8261%Z92;1%Z:2A1%Z;2F1%Z<2N1%Z=2Q41%Z>2Q:1%Z?2Q@1%Z@2QF1%ZA2QL1%ZB2R41%ZC2R:1%ZD2R@1%ZE2RE1%ZF2S71%ZG2S:1%ZH2S@1%ZI2SE1%ZJ2SK1%ZK2T11%ZL2T71%ZM2T<1%ZN2TA1%ZO2TG1%[02TL1%[12TO1%[22U51%[32U;1%[42U?1%[52UE1%[62UI1%[72UM1%[82V21%[92V81qF]91%VK2]:1qR>]@1%VM2]A1p0VO1p0W51p0W;1p0WA1p0WF1p0WL1p0X51p0X91p0X=1p0XD1p0XH1p0XJ1p0XM1p0Y01p0Y31p0Y71p0Y;1p0YC1p0YI1p0YL1p0YO1p0Z41p0Z61p0Z;1p0Z?1p0ZF1p0ZL1p0[01p0[71p0[:1p0[D1p0[I1p0[M1p0\41p0\81p0\B1p0\H1p0\O1p0]71p0]?1p0]E1p0]M1p0^51p0^=1pR<^H1pRJ^I1pR:^J1pRH^K1pRD^L1pS8^M1pR0^N1pS<^O1pR6_01pS:_11pS6_21pR8_31pR4_41pRL_51pR@_=1pRF_81pD_91pRB_?1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_allocate_pre3a) 0%nat 0%nat).
Variable M0 : ltac:(sec_ty2 constr:(SEC_T_art_allocate_pre3a) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_allocate_pre3a) 2%nat 0%nat).
Variable raw : ltac:(sec_ty2 constr:(SEC_T_art_allocate_pre3a) 3%nat 0%nat).
Variable sp : ltac:(sec_ty2 constr:(SEC_T_art_allocate_pre3a) 4%nat 0%nat).
Variable ia : ltac:(sec_ty2 constr:(SEC_T_art_allocate_pre3a) 5%nat 0%nat).
Variable n : ltac:(sec_ty2 constr:(SEC_T_art_allocate_pre3a) 6%nat 0%nat).
Variable stk : ltac:(sec_ty2 constr:(SEC_T_art_allocate_pre3a) 7%nat 0%nat).
Variable tp : ltac:(sec_ty2 constr:(SEC_T_art_allocate_pre3a) 8%nat 0%nat).
Variable key : ltac:(sec_ty2 constr:(SEC_T_art_allocate_pre3a) 9%nat 0%nat).
Variable tsd : ltac:(sec_ty2 constr:(SEC_T_art_allocate_pre3a) 10%nat 0%nat).
Variable ctx : ltac:(sec_ty2 constr:(SEC_T_art_allocate_pre3a) 11%nat 0%nat).
Variable t : ltac:(sec_ty2 constr:(SEC_T_art_allocate_pre3a) 12%nat 0%nat).
Variable rl : ltac:(sec_ty2 constr:(SEC_T_art_allocate_pre3a) 13%nat 0%nat).
Variable rs : ltac:(sec_ty2 constr:(SEC_T_art_allocate_pre3a) 14%nat 0%nat).
Variable qr : ltac:(sec_ty2 constr:(SEC_T_art_allocate_pre3a) 15%nat 0%nat).
Variable rz : ltac:(sec_ty2 constr:(SEC_T_art_allocate_pre3a) 16%nat 0%nat).
Variable qz : ltac:(sec_ty2 constr:(SEC_T_art_allocate_pre3a) 17%nat 0%nat).
Theorem art_allocate_pre3a : ltac:(sec_stmt2 constr:(SEC_T_art_allocate_pre3a) 18%nat 0%nat).
Proof using Type regs M0 rom raw sp ia n stk tp key tsd ctx t rl rs qr rz qz.
intros H1 H2 H4 H10 H11 H12 H13 H14 H15.
intros Hn Er Erz Erz16 Hqz Ers Ers8 Hrs Hprim.
intros Hsp Hsp' Hstk Hstk' Hia Hia' Ht Ht' Timg Atsp Actx Cimg Atctx Htp0 Htp1 Htsd0 Htsd.
intros W RO RZRO TSD Ci Cr Cmax Cmin16 Cmax2048.
pose proof TSD as (Ttsd1 & Ttsd2 & Ttsd3 & Ttsd4 & Ttsd5 & TR).
pose proof (AsanTab.rz_log_range n) as Hr. rewrite <- Er in Hr.
change (hid (t + 4096 <= 0x10000 \/ 0x691000 <= t)) in Timg. change (hid (ctx + 4096 <= 0x10000 \/ 0x691000 <= ctx)) in Cimg.
pose proof (art_alloc_a1_fn regs M0 rom raw sp ia n stk H1 H2 H10 H11 H12 H13 H14 H15 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
ltac:(eapply wr_sub; [exact W|lia|lia]) ltac:(lia) RO Ci Cr) as RUN1.
set (M1 := art_alloc_memA1 M0 sp raw regs) in RUN1.
lazymatch type of RUN1 with msteps _ _ (mkst ?R _ _ _) => set (R1 := R) in RUN1 end.
assert (AG1 : forall a k v, 0 <= a -> a + Z.of_nat k <= sp - 128 \/ sp <= a -> a + Z.of_nat k < 2 ^ 64 -> cellA M0 a k v -> cellA M1 a k v).
{ intros a k v Ha Hak Hak' C. unfold M1, art_alloc_memA1. zcell. }
assert (W1 : wrA M1 (sp - 1952) 1952) by (unfold M1, art_alloc_memA1; zwr).
destruct (art_alloc_ladder R1 M1 rom n ltac:(unfold R1; gres; reflexivity) ltac:(unfold R1; gres; reflexivity) ltac:(lia)) as (r2 & RUN2 & P2_19 & K2).
assert (KK2 : forall r v, r <> 10%bv -> r <> 19%bv -> getr R1 r = v -> getr r2 r = v). { intros r v N1 N2 E. rewrite K2 by assumption. exact E. }
pose proof (art_alloc_a2_fn r2 M1 rom (sp - 128) ia
(KK2 2%bv _ ltac:(discriminate) ltac:(discriminate) ltac:(unfold R1; gres; f_equal; lia))
(KK2 26%bv _ ltac:(discriminate) ltac:(discriminate) ltac:(unfold R1; gres; reflexivity))
ltac:(lia) ltac:(lia) ltac:(lia) Hia' ltac:(eapply wr_sub; [exact W1|lia|lia]) ltac:(lia)
ltac:(destruct RZRO as (X1 & X2 & X3); repeat split; apply AG1; try assumption; cbn; lia)
ltac:(apply AG1; first [exact Cmin16 | ond | oside]; cbn; lia) ltac:(apply AG1; first [exact Cmax2048 | ond | oside]; cbn; lia)) as RUN3.
lazymatch type of RUN3 with msteps _ _ (mkst ?R _ ?MM _) => set (R3 := R) in RUN3; set (M3 := MM) in RUN3 end.
assert (AG3 : forall a k v, 0 <= a -> a + Z.of_nat k <= sp - 128 - 16 \/ sp <= a -> a + Z.of_nat k < 2 ^ 64 -> cellA M0 a k v -> cellA M3 a k v).
{ intros a k v Ha Hak Hak' C. unfold M3. do 2 (apply cell_Wn_other; [lia|lia|lia|lia|unfold apart; lia|]). apply AG1; assumption || lia. }
assert (W3 : wrA M3 (sp - 1952) 1952) by (unfold M3; zwr).
destruct (art_alloc_clamp R3 M3 rom n rl ltac:(unfold R3; gres; reflexivity) ltac:(unfold R3; gres; reflexivity)
ltac:(unfold R3; gres; rewrite P2_19; f_equal; symmetry; exact Er)
ltac:(unfold R3; gres; apply (KK2 21%bv); [discriminate|discriminate|unfold R1; gres; reflexivity]) ltac:(lia)
Er) as (r4 & RUN4 & P4_10 & P4_11 & P4_19 & K4).
assert (KK4 : forall r v, r <> 10%bv -> r <> 11%bv -> r <> 19%bv -> getr R3 r = v -> getr r4 r = v). { intros r v N1 N2 N3 E. rewrite K4 by assumption. exact E. }
assert (Q2 : getr r4 2 = Z_to_bv 64 (sp - 128)). { apply KK4; [discriminate|discriminate|discriminate|]. unfold R3; gres. f_equal; lia. }
assert (Q4 : getr r4 4 = Z_to_bv 64 tp). { apply KK4; [discriminate|discriminate|discriminate|]. unfold R3; gres. apply (KK2 4%bv); [discriminate|discriminate|]. unfold R1; gres. exact H4. }
assert (Q8 : getr r4 8 = Z_to_bv 64 8). { apply KK4; [discriminate|discriminate|discriminate|]. unfold R3; gres. apply (KK2 8%bv); [discriminate|discriminate|]. unfold R1; gres. reflexivity. }
assert (Q18 : getr r4 18 = Z_to_bv 64 8). { apply KK4; [discriminate|discriminate|discriminate|]. unfold R3; gres. apply (KK2 18%bv); [discriminate|discriminate|]. unfold R1; gres. reflexivity. }
assert (Q20 : getr r4 20 = Z_to_bv 64 65536). { apply KK4; [discriminate|discriminate|discriminate|]. unfold R3; gres. reflexivity. }
assert (Q21 : getr r4 21 = Z_to_bv 64 n). { apply KK4; [discriminate|discriminate|discriminate|]. unfold R3; gres. apply (KK2 21%bv); [discriminate|discriminate|]. unfold R1; gres. reflexivity. }
assert (Q22 : getr r4 22 = Z_to_bv 64 ia). { apply KK4; [discriminate|discriminate|discriminate|]. unfold R3; gres. apply (KK2 22%bv); [discriminate|discriminate|]. unfold R1; gres. reflexivity. }
assert (Q26 : getr r4 26 = Z_to_bv 64 (ia + 2047)). { apply KK4; [discriminate|discriminate|discriminate|]. unfold R3; gres. apply (KK2 26%bv); [discriminate|discriminate|]. unfold R1; gres. reflexivity. }
assert (Q23 : getr r4 23 = Z_to_bv 64 stk). { apply KK4; [discriminate|discriminate|discriminate|]. unfold R3; gres. apply (KK2 23%bv); [discriminate|discriminate|]. unfold R1; gres. reflexivity. }
assert (Q25 : getr r4 25 = Z_to_bv 64 7). { apply KK4; [discriminate|discriminate|discriminate|]. unfold R3; gres. apply (KK2 25%bv); [discriminate|discriminate|]. unfold R1; gres. reflexivity. }
assert (Q27 : getr r4 27 = Z_to_bv 64 1). { apply KK4; [discriminate|discriminate|discriminate|]. unfold R3; gres. apply (KK2 27%bv); [discriminate|discriminate|]. unfold R1; gres. reflexivity. }
assert (Q24 : getr r4 24 = Z_to_bv 64 65535). { apply KK4; [discriminate|discriminate|discriminate|]. unfold R3; gres. reflexivity. }
assert (TSD3 : art_tsd M3 tp key tsd ctx t). { unfold art_tsd. repeat split; try lia; (apply AG3; first [assumption | ond | oside]). }
pose proof (art_alloc_a3_fn r4 M3 rom (sp - 128) ia n rl rs rz tp key tsd ctx t Q2 Q4 Q8 ltac:(rewrite P4_10; f_equal; lia) Q18 P4_19 Q20 Q21 Q22 Q26
ltac:(lia) ltac:(lia) ltac:(lia) Hia' ltac:(lia) ltac:(lia) ltac:(lia) Ers Erz ltac:(lia)
ltac:(eapply wr_sub; [exact W3|lia|lia]) ltac:(apply AG3; first [exact Cmax | ond | oside]; cbn; lia) TSD3 ltac:(lia)
ltac:(unfold apart; lia) ltac:(unfold apart; lia) ltac:(unfold apart in Actx |- *; lia)) as RUN5.
lazymatch type of RUN5 with msteps _ _ (mkst ?R _ ?MM _) => set (R5 := R) in RUN5; set (M5 := MM) in RUN5 end.
assert (AG5 : forall a k v, 0 <= a -> a + Z.of_nat k <= sp - 128 - 16 \/ sp <= a -> a + Z.of_nat k < 2 ^ 64 -> cellA M0 a k v -> cellA M5 a k v).
{ intros a k v Ha Hak Hak' C. unfold M5. apply cell_Wn_other; [lia|lia|lia|lia|unfold apart; lia|]. apply AG3; assumption || lia. }
assert (W5 : wrA M5 (sp - 1952) 1952) by (unfold M5; zwr).
assert (G5 : mem_grows M0 M5).
{ unfold M5, M3, M1, art_alloc_memA1. repeat (eapply mem_grows_trans; [|apply Wn_grows]). apply mem_grows_refl. }
assert (AGt5 : forall a k v, 0 <= a -> a + Z.of_nat k < 2 ^ 64 -> (a + Z.of_nat k <= sp - 1952 \/ sp <= a) -> cellA M0 a k v -> cellA M5 a k v).
{ intros a k v Ha Hak O C. apply AG5; try assumption. lia. }
assert (A05 : forall x : word, ~ (sp - 144 <= U x < sp) -> M5 x = M0 x).
{ intros x N1. unfold M5, M3, M1, art_alloc_memA1. zagree. }
assert (Q3 : getr r4 3 = getr regs 3). { apply KK4; [discriminate|discriminate|discriminate|]. unfold R3; gres. apply (KK2 3%bv); [discriminate|discriminate|]. unfold R1; gres. reflexivity. }
assert (AF5 : forall a k v, sp - 128 <= a -> a + Z.of_nat k <= sp -> cellA M1 a k v -> cellA M5 a k v).
{ intros a k v Ha Hak C. unfold M5, M3. do 3 (apply cell_Wn_other; [lia|lia|lia|lia|unfold apart; lia|]). exact C. }
exists R5, M5.
split. { eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|]. eapply msteps_trans; [exact RUN3|]. eapply msteps_trans; [exact RUN4|]. exact RUN5. }
split; [unfold R5; gres; reflexivity|]. split; [unfold R5; gres; reflexivity|]. split; [unfold R5; gres; exact Q4|]. split; [unfold R5; gres; reflexivity|].
split; [unfold R5; gres; reflexivity|]. split; [unfold R5; gres; reflexivity|]. split; [unfold R5; gres; reflexivity|]. split; [unfold R5; gres; reflexivity|].
split; [unfold R5; gres; reflexivity|]. split; [unfold R5; gres; reflexivity|]. split; [unfold R5; gres; reflexivity|]. split; [unfold R5; gres; exact Q21|].
split; [unfold R5; gres; exact Q22|]. split; [unfold R5; gres; exact Q23|]. split; [unfold R5; gres; exact Q25|]. split; [unfold R5; gres; reflexivity|].
split; [unfold R5; gres; exact Q27|].
split; [unfold R5; gres; exact Q3|].
split; [exact G5|]. split; [exact A05|].
zsplit; (apply AF5; [lia|cbn; lia|unfold M1, art_alloc_memA1; zcell]).
Qed.
End SE.
End FPX.
