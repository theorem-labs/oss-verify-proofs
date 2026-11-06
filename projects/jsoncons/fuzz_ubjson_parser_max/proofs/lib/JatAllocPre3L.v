(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib As0Tables
ArtMem ArtRegs ArtAtomics ArtTac JatLeaf JatRzLog JatAllocA JatAllocSecA JatPoison JatAllocG.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLiaT.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__JatAllocPre3L () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ArtMem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.As0Tables.AsanTab."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatAllocA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatLeaf."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatRzLog."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.StoreOk."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1option"; "2I"; "2and"; "2eq"; "2ex"; "2not"; "2or"; "3Z"; "4bvmap"; "0M0"; "0M5"; "5apart"; "5cell"; "5wr"; "6rz_log"; "7msteps"]; ["8art_alloc_rodata"; "9art_tsd"; ":art_rz_rodata"; ";getr"; ";mkst"; "<mem_grows"; "=loaded_segments"; ">add"; ">div"; ">le"; ">lt"; ">max"; ">mul"; ">pow"; ">sub"; "0ctx"]; ["0fx"; "0ia"; "0key"; "0n"; "0qr"; "0qz"; "0r5"; "0raw"; "0regs"; "0rl"; "0rom"; "0rs"; "0rz"; "0sp"; "?BV"; "?Z_to_bv"]; ["?bv"; "?bv_unsigned"; "0stk"; "0t"; "0tp"; "0tsd"; "0x"]]).
Local Ltac lia := L5FastLiaT.plia1.
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
Local Abbreviation SEC_T_art_allocate_pre3a_sec := (ltac2:(TCodec.tc2 tcn__JatAllocPre3L "_I&8y5'Q@yR0%211%5241'0y8%611%311p061'7'3&CrB(Q>+1(1%33A21%6251r?%93A21rC+2%93G17%<231&Q?%12H7%@3H31rD+4%@3N1>%C231r<%82O1%G3O31rE+:%G3Q51E%J231r@%?2Q61%N3Q631rF+;%N3Q<1L%Q1231%Q33Q;16rG+<%Q33QA1Q1%Q6231+8%K2QB1%Q:3QB31rH+=%Q:3QH1Q8%Q=231rA%Q22QI1%QA3QI31rI+>%QA3QO1Q?%QD231%Q82QOQB%QG3QO21rJ+?%QG3R51QE%QJ231%QL3R416'2&I%12QKQ7&J&M+Q7%22QH1%42Q<1%8261&>%11Q8%R83R9R01r=&L+@%;2R1Q@%3221%R>3R?51r>%6257%RA3RB21%D2R>3+T0%F251%H231&H&G&K%12Q1QA+7%4221%621QD%C21QE%RN3RORL1%E2QGRM%S03S1RF1rL%:21QJ%Q521RB%=22:%Q72RD1%Q9231+RPP0%A2R@RN%Q9221+`PQoooPP0+TP0%E221rQ0%Q@221rQ1+RS0%J221+Q?%QB2S81%QF231rQ2rO%QI221%Q12;Q=rQ3%Q321?%QM231%QN2E3rQ4%Q721C+VbTP0%R2221rN%R42G1%Q<2=H%R421A'6%Q?2IK%R921Q0%R:29K%4221&;&NrQ9+Qm0%3221+Um0%64Q1Q521rQ:%7215%94JQ814%RF2FQ=%RG2FH%A221rQ5%>4KQ=1Q=+RPX0%RL21>%R42:SC%RN21M%RO2QFA+QP0%R82>1%S221Q1&=&FrQDrQA%J21H%54431I&@rQE%211&BrQF%211&ArQGrQ@rQ?rQ>rQ=rQ<%76654321&<rQH+QW^^Hu1%45G321UErQI+Qgck2z%85K3251rQJ+Sa0%S92E1u8+Q8%T22UH1%?5Q26431rQK+Sa8%S@2I1u2%D5Q7421SNrQL+Sa:%SE2F1+RP0%I5Q<4261'4'?&DvQ0rR0+ZVo4%VB3VN1V@/01VNrQOrQN%8576321r2+ZhiL%VI3W51VG/01W5r1%>5=5217%@3QN71%W027VK+ZWd4%W03W<1VN/01W<%W53W=41%W52<VJ%RL2MTD%VJ2WA1%W93WA31%W92@VG%VM2WDQE%W<3WD21%W:3WHV5W8%W=2D1%W12WHQC%W@3WH21+9%W?3WM1W=%WB2I1%W62WMQF%WE3WM21%WE2LVL%W92X0QB%WH3X021%WH2OVH+V@%U42RH1%W>2X51%WM3X541%WM2Q4VHrQB%U921RA%U:21RB%WD2X;1%X33X;51%X32Q:VG%X53X=1VL+C%X43XB1X2%X72Q>1%X93XA17+D%X83XF1X6%X;2QB1%WO2XFRN%X>3XF21+E%X=3XK1X;%X@2QG1%XB3XJ1N+F%XA3XO1X?%XD2QK1%XF3XN1O+G%XE3Y31XC%XH2QO1%X<2Y3S0%XK3Y321+I%XJ3Y81XH%XM2R41%XA2Y8V5%Y03Y821+J%XO3Y=1XM%Y22R91%XF2Y=T1%Y53Y=21+K%Y43YB1Y2%Y72R>1%Y93YA1WC+3%Y83YF1Y6%Y;2RB1%Y<2RJ2%Y>3YF21&E%12RIRB&5rQM+T@%U9221&QA%12YORH%WI231%WH226%WL221%911r3%11S2rR1%11S4%YO3Z231p061pS>Z91+SH%W<2RL1%?2Z=B%T@5U3S72T41+S@%W@2S01%Z72SERK%D2ZB1%TE5U8S<3T91+S8%WE2S51%Z<2SJRK%I2ZG1%TJ5U=SA3T>1+S0%WJ2S:1+B%Z@3ZN1Z>%ZC2T11%Q02ZN1%U15UDSH5TE1+RH%X12SA1%ZH2T6RB%Q52[31%U65UISM3TJ1+R@%X62SF1%ZM2T;RC%Q:2[81%U;5UNT23TO1+R8%X;2SK1%[22T@RC%Q?2[=1%U@5V3T73U41+R0%X@2T01%[72TERD%QD2[B1%UE5V8T<3U91+QH%XE2T51%[<2TJRE%QI2[G1%UJ5V=TA3U>1+Q@%XJ2T:1+H%[@3[N1[>%[C2U11%R02[N1%V15VDTH5UE1%Y02T@UE%[G2U5RK%R42\21%V55VHTL3UI1+Q0%Y52TE1%[L2U:RK%R92\71%V:5VMU13UN1%Y92TI>%\02U>RJ%R=2\;1%V>5W1U53V21%Y=2TMZL%V@5W3U71V4\1%Y?2TOYK%VB5W5U91V6YL%Z;231%Z<261%Z=2;1%Z>2A1%Z?2F1%Z@2N1%ZA2Q41%ZB2Q:1%ZC2Q@1%ZD2QF1%ZE2QL1%ZF2R41%ZG2R:1%ZH2R@1%ZI2RE1%ZJ2S71%ZK2S:1%ZL2S@1%ZM2SE1%ZN2SK1%ZO2T11%[02T71%[12T<1%[22TA1%[32TG1%[42TL1%[52TO1%[62U61%[72U<1%[82U@1%[92UF1%[:2UK1%[;2UO1%[<2V41%[=2V:1qF]=1%VM2]>1qR>]D1%VO2]E1p0W11p0W71p0W=1p0WE1p0WJ1p0X01p0X91p0X=1p0XA1p0XH1p0XL1p0XN1p0Y11p0Y41p0Y71p0Y;1p0Y?1p0YG1p0YM1p0Z01p0Z31p0Z81p0Z:1p0Z?1p0ZC1p0ZJ1p0[01p0[41p0[;1p0[>1p0[H1p0[M1p0\11p0\81p0\<1p0\F1p0\L1p0]31p0];1p0]C1p0]I1p0^11p0^91p0^A1pR<^L1pRJ^M1pR:^N1pRH^O1pRD_01pS8_11pR0_21pS<_31pR6_41pS:_51pS6_61pR8_71pR4_81pRL_91pR@_A1pRF_<1pD_=1pRB_C1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_allocate_pre3a_sec) 0%nat 0%nat).
Variable M0 : ltac:(sec_ty2 constr:(SEC_T_art_allocate_pre3a_sec) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_allocate_pre3a_sec) 2%nat 0%nat).
Variable raw : ltac:(sec_ty2 constr:(SEC_T_art_allocate_pre3a_sec) 3%nat 0%nat).
Variable sp : ltac:(sec_ty2 constr:(SEC_T_art_allocate_pre3a_sec) 4%nat 0%nat).
Variable ia : ltac:(sec_ty2 constr:(SEC_T_art_allocate_pre3a_sec) 5%nat 0%nat).
Variable n : ltac:(sec_ty2 constr:(SEC_T_art_allocate_pre3a_sec) 6%nat 0%nat).
Variable stk : ltac:(sec_ty2 constr:(SEC_T_art_allocate_pre3a_sec) 7%nat 0%nat).
Variable tp : ltac:(sec_ty2 constr:(SEC_T_art_allocate_pre3a_sec) 8%nat 0%nat).
Variable key : ltac:(sec_ty2 constr:(SEC_T_art_allocate_pre3a_sec) 9%nat 0%nat).
Variable tsd : ltac:(sec_ty2 constr:(SEC_T_art_allocate_pre3a_sec) 10%nat 0%nat).
Variable ctx : ltac:(sec_ty2 constr:(SEC_T_art_allocate_pre3a_sec) 11%nat 0%nat).
Variable t : ltac:(sec_ty2 constr:(SEC_T_art_allocate_pre3a_sec) 12%nat 0%nat).
Variable rl : ltac:(sec_ty2 constr:(SEC_T_art_allocate_pre3a_sec) 13%nat 0%nat).
Variable rs : ltac:(sec_ty2 constr:(SEC_T_art_allocate_pre3a_sec) 14%nat 0%nat).
Variable qr : ltac:(sec_ty2 constr:(SEC_T_art_allocate_pre3a_sec) 15%nat 0%nat).
Variable rz : ltac:(sec_ty2 constr:(SEC_T_art_allocate_pre3a_sec) 16%nat 0%nat).
Variable qz : ltac:(sec_ty2 constr:(SEC_T_art_allocate_pre3a_sec) 17%nat 0%nat).
Theorem art_allocate_pre3a_sec : ltac:(sec_stmt2 constr:(SEC_T_art_allocate_pre3a_sec) 18%nat 0%nat).
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
pose proof (art_alloc_a3_sec_fn r4 M3 rom (sp - 128) ia n rl rs rz tp key tsd ctx t Q2 Q4 Q8 ltac:(rewrite P4_10; f_equal; lia) Q18 P4_19 Q20 Q21 Q22 Q26
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
