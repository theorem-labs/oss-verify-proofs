(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib RefMemcpyLib
MemSplit ArtMem ArtRegs ArtAtomics ArtAtomics2 ArtTac JatAllocG JatDepotA JatDepotB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLiaT.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import OtfKit.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__JatDepot () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ArtMem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatAllocG."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatDepot."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatDepotA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1S"; "1bool"; "1nat"; "1option"; "1orb"; "1true"; "2I"; "2and"; "2eq"; "2ex"; "2not"; "2or"; "3Z"; "4store_ok"; "5bvmap"; "0M"]; ["0M'"; "0N"; "0P"; "6Wn"; "6apart"; "6cell"; "6wok"; "6wr"; "7msteps"; "8art_depot_frame"; "8art_depot_spec"; "8art_dpre_frame"; "8nodp"; "9DInvD"; "9DPreD"; "9DRoD"]; ["9dprivD"; ":DEP"; ":MAP1"; ":NID"; ";getr"; ";mkst"; "<loaded_segments"; "=add"; "=le"; "=lt"; "=ltb"; "=modulo"; "=mul"; "=of_nat"; "=pow"; "=sub"]; ["0X"; "0a"; "0adr"; "0b"; "0blk"; "0c"; "0fx"; "0h"; "0i"; "0id"; "0k"; "0l2"; "0m"; "0n"; "0nd"; "0r"]; ["0regs"; "0regs'"; "0rom"; "0s"; ">BV"; ">Z_to_bv"; ">bv"; ">bv_unsigned"; "0szt"; "0trp"; "0v"; "0w"; "0x"]]).
Local Ltac oF' pc := oF constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc.
Local Ltac oD' pc := oD constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc.
Local Ltac oE' pc := oE constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc.
Local Ltac oW' pc := oW constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc. Local Ltac lia := L5FastLiaT.plia2.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation cellA := (cell Asan.M.loaded_segments).
#[local] Abbreviation wrA := (wr Asan.M.loaded_segments).
#[local] Abbreviation wokA := (wok Asan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).
Definition dprivD (l2 blk x : Z) : Prop := 0x20cbc8 <= x < 0x65cbe8 \/ l2 <= x < l2 + 2 ^ 20 \/ blk <= x < blk + 2 ^ 23.
Definition DRoD (M : word -> option byte) : Prop :=
cellA M 0x102e8 8 0xc6a4a7935bd1e995 /\ cellA M 0x10320 8 0x35253c9ade8f4ca8 /\ cellA M 0x103f8 8 0x9747b28c9747b28c.
Definition DPreD (blk : Z) (M : word -> option byte) (trp szt : Z) : Prop :=
1 <= szt <= 30 /\ trp mod 8 = 0 /\ 4096 <= trp /\ trp + 8 * szt < 2 ^ 64 /\ apart trp (8 * szt) blk (2 ^ 23)
/\ (forall i, 0 <= i < szt -> rcell M (trp + 8 * i)).
Definition DInvD (l2 blk : Z) (k : nat) (M : word -> option byte) : Prop :=
exists N TF ST,
0x691000 <= l2 /\ l2 + 2 ^ 20 < 2 ^ 47 /\ l2 mod 4096 = 0 /\ 0x691000 <= blk /\ blk + 2 ^ 23 < 2 ^ 47 /\ blk mod 4096 = 0 /\ apart l2 (2 ^ 20) blk (2 ^ 23)
/\ cellA M NID 4 N /\ 0 <= N /\ N + Z.of_nat k < 2 ^ 16 - 1
/\ cellA M STO 8 TF /\ 0 <= TF /\ TF + 31 * Z.of_nat k <= 2 ^ 20 - 64
/\ cellA M (STO + 24) 4 ST /\ 0 <= ST /\ ST + 31 * Z.of_nat k < 2 ^ 20
/\ cellA M MAP1 8 l2 /\ cellA M (STO + 16) 8 blk
/\ (forall b, 0 <= b < 2 ^ 20 -> exists v, cellA M (DEP + 4 * b) 4 v /\ 0 <= v <= N)
/\ dp_nodes M l2 N
/\ wrA M DEP 4194308 /\ wrA M STO 32 /\ wrA M l2 (2 ^ 20) /\ wrA M blk (2 ^ 23).
Lemma store_ok_agree : ltac2:(TCodec.tc2 tcn__JatDepot "QI'2'R6yR0%211'3y8%511%311p051&Q8&Q7&R7r1%22;1&Q=r4%211%7241&Q>+2+R0%3221%=251'7r3%>2G1%A21=&Q9r6%?11%D251%42B1%9261'8r5r2%211%912%53O21p071pTJQ51'1&=&Q6%241:D@(5%=3521r7%645>Q11%@3814p041p0;1p0N1pTHQB1pQ2Q>1pQ0Q?1pSFQH1").
Proof.
induction k as [|k IH]; intros M M' w Hnw AGw S; [reflexivity|]. cbn [store_ok] in S |- *.
unfold wview in S |- *. rewrite (AGw w) by lia.
assert (NEXT : store_ok ASEGS M (w + 1)%bv k = true -> store_ok ASEGS M' (w + 1)%bv k = true).
{ intros S1. destruct k as [|k']; [reflexivity|].
pose proof (u64_range w). assert (U1 : U (w + 1)%bv = U w + 1) by (apply u_add1; lia).
apply (IH M M'); [rewrite U1; lia | | exact S1]. intros x Hx. apply AGw. rewrite U1 in Hx. lia. }
destruct (M w) as [b|].
- apply NEXT. exact S.
- destruct (find_segment _ _ _) as [seg|]; [|discriminate]. destruct (seg_writable seg); [|discriminate].
destruct (segment_byte_at _ _); [|discriminate]. apply NEXT. exact S.
Qed.
Lemma wr_agree : ltac2:(TCodec.tc2 tcn__JatDepot "QE'R6yR0%211'3y8%511%311p051'<&Q8zr2%3221&Q7r3%2214&Q>+2+R0%3221%;251'7r5&R7r1%22H1%A241&Q9r4%@271%3251%:251'8r7%11Gr8%11I%53O31p071pTJQ51&G&Q6%2419D>r6%443;1Fp031p071p0K1p0Q41pSLQ91pS4Q:1pQ2Q<1pQ0Q=1").
Proof.
intros M M' a n Ha Han AG W d k Hd Hk. specialize (W d k Hd Hk). destruct k as [|k]; [reflexivity|].
rewrite Nat2Z.inj_succ in Hk.
apply (store_ok_agree (S k) M M'); [rewrite art_u_lit by lia; rewrite Nat2Z.inj_succ; lia | | exact W].
intros x Hx. rewrite art_u_lit in Hx by lia. rewrite Nat2Z.inj_succ in Hx. apply AG. lia.
Qed.
Section SE.
Local Abbreviation SEC_T_DInvD_frame := (ltac2:(TCodec.tc2 tcn__JatDepot ";'<&I&Mr2r1%3221&Q0%1243%7231pS:91pSH:1")) (only parsing).
Variable l2 : ltac:(sec_ty2 constr:(SEC_T_DInvD_frame) 0%nat 0%nat).
Variable blk : ltac:(sec_ty2 constr:(SEC_T_DInvD_frame) 1%nat 0%nat).
Lemma DInvD_frame : ltac:(sec_stmt2 constr:(SEC_T_DInvD_frame) 2%nat 0%nat).
Proof.
intros k M M' (N & TF & ST & G1 & G2 & G3 & G4 & G5 & G6 & G7 & CN & RN & BN & CTF & RTF & BTF & CST & RST & BST & CM1 & CBL & BK & ND & W1 & W2 & W3 & W4) AG.
unfold dprivD in AG. exists N, TF, ST. unfold NID, STO, MAP1, DEP in *.
zsplit; try assumption.
- apply (cell_agree M M'); [intros x Hx; apply AG; cbn in Hx; lia | lia | cbn; lia | exact CN].
- apply (cell_agree M M'); [intros x Hx; apply AG; cbn in Hx; lia | lia | cbn; lia | exact CTF].
- apply (cell_agree M M'); [intros x Hx; apply AG; cbn in Hx; lia | lia | cbn; lia | exact CST].
- apply (cell_agree M M'); [intros x Hx; apply AG; cbn in Hx; lia | lia | cbn; lia | exact CM1].
- apply (cell_agree M M'); [intros x Hx; apply AG; cbn in Hx; lia | lia | cbn; lia | exact CBL].
- intros b Hb. destruct (BK b Hb) as (v & Cv & Rv). exists v. split; [|exact Rv].
apply (cell_agree M M'); [intros x Hx; apply AG; cbn in Hx; lia | lia | cbn; lia | exact Cv].
- intros id Hid. destruct (ND id Hid) as (hv & lk & Rhv & Chv & Clk & Rlk). exists hv, lk.
split; [exact Rhv|]. split; [|split; [|exact Rlk]].
+ apply (cell_agree M M'); [intros x Hx; apply AG; cbn in Hx; lia | lia | cbn; lia | exact Chv].
+ apply (cell_agree M M'); [intros x Hx; apply AG; cbn in Hx; lia | lia | cbn; lia | exact Clk].
- apply (wr_agree M M'); [lia | lia | intros x Hx; apply AG; lia | exact W1].
- apply (wr_agree M M'); [lia | lia | intros x Hx; apply AG; lia | exact W2].
- apply (wr_agree M M'); [lia | lia | intros x Hx; apply AG; lia | exact W3].
- apply (wr_agree M M'); [lia | lia | intros x Hx; apply AG; lia | exact W4].
Qed.
End SE.
Lemma DPreD_frame : ltac2:(TCodec.tc2 tcn__JatDepot "7'<&K&Nr1%211%411pS:61").
Proof.
intros blk M M' trp szt (Hs & Ha & Ht & Ht' & AP & RC) AG. repeat (split; [assumption|]).
intros i Hi. destruct (RC i Hi) as (bs & R). exists bs.
rewrite <- R. apply rdn_ext; [rewrite art_u_lit by lia; cbn; lia|]. intros x Hx. rewrite art_u_lit in Hx by lia. apply AG. cbn in Hx. lia.
Qed.
Lemma DPreD_intro : ltac2:(TCodec.tc2 tcn__JatDepot "R='<'R6yR0%211'3y8%511%311p051'7&Q8+1r1%3221+N%5231%7231'8&Q;r3+8%3221z%63G21+TP0r4%@221&Q9&Q7r5&Q<%12;6%4231&Q>+2+R0%3221%:251&Dr6%:2D;r8+G%:291%645431%Q32GQ1r7%D2Q31%Q7231'9&E&Q6r;r:%H2Q2Q3%K221u8&R7%12QHQ>%9587431qTHQI1%<2QJ1p0>1pSBQO1&Nr9%24=1IDp041p0H1p0Q01p0Q<1p0Q@1p0QH1pTBR91pTDR:1pQ0R31pS:R<1").
Proof.
intros blk M trp szt Hs Ha Ht Ht' AP CW. repeat (split; [assumption|]).
intros i Hi. destruct (CW i Hi) as [w C]. eexists. exact C.
Qed.
Lemma DRoD_frame : ltac2:(TCodec.tc2 tcn__JatDepot "Q5'R6yR0%211'3y8%511%311p051pTJ62&Or2%211'7&Q8+RPP0&R7r1%22@1%5241&Q9+RQbn8%2241%:241'8r4%11?r5%11A%53F31p071pTJL1r3%G11p031p0G1pQ2K1pQ0M1").
Proof.
intros M M' (C1 & C2 & C3) AG. unfold DRoD.
repeat split; (apply (cell_agree M M'); [intros x Hx; apply AG; cbn in Hx; lia | lia | cbn; lia | assumption]).
Qed.
Section SE.
Local Abbreviation SEC_T_DInvD_weaken := (ltac2:(TCodec.tc2 tcn__JatDepot "I'<'2'R6yR0%211'3y8%511%311p051&Mr4r3(0r2%211r1%746521r5%941875p031pQ0<1pSFE1pS:G1pSHH1")) (only parsing).
Variable l2 : ltac:(sec_ty2 constr:(SEC_T_DInvD_weaken) 0%nat 0%nat).
Variable blk : ltac:(sec_ty2 constr:(SEC_T_DInvD_weaken) 1%nat 0%nat).
Variable k : ltac:(sec_ty2 constr:(SEC_T_DInvD_weaken) 2%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_DInvD_weaken) 3%nat 0%nat).
Lemma DInvD_weaken : ltac:(sec_stmt2 constr:(SEC_T_DInvD_weaken) 4%nat 0%nat).
Proof.
intros (N & TF & ST & H).
exists N, TF, ST. rewrite Nat2Z.inj_succ in H. zsplit; try tauto; lia.
Qed.
End SE.
Lemma nodp_apart : ltac2:(TCodec.tc2 tcn__JatDepot "Q6'<!p021&Lr5r4r3%43321'7&Q8r1%2261&Q9&Q7%1298%3251%8251r8r2%211p041pSBE1z%;21C%<22C&Dr7r6%34;21Hp051p071p0:1p0I1pSJQ11pS8Q21pSLQ31pS4Q41pQ6Q31").
Proof.
intros P a n b m NP PB Hn Hm. unfold apart. destruct (Z_lt_le_dec b (a + n)) as [L|G]; [|left; lia].
destruct (Z_lt_le_dec a (b + m)) as [L'|G']; [|right; lia].
destruct (Z_lt_le_dec a b) as [L''|G''].
- exfalso. apply (NP b ltac:(lia)). apply PB. lia.
- exfalso. apply (NP a ltac:(lia)). apply PB. lia.
Qed.
Section FPX. Context {fx : PropExec.FPState}.
#[local] Ltac wpc := lazymatch goal with |- msteps _ (mkstr _ ?p _ _ _) _ => wlit p | |- msteps _ (mkst _ ?p _ _) _ => wlit p end.
Section SE.
Local Abbreviation SEC_T_dp_ins_run := (ltac2:(TCodec.tc2 tcn__JatDepot "X5&>y5'R6yR0%211%5241'3y8%611%311p061'<'8&Q4r8(R4+:(6%33A21%6251&R5r4%22C1%;3C41r9+I%;3I19%>231r5%92J1%B3J31r:+9%B3Q01@%E231&Q1%@2Q11%I3Q131r;+H%I3Q71G%L231&Q2%G2Q81%Q03Q831r<+F%Q03Q>1N%Q3231+QooO%N2Q?1%Q73Q?31r=+C%Q73QE1Q5%Q:231%Q42QEQ:%Q=3QE21r>+2%Q=3QK1Q;%Q@231&Q?+S@%22J1%Q=2QN1%QF3QN51&Q8+TP0+W0%82I1%4231&Q9&Q>+R0%22@1%42H1'7z%<21K%=2LQ:%4221%?24Q5&Q7+1%22Q11+@%>2L1%@231r?%G2<1%C22@%?221+VbTP0%K21Q4+D%G2Q51%>281+Q?%J2Q81%L231&E&Q6rF&Q3u4rA%6554321rGu8%9582R414&FrH%24;198'9'H&Q5vQFrK+cVP<%S93SE1S7/01SErJrI%8576321r1+cTl4%S@3SL1S>/01SL&CrE%Q@21Q?%34K:L1%A5@851:%C3Q0:1%SJ2:SErD&Q<%12QD7%QH231%SH2T91%T13T961+;%T03T>1SN%T32C1%SM2T>R3%T63T>21+<%T53TC1T3%T82H1+S8%RI2Q71%T42TE1%T=3TE41+=%T<3TJ1T:%T?2O1%T92TJQF%TB3TJ21%T@3TNR;T>%TC2Q31+cVTD%TC3TO1TA/01TO%TH3U041%TH2Q8S9%S82QFS7%TC2U41%TL3U431+G%TK3U91TI%TN2Q>1%TH2U9Q9%U13U921%U12QAT=%U33U;1Q3+E%U23U@1U0%U52QE1%TO2U@R7%U83U@21+8%U73UE1U5%U:2QJ1%U;2R22%U=3UE21+B%U<3UJ1U:%U?2QO1%U@2R72%UB3UJ21%UM1UN&:%UE32R4Q2%211r2%UH351U3%511r3%UK381F%811%UM3:UDO%:11&R7%12V;U@%T:2UM1%T;22QD%T2221%@11r7r6%V6221rQ1%V8213%V:3VB31p071p0>1p0A1p0E1p0I1pT0M1%T@2O1%TA2Q51%TB2Q;1%TC2QA1%TD2QD1%TE2QJ1%TF2QO1%TG2R61%TH2R<1%TI2RD1%TJ2RJ1%TK2S21qT4W41%SH2W51p0SJ1p0SN1p0T21p0T:1p0TA1p0TD1p0TI1p0U01p0U21p0U81p0U>1p0UD1p0UN1p0V51p0V=1p0VE1p0VM1p0W51pSHWB1pQ4WC1pS@WD1pTFWE1pT8WF1pT6WH1pS2WI1pT2WO1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_dp_ins_run) 0%nat 0%nat).
Variable X : ltac:(sec_ty2 constr:(SEC_T_dp_ins_run) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_dp_ins_run) 2%nat 0%nat).
Variable s : ltac:(sec_ty2 constr:(SEC_T_dp_ins_run) 3%nat 0%nat).
Variable v : ltac:(sec_ty2 constr:(SEC_T_dp_ins_run) 4%nat 0%nat).
Variable h : ltac:(sec_ty2 constr:(SEC_T_dp_ins_run) 5%nat 0%nat).
Variable N : ltac:(sec_ty2 constr:(SEC_T_dp_ins_run) 6%nat 0%nat).
Variable l2 : ltac:(sec_ty2 constr:(SEC_T_dp_ins_run) 7%nat 0%nat).
Lemma dp_ins_run : ltac:(sec_stmt2 constr:(SEC_T_dp_ins_run) 8%nat 0%nat).
Proof using Type regs X rom s v h N l2.
intros H10 H25 H9 H24 H22 H19 H2 Hs Hs' Hv HN HN' Hh Hl2 Hl2' CN CM WN.
unfold NID, MAP1, DEP in *.
pose proof (Z.div_small (N + 1) (2 ^ 16) ltac:(lia)) as D16.
eexists. split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]]]]]].
- zstep (ltac:(oF' 0x9980c%Z)) (ltac:(oD' 0x9980c%Z)).
zbtk (ltac:(oF' 0x99810%Z)) (ltac:(oD' 0x99810%Z)).
stepn (ltac:(oF' 0x9983c%Z)) (ltac:(oD' 0x9983c%Z)).
zstep (ltac:(oF' 0x99840%Z)) (ltac:(oD' 0x99840%Z)).
zstep (ltac:(oF' 0x99844%Z)) (ltac:(oD' 0x99844%Z)).
replace (2214872 + 4194304) with 6409176 by lia.
chain_step; [reflexivity
| eapply (art_step_amoadd_w_rd _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 6409176) (Z_to_bv 64 1) (Z_to_bv 64 N));
[ exact (ltac:(oF' 0x99848%Z)) | reflexivity | exact (ltac:(oD' 0x99848%Z)) | reflexivity | gres; rwH; reflexivity | rewrite art_u_lit by lia; reflexivity
| exact CN | apply art_bytes4; lia | rewrite art_u_lit by lia; lia | gres; rwH; reflexivity | exact WN ]
| ]. wpc. rewrite art_zb_add. rewrite art_v_lw_small by lia.
change (wbytes ?M0 (Z_to_bv 64 6409176) (word_to_le_bytes 4 (Z_to_bv 64 (N + 1)))) with (Wn 4 M0 6409176 (N + 1)).
stepn (ltac:(oF' 0x9984c%Z)) (ltac:(oD' 0x9984c%Z)). rwH. unfold v_addiw. rewrite art_u_lit by lia.
replace (bv_swrap 32 (N + 1)) with (N + 1) by (unfold bv_swrap, bv_wrap; change (bv_half_modulus 32) with (2 ^ 31); change (bv_modulus 32) with (2 ^ 32); rewrite Z.mod_small; lia).
zstep (ltac:(oF' 0x99850%Z)) (ltac:(oD' 0x99850%Z)).
stepn (ltac:(oF' 0x99854%Z)) (ltac:(oD' 0x99854%Z)). rwH. rewrite (art_zb_srli_exact ((N + 1) * 2 ^ 32) 32 (N + 1)) by lia.
stepb_ft (ltac:(oF' 0x99858%Z)) (ltac:(oD' 0x99858%Z)) ltac:(zconds).
zstep (ltac:(oF' 0x9985c%Z)) (ltac:(oD' 0x9985c%Z)).
stepn (ltac:(oF' 0x99860%Z)) (ltac:(oD' 0x99860%Z)). rwH. rewrite art_zb_srli by lia. rewrite D16.
zstep (ltac:(oF' 0x99864%Z)) (ltac:(oD' 0x99864%Z)).
zstep (ltac:(oF' 0x99868%Z)) (ltac:(oD' 0x99868%Z)).
match goal with |- msteps _ (mkst _ _ ?Y _) _ => assert (CM' : cellA Y 6409192 8 l2) by zcell end.
zld (ltac:(oF' 0x9986c%Z)) (ltac:(oD' 0x9986c%Z)) 6409192 CM'.
zbft (ltac:(oF' 0x99870%Z)) (ltac:(oD' 0x99870%Z)).
stepn (ltac:(oF' 0x99874%Z)) (ltac:(oD' 0x99874%Z)). rwH. rewrite art_zb_and by lia. change 65535 with (Z.ones 16). rewrite Z.land_ones by lia.
rewrite (Z.mod_small (N + 1) (2 ^ 16)) by lia.
zstep (ltac:(oF' 0x99878%Z)) (ltac:(oD' 0x99878%Z)).
zstep (ltac:(oF' 0x9987c%Z)) (ltac:(oD' 0x9987c%Z)).
zstep (ltac:(oF' 0x99880%Z)) (ltac:(oD' 0x99880%Z)).
zstep (ltac:(oF' 0x99884%Z)) (ltac:(oD' 0x99884%Z)).
zstep (ltac:(oF' 0x99888%Z)) (ltac:(oD' 0x99888%Z)).
zstep (ltac:(oF' 0x9988c%Z)) (ltac:(oD' 0x9988c%Z)).
stepn (ltac:(oF' 0x99890%Z)) (ltac:(oD' 0x99890%Z)).
replace (l2 + (N + 1) * 2 ^ 4) with (l2 + 16 * (N + 1)) by lia. replace (s - 112 + 8) with (s - 104) by lia.
apply mst_refl.
- kept_solve.
- kept_solve.
- kept_solve.
- kept_solve.
- gres. apply bv_eq. vm_compute. reflexivity.
- kept_solve.
- kept_solve.
- kept_solve.
- kept_solve.
- kept_solve.
- kept_solve.
- intros r N1 N9 N21 N23 NR.
destruct (decide (r = 10%bv)) as [->|N10]; [exfalso; apply NR; clear; vm_compute; split; discriminate|].
destruct (decide (r = 11%bv)) as [->|N11]; [exfalso; apply NR; clear; vm_compute; split; discriminate|].
destruct (decide (r = 12%bv)) as [->|N12]; [exfalso; apply NR; clear; vm_compute; split; discriminate|].
destruct (decide (r = 13%bv)) as [->|N13]; [exfalso; apply NR; clear; vm_compute; split; discriminate|].
kept_solve.
Qed.
End SE.
#[using="Type"] Lemma dp_tail_run : ltac2:(TCodec.tc2 tcn__JatDepot "T<&>y5'R6yR0%211%5241'3y8%611%311p061'<'8&Q4r8(R4+9(6%33A21%6251&R5r4%22C1%;3C41r9+E%;3I19%>231%@3H16r:+G%@3N1>%C231%E3M1;r;+B%E3Q31C%H231%J3Q21@r<+8%J3Q81H%M231z%H2Q91%Q13Q931&Q8%124G&Q9&Q7+@%22F1&Q>+2+R0%3221%8251%;2>Q;+4%:2Q31%<215'7%@2CG%?2H8%3221&F&Q6rBr?%D21Mu4%645421rCr=%948214'9'H&Q5vQFrF+cVTD%R23R>1R0/01R>rErD%8576321r1+cVU@%R93RE1R7/01RE&C%Q:2HQCrA%34G:21r@%54I2K1%C5B:71<%E3O<1+:%RD3S21RB%RG2>1%RA2S27%RJ3S221%S51S6&:%RM32C6%211r3r2%S0221rH%S2213%S43S<31p071pT0;1%QF2=1%QG2C1qT4S@1%Q;2SA1p0Q=1p0QA1p0QI1p0QJ1p0QO1p0R31p0R51p0R?1p0RB1p0RJ1p0S01p0S61p0S<1pS6SI1pSDSJ1pTFSK1pSNSL1pT8SM1pT6SO1pS2T01pT2T61").
Proof.
intros regs X rom s nd v id adr H9 H21 H23 H18 H8 Hn Hn' Ha Ha' Hv Hid W1 W2.
eexists. split; [|split].
- zsw (ltac:(oF' 0x99894%Z)) (ltac:(oD' 0x99894%Z)) (nd + 8) v ltac:(exact W1).
stepfence (ltac:(oF' 0x99898%Z)) (ltac:(oD' 0x99898%Z)).
zstep (ltac:(oF' 0x9989c%Z)) (ltac:(oD' 0x9989c%Z)).
zsw (ltac:(oF' 0x998a0%Z)) (ltac:(oD' 0x998a0%Z)) adr id ltac:(apply wok_Wn; exact W2).
zbtk (ltac:(oF' 0x998a4%Z)) (ltac:(oD' 0x998a4%Z)).
apply mst_refl.
- kept_solve.
- intros r N10. kept_solve.
Qed.
#[using="Type"] Lemma nrange_lit : ltac2:(TCodec.tc2 tcn__JatDepot "I'<'8'1&4&Q:r1r3%3221r2%5214%7231(5%;3:21&:'7&Q8r4%2219%32:<%5221%711p091pS<F1pS8G1pS4H1").
Proof. intros a b c H [L1 L2]. apply Bool.orb_true_iff in H. destruct H as [H|H]; apply Z.ltb_lt in H; lia. Qed.
Ltac nlit := first [ let E := fresh in intros E; discriminate E | apply nrange_lit; vm_compute; reflexivity ].
#[using="Type"] Lemma reg_cases_18_27 : ltac2:(TCodec.tc2 tcn__JatDepot "QI'R6y5%211'7&Q8+B&R7r1%2271%5241+K%7231%9231';'8r2(R4(6%23A=1%53A41+C%53D14%83D71+D%83G17%;3G:1+E%;3J1:%>3J=1+F%>3M1=%A3M@1+G%A3Q01@%D3Q0C1+H%D3Q31C%G3Q3F1+I%G3Q61F%J3Q6I1+J%J3Q91I%M3Q9L1%L3Q;Q2K%O3Q;N1%Q1231%Q2271%Q32;1%Q42?1%Q52C1%Q62G1%Q72K1%Q82O1%Q92Q31p0Q;1pT0QF1").
Proof.
intros r Hr.
assert (E : U r = 18 \/ U r = 19 \/ U r = 20 \/ U r = 21 \/ U r = 22 \/ U r = 23 \/ U r = 24 \/ U r = 25 \/ U r = 26 \/ U r = 27) by lia.
destruct E as [E|[E|[E|[E|[E|[E|[E|[E|[E|E]]]]]]]]];
[left|right;left|do 2 right;left|do 3 right;left|do 4 right;left|do 5 right;left|do 6 right;left|do 7 right;left|do 8 right;left|do 9 right];
apply bv_eq; exact E.
Qed.
Section SE.
Local Abbreviation SEC_T_art_depot_spec_holds := (ltac2:(TCodec.tc2 tcn__JatDepot "@'<&JvQF&Mr2r1%3221&N%113&Q0%1265&O+W0%<6;75321pS:>1pSH?1")) (only parsing).
Variable l2 : ltac:(sec_ty2 constr:(SEC_T_art_depot_spec_holds) 0%nat 0%nat).
Variable blk : ltac:(sec_ty2 constr:(SEC_T_art_depot_spec_holds) 1%nat 0%nat).
Theorem art_depot_spec_holds : ltac:(sec_stmt2 constr:(SEC_T_art_depot_spec_holds) 2%nat 0%nat).
Proof using Type l2 blk.
intros k regs M rom raw sp trp szt H1 Hret H2 H10 H11 HDK Hsp Hsp6 W ND DI DP DR.
pose proof DI as DI0.
destruct DI as (N & TF & ST & G1 & G2 & G3 & G4 & G5 & G6 & G7 & CN & RN & BN & CTF & RTF & BTF & CST & RST & BST & CM1 & CBL & BK & NDS & W1 & W2 & W3 & W4).
rewrite Nat2Z.inj_succ in BN, BTF, BST.
destruct DP as (Hsz & Hta & Ht4 & Ht' & AT & RC). destruct DR as (Cm & Ck1 & Ck2).
unfold NID, STO, MAP1, DEP in *.
assert (Al2 : apart (sp - 224) 224 l2 (2 ^ 20)) by (apply (nodp_apart _ _ _ _ _ ND); [intros i Hi; unfold dprivD; lia | lia | lia]).
assert (Ablk : apart (sp - 224) 224 blk (2 ^ 23)) by (apply (nodp_apart _ _ _ _ _ ND); [intros i Hi; unfold dprivD; lia | lia | lia]).
assert (Ast : apart (sp - 224) 224 0x20cbc8 4456992) by (apply (nodp_apart _ _ _ _ _ ND); [intros i Hi; unfold dprivD; lia | lia | lia]).
destruct (dp_pro_run regs M rom raw sp trp szt 0xc6a4a7935bd1e995 0x35253c9ade8f4ca8 0x9747b28c9747b28c H2 H10 H11 H1 Hsp6 Hsp Ht4 Ht' Hsz
ltac:(lia) ltac:(lia) ltac:(lia) Cm Ck1 Ck2 W) as (r1 & h0 & RUN1 & P11 & P14 & P10 & P12 & Rh0 & P13 & P8 & P9 & P2 & K1).
set (F := dp_frame M sp trp szt raw regs) in RUN1.
assert (GF : mem_grows M F) by (unfold F, dp_frame; repeat (eapply mem_grows_trans; [|apply Wn_grows]); apply mem_grows_refl).
assert (OF : forall x : word, ~ (sp - 104 <= U x < sp) -> F x = M x).
{ intros x Hx. pose proof (u64_range x). unfold F, dp_frame. rewrite !Wn_outside by (first [lia | cbn; lia]). reflexivity. }
assert (RCF : forall j, 0 <= j < szt -> rcell F (trp + 8 * j)) by (intros j Hj; apply (rcell_grows M F _ GF); apply RC; exact Hj).
replace (Z_to_bv 64 trp : word) with (Z_to_bv 64 (trp + 8 * 0) : word) in P11 by (f_equal; lia).
destruct (dp_hash_loop (Z.to_nat (szt - 1)) r1 F rom trp szt 0xc6a4a7935bd1e995 0 h0 RCF ltac:(lia) ltac:(lia) ltac:(lia) Rh0 ltac:(lia)
ltac:(rewrite Z2Nat.id by lia; lia) P11 P14 P10 P12) as (r2 & hN & RUN2 & Q11 & Q12 & RhN & K2).
unfold DEP, MAP1 in *.
assert (X13 : getr r2 13 = Z_to_bv 64 0) by (rewrite (K2 13%bv) by (intros E; discriminate E); exact P13).
assert (X10 : getr r2 10 = Z_to_bv 64 0xc6a4a7935bd1e995) by (rewrite (K2 10%bv) by (intros E; discriminate E); exact P10).
assert (X9 : getr r2 9 = Z_to_bv 64 2214872) by (rewrite (K2 9%bv) by (intros E; discriminate E); exact P9).
assert (BKF : forall b, 0 <= b < 2 ^ 20 -> exists v, cellA F (2214872 + 4 * b) 4 v /\ 0 <= v <= N).
{ intros b Hb. destruct (BK b Hb) as (v & Cv & Rv). exists v. split; [|exact Rv].
apply (cell_agree M F); [intros x Hx; apply OF; unfold apart in Ast; cbn in Hx; lia | lia | cbn; lia | exact Cv]. }
destruct (dp_mid_run r2 F rom hN 0xc6a4a7935bd1e995 N Q12 X13 X10 X9 RhN ltac:(lia) ltac:(lia) BKF)
as (r3 & h & b & v & RUN3 & Rh & Rb & Cv & Rv & T19 & T18 & T11 & T25 & T24 & T20 & T22 & T23 & T9 & K3).
assert (CM1F : cellA F 6409192 8 l2) by (apply (cell_agree M F); [intros x Hx; apply OF; unfold apart in Ast; cbn in Hx; lia | lia | cbn; lia | exact CM1]).
assert (NDSF : dp_nodes F l2 N).
{ intros id Hid. destruct (NDS id Hid) as (hv & lk & Rhv & Chv & Clk & Rlk). exists hv, lk. split; [exact Rhv|]. split; [|split; [|exact Rlk]].
- apply (cell_agree M F); [intros x Hx; apply OF; unfold apart in Al2; cbn in Hx; lia | lia | cbn; lia | exact Chv].
- apply (cell_agree M F); [intros x Hx; apply OF; unfold apart in Al2; cbn in Hx; lia | lia | cbn; lia | exact Clk]. }
assert (Hl16 : l2 mod 16 = 0).
{ apply (proj2 (Z.mod_divide l2 16 ltac:(lia))). apply (Z.divide_trans 16 4096 l2); [exists 256; reflexivity | apply (proj1 (Z.mod_divide l2 4096 ltac:(lia))); exact G3]. }
destruct (dp_find_loop (Z.to_nat v) r3 F rom l2 N h v ltac:(lia) CM1F ltac:(lia) ltac:(lia) Hl16 ltac:(lia) NDSF ltac:(lia) Rh T11 T19 T24 T22)
as (r4 & ALT & K4).
assert (Y2 : getr r4 2 = Z_to_bv 64 (sp - 112)).
{ rewrite (K4 2%bv) by nlit. rewrite (K3 2%bv) by nlit. rewrite (K2 2%bv) by nlit. exact P2. }
assert (L1 : cellA F (sp - 8) 8 (U raw)) by (unfold F, dp_frame; zcell).
assert (L2 : cellA F (sp - 16) 8 (U (getr regs 8))) by (unfold F, dp_frame; zcell).
assert (L3 : cellA F (sp - 24) 8 (U (getr regs 9))) by (unfold F, dp_frame; zcell).
assert (L4 : cellA F (sp - 32) 8 (U (getr regs 18))) by (unfold F, dp_frame; zcell).
assert (L5 : cellA F (sp - 40) 8 (U (getr regs 19))) by (unfold F, dp_frame; zcell).
assert (L6 : cellA F (sp - 48) 8 (U (getr regs 20))) by (unfold F, dp_frame; zcell).
assert (L7 : cellA F (sp - 56) 8 (U (getr regs 21))) by (unfold F, dp_frame; zcell).
assert (L8 : cellA F (sp - 64) 8 (U (getr regs 22))) by (unfold F, dp_frame; zcell).
assert (L9 : cellA F (sp - 72) 8 (U (getr regs 23))) by (unfold F, dp_frame; zcell).
assert (L10 : cellA F (sp - 80) 8 (U (getr regs 24))) by (unfold F, dp_frame; zcell).
assert (L11 : cellA F (sp - 88) 8 (U (getr regs 25))) by (unfold F, dp_frame; zcell).
assert (KF : forall r : reg, r = 3%bv \/ r = 4%bv \/ r = 26%bv \/ r = 27%bv -> getr r4 r = getr regs r).
{ intros r Hr. destruct Hr as [->|[->|[->| ->]]];
(rewrite (K4 _) by nlit; rewrite (K3 _) by nlit; rewrite (K2 _) by nlit; apply K1; nlit). }
destruct ALT as [[RUN4 Z11] | [RUN4 (id & Rid & Z10)]].
2: {
destruct (dp_epi_run regs r4 F rom raw sp Y2 Hret ltac:(lia) Hsp L1 L2 L3 L4 L5 L6 L7 L8 L9 L10 L11)
as (r5 & RUN5 & E10 & E2 & E1 & E8 & E9 & E18 & E19 & E20 & E21 & E22 & E23 & E24 & E25 & K5).
exists r5, F, id. split; [|split; [|split; [|split; [|split; [|split]]]]].
- eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|]. eapply msteps_trans; [exact RUN3|].
eapply msteps_trans; [exact RUN4|]. exact RUN5.
- rewrite E10. exact Z10.
- lia.
- intros r Hk. unfold art_depot_kept in Hk.
destruct Hk as [->|[->|[->|[->|[->|Hk]]]]]; [rewrite E2, H2; reflexivity | | | exact E8 | exact E9 |].
+ rewrite (K5 3%bv) by nlit. apply KF. tauto.
+ rewrite (K5 4%bv) by nlit. apply KF. tauto.
+ destruct (reg_cases_18_27 r Hk) as [->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]; try assumption;
(rewrite (K5 _) by nlit; apply KF; tauto).
- exact GF.
- intros x NDx NWx. apply OF. lia.
- apply DInvD_weaken. apply (DInvD_frame l2 blk (S k) M F DI0). intros x Dx. apply OF.
intros Wx. exact (ND (U x) ltac:(lia) Dx). }
assert (SL : exists r5, msteps ASEGS (mkst r4 (0x99804 : word) F rom) (mkst r5 (0x99e00 : word) F rom)
/\ (getr r5 10 = Z_to_bv 64 (2214872 + 4 * b) /\ getr r5 1 = Z_to_bv 64 0x9980c /\ getr r5 2 = Z_to_bv 64 (sp - 112)
/\ (forall r : reg, r <> 1%bv -> r <> 10%bv -> getr r5 r = getr r4 r))).
{ assert (Y18 : getr r4 18 = Z_to_bv 64 (2214872 + 4 * b)) by (rewrite (K4 18%bv) by nlit; exact T18).
eexists. split.
- zstep (ltac:(oF' 0x99804%Z)) (ltac:(oD' 0x99804%Z)).
stepn (ltac:(oF' 0x99808%Z)) (ltac:(oD' 0x99808%Z)).
apply mst_refl.
- split; [kept_solve|]. split; [kept_solve|]. split; [kept_solve|]. intros r N1 N10. kept_solve. }
destruct SL as (r5 & RUN5 & U10 & U1 & U2 & K5).
assert (WFv : wrA F (2214872 + 4 * b) 4) by (apply (wr_grows _ M F _ _ GF); apply (wr_sub _ _ _ _ _ _ W1); lia).
assert (WFf : wrA F (sp - 112 - 48) 48) by (apply (wr_grows _ M F _ _ GF); apply (wr_sub _ _ _ _ _ _ W); lia).
assert (AM4 : (2214872 + 4 * b) mod 4 = 0) by (replace (2214872 + 4 * b) with ((553718 + b) * 4) by lia; apply Z_mod_mult).
assert (U1' : getr r5 1 = (0x9980c : word)%bv) by (rewrite U1; apply bv_eq; vm_compute; reflexivity).
destruct (dp_lock_run r5 F rom (0x9980c : word)%bv (sp - 112) (2214872 + 4 * b) v U2 U10 U1'
ltac:(unfold ret_ok; apply bv_eq; vm_compute; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) AM4 ltac:(lia)
Cv WFv WFf ltac:(unfold apart in Ast |- *; lia)) as (r6 & RUN6 & V10 & V2 & K6).
set (LM := dp_lock_mem F (sp - 112) (2214872 + 4 * b) v (0x9980c : word)%bv (getr r5 8) (getr r5 9) (getr r5 18) (getr r5 19)) in RUN6.
assert (GLM : mem_grows M LM) by (unfold LM, dp_lock_mem; do 6 (eapply mem_grows_trans; [|apply Wn_grows]); exact GF).
assert (OLM : forall x : word, ~ (sp - 160 <= U x < sp) -> ~ (2214872 + 4 * b <= U x < 2214872 + 4 * b + 4) -> LM x = M x).
{ intros x Hx1 Hx2. pose proof (u64_range x). unfold LM, dp_lock_mem. rewrite !Wn_outside by (first [lia | cbn; lia]). apply OF. lia. }
#[local] Ltac chase K := rewrite (K _) by nlit.
assert (V25 : getr r6 25 = Z_to_bv 64 v) by (chase K6; chase K5; chase K4; exact T25).
assert (V9 : getr r6 9 = Z_to_bv 64 2214872) by (chase K6; chase K5; chase K4; exact T9).
assert (V24 : getr r6 24 = Z_to_bv 64 6409192) by (chase K6; chase K5; chase K4; exact T24).
assert (V22 : getr r6 22 = Z_to_bv 64 65535) by (chase K6; chase K5; chase K4; exact T22).
assert (V19 : getr r6 19 = Z_to_bv 64 h) by (chase K6; chase K5; chase K4; exact T19).
assert (CNL : cellA LM 6409176 4 N) by (apply (cell_agree M LM); [intros x Hx; apply OLM; unfold apart in Ast; cbn in Hx; lia | lia | cbn; lia | exact CN]).
assert (CML : cellA LM 6409192 8 l2) by (apply (cell_agree M LM); [intros x Hx; apply OLM; unfold apart in Ast; cbn in Hx; lia | lia | cbn; lia | exact CM1]).
assert (WNL : wokA LM 6409176 4) by (apply (wr_wok _ _ _ _ (wr_grows _ M LM _ _ GLM W1)); lia).
pose proof (dp_ins_run r6 LM rom sp v h N l2 V10 V25 V9 V24 V22 V19 V2 ltac:(lia) Hsp ltac:(lia) ltac:(lia) ltac:(lia) Rh G1 G2 CNL CML WNL)
as (r7 & RUN7 & I10 & I11 & I12 & I13 & I1 & I2 & I23 & I9 & I21 & I8 & I18 & K7).
set (IM := Wn 4 LM 6409176 (N + 1)) in RUN7.
assert (GIM : mem_grows M IM) by (unfold IM; eapply mem_grows_trans; [exact GLM | apply Wn_grows]).
assert (OIM : forall x : word, ~ (sp - 160 <= U x < sp) -> ~ (2214872 + 4 * b <= U x < 2214872 + 4 * b + 4) -> ~ (6409176 <= U x < 6409180) -> IM x = M x).
{ intros x Hx1 Hx2 Hx3. pose proof (u64_range x). unfold IM. rewrite Wn_outside by (first [lia | cbn; lia]). apply OLM; assumption. }
set (nd := l2 + 16 * (N + 1)) in *. assert (End : nd = l2 + 16 * (N + 1)) by reflexivity.
assert (HND : l2 + 16 <= nd /\ nd + 16 <= l2 + 2 ^ 20 /\ nd mod 16 = 0).
{ subst nd. split; [lia|]. split; [lia|]. apply (proj2 (Z.mod_divide _ 16 ltac:(lia))).
apply Z.divide_add_r; [| exists (N + 1); lia]. apply (proj1 (Z.mod_divide l2 16 ltac:(lia))). exact Hl16. }
assert (HBLK : 0x691000 <= blk /\ blk + 2 ^ 23 < 2 ^ 64 /\ blk mod 8 = 0).
{ split; [lia|]. split; [lia|]. apply (proj2 (Z.mod_divide blk 8 ltac:(lia))).
apply (Z.divide_trans 8 4096 blk); [exists 512; reflexivity | apply (proj1 (Z.mod_divide blk 4096 ltac:(lia))); exact G6]. }
assert (CI1 : cellA IM (sp - 104) 8 trp) by (unfold IM, LM, dp_lock_mem, F, dp_frame; zcell).
assert (CI2 : cellA IM (sp - 96) 8 szt) by (unfold IM, LM, dp_lock_mem, F, dp_frame; zcell).
assert (CI3 : cellA IM 2149320 8 TF) by (apply (cell_agree M IM); [intros x Hx; apply OIM; unfold apart in Ast; cbn in Hx; lia | lia | cbn; lia | exact CTF]).
assert (CI4 : cellA IM (2149320 + 16) 8 blk) by (apply (cell_agree M IM); [intros x Hx; apply OIM; unfold apart in Ast; cbn in Hx; lia | lia | cbn; lia | exact CBL]).
assert (CI5 : cellA IM (2149320 + 24) 4 ST) by (apply (cell_agree M IM); [intros x Hx; apply OIM; unfold apart in Ast; cbn in Hx; lia | lia | cbn; lia | exact CST]).
assert (RCI : forall i, 0 <= i < szt -> rcell IM (trp + 8 * i)) by (intros i Hi; apply (rcell_grows M IM _ GIM); apply RC; exact Hi).
assert (WI1 : wrA IM (sp - 224) 112) by (apply (wr_grows _ M IM _ _ GIM); apply (wr_sub _ _ _ _ _ _ W); lia).
assert (WI2 : wrA IM nd 16) by (apply (wr_grows _ M IM _ _ GIM); apply (wr_sub _ _ _ _ _ _ W3); lia).
assert (WI3 : wrA IM blk (2 ^ 23)) by (apply (wr_grows _ M IM _ _ GIM); exact W4).
assert (WI4 : wrA IM 2149320 32) by (apply (wr_grows _ M IM _ _ GIM); exact W2).
pose proof (dp_store_run IM rom sp nd h trp szt TF ST blk l2) as ST8.
repeat lazymatch type of ST8 with
| forall rg : bvmap 5 word, _ => fail
| ?P -> _ => let HP := fresh in assert (HP : P) by (first [eassumption | lia]); specialize (ST8 HP); clear HP
end.
fold nd in I10, I9.
destruct (ST8 r7 I10 I11 I12 I13 I1 I2) as (r8 & SM & RUN8 & S2' & K8 & G8 & O8 & C1 & C2 & C3 & C4 & C5). clear ST8.
assert (J9 : getr r8 9 = Z_to_bv 64 nd) by (rewrite (K8 9%bv) by (cbv; tauto); exact I9).
assert (J21 : getr r8 21 = Z_to_bv 64 v) by (rewrite (K8 21%bv) by (cbv; tauto); exact I21).
assert (J23 : getr r8 23 = Z_to_bv 64 (N + 1)) by (rewrite (K8 23%bv) by (cbv; tauto); exact I23).
assert (J18 : getr r8 18 = Z_to_bv 64 (2214872 + 4 * b)).
{ rewrite (K8 18%bv) by (cbv; tauto). rewrite I18. chase K6. chase K5. chase K4. exact T18. }
assert (J8 : getr r8 8 = Z_to_bv 64 0).
{ rewrite (K8 8%bv) by (cbv; tauto). rewrite I8. chase K6. chase K5. chase K4. chase K3. chase K2. exact P8. }
assert (GSM : mem_grows M SM) by (eapply mem_grows_trans; [exact GIM | exact G8]).
destruct (dp_tail_run r8 SM rom sp nd v (N + 1) (2214872 + 4 * b) J9 J21 J23 J18 J8 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
ltac:(apply (wr_wok _ _ _ _ (wr_grows _ M SM _ _ GSM W3)); lia) ltac:(apply (wr_wok _ _ _ _ (wr_grows _ M SM _ _ GSM W1)); lia))
as (r9 & RUN9 & J10 & K9).
set (TM := Wn 4 (Wn 4 SM (nd + 8) v) (2214872 + 4 * b) (N + 1)) in RUN9.
unfold apart in Ast, Al2, Ablk, G7.
assert (AG : forall x : word, ~ (sp - 224 <= U x < sp) -> ~ (2214872 + 4 * b <= U x < 2214872 + 4 * b + 4) -> ~ (6409176 <= U x < 6409180) ->
~ (nd <= U x < nd + 16) -> ~ (2149320 <= U x < 2149328) -> ~ (2149344 <= U x < 2149348) ->
~ (blk + 8 * TF <= U x < blk + 8 * TF + 8 * (szt + 1)) -> TM x = M x).
{ intros x X1 X2 X3 X4 X5 X6 X7. pose proof (u64_range x). unfold TM. rewrite !Wn_outside by (first [lia | cbn; lia]).
rewrite (O8 x) by (unfold dp_store_out, STO; repeat split; lia). apply OIM; lia. }
assert (SLOT : forall a u, sp - 88 <= a -> a + 8 <= sp -> cellA F a 8 u -> cellA TM a 8 u).
{ intros a u Ha1 Ha2 C. unfold TM. apply cell_Wn_other; [lia | cbn; lia | lia | cbn; lia | unfold apart; cbn; lia |].
apply cell_Wn_other; [lia | cbn; lia | lia | cbn; lia | unfold apart; cbn; lia |].
apply (cell_agree IM SM); [intros x Hx; apply O8; unfold dp_store_out, STO; cbn in Hx; repeat split; lia | lia | cbn; lia |].
unfold IM, LM, dp_lock_mem. do 7 (apply cell_Wn_other; [lia | cbn; lia | lia | cbn; lia | unfold apart; cbn; lia |]). exact C. }
assert (Z2 : getr r9 2 = Z_to_bv 64 (sp - 112)) by (rewrite (K9 2%bv) by nlit; exact S2').
destruct (dp_epi_run regs r9 TM rom raw sp Z2 Hret ltac:(lia) Hsp
(SLOT (sp - 8) _ ltac:(lia) ltac:(lia) L1) (SLOT (sp - 16) _ ltac:(lia) ltac:(lia) L2) (SLOT (sp - 24) _ ltac:(lia) ltac:(lia) L3) (SLOT (sp - 32) _ ltac:(lia) ltac:(lia) L4) (SLOT (sp - 40) _ ltac:(lia) ltac:(lia) L5) (SLOT (sp - 48) _ ltac:(lia) ltac:(lia) L6) (SLOT (sp - 56) _ ltac:(lia) ltac:(lia) L7) (SLOT (sp - 64) _ ltac:(lia) ltac:(lia) L8) (SLOT (sp - 72) _ ltac:(lia) ltac:(lia) L9) (SLOT (sp - 80) _ ltac:(lia) ltac:(lia) L10) (SLOT (sp - 88) _ ltac:(lia) ltac:(lia) L11))
as (r10 & RUN10 & E10 & E2 & E1 & E8 & E9 & E18 & E19 & E20 & E21 & E22 & E23 & E24 & E25 & K10).
exists r10, TM, (N + 1). split; [|split; [|split; [|split; [|split; [|split]]]]].
- eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|]. eapply msteps_trans; [exact RUN3|]. eapply msteps_trans; [exact RUN4|].
eapply msteps_trans; [exact RUN5|]. eapply msteps_trans; [exact RUN6|]. eapply msteps_trans; [exact RUN7|]. eapply msteps_trans; [exact RUN8|].
eapply msteps_trans; [exact RUN9|]. exact RUN10.
- rewrite E10. exact J10.
- lia.
-
assert (KALL : forall r : reg, r = 3%bv \/ r = 4%bv \/ r = 26%bv \/ r = 27%bv -> getr r10 r = getr regs r).
{ intros r Hr. rewrite <- (KF r Hr). destruct Hr as [->|[->|[->| ->]]];
(chase K10; chase K9; rewrite (K8 _) by (cbv; tauto); chase K7; chase K6; chase K5; reflexivity). }
intros r Hk. unfold art_depot_kept in Hk.
destruct Hk as [->|[->|[->|[->|[->|Hk]]]]]; [rewrite E2, H2; reflexivity | apply KALL; tauto | apply KALL; tauto | exact E8 | exact E9 |].
destruct (reg_cases_18_27 r Hk) as [->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]; try assumption; (apply KALL; tauto).
- unfold TM. do 2 (eapply mem_grows_trans; [|apply Wn_grows]). exact GSM.
- intros x NDx NWx. apply AG; try lia; intros BAD; apply NDx; unfold dprivD; lia.
-
exists (N + 1), (TF + szt + 1), (ST + szt + 1). unfold NID, STO, MAP1, DEP.
assert (WT : forall a n, wrA M a n -> wrA TM a n).
{ intros a n Wa. unfold TM. apply wr_Wn. apply wr_Wn. apply (wr_grows _ M SM _ _ GSM). exact Wa. }
zsplit; try assumption; try lia.
+ unfold TM. do 2 (apply cell_Wn_other; [lia | cbn; lia | lia | cbn; lia | unfold apart; cbn; lia |]).
apply (cell_agree IM SM); [intros x Hx; apply O8; unfold dp_store_out, STO; cbn in Hx; repeat split; lia | lia | cbn; lia |].
unfold IM. apply cell_Wn_hit; cbn; lia.
+ unfold TM. do 2 (apply cell_Wn_other; [lia | cbn; lia | lia | cbn; lia | unfold apart; cbn; lia |]).
replace (TF + szt + 1) with (TF + szt + 1) by lia. exact C1.
+ unfold TM. do 2 (apply cell_Wn_other; [lia | cbn; lia | lia | cbn; lia | unfold apart; cbn; lia |]). exact C2.
+ apply (cell_agree M TM); [intros x Hx; apply AG; cbn in Hx; lia | lia | cbn; lia | exact CM1].
+ unfold TM. do 2 (apply cell_Wn_other; [lia | cbn; lia | lia | cbn; lia | unfold apart; cbn; lia |]). exact C3.
+ intros b' Hb'. destruct (Z.eq_dec b' b) as [->|NE].
* exists (N + 1). split; [|lia]. unfold TM. apply cell_Wn_hit; cbn; lia.
* destruct (BK b' Hb') as (v' & Cv' & Rv'). exists v'. split; [|lia].
apply (cell_agree M TM); [intros x Hx; apply AG; cbn in Hx; lia | lia | cbn; lia | exact Cv'].
+ intros id Hid. destruct (Z.eq_dec id (N + 1)) as [->|NE].
* exists h, v. split; [exact Rh|]. split; [|split; [|lia]].
-- unfold TM. do 2 (apply cell_Wn_other; [lia | cbn; lia | lia | cbn; lia | unfold apart; cbn; lia |]). fold nd. exact C4.
-- unfold TM. apply cell_Wn_other; [lia | cbn; lia | lia | cbn; lia | unfold apart; cbn; lia |]. fold nd. apply cell_Wn_hit; cbn; lia.
* destruct (NDS id ltac:(lia)) as (hv & lk & Rhv & Chv & Clk & Rlk). exists hv, lk. split; [exact Rhv|]. split; [|split; [|exact Rlk]].
-- apply (cell_agree M TM); [intros x Hx; apply AG; cbn in Hx; lia | lia | cbn; lia | exact Chv].
-- apply (cell_agree M TM); [intros x Hx; apply AG; cbn in Hx; lia | lia | cbn; lia | exact Clk].
+ apply WT. exact W1.
+ apply WT. exact W2.
+ apply WT. exact W3.
+ apply WT. exact W4.
Qed.
End SE.
End FPX.
