(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import HeapIfaceAJx PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface HeapIfaceA IcptIfaceA LibIface
AsanAcct AxSymExec3 AxSymExec3Sound SegRun BigLinkBase BigLinkGlue BigModel BigFactsRun BigFactsDigits L5Defs L5Kn L5KnA L5Core L5LazyA L5DefsA
L5CoreA L5CoreSpecsA L5StepAR L5CoreBR
AsanPlanCore AsanPlanSound Ja0PlanKit.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLiaT. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__asan_L5ADetailHR () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanAcct."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIfaceA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs.L5."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5DefsA.L5A."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ShapeAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.StoreOk."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.asan.L5ADetailHR.L5ADHR.SCFG_1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.asan.L5ADetailHR.L5ADHR.SCFG_1.WithIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.asan.L5ADetailHR.L5ADHR.SCFG_1.WithIface.OWN."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.asan.L5CoreA.L5CA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.asan.L5CoreBR.L5CBR."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.asan.L5CoreSpecsA.L5CSA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.asan.L5StepAR.L5SAR."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0A"; "0A0"; "0Ax"; "0BX"; "1None"; "1Some"; "1app"; "1bool"; "1cons"; "1fst"; "1length"; "1list"; "1nat"; "1nil"; "1option"; "1pair"]; ["1prod"; "1snd"; "2I"; "2and"; "2eq"; "2not"; "2or"; "3Z"; "0D"; "0F"; "0FF"; "0FF'"; "0FF0"; "0FFk"; "0FFx"; "0H"]; ["0HI"; "0IL"; "0K"; "0L"; "0LB"; "0LB'"; "0LB0"; "0LBk"; "0LBx"; "0LBy"; "0LK"; "0LK0"; "0LKx"; "4Model"; "5bvmap"; "0M"]; ["0M'"; "0M0"; "0M1"; "0M2"; "0MV"; "0Mk"; "0Mx"; "0R"; "0Ra"; "0Rb"; "6mrestrict"; "7msteps"; "8credit"; "8lb_remove"; "9FS_BYTES"; "9S"]; ["9SB"; "9ablock_range"; "9aclient"; "9aheap_pres"; "9ahid"; "9ar_fs"; "9ar_sptop"; "9fframe"; "9model_rt"; "9ri_inv"; "9vml"; "9vml_of"; ";bytes_at"; ";img_clear"; ";range"; ";u32_at"]; [";u64_at"; ";u8_at"; ":SCFG"; "<avis"; "=FPState"; "=getr"; "=mkst"; "=seg_rom"; ">TSet"; "?srealizes"; "@mem_grows"; "AU"; "Cown"; "Bfrk"; "Bspk"; "Dahpres"]; ["Damodel_ok"; "Daobj"; "Dastk"; "Easrc"; "Fcfg"; "Gek"; "Hloaded_segments"; "0SCFG_P"; "0SCR"; "IIn"; "Iincl"; "Jadd"; "Jdiv"; "Jle"; "Jlt"; "Jof_nat"]; ["Jpow"; "Jsub"; "0V0"; "0Vx"; "0W"; "0a"; "0ar"; "0b"; "0cr"; "0cr0"; "0crx"; "0fx"; "0fx1"; "0j"; "0k"; "0m"]; ["0model"; "0model1"; "0negz"; "0nq"; "0o"; "0p"; "0pc"; "0pc1"; "0q"; "0q'"; "0rr"; "0rs"; "0s"; "0sb"; "0scr"; "0scr'"]; ["0sp"; "0sp'"; "0spc"; "KBV"; "KZ_to_bv"; "Kbv"; "0v"; "0x"; "0z"]]).
Local Ltac lia := L5FastLiaT.plia2.
Local Ltac pvz_hg tac := lazymatch goal with |- ?G0 => let PG := fresh "PGoal" in set (PG := G0); tac; subst PG end.
Local Ltac pvz_fold B k := lazymatch B with | ?A2 /\ ?B2 => pvz_fold B2 ltac:(fun T2 => let T := fresh "pvzT" in pose (T := A2 /\ T2); k T) | _ => k B end.
Local Ltac pvz_lin P := lazymatch type of P with ?A /\ ?B => pvz_fold B ltac:(fun T => change_no_check (A /\ T) in P) | _ => idtac end.
Local Ltac pvz_clrT := repeat match goal with T := (_ /\ _) : Prop |- _ => clear T end.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Module L5ADHR.
Import L5A. Import L5CA. Import L5CSA. Import L5SAR. Import L5CBR.
Section SCFG_1.
Context {SCFG_P : ScfgP}.
Local Ltac inl := apply L5K.in_b; vm_compute; reflexivity.
Local Ltac blia := keep_arith; first [ (repeat match goal with H : _ \/ _ |- _ => clear H end); lia
| match goal with H : _ \/ _ |- _ => clear_disj_but H; destruct H; lia end ].
Local Ltac asm := match goal with H : ?T |- ?G => constr_eq T G; exact H end.
Local Ltac sc := first [ asm | rk | gmem | (arith_goal; first [asm | blia]) | assumption ].
Definition U (R : bvmap 5 word) (k : nat) : Z := bv_unsigned (getr R (reg k)).
#[using="Type"] Lemma UR : ltac2:(TCodec.tc2 tcn__asan_L5ADetailHR "H&Q>y5'TEyR0%211%5241'<'C&S=z&RKr2r1%3221%6251&S>&S@+2+R0%3221%5271%>271pWN@1pS@B1"). Proof. intros R k. unfold U. apply BL.bvu_range. Qed.
#[using="Type"] Lemma U_of : ltac2:(TCodec.tc2 tcn__asan_L5ADetailHR "Q9&Q>y5'TEyR0%211%5241'<'G'D&REr3&TD&S?r2%211%42>1%7261r1%72?1%;3?31'C&S=z%221:&S>&S@+2+R0%3221%52@1%:271&RKr5r4%3221%K3L1Ip061p0B1pYBO1pWNQ11pS@Q31").
Proof. intros R k z. intros H Hz. unfold U. rewrite H. apply L5.unsigned_lit. exact Hz. Qed.
#[using="Type"] Lemma U_to : ltac2:(TCodec.tc2 tcn__asan_L5ADetailHR "F&Q>y5'TEyR0%211%5241'<'D&REr2&TD&S?r1%211%42=1%7261&RK%1285%82?1%<3?41pWN>1pS@@1"). Proof. intros R k. unfold U. symmetry. apply Z_to_bv_bv_unsigned. Qed.
#[using="Type"] Lemma r13 : ltac2:(TCodec.tc2 tcn__asan_L5ADetailHR "?'D'TEy5%211(TC+=(B%33521/015&TD&S?u=%211%42;1%>3;61"). Proof. apply bv_eq; reflexivity. Qed.
#[using="Type"] Lemma byte_of_u8 : ltac2:(TCodec.tc2 tcn__asan_L5ADetailHR "QA'TEyR0%211'>y8%511%311p051'G&RA&S6r3r2r1%544321'F&S>+RPP0%2271&S=+VbTP0%221:%7241'Czr4%7221&S@+2+R0%3221%?261%9261'Dr6&TDr5%22Q41%411(5%52Q4?%22Q41%93Q441p0;1p0F1p0O1pY>Q61pW<Q71pS0Q91").
Proof. intros M a v.
intros U0 HA Ha. unfold L5.u8_at in U0. cbn [rdn] in U0.
destruct (M (Z_to_bv 64 a)) as [b|] eqn:E.
- inversion U0. reflexivity.
- exfalso. unfold seg_rom in U0. unfold memory_read in U0. change (Z.of_N 1) with 1 in U0.
rewrite (as0_in_hull (Z_to_bv 64 a)) in U0. discriminate U0.
rewrite L5.unsigned_lit by lia. unfold APS.in_hull. cbn. destruct HA; [apply andb_false_intro1 | apply andb_false_intro2]; apply Z.leb_gt || apply Z.ltb_ge; lia.
Qed.
Section WithIface.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (IL : icpt_layout) (HI : asan_iface).
Hypothesis LY : as0_layout L C.
Let LY2 : as0_layout2 L := as0_layout2_of L C LY.
Hypothesis ILY : as0_icpt_layout IL.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Hypothesis ICok : aicpt_ok L ar IL SCFG HI.
#[using="SCFG_P L ar C LY HIok"] Lemma statics_vis : ltac2:(TCodec.tc2 tcn__asan_L5ADetailHR "QJ';'@'G%2211%411&R7%611&QL'TEyR0%211'>y8%511%311p051'Q=&R9vQ0r7r6r5r4r3r2&R;r1%211%;8:9876541&QJ&R4%1297%3219'C&R=+QU`P0+QV`P0%33;21&R@&S6+QW[WH+QoooPP0%443@21&R?+QW[X0+1%347D21%>251%?2;1tS:Q2A1p0F1pX2Q31pS0Q51p2QA1pWBQ?1pRFQA1pQFQB1pR:QE1").
Proof. intros LB FF LK cr A M model.
intros HH. pose proof (HAJ.aior_statics _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as ST. rewrite (aly_segs L C LY) in ST.
pose proof (statics_facts L C M LY ST) as (IMGC & CSB & CUAR & _).
pose proof (vis_pack L ar C HI LY HIok LB FF LK cr A M model HH) as (_ & _ & VIMG & _).
split. apply img_clear_mrestrict. exact IMGC.
split. apply (proj2 (u64_at_vis _ M _ _ (VIMG 1289464 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). exact CSB.
apply (proj2 (u32_at_vis _ M _ _ (VIMG 1289472 4 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). exact CUAR.
Qed.
#[using="C LY LY2 ILY"] Lemma ek_bytes : ltac2:(TCodec.tc2 tcn__asan_L5ADetailHR "R3';'@'G%2211%411&R7%611'TEyR0%211'>y8%511%311p051%?1=&S5vQ3vSFr8r7r6r5(=&R>%211r4r3%<9;:9876321&S3vQ1r9&S?&:r2%22Q11%411%8676B?:1&S=z%221>&S;%92Q8@%;11%32F1&S@+2+R0%3221%;251&R<&S6%241Q1ON%342Q2Q1Q0p021p061p0@1p0D1p0N1pXJQ<1pX<QJ1pS<Q?1pS0Q@1pXNQM1pY2QN1pQFQK1pR:QN1").
Proof. intros LB FF sp scr M Mk p s.
intros EK SRC P0 P1 B. eapply L5C.bytes_at_agree. 4: exact B. 2: exact P0. 2: exact P1.
intros i Hi. apply EK. split. lia. split. replace i with (p + (i - p)) by lia. apply (asrc_client L ar C IL LY LY2 ILY LB FF M sp scr p _ (i - p) SRC). lia. intros rr [].
Qed.
#[using="SCFG_P C LY HIok"] Lemma ek_src : ltac2:(TCodec.tc2 tcn__asan_L5ADetailHR "R5';'@'G%2211%411&R7%611&QL'TEyR0%211'>y8%511%311p051'Q=&R9vQ0r>r=r<r;r:r7&R;r6%211%;8:9876541&S5vQ3vSFr?r9(=&R>%211r8%99876C?521<&S3vQ1r@r4r3%5643<;21&S:rA%23Q<1G%33Q;2H%:69@<JIGp021p041p081p0?1p0J1pX0QE1pX<QF1pQHQC1pR<QF1pS<Q<1pX2Q<1pS0Q>1pXNQL1pY2QM1p2QL1pWBQJ1pRFQL1pQFQM1pR:R01").
Proof. intros LB FF LK cr A sp scr M model Mk LB' FF' p m.
intros HH EK SRC IL1 IF1. eapply asrc_keep. exact SRC. exact IL1. exact IF1.
intros so AO SZ j Hj. unfold byte_at. rewrite EK. apply SZ. exact Hj.
pose proof (aobj_facts L ar C HI LY HIok LB FF LK cr A M model so 24 sp scr HH AO ltac:(lia) ltac:(reflexivity)) as (OR & OBIG & _ & _ & _ & _ & OCLSH).
change (24 / 8) with 3 in OCLSH. split. unfold S, SB. lia. split. unfold S. apply OCLSH. exact Hj. intros rr [].
Qed.
Definition frk (sb : Z) (R : bvmap 5 word) (M : word -> option byte) : Prop :=
L5.u64_at RSEGS M (sb + 8) (U R 1) /\ L5.u64_at RSEGS M sb (U R 8) /\ L5.u64_at RSEGS M (sb - 8) (U R 9) /\ L5.u64_at RSEGS M (sb - 16) (U R 18) /\
L5.u64_at RSEGS M (sb - 24) (U R 19) /\ L5.u64_at RSEGS M (sb - 32) (U R 20) /\ L5.u64_at RSEGS M (sb - 40) (U R 21) /\ L5.u64_at RSEGS M (sb - 48) (U R 22) /\
L5.u64_at RSEGS M (sb - 56) (U R 23) /\ L5.u64_at RSEGS M (sb - 64) (U R 24) /\ L5.u64_at RSEGS M (sb - 72) (U R 25) /\ L5.u64_at RSEGS M (sb - 80) (U R 26) /\
L5.u64_at RSEGS M (sb - 88) (U R 27).
Definition spk (sb F negz : Z) (M : word -> option byte) : Prop :=
L5.u64_at RSEGS M (sb - 112) F /\ L5.u64_at RSEGS M (sb - 136) F /\ L5.u64_at RSEGS M (sb - 144) negz.
#[using="Type"] Lemma frk_agree : ltac2:(TCodec.tc2 tcn__asan_L5ADetailHR "QL'G&Q>y5'TEyR0%211%5241'>y8%611%311p061pY@72&RMr4r3r2%43321'C&S=&SAr6+RH%3221r1%6221&S>&S;+@%2281%4261%=261'D&TD%12NB%E11r5%113%63L31p081pW<Q81+U0%G21Er7%A21@&S@+2+R0%3221%N251r8%Q6318?p031p0;1p0>1p0Q61pS2Q<1pS0Q>1pS@QD1pXLQK1").
Proof. intros sb R M M'.
intros (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12 & C13) AG H0 H1. unfold frk.
repeat split; (eapply L5C.u64_at_agree; [ | | | eassumption]; [intros j Hj; apply AG; lia | lia | lia]).
Qed.
#[using="Type"] Lemma spk_agree : ltac2:(TCodec.tc2 tcn__asan_L5ADetailHR "QK'G'TEyR0%211'>y8%511%311p051pY@62&RNr5r4r3r2%544321'C&S=&SAr7+T@%3221r1%6221&S>+S8%8271%3251%<251'D&TD%12MA%D11%F12%53K21p071pW<Q41+U0%E21C&S;r8+@%3221&S@+2+R0%3221%N251r9%Q7419NQ6p031p0=1p0@1p0Q61pS2Q=1pS0Q?1pX6QH1pQDQI1pXLQJ1").
Proof. intros sb F negz M M'.
intros (C1 & C2 & C3) AG H0 H1. unfold spk.
repeat split; (eapply L5C.u64_at_agree; [ | | | eassumption]; [intros j Hj; apply AG; lia | lia | lia]).
Qed.
#[using="Type"] Lemma stack_callee : ltac2:(TCodec.tc2 tcn__asan_L5ADetailHR "R>';'@'G%2211%411&R7%611&R>%811'TEyR0%211'>y8%511%311p051&ROvQ3vSFr8r7r6r5r4r3r2%:9987654321&S9r1%23G18&S=&S;&9%13Q0Q08&A%13Q2Q2:%5231&SA&R6%11E+XPPP0%4221%<261p0>1pXFQ61z%@21F'C%B27I&S>&S@+2+Q?%3221%52O1%8271r:%K21Q3'D&TD%12QCQ7%Q911%Q;12%53QA21p071p0:1p0D1p0G1p0Q:1pW<R41pS2QG1pS0QH1pW:R11pVBR81pY6R91pQLR61pR@R91").
Proof. intros LBk FFk spc SCR W M M' a.
intros (E & _) HW H0 Ha Hs. apply E. split. lia. split. apply stack_client. exact Ha. lia.
intros rr Hr X. specialize (HW rr Hr). unfold L5.in_rng in X. lia.
Qed.
#[using="Type"] Lemma stack_rt : ltac2:(TCodec.tc2 tcn__asan_L5ADetailHR "QM';'@'G%2211%411&R7%611'TEyR0%211'>y8%511%311p051&R3vQ3vSFr7r6r5r4r3r2%9887654321&S=z%2214'C&SA&R6%11>+XPPP0%4221%921<&S>&S@+2+Q?%3221%52B1%=271r8%B21F'D&TD%12Q6J%L11%N12%53Q421p071p0:1p0I1p0M1pW<QD1pS2Q91pS0Q:1pXNQG1pY6QH1pQLQE1pR@QH1").
Proof. intros LBk FFk spc scr M M' a. intros (E & _) H0 Ha Hs. apply E. lia. apply stack_client. exact Ha. lia. Qed.
Section OWN.
Variables (sb F rs : Z) (R0 : bvmap 5 word) (negz : Z).
Hypothesis SBR : 140735332487488 <= sb <= 140737488355312.
Hypothesis SBC : ahl_ceil ar + 4096 <= sb - 160.
Hypothesis FRR : 4096 <= F /\ F + 256 <= 2 ^ 47 /\ (F / 8) * 8 = F.
Definition own (M : word -> option byte) : Prop := frk sb R0 M /\ spk sb F negz M /\ L5.defined M (F / 8 + SB) 32.
#[using="SBR"] Lemma own_agree : ltac2:(TCodec.tc2 tcn__asan_L5ADetailHR "R5'TEyR0%211'>y8%511%311p051pY@62&RLr2%211'G'C&S=&SAvT=+T@%3221r1%6221&S>&S;+@%2281%4261%=261'Dr4&TD%12MD%311r5%113%73L31p091pW<H1&S<vI+8%3221&R0%D221%M21H+Q0%G231%I2K1%Q2241&Er6%11D(4%11Q?%J3Q?31%611r3%K2QG1%811%O3QD16%;11p061p0>1pW<QB1%QF1Q3p021p0M1p0QG1pS2QK1pS0QM1").
Proof. intros M M'.
intros (K1 & K2 & K3) AG DF. split. apply (frk_agree sb R0 M M' K1). intros a Ha. apply AG. lia. lia. lia.
split. apply (spk_agree sb F negz M M' K2). intros a Ha. apply AG. lia. lia. lia.
intros i Hi. apply DF. lia. apply K3. exact Hi.
Qed.
#[using="SBR"] Lemma own_piece : ltac2:(TCodec.tc2 tcn__asan_L5ADetailHR "R4'TEyR0%211'>y8%511%311p051pY@62'G!p021&RLr3%211'C&S=zr1%3221&S>&S@+2+R0%3221%5271%;271&Er4r2%211%411'Dr6&TD%12Q2F%311r7%113%73Q131p091p0?1pW<Q11&RJr5%221A&SAvT=+T@%3221%Q221Q0&S;+@%2261%Q22Q41%Q8251%G1K%N11p031pW<QB1%Q@1Kp021p0A1p0E1p0QB1pW:QF1pS2QJ1pS0QL1").
Proof. intros M M' W. intros O FRM MG NW. apply (own_agree M M' O). intros a Ha. apply FRM. lia. apply NW. exact Ha. intros a _ X. apply MG. exact X. Qed.
#[using="SBR SBC FRR"] Lemma own_rt : ltac2:(TCodec.tc2 tcn__asan_L5ADetailHR "QE';'@'G%2211%411&R7%611'TEyR0%211'>y8%511%311p051&RLr2%211&R3vQ3vSFr7r6r5r4r3%887654321:&S9%K2IJ(?vI+2%34NN21vT;%54OQ021%8371>&S=&SAvT=+T@%3221%52D1%K1Cp021p091p0C1p0M1pS2Q11pS0Q21pXNQ?1pY6Q@1pQLQ=1pR@Q@1").
Proof. intros LBk FFk spc scr M M'.
intros O PRES INF Hs. apply (own_agree M M' O).
- intros a Ha. apply (stack_rt LBk FFk spc scr M M' a PRES). lia. lia. lia.
- intros a Ha X. rewrite (proj1 PRES a). exact X. unfold SB in Ha. lia.
apply (fframe_shadow_client L ar LBk FFk spc scr F 2 rs). exact INF. change (ff_bytes 2) with 256. unfold in_shadow_of, S. destruct FRR as (F0 & F1 & F8).
clear - Ha F8. unfold SB in *. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
#[using="SBR SBC FRR"] Lemma own_callee : ltac2:(TCodec.tc2 tcn__asan_L5ADetailHR "R9';'@'G%2211%411&R7%611&R>%811'TEyR0%211'>y8%511%311p051&RLr2%211&ROvQ3vSFr8r7r6r5r4r3%9987654321;&S9%N2LM(?vI+2%34Q1Q121vT;%54Q2Q321%8371?&S=&SAvT=+T@%3221%52E1r1%@3Q71G&S;&9%13Q?Q?O&A%13QAQAQ1%5231&R6%11Q0+XPPP0%@221%B251p0<1pXFQD1%Q;1Q3p021p0B1p0I1p0Q31p0Q>1pS2QB1pS0QC1pW:QL1pVBR31pY6R41pQLR11pR@R41").
Proof. intros LBk FFk spc SCR W M M'.
intros O AH INF Hs HW. apply (own_agree M M' O).
- intros a Ha. apply (stack_callee LBk FFk spc SCR W M M' a AH HW). lia. lia. lia.
- intros a Ha X. apply (proj2 (proj2 AH) a). unfold SB in Ha. lia. 2: exact X.
apply (fframe_shadow_client L ar LBk FFk spc SCR F 2 rs). exact INF. change (ff_bytes 2) with 256. unfold in_shadow_of, S. destruct FRR as (F0 & F1 & F8).
clear - Ha F8. unfold SB in *. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
#[using="SBR SBC FRR"] Lemma own_mem : ltac2:(TCodec.tc2 tcn__asan_L5ADetailHR "S8';'@'G%2211%411&R7%611!p061'TEyR0%211'>y8%511%311p051pY@62&RLr2%211'C&S=zr1%3221&S>&S@+2+R0%3221%5271%;271&R2vQ3vSFr:r9r8r7%77654321E&Er3%411%311'Dr6&TDr4%22Q71%411%<12%73Q521p091p0>1p0G1pW<QF1&S9%QI2QGQH(?vI%24QKQK1Q1vT;%44QLQM21%7361J&SAvT=+T@%3221%Q?2O1%Q01Q>&R6%11Q5+XPPP0%9221%QA2QH1&S;&S<+8%22C1&R0%5221%QL21QO+Q0%8231%QK2R21%R1241%Q>11%R32=1p0C1pW<RH1%R91Q=p021p0H1p0N1p0Q71p0R<1pS2R@1pS0RB1pQBRK1pXNS21pY6S31pQLS01pR@S31").
Proof. intros LBk FFk spc scr D M M'.
intros O PRES INF Hs HD. apply (own_agree M M' O).
- intros a Ha. apply PRES. lia. apply stack_client. lia. lia. intros X. apply HD in X. lia.
- intros a Ha X. rewrite PRES. exact X. unfold SB in Ha. lia. 2:{ intros Y. apply HD in Y. tauto. }
apply (fframe_shadow_client L ar LBk FFk spc scr F 2 rs). exact INF. change (ff_bytes 2) with 256. unfold in_shadow_of, S. destruct FRR as (F0 & F1 & F8).
clear - Ha F8. unfold SB in *. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
#[using="SBR"] Lemma own_vis : ltac2:(TCodec.tc2 tcn__asan_L5ADetailHR "Q8'TEyR0%211'7p021'>y8%711%311p071&RLr1%211&RCr3&SAvT=+U0%3221+U@%73621r4&S;&S<vI+8%3221&R0%6221+Q0%A3921&QJr5%221<%H11p051p0@1p0I1pS0M1pR0Q31").
Proof. intros H M.
intros O V1 V2. apply (own_agree M (mrestrict H M) O).
- intros a Ha. apply mrestrict_visible. replace a with ((sb - 160) + (a - (sb - 160))) by lia. apply V1. lia.
- intros a Ha X. rewrite mrestrict_visible. exact X. replace a with ((F / 8 + SB) + (a - (F / 8 + SB))) by lia. apply V2. lia.
Qed.
End OWN.
#[using="SCFG_P C LY HIok"] Lemma ek_obj : ltac2:(TCodec.tc2 tcn__asan_L5ADetailHR "RI';'@'G%2211%411&R7%611&QL'TEyR0%211'>y8%511%311p051'Q=&R9vQ0r;r:r9r8r7r4&R;r3%211%;8:9876541&S5vQ3vSFr<r6(=&R>%211r5%99876C?521<&S1+Q0%239?1'C&S=r1%2281&S>&S;%12;8%3251%8251'D&TDr2%22Q=1%Q011%Q312%63Q;21p081pW<QI1z%B21A+4%A2C1%F231&QO%11Q1%D21>%@2QK1%Q>11%QA12%D3QI21p081pWLR71%Q02?1p0Q21p0Q61p0QA1pX:R<1pS<R01pX2R01pS0R21pXNR@1pY2RA1p2R@1pWBR>1pRFR@1pQFRA1pR:RD1").
Proof. intros LB FF LK cr A sp scr M model Mk o.
intros HH EK AO.
pose proof (aobj_facts L ar C HI LY HIok LB FF LK cr A M model o 32 sp scr HH AO ltac:(lia) ltac:(reflexivity)) as (OR & OBIG & _ & _ & _ & OCL & OCLSH).
change (32 / 8) with 4 in OCLSH. split.
- intros a Ha. apply EK. split. lia. split. replace a with (o + (a - o)) by lia. apply OCL. lia. intros rr [].
- intros j Hj. apply EK. split. unfold S, SB. lia. split. unfold S. apply OCLSH. exact Hj. intros rr [].
Qed.
#[using="L ar C LY HIok"] Lemma apure : ltac2:(TCodec.tc2 tcn__asan_L5ADetailHR "S9';'@'G%2211%411&R7%611&QL'TEyR0%211'>y8%511%311p051'Q='RD&Q>y5%221:&RH&R9vQ0r>r=r<r;r:r9&R;r8%211%;8:9876541&S0%1286'QK&S6&RFr7&TDr6%22Q11&QJ&R4%12CA%321C&RG%11;%;5D:731r5r4%<2Q;1%?5F3175%B3A51rBrAr@r?r1%N11%Q78Q66543Q5Q41r2%M251&R8r3%22Q:1'D'7p0QK1%J2>C%K2?=%53321'RI&RBvS7%211&S4%15QFQCQBFL%64Q:31QBp081p0?1p0C1p0F1pX4R41%85QJQHQFQLQK%=4QA:1Q4p031p0Q21p0QF1p0QI1pR6R61pX@RJ1pSDR91pX>RL1pSBR;1pWJR?1pWHR@1pX2RB1pS0RD1p2S01pWBRN1pRFS01pQFS11pR:S41").
Proof. intros LB FF LK cr A M model fx fx1 Ra pc Rb pc1 K.
intros HH AM MS KONT.
apply (apiece_ro L ar C HI LY HIok LB FF LK cr A M model fx fx1 Ra pc Rb pc1 (mrestrict (ahid A model) M) K HH AM MS (mem_grows_refl _) (fun a _ => eq_refl)).
intros M1 model1 HH1 AM1 RT1 AH1 VIS1 MGM1 FRM1.
assert (E : M1 = M) by (apply mem_eq_of_agree; exact FRM1). subst M1. apply KONT; assumption.
Qed.
#[using="SCFG_P C HIok"] Lemma astk_after2 : ltac2:(TCodec.tc2 tcn__asan_L5ADetailHR "R=';'@'G%2211%411&R7%611&QL'TEyR0%211'>y8%511%311p051&R:&R>%B11&R9vQ0rAr@r?r>r=r<r;%9887654321&S2vSFr9r6r5%544321&RJr:%2216&ROvQ3r4%392;@?9815:&S=&SAr8%22>1r7%421?%6231%725=z%921?%G4FKJIp021p051p071p0?1p0D1p0H1p0O1pW:Q:1pY0QK1pY4QL1pXNQM1pY2QN1pS8QB1pS6QC1pS0QD1pQLQN1pR@R11pW6QF1pS4QH1p4R41pWDR21pRHR41pQJR51pR>R81").
Proof. intros LB0 FF0 LK0 cr0 A0 M0 V0 LBk FFk M M1 M2 sp scr sp' scr' W.
intros HH (A16 & SLO & SHI & SPT & DSCR & DUP) MG (PRES & SDEF & DK) H1 H2 H0.
assert (D : forall x, (sp - scr <= x < sp \/ sp <= x < ar_stack_top ar) -> M2 (Z_to_bv 64 x) <> None).
{ intros x Hx2. destruct (rng_dec x (sp' - scr') sp') as [I|O].
- replace x with (sp' - scr' + (x - (sp' - scr'))) by lia. apply SDEF. lia.
- pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & TOP & _).
apply DK. lia. apply stack_client. lia. exact O. apply MG. destruct (Z_lt_le_dec x sp).
+ replace x with (sp - scr + (x - (sp - scr))) by lia. apply DSCR. lia.
+ replace x with (sp + (x - sp)) by lia. apply DUP. lia. }
split. exact A16. split. lia. split. lia. split. exact SPT. split.
- intros j Hj. apply D. lia.
- intros j Hj. apply D. lia.
Qed.
#[using="Type"] Lemma lb_remove_head : ltac2:(TCodec.tc2 tcn__asan_L5ADetailHR "C'G';'@%1233%311'D&QMr3(8(?r2%24;;41r1%53:21%8271%:3;13pRB<1pX8A1pXBB1").
Proof. intros q nq LBx. cbn. rewrite Z.eqb_refl. reflexivity. Qed.
#[using="Type"] Lemma lb_remove_skip : ltac2:(TCodec.tc2 tcn__asan_L5ADetailHR "K'G';'@%1233%311&E'Dr3r4%33921%511&QMr5(8(?%14??78r2%43>21%7261%8273%73A51%?3A31p0<1pRBC1pX0H1pXDI1pXBJ1").
Proof. intros q q' m LBx. intros NE. cbn. destruct (Z.eqb_spec q' q). contradiction. reflexivity. Qed.
#[using="Type"] Lemma not_client_bx : ltac2:(TCodec.tc2 tcn__asan_L5ADetailHR "R5';&R7%211'G'@%1222%611&S9r1r3%33521'C&R1vQ3vSF&9r2%23>>1&A%13@@3%847631'F&S=&S;%1275&R5%11<%5231&QN%6231%821=%:241%E2<1p0G1pW@M1r4%>2:1&S>%1239%L231+QoonlP0+`PPPPPTP0%C221r5%F221+1%G231%I217%K241&E&R2r7zr6%47Q9Q8C3221%611&6%13QD4>r8%97Q>Q=21778%;11p061p0>1p0H1p0N1pRBQK1p8QL1pW<R01pQNR21").
Proof. intros FFx a.
induction BX as [|b BX IH]; intros LBx HB HA HBIG NC. exact NC.
cbn [app]. intros X. destruct (aclient_consb_inv L ar (BX ++ LBx) FFx b 0 0 a X) as [Y|[Y|Y]].
- revert Y. apply IH. intros b' Hb'. apply HB. right; exact Hb'. exact HA. exact HBIG. exact NC.
- destruct (HB b (or_introl eq_refl)) as (_ & Z0). clear - Y Z0 HA. lia.
- destruct (HB b (or_introl eq_refl)) as ((B0 & _ & _ & B3 & _ & (_ & _ & B6)) & _). unfold in_shadow_of, S, SB in Y.
assert (E1 : 0 <= fst b / 8) by (apply Z.div_pos; clear - B0; lia).
assert (E2 : (fst b + snd b - 1) / 8 <= (2 ^ 47 - 1) / 8) by (apply Z.div_le_mono; clear - B6; lia).
change ((2 ^ 47 - 1) / 8) with 17592186044415 in E2. clear - Y E1 E2 HBIG. lia.
Qed.
#[using="SCFG_P C HIok"] Lemma blocks_off_fs : ltac2:(TCodec.tc2 tcn__asan_L5ADetailHR "R6';'@'G%2211%411&R7%611&QL'TEyR0%211'>y8%511%311p051&R:&R9vQ0r9r8r7r6r5r4r3%9887654321'Dr:&6r2%23L61%53L41&S9r1%23Q01<'C&R1vQ3vSF&9%13Q7Q7;&A%13Q9Q9=%746531'F&S=&S;%1275&R5%11;%5231&QN%6231%821=%:241%D2<1p0F1pW@QG1p0K1p0Q21pRDQI1p8QJ1pW8Q?1pS>QA1p6QM1pWFQK1pRJQM1pQNQN1pRBR11").
Proof. intros LBx FFx LKx crx Ax Mx Vx BX LBy.
intros HH E b Hb. pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & _).
destruct (WB b ltac:(rewrite E; apply in_or_app; left; exact Hb)) as (BR & _ & _ & _ & _ & _ & BFS). split. exact BR. exact BFS.
Qed.
End WithIface.
End SCFG_1.
End L5ADHR.
