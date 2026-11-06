(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import AsanAcct.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import
PropExec CatExec CatSim SeqExec StoreOk ShapeAlg SpinAlg Hoare AsanAcctShape SymExec2 SymExec2Sound SymRun SymDrive SymDriveX
HeapIface HeapIfaceA IcptIfaceA DrvKitA DrvNodesLazyK As0DrvKitA Ja0DrvEntry Ja0Drv_defs Ja0DrvLib Ja0DrvRead.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Import SX2. Import SX2S.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__Ja0DrvStdio () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.LinuxProcessSem.State."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanAcct."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.DrvKitA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIfaceA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.IcptIfaceA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ja0DrvLib."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ja0DrvStdio."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2.SX2."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2Sound.SX2S."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymRun."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0A"; "1None"; "1O"; "1Some"; "1bool"; "1false"; "1fst"; "1list"; "1nat"; "1option"; "1pair"; "1prod"; "1snd"; "1true"; "2and"; "2eq"]; ["2not"; "2or"; "3Forall"; "4Z"; "0E"; "0HI"; "0IL"; "0LB"; "0LK"; "5store_ok"; "5word_to_le_bytes"; "6Model"; "0M"; "0M'"; "0M0"; "0MV"]; ["7mrestrict"; "8kentry_eqb"; "9credit"; ":ahid"; ":ar_sptop"; ":fframe"; ":shadow_allowed"; ";icl_poison"; "<dinv"; "<has_window"; "=PR_CELLS"; ">rdn"; "?ELit"; "?Env"; "?KImg"; "?KWord"]; ["?SA"; "?edenot"; "?env"; "?expr"; "?kentry"; "@know_ok"; "Avals_ev"; "Bloaded_segments"; "CIn"; "Cexistsb"; "Dadd"; "Ddiv"; "Dle"; "Dlt"; "Dof_nat"; "Dpow"]; ["Dsub"; "Dto_nat"; "0a"; "0ar"; "0bs"; "0cr"; "0d"; "0ebs"; "0hi"; "0i"; "0k"; "0kn"; "0lo"; "0model"; "0n"; "0r"]; ["0sp0"; "EZ_to_bv"; "Ebv"; "Ebv_unsigned"; "0v"; "0vals"; "0w"; "0x"]]).
Definition PR_CELLS : list (Z * Z * Z) :=
[(0x13b9d8, 1, 1); (0x13b9d9, 1, 1); (0x1cc87c, 1, 1); (0x13acf8, 8, 0x7fff8000);
(0x1344c0, 8, 0x1224a8); (0x1344c8, 8, 0x11c1c4); (0x134640, 8, 0x1249ac); (0x134648, 8, 0x124db0)].
Definition EX_CELLS : list (Z * Z * Z) :=
[(1262664, 8, 1262664); (1263176, 8, 1199536); (1275456, 8, 1); (1275536, 1, 0); (1279248, 4, 1); (1279408, 8, 0); (1287516, 1, 1); (1289464, 8, 2147450880); (1292760, 1, 1); (1886368, 8, 18446744073709551615); (1887136, 1, 0); (1279252, 1, 0)].
Definition DG_CELLS : list (Z * Z * Z) := [(1292760, 1, 1); (1292761, 1, 1); (1886332, 1, 1); (1289464, 8, 2147450880); (1262792, 8, 1163716); (1263168, 8, 1198508)].
Definition DGS_CELLS : list (Z * Z * Z) :=
[(1263088, 8, 1201360); (1262720, 8, 1198256); (0x13acf8, 8, 0x7fff8000); (0x13b9e8, 8, 0); (0x13b9f0, 8, 0); (0x13b9e0, 8, 2 ^ 47 - 1); (0x1cc923, 1, 1); (0x13b9d9, 1, 1); (0x134640, 8, 0x1249ac)].
Lemma rdn_tr : ltac2:(TCodec.tc2 tcn__Ja0DrvStdio "R6'RByR0%211'9y8%511%311p051'C'8'7%116'?%:12&Q;&QGr5&RAr3%22B1r2%746521(3r1%22=1%=3<41&QLzr4%3221&QJ&QN%114%32A1&QO+2+R0%3221%<251'>r7%?21B&QMr6%=11%?251%42G1%8261r9%Q02Q@M%211r:%113%Q93Q?31p071pTDQ?1r8%Q82QHA%Q<4Q;21?%Q52Q@Q;%Q@3Q?21p061p0H1p0Q21p0Q71pT:QF1pTNQI1pT6QK1pQLQM1pQJQN1").
Proof.
intros M M' a n bs H Ha Hn HF. rewrite <- H. apply rdn_agree. intros j Hj. rewrite u_small by lia. apply HF. lia.
Qed.
Lemma img_cell : ltac2:(TCodec.tc2 tcn__Ja0DrvStdio "R6'RByR0%211'9y8%511%311p051'C'8'7%116'?%:12&Q;&QG(1%11<q0@1&RAr3%22D1r2%948521(3r1%22?1%?3>41&QLzr4%3221&QJr5&QN%115%4231&QO+2+R0%3221%=251'>r7%@21C&QMr6%=11%@251%42H1%8261r9%Q12QCN%211%Q:3Q@1Q5p051pTDQ@1r8%Q72QI?%Q=4Q<21=%Q42QAK%QA3Q@21p061p0F1p0Q11p0Q61pT:QG1pTNQJ1pT6QL1pR0QN1").
Proof. intros MV a n bs H Ha Hn HN. exact (rdn_tr (fun _ => None) MV a n bs H Ha Hn HN). Qed.
Section FPX_1. Context {fx : PropExec.FPState}.
Variable scfg : SpuriousCfg.
Section Stdio.
Variable L : asan_layout.
Variable ar : asan_run.
Variable C : asan_statics_cells.
Variable IL : icpt_layout.
Variable HI : asan_iface.
Hypothesis HIok : asan_iface_ok L ar C scfg HI.
Hypothesis ICok : aicpt_ok L ar IL scfg HI.
Hypothesis ILY : as0_icpt_layout IL.
Variable sp0 : word.
Hypothesis Hsp : 0x7fff80000000 <= bv_unsigned sp0 <= 2 ^ 47.
Hypothesis Hal : bv_unsigned sp0 mod 16 = 0.
Hypothesis DL : drv_layoutA L ar IL sp0.
Hypothesis Hpr : incl PR_CELLS (asc_cells C).
Variable M0 : word -> option byte.
#[local] Notation dinvA := (dinv ar HI sp0 M0).
#[local] Notation usp := (bv_unsigned sp0).
Lemma vis_low : ltac2:(TCodec.tc2 tcn__Ja0DrvStdio "QF'7';'C%2211%411&Q5%611&Q2'RByR0%211'9y8%511%311p051'K'Q8vR3vEvR@vNr7r6r5r4r3r2%;::987654321'>&QLz%2215&QM+VbTP0%2281%7241'?'4&Q3&RA%12Q0?%33CA1(5%73621p091p0B1pT6Q=1pTLQ01pQJQ21p2Q>1pT<Q<1pQBQ>1pQ@QA1").
Proof. intros LB LK cr A M model a D Ha. apply (vis_of_inv scfg L ar C IL HI HIok sp0 DL _ _ _ _ _ _ _ a (di_inv _ _ _ _ _ _ _ _ _ _ D)); lia. Qed.
Lemma vis_stk : ltac2:(TCodec.tc2 tcn__Ja0DrvStdio "QM'7';'C%2211%411&Q5%611&Q2'RByR0%211'9y8%511%311p051'K'Q8vR3vEvR@vNr7r6r5r4r3r2%;::987654321'>&QL&R0&RC%12H=+XPPP0%4221%6219&QM&QO+2+R0%3221%52?1%>271'?'4&Q3&RA%12Q7F%33JH1(5%73621p091p0I1pT6QD1pTLQ71pQJQ91p2QE1pT<QC1pQBQE1pQ@QH1").
Proof. intros LB LK cr A M model a D Ha. pose proof Hsp. apply (vis_of_inv scfg L ar C IL HI HIok sp0 DL _ _ _ _ _ _ _ a (di_inv _ _ _ _ _ _ _ _ _ _ D)); lia. Qed.
Section SE.
Local Abbreviation SEC_T_pr_cell_vis := (ltac2:(TCodec.tc2 tcn__Ja0DrvStdio "R5'7';'C%2211%411&Q5%611&Q2'RByR0%211'9y8%511%311p051'K'Q8vR3vEvR@vNr9r8r7r6r5r4%;::987654321&QH%M2KL(:r3%24OO61r2%44Q0Q121&Q:%83721'?%Q71J%M11&Q;&QG&Q0&Q3%12FD%321F&RA%12Q7F&R1%11G%:49531(3&J%72Q=F%2251%42A1%C3A61p0E1p0O1pU:QJ1pTNQK1pT6QL1pTLQ?1pQJQA1p2QM1pT<QK1pQBQM1pQ@R01")) (only parsing).
Variable LB : ltac:(sec_ty2 constr:(SEC_T_pr_cell_vis) 0%nat 0%nat).
Variable LK : ltac:(sec_ty2 constr:(SEC_T_pr_cell_vis) 1%nat 0%nat).
Variable cr : ltac:(sec_ty2 constr:(SEC_T_pr_cell_vis) 2%nat 0%nat).
Variable A : ltac:(sec_ty2 constr:(SEC_T_pr_cell_vis) 3%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_pr_cell_vis) 4%nat 0%nat).
Variable model : ltac:(sec_ty2 constr:(SEC_T_pr_cell_vis) 5%nat 0%nat).
Variable a : ltac:(sec_ty2 constr:(SEC_T_pr_cell_vis) 6%nat 0%nat).
Variable n : ltac:(sec_ty2 constr:(SEC_T_pr_cell_vis) 7%nat 0%nat).
Variable v : ltac:(sec_ty2 constr:(SEC_T_pr_cell_vis) 8%nat 0%nat).
Lemma pr_cell_vis : ltac:(sec_stmt2 constr:(SEC_T_pr_cell_vis) 9%nat 0%nat).
Proof.
intros D Hin.
pose proof (di_inv _ _ _ _ _ _ _ _ _ _ D) as HH.
destruct (aio_statics _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (_ & CS). rewrite (dla_segs _ _ _ _ DL) in CS.
pose proof (proj1 (Forall_forall _ _) CS (a, n, v) (Hpr _ Hin)) as X. unfold cell_is in X. cbn [fst snd] in X.
rewrite rdn_mrestrict_eq; [exact X|].
intros k Hk. unfold woff.
assert (B : 0 <= a /\ a + Z.of_nat (Z.to_nat n) <= 0x691000).
{ unfold PR_CELLS in Hin. cbn [In] in Hin. repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <- <-; cbn; lia|]). destruct Hin. }
rewrite (u_small a) by lia. apply (vis_low _ _ _ _ _ _ _ D). lia.
Qed.
End SE.
Lemma stk_wr : ltac2:(TCodec.tc2 tcn__Ja0DrvStdio "R?'7'RByR0%211%411'8y8%611%811p041'9%114p091'QD%>11'C&QE&QG(Q=&QFr6%211r5%5221r4r3%:49321'?'4&Q9%116(=%53421r8(2%@221vR@%:3Q221&QL&R0&RC%12Q75+XPPP0%4221%621F&QJ%12JH%9216zr2%<221&QN%113%82L1r9%A221&Ir=&RAr;%?21Q4%32QK1%64Q=51Q5%Q43Q31Q0p091p0?1pTFQM1pT>QD1p0E1p0I1p0Q11p0Q71p0Q>1pTNQJ1pT6QK1pTHQM1pR0R01pT@R41pU<R:1").
Proof.
intros vals ebs MV kn a n HK Hw P0 Ha Hn d k Hd Hk.
pose proof (window_store_ok sp0 vals ebs MV kn (a + d - usp) k HK Hw P0 ltac:(lia) ltac:(lia)) as W.
replace (usp + (a + d - usp)) with (a + d) in W by ring. exact W.
Qed.
Lemma stk_def : ltac2:(TCodec.tc2 tcn__Ja0DrvStdio "RA'7'RByR0%211%411'8y8%611%811p041'9%114p091'QD%>11'C&QE&QG(Q=&QFr6%211r5%5221r4r3%:49321'?'4&Q9%116(=%53421r8(2%@221vR@%:3Q221&QL&R0&RC%12Q75+XPPP0%4221%621F&QJ%12JH%9216'>zr1%=221&QMr7%2241%7241&@r;&RAr9r2%@221%42QL1%611(1%11QJ%Q73QG31%;11p0=1pTDQF1p0G1p0K1p0Q31p0Q91p0Q@1pTNQL1pT6QM1pTHQO1pR0R21pT@R61pU<R<1").
Proof.
intros vals ebs MV kn a n HK Hw P0 Ha Hn i Hi. pose proof Hsp.
pose proof (stk_wr vals ebs MV kn a n HK Hw P0 Ha Hn i 1%nat ltac:(lia) ltac:(lia)) as W.
apply (store_ok_defined sp0); [lia | exact W].
Qed.
Lemma stk_sh0 : ltac2:(TCodec.tc2 tcn__Ja0DrvStdio "R6'7';'C%2211%411&Q5%611&Q2'RByR0%211'9y8%511%311p051'K'Q8vR3vEvR@vNr7r6r5r4r3r2%;::987654321'>&QL&QJ&QK&R0&RC%12J?+XPPP0%4221+8%7221+QoooPP0%:221%<21?+1%;291%=217%?216%A2D1%C261'?&Q0&Q3%12MK&RA%12Q=L%533O1(3z%52Q>1%32Q>1%;3Q>51p0=1p0Q21pU@QM1pTLQ@1pQJQB1p2QN1pT<QL1pQBQN1pQ@R11").
Proof.
intros LB LK cr A M model x D Hx. pose proof Hsp as Hsp'. pose proof (di_inv _ _ _ _ _ _ _ _ _ _ D) as HH.
pose proof (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (_ & _ & _ & _ & _ & _ & STSH & _).
assert (CE : ahl_ceil ar = usp - 8388608) by (unfold ahl_ceil; rewrite (dla_sptop _ _ _ _ DL); reflexivity).
assert (IS : in_shadow_of (ahl_ceil ar) (ar_sptop ar - ahl_ceil ar) x).
{ unfold in_shadow_of, S, SB. rewrite CE, (dla_sptop _ _ _ _ DL). replace (usp - 8388608 + (usp - (usp - 8388608)) - 1) with (usp - 1) by ring. exact Hx. }
unfold mrestrict. rewrite (vis_of_allowed _ _ _ _ _ STSH IS).
apply (di_stksh _ _ _ _ _ _ _ _ _ _ D). unfold in_shadow_of, S, SB, STKTOP. rewrite CE, (dla_sptop _ _ _ _ DL).
assert (MX : usp <= Z.max usp (ar_stack_top ar)) by lia.
split; [lia|]. assert ((usp - 1) / 8 <= (usp - 8388608 + (Z.max usp (ar_stack_top ar) - (usp - 8388608)) - 1) / 8) by (apply Z.div_le_mono; lia). lia.
Qed.
Lemma hi_sh0 : ltac2:(TCodec.tc2 tcn__Ja0DrvStdio "RA'7';'C%2211%411&Q5%611&Q2'RByR0%211'9y8%511%311p051'K'Q8vR3vEvR@vNr7r6r5r4r3r2%;::987654321&Q6&R0&Q4%11>+XPPP0%4221&QO+2+Q?%3221%9215%;3@61'>&QL&QJ&QK&RC%12Q5J%A21>+8%5221+QoooPP0%8221%:21J+1%H2@1%;217%=216%?2O1%A261'?&Q0&Q3%12Q8Q6&RA%12QGQ7%533Q:1(3z%52QH1%32QH1%;3QH51p0=1p0Q01p0Q=1pU@R81pTLQK1pQJQM1p2R91pT<R71pQBR91pQ@R<1").
Proof.
intros LB LK cr A M model x D SAH Hx. pose proof Hsp as Hsp'.
assert (CE : ahl_ceil ar = usp - 8388608) by (unfold ahl_ceil; rewrite (dla_sptop _ _ _ _ DL); reflexivity).
assert (IS : in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) x).
{ unfold in_shadow_of, S, SB. rewrite CE. replace (usp - 8388608 + (2 ^ 47 - (usp - 8388608)) - 1) with (2 ^ 47 - 1) by ring. lia. }
unfold mrestrict. rewrite (vis_of_allowed _ _ _ _ _ SAH IS). exact (di_hish _ _ _ _ _ _ _ _ _ _ D x IS).
Qed.
Lemma img_sh0 : ltac2:(TCodec.tc2 tcn__Ja0DrvStdio "S2'7';'C%2211%411&Q5%611&Q2'RByR0%211'9y8%511%311p051'K'Q8vR3vEvR@vNr9r8r7r6r5r4%;::987654321&QL+RPP0%2214&QJ%1276+VbTP0%6221&QMz%221<'B'A%92BA&6r1%23Q:Q:1%@241&<%13Q=Q=4%C21I%9241qU0Q?1&Q7vF%211%?3QC41'>&QK+8%22Q31+QoooPP0%L221%Q021Q4&R0+1%22G1%9218%Q2217%Q62Q:1%=271'?&Q0&Q3r<r:%3221r;&RA%12R4QE%83431(3%42R4Q;%22R41%=3R441p0?1p0N1p0Q?1p0QC1p0QH1p0QL1pU@RG1pTNRH1pT6RI1pTLR<1pQJR>1p2RJ1pT<RH1pQBRJ1pQ@RM1").
Proof.
intros LB LK cr A M model a n x D Ha Hn Hp HP Hx. pose proof (di_inv _ _ _ _ _ _ _ _ _ _ D) as HH.
destruct (aic_img_shadow _ _ _ _ _ ICok _ _ _ _ _ _ _ HH a n) as (Z0 & SA);
[rewrite (dla_img_lo _ _ _ _ DL); lia | rewrite (dla_img_hi _ _ _ _ DL); lia | exact Hp | exact HP |].
assert (IS : in_shadow_of a n x) by (unfold in_shadow_of, S, SB; exact Hx).
unfold mrestrict. rewrite (vis_of_allowed _ _ _ _ _ SA IS). exact (Z0 x IS).
Qed.
Lemma kimg_clear : ltac2:(TCodec.tc2 tcn__Ja0DrvStdio "QE'QB'RByR0%211'9y8%511%311p051'7'QD%211'C&QE&QGr5r4r3%544321'?'4&QI&Q1(Q>r2%2281%411%63A1;(=%:3921'>&QLr1%22B1&QM%123C%6231r8&RA%12Q5?%311(1%11Q4%H3Q431p081pTDQ11p0A1p0M1pTBQ41pTJQ51pTHQ71pR0Q;1pQ:QD1").
Proof.
intros E MV kn lo hi HK Hb. apply existsb_exists in Hb as (K & Hin & Heq). apply kentry_eqb_eq in Heq. subst K.
pose proof (proj1 (Forall_forall _ _) HK _ Hin) as X. cbn [kentry_ok] in X. exact (proj2 (proj2 X)).
Qed.
Lemma kword_lit : ltac2:(TCodec.tc2 tcn__Ja0DrvStdio "R;'QB'RByR0%211'9y8%511%311p051'7'QD%211'C'8'QC&QE&QGr6r5r4%544321'?'4&QI&Q1(Q?(Q@(Q<z%211%421;r3r2%83321%:11%<3I1A(=%@3?21&QL%12;E&QJ&QN%11H%32J1&QO+2+QO%3221%:251%Q81Q;%Q>11&Q;r9&RAr7%22QE1%54Q841Q7(3&J&QAr:%221Q;%42Q=1%62>1%Q;3>81p0A1p0K1p0N1p0Q@1pU:QG1pU>QI1pT6QK1pTHQM1pR0R11pQ:R:1").
Proof.
intros E MV kn a w v HK Hb Ha Hw. apply existsb_exists in Hb as (K & Hin & Heq). apply kentry_eqb_eq in Heq. subst K.
pose proof (proj1 (Forall_forall _ _) HK _ Hin) as X. cbn [kentry_ok] in X. destruct X as (_ & _ & X).
unfold adenot, v_addi in X. cbn [a_base a_off edenot] in X. rewrite (u_small 0) in X by lia. rewrite Z.add_0_l in X. exact X.
Qed.
End Stdio.
End FPX_1.
