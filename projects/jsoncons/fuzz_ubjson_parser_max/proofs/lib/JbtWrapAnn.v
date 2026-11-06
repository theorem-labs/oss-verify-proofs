(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatSim StoreOk ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA ArtMem ArtRuns ArtRunsMem JbtCls JbtCellEx JbtDepot ArtBridge JbtInv JbtInvMalloc JbtLift JbtWrapKit
JbtFsInv JbtFsInvLaws JbtIfaceLaws JbtWrapC JbtWrapVis JbtWrapC2 HeapIfaceAJx ShadowRLaws JbtInvFrameS JbtWrapFreeA JbtAnnotate JbtPoison JbtWrapRng JbtAllocG RefMemcpyLib.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLiaT. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__JbtWrapAnn () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.Run."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ArtBridge."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ArtMem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanAcct."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIfaceA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIfaceAJx.HAJ."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Hoare."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtFsInv."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtFsInvLaws."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtInv."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ShapeAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.StoreOk."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.base."; "stdpp.bitvector.definitions."], [["0A"; "0A'"; "0BASE"; "0BUDGET"; "1None"; "1Some"; "1bool"; "1false"; "1fst"; "1list"; "1nil"; "1option"; "1pair"; "1prod"; "1snd"; "2I"]; ["2and"; "2eq"; "2ex"; "2not"; "2or"; "3map"; "4Z"; "0FF"; "0FP"; "0G"; "0K"; "0L"; "0LB"; "0LK"; "5mkCfg"; "6Model"]; ["6event"; "6m_halted"; "6m_vm_lazy"; "7bvmap"; "0M"; "0M'"; "0M1"; "0MAPS0"; "0Mn"; "0Mo"; "0Mr'"; "0NOACC0"; "0Q"; "0R"; "0R'"; "0RESV0"]; ["8BInv"; "8bhid"; "9cell"; ":MInv"; ":mrestrict"; ";msteps"; "<credit"; "<in_block"; "<regs_preserved"; "=S"; "=aclient"; "=astack_ok"; "=fframe"; "=in_fframe"; "=in_shadow_of"; "=model_rt"]; ["=vml_of"; ">ann_shadow"; ">shadow_blkR"; "?ret_ok"; "@art_fsg"; "@art_fsinv"; "@cs_zone"; "Afs_zone3"; "Bart_alloc_rep"; "Bart_alloc_zone"; "Bart_client_ok"; "Bart_credit_ok"; "Bart_eager_ok"; "Bart_gs"; "Bart_kn_ok"; "Bart_lazy_ok"]; ["Bart_ri_inv"; "Bart_run"; "Bg_fs"; "Bg_log"; "Brn_HI"; "Brn_ar"; "Brn_loff"; "Brn_tp"; "Cgetr"; "Cmkst"; "Cseg_rom"; "DTSet"; "Esrealizes"; "Fmem_grows"; "Gloaded_segments"; "HIn"]; ["Hincl"; "Iadd"; "Idiv"; "Ile"; "Ilt"; "Imodulo"; "Ipow"; "Isub"; "0a"; "0b"; "0b'"; "0b0"; "0c"; "0c0"; "0cr"; "0fx"]; ["0j"; "0model"; "0model'"; "0pc0"; "0pc1"; "0rn"; "0scfg"; "0sp"; "JNoDup"; "KBV"; "KZ_to_bv"; "Kbv"; "Kbv_unsigned"; "0u"; "0u'"; "0x"]]).
Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.
#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).
Lemma art_ann_lb_uniq : ltac2:(TCodec.tc2 tcn__JbtWrapAnn "N'9'='F%2211%411'SH&E&8%1266r3%447821%6291&ROr4%23;51r5%43=71'A%;3@@3%<3AA6%33B21r6%53C17p031p081p0;1p0?1pVFH1pVDI1pQJI1").
Proof.
induction LB as [|x LB IH]; intros b b' ND Hb Hb' E; [destruct Hb|]. cbn [map] in ND. inversion ND as [|? ? NI ND']; subst.
destruct Hb as [<-|Hb]; destruct Hb' as [<-|Hb']; [reflexivity| | |exact (IH b b' ND' Hb Hb' E)].
- exfalso. apply NI. apply list_elem_of_In. rewrite E. apply in_map. exact Hb'.
- exfalso. apply NI. apply list_elem_of_In. rewrite <- E. apply in_map. exact Hb.
Qed.
#[using="Type"] Lemma art_client_ok_frame_sh : ltac2:(TCodec.tc2 tcn__JbtWrapAnn "R<'RA'9'='F%2211%411&QL%611'SKyR0%211';y8%511%311p051&R:r9r8r7r6r5r4%76654321&RM%1243&RO(<r3%24JJ71r:%53K21r2r=%83N21&C'A&8%13Q3Q3:%33Q41E%511&QN%53Q7Q7D&>%13Q9Q9F%4331Ar;&SJ%12Q7J%311r<%113%@3Q631p081p0>1p0E1pVBQE1pVDQE1&R2%13Q8Q7Q6r>%Q=61L;?OQ;p031p061p0Q11p0Q81p0Q;1pVLR01pVHR11pR>QF1pR:QG1p2R21pQLR11pQ@R21pQJR51pW<R;1").
Proof.
intros rn LB FF LK A M M1 b0 c0 (C1 & CR) GR HB0 AG SB. split; [|exact CR].
intros b Hb. destruct (C1 b Hb) as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9).
split; [exact K1|]. split; [exact K2|]. split; [exact K3|]. split; [exact K4|]. split; [exact K5|]. split; [exact K6|].
split. { intros i Hi. apply GR. exact (K7 i Hi). }
split; [|exact K9].
destruct (Z.eq_dec (fst b) b0) as [E|N].
- pose proof CR as (ND & _). rewrite (art_ann_lb_uniq LB b (b0, c0) ND Hb HB0 E). exact SB.
- apply (shadow_blkR_frame M M1 (fst b) (snd b)); [lia | | lia | intros a Ha; exact (AG b a Hb N Ha) | exact K8].
pose proof (Z.div_mod (fst b) 16 ltac:(lia)) as D. rewrite K3, Z.add_0_r in D. rewrite D. replace (16 * (fst b / 16)) with ((2 * (fst b / 16)) * 8) by ring. apply Z_mod_mult.
Qed.
Section WrapS.
Variables MAPS0 RESV0 NOACC0 : list (word * word).
Variables BASE BUDGET : Z.
Variable rn : art_run.
Variable scfg : SpuriousCfg.
Hypothesis Hwx : wx_segs_nowrap ASEGS.
Context {fx : PropExec.FPState}.
#[local] Abbreviation RI := (art_ri_inv art_fsg MAPS0 RESV0 NOACC0 BASE BUDGET art_fsinv rn).
#[local] Abbreviation BI := (BInv ASEGS MAPS0 RESV0 NOACC0 (rn_HI rn) BASE BUDGET).
#[using="Hwx"] Theorem art_wrap_pure2sh : ltac2:(TCodec.tc2 tcn__JbtWrapAnn "XM&RK&Q3y5'SKyR0%211%5241';y8%611%311p061'O'R='R4%211'9'='F%2211%411&QL%611&QF!p071p0?2p0F1p0F1&R8vSEr:r9&QD&QAr5r;%3221r<%6221%;5J:981&R5&RB%12M7r8r=%55@3>21'Q@&RNvQ7vQ?vQ;&RD%11Gv2v3&RC%12Q;Cr7r>%=;<;:9765321?&R;%16Q@7Q0AHN&R:r@%26Q3DKMQ11&R>%13BAQ5&R?&Q2rA%211%45QJQ:8Q41&R<rB%611%33<Q61&RO(<%14QMQMQ;Q@%33QM1:'A&S5+@%22Q>1z%53R421&S4%123QB'B'@'QE&RIvS?rLrKrCrI%R0221rJ%R3221&RJ%11QF%;5:9831r3r2r1%?5>3215%A3QL51&RM%12:4&C&SL%12S=7%B11%411%<1;rE%RD21G%RF31I>%Q73S>41p061pX0SE1&QB&S1&RG%11S0&RF%11S2%5231u4%85RCI21Q>&R2%13KQOR5r?%13ONM%Q>231%Q?261%Q@2@1%QA2M1%QB2Q01qRFT21%QE2T31qW:T:1%QG2T;1qRNT;1%QI2T<1%R=1Q9&R9rH%24T8SH1Q='D&QG%124QA&QN%13RAREQC%5231p071p0;1pX0T=1%RF1QF&R7%12T4QI&QM%12?QLp031p061pX0TE1%R81QN&R6%12T<R1%QL11p041pX0TK1%S13TKR5R;&8%13TNTNR8%S03TO1QL%R311r4%53U2U21&>%13U4U43%M331R?%Q315%R:11p031p091p0>1pX0U;1pVDU;1rF%13TM=RH&R@rOrNrM&R0%11RM%6?UITFTETDTAT@TNU9543S9S8RO1rQ3%RL21F%61RI%RL11%TB1S3rQ6%11S5%SN3V531p051pX0V<1'6rQ5%UB3B1S:(7%T53421%U;1S>%UH1S?%T83V?21p041pX0VF1rQ0%UK31U3SC%UL32ASD%T>3=21pX0VK1&QO%12EU8'QCrQ1%221UI'RLvSF(N%T=5T<ULV3V:T3%221V:rQ<%64UL521p081p0<1p0?1p0E1p0Q01p0Q91p0Q<1p0QD1pW6W91pR>W;1pRFW<1pW:WC1pRNWC1%TN5TMQHQGQFTD%C21TM%F4V<E1Q0p041p0R01p0RB1p0RI1p0S21p0S@1p0U;1p0U>1p0UE1p0UJ1p0UO1p0V51p0V81p0V<1p0V?1p0VN1p0W51pRJWB1pVLWM1pVHWN1pQBWH1p2WN1pVNWL1pQLWN1pQ@WO1pQJX21pQDX81pW4X<1pR:X>1pW8XE1pRLXE1pQFXL1").
Proof.
intros K R pc0 M model G LB FF LK cr A FP b0 c0 Q REPr FS B0 CRED CLI KN LZ EG HB0 Hb0a Hb0n RUN FPAZ FPFS FPCS FPSH CONT.
destruct RUN as (R' & pc1 & Mr' & MS & GRr & FRr & LSAN & SHr & HQ).
apply (bridge_msteps ASEGS scfg Hwx MAPS0 RESV0 NOACC0 (rn_HI rn) BASE BUDGET (g_log art_fsg G) A (mkst R pc0 M (seg_rom ASEGS)) model
(mkst R' pc1 Mr' (seg_rom ASEGS)) K B0).
{ rewrite restrict_mkst. exact MS. }
intros ms' model' Est B1 RT BS. destruct (restrict_eq_mkst _ _ _ _ _ _ Est) as (Ems & EMr0). set (M1 := ms_mem ms') in *. rewrite Ems. assert (EMr : mrestrict (bhid A model') M1 = Mr') by (symmetry; exact EMr0).
change (ms_mem (mkst R pc0 M (seg_rom ASEGS))) with M in BS.
pose proof (art_bstep_pure_frame A M M1 model model' Mr' BS EMr) as FRAME.
pose proof (art_bstep_pure_grows A M M1 model model' Mr' BS EMr GRr) as GROW.
pose proof (art_bstep_pure_hid A M M1 model model' BS) as HID.
assert (FR1 : forall x : word, ~ FP (U x) -> M1 x = M x) by (intros x Hx; apply FRAME; apply FRr; exact Hx).
assert (VIS1 : forall x : word, bhid A model x = false -> M1 x = Mr' x).
{ intros x Hx. rewrite (art_bstep_pure_mem A M M1 model model' Mr' BS EMr). rewrite Hx. reflexivity. }
pose proof CLI as (C1 & _). destruct (C1 (b0, c0) HB0) as (K1 & _ & K3 & K4 & K5 & _ & _ & _ & K9 & _). cbn [fst snd] in *.
assert (SH1 : HAJ.shadow_blkR M1 b0 c0).
{ apply (shadow_blkR_frame Mr' M1 b0 c0); [lia| |lia| |exact SHr].
- pose proof (Z.div_mod b0 16 ltac:(lia)) as D. rewrite K3, Z.add_0_r in D. rewrite D. replace (16 * (b0 / 16)) with ((2 * (b0 / 16)) * 8) by ring. apply Z_mod_mult.
- intros a Ha. apply VIS1. exact (art_vis_shadow A model b0 c0 a K9 Ha). }
apply (CONT R' pc1 Mr' M1 model' HQ); [ | exact GROW | exact FR1 | exact VIS1 | exact HID | exact RT | exact (bi_minv _ _ _ _ _ _ _ _ _ _ _ B1)].
exists G. cbn [vml_of fst snd].
split. { change (mkH (m_vm_lazy model') A) with (bhid A model'). rewrite EMr. apply (art_alloc_rep_frame_sh art_fsg MAPS0 RESV0 rn G LB _ Mr' b0 c0 REPr GRr).
- intros x Hz Hb Hs. apply FRr. intros HF. destruct (FPAZ _ HF Hz) as [X|X]; [exact (Hb X)|exact (Hs X)].
- exact LSAN.
- exact (bi_live _ _ _ _ _ _ _ _ _ _ _ B0).
- exact KN.
- exact HB0.
- exact Hb0a.
- exact Hb0n.
- exact SHr. }
split. { apply (art_fsinv_client_proved rn (g_fs art_fsg G) FF LK M M1 FS GROW).
- intros x a Hz Hn. apply FR1. intros HF. apply Hn. exact (FPFS _ HF Hz).
- intros x Hz. apply FR1. intros HF. exact (FPCS _ HF Hz). }
split. { exact (BINV_intro _ _ _ _ _ _ _ _ _ _ _ B1). }
split; [exact CRED|].
split. { apply (art_client_ok_frame_sh rn LB FF LK A M M1 b0 c0 CLI GROW HB0); [|exact SH1]. intros b a Hb Nb Ha.
pose proof CLI as (C1' & _ & _ & _ & _ & _ & _ & _ & _ & _ & CT). destruct (C1' b Hb) as (L1 & _ & _ & L4 & L5 & _).
assert (Ra : 0 <= a < 2 ^ 64).
{ unfold in_shadow_of, HeapIfaceA.S in Ha. assert (0 <= fst b / 8) by (apply Z.div_pos; lia).
assert ((fst b + snd b - 1) / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; lia). change (2 ^ 47 / 8) with 17592186044416 in *. unfold HeapIfaceA.SB in *. lia. }
pose proof (FR1 (Z_to_bv 64 a)) as X. rewrite art_u_lit in X by exact Ra. apply X. exact (FPSH b a Hb Nb Ha). }
split; [exact KN|].
split. { apply (art_lazy_ok_shrink art_fsg rn G A (m_vm_lazy model) (m_vm_lazy model') LZ). exact (art_bstep_pure_lazy A M M1 model model' BS). }
destruct EG as (AW & EB). split; [exact AW|]. intros b x Hb Hx. destruct (page_in_ranges (page_base x) (m_vm_lazy model')) eqn:E; [|reflexivity].
pose proof (art_bstep_pure_lazy A M M1 model model' BS x E) as E0. rewrite (EB b x Hb Hx) in E0. discriminate E0.
Qed.
End WrapS.
Lemma art_ann_grow_shadow : ltac2:(TCodec.tc2 tcn__JbtWrapAnn "RF'SKyR0%211';y8%511%311p051'F&S3zr2%3221&S4r3%2214r5%8231'A&S5+8%2251%43>1<&R1r;r9r7r8%544321'@r1%F2E1&S2r:%221>%F251%7251&C%M24K%72>C%K2M1%<231%511r>&SJ&S1&QIr=%211%421Q3%62QA1%811r?%113%Q43Q@31p0=1p0D1pW2QA1%QA2HL%Q>2MD%O221%@2=QB%B2QM1%D11(5%E2QMQG%22QM1%QA3QM41p081pW2QM1r<%Q@4H1Q>Q?p031p0@1p0Q>1p0QE1p0QF1p0QL1p0QO1p0R31pWNR81pWLR91pVJR:1pVDR;1pRBR=1pRDR>1").
Proof.
intros Mo Mn b c u u' Hu Huu Hu' H8 H8' (Z0 & F0) KEEP NEW.
assert (D1 : u / 8 <= u' / 8) by (apply Z.div_le_mono; lia). assert (D2 : u' / 8 <= c / 8) by (apply Z.div_le_mono; lia).
assert (D0 : 0 <= u / 8) by (apply Z.div_pos; lia).
split.
- intros j Hj. unfold byte_at. destruct (Z_lt_ge_dec j (u / 8)) as [Lo|Hi].
+ rewrite KEEP by lia. exact (Z0 j ltac:(lia)).
+ exact (NEW j ltac:(lia)).
- intros j Hj. unfold byte_at. rewrite KEEP by lia. exact (F0 j ltac:(lia)).
Qed.
Lemma art_ann_shrink_shadow : ltac2:(TCodec.tc2 tcn__JbtWrapAnn "RF'SKyR0%211';y8%511%311p051'F&S3zr1%3221&S4r2r3%3221r4r5%:221'A&S5+8%2251%43@1>&R1r;r9r7r8%544321'@&S2r:%221<%F2H1%52H1&C%62;@%N21I%K2J6%:221%511r>&SJ&S1&QIr=%211%421Q2%62QA1%811r?%113%Q23Q@31p0=1p0D1pW2QA1%QA2DQ?%L21H%?2<Q>%A2QL1%C11(5+WL%E2QM1%32QM1%Q?3QM51p091pW2QM1r<%Q>4H1Q<Q=p031p0@1p0Q<1p0QC1p0QD1p0QJ1p0QN1p0R31pWNR81pWLR91pVJR:1pVDR;1pRBR=1pRDR>1").
Proof.
intros Mo Mn b c u u' Hu Huu Hu' H8 H8' (Z0 & F0) KEEP NEW.
assert (D1 : u' / 8 <= u / 8) by (apply Z.div_le_mono; lia). assert (D2 : u / 8 <= c / 8) by (apply Z.div_le_mono; lia).
assert (D0 : 0 <= u' / 8) by (apply Z.div_pos; lia).
split.
- intros j Hj. unfold byte_at. rewrite KEEP by lia. exact (Z0 j ltac:(lia)).
- intros j Hj. unfold byte_at. destruct (Z_lt_ge_dec j (u / 8)) as [Lo|Hi].
+ exact (NEW j ltac:(lia)).
+ rewrite KEEP by lia. exact (F0 j ltac:(lia)).
Qed.
Lemma art_ann_eq_shadow : ltac2:(TCodec.tc2 tcn__JbtWrapAnn "QE'SKyR0%211';y8%511%311p051'F&R1r5r3r1r2%544321'@&S3z%2216&S4&S2r4+8%3221%52<1%:271'Ar7&SJ&S1&QIr6%211%421D%62Q11%811r8%113%<3Q031p0>1pW2Q01%I2HN%J2OE%L221%Q34A=GQ2p021p061p0Q11pWLQ81pVJQ91pVDQ:1pRBQ<1pRDQ=1").
Proof.
intros Mo Mn b c u (Z0 & F0) KEEP Hu. assert (D2 : u / 8 <= c / 8) by (apply Z.div_le_mono; lia).
split; intros j Hj; unfold byte_at; rewrite KEEP by lia; [exact (Z0 j Hj)|exact (F0 j Hj)].
Qed.
Lemma art_ann_shadowR : ltac2:(TCodec.tc2 tcn__JbtWrapAnn "Q9'SKyR0%211';y8%511%311p051'F'A&S5r2+8%3221z%63721'@&S3%1247r3%3291%5231%<23:%>3?19&R1r7r6r4r5%544321&R2r8%23176p041p0;1p0>1p0E1pWLM1pVJN1pVDO1pR:Q11").
Proof. intros M b c u Hc Hu Hu8 AN. right. split; [exact Hc|]. exists u. split; [exact Hu|]. split; [exact Hu8|exact AN]. Qed.
Definition art_ann_place (b c : Z) : Prop := (b + c <= 0x10000 \/ 0x693000 <= b) /\ (b + c <= 0x7fff7000 \/ 0x10007fff8000 <= b).
Section WA.
Variables MAPS0 RESV0 NOACC0 : list (word * word).
Variables BASE BUDGET : Z.
Variable rn : art_run.
Variable scfg : SpuriousCfg.
Hypothesis Hwx : wx_segs_nowrap ASEGS.
Variable L : asan_layout.
Hypothesis HLsegs : hl_segs L = ASEGS.
Hypothesis HLlo : hl_img_lo L = 0x10000.
Hypothesis HLhi : hl_img_hi L = 0x693000.
#[local] Abbreviation RI := (art_ri_inv art_fsg MAPS0 RESV0 NOACC0 BASE BUDGET art_fsinv rn).
Context {fx : PropExec.FPState}.
Section SE.
Variables (R : bvmap 5 word).
Variables (M : word -> option byte).
Variables (model : Model).
Variables (LB : list (Z * Z)).
Variables (FF LK : list fframe).
Variables (cr : credit).
Variables (A : list (Z * Z)).
Variables (K : ShapeAlg.TSet).
Variables (b c u u' : Z).
Theorem art_wrap_annotate : let sp := U (getr R 2) in
RI LB FF LK cr A M (vml_of model) -> m_halted model = None -> MInv A model ->
getr R 10 = Z_to_bv 64 b -> getr R 11 = Z_to_bv 64 (b + c) -> getr R 12 = Z_to_bv 64 (b + u) -> getr R 13 = Z_to_bv 64 (b + u') ->
In (b, c) LB -> b mod 16 = 0 -> c mod 8 = 0 -> u mod 8 = 0 -> u' mod 8 = 0 -> 0 <= u <= c -> 0 <= u' <= c ->
HAJ.ann_shadow M b u c ->
getr R 4 = Z_to_bv 64 (rn_tp rn) -> Hoare.ret_ok (getr R 1) ->
astack_ok L (rn_ar rn) M 2304 sp -> K [] ->
(forall (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (A' : list (Z * Z)),
regs_preserved R R' -> HAJ.ann_shadow M' b u' c ->
(forall a, 0 <= a < 2 ^ 64 -> aclient L (rn_ar rn) LB FF sp 2304 a -> ~ in_shadow_of b c a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
(forall a, in_shadow_of b c a -> M (Z_to_bv 64 a) <> None -> M' (Z_to_bv 64 a) <> None) ->
(forall a, sp - 2304 <= a < sp -> M' (Z_to_bv 64 a) <> None) ->
model_rt model model' -> incl A A' -> MInv A' model' ->
RI LB FF LK cr A' M' (vml_of model') ->
srealizes ASEGS scfg (mkCfg (mkst R' (getr R 1) M' (seg_rom ASEGS)) model') K) ->
srealizes ASEGS scfg (mkCfg (mkst R (0x7b3f4 : word) M (seg_rom ASEGS)) model) K.
Proof using Hwx HLsegs HLlo HLhi R M model LB FF LK cr A K b c u u'.
intros sp INV Hhalt HMI H10 H11 H12 H13 Hin Hb16 Hc8 Hu8 Hu8' Hu Hu' ANN H4 Hret AST KT0 CONT.
destruct (art_ri_open MAPS0 RESV0 NOACC0 BASE BUDGET rn LB FF LK cr A M model INV Hhalt HMI) as (G & REPr & FS & B0 & CRED & CLI & KN & LZ & EG).
set (Mr0 := mrestrict (bhid A model) M) in *.
destruct AST as (S16 & SHI & SLE & STOP & SWR & SDEF). fold sp in S16, SHI, SLE, SWR, SDEF. rewrite HLsegs in SWR.
assert (HIeq : ahl_ceil (rn_ar rn) = rn_HI rn) by reflexivity. rewrite HIeq in SHI.
pose proof (art_cli_hi rn LB FF LK A M CLI) as (HI1 & HI2).
pose proof REPr as (ROK & STAT & THR & _).
pose proof CLI as (CB & _). destruct (CB (b, c) Hin) as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12 & K13). cbn [fst snd] in *.
rewrite HIeq in K5.
destruct (art_wfa_kind art_fsg rn G LB Mr0 REPr b c Hin) as (kd & KIND).
destruct (art_wfa_hdr art_fsg rn G LB Mr0 REPr b c kd KIND) as ((bb & _ & _ & _ & _ & Hc28) & _).
assert (Hb8 : b mod 8 = 0) by (pose proof (Z.div_mod b 16 ltac:(lia)) as D; rewrite Hb16, Z.add_0_r in D; rewrite D; replace (16 * (b / 16)) with ((2 * (b / 16)) * 8) by ring; apply Z_mod_mult).
destruct K6 as (_ & K6 & _). unfold BIGSHADOW_LO, BIGSHADOW_HI in K6.
assert (PLACE : art_ann_place b c) by exact (conj K2 K6). clear K2 K6 K12 K13.
set (lo := art_ann_lo b u u') in *. set (n := art_ann_n u u') in *. set (v := art_ann_v u u') in *.
assert (Elo8 : lo / 8 = b / 8 + Z.min u u' / 8).
{ unfold lo, art_ann_lo. pose proof (Z.div_mod b 8 ltac:(lia)) as Db. rewrite Hb8, Z.add_0_r in Db. rewrite Db at 1.
rewrite Z.mul_comm, Z.div_add_l by lia. rewrite Z.add_comm. reflexivity. }
assert (Ediv : forall x y, x mod 8 = 0 -> y mod 8 = 0 -> (x - y) / 8 = x / 8 - y / 8).
{ intros x y Hx Hy. pose proof (Z.div_mod x 8 ltac:(lia)) as Dx. pose proof (Z.div_mod y 8 ltac:(lia)) as Dy. rewrite Hx, Z.add_0_r in Dx. rewrite Hy, Z.add_0_r in Dy.
rewrite Dx at 1. rewrite Dy at 1. replace (8 * (x / 8) - 8 * (y / 8)) with ((x / 8 - y / 8) * 8) by ring. apply Z.div_mul. lia. }
assert (ESb : HeapIfaceA.S b = 2147450880 + b / 8) by (unfold HeapIfaceA.S, HeapIfaceA.SB; ring).
assert (Dc : 0 <= c / 8) by (apply Z.div_pos; lia).
assert (Hcu : u / 8 <= c / 8) by (apply Z.div_le_mono; lia). assert (Hcu' : u' / 8 <= c / 8) by (apply Z.div_le_mono; lia).
assert (Hu0 : 0 <= u / 8) by (apply Z.div_pos; lia). assert (Hu0' : 0 <= u' / 8) by (apply Z.div_pos; lia).
set (jlo := Z.min u u' / 8). set (jhi := Z.max u u' / 8).
assert (EJ : lo / 8 = b / 8 + jlo /\ n / 8 = jhi - jlo /\ 0 <= jlo <= jhi /\ jhi <= c / 8).
{ unfold jlo, jhi, n, art_ann_n. rewrite Elo8. destruct (Z.le_ge_cases u u') as [Le|Ge].
- rewrite Z.min_l, Z.max_r by lia. rewrite Z.abs_neq by lia. replace (- (u - u')) with (u' - u) by ring. rewrite (Ediv u' u Hu8' Hu8).
assert (u / 8 <= u' / 8) by (apply Z.div_le_mono; lia). lia.
- rewrite Z.min_r, Z.max_l by lia. rewrite Z.abs_eq by lia. rewrite (Ediv u u' Hu8 Hu8').
assert (u' / 8 <= u / 8) by (apply Z.div_le_mono; lia). lia. }
destruct EJ as (EJ1 & EJ2 & EJ3 & EJ4).
assert (SBr : 0 <= b / 8 /\ b / 8 + c / 8 <= 2 ^ 44).
{ split; [apply Z.div_pos; lia|]. assert ((b + c) / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; lia).
pose proof (Z.div_mod b 8 ltac:(lia)). pose proof (Z.div_mod c 8 ltac:(lia)). change (2 ^ 47 / 8) with (2 ^ 44) in *. rewrite Hb8, Z.add_0_r in *. rewrite Hc8, Z.add_0_r in *.
assert ((b + c) / 8 = b / 8 + c / 8) by (symmetry; apply Z.div_unique_exact; lia). lia. }
assert (INSH : forall j, 0 <= j < c / 8 -> in_shadow_of b c (HeapIfaceA.S b + j)).
{ intros j Hj. unfold in_shadow_of. split; [lia|]. unfold HeapIfaceA.S.
assert (b / 8 + j <= (b + c - 1) / 8); [|lia]. apply Z.div_le_lower_bound; [lia|].
pose proof (Z.div_mod b 8 ltac:(lia)) as Db. pose proof (Z.div_mod c 8 ltac:(lia)) as Dc'. rewrite Hb8, Z.add_0_r in Db. rewrite Hc8, Z.add_0_r in Dc'. lia. }
assert (VSH : forall j, 0 <= j < c / 8 -> bhid A model (Z_to_bv 64 (HeapIfaceA.S b + j)) = false).
{ intros j Hj. exact (art_vis_shadow A model b c _ K9 (INSH j Hj)). }
assert (WM : wrA M (sp - 2192) 2192). { intros d k Hd Hk. replace (sp - 2192 + d) with (sp - 2304 + (112 + d)) by lia. apply SWR; lia. }
assert (W0 : wrA Mr0 (sp - 2192) 2192).
{ apply (art_stack_wr art_fsg rn G A (m_vm_lazy model) M sp 2192 ROK LZ ltac:(lia) ltac:(lia) ltac:(lia)). intros d k Hd Hk. apply WM; lia. }
destruct STAT as (PC & LAY & TSD & _ & _ & _ & _ & S8).
assert (CF : cellA Mr0 (0x13a238 + 96) 1 1) by conj_find S8.
assert (CV : cellA Mr0 0x1343f0 8 0x1cc4d8) by conj_find S8.
assert (CV0 : cellA Mr0 0x1cc4d8 4 0) by conj_find S8.
assert (WSH : wrA Mr0 (JbtPoison.SB + lo / 8) (n / 8)).
{ unfold JbtPoison.SB. apply art_wr_of_defined; [lia|lia|]. intros x Hx.
set (j := U x - HeapIfaceA.S b). assert (Ej : x = Z_to_bv 64 (HeapIfaceA.S b + j)) by (unfold j; rewrite <- (Z_to_bv_bv_unsigned 64 x) at 1; f_equal; ring).
assert (Hj : 0 <= j < c / 8) by (unfold j; rewrite ESb; lia).
unfold Mr0, mrestrict. rewrite Ej, (VSH j Hj).
destruct (shadow_blkR_bytes M b c K4 K8 j (proj1 Hj) (or_introl (proj2 Hj))) as (v0 & Bv). unfold byte_at in Bv. rewrite Bv. discriminate. }
assert (Hsp2 : getr R 2 = Z_to_bv 64 sp) by (unfold sp; rewrite Z_to_bv_bv_unsigned; reflexivity).
destruct (art_annotate_run R Mr0 (seg_rom ASEGS) (getr R 1) sp b c u u' eq_refl Hret Hsp2 H10 H11 H12 H13 K1 Hb8 Hc8 Hu8 Hu8' Hu Hu'
ltac:(lia) ltac:(lia) (proj2 PLACE) ltac:(lia) ltac:(lia) W0 LAY CF CV CV0 WSH)
as (R' & Mr' & RUN & Q1 & Q2 & Q8 & Q9 & Q18 & Q19 & Q20 & Q21 & QK & QGR & QFR & QNEW).
fold lo n v in QFR, QNEW. unfold JbtPoison.SB in QFR, QNEW.
assert (ANN0 : HAJ.ann_shadow Mr0 b u c).
{ apply (art_ann_eq_shadow M Mr0 b c u ANN); [|exact Hu]. intros j Hj. unfold Mr0, mrestrict. rewrite (VSH j Hj). reflexivity. }
assert (KEEPj : forall j, 0 <= j < c / 8 -> ~ (jlo <= j < jhi) -> Mr' (Z_to_bv 64 (HeapIfaceA.S b + j)) = Mr0 (Z_to_bv 64 (HeapIfaceA.S b + j))).
{ intros j Hj Nj. apply QFR; rewrite art_u_lit by (rewrite ESb; lia); rewrite ESb; lia. }
assert (NEWj : forall j, jlo <= j < jhi -> Mr' (Z_to_bv 64 (HeapIfaceA.S b + j)) = Some (Z_to_bv 8 v)).
{ intros j Hj. replace (HeapIfaceA.S b + j) with (2147450880 + lo / 8 + (j - jlo)) by (rewrite ESb; lia). apply QNEW. lia. }
assert (ANN' : HAJ.ann_shadow Mr' b u' c).
{ destruct (Z.lt_trichotomy u u') as [Lt|[Eq|Gt]].
- assert (Ej : jlo = u / 8 /\ jhi = u' / 8) by (unfold jlo, jhi; rewrite Z.min_l, Z.max_r by lia; split; reflexivity).
assert (Ev : v = 0) by (unfold v, art_ann_v; rewrite (proj2 (Z.ltb_lt u u') Lt); reflexivity).
destruct Ej as (Ej1 & Ej2). rewrite Ej1, Ej2 in KEEPj, NEWj. rewrite Ev in NEWj.
exact (art_ann_grow_shadow Mr0 Mr' b c u u' (proj1 Hu) Lt (proj2 Hu') Hu8 Hu8' ANN0 KEEPj NEWj).
- subst u'. apply (art_ann_eq_shadow Mr0 Mr' b c u ANN0); [|exact Hu]. intros j Hj. apply KEEPj; [exact Hj|]. unfold jlo, jhi. rewrite Z.min_id, Z.max_id. lia.
- assert (Ej : jlo = u' / 8 /\ jhi = u / 8) by (unfold jlo, jhi; rewrite Z.min_r, Z.max_l by lia; split; reflexivity).
assert (Ev : v = 252) by (unfold v, art_ann_v; rewrite (proj2 (Z.ltb_ge u u') ltac:(lia)); reflexivity).
destruct Ej as (Ej1 & Ej2). rewrite Ej1, Ej2 in KEEPj, NEWj. rewrite Ev in NEWj.
exact (art_ann_shrink_shadow Mr0 Mr' b c u u' (proj1 Hu') Gt (proj2 Hu) Hu8 Hu8' ANN0 KEEPj NEWj). }
assert (NBsh : forall x, 2147450880 + lo / 8 <= x < 2147450880 + lo / 8 + n / 8 -> in_shadow_of b c x).
{ intros x Hx. replace x with (HeapIfaceA.S b + (x - HeapIfaceA.S b)) by ring. apply INSH. rewrite ESb; lia. }
set (FP := fun x : Z => (sp - 2192 <= x < sp) \/ (2147450880 + lo / 8 <= x < 2147450880 + lo / 8 + n / 8)).
apply (art_wrap_pure2sh MAPS0 RESV0 NOACC0 BASE BUDGET rn scfg Hwx K R _ M model G LB FF LK cr A FP b c
(fun R1 pc1 M1 => pc1 = getr R 1 /\ R1 = R' /\ M1 = Mr') REPr FS B0 CRED CLI KN LZ EG Hin Hb16 K4).
-
exists R', (getr R 1), Mr'. split; [exact RUN|]. split; [exact QGR|].
split. { intros x Hx. apply QFR; intros X; apply Hx; unfold FP; [left|right]; exact X. }
split. { pose proof THR as (_ & _ & _ & _ & _ & _ & _ & THR0).
assert (TL : 0x10000 <= rn_tp rn + rn_loff rn /\ rn_tp rn + rn_loff rn + 4 <= 0x693000)
by (destruct ROK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & T1 & T2 & _); exact (conj T1 T2)).
apply (JbtAllocG.cell_agree Mr0 Mr'); [|clear - TL; lia|cbn; clear - TL; lia|exact THR0].
intros x Hx. cbn in Hx. apply QFR; clear - Hx TL SHI HI1 EJ1 EJ3 SBr; lia. }
split; [exact (art_ann_shadowR Mr' b c u' Hc8 Hu' Hu8' ANN')|]. split; [reflexivity|split; reflexivity].
-
intros x HF Z. destruct HF as [X|X].
+ exfalso. pose proof (art_zone_below MAPS0 RESV0 NOACC0 BASE BUDGET rn G LB A M Mr0 model x REPr KN B0 (or_introl Z)) as ZB. clear - ZB X SHI. lia.
+ right. exact (NBsh x X).
-
intros x HF Z3. exfalso. destruct HF as [X|X].
+ pose proof (art_fs_zone3_below rn G LB _ x REPr Z3) as ZB. clear - ZB X SHI. lia.
+ pose proof ROK as ROK'. rok_open ROK'. pose proof GEO as GEO'. geo_open GEO'. destruct Fapp as (_ & Fap & _). unfold BIGSHADOW_LO, BIGSHADOW_HI in Fap. unfold fs_zone3, FS_BYTES in Z3. unfold FS_BYTES in Fap. clear - X Z3 Fap G10 G19 G20 EJ1 EJ2 EJ3 EJ4 SBr. lia.
-
intros x HF CS. destruct HF as [X|X].
+ pose proof (art_cs_zone_below rn G LB FF LK M Mr0 x REPr FS CS) as CB1. clear - CB1 X SHI. lia.
+ unfold cs_zone in CS. change (HeapIfaceA.S 0x10000) with 2147459072 in CS. change (HeapIfaceA.S 0x693000) with 2148312576 in CS.
assert (KB : b + c <= 0x10000 -> b / 8 + c / 8 <= 0x2000).
{ intros HB. clear - HB Hb8 Hc8. assert (E1 : (b + c) / 8 <= 0x10000 / 8) by (apply Z.div_le_mono; lia).
pose proof (Z.div_mod b 8 ltac:(lia)) as Db. pose proof (Z.div_mod c 8 ltac:(lia)) as Dc. rewrite Hb8, Z.add_0_r in Db. rewrite Hc8, Z.add_0_r in Dc.
assert (E2 : (b + c) / 8 = b / 8 + c / 8) by (symmetry; apply Z.div_unique_exact; lia). change (0x10000 / 8) with 0x2000 in E1. lia. }
assert (KB' : 0x693000 <= b -> 0xd2600 <= b / 8) by (intros HB; clear - HB; change 0xd2600 with (0x693000 / 8); apply Z.div_le_mono; lia).
destruct PLACE as (K2 & _). pose proof ROK as ROK'. rok_open ROK'. pose proof GEO as GEO'. geo_open GEO'. destruct Fapp as (_ & Fap & _). unfold BIGSHADOW_LO, BIGSHADOW_HI in Fap. unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI in D3. clear - X CS K2 KB KB' EJ1 EJ2 EJ3 EJ4 D0 D1 D2 D3 G19 G20 SBr. unfold apart in *. lia.
-
intros b' x Hb' Nb' Hx HF. destruct HF as [X|X].
+ pose proof (art_block_shadow_below rn LB FF LK A M b' x CLI Hb' Hx) as B1. clear - B1 X SHI HI1. lia.
+ pose proof (K10 b' (art_lb_remove_keep b LB b' Hb' Nb')) as AP. destruct (CB b' Hb') as (L1 & _ & L3 & L4 & _).
unfold in_shadow_of, HeapIfaceA.S, HeapIfaceA.SB in Hx.
pose proof (Z.div_mod b 8 ltac:(lia)) as Db. rewrite Hb8, Z.add_0_r in Db.
assert (Hb'8 : fst b' mod 8 = 0) by (pose proof (Z.div_mod (fst b') 16 ltac:(lia)) as D; rewrite L3, Z.add_0_r in D; rewrite D; replace (16 * (fst b' / 16)) with ((2 * (fst b' / 16)) * 8) by ring; apply Z_mod_mult).
pose proof (Z.div_mod (fst b') 8 ltac:(lia)) as Db'. rewrite Hb'8, Z.add_0_r in Db'.
destruct AP as [AP|AP].
* assert (b / 8 + c / 8 <= fst b' / 8).
{ pose proof (Z.div_mod c 8 ltac:(lia)) as Dc'. rewrite Hc8, Z.add_0_r in Dc'. clear - Dc' Db Db' AP. lia. }
clear - X Hx H EJ1 EJ2 EJ3 EJ4. lia.
* assert ((fst b' + snd b' - 1) / 8 < b / 8) by (apply Z.div_lt_upper_bound; clear - Db AP L4; lia).
clear - X Hx H EJ1 EJ2 EJ3. lia.
-
intros R1 pc1 M1 M2 model' (Epc & ER & EM) RI' GROW FR1 VIS1 HID RT MI'. subst pc1 R1 M1.
apply (CONT R' M2 model' A).
+ apply keeps_cs_preserved. intros r Hr. cbn [callee_saved In] in Hr.
repeat (destruct Hr as [<-|Hr]; [first [ exact Q1 | rewrite Q2; exact (eq_sym Hsp2) | exact Q8 | exact Q9 | exact Q18 | exact Q19 | exact Q20 | exact Q21
| apply QK; unfold art_ann_kept; tauto ]|]).
destruct Hr.
+ apply (art_ann_eq_shadow Mr' M2 b c u' ANN'); [|exact Hu']. intros j Hj. exact (VIS1 _ (VSH j Hj)).
+ intros a Ra Ha NS. apply FR1. rewrite art_u_lit by exact Ra. unfold FP. intros [X|X].
* apply (art_cls_off_scratch rn LB FF LK A M CLI L HLlo HLhi (g_fs art_fsg G) FS sp 2304 a ltac:(clear - SHI; lia) (or_intror Ha)). clear - X. lia.
* exact (NS (NBsh a X)).
+ intros a Ha Hd. apply GROW. exact Hd.
+ intros a Ha. apply GROW.
assert (WM2 : wrA M (sp - 2304) 2304) by (intros d k Hd Hk; apply SWR; assumption).
pose proof (art_wr_wview ASEGS M (sp - 2304) 2304 ltac:(clear - SHI HI1; lia) ltac:(clear - SLE STOP; lia) WM2 (Z_to_bv 64 a)) as V.
rewrite art_u_lit in V by (clear - Ha SHI HI1 SLE STOP; lia). specialize (V ltac:(clear - Ha; lia)).
rewrite art_wview_off in V by (rewrite art_u_lit by (clear - Ha SHI HI1 SLE STOP; lia); right; clear - Ha SHI HI1; lia). exact V.
+ exact RT.
+ apply incl_refl.
+ exact MI'.
+ exact RI'.
Qed.
End SE.
End WA.
