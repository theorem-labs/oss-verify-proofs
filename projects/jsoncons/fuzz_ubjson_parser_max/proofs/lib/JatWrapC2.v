(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatSim StoreOk ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA ArtMem ArtRuns ArtRunsMem JatCls JatCellEx JatDepot ArtBridge JatInv JatInvMalloc JatLift JatWrapKit
JatFsInv JatFsInvLaws JatIfaceLaws JatWrapC JatWrapVis.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLiaT.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__JatWrapC2 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.Run."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ArtBridge."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ArtMem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanAcct."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIfaceA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatFsInv."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatFsInvLaws."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatInv."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ShapeAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.StoreOk."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0A"; "0BASE"; "0BUDGET"; "1None"; "1app"; "1bool"; "1false"; "1fst"; "1list"; "1option"; "1prod"; "1snd"; "2and"; "2eq"; "2ex"; "2not"]; ["3Z"; "0FF"; "0FF'"; "0FP"; "0G"; "0K"; "0LB"; "0LK"; "0LK'"; "4mkCfg"; "5Model"; "5m_halted"; "5m_vm_lazy"; "6bvmap"; "0M"; "0M1"]; ["0MAPS0"; "0Mr"; "0Mr'"; "0NOACC0"; "0Q"; "0R"; "0R'"; "0RESV0"; "7BInv"; "7bhid"; "8cell"; "9MInv"; "9mrestrict"; ":msteps"; ";credit"; ";in_block"]; ["<FS_BYTES"; "<S"; "<ar_fs"; "<fframe"; "<fframes_apart"; "<in_fframe"; "<in_shadow_of"; "<model_rt"; "<vml_of"; "=art_fsg"; "=art_fsinv"; "=cs_zone"; ">fs_zone3"; "?art_alloc_rep"; "?art_alloc_zone"; "?art_client_ok"]; ["?art_credit_ok"; "?art_eager_ok"; "?art_gs"; "?art_kn_ok"; "?art_lazy_ok"; "?art_ri_inv"; "?g_fs"; "?g_log"; "?rn_HI"; "?rn_ar"; "?rn_loff"; "?rn_tp"; "@mkst"; "@seg_rom"; "ATSet"; "Bsrealizes"]; ["Cmem_grows"; "Dloaded_segments"; "EIn"; "Fadd"; "Fle"; "Flt"; "0b"; "0cr"; "0fx"; "0g'"; "0model"; "0model'"; "0pc0"; "0pc1"; "0rn"; "0scfg"]; ["Gbv"; "Gbv_unsigned"; "0x"]]).
Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.
#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation cellA := (cell Asan.M.loaded_segments).
#[local] Abbreviation wrA := (wr Asan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).
Section Wrap2.
Variables MAPS0 RESV0 NOACC0 : list (word * word).
Variables BASE BUDGET : Z.
Variable rn : art_run.
Variable scfg : SpuriousCfg.
Hypothesis Hwx : wx_segs_nowrap ASEGS.
Hypothesis AFL : art_alloc_rep_frame_law art_fsg MAPS0 RESV0.
Context {fx : PropExec.FPState}.
#[local] Abbreviation RI := (art_ri_inv art_fsg MAPS0 RESV0 NOACC0 BASE BUDGET art_fsinv rn).
#[local] Abbreviation BI := (BInv ASEGS MAPS0 RESV0 NOACC0 (rn_HI rn) BASE BUDGET).
#[using="Hwx AFL"] Theorem art_wrap_pure2 : ltac2:(TCodec.tc2 tcn__JatWrapC2 "X2&R>&My5'S0yR0%211%5241'9y8%611%311p061'J'R2'QI%211'8':'@%2211%411&QC%611&Q>!p071p0?2p0F1p0F1&QMvRNr8r7&Q<&Q9r3r9%3221r:%6221%;5J:981&QJ&R6%12M7r6r;%55@3>21'Q8&RAvQ0vQ7vQ3&R8%11Gv1v2&R7%12Q;Cr5r<%=;<;:9765321?&R0%16Q@7Q0AHN&QOr>%26Q3DKMQ11&R3%13BAQ5&R4&Lr?%211%45QJQ:8Q41&R1r@%611%33<Q61'>'<'Q=&R<vRHrGrFrD%QC2E1rE%QF221&R=%11Q9%:598731r2r1%=5<QJ214%?3Q>41&R@%1294&?&S1%12RO7%Q411%411'=%R41<%R62NE%R831G>%43S031p061pV6S71&Q:&RC&R;%11RB&R:%11RD%5231u4z%95R6J321%QL3RDLK%Q:221%Q;2=1%Q<2J1%Q=2M1qR6SA1%Q@2SB1qULSI1%QB2SJ1qR>SJ1%QD2SK1%R71Q6&QNrC%24SGS71Q:&Q?%123S4p031p071pV6SH1r=%11Q@&QL%12S@QC&QE%12<S=p031p061pV6T11%RD1QH&QK%12SHQK%QF11p041pV6T71&RB%13T8R0R5&QF&7%13T<T<SK&;%13T>T>SM%5331R6rB%11T0%R311p041p0;1pV6TE1pU>TE1r4%Q63S@1T7&R5rJrIrH&QH%11RE%6?U3T0SOSNSKSJT8TC543RORNT>1rN%RD21:%61RA%RD11%TF1RKrQ1%11RM%RC3U?31p051pV6UF1'5rQ0%TL3B1S2(6%RJ3421%U21S6%TN1S7%RM3UI21p041pV6V01rK%U531U7S;%U632AS<%S33=21pV6V51&QG%12EU<'Q;rL%221U@'R?vRO(I%T35T2R8THU=SJ%221U@rQ7%64U6521p081p0<1p0?1p0E1p0Q01p0Q91p0Q<1p0QD1pUHVC1pR0VE1pR6VF1pULVM1pR>VM1%TD5TCQHQGQFT;%C21TC%F4UFE1Q0p041p0R01p0R@1p0RG1p0S11p0S;1p0U11p0U61p0U<1p0U?1p0UC1p0UF1p0V51p0V<1pR:VI1pQ8VM1p2W31pU@W11pQ@W31pQ4W41pQ>W71pQ:W=1pUFWA1pQNWC1pUJWJ1pR<WJ1pQ<X11").
Proof.
intros K R pc0 M model G LB FF LK cr A FP Q REPr FS B0 CRED CLI KN LZ EG RUN FPAZ FPFS FPCS FPSH CONT.
destruct RUN as (R' & pc1 & Mr' & MS & GRr & FRr & LSAN & HQ).
apply (bridge_msteps ASEGS scfg Hwx MAPS0 RESV0 NOACC0 (rn_HI rn) BASE BUDGET (g_log art_fsg G) A (mkst R pc0 M (seg_rom ASEGS)) model
(mkst R' pc1 Mr' (seg_rom ASEGS)) K B0).
{ rewrite restrict_mkst. exact MS. }
intros ms' model' Est B1 RT BS. destruct (restrict_eq_mkst _ _ _ _ _ _ Est) as (Ems & EMr0). set (M1 := ms_mem ms') in *. rewrite Ems. assert (EMr : mrestrict (bhid A model') M1 = Mr') by (symmetry; exact EMr0).
change (ms_mem (mkst R pc0 M (seg_rom ASEGS))) with M in BS.
pose proof (art_bstep_pure_frame A M M1 model model' Mr' BS EMr) as FRAME.
pose proof (art_bstep_pure_grows A M M1 model model' Mr' BS EMr GRr) as GROW.
pose proof (art_bstep_pure_hid A M M1 model model' BS) as HID.
assert (FR1 : forall x : word, ~ FP (U x) -> M1 x = M x) by (intros x Hx; apply FRAME; apply FRr; exact Hx).
apply (CONT R' pc1 Mr' M1 model' HQ); [ | exact GROW | exact FR1 | | exact HID | exact RT | exact (bi_minv _ _ _ _ _ _ _ _ _ _ _ B1)].
- exists G. cbn [vml_of fst snd].
split. { change (mkH (m_vm_lazy model') A) with (bhid A model'). rewrite EMr. apply (AFL rn G LB _ Mr' REPr GRr).
- intros x Hz Hb. apply FRr. intros HF. apply Hb. exact (FPAZ _ HF Hz).
- exact LSAN.
- exact (bi_live _ _ _ _ _ _ _ _ _ _ _ B0).
- exact KN. }
split. { apply (art_fsinv_client_proved rn (g_fs art_fsg G) FF LK M M1 FS GROW).
- intros x a Hz Hn. apply FR1. intros HF. apply Hn. exact (FPFS _ HF Hz).
- intros x Hz. apply FR1. intros HF. exact (FPCS _ HF Hz). }
split. { exact (BINV_intro _ _ _ _ _ _ _ _ _ _ _ B1). }
split; [exact CRED|].
split. { apply (art_client_ok_frame rn LB FF LK A M M1 CLI GROW). intros b a Hb Ha.
pose proof CLI as (C1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & CT). destruct (C1 b Hb) as (K1 & _ & _ & K4 & K5 & _).
assert (Ra : 0 <= a < 2 ^ 64).
{ unfold in_shadow_of, HeapIfaceA.S in Ha. assert (0 <= fst b / 8) by (apply Z.div_pos; lia).
assert ((fst b + snd b - 1) / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; lia). change (2 ^ 47 / 8) with 17592186044416 in *. unfold HeapIfaceA.SB in *. lia. }
pose proof (FR1 (Z_to_bv 64 a)) as X. rewrite art_u_lit in X by exact Ra. apply X. exact (FPSH b a Hb Ha). }
split; [exact KN|].
split. { apply (art_lazy_ok_shrink art_fsg rn G A (m_vm_lazy model) (m_vm_lazy model') LZ). exact (art_bstep_pure_lazy A M M1 model model' BS). }
destruct EG as (AW & EB). split; [exact AW|]. intros b x Hb Hx. destruct (page_in_ranges (page_base x) (m_vm_lazy model')) eqn:E; [|reflexivity].
pose proof (art_bstep_pure_lazy A M M1 model model' BS x E) as E0. rewrite (EB b x Hb Hx) in E0. discriminate E0.
- intros x Hx. rewrite (art_bstep_pure_mem A M M1 model model' Mr' BS EMr). rewrite Hx. reflexivity.
Qed.
Definition art_gs_fs (G : art_gs art_fsg) (g : art_fsg) : art_gs art_fsg :=
GS art_fsg (g_log art_fsg G) (g_inited art_fsg G) (g_cls art_fsg G) (g_st art_fsg G) (g_sec art_fsg G) (g_sec_committed art_fsg G)
(g_qt art_fsg G) (g_qg art_fsg G) (g_depot art_fsg G) (g_ia art_fsg G) g.
#[using="Type"] Lemma art_client_ok_frames : ltac2:(TCodec.tc2 tcn__JatWrapC2 "Q@'8':'@%2211%411&QC%611'S0yR0%211'9y8%511%311p051&QOvRNr7r6r5r2r1%76654321&RBr9%23F41&QD&7%13JJ8&;%13LL:&4%13K?>%73531p091pU>Q01r4r3%G6F>DC21p041p0B1pQNK1p2Q61pQBQ51pQ6Q61pQ@Q71pQ4Q81pQ>Q;1").
Proof.
intros LB FF LK FF' LK' A M (C1 & CT) AP. split; [|exact CT].
intros b Hb. destruct (C1 b Hb) as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & _ & K12).
repeat (split; [assumption|]). split; [exact (AP b Hb) | exact K12].
Qed.
#[using="Hwx AFL"] Theorem art_wrap_pure3 : ltac2:(TCodec.tc2 tcn__JatWrapC2 "XK&R>&My5'S0yR0%211%5241'9y8%611%311p061'J'R2'QI%211'8':'@%2211%411&QC%611&Q>!p071p0?2p0F1p0F1&QMvRNr;r:&Q<&Q9r6r<%3221r=%6221%;5J:981&QJ&R6%12M7r9r>%55@3>21'Q8&RAvQ0vQ7vQ3&R8%11Gv1v2&R7%12Q;Cr8r?%=;<;:9765321?&R0%16Q@7Q0AHN&QOrA%26Q3DKMQ11&R3%13BAQ5&R4&LrB%211%45QJQ:8Q41&R1rC%611%33<Q61'>'<'Q=&R<vRHrJrIrG%QC2E1rH%QF221&R=%11Q9%:598731r3r2r1%>5=3215%@3Q?51&R@%12:4&?&S1%12S07%Q511%411'=%=1<%R72OF%R931H>%43S131p061pV6S81&Q:&RC&R;%11RC&R:%11RE%5231u4z%95R7J321%QM3MLK%Q;221%Q<2=1%Q=2J1%Q>2M1qR6SB1%QA2SC1qULSJ1%QC2SK1qR>SK1%QE2SL1%R81Q6&QNrF%24SHS81Q:&Q?%123Q=p031p071pV6SI1&RB%13SJQA8&QF&7%13SNSNQE&;%13T0T0QG%5331QG%R:1QI%QC11p031p0:1pV6T61pU>T61r4%RA31R0QOrM%QM21R1%R:1QJ%QM11r5%11R5rQ0%11R7%QM3TJ31p061pV6U11'5rO%T73RF1R<(6%R43421%T91R@r7%11RB%R83U531p051pV6U<1rErD%T;5TFQ?21DrN%Q:3U3RI1&QD%Q93U6U6RL%Q83U7U7RM&4%13U6S7QF%53431p071pU>U;1%SA2;1p0?1p0K1p0Q51p0Q81pR0UI1pR6UJ1pULV11pR>V11%F3Q8Q>S=&R5rL&QH%11S@%4?UOTLTKTJTGTFU4U?3JT3SJSGSB1%S>2Q<QD%SM1S;%S>11rQ3%11SF%S<3V9Q51p041pV6V@1rQ2%UE3=1SJ%SA3QA1Q>%TO1SM%U>1SN%SD3VA21p041pV6VH1%UL3R2QAT1%UM3R3>T2%SI3QI21pV6VL1&QG%12BQF'Q;%12Q@U;'R?vRO(I%TI5THV3V5V9T@%221UNrQ9%64UL521p081p0;1p0>1p0C1p0L1p0Q41p0Q61p0Q<1pUHW91pR0W;1pR6W<1pULWC1pR>WC1rK%U;5U:QA1U9U2%D21U9%G4V=F1S1p051p0QH1p0S71p0SF1p0T01p0UG1p0UL1p0V21p0V51p0V91p0V<1p0VK1p0W21pQBWE1pQ6WF1pUDWO1pR:WB1pQ8WF1p2WL1pU@WJ1pQ@WL1pQ4WM1pQ>X01pQ:X61pUFX:1pQNX<1pUJXC1pR<XC1pQ<XJ1").
Proof.
intros K R pc0 M model G LB FF LK cr A FP Q g' FF' LK' REPr FS B0 CRED CLI KN LZ EG RUN FPAZ FPSH NEWFS CONT.
destruct RUN as (R' & pc1 & Mr' & MS & GRr & FRr & LSAN & HQ).
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
destruct (NEWFS R' pc1 Mr' M1 HQ GROW FR1 VIS1) as (FS' & AP').
apply (CONT R' pc1 Mr' M1 model' HQ); [ | exact GROW | exact FR1 | exact VIS1 | exact HID | exact RT | exact (bi_minv _ _ _ _ _ _ _ _ _ _ _ B1)].
exists (art_gs_fs G g'). cbn [vml_of fst snd].
split. { change (mkH (m_vm_lazy model') A) with (bhid A model'). rewrite EMr. change (art_alloc_rep art_fsg rn G LB Mr'). apply (AFL rn G LB _ Mr' REPr GRr).
- intros x Hz Hb. apply FRr. intros HF. apply Hb. exact (FPAZ _ HF Hz).
- exact LSAN.
- exact (bi_live _ _ _ _ _ _ _ _ _ _ _ B0).
- exact KN. }
split. { exact FS'. }
split. { exact (BINV_intro _ _ _ _ _ _ _ _ _ _ _ B1). }
split; [exact CRED|].
split. { apply (art_client_ok_frames LB FF LK FF' LK' A M1); [|exact AP']. apply (art_client_ok_frame rn LB FF LK A M M1 CLI GROW). intros b a Hb Ha.
pose proof CLI as (C1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & CT). destruct (C1 b Hb) as (K1 & _ & _ & K4 & K5 & _).
assert (Ra : 0 <= a < 2 ^ 64).
{ unfold in_shadow_of, HeapIfaceA.S in Ha. assert (0 <= fst b / 8) by (apply Z.div_pos; lia).
assert ((fst b + snd b - 1) / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; lia). change (2 ^ 47 / 8) with 17592186044416 in *. unfold HeapIfaceA.SB in *. lia. }
pose proof (FR1 (Z_to_bv 64 a)) as X. rewrite art_u_lit in X by exact Ra. apply X. exact (FPSH b a Hb Ha). }
split; [exact KN|].
split. { change (art_lazy_ok art_fsg rn G A (m_vm_lazy model')). apply (art_lazy_ok_shrink art_fsg rn G A (m_vm_lazy model) (m_vm_lazy model') LZ). exact (art_bstep_pure_lazy A M M1 model model' BS). }
destruct EG as (AW & EB). split; [exact AW|]. intros b x Hb Hx. destruct (page_in_ranges (page_base x) (m_vm_lazy model')) eqn:E; [|reflexivity].
pose proof (art_bstep_pure_lazy A M M1 model model' BS x E) as E0. rewrite (EB b x Hb Hx) in E0. discriminate E0.
Qed.
#[using="Type"] Lemma art_cs_zone_below : ltac2:(TCodec.tc2 tcn__JatWrapC2 "Q@'R2'QI%211'8':'@%2211%411&QC%611'S0yR0%211'9y8%511%311p051&QMvRNr7r6r2%55F4321&QJ&R6r8%22J1r5r4%65;3921&QKr3%22>1&RE&R8%11A%3281p051p091p0A1pV6Q41pR4I1pQNJ1pQ@Q31pQ4Q41pQ>Q71pQ:Q=1").
Proof.
intros G LB FF LK M Mr x REP FS Z. pose proof REP as (ROK & _). rok_open ROK. geo_open GEO. destruct (fsinv_cs _ _ _ _ _ FS) as ((Q1 & Q2 & Q3) & _).
unfold cs_zone in Z. change (HeapIfaceA.S 0x10000) with 2147459072 in Z. change (HeapIfaceA.S 0x691000) with 2148311552 in Z.
assert (D1' : rn_dtls rn + 4096 <= rn_HI rn) by assumption. clear - Z G1 Q1 D1'. lia.
Qed.
Section SE.
Local Abbreviation SEC_T_art_zone_not_stack_shadow := (ltac2:(TCodec.tc2 tcn__JatWrapC2 "R1'R2'QI%211'8':'@%2211%411'S0yR0%211'9y8%511%311p051'J&QMvRNr7r6r3%55E4321&R3vQ0vQ7%33218'Q8&RAvQ3&R8%11=v1v2&R7r9%22Q31r4%;;:>=97652CB1&QNr:%24Q8G14&?'<&RD&QA%11?r5%4221&RE+`PQoooPP0%2241%9241%;11p0=1p0A1p0N1p0Q31pV6QE1pUFQ;1pR4Q=1pQNQ>1p2QG1pQ>QH1pQ:QN1")) (only parsing).
Variable G : ltac:(sec_ty2 constr:(SEC_T_art_zone_not_stack_shadow) 0%nat 0%nat).
Variable LB : ltac:(sec_ty2 constr:(SEC_T_art_zone_not_stack_shadow) 1%nat 0%nat).
Variable A : ltac:(sec_ty2 constr:(SEC_T_art_zone_not_stack_shadow) 2%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_zone_not_stack_shadow) 3%nat 0%nat).
Variable Mr : ltac:(sec_ty2 constr:(SEC_T_art_zone_not_stack_shadow) 4%nat 0%nat).
Variable model : ltac:(sec_ty2 constr:(SEC_T_art_zone_not_stack_shadow) 5%nat 0%nat).
Variable x : ltac:(sec_ty2 constr:(SEC_T_art_zone_not_stack_shadow) 6%nat 0%nat).
Lemma art_zone_not_stack_shadow : ltac:(sec_stmt2 constr:(SEC_T_art_zone_not_stack_shadow) 7%nat 0%nat).
Proof using Type G LB A M Mr model x.
intros REP KN B0 Z X.
pose proof REP as (ROK & _). rok_open ROK. geo_open GEO.
pose proof (art_live_of_binv MAPS0 RESV0 NOACC0 BASE BUDGET rn _ _ _ _ B0 KN) as LIVE.
assert (SHI : 2201439137792 <= x < 0x10007fff8000).
{ unfold HeapIfaceA.S, HeapIfaceA.SB in X. assert (0x10007fff8000 / 8 <= rn_HI rn / 8) by (apply Z.div_le_mono; clear - G1; lia). change (0x10007fff8000 / 8) with 2199291686912 in H. clear - X H. lia. }
assert (SMONO : forall y, y <= rn_HI rn -> HeapIfaceA.S y <= x) by (intros y Hy; pose proof (art_S_mono y (rn_HI rn) Hy); clear - X H; lia).
unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI in Papp. unfold apart in *.
destruct Z as [Z | [Z | [Z | [Z | [Z | [Z | [Z | [Z | [Z | [Z | [Z | Z]]]]]]]]]]].
- unfold art_zone_statics in Z. clear - Z SHI. lia.
- unfold art_zone_thread in Z. clear - Z SHI G10. lia.
- clear - Z SHI G16. lia.
- unfold art_zone_kspace in Z. clear - Z SHI Khi. lia.
- destruct Z as [Z | (p & Hp & Z)]; [clear - Z SHI Papp; lia|]. destruct (LIVE p Hp) as (L1 & L2 & L3 & L4 & _). clear - Z SHI L4. lia.
- unfold art_zone_depot, dprivD in Z. clear - Z SHI Al2s Abs. lia.
- destruct Z as [Z | (p & Hp & Z)].
+ pose proof (SMONO (rn_kbase rn + 0x2000011000) ltac:(clear - Kend; lia)). clear - Z H. lia.
+ destruct (LIVE p Hp) as (L1 & L2 & L3 & _). pose proof (SMONO (fst p + snd p) ltac:(clear - L3; lia)). clear - Z H. lia.
- clear - Z SHI. lia.
- clear - Z SHI G20. lia.
- clear - Z SHI G22 Hkey. lia.
- clear - Z SHI. lia.
- clear - Z SHI. lia.
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_art_zone_off_fs := (ltac2:(TCodec.tc2 tcn__JatWrapC2 "R5'R2'QI%211'8':'@%2211%411'S0yR0%211'9y8%511%311p051'J&QMvRNr7r6r3%55E4321&R3vQ0vQ7%33218'Q8&RAvQ3&R8%11=v1v2&R7r9%22Q31r4%;;:>=97652CB1&QNr:%24Q8G14&?'<&RD&QB&R9%11M%311r5%6221&RE&RC&Q@%2261%4261%=261%?11p0A1p0E1p0Q21p0Q71pV6QI1pUFQ?1pR4QA1pQNQB1p2QK1pQ>QL1pQ:R21")) (only parsing).
Variable G : ltac:(sec_ty2 constr:(SEC_T_art_zone_off_fs) 0%nat 0%nat).
Variable LB : ltac:(sec_ty2 constr:(SEC_T_art_zone_off_fs) 1%nat 0%nat).
Variable A : ltac:(sec_ty2 constr:(SEC_T_art_zone_off_fs) 2%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_zone_off_fs) 3%nat 0%nat).
Variable Mr : ltac:(sec_ty2 constr:(SEC_T_art_zone_off_fs) 4%nat 0%nat).
Variable model : ltac:(sec_ty2 constr:(SEC_T_art_zone_off_fs) 5%nat 0%nat).
Variable x : ltac:(sec_ty2 constr:(SEC_T_art_zone_off_fs) 6%nat 0%nat).
Lemma art_zone_off_fs : ltac:(sec_stmt2 constr:(SEC_T_art_zone_off_fs) 7%nat 0%nat).
Proof using Type G LB A M Mr model x.
intros REP KN B0 Z X.
pose proof REP as (ROK & _). rok_open ROK. geo_open GEO.
pose proof (art_live_of_binv MAPS0 RESV0 NOACC0 BASE BUDGET rn _ _ _ _ B0 KN) as LIVE.
destruct Fapp as (_ & Fap & _). unfold BIGSHADOW_LO, BIGSHADOW_HI in Fap.
unfold apart, FS_BYTES in *.
destruct Z as [Z | [Z | [Z | [Z | [Z | [Z | [Z | [Z | [Z | [Z | [Z | Z]]]]]]]]]]].
- unfold art_zone_statics in Z. clear - Z X Fimg. lia.
- unfold art_zone_thread in Z. clear - Z X Aft. lia.
- clear - Z X Afc. lia.
- unfold art_zone_kspace in Z. clear - Z X Afkb. lia.
- destruct Z as [Z | (p & Hp & Z)]; [clear - Z X Afp; lia|]. destruct (LIVE p Hp) as (L1 & L2 & L3 & L4 & L5).
specialize (L5 (ar_fs (rn_ar rn), 11571200) ltac:(unfold art_objs; do 6 right; left; reflexivity)). unfold apart in L5. cbn [fst snd] in L5. clear - Z X L5. lia.
- unfold art_zone_depot, dprivD in Z. clear - Z X Fimg Afl Afb. lia.
- assert (SR : 0x7fff8000 <= x < 0x10007fff8000).
{ destruct Z as [Z | (p & Hp & Z)].
- pose proof (art_S_lo (rn_kbase rn) ltac:(clear - Khi; lia)). assert ((rn_kbase rn + 0x2000011000) / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; clear - Kend G2; lia). change (2 ^ 47 / 8) with 17592186044416 in *. unfold HeapIfaceA.S, HeapIfaceA.SB in *. clear - Z H H0. lia.
- destruct (LIVE p Hp) as (L1 & L2 & L3 & _). pose proof (art_S_lo (fst p) ltac:(clear - L1; lia)). assert ((fst p + snd p) / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; clear - L3 G2; lia). change (2 ^ 47 / 8) with 17592186044416 in *. unfold HeapIfaceA.S, HeapIfaceA.SB in *. clear - Z H H0. lia. }
clear - SR X Fap. lia.
- clear - Z X Fimg. lia.
- clear - Z X Fimg Htpd G20. lia.
- clear - Z X Fimg G21 G22 Hkey. lia.
- clear - Z X Fimg. lia.
- clear - Z X Fimg. lia.
Qed.
End SE.
#[using="Type"] Lemma art_ri_open : ltac2:(TCodec.tc2 tcn__JatWrapC2 "S4'8':'@%2211%411&QC%611&Q>'S0yR0%211'9y8%511%311p051'J&R5'QIvQ0vQ7vQ3v1v2&QJvRNr7r6r5r4r3r2&QHr1%211%B?A@?>=<;:9876541'=%J1K&K%118(3%11O%63531'Q;%12@>'>'R2%11M'<&QMr;&Q<&Q9%12KI%321K%65Q5NF51&R6%12Q7Hr:r9%Q45Q3321Q1'Q8&RA&R8%11Q7&R7%12Q@Q1%6;5Q@Q?Q>3Q=Q<1Q9Q8Q7&R0r8%26QDQ?Q=Q5D1&QO%16Q?F>=Q>Q=&R3%13QGQFQA&R4&L%11QA%35QLQEQ=QD1&R1%13NQF3%Q1231%Q2281%Q32;1%Q42>1%Q52B1%Q62J1%Q72Q01qQ:Q91%Q<2Q:1p0Q>1p0QA1p0QI1pUFR=1pQNR?1p2RK1pU@RI1pQ@RK1pQ4RL1pQ>RO1").
Proof.
intros LB FF LK cr A M model (G & REPr & FS & BV & CRED & CLI & KN & LZ & EG) Hh HMI. cbn [vml_of fst snd] in *.
exists G. split; [exact REPr|]. split; [exact FS|]. split; [exact (BINV_elim _ _ _ _ _ _ _ _ _ _ _ BV Hh HMI)|].
split; [exact CRED|]. split; [exact CLI|]. split; [exact KN|]. split; [exact LZ | exact EG].
Qed.
End Wrap2.
