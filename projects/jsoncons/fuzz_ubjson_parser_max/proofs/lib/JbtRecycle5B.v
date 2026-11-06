(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib As0Tables
ArtMem ArtRegs ArtAtomics ArtAtomics2 ArtTac ArtFxTac JbtLeaf JbtAllocG JbtPoison ArtRuns ArtRunsMem JbtFp JbtFree1 JbtCellEx JbtRecycle4.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLiaT.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import OtfKit.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__JbtRecycle5B () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ArtMem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Hoare."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtFp."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtRecycle5B."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.StoreOk."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1cons"; "1nil"; "1option"; "1pair"; "1prod"; "2I"; "2and"; "2eq"; "2ex"; "3Z"; "4bvmap"; "0M"; "0M'"; "5apart"; "5cell"; "5wr"]; ["6msteps"; "7ret_ok"; "8art_agree"; "9art_f112"; ":getr"; ":mkst"; ";mem_grows"; "<loaded_segments"; "=In"; ">add"; ">le"; ">lt"; ">mul"; ">pow"; ">sub"; "0b"]; ["0bytes"; "0c"; "0cache"; "0cbc"; "0cbs"; "0fx"; "0g18"; "0g19"; "0g20"; "0g21"; "0g22"; "0g23"; "0g24"; "0g25"; "0g8"; "0g9"]; ["0j"; "0k"; "0m"; "0next"; "0ni"; "0r"; "0raw"; "0regs"; "0regs'"; "0rom"; "0size"; "0sp"; "0sp1"; "0spb"; "?BV"; "?Z_to_bv"]; ["?bv"; "?bv_unsigned"; "0szi"; "0tmp"]]).
Local Ltac oF' pc := oF constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc.
Local Ltac oD' pc := oD constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc.
Local Ltac oE' pc := oE constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc.
Local Ltac oW' pc := oW constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc. Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Abbreviation wokA := (wok AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).
Definition art_f112 (M : word -> option byte) (sp : Z) (raw : word) (regs : bvmap 5 word) (cbc cbs : Z) : word -> option byte :=
Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 M (sp - 8) (U raw)) (sp - 16) (U (getr regs 8))) (sp - 24) (U (getr regs 9))) (sp - 32) (U (getr regs 18)))
(sp - 40) (U (getr regs 19))) (sp - 48) (U (getr regs 20))) (sp - 56) (U (getr regs 21))) (sp - 64) (U (getr regs 22))) (sp - 72) (U (getr regs 23))) (sp - 80) (U (getr regs 24)))
(sp - 88) (U (getr regs 25))) (sp - 104) cbc) (sp - 96) cbs.
Section FPX. Context {fx : PropExec.FPState}.
Section SE.
Local Abbreviation SEC_T_art_dr_pro := (ltac2:(TCodec.tc2 tcn__JbtRecycle5B "V7&:y5'R0yR0%211%5241'2y8%611%311p061'9'7&Dr9(QN+1(5%33A21%6251r6%93A21r:+2%93G17%<231&QO%12H7%@3H31r;+;%@3N1>%C231%E3M16r<+<%E3Q31C%H231%J3Q21;r=+=%J3Q81H%M231%O3Q71@&J&I+Vb\P0+S@%3221%521K&K&M+R0%22N1%42I1&?&Gr?&N%12I<%54431=%A2FK+Q0%B2H1%>21;'6z%G21L%B2M?%4221%J2QFO%6213&>rErAu8r>%55E4321'8'@&EvQ5rH+Z`T<%R53RA1R3/01RArGrF%8576321r1+Z`X4%R<3RH1R:/01RH&CrDrB%36:2G>1F%A5@851:%C3Q::1%RF2:R;%Q:26QE%R;2S21%RJ3S231+8%RI3S71RG%RL2@1rC%RA2S81%S03S831+9%RO3S=1RM%S22F1+QWTnH%RG2S>1%S63S>31+B%S53SC1S3%S82L1+QWUPH%RM2SD1%S<3SD31+C%S;3SI1S9%S>2Q21+QWUd8%S32SJ1%SB3SJ31+E%SA3SO1S?%SD2Q81+Q5%R@2S<1%S:2T11%SI3T141+:%SH3T61SF%SK2Q?1r@%S@2T71%SO3T731%T:1T;&H(0+3%T13T?1SO+4%T33TA1T1+J%T53TC1T3+K%T73TE1T5(1%11<%;3=31%<3>61%=3?91%>3@<1%@3AR41r3r2%TC221rJ%TE213%TG3TO31p071pS<I1%S52K1%S62Q21%S72Q:1%S82QA1%S92QH1%S:2QO1%S;2R61%S<2R;1qSBU91%S12U:1p0S31p0S:1p0S=1p0S>1p0SD1p0SH1p0SJ1p0T11p0T71p0T>1p0TD1p0TJ1p0U01p0U81pS4UC1pR:UD1pR8UE1pT8UF1pSHUG1pS>UO1pSDUJ1pHUK1pS@V11")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_dr_pro) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_dr_pro) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_dr_pro) 2%nat 0%nat).
Variable raw : ltac:(sec_ty2 constr:(SEC_T_art_dr_pro) 3%nat 0%nat).
Variable sp : ltac:(sec_ty2 constr:(SEC_T_art_dr_pro) 4%nat 0%nat).
Variable tmp : ltac:(sec_ty2 constr:(SEC_T_art_dr_pro) 5%nat 0%nat).
Variable cbc : ltac:(sec_ty2 constr:(SEC_T_art_dr_pro) 6%nat 0%nat).
Variable cbs : ltac:(sec_ty2 constr:(SEC_T_art_dr_pro) 7%nat 0%nat).
Variable k : ltac:(sec_ty2 constr:(SEC_T_art_dr_pro) 8%nat 0%nat).
Lemma art_dr_pro : ltac:(sec_stmt2 constr:(SEC_T_art_dr_pro) 9%nat 0%nat).
Proof using Type regs M rom raw sp tmp cbc cbs k.
intros H1 H2 H11 H12 H13 Hsp Hsp' W Htmp Htmp' Hcbc Hcbs Hk Ck.
eexists. split.
{ zstep (ltac:(oF' 0x5408c%Z)) (ltac:(oD' 0x5408c%Z)).
zsd (ltac:(oF' 0x54090%Z)) (ltac:(oD' 0x54090%Z)) (sp - 8) (U raw) ltac:(rewok W). zsd (ltac:(oF' 0x54094%Z)) (ltac:(oD' 0x54094%Z)) (sp - 16) (U (getr regs 8)) ltac:(rewok W).
zsd (ltac:(oF' 0x54098%Z)) (ltac:(oD' 0x54098%Z)) (sp - 24) (U (getr regs 9)) ltac:(rewok W). zsd (ltac:(oF' 0x5409c%Z)) (ltac:(oD' 0x5409c%Z)) (sp - 32) (U (getr regs 18)) ltac:(rewok W).
zsd (ltac:(oF' 0x540a0%Z)) (ltac:(oD' 0x540a0%Z)) (sp - 40) (U (getr regs 19)) ltac:(rewok W). zsd (ltac:(oF' 0x540a4%Z)) (ltac:(oD' 0x540a4%Z)) (sp - 48) (U (getr regs 20)) ltac:(rewok W).
zsd (ltac:(oF' 0x540a8%Z)) (ltac:(oD' 0x540a8%Z)) (sp - 56) (U (getr regs 21)) ltac:(rewok W). zsd (ltac:(oF' 0x540ac%Z)) (ltac:(oD' 0x540ac%Z)) (sp - 64) (U (getr regs 22)) ltac:(rewok W).
zsd (ltac:(oF' 0x540b0%Z)) (ltac:(oD' 0x540b0%Z)) (sp - 72) (U (getr regs 23)) ltac:(rewok W). zsd (ltac:(oF' 0x540b4%Z)) (ltac:(oD' 0x540b4%Z)) (sp - 80) (U (getr regs 24)) ltac:(rewok W).
zsd (ltac:(oF' 0x540b8%Z)) (ltac:(oD' 0x540b8%Z)) (sp - 88) (U (getr regs 25)) ltac:(rewok W).
match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Ck' : cellA X tmp 8 k) by zcell end.
zld (ltac:(oF' 0x540bc%Z)) (ltac:(oD' 0x540bc%Z)) tmp Ck'.
zsd (ltac:(oF' 0x540c0%Z)) (ltac:(oD' 0x540c0%Z)) (sp - 104) cbc ltac:(rewok W). zsd (ltac:(oF' 0x540c4%Z)) (ltac:(oD' 0x540c4%Z)) (sp - 96) cbs ltac:(rewok W).
zbft (ltac:(oF' 0x540c8%Z)) (ltac:(oD' 0x540c8%Z)).
zstep (ltac:(oF' 0x540cc%Z)) (ltac:(oD' 0x540cc%Z)).
stepn (ltac:(oF' 0x540d0%Z)) (ltac:(oD' 0x540d0%Z)). zstep (ltac:(oF' 0x540d4%Z)) (ltac:(oD' 0x540d4%Z)). stepn (ltac:(oF' 0x540d8%Z)) (ltac:(oD' 0x540d8%Z)). zcl4.
zstep (ltac:(oF' 0x540dc%Z)) (ltac:(oD' 0x540dc%Z)). zstep (ltac:(oF' 0x540e0%Z)) (ltac:(oD' 0x540e0%Z)). zstep (ltac:(oF' 0x540e4%Z)) (ltac:(oD' 0x540e4%Z)).
stepn (ltac:(oF' 0x540e8%Z)) (ltac:(oD' 0x540e8%Z)).
unfold art_f112. apply mst_refl. }
split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; f_equal; lia|]. split; [gres; f_equal; lia|].
split; [gres; f_equal; lia|]. split; [gres; reflexivity|].
intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]). destruct Hr.
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_art_dr_pop := (ltac2:(TCodec.tc2 tcn__JbtRecycle5B "W;&:y5'R0yR0%211%5241'2y8%611%311p061'9'7&Dr:(QN+8(5%33A21%6251&QOr7%22C1%;3C41r;+:%;3I19%>231%@3H16&J+Vb\P0r9%3221&K&I+Q0%22F1&M+2+R0%3221%8251+XP0%92M1%;214&=r=%241<G5'6+1%E214%B25;%4221zr<%J221%G22@%9221%M294%F2EH%K261%=231&?&GrErC%44321O&>rFrD%Q421QFu8rB%65:5321rG%85<1:43rH%:5>1765rI+H%Q>261%>5B31:9rJ+@%QB2@1%B5F31>='8'@&EvQ5rN+Z`X4%R=3RI1R;/01RIrMrL%8576321r2+Z`Z4%RD3S01RB/01S0r1%>5=5217%@3Q871+D%RJ3S81RH%RM291%RG2S8M%S03S821+F%RO3S=1RM%S22>1%RL2S=Q@%S53S=21+G%S43SB1S2%S72C1+TH%RD2Q81%S32SD1%S<3SD41%S:3SHQ:S8%S=2I1%RI2QKQ8%S82SI1%SA3SI31+I%S@3SN1S>%SC2O1%S=2SNQ>%SF3SN21%T11T2&H(0%SG3T5RESE%SH3T6S1SF+3%SJ3T81SH+4%SL3T:1SJ+9%SN3T<1SL+B%T03T>1SN+C%T23T@1T0+E%T43TB1T2+J%T63TD1T4+K%T83TF1T6(1%11F%E3G31%F3H61%G3I91%H3J<1%I3K?1%J3LB1%K3MT>1%L3NF1%M3OI1%N3Q0L1%O3Q1N1%Q13Q2R01r4%TJ21R6rQ0%TL21R8%TN3U631p061pS<Q91&F%12R@R9&B'4%12U6U6(3rK%24U9U91TA%M14%QA3521%831RIRB&N%12S7T8%SG5SKRE7SC1%TI28U;%SI5SMRG1SES@%TK2:S>%62SJSD%SL5T0RJ2SH1%T@241%TA271%TB2;1%TC2E1%TD2H1%TE2R31%TF2R91%TG2R?1%TH2RG1%TI2RM1%TJ2S31qJV11%SF2V21qSBV81%SH2V91p0SJ1p0SO1p0T41p0T71p0T:1p0TB1p0TH1p0TM1p0TN1p0TO1p0U51p0U;1p0U?1p0UL1p0UD1p0UN1p0V31p0V91pS:VF1pR2VG1pSFVH1pS8VI1pR0VJ1pS4VK1pT8VL1pSDVN1pHVO1pS@W51")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_dr_pop) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_dr_pop) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_dr_pop) 2%nat 0%nat).
Variable tmp : ltac:(sec_ty2 constr:(SEC_T_art_dr_pop) 3%nat 0%nat).
Variable k : ltac:(sec_ty2 constr:(SEC_T_art_dr_pop) 4%nat 0%nat).
Variable b : ltac:(sec_ty2 constr:(SEC_T_art_dr_pop) 5%nat 0%nat).
Variable next : ltac:(sec_ty2 constr:(SEC_T_art_dr_pop) 6%nat 0%nat).
Variable size : ltac:(sec_ty2 constr:(SEC_T_art_dr_pop) 7%nat 0%nat).
Variable bytes : ltac:(sec_ty2 constr:(SEC_T_art_dr_pop) 8%nat 0%nat).
Variable ni : ltac:(sec_ty2 constr:(SEC_T_art_dr_pop) 9%nat 0%nat).
Lemma art_dr_pop : ltac:(sec_stmt2 constr:(SEC_T_art_dr_pop) 10%nat 0%nat).
Proof using Type regs M rom tmp k b next size bytes ni.
intros H8 H10 Htmp Htmp' Hb Hb' Ap Hk Hnext Hsize Hbytes Hni W Cb Cnext Csize Cbytes Cni.
unfold apart in Ap.
destruct (Z.eq_dec next 0) as [E0|NE0].
- eexists. eexists. split.
{ zld (ltac:(oF' 0x54104%Z)) (ltac:(oD' 0x54104%Z)) (tmp + 8) Cb.
zld (ltac:(oF' 0x54108%Z)) (ltac:(oD' 0x54108%Z)) b Cnext.
zsd (ltac:(oF' 0x5410c%Z)) (ltac:(oD' 0x5410c%Z)) (tmp + 8) next ltac:(rewok W).
zbft (ltac:(oF' 0x54110%Z)) (ltac:(oD' 0x54110%Z)).
zsd (ltac:(oF' 0x54114%Z)) (ltac:(oD' 0x54114%Z)) (tmp + 16) 0 ltac:(rewok W).
zstep (ltac:(oF' 0x54118%Z)) (ltac:(oD' 0x54118%Z)).
zsd (ltac:(oF' 0x5411c%Z)) (ltac:(oD' 0x5411c%Z)) tmp (k + -1) ltac:(rewok W).
match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Csize' : cellA X (b + 8) 8 size) by zcell; assert (Cbytes' : cellA X (tmp + 24) 8 bytes) by zcell;
assert (Cni' : cellA X (b + 16) 8 ni) by zcell end.
zld (ltac:(oF' 0x54120%Z)) (ltac:(oD' 0x54120%Z)) (b + 8) Csize'.
zld (ltac:(oF' 0x54124%Z)) (ltac:(oD' 0x54124%Z)) (tmp + 24) Cbytes'.
zstep (ltac:(oF' 0x54128%Z)) (ltac:(oD' 0x54128%Z)).
zsd (ltac:(oF' 0x5412c%Z)) (ltac:(oD' 0x5412c%Z)) (tmp + 24) (bytes - size) ltac:(rewok W).
match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cni'' : cellA X (b + 16) 8 ni) by zcell end.
zld (ltac:(oF' 0x54130%Z)) (ltac:(oD' 0x54130%Z)) (b + 16) Cni''.
zbft (ltac:(oF' 0x54134%Z)) (ltac:(oD' 0x54134%Z)).
zstep (ltac:(oF' 0x54138%Z)) (ltac:(oD' 0x54138%Z)). zstep (ltac:(oF' 0x5413c%Z)) (ltac:(oD' 0x5413c%Z)). zstep (ltac:(oF' 0x54140%Z)) (ltac:(oD' 0x54140%Z)).
apply mst_refl. }
split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|].
split. { intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]). destruct Hr. }
split; [zgrows|]. split; [eapply art_agree_sub; [zagree|]; zsub|].
split; [replace (k - 1) with (k + -1) by lia; zcell|]. split; [zcell|zcell].
- eexists. eexists. split.
{ zld (ltac:(oF' 0x54104%Z)) (ltac:(oD' 0x54104%Z)) (tmp + 8) Cb.
zld (ltac:(oF' 0x54108%Z)) (ltac:(oD' 0x54108%Z)) b Cnext.
zsd (ltac:(oF' 0x5410c%Z)) (ltac:(oD' 0x5410c%Z)) (tmp + 8) next ltac:(rewok W).
zbtk (ltac:(oF' 0x54110%Z)) (ltac:(oD' 0x54110%Z)).
zstep (ltac:(oF' 0x54118%Z)) (ltac:(oD' 0x54118%Z)).
zsd (ltac:(oF' 0x5411c%Z)) (ltac:(oD' 0x5411c%Z)) tmp (k + -1) ltac:(rewok W).
match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Csize' : cellA X (b + 8) 8 size) by zcell; assert (Cbytes' : cellA X (tmp + 24) 8 bytes) by zcell;
assert (Cni' : cellA X (b + 16) 8 ni) by zcell end.
zld (ltac:(oF' 0x54120%Z)) (ltac:(oD' 0x54120%Z)) (b + 8) Csize'.
zld (ltac:(oF' 0x54124%Z)) (ltac:(oD' 0x54124%Z)) (tmp + 24) Cbytes'.
zstep (ltac:(oF' 0x54128%Z)) (ltac:(oD' 0x54128%Z)).
zsd (ltac:(oF' 0x5412c%Z)) (ltac:(oD' 0x5412c%Z)) (tmp + 24) (bytes - size) ltac:(rewok W).
match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cni'' : cellA X (b + 16) 8 ni) by zcell end.
zld (ltac:(oF' 0x54130%Z)) (ltac:(oD' 0x54130%Z)) (b + 16) Cni''.
zbft (ltac:(oF' 0x54134%Z)) (ltac:(oD' 0x54134%Z)).
zstep (ltac:(oF' 0x54138%Z)) (ltac:(oD' 0x54138%Z)). zstep (ltac:(oF' 0x5413c%Z)) (ltac:(oD' 0x5413c%Z)). zstep (ltac:(oF' 0x54140%Z)) (ltac:(oD' 0x54140%Z)).
apply mst_refl. }
split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|].
split. { intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]). destruct Hr. }
split; [zgrows|]. split; [eapply art_agree_sub; [zagree|]; zsub|].
split; [replace (k - 1) with (k + -1) by lia; zcell|]. split; [zcell|zcell].
Qed.
End SE.
#[using="Type"] Lemma art_dr_item_call : ltac2:(TCodec.tc2 tcn__JbtRecycle5B "UE&:y5'R0yR0%211%5241'2y8%611%311p061'9'7&Dr7(QN+2(5%33A21%6251&QOr4%22C1%;3C41r8+G%;3I19%>231&I+TH%2291&L+8r3%3221%7251%@2Q11%I3Q1:1&Jzr6%3221&K%?2M;&M+R0%22N1%5241+Vb\P0%;21Q3+XP0%G2K1%:216'6%@2?N+oM%>2Q01%4231%@2Q2<%6251&>&Gr>r;+H%Q5221r:%Q42Q31%Q8231u8r9%;5:9321'8'@&EvQ5rA+Z`Z4%QO3R;1QM/01R;r@r?%8576321r1+Z`^4%R63RB1R4/01RB%=5<4176%?3K61+1%R;3RI1R9%R>281+Z`Z@%R>3RJ1R</01RJ%RC3RK41+:%RB3S01R@%RE2?1%R72Q5R3%R@2S11%RI3S131+;%RH3S61RF%RK2E1%RE2S6Q:%RN3S621%S91S:&H(0+3%S03S>1RN+4%S23S@1S0%S33SARBS1+9%S53SC1S3+B%S73SE1S5+C%S93SG1S7+D%S;3SI1S9+E%S=3SK1S;+F%S?3SM1S=%S@3SNQOS>+I%SB3T01S@+J%SD3T21SB+K%SF3T41SD(1%11L%K3M31%L3N61%M3O91%N3Q0<1%O3Q1SB1%Q03Q2?1%Q13Q3B1%Q23Q4E1%Q33Q5H1%Q43Q6K1%Q53Q7N1%Q63Q8Q11%Q73Q9Q31%Q83Q:Q61%Q93Q;T41%Q;3Q<R41r2%T<2SH1rC%T>213%T@3TH31p061pS<QC1%S:2QE1%S;2QK1%S<2R21%S=2R:1qSBTN1%RL2TO1p0RN1p0S;1p0S>1p0SD1p0SH1p0SK1p0T21p0T71p0TF1pS6U31pS2U41pR0U51pSJU61pSDU81pHU91pS@U?1").
Proof.
intros regs M rom sp1 b j m H2 H23 Hsp Hsp' Hb Hb' Hj Hm Cm.
eexists. split.
{ zld (ltac:(oF' 0x54144%Z)) (ltac:(oD' 0x54144%Z)) (b + 24 + 8 * j) Cm.
zstep (ltac:(oF' 0x54148%Z)) (ltac:(oD' 0x54148%Z)).
stepn (ltac:(oF' 0x5414c%Z)) (ltac:(oD' 0x5414c%Z)).
apply mst_refl. }
split; [gres; bveq|]. split; [gres; reflexivity|]. split; [gres; reflexivity|].
intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]). destruct Hr.
Qed.
Section SE.
Local Abbreviation SEC_T_art_dr_item_more := (ltac2:(TCodec.tc2 tcn__JbtRecycle5B "U9&:y5'R0yR0%211%5241'2y8%611%311p061'9'7&Dr6(QN+G(5%33A21%6251&QO&Ir3+TH%3221&L+8r2%3221%8251%:2K1%C3K<1r7+H%C3Q11A%F231+@%@2:1%B2Q31%K3Q341r8+I%K3Q91I%N231r4%H291%J2Q;1%Q33Q;41&Jzr5%3221&K+1%Q12Q81%3215&M+2+Q0%3221%82Q>1r9%>2=1r:+XP0%Q<221+R0%;2:1%@231'8'6'@&G&EvQ5r?+Z`Z@%QN3R:1QL/01R:r>r=%8576321r1+Z`Z4%R53RA1R3/01RA%=5<4176%@3?61%R;26R6r<%R521R3r;%R721Q7%R42R31%R9241%R;2RL1%RD3RL81%RD2?QG%R=2QN6%R?2S01%RH3S031%S31S4&H(0%RI3S7QCRG%RJ3S8Q@RH+3%RL3S:1RJ+4%RN3S<1RL%RO3S=RDRM+9%S13S?1RO+B%S33SA1S1+C%S53SC1S3+D%S73SE1S5+E%S93SG1S7+F%S;3SI1S9+J%S=3SK1S;+K%S?3SM1S=(1%11K%J3L31%K3M61%L3NS11%M3O:1%N3Q0=1%O3Q1@1%Q03Q2C1%Q13Q3F1%Q23Q4I1%Q33Q5L1%Q43Q6N1%Q53Q7Q11%Q63Q8Q41%Q73Q9Q61%Q93Q:QM1%T32SJSErA%T521SG%T73T?31p051pS<Q@1%R@2QB1%RA2QG1%RB2R11qSBTD1%RE2TE1p0RG1p0RN1p0S11p0S71p0S<1p0SA1p0SJ1p0T31pS:TH1pS2TI1pR0TJ1pSDTL1pHTM1pS@U31")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_dr_item_more) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_dr_item_more) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_dr_item_more) 2%nat 0%nat).
Variable b : ltac:(sec_ty2 constr:(SEC_T_art_dr_item_more) 3%nat 0%nat).
Variable j : ltac:(sec_ty2 constr:(SEC_T_art_dr_item_more) 4%nat 0%nat).
Variable ni : ltac:(sec_ty2 constr:(SEC_T_art_dr_item_more) 5%nat 0%nat).
Lemma art_dr_item_more : ltac:(sec_stmt2 constr:(SEC_T_art_dr_item_more) 6%nat 0%nat).
Proof using Type regs M rom b j ni.
intros H23 H24 H25 Hj Hjn Hni Hb Hb'.
eexists. split.
{ zstep (ltac:(oF' 0x54150%Z)) (ltac:(oD' 0x54150%Z)). zstep (ltac:(oF' 0x54154%Z)) (ltac:(oD' 0x54154%Z)).
zbtk (ltac:(oF' 0x54158%Z)) (ltac:(oD' 0x54158%Z)).
apply mst_refl. }
split; [gres; f_equal; lia|]. split; [gres; f_equal; lia|].
intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]). destruct Hr.
Qed.
End SE.
#[using="Type"] Lemma art_dr_item_last : ltac2:(TCodec.tc2 tcn__JbtRecycle5B "TJ&:y5'R0yR0%211%5241'2y8%611%311p061'9'7&Dr6(QN+G(5%33A21%6251&QO&Ir3+TH%3221&L+8r2%3221%8251%:2K1%C3K<1r7+H%C3Q11A%F231+@%@2:1%B2Q31%K3Q341r8+I%K3Q91I%N231r4%H291%J2Q;1%Q33Q;41&Jzr5%3221+1%Q02Q71%Q:3Q;14&K&M+2+Q0%3221%52Q>1r9%>2=1r:+XP0%Q<221+R0%;2:1%=231'8'6'@&G&EvQ5r?+Z`Z@%QN3R:1QL/01R:r>r=%8576321r1+Z`ZL%R53RA1R3/01RA%=5<4176%@3?61%RF1RG&H(0%R<3RJQ7R:%R=3RKQ3R;+3%R?3RM1R=+4%RA3RO1R?%RB3S0R7R@+9%RD3S21RB+B%RF3S41RD+C%RH3S61RF+D%RJ3S81RH+E%RL3S:1RJ+F%RN3S<1RL+J%S03S>1RN+K%S23S@1S0(1%11K%J3L31%K3M61%L3NRD1%M3O:1%N3Q0=1%O3Q1@1%Q03Q2C1%Q13Q3F1%Q23Q4I1%Q33Q5L1%Q43Q6N1%Q53Q7Q11%Q63Q8Q41%Q73Q9Q61%Q93Q:Q@1%SF2S=S8rA%SH21S:%SJ3T231p051pS<Q@1%R32QB1qSBT51%R62T61p0R81p0R?1p0RB1p0RI1p0RM1p0S21p0S;1p0SD1pS:T91pS2T:1pR0T;1pSDT=1pHT>1pS@TD1").
Proof.
intros regs M rom b j ni H23 H24 H25 Hj Hjn Hni Hb Hb'.
eexists. split.
{ zstep (ltac:(oF' 0x54150%Z)) (ltac:(oD' 0x54150%Z)). zstep (ltac:(oF' 0x54154%Z)) (ltac:(oD' 0x54154%Z)).
zbft (ltac:(oF' 0x54158%Z)) (ltac:(oD' 0x54158%Z)).
apply mst_refl. }
intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]). destruct Hr.
Qed.
Section SE.
Local Abbreviation SEC_T_art_dr_bd_call := (ltac2:(TCodec.tc2 tcn__JbtRecycle5B "VH&:y5'R0yR0%211%5241'2y8%611%311p061'9&Ir4&Lr3&M+2+Q0%3221%6251%9281r2%;221'7&Dr9(QN(5%23L<1%5241&QOr6%22N1%:3N41r:+9%:3Q419%=231+QWTnH%92Q51%A3Q531r;+D%A3Q;1@%D231%?2Q;O%G3Q;21r<+E%G3QA1F%J231+Q5%Q52Q41%G2QC1%O3QC41&Jz%221G&K+@%QA2C1+R0%Q?2Q>1%5231+Vb\P0%:21H%QG2C>+Q?%QE2QD1%;231'6+1%A21I+N%C2K1%5231%E2DM%C2NQK%8221%E2Q0A%:241&>&GrC%R92Q>R3u8r@%6554321rDrB+8%R@221r>%<5;5281'8'@&EvQ5rG+Z`ZL%R:3S21R9/01S2rFrE%8576321r1+Za^8%RA3S91R@/01S9%=5<4176%?3L61%RE3S?Q8RD%RH271+Z`\8%RH3S@1RG/01S@%RM3SA41+:%RL3SF1RK%RO2>1%RJ2SFQ2%S23SF21+;%S13SK1S0%S42C1%S63SJ1RF+<%S53SO1S4%S82G1%S32SOQ8%S;3SO21+=%S:3T41S9%S=2L1r?%S92T51%SA3T531%T81T9&H(0+3%SC3T=1SB+4%SE3T?1SD%SF3T@QFSE+B%SH3TB1SG+C%SJ3TD1SI+F%SL3TF1SK+G%SN3TH1SM+H%T03TJ1SO+I%T23TL1T1+J%T43TN1T3+K%T63U01T5(1%11I%H3J31%I3K61%J3L91%K3M<1%L3N?1%M3OB1%N3Q0SH1%O3Q1SO1%Q03Q2G1%Q13Q3J1%Q23Q4T91%Q33Q5N1%Q43Q6Q01%Q53Q7Q31%Q63Q8TE1%Q83Q9R91%TK2U5TNrI%TM21U0%TO3UC31p051pS<Q?1%SC2QA1%SD2QH1%SE2QN1%SF2R31%SG2R91%SH2R@1qSBUK1%S22UL1p0S41p0S;1p0SC1p0SF1p0SJ1p0T11p0T61p0T91p0T@1p0TD1p0TM1p0U41p0U<1tR0V4UH1pR6V51pT6V61pR4V71pSLV81pSJV91pSDV;1pHV<1pS@VB1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_dr_bd_call) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_dr_bd_call) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_dr_bd_call) 2%nat 0%nat).
Variable sp1 : ltac:(sec_ty2 constr:(SEC_T_art_dr_bd_call) 3%nat 0%nat).
Variable spb : ltac:(sec_ty2 constr:(SEC_T_art_dr_bd_call) 4%nat 0%nat).
Variable c : ltac:(sec_ty2 constr:(SEC_T_art_dr_bd_call) 5%nat 0%nat).
Variable szi : ltac:(sec_ty2 constr:(SEC_T_art_dr_bd_call) 6%nat 0%nat).
Variable cache : ltac:(sec_ty2 constr:(SEC_T_art_dr_bd_call) 7%nat 0%nat).
Lemma art_dr_bd_call : ltac:(sec_stmt2 constr:(SEC_T_art_dr_bd_call) 8%nat 0%nat).
Proof using Type regs M rom sp1 spb c szi cache.
intros b H2 H9 H20 H21 Hsp Hsp' Hspb Hspb' Hc Hszi Hcache Cspb Ccache.
assert (Hb : b = spb + c * 2 ^ 32 + szi) by reflexivity. clearbody b.
assert (Ec : (b - spb) * 2 ^ 27 / 2 ^ 59 = c).
{ symmetry. apply (Z.div_unique_pos ((b - spb) * 2 ^ 27) (2 ^ 59) c (szi * 2 ^ 27)); lia. }
eexists. split.
{ zld (ltac:(oF' 0x5415c%Z)) (ltac:(oD' 0x5415c%Z)) (1283032 + 32) Cspb.
zbft (ltac:(oF' 0x54160%Z)) (ltac:(oD' 0x54160%Z)).
zstep (ltac:(oF' 0x54164%Z)) (ltac:(oD' 0x54164%Z)).
zbft (ltac:(oF' 0x54168%Z)) (ltac:(oD' 0x54168%Z)).
zld (ltac:(oF' 0x5416c%Z)) (ltac:(oD' 0x5416c%Z)) (sp1 + 8) Ccache.
zstep (ltac:(oF' 0x54170%Z)) (ltac:(oD' 0x54170%Z)). zstep (ltac:(oF' 0x54174%Z)) (ltac:(oD' 0x54174%Z)).
stepn (ltac:(oF' 0x54178%Z)) (ltac:(oD' 0x54178%Z)). rwH. rewrite (art_zb_srli ((b - spb) * 2 ^ 27) 59) by lia. rewrite Ec.
zstep (ltac:(oF' 0x5417c%Z)) (ltac:(oD' 0x5417c%Z)). zstep (ltac:(oF' 0x54180%Z)) (ltac:(oD' 0x54180%Z)).
stepn (ltac:(oF' 0x54184%Z)) (ltac:(oD' 0x54184%Z)).
apply mst_refl. }
split; [gres; bveq|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|].
intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]). destruct Hr.
Qed.
End SE.
#[using="Type"] Lemma art_dr_next_more : ltac2:(TCodec.tc2 tcn__JbtRecycle5B "T=&:y5'R0yR0%211%5241'2y8%611%311p061'9'7&Dr5(QN+8(5%33A21%6251&QOr2%22C1%;3C41&Jzr3%3221&K&Ir4%221?&M+2+R0%3221%8251'6+1%?219%<2:5%4221&>&Gr8r6u8%554321Q1'8'@&EvQ5r;+Z`\8%Q73QC1Q5/01QCr:r9%8576321r1+Z`X4%Q>3QJ1Q</01QJ%=5<4176%?3E61+:%QC3R11QA%QF281r7%QA2R21%QJ3R231%R51R6&H(0%QK3R9Q4QI%QL3R:Q:QJ+3%QN3R<1QL+4%R03R>1QN+9%R23R@1R0+B%R43RB1R2+C%R63RD1R4+D%R83RF1R6+E%R:3RH1R8+F%R<3RJ1R:+G%R>3RL1R<+H%R@3RN1R>+I%RB3S01R@+J%RD3S21RB+K%RF3S41RD(1%11Q0%O3Q131%Q03Q261%Q13Q391%Q23Q4<1%Q33Q5?1%Q43Q6B1%Q53Q7E1%Q63Q8H1%Q73Q9K1%Q83Q:N1%Q93Q;Q11%Q:3Q<S11%Q;3Q=Q51%Q<3Q>Q81%Q=3Q?Q;1%Q>3Q@Q=1%Q@3QAQM1%S<2ROS4r=%S>21S6%S@3SH31p051pS<QG1%RJ2QI1%RK2R01qSBSL1%RB2SM1p0RD1p0RK1p0S11p0S;1p0S@1pS4SM1pT8SN1pSDT01pHT11pS@T71").
Proof.
intros regs M rom tmp k H8 Htmp Htmp' Hk Ck.
eexists. split.
{ zld (ltac:(oF' 0x54188%Z)) (ltac:(oD' 0x54188%Z)) tmp Ck.
zbtk (ltac:(oF' 0x5418c%Z)) (ltac:(oD' 0x5418c%Z)).
apply mst_refl. }
split; [gres; reflexivity|].
intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]). destruct Hr.
Qed.
#[using="Type"] Lemma art_dr_next_done : ltac2:(TCodec.tc2 tcn__JbtRecycle5B "WA&:y5'R0yR0%211%5241'2y8%611%311p061'9'7&Dr@(QN+2(5%33A21%6251&QO&Nr<+S@%3221%52F1%>3F71rA+8%>3L1<%A231%;2L9%D3L21&Ar?%211&J%12>3&K&M+R0%22I1%42L1z%821N&I%12CB%9216&>&GrFrBu8%554321:rGrD%Q321L&R1rE%22QH1%<5;6481rH+@%Q:251rC%A5@42=1rI+H%Q?2B1%E5D31A5rJ+Q0%QC2B1%I5H31E9rK+Q8%QG2?1%M5L31I=rL+Q@%QK2>1%Q15Q031MArM+QH%QO2>1%Q55Q431Q1ErN%R22=Q?%Q85Q721Q4HrO+R8%R62=1%Q<5Q;31Q8LrQ0+R@%R:2=1%Q@5Q?31Q<Q0rQ1+RH%R>2=1%QD5QC31Q@Q4'8'6'@&EvQ5rQ4+Z`\8%RM3S91RK/01S9rQ3rQ2%8576321r1%:591A43%<3R231%S723S2%S12SBH%S:3SB21%S:26RJ%S42SEQ2%S=3SE21+9%S<3SJ1S:%S?2;1%S92SJQ;%SB3SJ21+B%SA3SO1S?%SD2@1%S>2SOQD%SG3SO21+C%SF3T41SD%SI2E1%SC2T4QM%SL3T421+D%SK3T91SI%SN2J1%SH2T9R6%T13T921+E%T03T>1SN%T32O1%SM2T>R?%T63T>21+F%T53TC1T3%T82Q41%T22TCRI%T;3TC21+G%T:3TH1T8%T=2Q91%T72THS5%T@3TH21%T>3TLRJT<%TA2Q=1%T;2TLS=%TD3TL21+I%TC3U11TA%TF2QB1%T@2U1S:%TI3U121%U41U5&H(0+3%TK3U91TI+4%TM3U;1TK+J%TO3U=1TM+K%U13U?1TO(1%11<%;3=31%<3>61%=3?91%>3@<1%@3AR61r3r2%U=221rQ6%U?213%UA3UI31p071pS<I1%RJ2K1%RK2Q11%RL2Q61%RM2Q<1%RN2QB1%RO2QH1%S02QN1%S12R41%S22R:1%S32R@1%S42RD1%S52RH1qSBV71%S82V81p0S:1p0S?1p0SD1p0SI1p0SM1p0T21p0T71p0T<1p0TA1p0TF1p0TL1p0U41p0U;1p0U?1p0UB1p0UH1p0UK1p0UO1p0V61pRLVF1pRJVG1pRHVH1pRFVI1pRDVJ1pRBVK1pR@VL1pR>VM1pS0VN1pRNVO1pT8W01pSHW11pS>W91pSDW41pHW51pS@W;1").
Proof.
intros regs M rom raw sp tmp g8 g9 g18 g19 g20 g21 g22 g23 g24 g25 H2 H8 Hret Hsp Hsp' Htmp Htmp' Ck F1 F8 F9 F18 F19 F20 F21 F22 F23 F24 F25.
eexists. split.
{ zld (ltac:(oF' 0x54188%Z)) (ltac:(oD' 0x54188%Z)) tmp Ck.
zbft (ltac:(oF' 0x5418c%Z)) (ltac:(oD' 0x5418c%Z)).
zld (ltac:(oF' 0x54190%Z)) (ltac:(oD' 0x54190%Z)) (sp - 8) F1. rewrite Z_to_bv_bv_unsigned.
zld (ltac:(oF' 0x54194%Z)) (ltac:(oD' 0x54194%Z)) (sp - 16) F8. zld (ltac:(oF' 0x54198%Z)) (ltac:(oD' 0x54198%Z)) (sp - 24) F9. zld (ltac:(oF' 0x5419c%Z)) (ltac:(oD' 0x5419c%Z)) (sp - 32) F18. zld (ltac:(oF' 0x541a0%Z)) (ltac:(oD' 0x541a0%Z)) (sp - 40) F19. zld (ltac:(oF' 0x541a4%Z)) (ltac:(oD' 0x541a4%Z)) (sp - 48) F20.
zld (ltac:(oF' 0x541a8%Z)) (ltac:(oD' 0x541a8%Z)) (sp - 56) F21. zld (ltac:(oF' 0x541ac%Z)) (ltac:(oD' 0x541ac%Z)) (sp - 64) F22. zld (ltac:(oF' 0x541b0%Z)) (ltac:(oD' 0x541b0%Z)) (sp - 72) F23. zld (ltac:(oF' 0x541b4%Z)) (ltac:(oD' 0x541b4%Z)) (sp - 80) F24. zld (ltac:(oF' 0x541b8%Z)) (ltac:(oD' 0x541b8%Z)) (sp - 88) F25.
zstep (ltac:(oF' 0x541bc%Z)) (ltac:(oD' 0x541bc%Z)).
stepret (ltac:(oF' 0x541c0%Z)) (ltac:(oD' 0x541c0%Z)) raw ltac:(reflexivity).
apply mst_refl. }
split; [gres; f_equal; lia|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|].
split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|].
intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]). destruct Hr.
Qed.
End FPX.
