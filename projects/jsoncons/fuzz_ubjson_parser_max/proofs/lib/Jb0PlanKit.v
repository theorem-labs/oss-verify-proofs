(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3
AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegRunStrlen Jb0Sums Jb0SumsStrlen SegPlan.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__Jb0PlanKit () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Init.Peano."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.MemImageType."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanPlanSound.APS."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AxSymExec3.AX2."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AxSymExec3Sound.AX2S."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AxSymRun3."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Jb0PlanKit."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.LibSym."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SegPlan.SGP."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SegRun.SR."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.StoreOk."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0BFUEL"; "0BR"; "1None"; "1O"; "1Some"; "1bool"; "1false"; "1list"; "1nat"; "1option"; "1pair"; "1prod"; "1true"; "2and"; "2eq"; "2ex"]; ["3lt"; "4Z"; "0E"; "0E'"; "0F"; "0K"; "5Segment"; "6find_segment"; "7bvmap"; "0M"; "0M'"; "0M0"; "0PSS"; "0R"; "0R'"; "8hull_ok"]; ["8in_hull"; "9edenot"; "9env"; "9expr"; "9kentry"; "9sym_state"; ":kentry_ok"; ":know_ok"; ":regs_ok"; ";env_agree"; "<msteps"; "=A0"; "=RO_HI"; "=RO_LO"; "=X_CPY"; "=X_LEN"]; ["=X_SET"; ">itab_of"; "?FPState"; "?getr"; "?mkst"; "?seg_rom"; "@XSTEP2_ok"; "@XSTEP_ok"; "@bfact"; "@bfacts_ok"; "@cert_ok"; "@outside"; "@region"; "@regions_ok"; "@splan"; "@xstep2_none"]; ["Apost_spec"; "Aps_cells"; "Aps_pc"; "Aps_regs"; "Bmem_grows"; "Cloaded_segments"; "DIn"; "Dnth_error"; "Eof_nat"; "0XSTEP"; "0XSTEP2"; "0a"; "0e"; "0fx"; "0fx'"; "0i"]; ["0itr"; "0kn0"; "0nx0"; "0p"; "0pc0"; "0ps"; "0sr0"; "FZ_to_bv"; "Fbv"; "Fbv_unsigned"]]).
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition X_CPY : Z := 0x1267e4. Definition X_SET : Z := 0x126be8. Definition X_LEN : Z := 0x1270cc.
Definition RO_LO : Z := 0x10390. Definition RO_HI : Z := 0x103b0.
Definition A0 : APC.atable := APC.AT 0x10000 0x693000 0%nat 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 [].
Lemma as0_in_hull : ltac2:(TCodec.tc2 tcn__Jb0PlanKit "K'RHyR0%211'>'5&Q0&Q;&RIr1%2281%5241(6%93821'9'F%211&G&R5r2%<2B1+1%53421(2%119%E3931p0=1pTHH1").
Proof. apply SGP.in_hull_of_b. vm_compute. reflexivity. Qed.
Lemma as0_hull_ok : ltac2:(TCodec.tc2 tcn__Jb0PlanKit "3&O&Q;%211").
Proof. unfold APS.hull_ok. cbn [APC.img_lo APC.img_hi A0]. unfold APC.KHI. repeat split; reflexivity || lia. Qed.
Theorem as0_plan_sound2 : ltac2:(TCodec.tc2 tcn__Jb0PlanKit "V6'7';'A'8%3221%511'QH%711&QL%911'Q5'9%112p031p0;1p061%?266%611p081p0@1p0;1'R0%F11'QN'Q3%I11'Q4%K11'>'5&QJ&R5&QAr<%2231&Q>&Q@&Q?&Q=&Q<r;&Q;r:r9r8r7r6r5r4r3r2r1%FCEBA@?>=<;:987654321(<%J3I21'RHyR0%211y8%411%QA11p041&QG%16Q0NGEC<pQH31&QFr=%26Q41Q2IH@pQH71'QB'Q2&Hy5%221@&Q8%13JQ0I&Q7%14Q>MKQ2&QIrB%221Q1'?'=%R81QN&R7rE%23R11Q4(4%12R3Q5%QM3631&Q9rJ%231QKQ='Q:&QD&RGrC%22Q91&QE%11R4%65Q2QL3QJ1&R2%11QC%82Q?1%:5QJQH1QG5%<3R:51&R6%S:2S8RC(:%14S:REQKQJ&R3%11QN%63531&@(3%221R2uQ0%42R41%Q4231&QC&R8%11R8%K2QB1%42R>1&Q1%12RAR;%S23R531%Q=291p0@1pTJS91pU0SO1z%Q52QL1%>2RE1%Q72R>3%S;3R>21&QMrF%22RK1&QKrG%23RO1RJ%RO1RL%S>1RM%SD3RD21p041pTHRI1&R1%11S2%Q;3SKS21&Q6%14SHS:S8S5p031pQ<SO1&R4%12SAS:%R:231%R;2;1%R<2D1%R=2H1%R>2N1%R?2QH1%R@2R61%RA2R:1qU<T?1%RD2T@1qU0U31%RF2U41qQFS;1%RH2S<1qQNS11%RJ2S21qQ8S61%RL2S71qTNS91%RN2S:1p0S01p0S41p0S71pQDSF1pQLS;1pQ6S?1pTLSA1p0SC1p0SH1p0T31pU4TO1pU>U21pU:UJ1pU8U61pQJU81pQ:UF1pTFU<1pTDUB1p4UK1pU6V01p2V11pU2V01").
Proof.
intros itr BFUEL nx0 BR XSTEP XSTEP2 F PSS p pc0 sr0 kn0 Hc HXS HXS2 fx E R M HR HK HBF.
exact (SGP.plan_entry_sound RSEGS (itab_of RSEGS itr) X_CPY X_SET X_LEN RO_LO RO_HI BFUEL A0 nx0 BR XSTEP XSTEP2
(itab_of_sound _ _) as0_copy_spec_memcpy as0_fill_spec_memset
(SRS.strlen_step_sound _ _ _ _ as0_strlen_spec) as0_in_hull as0_hull_ok
F PSS p pc0 sr0 kn0 fx E R M Hc HXS HXS2 HR HK HBF).
Qed.
Theorem as0_plan_sound : ltac2:(TCodec.tc2 tcn__Jb0PlanKit "UM'7';'A'8%3221%511'QH%711&QL%911'Q5'9%112p031p0;1p061'R0%A11'QN'Q3%D11'Q4%F11'>'5&QJ&R5&QAr;%2231&Q>&Q@&Q?&Q=&Q<r:&Q;r9r8r7&QOr6r5r4r3r2r1%FCEBA@?>=<;:987654321(<%J3I21'RHyR0%211y8%411%Q<11p041&QG%16Q0NGED<pQH31'QB'Q2&Hy5%221<&Q8%13FLE&Q7%14Q:IGN&QIr@%221M'?'=%QO1QJ&R7rD%23QM1Q0(4%12QOQ1%QI3631&Q9rHr<%3321Q:'Q:&QDr=&RGrB%22Q71&QE%11R2%756R13QJ1&R2%11QA%82Q=1%;5QHQF1QE5%=3R851&R6%S32S1RA(:%14S3RCQIQH&R3%11QL%63531&@(3%221R0uQ0%42R21%Q6231&QC&R8%11R6%K2QD1%42R=1&Q1%12R@R9%S03R331%Q?291p0@1pTJS71pU0SH1z%Q52QN1%>2RC1%Q72R<3%S93R<21&QMrE%22RI1&QKrF%23RM1RH%RM1RJ%QE1RK%SB3RB21p041pTHRG1&R1%11S0%Q;3SIS01&Q6%14SFS9S6S3p031pQ<SM1&R4%12SAS8%R<231%R=2;1%R>2D1%R?2H1%R@2N1%RA2QH1%RB2R71%RC2R<1qU<T=1%RF2T>1qU0TL1%RH2TM1qQFS91%RJ2S:1qQNS31%RL2S41qQ8S81%RN2S91qTNS;1%S02S<1p0S21p0S61p0S91pQDSD1pQLS=1pQ6SA1pTLSC1p0SE1p0T01pU4TL1pU>TO1pU:UB1pU8U31pQJU51pQ:U>1pTDU91p4UB1pU6UG1p2UH1pU2UG1").
Proof.
intros itr BFUEL nx0 BR XSTEP F PSS p pc0 sr0 kn0 Hc HXS.
exact (as0_plan_sound2 itr BFUEL nx0 BR XSTEP SGP.xstep2_none F PSS p pc0 sr0 kn0 Hc HXS (fun M0 => SGP.xstep2_none_ok RSEGS nx0 BR F M0)).
Qed.
