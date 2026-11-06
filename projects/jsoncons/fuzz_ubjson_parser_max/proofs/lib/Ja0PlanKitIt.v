(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3
AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegRunStrlen Ja0Sums Ja0SumsStrlen SegPlan Ja0PlanKit.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__Ja0PlanKitIt () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Init.Peano."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AxSymExec3.AX2."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AxSymExec3Sound.AX2S."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AxSymRun3."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ja0PlanKit."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SegPlan.SGP."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SegRun.SR."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.StoreOk."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0BFUEL"; "0BR"; "1O"; "1Some"; "1bool"; "1list"; "1nat"; "1option"; "1pair"; "1prod"; "1true"; "2and"; "2eq"; "2ex"; "3lt"; "4Z"]; ["0E"; "0E'"; "0F"; "0IT"; "0K"; "5bvmap"; "0M"; "0M'"; "0M0"; "0PSS"; "0R"; "0R'"; "6edenot"; "6env"; "6expr"; "6itab"]; ["6itab_sound"; "6kentry"; "6sym_state"; "7kentry_ok"; "7know_ok"; "7regs_ok"; "8env_agree"; "9msteps"; ":A0"; ":RO_HI"; ":RO_LO"; ":X_CPY"; ":X_LEN"; ":X_SET"; ";FPState"; ";getr"]; [";mkst"; ";seg_rom"; "<XSTEP_ok"; "<bfact"; "<bfacts_ok"; "<cert_ok"; "<outside"; "<region"; "<regions_ok"; "<splan"; "<xstep2_none"; "=post_spec"; "=ps_cells"; "=ps_pc"; "=ps_regs"; ">mem_grows"]; ["?loaded_segments"; "@In"; "@nth_error"; "Aof_nat"; "0XSTEP"; "0a"; "0e"; "0fx"; "0fx'"; "0i"; "0kn0"; "0nx0"; "0p"; "0pc0"; "0ps"; "0sr0"]; ["BZ_to_bv"; "Bbv"]]).
Abbreviation RSEGS := Asan.M.loaded_segments.
Theorem as0_plan_sound_it : ltac2:(TCodec.tc2 tcn__Ja0PlanKitIt "UM&O&Q0&R0r1%3221'6'5'QC%211&QG%411'Q2'7%112p031p0:1p061'QK%<11'QI'?'N%@11'Q1%B11'<'4&QEr<&Q;&Q=&Q<&Q:&Q9r:&Q8r9r8r7&QJr6r5r4r3r2%BCQ;A@?>=<;:987654321Q:(:%F3E21'RAyR0%211y8%411%Q911p041&QBr;%26QG1GEDQFpQB41'Q>'M&Ey5%221=&Q5%13FLE&Q4%14R1IGN&QDr@%221M'=';%QM1QH&R2rD%23QK1Q0(3%12QMR;%QF3631&Q6rH%231QFQ9'Q7&Q@r=&R@rB%22Q71&QA%11RH%756Q33QI1&QM%11RJ%82Q=1%;5QGQE1QD5%=3RN51&R1'9%12RNR>(8%14S0R@QIS2&QN%11QL%73531&>(2%221R0uQ0%42R21%Q6231&Q?&R3%11R6%L2QD1%42R=1&L%12R@R9%RM3R431%Q?291p0@1pT>S41pTDSE1z%Q62QN1%>2RC1%Q82R=3%S63R=21&QHrE%22RI1&QFrF%23RM1T2%RM1RJ%S;1RK%S?3RC21p041pT<RH1&QL%11S0%Q<3SFT:1&Q3%14T=S9S6S3p031pQ:SJ1&QO%12SAS8%R<231%R=2;1%R>2D1%R?2H1%R@2N1%RA2QI1%RB2R81%RC2R<1qTNT;1%RF2T<1qTDTI1%RH2TJ1qQ@S:1%RJ2S;1qQHS31%RL2S41qQ4S81%RN2S91qTBS;1%S02S<1p0S21p0S61p0S91pQ>SE1pQFS=1pQ2SA1pT@SC1p0SE1p0T11pTFTI1pU0TL1pTLTO1pTJU11pQDU31pQ6U<1pT:U71p4U@1pTHUD1p2UE1p0UG1pQ8UL1").
Proof.
intros IT HIT BFUEL nx0 BR XSTEP F PSS p pc0 sr0 kn0 Hc HXS fx E R M HR HK HBF.
exact (SGP.plan_entry_sound RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BFUEL A0 nx0 BR XSTEP SGP.xstep2_none
HIT as0_copy_spec_memcpy as0_fill_spec_memset
(SRS.strlen_step_sound _ _ _ _ as0_strlen_spec) as0_in_hull as0_hull_ok
F PSS p pc0 sr0 kn0 fx E R M Hc HXS (fun M0 => SGP.xstep2_none_ok RSEGS nx0 BR F M0) HR HK HBF).
Qed.
