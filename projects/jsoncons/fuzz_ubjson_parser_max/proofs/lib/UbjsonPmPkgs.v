(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import HeapIface LibIface L5Defs.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Bridge Require Import HeapInst0 HeapInst1 HeapClosed.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import Js0PmLayout Ju0PmLayout PmSpecsS PmSpecsU PmSHarness PmUTop UbjsonPmFinal
PmStrS PmIssS PmReadS PmSysS PmLocS PmSSrcDtor PmSIosDtor Js0Opdel Js0Opnew PmSReset
PmStrU PmIssU PmReadU PmSysU PmLocU PmUReset PmUSrcDtor PmUIosDtor Ju0Opdel Ju0Opnew PmSClose PmUClose.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Theorem packages_src : PACKAGES_src.
Proof.
intros sptop W.
assert (LY : PMS.layout (L0 sptop)) by (apply pm_layout_L0; unfold sptop_window in W; lia).
pose proof (HI0_ok_closed sptop cfg0 eq_refl) as HIok.
pose proof (@L5NEW.opnew_ok ScfgP_cfg0 (L0 sptop) (HI0 sptop) LY HIok) as OPN.
pose proof (@L5DEL.opdel_ok ScfgP_cfg0 (L0 sptop) (HI0 sptop) LY HIok) as OPD.
pose proof (@PMLOC.locale_ctor_ok ScfgP_cfg0 (L0 sptop) (HI0 sptop) LY HIok) as LCT.
pose proof (@PMLOC.locale_dtor_ok ScfgP_cfg0 (L0 sptop)) as LDT.
pose proof (@PMSID.ios_dtor_ok ScfgP_cfg0 (L0 sptop) (HI0 sptop) LY HIok LDT) as IDT.
constructor.
- exact (@PMSTR.str_ctor_ok ScfgP_cfg0 (L0 sptop) (HI0 sptop) LY HIok OPN).
- exact (@PMISS.iss_ctor_ok ScfgP_cfg0 (L0 sptop) (HI0 sptop) LY HIok LCT OPN).
- exact (@PMRD.reader_ctor_ok ScfgP_cfg0 (L0 sptop) (HI0 sptop) LY HIok LCT OPN).
- exact (@PMSYS.syscat_ok ScfgP_cfg0 (L0 sptop) (HI0 sptop) LY HIok).
- exact (@PMSRS.reset_ok ScfgP_cfg0 (L0 sptop) (HI0 sptop) LY HIok).
- exact (@PMSCL.parse_closed ScfgP_cfg0 (L0 sptop) (HI0 sptop) LY HIok).
- exact OPD.
- exact (@PMSSD.src_dtor_ok ScfgP_cfg0 (L0 sptop) (HI0 sptop) LY HIok OPD LDT IDT).
- exact LDT.
- exact IDT.
Qed.
Theorem packages_ub : PACKAGES_ub.
Proof.
intros sptop W.
assert (LY : PMU.layout (L1 sptop)) by (apply pm_layout_L1; unfold sptop_window in W; lia).
pose proof (HI1_ok_closed sptop cfg0 eq_refl) as HIok.
pose proof (@L5DELU.opdel_ok ScfgP_cfg0 (L1 sptop) (HI1 sptop) LY HIok) as OPD.
pose proof (@L5NEWU.opnew_ok ScfgP_cfg0 (L1 sptop) (HI1 sptop) LY HIok) as OPN.
pose proof (@PMLOCU.locale_ctor_ok ScfgP_cfg0 (L1 sptop) (HI1 sptop) LY HIok) as LCT.
pose proof (@PMLOCU.locale_dtor_ok ScfgP_cfg0 (L1 sptop)) as LDT.
pose proof (@PMUID.ios_dtor_ok ScfgP_cfg0 (L1 sptop) (HI1 sptop) LY HIok LDT) as IDT.
constructor.
- exact (@PMSTRU.str_ctor_ok ScfgP_cfg0 (L1 sptop) (HI1 sptop) LY HIok OPN).
- exact (@PMISSU.iss_ctor_ok ScfgP_cfg0 (L1 sptop) (HI1 sptop) LY HIok LCT OPN).
- exact (@PMRDU.reader_ctor_ok ScfgP_cfg0 (L1 sptop) (HI1 sptop) LY HIok LCT OPN).
- exact (@PMSYSU.syscat_ok ScfgP_cfg0 (L1 sptop) (HI1 sptop) LY HIok).
- exact (@PMURS.reset_ok ScfgP_cfg0 (L1 sptop) (HI1 sptop) LY HIok).
- exact (@PMUCL.parse_closed ScfgP_cfg0 (L1 sptop) (HI1 sptop) LY HIok).
- exact OPD.
- exact (@PMUSD.src_dtor_ok ScfgP_cfg0 (L1 sptop) (HI1 sptop) LY HIok OPD LDT IDT).
- exact LDT.
- exact IDT.
Qed.
