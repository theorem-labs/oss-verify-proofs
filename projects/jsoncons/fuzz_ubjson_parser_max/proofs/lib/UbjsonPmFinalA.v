(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Plain.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import ShapeAlg DivergeSim SpinAlg SpinAlgX ShapeEF Spec BigintSpec HeapIface LibIface L5Defs.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Bridge Require Import HeapInst0 HeapInst1 HeapClosed.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import Js0DrvLibL Ju0DrvLibL Js0DrvG Ju0DrvG Js0DrvMain Ju0DrvMain Js0HeapBridge Ju0HeapBridge
PmTopS PmTopU PmSExitCells PmUExitCells UbjsonPmFinal KillFree.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require PropExec.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__UbjsonPmFinalA () := ([""; "LinuxProcessSemantics.EquivalenceDefinition.Equivalence."; "LinuxProcessSemantics.EquivalenceDefinition.Equivalence.ShippedBudgets."; "LinuxProcessSemantics.LinuxProcessSem.MemImageType."; "LinuxProcessSemantics.LinuxProcessSem.Run."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Bridge.HeapInst0."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Bridge.HeapInst1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.LibIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmTopS.PMTS."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmTopU.PMTU."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.UbjsonPmFinal."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Ubsan.M."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M."; "stdpp.bitvector.definitions."], [["2lim_source"; "2lim_target"; "1strong_universal_error_free_T_scfg_budgets_abort"; "3mkImage"; "4valid_sp"; "5HI0"; "5L0"; "6HI1"; "6L1"; "7lib_iface_ok"; "8TopLS"; "8TopLay"; "9TopLS"; "9TopLay"; ":PACKAGES_src"; ":PACKAGES_ub"]; [":cfg0"; ";init_pc"; ";loaded_segments"; ";phdrs"; "<init_pc"; "<loaded_segments"; "<phdrs"; "0sp"; "=bv"; "=bv_unsigned"]]).
Section FPX_1.
#[local] Existing Instance PropExec.fx0.
Theorem ubjson_pm_ubsan_final_abort : ltac2:(TCodec.tc2 tcn__UbjsonPmFinalA "Q>'HyR0%211&4r1%211'9&;&6&Ir2%22:1%411%611&@&5%115&:%<45421p0>1pQ@B1&=&8%11<%311&7%11?&<%F44>21p0H1pQ@L1&2&0&1(3&E&D&F%43321&B&A&C%83321%<5M;:51p0>1p0I1").
Proof.
intros LIB0 LIB1.
pose proof (src0_realizes_spec_heap cfg0 eq_refl eq_refl
(fun sp => PMTS.TopLay (HeapInst0.L0 (bv_unsigned sp))) (fun _ => PMTS.TopLS)
drv_lib_layout_top0 LIB0 (fun sp _ => PMSXC.top_lsx) budget0) as SRC.
pose proof (ub0_realizes_spec_heap cfg0 eq_refl eq_refl
(fun sp => PMTU.TopLay (HeapInst1.L1 (bv_unsigned sp))) (fun _ => PMTU.TopLS)
drv_lib_layout_top1 LIB1 (fun sp _ => PMUXC.top_lsx) budget1) as TGT.
intros [rsp rbrk rmb rrnd] [asp abrk amb arnd] inp Hens Hent Hvalid _.
pose proof (valid_input_abort_va_size _ Hvalid) as Hsv48.
rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hens. rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hent.
destruct Hens as [Hrsp [Hrbrk [Hrmb Hrfit]]]. destruct Hent as [Hasp [Habrk [Hamb Hafit]]].
destruct Hvalid as (Hargv & Henvp & Hfs & Hrel & Hcreds & _).
specialize (SRC rsp rbrk rmb rrnd inp Hrsp Hrbrk Hrmb Hrfit Hargv Henvp Hfs Hcreds).
specialize (TGT asp abrk amb arnd inp Hasp Habrk Hamb Hafit Hargv Henvp Hfs Hcreds).
unfold ShippedBudgets.lim_source, ShippedBudgets.lim_target.
split; [| split].
- eapply srealizes_error_free_unkilled; [exact SRC | apply kill_free_spec].
- eapply srealizes_error_free_unkilled; [exact TGT | apply kill_free_spec].
- intro tr.
rewrite (srealizes_traces_iff cfg0 _ _ _ _ _ _ _ _ _ _ tr SRC).
rewrite (srealizes_traces_iff cfg0 _ _ _ _ _ _ _ _ _ _ tr TGT).
reflexivity.
Qed.
Theorem ubjson_pm_ubsan_abort_modulo_packages : ltac2:(TCodec.tc2 tcn__UbjsonPmFinalA "B&>&?&2&@&0&1(3&E&D&F%43321&B&A&C%83321%=5<;:51p0?1p0A1").
Proof. intros P0 P1. exact (ubjson_pm_ubsan_final_abort (LIB0_of_packages P0) (LIB1_of_packages P1)). Qed.
End FPX_1.
