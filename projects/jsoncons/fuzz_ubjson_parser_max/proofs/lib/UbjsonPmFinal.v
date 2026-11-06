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
Js0PmLayout Ju0PmLayout PmLayout PmStatics PmSpecsS PmSpecsU PmTopS PmTopU PmSHarness PmUTop PmSExitCells PmUExitCells.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require PropExec.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__UbjsonPmFinal () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.EquivalenceDefinition.Equivalence."; "LinuxProcessSemantics.LinuxProcessSem.MemImageType."; "LinuxProcessSemantics.LinuxProcessSem.Run."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Bridge.HeapInst0."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Bridge.HeapInst1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Js0DrvG."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Js0DrvLibL."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Js0DrvMain."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ju0DrvG."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ju0DrvLibL."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ju0DrvMain."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.LibIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmTopS.PMTS."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmTopU.PMTU."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.UbjsonPmFinal."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.UbjsonPmFinal.FPX_1."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Ubsan.M."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1bool"; "1false"; "1fst"; "1pair"; "1snd"; "2and"; "2eq"; "3Z"; "4strong_universal_error_free_T_scfg"; "5mkImage"; "6SpuriousCfg"; "6sc_alloc"; "6valid_sp"; "7B0"; "7BOV"; "7HI0"]; ["7K0"; "7KPM"; "7L0"; "8B0"; "8BOV"; "8HI1"; "8K0"; "8KPM"; "8L1"; "9debit"; ":cred"; ";drv_lib_layout"; "<src_realizes_stmt2"; "=cred"; ">drv_lib_layout"; "?tgt_realizes_stmt2"]; ["@SCFG"; "Alib_iface_ok"; "All_credit"; "BTopLS"; "BTopLay"; "CTopLS"; "CTopLay"; "EPACKAGES_src"; "EPACKAGES_ub"; "Esptop_window"; "DScfgP_cfg0"; "Dcfg0"; "Finit_pc"; "Floaded_segments"; "Fphdrs"; "Ginit_pc"]; ["Gloaded_segments"; "Gphdrs"; "Hadd"; "Hle"; "Hlt"; "Hmul"; "0n"; "0scfg"; "0sp"; "Ibv"; "Ibv_unsigned"]]).
Definition cfg0 : SpuriousCfg := mkSpuriousCfg false true true true true true.
#[export] Instance ScfgP_cfg0 : ScfgP := {| SCFG := cfg0 |}.
Lemma sc_alloc_cfg0 : ltac2:(TCodec.tc2 tcn__UbjsonPmFinal "9'6'0&;&Q0&Q:%211%411(1%83721").
Proof. reflexivity. Qed.
Section FPX_1.
#[local] Existing Instance PropExec.fx0.
Theorem ubjson_pm_ubsan_ok2 : ltac2:(TCodec.tc2 tcn__UbjsonPmFinal "F':&Lr1%211&Or2%211&8r3(9&Q@&Q?&QA%43321&Q=&Q<&Q>%83321%;3:51p0=1p0A1pS@E1").
Proof. intros scfg.
intros SRC TGT.
intros [rsp rbrk rmb rrnd] [asp abrk amb arnd] inp Hens Hent Hvalid.
pose proof (valid_input_va_size _ Hvalid) as Hsv48.
rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hens. rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hent.
destruct Hens as [Hrsp [Hrbrk [Hrmb Hrfit]]]. destruct Hent as [Hasp [Habrk [Hamb Hafit]]].
destruct Hvalid as (Hargv & Henvp & Hfs & Hrel & Hcreds & _).
apply (shape_strong_equiv_efs scfg _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (spec (in_argv inp) (in_fs inp))).
- exact (SRC rsp rbrk rmb rrnd inp Hrsp Hrbrk Hrmb Hrfit Hargv Henvp Hfs Hcreds).
- exact (TGT asp abrk amb arnd inp Hasp Habrk Hamb Hafit Hargv Henvp Hfs Hcreds).
Qed.
Lemma drv_lib_layout_top0 : ltac2:(TCodec.tc2 tcn__UbjsonPmFinal "A'QIyR0%211&<r1%211'K&Q4&B&QJr2%22:1%411%611%8212p0:1pSB>1").
Proof.
intros sp Hsp. constructor; try reflexivity; try (cbn; lia).
- intros iv Hin. unfold PMTS.TopLay, pm_foot in Hin. cbn in Hin. destruct Hin as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn; lia.
- intros iv Hin. cbn in Hin. destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; cbn; lia.
- intros n Hn. cbn. unfold PMTS.TOPK, PMTS.TOPB. lia.
Qed.
Lemma drv_lib_layout_top1 : ltac2:(TCodec.tc2 tcn__UbjsonPmFinal "A'QIyR0%211&<r1%211'N&Q6&H&QJr2%22:1%411%611%8212p0:1pSB>1").
Proof.
intros sp Hsp. constructor; try reflexivity; try (cbn; lia).
- intros iv Hin. unfold PMTU.TopLay, pm_foot in Hin. cbn in Hin. destruct Hin as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn; lia.
- intros iv Hin. cbn in Hin. destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; cbn; lia.
- intros n Hn. cbn. unfold PMTU.TOPK, PMTU.TOPB. lia.
Qed.
Lemma budget0 : ltac2:(TCodec.tc2 tcn__UbjsonPmFinal "QD'QIyR0%211'7&<r2%211'5&QCz%2215&QD+RPPPP0%2281%7241&J&B&QJr4%22B1%411&QB&A&QE+4&2&Q2&Q4%118r3%4221%63LL1%9281%<2;1&>%>261&4%13Q2Q27%?2>1%B241&I(3&@&=%34Q9Q921+RPP0%63J21%Q05K>8Q61p0Q21p0Q;1pS>Q?1pSBQA1").
Proof.
intros sp n Hsp Hn. unfold Js0DrvG.cred, Js0DrvG.CAPk, debit. cbn [fst snd hl_k_per_malloc hl_b_overhead HeapInst0.L0 ll_credit PMTS.TopLay].
unfold PMTS.TOPK, PMTS.TOPB.
replace HeapInst0.BOV with 6350523 by (vm_compute; reflexivity). replace HeapInst0.KPM with 8 by (vm_compute; reflexivity).
replace HeapInst0.K0 with 8000 by (vm_compute; reflexivity). replace HeapInst0.B0 with (2 ^ 33) by (vm_compute; reflexivity). lia.
Qed.
Lemma budget1 : ltac2:(TCodec.tc2 tcn__UbjsonPmFinal "QD'QIyR0%211'7&<r2%211'5&QCz%2215&QD+RPPPP0%2281%7241&M&H&QJr4%22B1%411&QB&G&QE+4&2&Q2&Q6%118r3%4221%63LL1%9281%<2;1&D%>261&4%13Q2Q27%?2>1%B241&I(3&F&C%34Q9Q921+RPP0%63J21%Q05K>8Q61p0Q21p0Q;1pS>Q?1pSBQA1").
Proof.
intros sp n Hsp Hn. unfold Ju0DrvG.cred, Ju0DrvG.CAPk, debit. cbn [fst snd hl_k_per_malloc hl_b_overhead HeapInst1.L1 ll_credit PMTU.TopLay].
unfold PMTU.TOPK, PMTU.TOPB.
replace HeapInst1.BOV with 6350523 by (vm_compute; reflexivity). replace HeapInst1.KPM with 8 by (vm_compute; reflexivity).
replace HeapInst1.K0 with 8000 by (vm_compute; reflexivity). replace HeapInst1.B0 with (2 ^ 33) by (vm_compute; reflexivity). lia.
Qed.
Theorem ubjson_pm_ubsan_final : ltac2:(TCodec.tc2 tcn__UbjsonPmFinal "Q<'QIyR0%211&<r1%211'Q1&Q4&B&QJr2%22:1%411%611&Q;&?%115&Q3%<45421p0>1pSBB1&Q6&H%11<%311&E%11?&Q5%F44>21p0H1pSBL1&8(9&Q@&Q?&QA%43321&Q=&Q<&Q>%83321%:3K51p0<1p0G1").
Proof.
intros LIB0 LIB1. apply ubjson_pm_ubsan_ok2.
- apply (src0_realizes_spec_heap cfg0 eq_refl eq_refl
(fun sp => PMTS.TopLay (HeapInst0.L0 (bv_unsigned sp))) (fun _ => PMTS.TopLS));
[exact drv_lib_layout_top0 | exact LIB0 | intros sp _; exact PMSXC.top_lsx | exact budget0].
- apply (ub0_realizes_spec_heap cfg0 eq_refl eq_refl
(fun sp => PMTU.TopLay (HeapInst1.L1 (bv_unsigned sp))) (fun _ => PMTU.TopLS));
[exact drv_lib_layout_top1 | exact LIB1 | intros sp _; exact PMUXC.top_lsx | exact budget1].
Qed.
Definition sptop_window (sptop : Z) : Prop := 0x7fff80000000 <= sptop <= 2 ^ 47.
Lemma valid_sp_window : ltac2:(TCodec.tc2 tcn__UbjsonPmFinal "='QIyR0%211&<r1%211&Q9&QJr2%2281%411p061pSB:1").
Proof.
intros sp (Hlo & Hhi & _). unfold sptop_window. unfold sp_window_lo in Hlo. unfold sp_window_hi in Hhi.
split; [exact Hlo | exact Hhi].
Qed.
Definition PACKAGES_src : Prop := forall sptop, sptop_window sptop -> @PMHT.harness_deps ScfgP_cfg0 (L0 sptop) (HI0 sptop).
Definition PACKAGES_ub : Prop := forall sptop, sptop_window sptop -> @PMUT.top_deps ScfgP_cfg0 (L1 sptop) (HI1 sptop).
Lemma LIB0_of_packages : ltac2:(TCodec.tc2 tcn__UbjsonPmFinal "G&Q7'QIyR0%211&<r1%211'Q1&Q4&B&QJr2%22:1%411%611&Q;&?%115&Q3%<45421p0>1pSBB1p0F1").
Proof.
intros PK sp V. pose proof (valid_sp_window sp V) as W.
assert (LY : PMS.layout (L0 (bv_unsigned sp))) by (apply pm_layout_L0; unfold sptop_window in W; lia).
exact (@PMHT.harness_iface_ok ScfgP_cfg0 (L0 (bv_unsigned sp)) (HI0 (bv_unsigned sp)) LY (HI0_ok_closed (bv_unsigned sp) cfg0 eq_refl) (PK _ W)).
Qed.
Lemma LIB1_of_packages : ltac2:(TCodec.tc2 tcn__UbjsonPmFinal "G&Q8'QIyR0%211&<r1%211'Q1&Q6&H&QJr2%22:1%411%611&Q;&E%115&Q5%<45421p0>1pSBB1p0F1").
Proof.
intros PK sp V. pose proof (valid_sp_window sp V) as W.
assert (LY : PMU.layout (L1 (bv_unsigned sp))) by (apply pm_layout_L1; unfold sptop_window in W; lia).
exact (@PMUT.top_iface_ok ScfgP_cfg0 (L1 (bv_unsigned sp)) (HI1 (bv_unsigned sp)) LY (HI1_ok_closed (bv_unsigned sp) cfg0 eq_refl) (PK _ W)).
Qed.
Theorem ubjson_pm_ubsan_modulo_packages : ltac2:(TCodec.tc2 tcn__UbjsonPmFinal "@&Q7&Q8&8&Q;(9&Q@&Q?&QA%43321&Q=&Q<&Q>%83321%;3:51p0=1p0?1").
Proof. intros P0 P1. exact (ubjson_pm_ubsan_final (LIB0_of_packages P0) (LIB1_of_packages P1)). Qed.
End FPX_1.
