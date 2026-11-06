(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Plain.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import ShapeAlg DivergeSim SpinAlg SpinAlgX ShapeEF Spec BigintSpec HeapIface LibIface L5Defs.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Bridge Require Import HeapInst0 HeapClosed.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import Js0DrvLibL Js0DrvG Js0DrvMain Js0HeapBridge PmTopS PmSExitCells UbjsonPmFinal UbjsonPmPkgs KillFree.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import AsanAcct HeapIfaceA IcptIfaceAB0 LibIfaceAJ HeapIfaceAJx AsanInitK Jb0DefsK Jb0MainPhaseA
PmLayoutA PmStaticsA PmSpecsAX PmSpecsAb PmBHarnessStmts PmBStaticsTop PmBImgGap PmBLibOk PmBClose UbjsonPmBothTop.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require PropExec.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__UbjsonPmBothTopOld () := ([""; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.EquivalenceDefinition.Equivalence."; "LinuxProcessSemantics.LinuxProcessSem.MemImageType."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIfaceA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIfaceAJx.HAJ."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.IcptIfaceAB0."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Jb0MainPhaseA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmBHarnessStmts.PMHAS."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmBImgGap.PMBGAP."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmBLibOk.PMBLO."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmLayoutA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecsAb.PMB."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmStaticsA.PMSTA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.UbjsonPmBothTop."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.UbjsonPmFinal."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M."; "Stdlib.ZArith.BinInt.Z."], [["0BUDGET"; "0C"; "1Z"; "0HIR"; "0IL"; "0L"; "2strong_universal_error_free_T_scfg"; "3mkImage"; "4asan_iface"; "4asan_layout"; "4asan_run"; "4asan_statics_cells"; "5asan_ext_ok"; "5asan_iface_okR"; "6aicpt_ok"; "6icpt_layout"]; ["7dla_ok_stmt"; "7drv_consts_stmt"; "7drv_main_stmt"; "7ext_ok_stmt"; "7free_null_stmt"; "7gap_ok_stmt"; "7h4e_stmt"; "7icpt_ok_stmt"; "7inst_ok_stmt"; "7usage_stmt"; "8Lay"; "9rt_img_gap"; ":harness_depsB"; ";AADDR_B"; ";ADDR_B"; "<EXT"]; ["<layout"; "=TopLSA"; ">as0_tgt_stmt"; "?ScfgP_cfg0"; "?cfg0"; "@init_pc"; "@loaded_segments"; "@phdrs"; "Ainit_pc"; "Aloaded_segments"; "Aphdrs"; "Ble"; "Bpow"; "Bsub"; "0ar"]]).
Section FPX_1.
#[local] Existing Instance PropExec.fx0.
Theorem ubjson_pm_both_final_scfg : ltac2:(TCodec.tc2 tcn__UbjsonPmBothTopOld "?&Q2&Q4%211&6(7&Q9&Q8&Q:%43321&Q6&Q5&Q7%83321%:3<51p0<1").
Proof.
intros TGT.
pose proof (src0_realizes_spec_heap cfg0 eq_refl eq_refl
(fun sp => PMTS.TopLay (HeapInst0.L0 (bv_unsigned sp))) (fun _ => PMTS.TopLS)
drv_lib_layout_top0 (LIB0_of_packages packages_src) (fun sp _ => PMSXC.top_lsx) budget0) as SRC.
intros [rsp rbrk rmb rrnd] [asp abrk amb arnd] inp Hens Hent Hvalid.
pose proof (valid_input_va_size _ Hvalid) as Hsv48.
rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hens. rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hent.
destruct Hens as [Hrsp [Hrbrk [Hrmb Hrfit]]]. destruct Hent as [Hasp [Habrk [Hamb Hafit]]].
destruct Hvalid as (Hargv & Henvp & Hfs & Hrel & Hcreds & _ & _ & Hhw & _).
specialize (SRC rsp rbrk rmb rrnd inp Hrsp Hrbrk Hrmb Hrfit Hargv Henvp Hfs Hcreds).
specialize (TGT asp abrk amb arnd inp Hasp Habrk Hamb Hafit Hargv Henvp Hfs Hcreds Hhw Hsv48).
split; [| split].
- eapply srealizes_error_free; exact SRC.
- eapply srealizes_error_free; exact TGT.
- intro tr.
rewrite (srealizes_traces_iff cfg0 _ _ _ _ _ _ _ _ _ _ tr SRC).
rewrite (srealizes_traces_iff cfg0 _ _ _ _ _ _ _ _ _ _ tr TGT).
reflexivity.
Qed.
Theorem ubjson_pm_both_base_scfg_modulo : ltac2:(TCodec.tc2 tcn__UbjsonPmBothTopOld "S@'9';'?'2&Q;&Q<+2+Q2%3221r1%6221r2&Q=+Q7%9281+Q3%;2:1%5231%>271'Q0r6r5%3221':'8'=r9r8&Q4%453B21D'>r:r3%352165F'<r;r4&O%4532:61&K%114&L&Q3r=%3421HGp051p081p0>1p0C1p8I1pRNK1&Hr7%24IJ1Q0&D%13KMQ3&F%115&G%14OHQ1Q0&Cr<%24Q21IQ4&E%11Q1&@r>%24Q71H6&Ar?%2314K&Br@&J%112&Q1&Q6&N&M%43321q0QI1%:6QE9<?71&I%11QG&6(7&Q9&Q8&Q:%43321&Q5&Q7%73@21%93R141p0;1p0>1p0J1p0N1p0Q21p0Q51p0Q91p0Q<1p0Q?1p0QB1p0QF1p0RC1p0RH1p0S11p2S91p:S;1p4S=1p<S?1").
Proof.
intros L C IL BUDGET B1 B2 LY PKG H1 H1n H2 H3 H3e HG H5 H6 H7 H8.
assert (ILY : as0_icpt_layout IL) by exact (proj1 H6).
pose proof (@PMBLO.lib_ok ScfgP_cfg0 L C IL LY ILY PKG) as H4.
apply ubjson_pm_both_final_scfg. apply as0_tgt_of_run.
intros sp brk0 mbase rdraw argv envp fs stdin uid gid hw groups net nofile sigmask abrt urnd Hsp Hbrk Hva Hve Hfit Huid Hhw Hvfs.
exact (as0_realizes_spec_run cfg0 eq_refl eq_refl L C IL (PMHAS.Lay L) (fun _ => PMSTA.TopLSA AsanUbsan.M.loaded_segments PMB.AD PMB.AAD)
PMB.EXT BUDGET B1 B2 H1 H1n H2 H3 H3e HG H4 H5 H6 H7 H8 PMSTTB.lsx_atexit
sp brk0 mbase rdraw argv envp fs stdin uid gid hw groups net nofile sigmask abrt urnd Hsp Hbrk Hva Hve Hfit Huid Hhw Hvfs).
Qed.
End FPX_1.
