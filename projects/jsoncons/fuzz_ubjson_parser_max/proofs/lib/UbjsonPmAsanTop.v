(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Plain.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import ShapeAlg DivergeSim SpinAlg SpinAlgX ShapeEF Spec BigintSpec HeapIface LibIface L5Defs.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Bridge Require Import HeapInst0 HeapClosed.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import Js0DrvLibL Js0DrvG Js0DrvMain Js0HeapBridge PmTopS PmSExitCells UbjsonPmFinal UbjsonPmPkgs KillFree.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import AsanAcct HeapIfaceA IcptIfaceA LibIfaceAJ HeapIfaceAJx AsanInitK Ja0DefsK Ja0MainPhaseA
PmLayoutA PmStaticsA PmSpecsAX PmSpecsAa PmAHarnessStmts PmAStaticsTop PmAImgGap PmALibOk PmAClose.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require PropExec.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__UbjsonPmAsanTop () := ([""; "Corelib.Init.Datatypes."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.EquivalenceDefinition.Equivalence."; "LinuxProcessSemantics.EquivalenceDefinition.Equivalence.ShippedBudgets."; "LinuxProcessSemantics.LinuxProcessSem.Fs."; "LinuxProcessSemantics.LinuxProcessSem.MemImageType."; "LinuxProcessSemantics.LinuxProcessSem.Run."; "LinuxProcessSemantics.LinuxProcessSem.StackLayout."; "LinuxProcessSemantics.LinuxProcessSem.State."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanInitK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.BigintSpec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIfaceA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIfaceAJx.HAJ."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.IcptIfaceA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ja0DefsK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ja0MainPhaseA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmAHarnessStmts.PMHAS."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmAImgGap.PMAGAP."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmALibOk.PMALO."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmLayoutA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecsAa.PMA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmStaticsA.PMSTA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.UbjsonPmAsanTop.FPX_1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.UbjsonPmFinal."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0BUDGET"; "0C"; "1bool"; "1list"; "2Z"; "0HIR"; "0IL"; "0L"; "4lim_source"; "4lim_target"; "3strong_universal_error_free_T_scfg_budgets_abort"; "5Fs"; "5valid_fs"; "6mkImage"; "7SpuriousCfg"; "7entry_stack_fits"]; ["7init_config"; "7valid_argv"; "7valid_brk"; "7valid_envp"; "7valid_hwcap"; "7valid_id"; "7valid_sp"; "8EntryDraw"; "9InputStream"; "9NetQueue"; ":LIMIT"; ":inp"; ";spec"; "<asan_iface"; "<asan_layout"; "<asan_run"]; ["<asan_statics_cells"; "=asan_ext_ok"; "=asan_iface_okR"; ">aicpt_ok"; ">icpt_layout"; "?APH0"; "?ASEGS0"; "@dla_ok_stmt"; "@drv_consts_stmt"; "@drv_main_stmt"; "@ext_ok_stmt"; "@free_null_stmt"; "@gap_ok_stmt"; "@h4e_stmt"; "@icpt_ok_stmt"; "@inst_ok_stmt"]; ["@usage_stmt"; "ALay"; "Brt_img_gap"; "Charness_depsA"; "DAADDR_A"; "DADDR_A"; "EEXT"; "Elayout"; "FTopLSA"; "Gsrealizes"; "Has0_tgt_stmt"; "Hopen_leavesA"; "IScfgP_cfg0"; "Icfg0"; "Jinit_pc"; "Jloaded_segments"]; ["Jphdrs"; "Kinit_pc"; "Kloaded_segments"; "Kphdrs"; "Lle"; "Lpow"; "Lsub"; "0abrt"; "0ar"; "0argv"; "0brk0"; "0envp"; "0fs"; "0gid"; "0groups"; "0hw"]; ["0mbase"; "0net"; "0nofile"; "0rdraw"; "0scfg"; "0sigmask"; "0sp"; "0stdin"; "Mbv"; "0uid"; "0urnd"]]).
Section FPX_1.
#[local] Existing Instance PropExec.fx0.
Definition as0_tgt_stmt (scfg : SpuriousCfg) : Prop :=
forall sp brk mbase (rdraw : EntryDraw) (inp : ProcInput),
valid_sp sp -> valid_brk Asan.M.loaded_segments brk -> valid_mmap_base mbase ->
entry_stack_fits sp (in_argv inp) (in_envp inp) ->
valid_argv (in_argv inp) -> valid_envp (in_envp inp) -> valid_fs (in_fs inp) -> valid_creds inp -> valid_hwcap (in_hwcap inp) ->
in_va_size inp = Sv48 ->
srealizes Asan.M.loaded_segments scfg
(init_config Asan.M.loaded_segments Asan.M.init_pc Asan.M.phdrs
sp brk mbase rdraw target_alloc_limit inp)
(spec (in_argv inp) (in_fs inp)).
Lemma as0_tgt_of_run : ltac2:(TCodec.tc2 tcn__UbjsonPmAsanTop "RK'>'RHyR0%211'G'3y8%611%311%411&;'H%719'I'2&FrA%211&B&Q6%2214&Ar?%211&C%113&?rEr@%332=1&Er>%211&Dr=%211&<rB%211'QIrJ&@&QN&Q5rIrHrGrF&J&KrDrCr<r;r:r9%7=M65CQ8LQ2IF4321%@9Q6?>=<;:91&L%12Q08%E4Q9D31p0G1p0K1p0O1p0Q31p0Q81p0Q;1p0Q?1p0QC1pUFQJ1pT@QH1pU<R41pU6R51pU4QL1pTNQN1pU0R81pTLR91pUDR:1pU@R31pTJR51pTHR71pTDR81pU8R>1pU2R@1pTFRA1pU>RB1&QJr2%211p041pU:RJ1").
Proof.
intros scfg RUN sp brk mbase rdraw inp Hsp Hbrk Hmb Hfit Hva Hve Hvfs Hcreds Hhw Hsv.
destruct Hcreds as [Hu _].
exact (RUN sp brk mbase rdraw (in_argv inp) (in_envp inp) (in_fs inp) (in_stdin inp) (in_uid inp) (in_gid inp) (in_hwcap inp) (in_groups inp)
(in_net inp) (in_nofile inp) (in_sigmask inp) (in_abort_terminal inp) (in_urandom inp) Hsp Hbrk Hva Hve Hfit Hu Hhw Hvfs).
Qed.
Theorem ubjson_pm_asan_final_abort : ltac2:(TCodec.tc2 tcn__UbjsonPmAsanTop "A&QJ&QM%211&:&8&9(=&R2&R1&R3%43321&QO&QN&R0%83321%<5>;:51p0>1").
Proof.
intros TGT.
pose proof (src0_realizes_spec_heap cfg0 eq_refl eq_refl
(fun sp => PMTS.TopLay (HeapInst0.L0 (bv_unsigned sp))) (fun _ => PMTS.TopLS)
drv_lib_layout_top0 (LIB0_of_packages packages_src) (fun sp _ => PMSXC.top_lsx) budget0) as SRC.
intros [rsp rbrk rmb rrnd] [asp abrk amb arnd] inp Hens Hent Hvalid _.
pose proof (valid_input_abort_va_size _ Hvalid) as Hsv48.
rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hens. rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hent.
destruct Hens as [Hrsp [Hrbrk [Hrmb Hrfit]]]. destruct Hent as [Hasp [Habrk [Hamb Hafit]]].
destruct Hvalid as (Hargv & Henvp & Hfs & Hrel & Hcreds & _ & _ & Hhw & _).
specialize (SRC rsp rbrk rmb rrnd inp Hrsp Hrbrk Hrmb Hrfit Hargv Henvp Hfs Hcreds).
specialize (TGT asp abrk amb arnd inp Hasp Habrk Hamb Hafit Hargv Henvp Hfs Hcreds Hhw Hsv48).
unfold ShippedBudgets.lim_source, ShippedBudgets.lim_target.
split; [| split].
- eapply srealizes_error_free_unkilled; [exact SRC | apply kill_free_spec].
- eapply srealizes_error_free_unkilled; [exact TGT | apply kill_free_spec].
- intro tr.
rewrite (srealizes_traces_iff cfg0 _ _ _ _ _ _ _ _ _ _ tr SRC).
rewrite (srealizes_traces_iff cfg0 _ _ _ _ _ _ _ _ _ _ tr TGT).
reflexivity.
Qed.
Theorem ubjson_pm_asan_base_abort_modulo : ltac2:(TCodec.tc2 tcn__UbjsonPmAsanTop "SB'N'Q0'Q4'4&R4&R5+2+Q2%3221r1%6221r2&R6+Q7%9281+Q3%;2:1%5231%>271'QGr6r5%3221'O'M'Q2r9r8&QM%453B21D'Q3r:r3%352165F'Q1r;r4&QF%4532:61&QB%114&QC&QLr=%3421HGp051p081p0>1p0C1p<I1pTBK1&Q?r7%24IJ1Q0&Q;%13KMQ3&Q=%115&Q>%14OHQ1Q0&Q:r<%24Q21IQ4&Q<%11Q1&Q7r>%24Q71H6&Q8r?%2314K&Q9r@&QA%112&QH&QO&QE&QD%43321q0QI1%:6QE9<?71&Q@%11QG&:&8&9(=&R2&R1&R3%43321&QN&R0%73B21%;5R3:941p0=1p0@1p0L1p0Q01p0Q41p0Q71p0Q;1p0Q>1p0QA1p0QD1p0QH1p0RE1p0RJ1p0S31p2S;1p>S=1p4S?1p@SA1").
Proof.
intros L C IL BUDGET B1 B2 LY PKG H1 H1n H2 H3 H3e HG H5 H6 H7 H8.
assert (ILY : as0_icpt_layout IL) by exact (proj1 H6).
pose proof (@PMALO.lib_ok ScfgP_cfg0 L C IL LY ILY PKG) as H4.
apply ubjson_pm_asan_final_abort. apply as0_tgt_of_run.
intros sp brk0 mbase rdraw argv envp fs stdin uid gid hw groups net nofile sigmask abrt urnd Hsp Hbrk Hva Hve Hfit Huid Hhw Hvfs.
exact (as0_realizes_spec_run cfg0 eq_refl eq_refl L C IL (PMHAS.Lay L) (fun _ => PMSTA.TopLSA Asan.M.loaded_segments PMA.AD PMA.AAD)
PMA.EXT BUDGET B1 B2 H1 H1n H2 H3 H3e HG H4 H5 H6 H7 H8 PMSTT.lsx_atexit
sp brk0 mbase rdraw argv envp fs stdin uid gid hw groups net nofile sigmask abrt urnd Hsp Hbrk Hva Hve Hfit Huid Hhw Hvfs).
Qed.
Definition open_leavesA (L : asan_layout) (ar : asan_run) (HI : asan_iface) : Prop :=
@PMA.locale_ctor_spec ScfgP_cfg0 L ar HI /\ @PMA.locale_dtor_spec ScfgP_cfg0 L ar HI /\ @PMA.push_mi_spec ScfgP_cfg0 L ar HI
/\ @PMA.push_miu_spec ScfgP_cfg0 L ar HI /\ @PMA.ann_shrink_spec ScfgP_cfg0 L ar HI /\ @PMA.ann_delete_spec ScfgP_cfg0 L ar HI
/\ @PMA.parse_spec ScfgP_cfg0 L ar HI.
Theorem ubjson_pm_asan_base_abort_leaves : ltac2:(TCodec.tc2 tcn__UbjsonPmAsanTop "SA'N'Q0'Q4'4&R4&R5+2+Q2%3221r1%6221r2&R6+Q7%9281+Q3%;2:1%5231%>271'QGr6r5%3221'O'M'Q2r9r8&QM%453B21D'Q3r:r3%352165F'Q1r;r4&QF%4532:61&QB%114&QKr=%231GFp041p071p0=1p0B1p<H1pTBJ1&Q?r7%24HI1O&Q;%13JLQ2&Q=%115&Q>%14NGQ0O&Q:r<%24Q11HQ3&Q<%11Q0&Q7r>%24Q61H6&Q8r?%2314K&Q9r@&QA%112&QH&QO&QE&QD%43321q0QH1%:6QD9<?71&Q@%11QF&:&8&9(=&R2&R1&R3%43321&QN&R0%73B21%;5R2:941p0=1p0@1p0L1p0Q01p0Q41p0Q71p0Q;1p0Q>1p0QA1p0QD1p0QH1p0RD1p0RI1p0S21p2S:1p>S<1p4S>1p@S@1").
Proof.
intros L C IL BUDGET B1 B2 LY LV H1 H1n H2 H3 H3e HG H5 H6 H7 H8.
apply (ubjson_pm_asan_base_abort_modulo L C IL BUDGET B1 B2 LY); try assumption.
intros ar HIR OK IC EX GP. destruct (LV ar HIR OK IC EX GP) as (LCC & LCD & PMI & PMIU & ASH & ADL & PARSE).
exact (@PMACL.deps_closed ScfgP_cfg0 L ar C IL HIR LY OK IC (proj1 H6) EX LCC LCD PMI PMIU ASH ADL PARSE).
Qed.
End FPX_1.
