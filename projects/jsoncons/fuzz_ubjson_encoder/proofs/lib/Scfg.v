(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import BMode.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require KReplay.
Ltac2 kr_t_Scfg () := "C4ELinuxProcessSemantics?LinuxProcessSem2Fs4pathC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic7f_equalC47Corelib4Init5Logic8eq_ind_rC46Stdlib5Lists4List8nil_consC4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC47Corelib4Init9Datatypes3appC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC4ELinuxProcessSemantics?LinuxProcessSem5State7PipeBufI47Corelib4Init9Datatypes6option00K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02K47Corelib4Init9Datatypes4list01K4ELinuxProcessSemantics?LinuxProcessSem3Run;InjectedArm01K47Corelib4Init9Datatypes6option01K47Corelib4Init5Logic2eq01I4ELinuxProcessSemantics?LinuxProcessSem3Run;InjectedArm00K47Corelib7Numbers7BinNums8positive03K4ELinuxProcessSemantics?LinuxProcessSem3Run>SpuriousFamily01I47Corelib7Numbers7BinNums1Z00C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm6Mremap=mremap_errnosC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap;mmap_errnosC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm8Mprotect?mprotect_errnosK4ELinuxProcessSemantics?LinuxProcessSem3Run>SpuriousFamily02C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Fs4Open=openat_errnosK47Corelib4Init9Datatypes6option02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C4ELinuxProcessSemantics?LinuxProcessSem5State9errno_retC4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC46Stdlib4Bool4Bool;orb_false_rK47Corelib4Init9Datatypes4list02C46Stdlib5Lists4List7existsbI47Corelib4Init5Logic2eq00C4ELinuxProcessSemantics?LinuxProcessSem3Run=ret_in_errnosI47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool02C4ELinuxProcessSemantics?LinuxProcessSem5State8in_sysnoC45stdpp9bitvector;definitions;bv_unsignedC4ELinuxProcessSemantics?LinuxProcessSem3Run<injected_armC4ELinuxProcessSemantics?LinuxProcessSem3Run9ia_familyC4ELinuxProcessSemantics?LinuxProcessSem3Run?family_may_failC47Corelib4Init9Datatypes4negbC4ELinuxProcessSemantics?LinuxProcessSem3RunCinjected_family_offI4ELinuxProcessSemantics?LinuxProcessSem3Run;SpuriousCfg00I4ELinuxProcessSemantics?LinuxProcessSem5State<SyscallInput00C56Stdlib6ZArith6BinInt1Z3eqbC4ELinuxProcessSemantics?LinuxProcessSem5State6in_argC4ELinuxProcessSemantics?LinuxProcessSem3Run=brk_refusal_bC4ELinuxProcessSemantics?LinuxProcessSem3Run9ia_errnosC56Stdlib6ZArith6BinInt1Z6eqb_eqC47Corelib4Init5Logic9False_indC4ELinuxProcessSemantics?LinuxProcessSem3Run9refusal_bK47Corelib4Init9Datatypes4bool01I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00K47Corelib4Init9Datatypes3nat01I47Corelib4Init5Logic3and00c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4Scfg@injected_arm_214C13~~~I47Corelib4Init5Logic4True00I47Corelib4Init5Logic5False00K47Corelib4Init5Logic4True01C47Corelib4Init5Logic3notc79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4Scfg?ret_in_errnos_1C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4Scfg@refusal_b_errnosC13~~~C4ELinuxProcessSemantics?LinuxProcessSem5State6ENOMEMI47Corelib7Numbers7BinNums8positive00c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4Scfg@injected_arm_222C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4Scfg@injected_arm_226C13~~~I47Corelib4Init5Logic2or00C4ELinuxProcessSemantics?LinuxProcessSem3Run8sc_allocc79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4Scfg@injected_arm_216C13~~~C4ELinuxProcessSemantics?LinuxProcessSem3Run5sc_fsc79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4Scfg?injected_arm_56C13~~~C4ELinuxProcessSemantics?LinuxProcessSem3RunJspurious_refusal_family_onC4ELinuxProcessSemantics?LinuxProcessSem3RunLspurious_refusal_not_refusalI47Corelib4Init9Datatypes4list00C4ELinuxProcessSemantics?LinuxProcessSem5Specs<syscall_specC4ELinuxProcessSemantics?LinuxProcessSem5State7eff_retC4ELinuxProcessSemantics?LinuxProcessSem3RunDspurious_refusal_cfgI47Corelib4Init5Logic2ex00K4ELinuxProcessSemantics?LinuxProcessSem5Monad7outcome01I4ELinuxProcessSemantics?LinuxProcessSem5State=SyscallEffect00I4ELinuxProcessSemantics?LinuxProcessSem5State5event00K47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>ms_svc_pendingC4ELinuxProcessSemantics?LinuxProcessSem3Run9sys_inputc79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4Scfg6fam_onC13~~~I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4Scfg;fam_on_noneC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4Scfg>fam_on_mayfailC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4Scfg<fam_on_sysnoC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4Scfg?injected_arm_94C13~~~K4ELinuxProcessSemantics?LinuxProcessSem3Run6config01I4ELinuxProcessSemantics?LinuxProcessSem3Run5sstep00I4ELinuxProcessSemantics?LinuxProcessSem3Run9sstep_cfg00I47Corelib4Init9Datatypes4prod00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C4ELinuxProcessSemantics?LinuxProcessSem3Run?mi_account_stepK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01K4ELinuxProcessSemantics?LinuxProcessSem3Run7step_to01K4ELinuxProcessSemantics?LinuxProcessSem3Run9sstep_cfg01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02K4ELinuxProcessSemantics?LinuxProcessSem3Run9sstep_cfg02K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03K4ELinuxProcessSemantics?LinuxProcessSem3Run9sstep_cfg03C4ELinuxProcessSemantics?LinuxProcessSem5State8m_haltedC4ELinuxProcessSemantics?LinuxProcessSem5StateGsyscall_effect_accessesC4ELinuxProcessSemantics?LinuxProcessSem5StateJmaterialize_model_accessesC4ELinuxProcessSemantics?LinuxProcessSem3Run<apply_effectC4ELinuxProcessSemantics?LinuxProcessSem3Run@advance_past_svcc79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4Scfg?not_spurious_onC13~~~K4ELinuxProcessSemantics?LinuxProcessSem3Run9sstep_cfg04K4ELinuxProcessSemantics?LinuxProcessSem3Run9sstep_cfg05C4ELinuxProcessSemantics?LinuxProcessSem5State8m_killedC4ELinuxProcessSemantics?LinuxProcessSem5State4m_fsK4ELinuxProcessSemantics?LinuxProcessSem3Run9sstep_cfg06K4ELinuxProcessSemantics?LinuxProcessSem3Run9sstep_cfg07K4ELinuxProcessSemantics?LinuxProcessSem5Monad7outcome02K4ELinuxProcessSemantics?LinuxProcessSem3Run9sstep_cfg08K47Corelib4Init9Datatypes4prod01K4ELinuxProcessSemantics?LinuxProcessSem5State5event03K4ELinuxProcessSemantics?LinuxProcessSem5State5event04I4ELinuxProcessSemantics?LinuxProcessSem3Run6config00I4ELinuxProcessSemantics?LinuxProcessSem3Run7step_to00K4ELinuxProcessSemantics?LinuxProcessSem3Run7step_to02C4ELinuxProcessSemantics?LinuxProcessSem3Run6cfg_msc79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4ScfgBsstep_cfg_of_sstepC13~~~C4ELinuxProcessSemantics?LinuxProcessSem3Run=sstep_cfg_subI4ELinuxProcessSemantics?LinuxProcessSem3Run8star_cfg00K4ELinuxProcessSemantics?LinuxProcessSem3Run8star_cfg01K4ELinuxProcessSemantics?LinuxProcessSem3Run8star_cfg02C46Stdlib5Lists4List9app_nil_rC46Stdlib5Lists4List9app_assocC4ELinuxProcessSemantics?LinuxProcessSem3Run<star_cfg_indC4ELinuxProcessSemantics?LinuxProcessSem3Run9is_prefixC4ELinuxProcessSemantics?LinuxProcessSem3Run9cfg_modelc79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4ScfgEsstep_cfg_halted_noneC13~~~C4ELinuxProcessSemantics?LinuxProcessSem3RunAreaches_error_cfg".
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma injected_arm_214 : injected_arm 214 = Some (mkInjectedArm 214 FamAlloc []).
Proof.
ltac2:(KReplay.run1 (kr_t_Scfg ()) [] "p;1p;3p;2p10000p4p70R0p1000`p4p710R1p8P0p1001<p4p710R2p8P0p1001Zp4p7210R3p8P0p10027p4p710R0p8p1002Up4p710R4P1p8p10032p4p70R5P1p8P5P4p8P5P2p8P5P3p8P5P0p8P5p1003`p4p710p8p1004=p4p7210R5P1p8P5P2p8P5P3p8P5P0p8p1004ip4p70R5P1p8P5P2p8P5P3p8P5P0p8g005_j17Tg006Aj10Tg006fj11Tg007Kj12Tg007ij16Tg008Ij35Tg009Cj24Tg009ej23Tg00:?R0#7g00;9#0#1#0#1#0#0#1#2g00;^g00<[#635,40'3o"). Qed.
Lemma injected_arm_216 : injected_arm 216 = Some (mkInjectedArm 216 FamAlloc mremap_errnos).
Proof.
ltac2:(KReplay.run1 (kr_t_Scfg ()) [] "p;1p;3p;2g005_j16Tg006Aj11Tg006fj10Tg007Kj12Tg008Ij35Tg009Cj24Tg009ej23Tg00:?R0#6g00;9#1#0#1#1#0#0#0#2g00;^g00=935,40'3o"). Qed.
Lemma injected_arm_222 : injected_arm 222 = Some (mkInjectedArm 222 FamAlloc mmap_errnos).
Proof.
ltac2:(KReplay.run1 (kr_t_Scfg ()) [] "p;1p;3p;2g005_j16Tg006Aj10Tg006fj11Tg007Kj12Tg008Ij35Tg009Cj24Tg009ej23Tg00:?R0#6g00;9#0#1#0#0#0#0#1#2g00;^g00>=35,40'3o"). Qed.
Lemma injected_arm_226 : injected_arm 226 = Some (mkInjectedArm 226 FamAlloc mprotect_errnos).
Proof.
ltac2:(KReplay.run1 (kr_t_Scfg ()) [] "p;1p;3p;2g005_j16Tg006Aj11Tg006fj10Tg007Kj12Tg008Ij35Tg009Cj24Tg009ej23Tg00:?R0#6g00;9#1#1#0#0#0#1#0#2g00;^g00?=35,40'3o"). Qed.
Lemma injected_arm_56 : injected_arm 56 = Some (mkInjectedArm 56 FamFs openat_errnos).
Proof.
ltac2:(KReplay.run1 (kr_t_Scfg ()) [] "p;1p;3p;2g005_j16Tg006Aj11Tg006fj10Tg007Kj12Tg008Ij35Tg009Cj24Tg009ej23Tg00:?R0#6g00;9#1#1#0#0#0#2g00@Eg00AB35,40'3o"). Qed.

(* [comment removed for export] *)
Lemma injected_arm_29 : injected_arm 29 = None.
Proof.
ltac2:(KReplay.run1 (kr_t_Scfg ()) [] "p;1p;2g005_j12Tg00BDj11Tg009ej20Tg00:?R0#2%10'0o"). Qed.  (* [comment removed for export] *)
Lemma injected_arm_57 : injected_arm 57 = None.
Proof.
ltac2:(KReplay.run1 (kr_t_Scfg ()) [] "p;1p;2g005_j12Tg00BDj11Tg009ej20Tg00:?R0#2%10'0o"). Qed.  (* [comment removed for export] *)
Lemma injected_arm_63 : injected_arm 63 = None.
Proof.
ltac2:(KReplay.run1 (kr_t_Scfg ()) [] "p;1p;2g005_j12Tg00BDj11Tg009ej20Tg00:?R0#2%10'0o"). Qed.  (* [comment removed for export] *)
Lemma injected_arm_64 : injected_arm 64 = None.
Proof.
ltac2:(KReplay.run1 (kr_t_Scfg ()) [] "p;1p;2g005_j12Tg00BDj11Tg009ej20Tg00:?R0#2%10'0o"). Qed.  (* [comment removed for export] *)
Lemma injected_arm_66 : injected_arm 66 = None.
Proof.
ltac2:(KReplay.run1 (kr_t_Scfg ()) [] "p;1p;2g005_j12Tg00BDj11Tg009ej20Tg00:?R0#2%10'0o"). Qed.  (* [comment removed for export] *)
Lemma injected_arm_93 : injected_arm 93 = None.
Proof.
ltac2:(KReplay.run1 (kr_t_Scfg ()) [] "p;1p;2g005_j12Tg00BDj11Tg009ej20Tg00:?R0#2%10'0o"). Qed.  (* [comment removed for export] *)
Lemma injected_arm_94 : injected_arm 94 = None.
Proof.
ltac2:(KReplay.run1 (kr_t_Scfg ()) [] "p;1p;2g005_j12Tg00BDj11Tg009ej20Tg00:?R0#2%10'0o"). Qed.  (* [comment removed for export] *)
Lemma injected_arm_96 : injected_arm 96 = None.
Proof.
ltac2:(KReplay.run1 (kr_t_Scfg ()) [] "p;1p;2g005_j12Tg00BDj11Tg009ej20Tg00:?R0#2%10'0o"). Qed.  (* [comment removed for export] *)
Lemma injected_arm_215 : injected_arm 215 = None.
Proof.
ltac2:(KReplay.run1 (kr_t_Scfg ()) [] "p;1p;2g005_j12Tg00BDj11Tg009ej20Tg00:?R0#2%10'0o"). Qed.  (* [comment removed for export] *)

Lemma ret_in_errnos_1 : forall e r, ret_in_errnos [e] r = bv_eqb r (errno_ret e).
Proof.
ltac2:(KReplay.run1 (kr_t_Scfg ()) [] "h01eh11rp;1p;3p;2g006fj10Tg00Bfj1:Tg00CDj17Tg00Cgj11Tg00D_j33Tg00ELj19Tg007ij18Tg00Ekj36Tg00FKj35Tg00Fgj32Tg00GAj24Tg00<[R0g00;9#0#0#0#0#0#0#:R1#7f0R2f1R3#1531R4#9g00H;R5%129313X00%809603R3550;24e1432=254eW1W0o"). Qed.

Lemma ret_in_errnos_nil : forall r, ret_in_errnos [] r = false.
Proof.
ltac2:(KReplay.run1 (kr_t_Scfg ()) [] "h01rp;1p;2g006fj10Tg00Bfj13Tg00CDj12Tg009ej21Tg00;9#0#0#0#0#0#0#3#2g00H;g00H['1W0o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma injected_family_off_none : forall cfg i,
  injected_arm (bv_unsigned (in_sysno i)) = None ->
  injected_family_off cfg i = false.
Proof.
ltac2:(KReplay.run1 (kr_t_Scfg ()) [] "p'0h01Hh13cfgh21ih31oi001ai011xp;1p;2p;3p;6g005_R0j1=Tg006fj10Tg00Bfj18Tg00I;j13Tg00J2j24Tg00J\j12Tg00BDj1;Tg00Fgj31Tg00KUj17Tg00LKj26Tg00MGj15Tg009ej29Tg0027j6:Tg00Mej2<Tg00Neg00O_g00:?R1#=R2g00;9#0#0#0#0#0#0#8R3f0R4#3'4#2%;1R531P2P5g00H;R5P0P1P5P4f4%74'6#5g00H[R1n10110100021010000;11X321951f1R2#3,43#2P4E:f2/<2=151eW0W2W1o"). Qed.

Lemma injected_family_off_some : forall cfg i a,
  injected_arm (bv_unsigned (in_sysno i)) = Some a ->
  injected_family_off cfg i = negb (family_may_fail cfg (ia_family a)).
Proof.
ltac2:(KReplay.run1 (kr_t_Scfg ()) [] "p'0h01Hh11ai001ah23cfgh31ih41oi011xp;1p;2p;3p;6g005_R0j1=Tg006fj10Tg00Bfj1;Tg00I;j15Tg00J2j28Tg00J\j17Tg009Cj26Tg00Fgj33Tg00KUj12Tg00LKj24Tg00MGj11Tg009ej29Tg0027j6:Tg00Mej2<Tg00Neg00O_g00:?R1%=1R2g00;9#0#0#0#0#0#0#;R3f1R4#5'8#7f0R5,6133P21614g00H;R6P0P1P6P5f5%25'4#1g00H[n10110100021010000f4f2R1#2'4#133X42f3R2%24'4#1R4,96%51,83#7P5E:1<21=364eW0W1W3W2o"). Qed.

Lemma refusal_b_none : forall i m r,
  injected_arm (bv_unsigned (in_sysno i)) = None ->
  refusal_b i m r = false.
Proof.
ltac2:(KReplay.run1 (kr_t_Scfg ()) [] "p'0h01Eh11Hh21mh32H0h41nh51oi001oh61bi011bh71eh81ih91rh:1zi021ai031xp;1p;2p;3p;6g006fj11Tg00Bfj1JTg00CDj1ATg005_R0j1>Tg00I;j12Tg00J2j23Tg00J\j16Tg00BDj1@Tg00Fgj30Tg006Aj17Tg007Kj1=Tg00P\j24Tg009ej2:Tg00Q9j2<Tg00Qnj3;Tg00Rhj1ITg00GAj2HTg00S^j2FTg000`j68Tg007ij1ETg008Ij3BTg009Cj2CTg00T>j2DTg0027j6?Tg00T]j3GTg00H;R1f0R2g00H[R330p=5g00US9012p=9g00O_g00V3g00;9R4#1#1#1#1#1#1#JR5#Ag00:?R6#>R7f2R8#2,35#6%@6R930f3R:#2,35%74#1#7#1#7#7#1#=R4'4P11:12f4#2,35/44=012P1f6R;#2,35R</44=012P1P1f1R=f7R>g00ViR?'<f5R@5;;P0P6P1%2>,35R>#6%I2/H;R;P3n10110300021010200n0100000020000#5]0P=%2@,35/44RA#9g00<[RBg00WH14=2#9A0B8=[RCA0B=2148=#9RD[A0B:8\D1F=2P=n2001000000120000000X2BW4PC^2B^4BP2P>P4P=O3A0B>4PBf8#2,35%62=079X:BP@P4P2E8%64R@=079P7P@A0729X57P2g00;^%EB5B4,C6R4g00WcE8A0749P7P4P0P6p-0P2g00Y3g00YOR4n10110000021000000X77g00YlP9P2E8P4f:f;/<?f93;#5/D2b3b1b1b0b3W0%5AP7P9P0P6P1P2P;P3n10110300021010200#5X571:13%6<P:E?W0n0110100020100P2O1b0b6AG:8=#5eW1W9W2W8o"). Qed.

Lemma refusal_b_errnos : forall i m r a,
  bv_unsigned (in_sysno i) <> 214%Z ->
  injected_arm (bv_unsigned (in_sysno i)) = Some a ->
  refusal_b i m r = ret_in_errnos (ia_errnos a) r.
Proof.
ltac2:(KReplay.run1 (kr_t_Scfg ()) [] "p'0h01Eh11mh21nh31Hh42H0h53Hneh61ai001ah71bi011bh81ih91oh:1ri021xp;1p;2p;3p;6g006fj11Tg00Bfj1GTg00CDj1BTg00I;j13Tg00J2j22Tg006Aj18Tg007Kj1FTg00Fgj30Tg00ZHj1@Tg005_R0j1?Tg00J\j19Tg009Cj2;Tg00P\j24Tg009ej2>Tg00Q9j2=Tg00Qnj3<Tg00Rhj16Tg00GAj27Tg00S^j2ETg00T>j2DTg0027j6ATg00T]j3CTg00H;R1f1R2f0R330p=5g00US9013p=:g00O_g00V3g00;9R4#1#1#1#1#1#1#GR5#Bg00:?R6g00<[R7f3R8#3,25%84#1#8#1#8#8#1#FR430#@%?6R9f4R:#3,25#91;6230f5R;#3,25/44P11>13f6R<#3,25/44/53P1f8R=#3,25R>/44/53P1P1P2f9R?g00ViR@'=f7RA5<=P0P6P1%3?,25RB#9%63/7=RCg00H[RDn10110200021010000n0100000020000%6</7ARE'5]0P2%3A,25/44R5#:g00WH1423#:f2RF=072[RGA072314F2#:RH[A078F\H1E23P2n2001000000120000000X17X27PG^17^27P3PBP4P2O3A07B4f:/=@=<?=%6A/7='5P<P3O1'Db0b4W0A015DP91;6;P0P6P1P3PCPDn10110200021010000/5EX99%6;/7<,>1%9>P8EAW0n0110100020000P3O1b0b7AC;:8%6F/78'5eW3W5W6W:W1W8o"). Qed.

Lemma refusal_b_brk : forall i m r,
  bv_unsigned (in_sysno i) = 214%Z ->
  refusal_b i m r = brk_refusal_b m (in_arg i 0) r.
Proof.
ltac2:(KReplay.run1 (kr_t_Scfg ()) [] "p'0h01Hh11ih21mh31rh41zi001ai011xp;1p;2p;3p;6g006fj10Tg00Bfj1@Tg00CDj19Tg00I;j15Tg00J2j26Tg006Aj11Tg007Kj1;Tg00Fgj32Tg00P\j28Tg00Q9j23Tg00Qnj34Tg00J\j17Tg00Rhj1:Tg00GAj2?Tg009ej2>Tg0027j6=Tg00T]j3<Tg00O_g00V3g00;9R0#0#0#0#0#0#0#@R1#9g00<[R2f2R3#5,61%10#0#1#0#1#1#0#;R032P2P0g00H;R4P4P4f0R5/80f3R0f4g00ViR6'3;43R7g005_g00:?P4%75%:5/?0g00H[n10110100021010000n0100000020000;27X421306f1R6543R2,>4%50,61P5E=A<036=242eW0W3W2W1o"). Qed.

Lemma refusal_b_mmap : forall i m r,
  bv_unsigned (in_sysno i) = 222%Z ->
  refusal_b i m r = bv_eqb r (errno_ret ENOMEM).
Proof.
ltac2:(KReplay.run1 (kr_t_Scfg ()) [] "p'0h01zi001zh11Hh22H0h32H1h41bh51eh61ih71mh81ri011pp;1p;2p;3p;6g006fj10Tg00Bfj1FTg00CDj1>Tg00I;j17Tg00J2j29Tg006Aj11Tg007Kj16Tg00Fgj32Tg008Ij3<Tg00Rhj1;Tg00GAj24Tg00Cgj1:Tg00D_j35Tg00Zaj2ETg00T]j3DTg00ZHj18Tg000`j6CTg00T>j2BTg0027j63Tg005_j1?Tg00J\j1@Tg009Cj2ATg00\0j6=Tg00O_g00V3g00;9R0#0#0#0#0#0#0#FR1#>g00<[R2f2R3#7,91%10#0#1R0#1#1#1#0#6R432g00H;R5g00;^g00>=R65<4R7#;f1R8'4R9f0R:g00]@R;#:R<9513525X451E;81468A518<R<525eA259<ef3R<?D38P<P3P8P7P2P4%00#1#1#0#6R0922:#8X02A2240R8P2P4P2p-0R3P:g00YOR9g00^5R5P3P:P9P5P3P:P5P3P:P5P3P:g00Y3P9P9n011010003100001000000P9P9n011010003101011010100P9P9n011010003101011010100P9n011010003101011010100P9n011000003001010110101X52g00YlP0P:ECP91B9:b3W2%88e%7<,91R1P:E3P2P4g00:?R4#?%@:1A4732X02g00^ZP1P:E3E=E3W1W8W7W6o"). Qed.

Lemma refusal_b_mprotect : forall i m r,
  bv_unsigned (in_sysno i) = 226%Z ->
  refusal_b i m r = bv_eqb r (errno_ret ENOMEM).
Proof.
ltac2:(KReplay.run1 (kr_t_Scfg ()) [] "p'0h01zi001zh11Hh22H0h32H1h41bh51eh61ih71mh81ri011pp;1p;2p;3p;6g006fj10Tg00Bfj1FTg00CDj1>Tg00I;j17Tg00J2j29Tg006Aj12Tg007Kj16Tg00Fgj31Tg008Ij3<Tg00Rhj1;Tg00GAj24Tg00Cgj1:Tg00D_j35Tg00Zaj2ETg00T]j3DTg00ZHj18Tg000`j6CTg00T>j2BTg0027j63Tg005_j1?Tg00J\j1@Tg009Cj2ATg00\0j6=Tg00O_g00V3g00;9R0#0#0#0#0#0#0#FR1#>g00<[R2f2R3#7,91%20R0#2#0#0#0#2#0#6R431g00H;R5g00;^g00?=R65<4R7#;f1R8'4R9f0R:g00]@R;#:R<9513515X451E;81468A518<R<515eA159<ef3R<?D38P<P3P8P7P2P4%00#2#0#2#2#0#6R0912:#8X02A1240R8P2P4P2p-0R3P:g00YOR9g00^5R5P3P:P9P5P3P:P5P3P:P9g00Y3P9n011010003100001000000P9P9n011010003101011010100P9n011010003101011010100P9n011000003001010110101X52g00YlP0P:ECP91B9:b3W2%88e%7<,91R1P:E3P2P4g00:?R4#?%@:1A4731X02g00_jP1P:E3E=E3W1W8W7W6o"). Qed.

Lemma injected_family_off_alloc : forall cfg i n,
  bv_unsigned (in_sysno i) = n ->
  (n = 214 \/ n = 216 \/ n = 222 \/ n = 226)%Z ->
  injected_family_off cfg i = negb (sc_alloc cfg).
Proof.
ltac2:(KReplay.run1 (kr_t_Scfg ()) [] "p'0h02Hnh11Hh21nh31oh46Hcasesh53cfgh61ih71zi001ai011xp;1p;2p;3p;6p;7g00Bfj1JTg006Aj15Tg006fj13Tg007Kj1=Tg00J\j14Tg00KUj1BTg00LKj29Tg00MGj18Tg005_R0j1ITg007ij1HTg008Ij3?Tg009Cj2>Tg009ej2ATg0027j6:j7<Tg00Mej2FTg00I;j1ETg00J2j2DTg00Fgj3@Tg00a:R1j2CTg00aTj1GTf0R2#3#3p=;f1R3%E2'Dp=7g00<[R4?@32p=0f2R5=@43/C2p=2%G2#8p=6g00H;R6?@32p=1g00Neg00O_g00;9R7#;#;#;#JR8/73/02%57R7#3#5R9#3#5#5#3#=R:%59R9#3#;#=R;%59#5#3#=R9%57#3#;#5#3#=R7,03523523523P4P5P0g00:?R<P6%42f6R=%B2R>'9#8R?g00H[R@n10110100021010000f5RA#6RB'1X74P1105:10579259925;P0P<P6f3R5#4P?P@n10110100021010000/1BP2105:P4P:178=/02P0P<P6%43RBf9R?/9>#8RCP@n10110100021010000f8RD#6RE'1]0X24178A/0:%I<RFg00;^RG%H45?:,><P0P<P6P2PCP@n10110100021010000/1EX3Ff7RE#6RC,A6%4:g00WcE:W0f4R:P2P5F<W1P2O110579259925;P110:;10:792:9P0P<P6%4A19D>#8P@n10110100021010000/1CP210A;P4P;178D/02P0P<P6PBf;RC/9>#8RHP@n10110100021010000f:RI#6RJ'1]0X24178E/0;PFg00=99?;G,><P0P<P6P2PHP@n10110100021010000/1JX3F%6?RJ,A6%4;g00bIE:W0P=P2PAF<W1P2O110A792A9P110=910=7P0P<P6%4E19I>#8P@n10110100021010000/1JP210E9P4P9178I/02P0P<P6PBf=/9>#8R>P@n10110100021010000f<#6RB'1]0X24RI178?R?/09PFg00>=9?9G,><P0P<P6P2P>P@n10110100021010000/1BX3FRB%6C,A6R6%49g00^ZE:W0PDP2PEF<W1P2O110E7P4P7PI10?7PFg00?=9?7G,><PBP6%47g00_jE:W0PDP2PEF<W1P2O1n200100000021000010000W1P2O1n200100000021000011000W1P2O1n2001000000210000110001785P3E:1F:5%6:'1eW4W0X24W6W5o"). Qed.

Lemma injected_family_off_openat : forall cfg i,
  bv_unsigned (in_sysno i) = 56%Z ->
  injected_family_off cfg i = negb (sc_fs cfg).
Proof.
ltac2:(KReplay.run1 (kr_t_Scfg ()) [] "p'0h02Hnh13cfgh21ih31oh41zi001ai011xp;1p;2p;3p;6g006fj10Tg00Bfj1ATg00I;j15Tg00J2j26Tg006Aj18Tg007Kj1<Tg00Fgj31Tg00J\j13Tg00KUj1;Tg00LKj2:Tg00MGj12Tg00cYj14Tg005_R0j19Tg008Ij3@Tg009Cj2?Tg009ej2>Tg0027j67Tg00Mej2=Tg00Neg00O_g00<[R1g00;9R2#0#0#0#0#0#0#AR3f0R4#5'6%82#8#0#0#0#<R231P1P2g00H;R5P0g00:?R6P5%34f4%;4':#2R7g00H[R8n10110100021010000f3#4#2R931X41%96R1g00@Eg00AB5@2,?6P0P6P5P4P7P8n10110100021010000=159X31f2R1#4#2R9,>5%32g00dKE7f1R2#5,63P4E71=12=159eW0W2W1o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma not_spurious_on : forall cfg i m eff,
  injected_family_off cfg i = false -> ~ spurious_refusal_cfg cfg i m eff.
Proof.
ltac2:(KReplay.run1 (kr_t_Scfg ()) [] "g00eZo"). Qed.

Lemma not_spurious_nonrefusal : forall cfg i m eff,
  refusal_b i m (eff_ret eff) = false -> ~ spurious_refusal_cfg cfg i m eff.
Proof.
ltac2:(KReplay.run1 (kr_t_Scfg ()) [] "g00fao"). Qed.

Lemma not_spurious_forced : forall cfg i m eff,
  (forall eff' m' evs', syscall_spec i m (Ok eff' m' evs') ->
     refusal_b i m (eff_ret eff') = true) ->
  ~ spurious_refusal_cfg cfg i m eff.
Proof.
ltac2:(KReplay.run1 (kr_t_Scfg ()) [] "p'0h04evs'h12m'h21Hh34eff'h43Hnrh54Hallh65Hspech72_Hh83_H0h91bi001bh:3cfgh;1eh<3effh=1ih>1mi011xp;1p;3p;4p;2p;6g00gjj1BTg00hJj38Tg00iEj12Tg00T]j33Tg00j;j4=Tg00Mej2;Tg00k<R0j20Tg00WHR1j29Tg000`j6<Tg00Fgj37Tg00T>j2@Tg00ZHj1?Tg00kVj4>Tg00lNR2f2R3f1R4f0R5C>p=5g00H;R6g00USR7775p=4f5R8f4R9f3R:38A3345g00H[R;576'9p=1g00V3R</05p=6A3345=76;p=:A765;p=Ag00Neg00O_g00mL#BR=A5345R>9889f6R?%2:R@738#4[]0^1<^32P9P:P3P4C=RAP11;89#4%23RB939:#4f7RCP?P>PCP?PBE1X0=,0=X1<#6X32,02'9g00YORDP51;C?#4%28RE93C?#4f:RFf9RGP>PFPGPBE1X0=,0=X1<#6X32,02'9P1f8RH%2?RI73C#4f;RJPFP>PJPFPBE1X0=,0=X1<#6X32,02PDP5%2HRK93FG#4f>RFf=RLP>PFPLPBE1X0=,0=X1<#6X32,02P0P2f?RMPFP>PMPFPBE1X0=,0=X1<#6X32PDP5fARFf@RMP>PFPMPBE1X0=,0=X1<#6P0P<fBRBPFA5:45PBPFP@E1X0=,0=X1<PDP5fDR@fCRFA5845P@PFPEE1X0=,0=P0P=fER0P@A5?35P0P@PIE1X0=PDP5fGRIfFR@A5H95PIP@PKE1P1fHR1A5G8478I%2G9:1IPDP5fJR1fIRIA5JC:38fKRJf<#27:1P6fL%2L73J%A5X96P5P7PIPLPGP8P4O4E<A767;P6P7P6p-0P5g00Y3PDn0110000020000X;6g00YlP;P5E<PD1@D5b2b4W4W6P4P5O2n2001000000120000000W2X0=P4P5O2n2001000000120101000W2X1<P4P5O2n2001000000120101000W2X32P4P5O2n2001000000120101000W2W8P4P5O2n2001000000121000000W2W7P4P5O2n2001000000121000000W2%?AeW5X<2X><W=W:o"). Qed.

Lemma spurious_intro : forall cfg i m eff eff1 m1 evs1,
  injected_family_off cfg i = true ->
  refusal_b i m (eff_ret eff) = true ->
  syscall_spec i m (Ok eff1 m1 evs1) ->
  refusal_b i m (eff_ret eff1) = false ->
  spurious_refusal_cfg cfg i m eff.
Proof.
ltac2:(KReplay.run1 (kr_t_Scfg ()) [] "h04evs'h12m'h23Hnrh34Hoffh42Hrh55Hspech63cfgh73effh84eff'h94eff1h:4evs1h;1ih<1mh=2m1p;1p;2p;3p;4g00gjj1<Tg00Mej2;Tg00iEj11Tg00T]j30Tg00kVj44Tg00hJj32Tg00WHj26Tg00k<j25Tg00nBj49Tg00n]j48Tg00Fgj3:Tg00H;R0f0R1g00US3:p=7g00H[9:01p=3g00Neg00O_g00V3R0g00lNR2g00mL#<R3f6R4f5R5';#7f4R6#19045#7f7R7P2P6f3R8f2R9C4724f8R:%15707#3f:R;f9R<';#7%17R=90<:#7R>f<R?f;R@P2P9f1RAP1C432%1990?@#3'6X03,53X10,50X82R?,52RB'6P8P>PBP9P2P?P4P0P2P:PAP1C492@;%1:90@;#3'6X03,53X10P5P3P2P7P4P1C492;<A0;<=#3'6X03P6P2P4P5P6C492<:%1490<:#3PAP1C9C8C8C8C9C9W2W5W4W3W:X=0X92W7W<W;W6o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section WithSegs.
Variable segs : list Segment. Context {bmK : BMode}.   (* [comment removed for export] *)
Variable scfg : SpuriousCfg.

(* [comment removed for export] *)
Definition fam_on (ms : machine_state) : Prop :=
  forall x8, ms_svc_pending ms = Some x8 ->
    injected_family_off scfg (sys_input segs ms x8) = false.

Lemma fam_on_instr : forall ms, ms_svc_pending ms = None -> fam_on ms.
Proof.
ltac2:(KReplay.run1 (kr_t_Scfg ()) ["WithSegs"] "p'0h02Hxh11Hh22H0h31eh42msh51oi001oh62x8p;1p;3p;2p;6g006fj10Tg00Bfj1<Tg00CDj16Tg005_R0j15Tg00o7j13Tg00BDj1;Tg00Fgj31Tg009Cj22Tg000`j64Tg010=j37Tg00Mej28Tg00T>j29Tg0113j1:Tg0129g00;9#0#0#0#0#0#0#<#6R1#5R2f0R3#3%;1R431f2R5#31213512P2f3R6#31215R79123X52P3P4P5E4f1R5,219124P2P4P0P1p-0P3g00YOR0g00Y3n10110000021000000X32g00YlP7P3E4P0g00H;p,4scfgp,4segsf5;76'8g00H[31/93b2b0W0X61%:5eW1W4o"). Qed.

Lemma fam_on_none : forall ms x8,
  ms_svc_pending ms = Some x8 ->
  injected_arm (bv_unsigned x8) = None ->
  fam_on ms.
Proof.
ltac2:(KReplay.run1 (kr_t_Scfg ()) ["WithSegs"] "p'0h01Hh12Hyh21oi001oh31yh44Harmh54Hsvch61eh72msh82x8i011ai021bi031xp;1p;2p;3p;6g006fj11Tg00Bfj1DTg00CDj1=Tg005_R0j19Tg00o7j13Tg009Cj22Tg00Fgj30Tg00J2j27Tg00J\j16Tg00BDj1<Tg000`j65Tg001Zj6;Tg010=j38Tg00Mej2:Tg00KUj1CTg00LKj2BTg00MGj1ATg009ej2?Tg0027j6>Tg0113j1@Tg00H;R1f0R2g00H[R330p=4g0129g00;9#1#1#1#1#1#1#DR4#=R5%95R6f1R7#31252R830g00:?R9#9R:1747#6%<9R;30f4R<#3=068P6f5R8#3f2R=,25R>9062X26P2125<R?f3R@E51257906?P6P5P0P5P5P2P2f6R?n10110000021010200X661258P>P2E;A058=A05?@P5f7R?p,4scfgR=p,4segsR>f9;82':#4X35P:P;P0P9P1P2%C2,B=#AP3n10110300021010100#4X2:1?13174?#6P8E>f8=8>?,:=#4eP<P2E5W0P2O1b0b1W1X35%@@eW4W5W8W7o"). Qed.

Lemma fam_on_sysno : forall ms x8 n,
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = n ->
  injected_arm n = None ->
  fam_on ms.
Proof.
ltac2:(KReplay.run1 (kr_t_Scfg ()) ["WithSegs"] "h01nh11Hh24Harmh34Hsvch42msh52x8p;1p;2p;3p;4p;6g006fj10Tg00Bfj1<Tg00CDj16Tg005_j14Tg00o7j1;Tg009Cj2:Tg00Fgj31Tg00J2j22Tg00J\j13Tg00BDj17Tg0113j15Tg013@j48Tg000`j69Tg0129g00;9#0#0#0#0#0#0#<R0#6R1g00<[R2%41f2R3#;f1R4,:1311203=124P2f3,20R0g00:?R4#4R1f0R5#3%74R431f6#5[X02%30=114f5f4P3P5C8W2P3P5E9W1W3W0W5W4o"). Qed.

Lemma fam_on_mayfail : forall ms x8 a,
  ms_svc_pending ms = Some x8 ->
  injected_arm (bv_unsigned x8) = Some a ->
  family_may_fail scfg (ia_family a) = true ->
  fam_on ms.
Proof.
ltac2:(KReplay.run1 (kr_t_Scfg ()) ["WithSegs"] "p'0h01Hh12Hyh21oi001oh31yh44Harmh54Hfamh64Hsvch71ai011ah81bi021bh91eh:2msh;2x8i031xp;1p;2p;3p;6g006fj12Tg00Bfj1CTg00CDj1@Tg005_R0j1:Tg00o7j16Tg009Cj21Tg00Fgj30Tg00J2j29Tg00J\j18Tg00KUj14Tg00LKj25Tg000`j67Tg001Zj6?Tg010=j3>Tg00Mej2=Tg00MGj1;Tg009ej2BTg0027j6<Tg0113j1ATg00H;R1f0R2g00H[R330p=3g0129g00;9#2#2#2#2#2#2#CR4#@R5g00:?R6%:5R7f2R8#6f1R9,15R:30%:6R;1948#8116930p,4scfgR9%48'5g00USR<501f6R=#61152507P7f7R>#61158R?9072X27P2115=R@f4RAE7A07@:P7P5P0P5P5P2P2f8R@n10110000021010200X97115>P?P2E?A05>8f3905@P5f9R>p,4segsR8f;;>2,=9#3X35P;116@P0P6P1P2%42,59#;P3n10110300021010100#3X2;P1P<%;2#3X811B13%4@,59f5R@E<194>#8P=E<f:=>8>,=9#3ePAP2E7W0P2O1b0b1W1X35%A@eW5W4W6W7W;W:o"). Qed.

(* [comment removed for export] *)
Lemma fam_on_openat : forall ms x8,
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 56%Z ->
  sc_fs scfg = true ->
  fam_on ms.
Proof.
ltac2:(KReplay.run1 (kr_t_Scfg ()) ["WithSegs"] "h03Hfsh13Hnoh24Hsvch32msh42x8h51zp;1p;2p;3p;6g006fj10Tg00Bfj1>Tg00CDj18Tg005_j14Tg00o7j1=Tg009Cj25Tg00Fgj31Tg00J2j23Tg006Aj12Tg007Kj17Tg00cYj16Tg008Ij39Tg00J\j1:Tg0027j6<Tg014Kj6;Tg0129g00;9R0#0#0#0#0#0#0#>R1#8R2%42f1R3#=f0R4,5231g00<[R21313%20#2#0#0#0#7R031g00H;p,4scfg#6g00US31f4f3R5g00@Eg00AB590R6f2P2P0g00:?R0#4%:4150631X52g00dK1315P3E<P4E;W0W1W2W4W3o"). Qed.

(* [comment removed for export] *)
Lemma fam_on_exit : forall ms x8,
  ms_svc_pending ms = Some x8 -> (bv_unsigned x8 = 93%Z \/ bv_unsigned x8 = 94%Z) -> fam_on ms.
Proof.
ltac2:(KReplay.run1 (kr_t_Scfg ()) ["WithSegs"] "h01Hh12H0h24Hsvch32msh42x8p;1p;2p;3p;6g006fj10Tg00Bfj1=Tg00CDj18Tg005_j17Tg00o7j1<Tg009Cj2;Tg00Fgj35Tg00J2j23Tg006Aj12Tg007Kj14Tg00a:R0j29Tg0113j1:Tg015Yj66Tg00<[f1R1f0R235p=1g0129g00;9#0R3#0#0#0#0#0#=R4#8R5%75%<11;52351341R1%23#2#2R3#0#2#4R5'1%23#0#4R3,11'9P0f2,34R0/151103f4R0#:P2f3R1,34R4/15f5R6P0P5P1P2g016eR5E6W0P2O11143P6P0P3P1P2P5E6W0P2O1n200100000021000010000W1W2W4W3o"). Qed.

(* [comment removed for export] *)
Lemma sstep_cfg_of_sstep : forall ms model e st,
  sstep segs (mkCfg ms model) e st ->
  fam_on ms ->
  sstep_cfg segs scfg (mkCfg ms model) e st.
Proof.
ltac2:(KReplay.run1 (kr_t_Scfg ()) ["WithSegs"] "p'0h02H1h11Hh22H0h32H3h42H2h52H4h63Hssh72H5h82H6h91mh:1li001lh;1si011sh<6model0h=3ms0h>2sth?1eh@6model'i026model'hA2x8i032x8hB3effi043effhC3evsi053evshD2H7hE2e0hF3HonhG1ci061chH4codei074codehI5modeli085modelhJ7model''i097model''hK2msi0:2mshL3ms'i0;3ms'hM3sigi0<3sigi0=9cfg_modeli0>6cfg_msp%0p%1p;1p;2p;4p;3p;5p;9p;7p;6p;?p;>p;=p;8g00gjj1zTg0184j21Tg018iR0j43Tg0113j1jTg00Fgj30Tg019]j52Tg006fj1PTg00Bfj1lTg00CDj1iTg005_j1_Tg00BDj1^Tg00o7j1XTg01:Uj2xTg01;5j1wTg01<=j3ATg01=9j2VTg007ij1tTg01>Aj1JTg01?7l9kTg000`j7;j6<Tg01?oj1hTg01A7j7gTg01Aoj1fTg01C7j7yTg01Coj1QTg009Cj28Tg010=j3ETg01Dfj1NTg01Elj2LTg01G5j2ITg01Gnj1KTg01Hkj5eTg01J:l?vTg0027j6]Tg01K2l>uTg01Kjj1HTg01Laj1:Tg00hJj3UTg01MTl>sTg01NLl=rTg01ODj1qTg01P<j8pTg009ej2\Tg01Q4j4oTg001Zj6aTg00kVj4`Tg01QTj2nTg00Ekj3cTg003`j3dTg01RJj2mTg01S@R1f1R2f0R330p==g01T5R4?023p=bf2R5%Q2;03p=4g0129R6g00V3R7P2P3Cop=S%J2=043p=[P1P7f3R8P5P2P3Eap=TA0723p=6P1P6P8P5P2P3Eap=WA0623p=5%X2=053p=7P7f4R9P8P5P2P3E]p=CP6P9P8P5P2P3E]p=Bg01TkR:=043p=?P8P5P2P3P:D2p=OP4P:P9P8P5P2P3F;p=ZP4P:P8P5P2P3E<p=Yg00lNR;P5P2P3C`9U98p=D18239085p=M1152#J=043p=91123#Jp=>P;P5P2P3C`p=RAE985?U23p=@g00mLR<1n52=c<37d8p=F1m52=c<39d<8p=G%z<R=p,4segsR>1185P2P3C3%j9P0P>f9R0f8R?'1S00,=8A0=8?1b8?P>p,4scfgR@f<RAf;RB'1f:RCP0D2[[[P2g00;9#P#P#P#P#P#P#l#iRD#_RE%^DRF745RG%X9S01=0EFRH1x67RI#wRJf5RK=A>91S85,VI30f6RL/1KS02fCRMfBRN'1RO'=%t<R<=0=NQ02/[NQ00fFRPfERQ'1S03'=P1P7P3P3n0110600012010>10=XE1S0411C0S05fGRR/1PRSP3CT160PP1P6P3P2n0110600012010>10=XE1S0611BCS07fHRT/1RRUP2CW15BTfIRV,5AP3f=RWfJRX'5fKRYf>RZ/6YR[A0=<YR\f?R]/1ZR^/[YfAR_=4EFAA>KM1SN_,VI50JP>P@fRR`fQRa'1S08fPRbfORcD2]0^2H]1]5]3[X9616WXP3P[fLR[A0=<[Rdf@Re/1]S09/[[Rf%XaS0:=0EFAA>`91SMN,VI50JP>P@fSRg/1`S0;PaPbD2]0]2^1G]5]3X97P3PdP=P<11_eS0<fMRd'[RhA4EbFRiA7E`FRjAA>g`fDRk/SM,VI50JRlP>P@fTRm/1gS0=P9PaD2]0]2]1]5X:=P3PhP411N_Rh#JA4EaFA7EgFAA>mg1SQk,VI50JP>P@fURn/1mS0>P<P8D2]0]2]1X;4P=P<P>Q0>P3P`C3P>P@fVRo/1nRpP<%JSD2]6X?=P>Q0=P<PaC3P4Q03#JRSP>PpP<P3C3P>P@fWRp/1oP<%JUD2]6X>4P>Q0>P<PSC3P>P@PoPnPRPPP9P8P5M9kW6P`PKP3F;W6P`PLPbF;X7lX4jX0ifNRiP3E<b0X5fPdP3E<b0X3\P]P3DCb0W2PZP3DBb2W1P3O1b1P3O1b1W4P5P2P3PKP9P8O6W5W3W4W0W2W1X@7XL6X<7X=6PLPKP9P8P5P2P3O7A4E3FS0?A7E5FS0@AA>85R\%hIRf50J1198/=^S0AA0=<ZS0B%?ZS0Cf7Rj/1L/=hS0DQ0411?jS0EPOP3CTS0F16jNS0GQ06Q0011kMS0HP2CWS0I150kS0J15CQS0KP315BPS0LPR16ARROA0=<RRh%?RRlA4E]FRSAA>K_RU=0JfP>P@11idS0MP[PYD2S0N]0^2H]1]5]3[X9616BPRqP3POPTA0=<TRr%?TRsA7EdFRtAA>i9Ru=0JfP>P@11ciS0OPdP[D2S0P]0]2^1G]5]3X97P3PrP=P<%?VRvA4E[FRwA7EiFRxAA>ciRy=0JfRzP>P@11bcS0QP9PdD2S0R]0]2]1]5X:=P3PvA4EdFR{%XcS0S=0EFR|AA>bcR}=0JfP>P@11abS0TP<P8D2S0U]0]2]1X;4P=P<P>Q0TP3PiC3P>P@Q08P<CO]6X?=S0VP>Q0QP<PdC3RfP>Q08P<P3C3P>P@Q0;P<CO]6X>4S0WP>Q0TP<P:C3R~P>P@P`PaP9P8P5FgW6PiPKP3DZW6PiPLP[F;X7zX4xX0wPXP3CYb0X5sPVP3E<b0X3hPWP3DCb0W2PAP3DBb2W1P3O1b1P3O1b1W4P5P2P3PKP9P8O6W5W3W4W0W2W1X<7X=6P9P8P5P2P3O5Q0?Q0@%fIRI90J\Q0AQ0BQ0CQ0DQ0FQ0GQ0IQ0JQ0KP3Q0LPRA0JUIQ0N]0^2H^1S^5l^3h\OX96P3POPTA0JuIQ0P]0^2t^1G^5s^3rX97P3PrP=P<A0JyIRyQ0R]0^2x^1w^5vX:=P3PvA0J}IQ0U]0^2|^1{X;4P=P<Q0VQ0WP>P@P`PaP9P8P5FyX6~PiPKP3DZX6fPiPLP[F;X7yX4xX0wPXP3CYb0X5sPVP3E<b0X3hPWP3DCb0X2qPAP3DBb2W1P3O1b1P3O1b1W4P5P2P3PKP9P8O6W5W3W4W0W2W1X<7X=6P9P8P5P2P3O5%QKS0?=0EFRq18DK97EjS0@AE>?LS0APjPKP9P5DD%_7Rh%Nj,LLP7PKCMQ0711d['=S0BA0=L[1IWC#K?9?[11ZWS0CQ0Q'=S0DQ04P^Q0TP3CTS0K16ZbS0WQ06Q09Q08P2CWS0915e`S0V15_gS0UP315NmS0RPn16MnS0PA0=]nRs1I5M#K?9_n%QPS0N=0EFRwQ0118DPRx50ES0LAE>KRS0JPTPPPQPMDDPh%NT,LRRyP7PPCMP>P@f^Rff]R~'1S0If\R{f[R|D2S0G]3^4w]0]2]1]8]7[X9616NmS0FP3Q0PPoA0=eoRIfYR}/Ik#K?9NoRJ%X|S0X18DRS0Y50ES0ZAE>{TS0[P9PRPPPkDD%QRS0\=0EFS0]Ph%NV,LTS0^P7PRCMP>P@f_Rr/1fRtP~P{D2S0_]3]4]0]2^1G]8]7X97P3PIP=PpfZRI/IQ#K?9MpRuA4EIFRO18DTS0`97E{RlAE>~VS0aP{PTPRP8DD%QTS0b=0EFS0cPh%NX,LVS0dP7PTCMRSP>P@f`RH/1rRUPfP~D2]3]4]0]2]1]8X:=P3PuP41I|P#K/>kA4E|FS0e18DV97E~S0fAE>fXS0gP~PVPTP{DD%QVS0h=0EFPh%NY,LXP7PVCMP>P@faRu/1HR\PrPKD2]3]4]0]2]1X;4Q0aP{PTPRP|DDQ0cP41IHY#K/>VS0iP>P\PrP3C3P>P@fbRz/1uS0jPH1Izd#K/>YD2]6X>4P>PUPfQ0iC3P>P@PuPHPdP[PYPXPrPKP9P8P@AE>udPHP[P{PdP9O2DeP5P2M?vW6P~PLP{F;XDSW5W3X4lX0OfXRSP3E<b0X8JP_P3E]b0X7sPkP3DCb0W2PMP3DBb2W1P3O1b1P3O1b1W5P5P2P3PjPLPKP9P8O8W8W7W5W3X4qW0W2W1XC=XJ7X@7XB;XADX<7X=6PBPCP0P?PjPLPKP9P8P5P2P3O<A4E9FS0i18D997ELP>PjPKPLAR985D@Q0i%NL,LK%^7Rs50hQ0511YX'=S0kA0=<XS0l%?XS0m11WAQ0M'=S0MQ04Q0CQ0OP3CTS0O16WiS0CQ06P^Q0QP2CWS0n15]bS0o15eaS0pP315_`S0qPg16NgS0rA0=<gS0s%?gA4EQFS0tQ0118DQS0u50ES0vP>PKPPPRARQkMD@S0wQ0t%NR,LP=0hsP>P@11{|PIP}D2S0x]3]4]0]2]1]8]7[X9616_`S0yP3Q0rPmA0=<mR^%?mS0zA7E}xS0{P>PIPRP9ARPQkS0|D@S0}A0hysP>P@11~{S0~P|PID2]3^4w]0]2^1G]8]7X97Q0sP3P^P=P<%?nS10A4ESFR^Q0Y97EIRyP>P|PTPIARRPQS11D@RJQ0]Q0^=0hsS0^P>P@Q0IPLP|D2]3]4]0]2]1]8X:=Q0zP3Q10A4E}FS10Q0XQ0`50ES0`P>P{PVP|ARTRPS0XD@S12Q0cQ0d=0hsP>P@PtP<PKD2]3]4]0]2]1X;4Q0]Q0^P=P<P>PtP3P{C3P>P@PUP<CO]6X?=P>Q0IP<P|C3P>PUP<P3C3P>P@P\P<CO]6X>4P>PtP<P:C3P>P@PHPrPdP[PYPXPLPKP9P@AE>HdPrP[P|PdPKO2DeP8P5M>uW6P{PjP3DZW6P{P?PIF;WDW5X3JX4yX0^PoP3CYb0W8PnP3E<b0W7PMP3DCb0W2PNP3DBb2W1P3O1b1P3O1b1W5P5P2P3PjPLPKP9P8O8W8W7W5W3W4W0W2W1XC=X@7XB;XADX<7X=6PCP0P?PjPLPKP9P8P5P2P3O;Q0@Q0APjPKP9P8DDS0AQ0?18D8S0i50E%HL=0EFQ0BPjPL%:?P<CF=0=[A9W0[Q0DQ0KQ0WQ09Q0VQ0UP3Q0RPnQ0PPeP]%:_S0RP<CF=0=nS0VA95NnQ0LQ0JQ0|7UTQ0N18DkS0|50E%HRS0N=0EFQ0G]3]4]0]2^1w]8]7[X96Q0FP3Q0PPoP_Pe%:NS0PP<CF=0=oRwA9}MoS0LQ0ZQ0[Q117U9Q0\Q0u50E%HTS0\=0EFQ0_]3]4]0]2^1G]8]7X97Q0VP3PwP=PNP_%:MP<CFA9IkpS0ZQ0aQ0X7U{RwQ0b=0ExRs%HV=0EFRhP>P@PUPLP~D2]3]4]0^2l^1O]8X:=Q0LP3Q0ZP41>|QQ0eQ0fQ0gP~PVPTPRDDQ0hQ0Y50E%HX=0EFP>P@P\PXPV%:YS0hP<CFS0YPKD2]3]4]0]2]1X;4P=PVPT%:XS0eP<CFS0fP>P\P3PfC3P>P@Q0jPYPX%:[P<CFS0g1>z[D2]6X?=P>PUQ0fP~C3P41>uYS0fP>Q0jQ0gP3C3P>P@fcR~/1zP[PY%:dP<CF1>~dD2]6X>4P>P\Q0YQ0fC3P>P@PzPuPiPdP[PYPXPLPKP9P8P5M>sW6PfPjP3F;W6PfP?P{F;XDhX5sX3wX4lX0OPSP3E<b0W8PpP3E<b0W7PkP3DCb0W2PMP3DBb2W1P3O1b1P3O1b1W5P5P2P3PjPLPKP9P8O8W8W7W5W3W4W0W2X1qXHDXC=X@7XB;XADX<7X=6PBPCP0P?PjPLPKP9P8P5P2P3O<Q0@Q0A%HKQ0i50EQ0kPLPK%:jP<CG=0=XA9A?XQ0MQ0OQ0CQ0nQ0oQ0pP3Q0qPgQ0rP]PZ%:eP<CG=0=gROA95_gQ0tQ0vQ0w%HQ18DMRl50EP>P@11|IP}PSD2]4]0]2]1]7]5[X96Q0yP3Q0rPmPeP]Q0RP<CG=0=mR]A9pNmRpQ0{Q0}%HPQ0|50EQ0x]4]0]2^1G]7]5X97P3P]P=P_PeQ0PP<CGA9SMnRSQ0NQ0u50ER]P>P@Q0~PKPID2]4^0J^2y^1^]7X:=P3PSP41>}kQ10Q0`Q12Q0\=0ExP>P@Q0IPTPR%:VP<CGRxP9D2]4]0]2]1X;4P=PRPP%:TP<CGRSP>Q0IP3P|C3P>P@PtPVPTQ0eP<CGRw1>rXD2]6X?=P>Q0~PSPIC3P41>fVRIP>PtPwP3C3P>P@PUPXPVQ0hP<CG1>HYD2]6X>4P>Q0IPxPIC3P>P@PrPfP[PYPXPVPTPKP9P8P5M=rW6P|PLP3F;W6P|PjP}F;X8]X3JX4yX0^PoP3E<b0X7pPnP3E<b0X5OPMP3DCb0W2PNP3DBb2W1P3O1b1P3O1b1W3P5P2P3PLPKP9P8O7W7W5W3W4W0W2X1qXMDXC=X@7XB;XADX<7X=6PCP0P?PjPLPKP9P8P5P2P3O;A4E2F18D297E8P>P9P5P8%q;R;D@11K9RqQ0<'=A0=<e%?eQ0EQ0H'=Q04Q0011QkP3CT16?kQ06Q05Q03P2CW15CP15BRP315ATPV16WVRRA0=<VRVA4EeFPEQ01PDPeCMP>PKP_PNP;D@P>P@Q0QPiPdD2]0]2]1^5v]3[X9616ATP3PRPXQ0lQ0mPEQ0SPDP_CMP>PbPNP9P;D@P>P@Q0TPcPiD2]0]2^1G]5]3X97P3Q0lP=P<%?YRGA4EiFR_18DN97EbRNP>PaPMPbP;D@RMP>P@Q08P9PcD2]0]2]1]5X:=Q0mP3PGA4EcFQ0:=0ElP>P`PkPaP;D@P>P@Q0;P<P8D2]0]2]1X;4P=P<P>Q0;P3PbC3P>P@Q0=P<CO]6X?=P>Q08P<PcC3P>Q0=P<P3C3P>P@Q0>P<CO]6X>4P>Q0;P<P:C3P>P@PmPgPPP9P8P5GpW6PbPKP3DZW6PbPLPiF;X7MX4NX0_P[P3CYb0W5PYP3E<b0X3VPZP3DCb0W2PWP3DBb2W1P3O1b1P3O1b1W4P5P2P3PKP9P8O6W5W3W4W0W2W1XADX<7X=6PKP9P8P5P2P3O6n10410610010100000087110:10810;1020000000005110:1080000000005110:108000000000<110:108103104102109105000000000000000;110:108103104102105000000000000000<110:108103104102105107000000000000000;110:10810310410210510<0000000000006110:108103000000000Q0E,=5A0=5j1b5jP>P@Q07P0P?D2[[[X;4X:=XG1PqP8P5O3P3Q02,\11\=91\48O3b1WFW6X>4W?XI7XK6o"). Qed.

Lemma sstep_cfg_of_sstep' : forall c e st,
  sstep segs c e st ->
  fam_on (cfg_ms c) ->
  sstep_cfg segs scfg c e st.
Proof.
ltac2:(KReplay.run1 (kr_t_Scfg ()) ["WithSegs"] "p'0h01eh12sth21ci001ch35modelh42msi019cfg_modeli026cfg_msp;1p;4p;5p;2g00gjj16Tg018ij43Tg01Uaj12Tg0113j11Tg019]j54Tg01VTj45Tg0184j20Tg01S@R0P0g00mL#6R0g01T5R1p,4segsR2f2R3f1R4f0R5C3f3R6#2#1P2p,4scfgR7f4R8P6P3D4[[]1]0P5g0129g00V3P6P3P4P5C5P21063P4P5C31086#2#1P2P7f5/08P6P3D4[[eX11X00W3W4P4P5O2n01100000120102101W2o"). Qed.

(* [comment removed for export] *)
Lemma sstep_of_sstep_cfg : forall c e st,
  sstep_cfg segs scfg c e st -> sstep segs c e st.
Proof.
ltac2:(KReplay.run1 (kr_t_Scfg ()) ["WithSegs"] "h01Hh11ch21eh32stp;1p;5p;6g00gjj12Tg019]j51Tg01Wfj60Tg01S@g00mL#2g01T5p,4segsR0p,4scfgR1f2R2f1R3f0R4D1P0P1f3P2P3P4E0W0W3W2W1o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma star_cfg_one : forall c evs c',
  sstep_cfg segs scfg c evs (SNext c') -> star_cfg segs scfg c evs c'.
Proof.
ltac2:(KReplay.run1 (kr_t_Scfg ()) ["WithSegs"] "h03evsh11Hh21ch32c'p;1p;5p;3p;9p;2p;6g00gjj19Tg01>Aj18Tg019]j50Tg007ij11Tg003`j37Tg01X`j52Tg01YWj33Tg01ZNl94Tg01[Ej25Tg000`j66Tg01S@R0g00mLR1#9R2p,4segsR3p,4scfgR4f2R5f1R6f0R7#8D0P2%11R89715P3P4f4P7P5D2X02P3P4f3P5P6P8P6P7A3346M94P51515E6W1X30W0W2o"). Qed.

Lemma star_cfg_trans : forall c1 tr1 c2 tr2 c3,
  star_cfg segs scfg c1 tr1 c2 -> star_cfg segs scfg c2 tr2 c3 ->
  star_cfg segs scfg c1 (tr1 ++ tr2) c3.
Proof.
ltac2:(KReplay.run1 (kr_t_Scfg ()) ["WithSegs"] "h03H23h11ch22c1h32c2h43tr1h53H12h62Hsh73Hsth82IHh92c'h:3c''h;2c3h<3evsh=1lh>2trh?3tr2p;1p;5p;9p;4p;6p;:p;3g00gjj19Tg01X`j50Tg01>Aj12Tg019]j58Tg01ZNl97Tg01[cj44Tg000`j63Tg01\Al:5Tg003`j36Tg00mLR0f1R1f0R236p=1g01S@R3%90R4p,4segsR5p,4scfgR6f4R7f3R8f2R9D0P5P6P8P9P1D0R:P5P6P5P6P2f6R;f5R<D0P5P6P8f7R=,19P;D0]0X33X44X23P5P6P2P7P8D0P2W0X13P5P6P7P8%29D8P5P6P9f:R9f9R>D0P5P6P<f;R?,17P9D0]0P5P6P8P?P9D0P4f<R9,1<R@,1=P5P6P>P2P9D0X=4P5P6f8P=P;P@P?P8P1P2O1M9711=</19P0P=P<P9C4E3W0W8X7:W6X:3X>4X93X<4X13P;P<P7P1P2M:5W0W5X;3X?4X33W4W2o"). Qed.

Lemma obs_trace_cfg_nil : forall c0, obs_trace_cfg segs scfg c0 [].
Proof.
ltac2:(KReplay.run1 (kr_t_Scfg ()) ["WithSegs"] "h01ch12c0h23tr'p;1p;5p;3p;2p;4g00gjj18Tg01X`j50Tg007ij14Tg01]:j31Tg00WHj23Tg00k<j27Tg01YWj36Tg00nBj45Tg00n]j42Tg01S@R0g00mLR1#8R2p,4segsR3p,4scfgR4f2f1R5f0R6D0%41R7=115'3X00,70X22P7P0P3P4P5P7P6D0A1177R1'3X00P6P3P4P6P7P6D0P1A6346g00YlC5C2C2W1o"). Qed.

Lemma sstep_cfg_halted_none : forall c e st,
  sstep_cfg segs scfg c e st -> m_halted (cfg_model c) = None.
Proof.
ltac2:(KReplay.run1 (kr_t_Scfg ()) ["WithSegs"] "p'0h02H0h11Hh22H1h32H2h42H5h52H4h62H3h71ci001ch82H6h92H7h:1li011lh;1si021sh<2H8h=5modeli035modelh>2msi042msh?2sth@1ehA6model'i056model'hB2x8i062x8hC3effi073effhD3evsi083evshE4codei094codehF7model''i0:7model''hG3ms'i0;3ms'hH3sigi0<3sigp%0p;1p;5p;3p;2p;7p;6p;4g00gjj1iTg019]R0j51Tg00Fgj30Tg006fj1MTg00Bfj1_Tg00CDj1]Tg005_j1ZTg00BDj1YTg01:Uj2hTg01;5j1gTg01<=j3FTg01=9j2VTg0184j22Tg007ij1^Tg00o7j1TTg01>Aj1STg000`j79j67Tg01?oj1\Tg01Aoj1[Tg01Coj1JTg009Cj2<Tg010=j36Tg00j;j4ITg00ZHj1HTg01Dfj1KTg01Elj2LTg01G5j2PTg01Gnj1NTg0027j6fTg01Kjj1BTg01Laj1;Tg01QTj2ETg01RJj2DTg01ODj1bTg00hJj3OTg009ej2XTg01^0j1aTg01Q4j4cTg00kVj4`Tg00Ekj3dTg003`j3eTg01S@R1f1R2f0R330p=4g01T5R4?023p=Qf2R5%a2#J;03p=3%J2=053p=8%T2=053p=:g0129R6g00V3R7P2P3Ccp=U%S2=043p=?P1f5R8f4R9f3R:P5P2P3F9p=CP1P9P:P5P2P3E7p=@g01TkR;=043p=>P4P;P9P:P5P2P3F9p=WP4P;P:P5P2P3E7p=Rg00lNR<P5P2P3C`9O9:p==1<2390:5p=A1223#Sp=Gg00mLR=Ad=237e5p=5%i=R>p,4segsR?p,4scfgR@P5P2P3D1P0P?P@f7R0,4:A0>:01Q:0g00;9#M#M#M#M#M#M#_#]RA#ZRBf:RC%YARD33[[[P3A8B5DA:B9D1h67RE#gRFAF?891U:5,VE30f6RG/28RHfARI'4%^=R==0>IRJ1?HIf9RHf8RK'2RLfDRM'4P312CHS00fERN'4f;RO/2CRPfFRQ90>=RR1?PQRSf=RT=8BDRUf?RV#TS01=0BDRWf@RX=F?VRYf>RZ/UT,VE50FA3B8DS02]3]2]0]4]5X71A0>=NP3PRP>P=f<RR/2OR[fGR\'?R]A8BZDR^%TXS03=0BDR_AF?IX1UVZ,VE50FR`fBRa/2IRb=3BDS04]3]2]0]4X:>P3P]P412TRS05#SA8BVDA:BIDAF?aI1UXV,VE50FfCR]/2aRc=3BDS06]3]2]0X;4PbP?P@P3fMRdfLReD112M]S07=3BDS08]1X71P?P@PbPefKRfD1P>P=P?P@Q07P3PdD112NMRg=3BDS09]1X@>P?P@PcP=PeD1P4%SbRhP?P@PgP=P3D112QN=3BD]1X?4P?P@Q07P=PhD1P8Q09eW1PdPGP3F9W1PdP0P3F9W1PdPKfJRhECX3`X2_X0^fHR_P3E7b0X4SP\P3E7b0W5PQP3D@b0W6P5P2P3P8P9P:O6W4W5W6W3W2W0XA7XG6X=7X>6PGP8P9P:P5P2P3O7A8B3DRSA:B5DR`AF?:5Rg%\ERi50F129:/4TRjA0>=TRk%>TRl120G/4XRmP312K0S0:/4IRnPLA0>=aRo%>aRpA8BODRqA:BTDRrAF?ZTRs=0FiQ02]3]2]0]4]5X71P3PoP>P=%>]RtA8BRDRu%TZS0;=0BDRvAF?VZRw=0FiRx12XVRy=3BDRz]3]2]0]4X:>P3PtA0FYi12IXRi=3BDS0<]3^2W^0UX;4PyP?P@P3fIR{P_D1Q04]1X71P?P@PyP_P\D1P>P=P?P@PbP3P{D1Q06]1X@>P?P@PiP=P_D1P?P@PcP=P3D1Q08]1X?4P?P@PbP=P;D1P8Q06eW1P{PGP3DWW1P{P0P3F9W1P{PKPQECR|X3xX2vX0uPMP3CRb0X4pP]P3E7b0X5JPaP3D@b0W6P5P2P3P8P9P:O6W4W5W6W3W2W0X=7X>6P9P:P5P2P3O5%[ERE90FgP3PnPLA0FsEQ02]3^2r^0q^4p^5oX71P3PoP>P=A0FwERwPz]3^2v^0u^4tX:>P3PtA0FYEQ0<]3^2W^0UX;4P|X3wX2vX0uPMP3CRb0X4pP]P3E7b0X5JPaP3D@b0X6mP5P2P3P8P9P:O6X4lX5kX6jW3X2`X0SX=7X>6P9P:P5P2P3O5%J8S0==0BDRS1<A89:B0R`A6?KGS0>P0P8P9P5D=P@A6?H0PKPGCI#HA8BGD%Z7Rj%KK,L0P7PGCA14[dA0>0d1PZO#N/2H/?d12VZS0?fPR['4P3fQRk,4yPifRRl90>RRm1P]X#N/2Z/?lRJ%J]S0@=0BDRp1<A]9:BNRvA6?QMRwPNP]PaPXD=P@A6?\NR|PQPMCI#HRW%JMS0A=0BDREPj%KQ,LNRYP7PMCAA3BKDS0B]4]5]6]3]2]0]<]9X71A0>OkP3PmP>fSS0C1PMI#N/2VQ0C'?Rm1<AM9:BQRFP|PQPMP]P:D=P@A6?_QRtP\PNCI#HRzA8BNDRoPj%K\,LQS0DP7PNCARq12fhRr=3BDS0E]4]5]6]3]2^0E]<X:>P3PmP41PNa#N/GX1<AN9:B\PtP\PNPMfXRtD=P@A6?{\P_PQCI#HA8BQDPj%K_,L\P7PQCA12efRm=3BDS0F]4]5]6]3]2^0oX;4P|PQPMP]fWS0GD=PrP?P@P3f\Rsf[RnD112deS0H=3BDRg]1X71P?P@PrPnfZRxD1P41Pe{#N/G\R}P?P@Q0Hf]P3D1fNR~/2d=3BDS0I]1X?4P?P@PmPsP}D1P0PgeW1PnPKP3F9W1PsPOfYRsECX4qX5oX6zW3X2FX0EfTS0JP3E7b0X<JPTP3Efb0W9PlP3D@b0W8P5P2P3PKP0PGP8P9P:O9W<W9W8W4W5W6W3W2W0XD>XF7XA7XC<XBAX=7X>6PRPOPCPHPKP0PGP8P9P:P5P2P3O=A8B9D1<A99:BGA6?08PGP9P:P5D=P@Q0>P0P8CI#H%K0,LG%Y7RJ50j14PfS0KA0>=f%>f12ZTS0L/4~S0MP3Q0?fORP'4S0NPyA0>=[S0O%>[S0P%JaS0Q=0BDRq1<AaS0R9:BMRnA6?N]PMPaPIPXD=R}P@PwPNP]CI#H%KN,LM=0jJQ0B]4^5p]6]3]2]0]<]9X71A0>=PP3Q0OP>P=%>kS0OPwPNP]PaPID=RwA0jYJS0B12h{RY=3BDS0S]4^5E^6W]3^2v^0p]<X:>Q0PP3Q0OP|PQPMP]PaD=R|Q0D=0jJQ0E]4^5o^6z]3^2F^0EX;4Q0BPYP?P@P3PxPsD1Q0F]1X71P?P@PYPsPtD1P>P=P?P@PmP3PxD1Pg]1X@>P?P@PrP=PsD1P?P@Q0HP=P3D1Q0I]1X?4P?P@PmP=P;D1PKPgeW1PxPHP3DWW1PxPCP3F9W1PxPOQ0GECW4X5EX6WX3wX2vX0pPlP3CRb0W<PkP3E7b0W9P[P3D@b0W8P5P2P3PKP0PGP8P9P:O9W<W9W8W4X5SW6W3W2W0XD>XA7XC<XBAX=7X>6POPCPHPKP0PGP8P9P:P5P2P3O<Q0>P0P8P9P:D=S0>Q0=1<A:RW50B%BG=0BDQ0K%;K,EG=50==0>f12TH/?fQ0MP3Q0NPy%;TS0N,EO=5R==0>[Ry1GaZS0=/Q[RxQ0Q1<AXS0P50B%B]S0Q=0BDA3B0D]5]6^3}^2n^0q]9]8X71%;RRz,EC=5O==0>PP3PyP>%;Z,ER=5T=1G]VS0B/QkS0IQ0@1<AIRy50BRo%BM=0BDRJ12{_Rj=3BDS0@]5]6^3w^2v^0p]9X:>P3Q0IP41GMXQ0AQ0R50B%BN=0BDQ0S]5]6^3|^2F^0EX;4PjP?P@P3PsPtD1Q0E]1X71P?P@PjPtQ0GD1P>%;QRE,EM=5N=RFP?P@PrP3PsD1Q0F]1X@>P?P@PYPFPtD1P41Gf\RtP?P@Pm%;_,EQ=5\=P3D1Pg]1X?4P?P@Pr%;\,EN=5Q=PtD1P0Q0FeW1PsPKP3F9W1PsPHP3F9W1PsPCfVRsECX5JX6oX3wX2vX0pPlP3E7b0X9xPkP3E7b0W8P[P3D@b0W4P5P2P3P0PGP8P9P:O8W9W8W4W5W6W3X2`X0SXEAXD>XA7XC<XBAX=7X>6POPCPHPKP0PGP8P9P:P5P2P3O<Q0>%B8=0BWQ00/4{%;0,D8=5G==0>{12RK/?{Q05/4eP3Q0L/4dQ0?1DCz=5O==0>~Rz12IT/?~ReA8BIDA:B]yA6?MaP]PIPXPVD=PB%BIPAPVCAA3BGD]6]3]2]0]8]4X71%;O,DH=5C==0>dP3PzP>Q0N,DO=5R=Q0=/QPRO%BaQ0P50BRz12\QRd=3BD]6^3}^2n^0q]8X:>P3POP4Q0BQ0Q=0By12_\R\=3BD]6^3w^2v^0pX;4PdP?P@P3PsfURpD1Q0@]1X71P?P@PdPpQ0JD1P>%;M,Da=5]=RdP?P@PjP3PsD1Q0S]1X@>P?P@P\PdPpD1P41G{NRpP?P@PY1DME=5N=P3D1Q0E]1X?4P?P@Pj%;N,D]=5M=PpD1PGQ0SeW1PsP0P3F9W1PsPKP3F9W1PsPHQ0CECX6zX3}X2nX0qP[P3E7b0X8ePPP3E7b0W4P~P3D@b0W5P5P2P3PGP8P9P:O7W8W4W5W6W3X2`X0SXHAXD>XA7XC<XBAX=7X>6PCPHPKP0PGP8P9P:P5P2P3O;A8B2D1<A29:B:A6?95%b<R<7O:1289/4VA0>=V%>VQ0:/4aP314L]Q00A0>=MRL%>MRaPBQ0;PAPRCAA6?VT?OZ<Q02]3]2^0u]4]5X71A0>=]P3PLP>P=%>NRLPBQ01PAPTCARTA6?XZ?OV<R]Q0<]3]2^0U]4X:>P3PLPBQ03PAPZCAA6?IV?OX<Q04]3]2^0^X;4PiP?P@P3PfPhD1Q06]1X71P?P@PiPhP{D1P>P=P?P@PcP3PfD1Q08]1X@>P?P@PbP=PhD1P?P@Q07P=P3D1Q09]1X?4P?P@PcP=P;D1P8Q08eW1PfPGP3DWW1PfP0P3F9W1PfPKP_ECX3]X2TX0UPQP3CRb0X4aPNP3E7b0W5PMP3D@b0W6P5P2P3P8P9P:O6W4W5W6W3W2W0XBAX=7X>6P8P9P:P5P2P3O6n200410010110200000087110410310;1050000000005110410300000000051104103000000000=110410310610710510:108000000000000000000<1104103106107105108000000000000000000<1104103106107105108109000000000000000;110410310610710510810<00000000000061104103106000000000145GA0>5G1Q5GA3BHD[[[X;4X:>X71P:P5P2O3P31X191X>:1X45O3b0W1X?4W@X71o"). Qed.

Lemma star_cfg_halted_nil : forall c tr c',
  m_halted (cfg_model c) <> None -> star_cfg segs scfg c tr c' -> tr = [] /\ c' = c.
Proof.
ltac2:(KReplay.run1 (kr_t_Scfg ()) ["WithSegs"] "p'0h02H1h12H0h21ci001ch35Hstarh41Hh53Hssh66Hstar2h72Hhh81li011lh92tri022trh:2H2h;2c'h<2c0i032c0h=2c1i042c1h>2c2i052c2h?2c3i062c3h@3evsi073evshA3tr2p;1p;3p;5p;2p;4p;8p;7p;6g00gjj1KTg006fj15Tg00Bfj1ETg00CDj1BTg005_j1JTg01^0j1<Tg01Coj1:Tg00BDj1DTg00Fgj31Tg00ZHj1;Tg01X`R0j52Tg007ij1ATg009ej27Tg00nBj4ITg0027j8Hj68Tg000`j7?j6>Tg01>Aj16Tg019]j59Tg01^fj4FTg00T>j2CTg00WHj2@Tg003`j3GTg01S@R1f1R2f0R331p=0f4R4f3R5f2R631A1123'@p=3A1123,@6p==g00mLR7?G23p=4%K7R8g00;9#5#5#5#5#5#5#E#BR9#JR:%<6#:%D9R931#;p,4segsR;p,4scfgR<P5P6P2D2R=P0P;P<f8R0,05R>A1850P8f:R?%A7R7f9R@f;RAD3\>[[P3f6R>,03A187>106>105@P3104?P1PAA187ARB102AP8f=RCP7f<RDf>RED3]0]1X21A187?P3PBP8P710EDRBP8P2P7PCf?RFD3]0X8810CAP3PBP1PCA1877RB?=E3X21P8P7P;P<f@RGP3PED2A=BFF]3X98P;P<PFP7PCD2P1PE%<3#:=1:9#;P;P<P2P7PGD2fARH==BH]3]7X21%<E#:=1:9#;P;P<PFP7PFD2PB10GG1787171GCIW3W7PGP6PCP3GHW3PEP5PAF?PFP3E8b:W0PDP3E>b0W1f5RBP3E8b1W4P6P2P3O3W0W1W4X<1P3O1P;P<P4P5%66D9fBR9,0>14>4=1891049fE,0@P3fFR:,0?P1fGRI14A@=18IRJ10@IRIP;P<P6PC%6DD9P;P<PCPDPAD2P8fKRKP7fJRLfLRMD3]6]5]0]1X2114?0=18:P3PJP814D?fHRJ,0?R:P;P<PKPE%6CD9RNP;P<PEPCPDD2P8P5P7PKfMRDD3]6]5]0X88P3P:P1fIR:P;P<PMPF%6ED9P;P<PFPEP2D2P814HFP7PMfNRFD3RO]6]5X21P;P<PEPCPLD2P814GEREP;P<PFP3PMD2P8149GP7PDfOD3]3X98P;P<PDPEPKD2PKPFPH%6GP6CFO1,COW3PMPBP:F?W6X5NPAP3E8b:X0IPJP3E>b0W1PAP3E8b1W4P6P2P3P4P5O5W0W1W4X6=W5X?1XA8X>1X@8X=1P>PBP4P5P6P2P3O7n200410010110300000021110071104107105102106000000f7R2,06R>A1862P8P@P7P0P?D3\>[[X21X88X21P4P5P6O3P3171B17841715O3b4W3W7X;1W9X21o"). Qed.

(* [comment removed for export] *)
Lemma reaches_error_cfg_here : forall c evs,
  sstep_cfg segs scfg c evs SError -> reaches_error_cfg segs scfg c.
Proof.
ltac2:(KReplay.run1 (kr_t_Scfg ()) ["WithSegs"] "h03evsh11ch21Hh32trp;1p;5p;2p;3p;4g00gjj18Tg019]j53Tg01X`j50Tg00WHj21Tg00k<j24Tg007ij17Tg01YWj36Tg00nBj45Tg00n]j42Tg01S@R0g00mLR1#8R2p,4segsR3p,4scfgR4f1R5f0R6g01TkR7D3R8P2P3P4f5f2R9P5D0/18X02,42X10,40X32%71R1P0P3P4f4P1P5D0/18X02,42X10P9P2P3P4f3R0P1P0D0P3P4P0P6P7D3'1X02P5P3P4P9P1P9D0P3P4P9P5P7D3A6349P6C5C2C2C2W2W0W1o"). Qed.

Lemma reaches_error_cfg_step : forall c evs c',
  sstep_cfg segs scfg c evs (SNext c') ->
  reaches_error_cfg segs scfg c' -> reaches_error_cfg segs scfg c.
Proof.
ltac2:(KReplay.run1 (kr_t_Scfg ()) ["WithSegs"] "p'0h03evsh11ch21Hh32trh42Heh52Hsh63Hsth72c'h82c2h94evs2i001xp;1p;5p;3p;2p;9p;4g00gjj1<Tg01>Aj1;Tg019]j57Tg01`;j33Tg00k<R0j20Tg01X`j54Tg003`j35Tg01ZNl99Tg00nBj48Tg00n]j46Tg00WHR1j2:Tf3R2f2R3f1R4f0R5g01TkD7p=2f5R6f4R7P2P3P4D4/:5p=1g01S@R8g00mLR9#<R:p,4segsR;p,4scfgR<P3P4%;5D7A3;<4P0P:P;P<P6P3P4P;P<P4P5C2R=E1X0:,0:X18,08X3:A3;<6P5P;P<f7R>P3P4P=E1X0:,0:X18,08P0P8P;P<f8R?P2P4P=E1X0:,0:X18f9R293;<P5P;P<f:R@P6P4P=E1X0:,0:P0P:P;P<f;R0f6P3P;P<P3P5C2E1X0:f=RA93;<P5P;P<PAP?P7P;P<P7P5C2E1P1P;P<f>R1P2P6D4P;P<P6P4C2fARB93;<P5P;P<f@P0P>D4P;P<P?P7C2P:P;P<fGP3P4P=E1X0:,0:X18,08X3:fCR3=59AR7P8P;P<fFfER?f?559P4P=E1X0:,0:X18P2P:P;P<P?fDR?=591P@P;P<P@P5C2E1X0:P6P;P<P?P7P2D4P;P<P2P6C2P;P<P?P3fBPAP2PBP4M99P5C8C6C6C6W4W6P4P5O2n2001000000120000000W2X9:P4P5O2n2001000000120100000W2X88P4P5O2n2001000000120100000W2X3:P4P5O2n2001000000121100000W2W5X78W0W1o"). Qed.

End WithSegs.
