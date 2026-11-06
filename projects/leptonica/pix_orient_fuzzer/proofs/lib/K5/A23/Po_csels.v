(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.A23 Require Import ImageA.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Import RzCPS NodesA.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.A23 Require Import Layout.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.A23 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface Pm_iface Pm_iface2 Pm_iface4 Cf_iface RT_fk RT_fk_iface D_iface D_defs Bi_fktw Bi_fkweak Bi_iface2 RT23_iface.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.A23 Require Import Po_rows Po_iface Po_csels_defs Po_csels_cut Po_csels_front Po_csels_mid Po_csels_front16 Po_csels_mid16 Po_csels_tail.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_Po_csels () := "C69OSSVerify5KrLib2K53A238RT_iface3rtsC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00K47Corelib7Numbers7BinNums8positive01C4ELinuxProcessSemantics5Riscv7Prelude5bvmapI47Corelib4Init9Datatypes6option00I47Corelib4Init9Datatypes4list00C69OSSVerify5KrLib2K53A23<Po_csels_cut9csels_ctxC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23<Po_csels_cut7csels_QC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23=Po_csels_tail:csels_tailC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23<Po_csels_mid;csels_mid_0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23>Po_csels_front=csels_front_0C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00K47Corelib7Numbers7BinNums8positive03I47Corelib7Numbers7BinNums1Z00C69OSSVerify5KrLib2K53A23>Po_csels_mid16<csels_mid_16C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23@Po_csels_front16>csels_front_16C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23=Po_csels_defsJselectComposableSels_of_alC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53A238Po_cselsKselectComposableSels_al0_okC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53A238Po_cselsLselectComposableSels_al16_okC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope Z_scope.

Section CSELS.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis GP : rt_gaps RT.
Hypothesis FKC : rt_fk_contracts RT.
Hypothesis SM7 : stack_malloc_7_contractF RT.
Hypothesis SF7 : stack_free_7_contractF RT.

Theorem selectComposableSels_al0_ok : selectComposableSels_al RT 0.
Proof using AF GP FKC SM7 SF7.
ltac2:(KReplay.run1 (kr_t_Po_csels ()) ["CSELS"] "h03CTXh11Fh23PMch33dirh42gph52loh61mh72p1h82p2h92rah:3rash;2s0h<2s1h=3s10h>3s11h?2s2h@2s3hA2s4hB2s5hC2s6hD2s7hE2s8hF2s9hG4sizehH3usphI2Σp;1p;2p;<p;Hp;Np;Qp;6g0000j1<Tg000hj10Tg001Mj11Tg001kj12Tg002Nj1;Tg0033j2:Tg003_j17Tg004Aj14Tg004al<5Tg005clH6Tg006clN3Tg007glQ8Tg008kj69Tp,2RTR0p,2AFR1p,2GPR2p,3FKCR3p,3SM7%<0g00:3p-0[g00:i#0R4#0#0R5#0#0#0#1#2R6%;4#1/:6g00;NR4%15#2#7\6%44P0fHR5fGR7fFR8f7R9f6R:f5R;f4R<f3R=f2R>f1R?f0R@M<5P0P1P2P3p,3SF7fIRAP5P7P8fERBfDRCfCRDfBREfARFf@RGf?RHf>RIf=RJf<RKf;RLf:RMf9RNf8ROP9P:P;P<P=P>P?P@P0PAP5P7P8PBPCPDPEPFPGPHPIPJPKPLPMPNPOP9P:P;P=P>MH6P0P1P2P3PAP5P7P8PBPCPDPEPFPGPHPIPJPKPLPMPNPOP9P:P;P<P=P>P?P@MN3MQ8W0W:X84X74X34XG4W6X54WHW1X>6X=6XF6XE6XD6XC6XB6XA6X@6X?6X<6X;6X46W9W2WIE9o"). Qed.

Theorem selectComposableSels_al16_ok : selectComposableSels_al RT 16.
Proof using AF GP FKC SM7 SF7.
ltac2:(KReplay.run1 (kr_t_Po_csels ()) ["CSELS"] "h03CTXh11Fh23PMch33dirh42gph52loh61mh72p1h82p2h92rah:3rash;2s0h<2s1h=3s10h>3s11h?2s2h@2s3hA2s4hB2s5hC2s6hD2s7hE2s8hF2s9hG4sizehH3usphI2Σp;1p;2p;<p;Hp;Np;Qp;6g0000j1<Tg000hj10Tg001Mj11Tg001kj12Tg002Nj1;Tg0033j2:Tg003_j17Tg004Aj14Tg004al<5Tg005clH6Tg006clN3Tg00;llQ8Tg00=3j69Tp,2RTR0p,2AFR1p,2GPR2p,3FKCR3p,3SM7%<0g00:3p-0[g00:i#0R4#0#0R5#0#0#0#1#2R6%;4#1/:6g00;NR4%15#2#7\6%44P0fHR5fGR7fFR8f7R9f6R:f5R;f4R<f3R=f2R>f1R?f0R@M<5P0P1P2P3p,3SF7fIRAP5P7P8fERBfDRCfCRDfBREfARFf@RGf?RHf>RIf=RJf<RKf;RLf:RMf9RNf8ROP9P:P;P<P=P>P?P@P0PAP5P7P8PBPCPDPEPFPGPHPIPJPKPLPMPNPOP9P:P;P=P>MH6P0P1P2P3PAP5P7P8PBPCPDPEPFPGPHPIPJPKPLPMPNPOP9P:P;P<P=P>P?P@MN3MQ8W0W:X84X74X34XG4W6X54WHW1X>6X=6XF6XE6XD6XC6XB6XA6X@6X?6X<6X;6X46W9W2WIE9o"). Qed.

(* [comment removed for export] *)
Theorem selectComposableSels_ok : selectComposableSels_cps RT.
Proof using AF GP FKC SM7 SF7.
ltac2:(KReplay.run1 (kr_t_Po_csels ()) ["CSELS"] "p;3g00>>j30Tp,2RTg00?Rg00@b30o"). Qed.
End CSELS.
