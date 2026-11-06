(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import SimInv ExitSim CatSim ShapeAlg DivergeSim SpinAlg SpinAlgX.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require KReplay.
Ltac2 kr_t_ShapeEF () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9MorphismsKrespectful_per_obligation_1I47Corelib4Init9Datatypes4list00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C4ELinuxProcessSemantics?LinuxProcessSem3Run;init_configI79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7SpinAlg:srealizes000C13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7SpinAlgBsrealizes_no_errorC13~~~K4ELinuxProcessSemantics?LinuxProcessSem<MemImageType5Image01K4ELinuxProcessSemantics?LinuxProcessSem3Run9ExecEntry01C4ELinuxProcessSemantics?LinuxProcessSem3Run8run_scfgC4ELinuxProcessSemanticsEEquivalenceDefinition;Equivalence:error_freeI4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00I47Corelib7Numbers7BinNums1N00I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType8PhdrInfo00K47Corelib7Numbers7BinNums8positive03I4ELinuxProcessSemantics?LinuxProcessSem;StackLayout9EntryDraw00I47Corelib7Numbers7BinNums1Z00I4ELinuxProcessSemantics?LinuxProcessSem5State9ProcInput00C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8ShapeAlg4TSetC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib5BMode;bm_off_instC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7SpinAlgAsrealizes_obs_iffC13~~~C4ELinuxProcessSemantics?LinuxProcessSem3Run9bh_tracesC47Corelib4Init5Logic3iffI4ELinuxProcessSemantics?LinuxProcessSem5State5event00I79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8ShapeAlg8realizes00C13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8ShapeAlgArealizes_no_errorC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8ShapeAlg@realizes_obs_iffC13~~~C4ELinuxProcessSemanticsEEquivalenceDefinition;Equivalence;trace_equivI47Corelib4Init5Logic3and00c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7ShapeEFDsrealizes_error_freeC13~~~C47Corelib7Classes9Morphisms?eq_proper_proxyC47Corelib7Classes9MorphismsMtrans_co_eq_inv_impl_morphismc79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7ShapeEFDsrealizes_traces_iffC13~~~C47Corelib7Classes?RelationClasses?Equivalence_PERC47Corelib7Classes9MorphismsNtrans_sym_co_inv_impl_morphismC47Corelib7Classes?RelationClasses;reflexivityK47Corelib4Init5Logic3and01C47Corelib7Classes?RelationClasses>iff_TransitiveC47Corelib7Classes?RelationClasses?iff_equivalenceC47Corelib7Classes?RelationClasses=iff_ReflexiveC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8ShapeAlg4t_eqC13~~~K79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7SpinAlg:srealizes004C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7ShapeEFFshape_strong_equiv_efsC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7SpinAlgFsrealizes0_of_realizesC13~~~K79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8ShapeAlg8realizes03C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7ShapeEFEshape_strong_equiv_efC13~~~C4ELinuxProcessSemantics?LinuxProcessSem<MemImageType<img_segmentsC4ELinuxProcessSemantics?LinuxProcessSem<MemImageType;img_init_pcC4ELinuxProcessSemantics?LinuxProcessSem<MemImageType9img_phdrsC4ELinuxProcessSemantics?LinuxProcessSem3Run5en_spC4ELinuxProcessSemantics?LinuxProcessSem3Run6en_brkC4ELinuxProcessSemantics?LinuxProcessSem3Run<en_mmap_baseC4ELinuxProcessSemantics?LinuxProcessSem3Run7en_drawC4ELinuxProcessSemanticsEEquivalenceDefinition;EquivalenceLstrong_equiv_error_free_scfgI4ELinuxProcessSemantics?LinuxProcessSem<MemImageType5Image00I4ELinuxProcessSemantics?LinuxProcessSem3Run9ExecEntry00C4ELinuxProcessSemantics?LinuxProcessSem5StateBsource_alloc_limitC4ELinuxProcessSemantics?LinuxProcessSem5StateBtarget_alloc_limit".

Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section WithCfg.
Variable scfg : SpuriousCfg.

(* [comment removed for export] *)
Lemma srealizes_error_free : forall segs pc ph sp brk0 mb rnd lim inp T,
  srealizes0 segs scfg (init_config segs pc ph sp brk0 mb rnd lim inp) T ->
  error_free (run_scfg scfg (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp).
Proof.
ltac2:(KReplay.run1 (kr_t_ShapeEF ()) ["WithCfg"] "h01Th14brk0h23inph33limh42mbh52pch62phh73rndh84segsh92spp;1p;9p;5p;3p;4p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p710p9g002Uj1:Tg0035j10Tg003Zj13Tg0048j12Tg004[l91Tg005Sj59Tg006bj58Tg0087j34Tg0094j45Tg009lj56Tg00:aj17Tg00;f#:g00<eg00=Cg00>C#0#0#0#0#0#0#3#2R0g00>hg00?hg00@Fg00A@g00BHf9R1p,4scfgR2P1f8R3f7R4f6R5f5R6f4R7f3R8f2R9f1R:M91f0R;D9f:R<P2P<P1P3P4P5P6P7P8P9M91P:P;D8P2A4<13P8P4P5P6P7C5P9D6#7eUW0W2W3W7X40X10W9W6W5W8o"). Qed.

Lemma srealizes_traces_iff : forall segs pc ph sp brk0 mb rnd lim inp T tr,
  srealizes0 segs scfg (init_config segs pc ph sp brk0 mb rnd lim inp) T ->
  bh_traces (run_scfg scfg (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp) tr <-> T tr.
Proof.
ltac2:(KReplay.run1 (kr_t_ShapeEF ()) ["WithCfg"] "h01Th14brk0h23inph33limh42mbh52pch62phh73rndh84segsh92sph:2trp;1p;9p;5p;6p;3p;4p;2g002Uj11Tg0035j10Tg003Zj14Tg0048j13Tg004[l92Tg005Sj5;Tg00CTj6:Tg0087j35Tg0094j46Tg009lj57Tg00Dhj28Tg00E^j29Tg00;f#1g00<eg00=Cg00>C#0#0#0#0#0#0#4#3R0g00>hg00?hg00@Fg00A@g00F7#1g00BHf:R1p,4scfgR2P1f9R3f8R4f7R5f6R6f5R7f4R8f3R9f2R:M92f1R;D;f;R<P2P<P1P3P4P5P6P7P8P9M92P:f0P;E:P2A5<13P8P4P5P6P7C6P9D7/8;P:P;O1'9eUW:W0W2W3W7X40X10W9W6W5W8o"). Qed.

Lemma realizes_error_free : forall segs pc ph sp brk0 mb rnd lim inp T,
  realizes segs scfg (init_config segs pc ph sp brk0 mb rnd lim inp) T ->
  error_free (run_scfg scfg (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp).
Proof.
ltac2:(KReplay.run1 (kr_t_ShapeEF ()) ["WithCfg"] "h01Th14brk0h23inph33limh42mbh52pch62phh73rndh84segsh92spp;1p;9p;4p;5p;3g002Uj1:Tg0035j10Tg003Zj13Tg0048j12Tg004[l91Tg00Fmj49Tg00H;j58Tg0087j34Tg0094j45Tg009lj56Tg00:aj17Tg00;f#:g00<eg00=Cg00>C#0#0#0#0#0#0#3#2R0g00>hg00?hg00@Fg00A@f9R1p,4scfgR2P1f8R3f7R4f6R5f5R6f4R7f3R8f2R9f1R:M91f0R;C9f:R<P2P<P1P3P4P5P6P7P8P9M91P:P;D8P2A4<13P8P4P5P6P7C5P9D6#7eUW0W2W3W7X40X10W9W6W5W8o"). Qed.

Lemma realizes_traces_iff : forall segs pc ph sp brk0 mb rnd lim inp T tr,
  realizes segs scfg (init_config segs pc ph sp brk0 mb rnd lim inp) T ->
  bh_traces (run_scfg scfg (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp) tr <-> T tr.
Proof.
ltac2:(KReplay.run1 (kr_t_ShapeEF ()) ["WithCfg"] "h01Th14brk0h23inph33limh42mbh52pch62phh73rndh84segsh92sph:2trp;1p;9p;4p;6p;3p;5p;2g002Uj11Tg0035j10Tg003Zj14Tg0048j13Tg004[l92Tg00Fmj4;Tg00IPj6:Tg0087j35Tg0094j46Tg009lj57Tg00Dhj28Tg00E^j29Tg00;f#1g00<eg00=Cg00>C#0#0#0#0#0#0#4#3R0g00>hg00?hg00@Fg00A@g00F7#1f:R1p,4scfgR2P1f9R3f8R4f7R5f6R6f5R7f4R8f3R9f2R:M92f1R;C;f;R<P2P<P1P3P4P5P6P7P8P9M92P:f0P;E:P2A5<13P8P4P5P6P7C6P9D7/8;P:P;O1'9eUW:W0W2W3W7X40X10W9W6W5W8o"). Qed.

Theorem shape_strong_equiv_efs :
  forall source_segs rpc rph rsp rbrk rmb (rrnd : EntryDraw) (rlim : Z)
         target_segs apc aph asp abrk amb (arnd : EntryDraw) (alim : Z)
         (T : TSet) (inp : ProcInput),
  srealizes0 source_segs scfg
    (init_config source_segs rpc rph rsp rbrk rmb rrnd rlim inp) T ->
  srealizes0 target_segs scfg
    (init_config target_segs apc aph asp abrk amb arnd alim inp) T ->
  error_free (run_scfg scfg (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp)
  /\ error_free (run_scfg scfg (mkImage target_segs apc aph) alim (mkEntry asp abrk amb arnd) inp)
  /\ trace_equiv (bh_traces (run_scfg scfg (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp))
                 (bh_traces (run_scfg scfg (mkImage target_segs apc aph) alim (mkEntry asp abrk amb arnd) inp)).
Proof.
ltac2:(KReplay.run1 (kr_t_ShapeEF ()) ["WithCfg"] "h05lemmah17Hsourceh27Htargeth31Th44abrkh54alimh63ambh73apch83aphh94arndh:3asph;3inph<4rbrkh=4rlimh>3rmbh?3rpch@3rphhA4rrndhB3rsphC;source_segshD;target_segshE2trp;1p;9p;5p;3p;4p;2p;;p;<p;7g002Uj1;Tg0035j13Tg003Zj1ATg0048j1@Tg004[l9=Tg005Sj5:Tg0087j31Tg0094j42Tg009lj50Tg00:aj16Tg00Dhj15j24Tg00Jdj2?Tg00Kjj2>Tg00LEl;<Tg00E^R0j27Tg00M\j2FTg00NHl9ETg00OBl<8Tg00PYj3DTg00QKj7CTg00RFj4BTg00S4j49Tg00;f#;R1g00<eR2g00=CR3g00>C#3#3#3#3#3#3#A#@R4g00>hR5g00?hR6g00A@g00@Fg00BHR7fAR8p,4scfgR9P8f@R:f?R;f>R<f=R=f<R>f;R?f:R@f0RAM9=f1RBD:P7P@P9P@f9R7f8RCf7RDf6REf5RFf4RGf3RHPBM9=f2RID:P9fCRJfBRK;18P>P:P;P<P=C2PID0RL#6P9A1?@7PGPCPDPEPFC2PID0RM#6RN%5L%5M'?RM'>PJPKP8P:P;P<P=P>PIPHPBM;<PNPMP?P@P7PCPDPEPFPGPIPHPAM;<g00F7#;P9fDRN?1JKP=P8P:P;P<C2PHD0/4APGPAO1RL'7p-0ROP0g00SOP9fE?1NJP<PKP8P:P;C2PGD0/4BPFPBO1RPPAP9A1=>?PEP@P7PCPDC2PGD0/4BRQPQ1FOQM9EW0PNPJPKP8P:P;P<P=PHPGPAPIM<8P9A1>?@PFP7PCPDPEC2PHD0/4A/7LPOP0g00T@9DO0PPPQPPPAFCW0P>P?P@P7PCPDPEPFPHPGPAPBM<8POP0g00U2PLCBO2O2WEPMeC9C9W2W1W;W3X56X95X64X44X:4X83X72XD1W=WAX>4X<4WBW@W?WCo"). Qed.

(* [comment removed for export] *)
Corollary shape_strong_equiv_efs_eq :
  forall source_segs rpc rph rsp rbrk rmb (rrnd : EntryDraw) (rlim : Z)
         target_segs apc aph asp abrk amb (arnd : EntryDraw) (alim : Z)
         (T T' : TSet) (inp : ProcInput),
  srealizes0 source_segs scfg
    (init_config source_segs rpc rph rsp rbrk rmb rrnd rlim inp) T ->
  srealizes0 target_segs scfg
    (init_config target_segs apc aph asp abrk amb arnd alim inp) T' ->
  t_eq T T' ->
  error_free (run_scfg scfg (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp)
  /\ error_free (run_scfg scfg (mkImage target_segs apc aph) alim (mkEntry asp abrk amb arnd) inp)
  /\ trace_equiv (bh_traces (run_scfg scfg (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp))
                 (bh_traces (run_scfg scfg (mkImage target_segs apc aph) alim (mkEntry asp abrk amb arnd) inp)).
Proof.
ltac2:(KReplay.run1 (kr_t_ShapeEF ()) ["WithCfg"] "h03Heqh12Hsh22Hth31Th42T'h54abrkh64alimh73ambh83apch93aphh:4arndh;3asph<3inph=4rbrkh>4rlimh?3rmbh@3rpchA3rphhB4rrndhC3rsphD;source_segshE;target_segsp;1p;9p;5p;2p;8p;Dg002Uj18Tg0035j10Tg003Zj14Tg0048j13Tg004[l91Tg005Sj52Tg00Ubj27Tg00Vjj85Tg00X9lD6Tg00;f#8R0g00<eR1g00=CR2g00>C#0#0#0#0#0#0#4#3R3g00>hR4g00?hR5g00A@R6g00@Fg00BHR7fBR8p,4scfgR9P8fAR:f@R;f?R<f>R=f=R>f<R?f;R@f0RAM91f2RBD2P7P@P9P@f:RCf9RDf8REf7RFf6RGf5RHf4RIf1RJM91PBD2f3RK,7IfERLfDRMfCRNP8P:P;P<P=P>P?P@PCPDPEPFPGPIPKP7PLP9PLPMPNP8P:P;P<P=PKM91PHPIPBPAG5PJMD6W0W2W1W<X46W3X65X:4X73X53X;3X92X81XE0W>WBX?3X=3WCWAW@WDo"). Qed.

(* [comment removed for export] *)
Theorem shape_strong_equiv_ef :
  forall source_segs rpc rph rsp rbrk rmb (rrnd : EntryDraw) (rlim : Z)
         target_segs apc aph asp abrk amb (arnd : EntryDraw) (alim : Z)
         (T : TSet) (inp : ProcInput),
  realizes source_segs scfg
    (init_config source_segs rpc rph rsp rbrk rmb rrnd rlim inp) T ->
  realizes target_segs scfg
    (init_config target_segs apc aph asp abrk amb arnd alim inp) T ->
  error_free (run_scfg scfg (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp)
  /\ error_free (run_scfg scfg (mkImage target_segs apc aph) alim (mkEntry asp abrk amb arnd) inp)
  /\ trace_equiv (bh_traces (run_scfg scfg (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp))
                 (bh_traces (run_scfg scfg (mkImage target_segs apc aph) alim (mkEntry asp abrk amb arnd) inp)).
Proof.
ltac2:(KReplay.run1 (kr_t_ShapeEF ()) ["WithCfg"] "h02Hsh12Hth21Th34abrkh44alimh53ambh63apch73aphh84arndh93asph:3inph;4rbrkh<4rlimh=3rmbh>3rpch?3rphh@4rrndhA3rsphB;source_segshC;target_segsp;1p;9p;4p;6p;Dg002Uj17Tg0035j10Tg003Zj16Tg0048j14Tg004[l91Tg00Fmj43Tg00YRj62Tg00X9lD5Tg00;f#7R0g00<eR1g00=CR2g00>C#0#0#0#0#0#0#6#4R3g00>hR4g00?hR5g00A@g00@FfAR6p,4scfgR7P6f@R8f?R9f>R:f=R;f<R<f;R=f:R>f0R?M91f1R@C3P>P7P>f9RAf8RBf7RCf6RDf5REf4RFf3RGP@M91f2RHC3fCRIfBRJP6P8P9P:P;P<P=P>PAPBPCPDPEPFPGPHg00BHRKPIP7PIPJP6P8P9P:P;P<PHM91PGP@E2PKP=P7P=P>PAPBPCPDPEPFPHM91PGP?E2MD5W1W0W:W2X45X84X53X33X93X72X61XC0W<W@X=3X;3WAW?W>WBo"). Qed.

Corollary shape_strong_equiv_ef_eq :
  forall source_segs rpc rph rsp rbrk rmb (rrnd : EntryDraw) (rlim : Z)
         target_segs apc aph asp abrk amb (arnd : EntryDraw) (alim : Z)
         (T T' : TSet) (inp : ProcInput),
  realizes source_segs scfg
    (init_config source_segs rpc rph rsp rbrk rmb rrnd rlim inp) T ->
  realizes target_segs scfg
    (init_config target_segs apc aph asp abrk amb arnd alim inp) T' ->
  t_eq T T' ->
  error_free (run_scfg scfg (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp)
  /\ error_free (run_scfg scfg (mkImage target_segs apc aph) alim (mkEntry asp abrk amb arnd) inp)
  /\ trace_equiv (bh_traces (run_scfg scfg (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp))
                 (bh_traces (run_scfg scfg (mkImage target_segs apc aph) alim (mkEntry asp abrk amb arnd) inp)).
Proof.
ltac2:(KReplay.run1 (kr_t_ShapeEF ()) ["WithCfg"] "h03Heqh12Hsh22Hth31Th42T'h54abrkh64alimh73ambh83apch93aphh:4arndh;3asph<3inph=4rbrkh>4rlimh?3rmbh@3rpchA3rphhB4rrndhC3rsphD;source_segshE;target_segsp;1p;9p;4p;2p;7p;Dg002Uj18Tg0035j10Tg003Zj14Tg0048j13Tg004[l91Tg00Fmj42Tg00Ubj27Tg00Zkj75Tg00\9lD6Tg00;f#8R0g00<eR1g00=CR2g00>C#0#0#0#0#0#0#4#3R3g00>hR4g00?hR5g00A@R6g00@FfBR7p,4scfgR8P7fAR9f@R:f?R;f>R<f=R=f<R>f;R?f0R@M91f2RAC2P?P8P?f:RBf9RCf8RDf7REf6RFf5RGf4RHf1RIM91PAC2f3RJ,7HfERKfDRLfCRMP7P9P:P;P<P=P>P?PBPCPDPEPFPHPJPKP8PKPLPMP7P9P:P;P<PJM91PGPHPAP@F5PIMD6W0W2W1W<X46W3X65X:4X73X53X;3X92X81XE0W>WBX?3X=3WCWAW@WDo"). Qed.

(* [comment removed for export] *)
Corollary srealizes_strong_equiv_error_free_scfg :
  forall (SRC TGT : Image) (en_s en_t : ExecEntry) (T : TSet) (inp : ProcInput),
  srealizes0 (img_segments SRC) scfg
    (init_config (img_segments SRC) (img_init_pc SRC) (img_phdrs SRC)
                 (en_sp en_s) (en_brk en_s) (en_mmap_base en_s) (en_draw en_s) source_alloc_limit inp) T ->
  srealizes0 (img_segments TGT) scfg
    (init_config (img_segments TGT) (img_init_pc TGT) (img_phdrs TGT)
                 (en_sp en_t) (en_brk en_t) (en_mmap_base en_t) (en_draw en_t) target_alloc_limit inp) T ->
  strong_equiv_error_free_scfg scfg SRC TGT en_s en_t inp.
Proof.
ltac2:(KReplay.run1 (kr_t_ShapeEF ()) ["WithCfg"] "p'0h01Th13inph24en_th34en_sh43TGTh52Hsh62Hth73SRCh84sbrkh93smbh:3spch;3sphh<4srndh=5ssegsh>3ssph?4tbrkh@3tmbhA3tpchB3tphhC4trndhD5tsegshE3tspi001ei016en_brki027en_drawi03<en_mmap_basei045en_spi051ii06;img_init_pci079img_phdrsi08<img_segmentsp;1p;9p;6p;3p;4p;Dp;5g00]Qj15Tg00^Sj13Tg00_Tj14Tg00`Sj19Tg00aEj1<Tg00b8j1;Tg00c1j1:Tg004[l91Tg00cej67Tg002Uj1=Tg0087j30Tg0035j16Tg003Zj1ATg0048j1@Tg0094j48Tg00X9lD?Tg005Sj5>Tg00BHf3R0f2R1f1R2f0R3D>p=2g00e<R4P4g00f9R5g00A@R6g00@FR7f5R8#5R9p,4scfgR:P9%38R;%48R<%90R=%<0R>%;0R?%:0R@g00g1RAP3M91P2C2P9P:P9P;P<P=P>P?P@g00h2R<P2M91P1C2R;P:f7R9f6RBP8f4RCP1E7[[]1]0^25]3^44P3g00;f#=RDg00<eREg00=CRFP4f8RG?09BRH#5RIP:PI%3HRJ%4HRHP=P>P?P@PAP3M91P2C2P:f:f9RK;0GPBP8PCP1E7\;[^17^06^25^35P3P5f>R;f=RLf<RM30RN#5ROP:PO%3N%4NP=P>P?P@PAP3M91P2C2PIP:PIPJPHP=P>P?P@P<P2M91P1C2P:f@RHf?RJ;0;RIA0KG9P8PCP1E7[[^17^06^25P3g00>C#6#6#6#6#6#6#A#@RNg00>hROP5fFRPfERQfD30RR#5RSP:PS%3R%4RP9PBP8PCC8RR#9%<R%;R%:RPAP3M91P2C2%5IRSP:PS%3I%4IP=P>P?P@P<P2M91P1C2P:fHR@fGR?;0PR>fA?0HJPKPGP9PBC8PCP1E7[[^17^06P3fMRGfLfK30RK#5R=P:P=%3K%4KP;PLPMf;C8RM#9%<M%;M%:MPAP3M91P2C2A0?PQRQ#5RMP:PM%3Q%4QPBP8PCP0C8RQ#9%<Q%;Q%:QP<P2M91P1C2fORQfNRMPGPHPJP;PLPAP@P?PPP9PBP8PCP<P0P1P2P3MD?P:A0QMGP>PHPJP;PLC8PRP1E7eW6W5X17X06XCOX@NX?NXENP0P1P2P3O4n01100000140104101103102X25W<X9NX8NW>P0P1P2P3O4n01100000141104101103102X35XBFXAEXDDP1P2P3O3n01105000131108106107X44W;W:W=P1P2P3O3n01105000131108106107W7o"). Qed.

End WithCfg.
