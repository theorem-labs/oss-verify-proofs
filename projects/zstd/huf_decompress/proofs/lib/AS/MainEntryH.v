(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.zstd.huf_decompress.images Require Import Asan.
From OSSVerify.Proofs.zstd.huf_decompress.lib.AS Require Import
  PropExec ShapeAlg SpinAlg AsanAcct AsanAcctImages AxSymExec3 AxSymExec3Sound AxSymRun3
  AsanPlanCore AsanPlan AsanPlanSound AsanPlanImages AsanInit AsanStartup StartupHS2Asan AsanBoot
  AsanCertDefs AsanStartupCertH AsanStartupCertHB AsanStartupCertHC AsanStartupCertHD AsanStartupCertH2
  RegsEqv0 SrzEqv MainExport MainFactsAsan MainEntry.
From OSSVerify.Proofs.zstd.huf_decompress.lib.LibA Require Import AcctCore TopLevelGen.
From OSSVerify.Proofs.zstd.huf_decompress.lib.AsanW Require Import AImg.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require Import TopLevel.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_MainEntryH () := "C47Corelib7Classes?RelationClasses9ReflexiveC59OSSVerify5KrLib2AS9MainEntry?asan_main_bootLC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8AsanInit6LIMITHC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8AsanInit9LIMITH_geC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS@AsanStartupCertH>startup_cert_hC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2ASAAsanStartupCertHB?startup_certB_hC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2ASAAsanStartupCertHC?startup_certC_hC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2ASAAsanStartupCertHD?startup_certD_hC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2ASAAsanStartupCertH2?startup2_cert_hC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem<MemImageType5Image01C4ELinuxProcessSemantics?LinuxProcessSem3Run;valid_entryC4ELinuxProcessSemantics?LinuxProcessSem3RunBvalid_input_eitherK47Corelib4Init9Datatypes4list01K4ELinuxProcessSemantics?LinuxProcessSem3Run6config01I59OSSVerify5KrLib2AS7SpinAlg9srealizes00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00K4ELinuxProcessSemantics?LinuxProcessSem3Run9ExecEntry01C4ELinuxProcessSemantics?LinuxProcessSem3Run8valid_spC4ELinuxProcessSemantics?LinuxProcessSem3Run9valid_brkC4ELinuxProcessSemantics?LinuxProcessSem3Run?valid_mmap_baseI47Corelib4Init5Logic3and00C47Corelib4Init5Logic3iffC47Corelib7Classes9MorphismsDiff_impl_subrelationC49OSSVerify5KrLib8TopLevelBvalid_entry_eitherC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State7in_argvC4ELinuxProcessSemantics?LinuxProcessSem3Run:valid_argvC4ELinuxProcessSemantics?LinuxProcessSem5State7in_envpC4ELinuxProcessSemantics?LinuxProcessSem3Run:valid_envpC4ELinuxProcessSemantics?LinuxProcessSem3Run;valid_credsC4ELinuxProcessSemantics?LinuxProcessSem5State6in_uidC4ELinuxProcessSemantics?LinuxProcessSem3Run8valid_idC4ELinuxProcessSemantics?LinuxProcessSem5State6in_gidC4ELinuxProcessSemantics?LinuxProcessSem3Run=valid_sigmaskC4ELinuxProcessSemantics?LinuxProcessSem3Run=valid_urandomI47Corelib4Init9Datatypes4list00K4ELinuxProcessSemantics?LinuxProcessSem5State9ProcInput01C4ELinuxProcessSemantics?LinuxProcessSem3Run6en_brkC4ELinuxProcessSemantics?LinuxProcessSem3Run<en_mmap_baseC4ELinuxProcessSemantics?LinuxProcessSem3Run7en_drawC4ELinuxProcessSemantics?LinuxProcessSem5State;fs_seed_tmpc59OSSVerify5KrLib2AS:MainEntryH@asan_main_boot_hC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS7SpinAlgErealizes_of_srealizesC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rC59OSSVerify5KrLib2AS9MainEntry9amain_atLC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3Run5en_spC4ELinuxProcessSemantics?LinuxProcessSem3Run;init_configI59OSSVerify5KrLib2AS8ShapeAlg8realizes00C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3Run@entry_stack_fitsC4ELinuxProcessSemantics?LinuxProcessSem5State5in_fsC4ELinuxProcessSemantics?LinuxProcessSem2Fs8valid_fsC4ELinuxProcessSemantics?LinuxProcessSem5State;in_image_fsC4ELinuxProcessSemantics?LinuxProcessSem2Fs@fs_keys_relativeC4ELinuxProcessSemantics?LinuxProcessSem5State9in_nofileC4ELinuxProcessSemantics?LinuxProcessSem3Run<valid_nofileC4ELinuxProcessSemantics?LinuxProcessSem5State8in_hwcapC4ELinuxProcessSemantics?LinuxProcessSem3Run;valid_hwcapC4ELinuxProcessSemantics?LinuxProcessSem5State:in_va_sizeI47Corelib4Init5Logic2eq00C4ELinuxProcessSemantics?LinuxProcessSem5StateBsource_alloc_limitC59OSSVerify5KrLib5AsanW4AImg5asegsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW4AImg9a_init_pcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW4AImg7a_phdrsC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State6VaSize00K4ELinuxProcessSemantics?LinuxProcessSem5State6VaSize02I4ELinuxProcessSemantics?LinuxProcessSem3Run9ExecEntry00I4ELinuxProcessSemantics?LinuxProcessSem5State9ProcInput00C59OSSVerify5KrLib2AS8ShapeAlg4TSetC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5event00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00K47Corelib7Numbers7BinNums8positive03I4ELinuxProcessSemantics?LinuxProcessSem;StackLayout9EntryDraw00C4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsI4ELinuxProcessSemantics?LinuxProcessSem5State;InputStream00I4ELinuxProcessSemantics?LinuxProcessSem5State8NetQueue00I47Corelib4Init9Datatypes4bool00C4ELinuxProcessSemantics?LinuxProcessSem3Run;valid_inputC4ELinuxProcessSemantics?LinuxProcessSem3RunQvalid_input_either_of_valid_inputc59OSSVerify5KrLib2AS:MainEntryH;asan_boot_RC1?~~~~~~~~~~~~~~~".
Import ListNotations. Import AX2. Import AX2S. Import AP. Import APS.
Open Scope Z_scope.

Section BridgeH.
  Variable sp brk0 mbase : word.
  Variable rdraw : EntryDraw.
  Variable argv envp : list (list byte).
  Variable fs : Fs.Fs.
  Variable stdin : InputStream.
  Variables uid gid : word.
  Variable groups : list word.
  Variable net : NetQueue.
  Variables nof sigm : word.
  Variable hw : word.
  Variable abt : bool.
  Variable urnd : InputStream.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hbrk : valid_brk ASEGS brk0.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Hypothesis Hfit : entry_stack_fits sp argv envp.
  Hypothesis Huid : valid_id uid.
  Hypothesis Hhw : valid_hwcap hw.

  (* [comment removed for export] *)
  Variable T : TSet.
  Hypothesis T_nil : T [].
  Hypothesis MAINH : forall ms mo,
    amain_atL source_alloc_limit (mkEntry sp brk0 mbase rdraw) (AsanInit.inp argv envp fs stdin uid gid hw groups net nof sigm abt urnd) ms mo ->
    srealizes asegs (mkCfg ms mo) T.

  Theorem asan_main_boot_h :
    srealizes asegs (init_config asegs Asan.M.init_pc a_phdrs sp brk0 mbase rdraw source_alloc_limit
                               (AsanInit.inp argv envp fs stdin uid gid hw groups net nof sigm abt urnd)) T.
Proof.
ltac2:(KReplay.run1 (kr_t_MainEntryH ()) ["BridgeH"] "p;Rp-1p10000p4p710p9g000\lR0Tf0f1f2f3f4f5f6f7f8f9f:f;f<f=f>f?f@fAfBfCfDfEfFfGg001]g002TfHfIfJg003Ng004Ug005^g006gg0080MR0p=1p,2spp,4brk0p,5mbasep,5rdrawp,4argvp,4envpp,2fsp,5stdinp,3uidp,3gidp,6groupsp,3netp,3nofp,4sigmp,2hwp,3abtp,4urndp,3Hspp,4Hbrkp,3Hvap,3Hvep,4Hfitp,4Huidp,3Hhwp,1Tp,5T_nilp,5MAINHMK1o"). Qed.
End BridgeH.

(* [comment removed for export] *)
Theorem asan_boot_R : forall en inp (T : TSet),
  valid_entry (mkImage asegs a_init_pc a_phdrs) en inp -> valid_input_either inp -> T [] ->
  (forall ms mo, amain_atL source_alloc_limit en inp ms mo -> srealizes asegs (mkCfg ms mo) T) ->
  ShapeAlg.realizes asegs (init_config asegs a_init_pc a_phdrs (en_sp en) (en_brk en) (en_mmap_base en) (en_draw en) source_alloc_limit inp) T.
Proof.
ltac2:(KReplay.run1 (kr_t_MainEntryH ()) [] "p'0h01Hh12moh22msh32Hih44Hnofh54Hrelh65Hsigmh73Hurh85MAINHh94Hfith:3Hfsh;4Hgidh<3Hhwh=4Huidh>3Hvah?5Hvaszh@3HvehA2HvhB1ThC3inphD4vaszhE4HbrkhF3HmbhG3HsphH4TnilhI3abthJ4argvhK4brk0hL2enhM4envphN3gidhO6groupshP2hwhQ3ifshR5lemmahS5mbasehT3nethU3nofhV5rdrawhW4sigmhX2sphY5stdinhZ3tmph[3uidh\4urndi001ei016en_brki027en_drawi03<en_mmap_basei045en_spi05Ain_abort_terminali067in_argvi077in_envpi086in_gidi099in_groupsi0:8in_hwcapi0;;in_image_fsi0<6in_neti0=9in_nofilei0>:in_sigmaski0?8in_stdini0@6in_tmpi0A6in_uidi0B:in_urandomi0C:in_va_sizei0D1pp;3p;1p;2p;4p;9p;?p;Kp;<p;5g0099j3rTg00:6j3QTg00:nj1@Tg00;mj1aTg00<Mj2oTg00=Bj3GTg00>=j1ATg00>bj1YTg00?@j1XTg00?cj40Tg00@[j1RTg00APj2HTg00BFj1>Tg00CBR0j23Tg00C]j2jTg00D6j3dTg00Dgl9bTg00Egj1FTg00F]j1MTg00GTj1=Tg00HJj1BTg00IAj1<Tg00J9j1KTg00Jnj1;Tg00Kcj1JTg00LXj1:Tg00MRj18Tg00NLj1UTg00Nll?1Tg00Ofj1`Tg00PYj1_Tg00QRj1^Tg00RFj2pTg00S@lKnTg00TCj4mTg00UHl<lTg00Ufj5kTg00Vaj1]Tg00WSl9ZTg00XKj3iTg00YFj3hTg00ZCj1eTg00[7j1cTg00[kj1fTg00\ej1gTg00]aj1[Tg00^Yj1\Tg00_Rj1NTg00`Ij1OTg00aAj1STg00b:j3TTg00bTR1f3R2f2R3f1R4f0R5Dkp=Eg00cUR6P6g00dJR7g00eCR8f5R9#]f4R:#`%_2%^3P1P4M9Z;i5p=2%F4%=55h3p=71345,33p=6%e5#cp=9%f5#gp=4%[:#\%:2%N3#Og00f:R;%S4g00g1R<3T%85'3'3'3'3p=5%<4/35p=L%[5#\p=C%S4=T;<%85'3p=?%:3%N4#O/35'3p=W%N4#O/35p=V%N5#Op=I%S5=T;<p=PP5P4P3P2P:P9f6R=f7R>f8R?f9R@f:RAf;RBP<f<RCf=RDM?1p=DP6P7P8%]:P2P3P4P1P5M9Zp=qg00ghR1P1g00h`R1g00iZREAr678RF?Q34%@3RGP3g00jO#aO1RHg00kERIg00lLRJP>P=P4P5CE1o34RK=G6=RL[]1]2P=P=P=P=P9P:E2[[[[]B]CP5g00mB#A#A#ARM#A#A#A#Y#XRNg00mgP9P:P2P3C0=QF4PAP@P?P>C0ROP=P4P5CEPL[^1J^2IP@P?P>P=C0=QF9%R@1H6?%>>A7@99'336RL'jAQFO=%RARO1H6@%>?A7A==36RF'3;d5WRP6P7P8P@P?P>P=P9P3M9bP2O2PLP0POPFPBPAP@P?C0RFPFPFPFP>P=E2P5%RC1H6C%>BA7D@@36P01H6D%>Cf>RF?7AA'3f?ROPFPDPCC0RLPLPLPLPBPAE2P51H6O%>OfARL?7DD'3P0f@R8#>fBR7?7FFfCRPP7PLP8C0RQPQPQPQPOPFE2P5%>7fERQ?7LLPO%@7P0%FP#M%=P#B%9P%4P%<PPPPPPPPPPPD53636fHRRfGRSfFRTPQC0RUPUPUPUfDRUPPE2P5%FQ#M%=T#B%9T%4T%<TPTPTPTPTPTD53636P0%=S#B%9S%4SPSPSPSPSPSD5,LS36fLRVfKRWfJRXfIRYC0RZPZPZPZPRPSE2P5%=Y#B%9X%4XPXPXPXPXPXD5,LX36P0%9W%4W%<WPWPWPWPWPWD536fPRZfOR[fNR\fMR]C0R^P^P^P^PVPWE2P5%9]%4\%<\P\P\P\P\P\D536P0%4[P[P[P[P[P[D5,L[fTR^fSR_fRR`fQRaC0RbPbPbPbPZP[E2P5%4aP`P`P`P`P`D5,L`P0%<_P_P_P_P_P_D5fXRbfWRcfVRdfUReC0RfPfPfPfP^P_E2P5%<eP0%Kd#;%Jd#;PcPcPcPcPcD5f\Rdf[R^fZRffYRgC0RhPhPhPhPbPcE2[P5%Kb#;%Jg#;PfPfPfPfPfD5P0%C^1?^^9W^^f`Rff_Rbf^Rcf]RhC0RiPiPiPiPdP^E2P5%Ch1?cc9WccP0%:b1?bb,VbfdRcfcRhfbR^faRdC0RiPiPiPiPfPbE2P5%:d1?^^,V^P0%Ih1?hhfhR^fgRdffRbfeRfC0RiPiPiPiPcPhE2P5%If1?bbP0%Pd%8dflfkR0fjRffiRhC0RcPcPcPcP^PdE2P5%Ph%8fP1fpRf?755%@4ftfsfrfqC0P:P4P5CEAG6Kf[^1J^2I%F2#M%=:#B%99%4=%K>#;%J?#;%C@%:A%IB%PC%8Df~f}f|f{C0RfPfPfPfPFfyE2]7]?]<]6]4];]=]5]:]@]>]8]3]9P0%YM#X#U#URMg00ngR0g00oURf%UNg010Qg011Jp+01NRhPFPDPCPBPAP@P?P>P=P9P:P2P3P4P5M?1Rd;7dPOPFPDPCPBPAP@P?P>P=P9P:P2P3P4M?1#@p+01Rp+01QRdp+01Pp+01OC0P7PLP8POPFPDPCPBPAP@P?P>P=P9P:M?1RcP4P5CEAG6Kh[^1J^2IPLP8POPFPDPCPBPAP@P?P>P=P9P:P2M?1#F#M%=c#BPPP7PLP8POPFPDPCPBPAP@P?P>P=P9M?1#9PUPPP7PLP8POPFPDPCPBPAP@P?P>P=M?1#4PQPUPPP7PLP8POPFPDPCPBPAP@P?P>M?1#K#;PTPQPUPPP7PLP8POPFPDPCPBPAP@P?M?1#J#;PSPTPQPUPPP7PLP8POPFPDPCPBPAP@M?1#CPRPSPTPQPUPPP7PLP8POPFPDPCPBPAM?1#:PYPRPSPTPQPUPPP7PLP8POPFPDPCPBM?1#IPXPYPRPSPTPQPUPPP7PLP8POPFPDPCM?1#PPWPXPYPRPSPTPQPUPPP7PLP8POPFPDM?1#8P;P<P]PVPWPXPYPRPSPTPQPUPPP7P5P8POM?1#@p+01`R<p+01_Rcp+01^Rhp+01]RiC0PZP[P\P]PVPWPXPYPRPSPTPQP2PPP7M?1RjP4P5CEp+01\Rk9G6K[^1J^2IP[P\P]PVPWPXPYPRPSPTPQPUP3P7PLM?1#4%CjPaPZP[P\P]PVPWPXPYPRPSPTP:PUPPM?1#:P`PaPZP[P\P]PVPWPXPYPRPSP9PQPUM?1#8p+01cp+01bRjp+01aRlP<C0RmPmPmPmP_P`PaPZP[P\P]PVPWPXPYPRP=PTPQM?1PhE2]7]6]4]5]8]3XD;PVPWPXPYPRPSPTPQPUPPP7PLPOPFM>D#@PcPhPiPkC0P[P\P]PVPWPXPYPRPSPTPQPUP7PLM>DRkP4P5CEp+01[9G6K[^1J^2IP\P]PVPWPXPYPRPSPTPQPUPPPLP8M>D#4%CkPZP[P\P]PVPWPXPYPRPSPTPQPPP7M>D#:PaPZP[P\P]PVPWPXPYPRPSPTPUPPM>D#8P6PjPlP<PcC0R6%`6%_6%^6P`PaPZP[P\P]PVPWPXPYPRPSPQPUM>DDqPiPjPlP<PcP`Pa1pZUP[P\P]PVPWPXPYPRPSPQp+01UPdP8POPPPCP?Pip+01ZP:MKnCmW7W6W4W5W8W3P8P4PCPBP>P:P2P5M<lW7W?W<W6W4W;W=W5W:W@W>W8W3W9XZ0X\fXD;WIXPNXWNXUNWTWOXNNX[NWYWQXMMWJPFPDPCPBPAP@P?P>P=P9P:P2P3P4P5O?n0110D0001?110610710;10?10A10810910<10=10>10:10510C10B10@PgP^PbPePaP]PYP7PLPDP@P9P4P5O>W7W?P4P5O2n2001000000121000000W0W<P4P5O2n2001000000121000000W0W6P4P5O2n2001000000121000000W0W4P4P5O2n2001000000121000000W0W;W=P4P5O2n2001000000121000000W0P4P5O2n2001000000121000000W0W5P4P5O2n2001000000121000000W0W:P4P5O2n2001000000121000000W0W@P4P5O2n2001000000121000000W0W>P4P5O2n2001000000121000000b0W9WFP4P5O2n2001000000121000000W0WEP4P5O2n2001000000121000000W0WGP4P5O2n2001000000121000000bAW8XHHX3GWAXBEXC1WVXSNXKNWXP2P3P4P5O4n01100000141104101103102WLo"). Qed.

Corollary asan_boot_R_valid : forall en inp (T : TSet),
  valid_entry (mkImage asegs a_init_pc a_phdrs) en inp -> valid_input inp -> T [] ->
  (forall ms mo, amain_atL source_alloc_limit en inp ms mo -> srealizes asegs (mkCfg ms mo) T) ->
  ShapeAlg.realizes asegs (init_config asegs a_init_pc a_phdrs (en_sp en) (en_brk en) (en_mmap_base en) (en_draw en) source_alloc_limit inp) T.
Proof.
ltac2:(KReplay.run1 (kr_t_MainEntryH ()) [] "h02Hih12Hvh21Th32enh43inpp;3p;1p;2p;5g0099j34Tg00:6j33Tg011jj10Tg012bj21Tg0140j52Tg00ghg00h`g00iZg00cUg00dJg00eC34f2R0f1R133%00f4f3R2P0P1f0,12D2W0W1W2W4W3o"). Qed.
