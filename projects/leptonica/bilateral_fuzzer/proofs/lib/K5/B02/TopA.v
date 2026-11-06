(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.leptonica.bilateral_fuzzer.images Require Import AsanUbsan.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.Lib Require Import MState Mem Frame Cells Step Arr Exec.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.B02 Require Import ImageA.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.Lib Require Import RzCPS.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.Spec Require Import Prelim Canon Stdio Prog.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.B02 Require Import Layout.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.B02 Require Import RT_iface D_iface D_defs D_libiface I_iodefs X_xdefs.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.AS Require Import PropExec.
Local Instance topa2_fx : PropExec.FPState := PropExec.fx0.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.AS Require Import ShapeAlg SpinAlg AsanAcct AxSymExec3 AxSymExec3Sound AsanPlanCore AsanPlan AsanPlanSound.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.ASB02 Require Import AsanPlanImages.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.AS Require Import AsanInit.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.ASB02 Require Import AsanTablesA AsanStartup.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.AG Require Import HandoffKit.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.B02 Require Import HandoffStart HandoffImage HandoffArgv HandoffCLX HandoffA RT_state RT_rep RT_init RT_init_mem HandoffRT HandoffLIB TopA_iodefs TopA_io TopA_start.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.Top Require Import TopLevelA.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib Require KReplay.
Ltac2 kr_t_TopA () := "C4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC47Corelib4Init5Logic8eq_ind_rK47Corelib4Init5Logic2eq01I47Corelib7Numbers7BinNums1Z00C69OSSVerify5KrLib2K53B028RT_iface8SEGTOP_AC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AG6Shadow3SHBC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state7VMLIMITC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes4list00C4ELinuxProcessSemantics?LinuxProcessSem3Run8valid_spC4ELinuxProcessSemantics?LinuxProcessSem3Run:valid_argvC4ELinuxProcessSemantics?LinuxProcessSem3Run:valid_envpC4ELinuxProcessSemantics?LinuxProcessSem3Run@entry_stack_fitsI47Corelib4Init9Datatypes6option00K47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic2eq00K47Corelib7Numbers7BinNums8positive01C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC69OSSVerify5KrLib2K52AS8AsanInit5SINV0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AS8AsanInit5argH0C1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib2K52AS=AsanPlanSound3APS5cs_ok00C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B024TopA9hs_all_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028HandoffA;hs_start_okC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes4andbC69OSSVerify5KrLib2K53B02:HandoffLIB9hs_lib_okC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes9andb_propI47Corelib4Init5Logic3and00C79OSSVerify5KrLib2K52AS8AsanPlan2AP2pcC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2K52AS=AsanPlanSound3APS6cfg_ofC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54Spec4Prog6argv_ZC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State4m_fsC69OSSVerify5KrLib2K54Spec5Canon6canonTC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z6eqb_eqC69OSSVerify5KrLib2K52AS8AsanInit:argH0_highC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B02:HandoffLIB6hs_libC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B027TopA_io8main_rtaC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2K52AS=AsanPlanSound3APS5co_fsC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2K52AS=AsanPlanSound3APS:holes_stmtC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B02;RT_init_mem8hs_rt_okC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib2K52AS7SpinAlg9srealizes00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B029HandoffRT:hs_hole_rtC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C69OSSVerify5KrLib2K53B026Layout6a_mainC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K55ASB02;AsanTablesA6ASAN_AC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K55ASB02>AsanPlanImages5ASEGSC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2K52AS8AsanPlan2AP3NX0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AS8AsanInit5LIMITC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K55ASB02>AsanPlanImages3APHC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K55ASB02>AsanPlanImages<asan_in_hullC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K55ASB02>AsanPlanImages<asan_hull_okC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B024TopA;asan_segtopC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B024TopA:asan_shoffC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B024TopA8asan_limC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B02:D_libiface5LIB_AC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I4ELinuxProcessSemantics?LinuxProcessSem;StackLayout9EntryDraw00I47Corelib4Init9Datatypes3nat00I79OSSVerify5KrLib2K52AS8AsanPlan2AP3acs00C1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib2K52AS:AxSymExec33AX23env00C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00K4ELinuxProcessSemantics?LinuxProcessSem<MemImageType5Image01C4ELinuxProcessSemantics?LinuxProcessSem3Run;valid_entryC4ELinuxProcessSemantics?LinuxProcessSem3Run;valid_inputC69OSSVerify5KrLib2K54Spec5Canon:canonT_nilC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B02:TopA_start@asan_startup_genC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Top9TopLevelA8S3s_stmtC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem3Run9ExecEntry00I4ELinuxProcessSemantics?LinuxProcessSem5State9ProcInput00C59OSSVerify5KrImgITgt_bilateral_fuzzer_both1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~C59OSSVerify5KrImgITgt_bilateral_fuzzer_both1M7init_pcC1@~~~~~~~~~~~~~~~~C59OSSVerify5KrImgITgt_bilateral_fuzzer_both1M5phdrsC1@~~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B024TopA:topA_holesC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Import AX2. Import AX2S. Import AP.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition hs_all_ok (ch : acs) : bool :=
  (Z.eqb (pc ch) a_main && hs_start_ok ch && hs_rt_ok ASAN_A ch && hs_lib_ok ch)%bool.

(* [comment removed for export] *)
Lemma asan_segtop : img_hi ASAN_A = SEGTOP_A.
Proof.
ltac2:(KReplay.run1 (kr_t_TopA ()) [] "p;2p10000p4p70p1000^p4p710p8g001<j20Tg001Vg0024'0o"). Qed.
Lemma asan_shoff : shadow_off ASAN_A = SHB.
Proof.
ltac2:(KReplay.run1 (kr_t_TopA ()) [] "p;2g001<j20Tg001Vg0031'0o"). Qed.
Lemma asan_lim : AsanInit.LIMIT = VMLIMIT.
Proof.
ltac2:(KReplay.run1 (kr_t_TopA ()) [] "p;2g001<j20Tg001Vg003f'0o"). Qed.

Section Cert.
  (* [comment removed for export] *)
  Variable IT0 : itab.
  Hypothesis IT0_ok : itab_sound ASEGS IT0.
  Variable HS_asan : nat -> option acs.
  Variable startup_plan : plan.
  Variable startup_shape : shape.
  Variables KC0 BFUEL FUEL : nat.
  Hypothesis startup_cert :
    check ASEGS IT0 ASAN_A NX0 AsanInit.LIMIT XN0 XE0 XB0 HS_asan KC0 BFUEL FUEL None asan_a_init startup_plan = COk startup_shape.
  Hypothesis Hshape : holes_only startup_shape = true.
  Hypothesis HS_ok : forall h ch, HS_asan h = Some ch -> hs_all_ok ch = true.

  (* [comment removed for export] *)
  Hypothesis FUZZ : fuzz_one_cps RTA LIB_A.   (* [comment removed for export] *)
  Hypothesis RC : rt_contracts RTA.
  Hypothesis IOC : forall Σ m, ART RTA Σ m -> io_consts m.

  (* [comment removed for export] *)
  Lemma topA_holes : forall (sp : word) (rdraw : EntryDraw) (brk0 : word) (argv envp : list (list byte)) (uid hw : word) (fs : Fs.Fs),
    valid_sp sp -> valid_argv argv -> valid_envp envp -> entry_stack_fits sp argv envp ->
    APS.holes_stmt ASEGS ASAN_A NX0 AsanInit.LIMIT HS_asan (SINV0 APH sp rdraw brk0 argv envp uid hw) (argH0 APH sp rdraw argv envp uid hw)
               (fun _ _ fs' => canonT (argv_Z argv) fs') fs.
Proof using HS_ok FUZZ RC IOC.
ltac2:(KReplay.run1 (kr_t_TopA ()) ["Cert"] "h02HTh13Hpch21mh31nh41Eh54FULLh61Hh72HCh83HTLh93HTRh:3HTSh;4Hfith<2Hhh=3Hsph>3Hvah?3Hveh@1RhA4argvhB4brk0hC2chhD4envphE1fhF2fshG3fs'hH1hhI2hwhJ5modelhK5rdrawhL2sphM3uidhN1zp;1p;3p;2p;8p;7p;<p;5p;9p;@p;6p;=p;Qg004bj1;Tg005Gj1@Tg005ej1ETg006Hj1FTg006hj1ZTg007]j1UTg008Tj1NTg009Kj3MTg00:Hj1DTg00:jj2LTg00;Lj36Tg00;fj1ITg00<Kj2HTg00=7j8CTg00>0j7BTg00>il<VTg00?mj1TTg00@gj12Tg00Agj21Tg00BEj1=Tg00CEj3ATg00ChR0j2>Tg00DCj17Tg00E<j59Tg00F?j18Tg00G7j1<Tg00Gjj24Tg00Hcj2?Tg00I@j2KTg00I`l9JTg00J^l@OTg00K[j6PTg00LWl=RTg000^j6GTg00MYl9STg00N`j2YTg00O`j3XTg00P^lQWTg00Q^f0R1g00R>36p=0%71g00R^R2'?p=3g00SWR3/Y1p=:g00TWR4f1R5;X1p=5P3g00UYR6g00VSR7P1g00WLR8P5f2R9f3R:f4R;f5R<f6R=f7R>f8R?f9R@f:RAf;RBg00XLRCg00YURDg00Z^g00[Zg00\Uf<REf=RFf>RGf?RHf@RIfARJfBRKfCRLg00]NfDRMfERNfFROMQWp=Qg00^J#;RP#;#;RQ#;#;#;#@#ERRg00^o%@Q#ERQ#F#FRSg0000RT%Z>%U<%N<AMA>=g00_oRUg00`NRV%DVp,7HS_asanRWP5O11LV136g00aJRV%IP#@/HR%DQ\Rg00bIP4P3P6P7P8PKPJPIPHPGPFPEGCP8PKPJPHPGPFPEFBPBP:P<P9P5P1M<Vp,5HS_okP>P=P<O3%T=#0%3>%2>'1%:>'1RQ%=>RP;A1%0Q%0P'>P0%3?%2?'1%:?'1#0%=?#0P4P=%7@P<P;D9%8L%<;'4'5P1%3A%2A'1%:A'1#0%=B#0%3E%2E'1RP%:ERQ;A5%0P%0Q'>P0%3F%2F'1#0%:F#0P4PB%7GPAP@D9fHRF#8%<@'4'5P1%3H%2H'1#0%:I#0%3JRQ%2JRJ;A5%0Q%0J'>P0%3K#0%2K#0P4PI%7LPHPGD9fMRH#8%<G'4'5P1%3M#0%2N#0g001VRGP01?51#0A6G95[R0A6G511?95#0RI[A6G:9\I1K51P5n2001000000120000000X2GW3P0^2G^3GP1fG#7R0P2P9O3A6G02PGP2P4POP1PNPMD9fSR0#8RI%<M'4'5XNGPTfNRGP4POP2PNPMD914I1'5XETPGfURIfTR:P0fRRJfQRQfPRPfORXPHfLRYfKfJPOPFPNPMPLPKP9P>P3P6P7P8PIP:P0PJPQPPPXGCR0P8PIP:PJPQPPPXFBR9PGPCPDP8PIP:PJPQPPPXPHPYM9JPOPFPNPMPLPKPEM@O%8JRE/4Gp,4FUZZp,2RCp,3IOCPJPGPYEPMGQ%<LRYP4P3P6P7P0P9PGPOPFPNPMPLPKM=REGP4PNP2PMPLD914EY'5e%7FP1EGb1b6W:W1P5P1O2n2001000000121000000b0W9W0P5P1O2n2001000000121000000b0W8W0P5P1O2n2001000000121000000b0b0W7WJW5W@W4W<WCWHP4P3P6P7PWP8PBPAP@P?P>P=P<GCP8PBPAP?P>P=P<FB%8B/41XGTVVVUP;M9SeW;W?W>W=WFXIRXMRXDSWAXBRWKWLo"). Qed.

  (* [comment removed for export] *)
  Theorem s3s_A_of : S3s_stmt AsanUbsan.M.loaded_segments AsanUbsan.M.init_pc AsanUbsan.M.phdrs.
Proof using IT0_ok startup_cert Hshape HS_ok FUZZ RC IOC.
ltac2:(KReplay.run1 (kr_t_TopA ()) ["Cert"] "h04argvh12fsh23Hveh33Hvih42enh53inpp;3p;1p;2p;Ag00c?j3;Tg00d<j3:Tg00e4j13Tg004bj10Tg005Gj19Tg005ej17Tg006Hj11Tg00F?j14Tg00Gjj25Tg00elj26Tg00filA2Tg00h0j38Tg00hng00ifg00j`R0g00l1R1g00m:R23;f1R3f0R43:%33p,3IT0p,6IT0_okp,7HS_asanp,<startup_planp,=startup_shapep,3KC0p,5BFUELp,4FUELp,<startup_certp,6Hshapeg00^J#0#0#0#9#7#1#1R5g0000R6%43R7/54W1W01674X16X05g00nAf3f2P3P4MA2W3W2W5W4A8012eo"). Qed.

  (* [comment removed for export] *)
End Cert.
