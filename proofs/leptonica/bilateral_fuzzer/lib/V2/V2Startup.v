(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.leptonica.bilateral_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.CliDriver Require Import Amb.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common Require Import ShapeAlg PureModel RefNodesMF StartupTac ArgvEnv RefLayout.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Reloc Require Import Reloc.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Musl Require StartupBase StartupDefs Startup.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.V2 Require Import V2StartupDefs V2Reloc V2RelocCode V2RelocSites V2RelocImg V2RelocMusl V2RelocStart.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib Require KReplay.
Ltac2 kr_t_V2Startup () := "I47Corelib4Init9Datatypes4list00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C4ELinuxProcessSemantics?LinuxProcessSem5State8m_haltedK47Corelib4Init9Datatypes6option02I47Corelib4Init5Logic2eq00I47Corelib4Init9Datatypes4prod00C4ELinuxProcessSemantics?LinuxProcessSem5State9m_vm_lazyK47Corelib4Init9Datatypes4list01I5ARocqVerifyHarness?AgentSubmission6Common6CatSim6msteps00K4ELinuxProcessSemantics?LinuxProcessSem3Run6config01I5ARocqVerifyHarness?AgentSubmission6Common8ShapeAlg8realizes00C5ARocqVerifyHarness?AgentSubmission6Common8ShapeAlg9rz_mstepsC5ARocqVerifyHarness?AgentSubmission6Common:StartupTac3bwdI4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00C5ARocqVerifyHarness?AgentSubmission6Common8ShapeAlg4TSetK47Corelib7Numbers7BinNums8positive03I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00K47Corelib7Numbers7BinNums8positive01C4ELinuxProcessSemantics5Riscv7Prelude5bvmapI6ARocqVerifyHarness?AgentSubmission6Common4Musl7Startup:main_entry00i5ARocqVerifyHarness?AgentSubmission2V29V2Startup:main_entry00C6ARocqVerifyHarness?AgentSubmission6Common5Reloc5Reloc8rl_deltaC6ARocqVerifyHarness?AgentSubmission6Common5Reloc5Reloc2rlC45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z3subC45stdpp9bitvector;definitions7Z_to_bvK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3addC5ARocqVerifyHarness?AgentSubmission6Common7ArgvEnv5argcNC47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3mulC46Stdlib5Lists4List2InC5ARocqVerifyHarness?AgentSubmission6Common8MemSplit3wfJC6ARocqVerifyHarness?AgentSubmission6Common4Musl7Startup6J_mainC6ARocqVerifyHarness?AgentSubmission6Common9CliDriver3Amb5a_uidC6ARocqVerifyHarness?AgentSubmission6Common9CliDriver3Amb7a_hwcapC6ARocqVerifyHarness?AgentSubmission6Common9CliDriver3Amb6a_drawC5ARocqVerifyHarness?AgentSubmission6Common8PropExec8wrap_memC6ARocqVerifyHarness?AgentSubmission6Common4Musl;StartupDefs6D_mainC5ARocqVerifyHarness?AgentSubmission6Common8MemSplit4cmemI47Corelib4Init5Logic3and00I47Corelib4Init5Logic2ex00k5ARocqVerifyHarness?AgentSubmission2V29V2Startup:main_entry01K45stdpp9bitvector;definitions2bv01C5ARocqVerifyHarness?AgentSubmission6Common8PropExec4getrK47Corelib4Init9Datatypes4list02K47Corelib4Init5Logic4True01I6ARocqVerifyHarness?AgentSubmission6Common9CliDriver3Amb3Amb00C5ARocqVerifyHarness?AgentSubmission2V27V2Reloc8v2_relocK47Corelib7Numbers7BinNums1Z01C6ARocqVerifyHarness?AgentSubmission6Common4Musl:RelocStart4RPH0C56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z6moduloC4ELinuxProcessSemantics?LinuxProcessSem5State<sp_window_loC4ELinuxProcessSemantics?LinuxProcessSem5State<sp_window_hiI47Corelib7Numbers7BinNums1Z00C56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z3powC45stdpp9bitvector;definitions4BvWfC5ARocqVerifyHarness?AgentSubmission6Common8PropExec7seg_romC5ARocqVerifyHarness?AgentSubmission6Common8PropExec4mkstC4ELinuxProcessSemantics?LinuxProcessSem3RunAsegments_reservedC6ARocqVerifyHarness?AgentSubmission6Common9CliDriver3Amb<mkProcInputCC4ELinuxProcessSemantics?LinuxProcessSem5State:init_modelC4ELinuxProcessSemantics?LinuxProcessSem5State8with_tidC45stdpp9bitvector;definitions5bv_eqC56Stdlib6ZArith6BinInt1Z4of_NK47Corelib4Init5Logic2eq01c5ARocqVerifyHarness?AgentSubmission2V29V2Startup<main_entry_LC47Corelib4Init5Logic8eq_ind_rC6ARocqVerifyHarness?AgentSubmission6Common4Musl7Startup?ref_startup_secC5ARocqVerifyHarness?AgentSubmission2V2;V2RelocCode7v2_codeC5ARocqVerifyHarness?AgentSubmission2V2<V2RelocSites8v2_sitesC5ARocqVerifyHarness?AgentSubmission2V2:V2RelocImg6v2_imgC5ARocqVerifyHarness?AgentSubmission2V2:V2RelocImg7v2_dataC5ARocqVerifyHarness?AgentSubmission2V2;V2RelocMusl5v2_rwC5ARocqVerifyHarness?AgentSubmission2V2<V2RelocStart8v2_startC5ARocqVerifyHarness@ProcessOversightJTgt_bilateral_fuzzer_ubsan1M7init_pcC4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsI4ELinuxProcessSemantics?LinuxProcessSem5State;InputStream00C5ARocqVerifyHarness@ProcessOversightJTgt_bilateral_fuzzer_ubsan1M?loaded_segmentsC5ARocqVerifyHarness?AgentSubmission6Common8PropExec3fx0I47Corelib7Numbers7BinNums1N00C4ELinuxProcessSemantics?LinuxProcessSem3Run8valid_spC4ELinuxProcessSemantics?LinuxProcessSem5State7in_argvC4ELinuxProcessSemantics?LinuxProcessSem3Run:valid_argvC4ELinuxProcessSemantics?LinuxProcessSem5State7in_envpC4ELinuxProcessSemantics?LinuxProcessSem3Run:valid_envpC6ARocqVerifyHarness?AgentSubmission6Common9CliDriver3Amb6amb_ofC4ELinuxProcessSemantics?LinuxProcessSem5State5in_fsC4ELinuxProcessSemantics?LinuxProcessSem5State8in_stdinc5ARocqVerifyHarness?AgentSubmission2V29V2Startup?ref_startup_secI4ELinuxProcessSemantics?LinuxProcessSem;StackLayout9EntryDraw00I4ELinuxProcessSemantics?LinuxProcessSem5State9ProcInput00c5ARocqVerifyHarness?AgentSubmission2V29V2Startup6me_memc5ARocqVerifyHarness?AgentSubmission2V29V2Startup6J_mainC5ARocqVerifyHarness?AgentSubmission2V2=V2StartupDefs6D_mainC5ARocqVerifyHarness?AgentSubmission6Common8PropExec3rdnC5ARocqVerifyHarness?AgentSubmission6Common8MemSplit>rdn_cmem_aboveI47Corelib4Init9Datatypes3nat00C5ARocqVerifyHarness@ProcessOversightJTgt_bilateral_fuzzer_ubsan1M5phdrsC5ARocqVerifyHarness?AgentSubmission6Common8MemSplit=cmem_at_aboveC47Corelib4Init5Logic3notK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC5ARocqVerifyHarness?AgentSubmission6Common8MemSplit6in_winC5ARocqVerifyHarness?AgentSubmission6Common8MemSplit;cmem_at_winK46Stdlib9micromega5Tauto8GFormula04C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01C4ELinuxProcessSemantics?LinuxProcessSem5State>stack_max_sizeI46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC5ARocqVerifyHarness?AgentSubmission6Common8MemSplit6win_loK46Stdlib9micromega7EnvRing5PExpr03C5ARocqVerifyHarness?AgentSubmission6Common8MemSplitAstore_ok_cmem_winC5ARocqVerifyHarness?AgentSubmission6Common8MemSplit<cmem_at_dataC5ARocqVerifyHarness?AgentSubmission6Common8MemSplit=rdn_cmem_data".
Import ListNotations.
Open Scope bv_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.
Abbreviation RPH := Ubsan.M.phdrs.
(* [comment removed for export] *)
Local Notation rsegs := Ubsan.M.loaded_segments (only parsing).
Local Notation rpc := Ubsan.M.init_pc (only parsing).
Local Notation rph := Ubsan.M.phdrs (only parsing).

(* [comment removed for export] *)

(* [comment removed for export] *)
Section VP1. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma bwd_rz : forall segs model K,
  m_halted model = None -> m_vm_lazy model = [] ->
  bwd segs (fun st => realizes segs (mkCfg st model) K).
Proof.
ltac2:(KReplay.run1 (kr_t_V2Startup ()) ["VP1"] "h02sth12Hhh25Hlazyh33Hmsh44Hst'h51Kh65modelh74segsh83st'p;1p;3p;2p;9g0000j11Tg000Pj10Tg0015j1:Tg001Sj15Tg0026j1?Tg002Xj1<Tg003Oj1;Tg0041j32Tg004Kj29Tg004kj16Tg005cj17Tg006Cj38Tg007>j23Tg0083j34Tg0092l9>Tg00:0j2=Tg00:j#1g00;ig00<_g00=X#0#0#0#0#0#0#:#5R0#?f1R1#<%;0321900R0#1f2R2#6%7032g00>=R0f6R3f0R4781f7R51313f5R634f8f3R7P2P5P3P6f4R3P1P4M9>W4W3X80W01343=467X00,=3eW2W1W5W6W7o"). Qed.
End VP1.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition J_main {AMB : Amb} (sp0 : word) (av ev : list (list byte)) (s1v : word) : word -> option byte :=
  let J6 := J_tls sp0 (J_aux sp0 av ev a_uid a_hwcap (J_lsm sp0 av (fun _ => Some (Z_to_bv 8 0))))
              (Z_to_bv 64 0x3b7f0) (pn_w sp0 av ev) s1v (Z_to_bv 64 0x764f8)
              (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) in
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes J6
    (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 0x3b7f8)))   (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0)))           (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0)))          (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0)))          (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0)))          (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0)))          (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 (Z_to_bv 64 0x3b9ec)))    (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (argv_w sp0)))             (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 72)) (word_to_le_bytes 8 (argc_w av)))              (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 88)) (word_to_le_bytes 8 (Z_to_bv 64 0x3b93c)))    (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 96)) (word_to_le_bytes 8 (Z_to_bv 64 0x44e28)).    (* [comment removed for export] *)

(* [comment removed for export] *)
Record main_entry {AMB : Amb} (sp0 : word) (av ev : list (list byte)) (tid : word)
       (regs : bvmap 5 word) (mem : word -> option byte) : Prop := {
  me_ra  : getr regs 1 = Z_to_bv 64 0x3b9fc;
  me_sp  : getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 48);
  me_gp  : getr regs 3 = Z_to_bv 64 0x10800;
  me_tp  : getr regs 4 = Z_to_bv 64 0x56270;
  me_s0  : getr regs 8 = Z_to_bv 64 (bv_unsigned sp0 + 8);
  me_s1  : getr regs 9 = argcN av;
  me_a0  : getr regs 10 = argcN av;
  me_a1  : getr regs 11 = Z_to_bv 64 (bv_unsigned sp0 + 8);
  me_a2  : getr regs 12 = Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av));
  me_s2  : getr regs 18 = Z_to_bv 64 0x17868;
  me_s3  : getr regs 19 = Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av));
  me_szero : forall r : reg, In r [20; 21; 22; 23; 24; 25; 26; 27]%list -> getr regs r = Z_to_bv 64 0;
  me_mem : exists (J : word -> option byte) (s1v : word),
             wfJ sp0 J /\ J = J_main sp0 av ev s1v
             /\ mem = cmem sp0 (wrap_mem RPH sp0 av ev a_uid a_hwcap a_draw) J (D_main sp0 av ev a_hwcap a_draw tid)
}.

(* [comment removed for export] *)
Lemma main_entry_L : forall {AMB : Amb} sp0 av ev tid regs mem,
  @Startup.main_entry v2_reloc AMB sp0 av ev tid regs mem -> main_entry sp0 av ev tid regs mem.
Proof.
ltac2:(KReplay.run1 (kr_t_V2Startup ()) [] "p'0h03AMBh11Hh21Jh32avh42evh52f1h63f10h73f11h83f12h93f13h:2f2h;2f3h<2f4h=2f5h>2f6h?2f7h@2f8hA2f9hB3memhC1rhD4regshE3s1vhF3sp0hG3tidi005me_a0i015me_a1i025me_a2i035me_gpi046me_memi055me_rai065me_s0i075me_s1i085me_s2i095me_s3i0:5me_spi0;8me_szeroi0<5me_tpp;1p;2p;8p;7p;3p;6p;4p;Dg000Pj10Tg0015j1ATg001Sj1>Tg0000j1KTg00?Dj11Tg00?ij2ZTg0026j1XTg00@UR0j8WTg00AZj7VTg00BXj2?Tg00CXj2BTg00DRj2;Tg00E<j2[Tg00EYj28Tg00F?j14Tg00F]j2:Tg00G:j1DTg00H3j2CTg00HSj1FTg00I3j2GTg005cj1UTg00IPj3TTg00Igj2OTg00J_j6NTg0041j3=Tg00K^j1MTg00L]j1PTg00M^j1QTg00N^j7LTg00O[j7RTg00P^j4STg00QWj2JTg00R2j2ITg00RLlD]Tg00SJj3@Tg00Smj2HTg00Tfj3\Tf0R1#0#0p=2%11#1p=7%11#0p=9%01#1p=<%01#4p=6f4R2f3R3f2R4f1R5#4g00UFR63@'H;=1p=3A@516p=Y1H45==31p=EA@456=\31p=5g00Ubg00=XR6#0R7#0R8#0R9#0R:#2#AR;#>R<%A9#>R=#KR>#KR?%17R@#ARA/Z<%X=\<R=g00VaRBf6RCf5RDP2P3P4P5P1GWP0PBf7R0PCPDP2P3P4P5f8REP0PCPDP2P3P4FVP1P<f?PAP6%16R6#1#7RF#1#7#2,?B%0@RG#1RH#0#9#<#2#<#9#6'BD3P<f@PAP7fDR7,;;%06RI#0RJ#0RK#6'[,8;D3P<fAPAP6%1:#2#2#2#2#2#6,8;D3P<fBPAP8%18R8#1R6#9#9#<#<,?B%1@R@#1RL#9#7#7#<#7#2#6'BD3P<fC%49R9,YAfGRM,;;/:9,8;CEP<P7PAP8%DMD3P<fEPAPGfHR7#DD3P<fFPAP@fJRN,;;/:9,8;D3P<PMPAPJfKRM,;;%4:R:':1C>N#F,G9':,8;D3P<P7PA%08%0F#7#2,?B%06#2#7#9#9#2#6'BD3P<fIPAP6fMR6,;;/::fLR:,C>#F,G9':,8;D3%>AR9P9PA%6GP9PA%4HP9PA%6@P9PA%4LP9PA%4KP9PA%1J#4P9PA%1IRI#6P9PA%1I#4%U9C5C5C5C5C5C5C5C59T91P<P:P5g00WY,8;CE[]CfQR;/O5PBfRR9P;fPRIfORAP1EN9==5P;g00X7P;PIPA%M9%P9RJ%Q9R9FLP5PBP;PIPAPJP9fNR9FRCS9==:'J'JXE<,I<X2=,I=P;PIPAP9P6P:PMf<RMf;R:f:R6f9R9PEP0PCPDP2P3P4P5P1MD]W9W8W7W6WAW@W?W>W=W<W;W:W5PMP:P6P9PEP0PCPDP2P3P4P5P1O=n80000000010000001=110510:10310<10610710010110210810910;104W1WBWDXG<X4?W3WFW0o"). Qed.

Section Assembly.
  Context {AMB : Amb}.
  #[local] Existing Instance fx0.   (* [comment removed for export] *)
  Variable sp : word.
  Variables argv envp : list (list byte).
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Hypothesis Hvsp : valid_sp sp.

  Lemma Hlo : (0x7fff80000000 <= bv_unsigned sp)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_V2Startup ()) ["Assembly"] "h01Hh12_Hh21vp;1p;2p;3g0015j1:Tg00DRj28Tg00Y7j24Tg00F?j17Tg00YSj2;Tg0041j39Tg00QWR0j25Tg00?Dj13Tg000Pj12Tf0R1#2#2#2#2p=0%21#2p=6%31#3p=1p,4Hvspg00Z3g00=XR2#0R3#6#:p,2sp'8R4'4R5g00Zn,44g00[i%73,;4g00WY39'5R3'5P0P5P3%32#1#1#1#1#1#1#1#2#6#0#0#0#0#0#0#0#7/44P1f1R4X13X05P4P1O2n2001000000120000000b2o"). Qed.
  Lemma Hhi : (bv_unsigned sp <= 0x800000000000)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_V2Startup ()) ["Assembly"] "h01Hh12H0h22_Hh33_H0h41vp;1p;2p;3g0015j17Tg00DRj25Tg00Y7j22Tg00F?j14Tg00YSj28Tg0041j36Tg00QWR0j23Tg000Pj10Tf0R1#0#0#0#0p=:%01#0p=9%01#0#0#0#0#0#0#0p=1p,4Hvspg00Z3g00=X#:R2#9R3#7p,2sp'5R4'2R5g00Zn,24R6g00[i%42,84g00WY36R2'3R7'3P0P5P7%03#1#1#1#1#1#4,24R4P1P0P6P2P4P1f1R4X32X06P4P1O2n2001000000120000000X17X25P4P1O2n2001000000121000000b4o"). Qed.
  Lemma Hal : (bv_unsigned sp mod 16 = 0)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_V2Startup ()) ["Assembly"] "h01Hh12H0h22_Hh33_H0h41vp;1p;2p;3g000Pj10Tg0015j17Tg00DRj23Tg00Y7j21Tg00F?j16Tg00YSj25Tg0041j34Tg00QWR0j22Tp,4Hvspg00Z3g00=X#0#0#0#0R1#0#0#7p,2sp'3R2'1R3g00Zn,12R4g00[i%61,52g00WY34R2'2R1'2P0P3P1P2f0R5P0P4P2P2P5P5X02X34f1R4P5O2n2001000000120000000X11X23P4P5O2n2001000000120000000b4o"). Qed.

  Let J0 : word -> option byte := fun _ => Some (Z_to_bv 8 0).

  (* [comment removed for export] *)
  Ltac side Hva Hve HG :=
    first [ exact Hva | exact Hve | exact Hlo | exact Hhi | exact Hal | exact HG
          | apply wfJ_const
          | lazymatch goal with |- getr _ _ = _ =>
              gres; first [ assumption | reflexivity | bveq
                          | match goal with H : getr ?rs ?n = _ |- getr ?rs ?n = _ =>
                              rewrite H; unfold envp_w, envp_ptr, argv_w, pn_w, argc_w;
                              first [reflexivity | f_equal; lia | bveq] end ] end
          | idtac ].

  Theorem ref_startup_sec : forall brk mbase lim fs0 stdin0 K,
    (forall tid regs mem,
       (0 < bv_unsigned tid < 2^22)%Z ->
       main_entry sp argv envp tid regs mem ->
       realizes rsegs (mkCfg (mkst (fx:=fx0) regs (0x17868 : word) mem (seg_rom rsegs))
                             (with_tid tid (init_model (segments_reserved rsegs) brk mbase sp lim
                                                      (mkProcInputC argv envp fs0 stdin0)))) K) ->
    realizes rsegs (init_config rsegs rpc rph sp brk mbase a_draw lim (mkProcInputC argv envp fs0 stdin0)) K.
Proof.
ltac2:(KReplay.run1 (kr_t_V2Startup ()) ["Assembly"] "h01Hh11Rh22b1h32b2h43memh51nh64regsh73tidh82HKh94Htidh:1Kh;2MEh<1bh=3brkh>3fs0h?3limh@5mbasehA6stdin0p;1p;2p;7p;3p;5p;6p;8p;Gg000Pj11Tg0015j1>Tg001Sj14Tg00?Dj12Tg00?ij2RTg0026j1MTg00DRj23Tg00\Gj2@Tg00F?j1;Tg00\cj2ETg00QWR0j2DTg00AZj7TTg00]@j2STg00SJj3CTg00]cj1QTg00^_j5?Tg00_Xj1LTg00`Vj5<Tg00a\j68Tg00bUj2:Tg007>j29Tg0083j37Tg0041j35Tg00cLj3JTg00d0j1ITg00EYj2BTg00BXj2HTg00CXj2KTg00dNj2ATg00@Uj8GTg00dhj8FTg00efj6NTg00fDlGPTf0R1#1#1p=0%21#1p=6%21#2p==g00VaR2g00gLg00hGg00iDg00j=g00k7g00l0P1f1R3f2R4f3R5f4R6f5R7f6R8g00lmR9f7R:f8R;f9R<f:R=f;R>f<R?f=R@f>RAMGPp=Og00=XRB#1RC#1RD#1RE#1#0#>RF#4RGg00[iRHg00n7g00neg00<_%2CRI#>/RGRJ%>E#4#M\GREg00WY13F4RK'@%;C%6I#;'E,@K'DRKp,3AMBRIp,2spRCp,4argvRLp,4envpRMP5P4P3FTg00oaRNg0113ROP5%1B#=#=#0#0#2#6#6#0#;RPg00UFRQ1SFPd5CFPGeP4%QNRRD?RS%LNRTP=P<PCP;PIPLPMP:P8D<E8,:6'9;77[[]4]6^7GPIPCPLPMp,3Hvap,3Hvep,4Hvspg011kRU%41RV%43RWP0%44?5311354135355HR0[1343134155H%45?543[RX%46?554\0AJ431P1n2001000000120000000W3W2W5R0PX^3W^2V^5URUP1PF%I9,BF%2B#=#6#6#0,H2%=D#0#0#2#0#0#2#0#;'KRD13FD,AHO4b0P8P7P6P5P4P3P2PIPCPLPMP5P4P3GGP7P6P5P4P3PIPCPLPMP6P5P4P1GFO5PTP>P=PCP<PIPLPMP;P:D<E8,:6,9S=7N8P0PUP1PF1BFPRUACFPQRQ1AHP13FU13FQ55HdO4b0A5GUQPGPQPOP8P1P7PRD?PTPAP@PCP?PIPLPMP>P=D<E8,::'9=7N<X<GP3PUP1ENPOP7PUP6PRD?PTP@P?PCP>PIPLPMP=P<D<E8,:8'9=7N;P1b1b0b1W;X9KX4EX6JX7GM?OW8W:WAW>W?X@GW=o"). Qed.

End Assembly.

(* [comment removed for export] *)
Theorem ref_startup : forall sp brk mbase draw lim inp K,
  valid_sp sp -> valid_argv (in_argv inp) -> valid_envp (in_envp inp) ->
  (forall tid regs mem,
     (0 < bv_unsigned tid < 2^22)%Z ->
     @main_entry (amb_of inp draw) sp (in_argv inp) (in_envp inp) tid regs mem ->
     realizes rsegs (mkCfg (mkst (fx:=fx0) regs (0x17868 : word) mem (seg_rom rsegs))
                           (with_tid tid (init_model (segments_reserved rsegs) brk mbase sp lim inp))) K) ->
  realizes rsegs (init_config rsegs rpc rph sp brk mbase draw lim inp) K.
Proof.
ltac2:(KReplay.run1 (kr_t_V2Startup ()) [] "h02HKh13Hsph23Hvah33Hveh41Kh53brkh64drawh73inph83limh95mbaseh:3memh;4regsh<2sph=3tidp;1p;2p;7p;3p;5p;6p;>g000Pj11Tg0015j14Tg001Sj17Tg012Ij1NTg013>j13Tg0144j1DTg014kj15Tg015aj1>Tg00?Dj10Tg00?ij2<Tg0026j1;Tg00DRj2:Tg00\Gj29Tg00F?j16Tg00\cj2MTg00QWj2LTg016Xj28Tg00AZj7KTg00]@j2CTg00SJj3BTg00]cj1ATg00^_j5@Tg00_Xj1?Tg00a\j6ETg00bUj2FTg007>j2GTg0083j3HTg017Xj1=Tg018Lj1ITg019Cl>JTf0R0#1#1p=2g00=XR1#1R2#2R3#1#2#4R4#7R5g01:Dg00[ig01;Dg00<_f6R6#Nf2R7#3#Df3R8#5#>%02R9#4/<5%43#7#;\5g00WY1:47R3'9%62%09#1#6'M,93'Lf8R3f:R9'8f=R2%33%53P8P7f1R:FKg00oaR;g0113P8%11#0#0#0#0#2#2#0#0#1#0#1#2#6R1g00UF1C41d5B4P5eP7%A;D@f4R4%?;P2f<f>P9f9R2EE'F'G;H3[[]:];^=5f5R;f7'8P9%3;%5;P7P:P8P2P3P6%=;%I;P4P0M>JW0W3W2W1W4W7W8W6X95X55W<o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Consumers.
  Context {AMB : Amb}.
  Variable sp0 : word.
  Variables av ev : list (list byte).
  Variable tid : word.
  Variable regs : bvmap 5 word.
  Variable mem : word -> option byte.
  Hypothesis ME : main_entry sp0 av ev tid regs mem.

  (* [comment removed for export] *)
  Lemma main_entry_rdn_above : forall segs (a : word) n,
    (bv_unsigned sp0 <= bv_unsigned a)%Z ->
    (bv_unsigned a + Z.of_nat n <= 2^64)%Z ->
    rdn segs mem a n = rdn segs (wrap_mem RPH sp0 av ev a_uid a_hwcap a_draw) a n.
Proof.
ltac2:(KReplay.run1 (kr_t_V2Startup ()) ["Consumers"] "p'0h01Hh13s1vh21Jh32MEh42HJh52Hah62Hnh72_Hh81ah91eh:3memh;1nh<4segsi001xp;1p;2p;8p;5p;3p;7p;6p;4p;9g0000j19Tg000Pj14Tg0015j1<Tg001Sj1:Tg00DRj27Tg00Y7j2?Tg00HSj1ETg00F]j2CTg00F?j1;Tg00\cj2ATg01<>j8@Tg0026j18Tg00Igj25Tg01=6j56Tg0041j30Tg00K^j1JTg00L]j1ITg00M^j1HTg00N^j7GTg01=nj6DTg00P^j43Tg00QWR0j22Tg00R2R1j2=Tg01>jj41Tg00AZj7>Tg01?bl9BTg00efj7FTg00:j#9g00=X#4R2#4#4R3#4#4#4R4#<R5#:R6g01@ep,3sp0R7,75f1R8,75'?f2R9,75%E8'C%;2%;4'A'?p,3AMBR4P7p,2avR2p,2evR5p,3tidR:p,4regsR;p,3memR<p,2MER=G@%<3#:R3#8\6R>1578P4P7P2P5f0R?D6R@90>8P7g01ADP7P2P5%J4%I4RA%H4RBFGRCP8P7P2P5PAPBP:EDRBC390><'2'2X16,=6RAX2>RD'=P1P>PD%93#8R3f6RDP<f5REf4RFC1PDPCPEPFC130P?P1P61579A0>9@P7PCP9PBC390><'2'2X16f:R9P<f9R1f8RDC1P9PCP1PDC1503P?157FA0>F@P7PCPFPBC390><'2'2P0157EP4P7P2P5P8D690>EP7PCPEPBC390><'2f>R@P<f=R9f<RGC1P@PCP9PGC1503P?f7RH,57P4P7P2P5PFD690>DP7PCPDPBC390><'2P0P4P7P2P5PED690>1P7PCP1PBC390><fBR1P<fAREf@R0C1P1PCPEP0C1503P?f;P4P7P2P5PHD650>P7PCPGPBC390><P>P7PCP9PBC3R9P4P7P2P5P:P;P?F>fGRGP8fFRHfER0C1PGPCPHP0C1503]3X:>P4P7P2P5P:P;P9F>P7PCPHP@PBP0fDfCP1M9BW3P<P?P=FFW0W7P8P?O2n2001000000121000000W0W4P8P?O2n2001000000121000000W0X16P8P?O2n2001000000121100000X0AX2>P8P?O2n2001000000121100000b9W6W5W;W8W<o"). Qed.

  Lemma main_entry_mem_above : forall (a : word),
    (bv_unsigned sp0 <= bv_unsigned a)%Z -> mem a = wrap_mem RPH sp0 av ev a_uid a_hwcap a_draw a.
Proof.
ltac2:(KReplay.run1 (kr_t_V2Startup ()) ["Consumers"] "p'0h01Hh13s1vh21Jh32MEh42HJh52Hah62_Hh71ah81eh93memi001xp;1p;2p;8p;5p;3p;7p;6p;4g000Pj13Tg0015j1;Tg001Sj18Tg00DRj27Tg00Y7j2ETg01<>j8@Tg0026j1?Tg00Igj25Tg01=6j54Tg0041j30Tg00K^j1>Tg00L]j1=Tg00M^j1<Tg00N^j7Dj86Tg01=nj6CTg00P^j41Tg00QWR0j22Tg00R2R1j29Tg00AZj7:Tg01BLj6ATg00efj7BTg00=X#3#3#3R2#3#3#3#;R3#8R4p,3sp0R5,73f0R6,73'Ep,3AMBR3P5p,2avR7p,2evR8p,3tidR9p,4regsR:p,3memR;p,2MER<G@%;2#8#?R2\4R=f1R>,55P3P5P7P8P6D4R?90=>P5g01ADR@P5P7P8%>3RA%=3RB%<3RCFDRDP>P5P7P8PBPCP9ECREC190=;'2'2X14,94RFX2=RG'9P1P=PGP;f3RGO1P@P5P7P8PAPBPCPGG6502P6P1P4f2R1,55A0=1?P5PDP1PEC190=;'2'2X14P;f7R1O1P@P5P7P8PAPBPCP1G6502P6f4RG,55A0=G?P5PDPGPEC190=;'2'2P0f5R?,55P3P5P7P8P>D490=?P5PDP?PEC190=;'2P;f;RHO1P@P5P7P8PAPBPCPHG6502P61551f8RIP3P5P7P8PGD450=P5PDPIPEC190=;'2P0f9R0P3P5P7P8P?D450=P5PDP0PEC190=;P;f?R0O1P@P5P7P8PAPBPCP0G6502P6P3P5P7P8P1D490=HP5PDf<PEC190=;P=P5PDf=PEC1RHP3P5P7P8P9P:P6F:P>fDR1O1P@P5P7P8PAPBPCP1G6502]3X9=P3P5P7P8P9P:PHF:P5PDf>PEfCfBEAW3P;P6P<FBW0W6P>P6O2n2001000000121000000W0W4P>P6O2n2001000000121000000W0X14P>P6O2n2001000000121100000X0FX2=P>P6O2n2001000000121100000b8W5W7o"). Qed.

  (* [comment removed for export] *)
  Lemma main_entry_win_mapped : forall (a : word),
    (bv_unsigned sp0 - stack_max_size <= bv_unsigned a < bv_unsigned sp0)%Z -> mem a <> None.
Proof.
ltac2:(KReplay.run1 (kr_t_V2Startup ()) ["Consumers"] "p'0h01Hh13s1vh21Jh32MEh44__x1h54__x2h64__x3h72HJh82Hah92_Hh:7__arithh;4__ffh<8__varmaph=5__with>1ah?1eh@3memhA1oi001xp;1p;2p;8p;5p;3p;7p;6p;4g000Pj13Tg0015j1CTg001Sj1>Tg00DRj2:Tg00E<j2;Tg00Y7j29Tg00\Gj28Tg00QWR0j21Tg01<>j8LTg0026j1GTg00Igj25Tg01=6j56Tg0041j30Tg00K^j1^Tg00L]j1VTg00M^j1UTg00N^j7RTg01=nj6QTg00P^j42j5[Tg00R2R1j2@Tg003Oj1ATg01CNj14Tg00AZj7?Tg005cj1NTg0000j1MTg01Cgj2=Tg01DEj4KTg01Dcj1ITg01EAj1HTg01Elj27Tg01FOj3JTg00?Dj1FTg01G2j4<Tg01G]j7ETg01HAj8OTg01Hej2PTg00dNj2DTg01IGj2STg01J3j3TTg01JRj4]Tg01KDj2\Tg01L?j6WTg00efj6Xj7YTg01M?j7ZTf1R2g01McR3g01NBR4P4g01NbR5f0R6g01OBFZp=Bg00=XR7#3R8#3#3R9#3#3#3#CR:#>R;p,3sp0R<,::R=g01ObR>';1::6R?'918?='1p,3AMBR?P<p,2avR@p,2evRAp,3tidRBp,4regsRCp,3memRDp,2MEREGL%C9#>R9#GRF\;RG15<2P?P<P@PAP6D6RH90G2P<g01ADP<P@PA%^?%V?RI%U?RJFRRKP2P<P@PAPIPJPBEQRJC290GD'1'1X1;,@;RIX2GRL'@P1PGPLPDf3RLO1%A9R950F#4P6P1P;f2R1,5<A0G1HP<PKP1PJC290GD'1'1X1;PDf7RMO1=0F9#4P6f4RN,5<A0GNHP<PKPNPJC290GD'1'1P0f5RH,5<P?P<P@PAP2D690GHP<PKPHPJC290GD'1PDf;ROO1=0F9#4P615<Mf8RPP?P<P@PAPND650GP<PKPPPJC290GD'1P0f9R0P?P<P@PAPHD650GP<PKP0PJC290GDPDf?O1=0F9#4P6P?P<P@PAPMD690GOP<PKf<PJC290GDPGP<PKf=PJC2ROP?P<P@PAPBPCP6F?P2fDRMO1=0F9#4]3X@GP?P<P@PAPBPCPOF?PFf>ROfCRCO1A0F69#4XAFf6PCg00[iRFg01P_R9#N%M9PF1=F1P21=FLCK%IF%HFR9P3P4P4P5P9P3P4P4P5PF17F7R317F85JFg01QK%F7,7FR7C<,B9PFP7g01R2P3C<,B9FER3%A4P3GO1P95P6P1g01RYR9g01S9R5'D1S61=095dg00WY=TF2C]b;b<b=X4FX5FW61;62/911816'11;21/9L18L2'1[^4F^5F^6FP61::MP>P=PCO4b:1\<CeR=O2P<PKPOPJPCD[P<PKPOPJPCP=EWEXW3PDP6PEFYW0W9P2P6O2n2001000000121000000W0W7P2P6O2n2001000000121000000W0X1;P2P6O2n2001000000121100000X0IX2GP2P6O2n2001000000121100000b?W8W>o"). Qed.

  Lemma main_entry_store_ok_win : forall segs (a : word) n,
    (bv_unsigned sp0 - stack_max_size <= bv_unsigned a)%Z ->
    (bv_unsigned a + Z.of_nat n <= bv_unsigned sp0)%Z ->
    store_ok segs mem a n = true.
Proof.
ltac2:(KReplay.run1 (kr_t_V2Startup ()) ["Consumers"] "p'0h01Hh14__x1h24__x2h34__x3h43s1vh51Jh62MEh77__arithh84__ffh98__varmaph:5__with;4cstrh<2HJh=3Hhih>3Hloh?2_Hh@1ahA1ehB3memhC1nhD4segsi001xp;1p;2p;8p;5p;3p;7p;6p;4p;:g0000j1FTg000Pj15Tg0015j1ATg001Sj1@Tg00DRj29Tg00E<j2=Tg00Y7j23Tg00HSj1<Tg00F]j2:Tg01<>j8OTg0026j1JTg00Igj27Tg01=6j56Tg0041j30Tg00K^j1]Tg00L]j1VTg00M^j1UTg00N^j7TTg01=nj6RTg00P^j42Tg00QWR0j21Tg00R2R1j2CTg01SYj48Tg00AZj7BTg01TYj1QTg005cj1PTg01Cgj2?Tg01DEj4NTg01Dcj1LTg01EAj1KTg01Elj2;Tg01FOj3ITg00?Dj1MTg01G2j4>Tg003Oj1HTg01Hej2GTg00dNj2STg01IGj2`Tg01J3j3_Tg01JRj4^Tg01U>j1\Tg01V9j3WTg01V\l:XTg00efj7YTg01M?j7ZTg01HAj8[Tg01RYR2f0R3g01S9R430p=4f1R5g01McR6g01NBR7P7g01NbR8P3g01OBFZp=Ef3R9P6P7P7P8f2R6P5P3G[p=Dg00:j#Fg00=XR:#5R;#5#5R<#5#5#5#AR=#@R>g01@ep,3sp0R?,9=R@g01ObRA'=19=5'319=6%<5':/3@p,3AMBRBP?p,2avRCp,2evRDp,3tidREp,4regsRFp,3memRGp,2MERHGO%A<#@#J\>R<17?5PBP?PCPDP3D6RI90<5P?g01ADP?PCPD%]B%VBRJ%UBRKFTRLP5P?PCPDPJPKPEERRKC290<G'1'1X4>,C>RJX5<RM'CP1P<PMf6RMPGf5RNf4ROC8#4P3P1P>17?6A0<6IP?PLP6PKC290<G'1'1X4>f:PGf9R1f8RPC8#4P317?OA0<OIP?PLPOPKC290<G'1'1P017?NPBP?PCPDP5D690<NP?PLPNPKC290<G'1f>RIPGf=RQf<RRC8#4P3f7RS,7?PBP?PCPDPOD690<PP?PLPPPKC290<G'1P0PBP?PCPDPND690<1P?PLP1PKC290<GfBPGfAf@C8#4P3f;PBP?PCPDPSD650<P?PLPRPKC290<GP<P?PLPQPKC2RQPBP?PCPDPEPFP3FBfGRRP5fFRSfER1C8#4]6XB<PBP?PCPDPEPFPQFBP?PLPSPIPKP1fDRKPM%QKRMg00WYRI%<K'3RLg00[iRQg01P_RF#PRE%FFRFPQ1?Q6P51?Q9CNRD%LQRC%KQRBPQ1;Q:RN1;Q;R;5IQg01QKR0%M:,;QR:C>,EBRP%H7R7PPCD1GB8R8P3P61S241`36#4dA_QI5C^RIb8b9b:X1QX2QW31=35/361=56/39[^1Q^2Q^3QP319=RRRPAP@P1O4b7b;%\?19=1'3ePMPLPEPFPDPCPBPQAWQN;P0P:C>,EBRBP7PBCDP8PIb8b9b:X1QX2QX3Q1:35/361:56/39[^1Q^2Q^3QP3P@%<SPRPKO4b7b;M:XW6PGP3PHFYW0W?P5P3O2n2001000000121000000W0W<P5P3O2n2001000000121000000W0X4>P5P3O2n2001000000121100000X0JX5<P5P3O2n2001000000121100000bAW=W>WCW@WDo"). Qed.

  (* [comment removed for export] *)
  Lemma main_entry_mem_data : forall (a : word),
    (bv_unsigned a < bv_unsigned sp0 - stack_max_size)%Z ->
    mem a = D_main sp0 av ev a_hwcap a_draw tid a.
Proof.
ltac2:(KReplay.run1 (kr_t_V2Startup ()) ["Consumers"] "p'0h01Hh13s1vh21Jh32MEh42HJh52Hah62_Hh71ah81eh93memi001xp;1p;2p;8p;5p;3p;7p;6p;4g000Pj13Tg0015j1<Tg001Sj18Tg00DRj27Tg00E<j2GTg00\Gj29Tg01<>j8ATg0026j1@Tg00Igj25Tg01=6j54Tg0041j30Tg00K^j1>Tg00L]j1=Tg00M^j1FTg00N^j7ETg01=nj6Dj76Tg00P^j41Tg00QWR0j22Tg00R2R1j2:Tg00AZj7;Tg01U>j1BTg01Wbj6?Tg00efj7CTg00=X#3#3#3R2#3#3#3#<R3#8R4f0R5,73p,3sp0R6,73g01Ob'G'9p,3AMBR7P6p,2avR8p,2evR9p,3tidR:p,4regsR;p,3memR<p,2MER=GA%<2#8#@R2\4R>f1R?,56P7P6P8P9P5D4R@90>?P6g01ADP6P8P9%>7%=7RA%F7RBFERCP?P6P8P9PAPBP:EDRDC190><'2'2X14,:4REX2>RF':P1P>PFP<f3RFO1P6P8P9PAPBP:PFF6502P5P1P4f2R1,56A0>1@P6PCP1PDC190><'2'2X14P<f7R1O1P6P8P9PAPBP:P1F6502P5f4RF,56A0>F@P6PCPFPDC190><'2'2P0f5R@,56P7P6P8P9P?D490>@P6PCP@PDC190><'2P<f;RGO1P6P8P9PAPBP:PGF6502P51561f8RHP7P6P8P9PFD450>P6PCPHPDC190><'2P0f9R0P7P6P8P9P@D450>P6PCP0PDC190><P<f?R0O1P6P8P9PAPBP:P0F6502P5P7P6P8P9P1D490>GP6PCf<PDC190><P>P6PCf=PDC1RGP7P6P8P9P:P;P5F;P?fDR1O1P6P8P9PAPBP:P1F6502]3X9>P7P6P8P9P:P;PGF;P6PCf>PDfCRDfB173D%B6'9eE?W3P<P5P=FCW0W6P?P5O2n2001000000121000000W0W4P?P5O2n2001000000121000000W0X14P?P5O2n2001000000121100000X0EX2>P?P5O2n2001000000121100000b8W5W7o"). Qed.

  Lemma main_entry_rdn_data : forall segs (a : word) n,
    (bv_unsigned a + Z.of_nat n <= bv_unsigned sp0 - stack_max_size)%Z ->
    rdn segs mem a n = rdn segs (D_main sp0 av ev a_hwcap a_draw tid) a n.
Proof.
ltac2:(KReplay.run1 (kr_t_V2Startup ()) ["Consumers"] "p'0h01Hh13s1vh21Jh32MEh42HJh52Hah62_Hh71ah81eh93memh:1nh;4segsi001xp;1p;2p;8p;5p;3p;7p;6p;4g0000j1@Tg000Pj14Tg0015j1:Tg001Sj19Tg00DRj27Tg00HSj1?Tg00F]j2<Tg00E<j2DTg00Y7j2=Tg01<>j8ATg0026j18Tg00Igj25Tg01=6j56Tg0041j30Tg00K^j1JTg00L]j1ITg00M^j1HTg00N^j7GTg01=nj6ETg00P^j42Tg00QWR0j23Tg00R2R1j2;Tg01>jj41Tg00AZj7>Tg01U>j1CTg01Xcj8BTg00efj7FTg00:j#@g00=X#4#4#4R2#4#4#4#:R3#9R4g01@ef1R5,73f0R6#?'<p,3sp0R7,73g01Ob'D'=p,3AMBR8P7p,2avR9p,2evR:p,3tidR;p,4regsR<p,3memR=p,2MER>GA%:2#9R2#8\4R?1575P8P7P9P:P6D6R@90?5P7g01ADP7P9P:%J8%I8RA%H8RBFGRCP5P7P9P:PAPBP;EERBC290?='3'3X14,;4RAX2?RD';P1P?PD%@2#8R2f5RDP=f4REf3RFC1PDPBPEPFC130P6P1P4f2R1,57A0?1@P7PCP1PBC290?='3'3X14f9R1P=f8RFf7RGC1P1PBPFPGC1502P6157EA0?E@P7PCPEPBC290?='3'3P0157DP8P7P9P:P5D690?DP7PCPDPBC290?='3f=R@P=f<RHf;RIC1P@PBPHPIC1502P6157GP8P7P9P:PED690?FP7PCPFPBC290?='3P0P8P7P9P:PDD690?1P7PCP1PBC290?=fAR1P=f@RDf?R0C1P1PBPDP0C1502P6P8P7P9P:PGD690?IP7PCPHPBC290?=P?P7PCP@PBC2R@P8P7P9P:P;P<P6F>fFRHP5fERIfDRGC1PHPBPIPGC1502]3X9?P8P7P9P:P;P<P@F>P7PCPIf>PBPGfCRBfB173G%?B'<%C7'=eGBW3P=P6P>FFW0W6P5P6O2n2001000000121000000W0W4P5P6O2n2001000000121000000W0X14P5P6O2n2001000000121100000X0AX2?P5P6O2n2001000000121100000b8W5W:W7W;o"). Qed.
End Consumers.
