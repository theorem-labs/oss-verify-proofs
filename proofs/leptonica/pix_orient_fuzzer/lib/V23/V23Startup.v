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
From OssFuzzTheorems.leptonica.pix_orient_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.CliDriver Require Import Amb.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import ShapeAlg PureModel RefNodesMF StartupTac ArgvEnv RefLayout.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Reloc Require Import Reloc.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Musl Require StartupBase StartupDefs Startup.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23StartupDefs V23Reloc V23RelocCode V23RelocSites V23RelocImg V23RelocMusl V23RelocStart.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_V23Startup () := "I47Corelib4Init9Datatypes4list00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C4ELinuxProcessSemantics?LinuxProcessSem5State8m_haltedK47Corelib4Init9Datatypes6option02I47Corelib4Init5Logic2eq00I47Corelib4Init9Datatypes4prod00C4ELinuxProcessSemantics?LinuxProcessSem5State9m_vm_lazyK47Corelib4Init9Datatypes4list01I5ARocqVerifyHarness?AgentSubmission6Common6CatSim6msteps00K4ELinuxProcessSemantics?LinuxProcessSem3Run6config01I5ARocqVerifyHarness?AgentSubmission6Common8ShapeAlg8realizes00C5ARocqVerifyHarness?AgentSubmission6Common8ShapeAlg9rz_mstepsC5ARocqVerifyHarness?AgentSubmission6Common:StartupTac3bwdI4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00C5ARocqVerifyHarness?AgentSubmission6Common8ShapeAlg4TSetK47Corelib7Numbers7BinNums8positive03I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00K47Corelib7Numbers7BinNums8positive01C4ELinuxProcessSemantics5Riscv7Prelude5bvmapI6ARocqVerifyHarness?AgentSubmission6Common4Musl7Startup:main_entry00i5ARocqVerifyHarness?AgentSubmission3V23:V23Startup:main_entry00C6ARocqVerifyHarness?AgentSubmission6Common5Reloc5Reloc8rl_deltaC6ARocqVerifyHarness?AgentSubmission6Common5Reloc5Reloc2rlC45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z3subC45stdpp9bitvector;definitions7Z_to_bvK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3addC5ARocqVerifyHarness?AgentSubmission6Common7ArgvEnv5argcNC47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3mulC46Stdlib5Lists4List2InC5ARocqVerifyHarness?AgentSubmission6Common8MemSplit3wfJC6ARocqVerifyHarness?AgentSubmission6Common4Musl7Startup6J_mainC6ARocqVerifyHarness?AgentSubmission6Common9CliDriver3Amb5a_uidC6ARocqVerifyHarness?AgentSubmission6Common9CliDriver3Amb7a_hwcapC6ARocqVerifyHarness?AgentSubmission6Common9CliDriver3Amb6a_drawC5ARocqVerifyHarness?AgentSubmission6Common8PropExec8wrap_memC6ARocqVerifyHarness?AgentSubmission6Common4Musl;StartupDefs6D_mainC5ARocqVerifyHarness?AgentSubmission6Common8MemSplit4cmemI47Corelib4Init5Logic3and00I47Corelib4Init5Logic2ex00k5ARocqVerifyHarness?AgentSubmission3V23:V23Startup:main_entry01K45stdpp9bitvector;definitions2bv01C5ARocqVerifyHarness?AgentSubmission6Common8PropExec4getrK47Corelib4Init9Datatypes4list02K47Corelib4Init5Logic4True01I6ARocqVerifyHarness?AgentSubmission6Common9CliDriver3Amb3Amb00C5ARocqVerifyHarness?AgentSubmission3V238V23Reloc9v23_relocK47Corelib7Numbers7BinNums1Z01C6ARocqVerifyHarness?AgentSubmission6Common4Musl:RelocStart4RPH0C56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z6moduloC4ELinuxProcessSemantics?LinuxProcessSem5State<sp_window_loC4ELinuxProcessSemantics?LinuxProcessSem5State<sp_window_hiI47Corelib7Numbers7BinNums1Z00C56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z3powC45stdpp9bitvector;definitions4BvWfC5ARocqVerifyHarness?AgentSubmission6Common8PropExec7seg_romC5ARocqVerifyHarness?AgentSubmission6Common8PropExec4mkstC4ELinuxProcessSemantics?LinuxProcessSem3RunAsegments_reservedC6ARocqVerifyHarness?AgentSubmission6Common9CliDriver3Amb<mkProcInputCC4ELinuxProcessSemantics?LinuxProcessSem5State:init_modelC4ELinuxProcessSemantics?LinuxProcessSem5State8with_tidC45stdpp9bitvector;definitions5bv_eqC56Stdlib6ZArith6BinInt1Z4of_NK47Corelib4Init5Logic2eq01c5ARocqVerifyHarness?AgentSubmission3V23:V23Startup<main_entry_LC47Corelib4Init5Logic8eq_ind_rC6ARocqVerifyHarness?AgentSubmission6Common4Musl7Startup?ref_startup_secC5ARocqVerifyHarness?AgentSubmission3V23<V23RelocCode8v23_codeC5ARocqVerifyHarness?AgentSubmission3V23=V23RelocSites9v23_sitesC5ARocqVerifyHarness?AgentSubmission3V23;V23RelocImg7v23_imgC5ARocqVerifyHarness?AgentSubmission3V23;V23RelocImg8v23_dataC5ARocqVerifyHarness?AgentSubmission3V23<V23RelocMusl6v23_rwC5ARocqVerifyHarness?AgentSubmission3V23=V23RelocStart9v23_startC5ARocqVerifyHarness@ProcessOversightKTgt_pix_orient_fuzzer_ubsan1M7init_pc____________________C4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsI4ELinuxProcessSemantics?LinuxProcessSem5State;InputStream00C5ARocqVerifyHarness@ProcessOversightKTgt_pix_orient_fuzzer_ubsan1M?loaded_segments____________________C5ARocqVerifyHarness?AgentSubmission6Common8PropExec3fx0I47Corelib7Numbers7BinNums1N00C4ELinuxProcessSemantics?LinuxProcessSem3Run8valid_spC4ELinuxProcessSemantics?LinuxProcessSem5State7in_argvC4ELinuxProcessSemantics?LinuxProcessSem3Run:valid_argvC4ELinuxProcessSemantics?LinuxProcessSem5State7in_envpC4ELinuxProcessSemantics?LinuxProcessSem3Run:valid_envpC6ARocqVerifyHarness?AgentSubmission6Common9CliDriver3Amb6amb_ofC4ELinuxProcessSemantics?LinuxProcessSem5State5in_fsC4ELinuxProcessSemantics?LinuxProcessSem5State8in_stdinc5ARocqVerifyHarness?AgentSubmission3V23:V23Startup?ref_startup_secI4ELinuxProcessSemantics?LinuxProcessSem;StackLayout9EntryDraw00I4ELinuxProcessSemantics?LinuxProcessSem5State9ProcInput00c5ARocqVerifyHarness?AgentSubmission3V23:V23Startup6me_memc5ARocqVerifyHarness?AgentSubmission3V23:V23Startup6J_mainC5ARocqVerifyHarness?AgentSubmission3V23>V23StartupDefs6D_mainC5ARocqVerifyHarness?AgentSubmission6Common8PropExec3rdnC5ARocqVerifyHarness?AgentSubmission6Common8MemSplit>rdn_cmem_aboveI47Corelib4Init9Datatypes3nat00C5ARocqVerifyHarness@ProcessOversightKTgt_pix_orient_fuzzer_ubsan1M5phdrs____________________C5ARocqVerifyHarness?AgentSubmission6Common8MemSplit=cmem_at_aboveC47Corelib4Init5Logic3notK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC5ARocqVerifyHarness?AgentSubmission6Common8MemSplit6in_winC5ARocqVerifyHarness?AgentSubmission6Common8MemSplit;cmem_at_winK46Stdlib9micromega5Tauto8GFormula04C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01C4ELinuxProcessSemantics?LinuxProcessSem5State>stack_max_sizeI46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC5ARocqVerifyHarness?AgentSubmission6Common8MemSplit6win_loK46Stdlib9micromega7EnvRing5PExpr03C5ARocqVerifyHarness?AgentSubmission6Common8MemSplitAstore_ok_cmem_winC5ARocqVerifyHarness?AgentSubmission6Common8MemSplit<cmem_at_dataC5ARocqVerifyHarness?AgentSubmission6Common8MemSplit=rdn_cmem_data".
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
ltac2:(KReplay.run1 (kr_t_V23Startup ()) ["VP1"] "h02sth12Hhh25Hlazyh33Hmsh44Hst'h51Kh65modelh74segsh83st'p;1p;3p;2p;9g0000j11Tg000Pj10Tg0015j1:Tg001Sj15Tg0026j1?Tg002Xj1<Tg003Oj1;Tg0041j32Tg004Kj29Tg004kj16Tg005cj17Tg006Cj38Tg007>j23Tg0083j34Tg0092l9>Tg00:0j2=Tg00:j#1g00;ig00<_g00=X#0#0#0#0#0#0#:#5R0#?f1R1#<%;0321900R0#1f2R2#6%7032g00>=R0f6R3f0R4781f7R51313f5R634f8f3R7P2P5P3P6f4R3P1P4M9>W4W3X80W01343=467X00,=3eW2W1W5W6W7o"). Qed.
End VP1.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition J_main {AMB : Amb} (sp0 : word) (av ev : list (list byte)) (s1v : word) : word -> option byte :=
  let J6 := J_tls sp0 (J_aux sp0 av ev a_uid a_hwcap (J_lsm sp0 av (fun _ => Some (Z_to_bv 8 0))))
              (Z_to_bv 64 0x10dd14) (pn_w sp0 av ev) s1v (Z_to_bv 64 0x158460)
              (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) in
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes J6
    (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 0x10dd1c)))   (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0)))           (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0)))          (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0)))          (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0)))          (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0)))          (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 (Z_to_bv 64 0x10df10)))    (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (argv_w sp0)))             (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 72)) (word_to_le_bytes 8 (argc_w av)))              (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 88)) (word_to_le_bytes 8 (Z_to_bv 64 0x10de60)))    (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 96)) (word_to_le_bytes 8 (Z_to_bv 64 0x123698)).    (* [comment removed for export] *)

(* [comment removed for export] *)
Record main_entry {AMB : Amb} (sp0 : word) (av ev : list (list byte)) (tid : word)
       (regs : bvmap 5 word) (mem : word -> option byte) : Prop := {
  me_ra  : getr regs 1 = Z_to_bv 64 0x10df20;
  me_sp  : getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 48);
  me_gp  : getr regs 3 = Z_to_bv 64 0x10800;
  me_tp  : getr regs 4 = Z_to_bv 64 0x1381d0;
  me_s0  : getr regs 8 = Z_to_bv 64 (bv_unsigned sp0 + 8);
  me_s1  : getr regs 9 = argcN av;
  me_a0  : getr regs 10 = argcN av;
  me_a1  : getr regs 11 = Z_to_bv 64 (bv_unsigned sp0 + 8);
  me_a2  : getr regs 12 = Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av));
  me_s2  : getr regs 18 = Z_to_bv 64 0x63140;
  me_s3  : getr regs 19 = Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av));
  me_szero : forall r : reg, In r [20; 21; 22; 23; 24; 25; 26; 27]%list -> getr regs r = Z_to_bv 64 0;
  me_mem : exists (J : word -> option byte) (s1v : word),
             wfJ sp0 J /\ J = J_main sp0 av ev s1v
             /\ mem = cmem sp0 (wrap_mem RPH sp0 av ev a_uid a_hwcap a_draw) J (D_main sp0 av ev a_hwcap a_draw tid)
}.

(* [comment removed for export] *)
Lemma main_entry_L : forall {AMB : Amb} sp0 av ev tid regs mem,
  @Startup.main_entry v23_reloc AMB sp0 av ev tid regs mem -> main_entry sp0 av ev tid regs mem.
Proof.
ltac2:(KReplay.run1 (kr_t_V23Startup ()) [] "p'0h03AMBh11Hh21Jh32avh42evh52f1h63f10h73f11h83f12h93f13h:2f2h;2f3h<2f4h=2f5h>2f6h?2f7h@2f8hA2f9hB3memhC1rhD4regshE3s1vhF3sp0hG3tidi005me_a0i015me_a1i025me_a2i035me_gpi046me_memi055me_rai065me_s0i075me_s1i085me_s2i095me_s3i0:5me_spi0;8me_szeroi0<5me_tpp;1p;2p;8p;7p;3p;6p;4p;Dg000Pj10Tg0015j1ATg001Sj1>Tg0000j1KTg00?Dj11Tg00?ij2ZTg0026j1XTg00@UR0j8WTg00AZj7VTg00BZj2?Tg00CZj2BTg00DTj2;Tg00E>j2[Tg00E[j28Tg00FAj14Tg00F_j2:Tg00G<j1DTg00H5j2CTg00HUj1FTg00I5j2GTg005cj1UTg00IRj3TTg00Iij2OTg00Jaj6NTg0041j3=Tg00K`j1MTg00L_j1PTg00M`j1QTg00N`j7LTg00O]j7RTg00P`j4STg00QYj2JTg00R4j2ITg00RNlD]Tg00SNj3@Tg00T1j2HTg00Tjj3\Tf0R1#0#0p=2%11#1p=7%11#0p=9%01#1p=<%01#4p=6f4R2f3R3f2R4f1R5#4g00UJR63@'H;=1p=3A@516p=Y1H45==31p=EA@456=\31p=5g00Ufg00=XR6#0R7#0R8#0R9#0R:#2#AR;#>R<%A9#>R=#KR>#KR?%17R@#ARA/Z<%X=\<R=g00VeRBf6RCf5RDP2P3P4P5P1GWP0PBf7R0PCPDP2P3P4P5f8REP0PCPDP2P3P4FVP1P<f?PAP6%16R6#1#7RF#1#7#2,?B%0@RG#1RH#0#9#<#2#<#9#6'BD3P<f@PAP7fDR7,;;%06RI#0RJ#0RK#6'[,8;D3P<fAPAP6%1:#2#2#2#2#2#6,8;D3P<fBPAP8%18R8#1R6#9#9#<#<,?B%1@R@#1RL#9#7#7#<#7#2#6'BD3P<fC%49R9,YAfGRM,;;/:9,8;CEP<P7PAP8%DMD3P<fEPAPGfHR7#DD3P<fFPAP@fJRN,;;/:9,8;D3P<PMPAPJfKRM,;;%4:R:':1C>N#F,G9':,8;D3P<P7PA%08%0F#7#2,?B%06#2#7#9#9#2#6'BD3P<fIPAP6fMR6,;;/::fLR:,C>#F,G9':,8;D3%>AR9P9PA%6GP9PA%4HP9PA%6@P9PA%4LP9PA%4KP9PA%1J#4P9PA%1IRI#6P9PA%1I#4%U9C5C5C5C5C5C5C5C59T91P<P:P5g00W`,8;CE[]CfQR;/O5PBfRR9P;fPRIfORAP1EN9==5P;g00X>P;PIPA%M9%P9RJ%Q9R9FLP5PBP;PIPAPJP9fNR9FRCS9==:'J'JXE<,I<X2=,I=P;PIPAP9P6P:PMf<RMf;R:f:R6f9R9PEP0PCPDP2P3P4P5P1MD]W9W8W7W6WAW@W?W>W=W<W;W:W5PMP:P6P9PEP0PCPDP2P3P4P5P1O=n80000000010000001=110510:10310<10610710010110210810910;104W1WBWDXG<X4?W3WFW0o"). Qed.

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
ltac2:(KReplay.run1 (kr_t_V23Startup ()) ["Assembly"] "h01Hh12_Hh21vp;1p;2p;3g0015j1:Tg00DTj28Tg00Y>j24Tg00FAj17Tg00YZj2;Tg0041j39Tg00QYR0j25Tg00?Dj13Tg000Pj12Tf0R1#2#2#2#2p=0%21#2p=6%31#3p=1p,4Hvspg00Z:g00=XR2#0R3#6#:p,2sp'8R4'4R5g00[5,44g00\0%73,;4g00W`39'5R3'5P0P5P3%32#1#1#1#1#1#1#1#2#6#0#0#0#0#0#0#0#7/44P1f1R4X13X05P4P1O2n2001000000120000000b2o"). Qed.
  Lemma Hhi : (bv_unsigned sp <= 0x800000000000)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_V23Startup ()) ["Assembly"] "h01Hh12H0h22_Hh33_H0h41vp;1p;2p;3g0015j17Tg00DTj25Tg00Y>j22Tg00FAj14Tg00YZj28Tg0041j36Tg00QYR0j23Tg000Pj10Tf0R1#0#0#0#0p=:%01#0p=9%01#0#0#0#0#0#0#0p=1p,4Hvspg00Z:g00=X#:R2#9R3#7p,2sp'5R4'2R5g00[5,24R6g00\0%42,84g00W`36R2'3R7'3P0P5P7%03#1#1#1#1#1#4,24R4P1P0P6P2P4P1f1R4X32X06P4P1O2n2001000000120000000X17X25P4P1O2n2001000000121000000b4o"). Qed.
  Lemma Hal : (bv_unsigned sp mod 16 = 0)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_V23Startup ()) ["Assembly"] "h01Hh12H0h22_Hh33_H0h41vp;1p;2p;3g000Pj10Tg0015j17Tg00DTj23Tg00Y>j21Tg00FAj16Tg00YZj25Tg0041j34Tg00QYR0j22Tp,4Hvspg00Z:g00=X#0#0#0#0R1#0#0#7p,2sp'3R2'1R3g00[5,12R4g00\0%61,52g00W`34R2'2R1'2P0P3P1P2f0R5P0P4P2P2P5P5X02X34f1R4P5O2n2001000000120000000X11X23P4P5O2n2001000000120000000b4o"). Qed.

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
       realizes rsegs (mkCfg (mkst (fx:=fx0) regs (0x63140 : word) mem (seg_rom rsegs))
                             (with_tid tid (init_model (segments_reserved rsegs) brk mbase sp lim
                                                      (mkProcInputC argv envp fs0 stdin0)))) K) ->
    realizes rsegs (init_config rsegs rpc rph sp brk mbase a_draw lim (mkProcInputC argv envp fs0 stdin0)) K.
Proof.
ltac2:(KReplay.run1 (kr_t_V23Startup ()) ["Assembly"] "h01Hh11Rh22b1h32b2h43memh51nh64regsh73tidh82HKh94Htidh:1Kh;2MEh<1bh=3brkh>3fs0h?3limh@5mbasehA6stdin0p;1p;2p;7p;3p;5p;6p;8p;Gg000Pj15Tg0015j1=Tg001Sj13Tg00?Dj11Tg00?ij2QTg0026j1KTg00DTj22Tg00\Nj2?Tg00FAj1<Tg00\jj2DTg00QYR0j2CTg00AZj7STg00]Gj2RTg00SNj3BTg00]jj1PTg00^fj5>Tg00__j1LTg00`]j5;Tg00acj68Tg00b\j2:Tg007>j29Tg0083j37Tg0041j34Tg00cSj3ITg00d7j1HTg00E[j2ATg00BZj2GTg00CZj2JTg00dUj2@Tg00@Uj8FTg00doj8ETg00eoj6MTg00fMlGOTf0R1#5#5p=0%11#5p=6g00VeR2g00gUg00hSg00iSg00jOg00kLg00lHP1f1R3f2R4f3R5f4R6f5R7f6R8g00mHR9f7R:f8R;f9R<f:R=f;R>f<R?f=R@f>RAMGOp=Ng00=XRB#5RC#5RD#5RE#5#0#=RF#3RGg00\0RHg00ngg00oUg00<_%1CRI#=/QGRJ%=E#3#K\GREg00W`12F4RK'?%<C%6I#<'D,?K'CRKp,3AMBRIp,2spRCp,4argvRLp,4envpRMP5P4P3FSg010QRNg0128ROP5%6B#0#1#6#0#6#1#0#0#0#<RPg00UJRQ1RFPd5BFPGeP4%PNRRD>RS%LNRTP=P<PCP;PIPLPMP:P8D;E8,:6'9;77[[]4]6^7GPIPCPLPMp,3Hvap,3Hvep,4Hvspg0130RU%31RV%33RWP0%34?4311254125354HR0[1243124154H%35?443[RX%36?454\0AI431P1n2001000000120000000W3W2W5R0PX^3W^2V^5URUP1PF%H9,AF%1B#1#1#6#6#0,G2%1D#1#0#0#1#0#0#1#0#<'JRD12FD,@HO4b0P8P7P6P5P4P3P2PIPCPLPMP5P4P3GFP7P6P5P4P3PIPCPLPMP6P5P4P1GEO5PTP>P=PCP<PIPLPMP;P:D;E8,:6,9S=7N8P0PUP1PF1AFPRUABFPQRQ1@HP12FU12FQ54HdO4b0A4GUQPGPQPOP8P1P7PRD>PTPAP@PCP?PIPLPMP>P=D;E8,::'9=7N<X<GP3PUP1EMPOP7PUP6PRD>PTP@P?PCP>PIPLPMP=P<D;E8,:8'9=7N;P1b1b0b1W;X9KX4EX6JX7GM?NW8W:WAW>W?X@GW=o"). Qed.

End Assembly.

(* [comment removed for export] *)
Theorem ref_startup : forall sp brk mbase draw lim inp K,
  valid_sp sp -> valid_argv (in_argv inp) -> valid_envp (in_envp inp) ->
  (forall tid regs mem,
     (0 < bv_unsigned tid < 2^22)%Z ->
     @main_entry (amb_of inp draw) sp (in_argv inp) (in_envp inp) tid regs mem ->
     realizes rsegs (mkCfg (mkst (fx:=fx0) regs (0x63140 : word) mem (seg_rom rsegs))
                           (with_tid tid (init_model (segments_reserved rsegs) brk mbase sp lim inp))) K) ->
  realizes rsegs (init_config rsegs rpc rph sp brk mbase draw lim inp) K.
Proof.
ltac2:(KReplay.run1 (kr_t_V23Startup ()) [] "h02HKh13Hsph23Hvah33Hveh41Kh53brkh64drawh73inph83limh95mbaseh:3memh;4regsh<2sph=3tidp;1p;2p;7p;3p;5p;6p;>g000Pj10Tg0015j14Tg001Sj17Tg013Nj1NTg014Cj13Tg0159j1DTg0160j15Tg016fj1>Tg00?Dj11Tg00?ij2<Tg0026j1;Tg00DTj2:Tg00\Nj29Tg00FAj16Tg00\jj2MTg00QYj2LTg017]j28Tg00AZj7KTg00]Gj2CTg00SNj3BTg00]jj1ATg00^fj5@Tg00__j1?Tg00acj6ETg00b\j2FTg007>j2GTg0083j3HTg018]j1=Tg019Qj1ITg01:Hl>JTf0R0#0#0p=2g00=XR1#0R2#2R3#0#2#4R4#7R5g01;Kg00\0g01<Kg00<_f6R6#Nf2R7#3#Df3R8#5#>%12R9#4/<5%43#7#;\5g00W`1:47R3'9%62%19#0#6'M,93'Lf8R3f:R9'8f=R2%33%53P8P7f1R:FKg010QR;g0128P8%11#0#2#1#1#0#2#1#0#1#2#2#2#6R1g00UJ1C41d5B4P5eP7%A;D@f4R4%?;P2f<f>P9f9R2EE'F'G;H3[[]:];^=5f5R;f7'8P9%3;%5;P7P:P8P2P3P6%=;%I;P4P0M>JW0W3W2W1W4W7W8W6X95X55W<o"). Qed.

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
ltac2:(KReplay.run1 (kr_t_V23Startup ()) ["Consumers"] "p'0h01Hh13s1vh21Jh32MEh42HJh52Hah62Hnh72_Hh81ah91eh:3memh;1nh<4segsi001xp;1p;2p;8p;5p;3p;7p;6p;4p;9g0000j19Tg000Pj14Tg0015j1<Tg001Sj1:Tg00DTj27Tg00Y>j2?Tg00HUj1ETg00F_j2CTg00FAj1;Tg00\jj2ATg01=Ej8@Tg0026j18Tg00Iij25Tg01>?j56Tg0041j30Tg00K`j1JTg00L_j1ITg00M`j1HTg00N`j7GTg01?9j6DTg00P`j43Tg00QYR0j22Tg00R4R1j2=Tg01@7j41Tg00AZj7>Tg01@ol9BTg00eoj7FTg00:j#9g00=X#4R2#4#4R3#4#4#4R4#<R5#:R6g01B2p,3sp0R7,75f1R8,75'?f2R9,75%E8'C%;2%;4'A'?p,3AMBR4P7p,2avR2p,2evR5p,3tidR:p,4regsR;p,3memR<p,2MER=G@%<3#:R3#8\6R>1578P4P7P2P5f0R?D6R@90>8P7g01BQP7P2P5%J4%I4RA%H4RBFGRCP8P7P2P5PAPBP:EDRBC390><'2'2X16,=6RAX2>RD'=P1P>PD%93#8R3f6RDP<f5REf4RFC1PDPCPEPFC130P?P1P61579A0>9@P7PCP9PBC390><'2'2X16f:R9P<f9R1f8RDC1P9PCP1PDC1503P?157FA0>F@P7PCPFPBC390><'2'2P0157EP4P7P2P5P8D690>EP7PCPEPBC390><'2f>R@P<f=R9f<RGC1P@PCP9PGC1503P?f7RH,57P4P7P2P5PFD690>DP7PCPDPBC390><'2P0P4P7P2P5PED690>1P7PCP1PBC390><fBR1P<fAREf@R0C1P1PCPEP0C1503P?f;P4P7P2P5PHD650>P7PCPGPBC390><P>P7PCP9PBC3R9P4P7P2P5P:P;P?F>fGRGP8fFRHfER0C1PGPCPHP0C1503]3X:>P4P7P2P5P:P;P9F>P7PCPHP@PBP0fDfCP1M9BW3P<P?P=FFW0W7P8P?O2n2001000000121000000W0W4P8P?O2n2001000000121000000W0X16P8P?O2n2001000000121100000X0AX2>P8P?O2n2001000000121100000b9W6W5W;W8W<o"). Qed.

  Lemma main_entry_mem_above : forall (a : word),
    (bv_unsigned sp0 <= bv_unsigned a)%Z -> mem a = wrap_mem RPH sp0 av ev a_uid a_hwcap a_draw a.
Proof.
ltac2:(KReplay.run1 (kr_t_V23Startup ()) ["Consumers"] "p'0h01Hh13s1vh21Jh32MEh42HJh52Hah62_Hh71ah81eh93memi001xp;1p;2p;8p;5p;3p;7p;6p;4g000Pj13Tg0015j1;Tg001Sj18Tg00DTj27Tg00Y>j2ETg01=Ej8@Tg0026j1?Tg00Iij25Tg01>?j54Tg0041j30Tg00K`j1>Tg00L_j1=Tg00M`j1<Tg00N`j7Dj86Tg01?9j6CTg00P`j41Tg00QYR0j22Tg00R4R1j29Tg00AZj7:Tg01Cnj6ATg00eoj7BTg00=X#3#3#3R2#3#3#3#;R3#8R4p,3sp0R5,73f0R6,73'Ep,3AMBR3P5p,2avR7p,2evR8p,3tidR9p,4regsR:p,3memR;p,2MER<G@%;2#8#?R2\4R=f1R>,55P3P5P7P8P6D4R?90=>P5g01BQR@P5P7P8%>3RA%=3RB%<3RCFDRDP>P5P7P8PBPCP9ECREC190=;'2'2X14,94RFX2=RG'9P1P=PGP;f3RGO1P@P5P7P8PAPBPCPGG6502P6P1P4f2R1,55A0=1?P5PDP1PEC190=;'2'2X14P;f7R1O1P@P5P7P8PAPBPCP1G6502P6f4RG,55A0=G?P5PDPGPEC190=;'2'2P0f5R?,55P3P5P7P8P>D490=?P5PDP?PEC190=;'2P;f;RHO1P@P5P7P8PAPBPCPHG6502P61551f8RIP3P5P7P8PGD450=P5PDPIPEC190=;'2P0f9R0P3P5P7P8P?D450=P5PDP0PEC190=;P;f?R0O1P@P5P7P8PAPBPCP0G6502P6P3P5P7P8P1D490=HP5PDf<PEC190=;P=P5PDf=PEC1RHP3P5P7P8P9P:P6F:P>fDR1O1P@P5P7P8PAPBPCP1G6502]3X9=P3P5P7P8P9P:PHF:P5PDf>PEfCfBEAW3P;P6P<FBW0W6P>P6O2n2001000000121000000W0W4P>P6O2n2001000000121000000W0X14P>P6O2n2001000000121100000X0FX2=P>P6O2n2001000000121100000b8W5W7o"). Qed.

  (* [comment removed for export] *)
  Lemma main_entry_win_mapped : forall (a : word),
    (bv_unsigned sp0 - stack_max_size <= bv_unsigned a < bv_unsigned sp0)%Z -> mem a <> None.
Proof.
ltac2:(KReplay.run1 (kr_t_V23Startup ()) ["Consumers"] "p'0h01Hh13s1vh21Jh32MEh44__x1h54__x2h64__x3h72HJh82Hah92_Hh:7__arithh;4__ffh<8__varmaph=5__with>1ah?1eh@3memhA1oi001xp;1p;2p;8p;5p;3p;7p;6p;4g000Pj13Tg0015j1CTg001Sj1>Tg00DTj2:Tg00E>j2;Tg00Y>j29Tg00\Nj28Tg00QYR0j21Tg01=Ej8LTg0026j1GTg00Iij25Tg01>?j56Tg0041j30Tg00K`j1^Tg00L_j1VTg00M`j1UTg00N`j7RTg01?9j6QTg00P`j42j5[Tg00R4R1j2@Tg003Oj1ATg01E0j14Tg00AZj7?Tg005cj1NTg0000j1MTg01EIj2=Tg01Egj4KTg01FEj1ITg01Fcj1HTg01GNj27Tg01H1j3JTg00?Dj1FTg01HTj4<Tg01I?j7ETg01Icj8OTg01JGj2PTg00dUj2DTg01Jij2STg01KUj3TTg01L4j4]Tg01Lfj2\Tg01Maj6WTg00eoj6Xj7YTg01Naj7ZTf1R2g01OER3g01OdR4P4g01PDR5f0R6g01PdFZp=Bg00=XR7#3R8#3#3R9#3#3#3#CR:#>R;p,3sp0R<,::R=g01QDR>';1::6R?'918?='1p,3AMBR?P<p,2avR@p,2evRAp,3tidRBp,4regsRCp,3memRDp,2MEREGL%C9#>R9#GRF\;RG15<2P?P<P@PAP6D6RH90G2P<g01BQP<P@PA%^?%V?RI%U?RJFRRKP2P<P@PAPIPJPBEQRJC290GD'1'1X1;,@;RIX2GRL'@P1PGPLPDf3RLO1%A9R950F#4P6P1P;f2R1,5<A0G1HP<PKP1PJC290GD'1'1X1;PDf7RMO1=0F9#4P6f4RN,5<A0GNHP<PKPNPJC290GD'1'1P0f5RH,5<P?P<P@PAP2D690GHP<PKPHPJC290GD'1PDf;ROO1=0F9#4P615<Mf8RPP?P<P@PAPND650GP<PKPPPJC290GD'1P0f9R0P?P<P@PAPHD650GP<PKP0PJC290GDPDf?O1=0F9#4P6P?P<P@PAPMD690GOP<PKf<PJC290GDPGP<PKf=PJC2ROP?P<P@PAPBPCP6F?P2fDRMO1=0F9#4]3X@GP?P<P@PAPBPCPOF?PFf>ROfCRCO1A0F69#4XAFf6PCg00\0RFg01RAR9#N%M9PF1=F1P21=FLCK%IF%HFR9P3P4P4P5P9P3P4P4P5PF17F7R317F85JFg01Rm%F7,7FR7C<,B9PFP7g01STP3C<,B9FER3%A4P3GO1P95P6P1g01T;R9g01T[R5'D1S61=095dg00W`=TF2C]b;b<b=X4FX5FW61;62/911816'11;21/9L18L2'1[^4F^5F^6FP61::MP>P=PCO4b:1\<CeR=O2P<PKPOPJPCD[P<PKPOPJPCP=EWEXW3PDP6PEFYW0W9P2P6O2n2001000000121000000W0W7P2P6O2n2001000000121000000W0X1;P2P6O2n2001000000121100000X0IX2GP2P6O2n2001000000121100000b?W8W>o"). Qed.

  Lemma main_entry_store_ok_win : forall segs (a : word) n,
    (bv_unsigned sp0 - stack_max_size <= bv_unsigned a)%Z ->
    (bv_unsigned a + Z.of_nat n <= bv_unsigned sp0)%Z ->
    store_ok segs mem a n = true.
Proof.
ltac2:(KReplay.run1 (kr_t_V23Startup ()) ["Consumers"] "p'0h01Hh14__x1h24__x2h34__x3h43s1vh51Jh62MEh77__arithh84__ffh98__varmaph:5__with;4cstrh<2HJh=3Hhih>3Hloh?2_Hh@1ahA1ehB3memhC1nhD4segsi001xp;1p;2p;8p;5p;3p;7p;6p;4p;:g0000j1FTg000Pj15Tg0015j1ATg001Sj1@Tg00DTj29Tg00E>j2=Tg00Y>j23Tg00HUj1<Tg00F_j2:Tg01=Ej8OTg0026j1JTg00Iij27Tg01>?j56Tg0041j30Tg00K`j1]Tg00L_j1VTg00M`j1UTg00N`j7TTg01?9j6RTg00P`j42Tg00QYR0j21Tg00R4R1j2CTg01U;j48Tg00AZj7BTg01V;j1QTg005cj1PTg01EIj2?Tg01Egj4NTg01FEj1LTg01Fcj1KTg01GNj2;Tg01H1j3ITg00?Dj1MTg01HTj4>Tg003Oj1HTg01JGj2GTg00dUj2STg01Jij2`Tg01KUj3_Tg01L4j4^Tg01V`j1\Tg01W[j3WTg01X>l:XTg00eoj7YTg01Naj7ZTg01Icj8[Tg01T;R2f0R3g01T[R430p=4f1R5g01OER6g01OdR7P7g01PDR8P3g01PdFZp=Ef3R9P6P7P7P8f2R6P5P3G[p=Dg00:j#Fg00=XR:#5R;#5#5R<#5#5#5#AR=#@R>g01B2p,3sp0R?,9=R@g01QDRA'=19=5'319=6%<5':/3@p,3AMBRBP?p,2avRCp,2evRDp,3tidREp,4regsRFp,3memRGp,2MERHGO%A<#@#J\>R<17?5PBP?PCPDP3D6RI90<5P?g01BQP?PCPD%]B%VBRJ%UBRKFTRLP5P?PCPDPJPKPEERRKC290<G'1'1X4>,C>RJX5<RM'CP1P<PMf6RMPGf5RNf4ROC8#4P3P1P>17?6A0<6IP?PLP6PKC290<G'1'1X4>f:PGf9R1f8RPC8#4P317?OA0<OIP?PLPOPKC290<G'1'1P017?NPBP?PCPDP5D690<NP?PLPNPKC290<G'1f>RIPGf=RQf<RRC8#4P3f7RS,7?PBP?PCPDPOD690<PP?PLPPPKC290<G'1P0PBP?PCPDPND690<1P?PLP1PKC290<GfBPGfAf@C8#4P3f;PBP?PCPDPSD650<P?PLPRPKC290<GP<P?PLPQPKC2RQPBP?PCPDPEPFP3FBfGRRP5fFRSfER1C8#4]6XB<PBP?PCPDPEPFPQFBP?PLPSPIPKP1fDRKPM%QKRMg00W`RI%<K'3RLg00\0RQg01RARF#PRE%FFRFPQ1?Q6P51?Q9CNRD%LQRC%KQRBPQ1;Q:RN1;Q;R;5IQg01RmR0%M:,;QR:C>,EBRP%H7R7PPCD1GB8R8P3P61S241`36#4dA_QI5C^RIb8b9b:X1QX2QW31=35/361=56/39[^1Q^2Q^3QP319=RRRPAP@P1O4b7b;%\?19=1'3ePMPLPEPFPDPCPBPQAWQN;P0P:C>,EBRBP7PBCDP8PIb8b9b:X1QX2QX3Q1:35/361:56/39[^1Q^2Q^3QP3P@%<SPRPKO4b7b;M:XW6PGP3PHFYW0W?P5P3O2n2001000000121000000W0W<P5P3O2n2001000000121000000W0X4>P5P3O2n2001000000121100000X0JX5<P5P3O2n2001000000121100000bAW=W>WCW@WDo"). Qed.

  (* [comment removed for export] *)
  Lemma main_entry_mem_data : forall (a : word),
    (bv_unsigned a < bv_unsigned sp0 - stack_max_size)%Z ->
    mem a = D_main sp0 av ev a_hwcap a_draw tid a.
Proof.
ltac2:(KReplay.run1 (kr_t_V23Startup ()) ["Consumers"] "p'0h01Hh13s1vh21Jh32MEh42HJh52Hah62_Hh71ah81eh93memi001xp;1p;2p;8p;5p;3p;7p;6p;4g000Pj13Tg0015j1<Tg001Sj18Tg00DTj27Tg00E>j2GTg00\Nj29Tg01=Ej8ATg0026j1@Tg00Iij25Tg01>?j54Tg0041j30Tg00K`j1>Tg00L_j1=Tg00M`j1FTg00N`j7ETg01?9j6Dj76Tg00P`j41Tg00QYR0j22Tg00R4R1j2:Tg00AZj7;Tg01V`j1BTg01YDj6?Tg00eoj7CTg00=X#3#3#3R2#3#3#3#<R3#8R4f0R5,73p,3sp0R6,73g01QD'G'9p,3AMBR7P6p,2avR8p,2evR9p,3tidR:p,4regsR;p,3memR<p,2MER=GA%<2#8#@R2\4R>f1R?,56P7P6P8P9P5D4R@90>?P6g01BQP6P8P9%>7%=7RA%F7RBFERCP?P6P8P9PAPBP:EDRDC190><'2'2X14,:4REX2>RF':P1P>PFP<f3RFO1P6P8P9PAPBP:PFF6502P5P1P4f2R1,56A0>1@P6PCP1PDC190><'2'2X14P<f7R1O1P6P8P9PAPBP:P1F6502P5f4RF,56A0>F@P6PCPFPDC190><'2'2P0f5R@,56P7P6P8P9P?D490>@P6PCP@PDC190><'2P<f;RGO1P6P8P9PAPBP:PGF6502P51561f8RHP7P6P8P9PFD450>P6PCPHPDC190><'2P0f9R0P7P6P8P9P@D450>P6PCP0PDC190><P<f?R0O1P6P8P9PAPBP:P0F6502P5P7P6P8P9P1D490>GP6PCf<PDC190><P>P6PCf=PDC1RGP7P6P8P9P:P;P5F;P?fDR1O1P6P8P9PAPBP:P1F6502]3X9>P7P6P8P9P:P;PGF;P6PCf>PDfCRDfB173D%B6'9eE?W3P<P5P=FCW0W6P?P5O2n2001000000121000000W0W4P?P5O2n2001000000121000000W0X14P?P5O2n2001000000121100000X0EX2>P?P5O2n2001000000121100000b8W5W7o"). Qed.

  Lemma main_entry_rdn_data : forall segs (a : word) n,
    (bv_unsigned a + Z.of_nat n <= bv_unsigned sp0 - stack_max_size)%Z ->
    rdn segs mem a n = rdn segs (D_main sp0 av ev a_hwcap a_draw tid) a n.
Proof.
ltac2:(KReplay.run1 (kr_t_V23Startup ()) ["Consumers"] "p'0h01Hh13s1vh21Jh32MEh42HJh52Hah62_Hh71ah81eh93memh:1nh;4segsi001xp;1p;2p;8p;5p;3p;7p;6p;4g0000j1@Tg000Pj14Tg0015j1:Tg001Sj19Tg00DTj27Tg00HUj1?Tg00F_j2<Tg00E>j2DTg00Y>j2=Tg01=Ej8ATg0026j18Tg00Iij25Tg01>?j56Tg0041j30Tg00K`j1JTg00L_j1ITg00M`j1HTg00N`j7GTg01?9j6ETg00P`j42Tg00QYR0j23Tg00R4R1j2;Tg01@7j41Tg00AZj7>Tg01V`j1CTg01ZEj8BTg00eoj7FTg00:j#@g00=X#4#4#4R2#4#4#4#:R3#9R4g01B2f1R5,73f0R6#?'<p,3sp0R7,73g01QD'D'=p,3AMBR8P7p,2avR9p,2evR:p,3tidR;p,4regsR<p,3memR=p,2MER>GA%:2#9R2#8\4R?1575P8P7P9P:P6D6R@90?5P7g01BQP7P9P:%J8%I8RA%H8RBFGRCP5P7P9P:PAPBP;EERBC290?='3'3X14,;4RAX2?RD';P1P?PD%@2#8R2f5RDP=f4REf3RFC1PDPBPEPFC130P6P1P4f2R1,57A0?1@P7PCP1PBC290?='3'3X14f9R1P=f8RFf7RGC1P1PBPFPGC1502P6157EA0?E@P7PCPEPBC290?='3'3P0157DP8P7P9P:P5D690?DP7PCPDPBC290?='3f=R@P=f<RHf;RIC1P@PBPHPIC1502P6157GP8P7P9P:PED690?FP7PCPFPBC290?='3P0P8P7P9P:PDD690?1P7PCP1PBC290?=fAR1P=f@RDf?R0C1P1PBPDP0C1502P6P8P7P9P:PGD690?IP7PCPHPBC290?=P?P7PCP@PBC2R@P8P7P9P:P;P<P6F>fFRHP5fERIfDRGC1PHPBPIPGC1502]3X9?P8P7P9P:P;P<P@F>P7PCPIf>PBPGfCRBfB173G%?B'<%C7'=eGBW3P=P6P>FFW0W6P5P6O2n2001000000121000000W0W4P5P6O2n2001000000121000000W0X14P5P6O2n2001000000121100000X0AX2?P5P6O2n2001000000121100000b8W5W:W7W;o"). Qed.
End Consumers.
