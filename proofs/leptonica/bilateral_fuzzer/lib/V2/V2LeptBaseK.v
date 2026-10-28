(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.leptonica.bilateral_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure AllocCredit.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib LeptDefs LeptStructs.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.V2 Require Import V2LeptStderr V2LeptBase.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica Require Import LeptRoom LeptCredit.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib Require KReplay.
Ltac2 kr_t_V2LeptBaseK () := "C6ARocqVerifyHarness?AgentSubmission6Common8Mallocng;AllocCredit8acr_sureC6ARocqVerifyHarness?AgentSubmission6Common8Mallocng9AllocSure:asr_callocI6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs4lctx00C6ARocqVerifyHarness?AgentSubmission6Common8Mallocng;AllocCalloc8aic_baseC6ARocqVerifyHarness?AgentSubmission6Common8Mallocng9AllocBase2ASK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00K47Corelib7Numbers7BinNums8positive01C4ELinuxProcessSemantics5Riscv7Prelude5bvmapI47Corelib4Init9Datatypes4list00C5ARocqVerifyHarness?AgentSubmission6Common:AllocIface7al_segsI6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs3Cok00I6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs1W00K47Corelib7Numbers7BinNums1Z02K45stdpp9bitvector;definitions2bv01C5ARocqVerifyHarness?AgentSubmission6Common8PropExec4getrC45stdpp9bitvector;definitions7Z_to_bvI47Corelib4Init5Logic2eq00C56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z3mulC4ELinuxProcessSemantics?LinuxProcessSem5State8m_vmmapsC6ARocqVerifyHarness?AgentSubmission6Common8Mallocng;AllocCredit6aroomPC6ARocqVerifyHarness?AgentSubmission6Common8Mallocng9AllocSure<alloc_marginC56Stdlib6ZArith6BinInt1Z3addC5ARocqVerifyHarness?AgentSubmission6Common5Hoare6ret_okC56Stdlib6ZArith6BinInt1Z6moduloC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs5c_topC56Stdlib6ZArith6BinInt1Z3subC4ELinuxProcessSemantics?LinuxProcessSem5State;with_vmmapsC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs7cs_keptC45stdpp9bitvector;definitions;bv_unsignedC47Corelib4Init5Logic3notC6ARocqVerifyHarness?AgentSubmission6Common8Mallocng9AllocBase4liveK47Corelib4Init9Datatypes6option02K47Corelib4Init9Datatypes6option01C6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs4c_A0C5ARocqVerifyHarness?AgentSubmission6Common5Hoare3at_C5ARocqVerifyHarness?AgentSubmission6Common:AllocIface7round16C6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs4c_vmC4ELinuxProcessSemantics?LinuxProcessSem5State9alloc_topC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs5POSTMC6ARocqVerifyHarness?AgentSubmission6Common8Mallocng;AllocCredit:alloc_costC5ARocqVerifyHarness?AgentSubmission6Common:AllocIface6al_romC5ARocqVerifyHarness?AgentSubmission6Common8PropExec4mkstK4ELinuxProcessSemantics?LinuxProcessSem3Run6config01I5ARocqVerifyHarness?AgentSubmission6Common8ShapeAlg8realizes00C6ARocqVerifyHarness?AgentSubmission6Common8Mallocng;AllocCalloc<al_calloc_pcC5ARocqVerifyHarness?AgentSubmission6Common:AllocIface5al_gpC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica:LeptCredit>W_calloc_psureC5ARocqVerifyHarness?AgentSubmission2V2:V2LeptBase6p16_tpC47Corelib4Init5Logic6eq_indC5ARocqVerifyHarness?AgentSubmission2V2:V2LeptBase:p16_callocI47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01K47Corelib7Numbers7BinNums8positive03I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00C5ARocqVerifyHarness?AgentSubmission6Common8ShapeAlg4TSetI4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00C5ARocqVerifyHarness?AgentSubmission2V2:V2LeptBase5LLU16K47Corelib4Init5Logic4True01C6ARocqVerifyHarness?AgentSubmission6Common8Mallocng;AllocCredit<ROOM_CREDMAXC6ARocqVerifyHarness?AgentSubmission6Common8Mallocng9AllocSure9ROOM_NMAXC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs4LSTKC6ARocqVerifyHarness?AgentSubmission6Common8Mallocng;AllocCalloc<CALLOC_STACKI4ELinuxProcessSemantics?LinuxProcessSem5State6VmMaps00C5ARocqVerifyHarness@ProcessOversightJTgt_bilateral_fuzzer_ubsan1M?loaded_segments".
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section BaseK.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ACR : AllocCredit}.
Context {PINS : @LeptPins AL LLU16} {P16 : V2Pins}.
Let AL_segs : al_segs = SEGS := p16_segs.
#[local] Notation "'u'" := bv_unsigned (only parsing).

(* [comment removed for export] *)
Lemma W_calloc16_psure : forall C A m md regs (cnt sz kP pP : Z) (ret : word) (s : Z) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 10 = Z_to_bv 64 cnt -> getr regs 11 = Z_to_bv 64 sz ->
  0 <= cnt < 2 ^ 64 -> 0 <= sz < 2 ^ 64 -> 0 <= cnt * sz < 2 ^ 61 ->
  aroomP A (m_vmmaps md) kP pP -> 1 <= kP -> alloc_margin (cnt * sz) + ROOM_CREDMAX <= pP -> cnt * sz <= ROOM_NMAX ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 0x56270 ->
  getr regs 2 = Z_to_bv 64 s -> s mod 16 = 0 -> c_top C - LSTK + CALLOC_STACK <= s -> s <= c_top C ->
  (forall A' m' vm' regs' (res : word),
      W C A' m' (with_vmmaps vm' md) ->
      getr regs' 10 = res -> cs_kept regs regs' ->
      u res <> 0 -> live A res = None -> live A' res = Some (cnt * sz) -> live (c_A0 C) res = None ->
      (forall q, q <> res -> live A' q = live A q) ->
      (forall i, 0 <= i < cnt * sz -> m' (at_ res i) = Some (Z_to_bv 8 0)) ->
      u res mod 16 = 0 -> u res + round16 (cnt * sz) <= alloc_top (c_vm C) ->
      POSTM C A s m m' ->
      aroomP A' vm' (kP - 1) (pP - alloc_cost (cnt * sz)) ->
      realizes SEGS (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (mkst regs (Z_to_bv 64 0x3c0f8) m al_rom) md) S.
Proof.
ltac2:(KReplay.run1 (kr_t_V2LeptBaseK ()) ["BaseK"] "h02A'h11bh22m'h35regs'h43resh53vm'h61Ah71Ch81Sh93cnth:1ih;2kPh<1lh=1mh>2mdh?2pPh@1qhA4regshB3rethC1shD2szp;3p;2p;1p;5p;8p;7p;4p;9p;Bp;6g0000j3kTg0019j3jTg002Bj3XTg003Gj3UTg004Pj2iTg005Qj11Tg0066j1CTg006Tj1LTg0077j1JTg007Yj12Tg008>j2STg008jj1QTg009Jj1hTg00:Hj5fTg00;Lj8OTg00<Nj13Tg00<lj39Tg00=Oj28Tg00>Hj2;Tg00>nj30Tg00?Hj25Tg00?dj2NTg00@Aj2BTg00@]j2?Tg00A8j26Tg00AUj1WTg00BLj7KTg00CSj1VTg00D^j2ATg00E;j1TTg00F3j2ITg00FSj4GTg00GWj2@Tg00H4j2HTg00Hnj2RTg00J4j2ETg00J^j1MTg00K7j4<Tg00L:j1gTg00L\j2PTg00M>j4eTg00NAj2bTg00O6j1aTg00P4j4`Tg00Q7j1_Tg00Qol9^Tg00S3j1]Tg00T>j1\Tg00U;j5=Tg00V4j2>Tg00Vij3:Tg00Whj1[Tg00Y5j1ZTg00Z1lBcTg00[@j3dTg00\9j6DTg00\Uj3YTf0R0#1#1p=4%20#2p=7g00]RR1g00^0R2700p=Fp,2ALR3p,2CLR4p,3ACRR59k349j34R63XAU346R7,i3R8g00^NR9#1R:#1R;#1R<#1R=#4R>#CR?#LR@%C<R<#LRA#JRB[RCg00_3%2:RD#CRE/S@RFg00_ig00`b#QRG%h3RHP3P4P6g00aaRIf<RJDfRKP3P4P6PIf=RLPJf;RMf:RNGORO%1D#3g00bYRP59ERQ,8Nf9RR,;?RS50@RT%2D#3=9EP,8M=0@SRS152M%3:R:%3>'N,BM'?R>16LJRD,52%29#7#1#2#3,N:,BD'?RDP3P4P5fBRUf@RV#WPJPMFKRJ%39RW/5LRXf?RY,6V#Vg00c5'A/5LRZfAR[/6Vg00dB'5R\fCR]A9EWP'8f>R^50@R_%TYR`fE%3;=9EP'8R;%19#2#1#7#1#4#2#4#2#7#4#4#3,;?Ra50@RbfFA9E:P'81;?V50@R:%3=R=,I[#FR[P3P4P6fLRPCGg00eJ'@g00fM'A/5URUP3P4P6fMRECG,5]Rcg00gZRdP3P4P6PIfSRef4Rff3Rgf2RhfP'HGORi18hQf1RQ50@RjfQ/RgRk1E?g#F#MRl%J1RmP3P7fVRnPfC<%g1Ro30RpP3P7PRf5RqC<fR,6e,P150mReP3P7P3P4P6fYRrCef6RsC<=0moRof8Rt90@0#MP3P7PLPQC<P3P7f[PQC<50m[^@@Rm1520fWR7/6n,B0'?PL1bNQO11;<2,PA50B[^:1RB1E?R/I=#FR=1E?NfXRA/67#a'AP3P4P6f]R<C`#_'5R2P3P4P6PIf^P<fTR6f\P^M9^RnP3P4P5PVP^1@AWfZ/6r#],@7FKRrp,2fxRAP^P7PV%\3RVD=1HY<'>R<fURY5:6[[[[[[[[[[[[[^4@^3F]5^2C^08PAfKR6%29#7#4#4#4#2#7#7#1#4#3,;?R?PEPVD=/>PfDR95:][[[[[[[[[[[[[\>[[[[[X<GP@%[4RGA:H<Y\r\n\2\=\B\m\o\e\p\l\k\j\i^4@^3F^5d^2C^08R8PAP6P]PEPVD=/>P=:H9[\c\U\[\:\b\`\_\\\Z\X\J\D\>\>\S\T\O\KX1@P@%Z3A0@;LPAP6PGPEPVD=/>P=:H9\8\c\U\[\:[\`\_\\\Z\X\J\D\>\>\S\T\O\KX1@PAP3P4P5PIp,4PINSPMPNPRPtf7PsPqPfPgPhPQP0MBcPap,3P16Ra9d34EDP?AY34aEDg00hQp,7AL_segsEDW8XC1XB@X?1X;1XD1X91WAW>W=W6W7o"). Qed.
End BaseK.
